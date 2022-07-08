### [2020-03-31 22:26:22](https://github.com/leanprover-community/mathlib/commit/7d89f2e)
feat(data/fintype/card): prod_univ_sum ([#2284](https://github.com/leanprover-community/mathlib/pull/2284))
* feat(data/fintype/card): prod_univ_sum
* Update src/data/fintype.lean
* Update src/data/fintype/card.lean
* docstrings
* fix build
* remove unused argument
* fix build

### [2020-03-31 19:02:55](https://github.com/leanprover-community/mathlib/commit/224ba7e)
feat(data/finset): card_image_le ([#2295](https://github.com/leanprover-community/mathlib/pull/2295))
* feat(data/finset): card_image_le
* add list.to_finset_card_le

### [2020-03-31 16:02:27](https://github.com/leanprover-community/mathlib/commit/72d3b6e)
feat(tactic/equiv_rw): incorporating equiv_functor ([#2301](https://github.com/leanprover-community/mathlib/pull/2301))
* feat(tactic): rewriting along equivalences
* header
* minor
* type
* actually, rewriting the goal under functors is easy
* rewriting inside function types
* more
* way better
* improving comments
* fun
* feat(data/equiv): pi_congr
* various
* feat(data/equiv): sigma_congr
* docstrings
* change case for consistency
* tidying up
* minor
* minor
* switching names
* fixes
* add some tracing routines for convenience
* feat(tactic/core): trace_for
* typo
* oops
* oops
* various
* chore(tactic/solve_by_elim): cleanup
* cleanup
* what happened to my commit?
* fix
* fix
* rename to trace_if_enabled
* fixed?
* Tweak comments
* feat(tactic/solve_by_elim): add accept parameter to prune tree search
* when called with empty lemmas, use the same default set as the interactive tactic
* trace_state_if_enabled
* Update src/data/equiv/basic.lean
* implicit arguments
* stop cheating with [] ~ none
* indenting
* yay, working via solve_by_elim
* pretty good
* various
* various
* docstring
* fix docstrings
* more docs
* docs
* feat(data/equiv/functor): bifunctor.map_equiv
* bifunctors
* test rewriting under unique
* start
* sketch of equiv_functor
* rewriting in subtypes
* add documentation, and make the function an explicit argument
* documentation
* fix doc-strings
* typos
* minor
* adding demonstration of transporting semigroup
* update
* removing unimpressive inhabited example; easier later
* Update .vscode/settings.json
* err
* trying to transport through monoid
* err?
* much better
* improve documentation of accept, and add doc-string
* fix duplicated namespace
* improve docs
* feat(logic/basic): trivial transport lemmas
* try again with documentation
* update
* oops
* oops
* omit
* revert unnecessary change
* fix doc-string
* chore(data/equiv/basic): simp to_fun to coe
* feat(tactic/equiv_rw): incorporating equiv_functor
* rename adapt_equiv
* simplify the equivalence produced, and provide a tactic to access the equivalence
* add max_steps option
* add decl_name to add_tactic_doc
* fix add_tactic_doc
* satisfying linter
* fix names
* finish fix
* add defaults for cfg arguments
* remove simplify_term, which already existed as expr.simp
* remove duplicate functions that have been PRd separately
* no need for accept
* Update src/tactic/equiv_rw.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Update src/tactic/equiv_rw.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* replace max_steps with max_depth
* use solve_aux
* add missing simp lemmas about arrow_congr'
* fix failing test, by making sure we don't leave any ≃ goals on the table
* add comment
* comment out trace output
* fix fields

### [2020-03-31 14:30:05](https://github.com/leanprover-community/mathlib/commit/b508d0e)
feat(tactic/equiv_rw): rewriting along equivalences ([#2246](https://github.com/leanprover-community/mathlib/pull/2246))
* feat(tactic): rewriting along equivalences
* header
* minor
* type
* actually, rewriting the goal under functors is easy
* rewriting inside function types
* more
* way better
* improving comments
* fun
* feat(data/equiv): pi_congr
* various
* feat(data/equiv): sigma_congr
* docstrings
* change case for consistency
* tidying up
* minor
* minor
* switching names
* fixes
* add some tracing routines for convenience
* feat(tactic/core): trace_for
* typo
* oops
* oops
* various
* chore(tactic/solve_by_elim): cleanup
* cleanup
* what happened to my commit?
* fix
* fix
* rename to trace_if_enabled
* fixed?
* Tweak comments
* feat(tactic/solve_by_elim): add accept parameter to prune tree search
* when called with empty lemmas, use the same default set as the interactive tactic
* trace_state_if_enabled
* Update src/data/equiv/basic.lean
* implicit arguments
* stop cheating with [] ~ none
* indenting
* yay, working via solve_by_elim
* pretty good
* various
* various
* docstring
* fix docstrings
* more docs
* docs
* feat(data/equiv/functor): bifunctor.map_equiv
* bifunctors
* test rewriting under unique
* rewriting in subtypes
* add documentation, and make the function an explicit argument
* documentation
* fix doc-strings
* typos
* minor
* adding demonstration of transporting semigroup
* Update .vscode/settings.json
* err
* trying to transport through monoid
* err?
* much better
* improve documentation of accept, and add doc-string
* fix duplicated namespace
* improve docs
* try again with documentation
* update
* oops
* rename adapt_equiv
* simplify the equivalence produced, and provide a tactic to access the equivalence
* add max_steps option
* add decl_name to add_tactic_doc
* fix add_tactic_doc
* satisfying linter
* add defaults for cfg arguments
* remove simplify_term, which already existed as expr.simp
* remove duplicate functions that have been PRd separately
* no need for accept
* Update src/tactic/equiv_rw.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Update src/tactic/equiv_rw.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* replace max_steps with max_depth
* use solve_aux
* add missing simp lemmas about arrow_congr'
* fix failing test, by making sure we don't leave any ≃ goals on the table
* add comment
* comment out trace output

### [2020-03-31 11:30:19](https://github.com/leanprover-community/mathlib/commit/2669062)
feat(data/monoid_algebra): some lemmas about group rings ([#2239](https://github.com/leanprover-community/mathlib/pull/2239))
* feat(algebra/ring): generalize mul_ite
* fix proofs
* going off the deep-end
* cleaning up
* much better
* getting there
* no new congr lemma
* oops
* ...
* to_additive
* removing bad simp lemmas again...
* fix proof
* fix'
* oops
* feat(data/monoid_algebra): some lemmas about group rings
* Update src/algebra/ring.lean
* remove unnecessary arguments, thanks linter
* err.. marking simp again, because I can't remember what goes wrong and need CI to compile for me
* handing it back to CI for another try
* fix prod_ite as well
* cast_ite
* gross fix for quadratic reciprocity argument
* remove simp from add_ite, add comment
* sadness
* slight improvement
* remove redundant lemmas

### [2020-03-31 09:10:23](https://github.com/leanprover-community/mathlib/commit/1763220)
chore(scripts): update nolints.txt

### [2020-03-31 08:35:51](https://github.com/leanprover-community/mathlib/commit/85affa4)
refactor(*): migrate more files to bundled `ring_hom`s ([#2286](https://github.com/leanprover-community/mathlib/pull/2286))
* refactor(*): migrate more files to bundled `ring_hom`s
* Fix lint

### [2020-03-31 05:47:42](https://github.com/leanprover-community/mathlib/commit/66f3090)
feat(analysis/analytic): first take on analytic functions ([#2199](https://github.com/leanprover-community/mathlib/pull/2199))
* analytic: first definitions
* docstrings
* cleanup
* Update src/analysis/analytic/basic.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* comment on polydisk of convergence
* coefficient at 0
* protect sum
* rename with_top.dense_coe

### [2020-03-31 03:13:56](https://github.com/leanprover-community/mathlib/commit/20bff2c)
chore(scripts): update nolints.txt

### [2020-03-31 02:43:53](https://github.com/leanprover-community/mathlib/commit/4168aba)
refactor(data/fintype): move data/fintype to data/fintype/basic ([#2285](https://github.com/leanprover-community/mathlib/pull/2285))

### [2020-03-31 00:17:23](https://github.com/leanprover-community/mathlib/commit/c5181d1)
feat(*): more `prod`-related (continuous) linear maps and their derivatives ([#2277](https://github.com/leanprover-community/mathlib/pull/2277))
* feat(*): more `prod`-related (continuous) linear maps and their derivatives
* Make `R` argument of `continuous_linear_equiv.refl` explicit

### [2020-03-30 20:48:51](https://github.com/leanprover-community/mathlib/commit/64f835b)
chore(scripts): update nolints.txt

### [2020-03-30 20:13:52](https://github.com/leanprover-community/mathlib/commit/8a61723)
fix(algebra/punit_instance): punit.smul_eq is marked simp and can be proved by simp ([#2291](https://github.com/leanprover-community/mathlib/pull/2291))

### [2020-03-30 16:48:08](https://github.com/leanprover-community/mathlib/commit/3f0e700)
doc(algebra/group/type_tags): add docs ([#2287](https://github.com/leanprover-community/mathlib/pull/2287))
* doc(algebra/group/type_tags): add docs
* Update src/algebra/group/type_tags.lean

### [2020-03-30 13:16:33](https://github.com/leanprover-community/mathlib/commit/1331e29)
chore(*): completing most of the -T50000 challenge ([#2281](https://github.com/leanprover-community/mathlib/pull/2281))

### [2020-03-30 10:46:51](https://github.com/leanprover-community/mathlib/commit/37212a7)
feat(data/fin*): uniqueness of increasing bijection ([#2258](https://github.com/leanprover-community/mathlib/pull/2258))
* feat(data/fin*): uniqueness of increasing bijection
* protect
* remove tidy call
* Update src/data/finset.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Update src/data/finset.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Update src/data/fintype/card.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Update src/data/fintype/card.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Update src/data/fintype/card.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* prove prod_add, and use this to prove sum_pow_mul_eq_add_pow
* forgot to save
* fix build
* remove card_sub_card

### [2020-03-30 08:09:21](https://github.com/leanprover-community/mathlib/commit/cd38923)
docs(algebraic_geometry/prime_spectrum): linkify url in module docs ([#2288](https://github.com/leanprover-community/mathlib/pull/2288))

### [2020-03-30 06:25:08](https://github.com/leanprover-community/mathlib/commit/9288d10)
chore(scripts): update nolints.txt

### [2020-03-30 05:50:58](https://github.com/leanprover-community/mathlib/commit/51553e3)
chore(data/set/lattice): use dot syntax for `disjoint.*` ([#2282](https://github.com/leanprover-community/mathlib/pull/2282))

### [2020-03-30 03:22:11](https://github.com/leanprover-community/mathlib/commit/cf64860)
chore(*): remove 'using_well_founded wf_tacs', fixed in core ([#2280](https://github.com/leanprover-community/mathlib/pull/2280))

### [2020-03-30 00:45:51](https://github.com/leanprover-community/mathlib/commit/8c1e32f)
chore(scripts): update nolints.txt

### [2020-03-30 00:11:57](https://github.com/leanprover-community/mathlib/commit/7dad872)
feat(ci): try fetching olean caches from older commits ([#2278](https://github.com/leanprover-community/mathlib/pull/2278))
* feat(ci): try fetching older branch oleans
* docstring edits for set_theory.surreal
* debug
* debug 2
* formatting
* try fetching
* just increase depth
* improve script, improve surreal docstrings
* env context
* quieter curl
* fix overwriting
* git clean
* ci test: delete surreal.lean
* fix env var GIT_HISTORY_DEPTH
* add back surreal
* reviewer comments

### [2020-03-29 21:31:54](https://github.com/leanprover-community/mathlib/commit/c14c84e)
chore(topology/algebra/ordered): `le_of_tendsto`: use `∀ᶠ`, add primed versions ([#2270](https://github.com/leanprover-community/mathlib/pull/2270))
Also fix two typos in `order/filter/basic`

### [2020-03-29 19:03:26](https://github.com/leanprover-community/mathlib/commit/8b679d9)
fix(tactic/squeeze): make suggestion at correct location ([#2279](https://github.com/leanprover-community/mathlib/pull/2279))
Fixes [#2267](https://github.com/leanprover-community/mathlib/pull/2267).

### [2020-03-29 16:22:44](https://github.com/leanprover-community/mathlib/commit/38544f1)
feat(tactic/core): basic interaction monad functions ([#1658](https://github.com/leanprover-community/mathlib/pull/1658))
* feat(tactic/core): basic interaction monad functions
* review
* remove get_result
* update comments
* whitespace
* american spelling

### [2020-03-29 13:46:46](https://github.com/leanprover-community/mathlib/commit/c4fb403)
fix(tactic/core): remove all_goals option from apply_any ([#2275](https://github.com/leanprover-community/mathlib/pull/2275))
* fix(tactic/core): remove all_goals option from any_apply
* remove unnecessary imports

### [2020-03-29 11:19:27](https://github.com/leanprover-community/mathlib/commit/da8b23f)
chore(data/opposite): two trivial lemmas ([#2274](https://github.com/leanprover-community/mathlib/pull/2274))

### [2020-03-29 08:42:21](https://github.com/leanprover-community/mathlib/commit/79880e8)
chore(data/fintype/intervals): `simp` `Ico_*_card` lemmas ([#2271](https://github.com/leanprover-community/mathlib/pull/2271))

### [2020-03-29 05:46:53](https://github.com/leanprover-community/mathlib/commit/5d9e7f5)
feat(analysis/calculus/fderiv): define `has_strict_fderiv_at` ([#2249](https://github.com/leanprover-community/mathlib/pull/2249))
* Move code aroud
* general constructions (product, chain rule) before arithmetic;
* bundled `E →L[𝕜] F` maps before unbundled
* Use `maps_to` instead of `f '' _ ⊆ _`
* feat(analysis/calculus/fderiv): define `has_strict_fderiv_at`
Prove strict differentiability of all functions found in this file, cleanup.
* Update src/analysis/calculus/fderiv.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Docs, var name

### [2020-03-29 03:24:03](https://github.com/leanprover-community/mathlib/commit/de8c207)
chore(scripts): update nolints.txt

### [2020-03-29 02:52:21](https://github.com/leanprover-community/mathlib/commit/8454c10)
doc(ring_theory/noetherian): add docstring, normalise notation ([#2219](https://github.com/leanprover-community/mathlib/pull/2219))
* change notation; add module docstring
* adding reference to A-M
* Update src/ring_theory/noetherian.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Apply suggestions from code review

### [2020-03-29 00:11:06](https://github.com/leanprover-community/mathlib/commit/ecdb138)
feat(category/equiv_functor): type-level functoriality w.r.t. equiv ([#2255](https://github.com/leanprover-community/mathlib/pull/2255))
* feat(data/equiv/functor): bifunctor.map_equiv
* start
* sketch of equiv_functor
* update
* removing unimpressive inhabited example; easier later
* omit
* revert unnecessary change
* fix doc-string
* fix names
* finish fix

### [2020-03-28 21:19:19](https://github.com/leanprover-community/mathlib/commit/d500210)
feat(algebra/big_operators): missing lemmas ([#2259](https://github.com/leanprover-community/mathlib/pull/2259))

### [2020-03-28 18:32:12](https://github.com/leanprover-community/mathlib/commit/ad53e0b)
feat(tactic/solve_by_elim): add accept parameter to prune tree search ([#2245](https://github.com/leanprover-community/mathlib/pull/2245))
* chore(tactic/solve_by_elim): cleanup
* cleanup
* what happened to my commit?
* fix
* fix
* fixed?
* Tweak comments
* feat(tactic/solve_by_elim): add accept parameter to prune tree search
* when called with empty lemmas, use the same default set as the interactive tactic
* stop cheating with [] ~ none
* indenting
* various
* various
* docstring
* fix docstrings
* more docs
* docs
* fix doc-strings
* improve documentation of accept, and add doc-string
* improve docs
* try again with documentation
* clarify when accept runs
* Update src/tactic/solve_by_elim.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update src/tactic/solve_by_elim.lean
* Update src/tactic/solve_by_elim.lean

### [2020-03-28 17:37:54](https://github.com/leanprover-community/mathlib/commit/0187cb5)
fix(scripts/deploy_docs.sh): cd before git log ([#2264](https://github.com/leanprover-community/mathlib/pull/2264))
* fix(scripts/deploy_docs.sh): cd before git log
* Update scripts/deploy_docs.sh

### [2020-03-28 12:46:28](https://github.com/leanprover-community/mathlib/commit/17f8340)
chore(data/equiv/basic): simp to_fun to coe ([#2256](https://github.com/leanprover-community/mathlib/pull/2256))
* chore(data/equiv/basic): simp to_fun to coe
* fix proofs
* Update src/data/equiv/basic.lean
* fix proof
* partially removing to_fun
* finish switching to coercions

### [2020-03-28 06:05:30](https://github.com/leanprover-community/mathlib/commit/d470ae7)
fix(tactic/squeeze): do not fail when closing the goal ([#2262](https://github.com/leanprover-community/mathlib/pull/2262))

### [2020-03-28 03:34:11](https://github.com/leanprover-community/mathlib/commit/6732788)
feat(analysis/normed_space/operator_norm): a few more estimates ([#2233](https://github.com/leanprover-community/mathlib/pull/2233))
* feat(*): a few more theorems about `unique` and `subsingleton`
* Fix compile, fix two non-terminate `simp`s
* Update src/topology/metric_space/antilipschitz.lean
This lemma will go to another PR
* feat(analysis/normed_space/operator_norm): a few more estimates
* `le_op_norm_of_le` : `∥x∥ ≤ c → ∥f x∥ ≤ ∥f∥ * c`;
* `norm_id` → `norm_id_le`, new `norm_id` assumes `∃ x : E, x ≠ 0`
* estimates on the norm of `e : E ≃L[𝕜] F`` and `e.symm`.
* rename `(anti)lipschitz_with.to_inverse` to `to_right_inverse`

### [2020-03-28 02:36:23](https://github.com/leanprover-community/mathlib/commit/1b13ccd)
chore(scripts/deploy_docs.sh): skip gen_docs if already built ([#2263](https://github.com/leanprover-community/mathlib/pull/2263))
* chore(scripts/deploy_docs.sh): skip gen_docs if already built
* Update scripts/deploy_docs.sh

### [2020-03-28 00:46:23](https://github.com/leanprover-community/mathlib/commit/211c5d1)
chore(data/int/basic): change instance order ([#2257](https://github.com/leanprover-community/mathlib/pull/2257))

### [2020-03-27 22:08:58](https://github.com/leanprover-community/mathlib/commit/3c0b35c)
chore(scripts): update nolints.txt

### [2020-03-27 21:37:51](https://github.com/leanprover-community/mathlib/commit/d0a8507)
feat(algebra/ring): generalize mul_ite ([#2223](https://github.com/leanprover-community/mathlib/pull/2223))
* feat(algebra/ring): generalize mul_ite
* fix proofs
* going off the deep-end
* cleaning up
* much better
* getting there
* no new congr lemma
* oops
* ...
* to_additive
* removing bad simp lemmas again...
* fix proof
* fix'
* oops
* Update src/algebra/ring.lean
* err.. marking simp again, because I can't remember what goes wrong and need CI to compile for me
* handing it back to CI for another try
* fix prod_ite as well
* cast_ite
* gross fix for quadratic reciprocity argument
* remove simp from add_ite, add comment

### [2020-03-27 18:48:08](https://github.com/leanprover-community/mathlib/commit/786c737)
feat(logic/basic): trivial transport lemmas ([#2254](https://github.com/leanprover-community/mathlib/pull/2254))
* feat(logic/basic): trivial transport lemmas
* oops

### [2020-03-27 16:08:17](https://github.com/leanprover-community/mathlib/commit/451de27)
chore(tactic/lint): typo ([#2253](https://github.com/leanprover-community/mathlib/pull/2253))

### [2020-03-27 13:19:03](https://github.com/leanprover-community/mathlib/commit/21ad1d3)
chore(tactic/*): update tags ([#2224](https://github.com/leanprover-community/mathlib/pull/2224))
* add missing tactic tags
* add missing command tags
* add missing hole command tags
* add missing attribute tags
* combine tags 'type class' and 'type classes'
* combine tags 'logical manipulation' and 'logic'
* attribute additions and changes
* more tag updates
* hypothesis management -> context management
* remove 'simplification', add more tags
* classical reasoning -> classical logic
* substitution -> rewrite
* normalization -> simplification

### [2020-03-27 12:12:17](https://github.com/leanprover-community/mathlib/commit/d3cbd4d)
chore(ci): update nolints before docs and leanchecker ([#2250](https://github.com/leanprover-community/mathlib/pull/2250))
* Update build.yml
* run lint+tests if build step succeeds (see [#2250](https://github.com/leanprover-community/mathlib/pull/2250)) ([#2252](https://github.com/leanprover-community/mathlib/pull/2252))
* run lint+tests if build succeeds
* move lint (and nolints.txt) before tests
* Apply suggestions from code review

### [2020-03-26 16:57:24-04:00](https://github.com/leanprover-community/mathlib/commit/de39b9a)
chore(.mergify.yml): cleanup ([#2248](https://github.com/leanprover-community/mathlib/pull/2248))
remove [skip-ci] and pr bits that no longer apply.

### [2020-03-26 20:55:31](https://github.com/leanprover-community/mathlib/commit/2fbf007)
doc(docs/install/project.md): mention that projects are git repositories ([#2244](https://github.com/leanprover-community/mathlib/pull/2244))

### [2020-03-26 20:00:59](https://github.com/leanprover-community/mathlib/commit/75b4ee8)
feat(data/equiv/local_equiv): construct from `bij_on` or `inj_on` ([#2232](https://github.com/leanprover-community/mathlib/pull/2232))
* feat(data/equiv/local_equiv): construct from `bij_on` or `inj_on`
Also fix usage of `nonempty` vs `inhabited` in `set/function`. Linter
didn't catch these bugs because the types use the `.to_nonempty`
projection of the `[inhabited]` arguments.
* Add `simps`/`simp` attrs

### [2020-03-26 17:30:38](https://github.com/leanprover-community/mathlib/commit/8943351)
feat(topology/algebra/module): define `fst` and `snd`, review ([#2247](https://github.com/leanprover-community/mathlib/pull/2247))
* feat(topology/algebra/module): define `fst` and `snd`, review
* Fix compile

### [2020-03-26 14:41:41](https://github.com/leanprover-community/mathlib/commit/5b44363)
chore(scripts): update nolints.txt

### [2020-03-26 13:38:06](https://github.com/leanprover-community/mathlib/commit/0fc4e6a)
refactor(data/set/function): move `function.restrict` to `set`, redefine ([#2243](https://github.com/leanprover-community/mathlib/pull/2243))
* refactor(data/set/function): move `function.restrict` to `set`, redefine
We had `subtype.restrict` and `function.restrict` both defined in the
same way using `subtype.val`. This PR moves `function.restrict` to
`set.restrict` and makes it use `coe` instead of `subtype.val`.
* Fix compile
* Update src/data/set/function.lean

### [2020-03-26 11:00:48](https://github.com/leanprover-community/mathlib/commit/fa36a8e)
chore(scripts): update nolints.txt

### [2020-03-26 10:05:36](https://github.com/leanprover-community/mathlib/commit/ea10e17)
feat(data/equiv/functor): bifunctor.map_equiv ([#2241](https://github.com/leanprover-community/mathlib/pull/2241))
* feat(data/equiv/functor): bifunctor.map_equiv
* add documentation, and make the function an explicit argument
* Update src/data/equiv/functor.lean

### [2020-03-26 07:48:43](https://github.com/leanprover-community/mathlib/commit/ab33237)
chore(scripts): update nolints.txt

### [2020-03-26 06:56:37](https://github.com/leanprover-community/mathlib/commit/dbc4284)
feat(tactic/squeeze): improve suggestion of `cases x; squeeze_simp` ([#2218](https://github.com/leanprover-community/mathlib/pull/2218))
* feat(tactic/squeeze): improve produced argument list and format
* feat(tactic/squeeze): combine suggestions of repeated executions
* add documentation
* remove dead code
* suggestion from reviewers
* Apply suggestions from code review
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Update squeeze.lean
* Apply suggestions from code review
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* simplify and remove comparison of proof terms
* simplify goal comparison data structure
* add documentation and fix meta-variable handling
* add example
* fix tests
* move tests
* use binders with trivial names to abstract meta variables

### [2020-03-26 04:20:05](https://github.com/leanprover-community/mathlib/commit/30146a0)
chore(tactic/solve_by_elim): refactor ([#2222](https://github.com/leanprover-community/mathlib/pull/2222))
* chore(tactic/solve_by_elim): cleanup
* cleanup
* what happened to my commit?
* fix
* fix
* fixed?
* Tweak comments
* when called with empty lemmas, use the same default set as the interactive tactic
* stop cheating with [] ~ none
* indenting
* docstring
* fix docstrings

### [2020-03-26 01:26:44](https://github.com/leanprover-community/mathlib/commit/2755eae)
chore(ci): only run on push ([#2237](https://github.com/leanprover-community/mathlib/pull/2237))
* chore(ci): only run on push
* update contribution docs

### [2020-03-26 00:32:53](https://github.com/leanprover-community/mathlib/commit/6e6c81a)
feat(algebra/homology): chain complexes ([#2174](https://github.com/leanprover-community/mathlib/pull/2174))
* thoughts on chain complexes
* minor
* feat(category_theory): split epis and monos, and a result about (co)projections
* total functor faithful
* homology!
* remove lint
* something something homology
* comment out broken stuff
* adding comments
* various
* rewrite
* fixes
* Update src/category_theory/epi_mono.lean
* Update src/category_theory/epi_mono.lean
* Update src/category_theory/epi_mono.lean
* better use of ext
* feat(category_theory): subsingleton (has_zero_morphisms)
* revert some independent changes moved to [#2180](https://github.com/leanprover-community/mathlib/pull/2180)
* revert some independent changes moved to [#2181](https://github.com/leanprover-community/mathlib/pull/2181)
* revert independent changes moved to [#2182](https://github.com/leanprover-community/mathlib/pull/2182)
* fix
* Apply suggestions from code review
Co-Authored-By: Johan Commelin <johan@commelin.net>
* changes from review
* module docs
* various
* Update src/category_theory/shift.lean
Co-Authored-By: Kevin Buzzard <k.buzzard@imperial.ac.uk>
* various
* various fixes
* fix
* all the minor suggestions
Co-Authored-By: Markus Himmel <markus@himmel-villmar.de>
* ugh... fix reverting stuff from [#2180](https://github.com/leanprover-community/mathlib/pull/2180)
* off by one
* various
* use abbreviation
* chain as well as cochain
* satisfy the linter
* some simp lemmas
* simp lemmas

### [2020-03-25 21:56:35](https://github.com/leanprover-community/mathlib/commit/e04892e)
feat(topology/metric_space/isometry): add_left/right, neg ([#2234](https://github.com/leanprover-community/mathlib/pull/2234))
Also add some lemmas from `equiv` namespace to `isometric`.

### [2020-03-25 19:18:04](https://github.com/leanprover-community/mathlib/commit/bb01537)
feat(topology/local_homeomorph): a few facts about `local_homeomorph` ([#2231](https://github.com/leanprover-community/mathlib/pull/2231))
* `eventually_inv_right`, `eventually_inv_left`
* `is_O_congr`, `is_o_congr`

### [2020-03-25 16:34:50](https://github.com/leanprover-community/mathlib/commit/05aa955)
chore(scripts): update nolints.txt

### [2020-03-25 15:44:21](https://github.com/leanprover-community/mathlib/commit/bedb810)
feat(*): a few more theorems about `unique` and `subsingleton` ([#2230](https://github.com/leanprover-community/mathlib/pull/2230))
* feat(*): a few more theorems about `unique` and `subsingleton`
* Fix compile, fix two non-terminate `simp`s
* Update src/topology/metric_space/antilipschitz.lean
This lemma will go to another PR

### [2020-03-25 13:11:33](https://github.com/leanprover-community/mathlib/commit/1eae0be)
feat(data/equiv): pi_congr ([#2204](https://github.com/leanprover-community/mathlib/pull/2204))
* feat(data/equiv): pi_congr
* docstrings
* change case for consistency
* tidying up
* switching names
* fixes
* Update src/data/equiv/basic.lean
* implicit arguments

### [2020-03-25 10:30:42](https://github.com/leanprover-community/mathlib/commit/83014bf)
chore(README): add Bryan; alphabetize ([#2238](https://github.com/leanprover-community/mathlib/pull/2238))

### [2020-03-25 03:10:56](https://github.com/leanprover-community/mathlib/commit/d9083bc)
chore(algebra/ordered_field): merge `inv_pos` / `zero_lt_inv` with `inv_pos'` / `inv_neg` ([#2226](https://github.com/leanprover-community/mathlib/pull/2226))
* chore(algebra/ordered_field): merge `inv_pos` / `zero_lt_inv` with `inv_pos'` / `inv_neg`
Also move some lemmas to `linear_ordered_field`
* Update src/data/real/hyperreal.lean
* Fix compile
* Actually fix compile of `data/real/hyperreal`

### [2020-03-25 00:53:41](https://github.com/leanprover-community/mathlib/commit/24b82c9)
feat(tactic/core): trace_if_enabled ([#2209](https://github.com/leanprover-community/mathlib/pull/2209))
* feat(tactic/core): trace_for
* typo
* oops
* oops
* rename to trace_if_enabled
* trace_state_if_enabled

### [2020-03-24 22:07:53](https://github.com/leanprover-community/mathlib/commit/efdc850)
feat(tactic/conv/apply_congr): using congruence lemmas inside conv ([#2221](https://github.com/leanprover-community/mathlib/pull/2221))
* Update interactive.lean
Added Keeley Hoeks Zoom tactic.
* Add files via upload
Added operand.lean file to the tactic folder.
* Add files via upload
Added the test files for zoom and operand.
* Rename operand_test.lean to operand.lean
* Update and rename zoom_test.lean to zoom.lean
Fixed the imports
* Update operand.lean
* Update tactics.md
* Update operand.lean
Fixed the lamda problem.
* Update operand.lean
Added tests without lamdas
* Update operand.lean
Added header
* Update operand.lean
Added header
* Update operand.lean
deleted zoom
* Update zoom.lean
Added comment to self
* Update operand.lean
Added doc_string to operand
* Update interactive.lean
Added doc_string to zoom
* Update tactics.md
Fixed colon and brackets in operand doc
* Update operand.lean
Fixed colon placements and brackets
* merge
* feat(tactic/converter/apply_congr): apply congruence lemmas in conv
* last example
* fix docs
* Apply suggestions from code review
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* remove docs from tactics.md
* merge doc comment fragments
* import in tactic.basic
* docs
* add to conv doc tactic

### [2020-03-24 18:51:00](https://github.com/leanprover-community/mathlib/commit/5437b10)
feat(tactic/show_term): show_term { t } prints the term constructed by t ([#2227](https://github.com/leanprover-community/mathlib/pull/2227))
* feat(tactic): show_term { t } prints the term constructed by t
* add to tactic.basic
* move tests
* silencing
* Update src/tactic/show_term.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* clean up
* remove tests
* Update src/tactic/show_term.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>

### [2020-03-24 16:01:34](https://github.com/leanprover-community/mathlib/commit/5f376b2)
feat(data/equiv): sigma_congr ([#2205](https://github.com/leanprover-community/mathlib/pull/2205))

### [2020-03-24 12:31:39](https://github.com/leanprover-community/mathlib/commit/bb6e1d4)
chore(README,docs/*): replace tactic doc files with links to mathlib docs ([#2225](https://github.com/leanprover-community/mathlib/pull/2225))
* chore(README,doc/*): replace tactic doc files with links to mathlib docs
Other cleanup:
- replaced leanprover/lean and leanprover/mathlib with
  leanprover-community/lean and leanprover-community/mathlib
- updated pull request template and instructions for contributors with
  info about tactic doc entries
- formatting / style for simp.md and tactic_writing.md
- fixed broken link in category_theory.category.default
* reword contributor suggestion for tactic tests
* reviewer comments

### [2020-03-24 09:46:52](https://github.com/leanprover-community/mathlib/commit/b504430)
feat(linear_algebra): add range_le_ker_iff ([#2229](https://github.com/leanprover-community/mathlib/pull/2229))

### [2020-03-23 18:23:19](https://github.com/leanprover-community/mathlib/commit/6a7e55e)
chore(scripts): update nolints.txt

### [2020-03-23 17:30:32](https://github.com/leanprover-community/mathlib/commit/9a9794d)
doc(data/int/gcd): attribution + module doc ([#2217](https://github.com/leanprover-community/mathlib/pull/2217))
* doc(data/int/gcd): attribution + module doc
* reword

### [2020-03-23 14:57:34](https://github.com/leanprover-community/mathlib/commit/9832fba)
refactor(topology/metric_space/contracting): redefine using emetric ([#2070](https://github.com/leanprover-community/mathlib/pull/2070))
* refactor(topology/metric_space/contracting): redefine using emetric
* Fix a typo produced by "copy+paste"
* Fix compile
* Refactor `efixed_point`, `efixed_point'`
* Prove a version of Banach fixed point theorem for a map contracting
  on a complete forward-invariant set.
* Separately prove "primed" lemmas.
I Tried to define `efixed_point'` in terms of `efixed_point` and
failed: every time I use it, it generates a goal `complete_space ↥s`.
So, I decided to deduce `exists_fixed_point'` from
`exists_fixed_point`, then use it in the proofs.

### [2020-03-23 12:25:53](https://github.com/leanprover-community/mathlib/commit/25df50e)
chore(scripts): update nolints.txt

### [2020-03-23 11:21:48](https://github.com/leanprover-community/mathlib/commit/5b2c952)
feat(analysis/convex.cone): prove M. Riesz extension theorem, Hahn-Banach theorem ([#2120](https://github.com/leanprover-community/mathlib/pull/2120))
* feat(analysis/convex.cone): prove M. Riesz extension theorem
WIP
* Complete the proof
TODO: move many facts to `linear_algebra/basic`,
fix possible build failures in other files
* Fix compile of `analysis/convex/cone`
* Cleanup, rewrite using `linear_pmap`s
* Deduce Hahn-Banach theorem from M. Riesz extension theorem
* Fix lint
* Apply suggestions from code review [skip_ci]
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Expand comments, prove properties of `convex.to_cone`.
* Docstrings
* Apply suggestions from code review
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/analysis/convex/cone.lean
* Update src/linear_algebra/basic.lean

### [2020-03-23 04:27:27](https://github.com/leanprover-community/mathlib/commit/d3d78a9)
chore(ring_theory/algebra): generalize restrict_scalars to noncommutative algebras ([#2216](https://github.com/leanprover-community/mathlib/pull/2216))

### [2020-03-23 01:53:56](https://github.com/leanprover-community/mathlib/commit/fe40a15)
chore(scripts): update nolints.txt

### [2020-03-23 01:05:38](https://github.com/leanprover-community/mathlib/commit/6aa5572)
feat(algebra/module): `f : E →+ F` is `ℚ`-linear ([#2215](https://github.com/leanprover-community/mathlib/pull/2215))
* feat(algebra/module): `f : E →+ F` is `ℚ`-linear
Also cleanup similar lemmas about `ℕ` and `ℤ`.
* Fix a typo

### [2020-03-22 22:10:26](https://github.com/leanprover-community/mathlib/commit/b9ee94d)
chore(scripts): update nolints.txt

### [2020-03-22 21:15:30](https://github.com/leanprover-community/mathlib/commit/7f103fd)
fix(tactic/transport): make `to_additive` copy `protected`status ([#2212](https://github.com/leanprover-community/mathlib/pull/2212))
* fix(tactic/transport): make `to_additive` copy `protected`status
Fixes [#2210](https://github.com/leanprover-community/mathlib/pull/2210), also slightly cleanup `algebra/group/units`
* Fix compile (protected `finset.sum`)
* Fix usage of `finset.sum`
* Update src/tactic/transport.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* fix build

### [2020-03-22 17:01:05](https://github.com/leanprover-community/mathlib/commit/6febc8c)
feat(tactic/doc_commands): allow doc strings on add_tactic_doc ([#2201](https://github.com/leanprover-community/mathlib/pull/2201))
* feat(tactic/doc_commands): allow doc strings on add_tactic_doc
* Add link to Lean issue.
* Update src/tactic/doc_commands.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Change all `description :=` to docstrings.
* Change suggested by Bryan.
* Use docstrings in library_note
* Factor out `tactic.eval_pexpr`.
* Add add_decl_doc command.
* Update docs/contribute/doc.md
* Update src/tactic/doc_commands.lean
* Update src/tactic/doc_commands.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>

### [2020-03-22 13:55:54](https://github.com/leanprover-community/mathlib/commit/4e46b30)
chore(scripts): update nolints.txt

### [2020-03-22 13:06:37](https://github.com/leanprover-community/mathlib/commit/7d02c23)
chore(linear_algebra/*): rename copair, pair to coprod, prod ([#2213](https://github.com/leanprover-community/mathlib/pull/2213))
* chore(linear_algebra/*): rename copair, pair to coprod, prod
* add back mistakenly deleted lemma
* fix sensitivity, change comments to module docs
* docstrings, linting
* Update archive/sensitivity.lean

### [2020-03-22 08:44:10](https://github.com/leanprover-community/mathlib/commit/3a71499)
feat(ring_theory/algebra) : generalize `rat.algebra_rat` to `division_ring` ([#2208](https://github.com/leanprover-community/mathlib/pull/2208))
Other changes:
* add lemmas about field inverse to `algebra/semiconj` and `algebra/commute`;
* drop `rat.cast`, define `instance : has_coe` right away to avoid
  accidental use of `rat.cast` in theorems;
* define `rat.cast_hom` instead of `is_ring_hom rat.cast`;
* generalize some theorems about from `field` to `division_ring`.

### [2020-03-22 04:38:42](https://github.com/leanprover-community/mathlib/commit/9485a85)
fix(linear_algebra/basic): make R explicit in linear_equiv.refl ([#2161](https://github.com/leanprover-community/mathlib/pull/2161))
* fix(linear_algebra/basic): make R explicit in linear_equiv.refl
* getting mathlib to compile again
* better variablism

### [2020-03-22 02:00:48](https://github.com/leanprover-community/mathlib/commit/19de416)
doc(ring_theory/adjoin_root): add docstring ([#2211](https://github.com/leanprover-community/mathlib/pull/2211))
* docstring for adjoin_root
* adding some quotes

### [2020-03-21 14:18:51-07:00](https://github.com/leanprover-community/mathlib/commit/09401b7)
revert accidental push to master

### [2020-03-21 14:00:51-07:00](https://github.com/leanprover-community/mathlib/commit/3375126)
feat(tactic/core): trace_for

### [2020-03-21 19:24:58](https://github.com/leanprover-community/mathlib/commit/af0cf30)
chore(scripts): update nolints.txt

### [2020-03-21 18:41:30](https://github.com/leanprover-community/mathlib/commit/0bd8b94)
refactor(scripts/mk_nolint): produce nolints.txt file during linting ([#2194](https://github.com/leanprover-community/mathlib/pull/2194))
* Factor out code to determine automatically-generated declarations.
* Mark bool.decidable_eq and decidable.to_bool as [inline]
* Execute linters in parallel.
* Add lint_mathlib.lean script.
* Switch CI to new lint_mathlib.lean script.
* Make linter fail.
* Revert "Make linter fail."
This reverts commit 8b509c5815d862d0d060eac407cf6d22d743f960.
* Remove one line from nolints.txt
* Change shebang in rm_all.sh to be nixos-compatible
* Disable parallel checking.
* Make linter fail.
* Revert "Make linter fail."
This reverts commit 8f5ec62030ecaec93d01981b273c2a737d67eddf.
* Move is_auto_decl to meta/expr.lean
* Remove list.mmap_async
* Factor out name.from_string

### [2020-03-21 10:35:34](https://github.com/leanprover-community/mathlib/commit/dd85db0)
doc(docs/contribute/index.md): remove obsolete recommendation to use lean-3.7.2 branch ([#2206](https://github.com/leanprover-community/mathlib/pull/2206))

### [2020-03-21 08:46:38](https://github.com/leanprover-community/mathlib/commit/bc84a20)
chore(leanpkg.toml): Lean 3.7.2c ([#2203](https://github.com/leanprover-community/mathlib/pull/2203))
* chore(leanpkg.toml): Lean 3.7.2c
Lean 3.7.1c had a bug that prevented Lean on windows from importing oleans properly (see https://github.com/leanprover-community/lean/pull/155). This is fixed in Lean 3.7.2c.
* update contribute/index.md

### [2020-03-21 02:10:50](https://github.com/leanprover-community/mathlib/commit/34bac8d)
feat(category_theory): add naturality_assoc simp lemma ([#2200](https://github.com/leanprover-community/mathlib/pull/2200))

### [2020-03-20 23:38:07](https://github.com/leanprover-community/mathlib/commit/99ba8f4)
chore(category_theory): change monoidal_of_has_finite_products to use binary products ([#2190](https://github.com/leanprover-community/mathlib/pull/2190))
* chore(category_theory): change monoidal_of_has_finite_products to use binary products
* remove some simp annotations for now
* fixes

### [2020-03-20 21:22:50](https://github.com/leanprover-community/mathlib/commit/9420167)
feat(category_theory): unbundled functors and lax monoidal functors ([#2193](https://github.com/leanprover-community/mathlib/pull/2193))
* feat(category_theory): unbundled functors and lax monoidal functors
* doc string

### [2020-03-20 18:53:45](https://github.com/leanprover-community/mathlib/commit/b224943)
chore(scripts): update nolints.txt

### [2020-03-20 17:26:39](https://github.com/leanprover-community/mathlib/commit/8d44098)
feat(finsupp): move convolution product to type wrapper `add_monoid_algebra`. ([#2135](https://github.com/leanprover-community/mathlib/pull/2135))
* pulling out convolution product
* various
* chore(ring_theory/polynomial): refactor proof of is_noetherian_ring_fin
* not there yet
* feat(ring_theory/polynomial): refactor of is_integral_domain_fin
* fix
* ..
* refactor
* fix
* yay
* cleanup
* satisfying the linter
* linter
* improving documentation
* add distrib instance for pointwise multiplication
* move files per Johan's suggestion
* fix import
* Update src/data/polynomial.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* type annotation

### [2020-03-20 15:01:46](https://github.com/leanprover-community/mathlib/commit/0f1b465)
feat(category_theory/limits): the isomorphism expressing preservation of chosen limits ([#2192](https://github.com/leanprover-community/mathlib/pull/2192))
* feat(category_theory/limits): the isomorphism expressing preservation of chosen limits
* Update src/category_theory/limits/limits.lean

### [2020-03-20 12:24:26](https://github.com/leanprover-community/mathlib/commit/c66c4af)
chore(algebra/Module/monoidal): add the simp lemmas for unitors and associativity ([#2196](https://github.com/leanprover-community/mathlib/pull/2196))
* feat(algebra/category/Module/monoidal): simp lemmas
* oops
* depressingly easy
* order of arguments

### [2020-03-20 10:05:42](https://github.com/leanprover-community/mathlib/commit/d93e0dd)
chore(category_theory): missing simp lemmas ([#2188](https://github.com/leanprover-community/mathlib/pull/2188))
* chore(category_theory): missing simp lemmas
* Apply suggestions from code review
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2020-03-20 07:32:29](https://github.com/leanprover-community/mathlib/commit/b4e6313)
feat(category_theory): subsingleton (has_zero_morphisms) ([#2180](https://github.com/leanprover-community/mathlib/pull/2180))
* feat(category_theory): subsingleton (has_zero_morphisms)
* fix
* Update src/category_theory/limits/shapes/zero.lean
Co-Authored-By: Markus Himmel <markus@himmel-villmar.de>
* Update src/category_theory/limits/shapes/zero.lean
Co-Authored-By: Markus Himmel <markus@himmel-villmar.de>
* non-terminal simp
* add warning message
* Update src/category_theory/discrete_category.lean
Co-Authored-By: Markus Himmel <markus@himmel-villmar.de>
* Apply suggestions from code review

### [2020-03-20 05:08:55](https://github.com/leanprover-community/mathlib/commit/cc04132)
chore(scripts): update nolints.txt

### [2020-03-20 03:59:59](https://github.com/leanprover-community/mathlib/commit/6c97ce0)
feat(category_theory): some natural isomorphisms related to composition by functors ([#2189](https://github.com/leanprover-community/mathlib/pull/2189))
* feat(category_theory): some natural isomorphisms related to composition by functors
* tidy up
* cleanup
* fix
* better design

### [2020-03-20 01:35:59](https://github.com/leanprover-community/mathlib/commit/d12bbc0)
feat(data/zmod): lemmas about totient and zmod ([#2158](https://github.com/leanprover-community/mathlib/pull/2158))
* feat(data/zmod): lemmas about totient and zmod
* docstring
* Changes based on Johan's comments
* fix build
* subsingleton (units(zmod 2))

### [2020-03-19 23:15:04](https://github.com/leanprover-community/mathlib/commit/3dd95a2)
chore(scripts): update nolints.txt

### [2020-03-19 21:56:33](https://github.com/leanprover-community/mathlib/commit/1a398a7)
docs(category_theory/limits): adding many docstrings ([#2185](https://github.com/leanprover-community/mathlib/pull/2185))
* lots of comments!
* remove #lint
* Apply suggestions from code review
lots of missing "co"s
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2020-03-19 18:52:34](https://github.com/leanprover-community/mathlib/commit/344a41e)
feat(data/finset): monotone bijection from fin k ([#2163](https://github.com/leanprover-community/mathlib/pull/2163))
* feat(data/finset): increasing bijection between fin k and an ordered finset
* fix build
* fix linter
* make argument explicit
* add equiv for fintype

### [2020-03-19 16:32:37](https://github.com/leanprover-community/mathlib/commit/b3ef685)
chore(scripts): update nolints.txt

### [2020-03-19 15:12:14](https://github.com/leanprover-community/mathlib/commit/9dbc606)
refactor(*): drop `lattice` namespace ([#2166](https://github.com/leanprover-community/mathlib/pull/2166))
* refactor(*): drop `lattice` namespace
Other changes:
* rename `*neg*` to `*compl*` in `boolean_algebra`.
I didn't touch `sub` in `boolean_algebra`; should it become `sdiff`?
* Fix some compile failures
* Fix the rest of compile failures
Drop `real.Sup` and `real.Inf`, define instances instead.
* fix build
* fix build
* Fix build

### [2020-03-19 10:59:44](https://github.com/leanprover-community/mathlib/commit/a20f378)
chore(category_theory/images): fix some minor problems ([#2182](https://github.com/leanprover-community/mathlib/pull/2182))
* chore(category_theory/images): fix some minor problems
* minor
* oops, misplaced comment

### [2020-03-19 08:46:53](https://github.com/leanprover-community/mathlib/commit/4bc32ae)
feat(category_theory): regular monos ([#2154](https://github.com/leanprover-community/mathlib/pull/2154))
* feat(category_theory): regular and normal monos
* fixes
* Apply suggestions from code review
Co-Authored-By: Markus Himmel <markus@himmel-villmar.de>
* shorter proofs
* typos, thanks
Co-Authored-By: Markus Himmel <markus@himmel-villmar.de>
* Update src/category_theory/limits/shapes/regular_mono.lean
Co-Authored-By: Markus Himmel <markus@himmel-villmar.de>
* linting

### [2020-03-19 06:18:29](https://github.com/leanprover-community/mathlib/commit/445e332)
chore(category_theory/isomorphism): use @[simps] ([#2181](https://github.com/leanprover-community/mathlib/pull/2181))

### [2020-03-19 03:47:29](https://github.com/leanprover-community/mathlib/commit/e2b0e38)
chore(category_theory/binary_products): tweak spacing in notation ([#2184](https://github.com/leanprover-community/mathlib/pull/2184))

### [2020-03-19 01:12:44](https://github.com/leanprover-community/mathlib/commit/034685b)
chore(scripts): update nolints.txt

### [2020-03-18 23:51:31](https://github.com/leanprover-community/mathlib/commit/00d9f1d)
feat(topology/algebra/infinite_sum): dot notation, cauchy sequences ([#2171](https://github.com/leanprover-community/mathlib/pull/2171))
* more material on infinite sums
* minor fixes
* cleanup
* yury's comments

### [2020-03-18 21:14:22](https://github.com/leanprover-community/mathlib/commit/e719f8e)
chore(*): switch to lean 3.7.1c ([#2106](https://github.com/leanprover-community/mathlib/pull/2106))
* fix(deprecated/group): remove dangerous instances
* Update Lean version to nightly.
* Remove composition instances for group homomorphisms.
* Remove dangerous is_submonoid instances.
* Flip instance arguments.
* Various Lean 3.7 fixes.
* Correctly use lemma.
* Use new elan 0.8.0 lean version name.
* Remove dangerous *.comp instances.
* Fix comp instance fallout.
* Fix more *.comp fallout
* Fix more *.comp fallout.
* More *.comp fallout.
* Fix *.comp fallout
* Fix *.comp fallout
* Port to has_attribute and copy_attribute changes.
* Fix monad_writer_adapter_trans instance.
* Revert 3.6 hacks.
* Update library note for *.comp morphisms.
* fix(scripts/deploy_docs.sh): use lean_version from mathlib leanpkg.toml
* Do not mention is_mul_hom.mul in library note.
* Update lean version to 3.7.0.
* Remove of_tactic'
* switch to 3.7.1c

### [2020-03-18 18:36:06](https://github.com/leanprover-community/mathlib/commit/69f7bf8)
chore(scripts): update nolints.txt

### [2020-03-18 17:04:44](https://github.com/leanprover-community/mathlib/commit/5f62d3b)
feat(topology/bounded_continuous_functions): more general uniform convergence ([#2165](https://github.com/leanprover-community/mathlib/pull/2165))
* feat(topology/buonded_continuous_functions): more general uniform convergence
* yury's comments

### [2020-03-18 14:55:37](https://github.com/leanprover-community/mathlib/commit/739e831)
feat(analysis/complex/exponential): real powers of nnreals ([#2164](https://github.com/leanprover-community/mathlib/pull/2164))
* feat(analysis/complex/exponential): real powers of nnreals
* cleanup
* mean inequalities in nnreal
* mean inequalities
* use < instead of >
* reviewer's comments

### [2020-03-18 03:19:02](https://github.com/leanprover-community/mathlib/commit/f07a1eb)
feat(category_theory): images in Ab and Type ([#2101](https://github.com/leanprover-community/mathlib/pull/2101))
* not stacked on top of limits/colimits
* comment
* add ext to add_monoid_hom.ext
* fix
* cleanup
* suggestions from review
* fix
* use more existing structure
* fix names
* oops
* linter

### [2020-03-18 00:03:33](https://github.com/leanprover-community/mathlib/commit/6af37d3)
fix(category_theory/limits): require explicit instances of has_zero_morphisms ([#2169](https://github.com/leanprover-community/mathlib/pull/2169))
* fix(category_theory/limits): require explicit instances of has_zero_morphisms
* Fix unused arguments

### [2020-03-17 14:49:48+01:00](https://github.com/leanprover-community/mathlib/commit/422f640)
fix(scripts/mk_nolint): fix error introduced by [#2090](https://github.com/leanprover-community/mathlib/pull/2090) ([#2170](https://github.com/leanprover-community/mathlib/pull/2170))

### [2020-03-17 03:38:32](https://github.com/leanprover-community/mathlib/commit/e94fef0)
feat(lint): run some linters on automatically generated declarations ([#2090](https://github.com/leanprover-community/mathlib/pull/2090))
* style(lint): remove double periods
remove spacing in the OK-results of #lint
add newline after ever failed result of #lint_mathlib (1 newline between two files, 2 newlines between two linters)
* run some linters on automatically generated declarations
* fix doc string
* fix mk_nolint
* fix test
* fix linter errors
also explain how to fix linter errors for automatically generated declarations
* fix linter errors

### [2020-03-17 01:31:51](https://github.com/leanprover-community/mathlib/commit/496939c)
feat(data/real/*nnreal): add division lemmas ([#2167](https://github.com/leanprover-community/mathlib/pull/2167))
* feat(data/real/*nnreal): add division lemmas
* fix build
* elim_cast
* another elim_cast

### [2020-03-16 23:16:44](https://github.com/leanprover-community/mathlib/commit/4754368)
feat(category_theory): split epis and monos, and a result about (co)projections ([#2146](https://github.com/leanprover-community/mathlib/pull/2146))
* feat(category_theory): split epis and monos, and a result about (co)projections
* rearranging
* reviewers' suggestions
* A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
* fix
* cleanup
* split_epi_coequalizes
* fix
* cleanup
* reduce priorities
* Update src/category_theory/epi_mono.lean
Co-Authored-By: Yury G. Kudryashov <urkud@urkud.name>
* Update src/category_theory/epi_mono.lean

### [2020-03-16 21:22:20](https://github.com/leanprover-community/mathlib/commit/bc087d8)
chore(scripts): update nolints.txt

### [2020-03-16 20:04:17](https://github.com/leanprover-community/mathlib/commit/7a5496f)
chore(order/liminf_limsup): lint and cleanup the file ([#2162](https://github.com/leanprover-community/mathlib/pull/2162))
* chore(order/liminf_limsup): lint and cleanup the file, add some statements
* use eventually_mono

### [2020-03-16 19:22:51](https://github.com/leanprover-community/mathlib/commit/007b575)
chore(scripts): update nolints.txt

### [2020-03-16 17:51:32](https://github.com/leanprover-community/mathlib/commit/42b92aa)
feat(tactic): command for adding tactic, command, and attribute documentation ([#2114](https://github.com/leanprover-community/mathlib/pull/2114))
* chore(*): switch to lean 3.6.0
* begin tactic_doc command
* merge add_tactic_doc with library_note
* fix library_note imports
* undo accidental revert
* better attribute description
* unneeded to_expr
* fix doc string attribution
* unicode input error
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* display and collect doc entries
* missing doc string
* update for lean 3.6
* document core tactics
I considered adding these as doc strings in core. But the entry for `conv` mentions mathlib-specific things.
* move tfae and rcases docs
* move rintros and obtain
* simpa
* move part of tactic.interactive
* move more of tactic.interactive
* finish tactic.interactive
* move omega
* move renaming tactics
* move more
* move norm_cast
* more
* move more
* doc commands in core + docstring tweaks
* abel, alias, cache
* elide, finish
* hint, linearith, pi_instances
* norm_num, rewrite
* ring, ring_exp
* solve_by_elim, suggest
* doc_commands, rcases
* ext
* explode, find
* lint
* tidy
* localized
* reassoc_axiom, replacer, restate_axiom, where
* simps
* markdown files
* interactive
* new additions
* revert changes to md files
* fix merge
* allow entries with different categories to share the same name
* better error messages
* fix merge
* linter errors
* use derive handler for inhabited instances
* shorten doc entry names after category fix
* copy simp.md to doc entry, tag: "simp" -> "simplification"
* update add_tactic_doc_command docstring and doc.md
* simp doc entry changed to its doc string
* Apply suggestions from code review
* doc: horizontal rules must be surrounded by new lines
* address reviewer suggestions
* Update docs/contribute/doc.md
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* fix add_tactic_doc_command docstring

### [2020-03-16 15:33:24](https://github.com/leanprover-community/mathlib/commit/04c7381)
doc(docs/install/windows): emphasize projects link ([#2150](https://github.com/leanprover-community/mathlib/pull/2150))
You can't use mathlib in the test project created in step 6. I've seen a couple of Windows users get tripped up here.

### [2020-03-16 14:46:06](https://github.com/leanprover-community/mathlib/commit/555528e)
feat(category_theory/image): comparison maps for precomposition ([#2153](https://github.com/leanprover-community/mathlib/pull/2153))
* feat(category_theory/image): comparison maps for precomposition
* remove duplicate argument
* unused argument

### [2020-03-16 09:18:06](https://github.com/leanprover-community/mathlib/commit/1e38cb1)
chore(scripts): update nolints.txt

### [2020-03-16 08:00:01](https://github.com/leanprover-community/mathlib/commit/ff84bf4)
feat(category_theory/monad/limits): forgetful creates colimits ([#2138](https://github.com/leanprover-community/mathlib/pull/2138))
* forgetful creates colimits
* tidy up proofs
* add docs
* suggestions from review

### [2020-03-16 05:54:25](https://github.com/leanprover-community/mathlib/commit/4aed862)
feat(analysis/normed_space/operator_norm): completeness of the space of operators ([#2160](https://github.com/leanprover-community/mathlib/pull/2160))
* feat(analysis/normed_space/operator_norm): completeness of the space of operators
* add some comments

### [2020-03-16 03:42:23](https://github.com/leanprover-community/mathlib/commit/d8e5d99)
feat(category_theory/limits): Convenience methods for building limit (co)forks ([#2155](https://github.com/leanprover-community/mathlib/pull/2155))
* feat(category_theory/limits): Convenience methods for building limit (co)forks
* Formatting
* Rework a proof about kernels
* feat(category_theory/limits): kernel forks

### [2020-03-16 01:31:06](https://github.com/leanprover-community/mathlib/commit/c240fcb)
feat(category_theory/limits): pullbacks from binary products and equalizers ([#2143](https://github.com/leanprover-community/mathlib/pull/2143))
* feat(category_theory/limits): derive has_binary_products from has_limit (pair X Y)
* Rename *_of_diagram to diagram_iso_*
* feat(category_theory/limits): pullbacks from binary products and equalizers
* Fix build
* Fix indentation
* typos
* Fix proof
* Remove some simp lemmas that were duplicated during merge

### [2020-03-15 23:30:43](https://github.com/leanprover-community/mathlib/commit/fbe2ce0)
feat(category_theory/limits): kernel forks ([#2156](https://github.com/leanprover-community/mathlib/pull/2156))

### [2020-03-15 21:15:49](https://github.com/leanprover-community/mathlib/commit/87f8ab2)
chore(nnreal): replace coe_le with coe_le_coe ([#2159](https://github.com/leanprover-community/mathlib/pull/2159))

### [2020-03-15 15:21:50](https://github.com/leanprover-community/mathlib/commit/7104132)
chore(field_theory/finite): spelling mistake ([#2157](https://github.com/leanprover-community/mathlib/pull/2157))

### [2020-03-15 04:22:33](https://github.com/leanprover-community/mathlib/commit/0cbfbab)
refactor(logic/function): inv_fun takes a nonempty instance instead of inhabited ([#2148](https://github.com/leanprover-community/mathlib/pull/2148))

### [2020-03-15 03:04:18](https://github.com/leanprover-community/mathlib/commit/b314df2)
chore(scripts): update nolints.txt

### [2020-03-15 01:43:38](https://github.com/leanprover-community/mathlib/commit/8c2a254)
feat(category_theory): comonads and coalgebras ([#2134](https://github.com/leanprover-community/mathlib/pull/2134))
* Comonads and coalgebras
* Update docstring
* add docstrings
* Update src/category_theory/monad/algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/category_theory/monad/algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/category_theory/monad/algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* make the linter happy
* revert change to nolints
* disable inhabited instance linter

### [2020-03-15 00:49:28](https://github.com/leanprover-community/mathlib/commit/e4bf0bf)
chore(scripts): update nolints.txt

### [2020-03-14 23:31:44](https://github.com/leanprover-community/mathlib/commit/5433973)
feat(category_theory): limits and colimits in Ab ([#2097](https://github.com/leanprover-community/mathlib/pull/2097))
* limits and colimits in AddCommGroup
* feat(category_theory): limits and colimits in Ab
* to_additive comes last
* add to nolints
* Update src/algebra/category/Group/limits.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* docstrings
* use bundled homs throughout
* comment about better model of colimits
* fix comments
* fixes
* linter

### [2020-03-14 21:19:35](https://github.com/leanprover-community/mathlib/commit/2e781eb)
doc(docs/install/*): emphasize projects link ([#2151](https://github.com/leanprover-community/mathlib/pull/2151))

### [2020-03-14 20:14:08](https://github.com/leanprover-community/mathlib/commit/2065438)
feat(category_theory/comma): some limits in the over category and iterated slices ([#2131](https://github.com/leanprover-community/mathlib/pull/2131))
* iterated slice and limits in over category
* A bit more docs
* changes from review
* removed simp attributes
* over prod map left
* Update src/category_theory/comma.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* simplify equivalence definition
* fix indentation
* make lemmas simp again
* removed simp
* fix equalizers proof

### [2020-03-14 18:14:17](https://github.com/leanprover-community/mathlib/commit/cc39a15)
chore(scripts): update nolints.txt

### [2020-03-14 17:09:36](https://github.com/leanprover-community/mathlib/commit/7b2be40)
refactor(data/equiv/algebra): split ([#2147](https://github.com/leanprover-community/mathlib/pull/2147))
* refactor(data/equiv/algebra): split
I want to use `≃*` without importing `ring`.
* Update src/data/equiv/ring.lean

### [2020-03-14 15:02:52](https://github.com/leanprover-community/mathlib/commit/e6ccfe0)
feat(algebra): the forgetful functor Module ℤ ⥤ Ab is an equivalence ([#2130](https://github.com/leanprover-community/mathlib/pull/2130))
* feat(algebra): the forgetful functor Module ℤ ⥤ Ab is an equivalence
* oops, forgot to add file
* missing conversion
* not there yet
* fixes
* doc-strings, and remove more instances
* various
* oops
* revert
* Delete multilinear.olean.lock
* revert
* move instances
* Remove note about a bug fixed in [#1586](https://github.com/leanprover-community/mathlib/pull/1586).
* whitespace

### [2020-03-14 12:47:55](https://github.com/leanprover-community/mathlib/commit/d313d14)
chore(scripts): update nolints.txt

### [2020-03-14 11:28:34](https://github.com/leanprover-community/mathlib/commit/559921a)
feat(algebra/category/Group): the free-forgetful adjunction for AddCommGroup ([#2141](https://github.com/leanprover-community/mathlib/pull/2141))
* feat(algebra/category/Group): the free-forgetful adjunction for AddCommGroup
* fixes
* Update src/group_theory/free_abelian_group.lean
* oops

### [2020-03-14 09:21:38](https://github.com/leanprover-community/mathlib/commit/465f599)
chore(scripts): update nolints.txt

### [2020-03-14 08:02:49](https://github.com/leanprover-community/mathlib/commit/81d3ebf)
feat(algebra): monoidal category of R-modules ([#2125](https://github.com/leanprover-community/mathlib/pull/2125))
* feat(algebra): monoidal category of R-modules
* docstrings
* minor
* tweaks
* fix import
* fixes
* reduce use of @
* broken
* fixes
* Update src/algebra/category/Module/basic.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>

### [2020-03-14 04:10:31](https://github.com/leanprover-community/mathlib/commit/3d621b5)
refactor(ring_theory/subring): use bundled homs ([#2144](https://github.com/leanprover-community/mathlib/pull/2144))

### [2020-03-14 01:59:21](https://github.com/leanprover-community/mathlib/commit/ade1ee3)
feat(category_theory/limits): derive has_binary_products from has_limit (pair X Y) ([#2139](https://github.com/leanprover-community/mathlib/pull/2139))
* feat(category_theory/limits): derive has_binary_products from has_limit (pair X Y)
* Rename *_of_diagram to diagram_iso_*

### [2020-03-13 18:31:09](https://github.com/leanprover-community/mathlib/commit/49f5fb8)
chore(algebra/category/CommRing/limits): avoid `is_ring_hom` ([#2142](https://github.com/leanprover-community/mathlib/pull/2142))
define a `ring_hom` instead

### [2020-03-13 12:20:20](https://github.com/leanprover-community/mathlib/commit/32c2768)
chore(linear_algebra/basic): simplify two proofs ([#2123](https://github.com/leanprover-community/mathlib/pull/2123))
* chore(linear_algebra/basic): simplify two proofs
Also drop `linear_map.congr_right` in favor of
`linear_equiv.congr_right`. I'll restore the deleted `congr_right`
as `comp_map : (M₂ →ₗ[R] M₃) →ₗ[R] (M →ₗ[R] M₂) →ₗ[R] (M →ₗ[R] M₃)` soon.
* Fix compile
* Restore `congr_right` under the name `comp_right`.

### [2020-03-13 10:18:27](https://github.com/leanprover-community/mathlib/commit/aec62dc)
chore(scripts): update nolints.txt

### [2020-03-13 09:00:12](https://github.com/leanprover-community/mathlib/commit/b54960d)
refactor(*): migrate some files to bundled ring homs ([#2133](https://github.com/leanprover-community/mathlib/pull/2133))
* refactor(*): migrate some files to bundled ring homs
* Rename ring_hom.is_local back to is_local_ring_hom
* Apply suggestions from code review
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Restore 2 instances, make `map` use bundled homs
* More bundled homs
* Add a docstring

### [2020-03-12 18:52:10](https://github.com/leanprover-community/mathlib/commit/1c449b6)
chore(algebra/field*, field_theory/subfield): drop some `x ≠ 0`, use `division_ring` ([#2136](https://github.com/leanprover-community/mathlib/pull/2136))
* chore(algebra/field*, field_theory/subfield): drop some `x ≠ 0`, use `division_ring`
We have `0⁻¹=0` in `division_ring` now, so no need to assume `field`
in `ring_hom.map_inv` etc.
* Fix lint

### [2020-03-12 16:38:40](https://github.com/leanprover-community/mathlib/commit/5fe72b6)
chore(scripts): update nolints.txt

### [2020-03-12 15:18:41](https://github.com/leanprover-community/mathlib/commit/f5787f5)
doc(*): switch from update-mathlib to leanproject ([#2093](https://github.com/leanprover-community/mathlib/pull/2093))
* doc(*): switch from update-mathlib to leanproject
* Apply suggestions from code review
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Use shiny new `leanproject new` and `leanproject get`
* documentation tweaks
* project.md tweaks

### [2020-03-12 13:07:30](https://github.com/leanprover-community/mathlib/commit/8131108)
feat(category_theory/opposites): add nat_iso.unop ([#2132](https://github.com/leanprover-community/mathlib/pull/2132))
* Add nat_iso.unop
* Add docstrings to nat_iso.op, nat_iso.unop

### [2020-03-12 10:56:40](https://github.com/leanprover-community/mathlib/commit/7d357d7)
Fix a typo ([#2137](https://github.com/leanprover-community/mathlib/pull/2137))

### [2020-03-12 05:14:27](https://github.com/leanprover-community/mathlib/commit/35a6e68)
chore(scripts): update nolints.txt

### [2020-03-12 04:06:30](https://github.com/leanprover-community/mathlib/commit/1b0a749)
feat(topology): is_closed_proj_of_compact ([#2069](https://github.com/leanprover-community/mathlib/pull/2069))
* feat(lattice): add inf_le_inf_left/right
* feat(set/lattice): image_inter_subset
* feat(set/lattice): push_pull
* feat(order/filter): push_pull and product notation
* feat(topology/subset_properties): is_closed_proj_of_compact
* feat(set/lattice): push_pull'
* fix(order/filter): forgotten doc
* lint (including old missing docstrings in filter).
* Apply Yury's suggestions.
* Forgotten style fix
* urkud's suggestions
Co-Authored-By: Yury G. Kudryashov <urkud@urkud.name>
* Update src/order/filter/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>

### [2020-03-11 22:56:21](https://github.com/leanprover-community/mathlib/commit/7c8dc2a)
feat(category_theory/limits): construct equalizers from pullbacks and products ([#2124](https://github.com/leanprover-community/mathlib/pull/2124))
* construct equalizers from pullbacks and products
* ...
* changes from review
* Add docstrings
* golf proofs a little
* linter

### [2020-03-11 18:57:43](https://github.com/leanprover-community/mathlib/commit/7cffe25)
chore(category_theory/cones): make functor argument of forget explicit ([#2128](https://github.com/leanprover-community/mathlib/pull/2128))

### [2020-03-11 10:15:41](https://github.com/leanprover-community/mathlib/commit/43431be)
chore(category_theory): remove functor.of ([#2127](https://github.com/leanprover-community/mathlib/pull/2127))
* chore(category_theory): remove functor.of
* fix

### [2020-03-11 07:13:33](https://github.com/leanprover-community/mathlib/commit/d909a61)
fix(algebra/category): avoid deprecated lemmas ([#2126](https://github.com/leanprover-community/mathlib/pull/2126))

### [2020-03-10 19:54:59](https://github.com/leanprover-community/mathlib/commit/36ac916)
Add two missing duals ([#2122](https://github.com/leanprover-community/mathlib/pull/2122))

### [2020-03-10 17:38:33](https://github.com/leanprover-community/mathlib/commit/699401b)
feat(ci): look for equivalent oleans on Azure ([#2094](https://github.com/leanprover-community/mathlib/pull/2094))
* first attempt at avoiding recompilation in ci
* avoid using leanproject
* delete most of library for testing
* modify non-lean file for testing
* Revert "delete most of library for testing"
This reverts commit b4f298e866513a6e1517f7fb370fcf9e03eb8030.
* unnecessary to look up the exact git sha
* simplify
* apply Gabriel's suggestion
* untar all and only src directory
* Revert "modify non-lean file for testing"
This reverts commit 3157cb1d0d0b3530445c36f8a1e9f725847f71ce.
* simplify
* add git reset to script
* Revert "add git reset to script"
This reverts commit c63a8281fef1a16ad0133521b7c8b002ef47907e.

### [2020-03-10 15:29:25](https://github.com/leanprover-community/mathlib/commit/668a98e)
feat(measurable_space): is_measurable_supr lemma ([#2092](https://github.com/leanprover-community/mathlib/pull/2092))
* feat(data/set/lattice): add @[simp] to lemmas
* feat(measurable_space): is_measurable_supr lemma
* fix proof
* fix proof
* fix proof
* oops
* fix proofs
* typo in doc string
* remove @[simp]

### [2020-03-10 13:12:10](https://github.com/leanprover-community/mathlib/commit/9feefee)
feat(ring_theory/polynomial): refactor of is_integral_domain_fin ([#2119](https://github.com/leanprover-community/mathlib/pull/2119))
* chore(ring_theory/polynomial): refactor proof of is_noetherian_ring_fin
* not there yet
* feat(ring_theory/polynomial): refactor of is_integral_domain_fin
* fix
* refactor
* fix
* fix
* suggestion from linter
* Update src/data/mv_polynomial.lean

### [2020-03-10 10:57:20](https://github.com/leanprover-community/mathlib/commit/cdc56ba)
feat(analysis/calculus/tangent_cone): prove that all intervals are `unique_diff_on` ([#2108](https://github.com/leanprover-community/mathlib/pull/2108))
* feat(analysis/calculus/tangent_cone): prove that all intervals are `unique_diff_on`
* Drop some unneeded assumptions

### [2020-03-10 06:39:45](https://github.com/leanprover-community/mathlib/commit/e8ad2e3)
feat(category_theory/limits): the pullback of a monomorphism is a monomorphism ([#2113](https://github.com/leanprover-community/mathlib/pull/2113))
* The pullback of a monomorphism is a monomorphism
* The pushout of an epimorphism is an epimorphism
* Fix a proof
* renaming

### [2020-03-10 04:22:40](https://github.com/leanprover-community/mathlib/commit/945845d)
feat(linter): include linter name in report ([#2116](https://github.com/leanprover-community/mathlib/pull/2116))
* feat(linter): include linter name in report (closes [#2098](https://github.com/leanprover-community/mathlib/pull/2098))
* Update src/tactic/lint.lean

### [2020-03-10 02:12:06](https://github.com/leanprover-community/mathlib/commit/4089712)
chore(ring_theory/polynomial): refactor proof of is_noetherian_ring_fin ([#2117](https://github.com/leanprover-community/mathlib/pull/2117))

### [2020-03-09 23:57:38](https://github.com/leanprover-community/mathlib/commit/25df884)
reflexive transitive closure is symmetric of original ([#2115](https://github.com/leanprover-community/mathlib/pull/2115))
* reflexive transitive closure is symmetric if original
* Update src/logic/relation.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/logic/relation.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2020-03-09 21:54:46](https://github.com/leanprover-community/mathlib/commit/f90803c)
feat(algebra/group/hom): cancel injective/surjective `monoid_hom`s ([#2112](https://github.com/leanprover-community/mathlib/pull/2112))
* feat(algebra/group/hom): cancel injective/surjective `monoid_hom`s
* Add a `ring_hom` version

### [2020-03-09 19:43:42](https://github.com/leanprover-community/mathlib/commit/b39713f)
feat(analysis/calculus/darboux): IVT for derivatives ([#2110](https://github.com/leanprover-community/mathlib/pull/2110))
* feat(analysis/calculus/darboux): IVT for derivatives
* whitespace
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

### [2020-03-09 14:27:32](https://github.com/leanprover-community/mathlib/commit/62abc4d)
feat(category_theory): images ([#2100](https://github.com/leanprover-community/mathlib/pull/2100))
* feat(category_theory): images
* oops, forgot to add file
* Update src/category_theory/category/default.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* some improvements
* linting
* oops
* Update src/category_theory/limits/shapes/images.lean

### [2020-03-09 12:22:18](https://github.com/leanprover-community/mathlib/commit/d8d0927)
refactor(topology/algebra/ordered): rename `tendsto_of_tendsto_of_tendsto_of_le_of_le` to `tendsto_of_tendsto_of_tendsto_of_le_of_le'` ([#2111](https://github.com/leanprover-community/mathlib/pull/2111))
The new `tendsto_of_tendsto_of_tendsto_of_le_of_le` assumes that
the inequalities hold everywhere.

### [2020-03-09 10:19:36](https://github.com/leanprover-community/mathlib/commit/4258f5e)
refactor(analysis/normed_space/banach): use bundled `→L[𝕜]` maps ([#2107](https://github.com/leanprover-community/mathlib/pull/2107))

### [2020-03-09 07:16:17](https://github.com/leanprover-community/mathlib/commit/434b629)
chore(scripts): update nolints.txt

### [2020-03-09 05:00:06](https://github.com/leanprover-community/mathlib/commit/ce7248a)
doc(docs/tutorial/category_theory): introductory category theory tutorial ([#2104](https://github.com/leanprover-community/mathlib/pull/2104))
* doc(docs/tutorial/category_theory): Adding WIP beginner category theory docs
* linewraps
* presumably uncontroversial edits
* oops
* whitespace
* explaining more about universes
* warning about definitional associativity
* add TODO
* Update docs/tutorial/category_theory/category_theory_intro.md
* rename
* cleanup
* adding lean version
* various
* add a note about debugging universe problems
* rename
* delete old markdown tutorial
* adding sections to make variable names nicer
* tidy up universes
* url escape parentheses inside links
* tweaking text
* Update docs/tutorial/category_theory/intro.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

### [2020-03-09 02:49:14](https://github.com/leanprover-community/mathlib/commit/61d70ce)
chore(algebra/group): streamlining imports ([#2099](https://github.com/leanprover-community/mathlib/pull/2099))
* chore(algebra/group): streamlining imports
* reducing imports

### [2020-03-09 00:56:10](https://github.com/leanprover-community/mathlib/commit/ca370cb)
fix(deprecated/group): remove dangerous instances ([#2096](https://github.com/leanprover-community/mathlib/pull/2096))

### [2020-03-08 22:46:03](https://github.com/leanprover-community/mathlib/commit/15d3268)
chore(category_theory/functor): make arguments implicit ([#2103](https://github.com/leanprover-community/mathlib/pull/2103))

### [2020-03-08 05:53:07](https://github.com/leanprover-community/mathlib/commit/b7444b0)
Remove limits.lean which is superseded by limits_of_products_and_equalizers.lean ([#2105](https://github.com/leanprover-community/mathlib/pull/2105))

### [2020-03-07 21:37:38](https://github.com/leanprover-community/mathlib/commit/d53bbb6)
feat(data/fin_enum): `fin_enum` class for finite types with an enumeration order ([#1368](https://github.com/leanprover-community/mathlib/pull/1368))
* feat(data/enum): `enumerable` class for finite types with an
enumeration order
* little fixes
* Update enum.lean
* Update enum.lean
* Update finset.lean
* add documentation
* Update src/data/enum.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/data/enum.lean [skip ci]
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update fin.lean [skip ci[
* Update enum.lean
* Update enum.lean
* Update fin.lean [skip ci]
* Update enum.lean
* Update src/data/enum.lean [skip ci]
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Update interactive.lean [skip ci]
* Rename enum.lean to fin_enum.lean [skip ci]
* add `mono using` to doc/tactics.md [skip ci]
* update to Lean 3.5.1
* address lint comments
* Update src/data/fin_enum.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update fin_enum.lean
* Apply suggestions from code review
Co-Authored-By: Scott Morrison <scott@tqft.net>
* remove unneeded lemmas
* add `nodup_to_list`

### [2020-03-07 02:22:02](https://github.com/leanprover-community/mathlib/commit/726d83f)
feat(lint): add two new linters ([#2089](https://github.com/leanprover-community/mathlib/pull/2089))
* feat(lint): add two new linters
checks whether type-class inference searches end relatively quickly
checks that there are no instances has_coe a t with variable a
* remove `is_fast` from `has_coe_variable`
* add link to note
* typo in priority
* fix error, implement comments

### [2020-03-07 00:15:07](https://github.com/leanprover-community/mathlib/commit/c5437b4)
chore(scripts): update nolints.txt

### [2020-03-06 21:32:35](https://github.com/leanprover-community/mathlib/commit/6c23bad)
feat(data/set/lattice): add @[simp] to lemmas ([#2091](https://github.com/leanprover-community/mathlib/pull/2091))
* feat(data/set/lattice): add @[simp] to lemmas
* fix proof
* fix proof
* fix proof
* oops
* fix proofs
* typo in doc string

### [2020-03-06 19:21:21](https://github.com/leanprover-community/mathlib/commit/4f10d1e)
refactor(group_theory/monoid_localization): use characteristic predicate ([#2004](https://github.com/leanprover-community/mathlib/pull/2004))
* should I be changing and committing toml idk
* initial monoid loc lemmas
* responding to PR comments
* removing bad @[simp]
* inhabited instances
* remove #lint
* additive inhabited instance
* using is_unit & is_add_unit
* doc string
* remove simp
* submonoid.monoid_loc... -> submonoid.localization
* submonoid.monoid_loc... -> submonoid.localization
* generalize inhabited instance
* remove inhabited instance

### [2020-03-06 11:43:23](https://github.com/leanprover-community/mathlib/commit/36b336c)
chore(scripts): update nolints.txt

### [2020-03-06 09:04:50](https://github.com/leanprover-community/mathlib/commit/8fb9881)
fix(category_theory/limits): Add some missing instances for special shapes of limits ([#2083](https://github.com/leanprover-community/mathlib/pull/2083))
* Add some instances for limit shapes
* Deduce has_(equalizers|kernels|pullbacks) from has_finite_limits

### [2020-03-06 06:56:58](https://github.com/leanprover-community/mathlib/commit/f81f861)
feat(category_theory/limits): the kernel of the cokernel of an epimorphism is an isomorphism ([#2088](https://github.com/leanprover-community/mathlib/pull/2088))
* The kernel of the cokernel of an epimorphism is an isomorphism
* Fix unused argument warnings
* Remove a set_option
* Fix a typo

### [2020-03-05 18:58:12-08:00](https://github.com/leanprover-community/mathlib/commit/0f9751c)
feat(data/traversable): improve support for instances for recursive types ([#2072](https://github.com/leanprover-community/mathlib/pull/2072))

### [2020-03-06 01:31:18](https://github.com/leanprover-community/mathlib/commit/093ac77)
feat(analysis/calculus/specific_functions): smoothness of exp(-1/x) ([#2087](https://github.com/leanprover-community/mathlib/pull/2087))
* feat(analysis/calculus/specific_functions): smoothness of exp(-1/x)
* use namespace; shorter names
* fix field_simp

### [2020-03-05 16:05:27](https://github.com/leanprover-community/mathlib/commit/50c4adf)
chore(scripts): update nolints.txt

### [2020-03-05 13:17:04](https://github.com/leanprover-community/mathlib/commit/78ffbae)
chore(*): switch to lean 3.6.1 ([#2064](https://github.com/leanprover-community/mathlib/pull/2064))
* chore(*): switch to lean 3.6.0
* Port `src/linear_algebra` to Lean 3.6c
* Port `src/ring_theory` to Lean 3.6c
* Port `src/algebra` and its dependencies to Lean 3.6c
* Port `src/group_theory` to Lean 3.6c
* WIP: Ports part of `src/data` to Lean 3.6c
* Port `src/data` (and dependencies) to Lean 3.6
* fix set_theory.lists
* fix ring2
* fix pell.lean
these aren't the cleanest proofs, but pell.lean is kind of a standalone thing.
* fix dioph.lean
* Port `src/number_theory/sum_four_squares.lean` to Lean 3.6c
* Port `src/field_theory` to Lean 3.6
* Port `src/computability` to Lean 3.6c
* Port `src/measure_theory` (and dependencies) to Lean 3.6c
* fix manifold/real_instances
* fix analysis/complex/polynomial
* Fix some compile errors in `real_inner_product`
* Upgrade to Lean 3.6.1
* perf: speed up calls to linarith
* Reduce instance priorities for potentially noncomputable instances.
* Remove cyclic instance.
* Make arguments {implicit} in instances where they can be filled in via unification.
* Make inner_product_space compile.
* Style.
* Port data.nat.modeq
* Port data.int.parity
* Port data.int.modeq
* Port data.real.hyperreal
* fix(ci): always run git setup step
closes [#2079](https://github.com/leanprover-community/mathlib/pull/2079)
(cherry picked from commit 8a0157dc8dfc946d98eba02417052c3c9556559e)
* Remove pre-3.6 legacy code.
* Fix test/monotonicity.lean
* Fix test/ring_exp.lean
* Fix test/conv.lean
* Fix archive/imo1988_q6.lean
* Fix docs/tutorial/Zmod37.lean
* Fix archive/sensitivity.lean
* refactor(algebra/lie_algebra): lie_algebra should not extend lie_ring
* remove unused argument
* add doc-string to instance that became a def
* add docstring
* Fix linting error ☺
* Fix data.real.irrational
* fixing a proof
* cleaning up proof
* fix broken proof
* fix proof
* fix some more proofs
* fix
* fix proofs

### [2020-03-05 00:24:49](https://github.com/leanprover-community/mathlib/commit/8535132)
refactor(algebra/lie_algebra): lie_algebra should not extend lie_ring ([#2084](https://github.com/leanprover-community/mathlib/pull/2084))
* refactor(algebra/lie_algebra): lie_algebra should not extend lie_ring
* Fix linting error ☺

### [2020-03-04 22:23:00](https://github.com/leanprover-community/mathlib/commit/7d6c4fb)
fix(congruence): use has_coe_t instead of has_coe ([#2086](https://github.com/leanprover-community/mathlib/pull/2086))
* fix(congruence): use has_coe_t instead of has_coe
* capitalization
Does that matter for doc generation?

### [2020-03-04 19:56:00](https://github.com/leanprover-community/mathlib/commit/9fc675c)
chore(analysis/normed_space/basic): rename `ne_mem_of_tendsto_norm_at_top` ([#2085](https://github.com/leanprover-community/mathlib/pull/2085))
It uses `∀ᶠ` now, so rename to `eventually_ne_of_tendsto_norm_at_top`.

### [2020-03-04 13:10:10](https://github.com/leanprover-community/mathlib/commit/f112408)
fix(ci): adjust conditions for fixing steps ([#2082](https://github.com/leanprover-community/mathlib/pull/2082))
* fix(ci): always run git setup step
closes [#2079](https://github.com/leanprover-community/mathlib/pull/2079)
* fix(ci): always test doc gen
documentation will still be pushed only under the same conditions as before
closes [#2081](https://github.com/leanprover-community/mathlib/pull/2081)
* Update scripts/deploy_docs.sh
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>

### [2020-03-04 07:09:20](https://github.com/leanprover-community/mathlib/commit/cc4ac8a)
chore(scripts): update nolints.txt

### [2020-03-03 20:45:05-08:00](https://github.com/leanprover-community/mathlib/commit/0f1eb80)
fix(CI/documentation): add a name back

### [2020-03-03 22:24:50](https://github.com/leanprover-community/mathlib/commit/13f04c0)
feat(tactic/extract_goal): improve formatting to put assumptions on their own line ([#2076](https://github.com/leanprover-community/mathlib/pull/2076))

### [2020-03-03 20:14:28](https://github.com/leanprover-community/mathlib/commit/545dd03)
feat(topology/metric_space/antilipschitz): define `antilipschitz_with` ([#2075](https://github.com/leanprover-community/mathlib/pull/2075))
* chore(data/real/ennreal): weaker assumptions in `sub_mul`, add `coe_inv_le`
* feat(topology/metric_space/antilipschitz): define `antilipschitz_with`
Also make some proofs use facts about `antilipschitz_with`.
* Rename inequalities, move `K` to the other side
This way it's easier to glue it with the rest of the library, and
we can avoid assuming `0 < K` in many lemmas.

### [2020-03-03 14:39:18](https://github.com/leanprover-community/mathlib/commit/02d22c3)
chore(scripts): update nolints.txt

### [2020-03-03 11:51:46](https://github.com/leanprover-community/mathlib/commit/f7e82d0)
feat(tactic/lint): check for redundant simp lemmas ([#2066](https://github.com/leanprover-community/mathlib/pull/2066))
* chore(*): fix simp lemmas
* feat(tactic/lint): check for redundant simp lemmas

### [2020-03-03 09:04:21](https://github.com/leanprover-community/mathlib/commit/2d1bd45)
fix some docstrings [ci skip] ([#2078](https://github.com/leanprover-community/mathlib/pull/2078))

### [2020-03-03 07:18:28](https://github.com/leanprover-community/mathlib/commit/2a9ad03)
feat(data/list/basic): more lemmas about `list.chain'`; `chain'_of_pairwise` → `pairwise.chain'` ([#2071](https://github.com/leanprover-community/mathlib/pull/2071))

### [2020-03-03 05:29:57](https://github.com/leanprover-community/mathlib/commit/e003014)
feat(analysis/calculus/iterated_deriv): iterated derivative of a function defined on the base field ([#2067](https://github.com/leanprover-community/mathlib/pull/2067))
* iterated deriv
* cleanup
* fix docstring
* add iterated_deriv_within_succ'
* remove n.succ
* n+1 -> n + 1

### [2020-03-03 00:17:40](https://github.com/leanprover-community/mathlib/commit/262a39e)
chore(scripts): update nolints.txt

### [2020-03-02 21:45:35](https://github.com/leanprover-community/mathlib/commit/fe9d7ff)
feat(tactic/nat_cases): a tactic to case bash inequalities on natural numbers ([#1596](https://github.com/leanprover-community/mathlib/pull/1596))
* starting on finset_cases
* looking pretty nice
* moving lemma that rewrites nat.add back to (+)
* update tactics.md
* cleanup
* suggestions from review
* Update src/tactic/fin_cases.lean
Co-Authored-By: semorrison <scott@tqft.net>
* incomplete implementation of `with` syntax
* looks good
* failed attempt to use unification
* test showing elaboration problem
* elaborating the `with` argument with respect to the expected type
* testing the type of A in `x ∈ A` using unification rather than syntactic matching
* refactor and cleanup
* refactor
* initial start on nat_cases
* initial start on nat_cases
* resuming work on nat_cases
* looks reasonable
* documentation
* reverting bad merge in fin_cases
* fix module comment
* move non-meta lemmas
* add tests for Chris' use case
* cleanup
* oops
* starting on fintype instances for Icos
* finishing fintypes
* minor
* not really sure what to do next
* oops, forgot to commit??
* oops
* bit more work
* more progress
* everything works?
* moving everything to their natural homes
* rearrange
* cleanup
* linting
* doc-strings
* merge two interactive tactics, via `using` keyword
* improve documentation, in response to review
* add interval_cases to tactic.default
* Apply suggestions from code review

### [2020-03-02 19:54:08](https://github.com/leanprover-community/mathlib/commit/1d82a7c)
doc(data/fin): add docs; fin_zero_elim -> fin.elim0; fin_zero_elim' -> fin_zero_elim ([#2055](https://github.com/leanprover-community/mathlib/pull/2055))
* doc(data/fin): add some docs
Also drom `fin_zero_elim` in favor of `fin.elim0` from `stdlib` and
rename `fin_zero_elim'` to `fin_zero_elim`.
* Update src/data/fin.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update docs, fix `Π` vs `∀`.

### [2020-03-02 18:11:18](https://github.com/leanprover-community/mathlib/commit/8919541)
feat(data/finset): new basic material on finsets and fintypes ([#2068](https://github.com/leanprover-community/mathlib/pull/2068))
* feat(data/finset): additional basic material
* minor fixes
* golfed
* Update src/data/finset.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/data/finset.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/data/finset.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* golfed

### [2020-03-02 16:19:30](https://github.com/leanprover-community/mathlib/commit/62756bd)
chore(data/real/ennreal): weaker assumptions in `sub_mul`, add `coe_inv_le` ([#2074](https://github.com/leanprover-community/mathlib/pull/2074))

### [2020-03-02 14:25:59](https://github.com/leanprover-community/mathlib/commit/bfbd093)
chore(algebra/group): move `is_mul/monoid/group_hom` to `deprecated/` ([#2056](https://github.com/leanprover-community/mathlib/pull/2056))
* Move `is_mul/monoid/group_hom` to `deprecated/`
Also improve deprecation docstring.
TODO: fix compile
* chore(algebra/group): move `is_mul/monoid/group_hom` to `deprecated/`
Also migrate a few definitions to bundled homs:
* use `monoid_hom.map_is_conj` instead of `is_group_hom.is_conj`;
* `with_one.lift` and `with_one.map` now take `f` and an explicit
  argument `h : ∀ x y, f (x * y) = f x * f y` instead of `f` and
  `[is_mul_hom f]`, and produce a `monoid_hom`. As a side effect, they
  are now defined for semigroup homomorphisms only.
* Adjust module docstring
* Update src/algebra/group/with_one.lean
I wonder if mergify will do its job now.

### [2020-03-02 12:33:13](https://github.com/leanprover-community/mathlib/commit/3055b3c)
chore(topology/metric_space/isometry): rename `(e)metric.isometry.diam_image` to `isometry.(e)diam_image` ([#2073](https://github.com/leanprover-community/mathlib/pull/2073))
This way we can use dot notation to access these lemmas. Also add `(e)diam_range`.

### [2020-03-02 10:42:53](https://github.com/leanprover-community/mathlib/commit/2683fa0)
feat(order/galois_connection): lemmas about galois insertions and supr/infi ([#2052](https://github.com/leanprover-community/mathlib/pull/2052))
* feat(order/galois_connection): lemmas about galois insertions and supr/infi
* Fix build, hopefully

### [2020-03-02 08:53:22](https://github.com/leanprover-community/mathlib/commit/d5d907b)
feat(algebra/free_monoid): define `lift` and `map`, move out of `algebra/group` ([#2060](https://github.com/leanprover-community/mathlib/pull/2060))
* Move `free_monoid` from `algebra/group/` to `algebra/`
* feat(algebra/free_monoid): define `lift` and `map`
* Expand docstring, drop unneeded arguments to `to_additive`
* Fix compile
* Update src/algebra/free_monoid.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

### [2020-03-01 23:09:46-08:00](https://github.com/leanprover-community/mathlib/commit/aec54b3)
fix(.mergify.yml): remove " (leanprover-community/lean:3.5.1)" ([#2077](https://github.com/leanprover-community/mathlib/pull/2077))