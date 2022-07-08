### [2019-12-29 08:52:23](https://github.com/leanprover-community/mathlib/commit/acf2038)
feat(analysis/calculus/mean_value): more corollaries of the MVT ([#1819](https://github.com/leanprover-community/mathlib/pull/1819))
* feat(analysis/calculus/mean_value): more corolaries of the MVT
* Fix compile, add "strict inequalities" versions of some theorems, add docs
* Update src/analysis/calculus/mean_value.lean
* Add theorems for `convex_on univ`
* Fix comments
* @sgouezel adds missing articles
Thanks a lot! We don't have them in Russian, so it's hard for me to put them right.
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/analysis/calculus/mean_value.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Add more `univ` versions

### [2019-12-28 20:31:03](https://github.com/leanprover-community/mathlib/commit/64770a8)
feat(analysis/calculus/deriv): Prove equivalence of Fréchet derivative and the classical definition ([#1834](https://github.com/leanprover-community/mathlib/pull/1834))
* feat(analysis/calculus/deriv): Prove equivalence of Fréchet derivative and the classical definition
* Fix a typo
* Move, change doc, add versions for `has_deriv_within_at` and `has_deriv_at`.
* Fix docstring, remove an unsed argument

### [2019-12-28 13:01:45](https://github.com/leanprover-community/mathlib/commit/e43905b)
refactor(topology/algebra/ordered): formulate a few "Icc induction" principles ([#1833](https://github.com/leanprover-community/mathlib/pull/1833))
* refactor(topology/algebra/ordered): use `tfae`, prove equality of some `nhds_within`
* Add missing `order_dual.*` instances
* Try to fix the build
* Fix formatting, rename some variables
* refactor(topology/algebra/ordered): formulate a few "Icc induction" principles
They have other applications than proving `is_connected_Icc`.
* Fix doc
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Rephraze docs
* Drop an unused argument

### [2019-12-28 11:42:42](https://github.com/leanprover-community/mathlib/commit/a6a8a11)
refactor(data/equiv/encodable): bring `directed.sequence*` from `integration`, use `quotient.rep` instead of `quot.rep` ([#1825](https://github.com/leanprover-community/mathlib/pull/1825))
* refactor(data/equiv/encodable): bring `directed.sequence*` from `integration`, use `quotient.rep` instead of `quot.rep`
`sequence_of_directed` in `measure_theory/integration` did not belong
there.
Also add some docstrings.
* doc/style fixes by @sgouezel
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Remove an unused argument, add a docstring
* Completely remove the `reflexive r` assumption

### [2019-12-28 10:05:30](https://github.com/leanprover-community/mathlib/commit/340fa14)
feat(analysis/specific_limits): add a few more limits ([#1832](https://github.com/leanprover-community/mathlib/pull/1832))
* feat(analysis/specific_limits): add a few more limits
* Drop 1 lemma, generalize two others.
* Rename `tendsto_inverse_at_top_nhds_0`, fix compile

### [2019-12-27 20:26:09](https://github.com/leanprover-community/mathlib/commit/0a9a1ff)
refactor(topology/algebra/ordered): use `tfae`, prove equality of some `nhds_within` ([#1831](https://github.com/leanprover-community/mathlib/pull/1831))
* refactor(topology/algebra/ordered): use `tfae`, prove equality of some `nhds_within`
* Add missing `order_dual.*` instances
* Try to fix the build
* Fix formatting, rename some variables
* Fix compile

### [2019-12-27 18:11:30](https://github.com/leanprover-community/mathlib/commit/82ca731)
refactor(calculus): simplify derivative extension ([#1826](https://github.com/leanprover-community/mathlib/pull/1826))
* refactor(calculus): simplify derivative extension
* generalize continuous_within_at.closure_le
* Simplify proof following Sébastien
* Update src/analysis/calculus/extend_deriv.lean

### [2019-12-27 15:35:17](https://github.com/leanprover-community/mathlib/commit/3a78f49)
feat(order/basic): add `dual_le` and `dual_lt` lemmas ([#1830](https://github.com/leanprover-community/mathlib/pull/1830))

### [2019-12-27 14:05:28](https://github.com/leanprover-community/mathlib/commit/c9a81b0)
refactor(*): unify API of `list/multiset/finset.prod_hom` ([#1820](https://github.com/leanprover-community/mathlib/pull/1820))
* refactor(*): unify API of `list/multiset/finset.prod_hom`
Also remove `is_group_hom.map_prod`; use `*.prod_hom.symm` or
`monoid_hom.map_*prod` instead.
* Update src/ring_theory/ideal_operations.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Restore explicit args of `list.fold(l/r)_hom`
* Fix `group_theory/perm/sign`
* Fix `quadratic_reciprocity`
* Fix compile

### [2019-12-27 12:40:25](https://github.com/leanprover-community/mathlib/commit/0a87dd8)
feat(topology/basic): a few simple lemmas ([#1829](https://github.com/leanprover-community/mathlib/pull/1829))
* feat(topology/basic): a few simple lemmas
* Fix compile

### [2019-12-27 11:08:24](https://github.com/leanprover-community/mathlib/commit/89854fa)
refactor(analysis/calculus/deriv): Use equality of functions ([#1818](https://github.com/leanprover-community/mathlib/pull/1818))
* refactor(analysis/calculus/deriv): Use equality of functions
This way we can rewrite, e.g., in `deriv (deriv sin)`.
* Restore some old lemmas
* Restore old `deriv_cos`, fix `deriv_id'`
* Update src/analysis/calculus/deriv.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Fix compile

### [2019-12-27 09:41:58](https://github.com/leanprover-community/mathlib/commit/c1a993d)
feat(data/set/intervals): unions of adjacent intervals ([#1827](https://github.com/leanprover-community/mathlib/pull/1827))

### [2019-12-26 16:34:12](https://github.com/leanprover-community/mathlib/commit/7e2d4b8)
feat(analysis/calculus/extend_deriv): extend differentiability to the boundary ([#1794](https://github.com/leanprover-community/mathlib/pull/1794))
* feat(analysis/calculus/extend_deriv): extend differentiability to the boundary
* fix build

### [2019-12-24 05:40:16](https://github.com/leanprover-community/mathlib/commit/9a9f617)
fix(topology/algebra/infinite_sum): add a hint to speed up elaboration ([#1824](https://github.com/leanprover-community/mathlib/pull/1824))
Fix suggested by Joe on Zulip.

### [2019-12-23 23:32:58](https://github.com/leanprover-community/mathlib/commit/64921a4)
refactor(topology/*): migrate to `uniform_space.complete_of_convergent_controlled_sequences` ([#1821](https://github.com/leanprover-community/mathlib/pull/1821))
* refactor(topology/*): migrate to `uniform_space.complete_of_convergent_controlled_sequences`
Also rewrite
`uniform_space.complete_of_convergent_controlled_sequences` in terms
of `has_countable_basis`, and add a lemma useful to prove
`l = ⨅ i, f i` for filters.
* Revert some implicit/explicit argument changes
No reason to have them, at least in this PR
* Fix docstrings
* Fix a docstring
* Fix imports
* `cau_seq_filter`: change namespaces, adjust `hensel`
* Fix compile
* Update src/topology/metric_space/cau_seq_filter.lean
* Update src/topology/uniform_space/cauchy.lean

### [2019-12-23 22:13:46](https://github.com/leanprover-community/mathlib/commit/439ac4e)
feat(analysis/calculus/local_extr): Fermat's Theorem, Rolle's Theorem, Lagrange's MVT, Cauchy's MVT ([#1807](https://github.com/leanprover-community/mathlib/pull/1807))
* feat(analysis/calculus/local_extr): Rolle's Theorem, Lagrange's MVT, Cauchy's MVT
* feat(order/filter/extr,topology/algebra/local_extr): local min/max points
This commit contains facts that do not require smooth structure on the domain.
* Rewrite: introduce `is_min_filter`, `pos_tangent_cone_at`.
* Fix compile, move code around
* Drop a TODO, add some docs
* Fix compile
* Fix a typo
* Fix #lint error
* Add some docstrings
* Add some missing lemmas
* Use `differentiable_on`
* Add/rewrite file-level docs, rename some lemmas.
* Update src/analysis/calculus/local_extr.lean
* Update src/order/filter/extr.lean
* Fix a docstring, add Wiki links
* Add refs and tags
* File docstring: provide Lean names of the main lemmas.
* Update src/analysis/calculus/local_extr.lean
* Update src/analysis/calculus/local_extr.lean

### [2019-12-20 20:34:56](https://github.com/leanprover-community/mathlib/commit/883d974)
feat(algebra/module): sum_smul' (for semimodules) ([#1752](https://github.com/leanprover-community/mathlib/pull/1752))
* feat(algebra/module): sum_smul' (for semimodules)
* adding docstring
* use `classical` tactic
* moving ' name to the weaker theorem

### [2019-12-19 06:24:53](https://github.com/leanprover-community/mathlib/commit/e875492)
chore(algebra/module) remove an unneeded commutativity assumption ([#1813](https://github.com/leanprover-community/mathlib/pull/1813))

### [2019-12-18 12:57:28](https://github.com/leanprover-community/mathlib/commit/5dae5d2)
chore(ring_theory/algebra): redefine module structure of Z-algebra instance ([#1812](https://github.com/leanprover-community/mathlib/pull/1812))
This redefines the Z-algebra instance, so that the module structure is definitionally equal to the Z-module structure of any `add_comm_group`

### [2019-12-18 09:23:47](https://github.com/leanprover-community/mathlib/commit/bec46af)
refactor(topology/*): use dot notation with `compact`, prove `compact.image` with `continuous_on` ([#1809](https://github.com/leanprover-community/mathlib/pull/1809))
* refactor(topology/*): use dot notation, prove `compact.image` with `continuous_on`
* Apply suggestions from code review
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Fix compile, update some proofs
* Make `range_quot_mk` a `simp` lemma
* Fix lint errors

### [2019-12-18 06:01:42](https://github.com/leanprover-community/mathlib/commit/1207518)
feat(*): add command for declaring library notes ([#1810](https://github.com/leanprover-community/mathlib/pull/1810))
* feat(*): add command for declaring library notes
* add missing file
* make note names private
* update docs
* Update library_note.lean
* Update library_note.lean

### [2019-12-17 22:12:07](https://github.com/leanprover-community/mathlib/commit/acdf272)
chore(data/fintype): use `list.fin_range` for `fin.fintype` ([#1811](https://github.com/leanprover-community/mathlib/pull/1811))

### [2019-12-17 18:02:26](https://github.com/leanprover-community/mathlib/commit/52e1872)
refactor(topology/algebra/ordered): prove IVT for a connected set ([#1806](https://github.com/leanprover-community/mathlib/pull/1806))
* refactor(topology/algebra/ordered): prove IVT for a connected set
Also prove that intervals are connected, and deduce the classical IVT
from this.
* Rewrite the proof, move `min_le_max` to the root namespace
* Adjust `analysis/complex/exponential`
* Add comments/`obtain`
* Add some docs
* Add more docs
* Move some proofs to a section with weaker running assumptions
* Remove empty lines, fix a docstring
* +1 docstring

### [2019-12-17 14:48:50](https://github.com/leanprover-community/mathlib/commit/d8dc144)
feat(geometry/manifold): smooth bundles, tangent bundle ([#1607](https://github.com/leanprover-community/mathlib/pull/1607))
* feat(geometry/manifold): smooth bundles, tangent bundle
* remove decidable in preamble
* Update src/geometry/manifold/basic_smooth_bundle.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/geometry/manifold/basic_smooth_bundle.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/geometry/manifold/basic_smooth_bundle.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* comments
* cleanup
* oops, forgot squeeze_simp
* simpa instead of simp
* oops
* much better docstrings
* improved formatting
* space after forall
* fix build
* fix build, continuous.smul
* minor improvements

### [2019-12-17 13:38:54](https://github.com/leanprover-community/mathlib/commit/308a08c)
refactor(topology/metric_space/closeds): migrate to `cauchy_seq_of_edist_le_geometric_two` ([#1760](https://github.com/leanprover-community/mathlib/pull/1760))
* feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic
* Undo name change
* Fix compile
* nnreal: add `move_cast`
* ennreal: more lemmas
* Fix compile
* feat(topology/instances/ennreal): more lemmas
* Fix compile
* Rewrite `cauchy_seq_of_edist_le_geometric` etc in terms of `ennreal`s
I tried to actually use `nnreal`s, and it leads to coercions nightmare.
* Simplify some proofs using new lemmas
* Fix compile
* Fix compile
* refactor(topology/metric_space/closeds): migrate to `cauchy_seq_of_edist_le_geometric_two`

### [2019-12-17 08:52:57](https://github.com/leanprover-community/mathlib/commit/3053a16)
feat(tactic/field_simp): tactic to reduce to one division in fields ([#1792](https://github.com/leanprover-community/mathlib/pull/1792))
* feat(algebra/field): simp set to reduce to one division in fields
* tactic field_simp
* fix docstring
* fix build

### [2019-12-17 07:44:28](https://github.com/leanprover-community/mathlib/commit/abea298)
refactor(analysis/specific_limits): use `ennreal`s instead of `nnreal`s in `*_edist_le_geometric` ([#1759](https://github.com/leanprover-community/mathlib/pull/1759))
* feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic
* Undo name change
* Fix compile
* nnreal: add `move_cast`
* ennreal: more lemmas
* Fix compile
* feat(topology/instances/ennreal): more lemmas
* Fix compile
* Rewrite `cauchy_seq_of_edist_le_geometric` etc in terms of `ennreal`s
I tried to actually use `nnreal`s, and it leads to coercions nightmare.
* Simplify some proofs using new lemmas
* Fix compile
* Fix compile

### [2019-12-16 14:15:11](https://github.com/leanprover-community/mathlib/commit/cd53e27)
chore(topology/algebra/ordered): use interval notation here and there ([#1802](https://github.com/leanprover-community/mathlib/pull/1802))
* chore(topology/algebra/ordered): use interval notation here and there
Also prove a slightly more general version of `mem_nhds_orderable_dest`
* Fix a few compile errors
* Rename a lemma, fix compile, add docs and `dual_I??` lemmas
* Fix names, add comments
* Make some lemmas simp

### [2019-12-16 10:20:01](https://github.com/leanprover-community/mathlib/commit/de25b10)
refactor(analysis/convex): simplify proofs, use implicit args and  dot notation ([#1804](https://github.com/leanprover-community/mathlib/pull/1804))
* feat(data/set/intervals): add `nonempty_Icc` etc, `image_(add/mul)_(left/right)_Icc`
* refactor(analysis/convex): simplify proofs, use implicit args and  dot notation
* Use dot notation.
* Swap LHS and RHS of `image_Icc_zero_one_eq_segment`.
* Introduce `finset.center_mass`, prove basic properties.
* Deduce Jensen's inequality from the corresponding property of convex
  sets; rename corresponding lemmas.
* Fix a typo
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/analysis/convex.lean

### [2019-12-16 08:11:28](https://github.com/leanprover-community/mathlib/commit/6188b99)
feat(topology/instances/ennreal): more lemmas about tsum ([#1756](https://github.com/leanprover-community/mathlib/pull/1756))
* feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic
* Undo name change
* Fix compile
* nnreal: add `move_cast`
* ennreal: more lemmas
* Fix compile
* feat(topology/instances/ennreal): more lemmas
* Fix compile

### [2019-12-16 07:01:34](https://github.com/leanprover-community/mathlib/commit/ee981c2)
refactor(analysis/calculus/fderiv): prove `has_fderiv_within_at.lim` for any filter ([#1805](https://github.com/leanprover-community/mathlib/pull/1805))
* refactor(analysis/calculus/fderiv): prove `has_fderiv_within_at.lim` for any filter
Also prove two versions of "directional derivative agrees with
`has_fderiv_at`": `has_fderiv_at.lim` and `has_fderiv_at.lim_real`.
* Rename a lemma as suggested by @sgouezel

### [2019-12-15 22:29:01](https://github.com/leanprover-community/mathlib/commit/699da42)
feat(data/set/intervals): add `nonempty_Icc` etc, `image_(add/mul)_(left/right)_Icc` ([#1803](https://github.com/leanprover-community/mathlib/pull/1803))

### [2019-12-15 21:28:53](https://github.com/leanprover-community/mathlib/commit/7cda8bb)
feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic ([#1754](https://github.com/leanprover-community/mathlib/pull/1754))
* feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic
* Undo name change
* Fix compile
* nnreal: add `move_cast`
* ennreal: more lemmas
* Fix compile

### [2019-12-15 19:32:42](https://github.com/leanprover-community/mathlib/commit/871a36f)
feat(group_theory/monoid_localization) add localizations of commutative monoids at submonoids ([#1798](https://github.com/leanprover-community/mathlib/pull/1798))
* 1st half of monoid_localization
* change in implementation notes
* fixing naming clashes
* change additive version's name
* oops, had a /- instead of /--
* generalize comm_monoid instance
* remove notes to self
* responding to PR comments

### [2019-12-15 17:52:56](https://github.com/leanprover-community/mathlib/commit/7dfbcdd)
(docs/tactics.md) adding `norm_num` [ci skip] ([#1799](https://github.com/leanprover-community/mathlib/pull/1799))
* (docs/tactics.md) adding `norm_num` [ci skip]
* fixing example
* clarifying explanation, adding more examples
* one more example
* one more example
* editing norm_num docstring

### [2019-12-15 16:39:49](https://github.com/leanprover-community/mathlib/commit/9a37e3f)
refactor(*): make vector_space an abbreviation for module ([#1793](https://github.com/leanprover-community/mathlib/pull/1793))
* refactor(*): make vector_space an abbreviation for module
* Remove superfluous instances
* Fix build
* Add Note[vector space definition]
* Update src/algebra/module.lean
* Fix build (hopefully)
* Update src/measure_theory/bochner_integration.lean

### [2019-12-13 22:04:36](https://github.com/leanprover-community/mathlib/commit/a3844c8)
chore(algebra/group/basic): DRY, add `mul_left_surjective` ([#1801](https://github.com/leanprover-community/mathlib/pull/1801))
Some lemmas explicitly listed arguments already declared using
`variables`, remove them.

### [2019-12-13 18:10:30+01:00](https://github.com/leanprover-community/mathlib/commit/bb7d4c9)
chore(data/set/lattice): drop `Union_eq_sUnion_range` and `Inter_eq_sInter_range` ([#1800](https://github.com/leanprover-community/mathlib/pull/1800))
* chore(data/set/lattice): drop `Union_eq_sUnion_range` and `Inter_eq_sInter_range`
Two reasons:
* we already have `sUnion_range` and `sInter_range`, no need to repeat
  ourselves;
* proofs used wrong universes.
* Try to fix compile

### [2019-12-12 21:45:20](https://github.com/leanprover-community/mathlib/commit/3281698)
feat(data/padics/padic_integers): algebra structure Z_p -> Q_p ([#1796](https://github.com/leanprover-community/mathlib/pull/1796))
* feat(data/padics/padic_integers): algebra structure Z_p -> Q_p
* Update src/data/padics/padic_integers.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
* Fix build

### [2019-12-12 09:05:22](https://github.com/leanprover-community/mathlib/commit/69e861e)
feat(measure_theory/bochner_integration): connecting the Bochner integral with the integral on `ennreal`-valued functions ([#1790](https://github.com/leanprover-community/mathlib/pull/1790))
* shorter proof
* feat(measure_theory/bochner_integration): connecting the Bochner integral with the integral on `ennreal`
This PR proves that `∫ f = ∫ f⁺ - ∫ f⁻`, with the first integral sign being the Bochner integral of a real-valued function `f : α → ℝ`, and second and third integral sign being the integral on `ennreal`-valued functions. See `integral_eq_lintegral_max_sub_lintegral_min`.
I feel that most of the basic properties of the Bochner integral are proved. Please let me know if you think something else is needed.
* various things :
* add guides for typeclass inference;
* add `norm_cast` tags;
* prove some corollaries;
* add doc strings;
* other fixes
* Update bochner_integration.lean
* add some doc strings
* Fix doc strings
* Update bochner_integration.lean
* Update bochner_integration.lean
* fix doc strings
* Update bochner_integration.lean
* Use dot notation
* use dot notation
* Update Meas.lean

### [2019-12-11 17:17:17](https://github.com/leanprover-community/mathlib/commit/a8f6e23)
feat(data/list/basic): list.lex.not_nil_right ([#1797](https://github.com/leanprover-community/mathlib/pull/1797))

### [2019-12-11 09:52:57](https://github.com/leanprover-community/mathlib/commit/23e8ac7)
feat(ring_theory/algebra): elementary simp-lemmas for aeval ([#1795](https://github.com/leanprover-community/mathlib/pull/1795))

### [2019-12-10 19:03:24+01:00](https://github.com/leanprover-community/mathlib/commit/3a10c60)
chore(.mergify.yml): don't wait for travis when [ci skip] is present ([#1789](https://github.com/leanprover-community/mathlib/pull/1789))

### [2019-12-10 16:39:32](https://github.com/leanprover-community/mathlib/commit/361793a)
refactor(linear_algebra/finite_dimensional): universe polymorphism, doc  ([#1784](https://github.com/leanprover-community/mathlib/pull/1784))
* refactor(linear_algebra/finite_dimensional): universe polymorphism, doc
* docstrings
* improvements
* typo
* Update src/linear_algebra/dimension.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/linear_algebra/finite_dimensional.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/linear_algebra/finite_dimensional.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* fix comments
* fix build
* fix build
* remove pp.universe
* keep docstring in sync

### [2019-12-10 14:22:20](https://github.com/leanprover-community/mathlib/commit/6bb1728)
feat(analysis/convex): interiors/closures of convex sets are convex in a tvs ([#1781](https://github.com/leanprover-community/mathlib/pull/1781))
* feat(topology/algebra/module): scalar multiplication homeomorphisms
* feat(topology/algebra/module): more lemmas
- homeomorphisms given by scalar multiplication by unit is open/closed map.
* feat(analysis/convex): interior of convex set is convex in a tvs
- in separate file for interpretation time reasons.
* feat(analysis/convex): extract lemma
* feat(analysis/convex): closure of a convext set is convex
* style(analysis/convex): place lemmas at reasonable locations
* style(topology/algebra/module): fix bracketing style
* feat(analysis/convex): introduce `smul_set` and `pointwise_mul`
- also additional equivalent statements for convexity using those definitions.
* feat(algebra/pointwise): lemmas for `smul_set`
* doc(algebra/pointwise): add docstrings
* doc(algebra/pointwise): add global docstring
* docs(algebra/pointwise): amend global docstring

### [2019-12-09 20:49:33](https://github.com/leanprover-community/mathlib/commit/5c09372)
A `ring_exp` tactic for dealing with exponents in rings ([#1715](https://github.com/leanprover-community/mathlib/pull/1715))
* Test for ring_exp
* Implement -a/b * -a/b = a/b * a/b
* Hide extra information in the `ex` type in `ex_info`
* Some attempts to make the proof returned by ring_exp shorter
* Fix that ring_exp wouldn't handle pow that isn't monomial.has_pow
* Some optimizations in ring_exp
* Make all proofs explicit, halving execution time more or less
* Cache `has_add` and `has_mul` instances for another 2x speedup
* ring_exp can replace ring to compile mathlib
* Revert `ring` to non-test version
* Code cleanup and documentation
* Revert the test changes to `linarith`
* Undo the test changes to `ring2`
* Whitespace cleanup
* Fix overzealous error handling
Instead of catching any `fail` in eval, we just catch the operations that can
safely `fail` (i.e. `invert` and `negate`). This should make internal errors
visible again.
* Fix the TODO's
* Example use of ring_exp in data.polynomial
* Check that `ring_exp` deals well with natural number subtraction
* Fix incorrect docstring
* Improve documentation
* Small stylistic fixes
* Fix slow behaviour on large exponents
* Add `ring_exp` to the default tactics
* Use applicative notation where appropriate
* The `ring_exp` tactic also does normalization
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Move `normalize` from `tactic.interactive` to `ring_exp` namespace
* Fix name collision between `equiv` in data.equiv.basic and `equiv` in `test/tactics.lean`
I just renamed the definition in `test/tactics.lean` to `my_equiv`
and the operator to `my≅`.
* Fixes for the linter
* Fix the usage of type classes for `sub_pf` and `div_pf`
* Fix an additional linting error
* Optimization: we don't need norm_num to determine `x * 1 = x`
* Improve documentation of `test/ring_exp.lean`
* Rename `resolve_atoms` to `resolve_atom_aux` for clarity
* Small stylistic fixes
* Remove unneccessary hidden fields to `ex`
* Control how much unfolding `ring_exp` does by putting a `!` after it
* Reword comment for `ex_type`
* Use `ring_exp!` to deal with `(n : ℕ) + 1 - 1 = n`
* Document the `!` flag for `ring`, `ring_exp` and `ring_exp_eq`
* Get rid of searching for another cached instance
* Fix `ring_exp` failing on terms on the form `0^succ (succ ...)`

### [2019-12-09 11:40:19](https://github.com/leanprover-community/mathlib/commit/1809eb4)
feat(tactic/default): import suggest ([#1791](https://github.com/leanprover-community/mathlib/pull/1791))

### [2019-12-09 07:40:52](https://github.com/leanprover-community/mathlib/commit/acd769a)
feat(analysis/calculus/deriv): derivative of division and polynomials ([#1769](https://github.com/leanprover-community/mathlib/pull/1769))
* feat(data/set/intervals): more properties of intervals
* fix docstrings
* blank space
* iff versions
* fix docstring
* more details in docstrings
* initial commit
* div_deriv
* more derivatives
* cleanup
* better docstring
* fix
* better
* minor fix
* simp attributes
* Update src/analysis/calculus/deriv.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update src/analysis/calculus/deriv.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* nolint
* pow derivative
* Update src/topology/continuous_on.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* comp_add and friends
* remove useless variable

### [2019-12-07 19:47:19](https://github.com/leanprover-community/mathlib/commit/4c382b1)
(tactic/tidy): add docstring [skip ci] ([#1788](https://github.com/leanprover-community/mathlib/pull/1788))
* (tactic/tidy): add docstring [skip ci]
* Update src/tactic/tidy.lean
* mention [tidy] attribute

### [2019-12-07 17:48:37](https://github.com/leanprover-community/mathlib/commit/3c9f8f0)
feat(algebra/field_power): fpow is a strict mono ([#1778](https://github.com/leanprover-community/mathlib/pull/1778))
* WIP
* feat(algebra/field): remove is_field_hom
A field homomorphism is just a ring homomorphism.
This is one trivial tiny step in moving over to bundled homs.
* Fix up nolints.txt
* Process comments from reviews
* Rename lemma

### [2019-12-07 13:49:21](https://github.com/leanprover-community/mathlib/commit/0455962)
refactor(order/bounds,*): move code around to make `order.bounds` not depend on `complete_lattice` ([#1783](https://github.com/leanprover-community/mathlib/pull/1783))
* refactor(order/bounds,*): move code around to make `order.bounds` not depend on `complete_lattice`
In another PR I'm going to prove more facts in `order/bounds`, then
replace many proofs of lemmas about `(c)Sup`/`(c)Inf` with references to lemmas
about `is_lub`/`is_glb`.
* Move more code to `basic`, rewrite the only remaining proof in `default`
* Rename
* Add `default.lean`

### [2019-12-06 22:09:41](https://github.com/leanprover-community/mathlib/commit/6968d74)
chore(travis): add instance priority linter to CI ([#1787](https://github.com/leanprover-community/mathlib/pull/1787))
* add instance priority to linter
* Update mk_nolint.lean
* fix fintype.compact_space prio

### [2019-12-06 16:24:38](https://github.com/leanprover-community/mathlib/commit/8ca9263)
feat(topology/subset_properties): fintype.compact_space ([#1786](https://github.com/leanprover-community/mathlib/pull/1786))
Finite topological spaces are compact.

### [2019-12-06 15:20:53](https://github.com/leanprover-community/mathlib/commit/7084182)
feat(topology/dense_embedding): dense_range.equalizer ([#1785](https://github.com/leanprover-community/mathlib/pull/1785))
* feat(topology/dense_embedding): dense_range.equalizer
Two continuous functions to a t2-space
that agree on a dense set are equal.
* Fix docstring

### [2019-12-05 21:00:24](https://github.com/leanprover-community/mathlib/commit/7221900)
feat(data/set/basic): more lemmas about `set.nonempty` ([#1780](https://github.com/leanprover-community/mathlib/pull/1780))
* feat(data/set/basic): more lemmas about `set.nonempty`
* Fix compile

### [2019-12-05 17:22:16](https://github.com/leanprover-community/mathlib/commit/2adc122)
feat(data/set/finite): remove exists_finset_of_finite ([#1782](https://github.com/leanprover-community/mathlib/pull/1782))
* feat(data/set/finite): remove exists_finset_of_finite
exists_finset_of_finite is a duplicate of finite.exists_finset_coe
At same time, provide a `can_lift` instance to lift sets to finsets.
* Add docstring

### [2019-12-05 15:23:56](https://github.com/leanprover-community/mathlib/commit/3e6fe84)
feat(meta/expr): use structure_fields ([#1766](https://github.com/leanprover-community/mathlib/pull/1766))
removes is_structure_like
simplifies definition of is_structure
renames and simplifies definition get_projections. It is now called structure_fields_full

### [2019-12-05 06:07:31](https://github.com/leanprover-community/mathlib/commit/de377ea)
feat(algebra/field): remove is_field_hom ([#1777](https://github.com/leanprover-community/mathlib/pull/1777))
* feat(algebra/field): remove is_field_hom
A field homomorphism is just a ring homomorphism.
This is one trivial tiny step in moving over to bundled homs.
* Fix up nolints.txt
* Remove duplicate instances

### [2019-12-05 01:31:42](https://github.com/leanprover-community/mathlib/commit/324ae4b)
feat(data/set/basic): define `set.nonempty` ([#1779](https://github.com/leanprover-community/mathlib/pull/1779))
* Define `set.nonempty` and prove some basic lemmas
* Migrate `well_founded.min` to `set.nonempty`
* Fix a docstring and a few names
Based on comments in PR
* More docs
* Linebreaks
* +2 docstrings
* Fix compile
* Fix compile of `archive/imo1988_q6`

### [2019-12-04 19:03:55](https://github.com/leanprover-community/mathlib/commit/d4ee5b6)
fix(order.basic|ring_theory.algebra): lower instance priority ([#1729](https://github.com/leanprover-community/mathlib/pull/1729))
* algebra
* algebra2
* algebra3
* algebra4
* order.basic
* module
* algebra/ring
* explain default priority of 100
* undo priority changes

### [2019-12-04 15:51:17](https://github.com/leanprover-community/mathlib/commit/4353167)
doc(topology/basic): add a few doc strings [skip ci] ([#1775](https://github.com/leanprover-community/mathlib/pull/1775))
* doc(topology/basic): add a few doc strings
* Apply suggestions from code review

### [2019-12-04 13:46:21](https://github.com/leanprover-community/mathlib/commit/c43b332)
feat(data/set/intervals): more properties of intervals ([#1753](https://github.com/leanprover-community/mathlib/pull/1753))
* feat(data/set/intervals): more properties of intervals
* fix docstrings
* blank space
* iff versions
* fix docstring
* more details in docstrings

### [2019-12-04 09:12:47](https://github.com/leanprover-community/mathlib/commit/2c2cbb0)
feat(data/nat/prime): monoid.prime_pow and docs ([#1772](https://github.com/leanprover-community/mathlib/pull/1772))
* feat(data/nat/prime): monoid.prime_pow and docs
From the perfectoid project.
Also add some documentation.
* Add backticks in docs

### [2019-12-04 06:44:31](https://github.com/leanprover-community/mathlib/commit/71247eb)
feat(lift): check whether target is proposition ([#1767](https://github.com/leanprover-community/mathlib/pull/1767))
* feat(lift): check whether target is proposition
* simplify

### [2019-12-04 04:29:28](https://github.com/leanprover-community/mathlib/commit/c1105de)
feat(tactic): mk_simp_attribute command that includes doc string ([#1763](https://github.com/leanprover-community/mathlib/pull/1763))
* feat(tactic): mk_simp_attr command that includes doc string
* Update tactics.md
* rename mk_simp_attr to mk_simp_set
* rename again to mk_simp_attribute
* explain  syntax better
* simp with, not simp using
* simp with, not simp using
* avoid parsing ambiguity
* fix build
* Update docs/tactics.md
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>

### [2019-12-04 00:28:08](https://github.com/leanprover-community/mathlib/commit/b031290)
feat(data/finset): lemmas for folding min and max ([#1774](https://github.com/leanprover-community/mathlib/pull/1774))
From the perfectoid project.

### [2019-12-03 20:55:07](https://github.com/leanprover-community/mathlib/commit/827e78b)
feat(lint): avoid Travis error when declarations are renamed ([#1771](https://github.com/leanprover-community/mathlib/pull/1771))

### [2019-12-03 18:35:15](https://github.com/leanprover-community/mathlib/commit/866be5f)
feat(data/polynomial): monic.as_sum ([#1773](https://github.com/leanprover-community/mathlib/pull/1773))
From the perfectoid project.
It is often useful to write a monic polynomial f in the form
`X^n + sum of lower degree terms`.

### [2019-12-03 16:50:35](https://github.com/leanprover-community/mathlib/commit/922a4eb)
feat(set_theory/cardinal): eq_one_iff_subsingleton_and_nonempty ([#1770](https://github.com/leanprover-community/mathlib/pull/1770))
* feat(set_theory/cardinal): eq_one_iff_subsingleton_and_nonempty
From the perfectoid project
* Update src/set_theory/cardinal.lean

### [2019-12-03 14:47:38](https://github.com/leanprover-community/mathlib/commit/3266b96)
feat(tactic/lift): automatically handle pi types ([#1755](https://github.com/leanprover-community/mathlib/pull/1755))
* feat(tactic/lift): automatically handle pi types
* Add missing docs
* Update docs/tactics.md
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

### [2019-12-03 07:46:12](https://github.com/leanprover-community/mathlib/commit/89e7f6f)
feat(README): add link to Lean Links [skip ci] ([#1768](https://github.com/leanprover-community/mathlib/pull/1768))

### [2019-12-02 17:29:31](https://github.com/leanprover-community/mathlib/commit/3913d30)
refactor(topology/algebra): use dot notation in tendsto.add and friends ([#1765](https://github.com/leanprover-community/mathlib/pull/1765))

### [2019-12-02 14:48:24](https://github.com/leanprover-community/mathlib/commit/87929bf)
doc(*): correct bad markdown ([#1764](https://github.com/leanprover-community/mathlib/pull/1764))
* Update bochner_integration.lean
* Update mean_value.lean
* Update expr.lean
* Update doc.md

### [2019-12-02 09:14:36](https://github.com/leanprover-community/mathlib/commit/1c4a296)
chore(topology/*): dots for continuity proofs ([#1762](https://github.com/leanprover-community/mathlib/pull/1762))
* chore(topology/*): dots for continuity proofs
This is a sequel to 431551a891a270260b6ece53dcdff39a0527cf78
* fix build

### [2019-12-02 07:57:47](https://github.com/leanprover-community/mathlib/commit/89fd088)
feat(topology/uniform_space/cauchy): sequentially complete space with a countable basis is complete ([#1761](https://github.com/leanprover-community/mathlib/pull/1761))
* feat(topology/uniform_space/cauchy): sequentially complete space with a countable basis is complete
This is a more general version of what is currently proved in
`cau_seq_filter`. Migration of the latter file to the new code will be
done in a separate PR.
* Add docs, drop unused section vars, make arguments `U` and `U'` explicit.
* Update src/topology/uniform_space/cauchy.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Fix some comments

### [2019-12-01 17:32:14](https://github.com/leanprover-community/mathlib/commit/177cced)
feat(measure/bochner_integration): dominated convergence theorem ([#1757](https://github.com/leanprover-community/mathlib/pull/1757))
* feat(measure/bochner_integration): dominated convergence theorem
This PR
* proves the dominated convergence theorem
* and some other lemmas including `integral_congr_ae`, `norm_integral_le_lintegral_norm`.
* adds several equivalent definitions of the predicate `integrable` and shortens some proofs.
* fix linting error
* Add some section doc strings
* Indentation is very wrong
* Remove useless assumptions; fix doc strings
* remove `private`; add a doc string for Lebesgue's dominated convergence theorem
* Update basic.lean

### [2019-12-01 16:14:54](https://github.com/leanprover-community/mathlib/commit/8a89b06)
refactor(analysis/calculus/mean_value): prove the mean value theorem using 1D derivative ([#1740](https://github.com/leanprover-community/mathlib/pull/1740))
* refactor(analysis/calculus/mean_value): prove the mean value theorem using 1D derivative
* docstring
* use iff.rfl
* fix build
* fix docstring

### [2019-12-01 15:07:11](https://github.com/leanprover-community/mathlib/commit/431551a)
refactor(topology/algebra): use the dot notation in `continuous_mul` and friends ([#1758](https://github.com/leanprover-community/mathlib/pull/1758))
* continuous_add
* fixes
* more fixes
* fix
* tendsto_add
* fix tendsto
* last fix

### [2019-12-01 15:36:14+01:00](https://github.com/leanprover-community/mathlib/commit/a350f03)
chore(scripts/nolint.txt): regenerate