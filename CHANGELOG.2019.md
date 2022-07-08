### [2019-12-29T08:52:23+00:00](https://github.com/leanprover-community/mathlib/commit/acf2038a720036d2e6fdc035bc57627da71d343c)
feat(analysis/calculus/mean_value): more corollaries of the MVT ([#1819](https://github.com/leanprover-community/mathlib/pull/#1819))

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

Co-authored-by: sgouezel <sebastien.gouezel@univ-rennes1.fr>
Co-authored-by: mergify[bot] <37929162+mergify[bot]@users.noreply.github.com>

### [2019-12-28T20:31:03+00:00](https://github.com/leanprover-community/mathlib/commit/64770a898312524bc0e7d8495a45f8bb606cffdc)
feat(analysis/calculus/deriv): Prove equivalence of Fréchet derivative and the classical definition ([#1834](https://github.com/leanprover-community/mathlib/pull/#1834))

* feat(analysis/calculus/deriv): Prove equivalence of Fréchet derivative and the classical definition

* Fix a typo

* Move, change doc, add versions for `has_deriv_within_at` and `has_deriv_at`.

* Fix docstring, remove an unsed argument

### [2019-12-28T13:01:45+00:00](https://github.com/leanprover-community/mathlib/commit/e43905be6dd476248b65177b513a5237d8f8b509)
refactor(topology/algebra/ordered): formulate a few "Icc induction" principles ([#1833](https://github.com/leanprover-community/mathlib/pull/#1833))

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

Co-authored-by: sgouezel <sebastien.gouezel@univ-rennes1.fr>
Co-authored-by: mergify[bot] <37929162+mergify[bot]@users.noreply.github.com>

### [2019-12-28T11:42:42+00:00](https://github.com/leanprover-community/mathlib/commit/a6a8a11e25e683cbf1fae545818cb2a201f828c8)
refactor(data/equiv/encodable): bring `directed.sequence*` from `integration`, use `quotient.rep` instead of `quot.rep` ([#1825](https://github.com/leanprover-community/mathlib/pull/#1825))

* refactor(data/equiv/encodable): bring `directed.sequence*` from `integration`, use `quotient.rep` instead of `quot.rep`

`sequence_of_directed` in `measure_theory/integration` did not belong
there.

Also add some docstrings.

* doc/style fixes by @sgouezel

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Remove an unused argument, add a docstring

* Completely remove the `reflexive r` assumption

Co-authored-by: sgouezel <sebastien.gouezel@univ-rennes1.fr>
Co-authored-by: mergify[bot] <37929162+mergify[bot]@users.noreply.github.com>

### [2019-12-28T10:05:30+00:00](https://github.com/leanprover-community/mathlib/commit/340fa14657208c612a2a5348ef12014133cd9650)
feat(analysis/specific_limits): add a few more limits ([#1832](https://github.com/leanprover-community/mathlib/pull/#1832))

* feat(analysis/specific_limits): add a few more limits

* Drop 1 lemma, generalize two others.

* Rename `tendsto_inverse_at_top_nhds_0`, fix compile

### [2019-12-27T20:26:09+00:00](https://github.com/leanprover-community/mathlib/commit/0a9a1ff463a1f26e27d7c391eb7f6334f0d90383)
refactor(topology/algebra/ordered): use `tfae`, prove equality of some `nhds_within` ([#1831](https://github.com/leanprover-community/mathlib/pull/#1831))

* refactor(topology/algebra/ordered): use `tfae`, prove equality of some `nhds_within`

* Add missing `order_dual.*` instances

* Try to fix the build

* Fix formatting, rename some variables

* Fix compile

### [2019-12-27T18:11:30+00:00](https://github.com/leanprover-community/mathlib/commit/82ca7318a2c1007166f9db728e9e60917774c7ef)
refactor(calculus): simplify derivative extension ([#1826](https://github.com/leanprover-community/mathlib/pull/#1826))

* refactor(calculus): simplify derivative extension

* generalize continuous_within_at.closure_le

* Simplify proof following Sébastien

* Update src/analysis/calculus/extend_deriv.lean

Co-authored-by: sgouezel <sebastien.gouezel@univ-rennes1.fr>
Co-authored-by: mergify[bot] <37929162+mergify[bot]@users.noreply.github.com>

### [2019-12-27T15:35:17+00:00](https://github.com/leanprover-community/mathlib/commit/3a78f49ab3d9f9084eb9440185e6505b0e72bdb3)
feat(order/basic): add `dual_le` and `dual_lt` lemmas ([#1830](https://github.com/leanprover-community/mathlib/pull/#1830))

### [2019-12-27T14:05:28+00:00](https://github.com/leanprover-community/mathlib/commit/c9a81b00ab7123baeac9678d8cae7a8fd845df87)
refactor(*): unify API of `list/multiset/finset.prod_hom` ([#1820](https://github.com/leanprover-community/mathlib/pull/#1820))

* refactor(*): unify API of `list/multiset/finset.prod_hom`

Also remove `is_group_hom.map_prod`; use `*.prod_hom.symm` or
`monoid_hom.map_*prod` instead.

* Update src/ring_theory/ideal_operations.lean

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Restore explicit args of `list.fold(l/r)_hom`

* Fix `group_theory/perm/sign`

* Fix `quadratic_reciprocity`

* Fix compile

Co-authored-by: sgouezel <sebastien.gouezel@univ-rennes1.fr>
Co-authored-by: mergify[bot] <37929162+mergify[bot]@users.noreply.github.com>

### [2019-12-27T12:40:25+00:00](https://github.com/leanprover-community/mathlib/commit/0a87dd8c3499614cea361a42e98ea737efd8e610)
feat(topology/basic): a few simple lemmas ([#1829](https://github.com/leanprover-community/mathlib/pull/#1829))

* feat(topology/basic): a few simple lemmas

* Fix compile

Co-authored-by: mergify[bot] <37929162+mergify[bot]@users.noreply.github.com>

### [2019-12-27T11:08:24+00:00](https://github.com/leanprover-community/mathlib/commit/89854fa3a382b47be56099f861af7c56a9c811e8)
refactor(analysis/calculus/deriv): Use equality of functions ([#1818](https://github.com/leanprover-community/mathlib/pull/#1818))

* refactor(analysis/calculus/deriv): Use equality of functions

This way we can rewrite, e.g., in `deriv (deriv sin)`.

* Restore some old lemmas

* Restore old `deriv_cos`, fix `deriv_id'`

* Update src/analysis/calculus/deriv.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Fix compile

Co-authored-by: Johan Commelin <johan@commelin.net>
Co-authored-by: mergify[bot] <37929162+mergify[bot]@users.noreply.github.com>

### [2019-12-27T09:41:58+00:00](https://github.com/leanprover-community/mathlib/commit/c1a993d923db38d648a4c9b894466c62c47a7084)
feat(data/set/intervals): unions of adjacent intervals ([#1827](https://github.com/leanprover-community/mathlib/pull/#1827))

### [2019-12-26T16:34:12+00:00](https://github.com/leanprover-community/mathlib/commit/7e2d4b853b53d33d0b7fc243d460d14fc3879726)
feat(analysis/calculus/extend_deriv): extend differentiability to the boundary ([#1794](https://github.com/leanprover-community/mathlib/pull/#1794))

* feat(analysis/calculus/extend_deriv): extend differentiability to the boundary

* fix build

Co-authored-by: mergify[bot] <37929162+mergify[bot]@users.noreply.github.com>

### [2019-12-24T05:40:16+00:00](https://github.com/leanprover-community/mathlib/commit/9a9f617a23ba46e8dc3fc5a36cc394f34cf37b2d)
fix(topology/algebra/infinite_sum): add a hint to speed up elaboration ([#1824](https://github.com/leanprover-community/mathlib/pull/#1824))

Fix suggested by Joe on Zulip.

Co-authored-by: mergify[bot] <37929162+mergify[bot]@users.noreply.github.com>

### [2019-12-23T23:32:58+00:00](https://github.com/leanprover-community/mathlib/commit/64921a4cb428e37e72963be7d049f36729911347)
refactor(topology/*): migrate to `uniform_space.complete_of_convergent_controlled_sequences` ([#1821](https://github.com/leanprover-community/mathlib/pull/#1821))

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

Co-authored-by: sgouezel <sebastien.gouezel@univ-rennes1.fr>
Co-authored-by: mergify[bot] <37929162+mergify[bot]@users.noreply.github.com>

### [2019-12-23T22:13:46+00:00](https://github.com/leanprover-community/mathlib/commit/439ac4e9d5d5076d4c3dd4c9d3943ca5dce8c1da)
feat(analysis/calculus/local_extr): Fermat's Theorem, Rolle's Theorem, Lagrange's MVT, Cauchy's MVT ([#1807](https://github.com/leanprover-community/mathlib/pull/#1807))

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

Co-authored-by: sgouezel <sebastien.gouezel@univ-rennes1.fr>

### [2019-12-20T20:34:56+00:00](https://github.com/leanprover-community/mathlib/commit/883d974b608845bad30ae19e27e33c285200bf84)
feat(algebra/module): sum_smul' (for semimodules) ([#1752](https://github.com/leanprover-community/mathlib/pull/#1752))

* feat(algebra/module): sum_smul' (for semimodules)

* adding docstring

* use `classical` tactic

* moving ' name to the weaker theorem

### [2019-12-19T06:24:53+00:00](https://github.com/leanprover-community/mathlib/commit/e8754920246fb2669a5f36292b0041d458acd8e0)
chore(algebra/module) remove an unneeded commutativity assumption ([#1813](https://github.com/leanprover-community/mathlib/pull/#1813))

### [2019-12-18T12:57:28+00:00](https://github.com/leanprover-community/mathlib/commit/5dae5d233a6e3b617c15aa1ee88e377bd445d476)
chore(ring_theory/algebra): redefine module structure of Z-algebra instance ([#1812](https://github.com/leanprover-community/mathlib/pull/#1812))

This redefines the Z-algebra instance, so that the module structure is definitionally equal to the Z-module structure of any `add_comm_group`

### [2019-12-18T09:23:47+00:00](https://github.com/leanprover-community/mathlib/commit/bec46afdfefec72d64786d988744185b74981355)
refactor(topology/*): use dot notation with `compact`, prove `compact.image` with `continuous_on` ([#1809](https://github.com/leanprover-community/mathlib/pull/#1809))

* refactor(topology/*): use dot notation, prove `compact.image` with `continuous_on`

* Apply suggestions from code review

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Fix compile, update some proofs

* Make `range_quot_mk` a `simp` lemma

* Fix lint errors

### [2019-12-18T06:01:42+00:00](https://github.com/leanprover-community/mathlib/commit/12075180957afa1094899a4136efb830388e8587)
feat(*): add command for declaring library notes ([#1810](https://github.com/leanprover-community/mathlib/pull/#1810))

* feat(*): add command for declaring library notes

* add missing file

* make note names private

* update docs

* Update library_note.lean

* Update library_note.lean

### [2019-12-17T22:12:07+00:00](https://github.com/leanprover-community/mathlib/commit/acdf2729eb5e01c15cacf571e4972d965414d76f)
chore(data/fintype): use `list.fin_range` for `fin.fintype` ([#1811](https://github.com/leanprover-community/mathlib/pull/#1811))

### [2019-12-17T18:02:26+00:00](https://github.com/leanprover-community/mathlib/commit/52e1872346d126a8528a8f81d3ff24ca69b7dadb)
refactor(topology/algebra/ordered): prove IVT for a connected set ([#1806](https://github.com/leanprover-community/mathlib/pull/#1806))

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

### [2019-12-17T14:48:50+00:00](https://github.com/leanprover-community/mathlib/commit/d8dc1445cf8a8c74f8df60b9f7a1f5cf10946666)
feat(geometry/manifold): smooth bundles, tangent bundle ([#1607](https://github.com/leanprover-community/mathlib/pull/#1607))

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

### [2019-12-17T13:38:54+00:00](https://github.com/leanprover-community/mathlib/commit/308a08ce72988f5bc2fb301187cb0652f7326fca)
refactor(topology/metric_space/closeds): migrate to `cauchy_seq_of_edist_le_geometric_two` ([#1760](https://github.com/leanprover-community/mathlib/pull/#1760))

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

### [2019-12-17T08:52:57+00:00](https://github.com/leanprover-community/mathlib/commit/3053a16942cf8bc388eb4758cf9f9f5c0ff02ccb)
feat(tactic/field_simp): tactic to reduce to one division in fields ([#1792](https://github.com/leanprover-community/mathlib/pull/#1792))

* feat(algebra/field): simp set to reduce to one division in fields

* tactic field_simp

* fix docstring

* fix build

### [2019-12-17T07:44:28+00:00](https://github.com/leanprover-community/mathlib/commit/abea298497330c406d32709097776a0c65cce831)
refactor(analysis/specific_limits): use `ennreal`s instead of `nnreal`s in `*_edist_le_geometric` ([#1759](https://github.com/leanprover-community/mathlib/pull/#1759))

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

### [2019-12-16T14:15:11+00:00](https://github.com/leanprover-community/mathlib/commit/cd53e272d1fd0f4f085adfbb131f6394155641f1)
chore(topology/algebra/ordered): use interval notation here and there ([#1802](https://github.com/leanprover-community/mathlib/pull/#1802))

* chore(topology/algebra/ordered): use interval notation here and there

Also prove a slightly more general version of `mem_nhds_orderable_dest`

* Fix a few compile errors

* Rename a lemma, fix compile, add docs and `dual_I??` lemmas

* Fix names, add comments

* Make some lemmas simp

### [2019-12-16T10:20:01+00:00](https://github.com/leanprover-community/mathlib/commit/de25b101909d1ff76b632852b568a4c473ac736a)
refactor(analysis/convex): simplify proofs, use implicit args and  dot notation ([#1804](https://github.com/leanprover-community/mathlib/pull/#1804))

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

### [2019-12-16T08:11:28+00:00](https://github.com/leanprover-community/mathlib/commit/6188b991e2bd227b915a7ab4eb872a66d169c012)
feat(topology/instances/ennreal): more lemmas about tsum ([#1756](https://github.com/leanprover-community/mathlib/pull/#1756))

* feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic

* Undo name change

* Fix compile

* nnreal: add `move_cast`

* ennreal: more lemmas

* Fix compile

* feat(topology/instances/ennreal): more lemmas

* Fix compile

### [2019-12-16T07:01:34+00:00](https://github.com/leanprover-community/mathlib/commit/ee981c286a70844227ff5d0c6816be934815409a)
refactor(analysis/calculus/fderiv): prove `has_fderiv_within_at.lim` for any filter ([#1805](https://github.com/leanprover-community/mathlib/pull/#1805))

* refactor(analysis/calculus/fderiv): prove `has_fderiv_within_at.lim` for any filter

Also prove two versions of "directional derivative agrees with
`has_fderiv_at`": `has_fderiv_at.lim` and `has_fderiv_at.lim_real`.

* Rename a lemma as suggested by @sgouezel

### [2019-12-15T22:29:01+00:00](https://github.com/leanprover-community/mathlib/commit/699da421ea1a19c3b024bf8c02d6f1dd1d7e89d3)
feat(data/set/intervals): add `nonempty_Icc` etc, `image_(add/mul)_(left/right)_Icc` ([#1803](https://github.com/leanprover-community/mathlib/pull/#1803))

### [2019-12-15T21:28:53+00:00](https://github.com/leanprover-community/mathlib/commit/7cda8bb16ee5ffcc48f638e08a374ca4e4b7c109)
feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic ([#1754](https://github.com/leanprover-community/mathlib/pull/#1754))

* feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic

* Undo name change

* Fix compile

* nnreal: add `move_cast`

* ennreal: more lemmas

* Fix compile

### [2019-12-15T19:32:42+00:00](https://github.com/leanprover-community/mathlib/commit/871a36fc80f44ec9a2e924973322a5c48b95c760)
feat(group_theory/monoid_localization) add localizations of commutative monoids at submonoids ([#1798](https://github.com/leanprover-community/mathlib/pull/#1798))

* 1st half of monoid_localization

* change in implementation notes

* fixing naming clashes

* change additive version's name

* oops, had a /- instead of /--

* generalize comm_monoid instance

* remove notes to self

* responding to PR comments

### [2019-12-15T17:52:56+00:00](https://github.com/leanprover-community/mathlib/commit/7dfbcdd41c7c883a66a046ed262cc49d4e6b6c48)
(docs/tactics.md) adding `norm_num` [ci skip] ([#1799](https://github.com/leanprover-community/mathlib/pull/#1799))

* (docs/tactics.md) adding `norm_num` [ci skip]

* fixing example

* clarifying explanation, adding more examples

* one more example

* one more example

* editing norm_num docstring

### [2019-12-15T16:39:49+00:00](https://github.com/leanprover-community/mathlib/commit/9a37e3fd00b4dd8399b04485970650bc7d150815)
refactor(*): make vector_space an abbreviation for module ([#1793](https://github.com/leanprover-community/mathlib/pull/#1793))

* refactor(*): make vector_space an abbreviation for module

* Remove superfluous instances

* Fix build

* Add Note[vector space definition]

* Update src/algebra/module.lean

* Fix build (hopefully)

* Update src/measure_theory/bochner_integration.lean

### [2019-12-13T22:04:36+00:00](https://github.com/leanprover-community/mathlib/commit/a3844c85c606acca5922408217d55891b760fad6)
chore(algebra/group/basic): DRY, add `mul_left_surjective` ([#1801](https://github.com/leanprover-community/mathlib/pull/#1801))

Some lemmas explicitly listed arguments already declared using
`variables`, remove them.

### [2019-12-13T18:10:30+01:00](https://github.com/leanprover-community/mathlib/commit/bb7d4c98265dd75599a7067da9370e49405054e4)
chore(data/set/lattice): drop `Union_eq_sUnion_range` and `Inter_eq_sInter_range` ([#1800](https://github.com/leanprover-community/mathlib/pull/#1800))

* chore(data/set/lattice): drop `Union_eq_sUnion_range` and `Inter_eq_sInter_range`

Two reasons:

* we already have `sUnion_range` and `sInter_range`, no need to repeat
  ourselves;
* proofs used wrong universes.

* Try to fix compile

### [2019-12-12T21:45:20+00:00](https://github.com/leanprover-community/mathlib/commit/32816989303e1c811ef474343c5abf70e68ba578)
feat(data/padics/padic_integers): algebra structure Z_p -> Q_p ([#1796](https://github.com/leanprover-community/mathlib/pull/#1796))

* feat(data/padics/padic_integers): algebra structure Z_p -> Q_p

* Update src/data/padics/padic_integers.lean

Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>

* Fix build

### [2019-12-12T09:05:22+00:00](https://github.com/leanprover-community/mathlib/commit/69e861e9fe786dac4b5131e0fac6737bd27d2358)
feat(measure_theory/bochner_integration): connecting the Bochner integral with the integral on `ennreal`-valued functions ([#1790](https://github.com/leanprover-community/mathlib/pull/#1790))

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

### [2019-12-11T17:17:17+00:00](https://github.com/leanprover-community/mathlib/commit/a8f6e23be7f038df208343cedd838636484a5c90)
feat(data/list/basic): list.lex.not_nil_right ([#1797](https://github.com/leanprover-community/mathlib/pull/#1797))

### [2019-12-11T09:52:57+00:00](https://github.com/leanprover-community/mathlib/commit/23e8ac73dd4eb2f8c2779e89b0c4ef803a377b22)
feat(ring_theory/algebra): elementary simp-lemmas for aeval ([#1795](https://github.com/leanprover-community/mathlib/pull/#1795))

### [2019-12-10T19:03:24+01:00](https://github.com/leanprover-community/mathlib/commit/3a10c600729c5cf5ddb74af5f5e1d43831df6d31)
chore(.mergify.yml): don't wait for travis when [ci skip] is present ([#1789](https://github.com/leanprover-community/mathlib/pull/#1789))

### [2019-12-10T16:39:32+00:00](https://github.com/leanprover-community/mathlib/commit/361793a7336c135011c9b4482b83d92abe2eebb3)
refactor(linear_algebra/finite_dimensional): universe polymorphism, doc  ([#1784](https://github.com/leanprover-community/mathlib/pull/#1784))

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

### [2019-12-10T14:22:20+00:00](https://github.com/leanprover-community/mathlib/commit/6bb17284eadeb0dfc5516ebe44f2a631959c483d)
feat(analysis/convex): interiors/closures of convex sets are convex in a tvs ([#1781](https://github.com/leanprover-community/mathlib/pull/#1781))

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

### [2019-12-09T20:49:33+00:00](https://github.com/leanprover-community/mathlib/commit/5c09372658861c46bb4bf8d2b399601c5a711bb4)
A `ring_exp` tactic for dealing with exponents in rings ([#1715](https://github.com/leanprover-community/mathlib/pull/#1715))

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

### [2019-12-09T11:40:19+00:00](https://github.com/leanprover-community/mathlib/commit/1809eb4058bc4cccb43e2cbfb278a574591d020a)
feat(tactic/default): import suggest ([#1791](https://github.com/leanprover-community/mathlib/pull/#1791))

### [2019-12-09T07:40:52+00:00](https://github.com/leanprover-community/mathlib/commit/acd769af1ee9f01b3e30ac51629a15696d8793a3)
feat(analysis/calculus/deriv): derivative of division and polynomials ([#1769](https://github.com/leanprover-community/mathlib/pull/#1769))

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

### [2019-12-07T19:47:19+00:00](https://github.com/leanprover-community/mathlib/commit/4c382b1202d47770860049c05421b90e8ab9b24e)
(tactic/tidy): add docstring [skip ci] ([#1788](https://github.com/leanprover-community/mathlib/pull/#1788))

* (tactic/tidy): add docstring [skip ci]

* Update src/tactic/tidy.lean

* mention [tidy] attribute

### [2019-12-07T17:48:37+00:00](https://github.com/leanprover-community/mathlib/commit/3c9f8f0f318d1dc445ad63427d16d2a2bc61d994)
feat(algebra/field_power): fpow is a strict mono ([#1778](https://github.com/leanprover-community/mathlib/pull/#1778))

* WIP

* feat(algebra/field): remove is_field_hom

A field homomorphism is just a ring homomorphism.
This is one trivial tiny step in moving over to bundled homs.

* Fix up nolints.txt

* Process comments from reviews

* Rename lemma

### [2019-12-07T13:49:21+00:00](https://github.com/leanprover-community/mathlib/commit/0455962924f26c9bc76ed84f741ede13b46dd62c)
refactor(order/bounds,*): move code around to make `order.bounds` not depend on `complete_lattice` ([#1783](https://github.com/leanprover-community/mathlib/pull/#1783))

* refactor(order/bounds,*): move code around to make `order.bounds` not depend on `complete_lattice`

In another PR I'm going to prove more facts in `order/bounds`, then
replace many proofs of lemmas about `(c)Sup`/`(c)Inf` with references to lemmas
about `is_lub`/`is_glb`.

* Move more code to `basic`, rewrite the only remaining proof in `default`

* Rename

* Add `default.lean`

### [2019-12-06T22:09:41+00:00](https://github.com/leanprover-community/mathlib/commit/6968d749fd8d127e65af90d08722a0341b779633)
chore(travis): add instance priority linter to CI ([#1787](https://github.com/leanprover-community/mathlib/pull/#1787))

* add instance priority to linter

* Update mk_nolint.lean

* fix fintype.compact_space prio

### [2019-12-06T16:24:38+00:00](https://github.com/leanprover-community/mathlib/commit/8ca926372a198c4682d72d3b33ea2f33580e96df)
feat(topology/subset_properties): fintype.compact_space ([#1786](https://github.com/leanprover-community/mathlib/pull/#1786))

Finite topological spaces are compact.

### [2019-12-06T15:20:53+00:00](https://github.com/leanprover-community/mathlib/commit/708418244980a43f270143bc3da18183d7c97a2e)
feat(topology/dense_embedding): dense_range.equalizer ([#1785](https://github.com/leanprover-community/mathlib/pull/#1785))

* feat(topology/dense_embedding): dense_range.equalizer

Two continuous functions to a t2-space
that agree on a dense set are equal.

* Fix docstring

### [2019-12-05T21:00:24+00:00](https://github.com/leanprover-community/mathlib/commit/7221900b8b0da754937d0c87a31cf7dab74f296e)
feat(data/set/basic): more lemmas about `set.nonempty` ([#1780](https://github.com/leanprover-community/mathlib/pull/#1780))

* feat(data/set/basic): more lemmas about `set.nonempty`

* Fix compile

### [2019-12-05T17:22:16+00:00](https://github.com/leanprover-community/mathlib/commit/2adc122cf77573f0ea39ce05f86e5a5367aea713)
feat(data/set/finite): remove exists_finset_of_finite ([#1782](https://github.com/leanprover-community/mathlib/pull/#1782))

* feat(data/set/finite): remove exists_finset_of_finite

exists_finset_of_finite is a duplicate of finite.exists_finset_coe
At same time, provide a `can_lift` instance to lift sets to finsets.

* Add docstring

### [2019-12-05T15:23:56+00:00](https://github.com/leanprover-community/mathlib/commit/3e6fe842b818dcbe521226d4c1d4e5150010ddb9)
feat(meta/expr): use structure_fields ([#1766](https://github.com/leanprover-community/mathlib/pull/#1766))

removes is_structure_like
simplifies definition of is_structure
renames and simplifies definition get_projections. It is now called structure_fields_full

### [2019-12-05T06:07:31+00:00](https://github.com/leanprover-community/mathlib/commit/de377ea3dfe0af45995529948003e8acc4c49ced)
feat(algebra/field): remove is_field_hom ([#1777](https://github.com/leanprover-community/mathlib/pull/#1777))

* feat(algebra/field): remove is_field_hom

A field homomorphism is just a ring homomorphism.
This is one trivial tiny step in moving over to bundled homs.

* Fix up nolints.txt

* Remove duplicate instances

### [2019-12-05T01:31:42+00:00](https://github.com/leanprover-community/mathlib/commit/324ae4b1a530f96dcf462d4cbf16ce81a3bf1dcd)
feat(data/set/basic): define `set.nonempty` ([#1779](https://github.com/leanprover-community/mathlib/pull/#1779))

* Define `set.nonempty` and prove some basic lemmas

* Migrate `well_founded.min` to `set.nonempty`

* Fix a docstring and a few names

Based on comments in PR

* More docs

* Linebreaks

* +2 docstrings

* Fix compile

* Fix compile of `archive/imo1988_q6`

### [2019-12-04T19:03:55+00:00](https://github.com/leanprover-community/mathlib/commit/d4ee5b69427195b7cc8c8e9debbe1efbde9d1aae)
fix(order.basic|ring_theory.algebra): lower instance priority ([#1729](https://github.com/leanprover-community/mathlib/pull/#1729))

* algebra

* algebra2

* algebra3

* algebra4

* order.basic

* module

* algebra/ring

* explain default priority of 100

* undo priority changes

### [2019-12-04T15:51:17+00:00](https://github.com/leanprover-community/mathlib/commit/435316767c3de8fef4d3da3149d47e289dbadd5d)
doc(topology/basic): add a few doc strings [skip ci] ([#1775](https://github.com/leanprover-community/mathlib/pull/#1775))

* doc(topology/basic): add a few doc strings

* Apply suggestions from code review

### [2019-12-04T13:46:21+00:00](https://github.com/leanprover-community/mathlib/commit/c43b3329f203b72ecc93cde6269e8b11d7af6afe)
feat(data/set/intervals): more properties of intervals ([#1753](https://github.com/leanprover-community/mathlib/pull/#1753))

* feat(data/set/intervals): more properties of intervals

* fix docstrings

* blank space

* iff versions

* fix docstring

* more details in docstrings

### [2019-12-04T09:12:47+00:00](https://github.com/leanprover-community/mathlib/commit/2c2cbb0dc33bef42c292447c16f5eb8cb7bcd133)
feat(data/nat/prime): monoid.prime_pow and docs ([#1772](https://github.com/leanprover-community/mathlib/pull/#1772))

* feat(data/nat/prime): monoid.prime_pow and docs

From the perfectoid project.
Also add some documentation.

* Add backticks in docs

### [2019-12-04T06:44:31+00:00](https://github.com/leanprover-community/mathlib/commit/71247ebed72e73f2651491822af244f4cc1e367d)
feat(lift): check whether target is proposition ([#1767](https://github.com/leanprover-community/mathlib/pull/#1767))

* feat(lift): check whether target is proposition

* simplify

### [2019-12-04T04:29:28+00:00](https://github.com/leanprover-community/mathlib/commit/c1105de1d278b3974f17ddb9f91b31e60fe32126)
feat(tactic): mk_simp_attribute command that includes doc string ([#1763](https://github.com/leanprover-community/mathlib/pull/#1763))

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

### [2019-12-04T00:28:08+00:00](https://github.com/leanprover-community/mathlib/commit/b031290b228838d5e779908b129420331bb131c5)
feat(data/finset): lemmas for folding min and max ([#1774](https://github.com/leanprover-community/mathlib/pull/#1774))

From the perfectoid project.

### [2019-12-03T20:55:07+00:00](https://github.com/leanprover-community/mathlib/commit/827e78b1638868734de786baac70b5d3f1d5118e)
feat(lint): avoid Travis error when declarations are renamed ([#1771](https://github.com/leanprover-community/mathlib/pull/#1771))

### [2019-12-03T18:35:15+00:00](https://github.com/leanprover-community/mathlib/commit/866be5f67dd9ec5107ee1d507256572ac60a4a5a)
feat(data/polynomial): monic.as_sum ([#1773](https://github.com/leanprover-community/mathlib/pull/#1773))

From the perfectoid project.
It is often useful to write a monic polynomial f in the form
`X^n + sum of lower degree terms`.

### [2019-12-03T16:50:35+00:00](https://github.com/leanprover-community/mathlib/commit/922a4ebe29d39b67079e5e930d9c1afe45f7850c)
feat(set_theory/cardinal): eq_one_iff_subsingleton_and_nonempty ([#1770](https://github.com/leanprover-community/mathlib/pull/#1770))

* feat(set_theory/cardinal): eq_one_iff_subsingleton_and_nonempty

From the perfectoid project

* Update src/set_theory/cardinal.lean

### [2019-12-03T14:47:38+00:00](https://github.com/leanprover-community/mathlib/commit/3266b9606c713f6eb8808a42f6ae743c338024e0)
feat(tactic/lift): automatically handle pi types ([#1755](https://github.com/leanprover-community/mathlib/pull/#1755))

* feat(tactic/lift): automatically handle pi types

* Add missing docs

* Update docs/tactics.md

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

### [2019-12-03T07:46:12+00:00](https://github.com/leanprover-community/mathlib/commit/89e7f6fd232998f8cbe883eca4b4d5299f75754f)
feat(README): add link to Lean Links [skip ci] ([#1768](https://github.com/leanprover-community/mathlib/pull/#1768))

### [2019-12-02T17:29:31+00:00](https://github.com/leanprover-community/mathlib/commit/3913d303d0ea2a0f7e654dd927698b11e92bae4f)
refactor(topology/algebra): use dot notation in tendsto.add and friends ([#1765](https://github.com/leanprover-community/mathlib/pull/#1765))

### [2019-12-02T14:48:24+00:00](https://github.com/leanprover-community/mathlib/commit/87929bf701efd7506a1b339ad70b278a3d53d468)
doc(*): correct bad markdown ([#1764](https://github.com/leanprover-community/mathlib/pull/#1764))

* Update bochner_integration.lean

* Update mean_value.lean

* Update expr.lean

* Update doc.md

### [2019-12-02T09:14:36+00:00](https://github.com/leanprover-community/mathlib/commit/1c4a2966ef25ec82e65337022a0764e87a81d992)
chore(topology/*): dots for continuity proofs ([#1762](https://github.com/leanprover-community/mathlib/pull/#1762))

* chore(topology/*): dots for continuity proofs

This is a sequel to 431551a891a270260b6ece53dcdff39a0527cf78

* fix build

### [2019-12-02T07:57:47+00:00](https://github.com/leanprover-community/mathlib/commit/89fd08834bca00a7bd47b57c3cd8e78bba6216c9)
feat(topology/uniform_space/cauchy): sequentially complete space with a countable basis is complete ([#1761](https://github.com/leanprover-community/mathlib/pull/#1761))

* feat(topology/uniform_space/cauchy): sequentially complete space with a countable basis is complete

This is a more general version of what is currently proved in
`cau_seq_filter`. Migration of the latter file to the new code will be
done in a separate PR.

* Add docs, drop unused section vars, make arguments `U` and `U'` explicit.

* Update src/topology/uniform_space/cauchy.lean

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Fix some comments

### [2019-12-01T17:32:14+00:00](https://github.com/leanprover-community/mathlib/commit/177ccedb21ca423105081e4a20778a34f3ee356f)
feat(measure/bochner_integration): dominated convergence theorem ([#1757](https://github.com/leanprover-community/mathlib/pull/#1757))

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

### [2019-12-01T16:14:54+00:00](https://github.com/leanprover-community/mathlib/commit/8a89b06305ba6d47f1190a6e98bcde836f1ed57d)
refactor(analysis/calculus/mean_value): prove the mean value theorem using 1D derivative ([#1740](https://github.com/leanprover-community/mathlib/pull/#1740))

* refactor(analysis/calculus/mean_value): prove the mean value theorem using 1D derivative

* docstring

* use iff.rfl

* fix build

* fix docstring

### [2019-12-01T15:07:11+00:00](https://github.com/leanprover-community/mathlib/commit/431551a891a270260b6ece53dcdff39a0527cf78)
refactor(topology/algebra): use the dot notation in `continuous_mul` and friends ([#1758](https://github.com/leanprover-community/mathlib/pull/#1758))

* continuous_add

* fixes

* more fixes

* fix

* tendsto_add

* fix tendsto

* last fix

### [2019-12-01T15:36:14+01:00](https://github.com/leanprover-community/mathlib/commit/a350f0348c435909076f62b96b98c9346692ed59)
chore(scripts/nolint.txt): regenerate

### [2019-11-30T16:23:56+00:00](https://github.com/leanprover-community/mathlib/commit/343c54d6a39b1ac9d09ebc9cc987765833f7d83a)
feat(analysis/complex/exponential): limits of exp ([#1744](https://github.com/leanprover-community/mathlib/pull/#1744))

* staging

* exp div pow

* cleanup

* oops

* better proof

* cleanup

* docstring

* typo in docstring

### [2019-11-29T21:47:26+00:00](https://github.com/leanprover-community/mathlib/commit/e68b2be5c4b870f93b94ab48d6fe3f8e5382ea87)
doc(docs/contribute, meta/expr): sectioning doc strings  ([#1723](https://github.com/leanprover-community/mathlib/pull/#1723))

* doc(docs/contribute, meta/expr): explain sectioning doc strings and show in practice

* updates

### [2019-11-29T20:59:58+00:00](https://github.com/leanprover-community/mathlib/commit/b46ef845b5ce1a591279e1d631ba87a1f9e94d95)
doc(windows.md): update [ci skip] ([#1742](https://github.com/leanprover-community/mathlib/pull/#1742))

* doc(windows.md): update [ci skip]

* small

* Update docs/install/windows.md

Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>

* wording

### [2019-11-29T18:51:59+00:00](https://github.com/leanprover-community/mathlib/commit/9bb69dca3d8cb9ed7355c0772166bff3adebf387)
feat(analysis/specific_limits): add `cauchy_seq_of_edist_le_geometric` ([#1743](https://github.com/leanprover-community/mathlib/pull/#1743))

* feat(analysis/specific_limits): add `cauchy_seq_of_edist_le_geometric`

Other changes:

* Estimates on the convergence rate both in `edist` and `dist` cases.
* Swap lhs with lhs in `ennreal.tsum_coe` and `nnreal.tsum_coe`,
  rename accordingly
* Use `(1 - r)⁻¹` instead of `1 / (1 - r)` in `has_sum_geometric`

* Add some docstrings

* Update src/analysis/specific_limits.lean

### [2019-11-29T16:54:30+00:00](https://github.com/leanprover-community/mathlib/commit/817711d8bffc29c5c51a9ff951cafc53afc3e70b)
feat(measure_theory/bochner_integration): linearity of the Bochner Integral ([#1745](https://github.com/leanprover-community/mathlib/pull/#1745))

* Linearity of the Bochner Integral

* prove integral_neg and integral_smul with less assumptions; make integral irreducible

* remove simp tag

* create simp set for integral

* Add simp_attr.integral to nolint

* Make it possible to unfold the definition of `integral`

and other things.

* Update nolints.txt

* Make it possible to unfold l1.integral

* Update bochner_integration.lean

* Update bochner_integration.lean

### [2019-11-29T14:50:53+00:00](https://github.com/leanprover-community/mathlib/commit/65bdbabc38fd54918695417d7da6e59220c2d7ec)
chore(topology/instances/ennreal): simplify some statements&proofs ([#1750](https://github.com/leanprover-community/mathlib/pull/#1750))

API changes:

* `nhds_top`: use `⨅a ≠ ∞` instead of `⨅a:{a:ennreal // a ≠ ⊤}`
* `nhds_zero`, `nhds_of_ne_top` : similarly to `nhds_top`
* `tendsto_nhds`: get rid of the intermediate set `n`.

### [2019-11-29T13:45:43+00:00](https://github.com/leanprover-community/mathlib/commit/8f11c466c66bd06bde1dcc798dbde04f1f299e50)
feat(data/real/ennreal): more simp lemmas about `inv` and continuity of `inv` ([#1749](https://github.com/leanprover-community/mathlib/pull/#1749))

* Prove some algebraic properties of `ennreal.inv`

* More algebraic lemmas

* Prove continuity of `inv`

### [2019-11-29T11:45:14+00:00](https://github.com/leanprover-community/mathlib/commit/1b3347df155b1094e37ac55c2dcb35982f529292)
feat(algebra/*,data/real/*): add some inequalities about `canonically_ordered_comm_semiring`s ([#1746](https://github.com/leanprover-community/mathlib/pull/#1746))

Use them for `nnreal` and `ennreal`.

### [2019-11-29T07:22:29+00:00](https://github.com/leanprover-community/mathlib/commit/8e74c62a3b0c0e2a1eb908c1170d1423b4b67e0c)
chore(data/finset,order/filter): simplify a few proofs ([#1747](https://github.com/leanprover-community/mathlib/pull/#1747))

Also add `finset.image_mono` and `finset.range_mono`.

### [2019-11-27T19:49:59+00:00](https://github.com/leanprover-community/mathlib/commit/198fb09d89d19e958276295c8f0b2cfe539688eb)
feat(analysis/complex/exponential): derivatives ([#1695](https://github.com/leanprover-community/mathlib/pull/#1695))

* feat(analysis/complex/exponential): derivatives

* nhds

* nhds

* remove omega

* remove set_option

* simp attributes, field type

* restrict scalar

* staging

* complete proof

* staging

* cleanup

* staging

* cleanup

* docstring

* docstring

* reviewer's comments

* real derivatives of exp, sin, cos, sinh, cosh

* fix build

* remove priority

* better proofs

### [2019-11-27T17:34:07+00:00](https://github.com/leanprover-community/mathlib/commit/01b1576c5d81eb4234e061da9f4cef79a247665f)
feat(topology/algebra/infinite_sum): prove `cauchy_seq_of_edist_le_of_summable` ([#1739](https://github.com/leanprover-community/mathlib/pull/#1739))

* feat(topology/algebra/infinite_sum): prove `cauchy_seq_of_edist_le_of_summable`

Other changes:

* Add estimates on the distance to the limit (`dist` version only)
* Simplify some proofs
* Add some supporting lemmas
* Fix a typo in a lemma name in `ennreal`

* Add `move_cast` attrs

* More `*_cast` tags, use `norm_cast`

### [2019-11-26T14:35:37+00:00](https://github.com/leanprover-community/mathlib/commit/255bebc053e7bdb8ce6d8f54787c5e69e938ba4f)
feat(data/nat/multiplicity): multiplicity_choose and others ([#1704](https://github.com/leanprover-community/mathlib/pull/#1704))

### [2019-11-26T12:10:33+00:00](https://github.com/leanprover-community/mathlib/commit/3443a7d4bdc71eaafc8b2c0dcdc4d3c43251127b)
feat(analysis/complex/basic): restriction of scalars, real differentiability of complex functions ([#1716](https://github.com/leanprover-community/mathlib/pull/#1716))

* restrict scalar

* staging

* complete proof

* staging

* cleanup

* staging

* cleanup

* docstring

* docstring

* reviewer's comments

* Update src/analysis/complex/basic.lean

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

* Update src/analysis/calculus/fderiv.lean

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

* add ! in docstrings [ci skip]

* more doc formatting in fderiv

* fix comments

* add docstrings

### [2019-11-26T09:03:27+00:00](https://github.com/leanprover-community/mathlib/commit/33df7e88ddc7b9629348615ef06b2d2f8446b192)
feat(order/conditionally_complete_lattice): with_top (with_bot L) ins… ([#1725](https://github.com/leanprover-community/mathlib/pull/#1725))

* feat(order/conditionally_complete_lattice): with_top (with_bot L) instances

* dealing with most of Sebastien's comments

* initial defs. Now what happens?

* half way there

* compiles!

* tidy

* removing dead code

* docstring tinkering

* removing unused code

* is_lub_Sup' added

* refactor final proofs

* conforming to mathlib conventions

* def -> lemma

### [2019-11-25T19:40:41+00:00](https://github.com/leanprover-community/mathlib/commit/ef47de414bff815cf102c61e86a504e75258f07b)
chore(data/nat/basic): add some docs, drop unused arguments ([#1741](https://github.com/leanprover-community/mathlib/pull/#1741))

* add a docstring

* chore(data/nat/basic): add some docs, drop unused arguments

### [2019-11-25T17:00:45+00:00](https://github.com/leanprover-community/mathlib/commit/73735ad0a69dca9c163c45fbfe28a702940d80da)
feat(topology/metric_space/basic): define `cauchy_seq_of_le_tendsto_0` ([#1738](https://github.com/leanprover-community/mathlib/pull/#1738))

* Define `cauchy_seq_of_le_tendsto_0`

Sometimes it is convenient to avoid proving `0 ≤ b n`.

* Fix the comment, generalize to an inhabitted `sup`-semilattice.

### [2019-11-25T09:29:09+00:00](https://github.com/leanprover-community/mathlib/commit/242159f88a63b3e040b2665caa321fd0c69cc9ed)
feat(measure_theory/bochner_integration): bochner integral of simple functions ([#1676](https://github.com/leanprover-community/mathlib/pull/#1676))

* Bochner integral of simple functions

* Update bochner_integration.lean

* Change notation for simple functions in L1 space; Fill in blanks in `calc` proofs

* Better definitions of operations on integrable simple functions

* Update src/measure_theory/bochner_integration.lean

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Update src/measure_theory/bochner_integration.lean

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Update src/measure_theory/bochner_integration.lean

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Update src/measure_theory/bochner_integration.lean

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Update src/measure_theory/bochner_integration.lean

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Update src/measure_theory/bochner_integration.lean

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Several fixes - listed below

* K -> \bbk
* remove indentation after `calc`
* use local instances
* one tactic per line
* add `elim_cast` attributes
* remove definitions from nolints.txt
* use `linear_map.with_bound` to get continuity

* Update documentation and comments

* Fix things

* norm_triangle_sum -> norm_sum_le
* fix documentations and comments (The Bochner integral)

* Fix typos and grammatical errors

* Update src/measure_theory/ae_eq_fun.lean

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

### [2019-11-25T00:45:56+00:00](https://github.com/leanprover-community/mathlib/commit/6af35ecb67d9fe0dc97a4fe0e88cd1f528c55c5d)
feat(topology/algebra/infinite_sum): add `has_sum` versions of a few `tsum` lemmas ([#1737](https://github.com/leanprover-community/mathlib/pull/#1737))

Also add a few lemmas in `analysis/specific_limits`

### [2019-11-24T23:51:18+00:00](https://github.com/leanprover-community/mathlib/commit/bf509d782bb6d7a1e0e62f8b88b136e2d671efba)
feat(order/filter/basic): add more lemmas about `tendsto _ _ at_top` ([#1713](https://github.com/leanprover-community/mathlib/pull/#1713))

* feat(order/filter/basic): add more lemmas about `tendsto _ _ at_top`

* Use explicit arguments as suggested by @sgouezel

* Add lemmas for an `ordered_comm_group`

* Add a missing lemma

### [2019-11-24T23:02:27+00:00](https://github.com/leanprover-community/mathlib/commit/a03a0720f34c5fe6d46d8630e835a715269745c3)
chore(topology/metric_space/emetric_space): define `edist_le_zero` ([#1735](https://github.com/leanprover-community/mathlib/pull/#1735))

This makes a few proofs slightly more readable.

### [2019-11-24T20:38:04+00:00](https://github.com/leanprover-community/mathlib/commit/13fedc15ffdae15249e68183a124f72f1ccb44eb)
feat(algebra/group): define `mul/add_left/right_injective` ([#1730](https://github.com/leanprover-community/mathlib/pull/#1730))

Same as `mul_left_cancel` etc but uses `function.injective`.
This makes it easier to use functions from `function.injective` namespace.

### [2019-11-24T19:51:44+00:00](https://github.com/leanprover-community/mathlib/commit/7b1cdd4f3bd2572396b107bf19b8256d4e40c781)
feat(topology/metric_space/emetric_space): polygonal inequalities ([#1736](https://github.com/leanprover-community/mathlib/pull/#1736))

Migrate [#1572](https://github.com/leanprover-community/mathlib/pull/#1572) from `dist` to `edist`

### [2019-11-24T17:44:38+00:00](https://github.com/leanprover-community/mathlib/commit/ca53b5d5bd9a4690d379aa2fb3a7d510837060be)
feat(data/real/ennreal): 3 simple lemmas ([#1734](https://github.com/leanprover-community/mathlib/pull/#1734))

### [2019-11-24T10:11:36+00:00](https://github.com/leanprover-community/mathlib/commit/2d54a70a1b4ef8b0b5d6b5764957ca33d07f6eee)
feat(analysis/normed_space): prove more lemmas, rename some old lemmas ([#1733](https://github.com/leanprover-community/mathlib/pull/#1733))

Renamed lemmas:

* `norm_triangle` → `norm_add_le`
* `norm_triangle_sub` → `norm_sub_le`
* `norm_triangle_sum` → `norm_sum_le`
* `norm_reverse_triangle'` → `norm_sub_norm_le`
* `norm_reverse_triangle`: deleted; was a duplicate of `abs_norm_sub_norm_le`
* `nnorm_triangle` → `nnorm_add_le`

New lemmas:

* `dist_add_left`, `dist_add_right`, `dist_neg_neg`, dist_sub_left`,
  dist_sub_right`, `dist_smul`, `dist_add_add_le`, `dist_sub_sub_le`:
  operate with distances without rewriting them as norms.

* `norm_add_le_of_le`, `dist_add_add_le_of_le`,
  `dist_sub_sub_le_of_le`, `norm_sum_le_of_le` : chain a triangle-like
  inequality with an appropriate estimates on the right hand side.

Also simplify a few proofs and fix a typo in a comment.

### [2019-11-23T11:38:03+00:00](https://github.com/leanprover-community/mathlib/commit/f95c01e48c361cf5dd5a20f6ce0b7a760fd54b34)
feat(algebra/ordered_*): add three simple lemmas ([#1731](https://github.com/leanprover-community/mathlib/pull/#1731))

### [2019-11-23T00:15:59+00:00](https://github.com/leanprover-community/mathlib/commit/f86abc7781d85564a9fba9f3deafe73453d22e8d)
fix(*): lower instance priority ([#1724](https://github.com/leanprover-community/mathlib/pull/#1724))

* fix(*): lower instance priority

use lower instance priority for instances that always apply
also do this for automatically generated instances using the `extend` keyword
also add a comment to most places where we short-circuit type-class inference. This can lead to greatly increased search times (see issue [#1561](https://github.com/leanprover-community/mathlib/pull/#1561)), so we might want to delete some/all of them.

* put default_priority option inside section

Default priority also applies to all instances, not just automatically-generates ones
the scope of set_option is limited to a section

* two more low priorities

* fix some broken proofs

* fix proof

* more fixes

* more fixes

* increase max_depth a bit

* update notes

* fix linter issues

### [2019-11-22T21:37:11+00:00](https://github.com/leanprover-community/mathlib/commit/2b3eaa836cefddc81d392e1b9292451123f27b99)
feat(README) Point users to the tutorial project ([#1728](https://github.com/leanprover-community/mathlib/pull/#1728))

I think the tutorial project is a good place to start, and if other people don't think it is then I think they might want to consider adding more files to the tutorial project. I think mathlib is intimidating for beginners and this is a much better idea. However the link to the tutorial project is not even available on the main page -- you have to click through an installation procedure and find it at the bottom, and even then the first thing is suggests is that you make a new project, which I think is harder than getting the tutorial project up and running. This PR proposes that we point people directly to the tutorial project -- they will probably notice the existence of the tutorial project before they have even installed Lean/mathlib and will hence have it at the back of their mind once they've got things up and running.

### [2019-11-22T21:18:35+00:00](https://github.com/leanprover-community/mathlib/commit/013e91411fdc20f504e5f94555832e556411cf72)
fix(docs/install/project) compiling is quick ([#1727](https://github.com/leanprover-community/mathlib/pull/#1727))

I think the "it takes a long time" comment must either have been from before `update-mathlib` or from when we were pointing people to the perfectoid project.

### [2019-11-22T20:20:52+00:00](https://github.com/leanprover-community/mathlib/commit/62c1bc5b40c1f9d5935d1a7c4b5d185507c0fa30)
doc(topology/metric_space,measure_theory): move text in copyright docs to module docs ([#1726](https://github.com/leanprover-community/mathlib/pull/#1726))

### [2019-11-22T17:45:25+01:00](https://github.com/leanprover-community/mathlib/commit/5a1a469807b7ef366891c89794e88de69b978b68)
docs(README): revert 96ebf8cc

Revert "docs(README): Remove Patrick from the maintainer list."

This reverts commit 96ebf8cc7c446e977637a13740645a7f8e0c8992.

### [2019-11-21T22:11:03+00:00](https://github.com/leanprover-community/mathlib/commit/004618ad1ad06391872e11a77bf7440ef575e839)
feat(data/nat): two lemmas about choose ([#1717](https://github.com/leanprover-community/mathlib/pull/#1717))

* Two lemmas about choose

* swap choose_symm order

### [2019-11-21T19:22:23+00:00](https://github.com/leanprover-community/mathlib/commit/58fc8301e8591b77d62e9548a8a89a57a958153a)
fix(tactic/ext): handle case where goal is solved early ([#1721](https://github.com/leanprover-community/mathlib/pull/#1721))

* fix(tactic/ext): handle case where goal is solved early

* add test

### [2019-11-21T17:17:19+00:00](https://github.com/leanprover-community/mathlib/commit/a13027a5768e7442cfd50ce40ddbd8bd1b0df84e)
feat(data/finset): add cardinality of map ([#1722](https://github.com/leanprover-community/mathlib/pull/#1722))

* Add cardinality of map

* Update src/data/finset.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-11-21T11:57:54+00:00](https://github.com/leanprover-community/mathlib/commit/faf3289911fcf711b69e5f25483b9a2402e0a4b6)
add div_le_div_iff ([#1720](https://github.com/leanprover-community/mathlib/pull/#1720))

### [2019-11-21T07:04:43+00:00](https://github.com/leanprover-community/mathlib/commit/af9dcb98ec5c495cf27679e5dad477fc6326157c)
make  set_of_eq_eq_singleton a simp lemma ([#1719](https://github.com/leanprover-community/mathlib/pull/#1719))

### [2019-11-20T20:03:27+00:00](https://github.com/leanprover-community/mathlib/commit/9d031be091137f557c20c615f96d0413d67fabf4)
feat(group_theory/congruence): quotients of monoids by congruence relations ([#1710](https://github.com/leanprover-community/mathlib/pull/#1710))

* add congruence.lean

* add has_mul

* add definition of congruence relation

* minor changes

* Tidy up second half of congruence.lean

* tidying docstrings

* tidying

* constructive 3rd isom in setoid used in congruence

* remove import

* open namespaces earlier

* responding to PR comments

### [2019-11-20T17:12:35+00:00](https://github.com/leanprover-community/mathlib/commit/f34bb6b94adf4a48cbfc78e65ecfa4faaf5074b1)
refactor(topology/metric_space/lipschitz): review API of `lipschitz_with` ([#1700](https://github.com/leanprover-community/mathlib/pull/#1700))

* refactor(topology/metric_space/lipschitz): review API of `lipschitz_with`

* Take `K : ℝ≥0` instead of using a conjuction;
* Rename each `*_of_lipschitz` to `lipschitz_with.*`;
* Define convenience constructors (e.g., `of_le_add`);
* Move facts about contracting maps to a separate file&namespace;
* Adjust other files to API changes.

* Make the first argument of `lipschitz_with.weaken` implicit

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Fix compile

* Fix 'unused args' bug reported by `#lint`

### [2019-11-20T15:36:42+00:00](https://github.com/leanprover-community/mathlib/commit/5a6a67fc30ccea34d19dcbf9c5a24c8e31957bd5)
fix(data/padics): misstated lemma ([#1718](https://github.com/leanprover-community/mathlib/pull/#1718))

### [2019-11-20T01:38:56+00:00](https://github.com/leanprover-community/mathlib/commit/0744a3a96aae43c9f99e7382b55270c431de8a9f)
feat(analysis/normed_space/operator_norm): extension of a uniform continuous function ([#1649](https://github.com/leanprover-community/mathlib/pull/#1649))

* Extension of a uniform continuous function

* Use characteristic properties of an extended function, instead of the explicit construction

* Add documentation on similar results in the library

* Update src/topology/algebra/uniform_extension.lean

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Travis failed for no reason

* Update uniform_extension.lean

* eliminate `uniform_extension.lean`

* Update operator_norm.lean

* Update operator_norm.lean

* Remove `M`

* Fix docstring; extend_zero should be a simp lemma

### [2019-11-19T23:41:43+00:00](https://github.com/leanprover-community/mathlib/commit/d67e527adc99837b731799190fdc7cbeb596254f)
feat(algebra/group_power): prove Bernoulli's inequality for `a ≥ -2` ([#1709](https://github.com/leanprover-community/mathlib/pull/#1709))

* feat(algebra/group_power): prove Bernoulli's inequality for `a ≥ -2`

* Restate inequalities as suggested by @fpvandoorn

* Fix docs

### [2019-11-19T20:49:00+00:00](https://github.com/leanprover-community/mathlib/commit/d4fd7227aed2b7fa30351fbd2fa073804aeebc8d)
feat(algebra/group; data/nat) lemmas for sub sub assoc ([#1712](https://github.com/leanprover-community/mathlib/pull/#1712))

* Lemmas for sub sub assoc

* Removed a lemma

### [2019-11-19T18:41:34+00:00](https://github.com/leanprover-community/mathlib/commit/db6eab2e06cbcbee9fb03c7648c16630e578cb7d)
fix(tactic/ring): bugfix ring sub ([#1714](https://github.com/leanprover-community/mathlib/pull/#1714))

### [2019-11-19T18:03:43+00:00](https://github.com/leanprover-community/mathlib/commit/740168bf22c86e2d83b98e069b85ac7360dbba8c)
feat(.travis): add linting of new changes to CI ([#1634](https://github.com/leanprover-community/mathlib/pull/#1634))

* feat(.travis): add linting of new changes to CI

* explicitly list which linters to use

* upate nolints

* fix nolints.txt

* fix nolints

* remove instance_priority test

### [2019-11-19T16:06:05+01:00](https://github.com/leanprover-community/mathlib/commit/02659d634db53d4fc58a76d219402fbbaaa2b51f)
chore(scripts/nolint): regenerate nolints

### [2019-11-19T13:09:36+00:00](https://github.com/leanprover-community/mathlib/commit/8d7f093bba6987d1f770fe786c5a02990e4c05f8)
fix(tactic/omega): use eval_expr' ([#1711](https://github.com/leanprover-community/mathlib/pull/#1711))

* fix(tactic/omega): use eval_expr'

* add test

### [2019-11-19T11:07:21+00:00](https://github.com/leanprover-community/mathlib/commit/e3be70db3e7d49f277256b05f7c787fab235c7bc)
lemmas about powers of elements ([#1688](https://github.com/leanprover-community/mathlib/pull/#1688))

* feat(algebra/archimedean): add alternative version of exists_int_pow_near

- also add docstrings

* feat(analysis/normed_space/basic): additional inequality lemmas

- that there exists elements with large and small norms in a nondiscrete normed field.

* doc(algebra/archimedean): edit docstrings

* Apply suggestions from code review

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

### [2019-11-19T04:28:27+00:00](https://github.com/leanprover-community/mathlib/commit/b0520a31df3caf4c706ce1202eac24502f25d33c)
feat(algebra/order): define `forall_lt_iff_le` and `forall_lt_iff_le'` ([#1707](https://github.com/leanprover-community/mathlib/pull/#1707))

### [2019-11-19T02:27:10+00:00](https://github.com/leanprover-community/mathlib/commit/5d5da7e6e889cc709a84b5021a03ec23cdb6cb8c)
feat(data/set/intervals): more lemmas ([#1665](https://github.com/leanprover-community/mathlib/pull/#1665))

* feat(data/set/intervals): more lemmas

* Use `simp` in more proofs, drop two `@[simp]` attrs

* Drop more `@[simp]` attrs

It's not clear which side is simpler.

### [2019-11-18T23:52:03+00:00](https://github.com/leanprover-community/mathlib/commit/895f1ae05228950b5ad99ee9ebb8cbd26f677e6e)
feat(data/option): add `some_ne_none`, `bex_ne_none`, `ball_ne_none` ([#1708](https://github.com/leanprover-community/mathlib/pull/#1708))

### [2019-11-18T20:32:48+00:00](https://github.com/leanprover-community/mathlib/commit/6b408eb102654ad9ae6382a04124a67358f323c8)
feat(data/real/nnreal): define `nnreal.gi : galois_insertion of_real coe` ([#1699](https://github.com/leanprover-community/mathlib/pull/#1699))

### [2019-11-18T18:18:25+00:00](https://github.com/leanprover-community/mathlib/commit/af43a2bc760fa11e8a42819785224e0ead323a3d)
feat(data/nat/enat): add_right_cancel and other ([#1705](https://github.com/leanprover-community/mathlib/pull/#1705))

### [2019-11-18T16:16:44+00:00](https://github.com/leanprover-community/mathlib/commit/0d94020c5c58cfc95f7e9f1827d052cb9da5eaac)
feat(algebra/order_functions): define `min/max_mul_of_nonneg` ([#1698](https://github.com/leanprover-community/mathlib/pull/#1698))

Also define `monotone_mul_right_of_nonneg` and rename
`monotone_mul_of_nonneg` to `monotone_mul_left_of_nonneg`.

### [2019-11-18T14:10:09+00:00](https://github.com/leanprover-community/mathlib/commit/3f9c4d886493afe2dbaada17d25e486b1872e047)
chore(data/set): use `Sort*` in more lemmas ([#1706](https://github.com/leanprover-community/mathlib/pull/#1706))

Also replace `nonempty_of_nonempty_range` with
`range_ne_empty_iff_nonempty` and `range_ne_empty`.
The old lemma is equivalent to `range_ne_empty_iff_nonempty.mp`.

### [2019-11-18T12:21:07+00:00](https://github.com/leanprover-community/mathlib/commit/428aec90e1c395a95d1f300a49cec0f95e5fb6cd)
feat(group_theory/congruence): create file about congruence relations ([#1690](https://github.com/leanprover-community/mathlib/pull/#1690))

* add congruence.lean

* add has_mul

* add definition of congruence relation

* minor changes

* responding to review comments

* fix docstring mistake in setoid.lean

### [2019-11-18T10:15:17+00:00](https://github.com/leanprover-community/mathlib/commit/0a794facb39f70c161d78c45af1897d4858b4ec0)
feat(data/finset): new union, set difference, singleton lemmas ([#1702](https://github.com/leanprover-community/mathlib/pull/#1702))

* Singleton iff unique element lemma

* Set difference lemmas

* Changes from review

### [2019-11-18T08:08:24+00:00](https://github.com/leanprover-community/mathlib/commit/fafdcfdc5d5b192cd62093fb30a50a2e223c6f72)
chore(data/set/lattice): get most proofs from `pi` instance. ([#1685](https://github.com/leanprover-community/mathlib/pull/#1685))

This way we only provide proofs that don't come from `pi`

### [2019-11-18T04:03:50+00:00](https://github.com/leanprover-community/mathlib/commit/d19f7bc66324322d60f014417d215514e6f1840e)
feat(analysis/normed_space/finite_dimension): finite-dimensional spaces on complete fields ([#1687](https://github.com/leanprover-community/mathlib/pull/#1687))

* feat(analysis/normed_space/finite_dimension): equivalence of norms, continuity of linear maps

* improve doc

* cleanup

* cleanup

* Update src/data/equiv/basic.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* exact_mod_cast, remove classical

* unfreezeI

* remove typeclass assumption

* Update src/analysis/normed_space/finite_dimension.lean

Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>

* Update src/linear_algebra/basic.lean

Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>

* Update src/linear_algebra/finite_dimensional.lean

Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>

* cleanup

### [2019-11-18T02:08:50+00:00](https://github.com/leanprover-community/mathlib/commit/7c5f282dcfe1e0f20050f4aae3b6bdf77a652a13)
chore(algebra/order_functions): rename `min/max_distrib_of_monotone` ([#1697](https://github.com/leanprover-community/mathlib/pull/#1697))

New names `monotone.map_min/max` better align with `monoid_hom.map_mul` etc.

### [2019-11-18T00:18:22+00:00](https://github.com/leanprover-community/mathlib/commit/9607bbf808b80ccdb7ce1254a5b4b28950fc180e)
feat(algebra/big_operators): sum_Ico_succ_top and others ([#1692](https://github.com/leanprover-community/mathlib/pull/#1692))

* feat(Ico): sum_Ico_succ_top and others

* get rid of succ_bot and rename eq_cons

### [2019-11-17T21:17:19+00:00](https://github.com/leanprover-community/mathlib/commit/f5385fe013c958e9e3eb05b689c9a864544201a2)
chore(order_functions): use weakly implicit brackets in strict mono ([#1701](https://github.com/leanprover-community/mathlib/pull/#1701))

* chore(order_functions): use weakly implicit brackets in strict mono

* fix build

### [2019-11-17T19:31:14+00:00](https://github.com/leanprover-community/mathlib/commit/474004f1a83a3d8587c69fad334aff2ee797d75c)
fix(topology/dense_embeddings): tweaks ([#1684](https://github.com/leanprover-community/mathlib/pull/#1684))

* fix(topology/dense_embeddings): tweaks

This fixes some small issues with last summer dense embedding refactors.
This is preparation for helping with Bochner integration. Some of those
fixes are backported from the perfectoid project.

* chore(dense_embedding): remove is_closed_property'

* Update src/topology/uniform_space/completion.lean

* Update src/topology/dense_embedding.lean

### [2019-11-17T17:46:28+00:00](https://github.com/leanprover-community/mathlib/commit/1805f16a2d1fe9d5ac735a6457208f111ea4bfd7)
refactor(order/bounds): make the first argument of `x ∈ upper_bounds s` implicit ([#1691](https://github.com/leanprover-community/mathlib/pull/#1691))

* refactor(order/bounds): make the first argument of `x ∈ upper_bounds s` implicit

* Use `∈ *_bounds` in the definition of `conditionally_complete_lattice`.

### [2019-11-17T15:38:07+00:00](https://github.com/leanprover-community/mathlib/commit/10343579a1eb59284d9646d1f3eaf026fbd9fd4b)
feat(data/int/parity): not_even_iff ([#1694](https://github.com/leanprover-community/mathlib/pull/#1694))

### [2019-11-17T05:49:52+00:00](https://github.com/leanprover-community/mathlib/commit/e863c0884e1af6cba0ea5013d2e394b58f5284af)
feat(algebra/pointwise): set.add_comm_monoid ([#1696](https://github.com/leanprover-community/mathlib/pull/#1696))

* feat(algebra/pointwise): set.add_comm_monoid

* defs not instances

* fixing instance names

### [2019-11-17T01:34:34+00:00](https://github.com/leanprover-community/mathlib/commit/6b1ab646f66c22a8c40365752a0c29fd3290e57f)
Add lemma for injective pow ([#1683](https://github.com/leanprover-community/mathlib/pull/#1683))

* Add lemma for injective pow

* Rename lemma and remove spaces

* Use strict-mono for monotonic pow

* Rename iff statements

* Add left injective pow as well

### [2019-11-15T16:11:27+00:00](https://github.com/leanprover-community/mathlib/commit/6ebb7e7884c9b11c137f5bb288cd80a46bc6dfac)
feat(data/nat/modeq): add_div and others ([#1689](https://github.com/leanprover-community/mathlib/pull/#1689))

* feat(data/nat/modeq): add_div and others

* remove unnecessary positivity assumptions.

* fix build

* brackets

### [2019-11-14T21:06:24+00:00](https://github.com/leanprover-community/mathlib/commit/40de4fcb8c6936a074c984c1ec25a89483f72428)
doc(order/bounds,order/conditionaly_complete_lattice): add some docs ([#1686](https://github.com/leanprover-community/mathlib/pull/#1686))

* doc(order/bounds,order/conditionaly_complete_lattice): add some docs

* Fixes by @jcommelin

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Fix docs: `is_least` are not unique unless we have a partial order.

### [2019-11-13T22:27:06+00:00](https://github.com/leanprover-community/mathlib/commit/6fbf9f77400f3c1dc8f2dc3699d52ca9cdaaec5f)
doc(*): proper markdown urls [ci skip] ([#1680](https://github.com/leanprover-community/mathlib/pull/#1680))

### [2019-11-13T20:20:04+00:00](https://github.com/leanprover-community/mathlib/commit/10ced7665dc353a3810c3eaf1e286b0424dff1c1)
doc(*): move detailed headers into real module docs ([#1681](https://github.com/leanprover-community/mathlib/pull/#1681))

* doc(*): move detailed headers into real module docs

* update zmod

### [2019-11-13T17:53:09+00:00](https://github.com/leanprover-community/mathlib/commit/47296243d7f18a0da3084ca16ccee387437e2834)
doc(data/rel): add docs to some definitions ([#1678](https://github.com/leanprover-community/mathlib/pull/#1678))

* doc(data/rel): add docs to some definitions

* Update src/data/rel.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/data/rel.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-11-13T14:36:39+00:00](https://github.com/leanprover-community/mathlib/commit/6f5ad3cb5f1c54176979a125bff417268974eadf)
add dvd_gcd_iff for nat ([#1682](https://github.com/leanprover-community/mathlib/pull/#1682))

### [2019-11-13T12:44:49+00:00](https://github.com/leanprover-community/mathlib/commit/6625f663ca2368fd2342c32cc01c7c01b5dbcf27)
feat(analysis/calculus/deriv): one-dimensional derivatives ([#1670](https://github.com/leanprover-community/mathlib/pull/#1670))

* feat(analysis/calculus/deriv): one-dimensional derivatives

* Typos.

* Define deriv f x as fderiv 𝕜 f x 1

* Proof style.

* Fix failing proofs.

### [2019-11-13T10:53:30+00:00](https://github.com/leanprover-community/mathlib/commit/3bb2b5c5bc1be91d775a0820cff6ca22da2a8461)
feat(algebra/big_operators): dvd_sum ([#1679](https://github.com/leanprover-community/mathlib/pull/#1679))

* feat(data/multiset): dvd_sum

* feat(algebra/big_operators): dvd_sum

* fix build

* fix build

* fix build

### [2019-11-12T23:38:13+00:00](https://github.com/leanprover-community/mathlib/commit/dfd25ff4fe93bbe6e376dd2d27f7ef7ee7c8b3f9)
chore(meta/expr): delete local_binder_info; rename to_implicit ([#1668](https://github.com/leanprover-community/mathlib/pull/#1668))

* chore(meta/expr): delete local_binder_info; rename to_implicit

local_binder_info duplicated local_binding_info.
to_implicit has been renamed to_implicit_local_const, to distinguish it
from to_implicit_binder

* file missing from commit

### [2019-11-12T18:51:50+00:00](https://github.com/leanprover-community/mathlib/commit/1749a8dda233158ae2fb7b9316f74659081e00e1)
feat(group_theory/submonoid): add bundled submonoids and various lemmas ([#1623](https://github.com/leanprover-community/mathlib/pull/#1623))

* WIP -- removing  and everything is broken

* test

* test

* tidy

* fixed localization

* starting on coset

* WIP

* submonoid.lean now compiles but no to_additive stuff

* submonoid.lean compiles

* putting is_submonoid back

* docstrings

* terrible docstrings up to line 370

* finished docstrings

* more to_additive stuff

* WIP -- removing  and everything is broken

* test

* test

* tidy

* fixed localization

* starting on coset

* WIP

* submonoid.lean now compiles but no to_additive stuff

* submonoid.lean compiles

* putting is_submonoid back

* docstrings

* terrible docstrings up to line 370

* finished docstrings

* more to_additive stuff

* WIP quotient monoids

* quotient monoids WIP

* quotient_monoid w/o ideals.lean all compiles

* removing lemma

* adjunction

* some tidying

* remove pointless equiv

* completion compiles (very slowly)

* add lemma

* tidying

* more tidying

* mul -> smul oops

* might now compile

* tidied! I think

* fix

* breaking/adding stuff & switching branch

* add Inf relation

* removing sorrys

* nearly updated quotient_monoid

* updated quotient_monoid

* resurrecting computability

* tidied congruence.lean, added some docstrings

* extending setoids instead, WIP

* starting Galois insertion

* a few more bits of to_additive and docs

* no battery

* up to line 800

* congruence'll compile when data.setoid exists now

* more updates modulo existence of data.setoid

* rearranging stuff

* docstrings

* starting additive docstrings

* using newer additive docstring format in submonoid

* docstrings, tidying

* fixes and to_additive stuff, all WIP

* temporary congruence fixes

* slightly better approach to kernels, general chaos

* aahh

* more mess

* deleting doomed inductive congruence closure

* many fixes and better char pred isoms

* docstrings for group_theory.submonoid

* removing everything but bundled submonoids/lemmas

* removing things etc

* removing random empty folder

* tidy

* adding lemma back

* tidying

* responding to PR comments

* change 2 defs to lemmas

* @[simp] group_power.lean lemmas

* responding to commute.lean comments

* Remove unnecessary add_semiconj_by.eq

* Change prod.submonoid to submonoid.prod

* replacing a / at the end of docstring

Sorry - don't make commits on your phone when your laptop's playing up :/

* removing some not very useful to_additives

* fix pi_instances namespaces

* remove unnecessary prefix

* change extensionality to ext

not sure this is necessary because surely merging will change this automatically, but Travis told me to, and I really want it to compile, and I am not at my laptop

### [2019-11-12T16:51:10+00:00](https://github.com/leanprover-community/mathlib/commit/7b07932de99f1fbe16cf85f4ffdc6188e243dece)
feat(analysis/normed_space/operator_norm): continuity of linear forms; swap directions of `nnreal.coe_*` ([#1655](https://github.com/leanprover-community/mathlib/pull/#1655))

* feat(analysis/normed_space/operator_norm): continuity of linear forms

* use lift, change nnreal.coe_le direction

### [2019-11-12T15:22:02+00:00](https://github.com/leanprover-community/mathlib/commit/14435eb2ba93e3749509d490a55f75b7e77f5ba4)
feat(algebra/lie_algebra): Define lie algebras ([#1644](https://github.com/leanprover-community/mathlib/pull/#1644))

* feat(algebra/module): define abbreviation module.End

The algebra of endomorphisms of a module over a commutative ring.

* feat(ring_theory/algebra): define algebra structure on square matrices over a commutative ring

* feat(algebra/lie_algebras.lean): define Lie algebras

* feat(algebra/lie_algebras.lean): simp lemmas for Lie rings

Specifically:
  * zero_left
  * zero_right
  * neg_left
  * leg_right

* feat(algebra/lie_algebras): more simp lemmas for Lie rings

Specifically:
  * gsmul_left
  * gsmul_right

* style(algebra/lie_algebras): more systematic naming

* Update src/algebra/lie_algebras.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/algebra/lie_algebras.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/algebra/lie_algebras.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/algebra/lie_algebras.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/algebra/lie_algebras.lean

Catch up with renaming in recent Co-authored commits

* Rename src/algebra/lie_algebras.lean --> src/algebra/lie_algebra.lean

* Place lie_ring simp lemmas into global namespace

* Place lie_smul simp lemma into global namespace

* Drop now-redundant namespace qualifiers

* Update src/algebra/lie_algebra.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

* Update src/algebra/lie_algebra.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

* Catch up after recent Co-authored commits making carrier types implicit

* Add missing docstrings

* feat(algebra/lie_algebra): replace `instance` definitions with vanilla `def`s

* style(algebra/lie_algebra): Apply suggestions from code review

Co-Authored-By: Patrick Massot

* Update src/algebra/lie_algebra.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Minor tidy ups

### [2019-11-12T13:20:50+00:00](https://github.com/leanprover-community/mathlib/commit/08880c944e452018d6902ae7414a631f7d2a1aeb)
feat(data/equiv,category_theory): prove equivalences are the same as isos ([#1587](https://github.com/leanprover-community/mathlib/pull/#1587))

* refactor(category_theory,algebra/category): make algebraic categories not [reducible]

Adapted from part of [#1438](https://github.com/leanprover-community/mathlib/pull/#1438).

* Update src/algebra/category/CommRing/basic.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

* adding missing forget2 instances

* Converting Reid's comment to a [Note]

* adding examples testing coercions

* feat(data/equiv/algebra): equivalence of algebraic equivalences and categorical isomorphisms

* more @[simps]

* more @[simps]

### [2019-11-12T11:23:31+00:00](https://github.com/leanprover-community/mathlib/commit/2cbeed953366cb9eafc5a9c8955f5e777747a95b)
style(*): use notation `𝓝` for `nhds` ([#1582](https://github.com/leanprover-community/mathlib/pull/#1582))

* chore(*): notation for nhds

* Convert new uses of nhds

### [2019-11-12T07:05:03+00:00](https://github.com/leanprover-community/mathlib/commit/3cae70d675ae416a4c63d754d0bad2ef7c02d559)
feat(extensionality): generate ext_iff for structures ([#1656](https://github.com/leanprover-community/mathlib/pull/#1656))

* feat(extensionality): generate ext_iff for structures

* fix

* core.lean [skip ci]

* Update ext.lean

* Update ext.lean

* Update tactics.md

* Update src/tactic/ext.lean

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

### [2019-11-12T05:02:30+00:00](https://github.com/leanprover-community/mathlib/commit/f58f34043710073ec29163f8efd0a399427b0cab)
feat(order/lattice): add `monotone.le_map_sup` and `monotone.map_inf_le` ([#1673](https://github.com/leanprover-community/mathlib/pull/#1673))

Use it to simplify some proofs in `data/rel`.

### [2019-11-12T03:02:15+00:00](https://github.com/leanprover-community/mathlib/commit/c28497fa056ae52b93aa9aca2fd20155d57fa016)
chore(*): use `iff.rfl` instead of `iff.refl _` ([#1675](https://github.com/leanprover-community/mathlib/pull/#1675))

### [2019-11-11T21:44:54+00:00](https://github.com/leanprover-community/mathlib/commit/d077887141000fefa5a264e30fa57520e9f03522)
cleanup(data/equiv/basic): drop `quot_equiv_of_quot'`, rename `quot_equiv_of_quot` ([#1672](https://github.com/leanprover-community/mathlib/pull/#1672))

* cleanup(data/equiv/basic): drop `quot_equiv_of_quot'`, rename `quot_equiv_of_quot`

* `quot_equiv_of_quot` was the same as `quot.congr`
* rename `quot_equiv_of_quot` to `quot.congr_left` to match
  `quot.congr` and `quot.congr_right`.

* Add docs

### [2019-11-11T15:19:29+00:00](https://github.com/leanprover-community/mathlib/commit/a5b3af3dd33e1594b54f22f4a75e05c1769a22f3)
fix(tactic/core): correct `of_int` doc string ([#1671](https://github.com/leanprover-community/mathlib/pull/#1671))

### [2019-11-11T02:02:13+00:00](https://github.com/leanprover-community/mathlib/commit/6ecdefc01d3cd938875603a6e4d025244c778623)
chore(analysis/calculus/deriv): rename to fderiv ([#1661](https://github.com/leanprover-community/mathlib/pull/#1661))

### [2019-11-10T23:56:06+00:00](https://github.com/leanprover-community/mathlib/commit/886b15b5ea473ae51ed90de31b05f23de00be10d)
doc(measure_theory/l1_space): add doc and some lemmas ([#1657](https://github.com/leanprover-community/mathlib/pull/#1657))

* Add doc and lemmas

* Remove unnecessary assumption

* Fix integrable_neg

* Remove extra assumptions

* Wrong variable used

### [2019-11-10T21:49:19+00:00](https://github.com/leanprover-community/mathlib/commit/ce48727e0cf3ea5c515ddeb7be5bfb6a4deba551)
fix(order/conditionally_complete_lattice): fix 2 misleading names ([#1666](https://github.com/leanprover-community/mathlib/pull/#1666))

* `cSup_upper_bounds_eq_cInf` → `cSup_lower_bounds_eq_cInf`;
* `cInf_lower_bounds_eq_cSup` → `cInf_upper_bounds_eq_cSup`.

### [2019-11-10T19:42:35+00:00](https://github.com/leanprover-community/mathlib/commit/f738ec7e3a4082ac677178b03e322126ca96cc82)
refactor(data/zmod/quadratic_reciprocity): simplify proof of quadratic reciprocity and prove when 2 is a square ([#1609](https://github.com/leanprover-community/mathlib/pull/#1609))

* feat(number_theory/sum_four_squares): every natural number is the sum of four square numbers

* gauss_lemma

* Johan's suggestions

* some better parity proofs

* refactor(data/finset): restate disjoint_filter

* fix build

* fix silly lemmas in finite_fields

* generalize a lemma

* work on add_sum_mul_div_eq_mul

* fix build

* Update src/number_theory/sum_four_squares.lean

* feat(data/multiset): map_eq_map_of_bij_of_nodup

* finish proof of quad_rec

* minor fix

* Add docs

* add docs in correct style

* Use Ico 1 p instead of (range p).erase 0

### [2019-11-10T17:58:18+00:00](https://github.com/leanprover-community/mathlib/commit/4e681292786b5c37624f6d66cfda00b451529e0f)
feat(data/finset): Ico.subset ([#1669](https://github.com/leanprover-community/mathlib/pull/#1669))

Does not have the `m1 < n1` assumption required for `subset_iff`

### [2019-11-10T15:51:47+00:00](https://github.com/leanprover-community/mathlib/commit/2cd59b41099e6425ac98ee9ea8bbac79cd8f8b63)
feat(coinduction): add identifier list to `coinduction` tactic ([#1653](https://github.com/leanprover-community/mathlib/pull/#1653))

* feat(coinduction): add identifier list to `coinduction` tactic

* Update coinductive_predicates.lean

* two doc strings [skip ci]

* Update coinductive_predicates.lean

* fix merge

* move definitions around

* move more stuff

* fix build

* move and document functions

### [2019-11-10T13:45:26+00:00](https://github.com/leanprover-community/mathlib/commit/209e039713b42ec9504ed634e17536bd1996ae1c)
cleanup(tactic/core): removing unused tactics ([#1641](https://github.com/leanprover-community/mathlib/pull/#1641))

* doc(tactic/core): begin to add docstrings

* a few more doc strings

* more additions

* more doc

* deal with an undocumented definition by removing it

* minor

* add doc string

* remove some unused core tactics

* Revert "remove some unused core tactics"

This reverts commit 52de333c0c3fd4294930b270eeac503425f0070f.

* document get_classes

* Revert "deal with an undocumented definition by removing it"

This reverts commit 07b56e7456911466a15f1c340d9964e08aab195e.

* more doc strings

* dead code

* revert changing `subobject_names` to private

* remaining doc strings

* cleanup(tactic/core): removing unused tactics

* remove file_simp_attribute_decl and simp_lemmas_from_file

* delete drop_binders

* fix merge, delete check_defn

### [2019-11-10T11:28:40+00:00](https://github.com/leanprover-community/mathlib/commit/4ecc17b5008bd1811d95ed24347f0db183468832)
fix(scripts/mk_all): don't add `lint_mathlib` to `all.lean` [ci skip] ([#1667](https://github.com/leanprover-community/mathlib/pull/#1667))

### [2019-11-09T22:41:00+00:00](https://github.com/leanprover-community/mathlib/commit/c497f961cadc7c1dd65489a4bade68cdc5508656)
feat(tactic/norm_cast): add push_cast simp attribute ([#1647](https://github.com/leanprover-community/mathlib/pull/#1647))

* feat(tactic/norm_cast): add push_cast simp attribute

* test and docs

### [2019-11-09T19:14:09+00:00](https://github.com/leanprover-community/mathlib/commit/1236ced41bb5c9b39dfb3866ba20a05229c16449)
feat(data/nat/basic): succ_div ([#1664](https://github.com/leanprover-community/mathlib/pull/#1664))

* feat(data/nat/basic): succ_div

Rather long proof, but it was the best I could do.

* Update basic.lean

* add the two lemmas for each case

* get rid of positivity assumption

### [2019-11-09T14:11:28+00:00](https://github.com/leanprover-community/mathlib/commit/1c24f92b1e633a9e21b46fb77fba1386b0e51603)
feat(data/list/basic): nth_le_append_right ([#1662](https://github.com/leanprover-community/mathlib/pull/#1662))

### [2019-11-09T11:29:30+00:00](https://github.com/leanprover-community/mathlib/commit/b0c36dfd54ce4ba5bc0d806f193fe095d8b3eef9)
feat(measure_theory/integration) lemmas for calculating integral of simple functions ([#1659](https://github.com/leanprover-community/mathlib/pull/#1659))

* lemmas for calculating integration on simple functions

* Updates

* `finsupp` changed to `fin_vol_supp`
* less conditions for `to_real_mul_to_real`
* `sum_lt_top` with more abstraction

* Fix extra arguments

* One tactic per line

### [2019-11-08T14:09:26+01:00](https://github.com/leanprover-community/mathlib/commit/ca216162e074846f63031bc89eb168703ec00ed7)
chore(scripts): add linter and update nolints

### [2019-11-08T13:57:15+01:00](https://github.com/leanprover-community/mathlib/commit/8afcc5ae63c36f4fdd73cd1a63fcf8adef0f50cf)
feat(scripts): add nolints.txt

### [2019-11-08T11:03:46+00:00](https://github.com/leanprover-community/mathlib/commit/3223ba7f419f5728974da7b6e7f8785f5f089b44)
doc(linear_algebra): rename lin_equiv to linear_equiv ([#1660](https://github.com/leanprover-community/mathlib/pull/#1660))

### [2019-11-07T23:25:38+00:00](https://github.com/leanprover-community/mathlib/commit/362acb56d1ce4a583c09c81e847fb0650ca0780a)
feat(tactic/lint, script/mk_nolint): generate list of failing declarations to be ignored ([#1636](https://github.com/leanprover-community/mathlib/pull/#1636))

* feat(tactic/lint): return names of failing declarations

* feat(scripts/mk_nolint): produce sorted list of declarations failing lint tests

* fix copyright

* fix test

* Update scripts/mk_nolint.lean

### [2019-11-07T03:43:41+00:00](https://github.com/leanprover-community/mathlib/commit/c718a22925872db4cb5f64c36ed6e6a07bdf647c)
feat(extensionality): rename to `ext`; generate `ext` rules for structures ([#1645](https://github.com/leanprover-community/mathlib/pull/#1645))

* Update core.lean

* Update tactics.lean

* integrate generation of extensionality lemma of structures into `ext`

* Update src/tactic/ext.lean [skip ci]

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

* Update src/tactic/ext.lean [skip ci]

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

* Update src/tactic/ext.lean

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

* Update ext.lean [skip ci]

* Update tactics.md [skip ci]

* fix build

* fix build

### [2019-11-06T22:22:23+00:00](https://github.com/leanprover-community/mathlib/commit/17a7f69effbf219f0fdc6fb48b076bec184e19f9)
doc(measure_theory/ae_eq_fun): add documentations and some lemmas ([#1650](https://github.com/leanprover-community/mathlib/pull/#1650))

* Add documentations. `to_fun`.

* More precise comments

### [2019-11-06T07:01:00+00:00](https://github.com/leanprover-community/mathlib/commit/3c8bbdc6aa6ae0e5094e125c9f91188dc7ecab4f)
chore(topology/subset_properties): simplify a proof ([#1652](https://github.com/leanprover-community/mathlib/pull/#1652))

### [2019-11-05T23:56:57+00:00](https://github.com/leanprover-community/mathlib/commit/62815e3dda1ef1ffbac8e0f0adfaf20eb1d15363)
doc(tactic/core): docstrings on all definitions ([#1632](https://github.com/leanprover-community/mathlib/pull/#1632))

* doc(tactic/core): begin to add docstrings

* a few more doc strings

* more additions

* more doc

* deal with an undocumented definition by removing it

* minor

* add doc string

* remove some unused core tactics

* Revert "remove some unused core tactics"

This reverts commit 52de333c0c3fd4294930b270eeac503425f0070f.

* document get_classes

* Revert "deal with an undocumented definition by removing it"

This reverts commit 07b56e7456911466a15f1c340d9964e08aab195e.

* more doc strings

* dead code

* revert changing `subobject_names` to private

* remaining doc strings

* Apply suggestions from code review

Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>

* remove todo

### [2019-11-05T21:26:42+00:00](https://github.com/leanprover-community/mathlib/commit/d9578a63ac885e23ee41adaf02f92fd06d7ea555)
docs(tactic/lint) add code fence around #print statement to avoid its args looking like html tags. ([#1651](https://github.com/leanprover-community/mathlib/pull/#1651))

### [2019-11-05T15:37:42+00:00](https://github.com/leanprover-community/mathlib/commit/986e58caa8a7cfdf79b58d517148734c0b4e9ae7)
refactor(sum_two_square): extract lemmas about primes in Z[i] ([#1643](https://github.com/leanprover-community/mathlib/pull/#1643))

* refactor(sum_two_square): extract lemmas about primes in Z[i]

* forgot to save

* docztring

* module docstrings

### [2019-11-04T22:23:15+00:00](https://github.com/leanprover-community/mathlib/commit/f3f1fd8cf117e7907f25cd5a6ffa93b58807b141)
feat(floor): one more lemma ([#1646](https://github.com/leanprover-community/mathlib/pull/#1646))

* feat(floor): one more lemma

and #lint fix

* Update src/algebra/floor.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-11-04T20:13:48+00:00](https://github.com/leanprover-community/mathlib/commit/2dcc6c25a33c48025ba38c5e54c5971f339d54c6)
fix(tactic/tfae,scc): change the strongly connected component algorithm ([#1600](https://github.com/leanprover-community/mathlib/pull/#1600))

* fix(tactic/tfae,scc): change the strongly connected component algorithm

* add example

* fix scc algorithm and add documentation

* documentation [skip ci]

* Update scc.lean [skip ci]

* Update src/tactic/scc.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

* Update scc.lean

* Update tactics.lean

* Update src/tactic/scc.lean

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

* rename mk_closure, add line breaks, grammar tweaks

* Update scc.lean

* add to `to_tactic_format` output and docstring, more minor fixes

### [2019-11-04T15:02:31+00:00](https://github.com/leanprover-community/mathlib/commit/ee5b38dfc0cbf43215c2446351b36dd67ee83c2c)
feat(simps): allow the user to specify the projections ([#1630](https://github.com/leanprover-community/mathlib/pull/#1630))

* feat(simps): allow the user to specify the projections

Also add option to shorten generated lemma names
Add the attribute to more places in the category_theory library
The projection lemmas of inl_ and inr_ are now called inl__obj and similar

* use simps partially in limits/cones and whiskering

* revert whiskering

* rename last_name to short_name

* Update src/category_theory/products/basic.lean

* Update src/category_theory/limits/cones.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

* Update src/category_theory/products/associator.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

* Update src/data/string/defs.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

* clarify is_eta_expansion docstrings

### [2019-11-03T15:40:43+00:00](https://github.com/leanprover-community/mathlib/commit/a6ace342cf5bc7d40b8b3af829b3c74dc9797572)
feat(analysis/normed_space): Riesz's lemma ([#1642](https://github.com/leanprover-community/mathlib/pull/#1642))

* fix(topology/metric_space/hausdorff_distance): fix typo

* feat(analysis/normed_space): Riesz's Lemma

* fix(analysis/normed_space): fix silly mistake in statement of riesz lemma

* style(analysis/normed_space/riesz_lemma): variable names & indent

* doc(analysis/normed_space/riesz_lemma): add attribution

* doc(analysis/normed_space/riesz_lemma): fix module docstring style

* style(analysis/normed_space/riesz_lemma): more style & documentation

- recall statement in module header comment
- typecast instead of unfold

### [2019-11-01T11:28:15+00:00](https://github.com/leanprover-community/mathlib/commit/9af7e5b5fdf5d720bb0f516f8be8eb3714f5d213)
refactor(linear_algebra/basic): use smul_right ([#1640](https://github.com/leanprover-community/mathlib/pull/#1640))

* refactor(linear_algebra/basic): use smul_right

* Update src/linear_algebra/basic.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

* Update src/linear_algebra/basic.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

### [2019-11-01T03:25:06+00:00](https://github.com/leanprover-community/mathlib/commit/1710fd8b11528a5d54827c313c2e5a75e5cde7a0)
feat(lint): add priority test for instances that always apply ([#1625](https://github.com/leanprover-community/mathlib/pull/#1625))

* feat(lint): add priority test for instances that always apply

also move a defn from coinductive_predicates to expr
also slightly refactor incorrect_def_lemma

* update doc

* add priorities to linters

Now they are run in the order specified by the doc

* always run tests in the extra set

even when they are slow and  is false

* move some more declarations from coinductive_predicates to expr

remove coinductive_predicates as import from some (but not all) files

* reviewer comments

* remove unsafe prefixes

### [2019-11-01T01:22:43+00:00](https://github.com/leanprover-community/mathlib/commit/5f17abcc0a0d83d7f913a37caa6d84ce48548afa)
fix(tactic/elide): was untested and buggy. Fixed a few issues ([#1638](https://github.com/leanprover-community/mathlib/pull/#1638))

* fix(tactic/elide): was untested and buggy. Fixed a few issues

* Update tactics.lean

* add copyright header

* Update src/tactic/elide.lean

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

### [2019-10-31T23:37:26+00:00](https://github.com/leanprover-community/mathlib/commit/df91623267a907171b8107b59593c542efad8084)
chore(category_theory/whiskering): clean up ([#1613](https://github.com/leanprover-community/mathlib/pull/#1613))

* chore(category_theory/whiskering): clean up

* ugh, the stalks proofs are so fragile

* fixes

* minor

* fix

* fix

### [2019-10-31T21:03:05+00:00](https://github.com/leanprover-community/mathlib/commit/cd0bc32b1f3b21fb0d860c088e9b71d97fe0dc65)
chore(data/set/finite): move defns up hierarchy; rename fintype_of_finset, card_fintype_of_finset ([#1615](https://github.com/leanprover-community/mathlib/pull/#1615))

* chore(data/set/finite): move defns up hierarchy

* get namespaces right

* fixes

* fix build

### [2019-10-31T13:24:24+00:00](https://github.com/leanprover-community/mathlib/commit/6b51787e8bebe1f73fea6959eaa0038be6e2b6b0)
feat(order/conditionally_complete_lattice): add complete_linear_order instance for enat ([#1633](https://github.com/leanprover-community/mathlib/pull/#1633))

### [2019-10-31T11:20:33+00:00](https://github.com/leanprover-community/mathlib/commit/780cbc98b28cf141cca7f349dcd128d1286eaf2a)
feat(tactic/simps): allow let-expressions ([#1626](https://github.com/leanprover-community/mathlib/pull/#1626))

* feat(simps); allow let-expressions

* Update src/meta/expr.lean

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

### [2019-10-30T20:31:06+00:00](https://github.com/leanprover-community/mathlib/commit/d43f7f9c1562db60bc6e3ef65aefa0924bde9b4a)
feat(.travis.yml): add linting to test stage ([#1606](https://github.com/leanprover-community/mathlib/pull/#1606))

### [2019-10-30T17:35:02+00:00](https://github.com/leanprover-community/mathlib/commit/aadfde68a318c3108e5f47361569edb20475ec10)
feat(data/fintype): fintype.card_subtype_lt ([#1635](https://github.com/leanprover-community/mathlib/pull/#1635))

* feat(data/fintype): fintype.card_subtype_lt

* Update src/data/fintype.lean

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

### [2019-10-29T22:34:46+00:00](https://github.com/leanprover-community/mathlib/commit/ca9008153aaa6f16c7e2f691231b889dbb05a576)
feat(number_theory/sum_four_squares): every natural number is the sum of four square numbers ([#1560](https://github.com/leanprover-community/mathlib/pull/#1560))

* feat(number_theory/sum_four_squares): every natural number is the sum of four square numbers

* Johan's suggestions

* some better parity proofs

* fix silly lemmas in finite_fields

* generalize a lemma

* fix build

* Update src/number_theory/sum_four_squares.lean

* add docs in correct style

### [2019-10-29T09:22:53+00:00](https://github.com/leanprover-community/mathlib/commit/6030ff0a9d2498b1389c7a3be9b3d938a351dac3)
chore(category_theory): speed-up monoidal.of_has_finite_products ([#1616](https://github.com/leanprover-community/mathlib/pull/#1616))

### [2019-10-29T07:16:16+00:00](https://github.com/leanprover-community/mathlib/commit/e6e25d0610a48e87a67d40a79c6c05d48ff16d07)
cleanup(order|string) ([#1629](https://github.com/leanprover-community/mathlib/pull/#1629))

move data.string to data.string.basic
remove classical.decidable_linear_order. was duplicate of classical.DLO

### [2019-10-29T05:05:10+00:00](https://github.com/leanprover-community/mathlib/commit/b9e3dbba8516a7a0168a411716d3da5bba8d7e61)
feat(rat): give Q-algebra structure on field ([#1628](https://github.com/leanprover-community/mathlib/pull/#1628))

also move around some declarations in rat.cast
the only new declaration in that file is is_ring_hom_cast

### [2019-10-29T03:03:51+00:00](https://github.com/leanprover-community/mathlib/commit/b5b674c238d3b9ea7b5c3859dcfc27f47109ef10)
fix(*): use has_coe_t ([#1627](https://github.com/leanprover-community/mathlib/pull/#1627))

### [2019-10-29T00:42:49+00:00](https://github.com/leanprover-community/mathlib/commit/0ea3dfe4967657e6ffc1e2b573551443c6309c3d)
feat(tactic/rcases): transport the `cases h : e` syntax to `rcases` ([#1611](https://github.com/leanprover-community/mathlib/pull/#1611))

* Update rcases.lean

* Update rcases.lean

* Update rcases.lean

* Update lift.lean

* Update rcases.lean

* Update tactics.md

* Update rcases.lean

### [2019-10-28T21:23:53+00:00](https://github.com/leanprover-community/mathlib/commit/7a8f53e12b4d033ba0178b8f8bc2ab5ab7749537)
feat(tactic/lint): silent linting ([#1580](https://github.com/leanprover-community/mathlib/pull/#1580))

* feat(tactic/lint): silent linting

* doc(tactic/lint): doc silent linting and nolint features

* fix test

* change notation for silent linting

* style(tactic/lint): remove commented lines

### [2019-10-28T16:28:58+00:00](https://github.com/leanprover-community/mathlib/commit/94e368c5025c8e888da89c5bfc326c88d05f9496)
chore(ring_theory/algebra): add docstring to algebra.comap and remove unused instances ([#1624](https://github.com/leanprover-community/mathlib/pull/#1624))

* doc(ring_theory/algebra): add docstring to algebra.comap

* Update algebra.lean

### [2019-10-28T10:34:50+00:00](https://github.com/leanprover-community/mathlib/commit/c2e81ddde3d5d8e84358c767703656bf16f0ef7b)
fix(tactic/omega): fix omega bugs, add docstring (closes [#1484](https://github.com/leanprover-community/mathlib/pull/#1484)) ([#1620](https://github.com/leanprover-community/mathlib/pull/#1620))

* Fix omega bugs, add docstring

* style(tactic/omega/main): trivial cleaning

### [2019-10-27T17:05:13+00:00](https://github.com/leanprover-community/mathlib/commit/1fa03c29f9f273203bbffb79d10d31f696b3d317)
feat(linear_algebra/basic): define algebra structure on endomorphisms of module ([#1618](https://github.com/leanprover-community/mathlib/pull/#1618))

* feat(linear_algebra/basic): define algebra structure on endomorphisms of module

* Update algebra.lean

### [2019-10-27T07:06:37+00:00](https://github.com/leanprover-community/mathlib/commit/89ece147049fb463f9ff320b73433fcdd32370ce)
fix(data/mv_polynomial): generalize equivs to comm_semiring ([#1621](https://github.com/leanprover-community/mathlib/pull/#1621))

This apparently makes the elaborator's job a lot easier, and
reduces the compile time of the whole module by a factor of 3.

### [2019-10-27T02:35:54+00:00](https://github.com/leanprover-community/mathlib/commit/8a45d98fdcb2a707387214d798b0387feb761b6f)
chore(category_theory): remove superfluous lemma ([#1614](https://github.com/leanprover-community/mathlib/pull/#1614))

### [2019-10-26T12:58:23+00:00](https://github.com/leanprover-community/mathlib/commit/8eaf478a8d96bce3c62573ae452f86672aea4d66)
feat(linear_algebra/basis): Dedekind's linear independence of characters ([#1595](https://github.com/leanprover-community/mathlib/pull/#1595))

* feat(linear_algebra/basis): Dedekind's linear independence of characters

* feat(linear_algebra/basis): generalize independence of characters to integral domains

* chore(linear_algebra/basis): change proofs

* commenting the proof

### [2019-10-26T10:17:39+00:00](https://github.com/leanprover-community/mathlib/commit/b9798dc7bf2a342612bfa1f40591345d50bed9c8)
feat(data/nat): a lemma about min_fac ([#1603](https://github.com/leanprover-community/mathlib/pull/#1603))

* feat(data/nat): a lemma about min_fac

* feat(data/nat): a lemma about min_fac

* use Rob's proof

* fix

* let's play golf

* newline

* use Chris' proof

* cleaning up

* rename per Chris' suggestions

### [2019-10-26T08:23:59+00:00](https://github.com/leanprover-community/mathlib/commit/b46f5b0439434b2ed9e23059d5fbe26df5f6028f)
feat(data/set/intervals): fintype instances for ℕ and ℤ ([#1602](https://github.com/leanprover-community/mathlib/pull/#1602))

* starting on fintype instances for Icos

* finishing fintypes

* minor

* move file

* oops

* redone

* formatting

* cleaning up

### [2019-10-25T15:46:12+00:00](https://github.com/leanprover-community/mathlib/commit/6ee8bf9757fd5ca2b3f2955d99bfae693149eb8a)
refactor(data/rat/meta): rename to meta_defs ([#1612](https://github.com/leanprover-community/mathlib/pull/#1612))

* refactor(data/rat/meta): rename to meta_defs

* fix build

### [2019-10-24T21:13:25+00:00](https://github.com/leanprover-community/mathlib/commit/9db43a5fd78c6fb58b031524aeaed2ba55c74199)
chore(data/nat/basic): remove pos_iff_ne_zero' ([#1610](https://github.com/leanprover-community/mathlib/pull/#1610))

This used to be different from pos_iff_ne_zero because the latter
was phrased in terms of `n > 0`, not `0 < n`. Since [#1436](https://github.com/leanprover-community/mathlib/pull/#1436) they
are the same.

### [2019-10-24T17:11:21+00:00](https://github.com/leanprover-community/mathlib/commit/151bcbe22af10c8c3a8a71b035c9de3258f8dfb8)
feat(meta/expr,data/rat/basic): add rat.reflect ([#1565](https://github.com/leanprover-community/mathlib/pull/#1565))

* feat(meta/expr,data/rat/basic): add rat.reflect

* doc(meta/expr,data/rat/basic): clarify type restrictions for mk_numeral functions

* fix name clash with norm_num functions

* fix doc string to expr.of_rat

* Update src/data/rat/basic.lean

Co-Authored-By: Reid Barton <rwbarton@gmail.com>

* fix declaration and move to new file

* tests

* fix import

* protect rat.reflect

* to_pos_rat --> to_nonneg_rat

* correctly test rat.reflect

### [2019-10-24T15:08:35+00:00](https://github.com/leanprover-community/mathlib/commit/3f8a492bfa4ba2ad0ff26c3bff298e3afb05f861)
chore(category_theory): replace some @[simp] with @[simps] ([#1605](https://github.com/leanprover-community/mathlib/pull/#1605))

### [2019-10-24T13:48:11+00:00](https://github.com/leanprover-community/mathlib/commit/b1f44ba10bf61de72f8f2fc8f8b36d4691ad1260)
chore(group_theory/free_group,order/zorn): rename zorn.zorn and sum.sum ([#1604](https://github.com/leanprover-community/mathlib/pull/#1604))

* chore(order/zorn): rename zorn.zorn

* chore(group_theory/free_group): rename sum.sum

* chore(group_theory/free_group,order/zorn): remove nolint

### [2019-10-24T11:26:19+00:00](https://github.com/leanprover-community/mathlib/commit/5da754c96db69aa619b136a68bd9b70a2867958b)
fix(tactic/solve_by_elim): parameter parsing ([#1591](https://github.com/leanprover-community/mathlib/pull/#1591))

* fix(tactic/solve_by_elim): parameter parsing

* revert accidental commenting out

* doc comments for solve_by_elim

* fix build

### [2019-10-24T06:28:15+00:00](https://github.com/leanprover-community/mathlib/commit/4b9cdf44b38fcd0645ed2a2887f96783085119d1)
chore(*): pass dup_namespace and def_lemma lint tests ([#1599](https://github.com/leanprover-community/mathlib/pull/#1599))

* chore(*): pass dup_namespace and def_lemma lint tests

* Update src/group_theory/free_group.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/number_theory/pell.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/order/lattice.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/set_theory/ordinal.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/set_theory/ordinal.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/tactic/transfer.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/group_theory/free_group.lean

Co-Authored-By: Reid Barton <rwbarton@gmail.com>

* using nolint

### [2019-10-24T02:49:46+00:00](https://github.com/leanprover-community/mathlib/commit/31c73c1d38b786a5f26fd4675ebdf4ccb513fc13)
feat(data/multiset): map_eq_map_of_bij_of_nodup ([#1590](https://github.com/leanprover-community/mathlib/pull/#1590))

### [2019-10-24T00:47:18+00:00](https://github.com/leanprover-community/mathlib/commit/08977be6c38f2a5c361d5b02da1b7dc636c844b9)
feat(algebra/semiconj): define `semiconj_by` and some operations ([#1576](https://github.com/leanprover-community/mathlib/pull/#1576))

* feat(algebra/semiconj): define `semiconj_by` and some operations

Also rewrite `algebra/commute` to reuse results from `algebra/semiconj`.

* Some `@[simp]` attributes

* Fixes by @rwbarton, more docs

* Add two more constructors

### [2019-10-23T23:11:12+00:00](https://github.com/leanprover-community/mathlib/commit/e2a8e639a0d0f452d162e13c1d5b2804a135c635)
feat(geometry/manifold): improvements for smooth manifolds ([#1593](https://github.com/leanprover-community/mathlib/pull/#1593))

* feat(geometry/manifold): improvements to smooth manifolds

* fix

* better definition for half-space

* fix docstring

* address comments

* more comments

### [2019-10-23T20:48:14+00:00](https://github.com/leanprover-community/mathlib/commit/b433afa78a749ba0ae50006e76b84b0e0e45b2bf)
feat(algebra/big_operators): sum_ite ([#1598](https://github.com/leanprover-community/mathlib/pull/#1598))

* feat(algebra/big_operators): sum_ite

rename the current `sum_ite` to `sum_ite_eq` and add a more general version

* Update src/algebra/big_operators.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-10-23T20:28:52+00:00](https://github.com/leanprover-community/mathlib/commit/36dfcfcdcc19434f77c7d93caa7ea126eee22504)
doc(topology/topological_fiber_bundle): documentation improvements ([#1594](https://github.com/leanprover-community/mathlib/pull/#1594))

* feat(topology/topological_fiber_bundle): improvements

* minor fixes

### [2019-10-23T17:05:43+00:00](https://github.com/leanprover-community/mathlib/commit/d214c61c0ab67212cce2398d511ba133048ecf4f)
feat(data/nat/modeq): div_mod_eq_mod_mul_div ([#1597](https://github.com/leanprover-community/mathlib/pull/#1597))

### [2019-10-23T14:43:45+00:00](https://github.com/leanprover-community/mathlib/commit/36f711380208e821504443cc9f7787c5793f45e6)
fix(suggest): focus1 at the correct moment ([#1592](https://github.com/leanprover-community/mathlib/pull/#1592))

### [2019-10-23T12:50:43+00:00](https://github.com/leanprover-community/mathlib/commit/24dd80b0db5f2adbefd3b00709b4a445fc18fb9b)
chore(src/data/mv_polynomial): doc comments and removing unused arguments ([#1585](https://github.com/leanprover-community/mathlib/pull/#1585))

* chore(src/data/mv_polynomial): doc comments and removing unused arguments

* Update src/data/mv_polynomial.lean

### [2019-10-23T10:48:29+00:00](https://github.com/leanprover-community/mathlib/commit/079e6ec9dc1cdebfac33b4a3b87ecb7467d57c9c)
feat(analysis/normed_space): norms on ℤ and ℚ ([#1570](https://github.com/leanprover-community/mathlib/pull/#1570))

* feat(analysis/normed_space): norms on ℤ and ℚ

* Add some `elim_cast` lemmas

* Add `@[simp]`, thanks @robertylewis

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

### [2019-10-23T07:50:35+00:00](https://github.com/leanprover-community/mathlib/commit/ee5518c2f7687f998f9da841c885820972f3f781)
fix(category_theory/adjunctions): fix deterministic timeouts ([#1586](https://github.com/leanprover-community/mathlib/pull/#1586))

### [2019-10-23T00:26:28+00:00](https://github.com/leanprover-community/mathlib/commit/5722ee88d2018177c2f1945d90343e4f7fe81c97)
refactor(data/finset): restate disjoint_filter ([#1583](https://github.com/leanprover-community/mathlib/pull/#1583))

* refactor(data/finset): restate disjoint_filter

* fix build

* fix build

### [2019-10-22T16:25:55+00:00](https://github.com/leanprover-community/mathlib/commit/31906d885d3194e4bed035beebcfdd57063b9644)
chore(algebra/category/CommRing/limits): fix typo, remove private ([#1584](https://github.com/leanprover-community/mathlib/pull/#1584))

* chore(algebra/category/CommRing/limits): fix typo, remove private

* Update src/algebra/category/CommRing/limits.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/algebra/category/CommRing/limits.lean

* Update src/algebra/category/CommRing/limits.lean

* bleh

* Update src/algebra/category/CommRing/limits.lean

### [2019-10-22T14:30:51+00:00](https://github.com/leanprover-community/mathlib/commit/e8bdb05e4449b4f70404f7df9fbac14271bc6b0e)
feat(algebra/group): conversion between `→*` and `→+` ([#1569](https://github.com/leanprover-community/mathlib/pull/#1569))

* feat(algebra/group): conversion between `→*` and `→+`

* docs

* Rename to allow use of projection notation

### [2019-10-22T12:22:04+00:00](https://github.com/leanprover-community/mathlib/commit/93b17864077ed9f8d5998e77b94380ea65a19697)
feat(archive): add proof of sensitivity conjecture ([#1553](https://github.com/leanprover-community/mathlib/pull/#1553))

* feat(*): various lemmas from the sensitivity project

* fix proof broken by nonterminal simp

* Update src/linear_algebra/dual.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* lint dual.lean

* remove decidable_mem_of_fintype instance

this leads to loops with `subtype.fintype` under the right decidable_eq assumptions

* dual_lc is invalid simp lemma

* fix namespace

* add extra lemma

* feat(archive): add proof of sensitivity conjecture

* suggestions from Johan

* undo removed whitespace

* update header

### [2019-10-22T08:36:07+00:00](https://github.com/leanprover-community/mathlib/commit/1b4d1eaac1011fda0c6e80a6380a0f231cea6be3)
chore(algebra/category/*/colimits): remove unnecessary projections ([#1588](https://github.com/leanprover-community/mathlib/pull/#1588))

* refactor(category_theory,algebra/category): make algebraic categories not [reducible]

Adapted from part of [#1438](https://github.com/leanprover-community/mathlib/pull/#1438).

* Update src/algebra/category/CommRing/basic.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

* adding missing forget2 instances

* Converting Reid's comment to a [Note]

* adding examples testing coercions

* chore(algebra/category/*/colimits): remove unnecessary projections

### [2019-10-22T06:42:16+00:00](https://github.com/leanprover-community/mathlib/commit/2b98d47afe65139b7c7ee3a13be224940cae2d97)
feat(category_theory): add `reassoc` annotations ([#1558](https://github.com/leanprover-community/mathlib/pull/#1558))

* feat(category_theory): add `reassoc` annotations

* Update reassoc_axiom.lean

* Update src/tactic/reassoc_axiom.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

* Update src/tactic/reassoc_axiom.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

* Update src/tactic/reassoc_axiom.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

* Update src/tactic/reassoc_axiom.lean

* Update src/tactic/reassoc_axiom.lean

* Update reassoc_axiom.lean

* Update tactics.lean

* Update tactics.md

* Update reassoc_axiom.lean

### [2019-10-22T04:37:39+00:00](https://github.com/leanprover-community/mathlib/commit/1741a1d6774e5d72be05b3c463bc5639262b6e1d)
feat(data/nat/basic): division inequalities ([#1579](https://github.com/leanprover-community/mathlib/pull/#1579))

* feat(data/nat/basic): division inequalities

* whitespace

* fix

* shorten proof

### [2019-10-22T02:29:49+00:00](https://github.com/leanprover-community/mathlib/commit/c9ba7a5c5b86211f248ad1badeff57f1ba28de29)
refactor(category_theory,algebra/category): make algebraic categories not [reducible] ([#1491](https://github.com/leanprover-community/mathlib/pull/#1491))

* refactor(category_theory,algebra/category): make algebraic categories not [reducible]

Adapted from part of [#1438](https://github.com/leanprover-community/mathlib/pull/#1438).

* Update src/algebra/category/CommRing/basic.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

* adding missing forget2 instances

* Converting Reid's comment to a [Note]

* adding examples testing coercions

### [2019-10-22T00:57:19+00:00](https://github.com/leanprover-community/mathlib/commit/340178d86e1f3aa9ae203780ff1fc1a8812b85b5)
feat(data/finset): inj_on_of_surj_on_of_card_le ([#1578](https://github.com/leanprover-community/mathlib/pull/#1578))

* feat(data/finset): inj_on_of_surj_on_of_card_le

* Type ascriptions

* function namespace

### [2019-10-21T22:57:07+00:00](https://github.com/leanprover-community/mathlib/commit/39092ab01058c88aad27c3f98b3e71fed963eee1)
feat(*): various lemmas from the sensitivity project ([#1550](https://github.com/leanprover-community/mathlib/pull/#1550))

* feat(*): various lemmas from the sensitivity project

* fix proof broken by nonterminal simp

* Update src/linear_algebra/dual.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* lint dual.lean

* remove decidable_mem_of_fintype instance

this leads to loops with `subtype.fintype` under the right decidable_eq assumptions

* dual_lc is invalid simp lemma

* fix namespace

* add extra lemma

* fix sum_const

* remove unnecessary dec_eq assumptions

* remove decidable_eq assumptions

* document dual.lean

* use classical locale

* remove some unnecessary includes

* remove an unused variable

* Update src/linear_algebra/dual.lean

* fixing a doc comment

### [2019-10-21T20:49:04+02:00](https://github.com/leanprover-community/mathlib/commit/96ebf8cc7c446e977637a13740645a7f8e0c8992)
docs(README): Remove Patrick from the maintainer list.

### [2019-10-21T15:12:24+00:00](https://github.com/leanprover-community/mathlib/commit/6cf3d040d34d466543d0f02ccc072235f1c5e29f)
fix(algebra/group/hom): Fix spurrious arguments ([#1581](https://github.com/leanprover-community/mathlib/pull/#1581))

This bug was introduced in eb230d3b48f4da49b

### [2019-10-21T14:34:56+00:00](https://github.com/leanprover-community/mathlib/commit/f19dbf29de215cbe2ff6831cc9fa481b6ae56d64)
feat(geometric/manifold): smooth manifolds ([#1555](https://github.com/leanprover-community/mathlib/pull/#1555))

* smooth manifolds

* fix docstrings

* update docstring

* remove out_param

### [2019-10-21T12:39:30+00:00](https://github.com/leanprover-community/mathlib/commit/f52e952e18565bf8cf6d0d6742ee5a21ebad0b4b)
feat(data/finset): define `finset.Ico.subset_iff` ([#1574](https://github.com/leanprover-community/mathlib/pull/#1574))

### [2019-10-21T10:18:48+00:00](https://github.com/leanprover-community/mathlib/commit/a4bbbdeabd266f4a4374facc35a3d4fcd897c682)
feat(topology/topological_fiber_bundle): topological fiber bundles ([#1421](https://github.com/leanprover-community/mathlib/pull/#1421))

* feat(topology/topological_fiber_bundle): topological fiber bundles

* better definition of fiber bundles

### [2019-10-21T08:23:05+00:00](https://github.com/leanprover-community/mathlib/commit/d2d29ffd3676ddc60c8f9b5ca1d39ccc3845aa5a)
feat(algebra/geom_sum): sum of a geom_series over an Ico ([#1573](https://github.com/leanprover-community/mathlib/pull/#1573))

* feat(algebra/geom_sum): sum of a geom_series over an Ico

* Add two more versions as requested by @jcommelin

### [2019-10-21T08:06:20+00:00](https://github.com/leanprover-community/mathlib/commit/0b660a9f7cc69f3a1e83dff4262d06e13723051d)
fix(scripts): sanity_check -> lint [ci skip] ([#1575](https://github.com/leanprover-community/mathlib/pull/#1575))

* fix(scripts): sanity_check -> lint [ci skip]

* also fix in .gitignore

### [2019-10-21T12:08:57+11:00](https://github.com/leanprover-community/mathlib/commit/809276c0aa5d5d8640f230475e2f491b69db7093)
feat(topology/metric_space): polygonal version of the triangle inequality ([#1572](https://github.com/leanprover-community/mathlib/pull/#1572))

* feat(topology/metric_space): "polygon" version of the triangle inequality

* Add two more versions of the "polygonal" inequality

* Use `dist_le_Ico_sum_dist` in `cauchy_seq_of_summable_dist`

### [2019-10-20T15:33:20+00:00](https://github.com/leanprover-community/mathlib/commit/b1654df18ac2b5d516ccb30bbea5b67b60106940)
feat(meta/rb_map,tactic/monotonicity): replace rb_map.insert_cons ([#1571](https://github.com/leanprover-community/mathlib/pull/#1571))

rb_map key (list value) is the same as rb_lmap. Usages of this function
should be replaced with rb_lmap.insert

### [2019-10-20T10:46:47+00:00](https://github.com/leanprover-community/mathlib/commit/74bed0c924771c50088e328e2d5c77ccf060bbc0)
feat(tactic/suggest): generalize and reimplement library_search ([#1552](https://github.com/leanprover-community/mathlib/pull/#1552))

* Create refine_list.lean

The refine_list tactic.

* Create refine_list.lean

The refine_list.lean file

* Update tactics.md

Added refine_list docs.

* Update library_search.lean

Added replace_mvars function

* Update library_search.lean

Added tactic_statement function and some code in the main library_search function which uses it.

* commits

* refine_list commits

* Scott's work

* update tactics.md

* doc strings

* update

* Update refine_list.lean

Removes stray TODO line and changed the docstring for the main refine_list function.

* Update refine_list.lean

Spelling...

* get_state and set_state replace by read and write

* Combined functions and removed run_and_save_state

* removed symmetry from library_search

* removing test that doesn't work without symmetry

* test properly

* rename `refine_list` to `suggest`

* cleaning up

* minor

* better sorting of results

* oops, turn off trace messages again

* type annotation

* optimisation, and simpler logic

* further explanation

* a little more cleanup

* Update src/tactic/library_search.lean

Rob Lewis's refactoring of `tactic_statement`

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

* Update src/tactic/suggest.lean

Remove `do` in line 82

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

* Update src/tactic/suggest.lean

Rob's update of suggest in tactic.interactive.

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

* changed interactive to tactic.interactive

* used /--/ for copyright headers

* adding comments explaining logic in apply_and_solve, and an optimisation

* refactor no_mvars_in_target

* add missing argument to interactive tactic

* move all printing to the interactive tactic

* refactoring

* cleanup

* refactoring

* complete refactor; library_search is defined in terms of suggest_core now

* restore protect to list.traverse and option.traverse

* Update src/tactic/suggest.lean

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

* some doc comments

### [2019-10-19T22:11:22+00:00](https://github.com/leanprover-community/mathlib/commit/f54463254784b400da2e33dfa58f94775e3de845)
feat(algebra/big_operators): products and sums over `finset.Ico` ([#1567](https://github.com/leanprover-community/mathlib/pull/#1567))

### [2019-10-19T19:57:42+00:00](https://github.com/leanprover-community/mathlib/commit/173e70a0c4cbbf525bb8fde62105084ad27f4572)
feat(tactic/lint): rename and refactor sanity_check ([#1556](https://github.com/leanprover-community/mathlib/pull/#1556))

* chore(*): rename sanity_check to lint

* rename sanity_check files to lint

* refactor(tactic/lint): use attributes to add new linters

* feat(tactic/lint): restrict which linters are run

* doc(tactic/lint): document

* doc(tactic/lint): document list_linters

* chore(tactic/doc_blame): turn doc_blame into a linter

* remove doc_blame import

* fix(test/lint)

* feat(meta/rb_map): add name_set.insert_list

* feat(tactic/lint): better control over which linters are run

* ignore instances in doc_blame

* update lint documentation

* minor refactor

* correct docs

* correct command doc strings

* doc rb_map.lean

* consistently use key/value

* fix command doc strings

### [2019-10-19T19:04:46+00:00](https://github.com/leanprover-community/mathlib/commit/ee398b66c6b576848857a2383ebdf0608070cd62)
feat(algebra/floor): prove `⌈x⌉ ≤ ⌊x⌋ + 1` ([#1568](https://github.com/leanprover-community/mathlib/pull/#1568))

### [2019-10-18T19:41:32+00:00](https://github.com/leanprover-community/mathlib/commit/05102ecb38b4d253c71638713b45e514ee18de72)
chore(category_theory): using simps ([#1500](https://github.com/leanprover-community/mathlib/pull/#1500))

* chore(category_theory): using simps

* more simps

* remove simp lemma

* revertings overlapping @[simps]

### [2019-10-18T03:27:47+00:00](https://github.com/leanprover-community/mathlib/commit/a1c0ad588bcb07d77cf1c294522848b4915e1635)
feat(category_theory): def `is_isomorphic_setoid`, `groupoid.iso_equiv_hom` ([#1506](https://github.com/leanprover-community/mathlib/pull/#1506))

* feat(category_theory): def `is_isomorphic_setoid`, `groupoid.iso_equiv_hom`

* Move to a dedicated file, define `isomorphic_class_functor`

* explicit/implicit arguments

* Update src/category_theory/groupoid.lean

* Update src/category_theory/groupoid.lean

* Update src/category_theory/isomorphism_classes.lean

* Update src/category_theory/isomorphism_classes.lean

* Update src/category_theory/isomorphism_classes.lean

### [2019-10-17T20:03:17+00:00](https://github.com/leanprover-community/mathlib/commit/e5fc2a702a05614bab70087e0c7fe1be817ddb6f)
refactor(topology,calculus): change subset condition for composition ([#1549](https://github.com/leanprover-community/mathlib/pull/#1549))

* refactor(topology,calculus): change subset condition for composition

* improve docstrings

* add is_open Ioi

* reviewer's comments

* typo

### [2019-10-17T21:46:14+02:00](https://github.com/leanprover-community/mathlib/commit/cc19e30ee01c57846eee59dffd276c2b4e366b52)
docs(project): change example project [ci skip]

### [2019-10-17T07:58:42+00:00](https://github.com/leanprover-community/mathlib/commit/905beb0806965cce81933bce7bde1f3eadc0f9b0)
fix(topology/metric_space): fix uniform structure on Pi types ([#1551](https://github.com/leanprover-community/mathlib/pull/#1551))

* fix(topology/metric_space): fix uniform structure on pi tpype

* cleanup

* better construction of metric from emetric

* use simp only instead of simp

### [2019-10-16T21:40:58+00:00](https://github.com/leanprover-community/mathlib/commit/ee863ec1e049391355e5f634f186e130a9751035)
feat(ring_theory/algebraic): algebraic extensions, algebraic elements ([#1519](https://github.com/leanprover-community/mathlib/pull/#1519))

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

* Fix algebraic.lean

* Fix build, mostly

* Remove stuff about UMP of alg clos

* Prove transitivity of algebraic extensions

* Add some docstrings

* Remove files with stuff for future PRs

* Add a bit to the module docstring

* Fix module docstring

* Include assumption in section injective

* Aesthetic changes to is_integral_of_mem_of_fg

* Little improvements of proofs in algebraic.lean

* Improve some proofs in integral_closure.lean

* Make variable name explicit

* Process comments

### [2019-10-16T18:45:00+00:00](https://github.com/leanprover-community/mathlib/commit/cbf81dff8bfbc62aa974a26bedc6dff198a040c4)
archive(imo1988_q6): a formalization of Q6 on IMO1988 ([#1455](https://github.com/leanprover-community/mathlib/pull/#1455))

* archive(imo1988_q6): a formalization of Q6 on IMO1988

* WIP

* Clean up, document, and use omega

* Remove some non-terminal simps

* Non-terminal simp followed by ring is fine

* Include copyright statement

* Add comment justifying example

* Process review comments

* Oops, forgot a line

* Improve comments in the proof

### [2019-10-16T17:05:22+00:00](https://github.com/leanprover-community/mathlib/commit/ad8387cc8f0a90b217a883a070f8b2e1c9a2b8b7)
feat(field_theory/finite): cardinality of images of polynomials ([#1554](https://github.com/leanprover-community/mathlib/pull/#1554))

* feat(field_theory/finite): cardinality of images of polynomials

* docstrings

* Johan's suggestions

* slightly shorten proof

### [2019-10-16T03:46:48+00:00](https://github.com/leanprover-community/mathlib/commit/09fd631bed2af3ea89b11fdff6112a606de44d09)
feat(data/zmod/basic): val_min_abs ([#1548](https://github.com/leanprover-community/mathlib/pull/#1548))

* feat(data/zmod/basic): val_min_abs

* Update basic.lean

* docstring and fix `zmodp` versions

### [2019-10-14T12:13:21+00:00](https://github.com/leanprover-community/mathlib/commit/c3d1bd7106fd28852bcbc546b902dfe79e806d64)
feat(data/polynomial): card_roots' ([#1546](https://github.com/leanprover-community/mathlib/pull/#1546))

### [2019-10-13T12:52:09+00:00](https://github.com/leanprover-community/mathlib/commit/0ee1272aaec3b581dff6fddac1fe189fa383dbfd)
fix(doc/contribute): fix broken link ([#1547](https://github.com/leanprover-community/mathlib/pull/#1547))

### [2019-10-13T09:57:58+00:00](https://github.com/leanprover-community/mathlib/commit/d716648f22e02779394d75daf00485b10c253c43)
docs(topology): some more module docstrings ([#1544](https://github.com/leanprover-community/mathlib/pull/#1544))

### [2019-10-13T08:08:28+00:00](https://github.com/leanprover-community/mathlib/commit/d10fd1e895242b8280f7675da78753f92d41cf50)
feat(data/int/basic): int.nat_abs_eq_zero ([#1545](https://github.com/leanprover-community/mathlib/pull/#1545))

* feat(data/int/basic): int.nat_abs_eq_zero

* Update basic.lean

* Update basic.lean

### [2019-10-12T20:07:23+00:00](https://github.com/leanprover-community/mathlib/commit/646c035aefcca52c90e839ad3f521b535d52ad96)
refactor(topology): mild reorganization ([#1541](https://github.com/leanprover-community/mathlib/pull/#1541))

* refactor(topology): mild reorganization

Another attempt to increase cohesion of modules in topology.
The old `constructions` module was starting to turn into a collection
of miscellaneous results, and didn't actually contain any constructions
themselves.

The major changes are:

* `constructions` now contains the definitions of the product, subspace,
  ... topologies, which used to be in `order`. This means that theorems
  involving concepts from `maps` (e.g., embeddings) and constructions
  (e.g., products) are now in `constructions`, not `maps`.

* `subset_properties` and `separation` now import `constructions`
  rather than the other way around. This means that theorems like
  "a product of compact spaces is compact" are now in `subset_properties`,
  not `constructions`.

* `homeomorph` is split off into its own file, which was easy because
  it was at the end of `constructions` anyways.

* reorder universes in constructions

* move README.md to docs/theories/topology.md

* expand documentation of metric/uniform spaces slightly

* update pointers to docs/theories/topological_spaces.md

### [2019-10-12T18:21:51+00:00](https://github.com/leanprover-community/mathlib/commit/92a9a780791ca47ce15208adb5e3eb575bed09e6)
fix(topology/continuous_on): avoid duplicate instance arguments ([#1542](https://github.com/leanprover-community/mathlib/pull/#1542))

This was broken by [#1516](https://github.com/leanprover-community/mathlib/pull/#1516), caught by sanity_check.

### [2019-10-12T18:05:26+00:00](https://github.com/leanprover-community/mathlib/commit/995add3aaecf5d5c8a487cc24755afcdbfe9b2a3)
fix(topology/algebra/group_completion): remove redundant instance parameters ([#1543](https://github.com/leanprover-community/mathlib/pull/#1543))

### [2019-10-12T16:02:53+02:00](https://github.com/leanprover-community/mathlib/commit/76090bee103161fd6b31dc63cca75cb042150665)
chore(docs/install/debian): Remove old sentence [ci skip]

### [2019-10-12T10:28:08+00:00](https://github.com/leanprover-community/mathlib/commit/27515619bcd834006f2936b292021135496b4efb)
minor updates to the installation instructions ([#1538](https://github.com/leanprover-community/mathlib/pull/#1538))

### [2019-10-11T17:54:17+00:00](https://github.com/leanprover-community/mathlib/commit/d5de80376088954d592a59326c14404f538050a1)
refactor(ring_theory/algebra): alg_hom extends ring_hom and use curly brackets ([#1529](https://github.com/leanprover-community/mathlib/pull/#1529))

* chore(algebra/ring): use curly brackets for ring_hom where possible

* refactor(ring_theory/algebra): alg_hom extends ring_hom and use curly brackets

* fix build

* Update src/ring_theory/algebra.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* fix build

### [2019-10-11T13:15:04+00:00](https://github.com/leanprover-community/mathlib/commit/6b7377aa21568db86c42211b70155ebd7cf8e583)
chore(algebra/ring): use curly brackets for ring_hom where possible ([#1525](https://github.com/leanprover-community/mathlib/pull/#1525))

* chore(algebra/ring): use curly brackets for ring_hom where possible

* add comments explaining motivation

* move explanation to header

* fix build

* Update src/algebra/ring.lean

* scott's suggestion

### [2019-10-11T11:48:51+00:00](https://github.com/leanprover-community/mathlib/commit/38a0ffe9a87ab677bdbf56c9b5c60ae64da9dd19)
refactor(ring_theory/algebra): algebra should extend has_scalar not module ([#1532](https://github.com/leanprover-community/mathlib/pull/#1532))

* refactor(ring_theory/algebra): algebra should extend has_scalar not module

* fix build

* fix build

* Update algebra.lean

* Update module.lean

* fx build

* fix build

* fix again

* fix build

* fix build

### [2019-10-11T11:26:29+00:00](https://github.com/leanprover-community/mathlib/commit/338146b73d5693dad0f31f560ca107ee81ff37d5)
fix(algebra/char_p): typo in docstring ([#1537](https://github.com/leanprover-community/mathlib/pull/#1537))

I don't know anything about semirings but I do know there isn't a homomorphism from int to them in general. Do people talk about kernels? (this would be some semi-ideal or something). My change is probably better than what we had but someone who knows what a semiring is might want to check that my suggestion makes sense.

### [2019-10-11T03:41:02+00:00](https://github.com/leanprover-community/mathlib/commit/eb230d3b48f4da49b127d14ef477c521a43ff188)
chore(algebra/group/hom): use curly brackets for instances where possible ([#1524](https://github.com/leanprover-community/mathlib/pull/#1524))

* chore(algebra/group/hom): use curly brackets for instances where possible

* add comments mentioning motivation behind brackets

* move explanation to header

* fix build

* Update src/algebra/group/hom.lean

### [2019-10-11T01:59:31+00:00](https://github.com/leanprover-community/mathlib/commit/364c26e932a067cf47bf22cb910c6d94b8abdc93)
chore(algebra/module): use curly brackets instead of square brackets in more places ([#1523](https://github.com/leanprover-community/mathlib/pull/#1523))

* chore(algebra/module): use curly brackets instead of square brackets in more places

* Add explanation behind implicit brackets

* Update src/algebra/module.lean

### [2019-10-10T11:14:36+00:00](https://github.com/leanprover-community/mathlib/commit/43d3dee05375f66ea943931db2a30a523e9ee262)
chore(linear_algebra): rename type variables ([#1521](https://github.com/leanprover-community/mathlib/pull/#1521))

* doc(linear_algebra/basis): add doc

* doc(linear_algebra/basis): shorten docstrings

* refactor(linear_algebra/basis): rename type vars

* style(linear_algebra/basic): change variable names

* chore(linear_algebra/dimension): rename type variables

* remove commented code

* style(linear_algebra/bilinear_form): change variable names

* style(linear_algebra/direct_sum_module): change variable names

* style(linear_algebra/matrix): change variable names

* Rename variables in finsupp_vector_space.lean

* style(linear_algebra/sesquilinear_form): change variable names

* style(linear_algebra/tensor_product): change variable names

* change kappas to bb k's

* style(linear_algebra/finsupp): change variable names

* change universe levels

* change bb k to K

### [2019-10-10T09:00:38+00:00](https://github.com/leanprover-community/mathlib/commit/dc788a0b91064c0d74024fc8fc92c9e3fae10457)
feat(topology/sequences): every first-countable space is sequential ([#1528](https://github.com/leanprover-community/mathlib/pull/#1528))

* feat(topology/sequences): every first-countable space is sequential

* fixup style

* fixup comments

* remove redundant type ascription

### [2019-10-09T19:53:01+00:00](https://github.com/leanprover-community/mathlib/commit/7d792ec4645540f2b82b9a6e430240723db5ff85)
chore(ring_theory/adjoin_root): remove some unused decidable_eq ([#1530](https://github.com/leanprover-community/mathlib/pull/#1530))

### [2019-10-09T16:00:50+00:00](https://github.com/leanprover-community/mathlib/commit/a17a9a6a99fc5e14fda5021494f834b57eddc91c)
fix(tactic/{use,ring}): instantiate metavariables in goal ([#1520](https://github.com/leanprover-community/mathlib/pull/#1520))

`use` now tidies up the subgoals that it leaves behind after instantiating constructors.

`ring` is sensitive to the presence of such metavariables, and we can't guarantee that it doesn't see any,
so it should check for them before it runs.

### [2019-10-09T14:59:54+00:00](https://github.com/leanprover-community/mathlib/commit/45633aa030f5dc398a80d66d7dd1f21d744746d8)
refactor(topology/algebra/polynomial): move topology.instances.polynomial ([#1527](https://github.com/leanprover-community/mathlib/pull/#1527))

### [2019-10-09T14:24:19+00:00](https://github.com/leanprover-community/mathlib/commit/0ea83c09323cbd1fe11546a86ffa5810c763f5df)
docs(data/holor): some additional documentation ([#1526](https://github.com/leanprover-community/mathlib/pull/#1526))

### [2019-10-09T05:24:44+00:00](https://github.com/leanprover-community/mathlib/commit/6ccfe5a3479bd6b8d63d4ddffaaf37695a446793)
feat(algebra/ordered...): Two tiny lemmas ([#1522](https://github.com/leanprover-community/mathlib/pull/#1522))

* feat(algebra/ordered...): Two tiny lemmas

* style(src/algebra/ordered_field)

Co-Authored-By: Reid Barton <rwbarton@gmail.com>

### [2019-10-08T16:33:02+00:00](https://github.com/leanprover-community/mathlib/commit/7c560512b849832824493949a29fbf6b6b7ac223)
doc(linear_algebra/basis): add doc ([#1503](https://github.com/leanprover-community/mathlib/pull/#1503))

* doc(linear_algebra/basis): add doc

* doc(linear_algebra/basis): shorten docstrings

### [2019-10-08T15:54:18+00:00](https://github.com/leanprover-community/mathlib/commit/6b15eb29493cc1a3954fcc3960f49fcd4a7dda78)
chore(analysis): put lemmas in normed_field namespace ([#1517](https://github.com/leanprover-community/mathlib/pull/#1517))

The motivation is to be able to state, say norm_mul for subrings of a
normed field, typically p-adic integers. That way we can have
padic_int.norm_mul, open the padic_int namespace and have no ambiguous
name.

### [2019-10-08T13:51:59+00:00](https://github.com/leanprover-community/mathlib/commit/afda1a2c59521685840df3ddcda872a3344b3461)
refactor(topology/continuous_on): move continuous_{on,within_at} to own file ([#1516](https://github.com/leanprover-community/mathlib/pull/#1516))

* refactor(topology/continuous_on): move continuous_{on,within_at} to own file

* Update src/topology/continuous_on.lean

### [2019-10-08T02:26:24+00:00](https://github.com/leanprover-community/mathlib/commit/045d931eb47b9d247438fd6cd46b0c4e10197862)
feat(tactic/find): find defs as well as theorems ([#1512](https://github.com/leanprover-community/mathlib/pull/#1512))

* feat(tactic/find): find defs as well as theorems

* use env.mfold

* use try

### [2019-10-08T00:28:49+00:00](https://github.com/leanprover-community/mathlib/commit/ef7248f711c86eea44cb3bc05abe6b4bfbd27c63)
feat(data/quot): define `quotient.map₂'`, use it for group quotient ([#1507](https://github.com/leanprover-community/mathlib/pull/#1507))

### [2019-10-07T22:43:00+00:00](https://github.com/leanprover-community/mathlib/commit/bf2240808710882d09b7ba30b3183c48e79db8b8)
chore(topology/algebra/group_completion): missing namespace ([#1518](https://github.com/leanprover-community/mathlib/pull/#1518))

### [2019-10-07T21:52:59+00:00](https://github.com/leanprover-community/mathlib/commit/1bf831f24b258f0d839698ebb3abf76ee396ea93)
refactor(topology/dense_embedding): move dense embeddings to new file ([#1515](https://github.com/leanprover-community/mathlib/pull/#1515))

### [2019-10-07T21:06:26+00:00](https://github.com/leanprover-community/mathlib/commit/b3eb34d29588efff46a2c465e66f5ef67c036a47)
doc(topology/order): module and definition docstrings ([#1505](https://github.com/leanprover-community/mathlib/pull/#1505))

### [2019-10-07T17:24:46+00:00](https://github.com/leanprover-community/mathlib/commit/f519a125a6fafa59209c2cc9eec1187aefa08b11)
refactor(topology/list): move topology of lists, vectors to new file ([#1514](https://github.com/leanprover-community/mathlib/pull/#1514))

### [2019-10-07T16:34:46+00:00](https://github.com/leanprover-community/mathlib/commit/ddbeb7eb03c0427b66c03eb5a2d9dd1c64387356)
refactor(topology/maps): avoid repetition in dense embeddings ([#1513](https://github.com/leanprover-community/mathlib/pull/#1513))

### [2019-10-05T15:44:17+00:00](https://github.com/leanprover-community/mathlib/commit/78a78efc1699faa760ffe590bb2c948bdd48639e)
feat(group_theory/submonoid): define `subtype.comm_monoid` ([#1511](https://github.com/leanprover-community/mathlib/pull/#1511))

### [2019-10-05T12:20:29+00:00](https://github.com/leanprover-community/mathlib/commit/7df0e3505d32c33302b4ed09ab094dcb15134cc7)
chore(topology): sanity_check pass ([#1510](https://github.com/leanprover-community/mathlib/pull/#1510))

* chore(topology): sanity_check pass

* fix(topology/uniform_space/separation): fix build

* fix(topology/metric_space): some more namespace fixes

### [2019-10-05T05:18:27+00:00](https://github.com/leanprover-community/mathlib/commit/98dbe27a7074b168b1f410ff45f1491c95d678b1)
feat(algebra/opposites): add some trivial `@[simp]` lemmas ([#1508](https://github.com/leanprover-community/mathlib/pull/#1508))

### [2019-10-04T14:25:15+00:00](https://github.com/leanprover-community/mathlib/commit/2f1bd1e59c1c416cc426c0dc4824f65f911c110d)
fix(data/list/min_max): docs typo ([#1504](https://github.com/leanprover-community/mathlib/pull/#1504))

### [2019-10-04T14:08:27+00:00](https://github.com/leanprover-community/mathlib/commit/343237d14959af679257abf016e3a638ba3afe54)
feat(algebra/Module): the category of R-modules ([#1420](https://github.com/leanprover-community/mathlib/pull/#1420))

* Adds Module category

* Move punit module instance to punit_instances.lean

* Minor formatting

* Use coercions for Module morphisms to functions

* Small formatting improvements to Module

* Move module_id to id_apply

* Be specific about the universe Modules live in

* Minor indentation formatting

* updates for [#1380](https://github.com/leanprover-community/mathlib/pull/#1380)

* oops

* remove ext lemma, unnecessary

* reverting changes in TopCommRing

* Change name of `module_hom_comp`

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update todo in src/algebra/category/Module/basic.lean

Co-Authored-By: Scott Morrison <scott@tqft.net>

### [2019-10-04T11:56:55+00:00](https://github.com/leanprover-community/mathlib/commit/494132e1ebdba300a43d66e19ddc5b724fd20129)
feat(algebra): commuting elements ([#1089](https://github.com/leanprover-community/mathlib/pull/#1089))

* Not sure how this works

* Small refactor of geometric sums

* Properties of commuting elements

* Geometric sums moved to geom_sum.lean

* Geometric sums, two commuting variables

* Import geom_sum.lean

* Cover commuting elements of noncommutative rings

* Whitespace

* Add file headers

* Delete stray file

* Sum/prod over range 0, range 1

* Add simp lemmas

* Various changes from PR review

* Add semigroup case

* Changes from PR review

* Corrected all_commute to commute.all

* Minor changes from PR review

* Change line endings back to unix

* `@[to_additive]` can't be a `local attribute`

* Rename `add_pow_comm` to `add_pow_of_commute` as suggested by @jcommelin

* Add a few missing instances

* DRY

* Notation for `gsmul` should go into `add_group`, not `group`

* Prove `gsmul_one`

* Reorder `algebra/commute`, add more lemmas

* Add docs, rename `geom_sum₂_mul_add_comm` to `commute.geom_sum₂_mul_add`.

* Rename, add a docstring

* Fix a typo spotted by @ChrisHughes24

* Move common args to `variables`

* Rename `commute.mul` to `commute.mul_right` etc.

* Add some `@[simp]` attributes.

* More `@[simp]`

* Add some `_iff` versions

### [2019-10-04T00:45:14+00:00](https://github.com/leanprover-community/mathlib/commit/3c58f160fd51ebf989138ed7c8981f821f08f860)
doc(linear_algebra/basic): add module and declaration doc strings ([#1501](https://github.com/leanprover-community/mathlib/pull/#1501))

* doc(linear_algebra/basic): declaration doc strings

* doc(linear_algebra/basic): improve module doc

* Update src/linear_algebra/basic.lean

Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>

### [2019-10-03T19:53:03+00:00](https://github.com/leanprover-community/mathlib/commit/f854371190cf908a7eba4f35803a4ddcc3a0e6e7)
feat(tactic/squeeze_simp): better handling of private declarations ([#1498](https://github.com/leanprover-community/mathlib/pull/#1498))

* feat(tactic/squeeze_simp): better handling of private declarations

* Update core.lean

### [2019-10-03T17:37:55+00:00](https://github.com/leanprover-community/mathlib/commit/4ca1e634217bad1733c3559988fae9adb6706c5e)
chore(*): fix errors in library and sanity_check ([#1499](https://github.com/leanprover-community/mathlib/pull/#1499))

* chore(*): some cleanup by sanity_check

* fix(is_auto_generated): also check for ginductives

* fix(sanity_check): imp_intro is sanity_skip

* fix(sanity_check): don't report names of instances

* first errors

* second errors

* doc(logic/basic): add note

* add link to note

* mention letI

### [2019-10-03T09:33:33+00:00](https://github.com/leanprover-community/mathlib/commit/4bb8d4475f897c8997100d31fe84b33050444374)
feat(data/equiv/algebra): automorphism groups for other structures ([#1141](https://github.com/leanprover-community/mathlib/pull/#1141))

* Added automorphism groups to data/algebra/lean

* feat(data/equiv/algebra):
added automorphism groups

* feat(data/equiv/algebra)
Added automorphism groups

* Minor formatting

* feat(data/equiv/algebra):  add automorphism groups

* Changes based on comments

* minor change

* changes to namespaces and comments added

* expanding comments

* Update src/data/equiv/algebra.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

* Update src/data/equiv/algebra.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

* Update src/data/equiv/algebra.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

* Update src/data/equiv/algebra.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

* Update src/data/equiv/algebra.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

* Update src/data/equiv/algebra.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

* Update src/data/equiv/algebra.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

* Update src/data/equiv/algebra.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

* Update src/data/equiv/algebra.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

* Added monoid case

* Changed Type to Type* also further up in the file

* typo

* I made it compile but not pretty

* More changes

* fixed typo

* fix universes

* update docs

* minor change

* use coercion rather than to_fun in ext lemmas

* Use ≃+* and coercion in ring_equiv.ext

* arguments of group.aut?

* generalize ring_equiv.ext to semirings

* Various changes

* Use only `mul_aut`, `add_aut`, and `ring_aut` for automorphisms.

* Make `*_equiv.ext` arguments agree with `equiv.ext`.

* Adjust documentation.

* Fix compile, add `add_aut.to_perm`

### [2019-10-02T16:42:34+00:00](https://github.com/leanprover-community/mathlib/commit/bea1c20de3e2662b1289d7ed4402761c9555537f)
fix(dioph): remove global vector3 notation ([#1502](https://github.com/leanprover-community/mathlib/pull/#1502))

* fix(dioph): remove global vector3 notation

it overloads list notation, and then tries to find a coercion from vector3 to list

* also make other notations in dioph local

* undo localizing ++, overloading that is probably fine

* add comment

### [2019-10-02T17:27:04+02:00](https://github.com/leanprover-community/mathlib/commit/39ca4f146710d27c4ecff1f69ccfb1afad50cc94)
chore(.): delete CODEOWNERS

### [2019-10-01T18:48:13+00:00](https://github.com/leanprover-community/mathlib/commit/5ed5f59433278367f0b2ceeb7b363d21840a3fc0)
feat(tactic/delta_instance): handle parameters and use in library ([#1483](https://github.com/leanprover-community/mathlib/pull/#1483))

* feat(tactic/core): improve delta_instance handler

* feat(*): use delta_instance derive handler

* feat(tactic/delta_instance): cleaner handling of application under binders

* Revert "feat(tactic/delta_instance): cleaner handling of application under binders"

This reverts commit 4005a2fad571bf922c98f94cbc1154666abc259d.

* comment apply_under_pis

* properly get unused name

* feat(tactic/delta_instance): run with high priority and don't run on inductives

* Update src/tactic/core.lean

Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>

### [2019-10-01T07:53:40+00:00](https://github.com/leanprover-community/mathlib/commit/800dba4f5935bccf357ca5a63f007cf7b0f97f59)
chore(linear_map): use curly brackets for type class in linear_map coe_to_fun ([#1493](https://github.com/leanprover-community/mathlib/pull/#1493))

* chore(linear_map): use curly brackets for type class in linear_map coe_to_fun

*  fix

### [2019-09-30T14:17:53+00:00](https://github.com/leanprover-community/mathlib/commit/374c290ea4139cf7f39bb7674efb905115041358)
chore(linear_algebra): continue removing decidable_eq assumptions ([#1404](https://github.com/leanprover-community/mathlib/pull/#1404))

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

### [2019-09-30T08:55:58+00:00](https://github.com/leanprover-community/mathlib/commit/c6fab42c36f65ff95a9043aa7aa6fb9bc4b4708c)
feat(ring_theory/power_series): order ([#1292](https://github.com/leanprover-community/mathlib/pull/#1292))

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

### [2019-09-28T22:44:16+00:00](https://github.com/leanprover-community/mathlib/commit/30aa8d2f76ad856c407938cd9a2dec878495f1ad)
chore(order/basic): rename `monotone_comp` to `monotone.comp`, reorder arguments ([#1497](https://github.com/leanprover-community/mathlib/pull/#1497))

### [2019-09-27T22:59:45+00:00](https://github.com/leanprover-community/mathlib/commit/708faa9f3dba94a57e26ebd27a87cc6cd77a4d06)
feat(geometry/manifold/manifold): define manifolds ([#1422](https://github.com/leanprover-community/mathlib/pull/#1422))

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

### [2019-09-27T18:10:21+00:00](https://github.com/leanprover-community/mathlib/commit/e0c204ef90a47d38f2390667546ea8a89d773c35)
chore(algebra/group_power): move inv_one from group_power to field ([#1495](https://github.com/leanprover-community/mathlib/pull/#1495))

* chore(algebra/group_power): move inv_one from group_power to field

*  fix

### [2019-09-27T16:05:10+00:00](https://github.com/leanprover-community/mathlib/commit/74f09d0def762e0badefade08cf9511a05d7656f)
chore(algebra/char_p): remove some decidable_eq assumptions ([#1492](https://github.com/leanprover-community/mathlib/pull/#1492))

* chore(algebra/char_p): remove some decidable_eq assumptions

*  fix build

### [2019-09-27T14:10:25+00:00](https://github.com/leanprover-community/mathlib/commit/ce7c94fcd478468ddb468658828d126145f816a4)
feat(reduce_projections): add reduce_projections attribute ([#1402](https://github.com/leanprover-community/mathlib/pull/#1402))

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

### [2019-09-27T11:47:32+00:00](https://github.com/leanprover-community/mathlib/commit/efd5ab2dc980ea9e4b7e58a7c4c90c926b538c13)
feat(logic/function): define `function.involutive` ([#1474](https://github.com/leanprover-community/mathlib/pull/#1474))

* feat(logic/function): define `function.involutive`

* Prove that `inv`, `neg`, and `complex.conj` are involutive.

* Move `inv_inv'` to `algebra/field`

### [2019-09-27T09:36:44+00:00](https://github.com/leanprover-community/mathlib/commit/6a79f8a1998046960d93522d205de50a1799bb97)
feat(data/int/basic): to_nat lemmas ([#1479](https://github.com/leanprover-community/mathlib/pull/#1479))

* feat(data/int/basic): of_nat lemmas

* Adding lt_of_to_nat_lt

* reversing sides of <->

### [2019-09-27T07:02:36+00:00](https://github.com/leanprover-community/mathlib/commit/0bc5de530b0ad8fd2451fd474e0c8a53bf772e1a)
chore(*): drop some unused args reported by `#sanity_check_mathlib` ([#1490](https://github.com/leanprover-community/mathlib/pull/#1490))

* Drop some unused arguments

* Drop more unused arguments

* Move `round` to the bottom of `algebra/archimedean`

Suggested by @rwbarton

### [2019-09-26T20:42:25+00:00](https://github.com/leanprover-community/mathlib/commit/15ed0392706afd6e9870694a8f1ee2b2047066a8)
fix(scripts/mk_all): ignore hidden files ([#1488](https://github.com/leanprover-community/mathlib/pull/#1488))

* fix(scripts/mk_all): ignore hidden files

Emacs sometimes creates temporary files with names like `.#name.lean`.

* Fix comment

Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>

### [2019-09-26T13:55:55+00:00](https://github.com/leanprover-community/mathlib/commit/3cd334161808c7dd59148634cade6d660f206565)
feat(field_theory/minimal_polynomial): Basics on minimal polynomials ([#1449](https://github.com/leanprover-community/mathlib/pull/#1449))

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

### [2019-09-26T12:04:21+00:00](https://github.com/leanprover-community/mathlib/commit/f92e81247fd80359b5362088435d0e9587389ab7)
feat(data/setoid): create file about setoids ([#1453](https://github.com/leanprover-community/mathlib/pull/#1453))

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

### [2019-09-26T07:39:54+00:00](https://github.com/leanprover-community/mathlib/commit/7afdab63b0044ecda31b75eedf38befb9fcf5a20)
refactor(data/equiv/algebra): rewrite `ring_equiv` using bundled homs ([#1482](https://github.com/leanprover-community/mathlib/pull/#1482))

* refactor(data/equiv/algebra): rewrite `ring_equiv` using bundled homs

Fix some compile errors

* Fix compile, add missing docs

* Docstrings

* Use less `ring_equiv.to_equiv` outside of `data/equiv/algebra`

* Join lines

### [2019-09-26T00:29:27+00:00](https://github.com/leanprover-community/mathlib/commit/2e35a7aaa548010a35c5fe6b766aaa9151cc74d7)
feat(int/basic): add simp-lemma int.of_nat_eq_coe ([#1486](https://github.com/leanprover-community/mathlib/pull/#1486))

* feat(int/basic): add simp-lemma int.of_nat_eq_coe

* fix errors

in the process also add some lemmas about bxor to simplify proofs

* use coercion in rat.mk

### [2019-09-25T18:11:13+00:00](https://github.com/leanprover-community/mathlib/commit/b39040ff04e89ef76fde405bfeba923d10c5eb49)
feat(sanity_check): improvements  ([#1487](https://github.com/leanprover-community/mathlib/pull/#1487))

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

### [2019-09-25T04:39:17+00:00](https://github.com/leanprover-community/mathlib/commit/3e5dc889730320f3bc785dbf6764b985fbb16ff7)
chore(scripts): add executable bit to scripts/mk_all.sh, and create/delete sanity_check_mathlib.lean ([#1480](https://github.com/leanprover-community/mathlib/pull/#1480))

* chore(scripts): add executable bit to scripts/mk_all.sh

* another

* modify mk_all/rm_all to create a file containing #sanity_check_mathlib

* add sanity_check_mathlib.lean to .gitignore

* Update scripts/mk_all.sh

* Update scripts/mk_all.sh

Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-09-25T01:30:42+00:00](https://github.com/leanprover-community/mathlib/commit/491a68ea8cc8a18997a4b02c8502e2b34d8b17e7)
cleanup(*): use priority 10 for low priority ([#1485](https://github.com/leanprover-community/mathlib/pull/#1485))

Now we can locally use priorities lower than this low-priority

### [2019-09-24T15:16:11+00:00](https://github.com/leanprover-community/mathlib/commit/00d440a9c2b2bb5dc8bfe12aa6706774291d2c4b)
feat(tactic/import_private): make private definitions available outside of their scope ([#1450](https://github.com/leanprover-community/mathlib/pull/#1450))

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

### [2019-09-24T13:36:31+00:00](https://github.com/leanprover-community/mathlib/commit/1eaa292891dc120eaf5b861cb741423599ae5fd4)
feat(finset): add has_sep instance ([#1477](https://github.com/leanprover-community/mathlib/pull/#1477))

### [2019-09-24T08:39:19+00:00](https://github.com/leanprover-community/mathlib/commit/5344da4cd0bab75fd4d37ad3d8972ee13b26763d)
feat(algebra/big_operators): simp lemmas ([#1471](https://github.com/leanprover-community/mathlib/pull/#1471))

* feat(algebra/big_operators): simp lemmas

* remove @[simp]

### [2019-09-24T08:13:37+00:00](https://github.com/leanprover-community/mathlib/commit/201174d0f7c7c54e8ae1f33a4af4031f3576b7b5)
feat(algebra/continued_fractions): add basic defs/lemmas for continued fractions ([#1433](https://github.com/leanprover-community/mathlib/pull/#1433))

* feat(algebra/continued_fractions): add basic defs/lemmas for continued fractions

* Rename termiantes_at to terminated_at, use long names for cont. fracts.

* Fix indentation, remove subfolders, fix docstrings

### [2019-09-24T05:46:35+00:00](https://github.com/leanprover-community/mathlib/commit/327098b4cbab65889513da31587aecdbf709a476)
feat(tactic/library_search): a more powerful library_search ([#1470](https://github.com/leanprover-community/mathlib/pull/#1470))

* experimental extensions to library_search

* upgrades to library_search

* remove ! for a later PR

* move `run_norm_num`

* oops

* Update src/tactic/library_search.lean

Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>

* remove run_norm_num for later

### [2019-09-24T03:51:35+00:00](https://github.com/leanprover-community/mathlib/commit/88f37b510ab5847450c468a23c29868a710fd8f3)
fix(tactic.lift): fix error messages ([#1478](https://github.com/leanprover-community/mathlib/pull/#1478))

### [2019-09-24T00:00:49+00:00](https://github.com/leanprover-community/mathlib/commit/425644f8a3ceb38feda1de17a7b2f61a26d66d99)
refactor(algebra/*): Make `monoid_hom.ext` etc use `∀ x, f x = g x` as an assumption ([#1476](https://github.com/leanprover-community/mathlib/pull/#1476))

### [2019-09-23T22:04:22+00:00](https://github.com/leanprover-community/mathlib/commit/604699b14123e1e9ad93eb48340c31c327d9e70a)
feat(data|set_theory): various new lemmas ([#1466](https://github.com/leanprover-community/mathlib/pull/#1466))

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

### [2019-09-23T19:57:18+00:00](https://github.com/leanprover-community/mathlib/commit/fd7840ad63c15ae1703f99eb3c07da4d80b3876a)
feat(topology/constructions): is_open_prod_iff' ([#1454](https://github.com/leanprover-community/mathlib/pull/#1454))

* feat(topology/constructions): open_prod_iff'

* reviewer's comments

* fix build

* golfed; is_open_map_fst

### [2019-09-23T17:36:28+00:00](https://github.com/leanprover-community/mathlib/commit/87d1240feaee5a23a0023e391655f0e107c38caf)
feat(tactic/core): derive handler for simple instances ([#1475](https://github.com/leanprover-community/mathlib/pull/#1475))

* feat(tactic/core): derive handler for simple algebraic instances

* change comment

* use mk_definition

* Update src/tactic/core.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-09-22T04:34:09+00:00](https://github.com/leanprover-community/mathlib/commit/61ccaf65c4cfc9c6ff103463342e034347eb8b89)
chore(*): fix various issues reported by `sanity_check_mathlib` ([#1469](https://github.com/leanprover-community/mathlib/pull/#1469))

* chore(*): fix various issues reported by `sanity_check_mathlib`

* Drop a misleading comment, fix the proof

### [2019-09-21T06:12:35+00:00](https://github.com/leanprover-community/mathlib/commit/65bf45c96a9c152d1508376a6a335d638869f32e)
fix(category_theory/finite_limits): fix definition, and construct from finite products and equalizers ([#1427](https://github.com/leanprover-community/mathlib/pull/#1427))

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

### [2019-09-21T00:47:17+00:00](https://github.com/leanprover-community/mathlib/commit/9c89fa56ed17a94d8c33fe0c2f4f00a6952d81b3)
feat(tactic/interactive): add fconstructor ([#1467](https://github.com/leanprover-community/mathlib/pull/#1467))

### [2019-09-20T11:08:05+00:00](https://github.com/leanprover-community/mathlib/commit/708a28cc763383522c5c5808aaf27b433d6e4283)
chore(algebra/group/units): use `def to_units` instead of `has_lift` ([#1431](https://github.com/leanprover-community/mathlib/pull/#1431))

* chore(algebra/group/units): use `def to_units` instead of `has_lift`

* Move, upgrade to `mul_equiv`, add documentation

### [2019-09-20T03:28:58+00:00](https://github.com/leanprover-community/mathlib/commit/bfe9c6c16b699238dac814fb292fdb0f2ed6374e)
chore(data/pfun): run `#sanity_check` ([#1463](https://github.com/leanprover-community/mathlib/pull/#1463))

### [2019-09-19T15:32:04+00:00](https://github.com/leanprover-community/mathlib/commit/ce105fdaa73448625ee17d200d9203865b417632)
chore(algebra/group): rename `as_monoid_hom` into `monoid_hom.of`, define `ring_hom.of` ([#1443](https://github.com/leanprover-community/mathlib/pull/#1443))

* chore(algebra/group): rename `as_monoid_hom` into `monoid_hom.of`

This is similar to `Mon.of` etc.

* Fix compile

* Docs, missing universe

* Move variables declaration up as suggested by @jcommelin

* doc-string

### [2019-09-19T13:17:33+00:00](https://github.com/leanprover-community/mathlib/commit/d91028355b806fae83e8a0db227a685652f1bba8)
chore(category_theory/endomorphism): make `map_End` and `map_Aut` use bundled homs ([#1461](https://github.com/leanprover-community/mathlib/pull/#1461))

* Migrate `functor.map_End` and `functor.map_Aut` to bundled homs

Adjust implicit arguments of `iso.ext`

* Add docstrings

### [2019-09-19T13:21:35+02:00](https://github.com/leanprover-community/mathlib/commit/1b8285e1bd2e701a1f06cd6fb0dca67175e406f1)
chore(readme): Add new maintainers [ci skip]

### [2019-09-19T02:38:18+00:00](https://github.com/leanprover-community/mathlib/commit/b11f0f149dbb73a3c978293a4cdeb3f01227b98f)
refactor(category_theory): refactor concrete categories ([#1380](https://github.com/leanprover-community/mathlib/pull/#1380))

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

* update post [#1412](https://github.com/leanprover-community/mathlib/pull/#1412)

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

### [2019-09-18T17:59:44+00:00](https://github.com/leanprover-community/mathlib/commit/066d0535747721600e54bd9c81e0ceda222cbae3)
chore(topology/maps): a few tweaks to open_embedding and closed embeddings ([#1459](https://github.com/leanprover-community/mathlib/pull/#1459))

* chore(topology/maps): a few tweaks to open_embedding and closed
embeddings

aligning them with recent modification to embedding. From the perfectoid
project.

* chore(topology/maps): add missing empty line

### [2019-09-18T15:46:57+00:00](https://github.com/leanprover-community/mathlib/commit/08390f5459a966d0d5266cd631e2689bc966b2d4)
refactor(algebra/big_operators,data/finset): use `finset.disjoint` in definitions ([#1456](https://github.com/leanprover-community/mathlib/pull/#1456))

* Use `finset.disjoint` in `algebra/big_operators`

* New lemma `disjoint_filter`

It should be a painless step from using `filter_inter_filter_neg_eq`
to using this lemma

* Update other dependencies of finset.prod_union and finset.prod_bind

* Reformat some lines to make them fit within 100 characters

* We can actually do away with two non-terminal `simp`s now

### [2019-09-18T15:43:01+02:00](https://github.com/leanprover-community/mathlib/commit/b51978df49b72a5caa70a7525e95bc332162efee)
chore(data/mllist): Typo in author name [ci skip] ([#1458](https://github.com/leanprover-community/mathlib/pull/#1458))

### [2019-09-18T15:40:20+02:00](https://github.com/leanprover-community/mathlib/commit/874a15a19cc39590b5e388d6d4127719a8e7df5e)
Update lattice.lean ([#1457](https://github.com/leanprover-community/mathlib/pull/#1457))

### [2019-09-17T18:02:24+00:00](https://github.com/leanprover-community/mathlib/commit/b41277c70937d8cd46639bbef674e656e8e397dd)
feat(set_theory/game): the theory of combinatorial games ([#1274](https://github.com/leanprover-community/mathlib/pull/#1274))

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

### [2019-09-17T15:50:00+00:00](https://github.com/leanprover-community/mathlib/commit/19a246c4f18fe33c6b387e5902b88b026863f996)
fix(category_theory): require morphisms are in Type, again ([#1412](https://github.com/leanprover-community/mathlib/pull/#1412))

* chore(category_theory): require morphisms live in Type

* move back to Type

* fixes

### [2019-09-17T05:06:09+00:00](https://github.com/leanprover-community/mathlib/commit/ab2c546dd6f446d7f22a7e593fb49b7ed8f791ae)
feat(data/quot): define `quotient.map` and `quotient.map₂` (dep: 1441) ([#1442](https://github.com/leanprover-community/mathlib/pull/#1442))

* chore(algebra/group,logic/relator): review some explicit/implicit arguments

* ring_hom.ext too

* feat(data/quot): define `quotient.map` and `quotient.map₂`

* Add comments

* Fix a typo

Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-09-17T02:44:20+00:00](https://github.com/leanprover-community/mathlib/commit/d4cc1790d8eeadd6ea0f97ef13d0464bc5a2ad11)
feat(logic/basic): eq_iff_eq_cancel ([#1447](https://github.com/leanprover-community/mathlib/pull/#1447))

* feat(logic/basic): eq_iff_eq_cancel

These lemmas or not meant for `rw` but to be applied, as a sort of congruence lemma.

* State lemmas as iff

* Make'm simp

### [2019-09-17T00:58:35+00:00](https://github.com/leanprover-community/mathlib/commit/c412527218f140f887e15188fd5ef1d4329ddaf3)
feat(data/list/sort): ordered_insert lemmas ([#1437](https://github.com/leanprover-community/mathlib/pull/#1437))

* feat(data/list/sort): ordered_insert lemmas

* add a lemma about L.tail.count

### [2019-09-16T23:07:50+00:00](https://github.com/leanprover-community/mathlib/commit/dd0ff1c44dbf04bfae81538eb2dc88f0c850265b)
feat(data/nat/basic): dvd_add_self_{left,right} ([#1448](https://github.com/leanprover-community/mathlib/pull/#1448))

* feat(data/nat/basic): dvd_add_self_{left,right}

Two simp-lemmas of the form
```lean
@[simp] protected lemma dvd_add_self_left {m n : ℕ} :
  m ∣ m + n ↔ m ∣ n :=
dvd_add_right (dvd_refl m)
```

* Oops, lemmas were protected

* Provide version for rings

### [2019-09-16T22:49:24+00:00](https://github.com/leanprover-community/mathlib/commit/929c1869f4c61389707165cec2d8b55f2d2f255a)
fix(docs/tutorial/category_theory): fix import ([#1440](https://github.com/leanprover-community/mathlib/pull/#1440))

* fix(docs/tutorial/category_theory): fix import

* fix(.travis.yml): Travis stages to build docs/

* cache docs/ in travis build

### [2019-09-16T21:07:29+00:00](https://github.com/leanprover-community/mathlib/commit/a3ccc7ac167cf6a257ab5b1f23b5cb51736fb6d9)
chore(category_theory/notation): update notation for prod and coprod ([#1413](https://github.com/leanprover-community/mathlib/pull/#1413))

* updating notation for categorical prod and coprod

* update notation

### [2019-09-16T16:01:04+02:00](https://github.com/leanprover-community/mathlib/commit/b2b0de46f7a12c2e5ec17cbebb35cbe82cc6020f)
feat(algebra/group/basic): mul_left_eq_self etc ([#1446](https://github.com/leanprover-community/mathlib/pull/#1446))

Simp-lemmas for groups of the form a * b = b ↔ a = 1.

### [2019-09-16T09:26:53+00:00](https://github.com/leanprover-community/mathlib/commit/d7f0e68647c407d96654fbed1d29328f6bf1821d)
chore(algebra/group,logic/relator): review some explicit/implicit args ([#1441](https://github.com/leanprover-community/mathlib/pull/#1441))

* chore(algebra/group,logic/relator): review some explicit/implicit arguments

* ring_hom.ext too

### [2019-09-14T05:00:40+00:00](https://github.com/leanprover-community/mathlib/commit/81a31ca4a8c0287bf0b0ce40f1a0df16543b7abe)
chore(data/*): flipping inequalities ([#1436](https://github.com/leanprover-community/mathlib/pull/#1436))

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

### [2019-09-13T07:38:04+00:00](https://github.com/leanprover-community/mathlib/commit/e3234f0494c366bbe1f25ba859189a2a9c75f010)
feat(algebra/ring): add coercions from →+* to →* and →+ ([#1435](https://github.com/leanprover-community/mathlib/pull/#1435))

* feat(algebra/ring): add coercions from →+* to →* and →+

* two lemmas simplifying casts

* add squash_cast attributes

### [2019-09-11T23:51:16+00:00](https://github.com/leanprover-community/mathlib/commit/590fb89608bcbd237abec565f5248372095042b7)
chore(category_theory/functor_category): improve comment warning about hcomp_assoc [ci skip] ([#1434](https://github.com/leanprover-community/mathlib/pull/#1434))

* expanding comment

* no scare quotes

### [2019-09-11T17:42:41+00:00](https://github.com/leanprover-community/mathlib/commit/140a606a461aa066927ba3a2d8e5c3976a2f7367)
feat(well_founded_tactics):  patch default_dec_tac ([#1419](https://github.com/leanprover-community/mathlib/pull/#1419))

* let simp flip inequalities

* feat(well_founded_tactics):  patch default_dec_tac

* Keeley's suggested syntax, and adding to the docs

* more

* add docs

### [2019-09-11T12:46:21+00:00](https://github.com/leanprover-community/mathlib/commit/e27142aa4ad03371cd4c4bc2b498b79c183e4f1e)
chore(*): renaming files constructing category instances ([#1432](https://github.com/leanprover-community/mathlib/pull/#1432))

### [2019-09-11T03:52:18+00:00](https://github.com/leanprover-community/mathlib/commit/8a5156fced21fff56d2d7e660e63c430bacfad8e)
fix(algebra/*/colimits): avoid explicit `infer_instance` ([#1430](https://github.com/leanprover-community/mathlib/pull/#1430))

With an explicit universe level Lean can do it automatically.

### [2019-09-11T01:49:04+00:00](https://github.com/leanprover-community/mathlib/commit/45fe081f20e5866f9a6b47b354f7337fca6854f2)
feat(logic): make some decidability proofs [inline] ([#1393](https://github.com/leanprover-community/mathlib/pull/#1393))

* feat(logic): make some decidability proofs [inline]

* inline more decidability proofs

* test

* import logic.basic in test

### [2019-09-10T23:38:55+00:00](https://github.com/leanprover-community/mathlib/commit/8e46fa5a703a9cf833d4cb127bde5344181821d3)
chore(algebra/group/to_additive): map_namespace should make a meta constant ([#1409](https://github.com/leanprover-community/mathlib/pull/#1409))

* chore(algebra/group/to_additive): map_namespace should make a meta constance

`map_namespace` now produces a `meta constant` instead of a constant. This means that after importing `group_theory/coset` and typing `#print axioms`, `quotient_group._to_additive` is not in the list, since it is now a `meta constant`. This is a little bit neater, and it doesn't look like we're adding any axioms.

* Update to_additive.lean

* Update to_additive.lean

### [2019-09-10T22:44:22+00:00](https://github.com/leanprover-community/mathlib/commit/e2f904ece0cfa688adabb1f3f9884e0ce947fef5)
feat(tactic/auto_cases): run auto_cases on false and psigma ([#1428](https://github.com/leanprover-community/mathlib/pull/#1428))

### [2019-09-10T19:55:17+00:00](https://github.com/leanprover-community/mathlib/commit/c87ec0e4a94fbcc2d648c6fa34c4499c10bfc61e)
feat(tactic/{abel,ring}): state conditions of tactics more precisely ([#1423](https://github.com/leanprover-community/mathlib/pull/#1423))

### [2019-09-10T15:33:29+00:00](https://github.com/leanprover-community/mathlib/commit/2dd6398edf1118750f5d79e51100da8c34cb2e46)
let simp flip inequalities ([#1418](https://github.com/leanprover-community/mathlib/pull/#1418))

### [2019-09-10T11:26:37+00:00](https://github.com/leanprover-community/mathlib/commit/0935e8bf3bf22ae435c95cdd48c7bd8bf84a285e)
feat(algebra/group/units): add some lemmas about `divp` ([#1388](https://github.com/leanprover-community/mathlib/pull/#1388))

* feat(algebra/group/units): add some lemmas about `divp`

* Rename lemmas, add new ones

### [2019-09-10T09:32:30+00:00](https://github.com/leanprover-community/mathlib/commit/fe1575a0362362d8a49ddb28be2325f1bc526c31)
chore(topology): sanity_check pass ([#1416](https://github.com/leanprover-community/mathlib/pull/#1416))

* chore(topology): sanity_check pass

* improvement

* avoid _inst_3 to recover instance

### [2019-09-10T01:55:13+00:00](https://github.com/leanprover-community/mathlib/commit/72d6325a83f3d613527dc7f0acd43a13871bd2f0)
feat(sanity_check): greatly improve performance ([#1389](https://github.com/leanprover-community/mathlib/pull/#1389))

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

### [2019-09-09T21:11:13+00:00](https://github.com/leanprover-community/mathlib/commit/228d5bad9648b5c8d44d99abd77a6ad9930da6bd)
feat(algebra/big_operators): sum_eq_zero_iff_of_nonpos ([#1424](https://github.com/leanprover-community/mathlib/pull/#1424))

* feat(algebra/big_operators): sum_eq_zero_iff_of_nonpos

* more order_dual instances

### [2019-09-08T16:37:05+00:00](https://github.com/leanprover-community/mathlib/commit/313fe11b10c8c7f000307d28cd85dc27dfef581c)
feat(algebra/floor): Split floor from archimedean file. ([#1372](https://github.com/leanprover-community/mathlib/pull/#1372))

* feat(algebra/floor): Split floor from archimedean file.

* feat({algebra,rat}/floor): move lemmas/defs from rat.floor to algebra.floor

### [2019-09-08T12:00:15+00:00](https://github.com/leanprover-community/mathlib/commit/37b67460310c3e14c5ad84bbf1a156616f712211)
feat(data/list/basic): make chain.nil a simp lemma ([#1414](https://github.com/leanprover-community/mathlib/pull/#1414))

### [2019-09-08T08:47:37+00:00](https://github.com/leanprover-community/mathlib/commit/6f7224ccbfe95ca901a994761a74c89e09b81917)
feat(data/list/defs): move list.sum to list/defs.lean ([#1415](https://github.com/leanprover-community/mathlib/pull/#1415))

* feat(data/list/defs): move list.sum to list/defs.lean

* add comment

### [2019-09-08T06:22:25+00:00](https://github.com/leanprover-community/mathlib/commit/8bdb14743360c2db61d07edb20addb2fe9a58d63)
feat(topology/local_homeomorph): local homeomorphisms ([#1398](https://github.com/leanprover-community/mathlib/pull/#1398))

* feat(topology/local_homeomorph): local homeomorphisms

* local_homeomorph: reviewer comments

### [2019-09-07T05:32:33+00:00](https://github.com/leanprover-community/mathlib/commit/10cb0d125d1d02d0ea68e478456c522bd1920d29)
feat(topology/constructions): distributivity of products over sums ([#1059](https://github.com/leanprover-community/mathlib/pull/#1059))

* feat(topology/constructions): distributivity of products over sums

* Update src/topology/maps.lean

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* Reverse direction of sigma_prod_distrib

### [2019-09-07T05:17:43+00:00](https://github.com/leanprover-community/mathlib/commit/d6a0ac58faf20695b18ba22ab909b0d01b2fcea6)
refactor(category_theory/limits/shapes/pullbacks): proof golf ([#1407](https://github.com/leanprover-community/mathlib/pull/#1407))

* refactor(category_theory/limits): make is_[co]limit not a class

* refactor(category_theory/limits/shapes/pullbacks): proof golf

### [2019-09-07T05:00:00+00:00](https://github.com/leanprover-community/mathlib/commit/8eab714fb1fe988431f18b569dca5c232ec6b2fd)
refactor(category_theory/limits): make is_[co]limit not a class ([#1405](https://github.com/leanprover-community/mathlib/pull/#1405))

### [2019-09-06T22:20:07+02:00](https://github.com/leanprover-community/mathlib/commit/a7f268b8be24b1b87423dba63e2ca386f8308f54)
fix(category_theory/limits/shapes): doc typo [ci skip] ([#1406](https://github.com/leanprover-community/mathlib/pull/#1406))

### [2019-09-06T12:45:57+02:00](https://github.com/leanprover-community/mathlib/commit/a5fa162b273dd02eb8ba2edaa40ae46feb3f7b8b)
chore(data/mv_polynomial): use classical logic ([#1391](https://github.com/leanprover-community/mathlib/pull/#1391))

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

### [2019-09-05T21:37:18+00:00](https://github.com/leanprover-community/mathlib/commit/1a0ed8099383cca33ac18947b4faabac6925ee21)
fix(naming): typo [ci skip] ([#1401](https://github.com/leanprover-community/mathlib/pull/#1401))

* fix(naming): typo [ci skip]

* more typos

### [2019-09-05T11:03:20+00:00](https://github.com/leanprover-community/mathlib/commit/b1920f599efe036cefbd02916aba9f687793c8c8)
chore(algebra/ordered_field): add simp attributes to inv_pos' and others ([#1400](https://github.com/leanprover-community/mathlib/pull/#1400))

### [2019-09-05T09:22:42+00:00](https://github.com/leanprover-community/mathlib/commit/7f20843077613e600892a4b08545f778da51ad0c)
chore(order/filter): rephrase filter.has_le ([#1399](https://github.com/leanprover-community/mathlib/pull/#1399))

The goal of this tiny refactor is to prevent `filter.sets` leaking when
proving a filter g is finer than another one f. We want the goal to be
`s ∈ f → s ∈ g` instead of the definitionaly equivalent
`s ∈ f.sets ∈ g.sets`

### [2019-09-05T02:48:09+00:00](https://github.com/leanprover-community/mathlib/commit/285490946d7c48134dd2fb0ff06eed0d92750749)
feat(bounded_lattice/has_lt): add a `lt` relation independent from `l… ([#1366](https://github.com/leanprover-community/mathlib/pull/#1366))

* feat(bounded_lattice/has_lt): add a `lt` relation independent from `le` for `has_top`

* use priority 10 instead of 0

### [2019-09-05T00:46:57+00:00](https://github.com/leanprover-community/mathlib/commit/62928251a248a81894ab6b347d8aa1c4c8053d3c)
feat(data/equiv/local_equiv): define local equivalences  ([#1359](https://github.com/leanprover-community/mathlib/pull/#1359))

* feat(data/equiv/local_equiv): define local equivalences

* add doc

* add extensionality attribute

* sanity_check

### [2019-09-04T22:48:55+00:00](https://github.com/leanprover-community/mathlib/commit/79a1f841d7ae056499f27db6d2d19ffb448543ac)
fix(tactic/norm_num): bugfix bad proof application ([#1387](https://github.com/leanprover-community/mathlib/pull/#1387))

* fix(tactic/norm_num): bugfix bad proof application

* add test case that used to fail

* add try_for

* fix typecheck test

* increase test timeout

### [2019-09-04T20:52:45+00:00](https://github.com/leanprover-community/mathlib/commit/3c224f0c83b21780a9ae036ee60090b920839a03)
feat (logic/basic): exists_eq' ([#1397](https://github.com/leanprover-community/mathlib/pull/#1397))

Not a great name, but `exists_eq_left` and `exists_eq_right` are taken, and it's unlikely to be used except in `simp`

### [2019-09-04T19:28:57+00:00](https://github.com/leanprover-community/mathlib/commit/65ffb7b1208518aa0b9b7c589a217ce649ee69b9)
fix(topology/uniform_space): simplify continuity proof ([#1396](https://github.com/leanprover-community/mathlib/pull/#1396))

### [2019-09-04T17:22:01+00:00](https://github.com/leanprover-community/mathlib/commit/06cffebfd33e035f1c90a5eaf4109907a37b775d)
feat(order): add lemma ([#1375](https://github.com/leanprover-community/mathlib/pull/#1375))

### [2019-09-04T12:59:55+00:00](https://github.com/leanprover-community/mathlib/commit/5d59e8bd23cb76ec7b90af20d96e12fe433164e2)
feat(category_theory): finite products give a monoidal structure ([#1340](https://github.com/leanprover-community/mathlib/pull/#1340))

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

### [2019-09-04T12:27:02+00:00](https://github.com/leanprover-community/mathlib/commit/8cd16b97eed0290f0472ed1ade0d2104c37ac7f3)
feat(category_theory/sums): sums (disjoint unions) of categories ([#1357](https://github.com/leanprover-community/mathlib/pull/#1357))

* feat(category_theory/sum): direct sums of categories

* minor

* tidying

* Fix white space, remove old comments

* rearranging, associator

* add TODO comment about unitors

* fix import

* create /basic.lean files

### [2019-09-04T06:33:49+00:00](https://github.com/leanprover-community/mathlib/commit/b079298d81d1595757440b8ddd4c7ebb4e063a3e)
feat(tactic/doc_blame): Use is_auto_generated ([#1395](https://github.com/leanprover-community/mathlib/pull/#1395))

### [2019-09-03T21:08:11+00:00](https://github.com/leanprover-community/mathlib/commit/ff47fa316366c9ce236342d4f951ce9e30f59865)
feat(measure_theory): prove that the Giry monad is a monad in the category_theory sense ([#1259](https://github.com/leanprover-community/mathlib/pull/#1259))

* feat(measure_theory): prove that the Giry monad is a monad in the category_theory sense

* Add spaces to fix alignment

* document Measure

* Add documentation

* Add space before colon

### [2019-09-03T18:22:38+00:00](https://github.com/leanprover-community/mathlib/commit/b5b40c749f2f581778e5d72907eca1aa663962b1)
chore(*): use localized command in mathlib ([#1319](https://github.com/leanprover-community/mathlib/pull/#1319))

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

### [2019-09-03T17:52:30+00:00](https://github.com/leanprover-community/mathlib/commit/4b6fcd90690817ca07cc728f77c98ef02095d759)
perf(data/gaussian_int): speed up div and mod ([#1394](https://github.com/leanprover-community/mathlib/pull/#1394))

avoid using `int.cast`, and use `rat.of_int`.

This sped up `#eval (⟨1414,152⟩ : gaussian_int) % ⟨123,456⟩` from about 5 seconds to 2 milliseconds

### [2019-09-03T17:20:07+00:00](https://github.com/leanprover-community/mathlib/commit/974d413b269d17d00a29db24135a5e79daa17e77)
chore(linear_algebra/determinant): simplify det_mul proof ([#1392](https://github.com/leanprover-community/mathlib/pull/#1392))

* chore(linear_algebra/determinant): simplify det_mul proof

Minor improvement to the proof of `det_mul`

* make det_mul_aux more readable

### [2019-09-03T15:36:36+00:00](https://github.com/leanprover-community/mathlib/commit/3a58b50f2a9babe95f9390596855f0fc13682999)
feat(data/equiv/basic): add more functions for equivalences between complex types ([#1384](https://github.com/leanprover-community/mathlib/pull/#1384))

* Add more `equiv` combinators

* Fix compile

* Minor fixes

* Update src/data/equiv/basic.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

### [2019-09-03T13:42:57+00:00](https://github.com/leanprover-community/mathlib/commit/a199f856a8edf9db718d2b4b7af55c8ab1a0987b)
feat(topology/uniform_space): Abstract completions ([#1374](https://github.com/leanprover-community/mathlib/pull/#1374))

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

### [2019-09-03T11:51:43+00:00](https://github.com/leanprover-community/mathlib/commit/c7d36292c6b9234dc40143c16288932ae38fdc12)
fix(restate_axiom): create lemmas from lemmas ([#1390](https://github.com/leanprover-community/mathlib/pull/#1390))

### [2019-09-03T09:24:11+02:00](https://github.com/leanprover-community/mathlib/commit/94205c46aeeba744495e1e3da90d7beb748287c3)
feat(data/fintype): prove `card (subtype p) ≤ card α` ([#1383](https://github.com/leanprover-community/mathlib/pull/#1383))

* feat(data/fintype): prove `card (subtype p) ≤ card α`

* Add `cardinal.mk_le_of_subtype`

* Rename `mk_le_of_subtype` to `mk_subtype_le`, use it in `mk_set_le`

Earlier both `mk_subtype_le` and `mk_set_le` took `set α` as an
argument. Now `mk_subtype_le` takes `α → Prop`.

### [2019-09-02T14:19:49+00:00](https://github.com/leanprover-community/mathlib/commit/227b6821d64a494d3c49809b069149ef530608d4)
feat(category_theory): define `iso.conj` and friends ([#1381](https://github.com/leanprover-community/mathlib/pull/#1381))

* feat(category_theory): define `iso.conj` and friends

* Drop 2 `@[simp]` attributes

### [2019-09-02T12:18:38+00:00](https://github.com/leanprover-community/mathlib/commit/57d4b4117ad84864371ee7e33fd6cf0f20f8f216)
feat(category_theory/limits): construct limits from products and equalizers ([#1362](https://github.com/leanprover-community/mathlib/pull/#1362))

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

### [2019-09-02T07:54:36+00:00](https://github.com/leanprover-community/mathlib/commit/fe7695ba088cddc2649415291c91951aef56186f)
chore(data/nat/gcd): remove pointless parentheses ([#1386](https://github.com/leanprover-community/mathlib/pull/#1386))

### [2019-09-02T06:00:19+00:00](https://github.com/leanprover-community/mathlib/commit/d35dc135af7af22c5aec9fc2fae46ce7d6c945b9)
feat(data/nat/gcd): add simple lemmas ([#1382](https://github.com/leanprover-community/mathlib/pull/#1382))

* feat(data/nat/gcd): more simple lemmas

* Prove `iff` instead of one side implication

### [2019-09-01T11:29:41+00:00](https://github.com/leanprover-community/mathlib/commit/6d2b3ed82739ea1554b011d83fc0584f95a3b905)
chore(category_theory/notation): consistently use notation for functor.id ([#1378](https://github.com/leanprover-community/mathlib/pull/#1378))

* chore(category_theory/notation): consistently use notation for functor.id

* oops, overzealous search-and-replace

* more

* more

* more

### [2019-08-31T22:37:28+00:00](https://github.com/leanprover-community/mathlib/commit/df65dde5b7dc966691e19a9b3ec7009f37717523)
feat(data/option/basic): eq_some_iff_get_eq ([#1370](https://github.com/leanprover-community/mathlib/pull/#1370))

* feat(data/option/basic): eq_some_iff_get_eq

* Update basic.lean

### [2019-08-31T20:38:30+00:00](https://github.com/leanprover-community/mathlib/commit/72ce940c15861d1c55d6da98b03810a0d7667c9c)
feat(category_theory/limits/of_nat_iso): missing parts of the limits API ([#1355](https://github.com/leanprover-community/mathlib/pull/#1355))

* feat(category_theory/limits/of_nat_isp)

* Update src/category_theory/limits/limits.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/category_theory/limits/limits.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* use @[reassoc]

* fixing after rename

* fix renaming

### [2019-08-30T20:07:24+00:00](https://github.com/leanprover-community/mathlib/commit/455f060382ce502e4a8affd395ce6a929ceda5b2)
chore(unicode): improve arrows ([#1373](https://github.com/leanprover-community/mathlib/pull/#1373))

* chore(unicode): improve arrows

* grammar

Co-Authored-By: Johan Commelin <johan@commelin.net>

* moar

### [2019-08-30T13:16:52-04:00](https://github.com/leanprover-community/mathlib/commit/4c5c4dc72b7d6061ade5888b7568ca1dd6653f4f)
doc(contribute): add detailed instructions for cache-olean [skip ci] ([#1367](https://github.com/leanprover-community/mathlib/pull/#1367))

### [2019-08-30T16:13:59+00:00](https://github.com/leanprover-community/mathlib/commit/2db7fa45d0ecee7daef4464c4dee9442be518aba)
feat(sanity_check): improve sanity_check ([#1369](https://github.com/leanprover-community/mathlib/pull/#1369))

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

### [2019-08-30T11:48:46+00:00](https://github.com/leanprover-community/mathlib/commit/afe51c7630e68ca127f47665e506201b4c9aa622)
feat(category_theory/limits): special shapes ([#1339](https://github.com/leanprover-community/mathlib/pull/#1339))

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

### [2019-08-29T21:31:25+00:00](https://github.com/leanprover-community/mathlib/commit/1278efd6ddafe8b4c17e879a042ef160ca65f1f8)
Fix `tactic.exact` timeout in `apply'` ([#1371](https://github.com/leanprover-community/mathlib/pull/#1371))

Sometimes `tactic.exact` may timeout for no reason. See zulip discussion https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.60apply'.60timeout/near/174415043

### [2019-08-29T12:31:24+00:00](https://github.com/leanprover-community/mathlib/commit/1ff358588e56460fb856b2500832e4590fa1c596)
feat(analysis/calculus/times_cont_diff): adding a lemma ([#1358](https://github.com/leanprover-community/mathlib/pull/#1358))

* feat(analysis/calculus/times_cont_diff): adding a lemma

* doc

* change k to \bbk

### [2019-08-28T21:31:26+00:00](https://github.com/leanprover-community/mathlib/commit/3b195032c7fc7a378719c3dbb9ef7997cf002d99)
refactor(category_theory/single_obj): migrate to bundled morphisms ([#1330](https://github.com/leanprover-community/mathlib/pull/#1330))

* Define equivalence between `{ f // is_monoid_hom f }` and `monoid_hom`

* Migrate `single_obj` to bundled homomorphisms

Fix a bug in `to_End`: the old implementation used a wrong monoid
structure on `End`.

* Fix `Mon.hom_equiv_monoid_hom` as suggested by @jcommelin

### [2019-08-28T16:20:58+00:00](https://github.com/leanprover-community/mathlib/commit/d4c1c0f676af4b18ba87758f268a20c0532959f4)
fix(tactic.basic): add sanity_check import ([#1365](https://github.com/leanprover-community/mathlib/pull/#1365))

### [2019-08-28T10:14:09+00:00](https://github.com/leanprover-community/mathlib/commit/721d67a76bc7dd6d6f202712db1b2e4dd7671bf7)
fix(topology/uniform_space): sanity_check pass ([#1364](https://github.com/leanprover-community/mathlib/pull/#1364))

### [2019-08-28T09:17:30+00:00](https://github.com/leanprover-community/mathlib/commit/79dccba952baf0892254deab93a802d0ce164791)
refactor: change field notation from k to \bbk ([#1363](https://github.com/leanprover-community/mathlib/pull/#1363))

* refactor: change field notation from k to \bbK

* change \bbK to \bbk

### [2019-08-27T23:19:25+02:00](https://github.com/leanprover-community/mathlib/commit/45df75b3c9da159fe3192fa7f769dfbec0bd6bda)
fix(topology/algebra/uniform_group): tiny priority tweak

### [2019-08-26T17:11:07+00:00](https://github.com/leanprover-community/mathlib/commit/cc04ba7e5641d6c038d93d83dc163e2ae0d09709)
chore(algebra/ring): change semiring_hom to ring_hom ([#1361](https://github.com/leanprover-community/mathlib/pull/#1361))

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

### [2019-08-26T14:50:25+00:00](https://github.com/leanprover-community/mathlib/commit/914c572eb39f64476365f198fd8750719faaf8a3)
feat(data/rat): add lt, le, and eq def lemmas, move casts into rat to basic ([#1348](https://github.com/leanprover-community/mathlib/pull/#1348))

### [2019-08-26T08:13:13+00:00](https://github.com/leanprover-community/mathlib/commit/7bc18a84b3afec0b8add61dc28d2c328dc53c6d5)
feat(data/fin): coe_eq_val and coe_mk ([#1321](https://github.com/leanprover-community/mathlib/pull/#1321))

### [2019-08-23T12:07:10+02:00](https://github.com/leanprover-community/mathlib/commit/253a9f7d633ca38eaa165a909a4f19828567db85)
fix(docs/install): resize extensions icons for consistency [ci skip]

### [2019-08-23T12:00:49+02:00](https://github.com/leanprover-community/mathlib/commit/91a9b4bbefaccccc1a8652d76febd5f2e6645462)
doc(install/*): new VS-code icon [ci skip]

### [2019-08-23T08:45:41+00:00](https://github.com/leanprover-community/mathlib/commit/9a425726179608ee95ab0edbfca1d3a0572edbee)
feat(tactic/apply'): apply without unfolding type definitions ([#1234](https://github.com/leanprover-community/mathlib/pull/#1234))

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

### [2019-08-22T18:22:53+00:00](https://github.com/leanprover-community/mathlib/commit/f74cc70c5cc7d73365485b44ac22fc9d5d0b7112)
fix(tactic/tauto): use intro1 to deal with negations ([#1354](https://github.com/leanprover-community/mathlib/pull/#1354))

* fix(tactic/tauto): use intro1 to deal with negations

* test(tactic/tauto): add tests

### [2019-08-22T15:27:06+00:00](https://github.com/leanprover-community/mathlib/commit/40b09aabf7559fd5c075234433607d55d09e7976)
feat(*): small lemmas from the sensitivity formalization ([#1352](https://github.com/leanprover-community/mathlib/pull/#1352))

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

### [2019-08-22T10:31:24+00:00](https://github.com/leanprover-community/mathlib/commit/f442a41abe069d1d2b42b6cf6bf9dc051cbef43a)
docs(category/monad,bitraversable): add module docstrings [#1260](https://github.com/leanprover-community/mathlib/pull/#1260)  ([#1286](https://github.com/leanprover-community/mathlib/pull/#1286))

* docs(category/monad,bitraversable): add module docstrings

* more docs

* still more doc

* doc about traversable

### [2019-08-22T09:32:22+02:00](https://github.com/leanprover-community/mathlib/commit/a489719bb267658de7f73be49740f5256bc57999)
Rename Groupoid.lean to groupoid_category.lean ([#1353](https://github.com/leanprover-community/mathlib/pull/#1353))

This fixes a problem with `category_theory/groupoid` and `category_theory/Groupoid` having the same name except for the case of the first letter, which causes a problem on case insensitive file systems.

### [2019-08-21T19:35:06+00:00](https://github.com/leanprover-community/mathlib/commit/8de4273b698df2af494f937b0d947fe9f50084f1)
feat(category_theory/Groupoid): category of groupoids ([#1325](https://github.com/leanprover-community/mathlib/pull/#1325))

* feat(category_theory/Groupoid): category of groupoids

* fix comment

* more articles

### [2019-08-21T12:19:41+00:00](https://github.com/leanprover-community/mathlib/commit/35144f2763d799419e2a8bc103d7821021344eea)
feat(conv/conv): conv tactics for zooming/saving state ([#1351](https://github.com/leanprover-community/mathlib/pull/#1351))

* feat(conv/conv): conv tactics for zooming/saving state

* rob's doc fixes

* nicer docs

### [2019-08-21T11:04:30+00:00](https://github.com/leanprover-community/mathlib/commit/3f915fc594ef60b47f696b694f5fc3749044a36e)
feat(archive): add the cubing a cube proof ([#1343](https://github.com/leanprover-community/mathlib/pull/#1343))

* feat(archive): add the cubing a cube proof

* rename file

* add leanpkg configure to travis

### [2019-08-21T05:42:55+00:00](https://github.com/leanprover-community/mathlib/commit/c5128756d54f1f5207da88c6509647bbf1c57c2c)
refactor(*): rewrite `to_additive` attribute ([#1345](https://github.com/leanprover-community/mathlib/pull/#1345))

* chore(algebra/group/to_additive): auto add structure fields

* Snapshot

* Rewrite `@[to_additive]`

* Drop more explicit `name` arguments to `to_additive`

* Drop more explicit arguments to `to_additive`

* Map namespaces with `run_cmd to_additive.map_namespace`

* fix(`group_theory/perm/sign`): fix compile

* Fix handling of equational lemmas; fix warnings

* Use `list.mmap'`

### [2019-08-21T03:42:10+00:00](https://github.com/leanprover-community/mathlib/commit/733f616ff7d557f2946c5ae58ca020a1d803d69c)
chore(gitignore): ignore files generated by mk_all script ([#1328](https://github.com/leanprover-community/mathlib/pull/#1328))

### [2019-08-21T01:39:40+00:00](https://github.com/leanprover-community/mathlib/commit/807004988d27207cc7882d8d812b1377e4095ad9)
feat(tactic/lift): add lift tactic ([#1315](https://github.com/leanprover-community/mathlib/pull/#1315))

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

### [2019-08-20T23:38:53+00:00](https://github.com/leanprover-community/mathlib/commit/26a3e31de4ea6001e417bfec40c2e488d9518412)
chore(category_theory/monoidal): monoidal_category doesn't extend category ([#1338](https://github.com/leanprover-community/mathlib/pull/#1338))

* chore(category_theory/monoidal): monoidal_category doesn't extend category

* remove _aux file, simplifying

* make notations global, and add doc-strings

### [2019-08-20T21:37:32+00:00](https://github.com/leanprover-community/mathlib/commit/0dbe3a9495ffaafbc0de96328bc7610445813c92)
feat(algebra,equiv,logic): add various lemmas ([#1342](https://github.com/leanprover-community/mathlib/pull/#1342))

* add various lemmas

* add simp lemma

* fix simp

* rename to subtype_sigma_equiv

### [2019-08-20T15:42:54+00:00](https://github.com/leanprover-community/mathlib/commit/14024a3ea08504d50fa3588881b55d8566ecd890)
feat(linear_algebra/bilinear_form, linear_algebra/sesquilinear_form, ring_theory/maps): bilinear/sesquilinear forms ([#1300](https://github.com/leanprover-community/mathlib/pull/#1300))

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

### [2019-08-20T13:12:03+00:00](https://github.com/leanprover-community/mathlib/commit/6f747ec2cf19f15fb96c8dd72eae3fb3b49119e1)
feat(data/vector2): nth_map ([#1349](https://github.com/leanprover-community/mathlib/pull/#1349))

* feat(data/vector2): nth_map

* Update vector2.lean

* Update vector2.lean

### [2019-08-20T12:14:30+00:00](https://github.com/leanprover-community/mathlib/commit/87714320eadd3384ceaa20a22484c8be62c2c5f8)
doc(tactic/ring2): document parts of ring2 ([#1208](https://github.com/leanprover-community/mathlib/pull/#1208))

* doc(tactic/ring2): document parts of ring2

* feat(data/tree): refactor binary trees into their own module

* feat(tactic/ring2): resolve correct correctness

* chore(tactic/ring2): move copyright into comment

* doc(tactic/ring2): wording

### [2019-08-20T11:13:39+02:00](https://github.com/leanprover-community/mathlib/commit/f3eb8c2103db16a5cf945bb326eaa2e541d99629)
chore(data/matrix): simp attribute for transpose_tranpose ([#1350](https://github.com/leanprover-community/mathlib/pull/#1350))

### [2019-08-19T21:05:01+00:00](https://github.com/leanprover-community/mathlib/commit/5a309a3aa30fcec122a26f379f05b466ee46fc7a)
fix(category_theory/eq_to_hom): remove bad simp lemmas ([#1346](https://github.com/leanprover-community/mathlib/pull/#1346))

### [2019-08-19T19:01:37+00:00](https://github.com/leanprover-community/mathlib/commit/9eefd40e263279c2ccb4683f9bf974ac52c32f9c)
refactor(data/list/min_max): use with_top for maximum and define argmax ([#1320](https://github.com/leanprover-community/mathlib/pull/#1320))

* refactor(data/list/min_max): use option for maximum and define argmax

* prove minimum_singleton

* fix build

* use with_bot for maximum

* update comments

### [2019-08-19T17:09:44+00:00](https://github.com/leanprover-community/mathlib/commit/92fa24cfdc28539c402152372254c40303545cb4)
feat(data/fin): val simp lemmas ([#1347](https://github.com/leanprover-community/mathlib/pull/#1347))

* feat(data/fin): val simp lemmas

* Update fin.lean

### [2019-08-19T09:36:05-04:00](https://github.com/leanprover-community/mathlib/commit/6fbcc04afc39861237118ad201345d1c7114deae)
feat(tactic/reassoc_axiom): produce associativity-friendly lemmas in category theory ([#1341](https://github.com/leanprover-community/mathlib/pull/#1341))

### [2019-08-19T13:15:20+00:00](https://github.com/leanprover-community/mathlib/commit/8f09b0fb9fad59ccf4ab1076f021d64b5106f9d1)
fix(tactic/omega): simplify with mul_one and one_mul ([#1344](https://github.com/leanprover-community/mathlib/pull/#1344))

* Simplify multiplication by one

* Remove debug trace

* Fix integer version of omega

### [2019-08-19T11:20:20+00:00](https://github.com/leanprover-community/mathlib/commit/9c1718abf92b7e7bf0a5229a5ba1ab27d0ea5e66)
feat(tactic/obtain): make type argument optional ([#1327](https://github.com/leanprover-community/mathlib/pull/#1327))

* feat(tactic/obtain): make type argument optional

* fix(tactic/obtain): unnecessary steps

* feat(tactic/obtain): simplify cases

### [2019-08-18T19:43:51+00:00](https://github.com/leanprover-community/mathlib/commit/ab7d39b0c26f6c4ee6504122e03980898d0ec109)
feat(data/vector2): update_nth ([#1334](https://github.com/leanprover-community/mathlib/pull/#1334))

* feat(data/vector2): update_nth

* naming and docstrings

* remove double namespace fom vector.nth_mem

### [2019-08-17T20:50:04+00:00](https://github.com/leanprover-community/mathlib/commit/538d3f6fe150adc87513791ba534497fd2cc245c)
feat(data/vector2): to_list_map ([#1335](https://github.com/leanprover-community/mathlib/pull/#1335))

### [2019-08-17T18:55:40+00:00](https://github.com/leanprover-community/mathlib/commit/66fa499b6be8aaf143efbf5d36dfe5d24ec02459)
feat(data/list/basic): list.mem_insert_nth ([#1336](https://github.com/leanprover-community/mathlib/pull/#1336))

* feat(data/list/basic): list.mem_insert_nth

* Update src/data/list/basic.lean

Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>

### [2019-08-16T10:20:57+00:00](https://github.com/leanprover-community/mathlib/commit/a1dda1e9cefc23445fdf511f4a25a7c36447c8da)
feat(linear_algebra/matrix): linear maps are linearly equivalent to matrices ([#1310](https://github.com/leanprover-community/mathlib/pull/#1310))

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

### [2019-08-16T02:19:14+00:00](https://github.com/leanprover-community/mathlib/commit/2e76f36444942e98d2fa59bbbbe03ed739bd9e68)
feat(tactic/sanity_check): add #sanity_check command ([#1318](https://github.com/leanprover-community/mathlib/pull/#1318))

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

### [2019-08-16T00:19:33+00:00](https://github.com/leanprover-community/mathlib/commit/397c016905f4cc44a05ec3d6b78b399dfd581451)
feat(tactic/finish): parse ematch lemmas with `finish using ...` ([#1326](https://github.com/leanprover-community/mathlib/pull/#1326))

* feat(tactic/finish): parse ematch lemmas with `finish using ...`

Add test

Add documentation

* Add docstrings

* Formatting and docstrings

* Clean up test

* Add even more docstrings

clean up match expressions

Fix typo

### [2019-08-15T22:29:27+00:00](https://github.com/leanprover-community/mathlib/commit/2e90bed810a9bd95b7cf7baa9f4639e40b3f8d95)
feat(analysis/complex/exponential): prove that rpow is continuous ([#1306](https://github.com/leanprover-community/mathlib/pull/#1306))

* rpow is continuous

* Update exponential.lean

* Fix things

* Fix things

* Fix things

* Fix things

### [2019-08-15T20:26:47+00:00](https://github.com/leanprover-community/mathlib/commit/74c25a578114b0a7fdaeabf113ca065f8ebd85e3)
feat(*): lemmas needed for two projects ([#1294](https://github.com/leanprover-community/mathlib/pull/#1294))

* feat(multiplicity|enat): add facts needed for IMO 2019-4

* feat(*): various lemmas needed for the cubing a cube proof

* typo

* some cleanup

* fixes, add choose_two_right

* projections for associated.prime and irreducible

### [2019-08-15T18:18:27+00:00](https://github.com/leanprover-community/mathlib/commit/fa68342dd457e548f0f0b23f9e97fe296cc44c66)
feat(data/rat): move lemmas to right file, add nat cast lemmas, remove ([#1333](https://github.com/leanprover-community/mathlib/pull/#1333))

redundant lemma

### [2019-08-15T15:09:08+00:00](https://github.com/leanprover-community/mathlib/commit/73cc56c5bca59ad73c9698c6b7a9aaa5ab992352)
refactor(data/fintype): shorten proof of card_eq ([#1332](https://github.com/leanprover-community/mathlib/pull/#1332))

### [2019-08-15T11:27:01+00:00](https://github.com/leanprover-community/mathlib/commit/ebbbb76b6e4a689019fb24346b171e721f9a9d3d)
doc(contribute/style): remove outdated syntax [ci skip] ([#1329](https://github.com/leanprover-community/mathlib/pull/#1329))

* doc(contribute/style): remove outdated syntax [ci skip]

* doc(contribute/style): mistaken find/replace

### [2019-08-15T10:26:30+00:00](https://github.com/leanprover-community/mathlib/commit/3d512f79a6b3b811b86cd2643bf4c3c8c4672f91)
chore(category_theory/isomorphism): docstring, DRY, add some trivial lemmas ([#1309](https://github.com/leanprover-community/mathlib/pull/#1309))

- add module docstring;
- use `as_iso` more aggressively to avoid repeating proofs;
- add more trivial lemmas.

### [2019-08-15T05:08:24+00:00](https://github.com/leanprover-community/mathlib/commit/e48ad0dcfae91ad540308c3ec0c626598c52bbdf)
chore(*): migrate `units.map` to bundled homs ([#1331](https://github.com/leanprover-community/mathlib/pull/#1331))

### [2019-08-14T18:01:25+00:00](https://github.com/leanprover-community/mathlib/commit/02548ad65d12007a219f9d09e391c02580fce3c4)
fix(data/mllist): fix off-by-one bug in mllist.take ([#1298](https://github.com/leanprover-community/mathlib/pull/#1298))

* Update mllist.lean

Changed `n` to `n+1` in line 72. This fixes a bug in the `take` function for monadic lazy lists (mllist).

* add a test showing correct behaviour of take

### [2019-08-14T15:58:41+00:00](https://github.com/leanprover-community/mathlib/commit/0bc4a400d71c0c04a0e1c628712f372579db86af)
feat(data/pequiv): symm_single_apply ([#1324](https://github.com/leanprover-community/mathlib/pull/#1324))

### [2019-08-13T15:12:57+00:00](https://github.com/leanprover-community/mathlib/commit/2a131d9f2d8591b96dac040a78ce79abb112d763)
fix(.github): typo ([#1323](https://github.com/leanprover-community/mathlib/pull/#1323))

### [2019-08-13T15:19:45+02:00](https://github.com/leanprover-community/mathlib/commit/5796465f6c160059afdd60b472116a2fbb3611b7)
fix(algebra/ring): fix typo in docstring ([#1322](https://github.com/leanprover-community/mathlib/pull/#1322))

### [2019-08-12T17:42:15+00:00](https://github.com/leanprover-community/mathlib/commit/900c53ae6d5e3f8cc47953363479593e8debc4d8)
feat(scripts): add scripts to import all mathlib files ([#1281](https://github.com/leanprover-community/mathlib/pull/#1281))

* add scripts to import all mathlib files

mk_all makes a file all.lean in each subdirectory of src/, importing all files in that directory, including subdirectories
rm_all removes the files all.lean

* also delete all.olean files

* remove unnecessary maxdepth

* add comments, and generate comments

### [2019-08-12T17:59:16+02:00](https://github.com/leanprover-community/mathlib/commit/df1fb07ddfa4c3aee9a480cf57730c14498d4add)
doc(contribute): add link to doc requirements ([#1317](https://github.com/leanprover-community/mathlib/pull/#1317))

### [2019-08-12T15:28:09+00:00](https://github.com/leanprover-community/mathlib/commit/92a54240f7e21b12d65292418e78ec6d1493616b)
feat(data/fin): mem_find_iff ([#1307](https://github.com/leanprover-community/mathlib/pull/#1307))

* feat(data/fin): mem_find_iff

* add find_eq_some_iff ([#1308](https://github.com/leanprover-community/mathlib/pull/#1308))

### [2019-08-12T13:41:27+00:00](https://github.com/leanprover-community/mathlib/commit/f46b0dc6535dc2dddeb01c8cf92fc2bd45b1ef07)
feat(algebra/ordered_field): le_div_iff_of_neg ([#1311](https://github.com/leanprover-community/mathlib/pull/#1311))

* feat(algebra/ordered_field): le_div_iff_of_neg

* Update ordered_field.lean

* Update ordered_field.lean

* Update ordered_field.lean

* Update ordered_field.lean

### [2019-08-12T11:55:24+00:00](https://github.com/leanprover-community/mathlib/commit/3bd3dcd5ae55543f19769340ad64a45e3df001cc)
feat(data/option/basic): bind_eq_none' ([#1312](https://github.com/leanprover-community/mathlib/pull/#1312))

* feat(data/option/basic): bind_eq_none'

* Update basic.lean

* fix build and add simp

### [2019-08-12T10:14:40+00:00](https://github.com/leanprover-community/mathlib/commit/01cb33cbd078dbbec13edf37a97f083101a01bf2)
feat(algebra/ordered_ring): pos_of_mul_neg_left and similar ([#1313](https://github.com/leanprover-community/mathlib/pull/#1313))

### [2019-08-11T09:21:07+00:00](https://github.com/leanprover-community/mathlib/commit/37d4edab5a336aa52fb09c9ef7818e1b7394ceff)
Delete repeated item ([#1316](https://github.com/leanprover-community/mathlib/pull/#1316))

### [2019-08-10T04:04:40+00:00](https://github.com/leanprover-community/mathlib/commit/3aad7f1eaf1f29fd753a2e1b68bdf210cac69a5b)
feat(data/matrix/pequiv): partial equivalences to represent matrices ([#1228](https://github.com/leanprover-community/mathlib/pull/#1228))

* feat(matrix/pequiv): partial equivalences to represent matrices

* use notation for pequiv

* correct imports

* finish correcting imports

* add some docs

* Add documentation

* improve documentation

### [2019-08-09T09:57:38+00:00](https://github.com/leanprover-community/mathlib/commit/a79794ab98097754da437c75cd33a2f9b5836eff)
feat(archive): add archive ([#1295](https://github.com/leanprover-community/mathlib/pull/#1295))

* feat(archive): add archive

* reformulate sentence

### [2019-08-08T14:14:07+02:00](https://github.com/leanprover-community/mathlib/commit/dd4db5f48c578656d2aba418799ab2109d657a79)
fix(tactic/linarith): handle neq goals ([#1303](https://github.com/leanprover-community/mathlib/pull/#1303))

### [2019-08-08T02:35:57+00:00](https://github.com/leanprover-community/mathlib/commit/9c4dd9503fb0467df3ff41d18bf90e74efefbc0d)
feat (analysis/normed_space): Define real inner product space ([#1248](https://github.com/leanprover-community/mathlib/pull/#1248))

* Inner product space

* Change the definition of inner_product_space

The original definition introduces an instance loop.

See Zulip talks: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/ring.20tactic.20works.20at.20one.20place.2C.20fails.20at.20another

* Orthogonal Projection

Prove the existence of orthogonal projections onto complete subspaces in an inner product space.

* Fix names

* small fixes

### [2019-08-07T07:50:47+00:00](https://github.com/leanprover-community/mathlib/commit/a2a867e827c2a6702beb9efc2b9282bd801d5f9a)
feat(algebra/ring): bundled semiring homs ([#1305](https://github.com/leanprover-community/mathlib/pull/#1305))

* added bundled ring homs

* removed comment

* Tidy and making docstrings consistent

* fix spacing

* fix typo

Co-Authored-By: Johan Commelin <johan@commelin.net>

* fix typo

Co-Authored-By: Johan Commelin <johan@commelin.net>

* whoops, actually removing instances

### [2019-08-06T15:58:05+02:00](https://github.com/leanprover-community/mathlib/commit/57c1d6d74e365cb0be1ec148ea1c8ba75868c546)
chore(data/matrix): protect some lemmas ([#1304](https://github.com/leanprover-community/mathlib/pull/#1304))

### [2019-08-05T21:37:42+00:00](https://github.com/leanprover-community/mathlib/commit/88ad3cf59d905f8796f3fc954e1af9c8db14274a)
feat(tactic/push_neg): add optional name argument to contrapose ([#1302](https://github.com/leanprover-community/mathlib/pull/#1302))

### [2019-08-05T15:01:21+00:00](https://github.com/leanprover-community/mathlib/commit/de83205608860ade9719d81689e2254c9bb33394)
refactor(algebra/big_operators) delete duplicates and change names ([#1301](https://github.com/leanprover-community/mathlib/pull/#1301))

* refactor(algebra/big_operators) delete duplicates and change names

* fix build

### [2019-08-05T09:15:59+00:00](https://github.com/leanprover-community/mathlib/commit/fc56c852ff41784bdd6a7bbdf05e541cc5a53f3d)
feat(algebra/order_functions): abs_nonpos_iff ([#1299](https://github.com/leanprover-community/mathlib/pull/#1299))

* feat(algebra/ordered_group): abs_nonpos_iff

* Update ordered_group.lean

* move to order_functions

### [2019-08-04T04:21:08+00:00](https://github.com/leanprover-community/mathlib/commit/b46665fa5fea37d3b5cae84ec3847458f5e178b8)
chore(ring_theory/algebra): make first type argument explicit in alg_hom ([#1296](https://github.com/leanprover-community/mathlib/pull/#1296))

* chore(ring_theory/algebra): make first type argument explicit in alg_hom

Now this works, and it didn't work previously even with `@`
```lean
structure alg_equiv (α β γ : Type*) [comm_ring α] [ring β] [ring γ]
  [algebra α β] [algebra α γ] extends alg_hom α β γ :=
```

* Update algebra.lean

### [2019-08-03T04:14:56+00:00](https://github.com/leanprover-community/mathlib/commit/27d34b3160f61aaa4f7cdc6cc33ff37e4d479186)
feat(algebra/direct_limit): discrete_field ([#1293](https://github.com/leanprover-community/mathlib/pull/#1293))

### [2019-08-02T17:15:07+00:00](https://github.com/leanprover-community/mathlib/commit/8fe73f387594deb19b0815daed71ff186984cb20)
feat(data/fintype): psigma.fintype ([#1291](https://github.com/leanprover-community/mathlib/pull/#1291))

* feat(data/fintype): psigma.fintype

* Update fintype.lean

* Swap instance argument order

### [2019-08-02T15:14:38+00:00](https://github.com/leanprover-community/mathlib/commit/3af92bef09e1587102a1b325a6d548f865236d92)
feat(algebra/module): linear_map.coe_mk ([#1290](https://github.com/leanprover-community/mathlib/pull/#1290))

### [2019-08-02T14:52:18+00:00](https://github.com/leanprover-community/mathlib/commit/106123830974d84a3e7f6e8d7b432b70d6df9071)
feat(topology): category of uniform spaces ([#1275](https://github.com/leanprover-community/mathlib/pull/#1275))

* feat(category_theory): uniform spaces

* feat(topology/uniform_spaces): CpltSepUniformSpace is a reflective subcategory

### [2019-08-02T12:48:54+00:00](https://github.com/leanprover-community/mathlib/commit/5b4b208cb4917262bb319917b0006244989b590f)
feat(data/fintype): univ_unique ([#1289](https://github.com/leanprover-community/mathlib/pull/#1289))

### [2019-08-01T17:01:15+00:00](https://github.com/leanprover-community/mathlib/commit/766807f63e04043875b24f4e8fc69e9143832f11)
feat(data/rat): refactor into smaller files and add documentation ([#1284](https://github.com/leanprover-community/mathlib/pull/#1284))

### [2019-08-01T15:02:26+00:00](https://github.com/leanprover-community/mathlib/commit/0d66c875a99ee392d2a5f0483ce904cb665aedc1)
feat(data/seq): add ext proof, nats def, zip_with lemmas, and extract seq property ([#1278](https://github.com/leanprover-community/mathlib/pull/#1278))

### [2019-07-31T16:48:18+00:00](https://github.com/leanprover-community/mathlib/commit/49be50fbaf2fdab1a127b46688a2dfc80410fe8f)
doc(data/padics, data/real/cau_seq, algebra): add doc strings, remove unnecessary assumptions ([#1283](https://github.com/leanprover-community/mathlib/pull/#1283))

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

### [2019-07-31T14:37:08+00:00](https://github.com/leanprover-community/mathlib/commit/88d60dcf1bd63b29c0c82d9820be4006212bbb7c)
feat(data/pnat/basic): coe_bit0 and coe_bit1 ([#1288](https://github.com/leanprover-community/mathlib/pull/#1288))

### [2019-07-31T13:28:58+00:00](https://github.com/leanprover-community/mathlib/commit/53680f96c9dc8d41185ae961503097ba497cb33d)
feat(data/matrix): mul_sum and sum_mul ([#1253](https://github.com/leanprover-community/mathlib/pull/#1253))

* feat(data/matrix): mul_sum and sum_mul

* Update matrix.lean

* add comment explaing funny proof

### [2019-07-31T10:41:10+00:00](https://github.com/leanprover-community/mathlib/commit/da46b321746b828d5aba93b5ea73ab7f25cf1074)
feat(tactic/symmetry_at): apply symmetry on assumptions ([#1269](https://github.com/leanprover-community/mathlib/pull/#1269))

* feat(tactic/symmetry_at): apply symmetry on assumptions

* add docstrings

### [2019-07-31T08:37:56+00:00](https://github.com/leanprover-community/mathlib/commit/badeb48be0d20b977ae4a0c08df71ac0824a8b79)
feat(data/equiv/algebra): change mul_equiv field to map_mul ([#1287](https://github.com/leanprover-community/mathlib/pull/#1287))

* feat(data/equiv/algebra): bundle field for mul_equiv

* adding docs

* Update src/data/equiv/algebra.lean

* Update src/data/equiv/algebra.lean

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

### [2019-07-30T11:45:46+00:00](https://github.com/leanprover-community/mathlib/commit/9d589d7b3b6ad78143a78771f5e30a1018ac31fe)
feat(data/nat/fib): add Fibonacci sequence ([#1279](https://github.com/leanprover-community/mathlib/pull/#1279))

### [2019-07-30T06:58:24+00:00](https://github.com/leanprover-community/mathlib/commit/0b4767515e835e026c26bdd33a73be369de768af)
feat(algebra,data/complex/exponential): add abs_neg_one_pow, remove hyp from div_le_div_of_le_left ([#1280](https://github.com/leanprover-community/mathlib/pull/#1280))

### [2019-07-29T21:10:06+00:00](https://github.com/leanprover-community/mathlib/commit/132bc5677b17b6e4ea0f1c6fec5d4b2c6003a777)
doc(windows.md): clarify windows instructions ([#1165](https://github.com/leanprover-community/mathlib/pull/#1165))

* doc(windows.md): clarify windows instructions

* fix headers

* remove msys2 from windows installation instructions

* fix sentence

* typo

Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

* doc(windows.md): small changes

typos, and explicitly discourage msys2

### [2019-07-29T16:17:43+00:00](https://github.com/leanprover-community/mathlib/commit/363f1873b5569eb102210d6679a7970b0e4df10c)
feat(tactic/extract_goal): create stand-alone examples out of current goal ([#1233](https://github.com/leanprover-community/mathlib/pull/#1233))

* feat(tactic/extract_example): create stand-alone examples out of current goal

* feat(tactic/extract_example): add formatting and options

* feat(tactic/extract_goal): rename to `extract_goal`

* Update src/tactic/interactive.lean

Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

* make instances anonymous when the name starts with `_`

* add doc strings

* feat(tactic/interactive): exact_goal works on defs

### [2019-07-29T14:13:00+00:00](https://github.com/leanprover-community/mathlib/commit/ee15f68ee6cb49586f50a213722c88fc4e377918)
doc(category_theory): adding headers and basic comments to files without ([#1264](https://github.com/leanprover-community/mathlib/pull/#1264))

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

### [2019-07-29T11:22:47+00:00](https://github.com/leanprover-community/mathlib/commit/5adeebf1daf3ebe564436336034580a704e055ec)
feat(algebra/group/hom): bundled monoid and group homs ([#1271](https://github.com/leanprover-community/mathlib/pull/#1271))

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

### [2019-07-28T10:35:05+00:00](https://github.com/leanprover-community/mathlib/commit/879da1cf04c2baa9eaa7bd2472100bc0335e5c73)
fix(algebraic_geometry/presheafedspace): fix lame proofs ([#1273](https://github.com/leanprover-community/mathlib/pull/#1273))

* fix(algebraic_geometry/presheafedspace): fix lame proofs

* fix

* Update src/algebraic_geometry/presheafed_space.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-07-28T05:13:16+00:00](https://github.com/leanprover-community/mathlib/commit/9689f4d59769531f6b6f90fca4f455f52271c284)
feat(tactic/interactive): move `rotate` into interactive namespace ([#1272](https://github.com/leanprover-community/mathlib/pull/#1272))

also document `swap`

Add test

### [2019-07-25T14:09:56+02:00](https://github.com/leanprover-community/mathlib/commit/d5a539393efee6b3df2fc98b6bba0926ab0d1df4)
doc(contribute/index.md): add line about large PRs [ci skip] ([#1267](https://github.com/leanprover-community/mathlib/pull/#1267))

### [2019-07-25T10:40:50+00:00](https://github.com/leanprover-community/mathlib/commit/03c0d6c0d09fde0cb4b7e05987801277c8072e4c)
feat(algebra/group/basic): add_add_neg_cancel'_right ([#1261](https://github.com/leanprover-community/mathlib/pull/#1261))

* feat(algebra/group/basic): add_add_neg_cancel'_right

* fix build

### [2019-07-25T10:48:28+02:00](https://github.com/leanprover-community/mathlib/commit/926467dced189d9a8d7fc59dbd1b8c2217ba6e65)
doc(contribute/style.md): fix section on comments [ci skip] ([#1265](https://github.com/leanprover-community/mathlib/pull/#1265))

### [2019-07-25T08:45:56+00:00](https://github.com/leanprover-community/mathlib/commit/1000ae8d702b7a95b6f66f95b1450b6f2baac939)
doc(*): new documentation requirements ([#1229](https://github.com/leanprover-community/mathlib/pull/#1229))

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

### [2019-07-24T15:32:15+00:00](https://github.com/leanprover-community/mathlib/commit/5125f11a89c3c3a7dc6db599c59058cd3496e74b)
feat(data/matrix): smul_val ([#1262](https://github.com/leanprover-community/mathlib/pull/#1262))

* feat(data/matrix): smul_val

* Update src/data/matrix.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-07-24T11:03:46+00:00](https://github.com/leanprover-community/mathlib/commit/ed579163b849bc3723cc2e40e31dacddc746db6d)
feat(category_theory): functions to convert is_lawful_functor and is_… ([#1258](https://github.com/leanprover-community/mathlib/pull/#1258))

* feat(category_theory): functions to convert is_lawful_functor and is_lawful_monad to their corresponding category_theory concepts

* Fix typo

* feat(category): add mjoin_map_pure, mjoin_pure to the simpset (and use <$> notation)

### [2019-07-24T05:14:48+00:00](https://github.com/leanprover-community/mathlib/commit/b0c5251911da94f1d7b2c853b0335658d6a449b9)
cleanup(category_theory/monoidal): use equiv on prod/punit intead of adding new constants ([#1257](https://github.com/leanprover-community/mathlib/pull/#1257))

### [2019-07-23T11:10:07+00:00](https://github.com/leanprover-community/mathlib/commit/4a5529a2c91109d4c0118029d6a6486280a0e704)
feat(data/array): add some simp attributes ([#1255](https://github.com/leanprover-community/mathlib/pull/#1255))

### [2019-07-22T19:45:42+00:00](https://github.com/leanprover-community/mathlib/commit/a33315d594731876aa780bb12fc79b3e67198302)
feat(linear_algebra/dim): findim equivalence ([#1217](https://github.com/leanprover-community/mathlib/pull/#1217))

* feat(linear_algebra/dim): findim equivalence

* feat(linear_algebra/dim): two versions of dim_fun

* feat(linear_algebra/dim): clean up

### [2019-07-22T16:29:29+00:00](https://github.com/leanprover-community/mathlib/commit/3e77fec25f69f759ab91b752445b01b467149c72)
feat(linear_algebra/finite_dimensional): finite dimensional vector spaces ([#1241](https://github.com/leanprover-community/mathlib/pull/#1241))

* feat(linear_algebra/finite_dimensional): finite dimensional vector spaces

* rw `of_span_finite_eq_top` to `of_fg`

* prove infinite.nat_embedding

* generalize finite_of_linear_independent to noetherian modules

* fix build

* fix build (ring_theory/polynomial)

### [2019-07-22T11:20:31+00:00](https://github.com/leanprover-community/mathlib/commit/fd916604a36fcb3ab4300ad2e897816794ae66f2)
feat(data/power_series): Add multivariate power series and prove basic API ([#1244](https://github.com/leanprover-community/mathlib/pull/#1244))

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

### [2019-07-22T08:00:24+00:00](https://github.com/leanprover-community/mathlib/commit/7c09ed5eec8434176fbc493e0115555ccc4c8f99)
feat(category_theory/*): define `Cat` and a fully faithful functor `Mon ⥤ Cat` ([#1235](https://github.com/leanprover-community/mathlib/pull/#1235))

* feat(category_theory/*): define `Cat` and a fully faithful functor `Mon ⥤ Cat`

* Drop 2 commas

* Drop `functor.id_comp` etc, add `Cat.str` instance, adjust module-level comments

* Make `α` and `β` arguments of `map_hom_equiv` explicit

This way `e α β f` is automatically interpreted as `(e α β).to_fun f`.

### [2019-07-22T09:13:12+02:00](https://github.com/leanprover-community/mathlib/commit/b5a641e8aef27e400de14d4e7dff2264d66562f6)
chore(data/polynomial): clean up commented code ([#1251](https://github.com/leanprover-community/mathlib/pull/#1251))

Commented code that wasn't removed after a refactor.

### [2019-07-22T01:35:42+00:00](https://github.com/leanprover-community/mathlib/commit/f24dc98b70ed197e9edd16d9234350a42c60777b)
feat(logic/unique): forall_iff and exists_iff ([#1249](https://github.com/leanprover-community/mathlib/pull/#1249))

Maybe these should be `@[simp]`. My use case in `fin 1` and it's slightly annoying to have `default (fin 1)` everwhere instead of `0`, but maybe that should also be a `@[simp]` lemma.

### [2019-07-22T01:13:25+00:00](https://github.com/leanprover-community/mathlib/commit/a8c2923673b32605e6307f6a9330056bd97a0b56)
refactor(ring_theory/noetherian): change order of instance arguments ([#1250](https://github.com/leanprover-community/mathlib/pull/#1250))

Zulip discussion https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Type.20class.20failure

This change makes some type class searches work better.

### [2019-07-20T18:50:28+00:00](https://github.com/leanprover-community/mathlib/commit/93419b38843f2880934e11a7a43b88c28302fcd3)
chore(data/equiv/algebra): add `ring.to_mul/add_equiv`, DRY ([#1247](https://github.com/leanprover-community/mathlib/pull/#1247))

### [2019-07-20T17:33:46+00:00](https://github.com/leanprover-community/mathlib/commit/d371da685bdae353d43a6aed75d69ad33f733ec3)
fix(group_theory/subgroup): fix some typos introduced in 66a86ffe0 ([#1246](https://github.com/leanprover-community/mathlib/pull/#1246))

### [2019-07-20T06:49:37+00:00](https://github.com/leanprover-community/mathlib/commit/6e3516de7eb251a231421ac729cd91b21e1fb6ac)
feat(category_theory/monad): monadic adjunctions ([#1176](https://github.com/leanprover-community/mathlib/pull/#1176))

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

### [2019-07-19T17:09:12+00:00](https://github.com/leanprover-community/mathlib/commit/9505e5b33d73d2265fc8fa0527a378734c2888cc)
fix(data/matrix): use pi.module for the module structure ([#1242](https://github.com/leanprover-community/mathlib/pull/#1242))

* fix(data/matrix): use pi.module for the module structure

* Update matrix.lean

* Update matrix.lean

* Update matrix.lean

### [2019-07-19T14:39:27+00:00](https://github.com/leanprover-community/mathlib/commit/07ae80f4c97bec9e58aa5fd4b1dc37d0696dd257)
refactor(algebra/*): delete `free_monoid` from `algebra/free`, restore some functions in `algebra/group/with_one` ([#1227](https://github.com/leanprover-community/mathlib/pull/#1227))

* refactor(algebra/*): Remove `free_monoid` from `algebra/free`, fixes [#929](https://github.com/leanprover-community/mathlib/pull/#929)

* use `namespace with_one`

* Add `with_one.coe_is_mul_hom`

* Restore `with_one.lift` etc from `algebra/free` `free_monoid.lift` etc

* Define `with_one.map` based on the deleted `free_monoid.map`

Define using `option.map`, and prove equivalence to `λ f, lift $ coe ∘ f`.

### [2019-07-19T14:09:02+00:00](https://github.com/leanprover-community/mathlib/commit/74754acb77c1460f0c858dde76ead79948b93eb8)
feat(analysis/calculus/times_cont_diff): multiple differentiability ([#1226](https://github.com/leanprover-community/mathlib/pull/#1226))

* feat(analysis/calculus/times_cont_diff): multiple differentiability

* style

* style

* style and documentation

* better wording

### [2019-07-18T15:15:54+00:00](https://github.com/leanprover-community/mathlib/commit/8b102eb25d58ea48391231ac6a2a0ebe191cc02e)
feat(topology/algebra/group): define filter pointwise addition ([#1215](https://github.com/leanprover-community/mathlib/pull/#1215))

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

### [2019-07-18T06:27:03+00:00](https://github.com/leanprover-community/mathlib/commit/e704f9404d19580674dbaef16d3ea3122f656103)
fix(data/{nat,int}/parity): fix definition of 'even' ([#1240](https://github.com/leanprover-community/mathlib/pull/#1240))

### [2019-07-17T17:57:06+02:00](https://github.com/leanprover-community/mathlib/commit/86e728766f357865c02ecffdf35de67b4f747ab1)
fix(data/zmod/basic) remove unused argument from instance ([#1239](https://github.com/leanprover-community/mathlib/pull/#1239))

### [2019-07-17T09:56:01+00:00](https://github.com/leanprover-community/mathlib/commit/d6fd044cf4cbb0863825c16f35ce0f0acd5f91cd)
feat(*): add nat.antidiagonal and use it for polynomial.mul_coeff ([#1237](https://github.com/leanprover-community/mathlib/pull/#1237))

### [2019-07-16T22:00:41+00:00](https://github.com/leanprover-community/mathlib/commit/8785bd0fa6b31c7e573916c85c468f2d990322ce)
refactor(data/multiset): rename diagonal to antidiagonal ([#1236](https://github.com/leanprover-community/mathlib/pull/#1236))

* refactor(data/multiset): rename diagonal to antidiagonal

* Add docstrings

* fix build

* Fix build

### [2019-07-16T21:01:49+00:00](https://github.com/leanprover-community/mathlib/commit/e186fbb704eeb01b4fefb34e5ca1c90787ccfb24)
feat(data/mv_polynomial): coeff_mul ([#1216](https://github.com/leanprover-community/mathlib/pull/#1216))

* feat(data/mv_polynomial): coeff_mul

* refactor(data/multiset): rename diagonal to antidiagonal

* Rename diagonal to antidiagonal

* Define antidiagonal as to_finsupp instead of to_finset

* Add docstrings

* fix build

* Fix build

### [2019-07-15T21:35:36+00:00](https://github.com/leanprover-community/mathlib/commit/92ac50cbc5b4c08810bc1b1d2fafff31e70a0b3f)
chore(data/finset): rename le_min_of_mem to min_le_of_mem ([#1231](https://github.com/leanprover-community/mathlib/pull/#1231))

* chore(data/finset): rename le_min_of_mem to min_le_of_mem

* fix build

### [2019-07-15T14:48:52+00:00](https://github.com/leanprover-community/mathlib/commit/7217f1346670e0861976b4e91aa8e2ea3ff82187)
feat(data/option/basic): bind_eq_none ([#1232](https://github.com/leanprover-community/mathlib/pull/#1232))

* feat(data/option/basis): bind_eq_none

* delete extra line

### [2019-07-15T13:09:35+00:00](https://github.com/leanprover-community/mathlib/commit/46074fc14fcb02aa20ef64ed61f417579249d183)
chore(data/fintype): change `unique.fintype` to priority 0 ([#1230](https://github.com/leanprover-community/mathlib/pull/#1230))

### [2019-07-15T00:44:50+00:00](https://github.com/leanprover-community/mathlib/commit/0e9ac849fd8cd104856aa6150d1da0a8e2beeaf8)
feat(tactic/rcases): add obtain tactic ([#1218](https://github.com/leanprover-community/mathlib/pull/#1218))

* feat(tactic/rcases): add obtain tactic

* style(tactic/rcases): line break

* doc(docs/tactics): document obtain

* feat(tactic/obtain): support := syntax

### [2019-07-14T11:14:14+00:00](https://github.com/leanprover-community/mathlib/commit/dcf01308f55117360a8b263725ef5a0fc8153ecc)
feat(data/pequiv): partial equivalences ([#1206](https://github.com/leanprover-community/mathlib/pull/#1206))

* feat(data/pequiv): partial equivalences

* Update src/data/pequiv.lean

Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>

* use notation

### [2019-07-14T05:25:05+00:00](https://github.com/leanprover-community/mathlib/commit/03e6d0eae1c23f31d4478ad4bc7e54d66eb7b0fa)
chore(algebra/group/hom): add `is_monoid_hom.of_mul`, use it ([#1225](https://github.com/leanprover-community/mathlib/pull/#1225))

* Let `to_additive` generate `is_add_monoid_hom.map_add`

* Converting `is_mul_hom` into `is_monoid_hom` doesn't require `α` to be a group

* Simplify the proof of `is_add_group_hom.map_sub`

Avoid `simp` (without `only`)

### [2019-07-13T20:54:54+00:00](https://github.com/leanprover-community/mathlib/commit/51f26459dd028da896b8e0ba1f30a3ed2af27ff6)
feat(pformat): provide `trace!` and `fail!` and allow tactic values ([#1222](https://github.com/leanprover-community/mathlib/pull/#1222))

### [2019-07-13T18:17:06+00:00](https://github.com/leanprover-community/mathlib/commit/a1cfc5cc59804f0fd4b2b8cf7c178272f043a7b2)
feat(logic,data/equiv,prod): various lemmas ([#1224](https://github.com/leanprover-community/mathlib/pull/#1224))

* feat(logic,data/equiv,prod): various lemmas

* Update basic.lean

* Update basic.lean

### [2019-07-13T16:25:07+00:00](https://github.com/leanprover-community/mathlib/commit/0eea0d9fc53bd037da13abdf5d95a711cbd0c288)
feat(data/{nat,int}/parity): the 'even' predicate on nat and int ([#1219](https://github.com/leanprover-community/mathlib/pull/#1219))

* feat(data/{nat,int}/parity): the 'even' predicate on nat and int

* fix(data/{nat,int}/parity): shorten proof

* delete extra comma

### [2019-07-13T01:46:58+00:00](https://github.com/leanprover-community/mathlib/commit/6db582929bb18648bdfe3e38fa7c633b6949ba2c)
feat(data/finmap): extend the API ([#1223](https://github.com/leanprover-community/mathlib/pull/#1223))

### [2019-07-12T21:47:13+00:00](https://github.com/leanprover-community/mathlib/commit/5a48be3e29dacbb2f02071db4749dcdfa74fb79d)
chore(data/src/pending): remove unused folder ([#1221](https://github.com/leanprover-community/mathlib/pull/#1221))

### [2019-07-12T20:05:55+00:00](https://github.com/leanprover-community/mathlib/commit/fb7dfa162d93adc56a86214d06463c9444d8ea85)
feat(data/{nat,int,zmod,finset}): add a few useful facts ([#1220](https://github.com/leanprover-community/mathlib/pull/#1220))

* feat(data/finset): add a few useful facts

* feat(data/zmod/basic): express neg in terms of residues

* feat(data/{nat,int}): add theorem 'mod_mod_of_dvd'

### [2019-07-12T01:43:22+00:00](https://github.com/leanprover-community/mathlib/commit/3d36966eecba5d4846ee2536b43e575d2530510f)
feat(analysis/calculus/mean_value): the mean value inequality ([#1212](https://github.com/leanprover-community/mathlib/pull/#1212))

* feat(analysis/calculus/mean_value): the mean value inequality

* remove blank lines

### [2019-07-11T21:03:56+00:00](https://github.com/leanprover-community/mathlib/commit/7806586179e1053c94cf5eaabfa1ce2070c6794e)
feat(analysis/calculus/deriv): extended API for derivatives ([#1213](https://github.com/leanprover-community/mathlib/pull/#1213))

### [2019-07-11T18:24:16+00:00](https://github.com/leanprover-community/mathlib/commit/2511faf42541dbbfb6a52916a92dec2618acc440)
feat(tactic/localized): localized notation ([#1081](https://github.com/leanprover-community/mathlib/pull/#1081))

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

### [2019-07-11T13:58:17+00:00](https://github.com/leanprover-community/mathlib/commit/c2cc9a998ba9cc05c4d06206ff7f2cb32cddfa9f)
refactor(*): change priority of \simeq ([#1210](https://github.com/leanprover-community/mathlib/pull/#1210))

* change priority of \simeq

Also change priority of similar notations
Remove many unnecessary parentheses

* lower precedence on order_embedding and similar

also add parentheses in 1 place where they were needed

* spacing

* add parenthesis

### [2019-07-11T10:12:31+00:00](https://github.com/leanprover-community/mathlib/commit/86d0f29261ad4226f3e161c601e00145282671ad)
refactor(*): make `is_group_hom` extend `is_mul_hom` ([#1214](https://github.com/leanprover-community/mathlib/pull/#1214))

* map_mul/map_add: use explicit parameters

Preparing to merge `is_mul_hom` with `is_group_hom`

* make `is_group_hom` extend `is_mul_hom`, adjust many proof terms

* Add a comment

### [2019-07-11T07:41:05+00:00](https://github.com/leanprover-community/mathlib/commit/1b1c64b07612db6cef0f69a9e4120145e1a58724)
perf(algebraic_geometry/presheafed_space): replace/optimize tidy scripts ([#1204](https://github.com/leanprover-community/mathlib/pull/#1204))

* perf(algebraic_geometry/presheafed_space): replace/optimize tidy scripts

This file now takes 20 seconds to compile on my desktop instead of 160. This is a 9% speedup to mathlib overall.

* doc(algebraic_geometry/presheafed_space): comments

### [2019-07-11T04:18:40+00:00](https://github.com/leanprover-community/mathlib/commit/cc5870db6da4dcf4d0bfbd009fc98cc519ce7c48)
feat(algebra/ordered_ring): with_top.nat_induction ([#1211](https://github.com/leanprover-community/mathlib/pull/#1211))

### [2019-07-10T21:33:20+00:00](https://github.com/leanprover-community/mathlib/commit/5cdebb7578586496a57f7d37fd35b0a583267cbd)
feat(*): Miscellaneous lemmas in algebra ([#1188](https://github.com/leanprover-community/mathlib/pull/#1188))

* Trying things out

* feat(ring_theory/*): Misc little lemmas

* More little lemmas

### [2019-07-10T19:39:24+00:00](https://github.com/leanprover-community/mathlib/commit/5aebdc435b8e4c511475c547aaea1bc9ef8fb37a)
fix(*): fix line endings ([#1209](https://github.com/leanprover-community/mathlib/pull/#1209))

### [2019-07-10T18:25:32+00:00](https://github.com/leanprover-community/mathlib/commit/0bc4a50dd57b660ee366eb11689d845c1a36ca0d)
feat(tactic/apply_fun): adds `apply_fun` tactic ([#1184](https://github.com/leanprover-community/mathlib/pull/#1184))

* feat(tactic/apply_fun): adds `apply_fun` tactic

* move tests to test folder

* elaborate function with expected type

* fix merge mistake

### [2019-07-10T15:57:51+00:00](https://github.com/leanprover-community/mathlib/commit/d2b4380c4960f621fa239ef5f88f4963c941cf38)
feat(data/list/basic): list.prod_range_succ, list.sum_range_succ ([#1197](https://github.com/leanprover-community/mathlib/pull/#1197))

* feat(data/list/basic): list.prod_range_succ, list.sum_range_succ

* changes from review

* remove simp

* shorten proof

### [2019-07-10T11:22:33-04:00](https://github.com/leanprover-community/mathlib/commit/8939d9510ba7724af58bfd9ac835fa662230a118)
docs(contribute/index.md): [#1131](https://github.com/leanprover-community/mathlib/pull/#1131) [skip ci]

### [2019-07-10T09:10:06-04:00](https://github.com/leanprover-community/mathlib/commit/b00460c013fd9eb6166704594b1b204d8fd2fb46)
doc(README): Add link to website

### [2019-07-10T05:49:09+00:00](https://github.com/leanprover-community/mathlib/commit/fb1848bbbfce46152f58e219dc0712f3289d2b20)
refactor(topology/algebra/open_subgroup) Finish TODO ([#1202](https://github.com/leanprover-community/mathlib/pull/#1202))

* Create .DS_Store

* Revert "Create .DS_Store"

This reverts commit 5612886d493aef59205eddc5a34a75e6e5ba22c1.

* Finish TODO

* Update src/topology/algebra/open_subgroup.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-07-10T02:24:53+00:00](https://github.com/leanprover-community/mathlib/commit/e25a59704e56733ac0b7aee448d22106860f3a76)
feat(analysis/calculus/tangent_cone): more properties of the tangent cone ([#1136](https://github.com/leanprover-community/mathlib/pull/#1136))

### [2019-07-10T00:10:18+00:00](https://github.com/leanprover-community/mathlib/commit/0cd0d4edc14f0eee777d30c7378a1b393e42f65d)
feat(meta/pformat): format! macro using `pp` instead of `to_fmt` ([#1194](https://github.com/leanprover-community/mathlib/pull/#1194))

* feat(meta/pformat): format! macro which uses `pp` instead of `to_fmt`

* Update core.lean

### [2019-07-09T22:27:43+00:00](https://github.com/leanprover-community/mathlib/commit/60e4bb92a2d3f0ab6a2a9570a1234ec943fbe513)
refactor(category_theory/endomorphism): move to a dedicated file; prove simple lemmas ([#1195](https://github.com/leanprover-community/mathlib/pull/#1195))

* Move definitions of `End` and `Aut` to a dedicated file

* Adjust some proofs, use `namespace`, add docstrings

* `functor.map` and `functor.map_iso` define homomorphisms of `End/Aut`

* Define `functor.map_End` and `functor.map_Aut`

### [2019-07-09T20:34:02+00:00](https://github.com/leanprover-community/mathlib/commit/3a7c661af061224cf3539fbb52e7508c262b0d5e)
refactor(topology/*): define and use dense_inducing ([#1193](https://github.com/leanprover-community/mathlib/pull/#1193))

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

### [2019-07-09T15:55:54+00:00](https://github.com/leanprover-community/mathlib/commit/04608159e7bf9c7956ea74e0ad6affff32ca394b)
fix(docs/tactics): fix code block ([#1201](https://github.com/leanprover-community/mathlib/pull/#1201))

### [2019-07-09T15:04:11+00:00](https://github.com/leanprover-community/mathlib/commit/0099f0674625f4a45ca42d9bd7160e18c64f19ce)
perf(data/polynomial, field_theory/splitting_field): memory problems ([#1200](https://github.com/leanprover-community/mathlib/pull/#1200))

* perf(data/polynomial): avoid bad instance search

* perf(field_theory/splitting_field): local intance priority makes a big difference

### [2019-07-09T12:15:39+00:00](https://github.com/leanprover-community/mathlib/commit/13f76d336db3e377a179acbc9b4790b3f86b486b)
feat(tactic): add `convert_to` and `ac_change` ([#944](https://github.com/leanprover-community/mathlib/pull/#944))

* feat(tactic): add `convert_to` and `ac_change`

* style fixes

### [2019-07-09T13:05:07+02:00](https://github.com/leanprover-community/mathlib/commit/d50f63462d96bed96d90b947202b574c45b4b012)
feat(data/matrix): simp attributes on one_mul and mul_one ([#1199](https://github.com/leanprover-community/mathlib/pull/#1199))

### [2019-07-09T11:06:35+02:00](https://github.com/leanprover-community/mathlib/commit/6670e661a2604a6e86b780588af3af5fab8904ba)
feat(data/matrix): simp attributes on zero_mul and mul_zero ([#1198](https://github.com/leanprover-community/mathlib/pull/#1198))

### [2019-07-09T09:00:44+00:00](https://github.com/leanprover-community/mathlib/commit/9071969894a231c839f5c275b94b8125abaa94ce)
feat(data/nat/basic): some nat inequalities ([#1189](https://github.com/leanprover-community/mathlib/pull/#1189))

* feat(data/nat/basic): some inequalities

* remove redundant lemmas

* simplify proofs

* make implicit

* shorter proof

* rename

### [2019-07-08T20:51:06-04:00](https://github.com/leanprover-community/mathlib/commit/7fc3283ed1b14c2650e698f738f9ce20d093150f)
fix(README.md): Remove the AppVeyor badge [skip ci] ([#1192](https://github.com/leanprover-community/mathlib/pull/#1192))

It seems to me that we don't really care about whether the AppVeyor build fails or not. And I don't like the red badge. So I propose to remove it.

### [2019-07-09T00:20:18+02:00](https://github.com/leanprover-community/mathlib/commit/0cc67a1addb9bdec74e4d89ff928592d86e6981b)
chore(data/matrix): remove unnecessary decidable_eq ([#1196](https://github.com/leanprover-community/mathlib/pull/#1196))

This was generating annoying `decidable_eq (fin n)` goals when rewriting.

### [2019-07-07T20:48:20+00:00](https://github.com/leanprover-community/mathlib/commit/891741916b847859290d21e19ba9b9abf4b6f6ba)
chore(data/equiv/algebra): use `to_additive` ([#1191](https://github.com/leanprover-community/mathlib/pull/#1191))

- Define `add_equiv` and `add_equiv.*` using `to_additive`
- Simplify some instances

### [2019-07-06T22:30:41+00:00](https://github.com/leanprover-community/mathlib/commit/55b0b80bb61222c6efdcd1923659f7f72b447790)
fix(src/logic/basic): add [symm] attribute to ne. ([#1190](https://github.com/leanprover-community/mathlib/pull/#1190))

### [2019-07-06T11:29:31+00:00](https://github.com/leanprover-community/mathlib/commit/ccf5636fa753dffdf97e9edf840dd65774c5ca8d)
feat(data/option/basic): not_is_some_iff_eq_none and ne_none_iff_is_some ([#1186](https://github.com/leanprover-community/mathlib/pull/#1186))

### [2019-07-05T20:30:47+00:00](https://github.com/leanprover-community/mathlib/commit/12763b9e23161d6a50e94b869a05898f350a8251)
chore(algebra/group/type_tags): add some missing instances ([#1164](https://github.com/leanprover-community/mathlib/pull/#1164))

* chore(algebra/group/type_tags): add some missing instances

* Drop an unused import

### [2019-07-05T17:03:44+00:00](https://github.com/leanprover-community/mathlib/commit/05283d26acee9c882e1cd929643739bcde123926)
fix(category_theory/limits): make is_limit a class, clean up proofs ([#1187](https://github.com/leanprover-community/mathlib/pull/#1187))

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

### [2019-07-05T15:44:22+00:00](https://github.com/leanprover-community/mathlib/commit/05550eac85177ae1a3af894eac096cb2458552fe)
feat(category_theory/limits): equivalences create limits ([#1175](https://github.com/leanprover-community/mathlib/pull/#1175))

* feat(category_theory/limits): equivalences create limits

* equivalence lemma

* add @[simp]

* use right_adjoint_preserves_limits

* undo weird changes in topology files

* formatting

* do colimits too

### [2019-07-05T05:31:07+00:00](https://github.com/leanprover-community/mathlib/commit/27ae77cd99f146d4ea38ecace79b724428315ff7)
feat(tactic/tidy): lower the priority of ext in tidy ([#1178](https://github.com/leanprover-community/mathlib/pull/#1178))

* feat(category_theory/adjunction): additional simp lemmas

* experimenting with deferring ext in tidy

* abbreviate some proofs

* refactoring CommRing/adjunctions

* renaming

### [2019-07-05T05:02:40+00:00](https://github.com/leanprover-community/mathlib/commit/4af39760b860e0ee2725dc20247c69156dc3eed2)
chore(category_theory): cleanup ([#1173](https://github.com/leanprover-community/mathlib/pull/#1173))

* chore(category_theory): cleanup

* oops

* remove comment

* more uniform?

* fix stalks proof?

* Update src/algebra/CommRing/basic.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Apply suggestions from code review

Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-07-04T19:49:02+00:00](https://github.com/leanprover-community/mathlib/commit/569bcf9940470ac45da7756e348ff2935c8c51e7)
feat(algebra/ordered_group): eq_of_abs_non_pos ([#1185](https://github.com/leanprover-community/mathlib/pull/#1185))

* feat(algebra/ordered_group): decidable_linear_ordered_comm_group.eq_of_abs_non_pos

* fix(algebra/ordered_group): new line and name

### [2019-07-04T18:17:29+00:00](https://github.com/leanprover-community/mathlib/commit/c5d414018ce651d8a1f35165e473cfc428a2ae58)
feat(data/fin): fin.mk.inj_iff ([#1182](https://github.com/leanprover-community/mathlib/pull/#1182))

Quite surprised this insn't already there.

### [2019-07-04T16:47:39+00:00](https://github.com/leanprover-community/mathlib/commit/1723beef4bb08bbf8f4665b9bd900a1da7f9ecb4)
chore(algebra/order_functions): some proofs work for semirings ([#1183](https://github.com/leanprover-community/mathlib/pull/#1183))

* chore(algebra/order_functions): some proofs work for semirings, not only rings

* Update order_functions.lean

### [2019-07-04T14:31:11+00:00](https://github.com/leanprover-community/mathlib/commit/0818bb2a88837b71b3197be2343cc5e104a9dd8e)
feat(data/fin): mem_find_of_unique ([#1181](https://github.com/leanprover-community/mathlib/pull/#1181))

### [2019-07-04T12:14:42+00:00](https://github.com/leanprover-community/mathlib/commit/32ce1213919050664fadb371436a421046f9b9f6)
chore(topology/maps.lean): Delete a redundant argument ([#1179](https://github.com/leanprover-community/mathlib/pull/#1179))

* Create .DS_Store

* Revert "Create .DS_Store"

This reverts commit 5612886d493aef59205eddc5a34a75e6e5ba22c1.

* Redundant argument

### [2019-07-04T10:24:53+00:00](https://github.com/leanprover-community/mathlib/commit/34d69b5054549f6cc2de9a6311be5cba9c595977)
chore(data/set): set.mem_preimage_eq becomes an iff  ([#1174](https://github.com/leanprover-community/mathlib/pull/#1174))

* chore(data/set): set.mem_preimage_eq becomes an iff named set.mem_preimage

* fix(measure_theory/measurable_space): proof broken by mem_preimage
change

* fix(data/filter/basic)

* fix(topology/uniform_space/separation)

* fix(measure_theory/integration)

### [2019-07-04T08:45:49+00:00](https://github.com/leanprover-community/mathlib/commit/6493bb6eddcb4a811893353b06ac23a3463ef567)
feat(data/list/basic): nodup_update_nth, mem_diff_iff_of_nodup ([#1170](https://github.com/leanprover-community/mathlib/pull/#1170))

### [2019-07-04T06:57:24+00:00](https://github.com/leanprover-community/mathlib/commit/00de1cbb69d633ab77f306d84effaaf0ada9c2b3)
feat(data/list/basic): list.nodup_diff ([#1168](https://github.com/leanprover-community/mathlib/pull/#1168))

* feat(data/list/basic): list.nodup_diff

* Update basic.lean

* Update basic.lean

### [2019-07-04T05:16:33+00:00](https://github.com/leanprover-community/mathlib/commit/e6b9696a633f5058016886d9683df711be7e90ed)
feat(data/option): not_mem_none and bind_assoc ([#1177](https://github.com/leanprover-community/mathlib/pull/#1177))

### [2019-07-04T03:33:42+00:00](https://github.com/leanprover-community/mathlib/commit/4cca114acd1d82ea90bf69cd275e1067d67c9951)
feat(data/fin): fin.find ([#1167](https://github.com/leanprover-community/mathlib/pull/#1167))

* feat(data/fin): fin.find

* add nat_find_mem_find

### [2019-07-04T01:39:56+00:00](https://github.com/leanprover-community/mathlib/commit/3ee1f8578539992445d10fd41a36b7e5e32c2065)
feat(order/basic): order_dual.inhabited ([#1163](https://github.com/leanprover-community/mathlib/pull/#1163))

### [2019-07-03T23:52:50+00:00](https://github.com/leanprover-community/mathlib/commit/ae9615c84bd34c149bd242dfcea1982412bd78e3)
feat(order/pilex): lexicographic ordering on pi types ([#1157](https://github.com/leanprover-community/mathlib/pull/#1157))

* feat(order/pilex): lexicographic ordering on pi types

* fix instance name

* fix instance name properly

* Update basic.lean

* remove unnecessary import

### [2019-07-03T22:09:24+00:00](https://github.com/leanprover-community/mathlib/commit/992354c2f539de5b2d0ad7235b2ea4f4afc053c5)
feat(data/fintype): well_foundedness lemmas on fintypes ([#1156](https://github.com/leanprover-community/mathlib/pull/#1156))

* feat(data/fintype): well_foundedness lemmas on fintypes

* Update fintype.lean

* minor fixes

### [2019-07-03T18:10:52+00:00](https://github.com/leanprover-community/mathlib/commit/cb84234516d90d847ee730332aeaad5fa50786c4)
feat(category_theory/yoneda): coyoneda lemmas ([#1172](https://github.com/leanprover-community/mathlib/pull/#1172))

* feat(category_theory/yoneda): coyoneda lemmas

* oops, didn't include everything I needed

* oops

* removing fully_faithful

* missing underscore...

### [2019-07-03T15:25:41+00:00](https://github.com/leanprover-community/mathlib/commit/e4ee18b8729d8571bb894173615880a61616f9c4)
feat(category_theory/adjunction): additional simp lemmas ([#1143](https://github.com/leanprover-community/mathlib/pull/#1143))

* feat(category_theory/adjunction): additional simp lemmas

* spaces

Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-07-03T12:44:32+00:00](https://github.com/leanprover-community/mathlib/commit/f1b54734e38b8eb6ba349e211bfb82c8502cd3fd)
feat(data/list/basic): fin_range ([#1159](https://github.com/leanprover-community/mathlib/pull/#1159))

* feat(data/list/basic): fin_range

fin_range is like `list.range` but returns a `list (fin n)` instead of a `list nat`

* Update basic.lean

### [2019-07-03T09:42:00+00:00](https://github.com/leanprover-community/mathlib/commit/d2c5309d0bc66bdf813b4510dfe0a1d7523cad0a)
refactor(linear_algebra/lc): use families not sets ([#943](https://github.com/leanprover-community/mathlib/pull/#943))

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

### [2019-07-03T09:02:02+00:00](https://github.com/leanprover-community/mathlib/commit/9a338853ba8ed8bd0b627b8563cab0f36024813e)
chore(data/matrix): rows and columns the right way around ([#1171](https://github.com/leanprover-community/mathlib/pull/#1171))

* chore(data/matrix): rows and columns the right way around

* update matrix.lean

### [2019-07-03T00:58:19+00:00](https://github.com/leanprover-community/mathlib/commit/fd5617c11aeddbfe0fafdedd9e90d1de1f4a9dcc)
feat(measure_theory): Define Bochner integration ([#1149](https://github.com/leanprover-community/mathlib/pull/#1149))

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

### [2019-07-02T13:11:09+00:00](https://github.com/leanprover-community/mathlib/commit/1ef2c2df20cf45c21675d855436228c7ae02d47a)
feat(data/list/basic): filter_true and filter_false ([#1169](https://github.com/leanprover-community/mathlib/pull/#1169))

* feat(data/list/basic): filter_true and filter_false

* Update basic.lean

* Update basic.lean

* Update basic.lean

* Update basic.lean

### [2019-07-02T11:28:23+00:00](https://github.com/leanprover-community/mathlib/commit/b4989a04e68a09d759bad55d5a610825ec081214)
compute the cardinality of real ([#1096](https://github.com/leanprover-community/mathlib/pull/#1096))

* compute the cardinality of real

* minor improvements

* fix(data/rat/denumerable): change namespace of of_rat

* style(src/topology/algebra/infinite_sum): structure proof

### [2019-07-02T04:29:06+00:00](https://github.com/leanprover-community/mathlib/commit/57b57b38b406157762a671061ad887f53510e8b8)
feat(data/equiv/basic): improve arrow_congr, define conj ([#1119](https://github.com/leanprover-community/mathlib/pull/#1119))

* feat(data/equiv/basic): improve arrow_congr, define conj

- redefine `equiv.arrow_congr` without an enclosing `match`
- prove some trivial lemmas about `equiv.arrow_congr`
- define `equiv.conj`, and prove trivial lemmas about it

* chore(data/equiv/basic): add @[simp]

Also split some long lines, and swap lhs with rhs in a few lemmas.

* Reorder, drop TODO

### [2019-07-01T19:35:44+00:00](https://github.com/leanprover-community/mathlib/commit/a2c291de4a2dbdc281289a6678afb1644e2a7be1)
feat(data/mv_polynomial): miscellaneous lemmas on eval, rename, etc ([#1134](https://github.com/leanprover-community/mathlib/pull/#1134))

### [2019-07-01T17:57:38+00:00](https://github.com/leanprover-community/mathlib/commit/fcfa2a40469b6653a57c68caf8989c319c14a64e)
refactor(set_theory/ordinal): restate well_ordering_thm ([#1115](https://github.com/leanprover-community/mathlib/pull/#1115))

Define the relation rather than using an `exists` statement

### [2019-07-01T17:01:12+00:00](https://github.com/leanprover-community/mathlib/commit/f0bf43b6507c3bca1918eadf65250d4d2731201f)
feat(order/zorn): chain.image ([#1084](https://github.com/leanprover-community/mathlib/pull/#1084))

* feat(order/zorn): chain.image

* golf

### [2019-06-29T16:56:28+00:00](https://github.com/leanprover-community/mathlib/commit/469da2943dfee271e2c03c7ef283858bbe7ebf93)
feat(data/list/basic): map_nil and map_eq_nil ([#1161](https://github.com/leanprover-community/mathlib/pull/#1161))

* feat(data/list/basic): map_nil and map_eq_nil

* Update basic.lean

* make Simon's changes

### [2019-06-29T13:28:56+00:00](https://github.com/leanprover-community/mathlib/commit/0858157adb04eaeb610adc980936495fa5a4414d)
refactor(category_theory/category): reorder arguments of `End.has_mul` ([#1128](https://github.com/leanprover-community/mathlib/pull/#1128))

* Reorder arguments of `End.has_mul` and `Aut.has_mul`, adjust `category/fold`

* clean up proofs in `category.fold`

### [2019-06-29T12:31:13+00:00](https://github.com/leanprover-community/mathlib/commit/e310349838ff618e8fe8ce8b50953a709e2d4914)
refactor(ring_theory/ideals): refactor local rings, add local ring homs ([#1102](https://github.com/leanprover-community/mathlib/pull/#1102))

* WIP

* refactor(ring_theory/ideals): refactor local rings, add local ring homs

* residue_field.map is a field hom

* make is_local_ring_hom extends is_ring_hom

* refactor local_ring

* tiny changes

* Bump instance search depth

### [2019-06-28T15:11:00+00:00](https://github.com/leanprover-community/mathlib/commit/4a5a1a587de4673d0fe56af4fe964afef854bab5)
fix(data/list/min_max): correct names of mem_maximum and mem_minimum ([#1162](https://github.com/leanprover-community/mathlib/pull/#1162))

* fix(data/list/min_max): correct names of mem_maximum and mem_minimum

* Update denumerable.lean

### [2019-06-28T09:09:55+00:00](https://github.com/leanprover-community/mathlib/commit/7d56447e365ac9aa921dcba2db77be19bdb3cb3c)
feat(logic/unique): fin 1 is unique ([#1158](https://github.com/leanprover-community/mathlib/pull/#1158))

### [2019-06-27T11:12:29+00:00](https://github.com/leanprover-community/mathlib/commit/6bc930afb19f0220a10e49049531617fa32ec55a)
chore(src/tactic/interactive): `convert` docstring ([#1148](https://github.com/leanprover-community/mathlib/pull/#1148))

* chore(src/tactic/interactive): `convert` docstring 

The `using` option to `convert` was not mentioned in the docstring, and I often struggle to remember the (perhaps slightly exotic?) `using` catchphrase

* Update src/tactic/interactive.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update interactive.lean

### [2019-06-26T12:11:33+00:00](https://github.com/leanprover-community/mathlib/commit/9b0fd36245ae958aeda9e10d79650801f63cd3ae)
feat(data/fintype): unique.fintype ([#1154](https://github.com/leanprover-community/mathlib/pull/#1154))

### [2019-06-25T14:30:39+00:00](https://github.com/leanprover-community/mathlib/commit/7484ab443aed80111fa35a786a8973a44b67e65a)
fix(data/matrix): add brackets to mul_neg and neg_mul to correct statement ([#1151](https://github.com/leanprover-community/mathlib/pull/#1151))

* fix(data/matrix): add brackets to mul_neg and neg_mul to correct statement

Each side of `mul_neg` was identical.

* fix

### [2019-06-25T13:00:33+00:00](https://github.com/leanprover-community/mathlib/commit/a2aeabbbff79857ce88d179b771a0a9efa703fe4)
feat(data/finset): length_sort ([#1150](https://github.com/leanprover-community/mathlib/pull/#1150))

### [2019-06-25T13:54:02+02:00](https://github.com/leanprover-community/mathlib/commit/c4a4f795396ddd1164303e1f871e418d0d3061cf)
feat(algebra/pi_instances): pi.ordered_comm_group ([#1152](https://github.com/leanprover-community/mathlib/pull/#1152))

### [2019-06-24T12:33:51+00:00](https://github.com/leanprover-community/mathlib/commit/c7ee110492e5e80c9661ebb2435fb89f709c70ec)
feat(meta/expr): `simp` and `dsimp` an expr ([#1147](https://github.com/leanprover-community/mathlib/pull/#1147))

* feat(meta/expr): `simp` and `dsimp` an expr

* removing def that we don't need yet

### [2019-06-23T02:01:56+00:00](https://github.com/leanprover-community/mathlib/commit/d7283d7f8d9d65f175e6edbaef33bd63cc541d5a)
feat(string): `split_on` a `char` ([#1145](https://github.com/leanprover-community/mathlib/pull/#1145))

* lib: string

* type

### [2019-06-20T08:30:31+00:00](https://github.com/leanprover-community/mathlib/commit/a35d6824b6ba9160e683907106bd10eb33ae38d0)
feat(topology/order): more facts on continuous_on ([#1140](https://github.com/leanprover-community/mathlib/pull/#1140))

### [2019-06-19T21:00:28+00:00](https://github.com/leanprover-community/mathlib/commit/e598894d3296969e6172863d96ed132db2710a97)
chore(topology/*): reverse order on topological and uniform spaces ([#1138](https://github.com/leanprover-community/mathlib/pull/#1138))

* chore(topology/*): reverse order on topological and uniform spaces

* fix(topology/order): private lemma hiding partial order oscillation,
following Mario's suggestion

* change a temporary name

Co-Authored-By: Johan Commelin <johan@commelin.net>

* forgotten rename

### [2019-06-19T08:03:18+00:00](https://github.com/leanprover-community/mathlib/commit/b1cb48d1f9d15641c36b17505cb227e22b189a18)
feat(data/set): simple lemmas, renaming ([#1137](https://github.com/leanprover-community/mathlib/pull/#1137))

* feat(data/set): simple lemmas, renaming

* improve projection lemmas

* arguments order

### [2019-06-18T22:06:30+00:00](https://github.com/leanprover-community/mathlib/commit/235b8992fd8a9c8f1615122499279ad227e72915)
fix(category_theory/types): rename lemma `ulift_functor.map` ([#1133](https://github.com/leanprover-community/mathlib/pull/#1133))

* fix(category_theory/types): avoid shadowing `ulift_functor.map` by a lemma

Now we can use `ulift_functor.map` in the sense `functor.map ulift_functor`.

* `ulift_functor.map_spec` → `ulift_functor_map`

as suggested by @semorrison in https://github.com/leanprover-community/mathlib/pull/1133#pullrequestreview-250179914

### [2019-06-17T13:09:55+00:00](https://github.com/leanprover-community/mathlib/commit/d8d25e9adb01c87c355ae1358bba431c1237e2eb)
refactor(analysis/normed_space/deriv): split and move to calculus folder ([#1135](https://github.com/leanprover-community/mathlib/pull/#1135))

### [2019-06-16T19:28:43+00:00](https://github.com/leanprover-community/mathlib/commit/7b715eb6936c86fe73b9a1443ddd0ebb4221d341)
Direct limit of modules, abelian groups, rings, and fields. ([#754](https://github.com/leanprover-community/mathlib/pull/#754))

* stuff

* stuff

* more stuff

* pre merge commit

* prove of_zero.exact

* remove silly rewrite

* slightly shorten proof

* direct limit of modules

* upgrade mathlib

* direct limit of rings

* direct limit of fields (WIP)

* trying to prove zero_exact for rings

* use sqrt 2 instead of F4

* direct limit of field

* cleanup for mathlib

* remove ununsed lemmas

* clean up

* docstrings

* local

* fix build

* Replace real with polynomial int in proof

* Update basic.lean

### [2019-06-16T19:04:52+00:00](https://github.com/leanprover-community/mathlib/commit/38d5c12022e001a221e279f035e3cc0734c4a189)
feat(ring_theory/integral_closure): integral closure ([#1087](https://github.com/leanprover-community/mathlib/pull/#1087))

* feat(ring_theory/integral_closure): integral closure

* update

### [2019-06-15T01:30:00+00:00](https://github.com/leanprover-community/mathlib/commit/3ad35223f321e644ef3e16ae9ec5b9383b2baabe)
feat(data/rat/denumerable): computable denumerability of Q ([#1104](https://github.com/leanprover-community/mathlib/pull/#1104))

* feat(data/rat/denumerable): computable denumerability of Q

* blah

* fix build

* remove unnecessary decidable_eq

* add header

* delete rat.lean and update imports

* fix build

* prove exists_not_mem_finset

* massively speed up encode

* minor change

### [2019-06-14T17:40:58+00:00](https://github.com/leanprover-community/mathlib/commit/5040c81d7f15a70057f85bd9a8905f529e613265)
feat(measure_theory/integration): dominated convergence theorem ([#1123](https://github.com/leanprover-community/mathlib/pull/#1123))

* Create .DS_Store

* Revert "Create .DS_Store"

This reverts commit 5612886d493aef59205eddc5a34a75e6e5ba22c1.

* feat(measure_theory/integration): dominated convergence theorem

* Changes to styles

* Update ordered.lean

* Changes to styles

* Update integration.lean

* Changes to styles

### [2019-06-14T13:35:52+00:00](https://github.com/leanprover-community/mathlib/commit/5a183f04c00e0d9c0d99d9dba020c04a224a3dad)
provide some proof terms explicitly ([#1132](https://github.com/leanprover-community/mathlib/pull/#1132))

### [2019-06-12T04:45:45+00:00](https://github.com/leanprover-community/mathlib/commit/0c627fb3535d14955b2c2a24805b7cf473b4202f)
chore(algebra/group/hom): drop unused section variables ([#1130](https://github.com/leanprover-community/mathlib/pull/#1130))

### [2019-06-11T21:06:39+00:00](https://github.com/leanprover-community/mathlib/commit/3492206f59e8e6896d4c8f507af13e7a021b3545)
feat(data/mv_polynomial): misc lemmas on rename, map, and eval2 ([#1127](https://github.com/leanprover-community/mathlib/pull/#1127))

### [2019-06-11T19:10:13+00:00](https://github.com/leanprover-community/mathlib/commit/953c612eec2af94457f535eaf4699a3287ded425)
fix(category_theory): simplifying universes ([#1122](https://github.com/leanprover-community/mathlib/pull/#1122))

### [2019-06-11T17:46:50+00:00](https://github.com/leanprover-community/mathlib/commit/98ece77e0e07df8ac7167e4feeae26d87096fa85)
refactor(algebra/group): split into smaller files ([#1121](https://github.com/leanprover-community/mathlib/pull/#1121))

* rename `src/algebra/group.lean` → `src/algebra/group/default.lean`

* Split algebra/group/default into smaller files

No code changes, except for variables declaration and imports

* Fix compile

* fix compile error: import `anti_hom` in `algebra/group/default`

* Drop unused imports

### [2019-06-11T12:53:04-04:00](https://github.com/leanprover-community/mathlib/commit/8d0e719e255bd12557d97c7025826dc056f940a4)
chore(mergify): don't dismiss reviews [ci-skip] ([#1124](https://github.com/leanprover-community/mathlib/pull/#1124))

### [2019-06-11T04:39:39+00:00](https://github.com/leanprover-community/mathlib/commit/abfaf8d75369301725d20407253062eb8077ff46)
refactor(group_theory/abelianization): simplify abelianization  ([#1126](https://github.com/leanprover-community/mathlib/pull/#1126))

* feat(group_theory/conjugates) : define conjugates
define group conjugates and normal closure

* feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/#1022))

* trying to merge

* feat(group_theory\presented_group):  define presented groups

Presented groups are defined as a quotient of a free group by the normal subgroup  the relations generate.

* feat(group_theory\presented_group): define presented groups

Presented groups are defined as a quotient of a free group by the normal subgroup  the relations generate

* Update src/group_theory/presented_group.lean

Co-Authored-By: Keeley Hoek <keeley@hoek.io>

* Uniqueness of extension

* Tidied up to_group.unique

* Removed unnecessary line

* Changed naming

* refactor(group_theory/abelianization): simplify abelianization

The commutator of a group was previously defined using lists.
Now it is defined using `normal_closure`.
This change simplifies some of the proofs

### [2019-06-10T13:38:37+00:00](https://github.com/leanprover-community/mathlib/commit/bd2f35f3bc8830bc58179800a91197e04be65974)
feat(group_theory/presented_group): define presented groups ([#1118](https://github.com/leanprover-community/mathlib/pull/#1118))

* feat(group_theory/conjugates) : define conjugates
define group conjugates and normal closure

* feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/#1022))

* trying to merge

* feat(group_theory\presented_group):  define presented groups

Presented groups are defined as a quotient of a free group by the normal subgroup  the relations generate.

* feat(group_theory\presented_group): define presented groups

Presented groups are defined as a quotient of a free group by the normal subgroup  the relations generate

* Update src/group_theory/presented_group.lean

Co-Authored-By: Keeley Hoek <keeley@hoek.io>

* Uniqueness of extension

* Tidied up to_group.unique

* Removed unnecessary line

* Changed naming

### [2019-06-10T08:38:52+01:00](https://github.com/leanprover-community/mathlib/commit/004e0b30c769dc86702ab39f57df7ef5909ce9e4)
feat (data/pnat): extensions to pnat  ([#1073](https://github.com/leanprover-community/mathlib/pull/#1073))

* Extended API, especially divisibility and primes

* Positive euclidean algorithm

* Disambiguate overloaded ::

* Tweak broken proof of flip_is_special

* Change to mathlib style

* Update src/data/pnat.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Update src/data/pnat.lean

Co-Authored-By: Johan Commelin <johan@commelin.net>

* Adjust style for mathlib

* Moved and renamed

* Move some material from basic.lean to prime.lean

* Move some material from basic.lean to factors.lean

* Update import to data.pnat.basic.

* Update import to data.pnat.basic

* Fix import of data.pnat.basic

* Use monoid.pow instead of nat.pow

* Fix pnat.pow_succ -> pow_succ; stylistic changes

* More systematic use of coercion

* More consistent use of coercion

* Formatting; change flip' to prod.swap

### [2019-06-08T23:11:29+00:00](https://github.com/leanprover-community/mathlib/commit/3f9916e16b90236c120920df667aa97d71a8d851)
feat(tactic/rewrite_all): tactic to perform the nth occurrence of a rewrite ([#999](https://github.com/leanprover-community/mathlib/pull/#999))

* feat(tactic/rewrite_all): tactic to perform the nth occurrence of a rewrite

* formatting

* formatting

* perhaps a little bit easier to read?

* try renaming

* there was a duplicate definition, just not the one lean complained about

* Namespaces

* I think kabstract works now

* Fix

* Test

* Fix guard

* updating test to reflect difference between congr and kabstract

* oops

* adding Keeley's example

* remove kabstract implementation for now

* cleanup test file

* rename common to basic

* Update src/tactic/rewrite_all/default.lean

### [2019-06-07T16:54:39+00:00](https://github.com/leanprover-community/mathlib/commit/b55e44de0cdd632c2a1c3c21ce05f814ab6f614a)
refactor(analysis/normed_space/basic): change normed_space definition ([#1112](https://github.com/leanprover-community/mathlib/pull/#1112))

### [2019-06-07T15:21:25+00:00](https://github.com/leanprover-community/mathlib/commit/85ed958b261137a5c277a225ad8485bfba3450c0)
feat(data/quot): quot.map: act on non-id maps ([#1120](https://github.com/leanprover-community/mathlib/pull/#1120))

* old version renamed to `quot.map_right`
* similar changes to `quot.congr` and `quotient.congr`

### [2019-06-06T16:45:38+00:00](https://github.com/leanprover-community/mathlib/commit/f36fdfb4ea6010045d85c3e739a3bde1291c72e1)
refactor(category_theory/equivalence): simplify equivalence.trans ([#1114](https://github.com/leanprover-community/mathlib/pull/#1114))

### [2019-06-05T07:54:30+00:00](https://github.com/leanprover-community/mathlib/commit/a7524b63f86a95f9df918f61cdf37a9f80bcb3d6)
refactor(analysis/normed_space/operator_norm): topological modules ([#1085](https://github.com/leanprover-community/mathlib/pull/#1085))

* refactor(analysis/normed_space/operator_norm): topological modules

* remove useless typeclass in definition of topological module

* refactor(analysis/normed_space/operator_norm): style

### [2019-06-04T20:49:06+00:00](https://github.com/leanprover-community/mathlib/commit/a152f3a62f72395aaaa0f9199fdc207b918cf5ea)
chore(doc/install/macos): improve mac install instructions ([#1106](https://github.com/leanprover-community/mathlib/pull/#1106))

* tweaking install instructions

* minor

* minor

* minor

* minor

* small icon

* improve instructions for installing the extension on all OSes

* minor

### [2019-06-04T14:48:57+01:00](https://github.com/leanprover-community/mathlib/commit/542d25d6d7ff8752737db04ac4a6416b758dec91)
fix(data/logic/basic): Use a Sort for classical.some_spec2 ([#1111](https://github.com/leanprover-community/mathlib/pull/#1111))

### [2019-06-03T22:11:39+00:00](https://github.com/leanprover-community/mathlib/commit/dd832f03ea3f1ccfa045c4a9e3a5ac6e4f31dd66)
feat(topology/basic): is_open_Inter and others ([#1108](https://github.com/leanprover-community/mathlib/pull/#1108))

### [2019-06-03T20:36:09+00:00](https://github.com/leanprover-community/mathlib/commit/504c0ad2f8dd7eafbf1196bfc7f9ad8583332e5d)
feat(data/set/basic): union_inter_distrib lemmas ([#1107](https://github.com/leanprover-community/mathlib/pull/#1107))

* feat(data/set/basic): union_inter_distrib lemmas

* add parentheses

### [2019-06-03T18:05:35+00:00](https://github.com/leanprover-community/mathlib/commit/4263b2be91c453051aa5790d10fb454a9785fe35)
fix(data/nat/gcd): correct order of arguments in nat.coprime_mul_iff_right ([#1105](https://github.com/leanprover-community/mathlib/pull/#1105))

* Not sure how this works

* Fix order for coprime_mul_iff_right

* Remove spurious file

### [2019-06-01T20:38:34+00:00](https://github.com/leanprover-community/mathlib/commit/38b80546748f0f2a0d5644d539a863ef16c8911d)
feat(data/mv_polynomial): add coeff for mv_polynomial ([#1101](https://github.com/leanprover-community/mathlib/pull/#1101))

### [2019-05-31T20:59:47+00:00](https://github.com/leanprover-community/mathlib/commit/4f6307eb2ebd85f406294ac086743d8c0b44cc3e)
feat(topology/algebra/open_subgroup): basics on open subgroups  ([#1067](https://github.com/leanprover-community/mathlib/pull/#1067))

* Dump the file into mathlib

* feat(algebra/pi_instances): product of submonoids/groups/rings

From the perfectoid project.

* Small changes

* feat(topology/algebra/open_subgroup): basics on open subgroups

* Some proof compression

* Update src/topology/algebra/open_subgroup.lean

### [2019-05-31T19:49:44+00:00](https://github.com/leanprover-community/mathlib/commit/623793939c2649ec28a43453dd1b9c8cccc2642a)
fix(data/nat/enat): change [] to {} in some lemmas ([#1054](https://github.com/leanprover-community/mathlib/pull/#1054))

* fix(data/nat/enat): change [] to {} in some lemmas

* Update enat.lean

* remove space

### [2019-05-31T17:26:55+00:00](https://github.com/leanprover-community/mathlib/commit/8ebea31560fff24a78b6d242f6ad0c46996af134)
feat(category_theory/monoidal): the monoidal category of types ([#1100](https://github.com/leanprover-community/mathlib/pull/#1100))

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

### [2019-05-31T06:43:58+00:00](https://github.com/leanprover-community/mathlib/commit/2db435d8ea939af43fb215dea93543fe36ce516e)
chore(category_theory): move all instances (e.g. Top, CommRing, Meas) into the root namespace ([#1074](https://github.com/leanprover-community/mathlib/pull/#1074))

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

### [2019-05-30T12:43:47+00:00](https://github.com/leanprover-community/mathlib/commit/c49ac06ff9fa1371e9b6050a121df618cfd3fb80)
feat(category_theory/monoidal): monoidal categories, monoidal functors ([#1002](https://github.com/leanprover-community/mathlib/pull/#1002))

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

### [2019-05-29T22:06:00+00:00](https://github.com/leanprover-community/mathlib/commit/4845b663c182704738868db5861ffb4c6056be23)
feat(ring_theory): free_ring and free_comm_ring ([#734](https://github.com/leanprover-community/mathlib/pull/#734))

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

### [2019-05-29T11:10:22+00:00](https://github.com/leanprover-community/mathlib/commit/d935bc312fac7eca7ef08b16ca06079145b437f2)
feat(presheaves/stalks): stalks of presheafs, and presheafed spaces with extra structure on stalks ([#1018](https://github.com/leanprover-community/mathlib/pull/#1018))

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

### [2019-05-29T06:03:02+00:00](https://github.com/leanprover-community/mathlib/commit/0de4bba3208ee0bd8a78adf4396aa5cb083ffdf2)
feat(ordered_group): add missing instance ([#1094](https://github.com/leanprover-community/mathlib/pull/#1094))

### [2019-05-28T15:01:35+00:00](https://github.com/leanprover-community/mathlib/commit/b20b722b1920770016b4134e81ff74b7cecdf866)
fix(tactic/rcases): add parse desc to rcases/rintro ([#1091](https://github.com/leanprover-community/mathlib/pull/#1091))

### [2019-05-26T20:12:00+00:00](https://github.com/leanprover-community/mathlib/commit/d4343972661a252c53bd1ca1322a89448243c0f1)
feat(group_theory/conjugates) : define conjugates ([#1029](https://github.com/leanprover-community/mathlib/pull/#1029))

* feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/#1022))

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

### [2019-05-24T05:29:59+00:00](https://github.com/leanprover-community/mathlib/commit/c6a7f300ea43cfc0478e3ee81a141d5288d90df6)
refactor(set_theory/ordinal): shorten proof of well_ordering_thm ([#1078](https://github.com/leanprover-community/mathlib/pull/#1078))

* refactor(set_theory/ordinal): shorten proof of well_ordering_thm§

* Update ordinal.lean

* Update ordinal.lean

* Update ordinal.lean

* Improve readability

* shorten proof

* Shorten proof

### [2019-05-23T13:50:06+00:00](https://github.com/leanprover-community/mathlib/commit/62acd6b84eee7a6cf5b0448039f668294c6d8a9b)
chore(CommRing/adjunctions): refactor proofs ([#1049](https://github.com/leanprover-community/mathlib/pull/#1049))

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

### [2019-05-23T11:08:00+00:00](https://github.com/leanprover-community/mathlib/commit/15fecbdd8d4037f35a4cc4d5fdbb4e3ec3834f84)
doc(finsupp,category_theory): fixes ([#1075](https://github.com/leanprover-community/mathlib/pull/#1075))

* doc

* update emb_domain doc string

* typo

### [2019-05-22T19:04:36+00:00](https://github.com/leanprover-community/mathlib/commit/d07e3b3ed46430329635485d72a43210e2d5a912)
feat(linear_algebra/basic): general_linear_group basics ([#1064](https://github.com/leanprover-community/mathlib/pull/#1064))

* feat(linear_algebra/basic): general_linear_group basics

This patch proves that the general_linear_group (defined as units in the
endomorphism ring) are equivalent to the group of linear equivalences.

* shorten proof of ext

* Add mul_equiv

* Use coe

* Fix stupid error

### [2019-05-22T16:32:40+00:00](https://github.com/leanprover-community/mathlib/commit/f004d327cb23e7dbce2c5fb5aeceb42001953afd)
feat(data/nat): various lemmas ([#1017](https://github.com/leanprover-community/mathlib/pull/#1017))

* feat(data/nat): various lemmas

* protect a definition

* fixes

* Rob's suggestions

* Mario’s proof

(Working offline, let’s see what Travis says)

* minigolf

### [2019-05-21T21:29:42+00:00](https://github.com/leanprover-community/mathlib/commit/971ddcc2388c47bf37f6a9278e8589b325b8d838)
feat(*): image_closure ([#1069](https://github.com/leanprover-community/mathlib/pull/#1069))

Prove that the image of the closure is the closure of the image,
for submonoids/groups/rings.

From the perfectoid project.

### [2019-05-21T16:01:07+00:00](https://github.com/leanprover-community/mathlib/commit/3461399615e4b2bee12f1bc5bbf0c337d669b7b5)
refactor(integration.lean): changing `measure_space` to `measurable_space` ([#1072](https://github.com/leanprover-community/mathlib/pull/#1072))

I've been using this file and `range_const` doesn't seem to require the spurious `measure_space` instance. `measurable_space` seems to suffice.

### [2019-05-20T19:27:04+00:00](https://github.com/leanprover-community/mathlib/commit/cb30c97e743f865a4fd960036e62b4de8da4ce6b)
feat(algebra/pi_instances): product of submonoids/groups/rings ([#1066](https://github.com/leanprover-community/mathlib/pull/#1066))

From the perfectoid project.

### [2019-05-20T18:35:19+00:00](https://github.com/leanprover-community/mathlib/commit/0ab8a89d6aa862892276b7639d11849569653d12)
feat(category_theory): limits in CommRing ([#1006](https://github.com/leanprover-community/mathlib/pull/#1006))

* feat(category_theory): limits in CommRing

* by

* rename

* sections

* Update src/category_theory/types.lean

Co-Authored-By: Johannes Hölzl <johannes.hoelzl@gmx.de>

### [2019-05-20T15:36:59+00:00](https://github.com/leanprover-community/mathlib/commit/8cf7c4c8780f59104594de0829d135b95f9b0af6)
chore(topology/algebra/monoid): continuous_mul_left/right ([#1065](https://github.com/leanprover-community/mathlib/pull/#1065))

### [2019-05-20T15:11:50+00:00](https://github.com/leanprover-community/mathlib/commit/593938cd88edc2899b8e42d558f5310649b34609)
chore(ring_theory/algebra): simp-lemmas for alg_hom.to_linear_map ([#1062](https://github.com/leanprover-community/mathlib/pull/#1062))

* chore(ring_theory/algebra): simp-lemmas for alg_hom.to_linear_map

From the perfectoid project.

* Stupid error

* Update src/ring_theory/algebra.lean

Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

### [2019-05-20T11:52:29+00:00](https://github.com/leanprover-community/mathlib/commit/d001abfd48d64ac27310590458132009f47c852d)
feat(tactic/basic): adds `contrapose` tactic ([#1015](https://github.com/leanprover-community/mathlib/pull/#1015))

* feat(tactic/basic): adds `contrapose` tactic

* fix(tactic/push_neg): fix is_prop testing

* Setup error message testing following Rob, add tests for `contrapose`

* refactor(tactic/interactive): move noninteractive success_if_fail_with_msg to tactic/core

### [2019-05-20T11:16:53+00:00](https://github.com/leanprover-community/mathlib/commit/15a6af2256398decd57f2260c2cfe13af0c48b73)
feat(topology/opens): continuous.comap : opens Y → opens X ([#1061](https://github.com/leanprover-community/mathlib/pull/#1061))

* feat(topology/opens): continuous.comap : opens Y → opens X

From the perfectoid project.

* Update opens.lean

### [2019-05-20T09:26:59+00:00](https://github.com/leanprover-community/mathlib/commit/d4c7b7a6c26fed7f526234fa9c7f57eaf4f7b587)
feat(tactic/linarith): better input syntax linarith only [...] ([#1056](https://github.com/leanprover-community/mathlib/pull/#1056))

* feat(tactic/ring, tactic/linarith): add reducibility parameter

* fix(tactic/ring): interactive parsing for argument to ring1

* feat(tactic/linarith): better input syntax linarith only [...]

* fix(docs/tactics): fix linarith doc

### [2019-05-19T17:40:09+00:00](https://github.com/leanprover-community/mathlib/commit/f25340175631cdc85ad768a262433f968d0d6450)
refactor: coherent composition order ([#1055](https://github.com/leanprover-community/mathlib/pull/#1055))

### [2019-05-19T13:39:22+00:00](https://github.com/leanprover-community/mathlib/commit/cb4c9ee760ce21eed1a03f011e16ad2a3c5b6f87)
refactor(topology/metric/gromov_hausdorff): make Hausdorff_edist irreducible ([#1052](https://github.com/leanprover-community/mathlib/pull/#1052))

* refactor(topology/metric/gromov_hausdorff): remove linarith calls

* refactor(topology/metric/hausdorff_dist): make hausdorff_dist irreducible

### [2019-05-19T12:47:56+00:00](https://github.com/leanprover-community/mathlib/commit/b9cb69c37237d77d5b8a321042c16a9b0219bd4d)
feat(topology/order): make nhds irreducible ([#1043](https://github.com/leanprover-community/mathlib/pull/#1043))

* feat(topology/order): make nhds irreducible

* move nhds irreducible to topology.basic

### [2019-05-18T16:36:44-04:00](https://github.com/leanprover-community/mathlib/commit/73c3f71741552159a36388a1ab5cc2bcfd64459a)
feat(tactic/squeeze): remove noise from output ([#1047](https://github.com/leanprover-community/mathlib/pull/#1047))

### [2019-05-18T13:27:57+00:00](https://github.com/leanprover-community/mathlib/commit/fa0e757071d024bde3886f667576cc8269da7fc6)
refactor(data/complex/exponential): improve trig proofs ([#1041](https://github.com/leanprover-community/mathlib/pull/#1041))

* fix(data/complex/exponential): make complex.exp irreducible

See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/-T50000.20challenge

Using `ring` (and other tactics) on terms involving `exp` can lead to some unpleasant and unnecessary unfolding.

* refactor(data/complex/exponential): improve trig proofs

* fix build

* fix(algebra/group): prove lemma for comm_semigroup instead of comm_monoid

### [2019-05-17T20:21:42+00:00](https://github.com/leanprover-community/mathlib/commit/5e5298b9273b44aa06e3b30aa064cf866cd8152a)
feat(adjointify): make definition easier for elaborator ([#1045](https://github.com/leanprover-community/mathlib/pull/#1045))

### [2019-05-17T18:53:41+00:00](https://github.com/leanprover-community/mathlib/commit/45afa86e6e45ea4f2afa5dd5881cb5af7210a139)
fix(topology/stone_cech): faster proof from @PatrickMassot ([#1042](https://github.com/leanprover-community/mathlib/pull/#1042))

### [2019-05-17T17:38:35+00:00](https://github.com/leanprover-community/mathlib/commit/901178e2084d7d4a97bc2ddef68135eb124aa130)
feat(set_theory/surreal): surreal numbers ([#958](https://github.com/leanprover-community/mathlib/pull/#958))

* feat(set_theory/surreal): surreal numbers

* doc(set_theory/surreal): surreal docs

* minor changes in surreal

### [2019-05-17T16:13:20+00:00](https://github.com/leanprover-community/mathlib/commit/0b350228544244f2861ec8afc84dad0c27113a73)
refactor: change variables order in some composition lemmas ([#1035](https://github.com/leanprover-community/mathlib/pull/#1035))

### [2019-05-17T14:46:24+00:00](https://github.com/leanprover-community/mathlib/commit/f633c948ff523b9a47b3b41bc1dc0b1b4b2be5c4)
feat(tactic/basic): add tactic.rewrite, and sort list ([#1039](https://github.com/leanprover-community/mathlib/pull/#1039))

### [2019-05-17T13:20:21+00:00](https://github.com/leanprover-community/mathlib/commit/a6c1f377fdc47f6c2adaeaa6c63018dd261b44c6)
fix(data/complex/exponential): make complex.exp irreducible ([#1040](https://github.com/leanprover-community/mathlib/pull/#1040))

See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/-T50000.20challenge

Using `ring` (and other tactics) on terms involving `exp` can lead to some unpleasant and unnecessary unfolding.

### [2019-05-17T06:56:38+00:00](https://github.com/leanprover-community/mathlib/commit/96ea9b9996635bcc6ccdc43cebe18786482bd9aa)
chore(opposites): merge two definitions of `opposite` ([#1036](https://github.com/leanprover-community/mathlib/pull/#1036))

* chore(opposites): merge two definitions of `opposite`

* merge `opposite.opposite` from `algebra/opposites` with
  `category_theory.opposite` from `category_theory/opposites`, and put
  it into `data/opposite`

* main reasons: DRY, avoid confusion if both namespaces are open

* see https://github.com/leanprover-community/mathlib/pull/538#issuecomment-459488227

* Authors merged from `git blame` output on both original files;
  I assume my contribution to be trivial

* Update opposite.lean

### [2019-05-17T00:16:39+00:00](https://github.com/leanprover-community/mathlib/commit/def48b06f1ff9605bad07629c11c04c38324f7af)
feat(data/nat/basic): make decreasing induction eliminate to Sort ([#1032](https://github.com/leanprover-community/mathlib/pull/#1032))

* add interface for decreasing_induction to Sort

* make decreasing_induction a def

* add simp tags and explicit type

### [2019-05-16T12:58:27+00:00](https://github.com/leanprover-community/mathlib/commit/ad0f42dfaae66f646155e33acd047aa5c8a35014)
fix(data/nat/enat): Fix typo in lemma name ([#1037](https://github.com/leanprover-community/mathlib/pull/#1037))

### [2019-05-16T07:24:12+00:00](https://github.com/leanprover-community/mathlib/commit/c75c096a0f1841e3d0a8c5c96e77dfed5b0590ba)
chore(*): reduce imports ([#1033](https://github.com/leanprover-community/mathlib/pull/#1033))

* chore(*): reduce imports

* restoring import in later file

* fix import

### [2019-05-15T17:08:22+00:00](https://github.com/leanprover-community/mathlib/commit/b5aae18a7d0cd36db250069fa629f7d8517ed982)
feat(category_theory): monos and epis in Type and Top ([#1030](https://github.com/leanprover-community/mathlib/pull/#1030))

* feat(category_theory): monos and epis in Type and Top

* imports

* add file header

* use notation for adjunction

### [2019-05-15T13:26:27+00:00](https://github.com/leanprover-community/mathlib/commit/136e67a655364362908c58b644d5901c52193804)
refactor(topology): change continuous_at_within to continuous_within_at ([#1034](https://github.com/leanprover-community/mathlib/pull/#1034))

### [2019-05-15T09:44:25+00:00](https://github.com/leanprover-community/mathlib/commit/3022cafd10c3f98c996f2e0c7a636cfd38d38443)
feat(tactic/terminal_goal): determine if other goals depend on the current one ([#984](https://github.com/leanprover-community/mathlib/pull/#984))

* feat(tactics): add "terminal_goal" tactic and relatives

* fix(test/tactics): renaming test functions to avoid a name collision

* fix(tactic): moving terminal_goal to tactic/basic.lean

* fix(test/tactics): open tactics

* touching a file, to prompt travis to try again

* terminal_goal

* fix

* merge

### [2019-05-14T20:21:21+00:00](https://github.com/leanprover-community/mathlib/commit/7b579b795a1a1b7d837776ce9d9ce4959fd17c9d)
feat(category_theory): adjoint equivalences and limits under equivalences ([#986](https://github.com/leanprover-community/mathlib/pull/#986))

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

### [2019-05-14T18:15:35+00:00](https://github.com/leanprover-community/mathlib/commit/ae8f197b35776109c9b8f09df1f9e26a353cf689)
feat(data/nat/basic): decreasing induction ([#1031](https://github.com/leanprover-community/mathlib/pull/#1031))

* feat(data/nat/basic): decreasing induction

* feat(data/nat/basic): better proof of decreasing induction

### [2019-05-14T14:46:29+00:00](https://github.com/leanprover-community/mathlib/commit/e7b64c5501e90110fb8ef5aa87346f16821f89e8)
feat(data/equiv/functor): map_equiv ([#1026](https://github.com/leanprover-community/mathlib/pull/#1026))

* feat(data/equiv/functor): map_equiv

* golf proofs

### [2019-05-14T15:06:32+02:00](https://github.com/leanprover-community/mathlib/commit/02857d5672934dbd56140e6d29aae06311178552)
fix(docs/tactics): fix layout, remove noise

### [2019-05-14T12:43:19+00:00](https://github.com/leanprover-community/mathlib/commit/22790e069a2d29479ea2356df9bc5e056207a8da)
feat(tactic): new tactics to normalize casts inside expressions ([#988](https://github.com/leanprover-community/mathlib/pull/#988))

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

### [2019-05-14T11:13:33+00:00](https://github.com/leanprover-community/mathlib/commit/fe19bdb440c4e6e14e7d35f5f2254c24e57c715f)
fix(data/multiset): remove duplicate setoid instance ([#1027](https://github.com/leanprover-community/mathlib/pull/#1027))

* fix(data/multiset): remove duplicate setoid instance

* s/ : Type uu//

### [2019-05-14T10:24:51+00:00](https://github.com/leanprover-community/mathlib/commit/ade99c8ca957b815760ff01b0ac6897b994a15ba)
feat(analysis/normed_space/deriv): more material on derivatives ([#966](https://github.com/leanprover-community/mathlib/pull/#966))

* feat(analysis/normed_space/deriv): more material on derivatives

* feat(analysis/normed_space/deriv): minor improvements

* feat(analysis/normed_space/deriv) rename fderiv_at_within to fderiv_within_at

* feat(analysis/normed_space/deriv): more systematic renaming

* feat(analysis/normed_space/deriv): fix style

* modify travis.yml as advised by Simon Hudon

* fix travis.yml, second try

* feat(analysis/normed_space/deriv): add two missing lemmas

### [2019-05-14T07:24:40+00:00](https://github.com/leanprover-community/mathlib/commit/a72641be9f1856110c918416f91bbc8769daf4ba)
squeeze_simp ([#1019](https://github.com/leanprover-community/mathlib/pull/#1019))

### [2019-05-14T05:35:17+00:00](https://github.com/leanprover-community/mathlib/commit/cefb9d435a89f3ef387668a3bd956e755278d5e2)
feat(category_theory/opposites): iso.op ([#1021](https://github.com/leanprover-community/mathlib/pull/#1021))

### [2019-05-14T01:23:18+00:00](https://github.com/leanprover-community/mathlib/commit/6dc0682498270e16d457456435bd32302870e859)
feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/#1022))

### [2019-05-13T23:54:13+00:00](https://github.com/leanprover-community/mathlib/commit/07ba43ee1c8517fddbb0413e4a911e3e902105f2)
feat(topology/constructions): topology of sum types ([#1016](https://github.com/leanprover-community/mathlib/pull/#1016))

### [2019-05-13T22:28:23+00:00](https://github.com/leanprover-community/mathlib/commit/f8385b19d3ee0df3b3967514fd1a598300151354)
feat(data/equiv/basic): equiv.nonempty_iff_nonempty ([#1020](https://github.com/leanprover-community/mathlib/pull/#1020))

### [2019-05-13T20:36:11+00:00](https://github.com/leanprover-community/mathlib/commit/01b345c1a76e4b0cff4ce0f1886c8bc7b80b2f25)
feat(tactics/interactive): choose uses exists_prop ([#1014](https://github.com/leanprover-community/mathlib/pull/#1014))

* feat(tactics/interactive): choose uses exists_prop

* fix build

### [2019-05-13T20:00:57+00:00](https://github.com/leanprover-community/mathlib/commit/c8a0bb6b980e6cc3df916455fdbb1853647d8cd5)
feat(category_theory/products): missing simp lemmas ([#1003](https://github.com/leanprover-community/mathlib/pull/#1003))

* feat(category_theory/products): missing simp lemmas

* cleanup proofs

* fix proof

* squeeze_simp

### [2019-05-13T19:33:32+00:00](https://github.com/leanprover-community/mathlib/commit/6c35df0df10838bf02f1d90569488da1ae6232d2)
feat(category_theory/iso): missing lemmas ([#1001](https://github.com/leanprover-community/mathlib/pull/#1001))

* feat(category_theory/iso): missing lemmas

* formatting

* formatting

* oops

* one more

* sleep

### [2019-05-13T18:39:56+02:00](https://github.com/leanprover-community/mathlib/commit/82f151f538d6329c2072318e8927b03ec2ba7655)
document the change in scripts ([#1024](https://github.com/leanprover-community/mathlib/pull/#1024))

### [2019-05-13T15:42:01+00:00](https://github.com/leanprover-community/mathlib/commit/70cd00bc20ad304f2ac0886b2291b44261787607)
feat(Top.presheaf_ℂ): presheaves of functions to topological commutative rings ([#976](https://github.com/leanprover-community/mathlib/pull/#976))

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

### [2019-05-13T11:21:50-04:00](https://github.com/leanprover-community/mathlib/commit/b9b5bb4b53d19ffe792d34dcbeadf4ccf3be1db5)
chore(Github): no need to wait for Appveyor anymopre

### [2019-05-13T11:12:35-04:00](https://github.com/leanprover-community/mathlib/commit/e42d808be04831baafa80c8d336d513f978d9193)
chore(scripts): migrate scripts to own repo ([#1011](https://github.com/leanprover-community/mathlib/pull/#1011))

### [2019-05-13T18:20:20+10:00](https://github.com/leanprover-community/mathlib/commit/486451524b7291c3b48bfe192469058d19e5b02b)
feat(category_theory): lemmas about cancellation ([#1005](https://github.com/leanprover-community/mathlib/pull/#1005))

* feat(category_theory): lemmas about cancellation

* rename hypotheses

* Squeeze proofs

### [2019-05-12T14:51:35+00:00](https://github.com/leanprover-community/mathlib/commit/1e0761e5fe866d4004cc86e6439f507b06414ee3)
feat(topology/maps): closed embeddings ([#1013](https://github.com/leanprover-community/mathlib/pull/#1013))

* feat(topology/maps): closed embeddings

* fix "is_open_map"

### [2019-05-12T01:21:18+00:00](https://github.com/leanprover-community/mathlib/commit/de5d0387d115e872644455f58b68d7c06e166f05)
feat(logic/function): comp₂ -- useful for binary operations ([#993](https://github.com/leanprover-community/mathlib/pull/#993))

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

### [2019-05-11T18:16:49-04:00](https://github.com/leanprover-community/mathlib/commit/a154dedcc89f5c089ff30f9666e35ec43ec4c5eb)
fix(docs/*): docs reorganization [skip ci] ([#1012](https://github.com/leanprover-community/mathlib/pull/#1012))

### [2019-05-11T14:35:23-04:00](https://github.com/leanprover-community/mathlib/commit/8e71ceec788dab536b33546265ee90c3b9ee46a2)
chore(build): remove script testing on PRs [skip ci]

### [2019-05-11T13:26:30-04:00](https://github.com/leanprover-community/mathlib/commit/e6d959df6d0bc7fffdb9430afdaf97593486fb75)
docs(algebra/ring): document compatibility hack [skip ci]

### [2019-05-11T12:46:31-04:00](https://github.com/leanprover-community/mathlib/commit/c7d870e8debba680c476b18481e62a2c09317561)
chore(compatibility): compatibility with Lean 3.5.0c ([#1007](https://github.com/leanprover-community/mathlib/pull/#1007))

### [2019-05-11T15:00:03+00:00](https://github.com/leanprover-community/mathlib/commit/60da4f4d056f8d286d915f374efad539430c46cd)
feat(data/polynomial): degree_eq_one_of_irreducible_of_root ([#1010](https://github.com/leanprover-community/mathlib/pull/#1010))

### [2019-05-11T13:14:21+00:00](https://github.com/leanprover-community/mathlib/commit/8603e6b08ff6de86ae93d5f402b704a8f3c01aa6)
refactor(algebra/associated): rename nonzero_of_irreducible to ne_zero_of_irreducible ([#1009](https://github.com/leanprover-community/mathlib/pull/#1009))

### [2019-05-11T00:09:41+00:00](https://github.com/leanprover-community/mathlib/commit/6858c2f713aaa6419fb97c51a4088fd8f4a12614)
fix(category/fold): use correct `opposite` ([#1008](https://github.com/leanprover-community/mathlib/pull/#1008))

### [2019-05-10T02:32:26+00:00](https://github.com/leanprover-community/mathlib/commit/91a7fc239fd1e295ad5b20e739bf554603a9145c)
fix(tactic/basic): missing `conv` from tactic.basic ([#1004](https://github.com/leanprover-community/mathlib/pull/#1004))

### [2019-05-10T00:53:48+00:00](https://github.com/leanprover-community/mathlib/commit/e66e1f30d8a0a006ff93a309cc202ab4deaebf04)
feat(set_theory): add to cardinal, ordinal, cofinality ([#963](https://github.com/leanprover-community/mathlib/pull/#963))

* feat(set_theory): add to cardinal, ordinal, cofinality

The main new fact is the infinite pigeonhole principle
Also includes many basic additions

* fix name change in other files

* address all of Mario's comments

* use classical tactic in order/basic

I did not use it for well_founded.succ, because that resulted in an error in lt_succ

* fix error

### [2019-05-09T09:29:20+00:00](https://github.com/leanprover-community/mathlib/commit/5329bf3af9ecea916d32362dc28fd391075a63a1)
feat(algebra/pointwise): More lemmas on pointwise multiplication ([#997](https://github.com/leanprover-community/mathlib/pull/#997))

* feat(algebra/pointwise): More lemmas on pointwise multiplication

* Fix build, hopefully

* Fix build

* to_additive + fix formatting

### [2019-05-09T05:36:49+00:00](https://github.com/leanprover-community/mathlib/commit/df5eddebf25e9e3627591d8bf93cc78e3c3b36f8)
refactor(strict_mono): make definition + move to order_functions ([#998](https://github.com/leanprover-community/mathlib/pull/#998))

* refactor(strict_mono): make definition + move to order_functions

* Weaken assumptions from preorder to has_lt

### [2019-05-08T22:40:27+00:00](https://github.com/leanprover-community/mathlib/commit/8f5d240178d11b90e0bb79e777aef6055fb5cd8f)
refactor(order/basic): make type class args explicit in {*}order.lift ([#995](https://github.com/leanprover-community/mathlib/pull/#995))

* refactor(order/basic): make type class arguments explicit for {*}order.lift

* Let's try again

* And another try

* Silly typo

* Fix error

* Oops, missed this one

### [2019-05-08T20:20:16+00:00](https://github.com/leanprover-community/mathlib/commit/7f9717fdb0d0c75b61aa0f5a8fc829c2bfcb5cf8)
feat(*): preorder instances for with_bot and with_zero ([#996](https://github.com/leanprover-community/mathlib/pull/#996))

* feat(*): preorder instances for with_bot and with_zero

* Let's try again

### [2019-05-08T11:42:00+00:00](https://github.com/leanprover-community/mathlib/commit/c9cfafc922927c4fc157a4acc2e8df984d3e74bd)
chore(tactics): splitting tactics and tests into more files ([#985](https://github.com/leanprover-community/mathlib/pull/#985))

* chore(tactics): splitting tactics and tests into more files, cleaning up dependencies

* tweaking comment

* introducing `tactic.basic` and fixing imports

* fixes

* fix copyright

* fix some things

### [2019-05-08T09:47:14+00:00](https://github.com/leanprover-community/mathlib/commit/73a30da3433e3c28c224526e8452ed02200de156)
feat(group_theory/subgroup): is_subgroup.inter ([#994](https://github.com/leanprover-community/mathlib/pull/#994))

### [2019-05-07T20:44:11-05:00](https://github.com/leanprover-community/mathlib/commit/87cf6e364c2b5b75d64049d01ab088a03666b17f)
feat(category_theory/category_of_elements) ([#990](https://github.com/leanprover-community/mathlib/pull/#990))

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

### [2019-05-07T19:03:46+00:00](https://github.com/leanprover-community/mathlib/commit/820bac36ef82ad532b297bb0397b1d8c330644b6)
building the hyperreal library ([#835](https://github.com/leanprover-community/mathlib/pull/#835))

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

### [2019-05-07T17:27:55+00:00](https://github.com/leanprover-community/mathlib/commit/4a38d2e1389f2bb3eecbfcb425a08429caad1633)
feat(scripts): add --build-new flag to cache-olean ([#992](https://github.com/leanprover-community/mathlib/pull/#992))

### [2019-05-07T10:49:02-04:00](https://github.com/leanprover-community/mathlib/commit/717033e316f12ebd9eee9a731e631a8ffcd6e67c)
chore(build): cron build restarts from scratch

### [2019-05-07T08:45:19+00:00](https://github.com/leanprover-community/mathlib/commit/c726c12895037c4b4c7b048794601721956b7c67)
feat(category/monad/cont): monad_cont instances for state_t, reader_t, except_t and option_t ([#733](https://github.com/leanprover-community/mathlib/pull/#733))

* feat(category/monad/cont): monad_cont instances for state_t, reader_t,
except_t and option_t

* feat(category/monad/writer): writer monad transformer

### [2019-05-07T01:25:54-04:00](https://github.com/leanprover-community/mathlib/commit/98ba07bc36c0c976a399531a98caf8da1b34b815)
chore(build): fix stages in cron job

### [2019-05-07T00:28:50-04:00](https://github.com/leanprover-community/mathlib/commit/505f748bed48e552bffa1bdc257ca0da09c09fce)
chore(build): build against Lean 3.5 nightly build ([#989](https://github.com/leanprover-community/mathlib/pull/#989))

### [2019-05-06T16:50:37+00:00](https://github.com/leanprover-community/mathlib/commit/6eba20b05c4b77691cab203a92ca0566219f8304)
feat(category_theory): currying for functors ([#981](https://github.com/leanprover-community/mathlib/pull/#981))

* feat(category_theory): currying for functors

* Update src/category_theory/currying.lean

Co-Authored-By: semorrison <scott@tqft.net>

* compacting

* fix import

* change from review

* rfl on same line

### [2019-05-06T05:34:58+00:00](https://github.com/leanprover-community/mathlib/commit/f536dac8e35b4612d294ce2185c3a9452fd14916)
six(style.md): fix broken code ([#987](https://github.com/leanprover-community/mathlib/pull/#987))

### [2019-05-05T11:57:30+00:00](https://github.com/leanprover-community/mathlib/commit/23270e71db4dc10fb66a6cda47a054004a1ed57e)
feat(ring_theory/adjoin): adjoining elements to form subalgebras ([#756](https://github.com/leanprover-community/mathlib/pull/#756))

* feat(ring_theory/adjoin): adjoining elements to form subalgebras

* Fix build

* Change to_submodule into a coercion

* Use pointwise_mul

* add simp attribute to adjoin_empty

### [2019-05-05T07:50:10+00:00](https://github.com/leanprover-community/mathlib/commit/3f26ba88eb72269c5e9fe0f3794890e954a504e7)
feat(category_theory/products): associators ([#982](https://github.com/leanprover-community/mathlib/pull/#982))

### [2019-05-05T07:02:45+00:00](https://github.com/leanprover-community/mathlib/commit/1e8f438cd4d9fed9dfa744cf2258c64b01e6cd4d)
feat(presheaves) ([#886](https://github.com/leanprover-community/mathlib/pull/#886))

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

### [2019-05-05T02:40:54+00:00](https://github.com/leanprover-community/mathlib/commit/fc8b08b303c038d6b916eba2cff1d2a6d880e050)
feat(data/set/basic): prod_subset_iff ([#980](https://github.com/leanprover-community/mathlib/pull/#980))

* feat(data/set/basic): prod_subset_iff

* syntax

### [2019-05-04T23:56:50+00:00](https://github.com/leanprover-community/mathlib/commit/fbce6e4d46fb22ff4145c0e854d3966ef69a983d)
fix(data/set/finite): make fintype_seq an instance ([#979](https://github.com/leanprover-community/mathlib/pull/#979))

### [2019-05-04T22:16:39+00:00](https://github.com/leanprover-community/mathlib/commit/7dea60ba8909cddc931037acf3245aaae36aa486)
feat(logic/basic): forall_iff_forall_surj ([#977](https://github.com/leanprover-community/mathlib/pull/#977))

a lemma from the perfectoid project

### [2019-05-04T20:01:33+00:00](https://github.com/leanprover-community/mathlib/commit/b4d483e2ade32821d60951f7f93c30b8e5a46038)
feat(colimits): arbitrary colimits in Mon and CommRing ([#910](https://github.com/leanprover-community/mathlib/pull/#910))

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

### [2019-05-04T12:06:04-05:00](https://github.com/leanprover-community/mathlib/commit/c7baf8ef2beee52eeacf849d7e6417356883ad65)
feat(option/injective_map) ([#978](https://github.com/leanprover-community/mathlib/pull/#978))

### [2019-05-03T21:34:29+00:00](https://github.com/leanprover-community/mathlib/commit/f98ffdefc77ce0f40199280cea68ff13afb0206c)
feat(tactic/decl_mk_const): performance improvement for library_search ([#967](https://github.com/leanprover-community/mathlib/pull/#967))

* feat(tactic/decl_mk_const): auxiliary tactic for library_search [WIP]

* use decl_mk_const in library_search

* use decl_mk_const

* move into tactic/basic.lean

### [2019-05-03T13:58:06-04:00](https://github.com/leanprover-community/mathlib/commit/7b1105bfbefd78082ccbf2a90c4240ccb0a6121a)
chore(build): build only master and its related PRs

### [2019-05-03T13:37:08-04:00](https://github.com/leanprover-community/mathlib/commit/e747c91ce18853ab3e9eeb26a6d08f2cd8e2986f)
chore(README): put the badges in the README on one line ([#975](https://github.com/leanprover-community/mathlib/pull/#975))

### [2019-05-03T12:35:46-04:00](https://github.com/leanprover-community/mathlib/commit/f2db6369ec2a50274930ce22ef5cb70a83e858ca)
feat(docs/install_debian): Debian startup guide ([#974](https://github.com/leanprover-community/mathlib/pull/#974))

* feat(docs/install_debian): Debian startup guide

* feat(scripts/install_debian): One-line install for Debian  [ci skip]

* fix(docs/install_debian*): Typos pointed out by Johan

Also adds a summary of what will be installed

### [2019-05-03T11:30:19-05:00](https://github.com/leanprover-community/mathlib/commit/f5060c40044f8d126688e8ff829723a4ff3c447f)
feat(category_theory/limits): support for special shapes of (co)limits ([#938](https://github.com/leanprover-community/mathlib/pull/#938))

feat(category_theory/limits): support for special shapes of (co)limits

### [2019-05-03T15:24:11+02:00](https://github.com/leanprover-community/mathlib/commit/219cb1a1f308eb5001cb518c6fe1db0ac49c8ec3)
chore(travis): disable the check for minimal imports ([#973](https://github.com/leanprover-community/mathlib/pull/#973))

### [2019-05-03T14:11:01+01:00](https://github.com/leanprover-community/mathlib/commit/44386cde1be3a53379602659651bfbcf7cb18bfe)
chore(docs): delete docs/wip.md ([#972](https://github.com/leanprover-community/mathlib/pull/#972))

* chore(docs): delete docs/wip.md

long outdated

* remove link in README

### [2019-05-03T10:59:45+00:00](https://github.com/leanprover-community/mathlib/commit/3eb7ebca3d8d4614f37cef454e69a2ed7c0399d7)
remove code duplication ([#971](https://github.com/leanprover-community/mathlib/pull/#971))

### [2019-05-02T22:55:52+01:00](https://github.com/leanprover-community/mathlib/commit/6956daa2aa90bf84de0ebce5be25ad1a8b4a9b9b)
fix(data/polynomial): change instance order in polynomial.subsingleton ([#970](https://github.com/leanprover-community/mathlib/pull/#970))

### [2019-05-02T17:32:09+00:00](https://github.com/leanprover-community/mathlib/commit/60b3c198e31061bbe136f6180dea45a96602dcd2)
fix(scripts/remote-install-update-mathlib): apt shouldn't ask ([#969](https://github.com/leanprover-community/mathlib/pull/#969))

### [2019-05-02T12:29:34-04:00](https://github.com/leanprover-community/mathlib/commit/d288905871d8a2bb35beaf5bf11ae8ea94b5b894)
fix(script/remote-install-update-mathlib) fix answer reading and requests/urllib3 version conflict ([#968](https://github.com/leanprover-community/mathlib/pull/#968))

### [2019-05-02T08:40:53+00:00](https://github.com/leanprover-community/mathlib/commit/8a097f13837d4648caf054dd02c98ff600a80478)
feat(ring_theory/ideal_operations): inj_iff_trivial_ker for ring homomorphisms ([#951](https://github.com/leanprover-community/mathlib/pull/#951))

* feat(ring_theory/ideal_operations): inj_iff_trivial_ker for ring homomorphisms

* Update subgroup.lean

* Update ideal_operations.lean

### [2019-05-02T08:08:14+00:00](https://github.com/leanprover-community/mathlib/commit/ef11fb3d102e87cad6daf182b9929a1cc0004ab4)
feat(category_theory/limits/opposites): (co)limits in opposite categories ([#926](https://github.com/leanprover-community/mathlib/pull/#926))

* (co)limits in opposite categories

* moving lemmas

* moving stuff about complete lattices to separate PR

* renaming category_of_preorder elsewhere

* build limits functor/shape at a time

* removing stray commas, and making one-liners

* remove non-terminal simps

### [2019-05-02T04:37:39+00:00](https://github.com/leanprover-community/mathlib/commit/69094fcf364ebb393ac7cd1b298c59cd078268e4)
fix(tactic/library_search): iff lemmas with universes ([#935](https://github.com/leanprover-community/mathlib/pull/#935))

* fix(tactic/library_search): iff lemmas with universes

* cleaning up

* add crossreference

### [2019-05-02T02:35:03+00:00](https://github.com/leanprover-community/mathlib/commit/9b7fb5fddff105df7a5c9ee843f380b329dba433)
feat(category_theory/limits): complete lattices have (co)limits ([#931](https://github.com/leanprover-community/mathlib/pull/#931))

* feat(category_theory/limits): complete lattices have (co)limits

* Update lattice.lean

### [2019-05-01T08:53:51-04:00](https://github.com/leanprover-community/mathlib/commit/b3433a51ea8bc07c4159c1073838fc0ee9b8f227)
feat(script/auth_github): improve messages [ci skip] ([#965](https://github.com/leanprover-community/mathlib/pull/#965))

### [2019-04-30T20:17:17+00:00](https://github.com/leanprover-community/mathlib/commit/c8a2aa95af29632f1b1ac7457bc4a4699ce09d28)
chore(category_theory): move small_category_of_preorder to preorder namespace ([#932](https://github.com/leanprover-community/mathlib/pull/#932))

### [2019-04-30T18:22:31+02:00](https://github.com/leanprover-community/mathlib/commit/7c86814852349898b949968e17da5fed3ab44f7b)
fix(scripts/remote-install-update-mathlib): try again [ci skip]

The previous attempt to install setuptools seems to fails for timing
reasons (PyGithub need setuptools after it's downloaded but before
it is installed, this is probably also a packaging issue in PyGithub).

### [2019-04-30T15:20:36+00:00](https://github.com/leanprover-community/mathlib/commit/a15fca5da38507101b3688db2415ed372ea6e3de)
fix(scripts/remote-install-update-mathlib): missing dependency ([#964](https://github.com/leanprover-community/mathlib/pull/#964))

Also add a `--upgrade` option to `pip install` in case something is
already there but outdated

### [2019-04-30T12:53:25+01:00](https://github.com/leanprover-community/mathlib/commit/8dcce05f7902df5db35ad3a82f1b8c49cd4f2a18)
feat(analysis/normed_space): open mapping ([#900](https://github.com/leanprover-community/mathlib/pull/#900))

* The Banach open mapping theorem

* improve comments

* feat(analysis/normed_space): rebase, fix build

### [2019-04-29T20:12:03+00:00](https://github.com/leanprover-community/mathlib/commit/00aaf05a00b928ea9ac09721d87ae5d2ca1ae5a1)
refactor(tactic/interactive): remove dependencies of ([#878](https://github.com/leanprover-community/mathlib/pull/#878))

`tactic/interactive` on many theories

### [2019-04-29T12:46:38+02:00](https://github.com/leanprover-community/mathlib/commit/9b3e91b0d1560402f8792d84465039d0710454ea)
Update elan.md

### [2019-04-26T20:52:03+00:00](https://github.com/leanprover-community/mathlib/commit/53f9878642eb25238960bdff674d7beb55e83400)
refactor(analysis/normed_space): use bundled type for `fderiv` ([#956](https://github.com/leanprover-community/mathlib/pull/#956))

* feat(analysis/normed_space): refactor fderiv to use bounded_linear_map

- uniqueness remains sorry'd
- more simp lemmas about bounded_linear_map

* refactor uniqueness proof

* fix(analysis/normed_space/operator_norm): rename `bound_le_op_norm` to `op_norm_le_bound`

- so that the inequality goes the correct way.

### [2019-04-26T22:27:05+02:00](https://github.com/leanprover-community/mathlib/commit/b49bf61cfca12173e945c256c83d7a3f1ecd2723)
fix(README): update maintainer list

### [2019-04-26T10:52:46+01:00](https://github.com/leanprover-community/mathlib/commit/0444f9c2154b1ceed244bbaae2ef1ecd78f903e5)
feat(data/equiv/basic): sum_compl_apply and others ([#961](https://github.com/leanprover-community/mathlib/pull/#961))

* feat(data/equiv/basic): sum_congr_apply and others

* Update basic.lean

### [2019-04-25T18:58:02+00:00](https://github.com/leanprover-community/mathlib/commit/038f809c5856069728ea5828eb172d8114f496b4)
refactor(analysis/normed_space/operator_norm): replace subspace with … ([#955](https://github.com/leanprover-community/mathlib/pull/#955))

* refactor(analysis/normed_space/operator_norm): replace subspace with structure

* refactor(analysis/normed_space/operator_norm): add coercions

### [2019-04-23T20:15:47+00:00](https://github.com/leanprover-community/mathlib/commit/1d9ff681a28018db5cccbe34d3bbd980e3605c6c)
feat(function/embedding): ext and ext_iff ([#962](https://github.com/leanprover-community/mathlib/pull/#962))

### [2019-04-23T07:22:05+00:00](https://github.com/leanprover-community/mathlib/commit/0d7b41958463130461a1c2df100b0a96a3202afb)
fix(ring_theory/adjoin_root): move adjoin_root out of adjoin_root namespace ([#960](https://github.com/leanprover-community/mathlib/pull/#960))

### [2019-04-22T23:48:35+00:00](https://github.com/leanprover-community/mathlib/commit/45456cf1271c84d45e909800fb1d5f2c72822a0f)
refactor(data/equiv/basic): simplify definition of equiv.set.range ([#959](https://github.com/leanprover-community/mathlib/pull/#959))

* refactor(data/equiv/basic): simplify definition of equiv.set.range

* delete duplicate

### [2019-04-22T15:00:53+00:00](https://github.com/leanprover-community/mathlib/commit/63bbd1c39869bfb9746338e074110b37a64fa143)
feat(data/list/basic): index_of_inj ([#954](https://github.com/leanprover-community/mathlib/pull/#954))

* feat(data/list/basic): index_of_inj

* make it an iff

### [2019-04-21T06:07:43-04:00](https://github.com/leanprover-community/mathlib/commit/3478f1f65fc0aed5574a7f59316976f1c01522c2)
fix(tactic/interactive): allow `convert e using 0`

### [2019-04-20T18:42:45-04:00](https://github.com/leanprover-community/mathlib/commit/9daa1a579fd86c537229c34a00a18a23fdad4db8)
feat(tactic/clear_except): clear most of the assumptions in context ([#957](https://github.com/leanprover-community/mathlib/pull/#957))

### [2019-04-20T20:07:03+00:00](https://github.com/leanprover-community/mathlib/commit/4b9d94dc6063f98e70684fdea8c27b93482fb0ba)
feat(data/[fin]set): add some more basic properties of (finite) sets ([#948](https://github.com/leanprover-community/mathlib/pull/#948))

* feat(data/[fin]set): add some more basic properties of (finite) sets

* update after reviews

* fix error, move pairwise_disjoint to lattice as well

* fix error

### [2019-04-20T15:39:59+02:00](https://github.com/leanprover-community/mathlib/commit/7370cbf2e5dfdcf99a00641e95aa34d59381064e)
feat(tactic/linarith): treat expr atoms up to defeq ([#950](https://github.com/leanprover-community/mathlib/pull/#950))

### [2019-04-20T09:47:15+00:00](https://github.com/leanprover-community/mathlib/commit/784a68c3417d271882156e9fb5ccf4091685e694)
fix(topology/order): Missing Prop annotation ([#952](https://github.com/leanprover-community/mathlib/pull/#952))

### [2019-04-20T00:49:21+00:00](https://github.com/leanprover-community/mathlib/commit/e4fc5afd4f551e9acfc63e7c255fdeb0955bdb3d)
feat(tactic/ring): treat expr atoms up to defeq ([#949](https://github.com/leanprover-community/mathlib/pull/#949))

### [2019-04-18T22:33:17-04:00](https://github.com/leanprover-community/mathlib/commit/c1aff1b5c52b7996d69da2d2522cd696d811ed06)
style(tactic/omega): whitespace and minor tweaks

missed the PR review cycle

### [2019-04-18T20:15:55+00:00](https://github.com/leanprover-community/mathlib/commit/d0140dd8c5519ff0c79c3986d5058bef3906a756)
feat(group_theory/subgroup): additive version of inj_iff_trivial_ker ([#947](https://github.com/leanprover-community/mathlib/pull/#947))

### [2019-04-17T15:33:51+00:00](https://github.com/leanprover-community/mathlib/commit/032400bd3cd7833feecb5d2c447c706315776b8f)
feat(analysis/normed_space): more facts about operator norm ([#927](https://github.com/leanprover-community/mathlib/pull/#927))

* refactor(analysis/normed_space): refactor and additional lemmas

- rename `bounded_linear_maps` to `bounded_linear_map`, `operator_norm` to `op_norm`.

- refactor operator norm with an equivalent definition.

- change some names and notation to be more consistent with conventions elsewhere
  in mathlib: replace `bounded_by_*` with `le_*`, `operator_norm_homogeneous` with
  `op_norm_smul`.

- more simp lemmas for bounded_linear_map.

- additional results: lipschitz continuity of the operator norm, also
  that it is submultiplicative.

* chore(analysis/normed_space/operator_norm): add attribution

* style(analysis/normed_space/operator_norm): use namespace `real`

- open `real` instead of `lattice` and omit spurious prefixes.

* feat(analysis/normed_space/operator_norm): coercion to linear_map

* style(analysis/normed_space/bounded_linear_maps): minor edits

- extract variables for brevity of theorem statements.
- more consistent naming of variables.

* feat(analysis/normed_space/operator_norm): add constructor of bounded_linear_map from is_bounded_linear_map

* fix(analysis/normed_space/operator_norm): remove spurious explicit argument

* fix(analysis/normed_space): type of bounded linear maps

- change the definition of bounded_linear_map to be a type rather than
  the corresponding subspace, and mark it for unfolding.

- rename `bounded_linear_map.from_is_bounded_linear_map` to `is_bounded_linear_map.to_bounded_linear_map`.

* feat(analysis/normed_space): analysis results for bounded_linear_maps

### [2019-04-17T09:53:00-04:00](https://github.com/leanprover-community/mathlib/commit/8b23dadced773d60ca98080c0509c3feb3726644)
feat(scripts): use apt-get on ubuntu and support older Python versions ([#945](https://github.com/leanprover-community/mathlib/pull/#945))

### [2019-04-17T11:03:45+02:00](https://github.com/leanprover-community/mathlib/commit/3f4b154aa568463c26e32c2557108fe144afe68c)
feat(tactic/omega): tactic for linear integer & natural number arithmetic ([#827](https://github.com/leanprover-community/mathlib/pull/#827))

* feat(tactic/omega): tactic for discharging linear integer and natural number arithmetic goals

* refactor(tactic/omega): clean up namespace and notations

* Update src/data/list/func.lean

Co-Authored-By: skbaek <seulkeebaek@gmail.com>

* Add changed files

* Refactor val_between_map_div

* Use default inhabitants for list.func

### [2019-04-16T21:38:18+00:00](https://github.com/leanprover-community/mathlib/commit/4b8106b3c75461db186f5f98df78b1dee7618a35)
fix(test/local_cache): make the trace text explicit and quiet ([#941](https://github.com/leanprover-community/mathlib/pull/#941))

(by default)

### [2019-04-16T20:12:19+00:00](https://github.com/leanprover-community/mathlib/commit/7bbbee1e7e4ee23e43f385d2c713947f3be5a66a)
feat(*): various additions to low-level files ([#904](https://github.com/leanprover-community/mathlib/pull/#904))

* feat(*): various additions to low-level files

* fix(data/fin): add missing universe

### [2019-04-16T18:10:16+00:00](https://github.com/leanprover-community/mathlib/commit/22948763023aff7b0a9634b180e7838b39a3803d)
feat(data/finset): powerset_len (subsets of a given size) ([#899](https://github.com/leanprover-community/mathlib/pull/#899))

* feat(data/finset): powerset_len (subsets of a given size)

* fix build

### [2019-04-16T16:32:52+00:00](https://github.com/leanprover-community/mathlib/commit/8985a4335a19742d176c38cdc4849a324019d857)
feat(data/set/intervals): some interval lemmas ([#942](https://github.com/leanprover-community/mathlib/pull/#942))

* feat(data/set/intervals): a few more lemmas

* one-liners

### [2019-04-16T07:19:32+00:00](https://github.com/leanprover-community/mathlib/commit/361e216388d6d63e12f2cb11a444fce3c05701d9)
feature(category_theory/instances/Top/open[_nhds]): category of open sets, and open neighbourhoods of a point (merge [#920](https://github.com/leanprover-community/mathlib/pull/#920) first) ([#922](https://github.com/leanprover-community/mathlib/pull/#922))

* rearrange Top

* oops, import from the future

* the categories of open sets and of open_nhds

* missing import

* restoring opens, adding headers

* Update src/category_theory/instances/Top/open_nhds.lean

Co-Authored-By: semorrison <scott@tqft.net>

* use full_subcategory_inclusion

### [2019-04-15T19:41:40+00:00](https://github.com/leanprover-community/mathlib/commit/5f04e76eb850c07f4357b7869e7ca9d212d1b58f)
feat(nat/basic): add some basic nat inequality lemmas ([#937](https://github.com/leanprover-community/mathlib/pull/#937))

* feat(nat/basic): add some basic nat inequality lemmas, useful as specific cases of existing ring cases since uses less hypothesis

* feat(nat/basic): add some basic nat inequality lemmas, with convention fixes

* feat(nat/basic): add some basic nat inequality lemmas, with convention fixes

### [2019-04-15T19:09:47+00:00](https://github.com/leanprover-community/mathlib/commit/d06eb8582aa936fbdbd55ba47ecb2ae1677c8036)
feat(topology/algebra/continuous_functions): the ring of continuous functions ([#923](https://github.com/leanprover-community/mathlib/pull/#923))

* feat(topology/algebra/continuous_functions): the ring of continuous functions

* filling in the hierarchy

* use to_additive

### [2019-04-14T19:26:36-04:00](https://github.com/leanprover-community/mathlib/commit/ca5d4c1f16f9c451cf7170b10105d0051db79e1b)
feat(scripts): disable testing the install scripts in external PRs ([#936](https://github.com/leanprover-community/mathlib/pull/#936))

### [2019-04-14T15:16:28+01:00](https://github.com/leanprover-community/mathlib/commit/a1b7dcdf078238a597b922952f949a6cbe2de578)
fix(algebra/big_operators): change variables in finset.prod_map to remove spurious [comm_monoid β] ([#934](https://github.com/leanprover-community/mathlib/pull/#934))

The old version involved maps α → β → γ and an instance [comm_monoid γ], but there was also a section variable [comm_monoid β].  In applications of this lemma it is not necessary, and not usually true, that β is a monoid.  Change the statement to involve maps α → γ → β so that we already have a monoid structure on the last variable and we do not make spurious assumptions about the second one.

### [2019-04-13T21:56:41+02:00](https://github.com/leanprover-community/mathlib/commit/f01934c62f0fe00863ea1d52ed80fdb6869c967e)
docs(elan): remove reference to nightly Lean ([#928](https://github.com/leanprover-community/mathlib/pull/#928))

* docs(elan): Remove reference to nightly Lean.

### [2019-04-13T19:13:56+01:00](https://github.com/leanprover-community/mathlib/commit/49c3a04963b8c3056e9e341d6160e4081ce3b0b0)
fix(algebra.field): introduce division_ring_has_div' ([#852](https://github.com/leanprover-community/mathlib/pull/#852))

* fix division_ring_has_div

* priority default

* comment

### [2019-04-12T12:59:14+02:00](https://github.com/leanprover-community/mathlib/commit/3fe449e130ab56e0b7cd0a8c2eb6ed9d32c8e3fa)
feat(algebra/free): free magma, semigroup, monoid ([#735](https://github.com/leanprover-community/mathlib/pull/#735))

### [2019-04-11T19:08:59+00:00](https://github.com/leanprover-community/mathlib/commit/be79f25b254ee1beb0771d9019476686262d5959)
refactor(data/int/basic): weaken hypotheses for int.induction_on ([#887](https://github.com/leanprover-community/mathlib/pull/#887))

* refactor(data/int/basic): weaken hypotheses for int.induction_on

* fix build

* fix build

### [2019-04-11T14:11:00+00:00](https://github.com/leanprover-community/mathlib/commit/36f0c224bc416adf704fb0a416a7e6cc8c33e93e)
feat(submonoid, subgroup, subring): is_ring_hom instances for set.inclusion ([#917](https://github.com/leanprover-community/mathlib/pull/#917))

### [2019-04-11T04:11:18-04:00](https://github.com/leanprover-community/mathlib/commit/c1e07a2e46c954aba47335880b7bb9459dffc4aa)
fix(tactic/explode): more accurate may_be_proof ([#924](https://github.com/leanprover-community/mathlib/pull/#924))

### [2019-04-11T00:50:17+00:00](https://github.com/leanprover-community/mathlib/commit/22fcb4e95855edc8b1303eb500cb377a2cd4ebef)
minor changes ([#921](https://github.com/leanprover-community/mathlib/pull/#921))

### [2019-04-10T17:49:27+00:00](https://github.com/leanprover-community/mathlib/commit/f5d43a95f6586b76f0a5ee94919e5a4343148ec0)
feat(analysis/normed_space/deriv): show that the differential is unique (2) ([#916](https://github.com/leanprover-community/mathlib/pull/#916))

* Remove wrong simp attribute

* fix typo

* characterize convergence at_top in normed spaces

* copy some changes from [#829](https://github.com/leanprover-community/mathlib/pull/#829)

* small elements in normed fields go to zero

* derivatives are unique

* remove unnecessary lemma

* update according to review

* remove another empty line

### [2019-04-10T17:14:40+00:00](https://github.com/leanprover-community/mathlib/commit/41014e509a33c1921bee258aa45cf6bd58deb067)
rename has_sum and is_sum to summable and has_sum ([#912](https://github.com/leanprover-community/mathlib/pull/#912))

### [2019-04-10T16:24:03+01:00](https://github.com/leanprover-community/mathlib/commit/c4b65da1ffcad2d3a3e6ee1bec28f57eca0fa031)
fix(mergify): merge if either push or pr build passes. ([#918](https://github.com/leanprover-community/mathlib/pull/#918))

* fix(mergify): merge if either push or pr build passes.

* Update .mergify.yml

* Update .mergify.yml

### [2019-04-10T09:45:01+01:00](https://github.com/leanprover-community/mathlib/commit/49ccc9f74534b50b30127755f2e5adb189886315)
refactor(order/lexicographic): use prod.lex and psigma.lex ([#914](https://github.com/leanprover-community/mathlib/pull/#914))

* refactor(order/lexicographic): use prod.lex and psigma.lex

* update

### [2019-04-10T07:17:03+00:00](https://github.com/leanprover-community/mathlib/commit/899247267dcfc024afae682744399b5f9f9f370e)
fix(category_theory): make the `nat_trans` arrow `⟹` a synonym for the `hom` arrow ([#907](https://github.com/leanprover-community/mathlib/pull/#907))

* removing the nat_trans and vcomp notations; use \hom and \gg

* a simpler proposal

* getting rid of vcomp

* fix

* update notations in documentation

* typo in docs

### [2019-04-10T06:48:16+00:00](https://github.com/leanprover-community/mathlib/commit/f04535de1ce1e0dc5e8f0d8ffb39b61d7aae7d84)
feat(category_theory): iso_whisker_(left|right) ([#908](https://github.com/leanprover-community/mathlib/pull/#908))

* feat(category_theory): iso_whisker_(left|right)

* oops, use old notation for now

* update after merge

### [2019-04-10T02:08:58+00:00](https://github.com/leanprover-community/mathlib/commit/86bd577c14d3ea9efa0e858fb2a19bd61f16e12e)
refactor(algebra/group): is_monoid_hom extends is_mul_hom  ([#915](https://github.com/leanprover-community/mathlib/pull/#915))

* refactor(algebra/group): is_monoid_hom extends is_mul_hom

* Fix build

### [2019-04-10T00:40:05+00:00](https://github.com/leanprover-community/mathlib/commit/f1683a9ed817df1c435a4cf8135e6a2471c6ae1d)
feat(data/set/basic): inclusion map ([#906](https://github.com/leanprover-community/mathlib/pull/#906))

* feat(data/set/basic): inclusion map

* add continuous_inclusion

* minor style change

### [2019-04-10T00:12:57+00:00](https://github.com/leanprover-community/mathlib/commit/96d748eb1d300485a6e718bff79887be8833a08b)
refactor(category_theory): rename `functor.on_iso` to `functor.map_iso` ([#893](https://github.com/leanprover-community/mathlib/pull/#893))

* feat(category_theory): functor.map_nat_iso

* define `functor.map_nat_iso`, and relate to whiskering
* rename `functor.on_iso` to `functor.map_iso`
* add some missing lemmas about whiskering

* some more missing whiskering lemmas, while we're at it

* removing map_nat_iso

### [2019-04-09T22:44:04+00:00](https://github.com/leanprover-community/mathlib/commit/d692499eb622249456dd2abf9b221668924f41ed)
reorganising category_theory/instances/rings.lean ([#909](https://github.com/leanprover-community/mathlib/pull/#909))

### [2019-04-09T19:46:08+00:00](https://github.com/leanprover-community/mathlib/commit/4494001db7c404eb40f9a20024fce38635b55395)
feat(field_theory/subfield): subfields are fields ([#888](https://github.com/leanprover-community/mathlib/pull/#888))

* feat(field_theory/subfield): subfield are fields

* Update subfield.lean

### [2019-04-09T13:38:26-04:00](https://github.com/leanprover-community/mathlib/commit/5c4f5f2088ecd7c16f0547a3e567053c9533a071)
chore(build): allow PRs from separate repos to test deployment scripts

### [2019-04-09T10:16:41-04:00](https://github.com/leanprover-community/mathlib/commit/c2d79f854fa78e55ab53c9c474e3e6079fcecc39)
fix(mergify): require travis "push" check to push ([#913](https://github.com/leanprover-community/mathlib/pull/#913))

This hopefully fixes an error where mergify does not merge a PR is the "pr" build succeeds before the "push" build. In these situations mergify does not merge, because the branch protection settings require both builds to pass.

Unfortunately, there doesn't seem to be an option to change the branch protection settings to only require the "pr" build to pass

### [2019-04-09T13:50:54+01:00](https://github.com/leanprover-community/mathlib/commit/66a86ffe010ffc32ee92e2e92cbdaf83487af168)
refactor(*): rename is_group_hom.mul to map_mul ([#911](https://github.com/leanprover-community/mathlib/pull/#911))

* refactor(*): rename is_group_hom.mul to map_mul

* Fix splits_mul

### [2019-04-09T04:27:55+00:00](https://github.com/leanprover-community/mathlib/commit/eb024dc8402013c2eff69ad4c10308ef62869e9a)
feat(order/lexicographic): lexicographic pre/partial/linear orders ([#820](https://github.com/leanprover-community/mathlib/pull/#820))

* remove prod.(*)order instances

* feat(order/lexicographic): lexicographic pre/partial/linear orders

* add lex_decidable_linear_order

* identical constructions for dependent pairs

* cleaning up

* Update lexicographic.lean

forgotten `instance`

* restore product instances, and add lex type synonym for lexicographic instances

* proofs in progress

* * define lt
* prove lt_iff_le_not_le
* refactoring

### [2019-04-08T22:25:36+01:00](https://github.com/leanprover-community/mathlib/commit/29507a4baa8374d0c7d6f31f360993230d3372e0)
feat(group_theory/subgroup): subtype.add_comm_group ([#903](https://github.com/leanprover-community/mathlib/pull/#903))

### [2019-04-08T17:11:21+00:00](https://github.com/leanprover-community/mathlib/commit/ec51b6e19c79c74a33c4d7d6e0e32cc5cea79258)
feat(category_theory/colimits): missing simp lemmas ([#894](https://github.com/leanprover-community/mathlib/pull/#894))

### [2019-04-08T17:49:51+02:00](https://github.com/leanprover-community/mathlib/commit/6d2cf4ae8701d74ab25b5a2052a5cc30619bed03)
fix(doc/extra/tactic_writing): rename mul_left ([#902](https://github.com/leanprover-community/mathlib/pull/#902)) [ci skip]

*  fix(doc/extra/tactic_writing): rename mul_left

* one more fix

### [2019-04-08T12:50:22+02:00](https://github.com/leanprover-community/mathlib/commit/5f1329a2160126f695af0213eb453f7d27d20342)
feat(linear_algebra/dual): add dual vector spaces ([#881](https://github.com/leanprover-community/mathlib/pull/#881))

* feat(linear_algebra/dual): add dual vector spaces

Define dual modules and vector spaces and prove the basic theorems: the dual basis isomorphism and
evaluation isomorphism in the finite dimensional case, and the corresponding (injectivity)
statements in the general case. A variant of `linear_map.ker_eq_bot` and the "inverse" of
`is_basis.repr_total` are included.

Universe issues make an adaptation of `linear_equiv.dim_eq` necessary.

* style(linear_algebra/dual): adapt to remarks from PR dsicussion

* style(linear_algebra/dual): reformat proof of `ker_eq_bot'`

### [2019-04-08T05:21:27+00:00](https://github.com/leanprover-community/mathlib/commit/10490ea74ea853c2b77f97867072e8802c9a7b52)
feat(analysis/complex/polynomial): fundamental theorem of algebra ([#851](https://github.com/leanprover-community/mathlib/pull/#851))

* feat(data/complex/polynomia): fundamental theorem of algebra

* fix build

* add docstring

* add comment giving link to proof used.

* spag

* move to analysis/complex

* fix data/real/pi

* Update src/analysis/complex/polynomial.lean

Co-Authored-By: ChrisHughes24 <33847686+ChrisHughes24@users.noreply.github.com>

* make Reid's suggested changes

* make Reid's suggested changes

### [2019-04-07T23:05:06-04:00](https://github.com/leanprover-community/mathlib/commit/4fecb101e3bb6bc760f475fee25d0fe06659053e)
feat(topology/gromov_hausdorff): the Gromov-Hausdorff space ([#883](https://github.com/leanprover-community/mathlib/pull/#883))

### [2019-04-08T02:41:50+00:00](https://github.com/leanprover-community/mathlib/commit/5d81ab17f0fe179755768aca4c81de61c49ad024)
trying to work out what was wrong with catching signals ([#898](https://github.com/leanprover-community/mathlib/pull/#898))

### [2019-04-08T01:59:38+00:00](https://github.com/leanprover-community/mathlib/commit/0a49030224662e52a1343f0caa61afaa0a60e9dc)
fix(category_theory): turn `has_limits` classes into structures ([#896](https://github.com/leanprover-community/mathlib/pull/#896))

* fix(category_theory): turn `has_limits` classes into structures

* fixing all the other pi-type typclasses

* oops

### [2019-04-07T19:36:21+02:00](https://github.com/leanprover-community/mathlib/commit/483a6c231913342da585981355dc8f6a6d4c9832)
feat(data/list/min_max): add minimum ([#892](https://github.com/leanprover-community/mathlib/pull/#892))

### [2019-04-07T16:29:19+00:00](https://github.com/leanprover-community/mathlib/commit/891c05060cedcf12aca55c11e96368d382b29c87)
feat(subgroup, subring, subfield): directed Unions of subrings are subrings ([#889](https://github.com/leanprover-community/mathlib/pull/#889))

### [2019-04-07T10:29:26+01:00](https://github.com/leanprover-community/mathlib/commit/bd524fc19fd739d16c3b414988a12ecd3346a98b)
feat(field_theory/subfield): is_subfield instances ([#891](https://github.com/leanprover-community/mathlib/pull/#891))

### [2019-04-07T01:34:16+00:00](https://github.com/leanprover-community/mathlib/commit/7e70ebd05548277458d39dbe3674741d4cfebf8a)
feat(data/nat/basic): b = c if b - a = c - a ([#862](https://github.com/leanprover-community/mathlib/pull/#862))

### [2019-04-06T21:04:01-04:00](https://github.com/leanprover-community/mathlib/commit/3000f32848ab0a48597825ed1e1c9af75c3c5e12)
fix(build): external PRs can't use GitHub credentials

### [2019-04-07T00:21:11+01:00](https://github.com/leanprover-community/mathlib/commit/e4d3ca31cc8393bbed3777dc33512b392d8fa423)
fix(analysis/normed_space/bounded_linear_maps): fix build ([#895](https://github.com/leanprover-community/mathlib/pull/#895))

### [2019-04-06T16:44:31-04:00](https://github.com/leanprover-community/mathlib/commit/31ff5c5ce97e69a37bb7c366650acfbb7f71053e)
refactor(analysis/normed_space/bounded_linear_maps): nondiscrete normed field

### [2019-04-06T16:20:01-04:00](https://github.com/leanprover-community/mathlib/commit/53e7d724c8bc608ff42a6493929a42476f08be78)
fix(appveyor): build every commit

### [2019-04-06T16:14:28-04:00](https://github.com/leanprover-community/mathlib/commit/ae8a1fb6f93d48d88ecc29776738d2d40b4339ff)
refactor(analysis/normed_space/bounded_linear_maps): nondiscrete normed field

### [2019-04-06T15:56:00-04:00](https://github.com/leanprover-community/mathlib/commit/8831e0a7b211a33a984a478eb83d130bf5b94f9d)
chore(mergify): require the AppVeyor build to succeed

### [2019-04-06T15:08:22-04:00](https://github.com/leanprover-community/mathlib/commit/8fa071f4ae265cecb4a4490e6aa6ec05bd81905f)
fix(scripts): not all files were deployed through the curl command ([#879](https://github.com/leanprover-community/mathlib/pull/#879))

### [2019-04-06T18:45:57+00:00](https://github.com/leanprover-community/mathlib/commit/8d45ccb722e916f506e7ab333925e28b2fcdf5a7)
feat(category_theory/bifunctor): simp lemmas ([#867](https://github.com/leanprover-community/mathlib/pull/#867))

* feat(category_theory/bifunctor): simp lemmas

* remove need for @, thanks Kenny and Chris!

### [2019-04-06T16:52:11+00:00](https://github.com/leanprover-community/mathlib/commit/3360f98a53c4c9c64e4e0142bbcde8eacaf55e74)
more general hypotheses for integer induction ([#885](https://github.com/leanprover-community/mathlib/pull/#885))

### [2019-04-06T10:59:07-04:00](https://github.com/leanprover-community/mathlib/commit/d8a2bc51ae535236e8279072422576fc440bc66b)
feat(algebra/opposites): opposites of operators ([#538](https://github.com/leanprover-community/mathlib/pull/#538))

### [2019-04-05T14:05:35-04:00](https://github.com/leanprover-community/mathlib/commit/e0e231da87765c5bc955eda61474603bc5a37715)
fix(build): match build names

### [2019-04-05T13:44:34-04:00](https://github.com/leanprover-community/mathlib/commit/d0f860775f753be9f757afa5e326d5324c8ed9a2)
fix(scripts): protect `leanpkg test` against timeouts

### [2019-04-05T11:21:07-04:00](https://github.com/leanprover-community/mathlib/commit/e809df6d89604424a0ed7824f8882ec4dd2828e8)
fix(scripts): Mac Python's test support doesn't work on Travis

### [2019-04-05T11:07:11-04:00](https://github.com/leanprover-community/mathlib/commit/d9ec8a82c13193bdda66d4b35ae6abbd3ceb3973)
fix(scripts): not all files were deployed through the curl command

### [2019-04-05T14:37:35+00:00](https://github.com/leanprover-community/mathlib/commit/78a08ebc76668bd2ea716aac91c44247e18f8916)
feat(data/mllist): monadic lazy lists ([#865](https://github.com/leanprover-community/mathlib/pull/#865))

* feat(data/mllist): monadic lazy lists

* oops, fix header

* shove into tactic namespace

* make mllist into a monad ([#880](https://github.com/leanprover-community/mathlib/pull/#880))

* make mllist into a monad

* looks good. add `take`, and some tests

* update authors

* cleanup test

### [2019-04-05T06:30:13+00:00](https://github.com/leanprover-community/mathlib/commit/44d1c7aa742679cf9a7d659836fe1c75517a1ffd)
feat(list.split_on): [1,1,2,3,2,4,4].split_on 2 = [[1,1],[3],[4,4]] ([#866](https://github.com/leanprover-community/mathlib/pull/#866))

### [2019-04-05T06:11:40+00:00](https://github.com/leanprover-community/mathlib/commit/901bdbf4e0de3acc8b52d8056d7d34eeb2d6edc2)
feat(data/list/min_max): minimum and maximum over list ([#884](https://github.com/leanprover-community/mathlib/pull/#884))

* feat(data/list/min_max): minimum and maximum over list

* Update min_max.lean

* replace semicolons

### [2019-04-05T04:01:15+00:00](https://github.com/leanprover-community/mathlib/commit/858d111c836b0300b3da0eeeb35fd9922d14a59f)
feat(data/matrix): more basic matrix lemmas ([#873](https://github.com/leanprover-community/mathlib/pull/#873))

* feat(data/matrix): more basic matrix lemmas

* feat(data/matrix): transpose_add

### [2019-04-05T03:14:12+00:00](https://github.com/leanprover-community/mathlib/commit/0b7ee1b4751ed15793d0a25e3b3905f754c41259)
feat(category_theory): introduce the core of a category ([#832](https://github.com/leanprover-community/mathlib/pull/#832))

### [2019-04-04T20:42:02-04:00](https://github.com/leanprover-community/mathlib/commit/b6c2be42e6a2a1c2fbae86107ad2e50c63af971e)
chore(mergify): delete head branch when merging

### [2019-04-04T23:27:46+00:00](https://github.com/leanprover-community/mathlib/commit/7aaccae70a2fd928d68104b199a3ebd5e1a3848e)
feat(algebra/char_p,field_theory/finite_card): cardinality of finite fields ([#819](https://github.com/leanprover-community/mathlib/pull/#819))

* First lemma's added

* fixed lemmas by switching arguments

* vector_space card_fin

* char p implies zmod p module

* Finite field card

* renaming

* .

* bug fix

* move to_module to is_ring_hom.to_module

* fix bug

* remove unnecessary open

* instance instead of thm and remove unnecessary variables

* moved cast_is_ring_hom and zmod.to_module to char_p

* removed redundent nat.prime

* some char_p stuff inside namespace char_p

* fix

* Moved finite field card to a different file

* Removed unnecessary import

* Remove unnecessary lemmas

* Update src/algebra/char_p.lean

Co-Authored-By: CPutz <casper.putz@gmail.com>

* rename char_p lemmas

* Minor changes

### [2019-04-04T16:28:11-04:00](https://github.com/leanprover-community/mathlib/commit/3abfda0e417578eb55a069377317958f0f8e1d88)
chore(github/pr): enable code owners

### [2019-04-04T19:04:48+00:00](https://github.com/leanprover-community/mathlib/commit/8183a5a64c13c5503b106f55729965552f7bfcc9)
feat(data/list/perm): nil_subperm ([#882](https://github.com/leanprover-community/mathlib/pull/#882))

### [2019-04-04T17:16:18+00:00](https://github.com/leanprover-community/mathlib/commit/384c9be2b1ffd08758df803027a6feeca3efa486)
feat (analysis/normed_space/basic.lean): implement reverse triangle inequality ([#831](https://github.com/leanprover-community/mathlib/pull/#831))

* implement reverse triangle inequality

* make parameters explicit

### [2019-04-04T08:21:57-04:00](https://github.com/leanprover-community/mathlib/commit/07aa1e3ea320322ba4fd4f32cb1be7873107924e)
fix(build): fix Lean version

### [2019-04-03T17:19:10-04:00](https://github.com/leanprover-community/mathlib/commit/1c69b609dca390e2ab83fa189aad6242d08cd788)
chore(mergify): fix config

### [2019-04-03T16:22:27-04:00](https://github.com/leanprover-community/mathlib/commit/7762bc4f8a7f48f2cc267ef2cd14f4053661c181)
chore(mergify): fix config file

### [2019-04-03T16:06:06-04:00](https://github.com/leanprover-community/mathlib/commit/d4fd4b2b0afa77f8c31a7a5dadc90a05b9e30795)
chore(mergify): use team names instead of user names

### [2019-04-03T14:56:14-04:00](https://github.com/leanprover-community/mathlib/commit/2230934a3cdec762fa8610f4260dd55149726b41)
chore(mergify): disable `delete_head_branch`

### [2019-04-03T16:30:14+01:00](https://github.com/leanprover-community/mathlib/commit/840ddeb7fa0f60b712cf304f4fca8b24caebb409)
fix(README): fix mergify icon

### [2019-04-03T08:38:06-04:00](https://github.com/leanprover-community/mathlib/commit/542d1790057bc639bc6507f0b4e4872c38313fbc)
chore(github/pr): mergify configuration ([#871](https://github.com/leanprover-community/mathlib/pull/#871))

### [2019-04-03T08:10:21-04:00](https://github.com/leanprover-community/mathlib/commit/a0cbe3be056af2f0e8fc89d45bd969266cbdb844)
feat(data/fin): add `fin.clamp` ([#874](https://github.com/leanprover-community/mathlib/pull/#874))

### [2019-04-03T05:37:35-04:00](https://github.com/leanprover-community/mathlib/commit/2c735dc9c6ad9fac4942d389e37f066cae93f05e)
feat(ring_theory/algebra_operations): submodules form a semiring ([#856](https://github.com/leanprover-community/mathlib/pull/#856))

### [2019-04-03T05:35:05-04:00](https://github.com/leanprover-community/mathlib/commit/b9e9328e2573a58a4e20b19f3c9fc38268573686)
feat(topology/metric_space/completion): completion of metric spaces ([#743](https://github.com/leanprover-community/mathlib/pull/#743))

### [2019-04-03T09:38:15+02:00](https://github.com/leanprover-community/mathlib/commit/c3aba2611ea0b260846c6c49592abd1faf8755cc)
feat(topology/uniform_space/pi): indexed products of uniform spaces ([#845](https://github.com/leanprover-community/mathlib/pull/#845))

* feat(topology/uniform_space/pi): indexed products of uniform spaces

* fix(topology/uniform_space/pi): defeq topology

* fix(src/topology/uniform_space/pi): typo

Co-Authored-By: PatrickMassot <patrickmassot@free.fr>

### [2019-04-03T02:27:59-04:00](https://github.com/leanprover-community/mathlib/commit/7043a4abc00ffedfe28683236a1bd2649263fcc1)
feat(algebra/pointwise): pointwise addition and multiplication of sets ([#854](https://github.com/leanprover-community/mathlib/pull/#854))

### [2019-04-02T21:14:02-04:00](https://github.com/leanprover-community/mathlib/commit/f1120769fe74ef7e20127609dd17404f496cb736)
feat(tactic/basic): add `tactic.get_goal` ([#876](https://github.com/leanprover-community/mathlib/pull/#876))

### [2019-04-02T20:45:14-04:00](https://github.com/leanprover-community/mathlib/commit/e96d6b7522a05d91fd6213fe25953c227086b947)
fix(int/basic): change order of instances to int.cast ([#877](https://github.com/leanprover-community/mathlib/pull/#877))

As discussed at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Problem.20with.20type.20class.20search/near/161848744

Changing the order of arguments lets type class inference fail quickly for `int -> nat` coercions, rather than repeatedly looking for `has_neg` on `nat`.

### [2019-04-02T18:34:18-04:00](https://github.com/leanprover-community/mathlib/commit/ce92e8afc9aaeafeb16efd266f06312facf54594)
chore(.travis.yml): use Lean to determine the Lean version ([#714](https://github.com/leanprover-community/mathlib/pull/#714))

### [2019-04-02T18:33:34-04:00](https://github.com/leanprover-community/mathlib/commit/6c559892f3d95a6dd409cacaf33a87e635e667e3)
build(travis): interrupt the build at the first error message ([#708](https://github.com/leanprover-community/mathlib/pull/#708))

Also make travis_long.sh print its progress messages to stderr.
This sidesteps a mysterious issue where piping the output of
travis_long.sh to another program caused that output to be lost
(probably buffered somewhere?) so Travis would kill the build
after 10 minutes.

### [2019-04-02T11:22:44-04:00](https://github.com/leanprover-community/mathlib/commit/13034ba31b794705b1eedfc27aa61095d517519b)
feat(tactic/local_cache): add tactic-block-local caching mechanism ([#837](https://github.com/leanprover-community/mathlib/pull/#837))

### [2019-04-02T10:44:43-04:00](https://github.com/leanprover-community/mathlib/commit/7eac17850bb71cac8e3a06ae2a84c900538d4b3f)
fix(scripts/update-mathlib): protect file operations from interrupts ([#864](https://github.com/leanprover-community/mathlib/pull/#864))

### [2019-04-02T08:23:50-05:00](https://github.com/leanprover-community/mathlib/commit/f385ad6b40137394530e93e63f4e7bb8967d362e)
Inductive limit of metric spaces ([#732](https://github.com/leanprover-community/mathlib/pull/#732))

### [2019-04-02T07:57:52-04:00](https://github.com/leanprover-community/mathlib/commit/727120cc01b5a3b72220c097969e58a5c03cfd34)
fix(build): improve compatibility of caching scripts with Sourcetree ([#863](https://github.com/leanprover-community/mathlib/pull/#863))

### [2019-04-01T20:04:58-05:00](https://github.com/leanprover-community/mathlib/commit/5694d1524c37716f54e46375fb454e2d5e8202a6)
feat(data/nat/basic): nat.le_rec_on ([#585](https://github.com/leanprover-community/mathlib/pull/#585))

### [2019-04-01T18:55:36-04:00](https://github.com/leanprover-community/mathlib/commit/8e4542dafe1f170b9b48d2293ad71e80a18dac87)
Merge branch 'congr-2'

### [2019-04-01T18:52:21-04:00](https://github.com/leanprover-community/mathlib/commit/ec0a4ea1b78edb77ca731499aee000466fe45d22)
fix(tactic/congr'): some `\iff` goals were erroneously rejected

### [2019-04-01T16:48:53-04:00](https://github.com/leanprover-community/mathlib/commit/5fe470bb216e7b3fb6639d3b964c4eee36b88713)
feat(tactic/push_neg): a tactic pushing negations ([#853](https://github.com/leanprover-community/mathlib/pull/#853))

### [2019-04-01T16:21:09-04:00](https://github.com/leanprover-community/mathlib/commit/5995d460bc69535ecde4b49fd8af23befed1ac8e)
fix(build): prevent leanchecker from timing out

### [2019-04-01T16:13:58-04:00](https://github.com/leanprover-community/mathlib/commit/2f088fc1cb98c6e789f3c61e594e9c85a121d139)
feat(category_theory): working in Sort rather than Type ([#824](https://github.com/leanprover-community/mathlib/pull/#824))

### [2019-04-01T22:07:28+02:00](https://github.com/leanprover-community/mathlib/commit/404e2c932ed466594bea9b175a73a37034f3e916)
add tutorial about zmod37 ([#767](https://github.com/leanprover-community/mathlib/pull/#767))

Reference to a mathlib file which no longer exists has been fixed, and a more user-friendly example of an equivalence relation has been added in a tutorial.

### [2019-04-01T21:58:17+02:00](https://github.com/leanprover-community/mathlib/commit/867661e0a74f806048b95ea74b5d9c8c276888e2)
docs(tactics): add introduction to the instance cache tactic section

### [2019-04-01T21:55:31+02:00](https://github.com/leanprover-community/mathlib/commit/59e059301dfd7b9108eab11dec43678e8a63fb03)
docs(tactics): minor rewrite of exactI, resetI etc

I always found these tactics confusing, but I finally figured out what they do and so I rewrote the docs so that I understand them better.

### [2019-04-01T15:08:22-04:00](https://github.com/leanprover-community/mathlib/commit/a1fe39b1893fe9eba697024569f62ac00edfe02a)
refactor(analysis/convex): make instance local ([#869](https://github.com/leanprover-community/mathlib/pull/#869))

### [2019-04-01T14:48:06-04:00](https://github.com/leanprover-community/mathlib/commit/3bc0f00accb692b6d2febdae4657a3115d591eb0)
fix(scripts/cache-olean): only run the post-checkout hook if we actually changed branches ([#857](https://github.com/leanprover-community/mathlib/pull/#857))

### [2019-04-01T03:01:21-04:00](https://github.com/leanprover-community/mathlib/commit/2851236bf5e39e2520648931a62db1f6face3acb)
feat(data/real/pi): Compute the first three digits of pi ([#822](https://github.com/leanprover-community/mathlib/pull/#822))

### [2019-03-31T21:33:03+02:00](https://github.com/leanprover-community/mathlib/commit/c91e6c2eb882b0fea4f4bdbba2b1c498cdf40da1)
fix(ring_theory/algebra): remove duplicate theorems to fix build

### [2019-03-31T08:35:59-04:00](https://github.com/leanprover-community/mathlib/commit/9480df500e35198ea621b910e6a3761aac6ed869)
refactor(computability): unpack fixed_point proof

### [2019-03-31T08:35:21-04:00](https://github.com/leanprover-community/mathlib/commit/359cac1bfa1643759c1784bfc31880a0c31b0c56)
feat(computability): computable_iff_re_compl_re

### [2019-03-31T08:32:21-04:00](https://github.com/leanprover-community/mathlib/commit/514de772beea5e039ca091e5b26db509d4ea1564)
feat(data/finset): to_finset_eq_empty

### [2019-03-31T08:31:39-04:00](https://github.com/leanprover-community/mathlib/commit/72634d2c5ca048582107778aab164ac12aba0d40)
feat(data/complex/basic): smul_re,im

### [2019-03-31T00:48:41+00:00](https://github.com/leanprover-community/mathlib/commit/e1c035dae399a97a79f0f0c8a05ffc3d23860e22)
feat(data/polynomial): eval₂_neg

### [2019-03-29T23:56:28+00:00](https://github.com/leanprover-community/mathlib/commit/c2bb4c5cf85ba25891cd58f96f6073c4d4df758e)
refactor(data/zsqrtd/basic): move zsqrtd out of pell and into data ([#861](https://github.com/leanprover-community/mathlib/pull/#861))

### [2019-03-29T15:03:34-05:00](https://github.com/leanprover-community/mathlib/commit/dc7de46067dce93fae02ee5f2877c0f2c714d67d)
feat(analysis/convex): convex sets and functions ([#834](https://github.com/leanprover-community/mathlib/pull/#834))

### [2019-03-29T13:08:29-04:00](https://github.com/leanprover-community/mathlib/commit/171e913a33a3a47de695909ffe00ed13ba7a7c14)
fix(scripts/remote-install-update-mathlib): add GitPython dependency ([#860](https://github.com/leanprover-community/mathlib/pull/#860))

### [2019-03-28T22:56:01-04:00](https://github.com/leanprover-community/mathlib/commit/2e7f0099d2e97b370de475f8e7854f5557c265b7)
fix(scripts/deploy_nightly): pushing to the `lean-3.4.2` branch is sometimes blocked ([#859](https://github.com/leanprover-community/mathlib/pull/#859))

### [2019-03-28T22:11:15-04:00](https://github.com/leanprover-community/mathlib/commit/a4fd55ca3ea38fa0b23ca6af92e3537b0d3321e8)
feat(library_search): a simple library_search function ([#839](https://github.com/leanprover-community/mathlib/pull/#839))

### [2019-03-28T20:04:39-04:00](https://github.com/leanprover-community/mathlib/commit/59caf112e06370162a4c267d16573d7b8d2dc901)
fix(scripts/update-mathlib): fix imports of python files

### [2019-03-28T19:11:34-04:00](https://github.com/leanprover-community/mathlib/commit/6cd336cbe3e939f175393a87c6df213f1472a2fb)
fix(scripts/update-mathlib): github authentication

### [2019-03-28T16:32:00-04:00](https://github.com/leanprover-community/mathlib/commit/1c04a32901a3f8d20f166a0a1acf9e6cdfbde052)
fix(scripts/update-mathlib): update-mathlib shouldn't need github authentication

### [2019-03-28T14:01:35-04:00](https://github.com/leanprover-community/mathlib/commit/48df32191c68ed20e69b49aa831e5aaab6da4bb5)
feat(category_theory/instances): category of groups ([#749](https://github.com/leanprover-community/mathlib/pull/#749))

### [2019-03-28T16:25:01+00:00](https://github.com/leanprover-community/mathlib/commit/179d4d0890d8a4fe0d043849e6c9df2bb1bf52d2)
refactor(*): unify group/monoid_action, make semimodule extend action ([#850](https://github.com/leanprover-community/mathlib/pull/#850))

* refactor(*): unify group/monoid_action, use standard names, make semimodule extend action

* Rename action to mul_action

* Generalize lemmas. Also, add class for multiplicative action on additive structure

* Add pi-instances

* Dirty hacky fix

* Remove #print and set_option pp.all

* clean up proof, avoid diamonds

* Fix some build issues

* Fix build

* Rename mul_action_add to distrib_mul_action

* Bump up the type class search depth in some places

### [2019-03-27T21:28:39-04:00](https://github.com/leanprover-community/mathlib/commit/25bab564d914474f5627fd287ad9f6ffc7e0d79e)
feat(scripts/cache_olean): cache and fetch olean binaries ([#766](https://github.com/leanprover-community/mathlib/pull/#766))

* script setup and documentation
* fetch mathlib nightly when relevant
* use credentials to access `github.com`
* locate correct git directory, and add prompt
* add confirmation message to setup-dev-scripts
* adding --build-all option

### [2019-03-27T21:47:02+01:00](https://github.com/leanprover-community/mathlib/commit/8838ff3598406fe1fd02f3fd27202f734d1799d9)
feat(algebra/field_power): add fpow_one, one_fpow, fpow_mul, mul_fpow (closes [#855](https://github.com/leanprover-community/mathlib/pull/#855))

### [2019-03-27T20:15:04+01:00](https://github.com/leanprover-community/mathlib/commit/842935433b3a817b5fcbc5f13c7e3d2702477b8c)
feat(analysis): add real.rpow_le_one

### [2019-03-27T20:15:04+01:00](https://github.com/leanprover-community/mathlib/commit/4305ad62333b7eac3df207f63be3a3a05841a0bb)
feat(analysis): add rpow_pos_of_pos

### [2019-03-27T09:57:35-05:00](https://github.com/leanprover-community/mathlib/commit/02ca4942fb3cbef854713e46a6d8cf9dba2e09aa)
Remove outparam in normed space ([#844](https://github.com/leanprover-community/mathlib/pull/#844))

### [2019-03-27T08:20:35-04:00](https://github.com/leanprover-community/mathlib/commit/52fddda2a44a9ad70ab4bffb92e3259862ed365c)
feat(algebra/archimedean): lemmas about powers of elements ([#802](https://github.com/leanprover-community/mathlib/pull/#802))

### [2019-03-26T16:35:47-05:00](https://github.com/leanprover-community/mathlib/commit/17e40bbe61b3fe0b97ca6f29ca51e3857761ea1a)
feat(tactic/congr): apply to `iff` propositions ([#833](https://github.com/leanprover-community/mathlib/pull/#833))

### [2019-03-26T21:53:30+01:00](https://github.com/leanprover-community/mathlib/commit/c3a902852838e1552e991d84434c0f21927250d4)
fix(data/polynomial): (nat_)degree_map' assumed a comm_ring instead of a comm_semiring

### [2019-03-26T19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/a0166524693c1a0fad0f0ef06fef21b2e47e3216)
feat(data/finset): add range_add_one'

### [2019-03-26T19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/0ea37e90f3d26f6b7c7415d0796ea85b37f3195f)
feat(algebra/big_operators): add prod_map, sum_map

### [2019-03-26T19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/d3c68fc6463f9254550c8d3a14f3f29a575023ea)
feat(analysis/normed_space): tendsto_zero_iff_norm_tendsto_zero

### [2019-03-26T19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/df08058b641bb12dadafc1b60087bd95431a51a8)
refactor(analysis/normed_space): rename norm_mul -> norm_mul_le; use norm_mul for the equality in normed fields; and norm_mul_le for the inequality in normed_rings

### [2019-03-26T18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/bd21b0edb9981228b2a90ab2dabaf39b041ae492)
feat(analyis/normed_space): add normed_field instance for ℂ

### [2019-03-26T18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/a01cf8682690ab6e6b8002b4cfdd8540d125b934)
feat(data/multiset,data/finset): add multiset./finset.le_sum_of_additive

### [2019-03-26T18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/c9122539c2220c1e5f1179282c1bd9def4ac1c74)
feat(algebra/group_power): add lt_of_pow_lt_pow

### [2019-03-26T18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/fd37f9615e393623b434415f30bb6396b83bd199)
feat(data/fin): add injective_cast_le

### [2019-03-26T18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/c0c2edb163a10c282581c96721f9824379f681cb)
feat(algebra/big_operators): add Gauss' summation formula

### [2019-03-26T18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/cfeb887be96e31662dbb86d81cc1af81a9e63913)
feat(data/polynomial): degree_map', nat_degree_map' semiring variant of degree_map, nat_degree_map

### [2019-03-26T18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/aa2c6e222d31eaf1feb499738dfdf519a4a7d556)
feat(data/mv_polynomial): more about renaming

### [2019-03-26T18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/5b73f46b4b6d498c8b4f6b6774fd337466e80c67)
chore(data/mv_polynomial): use type name as filename

### [2019-03-26T18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/8ccca3f7b7731aeabfdddff3415bad7a026502dd)
feat(data/finsupp): add emb_domain

### [2019-03-26T18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/d7bd41ff9873c0169af1a9e90db5600d53eae18d)
feat(linear_algebra/dimension): add exists_mem_ne_zero_of_dim_pos

### [2019-03-26T18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/22352ff251318cbfdef4407efa6ce6f1c9c2d0d6)
feat(linear_algebra/dimension): add dim_span_le; add rank_finset_sum_le

### [2019-03-26T17:46:31+01:00](https://github.com/leanprover-community/mathlib/commit/f882b8b771f2fbfba998e305e84ac1bf71f055ed)
feat(data/polynomial): rec_on_horner ([#739](https://github.com/leanprover-community/mathlib/pull/#739))

### [2019-03-26T00:11:19+00:00](https://github.com/leanprover-community/mathlib/commit/410ae5d9ec48843f0c2bf6787faafaa83c766623)
feat(group_theory/subgroup): add inv_iff_ker' and related ([#790](https://github.com/leanprover-community/mathlib/pull/#790))

* feat(group_theory/subgroup): add inv_iff_ker' and related

* correcting spacing and adding to_additive attribute

* changing name to ker-mk

### [2019-03-25T16:03:35-04:00](https://github.com/leanprover-community/mathlib/commit/0bb64a21d682966ef1cfc47c62c74a7a54bdf202)
feat(tactic/solve_by_elim): working with multiple goals ([#838](https://github.com/leanprover-community/mathlib/pull/#838))

### [2019-03-25T19:21:49+00:00](https://github.com/leanprover-community/mathlib/commit/291a4f35f5b8def0f2e5158ebc222ffd8a6113d5)
refactor(algebra/group_action): use notation for monoid/group actions ([#846](https://github.com/leanprover-community/mathlib/pull/#846))

* refactor(module_action): bundle and introduce notation

* fix(linear_algebra/determinant): fix the coercion issue using a local notation

* fix(linear_algebra/dimension): fix build

### [2019-03-25T18:24:08+00:00](https://github.com/leanprover-community/mathlib/commit/a1158d84b8c495f1c07ebb92d65efc62f953f9f7)
feat(algebra/module): every abelian group is a Z-module ([#848](https://github.com/leanprover-community/mathlib/pull/#848))

### [2019-03-25T16:59:27+01:00](https://github.com/leanprover-community/mathlib/commit/cb5e185f4053013e29ff8823385efe9f04d749e8)
refactor(data/equiv): equiv_injective_surjective ([#849](https://github.com/leanprover-community/mathlib/pull/#849))

### [2019-03-23T21:28:16+01:00](https://github.com/leanprover-community/mathlib/commit/cd7402d684e4c3b2b304334d754c610baaf3a6d7)
Minor clarification to simpa doc ([#842](https://github.com/leanprover-community/mathlib/pull/#842))

### [2019-03-23T12:56:54-04:00](https://github.com/leanprover-community/mathlib/commit/b0b33abe49524f47a328b4507500da0c68f24d3a)
fix(import): remove relative imports

### [2019-03-22T16:02:14+00:00](https://github.com/leanprover-community/mathlib/commit/c29769f7f15fca6df78b44491c8e091e8b6ea60e)
fix(ring_theory/multiplicity): correct spelling mistake in docstring

### [2019-03-22T13:22:43+01:00](https://github.com/leanprover-community/mathlib/commit/b5bb4469a71fd6908719c5dfacf5304d0f8757f5)
fix(doc/extra/tactic_writing): fix a minor error ([#841](https://github.com/leanprover-community/mathlib/pull/#841)) [ci-skip]

* fix(doc/extra/tactic_writing): fix a minor error

* comma splice

### [2019-03-22T00:28:38+00:00](https://github.com/leanprover-community/mathlib/commit/989efabacf04705b71e1032cac81e92f4ac9fa6a)
feat(data/equiv/algebra): add add_equiv and mul_equiv ([#789](https://github.com/leanprover-community/mathlib/pull/#789))

* feat(data/equiv/algebra): add monoid_equiv and group_equiv

* refactor; now using mul_equiv; adding add_equiv

* tidy

* namechange broke my code; now fixed

* next effort

* switching is_mul_hom back to explicit args

* removing more implicits

* typo

* switching back to implicits (to fix mathlib breakage)

* Making is_mul_hom and is_add_hom classes

* adding more to_additive

### [2019-03-21T23:44:25+00:00](https://github.com/leanprover-community/mathlib/commit/798a08d49b16874884954d9b412bc0ff4152c85e)
feat(group_theory/submonoid): add closure_singleton ([#810](https://github.com/leanprover-community/mathlib/pull/#810))

* feat(group_theory/submonoid): add closure_singleton

* adding some to_additive

### [2019-03-20T10:16:08-04:00](https://github.com/leanprover-community/mathlib/commit/098c2cb1d1dab5f42260a6fe999abc252ceba313)
feat(tactic/wlog): `discharger` defaults to classical `tauto` ([#836](https://github.com/leanprover-community/mathlib/pull/#836))

### [2019-03-18T00:04:29+00:00](https://github.com/leanprover-community/mathlib/commit/d60d1616958787ccb9842dc943534f90ea0bab64)
feat(linear_algebra/basic): add ring instance ([#823](https://github.com/leanprover-community/mathlib/pull/#823))

### [2019-03-17T21:08:06+00:00](https://github.com/leanprover-community/mathlib/commit/9ff5e8d7f4563358cf6aabb046f4df565e279536)
feat(algebra/punit_instances): punit instances ([#828](https://github.com/leanprover-community/mathlib/pull/#828))

### [2019-03-17T21:07:14+00:00](https://github.com/leanprover-community/mathlib/commit/df996be42a558cfeeda0d03da50c08c61f2c0a03)
fix(topology/algebra/group): fix binders for top group extensionality ([#826](https://github.com/leanprover-community/mathlib/pull/#826))

### [2019-03-17T09:07:33-05:00](https://github.com/leanprover-community/mathlib/commit/e8bdc7fc14c6d56d4040892d16929f310e9d03d5)
feat(order/filter/filter_product): build hyperreals ([#801](https://github.com/leanprover-community/mathlib/pull/#801))

Construction of filter products, ultraproducts, some instances, hyperreal numbers.

### [2019-03-16T09:30:48-05:00](https://github.com/leanprover-community/mathlib/commit/0c2c2bdd49d9e9499d9814446b12529c00012a9a)
feat(group_theory/perm/cycles): cycle_factors ([#815](https://github.com/leanprover-community/mathlib/pull/#815))

### [2019-03-16T09:28:41-05:00](https://github.com/leanprover-community/mathlib/commit/7b001c9cc85456fbf6356b4813ff9af05338b32b)
feat(data/set/intervals): add missing intervals + some lemmas ([#805](https://github.com/leanprover-community/mathlib/pull/#805))

The lemmas about Icc ⊆ I** are important for convexity

### [2019-03-14T10:32:41+01:00](https://github.com/leanprover-community/mathlib/commit/2bf44d312d5f5f358ce8d9e682c23238e2e86429)
refactor(*): rename metric_space_subtype to subtype.metric_space ([#817](https://github.com/leanprover-community/mathlib/pull/#817))

### [2019-03-14T10:31:53+01:00](https://github.com/leanprover-community/mathlib/commit/c5afc52a76bf586ff5ebce09d42a28fd0cd63d4b)
feat(topology/metric_space/baire): Baire theorem ([#816](https://github.com/leanprover-community/mathlib/pull/#816))

### [2019-03-13T23:45:07-04:00](https://github.com/leanprover-community/mathlib/commit/72100bd5b3c215d3f3cb77d92a199aff186d007a)
feat(tactic/squeeze,hole): remove needless qualifications in names

### [2019-03-12T13:37:46-04:00](https://github.com/leanprover-community/mathlib/commit/82f79a58df3047b8002bbaf90ce50da2a978e114)
feat(data/list|multiset|finset): lemmas about intervals in nat ([#795](https://github.com/leanprover-community/mathlib/pull/#795))

### [2019-03-12T13:53:34+01:00](https://github.com/leanprover-community/mathlib/commit/2738f9b4aa19d525d30c9b284468c5b9cc5de1d1)
chore(topology/*): @uniformity α _ becomes 𝓤 α ([#814](https://github.com/leanprover-community/mathlib/pull/#814))

This is a binder type change and a local notation

### [2019-03-12T01:04:54-04:00](https://github.com/leanprover-community/mathlib/commit/3360267010e8505a53c810c78905d4d7ca4768bb)
feat(tactic/basic): folding over the environment, to get all declarations ([#798](https://github.com/leanprover-community/mathlib/pull/#798))

### [2019-03-11T16:11:52-04:00](https://github.com/leanprover-community/mathlib/commit/bde8690e663fd083091462ed2b52c6ddbe6f6096)
feat(data/alist,data/finmap): union ([#750](https://github.com/leanprover-community/mathlib/pull/#750))

### [2019-03-11T17:09:10+01:00](https://github.com/leanprover-community/mathlib/commit/eb96a25d539fa954177bd03c3914ca229f8547b1)
feat(topology/algebra/group): extensionality for top group structure

### [2019-03-11T14:06:20+00:00](https://github.com/leanprover-community/mathlib/commit/69249d8b51079734ad894ad9e9952080e1655ac7)
feat(topology/algebra/monoid): add is_submonoid.mem_nhds_one ([#809](https://github.com/leanprover-community/mathlib/pull/#809))

### [2019-03-09T17:49:20-05:00](https://github.com/leanprover-community/mathlib/commit/51c31cea3e506ce8a565a828ee71dc265cc0c8e0)
refactor(data/list): rm redundant eq_nil_of_forall_not_mem ([#804](https://github.com/leanprover-community/mathlib/pull/#804))

### [2019-03-09T11:34:38+00:00](https://github.com/leanprover-community/mathlib/commit/e8818faf3a96d664b8366ff079691c94c7620384)
feat(data/set/finite): add finite_lt_nat ([#807](https://github.com/leanprover-community/mathlib/pull/#807))

### [2019-03-08T20:10:50+00:00](https://github.com/leanprover-community/mathlib/commit/7de57e84c5231c3876ed5f9c9e448dc7e0d7cb9e)
feat(ring_theory/noetherian): Nakayama's Lemma ([#778](https://github.com/leanprover-community/mathlib/pull/#778))

* feat(ring_theory/noetherian): Nakayama's Lemma

* Update src/ring_theory/noetherian.lean

Co-Authored-By: kckennylau <kc_kennylau@yahoo.com.hk>

### [2019-03-08T15:01:45+01:00](https://github.com/leanprover-community/mathlib/commit/1159fa95961f2fa7e8bf4fee0d4cdf5d6242bc09)
refactot(data/equiv/basic): rename apply_inverse_apply to apply_symm_apply ([#800](https://github.com/leanprover-community/mathlib/pull/#800))

### [2019-03-08T13:42:54+01:00](https://github.com/leanprover-community/mathlib/commit/b1af14029c94c0b292448ada06aa16002ef6090c)
style(data/list/basic): clean up count_bag_inter

### [2019-03-08T08:46:58+01:00](https://github.com/leanprover-community/mathlib/commit/ffa6d6992c4de076154fdefad79c2488bcb48bbd)
feat(*): has_mem (set α) (filter α) ([#799](https://github.com/leanprover-community/mathlib/pull/#799))

### [2019-03-07T23:35:39+01:00](https://github.com/leanprover-community/mathlib/commit/7e77967706fcb7c1bb22ac8a235506b7a79bacc3)
refactor(localization): shorten proofs ([#796](https://github.com/leanprover-community/mathlib/pull/#796))

* feat(algebra/group): units.coe_map

* refactor(localization): shorten proofs

*  swap order of equality in ring_equiv.symm_to_equiv

### [2019-03-07T10:17:21-05:00](https://github.com/leanprover-community/mathlib/commit/26bd400b91bc1c96ad787cd67140067ab3c6939d)
feat(data/list): lemmas about count and bag_inter ([#797](https://github.com/leanprover-community/mathlib/pull/#797))

### [2019-03-06T20:07:22-05:00](https://github.com/leanprover-community/mathlib/commit/181647bb4c1ca43b32674234b79becea85335e4d)
feat(tactic/basic): utility functions for names ([#791](https://github.com/leanprover-community/mathlib/pull/#791))

### [2019-03-06T23:01:10+00:00](https://github.com/leanprover-community/mathlib/commit/48eaf05b7556aa6912988668f3377b8e8e03c043)
feat(algebra/group): units.coe_map

### [2019-03-06T22:11:42+00:00](https://github.com/leanprover-community/mathlib/commit/e286452d65bac5e4918ed1826012877abf67bc0b)
feat(data/nat/basic): some lemmas ([#792](https://github.com/leanprover-community/mathlib/pull/#792))

* feat(data/nat/basic): some lemmas

* fixing namespace, moving lemma

### [2019-03-06T10:16:34-05:00](https://github.com/leanprover-community/mathlib/commit/61e02dd26c07eb4cb44783ba9eaa16384cf31594)
feat(data/finset): missing fold_map lemma ([#794](https://github.com/leanprover-community/mathlib/pull/#794))

### [2019-03-06T14:21:24+00:00](https://github.com/leanprover-community/mathlib/commit/cc753d7b8c488e72cdf5f3a9046c90dca0303d58)
feat(ring_theory/localization): adds induced ring hom between fraction rings ([#781](https://github.com/leanprover-community/mathlib/pull/#781))

* feat(ring_theory/localization): adds induced ring hom between fraction rings

* Break some extremely long lines

* Put map in the fraction_ring namespace

* Move global variable into statements

* Rename rec to lift', make interface for lift, generalise map

* Improve simp-lemmas, add docstrings

* Rename circ to comp in lemma names

### [2019-03-05T21:55:19+01:00](https://github.com/leanprover-community/mathlib/commit/1ec0a1f49db97d45e8666a3bf33217ff79ca1d87)
fix(tactic/linarith): correctly parse 0*0

### [2019-03-05T14:15:40-05:00](https://github.com/leanprover-community/mathlib/commit/581cf19bf1885ef874c39c9902a93f579bc8c22d)
feat(topology): split uniform_space and topological_structure

### [2019-03-05T09:50:45+01:00](https://github.com/leanprover-community/mathlib/commit/708c0cfaf3ec074c90fa0c4f06c03cda64913419)
feat(data/multiset): add monad instance ([#744](https://github.com/leanprover-community/mathlib/pull/#744))

### [2019-03-05T09:44:51+01:00](https://github.com/leanprover-community/mathlib/commit/3525d212e3b3166b2f3cf1a5dc89114962630168)
refactor(topology/metric_space/lipschitz): Simplify proof in banach contraction ([#788](https://github.com/leanprover-community/mathlib/pull/#788))

### [2019-03-05T09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/b9f88d14bcf78da3c9dffcbd0f52ff48d67c77b8)
feat(data/finset): add card_sdiff

### [2019-03-05T09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/682f4b5a43b55540d6dfbe5f76626a4a7ce9398b)
feat(linear_algebra): module (vector space) structure for finsupp, matrix, and mv polynomials

### [2019-03-05T09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/738778aa8e88fd0cff5c24e0e87449d4b7575a56)
feat(data/matrix): basic definitions: transpose; row & column matrix; vector/matrix multiplication

### [2019-03-05T09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/528ff9337f56844c18cb53e70faf432cf6599092)
refactor(linear_algebra): move multivariate_polynomial to data

### [2019-03-05T09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/891a192fd86bcd8b0e75b828657d4c6bb012129d)
refactor(ring_theory): move matrix to data and determinant to linear_algebra

### [2019-03-05T09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/10a586b1d82098af32e13c8d8448696022132f17)
feat(linear_algebra): add module (vector_space) structure for function spaces

### [2019-03-05T09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/332121d42c1b96ecda72bbb3d6fc0503b0022fec)
feat(data/fintype): card_univ and card_univ_diff

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c0b1eb19dc3dd79152bcddf4bc325e1775f5d7b9)
refactor(data/finset): correct name sdiff_disjoint -> disjoint_sdiff; add sdiff_disjoint

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/b3c749b4b1d38ee7b80cbdff95addea3038c34b7)
remove superflous parameter from bot_eq_zero

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/73f1a08dfad73cce90780c92218321cdbf5527fa)
feat(data/finset): add filter_empty, filter_subset_filter, prod_filter

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/b9ead4d5446607a20561353acf82fa87d9d6695f)
feat(data/finset): add disjoint_bind_left/right

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/f82f5f2a93c787fbaa8e52b131db9fab29f4bf56)
refactor(algebra): canonically_ordered_monoid extends order_bot

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/f07a558dba53541ba610ed1d9cfb0b8d230fb788)
feat(data/equiv): add subtype_pi_equiv_pi

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/8070c05ccd61cd930be2c2c4a95c075635f5c404)
feat(data/set/lattice): more rules for disjoint sets

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c53ac415cb515f30c7497c80e50f59c4bc3b8f33)
feat(data/set): relate range and image to Union

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/41038bac0e9d47c0b6051c6ed72db95fa814789f)
feat(data/set): add exists_maximal_wrt

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/146d73c60dad5a6500dfda6029ddc95eed4ddc5e)
feat(data/set): add finite_image_iff_on

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/84a5f4d301072ffbb05ac387a1ba5cc5167e2bad)
feat(data/set): add subset_image_iff and subset_range_iff

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/cbe2f6171c478ca088fa6d7570853d2eaff13a01)
feat(logic/function): add inv_fun_neg

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/73db4c7c7ecce1dacb3036538b1eb50ea1cb6bb5)
feat(logic/function): add injective.ne

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c819617b7e146dffc8c3c359ce186ca5068ec809)
feat(logic): add plift.down_inj

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/985445f6b62a55483563352651981a207915bf05)
feat(linear_algebra/multivariate_polynomial): relate total_degree to degrees, add, zero, mul

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/78fd58ddfe89591347db6daefcc7afea9347d351)
feat(linear_algebra/multivariate_polynomial): add degrees

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c2d8bc2d3a19d154dcc4695ac1c5c1a8aebd0147)
feat(data/finsupp): relatie to_multiset to 0, +, single, card, map, prod, and to_finset

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/857842d0a722c98f7acd20976103e44765ee4447)
feat(data/finsupp): add support_mul

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/a77797f96826528000f7bbe54341b72e06e496be)
feat(data/multiset): add prod_smul

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/e9247457c8417b29f3a0f7e99f0a328f0cc5b123)
feat(data/finset): add multiset.count_sup

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/e07cac5499750def44ec7d199d8d1de8f41f7a77)
feat(data/finset): add to_finset_smul

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/f24b01be640a0e41e0bde67acf359d836b387a9a)
feat(algebra/group_power): smul and pow are monoid homs

### [2019-03-05T09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/32642e17a274c4767f980be008807b282b41b27e)
feat(linear_algebra): add dim_sup_add_dim_inf_eq

### [2019-03-04T16:26:09+01:00](https://github.com/leanprover-community/mathlib/commit/f46f0a6719da61ff7daaa24b5cc1ec02bfb88ff3)
feat(tactic/fin_cases): case bashing on finset, list, and fintype hypotheses. ([#775](https://github.com/leanprover-community/mathlib/pull/#775))

### [2019-03-04T12:37:27+01:00](https://github.com/leanprover-community/mathlib/commit/6cd0341ae21de7cd2ede4fdfd015e22f5fb2d1b1)
docs(extras/tactic_writing): add ``%%(reflect n)`` to the tactic writing guide ([#786](https://github.com/leanprover-community/mathlib/pull/#786))

### [2019-03-03T19:05:12+01:00](https://github.com/leanprover-community/mathlib/commit/201413b920eb737184fa05c0d0411734909e90e5)
chore(topology): Splits topology.basic and topology.continuity ([#785](https://github.com/leanprover-community/mathlib/pull/#785))

Also, the most basic aspects of continuity are now in topology.basic

### [2019-03-03T11:01:43-05:00](https://github.com/leanprover-community/mathlib/commit/108486871aa0a7f0afd221c191766e9bebefde82)
feat(analysis/{specific_limits,infinite_sum}): Cauchy of geometric bound ([#753](https://github.com/leanprover-community/mathlib/pull/#753))

### [2019-03-03T13:19:35+00:00](https://github.com/leanprover-community/mathlib/commit/1f90e189759a929a0dfa3545f59118efc89b4f31)
feat(ring_theory/ideal_operations): Chinese Remainder Theorem ([#774](https://github.com/leanprover-community/mathlib/pull/#774))

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/fb8001d6fd786a67e01d022241f01b7017ae0825)
hopefully fixed for good this time

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/182b2a3f14b6641151d426f1f531d6b175f0509c)
fix properly

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/a4cc8b725e19b63299e6dd14271579e7c9a0c6ab)
fix build

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/a75d57cb2cecf19c8b7534f677af6510c76fea21)
fix build

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/8dcd0718e5d685b71a68c7bd3f3e40366b500e9f)
generalize norm to zsqrtd

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/d98cae7f48b06f330b795459461035fe44b961be)
fix build

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/5cbd7fa7af70f3c59f6d16cdd427bc4701bc3efe)
changing names

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/a9dfabacd85e3a0d6e30263263724ec859a1579d)
The year is 2019

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/c36470f7ab2848b1db664536a72a3f8445c24e30)
put sum_two_squares in nat.prime namespace

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/d8f0921af75d5c6196a735ef0022773126d1d19b)
move lemmas to correct places

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/4e48324bf10f0c5fb2665bf26279daff82a84cf9)
fix build

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/9c9aee4545a22c07fd2d8cf997fb1947d29cdc92)
finish proof of sum two squares

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/bd86c0da6f23b202ebdb7b30209e990e2234b6a1)
commit properly

### [2019-03-02T17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/49a85f48453a2837f3af9ffe13e980a7d8edc867)
prove Z[i] is a euclidean_domain

### [2019-03-02T19:55:17+00:00](https://github.com/leanprover-community/mathlib/commit/1f4f2e421f30390efca68776a4850f471cc72169)
refactor(*): move matrix.lean to data/ and determinant.lean to linear_algebra/ ([#779](https://github.com/leanprover-community/mathlib/pull/#779))

### [2019-03-01T22:25:45-05:00](https://github.com/leanprover-community/mathlib/commit/8fbf296d9a50aaf7ea56832ac208a4ed6bbcae8e)
feat(topology/metric_space/hausdorff_distance): Hausdorff distance

### [2019-03-01T21:24:00-05:00](https://github.com/leanprover-community/mathlib/commit/be88ceca99871e9f7922728d29921d87197ebe0b)
feat(analysis/exponential): added inequality lemmas

### [2019-03-01T21:15:38+00:00](https://github.com/leanprover-community/mathlib/commit/0bb0cec5e27b8a9b52f3b6e70b989d81d206a0dc)
feat(group_theory): free_group and free_abelian_group are lawful monads ([#737](https://github.com/leanprover-community/mathlib/pull/#737))

### [2019-03-01T21:14:41+00:00](https://github.com/leanprover-community/mathlib/commit/116cffffffa7d15ffc305e0d52e1b5b5e34d3659)
feat(data/zmod/basic): cast_mod_nat' and cast_mod_int' ([#783](https://github.com/leanprover-community/mathlib/pull/#783))

* cast_mod_int'

* cast_val_int'

### [2019-03-01T10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/04b5f885908757bcb3830e21f37d9f38e0d3bf6d)
refactor(analysis/asymptotics): minor formatting changes

### [2019-03-01T10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/6363212d4b8746d53ae0b7f14bef8e0085ffcb63)
feat(analysis/normed_space/deriv): generalize to spaces over any normed field

### [2019-03-01T10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/89b8915e8f407089b7223f2c081b5877d5c9307a)
feat(analysis/normed_space/deriv): add readable proof of chain rule

### [2019-03-01T10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/5dd1ba5871ad359073e8739f5613db73fcf21b23)
feat(analysis/*): is_bigo -> is_O, is_littleo -> is_o

### [2019-03-01T10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/49ecc7b064c9f3a777b9ce67a761590b1fd02021)
fix(*): fix things from change tendsto_congr -> tendsto.congr'

### [2019-03-01T10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/d74804bd2108e211350cede52247aa0896ad3a97)
add has_fderiv_at_filter

### [2019-03-01T10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/21b1fcc8fc4e6ab7da5a61f05b76528b07929e9c)
fix(asymptotics, deriv): minor formatting fixes

### [2019-03-01T10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/16033bb5b9e563ab4ff819ea9b69f50c246130d7)
feat(analysis/asymptotics,analysis/normed_space/deriv): improvements and additions

### [2019-03-01T10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/6265d261447fd92f7a9ea3ed63b8c9771b9093b3)
feat(analysis/normed_space/deriv): start on derivative

### [2019-03-01T10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/92a5e0b150523967b1ed4fcb488c4fde9893f855)
feat(analysis/asymptotics): start on bigo and littlo

### [2019-03-01T10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/206a7a11cf944cdf189df77551dce3a8fbba8b0a)
feat(*): add various small lemmas

### [2019-03-01T13:10:17+00:00](https://github.com/leanprover-community/mathlib/commit/4f7853a17621fe5fa5eb6e1394ae48c8e7e955b1)
feat(data/list/basic): mem_rotate

### [2019-02-28T20:55:23+00:00](https://github.com/leanprover-community/mathlib/commit/05449a061744f8142bfc5396184e33ef19b08b82)
refactor(ring_theory/localization): rename of to mk, and define of ([#765](https://github.com/leanprover-community/mathlib/pull/#765))

* refactor(ring_theory/localization): rename of to mk, and define of

* Make submonoid implicit variable of 'of'

### [2019-02-28T19:14:55+00:00](https://github.com/leanprover-community/mathlib/commit/eb033cfe5de2f1cc1a431061b4803970b9246c51)
feat(ring_theory/ideals): make ideal.quotient.field a discrete_field ([#777](https://github.com/leanprover-community/mathlib/pull/#777))

### [2019-02-28T17:20:01+00:00](https://github.com/leanprover-community/mathlib/commit/e6a3ca81c644b8ff62cb38b9327b5cefa551a312)
refactor(algebra/group): generalise and extend the API for with_zero ([#762](https://github.com/leanprover-community/mathlib/pull/#762))

* refactor(algebra/group): generalise and extend the API for with_zero

* Shorter proof. Thanks Chris

* Travis, try your best

### [2019-02-28T16:55:44+00:00](https://github.com/leanprover-community/mathlib/commit/781d18758593fd95cc7bcff84f567259c4aa0f16)
feat(group_theory/quotient_group): define ker_lift and prove simp-lemmas ([#764](https://github.com/leanprover-community/mathlib/pull/#764))

* feat(group_theory/quotient_group): define ker_lift and prove simp-lemmas

* Add docstring

### [2019-02-28T11:09:35+01:00](https://github.com/leanprover-community/mathlib/commit/81f85308751ca13182a614701a529dbf427d96fc)
fix(tactic/linarith): typo

### [2019-02-28T10:33:40+01:00](https://github.com/leanprover-community/mathlib/commit/08d4d17b926a77234d3aab9485f6bdd55d327b99)
feat(topology/basic): Add instances for subset/inter/union for opens(X) ([#763](https://github.com/leanprover-community/mathlib/pull/#763))

* feat(topology/basic): Add instances for subset/inter/union for opens(X)

### [2019-02-27T23:53:37+01:00](https://github.com/leanprover-community/mathlib/commit/477338d295bae48df93ab8f8c793a97beb5e6083)
refactor(data/subtype): organise in namespaces, use variables, add two simp-lemmas ([#760](https://github.com/leanprover-community/mathlib/pull/#760))

### [2019-02-27T22:46:52+00:00](https://github.com/leanprover-community/mathlib/commit/af2cf74ab5ba3b482e71cf98fe7eac3520869e48)
feat(group_theory/quotient_group): map is a group hom ([#761](https://github.com/leanprover-community/mathlib/pull/#761))

### [2019-02-27T22:37:11+00:00](https://github.com/leanprover-community/mathlib/commit/dfa855c232d4134fde72dfc4d1fd8c506a4fc679)
feat(data/finset) remove unnecessary assumption from card_eq_succ ([#772](https://github.com/leanprover-community/mathlib/pull/#772))

### [2019-02-27T23:14:03+01:00](https://github.com/leanprover-community/mathlib/commit/cfde449a4ac1fed0a4ef48d42dc65c9dfe950bd3)
fix(doc/tactics): linarith doc is outdated [ci-skip]

### [2019-02-27T21:33:02+01:00](https://github.com/leanprover-community/mathlib/commit/6c71ac0be9813d0bde53244fa8e546e4ec20639c)
fix(tactic/linarith): fix bug in strengthening of strict nat/int inequalities

### [2019-02-27T15:25:19+00:00](https://github.com/leanprover-community/mathlib/commit/4667d2c2d49df4d5e9fa2a26337edd29ee15a610)
feat(ring_theory/ideal_operations): ideals form a commutative semiring ([#771](https://github.com/leanprover-community/mathlib/pull/#771))

### [2019-02-27T14:06:24+00:00](https://github.com/leanprover-community/mathlib/commit/05d1d33905014a1847469f454b89b31a89da5d62)
fix(algebra/archimedean): swap names of floor_add_fract and fract_add_floor ([#770](https://github.com/leanprover-community/mathlib/pull/#770))

### [2019-02-27T12:02:24+01:00](https://github.com/leanprover-community/mathlib/commit/42d1ed707cfde1b4dea8c4438eb92ebe0eec383f)
feat(linarith): improve handling of strict inequalities in nat and int ([#769](https://github.com/leanprover-community/mathlib/pull/#769))

* feat(linarith): perform slightly better on ℕ and ℤ by strengthening t < 0 hyps to t + 1 ≤ 0

* remove already completed TODO item

### [2019-02-26T22:04:45+01:00](https://github.com/leanprover-community/mathlib/commit/3f477395cc043b62b7083ab13649ad6102ff314f)
fix(docs/howto-contribute): main repository has moved

### [2019-02-26T12:57:23-05:00](https://github.com/leanprover-community/mathlib/commit/7450cc55a33a192c9fc5f8f67d0210b81beff645)
fix(scripts/update_mathlib): improve python style and error handling ([#759](https://github.com/leanprover-community/mathlib/pull/#759))

### [2019-02-25T16:20:56-05:00](https://github.com/leanprover-community/mathlib/commit/71a7e1c497336b2eeae75cc8a54bb4ada32ca0f7)
fix(scripts/update-mathlib): cached archived were never expanded

### [2019-02-25T16:01:35-05:00](https://github.com/leanprover-community/mathlib/commit/42224838d8a1586997c8448c1abee701edbbc61e)
fix(scripts/update-mathlib): fix the commit check

### [2019-02-24T23:52:02-05:00](https://github.com/leanprover-community/mathlib/commit/e23553a4088cead7388d3659a27fad2f250e5cec)
doc(nat/decidable_prime): add docstrings explaining the two decidable_prime instances ([#757](https://github.com/leanprover-community/mathlib/pull/#757))

### [2019-02-24T15:36:34+00:00](https://github.com/leanprover-community/mathlib/commit/f9220866822b6d606ac41af14384210048d73b32)
feat(ring_theory/polynomial): more operations on polynomials ([#679](https://github.com/leanprover-community/mathlib/pull/#679))

### [2019-02-24T11:59:27+00:00](https://github.com/leanprover-community/mathlib/commit/c9b2d0ee385d7de0495c3fbdaae3fc5392ed2571)
chore(linear_algebra/multivariate_polynomial): remove unnecessary decidable_eq assumption ([#755](https://github.com/leanprover-community/mathlib/pull/#755))

### [2019-02-23T11:37:37+00:00](https://github.com/leanprover-community/mathlib/commit/ddc016c64f8ef7227170d08004d8f38ed5f4142b)
feat(*): polar co-ordinates, de moivre, trig identities, quotient group for angles ([#745](https://github.com/leanprover-community/mathlib/pull/#745))

* feat(algebra/group_power): re-PRing polar co-ords

* Update group_power.lean

* feat(analysis/exponential): re-PRing polar stuff

* feat(data.complex.exponential): re-PR polar stuff

* fix(analysis.exponential): stylistic

* fix(data.complex.exponential): stylistic

* fix(analysis/exponential.lean): angle_eq_iff_two_pi_dvd_sub

* fix(analysis/exponential): angle_eq_iff_two_pi_dvd_sub

### [2019-02-23T00:41:40+00:00](https://github.com/leanprover-community/mathlib/commit/63fa61dbfd07df48046220ba40af85d4368414d3)
fix(analysis/specific_limits): remove useless assumption ([#751](https://github.com/leanprover-community/mathlib/pull/#751))

### [2019-02-21T21:35:05+00:00](https://github.com/leanprover-community/mathlib/commit/e739cf508474d04d7e92bc56a3933ddd149b92c0)
feat(order_dual): instances for order_dual and shortening proofs ([#746](https://github.com/leanprover-community/mathlib/pull/#746))

* feat(order_bot): instances for order_bot and shortening proofs

* fix(topological_structure); remove unused import

### [2019-02-21T16:24:47+00:00](https://github.com/leanprover-community/mathlib/commit/3c3a0521e444c4cd1fb13033c80fade667b527c4)
feat(field_theory/subfield): closure of subset in field ([#742](https://github.com/leanprover-community/mathlib/pull/#742))

### [2019-02-20T18:08:04-05:00](https://github.com/leanprover-community/mathlib/commit/96564857991fc95761d7e51b11a10e3fd0010f07)
feat(data/finmap): lift_on₂ ([#716](https://github.com/leanprover-community/mathlib/pull/#716))

* feat(data/finmap): define lift_on₂ with lift_on

### [2019-02-20T17:32:07+00:00](https://github.com/leanprover-community/mathlib/commit/8b8ae32c916e77b7bcb552a9bd3ea5994f1e951c)
fix(order/basic): give order_dual the correct lt ([#741](https://github.com/leanprover-community/mathlib/pull/#741))

### [2019-02-20T12:33:02+00:00](https://github.com/leanprover-community/mathlib/commit/c7202e57149d15391c6ca6e5539424c95fcf58d5)
feat(analysis/exponential): pow_nat_rpow_nat_inv ([#740](https://github.com/leanprover-community/mathlib/pull/#740))

### [2019-02-18T18:07:10+00:00](https://github.com/leanprover-community/mathlib/commit/78ce6e49a694f813a06cbda0f3a0e5151ffa963b)
feat(data/fintype): fintype.of_injective

### [2019-02-18T09:48:21-05:00](https://github.com/leanprover-community/mathlib/commit/9a2c13ab77ba62385ce9571901fec17e05adba6b)
feat(data/alist,data/finmap): always insert key-value pair ([#722](https://github.com/leanprover-community/mathlib/pull/#722))

* Change {alist,finmap}.insert to always insert the key-value pair
  instead of doing nothing if the inserted key is found. This allows for
  useful theorems such as lookup_insert.
* Add list.keys and used key membership instead of exists/forall. This
  makes proofs easier in some places.
* Add a few other useful theorems such as lookup_eq_none,
  lookup_erase, lookup_erase_ne.

### [2019-02-18T09:45:57+00:00](https://github.com/leanprover-community/mathlib/commit/6b4435be936b084622d7edd195441dbeab383794)
feat(data/polynomial): create nonzero_comm_semiring and generalize nonzero_comm_ring lemmas ([#736](https://github.com/leanprover-community/mathlib/pull/#736))

### [2019-02-16T21:24:09+00:00](https://github.com/leanprover-community/mathlib/commit/c64b67ed8e48974b7e776d30f08efbddd41fd67b)
feat(ring_theory/localization): revamp, ideal embedding ([#481](https://github.com/leanprover-community/mathlib/pull/#481))

### [2019-02-15T17:29:36-05:00](https://github.com/leanprover-community/mathlib/commit/17f9bef08da310fbbcc4b9656ebd5334eb2ddb72)
feat(category/monad/cont): continuation passing monad ([#728](https://github.com/leanprover-community/mathlib/pull/#728))

### [2019-02-15T19:37:56+00:00](https://github.com/leanprover-community/mathlib/commit/0a6e705706cf8e436babcc1ff6308e02de39694a)
refactor(data/equiv/algebra): move polynomial lemmas from equiv/algebra to mv_polynomial ([#731](https://github.com/leanprover-community/mathlib/pull/#731))

* refactor(data/equiv/algebra): move polynomial lemma from equiv/algebra to mv_polynomial

* remove update-mathlib.py

### [2019-02-15T14:26:25+01:00](https://github.com/leanprover-community/mathlib/commit/d80b03e6ede7f52d4b864a663d899725c0034401)
chore(order/filter/basic): update documentation of filter_upwards

### [2019-02-15T07:40:09+00:00](https://github.com/leanprover-community/mathlib/commit/8730619bb769cd92ef7c8557d8ee42a5c6bf05f1)
chore(topology/algebra/topological_structures): remove unused import ([#729](https://github.com/leanprover-community/mathlib/pull/#729))

### [2019-02-14T18:26:14+01:00](https://github.com/leanprover-community/mathlib/commit/ce580d7bf7d2052392a7273d3df345a0dd4a77ef)
refactor(data/equiv): rename subtype_equiv_of_subtype to subtype_congr and subtype_congr to subtype_congr_prop

### [2019-02-14T18:04:51+01:00](https://github.com/leanprover-community/mathlib/commit/683519f38532c00e4b2f131f1d54bc8587c668cf)
feat(data/equiv/basic): generalise subtype_equiv_of_subtype ([#724](https://github.com/leanprover-community/mathlib/pull/#724))

### [2019-02-14T18:04:24+01:00](https://github.com/leanprover-community/mathlib/commit/d4568a412425dd528b969446efc0452491ae8528)
fix(data/subtype): don't use pattern matching in subtype.map ([#725](https://github.com/leanprover-community/mathlib/pull/#725))

### [2019-02-13T19:51:35-05:00](https://github.com/leanprover-community/mathlib/commit/5da8605fd8bd7ae8f14836b218f0c95f9c3df4fd)
chore(deploy): clean up deploy_nightly.sh ([#720](https://github.com/leanprover-community/mathlib/pull/#720))

### [2019-02-13T23:30:38+01:00](https://github.com/leanprover-community/mathlib/commit/a6150a326a6141427a543676f955c52ef64c12f4)
refactor(data/real): move cau_seq_filter to analysis/metric_space ([#723](https://github.com/leanprover-community/mathlib/pull/#723))

### [2019-02-13T17:01:08+01:00](https://github.com/leanprover-community/mathlib/commit/3fd0e60a5b6859a6bf18597975579bf3e545f67c)
refactor(topology/algebra/infinite_sum): Cauchy condition for infinite sums generalized to complete topological groups

### [2019-02-12T22:44:40+01:00](https://github.com/leanprover-community/mathlib/commit/246c28095a685ae19090ee87af2df9246414ec80)
feat(tactic/basic,tactic/interactive): improvements to set tactic ([#712](https://github.com/leanprover-community/mathlib/pull/#712))

* feat(tactic/basic,tactic/interactive): improvements to set tactic

* feat(tactic/interactive): take optional explicit type in set tactic

### [2019-02-12T15:50:35-05:00](https://github.com/leanprover-community/mathlib/commit/f6ca16e0f9d57278434fd2eac94bc4d70a61751d)
fix(nightly): improve conditional ([#719](https://github.com/leanprover-community/mathlib/pull/#719))

### [2019-02-12T20:15:49+01:00](https://github.com/leanprover-community/mathlib/commit/a4afa904f2e902e34764ff69ec5baf31ad56525a)
refactor(analysis/specific_limits): generalize has_sum_of_absolute_convergence to normed_groups

### [2019-02-12T09:33:43-05:00](https://github.com/leanprover-community/mathlib/commit/503a4235959bd3ec26e1831dd26dd16ff402363e)
feat(update-mathlib): improve setup and error messages

### [2019-02-12T15:28:42+01:00](https://github.com/leanprover-community/mathlib/commit/b6a47633b5a9614b413f6ce8ed15e040bd524452)
refactor(order/filter): replace tendsto_comp_succ_at_top_iff by tendsto_add_at_top_iff_nat

### [2019-02-12T08:46:53-05:00](https://github.com/leanprover-community/mathlib/commit/c4e84146b29b3b900f0c69da7b5c7caf3da41d04)
fix(update-mathlib): install from anywhere in your directory structure

### [2019-02-12T14:09:42+01:00](https://github.com/leanprover-community/mathlib/commit/f5a85f10f05e8b0c3254a1d7d699b0bb77259b5d)
refactor(order/filter): move lift and lift' to separate file

### [2019-02-12T11:17:26+01:00](https://github.com/leanprover-community/mathlib/commit/253fe33b78f4a2c893499f8d5ea0ff62d23e5cc3)
refactor(order/filter): generalize map_succ_at_top_eq to arbitrary Galois insertions; generalize tendsto_coe_iff to arbitary order-preserving embeddings

### [2019-02-12T11:17:26+01:00](https://github.com/leanprover-community/mathlib/commit/c853c33593203e9c35f6dfe3b84e1bf5e5ee67ec)
chore(analysis/specific_limits): replace mul_add_one_le_pow by pow_ge_one_add_mul

### [2019-02-12T09:12:26+00:00](https://github.com/leanprover-community/mathlib/commit/41e3b6faf2f73b921bb57e7d3af4665a664c1b0d)
refactor(data/list): add prop arg for easier usage ([#715](https://github.com/leanprover-community/mathlib/pull/#715))

### [2019-02-11T20:48:17-05:00](https://github.com/leanprover-community/mathlib/commit/d1ef181c0fbe665685ba2873290ad09faec20a19)
feat(topology/metric_space/gluing): Gluing metric spaces ([#695](https://github.com/leanprover-community/mathlib/pull/#695))

### [2019-02-11T15:43:36-05:00](https://github.com/leanprover-community/mathlib/commit/8243300bbfca685033266b4cb7a291768b8b29af)
build(nightly): fix nightly

### [2019-02-11T16:50:18+00:00](https://github.com/leanprover-community/mathlib/commit/fb7e42dc1c42a28e806a46508afcc236a0d5846f)
fix(group_theory/quotient_group): remove duplicate group_hom instance ([#713](https://github.com/leanprover-community/mathlib/pull/#713))

### [2019-02-11T10:13:54+01:00](https://github.com/leanprover-community/mathlib/commit/4b84aac9ccbee57a0b979540886ae4029023ac51)
fix(data/finsupp): duplicated instance

### [2019-02-10T21:50:00+00:00](https://github.com/leanprover-community/mathlib/commit/091cad78bc0331f2d83defbd849ed28922e68a66)
feat(algebra/gcd_domain): normalize ([#668](https://github.com/leanprover-community/mathlib/pull/#668))

### [2019-02-10T12:36:00-05:00](https://github.com/leanprover-community/mathlib/commit/cfe582ffc17959cf98fbd956b6991d62d2941b93)
Automate the deployment of nightly builds ([#707](https://github.com/leanprover-community/mathlib/pull/#707))

* build(nightly): automate nightly releases of mathlib

### [2019-02-10T16:44:30+00:00](https://github.com/leanprover-community/mathlib/commit/9b28db0728954d6566d31fbadbd7b9479bfa6bf8)
refactor(*): refactor associates ([#710](https://github.com/leanprover-community/mathlib/pull/#710))

### [2019-02-10T14:25:05+00:00](https://github.com/leanprover-community/mathlib/commit/c25122bb6ff95feffc7b8b90b07e18df0dfd62e1)
feat(algebra/archimedean): add fractional parts of floor_rings ([#709](https://github.com/leanprover-community/mathlib/pull/#709))

### [2019-02-10T14:01:02+01:00](https://github.com/leanprover-community/mathlib/commit/d6f84daec3983f151981a32fa5226df16e7ff53b)
feat(tactic/tidy): add `tidy?` syntax for reporting a tactic script ([#704](https://github.com/leanprover-community/mathlib/pull/#704))

### [2019-02-10T10:39:51+00:00](https://github.com/leanprover-community/mathlib/commit/ed4c536a8c836379a51ed6fd04fc7db959296d0f)
feat(data/polynomial): multiplicity of roots of polynomials ([#656](https://github.com/leanprover-community/mathlib/pull/#656))

* feat(data/polynomial): multiplicity of roots of polynomials

* rename lemmas

* use section

* use `nonzero_comm_ring.of_ne`

* refactor(polynomial): weaken decidablility hypothesis

* indentation

* swap order of arguments

### [2019-02-09T15:41:40+00:00](https://github.com/leanprover-community/mathlib/commit/088f753a9ea150905f5af0302227ef218375e93e)
refactor(geo_sum): remove duplicate proofs about geometric sums ([#706](https://github.com/leanprover-community/mathlib/pull/#706))

* feat(data/finset): add range_add_one

* feat(algebra/big_operators): geometric sum for semiring, ring and division ring

* refactor(geo_sum): remove duplicate proofs about geometric sums

### [2019-02-09T15:38:37+00:00](https://github.com/leanprover-community/mathlib/commit/484d8648d7fc3683727f77f5ef2b4b91698c5a5f)
add geometric sum ([#701](https://github.com/leanprover-community/mathlib/pull/#701))

* feat(data/finset): add range_add_one

* feat(algebra/big_operators): geometric sum for semiring, ring and division ring

### [2019-02-08T20:56:33-05:00](https://github.com/leanprover-community/mathlib/commit/22c71795e8d62f2e4440b5274c90b80bae458393)
build(update-mathlib): adjust the header of python script

### [2019-02-08T18:41:17-05:00](https://github.com/leanprover-community/mathlib/commit/8b510176464ae4d0c6b643aac942f7680c314156)
build(update-mathlib): fix installation and documentation

### [2019-02-08T17:13:15-05:00](https://github.com/leanprover-community/mathlib/commit/650237b4df72439498241dfd780f80cf9a644ec4)
build(update-mathlib): install update-mathlib into `~/.mathlib/bin`

### [2019-02-08T17:01:46-05:00](https://github.com/leanprover-community/mathlib/commit/814cb034fbbfe4797aa1bee0a7ed338d962a9e6f)
build(update-mathlib): fix installation and documentation

### [2019-02-08T16:55:19-05:00](https://github.com/leanprover-community/mathlib/commit/64065f40769a4d456e8d74ea2b1687a755474c3f)
build(update-mathlib): improve installation and documentation

### [2019-02-08T16:11:45-05:00](https://github.com/leanprover-community/mathlib/commit/4227f5c6212abf757a42c2b743efb4e08edbde11)
Deploy olean ([#697](https://github.com/leanprover-community/mathlib/pull/#697))

* deploy(olean): deploy the olean files for every successful builds

### [2019-02-08T19:05:45+00:00](https://github.com/leanprover-community/mathlib/commit/11e19d8c0ece4ce08bf70788f6c37d6f9abaea39)
refactor(ring_theory/noetherian): make is_noetherian and is_noetherian_ring classes ([#689](https://github.com/leanprover-community/mathlib/pull/#689))

* refactor(ring_theory/noetherian): make is_noetherian and is_noetherian_ring classes

* correct spelling mistake.

* add well_founded_submodule_gt

### [2019-02-08T13:11:06-05:00](https://github.com/leanprover-community/mathlib/commit/1f50e0d85ea084af9a7897976a6d3c5c796e2c44)
fix(build): fix the output keeping travis builds alive ([#702](https://github.com/leanprover-community/mathlib/pull/#702))

### [2019-02-08T09:43:02-05:00](https://github.com/leanprover-community/mathlib/commit/0f2562e886ef3d032f32cd18c9edaebeb7cbe66e)
fix(build): fix the output keeping travis builds alive ([#700](https://github.com/leanprover-community/mathlib/pull/#700))

### [2019-02-08T09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/cfd2b75e7a80462001fd1c2b835196b28dcd25c1)
feat(order/filter): break filter into smaller files

### [2019-02-08T09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/8db042f060649f024c85e136fecb2b9cc6dd1b72)
feat(data/rel): galois_connection (image r) (core r)

### [2019-02-08T09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/b2ba37c79effdba84d2a042f561e8a899eeed464)
chore(*): fix errors introduced by rebasing

### [2019-02-08T09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/8e4aafabff5704042a97e4b1feb0238aed95be1c)
feat(analysis/metric): convergence wrt nhds_within

### [2019-02-08T09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/f5d73bdd1376304f9ac6b5c06cbe89d7162c22ba)
feat(analysis/topology/continuity): add some variations

### [2019-02-08T09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/e0b825330af45e2e9254ee0c0f867c820f49e5a5)
feat (analysis/topology/topological_space): properties of nhds, nhds_within

### [2019-02-08T09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/a96fa3be3beb9ea110c537ec7a9731ca794946c0)
feat(order/filter): convergence for relations and partial functions

### [2019-02-08T09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/4444464c61345dc038cdf4e322943909691fde45)
feat(data/pfun): add restrict, preimage, core, etc.

### [2019-02-08T09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/cae5c8b6cddfa88517401428516f06ea3863aba4)
fix(data/rel): make composition local notation

### [2019-02-08T09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/4779af7782f7c17399253d0e33ff38ed34458a9c)
feat(data/rel): a type for binary relations

### [2019-02-08T09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/126d573a6392fe999ecd8fbed89158d1a65eefdd)
feat(data/set/basic,logic/function): small additions and renamings

### [2019-02-07T22:32:47+00:00](https://github.com/leanprover-community/mathlib/commit/1ed7ad1129d4b70449f6c9cd90908dd768e2358e)
feat(algebra/archimedean): abs_sub_lt_one_of_floor_eq_floor ([#693](https://github.com/leanprover-community/mathlib/pull/#693))

* abs_diff_lt_one_of_floor_eq_floor

* better name

### [2019-02-07T19:37:17+01:00](https://github.com/leanprover-community/mathlib/commit/177b5eb0d801cc6451e15209049c8c673a55adcd)
feat(linear_algebra): dimension of the base field is 1

### [2019-02-07T19:36:51+01:00](https://github.com/leanprover-community/mathlib/commit/0f240304d6222d58d7095c88f68e7a80f342dffb)
refactor(src/data/finset): supr/infi as a directed supr/infi of finite inf/sup

### [2019-02-07T15:56:26+01:00](https://github.com/leanprover-community/mathlib/commit/eeed321830f72fd27f64d1b2dec68dce467fa07d)
chore(linear_algebra/basic): relate map/comap/ker/range/comp with 0 and smul; use map/comap Galois connection

### [2019-02-07T14:58:25+01:00](https://github.com/leanprover-community/mathlib/commit/e98999efdb4d0a0ed1aab4a0cf9c0ab0e403a64d)
chore(algebra/pi_instances): generalize pi.list/multiset/finset_prod/sum_apply to dependent types

### [2019-02-07T14:58:25+01:00](https://github.com/leanprover-community/mathlib/commit/ad7ef864092b3403e56a8108854ecdafeefccb80)
refactor(set_theory/cardinal): split up mk_Union_le_mk_sigma, add mk_Union_eq_mk_sigma; add equiv congruence for subtype

### [2019-02-07T13:13:39+01:00](https://github.com/leanprover-community/mathlib/commit/8a1de24981cf537429d96ce95e9093d4e4f1747c)
feat(data/{list/alist,finmap}): implicit key type ([#662](https://github.com/leanprover-community/mathlib/pull/#662))

* feat(data/{list/alist,finmap}): implicit key type

Make the key type α implicit in both alist and finmap. This brings these
types into line with the underlying sigma and simplifies usage since α
is inferred from the value function type β : α → Type v.

* doc(data/list/alist): alist is stored as a linked list

### [2019-02-07T13:02:53+01:00](https://github.com/leanprover-community/mathlib/commit/46d100926ff2cef5d1f066e4fb46c3ff88282af1)
feat(analysis/metric_space): Isometries ([#657](https://github.com/leanprover-community/mathlib/pull/#657))

### [2019-02-07T10:22:13+00:00](https://github.com/leanprover-community/mathlib/commit/8911b8cd36949c1e2dc5a368c38341970c279c91)
feat(algebra/order_functions): max_lt_max and min_lt_min ([#692](https://github.com/leanprover-community/mathlib/pull/#692))

### [2019-02-06T20:15:47+00:00](https://github.com/leanprover-community/mathlib/commit/51f80a3f8dafc81dd668e3c080c058d257bc6c68)
feat(data/quot): quotient.ind' ([#691](https://github.com/leanprover-community/mathlib/pull/#691))

* feat(data/quot): quotient.ind'

* correct elaborator tag; theorems not definitions

### [2019-02-06T10:58:04+01:00](https://github.com/leanprover-community/mathlib/commit/9615b385615e51359dce12af181d8cfcc386d105)
feat(data/real): completeness criterion for Cauchy sequences (closes [#654](https://github.com/leanprover-community/mathlib/pull/#654))

### [2019-02-06T10:36:56+01:00](https://github.com/leanprover-community/mathlib/commit/3ac796733c72b70da6501836a75a62898763cdb4)
feat(analysis/metric_space): add premetric spaces (closes [#652](https://github.com/leanprover-community/mathlib/pull/#652))

### [2019-02-06T10:29:32+01:00](https://github.com/leanprover-community/mathlib/commit/e93fa30697fa12d5bf6e90136cc6f7dd64369c04)
feat(category/fold): `foldl` and `foldr` for `traversable` structures ([#376](https://github.com/leanprover-community/mathlib/pull/#376))

### [2019-02-06T09:59:29+01:00](https://github.com/leanprover-community/mathlib/commit/c82243a81b18fab2bbf6bd8e9df2d44387fc559c)
feat(analysis/normed_space): bounded linear maps with the operator norm form a normed space (closes [#680](https://github.com/leanprover-community/mathlib/pull/#680))

### [2019-02-05T19:47:08+00:00](https://github.com/leanprover-community/mathlib/commit/d5a1b468afd83c5f36c9a2f48a34438f8bb43615)
to_nat_le_to_nat ([#685](https://github.com/leanprover-community/mathlib/pull/#685))

### [2019-02-05T14:26:19-05:00](https://github.com/leanprover-community/mathlib/commit/9f79d2eb7f19d73204898dc9472b5baeb19eee96)
fix(tactic/h_generalize): fix name resolution in h_generalize ([#688](https://github.com/leanprover-community/mathlib/pull/#688))

### [2019-02-05T14:13:55-05:00](https://github.com/leanprover-community/mathlib/commit/a0d8ae1e34ff8a5cb9ca2e74c5598f695ac9ad7e)
feat(tactic/replaceable): supplement `def_replacer` with attribute `replaceable`

### [2019-02-04T19:35:17-05:00](https://github.com/leanprover-community/mathlib/commit/178c09d70721451296c3f792f247583974ad6a68)
feat(natural_isomorphism): componentwise isos are isos ([#671](https://github.com/leanprover-community/mathlib/pull/#671))

### [2019-02-04T20:49:37+00:00](https://github.com/leanprover-community/mathlib/commit/9a8f1b0686bcae10189f80f00140af1246d24d0a)
feat(algebra/group_power): gpow_add_one ([#683](https://github.com/leanprover-community/mathlib/pull/#683))

* feat(algebra/group_power): gpow_add_one

* feat(data/nat//basic): int.coe_nat_abs

### [2019-02-04T19:00:17+00:00](https://github.com/leanprover-community/mathlib/commit/53952326718fe5130b1e05abeefe693993543102)
remove simp on set_coe_eq_subtype ([#682](https://github.com/leanprover-community/mathlib/pull/#682))

### [2019-02-04T10:43:58+01:00](https://github.com/leanprover-community/mathlib/commit/5e5f1e25512627f03ed7cefe50b563f5b7c5bdd2)
fix(data/*/Ico): succ_top is too aggressive as a simp lemma ([#678](https://github.com/leanprover-community/mathlib/pull/#678))

### [2019-02-03T22:31:10+00:00](https://github.com/leanprover-community/mathlib/commit/25392518719ce0eea13b821dd235000968479026)
feat(data/nat/cast): abs_cast

### [2019-02-03T17:00:41-05:00](https://github.com/leanprover-community/mathlib/commit/d01e523e497fd6e34bda2c138e61f49fe76b1a99)
feat(category_theory/kleisli): monoids, const applicative functor and kleisli categories ([#660](https://github.com/leanprover-community/mathlib/pull/#660))

* feat(category_theory/kleisli): monoids, const applicative functor and
kleisli categories

### [2019-02-03T17:01:45+01:00](https://github.com/leanprover-community/mathlib/commit/f5bd340c07d2eaa49004bf14926436c8f930676c)
cleanup(*): removing uses of bare `have` ([#676](https://github.com/leanprover-community/mathlib/pull/#676))

### [2019-02-03T02:14:48-05:00](https://github.com/leanprover-community/mathlib/commit/544f35c353ce189abf608b891ba788d2f5064694)
Update README.md

### [2019-02-03T02:06:28+00:00](https://github.com/leanprover-community/mathlib/commit/b3e1e6f3df04f1d9b209060dbb3c105e08873c89)
fix(README): update URL for build status icon ([#681](https://github.com/leanprover-community/mathlib/pull/#681))

### [2019-02-03T01:08:36+00:00](https://github.com/leanprover-community/mathlib/commit/044b6faeee727a4c07c41aac6842a887efc10a71)
feat(algebra/euclidean_domain): discrete field to euclidean domain ([#674](https://github.com/leanprover-community/mathlib/pull/#674))

### [2019-02-02T19:04:50-05:00](https://github.com/leanprover-community/mathlib/commit/3109c4b354a3071bd8a2c239660e99bcb3da9b3a)
chore(purge_olean.sh): a few small improvements ([#661](https://github.com/leanprover-community/mathlib/pull/#661))

* purge empty directories
* Only print if an .olean is rm'd. This reduces the noise and reduces the
script run time.
* use git top-level dir to make the script relocatable
* only affect src and test dirs
* use bash instead of sed

### [2019-02-02T18:43:29-05:00](https://github.com/leanprover-community/mathlib/commit/8590ff2b97e846c77588285f4faa23d0018f0134)
fix(functor_category): remove superfluous coercions ([#670](https://github.com/leanprover-community/mathlib/pull/#670))

### [2019-02-02T18:42:36-05:00](https://github.com/leanprover-community/mathlib/commit/a09dc9f22afdc9410942b6cf235811dd1e9fafab)
cleanup(category_theory/cones): tidying up, after making opposites work better ([#675](https://github.com/leanprover-community/mathlib/pull/#675))

### [2019-02-02T18:41:09-05:00](https://github.com/leanprover-community/mathlib/commit/b084cfcd59b865f7a1644ceb1a61fb1ed63aea7e)
fix(category_theory/equivalence): duplicated namespace prefix ([#669](https://github.com/leanprover-community/mathlib/pull/#669))

### [2019-02-02T17:59:12-05:00](https://github.com/leanprover-community/mathlib/commit/e501d0261725893f85ca1f3bfc666b630c531010)
fix(replacer): better flow control in replacer when tactic fails ([#673](https://github.com/leanprover-community/mathlib/pull/#673))

The main consequence is better error reporting.

### [2019-02-02T18:42:12+00:00](https://github.com/leanprover-community/mathlib/commit/0393ccbd47a5f14e425b3713e84a78bd629c76f1)
feat(ring_theory/algebra): subalgebra_of_subring ([#664](https://github.com/leanprover-community/mathlib/pull/#664))

### [2019-02-01T23:00:55-05:00](https://github.com/leanprover-community/mathlib/commit/f529870e34eb5370ae8ac1f49f728547e4f6bbe5)
feat(data/nat/gcd/coprime): some easy simp lemmas ([#677](https://github.com/leanprover-community/mathlib/pull/#677))

### [2019-02-02T01:41:01+00:00](https://github.com/leanprover-community/mathlib/commit/6925e4dcb4ff0f3a6446514f74687e5e97d2a98a)
feat(algebra/euclidean_domain): lcm ([#665](https://github.com/leanprover-community/mathlib/pull/#665))

### [2019-02-01T20:07:31-05:00](https://github.com/leanprover-community/mathlib/commit/fb6014598a1d5ac4a595a98e5de743d0eb30aa00)
cleanup: replace `begin intros ...` with lambdas ([#672](https://github.com/leanprover-community/mathlib/pull/#672))

### [2019-02-01T22:48:10+00:00](https://github.com/leanprover-community/mathlib/commit/ed0d24af1d2a96f1a8ae1fd2956f8bb950850ea6)
feat(algebra/euclidean_domain): add quotient_zero axiom to euclidean_domain ([#666](https://github.com/leanprover-community/mathlib/pull/#666))

### [2019-02-01T12:26:22+01:00](https://github.com/leanprover-community/mathlib/commit/d8f6dc46f2efb7278c6e5d68442c6e969388e93a)
feat(src/tactic/explode): improve printing of references

### [2019-02-01T12:26:22+01:00](https://github.com/leanprover-community/mathlib/commit/a32de36f20d887da76cb57f79f8353f5dbf24e44)
feat(src/tactic/explode): add printing for conclusions of sintros

### [2019-02-01T12:26:22+01:00](https://github.com/leanprover-community/mathlib/commit/a08c9a7261ad11d02184a91e0da992092734586f)
add printing for conclusions of sintros

### [2019-02-01T12:13:59+01:00](https://github.com/leanprover-community/mathlib/commit/c9e4f8edc30da76ffa740000957e26aaf79cc31e)
fix(tactic/inarith): fix denominator normalization of products

### [2019-02-01T12:13:31+01:00](https://github.com/leanprover-community/mathlib/commit/52adfd7335d71e19f612dd3c099eb01cd520c776)
feat(tactic,tactic/interactive): add set tactic, a variant of let

### [2019-02-01T09:53:51+01:00](https://github.com/leanprover-community/mathlib/commit/89bc63c365bba21a5fcb6ef4e1145a0c095aad82)
feat(ring_theory/noetherian): is_noetherian_ring_range

### [2019-02-01T00:30:09+00:00](https://github.com/leanprover-community/mathlib/commit/8e381f6e6db106a70932d51bf4d2d8b16f1d6199)
feat(ring_theory/algebra_operations): multiplication of submodules of an algebra ([#658](https://github.com/leanprover-community/mathlib/pull/#658))

### [2019-01-30T18:20:41-05:00](https://github.com/leanprover-community/mathlib/commit/50a03f76bb89ee5cf9d9703f78e1eb2139d9b609)
chore(test): fix test directory structure

### [2019-01-30T18:20:41-05:00](https://github.com/leanprover-community/mathlib/commit/12be0aaa4133c26f2be8063f69e4403ad9f0dad0)
refactor(category_theory/instances): rename `examples` to `instances`

### [2019-01-30T17:15:23-05:00](https://github.com/leanprover-community/mathlib/commit/829b49bde8af1e03e80fb066929e0906af122422)
chore(.travis.yml): use git clean to clean out untracked files ([#659](https://github.com/leanprover-community/mathlib/pull/#659))

* chore(.travis.yml): use git clean to clean out untracked files and delete more obsolete olean files

PR [#641](https://github.com/leanprover-community/mathlib/pull/#641) involved renaming a directory. The old directory was still
present in the cache, and in this situation `git status` lists the
directory as a whole as untracked, so the grep did not find any
`.lean` files.

### [2019-01-30T17:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/0eb9db6a1a8a605f0cf9e33873d0450f9f0ae9b0)
chore(linear_algebra/multivariate_polynomial): move rename to the right place

### [2019-01-30T16:37:18+01:00](https://github.com/leanprover-community/mathlib/commit/a480160a81743eea7cafee8c8d6a446ec76982ea)
feat(data/polynomial): generalize theorems from nonzero_comm_ring to comm_ring ([#653](https://github.com/leanprover-community/mathlib/pull/#653))

### [2019-01-30T16:32:15+01:00](https://github.com/leanprover-community/mathlib/commit/065f083b6dea7d981d53e14e38bd20185ae901f0)
feat(group_theory): monoid / group closure of union

### [2019-01-30T16:16:31+01:00](https://github.com/leanprover-community/mathlib/commit/f7b9d6b43e478661eb87fef36c75e8e4ffc08499)
refactor(data/equiv/algebra): mv_polynomial mv_polynomial (β ⊕ γ) α ≃r mv_polynomial β (mv_polynomial γ α)

### [2019-01-30T10:26:08+01:00](https://github.com/leanprover-community/mathlib/commit/aa944bffa99b83a587d8c3d4ab38706d222c25ad)
feat(analysis/exponential): real powers, `cpow_nat_inv_pow` ([#647](https://github.com/leanprover-community/mathlib/pull/#647))

### [2019-01-30T09:57:02+01:00](https://github.com/leanprover-community/mathlib/commit/626489add6d59f61aabbe4dc3a4f9c3ad26bc2bd)
feat(topology/metric_space): diameter of a set in metric spaces ([#651](https://github.com/leanprover-community/mathlib/pull/#651))

### [2019-01-30T09:55:58+01:00](https://github.com/leanprover-community/mathlib/commit/ef35c6c316f611dcd2b6b4f1dbd704c233f34818)
second countability criteria in metric spaces

### [2019-01-30T09:54:34+01:00](https://github.com/leanprover-community/mathlib/commit/30649f5575ab4aff977e3b7a142cde5258f3f807)
cleanup instances/ennreal

### [2019-01-30T09:49:08+01:00](https://github.com/leanprover-community/mathlib/commit/afa535e75259704d9377fbc0441d47f465230500)
feat(ring_theory/polynomial): hilbert basis theorem

### [2019-01-29T19:13:38+01:00](https://github.com/leanprover-community/mathlib/commit/860eba6735d8e1314ffd4642ca0403fb4a5508c0)
chore(.): change occurrences of tests directory to test

### [2019-01-29T19:07:10+01:00](https://github.com/leanprover-community/mathlib/commit/247dcb2d5ffb6211286f9e6777fd98a53a5d9503)
feat(linear_algebra): rules for kernel of `of_le`, `cod_restrict`, and `pair`

### [2019-01-29T18:32:34+01:00](https://github.com/leanprover-community/mathlib/commit/4fb6c7dc61c2232e29c25473ad577dce48d2ceea)
chore(test): rename the test directory so that `leanpkg` will find it

### [2019-01-29T17:18:52+01:00](https://github.com/leanprover-community/mathlib/commit/fc529b6f18f106c1b71f6f0f0790bac8b56b77a9)
feat(data/complex/basic): of_real_fpow ([#640](https://github.com/leanprover-community/mathlib/pull/#640))

### [2019-01-29T17:15:53+01:00](https://github.com/leanprover-community/mathlib/commit/d7d90fa648ded550351ab03cb0d222bd5673eadf)
docs(tactic/monotonicity/interactive): fix `mono` documentation [ci-skip]

### [2019-01-29T17:15:30+01:00](https://github.com/leanprover-community/mathlib/commit/0924ac0edf31749208aa2d3ccd9696fa565e5674)
fix build

### [2019-01-29T17:15:30+01:00](https://github.com/leanprover-community/mathlib/commit/a0e2de9611ba0e414a1e8295dde5b9f2752ed7f3)
refactor(*): use decidable_linear_order.lift

### [2019-01-29T17:15:15+01:00](https://github.com/leanprover-community/mathlib/commit/7cfcce3def9edccf3aa7aaddab6ac19ae89e3b75)
feat(data/equiv/algebra): ring equiv for mv_polynomial

### [2019-01-29T13:20:33+01:00](https://github.com/leanprover-community/mathlib/commit/54f4b29145fc3150a0cbf6e360b9ae3581623eb6)
feat(tactic/interactive.lean): clear_aux_decl

### [2019-01-29T13:20:13+01:00](https://github.com/leanprover-community/mathlib/commit/8faf8df02cb740d16a006aeabe6cffca55a3d6db)
feat(field_theory/splitting_field): splits predicate on polynomials

### [2019-01-29T13:17:09+01:00](https://github.com/leanprover-community/mathlib/commit/8ee4f2da98bca9f01a7a28c1bc1e9ddb18742906)
move continuous_of_lipschitz around

### [2019-01-29T11:39:45+01:00](https://github.com/leanprover-community/mathlib/commit/83edba46dabd5f0dcd0fedd8d592f99b9447edd5)
feat(measure_theory): integral is equal and monotone almost-everywhere and for measurable functions it is a.e. strict at 0

### [2019-01-29T09:37:59+01:00](https://github.com/leanprover-community/mathlib/commit/cd41acab650375e93b68c1b42421675b00e48903)
Move tendsto_div to a better place

### [2019-01-28T20:15:38+01:00](https://github.com/leanprover-community/mathlib/commit/042c290dac25b5f1c77255f1039fae301774d6cf)
refactor(category_theory/opposites): Make `opposite` irreducible

### [2019-01-28T20:11:16+01:00](https://github.com/leanprover-community/mathlib/commit/d1b7d9149fda663c2d39d6dceefc9c3f4b5bfd80)
feat(category_theory/limits/cones): forgetful functors

### [2019-01-28T19:59:32+01:00](https://github.com/leanprover-community/mathlib/commit/b39d6d8a502edfb5adb3026c256c82bea526328b)
feat(*) refactor module

### [2019-01-28T19:52:47+01:00](https://github.com/leanprover-community/mathlib/commit/fd3e5a1287ee20028377e2c1c23b25a644872b8c)
fix(topology/instances/ennreal): fix merge

### [2019-01-28T19:34:07+01:00](https://github.com/leanprover-community/mathlib/commit/e62c534c1ec4fe7eb99a4c698140432b8a89a5f3)
add ennreal.to_real

### [2019-01-28T17:14:45+01:00](https://github.com/leanprover-community/mathlib/commit/8572c6b07d85af3e6134aa7a286714a1052dd37d)
feat(topology): prove continuity of nndist and edist; `ball a r` is a metric space

### [2019-01-28T10:14:51+01:00](https://github.com/leanprover-community/mathlib/commit/afa31bed1b58a326af5584f1041fcbf9e57c3228)
refactor(linear_algebra/direct_sum_module): move to algebra/direct_sum

### [2019-01-28T08:02:17+01:00](https://github.com/leanprover-community/mathlib/commit/7199bb36b667b97b78696bd6d6485b62c87004aa)
chore(linear_algebra/dimension): simplify dim_add_le_dim_add_dim

### [2019-01-27T22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/038e0b2778311580de30236f409b237212e02095)
feat(ring_theory/algebra): remove out_param

### [2019-01-27T22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/af7a7ee35ed76f900808129f9c733bb1ed5dc220)
feat(ring_theory/algebra): remove of_core

### [2019-01-27T22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/79ba61cc1078f52cba4e069906a0f3667f1f0ff3)
feat(ring_theory/algebra): make algebra a class

### [2019-01-27T22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/a0b6cae4d175ab77120b803f5e9609dd3452cb1f)
feat(ring_theory/algebra): define algebra over a commutative ring

### [2019-01-27T22:44:50+01:00](https://github.com/leanprover-community/mathlib/commit/1d2eda7be4646692d4054eb68805f51f277961c4)
feat(category_theory/isomorphism): as_iso

Also clean up some proofs.

### [2019-01-27T22:43:45+01:00](https://github.com/leanprover-community/mathlib/commit/ccd895f83881e46779c97c59633309469f56b9f3)
feat(category_theory/types): conversions between iso and equiv

### [2019-01-27T22:42:53+01:00](https://github.com/leanprover-community/mathlib/commit/d074b51baf03cf392e01b44dafd41ee6b7eb473d)
refactor(category_theory/concrete_category): move `bundled` to own file

### [2019-01-27T22:40:37+01:00](https://github.com/leanprover-community/mathlib/commit/50398e50c2de40d283ee22d26d15a55b7e038469)
feat(category_theory/full_subcategory): induced categories

### [2019-01-27T22:37:46+01:00](https://github.com/leanprover-community/mathlib/commit/19c2f68c848b6983ce37e8c75fd9ba61e2eef77c)
feat(analysis/exponential): complex powers

### [2019-01-27T22:33:10+01:00](https://github.com/leanprover-community/mathlib/commit/c05775804db479a698c85d6b1c3cab90bffdd4b9)
feat(data/complex/exponential): exp_eq_one_iff

### [2019-01-27T22:32:41+01:00](https://github.com/leanprover-community/mathlib/commit/db691737197a060dfbc3a2e7f65a04b1a888168d)
refactor(algebra/field_power): notation for fpow

### [2019-01-27T22:31:44+01:00](https://github.com/leanprover-community/mathlib/commit/d359aa892c1695c5393e2b24de471924b8227d90)
feat(order/conditionally_complete_lattice): cinfi_const ([#634](https://github.com/leanprover-community/mathlib/pull/#634))

### [2019-01-27T22:30:58+01:00](https://github.com/leanprover-community/mathlib/commit/06eba7f890f662fbc36d6653f36be26fbd970366)
update authors on expr.lean (I don't know who's responsible for what)

### [2019-01-27T22:30:58+01:00](https://github.com/leanprover-community/mathlib/commit/be5dba970a1d499ab63f3bf69418198dd51bd7af)
fix(tactic/norm_num): only check core norm_num output up to numeral structure

### [2019-01-27T22:30:58+01:00](https://github.com/leanprover-community/mathlib/commit/daa7684d93c373664f95650e358d779f68fc83a3)
refactor(tactic/basic): move non-tactic decls to meta folder

### [2019-01-27T22:28:46+01:00](https://github.com/leanprover-community/mathlib/commit/6781ff0f6f6549810d0446ba62a4214449246d27)
feat(tactic/linarith): prefer type of goal if there are multiple types

### [2019-01-27T22:28:46+01:00](https://github.com/leanprover-community/mathlib/commit/8affebda3af9d2646b2705c98b4182c5ff0f4146)
fix(tactic/linarith): remove unused code

### [2019-01-27T22:28:46+01:00](https://github.com/leanprover-community/mathlib/commit/92508dccae8613e23df4731adec41ae7d59cdf6d)
fix(tactic/linarith): properly handle problems with inequalities in multiple types
When problems have inequalities over multiple types, it's almost safe to process everything at once, since none of the
variables overlap. But linarith deals with constants by homogenizing them and the "constant" variables do overlap.
This fix creates one call to linarith for each type that appears in a hypothesis.

### [2019-01-27T00:35:53-05:00](https://github.com/leanprover-community/mathlib/commit/84d1c450111d4c576c7aefd3a7901c4aa07d0b6f)
feat(tactic/match-stub): use Lean holes to create a pattern matching skeleton ([#630](https://github.com/leanprover-community/mathlib/pull/#630))

* feat(tactic/match-stub): use Lean holes to create a pattern matching skeleton

* feat(tactic/match-stub): add hole for listing relevant constructors

### [2019-01-25T17:50:12+01:00](https://github.com/leanprover-community/mathlib/commit/315a6427ddf252a1ee3a94d528e498a7f7f1e1ba)
feat(measure_theory): add Hahn decomposition

### [2019-01-24T16:02:42+01:00](https://github.com/leanprover-community/mathlib/commit/ed2ab1a391fcbd9922d089be47bc7d51b2d5789c)
feat(measure_theory): measures form a complete lattice

### [2019-01-24T09:18:32+01:00](https://github.com/leanprover-community/mathlib/commit/4aacae313ef096c33ed52a996dddd9bb9756b413)
feat(data/equiv/algebra): instances for transporting algebra across an equiv ([#618](https://github.com/leanprover-community/mathlib/pull/#618))

### [2019-01-24T09:17:37+01:00](https://github.com/leanprover-community/mathlib/commit/c49e89df9867022e44a9a00e6e099d70b61249c9)
feat(category_theory/adjunction): definitions, basic proofs, and examples ([#619](https://github.com/leanprover-community/mathlib/pull/#619))

### [2019-01-23T16:35:39+01:00](https://github.com/leanprover-community/mathlib/commit/0e6c3589fad3519fe1e55e981bb0d2bcbcb8cd59)
feat(set_theory/cardinal): more lemmas on cardinality ([#595](https://github.com/leanprover-community/mathlib/pull/#595))

### [2019-01-23T14:24:28+01:00](https://github.com/leanprover-community/mathlib/commit/9be8905efd5c47725db1d2cc085678a25d58e44c)
refactor(topology/sequences): restructure proofs

### [2019-01-23T14:24:12+01:00](https://github.com/leanprover-community/mathlib/commit/4018daff1b1fa72867e6b8c194ab1b9e26f3258c)
feat(topology): sequences, sequential spaces, and sequential continuity (closes [#440](https://github.com/leanprover-community/mathlib/pull/#440))

Co-Authored-By: Reid Barton <rwbarton@gmail.com>

### [2019-01-23T13:24:31+01:00](https://github.com/leanprover-community/mathlib/commit/c06fb67cf8b7bcc3e5e76c46b699d01cd4c212a6)
refactor(category_theory/category): split off has_hom

This gives a little more flexibility when defining a category,
which will be used for opposite categories. It should also be
useful for defining the free category on a graph.

### [2019-01-23T12:52:40+01:00](https://github.com/leanprover-community/mathlib/commit/2c95d2a134762260fbb6ede0adf11ed50efcb5ea)
maintain(vscode): add ruler at 100 in editor

### [2019-01-23T12:52:40+01:00](https://github.com/leanprover-community/mathlib/commit/b2700dd36618dbfd295491c5e28b3d2b22fbd830)
maintain(.vscode): add default settings

### [2019-01-23T12:45:23+01:00](https://github.com/leanprover-community/mathlib/commit/6da9b21f3d1507ea994fc30a14a0dba88a3bff7f)
le_induction

### [2019-01-23T12:38:43+01:00](https://github.com/leanprover-community/mathlib/commit/60efaec1b2bae0b6ff22ebd889f26606c8648924)
chore(topology): move contraction_mapping to metric_space/lipschitz

### [2019-01-23T11:48:36+01:00](https://github.com/leanprover-community/mathlib/commit/5317b593978588091d5f0fd538533ff0155ac535)
refactor(contraction_mapping): add more proves about Lipschitz continuous functions; cleanup proofs

### [2019-01-23T11:48:20+01:00](https://github.com/leanprover-community/mathlib/commit/96198b984026f71bc071688fce66435caa940520)
feat(contraction_mapping): proof the Banach fixed-point theorem (closes [#553](https://github.com/leanprover-community/mathlib/pull/#553))

### [2019-01-23T11:43:23+01:00](https://github.com/leanprover-community/mathlib/commit/8a0fd0b0cb8b8cab848a1f86d8413019c131ea2d)
feat(order): add order instances for prod

### [2019-01-23T08:09:04+01:00](https://github.com/leanprover-community/mathlib/commit/2ae2cf04471ba23213dd8d4bb0a5b9bdfef5b0d0)
feat(linear_algebra/multivariate_polynomial): C_mul'

### [2019-01-22T17:23:23-05:00](https://github.com/leanprover-community/mathlib/commit/8d44feebb4aa88264ee564eae82e3fd28762b629)
style(category_theory): adjust precedence of ⥤ ([#616](https://github.com/leanprover-community/mathlib/pull/#616))

### [2019-01-22T17:21:55-05:00](https://github.com/leanprover-community/mathlib/commit/c9a0b337cd3e8970fb3e398c0132a63102af2468)
refactor(category_theory/fully_faithful): move preimage_id ([#615](https://github.com/leanprover-community/mathlib/pull/#615))

### [2019-01-22T16:49:24+01:00](https://github.com/leanprover-community/mathlib/commit/edfa2061547510a41db4d0d471130badcb92ef20)
feat(linear_algebra/dimension): more dimension theorems; rank of a linear map

### [2019-01-22T16:02:10+01:00](https://github.com/leanprover-community/mathlib/commit/6e4c9ba84d9d2dfa430507eb57cfd4b0c646cf65)
feat(linear_algebra/linear_combination): lc lifts vector spaces

### [2019-01-22T16:00:18+01:00](https://github.com/leanprover-community/mathlib/commit/d5a302ff544e1cb4cfe81957895313944282c5de)
chore(linear_algebra): rename file lc to linear_combination

### [2019-01-22T15:32:49+01:00](https://github.com/leanprover-community/mathlib/commit/7baf093a9fb50b81e2142701eba100a6a7830d74)
feat(data/list,data/multiset,data/finset): add Ico intervals (closes [#496](https://github.com/leanprover-community/mathlib/pull/#496))

### [2019-01-21T20:02:01-05:00](https://github.com/leanprover-community/mathlib/commit/3dc9935aad61ce539c7a0b98f3c20f41607ae159)
fix(tactic/instance_stub): extend the applicability of instance_stub ([#612](https://github.com/leanprover-community/mathlib/pull/#612))

### [2019-01-21T11:12:50+01:00](https://github.com/leanprover-community/mathlib/commit/bc163a6e5992f5aa2b8eb0f241a3603ee512f1f6)
fix(.travis.yml): produce mathlib.txt only from src/

### [2019-01-20T22:50:48-05:00](https://github.com/leanprover-community/mathlib/commit/c1e594bc3dfb6c9357e94196cc3ae5d435bb07f1)
feat(meta, logic, tactic): lean 3.4.2: migrate coinductive_predicates, transfer, relator ([#610](https://github.com/leanprover-community/mathlib/pull/#610))

### [2019-01-20T20:42:15-05:00](https://github.com/leanprover-community/mathlib/commit/2c5bc214d1391659611591f4c6af222f2bea8e05)
feat(topology/emetric_space): basic facts for emetric spaces ([#608](https://github.com/leanprover-community/mathlib/pull/#608))

### [2019-01-19T18:43:24-05:00](https://github.com/leanprover-community/mathlib/commit/fa2e3991e1199afa8029c5417c2f719b3a326a77)
feat(topology/bounded_continuous_function): constructor in normed groups ([#607](https://github.com/leanprover-community/mathlib/pull/#607))

### [2019-01-18T19:50:09-05:00](https://github.com/leanprover-community/mathlib/commit/3fcba7d0eeacd931449af515ea478a032a3edd8a)
feat(logic/basic): add class 'unique' for uniquely inhabited types ([#605](https://github.com/leanprover-community/mathlib/pull/#605))

### [2019-01-18T16:30:23-05:00](https://github.com/leanprover-community/mathlib/commit/41b3fdd61a3ce0fc743d359d80097b2d3737b2f2)
feat(topology/real): bounded iff bounded below above ([#606](https://github.com/leanprover-community/mathlib/pull/#606))

### [2019-01-18T15:36:40+01:00](https://github.com/leanprover-community/mathlib/commit/eb1253fe08b878e959e884392ee08b4111c67709)
feat(measure_theory): add Giry monad

### [2019-01-18T14:10:04+01:00](https://github.com/leanprover-community/mathlib/commit/739d28a60f347e7357b76cd2d24e41460e49a456)
refactor(ring_theory/multiplicity): replace padic_val with multiplicity ([#495](https://github.com/leanprover-community/mathlib/pull/#495))

### [2019-01-18T13:28:37+01:00](https://github.com/leanprover-community/mathlib/commit/6144710d83d612b1f04634aa2979b3319daee543)
feat(measure_theory): add equivalence of measurable spaces

### [2019-01-18T13:26:32+01:00](https://github.com/leanprover-community/mathlib/commit/b352d2cbee4c9908d4443ec495ae75e8064121ba)
refactor(topology): topological_space.induced resembles set.image; second_countable_topology on subtypes; simplify filter.map_comap

### [2019-01-18T13:20:03+01:00](https://github.com/leanprover-community/mathlib/commit/6b6b04ac2bf69e2921d4fb978ed7ea9c9e9a0a78)
feat(order/complete_lattice): add rules for supr/infi under image and under propositions

### [2019-01-18T11:13:09+01:00](https://github.com/leanprover-community/mathlib/commit/f0f06ca1d07b441eda86342413b0088afb8aa875)
refactor(*): analysis reorganization ([#598](https://github.com/leanprover-community/mathlib/pull/#598))

* split `measure_theory` and `topology` out of analysis
* add `instances` sub directories for theories around type class instances

### [2019-01-17T19:21:33-05:00](https://github.com/leanprover-community/mathlib/commit/c1f162caadff0fc13738772dab36d8bad7739f62)
fix(tactic/linarith): don't reject expressions with division by variables ([#604](https://github.com/leanprover-community/mathlib/pull/#604))

norm_hyp_aux should have succeeded (without changing the type of h') in the case where lhs contains 1/x. But mk_single_comp_zero_pf is too clever when given the coeff 1. norm_hyp_aux will still do unnecessary work when it finds e.g. 1/(2*x), but shouldn't fail.

### [2019-01-17T14:37:38-05:00](https://github.com/leanprover-community/mathlib/commit/ae610a04404a7c64cf75d64eacb8228c54cc8487)
feat(ring_theory/adjoin_root): adjoin roots to polynomials ([#603](https://github.com/leanprover-community/mathlib/pull/#603))

### [2019-01-16T08:50:38-05:00](https://github.com/leanprover-community/mathlib/commit/5c37507c58d95f93ef0f587b2de2dabd75daec12)
doc(elan.md): fix msys2 setup ([#594](https://github.com/leanprover-community/mathlib/pull/#594)) [ci-skip]

For me, adding the suggested line to .profile did not change my path, even after restarting the terminal.
Moreover, elan is installed in $USERPROFILE/.elan/bin, not in $HOME/.elan/bin.
Adding $USERPROFILE/.elan/bin to the path did not work for me, so I give the full path.

### [2019-01-16T08:33:19-05:00](https://github.com/leanprover-community/mathlib/commit/5dd9998fc88d73cc3cf11239ea17b40375b9e86c)
doc(docs/tactics): document `convert` ([#601](https://github.com/leanprover-community/mathlib/pull/#601)) [ci-skip]

### [2019-01-16T08:14:44-05:00](https://github.com/leanprover-community/mathlib/commit/ab5849ed5dda3f8c553250fa9a74927dac4e2c09)
style(category_theory/opposites): increase binding power of ᵒᵖ ([#600](https://github.com/leanprover-community/mathlib/pull/#600))

### [2019-01-15T17:43:36-05:00](https://github.com/leanprover-community/mathlib/commit/024da4095269392369f0d818be5f0ada9b173e18)
refactor(logic/schroeder_bernstein): move to set_theory/ ([#599](https://github.com/leanprover-community/mathlib/pull/#599))

### [2019-01-15T12:05:23-05:00](https://github.com/leanprover-community/mathlib/commit/d4f80f664975f8ea614cb4b02f937c941353ed07)
refactor(*): Try again moving everything to src ([#597](https://github.com/leanprover-community/mathlib/pull/#597))

### [2019-01-15T10:51:04-05:00](https://github.com/leanprover-community/mathlib/commit/78f1949719676db358ea5e68e211a73e2ce95e7b)
refactor(*): move everything into `src` ([#583](https://github.com/leanprover-community/mathlib/pull/#583))

### [2019-01-15T11:15:57+01:00](https://github.com/leanprover-community/mathlib/commit/0c710160f5c7012054bdbbd7b44df3574a2b14e4)
feat(logic/basic): nonempty.map

### [2019-01-14T14:48:02+01:00](https://github.com/leanprover-community/mathlib/commit/667dcf379263f7f4cadbd5416a6bf7f0db8a2d67)
feat(group_theory/sylow): first sylow theorem (closes [#591](https://github.com/leanprover-community/mathlib/pull/#591))

### [2019-01-14T14:05:58+01:00](https://github.com/leanprover-community/mathlib/commit/f63fb54dab45fdb1e9da4a33653407334bea954f)
doc(tactic/simpa): rewrite simpa doc

### [2019-01-14T13:34:42+01:00](https://github.com/leanprover-community/mathlib/commit/49c059a4067bf842ca1873555e7e7ce39172019a)
refactor(analysis): add metric namespace

combines changes from @sgouezel, @PatrickMassot, and @digama0

### [2019-01-14T13:34:16+01:00](https://github.com/leanprover-community/mathlib/commit/2f9f3df7759b9d79060115e291d883daca2831c3)
doc(tactic/simpa): update simpa documentation

### [2019-01-14T13:34:16+01:00](https://github.com/leanprover-community/mathlib/commit/263e8a02216f047fd650358f904745b0c42a7baf)
fix(tactic/simpa): only try given expression in "simpa using"

### [2019-01-14T12:27:12+01:00](https://github.com/leanprover-community/mathlib/commit/4de9682ccc6ca83e97c41cc3a7a3e256bbb38397)
fix(PULL_REQUEST_TEMPLATE): use absolute urls

The relative urls do not resolve correctly.

### [2019-01-14T12:03:28+01:00](https://github.com/leanprover-community/mathlib/commit/c7f13fd7142213deae61c9d172e71cd4f45415ce)
feat(.vscode): add copyright snippet

### [2019-01-13T19:02:05+01:00](https://github.com/leanprover-community/mathlib/commit/b03c0aac3faf940b55461ff2b7800ebe631644f5)
feat(group_theory/sylow): Cauchy's theorem ([#458](https://github.com/leanprover-community/mathlib/pull/#458))

* feat(group_theory): adding add_subgroup and add_submonoid
* feat(data/list/basic): rotate a list

### [2019-01-12T10:19:18-05:00](https://github.com/leanprover-community/mathlib/commit/dc6c38a765799c99c4d9c8d5207d9e6c9e0e2cfd)
fix(field_theory/subfield): is_subfield should be a Prop ([#588](https://github.com/leanprover-community/mathlib/pull/#588))

### [2019-01-11T19:01:39+01:00](https://github.com/leanprover-community/mathlib/commit/e61a464518dda2bf00529e7ed5ba7914cae97aba)
feat(ring_theory/euclidean_domain): add more specific Euclidean domain stuff ([#527](https://github.com/leanprover-community/mathlib/pull/#527))

### [2019-01-11T18:59:19+01:00](https://github.com/leanprover-community/mathlib/commit/5c323cdc612bf01c8a375da7e56a013e86a0e2a2)
feat(category_theory): over and under categories  ([#549](https://github.com/leanprover-community/mathlib/pull/#549))

### [2019-01-11T18:17:13+01:00](https://github.com/leanprover-community/mathlib/commit/c19b4bec99fca1badf60e1909b32fdcabbafe7f2)
feat(meta/rb_map): add some monadic filtering

### [2019-01-11T17:06:02+01:00](https://github.com/leanprover-community/mathlib/commit/7a9b2e40a1d16336002cfb6a8c0e601ea27825ae)
Update PULL_REQUEST_TEMPLATE.md

### [2019-01-11T17:04:58+01:00](https://github.com/leanprover-community/mathlib/commit/6516c34cc4c7f3f8cdcdcc6331529a54ca7c3d54)
doc(README): elect new maintainers

### [2019-01-11T15:35:42+01:00](https://github.com/leanprover-community/mathlib/commit/4f3f86d20c5accb2774705156cce03ba263d97ed)
chore(ring_theory/subring): remove unused import

### [2019-01-11T11:37:17+01:00](https://github.com/leanprover-community/mathlib/commit/45787967c2ffb4a8093cfeac959bb2cdb1246e86)
feat(data/polynomial): various lemmas about degree and monic and coeff

### [2019-01-10T15:26:30-05:00](https://github.com/leanprover-community/mathlib/commit/b1684fee21a11528731a06bfaff1211eead08d10)
fix(principal_ideal_domain): correct spelling mistake ([#582](https://github.com/leanprover-community/mathlib/pull/#582))

### [2019-01-10T12:11:24+01:00](https://github.com/leanprover-community/mathlib/commit/6e97721b676d152e4db12c0aab419c88d342e38a)
refactor(principal_ideal_domain): simplify proof of PID -> UFD

### [2019-01-10T12:11:24+01:00](https://github.com/leanprover-community/mathlib/commit/f5bf2776c9b298a5679e6df28f0f0fc2556518f7)
refactor(unique_factorization_domain): simplify definition of UFD

### [2019-01-10T09:46:28+01:00](https://github.com/leanprover-community/mathlib/commit/8b66ebde21a68d405b1f2f783b01cad63f14e3b9)
functions and cardinality ([#556](https://github.com/leanprover-community/mathlib/pull/#556))

### [2019-01-09T10:08:23+01:00](https://github.com/leanprover-community/mathlib/commit/f488635dfa1b4bb69a4eeb552de8d0d37de81492)
chore(tactic/monotonicity/interactive) use derive for has_reflect ([#578](https://github.com/leanprover-community/mathlib/pull/#578))

### [2019-01-09T10:07:56+01:00](https://github.com/leanprover-community/mathlib/commit/af735a56bb3870d70a5754c8a848d8c28b992fc4)
feat(field_theory/finite): field_of_integral_domain ([#579](https://github.com/leanprover-community/mathlib/pull/#579))

### [2019-01-09T09:48:35+01:00](https://github.com/leanprover-community/mathlib/commit/d0532c10d3a85a78c168a6611c83269c8a78815a)
feat(data/polynomial): lemmas about map ([#530](https://github.com/leanprover-community/mathlib/pull/#530))

### [2019-01-05T16:41:07-05:00](https://github.com/leanprover-community/mathlib/commit/2e636352061a7fefde8db2c2f775ad0e63554ff2)
feat(group_theory/subgroup): simple groups ([#572](https://github.com/leanprover-community/mathlib/pull/#572))

### [2019-01-05T16:38:38-05:00](https://github.com/leanprover-community/mathlib/commit/d19c9bc07298cd40db3d42586db0f2dbc40814c1)
feat(data/fintype): decidable_left_inverse_fintype ([#575](https://github.com/leanprover-community/mathlib/pull/#575))

### [2019-01-05T16:37:57-05:00](https://github.com/leanprover-community/mathlib/commit/395aaddddc036fdd36bbf5c2c6cc115b6018b823)
feat(group_theory/sign): sign_surjective ([#576](https://github.com/leanprover-community/mathlib/pull/#576))

### [2019-01-05T14:19:05-05:00](https://github.com/leanprover-community/mathlib/commit/b9c5eb05effa1dd3a9d9e10efef7e164d9752f47)
feat(ring_theory/multiplicity): multiplicity of elements of a ring ([#523](https://github.com/leanprover-community/mathlib/pull/#523))

### [2019-01-05T14:17:10-05:00](https://github.com/leanprover-community/mathlib/commit/bc96ecadccde494ca901da34c93d0343ff64619f)
feat(group_theory/quotient_group): quotient_ker_equiv_range ([#574](https://github.com/leanprover-community/mathlib/pull/#574))

### [2019-01-05T14:13:47-05:00](https://github.com/leanprover-community/mathlib/commit/3ff5e93ed8399d5ac6916be916ad407f3868b6fa)
feat(data/polynomial): polynomials over a field are a normalization domain ([#560](https://github.com/leanprover-community/mathlib/pull/#560))

### [2019-01-05T14:12:49-05:00](https://github.com/leanprover-community/mathlib/commit/87bf61841d7095976d47ea70503d9e49035dcd73)
feat(data/polynomial): C_neg and C_sub ([#561](https://github.com/leanprover-community/mathlib/pull/#561))

### [2019-01-05T14:12:25-05:00](https://github.com/leanprover-community/mathlib/commit/78d0ebf3c337f34d1afe6da3da90ba08cc867bf6)
feat(data/multiset): prod_hom and exists_mem_of_rel_of_mem ([#562](https://github.com/leanprover-community/mathlib/pull/#562))

### [2019-01-05T14:11:58-05:00](https://github.com/leanprover-community/mathlib/commit/4e509a86ed0597c0f0fa2d18b95ec2fd6c4e6fa0)
feat(ring_theory/noetherian): irreducible_induction_on ([#563](https://github.com/leanprover-community/mathlib/pull/#563))

### [2019-01-05T14:10:24-05:00](https://github.com/leanprover-community/mathlib/commit/ea0ff0583c7625f2babe099f06a26e44be5f5959)
doc(category_theory): update `category_theory` documentation ([#564](https://github.com/leanprover-community/mathlib/pull/#564)) [ci-skip]

### [2019-01-05T14:09:18-05:00](https://github.com/leanprover-community/mathlib/commit/33df7eccf70d043aad473437fb74a9e67630ae7b)
feat(data/nat/enat): has_well_founded for enat ([#565](https://github.com/leanprover-community/mathlib/pull/#565))

### [2019-01-05T14:06:39-05:00](https://github.com/leanprover-community/mathlib/commit/4bacdf21772542f04dc54ee6558ebc19e6608f0e)
feat(logic/basic): inhabited_of_nonempty with instance parameter ([#566](https://github.com/leanprover-community/mathlib/pull/#566))

### [2019-01-05T14:05:50-05:00](https://github.com/leanprover-community/mathlib/commit/125feb6411f963f29cfa9d9bfcc9c7c89238bd3a)
feat(data/multiset): forall_of_pairwise ([#569](https://github.com/leanprover-community/mathlib/pull/#569))

### [2019-01-05T14:05:30-05:00](https://github.com/leanprover-community/mathlib/commit/da6ec21832ff3ae189fed471b58ce8f5f2b2b793)
feat(algebra/group): is_conj_one_right ([#570](https://github.com/leanprover-community/mathlib/pull/#570))

### [2019-01-05T14:05:06-05:00](https://github.com/leanprover-community/mathlib/commit/a32fa18f94d9ef7ac05efbb935839aa477a281dd)
feat(data/finset): finset.card_eq_one ([#571](https://github.com/leanprover-community/mathlib/pull/#571))

### [2019-01-05T04:49:24-05:00](https://github.com/leanprover-community/mathlib/commit/40fa9ade2f5649569639608db5e621e5fad0cc02)
fix(analysis/measure_theory): fix build

### [2019-01-04T20:28:21-05:00](https://github.com/leanprover-community/mathlib/commit/93a330e9867d2891875afb5ab0d8375fd2c20161)
fix(data/real/cau_seq_filter): fix build

### [2019-01-04T19:43:43-05:00](https://github.com/leanprover-community/mathlib/commit/19e7b1f574d813b9b305b41f8c0820c01bf99c84)
feat(analysis/topology): Bounded continuous functions ([#464](https://github.com/leanprover-community/mathlib/pull/#464))

### [2019-01-02T10:12:17-05:00](https://github.com/leanprover-community/mathlib/commit/dcd0466de4add821402454281552eeaef0593843)
feat(analysis/topology): complete sets, minor modifications ([#557](https://github.com/leanprover-community/mathlib/pull/#557))

### [2019-01-02T08:57:30-05:00](https://github.com/leanprover-community/mathlib/commit/f59f5d55fcdfdb26a62ba07ed027a1faa82afe93)
feat(data/real/ennreal): minor additions to ennreal ([#558](https://github.com/leanprover-community/mathlib/pull/#558))

### [2019-01-02T06:39:37-05:00](https://github.com/leanprover-community/mathlib/commit/50583b9e34d06db005db48663541e9e0bb3e5e32)
feat(algebra/order): additional theorems on cmp