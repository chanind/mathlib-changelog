### [2019-11-30 16:23:56](https://github.com/leanprover-community/mathlib/commit/343c54d)
feat(analysis/complex/exponential): limits of exp ([#1744](https://github.com/leanprover-community/mathlib/pull/1744))
* staging
* exp div pow
* cleanup
* oops
* better proof
* cleanup
* docstring
* typo in docstring

### [2019-11-29 21:47:26](https://github.com/leanprover-community/mathlib/commit/e68b2be)
doc(docs/contribute, meta/expr): sectioning doc strings  ([#1723](https://github.com/leanprover-community/mathlib/pull/1723))
* doc(docs/contribute, meta/expr): explain sectioning doc strings and show in practice
* updates

### [2019-11-29 20:59:58](https://github.com/leanprover-community/mathlib/commit/b46ef84)
doc(windows.md): update [ci skip] ([#1742](https://github.com/leanprover-community/mathlib/pull/1742))
* doc(windows.md): update [ci skip]
* small
* Update docs/install/windows.md
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* wording

### [2019-11-29 18:51:59](https://github.com/leanprover-community/mathlib/commit/9bb69dc)
feat(analysis/specific_limits): add `cauchy_seq_of_edist_le_geometric` ([#1743](https://github.com/leanprover-community/mathlib/pull/1743))
* feat(analysis/specific_limits): add `cauchy_seq_of_edist_le_geometric`
Other changes:
* Estimates on the convergence rate both in `edist` and `dist` cases.
* Swap lhs with lhs in `ennreal.tsum_coe` and `nnreal.tsum_coe`,
  rename accordingly
* Use `(1 - r)⁻¹` instead of `1 / (1 - r)` in `has_sum_geometric`
* Add some docstrings
* Update src/analysis/specific_limits.lean

### [2019-11-29 16:54:30](https://github.com/leanprover-community/mathlib/commit/817711d)
feat(measure_theory/bochner_integration): linearity of the Bochner Integral ([#1745](https://github.com/leanprover-community/mathlib/pull/1745))
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

### [2019-11-29 14:50:53](https://github.com/leanprover-community/mathlib/commit/65bdbab)
chore(topology/instances/ennreal): simplify some statements&proofs ([#1750](https://github.com/leanprover-community/mathlib/pull/1750))
API changes:
* `nhds_top`: use `⨅a ≠ ∞` instead of `⨅a:{a:ennreal // a ≠ ⊤}`
* `nhds_zero`, `nhds_of_ne_top` : similarly to `nhds_top`
* `tendsto_nhds`: get rid of the intermediate set `n`.

### [2019-11-29 13:45:43](https://github.com/leanprover-community/mathlib/commit/8f11c46)
feat(data/real/ennreal): more simp lemmas about `inv` and continuity of `inv` ([#1749](https://github.com/leanprover-community/mathlib/pull/1749))
* Prove some algebraic properties of `ennreal.inv`
* More algebraic lemmas
* Prove continuity of `inv`

### [2019-11-29 11:45:14](https://github.com/leanprover-community/mathlib/commit/1b3347d)
feat(algebra/*,data/real/*): add some inequalities about `canonically_ordered_comm_semiring`s ([#1746](https://github.com/leanprover-community/mathlib/pull/1746))
Use them for `nnreal` and `ennreal`.

### [2019-11-29 07:22:29](https://github.com/leanprover-community/mathlib/commit/8e74c62)
chore(data/finset,order/filter): simplify a few proofs ([#1747](https://github.com/leanprover-community/mathlib/pull/1747))
Also add `finset.image_mono` and `finset.range_mono`.

### [2019-11-27 19:49:59](https://github.com/leanprover-community/mathlib/commit/198fb09)
feat(analysis/complex/exponential): derivatives ([#1695](https://github.com/leanprover-community/mathlib/pull/1695))
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

### [2019-11-27 17:34:07](https://github.com/leanprover-community/mathlib/commit/01b1576)
feat(topology/algebra/infinite_sum): prove `cauchy_seq_of_edist_le_of_summable` ([#1739](https://github.com/leanprover-community/mathlib/pull/1739))
* feat(topology/algebra/infinite_sum): prove `cauchy_seq_of_edist_le_of_summable`
Other changes:
* Add estimates on the distance to the limit (`dist` version only)
* Simplify some proofs
* Add some supporting lemmas
* Fix a typo in a lemma name in `ennreal`
* Add `move_cast` attrs
* More `*_cast` tags, use `norm_cast`

### [2019-11-26 14:35:37](https://github.com/leanprover-community/mathlib/commit/255bebc)
feat(data/nat/multiplicity): multiplicity_choose and others ([#1704](https://github.com/leanprover-community/mathlib/pull/1704))

### [2019-11-26 12:10:33](https://github.com/leanprover-community/mathlib/commit/3443a7d)
feat(analysis/complex/basic): restriction of scalars, real differentiability of complex functions ([#1716](https://github.com/leanprover-community/mathlib/pull/1716))
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

### [2019-11-26 09:03:27](https://github.com/leanprover-community/mathlib/commit/33df7e8)
feat(order/conditionally_complete_lattice): with_top (with_bot L) ins… ([#1725](https://github.com/leanprover-community/mathlib/pull/1725))
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

### [2019-11-25 19:40:41](https://github.com/leanprover-community/mathlib/commit/ef47de4)
chore(data/nat/basic): add some docs, drop unused arguments ([#1741](https://github.com/leanprover-community/mathlib/pull/1741))
* add a docstring
* chore(data/nat/basic): add some docs, drop unused arguments

### [2019-11-25 17:00:45](https://github.com/leanprover-community/mathlib/commit/73735ad)
feat(topology/metric_space/basic): define `cauchy_seq_of_le_tendsto_0` ([#1738](https://github.com/leanprover-community/mathlib/pull/1738))
* Define `cauchy_seq_of_le_tendsto_0`
Sometimes it is convenient to avoid proving `0 ≤ b n`.
* Fix the comment, generalize to an inhabitted `sup`-semilattice.

### [2019-11-25 09:29:09](https://github.com/leanprover-community/mathlib/commit/242159f)
feat(measure_theory/bochner_integration): bochner integral of simple functions ([#1676](https://github.com/leanprover-community/mathlib/pull/1676))
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

### [2019-11-25 00:45:56](https://github.com/leanprover-community/mathlib/commit/6af35ec)
feat(topology/algebra/infinite_sum): add `has_sum` versions of a few `tsum` lemmas ([#1737](https://github.com/leanprover-community/mathlib/pull/1737))
Also add a few lemmas in `analysis/specific_limits`

### [2019-11-24 23:51:18](https://github.com/leanprover-community/mathlib/commit/bf509d7)
feat(order/filter/basic): add more lemmas about `tendsto _ _ at_top` ([#1713](https://github.com/leanprover-community/mathlib/pull/1713))
* feat(order/filter/basic): add more lemmas about `tendsto _ _ at_top`
* Use explicit arguments as suggested by @sgouezel
* Add lemmas for an `ordered_comm_group`
* Add a missing lemma

### [2019-11-24 23:02:27](https://github.com/leanprover-community/mathlib/commit/a03a072)
chore(topology/metric_space/emetric_space): define `edist_le_zero` ([#1735](https://github.com/leanprover-community/mathlib/pull/1735))
This makes a few proofs slightly more readable.

### [2019-11-24 20:38:04](https://github.com/leanprover-community/mathlib/commit/13fedc1)
feat(algebra/group): define `mul/add_left/right_injective` ([#1730](https://github.com/leanprover-community/mathlib/pull/1730))
Same as `mul_left_cancel` etc but uses `function.injective`.
This makes it easier to use functions from `function.injective` namespace.

### [2019-11-24 19:51:44](https://github.com/leanprover-community/mathlib/commit/7b1cdd4)
feat(topology/metric_space/emetric_space): polygonal inequalities ([#1736](https://github.com/leanprover-community/mathlib/pull/1736))
Migrate [#1572](https://github.com/leanprover-community/mathlib/pull/1572) from `dist` to `edist`

### [2019-11-24 17:44:38](https://github.com/leanprover-community/mathlib/commit/ca53b5d)
feat(data/real/ennreal): 3 simple lemmas ([#1734](https://github.com/leanprover-community/mathlib/pull/1734))

### [2019-11-24 10:11:36](https://github.com/leanprover-community/mathlib/commit/2d54a70)
feat(analysis/normed_space): prove more lemmas, rename some old lemmas ([#1733](https://github.com/leanprover-community/mathlib/pull/1733))
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

### [2019-11-23 11:38:03](https://github.com/leanprover-community/mathlib/commit/f95c01e)
feat(algebra/ordered_*): add three simple lemmas ([#1731](https://github.com/leanprover-community/mathlib/pull/1731))

### [2019-11-23 00:15:59](https://github.com/leanprover-community/mathlib/commit/f86abc7)
fix(*): lower instance priority ([#1724](https://github.com/leanprover-community/mathlib/pull/1724))
* fix(*): lower instance priority
use lower instance priority for instances that always apply
also do this for automatically generated instances using the `extend` keyword
also add a comment to most places where we short-circuit type-class inference. This can lead to greatly increased search times (see issue [#1561](https://github.com/leanprover-community/mathlib/pull/1561)), so we might want to delete some/all of them.
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

### [2019-11-22 21:37:11](https://github.com/leanprover-community/mathlib/commit/2b3eaa8)
feat(README) Point users to the tutorial project ([#1728](https://github.com/leanprover-community/mathlib/pull/1728))
I think the tutorial project is a good place to start, and if other people don't think it is then I think they might want to consider adding more files to the tutorial project. I think mathlib is intimidating for beginners and this is a much better idea. However the link to the tutorial project is not even available on the main page -- you have to click through an installation procedure and find it at the bottom, and even then the first thing is suggests is that you make a new project, which I think is harder than getting the tutorial project up and running. This PR proposes that we point people directly to the tutorial project -- they will probably notice the existence of the tutorial project before they have even installed Lean/mathlib and will hence have it at the back of their mind once they've got things up and running.

### [2019-11-22 21:18:35](https://github.com/leanprover-community/mathlib/commit/013e914)
fix(docs/install/project) compiling is quick ([#1727](https://github.com/leanprover-community/mathlib/pull/1727))
I think the "it takes a long time" comment must either have been from before `update-mathlib` or from when we were pointing people to the perfectoid project.

### [2019-11-22 20:20:52](https://github.com/leanprover-community/mathlib/commit/62c1bc5)
doc(topology/metric_space,measure_theory): move text in copyright docs to module docs ([#1726](https://github.com/leanprover-community/mathlib/pull/1726))

### [2019-11-22 17:45:25+01:00](https://github.com/leanprover-community/mathlib/commit/5a1a469)
docs(README): revert 96ebf8cc
Revert "docs(README): Remove Patrick from the maintainer list."
This reverts commit 96ebf8cc7c446e977637a13740645a7f8e0c8992.

### [2019-11-21 22:11:03](https://github.com/leanprover-community/mathlib/commit/004618a)
feat(data/nat): two lemmas about choose ([#1717](https://github.com/leanprover-community/mathlib/pull/1717))
* Two lemmas about choose
* swap choose_symm order

### [2019-11-21 19:22:23](https://github.com/leanprover-community/mathlib/commit/58fc830)
fix(tactic/ext): handle case where goal is solved early ([#1721](https://github.com/leanprover-community/mathlib/pull/1721))
* fix(tactic/ext): handle case where goal is solved early
* add test

### [2019-11-21 17:17:19](https://github.com/leanprover-community/mathlib/commit/a13027a)
feat(data/finset): add cardinality of map ([#1722](https://github.com/leanprover-community/mathlib/pull/1722))
* Add cardinality of map
* Update src/data/finset.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-11-21 11:57:54](https://github.com/leanprover-community/mathlib/commit/faf3289)
add div_le_div_iff ([#1720](https://github.com/leanprover-community/mathlib/pull/1720))

### [2019-11-21 07:04:43](https://github.com/leanprover-community/mathlib/commit/af9dcb9)
make  set_of_eq_eq_singleton a simp lemma ([#1719](https://github.com/leanprover-community/mathlib/pull/1719))

### [2019-11-20 20:03:27](https://github.com/leanprover-community/mathlib/commit/9d031be)
feat(group_theory/congruence): quotients of monoids by congruence relations ([#1710](https://github.com/leanprover-community/mathlib/pull/1710))
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

### [2019-11-20 17:12:35](https://github.com/leanprover-community/mathlib/commit/f34bb6b)
refactor(topology/metric_space/lipschitz): review API of `lipschitz_with` ([#1700](https://github.com/leanprover-community/mathlib/pull/1700))
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

### [2019-11-20 15:36:42](https://github.com/leanprover-community/mathlib/commit/5a6a67f)
fix(data/padics): misstated lemma ([#1718](https://github.com/leanprover-community/mathlib/pull/1718))

### [2019-11-20 01:38:56](https://github.com/leanprover-community/mathlib/commit/0744a3a)
feat(analysis/normed_space/operator_norm): extension of a uniform continuous function ([#1649](https://github.com/leanprover-community/mathlib/pull/1649))
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

### [2019-11-19 23:41:43](https://github.com/leanprover-community/mathlib/commit/d67e527)
feat(algebra/group_power): prove Bernoulli's inequality for `a ≥ -2` ([#1709](https://github.com/leanprover-community/mathlib/pull/1709))
* feat(algebra/group_power): prove Bernoulli's inequality for `a ≥ -2`
* Restate inequalities as suggested by @fpvandoorn
* Fix docs

### [2019-11-19 20:49:00](https://github.com/leanprover-community/mathlib/commit/d4fd722)
feat(algebra/group; data/nat) lemmas for sub sub assoc ([#1712](https://github.com/leanprover-community/mathlib/pull/1712))
* Lemmas for sub sub assoc
* Removed a lemma

### [2019-11-19 18:41:34](https://github.com/leanprover-community/mathlib/commit/db6eab2)
fix(tactic/ring): bugfix ring sub ([#1714](https://github.com/leanprover-community/mathlib/pull/1714))

### [2019-11-19 18:03:43](https://github.com/leanprover-community/mathlib/commit/740168b)
feat(.travis): add linting of new changes to CI ([#1634](https://github.com/leanprover-community/mathlib/pull/1634))
* feat(.travis): add linting of new changes to CI
* explicitly list which linters to use
* upate nolints
* fix nolints.txt
* fix nolints
* remove instance_priority test

### [2019-11-19 16:06:05+01:00](https://github.com/leanprover-community/mathlib/commit/02659d6)
chore(scripts/nolint): regenerate nolints

### [2019-11-19 13:09:36](https://github.com/leanprover-community/mathlib/commit/8d7f093)
fix(tactic/omega): use eval_expr' ([#1711](https://github.com/leanprover-community/mathlib/pull/1711))
* fix(tactic/omega): use eval_expr'
* add test

### [2019-11-19 11:07:21](https://github.com/leanprover-community/mathlib/commit/e3be70d)
lemmas about powers of elements ([#1688](https://github.com/leanprover-community/mathlib/pull/1688))
* feat(algebra/archimedean): add alternative version of exists_int_pow_near
- also add docstrings
* feat(analysis/normed_space/basic): additional inequality lemmas
- that there exists elements with large and small norms in a nondiscrete normed field.
* doc(algebra/archimedean): edit docstrings
* Apply suggestions from code review
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

### [2019-11-19 04:28:27](https://github.com/leanprover-community/mathlib/commit/b0520a3)
feat(algebra/order): define `forall_lt_iff_le` and `forall_lt_iff_le'` ([#1707](https://github.com/leanprover-community/mathlib/pull/1707))

### [2019-11-19 02:27:10](https://github.com/leanprover-community/mathlib/commit/5d5da7e)
feat(data/set/intervals): more lemmas ([#1665](https://github.com/leanprover-community/mathlib/pull/1665))
* feat(data/set/intervals): more lemmas
* Use `simp` in more proofs, drop two `@[simp]` attrs
* Drop more `@[simp]` attrs
It's not clear which side is simpler.

### [2019-11-18 23:52:03](https://github.com/leanprover-community/mathlib/commit/895f1ae)
feat(data/option): add `some_ne_none`, `bex_ne_none`, `ball_ne_none` ([#1708](https://github.com/leanprover-community/mathlib/pull/1708))

### [2019-11-18 20:32:48](https://github.com/leanprover-community/mathlib/commit/6b408eb)
feat(data/real/nnreal): define `nnreal.gi : galois_insertion of_real coe` ([#1699](https://github.com/leanprover-community/mathlib/pull/1699))

### [2019-11-18 18:18:25](https://github.com/leanprover-community/mathlib/commit/af43a2b)
feat(data/nat/enat): add_right_cancel and other ([#1705](https://github.com/leanprover-community/mathlib/pull/1705))

### [2019-11-18 16:16:44](https://github.com/leanprover-community/mathlib/commit/0d94020)
feat(algebra/order_functions): define `min/max_mul_of_nonneg` ([#1698](https://github.com/leanprover-community/mathlib/pull/1698))
Also define `monotone_mul_right_of_nonneg` and rename
`monotone_mul_of_nonneg` to `monotone_mul_left_of_nonneg`.

### [2019-11-18 14:10:09](https://github.com/leanprover-community/mathlib/commit/3f9c4d8)
chore(data/set): use `Sort*` in more lemmas ([#1706](https://github.com/leanprover-community/mathlib/pull/1706))
Also replace `nonempty_of_nonempty_range` with
`range_ne_empty_iff_nonempty` and `range_ne_empty`.
The old lemma is equivalent to `range_ne_empty_iff_nonempty.mp`.

### [2019-11-18 12:21:07](https://github.com/leanprover-community/mathlib/commit/428aec9)
feat(group_theory/congruence): create file about congruence relations ([#1690](https://github.com/leanprover-community/mathlib/pull/1690))
* add congruence.lean
* add has_mul
* add definition of congruence relation
* minor changes
* responding to review comments
* fix docstring mistake in setoid.lean

### [2019-11-18 10:15:17](https://github.com/leanprover-community/mathlib/commit/0a794fa)
feat(data/finset): new union, set difference, singleton lemmas ([#1702](https://github.com/leanprover-community/mathlib/pull/1702))
* Singleton iff unique element lemma
* Set difference lemmas
* Changes from review

### [2019-11-18 08:08:24](https://github.com/leanprover-community/mathlib/commit/fafdcfd)
chore(data/set/lattice): get most proofs from `pi` instance. ([#1685](https://github.com/leanprover-community/mathlib/pull/1685))
This way we only provide proofs that don't come from `pi`

### [2019-11-18 04:03:50](https://github.com/leanprover-community/mathlib/commit/d19f7bc)
feat(analysis/normed_space/finite_dimension): finite-dimensional spaces on complete fields ([#1687](https://github.com/leanprover-community/mathlib/pull/1687))
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

### [2019-11-18 02:08:50](https://github.com/leanprover-community/mathlib/commit/7c5f282)
chore(algebra/order_functions): rename `min/max_distrib_of_monotone` ([#1697](https://github.com/leanprover-community/mathlib/pull/1697))
New names `monotone.map_min/max` better align with `monoid_hom.map_mul` etc.

### [2019-11-18 00:18:22](https://github.com/leanprover-community/mathlib/commit/9607bbf)
feat(algebra/big_operators): sum_Ico_succ_top and others ([#1692](https://github.com/leanprover-community/mathlib/pull/1692))
* feat(Ico): sum_Ico_succ_top and others
* get rid of succ_bot and rename eq_cons

### [2019-11-17 21:17:19](https://github.com/leanprover-community/mathlib/commit/f5385fe)
chore(order_functions): use weakly implicit brackets in strict mono ([#1701](https://github.com/leanprover-community/mathlib/pull/1701))
* chore(order_functions): use weakly implicit brackets in strict mono
* fix build

### [2019-11-17 19:31:14](https://github.com/leanprover-community/mathlib/commit/474004f)
fix(topology/dense_embeddings): tweaks ([#1684](https://github.com/leanprover-community/mathlib/pull/1684))
* fix(topology/dense_embeddings): tweaks
This fixes some small issues with last summer dense embedding refactors.
This is preparation for helping with Bochner integration. Some of those
fixes are backported from the perfectoid project.
* chore(dense_embedding): remove is_closed_property'
* Update src/topology/uniform_space/completion.lean
* Update src/topology/dense_embedding.lean

### [2019-11-17 17:46:28](https://github.com/leanprover-community/mathlib/commit/1805f16)
refactor(order/bounds): make the first argument of `x ∈ upper_bounds s` implicit ([#1691](https://github.com/leanprover-community/mathlib/pull/1691))
* refactor(order/bounds): make the first argument of `x ∈ upper_bounds s` implicit
* Use `∈ *_bounds` in the definition of `conditionally_complete_lattice`.

### [2019-11-17 15:38:07](https://github.com/leanprover-community/mathlib/commit/1034357)
feat(data/int/parity): not_even_iff ([#1694](https://github.com/leanprover-community/mathlib/pull/1694))

### [2019-11-17 05:49:52](https://github.com/leanprover-community/mathlib/commit/e863c08)
feat(algebra/pointwise): set.add_comm_monoid ([#1696](https://github.com/leanprover-community/mathlib/pull/1696))
* feat(algebra/pointwise): set.add_comm_monoid
* defs not instances
* fixing instance names

### [2019-11-17 01:34:34](https://github.com/leanprover-community/mathlib/commit/6b1ab64)
Add lemma for injective pow ([#1683](https://github.com/leanprover-community/mathlib/pull/1683))
* Add lemma for injective pow
* Rename lemma and remove spaces
* Use strict-mono for monotonic pow
* Rename iff statements
* Add left injective pow as well

### [2019-11-15 16:11:27](https://github.com/leanprover-community/mathlib/commit/6ebb7e7)
feat(data/nat/modeq): add_div and others ([#1689](https://github.com/leanprover-community/mathlib/pull/1689))
* feat(data/nat/modeq): add_div and others
* remove unnecessary positivity assumptions.
* fix build
* brackets

### [2019-11-14 21:06:24](https://github.com/leanprover-community/mathlib/commit/40de4fc)
doc(order/bounds,order/conditionaly_complete_lattice): add some docs ([#1686](https://github.com/leanprover-community/mathlib/pull/1686))
* doc(order/bounds,order/conditionaly_complete_lattice): add some docs
* Fixes by @jcommelin
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Fix docs: `is_least` are not unique unless we have a partial order.

### [2019-11-13 22:27:06](https://github.com/leanprover-community/mathlib/commit/6fbf9f7)
doc(*): proper markdown urls [ci skip] ([#1680](https://github.com/leanprover-community/mathlib/pull/1680))

### [2019-11-13 20:20:04](https://github.com/leanprover-community/mathlib/commit/10ced76)
doc(*): move detailed headers into real module docs ([#1681](https://github.com/leanprover-community/mathlib/pull/1681))
* doc(*): move detailed headers into real module docs
* update zmod

### [2019-11-13 17:53:09](https://github.com/leanprover-community/mathlib/commit/4729624)
doc(data/rel): add docs to some definitions ([#1678](https://github.com/leanprover-community/mathlib/pull/1678))
* doc(data/rel): add docs to some definitions
* Update src/data/rel.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/data/rel.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-11-13 14:36:39](https://github.com/leanprover-community/mathlib/commit/6f5ad3c)
add dvd_gcd_iff for nat ([#1682](https://github.com/leanprover-community/mathlib/pull/1682))

### [2019-11-13 12:44:49](https://github.com/leanprover-community/mathlib/commit/6625f66)
feat(analysis/calculus/deriv): one-dimensional derivatives ([#1670](https://github.com/leanprover-community/mathlib/pull/1670))
* feat(analysis/calculus/deriv): one-dimensional derivatives
* Typos.
* Define deriv f x as fderiv 𝕜 f x 1
* Proof style.
* Fix failing proofs.

### [2019-11-13 10:53:30](https://github.com/leanprover-community/mathlib/commit/3bb2b5c)
feat(algebra/big_operators): dvd_sum ([#1679](https://github.com/leanprover-community/mathlib/pull/1679))
* feat(data/multiset): dvd_sum
* feat(algebra/big_operators): dvd_sum
* fix build
* fix build
* fix build

### [2019-11-12 23:38:13](https://github.com/leanprover-community/mathlib/commit/dfd25ff)
chore(meta/expr): delete local_binder_info; rename to_implicit ([#1668](https://github.com/leanprover-community/mathlib/pull/1668))
* chore(meta/expr): delete local_binder_info; rename to_implicit
local_binder_info duplicated local_binding_info.
to_implicit has been renamed to_implicit_local_const, to distinguish it
from to_implicit_binder
* file missing from commit

### [2019-11-12 18:51:50](https://github.com/leanprover-community/mathlib/commit/1749a8d)
feat(group_theory/submonoid): add bundled submonoids and various lemmas ([#1623](https://github.com/leanprover-community/mathlib/pull/1623))
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

### [2019-11-12 16:51:10](https://github.com/leanprover-community/mathlib/commit/7b07932)
feat(analysis/normed_space/operator_norm): continuity of linear forms; swap directions of `nnreal.coe_*` ([#1655](https://github.com/leanprover-community/mathlib/pull/1655))
* feat(analysis/normed_space/operator_norm): continuity of linear forms
* use lift, change nnreal.coe_le direction

### [2019-11-12 15:22:02](https://github.com/leanprover-community/mathlib/commit/14435eb)
feat(algebra/lie_algebra): Define lie algebras ([#1644](https://github.com/leanprover-community/mathlib/pull/1644))
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

### [2019-11-12 13:20:50](https://github.com/leanprover-community/mathlib/commit/08880c9)
feat(data/equiv,category_theory): prove equivalences are the same as isos ([#1587](https://github.com/leanprover-community/mathlib/pull/1587))
* refactor(category_theory,algebra/category): make algebraic categories not [reducible]
Adapted from part of [#1438](https://github.com/leanprover-community/mathlib/pull/1438).
* Update src/algebra/category/CommRing/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* adding missing forget2 instances
* Converting Reid's comment to a [Note]
* adding examples testing coercions
* feat(data/equiv/algebra): equivalence of algebraic equivalences and categorical isomorphisms
* more @[simps]
* more @[simps]

### [2019-11-12 11:23:31](https://github.com/leanprover-community/mathlib/commit/2cbeed9)
style(*): use notation `𝓝` for `nhds` ([#1582](https://github.com/leanprover-community/mathlib/pull/1582))
* chore(*): notation for nhds
* Convert new uses of nhds

### [2019-11-12 07:05:03](https://github.com/leanprover-community/mathlib/commit/3cae70d)
feat(extensionality): generate ext_iff for structures ([#1656](https://github.com/leanprover-community/mathlib/pull/1656))
* feat(extensionality): generate ext_iff for structures
* fix
* core.lean [skip ci]
* Update ext.lean
* Update ext.lean
* Update tactics.md
* Update src/tactic/ext.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

### [2019-11-12 05:02:30](https://github.com/leanprover-community/mathlib/commit/f58f340)
feat(order/lattice): add `monotone.le_map_sup` and `monotone.map_inf_le` ([#1673](https://github.com/leanprover-community/mathlib/pull/1673))
Use it to simplify some proofs in `data/rel`.

### [2019-11-12 03:02:15](https://github.com/leanprover-community/mathlib/commit/c28497f)
chore(*): use `iff.rfl` instead of `iff.refl _` ([#1675](https://github.com/leanprover-community/mathlib/pull/1675))

### [2019-11-11 21:44:54](https://github.com/leanprover-community/mathlib/commit/d077887)
cleanup(data/equiv/basic): drop `quot_equiv_of_quot'`, rename `quot_equiv_of_quot` ([#1672](https://github.com/leanprover-community/mathlib/pull/1672))
* cleanup(data/equiv/basic): drop `quot_equiv_of_quot'`, rename `quot_equiv_of_quot`
* `quot_equiv_of_quot` was the same as `quot.congr`
* rename `quot_equiv_of_quot` to `quot.congr_left` to match
  `quot.congr` and `quot.congr_right`.
* Add docs

### [2019-11-11 15:19:29](https://github.com/leanprover-community/mathlib/commit/a5b3af3)
fix(tactic/core): correct `of_int` doc string ([#1671](https://github.com/leanprover-community/mathlib/pull/1671))

### [2019-11-11 02:02:13](https://github.com/leanprover-community/mathlib/commit/6ecdefc)
chore(analysis/calculus/deriv): rename to fderiv ([#1661](https://github.com/leanprover-community/mathlib/pull/1661))

### [2019-11-10 23:56:06](https://github.com/leanprover-community/mathlib/commit/886b15b)
doc(measure_theory/l1_space): add doc and some lemmas ([#1657](https://github.com/leanprover-community/mathlib/pull/1657))
* Add doc and lemmas
* Remove unnecessary assumption
* Fix integrable_neg
* Remove extra assumptions
* Wrong variable used

### [2019-11-10 21:49:19](https://github.com/leanprover-community/mathlib/commit/ce48727)
fix(order/conditionally_complete_lattice): fix 2 misleading names ([#1666](https://github.com/leanprover-community/mathlib/pull/1666))
* `cSup_upper_bounds_eq_cInf` → `cSup_lower_bounds_eq_cInf`;
* `cInf_lower_bounds_eq_cSup` → `cInf_upper_bounds_eq_cSup`.

### [2019-11-10 19:42:35](https://github.com/leanprover-community/mathlib/commit/f738ec7)
refactor(data/zmod/quadratic_reciprocity): simplify proof of quadratic reciprocity and prove when 2 is a square ([#1609](https://github.com/leanprover-community/mathlib/pull/1609))
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

### [2019-11-10 17:58:18](https://github.com/leanprover-community/mathlib/commit/4e68129)
feat(data/finset): Ico.subset ([#1669](https://github.com/leanprover-community/mathlib/pull/1669))
Does not have the `m1 < n1` assumption required for `subset_iff`

### [2019-11-10 15:51:47](https://github.com/leanprover-community/mathlib/commit/2cd59b4)
feat(coinduction): add identifier list to `coinduction` tactic ([#1653](https://github.com/leanprover-community/mathlib/pull/1653))
* feat(coinduction): add identifier list to `coinduction` tactic
* Update coinductive_predicates.lean
* two doc strings [skip ci]
* Update coinductive_predicates.lean
* fix merge
* move definitions around
* move more stuff
* fix build
* move and document functions

### [2019-11-10 13:45:26](https://github.com/leanprover-community/mathlib/commit/209e039)
cleanup(tactic/core): removing unused tactics ([#1641](https://github.com/leanprover-community/mathlib/pull/1641))
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

### [2019-11-10 11:28:40](https://github.com/leanprover-community/mathlib/commit/4ecc17b)
fix(scripts/mk_all): don't add `lint_mathlib` to `all.lean` [ci skip] ([#1667](https://github.com/leanprover-community/mathlib/pull/1667))

### [2019-11-09 22:41:00](https://github.com/leanprover-community/mathlib/commit/c497f96)
feat(tactic/norm_cast): add push_cast simp attribute ([#1647](https://github.com/leanprover-community/mathlib/pull/1647))
* feat(tactic/norm_cast): add push_cast simp attribute
* test and docs

### [2019-11-09 19:14:09](https://github.com/leanprover-community/mathlib/commit/1236ced)
feat(data/nat/basic): succ_div ([#1664](https://github.com/leanprover-community/mathlib/pull/1664))
* feat(data/nat/basic): succ_div
Rather long proof, but it was the best I could do.
* Update basic.lean
* add the two lemmas for each case
* get rid of positivity assumption

### [2019-11-09 14:11:28](https://github.com/leanprover-community/mathlib/commit/1c24f92)
feat(data/list/basic): nth_le_append_right ([#1662](https://github.com/leanprover-community/mathlib/pull/1662))

### [2019-11-09 11:29:30](https://github.com/leanprover-community/mathlib/commit/b0c36df)
feat(measure_theory/integration) lemmas for calculating integral of simple functions ([#1659](https://github.com/leanprover-community/mathlib/pull/1659))
* lemmas for calculating integration on simple functions
* Updates
* `finsupp` changed to `fin_vol_supp`
* less conditions for `to_real_mul_to_real`
* `sum_lt_top` with more abstraction
* Fix extra arguments
* One tactic per line

### [2019-11-08 14:09:26+01:00](https://github.com/leanprover-community/mathlib/commit/ca21616)
chore(scripts): add linter and update nolints

### [2019-11-08 13:57:15+01:00](https://github.com/leanprover-community/mathlib/commit/8afcc5a)
feat(scripts): add nolints.txt

### [2019-11-08 11:03:46](https://github.com/leanprover-community/mathlib/commit/3223ba7)
doc(linear_algebra): rename lin_equiv to linear_equiv ([#1660](https://github.com/leanprover-community/mathlib/pull/1660))

### [2019-11-07 23:25:38](https://github.com/leanprover-community/mathlib/commit/362acb5)
feat(tactic/lint, script/mk_nolint): generate list of failing declarations to be ignored ([#1636](https://github.com/leanprover-community/mathlib/pull/1636))
* feat(tactic/lint): return names of failing declarations
* feat(scripts/mk_nolint): produce sorted list of declarations failing lint tests
* fix copyright
* fix test
* Update scripts/mk_nolint.lean

### [2019-11-07 03:43:41](https://github.com/leanprover-community/mathlib/commit/c718a22)
feat(extensionality): rename to `ext`; generate `ext` rules for structures ([#1645](https://github.com/leanprover-community/mathlib/pull/1645))
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

### [2019-11-06 22:22:23](https://github.com/leanprover-community/mathlib/commit/17a7f69)
doc(measure_theory/ae_eq_fun): add documentations and some lemmas ([#1650](https://github.com/leanprover-community/mathlib/pull/1650))
* Add documentations. `to_fun`.
* More precise comments

### [2019-11-06 07:01:00](https://github.com/leanprover-community/mathlib/commit/3c8bbdc)
chore(topology/subset_properties): simplify a proof ([#1652](https://github.com/leanprover-community/mathlib/pull/1652))

### [2019-11-05 23:56:57](https://github.com/leanprover-community/mathlib/commit/62815e3)
doc(tactic/core): docstrings on all definitions ([#1632](https://github.com/leanprover-community/mathlib/pull/1632))
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

### [2019-11-05 21:26:42](https://github.com/leanprover-community/mathlib/commit/d9578a6)
docs(tactic/lint) add code fence around #print statement to avoid its args looking like html tags. ([#1651](https://github.com/leanprover-community/mathlib/pull/1651))

### [2019-11-05 15:37:42](https://github.com/leanprover-community/mathlib/commit/986e58c)
refactor(sum_two_square): extract lemmas about primes in Z[i] ([#1643](https://github.com/leanprover-community/mathlib/pull/1643))
* refactor(sum_two_square): extract lemmas about primes in Z[i]
* forgot to save
* docztring
* module docstrings

### [2019-11-04 22:23:15](https://github.com/leanprover-community/mathlib/commit/f3f1fd8)
feat(floor): one more lemma ([#1646](https://github.com/leanprover-community/mathlib/pull/1646))
* feat(floor): one more lemma
and #lint fix
* Update src/algebra/floor.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-11-04 20:13:48](https://github.com/leanprover-community/mathlib/commit/2dcc6c2)
fix(tactic/tfae,scc): change the strongly connected component algorithm ([#1600](https://github.com/leanprover-community/mathlib/pull/1600))
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

### [2019-11-04 15:02:31](https://github.com/leanprover-community/mathlib/commit/ee5b38d)
feat(simps): allow the user to specify the projections ([#1630](https://github.com/leanprover-community/mathlib/pull/1630))
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

### [2019-11-03 15:40:43](https://github.com/leanprover-community/mathlib/commit/a6ace34)
feat(analysis/normed_space): Riesz's lemma ([#1642](https://github.com/leanprover-community/mathlib/pull/1642))
* fix(topology/metric_space/hausdorff_distance): fix typo
* feat(analysis/normed_space): Riesz's Lemma
* fix(analysis/normed_space): fix silly mistake in statement of riesz lemma
* style(analysis/normed_space/riesz_lemma): variable names & indent
* doc(analysis/normed_space/riesz_lemma): add attribution
* doc(analysis/normed_space/riesz_lemma): fix module docstring style
* style(analysis/normed_space/riesz_lemma): more style & documentation
- recall statement in module header comment
- typecast instead of unfold

### [2019-11-01 11:28:15](https://github.com/leanprover-community/mathlib/commit/9af7e5b)
refactor(linear_algebra/basic): use smul_right ([#1640](https://github.com/leanprover-community/mathlib/pull/1640))
* refactor(linear_algebra/basic): use smul_right
* Update src/linear_algebra/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/linear_algebra/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>

### [2019-11-01 03:25:06](https://github.com/leanprover-community/mathlib/commit/1710fd8)
feat(lint): add priority test for instances that always apply ([#1625](https://github.com/leanprover-community/mathlib/pull/1625))
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

### [2019-11-01 01:22:43](https://github.com/leanprover-community/mathlib/commit/5f17abc)
fix(tactic/elide): was untested and buggy. Fixed a few issues ([#1638](https://github.com/leanprover-community/mathlib/pull/1638))
* fix(tactic/elide): was untested and buggy. Fixed a few issues
* Update tactics.lean
* add copyright header
* Update src/tactic/elide.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>