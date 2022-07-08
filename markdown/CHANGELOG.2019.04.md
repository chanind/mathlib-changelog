### [2019-04-30 20:17:17](https://github.com/leanprover-community/mathlib/commit/c8a2aa9)
chore(category_theory): move small_category_of_preorder to preorder namespace ([#932](https://github.com/leanprover-community/mathlib/pull/932))

### [2019-04-30 18:22:31+02:00](https://github.com/leanprover-community/mathlib/commit/7c86814)
fix(scripts/remote-install-update-mathlib): try again [ci skip]
The previous attempt to install setuptools seems to fails for timing
reasons (PyGithub need setuptools after it's downloaded but before
it is installed, this is probably also a packaging issue in PyGithub).

### [2019-04-30 15:20:36](https://github.com/leanprover-community/mathlib/commit/a15fca5)
fix(scripts/remote-install-update-mathlib): missing dependency ([#964](https://github.com/leanprover-community/mathlib/pull/964))
Also add a `--upgrade` option to `pip install` in case something is
already there but outdated

### [2019-04-30 12:53:25+01:00](https://github.com/leanprover-community/mathlib/commit/8dcce05)
feat(analysis/normed_space): open mapping ([#900](https://github.com/leanprover-community/mathlib/pull/900))
* The Banach open mapping theorem
* improve comments
* feat(analysis/normed_space): rebase, fix build

### [2019-04-29 20:12:03](https://github.com/leanprover-community/mathlib/commit/00aaf05)
refactor(tactic/interactive): remove dependencies of ([#878](https://github.com/leanprover-community/mathlib/pull/878))
`tactic/interactive` on many theories

### [2019-04-29 12:46:38+02:00](https://github.com/leanprover-community/mathlib/commit/9b3e91b)
Update elan.md

### [2019-04-26 20:52:03](https://github.com/leanprover-community/mathlib/commit/53f9878)
refactor(analysis/normed_space): use bundled type for `fderiv` ([#956](https://github.com/leanprover-community/mathlib/pull/956))
* feat(analysis/normed_space): refactor fderiv to use bounded_linear_map
- uniqueness remains sorry'd
- more simp lemmas about bounded_linear_map
* refactor uniqueness proof
* fix(analysis/normed_space/operator_norm): rename `bound_le_op_norm` to `op_norm_le_bound`
- so that the inequality goes the correct way.

### [2019-04-26 22:27:05+02:00](https://github.com/leanprover-community/mathlib/commit/b49bf61)
fix(README): update maintainer list

### [2019-04-26 10:52:46+01:00](https://github.com/leanprover-community/mathlib/commit/0444f9c)
feat(data/equiv/basic): sum_compl_apply and others ([#961](https://github.com/leanprover-community/mathlib/pull/961))
* feat(data/equiv/basic): sum_congr_apply and others
* Update basic.lean

### [2019-04-25 18:58:02](https://github.com/leanprover-community/mathlib/commit/038f809)
refactor(analysis/normed_space/operator_norm): replace subspace with … ([#955](https://github.com/leanprover-community/mathlib/pull/955))
* refactor(analysis/normed_space/operator_norm): replace subspace with structure
* refactor(analysis/normed_space/operator_norm): add coercions

### [2019-04-23 20:15:47](https://github.com/leanprover-community/mathlib/commit/1d9ff68)
feat(function/embedding): ext and ext_iff ([#962](https://github.com/leanprover-community/mathlib/pull/962))

### [2019-04-23 07:22:05](https://github.com/leanprover-community/mathlib/commit/0d7b419)
fix(ring_theory/adjoin_root): move adjoin_root out of adjoin_root namespace ([#960](https://github.com/leanprover-community/mathlib/pull/960))

### [2019-04-22 23:48:35](https://github.com/leanprover-community/mathlib/commit/45456cf)
refactor(data/equiv/basic): simplify definition of equiv.set.range ([#959](https://github.com/leanprover-community/mathlib/pull/959))
* refactor(data/equiv/basic): simplify definition of equiv.set.range
* delete duplicate

### [2019-04-22 15:00:53](https://github.com/leanprover-community/mathlib/commit/63bbd1c)
feat(data/list/basic): index_of_inj ([#954](https://github.com/leanprover-community/mathlib/pull/954))
* feat(data/list/basic): index_of_inj
* make it an iff

### [2019-04-21 06:07:43-04:00](https://github.com/leanprover-community/mathlib/commit/3478f1f)
fix(tactic/interactive): allow `convert e using 0`

### [2019-04-20 18:42:45-04:00](https://github.com/leanprover-community/mathlib/commit/9daa1a5)
feat(tactic/clear_except): clear most of the assumptions in context ([#957](https://github.com/leanprover-community/mathlib/pull/957))

### [2019-04-20 20:07:03](https://github.com/leanprover-community/mathlib/commit/4b9d94d)
feat(data/[fin]set): add some more basic properties of (finite) sets ([#948](https://github.com/leanprover-community/mathlib/pull/948))
* feat(data/[fin]set): add some more basic properties of (finite) sets
* update after reviews
* fix error, move pairwise_disjoint to lattice as well
* fix error

### [2019-04-20 15:39:59+02:00](https://github.com/leanprover-community/mathlib/commit/7370cbf)
feat(tactic/linarith): treat expr atoms up to defeq ([#950](https://github.com/leanprover-community/mathlib/pull/950))

### [2019-04-20 09:47:15](https://github.com/leanprover-community/mathlib/commit/784a68c)
fix(topology/order): Missing Prop annotation ([#952](https://github.com/leanprover-community/mathlib/pull/952))

### [2019-04-20 00:49:21](https://github.com/leanprover-community/mathlib/commit/e4fc5af)
feat(tactic/ring): treat expr atoms up to defeq ([#949](https://github.com/leanprover-community/mathlib/pull/949))

### [2019-04-18 22:33:17-04:00](https://github.com/leanprover-community/mathlib/commit/c1aff1b)
style(tactic/omega): whitespace and minor tweaks
missed the PR review cycle

### [2019-04-18 20:15:55](https://github.com/leanprover-community/mathlib/commit/d0140dd)
feat(group_theory/subgroup): additive version of inj_iff_trivial_ker ([#947](https://github.com/leanprover-community/mathlib/pull/947))

### [2019-04-17 15:33:51](https://github.com/leanprover-community/mathlib/commit/032400b)
feat(analysis/normed_space): more facts about operator norm ([#927](https://github.com/leanprover-community/mathlib/pull/927))
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

### [2019-04-17 09:53:00-04:00](https://github.com/leanprover-community/mathlib/commit/8b23dad)
feat(scripts): use apt-get on ubuntu and support older Python versions ([#945](https://github.com/leanprover-community/mathlib/pull/945))

### [2019-04-17 11:03:45+02:00](https://github.com/leanprover-community/mathlib/commit/3f4b154)
feat(tactic/omega): tactic for linear integer & natural number arithmetic ([#827](https://github.com/leanprover-community/mathlib/pull/827))
* feat(tactic/omega): tactic for discharging linear integer and natural number arithmetic goals
* refactor(tactic/omega): clean up namespace and notations
* Update src/data/list/func.lean
Co-Authored-By: skbaek <seulkeebaek@gmail.com>
* Add changed files
* Refactor val_between_map_div
* Use default inhabitants for list.func

### [2019-04-16 21:38:18](https://github.com/leanprover-community/mathlib/commit/4b8106b)
fix(test/local_cache): make the trace text explicit and quiet ([#941](https://github.com/leanprover-community/mathlib/pull/941))
(by default)

### [2019-04-16 20:12:19](https://github.com/leanprover-community/mathlib/commit/7bbbee1)
feat(*): various additions to low-level files ([#904](https://github.com/leanprover-community/mathlib/pull/904))
* feat(*): various additions to low-level files
* fix(data/fin): add missing universe

### [2019-04-16 18:10:16](https://github.com/leanprover-community/mathlib/commit/2294876)
feat(data/finset): powerset_len (subsets of a given size) ([#899](https://github.com/leanprover-community/mathlib/pull/899))
* feat(data/finset): powerset_len (subsets of a given size)
* fix build

### [2019-04-16 16:32:52](https://github.com/leanprover-community/mathlib/commit/8985a43)
feat(data/set/intervals): some interval lemmas ([#942](https://github.com/leanprover-community/mathlib/pull/942))
* feat(data/set/intervals): a few more lemmas
* one-liners

### [2019-04-16 07:19:32](https://github.com/leanprover-community/mathlib/commit/361e216)
feature(category_theory/instances/Top/open[_nhds]): category of open sets, and open neighbourhoods of a point (merge [#920](https://github.com/leanprover-community/mathlib/pull/920) first) ([#922](https://github.com/leanprover-community/mathlib/pull/922))
* rearrange Top
* oops, import from the future
* the categories of open sets and of open_nhds
* missing import
* restoring opens, adding headers
* Update src/category_theory/instances/Top/open_nhds.lean
Co-Authored-By: semorrison <scott@tqft.net>
* use full_subcategory_inclusion

### [2019-04-15 19:41:40](https://github.com/leanprover-community/mathlib/commit/5f04e76)
feat(nat/basic): add some basic nat inequality lemmas ([#937](https://github.com/leanprover-community/mathlib/pull/937))
* feat(nat/basic): add some basic nat inequality lemmas, useful as specific cases of existing ring cases since uses less hypothesis
* feat(nat/basic): add some basic nat inequality lemmas, with convention fixes
* feat(nat/basic): add some basic nat inequality lemmas, with convention fixes

### [2019-04-15 19:09:47](https://github.com/leanprover-community/mathlib/commit/d06eb85)
feat(topology/algebra/continuous_functions): the ring of continuous functions ([#923](https://github.com/leanprover-community/mathlib/pull/923))
* feat(topology/algebra/continuous_functions): the ring of continuous functions
* filling in the hierarchy
* use to_additive

### [2019-04-14 19:26:36-04:00](https://github.com/leanprover-community/mathlib/commit/ca5d4c1)
feat(scripts): disable testing the install scripts in external PRs ([#936](https://github.com/leanprover-community/mathlib/pull/936))

### [2019-04-14 15:16:28+01:00](https://github.com/leanprover-community/mathlib/commit/a1b7dcd)
fix(algebra/big_operators): change variables in finset.prod_map to remove spurious [comm_monoid β] ([#934](https://github.com/leanprover-community/mathlib/pull/934))
The old version involved maps α → β → γ and an instance [comm_monoid γ], but there was also a section variable [comm_monoid β].  In applications of this lemma it is not necessary, and not usually true, that β is a monoid.  Change the statement to involve maps α → γ → β so that we already have a monoid structure on the last variable and we do not make spurious assumptions about the second one.

### [2019-04-13 21:56:41+02:00](https://github.com/leanprover-community/mathlib/commit/f01934c)
docs(elan): remove reference to nightly Lean ([#928](https://github.com/leanprover-community/mathlib/pull/928))
* docs(elan): Remove reference to nightly Lean.

### [2019-04-13 19:13:56+01:00](https://github.com/leanprover-community/mathlib/commit/49c3a04)
fix(algebra.field): introduce division_ring_has_div' ([#852](https://github.com/leanprover-community/mathlib/pull/852))
* fix division_ring_has_div
* priority default
* comment

### [2019-04-12 12:59:14+02:00](https://github.com/leanprover-community/mathlib/commit/3fe449e)
feat(algebra/free): free magma, semigroup, monoid ([#735](https://github.com/leanprover-community/mathlib/pull/735))

### [2019-04-11 19:08:59](https://github.com/leanprover-community/mathlib/commit/be79f25)
refactor(data/int/basic): weaken hypotheses for int.induction_on ([#887](https://github.com/leanprover-community/mathlib/pull/887))
* refactor(data/int/basic): weaken hypotheses for int.induction_on
* fix build
* fix build

### [2019-04-11 14:11:00](https://github.com/leanprover-community/mathlib/commit/36f0c22)
feat(submonoid, subgroup, subring): is_ring_hom instances for set.inclusion ([#917](https://github.com/leanprover-community/mathlib/pull/917))

### [2019-04-11 04:11:18-04:00](https://github.com/leanprover-community/mathlib/commit/c1e07a2)
fix(tactic/explode): more accurate may_be_proof ([#924](https://github.com/leanprover-community/mathlib/pull/924))

### [2019-04-11 00:50:17](https://github.com/leanprover-community/mathlib/commit/22fcb4e)
minor changes ([#921](https://github.com/leanprover-community/mathlib/pull/921))

### [2019-04-10 17:49:27](https://github.com/leanprover-community/mathlib/commit/f5d43a9)
feat(analysis/normed_space/deriv): show that the differential is unique (2) ([#916](https://github.com/leanprover-community/mathlib/pull/916))
* Remove wrong simp attribute
* fix typo
* characterize convergence at_top in normed spaces
* copy some changes from [#829](https://github.com/leanprover-community/mathlib/pull/829)
* small elements in normed fields go to zero
* derivatives are unique
* remove unnecessary lemma
* update according to review
* remove another empty line

### [2019-04-10 17:14:40](https://github.com/leanprover-community/mathlib/commit/41014e5)
rename has_sum and is_sum to summable and has_sum ([#912](https://github.com/leanprover-community/mathlib/pull/912))

### [2019-04-10 16:24:03+01:00](https://github.com/leanprover-community/mathlib/commit/c4b65da)
fix(mergify): merge if either push or pr build passes. ([#918](https://github.com/leanprover-community/mathlib/pull/918))
* fix(mergify): merge if either push or pr build passes.
* Update .mergify.yml
* Update .mergify.yml

### [2019-04-10 09:45:01+01:00](https://github.com/leanprover-community/mathlib/commit/49ccc9f)
refactor(order/lexicographic): use prod.lex and psigma.lex ([#914](https://github.com/leanprover-community/mathlib/pull/914))
* refactor(order/lexicographic): use prod.lex and psigma.lex
* update

### [2019-04-10 07:17:03](https://github.com/leanprover-community/mathlib/commit/8992472)
fix(category_theory): make the `nat_trans` arrow `⟹` a synonym for the `hom` arrow ([#907](https://github.com/leanprover-community/mathlib/pull/907))
* removing the nat_trans and vcomp notations; use \hom and \gg
* a simpler proposal
* getting rid of vcomp
* fix
* update notations in documentation
* typo in docs

### [2019-04-10 06:48:16](https://github.com/leanprover-community/mathlib/commit/f04535d)
feat(category_theory): iso_whisker_(left|right) ([#908](https://github.com/leanprover-community/mathlib/pull/908))
* feat(category_theory): iso_whisker_(left|right)
* oops, use old notation for now
* update after merge

### [2019-04-10 02:08:58](https://github.com/leanprover-community/mathlib/commit/86bd577)
refactor(algebra/group): is_monoid_hom extends is_mul_hom  ([#915](https://github.com/leanprover-community/mathlib/pull/915))
* refactor(algebra/group): is_monoid_hom extends is_mul_hom
* Fix build

### [2019-04-10 00:40:05](https://github.com/leanprover-community/mathlib/commit/f1683a9)
feat(data/set/basic): inclusion map ([#906](https://github.com/leanprover-community/mathlib/pull/906))
* feat(data/set/basic): inclusion map
* add continuous_inclusion
* minor style change

### [2019-04-10 00:12:57](https://github.com/leanprover-community/mathlib/commit/96d748e)
refactor(category_theory): rename `functor.on_iso` to `functor.map_iso` ([#893](https://github.com/leanprover-community/mathlib/pull/893))
* feat(category_theory): functor.map_nat_iso
* define `functor.map_nat_iso`, and relate to whiskering
* rename `functor.on_iso` to `functor.map_iso`
* add some missing lemmas about whiskering
* some more missing whiskering lemmas, while we're at it
* removing map_nat_iso

### [2019-04-09 22:44:04](https://github.com/leanprover-community/mathlib/commit/d692499)
reorganising category_theory/instances/rings.lean ([#909](https://github.com/leanprover-community/mathlib/pull/909))

### [2019-04-09 19:46:08](https://github.com/leanprover-community/mathlib/commit/4494001)
feat(field_theory/subfield): subfields are fields ([#888](https://github.com/leanprover-community/mathlib/pull/888))
* feat(field_theory/subfield): subfield are fields
* Update subfield.lean

### [2019-04-09 13:38:26-04:00](https://github.com/leanprover-community/mathlib/commit/5c4f5f2)
chore(build): allow PRs from separate repos to test deployment scripts

### [2019-04-09 10:16:41-04:00](https://github.com/leanprover-community/mathlib/commit/c2d79f8)
fix(mergify): require travis "push" check to push ([#913](https://github.com/leanprover-community/mathlib/pull/913))
This hopefully fixes an error where mergify does not merge a PR is the "pr" build succeeds before the "push" build. In these situations mergify does not merge, because the branch protection settings require both builds to pass.
Unfortunately, there doesn't seem to be an option to change the branch protection settings to only require the "pr" build to pass

### [2019-04-09 13:50:54+01:00](https://github.com/leanprover-community/mathlib/commit/66a86ff)
refactor(*): rename is_group_hom.mul to map_mul ([#911](https://github.com/leanprover-community/mathlib/pull/911))
* refactor(*): rename is_group_hom.mul to map_mul
* Fix splits_mul

### [2019-04-09 04:27:55](https://github.com/leanprover-community/mathlib/commit/eb024dc)
feat(order/lexicographic): lexicographic pre/partial/linear orders ([#820](https://github.com/leanprover-community/mathlib/pull/820))
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

### [2019-04-08 22:25:36+01:00](https://github.com/leanprover-community/mathlib/commit/29507a4)
feat(group_theory/subgroup): subtype.add_comm_group ([#903](https://github.com/leanprover-community/mathlib/pull/903))

### [2019-04-08 17:11:21](https://github.com/leanprover-community/mathlib/commit/ec51b6e)
feat(category_theory/colimits): missing simp lemmas ([#894](https://github.com/leanprover-community/mathlib/pull/894))

### [2019-04-08 17:49:51+02:00](https://github.com/leanprover-community/mathlib/commit/6d2cf4a)
fix(doc/extra/tactic_writing): rename mul_left ([#902](https://github.com/leanprover-community/mathlib/pull/902)) [ci skip]
*  fix(doc/extra/tactic_writing): rename mul_left
* one more fix

### [2019-04-08 12:50:22+02:00](https://github.com/leanprover-community/mathlib/commit/5f1329a)
feat(linear_algebra/dual): add dual vector spaces ([#881](https://github.com/leanprover-community/mathlib/pull/881))
* feat(linear_algebra/dual): add dual vector spaces
Define dual modules and vector spaces and prove the basic theorems: the dual basis isomorphism and
evaluation isomorphism in the finite dimensional case, and the corresponding (injectivity)
statements in the general case. A variant of `linear_map.ker_eq_bot` and the "inverse" of
`is_basis.repr_total` are included.
Universe issues make an adaptation of `linear_equiv.dim_eq` necessary.
* style(linear_algebra/dual): adapt to remarks from PR dsicussion
* style(linear_algebra/dual): reformat proof of `ker_eq_bot'`

### [2019-04-08 05:21:27](https://github.com/leanprover-community/mathlib/commit/10490ea)
feat(analysis/complex/polynomial): fundamental theorem of algebra ([#851](https://github.com/leanprover-community/mathlib/pull/851))
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

### [2019-04-07 23:05:06-04:00](https://github.com/leanprover-community/mathlib/commit/4fecb10)
feat(topology/gromov_hausdorff): the Gromov-Hausdorff space ([#883](https://github.com/leanprover-community/mathlib/pull/883))

### [2019-04-08 02:41:50](https://github.com/leanprover-community/mathlib/commit/5d81ab1)
trying to work out what was wrong with catching signals ([#898](https://github.com/leanprover-community/mathlib/pull/898))

### [2019-04-08 01:59:38](https://github.com/leanprover-community/mathlib/commit/0a49030)
fix(category_theory): turn `has_limits` classes into structures ([#896](https://github.com/leanprover-community/mathlib/pull/896))
* fix(category_theory): turn `has_limits` classes into structures
* fixing all the other pi-type typclasses
* oops

### [2019-04-07 19:36:21+02:00](https://github.com/leanprover-community/mathlib/commit/483a6c2)
feat(data/list/min_max): add minimum ([#892](https://github.com/leanprover-community/mathlib/pull/892))

### [2019-04-07 16:29:19](https://github.com/leanprover-community/mathlib/commit/891c050)
feat(subgroup, subring, subfield): directed Unions of subrings are subrings ([#889](https://github.com/leanprover-community/mathlib/pull/889))

### [2019-04-07 10:29:26+01:00](https://github.com/leanprover-community/mathlib/commit/bd524fc)
feat(field_theory/subfield): is_subfield instances ([#891](https://github.com/leanprover-community/mathlib/pull/891))

### [2019-04-07 01:34:16](https://github.com/leanprover-community/mathlib/commit/7e70ebd)
feat(data/nat/basic): b = c if b - a = c - a ([#862](https://github.com/leanprover-community/mathlib/pull/862))

### [2019-04-06 21:04:01-04:00](https://github.com/leanprover-community/mathlib/commit/3000f32)
fix(build): external PRs can't use GitHub credentials

### [2019-04-07 00:21:11+01:00](https://github.com/leanprover-community/mathlib/commit/e4d3ca3)
fix(analysis/normed_space/bounded_linear_maps): fix build ([#895](https://github.com/leanprover-community/mathlib/pull/895))

### [2019-04-06 16:44:31-04:00](https://github.com/leanprover-community/mathlib/commit/31ff5c5)
refactor(analysis/normed_space/bounded_linear_maps): nondiscrete normed field

### [2019-04-06 16:20:01-04:00](https://github.com/leanprover-community/mathlib/commit/53e7d72)
fix(appveyor): build every commit

### [2019-04-06 16:14:28-04:00](https://github.com/leanprover-community/mathlib/commit/ae8a1fb)
refactor(analysis/normed_space/bounded_linear_maps): nondiscrete normed field

### [2019-04-06 15:56:00-04:00](https://github.com/leanprover-community/mathlib/commit/8831e0a)
chore(mergify): require the AppVeyor build to succeed

### [2019-04-06 15:08:22-04:00](https://github.com/leanprover-community/mathlib/commit/8fa071f)
fix(scripts): not all files were deployed through the curl command ([#879](https://github.com/leanprover-community/mathlib/pull/879))

### [2019-04-06 18:45:57](https://github.com/leanprover-community/mathlib/commit/8d45ccb)
feat(category_theory/bifunctor): simp lemmas ([#867](https://github.com/leanprover-community/mathlib/pull/867))
* feat(category_theory/bifunctor): simp lemmas
* remove need for @, thanks Kenny and Chris!

### [2019-04-06 16:52:11](https://github.com/leanprover-community/mathlib/commit/3360f98)
more general hypotheses for integer induction ([#885](https://github.com/leanprover-community/mathlib/pull/885))

### [2019-04-06 10:59:07-04:00](https://github.com/leanprover-community/mathlib/commit/d8a2bc5)
feat(algebra/opposites): opposites of operators ([#538](https://github.com/leanprover-community/mathlib/pull/538))

### [2019-04-05 14:05:35-04:00](https://github.com/leanprover-community/mathlib/commit/e0e231d)
fix(build): match build names

### [2019-04-05 13:44:34-04:00](https://github.com/leanprover-community/mathlib/commit/d0f8607)
fix(scripts): protect `leanpkg test` against timeouts

### [2019-04-05 11:21:07-04:00](https://github.com/leanprover-community/mathlib/commit/e809df6)
fix(scripts): Mac Python's test support doesn't work on Travis

### [2019-04-05 11:07:11-04:00](https://github.com/leanprover-community/mathlib/commit/d9ec8a8)
fix(scripts): not all files were deployed through the curl command

### [2019-04-05 14:37:35](https://github.com/leanprover-community/mathlib/commit/78a08eb)
feat(data/mllist): monadic lazy lists ([#865](https://github.com/leanprover-community/mathlib/pull/865))
* feat(data/mllist): monadic lazy lists
* oops, fix header
* shove into tactic namespace
* make mllist into a monad ([#880](https://github.com/leanprover-community/mathlib/pull/880))
* make mllist into a monad
* looks good. add `take`, and some tests
* update authors
* cleanup test

### [2019-04-05 06:30:13](https://github.com/leanprover-community/mathlib/commit/44d1c7a)
feat(list.split_on): [1,1,2,3,2,4,4].split_on 2 = [[1,1],[3],[4,4]] ([#866](https://github.com/leanprover-community/mathlib/pull/866))

### [2019-04-05 06:11:40](https://github.com/leanprover-community/mathlib/commit/901bdbf)
feat(data/list/min_max): minimum and maximum over list ([#884](https://github.com/leanprover-community/mathlib/pull/884))
* feat(data/list/min_max): minimum and maximum over list
* Update min_max.lean
* replace semicolons

### [2019-04-05 04:01:15](https://github.com/leanprover-community/mathlib/commit/858d111)
feat(data/matrix): more basic matrix lemmas ([#873](https://github.com/leanprover-community/mathlib/pull/873))
* feat(data/matrix): more basic matrix lemmas
* feat(data/matrix): transpose_add

### [2019-04-05 03:14:12](https://github.com/leanprover-community/mathlib/commit/0b7ee1b)
feat(category_theory): introduce the core of a category ([#832](https://github.com/leanprover-community/mathlib/pull/832))

### [2019-04-04 20:42:02-04:00](https://github.com/leanprover-community/mathlib/commit/b6c2be4)
chore(mergify): delete head branch when merging

### [2019-04-04 23:27:46](https://github.com/leanprover-community/mathlib/commit/7aaccae)
feat(algebra/char_p,field_theory/finite_card): cardinality of finite fields ([#819](https://github.com/leanprover-community/mathlib/pull/819))
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

### [2019-04-04 16:28:11-04:00](https://github.com/leanprover-community/mathlib/commit/3abfda0)
chore(github/pr): enable code owners

### [2019-04-04 19:04:48](https://github.com/leanprover-community/mathlib/commit/8183a5a)
feat(data/list/perm): nil_subperm ([#882](https://github.com/leanprover-community/mathlib/pull/882))

### [2019-04-04 17:16:18](https://github.com/leanprover-community/mathlib/commit/384c9be)
feat (analysis/normed_space/basic.lean): implement reverse triangle inequality ([#831](https://github.com/leanprover-community/mathlib/pull/831))
* implement reverse triangle inequality
* make parameters explicit

### [2019-04-04 08:21:57-04:00](https://github.com/leanprover-community/mathlib/commit/07aa1e3)
fix(build): fix Lean version

### [2019-04-03 17:19:10-04:00](https://github.com/leanprover-community/mathlib/commit/1c69b60)
chore(mergify): fix config

### [2019-04-03 16:22:27-04:00](https://github.com/leanprover-community/mathlib/commit/7762bc4)
chore(mergify): fix config file

### [2019-04-03 16:06:06-04:00](https://github.com/leanprover-community/mathlib/commit/d4fd4b2)
chore(mergify): use team names instead of user names

### [2019-04-03 14:56:14-04:00](https://github.com/leanprover-community/mathlib/commit/2230934)
chore(mergify): disable `delete_head_branch`

### [2019-04-03 16:30:14+01:00](https://github.com/leanprover-community/mathlib/commit/840ddeb)
fix(README): fix mergify icon

### [2019-04-03 08:38:06-04:00](https://github.com/leanprover-community/mathlib/commit/542d179)
chore(github/pr): mergify configuration ([#871](https://github.com/leanprover-community/mathlib/pull/871))

### [2019-04-03 08:10:21-04:00](https://github.com/leanprover-community/mathlib/commit/a0cbe3b)
feat(data/fin): add `fin.clamp` ([#874](https://github.com/leanprover-community/mathlib/pull/874))

### [2019-04-03 05:37:35-04:00](https://github.com/leanprover-community/mathlib/commit/2c735dc)
feat(ring_theory/algebra_operations): submodules form a semiring ([#856](https://github.com/leanprover-community/mathlib/pull/856))

### [2019-04-03 05:35:05-04:00](https://github.com/leanprover-community/mathlib/commit/b9e9328)
feat(topology/metric_space/completion): completion of metric spaces ([#743](https://github.com/leanprover-community/mathlib/pull/743))

### [2019-04-03 09:38:15+02:00](https://github.com/leanprover-community/mathlib/commit/c3aba26)
feat(topology/uniform_space/pi): indexed products of uniform spaces ([#845](https://github.com/leanprover-community/mathlib/pull/845))
* feat(topology/uniform_space/pi): indexed products of uniform spaces
* fix(topology/uniform_space/pi): defeq topology
* fix(src/topology/uniform_space/pi): typo
Co-Authored-By: PatrickMassot <patrickmassot@free.fr>

### [2019-04-03 02:27:59-04:00](https://github.com/leanprover-community/mathlib/commit/7043a4a)
feat(algebra/pointwise): pointwise addition and multiplication of sets ([#854](https://github.com/leanprover-community/mathlib/pull/854))

### [2019-04-02 21:14:02-04:00](https://github.com/leanprover-community/mathlib/commit/f112076)
feat(tactic/basic): add `tactic.get_goal` ([#876](https://github.com/leanprover-community/mathlib/pull/876))

### [2019-04-02 20:45:14-04:00](https://github.com/leanprover-community/mathlib/commit/e96d6b7)
fix(int/basic): change order of instances to int.cast ([#877](https://github.com/leanprover-community/mathlib/pull/877))
As discussed at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Problem.20with.20type.20class.20search/near/161848744
Changing the order of arguments lets type class inference fail quickly for `int -> nat` coercions, rather than repeatedly looking for `has_neg` on `nat`.

### [2019-04-02 18:34:18-04:00](https://github.com/leanprover-community/mathlib/commit/ce92e8a)
chore(.travis.yml): use Lean to determine the Lean version ([#714](https://github.com/leanprover-community/mathlib/pull/714))

### [2019-04-02 18:33:34-04:00](https://github.com/leanprover-community/mathlib/commit/6c55989)
build(travis): interrupt the build at the first error message ([#708](https://github.com/leanprover-community/mathlib/pull/708))
Also make travis_long.sh print its progress messages to stderr.
This sidesteps a mysterious issue where piping the output of
travis_long.sh to another program caused that output to be lost
(probably buffered somewhere?) so Travis would kill the build
after 10 minutes.

### [2019-04-02 11:22:44-04:00](https://github.com/leanprover-community/mathlib/commit/13034ba)
feat(tactic/local_cache): add tactic-block-local caching mechanism ([#837](https://github.com/leanprover-community/mathlib/pull/837))

### [2019-04-02 10:44:43-04:00](https://github.com/leanprover-community/mathlib/commit/7eac178)
fix(scripts/update-mathlib): protect file operations from interrupts ([#864](https://github.com/leanprover-community/mathlib/pull/864))

### [2019-04-02 08:23:50-05:00](https://github.com/leanprover-community/mathlib/commit/f385ad6)
Inductive limit of metric spaces ([#732](https://github.com/leanprover-community/mathlib/pull/732))

### [2019-04-02 07:57:52-04:00](https://github.com/leanprover-community/mathlib/commit/727120c)
fix(build): improve compatibility of caching scripts with Sourcetree ([#863](https://github.com/leanprover-community/mathlib/pull/863))

### [2019-04-01 20:04:58-05:00](https://github.com/leanprover-community/mathlib/commit/5694d15)
feat(data/nat/basic): nat.le_rec_on ([#585](https://github.com/leanprover-community/mathlib/pull/585))

### [2019-04-01 18:55:36-04:00](https://github.com/leanprover-community/mathlib/commit/8e4542d)
Merge branch 'congr-2'

### [2019-04-01 18:52:21-04:00](https://github.com/leanprover-community/mathlib/commit/ec0a4ea)
fix(tactic/congr'): some `\iff` goals were erroneously rejected

### [2019-04-01 16:48:53-04:00](https://github.com/leanprover-community/mathlib/commit/5fe470b)
feat(tactic/push_neg): a tactic pushing negations ([#853](https://github.com/leanprover-community/mathlib/pull/853))

### [2019-04-01 16:21:09-04:00](https://github.com/leanprover-community/mathlib/commit/5995d46)
fix(build): prevent leanchecker from timing out

### [2019-04-01 16:13:58-04:00](https://github.com/leanprover-community/mathlib/commit/2f088fc)
feat(category_theory): working in Sort rather than Type ([#824](https://github.com/leanprover-community/mathlib/pull/824))

### [2019-04-01 22:07:28+02:00](https://github.com/leanprover-community/mathlib/commit/404e2c9)
add tutorial about zmod37 ([#767](https://github.com/leanprover-community/mathlib/pull/767))
Reference to a mathlib file which no longer exists has been fixed, and a more user-friendly example of an equivalence relation has been added in a tutorial.

### [2019-04-01 21:58:17+02:00](https://github.com/leanprover-community/mathlib/commit/867661e)
docs(tactics): add introduction to the instance cache tactic section

### [2019-04-01 21:55:31+02:00](https://github.com/leanprover-community/mathlib/commit/59e0593)
docs(tactics): minor rewrite of exactI, resetI etc
I always found these tactics confusing, but I finally figured out what they do and so I rewrote the docs so that I understand them better.

### [2019-04-01 15:08:22-04:00](https://github.com/leanprover-community/mathlib/commit/a1fe39b)
refactor(analysis/convex): make instance local ([#869](https://github.com/leanprover-community/mathlib/pull/869))

### [2019-04-01 14:48:06-04:00](https://github.com/leanprover-community/mathlib/commit/3bc0f00)
fix(scripts/cache-olean): only run the post-checkout hook if we actually changed branches ([#857](https://github.com/leanprover-community/mathlib/pull/857))

### [2019-04-01 03:01:21-04:00](https://github.com/leanprover-community/mathlib/commit/2851236)
feat(data/real/pi): Compute the first three digits of pi ([#822](https://github.com/leanprover-community/mathlib/pull/822))