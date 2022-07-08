### [2019-10-31 23:37:26](https://github.com/leanprover-community/mathlib/commit/df91623)
chore(category_theory/whiskering): clean up ([#1613](https://github.com/leanprover-community/mathlib/pull/1613))
* chore(category_theory/whiskering): clean up
* ugh, the stalks proofs are so fragile
* fixes
* minor
* fix
* fix

### [2019-10-31 21:03:05](https://github.com/leanprover-community/mathlib/commit/cd0bc32)
chore(data/set/finite): move defns up hierarchy; rename fintype_of_finset, card_fintype_of_finset ([#1615](https://github.com/leanprover-community/mathlib/pull/1615))
* chore(data/set/finite): move defns up hierarchy
* get namespaces right
* fixes
* fix build

### [2019-10-31 13:24:24](https://github.com/leanprover-community/mathlib/commit/6b51787)
feat(order/conditionally_complete_lattice): add complete_linear_order instance for enat ([#1633](https://github.com/leanprover-community/mathlib/pull/1633))

### [2019-10-31 11:20:33](https://github.com/leanprover-community/mathlib/commit/780cbc9)
feat(tactic/simps): allow let-expressions ([#1626](https://github.com/leanprover-community/mathlib/pull/1626))
* feat(simps); allow let-expressions
* Update src/meta/expr.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

### [2019-10-30 20:31:06](https://github.com/leanprover-community/mathlib/commit/d43f7f9)
feat(.travis.yml): add linting to test stage ([#1606](https://github.com/leanprover-community/mathlib/pull/1606))

### [2019-10-30 17:35:02](https://github.com/leanprover-community/mathlib/commit/aadfde6)
feat(data/fintype): fintype.card_subtype_lt ([#1635](https://github.com/leanprover-community/mathlib/pull/1635))
* feat(data/fintype): fintype.card_subtype_lt
* Update src/data/fintype.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

### [2019-10-29 22:34:46](https://github.com/leanprover-community/mathlib/commit/ca90081)
feat(number_theory/sum_four_squares): every natural number is the sum of four square numbers ([#1560](https://github.com/leanprover-community/mathlib/pull/1560))
* feat(number_theory/sum_four_squares): every natural number is the sum of four square numbers
* Johan's suggestions
* some better parity proofs
* fix silly lemmas in finite_fields
* generalize a lemma
* fix build
* Update src/number_theory/sum_four_squares.lean
* add docs in correct style

### [2019-10-29 09:22:53](https://github.com/leanprover-community/mathlib/commit/6030ff0)
chore(category_theory): speed-up monoidal.of_has_finite_products ([#1616](https://github.com/leanprover-community/mathlib/pull/1616))

### [2019-10-29 07:16:16](https://github.com/leanprover-community/mathlib/commit/e6e25d0)
cleanup(order|string) ([#1629](https://github.com/leanprover-community/mathlib/pull/1629))
move data.string to data.string.basic
remove classical.decidable_linear_order. was duplicate of classical.DLO

### [2019-10-29 05:05:10](https://github.com/leanprover-community/mathlib/commit/b9e3dbb)
feat(rat): give Q-algebra structure on field ([#1628](https://github.com/leanprover-community/mathlib/pull/1628))
also move around some declarations in rat.cast
the only new declaration in that file is is_ring_hom_cast

### [2019-10-29 03:03:51](https://github.com/leanprover-community/mathlib/commit/b5b674c)
fix(*): use has_coe_t ([#1627](https://github.com/leanprover-community/mathlib/pull/1627))

### [2019-10-29 00:42:49](https://github.com/leanprover-community/mathlib/commit/0ea3dfe)
feat(tactic/rcases): transport the `cases h : e` syntax to `rcases` ([#1611](https://github.com/leanprover-community/mathlib/pull/1611))
* Update rcases.lean
* Update rcases.lean
* Update rcases.lean
* Update lift.lean
* Update rcases.lean
* Update tactics.md
* Update rcases.lean

### [2019-10-28 21:23:53](https://github.com/leanprover-community/mathlib/commit/7a8f53e)
feat(tactic/lint): silent linting ([#1580](https://github.com/leanprover-community/mathlib/pull/1580))
* feat(tactic/lint): silent linting
* doc(tactic/lint): doc silent linting and nolint features
* fix test
* change notation for silent linting
* style(tactic/lint): remove commented lines

### [2019-10-28 16:28:58](https://github.com/leanprover-community/mathlib/commit/94e368c)
chore(ring_theory/algebra): add docstring to algebra.comap and remove unused instances ([#1624](https://github.com/leanprover-community/mathlib/pull/1624))
* doc(ring_theory/algebra): add docstring to algebra.comap
* Update algebra.lean

### [2019-10-28 10:34:50](https://github.com/leanprover-community/mathlib/commit/c2e81dd)
fix(tactic/omega): fix omega bugs, add docstring (closes [#1484](https://github.com/leanprover-community/mathlib/pull/1484)) ([#1620](https://github.com/leanprover-community/mathlib/pull/1620))
* Fix omega bugs, add docstring
* style(tactic/omega/main): trivial cleaning

### [2019-10-27 17:05:13](https://github.com/leanprover-community/mathlib/commit/1fa03c2)
feat(linear_algebra/basic): define algebra structure on endomorphisms of module ([#1618](https://github.com/leanprover-community/mathlib/pull/1618))
* feat(linear_algebra/basic): define algebra structure on endomorphisms of module
* Update algebra.lean

### [2019-10-27 07:06:37](https://github.com/leanprover-community/mathlib/commit/89ece14)
fix(data/mv_polynomial): generalize equivs to comm_semiring ([#1621](https://github.com/leanprover-community/mathlib/pull/1621))
This apparently makes the elaborator's job a lot easier, and
reduces the compile time of the whole module by a factor of 3.

### [2019-10-27 02:35:54](https://github.com/leanprover-community/mathlib/commit/8a45d98)
chore(category_theory): remove superfluous lemma ([#1614](https://github.com/leanprover-community/mathlib/pull/1614))

### [2019-10-26 12:58:23](https://github.com/leanprover-community/mathlib/commit/8eaf478)
feat(linear_algebra/basis): Dedekind's linear independence of characters ([#1595](https://github.com/leanprover-community/mathlib/pull/1595))
* feat(linear_algebra/basis): Dedekind's linear independence of characters
* feat(linear_algebra/basis): generalize independence of characters to integral domains
* chore(linear_algebra/basis): change proofs
* commenting the proof

### [2019-10-26 10:17:39](https://github.com/leanprover-community/mathlib/commit/b9798dc)
feat(data/nat): a lemma about min_fac ([#1603](https://github.com/leanprover-community/mathlib/pull/1603))
* feat(data/nat): a lemma about min_fac
* feat(data/nat): a lemma about min_fac
* use Rob's proof
* fix
* let's play golf
* newline
* use Chris' proof
* cleaning up
* rename per Chris' suggestions

### [2019-10-26 08:23:59](https://github.com/leanprover-community/mathlib/commit/b46f5b0)
feat(data/set/intervals): fintype instances for ℕ and ℤ ([#1602](https://github.com/leanprover-community/mathlib/pull/1602))
* starting on fintype instances for Icos
* finishing fintypes
* minor
* move file
* oops
* redone
* formatting
* cleaning up

### [2019-10-25 15:46:12](https://github.com/leanprover-community/mathlib/commit/6ee8bf9)
refactor(data/rat/meta): rename to meta_defs ([#1612](https://github.com/leanprover-community/mathlib/pull/1612))
* refactor(data/rat/meta): rename to meta_defs
* fix build

### [2019-10-24 21:13:25](https://github.com/leanprover-community/mathlib/commit/9db43a5)
chore(data/nat/basic): remove pos_iff_ne_zero' ([#1610](https://github.com/leanprover-community/mathlib/pull/1610))
This used to be different from pos_iff_ne_zero because the latter
was phrased in terms of `n > 0`, not `0 < n`. Since [#1436](https://github.com/leanprover-community/mathlib/pull/1436) they
are the same.

### [2019-10-24 17:11:21](https://github.com/leanprover-community/mathlib/commit/151bcbe)
feat(meta/expr,data/rat/basic): add rat.reflect ([#1565](https://github.com/leanprover-community/mathlib/pull/1565))
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

### [2019-10-24 15:08:35](https://github.com/leanprover-community/mathlib/commit/3f8a492)
chore(category_theory): replace some @[simp] with @[simps] ([#1605](https://github.com/leanprover-community/mathlib/pull/1605))

### [2019-10-24 13:48:11](https://github.com/leanprover-community/mathlib/commit/b1f44ba)
chore(group_theory/free_group,order/zorn): rename zorn.zorn and sum.sum ([#1604](https://github.com/leanprover-community/mathlib/pull/1604))
* chore(order/zorn): rename zorn.zorn
* chore(group_theory/free_group): rename sum.sum
* chore(group_theory/free_group,order/zorn): remove nolint

### [2019-10-24 11:26:19](https://github.com/leanprover-community/mathlib/commit/5da754c)
fix(tactic/solve_by_elim): parameter parsing ([#1591](https://github.com/leanprover-community/mathlib/pull/1591))
* fix(tactic/solve_by_elim): parameter parsing
* revert accidental commenting out
* doc comments for solve_by_elim
* fix build

### [2019-10-24 06:28:15](https://github.com/leanprover-community/mathlib/commit/4b9cdf4)
chore(*): pass dup_namespace and def_lemma lint tests ([#1599](https://github.com/leanprover-community/mathlib/pull/1599))
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

### [2019-10-24 02:49:46](https://github.com/leanprover-community/mathlib/commit/31c73c1)
feat(data/multiset): map_eq_map_of_bij_of_nodup ([#1590](https://github.com/leanprover-community/mathlib/pull/1590))

### [2019-10-24 00:47:18](https://github.com/leanprover-community/mathlib/commit/08977be)
feat(algebra/semiconj): define `semiconj_by` and some operations ([#1576](https://github.com/leanprover-community/mathlib/pull/1576))
* feat(algebra/semiconj): define `semiconj_by` and some operations
Also rewrite `algebra/commute` to reuse results from `algebra/semiconj`.
* Some `@[simp]` attributes
* Fixes by @rwbarton, more docs
* Add two more constructors

### [2019-10-23 23:11:12](https://github.com/leanprover-community/mathlib/commit/e2a8e63)
feat(geometry/manifold): improvements for smooth manifolds ([#1593](https://github.com/leanprover-community/mathlib/pull/1593))
* feat(geometry/manifold): improvements to smooth manifolds
* fix
* better definition for half-space
* fix docstring
* address comments
* more comments

### [2019-10-23 20:48:14](https://github.com/leanprover-community/mathlib/commit/b433afa)
feat(algebra/big_operators): sum_ite ([#1598](https://github.com/leanprover-community/mathlib/pull/1598))
* feat(algebra/big_operators): sum_ite
rename the current `sum_ite` to `sum_ite_eq` and add a more general version
* Update src/algebra/big_operators.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-10-23 20:28:52](https://github.com/leanprover-community/mathlib/commit/36dfcfc)
doc(topology/topological_fiber_bundle): documentation improvements ([#1594](https://github.com/leanprover-community/mathlib/pull/1594))
* feat(topology/topological_fiber_bundle): improvements
* minor fixes

### [2019-10-23 17:05:43](https://github.com/leanprover-community/mathlib/commit/d214c61)
feat(data/nat/modeq): div_mod_eq_mod_mul_div ([#1597](https://github.com/leanprover-community/mathlib/pull/1597))

### [2019-10-23 14:43:45](https://github.com/leanprover-community/mathlib/commit/36f7113)
fix(suggest): focus1 at the correct moment ([#1592](https://github.com/leanprover-community/mathlib/pull/1592))

### [2019-10-23 12:50:43](https://github.com/leanprover-community/mathlib/commit/24dd80b)
chore(src/data/mv_polynomial): doc comments and removing unused arguments ([#1585](https://github.com/leanprover-community/mathlib/pull/1585))
* chore(src/data/mv_polynomial): doc comments and removing unused arguments
* Update src/data/mv_polynomial.lean

### [2019-10-23 10:48:29](https://github.com/leanprover-community/mathlib/commit/079e6ec)
feat(analysis/normed_space): norms on ℤ and ℚ ([#1570](https://github.com/leanprover-community/mathlib/pull/1570))
* feat(analysis/normed_space): norms on ℤ and ℚ
* Add some `elim_cast` lemmas
* Add `@[simp]`, thanks @robertylewis
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

### [2019-10-23 07:50:35](https://github.com/leanprover-community/mathlib/commit/ee5518c)
fix(category_theory/adjunctions): fix deterministic timeouts ([#1586](https://github.com/leanprover-community/mathlib/pull/1586))

### [2019-10-23 00:26:28](https://github.com/leanprover-community/mathlib/commit/5722ee8)
refactor(data/finset): restate disjoint_filter ([#1583](https://github.com/leanprover-community/mathlib/pull/1583))
* refactor(data/finset): restate disjoint_filter
* fix build
* fix build

### [2019-10-22 16:25:55](https://github.com/leanprover-community/mathlib/commit/31906d8)
chore(algebra/category/CommRing/limits): fix typo, remove private ([#1584](https://github.com/leanprover-community/mathlib/pull/1584))
* chore(algebra/category/CommRing/limits): fix typo, remove private
* Update src/algebra/category/CommRing/limits.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebra/category/CommRing/limits.lean
* Update src/algebra/category/CommRing/limits.lean
* bleh
* Update src/algebra/category/CommRing/limits.lean

### [2019-10-22 14:30:51](https://github.com/leanprover-community/mathlib/commit/e8bdb05)
feat(algebra/group): conversion between `→*` and `→+` ([#1569](https://github.com/leanprover-community/mathlib/pull/1569))
* feat(algebra/group): conversion between `→*` and `→+`
* docs
* Rename to allow use of projection notation

### [2019-10-22 12:22:04](https://github.com/leanprover-community/mathlib/commit/93b1786)
feat(archive): add proof of sensitivity conjecture ([#1553](https://github.com/leanprover-community/mathlib/pull/1553))
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

### [2019-10-22 08:36:07](https://github.com/leanprover-community/mathlib/commit/1b4d1ea)
chore(algebra/category/*/colimits): remove unnecessary projections ([#1588](https://github.com/leanprover-community/mathlib/pull/1588))
* refactor(category_theory,algebra/category): make algebraic categories not [reducible]
Adapted from part of [#1438](https://github.com/leanprover-community/mathlib/pull/1438).
* Update src/algebra/category/CommRing/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* adding missing forget2 instances
* Converting Reid's comment to a [Note]
* adding examples testing coercions
* chore(algebra/category/*/colimits): remove unnecessary projections

### [2019-10-22 06:42:16](https://github.com/leanprover-community/mathlib/commit/2b98d47)
feat(category_theory): add `reassoc` annotations ([#1558](https://github.com/leanprover-community/mathlib/pull/1558))
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

### [2019-10-22 04:37:39](https://github.com/leanprover-community/mathlib/commit/1741a1d)
feat(data/nat/basic): division inequalities ([#1579](https://github.com/leanprover-community/mathlib/pull/1579))
* feat(data/nat/basic): division inequalities
* whitespace
* fix
* shorten proof

### [2019-10-22 02:29:49](https://github.com/leanprover-community/mathlib/commit/c9ba7a5)
refactor(category_theory,algebra/category): make algebraic categories not [reducible] ([#1491](https://github.com/leanprover-community/mathlib/pull/1491))
* refactor(category_theory,algebra/category): make algebraic categories not [reducible]
Adapted from part of [#1438](https://github.com/leanprover-community/mathlib/pull/1438).
* Update src/algebra/category/CommRing/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* adding missing forget2 instances
* Converting Reid's comment to a [Note]
* adding examples testing coercions

### [2019-10-22 00:57:19](https://github.com/leanprover-community/mathlib/commit/340178d)
feat(data/finset): inj_on_of_surj_on_of_card_le ([#1578](https://github.com/leanprover-community/mathlib/pull/1578))
* feat(data/finset): inj_on_of_surj_on_of_card_le
* Type ascriptions
* function namespace

### [2019-10-21 22:57:07](https://github.com/leanprover-community/mathlib/commit/39092ab)
feat(*): various lemmas from the sensitivity project ([#1550](https://github.com/leanprover-community/mathlib/pull/1550))
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

### [2019-10-21 20:49:04+02:00](https://github.com/leanprover-community/mathlib/commit/96ebf8c)
docs(README): Remove Patrick from the maintainer list.

### [2019-10-21 15:12:24](https://github.com/leanprover-community/mathlib/commit/6cf3d04)
fix(algebra/group/hom): Fix spurrious arguments ([#1581](https://github.com/leanprover-community/mathlib/pull/1581))
This bug was introduced in eb230d3b48f4da49b

### [2019-10-21 14:34:56](https://github.com/leanprover-community/mathlib/commit/f19dbf2)
feat(geometric/manifold): smooth manifolds ([#1555](https://github.com/leanprover-community/mathlib/pull/1555))
* smooth manifolds
* fix docstrings
* update docstring
* remove out_param

### [2019-10-21 12:39:30](https://github.com/leanprover-community/mathlib/commit/f52e952)
feat(data/finset): define `finset.Ico.subset_iff` ([#1574](https://github.com/leanprover-community/mathlib/pull/1574))

### [2019-10-21 10:18:48](https://github.com/leanprover-community/mathlib/commit/a4bbbde)
feat(topology/topological_fiber_bundle): topological fiber bundles ([#1421](https://github.com/leanprover-community/mathlib/pull/1421))
* feat(topology/topological_fiber_bundle): topological fiber bundles
* better definition of fiber bundles

### [2019-10-21 08:23:05](https://github.com/leanprover-community/mathlib/commit/d2d29ff)
feat(algebra/geom_sum): sum of a geom_series over an Ico ([#1573](https://github.com/leanprover-community/mathlib/pull/1573))
* feat(algebra/geom_sum): sum of a geom_series over an Ico
* Add two more versions as requested by @jcommelin

### [2019-10-21 08:06:20](https://github.com/leanprover-community/mathlib/commit/0b660a9)
fix(scripts): sanity_check -> lint [ci skip] ([#1575](https://github.com/leanprover-community/mathlib/pull/1575))
* fix(scripts): sanity_check -> lint [ci skip]
* also fix in .gitignore

### [2019-10-21 12:08:57+11:00](https://github.com/leanprover-community/mathlib/commit/809276c)
feat(topology/metric_space): polygonal version of the triangle inequality ([#1572](https://github.com/leanprover-community/mathlib/pull/1572))
* feat(topology/metric_space): "polygon" version of the triangle inequality
* Add two more versions of the "polygonal" inequality
* Use `dist_le_Ico_sum_dist` in `cauchy_seq_of_summable_dist`

### [2019-10-20 15:33:20](https://github.com/leanprover-community/mathlib/commit/b1654df)
feat(meta/rb_map,tactic/monotonicity): replace rb_map.insert_cons ([#1571](https://github.com/leanprover-community/mathlib/pull/1571))
rb_map key (list value) is the same as rb_lmap. Usages of this function
should be replaced with rb_lmap.insert

### [2019-10-20 10:46:47](https://github.com/leanprover-community/mathlib/commit/74bed0c)
feat(tactic/suggest): generalize and reimplement library_search ([#1552](https://github.com/leanprover-community/mathlib/pull/1552))
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

### [2019-10-19 22:11:22](https://github.com/leanprover-community/mathlib/commit/f544632)
feat(algebra/big_operators): products and sums over `finset.Ico` ([#1567](https://github.com/leanprover-community/mathlib/pull/1567))

### [2019-10-19 19:57:42](https://github.com/leanprover-community/mathlib/commit/173e70a)
feat(tactic/lint): rename and refactor sanity_check ([#1556](https://github.com/leanprover-community/mathlib/pull/1556))
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

### [2019-10-19 19:04:46](https://github.com/leanprover-community/mathlib/commit/ee398b6)
feat(algebra/floor): prove `⌈x⌉ ≤ ⌊x⌋ + 1` ([#1568](https://github.com/leanprover-community/mathlib/pull/1568))

### [2019-10-18 19:41:32](https://github.com/leanprover-community/mathlib/commit/05102ec)
chore(category_theory): using simps ([#1500](https://github.com/leanprover-community/mathlib/pull/1500))
* chore(category_theory): using simps
* more simps
* remove simp lemma
* revertings overlapping @[simps]

### [2019-10-18 03:27:47](https://github.com/leanprover-community/mathlib/commit/a1c0ad5)
feat(category_theory): def `is_isomorphic_setoid`, `groupoid.iso_equiv_hom` ([#1506](https://github.com/leanprover-community/mathlib/pull/1506))
* feat(category_theory): def `is_isomorphic_setoid`, `groupoid.iso_equiv_hom`
* Move to a dedicated file, define `isomorphic_class_functor`
* explicit/implicit arguments
* Update src/category_theory/groupoid.lean
* Update src/category_theory/groupoid.lean
* Update src/category_theory/isomorphism_classes.lean
* Update src/category_theory/isomorphism_classes.lean
* Update src/category_theory/isomorphism_classes.lean

### [2019-10-17 20:03:17](https://github.com/leanprover-community/mathlib/commit/e5fc2a7)
refactor(topology,calculus): change subset condition for composition ([#1549](https://github.com/leanprover-community/mathlib/pull/1549))
* refactor(topology,calculus): change subset condition for composition
* improve docstrings
* add is_open Ioi
* reviewer's comments
* typo

### [2019-10-17 21:46:14+02:00](https://github.com/leanprover-community/mathlib/commit/cc19e30)
docs(project): change example project [ci skip]

### [2019-10-17 07:58:42](https://github.com/leanprover-community/mathlib/commit/905beb0)
fix(topology/metric_space): fix uniform structure on Pi types ([#1551](https://github.com/leanprover-community/mathlib/pull/1551))
* fix(topology/metric_space): fix uniform structure on pi tpype
* cleanup
* better construction of metric from emetric
* use simp only instead of simp

### [2019-10-16 21:40:58](https://github.com/leanprover-community/mathlib/commit/ee863ec)
feat(ring_theory/algebraic): algebraic extensions, algebraic elements ([#1519](https://github.com/leanprover-community/mathlib/pull/1519))
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

### [2019-10-16 18:45:00](https://github.com/leanprover-community/mathlib/commit/cbf81df)
archive(imo1988_q6): a formalization of Q6 on IMO1988 ([#1455](https://github.com/leanprover-community/mathlib/pull/1455))
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

### [2019-10-16 17:05:22](https://github.com/leanprover-community/mathlib/commit/ad8387c)
feat(field_theory/finite): cardinality of images of polynomials ([#1554](https://github.com/leanprover-community/mathlib/pull/1554))
* feat(field_theory/finite): cardinality of images of polynomials
* docstrings
* Johan's suggestions
* slightly shorten proof

### [2019-10-16 03:46:48](https://github.com/leanprover-community/mathlib/commit/09fd631)
feat(data/zmod/basic): val_min_abs ([#1548](https://github.com/leanprover-community/mathlib/pull/1548))
* feat(data/zmod/basic): val_min_abs
* Update basic.lean
* docstring and fix `zmodp` versions

### [2019-10-14 12:13:21](https://github.com/leanprover-community/mathlib/commit/c3d1bd7)
feat(data/polynomial): card_roots' ([#1546](https://github.com/leanprover-community/mathlib/pull/1546))

### [2019-10-13 12:52:09](https://github.com/leanprover-community/mathlib/commit/0ee1272)
fix(doc/contribute): fix broken link ([#1547](https://github.com/leanprover-community/mathlib/pull/1547))

### [2019-10-13 09:57:58](https://github.com/leanprover-community/mathlib/commit/d716648)
docs(topology): some more module docstrings ([#1544](https://github.com/leanprover-community/mathlib/pull/1544))

### [2019-10-13 08:08:28](https://github.com/leanprover-community/mathlib/commit/d10fd1e)
feat(data/int/basic): int.nat_abs_eq_zero ([#1545](https://github.com/leanprover-community/mathlib/pull/1545))
* feat(data/int/basic): int.nat_abs_eq_zero
* Update basic.lean
* Update basic.lean

### [2019-10-12 20:07:23](https://github.com/leanprover-community/mathlib/commit/646c035)
refactor(topology): mild reorganization ([#1541](https://github.com/leanprover-community/mathlib/pull/1541))
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

### [2019-10-12 18:21:51](https://github.com/leanprover-community/mathlib/commit/92a9a78)
fix(topology/continuous_on): avoid duplicate instance arguments ([#1542](https://github.com/leanprover-community/mathlib/pull/1542))
This was broken by [#1516](https://github.com/leanprover-community/mathlib/pull/1516), caught by sanity_check.

### [2019-10-12 18:05:26](https://github.com/leanprover-community/mathlib/commit/995add3)
fix(topology/algebra/group_completion): remove redundant instance parameters ([#1543](https://github.com/leanprover-community/mathlib/pull/1543))

### [2019-10-12 16:02:53+02:00](https://github.com/leanprover-community/mathlib/commit/76090be)
chore(docs/install/debian): Remove old sentence [ci skip]

### [2019-10-12 10:28:08](https://github.com/leanprover-community/mathlib/commit/2751561)
minor updates to the installation instructions ([#1538](https://github.com/leanprover-community/mathlib/pull/1538))

### [2019-10-11 17:54:17](https://github.com/leanprover-community/mathlib/commit/d5de803)
refactor(ring_theory/algebra): alg_hom extends ring_hom and use curly brackets ([#1529](https://github.com/leanprover-community/mathlib/pull/1529))
* chore(algebra/ring): use curly brackets for ring_hom where possible
* refactor(ring_theory/algebra): alg_hom extends ring_hom and use curly brackets
* fix build
* Update src/ring_theory/algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* fix build

### [2019-10-11 13:15:04](https://github.com/leanprover-community/mathlib/commit/6b7377a)
chore(algebra/ring): use curly brackets for ring_hom where possible ([#1525](https://github.com/leanprover-community/mathlib/pull/1525))
* chore(algebra/ring): use curly brackets for ring_hom where possible
* add comments explaining motivation
* move explanation to header
* fix build
* Update src/algebra/ring.lean
* scott's suggestion

### [2019-10-11 11:48:51](https://github.com/leanprover-community/mathlib/commit/38a0ffe)
refactor(ring_theory/algebra): algebra should extend has_scalar not module ([#1532](https://github.com/leanprover-community/mathlib/pull/1532))
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

### [2019-10-11 11:26:29](https://github.com/leanprover-community/mathlib/commit/338146b)
fix(algebra/char_p): typo in docstring ([#1537](https://github.com/leanprover-community/mathlib/pull/1537))
I don't know anything about semirings but I do know there isn't a homomorphism from int to them in general. Do people talk about kernels? (this would be some semi-ideal or something). My change is probably better than what we had but someone who knows what a semiring is might want to check that my suggestion makes sense.

### [2019-10-11 03:41:02](https://github.com/leanprover-community/mathlib/commit/eb230d3)
chore(algebra/group/hom): use curly brackets for instances where possible ([#1524](https://github.com/leanprover-community/mathlib/pull/1524))
* chore(algebra/group/hom): use curly brackets for instances where possible
* add comments mentioning motivation behind brackets
* move explanation to header
* fix build
* Update src/algebra/group/hom.lean

### [2019-10-11 01:59:31](https://github.com/leanprover-community/mathlib/commit/364c26e)
chore(algebra/module): use curly brackets instead of square brackets in more places ([#1523](https://github.com/leanprover-community/mathlib/pull/1523))
* chore(algebra/module): use curly brackets instead of square brackets in more places
* Add explanation behind implicit brackets
* Update src/algebra/module.lean

### [2019-10-10 11:14:36](https://github.com/leanprover-community/mathlib/commit/43d3dee)
chore(linear_algebra): rename type variables ([#1521](https://github.com/leanprover-community/mathlib/pull/1521))
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

### [2019-10-10 09:00:38](https://github.com/leanprover-community/mathlib/commit/dc788a0)
feat(topology/sequences): every first-countable space is sequential ([#1528](https://github.com/leanprover-community/mathlib/pull/1528))
* feat(topology/sequences): every first-countable space is sequential
* fixup style
* fixup comments
* remove redundant type ascription

### [2019-10-09 19:53:01](https://github.com/leanprover-community/mathlib/commit/7d792ec)
chore(ring_theory/adjoin_root): remove some unused decidable_eq ([#1530](https://github.com/leanprover-community/mathlib/pull/1530))

### [2019-10-09 16:00:50](https://github.com/leanprover-community/mathlib/commit/a17a9a6)
fix(tactic/{use,ring}): instantiate metavariables in goal ([#1520](https://github.com/leanprover-community/mathlib/pull/1520))
`use` now tidies up the subgoals that it leaves behind after instantiating constructors.
`ring` is sensitive to the presence of such metavariables, and we can't guarantee that it doesn't see any,
so it should check for them before it runs.

### [2019-10-09 14:59:54](https://github.com/leanprover-community/mathlib/commit/45633aa)
refactor(topology/algebra/polynomial): move topology.instances.polynomial ([#1527](https://github.com/leanprover-community/mathlib/pull/1527))

### [2019-10-09 14:24:19](https://github.com/leanprover-community/mathlib/commit/0ea83c0)
docs(data/holor): some additional documentation ([#1526](https://github.com/leanprover-community/mathlib/pull/1526))

### [2019-10-09 05:24:44](https://github.com/leanprover-community/mathlib/commit/6ccfe5a)
feat(algebra/ordered...): Two tiny lemmas ([#1522](https://github.com/leanprover-community/mathlib/pull/1522))
* feat(algebra/ordered...): Two tiny lemmas
* style(src/algebra/ordered_field)
Co-Authored-By: Reid Barton <rwbarton@gmail.com>

### [2019-10-08 16:33:02](https://github.com/leanprover-community/mathlib/commit/7c56051)
doc(linear_algebra/basis): add doc ([#1503](https://github.com/leanprover-community/mathlib/pull/1503))
* doc(linear_algebra/basis): add doc
* doc(linear_algebra/basis): shorten docstrings

### [2019-10-08 15:54:18](https://github.com/leanprover-community/mathlib/commit/6b15eb2)
chore(analysis): put lemmas in normed_field namespace ([#1517](https://github.com/leanprover-community/mathlib/pull/1517))
The motivation is to be able to state, say norm_mul for subrings of a
normed field, typically p-adic integers. That way we can have
padic_int.norm_mul, open the padic_int namespace and have no ambiguous
name.

### [2019-10-08 13:51:59](https://github.com/leanprover-community/mathlib/commit/afda1a2)
refactor(topology/continuous_on): move continuous_{on,within_at} to own file ([#1516](https://github.com/leanprover-community/mathlib/pull/1516))
* refactor(topology/continuous_on): move continuous_{on,within_at} to own file
* Update src/topology/continuous_on.lean

### [2019-10-08 02:26:24](https://github.com/leanprover-community/mathlib/commit/045d931)
feat(tactic/find): find defs as well as theorems ([#1512](https://github.com/leanprover-community/mathlib/pull/1512))
* feat(tactic/find): find defs as well as theorems
* use env.mfold
* use try

### [2019-10-08 00:28:49](https://github.com/leanprover-community/mathlib/commit/ef7248f)
feat(data/quot): define `quotient.map₂'`, use it for group quotient ([#1507](https://github.com/leanprover-community/mathlib/pull/1507))

### [2019-10-07 22:43:00](https://github.com/leanprover-community/mathlib/commit/bf22408)
chore(topology/algebra/group_completion): missing namespace ([#1518](https://github.com/leanprover-community/mathlib/pull/1518))

### [2019-10-07 21:52:59](https://github.com/leanprover-community/mathlib/commit/1bf831f)
refactor(topology/dense_embedding): move dense embeddings to new file ([#1515](https://github.com/leanprover-community/mathlib/pull/1515))

### [2019-10-07 21:06:26](https://github.com/leanprover-community/mathlib/commit/b3eb34d)
doc(topology/order): module and definition docstrings ([#1505](https://github.com/leanprover-community/mathlib/pull/1505))

### [2019-10-07 17:24:46](https://github.com/leanprover-community/mathlib/commit/f519a12)
refactor(topology/list): move topology of lists, vectors to new file ([#1514](https://github.com/leanprover-community/mathlib/pull/1514))

### [2019-10-07 16:34:46](https://github.com/leanprover-community/mathlib/commit/ddbeb7e)
refactor(topology/maps): avoid repetition in dense embeddings ([#1513](https://github.com/leanprover-community/mathlib/pull/1513))

### [2019-10-05 15:44:17](https://github.com/leanprover-community/mathlib/commit/78a78ef)
feat(group_theory/submonoid): define `subtype.comm_monoid` ([#1511](https://github.com/leanprover-community/mathlib/pull/1511))

### [2019-10-05 12:20:29](https://github.com/leanprover-community/mathlib/commit/7df0e35)
chore(topology): sanity_check pass ([#1510](https://github.com/leanprover-community/mathlib/pull/1510))
* chore(topology): sanity_check pass
* fix(topology/uniform_space/separation): fix build
* fix(topology/metric_space): some more namespace fixes

### [2019-10-05 05:18:27](https://github.com/leanprover-community/mathlib/commit/98dbe27)
feat(algebra/opposites): add some trivial `@[simp]` lemmas ([#1508](https://github.com/leanprover-community/mathlib/pull/1508))

### [2019-10-04 14:25:15](https://github.com/leanprover-community/mathlib/commit/2f1bd1e)
fix(data/list/min_max): docs typo ([#1504](https://github.com/leanprover-community/mathlib/pull/1504))

### [2019-10-04 14:08:27](https://github.com/leanprover-community/mathlib/commit/343237d)
feat(algebra/Module): the category of R-modules ([#1420](https://github.com/leanprover-community/mathlib/pull/1420))
* Adds Module category
* Move punit module instance to punit_instances.lean
* Minor formatting
* Use coercions for Module morphisms to functions
* Small formatting improvements to Module
* Move module_id to id_apply
* Be specific about the universe Modules live in
* Minor indentation formatting
* updates for [#1380](https://github.com/leanprover-community/mathlib/pull/1380)
* oops
* remove ext lemma, unnecessary
* reverting changes in TopCommRing
* Change name of `module_hom_comp`
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update todo in src/algebra/category/Module/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>

### [2019-10-04 11:56:55](https://github.com/leanprover-community/mathlib/commit/494132e)
feat(algebra): commuting elements ([#1089](https://github.com/leanprover-community/mathlib/pull/1089))
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

### [2019-10-04 00:45:14](https://github.com/leanprover-community/mathlib/commit/3c58f16)
doc(linear_algebra/basic): add module and declaration doc strings ([#1501](https://github.com/leanprover-community/mathlib/pull/1501))
* doc(linear_algebra/basic): declaration doc strings
* doc(linear_algebra/basic): improve module doc
* Update src/linear_algebra/basic.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>

### [2019-10-03 19:53:03](https://github.com/leanprover-community/mathlib/commit/f854371)
feat(tactic/squeeze_simp): better handling of private declarations ([#1498](https://github.com/leanprover-community/mathlib/pull/1498))
* feat(tactic/squeeze_simp): better handling of private declarations
* Update core.lean

### [2019-10-03 17:37:55](https://github.com/leanprover-community/mathlib/commit/4ca1e63)
chore(*): fix errors in library and sanity_check ([#1499](https://github.com/leanprover-community/mathlib/pull/1499))
* chore(*): some cleanup by sanity_check
* fix(is_auto_generated): also check for ginductives
* fix(sanity_check): imp_intro is sanity_skip
* fix(sanity_check): don't report names of instances
* first errors
* second errors
* doc(logic/basic): add note
* add link to note
* mention letI

### [2019-10-03 09:33:33](https://github.com/leanprover-community/mathlib/commit/4bb8d44)
feat(data/equiv/algebra): automorphism groups for other structures ([#1141](https://github.com/leanprover-community/mathlib/pull/1141))
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

### [2019-10-02 16:42:34](https://github.com/leanprover-community/mathlib/commit/bea1c20)
fix(dioph): remove global vector3 notation ([#1502](https://github.com/leanprover-community/mathlib/pull/1502))
* fix(dioph): remove global vector3 notation
it overloads list notation, and then tries to find a coercion from vector3 to list
* also make other notations in dioph local
* undo localizing ++, overloading that is probably fine
* add comment

### [2019-10-02 17:27:04+02:00](https://github.com/leanprover-community/mathlib/commit/39ca4f1)
chore(.): delete CODEOWNERS

### [2019-10-01 18:48:13](https://github.com/leanprover-community/mathlib/commit/5ed5f59)
feat(tactic/delta_instance): handle parameters and use in library ([#1483](https://github.com/leanprover-community/mathlib/pull/1483))
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

### [2019-10-01 07:53:40](https://github.com/leanprover-community/mathlib/commit/800dba4)
chore(linear_map): use curly brackets for type class in linear_map coe_to_fun ([#1493](https://github.com/leanprover-community/mathlib/pull/1493))
* chore(linear_map): use curly brackets for type class in linear_map coe_to_fun
*  fix