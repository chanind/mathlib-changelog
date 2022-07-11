## [2019-10-31 23:37:26](https://github.com/leanprover-community/mathlib/commit/df91623)
chore(category_theory/whiskering): clean up ([#1613](https://github.com/leanprover-community/mathlib/pull/1613))
* chore(category_theory/whiskering): clean up
* ugh, the stalks proofs are so fragile
* fixes
* minor
* fix
* fix
#### Estimated changes
Modified src/algebraic_geometry/stalks.lean


Modified src/category_theory/monad/limits.lean


Modified src/category_theory/opposites.lean
- \+ *lemma* op_id
- \+ *lemma* unop_id
- \- *lemma* op_app
- \- *lemma* unop_app

Modified src/category_theory/whiskering.lean
- \- *lemma* whiskering_left_obj_obj
- \- *lemma* whiskering_left_obj_map
- \- *lemma* whiskering_left_map_app_app
- \- *lemma* whisker_left.app
- \- *lemma* whiskering_right_obj_obj
- \- *lemma* whiskering_right_obj_map
- \- *lemma* whiskering_right_map_app_app
- \- *lemma* whisker_right.app
- \+/\- *def* whisker_left
- \+/\- *def* whisker_right
- \+/\- *def* whiskering_left
- \+/\- *def* whiskering_right

Modified src/topology/sheaves/stalks.lean




## [2019-10-31 21:03:05](https://github.com/leanprover-community/mathlib/commit/cd0bc32)
chore(data/set/finite): move defns up hierarchy; rename fintype_of_finset, card_fintype_of_finset ([#1615](https://github.com/leanprover-community/mathlib/pull/1615))
* chore(data/set/finite): move defns up hierarchy
* get namespaces right
* fixes
* fix build
#### Estimated changes
Modified src/data/finsupp.lean


Modified src/data/fintype.lean
- \+ *theorem* card_of_finset
- \+ *theorem* card_of_finset'
- \+ *theorem* mem_to_finset
- \+ *theorem* mem_to_finset_val
- \+ *def* of_finset
- \+ *def* to_finset

Modified src/data/fintype/intervals.lean


Modified src/data/set/finite.lean
- \- *theorem* card_fintype_of_finset
- \- *theorem* card_fintype_of_finset'
- \- *theorem* mem_to_finset
- \- *theorem* mem_to_finset_val
- \- *def* fintype_of_finset
- \- *def* to_finset

Modified src/group_theory/order_of_element.lean




## [2019-10-31 13:24:24](https://github.com/leanprover-community/mathlib/commit/6b51787)
feat(order/conditionally_complete_lattice): add complete_linear_order instance for enat ([#1633](https://github.com/leanprover-community/mathlib/pull/1633))
#### Estimated changes
Modified src/data/nat/enat.lean
- \+ *lemma* with_top_equiv_top
- \+ *lemma* with_top_equiv_coe
- \+ *lemma* with_top_equiv_zero
- \+ *lemma* with_top_equiv_le
- \+ *lemma* with_top_equiv_lt
- \+ *lemma* with_top_equiv_symm_top
- \+ *lemma* with_top_equiv_symm_coe
- \+ *lemma* with_top_equiv_symm_zero
- \+ *lemma* with_top_equiv_symm_le
- \+ *lemma* with_top_equiv_symm_lt

Modified src/order/conditionally_complete_lattice.lean




## [2019-10-31 11:20:33](https://github.com/leanprover-community/mathlib/commit/780cbc9)
feat(tactic/simps): allow let-expressions ([#1626](https://github.com/leanprover-community/mathlib/pull/1626))
* feat(simps); allow let-expressions
* Update src/meta/expr.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
#### Estimated changes
Modified docs/tactics.md


Modified src/meta/expr.lean


Modified src/tactic/simps.lean


Modified test/simps.lean
- \+ *def* let1
- \+ *def* let2
- \+ *def* let3
- \+ *def* let4



## [2019-10-30 20:31:06](https://github.com/leanprover-community/mathlib/commit/d43f7f9)
feat(.travis.yml): add linting to test stage ([#1606](https://github.com/leanprover-community/mathlib/pull/1606))
#### Estimated changes
Modified .travis.yml


Modified scripts/mk_all.sh




## [2019-10-30 17:35:02](https://github.com/leanprover-community/mathlib/commit/aadfde6)
feat(data/fintype): fintype.card_subtype_lt ([#1635](https://github.com/leanprover-community/mathlib/pull/1635))
* feat(data/fintype): fintype.card_subtype_lt
* Update src/data/fintype.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/data/fintype.lean
- \+ *theorem* fintype.card_subtype_lt



## [2019-10-29 22:34:46](https://github.com/leanprover-community/mathlib/commit/ca90081)
feat(number_theory/sum_four_squares): every natural number is the sum of four square numbers ([#1560](https://github.com/leanprover-community/mathlib/pull/1560))
* feat(number_theory/sum_four_squares): every natural number is the sum of four square numbers
* Johan's suggestions
* some better parity proofs
* fix silly lemmas in finite_fields
* generalize a lemma
* fix build
* Update src/number_theory/sum_four_squares.lean
* add docs in correct style
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_eq_multiset_prod

Modified src/data/int/basic.lean
- \+ *lemma* is_ring_hom.map_int_cast
- \+ *lemma* ring_hom.map_int_cast

Modified src/data/int/parity.lean
- \+ *theorem* even_neg

Modified src/data/nat/cast.lean
- \+ *lemma* is_semiring_hom.map_nat_cast
- \+ *lemma* ring_hom.map_nat_cast

Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/field_theory/finite.lean
- \+ *lemma* sum_two_squares

Created src/number_theory/sum_four_squares.lean
- \+ *lemma* sum_two_squares_of_two_mul_sum_two_squares
- \+ *lemma* exists_sum_two_squares_add_one_eq_k
- \+ *lemma* sum_four_squares



## [2019-10-29 09:22:53](https://github.com/leanprover-community/mathlib/commit/6030ff0)
chore(category_theory): speed-up monoidal.of_has_finite_products ([#1616](https://github.com/leanprover-community/mathlib/pull/1616))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* prod.pentagon
- \+ *lemma* prod.associator_naturality
- \+ *lemma* prod.triangle
- \+ *lemma* coprod.pentagon
- \+ *lemma* coprod.associator_naturality
- \+ *lemma* coprod.triangle

Modified src/category_theory/monoidal/of_has_finite_products.lean




## [2019-10-29 07:16:16](https://github.com/leanprover-community/mathlib/commit/e6e25d0)
cleanup(order|string) ([#1629](https://github.com/leanprover-community/mathlib/pull/1629))
move data.string to data.string.basic
remove classical.decidable_linear_order. was duplicate of classical.DLO
#### Estimated changes
Modified src/data/multiset.lean


Renamed src/data/string.lean to src/data/string/basic.lean


Modified src/order/basic.lean


Modified src/order/pilex.lean


Modified src/tactic/subtype_instance.lean




## [2019-10-29 05:05:10](https://github.com/leanprover-community/mathlib/commit/b9e3dbb)
feat(rat): give Q-algebra structure on field ([#1628](https://github.com/leanprover-community/mathlib/pull/1628))
also move around some declarations in rat.cast
the only new declaration in that file is is_ring_hom_cast
#### Estimated changes
Modified src/data/rat/cast.lean
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_mk

Modified src/ring_theory/algebra.lean




## [2019-10-29 03:03:51](https://github.com/leanprover-community/mathlib/commit/b5b674c)
fix(*): use has_coe_t ([#1627](https://github.com/leanprover-community/mathlib/pull/1627))
#### Estimated changes
Modified src/data/seq/computation.lean


Modified src/group_theory/coset.lean


Modified src/order/filter/filter_product.lean


Modified src/ring_theory/localization.lean


Modified src/topology/uniform_space/completion.lean




## [2019-10-29 00:42:49](https://github.com/leanprover-community/mathlib/commit/0ea3dfe)
feat(tactic/rcases): transport the `cases h : e` syntax to `rcases` ([#1611](https://github.com/leanprover-community/mathlib/pull/1611))
* Update rcases.lean
* Update rcases.lean
* Update rcases.lean
* Update lift.lean
* Update rcases.lean
* Update tactics.md
* Update rcases.lean
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/lift.lean


Modified src/tactic/rcases.lean


Modified test/rcases.lean




## [2019-10-28 21:23:53](https://github.com/leanprover-community/mathlib/commit/7a8f53e)
feat(tactic/lint): silent linting ([#1580](https://github.com/leanprover-community/mathlib/pull/1580))
* feat(tactic/lint): silent linting
* doc(tactic/lint): doc silent linting and nolint features
* fix test
* change notation for silent linting
* style(tactic/lint): remove commented lines
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/lint.lean


Modified test/lint.lean




## [2019-10-28 16:28:58](https://github.com/leanprover-community/mathlib/commit/94e368c)
chore(ring_theory/algebra): add docstring to algebra.comap and remove unused instances ([#1624](https://github.com/leanprover-community/mathlib/pull/1624))
* doc(ring_theory/algebra): add docstring to algebra.comap
* Update algebra.lean
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+/\- *def* comap



## [2019-10-28 10:34:50](https://github.com/leanprover-community/mathlib/commit/c2e81dd)
fix(tactic/omega): fix omega bugs, add docstring (closes [#1484](https://github.com/leanprover-community/mathlib/pull/1484)) ([#1620](https://github.com/leanprover-community/mathlib/pull/1620))
* Fix omega bugs, add docstring
* style(tactic/omega/main): trivial cleaning
#### Estimated changes
Modified src/tactic/omega/int/main.lean


Modified src/tactic/omega/main.lean


Modified src/tactic/omega/nat/main.lean


Modified test/omega.lean




## [2019-10-27 17:05:13](https://github.com/leanprover-community/mathlib/commit/1fa03c2)
feat(linear_algebra/basic): define algebra structure on endomorphisms of module ([#1618](https://github.com/leanprover-community/mathlib/pull/1618))
* feat(linear_algebra/basic): define algebra structure on endomorphisms of module
* Update algebra.lean
#### Estimated changes
Modified src/ring_theory/algebra.lean




## [2019-10-27 07:06:37](https://github.com/leanprover-community/mathlib/commit/89ece14)
fix(data/mv_polynomial): generalize equivs to comm_semiring ([#1621](https://github.com/leanprover-community/mathlib/pull/1621))
This apparently makes the elaborator's job a lot easier, and
reduces the compile time of the whole module by a factor of 3.
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+/\- *def* ring_equiv_congr
- \+/\- *def* mv_polynomial_equiv_mv_polynomial



## [2019-10-27 02:35:54](https://github.com/leanprover-community/mathlib/commit/8a45d98)
chore(category_theory): remove superfluous lemma ([#1614](https://github.com/leanprover-community/mathlib/pull/1614))
#### Estimated changes
Modified src/category_theory/category/default.lean
- \- *lemma* category.assoc_symm

Modified src/category_theory/equivalence.lean


Modified src/category_theory/functor_category.lean


Modified src/category_theory/limits/limits.lean




## [2019-10-26 12:58:23](https://github.com/leanprover-community/mathlib/commit/8eaf478)
feat(linear_algebra/basis): Dedekind's linear independence of characters ([#1595](https://github.com/leanprover-community/mathlib/pull/1595))
* feat(linear_algebra/basis): Dedekind's linear independence of characters
* feat(linear_algebra/basis): generalize independence of characters to integral domains
* chore(linear_algebra/basis): change proofs
* commenting the proof
#### Estimated changes
Modified src/data/finset.lean


Modified src/linear_algebra/basis.lean
- \+ *theorem* linear_independent_iff'
- \+ *theorem* linear_independent_monoid_hom



## [2019-10-26 10:17:39](https://github.com/leanprover-community/mathlib/commit/b9798dc)
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
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* eq_of_dvd_of_div_eq_one
- \+ *lemma* eq_zero_of_dvd_of_div_eq_zero
- \- *lemma* eq_of_dvd_quot_one

Modified src/data/nat/prime.lean




## [2019-10-26 08:23:59](https://github.com/leanprover-community/mathlib/commit/b46f5b0)
feat(data/set/intervals): fintype instances for ℕ and ℤ ([#1602](https://github.com/leanprover-community/mathlib/pull/1602))
* starting on fintype instances for Icos
* finishing fintypes
* minor
* move file
* oops
* redone
* formatting
* cleaning up
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* mem
- \+ *def* Ico_ℤ

Created src/data/fintype/intervals.lean


Modified src/data/int/basic.lean
- \+ *lemma* to_nat_sub_of_le



## [2019-10-25 15:46:12](https://github.com/leanprover-community/mathlib/commit/6ee8bf9)
refactor(data/rat/meta): rename to meta_defs ([#1612](https://github.com/leanprover-community/mathlib/pull/1612))
* refactor(data/rat/meta): rename to meta_defs
* fix build
#### Estimated changes
Modified src/data/rat/default.lean


Renamed src/data/rat/meta.lean to src/data/rat/meta_defs.lean


Modified src/tactic/norm_num.lean


Modified test/rat.lean




## [2019-10-24 21:13:25](https://github.com/leanprover-community/mathlib/commit/9db43a5)
chore(data/nat/basic): remove pos_iff_ne_zero' ([#1610](https://github.com/leanprover-community/mathlib/pull/1610))
This used to be different from pos_iff_ne_zero because the latter
was phrased in terms of `n > 0`, not `0 < n`. Since [#1436](https://github.com/leanprover-community/mathlib/pull/1436) they
are the same.
#### Estimated changes
Modified src/analysis/complex/exponential.lean


Modified src/data/nat/basic.lean
- \- *theorem* pos_iff_ne_zero'

Modified src/ring_theory/multiplicity.lean




## [2019-10-24 17:11:21](https://github.com/leanprover-community/mathlib/commit/151bcbe)
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
#### Estimated changes
Modified src/data/rat/default.lean


Created src/data/rat/meta.lean


Modified src/meta/expr.lean


Modified src/tactic/norm_num.lean


Created test/rat.lean




## [2019-10-24 15:08:35](https://github.com/leanprover-community/mathlib/commit/3f8a492)
chore(category_theory): replace some @[simp] with @[simps] ([#1605](https://github.com/leanprover-community/mathlib/pull/1605))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *def* prod.braiding
- \+/\- *def* prod.associator
- \+/\- *def* prod.left_unitor
- \+/\- *def* prod.right_unitor
- \+/\- *def* coprod.braiding
- \+/\- *def* coprod.associator
- \+/\- *def* coprod.left_unitor
- \+/\- *def* coprod.right_unitor



## [2019-10-24 13:48:11](https://github.com/leanprover-community/mathlib/commit/b1f44ba)
chore(group_theory/free_group,order/zorn): rename zorn.zorn and sum.sum ([#1604](https://github.com/leanprover-community/mathlib/pull/1604))
* chore(order/zorn): rename zorn.zorn
* chore(group_theory/free_group): rename sum.sum
* chore(group_theory/free_group,order/zorn): remove nolint
#### Estimated changes
Modified src/group_theory/free_group.lean
- \+ *lemma* sum.mul
- \- *lemma* sum.sum

Modified src/order/filter/basic.lean


Modified src/order/zorn.lean
- \+ *theorem* exists_maximal_of_chains_bounded
- \- *theorem* zorn



## [2019-10-24 11:26:19](https://github.com/leanprover-community/mathlib/commit/5da754c)
fix(tactic/solve_by_elim): parameter parsing ([#1591](https://github.com/leanprover-community/mathlib/pull/1591))
* fix(tactic/solve_by_elim): parameter parsing
* revert accidental commenting out
* doc comments for solve_by_elim
* fix build
#### Estimated changes
Modified src/tactic/solve_by_elim.lean


Modified src/tactic/suggest.lean


Modified test/solve_by_elim.lean


Modified test/suggest.lean




## [2019-10-24 06:28:15](https://github.com/leanprover-community/mathlib/commit/4b9cdf4)
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
#### Estimated changes
Modified src/group_theory/free_group.lean
- \+/\- *lemma* sum.sum

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional_of_finite_basis
- \- *def* finite_dimensional_of_finite_basis

Modified src/number_theory/pell.lean


Modified src/order/lattice.lean
- \+ *theorem* ext
- \- *theorem* lattice.ext

Modified src/order/zorn.lean
- \+/\- *theorem* zorn

Modified src/ring_theory/algebraic.lean
- \+ *lemma* subalgebra.is_algebraic_iff
- \- *def* subalgebra.is_algebraic_iff

Modified src/set_theory/ordinal.lean
- \+/\- *def* div_def
- \+/\- *def* ord_eq_min

Modified src/tactic/reassoc_axiom.lean
- \+ *theorem* category_theory.reassoc_of
- \- *def* category_theory.reassoc_of

Modified src/tactic/transfer.lean




## [2019-10-24 02:49:46](https://github.com/leanprover-community/mathlib/commit/31c73c1)
feat(data/multiset): map_eq_map_of_bij_of_nodup ([#1590](https://github.com/leanprover-community/mathlib/pull/1590))
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/data/multiset.lean
- \+ *lemma* map_eq_map_of_bij_of_nodup
- \+ *theorem* eq_zero_iff_forall_not_mem



## [2019-10-24 00:47:18](https://github.com/leanprover-community/mathlib/commit/08977be)
feat(algebra/semiconj): define `semiconj_by` and some operations ([#1576](https://github.com/leanprover-community/mathlib/pull/1576))
* feat(algebra/semiconj): define `semiconj_by` and some operations
Also rewrite `algebra/commute` to reuse results from `algebra/semiconj`.
* Some `@[simp]` attributes
* Fixes by @rwbarton, more docs
* Add two more constructors
#### Estimated changes
Modified src/algebra/commute.lean
- \+/\- *theorem* one_right
- \+/\- *theorem* one_left
- \+/\- *theorem* units_inv_right
- \+/\- *theorem* units_inv_left
- \+/\- *theorem* pow_right
- \+/\- *theorem* pow_left
- \+/\- *theorem* pow_pow
- \+/\- *theorem* self_pow
- \+/\- *theorem* pow_self
- \+/\- *theorem* pow_pow_self
- \+/\- *theorem* units_coe
- \+ *theorem* units_of_coe
- \+ *theorem* units_coe_iff
- \+/\- *theorem* inv_right
- \+/\- *theorem* inv_right_iff
- \+/\- *theorem* inv_left
- \+/\- *theorem* inv_left_iff
- \+/\- *theorem* inv_inv
- \+/\- *theorem* inv_inv_iff
- \+/\- *theorem* gpow_right
- \+/\- *theorem* gpow_left
- \+/\- *theorem* gpow_gpow
- \+/\- *theorem* self_gpow
- \+/\- *theorem* gpow_self
- \+/\- *theorem* gpow_gpow_self
- \+/\- *theorem* zero_right
- \+/\- *theorem* zero_left
- \+/\- *theorem* add_right
- \+/\- *theorem* add_left
- \+/\- *theorem* smul_right
- \+/\- *theorem* smul_left
- \+/\- *theorem* smul_smul
- \+/\- *theorem* self_smul
- \+/\- *theorem* smul_self
- \+/\- *theorem* self_smul_smul
- \+/\- *theorem* cast_nat_right
- \+/\- *theorem* cast_nat_left
- \+/\- *theorem* neg_right
- \+/\- *theorem* neg_right_iff
- \+/\- *theorem* neg_left
- \+/\- *theorem* neg_left_iff
- \+/\- *theorem* neg_one_right
- \+/\- *theorem* neg_one_left
- \+/\- *theorem* sub_right
- \+/\- *theorem* sub_left
- \+/\- *theorem* gsmul_right
- \+/\- *theorem* gsmul_left
- \+/\- *theorem* gsmul_gsmul
- \+/\- *theorem* self_gsmul
- \+/\- *theorem* gsmul_self
- \+/\- *theorem* self_gsmul_gsmul
- \+/\- *theorem* cast_int_right
- \+/\- *theorem* cast_int_left
- \+/\- *theorem* mem_centralizer
- \+ *theorem* commute.list_prod_right
- \+ *theorem* commute.list_prod_left
- \- *theorem* list_prod_right
- \- *theorem* list_prod_left
- \+/\- *def* commute
- \+/\- *def* centralizer

Created src/algebra/semiconj.lean
- \+ *lemma* mul_right
- \+ *lemma* mul_left
- \+ *lemma* one_right
- \+ *lemma* one_left
- \+ *lemma* units_inv_right
- \+ *lemma* units_inv_right_iff
- \+ *lemma* units_inv_symm_left
- \+ *lemma* units_inv_symm_left_iff
- \+ *lemma* pow_right
- \+ *lemma* units_gpow_right
- \+ *lemma* units_conj_mk
- \+ *lemma* inv_right_iff
- \+ *lemma* inv_right
- \+ *lemma* inv_symm_left_iff
- \+ *lemma* inv_symm_left
- \+ *lemma* inv_inv_symm
- \+ *lemma* inv_inv_symm_iff
- \+ *lemma* conj_mk
- \+ *lemma* gpow_right
- \+ *lemma* add_right
- \+ *lemma* add_left
- \+ *lemma* zero_right
- \+ *lemma* zero_left
- \+ *lemma* smul_right
- \+ *lemma* smul_left
- \+ *lemma* smul_smul
- \+ *lemma* cast_nat_right
- \+ *lemma* cast_nat_left
- \+ *lemma* neg_right
- \+ *lemma* neg_right_iff
- \+ *lemma* neg_left
- \+ *lemma* neg_left_iff
- \+ *lemma* neg_one_right
- \+ *lemma* neg_one_left
- \+ *lemma* sub_right
- \+ *lemma* sub_left
- \+ *lemma* gsmul_right
- \+ *lemma* gsmul_left
- \+ *lemma* gsmul_gsmul
- \+ *theorem* units_coe
- \+ *theorem* units_of_coe
- \+ *theorem* units_coe_iff
- \+ *def* semiconj_by



## [2019-10-23 23:11:12](https://github.com/leanprover-community/mathlib/commit/e2a8e63)
feat(geometry/manifold): improvements for smooth manifolds ([#1593](https://github.com/leanprover-community/mathlib/pull/1593))
* feat(geometry/manifold): improvements to smooth manifolds
* fix
* better definition for half-space
* fix docstring
* address comments
* more comments
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_on_const
- \+ *lemma* times_cont_diff.comp_times_cont_diff_on
- \+ *lemma* times_cont_diff_on.add
- \+ *lemma* times_cont_diff.add
- \+ *lemma* times_cont_diff_on.neg
- \+ *lemma* times_cont_diff.neg
- \+ *lemma* times_cont_diff_on.sub
- \+ *lemma* times_cont_diff.sub

Modified src/geometry/manifold/manifold.lean
- \+ *lemma* mem_pregroupoid_of_eq_on_source
- \+ *lemma* has_groupoid_of_pregroupoid
- \+ *def* pregroupoid.groupoid
- \- *def* groupoid_of_pregroupoid

Created src/geometry/manifold/real_instances.lean
- \+ *lemma* findim_euclidean_space
- \+ *lemma* range_half_space
- \+ *lemma* range_quadrant
- \+ *def* euclidean_space
- \+ *def* euclidean_half_space
- \+ *def* euclidean_quadrant
- \+ *def* model_with_corners_euclidean_half_space
- \+ *def* model_with_corners_euclidean_quadrant
- \+ *def* lt_class
- \+ *def* Icc_left_chart
- \+ *def* Icc_right_chart

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+/\- *lemma* times_cont_diff_groupoid_le
- \+/\- *lemma* times_cont_diff_groupoid_zero_eq
- \+ *lemma* of_set_mem_times_cont_diff_groupoid
- \+ *lemma* symm_trans_mem_times_cont_diff_groupoid
- \- *lemma* range_half_space
- \+/\- *def* times_cont_diff_groupoid
- \- *def* euclidean_space
- \- *def* euclidean_half_space
- \- *def* model_with_corners_euclidean_half_space

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* findim_fintype_fun_eq_card
- \+ *lemma* findim_fin_fun



## [2019-10-23 20:48:14](https://github.com/leanprover-community/mathlib/commit/b433afa)
feat(algebra/big_operators): sum_ite ([#1598](https://github.com/leanprover-community/mathlib/pull/1598))
* feat(algebra/big_operators): sum_ite
rename the current `sum_ite` to `sum_ite_eq` and add a more general version
* Update src/algebra/big_operators.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_ite
- \+ *lemma* prod_ite_eq



## [2019-10-23 20:28:52](https://github.com/leanprover-community/mathlib/commit/36dfcfc)
doc(topology/topological_fiber_bundle): documentation improvements ([#1594](https://github.com/leanprover-community/mathlib/pull/1594))
* feat(topology/topological_fiber_bundle): improvements
* minor fixes
#### Estimated changes
Modified src/topology/topological_fiber_bundle.lean
- \+/\- *def* index
- \+/\- *def* base
- \+/\- *def* fiber
- \+/\- *def* total_space



## [2019-10-23 17:05:43](https://github.com/leanprover-community/mathlib/commit/d214c61)
feat(data/nat/modeq): div_mod_eq_mod_mul_div ([#1597](https://github.com/leanprover-community/mathlib/pull/1597))
#### Estimated changes
Modified src/data/nat/modeq.lean
- \+ *lemma* div_mod_eq_mod_mul_div



## [2019-10-23 14:43:45](https://github.com/leanprover-community/mathlib/commit/36f7113)
fix(suggest): focus1 at the correct moment ([#1592](https://github.com/leanprover-community/mathlib/pull/1592))
#### Estimated changes
Modified src/tactic/suggest.lean


Modified test/suggest.lean




## [2019-10-23 12:50:43](https://github.com/leanprover-community/mathlib/commit/24dd80b)
chore(src/data/mv_polynomial): doc comments and removing unused arguments ([#1585](https://github.com/leanprover-community/mathlib/pull/1585))
* chore(src/data/mv_polynomial): doc comments and removing unused arguments
* Update src/data/mv_polynomial.lean
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \- *def* tmp.coe



## [2019-10-23 10:48:29](https://github.com/leanprover-community/mathlib/commit/079e6ec)
feat(analysis/normed_space): norms on ℤ and ℚ ([#1570](https://github.com/leanprover-community/mathlib/pull/1570))
* feat(analysis/normed_space): norms on ℤ and ℚ
* Add some `elim_cast` lemmas
* Add `@[simp]`, thanks @robertylewis
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* int.norm_cast_real
- \+ *lemma* rat.norm_cast_real
- \+ *lemma* int.norm_cast_rat

Modified src/topology/instances/real.lean
- \+ *lemma* rat.dist_cast
- \+ *theorem* int.dist_eq
- \+ *theorem* int.dist_cast_real
- \+ *theorem* int.dist_cast_rat



## [2019-10-23 07:50:35](https://github.com/leanprover-community/mathlib/commit/ee5518c)
fix(category_theory/adjunctions): fix deterministic timeouts ([#1586](https://github.com/leanprover-community/mathlib/pull/1586))
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/limits.lean
- \+ *def* functoriality_right_adjoint
- \+ *def* functoriality_unit
- \+ *def* functoriality_counit
- \+ *def* functoriality_left_adjoint
- \+ *def* functoriality_unit'
- \+ *def* functoriality_counit'
- \+ *def* cocones_iso_component_hom
- \+ *def* cocones_iso_component_inv
- \+ *def* cones_iso_component_hom
- \+ *def* cones_iso_component_inv

Modified src/category_theory/limits/cones.lean




## [2019-10-23 00:26:28](https://github.com/leanprover-community/mathlib/commit/5722ee8)
refactor(data/finset): restate disjoint_filter ([#1583](https://github.com/leanprover-community/mathlib/pull/1583))
* refactor(data/finset): restate disjoint_filter
* fix build
* fix build
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/data/finset.lean


Modified src/data/nat/totient.lean


Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/group_theory/order_of_element.lean




## [2019-10-22 16:25:55](https://github.com/leanprover-community/mathlib/commit/31906d8)
chore(algebra/category/CommRing/limits): fix typo, remove private ([#1584](https://github.com/leanprover-community/mathlib/pull/1584))
* chore(algebra/category/CommRing/limits): fix typo, remove private
* Update src/algebra/category/CommRing/limits.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebra/category/CommRing/limits.lean
* Update src/algebra/category/CommRing/limits.lean
* bleh
* Update src/algebra/category/CommRing/limits.lean
#### Estimated changes
Modified src/algebra/category/CommRing/limits.lean
- \+ *def* limit
- \+ *def* limit_is_limit



## [2019-10-22 14:30:51](https://github.com/leanprover-community/mathlib/commit/e8bdb05)
feat(algebra/group): conversion between `→*` and `→+` ([#1569](https://github.com/leanprover-community/mathlib/pull/1569))
* feat(algebra/group): conversion between `→*` and `→+`
* docs
* Rename to allow use of projection notation
#### Estimated changes
Modified src/algebra/group/type_tags.lean
- \+ *def* add_monoid_hom.to_multiplicative
- \+ *def* monoid_hom.to_additive



## [2019-10-22 12:22:04](https://github.com/leanprover-community/mathlib/commit/93b1786)
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
#### Estimated changes
Created archive/sensitivity.lean
- \+ *lemma* card
- \+ *lemma* succ_n_eq
- \+ *lemma* not_adjacent_zero
- \+ *lemma* adj_iff_proj_eq
- \+ *lemma* adj_iff_proj_adj
- \+ *lemma* adjacent.symm
- \+ *lemma* e_zero_apply
- \+ *lemma* duality
- \+ *lemma* epsilon_total
- \+ *lemma* dim_V
- \+ *lemma* findim_V
- \+ *lemma* f_zero
- \+ *lemma* f_succ_apply
- \+ *lemma* f_squared
- \+ *lemma* f_matrix
- \+ *lemma* g_apply
- \+ *lemma* g_injective
- \+ *lemma* f_image_g
- \+ *lemma* exists_eigenvalue
- \+ *theorem* huang_degree_theorem
- \+ *def* π
- \+ *def* adjacent
- \+ *def* V
- \+ *def* module
- \+ *def* add_comm_semigroup
- \+ *def* add_comm_monoid
- \+ *def* has_scalar
- \+ *def* has_add
- \+ *def* dual_pair_e_ε



## [2019-10-22 08:36:07](https://github.com/leanprover-community/mathlib/commit/1b4d1ea)
chore(algebra/category/*/colimits): remove unnecessary projections ([#1588](https://github.com/leanprover-community/mathlib/pull/1588))
* refactor(category_theory,algebra/category): make algebraic categories not [reducible]
Adapted from part of [#1438](https://github.com/leanprover-community/mathlib/pull/1438).
* Update src/algebra/category/CommRing/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* adding missing forget2 instances
* Converting Reid's comment to a [Note]
* adding examples testing coercions
* chore(algebra/category/*/colimits): remove unnecessary projections
#### Estimated changes
Modified src/algebra/category/CommRing/colimits.lean
- \+/\- *def* cocone_fun

Modified src/algebra/category/Mon/colimits.lean
- \+/\- *def* cocone_fun



## [2019-10-22 06:42:16](https://github.com/leanprover-community/mathlib/commit/2b98d47)
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
#### Estimated changes
Modified docs/tactics.md


Modified src/category_theory/comma.lean
- \+/\- *lemma* w

Modified src/category_theory/functor.lean


Modified src/tactic/reassoc_axiom.lean
- \+ *def* calculated_Prop
- \+ *def* category_theory.reassoc_of

Modified test/tactics.lean




## [2019-10-22 04:37:39](https://github.com/leanprover-community/mathlib/commit/1741a1d)
feat(data/nat/basic): division inequalities ([#1579](https://github.com/leanprover-community/mathlib/pull/1579))
* feat(data/nat/basic): division inequalities
* whitespace
* fix
* shorten proof
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* mul_div_le_mul_div_assoc
- \+ *lemma* div_mul_div_le_div



## [2019-10-22 02:29:49](https://github.com/leanprover-community/mathlib/commit/c9ba7a5)
refactor(category_theory,algebra/category): make algebraic categories not [reducible] ([#1491](https://github.com/leanprover-community/mathlib/pull/1491))
* refactor(category_theory,algebra/category): make algebraic categories not [reducible]
Adapted from part of [#1438](https://github.com/leanprover-community/mathlib/pull/1438).
* Update src/algebra/category/CommRing/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* adding missing forget2 instances
* Converting Reid's comment to a [Note]
* adding examples testing coercions
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean
- \- *lemma* id_eq
- \- *lemma* comp_eq
- \- *lemma* forget_obj_eq_coe
- \- *lemma* forget_map_eq_coe
- \+/\- *def* SemiRing
- \+/\- *def* Ring
- \+/\- *def* CommSemiRing
- \+/\- *def* CommRing

Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/CommRing/limits.lean


Modified src/algebra/category/Group.lean
- \+/\- *def* Group
- \+/\- *def* CommGroup
- \+/\- *def* of

Modified src/algebra/category/Mon/basic.lean
- \+/\- *def* CommMon
- \+/\- *def* of

Modified src/algebra/category/Mon/colimits.lean


Modified src/category_theory/concrete_category/basic.lean
- \+ *lemma* forget_obj_eq_coe
- \+ *lemma* forget_map_eq_coe
- \+ *lemma* coe_id
- \+ *lemma* coe_comp
- \+ *def* concrete_category.has_coe_to_sort
- \+ *def* concrete_category.has_coe_to_fun

Modified src/category_theory/concrete_category/bundled.lean
- \+/\- *def* map

Modified src/category_theory/concrete_category/bundled_hom.lean
- \- *lemma* coe_id
- \- *lemma* coe_comp
- \- *def* has_coe_to_fun
- \- *def* full_subcategory_has_forget₂

Modified src/category_theory/full_subcategory.lean
- \+/\- *def* induced_functor

Modified src/category_theory/limits/cones.lean
- \+ *lemma* naturality_concrete
- \- *lemma* naturality_bundled



## [2019-10-22 00:57:19](https://github.com/leanprover-community/mathlib/commit/340178d)
feat(data/finset): inj_on_of_surj_on_of_card_le ([#1578](https://github.com/leanprover-community/mathlib/pull/1578))
* feat(data/finset): inj_on_of_surj_on_of_card_le
* Type ascriptions
* function namespace
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* inj_on_of_surj_on_of_card_le



## [2019-10-21 22:57:07](https://github.com/leanprover-community/mathlib/commit/39092ab)
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
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* module.smul_eq_smul
- \+ *lemma* finset.sum_const'

Modified src/algebra/ring.lean
- \+ *lemma* mul_ite

Modified src/data/set/finite.lean
- \+ *lemma* to_finset_card
- \+ *lemma* to_finset_inter
- \+ *lemma* fintype.exists_max
- \+ *def* decidable_mem_of_fintype

Modified src/linear_algebra/dual.lean
- \+/\- *lemma* to_dual_to_dual
- \+ *lemma* coeffs_apply
- \+ *lemma* dual_lc
- \+ *lemma* coeffs_lc
- \+ *lemma* decomposition
- \+ *lemma* mem_of_mem_span
- \+ *lemma* is_basis
- \+ *lemma* eq_dual
- \+ *def* coeffs
- \+ *def* lc

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* fg_of_finite_basis
- \+ *lemma* dim_eq_card
- \+ *def* finite_dimensional_of_finite_basis

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* linear_map.map_finsupp_total

Modified src/ring_theory/power_series.lean


Modified src/set_theory/cardinal.lean
- \+/\- *theorem* nat_cast_pow



## [2019-10-21 20:49:04+02:00](https://github.com/leanprover-community/mathlib/commit/96ebf8c)
docs(README): Remove Patrick from the maintainer list.
#### Estimated changes
Modified README.md




## [2019-10-21 15:12:24](https://github.com/leanprover-community/mathlib/commit/6cf3d04)
fix(algebra/group/hom): Fix spurrious arguments ([#1581](https://github.com/leanprover-community/mathlib/pull/1581))
This bug was introduced in eb230d3b48f4da49b
#### Estimated changes
Modified src/algebra/group/hom.lean




## [2019-10-21 14:34:56](https://github.com/leanprover-community/mathlib/commit/f19dbf2)
feat(geometric/manifold): smooth manifolds ([#1555](https://github.com/leanprover-community/mathlib/pull/1555))
* smooth manifolds
* fix docstrings
* update docstring
* remove out_param
#### Estimated changes
Created src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* model_with_corners_self_local_equiv
- \+ *lemma* model_with_corners_target
- \+ *lemma* model_with_corners_left_inv
- \+ *lemma* model_with_corners_inv_fun_comp
- \+ *lemma* model_with_corners_right_inv
- \+ *lemma* model_with_corners.image
- \+ *lemma* times_cont_diff_groupoid_le
- \+ *lemma* times_cont_diff_groupoid_zero_eq
- \+ *lemma* range_half_space
- \+ *def* model_with_corners_self
- \+ *def* model_with_corners.prod
- \+ *def* model_with_corners.tangent
- \+ *def* times_cont_diff_groupoid
- \+ *def* euclidean_space
- \+ *def* euclidean_half_space
- \+ *def* model_with_corners_euclidean_half_space



## [2019-10-21 12:39:30](https://github.com/leanprover-community/mathlib/commit/f52e952)
feat(data/finset): define `finset.Ico.subset_iff` ([#1574](https://github.com/leanprover-community/mathlib/pull/1574))
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* subset_iff

Modified src/data/nat/basic.lean
- \+ *lemma* le_of_pred_lt



## [2019-10-21 10:18:48](https://github.com/leanprover-community/mathlib/commit/a4bbbde)
feat(topology/topological_fiber_bundle): topological fiber bundles ([#1421](https://github.com/leanprover-community/mathlib/pull/1421))
* feat(topology/topological_fiber_bundle): topological fiber bundles
* better definition of fiber bundles
#### Estimated changes
Created src/topology/topological_fiber_bundle.lean
- \+ *lemma* bundle_trivialization.continuous_at_proj
- \+ *lemma* is_topological_fiber_bundle.continuous_proj
- \+ *lemma* is_topological_fiber_bundle.is_open_map_proj
- \+ *lemma* is_topological_fiber_bundle_fst
- \+ *lemma* is_topological_fiber_bundle_snd
- \+ *lemma* mem_triv_change_source
- \+ *lemma* mem_local_triv'_source
- \+ *lemma* mem_local_triv'_target
- \+ *lemma* local_triv'_fst
- \+ *lemma* local_triv'_inv_fst
- \+ *lemma* local_triv'_trans
- \+ *lemma* open_source'
- \+ *lemma* open_target'
- \+ *lemma* mem_local_triv_source
- \+ *lemma* mem_local_triv_target
- \+ *lemma* local_triv_fst
- \+ *lemma* local_triv_symm_fst
- \+ *lemma* local_triv_trans
- \+ *lemma* continuous_proj
- \+ *lemma* is_open_map_proj
- \+ *lemma* mem_local_triv_at_source
- \+ *lemma* local_triv_at_fst
- \+ *lemma* local_triv_at_symm_fst
- \+ *lemma* local_triv_at_ext_to_local_homeomorph
- \+ *theorem* is_topological_fiber_bundle
- \+ *def* is_topological_fiber_bundle
- \+ *def* index
- \+ *def* base
- \+ *def* fiber
- \+ *def* total_space
- \+ *def* proj
- \+ *def* triv_change
- \+ *def* local_triv'
- \+ *def* local_triv
- \+ *def* local_triv_ext
- \+ *def* local_triv_at
- \+ *def* local_triv_at_ext



## [2019-10-21 08:23:05](https://github.com/leanprover-community/mathlib/commit/d2d29ff)
feat(algebra/geom_sum): sum of a geom_series over an Ico ([#1573](https://github.com/leanprover-community/mathlib/pull/1573))
* feat(algebra/geom_sum): sum of a geom_series over an Ico
* Add two more versions as requested by @jcommelin
#### Estimated changes
Modified src/algebra/geom_sum.lean
- \+ *theorem* geom_sum_Ico_mul
- \+ *theorem* geom_sum_Ico_mul_neg
- \+ *theorem* geom_sum_Ico



## [2019-10-21 08:06:20](https://github.com/leanprover-community/mathlib/commit/0b660a9)
fix(scripts): sanity_check -> lint [ci skip] ([#1575](https://github.com/leanprover-community/mathlib/pull/1575))
* fix(scripts): sanity_check -> lint [ci skip]
* also fix in .gitignore
#### Estimated changes
Modified .gitignore


Modified scripts/mk_all.sh


Modified scripts/rm_all.sh




## [2019-10-21 12:08:57+11:00](https://github.com/leanprover-community/mathlib/commit/809276c)
feat(topology/metric_space): polygonal version of the triangle inequality ([#1572](https://github.com/leanprover-community/mathlib/pull/1572))
* feat(topology/metric_space): "polygon" version of the triangle inequality
* Add two more versions of the "polygonal" inequality
* Use `dist_le_Ico_sum_dist` in `cauchy_seq_of_summable_dist`
#### Estimated changes
Modified src/data/real/nnreal.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* dist_le_Ico_sum_dist
- \+ *lemma* dist_le_range_sum_dist
- \+ *lemma* dist_le_Ico_sum_of_dist_le
- \+ *lemma* dist_le_range_sum_of_dist_le



## [2019-10-20 15:33:20](https://github.com/leanprover-community/mathlib/commit/b1654df)
feat(meta/rb_map,tactic/monotonicity): replace rb_map.insert_cons ([#1571](https://github.com/leanprover-community/mathlib/pull/1571))
rb_map key (list value) is the same as rb_lmap. Usages of this function
should be replaced with rb_lmap.insert
#### Estimated changes
Modified src/meta/rb_map.lean


Modified src/tactic/monotonicity/basic.lean




## [2019-10-20 10:46:47](https://github.com/leanprover-community/mathlib/commit/74bed0c)
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
#### Estimated changes
Modified docs/tactics.md


Modified src/category/basic.lean


Modified src/data/list/defs.lean


Modified src/data/mllist.lean


Modified src/data/option/basic.lean
- \+/\- *lemma* eq_some_iff_get_eq

Modified src/data/option/defs.lean


Modified src/tactic/basic.lean


Modified src/tactic/core.lean


Deleted src/tactic/library_search.lean
- \- *def* head_symbol_match.to_string

Modified src/tactic/rewrite_all/congr.lean


Created src/tactic/suggest.lean
- \+ *def* head_symbol_match.to_string

Modified test/library_search/basic.lean


Modified test/library_search/ordered_ring.lean


Modified test/library_search/ring_theory.lean


Modified test/mllist.lean


Created test/suggest.lean




## [2019-10-19 22:11:22](https://github.com/leanprover-community/mathlib/commit/f544632)
feat(algebra/big_operators): products and sums over `finset.Ico` ([#1567](https://github.com/leanprover-community/mathlib/pull/1567))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* sum_Ico_add
- \+ *lemma* prod_Ico_add
- \+ *lemma* prod_Ico_consecutive
- \+ *lemma* prod_range_mul_prod_Ico
- \+ *lemma* prod_Ico_eq_div
- \+ *lemma* sum_Ico_eq_sub
- \+ *lemma* prod_Ico_eq_prod_range

Modified src/data/finset.lean
- \+/\- *lemma* inter_consecutive
- \+ *lemma* disjoint_consecutive
- \+/\- *theorem* self_eq_empty
- \+/\- *theorem* succ_singleton



## [2019-10-19 19:57:42](https://github.com/leanprover-community/mathlib/commit/173e70a)
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
#### Estimated changes
Modified docs/tactics.md


Modified src/category/functor.lean
- \+/\- *def* const

Modified src/measure_theory/l1_space.lean


Modified src/meta/rb_map.lean


Modified src/tactic/basic.lean


Modified src/tactic/core.lean


Deleted src/tactic/doc_blame.lean


Modified src/tactic/interactive.lean
- \+/\- *lemma* {u}

Created src/tactic/lint.lean


Deleted src/tactic/sanity_check.lean


Renamed test/sanity_check.lean to test/lint.lean
- \+/\- *def* bar.foo



## [2019-10-19 19:04:46](https://github.com/leanprover-community/mathlib/commit/ee398b6)
feat(algebra/floor): prove `⌈x⌉ ≤ ⌊x⌋ + 1` ([#1568](https://github.com/leanprover-community/mathlib/pull/1568))
#### Estimated changes
Modified src/algebra/floor.lean
- \+ *theorem* ceil_le_floor_add_one



## [2019-10-18 19:41:32](https://github.com/leanprover-community/mathlib/commit/05102ec)
chore(category_theory): using simps ([#1500](https://github.com/leanprover-community/mathlib/pull/1500))
* chore(category_theory): using simps
* more simps
* remove simp lemma
* revertings overlapping @[simps]
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \- *lemma* cones_obj
- \- *lemma* cones_map
- \- *lemma* cocones_obj
- \- *lemma* cocones_map
- \- *lemma* whisker_π_app
- \- *lemma* whisker_ι_app
- \- *lemma* id.hom
- \- *lemma* comp.hom
- \- *lemma* ext_hom_hom
- \- *lemma* postcompose_obj_X
- \- *lemma* postcompose_obj_π
- \- *lemma* postcompose_map_hom
- \- *lemma* forget_obj
- \- *lemma* forget_map
- \- *lemma* precompose_obj_X
- \- *lemma* precompose_obj_ι
- \- *lemma* precompose_map_hom
- \+/\- *def* cones
- \+/\- *def* cocones
- \+/\- *def* whisker
- \+/\- *def* ext
- \+/\- *def* postcompose
- \+/\- *def* forget
- \+/\- *def* functoriality
- \+/\- *def* precompose

Modified src/category_theory/limits/functor_category.lean
- \+/\- *def* functor_category_limit_cone
- \+/\- *def* functor_category_colimit_cocone

Modified src/category_theory/limits/over.lean
- \- *lemma* to_cocone_X
- \- *lemma* to_cocone_ι
- \- *lemma* to_cone_X
- \- *lemma* to_cone_π
- \- *lemma* colimit_X_hom
- \- *lemma* colimit_ι_app
- \- *lemma* limit_X_hom
- \- *lemma* limit_π_app
- \+/\- *def* to_cocone
- \+/\- *def* to_cone
- \+/\- *def* colimit
- \+/\- *def* limit

Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/algebra.lean
- \- *lemma* id_f
- \- *lemma* comp_f
- \- *lemma* forget_map
- \- *lemma* free_obj_a
- \- *lemma* free_map_f
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* forget
- \+/\- *def* free

Modified src/category_theory/monad/limits.lean
- \- *lemma* γ_app
- \- *lemma* c_π
- \- *lemma* cone_point_a
- \+/\- *def* γ
- \+/\- *def* c
- \+/\- *def* cone_point

Modified src/category_theory/monoidal/functor.lean
- \- *lemma* id_obj
- \- *lemma* id_map
- \- *lemma* id_ε
- \- *lemma* id_μ
- \- *lemma* comp_obj
- \- *lemma* comp_map
- \- *lemma* comp_ε
- \- *lemma* comp_μ
- \+/\- *def* id
- \+/\- *def* comp

Modified src/category_theory/whiskering.lean
- \- *lemma* left_unitor_hom_app
- \- *lemma* left_unitor_inv_app
- \- *lemma* right_unitor_hom_app
- \- *lemma* right_unitor_inv_app
- \- *lemma* associator_hom_app
- \- *lemma* associator_inv_app
- \+/\- *def* left_unitor
- \+/\- *def* right_unitor
- \+/\- *def* associator

Modified src/category_theory/yoneda.lean
- \- *lemma* obj_obj
- \- *lemma* obj_map
- \- *lemma* map_app
- \+/\- *def* yoneda
- \+/\- *def* coyoneda



## [2019-10-18 03:27:47](https://github.com/leanprover-community/mathlib/commit/a1c0ad5)
feat(category_theory): def `is_isomorphic_setoid`, `groupoid.iso_equiv_hom` ([#1506](https://github.com/leanprover-community/mathlib/pull/1506))
* feat(category_theory): def `is_isomorphic_setoid`, `groupoid.iso_equiv_hom`
* Move to a dedicated file, define `isomorphic_class_functor`
* explicit/implicit arguments
* Update src/category_theory/groupoid.lean
* Update src/category_theory/groupoid.lean
* Update src/category_theory/isomorphism_classes.lean
* Update src/category_theory/isomorphism_classes.lean
* Update src/category_theory/isomorphism_classes.lean
#### Estimated changes
Modified src/category_theory/groupoid.lean
- \+ *def* groupoid.iso_equiv_hom

Created src/category_theory/isomorphism_classes.lean
- \+ *lemma* groupoid.is_isomorphic_iff_nonempty_hom
- \+ *def* is_isomorphic
- \+ *def* is_isomorphic_setoid
- \+ *def* isomorphism_classes



## [2019-10-17 20:03:17](https://github.com/leanprover-community/mathlib/commit/e5fc2a7)
refactor(topology,calculus): change subset condition for composition ([#1549](https://github.com/leanprover-community/mathlib/pull/1549))
* refactor(topology,calculus): change subset condition for composition
* improve docstrings
* add is_open Ioi
* reviewer's comments
* typo
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* differentiable_within_at_inter'
- \+ *lemma* differentiable_within_at.congr
- \+ *lemma* differentiable_on.congr
- \+ *lemma* has_fderiv_within_at.image_tangent_cone_subset
- \+ *lemma* has_fderiv_within_at.unique_diff_within_at
- \+ *theorem* has_fderiv_within_at.lim
- \+/\- *theorem* has_fderiv_within_at.comp

Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *lemma* unique_diff_within_at.mono
- \+ *lemma* unique_diff_within_at_inter'
- \+ *lemma* unique_diff_within_at.inter'
- \+ *lemma* unique_diff_on.inter
- \- *lemma* unique_diff_on_inter

Modified src/analysis/calculus/times_cont_diff.lean


Modified src/data/equiv/local_equiv.lean


Modified src/data/set/basic.lean
- \+ *lemma* prod_subset_preimage_fst
- \+ *lemma* prod_subset_preimage_snd
- \+ *theorem* subset_preimage_univ
- \+ *theorem* prod_range_univ_eq
- \+ *theorem* prod_univ_range_eq

Modified src/geometry/manifold/manifold.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* is_open_Ioi

Modified src/topology/continuous_on.lean
- \+ *lemma* mem_nhds_within_of_mem_nhds
- \+ *lemma* mem_closure_iff_nhds_within_ne_bot
- \+ *lemma* continuous_within_at.mem_closure_image
- \+ *lemma* continuous_on.congr
- \+ *lemma* continuous_within_at.preimage_mem_nhds_within'
- \+ *lemma* continuous_within_at.congr

Modified src/topology/local_homeomorph.lean
- \+ *lemma* continuous_at_to_fun
- \+ *lemma* continuous_at_inv_fun
- \+ *lemma* image_open_of_open
- \+ *lemma* continuous_within_at_iff_continuous_within_at_comp_right
- \+ *lemma* continuous_at_iff_continuous_at_comp_right
- \+ *lemma* continuous_within_at_iff_continuous_within_at_comp_left
- \+ *lemma* continuous_at_iff_continuous_at_comp_left
- \+/\- *lemma* continuous_on_iff_continuous_on_comp_left
- \+ *lemma* to_homeomorph_to_fun
- \+ *lemma* to_homeomorph_inv_fun
- \+ *def* to_homeomorph_of_source_eq_univ_target_eq_univ



## [2019-10-17 21:46:14+02:00](https://github.com/leanprover-community/mathlib/commit/cc19e30)
docs(project): change example project [ci skip]
#### Estimated changes
Modified docs/install/project.md




## [2019-10-17 07:58:42](https://github.com/leanprover-community/mathlib/commit/905beb0)
fix(topology/metric_space): fix uniform structure on Pi types ([#1551](https://github.com/leanprover-community/mathlib/pull/1551))
* fix(topology/metric_space): fix uniform structure on pi tpype
* cleanup
* better construction of metric from emetric
* use simp only instead of simp
#### Estimated changes
Modified src/data/finset.lean
- \+/\- *lemma* sup_le_iff
- \+ *lemma* sup_lt_iff
- \- *lemma* sup_lt

Modified src/order/filter/basic.lean
- \+ *lemma* Inter_mem_sets_of_fintype
- \+ *lemma* infi_principal_finset
- \+ *lemma* infi_principal_fintype

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* dist_pi_def
- \+ *def* emetric_space.to_metric_space_of_dist
- \+/\- *def* emetric_space.to_metric_space

Modified src/topology/metric_space/emetric_space.lean




## [2019-10-16 21:40:58](https://github.com/leanprover-community/mathlib/commit/ee863ec)
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
#### Estimated changes
Modified src/data/polynomial.lean
- \+/\- *lemma* map_C
- \+/\- *lemma* map_X
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_add
- \+/\- *lemma* map_one
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_pow
- \+/\- *lemma* coeff_map
- \+/\- *lemma* map_map
- \+/\- *lemma* eval₂_map
- \+/\- *lemma* eval_map
- \+/\- *lemma* map_id
- \+ *lemma* mem_map_range
- \+/\- *lemma* hom_eval₂
- \+ *lemma* monic.ne_zero_of_zero_ne_one
- \+ *lemma* monic.ne_zero
- \+/\- *lemma* degree_map_eq_of_injective
- \+/\- *lemma* degree_map'
- \+/\- *lemma* nat_degree_map'
- \+ *lemma* map_injective
- \+ *lemma* leading_coeff_of_injective
- \+ *lemma* monic_of_injective
- \+/\- *def* map

Modified src/field_theory/minimal_polynomial.lean


Created src/ring_theory/algebraic.lean
- \+ *lemma* algebra.is_algebraic_iff
- \+ *lemma* is_integral.is_algebraic
- \+ *lemma* is_algebraic_iff_is_integral
- \+ *lemma* is_algebraic_trans
- \+ *def* is_algebraic
- \+ *def* subalgebra.is_algebraic
- \+ *def* algebra.is_algebraic
- \+ *def* subalgebra.is_algebraic_iff

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral_trans_aux
- \+ *lemma* is_integral_trans
- \+ *lemma* algebra.is_integral_trans
- \+/\- *theorem* is_integral_of_noetherian
- \+/\- *theorem* is_integral_of_mem_of_fg



## [2019-10-16 18:45:00](https://github.com/leanprover-community/mathlib/commit/cbf81df)
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
#### Estimated changes
Created archive/imo1988_q6.lean
- \+ *lemma* constant_descent_vieta_jumping
- \+ *lemma* imo1988_q6



## [2019-10-16 17:05:22](https://github.com/leanprover-community/mathlib/commit/ad8387c)
feat(field_theory/finite): cardinality of images of polynomials ([#1554](https://github.com/leanprover-community/mathlib/pull/1554))
* feat(field_theory/finite): cardinality of images of polynomials
* docstrings
* Johan's suggestions
* slightly shorten proof
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *theorem* card_eq_sum_card_image
- \+ *theorem* card_le_mul_card_image

Modified src/data/polynomial.lean
- \+ *lemma* degree_add_C
- \+ *lemma* nat_degree_neg
- \+ *lemma* card_roots_sub_C
- \+ *lemma* card_roots_sub_C'
- \+ *lemma* mem_roots_sub_C

Modified src/field_theory/finite.lean
- \+ *lemma* card_image_polynomial_eval
- \+ *lemma* exists_root_sum_quadratic



## [2019-10-16 03:46:48](https://github.com/leanprover-community/mathlib/commit/09fd631)
feat(data/zmod/basic): val_min_abs ([#1548](https://github.com/leanprover-community/mathlib/pull/1548))
* feat(data/zmod/basic): val_min_abs
* Update basic.lean
* docstring and fix `zmodp` versions
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* coe_val_min_abs
- \+ *lemma* nat_abs_val_min_abs_le
- \+ *lemma* val_min_abs_zero
- \+ *lemma* val_min_abs_eq_zero
- \+ *def* val_min_abs



## [2019-10-14 12:13:21](https://github.com/leanprover-community/mathlib/commit/c3d1bd7)
feat(data/polynomial): card_roots' ([#1546](https://github.com/leanprover-community/mathlib/pull/1546))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* card_roots'



## [2019-10-13 12:52:09](https://github.com/leanprover-community/mathlib/commit/0ee1272)
fix(doc/contribute): fix broken link ([#1547](https://github.com/leanprover-community/mathlib/pull/1547))
#### Estimated changes
Modified docs/contribute/doc.md




## [2019-10-13 09:57:58](https://github.com/leanprover-community/mathlib/commit/d716648)
docs(topology): some more module docstrings ([#1544](https://github.com/leanprover-community/mathlib/pull/1544))
#### Estimated changes
Modified src/topology/constructions.lean


Modified src/topology/maps.lean


Modified src/topology/order.lean




## [2019-10-13 08:08:28](https://github.com/leanprover-community/mathlib/commit/d10fd1e)
feat(data/int/basic): int.nat_abs_eq_zero ([#1545](https://github.com/leanprover-community/mathlib/pull/1545))
* feat(data/int/basic): int.nat_abs_eq_zero
* Update basic.lean
* Update basic.lean
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* nat_abs_eq_zero



## [2019-10-12 20:07:23](https://github.com/leanprover-community/mathlib/commit/646c035)
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
#### Estimated changes
Modified docs/theories.md


Renamed docs/theories/topological_spaces.md to docs/theories/topology.md


Modified src/topology/algebra/group.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean


Modified src/topology/compact_open.lean


Modified src/topology/constructions.lean
- \+ *lemma* quotient_dense_of_dense
- \+/\- *lemma* is_open_prod_iff'
- \+ *lemma* inducing.prod_mk
- \+ *lemma* embedding.prod_mk
- \+/\- *lemma* embedding_graph
- \+ *lemma* subtype_val.open_embedding
- \+ *lemma* subtype_val.closed_embedding
- \- *lemma* dense_range_prod
- \- *lemma* nhds_contain_boxes.symm
- \- *lemma* nhds_contain_boxes.comm
- \- *lemma* nhds_contain_boxes_of_singleton
- \- *lemma* nhds_contain_boxes_of_compact
- \- *lemma* generalized_tube_lemma
- \- *lemma* is_closed_diagonal
- \- *lemma* is_closed_eq
- \- *lemma* diagonal_eq_range_diagonal_map
- \- *lemma* prod_subset_compl_diagonal_iff_disjoint
- \- *lemma* compact_compact_separated
- \- *lemma* closed_of_compact
- \- *lemma* locally_compact_of_compact_nhds
- \- *lemma* normal_of_compact_t2
- \- *lemma* compact_prod
- \- *lemma* compact_iff_compact_image_of_embedding
- \- *lemma* compact_iff_compact_in_subtype
- \- *lemma* compact_iff_compact_univ
- \- *lemma* compact_iff_compact_space
- \- *lemma* compact_pi_infinite
- \- *lemma* is_closed_property
- \- *lemma* is_closed_property2
- \- *lemma* is_closed_property3
- \- *lemma* coe_eq_to_equiv
- \- *lemma* symm_comp_self
- \- *lemma* self_comp_symm
- \- *lemma* range_coe
- \- *lemma* image_symm
- \- *lemma* preimage_symm
- \- *lemma* induced_eq
- \- *lemma* coinduced_eq
- \- *lemma* compact_image
- \- *lemma* compact_preimage
- \+ *theorem* mem_nhds_subtype
- \+ *theorem* nhds_subtype
- \- *def* nhds_contain_boxes
- \- *def* subtype_emb
- \- *def* homeomorph_of_continuous_open
- \- *def* prod_congr
- \- *def* prod_comm
- \- *def* prod_assoc
- \- *def* sigma_prod_distrib

Modified src/topology/dense_embedding.lean
- \+ *lemma* dense_range_prod
- \+ *lemma* is_closed_property
- \+ *lemma* is_closed_property2
- \+ *lemma* is_closed_property3
- \+ *def* subtype_emb

Created src/topology/homeomorph.lean
- \+ *lemma* coe_eq_to_equiv
- \+ *lemma* symm_comp_self
- \+ *lemma* self_comp_symm
- \+ *lemma* range_coe
- \+ *lemma* image_symm
- \+ *lemma* preimage_symm
- \+ *lemma* induced_eq
- \+ *lemma* coinduced_eq
- \+ *lemma* compact_image
- \+ *lemma* compact_preimage
- \+ *def* homeomorph_of_continuous_open
- \+ *def* prod_congr
- \+ *def* prod_comm
- \+ *def* prod_assoc
- \+ *def* sigma_prod_distrib

Modified src/topology/local_homeomorph.lean


Modified src/topology/maps.lean
- \- *lemma* inducing.prod_mk
- \- *lemma* embedding.prod_mk
- \- *lemma* subtype_val.open_embedding
- \- *lemma* subtype_val.closed_embedding

Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/opens.lean


Modified src/topology/order.lean
- \- *lemma* quotient_dense_of_dense
- \- *theorem* mem_nhds_subtype
- \- *theorem* nhds_subtype

Modified src/topology/separation.lean
- \+ *lemma* is_closed_diagonal
- \+ *lemma* is_closed_eq
- \+ *lemma* diagonal_eq_range_diagonal_map
- \+ *lemma* prod_subset_compl_diagonal_iff_disjoint
- \+ *lemma* compact_compact_separated
- \+ *lemma* closed_of_compact
- \+ *lemma* locally_compact_of_compact_nhds
- \+ *lemma* normal_of_compact_t2

Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean
- \+ *lemma* nhds_contain_boxes.symm
- \+ *lemma* nhds_contain_boxes.comm
- \+ *lemma* nhds_contain_boxes_of_singleton
- \+ *lemma* nhds_contain_boxes_of_compact
- \+ *lemma* generalized_tube_lemma
- \+/\- *lemma* compact_image
- \+/\- *lemma* compact_range
- \+ *lemma* compact_iff_compact_image_of_embedding
- \+ *lemma* compact_iff_compact_in_subtype
- \+ *lemma* compact_iff_compact_univ
- \+ *lemma* compact_iff_compact_space
- \+ *lemma* compact_prod
- \+ *lemma* compact_pi_infinite
- \+ *def* nhds_contain_boxes

Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/complete_separated.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2019-10-12 18:21:51](https://github.com/leanprover-community/mathlib/commit/92a9a78)
fix(topology/continuous_on): avoid duplicate instance arguments ([#1542](https://github.com/leanprover-community/mathlib/pull/1542))
This was broken by [#1516](https://github.com/leanprover-community/mathlib/pull/1516), caught by sanity_check.
#### Estimated changes
Modified src/topology/continuous_on.lean




## [2019-10-12 18:05:26](https://github.com/leanprover-community/mathlib/commit/995add3)
fix(topology/algebra/group_completion): remove redundant instance parameters ([#1543](https://github.com/leanprover-community/mathlib/pull/1543))
#### Estimated changes
Modified src/topology/algebra/group_completion.lean
- \+/\- *lemma* is_add_group_hom_map



## [2019-10-12 16:02:53+02:00](https://github.com/leanprover-community/mathlib/commit/76090be)
chore(docs/install/debian): Remove old sentence [ci skip]
#### Estimated changes
Modified docs/install/debian.md




## [2019-10-12 10:28:08](https://github.com/leanprover-community/mathlib/commit/2751561)
minor updates to the installation instructions ([#1538](https://github.com/leanprover-community/mathlib/pull/1538))
#### Estimated changes
Modified docs/install/linux.md


Modified docs/install/macos.md


Modified docs/install/windows.md




## [2019-10-11 17:54:17](https://github.com/leanprover-community/mathlib/commit/d5de803)
refactor(ring_theory/algebra): alg_hom extends ring_hom and use curly brackets ([#1529](https://github.com/leanprover-community/mathlib/pull/1529))
* chore(algebra/ring): use curly brackets for ring_hom where possible
* refactor(ring_theory/algebra): alg_hom extends ring_hom and use curly brackets
* fix build
* Update src/ring_theory/algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* fix build
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *lemma* id_apply
- \+ *lemma* comp_apply

Modified src/ring_theory/algebra.lean
- \+/\- *def* comp



## [2019-10-11 13:15:04](https://github.com/leanprover-community/mathlib/commit/6b7377a)
chore(algebra/ring): use curly brackets for ring_hom where possible ([#1525](https://github.com/leanprover-community/mathlib/pull/1525))
* chore(algebra/ring): use curly brackets for ring_hom where possible
* add comments explaining motivation
* move explanation to header
* fix build
* Update src/algebra/ring.lean
* scott's suggestion
#### Estimated changes
Modified src/algebra/ring.lean
- \+/\- *lemma* coe_monoid_hom
- \+/\- *lemma* coe_add_monoid_hom



## [2019-10-11 11:48:51](https://github.com/leanprover-community/mathlib/commit/38a0ffe)
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
#### Estimated changes
Modified src/ring_theory/algebra.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/integral_closure.lean




## [2019-10-11 11:26:29](https://github.com/leanprover-community/mathlib/commit/338146b)
fix(algebra/char_p): typo in docstring ([#1537](https://github.com/leanprover-community/mathlib/pull/1537))
I don't know anything about semirings but I do know there isn't a homomorphism from int to them in general. Do people talk about kernels? (this would be some semi-ideal or something). My change is probably better than what we had but someone who knows what a semiring is might want to check that my suggestion makes sense.
#### Estimated changes
Modified src/algebra/char_p.lean




## [2019-10-11 03:41:02](https://github.com/leanprover-community/mathlib/commit/eb230d3)
chore(algebra/group/hom): use curly brackets for instances where possible ([#1524](https://github.com/leanprover-community/mathlib/pull/1524))
* chore(algebra/group/hom): use curly brackets for instances where possible
* add comments mentioning motivation behind brackets
* move explanation to header
* fix build
* Update src/algebra/group/hom.lean
#### Estimated changes
Modified src/algebra/group/hom.lean




## [2019-10-11 01:59:31](https://github.com/leanprover-community/mathlib/commit/364c26e)
chore(algebra/module): use curly brackets instead of square brackets in more places ([#1523](https://github.com/leanprover-community/mathlib/pull/1523))
* chore(algebra/module): use curly brackets instead of square brackets in more places
* Add explanation behind implicit brackets
* Update src/algebra/module.lean
#### Estimated changes
Modified src/algebra/module.lean




## [2019-10-10 11:14:36](https://github.com/leanprover-community/mathlib/commit/43d3dee)
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
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *lemma* smul_sum
- \+/\- *lemma* comp_cod_restrict
- \+/\- *lemma* subtype_comp_cod_restrict
- \+/\- *lemma* zero_apply
- \+/\- *lemma* neg_apply
- \+/\- *lemma* add_apply
- \+/\- *lemma* sum_apply
- \+/\- *lemma* sub_apply
- \+/\- *lemma* one_app
- \+/\- *lemma* mul_app
- \+/\- *lemma* smul_apply
- \+/\- *lemma* le_def
- \+/\- *lemma* le_def'
- \+/\- *lemma* subtype_comp_of_le
- \+/\- *lemma* bot_coe
- \+/\- *lemma* mem_bot
- \+/\- *lemma* top_coe
- \+/\- *lemma* mem_top
- \+/\- *lemma* eq_bot_of_zero_eq_one
- \+/\- *lemma* add_eq_sup
- \+/\- *lemma* zero_eq_bot
- \+/\- *lemma* eq_top_iff'
- \+/\- *lemma* map_coe
- \+/\- *lemma* mem_map
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_mono
- \+/\- *lemma* map_zero
- \+/\- *lemma* comap_coe
- \+/\- *lemma* mem_comap
- \+/\- *lemma* comap_comp
- \+/\- *lemma* comap_mono
- \+/\- *lemma* map_le_iff_le_comap
- \+/\- *lemma* gc_map_comap
- \+/\- *lemma* map_bot
- \+/\- *lemma* map_sup
- \+/\- *lemma* map_supr
- \+/\- *lemma* comap_top
- \+/\- *lemma* comap_inf
- \+/\- *lemma* comap_infi
- \+/\- *lemma* comap_zero
- \+/\- *lemma* map_comap_le
- \+/\- *lemma* le_comap_map
- \+/\- *lemma* map_inf_eq_map_inf_comap
- \+/\- *lemma* eq_zero_of_bot_submodule
- \+/\- *lemma* mem_span
- \+/\- *lemma* subset_span
- \+/\- *lemma* span_le
- \+/\- *lemma* span_mono
- \+/\- *lemma* span_eq_of_le
- \+/\- *lemma* span_eq
- \+/\- *lemma* span_induction
- \+/\- *lemma* span_empty
- \+/\- *lemma* span_univ
- \+/\- *lemma* span_union
- \+/\- *lemma* span_Union
- \+/\- *lemma* mem_supr_of_mem
- \+/\- *lemma* mem_span_singleton
- \+/\- *lemma* span_singleton_eq_range
- \+/\- *lemma* mem_span_insert
- \+/\- *lemma* mem_span_insert'
- \+/\- *lemma* span_insert_eq_span
- \+/\- *lemma* span_span
- \+/\- *lemma* span_eq_bot
- \+/\- *lemma* span_singleton_eq_bot
- \+/\- *lemma* span_image
- \+/\- *lemma* linear_eq_on
- \+/\- *lemma* mem_prod
- \+/\- *lemma* span_prod_le
- \+/\- *lemma* prod_top
- \+/\- *lemma* prod_bot
- \+/\- *lemma* prod_mono
- \+/\- *lemma* comap_smul
- \+/\- *lemma* map_smul
- \+/\- *lemma* comap_smul'
- \+/\- *lemma* map_smul'
- \+/\- *lemma* finsupp_sum
- \+/\- *lemma* range_le_iff_comap
- \+/\- *lemma* map_le_range
- \+/\- *lemma* disjoint_inl_inr
- \+/\- *lemma* le_ker_iff_map
- \+/\- *lemma* ker_cod_restrict
- \+/\- *lemma* range_cod_restrict
- \+/\- *lemma* map_comap_eq
- \+/\- *lemma* map_comap_eq_self
- \+/\- *lemma* comap_map_eq
- \+/\- *lemma* comap_map_eq_self
- \+/\- *lemma* range_le_bot_iff
- \+/\- *lemma* span_inl_union_inr
- \+/\- *lemma* ker_pair
- \+/\- *lemma* ker_smul
- \+/\- *lemma* ker_smul'
- \+/\- *lemma* range_smul
- \+/\- *lemma* range_smul'
- \+/\- *lemma* is_linear_map_add
- \+/\- *lemma* is_linear_map_sub
- \+/\- *lemma* map_subtype_le
- \+/\- *lemma* range_of_le
- \+/\- *lemma* disjoint_iff_comap_eq_bot
- \+/\- *lemma* map_subtype_embedding_eq
- \+/\- *lemma* le_comap_mkq
- \+/\- *lemma* comap_mkq_embedding_eq
- \+/\- *lemma* to_equiv_injective
- \+/\- *lemma* ext
- \+/\- *lemma* eq_bot_of_equiv
- \+/\- *lemma* is_linear_map_prod_iso
- \+/\- *lemma* pi_apply
- \+/\- *lemma* ker_pi
- \+/\- *lemma* pi_eq_zero
- \+/\- *lemma* pi_zero
- \+/\- *lemma* pi_comp
- \+/\- *lemma* proj_apply
- \+/\- *lemma* proj_pi
- \+/\- *lemma* infi_ker_proj
- \+/\- *lemma* update_apply
- \+/\- *lemma* std_basis_apply
- \+/\- *lemma* std_basis_same
- \+/\- *lemma* std_basis_ne
- \+/\- *lemma* ker_std_basis
- \+/\- *lemma* proj_comp_std_basis
- \+/\- *lemma* proj_std_basis_same
- \+/\- *lemma* proj_std_basis_ne
- \+/\- *lemma* supr_range_std_basis
- \+/\- *lemma* std_basis_eq_single
- \+/\- *lemma* general_linear_equiv_to_linear_map
- \+/\- *theorem* comp_assoc
- \+/\- *theorem* cod_restrict_apply
- \+/\- *theorem* smul_right_apply
- \+/\- *theorem* comp_zero
- \+/\- *theorem* zero_comp
- \+/\- *theorem* fst_apply
- \+/\- *theorem* snd_apply
- \+/\- *theorem* pair_apply
- \+/\- *theorem* fst_pair
- \+/\- *theorem* snd_pair
- \+/\- *theorem* pair_fst_snd
- \+/\- *theorem* inl_apply
- \+/\- *theorem* inr_apply
- \+/\- *theorem* copair_apply
- \+/\- *theorem* copair_inl
- \+/\- *theorem* copair_inr
- \+/\- *theorem* copair_inl_inr
- \+/\- *theorem* fst_eq_copair
- \+/\- *theorem* snd_eq_copair
- \+/\- *theorem* inl_eq_pair
- \+/\- *theorem* inr_eq_pair
- \+/\- *theorem* smul_comp
- \+/\- *theorem* comp_smul
- \+/\- *theorem* of_le_apply
- \+/\- *theorem* inf_coe
- \+/\- *theorem* mem_inf
- \+/\- *theorem* Inf_coe
- \+/\- *theorem* infi_coe
- \+/\- *theorem* mem_infi
- \+/\- *theorem* disjoint_def
- \+/\- *theorem* mem_map_of_mem
- \+/\- *theorem* mem_Sup_of_directed
- \+/\- *theorem* mk_eq_mk
- \+/\- *theorem* mk'_eq_mk
- \+/\- *theorem* quot_mk_eq_mk
- \+/\- *theorem* map_cod_restrict
- \+/\- *theorem* comap_cod_restrict
- \+/\- *theorem* range_coe
- \+/\- *theorem* mem_range
- \+/\- *theorem* range_id
- \+/\- *theorem* range_comp
- \+/\- *theorem* range_comp_le_range
- \+/\- *theorem* range_eq_top
- \+/\- *theorem* mem_ker
- \+/\- *theorem* ker_id
- \+/\- *theorem* ker_comp
- \+/\- *theorem* ker_le_ker_comp
- \+/\- *theorem* sub_mem_ker_iff
- \+/\- *theorem* disjoint_ker
- \+/\- *theorem* disjoint_ker'
- \+/\- *theorem* inj_of_disjoint_ker
- \+/\- *theorem* ker_eq_bot
- \+/\- *theorem* ker_eq_bot'
- \+/\- *theorem* ker_zero
- \+/\- *theorem* range_zero
- \+/\- *theorem* ker_eq_top
- \+/\- *theorem* map_le_map_iff
- \+/\- *theorem* map_injective
- \+/\- *theorem* comap_le_comap_iff
- \+/\- *theorem* comap_injective
- \+/\- *theorem* map_copair_prod
- \+/\- *theorem* comap_pair_prod
- \+/\- *theorem* prod_eq_inf_comap
- \+/\- *theorem* prod_eq_sup_map
- \+/\- *theorem* map_top
- \+/\- *theorem* comap_bot
- \+/\- *theorem* ker_of_le
- \+/\- *theorem* map_inl
- \+/\- *theorem* map_inr
- \+/\- *theorem* comap_fst
- \+/\- *theorem* comap_snd
- \+/\- *theorem* prod_comap_inl
- \+/\- *theorem* prod_comap_inr
- \+/\- *theorem* prod_map_fst
- \+/\- *theorem* prod_map_snd
- \+/\- *theorem* ker_inl
- \+/\- *theorem* ker_inr
- \+/\- *theorem* range_fst
- \+/\- *theorem* range_snd
- \+/\- *theorem* mkq_apply
- \+/\- *theorem* liftq_apply
- \+/\- *theorem* liftq_mkq
- \+/\- *theorem* mapq_apply
- \+/\- *theorem* mapq_mkq
- \+/\- *theorem* comap_liftq
- \+/\- *theorem* map_liftq
- \+/\- *theorem* ker_liftq
- \+/\- *theorem* range_liftq
- \+/\- *theorem* ker_liftq_eq_bot
- \+/\- *theorem* coe_apply
- \+/\- *theorem* apply_symm_apply
- \+/\- *theorem* symm_apply_apply
- \+/\- *theorem* of_bijective_apply
- \+/\- *theorem* of_linear_apply
- \+/\- *theorem* of_linear_symm_apply
- \+/\- *theorem* of_top_apply
- \+/\- *theorem* of_top_symm_apply
- \+/\- *def* cod_restrict
- \+/\- *def* inverse
- \+/\- *def* smul_right
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* pair
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* copair
- \+/\- *def* congr_right
- \+/\- *def* of_le
- \+/\- *def* map
- \+/\- *def* comap
- \+/\- *def* span
- \+/\- *def* prod
- \+/\- *def* quotient_rel
- \+/\- *def* mk
- \+/\- *def* range
- \+/\- *def* ker
- \+/\- *def* mkq
- \+/\- *def* liftq
- \+/\- *def* mapq
- \+/\- *def* refl
- \+/\- *def* symm
- \+/\- *def* trans
- \+/\- *def* of_linear
- \+/\- *def* of_top
- \+/\- *def* smul_of_unit
- \+/\- *def* arrow_congr
- \+/\- *def* conj
- \+/\- *def* smul_of_ne_zero
- \+/\- *def* to_linear_equiv
- \+/\- *def* sup_quotient_to_quotient_inf
- \+/\- *def* scalar_prod_space_iso
- \+/\- *def* pi
- \+/\- *def* proj
- \+/\- *def* diag
- \+/\- *def* std_basis
- \+/\- *def* general_linear_group
- \+/\- *def* of_linear_equiv
- \+/\- *def* general_linear_equiv

Modified src/linear_algebra/basis.lean
- \+/\- *lemma* linear_independent_empty_type
- \+/\- *lemma* linear_independent_of_zero_eq_one
- \+/\- *lemma* linear_independent.unique
- \+/\- *lemma* linear_independent.injective
- \+/\- *lemma* linear_independent_span
- \+/\- *lemma* linear_independent_empty
- \+/\- *lemma* linear_independent.mono
- \+/\- *lemma* linear_independent_union
- \+/\- *lemma* linear_independent_of_finite
- \+/\- *lemma* linear_independent_sUnion_of_directed
- \+/\- *lemma* linear_independent_bUnion_of_directed
- \+/\- *lemma* linear_independent_Union_finite_subtype
- \+/\- *lemma* linear_independent.total_repr
- \+/\- *lemma* linear_independent.total_comp_repr
- \+/\- *lemma* eq_of_linear_independent_of_span_subtype
- \+/\- *lemma* linear_independent.image
- \+/\- *lemma* linear_independent.image_subtype
- \+/\- *lemma* linear_independent_inl_union_inr
- \+/\- *lemma* linear_independent_inl_union_inr'
- \+/\- *lemma* le_of_span_le_span
- \+/\- *lemma* span_le_span_iff
- \+/\- *lemma* is_basis.mem_span
- \+/\- *lemma* is_basis.comp
- \+/\- *lemma* is_basis.injective
- \+/\- *lemma* is_basis.total_repr
- \+/\- *lemma* is_basis.total_comp_repr
- \+/\- *lemma* is_basis.repr_range
- \+/\- *lemma* is_basis.repr_total
- \+/\- *lemma* is_basis.ext
- \+/\- *lemma* constr_basis
- \+/\- *lemma* constr_eq
- \+/\- *lemma* constr_self
- \+/\- *lemma* constr_zero
- \+/\- *lemma* constr_add
- \+/\- *lemma* constr_neg
- \+/\- *lemma* constr_sub
- \+/\- *lemma* constr_smul
- \+/\- *lemma* constr_range
- \+/\- *lemma* is_basis_inl_union_inr
- \+/\- *lemma* is_basis_singleton_one
- \+/\- *lemma* linear_equiv.is_basis
- \+/\- *lemma* is_basis_span
- \+/\- *lemma* is_basis_empty
- \+/\- *lemma* is_basis_empty_bot
- \+/\- *lemma* mem_span_insert_exchange
- \+/\- *lemma* linear_independent_iff_not_mem_span
- \+/\- *lemma* linear_independent_unique
- \+/\- *lemma* linear_independent_singleton
- \+/\- *lemma* disjoint_span_singleton
- \+/\- *lemma* linear_independent.insert
- \+/\- *lemma* exists_linear_independent
- \+/\- *lemma* exists_subset_is_basis
- \+/\- *lemma* exists_is_basis
- \+/\- *lemma* exists_of_linear_independent_of_finite_span
- \+/\- *lemma* exists_left_inverse_linear_map_of_injective
- \+/\- *lemma* exists_right_inverse_linear_map_of_surjective
- \+/\- *lemma* is_basis_std_basis
- \+/\- *lemma* is_basis_fun₀
- \+/\- *lemma* is_basis_fun
- \+/\- *theorem* linear_independent_iff
- \+/\- *theorem* linear_independent_subtype
- \+/\- *theorem* linear_independent_subtype_disjoint
- \+/\- *theorem* linear_independent_iff_total_on
- \+/\- *theorem* is_basis.constr_apply
- \+/\- *theorem* module.card_fintype
- \+/\- *theorem* quotient_prod_linear_equiv
- \+/\- *theorem* vector_space.card_fintype
- \+/\- *def* linear_independent
- \+/\- *def* linear_independent.total_equiv
- \+/\- *def* linear_independent.repr
- \+/\- *def* is_basis
- \+/\- *def* is_basis.repr
- \+/\- *def* is_basis.constr
- \+/\- *def* module_equiv_finsupp
- \+/\- *def* equiv_of_is_basis
- \+/\- *def* equiv_fun_basis

Modified src/linear_algebra/bilinear_form.lean
- \+/\- *lemma* add_left
- \+/\- *lemma* smul_left
- \+/\- *lemma* add_right
- \+/\- *lemma* smul_right
- \+/\- *lemma* zero_left
- \+/\- *lemma* zero_right
- \+/\- *lemma* neg_left
- \+/\- *lemma* neg_right
- \+/\- *lemma* sub_left
- \+/\- *lemma* sub_right
- \+/\- *lemma* ext
- \+/\- *lemma* ortho_zero
- \+/\- *lemma* eq_zero
- \+/\- *lemma* ortho_sym
- \+/\- *lemma* sym
- \+/\- *lemma* self_eq_zero
- \+/\- *lemma* neg
- \+/\- *theorem* ortho_smul_left
- \+/\- *theorem* ortho_smul_right
- \+/\- *def* linear_map.to_bilin
- \+/\- *def* to_linear_map
- \+/\- *def* bilin_linear_map_equiv
- \+/\- *def* is_ortho
- \+/\- *def* is_refl
- \+/\- *def* is_sym
- \+/\- *def* is_alt

Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_bot
- \+/\- *lemma* dim_top
- \+/\- *lemma* dim_of_field
- \+/\- *lemma* dim_span
- \+/\- *lemma* dim_span_set
- \+/\- *lemma* dim_span_le
- \+/\- *lemma* dim_span_of_finset
- \+/\- *lemma* dim_range_le
- \+/\- *lemma* dim_map_le
- \+/\- *lemma* dim_range_of_surjective
- \+/\- *lemma* dim_eq_surjective
- \+/\- *lemma* dim_le_surjective
- \+/\- *lemma* dim_eq_injective
- \+/\- *lemma* dim_submodule_le
- \+/\- *lemma* dim_le_injective
- \+/\- *lemma* dim_le_of_submodule
- \+/\- *lemma* dim_sup_add_dim_inf_eq
- \+/\- *lemma* dim_add_le_dim_add_dim
- \+/\- *lemma* dim_pi
- \+/\- *lemma* dim_fun
- \+/\- *lemma* dim_fun'
- \+/\- *lemma* dim_fin_fun
- \+/\- *lemma* exists_mem_ne_zero_of_ne_bot
- \+/\- *lemma* exists_mem_ne_zero_of_dim_pos
- \+/\- *lemma* exists_is_basis_fintype
- \+/\- *lemma* rank_le_domain
- \+/\- *lemma* rank_le_range
- \+/\- *lemma* rank_add_le
- \+/\- *lemma* rank_zero
- \+/\- *lemma* rank_finset_sum_le
- \+/\- *lemma* rank_comp_le1
- \+/\- *lemma* rank_comp_le2
- \+/\- *theorem* is_basis.le_span
- \+/\- *theorem* mk_eq_mk_of_basis
- \+/\- *theorem* is_basis.mk_range_eq_dim
- \+/\- *theorem* is_basis.mk_eq_dim
- \+/\- *theorem* linear_equiv.dim_eq
- \+/\- *theorem* dim_prod
- \+/\- *theorem* dim_quotient
- \+/\- *theorem* dim_range_add_dim_ker
- \+/\- *theorem* linear_equiv.dim_eq_lift
- \+/\- *def* rank

Modified src/linear_algebra/direct_sum_module.lean
- \+/\- *lemma* single_eq_lof
- \+/\- *lemma* to_module_lof
- \+/\- *lemma* lof_apply
- \+/\- *lemma* apply_eq_component
- \+/\- *lemma* component.lof_self
- \+/\- *lemma* component.of
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *theorem* mk_smul
- \+/\- *theorem* of_smul
- \+/\- *theorem* to_module.unique
- \+/\- *theorem* to_module.ext
- \+/\- *def* lmk
- \+/\- *def* lof
- \+/\- *def* to_module
- \+/\- *def* component

Modified src/linear_algebra/finsupp.lean
- \+/\- *lemma* lsubtype_domain_apply
- \+/\- *lemma* lsingle_apply
- \+/\- *lemma* lapply_apply
- \+/\- *lemma* ker_lsingle
- \+/\- *lemma* infi_ker_lapply_le_bot
- \+/\- *lemma* supr_lsingle_range
- \+/\- *lemma* span_single_image
- \+/\- *lemma* mem_supported
- \+/\- *lemma* mem_supported'
- \+/\- *lemma* single_mem_supported
- \+/\- *lemma* supported_eq_span_single
- \+/\- *lemma* range_total
- \+/\- *theorem* restrict_dom_apply
- \+/\- *theorem* supported_empty
- \+/\- *theorem* supported_univ
- \+/\- *theorem* lsum_apply
- \+/\- *theorem* lmap_domain_apply
- \+/\- *theorem* lmap_domain_id
- \+/\- *theorem* total_apply
- \+/\- *theorem* total_single
- \+/\- *theorem* total_range
- \+/\- *theorem* lmap_domain_total
- \+/\- *theorem* total_emb_domain
- \+/\- *theorem* total_map_domain
- \+/\- *theorem* mem_span_iff_total
- \+/\- *theorem* total_on_range
- \+/\- *def* lsingle
- \+/\- *def* lapply
- \+/\- *def* lsubtype_domain
- \+/\- *def* supported
- \+/\- *def* restrict_dom
- \+/\- *def* lsum
- \+/\- *def* lmap_domain

Modified src/linear_algebra/finsupp_vector_space.lean
- \+/\- *lemma* linear_independent_single
- \+/\- *lemma* is_basis_single
- \+/\- *lemma* dim_eq
- \+/\- *lemma* eq_bot_iff_dim_eq_zero
- \+/\- *lemma* injective_of_surjective
- \+/\- *lemma* cardinal_mk_eq_cardinal_mk_field_pow_dim
- \+/\- *lemma* cardinal_lt_omega_of_dim_lt_omega
- \+/\- *def* equiv_of_dim_eq_dim

Modified src/linear_algebra/matrix.lean
- \+/\- *lemma* to_lin_add
- \+/\- *lemma* to_lin_zero
- \+/\- *lemma* to_lin_apply
- \+/\- *lemma* mul_to_lin
- \+/\- *lemma* to_matrix_to_lin
- \+/\- *lemma* to_lin_to_matrix
- \+/\- *lemma* proj_diagonal
- \+/\- *lemma* diagonal_comp_std_basis
- \+/\- *lemma* rank_vec_mul_vec
- \+/\- *lemma* diagonal_to_lin
- \+/\- *lemma* ker_diagonal_to_lin
- \+/\- *lemma* range_diagonal
- \+/\- *lemma* rank_diagonal
- \+/\- *def* eval
- \+/\- *def* to_lin
- \+/\- *def* to_matrixₗ
- \+/\- *def* to_matrix
- \+/\- *def* lin_equiv_matrix'
- \+/\- *def* lin_equiv_matrix

Modified src/linear_algebra/sesquilinear_form.lean
- \+/\- *lemma* add_left
- \+/\- *lemma* smul_left
- \+/\- *lemma* add_right
- \+/\- *lemma* smul_right
- \+/\- *lemma* zero_left
- \+/\- *lemma* zero_right
- \+/\- *lemma* neg_left
- \+/\- *lemma* neg_right
- \+/\- *lemma* sub_left
- \+/\- *lemma* sub_right
- \+/\- *lemma* ext
- \+/\- *lemma* ortho_zero
- \+/\- *lemma* eq_zero
- \+/\- *lemma* ortho_sym
- \+/\- *lemma* sym
- \+/\- *lemma* is_refl
- \+/\- *lemma* self_eq_zero
- \+/\- *lemma* neg
- \+/\- *theorem* ortho_smul_left
- \+/\- *theorem* ortho_smul_right
- \+/\- *def* is_ortho
- \+/\- *def* is_refl
- \+/\- *def* is_sym
- \+/\- *def* is_alt

Modified src/linear_algebra/tensor_product.lean
- \+/\- *def* direct_sum



## [2019-10-10 09:00:38](https://github.com/leanprover-community/mathlib/commit/dc788a0)
feat(topology/sequences): every first-countable space is sequential ([#1528](https://github.com/leanprover-community/mathlib/pull/1528))
* feat(topology/sequences): every first-countable space is sequential
* fixup style
* fixup comments
* remove redundant type ascription
#### Estimated changes
Modified src/data/set/countable.lean
- \+ *lemma* countable_iff_exists_surjective_to_subtype

Modified src/order/basic.lean
- \+ *lemma* directed_of_mono

Modified src/order/complete_lattice.lean
- \+ *lemma* infi_subtype'

Modified src/topology/bases.lean
- \+ *lemma* has_countable_basis_of_seq
- \+ *lemma* seq_of_has_countable_basis
- \+ *lemma* has_countable_basis_iff_seq
- \+ *lemma* mono_seq_of_has_countable_basis
- \+ *lemma* has_countable_basis_iff_mono_seq
- \+ *def* has_countable_basis

Modified src/topology/sequences.lean




## [2019-10-09 19:53:01](https://github.com/leanprover-community/mathlib/commit/7d792ec)
chore(ring_theory/adjoin_root): remove some unused decidable_eq ([#1530](https://github.com/leanprover-community/mathlib/pull/1530))
#### Estimated changes
Modified src/ring_theory/adjoin_root.lean
- \+/\- *def* adjoin_root



## [2019-10-09 16:00:50](https://github.com/leanprover-community/mathlib/commit/a17a9a6)
fix(tactic/{use,ring}): instantiate metavariables in goal ([#1520](https://github.com/leanprover-community/mathlib/pull/1520))
`use` now tidies up the subgoals that it leaves behind after instantiating constructors.
`ring` is sensitive to the presence of such metavariables, and we can't guarantee that it doesn't see any,
so it should check for them before it runs.
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/ring.lean




## [2019-10-09 14:59:54](https://github.com/leanprover-community/mathlib/commit/45633aa)
refactor(topology/algebra/polynomial): move topology.instances.polynomial ([#1527](https://github.com/leanprover-community/mathlib/pull/1527))
#### Estimated changes
Modified src/analysis/complex/polynomial.lean


Modified src/data/padics/hensel.lean


Renamed src/topology/instances/polynomial.lean to src/topology/algebra/polynomial.lean




## [2019-10-09 14:24:19](https://github.com/leanprover-community/mathlib/commit/0ea83c0)
docs(data/holor): some additional documentation ([#1526](https://github.com/leanprover-community/mathlib/pull/1526))
#### Estimated changes
Modified src/data/holor.lean




## [2019-10-09 05:24:44](https://github.com/leanprover-community/mathlib/commit/6ccfe5a)
feat(algebra/ordered...): Two tiny lemmas ([#1522](https://github.com/leanprover-community/mathlib/pull/1522))
* feat(algebra/ordered...): Two tiny lemmas
* style(src/algebra/ordered_field)
Co-Authored-By: Reid Barton <rwbarton@gmail.com>
#### Estimated changes
Modified src/algebra/floor.lean
- \+ *lemma* lt_of_nat_ceil_lt
- \+/\- *theorem* nat_ceil_lt_add_one

Modified src/algebra/ordered_field.lean
- \+ *lemma* one_div_lt



## [2019-10-08 16:33:02](https://github.com/leanprover-community/mathlib/commit/7c56051)
doc(linear_algebra/basis): add doc ([#1503](https://github.com/leanprover-community/mathlib/pull/1503))
* doc(linear_algebra/basis): add doc
* doc(linear_algebra/basis): shorten docstrings
#### Estimated changes
Modified src/linear_algebra/basis.lean




## [2019-10-08 15:54:18](https://github.com/leanprover-community/mathlib/commit/6b15eb2)
chore(analysis): put lemmas in normed_field namespace ([#1517](https://github.com/leanprover-community/mathlib/pull/1517))
The motivation is to be able to state, say norm_mul for subrings of a
normed field, typically p-adic integers. That way we can have
padic_int.norm_mul, open the padic_int namespace and have no ambiguous
name.
#### Estimated changes
Modified src/analysis/asymptotics.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_pow_le
- \+/\- *lemma* norm_int_of_nonneg

Modified src/analysis/normed_space/operator_norm.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean
- \+/\- *lemma* norm_one

Modified src/data/padics/padic_numbers.lean




## [2019-10-08 13:51:59](https://github.com/leanprover-community/mathlib/commit/afda1a2)
refactor(topology/continuous_on): move continuous_{on,within_at} to own file ([#1516](https://github.com/leanprover-community/mathlib/pull/1516))
* refactor(topology/continuous_on): move continuous_{on,within_at} to own file
* Update src/topology/continuous_on.lean
#### Estimated changes
Modified src/topology/algebra/monoid.lean


Modified src/topology/basic.lean
- \+ *lemma* continuous_at.preimage_mem_nhds
- \+ *lemma* continuous_at.comp
- \+ *lemma* continuous.continuous_at
- \- *lemma* map_nhds_within
- \- *theorem* nhds_within_eq
- \- *theorem* nhds_within_univ
- \- *theorem* mem_nhds_within
- \- *theorem* self_mem_nhds_within
- \- *theorem* inter_mem_nhds_within
- \- *theorem* nhds_within_mono
- \- *theorem* nhds_within_restrict''
- \- *theorem* nhds_within_restrict'
- \- *theorem* nhds_within_restrict
- \- *theorem* nhds_within_le_of_mem
- \- *theorem* nhds_within_eq_nhds_within
- \- *theorem* nhds_within_eq_of_open
- \- *theorem* nhds_within_empty
- \- *theorem* nhds_within_union
- \- *theorem* nhds_within_inter
- \- *theorem* nhds_within_inter'
- \- *theorem* tendsto_if_nhds_within
- \- *theorem* tendsto_nhds_within_mono_left
- \- *theorem* tendsto_nhds_within_mono_right
- \- *theorem* tendsto_nhds_within_of_tendsto_nhds
- \- *def* nhds_within
- \- *def* continuous_within_at
- \- *def* continuous_on

Modified src/topology/constructions.lean
- \- *lemma* continuous_within_at.prod
- \- *lemma* continuous_on.prod

Created src/topology/continuous_on.lean
- \+ *lemma* map_nhds_within
- \+ *lemma* continuous_iff_continuous_on_univ
- \+ *lemma* continuous_within_at.mono
- \+ *lemma* continuous_within_at_inter'
- \+ *lemma* continuous_within_at_inter
- \+ *lemma* continuous_on.congr_mono
- \+ *lemma* continuous_at.continuous_within_at
- \+ *lemma* continuous_within_at.continuous_at
- \+ *lemma* continuous_within_at.comp
- \+ *lemma* continuous_on.comp
- \+ *lemma* continuous_on.mono
- \+ *lemma* continuous.continuous_on
- \+ *lemma* continuous.comp_continuous_on
- \+ *lemma* continuous_within_at.preimage_mem_nhds_within
- \+ *lemma* continuous_within_at.congr_of_mem_nhds_within
- \+ *lemma* continuous_on_const
- \+ *lemma* continuous_on_open_iff
- \+ *lemma* continuous_on.preimage_open_of_open
- \+ *lemma* continuous_on.preimage_closed_of_closed
- \+ *lemma* continuous_on.preimage_interior_subset_interior_preimage
- \+ *lemma* continuous_on_of_locally_continuous_on
- \+ *lemma* continuous_on_open_of_generate_from
- \+ *lemma* continuous_within_at.prod
- \+ *lemma* continuous_on.prod
- \+ *theorem* nhds_within_eq
- \+ *theorem* nhds_within_univ
- \+ *theorem* mem_nhds_within
- \+ *theorem* self_mem_nhds_within
- \+ *theorem* inter_mem_nhds_within
- \+ *theorem* nhds_within_mono
- \+ *theorem* nhds_within_restrict''
- \+ *theorem* nhds_within_restrict'
- \+ *theorem* nhds_within_restrict
- \+ *theorem* nhds_within_le_of_mem
- \+ *theorem* nhds_within_eq_nhds_within
- \+ *theorem* nhds_within_eq_of_open
- \+ *theorem* nhds_within_empty
- \+ *theorem* nhds_within_union
- \+ *theorem* nhds_within_inter
- \+ *theorem* nhds_within_inter'
- \+ *theorem* tendsto_if_nhds_within
- \+ *theorem* tendsto_nhds_within_mono_left
- \+ *theorem* tendsto_nhds_within_mono_right
- \+ *theorem* tendsto_nhds_within_of_tendsto_nhds
- \+ *theorem* principal_subtype
- \+ *theorem* mem_nhds_within_subtype
- \+ *theorem* nhds_within_subtype
- \+ *theorem* nhds_within_eq_map_subtype_val
- \+ *theorem* tendsto_nhds_within_iff_subtype
- \+ *theorem* continuous_within_at_univ
- \+ *theorem* continuous_within_at_iff_continuous_at_restrict
- \+ *theorem* continuous_within_at.tendsto_nhds_within_image
- \+ *theorem* continuous_on_iff
- \+ *theorem* continuous_on_iff_continuous_restrict
- \+ *theorem* continuous_on_iff'
- \+ *theorem* continuous_on_iff_is_closed
- \+ *theorem* nhds_within_le_comap
- \+ *theorem* continuous_within_at_iff_ptendsto_res
- \+ *def* nhds_within
- \+ *def* continuous_within_at
- \+ *def* continuous_on

Modified src/topology/local_homeomorph.lean


Modified src/topology/order.lean
- \- *lemma* continuous_iff_continuous_on_univ
- \- *lemma* continuous_within_at.mono
- \- *lemma* continuous_within_at_inter'
- \- *lemma* continuous_within_at_inter
- \- *lemma* continuous_on.congr_mono
- \- *lemma* continuous_at.continuous_within_at
- \- *lemma* continuous_within_at.continuous_at
- \- *lemma* continuous_within_at.comp
- \- *lemma* continuous_at.comp
- \- *lemma* continuous_on.comp
- \- *lemma* continuous_on.mono
- \- *lemma* continuous.continuous_on
- \- *lemma* continuous.comp_continuous_on
- \- *lemma* continuous.continuous_at
- \- *lemma* continuous_at.preimage_mem_nhds
- \- *lemma* continuous_within_at.preimage_mem_nhds_within
- \- *lemma* continuous_within_at.congr_of_mem_nhds_within
- \- *lemma* continuous_on_const
- \- *lemma* continuous_on_open_iff
- \- *lemma* continuous_on.preimage_open_of_open
- \- *lemma* continuous_on.preimage_closed_of_closed
- \- *lemma* continuous_on.preimage_interior_subset_interior_preimage
- \- *lemma* continuous_on_of_locally_continuous_on
- \- *lemma* continuous_on_open_of_generate_from
- \- *theorem* principal_subtype
- \- *theorem* mem_nhds_within_subtype
- \- *theorem* nhds_within_subtype
- \- *theorem* nhds_within_eq_map_subtype_val
- \- *theorem* tendsto_nhds_within_iff_subtype
- \- *theorem* continuous_within_at_univ
- \- *theorem* continuous_within_at_iff_continuous_at_restrict
- \- *theorem* continuous_within_at.tendsto_nhds_within_image
- \- *theorem* continuous_on_iff
- \- *theorem* continuous_on_iff_continuous_restrict
- \- *theorem* continuous_on_iff'
- \- *theorem* continuous_on_iff_is_closed
- \- *theorem* nhds_within_le_comap
- \- *theorem* continuous_within_at_iff_ptendsto_res



## [2019-10-08 02:26:24](https://github.com/leanprover-community/mathlib/commit/045d931)
feat(tactic/find): find defs as well as theorems ([#1512](https://github.com/leanprover-community/mathlib/pull/1512))
* feat(tactic/find): find defs as well as theorems
* use env.mfold
* use try
#### Estimated changes
Modified src/tactic/find.lean




## [2019-10-08 00:28:49](https://github.com/leanprover-community/mathlib/commit/ef7248f)
feat(data/quot): define `quotient.map₂'`, use it for group quotient ([#1507](https://github.com/leanprover-community/mathlib/pull/1507))
#### Estimated changes
Modified src/data/quot.lean


Modified src/group_theory/quotient_group.lean




## [2019-10-07 22:43:00](https://github.com/leanprover-community/mathlib/commit/bf22408)
chore(topology/algebra/group_completion): missing namespace ([#1518](https://github.com/leanprover-community/mathlib/pull/1518))
#### Estimated changes
Modified src/topology/algebra/group_completion.lean
- \+ *lemma* uniform_space.completion.coe_zero
- \- *lemma* coe_zero



## [2019-10-07 21:52:59](https://github.com/leanprover-community/mathlib/commit/1bf831f)
refactor(topology/dense_embedding): move dense embeddings to new file ([#1515](https://github.com/leanprover-community/mathlib/pull/1515))
#### Estimated changes
Modified src/topology/constructions.lean


Created src/topology/dense_embedding.lean
- \+ *lemma* dense_range_iff_closure_eq
- \+ *lemma* dense_range.comp
- \+ *lemma* dense_range.nonempty
- \+ *lemma* nhds_eq_comap
- \+ *lemma* closure_range
- \+ *lemma* self_sub_closure_image_preimage_of_open
- \+ *lemma* closure_image_nhds_of_nhds
- \+ *lemma* tendsto_comap_nhds_nhds
- \+ *lemma* comap_nhds_neq_bot
- \+ *lemma* extend_eq
- \+ *lemma* extend_e_eq
- \+ *lemma* extend_eq_of_cont
- \+ *lemma* tendsto_extend
- \+ *lemma* continuous_extend
- \+ *lemma* mk'
- \+ *lemma* inj_iff
- \+ *lemma* to_embedding
- \+ *theorem* dense_embedding.mk'
- \+ *def* dense_range
- \+ *def* dense_range.inhabited
- \+ *def* extend

Modified src/topology/maps.lean
- \- *lemma* dense_range_iff_closure_eq
- \- *lemma* dense_range.comp
- \- *lemma* dense_range.nonempty
- \- *lemma* nhds_eq_comap
- \- *lemma* closure_range
- \- *lemma* self_sub_closure_image_preimage_of_open
- \- *lemma* closure_image_nhds_of_nhds
- \- *lemma* tendsto_comap_nhds_nhds
- \- *lemma* comap_nhds_neq_bot
- \- *lemma* extend_eq
- \- *lemma* extend_e_eq
- \- *lemma* extend_eq_of_cont
- \- *lemma* tendsto_extend
- \- *lemma* continuous_extend
- \- *lemma* mk'
- \- *lemma* inj_iff
- \- *lemma* to_embedding
- \- *theorem* dense_embedding.mk'
- \- *def* dense_range
- \- *def* dense_range.inhabited
- \- *def* extend



## [2019-10-07 21:06:26](https://github.com/leanprover-community/mathlib/commit/b3eb34d)
doc(topology/order): module and definition docstrings ([#1505](https://github.com/leanprover-community/mathlib/pull/1505))
#### Estimated changes
Modified src/topology/basic.lean


Modified src/topology/order.lean




## [2019-10-07 17:24:46](https://github.com/leanprover-community/mathlib/commit/f519a12)
refactor(topology/list): move topology of lists, vectors to new file ([#1514](https://github.com/leanprover-community/mathlib/pull/1514))
#### Estimated changes
Modified src/topology/constructions.lean
- \- *lemma* tendsto_cons'
- \- *lemma* tendsto_cons
- \- *lemma* tendsto_cons_iff
- \- *lemma* tendsto_nhds
- \- *lemma* continuous_at_length
- \- *lemma* tendsto_insert_nth'
- \- *lemma* tendsto_insert_nth
- \- *lemma* continuous_insert_nth
- \- *lemma* tendsto_remove_nth
- \- *lemma* continuous_remove_nth
- \- *lemma* cons_val
- \- *lemma* continuous_insert_nth'
- \- *lemma* continuous_at_remove_nth

Created src/topology/list.lean
- \+ *lemma* nhds_list
- \+ *lemma* nhds_nil
- \+ *lemma* nhds_cons
- \+ *lemma* tendsto_cons'
- \+ *lemma* tendsto_cons
- \+ *lemma* tendsto_cons_iff
- \+ *lemma* tendsto_nhds
- \+ *lemma* continuous_at_length
- \+ *lemma* tendsto_insert_nth'
- \+ *lemma* tendsto_insert_nth
- \+ *lemma* continuous_insert_nth
- \+ *lemma* tendsto_remove_nth
- \+ *lemma* continuous_remove_nth
- \+ *lemma* cons_val
- \+ *lemma* continuous_insert_nth'
- \+ *lemma* continuous_at_remove_nth

Modified src/topology/order.lean
- \- *lemma* nhds_list
- \- *lemma* nhds_nil
- \- *lemma* nhds_cons



## [2019-10-07 16:34:46](https://github.com/leanprover-community/mathlib/commit/ddbeb7e)
refactor(topology/maps): avoid repetition in dense embeddings ([#1513](https://github.com/leanprover-community/mathlib/pull/1513))
#### Estimated changes
Modified src/topology/maps.lean




## [2019-10-05 15:44:17](https://github.com/leanprover-community/mathlib/commit/78a78ef)
feat(group_theory/submonoid): define `subtype.comm_monoid` ([#1511](https://github.com/leanprover-community/mathlib/pull/1511))
#### Estimated changes
Modified src/group_theory/submonoid.lean




## [2019-10-05 12:20:29](https://github.com/leanprover-community/mathlib/commit/7df0e35)
chore(topology): sanity_check pass ([#1510](https://github.com/leanprover-community/mathlib/pull/1510))
* chore(topology): sanity_check pass
* fix(topology/uniform_space/separation): fix build
* fix(topology/metric_space): some more namespace fixes
#### Estimated changes
Modified src/topology/algebra/open_subgroup.lean
- \+/\- *lemma* is_open_of_nonempty_open_subset
- \+/\- *lemma* is_open_of_open_subgroup
- \+/\- *lemma* is_closed

Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/constructions.lean
- \+/\- *lemma* is_open_prod_iff'

Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/isometry.lean
- \- *lemma* Kuratowski_embedding_isometry
- \+/\- *def* ℓ_infty_ℝ

Modified src/topology/stone_cech.lean


Modified src/topology/uniform_space/separation.lean




## [2019-10-05 05:18:27](https://github.com/leanprover-community/mathlib/commit/98dbe27)
feat(algebra/opposites): add some trivial `@[simp]` lemmas ([#1508](https://github.com/leanprover-community/mathlib/pull/1508))
#### Estimated changes
Modified src/algebra/opposites.lean
- \+ *lemma* op_zero
- \+ *lemma* unop_zero
- \+ *lemma* op_one
- \+ *lemma* unop_one
- \+ *lemma* op_add
- \+ *lemma* unop_add
- \+ *lemma* op_neg
- \+ *lemma* unop_neg
- \+ *lemma* op_mul
- \+ *lemma* unop_mul
- \+ *lemma* op_inv
- \+ *lemma* unop_inv



## [2019-10-04 14:25:15](https://github.com/leanprover-community/mathlib/commit/2f1bd1e)
fix(data/list/min_max): docs typo ([#1504](https://github.com/leanprover-community/mathlib/pull/1504))
#### Estimated changes
Modified src/data/list/min_max.lean




## [2019-10-04 14:08:27](https://github.com/leanprover-community/mathlib/commit/343237d)
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
#### Estimated changes
Created src/algebra/category/Module/basic.lean
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *def* of

Modified src/algebra/punit_instances.lean




## [2019-10-04 11:56:55](https://github.com/leanprover-community/mathlib/commit/494132e)
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
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_range_zero
- \+ *lemma* prod_range_one
- \+ *lemma* sum_range_one
- \- *lemma* geom_sum_inv
- \- *theorem* geom_sum_mul_add
- \- *theorem* geom_sum_mul
- \- *theorem* geom_sum

Created src/algebra/commute.lean
- \+ *lemma* centralizer.inter_units_is_subgroup
- \+ *lemma* group.centralizer_closure
- \+ *lemma* add_monoid.centralizer_closure
- \+ *lemma* ring.centralizer_closure
- \+ *theorem* mem_centralizer
- \+ *theorem* mul_right
- \+ *theorem* mul_left
- \+ *theorem* one_right
- \+ *theorem* one_left
- \+ *theorem* units_inv_right
- \+ *theorem* units_inv_right_iff
- \+ *theorem* units_inv_left
- \+ *theorem* units_inv_left_iff
- \+ *theorem* units_coe
- \+ *theorem* inv_right
- \+ *theorem* inv_right_iff
- \+ *theorem* inv_left
- \+ *theorem* inv_left_iff
- \+ *theorem* inv_inv
- \+ *theorem* inv_inv_iff
- \+ *theorem* zero_right
- \+ *theorem* zero_left
- \+ *theorem* add_right
- \+ *theorem* add_left
- \+ *theorem* neg_right
- \+ *theorem* neg_right_iff
- \+ *theorem* neg_left
- \+ *theorem* neg_left_iff
- \+ *theorem* neg_one_right
- \+ *theorem* neg_one_left
- \+ *theorem* sub_right
- \+ *theorem* sub_left
- \+ *theorem* monoid.centralizer_closure
- \+ *theorem* pow_right
- \+ *theorem* pow_left
- \+ *theorem* pow_pow
- \+ *theorem* list_prod_right
- \+ *theorem* list_prod_left
- \+ *theorem* self_pow
- \+ *theorem* pow_self
- \+ *theorem* pow_pow_self
- \+ *theorem* gpow_right
- \+ *theorem* gpow_left
- \+ *theorem* gpow_gpow
- \+ *theorem* self_gpow
- \+ *theorem* gpow_self
- \+ *theorem* gpow_gpow_self
- \+ *theorem* smul_right
- \+ *theorem* smul_left
- \+ *theorem* smul_smul
- \+ *theorem* self_smul
- \+ *theorem* smul_self
- \+ *theorem* self_smul_smul
- \+ *theorem* cast_nat_right
- \+ *theorem* cast_nat_left
- \+ *theorem* gsmul_right
- \+ *theorem* gsmul_left
- \+ *theorem* gsmul_gsmul
- \+ *theorem* self_gsmul
- \+ *theorem* gsmul_self
- \+ *theorem* self_gsmul_gsmul
- \+ *theorem* cast_int_right
- \+ *theorem* cast_int_left
- \+ *theorem* neg_pow
- \+ *def* commute
- \+ *def* centralizer

Created src/algebra/geom_sum.lean
- \+ *lemma* geom_sum_inv
- \+ *theorem* geom_series_def
- \+ *theorem* geom_series_zero
- \+ *theorem* geom_series_one
- \+ *theorem* geom_series₂_def
- \+ *theorem* geom_series₂_zero
- \+ *theorem* geom_series₂_one
- \+ *theorem* geom_series₂_with_one
- \+ *theorem* geom_sum₂_mul_add
- \+ *theorem* geom_sum_mul_add
- \+ *theorem* geom_sum₂_mul_comm
- \+ *theorem* geom_sum₂_mul
- \+ *theorem* geom_sum_mul
- \+ *theorem* geom_sum_mul_neg
- \+ *theorem* geom_sum
- \+ *def* geom_series
- \+ *def* geom_series₂

Modified src/algebra/group_power.lean
- \+ *theorem* gsmul_one

Modified src/analysis/specific_limits.lean


Modified src/data/complex/exponential.lean


Modified src/data/nat/choose.lean
- \+ *theorem* commute.add_pow
- \+/\- *theorem* add_pow

Modified src/data/set/lattice.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid.lean
- \- *lemma* is_submonoid.inter

Modified src/ring_theory/subring.lean




## [2019-10-04 00:45:14](https://github.com/leanprover-community/mathlib/commit/3c58f16)
doc(linear_algebra/basic): add module and declaration doc strings ([#1501](https://github.com/leanprover-community/mathlib/pull/1501))
* doc(linear_algebra/basic): declaration doc strings
* doc(linear_algebra/basic): improve module doc
* Update src/linear_algebra/basic.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
#### Estimated changes
Modified src/linear_algebra/basic.lean




## [2019-10-03 19:53:03](https://github.com/leanprover-community/mathlib/commit/f854371)
feat(tactic/squeeze_simp): better handling of private declarations ([#1498](https://github.com/leanprover-community/mathlib/pull/1498))
* feat(tactic/squeeze_simp): better handling of private declarations
* Update core.lean
#### Estimated changes
Modified src/tactic/core.lean




## [2019-10-03 17:37:55](https://github.com/leanprover-community/mathlib/commit/4ca1e63)
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
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_eq_one
- \+/\- *lemma* sum_le_sum_of_ne_zero

Modified src/algebra/order_functions.lean
- \+ *lemma* abs_add
- \+ *lemma* sub_abs_le_abs_sub
- \- *def* abs_add
- \- *def* sub_abs_le_abs_sub

Modified src/analysis/complex/exponential.lean


Modified src/category/functor.lean
- \+/\- *def* const

Modified src/category_theory/isomorphism.lean
- \+ *lemma* inv_inv
- \- *lemma* is_iso.inv_inv

Modified src/category_theory/limits/preserves.lean


Modified src/computability/turing_machine.lean
- \- *theorem* {l}
- \+ *def* {l}

Modified src/data/finset.lean
- \+/\- *lemma* coe_filter
- \+/\- *lemma* image_const
- \+/\- *lemma* subset_image_iff
- \+/\- *lemma* card_lt_card
- \+/\- *lemma* card_le_card_of_inj_on
- \+/\- *theorem* subset_insert
- \+/\- *theorem* map_empty
- \+/\- *theorem* image_singleton
- \+/\- *theorem* fold_map
- \+/\- *def* pi.empty

Modified src/data/finsupp.lean


Modified src/data/fintype.lean


Modified src/data/list/basic.lean


Modified src/data/list/defs.lean
- \+/\- *def* neg

Modified src/data/opposite.lean


Modified src/data/rat/order.lean


Modified src/data/seq/computation.lean
- \+ *lemma* corec_eq
- \+ *lemma* lift_rel_aux.ret_left
- \+ *lemma* lift_rel_aux.ret_right
- \- *def* corec_eq
- \- *def* lift_rel_aux.ret_left
- \- *def* lift_rel_aux.ret_right

Modified src/data/set/finite.lean
- \+/\- *lemma* coe_to_finset'
- \+/\- *def* fintype_of_fintype_image

Modified src/data/set/function.lean
- \+/\- *theorem* right_inv_on_of_eq_on_left

Modified src/logic/basic.lean
- \+ *lemma* Exists.imp
- \+/\- *lemma* exists_imp_exists'
- \- *def* Exists.imp

Modified src/meta/expr.lean
- \+ *def* has_prefix

Modified src/meta/rb_map.lean


Modified src/set_theory/ordinal.lean
- \+/\- *theorem* lt_le_top
- \+/\- *theorem* equiv_lt_apply
- \+/\- *theorem* equiv_lt_top
- \+/\- *theorem* top_eq
- \+/\- *theorem* of_element_top

Modified src/tactic/core.lean


Modified src/tactic/interactive.lean
- \+/\- *lemma* {u}

Modified src/tactic/sanity_check.lean


Modified src/topology/category/Top/open_nhds.lean


Modified test/sanity_check.lean




## [2019-10-03 09:33:33](https://github.com/leanprover-community/mathlib/commit/4bb8d44)
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
#### Estimated changes
Modified src/data/equiv/algebra.lean
- \+ *lemma* ext
- \+ *def* mul_aut
- \+ *def* to_perm
- \+ *def* ring_aut
- \+ *def* to_add_aut
- \+ *def* to_mul_aut



## [2019-10-02 16:42:34](https://github.com/leanprover-community/mathlib/commit/bea1c20)
fix(dioph): remove global vector3 notation ([#1502](https://github.com/leanprover-community/mathlib/pull/1502))
* fix(dioph): remove global vector3 notation
it overloads list notation, and then tries to find a coercion from vector3 to list
* also make other notations in dioph local
* undo localizing ++, overloading that is probably fine
* add comment
#### Estimated changes
Modified src/number_theory/dioph.lean




## [2019-10-02 17:27:04+02:00](https://github.com/leanprover-community/mathlib/commit/39ca4f1)
chore(.): delete CODEOWNERS
#### Estimated changes
Deleted CODEOWNERS




## [2019-10-01 18:48:13](https://github.com/leanprover-community/mathlib/commit/5ed5f59)
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
#### Estimated changes
Modified src/category_theory/comma.lean


Modified src/data/nat/modeq.lean


Modified src/data/rel.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/linear_algebra/dual.lean
- \- *def* dual

Modified src/tactic/core.lean


Modified src/topology/uniform_space/compare_reals.lean
- \+/\- *def* Q

Modified test/delta_instance.lean
- \+ *def* X
- \+ *def* id_ring
- \+ *def* S



## [2019-10-01 07:53:40](https://github.com/leanprover-community/mathlib/commit/800dba4)
chore(linear_map): use curly brackets for type class in linear_map coe_to_fun ([#1493](https://github.com/leanprover-community/mathlib/pull/1493))
* chore(linear_map): use curly brackets for type class in linear_map coe_to_fun
*  fix
#### Estimated changes
Modified src/algebra/module.lean


Modified src/field_theory/mv_polynomial.lean


