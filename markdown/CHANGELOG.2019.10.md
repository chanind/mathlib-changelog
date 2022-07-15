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
- \- *lemma* category_theory.nat_trans.op_app
- \+ *lemma* category_theory.nat_trans.op_id
- \- *lemma* category_theory.nat_trans.unop_app
- \+ *lemma* category_theory.nat_trans.unop_id

Modified src/category_theory/whiskering.lean
- \- *lemma* category_theory.whisker_left.app
- \+/\- *def* category_theory.whisker_left
- \- *lemma* category_theory.whisker_right.app
- \+/\- *def* category_theory.whisker_right
- \+/\- *def* category_theory.whiskering_left
- \- *lemma* category_theory.whiskering_left_map_app_app
- \- *lemma* category_theory.whiskering_left_obj_map
- \- *lemma* category_theory.whiskering_left_obj_obj
- \+/\- *def* category_theory.whiskering_right
- \- *lemma* category_theory.whiskering_right_map_app_app
- \- *lemma* category_theory.whiskering_right_obj_map
- \- *lemma* category_theory.whiskering_right_obj_obj

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
- \+ *theorem* fintype.card_of_finset'
- \+ *theorem* fintype.card_of_finset
- \+ *def* fintype.of_finset
- \+ *theorem* set.mem_to_finset
- \+ *theorem* set.mem_to_finset_val
- \+ *def* set.to_finset

Modified src/data/fintype/intervals.lean


Modified src/data/set/finite.lean
- \- *theorem* set.card_fintype_of_finset'
- \- *theorem* set.card_fintype_of_finset
- \- *def* set.fintype_of_finset
- \- *theorem* set.mem_to_finset
- \- *theorem* set.mem_to_finset_val
- \- *def* set.to_finset

Modified src/group_theory/order_of_element.lean




## [2019-10-31 13:24:24](https://github.com/leanprover-community/mathlib/commit/6b51787)
feat(order/conditionally_complete_lattice): add complete_linear_order instance for enat ([#1633](https://github.com/leanprover-community/mathlib/pull/1633))
#### Estimated changes
Modified src/data/nat/enat.lean
- \+ *lemma* enat.with_top_equiv_coe
- \+ *lemma* enat.with_top_equiv_le
- \+ *lemma* enat.with_top_equiv_lt
- \+ *lemma* enat.with_top_equiv_symm_coe
- \+ *lemma* enat.with_top_equiv_symm_le
- \+ *lemma* enat.with_top_equiv_symm_lt
- \+ *lemma* enat.with_top_equiv_symm_top
- \+ *lemma* enat.with_top_equiv_symm_zero
- \+ *lemma* enat.with_top_equiv_top
- \+ *lemma* enat.with_top_equiv_zero

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
- \+ *lemma* finset.prod_eq_multiset_prod

Modified src/data/int/basic.lean
- \+ *lemma* is_ring_hom.map_int_cast
- \+ *lemma* ring_hom.map_int_cast

Modified src/data/int/parity.lean
- \+ *theorem* int.even_neg

Modified src/data/nat/cast.lean
- \+ *lemma* is_semiring_hom.map_nat_cast
- \+ *lemma* ring_hom.map_nat_cast

Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/field_theory/finite.lean
- \+ *lemma* char_p.sum_two_squares
- \+ *lemma* zmodp.sum_two_squares

Added src/number_theory/sum_four_squares.lean
- \+ *lemma* int.exists_sum_two_squares_add_one_eq_k
- \+ *lemma* int.sum_two_squares_of_two_mul_sum_two_squares
- \+ *lemma* nat.sum_four_squares



## [2019-10-29 09:22:53](https://github.com/leanprover-community/mathlib/commit/6030ff0)
chore(category_theory): speed-up monoidal.of_has_finite_products ([#1616](https://github.com/leanprover-community/mathlib/pull/1616))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.coprod.associator_naturality
- \+ *lemma* category_theory.limits.coprod.pentagon
- \+ *lemma* category_theory.limits.coprod.triangle
- \+ *lemma* category_theory.limits.prod.associator_naturality
- \+ *lemma* category_theory.limits.prod.pentagon
- \+ *lemma* category_theory.limits.prod.triangle

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
- \+/\- *theorem* rat.cast_add
- \+/\- *theorem* rat.cast_bit0
- \+/\- *theorem* rat.cast_bit1
- \+/\- *theorem* rat.cast_mul
- \+/\- *theorem* rat.cast_sub

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
- \+/\- *def* algebra.comap



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
- \+/\- *def* mv_polynomial.mv_polynomial_equiv_mv_polynomial
- \+/\- *def* mv_polynomial.ring_equiv_congr



## [2019-10-27 02:35:54](https://github.com/leanprover-community/mathlib/commit/8a45d98)
chore(category_theory): remove superfluous lemma ([#1614](https://github.com/leanprover-community/mathlib/pull/1614))
#### Estimated changes
Modified src/category_theory/category/default.lean
- \- *lemma* category_theory.category.assoc_symm

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
- \+ *lemma* nat.eq_of_dvd_of_div_eq_one
- \- *lemma* nat.eq_of_dvd_quot_one
- \+ *lemma* nat.eq_zero_of_dvd_of_div_eq_zero

Modified src/data/nat/prime.lean
- \+ *lemma* nat.min_fac_le_div



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
- \+ *lemma* finset.Ico_ℤ.mem
- \+ *def* finset.Ico_ℤ

Added src/data/fintype/intervals.lean


Modified src/data/int/basic.lean
- \+ *lemma* int.to_nat_sub_of_le



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
- \- *theorem* nat.pos_iff_ne_zero'

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


Added src/data/rat/meta.lean


Modified src/meta/expr.lean


Modified src/tactic/norm_num.lean


Added test/rat.lean




## [2019-10-24 15:08:35](https://github.com/leanprover-community/mathlib/commit/3f8a492)
chore(category_theory): replace some @[simp] with @[simps] ([#1605](https://github.com/leanprover-community/mathlib/pull/1605))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *def* category_theory.limits.coprod.associator
- \+/\- *def* category_theory.limits.coprod.braiding
- \+/\- *def* category_theory.limits.coprod.left_unitor
- \+/\- *def* category_theory.limits.coprod.right_unitor
- \+/\- *def* category_theory.limits.prod.associator
- \+/\- *def* category_theory.limits.prod.braiding
- \+/\- *def* category_theory.limits.prod.left_unitor
- \+/\- *def* category_theory.limits.prod.right_unitor



## [2019-10-24 13:48:11](https://github.com/leanprover-community/mathlib/commit/b1f44ba)
chore(group_theory/free_group,order/zorn): rename zorn.zorn and sum.sum ([#1604](https://github.com/leanprover-community/mathlib/pull/1604))
* chore(order/zorn): rename zorn.zorn
* chore(group_theory/free_group): rename sum.sum
* chore(group_theory/free_group,order/zorn): remove nolint
#### Estimated changes
Modified src/group_theory/free_group.lean
- \+ *lemma* free_group.sum.mul
- \- *lemma* free_group.sum.sum

Modified src/order/filter/basic.lean


Modified src/order/zorn.lean
- \+ *theorem* zorn.exists_maximal_of_chains_bounded
- \- *theorem* zorn.zorn



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
- \+/\- *lemma* free_group.sum.sum

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.finite_dimensional_of_finite_basis
- \- *def* finite_dimensional.finite_dimensional_of_finite_basis

Modified src/number_theory/pell.lean
- \+/\- *def* pell.pell

Modified src/order/lattice.lean
- \+ *theorem* lattice.ext
- \- *theorem* lattice.lattice.ext

Modified src/order/zorn.lean
- \+/\- *theorem* zorn.zorn

Modified src/ring_theory/algebraic.lean
- \+ *lemma* subalgebra.is_algebraic_iff
- \- *def* subalgebra.is_algebraic_iff

Modified src/set_theory/ordinal.lean
- \+/\- *def* cardinal.ord_eq_min
- \+/\- *def* ordinal.div_def

Modified src/tactic/reassoc_axiom.lean
- \+ *theorem* category_theory.reassoc_of
- \- *def* category_theory.reassoc_of

Modified src/tactic/transfer.lean




## [2019-10-24 02:49:46](https://github.com/leanprover-community/mathlib/commit/31c73c1)
feat(data/multiset): map_eq_map_of_bij_of_nodup ([#1590](https://github.com/leanprover-community/mathlib/pull/1590))
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/data/multiset.lean
- \+ *theorem* multiset.eq_zero_iff_forall_not_mem
- \+ *lemma* multiset.map_eq_map_of_bij_of_nodup



## [2019-10-24 00:47:18](https://github.com/leanprover-community/mathlib/commit/08977be)
feat(algebra/semiconj): define `semiconj_by` and some operations ([#1576](https://github.com/leanprover-community/mathlib/pull/1576))
* feat(algebra/semiconj): define `semiconj_by` and some operations
Also rewrite `algebra/commute` to reuse results from `algebra/semiconj`.
* Some `@[simp]` attributes
* Fixes by @rwbarton, more docs
* Add two more constructors
#### Estimated changes
Modified src/algebra/commute.lean
- \+/\- *theorem* commute.add_left
- \+/\- *theorem* commute.add_right
- \+/\- *theorem* commute.cast_nat_left
- \+/\- *theorem* commute.cast_nat_right
- \+/\- *theorem* commute.gpow_gpow
- \+/\- *theorem* commute.gpow_gpow_self
- \+/\- *theorem* commute.gpow_left
- \+/\- *theorem* commute.gpow_right
- \+/\- *theorem* commute.gsmul_gsmul
- \+/\- *theorem* commute.gsmul_left
- \+/\- *theorem* commute.gsmul_right
- \+/\- *theorem* commute.gsmul_self
- \+/\- *theorem* commute.inv_inv
- \+/\- *theorem* commute.inv_inv_iff
- \+/\- *theorem* commute.inv_left
- \+/\- *theorem* commute.inv_left_iff
- \+/\- *theorem* commute.inv_right
- \+/\- *theorem* commute.inv_right_iff
- \+/\- *theorem* commute.list_prod_left
- \+/\- *theorem* commute.list_prod_right
- \+/\- *theorem* commute.neg_left
- \+/\- *theorem* commute.neg_left_iff
- \+/\- *theorem* commute.neg_one_left
- \+/\- *theorem* commute.neg_one_right
- \+/\- *theorem* commute.neg_right
- \+/\- *theorem* commute.neg_right_iff
- \+/\- *theorem* commute.one_left
- \+/\- *theorem* commute.one_right
- \+/\- *theorem* commute.pow_pow
- \+/\- *theorem* commute.pow_right
- \+/\- *theorem* commute.self_gsmul
- \+/\- *theorem* commute.self_gsmul_gsmul
- \+/\- *theorem* commute.self_smul
- \+/\- *theorem* commute.self_smul_smul
- \+/\- *theorem* commute.smul_left
- \+/\- *theorem* commute.smul_right
- \+/\- *theorem* commute.smul_self
- \+/\- *theorem* commute.smul_smul
- \+/\- *theorem* commute.sub_left
- \+/\- *theorem* commute.sub_right
- \+/\- *theorem* commute.units_coe
- \+ *theorem* commute.units_coe_iff
- \+/\- *theorem* commute.units_inv_left
- \+/\- *theorem* commute.units_inv_right
- \+ *theorem* commute.units_of_coe
- \+/\- *theorem* commute.zero_left
- \+/\- *theorem* commute.zero_right
- \+/\- *def* commute

Added src/algebra/semiconj.lean
- \+ *lemma* semiconj_by.add_left
- \+ *lemma* semiconj_by.add_right
- \+ *lemma* semiconj_by.cast_nat_left
- \+ *lemma* semiconj_by.cast_nat_right
- \+ *lemma* semiconj_by.conj_mk
- \+ *lemma* semiconj_by.gpow_right
- \+ *lemma* semiconj_by.gsmul_gsmul
- \+ *lemma* semiconj_by.gsmul_left
- \+ *lemma* semiconj_by.gsmul_right
- \+ *lemma* semiconj_by.inv_inv_symm
- \+ *lemma* semiconj_by.inv_inv_symm_iff
- \+ *lemma* semiconj_by.inv_right
- \+ *lemma* semiconj_by.inv_right_iff
- \+ *lemma* semiconj_by.inv_symm_left
- \+ *lemma* semiconj_by.inv_symm_left_iff
- \+ *lemma* semiconj_by.mul_left
- \+ *lemma* semiconj_by.mul_right
- \+ *lemma* semiconj_by.neg_left
- \+ *lemma* semiconj_by.neg_left_iff
- \+ *lemma* semiconj_by.neg_one_left
- \+ *lemma* semiconj_by.neg_one_right
- \+ *lemma* semiconj_by.neg_right
- \+ *lemma* semiconj_by.neg_right_iff
- \+ *lemma* semiconj_by.one_left
- \+ *lemma* semiconj_by.one_right
- \+ *lemma* semiconj_by.pow_right
- \+ *lemma* semiconj_by.smul_left
- \+ *lemma* semiconj_by.smul_right
- \+ *lemma* semiconj_by.smul_smul
- \+ *lemma* semiconj_by.sub_left
- \+ *lemma* semiconj_by.sub_right
- \+ *theorem* semiconj_by.units_coe
- \+ *theorem* semiconj_by.units_coe_iff
- \+ *lemma* semiconj_by.units_conj_mk
- \+ *lemma* semiconj_by.units_gpow_right
- \+ *lemma* semiconj_by.units_inv_right
- \+ *lemma* semiconj_by.units_inv_right_iff
- \+ *lemma* semiconj_by.units_inv_symm_left
- \+ *lemma* semiconj_by.units_inv_symm_left_iff
- \+ *theorem* semiconj_by.units_of_coe
- \+ *lemma* semiconj_by.zero_left
- \+ *lemma* semiconj_by.zero_right
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
- \+ *lemma* times_cont_diff.add
- \+ *lemma* times_cont_diff.comp_times_cont_diff_on
- \+ *lemma* times_cont_diff.neg
- \+ *lemma* times_cont_diff.sub
- \+ *lemma* times_cont_diff_on.add
- \+ *lemma* times_cont_diff_on.neg
- \+ *lemma* times_cont_diff_on.sub
- \+ *lemma* times_cont_diff_on_const

Modified src/geometry/manifold/manifold.lean
- \- *def* groupoid_of_pregroupoid
- \+ *lemma* has_groupoid_of_pregroupoid
- \+ *lemma* mem_pregroupoid_of_eq_on_source
- \+ *def* pregroupoid.groupoid

Added src/geometry/manifold/real_instances.lean
- \+ *def* Icc_left_chart
- \+ *def* Icc_right_chart
- \+ *def* euclidean_half_space
- \+ *def* euclidean_quadrant
- \+ *def* euclidean_space
- \+ *lemma* findim_euclidean_space
- \+ *def* lt_class
- \+ *def* model_with_corners_euclidean_half_space
- \+ *def* model_with_corners_euclidean_quadrant
- \+ *lemma* range_half_space
- \+ *lemma* range_quadrant

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \- *def* euclidean_half_space
- \- *def* euclidean_space
- \- *def* model_with_corners_euclidean_half_space
- \+ *lemma* of_set_mem_times_cont_diff_groupoid
- \- *lemma* range_half_space
- \+ *lemma* symm_trans_mem_times_cont_diff_groupoid
- \+/\- *def* times_cont_diff_groupoid
- \+/\- *lemma* times_cont_diff_groupoid_le
- \+/\- *lemma* times_cont_diff_groupoid_zero_eq

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.findim_fin_fun
- \+ *lemma* finite_dimensional.findim_fintype_fun_eq_card



## [2019-10-23 20:48:14](https://github.com/leanprover-community/mathlib/commit/b433afa)
feat(algebra/big_operators): sum_ite ([#1598](https://github.com/leanprover-community/mathlib/pull/1598))
* feat(algebra/big_operators): sum_ite
rename the current `sum_ite` to `sum_ite_eq` and add a more general version
* Update src/algebra/big_operators.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* finset.prod_ite
- \+ *lemma* finset.prod_ite_eq



## [2019-10-23 20:28:52](https://github.com/leanprover-community/mathlib/commit/36dfcfc)
doc(topology/topological_fiber_bundle): documentation improvements ([#1594](https://github.com/leanprover-community/mathlib/pull/1594))
* feat(topology/topological_fiber_bundle): improvements
* minor fixes
#### Estimated changes
Modified src/topology/topological_fiber_bundle.lean
- \+/\- *def* topological_fiber_bundle_core.base
- \+/\- *def* topological_fiber_bundle_core.fiber
- \+/\- *def* topological_fiber_bundle_core.index
- \+/\- *def* topological_fiber_bundle_core.total_space



## [2019-10-23 17:05:43](https://github.com/leanprover-community/mathlib/commit/d214c61)
feat(data/nat/modeq): div_mod_eq_mod_mul_div ([#1597](https://github.com/leanprover-community/mathlib/pull/1597))
#### Estimated changes
Modified src/data/nat/modeq.lean
- \+ *lemma* nat.div_mod_eq_mod_mul_div



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
- \- *def* mv_polynomial.tmp.coe



## [2019-10-23 10:48:29](https://github.com/leanprover-community/mathlib/commit/079e6ec)
feat(analysis/normed_space): norms on ℤ and ℚ ([#1570](https://github.com/leanprover-community/mathlib/pull/1570))
* feat(analysis/normed_space): norms on ℤ and ℚ
* Add some `elim_cast` lemmas
* Add `@[simp]`, thanks @robertylewis
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* int.norm_cast_rat
- \+ *lemma* int.norm_cast_real
- \+ *lemma* rat.norm_cast_real

Modified src/topology/instances/real.lean
- \+ *theorem* int.dist_cast_rat
- \+ *theorem* int.dist_cast_real
- \+ *theorem* int.dist_eq
- \+ *lemma* rat.dist_cast



## [2019-10-23 07:50:35](https://github.com/leanprover-community/mathlib/commit/ee5518c)
fix(category_theory/adjunctions): fix deterministic timeouts ([#1586](https://github.com/leanprover-community/mathlib/pull/1586))
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/limits.lean
- \+ *def* category_theory.adjunction.cocones_iso_component_hom
- \+ *def* category_theory.adjunction.cocones_iso_component_inv
- \+ *def* category_theory.adjunction.cones_iso_component_hom
- \+ *def* category_theory.adjunction.cones_iso_component_inv
- \+ *def* category_theory.adjunction.functoriality_counit'
- \+ *def* category_theory.adjunction.functoriality_counit
- \+ *def* category_theory.adjunction.functoriality_left_adjoint
- \+ *def* category_theory.adjunction.functoriality_right_adjoint
- \+ *def* category_theory.adjunction.functoriality_unit'
- \+ *def* category_theory.adjunction.functoriality_unit

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
- \+ *def* CommRing.CommRing_has_limits.limit
- \+ *def* CommRing.CommRing_has_limits.limit_is_limit



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
Added archive/sensitivity.lean
- \+ *lemma* Q.adj_iff_proj_adj
- \+ *lemma* Q.adj_iff_proj_eq
- \+ *lemma* Q.adjacent.symm
- \+ *def* Q.adjacent
- \+ *lemma* Q.card
- \+ *lemma* Q.not_adjacent_zero
- \+ *lemma* Q.succ_n_eq
- \+ *def* V.add_comm_monoid
- \+ *def* V.add_comm_semigroup
- \+ *def* V.has_add
- \+ *def* V.has_scalar
- \+ *def* V.module
- \+ *def* V
- \+ *lemma* dim_V
- \+ *def* dual_pair_e_ε
- \+ *lemma* duality
- \+ *lemma* e_zero_apply
- \+ *lemma* epsilon_total
- \+ *lemma* exists_eigenvalue
- \+ *lemma* f_image_g
- \+ *lemma* f_matrix
- \+ *lemma* f_squared
- \+ *lemma* f_succ_apply
- \+ *lemma* f_zero
- \+ *lemma* findim_V
- \+ *lemma* g_apply
- \+ *lemma* g_injective
- \+ *theorem* huang_degree_theorem
- \+ *def* π



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
- \+/\- *def* CommRing.colimits.cocone_fun

Modified src/algebra/category/Mon/colimits.lean
- \+/\- *def* Mon.colimits.cocone_fun



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
- \+/\- *lemma* category_theory.over.w

Modified src/category_theory/functor.lean


Modified src/tactic/reassoc_axiom.lean
- \+ *def* category_theory.reassoc_of
- \+ *def* tactic.calculated_Prop

Modified test/tactics.lean




## [2019-10-22 04:37:39](https://github.com/leanprover-community/mathlib/commit/1741a1d)
feat(data/nat/basic): division inequalities ([#1579](https://github.com/leanprover-community/mathlib/pull/1579))
* feat(data/nat/basic): division inequalities
* whitespace
* fix
* shorten proof
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.div_mul_div_le_div
- \+ *lemma* nat.mul_div_le_mul_div_assoc



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
- \- *lemma* CommRing.comp_eq
- \- *lemma* CommRing.forget_map_eq_coe
- \- *lemma* CommRing.forget_obj_eq_coe
- \- *lemma* CommRing.id_eq
- \+/\- *def* CommRing
- \+/\- *def* CommSemiRing
- \+/\- *def* Ring
- \+/\- *def* SemiRing

Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/CommRing/limits.lean


Modified src/algebra/category/Group.lean
- \+/\- *def* CommGroup
- \+/\- *def* Group

Modified src/algebra/category/Mon/basic.lean
- \+/\- *def* CommMon.of
- \+/\- *def* CommMon

Modified src/algebra/category/Mon/colimits.lean


Modified src/category_theory/concrete_category/basic.lean
- \+ *lemma* category_theory.coe_comp
- \+ *lemma* category_theory.coe_id
- \+ *def* category_theory.concrete_category.has_coe_to_fun
- \+ *def* category_theory.concrete_category.has_coe_to_sort
- \+ *lemma* category_theory.forget_map_eq_coe
- \+ *lemma* category_theory.forget_obj_eq_coe

Modified src/category_theory/concrete_category/bundled.lean
- \+/\- *def* category_theory.bundled.map

Modified src/category_theory/concrete_category/bundled_hom.lean
- \- *lemma* category_theory.bundled_hom.coe_comp
- \- *lemma* category_theory.bundled_hom.coe_id
- \- *def* category_theory.bundled_hom.full_subcategory_has_forget₂
- \- *def* category_theory.bundled_hom.has_coe_to_fun

Modified src/category_theory/full_subcategory.lean
- \+/\- *def* category_theory.induced_functor

Modified src/category_theory/limits/cones.lean
- \- *lemma* category_theory.limits.cocone.naturality_bundled
- \+ *lemma* category_theory.limits.cocone.naturality_concrete
- \- *lemma* category_theory.limits.cone.naturality_bundled
- \+ *lemma* category_theory.limits.cone.naturality_concrete



## [2019-10-22 00:57:19](https://github.com/leanprover-community/mathlib/commit/340178d)
feat(data/finset): inj_on_of_surj_on_of_card_le ([#1578](https://github.com/leanprover-community/mathlib/pull/1578))
* feat(data/finset): inj_on_of_surj_on_of_card_le
* Type ascriptions
* function namespace
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* finset.inj_on_of_surj_on_of_card_le



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
- \+ *lemma* finset.sum_const'
- \+ *lemma* module.smul_eq_smul

Modified src/algebra/ring.lean
- \+ *lemma* mul_ite

Modified src/data/set/finite.lean
- \+ *lemma* fintype.exists_max
- \+ *def* set.decidable_mem_of_fintype
- \+ *lemma* set.to_finset_card
- \+ *lemma* set.to_finset_inter

Modified src/linear_algebra/dual.lean
- \+ *def* dual_pair.coeffs
- \+ *lemma* dual_pair.coeffs_apply
- \+ *lemma* dual_pair.coeffs_lc
- \+ *lemma* dual_pair.decomposition
- \+ *lemma* dual_pair.dual_lc
- \+ *lemma* dual_pair.eq_dual
- \+ *lemma* dual_pair.is_basis
- \+ *def* dual_pair.lc
- \+ *lemma* dual_pair.mem_of_mem_span
- \+ *structure* dual_pair
- \+/\- *lemma* is_basis.to_dual_to_dual

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.dim_eq_card
- \+ *lemma* finite_dimensional.fg_of_finite_basis
- \+ *def* finite_dimensional.finite_dimensional_of_finite_basis

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* linear_map.map_finsupp_total

Modified src/ring_theory/power_series.lean


Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.nat_cast_pow



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
Added src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *def* euclidean_half_space
- \+ *def* euclidean_space
- \+ *lemma* model_with_corners.image
- \+ *def* model_with_corners.prod
- \+ *def* model_with_corners.tangent
- \+ *structure* model_with_corners
- \+ *def* model_with_corners_euclidean_half_space
- \+ *lemma* model_with_corners_inv_fun_comp
- \+ *lemma* model_with_corners_left_inv
- \+ *lemma* model_with_corners_right_inv
- \+ *def* model_with_corners_self
- \+ *lemma* model_with_corners_self_local_equiv
- \+ *lemma* model_with_corners_target
- \+ *lemma* range_half_space
- \+ *def* times_cont_diff_groupoid
- \+ *lemma* times_cont_diff_groupoid_le
- \+ *lemma* times_cont_diff_groupoid_zero_eq



## [2019-10-21 12:39:30](https://github.com/leanprover-community/mathlib/commit/f52e952)
feat(data/finset): define `finset.Ico.subset_iff` ([#1574](https://github.com/leanprover-community/mathlib/pull/1574))
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.Ico.subset_iff

Modified src/data/nat/basic.lean
- \+ *lemma* nat.le_of_pred_lt



## [2019-10-21 10:18:48](https://github.com/leanprover-community/mathlib/commit/a4bbbde)
feat(topology/topological_fiber_bundle): topological fiber bundles ([#1421](https://github.com/leanprover-community/mathlib/pull/1421))
* feat(topology/topological_fiber_bundle): topological fiber bundles
* better definition of fiber bundles
#### Estimated changes
Added src/topology/topological_fiber_bundle.lean
- \+ *lemma* bundle_trivialization.continuous_at_proj
- \+ *structure* bundle_trivialization
- \+ *lemma* is_topological_fiber_bundle.continuous_proj
- \+ *lemma* is_topological_fiber_bundle.is_open_map_proj
- \+ *def* is_topological_fiber_bundle
- \+ *lemma* is_topological_fiber_bundle_fst
- \+ *lemma* is_topological_fiber_bundle_snd
- \+ *def* topological_fiber_bundle_core.base
- \+ *lemma* topological_fiber_bundle_core.continuous_proj
- \+ *def* topological_fiber_bundle_core.fiber
- \+ *def* topological_fiber_bundle_core.index
- \+ *lemma* topological_fiber_bundle_core.is_open_map_proj
- \+ *theorem* topological_fiber_bundle_core.is_topological_fiber_bundle
- \+ *def* topological_fiber_bundle_core.local_triv'
- \+ *lemma* topological_fiber_bundle_core.local_triv'_fst
- \+ *lemma* topological_fiber_bundle_core.local_triv'_inv_fst
- \+ *lemma* topological_fiber_bundle_core.local_triv'_trans
- \+ *def* topological_fiber_bundle_core.local_triv
- \+ *def* topological_fiber_bundle_core.local_triv_at
- \+ *def* topological_fiber_bundle_core.local_triv_at_ext
- \+ *lemma* topological_fiber_bundle_core.local_triv_at_ext_to_local_homeomorph
- \+ *lemma* topological_fiber_bundle_core.local_triv_at_fst
- \+ *lemma* topological_fiber_bundle_core.local_triv_at_symm_fst
- \+ *def* topological_fiber_bundle_core.local_triv_ext
- \+ *lemma* topological_fiber_bundle_core.local_triv_fst
- \+ *lemma* topological_fiber_bundle_core.local_triv_symm_fst
- \+ *lemma* topological_fiber_bundle_core.local_triv_trans
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv'_source
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv'_target
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv_at_source
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv_source
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv_target
- \+ *lemma* topological_fiber_bundle_core.mem_triv_change_source
- \+ *lemma* topological_fiber_bundle_core.open_source'
- \+ *lemma* topological_fiber_bundle_core.open_target'
- \+ *def* topological_fiber_bundle_core.proj
- \+ *def* topological_fiber_bundle_core.total_space
- \+ *def* topological_fiber_bundle_core.triv_change
- \+ *structure* topological_fiber_bundle_core



## [2019-10-21 08:23:05](https://github.com/leanprover-community/mathlib/commit/d2d29ff)
feat(algebra/geom_sum): sum of a geom_series over an Ico ([#1573](https://github.com/leanprover-community/mathlib/pull/1573))
* feat(algebra/geom_sum): sum of a geom_series over an Ico
* Add two more versions as requested by @jcommelin
#### Estimated changes
Modified src/algebra/geom_sum.lean
- \+ *theorem* geom_sum_Ico
- \+ *theorem* geom_sum_Ico_mul
- \+ *theorem* geom_sum_Ico_mul_neg



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
- \+ *lemma* dist_le_Ico_sum_of_dist_le
- \+ *lemma* dist_le_range_sum_dist
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
- \+/\- *lemma* option.eq_some_iff_get_eq

Modified src/data/option/defs.lean


Modified src/tactic/basic.lean


Modified src/tactic/core.lean


Deleted src/tactic/library_search.lean
- \- *def* tactic.library_search.head_symbol_match.to_string
- \- *inductive* tactic.library_search.head_symbol_match

Modified src/tactic/rewrite_all/congr.lean


Added src/tactic/suggest.lean
- \+ *def* tactic.suggest.head_symbol_match.to_string
- \+ *inductive* tactic.suggest.head_symbol_match

Modified test/library_search/basic.lean


Modified test/library_search/ordered_ring.lean


Modified test/library_search/ring_theory.lean


Modified test/mllist.lean


Added test/suggest.lean




## [2019-10-19 22:11:22](https://github.com/leanprover-community/mathlib/commit/f544632)
feat(algebra/big_operators): products and sums over `finset.Ico` ([#1567](https://github.com/leanprover-community/mathlib/pull/1567))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_Ico_add
- \+ *lemma* finset.prod_Ico_consecutive
- \+ *lemma* finset.prod_Ico_eq_div
- \+ *lemma* finset.prod_Ico_eq_prod_range
- \+ *lemma* finset.prod_range_mul_prod_Ico
- \+ *lemma* finset.sum_Ico_add
- \+ *lemma* finset.sum_Ico_eq_sub

Modified src/data/finset.lean
- \+ *lemma* finset.Ico.disjoint_consecutive
- \+/\- *lemma* finset.Ico.inter_consecutive
- \+/\- *theorem* finset.Ico.self_eq_empty
- \+/\- *theorem* finset.Ico.succ_singleton



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
- \+/\- *def* functor.const

Modified src/measure_theory/l1_space.lean


Modified src/meta/rb_map.lean


Modified src/tactic/basic.lean


Modified src/tactic/core.lean


Deleted src/tactic/doc_blame.lean


Modified src/tactic/interactive.lean
- \+/\- *lemma* tactic.interactive.{u}

Added src/tactic/lint.lean


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
- \+/\- *def* category_theory.cocones
- \- *lemma* category_theory.cocones_map
- \- *lemma* category_theory.cocones_obj
- \+/\- *def* category_theory.cones
- \- *lemma* category_theory.cones_map
- \- *lemma* category_theory.cones_obj
- \+/\- *def* category_theory.limits.cocone.whisker
- \- *lemma* category_theory.limits.cocone.whisker_ι_app
- \- *lemma* category_theory.limits.cocones.comp.hom
- \+/\- *def* category_theory.limits.cocones.ext
- \- *lemma* category_theory.limits.cocones.ext_hom_hom
- \+/\- *def* category_theory.limits.cocones.forget
- \- *lemma* category_theory.limits.cocones.forget_map
- \- *lemma* category_theory.limits.cocones.forget_obj
- \+/\- *def* category_theory.limits.cocones.functoriality
- \- *lemma* category_theory.limits.cocones.id.hom
- \+/\- *def* category_theory.limits.cocones.precompose
- \- *lemma* category_theory.limits.cocones.precompose_map_hom
- \- *lemma* category_theory.limits.cocones.precompose_obj_X
- \- *lemma* category_theory.limits.cocones.precompose_obj_ι
- \+/\- *def* category_theory.limits.cone.whisker
- \- *lemma* category_theory.limits.cone.whisker_π_app
- \- *lemma* category_theory.limits.cones.comp.hom
- \+/\- *def* category_theory.limits.cones.ext
- \- *lemma* category_theory.limits.cones.ext_hom_hom
- \+/\- *def* category_theory.limits.cones.forget
- \- *lemma* category_theory.limits.cones.forget_map
- \- *lemma* category_theory.limits.cones.forget_obj
- \+/\- *def* category_theory.limits.cones.functoriality
- \- *lemma* category_theory.limits.cones.id.hom
- \+/\- *def* category_theory.limits.cones.postcompose
- \- *lemma* category_theory.limits.cones.postcompose_map_hom
- \- *lemma* category_theory.limits.cones.postcompose_obj_X
- \- *lemma* category_theory.limits.cones.postcompose_obj_π

Modified src/category_theory/limits/functor_category.lean
- \+/\- *def* category_theory.limits.functor_category_colimit_cocone
- \+/\- *def* category_theory.limits.functor_category_limit_cone

Modified src/category_theory/limits/over.lean
- \+/\- *def* category_theory.functor.to_cocone
- \- *lemma* category_theory.functor.to_cocone_X
- \- *lemma* category_theory.functor.to_cocone_ι
- \+/\- *def* category_theory.functor.to_cone
- \- *lemma* category_theory.functor.to_cone_X
- \- *lemma* category_theory.functor.to_cone_π
- \+/\- *def* category_theory.over.colimit
- \- *lemma* category_theory.over.colimit_X_hom
- \- *lemma* category_theory.over.colimit_ι_app
- \+/\- *def* category_theory.under.limit
- \- *lemma* category_theory.under.limit_X_hom
- \- *lemma* category_theory.under.limit_π_app

Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/algebra.lean
- \- *lemma* category_theory.monad.algebra.comp_f
- \+/\- *def* category_theory.monad.algebra.hom.comp
- \- *lemma* category_theory.monad.algebra.hom.comp_f
- \+/\- *def* category_theory.monad.algebra.hom.id
- \- *lemma* category_theory.monad.algebra.hom.id_f
- \- *lemma* category_theory.monad.algebra.id_f
- \+/\- *def* category_theory.monad.forget
- \- *lemma* category_theory.monad.forget_map
- \+/\- *def* category_theory.monad.free
- \- *lemma* category_theory.monad.free_map_f
- \- *lemma* category_theory.monad.free_obj_a

Modified src/category_theory/monad/limits.lean
- \+/\- *def* category_theory.monad.forget_creates_limits.c
- \- *lemma* category_theory.monad.forget_creates_limits.c_π
- \+/\- *def* category_theory.monad.forget_creates_limits.cone_point
- \- *lemma* category_theory.monad.forget_creates_limits.cone_point_a
- \+/\- *def* category_theory.monad.forget_creates_limits.γ
- \- *lemma* category_theory.monad.forget_creates_limits.γ_app

Modified src/category_theory/monoidal/functor.lean
- \+/\- *def* category_theory.lax_monoidal_functor.comp
- \- *lemma* category_theory.lax_monoidal_functor.comp_map
- \- *lemma* category_theory.lax_monoidal_functor.comp_obj
- \- *lemma* category_theory.lax_monoidal_functor.comp_ε
- \- *lemma* category_theory.lax_monoidal_functor.comp_μ
- \+/\- *def* category_theory.monoidal_functor.id
- \- *lemma* category_theory.monoidal_functor.id_map
- \- *lemma* category_theory.monoidal_functor.id_obj
- \- *lemma* category_theory.monoidal_functor.id_ε
- \- *lemma* category_theory.monoidal_functor.id_μ

Modified src/category_theory/whiskering.lean
- \+/\- *def* category_theory.functor.associator
- \- *lemma* category_theory.functor.associator_hom_app
- \- *lemma* category_theory.functor.associator_inv_app
- \+/\- *def* category_theory.functor.left_unitor
- \- *lemma* category_theory.functor.left_unitor_hom_app
- \- *lemma* category_theory.functor.left_unitor_inv_app
- \+/\- *def* category_theory.functor.right_unitor
- \- *lemma* category_theory.functor.right_unitor_hom_app
- \- *lemma* category_theory.functor.right_unitor_inv_app

Modified src/category_theory/yoneda.lean
- \- *lemma* category_theory.coyoneda.map_app
- \- *lemma* category_theory.coyoneda.obj_map
- \- *lemma* category_theory.coyoneda.obj_obj
- \+/\- *def* category_theory.coyoneda
- \- *lemma* category_theory.yoneda.map_app
- \- *lemma* category_theory.yoneda.obj_map
- \- *lemma* category_theory.yoneda.obj_obj
- \+/\- *def* category_theory.yoneda



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
- \+ *def* category_theory.groupoid.iso_equiv_hom

Added src/category_theory/isomorphism_classes.lean
- \+ *lemma* category_theory.groupoid.is_isomorphic_iff_nonempty_hom
- \+ *def* category_theory.is_isomorphic
- \+ *def* category_theory.is_isomorphic_setoid
- \+ *def* category_theory.isomorphism_classes



## [2019-10-17 20:03:17](https://github.com/leanprover-community/mathlib/commit/e5fc2a7)
refactor(topology,calculus): change subset condition for composition ([#1549](https://github.com/leanprover-community/mathlib/pull/1549))
* refactor(topology,calculus): change subset condition for composition
* improve docstrings
* add is_open Ioi
* reviewer's comments
* typo
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* differentiable_on.congr
- \+ *lemma* differentiable_within_at.congr
- \+ *lemma* differentiable_within_at_inter'
- \+/\- *theorem* has_fderiv_within_at.comp
- \+ *lemma* has_fderiv_within_at.image_tangent_cone_subset
- \+ *theorem* has_fderiv_within_at.lim
- \+ *lemma* has_fderiv_within_at.unique_diff_within_at

Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean
- \+ *lemma* unique_diff_on.inter
- \- *lemma* unique_diff_on_inter
- \+ *lemma* unique_diff_within_at.inter'
- \+ *lemma* unique_diff_within_at_inter'

Modified src/analysis/calculus/times_cont_diff.lean


Modified src/data/equiv/local_equiv.lean


Modified src/data/set/basic.lean
- \+ *theorem* set.prod_range_univ_eq
- \+ *lemma* set.prod_subset_preimage_fst
- \+ *lemma* set.prod_subset_preimage_snd
- \+ *theorem* set.prod_univ_range_eq
- \+ *theorem* set.subset_preimage_univ

Modified src/geometry/manifold/manifold.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* is_open_Ioi

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.congr
- \+ *lemma* continuous_within_at.congr
- \+ *lemma* continuous_within_at.mem_closure_image
- \+ *lemma* continuous_within_at.preimage_mem_nhds_within'
- \+ *lemma* mem_closure_iff_nhds_within_ne_bot
- \+ *lemma* mem_nhds_within_of_mem_nhds

Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.continuous_at_iff_continuous_at_comp_left
- \+ *lemma* local_homeomorph.continuous_at_iff_continuous_at_comp_right
- \+ *lemma* local_homeomorph.continuous_at_inv_fun
- \+ *lemma* local_homeomorph.continuous_at_to_fun
- \+/\- *lemma* local_homeomorph.continuous_on_iff_continuous_on_comp_left
- \+ *lemma* local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_left
- \+ *lemma* local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_right
- \+ *lemma* local_homeomorph.image_open_of_open
- \+ *lemma* local_homeomorph.to_homeomorph_inv_fun
- \+ *def* local_homeomorph.to_homeomorph_of_source_eq_univ_target_eq_univ
- \+ *lemma* local_homeomorph.to_homeomorph_to_fun



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
- \+/\- *lemma* finset.sup_le_iff
- \- *lemma* finset.sup_lt
- \+ *lemma* finset.sup_lt_iff

Modified src/order/filter/basic.lean
- \+ *lemma* filter.Inter_mem_sets_of_fintype
- \+ *lemma* filter.infi_principal_finset
- \+ *lemma* filter.infi_principal_fintype

Modified src/topology/metric_space/basic.lean
- \+ *def* emetric_space.to_metric_space_of_dist

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
- \+/\- *lemma* polynomial.degree_map'
- \+/\- *lemma* polynomial.degree_map_eq_of_injective
- \+ *lemma* polynomial.leading_coeff_of_injective
- \+ *lemma* polynomial.map_injective
- \+/\- *lemma* polynomial.map_pow
- \+ *lemma* polynomial.mem_map_range
- \+ *lemma* polynomial.monic.ne_zero
- \+ *lemma* polynomial.monic.ne_zero_of_zero_ne_one
- \+ *lemma* polynomial.monic_of_injective
- \+/\- *lemma* polynomial.nat_degree_map'

Modified src/field_theory/minimal_polynomial.lean


Added src/ring_theory/algebraic.lean
- \+ *def* algebra.is_algebraic
- \+ *lemma* algebra.is_algebraic_iff
- \+ *lemma* algebra.is_algebraic_trans
- \+ *def* is_algebraic
- \+ *lemma* is_algebraic_iff_is_integral
- \+ *lemma* is_integral.is_algebraic
- \+ *def* subalgebra.is_algebraic
- \+ *def* subalgebra.is_algebraic_iff

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* algebra.is_integral_trans
- \+/\- *theorem* is_integral_of_mem_of_fg
- \+/\- *theorem* is_integral_of_noetherian
- \+ *lemma* is_integral_trans
- \+ *lemma* is_integral_trans_aux



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
Added archive/imo1988_q6.lean
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
- \+ *theorem* finset.card_eq_sum_card_image
- \+ *theorem* finset.card_le_mul_card_image

Modified src/data/polynomial.lean
- \+ *lemma* polynomial.card_roots_sub_C'
- \+ *lemma* polynomial.card_roots_sub_C
- \+ *lemma* polynomial.degree_add_C
- \+ *lemma* polynomial.mem_roots_sub_C
- \+ *lemma* polynomial.nat_degree_neg

Modified src/field_theory/finite.lean
- \+ *lemma* finite_field.card_image_polynomial_eval
- \+ *lemma* finite_field.exists_root_sum_quadratic



## [2019-10-16 03:46:48](https://github.com/leanprover-community/mathlib/commit/09fd631)
feat(data/zmod/basic): val_min_abs ([#1548](https://github.com/leanprover-community/mathlib/pull/1548))
* feat(data/zmod/basic): val_min_abs
* Update basic.lean
* docstring and fix `zmodp` versions
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.coe_val_min_abs
- \+ *lemma* zmod.nat_abs_val_min_abs_le
- \+ *def* zmod.val_min_abs
- \+ *lemma* zmod.val_min_abs_eq_zero
- \+ *lemma* zmod.val_min_abs_zero
- \+ *lemma* zmodp.coe_val_min_abs
- \+ *lemma* zmodp.nat_abs_val_min_abs_le
- \+ *def* zmodp.val_min_abs
- \+ *lemma* zmodp.val_min_abs_eq_zero
- \+ *lemma* zmodp.val_min_abs_zero



## [2019-10-14 12:13:21](https://github.com/leanprover-community/mathlib/commit/c3d1bd7)
feat(data/polynomial): card_roots' ([#1546](https://github.com/leanprover-community/mathlib/pull/1546))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.card_roots'



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
- \+ *lemma* int.nat_abs_eq_zero



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
- \- *lemma* closed_of_compact
- \- *lemma* compact_compact_separated
- \- *lemma* compact_iff_compact_image_of_embedding
- \- *lemma* compact_iff_compact_in_subtype
- \- *lemma* compact_iff_compact_space
- \- *lemma* compact_iff_compact_univ
- \- *lemma* compact_pi_infinite
- \- *lemma* compact_prod
- \- *def* dense_embedding.subtype_emb
- \- *lemma* dense_range_prod
- \- *lemma* diagonal_eq_range_diagonal_map
- \+ *lemma* embedding.prod_mk
- \- *lemma* generalized_tube_lemma
- \- *lemma* homeomorph.coe_eq_to_equiv
- \- *lemma* homeomorph.coinduced_eq
- \- *lemma* homeomorph.compact_image
- \- *lemma* homeomorph.compact_preimage
- \- *def* homeomorph.homeomorph_of_continuous_open
- \- *lemma* homeomorph.image_symm
- \- *lemma* homeomorph.induced_eq
- \- *lemma* homeomorph.preimage_symm
- \- *def* homeomorph.prod_assoc
- \- *def* homeomorph.prod_comm
- \- *def* homeomorph.prod_congr
- \- *lemma* homeomorph.range_coe
- \- *lemma* homeomorph.self_comp_symm
- \- *def* homeomorph.sigma_prod_distrib
- \- *lemma* homeomorph.symm_comp_self
- \- *structure* homeomorph
- \+ *lemma* inducing.prod_mk
- \- *lemma* is_closed_diagonal
- \- *lemma* is_closed_eq
- \- *lemma* is_closed_property2
- \- *lemma* is_closed_property3
- \- *lemma* is_closed_property
- \+/\- *lemma* is_open_prod_iff'
- \- *lemma* locally_compact_of_compact_nhds
- \+ *theorem* mem_nhds_subtype
- \- *lemma* nhds_contain_boxes.comm
- \- *lemma* nhds_contain_boxes.symm
- \- *def* nhds_contain_boxes
- \- *lemma* nhds_contain_boxes_of_compact
- \- *lemma* nhds_contain_boxes_of_singleton
- \+ *theorem* nhds_subtype
- \- *lemma* normal_of_compact_t2
- \- *lemma* prod_subset_compl_diagonal_iff_disjoint
- \+ *lemma* quotient_dense_of_dense
- \+ *lemma* subtype_val.closed_embedding
- \+ *lemma* subtype_val.open_embedding

Modified src/topology/dense_embedding.lean
- \+ *def* dense_embedding.subtype_emb
- \+ *lemma* dense_range_prod
- \+ *lemma* is_closed_property2
- \+ *lemma* is_closed_property3
- \+ *lemma* is_closed_property

Added src/topology/homeomorph.lean
- \+ *lemma* homeomorph.coe_eq_to_equiv
- \+ *lemma* homeomorph.coinduced_eq
- \+ *lemma* homeomorph.compact_image
- \+ *lemma* homeomorph.compact_preimage
- \+ *def* homeomorph.homeomorph_of_continuous_open
- \+ *lemma* homeomorph.image_symm
- \+ *lemma* homeomorph.induced_eq
- \+ *lemma* homeomorph.preimage_symm
- \+ *def* homeomorph.prod_assoc
- \+ *def* homeomorph.prod_comm
- \+ *def* homeomorph.prod_congr
- \+ *lemma* homeomorph.range_coe
- \+ *lemma* homeomorph.self_comp_symm
- \+ *def* homeomorph.sigma_prod_distrib
- \+ *lemma* homeomorph.symm_comp_self
- \+ *structure* homeomorph

Modified src/topology/local_homeomorph.lean


Modified src/topology/maps.lean
- \- *lemma* embedding.prod_mk
- \- *lemma* inducing.prod_mk
- \- *lemma* subtype_val.closed_embedding
- \- *lemma* subtype_val.open_embedding

Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/opens.lean


Modified src/topology/order.lean
- \- *theorem* mem_nhds_subtype
- \- *theorem* nhds_subtype
- \- *lemma* quotient_dense_of_dense

Modified src/topology/separation.lean
- \+ *lemma* closed_of_compact
- \+ *lemma* compact_compact_separated
- \+ *lemma* diagonal_eq_range_diagonal_map
- \+ *lemma* is_closed_diagonal
- \+ *lemma* is_closed_eq
- \+ *lemma* locally_compact_of_compact_nhds
- \+ *lemma* normal_of_compact_t2
- \+ *lemma* prod_subset_compl_diagonal_iff_disjoint

Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean
- \+ *lemma* compact_iff_compact_image_of_embedding
- \+ *lemma* compact_iff_compact_in_subtype
- \+ *lemma* compact_iff_compact_space
- \+ *lemma* compact_iff_compact_univ
- \+/\- *lemma* compact_image
- \+ *lemma* compact_pi_infinite
- \+ *lemma* compact_prod
- \+/\- *lemma* compact_range
- \+ *lemma* generalized_tube_lemma
- \+ *lemma* nhds_contain_boxes.comm
- \+ *lemma* nhds_contain_boxes.symm
- \+ *def* nhds_contain_boxes
- \+ *lemma* nhds_contain_boxes_of_compact
- \+ *lemma* nhds_contain_boxes_of_singleton

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
- \+/\- *lemma* uniform_space.completion.is_add_group_hom_map



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
- \+ *lemma* ring_hom.comp_apply
- \+ *lemma* ring_hom.id_apply

Modified src/ring_theory/algebra.lean
- \+/\- *def* alg_hom.comp



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
- \+/\- *lemma* coe_add_monoid_hom
- \+/\- *lemma* coe_monoid_hom



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
- \+/\- *def* equiv.to_linear_equiv
- \+/\- *lemma* finset.smul_sum
- \+/\- *lemma* finsupp.smul_sum
- \+/\- *lemma* is_linear_map.is_linear_map_add
- \+/\- *lemma* is_linear_map.is_linear_map_sub
- \+/\- *theorem* linear_equiv.apply_symm_apply
- \+/\- *def* linear_equiv.arrow_congr
- \+/\- *theorem* linear_equiv.coe_apply
- \+/\- *def* linear_equiv.congr_right
- \+/\- *def* linear_equiv.conj
- \+/\- *lemma* linear_equiv.eq_bot_of_equiv
- \+/\- *lemma* linear_equiv.ext
- \+/\- *theorem* linear_equiv.of_bijective_apply
- \+/\- *def* linear_equiv.of_linear
- \+/\- *theorem* linear_equiv.of_linear_apply
- \+/\- *theorem* linear_equiv.of_linear_symm_apply
- \+/\- *def* linear_equiv.of_top
- \+/\- *theorem* linear_equiv.of_top_apply
- \+/\- *theorem* linear_equiv.of_top_symm_apply
- \+/\- *def* linear_equiv.refl
- \+/\- *def* linear_equiv.smul_of_ne_zero
- \+/\- *def* linear_equiv.smul_of_unit
- \+/\- *def* linear_equiv.symm
- \+/\- *theorem* linear_equiv.symm_apply_apply
- \+/\- *lemma* linear_equiv.to_equiv_injective
- \+/\- *def* linear_equiv.trans
- \+/\- *structure* linear_equiv
- \+/\- *lemma* linear_map.add_apply
- \+/\- *def* linear_map.cod_restrict
- \+/\- *theorem* linear_map.cod_restrict_apply
- \+/\- *theorem* linear_map.comap_cod_restrict
- \+/\- *theorem* linear_map.comap_injective
- \+/\- *theorem* linear_map.comap_le_comap_iff
- \+/\- *lemma* linear_map.comap_map_eq
- \+/\- *lemma* linear_map.comap_map_eq_self
- \+/\- *theorem* linear_map.comap_pair_prod
- \+/\- *theorem* linear_map.comp_assoc
- \+/\- *lemma* linear_map.comp_cod_restrict
- \+/\- *theorem* linear_map.comp_smul
- \+/\- *theorem* linear_map.comp_zero
- \+/\- *def* linear_map.congr_right
- \+/\- *def* linear_map.copair
- \+/\- *theorem* linear_map.copair_apply
- \+/\- *theorem* linear_map.copair_inl
- \+/\- *theorem* linear_map.copair_inl_inr
- \+/\- *theorem* linear_map.copair_inr
- \+/\- *def* linear_map.diag
- \+/\- *lemma* linear_map.disjoint_inl_inr
- \+/\- *theorem* linear_map.disjoint_ker'
- \+/\- *theorem* linear_map.disjoint_ker
- \+/\- *lemma* linear_map.finsupp_sum
- \+/\- *def* linear_map.fst
- \+/\- *theorem* linear_map.fst_apply
- \+/\- *theorem* linear_map.fst_eq_copair
- \+/\- *theorem* linear_map.fst_pair
- \+/\- *def* linear_map.general_linear_group.general_linear_equiv
- \+/\- *lemma* linear_map.general_linear_group.general_linear_equiv_to_linear_map
- \+/\- *def* linear_map.general_linear_group.of_linear_equiv
- \+/\- *def* linear_map.general_linear_group.to_linear_equiv
- \+/\- *def* linear_map.general_linear_group
- \+/\- *lemma* linear_map.infi_ker_proj
- \+/\- *theorem* linear_map.inj_of_disjoint_ker
- \+/\- *def* linear_map.inl
- \+/\- *theorem* linear_map.inl_apply
- \+/\- *theorem* linear_map.inl_eq_pair
- \+/\- *def* linear_map.inr
- \+/\- *theorem* linear_map.inr_apply
- \+/\- *theorem* linear_map.inr_eq_pair
- \+/\- *def* linear_map.inverse
- \+/\- *lemma* linear_map.is_linear_map_prod_iso
- \+/\- *def* linear_map.ker
- \+/\- *lemma* linear_map.ker_cod_restrict
- \+/\- *theorem* linear_map.ker_comp
- \+/\- *theorem* linear_map.ker_eq_bot'
- \+/\- *theorem* linear_map.ker_eq_bot
- \+/\- *theorem* linear_map.ker_eq_top
- \+/\- *theorem* linear_map.ker_id
- \+/\- *theorem* linear_map.ker_le_ker_comp
- \+/\- *lemma* linear_map.ker_pair
- \+/\- *lemma* linear_map.ker_pi
- \+/\- *lemma* linear_map.ker_smul'
- \+/\- *lemma* linear_map.ker_smul
- \+/\- *lemma* linear_map.ker_std_basis
- \+/\- *theorem* linear_map.ker_zero
- \+/\- *lemma* linear_map.le_ker_iff_map
- \+/\- *theorem* linear_map.map_cod_restrict
- \+/\- *lemma* linear_map.map_comap_eq
- \+/\- *lemma* linear_map.map_comap_eq_self
- \+/\- *theorem* linear_map.map_copair_prod
- \+/\- *theorem* linear_map.map_injective
- \+/\- *theorem* linear_map.map_le_map_iff
- \+/\- *lemma* linear_map.map_le_range
- \+/\- *theorem* linear_map.mem_ker
- \+/\- *theorem* linear_map.mem_range
- \+/\- *lemma* linear_map.mul_app
- \+/\- *lemma* linear_map.neg_apply
- \+/\- *lemma* linear_map.one_app
- \+/\- *def* linear_map.pair
- \+/\- *theorem* linear_map.pair_apply
- \+/\- *theorem* linear_map.pair_fst_snd
- \+/\- *def* linear_map.pi
- \+/\- *lemma* linear_map.pi_apply
- \+/\- *lemma* linear_map.pi_comp
- \+/\- *lemma* linear_map.pi_eq_zero
- \+/\- *lemma* linear_map.pi_zero
- \+/\- *def* linear_map.prod
- \+/\- *theorem* linear_map.prod_eq_inf_comap
- \+/\- *theorem* linear_map.prod_eq_sup_map
- \+/\- *def* linear_map.proj
- \+/\- *lemma* linear_map.proj_apply
- \+/\- *lemma* linear_map.proj_comp_std_basis
- \+/\- *lemma* linear_map.proj_pi
- \+/\- *lemma* linear_map.proj_std_basis_ne
- \+/\- *lemma* linear_map.proj_std_basis_same
- \+/\- *def* linear_map.range
- \+/\- *lemma* linear_map.range_cod_restrict
- \+/\- *theorem* linear_map.range_coe
- \+/\- *theorem* linear_map.range_comp
- \+/\- *theorem* linear_map.range_comp_le_range
- \+/\- *theorem* linear_map.range_eq_top
- \+/\- *theorem* linear_map.range_id
- \+/\- *lemma* linear_map.range_le_bot_iff
- \+/\- *lemma* linear_map.range_le_iff_comap
- \+/\- *lemma* linear_map.range_smul'
- \+/\- *lemma* linear_map.range_smul
- \+/\- *theorem* linear_map.range_zero
- \+/\- *def* linear_map.scalar_prod_space_iso
- \+/\- *lemma* linear_map.smul_apply
- \+/\- *theorem* linear_map.smul_comp
- \+/\- *def* linear_map.smul_right
- \+/\- *theorem* linear_map.smul_right_apply
- \+/\- *def* linear_map.snd
- \+/\- *theorem* linear_map.snd_apply
- \+/\- *theorem* linear_map.snd_eq_copair
- \+/\- *theorem* linear_map.snd_pair
- \+/\- *lemma* linear_map.span_inl_union_inr
- \+/\- *def* linear_map.std_basis
- \+/\- *lemma* linear_map.std_basis_apply
- \+/\- *lemma* linear_map.std_basis_eq_single
- \+/\- *lemma* linear_map.std_basis_ne
- \+/\- *lemma* linear_map.std_basis_same
- \+/\- *lemma* linear_map.sub_apply
- \+/\- *theorem* linear_map.sub_mem_ker_iff
- \+/\- *lemma* linear_map.subtype_comp_cod_restrict
- \+/\- *lemma* linear_map.sum_apply
- \+/\- *def* linear_map.sup_quotient_to_quotient_inf
- \+/\- *lemma* linear_map.supr_range_std_basis
- \+/\- *lemma* linear_map.update_apply
- \+/\- *lemma* linear_map.zero_apply
- \+/\- *theorem* linear_map.zero_comp
- \+/\- *theorem* submodule.Inf_coe
- \+/\- *lemma* submodule.add_eq_sup
- \+/\- *lemma* submodule.bot_coe
- \+/\- *def* submodule.comap
- \+/\- *theorem* submodule.comap_bot
- \+/\- *lemma* submodule.comap_coe
- \+/\- *lemma* submodule.comap_comp
- \+/\- *theorem* submodule.comap_fst
- \+/\- *lemma* submodule.comap_inf
- \+/\- *lemma* submodule.comap_infi
- \+/\- *theorem* submodule.comap_liftq
- \+/\- *lemma* submodule.comap_mkq_embedding_eq
- \+/\- *lemma* submodule.comap_mono
- \+/\- *lemma* submodule.comap_smul'
- \+/\- *lemma* submodule.comap_smul
- \+/\- *theorem* submodule.comap_snd
- \+/\- *lemma* submodule.comap_top
- \+/\- *lemma* submodule.comap_zero
- \+/\- *theorem* submodule.disjoint_def
- \+/\- *lemma* submodule.disjoint_iff_comap_eq_bot
- \+/\- *lemma* submodule.eq_bot_of_zero_eq_one
- \+/\- *lemma* submodule.eq_top_iff'
- \+/\- *lemma* submodule.eq_zero_of_bot_submodule
- \+/\- *lemma* submodule.gc_map_comap
- \+/\- *theorem* submodule.inf_coe
- \+/\- *theorem* submodule.infi_coe
- \+/\- *theorem* submodule.ker_inl
- \+/\- *theorem* submodule.ker_inr
- \+/\- *theorem* submodule.ker_liftq
- \+/\- *theorem* submodule.ker_liftq_eq_bot
- \+/\- *theorem* submodule.ker_of_le
- \+/\- *lemma* submodule.le_comap_map
- \+/\- *lemma* submodule.le_comap_mkq
- \+/\- *lemma* submodule.le_def'
- \+/\- *lemma* submodule.le_def
- \+/\- *def* submodule.liftq
- \+/\- *theorem* submodule.liftq_apply
- \+/\- *theorem* submodule.liftq_mkq
- \+/\- *lemma* submodule.linear_eq_on
- \+/\- *def* submodule.map
- \+/\- *lemma* submodule.map_bot
- \+/\- *lemma* submodule.map_coe
- \+/\- *lemma* submodule.map_comap_le
- \+/\- *lemma* submodule.map_comp
- \+/\- *lemma* submodule.map_inf_eq_map_inf_comap
- \+/\- *theorem* submodule.map_inl
- \+/\- *theorem* submodule.map_inr
- \+/\- *lemma* submodule.map_le_iff_le_comap
- \+/\- *theorem* submodule.map_liftq
- \+/\- *lemma* submodule.map_mono
- \+/\- *lemma* submodule.map_smul'
- \+/\- *lemma* submodule.map_smul
- \+/\- *lemma* submodule.map_subtype_embedding_eq
- \+/\- *lemma* submodule.map_subtype_le
- \+/\- *lemma* submodule.map_sup
- \+/\- *lemma* submodule.map_supr
- \+/\- *theorem* submodule.map_top
- \+/\- *lemma* submodule.map_zero
- \+/\- *def* submodule.mapq
- \+/\- *theorem* submodule.mapq_apply
- \+/\- *theorem* submodule.mapq_mkq
- \+/\- *theorem* submodule.mem_Sup_of_directed
- \+/\- *lemma* submodule.mem_bot
- \+/\- *lemma* submodule.mem_comap
- \+/\- *theorem* submodule.mem_inf
- \+/\- *theorem* submodule.mem_infi
- \+/\- *lemma* submodule.mem_map
- \+/\- *theorem* submodule.mem_map_of_mem
- \+/\- *lemma* submodule.mem_prod
- \+/\- *lemma* submodule.mem_span
- \+/\- *lemma* submodule.mem_span_insert'
- \+/\- *lemma* submodule.mem_span_insert
- \+/\- *lemma* submodule.mem_span_singleton
- \+/\- *lemma* submodule.mem_supr_of_mem
- \+/\- *lemma* submodule.mem_top
- \+/\- *def* submodule.mkq
- \+/\- *theorem* submodule.mkq_apply
- \+/\- *def* submodule.of_le
- \+/\- *theorem* submodule.of_le_apply
- \+/\- *def* submodule.prod
- \+/\- *lemma* submodule.prod_bot
- \+/\- *theorem* submodule.prod_comap_inl
- \+/\- *theorem* submodule.prod_comap_inr
- \+/\- *theorem* submodule.prod_map_fst
- \+/\- *theorem* submodule.prod_map_snd
- \+/\- *lemma* submodule.prod_mono
- \+/\- *lemma* submodule.prod_top
- \+/\- *theorem* submodule.quotient.mk'_eq_mk
- \+/\- *def* submodule.quotient.mk
- \+/\- *theorem* submodule.quotient.mk_eq_mk
- \+/\- *theorem* submodule.quotient.quot_mk_eq_mk
- \+/\- *def* submodule.quotient_rel
- \+/\- *theorem* submodule.range_fst
- \+/\- *theorem* submodule.range_liftq
- \+/\- *lemma* submodule.range_of_le
- \+/\- *theorem* submodule.range_snd
- \+/\- *def* submodule.span
- \+/\- *lemma* submodule.span_Union
- \+/\- *lemma* submodule.span_empty
- \+/\- *lemma* submodule.span_eq
- \+/\- *lemma* submodule.span_eq_bot
- \+/\- *lemma* submodule.span_eq_of_le
- \+/\- *lemma* submodule.span_image
- \+/\- *lemma* submodule.span_induction
- \+/\- *lemma* submodule.span_insert_eq_span
- \+/\- *lemma* submodule.span_le
- \+/\- *lemma* submodule.span_mono
- \+/\- *lemma* submodule.span_prod_le
- \+/\- *lemma* submodule.span_singleton_eq_bot
- \+/\- *lemma* submodule.span_singleton_eq_range
- \+/\- *lemma* submodule.span_span
- \+/\- *lemma* submodule.span_union
- \+/\- *lemma* submodule.span_univ
- \+/\- *lemma* submodule.subset_span
- \+/\- *lemma* submodule.subtype_comp_of_le
- \+/\- *lemma* submodule.top_coe
- \+/\- *lemma* submodule.zero_eq_bot

Modified src/linear_algebra/basis.lean
- \+/\- *lemma* constr_add
- \+/\- *lemma* constr_basis
- \+/\- *lemma* constr_eq
- \+/\- *lemma* constr_neg
- \+/\- *lemma* constr_range
- \+/\- *lemma* constr_self
- \+/\- *lemma* constr_smul
- \+/\- *lemma* constr_sub
- \+/\- *lemma* constr_zero
- \+/\- *lemma* disjoint_span_singleton
- \+/\- *lemma* eq_of_linear_independent_of_span_subtype
- \+/\- *def* equiv_fun_basis
- \+/\- *def* equiv_of_is_basis
- \+/\- *lemma* exists_is_basis
- \+/\- *lemma* exists_left_inverse_linear_map_of_injective
- \+/\- *lemma* exists_linear_independent
- \+/\- *lemma* exists_of_linear_independent_of_finite_span
- \+/\- *lemma* exists_right_inverse_linear_map_of_surjective
- \+/\- *lemma* exists_subset_is_basis
- \+/\- *lemma* is_basis.comp
- \+/\- *def* is_basis.constr
- \+/\- *theorem* is_basis.constr_apply
- \+/\- *lemma* is_basis.ext
- \+/\- *lemma* is_basis.injective
- \+/\- *lemma* is_basis.mem_span
- \+/\- *def* is_basis.repr
- \+/\- *lemma* is_basis.repr_range
- \+/\- *lemma* is_basis.repr_total
- \+/\- *lemma* is_basis.total_comp_repr
- \+/\- *lemma* is_basis.total_repr
- \+/\- *def* is_basis
- \+/\- *lemma* is_basis_empty
- \+/\- *lemma* is_basis_empty_bot
- \+/\- *lemma* is_basis_inl_union_inr
- \+/\- *lemma* is_basis_singleton_one
- \+/\- *lemma* is_basis_span
- \+/\- *lemma* le_of_span_le_span
- \+/\- *lemma* linear_equiv.is_basis
- \+/\- *lemma* linear_independent.image
- \+/\- *lemma* linear_independent.image_subtype
- \+/\- *lemma* linear_independent.injective
- \+/\- *lemma* linear_independent.insert
- \+/\- *lemma* linear_independent.mono
- \+/\- *def* linear_independent.repr
- \+/\- *lemma* linear_independent.total_comp_repr
- \+/\- *def* linear_independent.total_equiv
- \+/\- *lemma* linear_independent.total_repr
- \+/\- *lemma* linear_independent.unique
- \+/\- *def* linear_independent
- \+/\- *lemma* linear_independent_Union_finite_subtype
- \+/\- *lemma* linear_independent_bUnion_of_directed
- \+/\- *lemma* linear_independent_empty
- \+/\- *lemma* linear_independent_empty_type
- \+/\- *theorem* linear_independent_iff
- \+/\- *lemma* linear_independent_iff_not_mem_span
- \+/\- *theorem* linear_independent_iff_total_on
- \+/\- *lemma* linear_independent_inl_union_inr'
- \+/\- *lemma* linear_independent_inl_union_inr
- \+/\- *lemma* linear_independent_of_finite
- \+/\- *lemma* linear_independent_of_zero_eq_one
- \+/\- *lemma* linear_independent_sUnion_of_directed
- \+/\- *lemma* linear_independent_singleton
- \+/\- *lemma* linear_independent_span
- \+/\- *theorem* linear_independent_subtype
- \+/\- *theorem* linear_independent_subtype_disjoint
- \+/\- *lemma* linear_independent_union
- \+/\- *lemma* linear_independent_unique
- \+/\- *lemma* mem_span_insert_exchange
- \+/\- *theorem* module.card_fintype
- \+/\- *def* module_equiv_finsupp
- \+/\- *lemma* pi.is_basis_fun
- \+/\- *lemma* pi.is_basis_fun₀
- \+/\- *lemma* pi.is_basis_std_basis
- \+/\- *theorem* quotient_prod_linear_equiv
- \+/\- *lemma* span_le_span_iff
- \+/\- *theorem* vector_space.card_fintype

Modified src/linear_algebra/bilinear_form.lean
- \+/\- *def* alt_bilin_form.is_alt
- \+/\- *lemma* alt_bilin_form.neg
- \+/\- *lemma* alt_bilin_form.self_eq_zero
- \+/\- *lemma* bilin_form.add_left
- \+/\- *lemma* bilin_form.add_right
- \+/\- *def* bilin_form.bilin_linear_map_equiv
- \+/\- *lemma* bilin_form.ext
- \+/\- *def* bilin_form.is_ortho
- \+/\- *lemma* bilin_form.neg_left
- \+/\- *lemma* bilin_form.neg_right
- \+/\- *theorem* bilin_form.ortho_smul_left
- \+/\- *theorem* bilin_form.ortho_smul_right
- \+/\- *lemma* bilin_form.ortho_zero
- \+/\- *lemma* bilin_form.smul_left
- \+/\- *lemma* bilin_form.smul_right
- \+/\- *lemma* bilin_form.sub_left
- \+/\- *lemma* bilin_form.sub_right
- \+/\- *def* bilin_form.to_linear_map
- \+/\- *lemma* bilin_form.zero_left
- \+/\- *lemma* bilin_form.zero_right
- \+/\- *structure* bilin_form
- \+/\- *def* linear_map.to_bilin
- \+/\- *lemma* refl_bilin_form.eq_zero
- \+/\- *def* refl_bilin_form.is_refl
- \+/\- *lemma* refl_bilin_form.ortho_sym
- \+/\- *def* sym_bilin_form.is_sym
- \+/\- *lemma* sym_bilin_form.ortho_sym
- \+/\- *lemma* sym_bilin_form.sym

Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_add_le_dim_add_dim
- \+/\- *lemma* dim_bot
- \+/\- *lemma* dim_eq_injective
- \+/\- *lemma* dim_eq_surjective
- \+/\- *lemma* dim_fin_fun
- \+/\- *lemma* dim_fun'
- \+/\- *lemma* dim_fun
- \+/\- *lemma* dim_le_injective
- \+/\- *lemma* dim_le_of_submodule
- \+/\- *lemma* dim_le_surjective
- \+/\- *lemma* dim_map_le
- \+/\- *lemma* dim_of_field
- \+/\- *lemma* dim_pi
- \+/\- *theorem* dim_prod
- \+/\- *theorem* dim_quotient
- \+/\- *theorem* dim_range_add_dim_ker
- \+/\- *lemma* dim_range_le
- \+/\- *lemma* dim_range_of_surjective
- \+/\- *lemma* dim_span
- \+/\- *lemma* dim_span_le
- \+/\- *lemma* dim_span_of_finset
- \+/\- *lemma* dim_span_set
- \+/\- *lemma* dim_submodule_le
- \+/\- *lemma* dim_sup_add_dim_inf_eq
- \+/\- *lemma* dim_top
- \+/\- *lemma* exists_is_basis_fintype
- \+/\- *lemma* exists_mem_ne_zero_of_dim_pos
- \+/\- *lemma* exists_mem_ne_zero_of_ne_bot
- \+/\- *theorem* is_basis.le_span
- \+/\- *theorem* is_basis.mk_eq_dim
- \+/\- *theorem* is_basis.mk_range_eq_dim
- \+/\- *theorem* linear_equiv.dim_eq
- \+/\- *theorem* linear_equiv.dim_eq_lift
- \+/\- *theorem* mk_eq_mk_of_basis
- \+/\- *def* rank
- \+/\- *lemma* rank_add_le
- \+/\- *lemma* rank_comp_le1
- \+/\- *lemma* rank_comp_le2
- \+/\- *lemma* rank_finset_sum_le
- \+/\- *lemma* rank_le_domain
- \+/\- *lemma* rank_le_range
- \+/\- *lemma* rank_zero

Modified src/linear_algebra/direct_sum_module.lean
- \+/\- *lemma* direct_sum.apply_eq_component
- \+/\- *lemma* direct_sum.component.lof_self
- \+/\- *lemma* direct_sum.component.of
- \+/\- *def* direct_sum.component
- \+/\- *lemma* direct_sum.ext
- \+/\- *lemma* direct_sum.ext_iff
- \+/\- *def* direct_sum.lmk
- \+/\- *def* direct_sum.lof
- \+/\- *lemma* direct_sum.lof_apply
- \+/\- *theorem* direct_sum.mk_smul
- \+/\- *theorem* direct_sum.of_smul
- \+/\- *lemma* direct_sum.single_eq_lof
- \+/\- *theorem* direct_sum.to_module.ext
- \+/\- *theorem* direct_sum.to_module.unique
- \+/\- *def* direct_sum.to_module
- \+/\- *lemma* direct_sum.to_module_lof

Modified src/linear_algebra/finsupp.lean
- \+/\- *lemma* finsupp.infi_ker_lapply_le_bot
- \+/\- *lemma* finsupp.ker_lsingle
- \+/\- *def* finsupp.lapply
- \+/\- *lemma* finsupp.lapply_apply
- \+/\- *def* finsupp.lmap_domain
- \+/\- *theorem* finsupp.lmap_domain_apply
- \+/\- *theorem* finsupp.lmap_domain_id
- \+/\- *theorem* finsupp.lmap_domain_total
- \+/\- *def* finsupp.lsingle
- \+/\- *lemma* finsupp.lsingle_apply
- \+/\- *def* finsupp.lsubtype_domain
- \+/\- *lemma* finsupp.lsubtype_domain_apply
- \+/\- *def* finsupp.lsum
- \+/\- *theorem* finsupp.lsum_apply
- \+/\- *theorem* finsupp.mem_span_iff_total
- \+/\- *lemma* finsupp.mem_supported'
- \+/\- *lemma* finsupp.mem_supported
- \+/\- *lemma* finsupp.range_total
- \+/\- *def* finsupp.restrict_dom
- \+/\- *theorem* finsupp.restrict_dom_apply
- \+/\- *lemma* finsupp.single_mem_supported
- \+/\- *lemma* finsupp.span_single_image
- \+/\- *def* finsupp.supported
- \+/\- *theorem* finsupp.supported_empty
- \+/\- *lemma* finsupp.supported_eq_span_single
- \+/\- *theorem* finsupp.supported_univ
- \+/\- *lemma* finsupp.supr_lsingle_range
- \+/\- *theorem* finsupp.total_apply
- \+/\- *theorem* finsupp.total_emb_domain
- \+/\- *theorem* finsupp.total_map_domain
- \+/\- *theorem* finsupp.total_on_range
- \+/\- *theorem* finsupp.total_range
- \+/\- *theorem* finsupp.total_single

Modified src/linear_algebra/finsupp_vector_space.lean
- \+/\- *lemma* cardinal_lt_omega_of_dim_lt_omega
- \+/\- *lemma* cardinal_mk_eq_cardinal_mk_field_pow_dim
- \+/\- *lemma* eq_bot_iff_dim_eq_zero
- \+/\- *def* equiv_of_dim_eq_dim
- \+/\- *lemma* finsupp.dim_eq
- \+/\- *lemma* finsupp.is_basis_single
- \+/\- *lemma* finsupp.linear_independent_single
- \+/\- *lemma* injective_of_surjective

Modified src/linear_algebra/matrix.lean
- \+/\- *def* lin_equiv_matrix'
- \+/\- *def* lin_equiv_matrix
- \+/\- *def* linear_map.to_matrix
- \+/\- *def* linear_map.to_matrixₗ
- \+/\- *lemma* matrix.diagonal_comp_std_basis
- \+/\- *lemma* matrix.diagonal_to_lin
- \+/\- *def* matrix.eval
- \+/\- *lemma* matrix.ker_diagonal_to_lin
- \+/\- *lemma* matrix.mul_to_lin
- \+/\- *lemma* matrix.proj_diagonal
- \+/\- *lemma* matrix.range_diagonal
- \+/\- *lemma* matrix.rank_diagonal
- \+/\- *lemma* matrix.rank_vec_mul_vec
- \+/\- *def* matrix.to_lin
- \+/\- *lemma* matrix.to_lin_add
- \+/\- *lemma* matrix.to_lin_apply
- \+/\- *lemma* matrix.to_lin_zero
- \+/\- *lemma* to_lin_to_matrix
- \+/\- *lemma* to_matrix_to_lin

Modified src/linear_algebra/sesquilinear_form.lean
- \+/\- *def* alt_sesq_form.is_alt
- \+/\- *lemma* alt_sesq_form.neg
- \+/\- *lemma* alt_sesq_form.self_eq_zero
- \+/\- *lemma* refl_sesq_form.eq_zero
- \+/\- *def* refl_sesq_form.is_refl
- \+/\- *lemma* refl_sesq_form.ortho_sym
- \+/\- *lemma* sesq_form.add_left
- \+/\- *lemma* sesq_form.add_right
- \+/\- *lemma* sesq_form.ext
- \+/\- *def* sesq_form.is_ortho
- \+/\- *lemma* sesq_form.neg_left
- \+/\- *lemma* sesq_form.neg_right
- \+/\- *theorem* sesq_form.ortho_smul_left
- \+/\- *theorem* sesq_form.ortho_smul_right
- \+/\- *lemma* sesq_form.ortho_zero
- \+/\- *lemma* sesq_form.smul_left
- \+/\- *lemma* sesq_form.smul_right
- \+/\- *lemma* sesq_form.sub_left
- \+/\- *lemma* sesq_form.sub_right
- \+/\- *lemma* sesq_form.zero_left
- \+/\- *lemma* sesq_form.zero_right
- \+/\- *structure* sesq_form
- \+/\- *lemma* sym_sesq_form.is_refl
- \+/\- *def* sym_sesq_form.is_sym
- \+/\- *lemma* sym_sesq_form.ortho_sym
- \+/\- *lemma* sym_sesq_form.sym

Modified src/linear_algebra/tensor_product.lean
- \+/\- *def* tensor_product.direct_sum



## [2019-10-10 09:00:38](https://github.com/leanprover-community/mathlib/commit/dc788a0)
feat(topology/sequences): every first-countable space is sequential ([#1528](https://github.com/leanprover-community/mathlib/pull/1528))
* feat(topology/sequences): every first-countable space is sequential
* fixup style
* fixup comments
* remove redundant type ascription
#### Estimated changes
Modified src/data/set/countable.lean
- \+ *lemma* set.countable_iff_exists_surjective_to_subtype

Modified src/order/basic.lean
- \+ *lemma* directed_of_mono

Modified src/order/complete_lattice.lean
- \+ *lemma* lattice.infi_subtype'

Modified src/topology/bases.lean
- \+ *def* filter.has_countable_basis
- \+ *lemma* filter.has_countable_basis_iff_mono_seq
- \+ *lemma* filter.has_countable_basis_iff_seq
- \+ *lemma* filter.has_countable_basis_of_seq
- \+ *lemma* filter.mono_seq_of_has_countable_basis
- \+ *lemma* filter.seq_of_has_countable_basis

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
- \+/\- *lemma* complex.norm_int_of_nonneg
- \- *lemma* exists_norm_lt_one
- \- *lemma* exists_one_lt_norm
- \- *lemma* norm_div
- \- *lemma* norm_fpow
- \- *lemma* norm_inv
- \- *lemma* norm_mul
- \- *lemma* norm_one
- \- *lemma* norm_pow
- \+/\- *lemma* norm_pow_le
- \- *lemma* norm_prod
- \+ *lemma* normed_field.exists_norm_lt_one
- \+ *lemma* normed_field.exists_one_lt_norm
- \+ *lemma* normed_field.norm_div
- \+ *lemma* normed_field.norm_fpow
- \+ *lemma* normed_field.norm_inv
- \+ *lemma* normed_field.norm_mul
- \+ *lemma* normed_field.norm_one
- \+ *lemma* normed_field.norm_pow
- \+ *lemma* normed_field.norm_prod

Modified src/analysis/normed_space/operator_norm.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean
- \+/\- *lemma* padic_norm_z.norm_one

Modified src/data/padics/padic_numbers.lean




## [2019-10-08 13:51:59](https://github.com/leanprover-community/mathlib/commit/afda1a2)
refactor(topology/continuous_on): move continuous_{on,within_at} to own file ([#1516](https://github.com/leanprover-community/mathlib/pull/1516))
* refactor(topology/continuous_on): move continuous_{on,within_at} to own file
* Update src/topology/continuous_on.lean
#### Estimated changes
Modified src/topology/algebra/monoid.lean


Modified src/topology/basic.lean
- \+ *lemma* continuous.continuous_at
- \+ *lemma* continuous_at.comp
- \+ *lemma* continuous_at.preimage_mem_nhds
- \- *def* continuous_on
- \- *def* continuous_within_at
- \- *theorem* inter_mem_nhds_within
- \- *lemma* map_nhds_within
- \- *theorem* mem_nhds_within
- \- *def* nhds_within
- \- *theorem* nhds_within_empty
- \- *theorem* nhds_within_eq
- \- *theorem* nhds_within_eq_nhds_within
- \- *theorem* nhds_within_eq_of_open
- \- *theorem* nhds_within_inter'
- \- *theorem* nhds_within_inter
- \- *theorem* nhds_within_le_of_mem
- \- *theorem* nhds_within_mono
- \- *theorem* nhds_within_restrict''
- \- *theorem* nhds_within_restrict'
- \- *theorem* nhds_within_restrict
- \- *theorem* nhds_within_union
- \- *theorem* nhds_within_univ
- \- *theorem* self_mem_nhds_within
- \- *theorem* tendsto_if_nhds_within
- \- *theorem* tendsto_nhds_within_mono_left
- \- *theorem* tendsto_nhds_within_mono_right
- \- *theorem* tendsto_nhds_within_of_tendsto_nhds

Modified src/topology/constructions.lean
- \- *lemma* continuous_on.prod
- \- *lemma* continuous_within_at.prod

Added src/topology/continuous_on.lean
- \+ *lemma* continuous.comp_continuous_on
- \+ *lemma* continuous.continuous_on
- \+ *lemma* continuous_at.continuous_within_at
- \+ *lemma* continuous_iff_continuous_on_univ
- \+ *lemma* continuous_on.comp
- \+ *lemma* continuous_on.congr_mono
- \+ *lemma* continuous_on.mono
- \+ *lemma* continuous_on.preimage_closed_of_closed
- \+ *lemma* continuous_on.preimage_interior_subset_interior_preimage
- \+ *lemma* continuous_on.preimage_open_of_open
- \+ *lemma* continuous_on.prod
- \+ *def* continuous_on
- \+ *lemma* continuous_on_const
- \+ *theorem* continuous_on_iff'
- \+ *theorem* continuous_on_iff
- \+ *theorem* continuous_on_iff_continuous_restrict
- \+ *theorem* continuous_on_iff_is_closed
- \+ *lemma* continuous_on_of_locally_continuous_on
- \+ *lemma* continuous_on_open_iff
- \+ *lemma* continuous_on_open_of_generate_from
- \+ *lemma* continuous_within_at.comp
- \+ *lemma* continuous_within_at.congr_of_mem_nhds_within
- \+ *lemma* continuous_within_at.continuous_at
- \+ *lemma* continuous_within_at.mono
- \+ *lemma* continuous_within_at.preimage_mem_nhds_within
- \+ *lemma* continuous_within_at.prod
- \+ *theorem* continuous_within_at.tendsto_nhds_within_image
- \+ *def* continuous_within_at
- \+ *theorem* continuous_within_at_iff_continuous_at_restrict
- \+ *theorem* continuous_within_at_iff_ptendsto_res
- \+ *lemma* continuous_within_at_inter'
- \+ *lemma* continuous_within_at_inter
- \+ *theorem* continuous_within_at_univ
- \+ *theorem* inter_mem_nhds_within
- \+ *lemma* map_nhds_within
- \+ *theorem* mem_nhds_within
- \+ *theorem* mem_nhds_within_subtype
- \+ *def* nhds_within
- \+ *theorem* nhds_within_empty
- \+ *theorem* nhds_within_eq
- \+ *theorem* nhds_within_eq_map_subtype_val
- \+ *theorem* nhds_within_eq_nhds_within
- \+ *theorem* nhds_within_eq_of_open
- \+ *theorem* nhds_within_inter'
- \+ *theorem* nhds_within_inter
- \+ *theorem* nhds_within_le_comap
- \+ *theorem* nhds_within_le_of_mem
- \+ *theorem* nhds_within_mono
- \+ *theorem* nhds_within_restrict''
- \+ *theorem* nhds_within_restrict'
- \+ *theorem* nhds_within_restrict
- \+ *theorem* nhds_within_subtype
- \+ *theorem* nhds_within_union
- \+ *theorem* nhds_within_univ
- \+ *theorem* principal_subtype
- \+ *theorem* self_mem_nhds_within
- \+ *theorem* tendsto_if_nhds_within
- \+ *theorem* tendsto_nhds_within_iff_subtype
- \+ *theorem* tendsto_nhds_within_mono_left
- \+ *theorem* tendsto_nhds_within_mono_right
- \+ *theorem* tendsto_nhds_within_of_tendsto_nhds

Modified src/topology/local_homeomorph.lean


Modified src/topology/order.lean
- \- *lemma* continuous.comp_continuous_on
- \- *lemma* continuous.continuous_at
- \- *lemma* continuous.continuous_on
- \- *lemma* continuous_at.comp
- \- *lemma* continuous_at.continuous_within_at
- \- *lemma* continuous_at.preimage_mem_nhds
- \- *lemma* continuous_iff_continuous_on_univ
- \- *lemma* continuous_on.comp
- \- *lemma* continuous_on.congr_mono
- \- *lemma* continuous_on.mono
- \- *lemma* continuous_on.preimage_closed_of_closed
- \- *lemma* continuous_on.preimage_interior_subset_interior_preimage
- \- *lemma* continuous_on.preimage_open_of_open
- \- *lemma* continuous_on_const
- \- *theorem* continuous_on_iff'
- \- *theorem* continuous_on_iff
- \- *theorem* continuous_on_iff_continuous_restrict
- \- *theorem* continuous_on_iff_is_closed
- \- *lemma* continuous_on_of_locally_continuous_on
- \- *lemma* continuous_on_open_iff
- \- *lemma* continuous_on_open_of_generate_from
- \- *lemma* continuous_within_at.comp
- \- *lemma* continuous_within_at.congr_of_mem_nhds_within
- \- *lemma* continuous_within_at.continuous_at
- \- *lemma* continuous_within_at.mono
- \- *lemma* continuous_within_at.preimage_mem_nhds_within
- \- *theorem* continuous_within_at.tendsto_nhds_within_image
- \- *theorem* continuous_within_at_iff_continuous_at_restrict
- \- *theorem* continuous_within_at_iff_ptendsto_res
- \- *lemma* continuous_within_at_inter'
- \- *lemma* continuous_within_at_inter
- \- *theorem* continuous_within_at_univ
- \- *theorem* mem_nhds_within_subtype
- \- *theorem* nhds_within_eq_map_subtype_val
- \- *theorem* nhds_within_le_comap
- \- *theorem* nhds_within_subtype
- \- *theorem* principal_subtype
- \- *theorem* tendsto_nhds_within_iff_subtype



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
- \- *lemma* coe_zero
- \+ *lemma* uniform_space.completion.coe_zero



## [2019-10-07 21:52:59](https://github.com/leanprover-community/mathlib/commit/1bf831f)
refactor(topology/dense_embedding): move dense embeddings to new file ([#1515](https://github.com/leanprover-community/mathlib/pull/1515))
#### Estimated changes
Modified src/topology/constructions.lean


Added src/topology/dense_embedding.lean
- \+ *lemma* dense_embedding.inj_iff
- \+ *theorem* dense_embedding.mk'
- \+ *lemma* dense_embedding.to_embedding
- \+ *structure* dense_embedding
- \+ *lemma* dense_inducing.closure_image_nhds_of_nhds
- \+ *lemma* dense_inducing.closure_range
- \+ *lemma* dense_inducing.comap_nhds_neq_bot
- \+ *lemma* dense_inducing.continuous_extend
- \+ *def* dense_inducing.extend
- \+ *lemma* dense_inducing.extend_e_eq
- \+ *lemma* dense_inducing.extend_eq
- \+ *lemma* dense_inducing.extend_eq_of_cont
- \+ *lemma* dense_inducing.mk'
- \+ *lemma* dense_inducing.nhds_eq_comap
- \+ *lemma* dense_inducing.self_sub_closure_image_preimage_of_open
- \+ *lemma* dense_inducing.tendsto_comap_nhds_nhds
- \+ *lemma* dense_inducing.tendsto_extend
- \+ *structure* dense_inducing
- \+ *lemma* dense_range.comp
- \+ *def* dense_range.inhabited
- \+ *lemma* dense_range.nonempty
- \+ *def* dense_range
- \+ *lemma* dense_range_iff_closure_eq

Modified src/topology/maps.lean
- \- *lemma* dense_embedding.inj_iff
- \- *theorem* dense_embedding.mk'
- \- *lemma* dense_embedding.to_embedding
- \- *structure* dense_embedding
- \- *lemma* dense_inducing.closure_image_nhds_of_nhds
- \- *lemma* dense_inducing.closure_range
- \- *lemma* dense_inducing.comap_nhds_neq_bot
- \- *lemma* dense_inducing.continuous_extend
- \- *def* dense_inducing.extend
- \- *lemma* dense_inducing.extend_e_eq
- \- *lemma* dense_inducing.extend_eq
- \- *lemma* dense_inducing.extend_eq_of_cont
- \- *lemma* dense_inducing.mk'
- \- *lemma* dense_inducing.nhds_eq_comap
- \- *lemma* dense_inducing.self_sub_closure_image_preimage_of_open
- \- *lemma* dense_inducing.tendsto_comap_nhds_nhds
- \- *lemma* dense_inducing.tendsto_extend
- \- *structure* dense_inducing
- \- *lemma* dense_range.comp
- \- *def* dense_range.inhabited
- \- *lemma* dense_range.nonempty
- \- *def* dense_range
- \- *lemma* dense_range_iff_closure_eq



## [2019-10-07 21:06:26](https://github.com/leanprover-community/mathlib/commit/b3eb34d)
doc(topology/order): module and definition docstrings ([#1505](https://github.com/leanprover-community/mathlib/pull/1505))
#### Estimated changes
Modified src/topology/basic.lean


Modified src/topology/order.lean




## [2019-10-07 17:24:46](https://github.com/leanprover-community/mathlib/commit/f519a12)
refactor(topology/list): move topology of lists, vectors to new file ([#1514](https://github.com/leanprover-community/mathlib/pull/1514))
#### Estimated changes
Modified src/topology/constructions.lean
- \- *lemma* list.continuous_at_length
- \- *lemma* list.continuous_insert_nth
- \- *lemma* list.continuous_remove_nth
- \- *lemma* list.tendsto_cons'
- \- *lemma* list.tendsto_cons
- \- *lemma* list.tendsto_cons_iff
- \- *lemma* list.tendsto_insert_nth'
- \- *lemma* list.tendsto_insert_nth
- \- *lemma* list.tendsto_nhds
- \- *lemma* list.tendsto_remove_nth
- \- *lemma* vector.cons_val
- \- *lemma* vector.continuous_at_remove_nth
- \- *lemma* vector.continuous_insert_nth'
- \- *lemma* vector.continuous_insert_nth
- \- *lemma* vector.continuous_remove_nth
- \- *lemma* vector.tendsto_cons
- \- *lemma* vector.tendsto_insert_nth

Added src/topology/list.lean
- \+ *lemma* list.continuous_at_length
- \+ *lemma* list.continuous_insert_nth
- \+ *lemma* list.continuous_remove_nth
- \+ *lemma* list.tendsto_cons'
- \+ *lemma* list.tendsto_cons
- \+ *lemma* list.tendsto_cons_iff
- \+ *lemma* list.tendsto_insert_nth'
- \+ *lemma* list.tendsto_insert_nth
- \+ *lemma* list.tendsto_nhds
- \+ *lemma* list.tendsto_remove_nth
- \+ *lemma* nhds_cons
- \+ *lemma* nhds_list
- \+ *lemma* nhds_nil
- \+ *lemma* vector.cons_val
- \+ *lemma* vector.continuous_at_remove_nth
- \+ *lemma* vector.continuous_insert_nth'
- \+ *lemma* vector.continuous_insert_nth
- \+ *lemma* vector.continuous_remove_nth
- \+ *lemma* vector.tendsto_cons
- \+ *lemma* vector.tendsto_insert_nth

Modified src/topology/order.lean
- \- *lemma* nhds_cons
- \- *lemma* nhds_list
- \- *lemma* nhds_nil



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
- \+/\- *lemma* open_subgroup.is_closed
- \+/\- *lemma* open_subgroup.is_open_of_nonempty_open_subset
- \+/\- *lemma* open_subgroup.is_open_of_open_subgroup

Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/constructions.lean
- \+/\- *lemma* is_open_prod_iff'

Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/isometry.lean
- \- *def* Kuratowski_embedding.Kuratowski_embedding
- \- *lemma* Kuratowski_embedding.Kuratowski_embedding_isometry
- \- *def* Kuratowski_embedding.nonempty_compacts.Kuratowski_embedding
- \- *def* Kuratowski_embedding.ℓ_infty_ℝ
- \+ *def* Kuratowski_embedding
- \+ *def* nonempty_compacts.Kuratowski_embedding
- \+ *def* ℓ_infty_ℝ

Modified src/topology/stone_cech.lean


Modified src/topology/uniform_space/separation.lean




## [2019-10-05 05:18:27](https://github.com/leanprover-community/mathlib/commit/98dbe27)
feat(algebra/opposites): add some trivial `@[simp]` lemmas ([#1508](https://github.com/leanprover-community/mathlib/pull/1508))
#### Estimated changes
Modified src/algebra/opposites.lean
- \+ *lemma* opposite.op_add
- \+ *lemma* opposite.op_inv
- \+ *lemma* opposite.op_mul
- \+ *lemma* opposite.op_neg
- \+ *lemma* opposite.op_one
- \+ *lemma* opposite.op_zero
- \+ *lemma* opposite.unop_add
- \+ *lemma* opposite.unop_inv
- \+ *lemma* opposite.unop_mul
- \+ *lemma* opposite.unop_neg
- \+ *lemma* opposite.unop_one
- \+ *lemma* opposite.unop_zero



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
Added src/algebra/category/Module/basic.lean
- \+ *lemma* Module.coe_comp
- \+ *lemma* Module.id_apply
- \+ *def* Module.of
- \+ *structure* Module

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
- \+ *lemma* finset.prod_range_one
- \+ *lemma* finset.prod_range_zero
- \+ *lemma* finset.sum_range_one
- \- *theorem* geom_sum
- \- *lemma* geom_sum_inv
- \- *theorem* geom_sum_mul
- \- *theorem* geom_sum_mul_add

Added src/algebra/commute.lean
- \+ *lemma* add_monoid.centralizer_closure
- \+ *lemma* centralizer.inter_units_is_subgroup
- \+ *def* centralizer
- \+ *theorem* commute.add_left
- \+ *theorem* commute.add_right
- \+ *theorem* commute.cast_int_left
- \+ *theorem* commute.cast_int_right
- \+ *theorem* commute.cast_nat_left
- \+ *theorem* commute.cast_nat_right
- \+ *theorem* commute.gpow_gpow
- \+ *theorem* commute.gpow_gpow_self
- \+ *theorem* commute.gpow_left
- \+ *theorem* commute.gpow_right
- \+ *theorem* commute.gpow_self
- \+ *theorem* commute.gsmul_gsmul
- \+ *theorem* commute.gsmul_left
- \+ *theorem* commute.gsmul_right
- \+ *theorem* commute.gsmul_self
- \+ *theorem* commute.inv_inv
- \+ *theorem* commute.inv_inv_iff
- \+ *theorem* commute.inv_left
- \+ *theorem* commute.inv_left_iff
- \+ *theorem* commute.inv_right
- \+ *theorem* commute.inv_right_iff
- \+ *theorem* commute.list_prod_left
- \+ *theorem* commute.list_prod_right
- \+ *theorem* commute.mul_left
- \+ *theorem* commute.mul_right
- \+ *theorem* commute.neg_left
- \+ *theorem* commute.neg_left_iff
- \+ *theorem* commute.neg_one_left
- \+ *theorem* commute.neg_one_right
- \+ *theorem* commute.neg_right
- \+ *theorem* commute.neg_right_iff
- \+ *theorem* commute.one_left
- \+ *theorem* commute.one_right
- \+ *theorem* commute.pow_left
- \+ *theorem* commute.pow_pow
- \+ *theorem* commute.pow_pow_self
- \+ *theorem* commute.pow_right
- \+ *theorem* commute.pow_self
- \+ *theorem* commute.self_gpow
- \+ *theorem* commute.self_gsmul
- \+ *theorem* commute.self_gsmul_gsmul
- \+ *theorem* commute.self_pow
- \+ *theorem* commute.self_smul
- \+ *theorem* commute.self_smul_smul
- \+ *theorem* commute.smul_left
- \+ *theorem* commute.smul_right
- \+ *theorem* commute.smul_self
- \+ *theorem* commute.smul_smul
- \+ *theorem* commute.sub_left
- \+ *theorem* commute.sub_right
- \+ *theorem* commute.units_coe
- \+ *theorem* commute.units_inv_left
- \+ *theorem* commute.units_inv_left_iff
- \+ *theorem* commute.units_inv_right
- \+ *theorem* commute.units_inv_right_iff
- \+ *theorem* commute.zero_left
- \+ *theorem* commute.zero_right
- \+ *def* commute
- \+ *lemma* group.centralizer_closure
- \+ *theorem* mem_centralizer
- \+ *theorem* monoid.centralizer_closure
- \+ *theorem* neg_pow
- \+ *lemma* ring.centralizer_closure

Added src/algebra/geom_sum.lean
- \+ *def* geom_series
- \+ *theorem* geom_series_def
- \+ *theorem* geom_series_one
- \+ *theorem* geom_series_zero
- \+ *def* geom_series₂
- \+ *theorem* geom_series₂_def
- \+ *theorem* geom_series₂_one
- \+ *theorem* geom_series₂_with_one
- \+ *theorem* geom_series₂_zero
- \+ *theorem* geom_sum
- \+ *lemma* geom_sum_inv
- \+ *theorem* geom_sum_mul
- \+ *theorem* geom_sum_mul_add
- \+ *theorem* geom_sum_mul_neg
- \+ *theorem* geom_sum₂_mul
- \+ *theorem* geom_sum₂_mul_add
- \+ *theorem* geom_sum₂_mul_comm

Modified src/algebra/group_power.lean
- \+ *theorem* gsmul_one

Modified src/analysis/specific_limits.lean


Modified src/data/complex/exponential.lean


Modified src/data/nat/choose.lean
- \+/\- *theorem* add_pow
- \+ *theorem* commute.add_pow

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
- \+/\- *lemma* finset.prod_eq_one
- \+/\- *lemma* finset.sum_le_sum_of_ne_zero

Modified src/algebra/order_functions.lean
- \+ *lemma* abs_add
- \- *def* abs_add
- \+ *lemma* sub_abs_le_abs_sub
- \- *def* sub_abs_le_abs_sub

Modified src/analysis/complex/exponential.lean
- \- *def* real.angle.angle
- \+ *def* real.angle

Modified src/category/functor.lean
- \+/\- *def* functor.const

Modified src/category_theory/isomorphism.lean
- \+ *lemma* category_theory.is_iso.inv_inv
- \- *lemma* category_theory.is_iso.is_iso.inv_inv

Modified src/category_theory/limits/preserves.lean


Modified src/computability/turing_machine.lean
- \+ *def* turing.TM2to1.{l}
- \- *theorem* turing.TM2to1.{l}

Modified src/data/finset.lean
- \+/\- *lemma* finset.card_le_card_of_inj_on
- \+/\- *lemma* finset.card_lt_card
- \+/\- *theorem* finset.fold_map
- \+/\- *lemma* finset.image_const
- \+/\- *theorem* finset.image_singleton
- \+/\- *theorem* finset.map_empty
- \+/\- *def* finset.pi.empty
- \+/\- *lemma* finset.subset_image_iff
- \+/\- *theorem* finset.subset_insert

Modified src/data/finsupp.lean


Modified src/data/fintype.lean


Modified src/data/list/basic.lean


Modified src/data/list/defs.lean


Modified src/data/opposite.lean
- \- *def* opposite.opposite
- \+ *def* opposite

Modified src/data/rat/order.lean


Modified src/data/seq/computation.lean
- \+ *lemma* computation.corec_eq
- \- *def* computation.corec_eq
- \+ *lemma* computation.lift_rel_aux.ret_left
- \- *def* computation.lift_rel_aux.ret_left
- \+ *lemma* computation.lift_rel_aux.ret_right
- \- *def* computation.lift_rel_aux.ret_right

Modified src/data/set/finite.lean
- \+/\- *lemma* finset.coe_to_finset'
- \+/\- *def* set.fintype_of_fintype_image

Modified src/data/set/function.lean
- \+/\- *theorem* set.right_inv_on_of_eq_on_left

Modified src/logic/basic.lean
- \+ *lemma* Exists.imp
- \- *def* Exists.imp
- \+/\- *lemma* exists_imp_exists'

Modified src/meta/expr.lean
- \+ *def* name.has_prefix

Modified src/meta/rb_map.lean


Modified src/set_theory/ordinal.lean
- \+/\- *theorem* principal_seg.equiv_lt_apply
- \+/\- *theorem* principal_seg.equiv_lt_top
- \+/\- *theorem* principal_seg.lt_le_top
- \+/\- *theorem* principal_seg.of_element_top
- \+/\- *theorem* principal_seg.top_eq

Modified src/tactic/core.lean


Modified src/tactic/interactive.lean
- \+/\- *lemma* tactic.interactive.{u}

Modified src/tactic/sanity_check.lean


Modified src/topology/category/Top/open_nhds.lean
- \- *def* topological_space.open_nhds.open_nhds
- \+ *def* topological_space.open_nhds

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
- \+ *def* add_aut.to_perm
- \+ *def* mul_aut.to_perm
- \+ *def* mul_aut
- \+ *lemma* mul_equiv.ext
- \+ *def* ring_aut.to_add_aut
- \+ *def* ring_aut.to_mul_aut
- \+ *def* ring_aut.to_perm
- \+ *def* ring_aut
- \+ *lemma* ring_equiv.ext



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
- \- *def* module.dual

Modified src/tactic/core.lean


Modified src/topology/uniform_space/compare_reals.lean
- \+/\- *def* compare_reals.Q

Modified test/delta_instance.lean
- \+ *inductive* P
- \+ *def* S
- \+ *def* X
- \+ *def* id_ring



## [2019-10-01 07:53:40](https://github.com/leanprover-community/mathlib/commit/800dba4)
chore(linear_map): use curly brackets for type class in linear_map coe_to_fun ([#1493](https://github.com/leanprover-community/mathlib/pull/1493))
* chore(linear_map): use curly brackets for type class in linear_map coe_to_fun
*  fix
#### Estimated changes
Modified src/algebra/module.lean


Modified src/field_theory/mv_polynomial.lean


