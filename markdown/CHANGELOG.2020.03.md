## [2020-03-31 22:26:22](https://github.com/leanprover-community/mathlib/commit/7d89f2e)
feat(data/fintype/card): prod_univ_sum ([#2284](https://github.com/leanprover-community/mathlib/pull/2284))
* feat(data/fintype/card): prod_univ_sum
* Update src/data/fintype.lean
* Update src/data/fintype/card.lean
* docstrings
* fix build
* remove unused argument
* fix build
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/data/finset.lean
- \+/\- *lemma* finset.card_map

Modified src/data/fintype/basic.lean
- \+/\- *lemma* fintype.pi_finset_univ

Modified src/data/fintype/card.lean
- \+ *lemma* finset.prod_univ_pi
- \+ *lemma* finset.prod_univ_sum

Modified src/linear_algebra/determinant.lean




## [2020-03-31 19:02:55](https://github.com/leanprover-community/mathlib/commit/224ba7e)
feat(data/finset): card_image_le ([#2295](https://github.com/leanprover-community/mathlib/pull/2295))
* feat(data/finset): card_image_le
* add list.to_finset_card_le
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.card_image_le
- \+ *theorem* list.to_finset_card_le
- \+ *theorem* multiset.to_finset_card_le



## [2020-03-31 16:02:27](https://github.com/leanprover-community/mathlib/commit/72d3b6e)
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
#### Estimated changes
Modified src/category/equiv_functor.lean


Added src/category/equiv_functor/instances.lean


Modified src/tactic/equiv_rw.lean


Modified test/equiv_rw.lean
- \+ *lemma* semigroup.id_map
- \- *lemma* semigroup.map_comp
- \- *def* semigroup.map_equiv
- \- *lemma* semigroup.map_id
- \+ *lemma* semigroup.map_map



## [2020-03-31 14:30:05](https://github.com/leanprover-community/mathlib/commit/b508d0e)
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
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.Pi_congr'
- \+ *def* equiv.arrow_congr'
- \+ *lemma* equiv.arrow_congr'_apply
- \+ *lemma* equiv.arrow_congr'_refl
- \+ *lemma* equiv.arrow_congr'_symm
- \+ *lemma* equiv.arrow_congr'_trans
- \+ *def* equiv.of_iff

Modified src/data/equiv/functor.lean
- \+ *lemma* bifunctor.map_equiv_refl_refl
- \+ *lemma* functor.map_equiv_refl

Modified src/set_theory/pgame.lean


Added src/tactic/equiv_rw.lean


Modified src/tactic/solve_by_elim.lean


Modified src/tactic/tidy.lean


Added test/equiv_rw.lean
- \+ *def* monoid.map
- \+ *def* semigroup.map
- \+ *lemma* semigroup.map_comp
- \+ *def* semigroup.map_equiv
- \+ *lemma* semigroup.map_id



## [2020-03-31 11:30:19](https://github.com/leanprover-community/mathlib/commit/2669062)
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
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* finsupp.prod_comm
- \+ *lemma* finsupp.prod_ite_eq'
- \+ *lemma* finsupp.prod_ite_eq
- \+/\- *lemma* finsupp.smul_apply

Modified src/data/monoid_algebra.lean
- \+ *lemma* monoid_algebra.mul_apply
- \+ *lemma* monoid_algebra.mul_apply_left
- \+ *lemma* monoid_algebra.mul_apply_right
- \+ *lemma* monoid_algebra.mul_single_apply
- \+ *lemma* monoid_algebra.single_mul_apply

Modified src/data/polynomial.lean




## [2020-03-31 09:10:23](https://github.com/leanprover-community/mathlib/commit/1763220)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-31 08:35:51](https://github.com/leanprover-community/mathlib/commit/85affa4)
refactor(*): migrate more files to bundled `ring_hom`s ([#2286](https://github.com/leanprover-community/mathlib/pull/2286))
* refactor(*): migrate more files to bundled `ring_hom`s
* Fix lint
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/algebra/char_p.lean
- \+ *def* zmod.cast_hom

Modified src/algebra/module.lean
- \- *def* is_ring_hom.to_module
- \+ *def* ring_hom.to_module

Modified src/data/equiv/basic.lean
- \+/\- *def* function.involutive.to_equiv

Modified src/data/int/basic.lean
- \+ *def* int.cast_ring_hom
- \+ *lemma* int.coe_cast_ring_hom
- \- *lemma* int.eq_cast'
- \- *lemma* is_ring_hom.map_int_cast
- \+ *lemma* ring_hom.eq_int_cast'
- \+ *lemma* ring_hom.eq_int_cast
- \+/\- *lemma* ring_hom.map_int_cast

Modified src/data/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.C_sub
- \+ *lemma* mv_polynomial.coe_eval₂_hom
- \+/\- *lemma* mv_polynomial.eval_sub
- \+ *def* mv_polynomial.eval₂_hom
- \+/\- *lemma* mv_polynomial.eval₂_sub
- \+/\- *lemma* mv_polynomial.map_sub

Modified src/data/nat/cast.lean
- \- *lemma* is_semiring_hom.map_nat_cast
- \+ *def* nat.cast_add_monoid_hom
- \+ *def* nat.cast_ring_hom
- \+ *lemma* nat.coe_cast_add_monoid_hom
- \+ *lemma* nat.coe_cast_ring_hom
- \+/\- *lemma* ring_hom.map_nat_cast

Modified src/data/polynomial.lean


Modified src/data/real/nnreal.lean


Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/field_theory/finite.lean


Modified src/field_theory/finite_card.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/free_comm_ring.lean




## [2020-03-31 05:47:42](https://github.com/leanprover-community/mathlib/commit/66f3090)
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
#### Estimated changes
Added src/analysis/analytic/basic.lean
- \+ *lemma* analytic_at.add
- \+ *lemma* analytic_at.continuous_at
- \+ *lemma* analytic_at.neg
- \+ *lemma* analytic_at.sub
- \+ *def* analytic_at
- \+ *lemma* formal_multilinear_series.bound_of_lt_radius
- \+ *lemma* formal_multilinear_series.continuous_on
- \+ *lemma* formal_multilinear_series.geometric_bound_of_lt_radius
- \+ *lemma* formal_multilinear_series.has_fpower_series_on_ball
- \+ *lemma* formal_multilinear_series.le_radius_of_bound
- \+ *lemma* formal_multilinear_series.min_radius_le_radius_add
- \+ *def* formal_multilinear_series.partial_sum
- \+ *lemma* formal_multilinear_series.partial_sum_continuous
- \+ *def* formal_multilinear_series.radius
- \+ *lemma* formal_multilinear_series.radius_neg
- \+ *lemma* has_fpower_series_at.add
- \+ *lemma* has_fpower_series_at.analytic_at
- \+ *lemma* has_fpower_series_at.coeff_zero
- \+ *lemma* has_fpower_series_at.continuous_at
- \+ *lemma* has_fpower_series_at.neg
- \+ *lemma* has_fpower_series_at.radius_pos
- \+ *lemma* has_fpower_series_at.sub
- \+ *def* has_fpower_series_at
- \+ *lemma* has_fpower_series_on_ball.add
- \+ *lemma* has_fpower_series_on_ball.analytic_at
- \+ *lemma* has_fpower_series_on_ball.coeff_zero
- \+ *lemma* has_fpower_series_on_ball.continuous_on
- \+ *lemma* has_fpower_series_on_ball.has_fpower_series_at
- \+ *lemma* has_fpower_series_on_ball.mono
- \+ *lemma* has_fpower_series_on_ball.neg
- \+ *lemma* has_fpower_series_on_ball.radius_pos
- \+ *lemma* has_fpower_series_on_ball.sub
- \+ *lemma* has_fpower_series_on_ball.sum
- \+ *lemma* has_fpower_series_on_ball.uniform_limit
- \+ *structure* has_fpower_series_on_ball

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.lt_iff_exists_nnreal_btwn

Modified src/data/set/finite.lean
- \+ *lemma* finset.bdd_above
- \+ *lemma* finset.bdd_below

Modified src/order/bounded_lattice.lean
- \- *lemma* with_top.dense_coe
- \+ *lemma* with_top.lt_iff_exists_coe_btwn

Modified src/topology/metric_space/emetric_space.lean




## [2020-03-31 03:13:56](https://github.com/leanprover-community/mathlib/commit/20bff2c)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-31 02:43:53](https://github.com/leanprover-community/mathlib/commit/4168aba)
refactor(data/fintype): move data/fintype to data/fintype/basic ([#2285](https://github.com/leanprover-community/mathlib/pull/2285))
#### Estimated changes
Modified docs/theories/sets.md


Modified src/algebra/char_p.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/computability/turing_machine.lean


Modified src/data/W.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/list.lean


Modified src/data/fin_enum.lean


Renamed src/data/fintype.lean to src/data/fintype/basic.lean


Modified src/data/fintype/card.lean


Modified src/data/fintype/intervals.lean


Modified src/data/matrix/basic.lean


Modified src/data/set/finite.lean


Modified src/data/zmod/basic.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/perm/sign.lean


Modified src/number_theory/bernoulli.lean


Modified src/tactic/fin_cases.lean


Modified test/omega.lean




## [2020-03-31 00:17:23](https://github.com/leanprover-community/mathlib/commit/c5181d1)
feat(*): more `prod`-related (continuous) linear maps and their derivatives ([#2277](https://github.com/leanprover-community/mathlib/pull/2277))
* feat(*): more `prod`-related (continuous) linear maps and their derivatives
* Make `R` argument of `continuous_linear_equiv.refl` explicit
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable.fst
- \+ *lemma* differentiable.snd
- \+ *lemma* differentiable_at.fst
- \+ *theorem* differentiable_at.prod_map
- \+ *lemma* differentiable_at.snd
- \+ *lemma* differentiable_at_fst
- \+ *lemma* differentiable_at_snd
- \+ *lemma* differentiable_fst
- \+ *lemma* differentiable_on.fst
- \+ *lemma* differentiable_on.snd
- \+ *lemma* differentiable_on_fst
- \+ *lemma* differentiable_on_snd
- \+ *lemma* differentiable_snd
- \+ *lemma* differentiable_within_at.fst
- \+ *lemma* differentiable_within_at.snd
- \+ *lemma* differentiable_within_at_fst
- \+ *lemma* differentiable_within_at_snd
- \+ *lemma* fderiv.fst
- \+ *lemma* fderiv.snd
- \+ *lemma* fderiv_fst
- \+ *lemma* fderiv_snd
- \+ *lemma* fderiv_within.fst
- \+ *lemma* fderiv_within.snd
- \+ *lemma* fderiv_within_fst
- \+ *lemma* fderiv_within_snd
- \+ *lemma* has_fderiv_at.fst
- \+ *theorem* has_fderiv_at.prod_map
- \+ *lemma* has_fderiv_at.snd
- \+ *lemma* has_fderiv_at_filter.fst
- \+ *lemma* has_fderiv_at_filter.snd
- \+ *lemma* has_fderiv_at_filter_fst
- \+ *lemma* has_fderiv_at_filter_snd
- \+ *lemma* has_fderiv_at_fst
- \+ *lemma* has_fderiv_at_snd
- \+ *lemma* has_fderiv_within_at.fst
- \+ *lemma* has_fderiv_within_at.snd
- \+ *lemma* has_fderiv_within_at_fst
- \+ *lemma* has_fderiv_within_at_snd
- \+ *lemma* has_strict_fderiv_at.fst
- \+ *theorem* has_strict_fderiv_at.prod_map
- \+ *lemma* has_strict_fderiv_at.snd
- \+ *lemma* has_strict_fderiv_at_fst
- \+ *theorem* has_strict_fderiv_at_id
- \+ *lemma* has_strict_fderiv_at_snd

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.coe_prod
- \+ *lemma* linear_equiv.skew_prod_apply
- \+ *lemma* linear_equiv.skew_prod_symm_apply
- \+ *def* linear_map.prod_map
- \+ *theorem* linear_map.prod_map_apply

Modified src/topology/algebra/module.lean
- \+ *theorem* continuous_linear_equiv.coe_def_rev
- \+ *lemma* continuous_linear_equiv.coe_prod
- \+ *lemma* continuous_linear_equiv.coe_refl'
- \+ *lemma* continuous_linear_equiv.coe_refl
- \+ *def* continuous_linear_equiv.prod
- \+ *lemma* continuous_linear_equiv.prod_apply
- \+ *def* continuous_linear_equiv.skew_prod
- \+ *lemma* continuous_linear_equiv.skew_prod_apply
- \+ *lemma* continuous_linear_equiv.skew_prod_symm_apply
- \+/\- *lemma* continuous_linear_map.coe_fst'
- \+/\- *lemma* continuous_linear_map.coe_fst
- \+ *lemma* continuous_linear_map.coe_prod_map
- \+/\- *lemma* continuous_linear_map.coe_snd'
- \+/\- *lemma* continuous_linear_map.coe_snd
- \+ *def* continuous_linear_map.fst
- \+ *def* continuous_linear_map.prod_map
- \+ *lemma* continuous_linear_map.prod_map_apply
- \+ *def* continuous_linear_map.snd

Modified src/topology/basic.lean
- \+/\- *lemma* nhds_basis_opens

Modified src/topology/constructions.lean
- \+ *lemma* continuous.prod_map



## [2020-03-30 20:48:51](https://github.com/leanprover-community/mathlib/commit/64f835b)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-30 20:13:52](https://github.com/leanprover-community/mathlib/commit/8a61723)
fix(algebra/punit_instance): punit.smul_eq is marked simp and can be proved by simp ([#2291](https://github.com/leanprover-community/mathlib/pull/2291))
#### Estimated changes
Modified src/algebra/punit_instances.lean
- \+/\- *lemma* punit.smul_eq



## [2020-03-30 16:48:08](https://github.com/leanprover-community/mathlib/commit/3f0e700)
doc(algebra/group/type_tags): add docs ([#2287](https://github.com/leanprover-community/mathlib/pull/2287))
* doc(algebra/group/type_tags): add docs
* Update src/algebra/group/type_tags.lean
#### Estimated changes
Modified src/algebra/group/type_tags.lean




## [2020-03-30 13:16:33](https://github.com/leanprover-community/mathlib/commit/1331e29)
chore(*): completing most of the -T50000 challenge ([#2281](https://github.com/leanprover-community/mathlib/pull/2281))
#### Estimated changes
Modified src/analysis/complex/basic.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/category_theory/limits/over.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* ring.fractional_ideal.ne_zero_of_mul_eq_one

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/category/Top/adjunctions.lean


Modified src/topology/category/UniformSpace.lean




## [2020-03-30 10:46:51](https://github.com/leanprover-community/mathlib/commit/37212a7)
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
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_add
- \+ *lemma* finset.sum_pow_mul_eq_add_pow

Modified src/data/fin.lean


Modified src/data/finset.lean
- \+ *lemma* finset.disjoint_iff_disjoint_coe
- \+ *lemma* finset.mono_of_fin_last
- \+ *lemma* finset.mono_of_fin_strict_mono
- \+ *lemma* finset.mono_of_fin_unique
- \+ *lemma* finset.mono_of_fin_zero
- \+ *lemma* finset.range_eq_Ico

Modified src/data/fintype.lean
- \+ *lemma* finset.mono_of_fin_unique'
- \+ *lemma* fintype.coe_image_univ

Modified src/data/fintype/card.lean
- \+ *lemma* fin.sum_pow_mul_eq_add_pow
- \+ *lemma* fintype.sum_pow_mul_eq_add_pow



## [2020-03-30 08:09:21](https://github.com/leanprover-community/mathlib/commit/cd38923)
docs(algebraic_geometry/prime_spectrum): linkify url in module docs ([#2288](https://github.com/leanprover-community/mathlib/pull/2288))
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean




## [2020-03-30 06:25:08](https://github.com/leanprover-community/mathlib/commit/9288d10)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-30 05:50:58](https://github.com/leanprover-community/mathlib/commit/51553e3)
chore(data/set/lattice): use dot syntax for `disjoint.*` ([#2282](https://github.com/leanprover-community/mathlib/pull/2282))
#### Estimated changes
Modified src/data/finsupp.lean


Modified src/data/set/lattice.lean
- \+ *theorem* disjoint.mono
- \+ *theorem* disjoint.mono_left
- \+ *theorem* disjoint.mono_right
- \+ *lemma* disjoint.ne
- \- *theorem* disjoint_mono
- \- *theorem* disjoint_mono_left
- \- *theorem* disjoint_mono_right
- \- *lemma* ne_of_disjoint
- \+/\- *def* set.kern_image
- \+ *lemma* set.pairwise_disjoint.elim
- \+ *lemma* set.pairwise_disjoint.range
- \+ *lemma* set.pairwise_disjoint.subset
- \- *lemma* set.pairwise_disjoint_elim
- \- *lemma* set.pairwise_disjoint_range
- \- *lemma* set.pairwise_disjoint_subset

Modified src/data/setoid.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/topology/separation.lean




## [2020-03-30 03:22:11](https://github.com/leanprover-community/mathlib/commit/cf64860)
chore(*): remove 'using_well_founded wf_tacs', fixed in core ([#2280](https://github.com/leanprover-community/mathlib/pull/2280))
#### Estimated changes
Modified docs/extras/well_founded_recursion.md


Modified src/computability/partrec_code.lean


Modified src/data/list/basic.lean


Modified src/data/list/sort.lean


Modified src/data/vector2.lean


Modified src/tactic/basic.lean


Deleted src/tactic/well_founded_tactics.lean




## [2020-03-30 00:45:51](https://github.com/leanprover-community/mathlib/commit/8c1e32f)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-30 00:11:57](https://github.com/leanprover-community/mathlib/commit/7dad872)
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
#### Estimated changes
Modified .github/workflows/build.yml


Modified scripts/fetch_olean_cache.sh


Modified src/set_theory/surreal.lean
- \+/\- *theorem* pgame.lt_iff_le_not_le



## [2020-03-29 21:31:54](https://github.com/leanprover-community/mathlib/commit/c14c84e)
chore(topology/algebra/ordered): `le_of_tendsto`: use `∀ᶠ`, add primed versions ([#2270](https://github.com/leanprover-community/mathlib/pull/2270))
Also fix two typos in `order/filter/basic`
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/l1_space.lean


Modified src/order/filter/basic.lean
- \- *lemma* filter.tendso_add_at_top_nat
- \- *lemma* filter.tendso_sub_at_top_nat
- \+ *lemma* filter.tendsto_add_at_top_nat
- \+ *lemma* filter.tendsto_sub_at_top_nat

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* ge_of_tendsto'
- \+ *lemma* le_of_tendsto'
- \+ *lemma* le_of_tendsto_of_tendsto'

Modified src/topology/bounded_continuous_function.lean




## [2020-03-29 19:03:26](https://github.com/leanprover-community/mathlib/commit/8b679d9)
fix(tactic/squeeze): make suggestion at correct location ([#2279](https://github.com/leanprover-community/mathlib/pull/2279))
Fixes [#2267](https://github.com/leanprover-community/mathlib/pull/2267).
#### Estimated changes
Modified src/tactic/squeeze.lean




## [2020-03-29 16:22:44](https://github.com/leanprover-community/mathlib/commit/38544f1)
feat(tactic/core): basic interaction monad functions ([#1658](https://github.com/leanprover-community/mathlib/pull/1658))
* feat(tactic/core): basic interaction monad functions
* review
* remove get_result
* update comments
* whitespace
* american spelling
#### Estimated changes
Modified src/tactic/core.lean




## [2020-03-29 13:46:46](https://github.com/leanprover-community/mathlib/commit/c4fb403)
fix(tactic/core): remove all_goals option from apply_any ([#2275](https://github.com/leanprover-community/mathlib/pull/2275))
* fix(tactic/core): remove all_goals option from any_apply
* remove unnecessary imports
#### Estimated changes
Modified src/set_theory/pgame.lean


Modified src/tactic/core.lean


Modified src/tactic/solve_by_elim.lean




## [2020-03-29 11:19:27](https://github.com/leanprover-community/mathlib/commit/da8b23f)
chore(data/opposite): two trivial lemmas ([#2274](https://github.com/leanprover-community/mathlib/pull/2274))
#### Estimated changes
Modified src/data/opposite.lean
- \+ *lemma* opposite.op_eq_iff_eq_unop
- \+ *lemma* opposite.unop_eq_iff_eq_op



## [2020-03-29 08:42:21](https://github.com/leanprover-community/mathlib/commit/79880e8)
chore(data/fintype/intervals): `simp` `Ico_*_card` lemmas ([#2271](https://github.com/leanprover-community/mathlib/pull/2271))
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* finset.Ico_ℤ.card

Modified src/data/fintype/intervals.lean
- \+ *lemma* set.Ico_pnat_card
- \+ *lemma* set.Ico_ℕ_card
- \+ *lemma* set.Ico_ℤ_card

Modified src/data/pnat/intervals.lean
- \+ *lemma* pnat.Ico.card



## [2020-03-29 05:46:53](https://github.com/leanprover-community/mathlib/commit/5d9e7f5)
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
#### Estimated changes
Modified src/algebra/pi_instances.lean
- \+ *lemma* prod.mk_sub_mk

Modified src/analysis/asymptotics.lean
- \+ *lemma* asymptotics.is_O_fst_prod'
- \+ *lemma* asymptotics.is_O_snd_prod'

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* continuous_linear_equiv.comp_has_strict_fderiv_at_iff
- \- *lemma* continuous_linear_map.has_fderiv_at_filter
- \+ *lemma* has_fderiv_at_filter.is_O_sub
- \- *theorem* has_fderiv_at_filter.is_O_sub
- \- *lemma* has_fderiv_within_at.image_tangent_cone_subset
- \+ *lemma* has_fderiv_within_at.maps_to_tangent_cone
- \+/\- *theorem* has_fderiv_within_at.mul_const
- \+ *theorem* has_strict_fderiv_at.add
- \+ *theorem* has_strict_fderiv_at.add_const
- \+ *lemma* has_strict_fderiv_at.comp
- \+ *theorem* has_strict_fderiv_at.const_add
- \+ *theorem* has_strict_fderiv_at.const_mul
- \+ *theorem* has_strict_fderiv_at.const_smul
- \+ *theorem* has_strict_fderiv_at.const_sub
- \+ *lemma* has_strict_fderiv_at.continuous_at
- \+ *lemma* has_strict_fderiv_at.differentiable_at
- \+ *lemma* has_strict_fderiv_at.has_fderiv_at
- \+ *lemma* has_strict_fderiv_at.is_O_sub
- \+ *theorem* has_strict_fderiv_at.mul
- \+ *theorem* has_strict_fderiv_at.mul_const
- \+ *theorem* has_strict_fderiv_at.neg
- \+ *lemma* has_strict_fderiv_at.prod
- \+ *lemma* has_strict_fderiv_at.restrict_scalars
- \+ *theorem* has_strict_fderiv_at.smul
- \+ *theorem* has_strict_fderiv_at.smul_const
- \+ *theorem* has_strict_fderiv_at.sub
- \+ *theorem* has_strict_fderiv_at.sub_const
- \+ *def* has_strict_fderiv_at
- \+ *theorem* has_strict_fderiv_at_congr_of_mem_sets
- \+ *theorem* has_strict_fderiv_at_const
- \+/\- *lemma* is_bounded_bilinear_map.differentiable_within_at
- \+ *lemma* is_bounded_bilinear_map.has_strict_fderiv_at

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* is_bounded_bilinear_map.is_O_comp

Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually.prod_inl
- \+ *lemma* filter.eventually.prod_inr
- \+ *lemma* filter.eventually.prod_mk
- \+ *lemma* filter.tendsto.eventually

Modified src/topology/constructions.lean
- \+ *lemma* continuous_at.prod_map'
- \+ *lemma* continuous_at.prod_map
- \+ *lemma* continuous_at_fst
- \+ *lemma* continuous_at_snd
- \+ *lemma* filter.eventually.prod_inl_nhds
- \+ *lemma* filter.eventually.prod_inr_nhds
- \+ *lemma* filter.eventually.prod_mk_nhds



## [2020-03-29 03:24:03](https://github.com/leanprover-community/mathlib/commit/de8c207)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-29 02:52:21](https://github.com/leanprover-community/mathlib/commit/8454c10)
doc(ring_theory/noetherian): add docstring, normalise notation ([#2219](https://github.com/leanprover-community/mathlib/pull/2219))
* change notation; add module docstring
* adding reference to A-M
* Update src/ring_theory/noetherian.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Apply suggestions from code review
#### Estimated changes
Modified docs/references.bib


Modified src/ring_theory/noetherian.lean
- \+/\- *lemma* finite_of_linear_independent
- \+/\- *theorem* is_noetherian_of_fg_of_noetherian
- \+/\- *theorem* is_noetherian_of_linear_equiv
- \+/\- *theorem* is_noetherian_of_quotient_of_noetherian
- \+/\- *theorem* is_noetherian_of_submodule_of_noetherian
- \+/\- *theorem* is_noetherian_of_surjective
- \+/\- *lemma* is_noetherian_ring.exists_factors
- \+/\- *lemma* is_noetherian_ring.exists_irreducible_factor
- \+/\- *lemma* is_noetherian_ring.irreducible_induction_on
- \+/\- *lemma* is_noetherian_ring.well_founded_dvd_not_unit
- \+/\- *def* is_noetherian_ring
- \+/\- *theorem* is_noetherian_span_of_finite
- \+/\- *theorem* is_noetherian_submodule
- \+/\- *theorem* is_noetherian_submodule_left
- \+/\- *theorem* is_noetherian_submodule_right
- \+/\- *def* submodule.fg
- \+/\- *theorem* submodule.fg_bot
- \+/\- *theorem* submodule.fg_def
- \+/\- *theorem* submodule.fg_map
- \+/\- *theorem* submodule.fg_of_fg_map_of_fg_inf_ker
- \+/\- *lemma* submodule.fg_pow
- \+/\- *theorem* submodule.fg_prod
- \+/\- *theorem* submodule.fg_sup
- \+/\- *lemma* well_founded_submodule_gt



## [2020-03-29 00:11:06](https://github.com/leanprover-community/mathlib/commit/ecdb138)
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
#### Estimated changes
Added src/category/equiv_functor.lean
- \+ *def* equiv_functor.map_equiv
- \+ *lemma* equiv_functor.map_equiv_apply
- \+ *lemma* equiv_functor.map_equiv_symm_apply

Modified src/category_theory/core.lean
- \+ *def* category_theory.of_equiv_functor

Modified src/category_theory/types.lean
- \+ *lemma* category_theory.iso.to_equiv_comp
- \+ *lemma* category_theory.iso.to_equiv_id

Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.prod_congr

Modified src/logic/unique.lean




## [2020-03-28 21:19:19](https://github.com/leanprover-community/mathlib/commit/d500210)
feat(algebra/big_operators): missing lemmas ([#2259](https://github.com/leanprover-community/mathlib/pull/2259))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_le_prod'
- \+ *lemma* finset.prod_pow_eq_pow_sum
- \+ *lemma* finset.sum_lt_sum_of_subset



## [2020-03-28 18:32:12](https://github.com/leanprover-community/mathlib/commit/ad53e0b)
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
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/core.lean


Modified src/tactic/solve_by_elim.lean


Modified test/solve_by_elim.lean
- \+ *def* solve_by_elim_use_b



## [2020-03-28 17:37:54](https://github.com/leanprover-community/mathlib/commit/0187cb5)
fix(scripts/deploy_docs.sh): cd before git log ([#2264](https://github.com/leanprover-community/mathlib/pull/2264))
* fix(scripts/deploy_docs.sh): cd before git log
* Update scripts/deploy_docs.sh
#### Estimated changes
Modified scripts/deploy_docs.sh




## [2020-03-28 12:46:28](https://github.com/leanprover-community/mathlib/commit/17f8340)
chore(data/equiv/basic): simp to_fun to coe ([#2256](https://github.com/leanprover-community/mathlib/pull/2256))
* chore(data/equiv/basic): simp to_fun to coe
* fix proofs
* Update src/data/equiv/basic.lean
* fix proof
* partially removing to_fun
* finish switching to coercions
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.inv_fun_as_coe
- \+ *lemma* equiv.to_fun_as_coe

Modified src/topology/metric_space/gromov_hausdorff.lean




## [2020-03-28 06:05:30](https://github.com/leanprover-community/mathlib/commit/d470ae7)
fix(tactic/squeeze): do not fail when closing the goal ([#2262](https://github.com/leanprover-community/mathlib/pull/2262))
#### Estimated changes
Modified src/tactic/squeeze.lean


Modified test/examples.lean




## [2020-03-28 03:34:11](https://github.com/leanprover-community/mathlib/commit/6732788)
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
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* continuous_linear_equiv.antilipschitz
- \- *lemma* continuous_linear_equiv.lipschitz
- \+ *lemma* continuous_linear_equiv.norm_pos
- \+ *lemma* continuous_linear_equiv.norm_symm_pos
- \+ *lemma* continuous_linear_equiv.one_le_norm_mul_norm_symm
- \+ *lemma* continuous_linear_equiv.subsingleton_or_nnnorm_symm_pos
- \+ *lemma* continuous_linear_equiv.subsingleton_or_norm_symm_pos
- \+/\- *lemma* continuous_linear_equiv.uniform_embedding
- \+ *theorem* continuous_linear_map.le_op_norm_of_le
- \+/\- *lemma* continuous_linear_map.norm_id
- \+ *lemma* continuous_linear_map.norm_id_le
- \+/\- *lemma* continuous_linear_map.op_norm_comp_le

Modified src/topology/metric_space/antilipschitz.lean
- \- *lemma* antilipschitz_with.to_inverse
- \+ *lemma* antilipschitz_with.to_right_inverse
- \- *lemma* lipschitz_with.to_inverse
- \+ *lemma* lipschitz_with.to_right_inverse



## [2020-03-28 02:36:23](https://github.com/leanprover-community/mathlib/commit/1b13ccd)
chore(scripts/deploy_docs.sh): skip gen_docs if already built ([#2263](https://github.com/leanprover-community/mathlib/pull/2263))
* chore(scripts/deploy_docs.sh): skip gen_docs if already built
* Update scripts/deploy_docs.sh
#### Estimated changes
Modified scripts/deploy_docs.sh




## [2020-03-28 00:46:23](https://github.com/leanprover-community/mathlib/commit/211c5d1)
chore(data/int/basic): change instance order ([#2257](https://github.com/leanprover-community/mathlib/pull/2257))
#### Estimated changes
Modified src/data/int/basic.lean




## [2020-03-27 22:08:58](https://github.com/leanprover-community/mathlib/commit/3c0b35c)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-27 21:37:51](https://github.com/leanprover-community/mathlib/commit/d0a8507)
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
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_apply_ite
- \+/\- *lemma* finset.prod_ite
- \+ *lemma* finset.prod_pow_boole
- \+ *lemma* finset.sum_boole

Modified src/algebra/group_power.lean
- \+ *lemma* ite_pow
- \+ *lemma* pow_boole
- \+ *lemma* pow_ite

Modified src/algebra/ring.lean
- \+ *lemma* boole_mul
- \+/\- *lemma* ite_mul
- \+ *lemma* mul_boole
- \+/\- *lemma* mul_ite

Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/specific_functions.lean


Modified src/data/equiv/basic.lean


Modified src/data/nat/cast.lean
- \+ *theorem* nat.cast_ite

Modified src/data/nat/multiplicity.lean


Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/linear_algebra/nonsingular_inverse.lean




## [2020-03-27 18:48:08](https://github.com/leanprover-community/mathlib/commit/786c737)
feat(logic/basic): trivial transport lemmas ([#2254](https://github.com/leanprover-community/mathlib/pull/2254))
* feat(logic/basic): trivial transport lemmas
* oops
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/data/nat/basic.lean


Modified src/logic/basic.lean
- \+ *lemma* eq_mp_rfl
- \+ *lemma* eq_mpr_rfl
- \+ *lemma* eq_rec_constant



## [2020-03-27 16:08:17](https://github.com/leanprover-community/mathlib/commit/451de27)
chore(tactic/lint): typo ([#2253](https://github.com/leanprover-community/mathlib/pull/2253))
#### Estimated changes
Modified src/tactic/lint.lean




## [2020-03-27 13:19:03](https://github.com/leanprover-community/mathlib/commit/21ad1d3)
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
#### Estimated changes
Modified src/tactic/cache.lean


Modified src/tactic/core.lean


Modified src/tactic/elide.lean


Modified src/tactic/ext.lean


Modified src/tactic/finish.lean


Modified src/tactic/hint.lean


Modified src/tactic/interactive.lean


Modified src/tactic/linarith.lean


Modified src/tactic/localized.lean


Modified src/tactic/norm_cast.lean


Modified src/tactic/omega/main.lean


Modified src/tactic/pi_instances.lean


Modified src/tactic/replacer.lean


Modified src/tactic/restate_axiom.lean


Modified src/tactic/ring.lean


Modified src/tactic/ring_exp.lean


Modified src/tactic/solve_by_elim.lean


Modified src/tactic/tidy.lean




## [2020-03-27 12:12:17](https://github.com/leanprover-community/mathlib/commit/d3cbd4d)
chore(ci): update nolints before docs and leanchecker ([#2250](https://github.com/leanprover-community/mathlib/pull/2250))
* Update build.yml
* run lint+tests if build step succeeds (see [#2250](https://github.com/leanprover-community/mathlib/pull/2250)) ([#2252](https://github.com/leanprover-community/mathlib/pull/2252))
* run lint+tests if build succeeds
* move lint (and nolints.txt) before tests
* Apply suggestions from code review
#### Estimated changes
Modified .github/workflows/build.yml




## [2020-03-26 16:57:24-04:00](https://github.com/leanprover-community/mathlib/commit/de39b9a)
chore(.mergify.yml): cleanup ([#2248](https://github.com/leanprover-community/mathlib/pull/2248))
remove [skip-ci] and pr bits that no longer apply.
#### Estimated changes
Modified .mergify.yml




## [2020-03-26 20:55:31](https://github.com/leanprover-community/mathlib/commit/2fbf007)
doc(docs/install/project.md): mention that projects are git repositories ([#2244](https://github.com/leanprover-community/mathlib/pull/2244))
#### Estimated changes
Modified docs/install/project.md




## [2020-03-26 20:00:59](https://github.com/leanprover-community/mathlib/commit/75b4ee8)
feat(data/equiv/local_equiv): construct from `bij_on` or `inj_on` ([#2232](https://github.com/leanprover-community/mathlib/pull/2232))
* feat(data/equiv/local_equiv): construct from `bij_on` or `inj_on`
Also fix usage of `nonempty` vs `inhabited` in `set/function`. Linter
didn't catch these bugs because the types use the `.to_nonempty`
projection of the `[inhabited]` arguments.
* Add `simps`/`simp` attrs
#### Estimated changes
Modified src/data/equiv/local_equiv.lean


Modified src/data/set/function.lean
- \+/\- *theorem* set.bij_on.inv_on_inv_fun_on
- \+/\- *lemma* set.inj_on.inv_fun_on_image
- \+/\- *theorem* set.inj_on.left_inv_on_inv_fun_on
- \+/\- *theorem* set.surj_on.bij_on_subset
- \+/\- *theorem* set.surj_on.inv_on_inv_fun_on
- \+/\- *theorem* set.surj_on.maps_to_inv_fun_on
- \+/\- *theorem* set.surj_on.right_inv_on_inv_fun_on



## [2020-03-26 17:30:38](https://github.com/leanprover-community/mathlib/commit/8943351)
feat(topology/algebra/module): define `fst` and `snd`, review ([#2247](https://github.com/leanprover-community/mathlib/pull/2247))
* feat(topology/algebra/module): define `fst` and `snd`, review
* Fix compile
#### Estimated changes
Modified src/geometry/manifold/mfderiv.lean


Modified src/topology/algebra/module.lean
- \+ *theorem* continuous_linear_equiv.bijective
- \+ *theorem* continuous_linear_equiv.injective
- \+ *theorem* continuous_linear_equiv.surjective
- \+ *lemma* continuous_linear_map.coe_fst'
- \+ *lemma* continuous_linear_map.coe_fst
- \+ *lemma* continuous_linear_map.coe_prod
- \+ *lemma* continuous_linear_map.coe_snd'
- \+ *lemma* continuous_linear_map.coe_snd
- \- *def* continuous_linear_map.prod
- \+ *lemma* continuous_linear_map.prod_apply
- \- *def* continuous_linear_map.zero



## [2020-03-26 14:41:41](https://github.com/leanprover-community/mathlib/commit/5b44363)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-26 13:38:06](https://github.com/leanprover-community/mathlib/commit/0fc4e6a)
refactor(data/set/function): move `function.restrict` to `set`, redefine ([#2243](https://github.com/leanprover-community/mathlib/pull/2243))
* refactor(data/set/function): move `function.restrict` to `set`, redefine
We had `subtype.restrict` and `function.restrict` both defined in the
same way using `subtype.val`. This PR moves `function.restrict` to
`set.restrict` and makes it use `coe` instead of `subtype.val`.
* Fix compile
* Update src/data/set/function.lean
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/analysis/complex/exponential.lean


Modified src/data/set/basic.lean
- \+ *theorem* set.preimage_coe_eq_preimage_coe_iff
- \- *lemma* set.subtype.val_range
- \+/\- *lemma* subtype.val_range

Modified src/data/set/countable.lean


Modified src/data/set/function.lean
- \+ *def* set.cod_restrict
- \+ *lemma* set.coe_cod_restrict_apply
- \+/\- *lemma* set.range_restrict
- \+ *def* set.restrict
- \+ *lemma* set.restrict_apply
- \+ *lemma* set.restrict_eq

Modified src/data/subtype.lean
- \+/\- *lemma* subtype.val_eq_coe

Modified src/linear_algebra/basis.lean


Modified src/logic/function.lean
- \- *def* function.restrict
- \- *theorem* function.restrict_eq

Modified src/measure_theory/integration.lean


Modified src/topology/constructions.lean


Modified src/topology/continuous_on.lean


Modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* antilipschitz_with.cod_restrict
- \- *lemma* antilipschitz_with.id
- \+ *lemma* antilipschitz_with.restrict
- \+ *lemma* antilipschitz_with.subtype_coe
- \+ *lemma* antilipschitz_with.to_right_inv_on'
- \+ *lemma* antilipschitz_with.to_right_inv_on

Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* subtype.dist_eq

Modified src/topology/metric_space/contracting.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* subtype.edist_eq

Modified src/topology/metric_space/lipschitz.lean




## [2020-03-26 11:00:48](https://github.com/leanprover-community/mathlib/commit/fa36a8e)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-26 10:05:36](https://github.com/leanprover-community/mathlib/commit/ea10e17)
feat(data/equiv/functor): bifunctor.map_equiv ([#2241](https://github.com/leanprover-community/mathlib/pull/2241))
* feat(data/equiv/functor): bifunctor.map_equiv
* add documentation, and make the function an explicit argument
* Update src/data/equiv/functor.lean
#### Estimated changes
Modified src/data/equiv/functor.lean
- \+ *def* bifunctor.map_equiv
- \+ *lemma* bifunctor.map_equiv_apply
- \+ *lemma* bifunctor.map_equiv_symm_apply
- \+/\- *def* functor.map_equiv
- \+ *lemma* functor.map_equiv_apply
- \+ *lemma* functor.map_equiv_symm_apply

Modified src/ring_theory/free_comm_ring.lean




## [2020-03-26 07:48:43](https://github.com/leanprover-community/mathlib/commit/ab33237)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-26 06:56:37](https://github.com/leanprover-community/mathlib/commit/dbc4284)
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
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/core.lean


Modified src/tactic/squeeze.lean
- \+ *def* tactic.squeeze_loc_attr_carrier

Modified test/examples.lean


Added test/packaged_goal.lean




## [2020-03-26 04:20:05](https://github.com/leanprover-community/mathlib/commit/30146a0)
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
#### Estimated changes
Modified src/set_theory/pgame.lean


Modified src/tactic/core.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/solve_by_elim.lean


Modified test/solve_by_elim.lean




## [2020-03-26 01:26:44](https://github.com/leanprover-community/mathlib/commit/2755eae)
chore(ci): only run on push ([#2237](https://github.com/leanprover-community/mathlib/pull/2237))
* chore(ci): only run on push
* update contribution docs
#### Estimated changes
Modified .github/workflows/build.yml


Modified docs/contribute/index.md




## [2020-03-26 00:32:53](https://github.com/leanprover-community/mathlib/commit/6e6c81a)
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
#### Estimated changes
Added src/algebra/homology/chain_complex.lean
- \+ *lemma* chain_complex.comm
- \+ *lemma* chain_complex.comm_at
- \+ *lemma* chain_complex.d_squared
- \+ *abbreviation* chain_complex.forget
- \+ *abbreviation* chain_complex
- \+ *lemma* cochain_complex.comm
- \+ *lemma* cochain_complex.comm_at
- \+ *lemma* cochain_complex.d_squared
- \+ *abbreviation* cochain_complex.forget
- \+ *abbreviation* cochain_complex

Added src/algebra/homology/homology.lean
- \+ *def* cochain_complex.cohomology
- \+ *def* cochain_complex.image_to_kernel_map
- \+ *def* cochain_complex.induced_map_on_cycles

Modified src/category_theory/concrete_category/basic.lean


Added src/category_theory/differential_object.lean
- \+ *lemma* category_theory.differential_object.comp_f
- \+ *def* category_theory.differential_object.forget
- \+ *def* category_theory.differential_object.hom.comp
- \+ *def* category_theory.differential_object.hom.id
- \+ *structure* category_theory.differential_object.hom
- \+ *lemma* category_theory.differential_object.id_f
- \+ *structure* category_theory.differential_object

Modified src/category_theory/equivalence.lean
- \+ *def* category_theory.equivalence.pow
- \+ *lemma* category_theory.equivalence.pow_minus_one
- \+ *lemma* category_theory.equivalence.pow_one
- \+ *lemma* category_theory.equivalence.pow_zero

Added src/category_theory/graded_object.lean
- \+ *def* category_theory.graded_object.comap
- \+ *def* category_theory.graded_object.comap_comp
- \+ *def* category_theory.graded_object.comap_eq
- \+ *lemma* category_theory.graded_object.comap_eq_symm
- \+ *lemma* category_theory.graded_object.comap_eq_trans
- \+ *def* category_theory.graded_object.comap_equiv
- \+ *def* category_theory.graded_object.comap_id
- \+ *lemma* category_theory.graded_object.comp_apply
- \+ *lemma* category_theory.graded_object.id_apply
- \+ *def* category_theory.graded_object.total
- \+ *def* category_theory.graded_object
- \+ *abbreviation* category_theory.graded_object_with_shift

Modified src/category_theory/limits/shapes/zero.lean


Added src/category_theory/shift.lean
- \+ *def* category_theory.shift
- \+ *lemma* category_theory.shift_zero_eq_zero



## [2020-03-25 21:56:35](https://github.com/leanprover-community/mathlib/commit/e04892e)
feat(topology/metric_space/isometry): add_left/right, neg ([#2234](https://github.com/leanprover-community/mathlib/pull/2234))
Also add some lemmas from `equiv` namespace to `isometric`.
#### Estimated changes
Modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometric.apply_symm_apply
- \+ *lemma* isometric.eq_symm_apply
- \+ *lemma* isometric.ext
- \+ *lemma* isometric.symm_apply_apply
- \+ *lemma* isometric.symm_apply_eq
- \+ *lemma* isometric.trans_apply



## [2020-03-25 19:18:04](https://github.com/leanprover-community/mathlib/commit/bb01537)
feat(topology/local_homeomorph): a few facts about `local_homeomorph` ([#2231](https://github.com/leanprover-community/mathlib/pull/2231))
* `eventually_inv_right`, `eventually_inv_left`
* `is_O_congr`, `is_o_congr`
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *lemma* homeomorph.is_O_congr
- \+ *lemma* homeomorph.is_O_with_congr
- \+ *lemma* homeomorph.is_o_congr
- \+ *lemma* local_homeomorph.is_O_congr
- \+ *lemma* local_homeomorph.is_O_with_congr
- \+ *lemma* local_homeomorph.is_o_congr

Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.eventually_left_inverse'
- \+ *lemma* local_homeomorph.eventually_left_inverse
- \+ *lemma* local_homeomorph.eventually_right_inverse'
- \+ *lemma* local_homeomorph.eventually_right_inverse



## [2020-03-25 16:34:50](https://github.com/leanprover-community/mathlib/commit/05aa955)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-25 15:44:21](https://github.com/leanprover-community/mathlib/commit/bedb810)
feat(*): a few more theorems about `unique` and `subsingleton` ([#2230](https://github.com/leanprover-community/mathlib/pull/2230))
* feat(*): a few more theorems about `unique` and `subsingleton`
* Fix compile, fix two non-terminate `simp`s
* Update src/topology/metric_space/antilipschitz.lean
This lemma will go to another PR
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.subsingleton_univ
- \+ *lemma* subsingleton.eq_univ_of_nonempty
- \+ *lemma* subsingleton.set_cases

Modified src/logic/unique.lean
- \+ *lemma* function.injective.comap_subsingleton
- \+ *def* function.surjective.unique
- \+ *lemma* nonempty_unique_or_exists_ne
- \+ *lemma* subsingleton_or_exists_ne
- \- *def* unique.of_surjective

Modified src/topology/basic.lean
- \+ *lemma* subsingleton.is_closed
- \+ *lemma* subsingleton.is_open

Modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* antilipschitz_with.of_subsingleton



## [2020-03-25 13:11:33](https://github.com/leanprover-community/mathlib/commit/1eae0be)
feat(data/equiv): pi_congr ([#2204](https://github.com/leanprover-community/mathlib/pull/2204))
* feat(data/equiv): pi_congr
* docstrings
* change case for consistency
* tidying up
* switching names
* fixes
* Update src/data/equiv/basic.lean
* implicit arguments
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.Pi_congr
- \+ *def* equiv.Pi_congr_left'
- \+ *lemma* equiv.Pi_congr_left'_apply
- \+ *lemma* equiv.Pi_congr_left'_symm_apply
- \+ *def* equiv.Pi_congr_left



## [2020-03-25 10:30:42](https://github.com/leanprover-community/mathlib/commit/83014bf)
chore(README): add Bryan; alphabetize ([#2238](https://github.com/leanprover-community/mathlib/pull/2238))
#### Estimated changes
Modified README.md




## [2020-03-25 03:10:56](https://github.com/leanprover-community/mathlib/commit/d9083bc)
chore(algebra/ordered_field): merge `inv_pos` / `zero_lt_inv` with `inv_pos'` / `inv_neg` ([#2226](https://github.com/leanprover-community/mathlib/pull/2226))
* chore(algebra/ordered_field): merge `inv_pos` / `zero_lt_inv` with `inv_pos'` / `inv_neg`
Also move some lemmas to `linear_ordered_field`
* Update src/data/real/hyperreal.lean
* Fix compile
* Actually fix compile of `data/real/hyperreal`
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/algebra/ordered_field.lean
- \+/\- *lemma* inv_lt_zero
- \- *lemma* inv_neg'
- \- *lemma* inv_pos'
- \+/\- *lemma* inv_pos

Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/specific_limits.lean


Modified src/data/complex/exponential.lean


Modified src/data/rat/cast.lean


Modified src/data/real/basic.lean


Modified src/data/real/hyperreal.lean
- \+/\- *lemma* hyperreal.omega_pos

Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/gromov_hausdorff.lean




## [2020-03-25 00:53:41](https://github.com/leanprover-community/mathlib/commit/24b82c9)
feat(tactic/core): trace_if_enabled ([#2209](https://github.com/leanprover-community/mathlib/pull/2209))
* feat(tactic/core): trace_for
* typo
* oops
* oops
* rename to trace_if_enabled
* trace_state_if_enabled
#### Estimated changes
Modified src/tactic/chain.lean


Modified src/tactic/core.lean


Modified src/tactic/finish.lean


Modified src/tactic/suggest.lean




## [2020-03-24 22:07:53](https://github.com/leanprover-community/mathlib/commit/efdc850)
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
#### Estimated changes
Modified src/tactic/basic.lean


Added src/tactic/converter/apply_congr.lean


Modified src/tactic/converter/interactive.lean


Modified src/tactic/doc_commands.lean


Added test/conv/apply_congr.lean




## [2020-03-24 18:51:00](https://github.com/leanprover-community/mathlib/commit/5437b10)
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
#### Estimated changes
Modified src/tactic/basic.lean


Added src/tactic/show_term.lean




## [2020-03-24 16:01:34](https://github.com/leanprover-community/mathlib/commit/5f376b2)
feat(data/equiv): sigma_congr ([#2205](https://github.com/leanprover-community/mathlib/pull/2205))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.sigma_congr
- \+ *def* equiv.sigma_congr_left'



## [2020-03-24 12:31:39](https://github.com/leanprover-community/mathlib/commit/bb6e1d4)
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
#### Estimated changes
Modified .github/PULL_REQUEST_TEMPLATE.md


Modified README.md


Modified archive/README.md


Modified docs/commands.md


Modified docs/contribute/doc.md


Modified docs/contribute/index.md


Modified docs/extras/calc.md


Modified docs/extras/conv.md


Modified docs/extras/simp.md


Modified docs/extras/tactic_writing.md


Modified docs/extras/well_founded_recursion.md


Modified docs/holes.md


Modified docs/tactics.md


Modified docs/theories/category_theory.md


Modified src/category_theory/category/default.lean




## [2020-03-24 09:46:52](https://github.com/leanprover-community/mathlib/commit/b504430)
feat(linear_algebra): add range_le_ker_iff ([#2229](https://github.com/leanprover-community/mathlib/pull/2229))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.range_le_ker_iff



## [2020-03-23 18:23:19](https://github.com/leanprover-community/mathlib/commit/6a7e55e)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-23 17:30:32](https://github.com/leanprover-community/mathlib/commit/9a9794d)
doc(data/int/gcd): attribution + module doc ([#2217](https://github.com/leanprover-community/mathlib/pull/2217))
* doc(data/int/gcd): attribution + module doc
* reword
#### Estimated changes
Modified src/data/int/gcd.lean
- \+/\- *theorem* nat.gcd_eq_gcd_ab
- \+/\- *theorem* nat.xgcd_aux_P
- \+/\- *theorem* nat.xgcd_aux_rec



## [2020-03-23 14:57:34](https://github.com/leanprover-community/mathlib/commit/9832fba)
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
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* set.maps_to.coe_restrict_apply
- \+ *theorem* set.maps_to.iterate
- \+ *theorem* set.maps_to.iterate_restrict
- \+ *def* set.maps_to.restrict

Modified src/data/subtype.lean
- \+ *lemma* subtype.val_eq_coe

Modified src/topology/constructions.lean
- \+ *lemma* continuous_subtype_coe

Modified src/topology/metric_space/contracting.lean
- \+ *lemma* contracting_with.apriori_edist_iterate_efixed_point_le'
- \+ *lemma* contracting_with.apriori_edist_iterate_efixed_point_le
- \+/\- *lemma* contracting_with.dist_fixed_point_le
- \+ *lemma* contracting_with.edist_efixed_point_le'
- \+ *lemma* contracting_with.edist_efixed_point_le
- \+ *lemma* contracting_with.edist_efixed_point_lt_top'
- \+ *lemma* contracting_with.edist_efixed_point_lt_top
- \+ *lemma* contracting_with.edist_inequality
- \+ *lemma* contracting_with.edist_le_of_fixed_point
- \+ *lemma* contracting_with.efixed_point_eq_of_edist_lt_top'
- \+ *lemma* contracting_with.efixed_point_eq_of_edist_lt_top
- \+ *lemma* contracting_with.efixed_point_is_fixed'
- \+ *lemma* contracting_with.efixed_point_is_fixed
- \+ *lemma* contracting_with.efixed_point_mem'
- \+ *lemma* contracting_with.eq_or_edist_eq_top_of_fixed_points
- \+ *theorem* contracting_with.exists_fixed_point'
- \+/\- *theorem* contracting_with.exists_fixed_point
- \+ *def* contracting_with.fixed_point
- \+/\- *lemma* contracting_with.fixed_point_is_fixed
- \+/\- *lemma* contracting_with.fixed_point_unique
- \+ *lemma* contracting_with.one_sub_K_ne_top
- \+ *lemma* contracting_with.one_sub_K_ne_zero
- \+ *lemma* contracting_with.one_sub_K_pos'
- \+/\- *lemma* contracting_with.one_sub_K_pos
- \+ *lemma* contracting_with.restrict
- \+ *lemma* contracting_with.tendsto_iterate_efixed_point'
- \+ *lemma* contracting_with.tendsto_iterate_efixed_point
- \+ *lemma* contracting_with.tendsto_iterate_fixed_point
- \+/\- *lemma* contracting_with.to_lipschitz_with

Modified src/topology/metric_space/emetric_space.lean
- \+ *def* emetric.edist_lt_top_setoid

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* lipschitz_with.edist_lt_top



## [2020-03-23 12:25:53](https://github.com/leanprover-community/mathlib/commit/25df50e)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-23 11:21:48](https://github.com/leanprover-community/mathlib/commit/5b2c952)
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
#### Estimated changes
Modified src/algebra/module.lean
- \+ *theorem* smul_eq_zero
- \+ *lemma* submodule.coe_mk
- \+/\- *lemma* submodule.coe_sub

Modified src/analysis/convex/basic.lean
- \+ *lemma* convex_iff_forall_pos

Added src/analysis/convex/cone.lean
- \+ *lemma* convex.mem_to_cone'
- \+ *lemma* convex.mem_to_cone
- \+ *lemma* convex.subset_to_cone
- \+ *def* convex.to_cone
- \+ *lemma* convex.to_cone_eq_Inf
- \+ *lemma* convex.to_cone_is_least
- \+ *lemma* convex_cone.add_mem
- \+ *lemma* convex_cone.coe_inf
- \+ *def* convex_cone.comap
- \+ *lemma* convex_cone.comap_comap
- \+ *lemma* convex_cone.comap_id
- \+ *lemma* convex_cone.convex
- \+ *theorem* convex_cone.ext'
- \+ *theorem* convex_cone.ext
- \+ *def* convex_cone.map
- \+ *lemma* convex_cone.map_id
- \+ *lemma* convex_cone.map_map
- \+ *lemma* convex_cone.mem_Inf
- \+ *lemma* convex_cone.mem_bot
- \+ *lemma* convex_cone.mem_coe
- \+ *lemma* convex_cone.mem_comap
- \+ *lemma* convex_cone.mem_inf
- \+ *lemma* convex_cone.mem_mk
- \+ *lemma* convex_cone.mem_top
- \+ *lemma* convex_cone.smul_mem
- \+ *lemma* convex_cone.smul_mem_iff
- \+ *structure* convex_cone
- \+ *lemma* convex_hull_to_cone_eq_Inf
- \+ *lemma* convex_hull_to_cone_is_least
- \+ *theorem* exists_extension_of_le_sublinear
- \+ *theorem* riesz_extension.exists_top
- \+ *lemma* riesz_extension.step
- \+ *theorem* riesz_extension

Added src/analysis/normed_space/hahn_banach.lean
- \+ *theorem* exists_extension_norm_eq

Modified src/data/set/basic.lean
- \+ *theorem* set.bex_image_iff
- \+ *theorem* set_coe.exists'

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.prod_apply
- \+ *lemma* linear_equiv.prod_symm
- \+ *lemma* linear_equiv.refl_apply
- \+ *theorem* submodule.coe_of_le
- \+ *lemma* submodule.disjoint_span_singleton
- \+/\- *theorem* submodule.of_le_apply

Added src/linear_algebra/linear_pmap.lean
- \+ *def* linear_map.comp_pmap
- \+ *lemma* linear_map.comp_pmap_apply
- \+ *def* linear_map.to_pmap
- \+ *lemma* linear_map.to_pmap_apply
- \+ *def* linear_pmap.cod_restrict
- \+ *def* linear_pmap.comp
- \+ *def* linear_pmap.coprod
- \+ *lemma* linear_pmap.coprod_apply
- \+ *lemma* linear_pmap.domain_mk_span_singleton
- \+ *lemma* linear_pmap.domain_mono
- \+ *lemma* linear_pmap.domain_sup
- \+ *def* linear_pmap.eq_locus
- \+ *lemma* linear_pmap.eq_of_le_of_domain_eq
- \+ *lemma* linear_pmap.fst_apply
- \+ *lemma* linear_pmap.le_of_eq_locus_ge
- \+ *lemma* linear_pmap.map_add
- \+ *lemma* linear_pmap.map_neg
- \+ *lemma* linear_pmap.map_smul
- \+ *lemma* linear_pmap.map_sub
- \+ *lemma* linear_pmap.map_zero
- \+ *lemma* linear_pmap.mk_apply
- \+ *lemma* linear_pmap.mk_span_singleton_apply
- \+ *lemma* linear_pmap.neg_apply
- \+ *lemma* linear_pmap.snd_apply
- \+ *lemma* linear_pmap.sup_apply
- \+ *lemma* linear_pmap.sup_h_of_disjoint
- \+ *lemma* linear_pmap.to_fun_eq_coe
- \+ *structure* linear_pmap
- \+ *lemma* subtype.coe_prop

Modified src/order/basic.lean
- \+ *theorem* directed.mono
- \- *theorem* directed_mono
- \+ *theorem* directed_on.mono
- \+ *theorem* directed_on_image

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* exists_between_of_forall_le



## [2020-03-23 04:27:27](https://github.com/leanprover-community/mathlib/commit/d3d78a9)
chore(ring_theory/algebra): generalize restrict_scalars to noncommutative algebras ([#2216](https://github.com/leanprover-community/mathlib/pull/2216))
#### Estimated changes
Modified src/ring_theory/algebra.lean




## [2020-03-23 01:53:56](https://github.com/leanprover-community/mathlib/commit/fe40a15)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-23 01:05:38](https://github.com/leanprover-community/mathlib/commit/6aa5572)
feat(algebra/module): `f : E →+ F` is `ℚ`-linear ([#2215](https://github.com/leanprover-community/mathlib/pull/2215))
* feat(algebra/module): `f : E →+ F` is `ℚ`-linear
Also cleanup similar lemmas about `ℕ` and `ℤ`.
* Fix a typo
#### Estimated changes
Modified src/algebra/direct_limit.lean
- \+/\- *lemma* add_comm_group.direct_limit.directed_system

Modified src/algebra/module.lean
- \+ *lemma* add_monoid_hom.map_int_cast_smul
- \+ *lemma* add_monoid_hom.map_nat_cast_smul
- \+ *lemma* add_monoid_hom.map_rat_cast_smul
- \+ *lemma* add_monoid_hom.map_rat_module_smul
- \- *lemma* add_monoid_hom.map_smul_cast
- \+ *def* add_monoid_hom.to_int_linear_map
- \+ *def* add_monoid_hom.to_rat_linear_map
- \- *def* is_add_group_hom.to_linear_map
- \- *lemma* module.add_monoid_smul_eq_smul
- \+/\- *lemma* module.gsmul_eq_smul_cast
- \- *lemma* module.smul_eq_smul
- \+ *lemma* semimodule.add_monoid_smul_eq_smul
- \+ *lemma* semimodule.smul_eq_smul



## [2020-03-22 22:10:26](https://github.com/leanprover-community/mathlib/commit/b9ee94d)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-22 21:15:30](https://github.com/leanprover-community/mathlib/commit/7f103fd)
fix(tactic/transport): make `to_additive` copy `protected`status ([#2212](https://github.com/leanprover-community/mathlib/pull/2212))
* fix(tactic/transport): make `to_additive` copy `protected`status
Fixes [#2210](https://github.com/leanprover-community/mathlib/pull/2210), also slightly cleanup `algebra/group/units`
* Fix compile (protected `finset.sum`)
* Fix usage of `finset.sum`
* Update src/tactic/transport.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* fix build
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/units.lean
- \- *theorem* nat.add_units_eq_one
- \+ *theorem* nat.add_units_eq_zero

Modified src/data/complex/exponential.lean


Modified src/data/polynomial.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/measure_space.lean


Modified src/tactic/transport.lean


Modified src/topology/algebra/infinite_sum.lean




## [2020-03-22 17:01:05](https://github.com/leanprover-community/mathlib/commit/6febc8c)
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
#### Estimated changes
Modified docs/commands.md


Modified docs/contribute/doc.md


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/module.lean


Modified src/deprecated/group.lean


Modified src/group_theory/coset.lean


Modified src/logic/basic.lean


Modified src/meta/expr.lean


Modified src/tactic/cache.lean
- \- *def* tactic.interactive.my_id

Modified src/tactic/doc_commands.lean
- \+ *def* f

Modified src/tactic/elide.lean


Modified src/tactic/ext.lean


Modified src/tactic/finish.lean


Added src/tactic/fix_reflect_string.lean


Modified src/tactic/lint.lean


Modified src/tactic/localized.lean


Modified src/tactic/norm_cast.lean


Modified src/tactic/norm_num.lean
- \- *def* tactic.interactive.a
- \- *def* tactic.interactive.normed_a

Added test/doc_commands.lean
- \+ *def* bar.foo



## [2020-03-22 13:55:54](https://github.com/leanprover-community/mathlib/commit/4e46b30)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-22 13:06:37](https://github.com/leanprover-community/mathlib/commit/7d02c23)
chore(linear_algebra/*): rename copair, pair to coprod, prod ([#2213](https://github.com/leanprover-community/mathlib/pull/2213))
* chore(linear_algebra/*): rename copair, pair to coprod, prod
* add back mistakenly deleted lemma
* fix sensitivity, change comments to module docs
* docstrings, linting
* Update archive/sensitivity.lean
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/linear_algebra/basic.lean
- \+/\- *theorem* linear_equiv.symm_symm_apply
- \+/\- *theorem* linear_equiv.trans_apply
- \+/\- *theorem* linear_map.comap_le_comap_iff
- \- *theorem* linear_map.comap_pair_prod
- \+ *theorem* linear_map.comap_prod_prod
- \- *def* linear_map.copair
- \- *theorem* linear_map.copair_apply
- \- *theorem* linear_map.copair_inl
- \- *theorem* linear_map.copair_inl_inr
- \- *theorem* linear_map.copair_inr
- \+ *def* linear_map.coprod
- \+ *theorem* linear_map.coprod_apply
- \+ *theorem* linear_map.coprod_inl
- \+ *theorem* linear_map.coprod_inl_inr
- \+ *theorem* linear_map.coprod_inr
- \- *theorem* linear_map.fst_eq_copair
- \+ *theorem* linear_map.fst_eq_coprod
- \- *theorem* linear_map.fst_pair
- \+ *theorem* linear_map.fst_prod
- \- *theorem* linear_map.inl_eq_pair
- \+ *theorem* linear_map.inl_eq_prod
- \- *theorem* linear_map.inr_eq_pair
- \+ *theorem* linear_map.inr_eq_prod
- \+/\- *lemma* linear_map.is_linear_map_prod_iso
- \- *lemma* linear_map.ker_pair
- \+ *lemma* linear_map.ker_prod
- \- *theorem* linear_map.map_copair_prod
- \+ *theorem* linear_map.map_coprod_prod
- \- *def* linear_map.pair
- \- *theorem* linear_map.pair_apply
- \+/\- *theorem* linear_map.pair_fst_snd
- \+/\- *def* linear_map.prod
- \+ *theorem* linear_map.prod_apply
- \- *theorem* linear_map.snd_eq_copair
- \+ *theorem* linear_map.snd_eq_coprod
- \- *theorem* linear_map.snd_pair
- \+ *theorem* linear_map.snd_prod

Modified src/linear_algebra/basis.lean
- \+/\- *lemma* constr_smul
- \+/\- *lemma* is_basis_empty_bot
- \+/\- *lemma* linear_independent.image_subtype
- \+/\- *lemma* linear_independent.total_comp_repr
- \+/\- *def* linear_independent.total_equiv
- \+/\- *lemma* linear_independent_iff_not_mem_span
- \+/\- *lemma* linear_independent_singleton

Modified src/linear_algebra/dimension.lean




## [2020-03-22 08:44:10](https://github.com/leanprover-community/mathlib/commit/3a71499)
feat(ring_theory/algebra) : generalize `rat.algebra_rat` to `division_ring` ([#2208](https://github.com/leanprover-community/mathlib/pull/2208))
Other changes:
* add lemmas about field inverse to `algebra/semiconj` and `algebra/commute`;
* drop `rat.cast`, define `instance : has_coe` right away to avoid
  accidental use of `rat.cast` in theorems;
* define `rat.cast_hom` instead of `is_ring_hom rat.cast`;
* generalize some theorems about from `field` to `division_ring`.
#### Estimated changes
Modified src/algebra/commute.lean
- \+ *theorem* commute.div_left
- \+ *theorem* commute.div_right
- \+ *theorem* commute.finv_finv
- \+ *theorem* commute.finv_left
- \+ *theorem* commute.finv_left_iff
- \+ *theorem* commute.finv_right
- \+ *theorem* commute.finv_right_iff

Modified src/algebra/field_power.lean
- \- *theorem* cast_fpow
- \+ *theorem* rat.cast_fpow

Modified src/algebra/semiconj.lean
- \+ *lemma* semiconj_by.finv_symm_left
- \+ *lemma* semiconj_by.finv_symm_left_iff

Modified src/data/padics/padic_numbers.lean


Modified src/data/rat/cast.lean
- \+/\- *theorem* rat.cast_div
- \+ *def* rat.cast_hom
- \+/\- *theorem* rat.cast_inv
- \+/\- *theorem* rat.cast_mk
- \+/\- *theorem* rat.cast_nonneg
- \+/\- *theorem* rat.cast_pow
- \+ *lemma* rat.coe_cast_hom

Modified src/ring_theory/algebra.lean




## [2020-03-22 04:38:42](https://github.com/leanprover-community/mathlib/commit/9485a85)
fix(linear_algebra/basic): make R explicit in linear_equiv.refl ([#2161](https://github.com/leanprover-community/mathlib/pull/2161))
* fix(linear_algebra/basic): make R explicit in linear_equiv.refl
* getting mathlib to compile again
* better variablism
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_equiv.congr_right

Modified src/topology/algebra/module.lean




## [2020-03-22 02:00:48](https://github.com/leanprover-community/mathlib/commit/19de416)
doc(ring_theory/adjoin_root): add docstring ([#2211](https://github.com/leanprover-community/mathlib/pull/2211))
* docstring for adjoin_root
* adding some quotes
#### Estimated changes
Modified src/ring_theory/adjoin_root.lean




## [2020-03-21 14:18:51-07:00](https://github.com/leanprover-community/mathlib/commit/09401b7)
revert accidental push to master
#### Estimated changes
Modified src/tactic/chain.lean


Modified src/tactic/core.lean


Modified src/tactic/finish.lean


Modified src/tactic/suggest.lean


Modified src/tactic/tidy.lean




## [2020-03-21 14:00:51-07:00](https://github.com/leanprover-community/mathlib/commit/3375126)
feat(tactic/core): trace_for
#### Estimated changes
Modified src/tactic/chain.lean


Modified src/tactic/core.lean


Modified src/tactic/finish.lean


Modified src/tactic/suggest.lean


Modified src/tactic/tidy.lean




## [2020-03-21 19:24:58](https://github.com/leanprover-community/mathlib/commit/af0cf30)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-21 18:41:30](https://github.com/leanprover-community/mathlib/commit/0bd8b94)
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
#### Estimated changes
Modified .github/workflows/build.yml


Modified .gitignore


Added scripts/lint_mathlib.lean


Modified scripts/mk_all.sh


Deleted scripts/mk_nolint.lean


Modified scripts/rm_all.sh


Modified scripts/update_nolints.sh


Modified src/logic/basic.lean


Modified src/logic/function.lean


Modified src/meta/expr.lean


Modified src/tactic/lint.lean


Modified test/lint.lean




## [2020-03-21 10:35:34](https://github.com/leanprover-community/mathlib/commit/dd85db0)
doc(docs/contribute/index.md): remove obsolete recommendation to use lean-3.7.2 branch ([#2206](https://github.com/leanprover-community/mathlib/pull/2206))
#### Estimated changes
Modified docs/contribute/index.md




## [2020-03-21 08:46:38](https://github.com/leanprover-community/mathlib/commit/bc84a20)
chore(leanpkg.toml): Lean 3.7.2c ([#2203](https://github.com/leanprover-community/mathlib/pull/2203))
* chore(leanpkg.toml): Lean 3.7.2c
Lean 3.7.1c had a bug that prevented Lean on windows from importing oleans properly (see https://github.com/leanprover-community/lean/pull/155). This is fixed in Lean 3.7.2c.
* update contribute/index.md
#### Estimated changes
Modified docs/contribute/index.md


Modified leanpkg.toml




## [2020-03-21 02:10:50](https://github.com/leanprover-community/mathlib/commit/34bac8d)
feat(category_theory): add naturality_assoc simp lemma ([#2200](https://github.com/leanprover-community/mathlib/pull/2200))
#### Estimated changes
Modified src/category_theory/natural_transformation.lean




## [2020-03-20 23:38:07](https://github.com/leanprover-community/mathlib/commit/99ba8f4)
chore(category_theory): change monoidal_of_has_finite_products to use binary products ([#2190](https://github.com/leanprover-community/mathlib/pull/2190))
* chore(category_theory): change monoidal_of_has_finite_products to use binary products
* remove some simp annotations for now
* fixes
#### Estimated changes
Modified src/category_theory/monoidal/of_has_finite_products.lean
- \+ *lemma* category_theory.monoidal_of_has_finite_coproducts.associator_hom
- \+ *lemma* category_theory.monoidal_of_has_finite_coproducts.left_unitor_hom
- \+ *lemma* category_theory.monoidal_of_has_finite_coproducts.left_unitor_inv
- \+ *lemma* category_theory.monoidal_of_has_finite_coproducts.right_unitor_hom
- \+ *lemma* category_theory.monoidal_of_has_finite_coproducts.right_unitor_inv
- \+/\- *def* category_theory.monoidal_of_has_finite_coproducts
- \+ *lemma* category_theory.monoidal_of_has_finite_products.associator_hom
- \+ *lemma* category_theory.monoidal_of_has_finite_products.left_unitor_hom
- \+ *lemma* category_theory.monoidal_of_has_finite_products.left_unitor_inv
- \+ *lemma* category_theory.monoidal_of_has_finite_products.right_unitor_hom
- \+ *lemma* category_theory.monoidal_of_has_finite_products.right_unitor_inv
- \+/\- *def* category_theory.monoidal_of_has_finite_products



## [2020-03-20 21:22:50](https://github.com/leanprover-community/mathlib/commit/9420167)
feat(category_theory): unbundled functors and lax monoidal functors ([#2193](https://github.com/leanprover-community/mathlib/pull/2193))
* feat(category_theory): unbundled functors and lax monoidal functors
* doc string
#### Estimated changes
Modified src/category_theory/functor.lean


Added src/category_theory/functorial.lean
- \+ *def* category_theory.functor.of
- \+ *def* category_theory.functorial_comp
- \+ *def* category_theory.map
- \+ *lemma* category_theory.map_functorial_obj

Added src/category_theory/monoidal/functorial.lean
- \+ *def* category_theory.lax_monoidal_functor.of



## [2020-03-20 18:53:45](https://github.com/leanprover-community/mathlib/commit/b224943)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-20 17:26:39](https://github.com/leanprover-community/mathlib/commit/8d44098)
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
#### Estimated changes
Modified src/data/finsupp.lean
- \- *lemma* finsupp.mul_def
- \- *lemma* finsupp.one_def
- \- *lemma* finsupp.prod_single
- \- *lemma* finsupp.single_mul_single
- \- *lemma* finsupp.support_mul

Added src/data/finsupp/pointwise.lean
- \+ *lemma* finsupp.mul_apply
- \+ *lemma* finsupp.support_mul

Added src/data/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.mul_def
- \+ *lemma* add_monoid_algebra.one_def
- \+ *lemma* add_monoid_algebra.prod_single
- \+ *lemma* add_monoid_algebra.single_mul_single
- \+ *lemma* add_monoid_algebra.support_mul
- \+ *def* add_monoid_algebra
- \+ *lemma* monoid_algebra.mul_def
- \+ *lemma* monoid_algebra.one_def
- \+ *lemma* monoid_algebra.prod_single
- \+ *lemma* monoid_algebra.single_mul_single
- \+ *lemma* monoid_algebra.support_mul
- \+ *def* monoid_algebra

Modified src/data/mv_polynomial.lean
- \+ *def* mv_polynomial.coeff_coe_to_fun
- \+/\- *def* mv_polynomial

Modified src/data/polynomial.lean
- \+/\- *def* polynomial.C
- \+/\- *def* polynomial.X
- \+ *def* polynomial.monomial
- \+/\- *lemma* polynomial.single_eq_C_mul_X
- \+/\- *def* polynomial

Modified src/linear_algebra/finsupp.lean


Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/power_series.lean
- \- *def* polynomial.monomial



## [2020-03-20 15:01:46](https://github.com/leanprover-community/mathlib/commit/0f1b465)
feat(category_theory/limits): the isomorphism expressing preservation of chosen limits ([#2192](https://github.com/leanprover-community/mathlib/pull/2192))
* feat(category_theory/limits): the isomorphism expressing preservation of chosen limits
* Update src/category_theory/limits/limits.lean
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.is_colimit.cone_point_unique_up_to_iso
- \+ *def* category_theory.limits.is_limit.cone_point_unique_up_to_iso

Modified src/category_theory/limits/preserves.lean
- \+ *def* category_theory.limits.preserves_colimit_iso
- \+ *def* category_theory.limits.preserves_limit_iso



## [2020-03-20 12:24:26](https://github.com/leanprover-community/mathlib/commit/c66c4af)
chore(algebra/Module/monoidal): add the simp lemmas for unitors and associativity ([#2196](https://github.com/leanprover-community/mathlib/pull/2196))
* feat(algebra/category/Module/monoidal): simp lemmas
* oops
* depressingly easy
* order of arguments
#### Estimated changes
Modified src/algebra/category/Module/basic.lean
- \- *def* Module.of_self
- \+ *def* Module.of_self_iso

Modified src/algebra/category/Module/monoidal.lean
- \+ *lemma* Module.monoidal_category.associator_hom
- \+ *lemma* Module.monoidal_category.left_unitor_hom
- \+ *lemma* Module.monoidal_category.right_unitor_hom



## [2020-03-20 10:05:42](https://github.com/leanprover-community/mathlib/commit/d93e0dd)
chore(category_theory): missing simp lemmas ([#2188](https://github.com/leanprover-community/mathlib/pull/2188))
* chore(category_theory): missing simp lemmas
* Apply suggestions from code review
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/category_theory/types.lean
- \+ *lemma* category_theory.functor_to_types.map_hom_map_inv_apply
- \+ *lemma* category_theory.functor_to_types.map_inv_map_hom_apply



## [2020-03-20 07:32:29](https://github.com/leanprover-community/mathlib/commit/b4e6313)
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
#### Estimated changes
Modified src/category_theory/discrete_category.lean


Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* category_theory.limits.equivalence_preserves_zero_morphisms
- \+ *lemma* category_theory.limits.has_zero_morphisms.ext

Modified src/tactic/ext.lean
- \- *lemma* ulift.ext



## [2020-03-20 05:08:55](https://github.com/leanprover-community/mathlib/commit/cc04132)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-20 03:59:59](https://github.com/leanprover-community/mathlib/commit/6c97ce0)
feat(category_theory): some natural isomorphisms related to composition by functors ([#2189](https://github.com/leanprover-community/mathlib/pull/2189))
* feat(category_theory): some natural isomorphisms related to composition by functors
* tidy up
* cleanup
* fix
* better design
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *def* category_theory.limits.map_pair
- \+ *def* category_theory.limits.map_pair_iso
- \+/\- *lemma* category_theory.limits.map_pair_left
- \+/\- *lemma* category_theory.limits.map_pair_right
- \+ *def* category_theory.limits.pair_comp
- \- *def* category_theory.limits.pair_function
- \+/\- *lemma* category_theory.limits.pair_obj_left
- \+/\- *lemma* category_theory.limits.pair_obj_right

Modified src/category_theory/pempty.lean
- \+ *def* category_theory.functor.empty_ext



## [2020-03-20 01:35:59](https://github.com/leanprover-community/mathlib/commit/d12bbc0)
feat(data/zmod): lemmas about totient and zmod ([#2158](https://github.com/leanprover-community/mathlib/pull/2158))
* feat(data/zmod): lemmas about totient and zmod
* docstring
* Changes based on Johan's comments
* fix build
* subsingleton (units(zmod 2))
#### Estimated changes
Modified src/data/fintype.lean


Modified src/data/nat/totient.lean
- \+ *theorem* nat.totient_zero
- \+ *lemma* zmod.card_units_eq_totient

Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.cast_unit_of_coprime
- \+ *def* zmod.unit_of_coprime

Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/field_theory/finite.lean
- \+ *lemma* nat.modeq.pow_totient
- \+ *lemma* zmod.pow_totient



## [2020-03-19 23:15:04](https://github.com/leanprover-community/mathlib/commit/3dd95a2)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-19 21:56:33](https://github.com/leanprover-community/mathlib/commit/1a398a7)
docs(category_theory/limits): adding many docstrings ([#2185](https://github.com/leanprover-community/mathlib/pull/2185))
* lots of comments!
* remove #lint
* Apply suggestions from code review
lots of missing "co"s
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/category_theory/limits/limits.lean




## [2020-03-19 18:52:34](https://github.com/leanprover-community/mathlib/commit/344a41e)
feat(data/finset): monotone bijection from fin k ([#2163](https://github.com/leanprover-community/mathlib/pull/2163))
* feat(data/finset): increasing bijection between fin k and an ordered finset
* fix build
* fix linter
* make argument explicit
* add equiv for fintype
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* dite_comp_equiv_update

Modified src/data/finset.lean
- \+ *lemma* finset.bij_on_mono_of_fin
- \+ *def* finset.mono_of_fin
- \+/\- *theorem* finset.sort_sorted_lt
- \+ *lemma* finset.sorted_last_eq_max'
- \+ *lemma* finset.sorted_zero_eq_min'

Modified src/data/fintype.lean
- \+ *lemma* finset.card_fin
- \+ *lemma* fintype.card_finset

Modified src/data/list/sort.lean
- \+ *lemma* list.nth_le_of_sorted_of_le

Modified src/group_theory/sylow.lean




## [2020-03-19 16:32:37](https://github.com/leanprover-community/mathlib/commit/b3ef685)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-19 15:12:14](https://github.com/leanprover-community/mathlib/commit/9dbc606)
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
#### Estimated changes
Modified docs/tactics.md


Modified scripts/nolints.txt


Modified src/algebra/associated.lean


Modified src/algebra/direct_limit.lean


Modified src/algebra/order_functions.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/punit_instances.lean


Modified src/analysis/ODE/gronwall.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/specific_limits.lean


Modified src/category_theory/limits/lattice.lean


Modified src/data/analysis/filter.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/finset.lean
- \+ *lemma* infi_eq_infi_finset
- \- *lemma* lattice.infi_eq_infi_finset
- \- *lemma* lattice.supr_eq_supr_finset
- \+ *lemma* supr_eq_supr_finset

Modified src/data/list/min_max.lean


Modified src/data/multiset.lean


Modified src/data/mv_polynomial.lean


Modified src/data/nat/enat.lean


Modified src/data/pequiv.lean


Modified src/data/pnat/basic.lean


Modified src/data/pnat/factors.lean


Modified src/data/polynomial.lean


Modified src/data/rat/order.lean


Modified src/data/real/basic.lean
- \+ *lemma* real.Inf_def
- \+/\- *theorem* real.Inf_empty
- \+/\- *theorem* real.Inf_of_not_bdd_below
- \+ *lemma* real.Sup_def
- \+/\- *theorem* real.Sup_empty
- \+/\- *theorem* real.Sup_of_not_bdd_above
- \+/\- *theorem* real.Sup_univ

Modified src/data/real/ennreal.lean


Modified src/data/real/ereal.lean


Modified src/data/real/hyperreal.lean
- \+/\- *theorem* hyperreal.is_st_Sup
- \+/\- *theorem* hyperreal.st_eq_Sup

Modified src/data/real/nnreal.lean


Modified src/data/rel.lean


Modified src/data/semiquot.lean


Modified src/data/set/basic.lean


Modified src/data/set/disjointed.lean


Modified src/data/set/finite.lean


Modified src/data/set/intervals/basic.lean


Modified src/data/set/intervals/disjoint.lean


Modified src/data/set/lattice.lean


Modified src/data/setoid.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/manifold.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/monoid_localization.lean


Modified src/group_theory/submonoid.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/indicator_function.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/order/boolean_algebra.lean
- \+ *theorem* boolean_algebra.sub_le_sub
- \+ *theorem* compl_bot
- \+ *theorem* compl_compl'
- \+ *theorem* compl_inf
- \+ *theorem* compl_inf_eq_bot
- \+ *theorem* compl_inj
- \+ *theorem* compl_inj_iff
- \+ *theorem* compl_le_compl
- \+ *theorem* compl_le_compl_iff_le
- \+ *theorem* compl_le_iff_compl_le
- \+ *theorem* compl_le_of_compl_le
- \+ *theorem* compl_sup
- \+ *theorem* compl_sup_eq_top
- \+ *theorem* compl_top
- \+ *theorem* compl_unique
- \+ *theorem* inf_compl_eq_bot
- \- *theorem* lattice.inf_neg_eq_bot
- \- *theorem* lattice.le_neg_of_le_neg
- \- *theorem* lattice.neg_bot
- \- *theorem* lattice.neg_eq_neg_iff
- \- *theorem* lattice.neg_eq_neg_of_eq
- \- *theorem* lattice.neg_inf
- \- *theorem* lattice.neg_inf_eq_bot
- \- *theorem* lattice.neg_le_iff_neg_le
- \- *theorem* lattice.neg_le_neg
- \- *theorem* lattice.neg_le_neg_iff_le
- \- *theorem* lattice.neg_le_of_neg_le
- \- *theorem* lattice.neg_neg
- \- *theorem* lattice.neg_sup
- \- *theorem* lattice.neg_sup_eq_top
- \- *theorem* lattice.neg_top
- \- *theorem* lattice.neg_unique
- \- *theorem* lattice.sub_eq
- \- *theorem* lattice.sub_eq_left
- \- *theorem* lattice.sub_le_sub
- \- *theorem* lattice.sup_neg_eq_top
- \- *theorem* lattice.sup_sub_same
- \+ *theorem* le_compl_of_le_compl
- \+ *theorem* sub_eq
- \+ *theorem* sub_eq_left
- \+ *theorem* sup_compl_eq_top
- \+ *theorem* sup_sub_same

Modified src/order/bounded_lattice.lean
- \+ *theorem* bot_inf_eq
- \+ *theorem* bot_le
- \+ *lemma* bot_lt_iff_ne_bot
- \+ *theorem* bot_sup_eq
- \+ *theorem* bot_unique
- \+ *theorem* bounded_lattice.ext
- \+ *theorem* eq_bot_iff
- \+ *theorem* eq_bot_mono
- \+ *theorem* eq_top_iff
- \+ *theorem* eq_top_mono
- \+ *theorem* inf_bot_eq
- \+ *lemma* inf_eq_bot_iff_le_compl
- \+ *theorem* inf_eq_top_iff
- \+ *theorem* inf_top_eq
- \- *theorem* lattice.bot_inf_eq
- \- *theorem* lattice.bot_le
- \- *lemma* lattice.bot_lt_iff_ne_bot
- \- *theorem* lattice.bot_sup_eq
- \- *theorem* lattice.bot_unique
- \- *theorem* lattice.bounded_lattice.ext
- \- *theorem* lattice.eq_bot_iff
- \- *theorem* lattice.eq_bot_mono
- \- *theorem* lattice.eq_top_iff
- \- *theorem* lattice.eq_top_mono
- \- *theorem* lattice.inf_bot_eq
- \- *lemma* lattice.inf_eq_bot_iff_le_compl
- \- *theorem* lattice.inf_eq_top_iff
- \- *theorem* lattice.inf_top_eq
- \- *theorem* lattice.le_bot_iff
- \- *theorem* lattice.le_top
- \- *lemma* lattice.lt_top_iff_ne_top
- \- *theorem* lattice.monotone_and
- \- *theorem* lattice.monotone_or
- \- *lemma* lattice.ne_bot_of_gt
- \- *theorem* lattice.ne_bot_of_le_ne_bot
- \- *theorem* lattice.ne_top_of_le_ne_top
- \- *lemma* lattice.ne_top_of_lt
- \- *theorem* lattice.not_lt_bot
- \- *theorem* lattice.not_top_lt
- \- *theorem* lattice.order_bot.ext
- \- *theorem* lattice.order_bot.ext_bot
- \- *theorem* lattice.order_top.ext
- \- *theorem* lattice.order_top.ext_top
- \- *theorem* lattice.sup_bot_eq
- \- *theorem* lattice.sup_eq_bot_iff
- \- *theorem* lattice.sup_top_eq
- \- *theorem* lattice.top_inf_eq
- \- *theorem* lattice.top_le_iff
- \- *theorem* lattice.top_sup_eq
- \- *theorem* lattice.top_unique
- \+ *theorem* le_bot_iff
- \+ *theorem* le_top
- \+ *lemma* lt_top_iff_ne_top
- \+ *theorem* monotone_and
- \+ *theorem* monotone_or
- \+ *lemma* ne_bot_of_gt
- \+ *theorem* ne_bot_of_le_ne_bot
- \+ *theorem* ne_top_of_le_ne_top
- \+ *lemma* ne_top_of_lt
- \+ *theorem* not_lt_bot
- \+ *theorem* not_top_lt
- \+ *theorem* order_bot.ext
- \+ *theorem* order_bot.ext_bot
- \+ *theorem* order_top.ext
- \+ *theorem* order_top.ext_top
- \+ *theorem* sup_bot_eq
- \+ *theorem* sup_eq_bot_iff
- \+ *theorem* sup_top_eq
- \+ *theorem* top_inf_eq
- \+ *theorem* top_le_iff
- \+ *theorem* top_sup_eq
- \+ *theorem* top_unique

Modified src/order/bounds.lean


Modified src/order/complete_boolean_algebra.lean
- \+ *theorem* Inf_sup_Inf
- \+ *theorem* Inf_sup_eq
- \+ *theorem* Sup_inf_Sup
- \+ *theorem* Sup_inf_eq
- \+ *theorem* compl_Inf
- \+ *theorem* compl_Sup
- \+ *theorem* compl_infi
- \+ *theorem* compl_supr
- \+ *theorem* inf_Sup_eq
- \- *theorem* lattice.Inf_sup_Inf
- \- *theorem* lattice.Inf_sup_eq
- \- *theorem* lattice.Sup_inf_Sup
- \- *theorem* lattice.Sup_inf_eq
- \- *theorem* lattice.inf_Sup_eq
- \- *theorem* lattice.neg_Inf
- \- *theorem* lattice.neg_Sup
- \- *theorem* lattice.neg_infi
- \- *theorem* lattice.neg_supr
- \- *theorem* lattice.sup_Inf_eq
- \+ *theorem* sup_Inf_eq

Modified src/order/complete_lattice.lean
- \+ *def* Inf
- \+ *lemma* Inf_Prop_eq
- \+ *lemma* Inf_apply
- \+ *theorem* Inf_empty
- \+ *lemma* Inf_eq_bot
- \+ *theorem* Inf_eq_infi
- \+ *theorem* Inf_eq_top
- \+ *theorem* Inf_image
- \+ *theorem* Inf_insert
- \+ *theorem* Inf_le
- \+ *theorem* Inf_le_Inf
- \+ *theorem* Inf_le_Sup
- \+ *theorem* Inf_le_of_le
- \+ *lemma* Inf_lt_iff
- \+ *theorem* Inf_pair
- \+ *lemma* Inf_range
- \+ *theorem* Inf_singleton
- \+ *theorem* Inf_union
- \+ *theorem* Inf_univ
- \+ *def* Sup
- \+ *lemma* Sup_Prop_eq
- \+ *lemma* Sup_apply
- \+ *theorem* Sup_empty
- \+ *theorem* Sup_eq_bot
- \+ *theorem* Sup_eq_supr
- \+ *lemma* Sup_eq_top
- \+ *theorem* Sup_image
- \+ *theorem* Sup_insert
- \+ *theorem* Sup_inter_le
- \+ *theorem* Sup_le
- \+ *theorem* Sup_le_Sup
- \+ *theorem* Sup_le_iff
- \+ *theorem* Sup_pair
- \+ *lemma* Sup_range
- \+ *theorem* Sup_singleton
- \+ *theorem* Sup_union
- \+ *theorem* Sup_univ
- \+ *lemma* binfi_inf
- \+ *lemma* has_Inf_to_nonempty
- \+ *lemma* has_Sup_to_nonempty
- \+ *lemma* inf_infi
- \+ *def* infi
- \+ *lemma* infi_Prop_eq
- \+ *theorem* infi_and
- \+ *lemma* infi_apply
- \+ *lemma* infi_bool_eq
- \+ *theorem* infi_comm
- \+ *theorem* infi_congr_Prop
- \+ *theorem* infi_const
- \+ *theorem* infi_empty
- \+ *theorem* infi_emptyset
- \+ *lemma* infi_eq_bot
- \+ *lemma* infi_eq_dif
- \+ *lemma* infi_eq_if
- \+ *lemma* infi_eq_top
- \+ *theorem* infi_exists
- \+ *theorem* infi_false
- \+ *lemma* infi_image
- \+ *lemma* infi_inf
- \+ *theorem* infi_inf_eq
- \+ *theorem* infi_infi_eq_left
- \+ *theorem* infi_infi_eq_right
- \+ *theorem* infi_insert
- \+ *theorem* infi_le'
- \+ *theorem* infi_le
- \+ *theorem* infi_le_infi2
- \+ *theorem* infi_le_infi
- \+ *theorem* infi_le_infi_const
- \+ *theorem* infi_le_infi_of_subset
- \+ *theorem* infi_le_of_le
- \+ *lemma* infi_lt_iff
- \+ *lemma* infi_neg
- \+ *theorem* infi_or
- \+ *theorem* infi_pair
- \+ *lemma* infi_pos
- \+ *theorem* infi_prod
- \+ *lemma* infi_range
- \+ *theorem* infi_sigma
- \+ *theorem* infi_singleton
- \+ *lemma* infi_subtype'
- \+ *theorem* infi_subtype
- \+ *theorem* infi_sum
- \+ *lemma* infi_top
- \+ *theorem* infi_true
- \+ *theorem* infi_union
- \+ *theorem* infi_unit
- \+ *theorem* infi_univ
- \+ *lemma* is_glb.Inf_eq
- \+ *lemma* is_glb.infi_eq
- \+ *lemma* is_glb_Inf
- \+ *lemma* is_glb_infi
- \+ *lemma* is_lub.Sup_eq
- \+ *lemma* is_lub.supr_eq
- \+ *lemma* is_lub_Sup
- \+ *lemma* is_lub_supr
- \- *def* lattice.Inf
- \- *lemma* lattice.Inf_Prop_eq
- \- *lemma* lattice.Inf_apply
- \- *theorem* lattice.Inf_empty
- \- *lemma* lattice.Inf_eq_bot
- \- *theorem* lattice.Inf_eq_infi
- \- *theorem* lattice.Inf_eq_top
- \- *theorem* lattice.Inf_image
- \- *theorem* lattice.Inf_insert
- \- *theorem* lattice.Inf_le
- \- *theorem* lattice.Inf_le_Inf
- \- *theorem* lattice.Inf_le_Sup
- \- *theorem* lattice.Inf_le_of_le
- \- *lemma* lattice.Inf_lt_iff
- \- *theorem* lattice.Inf_pair
- \- *lemma* lattice.Inf_range
- \- *theorem* lattice.Inf_singleton
- \- *theorem* lattice.Inf_union
- \- *theorem* lattice.Inf_univ
- \- *def* lattice.Sup
- \- *lemma* lattice.Sup_Prop_eq
- \- *lemma* lattice.Sup_apply
- \- *theorem* lattice.Sup_empty
- \- *theorem* lattice.Sup_eq_bot
- \- *theorem* lattice.Sup_eq_supr
- \- *lemma* lattice.Sup_eq_top
- \- *theorem* lattice.Sup_image
- \- *theorem* lattice.Sup_insert
- \- *theorem* lattice.Sup_inter_le
- \- *theorem* lattice.Sup_le
- \- *theorem* lattice.Sup_le_Sup
- \- *theorem* lattice.Sup_le_iff
- \- *theorem* lattice.Sup_pair
- \- *lemma* lattice.Sup_range
- \- *theorem* lattice.Sup_singleton
- \- *theorem* lattice.Sup_union
- \- *theorem* lattice.Sup_univ
- \- *lemma* lattice.binfi_inf
- \- *lemma* lattice.has_Inf_to_nonempty
- \- *lemma* lattice.has_Sup_to_nonempty
- \- *lemma* lattice.inf_infi
- \- *def* lattice.infi
- \- *lemma* lattice.infi_Prop_eq
- \- *theorem* lattice.infi_and
- \- *lemma* lattice.infi_apply
- \- *lemma* lattice.infi_bool_eq
- \- *theorem* lattice.infi_comm
- \- *theorem* lattice.infi_congr_Prop
- \- *theorem* lattice.infi_const
- \- *theorem* lattice.infi_empty
- \- *theorem* lattice.infi_emptyset
- \- *lemma* lattice.infi_eq_bot
- \- *lemma* lattice.infi_eq_dif
- \- *lemma* lattice.infi_eq_if
- \- *lemma* lattice.infi_eq_top
- \- *theorem* lattice.infi_exists
- \- *theorem* lattice.infi_false
- \- *lemma* lattice.infi_image
- \- *lemma* lattice.infi_inf
- \- *theorem* lattice.infi_inf_eq
- \- *theorem* lattice.infi_infi_eq_left
- \- *theorem* lattice.infi_infi_eq_right
- \- *theorem* lattice.infi_insert
- \- *theorem* lattice.infi_le'
- \- *theorem* lattice.infi_le
- \- *theorem* lattice.infi_le_infi2
- \- *theorem* lattice.infi_le_infi
- \- *theorem* lattice.infi_le_infi_const
- \- *theorem* lattice.infi_le_infi_of_subset
- \- *theorem* lattice.infi_le_of_le
- \- *lemma* lattice.infi_lt_iff
- \- *lemma* lattice.infi_neg
- \- *theorem* lattice.infi_or
- \- *theorem* lattice.infi_pair
- \- *lemma* lattice.infi_pos
- \- *theorem* lattice.infi_prod
- \- *lemma* lattice.infi_range
- \- *theorem* lattice.infi_sigma
- \- *theorem* lattice.infi_singleton
- \- *lemma* lattice.infi_subtype'
- \- *theorem* lattice.infi_subtype
- \- *theorem* lattice.infi_sum
- \- *lemma* lattice.infi_top
- \- *theorem* lattice.infi_true
- \- *theorem* lattice.infi_union
- \- *theorem* lattice.infi_unit
- \- *theorem* lattice.infi_univ
- \- *lemma* lattice.is_glb_Inf
- \- *lemma* lattice.is_glb_infi
- \- *lemma* lattice.is_lub_Sup
- \- *lemma* lattice.is_lub_supr
- \- *theorem* lattice.le_Inf
- \- *theorem* lattice.le_Inf_iff
- \- *theorem* lattice.le_Inf_inter
- \- *theorem* lattice.le_Sup
- \- *theorem* lattice.le_Sup_of_le
- \- *theorem* lattice.le_infi
- \- *theorem* lattice.le_infi_iff
- \- *theorem* lattice.le_supr'
- \- *theorem* lattice.le_supr
- \- *lemma* lattice.le_supr_iff
- \- *theorem* lattice.le_supr_of_le
- \- *lemma* lattice.lt_Sup_iff
- \- *lemma* lattice.lt_supr_iff
- \- *theorem* lattice.monotone_Inf_of_monotone
- \- *theorem* lattice.monotone_Sup_of_monotone
- \- *def* lattice.ord_continuous
- \- *lemma* lattice.ord_continuous_mono
- \- *lemma* lattice.ord_continuous_sup
- \- *def* lattice.supr
- \- *lemma* lattice.supr_Prop_eq
- \- *theorem* lattice.supr_and
- \- *lemma* lattice.supr_apply
- \- *lemma* lattice.supr_bool_eq
- \- *lemma* lattice.supr_bot
- \- *theorem* lattice.supr_comm
- \- *theorem* lattice.supr_congr_Prop
- \- *theorem* lattice.supr_const
- \- *theorem* lattice.supr_empty
- \- *theorem* lattice.supr_emptyset
- \- *lemma* lattice.supr_eq_bot
- \- *lemma* lattice.supr_eq_dif
- \- *lemma* lattice.supr_eq_if
- \- *lemma* lattice.supr_eq_top
- \- *theorem* lattice.supr_exists
- \- *theorem* lattice.supr_false
- \- *lemma* lattice.supr_image
- \- *theorem* lattice.supr_insert
- \- *theorem* lattice.supr_le
- \- *theorem* lattice.supr_le_iff
- \- *theorem* lattice.supr_le_supr2
- \- *theorem* lattice.supr_le_supr
- \- *theorem* lattice.supr_le_supr_const
- \- *theorem* lattice.supr_le_supr_of_subset
- \- *lemma* lattice.supr_neg
- \- *theorem* lattice.supr_or
- \- *theorem* lattice.supr_pair
- \- *lemma* lattice.supr_pos
- \- *theorem* lattice.supr_prod
- \- *lemma* lattice.supr_range
- \- *theorem* lattice.supr_sigma
- \- *theorem* lattice.supr_singleton
- \- *lemma* lattice.supr_subtype'
- \- *theorem* lattice.supr_subtype
- \- *theorem* lattice.supr_sum
- \- *theorem* lattice.supr_sup_eq
- \- *theorem* lattice.supr_supr_eq_left
- \- *theorem* lattice.supr_supr_eq_right
- \- *theorem* lattice.supr_true
- \- *theorem* lattice.supr_union
- \- *theorem* lattice.supr_unit
- \- *theorem* lattice.supr_univ
- \+ *theorem* le_Inf
- \+ *theorem* le_Inf_iff
- \+ *theorem* le_Inf_inter
- \+ *theorem* le_Sup
- \+ *theorem* le_Sup_of_le
- \+ *theorem* le_infi
- \+ *theorem* le_infi_iff
- \+ *theorem* le_supr'
- \+ *theorem* le_supr
- \+ *lemma* le_supr_iff
- \+ *theorem* le_supr_of_le
- \+ *lemma* lt_Sup_iff
- \+ *lemma* lt_supr_iff
- \+ *theorem* monotone_Inf_of_monotone
- \+ *theorem* monotone_Sup_of_monotone
- \+ *def* ord_continuous
- \+ *lemma* ord_continuous_mono
- \+ *lemma* ord_continuous_sup
- \+ *def* supr
- \+ *lemma* supr_Prop_eq
- \+ *theorem* supr_and
- \+ *lemma* supr_apply
- \+ *lemma* supr_bool_eq
- \+ *lemma* supr_bot
- \+ *theorem* supr_comm
- \+ *theorem* supr_congr_Prop
- \+ *theorem* supr_const
- \+ *theorem* supr_empty
- \+ *theorem* supr_emptyset
- \+ *lemma* supr_eq_bot
- \+ *lemma* supr_eq_dif
- \+ *lemma* supr_eq_if
- \+ *lemma* supr_eq_top
- \+ *theorem* supr_exists
- \+ *theorem* supr_false
- \+ *lemma* supr_image
- \+ *theorem* supr_insert
- \+ *theorem* supr_le
- \+ *theorem* supr_le_iff
- \+ *theorem* supr_le_supr2
- \+ *theorem* supr_le_supr
- \+ *theorem* supr_le_supr_const
- \+ *theorem* supr_le_supr_of_subset
- \+ *lemma* supr_neg
- \+ *theorem* supr_or
- \+ *theorem* supr_pair
- \+ *lemma* supr_pos
- \+ *theorem* supr_prod
- \+ *lemma* supr_range
- \+ *theorem* supr_sigma
- \+ *theorem* supr_singleton
- \+ *lemma* supr_subtype'
- \+ *theorem* supr_subtype
- \+ *theorem* supr_sum
- \+ *theorem* supr_sup_eq
- \+ *theorem* supr_supr_eq_left
- \+ *theorem* supr_supr_eq_right
- \+ *theorem* supr_true
- \+ *theorem* supr_union
- \+ *theorem* supr_unit
- \+ *theorem* supr_univ

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* Inf_nat_def
- \+ *lemma* Sup_nat_def
- \+ *lemma* cInf_Ici
- \+ *theorem* cInf_insert
- \+ *theorem* cInf_intro
- \+ *theorem* cInf_le
- \+ *theorem* cInf_le_cInf
- \+ *theorem* cInf_le_cSup
- \+ *theorem* cInf_le_of_le
- \+ *lemma* cInf_lt_of_lt
- \+ *theorem* cInf_singleton
- \+ *theorem* cInf_union
- \+ *lemma* cInf_upper_bounds_eq_cSup
- \+ *lemma* cSup_Iic
- \+ *lemma* cSup_empty
- \+ *theorem* cSup_insert
- \+ *theorem* cSup_inter_le
- \+ *theorem* cSup_intro'
- \+ *theorem* cSup_intro
- \+ *theorem* cSup_le
- \+ *theorem* cSup_le_cSup
- \+ *theorem* cSup_le_iff
- \+ *lemma* cSup_lower_bounds_eq_cInf
- \+ *theorem* cSup_singleton
- \+ *theorem* cSup_union
- \+ *theorem* cinfi_const
- \+ *lemma* cinfi_le
- \+ *lemma* cinfi_le_cinfi
- \+ *theorem* csupr_const
- \+ *lemma* csupr_le
- \+ *lemma* csupr_le_csupr
- \+ *lemma* exists_lt_of_cInf_lt
- \+ *lemma* exists_lt_of_cinfi_lt
- \+ *lemma* exists_lt_of_lt_cSup
- \+ *lemma* exists_lt_of_lt_csupr
- \+ *lemma* is_glb.cInf_eq
- \+ *lemma* is_glb_cInf
- \+ *lemma* is_greatest.cSup_eq
- \+ *lemma* is_least.cInf_eq
- \+ *lemma* is_lub.cSup_eq
- \+ *lemma* is_lub_cSup
- \- *lemma* lattice.Inf_nat_def
- \- *lemma* lattice.Sup_nat_def
- \- *lemma* lattice.cInf_Ici
- \- *theorem* lattice.cInf_insert
- \- *theorem* lattice.cInf_intro
- \- *theorem* lattice.cInf_le
- \- *theorem* lattice.cInf_le_cInf
- \- *theorem* lattice.cInf_le_cSup
- \- *theorem* lattice.cInf_le_of_le
- \- *lemma* lattice.cInf_lt_of_lt
- \- *theorem* lattice.cInf_singleton
- \- *theorem* lattice.cInf_union
- \- *lemma* lattice.cInf_upper_bounds_eq_cSup
- \- *lemma* lattice.cSup_Iic
- \- *lemma* lattice.cSup_empty
- \- *theorem* lattice.cSup_insert
- \- *theorem* lattice.cSup_inter_le
- \- *theorem* lattice.cSup_intro'
- \- *theorem* lattice.cSup_intro
- \- *theorem* lattice.cSup_le
- \- *theorem* lattice.cSup_le_cSup
- \- *theorem* lattice.cSup_le_iff
- \- *lemma* lattice.cSup_lower_bounds_eq_cInf
- \- *theorem* lattice.cSup_singleton
- \- *theorem* lattice.cSup_union
- \- *theorem* lattice.cinfi_const
- \- *lemma* lattice.cinfi_le
- \- *lemma* lattice.cinfi_le_cinfi
- \- *theorem* lattice.csupr_const
- \- *lemma* lattice.csupr_le
- \- *lemma* lattice.csupr_le_csupr
- \- *lemma* lattice.exists_lt_of_cInf_lt
- \- *lemma* lattice.exists_lt_of_cinfi_lt
- \- *lemma* lattice.exists_lt_of_lt_cSup
- \- *lemma* lattice.exists_lt_of_lt_csupr
- \- *lemma* lattice.is_glb_cInf
- \- *lemma* lattice.is_lub_cSup
- \- *theorem* lattice.le_cInf
- \- *theorem* lattice.le_cInf_iff
- \- *theorem* lattice.le_cInf_inter
- \- *theorem* lattice.le_cSup
- \- *theorem* lattice.le_cSup_of_le
- \- *lemma* lattice.le_cinfi
- \- *lemma* lattice.le_csupr
- \- *lemma* lattice.lt_cSup_of_lt
- \+ *theorem* le_cInf
- \+ *theorem* le_cInf_iff
- \+ *theorem* le_cInf_inter
- \+ *theorem* le_cSup
- \+ *theorem* le_cSup_of_le
- \+ *lemma* le_cinfi
- \+ *lemma* le_csupr
- \+ *lemma* lt_cSup_of_lt

Modified src/order/copy.lean
- \+ *def* bounded_lattice.copy
- \+ *def* complete_distrib_lattice.copy
- \+ *def* complete_lattice.copy
- \+ *def* conditionally_complete_lattice.copy
- \+ *def* distrib_lattice.copy
- \- *def* lattice.bounded_lattice.copy
- \- *def* lattice.complete_distrib_lattice.copy
- \- *def* lattice.complete_lattice.copy
- \- *def* lattice.conditionally_complete_lattice.copy
- \- *def* lattice.distrib_lattice.copy

Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/extr.lean


Modified src/order/filter/lift.lean


Modified src/order/filter/pointwise.lean


Modified src/order/fixed_points.lean
- \+ *theorem* fixed_points.Sup_le_f_of_fixed_points
- \+ *theorem* fixed_points.f_le_Inf_of_fixed_points
- \+ *theorem* fixed_points.f_le_inf_of_fixed_points
- \+ *def* fixed_points.next
- \+ *lemma* fixed_points.next_eq
- \+ *def* fixed_points.next_fixed
- \+ *theorem* fixed_points.next_le
- \+ *def* fixed_points.prev
- \+ *lemma* fixed_points.prev_eq
- \+ *def* fixed_points.prev_fixed
- \+ *theorem* fixed_points.prev_le
- \+ *theorem* fixed_points.sup_le_f_of_fixed_points
- \+ *def* fixed_points
- \+ *def* gfp
- \+ *theorem* gfp_comp
- \+ *theorem* gfp_eq
- \+ *theorem* gfp_gfp
- \+ *theorem* gfp_induct
- \+ *theorem* gfp_le
- \- *theorem* lattice.fixed_points.Sup_le_f_of_fixed_points
- \- *theorem* lattice.fixed_points.f_le_Inf_of_fixed_points
- \- *theorem* lattice.fixed_points.f_le_inf_of_fixed_points
- \- *def* lattice.fixed_points.next
- \- *lemma* lattice.fixed_points.next_eq
- \- *def* lattice.fixed_points.next_fixed
- \- *theorem* lattice.fixed_points.next_le
- \- *def* lattice.fixed_points.prev
- \- *lemma* lattice.fixed_points.prev_eq
- \- *def* lattice.fixed_points.prev_fixed
- \- *theorem* lattice.fixed_points.prev_le
- \- *theorem* lattice.fixed_points.sup_le_f_of_fixed_points
- \- *def* lattice.fixed_points
- \- *def* lattice.gfp
- \- *theorem* lattice.gfp_comp
- \- *theorem* lattice.gfp_eq
- \- *theorem* lattice.gfp_gfp
- \- *theorem* lattice.gfp_induct
- \- *theorem* lattice.gfp_le
- \- *theorem* lattice.le_gfp
- \- *theorem* lattice.le_lfp
- \- *def* lattice.lfp
- \- *theorem* lattice.lfp_comp
- \- *theorem* lattice.lfp_eq
- \- *theorem* lattice.lfp_induct
- \- *theorem* lattice.lfp_le
- \- *theorem* lattice.lfp_lfp
- \- *theorem* lattice.monotone_gfp
- \- *theorem* lattice.monotone_lfp
- \+ *theorem* le_gfp
- \+ *theorem* le_lfp
- \+ *def* lfp
- \+ *theorem* lfp_comp
- \+ *theorem* lfp_eq
- \+ *theorem* lfp_induct
- \+ *theorem* lfp_le
- \+ *theorem* lfp_lfp
- \+ *theorem* monotone_gfp
- \+ *theorem* monotone_lfp

Modified src/order/galois_connection.lean


Modified src/order/lattice.lean
- \+ *lemma* directed_of_inf
- \+ *lemma* directed_of_mono
- \+ *lemma* directed_of_sup
- \+ *lemma* eq_of_sup_eq_inf_eq
- \+ *lemma* forall_le_or_exists_lt_inf
- \+ *lemma* forall_le_or_exists_lt_sup
- \+ *theorem* inf_assoc
- \+ *theorem* inf_comm
- \+ *theorem* inf_eq_min
- \+ *theorem* inf_idem
- \+ *theorem* inf_le_inf
- \+ *lemma* inf_le_inf_left
- \+ *lemma* inf_le_inf_right
- \+ *theorem* inf_le_left'
- \+ *theorem* inf_le_left
- \+ *theorem* inf_le_left_of_le
- \+ *theorem* inf_le_right'
- \+ *theorem* inf_le_right
- \+ *theorem* inf_le_right_of_le
- \+ *lemma* inf_left_comm
- \+ *theorem* inf_of_le_left
- \+ *theorem* inf_of_le_right
- \+ *theorem* inf_sup_left
- \+ *theorem* inf_sup_right
- \+ *theorem* inf_sup_self
- \- *lemma* lattice.directed_of_antimono
- \- *lemma* lattice.directed_of_inf
- \- *lemma* lattice.directed_of_mono
- \- *lemma* lattice.directed_of_sup
- \- *lemma* lattice.eq_of_sup_eq_inf_eq
- \+/\- *theorem* lattice.ext
- \- *lemma* lattice.forall_le_or_exists_lt_inf
- \- *lemma* lattice.forall_le_or_exists_lt_sup
- \- *theorem* lattice.inf_assoc
- \- *theorem* lattice.inf_comm
- \- *theorem* lattice.inf_eq_min
- \- *theorem* lattice.inf_idem
- \- *theorem* lattice.inf_le_inf
- \- *lemma* lattice.inf_le_inf_left
- \- *lemma* lattice.inf_le_inf_right
- \- *theorem* lattice.inf_le_left'
- \- *theorem* lattice.inf_le_left
- \- *theorem* lattice.inf_le_left_of_le
- \- *theorem* lattice.inf_le_right'
- \- *theorem* lattice.inf_le_right
- \- *theorem* lattice.inf_le_right_of_le
- \- *lemma* lattice.inf_left_comm
- \- *theorem* lattice.inf_of_le_left
- \- *theorem* lattice.inf_of_le_right
- \- *theorem* lattice.inf_sup_left
- \- *theorem* lattice.inf_sup_right
- \- *theorem* lattice.inf_sup_self
- \- *theorem* lattice.le_inf
- \- *theorem* lattice.le_inf_iff
- \- *theorem* lattice.le_inf_sup
- \- *theorem* lattice.le_of_inf_eq
- \- *theorem* lattice.le_of_sup_eq
- \- *theorem* lattice.le_sup_inf
- \- *theorem* lattice.le_sup_left'
- \- *theorem* lattice.le_sup_left
- \- *theorem* lattice.le_sup_left_of_le
- \- *theorem* lattice.le_sup_right'
- \- *theorem* lattice.le_sup_right
- \- *theorem* lattice.le_sup_right_of_le
- \- *lemma* lattice.lt_inf_iff
- \- *theorem* lattice.semilattice_inf.ext
- \- *theorem* lattice.semilattice_inf.ext_inf
- \- *theorem* lattice.semilattice_sup.ext
- \- *theorem* lattice.semilattice_sup.ext_sup
- \- *theorem* lattice.sup_assoc
- \- *theorem* lattice.sup_comm
- \- *theorem* lattice.sup_eq_max
- \- *theorem* lattice.sup_idem
- \- *theorem* lattice.sup_inf_le
- \- *theorem* lattice.sup_inf_left
- \- *theorem* lattice.sup_inf_right
- \- *theorem* lattice.sup_inf_self
- \- *theorem* lattice.sup_le
- \- *theorem* lattice.sup_le_iff
- \- *theorem* lattice.sup_le_sup
- \- *theorem* lattice.sup_le_sup_left
- \- *theorem* lattice.sup_le_sup_right
- \- *lemma* lattice.sup_left_comm
- \- *lemma* lattice.sup_lt_iff
- \- *theorem* lattice.sup_of_le_left
- \- *theorem* lattice.sup_of_le_right
- \+/\- *theorem* le_antisymm'
- \+ *theorem* le_inf
- \+ *theorem* le_inf_iff
- \+ *theorem* le_inf_sup
- \+ *theorem* le_of_inf_eq
- \+ *theorem* le_of_sup_eq
- \+ *theorem* le_sup_inf
- \+ *theorem* le_sup_left'
- \+ *theorem* le_sup_left
- \+ *theorem* le_sup_left_of_le
- \+ *theorem* le_sup_right'
- \+ *theorem* le_sup_right
- \+ *theorem* le_sup_right_of_le
- \+ *lemma* lt_inf_iff
- \+ *theorem* semilattice_inf.ext
- \+ *theorem* semilattice_inf.ext_inf
- \+ *theorem* semilattice_sup.ext
- \+ *theorem* semilattice_sup.ext_sup
- \+ *theorem* sup_assoc
- \+ *theorem* sup_comm
- \+ *theorem* sup_eq_max
- \+ *theorem* sup_idem
- \+ *theorem* sup_inf_le
- \+ *theorem* sup_inf_left
- \+ *theorem* sup_inf_right
- \+ *theorem* sup_inf_self
- \+ *theorem* sup_le
- \+ *theorem* sup_le_iff
- \+ *theorem* sup_le_sup
- \+ *theorem* sup_le_sup_left
- \+ *theorem* sup_le_sup_right
- \+ *lemma* sup_left_comm
- \+ *lemma* sup_lt_iff
- \+ *theorem* sup_of_le_left
- \+ *theorem* sup_of_le_right

Modified src/order/liminf_limsup.lean


Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/ideals.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/power_series.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/schroeder_bernstein.lean


Modified src/tactic/converter/binders.lean
- \- *theorem* Inf_image
- \- *theorem* Sup_image

Modified src/tactic/interval_cases.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean


Modified src/topology/bounded_continuous_function.lean


Modified src/topology/category/Top/limits.lean


Modified src/topology/constructions.lean


Modified src/topology/continuous_on.lean


Modified src/topology/dense_embedding.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/local_extr.lean


Modified src/topology/maps.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/opens.lean


Modified src/topology/order.lean


Modified src/topology/separation.lean


Modified src/topology/sequences.lean


Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/absolute_value.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/compare_reals.lean


Modified src/topology/uniform_space/complete_separated.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/pi.lean


Modified src/topology/uniform_space/separation.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-03-19 10:59:44](https://github.com/leanprover-community/mathlib/commit/a20f378)
chore(category_theory/images): fix some minor problems ([#2182](https://github.com/leanprover-community/mathlib/pull/2182))
* chore(category_theory/images): fix some minor problems
* minor
* oops, misplaced comment
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* category_theory.limits.as_factor_thru_image
- \- *lemma* category_theory.limits.image.as_c
- \- *def* category_theory.limits.image.c
- \- *lemma* category_theory.limits.image.c_ι



## [2020-03-19 08:46:53](https://github.com/leanprover-community/mathlib/commit/4bc32ae)
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
#### Estimated changes
Modified src/category_theory/epi_mono.lean


Modified src/category_theory/limits/shapes/constructions/pullbacks.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.epi_of_is_colimit_parallel_pair
- \+ *lemma* category_theory.limits.mono_of_is_limit_parallel_pair

Modified src/category_theory/limits/shapes/images.lean


Added src/category_theory/limits/shapes/regular_mono.lean




## [2020-03-19 06:18:29](https://github.com/leanprover-community/mathlib/commit/445e332)
chore(category_theory/isomorphism): use @[simps] ([#2181](https://github.com/leanprover-community/mathlib/pull/2181))
#### Estimated changes
Modified src/category_theory/isomorphism.lean
- \+/\- *def* category_theory.iso.refl
- \- *lemma* category_theory.iso.refl_hom
- \- *lemma* category_theory.iso.refl_inv
- \+/\- *def* category_theory.iso.trans
- \- *lemma* category_theory.iso.trans_hom
- \- *lemma* category_theory.iso.trans_inv



## [2020-03-19 03:47:29](https://github.com/leanprover-community/mathlib/commit/e2b0e38)
chore(category_theory/binary_products): tweak spacing in notation ([#2184](https://github.com/leanprover-community/mathlib/pull/2184))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean




## [2020-03-19 01:12:44](https://github.com/leanprover-community/mathlib/commit/034685b)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-18 23:51:31](https://github.com/leanprover-community/mathlib/commit/00d9f1d)
feat(topology/algebra/infinite_sum): dot notation, cauchy sequences ([#2171](https://github.com/leanprover-community/mathlib/pull/2171))
* more material on infinite sums
* minor fixes
* cleanup
* yury's comments
#### Estimated changes
Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* cauchy_seq_finset_iff_vanishing_norm
- \+ *lemma* cauchy_seq_finset_of_norm_bounded
- \+ *lemma* cauchy_seq_finset_of_summable_norm
- \+ *lemma* edist_eq_coe_nnnorm_sub
- \+ *lemma* has_sum_of_subseq_of_summable
- \+/\- *lemma* summable_iff_vanishing_norm
- \+ *lemma* summable_of_nnnorm_bounded
- \+/\- *lemma* summable_of_norm_bounded
- \+ *lemma* summable_of_summable_nnnorm

Modified src/analysis/specific_limits.lean
- \+ *lemma* cauchy_seq_finset_of_geometric_bound
- \+ *lemma* dist_partial_sum_le_of_le_geometric
- \+ *lemma* nnreal.tendsto_const_div_at_top_nhds_0_nat
- \+ *lemma* nnreal.tendsto_inverse_at_top_nhds_0_nat
- \+ *lemma* norm_sub_le_of_geometric_bound_of_has_sum

Modified src/data/option/basic.lean
- \+ *def* option.cases_on'

Modified src/data/real/cardinality.lean


Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/probability_mass_function.lean
- \+/\- *lemma* pmf.summable_coe

Modified src/order/liminf_limsup.lean


Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* cauchy_seq_finset_iff_vanishing
- \+ *lemma* equiv.has_sum_iff
- \+ *lemma* equiv.summable_iff
- \+ *lemma* has_sum.add
- \+ *lemma* has_sum.has_sum_ne_zero
- \+ *lemma* has_sum.has_sum_of_sum_eq
- \+ *lemma* has_sum.mul_left
- \+ *lemma* has_sum.mul_right
- \+ *lemma* has_sum.neg
- \+ *lemma* has_sum.sigma
- \+ *lemma* has_sum.sigma_of_has_sum
- \+ *lemma* has_sum.sub
- \+ *lemma* has_sum.summable
- \+ *lemma* has_sum.tendsto_sum_nat
- \- *lemma* has_sum_add
- \- *lemma* has_sum_iff_of_summable
- \- *lemma* has_sum_mul_left
- \+ *lemma* has_sum_mul_left_iff
- \- *lemma* has_sum_mul_right
- \+ *lemma* has_sum_mul_right_iff
- \- *lemma* has_sum_neg
- \- *lemma* has_sum_of_has_sum
- \- *lemma* has_sum_of_has_sum_ne_zero
- \- *lemma* has_sum_sigma
- \- *lemma* has_sum_sub
- \- *lemma* has_sum_tsum
- \+/\- *lemma* has_sum_unique
- \- *def* option.cases_on'
- \+ *lemma* summable.add
- \+ *lemma* summable.has_sum
- \+ *lemma* summable.has_sum_iff
- \+ *lemma* summable.mul_left
- \+ *lemma* summable.mul_right
- \+ *lemma* summable.neg
- \+ *lemma* summable.sigma'
- \+ *lemma* summable.sigma
- \+ *lemma* summable.sigma_factor
- \+ *lemma* summable.sub
- \+ *lemma* summable.summable_comp_of_injective
- \+ *lemma* summable.summable_of_eq_zero_or_self
- \- *lemma* summable_add
- \- *lemma* summable_comp_of_summable_of_injective
- \- *lemma* summable_iff_cauchy
- \+ *lemma* summable_iff_cauchy_seq_finset
- \- *lemma* summable_mul_left
- \+ *lemma* summable_mul_left_iff
- \- *lemma* summable_mul_right
- \+ *lemma* summable_mul_right_iff
- \- *lemma* summable_neg
- \- *lemma* summable_of_summable_of_sub
- \- *lemma* summable_sigma
- \- *lemma* summable_spec
- \- *lemma* summable_sub
- \+/\- *lemma* summable_zero
- \- *lemma* tendsto_sum_nat_of_has_sum
- \+/\- *lemma* tsum_eq_has_sum
- \+ *lemma* tsum_eq_zero_of_not_summable
- \+ *lemma* tsum_le_tsum_of_inj
- \+ *lemma* tsum_nonneg
- \+ *lemma* tsum_nonpos
- \+ *lemma* tsum_sigma'

Modified src/topology/instances/ennreal.lean
- \+ *lemma* nnreal.tsum_comp_le_tsum_of_inj
- \+ *lemma* tsum_comp_le_tsum_of_inj

Modified src/topology/instances/nnreal.lean


Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* tendsto_nhds_of_cauchy_seq_of_subseq



## [2020-03-18 21:14:22](https://github.com/leanprover-community/mathlib/commit/e719f8e)
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
#### Estimated changes
Modified leanpkg.toml


Modified scripts/deploy_docs.sh


Modified src/algebra/direct_limit.lean


Modified src/algebra/direct_sum.lean
- \+/\- *theorem* direct_sum.to_group.unique

Modified src/algebra/euclidean_domain.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/ring.lean
- \+ *lemma* is_ring_hom.comp
- \+ *lemma* is_semiring_hom.comp

Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/category/monad/writer.lean


Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/monad/limits.lean
- \+/\- *def* category_theory.has_limits_of_reflective

Modified src/data/fintype.lean


Modified src/data/mv_polynomial.lean


Modified src/data/polynomial.lean


Modified src/deprecated/group.lean
- \+ *lemma* is_group_hom.comp
- \+ *lemma* is_monoid_hom.comp
- \+ *lemma* is_mul_hom.comp

Modified src/field_theory/splitting_field.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/presented_group.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid.lean
- \+ *lemma* additive.is_add_submonoid
- \+ *lemma* multiplicative.is_submonoid

Modified src/ring_theory/algebra.lean


Modified src/ring_theory/localization.lean


Modified src/set_theory/ordinal.lean


Modified src/tactic/alias.lean


Modified src/tactic/core.lean


Modified src/tactic/lint.lean


Modified src/tactic/reassoc_axiom.lean


Modified src/tactic/squeeze.lean


Modified src/tactic/transport.lean


Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* add_comm_group.is_Z_bilin.comp_hom

Modified src/topology/algebra/uniform_ring.lean




## [2020-03-18 18:36:06](https://github.com/leanprover-community/mathlib/commit/69f7bf8)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-18 17:04:44](https://github.com/leanprover-community/mathlib/commit/5f62d3b)
feat(topology/bounded_continuous_functions): more general uniform convergence ([#2165](https://github.com/leanprover-community/mathlib/pull/2165))
* feat(topology/buonded_continuous_functions): more general uniform convergence
* yury's comments
#### Estimated changes
Modified src/topology/bounded_continuous_function.lean
- \+/\- *def* bounded_continuous_function
- \+ *lemma* continuous_at_of_locally_uniform_limit_of_continuous_at
- \+/\- *lemma* continuous_of_locally_uniform_limit_of_continuous
- \+/\- *lemma* continuous_of_uniform_limit_of_continuous
- \+ *lemma* continuous_on_of_locally_uniform_limit_of_continuous_on
- \+ *lemma* continuous_on_of_uniform_limit_of_continuous_on
- \+ *lemma* continuous_within_at_of_locally_uniform_limit_of_continuous_within_at

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.continuous_at
- \+ *lemma* continuous_on.continuous_within_at
- \+ *lemma* continuous_on_empty
- \+/\- *theorem* continuous_on_iff_is_closed

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.ball_zero
- \+ *theorem* metric.continuous_at_iff'
- \+ *theorem* metric.continuous_on_iff'
- \+ *theorem* metric.continuous_on_iff
- \+ *theorem* metric.continuous_within_at_iff'
- \+ *theorem* metric.continuous_within_at_iff

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* emetric.ball_zero



## [2020-03-18 14:55:37](https://github.com/leanprover-community/mathlib/commit/739e831)
feat(analysis/complex/exponential): real powers of nnreals ([#2164](https://github.com/leanprover-community/mathlib/pull/2164))
* feat(analysis/complex/exponential): real powers of nnreals
* cleanup
* mean inequalities in nnreal
* mean inequalities
* use < instead of >
* reviewer's comments
#### Estimated changes
Modified src/analysis/complex/exponential.lean
- \+ *lemma* complex.cpow_eq_pow
- \+ *lemma* complex.cpow_eq_zero_iff
- \+ *lemma* filter.tendsto.nnrpow
- \+ *lemma* nnreal.coe_rpow
- \+ *lemma* nnreal.continuous_at_rpow
- \+ *lemma* nnreal.mul_rpow
- \+ *lemma* nnreal.one_le_rpow
- \+ *lemma* nnreal.one_lt_rpow
- \+ *lemma* nnreal.one_rpow
- \+ *lemma* nnreal.pow_nat_rpow_nat_inv
- \+ *lemma* nnreal.rpow_add
- \+ *lemma* nnreal.rpow_eq_pow
- \+ *lemma* nnreal.rpow_eq_zero_iff
- \+ *lemma* nnreal.rpow_le_one
- \+ *lemma* nnreal.rpow_le_rpow
- \+ *lemma* nnreal.rpow_le_rpow_of_exponent_ge
- \+ *lemma* nnreal.rpow_le_rpow_of_exponent_le
- \+ *lemma* nnreal.rpow_lt_one
- \+ *lemma* nnreal.rpow_lt_rpow
- \+ *lemma* nnreal.rpow_lt_rpow_of_exponent_gt
- \+ *lemma* nnreal.rpow_lt_rpow_of_exponent_lt
- \+ *lemma* nnreal.rpow_mul
- \+ *lemma* nnreal.rpow_nat_cast
- \+ *lemma* nnreal.rpow_nat_inv_pow_nat
- \+ *lemma* nnreal.rpow_neg
- \+ *lemma* nnreal.rpow_one
- \+ *lemma* nnreal.rpow_zero
- \+ *lemma* nnreal.zero_rpow
- \+ *lemma* real.continuous_at_rpow
- \+ *lemma* real.rpow_eq_pow
- \+ *lemma* real.rpow_eq_zero_iff_of_nonneg
- \+ *lemma* real.rpow_nat_inv_pow_nat

Modified src/analysis/mean_inequalities.lean




## [2020-03-18 03:19:02](https://github.com/leanprover-community/mathlib/commit/f07a1eb)
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
#### Estimated changes
Modified src/algebra/category/Group/adjunctions.lean
- \+/\- *def* AddCommGroup.adj

Modified src/algebra/category/Group/basic.lean
- \+ *def* AddCommGroup.as_hom
- \+ *lemma* AddCommGroup.as_hom_apply
- \+ *lemma* AddCommGroup.as_hom_injective
- \+ *lemma* AddCommGroup.injective_of_mono
- \+ *lemma* AddCommGroup.int_hom_ext

Added src/algebra/category/Group/images.lean
- \+ *def* AddCommGroup.factor_thru_image
- \+ *lemma* AddCommGroup.image.fac
- \+ *lemma* AddCommGroup.image.lift_fac
- \+ *def* AddCommGroup.image.ι
- \+ *def* AddCommGroup.image
- \+ *def* AddCommGroup.mono_factorisation

Modified src/algebra/group_power.lean
- \+ *lemma* gsmul_int_int
- \+ *lemma* gsmul_int_one

Modified src/category_theory/concrete_category/basic.lean
- \+ *lemma* category_theory.concrete_category.hom_ext
- \+ *lemma* category_theory.concrete_category.mono_of_injective

Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/limits/types.lean
- \+ *lemma* category_theory.limits.types.image.lift_fac
- \+ *def* category_theory.limits.types.image.ι
- \+ *def* category_theory.limits.types.image
- \+ *def* category_theory.limits.types.mono_factorisation

Modified src/group_theory/subgroup.lean
- \+ *def* monoid_hom.range_factorization
- \+ *def* monoid_hom.range_subtype_val



## [2020-03-18 00:03:33](https://github.com/leanprover-community/mathlib/commit/6af37d3)
fix(category_theory/limits): require explicit instances of has_zero_morphisms ([#2169](https://github.com/leanprover-community/mathlib/pull/2169))
* fix(category_theory/limits): require explicit instances of has_zero_morphisms
* Fix unused arguments
#### Estimated changes
Modified src/algebra/category/Module/basic.lean


Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/zero.lean




## [2020-03-17 14:49:48+01:00](https://github.com/leanprover-community/mathlib/commit/422f640)
fix(scripts/mk_nolint): fix error introduced by [#2090](https://github.com/leanprover-community/mathlib/pull/2090) ([#2170](https://github.com/leanprover-community/mathlib/pull/2170))
#### Estimated changes
Modified scripts/mk_nolint.lean




## [2020-03-17 03:38:32](https://github.com/leanprover-community/mathlib/commit/e94fef0)
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
#### Estimated changes
Modified scripts/mk_nolint.lean


Modified src/analysis/normed_space/basic.lean


Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/category_theory/limits/shapes/images.lean


Modified src/data/fin_enum.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/tactic/lint.lean


Modified src/topology/subset_properties.lean


Modified test/lint.lean




## [2020-03-17 01:31:51](https://github.com/leanprover-community/mathlib/commit/496939c)
feat(data/real/*nnreal): add division lemmas ([#2167](https://github.com/leanprover-community/mathlib/pull/2167))
* feat(data/real/*nnreal): add division lemmas
* fix build
* elim_cast
* another elim_cast
#### Estimated changes
Modified src/data/real/ennreal.lean
- \- *lemma* ennreal.coe_sub_infty
- \+ *lemma* ennreal.div_eq_top
- \+/\- *lemma* ennreal.div_le_iff_le_mul
- \+ *lemma* ennreal.div_one
- \+/\- *lemma* ennreal.le_div_iff_mul_le
- \+ *lemma* ennreal.lt_iff_exists_add_pos_lt
- \+ *lemma* ennreal.lt_sub_iff_add_lt
- \+ *lemma* ennreal.mul_div_assoc
- \+/\- *lemma* ennreal.none_eq_top
- \+/\- *lemma* ennreal.some_eq_coe

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.add_div'
- \+ *lemma* nnreal.coe_ne_zero
- \+ *lemma* nnreal.div_add'
- \+ *lemma* nnreal.div_add_div
- \+ *lemma* nnreal.div_div_eq_div_mul
- \+ *lemma* nnreal.div_div_eq_mul_div
- \+ *lemma* nnreal.div_eq_div_iff
- \+ *lemma* nnreal.div_eq_iff
- \+ *lemma* nnreal.div_eq_mul_one_div
- \+ *lemma* nnreal.div_lt_iff
- \+ *lemma* nnreal.div_lt_one_of_lt
- \+ *lemma* nnreal.div_mul_eq_mul_div
- \+ *theorem* nnreal.div_pow
- \+ *lemma* nnreal.eq_div_iff
- \+ *lemma* nnreal.inv_eq_one_div
- \+ *lemma* nnreal.lt_sub_iff_add_lt
- \+ *lemma* nnreal.mul_div_assoc'
- \+ *theorem* nnreal.mul_ne_zero'
- \+ *lemma* nnreal.one_div_div
- \+ *lemma* nnreal.one_div_eq_inv
- \+ *theorem* nnreal.pow_eq_zero
- \+ *theorem* nnreal.pow_ne_zero

Modified src/topology/instances/ennreal.lean




## [2020-03-16 23:16:44](https://github.com/leanprover-community/mathlib/commit/4754368)
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
#### Estimated changes
Modified src/category_theory/epi_mono.lean
- \+ *def* category_theory.retraction
- \+ *def* category_theory.section_
- \+ *lemma* category_theory.split_epi.id
- \+ *lemma* category_theory.split_mono.id

Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.cocone_of_split_epi
- \+ *lemma* category_theory.limits.cocone_of_split_epi_ι_app_one
- \+ *lemma* category_theory.limits.cocone_of_split_epi_ι_app_zero
- \+ *def* category_theory.limits.cone_of_split_mono
- \+ *lemma* category_theory.limits.cone_of_split_mono_π_app_one
- \+ *lemma* category_theory.limits.cone_of_split_mono_π_app_zero
- \+ *lemma* category_theory.limits.parallel_pair_obj_one
- \+ *lemma* category_theory.limits.parallel_pair_obj_zero
- \+ *def* category_theory.limits.split_epi_coequalizes
- \+ *def* category_theory.limits.split_mono_equalizes

Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/zero.lean
- \- *def* category_theory.limits.zero_of_zero_object



## [2020-03-16 21:22:20](https://github.com/leanprover-community/mathlib/commit/bc087d8)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-16 20:04:17](https://github.com/leanprover-community/mathlib/commit/7a5496f)
chore(order/liminf_limsup): lint and cleanup the file ([#2162](https://github.com/leanprover-community/mathlib/pull/2162))
* chore(order/liminf_limsup): lint and cleanup the file, add some statements
* use eventually_mono
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually.congr
- \+ *lemma* filter.eventually.congr_iff

Modified src/order/liminf_limsup.lean
- \+/\- *theorem* filter.Liminf_le_Limsup
- \+/\- *theorem* filter.Limsup_le_of_le
- \+ *lemma* filter.eventually_lt_of_limsup_lt
- \+ *lemma* filter.eventually_lt_of_lt_liminf
- \+/\- *theorem* filter.le_Liminf_of_le
- \+ *lemma* filter.liminf_congr
- \+ *lemma* filter.liminf_const
- \+ *lemma* filter.limsup_congr
- \+ *lemma* filter.limsup_const



## [2020-03-16 19:22:51](https://github.com/leanprover-community/mathlib/commit/007b575)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-16 17:51:32](https://github.com/leanprover-community/mathlib/commit/42b92aa)
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
#### Estimated changes
Modified docs/contribute/doc.md


Modified docs/extras.md


Modified docs/extras/simp.md


Modified src/logic/basic.lean


Modified src/tactic/abel.lean


Modified src/tactic/alias.lean
- \+ *theorem* alias1
- \+ *theorem* alias2
- \+ *theorem* tactic.alias.alias1
- \+ *theorem* tactic.alias.alias2

Modified src/tactic/apply_fun.lean


Modified src/tactic/cache.lean
- \+ *def* tactic.interactive.my_id

Modified src/tactic/clear.lean


Modified src/tactic/core.lean


Modified src/tactic/derive_inhabited.lean


Added src/tactic/doc_commands.lean
- \+ *inductive* doc_category
- \+ *def* string.hash
- \+ *structure* tactic_doc_entry

Modified src/tactic/elide.lean


Modified src/tactic/explode.lean


Modified src/tactic/ext.lean


Modified src/tactic/fin_cases.lean


Modified src/tactic/find.lean


Modified src/tactic/finish.lean


Modified src/tactic/hint.lean


Modified src/tactic/interactive.lean


Modified src/tactic/interval_cases.lean


Deleted src/tactic/library_note.lean
- \- *def* string.hash

Modified src/tactic/lift.lean


Modified src/tactic/linarith.lean


Modified src/tactic/lint.lean


Modified src/tactic/localized.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/norm_cast.lean


Modified src/tactic/norm_num.lean
- \+ *def* tactic.interactive.a
- \+ *def* tactic.interactive.normed_a

Modified src/tactic/omega/main.lean


Modified src/tactic/pi_instances.lean


Modified src/tactic/push_neg.lean


Modified src/tactic/rcases.lean


Modified src/tactic/reassoc_axiom.lean
- \+/\- *theorem* category_theory.reassoc_of

Modified src/tactic/rename.lean


Modified src/tactic/rename_var.lean


Modified src/tactic/replacer.lean


Modified src/tactic/restate_axiom.lean


Modified src/tactic/rewrite.lean


Modified src/tactic/ring.lean


Modified src/tactic/ring_exp.lean


Modified src/tactic/simp_rw.lean


Modified src/tactic/simpa.lean


Modified src/tactic/simps.lean


Modified src/tactic/solve_by_elim.lean


Modified src/tactic/squeeze.lean


Modified src/tactic/suggest.lean


Modified src/tactic/tauto.lean


Modified src/tactic/tfae.lean


Modified src/tactic/tidy.lean


Modified src/tactic/where.lean




## [2020-03-16 15:33:24](https://github.com/leanprover-community/mathlib/commit/04c7381)
doc(docs/install/windows): emphasize projects link ([#2150](https://github.com/leanprover-community/mathlib/pull/2150))
You can't use mathlib in the test project created in step 6. I've seen a couple of Windows users get tripped up here.
#### Estimated changes
Modified docs/install/windows.md




## [2020-03-16 14:46:06](https://github.com/leanprover-community/mathlib/commit/555528e)
feat(category_theory/image): comparison maps for precomposition ([#2153](https://github.com/leanprover-community/mathlib/pull/2153))
* feat(category_theory/image): comparison maps for precomposition
* remove duplicate argument
* unused argument
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean
- \+ *def* category_theory.limits.image.eq_to_hom
- \+ *def* category_theory.limits.image.eq_to_iso
- \+ *def* category_theory.limits.image.pre_comp
- \+ *lemma* category_theory.limits.image.pre_comp_comp



## [2020-03-16 09:18:06](https://github.com/leanprover-community/mathlib/commit/1e38cb1)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-16 08:00:01](https://github.com/leanprover-community/mathlib/commit/ff84bf4)
feat(category_theory/monad/limits): forgetful creates colimits ([#2138](https://github.com/leanprover-community/mathlib/pull/2138))
* forgetful creates colimits
* tidy up proofs
* add docs
* suggestions from review
#### Estimated changes
Modified src/category_theory/monad/limits.lean
- \+ *def* category_theory.monad.forget_creates_colimits.c
- \+ *def* category_theory.monad.forget_creates_colimits.cocone_point
- \+ *lemma* category_theory.monad.forget_creates_colimits.commuting
- \+ *def* category_theory.monad.forget_creates_colimits.lambda
- \+ *def* category_theory.monad.forget_creates_colimits.γ
- \+ *def* category_theory.monad.forget_creates_colimits_of_monad_preserves
- \+/\- *def* category_theory.monad.forget_creates_limits



## [2020-03-16 05:54:25](https://github.com/leanprover-community/mathlib/commit/4aed862)
feat(analysis/normed_space/operator_norm): completeness of the space of operators ([#2160](https://github.com/leanprover-community/mathlib/pull/2160))
* feat(analysis/normed_space/operator_norm): completeness of the space of operators
* add some comments
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean




## [2020-03-16 03:42:23](https://github.com/leanprover-community/mathlib/commit/d8e5d99)
feat(category_theory/limits): Convenience methods for building limit (co)forks ([#2155](https://github.com/leanprover-community/mathlib/pull/2155))
* feat(category_theory/limits): Convenience methods for building limit (co)forks
* Formatting
* Rework a proof about kernels
* feat(category_theory/limits): kernel forks
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.cofork.is_colimit.mk
- \+ *def* category_theory.limits.fork.is_limit.mk

Modified src/category_theory/limits/shapes/kernels.lean




## [2020-03-16 01:31:06](https://github.com/leanprover-community/mathlib/commit/c240fcb)
feat(category_theory/limits): pullbacks from binary products and equalizers ([#2143](https://github.com/leanprover-community/mathlib/pull/2143))
* feat(category_theory/limits): derive has_binary_products from has_limit (pair X Y)
* Rename *_of_diagram to diagram_iso_*
* feat(category_theory/limits): pullbacks from binary products and equalizers
* Fix build
* Fix indentation
* typos
* Fix proof
* Remove some simp lemmas that were duplicated during merge
#### Estimated changes
Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/shapes/constructions/equalizers.lean


Modified src/category_theory/limits/shapes/constructions/pullbacks.lean
- \+ *def* category_theory.limits.has_colimit_span_of_has_colimit_pair_of_has_colimit_parallel_pair
- \+ *def* category_theory.limits.has_limit_cospan_of_has_limit_pair_of_has_limit_parallel_pair
- \+ *def* category_theory.limits.has_pullbacks_of_has_binary_products_of_has_equalizers
- \+ *def* category_theory.limits.has_pushouts_of_has_binary_coproducts_of_has_coequalizers

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* category_theory.limits.pullback_cone.is_limit.mk
- \- *lemma* category_theory.limits.pullback_cone.mk_left
- \- *lemma* category_theory.limits.pullback_cone.mk_right
- \+ *lemma* category_theory.limits.pullback_cone.mk_π_app_left
- \+ *lemma* category_theory.limits.pullback_cone.mk_π_app_one
- \+ *lemma* category_theory.limits.pullback_cone.mk_π_app_right
- \+ *def* category_theory.limits.pushout_cocone.is_colimit.mk
- \+ *lemma* category_theory.limits.pushout_cocone.mk_ι_app_left
- \+ *lemma* category_theory.limits.pushout_cocone.mk_ι_app_right
- \+ *lemma* category_theory.limits.pushout_cocone.mk_ι_app_zero



## [2020-03-15 23:30:43](https://github.com/leanprover-community/mathlib/commit/fbe2ce0)
feat(category_theory/limits): kernel forks ([#2156](https://github.com/leanprover-community/mathlib/pull/2156))
#### Estimated changes
Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* category_theory.limits.cokernel_cofork.app_zero
- \+ *lemma* category_theory.limits.cokernel_cofork.condition
- \+ *abbreviation* category_theory.limits.cokernel_cofork.of_π
- \+ *abbreviation* category_theory.limits.cokernel_cofork
- \+ *lemma* category_theory.limits.kernel_fork.app_one
- \+ *lemma* category_theory.limits.kernel_fork.condition
- \+ *abbreviation* category_theory.limits.kernel_fork.of_ι
- \+ *abbreviation* category_theory.limits.kernel_fork



## [2020-03-15 21:15:49](https://github.com/leanprover-community/mathlib/commit/87f8ab2)
chore(nnreal): replace coe_le with coe_le_coe ([#2159](https://github.com/leanprover-community/mathlib/pull/2159))
#### Estimated changes
Modified src/analysis/convex/topology.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/specific_limits.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean


Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/basic.lean




## [2020-03-15 15:21:50](https://github.com/leanprover-community/mathlib/commit/7104132)
chore(field_theory/finite): spelling mistake ([#2157](https://github.com/leanprover-community/mathlib/pull/2157))
#### Estimated changes
Modified src/field_theory/finite.lean




## [2020-03-15 04:22:33](https://github.com/leanprover-community/mathlib/commit/0cbfbab)
refactor(logic/function): inv_fun takes a nonempty instance instead of inhabited ([#2148](https://github.com/leanprover-community/mathlib/pull/2148))
#### Estimated changes
Modified src/logic/function.lean
- \+/\- *lemma* function.inv_fun_neg
- \+/\- *theorem* function.inv_fun_on_neg



## [2020-03-15 03:04:18](https://github.com/leanprover-community/mathlib/commit/b314df2)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-15 01:43:38](https://github.com/leanprover-community/mathlib/commit/8c2a254)
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
#### Estimated changes
Modified scripts/nolints.txt


Modified src/category_theory/monad/algebra.lean
- \+ *def* category_theory.comonad.adj
- \+ *def* category_theory.comonad.coalgebra.hom.comp
- \+ *def* category_theory.comonad.coalgebra.hom.id
- \+ *structure* category_theory.comonad.coalgebra.hom
- \+ *structure* category_theory.comonad.coalgebra
- \+ *def* category_theory.comonad.cofree
- \+ *def* category_theory.comonad.forget

Modified src/category_theory/monad/basic.lean




## [2020-03-15 00:49:28](https://github.com/leanprover-community/mathlib/commit/e4bf0bf)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-14 23:31:44](https://github.com/leanprover-community/mathlib/commit/5433973)
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
#### Estimated changes
Added docs/tutorial/category_theory/Ab.lean


Modified scripts/nolints.txt


Modified src/algebra/category/CommRing/colimits.lean
- \+/\- *def* CommRing.colimits.desc_morphism

Renamed src/algebra/category/Group.lean to src/algebra/category/Group/basic.lean
- \+ *abbreviation* Ab
- \+ *lemma* CommGroup.one_apply
- \+ *lemma* Group.one_apply

Added src/algebra/category/Group/colimits.lean
- \+ *def* AddCommGroup.colimits.cocone_fun
- \+ *def* AddCommGroup.colimits.cocone_morphism
- \+ *lemma* AddCommGroup.colimits.cocone_naturality
- \+ *lemma* AddCommGroup.colimits.cocone_naturality_components
- \+ *def* AddCommGroup.colimits.colimit
- \+ *def* AddCommGroup.colimits.colimit_cocone
- \+ *def* AddCommGroup.colimits.colimit_is_colimit
- \+ *def* AddCommGroup.colimits.colimit_setoid
- \+ *def* AddCommGroup.colimits.colimit_type
- \+ *def* AddCommGroup.colimits.desc_fun
- \+ *def* AddCommGroup.colimits.desc_fun_lift
- \+ *def* AddCommGroup.colimits.desc_morphism
- \+ *inductive* AddCommGroup.colimits.prequotient
- \+ *lemma* AddCommGroup.colimits.quot_add
- \+ *lemma* AddCommGroup.colimits.quot_neg
- \+ *lemma* AddCommGroup.colimits.quot_zero
- \+ *inductive* AddCommGroup.colimits.relation

Added src/algebra/category/Group/default.lean


Added src/algebra/category/Group/limits.lean
- \+ *def* AddCommGroup.AddCommGroup_has_limits.limit
- \+ *def* AddCommGroup.AddCommGroup_has_limits.limit_is_limit
- \+ *def* AddCommGroup.limit_π_add_monoid_hom

Added src/algebra/category/Group/zero.lean


Modified src/algebra/category/Mon/colimits.lean
- \+/\- *def* Mon.colimits.desc_morphism



## [2020-03-14 21:19:35](https://github.com/leanprover-community/mathlib/commit/2e781eb)
doc(docs/install/*): emphasize projects link ([#2151](https://github.com/leanprover-community/mathlib/pull/2151))
#### Estimated changes
Modified docs/install/debian_details.md


Modified docs/install/linux.md


Modified docs/install/macos.md




## [2020-03-14 20:14:08](https://github.com/leanprover-community/mathlib/commit/2065438)
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
#### Estimated changes
Modified src/category_theory/comma.lean
- \+ *def* category_theory.over.iterated_slice_backward
- \+ *lemma* category_theory.over.iterated_slice_backward_forget_forget
- \+ *def* category_theory.over.iterated_slice_equiv
- \+ *def* category_theory.over.iterated_slice_forward
- \+ *lemma* category_theory.over.iterated_slice_forward_forget

Modified src/category_theory/limits/over.lean
- \+ *lemma* category_theory.over.over_prod_fst_left
- \+ *lemma* category_theory.over.over_prod_map_left
- \+ *lemma* category_theory.over.over_prod_pair_hom
- \+ *lemma* category_theory.over.over_prod_pair_left
- \+ *lemma* category_theory.over.over_prod_snd_left
- \+ *def* category_theory.over.over_product_of_pullbacks

Modified src/category_theory/limits/shapes/constructions/equalizers.lean


Modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *lemma* category_theory.limits.pullback_cone.condition
- \+ *lemma* category_theory.limits.pullback_cone.mk_left
- \+ *lemma* category_theory.limits.pullback_cone.mk_right



## [2020-03-14 18:14:17](https://github.com/leanprover-community/mathlib/commit/cc39a15)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-14 17:09:36](https://github.com/leanprover-community/mathlib/commit/7b2be40)
refactor(data/equiv/algebra): split ([#2147](https://github.com/leanprover-community/mathlib/pull/2147))
* refactor(data/equiv/algebra): split
I want to use `≃*` without importing `ring`.
* Update src/data/equiv/ring.lean
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/free_monoid.lean


Modified src/algebra/semiconj.lean


Modified src/category_theory/endomorphism.lean


Modified src/category_theory/single_obj.lean


Deleted src/data/equiv/algebra.lean
- \- *def* add_aut.to_perm
- \- *lemma* add_equiv.map_sub
- \- *structure* add_equiv
- \- *lemma* equiv.add_def
- \- *lemma* equiv.coe_units_equiv_ne_zero
- \- *lemma* equiv.inv_def
- \- *lemma* equiv.mul_def
- \- *lemma* equiv.neg_def
- \- *lemma* equiv.one_def
- \- *def* equiv.units_equiv_ne_zero
- \- *lemma* equiv.zero_def
- \- *def* mul_aut.to_perm
- \- *def* mul_aut
- \- *lemma* mul_equiv.apply_symm_apply
- \- *lemma* mul_equiv.ext
- \- *lemma* mul_equiv.map_eq_one_iff
- \- *lemma* mul_equiv.map_inv
- \- *lemma* mul_equiv.map_mul
- \- *lemma* mul_equiv.map_ne_one_iff
- \- *lemma* mul_equiv.map_one
- \- *def* mul_equiv.mk'
- \- *def* mul_equiv.refl
- \- *def* mul_equiv.symm
- \- *lemma* mul_equiv.symm_apply_apply
- \- *lemma* mul_equiv.symm_to_monoid_hom_apply_to_monoid_hom_apply
- \- *theorem* mul_equiv.to_equiv_symm
- \- *def* mul_equiv.to_monoid_hom
- \- *lemma* mul_equiv.to_monoid_hom_apply_symm_to_monoid_hom_apply
- \- *def* mul_equiv.to_ring_equiv
- \- *def* mul_equiv.trans
- \- *structure* mul_equiv
- \- *def* ring_aut.to_add_aut
- \- *def* ring_aut.to_mul_aut
- \- *def* ring_aut.to_perm
- \- *def* ring_aut
- \- *lemma* ring_equiv.apply_symm_apply
- \- *lemma* ring_equiv.coe_add_equiv
- \- *lemma* ring_equiv.coe_mul_equiv
- \- *lemma* ring_equiv.ext
- \- *lemma* ring_equiv.image_eq_preimage
- \- *lemma* ring_equiv.map_add
- \- *lemma* ring_equiv.map_eq_one_iff
- \- *lemma* ring_equiv.map_eq_zero_iff
- \- *lemma* ring_equiv.map_mul
- \- *lemma* ring_equiv.map_ne_one_iff
- \- *lemma* ring_equiv.map_ne_zero_iff
- \- *lemma* ring_equiv.map_neg
- \- *lemma* ring_equiv.map_neg_one
- \- *lemma* ring_equiv.map_one
- \- *lemma* ring_equiv.map_sub
- \- *lemma* ring_equiv.map_zero
- \- *def* ring_equiv.of'
- \- *def* ring_equiv.of
- \- *lemma* ring_equiv.symm_apply_apply
- \- *lemma* ring_equiv.symm_to_ring_hom_apply_to_ring_hom_apply
- \- *abbreviation* ring_equiv.to_add_monoid_hom
- \- *abbreviation* ring_equiv.to_monoid_hom
- \- *def* ring_equiv.to_ring_hom
- \- *lemma* ring_equiv.to_ring_hom_apply_symm_to_ring_hom_apply
- \- *structure* ring_equiv
- \- *def* to_units
- \- *def* units.map_equiv

Added src/data/equiv/mul_add.lean
- \+ *def* add_aut.to_perm
- \+ *lemma* add_equiv.map_sub
- \+ *structure* add_equiv
- \+ *def* mul_aut.to_perm
- \+ *def* mul_aut
- \+ *lemma* mul_equiv.apply_symm_apply
- \+ *lemma* mul_equiv.ext
- \+ *lemma* mul_equiv.map_eq_one_iff
- \+ *lemma* mul_equiv.map_inv
- \+ *lemma* mul_equiv.map_mul
- \+ *lemma* mul_equiv.map_ne_one_iff
- \+ *lemma* mul_equiv.map_one
- \+ *def* mul_equiv.mk'
- \+ *def* mul_equiv.refl
- \+ *def* mul_equiv.symm
- \+ *lemma* mul_equiv.symm_apply_apply
- \+ *theorem* mul_equiv.to_equiv_symm
- \+ *def* mul_equiv.to_monoid_hom
- \+ *lemma* mul_equiv.to_monoid_hom_apply
- \+ *def* mul_equiv.trans
- \+ *structure* mul_equiv
- \+ *def* to_units
- \+ *def* units.map_equiv

Added src/data/equiv/ring.lean
- \+ *lemma* equiv.coe_units_equiv_ne_zero
- \+ *def* equiv.units_equiv_ne_zero
- \+ *def* mul_equiv.to_ring_equiv
- \+ *def* ring_aut.to_add_aut
- \+ *def* ring_aut.to_mul_aut
- \+ *def* ring_aut.to_perm
- \+ *def* ring_aut
- \+ *lemma* ring_equiv.apply_symm_apply
- \+ *lemma* ring_equiv.coe_add_equiv
- \+ *lemma* ring_equiv.coe_mul_equiv
- \+ *lemma* ring_equiv.ext
- \+ *lemma* ring_equiv.image_eq_preimage
- \+ *lemma* ring_equiv.map_add
- \+ *lemma* ring_equiv.map_eq_one_iff
- \+ *lemma* ring_equiv.map_eq_zero_iff
- \+ *lemma* ring_equiv.map_mul
- \+ *lemma* ring_equiv.map_ne_one_iff
- \+ *lemma* ring_equiv.map_ne_zero_iff
- \+ *lemma* ring_equiv.map_neg
- \+ *lemma* ring_equiv.map_neg_one
- \+ *lemma* ring_equiv.map_one
- \+ *lemma* ring_equiv.map_sub
- \+ *lemma* ring_equiv.map_zero
- \+ *def* ring_equiv.of'
- \+ *def* ring_equiv.of
- \+ *lemma* ring_equiv.symm_apply_apply
- \+ *lemma* ring_equiv.symm_to_ring_hom_apply_to_ring_hom_apply
- \+ *abbreviation* ring_equiv.to_add_monoid_hom
- \+ *abbreviation* ring_equiv.to_monoid_hom
- \+ *def* ring_equiv.to_ring_hom
- \+ *lemma* ring_equiv.to_ring_hom_apply_symm_to_ring_hom_apply
- \+ *structure* ring_equiv

Added src/data/equiv/transfer_instance.lean
- \+ *lemma* equiv.add_def
- \+ *lemma* equiv.inv_def
- \+ *lemma* equiv.mul_def
- \+ *lemma* equiv.neg_def
- \+ *lemma* equiv.one_def
- \+ *lemma* equiv.zero_def

Modified src/data/mv_polynomial.lean


Modified src/field_theory/finite.lean


Modified src/group_theory/submonoid.lean


Modified src/linear_algebra/basic.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/free_ring.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/maps.lean


Modified src/ring_theory/noetherian.lean


Modified src/topology/algebra/group.lean




## [2020-03-14 15:02:52](https://github.com/leanprover-community/mathlib/commit/e6ccfe0)
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
#### Estimated changes
Modified src/algebra/category/Group.lean
- \+ *lemma* CommGroup.ext
- \+ *lemma* Group.ext

Added src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/algebra/category/Module/basic.lean


Modified src/algebra/module.lean
- \+ *def* add_comm_group.int_module
- \+ *def* add_comm_monoid.nat_semimodule
- \+ *lemma* add_monoid_hom.map_int_module_smul
- \+ *lemma* add_monoid_hom.map_smul_cast
- \+ *def* linear_map.to_add_monoid_hom
- \+ *lemma* linear_map.to_add_monoid_hom_coe
- \+ *lemma* module.add_monoid_smul_eq_smul
- \+ *lemma* module.gsmul_eq_smul
- \+ *lemma* module.gsmul_eq_smul_cast
- \+ *lemma* module_ext



## [2020-03-14 12:47:55](https://github.com/leanprover-community/mathlib/commit/d313d14)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-14 11:28:34](https://github.com/leanprover-community/mathlib/commit/559921a)
feat(algebra/category/Group): the free-forgetful adjunction for AddCommGroup ([#2141](https://github.com/leanprover-community/mathlib/pull/2141))
* feat(algebra/category/Group): the free-forgetful adjunction for AddCommGroup
* fixes
* Update src/group_theory/free_abelian_group.lean
* oops
#### Estimated changes
Added src/algebra/category/Group/adjunctions.lean
- \+ *def* AddCommGroup.adj
- \+ *def* AddCommGroup.free
- \+ *lemma* AddCommGroup.free_map_coe
- \+ *lemma* AddCommGroup.free_obj_coe

Modified src/algebra/group/hom.lean


Modified src/group_theory/free_abelian_group.lean
- \+ *def* free_abelian_group.hom_equiv
- \+ *lemma* free_abelian_group.hom_equiv_apply
- \+ *lemma* free_abelian_group.hom_equiv_symm_apply
- \- *def* free_abelian_group.lift.universal
- \+ *lemma* free_abelian_group.lift_comp
- \+ *lemma* free_abelian_group.map_of



## [2020-03-14 09:21:38](https://github.com/leanprover-community/mathlib/commit/465f599)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-14 08:02:49](https://github.com/leanprover-community/mathlib/commit/81d3ebf)
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
#### Estimated changes
Modified src/algebra/category/Module/basic.lean
- \+/\- *def* Module.kernel_is_limit
- \+ *def* Module.of_self
- \+ *def* category_theory.iso.to_linear_equiv
- \+ *def* linear_equiv.to_Module_iso
- \+ *def* linear_equiv_iso_Group_iso

Added src/algebra/category/Module/monoidal.lean
- \+ *def* Module.monoidal_category.associator
- \+ *lemma* Module.monoidal_category.associator_naturality
- \+ *def* Module.monoidal_category.left_unitor
- \+ *lemma* Module.monoidal_category.left_unitor_naturality
- \+ *lemma* Module.monoidal_category.pentagon
- \+ *def* Module.monoidal_category.right_unitor
- \+ *lemma* Module.monoidal_category.right_unitor_naturality
- \+ *lemma* Module.monoidal_category.tensor_comp
- \+ *def* Module.monoidal_category.tensor_hom
- \+ *lemma* Module.monoidal_category.tensor_id
- \+ *def* Module.monoidal_category.tensor_obj
- \+ *lemma* Module.monoidal_category.triangle

Modified src/category_theory/limits/types.lean
- \- *def* category_theory.limits.types.colimit
- \+ *def* category_theory.limits.types.colimit_
- \- *def* category_theory.limits.types.colimit_is_colimit
- \+ *def* category_theory.limits.types.colimit_is_colimit_
- \- *def* category_theory.limits.types.limit
- \+ *def* category_theory.limits.types.limit_
- \- *def* category_theory.limits.types.limit_is_limit
- \+ *def* category_theory.limits.types.limit_is_limit_
- \+/\- *lemma* category_theory.limits.types.types_limit_map
- \+/\- *lemma* category_theory.limits.types.types_limit_π

Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_equiv.refl
- \+/\- *def* linear_equiv.symm
- \+/\- *def* linear_equiv.trans
- \+ *theorem* linear_equiv.trans_apply

Modified src/linear_algebra/tensor_product.lean
- \+ *theorem* tensor_product.assoc_tmul
- \+ *theorem* tensor_product.ext_fourfold
- \+ *theorem* tensor_product.ext_threefold
- \+ *theorem* tensor_product.lid_tmul
- \+ *theorem* tensor_product.rid_tmul



## [2020-03-14 04:10:31](https://github.com/leanprover-community/mathlib/commit/3d621b5)
refactor(ring_theory/subring): use bundled homs ([#2144](https://github.com/leanprover-community/mathlib/pull/2144))
#### Estimated changes
Modified src/field_theory/subfield.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/subring.lean
- \+ *lemma* is_subring.coe_subtype
- \+ *def* is_subring.subtype
- \+/\- *lemma* ring.image_closure



## [2020-03-14 01:59:21](https://github.com/leanprover-community/mathlib/commit/ade1ee3)
feat(category_theory/limits): derive has_binary_products from has_limit (pair X Y) ([#2139](https://github.com/leanprover-community/mathlib/pull/2139))
* feat(category_theory/limits): derive has_binary_products from has_limit (pair X Y)
* Rename *_of_diagram to diagram_iso_*
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *def* category_theory.limits.diagram_iso_pair
- \+ *def* category_theory.limits.has_binary_coproducts_of_has_colimit_pair
- \+ *def* category_theory.limits.has_binary_products_of_has_limit_pair

Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.diagram_iso_parallel_pair
- \+ *def* category_theory.limits.has_coequalizers_of_has_colimit_parallel_pair
- \+ *def* category_theory.limits.has_equalizers_of_has_limit_parallel_pair

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* category_theory.limits.diagram_iso_cospan
- \+ *def* category_theory.limits.diagram_iso_span
- \+ *def* category_theory.limits.has_pullbacks_of_has_limit_cospan
- \+ *def* category_theory.limits.has_pushouts_of_has_colimit_span



## [2020-03-13 18:31:09](https://github.com/leanprover-community/mathlib/commit/49f5fb8)
chore(algebra/category/CommRing/limits): avoid `is_ring_hom` ([#2142](https://github.com/leanprover-community/mathlib/pull/2142))
define a `ring_hom` instead
#### Estimated changes
Modified src/algebra/category/CommRing/limits.lean
- \+ *def* CommRing.limit_π_ring_hom



## [2020-03-13 12:20:20](https://github.com/leanprover-community/mathlib/commit/32c2768)
chore(linear_algebra/basic): simplify two proofs ([#2123](https://github.com/leanprover-community/mathlib/pull/2123))
* chore(linear_algebra/basic): simplify two proofs
Also drop `linear_map.congr_right` in favor of
`linear_equiv.congr_right`. I'll restore the deleted `congr_right`
as `comp_map : (M₂ →ₗ[R] M₃) →ₗ[R] (M →ₗ[R] M₂) →ₗ[R] (M →ₗ[R] M₃)` soon.
* Fix compile
* Restore `congr_right` under the name `comp_right`.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_equiv.conj
- \+ *def* linear_map.comp_right
- \- *def* linear_map.congr_right
- \- *theorem* submodule.Union_coe_of_directed
- \+ *theorem* submodule.coe_supr_of_directed
- \+/\- *theorem* submodule.mem_supr_of_directed

Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/ideals.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial.lean




## [2020-03-13 10:18:27](https://github.com/leanprover-community/mathlib/commit/aec62dc)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-13 09:00:12](https://github.com/leanprover-community/mathlib/commit/b54960d)
refactor(*): migrate some files to bundled ring homs ([#2133](https://github.com/leanprover-community/mathlib/pull/2133))
* refactor(*): migrate some files to bundled ring homs
* Rename ring_hom.is_local back to is_local_ring_hom
* Apply suggestions from code review
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Restore 2 instances, make `map` use bundled homs
* More bundled homs
* Add a docstring
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* ring_hom.map_prod
- \+ *lemma* ring_hom.map_sum

Modified src/algebra/direct_limit.lean
- \+/\- *def* ring.direct_limit.lift
- \+/\- *lemma* ring.direct_limit.lift_add
- \+ *def* ring.direct_limit.lift_hom
- \+/\- *lemma* ring.direct_limit.lift_mul
- \+/\- *lemma* ring.direct_limit.lift_neg
- \+/\- *lemma* ring.direct_limit.lift_one
- \+/\- *lemma* ring.direct_limit.lift_pow
- \+/\- *lemma* ring.direct_limit.lift_sub
- \+/\- *lemma* ring.direct_limit.lift_zero

Modified src/algebra/pi_instances.lean


Modified src/algebra/ring.lean
- \+ *lemma* ring_hom.coe_mk

Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* adjoin_root.coe_injective
- \+/\- *lemma* adjoin_root.eval₂_root
- \+/\- *lemma* adjoin_root.is_root_root
- \+/\- *def* adjoin_root.lift
- \+/\- *lemma* adjoin_root.lift_mk
- \+/\- *lemma* adjoin_root.lift_of
- \+/\- *lemma* adjoin_root.lift_root
- \+/\- *def* adjoin_root.mk
- \+ *lemma* adjoin_root.mk_C
- \+/\- *lemma* adjoin_root.mk_self
- \+/\- *lemma* adjoin_root.mul_div_root_cancel
- \+/\- *def* adjoin_root.of
- \+/\- *def* adjoin_root.root
- \+/\- *def* adjoin_root

Modified src/ring_theory/free_comm_ring.lean
- \+ *lemma* free_comm_ring.coe_lift_hom
- \+ *def* free_comm_ring.lift_hom
- \+/\- *def* free_comm_ring.map
- \+/\- *lemma* free_comm_ring.map_add
- \+/\- *lemma* free_comm_ring.map_mul
- \+/\- *lemma* free_comm_ring.map_neg
- \+/\- *lemma* free_comm_ring.map_of
- \+/\- *lemma* free_comm_ring.map_one
- \+/\- *lemma* free_comm_ring.map_pow
- \+/\- *lemma* free_comm_ring.map_sub
- \+/\- *lemma* free_comm_ring.map_zero

Modified src/ring_theory/ideal_operations.lean
- \- *theorem* ideal.is_ring_hom_quotient_inf_to_pi_quotient
- \- *lemma* is_ring_hom.inj_iff_ker_eq_bot
- \- *lemma* is_ring_hom.injective_iff
- \- *def* is_ring_hom.ker
- \- *lemma* is_ring_hom.ker_eq
- \- *lemma* is_ring_hom.ker_eq_bot_iff_eq_zero
- \- *lemma* is_ring_hom.ker_is_prime
- \- *lemma* is_ring_hom.mem_ker
- \- *lemma* is_ring_hom.not_one_mem_ker
- \+ *lemma* ring_hom.inj_iff_ker_eq_bot
- \+ *def* ring_hom.ker
- \+ *lemma* ring_hom.ker_eq
- \+ *lemma* ring_hom.ker_eq_bot_iff_eq_zero
- \+ *lemma* ring_hom.ker_is_prime
- \+ *lemma* ring_hom.mem_ker
- \+ *lemma* ring_hom.not_one_mem_ker

Modified src/ring_theory/ideals.lean
- \+/\- *def* ideal.quotient.lift
- \+/\- *lemma* ideal.quotient.lift_mk
- \+ *def* ideal.quotient.mk_hom
- \+ *lemma* ideal.quotient.mk_prod
- \+ *lemma* ideal.quotient.mk_sum
- \+/\- *lemma* is_unit_of_map_unit

Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/power_series.lean


Modified src/ring_theory/subring.lean
- \+ *def* ring_hom.cod_restrict



## [2020-03-12 18:52:10](https://github.com/leanprover-community/mathlib/commit/1c449b6)
chore(algebra/field*, field_theory/subfield): drop some `x ≠ 0`, use `division_ring` ([#2136](https://github.com/leanprover-community/mathlib/pull/2136))
* chore(algebra/field*, field_theory/subfield): drop some `x ≠ 0`, use `division_ring`
We have `0⁻¹=0` in `division_ring` now, so no need to assume `field`
in `ring_hom.map_inv` etc.
* Fix lint
#### Estimated changes
Modified src/algebra/field.lean
- \- *lemma* is_ring_hom.map_div'
- \- *lemma* is_ring_hom.map_inv'
- \- *lemma* neg_inv'
- \- *lemma* ring_hom.map_div'
- \- *lemma* ring_hom.map_inv'

Modified src/algebra/field_power.lean
- \- *lemma* is_ring_hom.map_fpow'
- \+/\- *lemma* is_ring_hom.map_fpow
- \- *lemma* ring_hom.map_fpow'
- \+/\- *lemma* ring_hom.map_fpow

Modified src/field_theory/subfield.lean




## [2020-03-12 16:38:40](https://github.com/leanprover-community/mathlib/commit/5fe72b6)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-12 15:18:41](https://github.com/leanprover-community/mathlib/commit/f5787f5)
doc(*): switch from update-mathlib to leanproject ([#2093](https://github.com/leanprover-community/mathlib/pull/2093))
* doc(*): switch from update-mathlib to leanproject
* Apply suggestions from code review
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Use shiny new `leanproject new` and `leanproject get`
* documentation tweaks
* project.md tweaks
#### Estimated changes
Modified docs/contribute/index.md


Modified docs/install/debian.md


Modified docs/install/debian_details.md


Modified docs/install/linux.md


Modified docs/install/project.md


Modified docs/install/windows.md




## [2020-03-12 13:07:30](https://github.com/leanprover-community/mathlib/commit/8131108)
feat(category_theory/opposites): add nat_iso.unop ([#2132](https://github.com/leanprover-community/mathlib/pull/2132))
* Add nat_iso.unop
* Add docstrings to nat_iso.op, nat_iso.unop
#### Estimated changes
Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.nat_iso.unop_hom
- \+ *lemma* category_theory.nat_iso.unop_inv



## [2020-03-12 10:56:40](https://github.com/leanprover-community/mathlib/commit/7d357d7)
Fix a typo ([#2137](https://github.com/leanprover-community/mathlib/pull/2137))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.binary_cofan.mk_ι_app_left
- \+ *lemma* category_theory.limits.binary_cofan.mk_ι_app_right
- \- *lemma* category_theory.limits.binary_cofan.mk_π_app_left
- \- *lemma* category_theory.limits.binary_cofan.mk_π_app_right



## [2020-03-12 05:14:27](https://github.com/leanprover-community/mathlib/commit/35a6e68)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-12 04:06:30](https://github.com/leanprover-community/mathlib/commit/1b0a749)
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
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.image_inter_subset
- \- *theorem* set.mono_image

Modified src/data/set/lattice.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.bot_prod
- \+ *lemma* filter.map_ne_bot_iff
- \+/\- *lemma* filter.prod_bot
- \+/\- *lemma* filter.prod_comm'
- \+/\- *lemma* filter.prod_comm
- \+/\- *lemma* filter.prod_eq_bot
- \+/\- *lemma* filter.prod_ne_bot
- \+/\- *lemma* filter.prod_pure_pure
- \+/\- *lemma* filter.tendsto_fst
- \+/\- *lemma* filter.tendsto_snd

Modified src/order/lattice.lean
- \+ *lemma* lattice.inf_le_inf_left
- \+ *lemma* lattice.inf_le_inf_right

Modified src/ring_theory/free_comm_ring.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/subset_properties.lean
- \+ *lemma* cluster_point_of_compact
- \+ *theorem* is_closed_proj_of_compact

Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-03-11 22:56:21](https://github.com/leanprover-community/mathlib/commit/7c8dc2a)
feat(category_theory/limits): construct equalizers from pullbacks and products ([#2124](https://github.com/leanprover-community/mathlib/pull/2124))
* construct equalizers from pullbacks and products
* ...
* changes from review
* Add docstrings
* golf proofs a little
* linter
#### Estimated changes
Modified src/category_theory/category/default.lean
- \+ *lemma* category_theory.eq_whisker
- \+ *lemma* category_theory.whisker_eq

Added src/category_theory/limits/shapes/constructions/equalizers.lean
- \+ *def* category_theory.limits.has_equalizers_of_pullbacks_and_binary_products.construct_equalizer
- \+ *def* category_theory.limits.has_equalizers_of_pullbacks_and_binary_products.equalizer_cone
- \+ *def* category_theory.limits.has_equalizers_of_pullbacks_and_binary_products.equalizer_cone_is_limit
- \+ *abbreviation* category_theory.limits.has_equalizers_of_pullbacks_and_binary_products.pullback_fst
- \+ *lemma* category_theory.limits.has_equalizers_of_pullbacks_and_binary_products.pullback_fst_eq_pullback_snd
- \+ *def* category_theory.limits.has_equalizers_of_pullbacks_and_binary_products



## [2020-03-11 18:57:43](https://github.com/leanprover-community/mathlib/commit/7cffe25)
chore(category_theory/cones): make functor argument of forget explicit ([#2128](https://github.com/leanprover-community/mathlib/pull/2128))
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \+/\- *def* category_theory.limits.cocones.forget
- \+/\- *def* category_theory.limits.cones.forget

Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/kernels.lean
- \- *def* category_theory.limits.cokernel.of_kernel_of_mono
- \- *def* category_theory.limits.kernel.of_cokernel_of_epi



## [2020-03-11 10:15:41](https://github.com/leanprover-community/mathlib/commit/43431be)
chore(category_theory): remove functor.of ([#2127](https://github.com/leanprover-community/mathlib/pull/2127))
* chore(category_theory): remove functor.of
* fix
#### Estimated changes
Modified src/category_theory/comma.lean
- \+/\- *def* category_theory.over.map
- \+/\- *def* category_theory.over
- \+/\- *def* category_theory.under.map
- \+/\- *def* category_theory.under

Modified src/category_theory/elements.lean
- \+/\- *def* category_theory.category_of_elements.comma_equivalence
- \+/\- *def* category_theory.category_of_elements.from_comma
- \+/\- *def* category_theory.category_of_elements.to_comma

Modified src/category_theory/punit.lean
- \- *lemma* category_theory.functor.of.map_app
- \- *lemma* category_theory.functor.of.obj_map
- \- *lemma* category_theory.functor.of.obj_obj
- \- *def* category_theory.functor.of



## [2020-03-11 07:13:33](https://github.com/leanprover-community/mathlib/commit/d909a61)
fix(algebra/category): avoid deprecated lemmas ([#2126](https://github.com/leanprover-community/mathlib/pull/2126))
#### Estimated changes
Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/Mon/colimits.lean




## [2020-03-10 19:54:59](https://github.com/leanprover-community/mathlib/commit/36ac916)
Add two missing duals ([#2122](https://github.com/leanprover-community/mathlib/pull/2122))
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.cofork.of_π_app_one
- \+ *lemma* category_theory.limits.cofork.of_π_app_zero



## [2020-03-10 17:38:33](https://github.com/leanprover-community/mathlib/commit/699401b)
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
#### Estimated changes
Modified .github/workflows/build.yml


Added scripts/fetch_olean_cache.sh


Added scripts/look_up_olean_hash.py


Added scripts/write_azure_table_entry.py




## [2020-03-10 15:29:25](https://github.com/leanprover-community/mathlib/commit/668a98e)
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
#### Estimated changes
Modified src/measure_theory/measurable_space.lean
- \+ *theorem* measurable_space.is_measurable_Sup
- \+ *theorem* measurable_space.is_measurable_sup
- \+ *theorem* measurable_space.is_measurable_supr



## [2020-03-10 13:12:10](https://github.com/leanprover-community/mathlib/commit/9feefee)
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
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *def* mv_polynomial.fin_succ_equiv

Modified src/data/polynomial.lean
- \+ *lemma* is_integral_domain.polynomial

Modified src/ring_theory/polynomial.lean
- \+/\- *lemma* mv_polynomial.is_integral_domain_fin
- \+ *lemma* mv_polynomial.is_integral_domain_fin_zero



## [2020-03-10 10:57:20](https://github.com/leanprover-community/mathlib/commit/cdc56ba)
feat(analysis/calculus/tangent_cone): prove that all intervals are `unique_diff_on` ([#2108](https://github.com/leanprover-community/mathlib/pull/2108))
* feat(analysis/calculus/tangent_cone): prove that all intervals are `unique_diff_on`
* Drop some unneeded assumptions
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean
- \+ *lemma* unique_diff_on_Icc
- \+ *lemma* unique_diff_on_Ici
- \+ *lemma* unique_diff_on_Ico
- \+ *lemma* unique_diff_on_Iic
- \+ *lemma* unique_diff_on_Iio
- \+ *lemma* unique_diff_on_Ioc
- \+ *lemma* unique_diff_on_Ioi
- \+ *lemma* unique_diff_on_Ioo
- \+ *lemma* unique_diff_on_empty



## [2020-03-10 06:39:45](https://github.com/leanprover-community/mathlib/commit/e8ad2e3)
feat(category_theory/limits): the pullback of a monomorphism is a monomorphism ([#2113](https://github.com/leanprover-community/mathlib/pull/2113))
* The pullback of a monomorphism is a monomorphism
* The pushout of an epimorphism is an epimorphism
* Fix a proof
* renaming
#### Estimated changes
Modified src/category_theory/limits/shapes/constructions/binary_products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* category_theory.limits.pullback.hom_ext
- \+ *lemma* category_theory.limits.pullback_cone.equalizer_ext
- \+ *lemma* category_theory.limits.pushout.hom_ext
- \+ *lemma* category_theory.limits.pushout_cocone.coequalizer_ext



## [2020-03-10 04:22:40](https://github.com/leanprover-community/mathlib/commit/945845d)
feat(linter): include linter name in report ([#2116](https://github.com/leanprover-community/mathlib/pull/2116))
* feat(linter): include linter name in report (closes [#2098](https://github.com/leanprover-community/mathlib/pull/2098))
* Update src/tactic/lint.lean
#### Estimated changes
Modified src/tactic/lint.lean




## [2020-03-10 02:12:06](https://github.com/leanprover-community/mathlib/commit/4089712)
chore(ring_theory/polynomial): refactor proof of is_noetherian_ring_fin ([#2117](https://github.com/leanprover-community/mathlib/pull/2117))
#### Estimated changes
Modified src/ring_theory/polynomial.lean
- \+/\- *theorem* mv_polynomial.is_noetherian_ring_fin
- \+ *lemma* mv_polynomial.is_noetherian_ring_fin_0



## [2020-03-09 23:57:38](https://github.com/leanprover-community/mathlib/commit/25df884)
reflexive transitive closure is symmetric of original ([#2115](https://github.com/leanprover-community/mathlib/pull/2115))
* reflexive transitive closure is symmetric if original
* Update src/logic/relation.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/logic/relation.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/logic/relation.lean
- \+ *lemma* relation.refl_trans_gen.symmetric



## [2020-03-09 21:54:46](https://github.com/leanprover-community/mathlib/commit/f90803c)
feat(algebra/group/hom): cancel injective/surjective `monoid_hom`s ([#2112](https://github.com/leanprover-community/mathlib/pull/2112))
* feat(algebra/group/hom): cancel injective/surjective `monoid_hom`s
* Add a `ring_hom` version
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.cancel_left
- \+ *lemma* monoid_hom.cancel_right

Modified src/algebra/ring.lean
- \+ *lemma* ring_hom.cancel_left
- \+ *lemma* ring_hom.cancel_right



## [2020-03-09 19:43:42](https://github.com/leanprover-community/mathlib/commit/b39713f)
feat(analysis/calculus/darboux): IVT for derivatives ([#2110](https://github.com/leanprover-community/mathlib/pull/2110))
* feat(analysis/calculus/darboux): IVT for derivatives
* whitespace
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
#### Estimated changes
Added src/analysis/calculus/darboux.lean
- \+ *theorem* convex_image_has_deriv_at
- \+ *theorem* deriv_forall_lt_or_forall_gt_of_forall_ne
- \+ *theorem* exists_has_deriv_within_at_eq_of_gt_of_lt
- \+ *theorem* exists_has_deriv_within_at_eq_of_lt_of_gt

Modified src/analysis/calculus/local_extr.lean




## [2020-03-09 14:27:32](https://github.com/leanprover-community/mathlib/commit/62abc4d)
feat(category_theory): images ([#2100](https://github.com/leanprover-community/mathlib/pull/2100))
* feat(category_theory): images
* oops, forgot to add file
* Update src/category_theory/category/default.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* some improvements
* linting
* oops
* Update src/category_theory/limits/shapes/images.lean
#### Estimated changes
Modified src/category_theory/category/default.lean
- \+/\- *lemma* category_theory.cancel_epi
- \+ *lemma* category_theory.cancel_epi_id
- \+/\- *lemma* category_theory.cancel_mono
- \+ *lemma* category_theory.cancel_mono_id
- \+ *lemma* category_theory.epi_of_epi
- \+ *lemma* category_theory.epi_of_epi_fac
- \+ *lemma* category_theory.mono_of_mono
- \+ *lemma* category_theory.mono_of_mono_fac

Modified src/category_theory/limits/shapes/equalizers.lean
- \- *lemma* category_theory.limits.coequalizer.π_epi
- \- *lemma* category_theory.limits.equalizer.ι_mono

Added src/category_theory/limits/shapes/images.lean
- \+ *def* category_theory.limits.factor_thru_image
- \+ *lemma* category_theory.limits.has_image.uniq
- \+ *lemma* category_theory.limits.image.as_c
- \+ *lemma* category_theory.limits.image.as_ι
- \+ *def* category_theory.limits.image.c
- \+ *lemma* category_theory.limits.image.c_ι
- \+ *lemma* category_theory.limits.image.fac
- \+ *def* category_theory.limits.image.is_image
- \+ *def* category_theory.limits.image.lift
- \+ *lemma* category_theory.limits.image.lift_fac
- \+ *def* category_theory.limits.image.mono_factorisation
- \+ *def* category_theory.limits.image.ι
- \+ *def* category_theory.limits.image
- \+ *def* category_theory.limits.image_mono_iso_source
- \+ *lemma* category_theory.limits.image_mono_iso_source_hom_self
- \+ *lemma* category_theory.limits.image_mono_iso_source_inv_ι
- \+ *def* category_theory.limits.is_image.iso_ext
- \+ *def* category_theory.limits.is_image.self
- \+ *structure* category_theory.limits.is_image
- \+ *lemma* category_theory.limits.mono_factorisation.ext
- \+ *def* category_theory.limits.mono_factorisation.self
- \+ *structure* category_theory.limits.mono_factorisation



## [2020-03-09 12:22:18](https://github.com/leanprover-community/mathlib/commit/d8d0927)
refactor(topology/algebra/ordered): rename `tendsto_of_tendsto_of_tendsto_of_le_of_le` to `tendsto_of_tendsto_of_tendsto_of_le_of_le'` ([#2111](https://github.com/leanprover-community/mathlib/pull/2111))
The new `tendsto_of_tendsto_of_tendsto_of_le_of_le` assumes that
the inequalities hold everywhere.
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_of_tendsto_of_tendsto_of_le_of_le'

Modified src/topology/metric_space/basic.lean




## [2020-03-09 10:19:36](https://github.com/leanprover-community/mathlib/commit/4258f5e)
refactor(analysis/normed_space/banach): use bundled `→L[𝕜]` maps ([#2107](https://github.com/leanprover-community/mathlib/pull/2107))
#### Estimated changes
Modified src/analysis/normed_space/banach.lean
- \+/\- *lemma* exists_approx_preimage_norm_le
- \+/\- *theorem* exists_preimage_norm_le
- \+ *theorem* linear_equiv.continuous_symm
- \- *theorem* linear_equiv.is_bounded_inv
- \+/\- *theorem* open_mapping



## [2020-03-09 07:16:17](https://github.com/leanprover-community/mathlib/commit/434b629)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-09 05:00:06](https://github.com/leanprover-community/mathlib/commit/ce7248a)
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
#### Estimated changes
Added docs/tutorial/category_theory/intro.lean




## [2020-03-09 02:49:14](https://github.com/leanprover-community/mathlib/commit/61d70ce)
chore(algebra/group): streamlining imports ([#2099](https://github.com/leanprover-community/mathlib/pull/2099))
* chore(algebra/group): streamlining imports
* reducing imports
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/char_zero.lean


Modified src/algebra/group_power.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/pi_instances.lean


Modified src/algebra/punit_instances.lean


Modified src/algebra/ring.lean


Modified src/group_theory/free_group.lean




## [2020-03-09 00:56:10](https://github.com/leanprover-community/mathlib/commit/ca370cb)
fix(deprecated/group): remove dangerous instances ([#2096](https://github.com/leanprover-community/mathlib/pull/2096))
#### Estimated changes
Modified src/deprecated/group.lean
- \+ *lemma* additive.is_add_group_hom
- \+ *lemma* additive.is_add_hom
- \+ *lemma* additive.is_add_monoid_hom
- \+ *lemma* multiplicative.is_group_hom
- \+ *lemma* multiplicative.is_monoid_hom
- \+ *lemma* multiplicative.is_mul_hom

Modified src/group_theory/quotient_group.lean


Modified src/group_theory/subgroup.lean
- \+ *lemma* additive.is_add_subgroup
- \+ *lemma* additive.normal_add_subgroup
- \+/\- *def* is_group_hom.ker
- \+/\- *lemma* is_group_hom.mem_ker
- \+ *lemma* multiplicative.is_subgroup
- \+ *lemma* multiplicative.normal_subgroup



## [2020-03-08 22:46:03](https://github.com/leanprover-community/mathlib/commit/15d3268)
chore(category_theory/functor): make arguments implicit ([#2103](https://github.com/leanprover-community/mathlib/pull/2103))
#### Estimated changes
Modified src/category_theory/functor.lean
- \+/\- *lemma* category_theory.functor.comp_map



## [2020-03-08 05:53:07](https://github.com/leanprover-community/mathlib/commit/b7444b0)
Remove limits.lean which is superseded by limits_of_products_and_equalizers.lean ([#2105](https://github.com/leanprover-community/mathlib/pull/2105))
#### Estimated changes
Deleted src/category_theory/limits/shapes/constructions/limits.lean




## [2020-03-07 21:37:38](https://github.com/leanprover-community/mathlib/commit/d53bbb6)
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
#### Estimated changes
Modified docs/tactics.md


Modified src/data/fin.lean


Added src/data/fin_enum.lean
- \+ *def* fin_enum.finset.enum
- \+ *lemma* fin_enum.finset.mem_enum
- \+ *lemma* fin_enum.mem_pi
- \+ *lemma* fin_enum.mem_to_list
- \+ *lemma* fin_enum.nodup_to_list
- \+ *def* fin_enum.of_equiv
- \+ *def* fin_enum.of_list
- \+ *def* fin_enum.of_nodup_list
- \+ *def* fin_enum.of_surjective
- \+ *def* fin_enum.pi.cons
- \+ *def* fin_enum.pi.enum
- \+ *lemma* fin_enum.pi.mem_enum
- \+ *def* fin_enum.pi.tail
- \+ *def* fin_enum.pi
- \+ *def* fin_enum.to_list

Modified src/data/finset.lean
- \+ *theorem* finset.sdiff_empty
- \+ *theorem* finset.sdiff_eq_self
- \+ *theorem* finset.sdiff_inter_distrib_right
- \+ *theorem* finset.sdiff_inter_self_left
- \+ *theorem* finset.sdiff_inter_self_right
- \+ *theorem* finset.sdiff_self
- \+ *theorem* finset.sdiff_subset_self
- \+ *theorem* finset.superset.trans

Modified src/data/list/basic.lean
- \+ *theorem* list.mem_pure

Modified src/tactic/monotonicity/interactive.lean




## [2020-03-07 02:22:02](https://github.com/leanprover-community/mathlib/commit/726d83f)
feat(lint): add two new linters ([#2089](https://github.com/leanprover-community/mathlib/pull/2089))
* feat(lint): add two new linters
checks whether type-class inference searches end relatively quickly
checks that there are no instances has_coe a t with variable a
* remove `is_fast` from `has_coe_variable`
* add link to note
* typo in priority
* fix error, implement comments
#### Estimated changes
Modified docs/commands.md


Modified src/tactic/core.lean


Modified src/tactic/lint.lean


Modified test/lint.lean
- \+ *def* dangerous_instance_test
- \+ *def* foo_has_mul
- \+ *def* foo_instance
- \+ *def* impossible_instance_test



## [2020-03-07 00:15:07](https://github.com/leanprover-community/mathlib/commit/c5437b4)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-06 21:32:35](https://github.com/leanprover-community/mathlib/commit/6c23bad)
feat(data/set/lattice): add @[simp] to lemmas ([#2091](https://github.com/leanprover-community/mathlib/pull/2091))
* feat(data/set/lattice): add @[simp] to lemmas
* fix proof
* fix proof
* fix proof
* oops
* fix proofs
* typo in doc string
#### Estimated changes
Modified src/data/set/finite.lean


Modified src/data/set/lattice.lean
- \+/\- *lemma* set.bInter_image
- \+/\- *lemma* set.bInter_range
- \+/\- *lemma* set.bUnion_image
- \+/\- *lemma* set.bUnion_range

Modified src/measure_theory/integration.lean


Modified src/topology/instances/real.lean


Modified src/topology/uniform_space/cauchy.lean




## [2020-03-06 19:21:21](https://github.com/leanprover-community/mathlib/commit/4f10d1e)
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
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* inv_unique

Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.exists_inv_of_comp_exists_inv

Modified src/algebra/group/is_unit.lean
- \+/\- *lemma* is_unit.coe_lift_right
- \+/\- *lemma* is_unit.map
- \+/\- *theorem* is_unit_iff_exists_inv'
- \+/\- *theorem* is_unit_iff_exists_inv
- \+/\- *theorem* is_unit_of_mul_is_unit_right
- \+/\- *theorem* is_unit_of_mul_one
- \+/\- *theorem* is_unit_one
- \+/\- *lemma* is_unit_unit
- \+/\- *theorem* units.is_unit_mul_units

Modified src/algebra/group/units.lean
- \+ *structure* add_units
- \+ *theorem* nat.add_units_eq_one
- \+/\- *lemma* units.coe_inv
- \+/\- *lemma* units.coe_mk_of_mul_eq_one
- \+/\- *lemma* units.coe_mul
- \+/\- *lemma* units.coe_one
- \+/\- *theorem* units.eq_inv_mul_iff_mul_eq
- \+/\- *theorem* units.eq_mul_inv_iff_mul_eq
- \+/\- *theorem* units.ext
- \+/\- *theorem* units.ext_iff
- \+/\- *lemma* units.inv_mul
- \+/\- *lemma* units.inv_mul_cancel_left
- \+/\- *lemma* units.inv_mul_cancel_right
- \+/\- *theorem* units.inv_mul_eq_iff_eq_mul
- \+/\- *def* units.mk_of_mul_eq_one
- \+/\- *lemma* units.mul_inv
- \+/\- *lemma* units.mul_inv_cancel_left
- \+/\- *lemma* units.mul_inv_cancel_right
- \+/\- *theorem* units.mul_inv_eq_iff_eq_mul
- \+/\- *theorem* units.mul_left_inj
- \+/\- *theorem* units.mul_right_inj
- \+/\- *lemma* units.val_coe

Modified src/algebra/group/units_hom.lean
- \+/\- *lemma* units.coe_hom_apply
- \+/\- *lemma* units.coe_lift_right
- \+/\- *lemma* units.coe_map
- \+/\- *lemma* units.map_comp
- \+/\- *lemma* units.map_id

Modified src/algebra/pi_instances.lean
- \+ *def* prod.monoid_hom.inl
- \+ *def* prod.monoid_hom.inr

Modified src/group_theory/monoid_localization.lean
- \+ *structure* add_submonoid.localization_map
- \- *lemma* add_submonoid.r'.add
- \- *lemma* add_submonoid.r'.transitive
- \- *def* add_submonoid.r'
- \- *def* monoid_localization.aux
- \- *lemma* monoid_localization.exists_rep
- \- *lemma* monoid_localization.funext
- \- *theorem* monoid_localization.ind
- \- *theorem* monoid_localization.induction_on
- \- *lemma* monoid_localization.is_unit_of_of_comp
- \- *def* monoid_localization.lift'
- \- *lemma* monoid_localization.lift'_apply_of
- \- *lemma* monoid_localization.lift'_comp_of
- \- *lemma* monoid_localization.lift'_eq_iff
- \- *lemma* monoid_localization.lift'_mk
- \- *lemma* monoid_localization.lift'_of
- \- *lemma* monoid_localization.lift_apply_of
- \- *lemma* monoid_localization.lift_comp_of
- \- *lemma* monoid_localization.lift_eq_iff
- \- *lemma* monoid_localization.lift_mk
- \- *lemma* monoid_localization.lift_of
- \- *lemma* monoid_localization.lift_on_beta
- \- *def* monoid_localization.map
- \- *lemma* monoid_localization.map_comp_map
- \- *lemma* monoid_localization.map_comp_of
- \- *lemma* monoid_localization.map_eq
- \- *lemma* monoid_localization.map_ext
- \- *lemma* monoid_localization.map_id
- \- *lemma* monoid_localization.map_map
- \- *lemma* monoid_localization.map_mk
- \- *lemma* monoid_localization.map_of
- \- *def* monoid_localization.mk
- \- *lemma* monoid_localization.mk_eq
- \- *lemma* monoid_localization.mk_eq_iff_of_eq
- \- *lemma* monoid_localization.mk_eq_mul_mk_one
- \- *lemma* monoid_localization.mk_eq_of_eq
- \- *lemma* monoid_localization.mk_is_unit'
- \- *lemma* monoid_localization.mk_is_unit
- \- *lemma* monoid_localization.mk_mul_cancel_left
- \- *lemma* monoid_localization.mk_mul_cancel_right
- \- *lemma* monoid_localization.mk_mul_mk
- \- *lemma* monoid_localization.mk_self'
- \- *lemma* monoid_localization.mk_self
- \- *def* monoid_localization.of
- \- *lemma* monoid_localization.of_eq_mk
- \- *lemma* monoid_localization.of_is_unit'
- \- *lemma* monoid_localization.of_is_unit
- \- *lemma* monoid_localization.of_ker_iff
- \- *lemma* monoid_localization.of_mul_mk
- \- *lemma* monoid_localization.one_rel
- \- *lemma* monoid_localization.r_le_ker_aux
- \- *def* monoid_localization.to_units
- \- *lemma* monoid_localization.to_units_inv
- \- *lemma* monoid_localization.to_units_map_inv
- \- *lemma* monoid_localization.to_units_mk
- \- *def* monoid_localization.units_restrict
- \- *lemma* monoid_localization.units_restrict_mul
- \- *def* monoid_localization
- \+ *def* submonoid.localization.r'
- \+ *def* submonoid.localization.r
- \+ *theorem* submonoid.localization.r_eq_r'
- \+ *lemma* submonoid.localization.r_iff_exists
- \+ *def* submonoid.localization
- \+ *lemma* submonoid.localization_map.eq_iff_eq
- \+ *theorem* submonoid.localization_map.eq_mk'_iff_mul_eq
- \+ *lemma* submonoid.localization_map.exists_of_sec
- \+ *lemma* submonoid.localization_map.exists_of_sec_mk'
- \+ *lemma* submonoid.localization_map.inv_inj
- \+ *lemma* submonoid.localization_map.inv_unique
- \+ *lemma* submonoid.localization_map.mk'_eq_iff_eq
- \+ *theorem* submonoid.localization_map.mk'_eq_iff_eq_mul
- \+ *lemma* submonoid.localization_map.mk'_eq_iff_mk'_eq
- \+ *lemma* submonoid.localization_map.mk'_eq_of_eq
- \+ *lemma* submonoid.localization_map.mk'_mul
- \+ *lemma* submonoid.localization_map.mk'_mul_cancel_left
- \+ *lemma* submonoid.localization_map.mk'_mul_cancel_right
- \+ *lemma* submonoid.localization_map.mk'_mul_eq_mk'_of_mul
- \+ *lemma* submonoid.localization_map.mk'_one
- \+ *lemma* submonoid.localization_map.mk'_sec
- \+ *lemma* submonoid.localization_map.mk'_self'
- \+ *lemma* submonoid.localization_map.mk'_self
- \+ *lemma* submonoid.localization_map.mk'_spec'
- \+ *lemma* submonoid.localization_map.mk'_spec
- \+ *lemma* submonoid.localization_map.mk'_surjective
- \+ *lemma* submonoid.localization_map.mul_inv
- \+ *lemma* submonoid.localization_map.mul_inv_left
- \+ *lemma* submonoid.localization_map.mul_inv_right
- \+ *lemma* submonoid.localization_map.mul_mk'_eq_mk'_of_mul
- \+ *lemma* submonoid.localization_map.mul_mk'_one_eq_mk'
- \+ *lemma* submonoid.localization_map.sec_spec'
- \+ *lemma* submonoid.localization_map.sec_spec
- \+ *structure* submonoid.localization_map
- \- *def* submonoid.r'
- \- *def* submonoid.r
- \- *theorem* submonoid.r_eq_r'

Modified src/group_theory/submonoid.lean
- \+ *def* monoid_hom.restrict



## [2020-03-06 11:43:23](https://github.com/leanprover-community/mathlib/commit/36b336c)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-06 09:04:50](https://github.com/leanprover-community/mathlib/commit/8fb9881)
fix(category_theory/limits): Add some missing instances for special shapes of limits ([#2083](https://github.com/leanprover-community/mathlib/pull/2083))
* Add some instances for limit shapes
* Deduce has_(equalizers|kernels|pullbacks) from has_finite_limits
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.has_coequalizers_of_has_finite_colimits
- \+ *def* category_theory.limits.has_equalizers_of_has_finite_limits
- \+/\- *inductive* category_theory.limits.walking_parallel_pair_hom

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.has_cokernels_of_has_finite_colimits
- \+ *def* category_theory.limits.has_kernels_of_has_finite_limits

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* category_theory.limits.has_pullbacks_of_has_finite_limits
- \+ *def* category_theory.limits.has_pushouts_of_has_finite_colimits
- \+/\- *inductive* category_theory.limits.walking_cospan.hom
- \+/\- *inductive* category_theory.limits.walking_span.hom



## [2020-03-06 06:56:58](https://github.com/leanprover-community/mathlib/commit/f81f861)
feat(category_theory/limits): the kernel of the cokernel of an epimorphism is an isomorphism ([#2088](https://github.com/leanprover-community/mathlib/pull/2088))
* The kernel of the cokernel of an epimorphism is an isomorphism
* Fix unused argument warnings
* Remove a set_option
* Fix a typo
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.cocone_parallel_pair_ext
- \+ *lemma* category_theory.limits.cocone_parallel_pair_left
- \+ *lemma* category_theory.limits.cocone_parallel_pair_right
- \+ *def* category_theory.limits.cocone_parallel_pair_self
- \+ *lemma* category_theory.limits.cocone_parallel_pair_self_X
- \+ *lemma* category_theory.limits.cocone_parallel_pair_self_ι_app_one
- \+ *lemma* category_theory.limits.coequalizer.hom_ext
- \+ *lemma* category_theory.limits.coequalizer.π.cofork
- \+ *lemma* category_theory.limits.coequalizer.π.eq_app_one
- \+ *lemma* category_theory.limits.coequalizer.π_epi
- \+ *def* category_theory.limits.coequalizer.π_of_self'
- \+ *def* category_theory.limits.coequalizer.π_of_self
- \+ *lemma* category_theory.limits.cofork.eq_of_π_π
- \+ *def* category_theory.limits.colimit_cocone_parallel_pair_self_is_iso'
- \+ *def* category_theory.limits.colimit_cocone_parallel_pair_self_is_iso
- \+ *def* category_theory.limits.equalizer.ι_of_self'
- \+ *def* category_theory.limits.equalizer.ι_of_self
- \+ *def* category_theory.limits.is_colimit_cocone_parallel_pair_self
- \+ *def* category_theory.limits.limit_cone_parallel_pair_self_is_iso'
- \+ *def* category_theory.limits.mono_limit_cocone_parallel_pair_is_iso

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.cokernel.is_colimit_cocone_zero_cocone
- \+ *def* category_theory.limits.cokernel.of_epi
- \+ *def* category_theory.limits.cokernel.of_kernel_of_mono
- \+ *def* category_theory.limits.cokernel.zero_cocone
- \+ *lemma* category_theory.limits.cokernel.π_of_epi
- \+ *def* category_theory.limits.cokernel.π_of_zero
- \+ *def* category_theory.limits.kernel.of_cokernel_of_epi
- \+ *def* category_theory.limits.kernel.of_mono
- \+ *lemma* category_theory.limits.kernel.ι_of_mono
- \+ *def* category_theory.limits.kernel.ι_of_zero



## [2020-03-05 18:58:12-08:00](https://github.com/leanprover-community/mathlib/commit/0f9751c)
feat(data/traversable): improve support for instances for recursive types ([#2072](https://github.com/leanprover-community/mathlib/pull/2072))
#### Estimated changes
Modified src/category/traversable/derive.lean


Modified test/examples.lean
- \+ *def* ex
- \+ *inductive* my_tree
- \+ *def* x



## [2020-03-06 01:31:18](https://github.com/leanprover-community/mathlib/commit/093ac77)
feat(analysis/calculus/specific_functions): smoothness of exp(-1/x) ([#2087](https://github.com/leanprover-community/mathlib/pull/2087))
* feat(analysis/calculus/specific_functions): smoothness of exp(-1/x)
* use namespace; shorter names
* fix field_simp
#### Estimated changes
Modified src/algebra/field.lean
- \+ *lemma* div_sub'
- \+ *lemma* sub_div'

Added src/analysis/calculus/specific_functions.lean
- \+ *def* exp_neg_inv_glue.f_aux
- \+ *lemma* exp_neg_inv_glue.f_aux_deriv
- \+ *lemma* exp_neg_inv_glue.f_aux_deriv_pos
- \+ *lemma* exp_neg_inv_glue.f_aux_deriv_zero
- \+ *lemma* exp_neg_inv_glue.f_aux_has_deriv_at
- \+ *lemma* exp_neg_inv_glue.f_aux_iterated_deriv
- \+ *lemma* exp_neg_inv_glue.f_aux_limit
- \+ *lemma* exp_neg_inv_glue.f_aux_zero_eq
- \+ *lemma* exp_neg_inv_glue.nonneg
- \+ *lemma* exp_neg_inv_glue.pos_of_pos
- \+ *theorem* exp_neg_inv_glue.smooth
- \+ *lemma* exp_neg_inv_glue.zero_of_nonpos
- \+ *def* exp_neg_inv_glue

Modified test/ring.lean




## [2020-03-05 16:05:27](https://github.com/leanprover-community/mathlib/commit/50c4adf)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-05 13:17:04](https://github.com/leanprover-community/mathlib/commit/78ffbae)
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
#### Estimated changes
Modified archive/imo1988_q6.lean


Modified archive/sensitivity.lean


Modified docs/tutorial/Zmod37.lean


Modified leanpkg.toml


Modified scripts/nolints.txt


Modified src/algebra/archimedean.lean


Modified src/algebra/direct_limit.lean


Modified src/algebra/euclidean_domain.lean


Modified src/algebra/field.lean
- \- *lemma* div_div_cancel
- \- *lemma* div_div_div_cancel_right
- \+/\- *lemma* div_neg
- \- *lemma* div_right_comm
- \+/\- *lemma* division_ring.inv_eq_iff
- \+/\- *lemma* division_ring.inv_inj
- \+/\- *lemma* field.div_div_cancel
- \+/\- *lemma* field.div_div_div_cancel_right
- \+/\- *lemma* field.div_right_comm
- \+/\- *lemma* inv_div
- \+/\- *lemma* inv_div_left
- \+ *lemma* inv_inv''
- \- *theorem* inv_inv'
- \+/\- *lemma* inv_involutive'
- \+/\- *lemma* neg_inv

Modified src/algebra/field_power.lean
- \+/\- *lemma* is_ring_hom.map_fpow
- \+/\- *lemma* ring_hom.map_fpow

Modified src/algebra/floor.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/group/basic.lean
- \+/\- *lemma* neg_sub_neg
- \+ *lemma* sub_eq_sub_iff_add_eq_add

Modified src/algebra/group_power.lean
- \+/\- *theorem* div_pow
- \+/\- *theorem* division_ring.inv_pow
- \+/\- *lemma* inv_pow'
- \+/\- *theorem* one_div_pow
- \+/\- *lemma* pow_div

Modified src/algebra/lie_algebra.lean


Modified src/algebra/module.lean
- \+/\- *lemma* submodule.coe_sub
- \+/\- *abbreviation* vector_space

Modified src/algebra/opposites.lean


Modified src/algebra/order_functions.lean


Modified src/algebra/ordered_field.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_ring.lean
- \+ *def* linear_nonneg_ring.to_decidable_linear_ordered_comm_ring

Modified src/algebra/pi_instances.lean
- \+ *lemma* pi.sub_apply
- \+ *lemma* prod.fst_sub
- \+ *lemma* prod.snd_sub

Modified src/algebra/pointwise.lean


Modified src/algebra/quadratic_discriminant.lean


Modified src/algebra/ring.lean


Modified src/analysis/asymptotics.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/complex/basic.lean


Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* real.arcsin_eq_pi_div_two_sub_arccos

Modified src/analysis/complex/polynomial.lean


Modified src/analysis/convex/topology.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/specific_limits.lean


Modified src/computability/partrec_code.lean


Modified src/computability/primrec.lean


Modified src/computability/turing_machine.lean


Modified src/data/array/lemmas.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/dfinsupp.lean


Modified src/data/equiv/algebra.lean


Modified src/data/equiv/list.lean


Modified src/data/finset.lean
- \- *theorem* finset.has_insert_eq_insert

Modified src/data/finsupp.lean


Modified src/data/fintype.lean


Modified src/data/fp/basic.lean


Modified src/data/hash_map.lean


Modified src/data/holor.lean


Modified src/data/int/basic.lean


Modified src/data/int/gcd.lean


Modified src/data/int/modeq.lean


Modified src/data/int/parity.lean


Modified src/data/list/basic.lean
- \+/\- *theorem* list.mem_enum_from

Modified src/data/list/perm.lean


Modified src/data/multiset.lean


Modified src/data/mv_polynomial.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/cast.lean


Modified src/data/nat/dist.lean


Modified src/data/nat/enat.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/pairing.lean


Modified src/data/nat/sqrt.lean


Modified src/data/num/lemmas.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/polynomial.lean
- \+/\- *lemma* polynomial.degree_map
- \+/\- *lemma* polynomial.leading_coeff_map
- \+/\- *lemma* polynomial.map_div
- \+/\- *lemma* polynomial.map_eq_zero
- \+/\- *lemma* polynomial.map_mod
- \+/\- *lemma* polynomial.nat_degree_map

Modified src/data/rat/basic.lean


Modified src/data/rat/cast.lean
- \+/\- *theorem* rat.cast_div
- \+/\- *theorem* rat.cast_inv
- \+/\- *theorem* rat.cast_mk
- \+/\- *theorem* rat.cast_pow

Modified src/data/rat/order.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/hyperreal.lean
- \+/\- *lemma* hyperreal.inv_epsilon_eq_omega

Modified src/data/real/irrational.lean


Modified src/data/real/nnreal.lean
- \+/\- *lemma* nnreal.inv_inv

Modified src/data/real/pi.lean


Modified src/data/set/basic.lean
- \- *theorem* set.insert_of_has_insert

Modified src/data/set/enumerate.lean


Modified src/data/set/lattice.lean


Modified src/data/zmod/basic.lean


Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/data/zsqrtd/basic.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/finite.lean
- \+/\- *lemma* finite_field.pow_card_sub_one_eq_one

Modified src/field_theory/finite_card.lean


Modified src/field_theory/minimal_polynomial.lean


Modified src/field_theory/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.is_basis_monomials
- \+/\- *lemma* mv_polynomial.mem_restrict_degree
- \+/\- *lemma* mv_polynomial.mem_restrict_degree_iff_sup
- \+/\- *def* mv_polynomial.restrict_degree

Modified src/field_theory/perfect_closure.lean
- \+/\- *def* perfect_closure.UMP
- \+/\- *theorem* perfect_closure.eq_pth_root

Modified src/field_theory/splitting_field.lean


Modified src/field_theory/subfield.lean


Modified src/geometry/manifold/real_instances.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/order_of_element.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/contraction.lean


Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_of_field

Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* finite_dimensional.dim_lt_omega
- \+/\- *lemma* finite_dimensional.findim_eq_dim
- \+/\- *def* finite_dimensional

Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/matrix.lean
- \+/\- *lemma* matrix.rank_diagonal

Modified src/linear_algebra/multilinear.lean


Modified src/linear_algebra/sesquilinear_form.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/number_theory/dioph.lean


Modified src/number_theory/pell.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/order/filter/filter_product.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/ideals.lean
- \+/\- *lemma* ideal.eq_bot_of_prime
- \+/\- *lemma* ideal.eq_bot_or_top

Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/power_series.lean


Modified src/set_theory/lists.lean


Modified src/tactic/abel.lean


Modified src/tactic/algebra.lean


Modified src/tactic/linarith.lean


Modified src/tactic/lint.lean


Modified src/tactic/ring.lean


Modified src/tactic/ring2.lean


Modified src/tactic/ring_exp.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/multilinear.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/complex.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/isometry.lean


Modified src/topology/subset_properties.lean


Modified test/conv.lean


Modified test/monotonicity.lean


Modified test/ring_exp.lean




## [2020-03-05 00:24:49](https://github.com/leanprover-community/mathlib/commit/8535132)
refactor(algebra/lie_algebra): lie_algebra should not extend lie_ring ([#2084](https://github.com/leanprover-community/mathlib/pull/2084))
* refactor(algebra/lie_algebra): lie_algebra should not extend lie_ring
* Fix linting error ☺
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+/\- *lemma* lie_algebra.endo_algebra_bracket
- \+/\- *def* lie_algebra.of_associative_algebra
- \+/\- *lemma* lie_smul
- \+/\- *def* lie_subalgebra_lie_algebra
- \+ *def* lie_subalgebra_lie_ring
- \+ *def* matrix.lie_ring
- \+/\- *lemma* smul_lie

Modified src/algebra/ordered_group.lean
- \+/\- *lemma* add_neg_le_iff_le_add



## [2020-03-04 22:23:00](https://github.com/leanprover-community/mathlib/commit/7d6c4fb)
fix(congruence): use has_coe_t instead of has_coe ([#2086](https://github.com/leanprover-community/mathlib/pull/2086))
* fix(congruence): use has_coe_t instead of has_coe
* capitalization
Does that matter for doc generation?
#### Estimated changes
Modified src/group_theory/congruence.lean




## [2020-03-04 19:56:00](https://github.com/leanprover-community/mathlib/commit/9fc675c)
chore(analysis/normed_space/basic): rename `ne_mem_of_tendsto_norm_at_top` ([#2085](https://github.com/leanprover-community/mathlib/pull/2085))
It uses `∀ᶠ` now, so rename to `eventually_ne_of_tendsto_norm_at_top`.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* eventually_ne_of_tendsto_norm_at_top
- \- *lemma* ne_mem_of_tendsto_norm_at_top



## [2020-03-04 13:10:10](https://github.com/leanprover-community/mathlib/commit/f112408)
fix(ci): adjust conditions for fixing steps ([#2082](https://github.com/leanprover-community/mathlib/pull/2082))
* fix(ci): always run git setup step
closes [#2079](https://github.com/leanprover-community/mathlib/pull/2079)
* fix(ci): always test doc gen
documentation will still be pushed only under the same conditions as before
closes [#2081](https://github.com/leanprover-community/mathlib/pull/2081)
* Update scripts/deploy_docs.sh
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
#### Estimated changes
Modified .github/workflows/build.yml


Modified scripts/deploy_docs.sh




## [2020-03-04 07:09:20](https://github.com/leanprover-community/mathlib/commit/cc4ac8a)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-03 20:45:05-08:00](https://github.com/leanprover-community/mathlib/commit/0f1eb80)
fix(CI/documentation): add a name back
#### Estimated changes
Modified src/tactic/interactive.lean




## [2020-03-03 22:24:50](https://github.com/leanprover-community/mathlib/commit/13f04c0)
feat(tactic/extract_goal): improve formatting to put assumptions on their own line ([#2076](https://github.com/leanprover-community/mathlib/pull/2076))
#### Estimated changes
Modified src/tactic/interactive.lean




## [2020-03-03 20:14:28](https://github.com/leanprover-community/mathlib/commit/545dd03)
feat(topology/metric_space/antilipschitz): define `antilipschitz_with` ([#2075](https://github.com/leanprover-community/mathlib/pull/2075))
* chore(data/real/ennreal): weaker assumptions in `sub_mul`, add `coe_inv_le`
* feat(topology/metric_space/antilipschitz): define `antilipschitz_with`
Also make some proofs use facts about `antilipschitz_with`.
* Rename inequalities, move `K` to the other side
This way it's easier to glue it with the rest of the library, and
we can avoid assuming `0 < K` in many lemmas.
#### Estimated changes
Modified src/analysis/ODE/gronwall.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* abs_dist_sub_le_dist_add_add
- \+ *lemma* antilipschitz_with.add_lipschitz_with
- \+ *lemma* edist_add_add_le
- \+ *lemma* lipschitz_with.add
- \+ *lemma* lipschitz_with.neg
- \+ *lemma* lipschitz_with.sub
- \+ *lemma* nndist_add_add_le

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_equiv.antilipschitz
- \+ *lemma* continuous_linear_equiv.lipschitz
- \+ *lemma* continuous_linear_equiv.uniform_embedding
- \+ *theorem* continuous_linear_map.antilipschitz_of_uniform_embedding
- \- *theorem* continuous_linear_map.bound_of_uniform_embedding
- \+ *theorem* continuous_linear_map.op_norm_le_of_lipschitz
- \+/\- *theorem* continuous_linear_map.uniform_embedding_of_bound
- \+ *theorem* linear_map.antilipschitz_of_bound

Modified src/measure_theory/bochner_integration.lean


Modified src/topology/bounded_continuous_function.lean


Added src/topology/metric_space/antilipschitz.lean
- \+ *lemma* antilipschitz_with.comp
- \+ *lemma* antilipschitz_with.id
- \+ *lemma* antilipschitz_with.mul_le_dist
- \+ *lemma* antilipschitz_with.mul_le_edist
- \+ *lemma* antilipschitz_with.to_inverse
- \+ *lemma* antilipschitz_with.uniform_embedding
- \+ *def* antilipschitz_with
- \+ *lemma* antilipschitz_with_iff_le_mul_dist
- \+ *lemma* lipschitz_with.to_inverse

Modified src/topology/metric_space/contracting.lean
- \- *lemma* contracting_with.dist_le
- \+ *lemma* contracting_with.dist_le_mul

Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometry.antilipschitz
- \+/\- *lemma* isometry.injective
- \+ *lemma* isometry.lipschitz

Modified src/topology/metric_space/lipschitz.lean
- \- *lemma* lipschitz_with.edist_le
- \+ *lemma* lipschitz_with.edist_le_mul
- \+ *lemma* lipschitz_with.mul_edist_le
- \- *lemma* lipschitz_with_iff_dist_le
- \+ *lemma* lipschitz_with_iff_dist_le_mul



## [2020-03-03 14:39:18](https://github.com/leanprover-community/mathlib/commit/02d22c3)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-03 11:51:46](https://github.com/leanprover-community/mathlib/commit/f7e82d0)
feat(tactic/lint): check for redundant simp lemmas ([#2066](https://github.com/leanprover-community/mathlib/pull/2066))
* chore(*): fix simp lemmas
* feat(tactic/lint): check for redundant simp lemmas
#### Estimated changes
Modified docs/commands.md


Modified src/algebra/associated.lean
- \+/\- *lemma* dvd_mul_unit_iff
- \+/\- *lemma* mul_unit_dvd_iff

Modified src/algebra/big_operators.lean
- \+/\- *lemma* finset.prod_const_one
- \+/\- *lemma* finset.sum_const_zero

Modified src/algebra/category/Group.lean


Modified src/algebra/char_zero.lean
- \+/\- *theorem* nat.cast_ne_zero

Modified src/algebra/commute.lean
- \+/\- *theorem* commute.inv_left
- \+/\- *theorem* commute.inv_right
- \+/\- *theorem* commute.neg_left
- \+/\- *theorem* commute.neg_right
- \+/\- *theorem* commute.units_inv_left
- \+/\- *theorem* commute.units_inv_right

Modified src/algebra/free.lean
- \+/\- *lemma* free_semigroup.lift_of_mul

Modified src/algebra/group/basic.lean


Modified src/algebra/group_power.lean
- \+/\- *theorem* list.prod_repeat
- \+/\- *theorem* list.sum_repeat

Modified src/algebra/lie_algebra.lean
- \+ *lemma* lie_algebra.map_lie'
- \+/\- *lemma* lie_algebra.map_lie

Modified src/algebra/ring.lean
- \+/\- *lemma* ring_hom.comp_apply

Modified src/category_theory/discrete_category.lean
- \+/\- *lemma* category_theory.functor.of_function_map

Modified src/category_theory/functor_category.lean
- \+/\- *lemma* category_theory.nat_trans.vcomp_app'

Modified src/category_theory/monoidal/category.lean
- \+/\- *lemma* category_theory.monoidal_category.triangle_assoc_comp_left

Modified src/category_theory/natural_isomorphism.lean
- \+/\- *lemma* category_theory.nat_iso.app_hom
- \+/\- *lemma* category_theory.nat_iso.app_inv
- \+/\- *lemma* category_theory.nat_iso.hom_app_inv_app_id
- \+/\- *lemma* category_theory.nat_iso.inv_app_hom_app_id

Modified src/computability/partrec.lean
- \+/\- *theorem* nat.rfind_dom'

Modified src/data/bool.lean
- \+/\- *theorem* bool.coe_to_bool

Modified src/data/complex/basic.lean
- \+/\- *lemma* complex.abs_of_nat
- \+/\- *theorem* complex.of_real_ne_zero

Modified src/data/dfinsupp.lean
- \+/\- *lemma* dfinsupp.erase_ne
- \+/\- *lemma* dfinsupp.filter_apply_neg
- \+/\- *lemma* dfinsupp.filter_apply_pos
- \+/\- *lemma* dfinsupp.mem_support_iff
- \+/\- *lemma* dfinsupp.single_eq_of_ne

Modified src/data/equiv/algebra.lean
- \+/\- *lemma* equiv.coe_units_equiv_ne_zero

Modified src/data/equiv/denumerable.lean
- \+/\- *theorem* denumerable.decode_eq_of_nat

Modified src/data/fin.lean
- \+/\- *lemma* fin.mk_val

Modified src/data/finset.lean
- \+/\- *theorem* finset.image_val_of_inj_on
- \+/\- *theorem* finset.insert_empty_eq_singleton
- \+/\- *theorem* finset.mem_image_of_mem
- \+/\- *theorem* finset.mem_map_of_mem
- \+/\- *lemma* finset.piecewise_eq_of_mem
- \+/\- *lemma* finset.piecewise_eq_of_not_mem
- \+/\- *lemma* finset.piecewise_insert_of_ne
- \+/\- *theorem* finset.sdiff_union_of_subset
- \+/\- *theorem* finset.singleton_eq_singleton
- \+/\- *theorem* finset.union_sdiff_of_subset
- \+/\- *theorem* finset.union_self

Modified src/data/fintype.lean
- \+/\- *theorem* fintype.card_unit
- \+/\- *theorem* fintype.univ_unit

Modified src/data/int/basic.lean
- \+/\- *theorem* int.cast_ne_zero
- \+/\- *theorem* int.coe_nat_ne_zero
- \+/\- *theorem* int.mod_one
- \+/\- *theorem* int.mod_self
- \+/\- *theorem* int.mod_zero
- \+/\- *theorem* int.zero_mod

Modified src/data/int/gcd.lean


Modified src/data/list/basic.lean
- \+/\- *theorem* list.cons_inj'
- \+/\- *theorem* list.cons_ne_nil
- \+/\- *theorem* list.count_cons_of_ne
- \+/\- *theorem* list.count_eq_zero_of_not_mem
- \+/\- *theorem* list.disjoint_singleton
- \+/\- *theorem* list.erase_of_not_mem
- \+/\- *theorem* list.index_of_cons_ne
- \+/\- *theorem* list.index_of_of_not_mem
- \+/\- *theorem* list.insert_of_mem
- \+/\- *theorem* list.insert_of_not_mem
- \+/\- *theorem* list.mem_insert_of_mem
- \+/\- *theorem* list.mem_map_of_inj
- \+/\- *theorem* list.singleton_disjoint
- \+/\- *theorem* list.sublists'_singleton

Modified src/data/list/sigma.lean
- \+/\- *theorem* list.kerase_cons_eq
- \+/\- *theorem* list.kerase_cons_ne
- \+/\- *theorem* list.kerase_of_not_mem_keys
- \+/\- *theorem* list.mem_keys_kerase_of_ne

Modified src/data/list/sort.lean


Modified src/data/multiset.lean
- \+/\- *theorem* multiset.cons_erase
- \+/\- *theorem* multiset.cons_ndinter_of_mem
- \+/\- *theorem* multiset.count_cons_of_ne
- \+/\- *theorem* multiset.count_eq_zero_of_not_mem
- \+/\- *theorem* multiset.count_erase_of_ne
- \+/\- *theorem* multiset.disjoint_singleton
- \+/\- *theorem* multiset.erase_cons_tail
- \+/\- *theorem* multiset.erase_of_not_mem
- \- *theorem* multiset.forall_mem_ne
- \+/\- *theorem* multiset.length_ndinsert_of_mem
- \+/\- *theorem* multiset.length_ndinsert_of_not_mem
- \+/\- *theorem* multiset.map_id
- \+/\- *theorem* multiset.mem_map_of_inj
- \+/\- *theorem* multiset.mem_ndinsert_of_mem
- \+/\- *lemma* multiset.nat.nodup_antidiagonal
- \+/\- *theorem* multiset.ndinsert_of_mem
- \+/\- *theorem* multiset.ndinsert_of_not_mem
- \+/\- *theorem* multiset.ndinter_cons_of_not_mem
- \+/\- *theorem* multiset.ndinter_eq_inter
- \+/\- *theorem* multiset.ndunion_eq_union
- \+/\- *theorem* multiset.singleton_disjoint

Modified src/data/nat/basic.lean


Modified src/data/nat/enat.lean
- \+/\- *lemma* enat.coe_add_get
- \+ *lemma* enat.get_coe

Modified src/data/num/lemmas.lean
- \+/\- *theorem* num.add_to_nat
- \+/\- *theorem* num.cast_inj
- \+/\- *theorem* num.cast_le
- \+/\- *theorem* num.cast_lt
- \+/\- *theorem* num.dvd_to_nat
- \+/\- *theorem* num.land_to_nat
- \+/\- *theorem* num.ldiff_to_nat
- \+/\- *theorem* num.le_to_nat
- \+/\- *theorem* num.lor_to_nat
- \+/\- *theorem* num.lt_to_nat
- \+/\- *theorem* num.lxor_to_nat
- \+/\- *theorem* num.mul_to_nat
- \+/\- *theorem* num.of_nat_cast
- \+/\- *theorem* num.shiftl_to_nat
- \+/\- *theorem* num.shiftr_to_nat
- \+/\- *theorem* num.to_of_nat
- \+/\- *theorem* pos_num.add_to_nat
- \+/\- *theorem* pos_num.cast_add
- \+/\- *theorem* pos_num.cast_inj
- \+/\- *theorem* pos_num.cast_le
- \+/\- *theorem* pos_num.cast_lt
- \+/\- *theorem* pos_num.cast_mul
- \+/\- *theorem* pos_num.cast_succ
- \+/\- *theorem* pos_num.le_to_nat
- \+/\- *theorem* pos_num.lt_to_nat
- \+/\- *theorem* pos_num.mul_to_nat
- \+/\- *theorem* znum.cast_inj
- \+/\- *theorem* znum.cast_le
- \+/\- *theorem* znum.cast_lt
- \+/\- *theorem* znum.le_to_int
- \+/\- *theorem* znum.lt_to_int
- \+/\- *theorem* znum.to_of_int

Modified src/data/padics/padic_integers.lean
- \+/\- *lemma* padic_int.add_def
- \+/\- *lemma* padic_int.mul_def
- \+/\- *lemma* padic_norm_z.norm_one

Modified src/data/pequiv.lean


Modified src/data/pnat/basic.lean
- \+/\- *theorem* pnat.to_pnat'_coe

Modified src/data/polynomial.lean
- \+/\- *lemma* polynomial.coeff_C_mul_X
- \+/\- *lemma* polynomial.coeff_one

Modified src/data/rat/basic.lean


Modified src/data/rat/cast.lean
- \+/\- *theorem* rat.cast_ne_zero

Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.inv_le_inv
- \+/\- *lemma* ennreal.two_ne_top
- \+/\- *lemma* ennreal.two_ne_zero
- \+/\- *lemma* ennreal.zero_lt_coe_iff

Modified src/data/real/hyperreal.lean
- \+ *lemma* hyperreal.cast_div
- \+ *lemma* hyperreal.coe_abs
- \+ *lemma* hyperreal.coe_eq_coe
- \+ *lemma* hyperreal.coe_le_coe
- \+ *lemma* hyperreal.coe_lt_coe
- \+ *lemma* hyperreal.coe_max
- \+ *lemma* hyperreal.coe_min
- \+ *lemma* hyperreal.hyperfilter_ne_bot'
- \+ *lemma* hyperreal.hyperfilter_ne_bot

Modified src/data/real/nnreal.lean
- \+/\- *theorem* nnreal.coe_mk

Modified src/data/seq/seq.lean
- \+/\- *theorem* seq.join_cons

Modified src/data/set/basic.lean
- \+/\- *theorem* set.ball_image_iff
- \+/\- *theorem* set.compl_compl
- \+/\- *lemma* set.image_id'
- \+/\- *theorem* set.image_id
- \+/\- *theorem* set.insert_of_has_insert
- \- *lemma* set.set_of_mem
- \+/\- *lemma* subtype.range_val
- \+/\- *lemma* subtype.val_range

Modified src/data/set/function.lean
- \+/\- *lemma* set.piecewise_eq_of_mem
- \+/\- *lemma* set.piecewise_eq_of_not_mem
- \+/\- *lemma* set.piecewise_insert_of_ne

Modified src/data/set/lattice.lean
- \+/\- *theorem* set.mem_sUnion

Modified src/data/sigma/basic.lean
- \+/\- *theorem* sigma.mk.inj_iff

Modified src/data/subtype.lean
- \+/\- *theorem* subtype.mk_eq_mk

Modified src/data/sum.lean
- \+/\- *theorem* sum.inl.inj_iff
- \+/\- *theorem* sum.inl_ne_inr
- \+/\- *theorem* sum.inr.inj_iff
- \+/\- *theorem* sum.inr_ne_inl

Modified src/data/zmod/basic.lean
- \+/\- *lemma* zmod.cast_mod_int'
- \+/\- *lemma* zmod.cast_mod_nat'

Modified src/group_theory/perm/sign.lean
- \- *lemma* equiv.perm.swap_mul_self
- \- *lemma* equiv.perm.swap_swap_apply

Modified src/linear_algebra/basic.lean
- \+/\- *theorem* linear_equiv.map_ne_zero_iff

Modified src/linear_algebra/special_linear_group.lean
- \+/\- *lemma* matrix.special_linear_group.det_coe_fun

Modified src/logic/basic.lean
- \+/\- *theorem* coe_fn_coe_trans
- \+/\- *theorem* coe_sort_coe_trans
- \+/\- *theorem* false_ne_true
- \+/\- *theorem* imp_true_iff
- \+/\- *theorem* not_and_not_right

Modified src/order/complete_lattice.lean
- \+/\- *theorem* lattice.Inf_singleton
- \+/\- *theorem* lattice.Sup_singleton
- \+/\- *theorem* lattice.infi_const
- \- *theorem* lattice.insert_of_has_insert
- \+/\- *theorem* lattice.supr_const

Modified src/order/conditionally_complete_lattice.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.principal_ne_bot_iff

Modified src/order/filter/filter_product.lean
- \+ *lemma* filter.filter_product.coe_injective
- \+/\- *lemma* filter.filter_product.of_add
- \+ *lemma* filter.filter_product.of_bit0
- \+ *lemma* filter.filter_product.of_bit1
- \+/\- *lemma* filter.filter_product.of_div
- \+/\- *lemma* filter.filter_product.of_eq_zero
- \+/\- *lemma* filter.filter_product.of_inv
- \+/\- *lemma* filter.filter_product.of_mul
- \+/\- *lemma* filter.filter_product.of_ne_zero
- \+/\- *lemma* filter.filter_product.of_neg
- \+/\- *lemma* filter.filter_product.of_one
- \+/\- *lemma* filter.filter_product.of_sub
- \+/\- *lemma* filter.filter_product.of_zero

Modified src/ring_theory/localization.lean
- \+/\- *lemma* localization.fraction_ring.mk_eq_div
- \+/\- *lemma* localization.mk_mul_cancel_left
- \+/\- *lemma* localization.mk_mul_cancel_right
- \+/\- *lemma* localization.mk_self''
- \+/\- *lemma* localization.mk_self'
- \+/\- *lemma* localization.mk_self

Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/power_series.lean
- \+/\- *lemma* mv_power_series.coeff_zero_C
- \+/\- *lemma* mv_power_series.coeff_zero_X
- \+/\- *lemma* mv_power_series.coeff_zero_mul_X
- \+/\- *lemma* mv_power_series.coeff_zero_one
- \+/\- *lemma* mv_power_series.inv_of_unit_eq
- \+/\- *lemma* power_series.inv_of_unit_eq

Modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *theorem* associates.factor_set.coe_add

Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.mk_unit

Modified src/set_theory/ordinal.lean
- \+/\- *theorem* initial_seg.coe_coe_fn
- \+/\- *theorem* initial_seg.of_iso_apply
- \+/\- *theorem* ordinal.nat_cast_ne_zero
- \+/\- *theorem* ordinal.one_add_of_omega_le
- \+/\- *theorem* ordinal.type_ne_zero_iff_nonempty
- \+/\- *theorem* principal_seg.coe_coe_fn
- \+/\- *theorem* principal_seg.equiv_lt_apply
- \+/\- *theorem* principal_seg.lt_le_apply
- \+/\- *theorem* principal_seg.of_element_apply
- \+/\- *theorem* principal_seg.trans_apply
- \+/\- *theorem* principal_seg.trans_top

Modified src/set_theory/pgame.lean


Modified src/tactic/converter/binders.lean
- \- *theorem* mem_image

Modified src/tactic/lint.lean
- \+ *lemma* add_zero
- \+ *lemma* zero_add_zero

Modified src/topology/algebra/module.lean
- \+/\- *lemma* continuous_linear_map.id_apply
- \+ *lemma* continuous_linear_map.sub_apply'
- \+/\- *lemma* continuous_linear_map.sub_apply

Modified src/topology/category/Top/open_nhds.lean


Modified src/topology/category/Top/opens.lean


Modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *lemma* emetric.Hausdorff_edist_self_closure
- \+/\- *lemma* metric.Hausdorff_dist_self_closure

Modified src/topology/sheaves/presheaf.lean
- \+/\- *lemma* Top.presheaf.pushforward.id_hom_app

Modified test/lint_simp_nf.lean




## [2020-03-03 09:04:21](https://github.com/leanprover-community/mathlib/commit/2d1bd45)
fix some docstrings [ci skip] ([#2078](https://github.com/leanprover-community/mathlib/pull/2078))
#### Estimated changes
Modified src/category/monad/writer.lean


Modified src/category_theory/concrete_category/bundled_hom.lean




## [2020-03-03 07:18:28](https://github.com/leanprover-community/mathlib/commit/2a9ad03)
feat(data/list/basic): more lemmas about `list.chain'`; `chain'_of_pairwise` → `pairwise.chain'` ([#2071](https://github.com/leanprover-community/mathlib/pull/2071))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.chain'.cons
- \+ *theorem* list.chain'.tail
- \+ *theorem* list.chain'_cons
- \+ *theorem* list.chain'_nil
- \- *theorem* list.chain'_of_pairwise
- \+ *theorem* list.chain'_pair
- \+ *theorem* list.chain'_reverse
- \+/\- *theorem* list.chain'_singleton
- \+ *theorem* list.chain.imp'
- \+ *theorem* list.pairwise.chain'



## [2020-03-03 05:29:57](https://github.com/leanprover-community/mathlib/commit/e003014)
feat(analysis/calculus/iterated_deriv): iterated derivative of a function defined on the base field ([#2067](https://github.com/leanprover-community/mathlib/pull/2067))
* iterated deriv
* cleanup
* fix docstring
* add iterated_deriv_within_succ'
* remove n.succ
* n+1 -> n + 1
#### Estimated changes
Added src/analysis/calculus/iterated_deriv.lean
- \+ *def* iterated_deriv
- \+ *lemma* iterated_deriv_eq_equiv_comp
- \+ *lemma* iterated_deriv_eq_iterate
- \+ *lemma* iterated_deriv_eq_iterated_fderiv
- \+ *lemma* iterated_deriv_one
- \+ *lemma* iterated_deriv_succ'
- \+ *lemma* iterated_deriv_succ
- \+ *def* iterated_deriv_within
- \+ *lemma* iterated_deriv_within_eq_equiv_comp
- \+ *lemma* iterated_deriv_within_eq_iterate
- \+ *lemma* iterated_deriv_within_eq_iterated_fderiv_within
- \+ *lemma* iterated_deriv_within_one
- \+ *lemma* iterated_deriv_within_succ'
- \+ *lemma* iterated_deriv_within_succ
- \+ *lemma* iterated_deriv_within_univ
- \+ *lemma* iterated_deriv_within_zero
- \+ *lemma* iterated_deriv_zero
- \+ *lemma* iterated_fderiv_apply_eq_iterated_deriv_mul_prod
- \+ *lemma* iterated_fderiv_eq_equiv_comp
- \+ *lemma* iterated_fderiv_within_apply_eq_iterated_deriv_within_mul_prod
- \+ *lemma* iterated_fderiv_within_eq_equiv_comp
- \+ *lemma* times_cont_diff.continuous_iterated_deriv
- \+ *lemma* times_cont_diff.differentiable_iterated_deriv
- \+ *lemma* times_cont_diff_iff_iterated_deriv
- \+ *lemma* times_cont_diff_of_differentiable_iterated_deriv
- \+ *lemma* times_cont_diff_on.continuous_on_iterated_deriv_within
- \+ *lemma* times_cont_diff_on.differentiable_on_iterated_deriv_within
- \+ *lemma* times_cont_diff_on_iff_continuous_on_differentiable_on_deriv
- \+ *lemma* times_cont_diff_on_of_continuous_on_differentiable_on_deriv
- \+ *lemma* times_cont_diff_on_of_differentiable_on_deriv

Modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* iterated_fderiv_succ_apply_left
- \+/\- *theorem* iterated_fderiv_succ_apply_right
- \+/\- *lemma* iterated_fderiv_within_succ_apply_left



## [2020-03-03 00:17:40](https://github.com/leanprover-community/mathlib/commit/262a39e)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-03-02 21:45:35](https://github.com/leanprover-community/mathlib/commit/fe9d7ff)
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
#### Estimated changes
Modified docs/tactics.md


Modified src/algebra/ordered_group.lean
- \+/\- *lemma* bot_eq_zero

Modified src/data/finset.lean
- \+/\- *lemma* finset.Ico_ℤ.mem

Modified src/data/fintype/intervals.lean


Modified src/data/list/basic.lean
- \+ *lemma* list.Ico.trichotomy

Modified src/data/nat/basic.lean
- \+ *lemma* nat.add_one_le_iff
- \+ *lemma* nat.one_add_le_iff
- \+ *lemma* nat.pos_of_bit0_pos

Modified src/data/pnat/basic.lean
- \+ *theorem* pnat.add_one_le_iff
- \+ *lemma* pnat.bit0_le_bit0
- \+ *lemma* pnat.bit0_le_bit1
- \+ *lemma* pnat.bit1_le_bit0
- \+ *lemma* pnat.bit1_le_bit1
- \+ *lemma* pnat.bot_eq_zero
- \+ *theorem* pnat.lt_add_one_iff
- \+ *lemma* pnat.mk_bit0
- \+ *lemma* pnat.mk_bit1
- \+ *lemma* pnat.mk_one
- \+ *lemma* pnat.one_le

Added src/data/pnat/intervals.lean
- \+ *lemma* pnat.Ico.mem
- \+ *def* pnat.Ico

Modified src/tactic/default.lean


Modified src/tactic/fin_cases.lean


Added src/tactic/interval_cases.lean
- \+ *lemma* tactic.interval_cases.mem_set_elems
- \+ *def* tactic.interval_cases.set_elems

Modified test/fin_cases.lean


Added test/interval_cases.lean




## [2020-03-02 19:54:08](https://github.com/leanprover-community/mathlib/commit/1d82a7c)
doc(data/fin): add docs; fin_zero_elim -> fin.elim0; fin_zero_elim' -> fin_zero_elim ([#2055](https://github.com/leanprover-community/mathlib/pull/2055))
* doc(data/fin): add some docs
Also drom `fin_zero_elim` in favor of `fin.elim0` from `stdlib` and
rename `fin_zero_elim'` to `fin_zero_elim`.
* Update src/data/fin.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update docs, fix `Π` vs `∀`.
#### Estimated changes
Modified src/data/fin.lean
- \- *def* fin_zero_elim'
- \+/\- *def* fin_zero_elim



## [2020-03-02 18:11:18](https://github.com/leanprover-community/mathlib/commit/8919541)
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
#### Estimated changes
Modified src/data/finset.lean
- \+/\- *theorem* finset.le_max'
- \+/\- *theorem* finset.le_min'
- \+ *lemma* finset.left_eq_union_iff_subset
- \+/\- *def* finset.max'
- \+/\- *theorem* finset.max'_le
- \+/\- *theorem* finset.max'_mem
- \+/\- *def* finset.min'
- \+/\- *theorem* finset.min'_le
- \+/\- *theorem* finset.min'_lt_max'
- \+/\- *theorem* finset.min'_mem
- \+ *lemma* finset.pi_disjoint_of_disjoint
- \+ *lemma* finset.pi_subset
- \+ *lemma* finset.right_eq_union_iff_subset
- \+ *lemma* finset.sdiff_subset
- \+ *lemma* finset.singleton_subset_iff
- \+ *lemma* finset.union_eq_left_iff_subset
- \+ *lemma* finset.union_eq_right_iff_subset

Modified src/data/fintype.lean
- \+ *lemma* finset.card_le_one_iff
- \+ *lemma* finset.one_lt_card_iff
- \+ *lemma* fintype.mem_pi_finset
- \+ *def* fintype.pi_finset
- \+ *lemma* fintype.pi_finset_disjoint_of_disjoint
- \+ *lemma* fintype.pi_finset_subset
- \+ *lemma* fintype.pi_finset_univ

Modified src/data/fintype/card.lean
- \+ *lemma* fintype.card_pi_finset

Modified src/measure_theory/integration.lean




## [2020-03-02 16:19:30](https://github.com/leanprover-community/mathlib/commit/62756bd)
chore(data/real/ennreal): weaker assumptions in `sub_mul`, add `coe_inv_le` ([#2074](https://github.com/leanprover-community/mathlib/pull/2074))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.coe_inv_le
- \+/\- *lemma* ennreal.mul_sub
- \+/\- *lemma* ennreal.sub_mul
- \+ *lemma* ennreal.sub_mul_ge



## [2020-03-02 14:25:59](https://github.com/leanprover-community/mathlib/commit/bfbd093)
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
#### Estimated changes
Modified src/algebra/group/conj.lean


Modified src/algebra/group/hom.lean
- \- *lemma* inv.is_group_hom
- \- *lemma* is_add_group_hom.map_sub
- \- *lemma* is_add_group_hom.sub
- \- *lemma* is_group_hom.injective_iff
- \- *lemma* is_group_hom.inv
- \- *theorem* is_group_hom.map_inv
- \- *lemma* is_group_hom.map_one
- \- *lemma* is_group_hom.mk'
- \- *lemma* is_group_hom.mul
- \- *lemma* is_monoid_hom.map_mul
- \- *theorem* is_monoid_hom.of_mul
- \- *lemma* is_mul_hom.inv
- \- *lemma* is_mul_hom.mul
- \- *lemma* monoid_hom.coe_of
- \- *def* monoid_hom.of

Modified src/algebra/group/is_unit.lean
- \- *lemma* is_unit.map'

Modified src/algebra/group/type_tags.lean


Modified src/algebra/group/units_hom.lean
- \- *lemma* units.coe_map'
- \- *def* units.map'

Modified src/algebra/group/with_one.lean
- \+/\- *def* with_one.lift
- \+/\- *lemma* with_one.lift_coe
- \+/\- *lemma* with_one.lift_one
- \+/\- *theorem* with_one.lift_unique
- \+/\- *def* with_one.map
- \- *lemma* with_one.map_eq

Modified src/algebra/ring.lean


Added src/deprecated/group.lean
- \+ *lemma* inv.is_group_hom
- \+ *lemma* is_add_group_hom.map_sub
- \+ *lemma* is_add_group_hom.sub
- \+ *lemma* is_group_hom.injective_iff
- \+ *lemma* is_group_hom.inv
- \+ *theorem* is_group_hom.map_inv
- \+ *lemma* is_group_hom.map_one
- \+ *lemma* is_group_hom.mk'
- \+ *lemma* is_group_hom.mul
- \+ *lemma* is_monoid_hom.map_mul
- \+ *theorem* is_monoid_hom.of_mul
- \+ *lemma* is_mul_hom.inv
- \+ *lemma* is_mul_hom.mul
- \+ *lemma* is_unit.map'
- \+ *lemma* monoid_hom.coe_of
- \+ *def* monoid_hom.of
- \+ *lemma* units.coe_map'
- \+ *def* units.map'

Modified src/group_theory/perm/sign.lean




## [2020-03-02 12:33:13](https://github.com/leanprover-community/mathlib/commit/3055b3c)
chore(topology/metric_space/isometry): rename `(e)metric.isometry.diam_image` to `isometry.(e)diam_image` ([#2073](https://github.com/leanprover-community/mathlib/pull/2073))
This way we can use dot notation to access these lemmas. Also add `(e)diam_range`.
#### Estimated changes
Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/isometry.lean
- \- *lemma* emetric.isometry.diam_image
- \+ *lemma* isometry.diam_image
- \+ *lemma* isometry.diam_range
- \+ *lemma* isometry.ediam_image
- \+ *lemma* isometry.ediam_range
- \- *lemma* metric.isometry.diam_image



## [2020-03-02 10:42:53](https://github.com/leanprover-community/mathlib/commit/2683fa0)
feat(order/galois_connection): lemmas about galois insertions and supr/infi ([#2052](https://github.com/leanprover-community/mathlib/pull/2052))
* feat(order/galois_connection): lemmas about galois insertions and supr/infi
* Fix build, hopefully
#### Estimated changes
Modified src/order/galois_connection.lean
- \+ *lemma* galois_insertion.l_inf_u
- \+ *lemma* galois_insertion.l_infi_of_ul
- \+ *lemma* galois_insertion.l_infi_u
- \+ *lemma* galois_insertion.l_sup_u
- \+ *lemma* galois_insertion.l_supr_of_ul
- \+ *lemma* galois_insertion.l_supr_u
- \+ *lemma* galois_insertion.l_surjective
- \+/\- *lemma* galois_insertion.l_u_eq
- \+ *lemma* galois_insertion.u_injective
- \+/\- *theorem* order_iso.to_galois_connection

Modified src/topology/opens.lean




## [2020-03-02 08:53:22](https://github.com/leanprover-community/mathlib/commit/d5d907b)
feat(algebra/free_monoid): define `lift` and `map`, move out of `algebra/group` ([#2060](https://github.com/leanprover-community/mathlib/pull/2060))
* Move `free_monoid` from `algebra/group/` to `algebra/`
* feat(algebra/free_monoid): define `lift` and `map`
* Expand docstring, drop unneeded arguments to `to_additive`
* Fix compile
* Update src/algebra/free_monoid.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
#### Estimated changes
Added src/algebra/free_monoid.lean
- \+ *lemma* free_monoid.hom_eq
- \+ *def* free_monoid.lift
- \+ *lemma* free_monoid.lift_eval_of
- \+ *lemma* free_monoid.lift_of_comp_eq_map
- \+ *lemma* free_monoid.lift_restrict
- \+ *def* free_monoid.map
- \+ *lemma* free_monoid.map_comp
- \+ *lemma* free_monoid.map_of
- \+ *lemma* free_monoid.mul_def
- \+ *def* free_monoid.of
- \+ *lemma* free_monoid.of_mul_eq_cons
- \+ *lemma* free_monoid.one_def
- \+ *def* free_monoid

Modified src/algebra/group/default.lean


Deleted src/algebra/group/free_monoid.lean
- \- *lemma* free_monoid.mul_def
- \- *lemma* free_monoid.one_def
- \- *def* free_monoid

Modified src/category/fold.lean


Modified src/ring_theory/free_ring.lean




## [2020-03-01 23:09:46-08:00](https://github.com/leanprover-community/mathlib/commit/aec54b3)
fix(.mergify.yml): remove " (leanprover-community/lean:3.5.1)" ([#2077](https://github.com/leanprover-community/mathlib/pull/2077))
#### Estimated changes
Modified .mergify.yml


