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
modified src/algebra/big_operators.lean

modified src/data/finset.lean
- \+/\- *lemma* card_map
- \+/\- *lemma* card_map

modified src/data/fintype/basic.lean
- \+ *lemma* fintype.pi_finset_univ
- \- *lemma* pi_finset_univ

modified src/data/fintype/card.lean
- \+/\- *lemma* fintype.card_pi_finset
- \+ *lemma* finset.prod_univ_pi
- \+ *lemma* finset.prod_univ_sum
- \+/\- *lemma* fintype.card_pi_finset

modified src/linear_algebra/determinant.lean



## [2020-03-31 19:02:55](https://github.com/leanprover-community/mathlib/commit/224ba7e)
feat(data/finset): card_image_le ([#2295](https://github.com/leanprover-community/mathlib/pull/2295))
* feat(data/finset): card_image_le
* add list.to_finset_card_le
#### Estimated changes
modified src/data/finset.lean
- \+ *theorem* multiset.to_finset_card_le
- \+ *theorem* list.to_finset_card_le
- \+ *theorem* card_image_le



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
modified src/category/equiv_functor.lean

created src/category/equiv_functor/instances.lean

modified src/tactic/equiv_rw.lean

modified test/equiv_rw.lean
- \+ *lemma* semigroup.id_map
- \+ *lemma* semigroup.map_map
- \- *lemma* semigroup.map_id
- \- *lemma* semigroup.map_comp
- \- *def* semigroup.map_equiv



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
modified src/data/equiv/basic.lean
- \+ *lemma* arrow_congr'_apply
- \+ *lemma* arrow_congr'_refl
- \+ *lemma* arrow_congr'_trans
- \+ *lemma* arrow_congr'_symm
- \+ *def* of_iff
- \+ *def* arrow_congr'
- \+ *def* Pi_congr'

modified src/data/equiv/functor.lean
- \+ *lemma* map_equiv_refl
- \+ *lemma* map_equiv_refl_refl

modified src/set_theory/pgame.lean

created src/tactic/equiv_rw.lean

modified src/tactic/solve_by_elim.lean

modified src/tactic/tidy.lean

created test/equiv_rw.lean
- \+ *lemma* semigroup.map_id
- \+ *lemma* semigroup.map_comp
- \+ *def* semigroup.map
- \+ *def* semigroup.map_equiv
- \+ *def* monoid.map



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
modified src/data/finsupp.lean
- \+ *lemma* prod_comm
- \+ *lemma* prod_ite_eq
- \+ *lemma* prod_ite_eq'
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_apply

modified src/data/monoid_algebra.lean
- \+ *lemma* mul_apply
- \+ *lemma* mul_apply_left
- \+ *lemma* mul_single_apply
- \+ *lemma* mul_apply_right
- \+ *lemma* single_mul_apply

modified src/data/polynomial.lean
- \+/\- *lemma* coeff_smul
- \+/\- *lemma* C_mul'
- \+/\- *lemma* coeff_smul
- \+/\- *lemma* C_mul'



## [2020-03-31 09:10:23](https://github.com/leanprover-community/mathlib/commit/1763220)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-31 08:35:51](https://github.com/leanprover-community/mathlib/commit/85affa4)
refactor(*): migrate more files to bundled `ring_hom`s ([#2286](https://github.com/leanprover-community/mathlib/pull/2286))
* refactor(*): migrate more files to bundled `ring_hom`s
* Fix lint
#### Estimated changes
modified src/algebra/big_operators.lean

modified src/algebra/char_p.lean
- \+ *def* cast_hom

modified src/algebra/module.lean
- \+ *def* ring_hom.to_module
- \- *def* is_ring_hom.to_module

modified src/data/equiv/basic.lean
- \+/\- *def* function.involutive.to_equiv
- \+/\- *def* function.involutive.to_equiv

modified src/data/int/basic.lean
- \+ *lemma* coe_cast_ring_hom
- \+ *lemma* eq_int_cast
- \+ *lemma* eq_int_cast'
- \+ *lemma* map_int_cast
- \- *lemma* eq_cast'
- \- *lemma* is_ring_hom.map_int_cast
- \- *lemma* ring_hom.map_int_cast
- \+ *def* cast_ring_hom

modified src/data/mv_polynomial.lean
- \+ *lemma* coe_eval₂_hom
- \+/\- *lemma* C_sub
- \+/\- *lemma* eval₂_sub
- \+/\- *lemma* eval_sub
- \+/\- *lemma* map_sub
- \+/\- *lemma* C_sub
- \+/\- *lemma* eval₂_sub
- \+/\- *lemma* eval_sub
- \+/\- *lemma* map_sub
- \+ *def* eval₂_hom

modified src/data/nat/cast.lean
- \+ *lemma* coe_cast_add_monoid_hom
- \+ *lemma* coe_cast_ring_hom
- \+/\- *lemma* ring_hom.map_nat_cast
- \- *lemma* is_semiring_hom.map_nat_cast
- \+/\- *lemma* ring_hom.map_nat_cast
- \+ *def* cast_add_monoid_hom
- \+ *def* cast_ring_hom

modified src/data/polynomial.lean

modified src/data/real/nnreal.lean

modified src/data/zmod/quadratic_reciprocity.lean

modified src/field_theory/finite.lean

modified src/field_theory/finite_card.lean

modified src/ring_theory/algebra.lean

modified src/ring_theory/free_comm_ring.lean



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
created src/analysis/analytic/basic.lean
- \+ *lemma* le_radius_of_bound
- \+ *lemma* bound_of_lt_radius
- \+ *lemma* geometric_bound_of_lt_radius
- \+ *lemma* min_radius_le_radius_add
- \+ *lemma* radius_neg
- \+ *lemma* partial_sum_continuous
- \+ *lemma* has_fpower_series_on_ball.has_fpower_series_at
- \+ *lemma* has_fpower_series_at.analytic_at
- \+ *lemma* has_fpower_series_on_ball.analytic_at
- \+ *lemma* has_fpower_series_on_ball.radius_pos
- \+ *lemma* has_fpower_series_at.radius_pos
- \+ *lemma* has_fpower_series_on_ball.mono
- \+ *lemma* has_fpower_series_on_ball.add
- \+ *lemma* has_fpower_series_at.add
- \+ *lemma* analytic_at.add
- \+ *lemma* has_fpower_series_on_ball.neg
- \+ *lemma* has_fpower_series_at.neg
- \+ *lemma* analytic_at.neg
- \+ *lemma* has_fpower_series_on_ball.sub
- \+ *lemma* has_fpower_series_at.sub
- \+ *lemma* analytic_at.sub
- \+ *lemma* has_fpower_series_on_ball.coeff_zero
- \+ *lemma* has_fpower_series_at.coeff_zero
- \+ *lemma* has_fpower_series_on_ball.uniform_limit
- \+ *lemma* has_fpower_series_on_ball.continuous_on
- \+ *lemma* has_fpower_series_at.continuous_at
- \+ *lemma* analytic_at.continuous_at
- \+ *lemma* formal_multilinear_series.has_fpower_series_on_ball
- \+ *lemma* has_fpower_series_on_ball.sum
- \+ *lemma* formal_multilinear_series.continuous_on
- \+ *def* radius
- \+ *def* partial_sum
- \+ *def* has_fpower_series_at
- \+ *def* analytic_at

modified src/data/real/ennreal.lean
- \+ *lemma* lt_iff_exists_nnreal_btwn

modified src/data/set/finite.lean
- \+ *lemma* bdd_above
- \+ *lemma* bdd_below

modified src/order/bounded_lattice.lean
- \+ *lemma* lt_iff_exists_coe_btwn
- \- *lemma* dense_coe

modified src/topology/metric_space/emetric_space.lean



## [2020-03-31 03:13:56](https://github.com/leanprover-community/mathlib/commit/20bff2c)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-31 02:43:53](https://github.com/leanprover-community/mathlib/commit/4168aba)
refactor(data/fintype): move data/fintype to data/fintype/basic ([#2285](https://github.com/leanprover-community/mathlib/pull/2285))
#### Estimated changes
modified docs/theories/sets.md

modified src/algebra/char_p.lean

modified src/category_theory/discrete_category.lean

modified src/category_theory/limits/shapes/equalizers.lean

modified src/category_theory/limits/shapes/finite_limits.lean

modified src/category_theory/limits/shapes/finite_products.lean

modified src/category_theory/limits/shapes/pullbacks.lean

modified src/computability/turing_machine.lean

modified src/data/W.lean

modified src/data/equiv/denumerable.lean

modified src/data/equiv/list.lean

modified src/data/fin_enum.lean

renamed src/data/fintype.lean to src/data/fintype/basic.lean

modified src/data/fintype/card.lean

modified src/data/fintype/intervals.lean

modified src/data/matrix/basic.lean

modified src/data/set/finite.lean

modified src/data/zmod/basic.lean

modified src/group_theory/free_group.lean

modified src/group_theory/perm/sign.lean

modified src/number_theory/bernoulli.lean

modified src/tactic/fin_cases.lean

modified test/omega.lean



## [2020-03-31 00:17:23](https://github.com/leanprover-community/mathlib/commit/c5181d1)
feat(*): more `prod`-related (continuous) linear maps and their derivatives ([#2277](https://github.com/leanprover-community/mathlib/pull/2277))
* feat(*): more `prod`-related (continuous) linear maps and their derivatives
* Make `R` argument of `continuous_linear_equiv.refl` explicit
#### Estimated changes
modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* has_strict_fderiv_at.prod
- \+/\- *lemma* has_fderiv_at_filter.prod
- \+/\- *lemma* has_fderiv_within_at.prod
- \+/\- *lemma* has_fderiv_at.prod
- \+/\- *lemma* differentiable_within_at.prod
- \+/\- *lemma* differentiable_at.prod
- \+/\- *lemma* differentiable_on.prod
- \+/\- *lemma* differentiable.prod
- \+/\- *lemma* differentiable_at.fderiv_prod
- \+/\- *lemma* differentiable_at.fderiv_within_prod
- \+ *lemma* has_strict_fderiv_at_fst
- \+ *lemma* has_strict_fderiv_at.fst
- \+ *lemma* has_fderiv_at_filter_fst
- \+ *lemma* has_fderiv_at_filter.fst
- \+ *lemma* has_fderiv_at_fst
- \+ *lemma* has_fderiv_at.fst
- \+ *lemma* has_fderiv_within_at_fst
- \+ *lemma* has_fderiv_within_at.fst
- \+ *lemma* differentiable_at_fst
- \+ *lemma* differentiable_at.fst
- \+ *lemma* differentiable_fst
- \+ *lemma* differentiable.fst
- \+ *lemma* differentiable_within_at_fst
- \+ *lemma* differentiable_within_at.fst
- \+ *lemma* differentiable_on_fst
- \+ *lemma* differentiable_on.fst
- \+ *lemma* fderiv_fst
- \+ *lemma* fderiv.fst
- \+ *lemma* fderiv_within_fst
- \+ *lemma* fderiv_within.fst
- \+ *lemma* has_strict_fderiv_at_snd
- \+ *lemma* has_strict_fderiv_at.snd
- \+ *lemma* has_fderiv_at_filter_snd
- \+ *lemma* has_fderiv_at_filter.snd
- \+ *lemma* has_fderiv_at_snd
- \+ *lemma* has_fderiv_at.snd
- \+ *lemma* has_fderiv_within_at_snd
- \+ *lemma* has_fderiv_within_at.snd
- \+ *lemma* differentiable_at_snd
- \+ *lemma* differentiable_at.snd
- \+ *lemma* differentiable_snd
- \+ *lemma* differentiable.snd
- \+ *lemma* differentiable_within_at_snd
- \+ *lemma* differentiable_within_at.snd
- \+ *lemma* differentiable_on_snd
- \+ *lemma* differentiable_on.snd
- \+ *lemma* fderiv_snd
- \+ *lemma* fderiv.snd
- \+ *lemma* fderiv_within_snd
- \+ *lemma* fderiv_within.snd
- \+/\- *lemma* has_strict_fderiv_at.prod
- \+/\- *lemma* has_fderiv_at_filter.prod
- \+/\- *lemma* has_fderiv_within_at.prod
- \+/\- *lemma* has_fderiv_at.prod
- \+/\- *lemma* differentiable_within_at.prod
- \+/\- *lemma* differentiable_at.prod
- \+/\- *lemma* differentiable_on.prod
- \+/\- *lemma* differentiable.prod
- \+/\- *lemma* differentiable_at.fderiv_prod
- \+/\- *lemma* differentiable_at.fderiv_within_prod
- \+ *theorem* has_strict_fderiv_at_id
- \+ *theorem* has_strict_fderiv_at.prod_map
- \+ *theorem* has_fderiv_at.prod_map
- \+ *theorem* differentiable_at.prod_map

modified src/linear_algebra/basic.lean
- \+ *lemma* coe_prod
- \+ *lemma* skew_prod_apply
- \+ *lemma* skew_prod_symm_apply
- \+ *theorem* prod_map_apply
- \+ *def* prod_map

modified src/topology/algebra/module.lean
- \+/\- *lemma* coe_fst
- \+/\- *lemma* coe_fst'
- \+/\- *lemma* coe_snd
- \+/\- *lemma* coe_snd'
- \+ *lemma* coe_prod_map
- \+ *lemma* prod_map_apply
- \+ *lemma* coe_refl
- \+ *lemma* coe_refl'
- \+ *lemma* prod_apply
- \+ *lemma* coe_prod
- \+ *lemma* skew_prod_apply
- \+ *lemma* skew_prod_symm_apply
- \+/\- *lemma* coe_fst
- \+/\- *lemma* coe_fst'
- \+/\- *lemma* coe_snd
- \+/\- *lemma* coe_snd'
- \+ *theorem* coe_def_rev
- \+ *def* fst
- \+ *def* snd
- \+ *def* prod_map
- \+ *def* prod
- \+ *def* skew_prod

modified src/topology/basic.lean
- \+/\- *lemma* nhds_basis_opens
- \+/\- *lemma* nhds_basis_opens

modified src/topology/constructions.lean
- \+ *lemma* continuous.prod_map



## [2020-03-30 20:48:51](https://github.com/leanprover-community/mathlib/commit/64f835b)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-30 20:13:52](https://github.com/leanprover-community/mathlib/commit/8a61723)
fix(algebra/punit_instance): punit.smul_eq is marked simp and can be proved by simp ([#2291](https://github.com/leanprover-community/mathlib/pull/2291))
#### Estimated changes
modified src/algebra/punit_instances.lean
- \+/\- *lemma* smul_eq
- \+/\- *lemma* smul_eq



## [2020-03-30 16:48:08](https://github.com/leanprover-community/mathlib/commit/3f0e700)
doc(algebra/group/type_tags): add docs ([#2287](https://github.com/leanprover-community/mathlib/pull/2287))
* doc(algebra/group/type_tags): add docs
* Update src/algebra/group/type_tags.lean
#### Estimated changes
modified src/algebra/group/type_tags.lean



## [2020-03-30 13:16:33](https://github.com/leanprover-community/mathlib/commit/1331e29)
chore(*): completing most of the -T50000 challenge ([#2281](https://github.com/leanprover-community/mathlib/pull/2281))
#### Estimated changes
modified src/analysis/complex/basic.lean

modified src/analysis/normed_space/real_inner_product.lean

modified src/category_theory/limits/over.lean

modified src/measure_theory/integration.lean

modified src/measure_theory/simple_func_dense.lean

modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* ne_zero_of_mul_eq_one

modified src/topology/algebra/infinite_sum.lean

modified src/topology/category/Top/adjunctions.lean

modified src/topology/category/UniformSpace.lean



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
modified src/algebra/big_operators.lean
- \+ *lemma* prod_add
- \+ *lemma* sum_pow_mul_eq_add_pow

modified src/data/fin.lean

modified src/data/finset.lean
- \+ *lemma* mono_of_fin_strict_mono
- \+ *lemma* mono_of_fin_zero
- \+ *lemma* mono_of_fin_last
- \+ *lemma* mono_of_fin_unique
- \+ *lemma* disjoint_iff_disjoint_coe
- \+ *lemma* range_eq_Ico

modified src/data/fintype.lean
- \+ *lemma* finset.mono_of_fin_unique'
- \+ *lemma* fintype.coe_image_univ

modified src/data/fintype/card.lean
- \+ *lemma* fintype.sum_pow_mul_eq_add_pow
- \+ *lemma* fin.sum_pow_mul_eq_add_pow



## [2020-03-30 08:09:21](https://github.com/leanprover-community/mathlib/commit/cd38923)
docs(algebraic_geometry/prime_spectrum): linkify url in module docs ([#2288](https://github.com/leanprover-community/mathlib/pull/2288))
#### Estimated changes
modified src/algebraic_geometry/prime_spectrum.lean



## [2020-03-30 06:25:08](https://github.com/leanprover-community/mathlib/commit/9288d10)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-30 05:50:58](https://github.com/leanprover-community/mathlib/commit/51553e3)
chore(data/set/lattice): use dot syntax for `disjoint.*` ([#2282](https://github.com/leanprover-community/mathlib/pull/2282))
#### Estimated changes
modified src/data/finsupp.lean

modified src/data/set/lattice.lean
- \+ *lemma* disjoint.ne
- \+ *lemma* pairwise_disjoint.subset
- \+ *lemma* pairwise_disjoint.range
- \+ *lemma* pairwise_disjoint.elim
- \- *lemma* ne_of_disjoint
- \- *lemma* pairwise_disjoint_subset
- \- *lemma* pairwise_disjoint_range
- \- *lemma* pairwise_disjoint_elim
- \+ *theorem* disjoint.mono
- \+ *theorem* disjoint.mono_left
- \+ *theorem* disjoint.mono_right
- \- *theorem* disjoint_mono
- \- *theorem* disjoint_mono_left
- \- *theorem* disjoint_mono_right
- \+/\- *def* kern_image
- \+/\- *def* kern_image

modified src/data/setoid.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/basis.lean

modified src/linear_algebra/finsupp.lean

modified src/linear_algebra/finsupp_vector_space.lean

modified src/order/conditionally_complete_lattice.lean

modified src/topology/separation.lean



## [2020-03-30 03:22:11](https://github.com/leanprover-community/mathlib/commit/cf64860)
chore(*): remove 'using_well_founded wf_tacs', fixed in core ([#2280](https://github.com/leanprover-community/mathlib/pull/2280))
#### Estimated changes
modified docs/extras/well_founded_recursion.md

modified src/computability/partrec_code.lean

modified src/data/list/basic.lean

modified src/data/list/sort.lean

modified src/data/vector2.lean

modified src/tactic/basic.lean

deleted src/tactic/well_founded_tactics.lean



## [2020-03-30 00:45:51](https://github.com/leanprover-community/mathlib/commit/8c1e32f)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified .github/workflows/build.yml

modified scripts/fetch_olean_cache.sh

modified src/set_theory/surreal.lean
- \+/\- *theorem* lt_iff_le_not_le
- \+/\- *theorem* lt_iff_le_not_le



## [2020-03-29 21:31:54](https://github.com/leanprover-community/mathlib/commit/c14c84e)
chore(topology/algebra/ordered): `le_of_tendsto`: use `∀ᶠ`, add primed versions ([#2270](https://github.com/leanprover-community/mathlib/pull/2270))
Also fix two typos in `order/filter/basic`
#### Estimated changes
modified src/analysis/normed_space/basic.lean

modified src/measure_theory/decomposition.lean

modified src/measure_theory/l1_space.lean

modified src/order/filter/basic.lean
- \+ *lemma* tendsto_add_at_top_nat
- \+ *lemma* tendsto_sub_at_top_nat
- \- *lemma* tendso_add_at_top_nat
- \- *lemma* tendso_sub_at_top_nat

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/ordered.lean
- \+ *lemma* le_of_tendsto_of_tendsto'
- \+ *lemma* le_of_tendsto'
- \+ *lemma* ge_of_tendsto'

modified src/topology/bounded_continuous_function.lean



## [2020-03-29 19:03:26](https://github.com/leanprover-community/mathlib/commit/8b679d9)
fix(tactic/squeeze): make suggestion at correct location ([#2279](https://github.com/leanprover-community/mathlib/pull/2279))
Fixes [#2267](https://github.com/leanprover-community/mathlib/pull/2267).
#### Estimated changes
modified src/tactic/squeeze.lean



## [2020-03-29 16:22:44](https://github.com/leanprover-community/mathlib/commit/38544f1)
feat(tactic/core): basic interaction monad functions ([#1658](https://github.com/leanprover-community/mathlib/pull/1658))
* feat(tactic/core): basic interaction monad functions
* review
* remove get_result
* update comments
* whitespace
* american spelling
#### Estimated changes
modified src/tactic/core.lean



## [2020-03-29 13:46:46](https://github.com/leanprover-community/mathlib/commit/c4fb403)
fix(tactic/core): remove all_goals option from apply_any ([#2275](https://github.com/leanprover-community/mathlib/pull/2275))
* fix(tactic/core): remove all_goals option from any_apply
* remove unnecessary imports
#### Estimated changes
modified src/set_theory/pgame.lean

modified src/tactic/core.lean

modified src/tactic/solve_by_elim.lean



## [2020-03-29 11:19:27](https://github.com/leanprover-community/mathlib/commit/da8b23f)
chore(data/opposite): two trivial lemmas ([#2274](https://github.com/leanprover-community/mathlib/pull/2274))
#### Estimated changes
modified src/data/opposite.lean
- \+ *lemma* op_eq_iff_eq_unop
- \+ *lemma* unop_eq_iff_eq_op



## [2020-03-29 08:42:21](https://github.com/leanprover-community/mathlib/commit/79880e8)
chore(data/fintype/intervals): `simp` `Ico_*_card` lemmas ([#2271](https://github.com/leanprover-community/mathlib/pull/2271))
#### Estimated changes
modified src/data/finset.lean
- \+ *lemma* Ico_ℤ.card

modified src/data/fintype/intervals.lean
- \+ *lemma* Ico_ℕ_card
- \+ *lemma* Ico_pnat_card
- \+ *lemma* Ico_ℤ_card

modified src/data/pnat/intervals.lean
- \+ *lemma* Ico.card



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
modified src/algebra/pi_instances.lean
- \+ *lemma* mk_sub_mk

modified src/analysis/asymptotics.lean
- \+ *lemma* is_O_fst_prod'
- \+ *lemma* is_O_snd_prod'

modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_strict_fderiv_at.is_O_sub
- \+ *lemma* has_fderiv_at_filter.is_O_sub
- \+ *lemma* has_strict_fderiv_at.has_fderiv_at
- \+ *lemma* has_strict_fderiv_at.differentiable_at
- \+/\- *lemma* differentiable_within_at.continuous_within_at
- \+/\- *lemma* differentiable_at.continuous_at
- \+/\- *lemma* differentiable_on.continuous_on
- \+/\- *lemma* differentiable.continuous
- \+ *lemma* has_strict_fderiv_at.continuous_at
- \+/\- *lemma* is_bounded_linear_map.has_fderiv_at_filter
- \+ *lemma* has_strict_fderiv_at.prod
- \+/\- *lemma* has_fderiv_at_filter.prod
- \+/\- *lemma* has_fderiv_within_at.prod
- \+/\- *lemma* has_fderiv_at.prod
- \+/\- *lemma* differentiable_within_at.prod
- \+/\- *lemma* differentiable_at.prod
- \+/\- *lemma* differentiable_on.prod
- \+/\- *lemma* differentiable.prod
- \+/\- *lemma* differentiable_at.fderiv_prod
- \+/\- *lemma* differentiable_at.fderiv_within_prod
- \+/\- *lemma* differentiable_within_at.comp
- \+/\- *lemma* differentiable_at.comp
- \+/\- *lemma* differentiable_at.comp_differentiable_within_at
- \+/\- *lemma* fderiv_within.comp
- \+/\- *lemma* fderiv.comp
- \+/\- *lemma* fderiv.comp_fderiv_within
- \+/\- *lemma* differentiable_on.comp
- \+/\- *lemma* differentiable.comp
- \+/\- *lemma* differentiable.comp_differentiable_on
- \+ *lemma* has_strict_fderiv_at.comp
- \+/\- *lemma* differentiable_within_at.const_smul
- \+/\- *lemma* differentiable_at.const_smul
- \+/\- *lemma* differentiable_on.const_smul
- \+/\- *lemma* differentiable.const_smul
- \+/\- *lemma* fderiv_within_const_smul
- \+/\- *lemma* fderiv_const_smul
- \+ *lemma* is_bounded_bilinear_map.has_strict_fderiv_at
- \+/\- *lemma* is_bounded_bilinear_map.has_fderiv_at
- \+/\- *lemma* is_bounded_bilinear_map.differentiable_within_at
- \+ *lemma* continuous_linear_equiv.comp_has_strict_fderiv_at_iff
- \+ *lemma* has_fderiv_within_at.maps_to_tangent_cone
- \+ *lemma* has_strict_fderiv_at.restrict_scalars
- \+/\- *lemma* is_bounded_linear_map.has_fderiv_at_filter
- \- *lemma* continuous_linear_map.has_fderiv_at_filter
- \+/\- *lemma* differentiable_within_at.const_smul
- \+/\- *lemma* differentiable_at.const_smul
- \+/\- *lemma* differentiable_on.const_smul
- \+/\- *lemma* differentiable.const_smul
- \+/\- *lemma* fderiv_within_const_smul
- \+/\- *lemma* fderiv_const_smul
- \+/\- *lemma* differentiable_within_at.continuous_within_at
- \+/\- *lemma* differentiable_at.continuous_at
- \+/\- *lemma* differentiable_on.continuous_on
- \+/\- *lemma* differentiable.continuous
- \+/\- *lemma* is_bounded_bilinear_map.has_fderiv_at
- \+/\- *lemma* is_bounded_bilinear_map.differentiable_within_at
- \+/\- *lemma* has_fderiv_at_filter.prod
- \+/\- *lemma* has_fderiv_within_at.prod
- \+/\- *lemma* has_fderiv_at.prod
- \+/\- *lemma* differentiable_within_at.prod
- \+/\- *lemma* differentiable_at.prod
- \+/\- *lemma* differentiable_on.prod
- \+/\- *lemma* differentiable.prod
- \+/\- *lemma* differentiable_at.fderiv_prod
- \+/\- *lemma* differentiable_at.fderiv_within_prod
- \+/\- *lemma* differentiable_within_at.comp
- \+/\- *lemma* differentiable_at.comp
- \+/\- *lemma* differentiable_at.comp_differentiable_within_at
- \+/\- *lemma* fderiv_within.comp
- \+/\- *lemma* fderiv.comp
- \+/\- *lemma* fderiv.comp_fderiv_within
- \+/\- *lemma* differentiable_on.comp
- \+/\- *lemma* differentiable.comp
- \+/\- *lemma* differentiable.comp_differentiable_on
- \- *lemma* has_fderiv_within_at.image_tangent_cone_subset
- \+/\- *theorem* has_fderiv_at_filter.tendsto_nhds
- \+/\- *theorem* has_fderiv_within_at.continuous_within_at
- \+/\- *theorem* has_fderiv_at.continuous_at
- \+ *theorem* has_strict_fderiv_at_congr_of_mem_sets
- \+ *theorem* has_strict_fderiv_at_const
- \+/\- *theorem* has_fderiv_at_filter.comp
- \+/\- *theorem* has_fderiv_within_at.comp
- \+/\- *theorem* has_fderiv_at.comp
- \+/\- *theorem* has_fderiv_at.comp_has_fderiv_within_at
- \+ *theorem* has_strict_fderiv_at.const_smul
- \+/\- *theorem* has_fderiv_at_filter.const_smul
- \+/\- *theorem* has_fderiv_within_at.const_smul
- \+/\- *theorem* has_fderiv_at.const_smul
- \+ *theorem* has_strict_fderiv_at.add
- \+/\- *theorem* has_fderiv_at_filter.add
- \+/\- *theorem* has_fderiv_within_at.add
- \+/\- *theorem* has_fderiv_at.add
- \+ *theorem* has_strict_fderiv_at.add_const
- \+ *theorem* has_strict_fderiv_at.const_add
- \+ *theorem* has_strict_fderiv_at.neg
- \+ *theorem* has_strict_fderiv_at.sub
- \+ *theorem* has_strict_fderiv_at.sub_const
- \+ *theorem* has_strict_fderiv_at.const_sub
- \+ *theorem* has_strict_fderiv_at.smul
- \+ *theorem* has_strict_fderiv_at.smul_const
- \+ *theorem* has_strict_fderiv_at.mul
- \+ *theorem* has_strict_fderiv_at.mul_const
- \+/\- *theorem* has_fderiv_within_at.mul_const
- \+ *theorem* has_strict_fderiv_at.const_mul
- \+/\- *theorem* has_fderiv_at_filter.const_smul
- \+/\- *theorem* has_fderiv_within_at.const_smul
- \+/\- *theorem* has_fderiv_at.const_smul
- \+/\- *theorem* has_fderiv_at_filter.add
- \+/\- *theorem* has_fderiv_within_at.add
- \+/\- *theorem* has_fderiv_at.add
- \- *theorem* has_fderiv_at_filter.is_O_sub
- \+/\- *theorem* has_fderiv_at_filter.tendsto_nhds
- \+/\- *theorem* has_fderiv_within_at.continuous_within_at
- \+/\- *theorem* has_fderiv_at.continuous_at
- \+/\- *theorem* has_fderiv_at_filter.comp
- \+/\- *theorem* has_fderiv_within_at.comp
- \+/\- *theorem* has_fderiv_at.comp
- \+/\- *theorem* has_fderiv_at.comp_has_fderiv_within_at
- \+/\- *theorem* has_fderiv_within_at.mul_const
- \+ *def* has_strict_fderiv_at

modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* is_bounded_bilinear_map.is_O_comp

modified src/order/filter/basic.lean
- \+ *lemma* tendsto.eventually
- \+ *lemma* eventually.prod_inl
- \+ *lemma* eventually.prod_inr
- \+ *lemma* eventually.prod_mk

modified src/topology/constructions.lean
- \+ *lemma* continuous_at_fst
- \+ *lemma* continuous_at_snd
- \+ *lemma* filter.eventually.prod_inl_nhds
- \+ *lemma* filter.eventually.prod_inr_nhds
- \+ *lemma* filter.eventually.prod_mk_nhds
- \+ *lemma* continuous_at.prod_map
- \+ *lemma* continuous_at.prod_map'



## [2020-03-29 03:24:03](https://github.com/leanprover-community/mathlib/commit/de8c207)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-29 02:52:21](https://github.com/leanprover-community/mathlib/commit/8454c10)
doc(ring_theory/noetherian): add docstring, normalise notation ([#2219](https://github.com/leanprover-community/mathlib/pull/2219))
* change notation; add module docstring
* adding reference to A-M
* Update src/ring_theory/noetherian.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Apply suggestions from code review
#### Estimated changes
modified docs/references.bib

modified src/ring_theory/noetherian.lean
- \+/\- *lemma* well_founded_submodule_gt
- \+/\- *lemma* finite_of_linear_independent
- \+/\- *lemma* well_founded_dvd_not_unit
- \+/\- *lemma* exists_irreducible_factor
- \+/\- *lemma* irreducible_induction_on
- \+/\- *lemma* exists_factors
- \+/\- *lemma* fg_pow
- \+/\- *lemma* well_founded_submodule_gt
- \+/\- *lemma* finite_of_linear_independent
- \+/\- *lemma* well_founded_dvd_not_unit
- \+/\- *lemma* exists_irreducible_factor
- \+/\- *lemma* irreducible_induction_on
- \+/\- *lemma* exists_factors
- \+/\- *lemma* fg_pow
- \+/\- *theorem* fg_def
- \+/\- *theorem* fg_bot
- \+/\- *theorem* fg_sup
- \+/\- *theorem* fg_map
- \+/\- *theorem* fg_prod
- \+/\- *theorem* fg_of_fg_map_of_fg_inf_ker
- \+/\- *theorem* is_noetherian_submodule
- \+/\- *theorem* is_noetherian_submodule_left
- \+/\- *theorem* is_noetherian_submodule_right
- \+/\- *theorem* is_noetherian_of_surjective
- \+/\- *theorem* is_noetherian_of_linear_equiv
- \+/\- *theorem* is_noetherian_of_submodule_of_noetherian
- \+/\- *theorem* is_noetherian_of_quotient_of_noetherian
- \+/\- *theorem* is_noetherian_of_fg_of_noetherian
- \+/\- *theorem* is_noetherian_span_of_finite
- \+/\- *theorem* fg_def
- \+/\- *theorem* fg_bot
- \+/\- *theorem* fg_sup
- \+/\- *theorem* fg_map
- \+/\- *theorem* fg_prod
- \+/\- *theorem* fg_of_fg_map_of_fg_inf_ker
- \+/\- *theorem* is_noetherian_submodule
- \+/\- *theorem* is_noetherian_submodule_left
- \+/\- *theorem* is_noetherian_submodule_right
- \+/\- *theorem* is_noetherian_of_surjective
- \+/\- *theorem* is_noetherian_of_linear_equiv
- \+/\- *theorem* is_noetherian_of_submodule_of_noetherian
- \+/\- *theorem* is_noetherian_of_quotient_of_noetherian
- \+/\- *theorem* is_noetherian_of_fg_of_noetherian
- \+/\- *theorem* is_noetherian_span_of_finite
- \+/\- *def* fg
- \+/\- *def* is_noetherian_ring
- \+/\- *def* fg
- \+/\- *def* is_noetherian_ring



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
created src/category/equiv_functor.lean
- \+ *lemma* map_equiv_apply
- \+ *lemma* map_equiv_symm_apply
- \+ *def* map_equiv

modified src/category_theory/core.lean
- \+ *def* of_equiv_functor

modified src/category_theory/types.lean
- \+ *lemma* to_equiv_id
- \+ *lemma* to_equiv_comp

modified src/data/equiv/basic.lean
- \+/\- *def* prod_congr
- \+/\- *def* prod_congr

modified src/logic/unique.lean



## [2020-03-28 21:19:19](https://github.com/leanprover-community/mathlib/commit/d500210)
feat(algebra/big_operators): missing lemmas ([#2259](https://github.com/leanprover-community/mathlib/pull/2259))
#### Estimated changes
modified src/algebra/big_operators.lean
- \+ *lemma* prod_pow_eq_pow_sum
- \+ *lemma* sum_lt_sum_of_subset
- \+ *lemma* prod_le_prod'



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
modified src/meta/expr.lean

modified src/tactic/core.lean

modified src/tactic/solve_by_elim.lean

modified test/solve_by_elim.lean
- \+ *def* solve_by_elim_use_b



## [2020-03-28 17:37:54](https://github.com/leanprover-community/mathlib/commit/0187cb5)
fix(scripts/deploy_docs.sh): cd before git log ([#2264](https://github.com/leanprover-community/mathlib/pull/2264))
* fix(scripts/deploy_docs.sh): cd before git log
* Update scripts/deploy_docs.sh
#### Estimated changes
modified scripts/deploy_docs.sh



## [2020-03-28 12:46:28](https://github.com/leanprover-community/mathlib/commit/17f8340)
chore(data/equiv/basic): simp to_fun to coe ([#2256](https://github.com/leanprover-community/mathlib/pull/2256))
* chore(data/equiv/basic): simp to_fun to coe
* fix proofs
* Update src/data/equiv/basic.lean
* fix proof
* partially removing to_fun
* finish switching to coercions
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *lemma* to_fun_as_coe
- \+ *lemma* inv_fun_as_coe

modified src/topology/metric_space/gromov_hausdorff.lean



## [2020-03-28 06:05:30](https://github.com/leanprover-community/mathlib/commit/d470ae7)
fix(tactic/squeeze): do not fail when closing the goal ([#2262](https://github.com/leanprover-community/mathlib/pull/2262))
#### Estimated changes
modified src/tactic/squeeze.lean

modified test/examples.lean



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
modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* norm_id_le
- \+/\- *lemma* norm_id
- \+/\- *lemma* op_norm_comp_le
- \+ *lemma* uniform_embedding
- \+ *lemma* one_le_norm_mul_norm_symm
- \+ *lemma* norm_pos
- \+ *lemma* norm_symm_pos
- \+ *lemma* subsingleton_or_norm_symm_pos
- \+ *lemma* subsingleton_or_nnnorm_symm_pos
- \+/\- *lemma* norm_id
- \+/\- *lemma* op_norm_comp_le
- \- *lemma* continuous_linear_equiv.lipschitz
- \- *lemma* continuous_linear_equiv.antilipschitz
- \- *lemma* continuous_linear_equiv.uniform_embedding
- \+ *theorem* le_op_norm_of_le

modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* to_right_inverse
- \+ *lemma* lipschitz_with.to_right_inverse
- \- *lemma* to_inverse
- \- *lemma* lipschitz_with.to_inverse



## [2020-03-28 02:36:23](https://github.com/leanprover-community/mathlib/commit/1b13ccd)
chore(scripts/deploy_docs.sh): skip gen_docs if already built ([#2263](https://github.com/leanprover-community/mathlib/pull/2263))
* chore(scripts/deploy_docs.sh): skip gen_docs if already built
* Update scripts/deploy_docs.sh
#### Estimated changes
modified scripts/deploy_docs.sh



## [2020-03-28 00:46:23](https://github.com/leanprover-community/mathlib/commit/211c5d1)
chore(data/int/basic): change instance order ([#2257](https://github.com/leanprover-community/mathlib/pull/2257))
#### Estimated changes
modified src/data/int/basic.lean



## [2020-03-27 22:08:58](https://github.com/leanprover-community/mathlib/commit/3c0b35c)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified src/algebra/big_operators.lean
- \+ *lemma* prod_apply_ite
- \+/\- *lemma* prod_ite
- \+ *lemma* sum_boole
- \+ *lemma* prod_pow_boole
- \+/\- *lemma* prod_ite

modified src/algebra/group_power.lean
- \+ *lemma* pow_ite
- \+ *lemma* ite_pow
- \+ *lemma* pow_boole

modified src/algebra/ring.lean
- \+/\- *lemma* mul_ite
- \+/\- *lemma* ite_mul
- \+ *lemma* mul_boole
- \+ *lemma* boole_mul
- \+/\- *lemma* mul_ite
- \+/\- *lemma* ite_mul

modified src/analysis/convex/basic.lean

modified src/analysis/convex/specific_functions.lean

modified src/data/equiv/basic.lean

modified src/data/nat/cast.lean
- \+ *theorem* cast_ite

modified src/data/nat/multiplicity.lean

modified src/data/zmod/quadratic_reciprocity.lean

modified src/linear_algebra/nonsingular_inverse.lean



## [2020-03-27 18:48:08](https://github.com/leanprover-community/mathlib/commit/786c737)
feat(logic/basic): trivial transport lemmas ([#2254](https://github.com/leanprover-community/mathlib/pull/2254))
* feat(logic/basic): trivial transport lemmas
* oops
#### Estimated changes
modified src/category_theory/limits/shapes/equalizers.lean

modified src/data/nat/basic.lean

modified src/logic/basic.lean
- \+ *lemma* eq_rec_constant
- \+ *lemma* eq_mp_rfl
- \+ *lemma* eq_mpr_rfl



## [2020-03-27 16:08:17](https://github.com/leanprover-community/mathlib/commit/451de27)
chore(tactic/lint): typo ([#2253](https://github.com/leanprover-community/mathlib/pull/2253))
#### Estimated changes
modified src/tactic/lint.lean



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
modified src/tactic/cache.lean

modified src/tactic/core.lean

modified src/tactic/elide.lean

modified src/tactic/ext.lean

modified src/tactic/finish.lean

modified src/tactic/hint.lean

modified src/tactic/interactive.lean

modified src/tactic/linarith.lean

modified src/tactic/localized.lean

modified src/tactic/norm_cast.lean

modified src/tactic/omega/main.lean

modified src/tactic/pi_instances.lean

modified src/tactic/replacer.lean

modified src/tactic/restate_axiom.lean

modified src/tactic/ring.lean

modified src/tactic/ring_exp.lean

modified src/tactic/solve_by_elim.lean

modified src/tactic/tidy.lean



## [2020-03-27 12:12:17](https://github.com/leanprover-community/mathlib/commit/d3cbd4d)
chore(ci): update nolints before docs and leanchecker ([#2250](https://github.com/leanprover-community/mathlib/pull/2250))
* Update build.yml
* run lint+tests if build step succeeds (see [#2250](https://github.com/leanprover-community/mathlib/pull/2250)) ([#2252](https://github.com/leanprover-community/mathlib/pull/2252))
* run lint+tests if build succeeds
* move lint (and nolints.txt) before tests
* Apply suggestions from code review
#### Estimated changes
modified .github/workflows/build.yml



## [2020-03-26 16:57:24-04:00](https://github.com/leanprover-community/mathlib/commit/de39b9a)
chore(.mergify.yml): cleanup ([#2248](https://github.com/leanprover-community/mathlib/pull/2248))
remove [skip-ci] and pr bits that no longer apply.
#### Estimated changes
modified .mergify.yml



## [2020-03-26 20:55:31](https://github.com/leanprover-community/mathlib/commit/2fbf007)
doc(docs/install/project.md): mention that projects are git repositories ([#2244](https://github.com/leanprover-community/mathlib/pull/2244))
#### Estimated changes
modified docs/install/project.md



## [2020-03-26 20:00:59](https://github.com/leanprover-community/mathlib/commit/75b4ee8)
feat(data/equiv/local_equiv): construct from `bij_on` or `inj_on` ([#2232](https://github.com/leanprover-community/mathlib/pull/2232))
* feat(data/equiv/local_equiv): construct from `bij_on` or `inj_on`
Also fix usage of `nonempty` vs `inhabited` in `set/function`. Linter
didn't catch these bugs because the types use the `.to_nonempty`
projection of the `[inhabited]` arguments.
* Add `simps`/`simp` attrs
#### Estimated changes
modified src/data/equiv/local_equiv.lean

modified src/data/set/function.lean
- \+/\- *lemma* inj_on.inv_fun_on_image
- \+/\- *lemma* inj_on.inv_fun_on_image
- \+/\- *theorem* inj_on.left_inv_on_inv_fun_on
- \+/\- *theorem* surj_on.right_inv_on_inv_fun_on
- \+/\- *theorem* bij_on.inv_on_inv_fun_on
- \+/\- *theorem* surj_on.inv_on_inv_fun_on
- \+/\- *theorem* surj_on.maps_to_inv_fun_on
- \+/\- *theorem* surj_on.bij_on_subset
- \+/\- *theorem* inj_on.left_inv_on_inv_fun_on
- \+/\- *theorem* surj_on.right_inv_on_inv_fun_on
- \+/\- *theorem* bij_on.inv_on_inv_fun_on
- \+/\- *theorem* surj_on.inv_on_inv_fun_on
- \+/\- *theorem* surj_on.maps_to_inv_fun_on
- \+/\- *theorem* surj_on.bij_on_subset



## [2020-03-26 17:30:38](https://github.com/leanprover-community/mathlib/commit/8943351)
feat(topology/algebra/module): define `fst` and `snd`, review ([#2247](https://github.com/leanprover-community/mathlib/pull/2247))
* feat(topology/algebra/module): define `fst` and `snd`, review
* Fix compile
#### Estimated changes
modified src/geometry/manifold/mfderiv.lean

modified src/topology/algebra/module.lean
- \+ *lemma* coe_prod
- \+ *lemma* prod_apply
- \+ *lemma* coe_fst
- \+ *lemma* coe_fst'
- \+ *lemma* coe_snd
- \+ *lemma* coe_snd'
- \+ *theorem* bijective
- \+ *theorem* injective
- \+ *theorem* surjective
- \- *def* zero
- \- *def* prod



## [2020-03-26 14:41:41](https://github.com/leanprover-community/mathlib/commit/5b44363)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-26 13:38:06](https://github.com/leanprover-community/mathlib/commit/0fc4e6a)
refactor(data/set/function): move `function.restrict` to `set`, redefine ([#2243](https://github.com/leanprover-community/mathlib/pull/2243))
* refactor(data/set/function): move `function.restrict` to `set`, redefine
We had `subtype.restrict` and `function.restrict` both defined in the
same way using `subtype.val`. This PR moves `function.restrict` to
`set.restrict` and makes it use `coe` instead of `subtype.val`.
* Fix compile
* Update src/data/set/function.lean
#### Estimated changes
modified archive/sensitivity.lean

modified src/analysis/complex/exponential.lean

modified src/data/set/basic.lean
- \+/\- *lemma* val_range
- \+/\- *lemma* val_range
- \- *lemma* subtype.val_range
- \+ *theorem* preimage_coe_eq_preimage_coe_iff

modified src/data/set/countable.lean

modified src/data/set/function.lean
- \+ *lemma* restrict_eq
- \+ *lemma* restrict_apply
- \+/\- *lemma* range_restrict
- \+ *lemma* coe_cod_restrict_apply
- \+/\- *lemma* range_restrict
- \+ *def* restrict
- \+ *def* cod_restrict

modified src/data/subtype.lean
- \+/\- *lemma* val_eq_coe
- \+/\- *lemma* val_eq_coe

modified src/linear_algebra/basis.lean

modified src/logic/function.lean
- \- *theorem* restrict_eq
- \- *def* restrict

modified src/measure_theory/integration.lean

modified src/topology/constructions.lean

modified src/topology/continuous_on.lean

modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* restrict
- \+ *lemma* cod_restrict
- \+ *lemma* to_right_inv_on'
- \+ *lemma* to_right_inv_on
- \+ *lemma* subtype_coe
- \- *lemma* id

modified src/topology/metric_space/basic.lean
- \+/\- *theorem* subtype.dist_eq
- \+/\- *theorem* subtype.dist_eq

modified src/topology/metric_space/contracting.lean

modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* subtype.edist_eq
- \+/\- *theorem* subtype.edist_eq

modified src/topology/metric_space/lipschitz.lean



## [2020-03-26 11:00:48](https://github.com/leanprover-community/mathlib/commit/fa36a8e)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-26 10:05:36](https://github.com/leanprover-community/mathlib/commit/ea10e17)
feat(data/equiv/functor): bifunctor.map_equiv ([#2241](https://github.com/leanprover-community/mathlib/pull/2241))
* feat(data/equiv/functor): bifunctor.map_equiv
* add documentation, and make the function an explicit argument
* Update src/data/equiv/functor.lean
#### Estimated changes
modified src/data/equiv/functor.lean
- \+ *lemma* map_equiv_apply
- \+ *lemma* map_equiv_symm_apply
- \+ *lemma* map_equiv_apply
- \+ *lemma* map_equiv_symm_apply
- \+/\- *def* functor.map_equiv
- \+ *def* bifunctor.map_equiv
- \+ *def* map_equiv
- \+ *def* map_equiv
- \+/\- *def* functor.map_equiv

modified src/ring_theory/free_comm_ring.lean



## [2020-03-26 07:48:43](https://github.com/leanprover-community/mathlib/commit/ab33237)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified src/meta/expr.lean

modified src/tactic/core.lean

modified src/tactic/squeeze.lean
- \+ *def* squeeze_loc_attr_carrier

modified test/examples.lean

created test/packaged_goal.lean



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
modified src/set_theory/pgame.lean

modified src/tactic/core.lean

modified src/tactic/monotonicity/interactive.lean

modified src/tactic/solve_by_elim.lean

modified test/solve_by_elim.lean



## [2020-03-26 01:26:44](https://github.com/leanprover-community/mathlib/commit/2755eae)
chore(ci): only run on push ([#2237](https://github.com/leanprover-community/mathlib/pull/2237))
* chore(ci): only run on push
* update contribution docs
#### Estimated changes
modified .github/workflows/build.yml

modified docs/contribute/index.md



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
created src/algebra/homology/chain_complex.lean
- \+ *lemma* d_squared
- \+ *lemma* comm_at
- \+ *lemma* comm
- \+ *lemma* d_squared
- \+ *lemma* comm_at
- \+ *lemma* comm

created src/algebra/homology/homology.lean
- \+ *def* induced_map_on_cycles
- \+ *def* image_to_kernel_map
- \+ *def* cohomology

modified src/category_theory/concrete_category/basic.lean

created src/category_theory/differential_object.lean
- \+ *lemma* id_f
- \+ *lemma* comp_f
- \+ *def* id
- \+ *def* comp
- \+ *def* forget

modified src/category_theory/equivalence.lean
- \+ *lemma* pow_zero
- \+ *lemma* pow_one
- \+ *lemma* pow_minus_one
- \+ *def* pow

created src/category_theory/graded_object.lean
- \+ *lemma* id_apply
- \+ *lemma* comp_apply
- \+ *lemma* comap_eq_symm
- \+ *lemma* comap_eq_trans
- \+ *def* graded_object
- \+ *def* comap
- \+ *def* comap_id
- \+ *def* comap_comp
- \+ *def* comap_eq
- \+ *def* comap_equiv
- \+ *def* total

modified src/category_theory/limits/shapes/zero.lean

created src/category_theory/shift.lean
- \+ *lemma* shift_zero_eq_zero
- \+ *def* shift



## [2020-03-25 21:56:35](https://github.com/leanprover-community/mathlib/commit/e04892e)
feat(topology/metric_space/isometry): add_left/right, neg ([#2234](https://github.com/leanprover-community/mathlib/pull/2234))
Also add some lemmas from `equiv` namespace to `isometric`.
#### Estimated changes
modified src/topology/metric_space/isometry.lean
- \+ *lemma* ext
- \+ *lemma* trans_apply
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* symm_apply_eq
- \+ *lemma* eq_symm_apply



## [2020-03-25 19:18:04](https://github.com/leanprover-community/mathlib/commit/bb01537)
feat(topology/local_homeomorph): a few facts about `local_homeomorph` ([#2231](https://github.com/leanprover-community/mathlib/pull/2231))
* `eventually_inv_right`, `eventually_inv_left`
* `is_O_congr`, `is_o_congr`
#### Estimated changes
modified src/analysis/asymptotics.lean
- \+ *lemma* is_O_with_congr
- \+ *lemma* is_O_congr
- \+ *lemma* is_o_congr
- \+ *lemma* is_O_with_congr
- \+ *lemma* is_O_congr
- \+ *lemma* is_o_congr

modified src/topology/local_homeomorph.lean
- \+ *lemma* eventually_left_inverse
- \+ *lemma* eventually_left_inverse'
- \+ *lemma* eventually_right_inverse
- \+ *lemma* eventually_right_inverse'



## [2020-03-25 16:34:50](https://github.com/leanprover-community/mathlib/commit/05aa955)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-25 15:44:21](https://github.com/leanprover-community/mathlib/commit/bedb810)
feat(*): a few more theorems about `unique` and `subsingleton` ([#2230](https://github.com/leanprover-community/mathlib/pull/2230))
* feat(*): a few more theorems about `unique` and `subsingleton`
* Fix compile, fix two non-terminate `simp`s
* Update src/topology/metric_space/antilipschitz.lean
This lemma will go to another PR
#### Estimated changes
modified src/data/equiv/basic.lean

modified src/data/set/basic.lean
- \+ *lemma* subsingleton_univ
- \+ *lemma* eq_univ_of_nonempty
- \+ *lemma* set_cases

modified src/logic/unique.lean
- \+ *lemma* injective.comap_subsingleton
- \+ *lemma* nonempty_unique_or_exists_ne
- \+ *lemma* subsingleton_or_exists_ne
- \+ *def* surjective.unique
- \- *def* of_surjective

modified src/topology/basic.lean
- \+ *lemma* subsingleton.is_open
- \+ *lemma* subsingleton.is_closed

modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* of_subsingleton



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
modified src/data/equiv/basic.lean
- \+ *lemma* Pi_congr_left'_apply
- \+ *lemma* Pi_congr_left'_symm_apply
- \+ *def* Pi_congr_left'
- \+ *def* Pi_congr_left
- \+ *def* Pi_congr



## [2020-03-25 10:30:42](https://github.com/leanprover-community/mathlib/commit/83014bf)
chore(README): add Bryan; alphabetize ([#2238](https://github.com/leanprover-community/mathlib/pull/2238))
#### Estimated changes
modified README.md



## [2020-03-25 03:10:56](https://github.com/leanprover-community/mathlib/commit/d9083bc)
chore(algebra/ordered_field): merge `inv_pos` / `zero_lt_inv` with `inv_pos'` / `inv_neg` ([#2226](https://github.com/leanprover-community/mathlib/pull/2226))
* chore(algebra/ordered_field): merge `inv_pos` / `zero_lt_inv` with `inv_pos'` / `inv_neg`
Also move some lemmas to `linear_ordered_field`
* Update src/data/real/hyperreal.lean
* Fix compile
* Actually fix compile of `data/real/hyperreal`
#### Estimated changes
modified src/algebra/archimedean.lean

modified src/algebra/ordered_field.lean
- \+/\- *lemma* inv_pos
- \+/\- *lemma* inv_lt_zero
- \+/\- *lemma* inv_nonneg
- \+/\- *lemma* inv_nonpos
- \+/\- *lemma* inv_neg
- \+/\- *lemma* inv_le_inv_of_le
- \+/\- *lemma* div_nonneg'
- \+/\- *lemma* div_le_div_of_le_of_nonneg
- \+/\- *lemma* inv_pos
- \+/\- *lemma* inv_lt_zero
- \- *lemma* inv_pos'
- \- *lemma* inv_neg'
- \+/\- *lemma* inv_nonneg
- \+/\- *lemma* inv_nonpos
- \+/\- *lemma* inv_neg
- \+/\- *lemma* inv_le_inv_of_le
- \+/\- *lemma* div_nonneg'
- \+/\- *lemma* div_le_div_of_le_of_nonneg

modified src/analysis/calculus/mean_value.lean

modified src/analysis/calculus/tangent_cone.lean

modified src/analysis/complex/exponential.lean

modified src/analysis/convex/basic.lean

modified src/analysis/convex/cone.lean

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/analysis/specific_limits.lean

modified src/data/complex/exponential.lean

modified src/data/rat/cast.lean

modified src/data/real/basic.lean

modified src/data/real/hyperreal.lean
- \+/\- *lemma* omega_pos
- \+/\- *lemma* omega_pos

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/gromov_hausdorff.lean



## [2020-03-25 00:53:41](https://github.com/leanprover-community/mathlib/commit/24b82c9)
feat(tactic/core): trace_if_enabled ([#2209](https://github.com/leanprover-community/mathlib/pull/2209))
* feat(tactic/core): trace_for
* typo
* oops
* oops
* rename to trace_if_enabled
* trace_state_if_enabled
#### Estimated changes
modified src/tactic/chain.lean

modified src/tactic/core.lean

modified src/tactic/finish.lean

modified src/tactic/suggest.lean



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
modified src/tactic/basic.lean

created src/tactic/converter/apply_congr.lean

modified src/tactic/converter/interactive.lean

modified src/tactic/doc_commands.lean

created test/conv/apply_congr.lean



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
modified src/tactic/basic.lean

created src/tactic/show_term.lean



## [2020-03-24 16:01:34](https://github.com/leanprover-community/mathlib/commit/5f376b2)
feat(data/equiv): sigma_congr ([#2205](https://github.com/leanprover-community/mathlib/pull/2205))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *def* sigma_congr_left'
- \+ *def* sigma_congr



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
modified .github/PULL_REQUEST_TEMPLATE.md

modified README.md

modified archive/README.md

modified docs/commands.md
- \- *lemma* some_class.bar_assoc
- \- *theorem* alias1
- \- *theorem* alias2
- \- *def* f

modified docs/contribute/doc.md

modified docs/contribute/index.md

modified docs/extras/calc.md

modified docs/extras/conv.md

modified docs/extras/simp.md

modified docs/extras/tactic_writing.md

modified docs/extras/well_founded_recursion.md

modified docs/holes.md
- \- *def* foo
- \- *def* foo

modified docs/tactics.md
- \- *lemma* my_test
- \- *lemma* some_lemma
- \- *lemma* some_lemma_assoc
- \- *def* my_id

modified docs/theories/category_theory.md

modified src/category_theory/category/default.lean



## [2020-03-24 09:46:52](https://github.com/leanprover-community/mathlib/commit/b504430)
feat(linear_algebra): add range_le_ker_iff ([#2229](https://github.com/leanprover-community/mathlib/pull/2229))
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+ *lemma* range_le_ker_iff



## [2020-03-23 18:23:19](https://github.com/leanprover-community/mathlib/commit/6a7e55e)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-23 17:30:32](https://github.com/leanprover-community/mathlib/commit/9a9794d)
doc(data/int/gcd): attribution + module doc ([#2217](https://github.com/leanprover-community/mathlib/pull/2217))
* doc(data/int/gcd): attribution + module doc
* reword
#### Estimated changes
modified src/data/int/gcd.lean
- \+/\- *theorem* xgcd_aux_rec
- \+/\- *theorem* xgcd_aux_P
- \+/\- *theorem* gcd_eq_gcd_ab
- \+/\- *theorem* xgcd_aux_rec
- \+/\- *theorem* xgcd_aux_P
- \+/\- *theorem* gcd_eq_gcd_ab



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
modified src/data/set/function.lean
- \+ *lemma* maps_to.coe_restrict_apply
- \+ *theorem* maps_to.iterate
- \+ *theorem* maps_to.iterate_restrict
- \+ *def* maps_to.restrict

modified src/data/subtype.lean
- \+ *lemma* val_eq_coe

modified src/topology/constructions.lean
- \+ *lemma* continuous_subtype_coe

modified src/topology/metric_space/contracting.lean
- \+/\- *lemma* to_lipschitz_with
- \+ *lemma* one_sub_K_pos'
- \+ *lemma* one_sub_K_ne_zero
- \+ *lemma* one_sub_K_ne_top
- \+ *lemma* edist_inequality
- \+ *lemma* edist_le_of_fixed_point
- \+ *lemma* eq_or_edist_eq_top_of_fixed_points
- \+ *lemma* restrict
- \+ *lemma* efixed_point_is_fixed
- \+ *lemma* tendsto_iterate_efixed_point
- \+ *lemma* apriori_edist_iterate_efixed_point_le
- \+ *lemma* edist_efixed_point_le
- \+ *lemma* edist_efixed_point_lt_top
- \+ *lemma* efixed_point_eq_of_edist_lt_top
- \+ *lemma* efixed_point_mem'
- \+ *lemma* efixed_point_is_fixed'
- \+ *lemma* tendsto_iterate_efixed_point'
- \+ *lemma* apriori_edist_iterate_efixed_point_le'
- \+ *lemma* edist_efixed_point_le'
- \+ *lemma* edist_efixed_point_lt_top'
- \+ *lemma* efixed_point_eq_of_edist_lt_top'
- \+/\- *lemma* one_sub_K_pos
- \+/\- *lemma* fixed_point_is_fixed
- \+/\- *lemma* fixed_point_unique
- \+/\- *lemma* dist_fixed_point_le
- \+ *lemma* tendsto_iterate_fixed_point
- \+/\- *lemma* to_lipschitz_with
- \+/\- *lemma* one_sub_K_pos
- \+/\- *lemma* fixed_point_is_fixed
- \+/\- *lemma* fixed_point_unique
- \+/\- *lemma* dist_fixed_point_le
- \+/\- *theorem* exists_fixed_point
- \+ *theorem* exists_fixed_point'
- \+/\- *theorem* exists_fixed_point
- \+ *def* fixed_point

modified src/topology/metric_space/emetric_space.lean
- \+ *def* edist_lt_top_setoid

modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* edist_lt_top



## [2020-03-23 12:25:53](https://github.com/leanprover-community/mathlib/commit/25df50e)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified src/algebra/module.lean
- \+ *lemma* coe_mk
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub
- \+ *theorem* smul_eq_zero

modified src/analysis/convex/basic.lean
- \+ *lemma* convex_iff_forall_pos

created src/analysis/convex/cone.lean
- \+ *lemma* mem_coe
- \+ *lemma* mem_mk
- \+ *lemma* smul_mem
- \+ *lemma* add_mem
- \+ *lemma* smul_mem_iff
- \+ *lemma* convex
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* mem_Inf
- \+ *lemma* mem_bot
- \+ *lemma* mem_top
- \+ *lemma* map_map
- \+ *lemma* map_id
- \+ *lemma* comap_id
- \+ *lemma* comap_comap
- \+ *lemma* mem_comap
- \+ *lemma* mem_to_cone
- \+ *lemma* mem_to_cone'
- \+ *lemma* subset_to_cone
- \+ *lemma* to_cone_is_least
- \+ *lemma* to_cone_eq_Inf
- \+ *lemma* convex_hull_to_cone_is_least
- \+ *lemma* convex_hull_to_cone_eq_Inf
- \+ *lemma* step
- \+ *theorem* ext'
- \+ *theorem* ext
- \+ *theorem* exists_top
- \+ *theorem* riesz_extension
- \+ *theorem* exists_extension_of_le_sublinear
- \+ *def* map
- \+ *def* comap
- \+ *def* to_cone

created src/analysis/normed_space/hahn_banach.lean
- \+ *theorem* exists_extension_norm_eq

modified src/data/set/basic.lean
- \+ *theorem* set_coe.exists'
- \+ *theorem* bex_image_iff

modified src/linear_algebra/basic.lean
- \+ *lemma* disjoint_span_singleton
- \+ *lemma* refl_apply
- \+ *lemma* prod_symm
- \+ *lemma* prod_apply
- \+ *theorem* coe_of_le
- \+/\- *theorem* of_le_apply
- \+/\- *theorem* of_le_apply

created src/linear_algebra/linear_pmap.lean
- \+ *lemma* subtype.coe_prop
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* map_zero
- \+ *lemma* map_add
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* map_smul
- \+ *lemma* mk_apply
- \+ *lemma* domain_mk_span_singleton
- \+ *lemma* mk_span_singleton_apply
- \+ *lemma* fst_apply
- \+ *lemma* snd_apply
- \+ *lemma* neg_apply
- \+ *lemma* eq_of_le_of_domain_eq
- \+ *lemma* le_of_eq_locus_ge
- \+ *lemma* domain_mono
- \+ *lemma* domain_sup
- \+ *lemma* sup_apply
- \+ *lemma* sup_h_of_disjoint
- \+ *lemma* to_pmap_apply
- \+ *lemma* comp_pmap_apply
- \+ *lemma* coprod_apply
- \+ *def* eq_locus
- \+ *def* to_pmap
- \+ *def* comp_pmap
- \+ *def* cod_restrict
- \+ *def* comp
- \+ *def* coprod

modified src/order/basic.lean
- \+ *theorem* directed_on_image
- \+ *theorem* directed_on.mono
- \+ *theorem* directed.mono
- \- *theorem* directed_mono

modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* exists_between_of_forall_le



## [2020-03-23 04:27:27](https://github.com/leanprover-community/mathlib/commit/d3d78a9)
chore(ring_theory/algebra): generalize restrict_scalars to noncommutative algebras ([#2216](https://github.com/leanprover-community/mathlib/pull/2216))
#### Estimated changes
modified src/ring_theory/algebra.lean



## [2020-03-23 01:53:56](https://github.com/leanprover-community/mathlib/commit/fe40a15)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-23 01:05:38](https://github.com/leanprover-community/mathlib/commit/6aa5572)
feat(algebra/module): `f : E →+ F` is `ℚ`-linear ([#2215](https://github.com/leanprover-community/mathlib/pull/2215))
* feat(algebra/module): `f : E →+ F` is `ℚ`-linear
Also cleanup similar lemmas about `ℕ` and `ℤ`.
* Fix a typo
#### Estimated changes
modified src/algebra/direct_limit.lean
- \+/\- *lemma* directed_system
- \+/\- *lemma* directed_system

modified src/algebra/module.lean
- \+ *lemma* semimodule.smul_eq_smul
- \+ *lemma* semimodule.add_monoid_smul_eq_smul
- \+/\- *lemma* module.gsmul_eq_smul_cast
- \+ *lemma* add_monoid_hom.map_int_cast_smul
- \+ *lemma* add_monoid_hom.map_nat_cast_smul
- \+ *lemma* add_monoid_hom.map_rat_cast_smul
- \+ *lemma* add_monoid_hom.map_rat_module_smul
- \- *lemma* module.smul_eq_smul
- \- *lemma* module.add_monoid_smul_eq_smul
- \+/\- *lemma* module.gsmul_eq_smul_cast
- \- *lemma* add_monoid_hom.map_smul_cast
- \+ *def* add_monoid_hom.to_int_linear_map
- \+ *def* add_monoid_hom.to_rat_linear_map
- \- *def* is_add_group_hom.to_linear_map



## [2020-03-22 22:10:26](https://github.com/leanprover-community/mathlib/commit/b9ee94d)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified src/algebra/group/to_additive.lean

modified src/algebra/group/units.lean
- \+ *theorem* nat.add_units_eq_zero
- \- *theorem* nat.add_units_eq_one

modified src/data/complex/exponential.lean

modified src/data/polynomial.lean

modified src/linear_algebra/nonsingular_inverse.lean

modified src/measure_theory/bochner_integration.lean

modified src/measure_theory/measure_space.lean

modified src/tactic/transport.lean

modified src/topology/algebra/infinite_sum.lean



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
modified docs/commands.md

modified docs/contribute/doc.md

modified src/algebra/category/Mon/basic.lean

modified src/algebra/module.lean

modified src/deprecated/group.lean

modified src/group_theory/coset.lean

modified src/logic/basic.lean

modified src/meta/expr.lean

modified src/tactic/cache.lean

modified src/tactic/doc_commands.lean
- \+ *def* foo

modified src/tactic/elide.lean

modified src/tactic/ext.lean

modified src/tactic/finish.lean

created src/tactic/fix_reflect_string.lean

modified src/tactic/lint.lean

modified src/tactic/localized.lean

modified src/tactic/norm_cast.lean

modified src/tactic/norm_num.lean

created test/doc_commands.lean
- \+ *def* foo



## [2020-03-22 13:55:54](https://github.com/leanprover-community/mathlib/commit/4e46b30)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-22 13:06:37](https://github.com/leanprover-community/mathlib/commit/7d02c23)
chore(linear_algebra/*): rename copair, pair to coprod, prod ([#2213](https://github.com/leanprover-community/mathlib/pull/2213))
* chore(linear_algebra/*): rename copair, pair to coprod, prod
* add back mistakenly deleted lemma
* fix sensitivity, change comments to module docs
* docstrings, linting
* Update archive/sensitivity.lean
#### Estimated changes
modified archive/sensitivity.lean

modified src/linear_algebra/basic.lean
- \+ *lemma* ker_prod
- \+/\- *lemma* is_linear_map_prod_iso
- \- *lemma* ker_pair
- \+/\- *lemma* is_linear_map_prod_iso
- \+ *theorem* prod_apply
- \+ *theorem* fst_prod
- \+ *theorem* snd_prod
- \+/\- *theorem* pair_fst_snd
- \+ *theorem* coprod_apply
- \+ *theorem* coprod_inl
- \+ *theorem* coprod_inr
- \+ *theorem* coprod_inl_inr
- \+ *theorem* fst_eq_coprod
- \+ *theorem* snd_eq_coprod
- \+ *theorem* inl_eq_prod
- \+ *theorem* inr_eq_prod
- \+/\- *theorem* comap_le_comap_iff
- \+ *theorem* map_coprod_prod
- \+ *theorem* comap_prod_prod
- \+/\- *theorem* trans_apply
- \+/\- *theorem* symm_symm_apply
- \- *theorem* pair_apply
- \- *theorem* fst_pair
- \- *theorem* snd_pair
- \+/\- *theorem* pair_fst_snd
- \- *theorem* copair_apply
- \- *theorem* copair_inl
- \- *theorem* copair_inr
- \- *theorem* copair_inl_inr
- \- *theorem* fst_eq_copair
- \- *theorem* snd_eq_copair
- \- *theorem* inl_eq_pair
- \- *theorem* inr_eq_pair
- \+/\- *theorem* comap_le_comap_iff
- \- *theorem* map_copair_prod
- \- *theorem* comap_pair_prod
- \+/\- *theorem* trans_apply
- \+/\- *theorem* symm_symm_apply
- \+/\- *def* prod
- \+ *def* coprod
- \- *def* pair
- \- *def* copair
- \+/\- *def* prod

modified src/linear_algebra/basis.lean
- \+/\- *lemma* linear_independent.total_comp_repr
- \+/\- *lemma* linear_independent.image_subtype
- \+/\- *lemma* constr_smul
- \+/\- *lemma* is_basis_empty_bot
- \+/\- *lemma* linear_independent_iff_not_mem_span
- \+/\- *lemma* linear_independent_singleton
- \+/\- *lemma* linear_independent.total_comp_repr
- \+/\- *lemma* linear_independent.image_subtype
- \+/\- *lemma* constr_smul
- \+/\- *lemma* is_basis_empty_bot
- \+/\- *lemma* linear_independent_iff_not_mem_span
- \+/\- *lemma* linear_independent_singleton
- \+/\- *def* linear_independent.total_equiv
- \+/\- *def* linear_independent.total_equiv

modified src/linear_algebra/dimension.lean



## [2020-03-22 08:44:10](https://github.com/leanprover-community/mathlib/commit/3a71499)
feat(ring_theory/algebra) : generalize `rat.algebra_rat` to `division_ring` ([#2208](https://github.com/leanprover-community/mathlib/pull/2208))
Other changes:
* add lemmas about field inverse to `algebra/semiconj` and `algebra/commute`;
* drop `rat.cast`, define `instance : has_coe` right away to avoid
  accidental use of `rat.cast` in theorems;
* define `rat.cast_hom` instead of `is_ring_hom rat.cast`;
* generalize some theorems about from `field` to `division_ring`.
#### Estimated changes
modified src/algebra/commute.lean
- \+ *theorem* finv_left_iff
- \+ *theorem* finv_left
- \+ *theorem* finv_right_iff
- \+ *theorem* finv_right
- \+ *theorem* finv_finv
- \+ *theorem* div_right
- \+ *theorem* div_left

modified src/algebra/field_power.lean
- \+ *theorem* rat.cast_fpow
- \- *theorem* cast_fpow

modified src/algebra/semiconj.lean
- \+ *lemma* finv_symm_left_iff
- \+ *lemma* finv_symm_left

modified src/data/padics/padic_numbers.lean

modified src/data/rat/cast.lean
- \+ *lemma* coe_cast_hom
- \+/\- *theorem* cast_inv
- \+/\- *theorem* cast_div
- \+/\- *theorem* cast_mk
- \+/\- *theorem* cast_pow
- \+/\- *theorem* cast_nonneg
- \+/\- *theorem* cast_mk
- \+/\- *theorem* cast_inv
- \+/\- *theorem* cast_div
- \+/\- *theorem* cast_pow
- \+/\- *theorem* cast_nonneg
- \+ *def* cast_hom

modified src/ring_theory/algebra.lean



## [2020-03-22 04:38:42](https://github.com/leanprover-community/mathlib/commit/9485a85)
fix(linear_algebra/basic): make R explicit in linear_equiv.refl ([#2161](https://github.com/leanprover-community/mathlib/pull/2161))
* fix(linear_algebra/basic): make R explicit in linear_equiv.refl
* getting mathlib to compile again
* better variablism
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+/\- *def* congr_right
- \+/\- *def* congr_right

modified src/topology/algebra/module.lean



## [2020-03-22 02:00:48](https://github.com/leanprover-community/mathlib/commit/19de416)
doc(ring_theory/adjoin_root): add docstring ([#2211](https://github.com/leanprover-community/mathlib/pull/2211))
* docstring for adjoin_root
* adding some quotes
#### Estimated changes
modified src/ring_theory/adjoin_root.lean



## [2020-03-21 14:18:51-07:00](https://github.com/leanprover-community/mathlib/commit/09401b7)
revert accidental push to master
#### Estimated changes
modified src/tactic/chain.lean

modified src/tactic/core.lean

modified src/tactic/finish.lean

modified src/tactic/suggest.lean

modified src/tactic/tidy.lean



## [2020-03-21 14:00:51-07:00](https://github.com/leanprover-community/mathlib/commit/3375126)
feat(tactic/core): trace_for
#### Estimated changes
modified src/tactic/chain.lean

modified src/tactic/core.lean

modified src/tactic/finish.lean

modified src/tactic/suggest.lean

modified src/tactic/tidy.lean



## [2020-03-21 19:24:58](https://github.com/leanprover-community/mathlib/commit/af0cf30)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified .github/workflows/build.yml

modified .gitignore

created scripts/lint_mathlib.lean

modified scripts/mk_all.sh

deleted scripts/mk_nolint.lean

modified scripts/rm_all.sh

modified scripts/update_nolints.sh

modified src/logic/basic.lean

modified src/logic/function.lean

modified src/meta/expr.lean

modified src/tactic/lint.lean

modified test/lint.lean



## [2020-03-21 10:35:34](https://github.com/leanprover-community/mathlib/commit/dd85db0)
doc(docs/contribute/index.md): remove obsolete recommendation to use lean-3.7.2 branch ([#2206](https://github.com/leanprover-community/mathlib/pull/2206))
#### Estimated changes
modified docs/contribute/index.md



## [2020-03-21 08:46:38](https://github.com/leanprover-community/mathlib/commit/bc84a20)
chore(leanpkg.toml): Lean 3.7.2c ([#2203](https://github.com/leanprover-community/mathlib/pull/2203))
* chore(leanpkg.toml): Lean 3.7.2c
Lean 3.7.1c had a bug that prevented Lean on windows from importing oleans properly (see https://github.com/leanprover-community/lean/pull/155). This is fixed in Lean 3.7.2c.
* update contribute/index.md
#### Estimated changes
modified docs/contribute/index.md

modified leanpkg.toml



## [2020-03-21 02:10:50](https://github.com/leanprover-community/mathlib/commit/34bac8d)
feat(category_theory): add naturality_assoc simp lemma ([#2200](https://github.com/leanprover-community/mathlib/pull/2200))
#### Estimated changes
modified src/category_theory/natural_transformation.lean



## [2020-03-20 23:38:07](https://github.com/leanprover-community/mathlib/commit/99ba8f4)
chore(category_theory): change monoidal_of_has_finite_products to use binary products ([#2190](https://github.com/leanprover-community/mathlib/pull/2190))
* chore(category_theory): change monoidal_of_has_finite_products to use binary products
* remove some simp annotations for now
* fixes
#### Estimated changes
modified src/category_theory/monoidal/of_has_finite_products.lean
- \+ *lemma* left_unitor_hom
- \+ *lemma* left_unitor_inv
- \+ *lemma* right_unitor_hom
- \+ *lemma* right_unitor_inv
- \+ *lemma* associator_hom
- \+ *lemma* left_unitor_hom
- \+ *lemma* right_unitor_hom
- \+ *lemma* left_unitor_inv
- \+ *lemma* right_unitor_inv
- \+ *lemma* associator_hom
- \+/\- *def* monoidal_of_has_finite_products
- \+/\- *def* monoidal_of_has_finite_coproducts
- \+/\- *def* monoidal_of_has_finite_products
- \+/\- *def* monoidal_of_has_finite_coproducts



## [2020-03-20 21:22:50](https://github.com/leanprover-community/mathlib/commit/9420167)
feat(category_theory): unbundled functors and lax monoidal functors ([#2193](https://github.com/leanprover-community/mathlib/pull/2193))
* feat(category_theory): unbundled functors and lax monoidal functors
* doc string
#### Estimated changes
modified src/category_theory/functor.lean

created src/category_theory/functorial.lean
- \+ *lemma* map_functorial_obj
- \+ *def* map
- \+ *def* of
- \+ *def* functorial_comp

created src/category_theory/monoidal/functorial.lean
- \+ *def* of



## [2020-03-20 18:53:45](https://github.com/leanprover-community/mathlib/commit/b224943)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified src/data/finsupp.lean
- \- *lemma* mul_def
- \- *lemma* support_mul
- \- *lemma* one_def
- \- *lemma* single_mul_single
- \- *lemma* prod_single

created src/data/finsupp/pointwise.lean
- \+ *lemma* mul_apply
- \+ *lemma* support_mul

created src/data/monoid_algebra.lean
- \+ *lemma* mul_def
- \+ *lemma* support_mul
- \+ *lemma* one_def
- \+ *lemma* single_mul_single
- \+ *lemma* prod_single
- \+ *lemma* mul_def
- \+ *lemma* support_mul
- \+ *lemma* one_def
- \+ *lemma* single_mul_single
- \+ *lemma* prod_single
- \+ *def* monoid_algebra
- \+ *def* add_monoid_algebra

modified src/data/mv_polynomial.lean
- \+/\- *def* mv_polynomial
- \+ *def* coeff_coe_to_fun
- \+/\- *def* mv_polynomial

modified src/data/polynomial.lean
- \+/\- *lemma* single_eq_C_mul_X
- \+/\- *lemma* single_eq_C_mul_X
- \+/\- *def* polynomial
- \+ *def* monomial
- \+/\- *def* C
- \+/\- *def* X
- \+/\- *def* polynomial
- \+/\- *def* C
- \+/\- *def* X

modified src/linear_algebra/finsupp.lean

modified src/ring_theory/polynomial.lean

modified src/ring_theory/power_series.lean
- \- *def* monomial



## [2020-03-20 15:01:46](https://github.com/leanprover-community/mathlib/commit/0f1b465)
feat(category_theory/limits): the isomorphism expressing preservation of chosen limits ([#2192](https://github.com/leanprover-community/mathlib/pull/2192))
* feat(category_theory/limits): the isomorphism expressing preservation of chosen limits
* Update src/category_theory/limits/limits.lean
#### Estimated changes
modified src/category_theory/limits/limits.lean
- \+ *def* cone_point_unique_up_to_iso
- \+ *def* cone_point_unique_up_to_iso

modified src/category_theory/limits/preserves.lean
- \+ *def* preserves_limit_iso
- \+ *def* preserves_colimit_iso



## [2020-03-20 12:24:26](https://github.com/leanprover-community/mathlib/commit/c66c4af)
chore(algebra/Module/monoidal): add the simp lemmas for unitors and associativity ([#2196](https://github.com/leanprover-community/mathlib/pull/2196))
* feat(algebra/category/Module/monoidal): simp lemmas
* oops
* depressingly easy
* order of arguments
#### Estimated changes
modified src/algebra/category/Module/basic.lean
- \+ *def* of_self_iso
- \- *def* of_self

modified src/algebra/category/Module/monoidal.lean
- \+ *lemma* left_unitor_hom
- \+ *lemma* right_unitor_hom
- \+ *lemma* associator_hom



## [2020-03-20 10:05:42](https://github.com/leanprover-community/mathlib/commit/d93e0dd)
chore(category_theory): missing simp lemmas ([#2188](https://github.com/leanprover-community/mathlib/pull/2188))
* chore(category_theory): missing simp lemmas
* Apply suggestions from code review
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
modified src/category_theory/types.lean
- \+ *lemma* map_inv_map_hom_apply
- \+ *lemma* map_hom_map_inv_apply



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
modified src/category_theory/discrete_category.lean

modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* ext
- \+ *lemma* equivalence_preserves_zero_morphisms

modified src/tactic/ext.lean
- \- *lemma* ext



## [2020-03-20 05:08:55](https://github.com/leanprover-community/mathlib/commit/cc04132)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-20 03:59:59](https://github.com/leanprover-community/mathlib/commit/6c97ce0)
feat(category_theory): some natural isomorphisms related to composition by functors ([#2189](https://github.com/leanprover-community/mathlib/pull/2189))
* feat(category_theory): some natural isomorphisms related to composition by functors
* tidy up
* cleanup
* fix
* better design
#### Estimated changes
modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *lemma* pair_obj_left
- \+/\- *lemma* pair_obj_right
- \+/\- *lemma* map_pair_left
- \+/\- *lemma* map_pair_right
- \+/\- *lemma* pair_obj_left
- \+/\- *lemma* pair_obj_right
- \+/\- *lemma* map_pair_left
- \+/\- *lemma* map_pair_right
- \+/\- *def* map_pair
- \+ *def* map_pair_iso
- \+ *def* pair_comp
- \- *def* pair_function
- \+/\- *def* map_pair

modified src/category_theory/pempty.lean
- \+ *def* empty_ext



## [2020-03-20 01:35:59](https://github.com/leanprover-community/mathlib/commit/d12bbc0)
feat(data/zmod): lemmas about totient and zmod ([#2158](https://github.com/leanprover-community/mathlib/pull/2158))
* feat(data/zmod): lemmas about totient and zmod
* docstring
* Changes based on Johan's comments
* fix build
* subsingleton (units(zmod 2))
#### Estimated changes
modified src/data/fintype.lean

modified src/data/nat/totient.lean
- \+ *lemma* card_units_eq_totient
- \+ *theorem* totient_zero

modified src/data/zmod/basic.lean
- \+ *lemma* cast_unit_of_coprime
- \+ *def* unit_of_coprime

modified src/data/zmod/quadratic_reciprocity.lean

modified src/field_theory/finite.lean
- \+ *lemma* zmod.pow_totient
- \+ *lemma* nat.modeq.pow_totient



## [2020-03-19 23:15:04](https://github.com/leanprover-community/mathlib/commit/3dd95a2)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-19 21:56:33](https://github.com/leanprover-community/mathlib/commit/1a398a7)
docs(category_theory/limits): adding many docstrings ([#2185](https://github.com/leanprover-community/mathlib/pull/2185))
* lots of comments!
* remove #lint
* Apply suggestions from code review
lots of missing "co"s
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
modified src/category_theory/limits/limits.lean



## [2020-03-19 18:52:34](https://github.com/leanprover-community/mathlib/commit/344a41e)
feat(data/finset): monotone bijection from fin k ([#2163](https://github.com/leanprover-community/mathlib/pull/2163))
* feat(data/finset): increasing bijection between fin k and an ordered finset
* fix build
* fix linter
* make argument explicit
* add equiv for fintype
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *lemma* dite_comp_equiv_update

modified src/data/finset.lean
- \+ *lemma* sorted_zero_eq_min'
- \+ *lemma* sorted_last_eq_max'
- \+ *lemma* bij_on_mono_of_fin
- \+/\- *theorem* min'_mem
- \+/\- *theorem* min'_le
- \+/\- *theorem* le_min'
- \+/\- *theorem* max'_mem
- \+/\- *theorem* le_max'
- \+/\- *theorem* max'_le
- \+/\- *theorem* min'_lt_max'
- \+/\- *theorem* sort_sorted_lt
- \+/\- *theorem* sort_sorted_lt
- \+/\- *theorem* min'_mem
- \+/\- *theorem* min'_le
- \+/\- *theorem* le_min'
- \+/\- *theorem* max'_mem
- \+/\- *theorem* le_max'
- \+/\- *theorem* max'_le
- \+/\- *theorem* min'_lt_max'
- \+/\- *def* min'
- \+/\- *def* max'
- \+ *def* mono_of_fin
- \+/\- *def* min'
- \+/\- *def* max'

modified src/data/fintype.lean
- \+ *lemma* finset.card_fin
- \+ *lemma* fintype.card_finset

modified src/data/list/sort.lean
- \+ *lemma* nth_le_of_sorted_of_le

modified src/group_theory/sylow.lean



## [2020-03-19 16:32:37](https://github.com/leanprover-community/mathlib/commit/b3ef685)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified docs/tactics.md

modified scripts/nolints.txt

modified src/algebra/associated.lean

modified src/algebra/direct_limit.lean

modified src/algebra/order_functions.lean

modified src/algebra/ordered_group.lean

modified src/algebra/ordered_ring.lean

modified src/algebra/punit_instances.lean

modified src/analysis/ODE/gronwall.lean

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/fderiv.lean

modified src/analysis/calculus/mean_value.lean

modified src/analysis/calculus/tangent_cone.lean

modified src/analysis/calculus/times_cont_diff.lean

modified src/analysis/complex/polynomial.lean

modified src/analysis/normed_space/bounded_linear_maps.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/analysis/normed_space/real_inner_product.lean

modified src/analysis/specific_limits.lean

modified src/category_theory/limits/lattice.lean

modified src/data/analysis/filter.lean

modified src/data/equiv/denumerable.lean

modified src/data/finset.lean

modified src/data/list/min_max.lean

modified src/data/multiset.lean

modified src/data/mv_polynomial.lean

modified src/data/nat/enat.lean

modified src/data/pequiv.lean

modified src/data/pnat/basic.lean

modified src/data/pnat/factors.lean

modified src/data/polynomial.lean

modified src/data/rat/order.lean

modified src/data/real/basic.lean
- \+ *lemma* Sup_def
- \+ *lemma* Inf_def
- \+/\- *theorem* Sup_empty
- \+/\- *theorem* Sup_of_not_bdd_above
- \+/\- *theorem* Sup_univ
- \+/\- *theorem* Inf_empty
- \+/\- *theorem* Inf_of_not_bdd_below
- \+/\- *theorem* Sup_empty
- \+/\- *theorem* Sup_of_not_bdd_above
- \+/\- *theorem* Sup_univ
- \+/\- *theorem* Inf_empty
- \+/\- *theorem* Inf_of_not_bdd_below

modified src/data/real/ennreal.lean

modified src/data/real/ereal.lean

modified src/data/real/hyperreal.lean
- \+/\- *theorem* is_st_Sup
- \+/\- *theorem* st_eq_Sup
- \+/\- *theorem* is_st_Sup
- \+/\- *theorem* st_eq_Sup

modified src/data/real/nnreal.lean

modified src/data/rel.lean

modified src/data/semiquot.lean

modified src/data/set/basic.lean

modified src/data/set/disjointed.lean

modified src/data/set/finite.lean

modified src/data/set/intervals/basic.lean

modified src/data/set/intervals/disjoint.lean

modified src/data/set/lattice.lean

modified src/data/setoid.lean

modified src/field_theory/mv_polynomial.lean

modified src/geometry/manifold/basic_smooth_bundle.lean

modified src/geometry/manifold/manifold.lean

modified src/geometry/manifold/smooth_manifold_with_corners.lean

modified src/group_theory/congruence.lean

modified src/group_theory/monoid_localization.lean

modified src/group_theory/submonoid.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/basis.lean

modified src/linear_algebra/dimension.lean

modified src/linear_algebra/finsupp.lean

modified src/linear_algebra/finsupp_vector_space.lean

modified src/measure_theory/ae_eq_fun.lean

modified src/measure_theory/bochner_integration.lean

modified src/measure_theory/borel_space.lean

modified src/measure_theory/decomposition.lean

modified src/measure_theory/giry_monad.lean

modified src/measure_theory/indicator_function.lean

modified src/measure_theory/integration.lean

modified src/measure_theory/l1_space.lean

modified src/measure_theory/lebesgue_measure.lean

modified src/measure_theory/measurable_space.lean

modified src/measure_theory/measure_space.lean

modified src/measure_theory/outer_measure.lean

modified src/measure_theory/simple_func_dense.lean

modified src/order/boolean_algebra.lean
- \+ *theorem* inf_compl_eq_bot
- \+ *theorem* compl_inf_eq_bot
- \+ *theorem* sup_compl_eq_top
- \+ *theorem* compl_sup_eq_top
- \+ *theorem* compl_unique
- \+ *theorem* compl_top
- \+ *theorem* compl_bot
- \+ *theorem* compl_compl'
- \+ *theorem* compl_inj
- \+ *theorem* compl_inj_iff
- \+ *theorem* compl_inf
- \+ *theorem* compl_sup
- \+ *theorem* compl_le_compl
- \+ *theorem* compl_le_compl_iff_le
- \+ *theorem* le_compl_of_le_compl
- \+ *theorem* compl_le_of_compl_le
- \+ *theorem* compl_le_iff_compl_le
- \+ *theorem* boolean_algebra.sub_le_sub
- \- *theorem* inf_neg_eq_bot
- \- *theorem* neg_inf_eq_bot
- \- *theorem* sup_neg_eq_top
- \- *theorem* neg_sup_eq_top
- \- *theorem* neg_unique
- \- *theorem* neg_top
- \- *theorem* neg_bot
- \- *theorem* neg_neg
- \- *theorem* neg_eq_neg_of_eq
- \- *theorem* neg_eq_neg_iff
- \- *theorem* neg_inf
- \- *theorem* neg_sup
- \- *theorem* neg_le_neg
- \- *theorem* neg_le_neg_iff_le
- \- *theorem* le_neg_of_le_neg
- \- *theorem* neg_le_of_neg_le
- \- *theorem* neg_le_iff_neg_le
- \- *theorem* sub_le_sub

modified src/order/bounded_lattice.lean

modified src/order/bounds.lean

modified src/order/complete_boolean_algebra.lean
- \+ *theorem* compl_infi
- \+ *theorem* compl_supr
- \+ *theorem* compl_Inf
- \+ *theorem* compl_Sup
- \- *theorem* neg_infi
- \- *theorem* neg_supr
- \- *theorem* neg_Inf
- \- *theorem* neg_Sup

modified src/order/complete_lattice.lean
- \+ *lemma* is_lub.Sup_eq
- \+ *lemma* is_glb.Inf_eq
- \+ *lemma* is_lub.supr_eq
- \+ *lemma* is_glb.infi_eq

modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* is_lub.cSup_eq
- \+ *lemma* is_greatest.cSup_eq
- \+ *lemma* is_glb.cInf_eq
- \+ *lemma* is_least.cInf_eq

modified src/order/copy.lean

modified src/order/filter/bases.lean

modified src/order/filter/basic.lean

modified src/order/filter/extr.lean

modified src/order/filter/lift.lean

modified src/order/filter/pointwise.lean

modified src/order/fixed_points.lean

modified src/order/galois_connection.lean

modified src/order/lattice.lean
- \+/\- *lemma* directed_of_mono
- \+/\- *lemma* directed_of_inf
- \+/\- *lemma* directed_of_mono
- \- *lemma* directed_of_antimono
- \+/\- *lemma* directed_of_inf
- \+ *theorem* le_antisymm'
- \+ *theorem* lattice.ext
- \+/\- *theorem* sup_eq_max
- \+/\- *theorem* inf_eq_min
- \- *theorem* ext
- \+/\- *theorem* sup_eq_max
- \+/\- *theorem* inf_eq_min

modified src/order/liminf_limsup.lean

modified src/ring_theory/adjoin.lean

modified src/ring_theory/algebra.lean

modified src/ring_theory/algebra_operations.lean

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/ideal_operations.lean

modified src/ring_theory/ideals.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/noetherian.lean

modified src/ring_theory/polynomial.lean

modified src/ring_theory/power_series.lean

modified src/ring_theory/unique_factorization_domain.lean

modified src/set_theory/cardinal.lean

modified src/set_theory/schroeder_bernstein.lean

modified src/tactic/converter/binders.lean
- \- *theorem* Inf_image
- \- *theorem* Sup_image

modified src/tactic/interval_cases.lean

modified src/topology/algebra/group.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/monoid.lean

modified src/topology/algebra/open_subgroup.lean

modified src/topology/algebra/ordered.lean

modified src/topology/algebra/ring.lean

modified src/topology/algebra/uniform_ring.lean

modified src/topology/bases.lean

modified src/topology/basic.lean

modified src/topology/bounded_continuous_function.lean

modified src/topology/category/Top/limits.lean

modified src/topology/constructions.lean

modified src/topology/continuous_on.lean

modified src/topology/dense_embedding.lean

modified src/topology/instances/ennreal.lean

modified src/topology/instances/real.lean

modified src/topology/local_extr.lean

modified src/topology/maps.lean

modified src/topology/metric_space/baire.lean

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/completion.lean

modified src/topology/metric_space/emetric_space.lean

modified src/topology/metric_space/gluing.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/metric_space/hausdorff_distance.lean

modified src/topology/opens.lean

modified src/topology/order.lean

modified src/topology/separation.lean

modified src/topology/sequences.lean

modified src/topology/stone_cech.lean

modified src/topology/subset_properties.lean

modified src/topology/uniform_space/absolute_value.lean

modified src/topology/uniform_space/basic.lean

modified src/topology/uniform_space/cauchy.lean

modified src/topology/uniform_space/compare_reals.lean

modified src/topology/uniform_space/complete_separated.lean

modified src/topology/uniform_space/completion.lean

modified src/topology/uniform_space/pi.lean

modified src/topology/uniform_space/separation.lean

modified src/topology/uniform_space/uniform_embedding.lean



## [2020-03-19 10:59:44](https://github.com/leanprover-community/mathlib/commit/a20f378)
chore(category_theory/images): fix some minor problems ([#2182](https://github.com/leanprover-community/mathlib/pull/2182))
* chore(category_theory/images): fix some minor problems
* minor
* oops, misplaced comment
#### Estimated changes
modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* as_factor_thru_image
- \- *lemma* image.as_c
- \- *lemma* image.c_ι
- \- *def* image.c



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
modified src/category_theory/epi_mono.lean

modified src/category_theory/limits/shapes/constructions/pullbacks.lean

modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* mono_of_is_limit_parallel_pair
- \+ *lemma* epi_of_is_colimit_parallel_pair

modified src/category_theory/limits/shapes/images.lean

created src/category_theory/limits/shapes/regular_mono.lean



## [2020-03-19 06:18:29](https://github.com/leanprover-community/mathlib/commit/445e332)
chore(category_theory/isomorphism): use @[simps] ([#2181](https://github.com/leanprover-community/mathlib/pull/2181))
#### Estimated changes
modified src/category_theory/isomorphism.lean
- \- *lemma* refl_hom
- \- *lemma* refl_inv
- \- *lemma* trans_hom
- \- *lemma* trans_inv
- \+/\- *def* refl
- \+/\- *def* trans
- \+/\- *def* refl
- \+/\- *def* trans



## [2020-03-19 03:47:29](https://github.com/leanprover-community/mathlib/commit/e2b0e38)
chore(category_theory/binary_products): tweak spacing in notation ([#2184](https://github.com/leanprover-community/mathlib/pull/2184))
#### Estimated changes
modified src/category_theory/limits/shapes/binary_products.lean



## [2020-03-19 01:12:44](https://github.com/leanprover-community/mathlib/commit/034685b)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-18 23:51:31](https://github.com/leanprover-community/mathlib/commit/00d9f1d)
feat(topology/algebra/infinite_sum): dot notation, cauchy sequences ([#2171](https://github.com/leanprover-community/mathlib/pull/2171))
* more material on infinite sums
* minor fixes
* cleanup
* yury's comments
#### Estimated changes
modified src/analysis/normed_space/banach.lean

modified src/analysis/normed_space/basic.lean
- \+ *lemma* edist_eq_coe_nnnorm_sub
- \+ *lemma* cauchy_seq_finset_iff_vanishing_norm
- \+/\- *lemma* summable_iff_vanishing_norm
- \+ *lemma* cauchy_seq_finset_of_norm_bounded
- \+ *lemma* cauchy_seq_finset_of_summable_norm
- \+ *lemma* has_sum_of_subseq_of_summable
- \+/\- *lemma* norm_tsum_le_tsum_norm
- \+/\- *lemma* summable_of_norm_bounded
- \+ *lemma* summable_of_nnnorm_bounded
- \+ *lemma* summable_of_summable_nnnorm
- \+/\- *lemma* summable_iff_vanishing_norm
- \+/\- *lemma* summable_of_norm_bounded
- \+/\- *lemma* norm_tsum_le_tsum_norm

modified src/analysis/specific_limits.lean
- \+ *lemma* nnreal.tendsto_inverse_at_top_nhds_0_nat
- \+ *lemma* nnreal.tendsto_const_div_at_top_nhds_0_nat
- \+ *lemma* dist_partial_sum_le_of_le_geometric
- \+ *lemma* cauchy_seq_finset_of_geometric_bound
- \+ *lemma* norm_sub_le_of_geometric_bound_of_has_sum

modified src/data/option/basic.lean
- \+ *def* cases_on'

modified src/data/real/cardinality.lean

modified src/measure_theory/outer_measure.lean

modified src/measure_theory/probability_mass_function.lean
- \+/\- *lemma* summable_coe
- \+/\- *lemma* summable_coe

modified src/order/liminf_limsup.lean

modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* summable.has_sum
- \+ *lemma* has_sum.summable
- \+/\- *lemma* summable_zero
- \+ *lemma* tsum_eq_zero_of_not_summable
- \+ *lemma* equiv.has_sum_iff
- \+ *lemma* equiv.summable_iff
- \+ *lemma* has_sum.tendsto_sum_nat
- \+/\- *lemma* has_sum_unique
- \+ *lemma* has_sum.add
- \+ *lemma* summable.add
- \+ *lemma* has_sum.sigma
- \+ *lemma* summable.sigma
- \+ *lemma* has_sum.sigma_of_has_sum
- \+ *lemma* has_sum.has_sum_of_sum_eq
- \+ *lemma* has_sum.has_sum_ne_zero
- \+/\- *lemma* tsum_eq_has_sum
- \+ *lemma* summable.has_sum_iff
- \+ *lemma* has_sum.neg
- \+ *lemma* summable.neg
- \+ *lemma* has_sum.sub
- \+ *lemma* summable.sub
- \+ *lemma* has_sum.mul_left
- \+ *lemma* has_sum.mul_right
- \+ *lemma* summable.mul_left
- \+ *lemma* summable.mul_right
- \+ *lemma* has_sum_mul_left_iff
- \+ *lemma* has_sum_mul_right_iff
- \+ *lemma* summable_mul_left_iff
- \+ *lemma* summable_mul_right_iff
- \+ *lemma* tsum_le_tsum_of_inj
- \+ *lemma* tsum_nonneg
- \+ *lemma* tsum_nonpos
- \+ *lemma* summable_iff_cauchy_seq_finset
- \+ *lemma* cauchy_seq_finset_iff_vanishing
- \+/\- *lemma* summable_iff_vanishing
- \+ *lemma* summable.summable_of_eq_zero_or_self
- \+ *lemma* summable.summable_comp_of_injective
- \+ *lemma* summable.sigma_factor
- \+ *lemma* summable.sigma'
- \+ *lemma* tsum_sigma'
- \- *lemma* has_sum_tsum
- \- *lemma* summable_spec
- \+/\- *lemma* summable_zero
- \- *lemma* tendsto_sum_nat_of_has_sum
- \- *lemma* has_sum_add
- \- *lemma* summable_add
- \- *lemma* has_sum_sigma
- \- *lemma* summable_sigma
- \- *lemma* has_sum_of_has_sum
- \- *lemma* has_sum_of_has_sum_ne_zero
- \+/\- *lemma* has_sum_unique
- \+/\- *lemma* tsum_eq_has_sum
- \- *lemma* has_sum_iff_of_summable
- \- *lemma* has_sum_neg
- \- *lemma* summable_neg
- \- *lemma* has_sum_sub
- \- *lemma* summable_sub
- \- *lemma* has_sum_mul_left
- \- *lemma* has_sum_mul_right
- \- *lemma* summable_mul_left
- \- *lemma* summable_mul_right
- \- *lemma* summable_iff_cauchy
- \+/\- *lemma* summable_iff_vanishing
- \- *lemma* summable_of_summable_of_sub
- \- *lemma* summable_comp_of_summable_of_injective
- \- *def* option.cases_on'

modified src/topology/instances/ennreal.lean
- \+ *lemma* tsum_comp_le_tsum_of_inj
- \+ *lemma* tsum_comp_le_tsum_of_inj

modified src/topology/instances/nnreal.lean

modified src/topology/uniform_space/cauchy.lean
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
modified leanpkg.toml

modified scripts/deploy_docs.sh

modified src/algebra/direct_limit.lean

modified src/algebra/direct_sum.lean
- \+/\- *theorem* to_group.unique
- \+/\- *theorem* to_group.unique

modified src/algebra/euclidean_domain.lean

modified src/algebra/ordered_group.lean

modified src/algebra/ordered_ring.lean

modified src/algebra/ring.lean
- \+ *lemma* comp
- \+ *lemma* comp

modified src/analysis/normed_space/banach.lean

modified src/analysis/normed_space/real_inner_product.lean

modified src/category/monad/writer.lean

modified src/category_theory/limits/preserves.lean

modified src/category_theory/monad/limits.lean
- \+/\- *def* has_limits_of_reflective
- \+/\- *def* has_limits_of_reflective

modified src/data/fintype.lean

modified src/data/mv_polynomial.lean

modified src/data/polynomial.lean

modified src/deprecated/group.lean
- \+ *lemma* comp
- \+ *lemma* comp
- \+ *lemma* comp

modified src/field_theory/splitting_field.lean

modified src/group_theory/free_abelian_group.lean

modified src/group_theory/free_group.lean

modified src/group_theory/presented_group.lean

modified src/group_theory/quotient_group.lean

modified src/group_theory/subgroup.lean

modified src/group_theory/submonoid.lean
- \+ *lemma* additive.is_add_submonoid
- \+ *lemma* multiplicative.is_submonoid

modified src/ring_theory/algebra.lean

modified src/ring_theory/localization.lean

modified src/set_theory/ordinal.lean

modified src/tactic/alias.lean

modified src/tactic/core.lean

modified src/tactic/lint.lean

modified src/tactic/reassoc_axiom.lean

modified src/tactic/squeeze.lean

modified src/tactic/transport.lean

modified src/topology/algebra/group_completion.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/ring.lean

modified src/topology/algebra/uniform_group.lean
- \+ *lemma* is_Z_bilin.comp_hom

modified src/topology/algebra/uniform_ring.lean



## [2020-03-18 18:36:06](https://github.com/leanprover-community/mathlib/commit/69f7bf8)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-18 17:04:44](https://github.com/leanprover-community/mathlib/commit/5f62d3b)
feat(topology/bounded_continuous_functions): more general uniform convergence ([#2165](https://github.com/leanprover-community/mathlib/pull/2165))
* feat(topology/buonded_continuous_functions): more general uniform convergence
* yury's comments
#### Estimated changes
modified src/topology/bounded_continuous_function.lean
- \+ *lemma* continuous_within_at_of_locally_uniform_limit_of_continuous_within_at
- \+ *lemma* continuous_at_of_locally_uniform_limit_of_continuous_at
- \+ *lemma* continuous_on_of_locally_uniform_limit_of_continuous_on
- \+ *lemma* continuous_on_of_uniform_limit_of_continuous_on
- \+/\- *lemma* continuous_of_locally_uniform_limit_of_continuous
- \+/\- *lemma* continuous_of_uniform_limit_of_continuous
- \+/\- *lemma* continuous_of_locally_uniform_limit_of_continuous
- \+/\- *lemma* continuous_of_uniform_limit_of_continuous
- \+/\- *def* bounded_continuous_function
- \+/\- *def* bounded_continuous_function

modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.continuous_within_at
- \+ *lemma* continuous_on_empty
- \+ *lemma* continuous_on.continuous_at
- \+/\- *theorem* continuous_on_iff_is_closed
- \+/\- *theorem* continuous_on_iff_is_closed

modified src/topology/metric_space/basic.lean
- \+ *lemma* ball_zero
- \+ *theorem* continuous_within_at_iff
- \+ *theorem* continuous_on_iff
- \+ *theorem* continuous_at_iff'
- \+ *theorem* continuous_within_at_iff'
- \+ *theorem* continuous_on_iff'

modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* ball_zero



## [2020-03-18 14:55:37](https://github.com/leanprover-community/mathlib/commit/739e831)
feat(analysis/complex/exponential): real powers of nnreals ([#2164](https://github.com/leanprover-community/mathlib/pull/2164))
* feat(analysis/complex/exponential): real powers of nnreals
* cleanup
* mean inequalities in nnreal
* mean inequalities
* use < instead of >
* reviewer's comments
#### Estimated changes
modified src/analysis/complex/exponential.lean
- \+ *lemma* cpow_eq_pow
- \+ *lemma* cpow_eq_zero_iff
- \+ *lemma* rpow_eq_pow
- \+ *lemma* rpow_eq_zero_iff_of_nonneg
- \+ *lemma* rpow_nat_inv_pow_nat
- \+ *lemma* continuous_at_rpow
- \+ *lemma* rpow_eq_pow
- \+ *lemma* coe_rpow
- \+ *lemma* rpow_zero
- \+ *lemma* rpow_eq_zero_iff
- \+ *lemma* zero_rpow
- \+ *lemma* rpow_one
- \+ *lemma* one_rpow
- \+ *lemma* rpow_add
- \+ *lemma* rpow_mul
- \+ *lemma* rpow_neg
- \+ *lemma* rpow_nat_cast
- \+ *lemma* mul_rpow
- \+ *lemma* one_le_rpow
- \+ *lemma* rpow_le_rpow
- \+ *lemma* rpow_lt_rpow
- \+ *lemma* rpow_lt_rpow_of_exponent_lt
- \+ *lemma* rpow_le_rpow_of_exponent_le
- \+ *lemma* rpow_lt_rpow_of_exponent_gt
- \+ *lemma* rpow_le_rpow_of_exponent_ge
- \+ *lemma* rpow_le_one
- \+ *lemma* one_lt_rpow
- \+ *lemma* rpow_lt_one
- \+ *lemma* pow_nat_rpow_nat_inv
- \+ *lemma* rpow_nat_inv_pow_nat
- \+ *lemma* continuous_at_rpow
- \+ *lemma* filter.tendsto.nnrpow

modified src/analysis/mean_inequalities.lean



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
modified src/algebra/category/Group/adjunctions.lean
- \+/\- *def* adj
- \+/\- *def* adj

modified src/algebra/category/Group/basic.lean
- \+ *lemma* as_hom_apply
- \+ *lemma* as_hom_injective
- \+ *lemma* int_hom_ext
- \+ *lemma* injective_of_mono
- \+ *def* as_hom

created src/algebra/category/Group/images.lean
- \+ *lemma* image.fac
- \+ *lemma* image.lift_fac
- \+ *def* image
- \+ *def* image.ι
- \+ *def* factor_thru_image
- \+ *def* mono_factorisation

modified src/algebra/group_power.lean
- \+ *lemma* gsmul_int_int
- \+ *lemma* gsmul_int_one

modified src/category_theory/concrete_category/basic.lean
- \+ *lemma* concrete_category.hom_ext
- \+ *lemma* concrete_category.mono_of_injective

modified src/category_theory/limits/shapes/images.lean

modified src/category_theory/limits/types.lean
- \+ *lemma* image.lift_fac
- \+ *def* image
- \+ *def* image.ι
- \+ *def* mono_factorisation

modified src/group_theory/subgroup.lean
- \+ *def* monoid_hom.range_subtype_val
- \+ *def* monoid_hom.range_factorization



## [2020-03-18 00:03:33](https://github.com/leanprover-community/mathlib/commit/6af37d3)
fix(category_theory/limits): require explicit instances of has_zero_morphisms ([#2169](https://github.com/leanprover-community/mathlib/pull/2169))
* fix(category_theory/limits): require explicit instances of has_zero_morphisms
* Fix unused arguments
#### Estimated changes
modified src/algebra/category/Module/basic.lean

modified src/category_theory/limits/shapes/kernels.lean

modified src/category_theory/limits/shapes/zero.lean



## [2020-03-17 14:49:48+01:00](https://github.com/leanprover-community/mathlib/commit/422f640)
fix(scripts/mk_nolint): fix error introduced by [#2090](https://github.com/leanprover-community/mathlib/pull/2090) ([#2170](https://github.com/leanprover-community/mathlib/pull/2170))
#### Estimated changes
modified scripts/mk_nolint.lean



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
modified scripts/mk_nolint.lean

modified src/analysis/normed_space/basic.lean

modified src/category_theory/limits/shapes/finite_limits.lean

modified src/category_theory/limits/shapes/images.lean

modified src/data/fin_enum.lean

modified src/ring_theory/principal_ideal_domain.lean

modified src/tactic/lint.lean

modified src/topology/subset_properties.lean

modified test/lint.lean



## [2020-03-17 01:31:51](https://github.com/leanprover-community/mathlib/commit/496939c)
feat(data/real/*nnreal): add division lemmas ([#2167](https://github.com/leanprover-community/mathlib/pull/2167))
* feat(data/real/*nnreal): add division lemmas
* fix build
* elim_cast
* another elim_cast
#### Estimated changes
modified src/data/real/ennreal.lean
- \+/\- *lemma* none_eq_top
- \+/\- *lemma* some_eq_coe
- \+ *lemma* lt_iff_exists_add_pos_lt
- \+ *lemma* lt_sub_iff_add_lt
- \+ *lemma* mul_div_assoc
- \+ *lemma* div_one
- \+ *lemma* div_eq_top
- \+/\- *lemma* le_div_iff_mul_le
- \+/\- *lemma* div_le_iff_le_mul
- \+/\- *lemma* none_eq_top
- \+/\- *lemma* some_eq_coe
- \- *lemma* coe_sub_infty
- \+/\- *lemma* le_div_iff_mul_le
- \+/\- *lemma* div_le_iff_le_mul

modified src/data/real/nnreal.lean
- \+ *lemma* coe_ne_zero
- \+ *lemma* lt_sub_iff_add_lt
- \+ *lemma* div_lt_iff
- \+ *lemma* div_lt_one_of_lt
- \+ *lemma* mul_div_assoc'
- \+ *lemma* div_add_div
- \+ *lemma* inv_eq_one_div
- \+ *lemma* div_mul_eq_mul_div
- \+ *lemma* add_div'
- \+ *lemma* div_add'
- \+ *lemma* one_div_eq_inv
- \+ *lemma* one_div_div
- \+ *lemma* div_eq_mul_one_div
- \+ *lemma* div_div_eq_mul_div
- \+ *lemma* div_div_eq_div_mul
- \+ *lemma* div_eq_div_iff
- \+ *lemma* div_eq_iff
- \+ *lemma* eq_div_iff
- \+ *theorem* mul_ne_zero'
- \+ *theorem* div_pow
- \+ *theorem* pow_eq_zero
- \+ *theorem* pow_ne_zero

modified src/topology/instances/ennreal.lean



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
modified src/category_theory/epi_mono.lean
- \+ *lemma* split_mono.id
- \+ *lemma* split_epi.id
- \+ *def* retraction
- \+ *def* section_

modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* parallel_pair_obj_zero
- \+ *lemma* parallel_pair_obj_one
- \+ *lemma* cone_of_split_mono_π_app_zero
- \+ *lemma* cone_of_split_mono_π_app_one
- \+ *lemma* cocone_of_split_epi_ι_app_one
- \+ *lemma* cocone_of_split_epi_ι_app_zero
- \+ *def* cone_of_split_mono
- \+ *def* split_mono_equalizes
- \+ *def* cocone_of_split_epi
- \+ *def* split_epi_coequalizes

modified src/category_theory/limits/shapes/kernels.lean

modified src/category_theory/limits/shapes/zero.lean
- \- *def* zero_of_zero_object



## [2020-03-16 21:22:20](https://github.com/leanprover-community/mathlib/commit/bc087d8)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-16 20:04:17](https://github.com/leanprover-community/mathlib/commit/7a5496f)
chore(order/liminf_limsup): lint and cleanup the file ([#2162](https://github.com/leanprover-community/mathlib/pull/2162))
* chore(order/liminf_limsup): lint and cleanup the file, add some statements
* use eventually_mono
#### Estimated changes
modified src/order/filter/basic.lean
- \+ *lemma* eventually.congr
- \+ *lemma* eventually.congr_iff

modified src/order/liminf_limsup.lean
- \+ *lemma* limsup_congr
- \+ *lemma* liminf_congr
- \+ *lemma* limsup_const
- \+ *lemma* liminf_const
- \+ *lemma* eventually_lt_of_lt_liminf
- \+ *lemma* eventually_lt_of_limsup_lt
- \+/\- *theorem* Limsup_le_of_le
- \+/\- *theorem* le_Liminf_of_le
- \+/\- *theorem* Liminf_le_Limsup
- \+/\- *theorem* Limsup_le_of_le
- \+/\- *theorem* le_Liminf_of_le
- \+/\- *theorem* Liminf_le_Limsup



## [2020-03-16 19:22:51](https://github.com/leanprover-community/mathlib/commit/007b575)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified docs/contribute/doc.md

modified docs/extras.md

modified docs/extras/simp.md

modified src/logic/basic.lean

modified src/tactic/abel.lean

modified src/tactic/alias.lean
- \+ *theorem* alias1
- \+ *theorem* alias2

modified src/tactic/apply_fun.lean

modified src/tactic/cache.lean
- \+ *def* my_id

modified src/tactic/clear.lean

modified src/tactic/core.lean

modified src/tactic/derive_inhabited.lean

created src/tactic/doc_commands.lean
- \+ *def* string.hash
- \+ *def* f

modified src/tactic/elide.lean

modified src/tactic/explode.lean

modified src/tactic/ext.lean
- \+/\- *lemma* foo.ext
- \+/\- *lemma* foo.ext_iff
- \+ *lemma* my_collection.ext
- \+ *lemma* my_collection.ext
- \+ *lemma* my_collection.ext
- \+ *lemma* my_collection.ext
- \+/\- *lemma* foo.ext
- \+/\- *lemma* foo.ext_iff
- \+/\- *lemma* foo.ext
- \+/\- *lemma* foo.ext_iff

modified src/tactic/fin_cases.lean

modified src/tactic/find.lean

modified src/tactic/finish.lean

modified src/tactic/hint.lean

modified src/tactic/interactive.lean

modified src/tactic/interval_cases.lean

deleted src/tactic/library_note.lean
- \- *def* string.hash

modified src/tactic/lift.lean

modified src/tactic/linarith.lean

modified src/tactic/lint.lean

modified src/tactic/localized.lean

modified src/tactic/monotonicity/interactive.lean

modified src/tactic/norm_cast.lean

modified src/tactic/norm_num.lean
- \+ *def* a
- \+ *def* normed_a

modified src/tactic/omega/main.lean

modified src/tactic/pi_instances.lean

modified src/tactic/push_neg.lean

modified src/tactic/rcases.lean

modified src/tactic/reassoc_axiom.lean
- \+ *lemma* some_lemma
- \+ *lemma* some_lemma_assoc
- \+ *lemma* some_class.bar_assoc
- \- *lemma* foo_bar
- \- *lemma* foo_bar_assoc
- \+/\- *theorem* category_theory.reassoc_of
- \+/\- *theorem* category_theory.reassoc_of

modified src/tactic/rename.lean

modified src/tactic/rename_var.lean

modified src/tactic/replacer.lean

modified src/tactic/restate_axiom.lean

modified src/tactic/rewrite.lean

modified src/tactic/ring.lean

modified src/tactic/ring_exp.lean

modified src/tactic/simp_rw.lean

modified src/tactic/simpa.lean

modified src/tactic/simps.lean
- \+ *lemma* refl_to_fun
- \+ *lemma* refl_inv_fun
- \- *lemma* {simp_lemma}.
- \+ *def* refl

modified src/tactic/solve_by_elim.lean

modified src/tactic/squeeze.lean

modified src/tactic/suggest.lean

modified src/tactic/tauto.lean

modified src/tactic/tfae.lean

modified src/tactic/tidy.lean

modified src/tactic/where.lean



## [2020-03-16 15:33:24](https://github.com/leanprover-community/mathlib/commit/04c7381)
doc(docs/install/windows): emphasize projects link ([#2150](https://github.com/leanprover-community/mathlib/pull/2150))
You can't use mathlib in the test project created in step 6. I've seen a couple of Windows users get tripped up here.
#### Estimated changes
modified docs/install/windows.md



## [2020-03-16 14:46:06](https://github.com/leanprover-community/mathlib/commit/555528e)
feat(category_theory/image): comparison maps for precomposition ([#2153](https://github.com/leanprover-community/mathlib/pull/2153))
* feat(category_theory/image): comparison maps for precomposition
* remove duplicate argument
* unused argument
#### Estimated changes
modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* image.pre_comp_comp
- \+ *def* image.eq_to_hom
- \+ *def* image.eq_to_iso
- \+ *def* image.pre_comp



## [2020-03-16 09:18:06](https://github.com/leanprover-community/mathlib/commit/1e38cb1)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-16 08:00:01](https://github.com/leanprover-community/mathlib/commit/ff84bf4)
feat(category_theory/monad/limits): forgetful creates colimits ([#2138](https://github.com/leanprover-community/mathlib/pull/2138))
* forgetful creates colimits
* tidy up proofs
* add docs
* suggestions from review
#### Estimated changes
modified src/category_theory/monad/limits.lean
- \+ *lemma* commuting
- \+/\- *def* forget_creates_limits
- \+ *def* γ
- \+ *def* c
- \+ *def* lambda
- \+ *def* cocone_point
- \+ *def* forget_creates_colimits_of_monad_preserves
- \+/\- *def* forget_creates_limits



## [2020-03-16 05:54:25](https://github.com/leanprover-community/mathlib/commit/4aed862)
feat(analysis/normed_space/operator_norm): completeness of the space of operators ([#2160](https://github.com/leanprover-community/mathlib/pull/2160))
* feat(analysis/normed_space/operator_norm): completeness of the space of operators
* add some comments
#### Estimated changes
modified src/analysis/normed_space/operator_norm.lean



## [2020-03-16 03:42:23](https://github.com/leanprover-community/mathlib/commit/d8e5d99)
feat(category_theory/limits): Convenience methods for building limit (co)forks ([#2155](https://github.com/leanprover-community/mathlib/pull/2155))
* feat(category_theory/limits): Convenience methods for building limit (co)forks
* Formatting
* Rework a proof about kernels
* feat(category_theory/limits): kernel forks
#### Estimated changes
modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* fork.is_limit.mk
- \+ *def* cofork.is_colimit.mk

modified src/category_theory/limits/shapes/kernels.lean



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
modified src/category_theory/limits/over.lean

modified src/category_theory/limits/shapes/constructions/equalizers.lean

modified src/category_theory/limits/shapes/constructions/pullbacks.lean
- \+ *def* has_limit_cospan_of_has_limit_pair_of_has_limit_parallel_pair
- \+ *def* has_pullbacks_of_has_binary_products_of_has_equalizers
- \+ *def* has_colimit_span_of_has_colimit_pair_of_has_colimit_parallel_pair
- \+ *def* has_pushouts_of_has_binary_coproducts_of_has_coequalizers

modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* mk_π_app_left
- \+ *lemma* mk_π_app_right
- \+ *lemma* mk_π_app_one
- \+ *lemma* mk_ι_app_left
- \+ *lemma* mk_ι_app_right
- \+ *lemma* mk_ι_app_zero
- \- *lemma* mk_left
- \- *lemma* mk_right
- \+ *def* is_limit.mk
- \+ *def* is_colimit.mk



## [2020-03-15 23:30:43](https://github.com/leanprover-community/mathlib/commit/fbe2ce0)
feat(category_theory/limits): kernel forks ([#2156](https://github.com/leanprover-community/mathlib/pull/2156))
#### Estimated changes
modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* kernel_fork.condition
- \+ *lemma* kernel_fork.app_one
- \+ *lemma* cokernel_cofork.condition
- \+ *lemma* cokernel_cofork.app_zero



## [2020-03-15 21:15:49](https://github.com/leanprover-community/mathlib/commit/87f8ab2)
chore(nnreal): replace coe_le with coe_le_coe ([#2159](https://github.com/leanprover-community/mathlib/pull/2159))
#### Estimated changes
modified src/analysis/convex/topology.lean

modified src/analysis/mean_inequalities.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/specific_limits.lean

modified src/data/real/ennreal.lean

modified src/data/real/nnreal.lean

modified src/measure_theory/decomposition.lean

modified src/measure_theory/simple_func_dense.lean

modified src/topology/instances/ennreal.lean

modified src/topology/metric_space/basic.lean



## [2020-03-15 15:21:50](https://github.com/leanprover-community/mathlib/commit/7104132)
chore(field_theory/finite): spelling mistake ([#2157](https://github.com/leanprover-community/mathlib/pull/2157))
#### Estimated changes
modified src/field_theory/finite.lean



## [2020-03-15 04:22:33](https://github.com/leanprover-community/mathlib/commit/0cbfbab)
refactor(logic/function): inv_fun takes a nonempty instance instead of inhabited ([#2148](https://github.com/leanprover-community/mathlib/pull/2148))
#### Estimated changes
modified src/logic/function.lean
- \+/\- *lemma* inv_fun_neg
- \+/\- *lemma* inv_fun_neg
- \+/\- *theorem* inv_fun_on_neg
- \+/\- *theorem* inv_fun_on_neg



## [2020-03-15 03:04:18](https://github.com/leanprover-community/mathlib/commit/b314df2)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified scripts/nolints.txt

modified src/category_theory/monad/algebra.lean
- \+ *def* id
- \+ *def* comp
- \+ *def* forget
- \+ *def* cofree
- \+ *def* adj

modified src/category_theory/monad/basic.lean



## [2020-03-15 00:49:28](https://github.com/leanprover-community/mathlib/commit/e4bf0bf)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
created docs/tutorial/category_theory/Ab.lean

modified scripts/nolints.txt

modified src/algebra/category/CommRing/colimits.lean
- \+/\- *def* desc_morphism
- \+/\- *def* desc_morphism

renamed src/algebra/category/Group.lean to src/algebra/category/Group/basic.lean
- \+ *lemma* one_apply
- \+ *lemma* one_apply

created src/algebra/category/Group/colimits.lean
- \+ *lemma* quot_zero
- \+ *lemma* quot_neg
- \+ *lemma* quot_add
- \+ *lemma* cocone_naturality
- \+ *lemma* cocone_naturality_components
- \+ *def* colimit_setoid
- \+ *def* colimit_type
- \+ *def* colimit
- \+ *def* cocone_fun
- \+ *def* cocone_morphism
- \+ *def* colimit_cocone
- \+ *def* desc_fun_lift
- \+ *def* desc_fun
- \+ *def* desc_morphism
- \+ *def* colimit_is_colimit

created src/algebra/category/Group/default.lean

created src/algebra/category/Group/limits.lean
- \+ *def* limit_π_add_monoid_hom
- \+ *def* limit
- \+ *def* limit_is_limit

created src/algebra/category/Group/zero.lean

modified src/algebra/category/Mon/colimits.lean
- \+/\- *def* desc_morphism
- \+/\- *def* desc_morphism



## [2020-03-14 21:19:35](https://github.com/leanprover-community/mathlib/commit/2e781eb)
doc(docs/install/*): emphasize projects link ([#2151](https://github.com/leanprover-community/mathlib/pull/2151))
#### Estimated changes
modified docs/install/debian_details.md

modified docs/install/linux.md

modified docs/install/macos.md



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
modified src/category_theory/comma.lean
- \+ *lemma* iterated_slice_forward_forget
- \+ *lemma* iterated_slice_backward_forget_forget
- \+ *def* iterated_slice_forward
- \+ *def* iterated_slice_backward
- \+ *def* iterated_slice_equiv

modified src/category_theory/limits/over.lean
- \+ *lemma* over_prod_pair_left
- \+ *lemma* over_prod_pair_hom
- \+ *lemma* over_prod_fst_left
- \+ *lemma* over_prod_snd_left
- \+ *lemma* over_prod_map_left
- \+ *def* over_product_of_pullbacks

modified src/category_theory/limits/shapes/constructions/equalizers.lean

modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *lemma* condition
- \+ *lemma* mk_left
- \+ *lemma* mk_right
- \+/\- *lemma* condition



## [2020-03-14 18:14:17](https://github.com/leanprover-community/mathlib/commit/cc39a15)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-14 17:09:36](https://github.com/leanprover-community/mathlib/commit/7b2be40)
refactor(data/equiv/algebra): split ([#2147](https://github.com/leanprover-community/mathlib/pull/2147))
* refactor(data/equiv/algebra): split
I want to use `≃*` without importing `ring`.
* Update src/data/equiv/ring.lean
#### Estimated changes
modified src/algebra/category/CommRing/basic.lean

modified src/algebra/category/Mon/basic.lean

modified src/algebra/free_monoid.lean

modified src/algebra/semiconj.lean

modified src/category_theory/endomorphism.lean

modified src/category_theory/single_obj.lean

deleted src/data/equiv/algebra.lean
- \- *lemma* coe_units_equiv_ne_zero
- \- *lemma* zero_def
- \- *lemma* one_def
- \- *lemma* mul_def
- \- *lemma* add_def
- \- *lemma* inv_def
- \- *lemma* neg_def
- \- *lemma* map_mul
- \- *lemma* apply_symm_apply
- \- *lemma* symm_apply_apply
- \- *lemma* map_one
- \- *lemma* map_eq_one_iff
- \- *lemma* map_ne_one_iff
- \- *lemma* to_monoid_hom_apply_symm_to_monoid_hom_apply
- \- *lemma* symm_to_monoid_hom_apply_to_monoid_hom_apply
- \- *lemma* map_inv
- \- *lemma* ext
- \- *lemma* add_equiv.map_sub
- \- *lemma* coe_mul_equiv
- \- *lemma* coe_add_equiv
- \- *lemma* apply_symm_apply
- \- *lemma* symm_apply_apply
- \- *lemma* image_eq_preimage
- \- *lemma* map_mul
- \- *lemma* map_one
- \- *lemma* map_add
- \- *lemma* map_zero
- \- *lemma* map_eq_one_iff
- \- *lemma* map_eq_zero_iff
- \- *lemma* map_ne_one_iff
- \- *lemma* map_ne_zero_iff
- \- *lemma* map_neg
- \- *lemma* map_sub
- \- *lemma* map_neg_one
- \- *lemma* to_ring_hom_apply_symm_to_ring_hom_apply
- \- *lemma* symm_to_ring_hom_apply_to_ring_hom_apply
- \- *lemma* ext
- \- *theorem* to_equiv_symm
- \- *def* units_equiv_ne_zero
- \- *def* mk'
- \- *def* refl
- \- *def* symm
- \- *def* trans
- \- *def* to_monoid_hom
- \- *def* mul_aut
- \- *def* to_perm
- \- *def* to_perm
- \- *def* to_units
- \- *def* map_equiv
- \- *def* to_ring_hom
- \- *def* of
- \- *def* to_ring_equiv
- \- *def* of'
- \- *def* ring_aut
- \- *def* to_add_aut
- \- *def* to_mul_aut
- \- *def* to_perm

created src/data/equiv/mul_add.lean
- \+ *lemma* map_mul
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* map_one
- \+ *lemma* map_eq_one_iff
- \+ *lemma* map_ne_one_iff
- \+ *lemma* to_monoid_hom_apply
- \+ *lemma* map_inv
- \+ *lemma* ext
- \+ *lemma* add_equiv.map_sub
- \+ *theorem* to_equiv_symm
- \+ *def* mk'
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans
- \+ *def* to_monoid_hom
- \+ *def* mul_aut
- \+ *def* to_perm
- \+ *def* to_perm
- \+ *def* to_units
- \+ *def* map_equiv

created src/data/equiv/ring.lean
- \+ *lemma* coe_mul_equiv
- \+ *lemma* coe_add_equiv
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* image_eq_preimage
- \+ *lemma* map_mul
- \+ *lemma* map_one
- \+ *lemma* map_add
- \+ *lemma* map_zero
- \+ *lemma* map_eq_one_iff
- \+ *lemma* map_eq_zero_iff
- \+ *lemma* map_ne_one_iff
- \+ *lemma* map_ne_zero_iff
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* map_neg_one
- \+ *lemma* to_ring_hom_apply_symm_to_ring_hom_apply
- \+ *lemma* symm_to_ring_hom_apply_to_ring_hom_apply
- \+ *lemma* ext
- \+ *lemma* coe_units_equiv_ne_zero
- \+ *def* to_ring_hom
- \+ *def* of
- \+ *def* to_ring_equiv
- \+ *def* of'
- \+ *def* ring_aut
- \+ *def* to_add_aut
- \+ *def* to_mul_aut
- \+ *def* to_perm
- \+ *def* units_equiv_ne_zero

created src/data/equiv/transfer_instance.lean
- \+ *lemma* zero_def
- \+ *lemma* one_def
- \+ *lemma* mul_def
- \+ *lemma* add_def
- \+ *lemma* inv_def
- \+ *lemma* neg_def

modified src/data/mv_polynomial.lean

modified src/field_theory/finite.lean

modified src/group_theory/submonoid.lean

modified src/linear_algebra/basic.lean

modified src/ring_theory/free_comm_ring.lean

modified src/ring_theory/free_ring.lean

modified src/ring_theory/ideal_operations.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/maps.lean

modified src/ring_theory/noetherian.lean

modified src/topology/algebra/group.lean



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
modified src/algebra/category/Group.lean
- \+ *lemma* ext
- \+ *lemma* ext

created src/algebra/category/Group/Z_Module_equivalence.lean

modified src/algebra/category/Module/basic.lean

modified src/algebra/module.lean
- \+ *lemma* module_ext
- \+ *lemma* to_add_monoid_hom_coe
- \+ *lemma* module.add_monoid_smul_eq_smul
- \+/\- *lemma* gsmul_eq_smul
- \+ *lemma* module.gsmul_eq_smul_cast
- \+ *lemma* module.gsmul_eq_smul
- \+ *lemma* add_monoid_hom.map_int_module_smul
- \+ *lemma* add_monoid_hom.map_smul_cast
- \+/\- *lemma* gsmul_eq_smul
- \+ *def* to_add_monoid_hom
- \+ *def* nat_semimodule
- \+ *def* int_module
- \+/\- *def* is_add_group_hom.to_linear_map
- \+/\- *def* is_add_group_hom.to_linear_map



## [2020-03-14 12:47:55](https://github.com/leanprover-community/mathlib/commit/d313d14)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-14 11:28:34](https://github.com/leanprover-community/mathlib/commit/559921a)
feat(algebra/category/Group): the free-forgetful adjunction for AddCommGroup ([#2141](https://github.com/leanprover-community/mathlib/pull/2141))
* feat(algebra/category/Group): the free-forgetful adjunction for AddCommGroup
* fixes
* Update src/group_theory/free_abelian_group.lean
* oops
#### Estimated changes
created src/algebra/category/Group/adjunctions.lean
- \+ *lemma* free_obj_coe
- \+ *lemma* free_map_coe
- \+ *def* free
- \+ *def* adj

modified src/algebra/group/hom.lean

modified src/group_theory/free_abelian_group.lean
- \+ *lemma* hom_equiv_apply
- \+ *lemma* hom_equiv_symm_apply
- \+ *lemma* map_of
- \+ *lemma* lift_comp
- \+ *def* hom_equiv
- \- *def* universal



## [2020-03-14 09:21:38](https://github.com/leanprover-community/mathlib/commit/465f599)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified src/algebra/category/Module/basic.lean
- \+ *def* of_self
- \+ *def* linear_equiv.to_Module_iso
- \+ *def* to_linear_equiv
- \+ *def* linear_equiv_iso_Group_iso
- \+/\- *def* kernel_is_limit
- \+/\- *def* kernel_is_limit

created src/algebra/category/Module/monoidal.lean
- \+ *lemma* tensor_id
- \+ *lemma* tensor_comp
- \+ *lemma* associator_naturality
- \+ *lemma* pentagon
- \+ *lemma* left_unitor_naturality
- \+ *lemma* right_unitor_naturality
- \+ *lemma* triangle
- \+ *def* tensor_obj
- \+ *def* tensor_hom
- \+ *def* associator
- \+ *def* left_unitor
- \+ *def* right_unitor

modified src/category_theory/limits/types.lean
- \+/\- *lemma* types_limit_π
- \+/\- *lemma* types_limit_map
- \+/\- *lemma* types_limit_π
- \+/\- *lemma* types_limit_map
- \+ *def* limit_
- \+ *def* limit_is_limit_
- \+ *def* colimit_
- \+ *def* colimit_is_colimit_
- \- *def* limit
- \- *def* limit_is_limit
- \- *def* colimit
- \- *def* colimit_is_colimit

modified src/linear_algebra/basic.lean
- \+ *theorem* trans_apply
- \+/\- *def* refl
- \+/\- *def* symm
- \+/\- *def* trans
- \+/\- *def* refl
- \+/\- *def* symm
- \+/\- *def* trans

modified src/linear_algebra/tensor_product.lean
- \+ *theorem* ext_threefold
- \+ *theorem* ext_fourfold
- \+ *theorem* lid_tmul
- \+ *theorem* rid_tmul
- \+ *theorem* assoc_tmul



## [2020-03-14 04:10:31](https://github.com/leanprover-community/mathlib/commit/3d621b5)
refactor(ring_theory/subring): use bundled homs ([#2144](https://github.com/leanprover-community/mathlib/pull/2144))
#### Estimated changes
modified src/field_theory/subfield.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/subring.lean
- \+ *lemma* is_subring.coe_subtype
- \+/\- *lemma* image_closure
- \+/\- *lemma* image_closure
- \+ *def* is_subring.subtype



## [2020-03-14 01:59:21](https://github.com/leanprover-community/mathlib/commit/ade1ee3)
feat(category_theory/limits): derive has_binary_products from has_limit (pair X Y) ([#2139](https://github.com/leanprover-community/mathlib/pull/2139))
* feat(category_theory/limits): derive has_binary_products from has_limit (pair X Y)
* Rename *_of_diagram to diagram_iso_*
#### Estimated changes
modified src/category_theory/limits/shapes/binary_products.lean
- \+ *def* diagram_iso_pair
- \+ *def* has_binary_products_of_has_limit_pair
- \+ *def* has_binary_coproducts_of_has_colimit_pair

modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* diagram_iso_parallel_pair
- \+ *def* has_equalizers_of_has_limit_parallel_pair
- \+ *def* has_coequalizers_of_has_colimit_parallel_pair

modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* diagram_iso_cospan
- \+ *def* diagram_iso_span
- \+ *def* has_pullbacks_of_has_limit_cospan
- \+ *def* has_pushouts_of_has_colimit_span



## [2020-03-13 18:31:09](https://github.com/leanprover-community/mathlib/commit/49f5fb8)
chore(algebra/category/CommRing/limits): avoid `is_ring_hom` ([#2142](https://github.com/leanprover-community/mathlib/pull/2142))
define a `ring_hom` instead
#### Estimated changes
modified src/algebra/category/CommRing/limits.lean
- \+ *def* limit_π_ring_hom



## [2020-03-13 12:20:20](https://github.com/leanprover-community/mathlib/commit/32c2768)
chore(linear_algebra/basic): simplify two proofs ([#2123](https://github.com/leanprover-community/mathlib/pull/2123))
* chore(linear_algebra/basic): simplify two proofs
Also drop `linear_map.congr_right` in favor of
`linear_equiv.congr_right`. I'll restore the deleted `congr_right`
as `comp_map : (M₂ →ₗ[R] M₃) →ₗ[R] (M →ₗ[R] M₂) →ₗ[R] (M →ₗ[R] M₃)` soon.
* Fix compile
* Restore `congr_right` under the name `comp_right`.
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+ *theorem* coe_supr_of_directed
- \+/\- *theorem* mem_supr_of_directed
- \- *theorem* Union_coe_of_directed
- \+/\- *theorem* mem_supr_of_directed
- \+ *def* comp_right
- \+/\- *def* conj
- \- *def* congr_right
- \+/\- *def* conj

modified src/ring_theory/ideal_operations.lean

modified src/ring_theory/ideals.lean

modified src/ring_theory/noetherian.lean

modified src/ring_theory/polynomial.lean



## [2020-03-13 10:18:27](https://github.com/leanprover-community/mathlib/commit/aec62dc)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified src/algebra/big_operators.lean
- \+/\- *lemma* monoid_hom.map_prod
- \+ *lemma* ring_hom.map_prod
- \+ *lemma* ring_hom.map_sum
- \+/\- *lemma* monoid_hom.map_prod

modified src/algebra/direct_limit.lean
- \+/\- *lemma* lift_zero
- \+/\- *lemma* lift_one
- \+/\- *lemma* lift_add
- \+/\- *lemma* lift_neg
- \+/\- *lemma* lift_sub
- \+/\- *lemma* lift_mul
- \+/\- *lemma* lift_pow
- \+/\- *lemma* lift_zero
- \+/\- *lemma* lift_one
- \+/\- *lemma* lift_add
- \+/\- *lemma* lift_neg
- \+/\- *lemma* lift_sub
- \+/\- *lemma* lift_mul
- \+/\- *lemma* lift_pow
- \+ *def* lift_hom
- \+/\- *def* lift
- \+/\- *def* lift

modified src/algebra/pi_instances.lean

modified src/algebra/ring.lean
- \+ *lemma* coe_mk

modified src/ring_theory/adjoin.lean

modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* mk_self
- \+ *lemma* mk_C
- \+/\- *lemma* eval₂_root
- \+/\- *lemma* is_root_root
- \+/\- *lemma* lift_mk
- \+/\- *lemma* lift_root
- \+/\- *lemma* lift_of
- \+/\- *lemma* coe_injective
- \+/\- *lemma* mul_div_root_cancel
- \+/\- *lemma* mk_self
- \+/\- *lemma* eval₂_root
- \+/\- *lemma* is_root_root
- \+/\- *lemma* lift_mk
- \+/\- *lemma* lift_root
- \+/\- *lemma* lift_of
- \+/\- *lemma* coe_injective
- \+/\- *lemma* mul_div_root_cancel
- \+/\- *def* adjoin_root
- \+/\- *def* mk
- \+/\- *def* of
- \+/\- *def* root
- \+/\- *def* lift
- \+/\- *def* adjoin_root
- \+/\- *def* mk
- \+/\- *def* root
- \+/\- *def* of
- \+/\- *def* lift

modified src/ring_theory/free_comm_ring.lean
- \+ *lemma* coe_lift_hom
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_one
- \+/\- *lemma* map_of
- \+/\- *lemma* map_add
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_pow
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_one
- \+/\- *lemma* map_of
- \+/\- *lemma* map_add
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_pow
- \+ *def* lift_hom
- \+/\- *def* map
- \+/\- *def* map

modified src/ring_theory/ideal_operations.lean
- \+/\- *lemma* not_one_mem_ker
- \+/\- *lemma* ker_is_prime
- \- *lemma* injective_iff
- \+/\- *lemma* not_one_mem_ker
- \+/\- *lemma* ker_is_prime
- \- *theorem* is_ring_hom_quotient_inf_to_pi_quotient

modified src/ring_theory/ideals.lean
- \+ *lemma* mk_prod
- \+ *lemma* mk_sum
- \+/\- *lemma* lift_mk
- \+/\- *lemma* is_unit_of_map_unit
- \+/\- *lemma* lift_mk
- \+/\- *lemma* is_unit_of_map_unit
- \+ *def* mk_hom
- \+/\- *def* lift
- \+/\- *def* lift

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/noetherian.lean

modified src/ring_theory/power_series.lean

modified src/ring_theory/subring.lean
- \+ *def* ring_hom.cod_restrict



## [2020-03-12 18:52:10](https://github.com/leanprover-community/mathlib/commit/1c449b6)
chore(algebra/field*, field_theory/subfield): drop some `x ≠ 0`, use `division_ring` ([#2136](https://github.com/leanprover-community/mathlib/pull/2136))
* chore(algebra/field*, field_theory/subfield): drop some `x ≠ 0`, use `division_ring`
We have `0⁻¹=0` in `division_ring` now, so no need to assume `field`
in `ring_hom.map_inv` etc.
* Fix lint
#### Estimated changes
modified src/algebra/field.lean
- \+/\- *lemma* map_inv
- \+/\- *lemma* map_div
- \+/\- *lemma* injective
- \- *lemma* neg_inv'
- \- *lemma* map_inv'
- \- *lemma* map_div'
- \+/\- *lemma* map_inv
- \+/\- *lemma* map_div
- \- *lemma* map_inv'
- \- *lemma* map_div'
- \+/\- *lemma* injective

modified src/algebra/field_power.lean
- \+/\- *lemma* ring_hom.map_fpow
- \+/\- *lemma* map_fpow
- \+/\- *lemma* ring_hom.map_fpow
- \- *lemma* ring_hom.map_fpow'
- \+/\- *lemma* map_fpow
- \- *lemma* map_fpow'

modified src/field_theory/subfield.lean



## [2020-03-12 16:38:40](https://github.com/leanprover-community/mathlib/commit/5fe72b6)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-12 15:18:41](https://github.com/leanprover-community/mathlib/commit/f5787f5)
doc(*): switch from update-mathlib to leanproject ([#2093](https://github.com/leanprover-community/mathlib/pull/2093))
* doc(*): switch from update-mathlib to leanproject
* Apply suggestions from code review
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Use shiny new `leanproject new` and `leanproject get`
* documentation tweaks
* project.md tweaks
#### Estimated changes
modified docs/contribute/index.md

modified docs/install/debian.md

modified docs/install/debian_details.md

modified docs/install/linux.md

modified docs/install/project.md

modified docs/install/windows.md



## [2020-03-12 13:07:30](https://github.com/leanprover-community/mathlib/commit/8131108)
feat(category_theory/opposites): add nat_iso.unop ([#2132](https://github.com/leanprover-community/mathlib/pull/2132))
* Add nat_iso.unop
* Add docstrings to nat_iso.op, nat_iso.unop
#### Estimated changes
modified src/category_theory/opposites.lean
- \+ *lemma* unop_hom
- \+ *lemma* unop_inv



## [2020-03-12 10:56:40](https://github.com/leanprover-community/mathlib/commit/7d357d7)
Fix a typo ([#2137](https://github.com/leanprover-community/mathlib/pull/2137))
#### Estimated changes
modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* binary_cofan.mk_ι_app_left
- \+ *lemma* binary_cofan.mk_ι_app_right
- \- *lemma* binary_cofan.mk_π_app_left
- \- *lemma* binary_cofan.mk_π_app_right



## [2020-03-12 05:14:27](https://github.com/leanprover-community/mathlib/commit/35a6e68)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified src/data/set/basic.lean
- \+ *lemma* image_inter_subset
- \- *theorem* mono_image

modified src/data/set/lattice.lean

modified src/order/filter/basic.lean
- \+ *lemma* map_ne_bot_iff
- \+/\- *lemma* tendsto_fst
- \+/\- *lemma* tendsto_snd
- \+/\- *lemma* prod_comm'
- \+/\- *lemma* prod_comm
- \+/\- *lemma* prod_bot
- \+/\- *lemma* bot_prod
- \+/\- *lemma* prod_pure_pure
- \+/\- *lemma* prod_eq_bot
- \+/\- *lemma* prod_ne_bot
- \+/\- *lemma* tendsto_fst
- \+/\- *lemma* tendsto_snd
- \+/\- *lemma* prod_comm'
- \+/\- *lemma* prod_comm
- \+/\- *lemma* prod_bot
- \+/\- *lemma* bot_prod
- \+/\- *lemma* prod_pure_pure
- \+/\- *lemma* prod_eq_bot
- \+/\- *lemma* prod_ne_bot

modified src/order/lattice.lean
- \+ *lemma* inf_le_inf_left
- \+ *lemma* inf_le_inf_right

modified src/ring_theory/free_comm_ring.lean

modified src/topology/algebra/ordered.lean

modified src/topology/subset_properties.lean
- \+ *lemma* cluster_point_of_compact
- \+ *theorem* is_closed_proj_of_compact

modified src/topology/uniform_space/uniform_embedding.lean



## [2020-03-11 22:56:21](https://github.com/leanprover-community/mathlib/commit/7c8dc2a)
feat(category_theory/limits): construct equalizers from pullbacks and products ([#2124](https://github.com/leanprover-community/mathlib/pull/2124))
* construct equalizers from pullbacks and products
* ...
* changes from review
* Add docstrings
* golf proofs a little
* linter
#### Estimated changes
modified src/category_theory/category/default.lean
- \+ *lemma* eq_whisker
- \+ *lemma* whisker_eq

created src/category_theory/limits/shapes/constructions/equalizers.lean
- \+ *lemma* pullback_fst_eq_pullback_snd
- \+ *def* construct_equalizer
- \+ *def* equalizer_cone
- \+ *def* equalizer_cone_is_limit
- \+ *def* has_equalizers_of_pullbacks_and_binary_products



## [2020-03-11 18:57:43](https://github.com/leanprover-community/mathlib/commit/7cffe25)
chore(category_theory/cones): make functor argument of forget explicit ([#2128](https://github.com/leanprover-community/mathlib/pull/2128))
#### Estimated changes
modified src/category_theory/limits/cones.lean
- \+/\- *def* forget
- \+/\- *def* forget
- \+/\- *def* forget
- \+/\- *def* forget

modified src/category_theory/limits/shapes/equalizers.lean

modified src/category_theory/limits/shapes/kernels.lean
- \- *def* kernel.of_cokernel_of_epi
- \- *def* cokernel.of_kernel_of_mono



## [2020-03-11 10:15:41](https://github.com/leanprover-community/mathlib/commit/43431be)
chore(category_theory): remove functor.of ([#2127](https://github.com/leanprover-community/mathlib/pull/2127))
* chore(category_theory): remove functor.of
* fix
#### Estimated changes
modified src/category_theory/comma.lean
- \+/\- *def* over
- \+/\- *def* map
- \+/\- *def* under
- \+/\- *def* map
- \+/\- *def* over
- \+/\- *def* map
- \+/\- *def* under
- \+/\- *def* map

modified src/category_theory/elements.lean
- \+/\- *def* to_comma
- \+/\- *def* from_comma
- \+/\- *def* comma_equivalence
- \+/\- *def* to_comma
- \+/\- *def* from_comma
- \+/\- *def* comma_equivalence

modified src/category_theory/punit.lean
- \- *lemma* obj_obj
- \- *lemma* obj_map
- \- *lemma* map_app
- \- *def* of



## [2020-03-11 07:13:33](https://github.com/leanprover-community/mathlib/commit/d909a61)
fix(algebra/category): avoid deprecated lemmas ([#2126](https://github.com/leanprover-community/mathlib/pull/2126))
#### Estimated changes
modified src/algebra/category/CommRing/colimits.lean

modified src/algebra/category/Mon/colimits.lean



## [2020-03-10 19:54:59](https://github.com/leanprover-community/mathlib/commit/36ac916)
Add two missing duals ([#2122](https://github.com/leanprover-community/mathlib/pull/2122))
#### Estimated changes
modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* cofork.of_π_app_zero
- \+ *lemma* cofork.of_π_app_one



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
modified .github/workflows/build.yml

created scripts/fetch_olean_cache.sh

created scripts/look_up_olean_hash.py

created scripts/write_azure_table_entry.py
- \+ *def* add_entry(file_hash,



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
modified src/measure_theory/measurable_space.lean
- \+ *theorem* is_measurable_sup
- \+ *theorem* is_measurable_Sup
- \+ *theorem* is_measurable_supr



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
modified src/data/mv_polynomial.lean
- \+ *def* fin_succ_equiv

modified src/data/polynomial.lean
- \+ *lemma* polynomial

modified src/ring_theory/polynomial.lean
- \+ *lemma* is_integral_domain_fin_zero
- \+/\- *lemma* is_integral_domain_fin
- \+/\- *lemma* is_integral_domain_fin



## [2020-03-10 10:57:20](https://github.com/leanprover-community/mathlib/commit/cdc56ba)
feat(analysis/calculus/tangent_cone): prove that all intervals are `unique_diff_on` ([#2108](https://github.com/leanprover-community/mathlib/pull/2108))
* feat(analysis/calculus/tangent_cone): prove that all intervals are `unique_diff_on`
* Drop some unneeded assumptions
#### Estimated changes
modified src/analysis/calculus/tangent_cone.lean
- \+ *lemma* unique_diff_on_empty
- \+ *lemma* unique_diff_on_Ici
- \+ *lemma* unique_diff_on_Iic
- \+ *lemma* unique_diff_on_Ioi
- \+ *lemma* unique_diff_on_Iio
- \+ *lemma* unique_diff_on_Icc
- \+ *lemma* unique_diff_on_Ico
- \+ *lemma* unique_diff_on_Ioc
- \+ *lemma* unique_diff_on_Ioo



## [2020-03-10 06:39:45](https://github.com/leanprover-community/mathlib/commit/e8ad2e3)
feat(category_theory/limits): the pullback of a monomorphism is a monomorphism ([#2113](https://github.com/leanprover-community/mathlib/pull/2113))
* The pullback of a monomorphism is a monomorphism
* The pushout of an epimorphism is an epimorphism
* Fix a proof
* renaming
#### Estimated changes
modified src/category_theory/limits/shapes/constructions/binary_products.lean

modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* equalizer_ext
- \+ *lemma* coequalizer_ext
- \+ *lemma* pullback.hom_ext
- \+ *lemma* pushout.hom_ext



## [2020-03-10 04:22:40](https://github.com/leanprover-community/mathlib/commit/945845d)
feat(linter): include linter name in report ([#2116](https://github.com/leanprover-community/mathlib/pull/2116))
* feat(linter): include linter name in report (closes [#2098](https://github.com/leanprover-community/mathlib/pull/2098))
* Update src/tactic/lint.lean
#### Estimated changes
modified src/tactic/lint.lean



## [2020-03-10 02:12:06](https://github.com/leanprover-community/mathlib/commit/4089712)
chore(ring_theory/polynomial): refactor proof of is_noetherian_ring_fin ([#2117](https://github.com/leanprover-community/mathlib/pull/2117))
#### Estimated changes
modified src/ring_theory/polynomial.lean
- \+ *lemma* is_noetherian_ring_fin_0
- \+/\- *theorem* is_noetherian_ring_fin
- \+/\- *theorem* is_noetherian_ring_fin



## [2020-03-09 23:57:38](https://github.com/leanprover-community/mathlib/commit/25df884)
reflexive transitive closure is symmetric of original ([#2115](https://github.com/leanprover-community/mathlib/pull/2115))
* reflexive transitive closure is symmetric if original
* Update src/logic/relation.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/logic/relation.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
modified src/logic/relation.lean
- \+ *lemma* symmetric



## [2020-03-09 21:54:46](https://github.com/leanprover-community/mathlib/commit/f90803c)
feat(algebra/group/hom): cancel injective/surjective `monoid_hom`s ([#2112](https://github.com/leanprover-community/mathlib/pull/2112))
* feat(algebra/group/hom): cancel injective/surjective `monoid_hom`s
* Add a `ring_hom` version
#### Estimated changes
modified src/algebra/group/hom.lean
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left

modified src/algebra/ring.lean
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left



## [2020-03-09 19:43:42](https://github.com/leanprover-community/mathlib/commit/b39713f)
feat(analysis/calculus/darboux): IVT for derivatives ([#2110](https://github.com/leanprover-community/mathlib/pull/2110))
* feat(analysis/calculus/darboux): IVT for derivatives
* whitespace
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
#### Estimated changes
created src/analysis/calculus/darboux.lean
- \+ *theorem* exists_has_deriv_within_at_eq_of_gt_of_lt
- \+ *theorem* exists_has_deriv_within_at_eq_of_lt_of_gt
- \+ *theorem* convex_image_has_deriv_at
- \+ *theorem* deriv_forall_lt_or_forall_gt_of_forall_ne

modified src/analysis/calculus/local_extr.lean



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
modified src/category_theory/category/default.lean
- \+/\- *lemma* cancel_epi
- \+/\- *lemma* cancel_mono
- \+ *lemma* cancel_epi_id
- \+ *lemma* cancel_mono_id
- \+ *lemma* mono_of_mono
- \+ *lemma* mono_of_mono_fac
- \+ *lemma* epi_of_epi
- \+ *lemma* epi_of_epi_fac
- \+/\- *lemma* cancel_epi
- \+/\- *lemma* cancel_mono

modified src/category_theory/limits/shapes/equalizers.lean
- \- *lemma* equalizer.ι_mono
- \- *lemma* coequalizer.π_epi

created src/category_theory/limits/shapes/images.lean
- \+ *lemma* ext
- \+ *lemma* image.as_ι
- \+ *lemma* image.as_c
- \+ *lemma* image.c_ι
- \+ *lemma* image.fac
- \+ *lemma* image.lift_fac
- \+ *lemma* has_image.uniq
- \+ *lemma* image_mono_iso_source_inv_ι
- \+ *lemma* image_mono_iso_source_hom_self
- \+ *def* self
- \+ *def* self
- \+ *def* iso_ext
- \+ *def* image.mono_factorisation
- \+ *def* image.is_image
- \+ *def* image
- \+ *def* image.ι
- \+ *def* image.c
- \+ *def* factor_thru_image
- \+ *def* image.lift
- \+ *def* image_mono_iso_source



## [2020-03-09 12:22:18](https://github.com/leanprover-community/mathlib/commit/d8d0927)
refactor(topology/algebra/ordered): rename `tendsto_of_tendsto_of_tendsto_of_le_of_le` to `tendsto_of_tendsto_of_tendsto_of_le_of_le'` ([#2111](https://github.com/leanprover-community/mathlib/pull/2111))
The new `tendsto_of_tendsto_of_tendsto_of_le_of_le` assumes that
the inequalities hold everywhere.
#### Estimated changes
modified src/analysis/normed_space/real_inner_product.lean

modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_of_tendsto_of_tendsto_of_le_of_le'
- \+/\- *lemma* tendsto_of_tendsto_of_tendsto_of_le_of_le
- \+/\- *lemma* tendsto_of_tendsto_of_tendsto_of_le_of_le

modified src/topology/metric_space/basic.lean



## [2020-03-09 10:19:36](https://github.com/leanprover-community/mathlib/commit/4258f5e)
refactor(analysis/normed_space/banach): use bundled `→L[𝕜]` maps ([#2107](https://github.com/leanprover-community/mathlib/pull/2107))
#### Estimated changes
modified src/analysis/normed_space/banach.lean
- \+/\- *lemma* exists_approx_preimage_norm_le
- \+/\- *lemma* exists_approx_preimage_norm_le
- \+/\- *theorem* exists_preimage_norm_le
- \+/\- *theorem* open_mapping
- \+ *theorem* linear_equiv.continuous_symm
- \+/\- *theorem* exists_preimage_norm_le
- \+/\- *theorem* open_mapping
- \- *theorem* linear_equiv.is_bounded_inv



## [2020-03-09 07:16:17](https://github.com/leanprover-community/mathlib/commit/434b629)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
created docs/tutorial/category_theory/intro.lean



## [2020-03-09 02:49:14](https://github.com/leanprover-community/mathlib/commit/61d70ce)
chore(algebra/group): streamlining imports ([#2099](https://github.com/leanprover-community/mathlib/pull/2099))
* chore(algebra/group): streamlining imports
* reducing imports
#### Estimated changes
modified src/algebra/associated.lean

modified src/algebra/category/Mon/basic.lean

modified src/algebra/char_zero.lean

modified src/algebra/group_power.lean

modified src/algebra/ordered_group.lean

modified src/algebra/pi_instances.lean

modified src/algebra/punit_instances.lean

modified src/algebra/ring.lean

modified src/group_theory/free_group.lean



## [2020-03-09 00:56:10](https://github.com/leanprover-community/mathlib/commit/ca370cb)
fix(deprecated/group): remove dangerous instances ([#2096](https://github.com/leanprover-community/mathlib/pull/2096))
#### Estimated changes
modified src/deprecated/group.lean
- \+ *lemma* additive.is_add_hom
- \+ *lemma* multiplicative.is_mul_hom
- \+ *lemma* additive.is_add_monoid_hom
- \+ *lemma* multiplicative.is_monoid_hom
- \+ *lemma* additive.is_add_group_hom
- \+ *lemma* multiplicative.is_group_hom

modified src/group_theory/quotient_group.lean

modified src/group_theory/subgroup.lean
- \+ *lemma* additive.is_add_subgroup
- \+ *lemma* multiplicative.is_subgroup
- \+ *lemma* additive.normal_add_subgroup
- \+ *lemma* multiplicative.normal_subgroup
- \+/\- *lemma* mem_ker
- \+/\- *lemma* mem_ker
- \+/\- *def* ker
- \+/\- *def* ker



## [2020-03-08 22:46:03](https://github.com/leanprover-community/mathlib/commit/15d3268)
chore(category_theory/functor): make arguments implicit ([#2103](https://github.com/leanprover-community/mathlib/pull/2103))
#### Estimated changes
modified src/category_theory/functor.lean
- \+/\- *lemma* comp_map
- \+/\- *lemma* comp_map



## [2020-03-08 05:53:07](https://github.com/leanprover-community/mathlib/commit/b7444b0)
Remove limits.lean which is superseded by limits_of_products_and_equalizers.lean ([#2105](https://github.com/leanprover-community/mathlib/pull/2105))
#### Estimated changes
deleted src/category_theory/limits/shapes/constructions/limits.lean



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
modified docs/tactics.md

modified src/data/fin.lean

created src/data/fin_enum.lean
- \+ *lemma* mem_to_list
- \+ *lemma* nodup_to_list
- \+ *lemma* finset.mem_enum
- \+ *lemma* mem_pi
- \+ *lemma* pi.mem_enum
- \+ *def* of_equiv
- \+ *def* of_nodup_list
- \+ *def* of_list
- \+ *def* to_list
- \+ *def* of_surjective
- \+ *def* finset.enum
- \+ *def* pi.cons
- \+ *def* pi.tail
- \+ *def* pi
- \+ *def* pi.enum

modified src/data/finset.lean
- \+ *theorem* superset.trans
- \+ *theorem* sdiff_self
- \+ *theorem* sdiff_inter_distrib_right
- \+ *theorem* sdiff_inter_self_left
- \+ *theorem* sdiff_inter_self_right
- \+ *theorem* sdiff_empty
- \+ *theorem* sdiff_subset_self
- \+ *theorem* sdiff_eq_self

modified src/data/list/basic.lean
- \+ *theorem* mem_pure

modified src/tactic/monotonicity/interactive.lean



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
modified docs/commands.md

modified src/tactic/core.lean

modified src/tactic/lint.lean

modified test/lint.lean
- \+ *def* impossible_instance_test
- \+ *def* dangerous_instance_test
- \+ *def* foo_has_mul
- \+ *def* foo_instance



## [2020-03-07 00:15:07](https://github.com/leanprover-community/mathlib/commit/c5437b4)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified src/data/set/finite.lean

modified src/data/set/lattice.lean
- \+/\- *lemma* bUnion_range
- \+/\- *lemma* bInter_range
- \+/\- *lemma* bUnion_image
- \+/\- *lemma* bInter_image
- \+/\- *lemma* bUnion_range
- \+/\- *lemma* bInter_range
- \+/\- *lemma* bUnion_image
- \+/\- *lemma* bInter_image

modified src/measure_theory/integration.lean

modified src/topology/instances/real.lean

modified src/topology/uniform_space/cauchy.lean



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
modified src/algebra/group/basic.lean
- \+ *lemma* inv_unique

modified src/algebra/group/hom.lean
- \+ *lemma* exists_inv_of_comp_exists_inv

modified src/algebra/group/is_unit.lean
- \+/\- *lemma* is_unit_unit
- \+/\- *lemma* is_unit.map
- \+/\- *lemma* is_unit.coe_lift_right
- \+/\- *lemma* is_unit_unit
- \+/\- *lemma* is_unit.map
- \+/\- *lemma* is_unit.coe_lift_right
- \+/\- *theorem* is_unit_one
- \+/\- *theorem* is_unit_of_mul_one
- \+/\- *theorem* is_unit_iff_exists_inv
- \+/\- *theorem* is_unit_iff_exists_inv'
- \+/\- *theorem* units.is_unit_mul_units
- \+/\- *theorem* is_unit_of_mul_is_unit_right
- \+/\- *theorem* is_unit_one
- \+/\- *theorem* is_unit_of_mul_one
- \+/\- *theorem* is_unit_iff_exists_inv
- \+/\- *theorem* is_unit_iff_exists_inv'
- \+/\- *theorem* units.is_unit_mul_units
- \+/\- *theorem* is_unit_of_mul_is_unit_right

modified src/algebra/group/units.lean
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_one
- \+/\- *lemma* val_coe
- \+/\- *lemma* coe_inv
- \+/\- *lemma* inv_mul
- \+/\- *lemma* mul_inv
- \+/\- *lemma* mul_inv_cancel_left
- \+/\- *lemma* inv_mul_cancel_left
- \+/\- *lemma* mul_inv_cancel_right
- \+/\- *lemma* inv_mul_cancel_right
- \+/\- *lemma* units.coe_mk_of_mul_eq_one
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_one
- \+/\- *lemma* val_coe
- \+/\- *lemma* coe_inv
- \+/\- *lemma* inv_mul
- \+/\- *lemma* mul_inv
- \+/\- *lemma* mul_inv_cancel_left
- \+/\- *lemma* inv_mul_cancel_left
- \+/\- *lemma* mul_inv_cancel_right
- \+/\- *lemma* inv_mul_cancel_right
- \+/\- *lemma* units.coe_mk_of_mul_eq_one
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_right_inj
- \+/\- *theorem* eq_mul_inv_iff_mul_eq
- \+/\- *theorem* eq_inv_mul_iff_mul_eq
- \+/\- *theorem* inv_mul_eq_iff_eq_mul
- \+/\- *theorem* mul_inv_eq_iff_eq_mul
- \+ *theorem* nat.add_units_eq_one
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_right_inj
- \+/\- *theorem* eq_mul_inv_iff_mul_eq
- \+/\- *theorem* eq_inv_mul_iff_mul_eq
- \+/\- *theorem* inv_mul_eq_iff_eq_mul
- \+/\- *theorem* mul_inv_eq_iff_eq_mul
- \+/\- *def* units.mk_of_mul_eq_one
- \+/\- *def* units.mk_of_mul_eq_one

modified src/algebra/group/units_hom.lean
- \+/\- *lemma* coe_map
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_id
- \+/\- *lemma* coe_hom_apply
- \+/\- *lemma* coe_lift_right
- \+/\- *lemma* coe_map
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_id
- \+/\- *lemma* coe_hom_apply
- \+/\- *lemma* coe_lift_right

modified src/algebra/pi_instances.lean
- \+ *def* monoid_hom.inl
- \+ *def* monoid_hom.inr

modified src/group_theory/monoid_localization.lean
- \+ *lemma* r_iff_exists
- \+ *lemma* sec_spec
- \+ *lemma* sec_spec'
- \+ *lemma* mul_inv_left
- \+ *lemma* mul_inv_right
- \+ *lemma* mul_inv
- \+ *lemma* inv_inj
- \+ *lemma* inv_unique
- \+ *lemma* mk'_mul
- \+ *lemma* mk'_one
- \+ *lemma* mk'_sec
- \+ *lemma* mk'_surjective
- \+ *lemma* mk'_spec
- \+ *lemma* mk'_spec'
- \+ *lemma* mk'_eq_iff_eq
- \+ *lemma* eq_iff_eq
- \+ *lemma* mk'_eq_iff_mk'_eq
- \+ *lemma* exists_of_sec_mk'
- \+ *lemma* exists_of_sec
- \+ *lemma* mk'_eq_of_eq
- \+ *lemma* mk'_self
- \+ *lemma* mk'_self'
- \+ *lemma* mul_mk'_eq_mk'_of_mul
- \+ *lemma* mk'_mul_eq_mk'_of_mul
- \+ *lemma* mul_mk'_one_eq_mk'
- \+ *lemma* mk'_mul_cancel_right
- \+ *lemma* mk'_mul_cancel_left
- \- *lemma* r'.transitive
- \- *lemma* r'.add
- \- *lemma* one_rel
- \- *lemma* exists_rep
- \- *lemma* mk_eq_of_eq
- \- *lemma* mk_self'
- \- *lemma* mk_self
- \- *lemma* mk_mul_mk
- \- *lemma* lift_on_beta
- \- *lemma* of_ker_iff
- \- *lemma* of_eq_mk
- \- *lemma* of_mul_mk
- \- *lemma* mk_eq_mul_mk_one
- \- *lemma* mk_mul_cancel_right
- \- *lemma* mk_mul_cancel_left
- \- *lemma* to_units_mk
- \- *lemma* mk_is_unit
- \- *lemma* mk_is_unit'
- \- *lemma* to_units_inv
- \- *lemma* of_is_unit
- \- *lemma* of_is_unit'
- \- *lemma* to_units_map_inv
- \- *lemma* mk_eq
- \- *lemma* is_unit_of_of_comp
- \- *lemma* units_restrict_mul
- \- *lemma* r_le_ker_aux
- \- *lemma* lift'_mk
- \- *lemma* lift_mk
- \- *lemma* lift'_of
- \- *lemma* lift_of
- \- *lemma* lift'_eq_iff
- \- *lemma* lift_eq_iff
- \- *lemma* mk_eq_iff_of_eq
- \- *lemma* lift'_comp_of
- \- *lemma* lift_comp_of
- \- *lemma* lift'_apply_of
- \- *lemma* lift_apply_of
- \- *lemma* map_eq
- \- *lemma* map_of
- \- *lemma* map_comp_of
- \- *lemma* map_mk
- \- *lemma* map_id
- \- *lemma* map_comp_map
- \- *lemma* map_map
- \- *lemma* map_ext
- \+/\- *theorem* r_eq_r'
- \+ *theorem* eq_mk'_iff_mul_eq
- \+ *theorem* mk'_eq_iff_eq_mul
- \+/\- *theorem* r_eq_r'
- \- *theorem* ind
- \- *theorem* induction_on
- \+/\- *def* r
- \+/\- *def* r'
- \+ *def* localization
- \+/\- *def* r
- \+/\- *def* r'
- \+/\- *def* r'
- \- *def* monoid_localization
- \- *def* mk
- \- *def* of
- \- *def* to_units
- \- *def* units_restrict
- \- *def* aux
- \- *def* lift'
- \- *def* map

modified src/group_theory/submonoid.lean
- \+ *def* restrict



## [2020-03-06 11:43:23](https://github.com/leanprover-community/mathlib/commit/36b336c)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-06 09:04:50](https://github.com/leanprover-community/mathlib/commit/8fb9881)
fix(category_theory/limits): Add some missing instances for special shapes of limits ([#2083](https://github.com/leanprover-community/mathlib/pull/2083))
* Add some instances for limit shapes
* Deduce has_(equalizers|kernels|pullbacks) from has_finite_limits
#### Estimated changes
modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* has_equalizers_of_has_finite_limits
- \+ *def* has_coequalizers_of_has_finite_colimits

modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* has_kernels_of_has_finite_limits
- \+ *def* has_cokernels_of_has_finite_colimits

modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* has_pullbacks_of_has_finite_limits
- \+ *def* has_pushouts_of_has_finite_colimits



## [2020-03-06 06:56:58](https://github.com/leanprover-community/mathlib/commit/f81f861)
feat(category_theory/limits): the kernel of the cokernel of an epimorphism is an isomorphism ([#2088](https://github.com/leanprover-community/mathlib/pull/2088))
* The kernel of the cokernel of an epimorphism is an isomorphism
* Fix unused argument warnings
* Remove a set_option
* Fix a typo
#### Estimated changes
modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* cocone_parallel_pair_left
- \+ *lemma* cocone_parallel_pair_right
- \+ *lemma* cocone_parallel_pair_ext
- \+ *lemma* cofork.eq_of_π_π
- \+ *lemma* coequalizer.π.cofork
- \+ *lemma* coequalizer.π.eq_app_one
- \+ *lemma* coequalizer.hom_ext
- \+ *lemma* coequalizer.π_epi
- \+ *lemma* cocone_parallel_pair_self_ι_app_one
- \+ *lemma* cocone_parallel_pair_self_X
- \+ *def* equalizer.ι_of_self
- \+ *def* limit_cone_parallel_pair_self_is_iso'
- \+ *def* equalizer.ι_of_self'
- \+ *def* cocone_parallel_pair_self
- \+ *def* is_colimit_cocone_parallel_pair_self
- \+ *def* colimit_cocone_parallel_pair_self_is_iso
- \+ *def* coequalizer.π_of_self
- \+ *def* colimit_cocone_parallel_pair_self_is_iso'
- \+ *def* coequalizer.π_of_self'
- \+ *def* mono_limit_cocone_parallel_pair_is_iso

modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* kernel.ι_of_mono
- \+ *lemma* cokernel.π_of_epi
- \+ *def* kernel.of_mono
- \+ *def* kernel.ι_of_zero
- \+ *def* cokernel.zero_cocone
- \+ *def* cokernel.is_colimit_cocone_zero_cocone
- \+ *def* cokernel.of_epi
- \+ *def* cokernel.π_of_zero
- \+ *def* kernel.of_cokernel_of_epi
- \+ *def* cokernel.of_kernel_of_mono



## [2020-03-05 18:58:12-08:00](https://github.com/leanprover-community/mathlib/commit/0f9751c)
feat(data/traversable): improve support for instances for recursive types ([#2072](https://github.com/leanprover-community/mathlib/pull/2072))
#### Estimated changes
modified src/category/traversable/derive.lean

modified test/examples.lean
- \+ *def* x
- \+ *def* ex



## [2020-03-06 01:31:18](https://github.com/leanprover-community/mathlib/commit/093ac77)
feat(analysis/calculus/specific_functions): smoothness of exp(-1/x) ([#2087](https://github.com/leanprover-community/mathlib/pull/2087))
* feat(analysis/calculus/specific_functions): smoothness of exp(-1/x)
* use namespace; shorter names
* fix field_simp
#### Estimated changes
modified src/algebra/field.lean
- \+ *lemma* sub_div'
- \+ *lemma* div_sub'

created src/analysis/calculus/specific_functions.lean
- \+ *lemma* f_aux_zero_eq
- \+ *lemma* f_aux_deriv
- \+ *lemma* f_aux_deriv_pos
- \+ *lemma* f_aux_limit
- \+ *lemma* f_aux_deriv_zero
- \+ *lemma* f_aux_has_deriv_at
- \+ *lemma* f_aux_iterated_deriv
- \+ *lemma* zero_of_nonpos
- \+ *lemma* pos_of_pos
- \+ *lemma* nonneg
- \+ *theorem* smooth
- \+ *def* exp_neg_inv_glue
- \+ *def* f_aux

modified test/ring.lean



## [2020-03-05 16:05:27](https://github.com/leanprover-community/mathlib/commit/50c4adf)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified archive/imo1988_q6.lean

modified archive/sensitivity.lean

modified docs/tutorial/Zmod37.lean

modified leanpkg.toml

modified scripts/nolints.txt

modified src/algebra/archimedean.lean

modified src/algebra/direct_limit.lean

modified src/algebra/euclidean_domain.lean

modified src/algebra/field.lean
- \+ *lemma* inv_inv''
- \+/\- *lemma* inv_involutive'
- \+/\- *lemma* inv_div
- \+/\- *lemma* inv_div_left
- \+/\- *lemma* neg_inv
- \+/\- *lemma* division_ring.inv_inj
- \+/\- *lemma* division_ring.inv_eq_iff
- \+/\- *lemma* div_neg
- \+/\- *lemma* field.div_right_comm
- \+/\- *lemma* field.div_div_div_cancel_right
- \+/\- *lemma* field.div_div_cancel
- \+/\- *lemma* inv_involutive'
- \+/\- *lemma* inv_div
- \+/\- *lemma* inv_div_left
- \+/\- *lemma* neg_inv
- \+/\- *lemma* division_ring.inv_inj
- \+/\- *lemma* division_ring.inv_eq_iff
- \+/\- *lemma* div_neg
- \+/\- *lemma* field.div_right_comm
- \+/\- *lemma* field.div_div_div_cancel_right
- \+/\- *lemma* field.div_div_cancel
- \- *lemma* div_right_comm
- \- *lemma* div_div_div_cancel_right
- \- *lemma* div_div_cancel
- \- *theorem* inv_inv'

modified src/algebra/field_power.lean
- \+/\- *lemma* ring_hom.map_fpow
- \+/\- *lemma* map_fpow
- \+/\- *lemma* ring_hom.map_fpow
- \+/\- *lemma* map_fpow

modified src/algebra/floor.lean

modified src/algebra/geom_sum.lean

modified src/algebra/group/basic.lean
- \+/\- *lemma* neg_sub_neg
- \+ *lemma* sub_eq_sub_iff_add_eq_add
- \+/\- *lemma* neg_sub_neg

modified src/algebra/group_power.lean
- \+/\- *lemma* inv_pow'
- \+/\- *lemma* pow_div
- \+/\- *lemma* inv_pow'
- \+/\- *lemma* pow_div
- \+/\- *theorem* one_div_pow
- \+/\- *theorem* division_ring.inv_pow
- \+/\- *theorem* div_pow
- \+/\- *theorem* one_div_pow
- \+/\- *theorem* division_ring.inv_pow
- \+/\- *theorem* div_pow

modified src/algebra/lie_algebra.lean

modified src/algebra/module.lean
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub

modified src/algebra/opposites.lean

modified src/algebra/order_functions.lean

modified src/algebra/ordered_field.lean

modified src/algebra/ordered_group.lean

modified src/algebra/ordered_ring.lean
- \+ *def* to_decidable_linear_ordered_comm_ring

modified src/algebra/pi_instances.lean
- \+ *lemma* sub_apply
- \+ *lemma* fst_sub
- \+ *lemma* snd_sub

modified src/algebra/pointwise.lean

modified src/algebra/quadratic_discriminant.lean

modified src/algebra/ring.lean

modified src/analysis/asymptotics.lean

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/fderiv.lean

modified src/analysis/complex/basic.lean

modified src/analysis/complex/exponential.lean
- \+/\- *lemma* arcsin_eq_pi_div_two_sub_arccos
- \+/\- *lemma* arcsin_eq_pi_div_two_sub_arccos

modified src/analysis/complex/polynomial.lean

modified src/analysis/convex/topology.lean

modified src/analysis/normed_space/banach.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/bounded_linear_maps.lean

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/analysis/normed_space/real_inner_product.lean

modified src/analysis/specific_limits.lean

modified src/computability/partrec_code.lean

modified src/computability/primrec.lean

modified src/computability/turing_machine.lean

modified src/data/array/lemmas.lean

modified src/data/complex/basic.lean
- \+/\- *lemma* conj_inv
- \+/\- *lemma* conj_inv

modified src/data/complex/exponential.lean

modified src/data/dfinsupp.lean

modified src/data/equiv/algebra.lean

modified src/data/equiv/list.lean

modified src/data/finset.lean
- \- *theorem* has_insert_eq_insert

modified src/data/finsupp.lean

modified src/data/fintype.lean

modified src/data/fp/basic.lean

modified src/data/hash_map.lean

modified src/data/holor.lean

modified src/data/int/basic.lean

modified src/data/int/gcd.lean

modified src/data/int/modeq.lean

modified src/data/int/parity.lean

modified src/data/list/basic.lean
- \+/\- *theorem* mem_enum_from
- \+/\- *theorem* mem_enum_from

modified src/data/list/perm.lean

modified src/data/multiset.lean

modified src/data/mv_polynomial.lean

modified src/data/nat/basic.lean

modified src/data/nat/cast.lean

modified src/data/nat/dist.lean

modified src/data/nat/enat.lean

modified src/data/nat/modeq.lean

modified src/data/nat/multiplicity.lean

modified src/data/nat/pairing.lean

modified src/data/nat/sqrt.lean

modified src/data/num/lemmas.lean

modified src/data/padics/hensel.lean

modified src/data/padics/padic_integers.lean

modified src/data/padics/padic_norm.lean

modified src/data/padics/padic_numbers.lean

modified src/data/polynomial.lean
- \+/\- *lemma* degree_map
- \+/\- *lemma* nat_degree_map
- \+/\- *lemma* leading_coeff_map
- \+/\- *lemma* map_div
- \+/\- *lemma* map_mod
- \+/\- *lemma* map_eq_zero
- \+/\- *lemma* degree_map
- \+/\- *lemma* nat_degree_map
- \+/\- *lemma* leading_coeff_map
- \+/\- *lemma* map_div
- \+/\- *lemma* map_mod
- \+/\- *lemma* map_eq_zero

modified src/data/rat/basic.lean

modified src/data/rat/cast.lean
- \+/\- *theorem* cast_mk
- \+/\- *theorem* cast_inv
- \+/\- *theorem* cast_div
- \+/\- *theorem* cast_pow
- \+/\- *theorem* cast_mk
- \+/\- *theorem* cast_inv
- \+/\- *theorem* cast_div
- \+/\- *theorem* cast_pow

modified src/data/rat/order.lean

modified src/data/real/basic.lean

modified src/data/real/cau_seq.lean

modified src/data/real/cau_seq_completion.lean

modified src/data/real/ennreal.lean

modified src/data/real/hyperreal.lean
- \+/\- *lemma* inv_epsilon_eq_omega
- \+/\- *lemma* inv_epsilon_eq_omega

modified src/data/real/irrational.lean

modified src/data/real/nnreal.lean
- \+/\- *lemma* inv_inv
- \+/\- *lemma* inv_inv

modified src/data/real/pi.lean

modified src/data/set/basic.lean
- \- *theorem* insert_of_has_insert

modified src/data/set/enumerate.lean

modified src/data/set/lattice.lean

modified src/data/zmod/basic.lean

modified src/data/zmod/quadratic_reciprocity.lean

modified src/data/zsqrtd/basic.lean

modified src/data/zsqrtd/gaussian_int.lean

modified src/field_theory/finite.lean
- \+/\- *lemma* pow_card_sub_one_eq_one
- \+/\- *lemma* pow_card_sub_one_eq_one

modified src/field_theory/finite_card.lean

modified src/field_theory/minimal_polynomial.lean

modified src/field_theory/mv_polynomial.lean
- \+/\- *lemma* mem_restrict_degree
- \+/\- *lemma* mem_restrict_degree_iff_sup
- \+/\- *lemma* is_basis_monomials
- \+/\- *lemma* mem_restrict_degree
- \+/\- *lemma* mem_restrict_degree_iff_sup
- \+/\- *lemma* is_basis_monomials
- \+/\- *def* restrict_degree
- \+/\- *def* restrict_degree

modified src/field_theory/perfect_closure.lean
- \+/\- *theorem* eq_pth_root
- \+/\- *theorem* eq_pth_root
- \+/\- *def* UMP
- \+/\- *def* UMP

modified src/field_theory/splitting_field.lean

modified src/field_theory/subfield.lean

modified src/geometry/manifold/real_instances.lean

modified src/group_theory/free_abelian_group.lean

modified src/group_theory/free_group.lean

modified src/group_theory/order_of_element.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/basis.lean

modified src/linear_algebra/bilinear_form.lean

modified src/linear_algebra/contraction.lean

modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_of_field
- \+/\- *lemma* dim_of_field

modified src/linear_algebra/dual.lean

modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* dim_lt_omega
- \+/\- *lemma* findim_eq_dim
- \+/\- *lemma* dim_lt_omega
- \+/\- *lemma* findim_eq_dim
- \+/\- *def* finite_dimensional
- \+/\- *def* finite_dimensional

modified src/linear_algebra/finsupp_vector_space.lean

modified src/linear_algebra/matrix.lean
- \+/\- *lemma* rank_diagonal
- \+/\- *lemma* rank_diagonal

modified src/linear_algebra/multilinear.lean

modified src/linear_algebra/sesquilinear_form.lean

modified src/linear_algebra/tensor_product.lean

modified src/measure_theory/ae_eq_fun.lean

modified src/measure_theory/integration.lean

modified src/measure_theory/lebesgue_measure.lean

modified src/measure_theory/outer_measure.lean

modified src/measure_theory/simple_func_dense.lean

modified src/number_theory/dioph.lean

modified src/number_theory/pell.lean

modified src/number_theory/sum_four_squares.lean

modified src/order/filter/filter_product.lean

modified src/ring_theory/adjoin_root.lean

modified src/ring_theory/algebraic.lean

modified src/ring_theory/ideals.lean
- \+/\- *lemma* eq_bot_or_top
- \+/\- *lemma* eq_bot_of_prime
- \+/\- *lemma* eq_bot_or_top
- \+/\- *lemma* eq_bot_of_prime

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/power_series.lean

modified src/set_theory/lists.lean

modified src/tactic/abel.lean

modified src/tactic/algebra.lean

modified src/tactic/linarith.lean

modified src/tactic/lint.lean

modified src/tactic/ring.lean

modified src/tactic/ring2.lean

modified src/tactic/ring_exp.lean

modified src/topology/algebra/group.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/module.lean

modified src/topology/algebra/multilinear.lean

modified src/topology/algebra/ordered.lean

modified src/topology/algebra/ring.lean

modified src/topology/algebra/uniform_group.lean

modified src/topology/bounded_continuous_function.lean

modified src/topology/instances/complex.lean

modified src/topology/instances/ennreal.lean

modified src/topology/instances/real.lean

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/emetric_space.lean

modified src/topology/metric_space/gluing.lean

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/metric_space/hausdorff_distance.lean

modified src/topology/metric_space/isometry.lean

modified src/topology/subset_properties.lean

modified test/conv.lean

modified test/monotonicity.lean

modified test/ring_exp.lean



## [2020-03-05 00:24:49](https://github.com/leanprover-community/mathlib/commit/8535132)
refactor(algebra/lie_algebra): lie_algebra should not extend lie_ring ([#2084](https://github.com/leanprover-community/mathlib/pull/2084))
* refactor(algebra/lie_algebra): lie_algebra should not extend lie_ring
* Fix linting error ☺
#### Estimated changes
modified src/algebra/lie_algebra.lean
- \+/\- *lemma* lie_smul
- \+/\- *lemma* smul_lie
- \+/\- *lemma* endo_algebra_bracket
- \+/\- *lemma* lie_smul
- \+/\- *lemma* smul_lie
- \+/\- *lemma* endo_algebra_bracket
- \+/\- *def* of_associative_algebra
- \+ *def* lie_subalgebra_lie_ring
- \+/\- *def* lie_subalgebra_lie_algebra
- \+ *def* matrix.lie_ring
- \+/\- *def* of_associative_algebra
- \+/\- *def* lie_subalgebra_lie_algebra

modified src/algebra/ordered_group.lean
- \+/\- *lemma* add_neg_le_iff_le_add
- \+/\- *lemma* add_neg_le_iff_le_add



## [2020-03-04 22:23:00](https://github.com/leanprover-community/mathlib/commit/7d6c4fb)
fix(congruence): use has_coe_t instead of has_coe ([#2086](https://github.com/leanprover-community/mathlib/pull/2086))
* fix(congruence): use has_coe_t instead of has_coe
* capitalization
Does that matter for doc generation?
#### Estimated changes
modified src/group_theory/congruence.lean



## [2020-03-04 19:56:00](https://github.com/leanprover-community/mathlib/commit/9fc675c)
chore(analysis/normed_space/basic): rename `ne_mem_of_tendsto_norm_at_top` ([#2085](https://github.com/leanprover-community/mathlib/pull/2085))
It uses `∀ᶠ` now, so rename to `eventually_ne_of_tendsto_norm_at_top`.
#### Estimated changes
modified src/analysis/calculus/fderiv.lean

modified src/analysis/calculus/tangent_cone.lean

modified src/analysis/normed_space/basic.lean
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
modified .github/workflows/build.yml

modified scripts/deploy_docs.sh



## [2020-03-04 07:09:20](https://github.com/leanprover-community/mathlib/commit/cc4ac8a)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-03 20:45:05-08:00](https://github.com/leanprover-community/mathlib/commit/0f1eb80)
fix(CI/documentation): add a name back
#### Estimated changes
modified src/tactic/interactive.lean



## [2020-03-03 22:24:50](https://github.com/leanprover-community/mathlib/commit/13f04c0)
feat(tactic/extract_goal): improve formatting to put assumptions on their own line ([#2076](https://github.com/leanprover-community/mathlib/pull/2076))
#### Estimated changes
modified src/tactic/interactive.lean



## [2020-03-03 20:14:28](https://github.com/leanprover-community/mathlib/commit/545dd03)
feat(topology/metric_space/antilipschitz): define `antilipschitz_with` ([#2075](https://github.com/leanprover-community/mathlib/pull/2075))
* chore(data/real/ennreal): weaker assumptions in `sub_mul`, add `coe_inv_le`
* feat(topology/metric_space/antilipschitz): define `antilipschitz_with`
Also make some proofs use facts about `antilipschitz_with`.
* Rename inequalities, move `K` to the other side
This way it's easier to glue it with the rest of the library, and
we can avoid assuming `0 < K` in many lemmas.
#### Estimated changes
modified src/analysis/ODE/gronwall.lean

modified src/analysis/normed_space/basic.lean
- \+ *lemma* abs_dist_sub_le_dist_add_add
- \+ *lemma* nndist_add_add_le
- \+ *lemma* edist_add_add_le
- \+ *lemma* lipschitz_with.neg
- \+ *lemma* lipschitz_with.add
- \+ *lemma* lipschitz_with.sub
- \+ *lemma* antilipschitz_with.add_lipschitz_with

modified src/analysis/normed_space/finite_dimension.lean

modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_equiv.lipschitz
- \+ *lemma* continuous_linear_equiv.antilipschitz
- \+ *lemma* continuous_linear_equiv.uniform_embedding
- \+ *theorem* linear_map.antilipschitz_of_bound
- \+/\- *theorem* lipschitz
- \+ *theorem* op_norm_le_of_lipschitz
- \+/\- *theorem* uniform_embedding_of_bound
- \+ *theorem* antilipschitz_of_uniform_embedding
- \+/\- *theorem* lipschitz
- \+/\- *theorem* uniform_embedding_of_bound
- \- *theorem* bound_of_uniform_embedding

modified src/measure_theory/bochner_integration.lean

modified src/topology/bounded_continuous_function.lean

created src/topology/metric_space/antilipschitz.lean
- \+ *lemma* antilipschitz_with_iff_le_mul_dist
- \+ *lemma* antilipschitz_with.mul_le_dist
- \+ *lemma* mul_le_edist
- \+ *lemma* id
- \+ *lemma* comp
- \+ *lemma* to_inverse
- \+ *lemma* uniform_embedding
- \+ *lemma* lipschitz_with.to_inverse
- \+ *def* antilipschitz_with

modified src/topology/metric_space/contracting.lean
- \+ *lemma* dist_le_mul
- \- *lemma* dist_le

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometry.lipschitz
- \+ *lemma* isometry.antilipschitz
- \+/\- *lemma* isometry.injective
- \+/\- *lemma* isometry.injective

modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* lipschitz_with_iff_dist_le_mul
- \+ *lemma* edist_le_mul
- \+ *lemma* mul_edist_le
- \- *lemma* lipschitz_with_iff_dist_le
- \- *lemma* edist_le



## [2020-03-03 14:39:18](https://github.com/leanprover-community/mathlib/commit/02d22c3)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



## [2020-03-03 11:51:46](https://github.com/leanprover-community/mathlib/commit/f7e82d0)
feat(tactic/lint): check for redundant simp lemmas ([#2066](https://github.com/leanprover-community/mathlib/pull/2066))
* chore(*): fix simp lemmas
* feat(tactic/lint): check for redundant simp lemmas
#### Estimated changes
modified docs/commands.md

modified src/algebra/associated.lean
- \+/\- *lemma* mul_unit_dvd_iff
- \+/\- *lemma* dvd_mul_unit_iff
- \+/\- *lemma* mul_unit_dvd_iff
- \+/\- *lemma* dvd_mul_unit_iff

modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_const_one
- \+/\- *lemma* sum_const_zero
- \+/\- *lemma* prod_const_one
- \+/\- *lemma* sum_const_zero

modified src/algebra/category/Group.lean

modified src/algebra/char_zero.lean
- \+/\- *theorem* cast_ne_zero
- \+/\- *theorem* cast_ne_zero

modified src/algebra/commute.lean
- \+/\- *theorem* units_inv_right
- \+/\- *theorem* units_inv_left
- \+/\- *theorem* inv_right
- \+/\- *theorem* inv_left
- \+/\- *theorem* neg_right
- \+/\- *theorem* neg_left
- \+/\- *theorem* units_inv_right
- \+/\- *theorem* units_inv_left
- \+/\- *theorem* inv_right
- \+/\- *theorem* inv_left
- \+/\- *theorem* neg_right
- \+/\- *theorem* neg_left

modified src/algebra/free.lean
- \+/\- *lemma* lift_of_mul
- \+/\- *lemma* lift_of_mul

modified src/algebra/group/basic.lean

modified src/algebra/group_power.lean
- \+/\- *theorem* list.prod_repeat
- \+/\- *theorem* list.sum_repeat
- \+/\- *theorem* list.prod_repeat
- \+/\- *theorem* list.sum_repeat

modified src/algebra/lie_algebra.lean
- \+/\- *lemma* map_lie
- \+ *lemma* map_lie'
- \+/\- *lemma* map_lie

modified src/algebra/ring.lean
- \+/\- *lemma* comp_apply
- \+/\- *lemma* comp_apply

modified src/category_theory/discrete_category.lean
- \+/\- *lemma* of_function_map
- \+/\- *lemma* of_function_map

modified src/category_theory/functor_category.lean
- \+/\- *lemma* vcomp_app'
- \+/\- *lemma* vcomp_app'

modified src/category_theory/monoidal/category.lean
- \+/\- *lemma* triangle_assoc_comp_left
- \+/\- *lemma* triangle_assoc_comp_left

modified src/category_theory/natural_isomorphism.lean
- \+/\- *lemma* app_hom
- \+/\- *lemma* app_inv
- \+/\- *lemma* hom_app_inv_app_id
- \+/\- *lemma* inv_app_hom_app_id
- \+/\- *lemma* app_hom
- \+/\- *lemma* app_inv
- \+/\- *lemma* hom_app_inv_app_id
- \+/\- *lemma* inv_app_hom_app_id

modified src/computability/partrec.lean
- \+/\- *theorem* rfind_dom'
- \+/\- *theorem* rfind_dom'

modified src/data/bool.lean
- \+/\- *theorem* coe_to_bool
- \+/\- *theorem* coe_to_bool

modified src/data/complex/basic.lean
- \+/\- *lemma* conj_neg_I
- \+/\- *lemma* abs_of_nat
- \+/\- *lemma* conj_neg_I
- \+/\- *lemma* abs_of_nat
- \+/\- *theorem* of_real_ne_zero
- \+/\- *theorem* of_real_ne_zero

modified src/data/dfinsupp.lean
- \+/\- *lemma* filter_apply_pos
- \+/\- *lemma* filter_apply_neg
- \+/\- *lemma* single_eq_of_ne
- \+/\- *lemma* erase_ne
- \+/\- *lemma* mem_support_iff
- \+/\- *lemma* filter_apply_pos
- \+/\- *lemma* filter_apply_neg
- \+/\- *lemma* single_eq_of_ne
- \+/\- *lemma* erase_ne
- \+/\- *lemma* mem_support_iff

modified src/data/equiv/algebra.lean
- \+/\- *lemma* coe_units_equiv_ne_zero
- \+/\- *lemma* coe_units_equiv_ne_zero

modified src/data/equiv/denumerable.lean
- \+/\- *theorem* decode_eq_of_nat
- \+/\- *theorem* decode_eq_of_nat

modified src/data/fin.lean
- \+/\- *lemma* mk_val
- \+/\- *lemma* mk_val

modified src/data/finset.lean
- \+/\- *lemma* piecewise_eq_of_mem
- \+/\- *lemma* piecewise_eq_of_not_mem
- \+/\- *lemma* piecewise_insert_of_ne
- \+/\- *lemma* piecewise_eq_of_mem
- \+/\- *lemma* piecewise_eq_of_not_mem
- \+/\- *lemma* piecewise_insert_of_ne
- \+/\- *theorem* singleton_eq_singleton
- \+/\- *theorem* insert_empty_eq_singleton
- \+/\- *theorem* union_self
- \+/\- *theorem* sdiff_union_of_subset
- \+/\- *theorem* union_sdiff_of_subset
- \+/\- *theorem* mem_map_of_mem
- \+/\- *theorem* mem_image_of_mem
- \+/\- *theorem* image_val_of_inj_on
- \+/\- *theorem* singleton_eq_singleton
- \+/\- *theorem* insert_empty_eq_singleton
- \+/\- *theorem* union_self
- \+/\- *theorem* sdiff_union_of_subset
- \+/\- *theorem* union_sdiff_of_subset
- \+/\- *theorem* mem_map_of_mem
- \+/\- *theorem* mem_image_of_mem
- \+/\- *theorem* image_val_of_inj_on

modified src/data/fintype.lean
- \+/\- *theorem* fintype.univ_unit
- \+/\- *theorem* fintype.card_unit
- \+/\- *theorem* fintype.univ_unit
- \+/\- *theorem* fintype.card_unit

modified src/data/int/basic.lean
- \+/\- *theorem* coe_nat_ne_zero
- \+/\- *theorem* zero_mod
- \+/\- *theorem* mod_zero
- \+/\- *theorem* mod_one
- \+/\- *theorem* mod_self
- \+/\- *theorem* mod_mod
- \+/\- *theorem* cast_ne_zero
- \+/\- *theorem* coe_nat_ne_zero
- \+/\- *theorem* zero_mod
- \+/\- *theorem* mod_zero
- \+/\- *theorem* mod_one
- \+/\- *theorem* mod_self
- \+/\- *theorem* mod_mod
- \+/\- *theorem* cast_ne_zero

modified src/data/int/gcd.lean

modified src/data/list/basic.lean
- \+/\- *theorem* cons_ne_nil
- \+/\- *theorem* cons_inj'
- \+/\- *theorem* mem_map_of_inj
- \+/\- *theorem* index_of_cons_ne
- \+/\- *theorem* index_of_of_not_mem
- \+/\- *theorem* count_cons_of_ne
- \+/\- *theorem* count_eq_zero_of_not_mem
- \+/\- *theorem* sublists'_singleton
- \+/\- *theorem* insert_of_mem
- \+/\- *theorem* insert_of_not_mem
- \+/\- *theorem* mem_insert_of_mem
- \+/\- *theorem* erase_of_not_mem
- \+/\- *theorem* singleton_disjoint
- \+/\- *theorem* disjoint_singleton
- \+/\- *theorem* cons_ne_nil
- \+/\- *theorem* cons_inj'
- \+/\- *theorem* mem_map_of_inj
- \+/\- *theorem* index_of_cons_ne
- \+/\- *theorem* index_of_of_not_mem
- \+/\- *theorem* count_cons_of_ne
- \+/\- *theorem* count_eq_zero_of_not_mem
- \+/\- *theorem* sublists'_singleton
- \+/\- *theorem* insert_of_mem
- \+/\- *theorem* insert_of_not_mem
- \+/\- *theorem* mem_insert_of_mem
- \+/\- *theorem* erase_of_not_mem
- \+/\- *theorem* singleton_disjoint
- \+/\- *theorem* disjoint_singleton

modified src/data/list/sigma.lean
- \+/\- *theorem* kerase_cons_eq
- \+/\- *theorem* kerase_cons_ne
- \+/\- *theorem* kerase_of_not_mem_keys
- \+/\- *theorem* mem_keys_kerase_of_ne
- \+/\- *theorem* kerase_cons_eq
- \+/\- *theorem* kerase_cons_ne
- \+/\- *theorem* kerase_of_not_mem_keys
- \+/\- *theorem* mem_keys_kerase_of_ne

modified src/data/list/sort.lean
- \+/\- *theorem* sorted_singleton
- \+/\- *theorem* sorted_singleton

modified src/data/multiset.lean
- \+/\- *lemma* nodup_antidiagonal
- \+/\- *lemma* nodup_antidiagonal
- \+/\- *theorem* erase_cons_tail
- \+/\- *theorem* erase_of_not_mem
- \+/\- *theorem* cons_erase
- \+/\- *theorem* mem_map_of_inj
- \+/\- *theorem* map_id
- \+/\- *theorem* count_cons_of_ne
- \+/\- *theorem* count_eq_zero_of_not_mem
- \+/\- *theorem* count_erase_of_ne
- \+/\- *theorem* singleton_disjoint
- \+/\- *theorem* disjoint_singleton
- \+/\- *theorem* ndinsert_of_mem
- \+/\- *theorem* ndinsert_of_not_mem
- \+/\- *theorem* mem_ndinsert_of_mem
- \+/\- *theorem* length_ndinsert_of_mem
- \+/\- *theorem* length_ndinsert_of_not_mem
- \+/\- *theorem* ndunion_eq_union
- \+/\- *theorem* cons_ndinter_of_mem
- \+/\- *theorem* ndinter_cons_of_not_mem
- \+/\- *theorem* ndinter_eq_inter
- \+/\- *theorem* erase_cons_tail
- \+/\- *theorem* erase_of_not_mem
- \+/\- *theorem* cons_erase
- \+/\- *theorem* mem_map_of_inj
- \+/\- *theorem* map_id
- \+/\- *theorem* count_cons_of_ne
- \+/\- *theorem* count_eq_zero_of_not_mem
- \+/\- *theorem* count_erase_of_ne
- \+/\- *theorem* singleton_disjoint
- \+/\- *theorem* disjoint_singleton
- \- *theorem* forall_mem_ne
- \+/\- *theorem* ndinsert_of_mem
- \+/\- *theorem* ndinsert_of_not_mem
- \+/\- *theorem* mem_ndinsert_of_mem
- \+/\- *theorem* length_ndinsert_of_mem
- \+/\- *theorem* length_ndinsert_of_not_mem
- \+/\- *theorem* ndunion_eq_union
- \+/\- *theorem* cons_ndinter_of_mem
- \+/\- *theorem* ndinter_cons_of_not_mem
- \+/\- *theorem* ndinter_eq_inter

modified src/data/nat/basic.lean
- \+/\- *theorem* mod_mod
- \+/\- *theorem* fact_one
- \+/\- *theorem* mod_mod
- \+/\- *theorem* fact_one

modified src/data/nat/enat.lean
- \+ *lemma* get_coe
- \+/\- *lemma* coe_add_get
- \+/\- *lemma* coe_add_get

modified src/data/num/lemmas.lean

modified src/data/padics/padic_integers.lean
- \+/\- *lemma* add_def
- \+/\- *lemma* mul_def
- \+/\- *lemma* norm_one
- \+/\- *lemma* add_def
- \+/\- *lemma* mul_def
- \+/\- *lemma* norm_one

modified src/data/pequiv.lean
- \+/\- *lemma* of_set_eq_some_self_iff
- \+/\- *lemma* of_set_eq_some_self_iff

modified src/data/pnat/basic.lean
- \+/\- *theorem* to_pnat'_coe
- \+/\- *theorem* to_pnat'_coe

modified src/data/polynomial.lean
- \+/\- *lemma* coeff_C_mul_X
- \+/\- *lemma* coeff_one
- \+/\- *lemma* coeff_C_mul_X
- \+/\- *lemma* coeff_one

modified src/data/rat/basic.lean

modified src/data/rat/cast.lean
- \+/\- *theorem* cast_ne_zero
- \+/\- *theorem* cast_ne_zero

modified src/data/real/ennreal.lean
- \+/\- *lemma* two_ne_zero
- \+/\- *lemma* two_ne_top
- \+/\- *lemma* zero_lt_coe_iff
- \+/\- *lemma* inv_le_inv
- \+/\- *lemma* two_ne_zero
- \+/\- *lemma* two_ne_top
- \+/\- *lemma* zero_lt_coe_iff
- \+/\- *lemma* inv_le_inv

modified src/data/real/hyperreal.lean
- \+ *lemma* hyperfilter_ne_bot
- \+ *lemma* hyperfilter_ne_bot'
- \+ *lemma* coe_eq_coe
- \+ *lemma* cast_div
- \+ *lemma* coe_lt_coe
- \+ *lemma* coe_le_coe
- \+ *lemma* coe_abs
- \+ *lemma* coe_max
- \+ *lemma* coe_min

modified src/data/real/nnreal.lean
- \+/\- *theorem* coe_mk
- \+/\- *theorem* coe_mk

modified src/data/seq/seq.lean
- \+/\- *theorem* join_cons
- \+/\- *theorem* join_cons

modified src/data/set/basic.lean
- \+/\- *lemma* image_id'
- \+/\- *lemma* val_range
- \+/\- *lemma* range_val
- \- *lemma* set_of_mem
- \+/\- *lemma* image_id'
- \+/\- *lemma* val_range
- \+/\- *lemma* range_val
- \+/\- *theorem* insert_of_has_insert
- \+/\- *theorem* compl_compl
- \+/\- *theorem* ball_image_iff
- \+/\- *theorem* image_id
- \+/\- *theorem* insert_of_has_insert
- \+/\- *theorem* compl_compl
- \+/\- *theorem* ball_image_iff
- \+/\- *theorem* image_id

modified src/data/set/function.lean
- \+/\- *lemma* piecewise_eq_of_mem
- \+/\- *lemma* piecewise_eq_of_not_mem
- \+/\- *lemma* piecewise_insert_of_ne
- \+/\- *lemma* piecewise_eq_of_mem
- \+/\- *lemma* piecewise_eq_of_not_mem
- \+/\- *lemma* piecewise_insert_of_ne

modified src/data/set/lattice.lean
- \+/\- *theorem* mem_sUnion
- \+/\- *theorem* mem_sUnion

modified src/data/sigma/basic.lean
- \+/\- *theorem* sigma.mk.inj_iff
- \+/\- *theorem* sigma.mk.inj_iff

modified src/data/subtype.lean
- \+/\- *theorem* mk_eq_mk
- \+/\- *theorem* mk_eq_mk

modified src/data/sum.lean
- \+/\- *theorem* inl.inj_iff
- \+/\- *theorem* inr.inj_iff
- \+/\- *theorem* inl_ne_inr
- \+/\- *theorem* inr_ne_inl
- \+/\- *theorem* inl.inj_iff
- \+/\- *theorem* inr.inj_iff
- \+/\- *theorem* inl_ne_inr
- \+/\- *theorem* inr_ne_inl

modified src/data/zmod/basic.lean
- \+/\- *lemma* cast_mod_nat'
- \+/\- *lemma* cast_mod_int'
- \+/\- *lemma* cast_mod_nat'
- \+/\- *lemma* cast_mod_int'

modified src/group_theory/perm/sign.lean
- \- *lemma* swap_mul_self
- \- *lemma* swap_swap_apply

modified src/linear_algebra/basic.lean
- \+/\- *theorem* map_ne_zero_iff
- \+/\- *theorem* map_ne_zero_iff

modified src/linear_algebra/special_linear_group.lean
- \+/\- *lemma* det_coe_fun
- \+/\- *lemma* det_coe_fun

modified src/logic/basic.lean
- \+/\- *theorem* coe_fn_coe_trans
- \+/\- *theorem* coe_sort_coe_trans
- \+/\- *theorem* false_ne_true
- \+/\- *theorem* imp_true_iff
- \+/\- *theorem* not_and_not_right
- \+/\- *theorem* coe_fn_coe_trans
- \+/\- *theorem* coe_sort_coe_trans
- \+/\- *theorem* false_ne_true
- \+/\- *theorem* imp_true_iff
- \+/\- *theorem* not_and_not_right

modified src/order/complete_lattice.lean
- \+/\- *theorem* Sup_singleton
- \+/\- *theorem* Inf_singleton
- \+/\- *theorem* infi_const
- \+/\- *theorem* supr_const
- \+/\- *theorem* Sup_singleton
- \+/\- *theorem* Inf_singleton
- \+/\- *theorem* infi_const
- \+/\- *theorem* supr_const
- \- *theorem* insert_of_has_insert

modified src/order/conditionally_complete_lattice.lean

modified src/order/filter/basic.lean
- \+/\- *lemma* principal_ne_bot_iff
- \+/\- *lemma* principal_ne_bot_iff

modified src/order/filter/filter_product.lean
- \+ *lemma* coe_injective
- \+/\- *lemma* of_eq_zero
- \+/\- *lemma* of_ne_zero
- \+/\- *lemma* of_zero
- \+/\- *lemma* of_add
- \+ *lemma* of_bit0
- \+ *lemma* of_bit1
- \+/\- *lemma* of_neg
- \+/\- *lemma* of_sub
- \+/\- *lemma* of_one
- \+/\- *lemma* of_mul
- \+/\- *lemma* of_inv
- \+/\- *lemma* of_div
- \+/\- *lemma* of_eq_zero
- \+/\- *lemma* of_ne_zero
- \+/\- *lemma* of_zero
- \+/\- *lemma* of_add
- \+/\- *lemma* of_neg
- \+/\- *lemma* of_sub
- \+/\- *lemma* of_one
- \+/\- *lemma* of_mul
- \+/\- *lemma* of_inv
- \+/\- *lemma* of_div

modified src/ring_theory/localization.lean
- \+/\- *lemma* of_is_unit
- \+/\- *lemma* coe_is_unit
- \+/\- *lemma* mk_self
- \+/\- *lemma* mk_self'
- \+/\- *lemma* mk_self''
- \+/\- *lemma* mk_mul_cancel_left
- \+/\- *lemma* mk_mul_cancel_right
- \+/\- *lemma* mk_eq_div
- \+/\- *lemma* of_is_unit
- \+/\- *lemma* coe_is_unit
- \+/\- *lemma* mk_self
- \+/\- *lemma* mk_self'
- \+/\- *lemma* mk_self''
- \+/\- *lemma* mk_mul_cancel_left
- \+/\- *lemma* mk_mul_cancel_right
- \+/\- *lemma* mk_eq_div

modified src/ring_theory/multiplicity.lean
- \+/\- *lemma* one_left
- \+/\- *lemma* one_left

modified src/ring_theory/power_series.lean
- \+/\- *lemma* coeff_zero_one
- \+/\- *lemma* coeff_zero_C
- \+/\- *lemma* coeff_zero_X
- \+/\- *lemma* coeff_zero_mul_X
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* coeff_zero_one
- \+/\- *lemma* coeff_zero_C
- \+/\- *lemma* coeff_zero_X
- \+/\- *lemma* coeff_zero_mul_X
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* inv_of_unit_eq

modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *theorem* factor_set.coe_add
- \+/\- *theorem* factor_set.coe_add

modified src/set_theory/cardinal.lean
- \+/\- *theorem* mk_unit
- \+/\- *theorem* mk_unit

modified src/set_theory/ordinal.lean
- \+/\- *theorem* coe_coe_fn
- \+/\- *theorem* of_iso_apply
- \+/\- *theorem* coe_coe_fn
- \+/\- *theorem* lt_le_apply
- \+/\- *theorem* trans_apply
- \+/\- *theorem* trans_top
- \+/\- *theorem* equiv_lt_apply
- \+/\- *theorem* of_element_apply
- \+/\- *theorem* type_ne_zero_iff_nonempty
- \+/\- *theorem* one_add_of_omega_le
- \+/\- *theorem* nat_cast_ne_zero
- \+/\- *theorem* coe_coe_fn
- \+/\- *theorem* of_iso_apply
- \+/\- *theorem* coe_coe_fn
- \+/\- *theorem* lt_le_apply
- \+/\- *theorem* trans_apply
- \+/\- *theorem* trans_top
- \+/\- *theorem* equiv_lt_apply
- \+/\- *theorem* of_element_apply
- \+/\- *theorem* type_ne_zero_iff_nonempty
- \+/\- *theorem* one_add_of_omega_le
- \+/\- *theorem* nat_cast_ne_zero

modified src/set_theory/pgame.lean
- \+/\- *lemma* relabel_move_left
- \+/\- *lemma* relabel_move_right
- \+/\- *lemma* relabel_move_left
- \+/\- *lemma* relabel_move_right

modified src/tactic/converter/binders.lean
- \- *theorem* mem_image

modified src/tactic/lint.lean
- \- *lemma* -

modified src/topology/algebra/module.lean
- \+/\- *lemma* id_apply
- \+/\- *lemma* sub_apply
- \+ *lemma* sub_apply'
- \+/\- *lemma* id_apply
- \+/\- *lemma* sub_apply

modified src/topology/category/Top/open_nhds.lean
- \+/\- *lemma* map_id_obj'
- \+/\- *lemma* map_id_obj'

modified src/topology/category/Top/opens.lean
- \+/\- *lemma* map_id_obj'
- \+/\- *lemma* map_comp_obj'
- \+/\- *lemma* map_id_obj'
- \+/\- *lemma* map_comp_obj'

modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *lemma* Hausdorff_edist_self_closure
- \+/\- *lemma* Hausdorff_dist_self_closure
- \+/\- *lemma* Hausdorff_edist_self_closure
- \+/\- *lemma* Hausdorff_dist_self_closure

modified src/topology/sheaves/presheaf.lean
- \+/\- *lemma* id_hom_app
- \+/\- *lemma* id_hom_app

modified test/lint_simp_nf.lean



## [2020-03-03 09:04:21](https://github.com/leanprover-community/mathlib/commit/2d1bd45)
fix some docstrings [ci skip] ([#2078](https://github.com/leanprover-community/mathlib/pull/2078))
#### Estimated changes
modified src/category/monad/writer.lean

modified src/category_theory/concrete_category/bundled_hom.lean



## [2020-03-03 07:18:28](https://github.com/leanprover-community/mathlib/commit/2a9ad03)
feat(data/list/basic): more lemmas about `list.chain'`; `chain'_of_pairwise` → `pairwise.chain'` ([#2071](https://github.com/leanprover-community/mathlib/pull/2071))
#### Estimated changes
modified src/data/list/basic.lean
- \+ *theorem* chain.imp'
- \+ *theorem* chain'_nil
- \+/\- *theorem* chain'_singleton
- \+ *theorem* pairwise.chain'
- \+ *theorem* chain'_cons
- \+ *theorem* chain'.cons
- \+ *theorem* chain'.tail
- \+ *theorem* chain'_pair
- \+ *theorem* chain'_reverse
- \+/\- *theorem* chain'_singleton
- \- *theorem* chain'_of_pairwise



## [2020-03-03 05:29:57](https://github.com/leanprover-community/mathlib/commit/e003014)
feat(analysis/calculus/iterated_deriv): iterated derivative of a function defined on the base field ([#2067](https://github.com/leanprover-community/mathlib/pull/2067))
* iterated deriv
* cleanup
* fix docstring
* add iterated_deriv_within_succ'
* remove n.succ
* n+1 -> n + 1
#### Estimated changes
created src/analysis/calculus/iterated_deriv.lean
- \+ *lemma* iterated_deriv_within_univ
- \+ *lemma* iterated_deriv_within_eq_iterated_fderiv_within
- \+ *lemma* iterated_deriv_within_eq_equiv_comp
- \+ *lemma* iterated_fderiv_within_eq_equiv_comp
- \+ *lemma* iterated_fderiv_within_apply_eq_iterated_deriv_within_mul_prod
- \+ *lemma* iterated_deriv_within_zero
- \+ *lemma* iterated_deriv_within_one
- \+ *lemma* times_cont_diff_on_of_continuous_on_differentiable_on_deriv
- \+ *lemma* times_cont_diff_on_of_differentiable_on_deriv
- \+ *lemma* times_cont_diff_on.continuous_on_iterated_deriv_within
- \+ *lemma* times_cont_diff_on.differentiable_on_iterated_deriv_within
- \+ *lemma* times_cont_diff_on_iff_continuous_on_differentiable_on_deriv
- \+ *lemma* iterated_deriv_within_succ
- \+ *lemma* iterated_deriv_within_eq_iterate
- \+ *lemma* iterated_deriv_within_succ'
- \+ *lemma* iterated_deriv_eq_iterated_fderiv
- \+ *lemma* iterated_deriv_eq_equiv_comp
- \+ *lemma* iterated_fderiv_eq_equiv_comp
- \+ *lemma* iterated_fderiv_apply_eq_iterated_deriv_mul_prod
- \+ *lemma* iterated_deriv_zero
- \+ *lemma* iterated_deriv_one
- \+ *lemma* times_cont_diff_iff_iterated_deriv
- \+ *lemma* times_cont_diff_of_differentiable_iterated_deriv
- \+ *lemma* times_cont_diff.continuous_iterated_deriv
- \+ *lemma* times_cont_diff.differentiable_iterated_deriv
- \+ *lemma* iterated_deriv_succ
- \+ *lemma* iterated_deriv_eq_iterate
- \+ *lemma* iterated_deriv_succ'
- \+ *def* iterated_deriv
- \+ *def* iterated_deriv_within

modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* iterated_fderiv_within_succ_apply_left
- \+/\- *lemma* iterated_fderiv_succ_apply_left
- \+/\- *lemma* iterated_fderiv_within_succ_apply_left
- \+/\- *lemma* iterated_fderiv_succ_apply_left
- \+/\- *theorem* iterated_fderiv_succ_apply_right
- \+/\- *theorem* iterated_fderiv_succ_apply_right



## [2020-03-03 00:17:40](https://github.com/leanprover-community/mathlib/commit/262a39e)
chore(scripts): update nolints.txt
#### Estimated changes
modified scripts/nolints.txt



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
modified docs/tactics.md

modified src/algebra/ordered_group.lean
- \+/\- *lemma* bot_eq_zero
- \+/\- *lemma* bot_eq_zero

modified src/data/finset.lean
- \+ *lemma* Ico_ℤ.mem
- \- *lemma* mem

modified src/data/fintype/intervals.lean

modified src/data/list/basic.lean
- \+ *lemma* trichotomy

modified src/data/nat/basic.lean
- \+ *lemma* add_one_le_iff
- \+ *lemma* one_add_le_iff
- \+ *lemma* pos_of_bit0_pos

modified src/data/pnat/basic.lean
- \+ *lemma* one_le
- \+ *lemma* bot_eq_zero
- \+ *lemma* mk_one
- \+ *lemma* mk_bit0
- \+ *lemma* mk_bit1
- \+ *lemma* bit0_le_bit0
- \+ *lemma* bit0_le_bit1
- \+ *lemma* bit1_le_bit0
- \+ *lemma* bit1_le_bit1
- \+ *theorem* lt_add_one_iff
- \+ *theorem* add_one_le_iff

created src/data/pnat/intervals.lean
- \+ *lemma* Ico.mem
- \+ *def* Ico

modified src/tactic/default.lean

modified src/tactic/fin_cases.lean

created src/tactic/interval_cases.lean
- \+ *lemma* mem_set_elems
- \+ *def* set_elems

modified test/fin_cases.lean

created test/interval_cases.lean



## [2020-03-02 19:54:08](https://github.com/leanprover-community/mathlib/commit/1d82a7c)
doc(data/fin): add docs; fin_zero_elim -> fin.elim0; fin_zero_elim' -> fin_zero_elim ([#2055](https://github.com/leanprover-community/mathlib/pull/2055))
* doc(data/fin): add some docs
Also drom `fin_zero_elim` in favor of `fin.elim0` from `stdlib` and
rename `fin_zero_elim'` to `fin_zero_elim`.
* Update src/data/fin.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update docs, fix `Π` vs `∀`.
#### Estimated changes
modified src/data/fin.lean
- \+/\- *def* fin_zero_elim
- \+/\- *def* fin_zero_elim
- \- *def* fin_zero_elim'



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
modified src/data/finset.lean
- \+ *lemma* singleton_subset_iff
- \+ *lemma* union_eq_left_iff_subset
- \+ *lemma* left_eq_union_iff_subset
- \+ *lemma* union_eq_right_iff_subset
- \+ *lemma* right_eq_union_iff_subset
- \+ *lemma* sdiff_subset
- \+ *lemma* pi_subset
- \+ *lemma* pi_disjoint_of_disjoint
- \+/\- *theorem* min'_mem
- \+/\- *theorem* min'_le
- \+/\- *theorem* le_min'
- \+/\- *theorem* max'_mem
- \+/\- *theorem* le_max'
- \+/\- *theorem* max'_le
- \+/\- *theorem* min'_lt_max'
- \+/\- *theorem* min'_mem
- \+/\- *theorem* min'_le
- \+/\- *theorem* le_min'
- \+/\- *theorem* max'_mem
- \+/\- *theorem* le_max'
- \+/\- *theorem* max'_le
- \+/\- *theorem* min'_lt_max'
- \+/\- *def* min'
- \+/\- *def* max'
- \+/\- *def* min'
- \+/\- *def* max'

modified src/data/fintype.lean
- \+ *lemma* finset.card_le_one_iff
- \+ *lemma* finset.one_lt_card_iff
- \+ *lemma* mem_pi_finset
- \+ *lemma* pi_finset_subset
- \+ *lemma* pi_finset_disjoint_of_disjoint
- \+ *lemma* pi_finset_univ
- \+ *def* pi_finset

modified src/data/fintype/card.lean
- \+ *lemma* fintype.card_pi_finset

modified src/measure_theory/integration.lean



## [2020-03-02 16:19:30](https://github.com/leanprover-community/mathlib/commit/62756bd)
chore(data/real/ennreal): weaker assumptions in `sub_mul`, add `coe_inv_le` ([#2074](https://github.com/leanprover-community/mathlib/pull/2074))
#### Estimated changes
modified src/data/real/ennreal.lean
- \+/\- *lemma* sub_mul
- \+/\- *lemma* mul_sub
- \+ *lemma* sub_mul_ge
- \+ *lemma* coe_inv_le
- \+/\- *lemma* sub_mul
- \+/\- *lemma* mul_sub



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
modified src/algebra/group/conj.lean

modified src/algebra/group/hom.lean
- \- *lemma* mul
- \- *lemma* inv
- \- *lemma* map_mul
- \- *lemma* is_group_hom.mk'
- \- *lemma* map_one
- \- *lemma* injective_iff
- \- *lemma* mul
- \- *lemma* inv
- \- *lemma* inv.is_group_hom
- \- *lemma* map_sub
- \- *lemma* is_add_group_hom.sub
- \- *lemma* coe_of
- \- *theorem* is_monoid_hom.of_mul
- \- *theorem* map_inv
- \- *def* of

modified src/algebra/group/is_unit.lean
- \- *lemma* is_unit.map'

modified src/algebra/group/type_tags.lean

modified src/algebra/group/units_hom.lean
- \- *lemma* coe_map'
- \- *def* map'

modified src/algebra/group/with_one.lean
- \+/\- *lemma* lift_coe
- \+/\- *lemma* lift_one
- \+/\- *lemma* lift_coe
- \+/\- *lemma* lift_one
- \- *lemma* map_eq
- \+/\- *theorem* lift_unique
- \+/\- *theorem* lift_unique
- \+/\- *def* lift
- \+/\- *def* map
- \+/\- *def* lift
- \+/\- *def* map

modified src/algebra/ring.lean

created src/deprecated/group.lean
- \+ *lemma* mul
- \+ *lemma* inv
- \+ *lemma* coe_of
- \+ *lemma* map_mul
- \+ *lemma* is_group_hom.mk'
- \+ *lemma* map_one
- \+ *lemma* injective_iff
- \+ *lemma* mul
- \+ *lemma* inv
- \+ *lemma* inv.is_group_hom
- \+ *lemma* map_sub
- \+ *lemma* is_add_group_hom.sub
- \+ *lemma* coe_map'
- \+ *lemma* map'
- \+ *theorem* is_monoid_hom.of_mul
- \+ *theorem* map_inv
- \+ *def* of
- \+ *def* map'

modified src/group_theory/perm/sign.lean



## [2020-03-02 12:33:13](https://github.com/leanprover-community/mathlib/commit/3055b3c)
chore(topology/metric_space/isometry): rename `(e)metric.isometry.diam_image` to `isometry.(e)diam_image` ([#2073](https://github.com/leanprover-community/mathlib/pull/2073))
This way we can use dot notation to access these lemmas. Also add `(e)diam_range`.
#### Estimated changes
modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometry.ediam_image
- \+ *lemma* isometry.ediam_range
- \+ *lemma* isometry.diam_image
- \+ *lemma* isometry.diam_range
- \- *lemma* emetric.isometry.diam_image
- \- *lemma* metric.isometry.diam_image



## [2020-03-02 10:42:53](https://github.com/leanprover-community/mathlib/commit/2683fa0)
feat(order/galois_connection): lemmas about galois insertions and supr/infi ([#2052](https://github.com/leanprover-community/mathlib/pull/2052))
* feat(order/galois_connection): lemmas about galois insertions and supr/infi
* Fix build, hopefully
#### Estimated changes
modified src/order/galois_connection.lean
- \+/\- *lemma* l_u_eq
- \+ *lemma* l_surjective
- \+ *lemma* u_injective
- \+ *lemma* l_sup_u
- \+ *lemma* l_supr_u
- \+ *lemma* l_supr_of_ul
- \+ *lemma* l_inf_u
- \+ *lemma* l_infi_u
- \+ *lemma* l_infi_of_ul
- \+/\- *lemma* l_u_eq
- \+/\- *theorem* order_iso.to_galois_connection
- \+/\- *theorem* order_iso.to_galois_connection

modified src/topology/opens.lean



## [2020-03-02 08:53:22](https://github.com/leanprover-community/mathlib/commit/d5d907b)
feat(algebra/free_monoid): define `lift` and `map`, move out of `algebra/group` ([#2060](https://github.com/leanprover-community/mathlib/pull/2060))
* Move `free_monoid` from `algebra/group/` to `algebra/`
* feat(algebra/free_monoid): define `lift` and `map`
* Expand docstring, drop unneeded arguments to `to_additive`
* Fix compile
* Update src/algebra/free_monoid.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
#### Estimated changes
created src/algebra/free_monoid.lean
- \+ *lemma* one_def
- \+ *lemma* mul_def
- \+ *lemma* of_mul_eq_cons
- \+ *lemma* hom_eq
- \+ *lemma* lift_eval_of
- \+ *lemma* lift_restrict
- \+ *lemma* map_of
- \+ *lemma* lift_of_comp_eq_map
- \+ *lemma* map_comp
- \+ *def* free_monoid
- \+ *def* of
- \+ *def* lift
- \+ *def* map

modified src/algebra/group/default.lean

deleted src/algebra/group/free_monoid.lean
- \- *lemma* free_monoid.one_def
- \- *lemma* free_monoid.mul_def
- \- *def* free_monoid

modified src/category/fold.lean

modified src/ring_theory/free_ring.lean



## [2020-03-01 23:09:46-08:00](https://github.com/leanprover-community/mathlib/commit/aec54b3)
fix(.mergify.yml): remove " (leanprover-community/lean:3.5.1)" ([#2077](https://github.com/leanprover-community/mathlib/pull/2077))
#### Estimated changes
modified .mergify.yml

