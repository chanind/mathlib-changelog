## [2019-09-30 14:17:53](https://github.com/leanprover-community/mathlib/commit/374c290)
chore(linear_algebra): continue removing decidable_eq assumptions ([#1404](https://github.com/leanprover-community/mathlib/pull/1404))
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
#### Estimated changes
Modified src/field_theory/finite_card.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* linear_map.std_basis_eq_single

Modified src/linear_algebra/basis.lean
- \+/\- *lemma* constr_smul
- \+/\- *lemma* is_basis_singleton_one
- \+/\- *lemma* pi.is_basis_std_basis
- \+/\- *lemma* pi.linear_independent_std_basis

Modified src/linear_algebra/dimension.lean
- \+/\- *theorem* dim_quotient
- \+/\- *lemma* dim_span
- \+/\- *lemma* dim_span_set
- \+/\- *lemma* exists_is_basis_fintype
- \+/\- *theorem* is_basis.le_span
- \+/\- *theorem* is_basis.mk_eq_dim
- \+/\- *theorem* is_basis.mk_range_eq_dim
- \+/\- *theorem* linear_equiv.dim_eq_lift
- \+/\- *theorem* mk_eq_mk_of_basis

Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* finite_dimensional.card_eq_findim
- \+/\- *lemma* finite_dimensional.of_fg

Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/matrix.lean
- \+/\- *def* lin_equiv_matrix'
- \+/\- *def* lin_equiv_matrix
- \+/\- *lemma* matrix.rank_diagonal
- \+/\- *lemma* to_matrix_to_lin

Modified src/ring_theory/noetherian.lean




## [2019-09-30 08:55:58](https://github.com/leanprover-community/mathlib/commit/c6fab42)
feat(ring_theory/power_series): order ([#1292](https://github.com/leanprover-community/mathlib/pull/1292))
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
#### Estimated changes
Modified src/ring_theory/ideal_operations.lean
- \+ *lemma* is_ring_hom.ker_is_prime
- \+ *lemma* is_ring_hom.mem_ker
- \+ *lemma* is_ring_hom.not_one_mem_ker

Modified src/ring_theory/power_series.lean
- \+ *lemma* mv_polynomial.coe_C
- \+ *lemma* mv_polynomial.coe_X
- \+ *lemma* mv_polynomial.coe_add
- \+ *lemma* mv_polynomial.coe_monomial
- \+ *lemma* mv_polynomial.coe_mul
- \+ *lemma* mv_polynomial.coe_one
- \+ *lemma* mv_polynomial.coe_zero
- \+ *lemma* mv_polynomial.coeff_coe
- \- *def* mv_polynomial.to_mv_power_series
- \- *lemma* mv_polynomial.to_mv_power_series_coeff
- \+/\- *def* mv_power_series.C
- \- *lemma* mv_power_series.C_add
- \- *lemma* mv_power_series.C_mul
- \- *lemma* mv_power_series.C_one
- \- *lemma* mv_power_series.C_zero
- \+/\- *def* mv_power_series.X
- \+ *lemma* mv_power_series.X_def
- \+ *lemma* mv_power_series.X_dvd_iff
- \+ *lemma* mv_power_series.X_inj
- \+ *lemma* mv_power_series.X_pow_dvd_iff
- \+ *lemma* mv_power_series.X_pow_eq
- \+/\- *def* mv_power_series.coeff
- \- *lemma* mv_power_series.coeff_C_zero
- \- *lemma* mv_power_series.coeff_X''
- \- *lemma* mv_power_series.coeff_X'
- \+ *lemma* mv_power_series.coeff_X_pow
- \- *lemma* mv_power_series.coeff_add
- \+ *lemma* mv_power_series.coeff_comp_monomial
- \+ *lemma* mv_power_series.coeff_index_single_X
- \+ *lemma* mv_power_series.coeff_index_single_self_X
- \+/\- *lemma* mv_power_series.coeff_inv
- \+/\- *lemma* mv_power_series.coeff_map
- \+/\- *lemma* mv_power_series.coeff_mul
- \- *lemma* mv_power_series.coeff_neg
- \+/\- *lemma* mv_power_series.coeff_one
- \- *lemma* mv_power_series.coeff_one_zero
- \+/\- *lemma* mv_power_series.coeff_trunc
- \+/\- *lemma* mv_power_series.coeff_zero
- \+ *lemma* mv_power_series.coeff_zero_C
- \+ *lemma* mv_power_series.coeff_zero_X
- \+ *lemma* mv_power_series.coeff_zero_eq_constant_coeff
- \+ *lemma* mv_power_series.coeff_zero_eq_constant_coeff_apply
- \- *lemma* mv_power_series.coeff_zero_inv
- \- *lemma* mv_power_series.coeff_zero_inv_of_unit
- \+ *lemma* mv_power_series.coeff_zero_one
- \+ *def* mv_power_series.constant_coeff
- \+ *lemma* mv_power_series.constant_coeff_C
- \+ *lemma* mv_power_series.constant_coeff_X
- \+ *lemma* mv_power_series.constant_coeff_comp_C
- \+ *lemma* mv_power_series.constant_coeff_inv
- \+ *lemma* mv_power_series.constant_coeff_inv_of_unit
- \+ *lemma* mv_power_series.constant_coeff_map
- \+ *lemma* mv_power_series.constant_coeff_one
- \+ *lemma* mv_power_series.constant_coeff_zero
- \+/\- *lemma* mv_power_series.ext
- \+/\- *lemma* mv_power_series.inv_of_unit_eq'
- \+/\- *lemma* mv_power_series.inv_of_unit_eq
- \- *lemma* mv_power_series.is_unit_coeff_zero
- \+ *lemma* mv_power_series.is_unit_constant_coeff
- \+/\- *def* mv_power_series.map
- \- *lemma* mv_power_series.map_add
- \+/\- *lemma* mv_power_series.map_comp
- \+/\- *lemma* mv_power_series.map_id
- \- *lemma* mv_power_series.map_mul
- \- *lemma* mv_power_series.map_one
- \- *lemma* mv_power_series.map_zero
- \+/\- *def* mv_power_series.monomial
- \- *lemma* mv_power_series.monomial_add
- \+ *lemma* mv_power_series.monomial_mul_monomial
- \- *lemma* mv_power_series.monomial_zero
- \+ *lemma* mv_power_series.monomial_zero_eq_C
- \+ *lemma* mv_power_series.monomial_zero_eq_C_apply
- \+/\- *lemma* mv_power_series.mul_inv_of_unit
- \+/\- *def* mv_power_series.trunc
- \+/\- *lemma* mv_power_series.trunc_C
- \- *lemma* mv_power_series.trunc_add
- \+ *def* mv_power_series.trunc_fun
- \+/\- *lemma* mv_power_series.trunc_one
- \- *lemma* mv_power_series.trunc_zero
- \+ *lemma* polynomial.coe_C
- \+ *lemma* polynomial.coe_X
- \+ *lemma* polynomial.coe_add
- \+ *lemma* polynomial.coe_monomial
- \+ *lemma* polynomial.coe_mul
- \+ *lemma* polynomial.coe_one
- \+ *lemma* polynomial.coe_zero
- \+ *lemma* polynomial.coeff_coe
- \+ *def* polynomial.monomial
- \- *def* polynomial.to_power_series
- \- *lemma* polynomial.to_power_series_coeff
- \+/\- *def* power_series.C
- \- *lemma* power_series.C_add
- \- *lemma* power_series.C_mul
- \- *lemma* power_series.C_one
- \- *lemma* power_series.C_zero
- \+ *lemma* power_series.X_dvd_iff
- \+ *lemma* power_series.X_eq
- \+ *lemma* power_series.X_pow_dvd_iff
- \+ *lemma* power_series.X_pow_eq
- \+ *lemma* power_series.X_prime
- \+/\- *def* power_series.coeff
- \- *lemma* power_series.coeff_C_zero
- \- *lemma* power_series.coeff_X'
- \+ *lemma* power_series.coeff_X_pow
- \+ *lemma* power_series.coeff_X_pow_self
- \- *lemma* power_series.coeff_add
- \+ *lemma* power_series.coeff_comp_monomial
- \+ *lemma* power_series.coeff_def
- \+/\- *lemma* power_series.coeff_mk
- \+ *lemma* power_series.coeff_of_lt_order
- \+ *lemma* power_series.coeff_one_X
- \- *lemma* power_series.coeff_one_zero
- \+ *lemma* power_series.coeff_order
- \- *lemma* power_series.coeff_zero
- \+ *lemma* power_series.coeff_zero_C
- \+ *lemma* power_series.coeff_zero_X
- \+ *lemma* power_series.coeff_zero_eq_constant_coeff
- \+ *lemma* power_series.coeff_zero_eq_constant_coeff_apply
- \- *lemma* power_series.coeff_zero_inv
- \- *lemma* power_series.coeff_zero_inv_of_unit
- \+ *lemma* power_series.coeff_zero_one
- \+ *def* power_series.constant_coeff
- \+ *lemma* power_series.constant_coeff_C
- \+ *lemma* power_series.constant_coeff_X
- \+ *lemma* power_series.constant_coeff_comp_C
- \+ *lemma* power_series.constant_coeff_inv
- \+ *lemma* power_series.constant_coeff_inv_of_unit
- \+ *lemma* power_series.constant_coeff_one
- \+ *lemma* power_series.constant_coeff_zero
- \+ *lemma* power_series.eq_zero_or_eq_zero_of_mul_eq_zero
- \+/\- *lemma* power_series.ext
- \+/\- *lemma* power_series.ext_iff
- \+/\- *lemma* power_series.inv_of_unit_eq'
- \+/\- *lemma* power_series.inv_of_unit_eq
- \+ *lemma* power_series.is_unit_constant_coeff
- \+/\- *def* power_series.map
- \- *lemma* power_series.map_add
- \+/\- *lemma* power_series.map_comp
- \+/\- *lemma* power_series.map_id
- \- *lemma* power_series.map_mul
- \- *lemma* power_series.map_one
- \- *lemma* power_series.map_zero
- \+/\- *def* power_series.monomial
- \- *lemma* power_series.monomial_add
- \- *lemma* power_series.monomial_zero
- \+ *lemma* power_series.monomial_zero_eq_C
- \+ *lemma* power_series.monomial_zero_eq_C_apply
- \+/\- *lemma* power_series.mul_inv_of_unit
- \+ *def* power_series.order
- \+ *lemma* power_series.order_X
- \+ *lemma* power_series.order_X_pow
- \+ *lemma* power_series.order_add_ge
- \+ *lemma* power_series.order_add_of_order_eq
- \+ *lemma* power_series.order_eq
- \+ *lemma* power_series.order_eq_nat
- \+ *lemma* power_series.order_eq_top
- \+ *lemma* power_series.order_finite_of_coeff_ne_zero
- \+ *lemma* power_series.order_ge
- \+ *lemma* power_series.order_ge_nat
- \+ *lemma* power_series.order_le
- \+ *lemma* power_series.order_monomial
- \+ *lemma* power_series.order_monomial_of_ne_zero
- \+ *lemma* power_series.order_mul
- \+ *lemma* power_series.order_mul_ge
- \+ *lemma* power_series.order_one
- \+ *lemma* power_series.order_zero
- \+ *lemma* power_series.span_X_is_prime
- \+/\- *lemma* power_series.trunc_C



## [2019-09-28 22:44:16](https://github.com/leanprover-community/mathlib/commit/30aa8d2)
chore(order/basic): rename `monotone_comp` to `monotone.comp`, reorder arguments ([#1497](https://github.com/leanprover-community/mathlib/pull/1497))
#### Estimated changes
Modified src/order/basic.lean
- \- *theorem* monotone_comp

Modified src/order/filter/lift.lean


Modified src/order/fixed_points.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/completion.lean




## [2019-09-27 22:59:45](https://github.com/leanprover-community/mathlib/commit/708faa9)
feat(geometry/manifold/manifold): define manifolds ([#1422](https://github.com/leanprover-community/mathlib/pull/1422))
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
#### Estimated changes
Added src/geometry/manifold/manifold.lean
- \+ *lemma* chart_at_model_space_eq
- \+ *def* continuous_groupoid
- \+ *def* groupoid_of_pregroupoid
- \+ *lemma* groupoid_of_pregroupoid_le
- \+ *lemma* has_groupoid_of_le
- \+ *def* id_groupoid
- \+ *def* manifold_core.local_homeomorph
- \+ *lemma* manifold_core.open_source'
- \+ *lemma* manifold_core.open_target
- \+ *def* manifold_core.to_manifold
- \+ *lemma* mem_groupoid_of_pregroupoid
- \+ *lemma* model_space_atlas
- \+ *def* structomorph.refl
- \+ *def* structomorph.symm
- \+ *def* structomorph.trans



## [2019-09-27 18:10:21](https://github.com/leanprover-community/mathlib/commit/e0c204e)
chore(algebra/group_power): move inv_one from group_power to field ([#1495](https://github.com/leanprover-community/mathlib/pull/1495))
* chore(algebra/group_power): move inv_one from group_power to field
*  fix
#### Estimated changes
Modified src/algebra/field.lean
- \+ *theorem* inv_one

Modified src/algebra/group_power.lean
- \- *theorem* inv_one



## [2019-09-27 16:05:10](https://github.com/leanprover-community/mathlib/commit/74f09d0)
chore(algebra/char_p): remove some decidable_eq assumptions ([#1492](https://github.com/leanprover-community/mathlib/pull/1492))
* chore(algebra/char_p): remove some decidable_eq assumptions
*  fix build
#### Estimated changes
Modified src/algebra/char_p.lean
- \+/\- *theorem* char_p.char_is_prime
- \+/\- *theorem* char_p.char_ne_zero_of_fintype

Modified src/data/set/finite.lean
- \+/\- *lemma* set.not_injective_int_fintype
- \+/\- *lemma* set.not_injective_nat_fintype



## [2019-09-27 14:10:25](https://github.com/leanprover-community/mathlib/commit/ce7c94f)
feat(reduce_projections): add reduce_projections attribute ([#1402](https://github.com/leanprover-community/mathlib/pull/1402))
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
#### Estimated changes
Modified docs/tactics.md


Modified src/meta/expr.lean


Modified src/tactic/basic.lean


Modified src/tactic/core.lean


Modified src/tactic/default.lean


Added src/tactic/simps.lean


Added test/simps.lean
- \+ *def* bar
- \+ *def* baz
- \+ *def* count_nested.nested1
- \+ *def* count_nested.nested2
- \+ *def* foo.bar1
- \+ *def* foo.bar2
- \+ *def* foo.foo
- \+ *def* my_equiv
- \+ *def* name_clash
- \+ *def* name_clash_fst
- \+ *def* name_clash_snd
- \+ *def* name_clash_snd_2
- \+ *def* partially_applied_term
- \+ *def* refl_with_data'
- \+ *def* refl_with_data
- \+ *def* test
- \+ *def* very_partially_applied_term

Modified test/tactics.lean
- \+ *def* dummy
- \+ *def* eta_expansion_test2
- \+ *def* eta_expansion_test
- \+ *def* right_param
- \+ *def* wrong_param



## [2019-09-27 11:47:32](https://github.com/leanprover-community/mathlib/commit/efd5ab2)
feat(logic/function): define `function.involutive` ([#1474](https://github.com/leanprover-community/mathlib/pull/1474))
* feat(logic/function): define `function.involutive`
* Prove that `inv`, `neg`, and `complex.conj` are involutive.
* Move `inv_inv'` to `algebra/field`
#### Estimated changes
Modified src/algebra/field.lean
- \+ *theorem* inv_inv'
- \+ *lemma* inv_involutive'

Modified src/algebra/group/basic.lean
- \+ *lemma* inv_involutive

Modified src/algebra/group_power.lean
- \- *theorem* inv_inv'

Modified src/analysis/complex/polynomial.lean


Modified src/data/complex/basic.lean
- \+/\- *lemma* complex.conj_bijective
- \+ *lemma* complex.conj_involutive

Modified src/data/equiv/basic.lean
- \+ *def* function.involutive.to_equiv

Modified src/data/real/hyperreal.lean
- \+/\- *lemma* hyperreal.inv_epsilon_eq_omega

Modified src/data/real/nnreal.lean
- \+/\- *lemma* nnreal.inv_inv

Modified src/logic/function.lean
- \+ *def* function.involutive
- \+ *lemma* function.involutive_iff_iter_2_eq_id



## [2019-09-27 09:36:44](https://github.com/leanprover-community/mathlib/commit/6a79f8a)
feat(data/int/basic): to_nat lemmas ([#1479](https://github.com/leanprover-community/mathlib/pull/1479))
* feat(data/int/basic): of_nat lemmas
* Adding lt_of_to_nat_lt
* reversing sides of <->
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *theorem* int.lt_of_to_nat_lt
- \+ *theorem* int.lt_to_nat
- \+/\- *theorem* int.to_nat_le
- \+ *theorem* int.to_nat_lt_to_nat



## [2019-09-27 07:02:36](https://github.com/leanprover-community/mathlib/commit/0bc5de5)
chore(*): drop some unused args reported by `#sanity_check_mathlib` ([#1490](https://github.com/leanprover-community/mathlib/pull/1490))
* Drop some unused arguments
* Drop more unused arguments
* Move `round` to the bottom of `algebra/archimedean`
Suggested by @rwbarton
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+/\- *theorem* exists_nat_one_div_lt
- \+/\- *theorem* exists_rat_near
- \+/\- *theorem* rat.cast_round

Modified src/algebra/associated.lean
- \+/\- *lemma* associates.dvd_eq_le
- \+/\- *lemma* associates.eq_of_mul_eq_mul_left
- \+/\- *lemma* associates.le_of_mul_le_mul_left
- \+/\- *lemma* associates.one_or_eq_of_le_of_prime

Modified src/algebra/floor.lean
- \+/\- *lemma* floor_ring_unique

Modified src/algebra/group/units.lean
- \+/\- *theorem* divp_inv

Modified src/algebra/group/with_one.lean
- \+/\- *lemma* with_one.map_eq

Modified src/category/basic.lean


Modified src/category/bitraversable/instances.lean


Modified src/category/monad/writer.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.cofork.condition
- \- *def* category_theory.limits.cofork.condition
- \+ *lemma* category_theory.limits.fork.condition
- \- *def* category_theory.limits.fork.condition

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *lemma* category_theory.limits.pullback.condition
- \+/\- *lemma* category_theory.limits.pushout.condition

Modified src/data/equiv/algebra.lean
- \+/\- *lemma* equiv.coe_units_equiv_ne_zero
- \+/\- *def* equiv.units_equiv_ne_zero

Modified src/data/equiv/basic.lean
- \+/\- *lemma* equiv.symm_trans_swap_trans

Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measure_theory.borel_eq_subtype
- \+/\- *lemma* measure_theory.borel_induced
- \+/\- *lemma* measure_theory.measurable_of_continuous2

Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* is_measurable_inl_image
- \+/\- *lemma* is_measurable_inr_image
- \+/\- *lemma* is_measurable_range_inl
- \+/\- *lemma* is_measurable_range_inr

Modified src/number_theory/pell.lean
- \+/\- *theorem* pell.eq_of_xn_modeq_lem1

Modified src/topology/instances/polynomial.lean
- \+/\- *lemma* polynomial.continuous_eval



## [2019-09-26 20:42:25](https://github.com/leanprover-community/mathlib/commit/15ed039)
fix(scripts/mk_all): ignore hidden files ([#1488](https://github.com/leanprover-community/mathlib/pull/1488))
* fix(scripts/mk_all): ignore hidden files
Emacs sometimes creates temporary files with names like `.#name.lean`.
* Fix comment
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
#### Estimated changes
Modified scripts/mk_all.sh




## [2019-09-26 13:55:55](https://github.com/leanprover-community/mathlib/commit/3cd3341)
feat(field_theory/minimal_polynomial): Basics on minimal polynomials ([#1449](https://github.com/leanprover-community/mathlib/pull/1449))
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
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.lt_add_one_iff
- \+ *lemma* nat.lt_one_add_iff

Modified src/data/polynomial.lean
- \+ *lemma* polynomial.as_sum
- \+ *lemma* polynomial.coeff_eq_zero_of_nat_degree_lt
- \+ *lemma* polynomial.degree_eq_iff_nat_degree_eq
- \+ *lemma* polynomial.degree_eq_iff_nat_degree_eq_of_pos
- \+ *lemma* polynomial.ext
- \- *theorem* polynomial.ext
- \+ *theorem* polynomial.ext_iff
- \+ *lemma* polynomial.finset_sum_coeff
- \+ *lemma* polynomial.hom_eval₂
- \+ *lemma* polynomial.ite_le_nat_degree_coeff
- \+/\- *lemma* polynomial.map_id
- \+ *lemma* polynomial.monic.leading_coeff
- \+ *lemma* polynomial.zero_is_root_of_coeff_zero_eq_zero

Added src/field_theory/minimal_polynomial.lean
- \+ *lemma* minimal_polynomial.aeval
- \+ *lemma* minimal_polynomial.algebra_map'
- \+ *lemma* minimal_polynomial.coeff_zero_eq_zero
- \+ *lemma* minimal_polynomial.coeff_zero_ne_zero
- \+ *lemma* minimal_polynomial.degree_le_of_ne_zero
- \+ *lemma* minimal_polynomial.degree_ne_zero
- \+ *lemma* minimal_polynomial.degree_pos
- \+ *lemma* minimal_polynomial.dvd
- \+ *lemma* minimal_polynomial.irreducible
- \+ *lemma* minimal_polynomial.min
- \+ *lemma* minimal_polynomial.monic
- \+ *lemma* minimal_polynomial.ne_zero
- \+ *lemma* minimal_polynomial.not_is_unit
- \+ *lemma* minimal_polynomial.one
- \+ *lemma* minimal_polynomial.prime
- \+ *lemma* minimal_polynomial.root
- \+ *lemma* minimal_polynomial.unique
- \+ *lemma* minimal_polynomial.zero

Modified src/ring_theory/algebra.lean


Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/power_series.lean




## [2019-09-26 12:04:21](https://github.com/leanprover-community/mathlib/commit/f92e812)
feat(data/setoid): create file about setoids ([#1453](https://github.com/leanprover-community/mathlib/pull/1453))
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
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.exists_of_length_succ
- \+ *lemma* list.last_eq_nth_le
- \+ *theorem* list.length_pos_iff_ne_nil
- \+ *theorem* list.length_pos_of_ne_nil
- \+ *lemma* list.length_scanl
- \+ *theorem* list.ne_nil_of_length_pos

Modified src/data/set/lattice.lean
- \+ *lemma* set.disjoint_left
- \+ *theorem* set.disjoint_right
- \+ *lemma* set.sUnion_eq_univ_iff

Added src/data/setoid.lean
- \+ *lemma* quotient.eq_rel
- \+ *theorem* setoid.Inf_def
- \+ *lemma* setoid.Inf_le
- \+ *lemma* setoid.Sup_def
- \+ *lemma* setoid.Sup_eq_eqv_gen
- \+ *def* setoid.classes
- \+ *lemma* setoid.classes_eqv_classes
- \+ *lemma* setoid.classes_inj
- \+ *theorem* setoid.classes_mk_classes
- \+ *def* setoid.comap
- \+ *def* setoid.correspondence
- \+ *lemma* setoid.empty_not_mem_classes
- \+ *lemma* setoid.eq_eqv_class_of_mem
- \+ *lemma* setoid.eq_iff_classes_eq
- \+ *theorem* setoid.eq_iff_rel_eq
- \+ *lemma* setoid.eq_of_mem_classes
- \+ *lemma* setoid.eq_of_mem_eqv_class
- \+ *lemma* setoid.eqv_class_mem
- \+ *lemma* setoid.eqv_classes_disjoint
- \+ *lemma* setoid.eqv_classes_of_disjoint_union
- \+ *theorem* setoid.eqv_gen_eq
- \+ *lemma* setoid.eqv_gen_idem
- \+ *theorem* setoid.eqv_gen_le
- \+ *theorem* setoid.eqv_gen_mono
- \+ *lemma* setoid.eqv_gen_of_setoid
- \+ *lemma* setoid.exists_of_mem_partition
- \+ *lemma* setoid.ext'
- \+ *lemma* setoid.ext_iff
- \+ *def* setoid.gi
- \+ *lemma* setoid.inf_def
- \+ *theorem* setoid.inf_iff_and
- \+ *theorem* setoid.injective_iff_ker_bot
- \+ *lemma* setoid.injective_ker_lift
- \+ *def* setoid.is_partition
- \+ *def* setoid.ker
- \+ *lemma* setoid.ker_apply_eq_preimage
- \+ *lemma* setoid.ker_eq_lift_of_injective
- \+ *lemma* setoid.ker_mk_eq
- \+ *lemma* setoid.le_Inf
- \+ *theorem* setoid.le_def
- \+ *theorem* setoid.lift_unique
- \+ *def* setoid.map
- \+ *def* setoid.map_of_surjective
- \+ *lemma* setoid.map_of_surjective_eq_map
- \+ *lemma* setoid.mem_classes
- \+ *def* setoid.mk_classes
- \+ *theorem* setoid.mk_classes_classes
- \+ *lemma* setoid.ne_empty_of_mem_partition
- \+ *def* setoid.partition.order_iso
- \+ *lemma* setoid.refl'
- \+ *def* setoid.rel
- \+ *def* setoid.setoid_of_disjoint_union
- \+ *lemma* setoid.sup_def
- \+ *lemma* setoid.sup_eq_eqv_gen
- \+ *lemma* setoid.symm'
- \+ *lemma* setoid.trans'

Modified src/order/galois_connection.lean
- \+ *theorem* order_iso.to_galois_connection



## [2019-09-26 07:39:54](https://github.com/leanprover-community/mathlib/commit/7afdab6)
refactor(data/equiv/algebra): rewrite `ring_equiv` using bundled homs ([#1482](https://github.com/leanprover-community/mathlib/pull/1482))
* refactor(data/equiv/algebra): rewrite `ring_equiv` using bundled homs
Fix some compile errors
* Fix compile, add missing docs
* Docstrings
* Use less `ring_equiv.to_equiv` outside of `data/equiv/algebra`
* Join lines
#### Estimated changes
Modified src/algebra/ring.lean


Modified src/data/equiv/algebra.lean
- \+ *lemma* add_equiv.map_sub
- \+ *lemma* mul_equiv.map_eq_one_iff
- \+ *lemma* mul_equiv.map_inv
- \+ *lemma* mul_equiv.map_ne_one_iff
- \+ *lemma* ring_equiv.apply_symm_apply
- \+ *lemma* ring_equiv.coe_add_equiv
- \+ *lemma* ring_equiv.coe_mul_equiv
- \+ *lemma* ring_equiv.image_eq_preimage
- \+ *lemma* ring_equiv.map_add
- \+ *lemma* ring_equiv.map_mul
- \+ *lemma* ring_equiv.map_neg
- \+ *lemma* ring_equiv.map_neg_one
- \+ *lemma* ring_equiv.map_one
- \+ *lemma* ring_equiv.map_sub
- \+ *lemma* ring_equiv.map_zero
- \+ *def* ring_equiv.of'
- \+ *def* ring_equiv.of
- \+ *lemma* ring_equiv.symm_apply_apply
- \- *def* ring_equiv.to_add_equiv
- \- *lemma* ring_equiv.to_equiv_symm
- \- *lemma* ring_equiv.to_equiv_symm_apply
- \- *def* ring_equiv.to_mul_equiv
- \+ *def* ring_equiv.to_ring_hom

Modified src/data/mv_polynomial.lean
- \+/\- *def* mv_polynomial.option_equiv_left
- \+/\- *def* mv_polynomial.option_equiv_right
- \+/\- *def* mv_polynomial.pempty_ring_equiv
- \+/\- *def* mv_polynomial.punit_ring_equiv
- \+/\- *def* mv_polynomial.ring_equiv_congr
- \+/\- *def* mv_polynomial.ring_equiv_of_equiv
- \+/\- *def* mv_polynomial.sum_ring_equiv

Modified src/ring_theory/free_comm_ring.lean
- \+/\- *def* free_comm_ring_pempty_equiv_int
- \+/\- *def* free_comm_ring_punit_equiv_polynomial_int
- \+/\- *def* free_ring_pempty_equiv_int
- \+/\- *def* free_ring_punit_equiv_polynomial_int

Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/localization.lean
- \+/\- *def* localization.equiv_of_equiv
- \+/\- *def* localization.fraction_ring.equiv_of_equiv

Modified src/ring_theory/maps.lean
- \+/\- *def* comm_ring.anti_equiv_to_equiv
- \+/\- *def* comm_ring.equiv_to_anti_equiv
- \- *lemma* ring_equiv.map_add
- \- *lemma* ring_equiv.map_mul
- \- *lemma* ring_equiv.map_neg
- \- *lemma* ring_equiv.map_neg_one
- \- *lemma* ring_equiv.map_one
- \- *lemma* ring_equiv.map_sub
- \- *lemma* ring_equiv.map_zero

Modified src/ring_theory/noetherian.lean




## [2019-09-26 00:29:27](https://github.com/leanprover-community/mathlib/commit/2e35a7a)
feat(int/basic): add simp-lemma int.of_nat_eq_coe ([#1486](https://github.com/leanprover-community/mathlib/pull/1486))
* feat(int/basic): add simp-lemma int.of_nat_eq_coe
* fix errors
in the process also add some lemmas about bxor to simplify proofs
* use coercion in rat.mk
#### Estimated changes
Modified src/data/bool.lean
- \+ *theorem* bool.bxor_bnot_bnot
- \+ *theorem* bool.bxor_bnot_left
- \+ *theorem* bool.bxor_bnot_right

Modified src/data/int/basic.lean


Modified src/data/rat/basic.lean




## [2019-09-25 18:11:13](https://github.com/leanprover-community/mathlib/commit/b39040f)
feat(sanity_check): improvements  ([#1487](https://github.com/leanprover-community/mathlib/pull/1487))
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
#### Estimated changes
Modified docs/tactics.md


Modified src/meta/expr.lean


Modified src/tactic/sanity_check.lean


Modified test/sanity_check.lean
- \+ *def* bar.foo
- \+ *lemma* foo.foo
- \- *lemma* foo4



## [2019-09-25 04:39:17](https://github.com/leanprover-community/mathlib/commit/3e5dc88)
chore(scripts): add executable bit to scripts/mk_all.sh, and create/delete sanity_check_mathlib.lean ([#1480](https://github.com/leanprover-community/mathlib/pull/1480))
* chore(scripts): add executable bit to scripts/mk_all.sh
* another
* modify mk_all/rm_all to create a file containing #sanity_check_mathlib
* add sanity_check_mathlib.lean to .gitignore
* Update scripts/mk_all.sh
* Update scripts/mk_all.sh
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified .gitignore


Modified scripts/mk_all.sh


Modified scripts/rm_all.sh




## [2019-09-25 01:30:42](https://github.com/leanprover-community/mathlib/commit/491a68e)
cleanup(*): use priority 10 for low priority ([#1485](https://github.com/leanprover-community/mathlib/pull/1485))
Now we can locally use priorities lower than this low-priority
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/category/bifunctor.lean


Modified src/category/bitraversable/instances.lean


Modified src/category_theory/adjunction/basic.lean
- \+/\- *lemma* category_theory.adjunction.hom_equiv_naturality_left_symm
- \+/\- *lemma* category_theory.adjunction.hom_equiv_naturality_right

Modified src/computability/primrec.lean


Modified src/data/fintype.lean
- \+/\- *lemma* fintype.linear_order.is_well_order
- \+/\- *def* unique.fintype

Modified src/data/int/basic.lean


Modified src/data/nat/cast.lean


Modified src/data/num/basic.lean


Modified src/data/rat/cast.lean


Modified src/field_theory/splitting_field.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/finsupp.lean


Modified src/logic/basic.lean


Modified src/logic/function.lean


Modified src/tactic/finish.lean


Modified src/tactic/localized.lean


Modified src/tactic/push_neg.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/uniform_space/abstract_completion.lean




## [2019-09-24 15:16:11](https://github.com/leanprover-community/mathlib/commit/00d440a)
feat(tactic/import_private): make private definitions available outside of their scope ([#1450](https://github.com/leanprover-community/mathlib/pull/1450))
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
#### Estimated changes
Modified docs/tactics.md


Modified src/meta/expr.lean


Modified src/tactic/core.lean


Modified test/examples.lean




## [2019-09-24 13:36:31](https://github.com/leanprover-community/mathlib/commit/1eaa292)
feat(finset): add has_sep instance ([#1477](https://github.com/leanprover-community/mathlib/pull/1477))
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* finset.filter_congr_decidable
- \+ *lemma* finset.sep_def

Modified test/examples.lean




## [2019-09-24 08:39:19](https://github.com/leanprover-community/mathlib/commit/5344da4)
feat(algebra/big_operators): simp lemmas ([#1471](https://github.com/leanprover-community/mathlib/pull/1471))
* feat(algebra/big_operators): simp lemmas
* remove @[simp]
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_ite
- \+ *lemma* finset.sum_boole_mul
- \+ *lemma* finset.sum_mul_boole

Modified src/data/finset.lean
- \+ *lemma* finset.filter_eq



## [2019-09-24 08:13:37](https://github.com/leanprover-community/mathlib/commit/201174d)
feat(algebra/continued_fractions): add basic defs/lemmas for continued fractions ([#1433](https://github.com/leanprover-community/mathlib/pull/1433))
* feat(algebra/continued_fractions): add basic defs/lemmas for continued fractions
* Rename termiantes_at to terminated_at, use long names for cont. fracts.
* Fix indentation, remove subfolders, fix docstrings
#### Estimated changes
Modified docs/references.bib


Added src/algebra/continued_fractions/basic.lean
- \+ *lemma* continued_fraction.coe_to_generalized_continued_fraction
- \+ *lemma* continued_fraction.coe_to_simple_continued_fraction
- \+ *def* continued_fraction
- \+ *lemma* generalized_continued_fraction.coe_to_generalized_continued_fraction
- \+ *def* generalized_continued_fraction.continuants
- \+ *def* generalized_continued_fraction.continuants_aux
- \+ *def* generalized_continued_fraction.convergents'
- \+ *def* generalized_continued_fraction.convergents'_aux
- \+ *def* generalized_continued_fraction.convergents
- \+ *def* generalized_continued_fraction.denominators
- \+ *def* generalized_continued_fraction.is_simple_continued_fraction
- \+ *def* generalized_continued_fraction.next_continuants
- \+ *def* generalized_continued_fraction.next_denominator
- \+ *def* generalized_continued_fraction.next_numerator
- \+ *def* generalized_continued_fraction.numerators
- \+ *lemma* generalized_continued_fraction.pair.coe_to_generalized_continued_fraction_pair
- \+ *def* generalized_continued_fraction.partial_denominators
- \+ *def* generalized_continued_fraction.partial_numerators
- \+ *def* generalized_continued_fraction.seq.coe_to_seq
- \+ *def* generalized_continued_fraction.terminated_at
- \+ *def* generalized_continued_fraction.terminates
- \+ *lemma* simple_continued_fraction.coe_to_generalized_continued_fraction
- \+ *def* simple_continued_fraction.is_regular_continued_fraction
- \+ *def* simple_continued_fraction

Added src/algebra/continued_fractions/continuants_recurrence.lean
- \+ *lemma* generalized_continued_fraction.continuants_aux_recurrence
- \+ *theorem* generalized_continued_fraction.continuants_recurrence
- \+ *lemma* generalized_continued_fraction.continuants_recurrence_aux
- \+ *lemma* generalized_continued_fraction.denominators_recurrence
- \+ *lemma* generalized_continued_fraction.numerators_recurrence

Added src/algebra/continued_fractions/default.lean


Added src/algebra/continued_fractions/translations.lean
- \+ *lemma* generalized_continued_fraction.convergent_eq_conts_a_div_conts_b
- \+ *lemma* generalized_continued_fraction.convergent_eq_num_div_denom
- \+ *lemma* generalized_continued_fraction.denom_eq_conts_b
- \+ *lemma* generalized_continued_fraction.first_continuant_aux_eq_h_one
- \+ *lemma* generalized_continued_fraction.nth_cont_eq_succ_nth_cont_aux
- \+ *lemma* generalized_continued_fraction.num_eq_conts_a
- \+ *lemma* generalized_continued_fraction.obtain_conts_a_of_num
- \+ *lemma* generalized_continued_fraction.obtain_conts_b_of_denom
- \+ *lemma* generalized_continued_fraction.obtain_s_a_of_part_num
- \+ *lemma* generalized_continued_fraction.obtain_s_b_of_part_denom
- \+ *lemma* generalized_continued_fraction.part_denom_eq_s_b
- \+ *lemma* generalized_continued_fraction.part_denom_none_iff_s_none
- \+ *lemma* generalized_continued_fraction.part_num_eq_s_a
- \+ *lemma* generalized_continued_fraction.part_num_none_iff_s_none
- \+ *lemma* generalized_continued_fraction.terminated_at_iff_part_denom_none
- \+ *lemma* generalized_continued_fraction.terminated_at_iff_part_num_none
- \+ *lemma* generalized_continued_fraction.terminated_at_iff_s_none
- \+ *lemma* generalized_continued_fraction.terminated_at_iff_s_terminated_at
- \+ *lemma* generalized_continued_fraction.zeroth_continuant_aux_eq_one_zero
- \+ *lemma* generalized_continued_fraction.zeroth_continuant_eq_h_one
- \+ *lemma* generalized_continued_fraction.zeroth_convergent'_aux_eq_zero
- \+ *lemma* generalized_continued_fraction.zeroth_convergent'_eq_h
- \+ *lemma* generalized_continued_fraction.zeroth_convergent_eq_h

Modified src/data/seq/seq.lean
- \+ *def* seq.terminated_at
- \+ *lemma* seq.terminated_stable
- \+ *def* seq.terminates



## [2019-09-24 05:46:35](https://github.com/leanprover-community/mathlib/commit/327098b)
feat(tactic/library_search): a more powerful library_search ([#1470](https://github.com/leanprover-community/mathlib/pull/1470))
* experimental extensions to library_search
* upgrades to library_search
* remove ! for a later PR
* move `run_norm_num`
* oops
* Update src/tactic/library_search.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
* remove run_norm_num for later
#### Estimated changes
Modified src/tactic/library_search.lean


Modified src/tactic/solve_by_elim.lean


Modified test/library_search/basic.lean
- \- *def* test.library_search.P
- \- *def* test.library_search.Q
- \- *def* test.library_search.f
- \+ *def* test.library_search.lt_one
- \+ *lemma* test.library_search.zero_lt_one

Modified test/solve_by_elim.lean




## [2019-09-24 03:51:35](https://github.com/leanprover-community/mathlib/commit/88f37b5)
fix(tactic.lift): fix error messages ([#1478](https://github.com/leanprover-community/mathlib/pull/1478))
#### Estimated changes
Modified src/tactic/lift.lean


Modified test/tactics.lean




## [2019-09-24 00:00:49](https://github.com/leanprover-community/mathlib/commit/425644f)
refactor(algebra/*): Make `monoid_hom.ext` etc use `∀ x, f x = g x` as an assumption ([#1476](https://github.com/leanprover-community/mathlib/pull/1476))
#### Estimated changes
Modified src/algebra/category/CommRing/adjunctions.lean


Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/CommRing/limits.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.coe_inj
- \+/\- *lemma* monoid_hom.ext
- \+ *lemma* monoid_hom.ext_iff

Modified src/algebra/ring.lean
- \+ *theorem* ring_hom.coe_inj
- \+/\- *theorem* ring_hom.ext
- \+ *theorem* ring_hom.ext_iff

Modified src/data/mv_polynomial.lean




## [2019-09-23 22:04:22](https://github.com/leanprover-community/mathlib/commit/604699b)
feat(data|set_theory): various new lemmas ([#1466](https://github.com/leanprover-community/mathlib/pull/1466))
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
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* lt_one_add

Modified src/data/equiv/basic.lean


Modified src/data/equiv/list.lean
- \+ *def* equiv.list_unit_equiv

Modified src/data/fin.lean
- \+ *lemma* fin.coe_one
- \+ *lemma* fin.coe_two
- \+ *lemma* fin.coe_zero
- \+/\- *lemma* fin.injective_cast_le
- \+ *lemma* fin.injective_val
- \+ *lemma* fin.val_one
- \+ *lemma* fin.val_two

Modified src/data/list/basic.lean
- \- *theorem* list.app_subset_of_subset_of_subset
- \+/\- *theorem* list.append_sublist_append
- \+ *theorem* list.append_subset_iff
- \+ *theorem* list.append_subset_of_subset_of_subset
- \+/\- *theorem* list.bind_append
- \+/\- *theorem* list.bind_ret_eq_map
- \+/\- *theorem* list.chain'.iff_mem
- \+ *lemma* list.doubleton_eq
- \+ *lemma* list.empty_eq
- \+ *lemma* list.exists_le_of_sum_le
- \+ *lemma* list.exists_lt_of_sum_lt
- \+/\- *theorem* list.ilast'_mem
- \+ *lemma* list.injective_length
- \+ *lemma* list.injective_length_iff
- \+ *theorem* list.injective_map_iff
- \+ *lemma* list.insert_neg
- \+ *lemma* list.insert_pos
- \+ *lemma* list.join_join
- \+/\- *lemma* list.length_attach
- \+/\- *theorem* list.length_insert_of_mem
- \+/\- *theorem* list.length_insert_of_not_mem
- \+/\- *theorem* list.map_eq_map
- \+ *lemma* list.map_eq_map_iff
- \+ *theorem* list.map_subset_iff
- \- *theorem* list.nodup_app_comm
- \+ *theorem* list.nodup_append_comm
- \+/\- *theorem* list.nodup_append_of_nodup
- \+/\- *lemma* list.nth_le_attach
- \+ *theorem* list.nth_le_map_rev
- \- *theorem* list.pairwise_app_comm
- \+ *theorem* list.pairwise_append_comm
- \+/\- *lemma* list.rel_filter_map
- \+ *lemma* list.singleton_eq
- \- *theorem* list.sublist_app_of_sublist_left
- \- *theorem* list.sublist_app_of_sublist_right
- \+ *theorem* list.sublist_append_of_sublist_left
- \+ *theorem* list.sublist_append_of_sublist_right
- \- *theorem* list.subset_app_of_subset_left
- \- *theorem* list.subset_app_of_subset_right
- \+ *theorem* list.subset_append_of_subset_left
- \+ *theorem* list.subset_append_of_subset_right

Modified src/data/nat/basic.lean
- \+ *lemma* nat.pred_eq_succ_iff

Modified src/data/set/basic.lean
- \+ *lemma* set.set_of_app_iff

Modified src/data/subtype.lean
- \+ *theorem* subtype.forall'

Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.add_lt_omega_iff
- \+ *lemma* cardinal.lift_eq_nat_iff
- \+ *theorem* cardinal.mk_image_le_lift
- \+ *lemma* cardinal.mk_range_eq_lift
- \+ *lemma* cardinal.mk_sum_compl
- \+ *lemma* cardinal.mul_lt_omega_iff
- \+ *lemma* cardinal.mul_lt_omega_iff_of_ne_zero
- \+ *lemma* cardinal.nat_eq_lift_eq_iff
- \+ *theorem* cardinal.power_le_max_power_one

Modified src/set_theory/ordinal.lean
- \+ *lemma* cardinal.add_eq_left
- \+ *lemma* cardinal.add_eq_left_iff
- \+ *lemma* cardinal.add_eq_right
- \+ *lemma* cardinal.add_eq_right_iff
- \+ *def* cardinal.aleph'_equiv
- \- *theorem* cardinal.aleph_is_limit
- \+ *lemma* cardinal.eq_of_add_eq_of_omega_le
- \+ *theorem* cardinal.extend_function
- \+ *theorem* cardinal.extend_function_finite
- \+ *theorem* cardinal.extend_function_of_lt
- \+ *lemma* cardinal.le_mul_left
- \+ *lemma* cardinal.le_mul_right
- \+ *lemma* cardinal.mk_compl_eq_mk_compl_finite
- \+ *lemma* cardinal.mk_compl_eq_mk_compl_finite_lift
- \+ *lemma* cardinal.mk_compl_eq_mk_compl_finite_same
- \+ *lemma* cardinal.mk_compl_eq_mk_compl_infinite
- \+ *lemma* cardinal.mk_compl_finset_of_omega_le
- \+ *lemma* cardinal.mk_compl_of_omega_le
- \+ *lemma* cardinal.mul_eq_left
- \+ *lemma* cardinal.mul_eq_left_iff
- \+ *lemma* cardinal.mul_eq_right
- \+ *theorem* cardinal.ord_aleph_is_limit
- \+/\- *theorem* cardinal.pow_le
- \+ *theorem* ordinal.bsup_id
- \+ *theorem* ordinal.is_limit_add_iff
- \+ *theorem* ordinal.is_normal.bsup_eq
- \+ *theorem* ordinal.lt_bsup
- \+ *theorem* ordinal.nfp_eq_self
- \+/\- *def* principal_seg.equiv_lt
- \+/\- *def* principal_seg.lt_le
- \+/\- *theorem* principal_seg.lt_le_top
- \+/\- *def* principal_seg.of_element



## [2019-09-23 19:57:18](https://github.com/leanprover-community/mathlib/commit/fd7840a)
feat(topology/constructions): is_open_prod_iff' ([#1454](https://github.com/leanprover-community/mathlib/pull/1454))
* feat(topology/constructions): open_prod_iff'
* reviewer's comments
* fix build
* golfed; is_open_map_fst
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.prod_subset_prod_iff

Modified src/topology/constructions.lean
- \+ *lemma* is_open_map_fst
- \+ *lemma* is_open_map_snd
- \+ *lemma* is_open_prod_iff'



## [2019-09-23 17:36:28](https://github.com/leanprover-community/mathlib/commit/87d1240)
feat(tactic/core): derive handler for simple instances ([#1475](https://github.com/leanprover-community/mathlib/pull/1475))
* feat(tactic/core): derive handler for simple algebraic instances
* change comment
* use mk_definition
* Update src/tactic/core.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/tactic/core.lean


Added test/delta_instance.lean
- \+ *def* T
- \+ *def* V



## [2019-09-22 04:34:09](https://github.com/leanprover-community/mathlib/commit/61ccaf6)
chore(*): fix various issues reported by `sanity_check_mathlib` ([#1469](https://github.com/leanprover-community/mathlib/pull/1469))
* chore(*): fix various issues reported by `sanity_check_mathlib`
* Drop a misleading comment, fix the proof
#### Estimated changes
Modified src/algebra/direct_limit.lean
- \+ *lemma* add_comm_group.direct_limit.directed_system
- \- *def* add_comm_group.direct_limit.directed_system

Modified src/algebra/field.lean
- \+ *lemma* units.mk0_inj
- \- *lemma* units.units.mk0_inj

Modified src/algebra/group/basic.lean
- \+ *lemma* sub_sub_cancel
- \- *def* sub_sub_cancel

Modified src/algebra/group/with_one.lean


Modified src/algebra/ordered_field.lean
- \+ *lemma* div_nonneg
- \- *def* div_nonneg
- \+ *lemma* div_pos
- \- *def* div_pos
- \+ *lemma* half_lt_self
- \- *def* half_lt_self

Modified src/algebra/ordered_ring.lean
- \- *def* nonneg_ring.nonneg_ring.to_linear_nonneg_ring
- \+ *def* nonneg_ring.to_linear_nonneg_ring

Modified src/algebra/pointwise.lean
- \+ *lemma* set.pointwise_mul_image_is_semiring_hom
- \- *def* set.pointwise_mul_image_is_semiring_hom
- \+ *lemma* set.singleton.is_monoid_hom
- \- *def* set.singleton.is_monoid_hom
- \+ *lemma* set.singleton.is_mul_hom
- \- *def* set.singleton.is_mul_hom

Modified src/category/monad/cont.lean
- \- *def* cont_t.cont_t.monad_lift
- \+ *def* cont_t.monad_lift

Modified src/category/traversable/equiv.lean


Modified src/category_theory/natural_isomorphism.lean
- \+ *lemma* category_theory.nat_iso.of_components.app
- \- *def* category_theory.nat_iso.of_components.app
- \+ *lemma* category_theory.nat_iso.of_components.hom_app
- \- *def* category_theory.nat_iso.of_components.hom_app
- \+ *lemma* category_theory.nat_iso.of_components.inv_app
- \- *def* category_theory.nat_iso.of_components.inv_app

Modified src/data/equiv/algebra.lean
- \+ *lemma* mul_equiv.apply_symm_apply
- \- *def* mul_equiv.apply_symm_apply
- \+ *lemma* mul_equiv.map_mul
- \- *def* mul_equiv.map_mul
- \+ *lemma* mul_equiv.map_one
- \- *def* mul_equiv.map_one
- \+ *lemma* mul_equiv.symm_apply_apply
- \- *def* mul_equiv.symm_apply_apply

Modified src/data/equiv/basic.lean
- \+ *def* equiv.subtype_quotient_equiv_quotient_subtype
- \- *lemma* equiv.subtype_quotient_equiv_quotient_subtype

Modified src/data/finset.lean
- \+ *def* finset.strong_induction_on
- \- *lemma* finset.strong_induction_on

Modified src/data/finsupp.lean
- \+ *lemma* finsupp.lt_wf
- \- *def* finsupp.lt_wf

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.is_add_monoid_hom_mul_right
- \- *def* matrix.is_add_monoid_hom_mul_right

Modified src/data/multiset.lean
- \+ *theorem* multiset.map_eq_zero
- \- *theorem* multiset.multiset.map_eq_zero

Modified src/data/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.degrees_neg
- \+/\- *lemma* mv_polynomial.degrees_sub

Modified src/data/polynomial.lean
- \+ *def* polynomial.coeff_coe_to_fun
- \+ *lemma* polynomial.degree_lt_wf
- \- *def* polynomial.degree_lt_wf
- \- *def* polynomial.polynomial.has_coe_to_fun

Modified src/data/rat/basic.lean
- \+ *def* rat.{u}
- \- *theorem* rat.{u}

Modified src/data/rat/order.lean


Modified src/group_theory/free_group.lean
- \+ *lemma* free_group.to_word.inj
- \- *def* free_group.to_word.inj
- \+ *lemma* free_group.to_word.mk
- \- *def* free_group.to_word.mk

Modified src/group_theory/sylow.lean
- \+ *def* sylow.fixed_points_mul_left_cosets_equiv_quotient
- \- *lemma* sylow.fixed_points_mul_left_cosets_equiv_quotient

Modified src/linear_algebra/finsupp_vector_space.lean
- \+ *def* fin_dim_vectorspace_equiv
- \- *lemma* fin_dim_vectorspace_equiv

Modified src/logic/basic.lean
- \+/\- *theorem* imp_intro
- \+ *def* not.elim
- \- *theorem* not.elim
- \+/\- *theorem* not_of_not_imp

Modified src/measure_theory/ae_eq_fun.lean
- \+ *lemma* measure_theory.ae_eq_fun.lift_rel_mk_mk
- \- *def* measure_theory.ae_eq_fun.lift_rel_mk_mk

Modified src/number_theory/dioph.lean
- \+ *lemma* poly.ext
- \- *def* poly.ext
- \+ *lemma* poly.induction
- \- *def* poly.induction
- \+ *lemma* poly.isp
- \- *def* poly.isp

Modified src/order/filter/basic.lean


Modified src/order/filter/pointwise.lean
- \+ *lemma* filter.pointwise_add_map_is_add_monoid_hom
- \- *def* filter.pointwise_add_map_is_add_monoid_hom
- \+ *lemma* filter.pointwise_mul_map_is_monoid_hom
- \- *def* filter.pointwise_mul_map_is_monoid_hom

Modified src/ring_theory/algebra.lean


Modified src/ring_theory/ideals.lean
- \+/\- *theorem* ideal.is_coprime_def
- \+/\- *theorem* ideal.is_coprime_self
- \+/\- *theorem* ideal.mem_span_pair
- \+ *theorem* ideal.zero_ne_one_of_proper
- \- *def* ideal.zero_ne_one_of_proper

Modified src/ring_theory/power_series.lean
- \+ *lemma* mv_power_series.is_local_ring
- \- *def* mv_power_series.is_local_ring

Modified src/set_theory/ordinal.lean
- \+ *def* embedding_to_cardinal
- \+ *theorem* nonempty_embedding_to_cardinal
- \+/\- *def* ordinal.div_def

Modified src/set_theory/pgame.lean
- \+ *lemma* pgame.add_zero_equiv
- \- *def* pgame.add_zero_equiv
- \+ *lemma* pgame.subsequent.left_move
- \- *def* pgame.subsequent.left_move
- \+ *lemma* pgame.subsequent.right_move
- \- *def* pgame.subsequent.right_move
- \+ *lemma* pgame.zero_add_equiv
- \- *def* pgame.zero_add_equiv

Modified src/set_theory/surreal.lean
- \+ *lemma* pgame.numeric.move_left
- \- *def* pgame.numeric.move_left
- \+ *lemma* pgame.numeric.move_right
- \- *def* pgame.numeric.move_right

Modified src/set_theory/zfc.lean


Modified src/tactic/doc_blame.lean


Modified src/tactic/monotonicity/interactive.lean
- \+ *def* tactic.interactive.apply_rel
- \- *lemma* tactic.interactive.apply_rel

Modified src/tactic/omega/clause.lean
- \+ *lemma* omega.clause.holds_append
- \- *def* omega.clause.holds_append

Modified src/tactic/omega/coeffs.lean
- \+ *lemma* omega.coeffs.val_between_set
- \- *def* omega.coeffs.val_between_set
- \+ *lemma* omega.coeffs.val_except_add_eq
- \- *def* omega.coeffs.val_except_add_eq
- \+ *lemma* omega.coeffs.val_set
- \- *def* omega.coeffs.val_set

Modified src/tactic/omega/nat/form.lean
- \+ *lemma* omega.nat.form.holds_constant
- \- *def* omega.nat.form.holds_constant

Modified src/tactic/omega/nat/preterm.lean
- \+ *lemma* omega.nat.preterm.val_constant
- \- *def* omega.nat.preterm.val_constant

Modified src/tactic/ring.lean
- \+/\- *theorem* tactic.ring.pow_add_rev



## [2019-09-21 06:12:35](https://github.com/leanprover-community/mathlib/commit/65bf45c)
fix(category_theory/finite_limits): fix definition, and construct from finite products and equalizers ([#1427](https://github.com/leanprover-community/mathlib/pull/1427))
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
#### Estimated changes
Modified src/category_theory/discrete_category.lean


Deleted src/category_theory/limits/shapes/constructions/finite_limits.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean
- \- *def* category_theory.limits.equalizer_diagram.cones_hom
- \- *def* category_theory.limits.equalizer_diagram.cones_inv
- \- *def* category_theory.limits.equalizer_diagram.cones_iso
- \- *def* category_theory.limits.equalizer_diagram
- \+ *def* category_theory.limits.finite_limits_from_equalizers_and_finite_products
- \+ *def* category_theory.limits.has_limit_of_has_products_of_has_equalizers.cones_hom
- \+ *def* category_theory.limits.has_limit_of_has_products_of_has_equalizers.cones_inv
- \+ *def* category_theory.limits.has_limit_of_has_products_of_has_equalizers.cones_iso
- \+ *def* category_theory.limits.has_limit_of_has_products_of_has_equalizers.diagram

Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/category_theory/limits/shapes/finite_products.lean




## [2019-09-21 00:47:17](https://github.com/leanprover-community/mathlib/commit/9c89fa5)
feat(tactic/interactive): add fconstructor ([#1467](https://github.com/leanprover-community/mathlib/pull/1467))
#### Estimated changes
Modified src/tactic/interactive.lean




## [2019-09-20 11:08:05](https://github.com/leanprover-community/mathlib/commit/708a28c)
chore(algebra/group/units): use `def to_units` instead of `has_lift` ([#1431](https://github.com/leanprover-community/mathlib/pull/1431))
* chore(algebra/group/units): use `def to_units` instead of `has_lift`
* Move, upgrade to `mul_equiv`, add documentation
#### Estimated changes
Modified src/algebra/group/units.lean


Modified src/data/equiv/algebra.lean
- \+ *def* to_units



## [2019-09-20 03:28:58](https://github.com/leanprover-community/mathlib/commit/bfe9c6c)
chore(data/pfun): run `#sanity_check` ([#1463](https://github.com/leanprover-community/mathlib/pull/1463))
#### Estimated changes
Modified src/data/pfun.lean
- \+ *theorem* pfun.ext'
- \- *def* pfun.ext'
- \+ *theorem* pfun.ext
- \- *def* pfun.ext
- \+ *def* pfun.fix_induction
- \- *theorem* pfun.fix_induction
- \+ *lemma* pfun.mem_preimage
- \- *def* pfun.mem_preimage
- \+ *theorem* roption.ext'
- \- *def* roption.ext'
- \+ *theorem* roption.ext
- \- *def* roption.ext



## [2019-09-19 15:32:04](https://github.com/leanprover-community/mathlib/commit/ce105fd)
chore(algebra/group): rename `as_monoid_hom` into `monoid_hom.of`, define `ring_hom.of` ([#1443](https://github.com/leanprover-community/mathlib/pull/1443))
* chore(algebra/group): rename `as_monoid_hom` into `monoid_hom.of`
This is similar to `Mon.of` etc.
* Fix compile
* Docs, missing universe
* Move variables declaration up as suggested by @jcommelin
* doc-string
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/algebra/group/hom.lean
- \- *def* as_monoid_hom
- \- *lemma* coe_as_monoid_hom
- \+ *lemma* monoid_hom.coe_of
- \+ *def* monoid_hom.of

Modified src/algebra/group/units_hom.lean


Modified src/algebra/ring.lean
- \+/\- *lemma* ring_hom.coe_of
- \+/\- *def* ring_hom.of



## [2019-09-19 13:17:33](https://github.com/leanprover-community/mathlib/commit/d910283)
chore(category_theory/endomorphism): make `map_End` and `map_Aut` use bundled homs ([#1461](https://github.com/leanprover-community/mathlib/pull/1461))
* Migrate `functor.map_End` and `functor.map_Aut` to bundled homs
Adjust implicit arguments of `iso.ext`
* Add docstrings
#### Estimated changes
Modified src/category_theory/endomorphism.lean
- \+/\- *def* category_theory.functor.map_Aut
- \+/\- *def* category_theory.functor.map_End

Modified src/category_theory/isomorphism.lean
- \+ *lemma* category_theory.functor.map_iso_refl
- \+/\- *lemma* category_theory.iso.ext
- \+/\- *lemma* category_theory.iso.self_symm_id
- \+/\- *lemma* category_theory.iso.symm_self_id



## [2019-09-19 13:21:35+02:00](https://github.com/leanprover-community/mathlib/commit/1b8285e)
chore(readme): Add new maintainers [ci skip]
#### Estimated changes
Modified README.md




## [2019-09-19 02:38:18](https://github.com/leanprover-community/mathlib/commit/b11f0f1)
refactor(category_theory): refactor concrete categories ([#1380](https://github.com/leanprover-community/mathlib/pull/1380))
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
* update post [#1412](https://github.com/leanprover-community/mathlib/pull/1412)
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
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/category/CommRing/adjunctions.lean
- \+/\- *def* CommRing.adj
- \+ *lemma* CommRing.free_map_coe
- \- *lemma* CommRing.free_map_val
- \+ *lemma* CommRing.free_obj_coe
- \- *lemma* CommRing.free_obj_α
- \- *def* CommRing.hom_equiv

Modified src/algebra/category/CommRing/basic.lean
- \- *def* CommRing.Int.cast
- \- *def* CommRing.Int.hom_unique
- \+ *lemma* CommRing.comp_eq
- \+ *lemma* CommRing.forget_map_eq_coe
- \+ *lemma* CommRing.forget_obj_eq_coe
- \- *def* CommRing.forget_to_CommMon
- \+ *lemma* CommRing.id_eq
- \+/\- *def* CommRing.of
- \- *def* CommRing.to_Ring
- \+ *def* CommSemiRing.of
- \+ *def* CommSemiRing
- \+/\- *def* Ring.of
- \+ *def* SemiRing.of
- \+ *def* SemiRing

Modified src/algebra/category/CommRing/colimits.lean
- \+/\- *def* CommRing.colimits.colimit
- \- *lemma* CommRing.colimits.naturality_bundled

Modified src/algebra/category/CommRing/limits.lean
- \- *def* CommRing.limit
- \- *def* CommRing.limit_is_limit

Modified src/algebra/category/Group.lean
- \- *def* AddCommGroup.forget_to_Group
- \- *def* AddCommGroup.is_add_comm_group_hom
- \- *def* AddCommGroup.of
- \- *def* AddCommGroup
- \+ *def* CommGroup.of
- \+ *def* CommGroup
- \+/\- *def* Group.of
- \+/\- *def* Group

Modified src/algebra/category/Mon/basic.lean
- \- *def* CommMon.forget_to_Mon
- \- *def* CommMon.is_comm_monoid_hom
- \+/\- *def* CommMon.of
- \+/\- *def* CommMon
- \- *def* Mon.hom_equiv_monoid_hom
- \+/\- *def* Mon.of
- \+/\- *def* Mon

Modified src/algebra/category/Mon/colimits.lean


Modified src/algebra/punit_instances.lean


Modified src/algebra/ring.lean
- \+ *lemma* is_ring_hom.of_semiring
- \- *def* is_ring_hom.of_semiring
- \+ *lemma* ring_hom.coe_comp
- \+ *lemma* ring_hom.coe_of
- \+/\- *def* ring_hom.comp
- \+ *def* ring_hom.of

Modified src/algebraic_geometry/stalks.lean


Modified src/category_theory/category/Cat.lean
- \+/\- *def* category_theory.Cat.of

Modified src/category_theory/category/Groupoid.lean
- \+/\- *def* category_theory.Groupoid.of

Deleted src/category_theory/concrete_category.lean
- \- *lemma* category_theory.bundled.bundled_hom_coe
- \- *lemma* category_theory.bundled.coe_comp
- \- *lemma* category_theory.bundled.coe_id
- \- *lemma* category_theory.bundled.concrete_category_comp
- \- *lemma* category_theory.bundled.concrete_category_id
- \- *lemma* category_theory.bundled.hom_ext
- \- *def* category_theory.bundled.map
- \- *def* category_theory.concrete_functor
- \- *def* category_theory.forget
- \- *def* category_theory.mk_ob

Added src/category_theory/concrete_category/basic.lean
- \+ *def* category_theory.forget
- \+ *def* category_theory.forget₂
- \+ *def* category_theory.has_forget₂.mk'

Added src/category_theory/concrete_category/bundled.lean
- \+ *def* category_theory.bundled.map
- \+ *def* category_theory.bundled.of

Added src/category_theory/concrete_category/bundled_hom.lean
- \+ *lemma* category_theory.bundled_hom.coe_comp
- \+ *lemma* category_theory.bundled_hom.coe_id
- \+ *def* category_theory.bundled_hom.full_subcategory_has_forget₂
- \+ *def* category_theory.bundled_hom.has_coe_to_fun
- \+ *def* category_theory.bundled_hom.mk_has_forget₂

Added src/category_theory/concrete_category/default.lean


Added src/category_theory/concrete_category/unbundled_hom.lean
- \+ *def* category_theory.unbundled_hom.mk_has_forget₂

Modified src/category_theory/fully_faithful.lean
- \+ *lemma* category_theory.faithful.div_comp
- \+ *lemma* category_theory.faithful.div_faithful
- \+ *lemma* category_theory.faithful.of_comp
- \+ *lemma* category_theory.faithful.of_comp_eq
- \+ *lemma* category_theory.functor.injectivity
- \- *def* category_theory.functor.injectivity
- \+ *lemma* category_theory.preimage_iso_map_iso

Modified src/category_theory/functor.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/single_obj.lean


Modified src/data/mv_polynomial.lean
- \+ *def* mv_polynomial.hom_equiv

Modified src/logic/function.lean
- \+ *lemma* function.injective.of_comp
- \+ *lemma* function.surjective.of_comp

Modified src/measure_theory/category/Meas.lean
- \+/\- *def* Borel
- \+/\- *def* Meas.of

Modified src/topology/category/Top/adjunctions.lean
- \+/\- *def* Top.adj₁
- \+/\- *def* Top.adj₂

Modified src/topology/category/Top/basic.lean
- \+ *lemma* Top.id_app

Modified src/topology/category/Top/epi_mono.lean


Modified src/topology/category/Top/limits.lean


Modified src/topology/category/TopCommRing.lean
- \- *def* TopCommRing.forget
- \- *def* TopCommRing.forget_to_CommRing
- \- *def* TopCommRing.forget_to_Top
- \- *def* TopCommRing.forget_to_Type_via_CommRing
- \- *def* TopCommRing.forget_to_Type_via_Top

Modified src/topology/category/UniformSpace.lean
- \- *def* CpltSepUniformSpace.forget
- \- *def* CpltSepUniformSpace.forget_to_Type_via_UniformSpace
- \- *def* CpltSepUniformSpace.forget_to_UniformSpace
- \+ *lemma* UniformSpace.coe_comp
- \+ *lemma* UniformSpace.coe_id
- \+ *lemma* UniformSpace.coe_mk
- \+/\- *def* UniformSpace.completion_hom
- \- *def* UniformSpace.forget_to_Top
- \- *def* UniformSpace.forget_to_Type_via_Top
- \+ *lemma* UniformSpace.hom_ext

Modified src/topology/sheaves/presheaf_of_functions.lean
- \+/\- *def* Top.CommRing_yoneda
- \+ *lemma* Top.continuous_functions.zero

Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* uniform_continuous.comp



## [2019-09-18 17:59:44](https://github.com/leanprover-community/mathlib/commit/066d053)
chore(topology/maps): a few tweaks to open_embedding and closed embeddings ([#1459](https://github.com/leanprover-community/mathlib/pull/1459))
* chore(topology/maps): a few tweaks to open_embedding and closed
embeddings
aligning them with recent modification to embedding. From the perfectoid
project.
* chore(topology/maps): add missing empty line
#### Estimated changes
Modified src/topology/maps.lean
- \+/\- *lemma* closed_embedding.closed_iff_image_closed
- \+/\- *lemma* closed_embedding.closed_iff_preimage_closed
- \+ *lemma* closed_embedding.continuous
- \+/\- *lemma* closed_embedding.is_closed_map
- \- *def* closed_embedding
- \+/\- *lemma* closed_embedding_of_continuous_injective_closed
- \+/\- *lemma* closed_embedding_of_embedding_closed
- \+ *lemma* open_embedding.comp
- \+ *lemma* open_embedding.continuous
- \- *def* open_embedding
- \- *lemma* open_embedding_compose
- \+ *lemma* subtype_val.closed_embedding
- \+ *lemma* subtype_val.open_embedding



## [2019-09-18 15:46:57](https://github.com/leanprover-community/mathlib/commit/08390f5)
refactor(algebra/big_operators,data/finset): use `finset.disjoint` in definitions ([#1456](https://github.com/leanprover-community/mathlib/pull/1456))
* Use `finset.disjoint` in `algebra/big_operators`
* New lemma `disjoint_filter`
It should be a painless step from using `filter_inter_filter_neg_eq`
to using this lemma
* Update other dependencies of finset.prod_union and finset.prod_bind
* Reformat some lines to make them fit within 100 characters
* We can actually do away with two non-terminal `simp`s now
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* finset.prod_union

Modified src/data/finset.lean
- \+ *lemma* finset.disjoint_filter

Modified src/data/nat/totient.lean


Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/group_theory/order_of_element.lean


Modified src/topology/algebra/infinite_sum.lean




## [2019-09-18 15:43:01+02:00](https://github.com/leanprover-community/mathlib/commit/b51978d)
chore(data/mllist): Typo in author name [ci skip] ([#1458](https://github.com/leanprover-community/mathlib/pull/1458))
#### Estimated changes
Modified src/data/mllist.lean




## [2019-09-18 15:40:20+02:00](https://github.com/leanprover-community/mathlib/commit/874a15a)
Update lattice.lean ([#1457](https://github.com/leanprover-community/mathlib/pull/1457))
#### Estimated changes
Modified src/data/set/lattice.lean




## [2019-09-17 18:02:24](https://github.com/leanprover-community/mathlib/commit/b41277c)
feat(set_theory/game): the theory of combinatorial games ([#1274](https://github.com/leanprover-community/mathlib/pull/1274))
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
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/ordered_group.lean
- \+ *def* ordered_comm_group.mk'

Modified src/data/equiv/basic.lean
- \+ *theorem* equiv.refl_symm
- \+ *lemma* equiv.sum_congr_symm

Modified src/data/finset.lean
- \+ *theorem* finset.card_erase_le
- \+ *theorem* finset.card_erase_lt_of_mem
- \+ *theorem* finset.card_ne_zero_of_mem

Modified src/data/multiset.lean
- \+ *theorem* multiset.card_erase_le
- \+ *theorem* multiset.card_erase_lt_of_mem

Modified src/linear_algebra/dimension.lean


Modified src/logic/basic.lean
- \+ *theorem* exists_pempty
- \+ *theorem* forall_pempty
- \- *lemma* nonempty_pempty
- \+ *lemma* not_nonempty_pempty

Added src/set_theory/game.lean
- \+ *def* game.add
- \+ *theorem* game.add_assoc
- \+ *theorem* game.add_comm
- \+ *theorem* game.add_le_add_left
- \+ *theorem* game.add_left_neg
- \+ *theorem* game.add_zero
- \+ *def* game.game_partial_order
- \+ *def* game.le
- \+ *theorem* game.le_antisymm
- \+ *theorem* game.le_refl
- \+ *theorem* game.le_trans
- \+ *def* game.lt
- \+ *def* game.neg
- \+ *theorem* game.not_le
- \+ *def* game.ordered_comm_group_game
- \+ *theorem* game.zero_add
- \+ *def* game

Added src/set_theory/pgame.lean
- \+ *def* pgame.add
- \+ *theorem* pgame.add_assoc_equiv
- \+ *def* pgame.add_assoc_relabelling
- \+ *theorem* pgame.add_comm_equiv
- \+ *theorem* pgame.add_comm_le
- \+ *def* pgame.add_comm_relabelling
- \+ *theorem* pgame.add_congr
- \+ *theorem* pgame.add_le_add_left
- \+ *theorem* pgame.add_le_add_right
- \+ *theorem* pgame.add_left_neg_equiv
- \+ *theorem* pgame.add_left_neg_le_zero
- \+ *theorem* pgame.add_lt_add_left
- \+ *theorem* pgame.add_lt_add_right
- \+ *lemma* pgame.add_move_left_inl
- \+ *lemma* pgame.add_move_left_inr
- \+ *lemma* pgame.add_move_right_inl
- \+ *lemma* pgame.add_move_right_inr
- \+ *theorem* pgame.add_right_neg_le_zero
- \+ *def* pgame.add_zero_equiv
- \+ *def* pgame.add_zero_relabelling
- \+ *def* pgame.equiv
- \+ *theorem* pgame.equiv_of_relabelling
- \+ *theorem* pgame.equiv_refl
- \+ *theorem* pgame.equiv_symm
- \+ *theorem* pgame.equiv_trans
- \+ *theorem* pgame.le_congr
- \+ *theorem* pgame.le_def
- \+ *theorem* pgame.le_def_lt
- \+ *theorem* pgame.le_iff_neg_ge
- \+ *theorem* pgame.le_iff_sub_nonneg
- \+ *def* pgame.le_lt
- \+ *theorem* pgame.le_of_equiv_of_le
- \+ *theorem* pgame.le_of_le_of_equiv
- \+ *theorem* pgame.le_of_relabelling
- \+ *theorem* pgame.le_of_restricted
- \+ *theorem* pgame.le_refl
- \+ *theorem* pgame.le_trans
- \+ *theorem* pgame.le_trans_aux
- \+ *theorem* pgame.le_zero
- \+ *theorem* pgame.le_zero_iff_zero_le_neg
- \+ *def* pgame.left_moves
- \+ *def* pgame.left_moves_add
- \+ *lemma* pgame.left_moves_mk
- \+ *def* pgame.left_moves_neg
- \+ *lemma* pgame.left_response_spec
- \+ *theorem* pgame.lt_congr
- \+ *theorem* pgame.lt_def
- \+ *theorem* pgame.lt_def_le
- \+ *theorem* pgame.lt_iff_neg_gt
- \+ *theorem* pgame.lt_iff_sub_pos
- \+ *theorem* pgame.lt_irrefl
- \+ *theorem* pgame.lt_mk_of_le
- \+ *theorem* pgame.lt_of_equiv_of_lt
- \+ *theorem* pgame.lt_of_le_mk
- \+ *theorem* pgame.lt_of_le_of_lt
- \+ *theorem* pgame.lt_of_lt_of_equiv
- \+ *theorem* pgame.lt_of_lt_of_le
- \+ *theorem* pgame.lt_of_mk_le
- \+ *theorem* pgame.lt_zero
- \+ *lemma* pgame.mk_add_move_left_inl
- \+ *lemma* pgame.mk_add_move_left_inr
- \+ *lemma* pgame.mk_add_move_right_inl
- \+ *lemma* pgame.mk_add_move_right_inr
- \+ *theorem* pgame.mk_le_mk
- \+ *theorem* pgame.mk_lt_mk
- \+ *theorem* pgame.mk_lt_of_le
- \+ *def* pgame.move_left
- \+ *lemma* pgame.move_left_mk
- \+ *lemma* pgame.move_left_right_moves_neg
- \+ *lemma* pgame.move_left_right_moves_neg_symm
- \+ *def* pgame.move_right
- \+ *lemma* pgame.move_right_left_moves_neg
- \+ *lemma* pgame.move_right_mk
- \+ *lemma* pgame.move_right_right_moves_neg_symm
- \+ *theorem* pgame.ne_of_lt
- \+ *def* pgame.neg
- \+ *theorem* pgame.neg_add_le
- \+ *def* pgame.neg_add_relabelling
- \+ *theorem* pgame.neg_congr
- \+ *lemma* pgame.neg_def
- \+ *theorem* pgame.neg_neg
- \+ *theorem* pgame.neg_zero
- \+ *theorem* pgame.not_le
- \+ *theorem* pgame.not_le_lt
- \+ *theorem* pgame.not_lt
- \+ *def* pgame.of_lists
- \+ *def* pgame.omega
- \+ *lemma* pgame.one_left_moves
- \+ *lemma* pgame.one_move_left
- \+ *lemma* pgame.one_right_moves
- \+ *def* pgame.relabel
- \+ *lemma* pgame.relabel_move_left'
- \+ *lemma* pgame.relabel_move_left
- \+ *lemma* pgame.relabel_move_right'
- \+ *lemma* pgame.relabel_move_right
- \+ *def* pgame.relabel_relabelling
- \+ *def* pgame.relabelling.refl
- \+ *def* pgame.relabelling.symm
- \+ *def* pgame.restricted.refl
- \+ *def* pgame.restricted_of_relabelling
- \+ *def* pgame.right_moves
- \+ *def* pgame.right_moves_add
- \+ *lemma* pgame.right_moves_mk
- \+ *def* pgame.right_moves_neg
- \+ *lemma* pgame.right_response_spec
- \+ *def* pgame.star
- \+ *theorem* pgame.star_lt_zero
- \+ *def* pgame.subsequent.left_move
- \+ *def* pgame.subsequent.right_move
- \+ *theorem* pgame.wf_subsequent
- \+ *def* pgame.zero_add_equiv
- \+ *def* pgame.zero_add_relabelling
- \+ *theorem* pgame.zero_le
- \+ *theorem* pgame.zero_le_add_left_neg
- \+ *theorem* pgame.zero_le_add_right_neg
- \+ *theorem* pgame.zero_le_iff_neg_le_zero
- \+ *lemma* pgame.zero_left_moves
- \+ *theorem* pgame.zero_lt
- \+ *theorem* pgame.zero_lt_star
- \+ *lemma* pgame.zero_right_moves

Modified src/set_theory/surreal.lean
- \- *def* pSurreal.add
- \- *def* pSurreal.equiv
- \- *theorem* pSurreal.equiv_refl
- \- *theorem* pSurreal.equiv_symm
- \- *theorem* pSurreal.equiv_trans
- \- *def* pSurreal.inv'
- \- *def* pSurreal.inv_val
- \- *theorem* pSurreal.le_congr
- \- *def* pSurreal.le_lt
- \- *theorem* pSurreal.le_of_lt
- \- *theorem* pSurreal.le_refl
- \- *theorem* pSurreal.le_trans
- \- *theorem* pSurreal.le_trans_aux
- \- *theorem* pSurreal.lt_asymm
- \- *theorem* pSurreal.lt_congr
- \- *theorem* pSurreal.lt_iff_le_not_le
- \- *theorem* pSurreal.lt_irrefl
- \- *theorem* pSurreal.lt_mk_of_le
- \- *theorem* pSurreal.lt_of_le_mk
- \- *theorem* pSurreal.lt_of_mk_le
- \- *theorem* pSurreal.mk_le_mk
- \- *theorem* pSurreal.mk_lt_mk
- \- *theorem* pSurreal.mk_lt_of_le
- \- *def* pSurreal.mul
- \- *theorem* pSurreal.ne_of_lt
- \- *def* pSurreal.neg
- \- *theorem* pSurreal.not_le
- \- *theorem* pSurreal.not_le_lt
- \- *theorem* pSurreal.not_lt
- \- *def* pSurreal.ok
- \- *theorem* pSurreal.ok_rec
- \- *def* pSurreal.omega
- \+ *theorem* pgame.add_lt_add
- \+ *def* pgame.inv'
- \+ *def* pgame.inv_val
- \+ *theorem* pgame.le_of_lt
- \+ *theorem* pgame.lt_asymm
- \+ *theorem* pgame.lt_iff_le_not_le
- \+ *def* pgame.mul
- \+ *theorem* pgame.numeric.le_move_right
- \+ *theorem* pgame.numeric.lt_move_right
- \+ *def* pgame.numeric.move_left
- \+ *theorem* pgame.numeric.move_left_le
- \+ *theorem* pgame.numeric.move_left_lt
- \+ *def* pgame.numeric.move_right
- \+ *def* pgame.numeric
- \+ *theorem* pgame.numeric_add
- \+ *theorem* pgame.numeric_neg
- \+ *theorem* pgame.numeric_one
- \+ *theorem* pgame.numeric_rec
- \+ *theorem* pgame.numeric_zero
- \+ *def* surreal.add
- \+ *theorem* surreal.add_assoc
- \+/\- *def* surreal.equiv
- \+/\- *def* surreal.lift
- \+/\- *def* surreal.lift₂
- \+/\- *def* surreal.mk



## [2019-09-17 15:50:00](https://github.com/leanprover-community/mathlib/commit/19a246c)
fix(category_theory): require morphisms are in Type, again ([#1412](https://github.com/leanprover-community/mathlib/pull/1412))
* chore(category_theory): require morphisms live in Type
* move back to Type
* fixes
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean


Modified src/algebraic_geometry/stalks.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/category/Cat.lean


Modified src/category_theory/category/Groupoid.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/comma.lean
- \+/\- *def* category_theory.over
- \+/\- *def* category_theory.under

Modified src/category_theory/conj.lean


Modified src/category_theory/core.lean


Modified src/category_theory/currying.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/endomorphism.lean
- \+/\- *def* category_theory.Aut
- \+/\- *def* category_theory.End

Modified src/category_theory/functor_category.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/hom_functor.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.colimit.map_post
- \+/\- *lemma* category_theory.limits.colimit.pre_post
- \+/\- *def* category_theory.limits.is_colimit.of_faithful
- \+/\- *def* category_theory.limits.is_limit.of_faithful
- \+/\- *lemma* category_theory.limits.limit.map_post
- \+/\- *lemma* category_theory.limits.limit.pre_post

Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/limits/shapes/terminal.lean


Modified src/category_theory/monad/limits.lean


Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/functor.lean
- \+/\- *def* category_theory.monoidal_functor.μ_nat_iso

Modified src/category_theory/monoidal/of_has_finite_products.lean


Modified src/category_theory/monoidal/types.lean


Modified src/category_theory/natural_transformation.lean


Modified src/category_theory/pempty.lean
- \+/\- *def* category_theory.functor.empty

Modified src/category_theory/products/associator.lean


Modified src/category_theory/products/basic.lean


Modified src/category_theory/products/bifunctor.lean


Modified src/category_theory/sums/associator.lean


Modified src/category_theory/sums/basic.lean


Modified src/category_theory/types.lean
- \+/\- *lemma* category_theory.types_comp
- \+/\- *lemma* category_theory.types_hom
- \+/\- *lemma* category_theory.types_id

Modified src/category_theory/yoneda.lean
- \+/\- *def* category_theory.coyoneda
- \+/\- *def* category_theory.yoneda
- \+/\- *def* category_theory.yoneda_sections
- \+/\- *def* category_theory.yoneda_sections_small

Modified src/topology/category/Top/open_nhds.lean


Modified src/topology/category/Top/opens.lean


Modified src/topology/sheaves/presheaf.lean


Modified src/topology/sheaves/stalks.lean




## [2019-09-17 05:06:09](https://github.com/leanprover-community/mathlib/commit/ab2c546)
feat(data/quot): define `quotient.map` and `quotient.map₂` (dep: 1441) ([#1442](https://github.com/leanprover-community/mathlib/pull/1442))
* chore(algebra/group,logic/relator): review some explicit/implicit arguments
* ring_hom.ext too
* feat(data/quot): define `quotient.map` and `quotient.map₂`
* Add comments
* Fix a typo
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/quot.lean


Modified src/logic/relator.lean




## [2019-09-17 02:44:20](https://github.com/leanprover-community/mathlib/commit/d4cc179)
feat(logic/basic): eq_iff_eq_cancel ([#1447](https://github.com/leanprover-community/mathlib/pull/1447))
* feat(logic/basic): eq_iff_eq_cancel
These lemmas or not meant for `rw` but to be applied, as a sort of congruence lemma.
* State lemmas as iff
* Make'm simp
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* eq_iff_eq_cancel_left
- \+ *lemma* eq_iff_eq_cancel_right



## [2019-09-17 00:58:35](https://github.com/leanprover-community/mathlib/commit/c412527)
feat(data/list/sort): ordered_insert lemmas ([#1437](https://github.com/leanprover-community/mathlib/pull/1437))
* feat(data/list/sort): ordered_insert lemmas
* add a lemma about L.tail.count
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.count_tail

Modified src/data/list/sort.lean
- \+ *theorem* list.ordered_insert_count
- \+ *theorem* list.ordered_insert_length
- \+ *lemma* list.ordered_insert_nil
- \+ *theorem* list.sorted.tail



## [2019-09-16 23:07:50](https://github.com/leanprover-community/mathlib/commit/dd0ff1c)
feat(data/nat/basic): dvd_add_self_{left,right} ([#1448](https://github.com/leanprover-community/mathlib/pull/1448))
* feat(data/nat/basic): dvd_add_self_{left,right}
Two simp-lemmas of the form
```lean
@[simp] protected lemma dvd_add_self_left {m n : ℕ} :
  m ∣ m + n ↔ m ∣ n :=
dvd_add_right (dvd_refl m)
```
* Oops, lemmas were protected
* Provide version for rings
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *lemma* dvd_add_self_left
- \+ *lemma* dvd_add_self_right

Modified src/data/nat/basic.lean




## [2019-09-16 22:49:24](https://github.com/leanprover-community/mathlib/commit/929c186)
fix(docs/tutorial/category_theory): fix import ([#1440](https://github.com/leanprover-community/mathlib/pull/1440))
* fix(docs/tutorial/category_theory): fix import
* fix(.travis.yml): Travis stages to build docs/
* cache docs/ in travis build
#### Estimated changes
Modified .travis.yml


Modified docs/tutorial/category_theory/calculating_colimits_in_Top.lean




## [2019-09-16 21:07:29](https://github.com/leanprover-community/mathlib/commit/a3ccc7a)
chore(category_theory/notation): update notation for prod and coprod ([#1413](https://github.com/leanprover-community/mathlib/pull/1413))
* updating notation for categorical prod and coprod
* update notation
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *def* category_theory.limits.coprod.braiding
- \+/\- *def* category_theory.limits.prod.braiding



## [2019-09-16 16:01:04+02:00](https://github.com/leanprover-community/mathlib/commit/b2b0de4)
feat(algebra/group/basic): mul_left_eq_self etc ([#1446](https://github.com/leanprover-community/mathlib/pull/1446))
Simp-lemmas for groups of the form a * b = b ↔ a = 1.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* mul_left_eq_self
- \+ *lemma* mul_right_eq_self



## [2019-09-16 09:26:53](https://github.com/leanprover-community/mathlib/commit/d7f0e68)
chore(algebra/group,logic/relator): review some explicit/implicit args ([#1441](https://github.com/leanprover-community/mathlib/pull/1441))
* chore(algebra/group,logic/relator): review some explicit/implicit arguments
* ring_hom.ext too
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+/\- *lemma* monoid_hom.ext

Modified src/algebra/group/units.lean
- \+/\- *theorem* divp_eq_iff_mul_eq
- \+/\- *theorem* divp_eq_one_iff_eq
- \+/\- *theorem* units.ext

Modified src/algebra/ring.lean
- \+/\- *theorem* ring_hom.ext

Modified src/data/list/basic.lean


Modified src/data/multiset.lean


Modified src/logic/relator.lean




## [2019-09-14 05:00:40](https://github.com/leanprover-community/mathlib/commit/81a31ca)
chore(data/*): flipping inequalities ([#1436](https://github.com/leanprover-community/mathlib/pull/1436))
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
#### Estimated changes
Modified src/algebra/archimedean.lean
- \- *lemma* pow_unbounded_of_gt_one
- \+ *lemma* pow_unbounded_of_one_lt

Modified src/algebra/field_power.lean
- \- *lemma* fpow_ge_one_of_nonneg
- \+/\- *lemma* fpow_le_one_of_nonpos
- \+/\- *lemma* fpow_nonneg_of_nonneg
- \+/\- *lemma* fpow_pos_of_pos
- \+ *lemma* one_le_fpow_of_nonneg
- \+/\- *lemma* one_lt_fpow
- \+/\- *lemma* one_lt_pow
- \+/\- *lemma* pow_le_max_of_min_le

Modified src/algebra/floor.lean
- \+/\- *lemma* ceil_nonneg

Modified src/algebra/gcd_domain.lean
- \+/\- *theorem* int.gcd_pos_of_non_zero_left
- \+/\- *theorem* int.gcd_pos_of_non_zero_right

Modified src/algebra/group_power.lean
- \+/\- *theorem* add_monoid.smul_sub
- \+ *theorem* one_add_mul_le_pow
- \+ *theorem* one_add_sub_mul_le_pow
- \- *theorem* pow_ge_one_add_mul
- \- *theorem* pow_ge_one_add_sub_mul
- \+/\- *theorem* pow_sub

Modified src/algebra/order.lean
- \+/\- *lemma* decidable.ne_iff_lt_or_gt

Modified src/algebra/order_functions.lean
- \+/\- *lemma* abs_eq

Modified src/algebra/ordered_group.lean
- \+/\- *lemma* le_add_of_nonneg_left'
- \+/\- *lemma* le_add_of_nonneg_right'

Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* le_mul_iff_one_le_left
- \+/\- *lemma* le_mul_iff_one_le_right
- \- *lemma* le_mul_of_ge_one_left'
- \- *lemma* le_mul_of_ge_one_right'
- \+ *lemma* le_mul_of_one_le_left'
- \+ *lemma* le_mul_of_one_le_right'
- \+/\- *lemma* lt_mul_iff_one_lt_left
- \+/\- *lemma* lt_mul_iff_one_lt_right
- \- *lemma* lt_mul_of_gt_one_right'
- \+ *lemma* lt_mul_of_one_lt_right'
- \+/\- *lemma* mul_le_iff_le_one_left
- \+/\- *lemma* mul_le_iff_le_one_right
- \+/\- *lemma* mul_lt_iff_lt_one_left
- \+/\- *lemma* mul_lt_iff_lt_one_right
- \+ *lemma* mul_nonneg'
- \+ *lemma* mul_pos'
- \- *lemma* zero_le_mul

Modified src/analysis/convex.lean


Modified src/analysis/specific_limits.lean


Modified src/computability/partrec_code.lean


Modified src/computability/primrec.lean


Modified src/data/equiv/fin.lean


Modified src/data/fin.lean
- \+/\- *lemma* fin.add_nat_val
- \+/\- *def* fin.sub_nat
- \+/\- *lemma* fin.sub_nat_val

Modified src/data/finset.lean
- \- *lemma* finset.Ico.filter_ge
- \- *lemma* finset.Ico.filter_ge_of_ge
- \- *lemma* finset.Ico.filter_ge_of_le_bot
- \- *lemma* finset.Ico.filter_ge_of_top_le
- \+ *lemma* finset.Ico.filter_le
- \+ *lemma* finset.Ico.filter_le_of_le
- \+ *lemma* finset.Ico.filter_le_of_le_bot
- \+ *lemma* finset.Ico.filter_le_of_top_le
- \+/\- *theorem* finset.Ico.pred_singleton

Modified src/data/fintype.lean
- \- *lemma* fintype.exists_ne_of_card_gt_one
- \+ *lemma* fintype.exists_ne_of_one_lt_card

Modified src/data/fp/basic.lean


Modified src/data/int/basic.lean
- \+/\- *theorem* int.div_le_self
- \+/\- *theorem* int.div_neg'
- \+/\- *theorem* int.div_of_neg_of_pos
- \+/\- *theorem* int.div_pos_of_pos_of_dvd
- \+/\- *theorem* int.dvd_antisymm
- \+/\- *theorem* int.eq_one_of_dvd_one
- \+/\- *theorem* int.eq_one_of_mul_eq_one_left
- \+/\- *theorem* int.eq_one_of_mul_eq_one_right
- \+/\- *theorem* int.le_of_dvd
- \+/\- *theorem* int.lt_div_add_one_mul_self
- \+/\- *theorem* int.mod_lt_of_pos
- \+/\- *theorem* int.mod_nonneg
- \+/\- *theorem* int.mul_div_mul_of_pos
- \+/\- *theorem* int.mul_div_mul_of_pos_left
- \+/\- *theorem* int.mul_mod_mul_of_pos
- \+/\- *theorem* int.neg_succ_of_nat_div
- \+/\- *theorem* int.neg_succ_of_nat_mod

Modified src/data/int/modeq.lean
- \+/\- *lemma* int.modeq.exists_unique_equiv
- \+/\- *lemma* int.modeq.exists_unique_equiv_nat

Modified src/data/list/basic.lean
- \- *lemma* list.Ico.filter_ge
- \- *lemma* list.Ico.filter_ge_of_ge
- \- *lemma* list.Ico.filter_ge_of_le_bot
- \- *lemma* list.Ico.filter_ge_of_top_le
- \+ *lemma* list.Ico.filter_le
- \+ *lemma* list.Ico.filter_le_of_le
- \+ *lemma* list.Ico.filter_le_of_le_bot
- \+ *lemma* list.Ico.filter_le_of_top_le
- \+/\- *theorem* list.Ico.pred_singleton
- \- *theorem* list.nth_ge_len
- \+ *theorem* list.nth_len_le
- \- *theorem* list.take_all_of_ge
- \+ *theorem* list.take_all_of_le

Modified src/data/multiset.lean
- \- *lemma* multiset.Ico.filter_ge
- \- *lemma* multiset.Ico.filter_ge_of_ge
- \- *lemma* multiset.Ico.filter_ge_of_le_bot
- \- *lemma* multiset.Ico.filter_ge_of_top_le
- \+ *lemma* multiset.Ico.filter_le
- \+ *lemma* multiset.Ico.filter_le_of_le
- \+ *lemma* multiset.Ico.filter_le_of_le_bot
- \+ *lemma* multiset.Ico.filter_le_of_top_le
- \+/\- *theorem* multiset.Ico.pred_singleton

Modified src/data/nat/basic.lean
- \+/\- *theorem* nat.add_pos_iff_pos_or_pos
- \+/\- *theorem* nat.add_pos_left
- \+/\- *theorem* nat.add_pos_right
- \+/\- *theorem* nat.dvd_fact
- \+/\- *theorem* nat.fact_pos
- \+/\- *lemma* nat.le_induction
- \+/\- *lemma* nat.le_mul_of_pos_left
- \+/\- *lemma* nat.le_mul_of_pos_right
- \+/\- *lemma* nat.lt_pow_self
- \+/\- *lemma* nat.not_pos_pow_dvd
- \+/\- *theorem* nat.pos_iff_ne_zero
- \+/\- *lemma* nat.pow_lt_pow_succ
- \+/\- *theorem* nat.pow_pos

Modified src/data/nat/cast.lean
- \+/\- *theorem* nat.cast_pred

Modified src/data/nat/dist.lean
- \+/\- *theorem* nat.dist_pos_of_ne

Modified src/data/nat/gcd.lean
- \+/\- *theorem* nat.coprime_div_gcd_div_gcd
- \+/\- *theorem* nat.coprime_of_dvd
- \+/\- *theorem* nat.exists_coprime'
- \+/\- *theorem* nat.exists_coprime
- \+/\- *theorem* nat.gcd_le_left
- \+/\- *theorem* nat.gcd_le_right
- \+/\- *theorem* nat.gcd_pos_of_pos_left
- \+/\- *theorem* nat.gcd_pos_of_pos_right
- \+/\- *theorem* nat.not_coprime_of_dvd_of_dvd

Modified src/data/nat/modeq.lean


Modified src/data/nat/pairing.lean
- \+/\- *theorem* nat.unpair_lt

Modified src/data/nat/parity.lean
- \+/\- *theorem* nat.even_sub

Modified src/data/nat/prime.lean
- \- *theorem* nat.dvd_prime_ge_two
- \+ *theorem* nat.dvd_prime_two_le
- \+/\- *theorem* nat.exists_dvd_of_not_prime2
- \+/\- *theorem* nat.exists_dvd_of_not_prime
- \+/\- *theorem* nat.exists_infinite_primes
- \+/\- *theorem* nat.exists_prime_and_dvd
- \+/\- *theorem* nat.min_fac_aux_has_prop
- \+/\- *theorem* nat.min_fac_le
- \+/\- *theorem* nat.min_fac_le_of_dvd
- \+/\- *theorem* nat.min_fac_pos
- \+/\- *theorem* nat.not_prime_iff_min_fac_lt
- \- *theorem* nat.prime.ge_two
- \- *theorem* nat.prime.gt_one
- \+ *theorem* nat.prime.one_lt
- \+/\- *theorem* nat.prime.pos
- \+/\- *theorem* nat.prime.pred_pos
- \+ *theorem* nat.prime.two_le
- \+/\- *def* nat.prime
- \+/\- *theorem* nat.prime_def_le_sqrt
- \+/\- *theorem* nat.prime_def_lt'
- \+/\- *theorem* nat.prime_def_lt
- \+/\- *theorem* nat.prime_def_min_fac

Modified src/data/nat/sqrt.lean
- \+/\- *theorem* nat.sqrt_lt_self
- \+/\- *theorem* nat.sqrt_pos

Modified src/data/nat/totient.lean


Modified src/data/num/lemmas.lean
- \+/\- *theorem* pos_num.cast_pos
- \+/\- *theorem* pos_num.to_nat_pos

Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/pnat/basic.lean
- \+/\- *def* nat.to_pnat
- \+/\- *theorem* pnat.pos
- \+/\- *theorem* pnat.sub_coe
- \+/\- *theorem* pnat.to_pnat'_coe
- \+/\- *def* pnat

Modified src/data/polynomial.lean


Modified src/data/rat/basic.lean


Modified src/data/rat/order.lean
- \+/\- *theorem* rat.mk_nonneg

Modified src/data/real/irrational.lean


Modified src/data/real/nnreal.lean


Modified src/data/zmod/basic.lean


Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/data/zsqrtd/basic.lean
- \+/\- *theorem* zsqrtd.not_sq_le_succ

Modified src/data/zsqrtd/gaussian_int.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/sylow.lean


Modified src/number_theory/sum_two_squares.lean




## [2019-09-13 07:38:04](https://github.com/leanprover-community/mathlib/commit/e3234f0)
feat(algebra/ring): add coercions from →+* to →* and →+ ([#1435](https://github.com/leanprover-community/mathlib/pull/1435))
* feat(algebra/ring): add coercions from →+* to →* and →+
* two lemmas simplifying casts
* add squash_cast attributes
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *lemma* coe_add_monoid_hom
- \+ *lemma* coe_monoid_hom



## [2019-09-11 23:51:16](https://github.com/leanprover-community/mathlib/commit/590fb89)
chore(category_theory/functor_category): improve comment warning about hcomp_assoc [ci skip] ([#1434](https://github.com/leanprover-community/mathlib/pull/1434))
* expanding comment
* no scare quotes
#### Estimated changes
Modified src/category_theory/functor_category.lean




## [2019-09-11 17:42:41](https://github.com/leanprover-community/mathlib/commit/140a606)
feat(well_founded_tactics):  patch default_dec_tac ([#1419](https://github.com/leanprover-community/mathlib/pull/1419))
* let simp flip inequalities
* feat(well_founded_tactics):  patch default_dec_tac
* Keeley's suggested syntax, and adding to the docs
* more
* add docs
#### Estimated changes
Modified docs/extras/well_founded_recursion.md


Modified docs/tactics.md


Modified src/computability/partrec_code.lean


Modified src/data/hash_map.lean


Modified src/data/list/basic.lean


Modified src/data/list/sort.lean


Modified src/data/nat/basic.lean
- \+ *lemma* nat.succ_pos'

Modified src/data/vector2.lean
- \+/\- *lemma* vector.nth_map

Modified src/set_theory/lists.lean


Modified src/tactic/basic.lean


Added src/tactic/well_founded_tactics.lean




## [2019-09-11 12:46:21](https://github.com/leanprover-community/mathlib/commit/e27142a)
chore(*): renaming files constructing category instances ([#1432](https://github.com/leanprover-community/mathlib/pull/1432))
#### Estimated changes
Deleted src/algebra/CommRing/default.lean


Deleted src/algebra/Mon/default.lean


Renamed src/algebra/CommRing/adjunctions.lean to src/algebra/category/CommRing/adjunctions.lean


Renamed src/algebra/CommRing/basic.lean to src/algebra/category/CommRing/basic.lean


Renamed src/algebra/CommRing/colimits.lean to src/algebra/category/CommRing/colimits.lean


Added src/algebra/category/CommRing/default.lean


Renamed src/algebra/CommRing/limits.lean to src/algebra/category/CommRing/limits.lean


Renamed src/group_theory/category.lean to src/algebra/category/Group.lean


Renamed src/algebra/Mon/basic.lean to src/algebra/category/Mon/basic.lean


Renamed src/algebra/Mon/colimits.lean to src/algebra/category/Mon/colimits.lean


Added src/algebra/category/Mon/default.lean


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/algebraic_geometry/stalks.lean


Modified src/category/fold.lean


Renamed src/category_theory/Cat.lean to src/category_theory/category/Cat.lean


Renamed src/category_theory/groupoid_category.lean to src/category_theory/category/Groupoid.lean


Renamed src/category_theory/instances/kleisli.lean to src/category_theory/category/Kleisli.lean


Renamed src/category_theory/instances/rel.lean to src/category_theory/category/Rel.lean


Renamed src/category_theory/category.lean to src/category_theory/category/default.lean


Modified src/category_theory/single_obj.lean


Renamed src/measure_theory/Meas.lean to src/measure_theory/category/Meas.lean


Modified src/measure_theory/giry_monad.lean


Deleted src/topology/Top/default.lean


Deleted src/topology/algebra/TopCommRing/default.lean


Renamed src/topology/Top/adjunctions.lean to src/topology/category/Top/adjunctions.lean


Renamed src/topology/Top/basic.lean to src/topology/category/Top/basic.lean


Added src/topology/category/Top/default.lean


Renamed src/topology/Top/epi_mono.lean to src/topology/category/Top/epi_mono.lean


Renamed src/topology/Top/limits.lean to src/topology/category/Top/limits.lean


Renamed src/topology/Top/open_nhds.lean to src/topology/category/Top/open_nhds.lean


Renamed src/topology/Top/opens.lean to src/topology/category/Top/opens.lean


Renamed src/topology/algebra/TopCommRing/basic.lean to src/topology/category/TopCommRing.lean


Renamed src/topology/uniform_space/UniformSpace.lean to src/topology/category/UniformSpace.lean


Renamed src/topology/Top/presheaf.lean to src/topology/sheaves/presheaf.lean


Renamed src/topology/Top/presheaf_of_functions.lean to src/topology/sheaves/presheaf_of_functions.lean


Renamed src/topology/Top/stalks.lean to src/topology/sheaves/stalks.lean




## [2019-09-11 03:52:18](https://github.com/leanprover-community/mathlib/commit/8a5156f)
fix(algebra/*/colimits): avoid explicit `infer_instance` ([#1430](https://github.com/leanprover-community/mathlib/pull/1430))
With an explicit universe level Lean can do it automatically.
#### Estimated changes
Modified src/algebra/CommRing/colimits.lean


Modified src/algebra/Mon/colimits.lean




## [2019-09-11 01:49:04](https://github.com/leanprover-community/mathlib/commit/45fe081)
feat(logic): make some decidability proofs [inline] ([#1393](https://github.com/leanprover-community/mathlib/pull/1393))
* feat(logic): make some decidability proofs [inline]
* inline more decidability proofs
* test
* import logic.basic in test
#### Estimated changes
Modified src/logic/basic.lean


Added test/logic_inline.lean




## [2019-09-10 23:38:55](https://github.com/leanprover-community/mathlib/commit/8e46fa5)
chore(algebra/group/to_additive): map_namespace should make a meta constant ([#1409](https://github.com/leanprover-community/mathlib/pull/1409))
* chore(algebra/group/to_additive): map_namespace should make a meta constance
`map_namespace` now produces a `meta constant` instead of a constant. This means that after importing `group_theory/coset` and typing `#print axioms`, `quotient_group._to_additive` is not in the list, since it is now a `meta constant`. This is a little bit neater, and it doesn't look like we're adding any axioms.
* Update to_additive.lean
* Update to_additive.lean
#### Estimated changes
Modified src/algebra/group/to_additive.lean




## [2019-09-10 22:44:22](https://github.com/leanprover-community/mathlib/commit/e2f904e)
feat(tactic/auto_cases): run auto_cases on false and psigma ([#1428](https://github.com/leanprover-community/mathlib/pull/1428))
#### Estimated changes
Modified src/tactic/auto_cases.lean




## [2019-09-10 19:55:17](https://github.com/leanprover-community/mathlib/commit/c87ec0e)
feat(tactic/{abel,ring}): state conditions of tactics more precisely ([#1423](https://github.com/leanprover-community/mathlib/pull/1423))
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/abel.lean


Modified src/tactic/ring.lean


Added test/abel.lean




## [2019-09-10 15:33:29](https://github.com/leanprover-community/mathlib/commit/2dd6398)
let simp flip inequalities ([#1418](https://github.com/leanprover-community/mathlib/pull/1418))
#### Estimated changes
Modified src/algebra/order.lean
- \+ *lemma* ge_iff_le
- \+ *lemma* gt_iff_lt

Modified src/data/rat/order.lean


Modified src/number_theory/pell.lean


Modified src/tactic/linarith.lean




## [2019-09-10 11:26:37](https://github.com/leanprover-community/mathlib/commit/0935e8b)
feat(algebra/group/units): add some lemmas about `divp` ([#1388](https://github.com/leanprover-community/mathlib/pull/1388))
* feat(algebra/group/units): add some lemmas about `divp`
* Rename lemmas, add new ones
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *theorem* divp_divp_eq_divp_mul
- \+ *theorem* divp_eq_divp_iff
- \+ *theorem* divp_eq_iff_mul_eq
- \- *theorem* divp_eq_one
- \+ *theorem* divp_eq_one_iff_eq
- \+ *theorem* divp_inv
- \+ *theorem* divp_mul_divp



## [2019-09-10 09:32:30](https://github.com/leanprover-community/mathlib/commit/fe1575a)
chore(topology): sanity_check pass ([#1416](https://github.com/leanprover-community/mathlib/pull/1416))
* chore(topology): sanity_check pass
* improvement
* avoid _inst_3 to recover instance
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+/\- *theorem* asymptotics.is_o_iff_tendsto

Modified src/analysis/convex.lean
- \+/\- *lemma* convex_on_sum

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *theorem* is_bounded_linear_map.is_O_comp

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *theorem* continuous_linear_map.is_O_comp

Modified src/logic/basic.lean
- \+/\- *theorem* ball_of_forall
- \+/\- *theorem* not_iff

Modified src/meta/rb_map.lean


Modified src/order/basic.lean
- \+ *lemma* antisymm_of_asymm
- \- *def* antisymm_of_asymm
- \+/\- *theorem* comp_le_comp_left_of_monotone
- \+/\- *lemma* dense_or_discrete

Modified src/order/bounded_lattice.lean
- \+/\- *theorem* with_top.coe_ne_top
- \+/\- *theorem* with_top.top_ne_coe

Modified src/order/complete_lattice.lean
- \+ *lemma* lattice.has_Inf_to_nonempty
- \- *def* lattice.has_Inf_to_nonempty
- \+ *lemma* lattice.has_Sup_to_nonempty
- \- *def* lattice.has_Sup_to_nonempty
- \+/\- *theorem* lattice.insert_of_has_insert

Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* lattice.cInf_interval
- \+/\- *lemma* lattice.cSup_interval

Modified src/order/filter/partial.lean
- \+ *lemma* filter.mem_pmap
- \- *def* filter.mem_pmap
- \+ *lemma* filter.mem_rcomap'
- \- *def* filter.mem_rcomap'

Modified src/order/liminf_limsup.lean
- \+/\- *lemma* filter.liminf_le_liminf
- \+/\- *lemma* filter.liminf_le_limsup
- \+/\- *lemma* filter.limsup_le_limsup

Modified src/order/order_iso.lean
- \+ *def* order_embedding.nat_gt
- \- *theorem* order_embedding.nat_gt
- \+ *def* order_embedding.nat_lt
- \- *theorem* order_embedding.nat_lt
- \+/\- *theorem* order_embedding.well_founded_iff_no_descending_seq
- \+ *def* order_iso.prod_lex_congr
- \- *theorem* order_iso.prod_lex_congr
- \+ *def* order_iso.sum_lex_congr
- \- *theorem* order_iso.sum_lex_congr

Modified src/topology/algebra/group.lean
- \+ *lemma* nhds_is_mul_hom
- \- *def* nhds_is_mul_hom
- \+/\- *lemma* quotient_group_saturate

Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* has_sum_hom

Modified src/topology/algebra/module.lean
- \+/\- *lemma* continuous_linear_map.coe_add'
- \+/\- *lemma* continuous_linear_map.coe_add
- \+/\- *lemma* continuous_linear_map.coe_apply'
- \+/\- *lemma* continuous_linear_map.coe_apply
- \+/\- *lemma* continuous_linear_map.coe_neg'
- \+/\- *lemma* continuous_linear_map.coe_neg
- \+/\- *lemma* continuous_linear_map.coe_sub'
- \+/\- *lemma* continuous_linear_map.coe_sub

Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/ring.lean
- \+/\- *lemma* quotient_ring_saturate

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean
- \+/\- *lemma* mem_closure
- \+/\- *lemma* tendsto_pure_nhds

Modified src/topology/constructions.lean
- \+/\- *lemma* continuous_at_subtype_val
- \+/\- *def* dense_embedding.subtype_emb
- \+/\- *lemma* dense_range_prod
- \+/\- *lemma* diagonal_eq_range_diagonal_map
- \+/\- *lemma* is_closed_diagonal
- \+/\- *lemma* is_closed_eq
- \+/\- *lemma* is_closed_prod
- \+/\- *lemma* is_closed_property
- \+/\- *lemma* list.continuous_at_length
- \+/\- *lemma* list.tendsto_cons
- \+/\- *lemma* list.tendsto_cons_iff
- \+/\- *lemma* list.tendsto_insert_nth
- \+/\- *lemma* list.tendsto_nhds
- \+/\- *lemma* locally_compact_of_compact_nhds
- \+/\- *lemma* mem_closure2
- \+/\- *lemma* normal_of_compact_t2
- \+/\- *lemma* prod_eq_generate_from
- \+/\- *lemma* prod_generate_from_generate_from_eq
- \+/\- *lemma* prod_subset_compl_diagonal_iff_disjoint
- \+/\- *lemma* tendsto_subtype_rng

Modified src/topology/maps.lean
- \+ *def* dense_range.inhabited
- \- *lemma* dense_range.inhabited
- \+/\- *lemma* embedding.map_nhds_eq
- \+ *lemma* embedding.mk'
- \- *def* embedding.mk'
- \+/\- *lemma* inducing.map_nhds_eq
- \+/\- *lemma* inducing.nhds_eq_comap

Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* subtype.dist_eq

Modified src/topology/metric_space/cau_seq_filter.lean
- \+/\- *lemma* sequentially_complete.B2_lim
- \+/\- *lemma* sequentially_complete.B2_pos

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* subtype.edist_eq

Modified src/topology/metric_space/gluing.lean
- \+/\- *lemma* metric.glue_dist_glued_points

Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/isometry.lean
- \+ *def* isometry.isometric_on_range
- \- *lemma* isometry.isometric_on_range

Modified src/topology/opens.lean
- \+ *lemma* topological_space.opens.gc
- \- *def* topological_space.opens.gc

Modified src/topology/order.lean
- \+ *lemma* continuous_iff_continuous_on_univ
- \- *def* continuous_iff_continuous_on_univ
- \+/\- *theorem* continuous_within_at_iff_ptendsto_res
- \+/\- *lemma* induced_compose
- \+/\- *theorem* principal_subtype

Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean
- \+/\- *lemma* compact_image
- \+/\- *lemma* compact_of_closed
- \+/\- *lemma* compact_range
- \+/\- *lemma* compact_univ

Modified src/topology/uniform_space/uniform_embedding.lean




## [2019-09-10 01:55:13](https://github.com/leanprover-community/mathlib/commit/72d6325)
feat(sanity_check): greatly improve performance ([#1389](https://github.com/leanprover-community/mathlib/pull/1389))
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
#### Estimated changes
Modified src/data/bool.lean


Modified src/data/list/defs.lean
- \+ *def* list.mmap_filter

Modified src/meta/expr.lean


Modified src/tactic/core.lean


Modified src/tactic/sanity_check.lean


Modified test/sanity_check.lean




## [2019-09-09 21:11:13](https://github.com/leanprover-community/mathlib/commit/228d5ba)
feat(algebra/big_operators): sum_eq_zero_iff_of_nonpos ([#1424](https://github.com/leanprover-community/mathlib/pull/1424))
* feat(algebra/big_operators): sum_eq_zero_iff_of_nonpos
* more order_dual instances
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.sum_eq_zero_iff_of_nonpos

Modified src/algebra/ordered_group.lean




## [2019-09-08 16:37:05](https://github.com/leanprover-community/mathlib/commit/313fe11)
feat(algebra/floor): Split floor from archimedean file. ([#1372](https://github.com/leanprover-community/mathlib/pull/1372))
* feat(algebra/floor): Split floor from archimedean file.
* feat({algebra,rat}/floor): move lemmas/defs from rat.floor to algebra.floor
#### Estimated changes
Modified src/algebra/archimedean.lean
- \- *lemma* abs_sub_lt_one_of_floor_eq_floor
- \- *def* ceil
- \- *theorem* ceil_add_int
- \- *theorem* ceil_coe
- \- *theorem* ceil_le
- \- *theorem* ceil_lt_add_one
- \- *theorem* ceil_mono
- \- *lemma* ceil_nonneg
- \- *lemma* ceil_pos
- \- *theorem* ceil_sub_int
- \- *theorem* ceil_zero
- \- *def* floor
- \- *lemma* floor_add_fract
- \- *theorem* floor_add_int
- \- *theorem* floor_coe
- \- *lemma* floor_eq_iff
- \- *lemma* floor_fract
- \- *theorem* floor_le
- \- *theorem* floor_lt
- \- *theorem* floor_mono
- \- *theorem* floor_nonneg
- \- *theorem* floor_one
- \- *theorem* floor_sub_int
- \- *theorem* floor_zero
- \- *def* fract
- \- *theorem* fract_add
- \- *lemma* fract_add_floor
- \- *lemma* fract_coe
- \- *theorem* fract_eq_fract
- \- *theorem* fract_eq_iff
- \- *lemma* fract_floor
- \- *lemma* fract_fract
- \- *theorem* fract_lt_one
- \- *theorem* fract_mul_nat
- \- *theorem* fract_nonneg
- \- *lemma* fract_zero
- \- *theorem* le_ceil
- \- *theorem* le_floor
- \- *theorem* lt_ceil
- \- *theorem* lt_floor_add_one
- \- *theorem* lt_succ_floor
- \- *theorem* sub_one_lt_floor

Added src/algebra/floor.lean
- \+ *lemma* abs_sub_lt_one_of_floor_eq_floor
- \+ *def* ceil
- \+ *theorem* ceil_add_int
- \+ *theorem* ceil_coe
- \+ *theorem* ceil_le
- \+ *theorem* ceil_lt_add_one
- \+ *theorem* ceil_mono
- \+ *lemma* ceil_nonneg
- \+ *lemma* ceil_pos
- \+ *theorem* ceil_sub_int
- \+ *theorem* ceil_zero
- \+ *def* floor
- \+ *lemma* floor_add_fract
- \+ *theorem* floor_add_int
- \+ *theorem* floor_coe
- \+ *lemma* floor_eq_iff
- \+ *lemma* floor_fract
- \+ *theorem* floor_le
- \+ *theorem* floor_lt
- \+ *theorem* floor_mono
- \+ *theorem* floor_nonneg
- \+ *theorem* floor_one
- \+ *lemma* floor_ring_unique
- \+ *theorem* floor_sub_int
- \+ *theorem* floor_zero
- \+ *def* fract
- \+ *theorem* fract_add
- \+ *lemma* fract_add_floor
- \+ *lemma* fract_coe
- \+ *theorem* fract_eq_fract
- \+ *theorem* fract_eq_iff
- \+ *lemma* fract_floor
- \+ *lemma* fract_fract
- \+ *theorem* fract_lt_one
- \+ *theorem* fract_mul_nat
- \+ *theorem* fract_nonneg
- \+ *lemma* fract_zero
- \+ *theorem* le_ceil
- \+ *theorem* le_floor
- \+ *theorem* le_nat_ceil
- \+ *theorem* lt_ceil
- \+ *theorem* lt_floor_add_one
- \+ *theorem* lt_nat_ceil
- \+ *theorem* lt_succ_floor
- \+ *def* nat_ceil
- \+ *theorem* nat_ceil_add_nat
- \+ *theorem* nat_ceil_coe
- \+ *theorem* nat_ceil_le
- \+ *theorem* nat_ceil_lt_add_one
- \+ *theorem* nat_ceil_mono
- \+ *theorem* nat_ceil_zero
- \+ *theorem* sub_one_lt_floor

Modified src/data/rat/floor.lean
- \- *def* rat.ceil
- \- *theorem* rat.ceil_add_int
- \- *theorem* rat.ceil_coe
- \- *theorem* rat.ceil_le
- \- *theorem* rat.ceil_mono
- \- *theorem* rat.ceil_sub_int
- \- *def* rat.floor
- \- *theorem* rat.floor_add_int
- \- *theorem* rat.floor_coe
- \- *lemma* rat.floor_def
- \- *theorem* rat.floor_le
- \- *theorem* rat.floor_lt
- \- *theorem* rat.floor_mono
- \- *theorem* rat.floor_sub_int
- \- *theorem* rat.le_ceil
- \- *theorem* rat.le_floor
- \- *theorem* rat.le_nat_ceil
- \- *theorem* rat.lt_nat_ceil
- \- *theorem* rat.lt_succ_floor
- \- *def* rat.nat_ceil
- \- *theorem* rat.nat_ceil_add_nat
- \- *theorem* rat.nat_ceil_coe
- \- *theorem* rat.nat_ceil_le
- \- *theorem* rat.nat_ceil_lt_add_one
- \- *theorem* rat.nat_ceil_mono
- \- *theorem* rat.nat_ceil_zero

Modified src/tactic/norm_num.lean




## [2019-09-08 12:00:15](https://github.com/leanprover-community/mathlib/commit/37b6746)
feat(data/list/basic): make chain.nil a simp lemma ([#1414](https://github.com/leanprover-community/mathlib/pull/1414))
#### Estimated changes
Modified src/data/list/basic.lean


Modified src/data/list/defs.lean




## [2019-09-08 08:47:37](https://github.com/leanprover-community/mathlib/commit/6f7224c)
feat(data/list/defs): move list.sum to list/defs.lean ([#1415](https://github.com/leanprover-community/mathlib/pull/1415))
* feat(data/list/defs): move list.sum to list/defs.lean
* add comment
#### Estimated changes
Modified src/data/list/basic.lean


Modified src/data/list/defs.lean
- \+ *def* list.sum



## [2019-09-08 06:22:25](https://github.com/leanprover-community/mathlib/commit/8bdb147)
feat(topology/local_homeomorph): local homeomorphisms ([#1398](https://github.com/leanprover-community/mathlib/pull/1398))
* feat(topology/local_homeomorph): local homeomorphisms
* local_homeomorph: reviewer comments
#### Estimated changes
Added src/topology/local_homeomorph.lean
- \+ *lemma* homeomorph.refl_to_local_homeomorph
- \+ *lemma* homeomorph.symm_to_local_homeomorph
- \+ *def* homeomorph.to_local_homeomorph
- \+ *lemma* homeomorph.to_local_homeomorph_inv_fun
- \+ *lemma* homeomorph.to_local_homeomorph_source
- \+ *lemma* homeomorph.to_local_homeomorph_target
- \+ *lemma* homeomorph.to_local_homeomorph_to_fun
- \+ *lemma* homeomorph.trans_to_local_homeomorph
- \+ *lemma* local_homeomorph.apply_eq_of_eq_on_source
- \+ *lemma* local_homeomorph.continuous_on_iff_continuous_on_comp_left
- \+ *lemma* local_homeomorph.continuous_on_iff_continuous_on_comp_right
- \+ *lemma* local_homeomorph.eq_of_eq_on_source_univ
- \+ *lemma* local_homeomorph.eq_of_local_equiv_eq
- \+ *def* local_homeomorph.eq_on_source
- \+ *lemma* local_homeomorph.eq_on_source_iff
- \+ *lemma* local_homeomorph.eq_on_source_refl
- \+ *lemma* local_homeomorph.eq_on_source_restr
- \+ *lemma* local_homeomorph.eq_on_source_symm
- \+ *lemma* local_homeomorph.eq_on_source_trans
- \+ *lemma* local_homeomorph.image_trans_source
- \+ *lemma* local_homeomorph.inv_apply_eq_of_eq_on_source
- \+ *lemma* local_homeomorph.inv_image_trans_target
- \+ *def* local_homeomorph.of_set
- \+ *lemma* local_homeomorph.of_set_inv_fun
- \+ *lemma* local_homeomorph.of_set_source
- \+ *lemma* local_homeomorph.of_set_symm
- \+ *lemma* local_homeomorph.of_set_target
- \+ *lemma* local_homeomorph.of_set_to_fun
- \+ *lemma* local_homeomorph.of_set_to_local_equiv
- \+ *lemma* local_homeomorph.of_set_trans'
- \+ *lemma* local_homeomorph.of_set_trans
- \+ *lemma* local_homeomorph.preimage_interior
- \+ *def* local_homeomorph.prod
- \+ *lemma* local_homeomorph.prod_inv_fun
- \+ *lemma* local_homeomorph.prod_source
- \+ *lemma* local_homeomorph.prod_target
- \+ *lemma* local_homeomorph.prod_to_fun
- \+ *lemma* local_homeomorph.prod_to_local_equiv
- \+ *lemma* local_homeomorph.refl_inv_fun
- \+ *lemma* local_homeomorph.refl_local_equiv
- \+ *lemma* local_homeomorph.refl_source
- \+ *lemma* local_homeomorph.refl_symm
- \+ *lemma* local_homeomorph.refl_target
- \+ *lemma* local_homeomorph.refl_to_fun
- \+ *lemma* local_homeomorph.refl_trans
- \+ *lemma* local_homeomorph.restr_eq_of_source_subset
- \+ *lemma* local_homeomorph.restr_inv_fun
- \+ *lemma* local_homeomorph.restr_open_source
- \+ *lemma* local_homeomorph.restr_open_to_local_equiv
- \+ *lemma* local_homeomorph.restr_source'
- \+ *lemma* local_homeomorph.restr_source
- \+ *lemma* local_homeomorph.restr_source_inter
- \+ *lemma* local_homeomorph.restr_target
- \+ *lemma* local_homeomorph.restr_to_fun
- \+ *lemma* local_homeomorph.restr_to_local_equiv'
- \+ *lemma* local_homeomorph.restr_to_local_equiv
- \+ *lemma* local_homeomorph.restr_trans
- \+ *lemma* local_homeomorph.restr_univ
- \+ *lemma* local_homeomorph.source_eq_of_eq_on_source
- \+ *lemma* local_homeomorph.symm_inv_fun
- \+ *lemma* local_homeomorph.symm_source
- \+ *lemma* local_homeomorph.symm_symm
- \+ *lemma* local_homeomorph.symm_target
- \+ *lemma* local_homeomorph.symm_to_fun
- \+ *lemma* local_homeomorph.symm_to_local_equiv
- \+ *lemma* local_homeomorph.target_eq_of_eq_on_source
- \+ *lemma* local_homeomorph.trans_assoc
- \+ *lemma* local_homeomorph.trans_inv_fun
- \+ *lemma* local_homeomorph.trans_of_set'
- \+ *lemma* local_homeomorph.trans_of_set
- \+ *lemma* local_homeomorph.trans_refl
- \+ *lemma* local_homeomorph.trans_self_symm
- \+ *lemma* local_homeomorph.trans_source''
- \+ *lemma* local_homeomorph.trans_source'
- \+ *lemma* local_homeomorph.trans_source
- \+ *lemma* local_homeomorph.trans_symm_eq_symm_trans_symm
- \+ *lemma* local_homeomorph.trans_symm_self
- \+ *lemma* local_homeomorph.trans_target''
- \+ *lemma* local_homeomorph.trans_target'
- \+ *lemma* local_homeomorph.trans_target
- \+ *lemma* local_homeomorph.trans_to_fun
- \+ *lemma* local_homeomorph.trans_to_local_equiv



## [2019-09-07 05:32:33](https://github.com/leanprover-community/mathlib/commit/10cb0d1)
feat(topology/constructions): distributivity of products over sums ([#1059](https://github.com/leanprover-community/mathlib/pull/1059))
* feat(topology/constructions): distributivity of products over sums
* Update src/topology/maps.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Reverse direction of sigma_prod_distrib
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.sigma_prod_distrib

Modified src/data/set/lattice.lean
- \+ *theorem* set.Union_image_preimage_sigma_mk_eq_self

Modified src/topology/constructions.lean
- \+ *def* homeomorph.homeomorph_of_continuous_open
- \+ *def* homeomorph.sigma_prod_distrib
- \+ *lemma* is_open_map_sigma
- \+ *lemma* open_embedding_sigma_mk

Modified src/topology/maps.lean
- \+ *lemma* closed_embedding.is_closed_map
- \+ *lemma* closed_embedding_of_embedding_closed
- \+ *lemma* open_embedding.is_open_map
- \+ *lemma* open_embedding.open_iff_image_open
- \+ *lemma* open_embedding.open_iff_preimage_open
- \+ *def* open_embedding
- \+ *lemma* open_embedding_compose
- \+ *lemma* open_embedding_id
- \+ *lemma* open_embedding_of_continuous_injective_open
- \+ *lemma* open_embedding_of_embedding_open



## [2019-09-07 05:17:43](https://github.com/leanprover-community/mathlib/commit/d6a0ac5)
refactor(category_theory/limits/shapes/pullbacks): proof golf ([#1407](https://github.com/leanprover-community/mathlib/pull/1407))
* refactor(category_theory/limits): make is_[co]limit not a class
* refactor(category_theory/limits/shapes/pullbacks): proof golf
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean




## [2019-09-07 05:00:00](https://github.com/leanprover-community/mathlib/commit/8eab714)
refactor(category_theory/limits): make is_[co]limit not a class ([#1405](https://github.com/leanprover-community/mathlib/pull/1405))
#### Estimated changes
Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.colimit.is_colimit
- \+ *def* category_theory.limits.limit.is_limit

Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/limits/shapes/terminal.lean




## [2019-09-06 22:20:07+02:00](https://github.com/leanprover-community/mathlib/commit/a7f268b)
fix(category_theory/limits/shapes): doc typo [ci skip] ([#1406](https://github.com/leanprover-community/mathlib/pull/1406))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean




## [2019-09-06 12:45:57+02:00](https://github.com/leanprover-community/mathlib/commit/a5fa162)
chore(data/mv_polynomial): use classical logic ([#1391](https://github.com/leanprover-community/mathlib/pull/1391))
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
#### Estimated changes
Modified src/algebra/CommRing/adjunctions.lean


Modified src/data/finsupp.lean
- \+/\- *lemma* finsupp.comap_domain_apply
- \+/\- *lemma* finsupp.count_to_multiset
- \+/\- *lemma* finsupp.eq_zero_of_comap_domain_eq_zero
- \+/\- *def* finsupp.equiv_fun_on_fintype
- \+/\- *def* finsupp.equiv_multiset
- \+/\- *def* finsupp.filter
- \+/\- *lemma* finsupp.filter_curry
- \+/\- *lemma* finsupp.filter_pos_add_filter_neg
- \+/\- *lemma* finsupp.filter_smul
- \+/\- *def* finsupp.finsupp_prod_equiv
- \+/\- *lemma* finsupp.map_domain_comap_domain
- \+/\- *lemma* finsupp.map_domain_finset_sum
- \+/\- *lemma* finsupp.map_domain_smul
- \+/\- *lemma* finsupp.map_range_add
- \+/\- *lemma* finsupp.map_range_finset_sum
- \+/\- *lemma* finsupp.mem_support_finset_sum
- \+/\- *lemma* finsupp.mem_support_multiset_sum
- \+/\- *lemma* finsupp.mem_support_single
- \+/\- *def* finsupp.of_multiset
- \+/\- *lemma* finsupp.of_multiset_apply
- \+/\- *lemma* finsupp.prod_finset_sum_index
- \+/\- *lemma* finsupp.prod_map_range_index
- \+/\- *lemma* finsupp.prod_single
- \+/\- *def* finsupp.restrict_support_equiv
- \+/\- *lemma* finsupp.single_finset_sum
- \+/\- *lemma* finsupp.single_multiset_sum
- \+/\- *lemma* finsupp.single_sum
- \+/\- *lemma* finsupp.single_swap
- \+/\- *lemma* finsupp.smul_single
- \+/\- *def* finsupp.subtype_domain
- \+/\- *lemma* finsupp.sum_comap_domain
- \+/\- *lemma* finsupp.support_curry
- \+/\- *lemma* finsupp.support_eq_empty
- \+/\- *lemma* finsupp.support_subset_iff
- \+/\- *lemma* finsupp.to_multiset_strict_mono

Modified src/data/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.coeff_zero_X
- \+/\- *lemma* mv_polynomial.degrees_prod
- \+/\- *lemma* mv_polynomial.degrees_sum
- \+/\- *lemma* mv_polynomial.degrees_zero
- \+/\- *theorem* mv_polynomial.eval_assoc
- \+/\- *lemma* mv_polynomial.eval₂_assoc
- \+/\- *lemma* mv_polynomial.eval₂_cast_comp
- \+/\- *lemma* mv_polynomial.eval₂_hom_X
- \+/\- *lemma* mv_polynomial.eval₂_prod
- \+/\- *lemma* mv_polynomial.eval₂_sum
- \+/\- *lemma* mv_polynomial.map_eval₂
- \+/\- *theorem* mv_polynomial.map_map
- \+/\- *lemma* mv_polynomial.rename_sub

Modified src/data/polynomial.lean
- \+/\- *lemma* polynomial.coeff_C_zero
- \+/\- *lemma* polynomial.coeff_X
- \+/\- *lemma* polynomial.coeff_X_one
- \+/\- *lemma* polynomial.coeff_X_zero
- \+/\- *lemma* polynomial.coeff_one
- \+/\- *lemma* polynomial.coeff_one_zero
- \+/\- *lemma* polynomial.coeff_single
- \+/\- *lemma* polynomial.coeff_sum
- \+/\- *lemma* polynomial.degree_map'
- \+/\- *lemma* polynomial.degree_map_eq_of_injective
- \+/\- *lemma* polynomial.degree_map_eq_of_leading_coeff_ne_zero
- \+/\- *lemma* polynomial.degree_map_le
- \+/\- *lemma* polynomial.degree_sum_le
- \- *def* polynomial.div_mod_by_monic_aux
- \+/\- *lemma* polynomial.map_div_by_monic
- \+/\- *lemma* polynomial.map_map
- \+/\- *lemma* polynomial.map_mod_by_monic
- \+/\- *lemma* polynomial.map_mod_div_by_monic
- \+/\- *lemma* polynomial.map_neg
- \+/\- *lemma* polynomial.map_sub
- \+/\- *lemma* polynomial.monic_map
- \+/\- *lemma* polynomial.nat_degree_eq_of_degree_eq
- \+/\- *lemma* polynomial.nat_degree_map'
- \+ *def* polynomial.nth_roots
- \- *def* polynomial.rec_on_horner

Modified src/field_theory/mv_polynomial.lean


Modified src/field_theory/splitting_field.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finsupp.lean
- \+/\- *def* finsupp.lsum
- \+/\- *theorem* finsupp.lsum_apply
- \+/\- *theorem* finsupp.range_restrict_dom
- \+/\- *def* finsupp.restrict_dom
- \+/\- *theorem* finsupp.restrict_dom_apply
- \+/\- *theorem* finsupp.restrict_dom_comp_subtype
- \+/\- *lemma* finsupp.supported_eq_span_single
- \+/\- *def* finsupp.supported_equiv_finsupp

Modified src/linear_algebra/finsupp_vector_space.lean
- \+/\- *lemma* finsupp.is_basis_single
- \+/\- *lemma* finsupp.linear_independent_single

Modified src/linear_algebra/matrix.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/power_series.lean
- \+/\- *lemma* power_series.coeff_mk
- \+/\- *lemma* power_series.coeff_trunc
- \+ *lemma* power_series.inv_eq_inv_aux
- \+/\- *lemma* power_series.monomial_zero
- \+/\- *def* power_series.trunc
- \+/\- *lemma* power_series.trunc_C
- \+/\- *lemma* power_series.trunc_add
- \+/\- *lemma* power_series.trunc_one
- \+/\- *lemma* power_series.trunc_zero



## [2019-09-05 21:37:18](https://github.com/leanprover-community/mathlib/commit/1a0ed80)
fix(naming): typo [ci skip] ([#1401](https://github.com/leanprover-community/mathlib/pull/1401))
* fix(naming): typo [ci skip]
* more typos
#### Estimated changes
Modified docs/contribute/naming.md




## [2019-09-05 11:03:20](https://github.com/leanprover-community/mathlib/commit/b1920f5)
chore(algebra/ordered_field): add simp attributes to inv_pos' and others ([#1400](https://github.com/leanprover-community/mathlib/pull/1400))
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+/\- *lemma* inv_neg'
- \+/\- *lemma* inv_nonneg
- \+/\- *lemma* inv_nonpos
- \+/\- *lemma* inv_pos'



## [2019-09-05 09:22:42](https://github.com/leanprover-community/mathlib/commit/7f20843)
chore(order/filter): rephrase filter.has_le ([#1399](https://github.com/leanprover-community/mathlib/pull/1399))
The goal of this tiny refactor is to prevent `filter.sets` leaking when
proving a filter g is finer than another one f. We want the goal to be
`s ∈ f → s ∈ g` instead of the definitionaly equivalent
`s ∈ f.sets ∈ g.sets`
#### Estimated changes
Modified src/order/filter/basic.lean


Modified src/order/filter/lift.lean
- \+ *lemma* filter.mem_lift_iff

Modified src/topology/basic.lean




## [2019-09-05 02:48:09](https://github.com/leanprover-community/mathlib/commit/2854909)
feat(bounded_lattice/has_lt): add a `lt` relation independent from `l… ([#1366](https://github.com/leanprover-community/mathlib/pull/1366))
* feat(bounded_lattice/has_lt): add a `lt` relation independent from `le` for `has_top`
* use priority 10 instead of 0
#### Estimated changes
Modified src/algebra/ordered_group.lean


Modified src/order/bounded_lattice.lean
- \+ *theorem* with_top.none_le
- \+ *theorem* with_top.none_lt_some
- \+/\- *theorem* with_top.some_le_some
- \+/\- *theorem* with_top.some_lt_some



## [2019-09-05 00:46:57](https://github.com/leanprover-community/mathlib/commit/6292825)
feat(data/equiv/local_equiv): define local equivalences  ([#1359](https://github.com/leanprover-community/mathlib/pull/1359))
* feat(data/equiv/local_equiv): define local equivalences
* add doc
* add extensionality attribute
* sanity_check
#### Estimated changes
Added src/data/equiv/local_equiv.lean
- \+ *lemma* equiv.refl_to_local_equiv
- \+ *lemma* equiv.symm_to_local_equiv
- \+ *def* equiv.to_local_equiv
- \+ *lemma* equiv.to_local_equiv_inv_fun
- \+ *lemma* equiv.to_local_equiv_source
- \+ *lemma* equiv.to_local_equiv_target
- \+ *lemma* equiv.to_local_equiv_to_fun
- \+ *lemma* equiv.trans_to_local_equiv
- \+ *lemma* local_equiv.apply_eq_of_eq_on_source
- \+ *lemma* local_equiv.bij_on_source
- \+ *lemma* local_equiv.eq_of_eq_on_source_univ
- \+ *def* local_equiv.eq_on_source
- \+ *lemma* local_equiv.eq_on_source_preimage
- \+ *lemma* local_equiv.eq_on_source_refl
- \+ *lemma* local_equiv.eq_on_source_restr
- \+ *lemma* local_equiv.eq_on_source_symm
- \+ *lemma* local_equiv.eq_on_source_trans
- \+ *lemma* local_equiv.image_eq_target_inter_inv_preimage
- \+ *lemma* local_equiv.image_source_eq_target
- \+ *lemma* local_equiv.image_trans_source
- \+ *lemma* local_equiv.inv_apply_eq_of_eq_on_source
- \+ *lemma* local_equiv.inv_image_eq_source_inter_preimage
- \+ *lemma* local_equiv.inv_image_target_eq_source
- \+ *lemma* local_equiv.inv_image_trans_target
- \+ *def* local_equiv.of_set
- \+ *lemma* local_equiv.of_set_inv_fun
- \+ *lemma* local_equiv.of_set_source
- \+ *lemma* local_equiv.of_set_symm
- \+ *lemma* local_equiv.of_set_target
- \+ *lemma* local_equiv.of_set_to_fun
- \+ *def* local_equiv.prod
- \+ *lemma* local_equiv.prod_inv_fun
- \+ *lemma* local_equiv.prod_source
- \+ *lemma* local_equiv.prod_target
- \+ *lemma* local_equiv.prod_to_fun
- \+ *lemma* local_equiv.refl_inv_fun
- \+ *lemma* local_equiv.refl_restr_source
- \+ *lemma* local_equiv.refl_restr_target
- \+ *lemma* local_equiv.refl_source
- \+ *lemma* local_equiv.refl_symm
- \+ *lemma* local_equiv.refl_target
- \+ *lemma* local_equiv.refl_to_fun
- \+ *lemma* local_equiv.refl_trans
- \+ *lemma* local_equiv.restr_eq_of_source_subset
- \+ *lemma* local_equiv.restr_inv_fun
- \+ *lemma* local_equiv.restr_source
- \+ *lemma* local_equiv.restr_target
- \+ *lemma* local_equiv.restr_to_fun
- \+ *lemma* local_equiv.restr_trans
- \+ *lemma* local_equiv.restr_univ
- \+ *lemma* local_equiv.source_eq_of_eq_on_source
- \+ *lemma* local_equiv.source_inter_preimage_inv_preimage
- \+ *lemma* local_equiv.source_subset_preimage_target
- \+ *lemma* local_equiv.symm_inv_fun
- \+ *lemma* local_equiv.symm_source
- \+ *lemma* local_equiv.symm_symm
- \+ *lemma* local_equiv.symm_target
- \+ *lemma* local_equiv.symm_to_fun
- \+ *lemma* local_equiv.target_eq_of_eq_on_source
- \+ *lemma* local_equiv.target_inter_inv_preimage_preimage
- \+ *lemma* local_equiv.target_subset_preimage_source
- \+ *lemma* local_equiv.trans_apply
- \+ *lemma* local_equiv.trans_assoc
- \+ *lemma* local_equiv.trans_inv_apply
- \+ *lemma* local_equiv.trans_inv_fun
- \+ *lemma* local_equiv.trans_refl
- \+ *lemma* local_equiv.trans_refl_restr'
- \+ *lemma* local_equiv.trans_refl_restr
- \+ *lemma* local_equiv.trans_self_symm
- \+ *lemma* local_equiv.trans_source''
- \+ *lemma* local_equiv.trans_source'
- \+ *lemma* local_equiv.trans_source
- \+ *lemma* local_equiv.trans_symm_eq_symm_trans_symm
- \+ *lemma* local_equiv.trans_symm_self
- \+ *lemma* local_equiv.trans_target''
- \+ *lemma* local_equiv.trans_target'
- \+ *lemma* local_equiv.trans_target
- \+ *lemma* local_equiv.trans_to_fun



## [2019-09-04 22:48:55](https://github.com/leanprover-community/mathlib/commit/79a1f84)
fix(tactic/norm_num): bugfix bad proof application ([#1387](https://github.com/leanprover-community/mathlib/pull/1387))
* fix(tactic/norm_num): bugfix bad proof application
* add test case that used to fail
* add try_for
* fix typecheck test
* increase test timeout
#### Estimated changes
Modified src/tactic/norm_num.lean


Modified test/norm_num.lean




## [2019-09-04 20:52:45](https://github.com/leanprover-community/mathlib/commit/3c224f0)
feat (logic/basic): exists_eq' ([#1397](https://github.com/leanprover-community/mathlib/pull/1397))
Not a great name, but `exists_eq_left` and `exists_eq_right` are taken, and it's unlikely to be used except in `simp`
#### Estimated changes
Modified src/logic/basic.lean
- \+ *theorem* exists_eq'



## [2019-09-04 19:28:57](https://github.com/leanprover-community/mathlib/commit/65ffb7b)
fix(topology/uniform_space): simplify continuity proof ([#1396](https://github.com/leanprover-community/mathlib/pull/1396))
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* uniform_continuous.continuous
- \+/\- *lemma* uniform_continuous_iff



## [2019-09-04 17:22:01](https://github.com/leanprover-community/mathlib/commit/06cffeb)
feat(order): add lemma ([#1375](https://github.com/leanprover-community/mathlib/pull/1375))
#### Estimated changes
Modified src/algebra/order.lean
- \+ *lemma* decidable.min_le_max



## [2019-09-04 12:59:55](https://github.com/leanprover-community/mathlib/commit/5d59e8b)
feat(category_theory): finite products give a monoidal structure ([#1340](https://github.com/leanprover-community/mathlib/pull/1340))
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
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.lim.map_π
- \+/\- *lemma* category_theory.limits.limit.lift_π

Added src/category_theory/limits/shapes/constructions/finite_limits.lean


Added src/category_theory/limits/shapes/constructions/limits.lean


Added src/category_theory/monoidal/of_has_finite_products.lean
- \+ *def* category_theory.monoidal_of_has_finite_coproducts
- \+ *def* category_theory.monoidal_of_has_finite_products

Modified src/category_theory/monoidal/types.lean




## [2019-09-04 12:27:02](https://github.com/leanprover-community/mathlib/commit/8cd16b9)
feat(category_theory/sums): sums (disjoint unions) of categories ([#1357](https://github.com/leanprover-community/mathlib/pull/1357))
* feat(category_theory/sum): direct sums of categories
* minor
* tidying
* Fix white space, remove old comments
* rearranging, associator
* add TODO comment about unitors
* fix import
* create /basic.lean files
#### Estimated changes
Added src/category_theory/hom_functor.lean
- \+ *lemma* category_theory.functor.hom_obj
- \+ *lemma* category_theory.functor.hom_pairing_map

Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/opposites.lean
- \- *lemma* category_theory.functor.hom_obj
- \- *lemma* category_theory.functor.hom_pairing_map

Modified src/category_theory/products/associator.lean


Added src/category_theory/products/basic.lean
- \+ *def* category_theory.evaluation
- \+ *lemma* category_theory.evaluation_map_app
- \+ *lemma* category_theory.evaluation_obj_map
- \+ *lemma* category_theory.evaluation_obj_obj
- \+ *def* category_theory.evaluation_uncurried
- \+ *lemma* category_theory.evaluation_uncurried_map
- \+ *lemma* category_theory.evaluation_uncurried_obj
- \+ *def* category_theory.functor.prod
- \+ *lemma* category_theory.functor.prod_map
- \+ *lemma* category_theory.functor.prod_obj
- \+ *def* category_theory.nat_trans.prod
- \+ *lemma* category_theory.nat_trans.prod_app
- \+ *def* category_theory.prod.braiding
- \+ *def* category_theory.prod.fst
- \+ *lemma* category_theory.prod.fst_map
- \+ *lemma* category_theory.prod.fst_obj
- \+ *def* category_theory.prod.inl
- \+ *lemma* category_theory.prod.inl_map
- \+ *lemma* category_theory.prod.inl_obj
- \+ *def* category_theory.prod.inr
- \+ *lemma* category_theory.prod.inr_map
- \+ *lemma* category_theory.prod.inr_obj
- \+ *def* category_theory.prod.snd
- \+ *lemma* category_theory.prod.snd_map
- \+ *lemma* category_theory.prod.snd_obj
- \+ *def* category_theory.prod.swap
- \+ *lemma* category_theory.prod.swap_map
- \+ *lemma* category_theory.prod.swap_obj
- \+ *def* category_theory.prod.symmetry
- \+ *lemma* category_theory.prod_comp
- \+ *lemma* category_theory.prod_comp_fst
- \+ *lemma* category_theory.prod_comp_snd
- \+ *lemma* category_theory.prod_id
- \+ *lemma* category_theory.prod_id_fst
- \+ *lemma* category_theory.prod_id_snd

Modified src/category_theory/products/bifunctor.lean


Modified src/category_theory/products/default.lean
- \- *def* category_theory.evaluation
- \- *lemma* category_theory.evaluation_map_app
- \- *lemma* category_theory.evaluation_obj_map
- \- *lemma* category_theory.evaluation_obj_obj
- \- *def* category_theory.evaluation_uncurried
- \- *lemma* category_theory.evaluation_uncurried_map
- \- *lemma* category_theory.evaluation_uncurried_obj
- \- *def* category_theory.functor.prod
- \- *lemma* category_theory.functor.prod_map
- \- *lemma* category_theory.functor.prod_obj
- \- *def* category_theory.nat_trans.prod
- \- *lemma* category_theory.nat_trans.prod_app
- \- *def* category_theory.prod.fst
- \- *lemma* category_theory.prod.fst_map
- \- *lemma* category_theory.prod.fst_obj
- \- *def* category_theory.prod.inl
- \- *lemma* category_theory.prod.inl_map
- \- *lemma* category_theory.prod.inl_obj
- \- *def* category_theory.prod.inr
- \- *lemma* category_theory.prod.inr_map
- \- *lemma* category_theory.prod.inr_obj
- \- *def* category_theory.prod.snd
- \- *lemma* category_theory.prod.snd_map
- \- *lemma* category_theory.prod.snd_obj
- \- *def* category_theory.prod.swap
- \- *lemma* category_theory.prod.swap_map
- \- *lemma* category_theory.prod.swap_obj
- \- *def* category_theory.prod.symmetry
- \- *lemma* category_theory.prod_comp
- \- *lemma* category_theory.prod_comp_fst
- \- *lemma* category_theory.prod_comp_snd
- \- *lemma* category_theory.prod_id
- \- *lemma* category_theory.prod_id_fst
- \- *lemma* category_theory.prod_id_snd

Added src/category_theory/sums/associator.lean
- \+ *def* category_theory.sum.associativity
- \+ *def* category_theory.sum.associator
- \+ *lemma* category_theory.sum.associator_map_inl_inl
- \+ *lemma* category_theory.sum.associator_map_inl_inr
- \+ *lemma* category_theory.sum.associator_map_inr
- \+ *lemma* category_theory.sum.associator_obj_inl_inl
- \+ *lemma* category_theory.sum.associator_obj_inl_inr
- \+ *lemma* category_theory.sum.associator_obj_inr
- \+ *def* category_theory.sum.inverse_associator
- \+ *lemma* category_theory.sum.inverse_associator_map_inl
- \+ *lemma* category_theory.sum.inverse_associator_map_inr_inl
- \+ *lemma* category_theory.sum.inverse_associator_map_inr_inr
- \+ *lemma* category_theory.sum.inverse_associator_obj_inl
- \+ *lemma* category_theory.sum.inverse_associator_obj_inr_inl
- \+ *lemma* category_theory.sum.inverse_associator_obj_inr_inr

Added src/category_theory/sums/basic.lean
- \+ *def* category_theory.functor.sum
- \+ *lemma* category_theory.functor.sum_map_inl
- \+ *lemma* category_theory.functor.sum_map_inr
- \+ *lemma* category_theory.functor.sum_obj_inl
- \+ *lemma* category_theory.functor.sum_obj_inr
- \+ *def* category_theory.nat_trans.sum
- \+ *lemma* category_theory.nat_trans.sum_app_inl
- \+ *lemma* category_theory.nat_trans.sum_app_inr
- \+ *def* category_theory.sum.inl_
- \+ *lemma* category_theory.sum.inl_map
- \+ *lemma* category_theory.sum.inl_obj
- \+ *def* category_theory.sum.inr_
- \+ *lemma* category_theory.sum.inr_map
- \+ *lemma* category_theory.sum.inr_obj
- \+ *def* category_theory.sum.swap.equivalence
- \+ *def* category_theory.sum.swap.symmetry
- \+ *def* category_theory.sum.swap
- \+ *lemma* category_theory.sum.swap_map_inl
- \+ *lemma* category_theory.sum.swap_map_inr
- \+ *lemma* category_theory.sum.swap_obj_inl
- \+ *lemma* category_theory.sum.swap_obj_inr
- \+ *lemma* category_theory.sum_comp_inl
- \+ *lemma* category_theory.sum_comp_inr

Added src/category_theory/sums/default.lean


Modified src/category_theory/yoneda.lean




## [2019-09-04 06:33:49](https://github.com/leanprover-community/mathlib/commit/b079298)
feat(tactic/doc_blame): Use is_auto_generated ([#1395](https://github.com/leanprover-community/mathlib/pull/1395))
#### Estimated changes
Modified src/tactic/doc_blame.lean
- \- *def* name.is_not_auto



## [2019-09-03 21:08:11](https://github.com/leanprover-community/mathlib/commit/ff47fa3)
feat(measure_theory): prove that the Giry monad is a monad in the category_theory sense ([#1259](https://github.com/leanprover-community/mathlib/pull/1259))
* feat(measure_theory): prove that the Giry monad is a monad in the category_theory sense
* Add spaces to fix alignment
* document Measure
* Add documentation
* Add space before colon
#### Estimated changes
Modified src/measure_theory/Meas.lean
- \+ *def* Meas.Integral
- \+ *def* Meas.Measure

Modified src/measure_theory/giry_monad.lean
- \+ *lemma* measure_theory.measure.join_dirac
- \+ *lemma* measure_theory.measure.join_eq_bind
- \+ *lemma* measure_theory.measure.join_map_dirac
- \+ *lemma* measure_theory.measure.join_map_join
- \+ *lemma* measure_theory.measure.join_map_map
- \+ *lemma* measure_theory.measure.map_dirac

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_pi_apply
- \+ *lemma* measurable_pi_lambda



## [2019-09-03 18:22:38](https://github.com/leanprover-community/mathlib/commit/b5b40c7)
chore(*): use localized command in mathlib ([#1319](https://github.com/leanprover-community/mathlib/pull/1319))
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
#### Estimated changes
Modified .gitignore


Modified docs/tactics.md


Modified src/algebra/CommRing/adjunctions.lean


Modified src/algebra/archimedean.lean


Modified src/algebra/direct_limit.lean


Modified src/algebra/group_power.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/convex.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/specific_limits.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/computability/turing_machine.lean


Modified src/data/complex/exponential.lean


Modified src/data/list/basic.lean


Modified src/data/matrix/basic.lean


Modified src/data/matrix/pequiv.lean


Modified src/data/multiset.lean


Modified src/data/nat/totient.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/pfun.lean


Modified src/data/polynomial.lean


Modified src/data/rat/basic.lean


Modified src/data/rat/cast.lean


Modified src/data/rat/order.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/hyperreal.lean


Modified src/data/real/nnreal.lean


Modified src/data/set/countable.lean


Modified src/data/set/disjointed.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/field_theory/splitting_field.lean


Modified src/group_theory/coset.lean


Modified src/group_theory/order_of_element.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/logic/function.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/integration.lean
- \+/\- *theorem* measure_theory.simple_func.range_map

Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/probability_mass_function.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/number_theory/dioph.lean


Modified src/order/basic.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/filter_product.lean


Modified src/order/filter/lift.lean


Modified src/order/filter/pointwise.lean


Modified src/order/zorn.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/ideals.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/ordinal_notation.lean


Modified src/set_theory/schroeder_bernstein.lean


Modified src/tactic/basic.lean


Modified src/tactic/default.lean


Modified src/tactic/finish.lean


Modified src/tactic/localized.lean


Modified src/tactic/omega/coeffs.lean


Modified src/tactic/omega/eq_elim.lean


Modified src/tactic/omega/int/dnf.lean


Modified src/tactic/omega/int/form.lean


Modified src/tactic/omega/int/main.lean


Modified src/tactic/omega/int/preterm.lean


Modified src/tactic/omega/misc.lean


Modified src/tactic/omega/nat/dnf.lean


Modified src/tactic/omega/nat/form.lean


Modified src/tactic/omega/nat/main.lean


Modified src/tactic/omega/nat/neg_elim.lean


Modified src/tactic/omega/nat/preterm.lean


Modified src/tactic/omega/nat/sub_elim.lean


Modified src/tactic/push_neg.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/basic.lean


Modified src/topology/constructions.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/maps.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/order.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/pi.lean


Modified src/topology/uniform_space/separation.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2019-09-03 17:52:30](https://github.com/leanprover-community/mathlib/commit/4b6fcd9)
perf(data/gaussian_int): speed up div and mod ([#1394](https://github.com/leanprover-community/mathlib/pull/1394))
avoid using `int.cast`, and use `rat.of_int`.
This sped up `#eval (⟨1414,152⟩ : gaussian_int) % ⟨123,456⟩` from about 5 seconds to 2 milliseconds
#### Estimated changes
Modified src/data/zsqrtd/gaussian_int.lean




## [2019-09-03 17:20:07](https://github.com/leanprover-community/mathlib/commit/974d413)
chore(linear_algebra/determinant): simplify det_mul proof ([#1392](https://github.com/leanprover-community/mathlib/pull/1392))
* chore(linear_algebra/determinant): simplify det_mul proof
Minor improvement to the proof of `det_mul`
* make det_mul_aux more readable
#### Estimated changes
Modified src/linear_algebra/determinant.lean




## [2019-09-03 15:36:36](https://github.com/leanprover-community/mathlib/commit/3a58b50)
feat(data/equiv/basic): add more functions for equivalences between complex types ([#1384](https://github.com/leanprover-community/mathlib/pull/1384))
* Add more `equiv` combinators
* Fix compile
* Minor fixes
* Update src/data/equiv/basic.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
#### Estimated changes
Modified src/data/equiv/basic.lean
- \- *def* equiv.equiv_fib
- \- *def* equiv.equiv_sigma_subtype
- \+ *def* equiv.sigma_preimage_equiv
- \+ *def* equiv.sigma_subtype_equiv_of_subset
- \+ *def* equiv.sigma_subtype_preimage_equiv
- \+ *def* equiv.sigma_subtype_preimage_equiv_subtype
- \+/\- *def* equiv.subtype_subtype_equiv_subtype
- \+ *def* equiv.subtype_subtype_equiv_subtype_exists
- \+ *def* equiv.subtype_subtype_equiv_subtype_inter
- \+ *def* equiv.subtype_univ_equiv

Modified src/group_theory/coset.lean


Modified src/group_theory/sylow.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/cofinality.lean




## [2019-09-03 13:42:57](https://github.com/leanprover-community/mathlib/commit/a199f85)
feat(topology/uniform_space): Abstract completions ([#1374](https://github.com/leanprover-community/mathlib/pull/1374))
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
#### Estimated changes
Modified src/topology/algebra/group_completion.lean
- \- *lemma* uniform_space.completion.is_add_group_hom_prod

Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/maps.lean
- \+ *lemma* dense_range.nonempty

Added src/topology/uniform_space/absolute_value.lean
- \+ *theorem* is_absolute_value.mem_uniformity
- \+ *def* is_absolute_value.uniform_space
- \+ *def* is_absolute_value.uniform_space_core

Added src/topology/uniform_space/abstract_completion.lean
- \+ *def* abstract_completion.compare
- \+ *lemma* abstract_completion.compare_coe
- \+ *def* abstract_completion.compare_equiv
- \+ *lemma* abstract_completion.continuous_coe
- \+ *lemma* abstract_completion.continuous_extend
- \+ *lemma* abstract_completion.continuous_map
- \+ *lemma* abstract_completion.continuous_map₂
- \+ *lemma* abstract_completion.dense'
- \+ *lemma* abstract_completion.dense_inducing
- \+ *lemma* abstract_completion.extend_coe
- \+ *lemma* abstract_completion.extend_comp_coe
- \+ *lemma* abstract_completion.extend_def
- \+ *lemma* abstract_completion.extend_map
- \+ *lemma* abstract_completion.extend_unique
- \+ *lemma* abstract_completion.extension₂_coe_coe
- \+ *lemma* abstract_completion.induction_on
- \+ *lemma* abstract_completion.inverse_compare
- \+ *lemma* abstract_completion.map_coe
- \+ *lemma* abstract_completion.map_comp
- \+ *lemma* abstract_completion.map_id
- \+ *lemma* abstract_completion.map_unique
- \+ *lemma* abstract_completion.map₂_coe_coe
- \+ *lemma* abstract_completion.uniform_continuous_coe
- \+ *lemma* abstract_completion.uniform_continuous_compare
- \+ *lemma* abstract_completion.uniform_continuous_compare_equiv
- \+ *lemma* abstract_completion.uniform_continuous_compare_equiv_symm
- \+ *lemma* abstract_completion.uniform_continuous_extend
- \+ *lemma* abstract_completion.uniform_continuous_extension₂
- \+ *lemma* abstract_completion.uniform_continuous_map
- \+ *lemma* abstract_completion.uniform_continuous_map₂

Added src/topology/uniform_space/compare_reals.lean
- \+ *def* compare_reals.Bourbaki_pkg
- \+ *def* compare_reals.Bourbakiℝ
- \+ *def* compare_reals.Q
- \+ *lemma* compare_reals.compare_uc
- \+ *lemma* compare_reals.compare_uc_symm
- \+ *lemma* rat.uniform_space_eq
- \+ *def* rational_cau_seq_pkg

Modified src/topology/uniform_space/completion.lean
- \+ *def* uniform_space.completion.cpkg
- \- *lemma* uniform_space.completion.prod_coe_coe
- \- *lemma* uniform_space.completion.uniform_continuous_prod



## [2019-09-03 11:51:43](https://github.com/leanprover-community/mathlib/commit/c7d3629)
fix(restate_axiom): create lemmas from lemmas ([#1390](https://github.com/leanprover-community/mathlib/pull/1390))
#### Estimated changes
Modified src/tactic/restate_axiom.lean




## [2019-09-03 09:24:11+02:00](https://github.com/leanprover-community/mathlib/commit/94205c4)
feat(data/fintype): prove `card (subtype p) ≤ card α` ([#1383](https://github.com/leanprover-community/mathlib/pull/1383))
* feat(data/fintype): prove `card (subtype p) ≤ card α`
* Add `cardinal.mk_le_of_subtype`
* Rename `mk_le_of_subtype` to `mk_subtype_le`, use it in `mk_set_le`
Earlier both `mk_subtype_le` and `mk_set_le` took `set α` as an
argument. Now `mk_subtype_le` takes `α → Prop`.
#### Estimated changes
Modified src/data/fintype.lean
- \+ *theorem* fintype.card_subtype_le

Modified src/data/real/cardinality.lean


Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.mk_subtype_le
- \+ *theorem* cardinal.mk_subtype_le_of_subset



## [2019-09-02 14:19:49](https://github.com/leanprover-community/mathlib/commit/227b682)
feat(category_theory): define `iso.conj` and friends ([#1381](https://github.com/leanprover-community/mathlib/pull/1381))
* feat(category_theory): define `iso.conj` and friends
* Drop 2 `@[simp]` attributes
#### Estimated changes
Added src/category_theory/conj.lean
- \+ *lemma* category_theory.functor.map_conj
- \+ *lemma* category_theory.functor.map_conj_Aut
- \+ *lemma* category_theory.functor.map_hom_congr
- \+ *def* category_theory.iso.conj
- \+ *def* category_theory.iso.conj_Aut
- \+ *lemma* category_theory.iso.conj_Aut_apply
- \+ *lemma* category_theory.iso.conj_Aut_gpow
- \+ *lemma* category_theory.iso.conj_Aut_hom
- \+ *lemma* category_theory.iso.conj_Aut_mul
- \+ *lemma* category_theory.iso.conj_Aut_pow
- \+ *lemma* category_theory.iso.conj_Aut_trans
- \+ *lemma* category_theory.iso.conj_apply
- \+ *lemma* category_theory.iso.conj_comp
- \+ *lemma* category_theory.iso.conj_id
- \+ *lemma* category_theory.iso.conj_pow
- \+ *def* category_theory.iso.hom_congr
- \+ *lemma* category_theory.iso.hom_congr_apply
- \+ *lemma* category_theory.iso.hom_congr_comp
- \+ *lemma* category_theory.iso.hom_congr_refl
- \+ *lemma* category_theory.iso.hom_congr_symm
- \+ *lemma* category_theory.iso.hom_congr_trans
- \+ *lemma* category_theory.iso.refl_conj
- \+ *lemma* category_theory.iso.self_symm_conj
- \+ *lemma* category_theory.iso.symm_self_conj
- \+ *lemma* category_theory.iso.trans_conj
- \+ *lemma* category_theory.iso.trans_conj_Aut



## [2019-09-02 12:18:38](https://github.com/leanprover-community/mathlib/commit/57d4b41)
feat(category_theory/limits): construct limits from products and equalizers ([#1362](https://github.com/leanprover-community/mathlib/pull/1362))
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
#### Estimated changes
Modified src/category_theory/const.lean
- \+ *lemma* category_theory.functor.const.unop_functor_op_obj_map

Modified src/category_theory/limits/cones.lean
- \+ *def* category_theory.limits.cocone.equiv
- \+ *def* category_theory.limits.cone.equiv

Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.has_colimit.of_cocones_iso
- \+ *def* category_theory.limits.has_limit.of_cones_iso

Modified src/category_theory/limits/shapes/binary_products.lean


Added src/category_theory/limits/shapes/constructions/finite_products.lean


Added src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean
- \+ *def* category_theory.limits.equalizer_diagram.cones_hom
- \+ *def* category_theory.limits.equalizer_diagram.cones_inv
- \+ *def* category_theory.limits.equalizer_diagram.cones_iso
- \+ *def* category_theory.limits.equalizer_diagram
- \+ *def* category_theory.limits.limits_from_equalizers_and_products

Added src/category_theory/limits/shapes/constructions/pullbacks.lean


Added src/category_theory/limits/shapes/constructions/sums.lean




## [2019-09-02 07:54:36](https://github.com/leanprover-community/mathlib/commit/fe7695b)
chore(data/nat/gcd): remove pointless parentheses ([#1386](https://github.com/leanprover-community/mathlib/pull/1386))
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+/\- *theorem* nat.gcd_eq_right_iff_dvd



## [2019-09-02 06:00:19](https://github.com/leanprover-community/mathlib/commit/d35dc13)
feat(data/nat/gcd): add simple lemmas ([#1382](https://github.com/leanprover-community/mathlib/pull/1382))
* feat(data/nat/gcd): more simple lemmas
* Prove `iff` instead of one side implication
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+ *lemma* nat.coprime.gcd_both
- \+ *lemma* nat.coprime.gcd_left
- \+ *theorem* nat.coprime.gcd_mul
- \+ *lemma* nat.coprime.gcd_right
- \- *theorem* nat.exists_eq_prod_and_dvd_and_dvd
- \+ *theorem* nat.gcd_eq_left_iff_dvd
- \+ *theorem* nat.gcd_eq_right_iff_dvd
- \+ *theorem* nat.gcd_le_left
- \+ *theorem* nat.gcd_le_right
- \+ *theorem* nat.gcd_mul_dvd_mul_gcd
- \+ *def* nat.prod_dvd_and_dvd_of_dvd_prod



## [2019-09-01 11:29:41](https://github.com/leanprover-community/mathlib/commit/6d2b3ed)
chore(category_theory/notation): consistently use notation for functor.id ([#1378](https://github.com/leanprover-community/mathlib/pull/1378))
* chore(category_theory/notation): consistently use notation for functor.id
* oops, overzealous search-and-replace
* more
* more
* more
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \+/\- *def* category_theory.adjunction.id

Modified src/category_theory/comma.lean
- \+/\- *def* category_theory.comma.map_left_id
- \+/\- *def* category_theory.comma.map_right_id
- \+/\- *def* category_theory.over
- \+/\- *def* category_theory.under

Modified src/category_theory/equivalence.lean
- \+/\- *def* category_theory.functor.fun_inv_id
- \+/\- *def* category_theory.functor.inv_fun_id

Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean
- \+/\- *lemma* category_theory.functor.id_map
- \+/\- *lemma* category_theory.functor.id_obj

Modified src/category_theory/limits/cones.lean
- \+/\- *def* category_theory.limits.cocones.precompose_id
- \+/\- *def* category_theory.limits.cones.postcompose_id

Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/monad/adjunction.lean
- \+/\- *lemma* category_theory.adjunction.monad_η_app
- \+/\- *lemma* category_theory.adjunction.monad_μ_app
- \+/\- *lemma* category_theory.monad.comparison_map_f
- \+/\- *lemma* category_theory.monad.comparison_obj_a

Modified src/category_theory/monad/basic.lean


Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/natural_isomorphism.lean
- \+/\- *def* category_theory.functor.ulift_down_up
- \+/\- *def* category_theory.functor.ulift_up_down

Modified src/category_theory/products/default.lean
- \+/\- *def* category_theory.prod.symmetry

Modified src/category_theory/whiskering.lean
- \+/\- *def* category_theory.functor.left_unitor
- \+/\- *def* category_theory.functor.right_unitor

Modified src/category_theory/yoneda.lean


Modified src/topology/Top/opens.lean
- \+/\- *def* topological_space.opens.map_id

