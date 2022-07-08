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
modified src/field_theory/finite_card.lean

modified src/linear_algebra/basic.lean
- \+/\- *lemma* std_basis_eq_single
- \+/\- *lemma* std_basis_eq_single

modified src/linear_algebra/basis.lean
- \+/\- *lemma* constr_smul
- \+/\- *lemma* is_basis_singleton_one
- \+/\- *lemma* linear_independent_std_basis
- \+/\- *lemma* is_basis_std_basis
- \+/\- *lemma* constr_smul
- \+/\- *lemma* is_basis_singleton_one
- \+/\- *lemma* linear_independent_std_basis
- \+/\- *lemma* is_basis_std_basis

modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_span
- \+/\- *lemma* dim_span_set
- \+/\- *lemma* exists_is_basis_fintype
- \+/\- *lemma* dim_span
- \+/\- *lemma* dim_span_set
- \+/\- *lemma* exists_is_basis_fintype
- \+/\- *theorem* is_basis.le_span
- \+/\- *theorem* mk_eq_mk_of_basis
- \+/\- *theorem* is_basis.mk_range_eq_dim
- \+/\- *theorem* is_basis.mk_eq_dim
- \+/\- *theorem* dim_quotient
- \+/\- *theorem* linear_equiv.dim_eq_lift
- \+/\- *theorem* is_basis.le_span
- \+/\- *theorem* mk_eq_mk_of_basis
- \+/\- *theorem* is_basis.mk_range_eq_dim
- \+/\- *theorem* is_basis.mk_eq_dim
- \+/\- *theorem* dim_quotient
- \+/\- *theorem* linear_equiv.dim_eq_lift

modified src/linear_algebra/dual.lean

modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* of_fg
- \+/\- *lemma* card_eq_findim
- \+/\- *lemma* of_fg
- \+/\- *lemma* card_eq_findim

modified src/linear_algebra/finsupp_vector_space.lean

modified src/linear_algebra/matrix.lean
- \+/\- *lemma* to_matrix_to_lin
- \+/\- *lemma* rank_diagonal
- \+/\- *lemma* to_matrix_to_lin
- \+/\- *lemma* rank_diagonal
- \+/\- *def* lin_equiv_matrix'
- \+/\- *def* lin_equiv_matrix
- \+/\- *def* lin_equiv_matrix'
- \+/\- *def* lin_equiv_matrix

modified src/ring_theory/noetherian.lean



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
modified src/ring_theory/ideal_operations.lean
- \+ *lemma* mem_ker
- \+ *lemma* not_one_mem_ker
- \+ *lemma* ker_is_prime

modified src/ring_theory/power_series.lean
- \+/\- *lemma* ext
- \+ *lemma* coeff_comp_monomial
- \+/\- *lemma* coeff_zero
- \+/\- *lemma* coeff_one
- \+ *lemma* coeff_zero_one
- \+/\- *lemma* coeff_mul
- \+ *lemma* monomial_mul_monomial
- \+ *lemma* monomial_zero_eq_C
- \+ *lemma* monomial_zero_eq_C_apply
- \+/\- *lemma* coeff_C
- \+ *lemma* coeff_zero_C
- \+/\- *lemma* coeff_X
- \+ *lemma* coeff_index_single_X
- \+ *lemma* coeff_index_single_self_X
- \+ *lemma* coeff_zero_X
- \+ *lemma* X_def
- \+ *lemma* X_pow_eq
- \+ *lemma* coeff_X_pow
- \+ *lemma* coeff_zero_eq_constant_coeff
- \+ *lemma* coeff_zero_eq_constant_coeff_apply
- \+ *lemma* constant_coeff_C
- \+ *lemma* constant_coeff_comp_C
- \+ *lemma* constant_coeff_zero
- \+ *lemma* constant_coeff_one
- \+ *lemma* constant_coeff_X
- \+ *lemma* is_unit_constant_coeff
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp
- \+/\- *lemma* coeff_map
- \+ *lemma* constant_coeff_map
- \+/\- *lemma* coeff_trunc
- \+/\- *lemma* trunc_one
- \+/\- *lemma* trunc_C
- \+ *lemma* X_pow_dvd_iff
- \+ *lemma* X_dvd_iff
- \+ *lemma* constant_coeff_inv_of_unit
- \+/\- *lemma* mul_inv_of_unit
- \+ *lemma* X_inj
- \+/\- *lemma* coeff_inv
- \+ *lemma* constant_coeff_inv
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* inv_of_unit_eq'
- \+ *lemma* coeff_coe
- \+ *lemma* coe_monomial
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* coe_add
- \+ *lemma* coe_mul
- \+ *lemma* coe_C
- \+ *lemma* coe_X
- \+ *lemma* coeff_def
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coeff_mk
- \+/\- *lemma* coeff_monomial
- \+/\- *lemma* monomial_eq_mk
- \+/\- *lemma* coeff_monomial'
- \+ *lemma* coeff_comp_monomial
- \+ *lemma* coeff_zero_eq_constant_coeff
- \+ *lemma* coeff_zero_eq_constant_coeff_apply
- \+ *lemma* monomial_zero_eq_C
- \+ *lemma* monomial_zero_eq_C_apply
- \+ *lemma* coeff_zero_C
- \+ *lemma* X_eq
- \+ *lemma* coeff_zero_X
- \+ *lemma* coeff_one_X
- \+ *lemma* X_pow_eq
- \+ *lemma* coeff_X_pow
- \+ *lemma* coeff_X_pow_self
- \+ *lemma* coeff_zero_one
- \+ *lemma* constant_coeff_C
- \+ *lemma* constant_coeff_comp_C
- \+ *lemma* constant_coeff_zero
- \+ *lemma* constant_coeff_one
- \+ *lemma* constant_coeff_X
- \+ *lemma* is_unit_constant_coeff
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp
- \+ *lemma* X_pow_dvd_iff
- \+ *lemma* X_dvd_iff
- \+/\- *lemma* trunc_C
- \+ *lemma* constant_coeff_inv_of_unit
- \+/\- *lemma* mul_inv_of_unit
- \+ *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *lemma* span_X_is_prime
- \+ *lemma* X_prime
- \+ *lemma* constant_coeff_inv
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* inv_of_unit_eq'
- \+ *lemma* order_finite_of_coeff_ne_zero
- \+ *lemma* coeff_order
- \+ *lemma* order_le
- \+ *lemma* coeff_of_lt_order
- \+ *lemma* order_eq_top
- \+ *lemma* order_zero
- \+ *lemma* order_ge_nat
- \+ *lemma* order_ge
- \+ *lemma* order_eq_nat
- \+ *lemma* order_eq
- \+ *lemma* order_add_ge
- \+ *lemma* order_add_of_order_eq
- \+ *lemma* order_mul_ge
- \+ *lemma* order_monomial
- \+ *lemma* order_monomial_of_ne_zero
- \+ *lemma* order_one
- \+ *lemma* order_X
- \+ *lemma* order_X_pow
- \+ *lemma* order_mul
- \+ *lemma* coeff_coe
- \+ *lemma* coe_monomial
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* coe_add
- \+ *lemma* coe_mul
- \+ *lemma* coe_C
- \+ *lemma* coe_X
- \+/\- *lemma* ext
- \+/\- *lemma* coeff_C
- \- *lemma* coeff_C_zero
- \- *lemma* monomial_zero
- \+/\- *lemma* coeff_X
- \- *lemma* coeff_X'
- \- *lemma* coeff_X''
- \+/\- *lemma* coeff_zero
- \- *lemma* C_zero
- \+/\- *lemma* coeff_one
- \- *lemma* coeff_one_zero
- \- *lemma* C_one
- \- *lemma* coeff_add
- \- *lemma* monomial_add
- \- *lemma* C_add
- \+/\- *lemma* coeff_mul
- \- *lemma* C_mul
- \- *lemma* is_unit_coeff_zero
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp
- \+/\- *lemma* coeff_map
- \- *lemma* map_zero
- \- *lemma* map_one
- \- *lemma* map_add
- \- *lemma* map_mul
- \+/\- *lemma* coeff_trunc
- \- *lemma* trunc_zero
- \+/\- *lemma* trunc_one
- \+/\- *lemma* trunc_C
- \- *lemma* trunc_add
- \- *lemma* coeff_neg
- \- *lemma* coeff_zero_inv_of_unit
- \+/\- *lemma* mul_inv_of_unit
- \+/\- *lemma* coeff_inv
- \- *lemma* coeff_zero_inv
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* inv_of_unit_eq'
- \- *lemma* to_mv_power_series_coeff
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coeff_mk
- \+/\- *lemma* coeff_monomial
- \+/\- *lemma* monomial_eq_mk
- \+/\- *lemma* coeff_monomial'
- \- *lemma* monomial_zero
- \- *lemma* coeff_C_zero
- \- *lemma* coeff_X'
- \+/\- *lemma* coeff_zero
- \- *lemma* C_zero
- \- *lemma* coeff_one_zero
- \- *lemma* C_one
- \- *lemma* coeff_add
- \- *lemma* monomial_add
- \- *lemma* C_add
- \- *lemma* C_mul
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp
- \- *lemma* map_zero
- \- *lemma* map_one
- \- *lemma* map_add
- \- *lemma* map_mul
- \+/\- *lemma* trunc_C
- \- *lemma* coeff_zero_inv_of_unit
- \+/\- *lemma* mul_inv_of_unit
- \- *lemma* coeff_zero_inv
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* inv_of_unit_eq'
- \- *lemma* to_power_series_coeff
- \+/\- *def* monomial
- \+/\- *def* coeff
- \+/\- *def* C
- \+/\- *def* X
- \+ *def* constant_coeff
- \+/\- *def* map
- \+ *def* trunc_fun
- \+/\- *def* trunc
- \+/\- *def* coeff
- \+/\- *def* monomial
- \+ *def* constant_coeff
- \+/\- *def* C
- \+/\- *def* map
- \+ *def* order
- \+/\- *def* monomial
- \+/\- *def* coeff
- \+/\- *def* monomial
- \+/\- *def* C
- \+/\- *def* X
- \+/\- *def* map
- \+/\- *def* trunc
- \- *def* to_mv_power_series
- \+/\- *def* coeff
- \+/\- *def* monomial
- \+/\- *def* C
- \+/\- *def* map
- \- *def* to_power_series



## [2019-09-28 22:44:16](https://github.com/leanprover-community/mathlib/commit/30aa8d2)
chore(order/basic): rename `monotone_comp` to `monotone.comp`, reorder arguments ([#1497](https://github.com/leanprover-community/mathlib/pull/1497))
#### Estimated changes
modified src/order/basic.lean
- \- *theorem* monotone_comp

modified src/order/filter/lift.lean

modified src/order/fixed_points.lean

modified src/topology/uniform_space/basic.lean

modified src/topology/uniform_space/cauchy.lean

modified src/topology/uniform_space/completion.lean



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
created src/geometry/manifold/manifold.lean
- \+ *lemma* mem_groupoid_of_pregroupoid
- \+ *lemma* groupoid_of_pregroupoid_le
- \+ *lemma* model_space_atlas
- \+ *lemma* chart_at_model_space_eq
- \+ *lemma* open_source'
- \+ *lemma* open_target
- \+ *lemma* has_groupoid_of_le
- \+ *def* id_groupoid
- \+ *def* groupoid_of_pregroupoid
- \+ *def* continuous_groupoid
- \+ *def* local_homeomorph
- \+ *def* to_manifold
- \+ *def* structomorph.refl
- \+ *def* structomorph.symm
- \+ *def* structomorph.trans



## [2019-09-27 18:10:21](https://github.com/leanprover-community/mathlib/commit/e0c204e)
chore(algebra/group_power): move inv_one from group_power to field ([#1495](https://github.com/leanprover-community/mathlib/pull/1495))
* chore(algebra/group_power): move inv_one from group_power to field
*  fix
#### Estimated changes
modified src/algebra/field.lean
- \+ *theorem* inv_one

modified src/algebra/group_power.lean
- \- *theorem* inv_one



## [2019-09-27 16:05:10](https://github.com/leanprover-community/mathlib/commit/74f09d0)
chore(algebra/char_p): remove some decidable_eq assumptions ([#1492](https://github.com/leanprover-community/mathlib/pull/1492))
* chore(algebra/char_p): remove some decidable_eq assumptions
*  fix build
#### Estimated changes
modified src/algebra/char_p.lean
- \+/\- *theorem* char_ne_zero_of_fintype
- \+/\- *theorem* char_is_prime
- \+/\- *theorem* char_ne_zero_of_fintype
- \+/\- *theorem* char_is_prime

modified src/data/set/finite.lean
- \+/\- *lemma* not_injective_nat_fintype
- \+/\- *lemma* not_injective_int_fintype
- \+/\- *lemma* not_injective_nat_fintype
- \+/\- *lemma* not_injective_int_fintype



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
modified docs/tactics.md

modified src/meta/expr.lean

modified src/tactic/basic.lean

modified src/tactic/core.lean

modified src/tactic/default.lean

created src/tactic/simps.lean

created test/simps.lean
- \+ *def* foo
- \+ *def* bar1
- \+ *def* bar2
- \+ *def* my_equiv
- \+ *def* baz
- \+ *def* name_clash_fst
- \+ *def* name_clash_snd
- \+ *def* name_clash_snd_2
- \+ *def* name_clash
- \+ *def* nested1
- \+ *def* nested2
- \+ *def* bar
- \+ *def* refl_with_data
- \+ *def* refl_with_data'
- \+ *def* test
- \+ *def* partially_applied_term
- \+ *def* very_partially_applied_term

modified test/tactics.lean
- \+ *def* eta_expansion_test
- \+ *def* eta_expansion_test2
- \+ *def* dummy
- \+ *def* wrong_param
- \+ *def* right_param



## [2019-09-27 11:47:32](https://github.com/leanprover-community/mathlib/commit/efd5ab2)
feat(logic/function): define `function.involutive` ([#1474](https://github.com/leanprover-community/mathlib/pull/1474))
* feat(logic/function): define `function.involutive`
* Prove that `inv`, `neg`, and `complex.conj` are involutive.
* Move `inv_inv'` to `algebra/field`
#### Estimated changes
modified src/algebra/field.lean
- \+ *lemma* inv_involutive'
- \+ *theorem* inv_inv'

modified src/algebra/group/basic.lean
- \+ *lemma* inv_involutive

modified src/algebra/group_power.lean
- \- *theorem* inv_inv'

modified src/analysis/complex/polynomial.lean

modified src/data/complex/basic.lean
- \+ *lemma* conj_involutive
- \+/\- *lemma* conj_bijective
- \+/\- *lemma* conj_bijective

modified src/data/equiv/basic.lean
- \+ *def* function.involutive.to_equiv

modified src/data/real/hyperreal.lean
- \+/\- *lemma* inv_epsilon_eq_omega
- \+/\- *lemma* inv_epsilon_eq_omega

modified src/data/real/nnreal.lean
- \+/\- *lemma* inv_inv
- \+/\- *lemma* inv_inv

modified src/logic/function.lean
- \+ *lemma* involutive_iff_iter_2_eq_id
- \+ *def* involutive



## [2019-09-27 09:36:44](https://github.com/leanprover-community/mathlib/commit/6a79f8a)
feat(data/int/basic): to_nat lemmas ([#1479](https://github.com/leanprover-community/mathlib/pull/1479))
* feat(data/int/basic): of_nat lemmas
* Adding lt_of_to_nat_lt
* reversing sides of <->
#### Estimated changes
modified src/data/int/basic.lean
- \+/\- *theorem* to_nat_le
- \+ *theorem* lt_to_nat
- \+ *theorem* to_nat_lt_to_nat
- \+ *theorem* lt_of_to_nat_lt
- \+/\- *theorem* to_nat_le



## [2019-09-27 07:02:36](https://github.com/leanprover-community/mathlib/commit/0bc5de5)
chore(*): drop some unused args reported by `#sanity_check_mathlib` ([#1490](https://github.com/leanprover-community/mathlib/pull/1490))
* Drop some unused arguments
* Drop more unused arguments
* Move `round` to the bottom of `algebra/archimedean`
Suggested by @rwbarton
#### Estimated changes
modified src/algebra/archimedean.lean
- \+/\- *theorem* exists_nat_one_div_lt
- \+/\- *theorem* exists_rat_near
- \+/\- *theorem* rat.cast_round
- \+/\- *theorem* exists_nat_one_div_lt
- \+/\- *theorem* exists_rat_near
- \+/\- *theorem* rat.cast_round
- \+/\- *def* round
- \+/\- *def* round

modified src/algebra/associated.lean
- \+/\- *lemma* dvd_eq_le
- \+/\- *lemma* eq_of_mul_eq_mul_left
- \+/\- *lemma* le_of_mul_le_mul_left
- \+/\- *lemma* one_or_eq_of_le_of_prime
- \+/\- *lemma* dvd_eq_le
- \+/\- *lemma* eq_of_mul_eq_mul_left
- \+/\- *lemma* le_of_mul_le_mul_left
- \+/\- *lemma* one_or_eq_of_le_of_prime

modified src/algebra/floor.lean
- \+/\- *lemma* floor_ring_unique
- \+/\- *lemma* floor_ring_unique

modified src/algebra/group/units.lean

modified src/algebra/group/with_one.lean
- \+/\- *lemma* map_eq
- \+/\- *lemma* map_eq
- \+/\- *theorem* lift_unique
- \+/\- *theorem* lift_unique

modified src/category/basic.lean

modified src/category/bitraversable/instances.lean

modified src/category/monad/writer.lean

modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* fork.condition
- \+ *lemma* cofork.condition
- \- *def* fork.condition
- \- *def* cofork.condition

modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *lemma* pullback.condition
- \+/\- *lemma* pushout.condition
- \+/\- *lemma* pullback.condition
- \+/\- *lemma* pushout.condition

modified src/data/equiv/algebra.lean
- \+/\- *lemma* coe_units_equiv_ne_zero
- \+/\- *lemma* coe_units_equiv_ne_zero
- \+/\- *def* units_equiv_ne_zero
- \+/\- *def* units_equiv_ne_zero

modified src/data/equiv/basic.lean
- \+/\- *lemma* symm_trans_swap_trans
- \+/\- *lemma* symm_trans_swap_trans

modified src/measure_theory/ae_eq_fun.lean

modified src/measure_theory/borel_space.lean
- \+/\- *lemma* borel_induced
- \+/\- *lemma* borel_eq_subtype
- \+/\- *lemma* measurable_of_continuous2
- \+/\- *lemma* borel_induced
- \+/\- *lemma* borel_eq_subtype
- \+/\- *lemma* measurable_of_continuous2

modified src/measure_theory/l1_space.lean

modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* is_measurable_inl_image
- \+/\- *lemma* is_measurable_range_inl
- \+/\- *lemma* is_measurable_inr_image
- \+/\- *lemma* is_measurable_range_inr
- \+/\- *lemma* is_measurable_inl_image
- \+/\- *lemma* is_measurable_range_inl
- \+/\- *lemma* is_measurable_inr_image
- \+/\- *lemma* is_measurable_range_inr

modified src/number_theory/pell.lean

modified src/topology/instances/polynomial.lean
- \+/\- *lemma* polynomial.continuous_eval
- \+/\- *lemma* polynomial.continuous_eval



## [2019-09-26 20:42:25](https://github.com/leanprover-community/mathlib/commit/15ed039)
fix(scripts/mk_all): ignore hidden files ([#1488](https://github.com/leanprover-community/mathlib/pull/1488))
* fix(scripts/mk_all): ignore hidden files
Emacs sometimes creates temporary files with names like `.#name.lean`.
* Fix comment
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
#### Estimated changes
modified scripts/mk_all.sh



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
modified src/data/nat/basic.lean
- \+ *lemma* lt_add_one_iff
- \+ *lemma* lt_one_add_iff

modified src/data/polynomial.lean
- \+ *lemma* ext
- \+ *lemma* zero_is_root_of_coeff_zero_eq_zero
- \+/\- *lemma* map_id
- \+ *lemma* hom_eval₂
- \+ *lemma* monic.leading_coeff
- \+ *lemma* degree_eq_iff_nat_degree_eq
- \+ *lemma* degree_eq_iff_nat_degree_eq_of_pos
- \+ *lemma* coeff_eq_zero_of_nat_degree_lt
- \+ *lemma* finset_sum_coeff
- \+ *lemma* ite_le_nat_degree_coeff
- \+ *lemma* as_sum
- \+/\- *lemma* map_id
- \+ *theorem* ext_iff
- \- *theorem* ext

created src/field_theory/minimal_polynomial.lean
- \+ *lemma* monic
- \+ *lemma* aeval
- \+ *lemma* min
- \+ *lemma* ne_zero
- \+ *lemma* degree_le_of_ne_zero
- \+ *lemma* unique
- \+ *lemma* dvd
- \+ *lemma* degree_ne_zero
- \+ *lemma* not_is_unit
- \+ *lemma* degree_pos
- \+ *lemma* prime
- \+ *lemma* irreducible
- \+ *lemma* algebra_map'
- \+ *lemma* zero
- \+ *lemma* one
- \+ *lemma* root
- \+ *lemma* coeff_zero_eq_zero
- \+ *lemma* coeff_zero_ne_zero

modified src/ring_theory/algebra.lean

modified src/ring_theory/polynomial.lean

modified src/ring_theory/power_series.lean



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
modified src/data/list/basic.lean
- \+ *lemma* exists_of_length_succ
- \+ *lemma* last_eq_nth_le
- \+ *lemma* length_scanl
- \+ *theorem* ne_nil_of_length_pos
- \+ *theorem* length_pos_of_ne_nil
- \+ *theorem* length_pos_iff_ne_nil

modified src/data/set/lattice.lean
- \+ *lemma* sUnion_eq_univ_iff
- \+ *lemma* disjoint_left
- \+ *theorem* disjoint_right

created src/data/setoid.lean
- \+ *lemma* quotient.eq_rel
- \+ *lemma* ext'
- \+ *lemma* ext_iff
- \+ *lemma* refl'
- \+ *lemma* symm'
- \+ *lemma* trans'
- \+ *lemma* ker_mk_eq
- \+ *lemma* inf_def
- \+ *lemma* Inf_le
- \+ *lemma* le_Inf
- \+ *lemma* sup_eq_eqv_gen
- \+ *lemma* sup_def
- \+ *lemma* Sup_eq_eqv_gen
- \+ *lemma* Sup_def
- \+ *lemma* eqv_gen_of_setoid
- \+ *lemma* eqv_gen_idem
- \+ *lemma* ker_apply_eq_preimage
- \+ *lemma* injective_ker_lift
- \+ *lemma* ker_eq_lift_of_injective
- \+ *lemma* map_of_surjective_eq_map
- \+ *lemma* eq_of_mem_eqv_class
- \+ *lemma* mem_classes
- \+ *lemma* eq_iff_classes_eq
- \+ *lemma* classes_inj
- \+ *lemma* empty_not_mem_classes
- \+ *lemma* classes_eqv_classes
- \+ *lemma* eq_of_mem_classes
- \+ *lemma* eq_eqv_class_of_mem
- \+ *lemma* eqv_class_mem
- \+ *lemma* eqv_classes_disjoint
- \+ *lemma* eqv_classes_of_disjoint_union
- \+ *lemma* ne_empty_of_mem_partition
- \+ *lemma* exists_of_mem_partition
- \+ *theorem* eq_iff_rel_eq
- \+ *theorem* le_def
- \+ *theorem* inf_iff_and
- \+ *theorem* Inf_def
- \+ *theorem* eqv_gen_eq
- \+ *theorem* eqv_gen_le
- \+ *theorem* eqv_gen_mono
- \+ *theorem* injective_iff_ker_bot
- \+ *theorem* lift_unique
- \+ *theorem* mk_classes_classes
- \+ *theorem* classes_mk_classes
- \+ *def* setoid.rel
- \+ *def* ker
- \+ *def* gi
- \+ *def* map
- \+ *def* map_of_surjective
- \+ *def* comap
- \+ *def* mk_classes
- \+ *def* classes
- \+ *def* setoid_of_disjoint_union
- \+ *def* is_partition
- \+ *def* partition.order_iso

modified src/order/galois_connection.lean
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
modified src/algebra/ring.lean

modified src/data/equiv/algebra.lean
- \+ *lemma* map_eq_one_iff
- \+ *lemma* map_ne_one_iff
- \+ *lemma* map_inv
- \+ *lemma* add_equiv.map_sub
- \+ *lemma* coe_mul_equiv
- \+ *lemma* coe_add_equiv
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* image_eq_preimage
- \+ *lemma* map_mul
- \+ *lemma* map_one
- \+ *lemma* map_add
- \+ *lemma* map_zero
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* map_neg_one
- \- *lemma* to_equiv_symm
- \- *lemma* to_equiv_symm_apply
- \+ *def* to_ring_hom
- \+ *def* of
- \+ *def* of'
- \- *def* to_mul_equiv
- \- *def* to_add_equiv

modified src/data/mv_polynomial.lean
- \+/\- *def* pempty_ring_equiv
- \+/\- *def* punit_ring_equiv
- \+/\- *def* ring_equiv_of_equiv
- \+/\- *def* ring_equiv_congr
- \+/\- *def* sum_ring_equiv
- \+/\- *def* option_equiv_left
- \+/\- *def* option_equiv_right
- \+/\- *def* pempty_ring_equiv
- \+/\- *def* punit_ring_equiv
- \+/\- *def* ring_equiv_of_equiv
- \+/\- *def* ring_equiv_congr
- \+/\- *def* sum_ring_equiv
- \+/\- *def* option_equiv_left
- \+/\- *def* option_equiv_right

modified src/ring_theory/free_comm_ring.lean
- \+/\- *def* free_comm_ring_pempty_equiv_int
- \+/\- *def* free_comm_ring_punit_equiv_polynomial_int
- \+/\- *def* free_ring_pempty_equiv_int
- \+/\- *def* free_ring_punit_equiv_polynomial_int
- \+/\- *def* free_comm_ring_pempty_equiv_int
- \+/\- *def* free_comm_ring_punit_equiv_polynomial_int
- \+/\- *def* free_ring_pempty_equiv_int
- \+/\- *def* free_ring_punit_equiv_polynomial_int

modified src/ring_theory/ideal_operations.lean

modified src/ring_theory/localization.lean
- \+/\- *def* equiv_of_equiv
- \+/\- *def* equiv_of_equiv
- \+/\- *def* equiv_of_equiv
- \+/\- *def* equiv_of_equiv

modified src/ring_theory/maps.lean
- \- *lemma* map_add
- \- *lemma* map_zero
- \- *lemma* map_neg
- \- *lemma* map_sub
- \- *lemma* map_mul
- \- *lemma* map_one
- \- *lemma* map_neg_one
- \+/\- *def* comm_ring.equiv_to_anti_equiv
- \+/\- *def* comm_ring.anti_equiv_to_equiv
- \+/\- *def* comm_ring.equiv_to_anti_equiv
- \+/\- *def* comm_ring.anti_equiv_to_equiv

modified src/ring_theory/noetherian.lean



## [2019-09-26 00:29:27](https://github.com/leanprover-community/mathlib/commit/2e35a7a)
feat(int/basic): add simp-lemma int.of_nat_eq_coe ([#1486](https://github.com/leanprover-community/mathlib/pull/1486))
* feat(int/basic): add simp-lemma int.of_nat_eq_coe
* fix errors
in the process also add some lemmas about bxor to simplify proofs
* use coercion in rat.mk
#### Estimated changes
modified src/data/bool.lean
- \+ *theorem* bxor_bnot_left
- \+ *theorem* bxor_bnot_right
- \+ *theorem* bxor_bnot_bnot

modified src/data/int/basic.lean

modified src/data/rat/basic.lean



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
modified docs/tactics.md

modified src/meta/expr.lean

modified src/tactic/sanity_check.lean

modified test/sanity_check.lean
- \+ *lemma* foo.foo
- \- *lemma* foo4
- \+ *def* bar.foo



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
modified .gitignore

modified scripts/mk_all.sh

modified scripts/rm_all.sh



## [2019-09-25 01:30:42](https://github.com/leanprover-community/mathlib/commit/491a68e)
cleanup(*): use priority 10 for low priority ([#1485](https://github.com/leanprover-community/mathlib/pull/1485))
Now we can locally use priorities lower than this low-priority
#### Estimated changes
modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/times_cont_diff.lean

modified src/category/bifunctor.lean

modified src/category/bitraversable/instances.lean

modified src/category_theory/adjunction/basic.lean
- \+/\- *lemma* hom_equiv_naturality_left_symm
- \+/\- *lemma* hom_equiv_naturality_right
- \+/\- *lemma* hom_equiv_naturality_left_symm
- \+/\- *lemma* hom_equiv_naturality_right

modified src/computability/primrec.lean

modified src/data/fintype.lean
- \+/\- *lemma* linear_order.is_well_order
- \+/\- *lemma* linear_order.is_well_order
- \+/\- *def* unique.fintype
- \+/\- *def* unique.fintype

modified src/data/int/basic.lean

modified src/data/nat/cast.lean

modified src/data/num/basic.lean

modified src/data/rat/cast.lean

modified src/field_theory/splitting_field.lean

modified src/group_theory/sylow.lean

modified src/linear_algebra/finsupp.lean

modified src/logic/basic.lean

modified src/logic/function.lean

modified src/tactic/finish.lean

modified src/tactic/localized.lean

modified src/tactic/push_neg.lean

modified src/topology/algebra/uniform_group.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/uniform_space/abstract_completion.lean



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
modified docs/tactics.md

modified src/meta/expr.lean

modified src/tactic/core.lean

modified test/examples.lean



## [2019-09-24 13:36:31](https://github.com/leanprover-community/mathlib/commit/1eaa292)
feat(finset): add has_sep instance ([#1477](https://github.com/leanprover-community/mathlib/pull/1477))
#### Estimated changes
modified src/data/finset.lean
- \+ *lemma* filter_congr_decidable
- \+ *lemma* sep_def
- \- *lemma* `filter_congr_decidable`

modified test/examples.lean



## [2019-09-24 08:39:19](https://github.com/leanprover-community/mathlib/commit/5344da4)
feat(algebra/big_operators): simp lemmas ([#1471](https://github.com/leanprover-community/mathlib/pull/1471))
* feat(algebra/big_operators): simp lemmas
* remove @[simp]
#### Estimated changes
modified src/algebra/big_operators.lean
- \+ *lemma* prod_ite
- \+ *lemma* sum_mul_boole
- \+ *lemma* sum_boole_mul

modified src/data/finset.lean
- \+ *lemma* filter_eq



## [2019-09-24 08:13:37](https://github.com/leanprover-community/mathlib/commit/201174d)
feat(algebra/continued_fractions): add basic defs/lemmas for continued fractions ([#1433](https://github.com/leanprover-community/mathlib/pull/1433))
* feat(algebra/continued_fractions): add basic defs/lemmas for continued fractions
* Rename termiantes_at to terminated_at, use long names for cont. fracts.
* Fix indentation, remove subfolders, fix docstrings
#### Estimated changes
modified docs/references.bib

created src/algebra/continued_fractions/basic.lean
- \+ *lemma* coe_to_generalized_continued_fraction_pair
- \+ *lemma* coe_to_generalized_continued_fraction
- \+ *lemma* coe_to_generalized_continued_fraction
- \+ *lemma* coe_to_simple_continued_fraction
- \+ *lemma* coe_to_generalized_continued_fraction
- \+ *def* partial_numerators
- \+ *def* partial_denominators
- \+ *def* terminated_at
- \+ *def* terminates
- \+ *def* seq.coe_to_seq
- \+ *def* generalized_continued_fraction.is_simple_continued_fraction
- \+ *def* simple_continued_fraction
- \+ *def* simple_continued_fraction.is_regular_continued_fraction
- \+ *def* continued_fraction
- \+ *def* next_numerator
- \+ *def* next_denominator
- \+ *def* next_continuants
- \+ *def* continuants_aux
- \+ *def* continuants
- \+ *def* numerators
- \+ *def* denominators
- \+ *def* convergents
- \+ *def* convergents'_aux
- \+ *def* convergents'

created src/algebra/continued_fractions/continuants_recurrence.lean
- \+ *lemma* continuants_aux_recurrence
- \+ *lemma* continuants_recurrence_aux
- \+ *lemma* numerators_recurrence
- \+ *lemma* denominators_recurrence
- \+ *theorem* continuants_recurrence

created src/algebra/continued_fractions/default.lean

created src/algebra/continued_fractions/translations.lean
- \+ *lemma* terminated_at_iff_s_terminated_at
- \+ *lemma* terminated_at_iff_s_none
- \+ *lemma* part_num_none_iff_s_none
- \+ *lemma* terminated_at_iff_part_num_none
- \+ *lemma* part_denom_none_iff_s_none
- \+ *lemma* terminated_at_iff_part_denom_none
- \+ *lemma* part_num_eq_s_a
- \+ *lemma* part_denom_eq_s_b
- \+ *lemma* obtain_s_a_of_part_num
- \+ *lemma* obtain_s_b_of_part_denom
- \+ *lemma* nth_cont_eq_succ_nth_cont_aux
- \+ *lemma* num_eq_conts_a
- \+ *lemma* denom_eq_conts_b
- \+ *lemma* convergent_eq_num_div_denom
- \+ *lemma* convergent_eq_conts_a_div_conts_b
- \+ *lemma* obtain_conts_a_of_num
- \+ *lemma* obtain_conts_b_of_denom
- \+ *lemma* zeroth_continuant_aux_eq_one_zero
- \+ *lemma* first_continuant_aux_eq_h_one
- \+ *lemma* zeroth_continuant_eq_h_one
- \+ *lemma* zeroth_convergent_eq_h
- \+ *lemma* zeroth_convergent'_aux_eq_zero
- \+ *lemma* zeroth_convergent'_eq_h

modified src/data/seq/seq.lean
- \+ *lemma* terminated_stable
- \+ *def* terminated_at
- \+ *def* terminates



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
modified src/tactic/library_search.lean

modified src/tactic/solve_by_elim.lean

modified test/library_search/basic.lean
- \+ *lemma* zero_lt_one
- \+ *def* lt_one
- \- *def* P
- \- *def* Q
- \- *def* f

modified test/solve_by_elim.lean



## [2019-09-24 03:51:35](https://github.com/leanprover-community/mathlib/commit/88f37b5)
fix(tactic.lift): fix error messages ([#1478](https://github.com/leanprover-community/mathlib/pull/1478))
#### Estimated changes
modified src/tactic/lift.lean

modified test/tactics.lean



## [2019-09-24 00:00:49](https://github.com/leanprover-community/mathlib/commit/425644f)
refactor(algebra/*): Make `monoid_hom.ext` etc use `∀ x, f x = g x` as an assumption ([#1476](https://github.com/leanprover-community/mathlib/pull/1476))
#### Estimated changes
modified src/algebra/category/CommRing/adjunctions.lean

modified src/algebra/category/CommRing/basic.lean

modified src/algebra/category/CommRing/limits.lean

modified src/algebra/category/Mon/basic.lean

modified src/algebra/group/hom.lean
- \+ *lemma* coe_inj
- \+/\- *lemma* ext
- \+ *lemma* ext_iff
- \+/\- *lemma* ext

modified src/algebra/ring.lean
- \+ *theorem* coe_inj
- \+/\- *theorem* ext
- \+ *theorem* ext_iff
- \+/\- *theorem* ext

modified src/data/mv_polynomial.lean



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
modified src/algebra/ordered_ring.lean
- \+ *lemma* lt_one_add

modified src/data/equiv/basic.lean

modified src/data/equiv/list.lean
- \+ *def* list_unit_equiv

modified src/data/fin.lean
- \+ *lemma* injective_val
- \+ *lemma* val_one
- \+ *lemma* val_two
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* coe_two
- \+/\- *lemma* injective_cast_le
- \+/\- *lemma* injective_cast_le

modified src/data/list/basic.lean
- \+ *lemma* injective_length_iff
- \+ *lemma* injective_length
- \+ *lemma* empty_eq
- \+ *lemma* singleton_eq
- \+ *lemma* insert_neg
- \+ *lemma* insert_pos
- \+ *lemma* doubleton_eq
- \+ *lemma* join_join
- \+/\- *lemma* map_congr
- \+ *lemma* map_eq_map_iff
- \+ *lemma* exists_lt_of_sum_lt
- \+ *lemma* exists_le_of_sum_le
- \+/\- *lemma* length_attach
- \+/\- *lemma* rel_filter_map
- \+/\- *lemma* nth_le_attach
- \+/\- *lemma* map_congr
- \+/\- *lemma* length_attach
- \+/\- *lemma* rel_filter_map
- \+/\- *lemma* nth_le_attach
- \+/\- *theorem* length_eq_zero
- \+/\- *theorem* length_pos_of_mem
- \+/\- *theorem* exists_mem_of_length_pos
- \+/\- *theorem* length_pos_iff_exists_mem
- \+/\- *theorem* length_eq_one
- \+ *theorem* subset_append_of_subset_left
- \+ *theorem* subset_append_of_subset_right
- \+ *theorem* append_subset_of_subset_of_subset
- \+ *theorem* append_subset_iff
- \+ *theorem* map_subset_iff
- \+/\- *theorem* bind_append
- \+ *theorem* sublist_append_of_sublist_left
- \+ *theorem* sublist_append_of_sublist_right
- \+/\- *theorem* append_sublist_append
- \+ *theorem* nth_le_map_rev
- \+/\- *theorem* map_concat
- \+/\- *theorem* map_id'
- \+/\- *theorem* foldl_map
- \+/\- *theorem* foldr_map
- \+/\- *theorem* foldl_hom
- \+/\- *theorem* foldr_hom
- \+/\- *theorem* eq_nil_of_map_eq_nil
- \+/\- *theorem* map_join
- \+/\- *theorem* bind_ret_eq_map
- \+/\- *theorem* map_eq_map
- \+/\- *theorem* map_tail
- \+ *theorem* injective_map_iff
- \+/\- *theorem* nil_map₂
- \+/\- *theorem* map₂_nil
- \+/\- *theorem* length_insert_of_mem
- \+/\- *theorem* length_insert_of_not_mem
- \+ *theorem* pairwise_append_comm
- \+/\- *theorem* chain'.iff_mem
- \+/\- *theorem* nodup_append_of_nodup
- \+ *theorem* nodup_append_comm
- \+/\- *theorem* ilast'_mem
- \+/\- *theorem* length_eq_zero
- \+/\- *theorem* length_pos_of_mem
- \+/\- *theorem* exists_mem_of_length_pos
- \+/\- *theorem* length_pos_iff_exists_mem
- \+/\- *theorem* length_eq_one
- \- *theorem* subset_app_of_subset_left
- \- *theorem* subset_app_of_subset_right
- \- *theorem* app_subset_of_subset_of_subset
- \+/\- *theorem* bind_append
- \+/\- *theorem* map_concat
- \+/\- *theorem* map_id'
- \+/\- *theorem* foldl_map
- \+/\- *theorem* foldr_map
- \+/\- *theorem* foldl_hom
- \+/\- *theorem* foldr_hom
- \+/\- *theorem* eq_nil_of_map_eq_nil
- \+/\- *theorem* map_join
- \+/\- *theorem* bind_ret_eq_map
- \+/\- *theorem* map_eq_map
- \+/\- *theorem* map_tail
- \+/\- *theorem* nil_map₂
- \+/\- *theorem* map₂_nil
- \- *theorem* sublist_app_of_sublist_left
- \- *theorem* sublist_app_of_sublist_right
- \+/\- *theorem* append_sublist_append
- \+/\- *theorem* length_insert_of_mem
- \+/\- *theorem* length_insert_of_not_mem
- \- *theorem* pairwise_app_comm
- \+/\- *theorem* chain'.iff_mem
- \+/\- *theorem* nodup_append_of_nodup
- \- *theorem* nodup_app_comm
- \+/\- *theorem* ilast'_mem

modified src/data/nat/basic.lean
- \+ *lemma* pred_eq_succ_iff

modified src/data/set/basic.lean
- \+ *lemma* set_of_app_iff

modified src/data/subtype.lean
- \+ *theorem* subtype.forall'

modified src/set_theory/cardinal.lean
- \+ *lemma* lift_eq_nat_iff
- \+ *lemma* nat_eq_lift_eq_iff
- \+ *lemma* add_lt_omega_iff
- \+ *lemma* mul_lt_omega_iff
- \+ *lemma* mul_lt_omega_iff_of_ne_zero
- \+ *lemma* mk_range_eq_lift
- \+ *lemma* mk_sum_compl
- \+ *theorem* power_le_max_power_one
- \+ *theorem* mk_image_le_lift

modified src/set_theory/ordinal.lean
- \+ *lemma* mul_eq_left
- \+ *lemma* mul_eq_right
- \+ *lemma* le_mul_left
- \+ *lemma* le_mul_right
- \+ *lemma* mul_eq_left_iff
- \+ *lemma* eq_of_add_eq_of_omega_le
- \+ *lemma* add_eq_left
- \+ *lemma* add_eq_right
- \+ *lemma* add_eq_left_iff
- \+ *lemma* add_eq_right_iff
- \+ *lemma* mk_compl_of_omega_le
- \+ *lemma* mk_compl_finset_of_omega_le
- \+ *lemma* mk_compl_eq_mk_compl_infinite
- \+ *lemma* mk_compl_eq_mk_compl_finite_lift
- \+ *lemma* mk_compl_eq_mk_compl_finite
- \+ *lemma* mk_compl_eq_mk_compl_finite_same
- \+/\- *theorem* lt_le_top
- \+ *theorem* is_limit_add_iff
- \+ *theorem* lt_bsup
- \+ *theorem* bsup_id
- \+ *theorem* is_normal.bsup_eq
- \+ *theorem* nfp_eq_self
- \+ *theorem* ord_aleph_is_limit
- \+/\- *theorem* pow_le
- \+ *theorem* extend_function
- \+ *theorem* extend_function_finite
- \+ *theorem* extend_function_of_lt
- \+/\- *theorem* lt_le_top
- \- *theorem* aleph_is_limit
- \+/\- *theorem* pow_le
- \+/\- *def* lt_le
- \+/\- *def* equiv_lt
- \+/\- *def* of_element
- \+ *def* aleph'_equiv
- \+/\- *def* lt_le
- \+/\- *def* equiv_lt
- \+/\- *def* of_element



## [2019-09-23 19:57:18](https://github.com/leanprover-community/mathlib/commit/fd7840a)
feat(topology/constructions): is_open_prod_iff' ([#1454](https://github.com/leanprover-community/mathlib/pull/1454))
* feat(topology/constructions): open_prod_iff'
* reviewer's comments
* fix build
* golfed; is_open_map_fst
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* prod_subset_prod_iff

modified src/topology/constructions.lean
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
modified src/tactic/core.lean
- \+ *def* new_int

created test/delta_instance.lean
- \+ *def* T
- \+ *def* V



## [2019-09-22 04:34:09](https://github.com/leanprover-community/mathlib/commit/61ccaf6)
chore(*): fix various issues reported by `sanity_check_mathlib` ([#1469](https://github.com/leanprover-community/mathlib/pull/1469))
* chore(*): fix various issues reported by `sanity_check_mathlib`
* Drop a misleading comment, fix the proof
#### Estimated changes
modified src/algebra/direct_limit.lean
- \+ *lemma* directed_system
- \- *def* directed_system

modified src/algebra/field.lean
- \+ *lemma* mk0_inj
- \- *lemma* units.mk0_inj

modified src/algebra/group/basic.lean

modified src/algebra/group/with_one.lean

modified src/algebra/ordered_field.lean
- \+ *lemma* div_pos
- \+ *lemma* div_nonneg
- \+ *lemma* half_lt_self
- \- *def* div_pos
- \- *def* div_nonneg
- \- *def* half_lt_self

modified src/algebra/ordered_ring.lean
- \+ *def* to_linear_nonneg_ring
- \- *def* nonneg_ring.to_linear_nonneg_ring

modified src/algebra/pointwise.lean
- \+ *lemma* singleton.is_mul_hom
- \+ *lemma* singleton.is_monoid_hom
- \+ *lemma* pointwise_mul_image_is_semiring_hom
- \- *def* singleton.is_mul_hom
- \- *def* singleton.is_monoid_hom
- \- *def* pointwise_mul_image_is_semiring_hom

modified src/category/monad/cont.lean
- \+ *def* monad_lift
- \- *def* cont_t.monad_lift

modified src/category/traversable/equiv.lean

modified src/category_theory/natural_isomorphism.lean
- \+ *lemma* of_components.app
- \+ *lemma* of_components.hom_app
- \+ *lemma* of_components.inv_app
- \- *def* of_components.app
- \- *def* of_components.hom_app
- \- *def* of_components.inv_app

modified src/data/equiv/algebra.lean
- \+ *lemma* map_mul
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* map_one
- \- *def* map_mul
- \- *def* apply_symm_apply
- \- *def* symm_apply_apply
- \- *def* map_one

modified src/data/equiv/basic.lean
- \- *lemma* subtype_quotient_equiv_quotient_subtype
- \+ *def* subtype_quotient_equiv_quotient_subtype

modified src/data/finset.lean
- \- *lemma* strong_induction_on
- \+ *def* strong_induction_on

modified src/data/finsupp.lean
- \+ *lemma* lt_wf
- \- *def* lt_wf

modified src/data/matrix/basic.lean
- \+ *lemma* is_add_monoid_hom_mul_right
- \- *def* is_add_monoid_hom_mul_right

modified src/data/multiset.lean
- \+ *theorem* map_eq_zero
- \- *theorem* multiset.map_eq_zero

modified src/data/mv_polynomial.lean
- \+/\- *lemma* degrees_neg
- \+/\- *lemma* degrees_sub
- \+/\- *lemma* degrees_neg
- \+/\- *lemma* degrees_sub

modified src/data/polynomial.lean
- \+ *lemma* degree_lt_wf
- \+ *def* coeff_coe_to_fun
- \- *def* polynomial.has_coe_to_fun
- \- *def* degree_lt_wf

modified src/data/rat/basic.lean
- \- *theorem* {u}
- \- *theorem* {u}
- \+ *def* {u}
- \+ *def* {u}

modified src/data/rat/order.lean

modified src/group_theory/free_group.lean
- \+ *lemma* to_word.mk
- \+ *lemma* to_word.inj
- \- *def* to_word.mk
- \- *def* to_word.inj

modified src/group_theory/sylow.lean
- \- *lemma* fixed_points_mul_left_cosets_equiv_quotient
- \+ *def* fixed_points_mul_left_cosets_equiv_quotient

modified src/linear_algebra/finsupp_vector_space.lean
- \- *lemma* fin_dim_vectorspace_equiv
- \+ *def* fin_dim_vectorspace_equiv

modified src/logic/basic.lean
- \+/\- *theorem* imp_intro
- \+/\- *theorem* not_of_not_imp
- \+/\- *theorem* imp_intro
- \- *theorem* not.elim
- \+/\- *theorem* not_of_not_imp
- \+ *def* not.elim

modified src/measure_theory/ae_eq_fun.lean
- \+ *lemma* lift_rel_mk_mk
- \- *def* lift_rel_mk_mk

modified src/number_theory/dioph.lean
- \+ *lemma* isp
- \+ *lemma* ext
- \+ *lemma* induction
- \- *def* isp
- \- *def* ext
- \- *def* induction

modified src/order/filter/basic.lean

modified src/order/filter/pointwise.lean
- \+ *lemma* pointwise_mul_map_is_monoid_hom
- \+ *lemma* pointwise_add_map_is_add_monoid_hom
- \- *def* pointwise_mul_map_is_monoid_hom
- \- *def* pointwise_add_map_is_add_monoid_hom

modified src/ring_theory/algebra.lean

modified src/ring_theory/ideals.lean
- \+ *theorem* zero_ne_one_of_proper
- \+/\- *theorem* mem_span_pair
- \+/\- *theorem* is_coprime_def
- \+/\- *theorem* is_coprime_self
- \+/\- *theorem* mem_span_pair
- \+/\- *theorem* is_coprime_def
- \+/\- *theorem* is_coprime_self
- \- *def* zero_ne_one_of_proper

modified src/ring_theory/power_series.lean
- \+ *lemma* is_local_ring
- \- *def* is_local_ring

modified src/set_theory/ordinal.lean
- \+ *theorem* nonempty_embedding_to_cardinal
- \+ *def* embedding_to_cardinal
- \+/\- *def* div_def
- \+/\- *def* div_def

modified src/set_theory/pgame.lean
- \+ *lemma* subsequent.left_move
- \+ *lemma* subsequent.right_move
- \+ *lemma* add_zero_equiv
- \+ *lemma* zero_add_equiv
- \- *def* subsequent.left_move
- \- *def* subsequent.right_move
- \- *def* add_zero_equiv
- \- *def* zero_add_equiv

modified src/set_theory/surreal.lean
- \+ *lemma* numeric.move_left
- \+ *lemma* numeric.move_right
- \- *def* numeric.move_left
- \- *def* numeric.move_right

modified src/set_theory/zfc.lean

modified src/tactic/doc_blame.lean

modified src/tactic/monotonicity/interactive.lean
- \- *lemma* apply_rel
- \+ *def* apply_rel

modified src/tactic/omega/clause.lean
- \+ *lemma* holds_append
- \- *def* holds_append

modified src/tactic/omega/coeffs.lean
- \+ *lemma* val_between_set
- \+ *lemma* val_set
- \+ *lemma* val_except_add_eq
- \- *def* val_between_set
- \- *def* val_set
- \- *def* val_except_add_eq

modified src/tactic/omega/nat/form.lean
- \+ *lemma* holds_constant
- \- *def* holds_constant

modified src/tactic/omega/nat/preterm.lean
- \+ *lemma* val_constant
- \- *def* val_constant

modified src/tactic/ring.lean
- \+/\- *theorem* pow_add_rev
- \+/\- *theorem* pow_add_rev



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
modified src/category_theory/discrete_category.lean

deleted src/category_theory/limits/shapes/constructions/finite_limits.lean

modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean
- \+ *def* diagram
- \+ *def* cones_hom
- \+ *def* cones_inv
- \+ *def* cones_iso
- \+ *def* finite_limits_from_equalizers_and_finite_products
- \- *def* equalizer_diagram
- \- *def* equalizer_diagram.cones_hom
- \- *def* equalizer_diagram.cones_inv
- \- *def* equalizer_diagram.cones_iso

modified src/category_theory/limits/shapes/finite_limits.lean

modified src/category_theory/limits/shapes/finite_products.lean



## [2019-09-21 00:47:17](https://github.com/leanprover-community/mathlib/commit/9c89fa5)
feat(tactic/interactive): add fconstructor ([#1467](https://github.com/leanprover-community/mathlib/pull/1467))
#### Estimated changes
modified src/tactic/interactive.lean



## [2019-09-20 11:08:05](https://github.com/leanprover-community/mathlib/commit/708a28c)
chore(algebra/group/units): use `def to_units` instead of `has_lift` ([#1431](https://github.com/leanprover-community/mathlib/pull/1431))
* chore(algebra/group/units): use `def to_units` instead of `has_lift`
* Move, upgrade to `mul_equiv`, add documentation
#### Estimated changes
modified src/algebra/group/units.lean

modified src/data/equiv/algebra.lean
- \+ *def* to_units



## [2019-09-20 03:28:58](https://github.com/leanprover-community/mathlib/commit/bfe9c6c)
chore(data/pfun): run `#sanity_check` ([#1463](https://github.com/leanprover-community/mathlib/pull/1463))
#### Estimated changes
modified src/data/pfun.lean
- \+ *lemma* mem_preimage
- \+ *theorem* ext'
- \+ *theorem* ext
- \+ *theorem* ext'
- \+ *theorem* ext
- \- *theorem* fix_induction
- \+ *def* fix_induction
- \- *def* ext'
- \- *def* ext
- \- *def* ext'
- \- *def* ext
- \- *def* mem_preimage



## [2019-09-19 15:32:04](https://github.com/leanprover-community/mathlib/commit/ce105fd)
chore(algebra/group): rename `as_monoid_hom` into `monoid_hom.of`, define `ring_hom.of` ([#1443](https://github.com/leanprover-community/mathlib/pull/1443))
* chore(algebra/group): rename `as_monoid_hom` into `monoid_hom.of`
This is similar to `Mon.of` etc.
* Fix compile
* Docs, missing universe
* Move variables declaration up as suggested by @jcommelin
* doc-string
#### Estimated changes
modified src/algebra/associated.lean

modified src/algebra/group/hom.lean
- \+ *lemma* coe_of
- \- *lemma* coe_as_monoid_hom
- \+ *def* of
- \- *def* as_monoid_hom

modified src/algebra/group/units_hom.lean

modified src/algebra/ring.lean
- \+/\- *lemma* coe_of
- \+/\- *lemma* coe_of
- \+/\- *def* of
- \+/\- *def* of



## [2019-09-19 13:17:33](https://github.com/leanprover-community/mathlib/commit/d910283)
chore(category_theory/endomorphism): make `map_End` and `map_Aut` use bundled homs ([#1461](https://github.com/leanprover-community/mathlib/pull/1461))
* Migrate `functor.map_End` and `functor.map_Aut` to bundled homs
Adjust implicit arguments of `iso.ext`
* Add docstrings
#### Estimated changes
modified src/category_theory/endomorphism.lean
- \+/\- *def* map_End
- \+/\- *def* map_Aut
- \+/\- *def* map_End
- \+/\- *def* map_Aut

modified src/category_theory/isomorphism.lean
- \+/\- *lemma* ext
- \+/\- *lemma* symm_self_id
- \+/\- *lemma* self_symm_id
- \+ *lemma* map_iso_refl
- \+/\- *lemma* ext
- \+/\- *lemma* symm_self_id
- \+/\- *lemma* self_symm_id



## [2019-09-19 13:21:35+02:00](https://github.com/leanprover-community/mathlib/commit/1b8285e)
chore(readme): Add new maintainers [ci skip]
#### Estimated changes
modified README.md



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
modified docs/references.bib

modified src/algebra/category/CommRing/adjunctions.lean
- \+ *lemma* free_obj_coe
- \+ *lemma* free_map_coe
- \- *lemma* free_obj_α
- \- *lemma* free_map_val
- \+/\- *def* adj
- \- *def* hom_equiv
- \+/\- *def* adj

modified src/algebra/category/CommRing/basic.lean
- \+ *lemma* id_eq
- \+ *lemma* comp_eq
- \+ *lemma* forget_obj_eq_coe
- \+ *lemma* forget_map_eq_coe
- \+ *def* SemiRing
- \+/\- *def* of
- \+/\- *def* of
- \+ *def* CommSemiRing
- \+/\- *def* of
- \+/\- *def* CommRing
- \+/\- *def* of
- \+/\- *def* CommRing
- \+/\- *def* of
- \+/\- *def* of
- \- *def* Int.cast
- \- *def* Int.hom_unique
- \- *def* to_Ring
- \- *def* forget_to_CommMon

modified src/algebra/category/CommRing/colimits.lean
- \- *lemma* naturality_bundled
- \+/\- *def* colimit
- \+/\- *def* colimit

modified src/algebra/category/CommRing/limits.lean
- \- *def* limit
- \- *def* limit_is_limit

modified src/algebra/category/Group.lean
- \+/\- *def* Group
- \+/\- *def* of
- \+ *def* CommGroup
- \+/\- *def* of
- \+/\- *def* Group
- \- *def* AddCommGroup
- \+/\- *def* of
- \- *def* is_add_comm_group_hom
- \+/\- *def* of
- \- *def* forget_to_Group

modified src/algebra/category/Mon/basic.lean
- \+/\- *def* Mon
- \+/\- *def* of
- \+/\- *def* CommMon
- \+/\- *def* of
- \+/\- *def* Mon
- \+/\- *def* CommMon
- \+/\- *def* of
- \- *def* hom_equiv_monoid_hom
- \- *def* is_comm_monoid_hom
- \+/\- *def* of
- \- *def* forget_to_Mon

modified src/algebra/category/Mon/colimits.lean

modified src/algebra/punit_instances.lean

modified src/algebra/ring.lean
- \+ *lemma* of_semiring
- \+ *lemma* coe_of
- \+ *lemma* coe_comp
- \+ *def* of
- \+/\- *def* comp
- \- *def* of_semiring
- \+/\- *def* comp

modified src/algebraic_geometry/stalks.lean

modified src/category_theory/category/Cat.lean
- \+/\- *def* of
- \+/\- *def* of

modified src/category_theory/category/Groupoid.lean
- \+/\- *def* of
- \+/\- *def* of

deleted src/category_theory/concrete_category.lean
- \- *lemma* concrete_category_id
- \- *lemma* concrete_category_comp
- \- *lemma* hom_ext
- \- *lemma* coe_id
- \- *lemma* coe_comp
- \- *lemma* bundled_hom_coe
- \- *def* mk_ob
- \- *def* map
- \- *def* concrete_functor
- \- *def* forget

created src/category_theory/concrete_category/basic.lean
- \+ *def* forget
- \+ *def* forget₂
- \+ *def* has_forget₂.mk'

created src/category_theory/concrete_category/bundled.lean
- \+ *def* of
- \+ *def* map

created src/category_theory/concrete_category/bundled_hom.lean
- \+ *lemma* coe_id
- \+ *lemma* coe_comp
- \+ *def* has_coe_to_fun
- \+ *def* full_subcategory_has_forget₂
- \+ *def* mk_has_forget₂

created src/category_theory/concrete_category/default.lean

created src/category_theory/concrete_category/unbundled_hom.lean
- \+ *def* mk_has_forget₂

modified src/category_theory/fully_faithful.lean
- \+ *lemma* injectivity
- \+/\- *lemma* preimage_id
- \+/\- *lemma* preimage_comp
- \+/\- *lemma* preimage_map
- \+ *lemma* preimage_iso_map_iso
- \+ *lemma* faithful.of_comp
- \+ *lemma* faithful.of_comp_eq
- \+ *lemma* faithful.div_comp
- \+ *lemma* faithful.div_faithful
- \+/\- *lemma* preimage_id
- \+/\- *lemma* preimage_comp
- \+/\- *lemma* preimage_map
- \- *def* injectivity

modified src/category_theory/functor.lean

modified src/category_theory/limits/cones.lean

modified src/category_theory/single_obj.lean

modified src/data/mv_polynomial.lean
- \+ *def* hom_equiv

modified src/logic/function.lean
- \+ *lemma* injective.of_comp
- \+ *lemma* surjective.of_comp

modified src/measure_theory/category/Meas.lean
- \+/\- *def* of
- \+/\- *def* Borel
- \+/\- *def* of
- \+/\- *def* Borel

modified src/topology/category/Top/adjunctions.lean
- \+/\- *def* adj₁
- \+/\- *def* adj₂
- \+/\- *def* adj₁
- \+/\- *def* adj₂

modified src/topology/category/Top/basic.lean
- \+ *lemma* id_app
- \+/\- *def* of
- \+/\- *def* of

modified src/topology/category/Top/epi_mono.lean

modified src/topology/category/Top/limits.lean

modified src/topology/category/TopCommRing.lean
- \- *def* forget_to_CommRing
- \- *def* forget_to_Top
- \- *def* forget
- \- *def* forget_to_Type_via_Top
- \- *def* forget_to_Type_via_CommRing

modified src/topology/category/UniformSpace.lean
- \+ *lemma* coe_comp
- \+ *lemma* coe_id
- \+ *lemma* coe_mk
- \+ *lemma* hom_ext
- \+/\- *def* of
- \+/\- *def* completion_hom
- \+/\- *def* of
- \- *def* forget_to_Top
- \- *def* forget_to_Type_via_Top
- \- *def* forget_to_UniformSpace
- \- *def* forget
- \- *def* forget_to_Type_via_UniformSpace
- \+/\- *def* completion_hom

modified src/topology/sheaves/presheaf_of_functions.lean
- \+ *lemma* zero
- \+/\- *def* CommRing_yoneda
- \+/\- *def* CommRing_yoneda

modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* uniform_continuous.comp
- \+/\- *lemma* uniform_continuous.comp



## [2019-09-18 17:59:44](https://github.com/leanprover-community/mathlib/commit/066d053)
chore(topology/maps): a few tweaks to open_embedding and closed embeddings ([#1459](https://github.com/leanprover-community/mathlib/pull/1459))
* chore(topology/maps): a few tweaks to open_embedding and closed
embeddings
aligning them with recent modification to embedding. From the perfectoid
project.
* chore(topology/maps): add missing empty line
#### Estimated changes
modified src/topology/maps.lean
- \+ *lemma* open_embedding.continuous
- \+ *lemma* open_embedding.comp
- \+ *lemma* subtype_val.open_embedding
- \+ *lemma* closed_embedding.continuous
- \+/\- *lemma* closed_embedding.closed_iff_image_closed
- \+/\- *lemma* closed_embedding.is_closed_map
- \+/\- *lemma* closed_embedding.closed_iff_preimage_closed
- \+/\- *lemma* closed_embedding_of_embedding_closed
- \+/\- *lemma* closed_embedding_of_continuous_injective_closed
- \+ *lemma* subtype_val.closed_embedding
- \- *lemma* open_embedding_compose
- \+/\- *lemma* closed_embedding.closed_iff_image_closed
- \+/\- *lemma* closed_embedding.is_closed_map
- \+/\- *lemma* closed_embedding.closed_iff_preimage_closed
- \+/\- *lemma* closed_embedding_of_embedding_closed
- \+/\- *lemma* closed_embedding_of_continuous_injective_closed
- \- *def* open_embedding
- \- *def* closed_embedding



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
modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_union
- \+/\- *lemma* prod_union

modified src/data/finset.lean
- \+ *lemma* disjoint_filter

modified src/data/nat/totient.lean

modified src/data/zmod/quadratic_reciprocity.lean

modified src/group_theory/order_of_element.lean

modified src/topology/algebra/infinite_sum.lean



## [2019-09-18 15:43:01+02:00](https://github.com/leanprover-community/mathlib/commit/b51978d)
chore(data/mllist): Typo in author name [ci skip] ([#1458](https://github.com/leanprover-community/mathlib/pull/1458))
#### Estimated changes
modified src/data/mllist.lean



## [2019-09-18 15:40:20+02:00](https://github.com/leanprover-community/mathlib/commit/874a15a)
Update lattice.lean ([#1457](https://github.com/leanprover-community/mathlib/pull/1457))
#### Estimated changes
modified src/data/set/lattice.lean



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
modified docs/references.bib

modified src/algebra/ordered_group.lean
- \+ *def* ordered_comm_group.mk'

modified src/data/equiv/basic.lean
- \+ *lemma* sum_congr_symm
- \+ *theorem* refl_symm

modified src/data/finset.lean
- \+ *theorem* card_ne_zero_of_mem
- \+ *theorem* card_erase_lt_of_mem
- \+ *theorem* card_erase_le

modified src/data/multiset.lean
- \+/\- *theorem* card_erase_of_mem
- \+ *theorem* card_erase_lt_of_mem
- \+ *theorem* card_erase_le
- \+/\- *theorem* card_erase_of_mem

modified src/linear_algebra/dimension.lean

modified src/logic/basic.lean
- \+ *lemma* not_nonempty_pempty
- \- *lemma* nonempty_pempty
- \+ *theorem* forall_pempty
- \+ *theorem* exists_pempty

created src/set_theory/game.lean
- \+ *theorem* le_refl
- \+ *theorem* le_trans
- \+ *theorem* le_antisymm
- \+ *theorem* not_le
- \+ *theorem* add_assoc
- \+ *theorem* add_zero
- \+ *theorem* zero_add
- \+ *theorem* add_left_neg
- \+ *theorem* add_comm
- \+ *theorem* add_le_add_left
- \+ *def* game
- \+ *def* le
- \+ *def* lt
- \+ *def* neg
- \+ *def* add
- \+ *def* game_partial_order
- \+ *def* ordered_comm_group_game

created src/set_theory/pgame.lean
- \+ *lemma* left_moves_mk
- \+ *lemma* move_left_mk
- \+ *lemma* right_moves_mk
- \+ *lemma* move_right_mk
- \+ *lemma* zero_left_moves
- \+ *lemma* zero_right_moves
- \+ *lemma* one_left_moves
- \+ *lemma* one_move_left
- \+ *lemma* one_right_moves
- \+ *lemma* right_response_spec
- \+ *lemma* left_response_spec
- \+ *lemma* relabel_move_left
- \+ *lemma* relabel_move_left'
- \+ *lemma* relabel_move_right
- \+ *lemma* relabel_move_right'
- \+ *lemma* neg_def
- \+ *lemma* move_right_left_moves_neg
- \+ *lemma* move_left_right_moves_neg_symm
- \+ *lemma* move_left_right_moves_neg
- \+ *lemma* move_right_right_moves_neg_symm
- \+ *lemma* mk_add_move_left_inl
- \+ *lemma* add_move_left_inl
- \+ *lemma* mk_add_move_right_inl
- \+ *lemma* add_move_right_inl
- \+ *lemma* mk_add_move_left_inr
- \+ *lemma* add_move_left_inr
- \+ *lemma* mk_add_move_right_inr
- \+ *lemma* add_move_right_inr
- \+ *theorem* not_le
- \+ *theorem* not_lt
- \+ *theorem* `zero_le`
- \+ *theorem* `zero_lt`
- \+ *theorem* le_iff_sub_nonneg
- \+ *theorem* lt_iff_sub_pos
- \+ *theorem* wf_subsequent
- \+ *theorem* mk_le_mk
- \+ *theorem* le_def_lt
- \+ *theorem* mk_lt_mk
- \+ *theorem* lt_def_le
- \+ *theorem* le_def
- \+ *theorem* lt_def
- \+ *theorem* le_zero
- \+ *theorem* zero_le
- \+ *theorem* lt_zero
- \+ *theorem* zero_lt
- \+ *theorem* lt_of_le_mk
- \+ *theorem* lt_of_mk_le
- \+ *theorem* mk_lt_of_le
- \+ *theorem* lt_mk_of_le
- \+ *theorem* not_le_lt
- \+ *theorem* not_le
- \+ *theorem* not_lt
- \+ *theorem* le_refl
- \+ *theorem* lt_irrefl
- \+ *theorem* ne_of_lt
- \+ *theorem* le_trans_aux
- \+ *theorem* le_trans
- \+ *theorem* lt_of_le_of_lt
- \+ *theorem* lt_of_lt_of_le
- \+ *theorem* equiv_refl
- \+ *theorem* equiv_symm
- \+ *theorem* equiv_trans
- \+ *theorem* lt_of_lt_of_equiv
- \+ *theorem* le_of_le_of_equiv
- \+ *theorem* lt_of_equiv_of_lt
- \+ *theorem* le_of_equiv_of_le
- \+ *theorem* le_congr
- \+ *theorem* lt_congr
- \+ *theorem* le_of_restricted
- \+ *theorem* le_of_relabelling
- \+ *theorem* equiv_of_relabelling
- \+ *theorem* neg_neg
- \+ *theorem* neg_zero
- \+ *theorem* le_iff_neg_ge
- \+ *theorem* neg_congr
- \+ *theorem* lt_iff_neg_gt
- \+ *theorem* zero_le_iff_neg_le_zero
- \+ *theorem* le_zero_iff_zero_le_neg
- \+ *theorem* neg_add_le
- \+ *theorem* add_comm_le
- \+ *theorem* add_comm_equiv
- \+ *theorem* add_assoc_equiv
- \+ *theorem* add_le_add_right
- \+ *theorem* add_le_add_left
- \+ *theorem* add_congr
- \+ *theorem* add_left_neg_le_zero
- \+ *theorem* zero_le_add_left_neg
- \+ *theorem* add_left_neg_equiv
- \+ *theorem* add_right_neg_le_zero
- \+ *theorem* zero_le_add_right_neg
- \+ *theorem* add_lt_add_right
- \+ *theorem* add_lt_add_left
- \+ *theorem* le_iff_sub_nonneg
- \+ *theorem* lt_iff_sub_pos
- \+ *theorem* star_lt_zero
- \+ *theorem* zero_lt_star
- \+ *def* of_lists
- \+ *def* left_moves
- \+ *def* right_moves
- \+ *def* move_left
- \+ *def* move_right
- \+ *def* subsequent.left_move
- \+ *def* subsequent.right_move
- \+ *def* le_lt
- \+ *def* equiv
- \+ *def* restricted.refl
- \+ *def* restricted_of_relabelling
- \+ *def* relabelling.refl
- \+ *def* relabelling.symm
- \+ *def* relabel
- \+ *def* relabel_relabelling
- \+ *def* neg
- \+ *def* left_moves_neg
- \+ *def* right_moves_neg
- \+ *def* add
- \+ *def* add_zero_relabelling
- \+ *def* add_zero_equiv
- \+ *def* zero_add_relabelling
- \+ *def* zero_add_equiv
- \+ *def* left_moves_add
- \+ *def* right_moves_add
- \+ *def* neg_add_relabelling
- \+ *def* add_comm_relabelling
- \+ *def* add_assoc_relabelling
- \+ *def* star
- \+ *def* omega

modified src/set_theory/surreal.lean
- \+ *theorem* numeric_rec
- \+/\- *theorem* lt_asymm
- \+/\- *theorem* le_of_lt
- \+/\- *theorem* lt_iff_le_not_le
- \+ *theorem* numeric_zero
- \+ *theorem* numeric_one
- \+ *theorem* numeric_neg
- \+ *theorem* numeric.move_left_lt
- \+ *theorem* numeric.move_left_le
- \+ *theorem* numeric.lt_move_right
- \+ *theorem* numeric.le_move_right
- \+ *theorem* add_lt_add
- \+ *theorem* numeric_add
- \+ *theorem* add_assoc
- \- *theorem* mk_le_mk
- \- *theorem* mk_lt_mk
- \- *theorem* lt_of_le_mk
- \- *theorem* lt_of_mk_le
- \- *theorem* mk_lt_of_le
- \- *theorem* lt_mk_of_le
- \- *theorem* not_le_lt
- \- *theorem* not_le
- \- *theorem* not_lt
- \- *theorem* le_refl
- \- *theorem* lt_irrefl
- \- *theorem* ne_of_lt
- \- *theorem* le_trans_aux
- \- *theorem* le_trans
- \- *theorem* ok_rec
- \+/\- *theorem* lt_asymm
- \+/\- *theorem* le_of_lt
- \+/\- *theorem* lt_iff_le_not_le
- \- *theorem* equiv_refl
- \- *theorem* equiv_symm
- \- *theorem* equiv_trans
- \- *theorem* le_congr
- \- *theorem* lt_congr
- \+/\- *def* mul
- \+/\- *def* inv_val
- \+/\- *def* inv'
- \+ *def* numeric
- \+ *def* numeric.move_left
- \+ *def* numeric.move_right
- \+/\- *def* surreal.equiv
- \+/\- *def* mk
- \+/\- *def* lift
- \+/\- *def* lift₂
- \+/\- *def* add
- \- *def* le_lt
- \- *def* ok
- \- *def* equiv
- \- *def* neg
- \+/\- *def* add
- \+/\- *def* mul
- \+/\- *def* inv_val
- \+/\- *def* inv'
- \- *def* omega
- \+/\- *def* surreal.equiv
- \+/\- *def* mk
- \+/\- *def* lift
- \+/\- *def* lift₂



## [2019-09-17 15:50:00](https://github.com/leanprover-community/mathlib/commit/19a246c)
fix(category_theory): require morphisms are in Type, again ([#1412](https://github.com/leanprover-community/mathlib/pull/1412))
* chore(category_theory): require morphisms live in Type
* move back to Type
* fixes
#### Estimated changes
modified src/algebraic_geometry/presheafed_space.lean

modified src/algebraic_geometry/stalks.lean

modified src/category_theory/adjunction/limits.lean

modified src/category_theory/category/Cat.lean

modified src/category_theory/category/Groupoid.lean

modified src/category_theory/category/default.lean

modified src/category_theory/comma.lean
- \+/\- *def* over
- \+/\- *def* under
- \+/\- *def* over
- \+/\- *def* under

modified src/category_theory/conj.lean

modified src/category_theory/core.lean

modified src/category_theory/currying.lean

modified src/category_theory/discrete_category.lean

modified src/category_theory/endomorphism.lean
- \+/\- *def* End
- \+/\- *def* Aut
- \+/\- *def* End
- \+/\- *def* Aut

modified src/category_theory/functor_category.lean

modified src/category_theory/groupoid.lean

modified src/category_theory/hom_functor.lean

modified src/category_theory/limits/cones.lean

modified src/category_theory/limits/functor_category.lean

modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.pre_post
- \+/\- *lemma* limit.map_post
- \+/\- *lemma* colimit.pre_post
- \+/\- *lemma* colimit.map_post
- \+/\- *lemma* limit.pre_post
- \+/\- *lemma* limit.map_post
- \+/\- *lemma* colimit.pre_post
- \+/\- *lemma* colimit.map_post
- \+/\- *def* of_faithful
- \+/\- *def* of_faithful
- \+/\- *def* of_faithful
- \+/\- *def* of_faithful

modified src/category_theory/limits/opposites.lean

modified src/category_theory/limits/over.lean

modified src/category_theory/limits/preserves.lean

modified src/category_theory/limits/shapes/binary_products.lean

modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean

modified src/category_theory/limits/shapes/equalizers.lean

modified src/category_theory/limits/shapes/finite_limits.lean

modified src/category_theory/limits/shapes/finite_products.lean

modified src/category_theory/limits/shapes/products.lean

modified src/category_theory/limits/shapes/pullbacks.lean

modified src/category_theory/limits/shapes/terminal.lean

modified src/category_theory/monad/limits.lean

modified src/category_theory/monoidal/category.lean

modified src/category_theory/monoidal/functor.lean
- \+/\- *def* μ_nat_iso
- \+/\- *def* μ_nat_iso

modified src/category_theory/monoidal/of_has_finite_products.lean

modified src/category_theory/monoidal/types.lean

modified src/category_theory/natural_transformation.lean

modified src/category_theory/pempty.lean
- \+/\- *def* empty
- \+/\- *def* empty

modified src/category_theory/products/associator.lean

modified src/category_theory/products/basic.lean

modified src/category_theory/products/bifunctor.lean

modified src/category_theory/sums/associator.lean

modified src/category_theory/sums/basic.lean

modified src/category_theory/types.lean
- \+/\- *lemma* types_hom
- \+/\- *lemma* types_id
- \+/\- *lemma* types_comp
- \+/\- *lemma* types_hom
- \+/\- *lemma* types_id
- \+/\- *lemma* types_comp

modified src/category_theory/yoneda.lean
- \+/\- *def* yoneda
- \+/\- *def* coyoneda
- \+/\- *def* yoneda_sections
- \+/\- *def* yoneda_sections_small
- \+/\- *def* yoneda
- \+/\- *def* coyoneda
- \+/\- *def* yoneda_sections
- \+/\- *def* yoneda_sections_small

modified src/topology/category/Top/open_nhds.lean

modified src/topology/category/Top/opens.lean

modified src/topology/sheaves/presheaf.lean

modified src/topology/sheaves/stalks.lean



## [2019-09-17 05:06:09](https://github.com/leanprover-community/mathlib/commit/ab2c546)
feat(data/quot): define `quotient.map` and `quotient.map₂` (dep: 1441) ([#1442](https://github.com/leanprover-community/mathlib/pull/1442))
* chore(algebra/group,logic/relator): review some explicit/implicit arguments
* ring_hom.ext too
* feat(data/quot): define `quotient.map` and `quotient.map₂`
* Add comments
* Fix a typo
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
modified src/data/quot.lean

modified src/logic/relator.lean



## [2019-09-17 02:44:20](https://github.com/leanprover-community/mathlib/commit/d4cc179)
feat(logic/basic): eq_iff_eq_cancel ([#1447](https://github.com/leanprover-community/mathlib/pull/1447))
* feat(logic/basic): eq_iff_eq_cancel
These lemmas or not meant for `rw` but to be applied, as a sort of congruence lemma.
* State lemmas as iff
* Make'm simp
#### Estimated changes
modified src/logic/basic.lean
- \+ *lemma* eq_iff_eq_cancel_left
- \+ *lemma* eq_iff_eq_cancel_right



## [2019-09-17 00:58:35](https://github.com/leanprover-community/mathlib/commit/c412527)
feat(data/list/sort): ordered_insert lemmas ([#1437](https://github.com/leanprover-community/mathlib/pull/1437))
* feat(data/list/sort): ordered_insert lemmas
* add a lemma about L.tail.count
#### Estimated changes
modified src/data/list/basic.lean
- \+ *theorem* count_tail

modified src/data/list/sort.lean
- \+ *lemma* ordered_insert_nil
- \+ *theorem* sorted.tail
- \+ *theorem* ordered_insert_length
- \+ *theorem* ordered_insert_count



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
modified src/algebra/ring.lean
- \+ *lemma* dvd_add_self_left
- \+ *lemma* dvd_add_self_right

modified src/data/nat/basic.lean



## [2019-09-16 22:49:24](https://github.com/leanprover-community/mathlib/commit/929c186)
fix(docs/tutorial/category_theory): fix import ([#1440](https://github.com/leanprover-community/mathlib/pull/1440))
* fix(docs/tutorial/category_theory): fix import
* fix(.travis.yml): Travis stages to build docs/
* cache docs/ in travis build
#### Estimated changes
modified .travis.yml

modified docs/tutorial/category_theory/calculating_colimits_in_Top.lean



## [2019-09-16 21:07:29](https://github.com/leanprover-community/mathlib/commit/a3ccc7a)
chore(category_theory/notation): update notation for prod and coprod ([#1413](https://github.com/leanprover-community/mathlib/pull/1413))
* updating notation for categorical prod and coprod
* update notation
#### Estimated changes
modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *def* prod.braiding
- \+/\- *def* coprod.braiding
- \+/\- *def* prod.braiding
- \+/\- *def* coprod.braiding



## [2019-09-16 16:01:04+02:00](https://github.com/leanprover-community/mathlib/commit/b2b0de4)
feat(algebra/group/basic): mul_left_eq_self etc ([#1446](https://github.com/leanprover-community/mathlib/pull/1446))
Simp-lemmas for groups of the form a * b = b ↔ a = 1.
#### Estimated changes
modified src/algebra/group/basic.lean
- \+ *lemma* mul_left_eq_self
- \+ *lemma* mul_right_eq_self



## [2019-09-16 09:26:53](https://github.com/leanprover-community/mathlib/commit/d7f0e68)
chore(algebra/group,logic/relator): review some explicit/implicit args ([#1441](https://github.com/leanprover-community/mathlib/pull/1441))
* chore(algebra/group,logic/relator): review some explicit/implicit arguments
* ring_hom.ext too
#### Estimated changes
modified src/algebra/group/hom.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

modified src/algebra/group/units.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext

modified src/algebra/ring.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext

modified src/data/list/basic.lean

modified src/data/multiset.lean

modified src/logic/relator.lean



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
modified src/algebra/archimedean.lean
- \+ *lemma* pow_unbounded_of_one_lt
- \- *lemma* pow_unbounded_of_gt_one

modified src/algebra/field_power.lean
- \+/\- *lemma* fpow_nonneg_of_nonneg
- \+/\- *lemma* fpow_pos_of_pos
- \+/\- *lemma* pow_le_max_of_min_le
- \+/\- *lemma* fpow_le_one_of_nonpos
- \+ *lemma* one_le_fpow_of_nonneg
- \+/\- *lemma* one_lt_pow
- \+/\- *lemma* one_lt_fpow
- \+/\- *lemma* fpow_nonneg_of_nonneg
- \+/\- *lemma* fpow_pos_of_pos
- \+/\- *lemma* pow_le_max_of_min_le
- \+/\- *lemma* fpow_le_one_of_nonpos
- \- *lemma* fpow_ge_one_of_nonneg
- \+/\- *lemma* one_lt_pow
- \+/\- *lemma* one_lt_fpow

modified src/algebra/floor.lean
- \+/\- *lemma* ceil_nonneg
- \+/\- *lemma* ceil_nonneg

modified src/algebra/gcd_domain.lean
- \+/\- *theorem* gcd_pos_of_non_zero_left
- \+/\- *theorem* gcd_pos_of_non_zero_right
- \+/\- *theorem* gcd_pos_of_non_zero_left
- \+/\- *theorem* gcd_pos_of_non_zero_right

modified src/algebra/group_power.lean
- \+/\- *theorem* pow_sub
- \+/\- *theorem* add_monoid.smul_sub
- \+ *theorem* one_add_mul_le_pow
- \+ *theorem* one_add_sub_mul_le_pow
- \+/\- *theorem* pow_sub
- \+/\- *theorem* add_monoid.smul_sub
- \- *theorem* pow_ge_one_add_mul
- \- *theorem* pow_ge_one_add_sub_mul

modified src/algebra/order.lean
- \+/\- *lemma* ne_iff_lt_or_gt
- \+/\- *lemma* ne_iff_lt_or_gt

modified src/algebra/order_functions.lean
- \+/\- *lemma* abs_eq
- \+/\- *lemma* abs_eq

modified src/algebra/ordered_group.lean
- \+/\- *lemma* le_add_of_nonneg_right'
- \+/\- *lemma* le_add_of_nonneg_left'
- \+/\- *lemma* le_add_of_nonneg_right'
- \+/\- *lemma* le_add_of_nonneg_left'

modified src/algebra/ordered_ring.lean
- \+ *lemma* mul_nonneg'
- \+ *lemma* mul_pos'
- \+/\- *lemma* le_mul_iff_one_le_left
- \+/\- *lemma* lt_mul_iff_one_lt_left
- \+/\- *lemma* le_mul_iff_one_le_right
- \+/\- *lemma* lt_mul_iff_one_lt_right
- \+ *lemma* lt_mul_of_one_lt_right'
- \+ *lemma* le_mul_of_one_le_right'
- \+ *lemma* le_mul_of_one_le_left'
- \+/\- *lemma* mul_le_iff_le_one_left
- \+/\- *lemma* mul_lt_iff_lt_one_left
- \+/\- *lemma* mul_le_iff_le_one_right
- \+/\- *lemma* mul_lt_iff_lt_one_right
- \- *lemma* zero_le_mul
- \+/\- *lemma* le_mul_iff_one_le_left
- \+/\- *lemma* lt_mul_iff_one_lt_left
- \+/\- *lemma* le_mul_iff_one_le_right
- \+/\- *lemma* lt_mul_iff_one_lt_right
- \- *lemma* lt_mul_of_gt_one_right'
- \- *lemma* le_mul_of_ge_one_right'
- \- *lemma* le_mul_of_ge_one_left'
- \+/\- *lemma* mul_le_iff_le_one_left
- \+/\- *lemma* mul_lt_iff_lt_one_left
- \+/\- *lemma* mul_le_iff_le_one_right
- \+/\- *lemma* mul_lt_iff_lt_one_right

modified src/analysis/convex.lean

modified src/analysis/specific_limits.lean

modified src/computability/partrec_code.lean

modified src/computability/primrec.lean

modified src/data/equiv/fin.lean

modified src/data/fin.lean
- \+/\- *lemma* sub_nat_val
- \+/\- *lemma* add_nat_val
- \+/\- *lemma* sub_nat_val
- \+/\- *lemma* add_nat_val
- \+/\- *def* sub_nat
- \+/\- *def* sub_nat

modified src/data/finset.lean
- \+ *lemma* filter_le_of_le_bot
- \+ *lemma* filter_le_of_top_le
- \+ *lemma* filter_le_of_le
- \+ *lemma* filter_le
- \- *lemma* filter_ge_of_le_bot
- \- *lemma* filter_ge_of_top_le
- \- *lemma* filter_ge_of_ge
- \- *lemma* filter_ge
- \+/\- *theorem* pred_singleton
- \+/\- *theorem* pred_singleton

modified src/data/fintype.lean
- \+ *lemma* fintype.exists_ne_of_one_lt_card
- \- *lemma* fintype.exists_ne_of_card_gt_one

modified src/data/fp/basic.lean

modified src/data/int/basic.lean
- \+/\- *theorem* neg_succ_of_nat_div
- \+/\- *theorem* div_of_neg_of_pos
- \+/\- *theorem* div_neg'
- \+/\- *theorem* neg_succ_of_nat_mod
- \+/\- *theorem* mod_nonneg
- \+/\- *theorem* mod_lt_of_pos
- \+/\- *theorem* mul_div_mul_of_pos
- \+/\- *theorem* mul_div_mul_of_pos_left
- \+/\- *theorem* mul_mod_mul_of_pos
- \+/\- *theorem* lt_div_add_one_mul_self
- \+/\- *theorem* div_le_self
- \+/\- *theorem* dvd_antisymm
- \+/\- *theorem* le_of_dvd
- \+/\- *theorem* eq_one_of_dvd_one
- \+/\- *theorem* eq_one_of_mul_eq_one_right
- \+/\- *theorem* eq_one_of_mul_eq_one_left
- \+/\- *theorem* div_pos_of_pos_of_dvd
- \+/\- *theorem* neg_succ_of_nat_div
- \+/\- *theorem* div_of_neg_of_pos
- \+/\- *theorem* div_neg'
- \+/\- *theorem* neg_succ_of_nat_mod
- \+/\- *theorem* mod_nonneg
- \+/\- *theorem* mod_lt_of_pos
- \+/\- *theorem* mul_div_mul_of_pos
- \+/\- *theorem* mul_div_mul_of_pos_left
- \+/\- *theorem* mul_mod_mul_of_pos
- \+/\- *theorem* lt_div_add_one_mul_self
- \+/\- *theorem* div_le_self
- \+/\- *theorem* dvd_antisymm
- \+/\- *theorem* le_of_dvd
- \+/\- *theorem* eq_one_of_dvd_one
- \+/\- *theorem* eq_one_of_mul_eq_one_right
- \+/\- *theorem* eq_one_of_mul_eq_one_left
- \+/\- *theorem* div_pos_of_pos_of_dvd

modified src/data/int/modeq.lean
- \+/\- *lemma* exists_unique_equiv
- \+/\- *lemma* exists_unique_equiv_nat
- \+/\- *lemma* exists_unique_equiv
- \+/\- *lemma* exists_unique_equiv_nat

modified src/data/list/basic.lean
- \+ *lemma* filter_le_of_le_bot
- \+ *lemma* filter_le_of_top_le
- \+ *lemma* filter_le_of_le
- \+ *lemma* filter_le
- \- *lemma* filter_ge_of_le_bot
- \- *lemma* filter_ge_of_top_le
- \- *lemma* filter_ge_of_ge
- \- *lemma* filter_ge
- \+ *theorem* nth_len_le
- \+ *theorem* take_all_of_le
- \+/\- *theorem* pred_singleton
- \- *theorem* nth_ge_len
- \- *theorem* take_all_of_ge
- \+/\- *theorem* pred_singleton

modified src/data/multiset.lean
- \+ *lemma* filter_le_of_le_bot
- \+ *lemma* filter_le_of_top_le
- \+ *lemma* filter_le_of_le
- \+ *lemma* filter_le
- \- *lemma* filter_ge_of_le_bot
- \- *lemma* filter_ge_of_top_le
- \- *lemma* filter_ge_of_ge
- \- *lemma* filter_ge
- \+/\- *theorem* pred_singleton
- \+/\- *theorem* pred_singleton

modified src/data/nat/basic.lean
- \+/\- *lemma* le_mul_of_pos_left
- \+/\- *lemma* le_mul_of_pos_right
- \+/\- *lemma* pow_lt_pow_succ
- \+/\- *lemma* lt_pow_self
- \+/\- *lemma* not_pos_pow_dvd
- \+/\- *lemma* le_induction
- \+/\- *lemma* le_mul_of_pos_left
- \+/\- *lemma* le_mul_of_pos_right
- \+/\- *lemma* pow_lt_pow_succ
- \+/\- *lemma* lt_pow_self
- \+/\- *lemma* not_pos_pow_dvd
- \+/\- *lemma* le_induction
- \+/\- *theorem* pos_iff_ne_zero
- \+/\- *theorem* add_pos_left
- \+/\- *theorem* add_pos_right
- \+/\- *theorem* add_pos_iff_pos_or_pos
- \+/\- *theorem* pow_pos
- \+/\- *theorem* fact_pos
- \+/\- *theorem* dvd_fact
- \+/\- *theorem* pos_iff_ne_zero
- \+/\- *theorem* add_pos_left
- \+/\- *theorem* add_pos_right
- \+/\- *theorem* add_pos_iff_pos_or_pos
- \+/\- *theorem* pow_pos
- \+/\- *theorem* fact_pos
- \+/\- *theorem* dvd_fact

modified src/data/nat/cast.lean
- \+/\- *theorem* cast_pred
- \+/\- *theorem* cast_pred

modified src/data/nat/dist.lean
- \+/\- *theorem* dist_pos_of_ne
- \+/\- *theorem* dist_pos_of_ne

modified src/data/nat/gcd.lean
- \+/\- *theorem* gcd_le_left
- \+/\- *theorem* gcd_le_right
- \+/\- *theorem* gcd_pos_of_pos_left
- \+/\- *theorem* gcd_pos_of_pos_right
- \+/\- *theorem* coprime_of_dvd
- \+/\- *theorem* coprime_div_gcd_div_gcd
- \+/\- *theorem* not_coprime_of_dvd_of_dvd
- \+/\- *theorem* exists_coprime
- \+/\- *theorem* exists_coprime'
- \+/\- *theorem* gcd_le_left
- \+/\- *theorem* gcd_le_right
- \+/\- *theorem* gcd_pos_of_pos_left
- \+/\- *theorem* gcd_pos_of_pos_right
- \+/\- *theorem* coprime_of_dvd
- \+/\- *theorem* coprime_div_gcd_div_gcd
- \+/\- *theorem* not_coprime_of_dvd_of_dvd
- \+/\- *theorem* exists_coprime
- \+/\- *theorem* exists_coprime'

modified src/data/nat/modeq.lean

modified src/data/nat/pairing.lean
- \+/\- *theorem* unpair_lt
- \+/\- *theorem* unpair_lt

modified src/data/nat/parity.lean
- \+/\- *theorem* even_sub
- \+/\- *theorem* even_sub

modified src/data/nat/prime.lean
- \+ *theorem* prime.two_le
- \+ *theorem* prime.one_lt
- \+/\- *theorem* prime_def_lt
- \+/\- *theorem* prime_def_lt'
- \+/\- *theorem* prime_def_le_sqrt
- \+/\- *theorem* prime.pos
- \+/\- *theorem* prime.pred_pos
- \+ *theorem* dvd_prime_two_le
- \+/\- *theorem* exists_dvd_of_not_prime
- \+/\- *theorem* exists_dvd_of_not_prime2
- \+/\- *theorem* exists_prime_and_dvd
- \+/\- *theorem* exists_infinite_primes
- \- *theorem* prime.ge_two
- \- *theorem* prime.gt_one
- \+/\- *theorem* prime_def_lt
- \+/\- *theorem* prime_def_lt'
- \+/\- *theorem* prime_def_le_sqrt
- \+/\- *theorem* prime.pos
- \+/\- *theorem* prime.pred_pos
- \- *theorem* dvd_prime_ge_two
- \+/\- *theorem* exists_dvd_of_not_prime
- \+/\- *theorem* exists_dvd_of_not_prime2
- \+/\- *theorem* exists_prime_and_dvd
- \+/\- *theorem* exists_infinite_primes
- \+/\- *def* prime
- \+/\- *def* prime

modified src/data/nat/sqrt.lean
- \+/\- *theorem* sqrt_lt_self
- \+/\- *theorem* sqrt_pos
- \+/\- *theorem* sqrt_lt_self
- \+/\- *theorem* sqrt_pos

modified src/data/nat/totient.lean

modified src/data/num/lemmas.lean

modified src/data/padics/padic_norm.lean

modified src/data/padics/padic_numbers.lean

modified src/data/pnat/basic.lean
- \+/\- *theorem* pos
- \+/\- *theorem* to_pnat'_coe
- \+/\- *theorem* sub_coe
- \+/\- *theorem* pos
- \+/\- *theorem* to_pnat'_coe
- \+/\- *theorem* sub_coe
- \+/\- *def* pnat
- \+/\- *def* to_pnat
- \+/\- *def* pnat
- \+/\- *def* to_pnat

modified src/data/polynomial.lean

modified src/data/rat/basic.lean

modified src/data/rat/order.lean
- \+/\- *theorem* mk_nonneg
- \+/\- *theorem* mk_nonneg

modified src/data/real/irrational.lean

modified src/data/real/nnreal.lean

modified src/data/zmod/basic.lean

modified src/data/zmod/quadratic_reciprocity.lean

modified src/data/zsqrtd/basic.lean

modified src/data/zsqrtd/gaussian_int.lean

modified src/group_theory/perm/sign.lean

modified src/group_theory/sylow.lean

modified src/number_theory/sum_two_squares.lean



## [2019-09-13 07:38:04](https://github.com/leanprover-community/mathlib/commit/e3234f0)
feat(algebra/ring): add coercions from →+* to →* and →+ ([#1435](https://github.com/leanprover-community/mathlib/pull/1435))
* feat(algebra/ring): add coercions from →+* to →* and →+
* two lemmas simplifying casts
* add squash_cast attributes
#### Estimated changes
modified src/algebra/ring.lean
- \+ *lemma* coe_monoid_hom
- \+ *lemma* coe_add_monoid_hom



## [2019-09-11 23:51:16](https://github.com/leanprover-community/mathlib/commit/590fb89)
chore(category_theory/functor_category): improve comment warning about hcomp_assoc [ci skip] ([#1434](https://github.com/leanprover-community/mathlib/pull/1434))
* expanding comment
* no scare quotes
#### Estimated changes
modified src/category_theory/functor_category.lean



## [2019-09-11 17:42:41](https://github.com/leanprover-community/mathlib/commit/140a606)
feat(well_founded_tactics):  patch default_dec_tac ([#1419](https://github.com/leanprover-community/mathlib/pull/1419))
* let simp flip inequalities
* feat(well_founded_tactics):  patch default_dec_tac
* Keeley's suggested syntax, and adding to the docs
* more
* add docs
#### Estimated changes
modified docs/extras/well_founded_recursion.md

modified docs/tactics.md

modified src/computability/partrec_code.lean

modified src/data/hash_map.lean

modified src/data/list/basic.lean

modified src/data/list/sort.lean

modified src/data/nat/basic.lean
- \+ *lemma* succ_pos'

modified src/data/vector2.lean
- \+/\- *lemma* nth_map
- \+/\- *lemma* nth_map

modified src/set_theory/lists.lean

modified src/tactic/basic.lean

created src/tactic/well_founded_tactics.lean



## [2019-09-11 12:46:21](https://github.com/leanprover-community/mathlib/commit/e27142a)
chore(*): renaming files constructing category instances ([#1432](https://github.com/leanprover-community/mathlib/pull/1432))
#### Estimated changes
deleted src/algebra/CommRing/default.lean

deleted src/algebra/Mon/default.lean

renamed src/algebra/CommRing/adjunctions.lean to src/algebra/category/CommRing/adjunctions.lean

renamed src/algebra/CommRing/basic.lean to src/algebra/category/CommRing/basic.lean

renamed src/algebra/CommRing/colimits.lean to src/algebra/category/CommRing/colimits.lean

created src/algebra/category/CommRing/default.lean

renamed src/algebra/CommRing/limits.lean to src/algebra/category/CommRing/limits.lean

renamed src/group_theory/category.lean to src/algebra/category/Group.lean

renamed src/algebra/Mon/basic.lean to src/algebra/category/Mon/basic.lean

renamed src/algebra/Mon/colimits.lean to src/algebra/category/Mon/colimits.lean

created src/algebra/category/Mon/default.lean

modified src/algebraic_geometry/presheafed_space.lean

modified src/algebraic_geometry/stalks.lean

modified src/category/fold.lean

renamed src/category_theory/Cat.lean to src/category_theory/category/Cat.lean

renamed src/category_theory/groupoid_category.lean to src/category_theory/category/Groupoid.lean

renamed src/category_theory/instances/kleisli.lean to src/category_theory/category/Kleisli.lean

renamed src/category_theory/instances/rel.lean to src/category_theory/category/Rel.lean

renamed src/category_theory/category.lean to src/category_theory/category/default.lean

modified src/category_theory/single_obj.lean

renamed src/measure_theory/Meas.lean to src/measure_theory/category/Meas.lean

modified src/measure_theory/giry_monad.lean

deleted src/topology/Top/default.lean

deleted src/topology/algebra/TopCommRing/default.lean

renamed src/topology/Top/adjunctions.lean to src/topology/category/Top/adjunctions.lean

renamed src/topology/Top/basic.lean to src/topology/category/Top/basic.lean

created src/topology/category/Top/default.lean

renamed src/topology/Top/epi_mono.lean to src/topology/category/Top/epi_mono.lean

renamed src/topology/Top/limits.lean to src/topology/category/Top/limits.lean

renamed src/topology/Top/open_nhds.lean to src/topology/category/Top/open_nhds.lean

renamed src/topology/Top/opens.lean to src/topology/category/Top/opens.lean

renamed src/topology/algebra/TopCommRing/basic.lean to src/topology/category/TopCommRing.lean

renamed src/topology/uniform_space/UniformSpace.lean to src/topology/category/UniformSpace.lean

renamed src/topology/Top/presheaf.lean to src/topology/sheaves/presheaf.lean

renamed src/topology/Top/presheaf_of_functions.lean to src/topology/sheaves/presheaf_of_functions.lean

renamed src/topology/Top/stalks.lean to src/topology/sheaves/stalks.lean



## [2019-09-11 03:52:18](https://github.com/leanprover-community/mathlib/commit/8a5156f)
fix(algebra/*/colimits): avoid explicit `infer_instance` ([#1430](https://github.com/leanprover-community/mathlib/pull/1430))
With an explicit universe level Lean can do it automatically.
#### Estimated changes
modified src/algebra/CommRing/colimits.lean

modified src/algebra/Mon/colimits.lean



## [2019-09-11 01:49:04](https://github.com/leanprover-community/mathlib/commit/45fe081)
feat(logic): make some decidability proofs [inline] ([#1393](https://github.com/leanprover-community/mathlib/pull/1393))
* feat(logic): make some decidability proofs [inline]
* inline more decidability proofs
* test
* import logic.basic in test
#### Estimated changes
modified src/logic/basic.lean

created test/logic_inline.lean



## [2019-09-10 23:38:55](https://github.com/leanprover-community/mathlib/commit/8e46fa5)
chore(algebra/group/to_additive): map_namespace should make a meta constant ([#1409](https://github.com/leanprover-community/mathlib/pull/1409))
* chore(algebra/group/to_additive): map_namespace should make a meta constance
`map_namespace` now produces a `meta constant` instead of a constant. This means that after importing `group_theory/coset` and typing `#print axioms`, `quotient_group._to_additive` is not in the list, since it is now a `meta constant`. This is a little bit neater, and it doesn't look like we're adding any axioms.
* Update to_additive.lean
* Update to_additive.lean
#### Estimated changes
modified src/algebra/group/to_additive.lean



## [2019-09-10 22:44:22](https://github.com/leanprover-community/mathlib/commit/e2f904e)
feat(tactic/auto_cases): run auto_cases on false and psigma ([#1428](https://github.com/leanprover-community/mathlib/pull/1428))
#### Estimated changes
modified src/tactic/auto_cases.lean



## [2019-09-10 19:55:17](https://github.com/leanprover-community/mathlib/commit/c87ec0e)
feat(tactic/{abel,ring}): state conditions of tactics more precisely ([#1423](https://github.com/leanprover-community/mathlib/pull/1423))
#### Estimated changes
modified docs/tactics.md

modified src/tactic/abel.lean

modified src/tactic/ring.lean

created test/abel.lean



## [2019-09-10 15:33:29](https://github.com/leanprover-community/mathlib/commit/2dd6398)
let simp flip inequalities ([#1418](https://github.com/leanprover-community/mathlib/pull/1418))
#### Estimated changes
modified src/algebra/order.lean
- \+ *lemma* ge_iff_le
- \+ *lemma* gt_iff_lt

modified src/data/rat/order.lean

modified src/number_theory/pell.lean

modified src/tactic/linarith.lean



## [2019-09-10 11:26:37](https://github.com/leanprover-community/mathlib/commit/0935e8b)
feat(algebra/group/units): add some lemmas about `divp` ([#1388](https://github.com/leanprover-community/mathlib/pull/1388))
* feat(algebra/group/units): add some lemmas about `divp`
* Rename lemmas, add new ones
#### Estimated changes
modified src/algebra/group/units.lean
- \+ *theorem* divp_eq_divp_iff
- \+ *theorem* divp_mul_divp



## [2019-09-10 09:32:30](https://github.com/leanprover-community/mathlib/commit/fe1575a)
chore(topology): sanity_check pass ([#1416](https://github.com/leanprover-community/mathlib/pull/1416))
* chore(topology): sanity_check pass
* improvement
* avoid _inst_3 to recover instance
#### Estimated changes
modified src/analysis/asymptotics.lean
- \+/\- *theorem* is_o_iff_tendsto
- \+/\- *theorem* is_o_iff_tendsto

modified src/analysis/convex.lean
- \+/\- *lemma* convex_on_sum
- \+/\- *lemma* convex_on_sum

modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *theorem* is_O_comp
- \+/\- *theorem* is_O_comp

modified src/analysis/normed_space/operator_norm.lean
- \+/\- *theorem* is_O_comp
- \+/\- *theorem* is_O_comp

modified src/logic/basic.lean
- \+/\- *theorem* not_iff
- \+/\- *theorem* ball_of_forall
- \+/\- *theorem* not_iff
- \+/\- *theorem* ball_of_forall

modified src/meta/rb_map.lean

modified src/order/basic.lean
- \+ *lemma* antisymm_of_asymm
- \+/\- *lemma* dense_or_discrete
- \+/\- *lemma* dense_or_discrete
- \+/\- *theorem* comp_le_comp_left_of_monotone
- \+/\- *theorem* comp_le_comp_left_of_monotone
- \- *def* antisymm_of_asymm

modified src/order/bounded_lattice.lean
- \+/\- *theorem* top_ne_coe
- \+/\- *theorem* coe_ne_top
- \+/\- *theorem* top_ne_coe
- \+/\- *theorem* coe_ne_top

modified src/order/complete_lattice.lean
- \+ *lemma* has_Inf_to_nonempty
- \+ *lemma* has_Sup_to_nonempty
- \+/\- *theorem* insert_of_has_insert
- \+/\- *theorem* insert_of_has_insert
- \- *def* has_Inf_to_nonempty
- \- *def* has_Sup_to_nonempty

modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* cInf_interval
- \+/\- *lemma* cSup_interval
- \+/\- *lemma* cInf_interval
- \+/\- *lemma* cSup_interval

modified src/order/filter/partial.lean
- \+ *lemma* mem_rcomap'
- \+ *lemma* mem_pmap
- \- *def* mem_rcomap'
- \- *def* mem_pmap

modified src/order/liminf_limsup.lean
- \+/\- *lemma* limsup_le_limsup
- \+/\- *lemma* liminf_le_liminf
- \+/\- *lemma* liminf_le_limsup
- \+/\- *lemma* limsup_le_limsup
- \+/\- *lemma* liminf_le_liminf
- \+/\- *lemma* liminf_le_limsup

modified src/order/order_iso.lean
- \+/\- *theorem* well_founded_iff_no_descending_seq
- \- *theorem* nat_lt
- \- *theorem* nat_gt
- \+/\- *theorem* well_founded_iff_no_descending_seq
- \- *theorem* sum_lex_congr
- \- *theorem* prod_lex_congr
- \+ *def* nat_lt
- \+ *def* nat_gt
- \+ *def* sum_lex_congr
- \+ *def* prod_lex_congr

modified src/topology/algebra/group.lean
- \+/\- *lemma* quotient_group_saturate
- \+ *lemma* nhds_is_mul_hom
- \+/\- *lemma* quotient_group_saturate
- \- *def* nhds_is_mul_hom

modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* has_sum_hom
- \+/\- *lemma* has_sum_add
- \+/\- *lemma* summable_add
- \+/\- *lemma* has_sum_sum
- \+/\- *lemma* summable_sum
- \+/\- *lemma* tsum_add
- \+/\- *lemma* tsum_sum
- \+/\- *lemma* tsum_sigma
- \+/\- *lemma* has_sum_add
- \+/\- *lemma* summable_add
- \+/\- *lemma* has_sum_sum
- \+/\- *lemma* summable_sum
- \+/\- *lemma* has_sum_hom
- \+/\- *lemma* tsum_add
- \+/\- *lemma* tsum_sum
- \+/\- *lemma* tsum_sigma

modified src/topology/algebra/module.lean
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_add'
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_neg'
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub'
- \+/\- *lemma* coe_apply
- \+/\- *lemma* coe_apply'
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_add'
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_neg'
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub'
- \+/\- *lemma* coe_apply
- \+/\- *lemma* coe_apply'
- \+/\- *def* scalar_prod_space_iso
- \+/\- *def* scalar_prod_space_iso

modified src/topology/algebra/monoid.lean
- \+/\- *lemma* is_submonoid.mem_nhds_one
- \+/\- *lemma* is_submonoid.mem_nhds_one

modified src/topology/algebra/ordered.lean

modified src/topology/algebra/ring.lean
- \+/\- *lemma* quotient_ring_saturate
- \+/\- *lemma* quotient_ring_saturate

modified src/topology/algebra/uniform_group.lean

modified src/topology/bases.lean

modified src/topology/basic.lean
- \+/\- *lemma* tendsto_pure_nhds
- \+/\- *lemma* mem_closure
- \+/\- *lemma* tendsto_pure_nhds
- \+/\- *lemma* mem_closure

modified src/topology/constructions.lean
- \+/\- *lemma* prod_generate_from_generate_from_eq
- \+/\- *lemma* prod_eq_generate_from
- \+/\- *lemma* mem_closure2
- \+/\- *lemma* is_closed_prod
- \+/\- *lemma* dense_range_prod
- \+/\- *lemma* is_closed_diagonal
- \+/\- *lemma* is_closed_eq
- \+/\- *lemma* diagonal_eq_range_diagonal_map
- \+/\- *lemma* prod_subset_compl_diagonal_iff_disjoint
- \+/\- *lemma* locally_compact_of_compact_nhds
- \+/\- *lemma* normal_of_compact_t2
- \+/\- *lemma* continuous_at_subtype_val
- \+/\- *lemma* tendsto_subtype_rng
- \+/\- *lemma* tendsto_cons
- \+/\- *lemma* tendsto_cons_iff
- \+/\- *lemma* tendsto_nhds
- \+/\- *lemma* continuous_at_length
- \+/\- *lemma* tendsto_insert_nth
- \+/\- *lemma* is_closed_property
- \+/\- *lemma* prod_generate_from_generate_from_eq
- \+/\- *lemma* prod_eq_generate_from
- \+/\- *lemma* mem_closure2
- \+/\- *lemma* is_closed_prod
- \+/\- *lemma* dense_range_prod
- \+/\- *lemma* is_closed_diagonal
- \+/\- *lemma* is_closed_eq
- \+/\- *lemma* diagonal_eq_range_diagonal_map
- \+/\- *lemma* prod_subset_compl_diagonal_iff_disjoint
- \+/\- *lemma* locally_compact_of_compact_nhds
- \+/\- *lemma* normal_of_compact_t2
- \+/\- *lemma* continuous_at_subtype_val
- \+/\- *lemma* tendsto_subtype_rng
- \+/\- *lemma* tendsto_cons
- \+/\- *lemma* tendsto_cons_iff
- \+/\- *lemma* tendsto_nhds
- \+/\- *lemma* continuous_at_length
- \+/\- *lemma* tendsto_insert_nth
- \+/\- *lemma* is_closed_property
- \+/\- *def* subtype_emb
- \+/\- *def* subtype_emb

modified src/topology/maps.lean
- \+/\- *lemma* inducing.nhds_eq_comap
- \+/\- *lemma* inducing.map_nhds_eq
- \+ *lemma* embedding.mk'
- \+/\- *lemma* embedding.map_nhds_eq
- \- *lemma* dense_range.inhabited
- \+/\- *lemma* inducing.nhds_eq_comap
- \+/\- *lemma* inducing.map_nhds_eq
- \+/\- *lemma* embedding.map_nhds_eq
- \+ *def* dense_range.inhabited
- \- *def* embedding.mk'

modified src/topology/metric_space/basic.lean
- \+/\- *theorem* subtype.dist_eq
- \+/\- *theorem* subtype.dist_eq

modified src/topology/metric_space/cau_seq_filter.lean
- \+/\- *lemma* B2_pos
- \+/\- *lemma* B2_lim
- \+/\- *lemma* B2_pos
- \+/\- *lemma* B2_lim

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* subtype.edist_eq
- \+/\- *theorem* subtype.edist_eq

modified src/topology/metric_space/gluing.lean
- \+/\- *lemma* glue_dist_glued_points
- \+/\- *lemma* glue_dist_glued_points

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/isometry.lean
- \- *lemma* isometry.isometric_on_range
- \+ *def* isometry.isometric_on_range

modified src/topology/opens.lean
- \+ *lemma* gc
- \- *def* gc

modified src/topology/order.lean
- \+/\- *lemma* induced_compose
- \+ *lemma* continuous_iff_continuous_on_univ
- \+/\- *lemma* induced_compose
- \+/\- *theorem* principal_subtype
- \+/\- *theorem* continuous_within_at_iff_ptendsto_res
- \+/\- *theorem* principal_subtype
- \+/\- *theorem* continuous_within_at_iff_ptendsto_res
- \- *def* continuous_iff_continuous_on_univ

modified src/topology/separation.lean

modified src/topology/subset_properties.lean
- \+/\- *lemma* compact_univ
- \+/\- *lemma* compact_of_closed
- \+/\- *lemma* compact_image
- \+/\- *lemma* compact_range
- \+/\- *lemma* compact_univ
- \+/\- *lemma* compact_of_closed
- \+/\- *lemma* compact_image
- \+/\- *lemma* compact_range

modified src/topology/uniform_space/uniform_embedding.lean



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
modified src/data/bool.lean

modified src/data/list/defs.lean
- \+ *def* mmap_filter

modified src/meta/expr.lean

modified src/tactic/core.lean

modified src/tactic/sanity_check.lean

modified test/sanity_check.lean



## [2019-09-09 21:11:13](https://github.com/leanprover-community/mathlib/commit/228d5ba)
feat(algebra/big_operators): sum_eq_zero_iff_of_nonpos ([#1424](https://github.com/leanprover-community/mathlib/pull/1424))
* feat(algebra/big_operators): sum_eq_zero_iff_of_nonpos
* more order_dual instances
#### Estimated changes
modified src/algebra/big_operators.lean
- \+ *lemma* sum_eq_zero_iff_of_nonpos

modified src/algebra/ordered_group.lean



## [2019-09-08 16:37:05](https://github.com/leanprover-community/mathlib/commit/313fe11)
feat(algebra/floor): Split floor from archimedean file. ([#1372](https://github.com/leanprover-community/mathlib/pull/1372))
* feat(algebra/floor): Split floor from archimedean file.
* feat({algebra,rat}/floor): move lemmas/defs from rat.floor to algebra.floor
#### Estimated changes
modified src/algebra/archimedean.lean
- \- *lemma* abs_sub_lt_one_of_floor_eq_floor
- \- *lemma* floor_eq_iff
- \- *lemma* floor_add_fract
- \- *lemma* fract_add_floor
- \- *lemma* fract_zero
- \- *lemma* fract_coe
- \- *lemma* fract_floor
- \- *lemma* floor_fract
- \- *lemma* fract_fract
- \- *lemma* ceil_pos
- \- *lemma* ceil_nonneg
- \- *theorem* le_floor
- \- *theorem* floor_lt
- \- *theorem* floor_le
- \- *theorem* floor_nonneg
- \- *theorem* lt_succ_floor
- \- *theorem* lt_floor_add_one
- \- *theorem* sub_one_lt_floor
- \- *theorem* floor_coe
- \- *theorem* floor_zero
- \- *theorem* floor_one
- \- *theorem* floor_mono
- \- *theorem* floor_add_int
- \- *theorem* floor_sub_int
- \- *theorem* fract_nonneg
- \- *theorem* fract_lt_one
- \- *theorem* fract_eq_iff
- \- *theorem* fract_eq_fract
- \- *theorem* fract_add
- \- *theorem* fract_mul_nat
- \- *theorem* ceil_le
- \- *theorem* lt_ceil
- \- *theorem* le_ceil
- \- *theorem* ceil_coe
- \- *theorem* ceil_mono
- \- *theorem* ceil_add_int
- \- *theorem* ceil_sub_int
- \- *theorem* ceil_lt_add_one
- \- *theorem* ceil_zero
- \- *def* floor
- \- *def* fract
- \- *def* ceil

created src/algebra/floor.lean
- \+ *lemma* abs_sub_lt_one_of_floor_eq_floor
- \+ *lemma* floor_eq_iff
- \+ *lemma* floor_ring_unique
- \+ *lemma* floor_add_fract
- \+ *lemma* fract_add_floor
- \+ *lemma* fract_zero
- \+ *lemma* fract_coe
- \+ *lemma* fract_floor
- \+ *lemma* floor_fract
- \+ *lemma* fract_fract
- \+ *lemma* ceil_pos
- \+ *lemma* ceil_nonneg
- \+ *theorem* le_floor
- \+ *theorem* floor_lt
- \+ *theorem* floor_le
- \+ *theorem* floor_nonneg
- \+ *theorem* lt_succ_floor
- \+ *theorem* lt_floor_add_one
- \+ *theorem* sub_one_lt_floor
- \+ *theorem* floor_coe
- \+ *theorem* floor_zero
- \+ *theorem* floor_one
- \+ *theorem* floor_mono
- \+ *theorem* floor_add_int
- \+ *theorem* floor_sub_int
- \+ *theorem* fract_nonneg
- \+ *theorem* fract_lt_one
- \+ *theorem* fract_eq_iff
- \+ *theorem* fract_eq_fract
- \+ *theorem* fract_add
- \+ *theorem* fract_mul_nat
- \+ *theorem* ceil_le
- \+ *theorem* lt_ceil
- \+ *theorem* le_ceil
- \+ *theorem* ceil_coe
- \+ *theorem* ceil_mono
- \+ *theorem* ceil_add_int
- \+ *theorem* ceil_sub_int
- \+ *theorem* ceil_lt_add_one
- \+ *theorem* ceil_zero
- \+ *theorem* nat_ceil_le
- \+ *theorem* lt_nat_ceil
- \+ *theorem* le_nat_ceil
- \+ *theorem* nat_ceil_mono
- \+ *theorem* nat_ceil_coe
- \+ *theorem* nat_ceil_zero
- \+ *theorem* nat_ceil_add_nat
- \+ *theorem* nat_ceil_lt_add_one
- \+ *def* floor
- \+ *def* fract
- \+ *def* ceil
- \+ *def* nat_ceil

modified src/data/rat/floor.lean
- \- *lemma* floor_def
- \- *theorem* le_floor
- \- *theorem* floor_lt
- \- *theorem* floor_le
- \- *theorem* lt_succ_floor
- \- *theorem* floor_coe
- \- *theorem* floor_mono
- \- *theorem* floor_add_int
- \- *theorem* floor_sub_int
- \- *theorem* ceil_le
- \- *theorem* le_ceil
- \- *theorem* ceil_coe
- \- *theorem* ceil_mono
- \- *theorem* ceil_add_int
- \- *theorem* ceil_sub_int
- \- *theorem* nat_ceil_le
- \- *theorem* lt_nat_ceil
- \- *theorem* le_nat_ceil
- \- *theorem* nat_ceil_mono
- \- *theorem* nat_ceil_coe
- \- *theorem* nat_ceil_zero
- \- *theorem* nat_ceil_add_nat
- \- *theorem* nat_ceil_lt_add_one
- \- *def* floor
- \- *def* ceil
- \- *def* nat_ceil

modified src/tactic/norm_num.lean



## [2019-09-08 12:00:15](https://github.com/leanprover-community/mathlib/commit/37b6746)
feat(data/list/basic): make chain.nil a simp lemma ([#1414](https://github.com/leanprover-community/mathlib/pull/1414))
#### Estimated changes
modified src/data/list/basic.lean

modified src/data/list/defs.lean



## [2019-09-08 08:47:37](https://github.com/leanprover-community/mathlib/commit/6f7224c)
feat(data/list/defs): move list.sum to list/defs.lean ([#1415](https://github.com/leanprover-community/mathlib/pull/1415))
* feat(data/list/defs): move list.sum to list/defs.lean
* add comment
#### Estimated changes
modified src/data/list/basic.lean

modified src/data/list/defs.lean
- \+ *def* sum



## [2019-09-08 06:22:25](https://github.com/leanprover-community/mathlib/commit/8bdb147)
feat(topology/local_homeomorph): local homeomorphisms ([#1398](https://github.com/leanprover-community/mathlib/pull/1398))
* feat(topology/local_homeomorph): local homeomorphisms
* local_homeomorph: reviewer comments
#### Estimated changes
created src/topology/local_homeomorph.lean
- \+ *lemma* eq_of_local_equiv_eq
- \+ *lemma* symm_to_local_equiv
- \+ *lemma* symm_to_fun
- \+ *lemma* symm_inv_fun
- \+ *lemma* symm_source
- \+ *lemma* symm_target
- \+ *lemma* symm_symm
- \+ *lemma* preimage_interior
- \+ *lemma* restr_open_source
- \+ *lemma* restr_open_to_local_equiv
- \+ *lemma* restr_to_fun
- \+ *lemma* restr_inv_fun
- \+ *lemma* restr_source
- \+ *lemma* restr_target
- \+ *lemma* restr_to_local_equiv
- \+ *lemma* restr_source'
- \+ *lemma* restr_to_local_equiv'
- \+ *lemma* restr_eq_of_source_subset
- \+ *lemma* restr_univ
- \+ *lemma* restr_source_inter
- \+ *lemma* refl_source
- \+ *lemma* refl_target
- \+ *lemma* refl_symm
- \+ *lemma* refl_to_fun
- \+ *lemma* refl_inv_fun
- \+ *lemma* refl_local_equiv
- \+ *lemma* of_set_source
- \+ *lemma* of_set_target
- \+ *lemma* of_set_to_fun
- \+ *lemma* of_set_inv_fun
- \+ *lemma* of_set_symm
- \+ *lemma* of_set_to_local_equiv
- \+ *lemma* trans_to_local_equiv
- \+ *lemma* trans_to_fun
- \+ *lemma* trans_inv_fun
- \+ *lemma* trans_symm_eq_symm_trans_symm
- \+ *lemma* trans_source
- \+ *lemma* trans_source'
- \+ *lemma* trans_source''
- \+ *lemma* image_trans_source
- \+ *lemma* trans_target
- \+ *lemma* trans_target'
- \+ *lemma* trans_target''
- \+ *lemma* inv_image_trans_target
- \+ *lemma* trans_assoc
- \+ *lemma* trans_refl
- \+ *lemma* refl_trans
- \+ *lemma* trans_of_set
- \+ *lemma* trans_of_set'
- \+ *lemma* of_set_trans
- \+ *lemma* of_set_trans'
- \+ *lemma* restr_trans
- \+ *lemma* eq_on_source_iff
- \+ *lemma* eq_on_source_refl
- \+ *lemma* eq_on_source_symm
- \+ *lemma* source_eq_of_eq_on_source
- \+ *lemma* target_eq_of_eq_on_source
- \+ *lemma* apply_eq_of_eq_on_source
- \+ *lemma* inv_apply_eq_of_eq_on_source
- \+ *lemma* eq_on_source_trans
- \+ *lemma* eq_on_source_restr
- \+ *lemma* trans_self_symm
- \+ *lemma* trans_symm_self
- \+ *lemma* eq_of_eq_on_source_univ
- \+ *lemma* prod_to_local_equiv
- \+ *lemma* prod_source
- \+ *lemma* prod_target
- \+ *lemma* prod_to_fun
- \+ *lemma* prod_inv_fun
- \+ *lemma* continuous_on_iff_continuous_on_comp_right
- \+ *lemma* continuous_on_iff_continuous_on_comp_left
- \+ *lemma* to_local_homeomorph_source
- \+ *lemma* to_local_homeomorph_target
- \+ *lemma* to_local_homeomorph_to_fun
- \+ *lemma* to_local_homeomorph_inv_fun
- \+ *lemma* refl_to_local_homeomorph
- \+ *lemma* symm_to_local_homeomorph
- \+ *lemma* trans_to_local_homeomorph
- \+ *def* homeomorph.to_local_homeomorph
- \+ *def* of_set
- \+ *def* eq_on_source
- \+ *def* prod



## [2019-09-07 05:32:33](https://github.com/leanprover-community/mathlib/commit/10cb0d1)
feat(topology/constructions): distributivity of products over sums ([#1059](https://github.com/leanprover-community/mathlib/pull/1059))
* feat(topology/constructions): distributivity of products over sums
* Update src/topology/maps.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Reverse direction of sigma_prod_distrib
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *def* sigma_prod_distrib

modified src/data/set/lattice.lean
- \+ *theorem* Union_image_preimage_sigma_mk_eq_self

modified src/topology/constructions.lean
- \+ *lemma* open_embedding_sigma_mk
- \+ *lemma* is_open_map_sigma
- \+ *def* homeomorph_of_continuous_open
- \+ *def* sigma_prod_distrib

modified src/topology/maps.lean
- \+ *lemma* open_embedding.open_iff_image_open
- \+ *lemma* open_embedding.is_open_map
- \+ *lemma* open_embedding.open_iff_preimage_open
- \+ *lemma* open_embedding_of_embedding_open
- \+ *lemma* open_embedding_of_continuous_injective_open
- \+ *lemma* open_embedding_id
- \+ *lemma* open_embedding_compose
- \+ *lemma* closed_embedding.is_closed_map
- \+ *lemma* closed_embedding_of_embedding_closed
- \+ *def* open_embedding



## [2019-09-07 05:17:43](https://github.com/leanprover-community/mathlib/commit/d6a0ac5)
refactor(category_theory/limits/shapes/pullbacks): proof golf ([#1407](https://github.com/leanprover-community/mathlib/pull/1407))
* refactor(category_theory/limits): make is_[co]limit not a class
* refactor(category_theory/limits/shapes/pullbacks): proof golf
#### Estimated changes
modified src/category_theory/limits/shapes/pullbacks.lean



## [2019-09-07 05:00:00](https://github.com/leanprover-community/mathlib/commit/8eab714)
refactor(category_theory/limits): make is_[co]limit not a class ([#1405](https://github.com/leanprover-community/mathlib/pull/1405))
#### Estimated changes
modified src/category_theory/adjunction/limits.lean

modified src/category_theory/limits/limits.lean
- \+ *def* limit.is_limit
- \+ *def* colimit.is_colimit

modified src/category_theory/limits/preserves.lean

modified src/category_theory/limits/shapes/terminal.lean



## [2019-09-06 22:20:07+02:00](https://github.com/leanprover-community/mathlib/commit/a7f268b)
fix(category_theory/limits/shapes): doc typo [ci skip] ([#1406](https://github.com/leanprover-community/mathlib/pull/1406))
#### Estimated changes
modified src/category_theory/limits/shapes/binary_products.lean



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
modified src/algebra/CommRing/adjunctions.lean

modified src/data/finsupp.lean
- \+/\- *lemma* support_eq_empty
- \+/\- *lemma* support_subset_iff
- \+/\- *lemma* single_swap
- \+/\- *lemma* prod_map_range_index
- \+/\- *lemma* map_range_add
- \+/\- *lemma* single_multiset_sum
- \+/\- *lemma* single_finset_sum
- \+/\- *lemma* single_sum
- \+/\- *lemma* prod_finset_sum_index
- \+/\- *lemma* map_range_finset_sum
- \+/\- *lemma* map_domain_finset_sum
- \+/\- *lemma* comap_domain_apply
- \+/\- *lemma* sum_comap_domain
- \+/\- *lemma* eq_zero_of_comap_domain_eq_zero
- \+/\- *lemma* map_domain_comap_domain
- \+/\- *lemma* filter_pos_add_filter_neg
- \+/\- *lemma* count_to_multiset
- \+/\- *lemma* of_multiset_apply
- \+/\- *lemma* mem_support_multiset_sum
- \+/\- *lemma* mem_support_finset_sum
- \+/\- *lemma* mem_support_single
- \+/\- *lemma* filter_curry
- \+/\- *lemma* support_curry
- \+/\- *lemma* prod_single
- \+/\- *lemma* filter_smul
- \+/\- *lemma* map_domain_smul
- \+/\- *lemma* smul_single
- \+/\- *lemma* to_multiset_strict_mono
- \+/\- *lemma* support_eq_empty
- \+/\- *lemma* support_subset_iff
- \+/\- *lemma* single_swap
- \+/\- *lemma* prod_map_range_index
- \+/\- *lemma* map_range_add
- \+/\- *lemma* single_multiset_sum
- \+/\- *lemma* single_finset_sum
- \+/\- *lemma* single_sum
- \+/\- *lemma* prod_finset_sum_index
- \+/\- *lemma* map_range_finset_sum
- \+/\- *lemma* map_domain_finset_sum
- \+/\- *lemma* comap_domain_apply
- \+/\- *lemma* sum_comap_domain
- \+/\- *lemma* eq_zero_of_comap_domain_eq_zero
- \+/\- *lemma* map_domain_comap_domain
- \+/\- *lemma* filter_pos_add_filter_neg
- \+/\- *lemma* count_to_multiset
- \+/\- *lemma* of_multiset_apply
- \+/\- *lemma* mem_support_multiset_sum
- \+/\- *lemma* mem_support_finset_sum
- \+/\- *lemma* mem_support_single
- \+/\- *lemma* filter_curry
- \+/\- *lemma* support_curry
- \+/\- *lemma* prod_single
- \+/\- *lemma* filter_smul
- \+/\- *lemma* map_domain_smul
- \+/\- *lemma* smul_single
- \+/\- *lemma* to_multiset_strict_mono
- \+/\- *def* equiv_fun_on_fintype
- \+/\- *def* filter
- \+/\- *def* subtype_domain
- \+/\- *def* of_multiset
- \+/\- *def* equiv_multiset
- \+/\- *def* finsupp_prod_equiv
- \+/\- *def* restrict_support_equiv
- \+/\- *def* equiv_fun_on_fintype
- \+/\- *def* filter
- \+/\- *def* subtype_domain
- \+/\- *def* of_multiset
- \+/\- *def* equiv_multiset
- \+/\- *def* finsupp_prod_equiv
- \+/\- *def* restrict_support_equiv

modified src/data/mv_polynomial.lean
- \+/\- *lemma* coeff_zero_X
- \+/\- *lemma* eval₂_prod
- \+/\- *lemma* eval₂_sum
- \+/\- *lemma* eval₂_assoc
- \+/\- *lemma* map_eval₂
- \+/\- *lemma* degrees_zero
- \+/\- *lemma* degrees_sum
- \+/\- *lemma* degrees_prod
- \+/\- *lemma* eval₂_hom_X
- \+/\- *lemma* rename_sub
- \+/\- *lemma* eval₂_cast_comp
- \+/\- *lemma* coeff_zero_X
- \+/\- *lemma* eval₂_prod
- \+/\- *lemma* eval₂_sum
- \+/\- *lemma* eval₂_assoc
- \+/\- *lemma* map_eval₂
- \+/\- *lemma* degrees_zero
- \+/\- *lemma* degrees_sum
- \+/\- *lemma* degrees_prod
- \+/\- *lemma* eval₂_hom_X
- \+/\- *lemma* rename_sub
- \+/\- *lemma* eval₂_cast_comp
- \+/\- *theorem* eval_assoc
- \+/\- *theorem* map_map
- \+/\- *theorem* eval_assoc
- \+/\- *theorem* map_map

modified src/data/polynomial.lean
- \+/\- *lemma* coeff_single
- \+/\- *lemma* coeff_one_zero
- \+/\- *lemma* coeff_C_zero
- \+/\- *lemma* coeff_X_one
- \+/\- *lemma* coeff_X_zero
- \+/\- *lemma* coeff_X
- \+/\- *lemma* coeff_sum
- \+/\- *lemma* coeff_one
- \+/\- *lemma* map_map
- \+/\- *lemma* nat_degree_eq_of_degree_eq
- \+/\- *lemma* degree_sum_le
- \+/\- *lemma* degree_map_le
- \+/\- *lemma* degree_map_eq_of_leading_coeff_ne_zero
- \+/\- *lemma* degree_map_eq_of_injective
- \+/\- *lemma* monic_map
- \+/\- *lemma* degree_map'
- \+/\- *lemma* nat_degree_map'
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_mod_div_by_monic
- \+/\- *lemma* map_div_by_monic
- \+/\- *lemma* map_mod_by_monic
- \+/\- *lemma* coeff_one_zero
- \+/\- *lemma* coeff_C_zero
- \+/\- *lemma* coeff_X_one
- \+/\- *lemma* coeff_X_zero
- \+/\- *lemma* coeff_X
- \+/\- *lemma* coeff_sum
- \+/\- *lemma* coeff_single
- \+/\- *lemma* coeff_one
- \+/\- *lemma* map_map
- \+/\- *lemma* nat_degree_eq_of_degree_eq
- \+/\- *lemma* degree_sum_le
- \+/\- *lemma* degree_map_le
- \+/\- *lemma* degree_map_eq_of_leading_coeff_ne_zero
- \+/\- *lemma* degree_map_eq_of_injective
- \+/\- *lemma* monic_map
- \+/\- *lemma* degree_map'
- \+/\- *lemma* nat_degree_map'
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_mod_div_by_monic
- \+/\- *lemma* map_div_by_monic
- \+/\- *lemma* map_mod_by_monic
- \+ *def* nth_roots
- \- *def* rec_on_horner
- \- *def* div_mod_by_monic_aux

modified src/field_theory/mv_polynomial.lean

modified src/field_theory/splitting_field.lean

modified src/linear_algebra/basis.lean

modified src/linear_algebra/dimension.lean

modified src/linear_algebra/dual.lean

modified src/linear_algebra/finsupp.lean
- \+/\- *lemma* supported_eq_span_single
- \+/\- *lemma* supported_eq_span_single
- \+/\- *theorem* restrict_dom_apply
- \+/\- *theorem* restrict_dom_comp_subtype
- \+/\- *theorem* range_restrict_dom
- \+/\- *theorem* lsum_apply
- \+/\- *theorem* restrict_dom_apply
- \+/\- *theorem* restrict_dom_comp_subtype
- \+/\- *theorem* range_restrict_dom
- \+/\- *theorem* lsum_apply
- \+/\- *def* restrict_dom
- \+/\- *def* supported_equiv_finsupp
- \+/\- *def* lsum
- \+/\- *def* restrict_dom
- \+/\- *def* supported_equiv_finsupp
- \+/\- *def* lsum

modified src/linear_algebra/finsupp_vector_space.lean
- \+/\- *lemma* linear_independent_single
- \+/\- *lemma* is_basis_single
- \+/\- *lemma* linear_independent_single
- \+/\- *lemma* is_basis_single

modified src/linear_algebra/matrix.lean

modified src/ring_theory/adjoin_root.lean

modified src/ring_theory/algebra.lean

modified src/ring_theory/free_comm_ring.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/polynomial.lean

modified src/ring_theory/power_series.lean
- \+/\- *lemma* coeff_mk
- \+/\- *lemma* monomial_zero
- \+/\- *lemma* coeff_C_zero
- \+/\- *lemma* coeff_trunc
- \+/\- *lemma* trunc_zero
- \+/\- *lemma* trunc_one
- \+/\- *lemma* trunc_C
- \+/\- *lemma* trunc_add
- \+ *lemma* inv_eq_inv_aux
- \+/\- *lemma* coeff_mk
- \+/\- *lemma* coeff_C_zero
- \+/\- *lemma* monomial_zero
- \+/\- *lemma* coeff_trunc
- \+/\- *lemma* trunc_zero
- \+/\- *lemma* trunc_one
- \+/\- *lemma* trunc_C
- \+/\- *lemma* trunc_add
- \+/\- *def* trunc
- \+/\- *def* trunc



## [2019-09-05 21:37:18](https://github.com/leanprover-community/mathlib/commit/1a0ed80)
fix(naming): typo [ci skip] ([#1401](https://github.com/leanprover-community/mathlib/pull/1401))
* fix(naming): typo [ci skip]
* more typos
#### Estimated changes
modified docs/contribute/naming.md



## [2019-09-05 11:03:20](https://github.com/leanprover-community/mathlib/commit/b1920f5)
chore(algebra/ordered_field): add simp attributes to inv_pos' and others ([#1400](https://github.com/leanprover-community/mathlib/pull/1400))
#### Estimated changes
modified src/algebra/ordered_field.lean
- \+/\- *lemma* inv_pos'
- \+/\- *lemma* inv_neg'
- \+/\- *lemma* inv_nonneg
- \+/\- *lemma* inv_nonpos
- \+/\- *lemma* inv_pos'
- \+/\- *lemma* inv_neg'
- \+/\- *lemma* inv_nonneg
- \+/\- *lemma* inv_nonpos



## [2019-09-05 09:22:42](https://github.com/leanprover-community/mathlib/commit/7f20843)
chore(order/filter): rephrase filter.has_le ([#1399](https://github.com/leanprover-community/mathlib/pull/1399))
The goal of this tiny refactor is to prevent `filter.sets` leaking when
proving a filter g is finer than another one f. We want the goal to be
`s ∈ f → s ∈ g` instead of the definitionaly equivalent
`s ∈ f.sets ∈ g.sets`
#### Estimated changes
modified src/order/filter/basic.lean

modified src/order/filter/lift.lean
- \+ *lemma* mem_lift_iff

modified src/topology/basic.lean



## [2019-09-05 02:48:09](https://github.com/leanprover-community/mathlib/commit/2854909)
feat(bounded_lattice/has_lt): add a `lt` relation independent from `l… ([#1366](https://github.com/leanprover-community/mathlib/pull/1366))
* feat(bounded_lattice/has_lt): add a `lt` relation independent from `le` for `has_top`
* use priority 10 instead of 0
#### Estimated changes
modified src/algebra/ordered_group.lean

modified src/order/bounded_lattice.lean
- \+/\- *theorem* some_lt_some
- \+/\- *theorem* some_le_some
- \+ *theorem* none_le
- \+ *theorem* none_lt_some
- \+/\- *theorem* some_le_some
- \+/\- *theorem* some_lt_some



## [2019-09-05 00:46:57](https://github.com/leanprover-community/mathlib/commit/6292825)
feat(data/equiv/local_equiv): define local equivalences  ([#1359](https://github.com/leanprover-community/mathlib/pull/1359))
* feat(data/equiv/local_equiv): define local equivalences
* add doc
* add extensionality attribute
* sanity_check
#### Estimated changes
created src/data/equiv/local_equiv.lean
- \+ *lemma* symm_to_fun
- \+ *lemma* symm_inv_fun
- \+ *lemma* symm_source
- \+ *lemma* symm_target
- \+ *lemma* symm_symm
- \+ *lemma* bij_on_source
- \+ *lemma* image_eq_target_inter_inv_preimage
- \+ *lemma* inv_image_eq_source_inter_preimage
- \+ *lemma* source_inter_preimage_inv_preimage
- \+ *lemma* target_inter_inv_preimage_preimage
- \+ *lemma* image_source_eq_target
- \+ *lemma* source_subset_preimage_target
- \+ *lemma* inv_image_target_eq_source
- \+ *lemma* target_subset_preimage_source
- \+ *lemma* restr_to_fun
- \+ *lemma* restr_inv_fun
- \+ *lemma* restr_source
- \+ *lemma* restr_target
- \+ *lemma* restr_eq_of_source_subset
- \+ *lemma* restr_univ
- \+ *lemma* refl_source
- \+ *lemma* refl_target
- \+ *lemma* refl_to_fun
- \+ *lemma* refl_inv_fun
- \+ *lemma* refl_symm
- \+ *lemma* refl_restr_source
- \+ *lemma* refl_restr_target
- \+ *lemma* of_set_source
- \+ *lemma* of_set_target
- \+ *lemma* of_set_to_fun
- \+ *lemma* of_set_inv_fun
- \+ *lemma* of_set_symm
- \+ *lemma* trans_to_fun
- \+ *lemma* trans_apply
- \+ *lemma* trans_inv_fun
- \+ *lemma* trans_inv_apply
- \+ *lemma* trans_symm_eq_symm_trans_symm
- \+ *lemma* trans_source
- \+ *lemma* trans_source'
- \+ *lemma* trans_source''
- \+ *lemma* image_trans_source
- \+ *lemma* trans_target
- \+ *lemma* trans_target'
- \+ *lemma* trans_target''
- \+ *lemma* inv_image_trans_target
- \+ *lemma* trans_assoc
- \+ *lemma* trans_refl
- \+ *lemma* refl_trans
- \+ *lemma* trans_refl_restr
- \+ *lemma* trans_refl_restr'
- \+ *lemma* restr_trans
- \+ *lemma* eq_on_source_refl
- \+ *lemma* eq_on_source_symm
- \+ *lemma* source_eq_of_eq_on_source
- \+ *lemma* target_eq_of_eq_on_source
- \+ *lemma* apply_eq_of_eq_on_source
- \+ *lemma* inv_apply_eq_of_eq_on_source
- \+ *lemma* eq_on_source_trans
- \+ *lemma* eq_on_source_restr
- \+ *lemma* eq_on_source_preimage
- \+ *lemma* trans_self_symm
- \+ *lemma* trans_symm_self
- \+ *lemma* eq_of_eq_on_source_univ
- \+ *lemma* prod_source
- \+ *lemma* prod_target
- \+ *lemma* prod_to_fun
- \+ *lemma* prod_inv_fun
- \+ *lemma* to_local_equiv_to_fun
- \+ *lemma* to_local_equiv_inv_fun
- \+ *lemma* to_local_equiv_source
- \+ *lemma* to_local_equiv_target
- \+ *lemma* refl_to_local_equiv
- \+ *lemma* symm_to_local_equiv
- \+ *lemma* trans_to_local_equiv
- \+ *def* equiv.to_local_equiv
- \+ *def* of_set
- \+ *def* eq_on_source
- \+ *def* prod



## [2019-09-04 22:48:55](https://github.com/leanprover-community/mathlib/commit/79a1f84)
fix(tactic/norm_num): bugfix bad proof application ([#1387](https://github.com/leanprover-community/mathlib/pull/1387))
* fix(tactic/norm_num): bugfix bad proof application
* add test case that used to fail
* add try_for
* fix typecheck test
* increase test timeout
#### Estimated changes
modified src/tactic/norm_num.lean

modified test/norm_num.lean



## [2019-09-04 20:52:45](https://github.com/leanprover-community/mathlib/commit/3c224f0)
feat (logic/basic): exists_eq' ([#1397](https://github.com/leanprover-community/mathlib/pull/1397))
Not a great name, but `exists_eq_left` and `exists_eq_right` are taken, and it's unlikely to be used except in `simp`
#### Estimated changes
modified src/logic/basic.lean
- \+ *theorem* exists_eq'



## [2019-09-04 19:28:57](https://github.com/leanprover-community/mathlib/commit/65ffb7b)
fix(topology/uniform_space): simplify continuity proof ([#1396](https://github.com/leanprover-community/mathlib/pull/1396))
#### Estimated changes
modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* uniform_continuous_iff
- \+/\- *lemma* uniform_continuous.continuous
- \+/\- *lemma* uniform_continuous.continuous
- \+/\- *lemma* uniform_continuous_iff



## [2019-09-04 17:22:01](https://github.com/leanprover-community/mathlib/commit/06cffeb)
feat(order): add lemma ([#1375](https://github.com/leanprover-community/mathlib/pull/1375))
#### Estimated changes
modified src/algebra/order.lean
- \+ *lemma* min_le_max



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
modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.lift_π
- \+/\- *lemma* lim.map_π
- \+/\- *lemma* limit.lift_π
- \+/\- *lemma* lim.map_π

created src/category_theory/limits/shapes/constructions/finite_limits.lean

created src/category_theory/limits/shapes/constructions/limits.lean

created src/category_theory/monoidal/of_has_finite_products.lean
- \+ *def* monoidal_of_has_finite_products
- \+ *def* monoidal_of_has_finite_coproducts

modified src/category_theory/monoidal/types.lean



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
created src/category_theory/hom_functor.lean
- \+ *lemma* hom_obj
- \+ *lemma* hom_pairing_map

modified src/category_theory/limits/functor_category.lean

modified src/category_theory/monoidal/category.lean

modified src/category_theory/opposites.lean
- \- *lemma* hom_obj
- \- *lemma* hom_pairing_map

modified src/category_theory/products/associator.lean

created src/category_theory/products/basic.lean
- \+ *lemma* prod_id
- \+ *lemma* prod_comp
- \+ *lemma* prod_id_fst
- \+ *lemma* prod_id_snd
- \+ *lemma* prod_comp_fst
- \+ *lemma* prod_comp_snd
- \+ *lemma* inl_obj
- \+ *lemma* inl_map
- \+ *lemma* inr_obj
- \+ *lemma* inr_map
- \+ *lemma* fst_obj
- \+ *lemma* fst_map
- \+ *lemma* snd_obj
- \+ *lemma* snd_map
- \+ *lemma* swap_obj
- \+ *lemma* swap_map
- \+ *lemma* evaluation_obj_obj
- \+ *lemma* evaluation_obj_map
- \+ *lemma* evaluation_map_app
- \+ *lemma* evaluation_uncurried_obj
- \+ *lemma* evaluation_uncurried_map
- \+ *lemma* prod_obj
- \+ *lemma* prod_map
- \+ *lemma* prod_app
- \+ *def* inl
- \+ *def* inr
- \+ *def* fst
- \+ *def* snd
- \+ *def* swap
- \+ *def* symmetry
- \+ *def* braiding
- \+ *def* evaluation
- \+ *def* evaluation_uncurried
- \+ *def* prod
- \+ *def* prod

modified src/category_theory/products/bifunctor.lean

modified src/category_theory/products/default.lean
- \- *lemma* prod_id
- \- *lemma* prod_comp
- \- *lemma* prod_id_fst
- \- *lemma* prod_id_snd
- \- *lemma* prod_comp_fst
- \- *lemma* prod_comp_snd
- \- *lemma* inl_obj
- \- *lemma* inl_map
- \- *lemma* inr_obj
- \- *lemma* inr_map
- \- *lemma* fst_obj
- \- *lemma* fst_map
- \- *lemma* snd_obj
- \- *lemma* snd_map
- \- *lemma* swap_obj
- \- *lemma* swap_map
- \- *lemma* evaluation_obj_obj
- \- *lemma* evaluation_obj_map
- \- *lemma* evaluation_map_app
- \- *lemma* evaluation_uncurried_obj
- \- *lemma* evaluation_uncurried_map
- \- *lemma* prod_obj
- \- *lemma* prod_map
- \- *lemma* prod_app
- \- *def* inl
- \- *def* inr
- \- *def* fst
- \- *def* snd
- \- *def* swap
- \- *def* symmetry
- \- *def* evaluation
- \- *def* evaluation_uncurried
- \- *def* prod
- \- *def* prod

created src/category_theory/sums/associator.lean
- \+ *lemma* associator_obj_inl_inl
- \+ *lemma* associator_obj_inl_inr
- \+ *lemma* associator_obj_inr
- \+ *lemma* associator_map_inl_inl
- \+ *lemma* associator_map_inl_inr
- \+ *lemma* associator_map_inr
- \+ *lemma* inverse_associator_obj_inl
- \+ *lemma* inverse_associator_obj_inr_inl
- \+ *lemma* inverse_associator_obj_inr_inr
- \+ *lemma* inverse_associator_map_inl
- \+ *lemma* inverse_associator_map_inr_inl
- \+ *lemma* inverse_associator_map_inr_inr
- \+ *def* associator
- \+ *def* inverse_associator
- \+ *def* associativity

created src/category_theory/sums/basic.lean
- \+ *lemma* sum_comp_inl
- \+ *lemma* sum_comp_inr
- \+ *lemma* inl_obj
- \+ *lemma* inl_map
- \+ *lemma* inr_obj
- \+ *lemma* inr_map
- \+ *lemma* swap_obj_inl
- \+ *lemma* swap_obj_inr
- \+ *lemma* swap_map_inl
- \+ *lemma* swap_map_inr
- \+ *lemma* sum_obj_inl
- \+ *lemma* sum_obj_inr
- \+ *lemma* sum_map_inl
- \+ *lemma* sum_map_inr
- \+ *lemma* sum_app_inl
- \+ *lemma* sum_app_inr
- \+ *def* inl_
- \+ *def* inr_
- \+ *def* swap
- \+ *def* equivalence
- \+ *def* symmetry
- \+ *def* sum
- \+ *def* sum

created src/category_theory/sums/default.lean

modified src/category_theory/yoneda.lean



## [2019-09-04 06:33:49](https://github.com/leanprover-community/mathlib/commit/b079298)
feat(tactic/doc_blame): Use is_auto_generated ([#1395](https://github.com/leanprover-community/mathlib/pull/1395))
#### Estimated changes
modified src/tactic/doc_blame.lean
- \- *def* name.is_not_auto



## [2019-09-03 21:08:11](https://github.com/leanprover-community/mathlib/commit/ff47fa3)
feat(measure_theory): prove that the Giry monad is a monad in the category_theory sense ([#1259](https://github.com/leanprover-community/mathlib/pull/1259))
* feat(measure_theory): prove that the Giry monad is a monad in the category_theory sense
* Add spaces to fix alignment
* document Measure
* Add documentation
* Add space before colon
#### Estimated changes
modified src/measure_theory/Meas.lean
- \+ *def* Measure
- \+ *def* Integral

modified src/measure_theory/giry_monad.lean
- \+ *lemma* map_dirac
- \+ *lemma* join_eq_bind
- \+ *lemma* join_map_map
- \+ *lemma* join_map_join
- \+ *lemma* join_map_dirac
- \+ *lemma* join_dirac

modified src/measure_theory/measurable_space.lean
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
modified .gitignore

modified docs/tactics.md

modified src/algebra/CommRing/adjunctions.lean

modified src/algebra/archimedean.lean

modified src/algebra/direct_limit.lean

modified src/algebra/group_power.lean

modified src/analysis/complex/exponential.lean

modified src/analysis/convex.lean

modified src/analysis/normed_space/banach.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/bounded_linear_maps.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/analysis/specific_limits.lean

modified src/category_theory/natural_isomorphism.lean

modified src/computability/turing_machine.lean

modified src/data/complex/exponential.lean

modified src/data/list/basic.lean

modified src/data/matrix/basic.lean

modified src/data/matrix/pequiv.lean

modified src/data/multiset.lean

modified src/data/nat/totient.lean

modified src/data/padics/hensel.lean

modified src/data/padics/padic_integers.lean

modified src/data/padics/padic_norm.lean

modified src/data/padics/padic_numbers.lean

modified src/data/pfun.lean

modified src/data/polynomial.lean

modified src/data/rat/basic.lean

modified src/data/rat/cast.lean

modified src/data/rat/order.lean

modified src/data/real/basic.lean

modified src/data/real/cau_seq_completion.lean

modified src/data/real/ennreal.lean

modified src/data/real/hyperreal.lean

modified src/data/real/nnreal.lean

modified src/data/set/countable.lean

modified src/data/set/disjointed.lean

modified src/field_theory/mv_polynomial.lean

modified src/field_theory/splitting_field.lean

modified src/group_theory/coset.lean

modified src/group_theory/order_of_element.lean

modified src/linear_algebra/tensor_product.lean

modified src/logic/function.lean

modified src/measure_theory/ae_eq_fun.lean

modified src/measure_theory/bochner_integration.lean

modified src/measure_theory/borel_space.lean

modified src/measure_theory/decomposition.lean

modified src/measure_theory/giry_monad.lean

modified src/measure_theory/integration.lean
- \+/\- *theorem* range_map
- \+/\- *theorem* range_map

modified src/measure_theory/l1_space.lean

modified src/measure_theory/measurable_space.lean

modified src/measure_theory/measure_space.lean

modified src/measure_theory/outer_measure.lean

modified src/measure_theory/probability_mass_function.lean

modified src/measure_theory/simple_func_dense.lean

modified src/number_theory/dioph.lean

modified src/order/basic.lean

modified src/order/conditionally_complete_lattice.lean

modified src/order/filter/basic.lean

modified src/order/filter/filter_product.lean

modified src/order/filter/lift.lean

modified src/order/filter/pointwise.lean

modified src/order/zorn.lean

modified src/ring_theory/algebra.lean

modified src/ring_theory/euclidean_domain.lean

modified src/ring_theory/ideals.lean

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/principal_ideal_domain.lean

modified src/set_theory/cardinal.lean

modified src/set_theory/cofinality.lean

modified src/set_theory/ordinal.lean

modified src/set_theory/ordinal_notation.lean

modified src/set_theory/schroeder_bernstein.lean

modified src/tactic/basic.lean

modified src/tactic/default.lean

modified src/tactic/finish.lean

modified src/tactic/localized.lean

modified src/tactic/omega/coeffs.lean

modified src/tactic/omega/eq_elim.lean

modified src/tactic/omega/int/dnf.lean

modified src/tactic/omega/int/form.lean

modified src/tactic/omega/int/main.lean

modified src/tactic/omega/int/preterm.lean

modified src/tactic/omega/misc.lean

modified src/tactic/omega/nat/dnf.lean

modified src/tactic/omega/nat/form.lean

modified src/tactic/omega/nat/main.lean

modified src/tactic/omega/nat/neg_elim.lean

modified src/tactic/omega/nat/preterm.lean

modified src/tactic/omega/nat/sub_elim.lean

modified src/tactic/push_neg.lean

modified src/topology/algebra/group.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/monoid.lean

modified src/topology/algebra/ordered.lean

modified src/topology/algebra/ring.lean

modified src/topology/algebra/uniform_group.lean

modified src/topology/algebra/uniform_ring.lean

modified src/topology/basic.lean

modified src/topology/constructions.lean

modified src/topology/instances/ennreal.lean

modified src/topology/instances/nnreal.lean

modified src/topology/instances/real.lean

modified src/topology/maps.lean

modified src/topology/metric_space/baire.lean

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/emetric_space.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/metric_space/hausdorff_distance.lean

modified src/topology/order.lean

modified src/topology/separation.lean

modified src/topology/subset_properties.lean

modified src/topology/uniform_space/basic.lean

modified src/topology/uniform_space/cauchy.lean

modified src/topology/uniform_space/completion.lean

modified src/topology/uniform_space/pi.lean

modified src/topology/uniform_space/separation.lean

modified src/topology/uniform_space/uniform_embedding.lean



## [2019-09-03 17:52:30](https://github.com/leanprover-community/mathlib/commit/4b6fcd9)
perf(data/gaussian_int): speed up div and mod ([#1394](https://github.com/leanprover-community/mathlib/pull/1394))
avoid using `int.cast`, and use `rat.of_int`.
This sped up `#eval (⟨1414,152⟩ : gaussian_int) % ⟨123,456⟩` from about 5 seconds to 2 milliseconds
#### Estimated changes
modified src/data/zsqrtd/gaussian_int.lean



## [2019-09-03 17:20:07](https://github.com/leanprover-community/mathlib/commit/974d413)
chore(linear_algebra/determinant): simplify det_mul proof ([#1392](https://github.com/leanprover-community/mathlib/pull/1392))
* chore(linear_algebra/determinant): simplify det_mul proof
Minor improvement to the proof of `det_mul`
* make det_mul_aux more readable
#### Estimated changes
modified src/linear_algebra/determinant.lean



## [2019-09-03 15:36:36](https://github.com/leanprover-community/mathlib/commit/3a58b50)
feat(data/equiv/basic): add more functions for equivalences between complex types ([#1384](https://github.com/leanprover-community/mathlib/pull/1384))
* Add more `equiv` combinators
* Fix compile
* Minor fixes
* Update src/data/equiv/basic.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *def* sigma_preimage_equiv
- \+ *def* subtype_subtype_equiv_subtype_exists
- \+ *def* subtype_subtype_equiv_subtype_inter
- \+/\- *def* subtype_subtype_equiv_subtype
- \+ *def* subtype_univ_equiv
- \+ *def* sigma_subtype_equiv_of_subset
- \+ *def* sigma_subtype_preimage_equiv
- \+ *def* sigma_subtype_preimage_equiv_subtype
- \- *def* equiv_fib
- \+/\- *def* subtype_subtype_equiv_subtype
- \- *def* equiv_sigma_subtype

modified src/group_theory/coset.lean

modified src/group_theory/sylow.lean

modified src/set_theory/cardinal.lean

modified src/set_theory/cofinality.lean



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
modified src/topology/algebra/group_completion.lean
- \- *lemma* is_add_group_hom_prod

modified src/topology/algebra/uniform_ring.lean

modified src/topology/maps.lean
- \+ *lemma* dense_range.nonempty

created src/topology/uniform_space/absolute_value.lean
- \+ *theorem* mem_uniformity
- \+ *def* uniform_space_core
- \+ *def* uniform_space

created src/topology/uniform_space/abstract_completion.lean
- \+ *lemma* dense'
- \+ *lemma* dense_inducing
- \+ *lemma* uniform_continuous_coe
- \+ *lemma* continuous_coe
- \+ *lemma* induction_on
- \+ *lemma* extend_def
- \+ *lemma* extend_coe
- \+ *lemma* uniform_continuous_extend
- \+ *lemma* continuous_extend
- \+ *lemma* extend_unique
- \+ *lemma* extend_comp_coe
- \+ *lemma* uniform_continuous_map
- \+ *lemma* continuous_map
- \+ *lemma* map_coe
- \+ *lemma* map_unique
- \+ *lemma* map_id
- \+ *lemma* extend_map
- \+ *lemma* map_comp
- \+ *lemma* uniform_continuous_compare
- \+ *lemma* compare_coe
- \+ *lemma* inverse_compare
- \+ *lemma* uniform_continuous_compare_equiv
- \+ *lemma* uniform_continuous_compare_equiv_symm
- \+ *lemma* extension₂_coe_coe
- \+ *lemma* uniform_continuous_extension₂
- \+ *lemma* uniform_continuous_map₂
- \+ *lemma* continuous_map₂
- \+ *lemma* map₂_coe_coe
- \+ *def* compare
- \+ *def* compare_equiv

created src/topology/uniform_space/compare_reals.lean
- \+ *lemma* rat.uniform_space_eq
- \+ *lemma* compare_uc
- \+ *lemma* compare_uc_symm
- \+ *def* rational_cau_seq_pkg
- \+ *def* Q
- \+ *def* Bourbakiℝ
- \+ *def* Bourbaki_pkg

modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* dense
- \+/\- *lemma* nonempty_completion_iff
- \+/\- *lemma* uniform_continuous_coe
- \+/\- *lemma* continuous_coe
- \+/\- *lemma* nonempty_completion_iff
- \+/\- *lemma* uniform_continuous_coe
- \+/\- *lemma* continuous_coe
- \+/\- *lemma* dense
- \- *lemma* uniform_continuous_prod
- \- *lemma* prod_coe_coe
- \+ *def* cpkg



## [2019-09-03 11:51:43](https://github.com/leanprover-community/mathlib/commit/c7d3629)
fix(restate_axiom): create lemmas from lemmas ([#1390](https://github.com/leanprover-community/mathlib/pull/1390))
#### Estimated changes
modified src/tactic/restate_axiom.lean



## [2019-09-03 09:24:11+02:00](https://github.com/leanprover-community/mathlib/commit/94205c4)
feat(data/fintype): prove `card (subtype p) ≤ card α` ([#1383](https://github.com/leanprover-community/mathlib/pull/1383))
* feat(data/fintype): prove `card (subtype p) ≤ card α`
* Add `cardinal.mk_le_of_subtype`
* Rename `mk_le_of_subtype` to `mk_subtype_le`, use it in `mk_set_le`
Earlier both `mk_subtype_le` and `mk_set_le` took `set α` as an
argument. Now `mk_subtype_le` takes `α → Prop`.
#### Estimated changes
modified src/data/fintype.lean
- \+ *theorem* fintype.card_subtype_le

modified src/data/real/cardinality.lean

modified src/set_theory/cardinal.lean
- \+/\- *theorem* mk_subtype_le
- \+ *theorem* mk_subtype_le_of_subset
- \+/\- *theorem* mk_subtype_le



## [2019-09-02 14:19:49](https://github.com/leanprover-community/mathlib/commit/227b682)
feat(category_theory): define `iso.conj` and friends ([#1381](https://github.com/leanprover-community/mathlib/pull/1381))
* feat(category_theory): define `iso.conj` and friends
* Drop 2 `@[simp]` attributes
#### Estimated changes
created src/category_theory/conj.lean
- \+ *lemma* hom_congr_apply
- \+ *lemma* hom_congr_comp
- \+ *lemma* hom_congr_refl
- \+ *lemma* hom_congr_trans
- \+ *lemma* hom_congr_symm
- \+ *lemma* conj_apply
- \+ *lemma* conj_comp
- \+ *lemma* conj_id
- \+ *lemma* refl_conj
- \+ *lemma* trans_conj
- \+ *lemma* symm_self_conj
- \+ *lemma* self_symm_conj
- \+ *lemma* conj_pow
- \+ *lemma* conj_Aut_apply
- \+ *lemma* conj_Aut_hom
- \+ *lemma* trans_conj_Aut
- \+ *lemma* conj_Aut_mul
- \+ *lemma* conj_Aut_trans
- \+ *lemma* conj_Aut_pow
- \+ *lemma* conj_Aut_gpow
- \+ *lemma* map_hom_congr
- \+ *lemma* map_conj
- \+ *lemma* map_conj_Aut
- \+ *def* hom_congr
- \+ *def* conj
- \+ *def* conj_Aut



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
modified src/category_theory/const.lean
- \+ *lemma* unop_functor_op_obj_map

modified src/category_theory/limits/cones.lean
- \+ *def* equiv
- \+ *def* equiv

modified src/category_theory/limits/limits.lean
- \+ *def* has_limit.of_cones_iso
- \+ *def* has_colimit.of_cocones_iso

modified src/category_theory/limits/shapes/binary_products.lean

created src/category_theory/limits/shapes/constructions/finite_products.lean

created src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean
- \+ *def* equalizer_diagram
- \+ *def* equalizer_diagram.cones_hom
- \+ *def* equalizer_diagram.cones_inv
- \+ *def* equalizer_diagram.cones_iso
- \+ *def* limits_from_equalizers_and_products

created src/category_theory/limits/shapes/constructions/pullbacks.lean

created src/category_theory/limits/shapes/constructions/sums.lean



## [2019-09-02 07:54:36](https://github.com/leanprover-community/mathlib/commit/fe7695b)
chore(data/nat/gcd): remove pointless parentheses ([#1386](https://github.com/leanprover-community/mathlib/pull/1386))
#### Estimated changes
modified src/data/nat/gcd.lean
- \+/\- *theorem* gcd_eq_right_iff_dvd
- \+/\- *theorem* gcd_eq_right_iff_dvd



## [2019-09-02 06:00:19](https://github.com/leanprover-community/mathlib/commit/d35dc13)
feat(data/nat/gcd): add simple lemmas ([#1382](https://github.com/leanprover-community/mathlib/pull/1382))
* feat(data/nat/gcd): more simple lemmas
* Prove `iff` instead of one side implication
#### Estimated changes
modified src/data/nat/gcd.lean
- \+ *lemma* coprime.gcd_left
- \+ *lemma* coprime.gcd_right
- \+ *lemma* coprime.gcd_both
- \+ *theorem* gcd_le_left
- \+ *theorem* gcd_le_right
- \+ *theorem* gcd_eq_left_iff_dvd
- \+ *theorem* gcd_eq_right_iff_dvd
- \+ *theorem* gcd_mul_dvd_mul_gcd
- \+ *theorem* coprime.gcd_mul
- \- *theorem* exists_eq_prod_and_dvd_and_dvd
- \+ *def* prod_dvd_and_dvd_of_dvd_prod



## [2019-09-01 11:29:41](https://github.com/leanprover-community/mathlib/commit/6d2b3ed)
chore(category_theory/notation): consistently use notation for functor.id ([#1378](https://github.com/leanprover-community/mathlib/pull/1378))
* chore(category_theory/notation): consistently use notation for functor.id
* oops, overzealous search-and-replace
* more
* more
* more
#### Estimated changes
modified src/category_theory/adjunction/basic.lean
- \+/\- *def* id
- \+/\- *def* id

modified src/category_theory/comma.lean
- \+/\- *def* map_left_id
- \+/\- *def* map_right_id
- \+/\- *def* over
- \+/\- *def* under
- \+/\- *def* map_left_id
- \+/\- *def* map_right_id
- \+/\- *def* over
- \+/\- *def* under

modified src/category_theory/equivalence.lean
- \+/\- *def* fun_inv_id
- \+/\- *def* inv_fun_id
- \+/\- *def* fun_inv_id
- \+/\- *def* inv_fun_id

modified src/category_theory/fully_faithful.lean

modified src/category_theory/functor.lean
- \+/\- *lemma* id_obj
- \+/\- *lemma* id_map
- \+/\- *lemma* id_obj
- \+/\- *lemma* id_map

modified src/category_theory/limits/cones.lean
- \+/\- *def* postcompose_id
- \+/\- *def* precompose_id
- \+/\- *def* postcompose_id
- \+/\- *def* precompose_id

modified src/category_theory/limits/limits.lean

modified src/category_theory/limits/preserves.lean

modified src/category_theory/monad/adjunction.lean
- \+/\- *lemma* monad_η_app
- \+/\- *lemma* monad_μ_app
- \+/\- *lemma* comparison_map_f
- \+/\- *lemma* comparison_obj_a
- \+/\- *lemma* monad_η_app
- \+/\- *lemma* monad_μ_app
- \+/\- *lemma* comparison_map_f
- \+/\- *lemma* comparison_obj_a

modified src/category_theory/monad/basic.lean

modified src/category_theory/monoidal/category.lean

modified src/category_theory/monoidal/functor.lean

modified src/category_theory/natural_isomorphism.lean
- \+/\- *def* ulift_down_up
- \+/\- *def* ulift_up_down
- \+/\- *def* ulift_down_up
- \+/\- *def* ulift_up_down

modified src/category_theory/products/default.lean
- \+/\- *def* symmetry
- \+/\- *def* symmetry

modified src/category_theory/whiskering.lean
- \+/\- *def* left_unitor
- \+/\- *def* right_unitor
- \+/\- *def* left_unitor
- \+/\- *def* right_unitor

modified src/category_theory/yoneda.lean

modified src/topology/Top/opens.lean
- \+/\- *def* map_id
- \+/\- *def* map_id

