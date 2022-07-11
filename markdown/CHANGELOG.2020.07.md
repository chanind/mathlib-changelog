## [2020-07-31 19:09:51](https://github.com/leanprover-community/mathlib/commit/37ab426)
feat(complete_lattice): put supr_congr and infi_congr back ([#3646](https://github.com/leanprover-community/mathlib/pull/3646))
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *lemma* supr_congr
- \+ *lemma* infi_congr



## [2020-07-31 17:41:12](https://github.com/leanprover-community/mathlib/commit/7e570ed)
chore(*): assorted small lemmas ([#3644](https://github.com/leanprover-community/mathlib/pull/3644))
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *theorem* is_o.trans_le

Modified src/analysis/normed_space/indicator_function.lean
- \+ *lemma* nnnorm_indicator_eq_indicator_nnnorm

Modified src/data/real/ennreal.lean
- \+ *lemma* of_real_lt_top

Modified src/order/filter/basic.lean
- \+ *lemma* union_mem_sup

Modified src/order/liminf_limsup.lean
- \+ *lemma* is_bounded_under.mono

Modified src/topology/instances/ennreal.lean




## [2020-07-31 17:41:10](https://github.com/leanprover-community/mathlib/commit/396a764)
feat(analysis/calculus/fderiv): inversion is differentiable ([#3510](https://github.com/leanprover-community/mathlib/pull/3510))
At an invertible element `x` of a complete normed algebra, the inversion operation of the algebra is Fréchet-differentiable, with derivative `λ t, - x⁻¹ * t * x⁻¹`.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* inverse_unit

Modified src/analysis/asymptotics.lean
- \+ *lemma* is_o_id_const

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at_inverse
- \+ *lemma* differentiable_at_inverse
- \+ *lemma* fderiv_inverse

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* summable_of_norm_bounded
- \+ *lemma* tsum_of_norm_bounded

Modified src/analysis/normed_space/units.lean
- \+/\- *lemma* one_sub_coe
- \+/\- *lemma* add_coe
- \+/\- *lemma* unit_of_nearby_coe
- \+ *lemma* inverse_one_sub
- \+ *lemma* inverse_add
- \+ *lemma* inverse_one_sub_nth_order
- \+ *lemma* inverse_add_nth_order
- \+ *lemma* inverse_one_sub_norm
- \+ *lemma* inverse_add_norm
- \+ *lemma* inverse_add_norm_diff_nth_order
- \+ *lemma* inverse_add_norm_diff_first_order
- \+ *lemma* inverse_add_norm_diff_second_order
- \+ *lemma* inverse_continuous_at
- \+/\- *def* add
- \+/\- *def* unit_of_nearby

Modified src/analysis/specific_limits.lean
- \+ *lemma* normed_ring.tsum_geometric_of_norm_lt_1

Modified src/topology/algebra/ring.lean
- \+ *lemma* mul_left_continuous
- \+ *lemma* mul_right_continuous



## [2020-07-31 16:13:36](https://github.com/leanprover-community/mathlib/commit/3ae893d)
fix(tactic/simps): do not reach unreachable code ([#3637](https://github.com/leanprover-community/mathlib/pull/3637))
Fixes [#3636](https://github.com/leanprover-community/mathlib/pull/3636)
#### Estimated changes
Modified src/tactic/simps.lean


Modified test/simps.lean
- \+ *def* test_prop_class



## [2020-07-30 22:46:17](https://github.com/leanprover-community/mathlib/commit/f78a012)
feat(group_theory/subgroup): Add `mem_infi` and `coe_infi` ([#3634](https://github.com/leanprover-community/mathlib/pull/3634))
These already existed for submonoid, but were not lifted to subgroup.
Also adds some missing `norm_cast` attributes to similar lemmas.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* mem_infi
- \+ *lemma* coe_infi

Modified src/group_theory/submonoid/basic.lean




## [2020-07-30 21:46:00](https://github.com/leanprover-community/mathlib/commit/985a56b)
ci(fetch_olean_cache.sh): error handling ([#3628](https://github.com/leanprover-community/mathlib/pull/3628))
Previously, the CI would be interrupted if extracting the olean cache failed. After this PR, if that step fails, all oleans are deleted and then CI continues.
I also changed the search for ancestor commits with caches to look for `.xz` files instead of `.gz` files, for consistency.
#### Estimated changes
Modified scripts/fetch_olean_cache.sh




## [2020-07-30 20:16:57](https://github.com/leanprover-community/mathlib/commit/1a393e7)
feat(tactic/explode): support exploding "let" expressions and improve handling of "have" expressions ([#3632](https://github.com/leanprover-community/mathlib/pull/3632))
The current #explode has little effect on proofs using "let" expressions, e.g., #explode nat.exists_infinite_primes. #explode also
occasionally ignores certain dependencies due to macros occurring in "have" expressions. See examples below. This PR fixes these issues.
theorem foo {p q : Prop}: p → p :=
λ hp, have hh : p, from hp, hh
#explode foo -- missing dependencies at forall introduction
theorem bar {p q : Prop}: p → p :=
λ hp, (λ (hh : p), hh) hp
#explode bar -- expected behavior
#### Estimated changes
Modified src/tactic/explode.lean




## [2020-07-30 17:59:32](https://github.com/leanprover-community/mathlib/commit/43ccce5)
feat(geometry): first stab on Lie groups ([#3529](https://github.com/leanprover-community/mathlib/pull/3529))
#### Estimated changes
Modified src/algebra/group/defs.lean
- \+ *def* left_mul
- \+ *def* right_mul

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_at_fst
- \+ *lemma* times_cont_diff_within_at_fst
- \+ *lemma* times_cont_diff_at_snd
- \+ *lemma* times_cont_diff_within_at_snd
- \+ *lemma* times_cont_diff_add
- \+/\- *lemma* times_cont_diff.add
- \+ *lemma* times_cont_diff_neg
- \+/\- *lemma* times_cont_diff.neg
- \+ *lemma* times_cont_diff_within_at.prod_map'
- \+ *lemma* times_cont_diff_within_at.prod_map
- \+ *lemma* times_cont_diff_on.prod_map
- \+ *lemma* times_cont_diff_at.prod_map
- \+ *lemma* times_cont_diff_at.prod_map'
- \+ *lemma* times_cont_diff.prod_map
- \- *lemma* times_cont_diff_on.map_prod

Modified src/data/equiv/local_equiv.lean


Created src/geometry/algebra/lie_group.lean
- \+ *lemma* smooth_mul
- \+ *lemma* smooth.mul
- \+ *lemma* smooth_left_mul
- \+ *lemma* smooth_right_mul
- \+ *lemma* smooth_on.mul
- \+ *lemma* smooth_pow
- \+ *lemma* smooth_inv
- \+ *lemma* smooth.inv
- \+ *lemma* smooth_on.inv

Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* times_cont_mdiff.smooth
- \+ *lemma* smooth.times_cont_mdiff
- \+ *lemma* times_cont_mdiff_on.smooth_on
- \+ *lemma* smooth_on.times_cont_mdiff_on
- \+ *lemma* times_cont_mdiff_at.smooth_at
- \+ *lemma* smooth_at.times_cont_mdiff_at
- \+ *lemma* times_cont_mdiff_within_at.smooth_within_at
- \+ *lemma* smooth_within_at.times_cont_mdiff_within_at
- \+ *lemma* smooth.smooth_at
- \+ *lemma* smooth_at_univ
- \+ *lemma* smooth_on_univ
- \+ *lemma* times_cont_mdiff_within_at_iff
- \+ *lemma* smooth_within_at_iff
- \+ *lemma* smooth_on_iff
- \+ *lemma* smooth_iff
- \+ *lemma* smooth_at.smooth_within_at
- \+ *lemma* smooth.smooth_on
- \+ *lemma* smooth_within_at.smooth_at
- \+/\- *lemma* times_cont_mdiff_within_at.comp
- \+/\- *lemma* times_cont_mdiff_within_at.comp'
- \+/\- *lemma* times_cont_mdiff_at.comp
- \+ *lemma* times_cont_mdiff.comp_times_cont_mdiff_on
- \+ *lemma* smooth.comp_smooth_on
- \+ *lemma* smooth_id
- \+ *lemma* smooth_on_id
- \+ *lemma* smooth_at_id
- \+ *lemma* smooth_within_at_id
- \+ *lemma* smooth_const
- \+ *lemma* smooth_on_const
- \+ *lemma* smooth_at_const
- \+ *lemma* smooth_within_at_const
- \+ *lemma* times_cont_mdiff_proj
- \+ *lemma* smooth_proj
- \+ *lemma* times_cont_mdiff_on_proj
- \+ *lemma* smooth_on_proj
- \+ *lemma* times_cont_mdiff_at_proj
- \+ *lemma* smooth_at_proj
- \+ *lemma* times_cont_mdiff_within_at_proj
- \+ *lemma* smooth_within_at_proj
- \+ *lemma* times_cont_mdiff_within_at.prod_mk
- \+ *lemma* times_cont_mdiff_at.prod_mk
- \+ *lemma* times_cont_mdiff_on.prod_mk
- \+ *lemma* times_cont_mdiff.prod_mk
- \+ *lemma* smooth_within_at.prod_mk
- \+ *lemma* smooth_at.prod_mk
- \+ *lemma* smooth_on.prod_mk
- \+ *lemma* smooth.prod_mk
- \+ *lemma* times_cont_mdiff_within_at_fst
- \+ *lemma* times_cont_mdiff_at_fst
- \+ *lemma* times_cont_mdiff_on_fst
- \+ *lemma* times_cont_mdiff_fst
- \+ *lemma* smooth_within_at_fst
- \+ *lemma* smooth_at_fst
- \+ *lemma* smooth_on_fst
- \+ *lemma* smooth_fst
- \+ *lemma* times_cont_mdiff_within_at_snd
- \+ *lemma* times_cont_mdiff_at_snd
- \+ *lemma* times_cont_mdiff_on_snd
- \+ *lemma* times_cont_mdiff_snd
- \+ *lemma* smooth_within_at_snd
- \+ *lemma* smooth_at_snd
- \+ *lemma* smooth_on_snd
- \+ *lemma* smooth_snd
- \+ *lemma* smooth_iff_proj_smooth
- \+ *lemma* times_cont_mdiff_within_at.prod_map'
- \+ *lemma* times_cont_mdiff_within_at.prod_map
- \+ *lemma* times_cont_mdiff_at.prod_map
- \+ *lemma* times_cont_mdiff_at.prod_map'
- \+ *lemma* times_cont_mdiff_on.prod_map
- \+ *lemma* times_cont_mdiff.prod_map
- \+ *lemma* smooth_within_at.prod_map
- \+ *lemma* smooth_at.prod_map
- \+ *lemma* smooth_on.prod_map
- \+ *lemma* smooth.prod_map
- \+ *def* smooth_within_at
- \+ *def* smooth_at
- \+ *def* smooth_on
- \+ *def* smooth

Modified src/topology/continuous_on.lean
- \+ *lemma* nhds_within_prod
- \+ *lemma* continuous_on_fst
- \+ *lemma* continuous_within_at_fst
- \+ *lemma* continuous_on_snd
- \+ *lemma* continuous_within_at_snd



## [2020-07-30 13:59:09](https://github.com/leanprover-community/mathlib/commit/77f3fa4)
feat(tactic/interactive_expr): add copy button to type tooltip ([#3633](https://github.com/leanprover-community/mathlib/pull/3633))
There should now be a 'copy expression' button in each tooltip which can
be used to copy the current expression to the clipboard.
![image](https://user-images.githubusercontent.com/5064353/88916012-374ff580-d25d-11ea-8260-8149966fc84a.png)
I have not tested on windows yet.
Also broke out `widget_override.goals_accomplished_message` so that
users can override it. For example:
```
meta def my_new_msg {α : Type} : widget.html α := "my message"
attribute [vm_override my_new_msg] widget_override.goals_accomplished_message
```
#### Estimated changes
Modified src/tactic/interactive_expr.lean




## [2020-07-30 13:18:00](https://github.com/leanprover-community/mathlib/commit/e7075b8)
chore(topology/algebra/ordered): fix assumptions in some lemmas ([#3629](https://github.com/leanprover-community/mathlib/pull/3629))
* Some `nhds_within_I??_eq_nhds_within_I??` lemmas assumed strict
  inequalities when this was not needed.
* Remove TFAEs that only stated equality of three `nhds_within`s.
  Prove equality of `nhds_within`s instead.
* Genralize `I??_mem_nhds_within_I??` to `order_closed_topology`.
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* Ioo_mem_nhds_within_Ioi
- \+/\- *lemma* Ioc_mem_nhds_within_Ioi
- \+/\- *lemma* Ico_mem_nhds_within_Ioi
- \+/\- *lemma* Icc_mem_nhds_within_Ioi
- \+/\- *lemma* nhds_within_Ioo_eq_nhds_within_Ioi
- \+/\- *lemma* continuous_within_at_Ioc_iff_Ioi
- \+/\- *lemma* continuous_within_at_Ioo_iff_Ioi
- \+/\- *lemma* Ioo_mem_nhds_within_Iio
- \+/\- *lemma* Ico_mem_nhds_within_Iio
- \+/\- *lemma* Ioc_mem_nhds_within_Iio
- \+/\- *lemma* Icc_mem_nhds_within_Iio
- \+/\- *lemma* Ioo_mem_nhds_within_Ici
- \+/\- *lemma* Ioc_mem_nhds_within_Ici
- \+/\- *lemma* Ico_mem_nhds_within_Ici
- \+/\- *lemma* Icc_mem_nhds_within_Ici
- \+/\- *lemma* nhds_within_Ico_eq_nhds_within_Ici
- \+/\- *lemma* continuous_within_at_Icc_iff_Ici
- \+/\- *lemma* continuous_within_at_Ico_iff_Ici
- \+/\- *lemma* Ioo_mem_nhds_within_Iic
- \+/\- *lemma* Ico_mem_nhds_within_Iic
- \+/\- *lemma* Ioc_mem_nhds_within_Iic
- \+/\- *lemma* Icc_mem_nhds_within_Iic
- \+/\- *lemma* continuous_within_at_Icc_iff_Iic
- \+/\- *lemma* continuous_within_at_Ioc_iff_Iic
- \- *lemma* tfae_mem_nhds_within_Ioi'
- \- *lemma* tfae_mem_nhds_within_Iio'
- \- *lemma* tfae_mem_nhds_within_Ici'
- \- *lemma* tfae_mem_nhds_within_Iic'



## [2020-07-30 08:41:45](https://github.com/leanprover-community/mathlib/commit/29d5f11)
chore(algebra/group_with_zero): weaken assumptions in some lemmas ([#3630](https://github.com/leanprover-community/mathlib/pull/3630))
#### Estimated changes
Modified src/algebra/field.lean
- \+/\- *lemma* map_inv
- \+/\- *lemma* map_div

Modified src/algebra/group/hom.lean
- \+/\- *lemma* injective_iff

Modified src/algebra/group_with_zero.lean
- \+/\- *lemma* map_units_inv

Modified src/algebra/ring/basic.lean
- \+/\- *theorem* injective_iff



## [2020-07-30 07:34:56](https://github.com/leanprover-community/mathlib/commit/e1fa5cb)
feat(linear_algebra): invariant basis number property ([#3560](https://github.com/leanprover-community/mathlib/pull/3560))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* bot_ne_top

Created src/linear_algebra/invariant_basis_number.lean
- \+ *lemma* eq_of_fin_equiv
- \+ *lemma* nontrivial_of_invariant_basis_number
- \+ *lemma* invariant_basis_number_field

Modified src/ring_theory/ideals.lean
- \+ *lemma* mem_pi
- \+ *lemma* map_pi
- \+ *def* pi



## [2020-07-30 05:41:44](https://github.com/leanprover-community/mathlib/commit/03c302d)
feat(field_theory/fixed): field is separable over fixed subfield under group action ([#3568](https://github.com/leanprover-community/mathlib/pull/3568))
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \+ *theorem* is_unit_map
- \+ *theorem* gcd_map
- \+ *theorem* is_coprime_map

Modified src/field_theory/fixed.lean


Modified src/field_theory/separable.lean
- \+ *lemma* separable_X_sub_C
- \+ *lemma* separable_prod'
- \+ *lemma* separable_prod
- \+ *lemma* separable.inj_of_prod_X_sub_C
- \+ *lemma* separable.injective_of_prod_X_sub_C
- \+ *lemma* separable_prod_X_sub_C_iff'
- \+ *lemma* separable_prod_X_sub_C_iff
- \+ *theorem* separable_map
- \+ *def* is_separable



## [2020-07-29 23:48:24](https://github.com/leanprover-community/mathlib/commit/ef89e9a)
feat(data/qpf): compositional data type framework for inductive / coinductive types ([#3317](https://github.com/leanprover-community/mathlib/pull/3317))
First milestone of the QPF project. Includes multivariate quotients of polynomial functors and compiler for coinductive types.
Not included in this PR
 * nested inductive / coinductive data types
 * universe polymorphism with more than one variable
 * inductive / coinductive families
 * equation compiler
 * efficient byte code implementation
Those are coming in future PRs
#### Estimated changes
Created src/data/pfunctor/multivariate/M.lean
- \+ *lemma* M.bisim_lemma
- \+ *theorem* M.dest'_eq_dest'
- \+ *theorem* M.dest_eq_dest'
- \+ *theorem* M.dest_corec'
- \+ *theorem* M.dest_corec
- \+ *theorem* M.bisim
- \+ *theorem* M.bisim₀
- \+ *theorem* M.bisim'
- \+ *theorem* M.dest_map
- \+ *theorem* M.map_dest
- \+ *def* Mp
- \+ *def* M
- \+ *def* M.corec_shape
- \+ *def* cast_dropB
- \+ *def* cast_lastB
- \+ *def* M.corec_contents
- \+ *def* M.corec'
- \+ *def* M.corec
- \+ *def* M.path_dest_left
- \+ *def* M.path_dest_right
- \+ *def* M.dest'
- \+ *def* M.dest
- \+ *def* M.mk

Created src/data/pfunctor/multivariate/W.lean
- \+ *theorem* W_path_dest_left_W_path_cases_on
- \+ *theorem* W_path_dest_right_W_path_cases_on
- \+ *theorem* W_path_cases_on_eta
- \+ *theorem* comp_W_path_cases_on
- \+ *theorem* Wp_rec_eq
- \+ *theorem* Wp_ind
- \+ *theorem* W_rec_eq
- \+ *theorem* W_ind
- \+ *theorem* W_cases
- \+ *theorem* W_mk_eq
- \+ *theorem* W_map_W_mk
- \+ *theorem* map_obj_append1
- \+ *theorem* W_dest'_W_mk
- \+ *theorem* W_dest'_W_mk'
- \+ *def* W_path_cases_on
- \+ *def* W_path_dest_left
- \+ *def* W_path_dest_right
- \+ *def* Wp
- \+ *def* W
- \+ *def* Wp_mk
- \+ *def* Wp_rec
- \+ *def* W_mk
- \+ *def* W_rec
- \+ *def* W_map
- \+ *def* obj_append1
- \+ *def* W_mk'
- \+ *def* W_dest'

Modified src/data/pfunctor/multivariate/basic.lean


Modified src/data/pfunctor/univariate/M.lean
- \- *lemma* R_is_bisimulation
- \- *lemma* coinduction
- \- *lemma* coinduction'

Modified src/data/qpf/multivariate/basic.lean


Created src/data/qpf/multivariate/constructions/cofix.lean
- \+ *lemma* cofix.mk_dest
- \+ *lemma* cofix.dest_mk
- \+ *lemma* cofix.ext
- \+ *lemma* cofix.ext_mk
- \+ *lemma* cofix.abs_repr
- \+ *theorem* corecF_eq
- \+ *theorem* cofix.dest_corec
- \+ *theorem* cofix.bisim_rel
- \+ *theorem* cofix.bisim
- \+ *theorem* cofix.bisim₂
- \+ *theorem* cofix.bisim'
- \+ *theorem* liftr_map
- \+ *theorem* liftr_map_last
- \+ *theorem* liftr_map_last'
- \+ *theorem* corec_roll
- \+ *theorem* cofix.dest_corec'
- \+ *theorem* cofix.dest_corec₁
- \+ *def* corecF
- \+ *def* is_precongr
- \+ *def* Mcongr
- \+ *def* cofix
- \+ *def* Mrepr
- \+ *def* cofix.map
- \+ *def* cofix.corec
- \+ *def* cofix.dest
- \+ *def* cofix.abs
- \+ *def* cofix.repr
- \+ *def* cofix.corec'₁
- \+ *def* cofix.corec'
- \+ *def* cofix.corec₁
- \+ *def* cofix.mk

Created src/data/qpf/multivariate/constructions/comp.lean
- \+ *lemma* map_mk
- \+ *lemma* get_map
- \+ *def* comp

Created src/data/qpf/multivariate/constructions/const.lean
- \+ *lemma* map_mk
- \+ *lemma* get_map
- \+ *def* const

Created src/data/qpf/multivariate/constructions/fix.lean
- \+ *theorem* recF_eq
- \+ *theorem* recF_eq'
- \+ *theorem* recF_eq_of_Wequiv
- \+ *theorem* Wequiv.abs'
- \+ *theorem* Wequiv.refl
- \+ *theorem* Wequiv.symm
- \+ *theorem* Wrepr_W_mk
- \+ *theorem* Wrepr_equiv
- \+ *theorem* Wequiv_map
- \+ *theorem* fix.rec_eq
- \+ *theorem* fix.ind_aux
- \+ *theorem* fix.ind_rec
- \+ *theorem* fix.rec_unique
- \+ *theorem* fix.mk_dest
- \+ *theorem* fix.dest_mk
- \+ *theorem* fix.ind
- \+ *def* recF
- \+ *def* Wrepr
- \+ *def* W_setoid
- \+ *def* fix
- \+ *def* fix.map
- \+ *def* fix.rec
- \+ *def* fix_to_W
- \+ *def* fix.mk
- \+ *def* fix.dest
- \+ *def* fix.drec

Created src/data/qpf/multivariate/constructions/prj.lean
- \+ *def* prj
- \+ *def* prj.map
- \+ *def* prj.P
- \+ *def* prj.abs
- \+ *def* prj.repr

Created src/data/qpf/multivariate/constructions/quot.lean
- \+ *def* quotient_qpf
- \+ *def* quot1
- \+ *def* quot1.map
- \+ *def* quot1.mvfunctor

Created src/data/qpf/multivariate/constructions/sigma.lean
- \+ *def* sigma
- \+ *def* pi

Created src/data/qpf/multivariate/default.lean


Modified src/data/typevec.lean
- \+ *lemma* drop_fun_diag
- \+ *lemma* drop_fun_subtype_val
- \+ *lemma* last_fun_subtype_val
- \+ *lemma* drop_fun_to_subtype
- \+ *lemma* last_fun_to_subtype
- \+ *lemma* drop_fun_of_subtype
- \+ *lemma* last_fun_of_subtype
- \+ *lemma* drop_fun_rel_last
- \+ *lemma* drop_fun_prod
- \+ *lemma* last_fun_prod
- \+ *lemma* drop_fun_from_append1_drop_last
- \+ *lemma* last_fun_from_append1_drop_last
- \+ *lemma* drop_fun_id
- \+ *lemma* prod_map_id
- \+ *lemma* subtype_val_diag_sub
- \+ *lemma* to_subtype_of_subtype
- \+ *lemma* to_subtype_of_subtype_assoc
- \+ *def* from_append1_drop_last



## [2020-07-30 01:14:09+02:00](https://github.com/leanprover-community/mathlib/commit/4985ad5)
Revert "feat(topology): path connected spaces"
This reverts commit 9208c2bd1f6c8dedc0cd1646dd107842f05b0b0c.
#### Estimated changes
Modified src/order/filter/bases.lean
- \- *lemma* has_basis.to_has_basis

Deleted src/topology/path_connected.lean
- \- *lemma* Icc_zero_one_symm
- \- *lemma* coe_I_zero
- \- *lemma* coe_I_one
- \- *lemma* I_symm_zero
- \- *lemma* I_symm_one
- \- *lemma* continuous_I_symm
- \- *lemma* proj_I_I
- \- *lemma* range_proj_I
- \- *lemma* Iic_def
- \- *lemma* continuous_proj_I
- \- *lemma* continuous.I_extend
- \- *lemma* I_extend_extends
- \- *lemma* I_extend_zero
- \- *lemma* I_extend_one
- \- *lemma* I_extend_range
- \- *lemma* joined.refl
- \- *lemma* joined.symm
- \- *lemma* joined.continuous_extend
- \- *lemma* joined.extend_zero
- \- *lemma* joined.extend_one
- \- *lemma* joined.trans
- \- *lemma* joined_in.mem
- \- *lemma* joined_in.continuous_extend
- \- *lemma* joined_in.extend_zero
- \- *lemma* joined_in.extend_one
- \- *lemma* joined_in.continuous_map
- \- *lemma* joined_in.map_zero
- \- *lemma* joined_in.map_one
- \- *lemma* joined_in.extend_map_continuous
- \- *lemma* joined_in.extend_map_zero
- \- *lemma* joined_in.extend_map_one
- \- *lemma* joined_in.joined
- \- *lemma* joined_in_iff_joined
- \- *lemma* joined_in_univ
- \- *lemma* joined_in.mono
- \- *lemma* joined_in.refl
- \- *lemma* joined_in.symm
- \- *lemma* joined_in.trans
- \- *lemma* mem_path_component_self
- \- *lemma* path_component.nonempty
- \- *lemma* mem_path_component_of_mem
- \- *lemma* path_component_symm
- \- *lemma* path_component_congr
- \- *lemma* path_component_subset_component
- \- *lemma* path_component_in_univ
- \- *lemma* joined.mem_path_component
- \- *lemma* is_path_connected_iff_eq
- \- *lemma* is_path_connected.joined_in
- \- *lemma* is_path_connected_iff
- \- *lemma* is_path_connected.image
- \- *lemma* is_path_connected.mem_path_component
- \- *lemma* is_path_connected.union
- \- *lemma* is_path_connected.preimage_coe
- \- *lemma* continuous_path
- \- *lemma* path_zero
- \- *lemma* path_one
- \- *lemma* is_path_connected_iff_path_connected_space
- \- *lemma* path_connected_space_iff_univ
- \- *lemma* path_connected_space_iff_eq
- \- *lemma* loc_path_connected_of_bases
- \- *lemma* path_connected_space_iff_connected_space
- \- *lemma* path_connected_subset_basis
- \- *lemma* loc_path_connected_of_is_open
- \- *lemma* is_open.is_connected_iff_is_path_connected
- \- *def* I_symm
- \- *def* proj_I
- \- *def* I_extend
- \- *def* joined
- \- *def* joined.extend
- \- *def* joined_in
- \- *def* joined_in.extend
- \- *def* joined_in.map
- \- *def* joined_in.extend_map
- \- *def* path_component
- \- *def* path_component_in
- \- *def* is_path_connected
- \- *def* path



## [2020-07-30 01:12:56+02:00](https://github.com/leanprover-community/mathlib/commit/9208c2b)
feat(topology): path connected spaces
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* has_basis.to_has_basis

Created src/topology/path_connected.lean
- \+ *lemma* Icc_zero_one_symm
- \+ *lemma* coe_I_zero
- \+ *lemma* coe_I_one
- \+ *lemma* I_symm_zero
- \+ *lemma* I_symm_one
- \+ *lemma* continuous_I_symm
- \+ *lemma* proj_I_I
- \+ *lemma* range_proj_I
- \+ *lemma* Iic_def
- \+ *lemma* continuous_proj_I
- \+ *lemma* continuous.I_extend
- \+ *lemma* I_extend_extends
- \+ *lemma* I_extend_zero
- \+ *lemma* I_extend_one
- \+ *lemma* I_extend_range
- \+ *lemma* joined.refl
- \+ *lemma* joined.symm
- \+ *lemma* joined.continuous_extend
- \+ *lemma* joined.extend_zero
- \+ *lemma* joined.extend_one
- \+ *lemma* joined.trans
- \+ *lemma* joined_in.mem
- \+ *lemma* joined_in.continuous_extend
- \+ *lemma* joined_in.extend_zero
- \+ *lemma* joined_in.extend_one
- \+ *lemma* joined_in.continuous_map
- \+ *lemma* joined_in.map_zero
- \+ *lemma* joined_in.map_one
- \+ *lemma* joined_in.extend_map_continuous
- \+ *lemma* joined_in.extend_map_zero
- \+ *lemma* joined_in.extend_map_one
- \+ *lemma* joined_in.joined
- \+ *lemma* joined_in_iff_joined
- \+ *lemma* joined_in_univ
- \+ *lemma* joined_in.mono
- \+ *lemma* joined_in.refl
- \+ *lemma* joined_in.symm
- \+ *lemma* joined_in.trans
- \+ *lemma* mem_path_component_self
- \+ *lemma* path_component.nonempty
- \+ *lemma* mem_path_component_of_mem
- \+ *lemma* path_component_symm
- \+ *lemma* path_component_congr
- \+ *lemma* path_component_subset_component
- \+ *lemma* path_component_in_univ
- \+ *lemma* joined.mem_path_component
- \+ *lemma* is_path_connected_iff_eq
- \+ *lemma* is_path_connected.joined_in
- \+ *lemma* is_path_connected_iff
- \+ *lemma* is_path_connected.image
- \+ *lemma* is_path_connected.mem_path_component
- \+ *lemma* is_path_connected.union
- \+ *lemma* is_path_connected.preimage_coe
- \+ *lemma* continuous_path
- \+ *lemma* path_zero
- \+ *lemma* path_one
- \+ *lemma* is_path_connected_iff_path_connected_space
- \+ *lemma* path_connected_space_iff_univ
- \+ *lemma* path_connected_space_iff_eq
- \+ *lemma* loc_path_connected_of_bases
- \+ *lemma* path_connected_space_iff_connected_space
- \+ *lemma* path_connected_subset_basis
- \+ *lemma* loc_path_connected_of_is_open
- \+ *lemma* is_open.is_connected_iff_is_path_connected
- \+ *def* I_symm
- \+ *def* proj_I
- \+ *def* I_extend
- \+ *def* joined
- \+ *def* joined.extend
- \+ *def* joined_in
- \+ *def* joined_in.extend
- \+ *def* joined_in.map
- \+ *def* joined_in.extend_map
- \+ *def* path_component
- \+ *def* path_component_in
- \+ *def* is_path_connected
- \+ *def* path



## [2020-07-29 21:50:21](https://github.com/leanprover-community/mathlib/commit/86c83c3)
feat(topology): two missing connectedness lemmas ([#3626](https://github.com/leanprover-community/mathlib/pull/3626))
From the sphere eversion project.
#### Estimated changes
Modified src/topology/subset_properties.lean
- \+ *lemma* is_preconnected_iff_preconnected_space
- \+ *lemma* is_connected_iff_connected_space



## [2020-07-29 20:38:16](https://github.com/leanprover-community/mathlib/commit/ebeeee7)
feat(filters): a couple more lemmas ([#3625](https://github.com/leanprover-community/mathlib/pull/3625))
Random lemmas gathered while thinking about https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/nhds_left.20and.20nhds_right
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* union_distrib_Inter_right
- \+ *lemma* union_distrib_Inter_left

Modified src/order/filter/bases.lean
- \+ *lemma* has_basis.ext
- \+ *lemma* has_basis.sup
- \+ *lemma* has_basis_binfi_principal'

Modified src/order/filter/basic.lean
- \+ *lemma* infi_sup_left
- \+ *lemma* infi_sup_right
- \+ *lemma* binfi_sup_right
- \+ *lemma* binfi_sup_left
- \- *lemma* infi_sup_eq



## [2020-07-29 13:58:44](https://github.com/leanprover-community/mathlib/commit/652fb2e)
chore(doc/*): add README files ([#3623](https://github.com/leanprover-community/mathlib/pull/3623))
#### Estimated changes
Created docs/README.md


Created docs/contribute/README.md


Created docs/extras/README.md


Created docs/install/README.md


Created docs/theories/README.md




## [2020-07-29 11:45:51](https://github.com/leanprover-community/mathlib/commit/37e13a0)
feat(tactic/lint): quieter output by default ([#3622](https://github.com/leanprover-community/mathlib/pull/3622))
* The behavior of `lint-` hasn't changed.
* `lint` will now suppress the output of successful checks. If everything succeeds, it will print "All linting checks passed!"
* `lint+` behaves like the old `lint`. It prints a confirmation for each test.
Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/quiet.20linter
#### Estimated changes
Modified scripts/lint_mathlib.lean


Modified src/tactic/lint/default.lean


Modified src/tactic/lint/frontend.lean


Modified test/lint.lean




## [2020-07-29 11:19:36](https://github.com/leanprover-community/mathlib/commit/b0d1d17)
feat(data/ulift): add `monad ulift` and `monad plift` ([#3588](https://github.com/leanprover-community/mathlib/pull/3588))
We add `functor`/`applicative`/`monad` instances for `ulift` and `plift`.
#### Estimated changes
Modified src/data/ulift.lean
- \+ *lemma* rec.constant
- \- *lemma* plift.rec.constant
- \- *lemma* ulift.rec.constant



## [2020-07-29 08:21:11](https://github.com/leanprover-community/mathlib/commit/80f2762)
feat(topology): assorted topological lemmas ([#3619](https://github.com/leanprover-community/mathlib/pull/3619))
from the sphere eversion project
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* preimage_coe_nonempty
- \+ *theorem* union_diff_cancel'
- \+/\- *theorem* union_diff_cancel

Modified src/order/filter/bases.lean
- \+ *lemma* has_basis_iff
- \+ *lemma* has_basis.ex_mem
- \+ *lemma* has_basis.restrict
- \+ *lemma* has_basis.has_basis_self_subset

Modified src/order/filter/basic.lean
- \+ *lemma* not_ne_bot
- \+ *lemma* image_mem_sets
- \+ *lemma* image_coe_mem_sets

Modified src/topology/basic.lean
- \+ *lemma* closure_eq_interior_union_frontier
- \+ *lemma* closure_eq_self_union_frontier
- \+ *lemma* is_closed_iff_nhds

Modified src/topology/order.lean
- \+ *lemma* continuous_induced_rng'

Modified src/topology/subset_properties.lean
- \+ *lemma* is_connected_range
- \+ *lemma* connected_space_iff_connected_component
- \+ *lemma* eq_univ_of_nonempty_clopen
- \+ *def* connected_component_in



## [2020-07-29 00:35:48](https://github.com/leanprover-community/mathlib/commit/e14ba7b)
chore(scripts): update nolints.txt ([#3620](https://github.com/leanprover-community/mathlib/pull/3620))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-28 23:25:03](https://github.com/leanprover-community/mathlib/commit/e245254)
feat(category_theory/monoidal): λ_ (𝟙_ C) = ρ_ (𝟙_ C) ([#3556](https://github.com/leanprover-community/mathlib/pull/3556))
The incredibly tedious proof from the axioms that `λ_ (𝟙_ C) = ρ_ (𝟙_ C)` in any monoidal category.
One would hope that it falls out from a coherence theorem, but we're not close to having one, and I suspect that this result might be a step in any proof.
#### Estimated changes
Modified src/category_theory/monoidal/category.lean
- \+ *lemma* right_unitor_conjugation
- \+ *lemma* left_unitor_conjugation

Created src/category_theory/monoidal/unitors.lean
- \+ *lemma* cells_1_2
- \+ *lemma* cells_4
- \+ *lemma* cells_4'
- \+ *lemma* cells_3_4
- \+ *lemma* cells_1_4
- \+ *lemma* cells_6
- \+ *lemma* cells_6'
- \+ *lemma* cells_5_6
- \+ *lemma* cells_7
- \+ *lemma* cells_1_7
- \+ *lemma* cells_8
- \+ *lemma* cells_14
- \+ *lemma* cells_9
- \+ *lemma* cells_10_13
- \+ *lemma* cells_9_13
- \+ *lemma* cells_15
- \+ *lemma* unitors_equal



## [2020-07-28 22:08:48](https://github.com/leanprover-community/mathlib/commit/2e6c488)
chore(order/complete_lattice): use `Prop` args in `infi_inf` etc ([#3611](https://github.com/leanprover-community/mathlib/pull/3611))
This way one can `rw binfi_inf` first, then prove `∃ i, p i`.
Also move some code up to make it available near `infi_inf`.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+/\- *lemma* infi_subtype'
- \+/\- *lemma* infi_subtype''
- \+/\- *lemma* infi_inf
- \+/\- *lemma* inf_infi
- \+/\- *lemma* binfi_inf
- \+/\- *theorem* infi_subtype

Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* prod_infi_left
- \+/\- *lemma* prod_infi_right

Modified src/topology/algebra/ordered.lean


Modified src/topology/bases.lean


Modified src/topology/continuous_on.lean




## [2020-07-28 21:33:31](https://github.com/leanprover-community/mathlib/commit/aafc486)
feat(topology/ordered): intervals frontiers ([#3617](https://github.com/leanprover-community/mathlib/pull/3617))
from the sphere eversion project
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+ *lemma* closure_Icc
- \+ *lemma* closure_Iic
- \+ *lemma* closure_Ici
- \+/\- *lemma* closure_Ioi
- \+/\- *lemma* closure_Iio
- \+/\- *lemma* closure_Ioo
- \+/\- *lemma* closure_Ioc
- \+/\- *lemma* closure_Ico
- \+ *lemma* frontier_Ici
- \+ *lemma* frontier_Iic
- \+ *lemma* frontier_Ioi
- \+ *lemma* frontier_Iio
- \+ *lemma* frontier_Icc
- \+ *lemma* frontier_Ioo
- \+ *lemma* frontier_Ico
- \+ *lemma* frontier_Ioc



## [2020-07-28 20:45:39](https://github.com/leanprover-community/mathlib/commit/5cd6eeb)
chore(ci): only store oleans in azure cache ([#3616](https://github.com/leanprover-community/mathlib/pull/3616))
#### Estimated changes
Modified .github/workflows/build.yml


Modified scripts/fetch_olean_cache.sh




## [2020-07-28 20:12:44](https://github.com/leanprover-community/mathlib/commit/4ae8752)
chore(data/mv_polynomial): use bundled homs ([#3595](https://github.com/leanprover-community/mathlib/pull/3595))
I've done a lot of the scut work, but there are still about half a dozen broken proofs, if anyone would like to take a bash at them!
#### Estimated changes
Modified src/algebra/category/CommRing/adjunctions.lean


Modified src/data/mv_polynomial.lean
- \+ *lemma* eval₂_hom_congr
- \+/\- *lemma* eval_monomial
- \+/\- *lemma* eval_C
- \+/\- *lemma* eval_X
- \+/\- *lemma* coeff_map
- \+/\- *lemma* smul_eval
- \+/\- *lemma* eval₂_sub
- \+/\- *lemma* eval₂_neg
- \+/\- *lemma* eval₂_hom_X
- \+/\- *lemma* eval₂_rename
- \- *lemma* eval_zero
- \- *lemma* eval_one
- \- *lemma* eval_add
- \- *lemma* eval_mul
- \- *lemma* eval_pow
- \- *lemma* map_pow
- \- *lemma* eval_sub
- \- *lemma* eval_neg
- \- *lemma* map_sub
- \- *lemma* map_neg
- \- *lemma* rename_zero
- \- *lemma* rename_one
- \- *lemma* rename_add
- \- *lemma* rename_neg
- \- *lemma* rename_sub
- \- *lemma* rename_mul
- \- *lemma* rename_pow
- \- *theorem* map_one
- \- *theorem* map_add
- \- *theorem* map_mul
- \+/\- *def* eval
- \+/\- *def* map
- \+/\- *def* rename

Modified src/field_theory/chevalley_warning.lean


Modified src/field_theory/mv_polynomial.lean
- \+/\- *lemma* map_range_eq_map
- \+/\- *lemma* evalₗ_apply

Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/polynomial/basic.lean




## [2020-07-28 19:31:16](https://github.com/leanprover-community/mathlib/commit/b765570)
chore(topology): rename interior_eq_of_open ([#3614](https://github.com/leanprover-community/mathlib/pull/3614))
This allows to use dot notation and is more consistent with
its closed twin is_closed.closure_eq
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/geometry/manifold/charted_space.lean


Modified src/geometry/manifold/local_invariant_properties.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/basic.lean
- \+ *lemma* is_open.interior_eq
- \- *lemma* interior_eq_of_open

Modified src/topology/continuous_on.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/opens.lean


Modified src/topology/subset_properties.lean




## [2020-07-28 17:35:02](https://github.com/leanprover-community/mathlib/commit/9f51e33)
feat(measure_theory/measurable_space): introduce `filter.is_measurably_generated` ([#3594](https://github.com/leanprover-community/mathlib/pull/3594))
Sometimes I want to extract an `is_measurable` witness of a `filter.eventually` statement.
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_measurable.nhds_within_is_measurably_generated

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* eventually.exists_measurable_mem
- \+ *lemma* principal_is_measurably_generated_iff

Modified src/measure_theory/measure_space.lean




## [2020-07-28 17:35:00](https://github.com/leanprover-community/mathlib/commit/7236938)
feat(measure_theory/measure_space): add `count_apply_infinite` ([#3592](https://github.com/leanprover-community/mathlib/pull/3592))
Also add some supporting lemmas about `set.infinite`.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* exists_subset_card_eq

Modified src/data/set/finite.lean
- \+ *lemma* infinite.exists_subset_card_eq
- \+ *theorem* infinite_coe_iff
- \+ *theorem* infinite.to_subtype

Modified src/measure_theory/measure_space.lean
- \+ *lemma* count_apply_finite
- \+ *lemma* count_apply_infinite
- \+ *lemma* count_apply_eq_top
- \+ *lemma* count_apply_lt_top



## [2020-07-28 17:02:06](https://github.com/leanprover-community/mathlib/commit/f6f6f8a)
feat(linear_algebra/affine_space): more affine subspace lemmas ([#3552](https://github.com/leanprover-community/mathlib/pull/3552))
Add more lemmas on affine subspaces that came up in the course of
proving existence and uniqueness of the circumcenter of a simplex in a
Euclidean space.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* vsub_set_singleton

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* vector_span_singleton
- \+ *lemma* coe_affine_span_singleton
- \+ *lemma* direction_sup
- \+ *lemma* direction_affine_span_insert
- \+ *lemma* mem_affine_span_insert_iff



## [2020-07-28 15:30:51](https://github.com/leanprover-community/mathlib/commit/7848f28)
feat(category_theory): Mon_ (Type u) ≌ Mon.{u} ([#3562](https://github.com/leanprover-community/mathlib/pull/3562))
Verifying that internal monoid objects in Type are the same thing as bundled monoid objects.
#### Estimated changes
Modified src/algebra/category/Group/zero.lean


Created src/category_theory/limits/shapes/types.lean
- \+ *lemma* terminal
- \+ *lemma* terminal_from
- \+ *lemma* prod
- \+ *lemma* prod_fst
- \+ *lemma* prod_snd
- \+ *lemma* prod_lift
- \+ *lemma* prod_map
- \+ *def* types_has_terminal
- \+ *def* types_has_binary_products
- \+ *def* types_has_products

Created src/category_theory/monoidal/internal.lean
- \+ *lemma* assoc_flip
- \+ *lemma* id_hom'
- \+ *lemma* comp_hom'
- \+ *def* id
- \+ *def* comp
- \+ *def* forget
- \+ *def* regular
- \+ *def* comap

Created src/category_theory/monoidal/internal/types.lean
- \+ *def* functor
- \+ *def* inverse
- \+ *def* Mon_Type_equivalence_Mon
- \+ *def* Mon_Type_equivalence_Mon_forget

Modified src/category_theory/monoidal/types.lean
- \+ *lemma* tensor_apply
- \+ *lemma* left_unitor_hom_apply
- \+ *lemma* left_unitor_inv_apply
- \+ *lemma* right_unitor_hom_apply
- \+ *lemma* right_unitor_inv_apply
- \+ *lemma* associator_hom_apply
- \+ *lemma* associator_inv_apply

Modified src/tactic/ext.lean
- \+ *lemma* unit.ext
- \+ *lemma* punit.ext

Modified test/ext.lean
- \- *lemma* unit.ext



## [2020-07-28 14:20:39](https://github.com/leanprover-community/mathlib/commit/9e841c8)
feat(data/list/basic): add a proof that `(a :: l) ≠ l` ([#3584](https://github.com/leanprover-community/mathlib/pull/3584))
`list.cons_ne_self` is motivated by the existence of `nat.succ_ne_self`.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* cons_ne_self



## [2020-07-28 13:45:08](https://github.com/leanprover-community/mathlib/commit/f1dfece)
feat(linear_algebra/affine_space): bundled affine independent families ([#3561](https://github.com/leanprover-community/mathlib/pull/3561))
Define `affine_space.simplex` as `n + 1` affine independent points,
with the specific case of `affine_space.triangle`.  I expect most
definitions and results for these types (such as `circumcenter` and
`circumradius`, which I'm currently working on) will be specific to
the case of Euclidean affine spaces, but some make sense in a more
general affine space context.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *lemma* mk_of_point_points
- \+ *def* mk_of_point



## [2020-07-28 11:47:58](https://github.com/leanprover-community/mathlib/commit/5a876ca)
feat(category_theory): monoidal_category (C ⥤ C) ([#3557](https://github.com/leanprover-community/mathlib/pull/3557))
#### Estimated changes
Created src/category_theory/monoidal/End.lean
- \+ *def* endofunctor_monoidal_category
- \+ *def* tensoring_right_monoidal

Modified src/category_theory/monoidal/category.lean
- \+ *def* tensoring_right

Modified src/category_theory/monoidal/functor.lean
- \+ *lemma* map_tensor
- \+ *lemma* map_left_unitor
- \+ *lemma* map_right_unitor



## [2020-07-28 10:21:52](https://github.com/leanprover-community/mathlib/commit/be99e53)
chore(ci): remove unused build step ([#3607](https://github.com/leanprover-community/mathlib/pull/3607))
#### Estimated changes
Modified .github/workflows/build.yml




## [2020-07-28 10:21:50](https://github.com/leanprover-community/mathlib/commit/f1ad7a8)
docs(topology/sheaves): better docs for presheaf ([#3596](https://github.com/leanprover-community/mathlib/pull/3596))
Add module doc-strings to two files.
#### Estimated changes
Modified src/topology/sheaves/presheaf.lean


Modified src/topology/sheaves/presheaf_of_functions.lean




## [2020-07-28 10:21:48](https://github.com/leanprover-community/mathlib/commit/35f1f63)
doc(topology/basic): docstrings for nhds and a few related lemmas ([#3548](https://github.com/leanprover-community/mathlib/pull/3548))
`nhds` was the only `def` in the file which didn't have an explanation, so I documented it.
I also went ahead and documented a few related lemmas which I felt were worth calling out.
#### Estimated changes
Modified src/topology/basic.lean




## [2020-07-28 09:27:12](https://github.com/leanprover-community/mathlib/commit/037821b)
chore(category_theory/limits/types): remove simp lemmas ([#3604](https://github.com/leanprover-community/mathlib/pull/3604))
No one wants to see how the sausage is being made.
Or at least, no one wants `simp` to show you without asking.
#### Estimated changes
Modified src/category_theory/limits/types.lean
- \+/\- *lemma* types_limit
- \+/\- *lemma* types_limit_π
- \+/\- *lemma* types_limit_pre
- \+/\- *lemma* types_limit_map
- \+/\- *lemma* types_limit_lift
- \+/\- *lemma* types_colimit
- \+/\- *lemma* types_colimit_ι
- \+/\- *lemma* types_colimit_pre
- \+/\- *lemma* types_colimit_map
- \+/\- *lemma* types_colimit_desc



## [2020-07-28 09:27:10](https://github.com/leanprover-community/mathlib/commit/a574db1)
refactor(algebra/category/*/limits): refactor concrete limits ([#3463](https://github.com/leanprover-community/mathlib/pull/3463))
We used to construct categorical limits for `AddCommGroup` and `CommRing`.
Now we construct them for
* `(Add)(Comm)Mon`
* `(Add)(Comm)Group`
* `(Comm)(Semi)Ring`
* `Module R`
* `Algebra R`
Even better, we reuse structure along the way, and show that all the relevant forgetful functors preserve limits.
We're still not at the point were this can either be done by
* automation, or
* noticing that everything is a model of a Lawvere theory
but ... maybe one day.
#### Estimated changes
Created src/algebra/category/Algebra/limits.lean
- \+ *def* sections_subalgebra
- \+ *def* limit_π_alg_hom
- \+ *def* limit
- \+ *def* limit_is_limit

Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/CommRing/limits.lean
- \+ *def* sections_subsemiring
- \+/\- *def* limit_π_ring_hom
- \+/\- *def* limit
- \+/\- *def* limit_is_limit
- \+ *def* forget₂_AddCommMon_preserves_limits_aux
- \+ *def* forget₂_Mon_preserves_limits_aux
- \+ *def* forget₂_AddCommGroup_preserves_limits_aux

Modified src/algebra/category/Group/limits.lean
- \+ *def* sections_subgroup
- \+ *def* forget₂_CommMon_preserves_limits_aux
- \+/\- *def* kernel_iso_ker_over
- \- *def* limit_π_add_monoid_hom
- \- *def* limit
- \- *def* limit_is_limit

Modified src/algebra/category/Group/zero.lean


Created src/algebra/category/Module/limits.lean
- \+ *def* sections_submodule
- \+ *def* limit_π_linear_map
- \+ *def* limit
- \+ *def* limit_is_limit

Modified src/algebra/category/Mon/basic.lean


Created src/algebra/category/Mon/limits.lean
- \+ *def* sections_submonoid
- \+ *def* limit_π_monoid_hom
- \+ *def* limit
- \+ *def* limit_is_limit

Modified src/algebra/module/basic.lean
- \- *lemma* coe_injective
- \+ *theorem* coe_inj

Modified src/algebra/ring/pi.lean
- \+ *lemma* ring_hom_apply

Modified src/analysis/normed_space/operator_norm.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/concrete_category/bundled_hom.lean


Modified src/category_theory/limits/creates.lean
- \+ *def* creates_limit_of_fully_faithful_of_lift
- \+ *def* creates_limit_of_fully_faithful_of_iso

Modified src/category_theory/reflect_isomorphisms.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra_map_apply

Modified src/topology/algebra/module.lean
- \+ *theorem* coe_inj
- \- *theorem* coe_injective'



## [2020-07-28 08:55:31](https://github.com/leanprover-community/mathlib/commit/ce70305)
feat(category_theory): monoidal_category (C ⥤ D) when D is monoidal ([#3571](https://github.com/leanprover-community/mathlib/pull/3571))
When `C` is any category, and `D` is a monoidal category,
there is a natural "pointwise" monoidal structure on `C ⥤ D`.
The initial intended application is tensor product of presheaves.
#### Estimated changes
Created src/category_theory/monoidal/functor_category.lean
- \+ *lemma* tensor_unit_obj
- \+ *lemma* tensor_unit_map
- \+ *lemma* tensor_obj_obj
- \+ *lemma* tensor_obj_map
- \+ *lemma* tensor_hom_app
- \+ *lemma* left_unitor_hom_app
- \+ *lemma* left_unitor_inv_app
- \+ *lemma* right_unitor_hom_app
- \+ *lemma* right_unitor_inv_app
- \+ *lemma* associator_hom_app
- \+ *lemma* associator_inv_app
- \+ *def* tensor_obj
- \+ *def* tensor_hom



## [2020-07-28 07:54:19](https://github.com/leanprover-community/mathlib/commit/3576381)
chore(ring_theory/subsemiring): tidy up docstrings ([#3580](https://github.com/leanprover-community/mathlib/pull/3580))
#### Estimated changes
Modified src/ring_theory/subsemiring.lean




## [2020-07-28 02:35:47](https://github.com/leanprover-community/mathlib/commit/865e888)
chore(*): make sure definitions don't generate `s x`, `s : set _` ([#3591](https://github.com/leanprover-community/mathlib/pull/3591))
Fix the following definitions: `subtype.fintype`, `pfun.dom`, `pfun.as_subtype`, `pfun.equiv_subtype`.
#### Estimated changes
Modified src/data/fintype/basic.lean


Modified src/data/pfun.lean
- \+/\- *def* dom
- \+/\- *def* as_subtype

Modified src/data/set/basic.lean
- \+ *lemma* coe_preimage_self
- \+/\- *theorem* coe_image_subset

Modified src/data/set/countable.lean


Modified src/data/set/lattice.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* mem_span_singleton_self



## [2020-07-28 02:35:45](https://github.com/leanprover-community/mathlib/commit/d04e3fc)
feat(linear_algebra/char_poly): relates the characteristic polynomial to trace, determinant, and dimension ([#3536](https://github.com/leanprover-community/mathlib/pull/3536))
adds lemmas about the number of fixed points of a permutation
adds lemmas connecting the trace, determinant, and dimension of a matrix to its characteristic polynomial
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* scalar.commute

Modified src/group_theory/perm/cycles.lean
- \+ *lemma* one_lt_nonfixed_point_card_of_ne_one
- \+ *lemma* fixed_point_card_lt_of_ne_one

Created src/linear_algebra/char_poly/coeff.lean
- \+ *lemma* char_matrix_apply_nat_degree
- \+ *lemma* char_matrix_apply_nat_degree_le
- \+ *lemma* char_poly_sub_diagonal_degree_lt
- \+ *lemma* char_poly_coeff_eq_prod_coeff_of_le
- \+ *lemma* det_of_card_zero
- \+ *lemma* char_poly_monic_of_nontrivial
- \+ *lemma* char_poly_monic
- \+ *lemma* mat_poly_equiv_eval
- \+ *lemma* eval_det
- \+ *theorem* char_poly_degree_eq_dim
- \+ *theorem* char_poly_nat_degree_eq_dim
- \+ *theorem* trace_eq_neg_char_poly_coeff
- \+ *theorem* det_eq_sign_char_poly_coeff

Modified src/linear_algebra/determinant.lean
- \+ *lemma* ring_hom.map_det
- \+ *lemma* alg_hom.map_det



## [2020-07-28 02:35:42](https://github.com/leanprover-community/mathlib/commit/a9481d9)
feat(analysis/convex/basic): add lemmas about transformations of convex sets and functions ([#3524](https://github.com/leanprover-community/mathlib/pull/3524))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex.combo_to_vadd
- \+ *lemma* convex.combo_affine_apply
- \+ *lemma* convex.affine_preimage
- \+ *lemma* convex.affine_image
- \+/\- *lemma* convex.linear_image
- \+/\- *lemma* convex.is_linear_image
- \+/\- *lemma* convex.is_linear_preimage
- \+ *lemma* convex.translate_preimage_right
- \+ *lemma* convex.translate_preimage_left
- \+ *lemma* convex_on.comp_affine_map
- \+ *lemma* convex_on.comp_linear_map
- \+ *lemma* convex_on.translate_right
- \+ *lemma* convex_on.translate_left

Modified src/analysis/convex/cone.lean




## [2020-07-28 02:35:40](https://github.com/leanprover-community/mathlib/commit/005201a)
feat(linear_algebra/adic_completion): basic definitions about completions of modules ([#3452](https://github.com/leanprover-community/mathlib/pull/3452))
#### Estimated changes
Created src/linear_algebra/adic_completion.lean
- \+ *lemma* induction_on
- \+ *lemma* of_apply
- \+ *lemma* coe_eval
- \+ *lemma* eval_apply
- \+ *lemma* eval_of
- \+ *lemma* eval_comp_of
- \+ *lemma* range_eval
- \+ *lemma* ext
- \+ *theorem* infi_pow_smul
- \+ *theorem* lift_of
- \+ *theorem* lift_comp_of
- \+ *theorem* lift_eq
- \+ *def* is_Hausdorff
- \+ *def* is_precomplete
- \+ *def* is_adic_complete
- \+ *def* Hausdorffification
- \+ *def* adic_completion
- \+ *def* of
- \+ *def* lift
- \+ *def* eval

Created src/linear_algebra/smodeq.lean
- \+ *theorem* top
- \+ *theorem* bot
- \+ *theorem* mono
- \+ *theorem* refl
- \+ *theorem* symm
- \+ *theorem* trans
- \+ *theorem* add
- \+ *theorem* smul
- \+ *theorem* zero
- \+ *theorem* map
- \+ *theorem* comap
- \+ *def* smodeq

Modified src/ring_theory/ideal_operations.lean
- \+ *theorem* map_smul''
- \+ *theorem* top_pow



## [2020-07-28 01:10:52](https://github.com/leanprover-community/mathlib/commit/7cd1e26)
feat(data/set/basic): range_unique ([#3582](https://github.com/leanprover-community/mathlib/pull/3582))
Add a lemma on the `range` of a function from a `unique` type.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* range_unique



## [2020-07-28 01:10:50](https://github.com/leanprover-community/mathlib/commit/23bd09a)
chore(deprecated/ring): removing uses ([#3577](https://github.com/leanprover-community/mathlib/pull/3577))
This strips out a lot of the use of `deprecated.ring`. It's now only imported by `data.polynomial.eval`, and `ring_theory.free_ring`.
#### Estimated changes
Modified src/algebra/direct_limit.lean
- \+/\- *lemma* of_pow

Modified src/algebra/group_power.lean
- \- *lemma* is_semiring_hom.map_pow

Modified src/algebra/group_with_zero.lean


Modified src/data/complex/exponential.lean


Modified src/data/equiv/ring.lean
- \- *def* of
- \- *def* of'

Modified src/data/mv_polynomial.lean
- \+/\- *lemma* is_id
- \+/\- *lemma* map_eval₂
- \+/\- *lemma* map_rename
- \+/\- *theorem* map_id
- \+/\- *def* sum_to_iter
- \+/\- *def* iter_to_sum

Modified src/data/polynomial/eval.lean
- \+/\- *lemma* map_pow

Modified src/deprecated/group.lean


Modified src/deprecated/ring.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/ring_theory/free_comm_ring.lean
- \+ *def* of'

Modified src/ring_theory/free_ring.lean
- \+/\- *lemma* lift_comp_of

Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/subring.lean




## [2020-07-28 01:10:48](https://github.com/leanprover-community/mathlib/commit/7d4d985)
chore(data/polynomial): make eval2 irreducible ([#3543](https://github.com/leanprover-community/mathlib/pull/3543))
A while back @gebner identified that [an unfortunate timeout could be avoided](https://github.com/leanprover-community/mathlib/pull/3380#issuecomment-657449148) by making `polynomial.eval2` irreducible.
This PR does that.
It's not perfect: on a few occasions I have to temporarily set it back to semireducible, because it looks like the proofs really do some heavy refling.
I'd like to make more things irreducible in the polynomial API, but not yet.
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/degree.lean


Modified src/data/polynomial/eval.lean
- \+ *lemma* eval₂_eq_sum
- \+ *lemma* eval_eq_sum
- \+ *lemma* comp_eq_sum_left

Modified src/data/polynomial/identities.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/minimal_polynomial.lean


Modified src/field_theory/separable.lean
- \+ *lemma* expand_eq_sum

Modified src/ring_theory/algebra.lean
- \+ *lemma* subring_coe_algebra_map_hom
- \+ *lemma* subring_coe_algebra_map
- \+ *lemma* subring_algebra_map_apply

Modified src/ring_theory/integral_closure.lean
- \+ *theorem* is_integral_of_is_algebra_tower
- \+/\- *theorem* integral_closure_idem

Modified src/ring_theory/polynomial/basic.lean
- \+ *theorem* map_restriction

Modified src/ring_theory/polynomial/rational_root.lean


Modified src/topology/algebra/polynomial.lean




## [2020-07-28 00:39:31](https://github.com/leanprover-community/mathlib/commit/4afb214)
chore(scripts): update nolints.txt ([#3593](https://github.com/leanprover-community/mathlib/pull/3593))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-27 20:50:19](https://github.com/leanprover-community/mathlib/commit/7556353)
feat(data/int/cast): monoid_hom.ext_int ([#3587](https://github.com/leanprover-community/mathlib/pull/3587))
#### Estimated changes
Modified src/data/int/cast.lean
- \+ *theorem* ext_int



## [2020-07-27 20:50:17](https://github.com/leanprover-community/mathlib/commit/864a22a)
chore(ci): delete doc generation steps ([#3586](https://github.com/leanprover-community/mathlib/pull/3586))
Doc generation will be run on schedule in another repo for security reasons.
#### Estimated changes
Modified .github/workflows/build.yml


Modified bors.toml


Deleted scripts/deploy_docs.sh




## [2020-07-27 20:50:15](https://github.com/leanprover-community/mathlib/commit/2ecf70f)
feat(data/finset/basic): more lemmas on finsets of subtypes ([#3575](https://github.com/leanprover-community/mathlib/pull/3575))
Add two more lemmas related to `not_mem_map_subtype_of_not_property`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* property_of_mem_map_subtype
- \+ *lemma* map_subtype_subset



## [2020-07-27 15:26:50](https://github.com/leanprover-community/mathlib/commit/3550f4f)
feat(*): remaining preliminaries for Haar measure ([#3541](https://github.com/leanprover-community/mathlib/pull/3541))
Define `has_mul (finset α)`
more convenient formulation of `is_compact.finite_compact_cover`
some lemma additions
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+/\- *lemma* preimage_mul_right_one'
- \+ *lemma* inv_subset_inv
- \+ *lemma* inv_subset
- \+ *lemma* mul_def
- \+ *lemma* mem_mul
- \+ *lemma* coe_mul
- \+ *lemma* mul_mem_mul
- \+ *lemma* mul_card_le

Modified src/data/finset/lattice.lean
- \+ *lemma* supr_insert_update
- \+ *lemma* infi_insert_update
- \+ *lemma* bUnion_insert_update
- \+ *lemma* bInter_insert_update

Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/eval.lean


Modified src/data/set/basic.lean
- \+ *lemma* preimage_congr
- \+ *lemma* surjective.preimage_subset_preimage_iff

Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measurable_mul
- \+/\- *lemma* measurable.mul
- \+ *lemma* measurable_mul_left
- \+ *lemma* measurable_mul_right

Modified src/topology/opens.lean
- \+ *lemma* coe_mk

Modified src/topology/separation.lean




## [2020-07-27 14:54:00](https://github.com/leanprover-community/mathlib/commit/adfcfe7)
feat(category_theory/concrete_category): epi_of_surjective ([#3585](https://github.com/leanprover-community/mathlib/pull/3585))
Also, change the proof of `mono_of_injective` to use the fact that the forgetful function reflects monomorphisms.
#### Estimated changes
Modified src/category_theory/concrete_category/basic.lean
- \+ *lemma* concrete_category.epi_of_surjective



## [2020-07-27 12:21:03](https://github.com/leanprover-community/mathlib/commit/aeff5fc)
chore(ci): get xz archive ([#3581](https://github.com/leanprover-community/mathlib/pull/3581))
We've been storing both .gz and .xz for a while for backward compatibility but will eventually drop .gz support.
#### Estimated changes
Modified scripts/fetch_olean_cache.sh




## [2020-07-27 12:20:59](https://github.com/leanprover-community/mathlib/commit/133067c)
feat(set_theory/cardinal_ordinal): cardinal.mk_finset_eq_mk ([#3578](https://github.com/leanprover-community/mathlib/pull/3578))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* to_finset_surjective

Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* mk_finset_eq_mk



## [2020-07-27 11:35:50](https://github.com/leanprover-community/mathlib/commit/4a5e25c)
chore(ci): remove branch update script ([#3579](https://github.com/leanprover-community/mathlib/pull/3579))
For security reasons, this will move to a scheduled action in a different repo.
#### Estimated changes
Modified .github/workflows/build.yml


Deleted scripts/update_branch.sh




## [2020-07-27 11:35:48](https://github.com/leanprover-community/mathlib/commit/8ba59d8)
feat(measure_theory/measure_space): 2 lemmas about compact sets ([#3573](https://github.com/leanprover-community/mathlib/pull/3573))
A compact set `s` has finite (resp., zero) measure if every point of
`s` has a neighborhood within `s` of finite (resp., zero) measure.
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* compl_mem_cofinite
- \+ *lemma* compl_mem_ae_iff
- \+ *lemma* finite_measure_of_nhds_within
- \+ *lemma* measure_zero_of_nhds_within



## [2020-07-27 11:35:46](https://github.com/leanprover-community/mathlib/commit/da64c7f)
chore(order/filter/basic): use `set.eq_on` in a few lemmas ([#3565](https://github.com/leanprover-community/mathlib/pull/3565))
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean


Modified src/geometry/manifold/local_invariant_properties.lean


Modified src/order/filter/basic.lean
- \+ *lemma* eventually_eq.eventually
- \+ *lemma* eventually_eq_principal
- \+ *lemma* set.eq_on.eventually_eq



## [2020-07-27 10:07:11](https://github.com/leanprover-community/mathlib/commit/8c8d6a2)
feat(topology/tactic): continuity faster and more powerful ([#3545](https://github.com/leanprover-community/mathlib/pull/3545))
Following up on the recent introduction of Reid's continuity tactic in [#2879](https://github.com/leanprover-community/mathlib/pull/2879), I've made some tweaks that make it both faster and more capable.
1. we use `apply_rules {md:=semireducible}`, taking advantage of [#3538](https://github.com/leanprover-community/mathlib/pull/3538). This makes examples like
`example : continuous (λ x : ℝ, exp ((max x (-x)) + sin (cos x))^2) := by continuity` viable.
2. in `apply_rules`, if we pull in lemmas using an attribute, we reverse the list of lemmas (on the heuristic that older lemmas are more frequently applicable than newer lemmas)
3. in `continuity`, I removed the `apply_assumption` step in the `tidy` loop, since `apply_rules` is already calling `assumption`
4. also in the `tidy` loop, I moved `intro1` above `apply_rules`.
The example in the test file
```
example {κ ι : Type}
  (K : κ → Type) [∀ k, topological_space (K k)] (I : ι → Type) [∀ i, topological_space (I i)]
  (e : κ ≃ ι) (F : Π k, homeomorph (K k) (I (e k))) :
  continuous (λ (f : Π k, K k) (i : ι), F (e.symm i) (f (e.symm i))) :=
by show_term { continuity }
```
which previously timed out now runs happily even with `-T50000`.
#### Estimated changes
Modified src/tactic/core.lean


Modified src/topology/algebra/multilinear.lean
- \+ *lemma* coe_continuous

Modified src/topology/continuous_map.lean
- \+ *lemma* coe_continuous

Modified src/topology/tactic.lean
- \+ *lemma* continuous_id'

Modified test/continuity.lean




## [2020-07-27 06:09:20](https://github.com/leanprover-community/mathlib/commit/4c0881e)
feat(measure_theory/measure_space): several lemmas about `restrict` ([#3574](https://github.com/leanprover-community/mathlib/pull/3574))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_univ_eq_zero
- \+ *lemma* restrict_apply_univ
- \+ *lemma* restrict_eq_zero
- \+ *lemma* restrict_add_restrict_compl
- \+ *lemma* restrict_compl_add_restrict
- \+ *lemma* restrict_le_self
- \+ *lemma* ae_eq_bot
- \+ *lemma* ae_restrict_eq_bot
- \+ *lemma* ae_restrict_ne_bot



## [2020-07-27 04:33:38](https://github.com/leanprover-community/mathlib/commit/d5d463e)
chore(topology/subset_properties): +2 lemmas about `is_compact` ([#3567](https://github.com/leanprover-community/mathlib/pull/3567))
Also use `variables {s t : set α}`
#### Estimated changes
Modified src/topology/subset_properties.lean
- \+ *lemma* is_compact.compl_mem_sets
- \+ *lemma* is_compact.compl_mem_sets_of_nhds_within
- \+/\- *lemma* is_compact.inter_right
- \+/\- *lemma* is_compact.inter_left
- \+/\- *lemma* compact_diff
- \+/\- *lemma* compact_of_is_closed_subset
- \+/\- *lemma* is_compact.adherence_nhdset
- \+/\- *lemma* compact_iff_ultrafilter_le_nhds
- \+/\- *lemma* is_compact.elim_finite_subcover
- \+/\- *lemma* is_compact.elim_finite_subcover_image
- \+/\- *lemma* compact_of_finite_subcover
- \+/\- *lemma* compact_iff_finite_subcover
- \+/\- *lemma* set.finite.is_compact
- \+/\- *lemma* is_compact.union
- \+/\- *lemma* cluster_point_of_compact
- \+/\- *lemma* is_compact.image_of_continuous_on
- \+/\- *lemma* is_compact.image
- \+/\- *lemma* embedding.compact_iff_compact_image
- \+/\- *lemma* compact_univ_pi
- \+/\- *theorem* compact_of_finite_subfamily_closed
- \+/\- *theorem* compact_iff_finite_subfamily_closed



## [2020-07-27 03:38:45](https://github.com/leanprover-community/mathlib/commit/8673f23)
chore(data/finsupp): move into finsupp folder ([#3566](https://github.com/leanprover-community/mathlib/pull/3566))
#### Estimated changes
Renamed src/data/finsupp.lean to src/data/finsupp/basic.lean


Created src/data/finsupp/default.lean


Modified src/data/finsupp/lattice.lean


Modified src/data/finsupp/pointwise.lean


Modified src/linear_algebra/basic.lean


Modified test/conv/apply_congr.lean




## [2020-07-27 02:48:13](https://github.com/leanprover-community/mathlib/commit/d6e399f)
chore(order/filter/basic): add `@[simp]` to `principal_empty/univ` ([#3572](https://github.com/leanprover-community/mathlib/pull/3572))
#### Estimated changes
Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* principal_univ
- \+/\- *lemma* principal_empty

Modified src/topology/subset_properties.lean




## [2020-07-27 01:32:13](https://github.com/leanprover-community/mathlib/commit/d06f62d)
feat(analysis/calculus/times_cont_diff): more thorough times_cont_diff interface ([#3551](https://github.com/leanprover-community/mathlib/pull/3551))
Add missing lemmas on smooth functions between vector spaces, that were necessary to solve the manifold exercises in Lftcm2020.
Changes the `{x : E}` argument from implicit to explicit in `lemma times_cont_diff_within_at.comp` and `lemma times_cont_diff_within_at.comp'`.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_id'
- \+ *lemma* fderiv_within_id'

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff.times_cont_diff_within_at
- \+ *lemma* times_cont_diff.comp_times_cont_diff_within_at
- \+ *lemma* times_cont_diff_within_at.add
- \+ *lemma* times_cont_diff_at.add
- \+/\- *lemma* times_cont_diff_on.add
- \+ *lemma* times_cont_diff_within_at.neg
- \+ *lemma* times_cont_diff_at.neg
- \+/\- *lemma* times_cont_diff_on.neg
- \+ *lemma* times_cont_diff_within_at.sub
- \+ *lemma* times_cont_diff_at.sub
- \+ *lemma* times_cont_diff_within_at.sum
- \+ *lemma* times_cont_diff_at.sum
- \+ *lemma* times_cont_diff_on.sum
- \+ *lemma* times_cont_diff.sum

Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/hausdorff_distance.lean




## [2020-07-27 00:02:05](https://github.com/leanprover-community/mathlib/commit/ca6cebc)
feat(data/nat/digits): add `last_digit_ne_zero` ([#3544](https://github.com/leanprover-community/mathlib/pull/3544))
The proof of `base_pow_length_digits_le` was refactored as suggested by @fpvandoorn in [#3498](https://github.com/leanprover-community/mathlib/pull/3498).
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* last_repeat_succ

Modified src/data/nat/digits.lean
- \+ *lemma* of_digits_singleton
- \+ *lemma* digits_eq_nil_iff_eq_zero
- \+ *lemma* digits_ne_nil_iff_ne_zero
- \+ *lemma* digits_last
- \+ *lemma* last_digit_ne_zero
- \+ *lemma* pow_length_le_mul_of_digits
- \+/\- *lemma* base_pow_length_digits_le'



## [2020-07-26 23:00:29](https://github.com/leanprover-community/mathlib/commit/3c4abe0)
chore(ci): remove update_nolint action ([#3570](https://github.com/leanprover-community/mathlib/pull/3570))
this action will move to another repository for security reasons
#### Estimated changes
Deleted .github/workflows/update_nolints.yml




## [2020-07-26 22:16:42](https://github.com/leanprover-community/mathlib/commit/4763feb)
chore(topology/basic): directly use `self_of_nhds` in `eq_of_nhds` ([#3569](https://github.com/leanprover-community/mathlib/pull/3569))
#### Estimated changes
Modified src/topology/basic.lean




## [2020-07-26 17:38:11](https://github.com/leanprover-community/mathlib/commit/a6d3d65)
chore(data/set/intervals): more `simp` lemmas ([#3564](https://github.com/leanprover-community/mathlib/pull/3564))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* compl_Iic
- \+/\- *lemma* compl_Ici
- \+/\- *lemma* compl_Iio
- \+/\- *lemma* compl_Ioi
- \+ *lemma* Ici_diff_Ici
- \+ *lemma* Ici_diff_Ioi
- \+ *lemma* Ioi_diff_Ioi
- \+ *lemma* Ioi_diff_Ici
- \+ *lemma* Iic_diff_Iic
- \+ *lemma* Iio_diff_Iic
- \+ *lemma* Iic_diff_Iio
- \+ *lemma* Iio_diff_Iio



## [2020-07-26 14:16:23](https://github.com/leanprover-community/mathlib/commit/692a689)
feat(data/list/chain): chain'.append_overlap ([#3559](https://github.com/leanprover-community/mathlib/pull/3559))
#### Estimated changes
Modified src/data/list/chain.lean
- \+ *lemma* chain'.append_overlap



## [2020-07-26 10:41:56](https://github.com/leanprover-community/mathlib/commit/f4106af)
feat(order/filters, topology): relation between neighborhoods of a in [a, u), [a, u] and [a,+inf) + various nhds_within lemmas ([#3516](https://github.com/leanprover-community/mathlib/pull/3516))
Content : 
- two lemmas about filters, namely `tendsto_sup` and `eventually_eq_inf_principal_iff`
- a few lemmas about `nhds_within`
- duplicate and move parts of the lemmas `tfae_mem_nhds_within_[Ioi/Iio/Ici/Iic]` that only require `order_closed_topology α` instead of `order_topology α`. This allows to turn any left/right neighborhood of `a` into its "canonical" form (i.e `Ioi`/`Iio`/`Ici`/`Iic`) with a weaker assumption than before
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* eventually_eq_inf_principal_iff
- \+ *lemma* tendsto_sup
- \+ *lemma* tendsto.sup

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tfae_mem_nhds_within_Ioi'
- \+/\- *lemma* nhds_within_Ioc_eq_nhds_within_Ioi
- \+/\- *lemma* nhds_within_Ioo_eq_nhds_within_Ioi
- \+ *lemma* continuous_within_at_Ioc_iff_Ioi
- \+ *lemma* continuous_within_at_Ioo_iff_Ioi
- \+ *lemma* tfae_mem_nhds_within_Iio'
- \+/\- *lemma* nhds_within_Ico_eq_nhds_within_Iio
- \+/\- *lemma* nhds_within_Ioo_eq_nhds_within_Iio
- \+ *lemma* continuous_within_at_Ico_iff_Iio
- \+ *lemma* continuous_within_at_Ioo_iff_Iio
- \+ *lemma* tfae_mem_nhds_within_Ici'
- \+/\- *lemma* nhds_within_Icc_eq_nhds_within_Ici
- \+/\- *lemma* nhds_within_Ico_eq_nhds_within_Ici
- \+ *lemma* continuous_within_at_Icc_iff_Ici
- \+ *lemma* continuous_within_at_Ico_iff_Ici
- \+ *lemma* tfae_mem_nhds_within_Iic'
- \+/\- *lemma* nhds_within_Icc_eq_nhds_within_Iic
- \+/\- *lemma* nhds_within_Ioc_eq_nhds_within_Iic
- \+ *lemma* continuous_within_at_Icc_iff_Iic
- \+ *lemma* continuous_within_at_Ioc_iff_Iic

Modified src/topology/continuous_on.lean
- \+ *lemma* eventually_eq_nhds_within_iff
- \+ *lemma* eventually_eq_nhds_within_of_eq_on
- \+ *lemma* set.eq_on.eventually_eq_nhds_within
- \+ *lemma* tendsto_nhds_within_congr
- \+ *lemma* eventually_nhds_with_of_forall
- \+ *lemma* tendsto_nhds_within_of_tendsto_nhds_of_eventually_within



## [2020-07-26 09:05:48](https://github.com/leanprover-community/mathlib/commit/f95e90b)
chore(order/liminf_limsup): use dot notation and `order_dual` ([#3555](https://github.com/leanprover-community/mathlib/pull/3555))
## New
* `filter.has_basis.Limsup_eq_infi_Sup`
## Rename
### Namespace `filter`
* `is_bounded_of_le` → `is_bounded_mono`;
* `is_bounded_under_of_is_bounded` → `is_bounded.is_bounded_under`;
* `is_cobounded_of_is_bounded` → `is_bounded.is_cobounded_flip`;
* `is_cobounded_of_le` → `is_cobounded.mono`;
### Top namespace
* `is_bounded_under_le_of_tendsto` → `filter.tendsto.is_bounded_under_le`;
* `is_cobounded_under_ge_of_tendsto` → `filter.tendsto.is_cobounded_under_ge`;
* `is_bounded_under_ge_of_tendsto` → `filter.tendsto.is_bounded_under_ge`;
* `is_cobounded_under_le_of_tendsto` → `filter.tendsto.is_cobounded_under_le`.
## Remove
* `filter.is_trans_le`, `filter.is_trans_ge`: we have both
  in `order/rel_classes`.
#### Estimated changes
Modified src/order/liminf_limsup.lean
- \+ *lemma* is_bounded.mono
- \+ *lemma* is_bounded.is_bounded_under
- \+ *lemma* is_bounded.is_cobounded_flip
- \+ *lemma* is_cobounded.mono
- \- *lemma* is_bounded_of_le
- \- *lemma* is_bounded_under_of_is_bounded
- \- *lemma* is_cobounded_of_is_bounded
- \- *lemma* is_cobounded_of_le
- \+ *theorem* has_basis.Limsup_eq_infi_Sup
- \+/\- *theorem* Limsup_eq_infi_Sup

Modified src/topology/algebra/ordered.lean
- \+ *lemma* filter.tendsto.is_bounded_under_le
- \+ *lemma* filter.tendsto.is_cobounded_under_ge
- \+ *lemma* filter.tendsto.is_bounded_under_ge
- \+ *lemma* filter.tendsto.is_cobounded_under_le
- \- *lemma* is_bounded_under_le_of_tendsto
- \- *lemma* is_cobounded_under_ge_of_tendsto
- \- *lemma* is_bounded_under_ge_of_tendsto
- \- *lemma* is_cobounded_under_le_of_tendsto



## [2020-07-26 09:05:46](https://github.com/leanprover-community/mathlib/commit/493a5b0)
feat(data/set/lattice): add lemmas `disjoint.union_left/right` etc ([#3554](https://github.com/leanprover-community/mathlib/pull/3554))
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *theorem* disjoint_union_left
- \+ *theorem* disjoint.union_left
- \+ *theorem* disjoint_union_right
- \+ *theorem* disjoint.union_right

Modified src/order/bounded_lattice.lean
- \+ *lemma* disjoint_sup_left
- \+ *lemma* disjoint_sup_right
- \+ *lemma* disjoint.sup_left
- \+ *lemma* disjoint.sup_right



## [2020-07-26 07:41:04](https://github.com/leanprover-community/mathlib/commit/3c1f332)
feat(tactic/to_additive): automate substructure naming ([#3553](https://github.com/leanprover-community/mathlib/pull/3553))
This is all @cipher1024's work, improving `to_additive` to correctly generate names when we're talking about structures (rather than just operations).
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/free.lean


Modified src/algebra/free_monoid.lean


Modified src/algebra/group/defs.lean


Modified src/algebra/group/hom.lean


Modified src/algebra/group/inj_surj.lean


Modified src/algebra/group/pi.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/punit_instances.lean


Modified src/data/equiv/mul_add.lean


Modified src/deprecated/group.lean


Modified src/deprecated/subgroup.lean


Modified src/deprecated/submonoid.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid/basic.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/order/filter/germ.lean


Modified src/topology/algebra/continuous_functions.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/open_subgroup.lean




## [2020-07-26 07:03:20](https://github.com/leanprover-community/mathlib/commit/d7fcd8c)
chore(analysis/normed_space): remove 2 `norm_zero` lemmas ([#3558](https://github.com/leanprover-community/mathlib/pull/3558))
We have a general `norm_zero` lemma and these lemmas are not used
before we introduce `normed_group` instances.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/normed_space/multilinear.lean
- \- *lemma* norm_zero

Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* norm_zero

Modified src/measure_theory/bochner_integration.lean




## [2020-07-26 02:39:04](https://github.com/leanprover-community/mathlib/commit/11179d5)
feat(algebra/category/Group/*): compare categorical (co)kernels/images with the usual notions ([#3443](https://github.com/leanprover-community/mathlib/pull/3443))
#### Estimated changes
Modified src/algebra/category/Group/colimits.lean
- \+ *def* cokernel_iso_quotient

Modified src/algebra/category/Group/images.lean
- \+ *def* image_iso_range

Modified src/algebra/category/Group/limits.lean
- \+ *lemma* kernel_iso_ker_hom_comp_subtype
- \+ *lemma* kernel_iso_ker_inv_comp_ι
- \+ *def* kernel_iso_ker
- \+ *def* kernel_iso_ker_over

Modified src/category_theory/limits/concrete_category.lean


Created src/category_theory/limits/shapes/concrete_category.lean
- \+ *lemma* kernel_condition_apply
- \+ *lemma* cokernel_condition_apply



## [2020-07-25 15:53:29](https://github.com/leanprover-community/mathlib/commit/8582b06)
feat(logic/basic): mark cast_eq as a `simp` lemma ([#3547](https://github.com/leanprover-community/mathlib/pull/3547))
The theorem `cast_eq` is in core and says `theorem cast_eq : ∀ {α : Sort u} (h : α = α) (a : α), cast h a = a`
#### Estimated changes
Modified src/data/fin.lean


Modified src/logic/basic.lean




## [2020-07-25 15:23:48](https://github.com/leanprover-community/mathlib/commit/3484194)
chore(geometry/manifold/real_instance): remove global fact instance ([#3549](https://github.com/leanprover-community/mathlib/pull/3549))
Remove global `fact` instance that was used to get a manifold structure on `[0, 1]`, and register only the manifold structure.
#### Estimated changes
Modified src/geometry/manifold/real_instances.lean
- \+ *lemma* fact_zero_lt_one



## [2020-07-25 10:09:45](https://github.com/leanprover-community/mathlib/commit/e90c7b9)
feat(data/num/prime): kernel-friendly decision procedure for prime ([#3525](https://github.com/leanprover-community/mathlib/pull/3525))
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+/\- *lemma* dvd_mul_sub_mul
- \+/\- *lemma* dvd_iff_dvd_of_dvd_sub
- \+ *theorem* two_dvd_bit0
- \+ *theorem* two_dvd_bit1

Modified src/data/nat/basic.lean


Modified src/data/num/lemmas.lean
- \+ *theorem* dvd_to_nat

Created src/data/num/prime.lean
- \+ *theorem* min_fac_aux_to_nat
- \+ *theorem* min_fac_to_nat
- \+ *def* min_fac_aux
- \+ *def* min_fac
- \+ *def* prime



## [2020-07-25 07:31:35](https://github.com/leanprover-community/mathlib/commit/0379d3a)
chore(*): minor import cleanup ([#3546](https://github.com/leanprover-community/mathlib/pull/3546))
#### Estimated changes
Modified src/algebra/group/pi.lean


Modified src/algebra/ring/pi.lean


Modified src/category_theory/endomorphism.lean


Modified src/category_theory/groupoid.lean


Modified src/data/equiv/encodable/lattice.lean


Modified src/data/indicator_function.lean


Modified src/data/real/nnreal.lean


Modified src/topology/algebra/monoid.lean




## [2020-07-25 06:33:04](https://github.com/leanprover-community/mathlib/commit/2a456a9)
feat(topology/*, geometry/*): missing lemmas ([#3528](https://github.com/leanprover-community/mathlib/pull/3528))
Grab bag of missing lemmas on topology and geometry that were needed for the manifold exercises in Lftcm2020.
#### Estimated changes
Modified src/geometry/manifold/mfderiv.lean
- \+ *lemma* mfderiv_within_congr
- \+ *lemma* tangent_map_within_congr
- \+ *lemma* tangent_map_id
- \+ *lemma* tangent_map_within_id

Modified src/geometry/manifold/real_instances.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* inducing.continuous_on_iff
- \+ *lemma* embedding.continuous_on_iff

Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph_mk_coe
- \+ *lemma* homeomorph_mk_coe_symm

Modified src/topology/metric_space/basic.lean
- \+ *lemma* is_closed_sphere



## [2020-07-25 06:33:02](https://github.com/leanprover-community/mathlib/commit/12a7ce3)
feat(category_theory/isomorphism): lemmas about cancelling isomorphisms ([#3436](https://github.com/leanprover-community/mathlib/pull/3436))
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+ *lemma* cancel_unit_right
- \+ *lemma* cancel_unit_inv_right
- \+ *lemma* cancel_counit_right
- \+ *lemma* cancel_counit_inv_right
- \+ *lemma* cancel_unit_right_assoc
- \+ *lemma* cancel_counit_inv_right_assoc
- \+ *lemma* cancel_unit_right_assoc'
- \+ *lemma* cancel_counit_inv_right_assoc'

Modified src/category_theory/isomorphism.lean
- \+ *lemma* cancel_iso_hom_left
- \+ *lemma* cancel_iso_inv_left
- \+ *lemma* cancel_iso_hom_right
- \+ *lemma* cancel_iso_inv_right
- \+ *lemma* cancel_iso_hom_right_assoc
- \+ *lemma* cancel_iso_inv_right_assoc

Modified src/category_theory/natural_isomorphism.lean
- \+ *lemma* cancel_nat_iso_hom_left
- \+ *lemma* cancel_nat_iso_inv_left
- \+ *lemma* cancel_nat_iso_hom_right
- \+ *lemma* cancel_nat_iso_inv_right
- \+ *lemma* cancel_nat_iso_hom_right_assoc
- \+ *lemma* cancel_nat_iso_inv_right_assoc



## [2020-07-25 05:30:35](https://github.com/leanprover-community/mathlib/commit/2d29f80)
feat(data/finsupp): lattice structure on finsupp ([#3335](https://github.com/leanprover-community/mathlib/pull/3335))
adds facts about order_isos respecting lattice operations
defines lattice structures on finsupps to N
constructs an order_iso out of finsupp.to_multiset
#### Estimated changes
Modified src/algebra/ordered_group.lean


Created src/data/finsupp/lattice.lean
- \+ *lemma* le_def
- \+ *lemma* inf_apply
- \+ *lemma* support_inf
- \+ *lemma* sup_apply
- \+ *lemma* support_sup
- \+ *lemma* of_multiset_strict_mono
- \+ *lemma* bot_eq_zero
- \+ *lemma* disjoint_iff
- \+ *lemma* order_iso_multiset_apply
- \+ *lemma* order_iso_multiset_symm_apply
- \+ *lemma* order_embedding_to_fun_apply
- \+ *lemma* monotone_to_fun
- \+ *def* order_iso_multiset
- \+ *def* order_embedding_to_fun



## [2020-07-25 04:26:19](https://github.com/leanprover-community/mathlib/commit/8d55eda)
feat(topology/tactic): `continuity` tactic ([#2879](https://github.com/leanprover-community/mathlib/pull/2879))
#### Estimated changes
Modified docs/tutorial/category_theory/calculating_colimits_in_Top.lean
- \+/\- *def* f

Modified src/analysis/analytic/basic.lean


Modified src/analysis/normed_space/banach.lean


Modified src/data/complex/exponential.lean
- \+/\- *lemma* exp_monotone

Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/topology/algebra/group.lean
- \+/\- *lemma* continuous.sub

Modified src/topology/algebra/module.lean


Modified src/topology/algebra/monoid.lean
- \+ *lemma* continuous.pow

Modified src/topology/algebra/multilinear.lean


Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* continuous.max
- \+/\- *lemma* continuous.min

Modified src/topology/algebra/polynomial.lean


Modified src/topology/compact_open.lean


Modified src/topology/constructions.lean
- \+/\- *lemma* continuous_fst
- \+/\- *lemma* continuous_snd
- \+/\- *lemma* continuous.prod_mk
- \+/\- *lemma* continuous_inl
- \+/\- *lemma* continuous_inr
- \+/\- *lemma* continuous_sum_rec
- \+/\- *lemma* continuous_subtype_val
- \+/\- *lemma* continuous_subtype_mk
- \+/\- *lemma* continuous_quot_mk
- \+/\- *lemma* continuous_quot_lift
- \+/\- *lemma* continuous_ulift_down
- \+/\- *lemma* continuous_ulift_up

Modified src/topology/continuous_map.lean
- \+/\- *def* id
- \+/\- *def* const

Modified src/topology/homeomorph.lean


Modified src/topology/order.lean
- \+/\- *lemma* continuous_bot
- \+/\- *lemma* continuous_top

Created src/topology/tactic.lean


Created test/continuity.lean




## [2020-07-24 21:19:13](https://github.com/leanprover-community/mathlib/commit/6f9da35)
feat(tactic/simps): improvements ([#3477](https://github.com/leanprover-community/mathlib/pull/3477))
Features:
* `@[simps]` will look for `has_coe_to_sort` and `has_coe_to_fun` instances, and use those instead of direct projections. This should make it way more applicable for `equiv`, `local_equiv` and all other structures that coerce to a function (and for the few structures that coerce to a type). This works out-of-the-box without special configuration.
* Use `has_mul.mul`, `has_zero.zero` and all the other "notation projections" instead of the projections directly. This should make it more useful in category theory and the algebraic hierarchy (note: the `[notation_class]` attribute still needs to be added to all notation classes not defined in `init.core`)
* Add an easy way to specify custom projections of structures (like using `⇑e.symm` instead of `e.inv_fun`). They have to be definitionally equal to the projection.
Minor changes:
* Change the syntax to specify options.
* `prod` (and `pprod`) are treated as a special case: we do not recursively apply projections of these structure. This was the most common reason that we had to write the desired projections manually. You can still override this behavior by writing out the projections manually.
* A flag to apply `simp` to the rhs of the generated lemma, so that they are in simp-normal-form.
* Added an options to add more attributes to the generated lemmas
* Added an option which definitions to unfold to determine whether a type is a function type. By default it will unfold reducible definitions and instances (but e.g. not `set α`)
* Added an option to unfold definitions in the declaration to determine whether it is a constructor. (default: none)
* Added an option to not fully-apply the terms in the generated lemmas.
Design decisions:
* For every field in a structure there is a specified "projection expression" that acts as the projection for that field. For most fields this is just the projection of the structure, but this will be automatically overridden under certain conditions, like a coercion to functions/sorts existing, or a notation typeclass existing for a certain field.
* The first time you call `simps` for a specific structure, these projection expressions are cached using an attribute for that structure, and it is assumed you want to use the same projection expressions every time.
* You can also manually specify the projection. See Note [custom simps projection].
#### Estimated changes
Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/category/Mon/colimits.lean


Modified src/category_theory/products/associator.lean
- \+/\- *def* associator
- \+/\- *def* inverse_associator

Modified src/category_theory/products/basic.lean
- \+/\- *def* sectl
- \+/\- *def* sectr
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* swap
- \+/\- *def* symmetry
- \+/\- *def* evaluation_uncurried
- \+/\- *def* prod

Modified src/meta/expr.lean


Modified src/tactic/core.lean


Modified src/tactic/simps.lean
- \+ *lemma* foo_fst
- \+ *lemma* foo_snd
- \- *lemma* {simp_lemma}.
- \- *lemma* {nm.append_suffix
- \- *lemma* refl_to_fun
- \- *lemma* refl_inv_fun
- \+ *def* foo
- \- *def* refl

Modified test/simps.lean
- \- *lemma* specify.specify1_fst_fst.
- \- *lemma* specify.specify1_foo_fst.
- \- *lemma* specify.specify1_snd_bar.
- \- *lemma* specify.specify5_snd_snd.
- \+ *def* myprod.map
- \+ *def* rfl2
- \+ *def* rfl3
- \+ *def* test_sneaky
- \+/\- *def* partially_applied_term
- \+/\- *def* very_partially_applied_term
- \+/\- *def* short_name1
- \+ *def* equiv.trans
- \+ *def* my_nat_equiv
- \+ *def* succeed_without_simplification_possible
- \+ *def* pprod_equiv_prod
- \+ *def* foo
- \+ *def* foo2
- \+ *def* voo
- \+ *def* voo2
- \+ *def* prod_Semigroup
- \+ *def* bar
- \+ *def* new_bar
- \+ *def* equiv.symm
- \+ *def* equiv.simps.inv_fun
- \+ *def* nat_set_plus
- \+ *def* nat_set_plus2
- \+ *def* nat_set_plus3
- \+ *def* equiv.symm2
- \+ *def* equiv.symm3
- \- *def* nested1
- \- *def* nested2

Modified test/tactics.lean




## [2020-07-24 18:42:44](https://github.com/leanprover-community/mathlib/commit/4d81149)
chore(ring_theory/prod): move file to algebra/ring/prod ([#3540](https://github.com/leanprover-community/mathlib/pull/3540))
#### Estimated changes
Renamed src/ring_theory/prod.lean to src/algebra/ring/prod.lean


Modified src/ring_theory/subsemiring.lean




## [2020-07-24 17:03:22](https://github.com/leanprover-community/mathlib/commit/47efcf3)
chore(algebraic_geometry/presheafed_space): use projection rather than fancy coercion ([#3507](https://github.com/leanprover-community/mathlib/pull/3507))
We'd gone to great effort when writing `PresheafedSpace` to create a coercion from morphisms of `PresheafedSpace`s to morphisms in `Top`.
It's hard to read, it's fragile.
So this PR rips out that coercion, and renames the "continuous map between base spaces" field from `f` to `base`, and uses that throughout.
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean
- \+ *lemma* id_base
- \+/\- *lemma* id_c_app
- \+ *lemma* comp_base
- \- *lemma* hom_mk_coe
- \- *lemma* f_as_coe
- \- *lemma* id_coe
- \- *lemma* id_coe_fn
- \- *lemma* comp_coe

Modified src/algebraic_geometry/stalks.lean
- \+/\- *def* stalk_map



## [2020-07-24 13:04:01](https://github.com/leanprover-community/mathlib/commit/229cf6e)
feat(data/polynomial): irreducible_of_irreducible_mod_prime ([#3539](https://github.com/leanprover-community/mathlib/pull/3539))
I was waiting on this, an exercise from Johan's tutorial at LftCM, to see if a participant would PR it. Perhaps not, so I'll contribute this now.
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *lemma* is_unit_of_is_unit_leading_coeff_of_is_unit_map
- \+ *lemma* irreducible_of_irreducible_map



## [2020-07-24 13:03:59](https://github.com/leanprover-community/mathlib/commit/579b142)
feat(field_theory/fixed): a field is normal over the fixed subfield under a group action ([#3520](https://github.com/leanprover-community/mathlib/pull/3520))
From my Galois theory repo.
#### Estimated changes
Modified src/algebra/group_action_hom.lean
- \+ *theorem* coe_polynomial
- \+ *theorem* is_invariant_subring.coe_subtype_hom
- \+ *theorem* is_invariant_subring.coe_subtype_hom'
- \+ *def* is_invariant_subring.subtype_hom

Modified src/algebra/group_ring_action.lean
- \+ *lemma* list.smul_prod
- \+ *lemma* multiset.smul_prod
- \+ *lemma* smul_prod
- \+ *lemma* coeff_smul'
- \+ *lemma* smul_C
- \+ *lemma* smul_X
- \- *lemma* polynomial.coeff_smul'
- \- *lemma* polynomial.smul_C
- \- *lemma* polynomial.smul_X
- \+ *theorem* smul_eval_smul
- \+ *theorem* eval_smul'
- \+ *theorem* smul_eval
- \+ *theorem* prod_X_sub_smul.monic
- \+ *theorem* prod_X_sub_smul.eval
- \+ *theorem* prod_X_sub_smul.smul
- \+ *theorem* prod_X_sub_smul.coeff

Modified src/algebra/module/basic.lean
- \- *theorem* smul_neg
- \- *theorem* smul_sub

Modified src/data/polynomial/div.lean
- \+ *theorem* map_dvd_map

Modified src/data/polynomial/field_division.lean
- \+ *theorem* irreducible_of_monic
- \+ *theorem* map_dvd_map'

Modified src/data/polynomial/ring_division.lean
- \+ *theorem* eq_of_monic_of_associated

Created src/field_theory/fixed.lean
- \+ *theorem* fixed_points.smul
- \+ *theorem* fixed_points.smul_polynomial
- \+ *theorem* fixed_points.coe_algebra_map
- \+ *theorem* fixed_points.minpoly.monic
- \+ *theorem* fixed_points.minpoly.eval₂
- \+ *theorem* fixed_points.is_integral
- \+ *theorem* fixed_points.minpoly.ne_one
- \+ *theorem* fixed_points.of_eval₂
- \+ *theorem* fixed_points.minpoly.irreducible_aux
- \+ *theorem* fixed_points.minpoly.irreducible
- \+ *theorem* fixed_points.minpoly.minimal_polynomial
- \+ *def* fixed_points.minpoly

Modified src/field_theory/minimal_polynomial.lean
- \+ *theorem* unique'

Created src/field_theory/normal.lean
- \+ *theorem* normal.is_integral
- \+ *theorem* normal.splits
- \+ *theorem* normal.exists_is_splitting_field
- \+ *def* normal

Modified src/group_theory/group_action.lean
- \+ *lemma* mem_fixed_by
- \+ *theorem* fixed_eq_Inter_fixed_by
- \+ *theorem* of_quotient_stabilizer_mk
- \+ *theorem* of_quotient_stabilizer_mem_orbit
- \+ *theorem* of_quotient_stabilizer_smul
- \+ *theorem* injective_of_quotient_stabilizer
- \+/\- *theorem* orbit_equiv_quotient_stabilizer_symm_apply
- \+ *theorem* smul_neg
- \+ *theorem* smul_sub
- \+/\- *def* fixed_points
- \+ *def* fixed_by
- \+ *def* of_quotient_stabilizer

Modified src/ring_theory/algebra.lean
- \+ *theorem* coe_top

Modified src/ring_theory/polynomial/basic.lean
- \+ *theorem* map_to_subring



## [2020-07-24 11:52:28](https://github.com/leanprover-community/mathlib/commit/a6ad904)
feat(tactic/apply_rules): allow apply_cfg argument ([#3538](https://github.com/leanprover-community/mathlib/pull/3538))
This allows passing an `apply_cfg` argument to `apply_rules` (and simplifies the configuration argument to `solve_by_elim`).
This is prompted by the desire to try using `apply_rules` with `md := semireducible` when working on the `continuity` tactic.
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified src/tactic/suggest.lean


Modified test/library_search/basic.lean




## [2020-07-24 11:07:23](https://github.com/leanprover-community/mathlib/commit/2d47d0c)
chore(measure_theory/indicator_function): split into 2 files deps: 3503 ([#3509](https://github.com/leanprover-community/mathlib/pull/3509))
Split `measure_theory/indicator_function` into 2 files.
This file formulated all lemmas for `measure.ae` but they hold for any filter.
#### Estimated changes
Created src/analysis/normed_space/indicator_function.lean
- \+ *lemma* norm_indicator_eq_indicator_norm
- \+ *lemma* norm_indicator_le_of_subset
- \+ *lemma* indicator_norm_le_norm_self
- \+ *lemma* norm_indicator_le_norm_self

Modified src/data/indicator_function.lean
- \+ *lemma* indicator_rel_indicator

Deleted src/measure_theory/indicator_function.lean
- \- *lemma* indicator_congr_ae
- \- *lemma* indicator_congr_of_set
- \- *lemma* indicator_union_ae
- \- *lemma* norm_indicator_le_of_subset
- \- *lemma* norm_indicator_le_norm_self
- \- *lemma* norm_indicator_eq_indicator_norm
- \- *lemma* indicator_norm_le_norm_self
- \- *lemma* indicator_le_indicator_ae
- \- *lemma* tendsto_indicator_of_monotone
- \- *lemma* tendsto_indicator_of_antimono
- \- *lemma* tendsto_indicator_bUnion_finset

Modified src/measure_theory/set_integral.lean


Modified src/order/filter/basic.lean
- \+ *lemma* eventually_set_ext
- \+ *lemma* eventually_eq.mem_iff

Created src/order/filter/indicator_function.lean
- \+ *lemma* indicator_eventually_eq
- \+ *lemma* indicator_union_eventually_eq
- \+ *lemma* indicator_eventually_le_indicator
- \+ *lemma* tendsto_indicator_of_monotone
- \+ *lemma* tendsto_indicator_of_antimono
- \+ *lemma* tendsto_indicator_bUnion_finset



## [2020-07-24 09:01:42](https://github.com/leanprover-community/mathlib/commit/6fe81bd)
chore(*): remove `plift` from some lemmas about `infi`/`supr` ([#3503](https://github.com/leanprover-community/mathlib/pull/3503))
Now `supr_eq_supr_finset` etc assume `ι` is a `Type*` and don't use `plift`. If you want
to apply it to a `Sort*`, rewrite on `equiv.plift.surjective.supr_comp` first.
## Full list of API changes:
### `data/equiv/basic`
* `equiv.ulift`: change the order of universe arguments to match `ulift`;
* add `coe_ulift`, `coe_plift`, `coe_ulift_symm`, `coe_plift_symm`;
### `data/finset/lattice`
* `supr_eq_supr_finset`, `infi_eq_infi_finset`: assume `ι` is a `Type*`, avoid `plift`;
* `Union_eq_Union_finset`, `Inter_eq_Inter_finset`: same as above;
### `data/set/basic`
* `function.surjective.range_comp`: generalize to `Sort*` for 2 of 3 arguments;
### `order/complete_lattice`
* remove `supr_congr` and `infi_congr`;
* add `function.surjective.supr_comp` and `function.surjective.infi_comp`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* coe_ulift
- \+ *lemma* coe_ulift_symm
- \+ *lemma* coe_plift
- \+ *lemma* coe_plift_symm

Modified src/data/finset/lattice.lean
- \+ *lemma* supr_eq_supr_finset'
- \+ *lemma* infi_eq_infi_finset'
- \+ *lemma* Union_eq_Union_finset'
- \+ *lemma* Inter_eq_Inter_finset'

Modified src/data/set/basic.lean
- \+/\- *lemma* surjective.range_comp

Modified src/linear_algebra/basis.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* function.surjective.supr_comp
- \+ *lemma* function.surjective.infi_comp
- \- *lemma* supr_congr
- \- *lemma* infi_congr

Modified src/order/filter/basic.lean
- \+/\- *lemma* infi_sets_eq_finite
- \+ *lemma* infi_sets_eq_finite'
- \+/\- *lemma* mem_infi_finite
- \+ *lemma* mem_infi_finite'

Modified src/set_theory/ordinal.lean




## [2020-07-24 08:19:54](https://github.com/leanprover-community/mathlib/commit/499cb9b)
refactor(data/nat/digits): refactor into sections ([#3527](https://github.com/leanprover-community/mathlib/pull/3527))
Refactor `data.nat.digits` into sections and grouping similar lemmas together.
#### Estimated changes
Modified src/data/nat/digits.lean
- \+/\- *lemma* digits_lt_base'
- \+/\- *lemma* digits_lt_base
- \+/\- *lemma* of_digits_lt_base_pow_length'
- \+/\- *lemma* of_digits_lt_base_pow_length
- \+/\- *lemma* digits_len_le_digits_len_succ
- \+/\- *lemma* le_digits_len_le
- \+/\- *lemma* base_pow_length_digits_le'
- \+/\- *lemma* base_pow_length_digits_le
- \+/\- *lemma* dvd_iff_dvd_digits_sum
- \+/\- *lemma* three_dvd_iff
- \+/\- *lemma* nine_dvd_iff



## [2020-07-24 07:44:28](https://github.com/leanprover-community/mathlib/commit/5d41ec7)
feat(ring_theory/polynomial/basic): remove unnecessary commutativity assumption ([#3535](https://github.com/leanprover-community/mathlib/pull/3535))
#### Estimated changes
Modified src/ring_theory/polynomial/basic.lean




## [2020-07-24 00:41:59](https://github.com/leanprover-community/mathlib/commit/c88f8be)
chore(scripts): update nolints.txt ([#3534](https://github.com/leanprover-community/mathlib/pull/3534))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-23 23:18:12](https://github.com/leanprover-community/mathlib/commit/bad4f97)
feat(algebra/direct_sum): Add ⨁ notation ([#3473](https://github.com/leanprover-community/mathlib/pull/3473))
This uses the unicode character "n-ary circled plus operator", which seems to be the usual symbol for this operation
#### Estimated changes
Modified src/algebra/direct_sum.lean
- \+/\- *theorem* to_group.unique
- \+/\- *def* mk
- \+/\- *def* of
- \+/\- *def* to_group

Modified src/linear_algebra/direct_sum/tensor_product.lean


Modified src/linear_algebra/direct_sum_module.lean
- \+/\- *lemma* apply_eq_component
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *theorem* to_module.unique
- \+/\- *theorem* to_module.ext
- \+/\- *def* lmk
- \+/\- *def* lof
- \+/\- *def* to_module
- \+/\- *def* component



## [2020-07-23 19:52:19](https://github.com/leanprover-community/mathlib/commit/289d17c)
chore(data/equiv/basic): avoid `λ ⟨a, b⟩` in some defs, add `simp` lemmas ([#3530](https://github.com/leanprover-community/mathlib/pull/3530))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* psigma_equiv_sigma_apply
- \+ *lemma* psigma_equiv_sigma_symm_apply
- \+ *lemma* sigma_congr_right_apply
- \+ *lemma* sigma_congr_right_symm_apply
- \+ *lemma* sigma_congr_left_apply
- \+ *lemma* sigma_equiv_prod_apply
- \+ *lemma* sigma_equiv_prod_symm_apply
- \+/\- *def* sigma_congr_left
- \+/\- *def* sigma_equiv_prod
- \+/\- *def* sigma_equiv_prod_of_equiv



## [2020-07-23 18:29:16](https://github.com/leanprover-community/mathlib/commit/2d395a9)
refactor(algebra/pi_instance): delete pi_instance file, and move instances to group/ring etc appropriately ([#3513](https://github.com/leanprover-community/mathlib/pull/3513))
#### Estimated changes
Modified src/algebra/add_torsor.lean


Created src/algebra/big_operators/pi.lean
- \+ *lemma* list_prod_apply
- \+ *lemma* multiset_prod_apply
- \+ *lemma* finset.prod_apply
- \+ *lemma* prod_mk_prod
- \+ *lemma* finset.univ_sum_single
- \+ *lemma* add_monoid_hom.functions_ext
- \+ *lemma* ring_hom.functions_ext
- \+ *lemma* fst_prod
- \+ *lemma* snd_prod

Modified src/algebra/category/CommRing/limits.lean


Modified src/algebra/category/Group/biproducts.lean


Modified src/algebra/category/Group/limits.lean


Modified src/algebra/char_p.lean


Modified src/algebra/default.lean


Modified src/algebra/field.lean


Created src/algebra/group/pi.lean
- \+ *lemma* one_apply
- \+ *lemma* mul_apply
- \+ *lemma* inv_apply
- \+ *lemma* sub_apply
- \+ *lemma* single_eq_same
- \+ *lemma* single_eq_of_ne
- \+ *lemma* monoid_hom.apply_apply
- \+ *lemma* add_monoid_hom.single_apply
- \+ *def* single
- \+ *def* monoid_hom.apply
- \+ *def* add_monoid_hom.single

Modified src/algebra/group/with_one.lean


Modified src/algebra/midpoint.lean


Renamed src/algebra/module.lean to src/algebra/module/basic.lean


Created src/algebra/module/default.lean


Created src/algebra/module/pi.lean
- \+ *lemma* smul_apply
- \+ *lemma* smul_apply'

Created src/algebra/module/prod.lean
- \+ *theorem* smul_fst
- \+ *theorem* smul_snd
- \+ *theorem* smul_mk

Deleted src/algebra/pi_instances.lean
- \- *lemma* one_apply
- \- *lemma* mul_apply
- \- *lemma* inv_apply
- \- *lemma* smul_apply
- \- *lemma* smul_apply'
- \- *lemma* sub_apply
- \- *lemma* list_prod_apply
- \- *lemma* multiset_prod_apply
- \- *lemma* finset_prod_apply
- \- *lemma* single_eq_same
- \- *lemma* single_eq_of_ne
- \- *lemma* monoid_hom.apply_apply
- \- *lemma* ring_hom.apply_apply
- \- *lemma* finset.prod_apply
- \- *lemma* finset.univ_sum_single
- \- *lemma* add_monoid_hom.single_apply
- \- *lemma* add_monoid_hom.functions_ext
- \- *lemma* ring_hom.functions_ext
- \- *lemma* fst.is_monoid_hom
- \- *lemma* snd.is_monoid_hom
- \- *lemma* fst.is_group_hom
- \- *lemma* snd.is_group_hom
- \- *lemma* fst_prod
- \- *lemma* snd_prod
- \- *lemma* inl_injective
- \- *lemma* inr_injective
- \- *lemma* inl_eq_inl
- \- *lemma* inr_eq_inr
- \- *lemma* inl_eq_inr
- \- *lemma* inr_eq_inl
- \- *lemma* fst_inl
- \- *lemma* snd_inl
- \- *lemma* fst_inr
- \- *lemma* snd_inr
- \- *lemma* prod_mk_prod
- \- *theorem* smul_fst
- \- *theorem* smul_snd
- \- *theorem* smul_mk
- \- *def* single
- \- *def* monoid_hom.apply
- \- *def* ring_hom.apply
- \- *def* add_monoid_hom.single
- \- *def* inl
- \- *def* inr

Modified src/algebra/pointwise.lean


Modified src/algebra/punit_instances.lean


Renamed src/algebra/ring.lean to src/algebra/ring/basic.lean


Created src/algebra/ring/default.lean


Created src/algebra/ring/pi.lean
- \+ *lemma* ring_hom.apply_apply
- \+ *def* ring_hom.apply

Modified src/analysis/calculus/tangent_cone.lean


Modified src/data/dfinsupp.lean


Modified src/data/finsupp.lean


Modified src/data/holor.lean


Modified src/data/indicator_function.lean


Modified src/data/matrix/basic.lean


Modified src/deprecated/group.lean


Modified src/deprecated/ring.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/linear_algebra/basic.lean
- \+ *theorem* inl_injective
- \+ *theorem* inr_injective
- \+/\- *def* inl
- \+/\- *def* inr

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/linear_algebra/sesquilinear_form.lean


Modified src/order/filter/filter_product.lean


Modified src/order/filter/germ.lean


Modified src/order/pilex.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/prod.lean


Modified src/topology/algebra/monoid.lean


Modified test/lint.lean


Modified test/pi_simp.lean




## [2020-07-23 14:56:16](https://github.com/leanprover-community/mathlib/commit/ed33a99)
chore(measure_theory/l1_space): make `measure` argument of `integrable` optional ([#3508](https://github.com/leanprover-community/mathlib/pull/3508))
Other changes:
* a few trivial lemmas;
* fix notation for `∀ᵐ`: now Lean can use it for printing, not only
  for parsing.
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* integral_zero_meas

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* integrable.mono
- \+/\- *lemma* integrable.congr
- \+/\- *lemma* integrable_congr
- \+/\- *def* integrable

Modified src/measure_theory/measure_space.lean




## [2020-07-23 13:44:07](https://github.com/leanprover-community/mathlib/commit/396a66a)
chore(order/filter/*): use `[nonempty _]` instead of `(_ : nonempty _)` ([#3526](https://github.com/leanprover-community/mathlib/pull/3526))
In most cases Lean can find an instance automatically.
#### Estimated changes
Modified src/order/basic.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* at_top_basis

Modified src/order/filter/bases.lean
- \+/\- *lemma* has_basis_generate
- \+/\- *lemma* has_basis_infi_principal

Modified src/order/filter/basic.lean
- \+/\- *lemma* infi_sets_eq
- \+/\- *lemma* mem_infi
- \+/\- *lemma* infi_ne_bot_of_directed'
- \+/\- *lemma* map_infi_eq

Modified src/order/filter/lift.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/uniform_space/absolute_value.lean


Modified src/topology/uniform_space/basic.lean




## [2020-07-23 11:08:28](https://github.com/leanprover-community/mathlib/commit/b9beca0)
chore(set_theory/ordinal): split into multiple files ([#3517](https://github.com/leanprover-community/mathlib/pull/3517))
Split the file `ordinal.lean` into three files, and add docstrings for all definitions and file-level docstrings. This is just shuffling things around: no new content, no erased content.
#### Estimated changes
Modified src/data/real/cardinality.lean


Modified src/linear_algebra/dimension.lean


Modified src/set_theory/cardinal.lean


Created src/set_theory/cardinal_ordinal.lean
- \+ *lemma* mul_le_max_of_omega_le_left
- \+ *lemma* mul_eq_max_of_omega_le_left
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
- \+ *lemma* add_one_eq
- \+ *lemma* power_self_eq
- \+ *lemma* power_nat_le
- \+ *lemma* powerlt_omega
- \+ *lemma* powerlt_omega_le
- \+ *lemma* mk_bounded_set_le_of_omega_le
- \+ *lemma* mk_bounded_set_le
- \+ *lemma* mk_bounded_subset_le
- \+ *lemma* mk_compl_of_omega_le
- \+ *lemma* mk_compl_finset_of_omega_le
- \+ *lemma* mk_compl_eq_mk_compl_infinite
- \+ *lemma* mk_compl_eq_mk_compl_finite_lift
- \+ *lemma* mk_compl_eq_mk_compl_finite
- \+ *lemma* mk_compl_eq_mk_compl_finite_same
- \+ *lemma* bit0_ne_zero
- \+ *lemma* bit1_ne_zero
- \+ *lemma* zero_lt_bit0
- \+ *lemma* zero_lt_bit1
- \+ *lemma* one_le_bit0
- \+ *lemma* one_le_bit1
- \+ *lemma* bit0_le_bit0
- \+ *lemma* bit0_le_bit1
- \+ *lemma* bit1_le_bit1
- \+ *lemma* bit1_le_bit0
- \+ *lemma* bit0_lt_bit0
- \+ *lemma* bit1_lt_bit0
- \+ *lemma* bit1_lt_bit1
- \+ *lemma* bit0_lt_bit1
- \+ *lemma* one_lt_two
- \+ *lemma* one_lt_bit0
- \+ *lemma* one_lt_bit1
- \+ *lemma* one_le_one
- \+ *theorem* ord_is_limit
- \+ *theorem* aleph_idx.initial_seg_coe
- \+ *theorem* aleph_idx_lt
- \+ *theorem* aleph_idx_le
- \+ *theorem* aleph_idx.init
- \+ *theorem* aleph_idx.order_iso_coe
- \+ *theorem* type_cardinal
- \+ *theorem* mk_cardinal
- \+ *theorem* aleph'.order_iso_coe
- \+ *theorem* aleph'_lt
- \+ *theorem* aleph'_le
- \+ *theorem* aleph'_aleph_idx
- \+ *theorem* aleph_idx_aleph'
- \+ *theorem* aleph'_zero
- \+ *theorem* aleph'_succ
- \+ *theorem* aleph'_nat
- \+ *theorem* aleph'_le_of_limit
- \+ *theorem* aleph'_omega
- \+ *theorem* aleph_lt
- \+ *theorem* aleph_le
- \+ *theorem* aleph_succ
- \+ *theorem* aleph_zero
- \+ *theorem* omega_le_aleph'
- \+ *theorem* omega_le_aleph
- \+ *theorem* ord_aleph_is_limit
- \+ *theorem* exists_aleph
- \+ *theorem* aleph'_is_normal
- \+ *theorem* aleph_is_normal
- \+ *theorem* mul_eq_self
- \+ *theorem* mul_eq_max
- \+ *theorem* mul_lt_of_lt
- \+ *theorem* add_eq_self
- \+ *theorem* add_eq_max
- \+ *theorem* add_lt_of_lt
- \+ *theorem* pow_le
- \+ *theorem* mk_list_eq_mk
- \+ *theorem* extend_function
- \+ *theorem* extend_function_finite
- \+ *theorem* extend_function_of_lt
- \+ *theorem* bit0_eq_self
- \+ *theorem* bit0_lt_omega
- \+ *theorem* omega_le_bit0
- \+ *theorem* bit1_eq_self_iff
- \+ *theorem* bit1_lt_omega
- \+ *theorem* omega_le_bit1
- \+ *def* aleph_idx.initial_seg
- \+ *def* aleph_idx
- \+ *def* aleph_idx.order_iso
- \+ *def* aleph'.order_iso
- \+ *def* aleph'
- \+ *def* aleph'_equiv
- \+ *def* aleph

Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal.lean
- \- *lemma* has_succ_of_is_limit
- \- *lemma* type_subrel_lt
- \- *lemma* mk_initial_seg
- \- *lemma* div_def
- \- *lemma* sup_succ
- \- *lemma* unbounded_range_of_sup_ge
- \- *lemma* mul_le_max_of_omega_le_left
- \- *lemma* mul_eq_max_of_omega_le_left
- \- *lemma* mul_eq_left
- \- *lemma* mul_eq_right
- \- *lemma* le_mul_left
- \- *lemma* le_mul_right
- \- *lemma* mul_eq_left_iff
- \- *lemma* eq_of_add_eq_of_omega_le
- \- *lemma* add_eq_left
- \- *lemma* add_eq_right
- \- *lemma* add_eq_left_iff
- \- *lemma* add_eq_right_iff
- \- *lemma* add_one_eq
- \- *lemma* power_self_eq
- \- *lemma* power_nat_le
- \- *lemma* powerlt_omega
- \- *lemma* powerlt_omega_le
- \- *lemma* mk_bounded_set_le_of_omega_le
- \- *lemma* mk_bounded_set_le
- \- *lemma* mk_bounded_subset_le
- \- *lemma* mk_compl_of_omega_le
- \- *lemma* mk_compl_finset_of_omega_le
- \- *lemma* mk_compl_eq_mk_compl_infinite
- \- *lemma* mk_compl_eq_mk_compl_finite_lift
- \- *lemma* mk_compl_eq_mk_compl_finite
- \- *lemma* mk_compl_eq_mk_compl_finite_same
- \- *lemma* bit0_ne_zero
- \- *lemma* bit1_ne_zero
- \- *lemma* zero_lt_bit0
- \- *lemma* zero_lt_bit1
- \- *lemma* one_le_bit0
- \- *lemma* one_le_bit1
- \- *lemma* bit0_le_bit0
- \- *lemma* bit0_le_bit1
- \- *lemma* bit1_le_bit1
- \- *lemma* bit1_le_bit0
- \- *lemma* bit0_lt_bit0
- \- *lemma* bit1_lt_bit0
- \- *lemma* bit1_lt_bit1
- \- *lemma* bit0_lt_bit1
- \- *lemma* one_lt_two
- \- *lemma* one_lt_bit0
- \- *lemma* one_lt_bit1
- \- *lemma* one_le_one
- \+/\- *theorem* typein.principal_seg_coe
- \+/\- *theorem* lift.initial_seg_coe
- \+/\- *theorem* card_add
- \+/\- *theorem* card_nat
- \+/\- *theorem* type_add
- \+/\- *theorem* succ_eq_add_one
- \+/\- *theorem* add_le_add_left
- \+/\- *theorem* le_add_right
- \+/\- *theorem* lt_succ_self
- \+/\- *theorem* succ_le
- \+/\- *theorem* univ_id
- \+/\- *theorem* lift_univ
- \+/\- *theorem* univ_umax
- \+/\- *theorem* lift.principal_seg_coe
- \+/\- *theorem* lift.principal_seg_top
- \+/\- *theorem* lift.principal_seg_top'
- \+/\- *theorem* min_eq
- \+/\- *theorem* min_le
- \+/\- *theorem* le_min
- \- *theorem* succ_pos
- \- *theorem* succ_ne_zero
- \- *theorem* card_succ
- \- *theorem* nat_cast_succ
- \- *theorem* add_succ
- \- *theorem* succ_zero
- \- *theorem* one_le_iff_pos
- \- *theorem* one_le_iff_ne_zero
- \- *theorem* add_le_add_iff_left
- \- *theorem* add_left_cancel
- \- *theorem* lift_add
- \- *theorem* lift_succ
- \- *theorem* lt_succ
- \- *theorem* add_lt_add_iff_left
- \- *theorem* lt_of_add_lt_add_right
- \- *theorem* succ_lt_succ
- \- *theorem* succ_le_succ
- \- *theorem* succ_inj
- \- *theorem* add_le_add_iff_right
- \- *theorem* add_right_cancel
- \- *theorem* card_eq_zero
- \- *theorem* type_ne_zero_iff_nonempty
- \- *theorem* type_eq_zero_iff_empty
- \- *theorem* zero_lt_one
- \- *theorem* pred_succ
- \- *theorem* pred_le_self
- \- *theorem* pred_eq_iff_not_succ
- \- *theorem* pred_lt_iff_is_succ
- \- *theorem* succ_pred_iff_is_succ
- \- *theorem* succ_lt_of_not_succ
- \- *theorem* lt_pred
- \- *theorem* pred_le
- \- *theorem* lift_is_succ
- \- *theorem* lift_pred
- \- *theorem* not_zero_is_limit
- \- *theorem* not_succ_is_limit
- \- *theorem* not_succ_of_is_limit
- \- *theorem* succ_lt_of_is_limit
- \- *theorem* le_succ_of_is_limit
- \- *theorem* limit_le
- \- *theorem* lt_limit
- \- *theorem* lift_is_limit
- \- *theorem* is_limit.pos
- \- *theorem* is_limit.one_lt
- \- *theorem* is_limit.nat_lt
- \- *theorem* zero_or_succ_or_limit
- \- *theorem* limit_rec_on_zero
- \- *theorem* limit_rec_on_succ
- \- *theorem* limit_rec_on_limit
- \- *theorem* is_normal.limit_le
- \- *theorem* is_normal.limit_lt
- \- *theorem* is_normal.lt_iff
- \- *theorem* is_normal.le_iff
- \- *theorem* is_normal.inj
- \- *theorem* is_normal.le_self
- \- *theorem* is_normal.le_set
- \- *theorem* is_normal.le_set'
- \- *theorem* is_normal.refl
- \- *theorem* is_normal.trans
- \- *theorem* is_normal.is_limit
- \- *theorem* add_le_of_limit
- \- *theorem* add_is_normal
- \- *theorem* add_is_limit
- \- *theorem* le_add_sub
- \- *theorem* sub_le
- \- *theorem* lt_sub
- \- *theorem* add_sub_cancel
- \- *theorem* sub_eq_of_add_eq
- \- *theorem* sub_le_self
- \- *theorem* add_sub_cancel_of_le
- \- *theorem* sub_zero
- \- *theorem* zero_sub
- \- *theorem* sub_self
- \- *theorem* sub_eq_zero_iff_le
- \- *theorem* sub_sub
- \- *theorem* add_sub_add_cancel
- \- *theorem* sub_is_limit
- \- *theorem* one_add_omega
- \- *theorem* one_add_of_omega_le
- \- *theorem* type_mul
- \- *theorem* lift_mul
- \- *theorem* card_mul
- \- *theorem* mul_zero
- \- *theorem* zero_mul
- \- *theorem* mul_add
- \- *theorem* mul_add_one
- \- *theorem* mul_succ
- \- *theorem* mul_le_mul_left
- \- *theorem* mul_le_mul_right
- \- *theorem* mul_le_mul
- \- *theorem* mul_le_of_limit
- \- *theorem* mul_is_normal
- \- *theorem* lt_mul_of_limit
- \- *theorem* mul_lt_mul_iff_left
- \- *theorem* mul_le_mul_iff_left
- \- *theorem* mul_lt_mul_of_pos_left
- \- *theorem* mul_pos
- \- *theorem* mul_ne_zero
- \- *theorem* le_of_mul_le_mul_left
- \- *theorem* mul_right_inj
- \- *theorem* mul_is_limit
- \- *theorem* mul_is_limit_left
- \- *theorem* div_zero
- \- *theorem* lt_mul_succ_div
- \- *theorem* lt_mul_div_add
- \- *theorem* div_le
- \- *theorem* lt_div
- \- *theorem* le_div
- \- *theorem* div_lt
- \- *theorem* div_le_of_le_mul
- \- *theorem* mul_lt_of_lt_div
- \- *theorem* zero_div
- \- *theorem* mul_div_le
- \- *theorem* mul_add_div
- \- *theorem* div_eq_zero_of_lt
- \- *theorem* mul_div_cancel
- \- *theorem* div_one
- \- *theorem* div_self
- \- *theorem* mul_sub
- \- *theorem* is_limit_add_iff
- \- *theorem* dvd_def
- \- *theorem* dvd_mul
- \- *theorem* dvd_trans
- \- *theorem* dvd_mul_of_dvd
- \- *theorem* dvd_add_iff
- \- *theorem* dvd_add
- \- *theorem* dvd_zero
- \- *theorem* zero_dvd
- \- *theorem* one_dvd
- \- *theorem* div_mul_cancel
- \- *theorem* le_of_dvd
- \- *theorem* dvd_antisymm
- \- *theorem* mod_def
- \- *theorem* mod_zero
- \- *theorem* mod_eq_of_lt
- \- *theorem* zero_mod
- \- *theorem* div_add_mod
- \- *theorem* mod_lt
- \- *theorem* mod_self
- \- *theorem* mod_one
- \- *theorem* le_sup
- \- *theorem* sup_le
- \- *theorem* lt_sup
- \- *theorem* is_normal.sup
- \- *theorem* sup_ord
- \- *theorem* bsup_le
- \- *theorem* bsup_type
- \- *theorem* le_bsup
- \- *theorem* lt_bsup
- \- *theorem* bsup_id
- \- *theorem* is_normal.bsup
- \- *theorem* is_normal.bsup_eq
- \- *theorem* zero_power'
- \- *theorem* zero_power
- \- *theorem* power_zero
- \- *theorem* power_succ
- \- *theorem* power_limit
- \- *theorem* power_le_of_limit
- \- *theorem* lt_power_of_limit
- \- *theorem* power_one
- \- *theorem* one_power
- \- *theorem* power_pos
- \- *theorem* power_ne_zero
- \- *theorem* power_is_normal
- \- *theorem* power_lt_power_iff_right
- \- *theorem* power_le_power_iff_right
- \- *theorem* power_right_inj
- \- *theorem* power_is_limit
- \- *theorem* power_is_limit_left
- \- *theorem* power_le_power_right
- \- *theorem* power_le_power_left
- \- *theorem* le_power_self
- \- *theorem* power_lt_power_left_of_succ
- \- *theorem* power_add
- \- *theorem* power_dvd_power
- \- *theorem* power_dvd_power_iff
- \- *theorem* power_mul
- \- *theorem* log_not_one_lt
- \- *theorem* log_def
- \- *theorem* log_zero
- \- *theorem* succ_log_def
- \- *theorem* lt_power_succ_log
- \- *theorem* power_log_le
- \- *theorem* le_log
- \- *theorem* log_lt
- \- *theorem* log_le_log
- \- *theorem* log_le_self
- \- *theorem* nat_cast_mul
- \- *theorem* nat_cast_power
- \- *theorem* nat_cast_le
- \- *theorem* nat_cast_lt
- \- *theorem* nat_cast_inj
- \- *theorem* nat_cast_eq_zero
- \- *theorem* nat_cast_ne_zero
- \- *theorem* nat_cast_pos
- \- *theorem* nat_cast_sub
- \- *theorem* nat_cast_div
- \- *theorem* nat_cast_mod
- \- *theorem* nat_le_card
- \- *theorem* nat_lt_card
- \- *theorem* card_lt_nat
- \- *theorem* card_le_nat
- \- *theorem* card_eq_nat
- \- *theorem* type_fin
- \- *theorem* lift_nat_cast
- \- *theorem* lift_type_fin
- \- *theorem* fintype_card
- \- *theorem* ord_omega
- \- *theorem* add_one_of_omega_le
- \- *theorem* lt_omega
- \- *theorem* nat_lt_omega
- \- *theorem* omega_pos
- \- *theorem* omega_ne_zero
- \- *theorem* one_lt_omega
- \- *theorem* omega_is_limit
- \- *theorem* omega_le
- \- *theorem* nat_lt_limit
- \- *theorem* omega_le_of_is_limit
- \- *theorem* add_omega
- \- *theorem* add_lt_omega
- \- *theorem* mul_lt_omega
- \- *theorem* is_limit_iff_omega_dvd
- \- *theorem* power_lt_omega
- \- *theorem* add_omega_power
- \- *theorem* add_lt_omega_power
- \- *theorem* add_absorp
- \- *theorem* add_absorp_iff
- \- *theorem* add_mul_limit_aux
- \- *theorem* add_mul_succ
- \- *theorem* add_mul_limit
- \- *theorem* mul_omega
- \- *theorem* mul_lt_omega_power
- \- *theorem* mul_omega_dvd
- \- *theorem* mul_omega_power_power
- \- *theorem* power_omega
- \- *theorem* CNF_aux
- \- *theorem* CNF_rec_zero
- \- *theorem* CNF_rec_ne_zero
- \- *theorem* zero_CNF
- \- *theorem* CNF_zero
- \- *theorem* CNF_ne_zero
- \- *theorem* one_CNF
- \- *theorem* CNF_foldr
- \- *theorem* CNF_pairwise_aux
- \- *theorem* CNF_pairwise
- \- *theorem* CNF_fst_le_log
- \- *theorem* CNF_fst_le
- \- *theorem* CNF_snd_lt
- \- *theorem* CNF_sorted
- \- *theorem* iterate_le_nfp
- \- *theorem* le_nfp_self
- \- *theorem* is_normal.lt_nfp
- \- *theorem* is_normal.nfp_le
- \- *theorem* is_normal.nfp_le_fp
- \- *theorem* is_normal.nfp_fp
- \- *theorem* is_normal.le_nfp
- \- *theorem* nfp_eq_self
- \- *theorem* deriv_zero
- \- *theorem* deriv_succ
- \- *theorem* deriv_limit
- \- *theorem* deriv_is_normal
- \- *theorem* is_normal.deriv_fp
- \- *theorem* is_normal.fp_iff_deriv
- \- *theorem* ord_is_limit
- \- *theorem* aleph_idx.initial_seg_coe
- \- *theorem* aleph_idx_lt
- \- *theorem* aleph_idx_le
- \- *theorem* aleph_idx.init
- \- *theorem* aleph_idx.order_iso_coe
- \- *theorem* type_cardinal
- \- *theorem* mk_cardinal
- \- *theorem* aleph'.order_iso_coe
- \- *theorem* aleph'_lt
- \- *theorem* aleph'_le
- \- *theorem* aleph'_aleph_idx
- \- *theorem* aleph_idx_aleph'
- \- *theorem* aleph'_zero
- \- *theorem* aleph'_succ
- \- *theorem* aleph'_nat
- \- *theorem* aleph'_le_of_limit
- \- *theorem* aleph'_omega
- \- *theorem* aleph_lt
- \- *theorem* aleph_le
- \- *theorem* aleph_succ
- \- *theorem* aleph_zero
- \- *theorem* omega_le_aleph'
- \- *theorem* omega_le_aleph
- \- *theorem* ord_aleph_is_limit
- \- *theorem* exists_aleph
- \- *theorem* aleph'_is_normal
- \- *theorem* aleph_is_normal
- \- *theorem* mul_eq_self
- \- *theorem* mul_eq_max
- \- *theorem* mul_lt_of_lt
- \- *theorem* add_eq_self
- \- *theorem* add_eq_max
- \- *theorem* add_lt_of_lt
- \- *theorem* pow_le
- \- *theorem* mk_list_eq_mk
- \- *theorem* extend_function
- \- *theorem* extend_function_finite
- \- *theorem* extend_function_of_lt
- \- *theorem* bit0_eq_self
- \- *theorem* bit0_lt_omega
- \- *theorem* omega_le_bit0
- \- *theorem* bit1_eq_self_iff
- \- *theorem* bit1_lt_omega
- \- *theorem* omega_le_bit1
- \+/\- *def* typein.principal_seg
- \+/\- *def* lift.initial_seg
- \+/\- *def* succ
- \+/\- *def* univ
- \+/\- *def* lift.principal_seg
- \+/\- *def* min
- \- *def* pred
- \- *def* is_limit
- \- *def* limit_rec_on
- \- *def* is_normal
- \- *def* sub
- \- *def* sup
- \- *def* bsup
- \- *def* power
- \- *def* log
- \- *def* CNF
- \- *def* nfp
- \- *def* deriv
- \- *def* aleph_idx.initial_seg
- \- *def* aleph_idx
- \- *def* aleph_idx.order_iso
- \- *def* aleph'.order_iso
- \- *def* aleph'
- \- *def* aleph'_equiv
- \- *def* aleph

Created src/set_theory/ordinal_arithmetic.lean
- \+ *lemma* has_succ_of_is_limit
- \+ *lemma* type_subrel_lt
- \+ *lemma* mk_initial_seg
- \+ *lemma* div_def
- \+ *lemma* sup_succ
- \+ *lemma* unbounded_range_of_sup_ge
- \+ *theorem* lift_add
- \+ *theorem* lift_succ
- \+ *theorem* add_le_add_iff_left
- \+ *theorem* add_succ
- \+ *theorem* succ_zero
- \+ *theorem* one_le_iff_pos
- \+ *theorem* one_le_iff_ne_zero
- \+ *theorem* succ_pos
- \+ *theorem* succ_ne_zero
- \+ *theorem* card_succ
- \+ *theorem* nat_cast_succ
- \+ *theorem* add_left_cancel
- \+ *theorem* lt_succ
- \+ *theorem* add_lt_add_iff_left
- \+ *theorem* lt_of_add_lt_add_right
- \+ *theorem* succ_lt_succ
- \+ *theorem* succ_le_succ
- \+ *theorem* succ_inj
- \+ *theorem* add_le_add_iff_right
- \+ *theorem* add_right_cancel
- \+ *theorem* card_eq_zero
- \+ *theorem* type_ne_zero_iff_nonempty
- \+ *theorem* type_eq_zero_iff_empty
- \+ *theorem* zero_lt_one
- \+ *theorem* pred_succ
- \+ *theorem* pred_le_self
- \+ *theorem* pred_eq_iff_not_succ
- \+ *theorem* pred_lt_iff_is_succ
- \+ *theorem* succ_pred_iff_is_succ
- \+ *theorem* succ_lt_of_not_succ
- \+ *theorem* lt_pred
- \+ *theorem* pred_le
- \+ *theorem* lift_is_succ
- \+ *theorem* lift_pred
- \+ *theorem* not_zero_is_limit
- \+ *theorem* not_succ_is_limit
- \+ *theorem* not_succ_of_is_limit
- \+ *theorem* succ_lt_of_is_limit
- \+ *theorem* le_succ_of_is_limit
- \+ *theorem* limit_le
- \+ *theorem* lt_limit
- \+ *theorem* lift_is_limit
- \+ *theorem* is_limit.pos
- \+ *theorem* is_limit.one_lt
- \+ *theorem* is_limit.nat_lt
- \+ *theorem* zero_or_succ_or_limit
- \+ *theorem* limit_rec_on_zero
- \+ *theorem* limit_rec_on_succ
- \+ *theorem* limit_rec_on_limit
- \+ *theorem* is_normal.limit_le
- \+ *theorem* is_normal.limit_lt
- \+ *theorem* is_normal.lt_iff
- \+ *theorem* is_normal.le_iff
- \+ *theorem* is_normal.inj
- \+ *theorem* is_normal.le_self
- \+ *theorem* is_normal.le_set
- \+ *theorem* is_normal.le_set'
- \+ *theorem* is_normal.refl
- \+ *theorem* is_normal.trans
- \+ *theorem* is_normal.is_limit
- \+ *theorem* add_le_of_limit
- \+ *theorem* add_is_normal
- \+ *theorem* add_is_limit
- \+ *theorem* le_add_sub
- \+ *theorem* sub_le
- \+ *theorem* lt_sub
- \+ *theorem* add_sub_cancel
- \+ *theorem* sub_eq_of_add_eq
- \+ *theorem* sub_le_self
- \+ *theorem* add_sub_cancel_of_le
- \+ *theorem* sub_zero
- \+ *theorem* zero_sub
- \+ *theorem* sub_self
- \+ *theorem* sub_eq_zero_iff_le
- \+ *theorem* sub_sub
- \+ *theorem* add_sub_add_cancel
- \+ *theorem* sub_is_limit
- \+ *theorem* one_add_omega
- \+ *theorem* one_add_of_omega_le
- \+ *theorem* type_mul
- \+ *theorem* lift_mul
- \+ *theorem* card_mul
- \+ *theorem* mul_zero
- \+ *theorem* zero_mul
- \+ *theorem* mul_add
- \+ *theorem* mul_add_one
- \+ *theorem* mul_succ
- \+ *theorem* mul_le_mul_left
- \+ *theorem* mul_le_mul_right
- \+ *theorem* mul_le_mul
- \+ *theorem* mul_le_of_limit
- \+ *theorem* mul_is_normal
- \+ *theorem* lt_mul_of_limit
- \+ *theorem* mul_lt_mul_iff_left
- \+ *theorem* mul_le_mul_iff_left
- \+ *theorem* mul_lt_mul_of_pos_left
- \+ *theorem* mul_pos
- \+ *theorem* mul_ne_zero
- \+ *theorem* le_of_mul_le_mul_left
- \+ *theorem* mul_right_inj
- \+ *theorem* mul_is_limit
- \+ *theorem* mul_is_limit_left
- \+ *theorem* div_zero
- \+ *theorem* lt_mul_succ_div
- \+ *theorem* lt_mul_div_add
- \+ *theorem* div_le
- \+ *theorem* lt_div
- \+ *theorem* le_div
- \+ *theorem* div_lt
- \+ *theorem* div_le_of_le_mul
- \+ *theorem* mul_lt_of_lt_div
- \+ *theorem* zero_div
- \+ *theorem* mul_div_le
- \+ *theorem* mul_add_div
- \+ *theorem* div_eq_zero_of_lt
- \+ *theorem* mul_div_cancel
- \+ *theorem* div_one
- \+ *theorem* div_self
- \+ *theorem* mul_sub
- \+ *theorem* is_limit_add_iff
- \+ *theorem* dvd_def
- \+ *theorem* dvd_mul
- \+ *theorem* dvd_trans
- \+ *theorem* dvd_mul_of_dvd
- \+ *theorem* dvd_add_iff
- \+ *theorem* dvd_add
- \+ *theorem* dvd_zero
- \+ *theorem* zero_dvd
- \+ *theorem* one_dvd
- \+ *theorem* div_mul_cancel
- \+ *theorem* le_of_dvd
- \+ *theorem* dvd_antisymm
- \+ *theorem* mod_def
- \+ *theorem* mod_zero
- \+ *theorem* mod_eq_of_lt
- \+ *theorem* zero_mod
- \+ *theorem* div_add_mod
- \+ *theorem* mod_lt
- \+ *theorem* mod_self
- \+ *theorem* mod_one
- \+ *theorem* le_sup
- \+ *theorem* sup_le
- \+ *theorem* lt_sup
- \+ *theorem* is_normal.sup
- \+ *theorem* sup_ord
- \+ *theorem* bsup_le
- \+ *theorem* bsup_type
- \+ *theorem* le_bsup
- \+ *theorem* lt_bsup
- \+ *theorem* bsup_id
- \+ *theorem* is_normal.bsup
- \+ *theorem* is_normal.bsup_eq
- \+ *theorem* zero_power'
- \+ *theorem* zero_power
- \+ *theorem* power_zero
- \+ *theorem* power_succ
- \+ *theorem* power_limit
- \+ *theorem* power_le_of_limit
- \+ *theorem* lt_power_of_limit
- \+ *theorem* power_one
- \+ *theorem* one_power
- \+ *theorem* power_pos
- \+ *theorem* power_ne_zero
- \+ *theorem* power_is_normal
- \+ *theorem* power_lt_power_iff_right
- \+ *theorem* power_le_power_iff_right
- \+ *theorem* power_right_inj
- \+ *theorem* power_is_limit
- \+ *theorem* power_is_limit_left
- \+ *theorem* power_le_power_right
- \+ *theorem* power_le_power_left
- \+ *theorem* le_power_self
- \+ *theorem* power_lt_power_left_of_succ
- \+ *theorem* power_add
- \+ *theorem* power_dvd_power
- \+ *theorem* power_dvd_power_iff
- \+ *theorem* power_mul
- \+ *theorem* log_not_one_lt
- \+ *theorem* log_def
- \+ *theorem* log_zero
- \+ *theorem* succ_log_def
- \+ *theorem* lt_power_succ_log
- \+ *theorem* power_log_le
- \+ *theorem* le_log
- \+ *theorem* log_lt
- \+ *theorem* log_le_log
- \+ *theorem* log_le_self
- \+ *theorem* CNF_aux
- \+ *theorem* CNF_rec_zero
- \+ *theorem* CNF_rec_ne_zero
- \+ *theorem* zero_CNF
- \+ *theorem* CNF_zero
- \+ *theorem* CNF_ne_zero
- \+ *theorem* one_CNF
- \+ *theorem* CNF_foldr
- \+ *theorem* CNF_pairwise_aux
- \+ *theorem* CNF_pairwise
- \+ *theorem* CNF_fst_le_log
- \+ *theorem* CNF_fst_le
- \+ *theorem* CNF_snd_lt
- \+ *theorem* CNF_sorted
- \+ *theorem* nat_cast_mul
- \+ *theorem* nat_cast_power
- \+ *theorem* nat_cast_le
- \+ *theorem* nat_cast_lt
- \+ *theorem* nat_cast_inj
- \+ *theorem* nat_cast_eq_zero
- \+ *theorem* nat_cast_ne_zero
- \+ *theorem* nat_cast_pos
- \+ *theorem* nat_cast_sub
- \+ *theorem* nat_cast_div
- \+ *theorem* nat_cast_mod
- \+ *theorem* nat_le_card
- \+ *theorem* nat_lt_card
- \+ *theorem* card_lt_nat
- \+ *theorem* card_le_nat
- \+ *theorem* card_eq_nat
- \+ *theorem* type_fin
- \+ *theorem* lift_nat_cast
- \+ *theorem* lift_type_fin
- \+ *theorem* fintype_card
- \+ *theorem* ord_omega
- \+ *theorem* add_one_of_omega_le
- \+ *theorem* lt_omega
- \+ *theorem* nat_lt_omega
- \+ *theorem* omega_pos
- \+ *theorem* omega_ne_zero
- \+ *theorem* one_lt_omega
- \+ *theorem* omega_is_limit
- \+ *theorem* omega_le
- \+ *theorem* nat_lt_limit
- \+ *theorem* omega_le_of_is_limit
- \+ *theorem* add_omega
- \+ *theorem* add_lt_omega
- \+ *theorem* mul_lt_omega
- \+ *theorem* is_limit_iff_omega_dvd
- \+ *theorem* power_lt_omega
- \+ *theorem* add_omega_power
- \+ *theorem* add_lt_omega_power
- \+ *theorem* add_absorp
- \+ *theorem* add_absorp_iff
- \+ *theorem* add_mul_limit_aux
- \+ *theorem* add_mul_succ
- \+ *theorem* add_mul_limit
- \+ *theorem* mul_omega
- \+ *theorem* mul_lt_omega_power
- \+ *theorem* mul_omega_dvd
- \+ *theorem* mul_omega_power_power
- \+ *theorem* power_omega
- \+ *theorem* iterate_le_nfp
- \+ *theorem* le_nfp_self
- \+ *theorem* is_normal.lt_nfp
- \+ *theorem* is_normal.nfp_le
- \+ *theorem* is_normal.nfp_le_fp
- \+ *theorem* is_normal.nfp_fp
- \+ *theorem* is_normal.le_nfp
- \+ *theorem* nfp_eq_self
- \+ *theorem* deriv_zero
- \+ *theorem* deriv_succ
- \+ *theorem* deriv_limit
- \+ *theorem* deriv_is_normal
- \+ *theorem* is_normal.deriv_fp
- \+ *theorem* is_normal.fp_iff_deriv
- \+ *def* pred
- \+ *def* is_limit
- \+ *def* limit_rec_on
- \+ *def* is_normal
- \+ *def* sub
- \+ *def* sup
- \+ *def* bsup
- \+ *def* power
- \+ *def* log
- \+ *def* nfp
- \+ *def* deriv

Modified src/set_theory/ordinal_notation.lean
- \+/\- *theorem* oadd_lt_oadd_1
- \+/\- *theorem* oadd_lt_oadd_2
- \+/\- *theorem* oadd_lt_oadd_3
- \+/\- *def* NF



## [2020-07-23 08:52:03](https://github.com/leanprover-community/mathlib/commit/79df8cc)
refactor(order/filter/at_top): import order.filter.bases ([#3523](https://github.com/leanprover-community/mathlib/pull/3523))
This way we can use facts about `filter.has_basis` in `filter.at_top`.
Also generalize `is_countably_generated_at_top_finset_nat`
to `at_top` filter on any `encodable` type.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* at_top_basis
- \+ *lemma* at_top_basis'
- \+ *lemma* at_top_countable_basis
- \+ *lemma* has_antimono_basis.tendsto
- \+ *lemma* tendsto_iff_seq_tendsto
- \+ *lemma* tendsto_of_seq_tendsto
- \+ *lemma* subseq_tendsto

Modified src/order/filter/bases.lean
- \+ *lemma* has_countable_basis.is_countably_generated
- \- *lemma* at_top_basis
- \- *lemma* at_top_basis'
- \- *lemma* has_antimono_basis.tendsto
- \- *lemma* tendsto_iff_seq_tendsto
- \- *lemma* tendsto_of_seq_tendsto
- \- *lemma* subseq_tendsto
- \- *lemma* is_countably_generated_at_top_finset_nat



## [2020-07-23 07:50:13](https://github.com/leanprover-community/mathlib/commit/d974457)
feat(ring_theory/ideal_over): a prime ideal lying over a maximal ideal is maximal ([#3488](https://github.com/leanprover-community/mathlib/pull/3488))
By making the results in `ideal_over.lean` a bit more general, we can transfer to quotient rings. This allows us to prove a strict inclusion `I < J` of ideals in `S` results in a strict inclusion `I.comap f < J.comap f` if `R` if `f : R ->+* S` is nice enough. As a corollary, a prime ideal lying over a maximal ideal is maximal.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* map_monic_eq_zero_iff

Modified src/ring_theory/ideal_operations.lean
- \+ *lemma* comap_eq_top_iff
- \+ *lemma* mem_quotient_iff_mem

Modified src/ring_theory/ideal_over.lean
- \+ *lemma* coeff_zero_mem_comap_of_root_mem_of_eval_mem
- \+/\- *lemma* coeff_zero_mem_comap_of_root_mem
- \+ *lemma* exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem
- \+/\- *lemma* exists_coeff_ne_zero_mem_comap_of_root_mem
- \+ *lemma* exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff
- \+ *lemma* comap_lt_comap_of_root_mem_sdiff
- \+/\- *lemma* comap_ne_bot_of_algebraic_mem
- \+/\- *lemma* comap_ne_bot_of_integral_mem
- \+ *lemma* mem_of_one_mem
- \+ *lemma* comap_lt_comap_of_integral_mem_sdiff
- \+ *lemma* is_maximal_of_is_integral_of_is_maximal_comap
- \+ *lemma* integral_closure.comap_lt_comap
- \+ *lemma* integral_closure.is_maximal_of_is_maximal_comap

Modified src/ring_theory/ideals.lean
- \+ *lemma* mk_surjective



## [2020-07-23 02:51:42](https://github.com/leanprover-community/mathlib/commit/7397db7)
chore(data/sym2) : simplify proofs ([#3522](https://github.com/leanprover-community/mathlib/pull/3522))
This shouldn't change any declarations, only proofs.
#### Estimated changes
Modified src/data/sym2.lean
- \+/\- *lemma* rel.is_equivalence
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp
- \+/\- *lemma* mk_has_mem
- \+/\- *lemma* vmem_other_spec
- \+/\- *lemma* from_rel_proj_prop
- \+/\- *lemma* from_rel_prop
- \+/\- *def* is_diag



## [2020-07-23 01:10:58](https://github.com/leanprover-community/mathlib/commit/c149839)
chore(topology/uniform_space/basic): golf a proof ([#3521](https://github.com/leanprover-community/mathlib/pull/3521))
Also prove that a `subsingleton` has a unique `topological_space` structure.
#### Estimated changes
Modified src/topology/order.lean


Modified src/topology/uniform_space/basic.lean




## [2020-07-23 01:10:56](https://github.com/leanprover-community/mathlib/commit/4a918fb)
chore(order/complete_lattice): add `supr/infi_of_empty(')` ([#3519](https://github.com/leanprover-community/mathlib/pull/3519))
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *theorem* infi_of_empty'
- \+ *theorem* supr_of_empty'
- \+ *theorem* infi_of_empty
- \+ *theorem* supr_of_empty



## [2020-07-23 01:10:54](https://github.com/leanprover-community/mathlib/commit/827fcd0)
feat(analysis/convex/basic): add lemmas about convex combination of endpoints of intervals ([#3482](https://github.com/leanprover-community/mathlib/pull/3482))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex.combo_self
- \+ *lemma* convex.mem_Ioo
- \+ *lemma* convex.mem_Ioc
- \+ *lemma* convex.mem_Ico
- \+ *lemma* convex.mem_Icc



## [2020-07-22 23:58:19](https://github.com/leanprover-community/mathlib/commit/fbcd890)
chore(data/subtype,order/complete_lattice): use `coe` instead of `subtype.val` ([#3518](https://github.com/leanprover-community/mathlib/pull/3518))
#### Estimated changes
Modified src/data/subtype.lean


Modified src/measure_theory/measure_space.lean


Modified src/order/complete_lattice.lean


Modified src/order/filter/bases.lean
- \+/\- *lemma* countable_binfi_eq_infi_seq

Modified src/ring_theory/algebraic.lean




## [2020-07-22 19:30:06](https://github.com/leanprover-community/mathlib/commit/1dd69d3)
refactor(data/polynomial): re-organizing ([#3512](https://github.com/leanprover-community/mathlib/pull/3512))
This builds on [#3407](https://github.com/leanprover-community/mathlib/pull/3407), trying to get related material closer together. 
There shouldn't be any change to the set of declarations, just the order they come in and the imports required to get them.
The major changes are:
1. `data.polynomial.derivative` now has much weaker imports
2. generally, material has been moved "upwards" to the first place it can be done (a lot of material moved out of `data.polynomial.degree` into `data.polynomial.degree.basic` -- essentially `degree` is the material about `degree` that also needs `eval` and friends; a further rename might be appropriate)
3. some of the later material is no longer a big chain of linear dependencies, but compiles separately
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \- *lemma* C_mul'
- \- *lemma* C_inj
- \- *lemma* eval_mul
- \- *lemma* eval_pow
- \- *lemma* eval₂_hom
- \- *lemma* root_mul_left_of_is_root
- \- *lemma* root_mul_right_of_is_root

Modified src/data/polynomial/basic.lean


Modified src/data/polynomial/coeff.lean
- \+ *lemma* finset_sum_coeff
- \+ *lemma* C_mul'

Modified src/data/polynomial/default.lean


Modified src/data/polynomial/degree.lean
- \- *lemma* coeff_nat_degree_eq_zero_of_degree_lt
- \- *lemma* ne_zero_of_degree_gt
- \- *lemma* eq_C_of_degree_le_zero
- \- *lemma* eq_C_of_degree_eq_zero
- \- *lemma* degree_le_zero_iff
- \- *lemma* degree_add_le
- \- *lemma* leading_coeff_zero
- \- *lemma* leading_coeff_eq_zero
- \- *lemma* leading_coeff_eq_zero_iff_deg_eq_bot
- \- *lemma* degree_add_eq_of_degree_lt
- \- *lemma* degree_add_C
- \- *lemma* degree_add_eq_of_leading_coeff_add_ne_zero
- \- *lemma* degree_erase_le
- \- *lemma* degree_erase_lt
- \- *lemma* degree_sum_le
- \- *lemma* degree_mul_le
- \- *lemma* degree_pow_le
- \- *lemma* leading_coeff_monomial
- \- *lemma* leading_coeff_C
- \- *lemma* leading_coeff_X
- \- *lemma* monic_X
- \- *lemma* leading_coeff_one
- \- *lemma* monic_one
- \- *lemma* monic.ne_zero_of_zero_ne_one
- \- *lemma* monic.ne_zero
- \- *lemma* leading_coeff_add_of_degree_lt
- \- *lemma* leading_coeff_add_of_degree_eq
- \- *lemma* coeff_mul_degree_add_degree
- \- *lemma* degree_mul'
- \- *lemma* nat_degree_mul'
- \- *lemma* leading_coeff_mul'
- \- *lemma* leading_coeff_pow'
- \- *lemma* degree_pow'
- \- *lemma* nat_degree_pow'
- \- *lemma* leading_coeff_X_pow
- \- *lemma* nat_degree_mul_le
- \- *lemma* subsingleton_of_monic_zero
- \- *lemma* zero_le_degree_iff
- \- *lemma* degree_nonneg_iff_ne_zero
- \- *lemma* nat_degree_eq_zero_iff_degree_le_zero
- \- *lemma* degree_lt_degree_mul_X
- \- *lemma* eq_C_of_nat_degree_le_zero
- \- *lemma* nat_degree_pos_iff_degree_pos
- \- *lemma* degree_X_pow
- \- *lemma* degree_sub_le
- \- *lemma* degree_sub_lt
- \- *lemma* nat_degree_X_sub_C_le
- \- *lemma* degree_X_sub_C
- \- *lemma* nat_degree_X_sub_C
- \- *lemma* next_coeff_X_sub_C
- \- *lemma* degree_X_pow_sub_C
- \- *lemma* X_pow_sub_C_ne_zero
- \- *lemma* nat_degree_X_pow_sub_C
- \- *lemma* degree_mul
- \- *lemma* degree_pow
- \- *lemma* leading_coeff_mul
- \- *lemma* leading_coeff_hom_apply
- \- *lemma* leading_coeff_pow
- \- *theorem* leading_coeff_mul_X_pow
- \- *theorem* degree_le_iff_coeff_zero
- \- *theorem* not_is_unit_X
- \- *theorem* X_sub_C_ne_zero
- \- *def* leading_coeff_hom

Modified src/data/polynomial/degree/basic.lean
- \+ *lemma* as_sum
- \+ *lemma* sum_over_range'
- \+ *lemma* sum_over_range
- \+ *lemma* coeff_nat_degree_eq_zero_of_degree_lt
- \+ *lemma* ne_zero_of_degree_gt
- \+ *lemma* eq_C_of_degree_le_zero
- \+ *lemma* eq_C_of_degree_eq_zero
- \+ *lemma* degree_le_zero_iff
- \+ *lemma* degree_add_le
- \+ *lemma* leading_coeff_zero
- \+ *lemma* leading_coeff_eq_zero
- \+ *lemma* leading_coeff_eq_zero_iff_deg_eq_bot
- \+ *lemma* degree_add_eq_of_degree_lt
- \+ *lemma* degree_add_C
- \+ *lemma* degree_add_eq_of_leading_coeff_add_ne_zero
- \+ *lemma* degree_erase_le
- \+ *lemma* degree_erase_lt
- \+ *lemma* degree_sum_le
- \+ *lemma* degree_mul_le
- \+ *lemma* degree_pow_le
- \+ *lemma* leading_coeff_monomial
- \+ *lemma* leading_coeff_C
- \+ *lemma* leading_coeff_X
- \+ *lemma* monic_X
- \+ *lemma* leading_coeff_one
- \+ *lemma* monic_one
- \+ *lemma* monic.ne_zero_of_zero_ne_one
- \+ *lemma* monic.ne_zero
- \+ *lemma* leading_coeff_add_of_degree_lt
- \+ *lemma* leading_coeff_add_of_degree_eq
- \+ *lemma* coeff_mul_degree_add_degree
- \+ *lemma* degree_mul'
- \+ *lemma* nat_degree_mul'
- \+ *lemma* leading_coeff_mul'
- \+ *lemma* leading_coeff_pow'
- \+ *lemma* degree_pow'
- \+ *lemma* nat_degree_pow'
- \+ *lemma* leading_coeff_X_pow
- \+ *lemma* nat_degree_mul_le
- \+ *lemma* subsingleton_of_monic_zero
- \+ *lemma* zero_le_degree_iff
- \+ *lemma* degree_nonneg_iff_ne_zero
- \+ *lemma* nat_degree_eq_zero_iff_degree_le_zero
- \+ *lemma* degree_lt_degree_mul_X
- \+ *lemma* eq_C_of_nat_degree_le_zero
- \+ *lemma* nat_degree_pos_iff_degree_pos
- \+ *lemma* degree_X_pow
- \+ *lemma* degree_sub_le
- \+ *lemma* degree_sub_lt
- \+ *lemma* nat_degree_X_sub_C_le
- \+ *lemma* degree_X_sub_C
- \+ *lemma* nat_degree_X_sub_C
- \+ *lemma* next_coeff_X_sub_C
- \+ *lemma* degree_X_pow_sub_C
- \+ *lemma* X_pow_sub_C_ne_zero
- \+ *lemma* nat_degree_X_pow_sub_C
- \+ *lemma* degree_mul
- \+ *lemma* degree_pow
- \+ *lemma* leading_coeff_mul
- \+ *lemma* leading_coeff_hom_apply
- \+ *lemma* leading_coeff_pow
- \+ *theorem* leading_coeff_mul_X_pow
- \+ *theorem* degree_le_iff_coeff_zero
- \+ *theorem* not_is_unit_X
- \+ *theorem* X_sub_C_ne_zero
- \+ *def* leading_coeff_hom

Modified src/data/polynomial/derivative.lean
- \- *lemma* derivative_eval
- \- *lemma* is_coprime_of_is_root_of_eval_derivative_ne_zero

Modified src/data/polynomial/div.lean


Modified src/data/polynomial/eval.lean
- \+ *lemma* eval_mul
- \+ *lemma* eval_pow
- \+ *lemma* eval₂_hom
- \+ *lemma* root_mul_left_of_is_root
- \+ *lemma* root_mul_right_of_is_root

Modified src/data/polynomial/field_division.lean
- \+ *lemma* is_coprime_of_is_root_of_eval_derivative_ne_zero

Modified src/data/polynomial/identities.lean
- \+ *lemma* derivative_eval

Modified src/data/polynomial/induction.lean
- \- *lemma* finset_sum_coeff
- \- *lemma* as_sum
- \- *lemma* sum_over_range'
- \- *lemma* sum_over_range

Created src/data/polynomial/integral_normalization.lean
- \+ *lemma* integral_normalization_coeff_degree
- \+ *lemma* integral_normalization_coeff_nat_degree
- \+ *lemma* integral_normalization_coeff_ne_degree
- \+ *lemma* integral_normalization_coeff_ne_nat_degree
- \+ *lemma* monic_integral_normalization
- \+ *lemma* support_integral_normalization
- \+ *lemma* integral_normalization_eval₂_eq_zero
- \+ *lemma* integral_normalization_aeval_eq_zero

Modified src/data/polynomial/monic.lean
- \- *lemma* integral_normalization_coeff_degree
- \- *lemma* integral_normalization_coeff_nat_degree
- \- *lemma* integral_normalization_coeff_ne_degree
- \- *lemma* integral_normalization_coeff_ne_nat_degree
- \- *lemma* monic_integral_normalization
- \- *lemma* support_integral_normalization
- \- *lemma* integral_normalization_eval₂_eq_zero
- \- *lemma* integral_normalization_aeval_eq_zero

Modified src/data/polynomial/monomial.lean
- \+ *lemma* C_inj

Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/separable.lean


Modified src/ring_theory/algebraic.lean




## [2020-07-22 16:16:15](https://github.com/leanprover-community/mathlib/commit/36ea9e8)
chore(*): cleanup imports ([#3511](https://github.com/leanprover-community/mathlib/pull/3511))
A not-very-interesting cleanup of imports.
I deleted 
```
instance orbit_fintype (b : β) [fintype α] [decidable_eq β] :	
  fintype (orbit α b) := set.fintype_range _
```
which wasn't being used, for the sake of not having to import everything about finiteness into `algebra.group_action`.
#### Estimated changes
Modified src/algebra/char_zero.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/group/units_hom.lean


Modified src/algebra/group_power.lean


Modified src/algebra/pi_instances.lean


Modified src/algebra/pointwise.lean


Modified src/algebra/ring.lean


Modified src/analysis/convex/basic.lean


Modified src/computability/primrec.lean


Modified src/computability/turing_machine.lean


Modified src/data/dfinsupp.lean


Modified src/data/finsupp.lean


Modified src/data/monoid_algebra.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/eval.lean


Modified src/data/polynomial/ring_division.lean


Modified src/data/sigma/basic.lean


Modified src/deprecated/group.lean


Modified src/deprecated/ring.lean


Modified src/group_theory/group_action.lean


Modified src/group_theory/submonoid/basic.lean


Modified src/logic/embedding.lean


Modified src/order/complete_boolean_algebra.lean


Modified src/order/order_iso.lean


Modified src/order/order_iso_nat.lean


Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/ideals.lean


Modified src/ring_theory/matrix_algebra.lean


Modified src/ring_theory/polynomial_algebra.lean


Modified src/topology/metric_space/lipschitz.lean




## [2020-07-22 16:16:13](https://github.com/leanprover-community/mathlib/commit/a8cedf9)
feat(data/nat/digits): a number is bigger than base^(digits length - 1) ([#3498](https://github.com/leanprover-community/mathlib/pull/3498))
#### Estimated changes
Modified src/data/nat/digits.lean
- \+ *lemma* base_pow_length_digits_le'
- \+ *lemma* base_pow_length_digits_le



## [2020-07-22 14:52:45](https://github.com/leanprover-community/mathlib/commit/acc2802)
feat(tactic/extract_goal): remove annoying spaces ([#3514](https://github.com/leanprover-community/mathlib/pull/3514))
closes [#3375](https://github.com/leanprover-community/mathlib/pull/3375)
#### Estimated changes
Modified src/tactic/interactive.lean




## [2020-07-22 14:04:33](https://github.com/leanprover-community/mathlib/commit/a971a88)
refactor(linear_algebra/nonsingular_inverse, data/matrix/basic): update_* rectangular matrices ([#3403](https://github.com/leanprover-community/mathlib/pull/3403))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* update_row_self
- \+ *lemma* update_column_self
- \+ *lemma* update_row_ne
- \+ *lemma* update_column_ne
- \+ *lemma* update_row_val
- \+ *lemma* update_column_val
- \+ *lemma* update_row_transpose
- \+ *lemma* update_column_transpose
- \+ *def* update_row
- \+ *def* update_column

Modified src/linear_algebra/nonsingular_inverse.lean
- \- *lemma* update_row_self
- \- *lemma* update_column_self
- \- *lemma* update_row_ne
- \- *lemma* update_column_ne
- \- *lemma* update_row_val
- \- *lemma* update_column_val
- \- *lemma* update_row_transpose
- \- *def* update_row
- \- *def* update_column



## [2020-07-22 11:32:56](https://github.com/leanprover-community/mathlib/commit/90d3386)
feat(category_theory/kernels): compute kernel (f ≫ g) when one is an iso ([#3438](https://github.com/leanprover-community/mathlib/pull/3438))
#### Estimated changes
Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* kernel_comp_is_iso_hom_comp_kernel_ι
- \+ *lemma* kernel_comp_is_iso_inv_comp_kernel_ι
- \+ *lemma* kernel_is_iso_comp_hom_comp_kernel_ι
- \+ *lemma* kernel_is_iso_comp_inv_comp_kernel_ι
- \+ *lemma* cokernel_π_comp_cokernel_comp_is_iso_hom
- \+ *lemma* cokernel_π_comp_cokernel_comp_is_iso_inv
- \+ *lemma* cokernel_π_comp_cokernel_is_iso_comp_hom
- \+ *lemma* cokernel_π_comp_cokernel_is_iso_comp_inv
- \+ *def* kernel_comp_is_iso
- \+ *def* kernel_is_iso_comp
- \+ *def* cokernel_comp_is_iso
- \+ *def* cokernel_is_iso_comp



## [2020-07-22 10:18:14](https://github.com/leanprover-community/mathlib/commit/39f8f02)
refactor(algebra/big_operators): split file, reduce imports ([#3495](https://github.com/leanprover-community/mathlib/pull/3495))
I've split up `algebra.big_operators`. It wasn't completely obvious how to divide it up, but this is an attempt to balance coherence / file size / minimal imports.
#### Estimated changes
Modified archive/100-theorems-list/42_inverse_triangle_sum.lean


Modified archive/sensitivity.lean


Renamed src/algebra/big_operators.lean to src/algebra/big_operators/basic.lean
- \+/\- *lemma* prod_pow_boole
- \+/\- *lemma* card_eq_sum_ones
- \+/\- *lemma* sum_nat_cast
- \+/\- *lemma* sum_comp
- \- *lemma* sum_Ico_add
- \- *lemma* prod_Ico_add
- \- *lemma* sum_Ico_succ_top
- \- *lemma* prod_Ico_succ_top
- \- *lemma* sum_eq_sum_Ico_succ_bot
- \- *lemma* prod_eq_prod_Ico_succ_bot
- \- *lemma* prod_Ico_consecutive
- \- *lemma* prod_range_mul_prod_Ico
- \- *lemma* prod_Ico_eq_mul_inv
- \- *lemma* sum_Ico_eq_sub
- \- *lemma* prod_Ico_eq_prod_range
- \- *lemma* prod_Ico_reflect
- \- *lemma* sum_Ico_reflect
- \- *lemma* prod_range_reflect
- \- *lemma* sum_range_reflect
- \- *lemma* prod_powerset_insert
- \- *lemma* prod_nat_cast
- \- *lemma* le_sum_of_subadditive
- \- *lemma* abs_sum_le_sum_abs
- \- *lemma* sum_mul
- \- *lemma* mul_sum
- \- *lemma* sum_mul_boole
- \- *lemma* sum_boole_mul
- \- *lemma* sum_div
- \- *lemma* prod_sum
- \- *lemma* sum_mul_sum
- \- *lemma* prod_add
- \- *lemma* sum_pow_mul_eq_add_pow
- \- *lemma* prod_pow_eq_pow_sum
- \- *lemma* sum_le_sum
- \- *lemma* sum_nonneg
- \- *lemma* sum_nonpos
- \- *lemma* sum_le_sum_of_subset_of_nonneg
- \- *lemma* sum_mono_set_of_nonneg
- \- *lemma* sum_eq_zero_iff_of_nonneg
- \- *lemma* sum_eq_zero_iff_of_nonpos
- \- *lemma* single_le_sum
- \- *lemma* sum_eq_zero_iff
- \- *lemma* sum_le_sum_of_subset
- \- *lemma* sum_mono_set
- \- *lemma* sum_le_sum_of_ne_zero
- \- *lemma* sum_lt_sum_of_nonempty
- \- *lemma* sum_lt_sum_of_subset
- \- *lemma* exists_pos_of_sum_zero_of_exists_nonzero
- \- *lemma* prod_nonneg
- \- *lemma* prod_pos
- \- *lemma* prod_le_prod
- \- *lemma* prod_le_prod'
- \- *lemma* card_pi
- \- *lemma* prod_Ico_id_eq_fact
- \- *lemma* sum_range_id_mul_two
- \- *lemma* sum_range_id
- \- *lemma* is_group_hom_finset_prod
- \- *lemma* sum_lt_top
- \- *lemma* sum_lt_top_iff
- \- *lemma* sum_eq_top_iff
- \- *lemma* op_sum
- \- *lemma* unop_sum
- \- *theorem* directed.finset_le
- \- *theorem* finset.exists_le
- \- *theorem* dvd_sum
- \- *theorem* sum_lt_sum
- \- *theorem* exists_le_of_sum_le
- \- *theorem* card_le_mul_card_image

Created src/algebra/big_operators/default.lean


Created src/algebra/big_operators/intervals.lean
- \+ *lemma* sum_Ico_add
- \+ *lemma* prod_Ico_add
- \+ *lemma* sum_Ico_succ_top
- \+ *lemma* prod_Ico_succ_top
- \+ *lemma* sum_eq_sum_Ico_succ_bot
- \+ *lemma* prod_eq_prod_Ico_succ_bot
- \+ *lemma* prod_Ico_consecutive
- \+ *lemma* prod_range_mul_prod_Ico
- \+ *lemma* prod_Ico_eq_mul_inv
- \+ *lemma* sum_Ico_eq_sub
- \+ *lemma* prod_Ico_eq_prod_range
- \+ *lemma* prod_Ico_reflect
- \+ *lemma* sum_Ico_reflect
- \+ *lemma* prod_range_reflect
- \+ *lemma* sum_range_reflect
- \+ *lemma* prod_Ico_id_eq_fact
- \+ *lemma* sum_range_id_mul_two
- \+ *lemma* sum_range_id

Created src/algebra/big_operators/order.lean
- \+ *lemma* le_sum_of_subadditive
- \+ *lemma* abs_sum_le_sum_abs
- \+ *lemma* sum_le_sum
- \+ *lemma* sum_nonneg
- \+ *lemma* sum_nonpos
- \+ *lemma* sum_le_sum_of_subset_of_nonneg
- \+ *lemma* sum_mono_set_of_nonneg
- \+ *lemma* sum_eq_zero_iff_of_nonneg
- \+ *lemma* sum_eq_zero_iff_of_nonpos
- \+ *lemma* single_le_sum
- \+ *lemma* sum_eq_zero_iff
- \+ *lemma* sum_le_sum_of_subset
- \+ *lemma* sum_mono_set
- \+ *lemma* sum_le_sum_of_ne_zero
- \+ *lemma* sum_lt_sum_of_nonempty
- \+ *lemma* sum_lt_sum_of_subset
- \+ *lemma* exists_pos_of_sum_zero_of_exists_nonzero
- \+ *lemma* prod_nonneg
- \+ *lemma* prod_pos
- \+ *lemma* prod_le_prod
- \+ *lemma* prod_le_prod'
- \+ *lemma* sum_lt_top
- \+ *lemma* sum_lt_top_iff
- \+ *lemma* sum_eq_top_iff
- \+ *lemma* op_sum
- \+ *lemma* unop_sum
- \+ *theorem* card_le_mul_card_image
- \+ *theorem* sum_lt_sum
- \+ *theorem* exists_le_of_sum_le

Created src/algebra/big_operators/ring.lean
- \+ *lemma* sum_mul
- \+ *lemma* mul_sum
- \+ *lemma* sum_mul_boole
- \+ *lemma* sum_boole_mul
- \+ *lemma* sum_div
- \+ *lemma* prod_sum
- \+ *lemma* sum_mul_sum
- \+ *lemma* prod_add
- \+ *lemma* sum_pow_mul_eq_add_pow
- \+ *lemma* prod_pow_eq_pow_sum
- \+ *lemma* prod_nat_cast
- \+ *lemma* prod_powerset_insert
- \+ *theorem* dvd_sum

Modified src/algebra/direct_limit.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/module.lean
- \- *lemma* sum_const'
- \- *theorem* exists_card_smul_le_sum
- \- *theorem* exists_card_smul_ge_sum

Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/preadditive/default.lean


Created src/data/finset/order.lean
- \+ *theorem* directed.finset_le
- \+ *theorem* finset.exists_le

Modified src/data/finsupp.lean


Modified src/data/fintype/card.lean
- \+ *lemma* finset.card_pi

Modified src/data/matrix/basic.lean


Modified src/data/nat/choose.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/totient.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/nnreal.lean


Modified src/data/set/finite.lean


Modified src/data/support.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/submonoid/membership.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/lagrange.lean


Modified src/linear_algebra/multilinear.lean


Modified src/ring_theory/coprime.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/prime.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/subset_properties.lean


Modified test/conv/apply_congr.lean


Modified test/fin_cases.lean




## [2020-07-22 08:55:49](https://github.com/leanprover-community/mathlib/commit/197b501)
feat(tactic/extract_goal): better support for `let` expressions ([#3496](https://github.com/leanprover-community/mathlib/pull/3496))
Improve treatment of let expressions [#3375](https://github.com/leanprover-community/mathlib/pull/3375)
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/interactive.lean




## [2020-07-22 05:08:37](https://github.com/leanprover-community/mathlib/commit/64335de)
chore(topology/category/): switch to bundled morphisms in Top ([#3506](https://github.com/leanprover-community/mathlib/pull/3506))
This is a natural follow-up to @Nicknamen's recent PRs splitting bundled continuous maps out of `compact_open`.
There is a slight regression in `algebraic_geometry.presheafed_space` and `algebraic_geometry.stalks`, requiring a more explicit coercion. I'd encourage reviewers to ignore this, as I'll make a separate PR simplifying this (basically: having a coercion from morphisms of `PresheafedSpace`s to morphisms of `Top`s is unrealistically ambitious, and moreover harder to read, than just using the projection notation, and removing it makes everything easier).
#### Estimated changes
Modified docs/tutorial/category_theory/calculating_colimits_in_Top.lean
- \+/\- *def* f

Modified src/algebraic_geometry/presheafed_space.lean


Modified src/algebraic_geometry/stalks.lean


Modified src/topology/category/Top/adjunctions.lean
- \+/\- *def* adj₁
- \+/\- *def* adj₂

Modified src/topology/category/Top/basic.lean
- \+ *lemma* comp_app

Modified src/topology/category/Top/limits.lean


Modified src/topology/category/Top/opens.lean
- \+/\- *lemma* map_obj

Modified src/topology/category/UniformSpace.lean


Modified src/topology/continuous_map.lean
- \+ *lemma* coe_inj
- \+ *def* id
- \+ *def* comp

Modified src/topology/sheaves/presheaf_of_functions.lean
- \- *lemma* one
- \- *lemma* zero
- \- *lemma* add
- \- *lemma* mul
- \+/\- *def* map



## [2020-07-22 03:47:11](https://github.com/leanprover-community/mathlib/commit/dced343)
feat(data/list/basic): induction from both ends ([#3448](https://github.com/leanprover-community/mathlib/pull/3448))
This was originally an induction principle on palindromes, but researching Coq solutions made me realize that weakening the statement made it simpler and much easier to prove.
- ["The way we proceeded was to prove first an induction principle for lists, considering insertions at both ends..."][1]
- ["... generalizing a single variable in that definition would create another inductive definition of a list."][2]
[1]: https://www.labri.fr/perso/casteran/CoqArt/inductive-prop-chap/palindrome.html
[2]: https://danilafe.com/blog/coq_palindrome/
This also adds the lemmas `length_init` and `init_append_last`.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* length_init
- \+ *theorem* init_append_last
- \+/\- *def* reverse_rec_on
- \+ *def* bidirectional_rec
- \+ *def* bidirectional_rec_on



## [2020-07-22 02:38:08](https://github.com/leanprover-community/mathlib/commit/55e7dcc)
fix(ring_theory/jacobson): Clean up documentation in Jacobson Ring definitions ([#3501](https://github.com/leanprover-community/mathlib/pull/3501))
Fixes to formatting and documentation found after merging the definition of Jacobson Rings in https://github.com/leanprover-community/mathlib/pull/3404
#### Estimated changes
Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/jacobson_ideal.lean




## [2020-07-22 01:12:15](https://github.com/leanprover-community/mathlib/commit/314b209)
chore(scripts): update nolints.txt ([#3505](https://github.com/leanprover-community/mathlib/pull/3505))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-22 00:27:14](https://github.com/leanprover-community/mathlib/commit/2219dc1)
feat(tactic/linarith): put certificate generation in tactic monad ([#3504](https://github.com/leanprover-community/mathlib/pull/3504))
#### Estimated changes
Modified src/tactic/linarith/datatypes.lean


Modified src/tactic/linarith/elimination.lean


Modified src/tactic/linarith/frontend.lean


Modified src/tactic/linarith/verification.lean




## [2020-07-22 00:27:12](https://github.com/leanprover-community/mathlib/commit/219e298)
feat(ring_theory/discrete_valuation_ring): add DVR ([#3476](https://github.com/leanprover-community/mathlib/pull/3476))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* dvd_of_associated
- \+ *lemma* dvd_dvd_of_associated
- \+ *theorem* dvd_dvd_iff_associated

Created src/ring_theory/discrete_valuation_ring.lean
- \+ *lemma* not_a_field
- \+ *lemma* associated_of_irreducible
- \+ *theorem* irreducible_iff_uniformiser
- \+ *theorem* exists_irreducible
- \+ *theorem* iff_PID_with_one_nonzero_prime

Modified src/ring_theory/ideals.lean
- \+ *lemma* span_singleton_eq_span_singleton
- \+ *lemma* span_singleton_mul_right_unit
- \+ *lemma* span_singleton_mul_left_unit
- \+ *lemma* maximal_of_no_maximal
- \+ *lemma* maximal_ideal_unique
- \+ *lemma* eq_maximal_ideal
- \+ *lemma* le_maximal_ideal
- \+ *lemma* local_of_unique_nonzero_prime
- \- *lemma* max_ideal_unique



## [2020-07-21 23:16:29](https://github.com/leanprover-community/mathlib/commit/84d6497)
fix(algebra/ring): add coe_neg_one lemma to units ([#3489](https://github.com/leanprover-community/mathlib/pull/3489))
Follow up to [#3472](https://github.com/leanprover-community/mathlib/pull/3472) - adds `coe_neg_one`, which allows `norm_cast` to handle hypotheses like `↑-1 = 1`
#### Estimated changes
Modified src/algebra/ring.lean




## [2020-07-21 22:26:30](https://github.com/leanprover-community/mathlib/commit/e448bb1)
feat(tactic/linarith): modularize coefficient oracle ([#3502](https://github.com/leanprover-community/mathlib/pull/3502))
This makes it easy to plug an alternate certificate search method (e.g. simplex-based) into `linarith`, should one desire.
#### Estimated changes
Modified src/tactic/linarith/datatypes.lean


Modified src/tactic/linarith/elimination.lean


Modified src/tactic/linarith/frontend.lean


Modified src/tactic/linarith/verification.lean




## [2020-07-21 21:58:58](https://github.com/leanprover-community/mathlib/commit/c6aa8e7)
feat(algebra/invertible): invertible elements are units ([#3499](https://github.com/leanprover-community/mathlib/pull/3499))
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *lemma* unit_of_invertible_val
- \+ *lemma* unit_of_invertible_inv
- \+ *def* unit_of_invertible



## [2020-07-21 21:58:56](https://github.com/leanprover-community/mathlib/commit/2fb6a05)
feat(group_theory/semidirect_product): semidirect_product.map ([#3492](https://github.com/leanprover-community/mathlib/pull/3492))
#### Estimated changes
Modified src/group_theory/semidirect_product.lean
- \+ *lemma* map_left
- \+ *lemma* map_right
- \+ *lemma* right_hom_comp_map
- \+ *lemma* map_inl
- \+ *lemma* map_comp_inl
- \+ *lemma* map_inr
- \+ *lemma* map_comp_inr
- \+ *def* map



## [2020-07-21 21:29:16](https://github.com/leanprover-community/mathlib/commit/dfef07a)
chore(analysis/special_functions): moved trig vals out of real.pi, added new trig vals ([#3497](https://github.com/leanprover-community/mathlib/pull/3497))
Moved trigonometric lemmas from real.pi to analysis.special_functions.trigonometric. Also added two new trig lemmas, tan_pi_div_four and arctan_one, to analysis.special_functions.trigonometric.
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Trig.20function.20values
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* sqrt_two_add_series_zero
- \+ *lemma* sqrt_two_add_series_one
- \+ *lemma* sqrt_two_add_series_two
- \+ *lemma* sqrt_two_add_series_zero_nonneg
- \+ *lemma* sqrt_two_add_series_nonneg
- \+ *lemma* sqrt_two_add_series_lt_two
- \+ *lemma* sqrt_two_add_series_succ
- \+ *lemma* sqrt_two_add_series_monotone_left
- \+ *lemma* cos_pi_over_two_pow
- \+ *lemma* sin_square_pi_over_two_pow
- \+ *lemma* sin_square_pi_over_two_pow_succ
- \+ *lemma* sin_pi_over_two_pow_succ
- \+ *lemma* cos_pi_div_four
- \+ *lemma* sin_pi_div_four
- \+ *lemma* cos_pi_div_eight
- \+ *lemma* sin_pi_div_eight
- \+ *lemma* cos_pi_div_sixteen
- \+ *lemma* sin_pi_div_sixteen
- \+ *lemma* cos_pi_div_thirty_two
- \+ *lemma* sin_pi_div_thirty_two
- \+ *lemma* tan_pi_div_four
- \+ *lemma* arctan_one

Modified src/data/real/pi.lean
- \- *lemma* sqrt_two_add_series_zero
- \- *lemma* sqrt_two_add_series_one
- \- *lemma* sqrt_two_add_series_two
- \- *lemma* sqrt_two_add_series_zero_nonneg
- \- *lemma* sqrt_two_add_series_nonneg
- \- *lemma* sqrt_two_add_series_lt_two
- \- *lemma* sqrt_two_add_series_succ
- \- *lemma* sqrt_two_add_series_monotone_left
- \- *lemma* cos_pi_over_two_pow
- \- *lemma* sin_square_pi_over_two_pow
- \- *lemma* sin_square_pi_over_two_pow_succ
- \- *lemma* sin_pi_over_two_pow_succ
- \- *lemma* cos_pi_div_four
- \- *lemma* sin_pi_div_four
- \- *lemma* cos_pi_div_eight
- \- *lemma* sin_pi_div_eight
- \- *lemma* cos_pi_div_sixteen
- \- *lemma* sin_pi_div_sixteen
- \- *lemma* cos_pi_div_thirty_two
- \- *lemma* sin_pi_div_thirty_two



## [2020-07-21 16:25:32](https://github.com/leanprover-community/mathlib/commit/c47d1d0)
feat(data/{mv_}polynomial): make args to aeval implicit ([#3494](https://github.com/leanprover-community/mathlib/pull/3494))
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+/\- *lemma* aeval_X
- \+/\- *lemma* aeval_C
- \+/\- *theorem* aeval_def

Modified src/data/polynomial/algebra_map.lean
- \+/\- *lemma* aeval_X
- \+/\- *lemma* aeval_C
- \+/\- *lemma* coeff_zero_eq_aeval_zero
- \+/\- *theorem* aeval_def
- \+/\- *theorem* aeval_alg_hom
- \+/\- *theorem* aeval_alg_hom_apply

Modified src/data/polynomial/monic.lean


Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/minimal_polynomial.lean
- \+/\- *lemma* aeval
- \+/\- *lemma* min
- \+/\- *lemma* unique
- \+/\- *lemma* dvd

Modified src/ring_theory/adjoin.lean
- \+/\- *theorem* adjoin_singleton_eq_range

Modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* aeval_eq

Modified src/ring_theory/algebra_tower.lean
- \+/\- *theorem* aeval_apply

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \+/\- *lemma* is_integral_trans_aux

Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/rational_root.lean
- \+/\- *theorem* num_dvd_of_is_root
- \+/\- *theorem* denom_dvd_of_is_root
- \+/\- *theorem* is_integer_of_is_root_of_monic



## [2020-07-21 16:25:30](https://github.com/leanprover-community/mathlib/commit/7efdd99)
feat(algebra/invertible): lemmas ([#3493](https://github.com/leanprover-community/mathlib/pull/3493))
Coauthored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *def* invertible.map



## [2020-07-21 15:23:28](https://github.com/leanprover-community/mathlib/commit/5776f4c)
feat(topology): more lemmas about Ici and Iic neighborhoods ([#3474](https://github.com/leanprover-community/mathlib/pull/3474))
Main feature :  add `tfae_mem_nhds_within_Ici` and `tfae_mem_nhds_within_Iic`, analogous to the existing `tfae_mem_nhds_within_Ioi` and `tfae_mem_nhds_within_Iio`, as well as related lemmas (again imitating the open case)
I also added a few lemmas in `data/set/intervals/basic.lean` that were useful for this and a few upcoming PRs
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* Icc_subset_Ioo
- \+ *lemma* Icc_subset_Ici_self
- \+ *lemma* Icc_subset_Iic_self
- \+ *lemma* Ioc_subset_Ioo_right

Modified src/topology/algebra/ordered.lean
- \+ *lemma* nhds_within_Ici_ne_bot
- \+ *lemma* nhds_within_Ici_self_ne_bot
- \+ *lemma* nhds_within_Iic_ne_bot
- \+ *lemma* nhds_within_Iic_self_ne_bot
- \+ *lemma* tfae_mem_nhds_within_Ici
- \+ *lemma* nhds_within_Icc_eq_nhds_within_Ici
- \+ *lemma* nhds_within_Ico_eq_nhds_within_Ici
- \+ *lemma* mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset
- \+/\- *lemma* mem_nhds_within_Ici_iff_exists_Ico_subset'
- \+ *lemma* mem_nhds_within_Ici_iff_exists_Icc_subset'
- \+ *lemma* Ioo_mem_nhds_within_Ici
- \+ *lemma* Ioc_mem_nhds_within_Ici
- \+ *lemma* Ico_mem_nhds_within_Ici
- \+ *lemma* Icc_mem_nhds_within_Ici
- \+ *lemma* tfae_mem_nhds_within_Iic
- \+ *lemma* nhds_within_Icc_eq_nhds_within_Iic
- \+ *lemma* nhds_within_Ioc_eq_nhds_within_Iic
- \+ *lemma* mem_nhds_within_Iic_iff_exists_mem_Ico_Ioc_subset
- \+ *lemma* mem_nhds_within_Iic_iff_exists_Icc_subset'
- \+ *lemma* Ioo_mem_nhds_within_Iic
- \+ *lemma* Ioc_mem_nhds_within_Iic
- \+ *lemma* Ico_mem_nhds_within_Iic
- \+ *lemma* Icc_mem_nhds_within_Iic
- \+/\- *lemma* mem_nhds_within_Ici_iff_exists_Icc_subset



## [2020-07-21 12:58:53](https://github.com/leanprover-community/mathlib/commit/49049e4)
feat(topology): implemented continuous bundled maps ([#3486](https://github.com/leanprover-community/mathlib/pull/3486))
In this PR we defined continuous bundled maps, adapted the file `compact_open` accordingly, and proved instances of algebraic structures over the type `continuous_map` of continuous bundled maps. This feature was suggested on Zulip multiple times, see for example https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Continuous.20maps
#### Estimated changes
Modified src/topology/algebra/continuous_functions.lean
- \+ *def* continuous.C
- \+ *def* continuous_map.C
- \- *def* C

Modified src/topology/algebra/group.lean


Modified src/topology/compact_open.lean
- \+/\- *lemma* image_coev
- \+/\- *def* induced
- \- *def* continuous_map

Created src/topology/continuous_map.lean
- \+ *theorem* ext
- \+ *def* const



## [2020-07-21 11:50:25](https://github.com/leanprover-community/mathlib/commit/5c55e15)
feat(data/finset/intervals): Lemma about filter and Ico ([#3479](https://github.com/leanprover-community/mathlib/pull/3479))
Add "if you filter an Ico based on being less than or equal to its bottom element, you get the singleton bottom element".
#### Estimated changes
Modified src/data/finset/intervals.lean
- \+ *lemma* filter_Ico_bot

Modified src/data/list/intervals.lean
- \+ *lemma* filter_lt_of_succ_bot
- \+ *lemma* filter_le_of_bot

Modified src/data/multiset/intervals.lean
- \+ *lemma* filter_le_of_bot



## [2020-07-21 10:37:37](https://github.com/leanprover-community/mathlib/commit/d57130b)
feat(field_theory/mv_polynomial): char_p instance ([#3491](https://github.com/leanprover-community/mathlib/pull/3491))
#### Estimated changes
Modified src/field_theory/mv_polynomial.lean




## [2020-07-21 09:25:11](https://github.com/leanprover-community/mathlib/commit/1a31e69)
chore(algebra/group/anti_hom): remove is_group_anti_hom ([#3485](https://github.com/leanprover-community/mathlib/pull/3485))
`is_group_anti_hom` is no longer used anywhere, so I'm going to count it as deprecated and propose removing it.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \- *theorem* is_group_anti_hom.map_prod
- \- *theorem* inv_prod

Deleted src/algebra/group/anti_hom.lean
- \- *theorem* map_one
- \- *theorem* map_inv
- \- *theorem* inv_is_group_anti_hom

Modified src/algebra/group/default.lean




## [2020-07-21 08:38:58](https://github.com/leanprover-community/mathlib/commit/3169970)
feat(category_theory/kernels): helper lemmas for constructing kernels ([#3439](https://github.com/leanprover-community/mathlib/pull/3439))
This does for kernels what [#3398](https://github.com/leanprover-community/mathlib/pull/3398) did for pullbacks.
#### Estimated changes
Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* is_limit_aux
- \+ *def* is_limit.of_ι
- \+ *def* is_colimit_aux
- \+ *def* is_colimit.of_π



## [2020-07-21 07:47:44](https://github.com/leanprover-community/mathlib/commit/d174d3d)
refactor(linear_algebra/*): postpone importing material on direct sums ([#3484](https://github.com/leanprover-community/mathlib/pull/3484))
This is just a refactor, to avoid needing to develop material on direct sums before we can even define an algebra.
#### Estimated changes
Modified src/algebra/direct_limit.lean


Modified src/algebra/lie_algebra.lean


Created src/linear_algebra/direct_sum/finsupp.lean
- \+ *theorem* finsupp_lequiv_direct_sum_single
- \+ *theorem* finsupp_lequiv_direct_sum_symm_lof
- \+ *theorem* finsupp_tensor_finsupp_single
- \+ *theorem* finsupp_tensor_finsupp_symm_single
- \+ *def* finsupp_lequiv_direct_sum
- \+ *def* finsupp_tensor_finsupp

Created src/linear_algebra/direct_sum/tensor_product.lean
- \+ *theorem* direct_sum_lof_tmul_lof
- \+ *def* direct_sum

Modified src/linear_algebra/finsupp.lean
- \- *theorem* finsupp_lequiv_direct_sum_single
- \- *theorem* finsupp_lequiv_direct_sum_symm_lof
- \- *theorem* finsupp_tensor_finsupp_single
- \- *theorem* finsupp_tensor_finsupp_symm_single
- \- *def* finsupp_lequiv_direct_sum
- \- *def* finsupp_tensor_finsupp

Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/tensor_product.lean
- \- *theorem* direct_sum_lof_tmul_lof
- \- *def* direct_sum



## [2020-07-21 04:06:36](https://github.com/leanprover-community/mathlib/commit/c71e67a)
feat(ring_theory/jacobson): definition of Jacobson rings ([#3404](https://github.com/leanprover-community/mathlib/pull/3404))
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* coe_ring_hom

Modified src/ring_theory/ideal_operations.lean
- \+ *lemma* mem_map_iff_of_surjective
- \+ *lemma* le_map_of_comap_le_of_surjective
- \+ *lemma* comap_bot_le_of_injective
- \+ *lemma* comap_le_iff_le_map
- \+ *lemma* ker_le_comap
- \+ *lemma* map_Inf
- \+ *theorem* map_eq_top_or_is_maximal_of_surjective
- \+ *theorem* map.is_maximal
- \+ *theorem* comap.is_maximal
- \- *theorem* jacobson_eq_top_iff
- \- *theorem* mem_jacobson_iff
- \- *theorem* is_local_of_is_maximal_radical
- \- *theorem* is_local.le_jacobson
- \- *theorem* is_local.mem_jacobson_or_exists_inv
- \- *theorem* is_primary_of_is_maximal_radical
- \+ *def* order_iso_of_bijective
- \- *def* jacobson
- \- *def* is_local

Modified src/ring_theory/ideals.lean
- \+ *lemma* bot_is_maximal

Created src/ring_theory/jacobson.lean
- \+ *lemma* is_jacobson_iff_prime_eq
- \+ *lemma* is_jacobson_iff_Inf_maximal
- \+ *lemma* radical_eq_jacobson
- \+ *lemma* is_jacobson_iso
- \+ *theorem* is_jacobson_of_surjective
- \+ *def* is_jacobson

Created src/ring_theory/jacobson_ideal.lean
- \+ *lemma* le_jacobson
- \+ *lemma* jacobson_top
- \+ *lemma* jacobson_eq_bot
- \+ *lemma* jacobson.is_maximal
- \+ *lemma* jacobson_mono
- \+ *theorem* jacobson_eq_top_iff
- \+ *theorem* mem_jacobson_iff
- \+ *theorem* is_local_of_is_maximal_radical
- \+ *theorem* is_local.le_jacobson
- \+ *theorem* is_local.mem_jacobson_or_exists_inv
- \+ *theorem* is_primary_of_is_maximal_radical
- \+ *def* jacobson
- \+ *def* is_local



## [2020-07-21 01:55:48](https://github.com/leanprover-community/mathlib/commit/0322d89)
refactor(topology/algebra/monoid): changed topological_monoid into has_continuous_mul ([#3481](https://github.com/leanprover-community/mathlib/pull/3481))
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/normed_space/basic.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measurable_mul
- \+/\- *lemma* measurable.mul
- \+/\- *lemma* finset.measurable_prod

Modified src/topology/algebra/continuous_functions.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* submodule.eq_top_of_nonempty_interior'
- \+/\- *lemma* comp_add
- \+/\- *lemma* add_comp
- \+/\- *lemma* coe_coprod
- \+/\- *lemma* coprod_apply
- \- *lemma* submodule.eq_top_of_nonempty_interior
- \+/\- *def* coprod

Modified src/topology/algebra/monoid.lean
- \+/\- *lemma* continuous_pow

Modified src/topology/algebra/multilinear.lean


Modified src/topology/algebra/open_subgroup.lean
- \+/\- *lemma* is_closed

Modified src/topology/algebra/ring.lean


Modified src/topology/instances/ennreal.lean


Modified test/apply.lean




## [2020-07-21 01:05:11](https://github.com/leanprover-community/mathlib/commit/079d409)
chore(scripts): update nolints.txt ([#3483](https://github.com/leanprover-community/mathlib/pull/3483))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-21 01:05:09](https://github.com/leanprover-community/mathlib/commit/6721ddf)
refactor(ring_theory): remove unbundled leftovers in `ideal.quotient` ([#3467](https://github.com/leanprover-community/mathlib/pull/3467))
This PR aims to smooth some corners in the `ideal.quotient` namespace left by the move to bundled `ring_hom`s. The main irritation is the ambiguity between different ways to map `x : R` to the quotient ring: `quot.mk`, `quotient.mk`, `quotient.mk'`, `submodule.quotient.mk`, `ideal.quotient.mk` and `ideal.quotient.mk_hom`, which caused a lot of duplication and more awkward proofs.
The specific changes are:
 * delete function `ideal_quotient.mk`
 * rename ring hom `ideal.quotient.mk_hom` to `ideal.quotient.mk`
 * make new `ideal_quotient.mk` the `simp` normal form
 * delete obsolete `mk_eq_mk_hom`
 * delete obsolete `mk_...` `simp` lemmas (use `ring_hom.map_...` instead)
 * delete `quotient.map_mk` which was unused and had no lemmas (`ideal.map quotient.mk` is used elsewhere)
#### Estimated changes
Modified src/algebra/direct_limit.lean


Modified src/number_theory/basic.lean


Modified src/ring_theory/adjoin_root.lean
- \+/\- *def* mk

Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/ideals.lean
- \- *lemma* mk_one
- \- *lemma* mk_eq_mk_hom
- \- *lemma* mk_zero
- \- *lemma* mk_add
- \- *lemma* mk_neg
- \- *lemma* mk_sub
- \- *lemma* mk_pow
- \- *lemma* mk_prod
- \- *lemma* mk_sum
- \+ *theorem* mk_eq_mk
- \- *theorem* mk_mul
- \+/\- *def* mk
- \- *def* mk_hom
- \- *def* map_mk

Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/valuation/basic.lean




## [2020-07-21 01:05:07](https://github.com/leanprover-community/mathlib/commit/564ab02)
feat(category_theory/kernels): cokernel (image.ι f) ≅ cokernel f ([#3441](https://github.com/leanprover-community/mathlib/pull/3441))
#### Estimated changes
Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* cokernel_image_ι



## [2020-07-20 23:42:11](https://github.com/leanprover-community/mathlib/commit/32c082f)
fix(tactic/library_search): group monotone lemmas with le lemmas ([#3471](https://github.com/leanprover-community/mathlib/pull/3471))
This lets `library_search` use `monotone` lemmas to prove `\le` goals, and vice versa, resolving a problem people were experiencing in Patrick's exercises at LftCM2020:
```
import order.filter.basic
open filter
example {α β γ : Type*} {A : filter α} {B : filter β} {C : filter γ} {f : α → β} {g : β → γ}
  (hf : tendsto f A B) (hg : tendsto g B C) : tendsto (g ∘ f) A C :=
calc
map (g ∘ f) A = map g (map f A) : by library_search
          ... ≤ map g B         : by library_search!
          ... ≤ C               : by library_search!
```
#### Estimated changes
Modified src/tactic/suggest.lean


Created test/library_search/filter.lean




## [2020-07-20 22:17:29](https://github.com/leanprover-community/mathlib/commit/2915fae)
feat(data/finset/basic): Cardinality of intersection with singleton ([#3480](https://github.com/leanprover-community/mathlib/pull/3480))
Intersecting with a singleton produces a set of cardinality either 0 or 1.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* card_singleton_inter



## [2020-07-20 20:30:53](https://github.com/leanprover-community/mathlib/commit/1f74ddd)
feat(topology/local_extr): add lemmas on composition with continuous functions ([#3459](https://github.com/leanprover-community/mathlib/pull/3459))
#### Estimated changes
Modified src/topology/local_extr.lean
- \+ *lemma* is_local_min_on.comp_continuous_on
- \+ *lemma* is_local_max_on.comp_continuous_on
- \+ *lemma* is_local_extr_on.comp_continuous_on



## [2020-07-20 18:42:24](https://github.com/leanprover-community/mathlib/commit/7aa85c2)
fix(algebra/group/units): add missing coe lemmas to units ([#3472](https://github.com/leanprover-community/mathlib/pull/3472))
Per @kbuzzard's suggestions [here](https://leanprover-community.github.io/archive/stream/113489-new-members/topic/Shortening.20proof.20on.20product.20of.20units.20in.20Z.html[#204406319](https://github.com/leanprover-community/mathlib/pull/204406319)):
- Add a new lemma `coe_eq_one` to `units` API
- Tag `eq_iff` with `norm_cast`
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* coe_eq_one
- \+ *theorem* eq_iff

Modified src/data/int/basic.lean




## [2020-07-20 17:56:13](https://github.com/leanprover-community/mathlib/commit/b66d1be)
feat(data/multivariate/qpf): definition ([#3395](https://github.com/leanprover-community/mathlib/pull/3395))
Part of [#3317](https://github.com/leanprover-community/mathlib/pull/3317)
#### Estimated changes
Modified src/control/functor/multivariate.lean


Created src/data/pfunctor/multivariate/basic.lean
- \+ *lemma* const.get_map
- \+ *lemma* const.get_mk
- \+ *lemma* const.mk_get
- \+ *lemma* comp.get_map
- \+ *lemma* comp.get_mk
- \+ *lemma* comp.mk_get
- \+ *theorem* map_eq
- \+ *theorem* id_map
- \+ *theorem* comp_map
- \+ *theorem* liftp_iff
- \+ *theorem* liftp_iff'
- \+ *theorem* liftr_iff
- \+ *theorem* supp_eq
- \+ *def* obj
- \+ *def* map
- \+ *def* const
- \+ *def* const.mk
- \+ *def* const.get
- \+ *def* comp
- \+ *def* comp.mk
- \+ *def* comp.get
- \+ *def* drop
- \+ *def* last
- \+ *def* append_contents

Modified src/data/pfunctor/univariate/basic.lean
- \+ *def* W.head
- \+ *def* W.children

Created src/data/qpf/multivariate/basic.lean
- \+ *theorem* comp_map
- \+ *theorem* liftp_iff
- \+ *theorem* liftr_iff
- \+ *theorem* mem_supp
- \+ *theorem* supp_eq
- \+ *theorem* has_good_supp_iff
- \+ *theorem* supp_eq_of_is_uniform
- \+ *theorem* liftp_iff_of_is_uniform
- \+ *theorem* supp_map
- \+ *theorem* supp_preservation_iff_uniform
- \+ *theorem* supp_preservation_iff_liftp_preservation
- \+ *theorem* liftp_preservation_iff_uniform
- \+ *def* list
- \+ *def* multiset
- \+ *def* is_uniform
- \+ *def* liftp_preservation
- \+ *def* supp_preservation



## [2020-07-20 15:42:49](https://github.com/leanprover-community/mathlib/commit/78f438b)
feat(tactic/squeeze_*): improve suggestions ([#3431](https://github.com/leanprover-community/mathlib/pull/3431))
This makes this gives `squeeze_simp`, `squeeze_simpa` and `squeeze_dsimp` the `?` optional argument that indicates that we should consider all `simp` lemmas that are also `_refl_lemma`
#### Estimated changes
Modified src/tactic/squeeze.lean




## [2020-07-20 14:17:48](https://github.com/leanprover-community/mathlib/commit/d0df6b8)
feat(data/equiv/mul_add): refl_apply and trans_apply ([#3470](https://github.com/leanprover-community/mathlib/pull/3470))
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *theorem* refl_apply
- \+ *theorem* trans_apply



## [2020-07-20 14:17:46](https://github.com/leanprover-community/mathlib/commit/2994f1b)
feat(solve_by_elim): add tracing ([#3468](https://github.com/leanprover-community/mathlib/pull/3468))
When `solve_by_elim` fails, it now prints:
```
`solve_by_elim` failed.
Try `solve_by_elim { max_depth := N }` for a larger `N`,
or use `set_option trace.solve_by_elim true` to view the search.
```
and with `set_option trace.solve_by_elim true` we get messages like:
```
example (n m : ℕ) (f : ℕ → ℕ → Prop) (h : f n m) : ∃ p : ℕ × ℕ, f p.1 p.2 :=
begin
  repeat { fsplit },
  solve_by_elim*,
end
```
producing:
```
[solve_by_elim . ✅ `n` solves `⊢ ℕ`]
[solve_by_elim .. ✅ `n` solves `⊢ ℕ`]
[solve_by_elim ... ❌ failed to solve `⊢ f (n, n).fst (n, n).snd`]
[solve_by_elim .. ✅ `m` solves `⊢ ℕ`]
[solve_by_elim ... ✅ `h` solves `⊢ f (n, m).fst (n, m).snd`]
[solve_by_elim .... success!]
```
Fixed [#3063](https://github.com/leanprover-community/mathlib/pull/3063)
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/solve_by_elim.lean


Modified test/solve_by_elim.lean




## [2020-07-20 14:17:44](https://github.com/leanprover-community/mathlib/commit/38b95c8)
feat(set_theory/cardinal): simp lemmas about numerals ([#3450](https://github.com/leanprover-community/mathlib/pull/3450))
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+/\- *theorem* zero_lt_one
- \+/\- *theorem* one_lt_omega

Modified src/set_theory/ordinal.lean
- \+ *lemma* bit0_ne_zero
- \+ *lemma* bit1_ne_zero
- \+ *lemma* zero_lt_bit0
- \+ *lemma* zero_lt_bit1
- \+ *lemma* one_le_bit0
- \+ *lemma* one_le_bit1
- \+ *lemma* bit0_le_bit0
- \+ *lemma* bit0_le_bit1
- \+ *lemma* bit1_le_bit1
- \+ *lemma* bit1_le_bit0
- \+ *lemma* bit0_lt_bit0
- \+ *lemma* bit1_lt_bit0
- \+ *lemma* bit1_lt_bit1
- \+ *lemma* bit0_lt_bit1
- \+ *lemma* one_lt_two
- \+ *lemma* one_lt_bit0
- \+ *lemma* one_lt_bit1
- \+ *lemma* one_le_one
- \+ *theorem* bit0_eq_self
- \+ *theorem* bit0_lt_omega
- \+ *theorem* omega_le_bit0
- \+ *theorem* bit1_eq_self_iff
- \+ *theorem* bit1_lt_omega
- \+ *theorem* omega_le_bit1



## [2020-07-20 14:17:41](https://github.com/leanprover-community/mathlib/commit/9a92363)
feat(logic/basic): nonempty.some ([#3449](https://github.com/leanprover-community/mathlib/pull/3449))
Could we please have this? I've a number of times been annoyed by the difficulty of extracting an element from a `nonempty`.
(Criterion for alternative solutions: `library_search` solves `nonempty X -> X`.)
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* Exists.some_spec
- \- *theorem* forall_not_of_not_exists



## [2020-07-20 14:17:39](https://github.com/leanprover-community/mathlib/commit/469043f)
refactor(tactic/generalizes): reimplement generalizes' ([#3416](https://github.com/leanprover-community/mathlib/pull/3416))
The new implementation is somewhat simpler. It is inspired by the C++
function `generalize_indices` in `library/tactic/cases_tactic.cpp`,
which performs essentially the same construction.
The only non-internal change is the return type of `generalizes_intro`.
#### Estimated changes
Modified src/tactic/generalizes.lean




## [2020-07-20 12:54:51](https://github.com/leanprover-community/mathlib/commit/593b1bb)
feat(linear_algebra/affine_space): lemmas on affine spans ([#3453](https://github.com/leanprover-community/mathlib/pull/3453))
Add more lemmas on affine spans; in particular, that the points in an
`affine_span` are exactly the `affine_combination`s where the sum of
weights equals 1, provided the underlying ring is nontrivial.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *lemma* vector_span_empty
- \+ *lemma* span_points_nonempty
- \+ *lemma* weighted_vsub_of_point_indicator_subset
- \+ *lemma* weighted_vsub_empty
- \+ *lemma* weighted_vsub_indicator_subset
- \+ *lemma* affine_combination_apply
- \+ *lemma* affine_combination_of_eq_one_of_eq_zero
- \+ *lemma* affine_combination_indicator_subset
- \+ *lemma* vector_span_eq_span_vsub_set_left
- \+ *lemma* vector_span_eq_span_vsub_set_right
- \+ *lemma* vector_span_range_eq_span_range_vsub_left
- \+ *lemma* vector_span_range_eq_span_range_vsub_right
- \+ *lemma* affine_span_nonempty
- \+ *lemma* weighted_vsub_mem_vector_span
- \+ *lemma* affine_combination_mem_affine_span
- \+ *lemma* mem_vector_span_iff_eq_weighted_vsub
- \+ *lemma* eq_affine_combination_of_mem_affine_span
- \+ *lemma* mem_affine_span_iff_eq_affine_combination
- \- *lemma* span_points_nonempty_of_nonempty



## [2020-07-20 12:54:49](https://github.com/leanprover-community/mathlib/commit/65208ed)
refactor(data/polynomial/*): further refactors ([#3435](https://github.com/leanprover-community/mathlib/pull/3435))
There's a lot further to go, but I need to do other things for a while so will PR what I have so far.
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/basic.lean
- \+ *lemma* coeff_X_one
- \+ *lemma* coeff_X_zero
- \+ *lemma* coeff_X
- \+ *lemma* X_ne_zero

Modified src/data/polynomial/coeff.lean
- \+/\- *lemma* coeff_mul_X_zero
- \+ *lemma* coeff_X_mul_zero
- \+/\- *lemma* coeff_X_pow
- \+ *lemma* coeff_X_pow_self

Modified src/data/polynomial/degree.lean


Modified src/data/polynomial/degree/basic.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/div.lean


Modified src/data/polynomial/eval.lean


Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/identities.lean


Modified src/data/polynomial/induction.lean


Modified src/data/polynomial/monic.lean


Modified src/data/polynomial/monomial.lean
- \- *lemma* coeff_X_one
- \- *lemma* coeff_X_zero
- \- *lemma* coeff_X
- \- *lemma* X_ne_zero

Modified src/data/polynomial/ring_division.lean




## [2020-07-20 12:54:47](https://github.com/leanprover-community/mathlib/commit/cb06214)
feat(tactic/interactive_expr): always select all arguments ([#3384](https://github.com/leanprover-community/mathlib/pull/3384))
If you hover over `id id 0` in the widget (or really any function with more than one argument), then it is possible to select the partial application `id id`.  The popup will then only show the function `id` and the argument `id`, but not the second argument `0`.
This PR changes this behavior so that you can't select partial applications and always see all argument in the popup.
#### Estimated changes
Modified src/tactic/interactive_expr.lean




## [2020-07-20 11:25:58](https://github.com/leanprover-community/mathlib/commit/4a3755a)
chore(algebra/ring): fix a mistake ([#3469](https://github.com/leanprover-community/mathlib/pull/3469))
#### Estimated changes
Modified src/algebra/ring.lean




## [2020-07-20 09:41:20](https://github.com/leanprover-community/mathlib/commit/4dc0814)
feat (algebra/module): lemma about submodules ([#3466](https://github.com/leanprover-community/mathlib/pull/3466))
Add a 3-line lemma saying that a linear combination of elements of a submodule is still in that submodule.
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* sum_smul_mem



## [2020-07-20 08:16:52](https://github.com/leanprover-community/mathlib/commit/a400adb)
fix(tactic/library_search): 1 ≤ n goals in nat ([#3462](https://github.com/leanprover-community/mathlib/pull/3462))
Fixes [#3432](https://github.com/leanprover-community/mathlib/pull/3432).
This PR changes `library_search` and `suggest`:
1. instead of just selecting lemma with a single `name` as their head symbol, allows selecting from a `name_set`.
2. when the goal is `≤` on certain `ℕ` goals, set that `name_set` to `[has_lt.lt, has_le.le]`, for more flexible matching of inequality lemmas about `ℕ`
3. now successfully solves `theorem nonzero_gt_one (n : ℕ) : ¬ n = 0 → n ≥ 1 := by library_search!`
4. splits the `test/library_search/basic.lean` file into two parts, one which doesn't import `data.nat.basic`, for faster testing
#### Estimated changes
Modified src/tactic/suggest.lean


Modified test/library_search/basic.lean
- \- *lemma* zero_lt_one
- \+ *theorem* nonzero_gt_one
- \- *def* lt_one

Created test/library_search/nat.lean
- \+ *lemma* zero_lt_one
- \+ *def* lt_one



## [2020-07-20 06:04:37](https://github.com/leanprover-community/mathlib/commit/5080dd5)
feat(data/padics/padic_norm): lemmas about padic_val_nat ([#3230](https://github.com/leanprover-community/mathlib/pull/3230))
Collection of lemmas about `padic_val_nat`, culminating in `lemma prod_pow_prime_padic_val_nat : ∀ (n : nat) (s : n ≠ 0) (m : nat) (pr : n < m),  ∏ p in finset.filter nat.prime (finset.range m), pow p (padic_val_nat p n) = n`.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_multiset_count

Modified src/algebra/char_zero.lean
- \+ *theorem* cast_dvd_char_zero

Modified src/data/nat/basic.lean
- \+ *lemma* div_div_div_eq_div

Modified src/data/nat/cast.lean
- \+ *theorem* cast_dvd

Modified src/data/nat/gcd.lean
- \+ *theorem* coprime.coprime_div_left
- \+ *theorem* coprime.coprime_div_right

Modified src/data/nat/prime.lean
- \+ *lemma* factors_add_two
- \+ *theorem* prime_dvd_prime_iff_eq

Modified src/data/padics/padic_norm.lean
- \+ *lemma* one_le_padic_val_nat_of_dvd
- \+ *lemma* padic_val_nat_zero
- \+ *lemma* padic_val_nat_one
- \+ *lemma* padic_val_nat_of_not_dvd
- \+ *lemma* padic_val_nat_primes
- \+ *lemma* padic_val_nat_eq_factors_count
- \+ *lemma* prod_pow_prime_padic_val_nat



## [2020-07-20 05:06:14](https://github.com/leanprover-community/mathlib/commit/84d4ea7)
feat(data/nat/digits): a bigger number has more digits ([#3457](https://github.com/leanprover-community/mathlib/pull/3457))
#### Estimated changes
Modified src/data/nat/digits.lean
- \+ *lemma* digits_zero_zero
- \+ *lemma* digits_zero_succ
- \+ *lemma* digits_one
- \+/\- *lemma* digits_one_succ
- \+ *lemma* digits_len_le_digits_len_succ
- \+ *lemma* le_digits_len_le



## [2020-07-20 05:06:12](https://github.com/leanprover-community/mathlib/commit/792f541)
feat(field_theory/tower): tower law ([#3355](https://github.com/leanprover-community/mathlib/pull/3355))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_extend_by_one

Modified src/algebra/pointwise.lean
- \+ *theorem* range_smul_range

Modified src/data/finset/basic.lean
- \+ *theorem* subset_product

Created src/field_theory/tower.lean
- \+ *theorem* dim_mul_dim'
- \+ *theorem* dim_mul_dim
- \+ *theorem* trans
- \+ *theorem* findim_mul_findim

Modified src/linear_algebra/basis.lean
- \+ *theorem* linear_independent_iff''

Modified src/ring_theory/algebra_tower.lean
- \+/\- *theorem* of_algebra_map_eq
- \+/\- *theorem* algebra_map_eq
- \+/\- *theorem* algebra_map_apply
- \+ *theorem* algebra_map_smul
- \+ *theorem* smul_left_comm
- \+ *theorem* restrict_scalars'_top
- \+ *theorem* restrict_scalars'_injective
- \+ *theorem* restrict_scalars'_inj
- \+ *theorem* smul_mem_span_smul_of_mem
- \+ *theorem* smul_mem_span_smul
- \+ *theorem* smul_mem_span_smul'
- \+ *theorem* span_smul
- \+ *theorem* linear_independent_smul
- \+ *theorem* is_basis.smul
- \+ *def* restrict_scalars'



## [2020-07-20 03:39:14](https://github.com/leanprover-community/mathlib/commit/501aeb7)
feat(data/quot.lean): add lift_on_beta\_2 ([#3456](https://github.com/leanprover-community/mathlib/pull/3456))
This corresponds to `lift_on\_2` in `library/init/data/quot.lean` just as `lift_beta` and `lift_on_beta` correspond to `lift` and `lift_on`. It greatly simplifies quotient proofs but was, surprisingly, missing.
#### Estimated changes
Modified src/data/quot.lean
- \+ *theorem* quotient.lift_on_beta₂



## [2020-07-20 03:10:32](https://github.com/leanprover-community/mathlib/commit/697488c)
feat(tactic/unfold_cases): add unfold_cases tactic ([#3396](https://github.com/leanprover-community/mathlib/pull/3396))
#### Estimated changes
Modified src/tactic/default.lean


Created src/tactic/unfold_cases.lean


Created test/unfold_cases.lean
- \+ *def* balance_eqn_compiler
- \+ *def* balance_match
- \+ *def* foo
- \+ *def* bar
- \+ *def* baz



## [2020-07-20 00:16:06](https://github.com/leanprover-community/mathlib/commit/2975f93)
chore(tactic/interactive): move non-monadic part of `clean` to `expr.clean` ([#3461](https://github.com/leanprover-community/mathlib/pull/3461))
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/interactive.lean




## [2020-07-20 00:16:04](https://github.com/leanprover-community/mathlib/commit/db18144)
chore(order/bounded_lattice): add `is_compl.inf_left_eq_bot_iff` etc ([#3460](https://github.com/leanprover-community/mathlib/pull/3460))
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+ *lemma* inf_left_eq_bot_iff
- \+ *lemma* inf_right_eq_bot_iff
- \+ *lemma* disjoint_left_iff
- \+ *lemma* disjoint_right_iff

Modified src/topology/basic.lean




## [2020-07-19 21:18:59](https://github.com/leanprover-community/mathlib/commit/1bb3d19)
refactor(order/filter/basic): add class `filter.ne_bot` ([#3454](https://github.com/leanprover-community/mathlib/pull/3454))
This way Lean will f`≠ ⊥` in a few most common cases
(incl. `nhds_ne_bot`, `at_top_ne_bot`) automatically.
Other API changes:
* many lemmas now take `[ne_bot l]` instead of `(hl : l ≠ ⊥)`;
* some lemmas got `'` versions that take an explicit `(hl : ne_bot l)`;
* rename `ultrafilter_unique` to `is_ultrafilter.unique`;
* `cauchy_downwards` is now `cauchy.mono` (instance arg) and `cauchy.mono'` (explicit arg);
* `cauchy_map` is now `cauchy.map`;
* `cauchy_comap` is now `cauchy.comap`;
* `totally_bounded_closure` is now `totally_bounded.closure`;
* `totally_bounded_image` is now `totally_bounded.image`;
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/hofer.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nhds_within_is_unit_ne_bot
- \- *lemma* submodule.eq_top_of_nonempty_interior

Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/specific_limits.lean


Modified src/data/padics/hensel.lean


Modified src/data/real/hyperreal.lean
- \+/\- *lemma* coe_le_coe

Modified src/data/set/basic.lean
- \+ *lemma* nonempty_of_not_subset

Modified src/data/set/finite.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/dynamics/fixed_points/topology.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* at_top_ne_bot

Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean
- \+ *lemma* ne_bot.ne
- \+ *lemma* ne_bot.mono
- \+ *lemma* ne_bot_of_le
- \+/\- *lemma* nonempty_of_mem_sets
- \+ *lemma* ne_bot.nonempty_of_mem
- \+/\- *lemma* nonempty_of_ne_bot
- \+/\- *lemma* infi_ne_bot_of_directed'
- \+/\- *lemma* infi_ne_bot_iff_of_directed'
- \+/\- *lemma* infi_ne_bot_iff_of_directed
- \+/\- *lemma* principal_ne_bot_iff
- \+/\- *lemma* eventually_const
- \+/\- *lemma* eventually.frequently
- \+/\- *lemma* frequently_of_forall
- \+/\- *lemma* eventually.exists
- \+/\- *lemma* frequently_true_iff_ne_bot
- \+/\- *lemma* frequently_const
- \+/\- *lemma* frequently_or_distrib_left
- \+/\- *lemma* frequently_or_distrib_right
- \+/\- *lemma* frequently_imp_distrib_left
- \+/\- *lemma* frequently_imp_distrib_right
- \+/\- *lemma* comap_ne_bot_iff
- \+/\- *lemma* comap_ne_bot
- \+ *lemma* ne_bot.comap_of_range_mem
- \+ *lemma* ne_bot.comap_of_surj
- \+ *lemma* ne_bot.comap_of_image_mem
- \+/\- *lemma* map_ne_bot_iff
- \+ *lemma* ne_bot.map
- \+/\- *lemma* tendsto.ne_bot
- \+/\- *lemma* prod_ne_bot
- \+ *lemma* ne_bot.prod
- \- *lemma* comap_ne_bot_of_range_mem
- \- *lemma* comap_ne_bot_of_surj
- \- *lemma* comap_ne_bot_of_image_mem
- \- *lemma* map_ne_bot
- \- *lemma* pure_ne_bot
- \+ *def* ne_bot

Modified src/order/filter/cofinite.lean
- \- *lemma* cofinite_ne_bot

Modified src/order/filter/filter_product.lean


Modified src/order/filter/germ.lean
- \+/\- *lemma* const_eventually_eq'
- \+/\- *lemma* const_eventually_eq
- \+/\- *lemma* const_inj
- \+/\- *lemma* lift_pred_const_iff
- \+/\- *lemma* lift_rel_const_iff
- \+/\- *lemma* const_le_iff

Modified src/order/filter/lift.lean
- \+/\- *lemma* lift_ne_bot_iff
- \+/\- *lemma* lift'_ne_bot_iff

Modified src/order/filter/pointwise.lean
- \+ *lemma* ne_bot.mul
- \- *lemma* mul_ne_bot

Modified src/order/filter/ultrafilter.lean
- \+ *lemma* is_ultrafilter.unique
- \+/\- *lemma* le_of_ultrafilter
- \+/\- *lemma* exists_ultrafilter
- \+/\- *lemma* ultrafilter_of_spec
- \+/\- *lemma* ultrafilter_ultrafilter_of
- \+ *lemma* ultrafilter_ultrafilter_of'
- \+/\- *lemma* hyperfilter_ne_bot
- \+/\- *lemma* exists_ultrafilter_iff
- \- *lemma* ultrafilter_unique
- \+/\- *def* is_ultrafilter

Modified src/order/liminf_limsup.lean
- \+/\- *lemma* is_cobounded_of_is_bounded
- \+/\- *lemma* limsup_const
- \+/\- *lemma* liminf_const
- \+/\- *lemma* liminf_le_limsup
- \+/\- *theorem* Liminf_le_Limsup

Modified src/order/zorn.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* submodule.eq_top_of_nonempty_interior
- \- *lemma* submodule.eq_top_of_nonempty_interior'

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* le_of_tendsto_of_tendsto
- \+/\- *lemma* le_of_tendsto_of_tendsto'
- \+/\- *lemma* ge_of_tendsto
- \+/\- *lemma* ge_of_tendsto'
- \+/\- *theorem* Liminf_eq_of_le_nhds
- \+/\- *theorem* Limsup_eq_of_le_nhds
- \+/\- *theorem* filter.tendsto.limsup_eq
- \+/\- *theorem* filter.tendsto.liminf_eq

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean
- \+ *lemma* cluster_pt.ne_bot
- \+/\- *lemma* cluster_pt.of_le_nhds
- \+ *lemma* cluster_pt.of_le_nhds'
- \- *lemma* nhds_ne_bot
- \+/\- *def* cluster_pt

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/continuous_on.lean


Modified src/topology/dense_embedding.lean
- \+ *lemma* dense_range.nhds_within_ne_bot
- \+/\- *lemma* comap_nhds_ne_bot

Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/cau_seq_filter.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/order.lean


Modified src/topology/separation.lean
- \+/\- *lemma* eq_of_nhds_ne_bot
- \+/\- *lemma* t2_iff_nhds
- \+ *lemma* tendsto_nhds_unique'
- \+/\- *lemma* Lim_eq

Modified src/topology/sequences.lean


Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean
- \+/\- *lemma* is_compact.inter_right
- \+/\- *lemma* is_compact.prod
- \+/\- *def* is_compact

Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy_map_iff'
- \+ *lemma* cauchy.mono
- \+ *lemma* cauchy.mono'
- \+ *lemma* cauchy.map
- \+ *lemma* cauchy.comap
- \+ *lemma* cauchy.comap'
- \+/\- *lemma* cauchy_iff_exists_le_nhds
- \+/\- *lemma* cauchy_map_iff_exists_tendsto
- \+ *lemma* totally_bounded.closure
- \+ *lemma* totally_bounded.image
- \- *lemma* cauchy_downwards
- \- *lemma* cauchy_map
- \- *lemma* cauchy_comap
- \- *lemma* totally_bounded_closure
- \- *lemma* totally_bounded_image
- \+/\- *def* cauchy
- \+/\- *def* seq

Modified src/topology/uniform_space/compact_separated.lean


Modified src/topology/uniform_space/complete_separated.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/pi.lean


Modified src/topology/uniform_space/uniform_convergence.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-07-19 21:18:58](https://github.com/leanprover-community/mathlib/commit/953ab3a)
feat(geometry/manifold/charted_space): open subset of a manifold is a manifold ([#3442](https://github.com/leanprover-community/mathlib/pull/3442))
An open subset of a charted space is naturally a charted space.  If the charted space has structure groupoid `G` (with `G` closed under restriction), then the open subset does also.
Most of the work is in `topology/local_homeomorph`, where it is proved that a local homeomorphism whose source is `univ` is an open embedding, and conversely.
#### Estimated changes
Modified src/geometry/manifold/charted_space.lean


Modified src/topology/local_homeomorph.lean
- \+ *lemma* source_preimage_target
- \+ *lemma* image_open_of_open'
- \+ *lemma* to_open_embedding
- \+ *lemma* to_local_equiv_coe
- \+ *lemma* to_local_equiv_source
- \+ *lemma* to_local_equiv_target
- \+ *lemma* open_target
- \+ *lemma* continuous_inv_fun
- \+ *lemma* to_local_homeomorph_coe
- \+ *lemma* source
- \+ *lemma* target
- \+ *lemma* local_homeomorph_subtype_coe_coe
- \+ *lemma* local_homeomorph_subtype_coe_source
- \+ *lemma* local_homeomorph_subtype_coe_target
- \+ *lemma* subtype_restr_def
- \+ *lemma* subtype_restr_coe
- \+ *lemma* subtype_restr_source
- \+ *lemma* subtype_restr_symm_trans_subtype_restr



## [2020-07-19 16:12:23](https://github.com/leanprover-community/mathlib/commit/bc278b7)
fix(tactic/apply_rules): fix stuck metavariable bug ([#3451](https://github.com/leanprover-community/mathlib/pull/3451))
`apply_rules` had the same bug `solve_by_elim` used to suffer from: applying a lemma once would fix its arguments, and prevent it from being applied a second time with different arguments.
This essentially ports over the fix from `solve_by_elim`: rather than carrying around a `list expr`, we carry a `list (tactic expr)` and generate on demand.
#### Estimated changes
Modified src/analysis/analytic/composition.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/tactic/core.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Created test/apply_rules.lean


Modified test/tactics.lean




## [2020-07-19 15:29:48](https://github.com/leanprover-community/mathlib/commit/9b0435a)
fix(tactic/linarith): find correct zero_lt_one ([#3455](https://github.com/leanprover-community/mathlib/pull/3455))
Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/linarith.20and.20ordinal.20file
#### Estimated changes
Modified src/tactic/linarith/verification.lean


Modified test/linarith.lean
- \+ *lemma* zero_lt_one
- \+ *lemma* works



## [2020-07-19 14:44:28](https://github.com/leanprover-community/mathlib/commit/47ea2a6)
feat(topology, analysis) : add lemmas about `has_neg.neg` (preliminaries for L'Hopital's rule) ([#3392](https://github.com/leanprover-community/mathlib/pull/3392))
This PR contains a few lemmas about the `has_neg.neg` function, such as : 
- its limit along `at_top` and `at_bot`
- its limit along `nhds a`, `nhds_within a (Ioi a)` and similar filters
- its differentiability and derivative
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_within.neg
- \+ *lemma* deriv.neg
- \+ *lemma* deriv.neg'
- \+/\- *lemma* deriv_neg
- \+/\- *lemma* deriv_neg'
- \+ *lemma* deriv_neg''
- \+/\- *lemma* deriv_within_neg
- \+ *lemma* differentiable_neg
- \+ *lemma* differentiable_on_neg
- \+ *theorem* has_deriv_at_filter_neg
- \+ *theorem* has_deriv_within_at_neg
- \+ *theorem* has_deriv_at_neg
- \+ *theorem* has_deriv_at_neg'
- \+ *theorem* has_strict_deriv_at_neg

Modified src/analysis/calculus/mean_value.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* eventually_at_top
- \+ *lemma* eventually_ge_at_top
- \+/\- *lemma* tendsto_at_top_pure
- \+/\- *lemma* eventually.exists_forall_of_at_top
- \+/\- *lemma* frequently_at_top
- \+/\- *lemma* frequently_at_top'
- \+/\- *lemma* frequently.forall_exists_of_at_top
- \+ *lemma* tendsto_at_bot
- \+ *lemma* tendsto_at_bot'
- \+/\- *lemma* tendsto_at_top_embedding
- \+/\- *lemma* tendsto_at_top_at_bot
- \+ *lemma* tendsto_at_bot_at_top
- \+ *lemma* tendsto_at_bot_at_bot
- \+/\- *lemma* tendsto_at_top_at_top_of_monotone'
- \+/\- *lemma* unbounded_of_tendsto_at_top
- \+/\- *lemma* tendsto_at_top_of_monotone_of_filter
- \+/\- *lemma* tendsto_at_top_of_monotone_of_subseq
- \+ *lemma* tendsto_neg_at_top_at_bot
- \+ *lemma* tendsto_neg_at_bot_at_top

Modified src/topology/algebra/group.lean
- \+ *lemma* continuous_on_inv
- \+ *lemma* tendsto_inv

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_inv_nhds_within_Ioi
- \+ *lemma* tendsto_inv_nhds_within_Iio
- \+ *lemma* tendsto_inv_nhds_within_Ioi_inv
- \+ *lemma* tendsto_inv_nhds_within_Iio_inv



## [2020-07-19 14:13:17](https://github.com/leanprover-community/mathlib/commit/8187551)
feat(topology/algebra/continuous_functions): algebra structure over continuous functions ([#3383](https://github.com/leanprover-community/mathlib/pull/3383))
#### Estimated changes
Modified src/topology/algebra/continuous_functions.lean
- \+ *def* C



## [2020-07-19 09:29:38](https://github.com/leanprover-community/mathlib/commit/5228d55)
feat(linear_algebra/basic): add span_zero ([#3306](https://github.com/leanprover-community/mathlib/pull/3306))
`simp` now proves span_zero for both submodules and ideals
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *lemma* span_singleton_eq_bot
- \+ *lemma* span_zero

Modified src/linear_algebra/basis.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideals.lean
- \+/\- *lemma* span_singleton_eq_bot
- \+ *lemma* span_zero



## [2020-07-19 06:24:31](https://github.com/leanprover-community/mathlib/commit/3354476)
feat(data/indicator_function): more lemmas ([#3424](https://github.com/leanprover-community/mathlib/pull/3424))
Add some lemmas of use when using `set.indicator` to manipulate
functions involved in summations.
#### Estimated changes
Modified src/data/indicator_function.lean
- \+ *lemma* mem_of_indicator_ne_zero
- \+ *lemma* sum_indicator_subset_of_eq_zero
- \+ *lemma* sum_indicator_subset



## [2020-07-19 05:43:15](https://github.com/leanprover-community/mathlib/commit/8312419)
refactor(data/polynomial): remove has_coe_to_fun, and @[reducible] on monomial ([#3420](https://github.com/leanprover-community/mathlib/pull/3420))
I'm going to refactor in stages, trying to clean up some of the cruftier aspects of `data/polynomial/*`.
This PR:
1. removes the `has_coe_to_fun` on polynomial
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* monomial_mul_monomial
- \+ *lemma* coeff_monomial
- \+/\- *lemma* coeff_one_zero
- \- *lemma* apply_eq_coeff
- \- *def* coeff_coe_to_fun

Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/degree/basic.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/div.lean
- \+ *lemma* apply_eq_coeff
- \+ *def* coeff_coe_to_fun

Modified src/data/polynomial/eval.lean


Modified src/data/polynomial/monomial.lean
- \+/\- *lemma* coeff_X_one
- \+/\- *lemma* coeff_X_zero
- \+/\- *lemma* coeff_X
- \+/\- *lemma* coeff_C_zero

Modified src/ring_theory/polynomial_algebra.lean




## [2020-07-19 04:53:42](https://github.com/leanprover-community/mathlib/commit/eca55c9)
feat(category_theory/equivalence): injectivity simp lemmas for equivalences ([#3437](https://github.com/leanprover-community/mathlib/pull/3437))
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+ *lemma* functor_map_inj_iff
- \+ *lemma* inverse_map_inj_iff



## [2020-07-19 04:53:40](https://github.com/leanprover-community/mathlib/commit/eb68f4c)
feat (linear_algebra/matrix): make diag and trace compatible with semirings ([#3433](https://github.com/leanprover-community/mathlib/pull/3433))
changes ring and related instances to semiring etc. in requirements for matrix.diag and matrix.trace
#### Estimated changes
Modified src/linear_algebra/matrix.lean
- \+/\- *def* diag
- \+/\- *def* trace



## [2020-07-19 04:53:38](https://github.com/leanprover-community/mathlib/commit/e6bfe18)
feat(topology/algebra/module): pi and proj for CLM ([#3430](https://github.com/leanprover-community/mathlib/pull/3430))
#### Estimated changes
Modified src/topology/algebra/module.lean
- \+ *lemma* pi_apply
- \+ *lemma* pi_eq_zero
- \+ *lemma* pi_zero
- \+ *lemma* pi_comp
- \+ *lemma* proj_apply
- \+ *lemma* proj_pi
- \+ *lemma* infi_ker_proj
- \+ *def* pi
- \+ *def* proj
- \+ *def* infi_ker_proj_equiv



## [2020-07-19 03:42:37](https://github.com/leanprover-community/mathlib/commit/f83cf57)
feat(data/equiv/mul_add): minor lemmas ([#3447](https://github.com/leanprover-community/mathlib/pull/3447))
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *lemma* apply_inv_self
- \+ *lemma* inv_apply_self



## [2020-07-19 03:42:35](https://github.com/leanprover-community/mathlib/commit/61bd966)
feat(data/list/basic): add concat lemmas ([#3445](https://github.com/leanprover-community/mathlib/pull/3445))
The first two are taken after the `head_eq_of_cons_eq` and `tail_eq_of_cons_eq` lemmas further up in the file.
The third, `reverse_concat`, is like `reverse_cons'` but with the `::` and `concat` swapped.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* init_eq_of_concat_eq
- \+ *theorem* last_eq_of_concat_eq
- \+ *theorem* reverse_concat



## [2020-07-19 03:15:24](https://github.com/leanprover-community/mathlib/commit/91ca927)
feat(geometry/manifold/local_invariant_properties):  local structomorphism is `local_invariant_prop` ([#3434](https://github.com/leanprover-community/mathlib/pull/3434))
For a groupoid `G`, define the property of being a local structomorphism; prove that if `G` is closed under restriction then this property satisfies `local_invariant_prop` (i.e., is local and `G`-invariant).
#### Estimated changes
Modified src/geometry/manifold/charted_space.lean
- \+ *lemma* closed_under_restriction'

Modified src/geometry/manifold/local_invariant_properties.lean
- \+ *lemma* is_local_structomorph_within_at_local_invariant_prop
- \+ *def* is_local_structomorph_within_at



## [2020-07-18 16:49:37](https://github.com/leanprover-community/mathlib/commit/4760a33)
feat(algebra/polynomial, data/polynomial): lemmas about monic polynomials ([#3402](https://github.com/leanprover-community/mathlib/pull/3402))
#### Estimated changes
Modified src/algebra/char_p.lean
- \+ *theorem* add_pow_char_of_commute

Deleted src/algebra/polynomial/basic.lean
- \- *lemma* coe_aeval_eq_eval
- \- *lemma* coeff_zero_eq_aeval_zero
- \- *lemma* leading_coeff_hom_apply
- \- *def* leading_coeff_hom

Modified src/algebra/polynomial/big_operators.lean
- \+ *lemma* nat_degree_prod'
- \+ *lemma* nat_degree_prod_of_monic
- \+ *lemma* prod_X_sub_C_next_coeff
- \+ *lemma* prod_X_sub_C_coeff_card_pred
- \+ *lemma* nat_degree_prod
- \- *lemma* nat_degree_prod_eq'
- \- *lemma* monic_prod_of_monic
- \- *lemma* nat_degree_prod_eq_of_monic
- \- *lemma* nat_degree_prod_eq

Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* coe_aeval_eq_eval
- \+ *lemma* coeff_zero_eq_aeval_zero
- \+ *lemma* pow_comp

Modified src/data/polynomial/degree.lean
- \+ *lemma* degree_mul'
- \+ *lemma* nat_degree_mul'
- \+ *lemma* degree_pow'
- \+ *lemma* nat_degree_pow'
- \+ *lemma* next_coeff_X_sub_C
- \+ *lemma* degree_mul
- \+ *lemma* degree_pow
- \+ *lemma* leading_coeff_mul
- \+ *lemma* leading_coeff_hom_apply
- \+ *lemma* leading_coeff_pow
- \- *lemma* degree_mul_eq'
- \- *lemma* nat_degree_mul_eq'
- \- *lemma* degree_pow_eq'
- \- *lemma* nat_degree_pow_eq'
- \+ *def* leading_coeff_hom

Modified src/data/polynomial/degree/basic.lean
- \+ *lemma* next_coeff_C_eq_zero
- \+ *lemma* next_coeff_of_pos_nat_degree
- \+ *def* next_coeff

Modified src/data/polynomial/div.lean


Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/monic.lean
- \+ *lemma* monic_prod_of_monic
- \+ *lemma* coeff_nat_degree
- \+ *lemma* degree_eq_zero_iff_eq_one
- \+ *lemma* nat_degree_mul
- \+ *lemma* next_coeff_mul
- \+ *lemma* next_coeff_prod

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* nat_degree_mul
- \+ *lemma* nat_degree_pow
- \- *lemma* degree_mul_eq
- \- *lemma* degree_pow_eq
- \- *lemma* leading_coeff_mul
- \- *lemma* leading_coeff_pow
- \- *lemma* nat_degree_mul_eq
- \- *lemma* nat_degree_pow_eq

Modified src/linear_algebra/lagrange.lean


Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/polynomial/basic.lean




## [2020-07-18 16:19:16](https://github.com/leanprover-community/mathlib/commit/37cf166)
feat(data/complex/exponential): added @[mono] tag to exp_le_exp and exp_lt_exp ([#3318](https://github.com/leanprover-community/mathlib/pull/3318))
added @[mono] tag to exp_le_exp and exp_lt_exp.
#### Estimated changes
Modified src/data/complex/exponential.lean
- \+ *lemma* exp_monotone



## [2020-07-18 12:28:11](https://github.com/leanprover-community/mathlib/commit/e3e0aa0)
chore(linear_algebra/direct_sum_module): add dosctrings ([#3418](https://github.com/leanprover-community/mathlib/pull/3418))
#### Estimated changes
Modified src/linear_algebra/direct_sum_module.lean
- \+/\- *def* lmk



## [2020-07-18 11:26:57](https://github.com/leanprover-community/mathlib/commit/21a1683)
feat(data/finsupp): sums over on_finset ([#3427](https://github.com/leanprover-community/mathlib/pull/3427))
There aren't many lemmas about `finsupp.on_finset`.  Add one that's
useful for manipulating sums over `on_finset`.
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* on_finset_sum



## [2020-07-18 11:26:55](https://github.com/leanprover-community/mathlib/commit/4767b30)
feat(algebra/big_operators): more general prod_insert_one ([#3426](https://github.com/leanprover-community/mathlib/pull/3426))
I found I had a use for a slightly more general version of
`prod_insert_one` / `sum_insert_zero`.  Add that version and use it in
the proof of `prod_insert_one`.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_insert_of_eq_one_if_not_mem
- \+/\- *lemma* prod_insert_one



## [2020-07-18 10:34:10](https://github.com/leanprover-community/mathlib/commit/f81568a)
feat(group_theory/semidirect_product): mk_eq_inl_mul_inr and hom_ext ([#3408](https://github.com/leanprover-community/mathlib/pull/3408))
#### Estimated changes
Modified src/group_theory/semidirect_product.lean
- \+ *lemma* mk_eq_inl_mul_inr
- \+ *lemma* hom_ext



## [2020-07-18 09:27:48](https://github.com/leanprover-community/mathlib/commit/907147a)
feat(linear_algebra/matrix): define equivalences for reindexing matrices with equivalent types ([#3409](https://github.com/leanprover-community/mathlib/pull/3409))
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+ *lemma* matrix.reindex_lie_equiv_apply
- \+ *lemma* matrix.reindex_lie_equiv_symm_apply
- \+ *def* matrix.reindex_lie_equiv

Modified src/linear_algebra/matrix.lean
- \+ *lemma* reindex_apply
- \+ *lemma* reindex_symm_apply
- \+ *lemma* reindex_linear_equiv_apply
- \+ *lemma* reindex_linear_equiv_symm_apply
- \+ *lemma* reindex_mul
- \+ *lemma* reindex_alg_equiv_apply
- \+ *lemma* reindex_alg_equiv_symm_apply
- \+ *def* reindex
- \+ *def* reindex_linear_equiv
- \+ *def* reindex_alg_equiv



## [2020-07-18 06:56:08](https://github.com/leanprover-community/mathlib/commit/06823d6)
chore(*): add copyright header, cleanup imports ([#3440](https://github.com/leanprover-community/mathlib/pull/3440))
Fixes
1. a missing copyright header
2. moves `tactic.obviously` into the imports of `tactic.basic`, so everyone has `tidy` and `obviously` available.
3. removes a few redundant imports
#### Estimated changes
Modified src/algebra/group/basic.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/limits/limits.lean


Modified src/data/equiv/basic.lean


Modified src/order/boolean_algebra.lean


Modified src/tactic/basic.lean


Modified src/tactic/core.lean


Modified src/tactic/ext.lean


Modified src/tactic/obviously.lean


Modified src/tactic/pi_instances.lean




## [2020-07-17 14:49:16](https://github.com/leanprover-community/mathlib/commit/9616f44)
feat(algebra/ordered_group): decidable_linear_order for multiplicative and additive ([#3429](https://github.com/leanprover-community/mathlib/pull/3429))
#### Estimated changes
Modified src/algebra/ordered_group.lean




## [2020-07-17 14:49:14](https://github.com/leanprover-community/mathlib/commit/3acf220)
feat(group_theory/semidirect_product): inl_aut_inv ([#3410](https://github.com/leanprover-community/mathlib/pull/3410))
#### Estimated changes
Modified src/group_theory/semidirect_product.lean
- \+ *lemma* inl_aut_inv
- \+/\- *lemma* inl_left_mul_inr_right



## [2020-07-17 13:47:53](https://github.com/leanprover-community/mathlib/commit/8999625)
chore(*): more import reduction ([#3421](https://github.com/leanprover-community/mathlib/pull/3421))
Another import reduction PR. (This is by hand, not just removing transitive imports.)
Mostly this one is from staring at `leanproject import-graph --to data.polynomial.basic` and wondering about weird edges in the graph.
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/algebra/polynomial/big_operators.lean


Modified src/combinatorics/composition.lean


Modified src/data/fintype/card.lean


Modified src/data/int/sqrt.lean


Modified src/data/nat/digits.lean


Modified src/data/polynomial/ring_division.lean


Modified src/data/rat/basic.lean


Modified src/data/rat/order.lean
- \- *theorem* sqrt_eq
- \- *theorem* exists_mul_self
- \- *theorem* sqrt_nonneg
- \- *def* sqrt

Created src/data/rat/sqrt.lean
- \+ *theorem* sqrt_eq
- \+ *theorem* exists_mul_self
- \+ *theorem* sqrt_nonneg
- \+ *def* sqrt

Modified src/data/real/irrational.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/subgroup.lean


Modified src/tactic/norm_num.lean




## [2020-07-17 12:38:22](https://github.com/leanprover-community/mathlib/commit/207a1d4)
feat(data/finset/basic): finset of empty type ([#3425](https://github.com/leanprover-community/mathlib/pull/3425))
In a proof working by cases for whether a type is nonempty, I found I
had a use for the result that a `finset` of an empty type is empty.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* eq_empty_of_not_nonempty



## [2020-07-17 09:26:56](https://github.com/leanprover-community/mathlib/commit/4a6b716)
fix(tactic/nlinarith): stop nlinarith failing in the presence of squares when there is no order ([#3417](https://github.com/leanprover-community/mathlib/pull/3417))
As reported by Heather Macbeth at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/app_builder_exception.20in.20.60nlinarith.60/near/204138256
#### Estimated changes
Modified src/tactic/linarith/preprocessing.lean


Modified test/linarith.lean
- \+ *lemma* abs_nonneg'



## [2020-07-17 07:23:09](https://github.com/leanprover-community/mathlib/commit/7d31f77)
refactor(measure_theory/*): big refactor ([#3373](https://github.com/leanprover-community/mathlib/pull/3373))
Big refactor of integrals, fixes [#3084](https://github.com/leanprover-community/mathlib/pull/3084) 
Make `integral (f : α → E) (μ : measure α)` the main definition, and use `notation` for other integrals
(over a set and/or w.r.t. the canonical measure `volume`).
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* coe_injective

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* extend_unique

Modified src/data/indicator_function.lean
- \+ *lemma* indicator_le'
- \+ *lemma* indicator_le_self'
- \+ *lemma* indicator_le_self
- \+ *lemma* indicator_le
- \+ *lemma* add_monoid_hom.map_indicator

Modified src/data/real/ennreal.lean
- \+ *lemma* coe_indicator

Modified src/data/real/nnreal.lean
- \+ *lemma* coe_indicator

Modified src/data/set/basic.lean
- \- *lemma* if_preimage
- \+ *theorem* set_of_true
- \- *theorem* univ_def

Modified src/data/set/function.lean
- \+ *lemma* piecewise_preimage

Modified src/measure_theory/ae_eq_fun.lean
- \+/\- *lemma* quot_mk_eq_mk
- \+ *lemma* quotient_out'_eq_coe_fn
- \+/\- *lemma* mk_eq_mk
- \+ *lemma* mk_coe_fn
- \+/\- *lemma* ext
- \+ *lemma* coe_fn_mk
- \+ *lemma* induction_on
- \+ *lemma* induction_on₂
- \+ *lemma* induction_on₃
- \+/\- *lemma* comp_mk
- \+ *lemma* comp_eq_mk
- \+ *lemma* coe_fn_comp
- \+ *lemma* pair_mk_mk
- \+ *lemma* pair_eq_mk
- \+ *lemma* coe_fn_pair
- \+ *lemma* comp₂_eq_pair
- \+ *lemma* comp₂_eq_mk
- \+ *lemma* coe_fn_comp₂
- \+ *lemma* mk_to_germ
- \+ *lemma* to_germ_eq
- \+ *lemma* to_germ_injective
- \+ *lemma* comp_to_germ
- \+ *lemma* comp₂_to_germ
- \+/\- *lemma* lift_rel_mk_mk
- \+ *lemma* lift_rel_iff_coe_fn
- \+/\- *lemma* mk_le_mk
- \+ *lemma* coe_fn_le
- \+ *lemma* coe_fn_const
- \+/\- *lemma* one_def
- \+ *lemma* coe_fn_one
- \+ *lemma* one_to_germ
- \+ *lemma* mk_mul_mk
- \+ *lemma* coe_fn_mul
- \+ *lemma* mul_to_germ
- \+ *lemma* inv_mk
- \+ *lemma* coe_fn_inv
- \+ *lemma* inv_to_germ
- \+ *lemma* mk_sub
- \+ *lemma* coe_fn_sub
- \+ *lemma* coe_fn_smul
- \+ *lemma* smul_to_germ
- \+ *lemma* lintegral_mk
- \+ *lemma* lintegral_coe_fn
- \+ *lemma* lintegral_zero
- \+ *lemma* lintegral_eq_zero_iff
- \+ *lemma* lintegral_add
- \+ *lemma* lintegral_mono
- \+ *lemma* coe_fn_edist
- \+/\- *lemma* edist_mk_mk
- \+ *lemma* edist_eq_coe
- \+ *lemma* edist_zero_eq_coe
- \+ *lemma* edist_eq_coe'
- \+ *lemma* edist_add_right
- \+/\- *lemma* edist_smul
- \+ *lemma* pos_part_mk
- \+ *lemma* coe_fn_pos_part
- \- *lemma* self_eq_mk
- \- *lemma* all_ae_mk_to_fun
- \- *lemma* comp_eq_mk_to_fun
- \- *lemma* comp_to_fun
- \- *lemma* comp₂_eq_mk_to_fun
- \- *lemma* comp₂_to_fun
- \- *lemma* lift_rel_iff_to_fun
- \- *lemma* le_iff_to_fun_le
- \- *lemma* const_to_fun
- \- *lemma* zero_def
- \- *lemma* zero_to_fun
- \- *lemma* one_to_fun
- \- *lemma* mk_add_mk
- \- *lemma* add_to_fun
- \- *lemma* neg_mk
- \- *lemma* neg_to_fun
- \- *lemma* mk_sub_mk
- \- *lemma* sub_to_fun
- \- *lemma* smul_to_fun
- \- *lemma* eintegral_mk
- \- *lemma* eintegral_to_fun
- \- *lemma* eintegral_zero
- \- *lemma* eintegral_eq_zero_iff
- \- *lemma* eintegral_add
- \- *lemma* eintegral_le_eintegral
- \- *lemma* comp_edist_to_fun
- \- *lemma* comp_edist_self
- \- *lemma* edist_to_fun
- \- *lemma* edist_zero_to_fun
- \- *lemma* edist_to_fun'
- \- *lemma* edist_eq_add_add
- \- *lemma* pos_part_to_fun
- \+ *def* measure.ae_eq_setoid
- \+/\- *def* ae_eq_fun
- \+/\- *def* mk
- \+/\- *def* comp
- \+ *def* pair
- \+/\- *def* comp₂
- \+ *def* to_germ
- \+/\- *def* lift_pred
- \+/\- *def* lift_rel
- \+/\- *def* const
- \+ *def* lintegral
- \+/\- *def* pos_part
- \- *def* eintegral
- \- *def* comp_edist

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* integrable_iff_fin_meas_supp
- \+ *lemma* fin_meas_supp.integrable
- \+/\- *lemma* integrable_pair
- \+ *lemma* integral_eq_sum_filter
- \+ *lemma* map_integral
- \+ *lemma* integral_eq_lintegral'
- \+/\- *lemma* integral_congr
- \+/\- *lemma* integral_eq_lintegral
- \+/\- *lemma* integral_add
- \+/\- *lemma* integral_neg
- \+/\- *lemma* integral_sub
- \+/\- *lemma* integral_smul
- \+/\- *lemma* norm_integral_le_integral_norm
- \+ *lemma* integral_add_meas
- \+ *lemma* coe_coe
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* edist_eq
- \+/\- *lemma* dist_eq
- \+/\- *lemma* norm_eq
- \+/\- *lemma* norm_eq'
- \+/\- *lemma* coe_smul
- \+/\- *lemma* of_simple_func_eq_of_fun
- \+/\- *lemma* of_simple_func_eq_mk
- \+/\- *lemma* of_simple_func_zero
- \+/\- *lemma* of_simple_func_add
- \+/\- *lemma* of_simple_func_neg
- \+/\- *lemma* of_simple_func_sub
- \+/\- *lemma* of_simple_func_smul
- \+/\- *lemma* norm_of_simple_func
- \+/\- *lemma* of_simple_func_to_simple_func
- \+/\- *lemma* to_simple_func_of_simple_func
- \+/\- *lemma* to_simple_func_eq_to_fun
- \+/\- *lemma* zero_to_simple_func
- \+/\- *lemma* add_to_simple_func
- \+/\- *lemma* neg_to_simple_func
- \+/\- *lemma* sub_to_simple_func
- \+/\- *lemma* smul_to_simple_func
- \+/\- *lemma* lintegral_edist_to_simple_func_lt_top
- \+/\- *lemma* dist_to_simple_func
- \+/\- *lemma* norm_to_simple_func
- \+ *lemma* norm_eq_integral
- \+/\- *lemma* coe_pos_part
- \+/\- *lemma* coe_neg_part
- \+ *lemma* integral_eq_integral
- \+/\- *lemma* norm_integral_le_norm
- \+/\- *lemma* pos_part_to_simple_func
- \+/\- *lemma* neg_part_to_simple_func
- \+/\- *lemma* integral_eq_norm_pos_part_sub
- \+/\- *lemma* integral_eq
- \+ *lemma* simple_func.integral_l1_eq_integral
- \+/\- *lemma* integral_zero
- \+/\- *lemma* norm_integral_le
- \+/\- *lemma* integral_undef
- \+/\- *lemma* integral_non_integrable
- \+/\- *lemma* integral_non_measurable
- \+/\- *lemma* integral_mul_left
- \+/\- *lemma* integral_mul_right
- \+/\- *lemma* integral_div
- \+/\- *lemma* integral_congr_ae
- \+/\- *lemma* norm_integral_le_lintegral_norm
- \+ *lemma* tendsto_integral_of_l1
- \+/\- *lemma* integral_eq_lintegral_of_nonneg_ae
- \+/\- *lemma* integral_nonneg_of_ae
- \+/\- *lemma* integral_nonpos_of_nonpos_ae
- \+ *lemma* integral_mono
- \+/\- *lemma* integral_finset_sum
- \+/\- *lemma* simple_func.integral_eq_integral
- \+ *lemma* integral_const
- \- *lemma* integrable_iff_integral_lt_top
- \- *lemma* fin_vol_supp_of_integrable
- \- *lemma* integrable_of_fin_vol_supp
- \- *lemma* integrable_iff_fin_vol_supp
- \- *lemma* map_bintegral
- \- *lemma* bintegral_eq_integral
- \- *lemma* bintegral_eq_lintegral
- \- *lemma* bintegral_congr
- \- *lemma* bintegral_eq_integral'
- \- *lemma* bintegral_eq_lintegral'
- \- *lemma* bintegral_add
- \- *lemma* bintegral_neg
- \- *lemma* bintegral_sub
- \- *lemma* bintegral_smul
- \- *lemma* norm_bintegral_le_bintegral_norm
- \- *lemma* norm_eq_bintegral
- \- *lemma* exists_simple_func_near
- \- *lemma* integral_eq_bintegral
- \- *lemma* integral_le_integral_ae
- \- *lemma* integral_le_integral
- \+/\- *theorem* tendsto_integral_of_dominated_convergence
- \+/\- *def* pos_part
- \+/\- *def* neg_part
- \+/\- *def* integral
- \+/\- *def* simple_func
- \+/\- *def* of_simple_func
- \+/\- *def* to_simple_func
- \+/\- *def* coe_to_l1
- \+/\- *def* integral_clm
- \- *def* bintegral

Modified src/measure_theory/borel_space.lean
- \- *lemma* is_measurable_singleton
- \- *lemma* is_measurable_eq

Modified src/measure_theory/category/Meas.lean


Modified src/measure_theory/giry_monad.lean
- \+ *lemma* measurable_lintegral
- \+ *lemma* lintegral_join
- \+ *lemma* lintegral_bind
- \- *lemma* measurable_integral
- \- *lemma* integral_join
- \- *lemma* integral_bind

Modified src/measure_theory/indicator_function.lean
- \+/\- *lemma* indicator_congr_ae
- \+/\- *lemma* indicator_congr_of_set
- \+/\- *lemma* indicator_le_indicator_ae

Modified src/measure_theory/integration.lean
- \+ *lemma* coe_injective
- \+ *lemma* finite_range
- \+ *lemma* is_measurable_fiber
- \+ *lemma* coe_range
- \+ *lemma* forall_range_iff
- \+ *lemma* exists_range_iff
- \+/\- *lemma* range_const
- \+/\- *lemma* is_measurable_cut
- \+ *lemma* piecewise_compl
- \+ *lemma* piecewise_univ
- \+ *lemma* piecewise_empty
- \+ *lemma* coe_zero
- \+ *lemma* const_zero
- \+ *lemma* coe_add
- \+ *lemma* coe_mul
- \+ *lemma* coe_le
- \+ *lemma* range_zero
- \+ *lemma* eq_zero_of_mem_range_zero
- \+/\- *lemma* sup_apply
- \+/\- *lemma* mul_apply
- \+ *lemma* mul_eq_map₂
- \+ *lemma* coe_neg
- \+ *lemma* coe_sub
- \+ *lemma* coe_smul
- \+/\- *lemma* smul_eq_map
- \+/\- *lemma* mem_restrict_range
- \+ *lemma* mem_image_of_mem_range_restrict
- \+ *lemma* restrict_mono
- \+/\- *lemma* supr_eapprox_apply
- \+ *lemma* lintegral_eq_of_subset
- \+ *lemma* map_lintegral
- \+ *lemma* add_lintegral
- \+ *lemma* const_mul_lintegral
- \+ *lemma* zero_lintegral
- \+ *lemma* lintegral_add
- \+ *lemma* lintegral_smul
- \+/\- *lemma* lintegral_zero
- \+ *lemma* lintegral_sum
- \+ *lemma* restrict_lintegral
- \+ *lemma* lintegral_restrict
- \+ *lemma* restrict_lintegral_eq_lintegral_restrict
- \+ *lemma* const_lintegral
- \+ *lemma* const_lintegral_restrict
- \+ *lemma* restrict_const_lintegral
- \+ *lemma* le_sup_lintegral
- \+/\- *lemma* lintegral_mono
- \+ *lemma* lintegral_eq_of_measure_preimage
- \+ *lemma* lintegral_congr
- \+ *lemma* lintegral_map
- \+ *lemma* support_eq
- \+ *lemma* fin_meas_supp_iff_support
- \+ *lemma* fin_meas_supp_iff
- \+ *lemma* meas_preimage_singleton_ne_zero
- \+ *lemma* of_map
- \+ *lemma* map_iff
- \+ *lemma* lintegral_lt_top
- \+ *lemma* of_lintegral_lt_top
- \+ *lemma* iff_lintegral_lt_top
- \+ *lemma* lintegral_mono'
- \+/\- *lemma* monotone_lintegral
- \+ *lemma* lintegral_const
- \+/\- *lemma* lintegral_eq_nnreal
- \+ *lemma* lintegral_eq_supr_eapprox_lintegral
- \+ *lemma* lintegral_smul_meas
- \+ *lemma* lintegral_sum_meas
- \+ *lemma* lintegral_add_meas
- \+ *lemma* lintegral_zero_meas
- \+/\- *lemma* lintegral_const_mul_le
- \+ *lemma* lintegral_mono_ae
- \+/\- *lemma* lintegral_congr_ae
- \+/\- *lemma* lintegral_rw₁
- \+/\- *lemma* lintegral_rw₂
- \+ *lemma* lintegral_indicator
- \+ *lemma* mul_meas_ge_le_lintegral
- \+ *lemma* meas_ge_le_lintegral_div
- \+ *lemma* lintegral_Union
- \+ *lemma* lintegral_Union_le
- \+ *lemma* lintegral_dirac
- \+/\- *lemma* with_density_apply
- \- *lemma* volume_bUnion_preimage
- \- *lemma* map_integral
- \- *lemma* zero_integral
- \- *lemma* add_integral
- \- *lemma* const_mul_integral
- \- *lemma* restrict_preimage'
- \- *lemma* restrict_integral
- \- *lemma* restrict_const_integral
- \- *lemma* integral_sup_le
- \- *lemma* integral_le_integral
- \- *lemma* integral_congr
- \- *lemma* integral_map
- \- *lemma* fin_vol_supp_map
- \- *lemma* fin_vol_supp_of_fin_vol_supp_map
- \- *lemma* fin_vol_supp_pair
- \- *lemma* integral_lt_top_of_fin_vol_supp
- \- *lemma* fin_vol_supp_of_integral_lt_top
- \- *lemma* integral_map_coe_lt_top
- \- *lemma* lintegral_eq_supr_eapprox_integral
- \- *lemma* lintegral_supr_const
- \- *lemma* lintegral_le_lintegral_ae
- \- *lemma* simple_func.lintegral_map
- \- *lemma* mul_volume_ge_le_lintegral
- \- *lemma* volume_ge_le_lintegral_div
- \- *lemma* integral_zero
- \- *lemma* integral_dirac
- \+/\- *theorem* mem_range
- \+ *theorem* mem_range_self
- \+ *theorem* mem_range_of_measure_ne_zero
- \+/\- *theorem* const_apply
- \+ *theorem* coe_const
- \+ *theorem* is_measurable_preimage
- \+ *theorem* coe_piecewise
- \+ *theorem* piecewise_apply
- \+/\- *theorem* map_apply
- \+/\- *theorem* coe_map
- \+ *theorem* map_const
- \+ *theorem* restrict_of_not_measurable
- \+ *theorem* coe_restrict
- \+ *theorem* restrict_univ
- \+ *theorem* restrict_empty
- \+ *theorem* map_restrict_of_zero
- \+ *theorem* map_coe_ennreal_restrict
- \+ *theorem* map_coe_nnreal_restrict
- \+/\- *theorem* restrict_apply
- \+/\- *theorem* restrict_preimage
- \+ *theorem* restrict_preimage_singleton
- \+ *theorem* simple_func.lintegral_eq_lintegral
- \- *theorem* preimage_measurable
- \- *theorem* ite_apply
- \- *theorem* simple_func.lintegral_eq_integral
- \+ *def* piecewise
- \+/\- *def* restrict
- \+/\- *def* lintegral
- \+ *def* lintegralₗ
- \+ *def* measure.with_density
- \- *def* ite
- \- *def* integral
- \- *def* with_density

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* integrable_iff_norm
- \+/\- *lemma* integrable_iff_edist
- \+/\- *lemma* integrable_iff_of_real
- \+ *lemma* integrable.congr
- \+ *lemma* integrable_const
- \+ *lemma* integrable_congr
- \+ *lemma* integrable.mono
- \+ *lemma* integrable.mono_meas
- \+ *lemma* integrable.add_meas
- \+ *lemma* integrable.left_of_add_meas
- \+ *lemma* integrable.right_of_add_meas
- \+ *lemma* integrable.smul_meas
- \+ *lemma* integrable.mono_set
- \+ *lemma* integrable.union
- \+/\- *lemma* lintegral_nnnorm_zero
- \+/\- *lemma* integrable_zero
- \+/\- *lemma* integrable.neg
- \+/\- *lemma* integrable_neg_iff
- \+/\- *lemma* integrable.norm
- \+/\- *lemma* integrable_norm_iff
- \+/\- *lemma* integrable_of_integrable_bound
- \+/\- *lemma* all_ae_of_real_F_le_bound
- \+/\- *lemma* all_ae_tendsto_of_real_norm
- \+/\- *lemma* all_ae_of_real_f_le_bound
- \+/\- *lemma* integrable.max_zero
- \+/\- *lemma* integrable.min_zero
- \+/\- *lemma* integrable.smul
- \+ *lemma* integrable_coe_fn
- \+/\- *lemma* integrable.add
- \+/\- *lemma* integrable.sub
- \+ *lemma* coe_coe
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* edist_eq
- \+/\- *lemma* dist_eq
- \+/\- *lemma* norm_eq
- \+/\- *lemma* coe_smul
- \+/\- *lemma* of_fun_eq_mk
- \+/\- *lemma* of_fun_smul
- \+/\- *lemma* of_fun_to_fun
- \+/\- *lemma* mk_to_fun
- \+/\- *lemma* to_fun_of_fun
- \+/\- *lemma* zero_to_fun
- \+/\- *lemma* add_to_fun
- \+/\- *lemma* neg_to_fun
- \+/\- *lemma* sub_to_fun
- \+/\- *lemma* dist_to_fun
- \+/\- *lemma* norm_eq_nnnorm_to_fun
- \+/\- *lemma* norm_eq_norm_to_fun
- \+/\- *lemma* lintegral_edist_to_fun_lt_top
- \+/\- *lemma* smul_to_fun
- \+/\- *lemma* coe_pos_part
- \+/\- *lemma* pos_part_to_fun
- \+/\- *lemma* neg_part_to_fun_eq_max
- \+/\- *lemma* neg_part_to_fun_eq_min
- \+/\- *lemma* norm_le_norm_of_ae_le
- \+/\- *lemma* continuous_pos_part
- \+/\- *lemma* continuous_neg_part
- \- *lemma* integrable_of_ae_eq
- \- *lemma* integrable_congr_ae
- \- *lemma* integrable_of_le_ae
- \- *lemma* integrable_of_le
- \- *lemma* integrable_to_fun
- \+/\- *def* integrable
- \+/\- *def* l1
- \+/\- *def* of_fun
- \+/\- *def* pos_part
- \+/\- *def* neg_part

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* is_measurable.empty
- \+/\- *lemma* is_measurable.compl_iff
- \+/\- *lemma* is_measurable.univ
- \+ *lemma* is_measurable_eq
- \+ *lemma* is_measurable.insert
- \+ *lemma* is_measurable_insert
- \+ *lemma* set.finite.is_measurable
- \+ *lemma* measurable_iff_le_map
- \+ *lemma* measurable_iff_comap_le
- \+/\- *lemma* measurable_id
- \+ *lemma* measurable.piecewise
- \+/\- *lemma* measurable_const
- \+ *lemma* measurable.indicator
- \+ *lemma* measurable_one
- \+ *lemma* measurable_subtype_coe
- \+ *lemma* is_measurable.subtype_image
- \+ *lemma* measurable_fst
- \+ *lemma* measurable_snd
- \+/\- *lemma* measurable_inl
- \+/\- *lemma* measurable_inr
- \+ *lemma* measurable.sum_rec
- \+ *lemma* is_measurable.inl_image
- \- *lemma* measurable.preimage
- \- *lemma* measurable.if
- \- *lemma* measurable_zero
- \- *lemma* is_measurable_subtype_image
- \- *lemma* measurable_sum_rec
- \- *lemma* is_measurable_inl_image
- \+/\- *def* measurable

Modified src/measure_theory/measure_space.lean
- \+ *lemma* to_outer_measure_injective
- \+/\- *lemma* ext
- \+ *lemma* coe_to_outer_measure
- \+/\- *lemma* to_outer_measure_apply
- \+ *lemma* nonempty_of_measure_ne_zero
- \+ *lemma* exists_is_measurable_superset_iff_measure_eq_zero
- \+ *lemma* measure_bUnion_le
- \+ *lemma* measure_bUnion_finset_le
- \+ *lemma* tsum_measure_preimage_singleton
- \+ *lemma* sum_measure_preimage_singleton
- \+/\- *lemma* to_measure_to_outer_measure
- \+ *lemma* le_to_measure_apply
- \+/\- *lemma* to_outer_measure_to_measure
- \+ *lemma* eq_zero_of_not_nonempty
- \+ *lemma* lift_linear_apply
- \+ *lemma* le_lift_linear_apply
- \+ *lemma* comap_apply
- \+ *lemma* restrictₗ_apply
- \+ *lemma* restrict_apply
- \+ *lemma* le_restrict_apply
- \+ *lemma* restrict_add
- \+ *lemma* restrict_zero
- \+ *lemma* restrict_smul
- \+ *lemma* restrict_apply_eq_zero
- \+ *lemma* restrict_apply_eq_zero'
- \+ *lemma* restrict_empty
- \+ *lemma* restrict_univ
- \+ *lemma* restrict_union_apply
- \+ *lemma* restrict_union
- \+ *lemma* restrict_union_le
- \+ *lemma* restrict_Union_apply
- \+ *lemma* map_comap_subtype_coe
- \+ *lemma* restrict_mono
- \+ *lemma* dirac_apply'
- \+/\- *lemma* dirac_apply
- \+ *lemma* dirac_apply_of_mem
- \+ *lemma* sum_apply
- \+ *lemma* restrict_Union
- \+ *lemma* restrict_Union_le
- \+ *lemma* sum_bool
- \+ *lemma* restrict_sum
- \+ *lemma* count_apply
- \+ *lemma* count_apply_finset
- \+ *lemma* mem_cofinite
- \+ *lemma* eventually_cofinite
- \+/\- *lemma* mem_ae_iff
- \+/\- *lemma* ae_iff
- \+/\- *lemma* measure_zero_iff_ae_nmem
- \+/\- *lemma* ae_of_all
- \+/\- *lemma* ae_eq_refl
- \+/\- *lemma* ae_eq_symm
- \+/\- *lemma* ae_eq_trans
- \+ *lemma* mem_ae_map_iff
- \+ *lemma* ae_map_iff
- \+ *lemma* ae_restrict_eq
- \+ *lemma* mem_dirac_ae_iff
- \+ *lemma* eventually_dirac
- \+ *lemma* eventually_eq_dirac
- \+ *lemma* dirac_ae_eq
- \+ *lemma* eventually_eq_dirac'
- \+ *lemma* measure_diff_of_ae_imp
- \+ *lemma* measure_le_of_ae_imp
- \+ *lemma* measure_congr
- \- *lemma* trim_smul
- \+/\- *theorem* trim_eq_infi'
- \+ *theorem* trim_smul
- \+/\- *theorem* zero_to_outer_measure
- \+ *theorem* coe_zero
- \+ *theorem* coe_add
- \+/\- *theorem* add_apply
- \+ *theorem* smul_to_outer_measure
- \+ *theorem* coe_smul
- \+ *theorem* lt_iff
- \+ *theorem* lt_iff'
- \+/\- *theorem* map_apply
- \- *theorem* zero_apply
- \- *theorem* smul_apply
- \+ *def* lift_linear
- \+/\- *def* map
- \+ *def* comap
- \+ *def* restrictₗ
- \+ *def* restrict
- \+ *def* cofinite

Modified src/measure_theory/outer_measure.lean
- \+/\- *lemma* measure_of_eq_coe
- \+ *lemma* coe_fn_injective
- \+/\- *lemma* ext
- \+ *lemma* coe_smul
- \+ *lemma* smul_apply
- \+ *lemma* comap_apply
- \+ *lemma* restrict_apply
- \+ *theorem* coe_zero
- \+ *theorem* coe_add
- \+/\- *theorem* add_apply
- \- *theorem* zero_apply
- \- *theorem* smul_apply
- \+/\- *def* map
- \+ *def* comap
- \+ *def* restrict

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* integral_on_congr
- \+/\- *lemma* integral_on_nonneg_of_ae
- \+/\- *lemma* integral_on_nonpos_of_ae
- \- *lemma* measurable_on_empty
- \- *lemma* measurable.measurable_on_univ
- \- *lemma* measurable_on_singleton
- \- *lemma* is_measurable.inter_preimage
- \- *lemma* measurable.measurable_on
- \- *lemma* measurable_on.subset
- \- *lemma* measurable_on.union
- \- *lemma* integrable_on_congr
- \- *lemma* integrable_on_congr_ae
- \- *lemma* integrable_on_empty
- \- *lemma* measure_theory.integrable.integrable_on
- \- *lemma* integrable_on.subset
- \- *lemma* integrable_on.smul
- \- *lemma* integrable_on.mul_left
- \- *lemma* integrable_on.mul_right
- \- *lemma* integrable_on.divide
- \- *lemma* integrable_on.add
- \- *lemma* integrable_on.neg
- \- *lemma* integrable_on.sub
- \- *lemma* integrable_on.union
- \- *lemma* integrable_on_norm_iff
- \- *lemma* integral_on_undef
- \- *lemma* integral_on_non_measurable
- \- *lemma* integral_on_non_integrable
- \- *lemma* integral_on_zero
- \- *lemma* integral_on_congr_of_ae_eq
- \- *def* measurable_on
- \- *def* integrable_on

Modified src/measure_theory/simple_func_dense.lean
- \+/\- *lemma* simple_func_sequence_tendsto'

Modified src/order/complete_lattice.lean
- \+/\- *lemma* infi_eq_bot

Modified src/order/filter/basic.lean
- \+ *lemma* eventually_eq.prod_mk
- \+/\- *theorem* mem_inf_principal
- \+ *theorem* eventually_inf_principal

Modified src/order/filter/germ.lean
- \+ *lemma* map₂_coe

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tsum_subtype

Modified src/topology/algebra/module.lean
- \+ *lemma* coe_mk
- \+ *lemma* coe_mk'
- \+ *theorem* coe_injective
- \+ *theorem* coe_injective'

Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/continuous_on.lean


Modified src/topology/dense_embedding.lean
- \+ *lemma* extend_eq_of_tendsto
- \+ *lemma* extend_eq_at
- \+/\- *lemma* extend_eq
- \+ *lemma* extend_unique_at
- \+ *lemma* extend_unique
- \- *lemma* extend_e_eq
- \- *lemma* extend_eq_of_cont

Modified src/topology/stone_cech.lean


Modified src/topology/uniform_space/abstract_completion.lean


Modified src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* uniformly_extend_unique



## [2020-07-17 05:45:27](https://github.com/leanprover-community/mathlib/commit/819bd86)
feat(tactic/squeeze_*): add `squeeze_dsimp` ([#3386](https://github.com/leanprover-community/mathlib/pull/3386))
#### Estimated changes
Modified src/tactic/squeeze.lean




## [2020-07-17 03:52:34](https://github.com/leanprover-community/mathlib/commit/9d74f9b)
chore(data/polynomial): reduce imports ([#3419](https://github.com/leanprover-community/mathlib/pull/3419))
Now that @jalex-stark has split up `data.polynomial` into submodules, this PR minimises imports.
#### Estimated changes
Modified src/algebra/group_ring_action.lean


Modified src/algebra/polynomial/basic.lean


Modified src/analysis/calculus/deriv.lean


Modified src/data/mv_polynomial.lean


Modified src/data/padics/hensel.lean


Modified src/data/polynomial/identities.lean


Modified src/field_theory/minimal_polynomial.lean


Modified src/field_theory/separable.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/free_ring.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial_algebra.lean


Modified src/ring_theory/power_series.lean


Modified src/topology/algebra/polynomial.lean




## [2020-07-17 00:03:26](https://github.com/leanprover-community/mathlib/commit/f1b687c)
feat (order/order_iso): lemmas about order_isos on lattices ([#3397](https://github.com/leanprover-community/mathlib/pull/3397))
shows that `order_embedding`s and `order_iso`s respect `lattice` operations
#### Estimated changes
Modified src/order/order_iso.lean
- \+ *lemma* order_iso.map_bot
- \+ *lemma* order_iso.map_top
- \+ *lemma* order_embedding.map_inf_le
- \+ *lemma* order_iso.map_inf
- \+ *lemma* order_embedding.le_map_sup
- \+ *lemma* order_iso.map_sup



## [2020-07-16 19:13:26](https://github.com/leanprover-community/mathlib/commit/33d45bf)
chore(data/polynomial): break up behemoth file ([#3407](https://github.com/leanprover-community/mathlib/pull/3407))
Polynomial refactor
The goal is to split `data/polynomial.lean` into several self-contained files in the same place. For the time being, the new place for all these files is `data/polynomial/`.
Future PRs may simplify proofs, remove duplicate lemmas, and move files out of the `data` directory.
#### Estimated changes
Deleted src/data/polynomial.lean
- \- *lemma* support_zero
- \- *lemma* monomial_zero_right
- \- *lemma* monomial_add
- \- *lemma* X_mul
- \- *lemma* X_pow_mul
- \- *lemma* X_pow_mul_assoc
- \- *lemma* coeff_mk
- \- *lemma* ext
- \- *lemma* degree_lt_wf
- \- *lemma* apply_eq_coeff
- \- *lemma* coeff_zero
- \- *lemma* coeff_single
- \- *lemma* coeff_one_zero
- \- *lemma* coeff_add
- \- *lemma* coeff_X_one
- \- *lemma* coeff_X_zero
- \- *lemma* coeff_X
- \- *lemma* coeff_sum
- \- *lemma* coeff_smul
- \- *lemma* coeff_one
- \- *lemma* coeff_mul
- \- *lemma* mul_coeff_zero
- \- *lemma* monomial_one_eq_X_pow
- \- *lemma* monomial_eq_smul_X
- \- *lemma* coeff_X_pow
- \- *lemma* monomial_zero_left
- \- *lemma* single_eq_C_mul_X
- \- *lemma* sum_C_mul_X_eq
- \- *lemma* sum_monomial_eq
- \- *lemma* C_0
- \- *lemma* C_1
- \- *lemma* C_mul
- \- *lemma* C_add
- \- *lemma* C_bit0
- \- *lemma* C_bit1
- \- *lemma* C_pow
- \- *lemma* C_eq_nat_cast
- \- *lemma* sum_C_index
- \- *lemma* coeff_C
- \- *lemma* coeff_C_zero
- \- *lemma* coeff_C_mul_X
- \- *lemma* coeff_C_mul
- \- *lemma* coeff_mul_C
- \- *lemma* C_mul'
- \- *lemma* C_inj
- \- *lemma* eval₂_zero
- \- *lemma* eval₂_C
- \- *lemma* eval₂_X
- \- *lemma* eval₂_monomial
- \- *lemma* eval₂_X_pow
- \- *lemma* eval₂_add
- \- *lemma* eval₂_one
- \- *lemma* eval₂_bit0
- \- *lemma* eval₂_bit1
- \- *lemma* eval₂_smul
- \- *lemma* eval₂_nat_cast
- \- *lemma* eval₂_sum
- \- *lemma* eval_C
- \- *lemma* eval_nat_cast
- \- *lemma* eval_X
- \- *lemma* eval_monomial
- \- *lemma* eval_zero
- \- *lemma* eval_add
- \- *lemma* eval_one
- \- *lemma* eval_bit0
- \- *lemma* eval_bit1
- \- *lemma* eval_smul
- \- *lemma* eval_sum
- \- *lemma* is_root.def
- \- *lemma* coeff_zero_eq_eval_zero
- \- *lemma* zero_is_root_of_coeff_zero_eq_zero
- \- *lemma* comp_X
- \- *lemma* X_comp
- \- *lemma* comp_C
- \- *lemma* C_comp
- \- *lemma* comp_zero
- \- *lemma* zero_comp
- \- *lemma* comp_one
- \- *lemma* one_comp
- \- *lemma* add_comp
- \- *lemma* eval₂_mul
- \- *lemma* coe_eval₂_ring_hom
- \- *lemma* eval₂_pow
- \- *lemma* algebra_map_apply
- \- *lemma* C_eq_algebra_map
- \- *lemma* alg_hom_eval₂_algebra_map
- \- *lemma* eval₂_algebra_map_X
- \- *lemma* ring_hom_eval₂_algebra_map_int
- \- *lemma* eval₂_algebra_map_int_X
- \- *lemma* eval_mul
- \- *lemma* eval_pow
- \- *lemma* eval₂_hom
- \- *lemma* root_mul_left_of_is_root
- \- *lemma* root_mul_right_of_is_root
- \- *lemma* eval₂_comp
- \- *lemma* eval_comp
- \- *lemma* mul_comp
- \- *lemma* monic.def
- \- *lemma* monic.leading_coeff
- \- *lemma* degree_zero
- \- *lemma* nat_degree_zero
- \- *lemma* degree_eq_bot
- \- *lemma* degree_eq_nat_degree
- \- *lemma* degree_eq_iff_nat_degree_eq
- \- *lemma* degree_eq_iff_nat_degree_eq_of_pos
- \- *lemma* nat_degree_eq_of_degree_eq_some
- \- *lemma* degree_le_nat_degree
- \- *lemma* nat_degree_eq_of_degree_eq
- \- *lemma* le_degree_of_ne_zero
- \- *lemma* le_nat_degree_of_ne_zero
- \- *lemma* degree_le_degree
- \- *lemma* degree_ne_of_nat_degree_ne
- \- *lemma* nat_degree_le_nat_degree
- \- *lemma* degree_C
- \- *lemma* degree_C_le
- \- *lemma* degree_one_le
- \- *lemma* nat_degree_C
- \- *lemma* nat_degree_one
- \- *lemma* nat_degree_nat_cast
- \- *lemma* degree_monomial
- \- *lemma* degree_monomial_le
- \- *lemma* coeff_eq_zero_of_degree_lt
- \- *lemma* coeff_eq_zero_of_nat_degree_lt
- \- *lemma* coeff_nat_degree_succ_eq_zero
- \- *lemma* finset_sum_coeff
- \- *lemma* ite_le_nat_degree_coeff
- \- *lemma* as_sum
- \- *lemma* monic.as_sum
- \- *lemma* coeff_ne_zero_of_eq_degree
- \- *lemma* sum_over_range'
- \- *lemma* sum_over_range
- \- *lemma* map_C
- \- *lemma* map_X
- \- *lemma* map_monomial
- \- *lemma* map_zero
- \- *lemma* map_add
- \- *lemma* map_one
- \- *lemma* coeff_map
- \- *lemma* map_map
- \- *lemma* map_id
- \- *lemma* eval₂_eq_eval_map
- \- *lemma* coeff_nat_degree_eq_zero_of_degree_lt
- \- *lemma* ne_zero_of_degree_gt
- \- *lemma* eq_C_of_degree_le_zero
- \- *lemma* eq_C_of_degree_eq_zero
- \- *lemma* degree_le_zero_iff
- \- *lemma* degree_add_le
- \- *lemma* leading_coeff_zero
- \- *lemma* leading_coeff_eq_zero
- \- *lemma* leading_coeff_eq_zero_iff_deg_eq_bot
- \- *lemma* degree_add_eq_of_degree_lt
- \- *lemma* degree_add_C
- \- *lemma* degree_add_eq_of_leading_coeff_add_ne_zero
- \- *lemma* degree_erase_le
- \- *lemma* degree_erase_lt
- \- *lemma* degree_sum_le
- \- *lemma* degree_mul_le
- \- *lemma* degree_pow_le
- \- *lemma* leading_coeff_monomial
- \- *lemma* leading_coeff_C
- \- *lemma* leading_coeff_X
- \- *lemma* monic_X
- \- *lemma* leading_coeff_one
- \- *lemma* monic_one
- \- *lemma* monic.ne_zero_of_zero_ne_one
- \- *lemma* monic.ne_zero
- \- *lemma* leading_coeff_add_of_degree_lt
- \- *lemma* leading_coeff_add_of_degree_eq
- \- *lemma* coeff_mul_degree_add_degree
- \- *lemma* degree_mul_eq'
- \- *lemma* nat_degree_mul_eq'
- \- *lemma* leading_coeff_mul'
- \- *lemma* leading_coeff_pow'
- \- *lemma* degree_pow_eq'
- \- *lemma* nat_degree_pow_eq'
- \- *lemma* leading_coeff_X_pow
- \- *lemma* nat_degree_comp_le
- \- *lemma* degree_map_le
- \- *lemma* subsingleton_of_monic_zero
- \- *lemma* degree_map_eq_of_leading_coeff_ne_zero
- \- *lemma* monic_map
- \- *lemma* zero_le_degree_iff
- \- *lemma* coeff_mul_X_zero
- \- *lemma* degree_nonneg_iff_ne_zero
- \- *lemma* nat_degree_eq_zero_iff_degree_le_zero
- \- *lemma* map_mul
- \- *lemma* map_pow
- \- *lemma* mem_map_range
- \- *lemma* eval₂_map
- \- *lemma* eval_map
- \- *lemma* hom_eval₂
- \- *lemma* is_unit_C
- \- *lemma* eq_one_of_is_unit_of_monic
- \- *lemma* ne_zero_of_monic_of_zero_ne_one
- \- *lemma* eq_X_add_C_of_degree_le_one
- \- *lemma* eq_X_add_C_of_degree_eq_one
- \- *lemma* nat_degree_X_le
- \- *lemma* degree_map_eq_of_injective
- \- *lemma* degree_map'
- \- *lemma* nat_degree_map'
- \- *lemma* map_injective
- \- *lemma* leading_coeff_of_injective
- \- *lemma* monic_of_injective
- \- *lemma* nat_degree_mul_le
- \- *lemma* monic_mul
- \- *lemma* monic_pow
- \- *lemma* multiplicity_finite_of_degree_pos_of_monic
- \- *lemma* degree_one
- \- *lemma* degree_X
- \- *lemma* nat_degree_X
- \- *lemma* X_ne_zero
- \- *lemma* degree_X_pow
- \- *lemma* not_monic_zero
- \- *lemma* ne_zero_of_monic
- \- *lemma* div_X_mul_X_add
- \- *lemma* div_X_C
- \- *lemma* div_X_eq_zero_iff
- \- *lemma* div_X_add
- \- *lemma* degree_lt_degree_mul_X
- \- *lemma* degree_div_X_lt
- \- *lemma* degree_pos_induction_on
- \- *lemma* lcoeff_apply
- \- *lemma* degree_pos_of_root
- \- *lemma* eq_C_of_nat_degree_le_zero
- \- *lemma* nat_degree_pos_iff_degree_pos
- \- *lemma* nat_degree_pos_of_eval₂_root
- \- *lemma* degree_pos_of_eval₂_root
- \- *lemma* C_eq_int_cast
- \- *lemma* C_neg
- \- *lemma* C_sub
- \- *lemma* map_sub
- \- *lemma* map_neg
- \- *lemma* degree_neg
- \- *lemma* degree_sub_le
- \- *lemma* nat_degree_neg
- \- *lemma* nat_degree_int_cast
- \- *lemma* coeff_neg
- \- *lemma* coeff_sub
- \- *lemma* eval_int_cast
- \- *lemma* eval₂_neg
- \- *lemma* eval₂_sub
- \- *lemma* eval_neg
- \- *lemma* eval_sub
- \- *lemma* coeff_mul_X_sub_C
- \- *lemma* aeval_X
- \- *lemma* aeval_C
- \- *lemma* is_root_of_eval₂_map_eq_zero
- \- *lemma* is_root_of_aeval_algebra_map_eq_zero
- \- *lemma* dvd_term_of_dvd_eval_of_dvd_terms
- \- *lemma* dvd_term_of_is_root_of_dvd_terms
- \- *lemma* degree_sub_lt
- \- *lemma* ne_zero_of_ne_zero_of_monic
- \- *lemma* div_wf_lemma
- \- *lemma* degree_mod_by_monic_lt
- \- *lemma* zero_mod_by_monic
- \- *lemma* zero_div_by_monic
- \- *lemma* mod_by_monic_zero
- \- *lemma* div_by_monic_zero
- \- *lemma* div_by_monic_eq_of_not_monic
- \- *lemma* mod_by_monic_eq_of_not_monic
- \- *lemma* mod_by_monic_eq_self_iff
- \- *lemma* mod_by_monic_eq_sub_mul_div
- \- *lemma* mod_by_monic_add_div
- \- *lemma* div_by_monic_eq_zero_iff
- \- *lemma* degree_add_div_by_monic
- \- *lemma* degree_div_by_monic_le
- \- *lemma* degree_div_by_monic_lt
- \- *lemma* div_mod_by_monic_unique
- \- *lemma* map_mod_div_by_monic
- \- *lemma* map_div_by_monic
- \- *lemma* map_mod_by_monic
- \- *lemma* dvd_iff_mod_by_monic_eq_zero
- \- *lemma* mod_by_monic_one
- \- *lemma* div_by_monic_one
- \- *lemma* nat_degree_pos_of_aeval_root
- \- *lemma* degree_pos_of_aeval_root
- \- *lemma* root_X_sub_C
- \- *lemma* degree_X_sub_C
- \- *lemma* nat_degree_X_sub_C
- \- *lemma* degree_X_pow_sub_C
- \- *lemma* X_pow_sub_C_ne_zero
- \- *lemma* nat_degree_X_pow_sub_C
- \- *lemma* eq_zero_of_eq_zero
- \- *lemma* nat_degree_X_sub_C_le
- \- *lemma* eval_mul_X_sub_C
- \- *lemma* mod_by_monic_X_sub_C_eq_C_eval
- \- *lemma* mul_div_by_monic_eq_iff_is_root
- \- *lemma* dvd_iff_is_root
- \- *lemma* mod_by_monic_X
- \- *lemma* multiplicity_X_sub_C_finite
- \- *lemma* root_multiplicity_eq_multiplicity
- \- *lemma* pow_root_multiplicity_dvd
- \- *lemma* div_by_monic_mul_pow_root_multiplicity_eq
- \- *lemma* eval_div_by_monic_pow_root_multiplicity_ne_zero
- \- *lemma* degree_mul_eq
- \- *lemma* degree_pow_eq
- \- *lemma* leading_coeff_mul
- \- *lemma* leading_coeff_pow
- \- *lemma* nat_degree_mul_eq
- \- *lemma* nat_degree_pow_eq
- \- *lemma* root_mul
- \- *lemma* root_or_root_of_root_mul
- \- *lemma* degree_le_mul_left
- \- *lemma* exists_finset_roots
- \- *lemma* card_roots
- \- *lemma* card_roots'
- \- *lemma* card_roots_sub_C
- \- *lemma* card_roots_sub_C'
- \- *lemma* mem_roots
- \- *lemma* roots_mul
- \- *lemma* mem_roots_sub_C
- \- *lemma* roots_X_sub_C
- \- *lemma* card_roots_X_pow_sub_C
- \- *lemma* mem_nth_roots
- \- *lemma* card_nth_roots
- \- *lemma* coeff_comp_degree_mul_degree
- \- *lemma* nat_degree_comp
- \- *lemma* leading_coeff_comp
- \- *lemma* degree_eq_zero_of_is_unit
- \- *lemma* degree_coe_units
- \- *lemma* nat_degree_coe_units
- \- *lemma* coeff_coe_units_zero_ne_zero
- \- *lemma* degree_eq_degree_of_associated
- \- *lemma* degree_eq_one_of_irreducible_of_root
- \- *lemma* prime_of_degree_eq_one_of_monic
- \- *lemma* irreducible_of_degree_eq_one_of_monic
- \- *lemma* is_unit_iff_degree_eq_zero
- \- *lemma* degree_pos_of_ne_zero_of_nonunit
- \- *lemma* monic_mul_leading_coeff_inv
- \- *lemma* degree_mul_leading_coeff_inv
- \- *lemma* div_def
- \- *lemma* mod_def
- \- *lemma* mod_by_monic_eq_mod
- \- *lemma* div_by_monic_eq_div
- \- *lemma* mod_X_sub_C_eq_C_eval
- \- *lemma* mul_div_eq_iff_is_root
- \- *lemma* mod_eq_self_iff
- \- *lemma* div_eq_zero_iff
- \- *lemma* degree_add_div
- \- *lemma* degree_div_le
- \- *lemma* degree_div_lt
- \- *lemma* degree_map
- \- *lemma* nat_degree_map
- \- *lemma* leading_coeff_map
- \- *lemma* map_div
- \- *lemma* map_mod
- \- *lemma* map_eq_zero
- \- *lemma* exists_root_of_degree_eq_one
- \- *lemma* coeff_inv_units
- \- *lemma* monic_normalize
- \- *lemma* coe_norm_unit
- \- *lemma* degree_normalize
- \- *lemma* prime_of_degree_eq_one
- \- *lemma* irreducible_of_degree_eq_one
- \- *lemma* coeff_derivative
- \- *lemma* derivative_zero
- \- *lemma* derivative_monomial
- \- *lemma* derivative_C
- \- *lemma* derivative_X
- \- *lemma* derivative_one
- \- *lemma* derivative_add
- \- *lemma* derivative_neg
- \- *lemma* derivative_sub
- \- *lemma* derivative_sum
- \- *lemma* derivative_smul
- \- *lemma* derivative_mul
- \- *lemma* derivative_eval
- \- *lemma* is_coprime_of_is_root_of_eval_derivative_ne_zero
- \- *lemma* mem_support_derivative
- \- *lemma* degree_derivative_eq
- \- *lemma* integral_normalization_coeff_degree
- \- *lemma* integral_normalization_coeff_nat_degree
- \- *lemma* integral_normalization_coeff_ne_degree
- \- *lemma* integral_normalization_coeff_ne_nat_degree
- \- *lemma* monic_integral_normalization
- \- *lemma* support_integral_normalization
- \- *lemma* integral_normalization_eval₂_eq_zero
- \- *lemma* integral_normalization_aeval_eq_zero
- \- *lemma* polynomial
- \- *theorem* ext_iff
- \- *theorem* coeff_mul_X_pow
- \- *theorem* coeff_mul_X
- \- *theorem* mul_X_pow_eq_zero
- \- *theorem* coeff_mul_monomial
- \- *theorem* coeff_monomial_mul
- \- *theorem* coeff_mul_monomial_zero
- \- *theorem* coeff_monomial_zero_mul
- \- *theorem* nat_degree_le_of_degree_le
- \- *theorem* map_nat_cast
- \- *theorem* degree_C_mul_X_pow_le
- \- *theorem* degree_X_pow_le
- \- *theorem* degree_X_le
- \- *theorem* monic_of_degree_le
- \- *theorem* monic_X_pow_add
- \- *theorem* monic_X_add_C
- \- *theorem* degree_le_iff_coeff_zero
- \- *theorem* leading_coeff_mul_X_pow
- \- *theorem* not_is_unit_X
- \- *theorem* nonzero.of_polynomial_ne
- \- *theorem* X_dvd_iff
- \- *theorem* aeval_def
- \- *theorem* eval_unique
- \- *theorem* aeval_alg_hom
- \- *theorem* aeval_alg_hom_apply
- \- *theorem* monic_X_sub_C
- \- *theorem* monic_X_pow_sub
- \- *theorem* degree_mod_by_monic_le
- \- *theorem* nat_degree_div_by_monic
- \- *theorem* X_sub_C_ne_zero
- \- *theorem* not_is_unit_X_sub_C
- \- *theorem* nat_degree_le_of_dvd
- \- *theorem* is_unit_iff
- \- *theorem* prime_X_sub_C
- \- *theorem* prime_X
- \- *theorem* irreducible_X_sub_C
- \- *theorem* irreducible_X
- \- *theorem* pairwise_coprime_X_sub
- \- *theorem* derivative_pow_succ
- \- *theorem* derivative_pow
- \- *theorem* derivative_map
- \- *theorem* derivative_eval₂_C
- \- *theorem* of_mem_support_derivative
- \- *theorem* degree_derivative_lt
- \- *theorem* nat_degree_derivative_lt
- \- *theorem* degree_derivative_le
- \- *def* polynomial
- \- *def* coeff_coe_to_fun
- \- *def* monomial
- \- *def* X
- \- *def* coeff
- \- *def* degree
- \- *def* nat_degree
- \- *def* C
- \- *def* eval₂
- \- *def* eval
- \- *def* is_root
- \- *def* comp
- \- *def* eval₂_ring_hom
- \- *def* leading_coeff
- \- *def* monic
- \- *def* map
- \- *def* div_X
- \- *def* lcoeff
- \- *def* aeval
- \- *def* div_by_monic
- \- *def* mod_by_monic
- \- *def* decidable_dvd_monic
- \- *def* root_multiplicity
- \- *def* nth_roots
- \- *def* div
- \- *def* mod
- \- *def* derivative
- \- *def* derivative_hom
- \- *def* derivative_lhom
- \- *def* pow_add_expansion
- \- *def* binom_expansion
- \- *def* pow_sub_pow_factor
- \- *def* eval_sub_factor

Created src/data/polynomial/algebra_map.lean
- \+ *lemma* C_mul'
- \+ *lemma* C_inj
- \+ *lemma* algebra_map_apply
- \+ *lemma* C_eq_algebra_map
- \+ *lemma* alg_hom_eval₂_algebra_map
- \+ *lemma* eval₂_algebra_map_X
- \+ *lemma* ring_hom_eval₂_algebra_map_int
- \+ *lemma* eval₂_algebra_map_int_X
- \+ *lemma* eval_mul
- \+ *lemma* eval_pow
- \+ *lemma* eval₂_hom
- \+ *lemma* root_mul_left_of_is_root
- \+ *lemma* root_mul_right_of_is_root
- \+ *lemma* eval₂_comp
- \+ *lemma* eval_comp
- \+ *lemma* mul_comp
- \+ *lemma* aeval_X
- \+ *lemma* aeval_C
- \+ *lemma* is_root_of_eval₂_map_eq_zero
- \+ *lemma* is_root_of_aeval_algebra_map_eq_zero
- \+ *lemma* dvd_term_of_dvd_eval_of_dvd_terms
- \+ *lemma* dvd_term_of_is_root_of_dvd_terms
- \+ *lemma* eval_mul_X_sub_C
- \+ *theorem* aeval_def
- \+ *theorem* eval_unique
- \+ *theorem* aeval_alg_hom
- \+ *theorem* aeval_alg_hom_apply
- \+ *theorem* not_is_unit_X_sub_C
- \+ *def* aeval

Created src/data/polynomial/basic.lean
- \+ *lemma* support_zero
- \+ *lemma* monomial_zero_right
- \+ *lemma* monomial_add
- \+ *lemma* X_mul
- \+ *lemma* X_pow_mul
- \+ *lemma* X_pow_mul_assoc
- \+ *lemma* apply_eq_coeff
- \+ *lemma* coeff_mk
- \+ *lemma* coeff_single
- \+ *lemma* coeff_zero
- \+ *lemma* coeff_one_zero
- \+ *lemma* ext
- \+ *lemma* eq_zero_of_eq_zero
- \+ *lemma* coeff_neg
- \+ *lemma* coeff_sub
- \+ *theorem* ext_iff
- \+ *def* polynomial
- \+ *def* coeff_coe_to_fun
- \+ *def* monomial
- \+ *def* X
- \+ *def* coeff

Created src/data/polynomial/coeff.lean
- \+ *lemma* coeff_one
- \+ *lemma* coeff_add
- \+ *lemma* coeff_sum
- \+ *lemma* coeff_smul
- \+ *lemma* lcoeff_apply
- \+ *lemma* coeff_mul
- \+ *lemma* mul_coeff_zero
- \+ *lemma* coeff_mul_X_zero
- \+ *lemma* coeff_C_mul_X
- \+ *lemma* coeff_C_mul
- \+ *lemma* coeff_mul_C
- \+ *lemma* monomial_one_eq_X_pow
- \+ *lemma* monomial_eq_smul_X
- \+ *lemma* coeff_X_pow
- \+ *theorem* coeff_mul_X_pow
- \+ *theorem* coeff_mul_X
- \+ *theorem* mul_X_pow_eq_zero
- \+ *def* lcoeff

Created src/data/polynomial/default.lean


Created src/data/polynomial/degree.lean
- \+ *lemma* coeff_nat_degree_eq_zero_of_degree_lt
- \+ *lemma* ne_zero_of_degree_gt
- \+ *lemma* eq_C_of_degree_le_zero
- \+ *lemma* eq_C_of_degree_eq_zero
- \+ *lemma* degree_le_zero_iff
- \+ *lemma* degree_add_le
- \+ *lemma* leading_coeff_zero
- \+ *lemma* leading_coeff_eq_zero
- \+ *lemma* leading_coeff_eq_zero_iff_deg_eq_bot
- \+ *lemma* degree_add_eq_of_degree_lt
- \+ *lemma* degree_add_C
- \+ *lemma* degree_add_eq_of_leading_coeff_add_ne_zero
- \+ *lemma* degree_erase_le
- \+ *lemma* degree_erase_lt
- \+ *lemma* degree_sum_le
- \+ *lemma* degree_mul_le
- \+ *lemma* degree_pow_le
- \+ *lemma* leading_coeff_monomial
- \+ *lemma* leading_coeff_C
- \+ *lemma* leading_coeff_X
- \+ *lemma* monic_X
- \+ *lemma* leading_coeff_one
- \+ *lemma* monic_one
- \+ *lemma* monic.ne_zero_of_zero_ne_one
- \+ *lemma* monic.ne_zero
- \+ *lemma* leading_coeff_add_of_degree_lt
- \+ *lemma* leading_coeff_add_of_degree_eq
- \+ *lemma* coeff_mul_degree_add_degree
- \+ *lemma* degree_mul_eq'
- \+ *lemma* nat_degree_mul_eq'
- \+ *lemma* leading_coeff_mul'
- \+ *lemma* leading_coeff_pow'
- \+ *lemma* degree_pow_eq'
- \+ *lemma* nat_degree_pow_eq'
- \+ *lemma* leading_coeff_X_pow
- \+ *lemma* nat_degree_comp_le
- \+ *lemma* degree_map_le
- \+ *lemma* nat_degree_mul_le
- \+ *lemma* subsingleton_of_monic_zero
- \+ *lemma* degree_map_eq_of_leading_coeff_ne_zero
- \+ *lemma* zero_le_degree_iff
- \+ *lemma* degree_nonneg_iff_ne_zero
- \+ *lemma* nat_degree_eq_zero_iff_degree_le_zero
- \+ *lemma* degree_lt_degree_mul_X
- \+ *lemma* eq_C_of_nat_degree_le_zero
- \+ *lemma* nat_degree_pos_iff_degree_pos
- \+ *lemma* degree_pos_of_root
- \+ *lemma* nat_degree_pos_of_eval₂_root
- \+ *lemma* degree_pos_of_eval₂_root
- \+ *lemma* degree_map_eq_of_injective
- \+ *lemma* degree_map'
- \+ *lemma* nat_degree_map'
- \+ *lemma* degree_X_pow
- \+ *lemma* degree_sub_le
- \+ *lemma* degree_sub_lt
- \+ *lemma* nat_degree_X_sub_C_le
- \+ *lemma* degree_X_sub_C
- \+ *lemma* nat_degree_X_sub_C
- \+ *lemma* degree_X_pow_sub_C
- \+ *lemma* X_pow_sub_C_ne_zero
- \+ *lemma* nat_degree_X_pow_sub_C
- \+ *theorem* leading_coeff_mul_X_pow
- \+ *theorem* degree_le_iff_coeff_zero
- \+ *theorem* not_is_unit_X
- \+ *theorem* X_sub_C_ne_zero

Created src/data/polynomial/degree/basic.lean
- \+ *lemma* degree_lt_wf
- \+ *lemma* monic.def
- \+ *lemma* monic.leading_coeff
- \+ *lemma* degree_zero
- \+ *lemma* nat_degree_zero
- \+ *lemma* degree_eq_bot
- \+ *lemma* degree_eq_nat_degree
- \+ *lemma* degree_eq_iff_nat_degree_eq
- \+ *lemma* degree_eq_iff_nat_degree_eq_of_pos
- \+ *lemma* nat_degree_eq_of_degree_eq_some
- \+ *lemma* degree_le_nat_degree
- \+ *lemma* nat_degree_eq_of_degree_eq
- \+ *lemma* le_degree_of_ne_zero
- \+ *lemma* le_nat_degree_of_ne_zero
- \+ *lemma* degree_le_degree
- \+ *lemma* degree_ne_of_nat_degree_ne
- \+ *lemma* nat_degree_le_nat_degree
- \+ *lemma* degree_C
- \+ *lemma* degree_C_le
- \+ *lemma* degree_one_le
- \+ *lemma* nat_degree_C
- \+ *lemma* nat_degree_one
- \+ *lemma* nat_degree_nat_cast
- \+ *lemma* degree_monomial
- \+ *lemma* degree_monomial_le
- \+ *lemma* coeff_eq_zero_of_degree_lt
- \+ *lemma* coeff_eq_zero_of_nat_degree_lt
- \+ *lemma* coeff_nat_degree_succ_eq_zero
- \+ *lemma* ite_le_nat_degree_coeff
- \+ *lemma* coeff_ne_zero_of_eq_degree
- \+ *lemma* eq_X_add_C_of_degree_le_one
- \+ *lemma* eq_X_add_C_of_degree_eq_one
- \+ *lemma* nat_degree_X_le
- \+ *lemma* degree_one
- \+ *lemma* degree_X
- \+ *lemma* nat_degree_X
- \+ *lemma* coeff_mul_X_sub_C
- \+ *lemma* C_eq_int_cast
- \+ *lemma* degree_neg
- \+ *lemma* nat_degree_neg
- \+ *lemma* nat_degree_int_cast
- \+ *theorem* nat_degree_le_of_degree_le
- \+ *theorem* degree_C_mul_X_pow_le
- \+ *theorem* degree_X_pow_le
- \+ *theorem* degree_X_le
- \+ *def* degree
- \+ *def* nat_degree
- \+ *def* leading_coeff
- \+ *def* monic

Created src/data/polynomial/derivative.lean
- \+ *lemma* coeff_derivative
- \+ *lemma* derivative_zero
- \+ *lemma* derivative_monomial
- \+ *lemma* derivative_C
- \+ *lemma* derivative_X
- \+ *lemma* derivative_one
- \+ *lemma* derivative_add
- \+ *lemma* derivative_neg
- \+ *lemma* derivative_sub
- \+ *lemma* derivative_sum
- \+ *lemma* derivative_smul
- \+ *lemma* derivative_mul
- \+ *lemma* derivative_eval
- \+ *lemma* is_coprime_of_is_root_of_eval_derivative_ne_zero
- \+ *lemma* mem_support_derivative
- \+ *lemma* degree_derivative_eq
- \+ *theorem* derivative_pow_succ
- \+ *theorem* derivative_pow
- \+ *theorem* derivative_map
- \+ *theorem* derivative_eval₂_C
- \+ *theorem* of_mem_support_derivative
- \+ *theorem* degree_derivative_lt
- \+ *theorem* nat_degree_derivative_lt
- \+ *theorem* degree_derivative_le
- \+ *def* derivative
- \+ *def* derivative_hom
- \+ *def* derivative_lhom

Created src/data/polynomial/div.lean
- \+ *lemma* div_X_mul_X_add
- \+ *lemma* div_X_C
- \+ *lemma* div_X_eq_zero_iff
- \+ *lemma* div_X_add
- \+ *lemma* degree_div_X_lt
- \+ *lemma* degree_pos_induction_on
- \+ *lemma* multiplicity_finite_of_degree_pos_of_monic
- \+ *lemma* div_wf_lemma
- \+ *lemma* degree_mod_by_monic_lt
- \+ *lemma* zero_mod_by_monic
- \+ *lemma* zero_div_by_monic
- \+ *lemma* mod_by_monic_zero
- \+ *lemma* div_by_monic_zero
- \+ *lemma* div_by_monic_eq_of_not_monic
- \+ *lemma* mod_by_monic_eq_of_not_monic
- \+ *lemma* mod_by_monic_eq_self_iff
- \+ *lemma* mod_by_monic_eq_sub_mul_div
- \+ *lemma* mod_by_monic_add_div
- \+ *lemma* div_by_monic_eq_zero_iff
- \+ *lemma* degree_add_div_by_monic
- \+ *lemma* degree_div_by_monic_le
- \+ *lemma* degree_div_by_monic_lt
- \+ *lemma* div_mod_by_monic_unique
- \+ *lemma* map_mod_div_by_monic
- \+ *lemma* map_div_by_monic
- \+ *lemma* map_mod_by_monic
- \+ *lemma* dvd_iff_mod_by_monic_eq_zero
- \+ *lemma* mod_by_monic_one
- \+ *lemma* div_by_monic_one
- \+ *lemma* mod_by_monic_X_sub_C_eq_C_eval
- \+ *lemma* mul_div_by_monic_eq_iff_is_root
- \+ *lemma* dvd_iff_is_root
- \+ *lemma* mod_by_monic_X
- \+ *lemma* multiplicity_X_sub_C_finite
- \+ *lemma* root_multiplicity_eq_multiplicity
- \+ *lemma* pow_root_multiplicity_dvd
- \+ *lemma* div_by_monic_mul_pow_root_multiplicity_eq
- \+ *lemma* eval_div_by_monic_pow_root_multiplicity_ne_zero
- \+ *theorem* X_dvd_iff
- \+ *theorem* degree_mod_by_monic_le
- \+ *theorem* nat_degree_div_by_monic
- \+ *def* div_X
- \+ *def* div_by_monic
- \+ *def* mod_by_monic
- \+ *def* decidable_dvd_monic
- \+ *def* root_multiplicity

Created src/data/polynomial/eval.lean
- \+ *lemma* eval₂_zero
- \+ *lemma* eval₂_C
- \+ *lemma* eval₂_X
- \+ *lemma* eval₂_monomial
- \+ *lemma* eval₂_X_pow
- \+ *lemma* eval₂_add
- \+ *lemma* eval₂_one
- \+ *lemma* eval₂_bit0
- \+ *lemma* eval₂_bit1
- \+ *lemma* eval₂_smul
- \+ *lemma* eval₂_nat_cast
- \+ *lemma* eval₂_sum
- \+ *lemma* eval₂_finset_sum
- \+ *lemma* eval₂_mul
- \+ *lemma* coe_eval₂_ring_hom
- \+ *lemma* eval₂_pow
- \+ *lemma* eval_C
- \+ *lemma* eval_nat_cast
- \+ *lemma* eval_X
- \+ *lemma* eval_monomial
- \+ *lemma* eval_zero
- \+ *lemma* eval_add
- \+ *lemma* eval_one
- \+ *lemma* eval_bit0
- \+ *lemma* eval_bit1
- \+ *lemma* eval_smul
- \+ *lemma* eval_sum
- \+ *lemma* is_root.def
- \+ *lemma* coeff_zero_eq_eval_zero
- \+ *lemma* zero_is_root_of_coeff_zero_eq_zero
- \+ *lemma* comp_X
- \+ *lemma* X_comp
- \+ *lemma* comp_C
- \+ *lemma* C_comp
- \+ *lemma* comp_zero
- \+ *lemma* zero_comp
- \+ *lemma* comp_one
- \+ *lemma* one_comp
- \+ *lemma* add_comp
- \+ *lemma* map_C
- \+ *lemma* map_X
- \+ *lemma* map_monomial
- \+ *lemma* map_zero
- \+ *lemma* map_add
- \+ *lemma* map_one
- \+ *lemma* coeff_map
- \+ *lemma* map_map
- \+ *lemma* map_id
- \+ *lemma* eval₂_eq_eval_map
- \+ *lemma* map_injective
- \+ *lemma* map_mul
- \+ *lemma* map_pow
- \+ *lemma* mem_map_range
- \+ *lemma* eval₂_map
- \+ *lemma* eval_map
- \+ *lemma* hom_eval₂
- \+ *lemma* C_neg
- \+ *lemma* C_sub
- \+ *lemma* map_sub
- \+ *lemma* map_neg
- \+ *lemma* eval_int_cast
- \+ *lemma* eval₂_neg
- \+ *lemma* eval₂_sub
- \+ *lemma* eval_neg
- \+ *lemma* eval_sub
- \+ *lemma* root_X_sub_C
- \+ *theorem* map_nat_cast
- \+ *def* eval₂
- \+ *def* eval₂_ring_hom
- \+ *def* eval
- \+ *def* is_root
- \+ *def* comp
- \+ *def* map

Created src/data/polynomial/field_division.lean
- \+ *lemma* is_unit_iff_degree_eq_zero
- \+ *lemma* degree_pos_of_ne_zero_of_nonunit
- \+ *lemma* monic_mul_leading_coeff_inv
- \+ *lemma* degree_mul_leading_coeff_inv
- \+ *lemma* div_def
- \+ *lemma* mod_def
- \+ *lemma* mod_by_monic_eq_mod
- \+ *lemma* div_by_monic_eq_div
- \+ *lemma* mod_X_sub_C_eq_C_eval
- \+ *lemma* mul_div_eq_iff_is_root
- \+ *lemma* mod_eq_self_iff
- \+ *lemma* div_eq_zero_iff
- \+ *lemma* degree_add_div
- \+ *lemma* degree_div_le
- \+ *lemma* degree_div_lt
- \+ *lemma* degree_map
- \+ *lemma* nat_degree_map
- \+ *lemma* leading_coeff_map
- \+ *lemma* map_div
- \+ *lemma* map_mod
- \+ *lemma* map_eq_zero
- \+ *lemma* exists_root_of_degree_eq_one
- \+ *lemma* coeff_inv_units
- \+ *lemma* monic_normalize
- \+ *lemma* coe_norm_unit
- \+ *lemma* degree_normalize
- \+ *lemma* prime_of_degree_eq_one
- \+ *lemma* irreducible_of_degree_eq_one
- \+ *theorem* pairwise_coprime_X_sub
- \+ *def* div
- \+ *def* mod

Created src/data/polynomial/identities.lean
- \+ *def* pow_add_expansion
- \+ *def* binom_expansion
- \+ *def* pow_sub_pow_factor
- \+ *def* eval_sub_factor

Created src/data/polynomial/induction.lean
- \+ *lemma* sum_C_mul_X_eq
- \+ *lemma* sum_monomial_eq
- \+ *lemma* finset_sum_coeff
- \+ *lemma* as_sum
- \+ *lemma* sum_over_range'
- \+ *lemma* sum_over_range
- \+ *theorem* coeff_mul_monomial
- \+ *theorem* coeff_monomial_mul
- \+ *theorem* coeff_mul_monomial_zero
- \+ *theorem* coeff_monomial_zero_mul

Created src/data/polynomial/monic.lean
- \+ *lemma* monic.as_sum
- \+ *lemma* ne_zero_of_monic_of_zero_ne_one
- \+ *lemma* ne_zero_of_ne_zero_of_monic
- \+ *lemma* monic_map
- \+ *lemma* monic_mul
- \+ *lemma* monic_pow
- \+ *lemma* is_unit_C
- \+ *lemma* eq_one_of_is_unit_of_monic
- \+ *lemma* leading_coeff_of_injective
- \+ *lemma* monic_of_injective
- \+ *lemma* not_monic_zero
- \+ *lemma* ne_zero_of_monic
- \+ *lemma* integral_normalization_coeff_degree
- \+ *lemma* integral_normalization_coeff_nat_degree
- \+ *lemma* integral_normalization_coeff_ne_degree
- \+ *lemma* integral_normalization_coeff_ne_nat_degree
- \+ *lemma* monic_integral_normalization
- \+ *lemma* support_integral_normalization
- \+ *lemma* integral_normalization_eval₂_eq_zero
- \+ *lemma* integral_normalization_aeval_eq_zero
- \+ *theorem* monic_of_degree_le
- \+ *theorem* monic_X_pow_add
- \+ *theorem* monic_X_add_C
- \+ *theorem* monic_X_sub_C
- \+ *theorem* monic_X_pow_sub

Created src/data/polynomial/monomial.lean
- \+ *lemma* monomial_zero_left
- \+ *lemma* C_0
- \+ *lemma* C_1
- \+ *lemma* C_mul
- \+ *lemma* C_add
- \+ *lemma* C_bit0
- \+ *lemma* C_bit1
- \+ *lemma* C_pow
- \+ *lemma* C_eq_nat_cast
- \+ *lemma* sum_C_index
- \+ *lemma* coeff_X_one
- \+ *lemma* coeff_X_zero
- \+ *lemma* coeff_X
- \+ *lemma* coeff_C
- \+ *lemma* coeff_C_zero
- \+ *lemma* single_eq_C_mul_X
- \+ *lemma* X_ne_zero
- \+ *theorem* nonzero.of_polynomial_ne
- \+ *def* C

Created src/data/polynomial/ring_division.lean
- \+ *lemma* nat_degree_pos_of_aeval_root
- \+ *lemma* degree_pos_of_aeval_root
- \+ *lemma* degree_mul_eq
- \+ *lemma* degree_pow_eq
- \+ *lemma* leading_coeff_mul
- \+ *lemma* leading_coeff_pow
- \+ *lemma* nat_degree_mul_eq
- \+ *lemma* nat_degree_pow_eq
- \+ *lemma* root_mul
- \+ *lemma* root_or_root_of_root_mul
- \+ *lemma* degree_le_mul_left
- \+ *lemma* exists_finset_roots
- \+ *lemma* card_roots
- \+ *lemma* card_roots'
- \+ *lemma* card_roots_sub_C
- \+ *lemma* card_roots_sub_C'
- \+ *lemma* mem_roots
- \+ *lemma* roots_mul
- \+ *lemma* mem_roots_sub_C
- \+ *lemma* roots_X_sub_C
- \+ *lemma* card_roots_X_pow_sub_C
- \+ *lemma* mem_nth_roots
- \+ *lemma* card_nth_roots
- \+ *lemma* coeff_comp_degree_mul_degree
- \+ *lemma* nat_degree_comp
- \+ *lemma* leading_coeff_comp
- \+ *lemma* degree_eq_zero_of_is_unit
- \+ *lemma* degree_coe_units
- \+ *lemma* nat_degree_coe_units
- \+ *lemma* coeff_coe_units_zero_ne_zero
- \+ *lemma* degree_eq_degree_of_associated
- \+ *lemma* degree_eq_one_of_irreducible_of_root
- \+ *lemma* prime_of_degree_eq_one_of_monic
- \+ *lemma* irreducible_of_degree_eq_one_of_monic
- \+ *lemma* polynomial
- \+ *theorem* nat_degree_le_of_dvd
- \+ *theorem* is_unit_iff
- \+ *theorem* prime_X_sub_C
- \+ *theorem* prime_X
- \+ *theorem* irreducible_X_sub_C
- \+ *theorem* irreducible_X
- \+ *def* nth_roots



## [2020-07-16 18:00:07](https://github.com/leanprover-community/mathlib/commit/6fd4f8f)
feat(meta/expr): add tactic_format instance for declaration ([#3390](https://github.com/leanprover-community/mathlib/pull/3390))
This allows you to `trace d` where `d : declaration`. Useful for debugging metaprograms.
#### Estimated changes
Modified src/meta/expr.lean




## [2020-07-16 14:24:27](https://github.com/leanprover-community/mathlib/commit/25be04a)
feat(data/nat/digits): add lemmas about digits ([#3406](https://github.com/leanprover-community/mathlib/pull/3406))
Added `lt_base_pow_length_digits`, `of_digits_lt_base_pow_length`, `of_digits_append` and `of_digits_digits_append_digits`
#### Estimated changes
Modified src/data/nat/digits.lean
- \+ *lemma* of_digits_append
- \+ *lemma* of_digits_lt_base_pow_length'
- \+ *lemma* of_digits_lt_base_pow_length
- \+ *lemma* lt_base_pow_length_digits'
- \+ *lemma* lt_base_pow_length_digits
- \+ *lemma* of_digits_digits_append_digits



## [2020-07-16 12:55:24](https://github.com/leanprover-community/mathlib/commit/a8c10e1)
chore(topology/algebra/ordered): rename `lim*_eq_of_tendsto` to `tendsto.lim*_eq` ([#3415](https://github.com/leanprover-community/mathlib/pull/3415))
Also add `tendsto_of_le_liminf_of_limsup_le`
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/measure_theory/integration.lean


Modified src/topology/algebra/ordered.lean
- \+ *theorem* tendsto_of_le_liminf_of_limsup_le
- \+ *theorem* filter.tendsto.limsup_eq
- \+ *theorem* filter.tendsto.liminf_eq
- \- *theorem* limsup_eq_of_tendsto
- \- *theorem* liminf_eq_of_tendsto



## [2020-07-16 07:53:56](https://github.com/leanprover-community/mathlib/commit/1311eb2)
feat(tactic/obviously): improve error reporting ([#3412](https://github.com/leanprover-community/mathlib/pull/3412))
If `obviously` (used for auto_params) fails, it now prints a more useful message than "chain tactic made no progress"
If the goal presented to obviously contains `sorry`, it just uses `sorry` to discard it.
#### Estimated changes
Modified src/category_theory/category/default.lean


Modified src/meta/expr.lean


Modified src/tactic/core.lean


Created src/tactic/obviously.lean




## [2020-07-16 06:45:37](https://github.com/leanprover-community/mathlib/commit/9ca3ce6)
chore(data/opposite): pp_nodot on op and unop ([#3413](https://github.com/leanprover-community/mathlib/pull/3413))
Since it's not possible to write `X.op`, its extremely unhelpful for the pretty printer to output this.
#### Estimated changes
Modified src/data/opposite.lean




## [2020-07-15 23:05:39](https://github.com/leanprover-community/mathlib/commit/c1a5ae9)
chore(order/directed): use implicit args in `iff`s ([#3411](https://github.com/leanprover-community/mathlib/pull/3411))
#### Estimated changes
Modified src/analysis/convex/cone.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid/membership.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/linear_pmap.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* Sup_eq_supr'

Modified src/order/directed.lean
- \+/\- *theorem* directed_comp

Modified src/ring_theory/subsemiring.lean


Modified src/topology/algebra/infinite_sum.lean




## [2020-07-15 16:50:18](https://github.com/leanprover-community/mathlib/commit/5fe67b7)
feat(measure_theory): preliminaries for Haar measure ([#3195](https://github.com/leanprover-community/mathlib/pull/3195))
Move properties about lattice operations on encodable types to a new file. These are generalized from lemmas in the measure theory folder, for lattice operations and not just for `ennreal`. Also move them to the `encodable` namespace.
Rename `outer_measure.Union_aux` to `encodable.Union_decode2`.
Generalize some properties for outer measures to arbitrary complete lattices. This is useful for operations that behave like outer measures on a subset of `set α`.
#### Estimated changes
Modified src/data/equiv/denumerable.lean


Renamed src/data/equiv/encodable.lean to src/data/equiv/encodable/basic.lean


Created src/data/equiv/encodable/lattice.lean
- \+ *lemma* supr_decode2
- \+ *lemma* Union_decode2
- \+ *lemma* Union_decode2_cases
- \+ *lemma* nonempty_encodable
- \+ *theorem* Union_decode2_disjoint_on

Modified src/data/rat/basic.lean


Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_compact.is_measurable

Modified src/measure_theory/measurable_space.lean
- \- *lemma* encodable.Union_decode2
- \- *lemma* encodable.Union_decode2_cases
- \- *theorem* Union_decode2_disjoint_on

Modified src/measure_theory/measure_space.lean
- \+ *lemma* exists_is_measurable_superset_of_trim_eq_zero
- \+ *lemma* trim_smul
- \+/\- *theorem* trim_zero
- \+ *theorem* smul_apply

Modified src/measure_theory/outer_measure.lean
- \+ *lemma* measure_of_eq_coe
- \+ *lemma* le_inter_add_diff
- \- *theorem* Union_aux

Modified src/order/ideal.lean


Modified src/tactic/default.lean


Modified src/topology/algebra/infinite_sum.lean
- \+ *theorem* tsum_supr_decode2
- \+ *theorem* tsum_Union_decode2
- \+ *theorem* rel_supr_tsum
- \+ *theorem* rel_supr_sum
- \+ *theorem* rel_sup_add



## [2020-07-15 13:56:45](https://github.com/leanprover-community/mathlib/commit/5f5d641)
feat(algebra/ordered_group): instances for additive/multiplicative ([#3405](https://github.com/leanprover-community/mathlib/pull/3405))
#### Estimated changes
Modified src/algebra/ordered_group.lean




## [2020-07-15 11:42:20](https://github.com/leanprover-community/mathlib/commit/a41a307)
refactor(topology/algebra/infinite_sum): review ([#3371](https://github.com/leanprover-community/mathlib/pull/3371))
## Rename
- `has_sum_unique` → `has_sum.unique`;
- `summable.summable_comp_of_injective` → `summable.comp_injective`;
- `has_sum_iff_tendsto_nat_of_summable` → `summable.has_sum_iff_tendsto_nat`;
- `tsum_eq_has_sum` → `has_sum.tsum_eq`;
- `support_comp` → `support_comp_subset`, delete `support_comp'`;
## Change arguments
- `tsum_eq_tsum_of_ne_zero_bij`, `has_sum_iff_has_sum_of_ne_zero_bij`: use functions from `support` instead of `Π x, f x ≠ 0 → β`;
## Add
- `indicator_compl_add_self_apply`, `indicator_compl_add_self`;
- `indicator_self_add_compl_apply`, `indicator_self_add_compl`;
- `support_subset_iff`, `support_subset_iff'`;
- `support_subset_comp`;
- `support_prod_mk`;
- `embedding.coe_subtype`;
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/specific_limits.lean


Modified src/data/indicator_function.lean
- \+ *lemma* indicator_compl_add_self_apply
- \+ *lemma* indicator_compl_add_self
- \+ *lemma* indicator_self_add_compl_apply
- \+ *lemma* indicator_self_add_compl
- \+/\- *lemma* indicator_compl

Modified src/data/set/basic.lean
- \+ *lemma* insert_diff_self_of_not_mem
- \+ *theorem* eq_empty_of_not_nonempty

Modified src/data/support.lean
- \+ *lemma* support_subset_iff
- \+ *lemma* support_subset_iff'
- \+ *lemma* support_comp_subset
- \+ *lemma* support_subset_comp
- \+ *lemma* support_prod_mk
- \- *lemma* support_comp
- \- *lemma* support_comp'
- \- *lemma* support_comp_eq'

Modified src/logic/embedding.lean
- \+ *lemma* coe_subtype

Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/probability_mass_function.lean
- \+/\- *lemma* tsum_coe

Modified src/measure_theory/set_integral.lean


Modified src/order/filter/at_top_bot.lean
- \+ *lemma* map_at_top_finset_prod_le_of_prod_eq
- \+ *lemma* function.injective.map_at_top_finset_prod_eq

Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* has_sum.has_sum_of_sum_eq
- \+/\- *lemma* has_sum_iff_has_sum
- \+ *lemma* function.injective.has_sum_iff
- \+ *lemma* function.injective.summable_iff
- \+ *lemma* has_sum_subtype_iff_of_support_subset
- \+ *lemma* has_sum_subtype_iff_indicator
- \+ *lemma* has_sum_subtype_support
- \+/\- *lemma* has_sum_sum_of_ne_finset_zero
- \+ *lemma* summable_of_ne_finset_zero
- \+ *lemma* summable.prod_symm
- \+ *lemma* equiv.has_sum_iff_of_support
- \+/\- *lemma* has_sum_iff_has_sum_of_ne_zero_bij
- \+ *lemma* equiv.summable_iff_of_support
- \+ *lemma* has_sum.unique
- \+ *lemma* summable.has_sum_iff_tendsto_nat
- \+ *lemma* equiv.summable_iff_of_has_sum_iff
- \+ *lemma* has_sum.add_compl
- \+ *lemma* summable.add_compl
- \+ *lemma* has_sum.compl_add
- \+ *lemma* summable.compl_add
- \+ *lemma* has_sum.prod_fiberwise
- \+/\- *lemma* summable.sigma'
- \+/\- *lemma* has_sum.sigma_of_has_sum
- \+ *lemma* has_sum.tsum_eq
- \+/\- *lemma* tsum_zero
- \+ *lemma* finset.tsum_subtype
- \+ *lemma* equiv.tsum_eq_tsum_of_has_sum_iff_has_sum
- \+/\- *lemma* tsum_eq_tsum_of_has_sum_iff_has_sum
- \+ *lemma* equiv.tsum_eq
- \+ *lemma* equiv.tsum_eq_tsum_of_support
- \+/\- *lemma* tsum_eq_tsum_of_ne_zero_bij
- \+/\- *lemma* tsum_sigma'
- \+ *lemma* tsum_prod'
- \+ *lemma* tsum_comm'
- \+/\- *lemma* has_sum.neg
- \+ *lemma* has_sum.has_sum_compl_iff
- \+ *lemma* has_sum.has_sum_iff_compl
- \+ *lemma* summable.summable_compl_iff
- \+ *lemma* set.finite.summable_compl_iff
- \+ *lemma* tsum_add_tsum_compl
- \+ *lemma* sum_add_tsum_compl
- \+/\- *lemma* summable_nat_add_iff
- \+/\- *lemma* tsum_eq_zero_add
- \+/\- *lemma* has_sum.mul_left
- \+/\- *lemma* summable.summable_of_eq_zero_or_self
- \+ *lemma* summable.comp_injective
- \+ *lemma* summable.subtype
- \+/\- *lemma* summable.sigma
- \+ *lemma* summable.prod_factor
- \+/\- *lemma* tsum_sigma
- \+ *lemma* tsum_prod
- \+ *lemma* tsum_comm
- \- *lemma* summable_sum_of_ne_finset_zero
- \- *lemma* has_sum_of_iso
- \- *lemma* has_sum_iff_has_sum_of_iso
- \- *lemma* has_sum_hom
- \- *lemma* has_sum_unique
- \- *lemma* has_sum_iff_tendsto_nat_of_summable
- \- *lemma* has_sum.has_sum_ne_zero
- \- *lemma* has_sum_iff_has_sum_of_ne_zero
- \- *lemma* summable_iff_summable_ne_zero
- \- *lemma* summable_iff_summable_ne_zero_bij
- \- *lemma* has_sum_subtype_iff_of_eq_zero
- \- *lemma* tsum_eq_has_sum
- \- *lemma* tsum_subtype_eq_sum
- \- *lemma* tsum_eq_tsum_of_ne_zero
- \- *lemma* tsum_eq_tsum_of_iso
- \- *lemma* tsum_equiv
- \- *lemma* has_sum_subtype_iff
- \- *lemma* has_sum_subtype_iff'
- \- *lemma* summable_subtype_iff
- \- *lemma* sum_add_tsum_subtype
- \- *lemma* summable.summable_comp_of_injective

Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* has_sum_coe
- \+/\- *lemma* summable_coe



## [2020-07-15 09:51:42](https://github.com/leanprover-community/mathlib/commit/503a40a)
feat(logic/basic) forall_imp ([#3391](https://github.com/leanprover-community/mathlib/pull/3391))
Added a missing lemma, which is the one-way implication version of `forall_congr`.
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* forall_imp



## [2020-07-15 05:11:12](https://github.com/leanprover-community/mathlib/commit/51a75ff)
feat(category_theory/pullback): make the is_limit helper lemmas more ergonomic ([#3398](https://github.com/leanprover-community/mathlib/pull/3398))
#### Estimated changes
Modified src/category_theory/abelian/non_preadditive.lean


Modified src/category_theory/limits/shapes/constructions/pullbacks.lean


Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* is_limit_aux
- \+ *def* is_limit_aux'
- \+/\- *def* is_limit.mk
- \+ *def* is_colimit_aux
- \+ *def* is_colimit_aux'
- \+/\- *def* is_colimit.mk
- \- *def* is_limit.mk'
- \- *def* is_colimit.mk'



## [2020-07-15 00:57:03](https://github.com/leanprover-community/mathlib/commit/8495f76)
feat(geometry/manifold/times_cont_mdiff): smooth functions between manifolds ([#3387](https://github.com/leanprover-community/mathlib/pull/3387))
We define smooth functions between smooth manifolds, and prove their basic properties (including the facts that a composition of smooth functions is smooth, and that the tangent map of a smooth map is smooth).
To avoid reproving always the same stuff in manifolds, we build a general theory of local invariant properties in the model space (i.e., properties which are local, and invariant under the structure groupoids) and show that the lift of such properties to charted spaces automatically inherit all the good behavior of the original property. We apply this general machinery to prove most basic properties of smooth functions between manifolds.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean


Modified src/data/equiv/local_equiv.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/charted_space.lean
- \+/\- *lemma* mem_groupoid_of_pregroupoid
- \+ *lemma* charted_space_self_atlas
- \+ *lemma* chart_at_self_eq
- \+ *lemma* structure_groupoid.id_mem_maximal_atlas
- \- *lemma* model_space_atlas
- \- *lemma* chart_at_model_space_eq

Created src/geometry/manifold/local_invariant_properties.lean
- \+ *lemma* lift_prop_within_at_univ
- \+ *lemma* lift_prop_on_univ
- \+ *lemma* lift_prop_within_at_indep_chart_aux
- \+ *lemma* lift_prop_within_at_indep_chart
- \+ *lemma* lift_prop_on_indep_chart
- \+ *lemma* lift_prop_within_at_inter'
- \+ *lemma* lift_prop_within_at_inter
- \+ *lemma* lift_prop_at_of_lift_prop_within_at
- \+ *lemma* lift_prop_within_at_of_lift_prop_at_of_mem_nhds
- \+ *lemma* lift_prop_on_of_locally_lift_prop_on
- \+ *lemma* lift_prop_of_locally_lift_prop_on
- \+ *lemma* lift_prop_within_at_congr
- \+ *lemma* lift_prop_within_at_congr_iff
- \+ *lemma* lift_prop_within_at_congr_of_eventually_eq
- \+ *lemma* lift_prop_within_at_congr_iff_of_eventually_eq
- \+ *lemma* lift_prop_at_congr_of_eventually_eq
- \+ *lemma* lift_prop_at_congr_iff_of_eventually_eq
- \+ *lemma* lift_prop_on_congr
- \+ *lemma* lift_prop_on_congr_iff
- \+ *lemma* lift_prop_within_at_mono
- \+ *lemma* lift_prop_within_at_of_lift_prop_at
- \+ *lemma* lift_prop_on_mono
- \+ *lemma* lift_prop_on_of_lift_prop
- \+ *lemma* lift_prop_at_of_mem_maximal_atlas
- \+ *lemma* lift_prop_on_of_mem_maximal_atlas
- \+ *lemma* lift_prop_at_symm_of_mem_maximal_atlas
- \+ *lemma* lift_prop_on_symm_of_mem_maximal_atlas
- \+ *lemma* lift_prop_at_chart
- \+ *lemma* lift_prop_on_chart
- \+ *lemma* lift_prop_at_chart_symm
- \+ *lemma* lift_prop_on_chart_symm
- \+ *lemma* lift_prop_id
- \+ *def* charted_space.lift_prop_within_at
- \+ *def* charted_space.lift_prop_on
- \+ *def* charted_space.lift_prop_at
- \+ *def* charted_space.lift_prop

Modified src/geometry/manifold/mfderiv.lean


Modified src/geometry/manifold/real_instances.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+/\- *lemma* ext_chart_preimage_inter_eq
- \+/\- *def* maximal_atlas

Created src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* times_cont_diff_within_at_local_invariant_prop
- \+ *lemma* times_cont_diff_within_at_local_invariant_prop_mono
- \+ *lemma* times_cont_diff_within_at_local_invariant_prop_id
- \+ *lemma* times_cont_mdiff.times_cont_mdiff_at
- \+ *lemma* times_cont_mdiff_within_at_univ
- \+ *lemma* times_cont_mdiff_on_univ
- \+ *lemma* times_cont_mdiff_on_iff
- \+ *lemma* times_cont_mdiff_iff
- \+ *lemma* times_cont_mdiff_within_at.of_le
- \+ *lemma* times_cont_mdiff_at.of_le
- \+ *lemma* times_cont_mdiff_on.of_le
- \+ *lemma* times_cont_mdiff.of_le
- \+ *lemma* times_cont_mdiff_within_at.of_succ
- \+ *lemma* times_cont_mdiff_at.of_succ
- \+ *lemma* times_cont_mdiff_on.of_succ
- \+ *lemma* times_cont_mdiff.of_succ
- \+ *lemma* times_cont_mdiff_within_at.continuous_within_at
- \+ *lemma* times_cont_mdiff_at.continuous_at
- \+ *lemma* times_cont_mdiff_on.continuous_on
- \+ *lemma* times_cont_mdiff.continuous
- \+ *lemma* times_cont_mdiff_within_at.mdifferentiable_within_at
- \+ *lemma* times_cont_mdiff_at.mdifferentiable_at
- \+ *lemma* times_cont_mdiff_on.mdifferentiable_on
- \+ *lemma* times_cont_mdiff.mdifferentiable
- \+ *lemma* times_cont_mdiff_within_at_top
- \+ *lemma* times_cont_mdiff_at_top
- \+ *lemma* times_cont_mdiff_on_top
- \+ *lemma* times_cont_mdiff_top
- \+ *lemma* times_cont_mdiff_within_at_iff_nat
- \+ *lemma* times_cont_mdiff_within_at.mono
- \+ *lemma* times_cont_mdiff_at.times_cont_mdiff_within_at
- \+ *lemma* times_cont_mdiff_on.mono
- \+ *lemma* times_cont_mdiff.times_cont_mdiff_on
- \+ *lemma* times_cont_mdiff_within_at_inter'
- \+ *lemma* times_cont_mdiff_within_at_inter
- \+ *lemma* times_cont_mdiff_within_at.times_cont_mdiff_at
- \+ *lemma* times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds
- \+ *lemma* times_cont_mdiff_at_iff_times_cont_mdiff_on_nhds
- \+ *lemma* times_cont_mdiff_within_at.congr
- \+ *lemma* times_cont_mdiff_within_at_congr
- \+ *lemma* times_cont_mdiff_within_at.congr_of_eventually_eq
- \+ *lemma* filter.eventually_eq.times_cont_mdiff_within_at_iff
- \+ *lemma* times_cont_mdiff_at.congr_of_eventually_eq
- \+ *lemma* filter.eventually_eq.times_cont_mdiff_at_iff
- \+ *lemma* times_cont_mdiff_on.congr
- \+ *lemma* times_cont_mdiff_on_congr
- \+ *lemma* times_cont_mdiff_on_of_locally_times_cont_mdiff_on
- \+ *lemma* times_cont_mdiff_of_locally_times_cont_mdiff_on
- \+ *lemma* times_cont_mdiff_on.comp
- \+ *lemma* times_cont_mdiff_on.comp'
- \+ *lemma* times_cont_mdiff.comp
- \+ *lemma* times_cont_mdiff_within_at.comp
- \+ *lemma* times_cont_mdiff_within_at.comp'
- \+ *lemma* times_cont_mdiff_at.comp
- \+ *lemma* times_cont_mdiff_on_of_mem_maximal_atlas
- \+ *lemma* times_cont_mdiff_on_symm_of_mem_maximal_atlas
- \+ *lemma* times_cont_mdiff_on_chart
- \+ *lemma* times_cont_mdiff_on_chart_symm
- \+ *lemma* times_cont_mdiff_id
- \+ *lemma* times_cont_mdiff_on_id
- \+ *lemma* times_cont_mdiff_at_id
- \+ *lemma* times_cont_mdiff_within_at_id
- \+ *lemma* times_cont_mdiff_const
- \+ *lemma* times_cont_mdiff_on_const
- \+ *lemma* times_cont_mdiff_at_const
- \+ *lemma* times_cont_mdiff_within_at_const
- \+ *lemma* times_cont_mdiff_within_at_iff_times_cont_diff_within_at
- \+ *lemma* times_cont_mdiff_at_iff_times_cont_diff_at
- \+ *lemma* times_cont_mdiff_on_iff_times_cont_diff_on
- \+ *lemma* times_cont_mdiff_iff_times_cont_diff
- \+ *lemma* times_cont_mdiff_on.continuous_on_tangent_map_within_aux
- \+ *lemma* times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within_aux
- \+ *theorem* times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within
- \+ *theorem* times_cont_mdiff_on.continuous_on_tangent_map_within
- \+ *theorem* times_cont_mdiff.times_cont_mdiff_tangent_map
- \+ *theorem* times_cont_mdiff.continuous_tangent_map
- \+ *def* times_cont_diff_within_at_prop
- \+ *def* times_cont_mdiff_within_at
- \+ *def* times_cont_mdiff_at
- \+ *def* times_cont_mdiff_on
- \+ *def* times_cont_mdiff

Modified src/topology/basic.lean
- \+ *lemma* filter.eventually_eq.eq_of_nhds

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_within_at.congr_mono

Modified src/topology/local_homeomorph.lean
- \+ *lemma* preimage_open_of_open
- \+ *lemma* preimage_open_of_open_symm
- \+/\- *lemma* refl_local_equiv
- \+/\- *lemma* refl_symm
- \+/\- *lemma* of_set_univ_eq_refl
- \+/\- *lemma* of_set_trans_of_set



## [2020-07-14 16:40:34](https://github.com/leanprover-community/mathlib/commit/708e481)
chore(data/set/basic): simp attribute on set.image_subset_iff ([#3394](https://github.com/leanprover-community/mathlib/pull/3394))
see discussion here with @sgouezel :
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.233387.3A.20smooth.20functions.20on.20manifolds/near/203751071
#### Estimated changes
Modified src/data/analysis/filter.lean


Modified src/data/set/basic.lean
- \+/\- *theorem* image_subset_iff

Modified src/topology/basic.lean




## [2020-07-14 15:06:30](https://github.com/leanprover-community/mathlib/commit/6c1ae3b)
chore(category_theory/natural_isomorphism): move lemmas to correct namespace, add simp lemma ([#3401](https://github.com/leanprover-community/mathlib/pull/3401))
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/natural_isomorphism.lean
- \+/\- *lemma* hom_inv_id_app
- \+/\- *lemma* inv_hom_id_app
- \- *lemma* hom_app_inv_app_id
- \- *lemma* inv_app_hom_app_id
- \+ *def* app
- \- *def* iso.app

Modified src/category_theory/opposites.lean


Modified src/category_theory/types.lean
- \+ *lemma* hom_inv_id_app_apply
- \+ *lemma* inv_hom_id_app_apply



## [2020-07-14 15:06:28](https://github.com/leanprover-community/mathlib/commit/f7825bf)
feat(algebra/polynomial): big_operators lemmas for polynomials ([#3378](https://github.com/leanprover-community/mathlib/pull/3378))
This starts a new folder algebra/polynomial. As we refactor data/polynomial.lean, much of that content should land in this folder.
#### Estimated changes
Created src/algebra/polynomial/basic.lean
- \+ *lemma* coe_aeval_eq_eval
- \+ *lemma* coeff_zero_eq_aeval_zero
- \+ *lemma* leading_coeff_hom_apply
- \+ *def* leading_coeff_hom

Created src/algebra/polynomial/big_operators.lean
- \+ *lemma* nat_degree_prod_le
- \+ *lemma* leading_coeff_prod'
- \+ *lemma* nat_degree_prod_eq'
- \+ *lemma* monic_prod_of_monic
- \+ *lemma* nat_degree_prod_eq_of_monic
- \+ *lemma* nat_degree_prod_eq
- \+ *lemma* leading_coeff_prod



## [2020-07-14 14:42:05](https://github.com/leanprover-community/mathlib/commit/bcf61df)
feat(data/qpf): uniformity iff preservation of supp ([#3388](https://github.com/leanprover-community/mathlib/pull/3388))
#### Estimated changes
Modified src/data/pfunctor/univariate/basic.lean
- \+ *theorem* liftp_iff'
- \+ *theorem* supp_eq

Modified src/data/qpf/univariate/basic.lean
- \+ *theorem* supp_preservation_iff_uniform
- \+ *theorem* supp_preservation_iff_liftp_preservation
- \+ *theorem* liftp_preservation_iff_uniform
- \+ *def* liftp_preservation
- \+ *def* supp_preservation



## [2020-07-14 14:05:54](https://github.com/leanprover-community/mathlib/commit/02f2f94)
refactor(category_theory/finite_limits): missing piece of [#3320](https://github.com/leanprover-community/mathlib/pull/3320) ([#3400](https://github.com/leanprover-community/mathlib/pull/3400))
A recent PR [#3320](https://github.com/leanprover-community/mathlib/pull/3320) did some refactoring of special shapes of limits. It seems I forgot to include `wide_pullbacks` in that refactor, so I've done that here.
#### Estimated changes
Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/category_theory/limits/shapes/wide_pullbacks.lean




## [2020-07-14 11:42:20](https://github.com/leanprover-community/mathlib/commit/a0846da)
chore(category_theory/limits/over): split a slow file ([#3399](https://github.com/leanprover-community/mathlib/pull/3399))
This was previously the last file to finish compiling when compiling `category_theory/`. This PR splits it into some smaller pieces which can compile in parallel (and some pieces now come earlier in the import hierarchy).
No change to content.
#### Estimated changes
Modified src/category_theory/connected.lean


Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/over.lean
- \- *lemma* raised_cone_lowers_to_original
- \- *def* wide_pullback_diagram_of_diagram_over
- \- *def* cones_equiv_inverse_obj
- \- *def* cones_equiv_inverse
- \- *def* cones_equiv_functor
- \- *def* cones_equiv_unit_iso
- \- *def* cones_equiv_counit_iso
- \- *def* cones_equiv
- \- *def* has_over_limit_discrete_of_wide_pullback_limit
- \- *def* over_product_of_wide_pullback
- \- *def* over_binary_product_of_pullback
- \- *def* over_products_of_wide_pullbacks
- \- *def* over_finite_products_of_finite_wide_pullbacks
- \- *def* over_has_terminal
- \- *def* nat_trans_in_over
- \- *def* raise_cone
- \- *def* raised_cone_is_limit

Created src/category_theory/limits/shapes/constructions/over/connected.lean
- \+ *lemma* raised_cone_lowers_to_original
- \+ *def* nat_trans_in_over
- \+ *def* raise_cone
- \+ *def* raised_cone_is_limit

Created src/category_theory/limits/shapes/constructions/over/default.lean


Created src/category_theory/limits/shapes/constructions/over/products.lean
- \+ *def* wide_pullback_diagram_of_diagram_over
- \+ *def* cones_equiv_inverse_obj
- \+ *def* cones_equiv_inverse
- \+ *def* cones_equiv_functor
- \+ *def* cones_equiv_unit_iso
- \+ *def* cones_equiv_counit_iso
- \+ *def* cones_equiv
- \+ *def* has_over_limit_discrete_of_wide_pullback_limit
- \+ *def* over_product_of_wide_pullback
- \+ *def* over_binary_product_of_pullback
- \+ *def* over_products_of_wide_pullbacks
- \+ *def* over_finite_products_of_finite_wide_pullbacks
- \+ *def* over_has_terminal



## [2020-07-14 11:42:18](https://github.com/leanprover-community/mathlib/commit/0fff477)
feat(analysis/normed_space): complex Hahn-Banach theorem ([#3286](https://github.com/leanprover-community/mathlib/pull/3286))
This proves the complex Hahn-Banach theorem by reducing it to the real version.
The corollaries from [#3021](https://github.com/leanprover-community/mathlib/pull/3021) should be generalized as well at some point.
#### Estimated changes
Created src/analysis/normed_space/extend.lean
- \+ *lemma* norm_bound

Modified src/analysis/normed_space/hahn_banach.lean
- \+ *theorem* complex.exists_extension_norm_eq

Modified src/data/complex/basic.lean
- \+ *lemma* of_real_smul
- \+ *lemma* I_mul
- \+ *lemma* abs_ne_zero



## [2020-07-14 11:05:58](https://github.com/leanprover-community/mathlib/commit/5f01b54)
feat(category_theory/kernels): kernel_iso_of_eq ([#3372](https://github.com/leanprover-community/mathlib/pull/3372))
This provides two useful isomorphisms when working with abstract (co)kernels:
```
def kernel_zero_iso_source [has_kernel (0 : X ⟶ Y)] : kernel (0 : X ⟶ Y) ≅ X :=
def kernel_iso_of_eq {f g : X ⟶ Y} [has_kernel f] [has_kernel g] (h : f = g) : kernel f ≅ kernel g :=
```
and some associated simp lemmas.
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+ *lemma* has_colimit.iso_of_nat_iso_ι_hom
- \- *lemma* has_colimit.iso_of_nat_iso_hom_π

Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* equalizer.iso_source_of_self_hom
- \+ *lemma* equalizer.iso_source_of_self_inv
- \+ *lemma* coequalizer.iso_target_of_self_hom
- \+ *lemma* coequalizer.iso_target_of_self_inv
- \+ *def* equalizer.iso_source_of_self
- \+ *def* coequalizer.iso_target_of_self
- \- *def* equalizer.ι_of_self
- \- *def* coequalizer.π_of_self

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* kernel_zero_iso_source_hom
- \+ *lemma* kernel_zero_iso_source_inv
- \+ *lemma* kernel_iso_of_eq_refl
- \+ *lemma* kernel_iso_of_eq_trans
- \+ *lemma* cokernel_zero_iso_target_hom
- \+ *lemma* cokernel_zero_iso_target_inv
- \+ *lemma* cokernel_iso_of_eq_refl
- \+ *lemma* cokernel_iso_of_eq_trans
- \+ *def* kernel_zero_iso_source
- \+ *def* kernel_iso_of_eq
- \+ *def* cokernel_zero_iso_target
- \+ *def* cokernel_iso_of_eq



## [2020-07-14 09:01:17](https://github.com/leanprover-community/mathlib/commit/58dde5b)
chore(*): generalize tensor product to semirings ([#3389](https://github.com/leanprover-community/mathlib/pull/3389))
#### Estimated changes
Modified src/data/polynomial.lean


Modified src/linear_algebra/tensor_product.lean
- \+/\- *lemma* zero_tmul
- \+/\- *lemma* tmul_zero
- \+ *lemma* lift_aux_tmul
- \+/\- *lemma* lift_aux.smul
- \+/\- *lemma* neg_tmul
- \+/\- *lemma* tmul_neg
- \- *lemma* lift_aux.add
- \+ *theorem* smul.aux_of
- \+ *theorem* smul_tmul'
- \+/\- *theorem* ext
- \+/\- *def* tmul
- \+/\- *def* smul.aux
- \+/\- *def* lift_aux
- \- *def* relators

Modified src/ring_theory/matrix_algebra.lean


Modified src/ring_theory/polynomial_algebra.lean


Modified src/ring_theory/tensor_product.lean




## [2020-07-14 01:25:26](https://github.com/leanprover-community/mathlib/commit/0410946)
chore(linear_algebra/nonsingular_inverse): swap update_row/column names ([#3393](https://github.com/leanprover-community/mathlib/pull/3393))
The names for `update_row` and `update_column` did not correspond to their definitions. Doing a global swap of the names keep all the proofs valid and makes the semantics match.
#### Estimated changes
Modified src/linear_algebra/nonsingular_inverse.lean
- \+/\- *lemma* update_row_self
- \+/\- *lemma* update_column_self
- \+/\- *lemma* update_row_ne
- \+/\- *lemma* update_column_ne
- \+/\- *lemma* update_row_val
- \+/\- *lemma* update_column_val
- \+ *lemma* update_row_transpose
- \+/\- *lemma* cramer_apply
- \- *lemma* update_column_transpose
- \+/\- *def* update_row
- \+/\- *def* update_column
- \+/\- *def* cramer_map



## [2020-07-13 20:57:57](https://github.com/leanprover-community/mathlib/commit/32c75d0)
feat(linear_algebra/affine_space): more lemmas on directions of affine subspaces ([#3377](https://github.com/leanprover-community/mathlib/pull/3377))
Add more lemmas on directions of affine subspaces, motivated by uses
for Euclidean geometry.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *lemma* coe_direction_eq_vsub_set_right
- \+ *lemma* coe_direction_eq_vsub_set_left
- \+ *lemma* mem_direction_iff_eq_vsub_right
- \+ *lemma* mem_direction_iff_eq_vsub_left
- \+ *lemma* vsub_right_mem_direction_iff_mem
- \+ *lemma* vsub_left_mem_direction_iff_mem
- \+ *lemma* direction_le
- \+ *lemma* direction_lt_of_nonempty
- \+ *lemma* sup_direction_le
- \+ *lemma* sup_direction_lt_of_nonempty_of_inter_empty
- \+ *lemma* inter_nonempty_of_nonempty_of_sup_direction_eq_top
- \+ *lemma* inter_eq_singleton_of_nonempty_of_is_compl



## [2020-07-13 20:02:35](https://github.com/leanprover-community/mathlib/commit/1132237)
feat(ring_theory/ideal_over): lemmas for nonzero ideals lying over nonzero ideals ([#3385](https://github.com/leanprover-community/mathlib/pull/3385))
Let `f` be a ring homomorphism from `R` to `S` and `I` be an ideal in `S`. To show that `I.comap f` is not the zero ideal, we can show `I` contains a non-zero root of some non-zero polynomial `p : polynomial R`. As a corollary, if `S` is algebraic over `R` (e.g. the integral closure of `R`), nonzero ideals in `S` lie over nonzero ideals in `R`.
I created a new file because `integral_closure.comap_ne_bot` depends on `comap_ne_bot_of_algebraic_mem`, but `ring_theory/algebraic.lean` imports `ring_theory/integral_closure.lean` and I didn't see any obvious join in the dependency graph where they both belonged.
#### Estimated changes
Modified src/linear_algebra/basic.lean


Created src/ring_theory/ideal_over.lean
- \+ *lemma* coeff_zero_mem_comap_of_root_mem
- \+ *lemma* exists_coeff_ne_zero_mem_comap_of_root_mem
- \+ *lemma* comap_ne_bot_of_root_mem
- \+ *lemma* comap_ne_bot_of_algebraic_mem
- \+ *lemma* comap_ne_bot_of_integral_mem
- \+ *lemma* integral_closure.comap_ne_bot
- \+ *lemma* integral_closure.eq_bot_of_comap_eq_bot

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* integral_closure.is_integral



## [2020-07-13 19:35:16](https://github.com/leanprover-community/mathlib/commit/45477c8)
feat(analysis/normed_space/real_inner_product): orthogonal subspaces ([#3369](https://github.com/leanprover-community/mathlib/pull/3369))
Define the subspace of vectors orthogonal to a given subspace and
prove some basic properties of it, building on the existing results
about minimizers.  This is in preparation for doing similar things in
Euclidean geometry (working with the affine subspace through a given
point and orthogonal to a given affine subspace, for example).
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* submodule.mem_orthogonal
- \+ *lemma* submodule.mem_orthogonal'
- \+ *lemma* submodule.inner_right_of_mem_orthogonal
- \+ *lemma* submodule.inner_left_of_mem_orthogonal
- \+ *lemma* submodule.orthogonal_disjoint
- \+ *lemma* submodule.le_orthogonal_orthogonal
- \+ *lemma* submodule.sup_orthogonal_of_is_complete
- \+ *lemma* submodule.is_compl_orthogonal_of_is_complete
- \+ *def* submodule.orthogonal



## [2020-07-13 19:01:01](https://github.com/leanprover-community/mathlib/commit/2ae7ad8)
feat(functor): definition multivariate functors ([#3360](https://github.com/leanprover-community/mathlib/pull/3360))
One part of [#3317](https://github.com/leanprover-community/mathlib/pull/3317)
#### Estimated changes
Created src/control/functor/multivariate.lean
- \+ *lemma* id_map
- \+ *lemma* id_map'
- \+ *lemma* map_map
- \+ *lemma* exists_iff_exists_of_mono
- \+ *lemma* liftp_def
- \+ *lemma* liftr_def
- \+ *lemma* liftp_last_pred_iff
- \+ *lemma* liftr_last_rel_iff
- \+ *theorem* of_mem_supp
- \+ *def* liftp
- \+ *def* liftr
- \+ *def* supp
- \+ *def* liftp'
- \+ *def* liftr'

Created src/data/fin2.lean
- \+ *def* elim0
- \+ *def* to_nat
- \+ *def* opt_of_nat
- \+ *def* add
- \+ *def* left
- \+ *def* insert_perm
- \+ *def* remap_left
- \+ *def* of_nat'

Created src/data/typevec.lean
- \+ *lemma* append_fun_comp
- \+ *lemma* append_fun_comp'
- \+ *lemma* nil_fun_comp
- \+ *lemma* typevec_cases_nil₂_append_fun
- \+ *lemma* typevec_cases_cons₂_append_fun
- \+ *lemma* const_append1
- \+ *lemma* eq_nil_fun
- \+ *lemma* id_eq_nil_fun
- \+ *lemma* const_nil
- \+ *lemma* repeat_eq_append1
- \+ *lemma* repeat_eq_nil
- \+ *lemma* const_iff_true
- \+ *lemma* repeat_eq_iff_eq
- \+ *lemma* subtype_val_nil
- \+ *lemma* diag_sub_val
- \+ *lemma* prod_id
- \+ *lemma* append_prod_append_fun
- \+ *theorem* id_comp
- \+ *theorem* comp_id
- \+ *theorem* comp_assoc
- \+ *theorem* drop_append1
- \+ *theorem* drop_append1'
- \+ *theorem* last_append1
- \+ *theorem* append1_drop_last
- \+ *theorem* append1_cases_append1
- \+ *theorem* eq_of_drop_last_eq
- \+ *theorem* drop_fun_split_fun
- \+ *theorem* last_fun_split_fun
- \+ *theorem* drop_fun_append_fun
- \+ *theorem* last_fun_append_fun
- \+ *theorem* split_drop_fun_last_fun
- \+ *theorem* split_fun_inj
- \+ *theorem* append_fun_inj
- \+ *theorem* split_fun_comp
- \+ *theorem* append_fun_comp_split_fun
- \+ *theorem* append_fun_comp_id
- \+ *theorem* drop_fun_comp
- \+ *theorem* last_fun_comp
- \+ *theorem* append_fun_aux
- \+ *theorem* append_fun_id_id
- \+ *theorem* fst_prod_mk
- \+ *theorem* snd_prod_mk
- \+ *theorem* fst_diag
- \+ *theorem* snd_diag
- \+ *def* typevec
- \+ *def* arrow
- \+ *def* id
- \+ *def* comp
- \+ *def* append1
- \+ *def* drop
- \+ *def* last
- \+ *def* append1_cases
- \+ *def* split_fun
- \+ *def* append_fun
- \+ *def* drop_fun
- \+ *def* last_fun
- \+ *def* nil_fun
- \+ *def* arrow.mp
- \+ *def* arrow.mpr
- \+ *def* to_append1_drop_last
- \+ *def* typevec_cases_nil₃
- \+ *def* typevec_cases_cons₃
- \+ *def* typevec_cases_nil₂
- \+ *def* typevec_cases_cons₂
- \+ *def* pred_last
- \+ *def* rel_last
- \+ *def* repeat
- \+ *def* prod
- \+ *def* repeat_eq
- \+ *def* pred_last'
- \+ *def* rel_last'
- \+ *def* curry
- \+ *def* drop_repeat
- \+ *def* of_repeat
- \+ *def* prod.fst
- \+ *def* prod.snd
- \+ *def* prod.diag
- \+ *def* prod.mk
- \+ *def* subtype_
- \+ *def* subtype_val
- \+ *def* to_subtype
- \+ *def* of_subtype
- \+ *def* to_subtype'
- \+ *def* of_subtype'
- \+ *def* diag_sub

Modified src/number_theory/dioph.lean
- \- *def* elim0
- \- *def* to_nat
- \- *def* opt_of_nat
- \- *def* add
- \- *def* left
- \- *def* insert_perm
- \- *def* remap_left
- \- *def* of_nat'



## [2020-07-13 12:37:11](https://github.com/leanprover-community/mathlib/commit/f034899)
feat(data/equiv/mul_add): conj as a mul_aut ([#3367](https://github.com/leanprover-community/mathlib/pull/3367))
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *lemma* mul_def
- \+ *lemma* one_def
- \+ *lemma* inv_def
- \+ *lemma* mul_apply
- \+ *lemma* one_apply
- \+ *lemma* conj_apply
- \+ *lemma* conj_symm_apply
- \+ *def* conj

Modified src/group_theory/semidirect_product.lean




## [2020-07-13 09:46:22](https://github.com/leanprover-community/mathlib/commit/e26b459)
feat(data/polynomial): some lemmas about eval2 and algebra_map ([#3382](https://github.com/leanprover-community/mathlib/pull/3382))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* C_eq_algebra_map
- \+ *lemma* alg_hom_eval₂_algebra_map
- \+ *lemma* eval₂_algebra_map_X
- \+ *lemma* ring_hom_eval₂_algebra_map_int
- \+ *lemma* eval₂_algebra_map_int_X

Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra_ext
- \+ *def* ring_hom.to_int_alg_hom



## [2020-07-13 08:17:18](https://github.com/leanprover-community/mathlib/commit/792faae)
chore(data/polynomial): missing a simp attribute ([#3381](https://github.com/leanprover-community/mathlib/pull/3381))
#### Estimated changes
Modified src/data/polynomial.lean




## [2020-07-13 08:17:16](https://github.com/leanprover-community/mathlib/commit/afa534c)
chore(tactic/show_term): use Try this: ([#3374](https://github.com/leanprover-community/mathlib/pull/3374))
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/show_term.lean


Modified src/tactic/suggest.lean




## [2020-07-12 23:29:02](https://github.com/leanprover-community/mathlib/commit/eb851ae)
chore(data/nat/prime): @[pp_nodot] nat.prime ([#3379](https://github.com/leanprover-community/mathlib/pull/3379))
#### Estimated changes
Modified src/data/nat/prime.lean




## [2020-07-12 10:32:15](https://github.com/leanprover-community/mathlib/commit/a8d6bdf)
feat(algebra/category/AddCommGroup): has_image_maps ([#3366](https://github.com/leanprover-community/mathlib/pull/3366))
#### Estimated changes
Modified src/algebra/category/Group/images.lean
- \+ *lemma* image_map

Modified src/category_theory/arrow.lean
- \+ *def* map_arrow

Modified src/category_theory/limits/types.lean
- \+ *lemma* image_map



## [2020-07-12 09:02:34](https://github.com/leanprover-community/mathlib/commit/fa6c45a)
feat(data/polynomial): simp lemmas for bit0 / bit1 ([#3376](https://github.com/leanprover-community/mathlib/pull/3376))
Add lemmas on polynomials and bit0/bit1 (as suggested [here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Eval.20of.20constant.20polynomial))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* C_bit0
- \+ *lemma* C_bit1
- \+ *lemma* eval₂_bit0
- \+ *lemma* eval₂_bit1
- \+ *lemma* eval_bit0
- \+ *lemma* eval_bit1



## [2020-07-12 07:43:26](https://github.com/leanprover-community/mathlib/commit/4e603f4)
feat(geometry/manifold/charted_space):  typeclass `closed_under_restriction` for structure groupoids ([#3347](https://github.com/leanprover-community/mathlib/pull/3347))
* Define a typeclass `closed_under_restriction` for structure groupoids.
* Prove that it is equivalent to requiring that the structure groupoid contain all local homeomorphisms equivalent to the restriction of the identity to an open subset.
* Verify that `continuous_groupoid` and `times_cont_diff_groupoid` satisfy `closed_under_restriction`.  
* Show that a charted space defined by a single chart is `has_groupoid` for any structure groupoid satisfying `closed_under_restriction`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Restriction.20in.20structure.20groupoid)
#### Estimated changes
Modified src/geometry/manifold/charted_space.lean
- \+ *lemma* id_restr_groupoid_mem
- \+ *lemma* closed_under_restriction_iff_id_le
- \+ *lemma* singleton_charted_space_one_chart
- \+ *lemma* singleton_has_groupoid
- \+ *def* id_restr_groupoid
- \+ *def* singleton_charted_space

Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/topology/local_homeomorph.lean
- \+ *lemma* of_set_univ_eq_refl
- \+ *lemma* of_set_trans_of_set



## [2020-07-12 05:07:52](https://github.com/leanprover-community/mathlib/commit/0e1c2bc)
feat(algebra/add_torsor): more cancellation lemmas ([#3368](https://github.com/leanprover-community/mathlib/pull/3368))
Add more cancellation lemmas for `vsub`, similar to lemmas already
present for `vadd`.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* vsub_left_cancel
- \+ *lemma* vsub_left_cancel_iff
- \+ *lemma* vsub_right_cancel
- \+ *lemma* vsub_right_cancel_iff



## [2020-07-12 03:42:43](https://github.com/leanprover-community/mathlib/commit/b047396)
feat(data/set/finite): add a version of `prod_preimage` for `inj_on` ([#3342](https://github.com/leanprover-community/mathlib/pull/3342))
* rename `finset.prod_preimage` to `finset.prod_preimage_of_bij`;
* new `prod_preimage` assumes `∀ x ∈ s, x ∉ range f, g x = 1`;
* rename `finset.image_preimage` to `finset.image_preimage_of_bij`;
* new `finset.image_preimage` says
  `image f (preimage s hf) = s.filter (λ x, x ∈ set.range f)`;
* change the order of implicit arguments in the definition of `set.inj_on`;
* add `prod_filter_of_ne`;
* use `coe` instead of `subtype.val` in `prod_attach`;
* add `finset.image_subset_iff`, `finset.image_subset_iff_subset_preimage`,
  `finset.map_subset_iff_subset_preimage`.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_filter_of_ne
- \+/\- *lemma* prod_attach

Modified src/data/finset/basic.lean
- \+ *theorem* image_subset_iff

Modified src/data/finsupp.lean


Modified src/data/set/countable.lean


Modified src/data/set/finite.lean
- \+ *lemma* image_subset_iff_subset_preimage
- \+ *lemma* map_subset_iff_subset_preimage
- \+/\- *lemma* image_preimage
- \+ *lemma* image_preimage_of_bij
- \+ *lemma* prod_preimage_of_bij

Modified src/data/set/function.lean
- \+ *theorem* surj_on.subset_range
- \+ *theorem* bij_on.subset_range

Modified src/linear_algebra/basis.lean


Modified src/logic/function/basic.lean
- \+/\- *theorem* inv_fun_on_eq'

Modified src/ring_theory/noetherian.lean




## [2020-07-12 00:42:49](https://github.com/leanprover-community/mathlib/commit/298caa0)
chore(scripts): update nolints.txt ([#3370](https://github.com/leanprover-community/mathlib/pull/3370))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-11 10:11:11](https://github.com/leanprover-community/mathlib/commit/d7ac180)
feat(data/fintype/basic): set.to_finset_empty ([#3361](https://github.com/leanprover-community/mathlib/pull/3361))
Add set.to_finset_empty, analogously to set.to_finset_univ.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* set.to_finset_empty



## [2020-07-11 10:11:09](https://github.com/leanprover-community/mathlib/commit/34d3fe1)
chore(category_theory/comma): split into three files ([#3358](https://github.com/leanprover-community/mathlib/pull/3358))
Just reorganisation.
#### Estimated changes
Created src/category_theory/arrow.lean
- \+ *lemma* id_left
- \+ *lemma* id_right
- \+ *lemma* w
- \+ *lemma* lift.fac_left
- \+ *lemma* lift.fac_right
- \+ *lemma* lift_mk'_left
- \+ *lemma* lift_mk'_right
- \+ *def* arrow
- \+ *def* mk
- \+ *def* hom_mk
- \+ *def* hom_mk'

Modified src/category_theory/comma.lean
- \- *lemma* over_morphism.ext
- \- *lemma* over_right
- \- *lemma* id_left
- \- *lemma* comp_left
- \- *lemma* w
- \- *lemma* mk_left
- \- *lemma* mk_hom
- \- *lemma* forget_obj
- \- *lemma* forget_map
- \- *lemma* map_obj_left
- \- *lemma* map_obj_hom
- \- *lemma* map_map_left
- \- *lemma* iterated_slice_forward_forget
- \- *lemma* iterated_slice_backward_forget_forget
- \- *lemma* under_morphism.ext
- \- *lemma* under_left
- \- *lemma* id_right
- \- *lemma* comp_right
- \- *lemma* map_obj_right
- \- *lemma* map_map_right
- \- *lemma* lift.fac_left
- \- *lemma* lift.fac_right
- \- *lemma* lift_mk'_left
- \- *lemma* lift_mk'_right
- \- *def* over
- \- *def* mk
- \- *def* hom_mk
- \- *def* forget
- \- *def* map
- \- *def* iterated_slice_forward
- \- *def* iterated_slice_backward
- \- *def* iterated_slice_equiv
- \- *def* post
- \- *def* under
- \- *def* arrow
- \- *def* hom_mk'

Modified src/category_theory/elements.lean


Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/shapes/strong_epi.lean


Created src/category_theory/over.lean
- \+ *lemma* over_morphism.ext
- \+ *lemma* over_right
- \+ *lemma* id_left
- \+ *lemma* comp_left
- \+ *lemma* w
- \+ *lemma* mk_left
- \+ *lemma* mk_hom
- \+ *lemma* forget_obj
- \+ *lemma* forget_map
- \+ *lemma* map_obj_left
- \+ *lemma* map_obj_hom
- \+ *lemma* map_map_left
- \+ *lemma* iterated_slice_forward_forget
- \+ *lemma* iterated_slice_backward_forget_forget
- \+ *lemma* under_morphism.ext
- \+ *lemma* under_left
- \+ *lemma* id_right
- \+ *lemma* comp_right
- \+ *lemma* map_obj_right
- \+ *lemma* map_map_right
- \+ *def* over
- \+ *def* mk
- \+ *def* hom_mk
- \+ *def* forget
- \+ *def* map
- \+ *def* iterated_slice_forward
- \+ *def* iterated_slice_backward
- \+ *def* iterated_slice_equiv
- \+ *def* post
- \+ *def* under



## [2020-07-11 08:43:40](https://github.com/leanprover-community/mathlib/commit/f742a3d)
refactor(tactic/push_neg): simp ¬ (p ∧ q) better ([#3362](https://github.com/leanprover-community/mathlib/pull/3362))
This simplifies `¬ (p ∧ q)` to `(p → ¬ q)` instead of `¬ p ∨ ¬ q`. This has better behavior when going between `\forall x, P -> Q` and `\exists x, P /\ Q'` where `Q` and `Q'` are opposite.
#### Estimated changes
Modified src/data/pequiv.lean


Modified src/order/filter/at_top_bot.lean


Modified src/tactic/push_neg.lean
- \+/\- *theorem* not_and_eq

Modified src/topology/instances/ennreal.lean


Modified src/topology/sequences.lean




## [2020-07-11 08:43:39](https://github.com/leanprover-community/mathlib/commit/36a25d9)
feat(algebra/category/*): get rid of the local reducible hack ([#3354](https://github.com/leanprover-community/mathlib/pull/3354))
I thought I did this back in April, but apparently never made the PR.
We currently use a strange hack when setting up concrete categories, making them locally reducible. There's a library note about this, which ends:
```
TODO: Probably @[derive] should be able to create instances of the	
required form (without `id`), and then we could use that instead of	
this obscure `local attribute [reducible]` method.
```
This PR makes the small change required to `delta_instance` to make this happen, and then stops using the hack in setting up concrete categories (and deletes the library note explaining this hack).
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/computability/halting.lean


Modified src/linear_algebra/finsupp.lean


Modified src/measure_theory/category/Meas.lean
- \+/\- *def* Meas

Modified src/tactic/basic.lean


Modified src/tactic/core.lean
- \- *def* new_int

Created src/tactic/delta_instance.lean
- \+ *def* new_int

Created src/tactic/fix_by_cases.lean


Modified src/tactic/omega/coeffs.lean


Modified src/topology/category/Top/basic.lean
- \+/\- *def* Top

Modified src/topology/category/UniformSpace.lean
- \+/\- *def* UniformSpace



## [2020-07-11 07:58:56](https://github.com/leanprover-community/mathlib/commit/75b9cfa)
feat(category/has_shift): missing simp lemmas ([#3365](https://github.com/leanprover-community/mathlib/pull/3365))
#### Estimated changes
Modified src/category_theory/graded_object.lean
- \+ *lemma* shift_functor_obj_apply
- \+ *lemma* shift_functor_map_apply



## [2020-07-11 07:58:54](https://github.com/leanprover-community/mathlib/commit/f669a78)
chore(category_theory/functor): explain how to type 𝟭 ([#3364](https://github.com/leanprover-community/mathlib/pull/3364))
#### Estimated changes
Modified docs/tutorial/category_theory/intro.lean


Modified src/category_theory/functor.lean




## [2020-07-11 06:47:13](https://github.com/leanprover-community/mathlib/commit/574dac5)
feat(tactic/interval_cases): add `with h` option ([#3353](https://github.com/leanprover-community/mathlib/pull/3353))
closes [#2881](https://github.com/leanprover-community/mathlib/pull/2881)
#### Estimated changes
Modified src/tactic/interval_cases.lean


Modified test/interval_cases.lean




## [2020-07-11 00:41:45](https://github.com/leanprover-community/mathlib/commit/5ddbdc1)
chore(scripts): update nolints.txt ([#3363](https://github.com/leanprover-community/mathlib/pull/3363))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-10 19:01:46](https://github.com/leanprover-community/mathlib/commit/1aff3af)
feat(interactive_expr): bigger accomplishment ([#3359](https://github.com/leanprover-community/mathlib/pull/3359))
Lean is difficult, we need more incentives.
#### Estimated changes
Modified src/tactic/interactive_expr.lean




## [2020-07-10 17:35:22](https://github.com/leanprover-community/mathlib/commit/960fc8e)
feat(data/univariate/qpf): compositional data type framework for (co)inductive types ([#3325](https://github.com/leanprover-community/mathlib/pull/3325))
Define univariate QPFs (quotients of polynomial functors).  This is the first part of [#3317](https://github.com/leanprover-community/mathlib/pull/3317).
#### Estimated changes
Modified docs/references.bib


Modified src/control/functor.lean
- \+ *theorem* of_mem_supp
- \+ *def* liftp
- \+ *def* liftr
- \+ *def* supp

Created src/data/pfunctor/univariate/M.lean
- \+ *lemma* cofix_a_eq_zero
- \+ *lemma* approx_eta
- \+ *lemma* agree_trival
- \+ *lemma* agree_children
- \+ *lemma* truncate_eq_of_agree
- \+ *lemma* P_corec
- \+ *lemma* head_succ'
- \+ *lemma* M.default_consistent
- \+ *lemma* ext'
- \+ *lemma* head_succ
- \+ *lemma* head_eq_head'
- \+ *lemma* head'_eq_head
- \+ *lemma* truncate_approx
- \+ *lemma* dest_mk
- \+ *lemma* mk_dest
- \+ *lemma* mk_inj
- \+ *lemma* approx_mk
- \+ *lemma* agree'_refl
- \+ *lemma* agree_iff_agree'
- \+ *lemma* cases_mk
- \+ *lemma* cases_on_mk
- \+ *lemma* cases_on_mk'
- \+ *lemma* is_path_cons
- \+ *lemma* is_path_cons'
- \+ *lemma* iselect_eq_default
- \+ *lemma* head_mk
- \+ *lemma* children_mk
- \+ *lemma* ichildren_mk
- \+ *lemma* isubtree_cons
- \+ *lemma* iselect_nil
- \+ *lemma* iselect_cons
- \+ *lemma* corec_def
- \+ *lemma* ext_aux
- \+ *lemma* ext
- \+ *lemma* R_is_bisimulation
- \+ *lemma* coinduction
- \+ *lemma* coinduction'
- \+ *lemma* dest_corec
- \+ *lemma* bisim
- \+ *theorem* nth_of_bisim
- \+ *theorem* eq_of_bisim
- \+ *theorem* bisim'
- \+ *theorem* bisim_equiv
- \+ *theorem* corec_unique
- \+ *def* head'
- \+ *def* children'
- \+ *def* all_agree
- \+ *def* truncate
- \+ *def* s_corec
- \+ *def* path
- \+ *def* M
- \+ *def* head
- \+ *def* children
- \+ *def* ichildren
- \+ *def* dest
- \+ *def* isubtree
- \+ *def* iselect
- \+ *def* corec_on
- \+ *def* corec₁
- \+ *def* corec'

Created src/data/pfunctor/univariate/basic.lean
- \+ *lemma* fst_map
- \+ *lemma* iget_map
- \+ *theorem* W.dest_mk
- \+ *theorem* W.mk_dest
- \+ *theorem* liftp_iff
- \+ *theorem* liftr_iff
- \+ *def* obj
- \+ *def* map
- \+ *def* W
- \+ *def* W.dest
- \+ *def* W.mk
- \+ *def* Idx
- \+ *def* obj.iget
- \+ *def* comp
- \+ *def* comp.mk
- \+ *def* comp.get

Created src/data/pfunctor/univariate/default.lean


Created src/data/qpf/univariate/basic.lean
- \+ *theorem* id_map
- \+ *theorem* comp_map
- \+ *theorem* is_lawful_functor
- \+ *theorem* liftp_iff
- \+ *theorem* liftp_iff'
- \+ *theorem* liftr_iff
- \+ *theorem* recF_eq
- \+ *theorem* recF_eq'
- \+ *theorem* recF_eq_of_Wequiv
- \+ *theorem* Wequiv.abs'
- \+ *theorem* Wequiv.refl
- \+ *theorem* Wequiv.symm
- \+ *theorem* Wrepr_equiv
- \+ *theorem* fix.rec_eq
- \+ *theorem* fix.ind_aux
- \+ *theorem* fix.ind_rec
- \+ *theorem* fix.rec_unique
- \+ *theorem* fix.mk_dest
- \+ *theorem* fix.dest_mk
- \+ *theorem* fix.ind
- \+ *theorem* corecF_eq
- \+ *theorem* cofix.dest_corec
- \+ *theorem* cofix.bisim_rel
- \+ *theorem* cofix.bisim
- \+ *theorem* cofix.bisim'
- \+ *theorem* mem_supp
- \+ *theorem* supp_eq
- \+ *theorem* has_good_supp_iff
- \+ *theorem* supp_eq_of_is_uniform
- \+ *theorem* liftp_iff_of_is_uniform
- \+ *theorem* supp_map
- \+ *def* recF
- \+ *def* Wrepr
- \+ *def* W_setoid
- \+ *def* fix
- \+ *def* fix.rec
- \+ *def* fix_to_W
- \+ *def* fix.mk
- \+ *def* fix.dest
- \+ *def* corecF
- \+ *def* is_precongr
- \+ *def* Mcongr
- \+ *def* cofix
- \+ *def* cofix.corec
- \+ *def* cofix.dest
- \+ *def* comp
- \+ *def* quotient_qpf
- \+ *def* is_uniform

Modified src/data/quot.lean
- \+ *lemma* factor_mk_eq
- \+ *def* factor

Modified src/data/sigma/basic.lean
- \+ *lemma* ext

Modified src/tactic/ext.lean


Created test/qpf.lean
- \+ *lemma* equivalence_foo.R
- \+ *lemma* foo.map_mk
- \+ *lemma* foo.map_mk'
- \+ *lemma* foo.map_tt
- \+ *lemma* supp_mk_ff₀
- \+ *lemma* supp_mk_ff₁
- \+ *lemma* foo_not_uniform
- \+ *lemma* supp_mk_tt
- \+ *lemma* supp_mk_ff'
- \+ *lemma* supp_mk_tt'
- \+ *def* box
- \+ *def* supp'
- \+ *def* liftp'
- \+ *def* prod.pfunctor
- \+ *def* foo.R
- \+ *def* foo
- \+ *def* foo.map
- \+ *def* foo.mk



## [2020-07-10 12:28:46](https://github.com/leanprover-community/mathlib/commit/d1e63f3)
chore(category_theory/limits): remove an unnecessary import ([#3357](https://github.com/leanprover-community/mathlib/pull/3357))
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean




## [2020-07-10 12:28:40](https://github.com/leanprover-community/mathlib/commit/699c915)
feat(number_theory): pythagorean triples ([#3200](https://github.com/leanprover-community/mathlib/pull/3200))
The classification of pythagorean triples (one of the "100 theorems")
#### Estimated changes
Modified src/algebra/gcd_domain.lean
- \+ *lemma* int.prime.dvd_mul
- \+ *lemma* int.prime.dvd_mul'
- \+ *lemma* prime_two_or_dvd_of_dvd_two_mul_pow_self_two
- \+ *theorem* gcd_div_gcd_div_gcd
- \+ *theorem* ne_zero_of_gcd
- \+ *theorem* exists_gcd_one
- \+ *theorem* exists_gcd_one'
- \+ *theorem* pow_dvd_pow_iff

Modified src/algebra/group_power.lean
- \+ *lemma* pow_two_sub_pow_two
- \+ *lemma* eq_or_eq_neg_of_pow_two_eq_pow_two
- \+ *theorem* pow_dvd_pow_of_dvd
- \+ *theorem* pow_two_pos_of_ne_zero

Modified src/data/int/basic.lean
- \+ *lemma* sub_mod

Modified src/data/int/gcd.lean
- \+ *lemma* prime.dvd_nat_abs_of_coe_dvd_pow_two

Modified src/data/nat/prime.lean
- \+ *theorem* prime.not_coprime_iff_dvd

Modified src/data/rat/basic.lean
- \+ *lemma* num_div_eq_of_coprime
- \+ *lemma* denom_div_eq_of_coprime
- \+ *lemma* div_int_inj

Created src/number_theory/pythagorean_triples.lean
- \+ *lemma* pythagorean_triple_comm
- \+ *lemma* pythagorean_triple.zero
- \+ *lemma* eq
- \+ *lemma* symm
- \+ *lemma* mul
- \+ *lemma* mul_iff
- \+ *lemma* mul_is_classified
- \+ *lemma* even_odd_of_coprime
- \+ *lemma* gcd_dvd
- \+ *lemma* normalize
- \+ *lemma* is_classified_of_is_primitive_classified
- \+ *lemma* is_classified_of_normalize_is_primitive_classified
- \+ *lemma* ne_zero_of_coprime
- \+ *lemma* is_primitive_classified_of_coprime_of_zero_left
- \+ *lemma* coprime_of_coprime
- \+ *lemma* circle_equiv_apply
- \+ *lemma* circle_equiv_symm_apply
- \+ *lemma* is_primitive_classified_aux
- \+ *theorem* is_primitive_classified_of_coprime_of_odd_of_pos
- \+ *theorem* is_primitive_classified_of_coprime_of_pos
- \+ *theorem* is_primitive_classified_of_coprime
- \+ *theorem* classified
- \+ *theorem* coprime_classification
- \+ *theorem* classification
- \+ *def* pythagorean_triple
- \+ *def* is_classified
- \+ *def* is_primitive_classified
- \+ *def* circle_equiv_gen



## [2020-07-10 11:15:29](https://github.com/leanprover-community/mathlib/commit/e52108d)
chore(data/int/basic): move content requiring advanced imports ([#3334](https://github.com/leanprover-community/mathlib/pull/3334))
`data.int.basic` had grown to require substantial imports from `algebra.*`. This PR moves out the end of this file into separate files. As a consequence it's then possible to separate out `data.multiset.basic` into some further pieces.
#### Estimated changes
Modified src/algebra/euclidean_domain.lean


Modified src/algebra/group_power.lean


Modified src/data/fintype/basic.lean


Modified src/data/hash_map.lean


Modified src/data/int/basic.lean
- \- *lemma* coe_cast_add_hom
- \- *lemma* coe_cast_ring_hom
- \- *lemma* cast_commute
- \- *lemma* commute_cast
- \- *lemma* cast_two
- \- *lemma* eq_int_cast
- \- *lemma* eq_int_cast'
- \- *lemma* map_int_cast
- \- *lemma* ext_int
- \- *theorem* nat_cast_eq_coe_nat
- \- *theorem* cast_zero
- \- *theorem* cast_of_nat
- \- *theorem* cast_coe_nat
- \- *theorem* cast_coe_nat'
- \- *theorem* cast_neg_succ_of_nat
- \- *theorem* cast_one
- \- *theorem* cast_sub_nat_nat
- \- *theorem* cast_neg_of_nat
- \- *theorem* cast_add
- \- *theorem* cast_neg
- \- *theorem* cast_sub
- \- *theorem* cast_eq_zero
- \- *theorem* cast_inj
- \- *theorem* cast_injective
- \- *theorem* cast_ne_zero
- \- *theorem* cast_mul
- \- *theorem* coe_nat_bit0
- \- *theorem* coe_nat_bit1
- \- *theorem* cast_bit0
- \- *theorem* cast_bit1
- \- *theorem* cast_nonneg
- \- *theorem* cast_le
- \- *theorem* cast_lt
- \- *theorem* cast_nonpos
- \- *theorem* cast_pos
- \- *theorem* cast_lt_zero
- \- *theorem* cast_min
- \- *theorem* cast_max
- \- *theorem* cast_abs
- \- *theorem* mem_range_iff
- \- *theorem* ext_int
- \- *theorem* eq_int_cast_hom
- \- *theorem* eq_int_cast
- \- *theorem* int.cast_id
- \- *def* of_nat_hom
- \- *def* cast_add_hom
- \- *def* cast_ring_hom
- \- *def* range

Created src/data/int/cast.lean
- \+ *lemma* coe_cast_add_hom
- \+ *lemma* coe_cast_ring_hom
- \+ *lemma* cast_commute
- \+ *lemma* commute_cast
- \+ *lemma* cast_two
- \+ *lemma* eq_int_cast
- \+ *lemma* eq_int_cast'
- \+ *lemma* map_int_cast
- \+ *lemma* ext_int
- \+ *theorem* nat_cast_eq_coe_nat
- \+ *theorem* cast_zero
- \+ *theorem* cast_of_nat
- \+ *theorem* cast_coe_nat
- \+ *theorem* cast_coe_nat'
- \+ *theorem* cast_neg_succ_of_nat
- \+ *theorem* cast_one
- \+ *theorem* cast_sub_nat_nat
- \+ *theorem* cast_neg_of_nat
- \+ *theorem* cast_add
- \+ *theorem* cast_neg
- \+ *theorem* cast_sub
- \+ *theorem* cast_mul
- \+ *theorem* coe_nat_bit0
- \+ *theorem* coe_nat_bit1
- \+ *theorem* cast_bit0
- \+ *theorem* cast_bit1
- \+ *theorem* cast_nonneg
- \+ *theorem* cast_le
- \+ *theorem* cast_lt
- \+ *theorem* cast_nonpos
- \+ *theorem* cast_pos
- \+ *theorem* cast_lt_zero
- \+ *theorem* cast_min
- \+ *theorem* cast_max
- \+ *theorem* cast_abs
- \+ *theorem* ext_int
- \+ *theorem* eq_int_cast_hom
- \+ *theorem* eq_int_cast
- \+ *theorem* int.cast_id
- \+ *def* of_nat_hom
- \+ *def* cast_add_hom
- \+ *def* cast_ring_hom

Created src/data/int/char_zero.lean
- \+ *theorem* cast_eq_zero
- \+ *theorem* cast_inj
- \+ *theorem* cast_injective
- \+ *theorem* cast_ne_zero

Created src/data/int/range.lean
- \+ *theorem* mem_range_iff
- \+ *def* range

Modified src/data/list/basic.lean


Modified src/data/multiset/basic.lean
- \- *theorem* range_zero
- \- *theorem* range_succ
- \- *theorem* card_range
- \- *theorem* range_subset
- \- *theorem* mem_range
- \- *theorem* not_mem_range_self
- \- *theorem* self_mem_range_succ
- \- *def* range

Modified src/data/multiset/nodup.lean


Created src/data/multiset/range.lean
- \+ *theorem* range_zero
- \+ *theorem* range_succ
- \+ *theorem* card_range
- \+ *theorem* range_subset
- \+ *theorem* mem_range
- \+ *theorem* not_mem_range_self
- \+ *theorem* self_mem_range_succ
- \+ *def* range

Modified src/data/nat/prime.lean


Modified src/data/num/lemmas.lean


Modified src/data/rat/basic.lean
- \+/\- *lemma* coe_int_inj

Modified src/data/rat/cast.lean


Modified src/tactic/ring.lean


Modified src/tactic/zify.lean


Modified test/norm_cast_int.lean




## [2020-07-10 10:35:29](https://github.com/leanprover-community/mathlib/commit/a348944)
chore(topology): rename compact to is_compact ([#3356](https://github.com/leanprover-community/mathlib/pull/3356))
#### Estimated changes
Modified src/analysis/convex/topology.lean
- \+/\- *lemma* compact_std_simplex

Modified src/measure_theory/lebesgue_measure.lean
- \+/\- *lemma* real.volume_lt_top_of_compact

Modified src/topology/algebra/group.lean
- \+/\- *lemma* compact_open_separated_mul
- \+/\- *lemma* compact_covered_by_mul_left_translates

Modified src/topology/algebra/ordered.lean
- \+ *lemma* is_compact.bdd_below
- \+ *lemma* is_compact.bdd_above
- \+ *lemma* is_compact.Inf_mem
- \+ *lemma* is_compact.Sup_mem
- \+ *lemma* is_compact.is_glb_Inf
- \+ *lemma* is_compact.is_lub_Sup
- \+ *lemma* is_compact.is_least_Inf
- \+ *lemma* is_compact.is_greatest_Sup
- \+ *lemma* is_compact.exists_is_least
- \+ *lemma* is_compact.exists_is_greatest
- \+ *lemma* is_compact.exists_is_glb
- \+ *lemma* is_compact.exists_is_lub
- \+ *lemma* is_compact.exists_Inf_image_eq
- \+ *lemma* is_compact.exists_forall_le
- \+ *lemma* is_compact.exists_forall_ge
- \+ *lemma* is_compact.exists_Sup_image_eq
- \+/\- *lemma* eq_Icc_of_connected_compact
- \- *lemma* compact.bdd_below
- \- *lemma* compact.bdd_above
- \- *lemma* compact.Inf_mem
- \- *lemma* compact.Sup_mem
- \- *lemma* compact.is_glb_Inf
- \- *lemma* compact.is_lub_Sup
- \- *lemma* compact.is_least_Inf
- \- *lemma* compact.is_greatest_Sup
- \- *lemma* compact.exists_is_least
- \- *lemma* compact.exists_is_greatest
- \- *lemma* compact.exists_is_glb
- \- *lemma* compact.exists_is_lub
- \- *lemma* compact.exists_Inf_image_eq
- \- *lemma* compact.exists_forall_le
- \- *lemma* compact.exists_forall_ge
- \- *lemma* compact.exists_Sup_image_eq

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/compact_open.lean


Modified src/topology/compacts.lean
- \+/\- *def* compacts
- \+/\- *def* nonempty_compacts
- \+/\- *def* positive_compacts:

Modified src/topology/homeomorph.lean
- \+/\- *lemma* compact_image
- \+/\- *lemma* compact_preimage

Modified src/topology/instances/real.lean
- \+/\- *lemma* compact_Icc

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* bounded_of_compact

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *lemma* countable_closure_of_compact

Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/separation.lean
- \+ *lemma* is_compact.is_closed
- \+ *lemma* is_compact.inter
- \+ *lemma* is_compact.binary_compact_cover
- \+ *lemma* is_compact.finite_compact_cover
- \+/\- *lemma* locally_compact_of_compact_nhds
- \- *lemma* compact.is_closed
- \- *lemma* compact.inter
- \- *lemma* compact.binary_compact_cover
- \- *lemma* compact.finite_compact_cover

Modified src/topology/sequences.lean
- \+ *lemma* is_seq_compact.subseq_of_frequently_in
- \+ *lemma* is_compact.is_seq_compact
- \+ *lemma* is_compact.tendsto_subseq'
- \+ *lemma* is_compact.tendsto_subseq
- \+ *lemma* is_seq_compact.totally_bounded
- \+/\- *lemma* metric.compact_iff_seq_compact
- \- *lemma* seq_compact.subseq_of_frequently_in
- \- *lemma* compact.seq_compact
- \- *lemma* compact.tendsto_subseq'
- \- *lemma* compact.tendsto_subseq
- \- *lemma* seq_compact.totally_bounded
- \+ *def* is_seq_compact
- \- *def* seq_compact

Modified src/topology/subset_properties.lean
- \+ *lemma* is_compact.inter_right
- \+ *lemma* is_compact.inter_left
- \+/\- *lemma* compact_diff
- \+ *lemma* is_compact.adherence_nhdset
- \+ *lemma* is_compact.elim_finite_subcover
- \+ *lemma* is_compact.elim_finite_subfamily_closed
- \+ *lemma* is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
- \+ *lemma* is_compact.nonempty_Inter_of_sequence_nonempty_compact_closed
- \+ *lemma* is_compact.elim_finite_subcover_image
- \+/\- *lemma* compact_empty
- \+/\- *lemma* compact_singleton
- \+ *lemma* set.finite.is_compact
- \+ *lemma* is_compact.union
- \+/\- *lemma* nhds_contain_boxes_of_compact
- \+/\- *lemma* generalized_tube_lemma
- \+/\- *lemma* compact_univ
- \+ *lemma* is_compact.image_of_continuous_on
- \+ *lemma* is_compact.image
- \+/\- *lemma* compact_iff_compact_univ
- \+/\- *lemma* compact_iff_compact_space
- \+ *lemma* is_compact.prod
- \+/\- *lemma* compact_univ_pi
- \- *lemma* compact.inter_right
- \- *lemma* compact.inter_left
- \- *lemma* compact.adherence_nhdset
- \- *lemma* compact.elim_finite_subcover
- \- *lemma* compact.elim_finite_subfamily_closed
- \- *lemma* compact.nonempty_Inter_of_directed_nonempty_compact_closed
- \- *lemma* compact.nonempty_Inter_of_sequence_nonempty_compact_closed
- \- *lemma* compact.elim_finite_subcover_image
- \- *lemma* set.finite.compact
- \- *lemma* compact.union
- \- *lemma* compact.image_of_continuous_on
- \- *lemma* compact.image
- \- *lemma* compact.prod
- \+ *def* is_compact
- \- *def* compact

Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/compact_separated.lean
- \+ *lemma* is_compact.uniform_continuous_on_of_continuous'
- \+ *lemma* is_compact.uniform_continuous_on_of_continuous
- \- *lemma* compact.uniform_continuous_on_of_continuous'
- \- *lemma* compact.uniform_continuous_on_of_continuous



## [2020-07-10 07:09:28](https://github.com/leanprover-community/mathlib/commit/79bb8b7)
feat(linear_algebra/cayley_hamilton): the Cayley-Hamilton theorem ([#3276](https://github.com/leanprover-community/mathlib/pull/3276))
The Cayley-Hamilton theorem, following the proof at http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf.
#### Estimated changes
Created src/linear_algebra/char_poly.lean
- \+ *lemma* char_matrix_apply_eq
- \+ *lemma* char_matrix_apply_ne
- \+ *lemma* mat_poly_equiv_char_matrix
- \+ *theorem* char_poly_map_eval_self
- \+ *def* char_matrix
- \+ *def* char_poly

Modified src/ring_theory/polynomial_algebra.lean




## [2020-07-10 06:31:16](https://github.com/leanprover-community/mathlib/commit/66db1ad)
refactor(algebra/homology): handle co/homology uniformly ([#3316](https://github.com/leanprover-community/mathlib/pull/3316))
A refactor of `algebra/homology` so homology and cohomology are handled uniformly, and factor out a file `image_to_kernel_map.lean` which gains some extra lemmas (which will be useful for talking about exact sequences).
#### Estimated changes
Modified src/algebra/homology/chain_complex.lean
- \+/\- *lemma* d_squared
- \+/\- *lemma* comm_at
- \+/\- *lemma* comm

Modified src/algebra/homology/homology.lean
- \+/\- *lemma* kernel_map_condition
- \+/\- *lemma* kernel_map_id
- \+/\- *lemma* kernel_map_comp
- \+/\- *lemma* image_map_ι
- \+/\- *lemma* image_to_kernel_map_condition
- \+ *lemma* image_to_kernel_map_comp_kernel_map
- \+ *lemma* homology_map_condition
- \+ *lemma* homology_map_id
- \+ *lemma* homology_map_comp
- \- *lemma* induced_maps_commute
- \- *lemma* cohomology_map_condition
- \- *lemma* cohomology_map_id
- \- *lemma* cohomology_map_comp
- \+/\- *def* kernel_map
- \+/\- *def* kernel_functor
- \+/\- *def* image_to_kernel_map
- \+ *def* homology_group
- \+ *def* homology_map
- \+ *def* homology
- \+ *def* graded_homology
- \- *def* cohomology
- \- *def* cohomology_map
- \- *def* cohomology_functor

Created src/algebra/homology/image_to_kernel_map.lean
- \+ *lemma* image_to_kernel_map_zero_left
- \+ *lemma* image_to_kernel_map_zero_right
- \+ *lemma* image_to_kernel_map_epi_of_zero_of_mono
- \+ *lemma* image_to_kernel_map_epi_of_epi_of_zero
- \+ *def* image_to_kernel_map

Modified src/category_theory/limits/shapes/kernels.lean




## [2020-07-10 05:40:16](https://github.com/leanprover-community/mathlib/commit/bcf733f)
feat(data/matrix): add matrix.map and supporting lemmas ([#3352](https://github.com/leanprover-community/mathlib/pull/3352))
As [requested](https://github.com/leanprover-community/mathlib/pull/3276/files#r452366674).
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* map_apply
- \+ *lemma* map_zero
- \+ *lemma* map_add
- \+ *lemma* add_monoid_hom.map_matrix_apply
- \+ *lemma* diagonal_map
- \+ *lemma* one_map
- \+ *lemma* map_mul
- \+ *lemma* ring_hom.map_matrix_apply
- \+ *lemma* matrix_eq_sum_std_basis
- \+ *lemma* std_basis_eq_basis_mul_basis
- \+/\- *lemma* transpose_sub
- \+/\- *lemma* transpose_mul
- \+/\- *lemma* transpose_smul
- \+/\- *lemma* transpose_neg
- \+ *lemma* transpose_map
- \- *lemma* matrix_eq_sum_elementary
- \- *lemma* elementary_eq_basis_mul_basis
- \+ *def* map
- \+ *def* add_monoid_hom.map_matrix
- \+ *def* ring_hom.map_matrix

Modified src/ring_theory/matrix_algebra.lean
- \+ *lemma* matrix_equiv_tensor_apply_std_basis
- \- *lemma* matrix_equiv_tensor_apply_elementary

Modified src/ring_theory/polynomial_algebra.lean




## [2020-07-10 04:14:30](https://github.com/leanprover-community/mathlib/commit/8b630df)
feat(ring_theory/matrix_algebra): drop commutativity assumption ([#3351](https://github.com/leanprover-community/mathlib/pull/3351))
Remove the unnecessary assumption that `A` is commutative in `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
(This didn't cause a problem for Cayley-Hamilton, but @alexjbest and Bassem Safieldeen [realised it's not necessary](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Tensor.20product.20of.20matrices).)
#### Estimated changes
Modified src/ring_theory/matrix_algebra.lean




## [2020-07-10 04:14:28](https://github.com/leanprover-community/mathlib/commit/c949dd4)
chore(logic/embedding): reuse proofs from `data.*` ([#3341](https://github.com/leanprover-community/mathlib/pull/3341))
Other changes:
* rename `injective.prod` to `injective.prod_map`;
* add `surjective.prod_map`;
* redefine `sigma.map` without pattern matching;
* rename `sigma_map_injective` to `injective.sigma_map`;
* add `surjective.sigma_map`;
* add `injective.sum_map` and `surjective.sum_map`;
* rename `embedding.prod_congr` to `embedding.prod_map`;
* rename `embedding.sum_congr` to `embedding.sum_map`;
* delete `embedding.sigma_congr_right`, add more
  general `embedding.sigma_map`.
#### Estimated changes
Modified src/data/prod.lean
- \+ *lemma* function.injective.prod_map
- \+ *lemma* function.surjective.prod_map
- \- *lemma* function.injective.prod

Modified src/data/sigma/basic.lean
- \+ *lemma* function.injective.sigma_map
- \+ *lemma* function.surjective.sigma_map
- \- *lemma* sigma_map_injective
- \+/\- *def* sigma.map

Modified src/data/sum.lean
- \+ *lemma* injective.sum_map
- \+ *lemma* surjective.sum_map

Modified src/logic/embedding.lean
- \+ *lemma* coe_prod_map
- \+ *lemma* coe_sigma_map
- \+ *theorem* coe_sum_map
- \- *theorem* sum_congr_apply_inl
- \- *theorem* sum_congr_apply_inr
- \+ *def* prod_map
- \+ *def* sum_map
- \+ *def* sigma_map
- \- *def* prod_congr
- \- *def* sum_congr
- \- *def* sigma_congr_right

Modified src/set_theory/cardinal.lean


Modified src/set_theory/game/domineering.lean


Modified src/set_theory/ordinal.lean


Modified src/topology/constructions.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-07-10 02:38:09](https://github.com/leanprover-community/mathlib/commit/92d508a)
chore(*): import tactic.basic as early as possible, and reduce imports ([#3333](https://github.com/leanprover-community/mathlib/pull/3333))
As discussed on [zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/import.20refactor.20and.20library_search), [#3235](https://github.com/leanprover-community/mathlib/pull/3235) had the unfortunate effect of making `library_search` and `#where` and various other things unavailable in many places in mathlib.
This PR makes an effort to import `tactic.basic` as early as possible, while otherwise reducing unnecessary imports. 
1. import `tactic.basic` "as early as possible" (i.e. in any file that `tactic.basic` doesn't depend on, and which imports any tactic strictly between `tactic.core` and `tactic.basic`, just `import tactic.basic` itself
2. add `tactic.finish`, `tactic.tauto` and `tactic.norm_cast` to tactic.basic (doesn't requires adding any dependencies)
3. delete various unnecessary imports
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/algebra/category/Group/biproducts.lean


Modified src/algebra/group/basic.lean


Modified src/algebra/group/conj.lean


Modified src/algebra/group/defs.lean


Modified src/algebra/group/hom.lean


Modified src/algebra/group/semiconj.lean


Modified src/algebra/group/units.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/group_with_zero.lean


Modified src/algebra/homology/homology.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/ring.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/concrete_category/bundled.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/isomorphism.lean


Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/preadditive/biproducts.lean


Modified src/category_theory/types.lean


Modified src/data/equiv/basic.lean


Modified src/data/equiv/local_equiv.lean


Modified src/data/finset/sort.lean


Modified src/data/fintype/card.lean


Modified src/data/int/basic.lean


Modified src/data/list/basic.lean


Modified src/data/list/forall2.lean


Modified src/data/list/func.lean


Modified src/data/list/pairwise.lean


Modified src/data/nat/basic.lean


Modified src/data/opposite.lean


Modified src/data/option/basic.lean


Modified src/data/polynomial.lean


Modified src/data/prod.lean


Modified src/data/seq/computation.lean


Modified src/data/set/basic.lean


Modified src/data/set/intervals/basic.lean


Modified src/data/sym.lean


Modified src/data/sym2.lean


Modified src/data/vector2.lean


Modified src/group_theory/eckmann_hilton.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/logic/nontrivial.lean


Modified src/logic/relation.lean


Modified src/logic/unique.lean


Modified src/order/basic.lean


Modified src/order/bounded_lattice.lean


Modified src/order/rel_classes.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/algebra_operations.lean


Modified src/tactic/basic.lean


Modified src/tactic/chain.lean


Modified src/tactic/interactive.lean


Modified src/tactic/noncomm_ring.lean


Modified src/tactic/push_neg.lean


Modified src/tactic/wlog.lean


Modified test/mk_iff_of_inductive.lean




## [2020-07-10 00:38:39](https://github.com/leanprover-community/mathlib/commit/997025d)
chore(scripts): update nolints.txt ([#3350](https://github.com/leanprover-community/mathlib/pull/3350))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-09 22:44:21](https://github.com/leanprover-community/mathlib/commit/270e3c9)
chore(data/fintype/basic): add `finset.order_top` and `finset.bounded_distrib_lattice` ([#3345](https://github.com/leanprover-community/mathlib/pull/3345))
#### Estimated changes
Modified src/data/fintype/basic.lean




## [2020-07-09 22:44:20](https://github.com/leanprover-community/mathlib/commit/f5fa614)
chore(*): some monotonicity lemmas ([#3344](https://github.com/leanprover-community/mathlib/pull/3344))
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *theorem* bInter_mono'
- \+ *theorem* bInter_mono

Modified src/order/filter/basic.lean
- \+/\- *lemma* monotone_principal
- \+/\- *lemma* map_mono
- \+/\- *lemma* comap_mono
- \+/\- *lemma* seq_mono
- \+/\- *lemma* prod_mono

Modified src/tactic/monotonicity/lemmas.lean




## [2020-07-09 21:17:53](https://github.com/leanprover-community/mathlib/commit/d6e9f97)
feat(topology/basic): yet another mem_closure ([#3348](https://github.com/leanprover-community/mathlib/pull/3348))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* comap_ne_bot_iff
- \+/\- *lemma* comap_ne_bot

Modified src/topology/basic.lean
- \+ *theorem* mem_closure_iff_comap_ne_bot



## [2020-07-09 21:17:51](https://github.com/leanprover-community/mathlib/commit/ac62213)
chore(order/filter/at_top_bot): in `order_top` `at_top = pure ⊤` ([#3346](https://github.com/leanprover-community/mathlib/pull/3346))
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* order_top.at_top_eq
- \+ *lemma* tendsto_at_top_pure

Modified src/topology/basic.lean
- \+ *lemma* order_top.tendsto_at_top



## [2020-07-09 21:17:48](https://github.com/leanprover-community/mathlib/commit/4a63f3f)
feat(data/indicator_function): add `indicator_range_comp` ([#3343](https://github.com/leanprover-community/mathlib/pull/3343))
Add
* `comp_eq_of_eq_on_range`;
* `piecewise_eq_on`;
* `piecewise_eq_on_compl`;
* `piecewise_compl`;
* `piecewise_range_comp`;
* `indicator_range_comp`.
#### Estimated changes
Modified src/data/indicator_function.lean
- \+ *lemma* indicator_range_comp
- \+/\- *lemma* indicator_le_indicator

Modified src/data/set/function.lean
- \+ *lemma* comp_eq_of_eq_on_range
- \+ *lemma* piecewise_eq_on
- \+ *lemma* piecewise_eq_on_compl
- \+ *lemma* piecewise_compl
- \+ *lemma* piecewise_range_comp



## [2020-07-09 16:34:14](https://github.com/leanprover-community/mathlib/commit/d6ecb44)
feat(topology/basic): closure in term of subtypes ([#3339](https://github.com/leanprover-community/mathlib/pull/3339))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* nonempty_inter_iff_exists_right
- \+ *lemma* nonempty_inter_iff_exists_left

Modified src/topology/basic.lean
- \+ *theorem* mem_closure_iff_nhds'



## [2020-07-09 15:24:02](https://github.com/leanprover-community/mathlib/commit/593a4c8)
fix(tactic/norm_cast): remove bad norm_cast lemma ([#3340](https://github.com/leanprover-community/mathlib/pull/3340))
This was identified as a move_cast lemma, which meant it was rewriting to the LHS which it couldn't reduce. It's better to let the conditional rewriting handle nat subtraction -- if the right inequality is in the context there's no need to go to `int.sub_nat_nat`.
#### Estimated changes
Modified src/data/int/basic.lean
- \+/\- *theorem* cast_sub_nat_nat

Modified src/number_theory/bernoulli.lean




## [2020-07-09 14:50:06](https://github.com/leanprover-community/mathlib/commit/33ca9f1)
doc(category_theory/terminal): add doc-strings ([#3338](https://github.com/leanprover-community/mathlib/pull/3338))
Just adding some doc-strings.
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean




## [2020-07-09 13:55:03](https://github.com/leanprover-community/mathlib/commit/9d47b28)
feat(data): Mark all `sqrt`s as `@[pp_nodot]` ([#3337](https://github.com/leanprover-community/mathlib/pull/3337))
#### Estimated changes
Modified src/data/int/sqrt.lean
- \+/\- *def* sqrt

Modified src/data/nat/sqrt.lean
- \+/\- *def* sqrt

Modified src/data/rat/order.lean
- \+/\- *def* sqrt

Modified src/data/real/basic.lean




## [2020-07-09 05:00:10-07:00](https://github.com/leanprover-community/mathlib/commit/e4ecf14)
I'm just another maintainer
#### Estimated changes
Modified README.md




## [2020-07-09 10:43:05](https://github.com/leanprover-community/mathlib/commit/be2e42f)
chore(ring_theory/algebraic): speedup slow proof ([#3336](https://github.com/leanprover-community/mathlib/pull/3336))
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+ *lemma* val_apply

Modified src/ring_theory/algebraic.lean




## [2020-07-09 06:11:02](https://github.com/leanprover-community/mathlib/commit/c06f500)
feat(logic/basic): add eq_iff_true_of_subsingleton ([#3308](https://github.com/leanprover-community/mathlib/pull/3308))
I'm surprised we didn't have this already.
```lean
example (x y : unit) : x = y := by simp
```
#### Estimated changes
Modified src/linear_algebra/basis.lean


Modified src/logic/basic.lean
- \+ *lemma* eq_iff_true_of_subsingleton

Modified src/tactic/fin_cases.lean


Modified src/tactic/norm_num.lean


Modified test/fin_cases.lean


Modified test/tidy.lean
- \- *def* tidy_test_0



## [2020-07-09 03:35:05](https://github.com/leanprover-community/mathlib/commit/95cc1b1)
refactor(topology/dense_embedding): simplify proof ([#3329](https://github.com/leanprover-community/mathlib/pull/3329))
Using filter bases, we can give a cleaner proof of continuity of extension by continuity. Also switch to use the "new" `continuous_at` in the statement.
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* nhds_basis_opens'

Modified src/topology/dense_embedding.lean
- \+ *lemma* continuous_at_extend
- \- *lemma* tendsto_extend

Modified src/topology/separation.lean
- \+ *lemma* closed_nhds_basis



## [2020-07-09 03:35:03](https://github.com/leanprover-community/mathlib/commit/d5cfa87)
fix(tactic/lint/type_classes): add missing unfreeze_local_instances ([#3328](https://github.com/leanprover-community/mathlib/pull/3328))
#### Estimated changes
Modified src/tactic/cache.lean


Modified src/tactic/lint/simp.lean


Modified src/tactic/lint/type_classes.lean


Modified test/lint_coe_to_fun.lean




## [2020-07-09 03:06:58](https://github.com/leanprover-community/mathlib/commit/b535b0a)
fix(tactic/default): add transport, equiv_rw ([#3330](https://github.com/leanprover-community/mathlib/pull/3330))
Also added a tactic doc entry for `transport`.
#### Estimated changes
Modified src/tactic/default.lean


Modified src/tactic/transport.lean




## [2020-07-09 00:41:30](https://github.com/leanprover-community/mathlib/commit/65dcf4d)
chore(scripts): update nolints.txt ([#3331](https://github.com/leanprover-community/mathlib/pull/3331))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-08 20:57:45](https://github.com/leanprover-community/mathlib/commit/782013d)
fix(tactic/monotonicity): support monotone in mono ([#3310](https://github.com/leanprover-community/mathlib/pull/3310))
This PR allow the `mono` tactic to use lemmas stated using `monotone`.
Mostly authored by Simon Hudon
#### Estimated changes
Modified scripts/nolints.txt


Modified src/tactic/monotonicity/basic.lean


Modified src/tactic/monotonicity/interactive.lean


Modified test/monotonicity/test_cases.lean
- \+ *lemma* test



## [2020-07-08 17:40:17](https://github.com/leanprover-community/mathlib/commit/19225c3)
chore(*): update to 3.17.1 ([#3327](https://github.com/leanprover-community/mathlib/pull/3327))
#### Estimated changes
Modified leanpkg.toml




## [2020-07-08 14:31:06](https://github.com/leanprover-community/mathlib/commit/27f622e)
chore(data/fintype/basic): split, and reduce imports ([#3319](https://github.com/leanprover-community/mathlib/pull/3319))
Following on from [#3256](https://github.com/leanprover-community/mathlib/pull/3256) and [#3235](https://github.com/leanprover-community/mathlib/pull/3235), this slices a little out of `data.fintype.basic`, and reduces imports, mostly in the vicinity of `data.fintype.basic`.
#### Estimated changes
Modified src/combinatorics/composition.lean


Modified src/control/bifunctor.lean


Modified src/control/bitraversable/basic.lean


Modified src/control/bitraversable/instances.lean


Modified src/data/equiv/list.lean


Modified src/data/finset/basic.lean
- \+ *lemma* fin_range_card
- \+ *lemma* mem_fin_range
- \+ *def* fin_range

Modified src/data/finset/sort.lean
- \+ *lemma* mono_of_fin_unique'

Modified src/data/fintype/basic.lean
- \- *lemma* finset.mono_of_fin_unique'

Created src/data/fintype/sort.lean


Modified src/data/polynomial.lean


Modified src/data/set/basic.lean


Modified src/data/set/intervals/basic.lean


Modified src/group_theory/perm/sign.lean


Modified src/linear_algebra/multilinear.lean


Modified src/order/rel_classes.lean


Modified src/tactic/equiv_rw.lean




## [2020-07-08 14:31:04](https://github.com/leanprover-community/mathlib/commit/f90fcc9)
chore(*): use is_algebra_tower instead of algebra.comap and generalize some constructions to semirings ([#3299](https://github.com/leanprover-community/mathlib/pull/3299))
`algebra.comap` is now reserved to the **creation** of new algebra instances. For assumptions of theorems / constructions, `is_algebra_tower` is the new way to do it. For example:
```lean
variables [algebra K L] [algebra L A]
lemma is_algebraic_trans (L_alg : is_algebraic K L) (A_alg : is_algebraic L A) :
  is_algebraic K (comap K L A) :=
```
is now written as:
```lean
variables [algebra K L] [algebra L A] [algebra K A] [is_algebra_tower K L A]
lemma is_algebraic_trans (L_alg : is_algebraic K L) (A_alg : is_algebraic L A) :
  is_algebraic K A :=
```
#### Estimated changes
Modified src/algebra/lie_algebra.lean


Modified src/data/mv_polynomial.lean
- \+/\- *lemma* aeval_X
- \+/\- *lemma* aeval_C
- \+/\- *theorem* aeval_def
- \+/\- *theorem* eval_unique
- \+/\- *def* aeval

Modified src/data/polynomial.lean
- \+/\- *lemma* dvd_term_of_dvd_eval_of_dvd_terms
- \+/\- *lemma* dvd_term_of_is_root_of_dvd_terms
- \+ *theorem* aeval_alg_hom
- \+ *theorem* aeval_alg_hom_apply

Modified src/field_theory/splitting_field.lean


Modified src/linear_algebra/tensor_product.lean
- \+/\- *theorem* map_neg₂
- \+/\- *def* mk
- \+/\- *def* map

Modified src/ring_theory/adjoin.lean
- \+/\- *theorem* adjoin_union
- \+/\- *theorem* adjoin_singleton_eq_range
- \+/\- *theorem* adjoin_int
- \+ *theorem* mem_adjoin_iff
- \+ *theorem* adjoin_eq_ring_closure

Modified src/ring_theory/algebra.lean
- \+/\- *lemma* map_eq_self
- \+/\- *lemma* smul_eq_mul
- \+/\- *lemma* to_linear_map_apply
- \+/\- *lemma* comp_to_linear_map
- \+ *lemma* mem_to_submodule
- \+ *lemma* mem_subalgebra_of_subsemiring
- \+ *lemma* span_nat_eq_add_group_closure
- \+ *lemma* span_nat_eq
- \- *lemma* range_le
- \- *lemma* mul_mem
- \+/\- *theorem* to_linear_map_inj
- \+ *theorem* algebra_map_mem
- \+ *theorem* srange_le
- \+ *theorem* range_subset
- \+ *theorem* range_le
- \+ *theorem* one_mem
- \+ *theorem* mul_mem
- \+ *theorem* smul_mem
- \+ *theorem* pow_mem
- \+ *theorem* zero_mem
- \+ *theorem* add_mem
- \+ *theorem* neg_mem
- \+ *theorem* sub_mem
- \+ *theorem* nsmul_mem
- \+ *theorem* gsmul_mem
- \+ *theorem* coe_nat_mem
- \+ *theorem* coe_int_mem
- \+ *theorem* list_prod_mem
- \+ *theorem* list_sum_mem
- \+ *theorem* multiset_prod_mem
- \+ *theorem* multiset_sum_mem
- \+ *theorem* prod_mem
- \+ *theorem* sum_mem
- \+ *theorem* to_submodule_injective
- \+ *theorem* to_submodule_inj
- \+/\- *def* to_linear_map
- \+/\- *def* under
- \+ *def* alg_hom_nat
- \+ *def* subalgebra_of_subsemiring

Modified src/ring_theory/algebra_operations.lean
- \+/\- *lemma* map_mul

Modified src/ring_theory/algebra_tower.lean
- \+ *lemma* to_alg_hom_apply
- \+ *lemma* restrict_base_apply
- \+ *theorem* aeval_apply
- \+ *def* restrict_base

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \+/\- *lemma* is_integral_trans_aux
- \+ *theorem* is_integral_alg_hom

Modified src/ring_theory/localization.lean
- \+ *lemma* algebra_map_eq
- \+/\- *lemma* integer_normalization_aeval_eq_zero
- \+/\- *lemma* comap_is_algebraic_iff
- \+/\- *def* fraction_map_of_finite_extension

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* mem_closure_iff
- \+ *lemma* mem_closure_iff_exists_list
- \+/\- *theorem* ext



## [2020-07-08 14:31:02](https://github.com/leanprover-community/mathlib/commit/ba8af8c)
feat(ring_theory/polynomial_algebra): polynomial A ≃ₐ[R] (A ⊗[R] polynomial R) ([#3275](https://github.com/leanprover-community/mathlib/pull/3275))
This is a formal nonsense preliminary to the Cayley-Hamilton theorem, which comes in the next PR.
We produce the algebra isomorphism `polynomial A ≃ₐ[R] (A ⊗[R] polynomial R)`, and as a consequence also the algebra isomorphism
```
matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R)
```
which is characterized by
```
coeff (matrix_polynomial_equiv_polynomial_matrix m) k i j = coeff (m i j) k
```
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/data/monoid_algebra.lean
- \+/\- *def* algebra_map'

Modified src/data/polynomial.lean
- \+ *lemma* algebra_map_apply
- \+/\- *def* C

Created src/ring_theory/polynomial_algebra.lean
- \+ *lemma* to_fun_linear_mul_tmul_mul_aux_1
- \+ *lemma* to_fun_linear_mul_tmul_mul_aux_2
- \+ *lemma* to_fun_linear_mul_tmul_mul
- \+ *lemma* to_fun_linear_algebra_map_tmul_one
- \+ *lemma* to_fun_alg_hom_apply_tmul
- \+ *lemma* inv_fun_add
- \+ *lemma* left_inv
- \+ *lemma* right_inv
- \+ *lemma* poly_equiv_tensor_apply
- \+ *lemma* poly_equiv_tensor_symm_apply_tmul
- \+ *lemma* mat_poly_equiv_coeff_apply_aux_1
- \+ *lemma* mat_poly_equiv_coeff_apply_aux_2
- \+ *lemma* mat_poly_equiv_coeff_apply
- \+ *lemma* mat_poly_equiv_symm_apply_coeff
- \+ *lemma* mat_poly_equiv_smul_one
- \+ *def* mat_poly_equiv
- \+ *def* to_fun
- \+ *def* to_fun_linear_right
- \+ *def* to_fun_bilinear
- \+ *def* to_fun_linear
- \+ *def* to_fun_alg_hom
- \+ *def* inv_fun
- \+ *def* equiv
- \+ *def* poly_equiv_tensor

Modified src/ring_theory/tensor_product.lean




## [2020-07-08 13:22:00](https://github.com/leanprover-community/mathlib/commit/8f6090c)
feat(algebra/ordered_field): missing lemma ([#3324](https://github.com/leanprover-community/mathlib/pull/3324))
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* one_div_le



## [2020-07-08 11:56:25](https://github.com/leanprover-community/mathlib/commit/97853b9)
doc(tactic/lean_core_docs): remove "hypothesis management" tag ([#3323](https://github.com/leanprover-community/mathlib/pull/3323))
#### Estimated changes
Modified src/tactic/lean_core_docs.lean




## [2020-07-08 10:26:52](https://github.com/leanprover-community/mathlib/commit/a3e21a8)
feat(category_theory/zero): lemmas about zero objects and zero morphisms, and improve docs ([#3315](https://github.com/leanprover-community/mathlib/pull/3315))
#### Estimated changes
Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* kernel.lift_zero
- \+ *lemma* cokernel.desc_zero
- \- *def* kernel.ι_zero_is_iso
- \- *def* cokernel.π_zero_is_iso

Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* id_zero
- \+ *lemma* zero_of_target_iso_zero
- \+ *lemma* zero_of_source_iso_zero
- \+ *lemma* mono_of_source_iso_zero
- \+ *lemma* epi_of_target_iso_zero
- \+ *lemma* id_zero_equiv_iso_zero_apply_hom
- \+ *lemma* id_zero_equiv_iso_zero_apply_inv
- \+ *lemma* image.ι_zero
- \+ *lemma* image.ι_zero'
- \+/\- *def* has_initial
- \+/\- *def* has_terminal
- \+ *def* id_zero_equiv_iso_zero
- \+ *def* is_iso_zero_equiv
- \+ *def* is_iso_zero_self_equiv
- \+ *def* is_iso_zero_equiv_iso_zero
- \+ *def* is_iso_zero_self_equiv_iso_zero
- \+ *def* mono_factorisation_zero
- \+ *def* has_image.zero
- \+ *def* image_zero
- \+ *def* image_zero'



## [2020-07-08 10:26:50](https://github.com/leanprover-community/mathlib/commit/fbb49cb)
refactor(*): place map_map in the functor namespace ([#3309](https://github.com/leanprover-community/mathlib/pull/3309))
Renames `_root_.map_map` to `functor.map_map` and `filter.comap_comap_comp` to `filter.comap_comap` (which is consistent with `filter.map_map`).
#### Estimated changes
Modified src/control/basic.lean
- \+ *theorem* functor.map_map

Modified src/order/filter/basic.lean
- \+ *lemma* comap_comap
- \- *lemma* comap_comap_comp

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/dense_embedding.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniform_space.comap_comap
- \- *lemma* uniform_space.comap_comap_comp

Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-07-08 09:01:29](https://github.com/leanprover-community/mathlib/commit/afae2c4)
doc(tactic/localized): unnecessary escape characters ([#3322](https://github.com/leanprover-community/mathlib/pull/3322))
This is probably left over from when it was a string literal instead of a doc string.
#### Estimated changes
Modified src/tactic/localized.lean




## [2020-07-08 08:25:47](https://github.com/leanprover-community/mathlib/commit/18246ac)
refactor(category_theory/finite_limits): reorganise import hierarchy ([#3320](https://github.com/leanprover-community/mathlib/pull/3320))
Previously, all of the "special shapes" that happened to be finite imported `category_theory.limits.shapes.finite_limits`. Now it's the other way round, which I think ends up being cleaner.
This also results in some significant reductions to the dependency graph (e.g. talking about homology of complexes no longer requires compiling `data.fintype.basic` and all its antecedents).
No actual content, just moving content around.
#### Estimated changes
Modified docs/tutorial/category_theory/calculating_colimits_in_Top.lean


Modified docs/tutorial/category_theory/intro.lean


Modified src/algebra/homology/chain_complex.lean


Modified src/category_theory/abelian/non_preadditive.lean


Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/connected.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/shapes/binary_products.lean
- \- *lemma* braid_natural
- \- *lemma* prod.symmetry'
- \- *lemma* prod.symmetry
- \- *lemma* prod.pentagon
- \- *lemma* prod.associator_naturality
- \- *lemma* prod_left_unitor_hom_naturality
- \- *lemma* prod_left_unitor_inv_naturality
- \- *lemma* prod_right_unitor_hom_naturality
- \- *lemma* prod_right_unitor_inv_naturality
- \- *lemma* prod.triangle
- \- *lemma* coprod.symmetry'
- \- *lemma* coprod.symmetry
- \- *lemma* coprod.pentagon
- \- *lemma* coprod.associator_naturality
- \- *lemma* coprod.triangle
- \- *def* prod.braiding
- \- *def* prod.associator
- \- *def* prod_functor_left_comp
- \- *def* prod.left_unitor
- \- *def* prod.right_unitor
- \- *def* coprod.braiding
- \- *def* coprod.associator
- \- *def* coprod.left_unitor
- \- *def* coprod.right_unitor

Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/constructions/binary_products.lean


Modified src/category_theory/limits/shapes/default.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \- *def* has_equalizers_of_has_finite_limits
- \- *def* has_coequalizers_of_has_finite_colimits

Modified src/category_theory/limits/shapes/finite_limits.lean
- \+ *def* has_equalizers_of_has_finite_limits
- \+ *def* has_coequalizers_of_has_finite_colimits
- \+ *def* has_finite_wide_pullbacks_of_has_finite_limits
- \+ *def* has_finite_wide_pushouts_of_has_finite_limits
- \+ *def* has_pullbacks_of_has_finite_limits
- \+ *def* has_pushouts_of_has_finite_colimits

Modified src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/kernels.lean
- \- *def* has_kernels_of_has_finite_limits
- \- *def* has_cokernels_of_has_finite_colimits

Modified src/category_theory/limits/shapes/pullbacks.lean
- \- *def* has_pullbacks_of_has_finite_limits
- \- *def* has_pushouts_of_has_finite_colimits

Modified src/category_theory/limits/shapes/terminal.lean


Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \- *def* has_finite_wide_pullbacks_of_has_finite_limits
- \- *def* has_finite_wide_pushouts_of_has_finite_limits

Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/monoidal/of_has_finite_products.lean
- \+ *lemma* braid_natural
- \+ *lemma* prod.symmetry'
- \+ *lemma* prod.symmetry
- \+ *lemma* prod.pentagon
- \+ *lemma* prod.associator_naturality
- \+ *lemma* prod_left_unitor_hom_naturality
- \+ *lemma* prod_left_unitor_inv_naturality
- \+ *lemma* prod_right_unitor_hom_naturality
- \+ *lemma* prod_right_unitor_inv_naturality
- \+ *lemma* prod.triangle
- \+ *lemma* coprod.symmetry'
- \+ *lemma* coprod.symmetry
- \+ *lemma* coprod.pentagon
- \+ *lemma* coprod.associator_naturality
- \+ *lemma* coprod.triangle
- \+ *def* prod.braiding
- \+ *def* prod.associator
- \+ *def* prod_functor_left_comp
- \+ *def* prod.left_unitor
- \+ *def* prod.right_unitor
- \+ *def* coprod.braiding
- \+ *def* coprod.associator
- \+ *def* coprod.left_unitor
- \+ *def* coprod.right_unitor

Modified src/category_theory/monoidal/types.lean


Modified src/category_theory/punit.lean




## [2020-07-08 07:12:45](https://github.com/leanprover-community/mathlib/commit/13eea4c)
chore(category_theory/images): cleanup ([#3314](https://github.com/leanprover-community/mathlib/pull/3314))
Just some cleanup, and adding two easy lemmas.
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* image.ext
- \+ *lemma* epi_image_of_epi
- \+ *lemma* image.eq_fac



## [2020-07-08 07:12:43](https://github.com/leanprover-community/mathlib/commit/eb271b2)
feat(data/int/basic): some lemmas ([#3313](https://github.com/leanprover-community/mathlib/pull/3313))
A few small lemmas about `to_nat` that I wanted while playing with exact sequences.
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* le_add_one
- \+ *lemma* to_nat_zero
- \+ *lemma* to_nat_one
- \+ *lemma* to_nat_coe_nat_add_one
- \+ *lemma* to_nat_add
- \+ *lemma* to_nat_add_one



## [2020-07-08 05:45:29](https://github.com/leanprover-community/mathlib/commit/ff1aea5)
feat(data/equiv): α × α ≃ α for [subsingleton α] ([#3312](https://github.com/leanprover-community/mathlib/pull/3312))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* subsingleton_prod_self_equiv

Modified src/logic/basic.lean




## [2020-07-08 00:37:50](https://github.com/leanprover-community/mathlib/commit/e987f62)
chore(scripts): update nolints.txt ([#3311](https://github.com/leanprover-community/mathlib/pull/3311))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-07 19:51:20](https://github.com/leanprover-community/mathlib/commit/23f449b)
feat(topology/metric_space/basic): add closed_ball_mem_nhds ([#3305](https://github.com/leanprover-community/mathlib/pull/3305))
I found this lemma handy when converting between the epsilon-N definition of convergence and the filter definition
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *theorem* closed_ball_mem_nhds



## [2020-07-07 17:45:54](https://github.com/leanprover-community/mathlib/commit/35940dd)
feat(linear_algebra/finite_dimensional): add dim_sup_add_dim_inf_eq ([#3304](https://github.com/leanprover-community/mathlib/pull/3304))
Adding a finite-dimensional version of dim(W+X)+dim(W \cap X)=dim(W)+dim(X)
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+ *theorem* dim_sup_add_dim_inf_eq



## [2020-07-07 16:39:23](https://github.com/leanprover-community/mathlib/commit/ea10944)
feat(data/list/defs): list.singleton_append and list.bind_singleton ([#3298](https://github.com/leanprover-community/mathlib/pull/3298))
I found these useful when working with palindromes and Fibonacci words respectively.
While `bind_singleton` is available as a monad law, I find the specialized version more convenient.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* singleton_append
- \+ *theorem* bind_singleton



## [2020-07-07 15:15:11](https://github.com/leanprover-community/mathlib/commit/11ba687)
chore(algebra/big_operators): use proper `*_with_zero` class in `prod_eq_zero(_iff)` ([#3303](https://github.com/leanprover-community/mathlib/pull/3303))
Also add a missing instance `comm_semiring → comm_monoid_with_zero`.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_eq_zero

Modified src/algebra/ring.lean


Modified src/data/support.lean
- \+ *lemma* mem_support
- \+ *lemma* support_prod_subset
- \+/\- *lemma* support_prod



## [2020-07-07 09:59:21](https://github.com/leanprover-community/mathlib/commit/12c2acb)
feat(algebra/continued_fractions): add first set of approximation lemmas ([#3218](https://github.com/leanprover-community/mathlib/pull/3218))
#### Estimated changes
Created src/algebra/continued_fractions/computation/approximations.lean
- \+ *lemma* nth_stream_fr_nonneg_lt_one
- \+ *lemma* nth_stream_fr_nonneg
- \+ *lemma* nth_stream_fr_lt_one
- \+ *lemma* one_le_succ_nth_stream_b
- \+ *lemma* succ_nth_stream_b_le_nth_stream_fr_inv
- \+ *lemma* of_one_le_nth_part_denom
- \+ *lemma* of_part_num_eq_one_and_exists_int_part_denom_eq
- \+ *lemma* of_part_num_eq_one
- \+ *lemma* exists_int_eq_of_part_denom
- \+ *lemma* fib_le_of_continuants_aux_b
- \+ *lemma* succ_nth_fib_le_of_nth_denom
- \+ *lemma* zero_le_of_continuants_aux_b
- \+ *lemma* zero_le_of_denom
- \+ *lemma* le_of_succ_succ_nth_continuants_aux_b
- \+ *theorem* le_of_succ_nth_denom
- \+ *theorem* of_denom_mono

Modified src/algebra/continued_fractions/computation/correctness_terminating.lean
- \+ *lemma* of_correctness_of_nth_stream_eq_none
- \- *lemma* comp_exact_value_correctness_of_stream_eq_none

Modified src/algebra/continued_fractions/computation/translations.lean
- \+ *lemma* exists_succ_nth_stream_of_fr_zero
- \+ *lemma* int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some
- \- *lemma* obtain_succ_nth_stream_of_fr_zero
- \- *lemma* int_fract_pair.obtain_succ_nth_stream_of_gcf_of_nth_eq_some

Modified src/algebra/continued_fractions/continuants_recurrence.lean


Modified src/algebra/continued_fractions/convergents_equiv.lean


Modified src/algebra/continued_fractions/terminated_stable.lean


Modified src/algebra/continued_fractions/translations.lean
- \+ *lemma* exists_s_a_of_part_num
- \+ *lemma* exists_s_b_of_part_denom
- \+ *lemma* exists_conts_a_of_num
- \+ *lemma* exists_conts_b_of_denom
- \+ *lemma* zeroth_numerator_eq_h
- \+ *lemma* zeroth_denominator_eq_one
- \+ *lemma* second_continuant_aux_eq
- \+ *lemma* first_continuant_eq
- \+ *lemma* first_numerator_eq
- \+ *lemma* first_denominator_eq
- \- *lemma* obtain_s_a_of_part_num
- \- *lemma* obtain_s_b_of_part_denom
- \- *lemma* obtain_conts_a_of_num
- \- *lemma* obtain_conts_b_of_denom



## [2020-07-07 09:25:12](https://github.com/leanprover-community/mathlib/commit/08ffbbb)
feat(analysis/normed_space/operator_norm): normed algebra of continuous linear maps ([#3282](https://github.com/leanprover-community/mathlib/pull/3282))
Given a normed space `E`, its continuous linear endomorphisms form a normed ring, and a normed algebra if `E` is nonzero.  Moreover, the units of this ring are precisely the continuous linear equivalences.
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* units_equiv_to_continuous_linear_map
- \+ *def* of_unit
- \+ *def* to_unit
- \+ *def* units_equiv



## [2020-07-07 04:39:03](https://github.com/leanprover-community/mathlib/commit/095445e)
refactor(order/*): make `data.set.basic` import `order.bounded_lattice` ([#3285](https://github.com/leanprover-community/mathlib/pull/3285))
I have two goals:
* make it possible to refactor `set` to use `lattice` operations;
* make `submonoid.basic` independent of `data.nat.basic`.
#### Estimated changes
Modified src/algebra/ordered_group.lean


Modified src/data/equiv/encodable.lean


Modified src/data/nat/basic.lean


Modified src/data/set/basic.lean
- \+ *lemma* bot_eq_empty
- \+ *lemma* sup_eq_union
- \+ *lemma* inf_eq_inter
- \+ *lemma* le_eq_subset
- \+ *lemma* lt_eq_ssubset
- \+/\- *lemma* image_eq_range
- \- *def* strict_subset

Modified src/data/set/intervals/basic.lean


Modified src/data/set/lattice.lean
- \- *lemma* bot_eq_empty
- \- *lemma* sup_eq_union
- \- *lemma* inf_eq_inter
- \- *lemma* le_eq_subset
- \- *lemma* lt_eq_ssubset

Modified src/data/setoid/basic.lean


Modified src/group_theory/congruence.lean
- \+ *lemma* rel_eq_coe

Modified src/order/basic.lean
- \- *theorem* directed_on_iff_directed
- \- *theorem* directed_on_image
- \- *theorem* directed_on.mono
- \- *theorem* directed_comp
- \- *theorem* directed.mono
- \- *theorem* directed.mono_comp
- \- *def* directed
- \- *def* directed_on

Modified src/order/boolean_algebra.lean


Modified src/order/bounded_lattice.lean
- \+ *lemma* sup_apply
- \+ *lemma* inf_apply
- \+ *lemma* bot_apply
- \+ *lemma* top_apply

Modified src/order/complete_lattice.lean
- \+/\- *lemma* Inf_apply
- \+/\- *lemma* infi_apply
- \+/\- *lemma* Sup_apply
- \+/\- *lemma* supr_apply
- \- *def* Sup
- \- *def* Inf

Created src/order/directed.lean
- \+ *lemma* directed_of_sup
- \+ *lemma* directed_of_inf
- \+ *theorem* directed_on_iff_directed
- \+ *theorem* directed_on_image
- \+ *theorem* directed_on.mono
- \+ *theorem* directed_comp
- \+ *theorem* directed.mono
- \+ *theorem* directed.mono_comp
- \+ *def* directed
- \+ *def* directed_on

Modified src/order/filter/bases.lean


Modified src/order/lattice.lean
- \- *lemma* directed_of_mono
- \- *lemma* directed_of_sup
- \- *lemma* directed_of_inf

Modified src/order/order_iso.lean
- \- *theorem* well_founded_iff_no_descending_seq
- \- *def* nat_lt
- \- *def* nat_gt

Created src/order/order_iso_nat.lean
- \+ *theorem* well_founded_iff_no_descending_seq
- \+ *def* nat_lt
- \+ *def* nat_gt

Modified src/order/rel_classes.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/noetherian.lean


Modified src/tactic/pi_instances.lean


Modified src/topology/subset_properties.lean




## [2020-07-07 00:37:33](https://github.com/leanprover-community/mathlib/commit/d62e71d)
chore(scripts): update nolints.txt ([#3302](https://github.com/leanprover-community/mathlib/pull/3302))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-06 20:20:45](https://github.com/leanprover-community/mathlib/commit/f548db4)
feat(linear_algebra/affine_space): lattice structure on affine subspaces ([#3288](https://github.com/leanprover-community/mathlib/pull/3288))
Define a `complete_lattice` instance on affine subspaces of an affine
space, and prove a few basic lemmas relating to it.  (There are plenty
more things that could be proved about it, that I think can reasonably
be added later.)
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* vsub_set_empty

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* vector_span_def
- \+ *lemma* span_points_subset_coe_of_subset_coe
- \+ *lemma* le_def
- \+ *lemma* le_def'
- \+ *lemma* lt_def
- \+ *lemma* not_le_iff_exists
- \+ *lemma* exists_of_lt
- \+ *lemma* lt_iff_le_and_exists
- \+ *lemma* affine_span_eq_Inf
- \+ *lemma* span_empty
- \+ *lemma* span_univ
- \+ *lemma* span_union
- \+ *lemma* span_Union
- \+ *lemma* top_coe
- \+ *lemma* mem_top
- \+ *lemma* direction_top
- \+ *lemma* bot_coe
- \+ *lemma* not_mem_bot
- \+ *lemma* direction_bot
- \+ *lemma* inf_coe
- \+ *lemma* mem_inf_iff
- \+ *lemma* direction_inf
- \- *lemma* univ_coe
- \- *lemma* mem_univ
- \- *def* univ



## [2020-07-06 19:04:56](https://github.com/leanprover-community/mathlib/commit/edd29d0)
chore(ring_theory/power_series): weaken assumptions for nontrivial ([#3301](https://github.com/leanprover-community/mathlib/pull/3301))
#### Estimated changes
Modified src/logic/nontrivial.lean


Modified src/ring_theory/power_series.lean
- \+/\- *lemma* X_inj



## [2020-07-06 17:34:23](https://github.com/leanprover-community/mathlib/commit/c0926f0)
chore(*): update to lean 3.17.0 ([#3300](https://github.com/leanprover-community/mathlib/pull/3300))
#### Estimated changes
Modified leanpkg.toml


Modified src/control/fold.lean


Modified src/tactic/interactive_expr.lean




## [2020-07-06 16:58:21](https://github.com/leanprover-community/mathlib/commit/f06e4e0)
feat(data/sym2) Defining the symmetric square (unordered pairs) ([#3264](https://github.com/leanprover-community/mathlib/pull/3264))
This adds a type for the symmetric square of a type, which is the quotient of the cartesian square by permutations.  These are also known as unordered pairs.
Additionally, this provides some definitions and lemmas for equalities, functoriality, membership, and a relationship between symmetric relations and terms of the symmetric square.
I preferred `sym2` over `unordered_pairs` out of a combination of familiarity and brevity, but I could go either way for naming.
#### Estimated changes
Created src/data/sym.lean
- \+ *def* sym
- \+ *def* vector.perm.is_setoid
- \+ *def* sym'
- \+ *def* sym_equiv_sym'

Created src/data/sym2.lean
- \+ *lemma* rel.symm
- \+ *lemma* rel.trans
- \+ *lemma* rel.is_equivalence
- \+ *lemma* eq_swap
- \+ *lemma* congr_right
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* mk_has_mem
- \+ *lemma* vmem_other_spec
- \+ *lemma* mem_other_spec
- \+ *lemma* other_is_mem_other
- \+ *lemma* eq_iff
- \+ *lemma* mem_iff
- \+ *lemma* is_diag_iff_proj_eq
- \+ *lemma* from_rel_proj_prop
- \+ *lemma* from_rel_prop
- \+ *lemma* from_rel_irreflexive
- \+ *def* sym2
- \+ *def* map
- \+ *def* mem
- \+ *def* vmem
- \+ *def* mk_has_vmem
- \+ *def* vmem.other
- \+ *def* diag
- \+ *def* is_diag
- \+ *def* from_rel
- \+ *def* sym2_equiv_sym'
- \+ *def* equiv_sym
- \+ *def* equiv_multiset



## [2020-07-06 15:34:25](https://github.com/leanprover-community/mathlib/commit/e3a1a61)
feat(tactic/interactive): identity tactic ([#3295](https://github.com/leanprover-community/mathlib/pull/3295))
A surprisingly missing tactic combinator.
#### Estimated changes
Modified src/tactic/interactive.lean




## [2020-07-06 14:12:29](https://github.com/leanprover-community/mathlib/commit/33b6cba)
refactor(*): replace nonzero with nontrivial ([#3296](https://github.com/leanprover-community/mathlib/pull/3296))
Introduce a typeclass `nontrivial` saying that a type has at least two distinct elements, and use it instead of the predicate `nonzero` requiring that `0` is different from `1`. These two predicates are equivalent in monoids with zero, which cover essentially all relevant ring-like situations, but `nontrivial` applies also to say that a vector space is nontrivial, for instance.
Along the way, fix some quirks in the alebraic hierarchy (replacing fields `zero_ne_one` in many structures with extending `nontrivial`, for instance). Also, `quadratic_reciprocity` was timing out. I guess it was just below the threshold before the refactoring, and some of the changes related to typeclass inference made it just above after the change. So, I squeeze_simped it, going from 47s to 1.7s on my computer.
Zulip discussion at https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/nonsingleton/near/202865366
#### Estimated changes
Modified src/algebra/associated.lean
- \+/\- *theorem* associated_zero_iff_eq_zero

Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/char_p.lean
- \+/\- *lemma* false_of_nonzero_of_char_one
- \+/\- *lemma* ring_char_ne_one

Modified src/algebra/classical_lie_algebras.lean
- \+/\- *lemma* sl_non_abelian

Modified src/algebra/direct_limit.lean


Modified src/algebra/euclidean_domain.lean


Modified src/algebra/field.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/group_with_zero.lean
- \+/\- *lemma* zero_ne_one
- \+/\- *lemma* one_ne_zero
- \+/\- *lemma* ne_zero_of_eq_one
- \+/\- *lemma* left_ne_zero_of_mul_eq_one
- \+/\- *lemma* right_ne_zero_of_mul_eq_one
- \+/\- *lemma* ne_zero
- \- *lemma* subsingleton_or_nonzero
- \+/\- *theorem* not_is_unit_zero

Modified src/algebra/opposites.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/ring.lean
- \+/\- *lemma* succ_ne_self
- \+/\- *lemma* pred_ne_self
- \+/\- *lemma* units.coe_ne_zero
- \- *theorem* nonzero.of_ne

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* units.norm_pos
- \+/\- *lemma* normed_algebra.to_nonzero
- \+/\- *theorem* interior_closed_ball'
- \+/\- *theorem* frontier_closed_ball'

Modified src/analysis/normed_space/hahn_banach.lean
- \+/\- *theorem* exists_dual_vector'

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* norm_id
- \+/\- *lemma* one_le_norm_mul_norm_symm
- \+/\- *lemma* norm_pos
- \+/\- *lemma* norm_symm_pos

Modified src/analysis/normed_space/units.lean


Modified src/data/complex/basic.lean


Modified src/data/equiv/ring.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_le_one_iff_subsingleton
- \+ *lemma* fintype.one_lt_card_iff_nontrivial

Modified src/data/int/basic.lean


Modified src/data/matrix/pequiv.lean
- \+/\- *lemma* to_matrix_injective

Modified src/data/mv_polynomial.lean
- \+/\- *lemma* total_degree_X

Modified src/data/nat/basic.lean


Modified src/data/num/lemmas.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/polynomial.lean
- \+/\- *lemma* monic.ne_zero
- \+/\- *theorem* nonzero.of_polynomial_ne

Modified src/data/rat/basic.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/nnreal.lean


Modified src/data/zmod/basic.lean


Modified src/data/zsqrtd/basic.lean
- \+/\- *theorem* conj_mul

Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/perfect_closure.lean


Modified src/field_theory/subfield.lean


Modified src/group_theory/free_abelian_group.lean
- \+ *lemma* mul_def

Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* exists_mem_ne_zero_of_dim_pos
- \+/\- *lemma* dim_pos_iff_exists_ne_zero
- \+ *lemma* dim_pos_iff_nontrivial
- \+ *lemma* dim_pos
- \+/\- *theorem* is_basis.le_span

Created src/logic/nontrivial.lean
- \+ *lemma* nontrivial_iff
- \+ *lemma* exists_pair_ne
- \+ *lemma* exists_ne
- \+ *lemma* nontrivial_of_ne
- \+ *lemma* subsingleton_iff
- \+ *lemma* not_nontrivial_iff_subsingleton
- \+ *lemma* subsingleton_or_nontrivial

Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/order/filter/filter_product.lean


Modified src/order/filter/germ.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/fintype.lean
- \+/\- *lemma* card_units_lt

Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/free_ring.lean


Modified src/ring_theory/ideal_operations.lean
- \+/\- *lemma* not_one_mem_ker

Modified src/ring_theory/ideals.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/noetherian.lean
- \+/\- *lemma* finite_of_linear_independent

Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/power_series.lean


Modified src/ring_theory/prod.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/set_theory/cardinal.lean
- \+ *theorem* one_lt_iff_nontrivial

Modified src/set_theory/ordinal.lean


Modified src/topology/metric_space/isometry.lean




## [2020-07-06 13:27:20](https://github.com/leanprover-community/mathlib/commit/2c9d9bd)
chore(scripts/nolints_summary.sh): list number of nolints per file
#### Estimated changes
Created scripts/nolints_summary.sh




## [2020-07-06 07:16:47](https://github.com/leanprover-community/mathlib/commit/5ff099b)
feat(topology): preliminaries for Haar measure ([#3194](https://github.com/leanprover-community/mathlib/pull/3194))
Define group operations on sets
Define compacts, in a similar way to opens
Prove some "separation" properties for topological groups
Rename `continuous.comap` to `opens.comap` (so that we can have comaps for other kinds of sets in topological spaces)
Rename `inf_val` to `inf_def` (unused)
Move some definitions from `topology.opens` to `topology.compacts`
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* sup_coe
- \+ *lemma* inf_def
- \+ *lemma* inf_coe
- \- *lemma* inf_val

Modified src/data/real/ennreal.lean
- \+ *lemma* mul_pos
- \+ *lemma* inv_lt_top
- \+ *lemma* div_lt_top
- \+ *lemma* infi_mul
- \+ *lemma* mul_infi

Modified src/order/bounded_lattice.lean


Modified src/topology/algebra/group.lean
- \+ *lemma* one_open_separated_mul
- \+ *lemma* compact_open_separated_mul
- \+ *lemma* compact_covered_by_mul_left_translates

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tsum_subtype_eq_sum

Modified src/topology/basic.lean
- \+ *lemma* is_open.preimage
- \+ *lemma* is_closed.preimage

Created src/topology/compacts.lean
- \+ *lemma* bot_val
- \+ *lemma* sup_val
- \+ *lemma* finset_sup_val
- \+ *lemma* map_val
- \+ *lemma* equiv_to_fun_val
- \+ *def* closeds
- \+ *def* compacts
- \+ *def* nonempty_compacts
- \+ *def* positive_compacts:
- \+ *def* nonempty_compacts.to_closeds

Modified src/topology/constructions.lean
- \+ *lemma* exists_nhds_square

Modified src/topology/homeomorph.lean
- \+ *lemma* is_open_preimage

Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/isometry.lean


Modified src/topology/opens.lean
- \+ *lemma* val_eq_coe
- \+/\- *lemma* ext
- \+ *lemma* ext_iff
- \+/\- *lemma* gc
- \+/\- *lemma* Sup_s
- \+ *lemma* supr_def
- \+/\- *lemma* comap_id
- \+/\- *lemma* comap_mono
- \+ *lemma* coe_comap
- \+ *lemma* comap_val
- \+/\- *def* opens
- \+/\- *def* gi
- \+/\- *def* is_basis
- \+/\- *def* comap
- \+ *def* open_nhds_of
- \- *def* closeds
- \- *def* nonempty_compacts
- \- *def* nonempty_compacts.to_closeds

Modified src/topology/separation.lean
- \+ *lemma* compact.inter
- \+ *lemma* compact.binary_compact_cover
- \+ *lemma* compact.finite_compact_cover
- \+ *lemma* exists_open_with_compact_closure
- \+ *lemma* exists_compact_superset

Modified src/topology/subset_properties.lean
- \+ *lemma* compact_univ_pi
- \+ *lemma* exists_compact_subset



## [2020-07-06 05:41:46](https://github.com/leanprover-community/mathlib/commit/2e140f1)
refactor(algebra/inj_surj): more lemmas, move to files, rename ([#3290](https://github.com/leanprover-community/mathlib/pull/3290))
* use names `function.?jective.monoid` etc;
* move definitions to different files;
* add versions for `semimodules` and various `*_with_zero`;
* add `funciton.surjective.forall` etc.
#### Estimated changes
Created src/algebra/group/inj_surj.lean


Modified src/algebra/group_with_zero.lean


Deleted src/algebra/inj_surj.lean
- \- *def* semigroup_of_injective
- \- *def* comm_semigroup_of_injective
- \- *def* semigroup_of_surjective
- \- *def* comm_semigroup_of_surjective
- \- *def* monoid_of_injective
- \- *def* comm_monoid_of_injective
- \- *def* group_of_injective
- \- *def* comm_group_of_injective
- \- *def* monoid_of_surjective
- \- *def* comm_monoid_of_surjective
- \- *def* group_of_surjective
- \- *def* comm_group_of_surjective
- \- *def* semiring_of_injective
- \- *def* comm_semiring_of_injective
- \- *def* ring_of_injective
- \- *def* comm_ring_of_injective
- \- *def* semiring_of_surjective
- \- *def* comm_semiring_of_surjective
- \- *def* ring_of_surjective
- \- *def* comm_ring_of_surjective

Modified src/algebra/module.lean


Modified src/algebra/ring.lean
- \+/\- *lemma* cancel_right
- \+/\- *lemma* cancel_left

Modified src/group_theory/group_action.lean
- \- *lemma* bijective

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* coe_injective

Modified src/group_theory/submonoid/operations.lean


Modified src/logic/function/basic.lean
- \+ *lemma* injective.ne_iff'
- \+ *theorem* injective.eq_iff'
- \+ *theorem* surjective.forall
- \+ *theorem* surjective.forall₂
- \+ *theorem* surjective.forall₃
- \+ *theorem* surjective.exists
- \+ *theorem* surjective.exists₂
- \+ *theorem* surjective.exists₃



## [2020-07-06 04:31:33](https://github.com/leanprover-community/mathlib/commit/ffa504c)
fix(finset/lattice): undo removal of bUnion_preimage_singleton ([#3293](https://github.com/leanprover-community/mathlib/pull/3293))
In [#3189](https://github.com/leanprover-community/mathlib/pull/3189) I removed it, which was a mistake.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* bUnion_preimage_singleton



## [2020-07-06 00:39:48](https://github.com/leanprover-community/mathlib/commit/e1f6ed2)
chore(scripts): update nolints.txt ([#3294](https://github.com/leanprover-community/mathlib/pull/3294))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-05 10:40:51](https://github.com/leanprover-community/mathlib/commit/0cd500e)
doc(tactic/explode): expand doc string ([#3271](https://github.com/leanprover-community/mathlib/pull/3271))
Explanation copied from @digama0's Zulip message [here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.23explode.20error/near/202396813). Also removed a redundant function and added some type ascriptions.
#### Estimated changes
Modified src/tactic/explode.lean
- \- *def* head'



## [2020-07-05 10:13:00](https://github.com/leanprover-community/mathlib/commit/293287d)
chore(category_theory/over/limits): change instance to def ([#3281](https://github.com/leanprover-community/mathlib/pull/3281))
Having this as an instance causes confusion since it's a different terminal object to the one inferred by the other limit constructions in the file.
#### Estimated changes
Modified src/category_theory/limits/over.lean
- \+ *def* over_has_terminal



## [2020-07-05 09:46:41](https://github.com/leanprover-community/mathlib/commit/f39e0d7)
chore(algebra/category): use preadditivity for biproducts ([#3280](https://github.com/leanprover-community/mathlib/pull/3280))
We can avoid some scary calculations thanks to abstract nonsense.
#### Estimated changes
Modified src/algebra/category/Group/biproducts.lean
- \- *lemma* desc_apply
- \- *def* desc



## [2020-07-04 19:11:32](https://github.com/leanprover-community/mathlib/commit/023d4f7)
feat(ring_theory/localization): order embedding of ideals, local ring instance ([#3287](https://github.com/leanprover-community/mathlib/pull/3287))
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/localization.lean
- \+ *lemma* mk'_surjective
- \+/\- *lemma* mk'_self
- \+ *lemma* mk'_mul_mk'_eq_one
- \+ *lemma* mk'_mul_mk'_eq_one'
- \+ *theorem* map_comap
- \+/\- *def* codomain
- \+ *def* prime_compl
- \+ *def* at_prime
- \+ *def* le_order_embedding



## [2020-07-04 15:02:36](https://github.com/leanprover-community/mathlib/commit/08e1adc)
feat(data/pnat): basic pnat facts needed for perfect numbers (3094) ([#3274](https://github.com/leanprover-community/mathlib/pull/3274))
define pnat.coprime
add some basic lemmas pnats, mostly about coprime, gcd
designate some existing lemmas with @[simp]
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* coe_inj
- \+ *lemma* coe_eq_one_iff
- \+ *lemma* le_of_dvd
- \+ *lemma* eq_one_of_lt_two
- \+ *lemma* prime.one_lt
- \+ *lemma* prime_two
- \+ *lemma* dvd_prime
- \+ *lemma* prime.ne_one
- \+ *lemma* not_prime_one
- \+ *lemma* prime.not_dvd_one
- \+ *lemma* exists_prime_and_dvd
- \+ *lemma* coprime_coe
- \+ *lemma* coprime.mul
- \+ *lemma* coprime.mul_right
- \+ *lemma* gcd_comm
- \+ *lemma* gcd_eq_left_iff_dvd
- \+ *lemma* gcd_eq_right_iff_dvd
- \+ *lemma* coprime.gcd_mul_left_cancel
- \+ *lemma* coprime.gcd_mul_right_cancel
- \+ *lemma* coprime.gcd_mul_left_cancel_right
- \+ *lemma* coprime.gcd_mul_right_cancel_right
- \+ *lemma* one_gcd
- \+ *lemma* gcd_one
- \+ *lemma* coprime.symm
- \+ *lemma* one_coprime
- \+ *lemma* coprime_one
- \+ *lemma* coprime.coprime_dvd_left
- \+ *lemma* coprime.factor_eq_gcd_left
- \+ *lemma* coprime.factor_eq_gcd_right
- \+ *lemma* coprime.factor_eq_gcd_left_right
- \+ *lemma* coprime.factor_eq_gcd_right_right
- \+ *lemma* coprime.gcd_mul
- \+ *lemma* gcd_eq_left
- \+ *lemma* coprime.pow
- \+ *def* coprime

Modified test/interval_cases.lean




## [2020-07-04 08:32:44](https://github.com/leanprover-community/mathlib/commit/0d249d7)
feat(analysis/normed_space/*): group of units of a normed ring is open ([#3210](https://github.com/leanprover-community/mathlib/pull/3210))
In a complete normed ring, the group of units is an open subset of the ring ([Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Inversion.20is.20analytic))
Supporting material:
* `topology.metric_space.basic`, `analysis.normed_space.basic`, `normed_space.operator_norm`: some lemmas about limits and infinite sums in metric and normed spaces
* `analysis.normed_space.basic`, `normed_space.operator_norm`: left- and right- multiplication in a normed ring (algebra) is a bounded homomorphism (linear map); the algebra/linear-map versions are not needed for the main result but included for completeness
* `analysis.normed_space.basic`: a normed algebra is `nonzero` (not needed for the main result) ([Zulip](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Dangerous.20instance))
* `algebra.group_with_zero`: the `subsingleton_or_nonzero` dichotomy for monoids with zero ([Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/zero.20ring/near/202202187)) (written by @jcommelin )
* `analysis.specific_limits`: results on geometric series in a complete `normed_ring`; relies on
* `algebra.geom_sum`: "left" variants of some existing "right" lemmas on finite geometric series; relies on
* `algebra.opposites`, `algebra.group_power`, `algebra.big_operators`: lemmas about the opposite ring ([Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Finite.20geometric.20series))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* op_sum
- \+ *lemma* unop_sum

Modified src/algebra/geom_sum.lean
- \+ *lemma* op_geom_series
- \+ *lemma* mul_geom_sum
- \+ *lemma* mul_neg_geom_sum

Modified src/algebra/group_power.lean
- \+ *lemma* op_pow
- \+ *lemma* unop_pow

Modified src/algebra/group_with_zero.lean
- \+ *lemma* subsingleton_or_nonzero

Modified src/algebra/opposites.lean
- \+ *lemma* op_sub
- \+ *lemma* unop_sub
- \+ *lemma* coe_op_add_hom
- \+ *lemma* coe_unop_add_hom
- \+ *def* op_add_hom
- \+ *def* unop_add_hom

Modified src/algebra/ring.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* add_monoid_hom.lipschitz_of_bound
- \+ *lemma* add_monoid_hom.continuous_of_bound
- \+ *lemma* squeeze_zero_norm'
- \+ *lemma* squeeze_zero_norm
- \+ *lemma* eventually_norm_pow_le
- \+ *lemma* units.norm_pos
- \+ *lemma* mul_left_bound
- \+ *lemma* mul_right_bound
- \+ *lemma* normed_algebra.norm_one
- \+ *lemma* normed_algebra.zero_ne_one
- \+ *lemma* normed_algebra.to_nonzero
- \+ *lemma* has_sum_of_bounded_monoid_hom_of_has_sum
- \+ *lemma* has_sum_of_bounded_monoid_hom_of_summable
- \+ *lemma* summable_of_norm_bounded_eventually

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* lmul_left_apply
- \+ *lemma* lmul_right_apply
- \+ *lemma* continuous_linear_map.has_sum
- \+ *lemma* continuous_linear_map.has_sum_of_summable
- \+ *def* lmul_left
- \+ *def* lmul_right

Created src/analysis/normed_space/units.lean
- \+ *lemma* one_sub_coe
- \+ *lemma* add_coe
- \+ *lemma* unit_of_nearby_coe
- \+ *lemma* is_open
- \+ *def* one_sub
- \+ *def* add
- \+ *def* unit_of_nearby

Modified src/analysis/specific_limits.lean
- \+/\- *lemma* tendsto_pow_at_top_nhds_0_of_norm_lt_1
- \+ *lemma* normed_ring.summable_geometric_of_norm_lt_1
- \+ *lemma* geom_series_mul_neg
- \+ *lemma* mul_neg_geom_series

Modified src/topology/metric_space/basic.lean
- \+ *lemma* squeeze_zero'



## [2020-07-04 06:17:21](https://github.com/leanprover-community/mathlib/commit/c2886d3)
fix(tactic/default): import tactic.basic ([#3284](https://github.com/leanprover-community/mathlib/pull/3284))
Some basic tactics and commands (e.g. `#explode`) were not available even if `import tactic` was used. I added `import tactic.basic` to `tactic/default.lean` to remedy this.
#### Estimated changes
Modified src/tactic/default.lean




## [2020-07-04 00:39:31](https://github.com/leanprover-community/mathlib/commit/2a43e26)
chore(scripts): update nolints.txt ([#3283](https://github.com/leanprover-community/mathlib/pull/3283))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-03 23:00:44](https://github.com/leanprover-community/mathlib/commit/742dc88)
feat(ring_theory/polynomial): rational root theorem and integral root theorem ([#3241](https://github.com/leanprover-community/mathlib/pull/3241))
Prove the rational root theorem for a unique factorization domain `A`: Let `K` be the field of fractions of `A` and `p` a polynomial over `A`. If `x : K` is a root of `p`, then the numerator of `x` divides the constant coefficient and the denominator of `x` divides the leading coefficient. (This required defining the numerator and denominator.) As a corollary we have the integral root theorem: if `p` is monic, then its roots in `K` are in fact elements of `A`. As a second corollary, the integral closure of `A` in `K` is `A` itself.
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* dvd_of_dvd_pow
- \+ *lemma* dvd_symm_of_irreducible
- \+ *lemma* dvd_symm_iff_of_irreducible

Modified src/algebra/field.lean
- \+ *lemma* map_units_inv

Modified src/algebra/group/units.lean
- \+ *lemma* is_unit.mul

Modified src/algebra/group_with_zero.lean
- \+ *lemma* map_units_inv

Modified src/algebra/ring.lean
- \+ *lemma* mul_right_dvd_of_dvd
- \+ *lemma* mul_left_dvd_of_dvd

Modified src/data/polynomial.lean
- \+ *lemma* is_root_of_eval₂_map_eq_zero
- \+ *lemma* is_root_of_aeval_algebra_map_eq_zero
- \+ *lemma* dvd_term_of_dvd_eval_of_dvd_terms
- \+ *lemma* dvd_term_of_is_root_of_dvd_terms

Modified src/ring_theory/integral_domain.lean
- \+ *lemma* left_dvd_or_dvd_right_of_dvd_prime_mul

Modified src/ring_theory/localization.lean
- \+ *lemma* mul_mem_non_zero_divisors
- \+ *lemma* exists_reduced_fraction
- \+ *lemma* num_denom_reduced
- \+ *lemma* mk'_num_denom
- \+ *lemma* num_mul_denom_eq_num_iff_eq
- \+ *lemma* num_mul_denom_eq_num_iff_eq'
- \+ *lemma* num_mul_denom_eq_num_mul_denom_iff_eq
- \+ *lemma* eq_zero_of_num_eq_zero
- \+ *lemma* is_integer_of_is_unit_denom
- \+ *lemma* is_unit_denom_of_num_eq_zero

Created src/ring_theory/polynomial/rational_root.lean
- \+ *lemma* coeff_scale_roots
- \+ *lemma* coeff_scale_roots_nat_degree
- \+ *lemma* zero_scale_roots
- \+ *lemma* scale_roots_ne_zero
- \+ *lemma* support_scale_roots_le
- \+ *lemma* support_scale_roots_eq
- \+ *lemma* degree_scale_roots
- \+ *lemma* nat_degree_scale_roots
- \+ *lemma* monic_scale_roots_iff
- \+ *lemma* scale_roots_eval₂_eq_zero
- \+ *lemma* scale_roots_aeval_eq_zero
- \+ *lemma* scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero
- \+ *lemma* scale_roots_aeval_eq_zero_of_aeval_div_eq_zero
- \+ *lemma* scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero
- \+ *lemma* num_is_root_scale_roots_of_aeval_eq_zero
- \+ *lemma* integer_of_integral
- \+ *lemma* integrally_closed
- \+ *theorem* num_dvd_of_is_root
- \+ *theorem* denom_dvd_of_is_root
- \+ *theorem* is_integer_of_is_root_of_monic

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* no_factors_of_no_prime_factors
- \+ *lemma* dvd_of_dvd_mul_left_of_no_prime_factors
- \+ *lemma* dvd_of_dvd_mul_right_of_no_prime_factors
- \+ *lemma* exists_reduced_factors
- \+ *lemma* exists_reduced_factors'



## [2020-07-03 22:00:28](https://github.com/leanprover-community/mathlib/commit/c4bf9e4)
chore(algebra/ordered_group): deduplicate ([#3279](https://github.com/leanprover-community/mathlib/pull/3279))
For historical reasons we have some lemmas duplicated for `ordered_comm_monoid`
and `ordered_cancel_comm_monoid`. This PR merges some duplicates.
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/algebra/group_power.lean


Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/ordered_group.lean
- \+/\- *lemma* mul_le_mul_left'
- \+/\- *lemma* mul_le_mul_right'
- \+/\- *lemma* mul_le_mul_three
- \+/\- *lemma* le_mul_of_one_le_right
- \+/\- *lemma* le_mul_of_one_le_left
- \+/\- *lemma* le_mul_of_one_le_of_le
- \+/\- *lemma* le_mul_of_le_of_one_le
- \+/\- *lemma* one_le_mul
- \+ *lemma* one_lt_mul_of_lt_of_le'
- \+ *lemma* one_lt_mul_of_le_of_lt'
- \+ *lemma* one_lt_mul'
- \+/\- *lemma* mul_lt_mul_left'
- \- *lemma* le_mul_of_one_le_right''
- \- *lemma* le_mul_of_one_le_left''
- \- *lemma* le_mul_of_one_le_of_le'
- \- *lemma* le_mul_of_le_of_one_le'
- \- *lemma* one_le_mul'
- \- *lemma* mul_one_lt_of_one_lt_of_one_le'
- \- *lemma* mul_one_lt'
- \- *lemma* mul_one_lt_of_one_le_of_one_lt'
- \- *lemma* one_le_mul_of_one_le_of_one_le
- \- *lemma* mul_le_one_of_le_one_of_le_one
- \- *lemma* mul_le_mul_left''
- \- *lemma* lt_of_mul_lt_mul_left''
- \- *lemma* mul_le_mul_right''
- \- *lemma* lt_of_mul_lt_mul_right''
- \- *lemma* mul_one_lt
- \- *lemma* mul_one_lt_of_one_lt_of_one_le
- \- *lemma* mul_one_lt_of_one_le_of_one_lt
- \- *lemma* mul_le_one''
- \- *lemma* mul_eq_one_iff_eq_one_and_eq_one_of_one_le_of_one_le

Modified src/algebra/pi_instances.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/specific_limits.lean


Modified src/data/complex/exponential.lean


Modified src/data/list/basic.lean


Modified src/data/multiset/basic.lean


Modified src/data/nat/enat.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/polynomial.lean


Modified src/data/real/ennreal.lean


Modified src/geometry/euclidean.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/lagrange.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/outer_measure.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* tendsto_at_top_mono'
- \+/\- *lemma* tendsto_at_top_add_nonneg_left'
- \+/\- *lemma* tendsto_at_top_add_nonneg_right'
- \+/\- *lemma* tendsto_at_top_of_add_bdd_above_left'
- \+/\- *lemma* tendsto_at_top_of_add_bdd_above_right'
- \+/\- *lemma* tendsto_at_top_add_left_of_le'
- \+/\- *lemma* tendsto_at_top_add_right_of_le'

Modified src/order/filter/germ.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/hausdorff_distance.lean




## [2020-07-03 22:00:26](https://github.com/leanprover-community/mathlib/commit/f1637e5)
feat(field_theory/splitting_field): definition of splitting field ([#3272](https://github.com/leanprover-community/mathlib/pull/3272))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* nat_degree_le_nat_degree
- \+ *lemma* nat_degree_X_le
- \+ *lemma* nat_degree_X
- \+/\- *lemma* nat_degree_X_sub_C
- \+ *lemma* root_mul
- \+ *lemma* roots_mul
- \+ *lemma* roots_X_sub_C
- \+/\- *theorem* nat_degree_le_of_degree_le
- \+ *theorem* not_is_unit_X
- \+ *theorem* X_dvd_iff
- \+ *theorem* nat_degree_div_by_monic
- \+ *theorem* X_sub_C_ne_zero
- \+ *theorem* not_is_unit_X_sub_C
- \+ *theorem* prime_X_sub_C
- \+ *theorem* prime_X
- \+ *theorem* irreducible_X_sub_C
- \+ *theorem* irreducible_X

Modified src/field_theory/splitting_field.lean
- \+ *lemma* splits_of_splits_of_dvd
- \+ *theorem* factor_dvd_of_not_is_unit
- \+ *theorem* factor_dvd_of_degree_ne_zero
- \+ *theorem* factor_dvd_of_nat_degree_ne_zero
- \+ *theorem* X_sub_C_mul_remove_factor
- \+ *theorem* nat_degree_remove_factor
- \+ *theorem* nat_degree_remove_factor'
- \+ *theorem* succ
- \+ *theorem* algebra_map_succ
- \+ *theorem* exists_lift
- \+ *theorem* adjoin_roots
- \+ *def* factor
- \+ *def* remove_factor
- \+ *def* splitting_field_aux
- \+ *def* splitting_field
- \+ *def* lift

Modified src/ring_theory/adjoin_root.lean
- \+ *lemma* algebra_map_eq
- \+ *lemma* mk_X
- \+ *lemma* aeval_eq
- \+/\- *lemma* lift_root
- \+ *lemma* lift_comp_of
- \+ *theorem* induction_on
- \+ *theorem* adjoin_root_eq_top

Modified src/ring_theory/algebra.lean
- \+ *theorem* map_le
- \+ *theorem* map_top
- \+ *theorem* map_bot
- \+ *theorem* comap_top
- \+ *def* map
- \+ *def* comap'

Created src/ring_theory/algebra_tower.lean
- \+ *lemma* algebra.ext
- \+ *theorem* algebra_map_eq
- \+ *theorem* algebra_map_apply
- \+ *theorem* of_algebra_map_eq
- \+ *theorem* comap_eq
- \+ *theorem* subalgebra_comap_top
- \+ *theorem* range_under_adjoin
- \+ *theorem* adjoin_algebra_map'
- \+ *theorem* adjoin_algebra_map
- \+ *def* to_alg_hom
- \+ *def* subalgebra_comap

Modified src/ring_theory/polynomial/basic.lean
- \+ *theorem* exists_irreducible_of_degree_pos
- \+ *theorem* exists_irreducible_of_nat_degree_pos
- \+ *theorem* exists_irreducible_of_nat_degree_ne_zero



## [2020-07-03 20:42:56](https://github.com/leanprover-community/mathlib/commit/48dea2f)
feat(algebra/pointwise): make instances global ([#3240](https://github.com/leanprover-community/mathlib/pull/3240))
add image2 and image3, the images of binary and ternary functions
cleanup in algebra/pointwise
make many variables implicit
make many names shorter
add some lemmas
add more simp lemmas
add type set_semiring as alias for set, with semiring instance using union as "addition"
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* singleton_one
- \+ *lemma* mem_one
- \+ *lemma* one_mem_one
- \+ *lemma* image2_mul
- \+ *lemma* mem_mul
- \+ *lemma* mul_mem_mul
- \+ *lemma* image_mul_prod
- \+ *lemma* image_mul_left
- \+ *lemma* image_mul_right
- \+ *lemma* image_mul_left'
- \+ *lemma* image_mul_right'
- \+ *lemma* preimage_mul_left_one
- \+ *lemma* preimage_mul_right_one
- \+ *lemma* preimage_mul_left_one'
- \+ *lemma* preimage_mul_right_one'
- \+ *lemma* mul_singleton
- \+ *lemma* singleton_mul
- \+ *lemma* singleton_mul_singleton
- \+/\- *lemma* singleton.is_mul_hom
- \+ *lemma* empty_mul
- \+ *lemma* mul_empty
- \+ *lemma* mul_subset_mul
- \+ *lemma* union_mul
- \+ *lemma* mul_union
- \+ *lemma* Union_mul_left_image
- \+ *lemma* Union_mul_right_image
- \+ *lemma* univ_mul_univ
- \+ *lemma* nonempty.mul
- \+ *lemma* finite.mul
- \+ *lemma* mem_inv
- \+ *lemma* inv_mem_inv
- \+ *lemma* inv_preimage
- \+ *lemma* image_inv
- \+ *lemma* inter_inv
- \+ *lemma* union_inv
- \+ *lemma* compl_inv
- \+ *lemma* image_smul
- \+/\- *lemma* mem_smul_set
- \+/\- *lemma* smul_mem_smul_set
- \+/\- *lemma* smul_set_union
- \+/\- *lemma* smul_set_empty
- \+/\- *lemma* smul_set_mono
- \+ *lemma* image2_smul
- \+ *lemma* mem_smul
- \+ *lemma* image_smul_prod
- \+ *lemma* singleton_smul
- \+ *lemma* image_mul
- \+ *lemma* preimage_mul_preimage_subset
- \+/\- *lemma* zero_smul_set
- \+/\- *lemma* mem_inv_smul_set_iff
- \+/\- *lemma* mem_smul_set_iff_inv_smul_mem
- \- *lemma* mem_pointwise_one
- \- *lemma* mem_pointwise_mul
- \- *lemma* mul_mem_pointwise_mul
- \- *lemma* pointwise_mul_eq_image
- \- *lemma* pointwise_mul_finite
- \- *lemma* singleton.is_monoid_hom
- \- *lemma* pointwise_mul_empty
- \- *lemma* empty_pointwise_mul
- \- *lemma* pointwise_mul_subset_mul
- \- *lemma* pointwise_mul_union
- \- *lemma* union_pointwise_mul
- \- *lemma* pointwise_mul_eq_Union_mul_left
- \- *lemma* pointwise_mul_eq_Union_mul_right
- \- *lemma* nonempty.pointwise_mul
- \- *lemma* univ_pointwise_mul_univ
- \- *lemma* smul_set_eq_image
- \- *lemma* smul_set_eq_pointwise_smul_singleton
- \- *lemma* image_pointwise_mul
- \- *lemma* preimage_pointwise_mul_preimage_subset
- \+ *theorem* one_subset
- \+ *theorem* one_nonempty
- \+ *theorem* image_one
- \+ *def* singleton_hom
- \+ *def* fintype_mul
- \+ *def* set_semiring
- \+ *def* image_hom
- \- *def* pointwise_one
- \- *def* pointwise_mul
- \- *def* pointwise_mul_semigroup
- \- *def* pointwise_mul_monoid
- \- *def* pointwise_inv
- \- *def* pointwise_mul_fintype
- \- *def* pointwise_add_fintype
- \- *def* pointwise_smul
- \- *def* smul_set
- \- *def* pointwise_mul_semiring
- \- *def* pointwise_mul_comm_semiring
- \- *def* comm_monoid
- \- *def* add_comm_monoid
- \- *def* smul_set_action
- \- *def* pointwise_mul_image_ring_hom

Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/convex/topology.lean


Modified src/data/set/basic.lean
- \+ *lemma* nonempty_def
- \+ *lemma* image_eta
- \+ *lemma* mem_image2_eq
- \+ *lemma* mem_image2
- \+ *lemma* mem_image2_of_mem
- \+ *lemma* mem_image2_iff
- \+ *lemma* image2_subset
- \+ *lemma* image2_union_left
- \+ *lemma* image2_union_right
- \+ *lemma* image2_empty_left
- \+ *lemma* image2_empty_right
- \+ *lemma* image2_inter_subset_left
- \+ *lemma* image2_inter_subset_right
- \+ *lemma* image2_singleton
- \+ *lemma* image2_singleton_left
- \+ *lemma* image2_singleton_right
- \+ *lemma* image2_congr
- \+ *lemma* image2_congr'
- \+ *lemma* mem_image3
- \+ *lemma* image3_congr
- \+ *lemma* image3_congr'
- \+ *lemma* image2_image2_left
- \+ *lemma* image2_image2_right
- \+ *lemma* image_image2
- \+ *lemma* image2_image_left
- \+ *lemma* image2_image_right
- \+ *lemma* image2_swap
- \+ *lemma* image2_left
- \+ *lemma* image2_right
- \+ *lemma* image_prod
- \+ *lemma* nonempty.image2
- \+/\- *lemma* eq_univ_of_nonempty
- \+/\- *lemma* set_cases
- \+ *def* image2
- \+ *def* image3

Modified src/data/set/finite.lean
- \+ *lemma* finite.image2

Modified src/data/set/intervals/image_preimage.lean
- \+/\- *lemma* preimage_neg_Ici
- \+/\- *lemma* preimage_neg_Iic
- \+/\- *lemma* preimage_neg_Ioi
- \+/\- *lemma* preimage_neg_Iio
- \+/\- *lemma* preimage_neg_Icc
- \+/\- *lemma* preimage_neg_Ico
- \+/\- *lemma* preimage_neg_Ioc
- \+/\- *lemma* preimage_neg_Ioo
- \+/\- *lemma* image_add_const_Ici
- \+/\- *lemma* image_add_const_Iic
- \+/\- *lemma* image_add_const_Iio
- \+/\- *lemma* image_add_const_Ioi
- \+/\- *lemma* image_neg_Ici
- \+/\- *lemma* image_neg_Iic
- \+/\- *lemma* image_neg_Ioi
- \+/\- *lemma* image_neg_Iio
- \+/\- *lemma* image_neg_Icc
- \+/\- *lemma* image_neg_Ico
- \+/\- *lemma* image_neg_Ioc
- \+/\- *lemma* image_neg_Ioo

Modified src/data/set/lattice.lean
- \+ *lemma* Union_image_left
- \+ *lemma* Union_image_right

Modified src/group_theory/group_action.lean
- \+ *lemma* inv_smul_eq_iff
- \+ *lemma* eq_inv_smul_iff

Modified src/logic/function/basic.lean
- \+ *lemma* eq_iff
- \+ *def* injective2

Modified src/order/filter/pointwise.lean
- \+ *lemma* mem_one
- \+ *lemma* mem_mul
- \+ *lemma* mul_mem_mul
- \+ *lemma* mul_ne_bot
- \+ *lemma* map.is_monoid_hom
- \- *lemma* mem_pointwise_one
- \- *lemma* mem_pointwise_mul
- \- *lemma* mul_mem_pointwise_mul
- \- *lemma* pointwise_mul_le_mul
- \- *lemma* pointwise_mul_ne_bot
- \- *lemma* pointwise_mul_assoc
- \- *lemma* pointwise_one_mul
- \- *lemma* pointwise_mul_one
- \- *lemma* map_pointwise_mul
- \- *lemma* map_pointwise_one
- \- *lemma* pointwise_mul_map_is_monoid_hom
- \- *lemma* pointwise_add_map_is_add_monoid_hom
- \- *def* pointwise_one
- \- *def* pointwise_mul
- \- *def* pointwise_mul_monoid

Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/algebra_operations.lean
- \+/\- *lemma* mul_subset_mul
- \+/\- *lemma* pow_subset_pow
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_le_smul
- \+/\- *def* span.ring_hom

Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideals.lean
- \+/\- *lemma* span_singleton_one

Modified src/ring_theory/noetherian.lean


Modified src/topology/algebra/group.lean
- \+ *lemma* is_open_mul_left
- \+ *lemma* is_open_mul_right
- \+ *lemma* nhds_mul
- \+/\- *lemma* nhds_is_mul_hom
- \- *lemma* is_open_pointwise_mul_left
- \- *lemma* is_open_pointwise_mul_right
- \- *lemma* nhds_pointwise_mul

Modified src/topology/metric_space/gromov_hausdorff.lean




## [2020-07-03 15:04:51](https://github.com/leanprover-community/mathlib/commit/f9f0ca6)
feat(analysic/calculus/times_cont_diff): add times_cont_diff_within_at ([#3262](https://github.com/leanprover-community/mathlib/pull/3262))
I want to refactor manifolds, defining local properties in the model space and showing that they automatically inherit nice behavior in manifolds. 
In this PR, we modify a little bit the definition of smooth functions in vector spaces by introducing a predicate `times_cont_diff_within_at` (just like we already have `continuous_within_at` or `differentiable_within_at`) and using it in all definitions and proofs. This will be the basis of the locality argument in manifolds.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_within_at_nat
- \+ *lemma* times_cont_diff_within_at_top
- \+ *lemma* times_cont_diff_within_at.continuous_within_at'
- \+ *lemma* times_cont_diff_within_at.continuous_within_at
- \+ *lemma* times_cont_diff_within_at.congr_of_eventually_eq
- \+ *lemma* times_cont_diff_within_at.congr_of_eventually_eq'
- \+ *lemma* filter.eventually_eq.times_cont_diff_within_at_iff
- \+ *lemma* times_cont_diff_within_at.congr
- \+ *lemma* times_cont_diff_within_at.mono
- \+ *lemma* times_cont_diff_within_at.of_le
- \+ *lemma* times_cont_diff_within_at_inter'
- \+ *lemma* times_cont_diff_within_at_inter
- \+ *lemma* times_cont_diff_within_at.differentiable_within_at'
- \+ *lemma* times_cont_diff_within_at.differentiable_within_at
- \+ *lemma* times_cont_diff_on.times_cont_diff_within_at
- \+ *lemma* times_cont_diff_within_at.times_cont_diff_on
- \+/\- *lemma* times_cont_diff_on_top
- \+/\- *lemma* times_cont_diff_on.continuous_on
- \+ *lemma* times_cont_diff_at_top
- \+ *lemma* times_cont_diff_at.times_cont_diff_within_at
- \+ *lemma* times_cont_diff_within_at.times_cont_diff_at
- \+ *lemma* times_cont_diff_at.of_le
- \+ *lemma* times_cont_diff_at.continuous_at
- \+ *lemma* times_cont_diff_at.differentiable
- \+ *lemma* times_cont_diff_iff_times_cont_diff_at
- \+ *lemma* times_cont_diff.times_cont_diff_at
- \+ *lemma* times_cont_diff_at_const
- \+ *lemma* times_cont_diff_within_at_const
- \+ *lemma* times_cont_diff_within_at.continuous_linear_map_comp
- \+ *lemma* times_cont_diff_at.continuous_linear_map_comp
- \+ *lemma* continuous_linear_equiv.comp_times_cont_diff_within_at_iff
- \+/\- *lemma* continuous_linear_equiv.comp_times_cont_diff_on_iff
- \+ *lemma* times_cont_diff_within_at.comp_continuous_linear_map
- \+/\- *lemma* times_cont_diff_on.comp_continuous_linear_map
- \+ *lemma* continuous_linear_equiv.times_cont_diff_within_at_comp_iff
- \+ *lemma* times_cont_diff_within_at.prod
- \+/\- *lemma* times_cont_diff_on.prod
- \+ *lemma* times_cont_diff_on.comp'
- \+ *lemma* times_cont_diff_within_at.comp
- \+ *lemma* times_cont_diff_within_at.comp'
- \+/\- *lemma* times_cont_diff_on.map_prod
- \+ *lemma* times_cont_diff_at.has_strict_fderiv_at
- \- *lemma* times_cont_diff_on_nat
- \- *lemma* times_cont_diff_on.has_strict_fderiv_at
- \+ *theorem* times_cont_diff_within_at_succ_iff_has_fderiv_within_at
- \+ *theorem* times_cont_diff_within_at_univ
- \+ *def* times_cont_diff_within_at
- \+ *def* times_cont_diff_at

Modified src/data/set/basic.lean
- \+ *lemma* insert_inter

Modified src/topology/continuous_on.lean
- \+ *lemma* mem_nhds_within_insert



## [2020-07-03 09:21:25](https://github.com/leanprover-community/mathlib/commit/53c1531)
feat(geometry/manifold/smooth_manifold_with_corners): product of smooth manifolds with corners ([#3250](https://github.com/leanprover-community/mathlib/pull/3250))
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_on_fst
- \+ *lemma* times_cont_diff_on_snd
- \+ *lemma* times_cont_diff_on.map_prod

Modified src/data/prod.lean
- \+ *lemma* prod_map
- \+/\- *lemma* map_fst
- \+/\- *lemma* map_snd
- \+/\- *lemma* map_fst'
- \+/\- *lemma* map_snd'

Modified src/geometry/manifold/basic_smooth_bundle.lean
- \+/\- *lemma* mem_atlas_iff

Modified src/geometry/manifold/charted_space.lean
- \+ *lemma* model_prod_range_prod_id
- \+ *lemma* prod_charted_space_chart_at
- \+ *def* model_prod

Modified src/geometry/manifold/mfderiv.lean
- \+/\- *lemma* tangent_map_chart_symm

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* model_with_corners_prod_to_local_equiv
- \+ *lemma* model_with_corners_prod_coe
- \+ *lemma* model_with_corners_prod_coe_symm
- \+ *lemma* times_cont_diff_groupoid_prod



## [2020-07-03 08:38:36](https://github.com/leanprover-community/mathlib/commit/e236160)
chore(order/filter/basic): implicit arg in `eventually_of_forall` ([#3277](https://github.com/leanprover-community/mathlib/pull/3277))
Make `l : filter α` argument of `eventually_of_forall` implicit
because everywhere in `mathlib` it was used as `eventually_of_forall _`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/measure_theory/measure_space.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* eventually_of_forall
- \+/\- *lemma* eventually.exists_mem

Modified src/order/filter/filter_product.lean


Modified src/order/filter/germ.lean


Modified src/order/liminf_limsup.lean


Modified src/topology/algebra/ordered.lean




## [2020-07-03 07:27:21](https://github.com/leanprover-community/mathlib/commit/56ed551)
fix(algebra/group_with_zero): fix left/right ([#3278](https://github.com/leanprover-community/mathlib/pull/3278))
Rename `mul_inv_cancel_left'`/`mul_inv_cancel_right'` to match
`mul_inv_cancel_left`/`mul_inv_cancel_right`.
#### Estimated changes
Modified src/algebra/group_with_zero.lean
- \+/\- *lemma* mul_inv_cancel_right'
- \+/\- *lemma* mul_inv_cancel_left'
- \+/\- *lemma* inv_mul_cancel_right'
- \+/\- *lemma* inv_mul_cancel_left'

Modified src/ring_theory/valuation/basic.lean




## [2020-07-03 04:28:12](https://github.com/leanprover-community/mathlib/commit/303740d)
feat(category_theory/abelian): every abelian category is preadditive  ([#3247](https://github.com/leanprover-community/mathlib/pull/3247))
#### Estimated changes
Modified src/category_theory/abelian/basic.lean
- \+ *def* has_finite_biproducts
- \+ *def* abelian

Created src/category_theory/abelian/non_preadditive.lean
- \+ *lemma* mono_of_zero_kernel
- \+ *lemma* epi_of_zero_cokernel
- \+ *lemma* mono_of_cancel_zero
- \+ *lemma* epi_of_zero_cancel
- \+ *lemma* Δ_σ
- \+ *lemma* lift_σ
- \+ *lemma* Δ_map
- \+ *lemma* lift_map
- \+ *lemma* σ_comp
- \+ *lemma* sub_def
- \+ *lemma* add_def
- \+ *lemma* neg_def
- \+ *lemma* sub_zero
- \+ *lemma* sub_self
- \+ *lemma* lift_sub_lift
- \+ *lemma* sub_sub_sub
- \+ *lemma* neg_sub
- \+ *lemma* neg_neg
- \+ *lemma* add_comm
- \+ *lemma* add_neg
- \+ *lemma* add_neg_self
- \+ *lemma* neg_add_self
- \+ *lemma* neg_sub'
- \+ *lemma* neg_add
- \+ *lemma* sub_add
- \+ *lemma* add_assoc
- \+ *lemma* add_zero
- \+ *lemma* comp_sub
- \+ *lemma* sub_comp
- \+ *lemma* comp_add
- \+ *lemma* add_comp
- \+ *def* strong_epi_of_epi
- \+ *def* is_iso_of_mono_of_epi
- \+ *def* pullback_of_mono
- \+ *def* pushout_of_epi
- \+ *def* has_limit_parallel_pair
- \+ *def* has_colimit_parallel_pair
- \+ *def* zero_kernel_of_cancel_zero
- \+ *def* zero_cokernel_of_zero_cancel
- \+ *def* epi_is_cokernel_of_kernel
- \+ *def* mono_is_kernel_of_cokernel
- \+ *def* is_colimit_σ
- \+ *def* has_sub
- \+ *def* has_neg
- \+ *def* has_add
- \+ *def* preadditive

Modified src/category_theory/discrete_category.lean
- \+ *def* nat_iso_functor

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* has_finite_biproducts.of_has_finite_products
- \+ *def* has_finite_biproducts.of_has_finite_coproducts

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* kernel_fork.ι_of_ι
- \+ *lemma* cokernel_cofork.π_of_π



## [2020-07-03 00:58:35](https://github.com/leanprover-community/mathlib/commit/9b086e1)
chore(*): reduce imports ([#3235](https://github.com/leanprover-community/mathlib/pull/3235))
The RFC pull request simply removes some `import tactic` or `import tactic.basic`, and then makes the necessary changes in later files to import things as needed.
I'm not sure if it's useful or not
#### Estimated changes
Modified archive/100-theorems-list/73_ascending_descending_sequences.lean


Modified src/algebra/big_operators.lean


Modified src/algebra/category/Group/biproducts.lean


Modified src/algebra/free.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/isomorphism.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/preadditive/biproducts.lean


Modified src/category_theory/types.lean


Modified src/control/traversable/instances.lean


Modified src/data/equiv/basic.lean


Modified src/data/equiv/local_equiv.lean


Modified src/data/int/basic.lean


Modified src/data/int/modeq.lean


Modified src/data/list/forall2.lean


Modified src/data/list/func.lean


Modified src/data/list/pairwise.lean


Modified src/data/option/basic.lean


Modified src/data/polynomial.lean


Modified src/data/set/basic.lean


Modified src/data/set/intervals/basic.lean


Modified src/data/vector2.lean


Modified src/field_theory/finite.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/logic/relation.lean


Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/primorial.lean


Modified src/order/rel_classes.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/matrix_algebra.lean


Modified src/ring_theory/tensor_product.lean


Modified src/tactic/ring_exp.lean


Modified test/library_search/basic.lean


Modified test/library_search/ordered_ring.lean


Modified test/library_search/ring_theory.lean




## [2020-07-03 00:22:34](https://github.com/leanprover-community/mathlib/commit/6a49975)
feat(category_theory/limits): fully faithful functors reflect limits and colimits ([#3269](https://github.com/leanprover-community/mathlib/pull/3269))
A fully faithful functor reflects limits and colimits
#### Estimated changes
Modified src/category_theory/limits/preserves.lean
- \+ *def* fully_faithful_reflects_limits
- \+ *def* fully_faithful_reflects_colimits



## [2020-07-02 20:45:17](https://github.com/leanprover-community/mathlib/commit/838dc66)
feat(topology/basic): add `eventually_eventually_nhds` ([#3266](https://github.com/leanprover-community/mathlib/pull/3266))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+/\- *lemma* inf_principal_ne_bot_iff
- \+ *lemma* join_mono
- \+ *lemma* eventually_le.congr
- \+ *lemma* eventually_le_congr
- \+ *lemma* eventually_eq.le
- \+ *lemma* eventually_le.refl
- \+ *lemma* eventually_le.trans
- \+ *lemma* eventually_eq.trans_le
- \+ *lemma* eventually_le.trans_eq
- \+ *lemma* eventually_le.antisymm
- \+ *lemma* join_le
- \+ *lemma* eventually_bind
- \+ *lemma* eventually_eq_bind
- \+ *lemma* eventually_le_bind
- \+ *lemma* mem_bind_sets'
- \+ *lemma* bind_le
- \+/\- *lemma* bind_mono
- \+ *lemma* bind_inf_principal
- \+ *lemma* sup_bind
- \- *lemma* bind_sup
- \- *lemma* bind_mono2
- \+ *def* eventually_le

Modified src/order/filter/germ.lean
- \- *lemma* eventually_le.congr
- \- *lemma* eventually_le_congr
- \- *lemma* eventually_eq.le
- \- *lemma* eventually_le.refl
- \- *lemma* eventually_le.trans
- \- *lemma* eventually_eq.trans_le
- \- *lemma* eventually_le.trans_eq
- \- *lemma* eventually_le.antisymm
- \- *def* eventually_le

Modified src/topology/basic.lean
- \+ *lemma* eventually_nhds_iff
- \+ *lemma* filter.eventually.eventually_nhds
- \+ *lemma* eventually_eventually_nhds
- \+ *lemma* nhds_bind_nhds
- \+ *lemma* eventually_eventually_eq_nhds
- \+ *lemma* eventually_eventually_le_nhds
- \+ *lemma* filter.eventually_eq.eventually_eq_nhds
- \+ *lemma* filter.eventually_le.eventually_le_nhds
- \+ *lemma* cluster_pt_principal_iff

Modified src/topology/continuous_on.lean
- \+ *lemma* nhds_bind_nhds_within
- \+ *lemma* eventually_nhds_nhds_within
- \+ *lemma* eventually_nhds_within_iff
- \+ *lemma* eventually_nhds_within_nhds_within



## [2020-07-02 19:38:26](https://github.com/leanprover-community/mathlib/commit/d84c48c)
feat(data/real/cardinality): cardinalities of intervals of reals ([#3252](https://github.com/leanprover-community/mathlib/pull/3252))
Use the existing result `mk_real` to deduce corresponding results for
all eight kinds of intervals of reals.
It's convenient for this result to add a new lemma to
`data.set.intervals.image_preimage` about the image of an interval
under `inv`.  Just as there are only a few results there about images
of intervals under multiplication rather than a full set, so I just
added the result I needed rather than all the possible variants.  (I
think there are something like 36 reasonable variants of that lemma
that could be stated, for (image or preimage - the same thing in this
case, but still separate statements) x (interval in positive or
negative reals) x (end closer to 0 is 0 (open), nonzero (open) or
nonzero (closed)) x (other end is open, closed or infinite).)
#### Estimated changes
Modified src/data/real/cardinality.lean
- \+ *lemma* mk_univ_real
- \+ *lemma* mk_Ioi_real
- \+ *lemma* mk_Ici_real
- \+ *lemma* mk_Iio_real
- \+ *lemma* mk_Iic_real
- \+ *lemma* mk_Ioo_real
- \+ *lemma* mk_Ico_real
- \+ *lemma* mk_Icc_real
- \+ *lemma* mk_Ioc_real

Modified src/data/set/intervals/image_preimage.lean
- \+ *lemma* image_inv_Ioo_0_left

Modified src/set_theory/cardinal.lean
- \+ *lemma* mk_union_le



## [2020-07-02 18:55:47](https://github.com/leanprover-community/mathlib/commit/e4fdc75)
refactor(analysis/calculus/*deriv): use eventually_eq in congruence statements ([#3261](https://github.com/leanprover-community/mathlib/pull/3261))
Use `eventually_eq` instead of `mem_sets` for congruence lemmas in continuity and differentiability statements.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_at_filter.congr_of_eventually_eq
- \+ *lemma* has_deriv_within_at.congr_of_eventually_eq
- \+ *lemma* has_deriv_at.congr_of_eventually_eq
- \+ *lemma* filter.eventually_eq.deriv_within_eq
- \+ *lemma* filter.eventually_eq.deriv_eq
- \- *lemma* has_deriv_at_filter.congr_of_mem_sets
- \- *lemma* has_deriv_within_at.congr_of_mem_nhds_within
- \- *lemma* has_deriv_at.congr_of_mem_nhds
- \- *lemma* deriv_within_congr_of_mem_nhds_within
- \- *lemma* deriv_congr_of_mem_nhds
- \+ *theorem* filter.eventually_eq.has_deriv_at_filter_iff
- \- *theorem* has_deriv_at_filter_congr_of_mem_sets

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at_filter.congr_of_eventually_eq
- \+ *lemma* has_fderiv_within_at.congr_of_eventually_eq
- \+ *lemma* has_fderiv_at.congr_of_eventually_eq
- \+ *lemma* differentiable_within_at.congr_of_eventually_eq
- \+ *lemma* differentiable_at.congr_of_eventually_eq
- \+ *lemma* filter.eventually_eq.fderiv_within_eq
- \+ *lemma* filter.eventually_eq.fderiv_eq
- \+ *lemma* differentiable_within_at.comp'
- \- *lemma* has_fderiv_at_filter.congr_of_mem_sets
- \- *lemma* has_fderiv_within_at.congr_of_mem_nhds_within
- \- *lemma* has_fderiv_at.congr_of_mem_nhds
- \- *lemma* differentiable_within_at.congr_of_mem_nhds_within
- \- *lemma* differentiable_at.congr_of_mem_nhds
- \- *lemma* fderiv_within_congr_of_mem_nhds_within
- \- *lemma* fderiv_congr_of_mem_nhds
- \+ *theorem* filter.eventually_eq.has_strict_fderiv_at_iff
- \+ *theorem* has_strict_fderiv_at.congr_of_eventually_eq
- \+ *theorem* filter.eventually_eq.has_fderiv_at_filter_iff
- \- *theorem* has_strict_fderiv_at_congr_of_mem_sets
- \- *theorem* has_strict_fderiv_at.congr_of_mem_sets
- \- *theorem* has_fderiv_at_filter_congr_of_mem_sets

Modified src/analysis/calculus/inverse.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/special_functions/pow.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/mfderiv.lean
- \+ *lemma* has_mfderiv_within_at.congr_of_eventually_eq
- \+ *lemma* has_mfderiv_at.congr_of_eventually_eq
- \+ *lemma* mdifferentiable_within_at.congr_of_eventually_eq
- \+ *lemma* filter.eventually_eq.mdifferentiable_within_at_iff
- \+ *lemma* mdifferentiable_at.congr_of_eventually_eq
- \+ *lemma* filter.eventually_eq.mfderiv_within_eq
- \+ *lemma* filter.eventually_eq.mfderiv_eq
- \- *lemma* has_mfderiv_within_at.congr_of_mem_nhds_within
- \- *lemma* has_mfderiv_at.congr_of_mem_nhds
- \- *lemma* mdifferentiable_within_at.congr_of_mem_nhds_within
- \- *lemma* mdifferentiable_within_at_congr_of_mem_nhds_within
- \- *lemma* mdifferentiable_at.congr_of_mem_nhds
- \- *lemma* mfderiv_within_congr_of_mem_nhds_within
- \- *lemma* mfderiv_congr_of_mem_nhds

Modified src/order/filter/basic.lean
- \+ *lemma* eventually.exists_mem
- \+ *lemma* eventually_iff_exists_mem
- \+ *lemma* eventually_eq.exists_mem
- \+ *lemma* eventually_eq_of_mem
- \+ *lemma* eventually_eq_iff_exists_mem

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_within_at.comp'
- \+ *lemma* continuous_on.comp'
- \+ *lemma* continuous_within_at.congr_of_eventually_eq
- \- *lemma* continuous_within_at.congr_of_mem_nhds_within



## [2020-07-02 18:14:59](https://github.com/leanprover-community/mathlib/commit/237b1ea)
feat(analysis/specific_limits): proof of harmonic series diverging and preliminaries ([#3233](https://github.com/leanprover-community/mathlib/pull/3233))
This PR is made of two parts : 
- A few new generic lemmas, mostly by @PatrickMassot , in `order/filter/at_top_bot.lean` and `topology/algebra/ordered.lean`
- Definition of the harmonic series, basic lemmas about it, and proof of its divergence, in `analysis/specific_limits.lean`
Zulip : https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Harmonic.20Series.20Divergence/near/201651652
#### Estimated changes
Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/specific_limits.lean
- \+ *lemma* mono_harmonic
- \+ *lemma* half_le_harmonic_double_sub_harmonic
- \+ *lemma* self_div_two_le_harmonic_two_pow
- \+ *theorem* harmonic_tendsto_at_top
- \+ *def* harmonic_series

Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* tendsto_at_top_mono
- \+/\- *lemma* tendsto_at_top_at_top_of_monotone
- \+ *lemma* tendsto_at_top_at_top_iff_of_monotone
- \+/\- *lemma* monotone.tendsto_at_top_finset
- \+/\- *lemma* tendsto_finset_image_at_top_at_top
- \+/\- *lemma* prod_at_top_at_top_eq
- \+/\- *lemma* prod_map_at_top_eq
- \+ *lemma* tendsto_at_top_at_top_of_monotone'
- \+ *lemma* unbounded_of_tendsto_at_top
- \+ *lemma* tendsto_at_top_of_monotone_of_filter
- \+ *lemma* tendsto_at_top_of_monotone_of_subseq

Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter_eq_bot_of_not_nonempty
- \+ *lemma* tendsto_bot
- \+ *lemma* tendsto_of_not_nonempty
- \+/\- *lemma* tendsto_congr'

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_at_top_csupr
- \+ *lemma* tendsto_at_top_supr
- \+ *lemma* tendsto_of_monotone



## [2020-07-02 13:05:20](https://github.com/leanprover-community/mathlib/commit/8be66ee)
fix(library_search): fix a bug with iff lemmas where both sides match ([#3270](https://github.com/leanprover-community/mathlib/pull/3270))
Also add a proper failure message for `library_search`, using Mario's text.
#### Estimated changes
Modified src/tactic/suggest.lean


Modified test/library_search/basic.lean


Created test/library_search/exp_le_exp.lean




## [2020-07-02 13:05:18](https://github.com/leanprover-community/mathlib/commit/18a80ea)
chore(tactic/noncomm_ring): allow simp to fail ([#3268](https://github.com/leanprover-community/mathlib/pull/3268))
Fixes [#3267](https://github.com/leanprover-community/mathlib/pull/3267).
#### Estimated changes
Modified src/tactic/noncomm_ring.lean


Modified test/noncomm_ring.lean




## [2020-07-02 10:27:52](https://github.com/leanprover-community/mathlib/commit/dc1d936)
feat(data/polynomial): preliminaries for Cayley-Hamilton ([#3243](https://github.com/leanprover-community/mathlib/pull/3243))
Many cheerful facts about polynomials!
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* sum_range_sub'
- \+ *lemma* prod_range_div'

Modified src/data/polynomial.lean
- \+ *lemma* monomial_zero_right
- \+ *lemma* monomial_add
- \+ *lemma* mul_coeff_zero
- \+ *lemma* monomial_zero_left
- \+ *lemma* sum_monomial_eq
- \+ *lemma* sum_C_index
- \+ *lemma* coeff_mul_C
- \+/\- *lemma* eval₂_sum
- \+ *lemma* eval_monomial
- \+ *lemma* coeff_nat_degree_succ_eq_zero
- \+ *lemma* sum_over_range'
- \+ *lemma* sum_over_range
- \+ *lemma* map_monomial
- \+ *lemma* eval₂_eq_eval_map
- \+ *lemma* nat_degree_mul_le
- \+ *lemma* coeff_mul_X_sub_C
- \+ *lemma* nat_degree_X_sub_C
- \+ *lemma* nat_degree_X_pow_sub_C
- \+ *lemma* eq_zero_of_eq_zero
- \+ *lemma* nat_degree_X_sub_C_le
- \+ *lemma* eval_mul_X_sub_C
- \- *lemma* C_def
- \+/\- *theorem* coeff_mul_X
- \+ *theorem* coeff_mul_monomial
- \+ *theorem* coeff_monomial_mul
- \+ *theorem* coeff_mul_monomial_zero
- \+ *theorem* coeff_monomial_zero_mul



## [2020-07-02 00:35:42](https://github.com/leanprover-community/mathlib/commit/cd29ede)
chore(scripts): update nolints.txt ([#3265](https://github.com/leanprover-community/mathlib/pull/3265))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-01 23:16:08](https://github.com/leanprover-community/mathlib/commit/9309910)
chore(algebra/*): deduplicate `*_with_zero`/`semiring`/`field` ([#3259](https://github.com/leanprover-community/mathlib/pull/3259))
All moved/renamed/merged lemmas were generalized to use
`*_with_zero`/`nonzero`/`mul_zero_class` instead of
`(semi)ring`/`division_ring`/`field`.
## Moved to `group_with_zero`
The following lemmas were formulated for
`(semi_)ring`s/`division_ring`s/`field`s. Some of them had strictly
more general “prime” versions for `*_with_zero`. I either moved a
lemma to `algebra/group_with_zero` and adjusted the requirements or
removed the non-prime version and `'` from the name of the prime
version. Sometimes I also made some arguments implicit.
TL;DR: moved to `group_with_zero`, removed `name'` lemma if it was there.
* `is_unit_zero_iff`;
* `not_is_unit_zero`;
* `div_eq_one_iff_eq`;
* `eq_div_iff_mul_eq`;
* `eq_div_of_mul_eq`;
* `eq_one_div_of_mul_eq_one`;
* `eq_one_div_of_mul_eq_one_left`;
* `one_div_one_div`;
* `eq_of_one_div_eq_one_div`;
* `one_div_div`;
* `mul_eq_of_eq_div`;
* `mul_mul_div`;
* `eq_zero_of_zero_eq_one`;
* `eq_inv_of_mul_right_eq_one`;
* `eq_inv_of_mul_left_eq_one`;
* `div_right_comm`;
* `div_div_div_cancel_right`;
* `div_mul_div_cancel`;
## Renamed/merged
* rename `mul_inv''` to `mul_inv'` and merge `mul_inv'` into `mul_inv_rev'`;
* `coe_unit_mul_inv`, `coe_unit_inv_mul`: `units.mul_inv'`, `units.inv_mul'`
* `division_ring.inv_eq_iff`: `inv_eq_iff`;
* `division_ring.inv_inj`: `inv_inj'`;
* `domain.mul_left_inj`: `mul_left_inj'`;
* `domain.mul_right_inj`: `mul_right_inj'`;
* `eq_of_mul_eq_mul_of_nonzero_left` and `eq_of_mul_eq_mul_left`: `mul_left_cancel'`;
* `eq_of_mul_eq_mul_of_nonzero_right` and `eq_of_mul_eq_mul_right`: `mul_right_cancel'`;
* `inv_inj`, `inv_inj'`, `inv_inj''`: `inv_injective`, `inv_inj`, and `inv_inj'`, respectively;
* `mul_inv_cancel_assoc_left`, `mul_inv_cancel_assoc_right`,
  `inv_mul_cancel_assoc_left`, `inv_mul_cancel_assoc_right`:
  `mul_inv_cancel_left'`, `mul_inv_cacnel_right'`,
  `inv_mul_cancel_left'`, `inv_mul_cancel_right'`;
* `ne_zero_and_ne_zero_of_mul_ne_zero` : `ne_zero_and_ne_zero_of_mul`.
* `ne_zero_of_mul_left_eq_one`: `left_ne_zero_of_mul_eq_one`
* `ne_zero_of_mul_ne_zero_left` : `right_ne_zero_of_mul`;
* `ne_zero_of_mul_ne_zero_right` : `left_ne_zero_of_mul`;
* `ne_zero_of_mul_right_eq_one`: `left_ne_zero_of_mul_eq_one`
* `neg_inj` and `neg_inj` renamed to `neg_injective` and `neg_inj`;
* `one_inv_eq`: merged into `inv_one`;
* `unit_ne_zero`: `units.ne_zero`;
* `units.mul_inv'` and `units.inv_mul'`: `units.mul_inv_of_eq` and `units.inv_mul_of_eq`;
* `units.mul_left_eq_zero_iff_eq_zero`,
  `units.mul_right_eq_zero_iff_eq_zero`: `units.mul_left_eq_zero`,
  `units.mul_right_eq_zero`;
## New
* `class cancel_monoid_with_zero`: a `monoid_with_zero` such that
  left/right multiplication by a non-zero element is injective; the
  main instances are `group_with_zero`s and `domain`s;
* `monoid_hom.map_ne_zero`, `monoid_hom.map_eq_zero`,
  `monoid_hom.map_inv'`, `monoid_hom.map_div`, `monoid_hom.injective`:
  lemmas about monoid homomorphisms of two groups with zeros such that
  `f 0 = 0`;
* `mul_eq_zero_of_left`, `mul_eq_zero_of_right`, `ne_zero_of_eq_one`
* `unique_of_zero_eq_one`, `eq_of_zero_eq_one`, `nonzero_psum_unique`,
  `zero_ne_one_or_forall_eq_0`;
* `mul_left_inj'`, `mul_right_inj'`
## Misc changes
* `eq_of_div_eq_one` no more requires `b ≠ 0`;
#### Estimated changes
Modified src/algebra/associated.lean
- \- *theorem* is_unit_zero_iff
- \- *theorem* not_is_unit_zero

Modified src/algebra/euclidean_domain.lean


Modified src/algebra/field.lean
- \+/\- *lemma* map_ne_zero
- \+/\- *lemma* map_eq_zero
- \+/\- *lemma* map_inv
- \+/\- *lemma* map_div
- \- *lemma* eq_one_div_of_mul_eq_one
- \- *lemma* eq_one_div_of_mul_eq_one_left
- \- *lemma* one_div_one_div
- \- *lemma* eq_of_one_div_eq_one_div
- \- *lemma* mul_inv'
- \- *lemma* one_div_div
- \- *lemma* division_ring.inv_inj
- \- *lemma* division_ring.inv_eq_iff
- \- *lemma* div_eq_one_iff_eq
- \- *lemma* eq_of_div_eq_one
- \- *lemma* eq_div_iff_mul_eq
- \- *lemma* eq_div_of_mul_eq
- \- *lemma* mul_eq_of_eq_div
- \- *lemma* mul_mul_div
- \- *lemma* injective

Modified src/algebra/gcd_domain.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/group/basic.lean
- \+/\- *lemma* inv_involutive
- \+ *lemma* inv_injective
- \- *lemma* inv_inj
- \+ *theorem* inv_inj
- \- *theorem* inv_inj'
- \- *theorem* eq_of_inv_eq_inv

Modified src/algebra/group/units.lean
- \+ *lemma* inv_mul_of_eq
- \+ *lemma* mul_inv_of_eq
- \- *lemma* inv_mul'
- \- *lemma* mul_inv'

Modified src/algebra/group_ring_action.lean


Modified src/algebra/group_with_zero.lean
- \+/\- *lemma* zero_mul
- \+/\- *lemma* mul_zero
- \+ *lemma* mul_eq_zero_of_left
- \+ *lemma* mul_eq_zero_of_right
- \+ *lemma* left_ne_zero_of_mul
- \+ *lemma* right_ne_zero_of_mul
- \+ *lemma* ne_zero_and_ne_zero_of_mul
- \+/\- *lemma* zero_ne_one
- \+/\- *lemma* one_ne_zero
- \+ *lemma* ne_zero_of_eq_one
- \+ *lemma* left_ne_zero_of_mul_eq_one
- \+ *lemma* right_ne_zero_of_mul_eq_one
- \+/\- *lemma* eq_zero_of_mul_self_eq_zero
- \+ *lemma* ne_zero
- \+ *lemma* mul_left_eq_zero
- \+ *lemma* mul_right_eq_zero
- \+ *lemma* eq_zero_of_zero_eq_one
- \+ *lemma* eq_of_zero_eq_one
- \+ *lemma* zero_ne_one_or_forall_eq_0
- \+/\- *lemma* mul_left_cancel'
- \+/\- *lemma* mul_right_cancel'
- \+/\- *lemma* mul_left_inj'
- \+ *lemma* mul_right_inj'
- \+/\- *lemma* div_eq_mul_inv
- \+ *lemma* mul_inv_cancel_left'
- \+ *lemma* mul_inv_cancel_right'
- \+ *lemma* inv_mul_cancel_left'
- \+ *lemma* inv_mul_cancel_right'
- \+/\- *lemma* inv_one
- \+ *lemma* eq_inv_of_mul_right_eq_one
- \+ *lemma* eq_inv_of_mul_left_eq_one
- \+ *lemma* inv_inj'
- \+ *lemma* coe_inv'
- \+ *lemma* mul_inv'
- \+ *lemma* inv_mul'
- \+/\- *lemma* exists_iff_ne_zero
- \+ *lemma* eq_one_div_of_mul_eq_one
- \+ *lemma* eq_one_div_of_mul_eq_one_left
- \+ *lemma* one_div_div
- \+ *lemma* one_div_one_div
- \+ *lemma* eq_of_one_div_eq_one_div
- \+/\- *lemma* div_eq_zero_iff
- \+ *lemma* eq_div_iff_mul_eq
- \+ *lemma* div_eq_of_eq_mul
- \+ *lemma* eq_div_of_mul_eq
- \+ *lemma* eq_of_div_eq_one
- \+ *lemma* div_eq_one_iff_eq
- \+ *lemma* mul_mul_div
- \+ *lemma* div_right_comm
- \+ *lemma* div_div_div_cancel_right
- \+ *lemma* div_mul_div_cancel
- \+ *lemma* map_ne_zero
- \+ *lemma* map_eq_zero
- \+ *lemma* map_inv'
- \+ *lemma* map_div
- \- *lemma* mul_inv_cancel_assoc_left
- \- *lemma* mul_inv_cancel_assoc_right
- \- *lemma* inv_mul_cancel_assoc_left
- \- *lemma* inv_mul_cancel_assoc_right
- \- *lemma* one_inv_eq
- \- *lemma* ne_zero_of_mul_right_eq_one'
- \- *lemma* ne_zero_of_mul_left_eq_one'
- \- *lemma* eq_inv_of_mul_right_eq_one'
- \- *lemma* eq_inv_of_mul_left_eq_one'
- \- *lemma* inv_inj''
- \- *lemma* coe_unit_mul_inv'
- \- *lemma* coe_unit_inv_mul'
- \- *lemma* unit_ne_zero
- \- *lemma* mul_inv_eq_of_eq_mul'
- \- *lemma* eq_mul_inv_of_mul_eq'
- \- *lemma* eq_one_div_of_mul_eq_one'
- \- *lemma* eq_one_div_of_mul_eq_one_left'
- \- *lemma* one_div_div'
- \- *lemma* one_div_one_div'
- \- *lemma* eq_of_one_div_eq_one_div'
- \- *lemma* mul_inv''
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_left
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_right
- \- *lemma* div_right_comm'
- \- *lemma* div_div_div_cancel_right'
- \- *lemma* div_mul_div_cancel'
- \+ *theorem* subsingleton_of_zero_eq_one
- \+ *theorem* is_unit_zero_iff
- \+ *theorem* not_is_unit_zero
- \+ *theorem* eq_zero_of_mul_eq_self_right
- \+ *theorem* eq_zero_of_mul_eq_self_left
- \- *theorem* inv_eq_inv
- \+ *def* unique_of_zero_eq_one

Modified src/algebra/group_with_zero_power.lean


Modified src/algebra/linear_ordered_comm_group_with_zero.lean
- \+ *lemma* units.zero_lt
- \- *lemma* zero_lt_unit

Modified src/algebra/ordered_field.lean


Modified src/algebra/quadratic_discriminant.lean


Modified src/algebra/ring.lean
- \+/\- *lemma* mul_self_eq_mul_self_iff
- \+/\- *lemma* mul_self_eq_one_iff
- \- *lemma* ne_zero_of_mul_ne_zero_right
- \- *lemma* ne_zero_of_mul_ne_zero_left
- \- *lemma* zero_ne_one_or_forall_eq_0
- \- *lemma* eq_zero_of_zero_eq_one
- \- *lemma* ring.mul_zero
- \- *lemma* ring.zero_mul
- \- *lemma* eq_of_mul_eq_mul_right
- \- *lemma* eq_of_mul_eq_mul_left
- \- *theorem* subsingleton_of_zero_eq_one
- \- *theorem* ne_zero_and_ne_zero_of_mul_ne_zero
- \- *theorem* domain.mul_left_inj
- \- *theorem* domain.mul_right_inj
- \- *theorem* eq_zero_of_mul_eq_self_right
- \- *theorem* eq_zero_of_mul_eq_self_left
- \- *theorem* eq_of_mul_eq_mul_right_of_ne_zero
- \- *theorem* eq_of_mul_eq_mul_left_of_ne_zero
- \- *theorem* mul_left_eq_zero_iff_eq_zero
- \- *theorem* mul_right_eq_zero_iff_eq_zero

Modified src/analysis/calculus/darboux.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/category_theory/preadditive/default.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/finsupp.lean


Modified src/data/fintype/basic.lean


Modified src/data/int/basic.lean


Modified src/data/int/gcd.lean


Modified src/data/num/lemmas.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/polynomial.lean


Modified src/data/rat/basic.lean


Modified src/data/rat/cast.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/nnreal.lean


Modified src/data/zsqrtd/basic.lean


Modified src/deprecated/subgroup.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/subfield.lean


Modified src/geometry/euclidean.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/group_theory/subgroup.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/linear_algebra/sesquilinear_form.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/prime.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/valuation/basic.lean


Modified src/tactic/cancel_denoms.lean


Modified src/tactic/norm_num.lean
- \+/\- *theorem* inv_one

Modified src/tactic/ring2.lean




## [2020-07-01 18:46:03](https://github.com/leanprover-community/mathlib/commit/1a419a9)
feat(data/nat/digits): add digits_lt_base ([#3246](https://github.com/leanprover-community/mathlib/pull/3246))
#### Estimated changes
Modified src/data/nat/digits.lean
- \+ *lemma* digits_lt_base'
- \+ *lemma* digits_lt_base



## [2020-07-01 17:12:55](https://github.com/leanprover-community/mathlib/commit/f00b7c0)
chore(*): work on removing deprecated is_X_hom typeclasses ([#3258](https://github.com/leanprover-community/mathlib/pull/3258))
It's far from over, but as I was bumping up against issues in `polynomial.lean` and `mv_polynomial.lean`, I'm going to PR this part for now, and then wait to return to it when other PRs affecting `polynomial.lean` have cleared.
#### Estimated changes
Modified src/algebra/field_power.lean
- \- *lemma* map_fpow

Modified src/algebra/pointwise.lean
- \- *lemma* pointwise_mul_image_is_semiring_hom
- \+ *def* pointwise_mul_image_ring_hom

Modified src/algebra/punit_instances.lean


Modified src/category_theory/conj.lean


Modified src/data/complex/basic.lean
- \- *lemma* conj_zero
- \- *lemma* conj_one
- \- *lemma* conj_add
- \- *lemma* conj_neg
- \- *lemma* conj_mul
- \- *lemma* conj_sub
- \- *lemma* conj_pow
- \- *lemma* conj_inv
- \- *lemma* conj_div
- \+/\- *def* conj

Modified src/data/complex/exponential.lean


Modified src/data/complex/module.lean


Modified src/data/equiv/ring.lean


Modified src/data/finsupp.lean
- \+ *def* map_range.add_monoid_hom

Modified src/data/padics/padic_integers.lean
- \+ *def* coe.ring_hom

Modified src/data/padics/padic_norm.lean


Modified src/data/pnat/factors.lean


Modified src/data/polynomial.lean


Modified src/data/zsqrtd/gaussian_int.lean
- \+/\- *lemma* to_complex_add
- \+/\- *lemma* to_complex_mul
- \+/\- *lemma* to_complex_one
- \+/\- *lemma* to_complex_zero
- \+/\- *lemma* to_complex_neg
- \+/\- *lemma* to_complex_sub
- \+/\- *def* to_complex

Deleted src/deprecated/field.lean
- \- *lemma* map_ne_zero
- \- *lemma* map_eq_zero
- \- *lemma* map_inv
- \- *lemma* map_div
- \- *lemma* injective

Modified src/field_theory/minimal_polynomial.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean
- \- *lemma* of_subtype_one
- \+/\- *def* of_subtype

Modified src/ring_theory/algebra_operations.lean
- \+ *def* span.ring_hom

Modified src/ring_theory/power_series.lean
- \+ *def* coe_to_mv_power_series.ring_hom
- \+ *def* coe_to_power_series.ring_hom

Modified src/ring_theory/subring.lean




## [2020-07-01 12:12:44](https://github.com/leanprover-community/mathlib/commit/e803c85)
feat(field_theory/separable): relating irreducibility and separability ([#3198](https://github.com/leanprover-community/mathlib/pull/3198))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* eval₂_nat_cast
- \+ *theorem* map_nat_cast
- \+ *theorem* nat_degree_le_of_dvd
- \+ *theorem* is_unit_iff
- \+ *theorem* derivative_pow_succ
- \+ *theorem* derivative_pow
- \+ *theorem* derivative_map
- \+ *theorem* derivative_eval₂_C
- \+ *theorem* of_mem_support_derivative
- \+ *theorem* degree_derivative_lt
- \+ *theorem* nat_degree_derivative_lt
- \+ *theorem* degree_derivative_le

Modified src/field_theory/separable.lean
- \+ *lemma* separable_C
- \+ *lemma* separable.is_coprime
- \+ *lemma* coe_expand
- \+ *lemma* expand_C
- \+ *lemma* expand_X
- \+ *lemma* expand_monomial
- \+ *theorem* separable.of_pow'
- \+ *theorem* separable.of_pow
- \+ *theorem* separable.map
- \+ *theorem* expand_expand
- \+ *theorem* expand_mul
- \+ *theorem* expand_one
- \+ *theorem* expand_pow
- \+ *theorem* derivative_expand
- \+ *theorem* coeff_expand
- \+ *theorem* coeff_expand_mul
- \+ *theorem* coeff_expand_mul'
- \+ *theorem* expand_eq_map_domain
- \+ *theorem* expand_inj
- \+ *theorem* expand_eq_zero
- \+ *theorem* expand_eq_C
- \+ *theorem* nat_degree_expand
- \+ *theorem* is_local_ring_hom_expand
- \+ *theorem* separable_iff_derivative_ne_zero
- \+ *theorem* coeff_contract
- \+ *theorem* of_irreducible_expand
- \+ *theorem* of_irreducible_expand_pow
- \+ *theorem* expand_contract
- \+ *theorem* separable_or
- \+ *theorem* exists_separable_of_irreducible
- \+ *theorem* is_unit_or_eq_zero_of_separable_expand
- \+ *theorem* unique_separable_of_irreducible
- \+ *theorem* irreducible.separable

Modified src/ring_theory/algebra.lean
- \+ *lemma* map_nat_cast

Modified src/ring_theory/ideals.lean
- \+ *theorem* of_irreducible_map

Modified src/ring_theory/polynomial/basic.lean




## [2020-07-01 10:05:14](https://github.com/leanprover-community/mathlib/commit/a7cdab5)
chore(data/set/basic): simp attribute on mem_range_self ([#3260](https://github.com/leanprover-community/mathlib/pull/3260))
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *theorem* mem_range_self



## [2020-07-01 10:05:12](https://github.com/leanprover-community/mathlib/commit/7bd19b3)
chore(data/finset, data/multiset): split into smaller files ([#3256](https://github.com/leanprover-community/mathlib/pull/3256))
This follows on from [#2341](https://github.com/leanprover-community/mathlib/pull/2341), which split the second half of `data.list.basic` into separate files. This now does the same (trying to follow a similar split) for `data.multiset` and `data.finset`.
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/algebra/big_operators.lean


Modified src/control/equiv_functor/instances.lean


Modified src/data/finmap.lean


Renamed src/data/finset.lean to src/data/finset/basic.lean
- \- *lemma* pi_val
- \- *lemma* mem_pi
- \- *lemma* pi.cons_same
- \- *lemma* pi.cons_ne
- \- *lemma* pi_cons_injective
- \- *lemma* pi_empty
- \- *lemma* pi_insert
- \- *lemma* pi_subset
- \- *lemma* powerset_empty
- \- *lemma* not_mem_of_mem_powerset_of_not_mem
- \- *lemma* powerset_insert
- \- *lemma* fold_op_rel_iff_and
- \- *lemma* fold_op_rel_iff_or
- \- *lemma* le_fold_min
- \- *lemma* fold_min_le
- \- *lemma* lt_fold_min
- \- *lemma* fold_min_lt
- \- *lemma* fold_max_le
- \- *lemma* le_fold_max
- \- *lemma* fold_max_lt
- \- *lemma* lt_fold_max
- \- *lemma* sup_def
- \- *lemma* sup_empty
- \- *lemma* sup_insert
- \- *lemma* sup_singleton
- \- *lemma* sup_union
- \- *lemma* sup_le_iff
- \- *lemma* sup_le
- \- *lemma* le_sup
- \- *lemma* sup_mono_fun
- \- *lemma* sup_mono
- \- *lemma* sup_lt_iff
- \- *lemma* comp_sup_eq_sup_comp
- \- *lemma* comp_sup_eq_sup_comp_of_is_total
- \- *lemma* sup_eq_supr
- \- *lemma* inf_val
- \- *lemma* inf_empty
- \- *lemma* le_inf_iff
- \- *lemma* inf_insert
- \- *lemma* inf_singleton
- \- *lemma* inf_union
- \- *lemma* inf_le
- \- *lemma* le_inf
- \- *lemma* inf_mono_fun
- \- *lemma* inf_mono
- \- *lemma* lt_inf_iff
- \- *lemma* comp_inf_eq_inf_comp
- \- *lemma* comp_inf_eq_inf_comp_of_is_total
- \- *lemma* inf_eq_infi
- \- *lemma* min'_lt_max'_of_card
- \- *lemma* exists_max_image
- \- *lemma* exists_min_image
- \- *lemma* sorted_zero_eq_min'
- \- *lemma* sorted_last_eq_max'
- \- *lemma* mono_of_fin_strict_mono
- \- *lemma* mono_of_fin_bij_on
- \- *lemma* mono_of_fin_injective
- \- *lemma* mono_of_fin_zero
- \- *lemma* mono_of_fin_last
- \- *lemma* mono_of_fin_unique
- \- *lemma* mono_of_fin_eq_mono_of_fin_iff
- \- *lemma* pi_disjoint_of_disjoint
- \- *lemma* union_consecutive
- \- *lemma* inter_consecutive
- \- *lemma* disjoint_consecutive
- \- *lemma* filter_lt_of_top_le
- \- *lemma* filter_lt_of_le_bot
- \- *lemma* filter_lt_of_ge
- \- *lemma* filter_lt
- \- *lemma* filter_le_of_le_bot
- \- *lemma* filter_le_of_top_le
- \- *lemma* filter_le_of_le
- \- *lemma* filter_le
- \- *lemma* diff_left
- \- *lemma* diff_right
- \- *lemma* image_const_sub
- \- *lemma* range_eq_Ico
- \- *lemma* range_image_pred_top_sub
- \- *lemma* Ico_ℤ.mem
- \- *lemma* Ico_ℤ.card
- \- *lemma* count_sup
- \- *lemma* supr_eq_supr_finset
- \- *lemma* infi_eq_infi_finset
- \- *lemma* Union_eq_Union_finset
- \- *lemma* Inter_eq_Inter_finset
- \- *lemma* mem_antidiagonal
- \- *lemma* card_antidiagonal
- \- *lemma* antidiagonal_zero
- \- *lemma* supr_coe
- \- *lemma* infi_coe
- \- *lemma* supr_insert
- \- *lemma* infi_insert
- \- *lemma* supr_finset_image
- \- *lemma* infi_finset_image
- \- *lemma* bUnion_union
- \- *lemma* bInter_inter
- \- *lemma* bUnion_insert
- \- *lemma* bInter_insert
- \- *lemma* bUnion_finset_image
- \- *lemma* bInter_finset_image
- \- *theorem* mem_powerset
- \- *theorem* empty_mem_powerset
- \- *theorem* mem_powerset_self
- \- *theorem* powerset_mono
- \- *theorem* card_powerset
- \- *theorem* mem_powerset_len
- \- *theorem* powerset_len_mono
- \- *theorem* card_powerset_len
- \- *theorem* fold_empty
- \- *theorem* fold_insert
- \- *theorem* fold_singleton
- \- *theorem* fold_map
- \- *theorem* fold_image
- \- *theorem* fold_congr
- \- *theorem* fold_op_distrib
- \- *theorem* fold_hom
- \- *theorem* fold_union_inter
- \- *theorem* fold_insert_idem
- \- *theorem* sup_congr
- \- *theorem* subset_range_sup_succ
- \- *theorem* exists_nat_subset_range
- \- *theorem* inf_congr
- \- *theorem* max_eq_sup_with_bot
- \- *theorem* max_empty
- \- *theorem* max_insert
- \- *theorem* max_singleton
- \- *theorem* max_of_mem
- \- *theorem* max_of_nonempty
- \- *theorem* max_eq_none
- \- *theorem* mem_of_max
- \- *theorem* le_max_of_mem
- \- *theorem* min_eq_inf_with_top
- \- *theorem* min_empty
- \- *theorem* min_insert
- \- *theorem* min_singleton
- \- *theorem* min_of_mem
- \- *theorem* min_of_nonempty
- \- *theorem* min_eq_none
- \- *theorem* mem_of_min
- \- *theorem* min_le_of_mem
- \- *theorem* min'_mem
- \- *theorem* min'_le
- \- *theorem* le_min'
- \- *theorem* max'_mem
- \- *theorem* le_max'
- \- *theorem* max'_le
- \- *theorem* min'_lt_max'
- \- *theorem* sort_sorted
- \- *theorem* sort_eq
- \- *theorem* sort_nodup
- \- *theorem* sort_to_finset
- \- *theorem* mem_sort
- \- *theorem* length_sort
- \- *theorem* sort_sorted_lt
- \- *theorem* val
- \- *theorem* to_finset
- \- *theorem* image_add
- \- *theorem* image_sub
- \- *theorem* zero_bot
- \- *theorem* card
- \- *theorem* mem
- \- *theorem* eq_empty_of_le
- \- *theorem* self_eq_empty
- \- *theorem* eq_empty_iff
- \- *theorem* subset_iff
- \- *theorem* succ_singleton
- \- *theorem* succ_top
- \- *theorem* succ_top'
- \- *theorem* insert_succ_bot
- \- *theorem* pred_singleton
- \- *theorem* not_mem_top
- \- *theorem* supr_singleton
- \- *theorem* infi_singleton
- \- *theorem* supr_union
- \- *theorem* infi_union
- \- *theorem* bUnion_coe
- \- *theorem* bInter_coe
- \- *theorem* bUnion_singleton
- \- *theorem* bInter_singleton
- \- *def* pi
- \- *def* pi.empty
- \- *def* pi.cons
- \- *def* powerset
- \- *def* powerset_len
- \- *def* fold
- \- *def* sup
- \- *def* inf
- \- *def* min'
- \- *def* max'
- \- *def* sort
- \- *def* mono_of_fin
- \- *def* Ico
- \- *def* Ico_ℤ
- \- *def* antidiagonal

Created src/data/finset/default.lean


Created src/data/finset/fold.lean
- \+ *lemma* fold_op_rel_iff_and
- \+ *lemma* fold_op_rel_iff_or
- \+ *lemma* le_fold_min
- \+ *lemma* fold_min_le
- \+ *lemma* lt_fold_min
- \+ *lemma* fold_min_lt
- \+ *lemma* fold_max_le
- \+ *lemma* le_fold_max
- \+ *lemma* fold_max_lt
- \+ *lemma* lt_fold_max
- \+ *theorem* fold_empty
- \+ *theorem* fold_insert
- \+ *theorem* fold_singleton
- \+ *theorem* fold_map
- \+ *theorem* fold_image
- \+ *theorem* fold_congr
- \+ *theorem* fold_op_distrib
- \+ *theorem* fold_hom
- \+ *theorem* fold_union_inter
- \+ *theorem* fold_insert_idem
- \+ *def* fold

Created src/data/finset/intervals.lean
- \+ *lemma* union_consecutive
- \+ *lemma* inter_consecutive
- \+ *lemma* disjoint_consecutive
- \+ *lemma* filter_lt_of_top_le
- \+ *lemma* filter_lt_of_le_bot
- \+ *lemma* filter_lt_of_ge
- \+ *lemma* filter_lt
- \+ *lemma* filter_le_of_le_bot
- \+ *lemma* filter_le_of_top_le
- \+ *lemma* filter_le_of_le
- \+ *lemma* filter_le
- \+ *lemma* diff_left
- \+ *lemma* diff_right
- \+ *lemma* image_const_sub
- \+ *lemma* range_eq_Ico
- \+ *lemma* range_image_pred_top_sub
- \+ *lemma* Ico_ℤ.mem
- \+ *lemma* Ico_ℤ.card
- \+ *theorem* val
- \+ *theorem* to_finset
- \+ *theorem* image_add
- \+ *theorem* image_sub
- \+ *theorem* zero_bot
- \+ *theorem* card
- \+ *theorem* mem
- \+ *theorem* eq_empty_of_le
- \+ *theorem* self_eq_empty
- \+ *theorem* eq_empty_iff
- \+ *theorem* subset_iff
- \+ *theorem* succ_singleton
- \+ *theorem* succ_top
- \+ *theorem* succ_top'
- \+ *theorem* insert_succ_bot
- \+ *theorem* pred_singleton
- \+ *theorem* not_mem_top
- \+ *def* Ico
- \+ *def* Ico_ℤ

Created src/data/finset/lattice.lean
- \+ *lemma* sup_def
- \+ *lemma* sup_empty
- \+ *lemma* sup_insert
- \+ *lemma* sup_singleton
- \+ *lemma* sup_union
- \+ *lemma* sup_le_iff
- \+ *lemma* sup_le
- \+ *lemma* le_sup
- \+ *lemma* sup_mono_fun
- \+ *lemma* sup_mono
- \+ *lemma* sup_lt_iff
- \+ *lemma* comp_sup_eq_sup_comp
- \+ *lemma* comp_sup_eq_sup_comp_of_is_total
- \+ *lemma* sup_eq_supr
- \+ *lemma* inf_val
- \+ *lemma* inf_empty
- \+ *lemma* le_inf_iff
- \+ *lemma* inf_insert
- \+ *lemma* inf_singleton
- \+ *lemma* inf_union
- \+ *lemma* inf_le
- \+ *lemma* le_inf
- \+ *lemma* inf_mono_fun
- \+ *lemma* inf_mono
- \+ *lemma* lt_inf_iff
- \+ *lemma* comp_inf_eq_inf_comp
- \+ *lemma* comp_inf_eq_inf_comp_of_is_total
- \+ *lemma* inf_eq_infi
- \+ *lemma* min'_lt_max'_of_card
- \+ *lemma* exists_max_image
- \+ *lemma* exists_min_image
- \+ *lemma* count_sup
- \+ *lemma* supr_eq_supr_finset
- \+ *lemma* infi_eq_infi_finset
- \+ *lemma* Union_eq_Union_finset
- \+ *lemma* Inter_eq_Inter_finset
- \+ *lemma* supr_coe
- \+ *lemma* infi_coe
- \+ *lemma* supr_insert
- \+ *lemma* infi_insert
- \+ *lemma* supr_finset_image
- \+ *lemma* infi_finset_image
- \+ *lemma* bUnion_union
- \+ *lemma* bInter_inter
- \+ *lemma* bUnion_insert
- \+ *lemma* bInter_insert
- \+ *lemma* bUnion_finset_image
- \+ *lemma* bInter_finset_image
- \+ *theorem* sup_congr
- \+ *theorem* subset_range_sup_succ
- \+ *theorem* exists_nat_subset_range
- \+ *theorem* inf_congr
- \+ *theorem* max_eq_sup_with_bot
- \+ *theorem* max_empty
- \+ *theorem* max_insert
- \+ *theorem* max_singleton
- \+ *theorem* max_of_mem
- \+ *theorem* max_of_nonempty
- \+ *theorem* max_eq_none
- \+ *theorem* mem_of_max
- \+ *theorem* le_max_of_mem
- \+ *theorem* min_eq_inf_with_top
- \+ *theorem* min_empty
- \+ *theorem* min_insert
- \+ *theorem* min_singleton
- \+ *theorem* min_of_mem
- \+ *theorem* min_of_nonempty
- \+ *theorem* min_eq_none
- \+ *theorem* mem_of_min
- \+ *theorem* min_le_of_mem
- \+ *theorem* min'_mem
- \+ *theorem* min'_le
- \+ *theorem* le_min'
- \+ *theorem* max'_mem
- \+ *theorem* le_max'
- \+ *theorem* max'_le
- \+ *theorem* min'_lt_max'
- \+ *theorem* supr_singleton
- \+ *theorem* infi_singleton
- \+ *theorem* supr_union
- \+ *theorem* infi_union
- \+ *theorem* bUnion_coe
- \+ *theorem* bInter_coe
- \+ *theorem* bUnion_singleton
- \+ *theorem* bInter_singleton
- \+ *def* sup
- \+ *def* inf
- \+ *def* min'
- \+ *def* max'

Created src/data/finset/nat_antidiagonal.lean
- \+ *lemma* mem_antidiagonal
- \+ *lemma* card_antidiagonal
- \+ *lemma* antidiagonal_zero
- \+ *def* antidiagonal

Created src/data/finset/pi.lean
- \+ *lemma* pi_val
- \+ *lemma* mem_pi
- \+ *lemma* pi.cons_same
- \+ *lemma* pi.cons_ne
- \+ *lemma* pi_cons_injective
- \+ *lemma* pi_empty
- \+ *lemma* pi_insert
- \+ *lemma* pi_subset
- \+ *lemma* pi_disjoint_of_disjoint
- \+ *def* pi
- \+ *def* pi.empty
- \+ *def* pi.cons

Created src/data/finset/powerset.lean
- \+ *lemma* powerset_empty
- \+ *lemma* not_mem_of_mem_powerset_of_not_mem
- \+ *lemma* powerset_insert
- \+ *theorem* mem_powerset
- \+ *theorem* empty_mem_powerset
- \+ *theorem* mem_powerset_self
- \+ *theorem* powerset_mono
- \+ *theorem* card_powerset
- \+ *theorem* mem_powerset_len
- \+ *theorem* powerset_len_mono
- \+ *theorem* card_powerset_len
- \+ *def* powerset
- \+ *def* powerset_len

Created src/data/finset/sort.lean
- \+ *lemma* sorted_zero_eq_min'
- \+ *lemma* sorted_last_eq_max'
- \+ *lemma* mono_of_fin_strict_mono
- \+ *lemma* mono_of_fin_bij_on
- \+ *lemma* mono_of_fin_injective
- \+ *lemma* mono_of_fin_zero
- \+ *lemma* mono_of_fin_last
- \+ *lemma* mono_of_fin_unique
- \+ *lemma* mono_of_fin_eq_mono_of_fin_iff
- \+ *theorem* sort_sorted
- \+ *theorem* sort_eq
- \+ *theorem* sort_nodup
- \+ *theorem* sort_to_finset
- \+ *theorem* mem_sort
- \+ *theorem* length_sort
- \+ *theorem* sort_sorted_lt
- \+ *def* sort
- \+ *def* mono_of_fin

Modified src/data/finsupp.lean


Modified src/data/fintype/basic.lean


Modified src/data/list/default.lean


Renamed src/data/list/antidiagonal.lean to src/data/list/nat_antidiagonal.lean


Created src/data/multiset/antidiagonal.lean
- \+ *lemma* prod_map_add
- \+ *theorem* antidiagonal_coe
- \+ *theorem* antidiagonal_coe'
- \+ *theorem* mem_antidiagonal
- \+ *theorem* antidiagonal_map_fst
- \+ *theorem* antidiagonal_map_snd
- \+ *theorem* antidiagonal_zero
- \+ *theorem* antidiagonal_cons
- \+ *theorem* card_antidiagonal
- \+ *def* antidiagonal

Renamed src/data/multiset.lean to src/data/multiset/basic.lean
- \- *lemma* prod_map_add
- \- *lemma* pairwise_of_nodup
- \- *lemma* forall_of_pairwise
- \- *lemma* nodup_bind
- \- *lemma* map_eq_map_of_bij_of_nodup
- \- *lemma* attach_ndinsert
- \- *lemma* sup_zero
- \- *lemma* sup_cons
- \- *lemma* sup_singleton
- \- *lemma* sup_add
- \- *lemma* sup_le
- \- *lemma* le_sup
- \- *lemma* sup_mono
- \- *lemma* sup_erase_dup
- \- *lemma* sup_ndunion
- \- *lemma* sup_union
- \- *lemma* sup_ndinsert
- \- *lemma* inf_zero
- \- *lemma* inf_cons
- \- *lemma* inf_singleton
- \- *lemma* inf_add
- \- *lemma* le_inf
- \- *lemma* inf_le
- \- *lemma* inf_mono
- \- *lemma* inf_erase_dup
- \- *lemma* inf_ndunion
- \- *lemma* inf_union
- \- *lemma* inf_ndinsert
- \- *lemma* sections_zero
- \- *lemma* sections_cons
- \- *lemma* coe_sections
- \- *lemma* sections_add
- \- *lemma* mem_sections
- \- *lemma* card_sections
- \- *lemma* prod_map_sum
- \- *lemma* pi.cons_same
- \- *lemma* pi.cons_ne
- \- *lemma* pi.cons_swap
- \- *lemma* pi_zero
- \- *lemma* pi_cons
- \- *lemma* pi_cons_injective
- \- *lemma* card_pi
- \- *lemma* nodup_pi
- \- *lemma* mem_pi
- \- *lemma* fmap_def
- \- *lemma* pure_def
- \- *lemma* bind_def
- \- *lemma* lift_beta
- \- *lemma* map_comp_coe
- \- *lemma* id_traverse
- \- *lemma* comp_traverse
- \- *lemma* map_traverse
- \- *lemma* traverse_map
- \- *lemma* naturality
- \- *lemma* add_consecutive
- \- *lemma* inter_consecutive
- \- *lemma* filter_lt_of_top_le
- \- *lemma* filter_lt_of_le_bot
- \- *lemma* filter_lt_of_ge
- \- *lemma* filter_lt
- \- *lemma* filter_le_of_le_bot
- \- *lemma* filter_le_of_top_le
- \- *lemma* filter_le_of_le
- \- *lemma* filter_le
- \- *lemma* mem_antidiagonal
- \- *lemma* card_antidiagonal
- \- *lemma* antidiagonal_zero
- \- *lemma* nodup_antidiagonal
- \- *theorem* powerset_aux_eq_map_coe
- \- *theorem* mem_powerset_aux
- \- *theorem* powerset_aux_perm_powerset_aux'
- \- *theorem* powerset_aux'_nil
- \- *theorem* powerset_aux'_cons
- \- *theorem* powerset_aux'_perm
- \- *theorem* powerset_aux_perm
- \- *theorem* powerset_coe
- \- *theorem* powerset_coe'
- \- *theorem* powerset_zero
- \- *theorem* powerset_cons
- \- *theorem* mem_powerset
- \- *theorem* map_single_le_powerset
- \- *theorem* card_powerset
- \- *theorem* revzip_powerset_aux
- \- *theorem* revzip_powerset_aux'
- \- *theorem* revzip_powerset_aux_lemma
- \- *theorem* revzip_powerset_aux_perm_aux'
- \- *theorem* revzip_powerset_aux_perm
- \- *theorem* antidiagonal_coe
- \- *theorem* antidiagonal_coe'
- \- *theorem* mem_antidiagonal
- \- *theorem* antidiagonal_map_fst
- \- *theorem* antidiagonal_map_snd
- \- *theorem* antidiagonal_zero
- \- *theorem* antidiagonal_cons
- \- *theorem* card_antidiagonal
- \- *theorem* powerset_len_aux_eq_map_coe
- \- *theorem* mem_powerset_len_aux
- \- *theorem* powerset_len_aux_zero
- \- *theorem* powerset_len_aux_nil
- \- *theorem* powerset_len_aux_cons
- \- *theorem* powerset_len_aux_perm
- \- *theorem* powerset_len_coe'
- \- *theorem* powerset_len_coe
- \- *theorem* powerset_len_zero_left
- \- *theorem* powerset_len_zero_right
- \- *theorem* powerset_len_cons
- \- *theorem* mem_powerset_len
- \- *theorem* card_powerset_len
- \- *theorem* powerset_len_le_powerset
- \- *theorem* powerset_len_mono
- \- *theorem* coe_nodup
- \- *theorem* nodup_zero
- \- *theorem* nodup_cons
- \- *theorem* nodup_cons_of_nodup
- \- *theorem* nodup_singleton
- \- *theorem* nodup_of_nodup_cons
- \- *theorem* not_mem_of_nodup_cons
- \- *theorem* nodup_of_le
- \- *theorem* not_nodup_pair
- \- *theorem* nodup_iff_le
- \- *theorem* nodup_iff_count_le_one
- \- *theorem* count_eq_one_of_mem
- \- *theorem* nodup_add
- \- *theorem* disjoint_of_nodup_add
- \- *theorem* nodup_add_of_nodup
- \- *theorem* nodup_of_nodup_map
- \- *theorem* nodup_map_on
- \- *theorem* nodup_map
- \- *theorem* nodup_filter
- \- *theorem* nodup_attach
- \- *theorem* nodup_pmap
- \- *theorem* nodup_erase_eq_filter
- \- *theorem* nodup_erase_of_nodup
- \- *theorem* mem_erase_iff_of_nodup
- \- *theorem* mem_erase_of_nodup
- \- *theorem* nodup_product
- \- *theorem* nodup_sigma
- \- *theorem* nodup_filter_map
- \- *theorem* nodup_range
- \- *theorem* nodup_inter_left
- \- *theorem* nodup_inter_right
- \- *theorem* nodup_union
- \- *theorem* nodup_powerset
- \- *theorem* nodup_powerset_len
- \- *theorem* nodup_ext
- \- *theorem* le_iff_subset
- \- *theorem* range_le
- \- *theorem* mem_sub_of_nodup
- \- *theorem* coe_erase_dup
- \- *theorem* erase_dup_zero
- \- *theorem* mem_erase_dup
- \- *theorem* erase_dup_cons_of_mem
- \- *theorem* erase_dup_cons_of_not_mem
- \- *theorem* erase_dup_le
- \- *theorem* erase_dup_subset
- \- *theorem* subset_erase_dup
- \- *theorem* erase_dup_subset'
- \- *theorem* subset_erase_dup'
- \- *theorem* nodup_erase_dup
- \- *theorem* erase_dup_eq_self
- \- *theorem* erase_dup_eq_zero
- \- *theorem* erase_dup_singleton
- \- *theorem* le_erase_dup
- \- *theorem* erase_dup_ext
- \- *theorem* erase_dup_map_erase_dup_eq
- \- *theorem* coe_ndinsert
- \- *theorem* ndinsert_zero
- \- *theorem* ndinsert_of_mem
- \- *theorem* ndinsert_of_not_mem
- \- *theorem* mem_ndinsert
- \- *theorem* le_ndinsert_self
- \- *theorem* mem_ndinsert_self
- \- *theorem* mem_ndinsert_of_mem
- \- *theorem* length_ndinsert_of_mem
- \- *theorem* length_ndinsert_of_not_mem
- \- *theorem* erase_dup_cons
- \- *theorem* nodup_ndinsert
- \- *theorem* ndinsert_le
- \- *theorem* disjoint_ndinsert_left
- \- *theorem* disjoint_ndinsert_right
- \- *theorem* coe_ndunion
- \- *theorem* zero_ndunion
- \- *theorem* cons_ndunion
- \- *theorem* mem_ndunion
- \- *theorem* le_ndunion_right
- \- *theorem* subset_ndunion_right
- \- *theorem* ndunion_le_add
- \- *theorem* ndunion_le
- \- *theorem* subset_ndunion_left
- \- *theorem* le_ndunion_left
- \- *theorem* ndunion_le_union
- \- *theorem* nodup_ndunion
- \- *theorem* ndunion_eq_union
- \- *theorem* erase_dup_add
- \- *theorem* coe_ndinter
- \- *theorem* zero_ndinter
- \- *theorem* cons_ndinter_of_mem
- \- *theorem* ndinter_cons_of_not_mem
- \- *theorem* mem_ndinter
- \- *theorem* nodup_ndinter
- \- *theorem* le_ndinter
- \- *theorem* ndinter_le_left
- \- *theorem* ndinter_subset_left
- \- *theorem* ndinter_subset_right
- \- *theorem* ndinter_le_right
- \- *theorem* inter_le_ndinter
- \- *theorem* ndinter_eq_inter
- \- *theorem* ndinter_eq_zero_iff_disjoint
- \- *theorem* fold_eq_foldr
- \- *theorem* coe_fold_r
- \- *theorem* coe_fold_l
- \- *theorem* fold_eq_foldl
- \- *theorem* fold_zero
- \- *theorem* fold_cons_left
- \- *theorem* fold_cons_right
- \- *theorem* fold_cons'_right
- \- *theorem* fold_cons'_left
- \- *theorem* fold_add
- \- *theorem* fold_singleton
- \- *theorem* fold_distrib
- \- *theorem* fold_hom
- \- *theorem* fold_union_inter
- \- *theorem* fold_erase_dup_idem
- \- *theorem* le_smul_erase_dup
- \- *theorem* coe_sort
- \- *theorem* sort_sorted
- \- *theorem* sort_eq
- \- *theorem* mem_sort
- \- *theorem* length_sort
- \- *theorem* map_add
- \- *theorem* map_sub
- \- *theorem* zero_bot
- \- *theorem* card
- \- *theorem* nodup
- \- *theorem* mem
- \- *theorem* eq_zero_of_le
- \- *theorem* self_eq_zero
- \- *theorem* eq_zero_iff
- \- *theorem* succ_singleton
- \- *theorem* succ_top
- \- *theorem* eq_cons
- \- *theorem* pred_singleton
- \- *theorem* not_mem_top
- \- *def* powerset_aux
- \- *def* powerset_aux'
- \- *def* powerset
- \- *def* antidiagonal
- \- *def* powerset_len_aux
- \- *def* powerset_len
- \- *def* nodup
- \- *def* erase_dup
- \- *def* ndinsert
- \- *def* ndunion
- \- *def* ndinter
- \- *def* fold
- \- *def* sup
- \- *def* inf
- \- *def* sort
- \- *def* sections
- \- *def* pi.cons
- \- *def* pi.empty
- \- *def* pi
- \- *def* traverse
- \- *def* Ico

Created src/data/multiset/default.lean


Created src/data/multiset/erase_dup.lean
- \+ *theorem* coe_erase_dup
- \+ *theorem* erase_dup_zero
- \+ *theorem* mem_erase_dup
- \+ *theorem* erase_dup_cons_of_mem
- \+ *theorem* erase_dup_cons_of_not_mem
- \+ *theorem* erase_dup_le
- \+ *theorem* erase_dup_subset
- \+ *theorem* subset_erase_dup
- \+ *theorem* erase_dup_subset'
- \+ *theorem* subset_erase_dup'
- \+ *theorem* nodup_erase_dup
- \+ *theorem* erase_dup_eq_self
- \+ *theorem* erase_dup_eq_zero
- \+ *theorem* erase_dup_singleton
- \+ *theorem* le_erase_dup
- \+ *theorem* erase_dup_ext
- \+ *theorem* erase_dup_map_erase_dup_eq
- \+ *def* erase_dup

Created src/data/multiset/finset_ops.lean
- \+ *lemma* attach_ndinsert
- \+ *theorem* coe_ndinsert
- \+ *theorem* ndinsert_zero
- \+ *theorem* ndinsert_of_mem
- \+ *theorem* ndinsert_of_not_mem
- \+ *theorem* mem_ndinsert
- \+ *theorem* le_ndinsert_self
- \+ *theorem* mem_ndinsert_self
- \+ *theorem* mem_ndinsert_of_mem
- \+ *theorem* length_ndinsert_of_mem
- \+ *theorem* length_ndinsert_of_not_mem
- \+ *theorem* erase_dup_cons
- \+ *theorem* nodup_ndinsert
- \+ *theorem* ndinsert_le
- \+ *theorem* disjoint_ndinsert_left
- \+ *theorem* disjoint_ndinsert_right
- \+ *theorem* coe_ndunion
- \+ *theorem* zero_ndunion
- \+ *theorem* cons_ndunion
- \+ *theorem* mem_ndunion
- \+ *theorem* le_ndunion_right
- \+ *theorem* subset_ndunion_right
- \+ *theorem* ndunion_le_add
- \+ *theorem* ndunion_le
- \+ *theorem* subset_ndunion_left
- \+ *theorem* le_ndunion_left
- \+ *theorem* ndunion_le_union
- \+ *theorem* nodup_ndunion
- \+ *theorem* ndunion_eq_union
- \+ *theorem* erase_dup_add
- \+ *theorem* coe_ndinter
- \+ *theorem* zero_ndinter
- \+ *theorem* cons_ndinter_of_mem
- \+ *theorem* ndinter_cons_of_not_mem
- \+ *theorem* mem_ndinter
- \+ *theorem* nodup_ndinter
- \+ *theorem* le_ndinter
- \+ *theorem* ndinter_le_left
- \+ *theorem* ndinter_subset_left
- \+ *theorem* ndinter_subset_right
- \+ *theorem* ndinter_le_right
- \+ *theorem* inter_le_ndinter
- \+ *theorem* ndinter_eq_inter
- \+ *theorem* ndinter_eq_zero_iff_disjoint
- \+ *def* ndinsert
- \+ *def* ndunion
- \+ *def* ndinter

Created src/data/multiset/fold.lean
- \+ *theorem* fold_eq_foldr
- \+ *theorem* coe_fold_r
- \+ *theorem* coe_fold_l
- \+ *theorem* fold_eq_foldl
- \+ *theorem* fold_zero
- \+ *theorem* fold_cons_left
- \+ *theorem* fold_cons_right
- \+ *theorem* fold_cons'_right
- \+ *theorem* fold_cons'_left
- \+ *theorem* fold_add
- \+ *theorem* fold_singleton
- \+ *theorem* fold_distrib
- \+ *theorem* fold_hom
- \+ *theorem* fold_union_inter
- \+ *theorem* fold_erase_dup_idem
- \+ *theorem* le_smul_erase_dup
- \+ *def* fold

Created src/data/multiset/functor.lean
- \+ *lemma* fmap_def
- \+ *lemma* pure_def
- \+ *lemma* bind_def
- \+ *lemma* lift_beta
- \+ *lemma* map_comp_coe
- \+ *lemma* id_traverse
- \+ *lemma* comp_traverse
- \+ *lemma* map_traverse
- \+ *lemma* traverse_map
- \+ *lemma* naturality
- \+ *def* traverse

Created src/data/multiset/intervals.lean
- \+ *lemma* add_consecutive
- \+ *lemma* inter_consecutive
- \+ *lemma* filter_lt_of_top_le
- \+ *lemma* filter_lt_of_le_bot
- \+ *lemma* filter_lt_of_ge
- \+ *lemma* filter_lt
- \+ *lemma* filter_le_of_le_bot
- \+ *lemma* filter_le_of_top_le
- \+ *lemma* filter_le_of_le
- \+ *lemma* filter_le
- \+ *theorem* map_add
- \+ *theorem* map_sub
- \+ *theorem* zero_bot
- \+ *theorem* card
- \+ *theorem* nodup
- \+ *theorem* mem
- \+ *theorem* eq_zero_of_le
- \+ *theorem* self_eq_zero
- \+ *theorem* eq_zero_iff
- \+ *theorem* succ_singleton
- \+ *theorem* succ_top
- \+ *theorem* eq_cons
- \+ *theorem* pred_singleton
- \+ *theorem* not_mem_top
- \+ *def* Ico

Created src/data/multiset/lattice.lean
- \+ *lemma* sup_zero
- \+ *lemma* sup_cons
- \+ *lemma* sup_singleton
- \+ *lemma* sup_add
- \+ *lemma* sup_le
- \+ *lemma* le_sup
- \+ *lemma* sup_mono
- \+ *lemma* sup_erase_dup
- \+ *lemma* sup_ndunion
- \+ *lemma* sup_union
- \+ *lemma* sup_ndinsert
- \+ *lemma* inf_zero
- \+ *lemma* inf_cons
- \+ *lemma* inf_singleton
- \+ *lemma* inf_add
- \+ *lemma* le_inf
- \+ *lemma* inf_le
- \+ *lemma* inf_mono
- \+ *lemma* inf_erase_dup
- \+ *lemma* inf_ndunion
- \+ *lemma* inf_union
- \+ *lemma* inf_ndinsert
- \+ *def* sup
- \+ *def* inf

Created src/data/multiset/nat_antidiagonal.lean
- \+ *lemma* mem_antidiagonal
- \+ *lemma* card_antidiagonal
- \+ *lemma* antidiagonal_zero
- \+ *lemma* nodup_antidiagonal
- \+ *def* antidiagonal

Created src/data/multiset/nodup.lean
- \+ *lemma* pairwise_of_nodup
- \+ *lemma* forall_of_pairwise
- \+ *lemma* nodup_bind
- \+ *lemma* map_eq_map_of_bij_of_nodup
- \+ *theorem* coe_nodup
- \+ *theorem* nodup_zero
- \+ *theorem* nodup_cons
- \+ *theorem* nodup_cons_of_nodup
- \+ *theorem* nodup_singleton
- \+ *theorem* nodup_of_nodup_cons
- \+ *theorem* not_mem_of_nodup_cons
- \+ *theorem* nodup_of_le
- \+ *theorem* not_nodup_pair
- \+ *theorem* nodup_iff_le
- \+ *theorem* nodup_iff_count_le_one
- \+ *theorem* count_eq_one_of_mem
- \+ *theorem* nodup_add
- \+ *theorem* disjoint_of_nodup_add
- \+ *theorem* nodup_add_of_nodup
- \+ *theorem* nodup_of_nodup_map
- \+ *theorem* nodup_map_on
- \+ *theorem* nodup_map
- \+ *theorem* nodup_filter
- \+ *theorem* nodup_attach
- \+ *theorem* nodup_pmap
- \+ *theorem* nodup_erase_eq_filter
- \+ *theorem* nodup_erase_of_nodup
- \+ *theorem* mem_erase_iff_of_nodup
- \+ *theorem* mem_erase_of_nodup
- \+ *theorem* nodup_product
- \+ *theorem* nodup_sigma
- \+ *theorem* nodup_filter_map
- \+ *theorem* nodup_range
- \+ *theorem* nodup_inter_left
- \+ *theorem* nodup_inter_right
- \+ *theorem* nodup_union
- \+ *theorem* nodup_powerset
- \+ *theorem* nodup_powerset_len
- \+ *theorem* nodup_ext
- \+ *theorem* le_iff_subset
- \+ *theorem* range_le
- \+ *theorem* mem_sub_of_nodup
- \+ *def* nodup

Created src/data/multiset/pi.lean
- \+ *lemma* pi.cons_same
- \+ *lemma* pi.cons_ne
- \+ *lemma* pi.cons_swap
- \+ *lemma* pi_zero
- \+ *lemma* pi_cons
- \+ *lemma* pi_cons_injective
- \+ *lemma* card_pi
- \+ *lemma* nodup_pi
- \+ *lemma* mem_pi
- \+ *def* pi.cons
- \+ *def* pi.empty
- \+ *def* pi

Created src/data/multiset/powerset.lean
- \+ *theorem* powerset_aux_eq_map_coe
- \+ *theorem* mem_powerset_aux
- \+ *theorem* powerset_aux_perm_powerset_aux'
- \+ *theorem* powerset_aux'_nil
- \+ *theorem* powerset_aux'_cons
- \+ *theorem* powerset_aux'_perm
- \+ *theorem* powerset_aux_perm
- \+ *theorem* powerset_coe
- \+ *theorem* powerset_coe'
- \+ *theorem* powerset_zero
- \+ *theorem* powerset_cons
- \+ *theorem* mem_powerset
- \+ *theorem* map_single_le_powerset
- \+ *theorem* card_powerset
- \+ *theorem* revzip_powerset_aux
- \+ *theorem* revzip_powerset_aux'
- \+ *theorem* revzip_powerset_aux_lemma
- \+ *theorem* revzip_powerset_aux_perm_aux'
- \+ *theorem* revzip_powerset_aux_perm
- \+ *theorem* powerset_len_aux_eq_map_coe
- \+ *theorem* mem_powerset_len_aux
- \+ *theorem* powerset_len_aux_zero
- \+ *theorem* powerset_len_aux_nil
- \+ *theorem* powerset_len_aux_cons
- \+ *theorem* powerset_len_aux_perm
- \+ *theorem* powerset_len_coe'
- \+ *theorem* powerset_len_coe
- \+ *theorem* powerset_len_zero_left
- \+ *theorem* powerset_len_zero_right
- \+ *theorem* powerset_len_cons
- \+ *theorem* mem_powerset_len
- \+ *theorem* card_powerset_len
- \+ *theorem* powerset_len_le_powerset
- \+ *theorem* powerset_len_mono
- \+ *def* powerset_aux
- \+ *def* powerset_aux'
- \+ *def* powerset
- \+ *def* powerset_len_aux
- \+ *def* powerset_len

Created src/data/multiset/sections.lean
- \+ *lemma* sections_zero
- \+ *lemma* sections_cons
- \+ *lemma* coe_sections
- \+ *lemma* sections_add
- \+ *lemma* mem_sections
- \+ *lemma* card_sections
- \+ *lemma* prod_map_sum
- \+ *def* sections

Created src/data/multiset/sort.lean
- \+ *theorem* coe_sort
- \+ *theorem* sort_sorted
- \+ *theorem* sort_eq
- \+ *theorem* mem_sort
- \+ *theorem* length_sort
- \+ *def* sort

Modified src/data/pnat/factors.lean


Modified src/data/pnat/intervals.lean


Modified src/data/polynomial.lean


Modified src/data/real/nnreal.lean


Modified test/ext.lean


Modified test/mk_iff_of_inductive.lean


Modified test/where.lean




## [2020-07-01 10:05:10](https://github.com/leanprover-community/mathlib/commit/8ba7595)
feat(category/preadditive): properties of preadditive biproducts ([#3245](https://github.com/leanprover-community/mathlib/pull/3245))
### Basic facts about morphisms between biproducts in preadditive categories.
* In any category (with zero morphisms), if `biprod.map f g` is an isomorphism,
  then both `f` and `g` are isomorphisms.
The remaining lemmas hold in any preadditive category.
* If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
  so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
  via Gaussian elimination.
* As a corollary of the previous two facts,
  if we have an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  we can construct an isomorphism `X₂ ≅ Y₂`.
* If `f : W ⊞ X ⟶ Y ⊞ Z` is an isomorphism, either `𝟙 W = 0`,
  or at least one of the component maps `W ⟶ Y` and `W ⟶ Z` is nonzero.
* If `f : ⨁ S ⟶ ⨁ T` is an isomorphism,
  then every column (corresponding to a nonzero summand in the domain)
  has some nonzero matrix entry.
This PR is preliminary to some work on semisimple categories.
#### Estimated changes
Created src/category_theory/preadditive/biproducts.lean
- \+ *lemma* biprod.inl_of_components
- \+ *lemma* biprod.inr_of_components
- \+ *lemma* biprod.of_components_fst
- \+ *lemma* biprod.of_components_snd
- \+ *lemma* biprod.of_components_eq
- \+ *lemma* biprod.of_components_comp
- \+ *lemma* biprod.column_nonzero_of_iso
- \+ *lemma* biproduct.column_nonzero_of_iso'
- \+ *def* is_iso_left_of_is_iso_biprod_map
- \+ *def* is_iso_right_of_is_iso_biprod_map
- \+ *def* biprod.of_components
- \+ *def* biprod.unipotent_upper
- \+ *def* biprod.unipotent_lower
- \+ *def* biprod.gaussian'
- \+ *def* biprod.gaussian
- \+ *def* biprod.iso_elim'
- \+ *def* biprod.iso_elim
- \+ *def* biproduct.column_nonzero_of_iso

Renamed src/category_theory/preadditive.lean to src/category_theory/preadditive/default.lean


Renamed src/category_theory/schur.lean to src/category_theory/preadditive/schur.lean




## [2020-07-01 09:03:47](https://github.com/leanprover-community/mathlib/commit/aff951a)
chore(algebra/big_operators): don't use omega ([#3255](https://github.com/leanprover-community/mathlib/pull/3255))
Postpone importing `omega` a little bit longer.
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/data/nat/choose.lean


Modified src/ring_theory/coprime.lean




## [2020-07-01 07:55:07](https://github.com/leanprover-community/mathlib/commit/e68503a)
feat(ring_theory/valuation): definition and basic properties of valuations ([#3222](https://github.com/leanprover-community/mathlib/pull/3222))
From the perfectoid project.
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/linear_ordered_comm_group_with_zero.lean
- \+ *lemma* one_le_pow_of_one_le'
- \+ *lemma* pow_le_one_of_le_one
- \+ *lemma* eq_one_of_pow_eq_one
- \+ *lemma* pow_eq_one_iff
- \+ *lemma* one_le_pow_iff
- \+ *lemma* pow_le_one_iff

Modified src/algebra/ordered_group.lean
- \+ *lemma* one_le_mul_of_one_le_of_one_le
- \+ *lemma* mul_le_one_of_le_one_of_le_one

Created src/ring_theory/valuation/basic.lean
- \+ *lemma* coe_coe
- \+ *lemma* map_zero
- \+ *lemma* map_one
- \+ *lemma* map_mul
- \+ *lemma* map_add
- \+ *lemma* map_pow
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* zero_iff
- \+ *lemma* ne_zero_iff
- \+ *lemma* map_inv
- \+ *lemma* map_units_inv
- \+ *lemma* map_neg
- \+ *lemma* map_sub_swap
- \+ *lemma* map_sub_le_max
- \+ *lemma* map_add_of_distinct_val
- \+ *lemma* map_eq_of_sub_lt
- \+ *lemma* comap_id
- \+ *lemma* comap_comp
- \+ *lemma* refl
- \+ *lemma* symm
- \+ *lemma* trans
- \+ *lemma* of_eq
- \+ *lemma* map
- \+ *lemma* comap
- \+ *lemma* val_eq
- \+ *lemma* ne_zero
- \+ *lemma* is_equiv_of_map_strict_mono
- \+ *lemma* is_equiv_of_val_le_one
- \+ *lemma* mem_supp_iff
- \+ *lemma* map_add_supp
- \+ *lemma* on_quot_comap_eq
- \+ *lemma* comap_supp
- \+ *lemma* self_le_supp_comap
- \+ *lemma* comap_on_quot_eq
- \+ *lemma* supp_quot
- \+ *lemma* supp_quot_supp
- \+ *theorem* unit_map_eq
- \+ *theorem* map_neg_one
- \+ *def* to_preorder
- \+ *def* comap
- \+ *def* map
- \+ *def* is_equiv
- \+ *def* supp
- \+ *def* on_quot_val
- \+ *def* on_quot



## [2020-07-01 03:39:36](https://github.com/leanprover-community/mathlib/commit/a22cd4d)
chore(algebra/group_with_zero): nolint ([#3254](https://github.com/leanprover-community/mathlib/pull/3254))
Adding two doc strings to make the file lint-free again. cf. [#3253](https://github.com/leanprover-community/mathlib/pull/3253).
#### Estimated changes
Modified src/algebra/group_with_zero.lean




## [2020-07-01 01:31:04](https://github.com/leanprover-community/mathlib/commit/859edfb)
chore(scripts): update nolints.txt ([#3253](https://github.com/leanprover-community/mathlib/pull/3253))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-07-01 00:28:03](https://github.com/leanprover-community/mathlib/commit/89f3bbc)
feat(data/matrix): std_basis_matrix ([#3244](https://github.com/leanprover-community/mathlib/pull/3244))
The definition of
```
def std_basis_matrix (i : m) (j : n) (a : α) : matrix m n α :=
(λ i' j', if i' = i ∧ j' = j then a else 0)
```
and associated lemmas, and some refactoring of `src/ring_theory/matrix_algebra.lean` to use it.
This is work of @jalex-stark which I'm PR'ing as part of getting Cayley-Hamilton ready.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* mul_equiv.map_prod
- \+ *lemma* prod_product'

Modified src/data/matrix/basic.lean
- \+ *lemma* coe_scalar
- \+ *lemma* scalar_apply_eq
- \+ *lemma* scalar_apply_ne
- \+ *lemma* smul_std_basis_matrix
- \+ *lemma* std_basis_matrix_zero
- \+ *lemma* std_basis_matrix_add
- \+ *lemma* matrix_eq_sum_elementary
- \+ *lemma* elementary_eq_basis_mul_basis
- \+ *def* std_basis_matrix

Modified src/ring_theory/algebra.lean
- \+ *lemma* map_sum
- \+ *lemma* trans_apply

Modified src/ring_theory/matrix_algebra.lean
- \+ *lemma* matrix_equiv_tensor_apply_elementary



## [2020-07-01 00:02:51](https://github.com/leanprover-community/mathlib/commit/a40be98)
feat(category_theory/limits/shapes): simp lemmas to decompose pullback_cone.mk.fst ([#3249](https://github.com/leanprover-community/mathlib/pull/3249))
Decompose `(pullback_cone.mk _ _ _).fst` into its first component (+symmetrical and dual versions)
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* mk_fst
- \+ *lemma* mk_snd
- \+ *lemma* mk_inl
- \+ *lemma* mk_inr

