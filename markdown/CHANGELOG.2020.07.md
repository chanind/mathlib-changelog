## [2020-07-31 19:09:51](https://github.com/leanprover-community/mathlib/commit/37ab426)
feat(complete_lattice): put supr_congr and infi_congr back ([#3646](https://github.com/leanprover-community/mathlib/pull/3646))
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *lemma* infi_congr
- \+ *lemma* supr_congr



## [2020-07-31 17:41:12](https://github.com/leanprover-community/mathlib/commit/7e570ed)
chore(*): assorted small lemmas ([#3644](https://github.com/leanprover-community/mathlib/pull/3644))
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *theorem* asymptotics.is_o.trans_le

Modified src/analysis/normed_space/indicator_function.lean
- \+ *lemma* nnnorm_indicator_eq_indicator_nnnorm

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.of_real_lt_top

Modified src/order/filter/basic.lean
- \+ *lemma* filter.union_mem_sup

Modified src/order/liminf_limsup.lean
- \+ *lemma* filter.is_bounded_under.mono

Modified src/topology/instances/ennreal.lean




## [2020-07-31 17:41:10](https://github.com/leanprover-community/mathlib/commit/396a764)
feat(analysis/calculus/fderiv): inversion is differentiable ([#3510](https://github.com/leanprover-community/mathlib/pull/3510))
At an invertible element `x` of a complete normed algebra, the inversion operation of the algebra is Fréchet-differentiable, with derivative `λ t, - x⁻¹ * t * x⁻¹`.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* ring.inverse_unit

Modified src/analysis/asymptotics.lean
- \+ *lemma* asymptotics.is_o_id_const

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable_at_inverse
- \+ *lemma* fderiv_inverse
- \+ *lemma* has_fderiv_at_inverse

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* summable_of_norm_bounded
- \+ *lemma* tsum_of_norm_bounded

Modified src/analysis/normed_space/units.lean
- \+ *lemma* normed_ring.inverse_add
- \+ *lemma* normed_ring.inverse_add_norm
- \+ *lemma* normed_ring.inverse_add_norm_diff_first_order
- \+ *lemma* normed_ring.inverse_add_norm_diff_nth_order
- \+ *lemma* normed_ring.inverse_add_norm_diff_second_order
- \+ *lemma* normed_ring.inverse_add_nth_order
- \+ *lemma* normed_ring.inverse_continuous_at
- \+ *lemma* normed_ring.inverse_one_sub
- \+ *lemma* normed_ring.inverse_one_sub_norm
- \+ *lemma* normed_ring.inverse_one_sub_nth_order
- \+/\- *def* units.add
- \+/\- *lemma* units.add_coe
- \+/\- *lemma* units.one_sub_coe
- \+/\- *def* units.unit_of_nearby
- \+/\- *lemma* units.unit_of_nearby_coe

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
- \+ *structure* needs_prop_class
- \+ *def* test_prop_class



## [2020-07-30 22:46:17](https://github.com/leanprover-community/mathlib/commit/f78a012)
feat(group_theory/subgroup): Add `mem_infi` and `coe_infi` ([#3634](https://github.com/leanprover-community/mathlib/pull/3634))
These already existed for submonoid, but were not lifted to subgroup.
Also adds some missing `norm_cast` attributes to similar lemmas.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.coe_infi
- \+ *lemma* subgroup.mem_infi

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
- \+ *lemma* times_cont_diff.prod_map
- \+ *lemma* times_cont_diff_add
- \+ *lemma* times_cont_diff_at.prod_map'
- \+ *lemma* times_cont_diff_at.prod_map
- \+ *lemma* times_cont_diff_at_fst
- \+ *lemma* times_cont_diff_at_snd
- \+ *lemma* times_cont_diff_neg
- \- *lemma* times_cont_diff_on.map_prod
- \+ *lemma* times_cont_diff_on.prod_map
- \+ *lemma* times_cont_diff_within_at.prod_map'
- \+ *lemma* times_cont_diff_within_at.prod_map
- \+ *lemma* times_cont_diff_within_at_fst
- \+ *lemma* times_cont_diff_within_at_snd

Modified src/data/equiv/local_equiv.lean


Added src/geometry/algebra/lie_group.lean
- \+ *structure* lie_add_group_core
- \+ *structure* lie_add_group_morphism
- \+ *structure* lie_group_core
- \+ *structure* lie_group_morphism
- \+ *lemma* smooth.inv
- \+ *lemma* smooth.mul
- \+ *lemma* smooth_inv
- \+ *lemma* smooth_left_mul
- \+ *lemma* smooth_mul
- \+ *lemma* smooth_on.inv
- \+ *lemma* smooth_on.mul
- \+ *lemma* smooth_pow
- \+ *lemma* smooth_right_mul

Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* basic_smooth_bundle_core.smooth_at_proj
- \+ *lemma* basic_smooth_bundle_core.smooth_on_proj
- \+ *lemma* basic_smooth_bundle_core.smooth_proj
- \+ *lemma* basic_smooth_bundle_core.smooth_within_at_proj
- \+ *lemma* basic_smooth_bundle_core.times_cont_mdiff_at_proj
- \+ *lemma* basic_smooth_bundle_core.times_cont_mdiff_on_proj
- \+ *lemma* basic_smooth_bundle_core.times_cont_mdiff_proj
- \+ *lemma* basic_smooth_bundle_core.times_cont_mdiff_within_at_proj
- \+ *lemma* smooth.comp_smooth_on
- \+ *lemma* smooth.prod_map
- \+ *lemma* smooth.prod_mk
- \+ *lemma* smooth.smooth_at
- \+ *lemma* smooth.smooth_on
- \+ *lemma* smooth.times_cont_mdiff
- \+ *def* smooth
- \+ *lemma* smooth_at.prod_map
- \+ *lemma* smooth_at.prod_mk
- \+ *lemma* smooth_at.smooth_within_at
- \+ *lemma* smooth_at.times_cont_mdiff_at
- \+ *def* smooth_at
- \+ *lemma* smooth_at_const
- \+ *lemma* smooth_at_fst
- \+ *lemma* smooth_at_id
- \+ *lemma* smooth_at_snd
- \+ *lemma* smooth_at_univ
- \+ *lemma* smooth_const
- \+ *lemma* smooth_fst
- \+ *lemma* smooth_id
- \+ *lemma* smooth_iff
- \+ *lemma* smooth_iff_proj_smooth
- \+ *lemma* smooth_on.prod_map
- \+ *lemma* smooth_on.prod_mk
- \+ *lemma* smooth_on.times_cont_mdiff_on
- \+ *def* smooth_on
- \+ *lemma* smooth_on_const
- \+ *lemma* smooth_on_fst
- \+ *lemma* smooth_on_id
- \+ *lemma* smooth_on_iff
- \+ *lemma* smooth_on_snd
- \+ *lemma* smooth_on_univ
- \+ *lemma* smooth_snd
- \+ *lemma* smooth_within_at.prod_map
- \+ *lemma* smooth_within_at.prod_mk
- \+ *lemma* smooth_within_at.smooth_at
- \+ *lemma* smooth_within_at.times_cont_mdiff_within_at
- \+ *def* smooth_within_at
- \+ *lemma* smooth_within_at_const
- \+ *lemma* smooth_within_at_fst
- \+ *lemma* smooth_within_at_id
- \+ *lemma* smooth_within_at_iff
- \+ *lemma* smooth_within_at_snd
- \+ *lemma* tangent_bundle.smooth_at_proj
- \+ *lemma* tangent_bundle.smooth_on_proj
- \+ *lemma* tangent_bundle.smooth_proj
- \+ *lemma* tangent_bundle.smooth_within_at_proj
- \+ *lemma* tangent_bundle.times_cont_mdiff_at_proj
- \+ *lemma* tangent_bundle.times_cont_mdiff_on_proj
- \+ *lemma* tangent_bundle.times_cont_mdiff_proj
- \+ *lemma* tangent_bundle.times_cont_mdiff_within_at_proj
- \+ *lemma* times_cont_mdiff.comp_times_cont_mdiff_on
- \+ *lemma* times_cont_mdiff.prod_map
- \+ *lemma* times_cont_mdiff.prod_mk
- \+ *lemma* times_cont_mdiff.smooth
- \+/\- *lemma* times_cont_mdiff_at.comp
- \+ *lemma* times_cont_mdiff_at.prod_map'
- \+ *lemma* times_cont_mdiff_at.prod_map
- \+ *lemma* times_cont_mdiff_at.prod_mk
- \+ *lemma* times_cont_mdiff_at.smooth_at
- \+ *lemma* times_cont_mdiff_at_fst
- \+ *lemma* times_cont_mdiff_at_snd
- \+ *lemma* times_cont_mdiff_fst
- \+ *lemma* times_cont_mdiff_on.prod_map
- \+ *lemma* times_cont_mdiff_on.prod_mk
- \+ *lemma* times_cont_mdiff_on.smooth_on
- \+ *lemma* times_cont_mdiff_on_fst
- \+ *lemma* times_cont_mdiff_on_snd
- \+ *lemma* times_cont_mdiff_snd
- \+/\- *lemma* times_cont_mdiff_within_at.comp'
- \+/\- *lemma* times_cont_mdiff_within_at.comp
- \+ *lemma* times_cont_mdiff_within_at.prod_map'
- \+ *lemma* times_cont_mdiff_within_at.prod_map
- \+ *lemma* times_cont_mdiff_within_at.prod_mk
- \+ *lemma* times_cont_mdiff_within_at.smooth_within_at
- \+ *lemma* times_cont_mdiff_within_at_fst
- \+ *lemma* times_cont_mdiff_within_at_iff
- \+ *lemma* times_cont_mdiff_within_at_snd

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on_fst
- \+ *lemma* continuous_on_snd
- \+ *lemma* continuous_within_at_fst
- \+ *lemma* continuous_within_at_snd
- \+ *lemma* nhds_within_prod



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
- \+/\- *lemma* Icc_mem_nhds_within_Ici
- \+/\- *lemma* Icc_mem_nhds_within_Iic
- \+/\- *lemma* Icc_mem_nhds_within_Iio
- \+/\- *lemma* Ico_mem_nhds_within_Ici
- \+/\- *lemma* Ico_mem_nhds_within_Iic
- \+/\- *lemma* Ico_mem_nhds_within_Iio
- \+/\- *lemma* Ioc_mem_nhds_within_Iic
- \+/\- *lemma* Ioc_mem_nhds_within_Iio
- \+/\- *lemma* Ioo_mem_nhds_within_Iic
- \+/\- *lemma* Ioo_mem_nhds_within_Iio
- \+/\- *lemma* continuous_within_at_Icc_iff_Ici
- \+/\- *lemma* continuous_within_at_Icc_iff_Iic
- \+/\- *lemma* continuous_within_at_Ico_iff_Ici
- \+/\- *lemma* continuous_within_at_Ioc_iff_Iic
- \+/\- *lemma* continuous_within_at_Ioc_iff_Ioi
- \+/\- *lemma* continuous_within_at_Ioo_iff_Ioi
- \+/\- *lemma* nhds_within_Ico_eq_nhds_within_Ici
- \+/\- *lemma* nhds_within_Ioo_eq_nhds_within_Ioi
- \- *lemma* tfae_mem_nhds_within_Ici'
- \- *lemma* tfae_mem_nhds_within_Iic'
- \- *lemma* tfae_mem_nhds_within_Iio'
- \- *lemma* tfae_mem_nhds_within_Ioi'



## [2020-07-30 08:41:45](https://github.com/leanprover-community/mathlib/commit/29d5f11)
chore(algebra/group_with_zero): weaken assumptions in some lemmas ([#3630](https://github.com/leanprover-community/mathlib/pull/3630))
#### Estimated changes
Modified src/algebra/field.lean
- \+/\- *lemma* ring_hom.map_div
- \+/\- *lemma* ring_hom.map_inv

Modified src/algebra/group/hom.lean
- \+/\- *lemma* monoid_hom.injective_iff

Modified src/algebra/group_with_zero.lean
- \+/\- *lemma* monoid_hom.map_units_inv

Modified src/algebra/ring/basic.lean
- \+/\- *theorem* ring_hom.injective_iff



## [2020-07-30 07:34:56](https://github.com/leanprover-community/mathlib/commit/e1fa5cb)
feat(linear_algebra): invariant basis number property ([#3560](https://github.com/leanprover-community/mathlib/pull/3560))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.bot_ne_top

Added src/linear_algebra/invariant_basis_number.lean
- \+ *lemma* eq_of_fin_equiv
- \+ *lemma* invariant_basis_number_field
- \+ *lemma* nontrivial_of_invariant_basis_number

Modified src/ring_theory/ideals.lean
- \+ *lemma* ideal.map_pi
- \+ *lemma* ideal.mem_pi
- \+ *def* ideal.pi



## [2020-07-30 05:41:44](https://github.com/leanprover-community/mathlib/commit/03c302d)
feat(field_theory/fixed): field is separable over fixed subfield under group action ([#3568](https://github.com/leanprover-community/mathlib/pull/3568))
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \+ *theorem* polynomial.gcd_map
- \+ *theorem* polynomial.is_coprime_map
- \+ *theorem* polynomial.is_unit_map

Modified src/field_theory/fixed.lean


Modified src/field_theory/separable.lean
- \+ *def* is_separable
- \+ *lemma* polynomial.separable.inj_of_prod_X_sub_C
- \+ *lemma* polynomial.separable.injective_of_prod_X_sub_C
- \+ *lemma* polynomial.separable_X_sub_C
- \+ *theorem* polynomial.separable_map
- \+ *lemma* polynomial.separable_prod'
- \+ *lemma* polynomial.separable_prod
- \+ *lemma* polynomial.separable_prod_X_sub_C_iff'
- \+ *lemma* polynomial.separable_prod_X_sub_C_iff



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
Added src/data/pfunctor/multivariate/M.lean
- \+ *theorem* mvpfunctor.M.bisim'
- \+ *theorem* mvpfunctor.M.bisim
- \+ *lemma* mvpfunctor.M.bisim_lemma
- \+ *theorem* mvpfunctor.M.bisim₀
- \+ *def* mvpfunctor.M.corec'
- \+ *def* mvpfunctor.M.corec
- \+ *def* mvpfunctor.M.corec_contents
- \+ *def* mvpfunctor.M.corec_shape
- \+ *def* mvpfunctor.M.dest'
- \+ *theorem* mvpfunctor.M.dest'_eq_dest'
- \+ *def* mvpfunctor.M.dest
- \+ *theorem* mvpfunctor.M.dest_corec'
- \+ *theorem* mvpfunctor.M.dest_corec
- \+ *theorem* mvpfunctor.M.dest_eq_dest'
- \+ *theorem* mvpfunctor.M.dest_map
- \+ *theorem* mvpfunctor.M.map_dest
- \+ *def* mvpfunctor.M.mk
- \+ *inductive* mvpfunctor.M.path
- \+ *def* mvpfunctor.M.path_dest_left
- \+ *def* mvpfunctor.M.path_dest_right
- \+ *def* mvpfunctor.M
- \+ *def* mvpfunctor.Mp
- \+ *def* mvpfunctor.cast_dropB
- \+ *def* mvpfunctor.cast_lastB

Added src/data/pfunctor/multivariate/W.lean
- \+ *def* mvpfunctor.W
- \+ *theorem* mvpfunctor.W_cases
- \+ *def* mvpfunctor.W_dest'
- \+ *theorem* mvpfunctor.W_dest'_W_mk'
- \+ *theorem* mvpfunctor.W_dest'_W_mk
- \+ *theorem* mvpfunctor.W_ind
- \+ *def* mvpfunctor.W_map
- \+ *theorem* mvpfunctor.W_map_W_mk
- \+ *def* mvpfunctor.W_mk'
- \+ *def* mvpfunctor.W_mk
- \+ *theorem* mvpfunctor.W_mk_eq
- \+ *inductive* mvpfunctor.W_path
- \+ *def* mvpfunctor.W_path_cases_on
- \+ *theorem* mvpfunctor.W_path_cases_on_eta
- \+ *def* mvpfunctor.W_path_dest_left
- \+ *theorem* mvpfunctor.W_path_dest_left_W_path_cases_on
- \+ *def* mvpfunctor.W_path_dest_right
- \+ *theorem* mvpfunctor.W_path_dest_right_W_path_cases_on
- \+ *def* mvpfunctor.W_rec
- \+ *theorem* mvpfunctor.W_rec_eq
- \+ *def* mvpfunctor.Wp
- \+ *theorem* mvpfunctor.Wp_ind
- \+ *def* mvpfunctor.Wp_mk
- \+ *def* mvpfunctor.Wp_rec
- \+ *theorem* mvpfunctor.Wp_rec_eq
- \+ *theorem* mvpfunctor.comp_W_path_cases_on
- \+ *theorem* mvpfunctor.map_obj_append1
- \+ *def* mvpfunctor.obj_append1

Modified src/data/pfunctor/multivariate/basic.lean


Modified src/data/pfunctor/univariate/M.lean
- \- *lemma* pfunctor.M.R_is_bisimulation
- \- *lemma* pfunctor.M.coinduction'
- \- *lemma* pfunctor.M.coinduction

Modified src/data/qpf/multivariate/basic.lean


Added src/data/qpf/multivariate/constructions/cofix.lean
- \+ *def* mvqpf.Mcongr
- \+ *def* mvqpf.Mrepr
- \+ *def* mvqpf.cofix.abs
- \+ *lemma* mvqpf.cofix.abs_repr
- \+ *theorem* mvqpf.cofix.bisim'
- \+ *theorem* mvqpf.cofix.bisim
- \+ *theorem* mvqpf.cofix.bisim_rel
- \+ *theorem* mvqpf.cofix.bisim₂
- \+ *def* mvqpf.cofix.corec'
- \+ *def* mvqpf.cofix.corec'₁
- \+ *def* mvqpf.cofix.corec
- \+ *def* mvqpf.cofix.corec₁
- \+ *def* mvqpf.cofix.dest
- \+ *theorem* mvqpf.cofix.dest_corec'
- \+ *theorem* mvqpf.cofix.dest_corec
- \+ *theorem* mvqpf.cofix.dest_corec₁
- \+ *lemma* mvqpf.cofix.dest_mk
- \+ *lemma* mvqpf.cofix.ext
- \+ *lemma* mvqpf.cofix.ext_mk
- \+ *def* mvqpf.cofix.map
- \+ *def* mvqpf.cofix.mk
- \+ *lemma* mvqpf.cofix.mk_dest
- \+ *def* mvqpf.cofix.repr
- \+ *def* mvqpf.cofix
- \+ *def* mvqpf.corecF
- \+ *theorem* mvqpf.corecF_eq
- \+ *theorem* mvqpf.corec_roll
- \+ *def* mvqpf.is_precongr
- \+ *theorem* mvqpf.liftr_map
- \+ *theorem* mvqpf.liftr_map_last'
- \+ *theorem* mvqpf.liftr_map_last

Added src/data/qpf/multivariate/constructions/comp.lean
- \+ *lemma* mvqpf.comp.get_map
- \+ *lemma* mvqpf.comp.map_mk
- \+ *def* mvqpf.comp

Added src/data/qpf/multivariate/constructions/const.lean
- \+ *lemma* mvqpf.const.get_map
- \+ *lemma* mvqpf.const.map_mk
- \+ *def* mvqpf.const

Added src/data/qpf/multivariate/constructions/fix.lean
- \+ *def* mvqpf.W_setoid
- \+ *theorem* mvqpf.Wequiv.abs'
- \+ *theorem* mvqpf.Wequiv.refl
- \+ *theorem* mvqpf.Wequiv.symm
- \+ *inductive* mvqpf.Wequiv
- \+ *theorem* mvqpf.Wequiv_map
- \+ *def* mvqpf.Wrepr
- \+ *theorem* mvqpf.Wrepr_W_mk
- \+ *theorem* mvqpf.Wrepr_equiv
- \+ *def* mvqpf.fix.dest
- \+ *theorem* mvqpf.fix.dest_mk
- \+ *def* mvqpf.fix.drec
- \+ *theorem* mvqpf.fix.ind
- \+ *theorem* mvqpf.fix.ind_aux
- \+ *theorem* mvqpf.fix.ind_rec
- \+ *def* mvqpf.fix.map
- \+ *def* mvqpf.fix.mk
- \+ *theorem* mvqpf.fix.mk_dest
- \+ *def* mvqpf.fix.rec
- \+ *theorem* mvqpf.fix.rec_eq
- \+ *theorem* mvqpf.fix.rec_unique
- \+ *def* mvqpf.fix
- \+ *def* mvqpf.fix_to_W
- \+ *def* mvqpf.recF
- \+ *theorem* mvqpf.recF_eq'
- \+ *theorem* mvqpf.recF_eq
- \+ *theorem* mvqpf.recF_eq_of_Wequiv

Added src/data/qpf/multivariate/constructions/prj.lean
- \+ *def* mvqpf.prj.P
- \+ *def* mvqpf.prj.abs
- \+ *def* mvqpf.prj.map
- \+ *def* mvqpf.prj.repr
- \+ *def* mvqpf.prj

Added src/data/qpf/multivariate/constructions/quot.lean
- \+ *def* mvqpf.quot1.map
- \+ *def* mvqpf.quot1.mvfunctor
- \+ *def* mvqpf.quot1
- \+ *def* mvqpf.quotient_qpf

Added src/data/qpf/multivariate/constructions/sigma.lean
- \+ *def* mvqpf.pi
- \+ *def* mvqpf.sigma

Added src/data/qpf/multivariate/default.lean


Modified src/data/typevec.lean
- \+ *lemma* typevec.drop_fun_diag
- \+ *lemma* typevec.drop_fun_from_append1_drop_last
- \+ *lemma* typevec.drop_fun_id
- \+ *lemma* typevec.drop_fun_of_subtype
- \+ *lemma* typevec.drop_fun_prod
- \+ *lemma* typevec.drop_fun_rel_last
- \+ *lemma* typevec.drop_fun_subtype_val
- \+ *lemma* typevec.drop_fun_to_subtype
- \+ *def* typevec.from_append1_drop_last
- \+ *lemma* typevec.last_fun_from_append1_drop_last
- \+ *lemma* typevec.last_fun_of_subtype
- \+ *lemma* typevec.last_fun_prod
- \+ *lemma* typevec.last_fun_subtype_val
- \+ *lemma* typevec.last_fun_to_subtype
- \+ *lemma* typevec.prod_map_id
- \+ *lemma* typevec.subtype_val_diag_sub
- \+ *lemma* typevec.to_subtype_of_subtype
- \+ *lemma* typevec.to_subtype_of_subtype_assoc



## [2020-07-30 01:14:09+02:00](https://github.com/leanprover-community/mathlib/commit/4985ad5)
Revert "feat(topology): path connected spaces"
This reverts commit 9208c2bd1f6c8dedc0cd1646dd107842f05b0b0c.
#### Estimated changes
Modified src/order/filter/bases.lean
- \- *lemma* filter.has_basis.to_has_basis

Deleted src/topology/path_connected.lean
- \- *def* I_extend
- \- *lemma* I_extend_extends
- \- *lemma* I_extend_one
- \- *lemma* I_extend_range
- \- *lemma* I_extend_zero
- \- *def* I_symm
- \- *lemma* I_symm_one
- \- *lemma* I_symm_zero
- \- *lemma* Icc_zero_one_symm
- \- *lemma* Iic_def
- \- *lemma* coe_I_one
- \- *lemma* coe_I_zero
- \- *lemma* continuous.I_extend
- \- *lemma* continuous_I_symm
- \- *lemma* continuous_proj_I
- \- *lemma* is_open.is_connected_iff_is_path_connected
- \- *lemma* is_path_connected.image
- \- *lemma* is_path_connected.joined_in
- \- *lemma* is_path_connected.mem_path_component
- \- *lemma* is_path_connected.preimage_coe
- \- *lemma* is_path_connected.subset_path_component
- \- *lemma* is_path_connected.union
- \- *def* is_path_connected
- \- *lemma* is_path_connected_iff
- \- *lemma* is_path_connected_iff_eq
- \- *lemma* is_path_connected_iff_path_connected_space
- \- *lemma* joined.continuous_extend
- \- *def* joined.extend
- \- *lemma* joined.extend_one
- \- *lemma* joined.extend_zero
- \- *lemma* joined.mem_path_component
- \- *lemma* joined.refl
- \- *lemma* joined.symm
- \- *lemma* joined.trans
- \- *def* joined
- \- *lemma* joined_in.continuous_extend
- \- *lemma* joined_in.continuous_map
- \- *def* joined_in.extend
- \- *def* joined_in.extend_map
- \- *lemma* joined_in.extend_map_continuous
- \- *lemma* joined_in.extend_map_one
- \- *lemma* joined_in.extend_map_zero
- \- *lemma* joined_in.extend_one
- \- *lemma* joined_in.extend_zero
- \- *lemma* joined_in.joined
- \- *def* joined_in.map
- \- *lemma* joined_in.map_one
- \- *lemma* joined_in.map_zero
- \- *lemma* joined_in.mem
- \- *lemma* joined_in.mono
- \- *lemma* joined_in.refl
- \- *lemma* joined_in.symm
- \- *lemma* joined_in.trans
- \- *def* joined_in
- \- *lemma* joined_in_iff_joined
- \- *lemma* joined_in_univ
- \- *lemma* loc_path_connected_of_bases
- \- *lemma* loc_path_connected_of_is_open
- \- *lemma* mem_path_component_of_mem
- \- *lemma* mem_path_component_self
- \- *lemma* path_component.nonempty
- \- *def* path_component
- \- *lemma* path_component_congr
- \- *def* path_component_in
- \- *lemma* path_component_in_univ
- \- *lemma* path_component_subset_component
- \- *lemma* path_component_symm
- \- *lemma* path_connected_space.continuous_path
- \- *def* path_connected_space.path
- \- *lemma* path_connected_space.path_one
- \- *lemma* path_connected_space.path_zero
- \- *lemma* path_connected_space_iff_connected_space
- \- *lemma* path_connected_space_iff_eq
- \- *lemma* path_connected_space_iff_univ
- \- *lemma* path_connected_subset_basis
- \- *def* proj_I
- \- *lemma* proj_I_I
- \- *lemma* range_proj_I



## [2020-07-30 01:12:56+02:00](https://github.com/leanprover-community/mathlib/commit/9208c2b)
feat(topology): path connected spaces
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.to_has_basis

Added src/topology/path_connected.lean
- \+ *def* I_extend
- \+ *lemma* I_extend_extends
- \+ *lemma* I_extend_one
- \+ *lemma* I_extend_range
- \+ *lemma* I_extend_zero
- \+ *def* I_symm
- \+ *lemma* I_symm_one
- \+ *lemma* I_symm_zero
- \+ *lemma* Icc_zero_one_symm
- \+ *lemma* Iic_def
- \+ *lemma* coe_I_one
- \+ *lemma* coe_I_zero
- \+ *lemma* continuous.I_extend
- \+ *lemma* continuous_I_symm
- \+ *lemma* continuous_proj_I
- \+ *lemma* is_open.is_connected_iff_is_path_connected
- \+ *lemma* is_path_connected.image
- \+ *lemma* is_path_connected.joined_in
- \+ *lemma* is_path_connected.mem_path_component
- \+ *lemma* is_path_connected.preimage_coe
- \+ *lemma* is_path_connected.subset_path_component
- \+ *lemma* is_path_connected.union
- \+ *def* is_path_connected
- \+ *lemma* is_path_connected_iff
- \+ *lemma* is_path_connected_iff_eq
- \+ *lemma* is_path_connected_iff_path_connected_space
- \+ *lemma* joined.continuous_extend
- \+ *def* joined.extend
- \+ *lemma* joined.extend_one
- \+ *lemma* joined.extend_zero
- \+ *lemma* joined.mem_path_component
- \+ *lemma* joined.refl
- \+ *lemma* joined.symm
- \+ *lemma* joined.trans
- \+ *def* joined
- \+ *lemma* joined_in.continuous_extend
- \+ *lemma* joined_in.continuous_map
- \+ *def* joined_in.extend
- \+ *def* joined_in.extend_map
- \+ *lemma* joined_in.extend_map_continuous
- \+ *lemma* joined_in.extend_map_one
- \+ *lemma* joined_in.extend_map_zero
- \+ *lemma* joined_in.extend_one
- \+ *lemma* joined_in.extend_zero
- \+ *lemma* joined_in.joined
- \+ *def* joined_in.map
- \+ *lemma* joined_in.map_one
- \+ *lemma* joined_in.map_zero
- \+ *lemma* joined_in.mem
- \+ *lemma* joined_in.mono
- \+ *lemma* joined_in.refl
- \+ *lemma* joined_in.symm
- \+ *lemma* joined_in.trans
- \+ *def* joined_in
- \+ *lemma* joined_in_iff_joined
- \+ *lemma* joined_in_univ
- \+ *lemma* loc_path_connected_of_bases
- \+ *lemma* loc_path_connected_of_is_open
- \+ *lemma* mem_path_component_of_mem
- \+ *lemma* mem_path_component_self
- \+ *lemma* path_component.nonempty
- \+ *def* path_component
- \+ *lemma* path_component_congr
- \+ *def* path_component_in
- \+ *lemma* path_component_in_univ
- \+ *lemma* path_component_subset_component
- \+ *lemma* path_component_symm
- \+ *lemma* path_connected_space.continuous_path
- \+ *def* path_connected_space.path
- \+ *lemma* path_connected_space.path_one
- \+ *lemma* path_connected_space.path_zero
- \+ *lemma* path_connected_space_iff_connected_space
- \+ *lemma* path_connected_space_iff_eq
- \+ *lemma* path_connected_space_iff_univ
- \+ *lemma* path_connected_subset_basis
- \+ *def* proj_I
- \+ *lemma* proj_I_I
- \+ *lemma* range_proj_I



## [2020-07-29 21:50:21](https://github.com/leanprover-community/mathlib/commit/86c83c3)
feat(topology): two missing connectedness lemmas ([#3626](https://github.com/leanprover-community/mathlib/pull/3626))
From the sphere eversion project.
#### Estimated changes
Modified src/topology/subset_properties.lean
- \+ *lemma* is_connected_iff_connected_space
- \+ *lemma* is_preconnected_iff_preconnected_space



## [2020-07-29 20:38:16](https://github.com/leanprover-community/mathlib/commit/ebeeee7)
feat(filters): a couple more lemmas ([#3625](https://github.com/leanprover-community/mathlib/pull/3625))
Random lemmas gathered while thinking about https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/nhds_left.20and.20nhds_right
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.union_distrib_Inter_left
- \+ *lemma* set.union_distrib_Inter_right

Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.ext
- \+ *lemma* filter.has_basis.sup
- \+ *lemma* filter.has_basis_binfi_principal'

Modified src/order/filter/basic.lean
- \+ *lemma* filter.binfi_sup_left
- \+ *lemma* filter.binfi_sup_right
- \- *lemma* filter.infi_sup_eq
- \+ *lemma* filter.infi_sup_left
- \+ *lemma* filter.infi_sup_right



## [2020-07-29 13:58:44](https://github.com/leanprover-community/mathlib/commit/652fb2e)
chore(doc/*): add README files ([#3623](https://github.com/leanprover-community/mathlib/pull/3623))
#### Estimated changes
Added docs/README.md


Added docs/contribute/README.md


Added docs/extras/README.md


Added docs/install/README.md


Added docs/theories/README.md




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
- \+ *inductive* lint_verbosity

Modified test/lint.lean




## [2020-07-29 11:19:36](https://github.com/leanprover-community/mathlib/commit/b0d1d17)
feat(data/ulift): add `monad ulift` and `monad plift` ([#3588](https://github.com/leanprover-community/mathlib/pull/3588))
We add `functor`/`applicative`/`monad` instances for `ulift` and `plift`.
#### Estimated changes
Modified src/data/ulift.lean
- \+/\- *lemma* plift.rec.constant
- \+/\- *lemma* ulift.rec.constant



## [2020-07-29 08:21:11](https://github.com/leanprover-community/mathlib/commit/80f2762)
feat(topology): assorted topological lemmas ([#3619](https://github.com/leanprover-community/mathlib/pull/3619))
from the sphere eversion project
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.union_diff_cancel'
- \+ *lemma* subtype.preimage_coe_nonempty

Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.ex_mem
- \+ *lemma* filter.has_basis.has_basis_self_subset
- \+ *lemma* filter.has_basis.restrict
- \+ *lemma* filter.has_basis_iff

Modified src/order/filter/basic.lean
- \+ *lemma* filter.image_coe_mem_sets
- \+ *lemma* filter.image_mem_sets
- \+ *lemma* filter.not_ne_bot

Modified src/topology/basic.lean
- \+ *lemma* closure_eq_interior_union_frontier
- \+ *lemma* closure_eq_self_union_frontier
- \+ *lemma* is_closed_iff_nhds

Modified src/topology/order.lean
- \+ *lemma* continuous_induced_rng'

Modified src/topology/subset_properties.lean
- \+ *def* connected_component_in
- \+ *lemma* connected_space_iff_connected_component
- \+ *lemma* eq_univ_of_nonempty_clopen
- \+ *lemma* is_connected_range



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
- \+ *lemma* category_theory.monoidal_category.left_unitor_conjugation
- \+ *lemma* category_theory.monoidal_category.right_unitor_conjugation

Added src/category_theory/monoidal/unitors.lean
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_10_13
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_14
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_15
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_1_2
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_1_4
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_1_7
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_3_4
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_4'
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_4
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_5_6
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_6'
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_6
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_7
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_8
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_9
- \+ *lemma* category_theory.monoidal_category.unitors_equal.cells_9_13
- \+ *lemma* category_theory.monoidal_category.unitors_equal



## [2020-07-28 22:08:48](https://github.com/leanprover-community/mathlib/commit/2e6c488)
chore(order/complete_lattice): use `Prop` args in `infi_inf` etc ([#3611](https://github.com/leanprover-community/mathlib/pull/3611))
This way one can `rw binfi_inf` first, then prove `∃ i, p i`.
Also move some code up to make it available near `infi_inf`.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+/\- *lemma* binfi_inf
- \+/\- *lemma* inf_infi
- \+/\- *lemma* infi_inf

Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.prod_infi_left
- \+/\- *lemma* filter.prod_infi_right

Modified src/topology/algebra/ordered.lean


Modified src/topology/bases.lean


Modified src/topology/continuous_on.lean




## [2020-07-28 21:33:31](https://github.com/leanprover-community/mathlib/commit/aafc486)
feat(topology/ordered): intervals frontiers ([#3617](https://github.com/leanprover-community/mathlib/pull/3617))
from the sphere eversion project
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+ *lemma* closure_Icc
- \+ *lemma* closure_Ici
- \+/\- *lemma* closure_Ico
- \+ *lemma* closure_Iic
- \+/\- *lemma* closure_Iio
- \+/\- *lemma* closure_Ioc
- \+/\- *lemma* closure_Ioi
- \+/\- *lemma* closure_Ioo
- \+ *lemma* frontier_Icc
- \+ *lemma* frontier_Ici
- \+ *lemma* frontier_Ico
- \+ *lemma* frontier_Iic
- \+ *lemma* frontier_Iio
- \+ *lemma* frontier_Ioc
- \+ *lemma* frontier_Ioi
- \+ *lemma* frontier_Ioo



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
- \+/\- *lemma* mv_polynomial.coeff_map
- \+/\- *def* mv_polynomial.eval
- \+/\- *lemma* mv_polynomial.eval_C
- \+/\- *lemma* mv_polynomial.eval_X
- \- *lemma* mv_polynomial.eval_add
- \+/\- *lemma* mv_polynomial.eval_monomial
- \- *lemma* mv_polynomial.eval_mul
- \- *lemma* mv_polynomial.eval_neg
- \- *lemma* mv_polynomial.eval_one
- \- *lemma* mv_polynomial.eval_pow
- \- *lemma* mv_polynomial.eval_sub
- \- *lemma* mv_polynomial.eval_zero
- \+/\- *lemma* mv_polynomial.eval₂_hom_X
- \+ *lemma* mv_polynomial.eval₂_hom_congr
- \+/\- *lemma* mv_polynomial.eval₂_neg
- \+/\- *lemma* mv_polynomial.eval₂_rename
- \+/\- *lemma* mv_polynomial.eval₂_sub
- \+/\- *def* mv_polynomial.map
- \- *theorem* mv_polynomial.map_add
- \- *theorem* mv_polynomial.map_mul
- \- *lemma* mv_polynomial.map_neg
- \- *theorem* mv_polynomial.map_one
- \- *lemma* mv_polynomial.map_pow
- \- *lemma* mv_polynomial.map_sub
- \+/\- *def* mv_polynomial.rename
- \- *lemma* mv_polynomial.rename_add
- \- *lemma* mv_polynomial.rename_mul
- \- *lemma* mv_polynomial.rename_neg
- \- *lemma* mv_polynomial.rename_one
- \- *lemma* mv_polynomial.rename_pow
- \- *lemma* mv_polynomial.rename_sub
- \- *lemma* mv_polynomial.rename_zero
- \+/\- *lemma* mv_polynomial.smul_eval

Modified src/field_theory/chevalley_warning.lean


Modified src/field_theory/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.evalₗ_apply
- \+/\- *lemma* mv_polynomial.map_range_eq_map

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
- \- *lemma* interior_eq_of_open
- \+ *lemma* is_open.interior_eq

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
- \+ *lemma* filter.eventually.exists_measurable_mem
- \+ *lemma* filter.principal_is_measurably_generated_iff

Modified src/measure_theory/measure_space.lean




## [2020-07-28 17:35:00](https://github.com/leanprover-community/mathlib/commit/7236938)
feat(measure_theory/measure_space): add `count_apply_infinite` ([#3592](https://github.com/leanprover-community/mathlib/pull/3592))
Also add some supporting lemmas about `set.infinite`.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* infinite.exists_subset_card_eq

Modified src/data/set/finite.lean
- \+ *lemma* set.infinite.exists_subset_card_eq
- \+ *theorem* set.infinite.to_subtype
- \+ *theorem* set.infinite_coe_iff

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.count_apply_eq_top
- \+ *lemma* measure_theory.measure.count_apply_finite
- \+ *lemma* measure_theory.measure.count_apply_infinite
- \+ *lemma* measure_theory.measure.count_apply_lt_top



## [2020-07-28 17:02:06](https://github.com/leanprover-community/mathlib/commit/f6f6f8a)
feat(linear_algebra/affine_space): more affine subspace lemmas ([#3552](https://github.com/leanprover-community/mathlib/pull/3552))
Add more lemmas on affine subspaces that came up in the course of
proving existence and uniqueness of the circumcenter of a simplex in a
Euclidean space.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* add_torsor.vsub_set_singleton

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* affine_space.vector_span_singleton
- \+ *lemma* affine_subspace.coe_affine_span_singleton
- \+ *lemma* affine_subspace.direction_affine_span_insert
- \+ *lemma* affine_subspace.direction_sup
- \+ *lemma* affine_subspace.mem_affine_span_insert_iff



## [2020-07-28 15:30:51](https://github.com/leanprover-community/mathlib/commit/7848f28)
feat(category_theory): Mon_ (Type u) ≌ Mon.{u} ([#3562](https://github.com/leanprover-community/mathlib/pull/3562))
Verifying that internal monoid objects in Type are the same thing as bundled monoid objects.
#### Estimated changes
Modified src/algebra/category/Group/zero.lean


Added src/category_theory/limits/shapes/types.lean
- \+ *lemma* category_theory.limits.types.prod
- \+ *lemma* category_theory.limits.types.prod_fst
- \+ *lemma* category_theory.limits.types.prod_lift
- \+ *lemma* category_theory.limits.types.prod_map
- \+ *lemma* category_theory.limits.types.prod_snd
- \+ *lemma* category_theory.limits.types.terminal
- \+ *lemma* category_theory.limits.types.terminal_from
- \+ *def* category_theory.limits.types.types_has_binary_products
- \+ *def* category_theory.limits.types.types_has_products
- \+ *def* category_theory.limits.types.types_has_terminal

Added src/category_theory/monoidal/internal.lean
- \+ *lemma* Mod.assoc_flip
- \+ *def* Mod.comap
- \+ *def* Mod.comp
- \+ *lemma* Mod.comp_hom'
- \+ *structure* Mod.hom
- \+ *def* Mod.id
- \+ *lemma* Mod.id_hom'
- \+ *def* Mod.regular
- \+ *structure* Mod
- \+ *lemma* Mon_.assoc_flip
- \+ *def* Mon_.comp
- \+ *lemma* Mon_.comp_hom'
- \+ *def* Mon_.forget
- \+ *structure* Mon_.hom
- \+ *def* Mon_.id
- \+ *lemma* Mon_.id_hom'
- \+ *structure* Mon_

Added src/category_theory/monoidal/internal/types.lean
- \+ *def* Mon_Type_equivalence_Mon.functor
- \+ *def* Mon_Type_equivalence_Mon.inverse
- \+ *def* Mon_Type_equivalence_Mon
- \+ *def* Mon_Type_equivalence_Mon_forget

Modified src/category_theory/monoidal/types.lean
- \+ *lemma* category_theory.monoidal.associator_hom_apply
- \+ *lemma* category_theory.monoidal.associator_inv_apply
- \+ *lemma* category_theory.monoidal.left_unitor_hom_apply
- \+ *lemma* category_theory.monoidal.left_unitor_inv_apply
- \+ *lemma* category_theory.monoidal.right_unitor_hom_apply
- \+ *lemma* category_theory.monoidal.right_unitor_inv_apply
- \+ *lemma* category_theory.monoidal.tensor_apply

Modified src/tactic/ext.lean
- \+ *lemma* punit.ext
- \+ *lemma* unit.ext

Modified test/ext.lean
- \- *lemma* unit.ext



## [2020-07-28 14:20:39](https://github.com/leanprover-community/mathlib/commit/9e841c8)
feat(data/list/basic): add a proof that `(a :: l) ≠ l` ([#3584](https://github.com/leanprover-community/mathlib/pull/3584))
`list.cons_ne_self` is motivated by the existence of `nat.succ_ne_self`.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.cons_ne_self



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
- \+ *def* affine_space.simplex.mk_of_point
- \+ *lemma* affine_space.simplex.mk_of_point_points
- \+ *structure* affine_space.simplex
- \+ *abbreviation* affine_space.triangle



## [2020-07-28 11:47:58](https://github.com/leanprover-community/mathlib/commit/5a876ca)
feat(category_theory): monoidal_category (C ⥤ C) ([#3557](https://github.com/leanprover-community/mathlib/pull/3557))
#### Estimated changes
Added src/category_theory/monoidal/End.lean
- \+ *def* category_theory.endofunctor_monoidal_category
- \+ *def* category_theory.tensoring_right_monoidal

Modified src/category_theory/monoidal/category.lean
- \+ *def* category_theory.monoidal_category.tensoring_right

Modified src/category_theory/monoidal/functor.lean
- \+ *lemma* category_theory.monoidal_functor.map_left_unitor
- \+ *lemma* category_theory.monoidal_functor.map_right_unitor
- \+ *lemma* category_theory.monoidal_functor.map_tensor



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
- \+/\- *lemma* category_theory.limits.types.types_colimit
- \+/\- *lemma* category_theory.limits.types.types_colimit_desc
- \+/\- *lemma* category_theory.limits.types.types_colimit_map
- \+/\- *lemma* category_theory.limits.types.types_colimit_pre
- \+/\- *lemma* category_theory.limits.types.types_colimit_ι
- \+/\- *lemma* category_theory.limits.types.types_limit
- \+/\- *lemma* category_theory.limits.types.types_limit_lift
- \+/\- *lemma* category_theory.limits.types.types_limit_map
- \+/\- *lemma* category_theory.limits.types.types_limit_pre
- \+/\- *lemma* category_theory.limits.types.types_limit_π



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
Added src/algebra/category/Algebra/limits.lean
- \+ *def* Algebra.has_limits.limit
- \+ *def* Algebra.has_limits.limit_is_limit
- \+ *def* Algebra.limit_π_alg_hom
- \+ *def* Algebra.sections_subalgebra

Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/CommRing/limits.lean
- \- *def* CommRing.CommRing_has_limits.limit
- \- *def* CommRing.CommRing_has_limits.limit_is_limit
- \- *def* CommRing.limit_π_ring_hom
- \+ *def* Ring.forget₂_AddCommGroup_preserves_limits_aux
- \+ *def* SemiRing.forget₂_AddCommMon_preserves_limits_aux
- \+ *def* SemiRing.forget₂_Mon_preserves_limits_aux
- \+ *def* SemiRing.has_limits.limit
- \+ *def* SemiRing.has_limits.limit_is_limit
- \+ *def* SemiRing.limit_π_ring_hom
- \+ *def* SemiRing.sections_subsemiring

Modified src/algebra/category/Group/limits.lean
- \- *def* AddCommGroup.AddCommGroup_has_limits.limit
- \- *def* AddCommGroup.AddCommGroup_has_limits.limit_is_limit
- \+/\- *def* AddCommGroup.kernel_iso_ker_over
- \- *def* AddCommGroup.limit_π_add_monoid_hom
- \+ *def* CommGroup.forget₂_CommMon_preserves_limits_aux
- \+ *def* Group.sections_subgroup

Modified src/algebra/category/Group/zero.lean


Added src/algebra/category/Module/limits.lean
- \+ *def* Module.has_limits.limit
- \+ *def* Module.has_limits.limit_is_limit
- \+ *def* Module.limit_π_linear_map
- \+ *def* Module.sections_submodule

Modified src/algebra/category/Mon/basic.lean


Added src/algebra/category/Mon/limits.lean
- \+ *def* Mon.has_limits.limit
- \+ *def* Mon.has_limits.limit_is_limit
- \+ *def* Mon.limit_π_monoid_hom
- \+ *def* Mon.sections_submonoid

Modified src/algebra/module/basic.lean
- \+ *theorem* linear_map.coe_inj
- \- *lemma* linear_map.coe_injective

Modified src/algebra/ring/pi.lean
- \+ *lemma* pi.ring_hom_apply

Modified src/analysis/normed_space/operator_norm.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/concrete_category/bundled_hom.lean


Modified src/category_theory/limits/creates.lean
- \+ *def* category_theory.creates_limit_of_fully_faithful_of_iso
- \+ *def* category_theory.creates_limit_of_fully_faithful_of_lift

Modified src/category_theory/reflect_isomorphisms.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* pi.algebra_map_apply

Modified src/topology/algebra/module.lean
- \+ *theorem* continuous_linear_map.coe_inj
- \- *theorem* continuous_linear_map.coe_injective'



## [2020-07-28 08:55:31](https://github.com/leanprover-community/mathlib/commit/ce70305)
feat(category_theory): monoidal_category (C ⥤ D) when D is monoidal ([#3571](https://github.com/leanprover-community/mathlib/pull/3571))
When `C` is any category, and `D` is a monoidal category,
there is a natural "pointwise" monoidal structure on `C ⥤ D`.
The initial intended application is tensor product of presheaves.
#### Estimated changes
Added src/category_theory/monoidal/functor_category.lean
- \+ *lemma* category_theory.monoidal.associator_hom_app
- \+ *lemma* category_theory.monoidal.associator_inv_app
- \+ *def* category_theory.monoidal.functor_category.tensor_hom
- \+ *def* category_theory.monoidal.functor_category.tensor_obj
- \+ *lemma* category_theory.monoidal.left_unitor_hom_app
- \+ *lemma* category_theory.monoidal.left_unitor_inv_app
- \+ *lemma* category_theory.monoidal.right_unitor_hom_app
- \+ *lemma* category_theory.monoidal.right_unitor_inv_app
- \+ *lemma* category_theory.monoidal.tensor_hom_app
- \+ *lemma* category_theory.monoidal.tensor_obj_map
- \+ *lemma* category_theory.monoidal.tensor_obj_obj
- \+ *lemma* category_theory.monoidal.tensor_unit_map
- \+ *lemma* category_theory.monoidal.tensor_unit_obj



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
- \+/\- *def* pfun.as_subtype
- \+/\- *def* pfun.dom

Modified src/data/set/basic.lean
- \+/\- *theorem* subtype.coe_image_subset
- \+ *lemma* subtype.coe_preimage_self

Modified src/data/set/countable.lean


Modified src/data/set/lattice.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* submodule.mem_span_singleton_self



## [2020-07-28 02:35:45](https://github.com/leanprover-community/mathlib/commit/d04e3fc)
feat(linear_algebra/char_poly): relates the characteristic polynomial to trace, determinant, and dimension ([#3536](https://github.com/leanprover-community/mathlib/pull/3536))
adds lemmas about the number of fixed points of a permutation
adds lemmas connecting the trace, determinant, and dimension of a matrix to its characteristic polynomial
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.scalar.commute

Modified src/group_theory/perm/cycles.lean
- \+ *lemma* equiv.perm.fixed_point_card_lt_of_ne_one
- \+ *lemma* equiv.perm.one_lt_nonfixed_point_card_of_ne_one

Added src/linear_algebra/char_poly/coeff.lean
- \+ *lemma* char_matrix_apply_nat_degree
- \+ *lemma* char_matrix_apply_nat_degree_le
- \+ *lemma* char_poly_coeff_eq_prod_coeff_of_le
- \+ *theorem* char_poly_degree_eq_dim
- \+ *lemma* char_poly_monic
- \+ *lemma* char_poly_monic_of_nontrivial
- \+ *theorem* char_poly_nat_degree_eq_dim
- \+ *lemma* char_poly_sub_diagonal_degree_lt
- \+ *theorem* det_eq_sign_char_poly_coeff
- \+ *lemma* det_of_card_zero
- \+ *lemma* eval_det
- \+ *lemma* mat_poly_equiv_eval
- \+ *theorem* trace_eq_neg_char_poly_coeff

Modified src/linear_algebra/determinant.lean
- \+ *lemma* matrix.alg_hom.map_det
- \+ *lemma* matrix.ring_hom.map_det



## [2020-07-28 02:35:42](https://github.com/leanprover-community/mathlib/commit/a9481d9)
feat(analysis/convex/basic): add lemmas about transformations of convex sets and functions ([#3524](https://github.com/leanprover-community/mathlib/pull/3524))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex.affine_image
- \+ *lemma* convex.affine_preimage
- \+ *lemma* convex.combo_affine_apply
- \+ *lemma* convex.combo_to_vadd
- \+ *lemma* convex.translate_preimage_left
- \+ *lemma* convex.translate_preimage_right
- \+ *lemma* convex_on.comp_affine_map
- \+ *lemma* convex_on.comp_linear_map
- \+ *lemma* convex_on.translate_left
- \+ *lemma* convex_on.translate_right

Modified src/analysis/convex/cone.lean




## [2020-07-28 02:35:40](https://github.com/leanprover-community/mathlib/commit/005201a)
feat(linear_algebra/adic_completion): basic definitions about completions of modules ([#3452](https://github.com/leanprover-community/mathlib/pull/3452))
#### Estimated changes
Added src/linear_algebra/adic_completion.lean
- \+ *lemma* Hausdorffification.induction_on
- \+ *def* Hausdorffification.lift
- \+ *theorem* Hausdorffification.lift_comp_of
- \+ *theorem* Hausdorffification.lift_eq
- \+ *theorem* Hausdorffification.lift_of
- \+ *def* Hausdorffification.of
- \+ *def* Hausdorffification
- \+ *lemma* adic_completion.coe_eval
- \+ *def* adic_completion.eval
- \+ *lemma* adic_completion.eval_apply
- \+ *lemma* adic_completion.eval_comp_of
- \+ *lemma* adic_completion.eval_of
- \+ *lemma* adic_completion.ext
- \+ *def* adic_completion.of
- \+ *lemma* adic_completion.of_apply
- \+ *lemma* adic_completion.range_eval
- \+ *def* adic_completion
- \+ *theorem* is_Hausdorff.infi_pow_smul
- \+ *def* is_Hausdorff
- \+ *def* is_adic_complete
- \+ *def* is_precomplete

Added src/linear_algebra/smodeq.lean
- \+ *theorem* smodeq.add
- \+ *theorem* smodeq.bot
- \+ *theorem* smodeq.comap
- \+ *theorem* smodeq.map
- \+ *theorem* smodeq.mono
- \+ *theorem* smodeq.refl
- \+ *theorem* smodeq.smul
- \+ *theorem* smodeq.symm
- \+ *theorem* smodeq.top
- \+ *theorem* smodeq.trans
- \+ *theorem* smodeq.zero
- \+ *def* smodeq

Modified src/ring_theory/ideal_operations.lean
- \+ *theorem* ideal.top_pow
- \+ *theorem* submodule.map_smul''



## [2020-07-28 01:10:52](https://github.com/leanprover-community/mathlib/commit/7cd1e26)
feat(data/set/basic): range_unique ([#3582](https://github.com/leanprover-community/mathlib/pull/3582))
Add a lemma on the `range` of a function from a `unique` type.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.range_unique



## [2020-07-28 01:10:50](https://github.com/leanprover-community/mathlib/commit/23bd09a)
chore(deprecated/ring): removing uses ([#3577](https://github.com/leanprover-community/mathlib/pull/3577))
This strips out a lot of the use of `deprecated.ring`. It's now only imported by `data.polynomial.eval`, and `ring_theory.free_ring`.
#### Estimated changes
Modified src/algebra/direct_limit.lean
- \+/\- *lemma* ring.direct_limit.of_pow

Modified src/algebra/group_power.lean
- \- *lemma* is_semiring_hom.map_pow

Modified src/algebra/group_with_zero.lean


Modified src/data/complex/exponential.lean


Modified src/data/equiv/ring.lean
- \- *def* ring_equiv.of'
- \- *def* ring_equiv.of

Modified src/data/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.is_id
- \+/\- *def* mv_polynomial.iter_to_sum
- \+/\- *lemma* mv_polynomial.map_eval₂
- \+/\- *theorem* mv_polynomial.map_id
- \+/\- *lemma* mv_polynomial.map_rename
- \+/\- *def* mv_polynomial.sum_to_iter

Modified src/data/polynomial/eval.lean
- \+/\- *lemma* polynomial.map_pow

Modified src/deprecated/group.lean


Modified src/deprecated/ring.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/ring_theory/free_comm_ring.lean
- \+ *def* free_ring.of'

Modified src/ring_theory/free_ring.lean
- \+/\- *lemma* free_ring.lift_comp_of

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
- \+ *lemma* polynomial.comp_eq_sum_left
- \+ *lemma* polynomial.eval_eq_sum
- \+ *lemma* polynomial.eval₂_eq_sum

Modified src/data/polynomial/identities.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/minimal_polynomial.lean


Modified src/field_theory/separable.lean
- \+ *lemma* polynomial.expand_eq_sum

Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra.subring_algebra_map_apply
- \+ *lemma* algebra.subring_coe_algebra_map
- \+ *lemma* algebra.subring_coe_algebra_map_hom

Modified src/ring_theory/integral_closure.lean
- \+/\- *theorem* integral_closure_idem
- \+ *theorem* is_integral_of_is_algebra_tower

Modified src/ring_theory/polynomial/basic.lean
- \+ *theorem* polynomial.map_restriction

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
- \+ *theorem* monoid_hom.ext_int



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
- \+ *lemma* finset.map_subtype_subset
- \+ *lemma* finset.property_of_mem_map_subtype



## [2020-07-27 15:26:50](https://github.com/leanprover-community/mathlib/commit/3550f4f)
feat(*): remaining preliminaries for Haar measure ([#3541](https://github.com/leanprover-community/mathlib/pull/3541))
Define `has_mul (finset α)`
more convenient formulation of `is_compact.finite_compact_cover`
some lemma additions
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* finset.coe_mul
- \+ *lemma* finset.mem_mul
- \+ *lemma* finset.mul_card_le
- \+ *lemma* finset.mul_def
- \+ *lemma* finset.mul_mem_mul
- \+ *lemma* set.inv_subset
- \+ *lemma* set.inv_subset_inv
- \+/\- *lemma* set.preimage_mul_right_one'

Modified src/data/finset/lattice.lean
- \+ *lemma* finset.bInter_insert_update
- \+ *lemma* finset.bUnion_insert_update
- \+ *lemma* finset.infi_insert_update
- \+ *lemma* finset.supr_insert_update

Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/eval.lean


Modified src/data/set/basic.lean
- \+ *lemma* function.surjective.preimage_subset_preimage_iff
- \+ *lemma* set.preimage_congr

Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measurable.mul
- \+/\- *lemma* measurable_mul
- \+ *lemma* measurable_mul_left
- \+ *lemma* measurable_mul_right

Modified src/topology/opens.lean
- \+ *lemma* topological_space.opens.coe_mk

Modified src/topology/separation.lean




## [2020-07-27 14:54:00](https://github.com/leanprover-community/mathlib/commit/adfcfe7)
feat(category_theory/concrete_category): epi_of_surjective ([#3585](https://github.com/leanprover-community/mathlib/pull/3585))
Also, change the proof of `mono_of_injective` to use the fact that the forgetful function reflects monomorphisms.
#### Estimated changes
Modified src/category_theory/concrete_category/basic.lean
- \+ *lemma* category_theory.concrete_category.epi_of_surjective



## [2020-07-27 12:21:03](https://github.com/leanprover-community/mathlib/commit/aeff5fc)
chore(ci): get xz archive ([#3581](https://github.com/leanprover-community/mathlib/pull/3581))
We've been storing both .gz and .xz for a while for backward compatibility but will eventually drop .gz support.
#### Estimated changes
Modified scripts/fetch_olean_cache.sh




## [2020-07-27 12:20:59](https://github.com/leanprover-community/mathlib/commit/133067c)
feat(set_theory/cardinal_ordinal): cardinal.mk_finset_eq_mk ([#3578](https://github.com/leanprover-community/mathlib/pull/3578))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* list.to_finset_surjective

Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.mk_finset_eq_mk



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
- \+ *lemma* is_compact.finite_measure_of_nhds_within
- \+ *lemma* is_compact.measure_zero_of_nhds_within
- \+ *lemma* measure_theory.compl_mem_ae_iff
- \+ *lemma* measure_theory.measure.compl_mem_cofinite



## [2020-07-27 11:35:46](https://github.com/leanprover-community/mathlib/commit/da64c7f)
chore(order/filter/basic): use `set.eq_on` in a few lemmas ([#3565](https://github.com/leanprover-community/mathlib/pull/3565))
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean


Modified src/geometry/manifold/local_invariant_properties.lean


Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_eq.eventually
- \+ *lemma* filter.eventually_eq_principal
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
- \+ *lemma* continuous_multilinear_map.coe_continuous

Modified src/topology/continuous_map.lean
- \+ *lemma* continuous_map.coe_continuous

Modified src/topology/tactic.lean
- \+ *lemma* continuous_id'

Modified test/continuity.lean




## [2020-07-27 06:09:20](https://github.com/leanprover-community/mathlib/commit/4c0881e)
feat(measure_theory/measure_space): several lemmas about `restrict` ([#3574](https://github.com/leanprover-community/mathlib/pull/3574))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.ae_eq_bot
- \+ *lemma* measure_theory.ae_restrict_eq_bot
- \+ *lemma* measure_theory.ae_restrict_ne_bot
- \+ *lemma* measure_theory.measure.measure_univ_eq_zero
- \+ *lemma* measure_theory.measure.restrict_add_restrict_compl
- \+ *lemma* measure_theory.measure.restrict_apply_univ
- \+ *lemma* measure_theory.measure.restrict_compl_add_restrict
- \+ *lemma* measure_theory.measure.restrict_eq_zero
- \+ *lemma* measure_theory.measure.restrict_le_self



## [2020-07-27 04:33:38](https://github.com/leanprover-community/mathlib/commit/d5d463e)
chore(topology/subset_properties): +2 lemmas about `is_compact` ([#3567](https://github.com/leanprover-community/mathlib/pull/3567))
Also use `variables {s t : set α}`
#### Estimated changes
Modified src/topology/subset_properties.lean
- \+/\- *lemma* cluster_point_of_compact
- \+/\- *lemma* compact_diff
- \+/\- *lemma* compact_iff_finite_subcover
- \+/\- *theorem* compact_iff_finite_subfamily_closed
- \+/\- *lemma* compact_iff_ultrafilter_le_nhds
- \+/\- *lemma* compact_of_finite_subcover
- \+/\- *theorem* compact_of_finite_subfamily_closed
- \+/\- *lemma* compact_of_is_closed_subset
- \+/\- *lemma* compact_univ_pi
- \+/\- *lemma* embedding.compact_iff_compact_image
- \+/\- *lemma* is_compact.adherence_nhdset
- \+ *lemma* is_compact.compl_mem_sets
- \+ *lemma* is_compact.compl_mem_sets_of_nhds_within
- \+/\- *lemma* is_compact.elim_finite_subcover
- \+/\- *lemma* is_compact.elim_finite_subcover_image
- \+/\- *lemma* is_compact.image
- \+/\- *lemma* is_compact.image_of_continuous_on
- \+/\- *lemma* is_compact.inter_left
- \+/\- *lemma* is_compact.inter_right
- \+/\- *lemma* is_compact.union
- \+/\- *lemma* set.finite.is_compact



## [2020-07-27 03:38:45](https://github.com/leanprover-community/mathlib/commit/8673f23)
chore(data/finsupp): move into finsupp folder ([#3566](https://github.com/leanprover-community/mathlib/pull/3566))
#### Estimated changes
Renamed src/data/finsupp.lean to src/data/finsupp/basic.lean


Added src/data/finsupp/default.lean


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
- \+/\- *lemma* filter.principal_empty
- \+/\- *lemma* filter.principal_univ

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
- \+ *lemma* times_cont_diff.comp_times_cont_diff_within_at
- \+ *lemma* times_cont_diff.sum
- \+ *lemma* times_cont_diff.times_cont_diff_within_at
- \+ *lemma* times_cont_diff_at.add
- \+ *lemma* times_cont_diff_at.neg
- \+ *lemma* times_cont_diff_at.sub
- \+ *lemma* times_cont_diff_at.sum
- \+ *lemma* times_cont_diff_on.sum
- \+ *lemma* times_cont_diff_within_at.add
- \+ *lemma* times_cont_diff_within_at.neg
- \+ *lemma* times_cont_diff_within_at.sub
- \+ *lemma* times_cont_diff_within_at.sum

Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/hausdorff_distance.lean




## [2020-07-27 00:02:05](https://github.com/leanprover-community/mathlib/commit/ca6cebc)
feat(data/nat/digits): add `last_digit_ne_zero` ([#3544](https://github.com/leanprover-community/mathlib/pull/3544))
The proof of `base_pow_length_digits_le` was refactored as suggested by @fpvandoorn in [#3498](https://github.com/leanprover-community/mathlib/pull/3498).
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.last_repeat_succ

Modified src/data/nat/digits.lean
- \+/\- *lemma* base_pow_length_digits_le'
- \+ *lemma* digits_eq_nil_iff_eq_zero
- \+ *lemma* digits_last
- \+ *lemma* digits_ne_nil_iff_ne_zero
- \+ *lemma* last_digit_ne_zero
- \+ *lemma* of_digits_singleton
- \+ *lemma* pow_length_le_mul_of_digits



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
- \+ *lemma* set.Ici_diff_Ici
- \+ *lemma* set.Ici_diff_Ioi
- \+ *lemma* set.Iic_diff_Iic
- \+ *lemma* set.Iic_diff_Iio
- \+ *lemma* set.Iio_diff_Iic
- \+ *lemma* set.Iio_diff_Iio
- \+ *lemma* set.Ioi_diff_Ici
- \+ *lemma* set.Ioi_diff_Ioi
- \+/\- *lemma* set.compl_Ici
- \+/\- *lemma* set.compl_Iic
- \+/\- *lemma* set.compl_Iio
- \+/\- *lemma* set.compl_Ioi



## [2020-07-26 14:16:23](https://github.com/leanprover-community/mathlib/commit/692a689)
feat(data/list/chain): chain'.append_overlap ([#3559](https://github.com/leanprover-community/mathlib/pull/3559))
#### Estimated changes
Modified src/data/list/chain.lean
- \+ *lemma* list.chain'.append_overlap



## [2020-07-26 10:41:56](https://github.com/leanprover-community/mathlib/commit/f4106af)
feat(order/filters, topology): relation between neighborhoods of a in [a, u), [a, u] and [a,+inf) + various nhds_within lemmas ([#3516](https://github.com/leanprover-community/mathlib/pull/3516))
Content : 
- two lemmas about filters, namely `tendsto_sup` and `eventually_eq_inf_principal_iff`
- a few lemmas about `nhds_within`
- duplicate and move parts of the lemmas `tfae_mem_nhds_within_[Ioi/Iio/Ici/Iic]` that only require `order_closed_topology α` instead of `order_topology α`. This allows to turn any left/right neighborhood of `a` into its "canonical" form (i.e `Ioi`/`Iio`/`Ici`/`Iic`) with a weaker assumption than before
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_eq_inf_principal_iff
- \+ *lemma* filter.tendsto.sup
- \+ *lemma* filter.tendsto_sup

Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous_within_at_Icc_iff_Ici
- \+ *lemma* continuous_within_at_Icc_iff_Iic
- \+ *lemma* continuous_within_at_Ico_iff_Ici
- \+ *lemma* continuous_within_at_Ico_iff_Iio
- \+ *lemma* continuous_within_at_Ioc_iff_Iic
- \+ *lemma* continuous_within_at_Ioc_iff_Ioi
- \+ *lemma* continuous_within_at_Ioo_iff_Iio
- \+ *lemma* continuous_within_at_Ioo_iff_Ioi
- \+ *lemma* tfae_mem_nhds_within_Ici'
- \+ *lemma* tfae_mem_nhds_within_Iic'
- \+ *lemma* tfae_mem_nhds_within_Iio'
- \+ *lemma* tfae_mem_nhds_within_Ioi'

Modified src/topology/continuous_on.lean
- \+ *lemma* eventually_eq_nhds_within_iff
- \+ *lemma* eventually_eq_nhds_within_of_eq_on
- \+ *lemma* eventually_nhds_with_of_forall
- \+ *lemma* set.eq_on.eventually_eq_nhds_within
- \+ *lemma* tendsto_nhds_within_congr
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
- \+ *theorem* filter.has_basis.Limsup_eq_infi_Sup
- \+ *lemma* filter.is_bounded.is_bounded_under
- \+ *lemma* filter.is_bounded.is_cobounded_flip
- \+ *lemma* filter.is_bounded.mono
- \- *lemma* filter.is_bounded_of_le
- \- *lemma* filter.is_bounded_under_of_is_bounded
- \+ *lemma* filter.is_cobounded.mono
- \- *lemma* filter.is_cobounded_of_is_bounded
- \- *lemma* filter.is_cobounded_of_le

Modified src/topology/algebra/ordered.lean
- \+ *lemma* filter.tendsto.is_bounded_under_ge
- \+ *lemma* filter.tendsto.is_bounded_under_le
- \+ *lemma* filter.tendsto.is_cobounded_under_ge
- \+ *lemma* filter.tendsto.is_cobounded_under_le
- \- *lemma* is_bounded_under_ge_of_tendsto
- \- *lemma* is_bounded_under_le_of_tendsto
- \- *lemma* is_cobounded_under_ge_of_tendsto
- \- *lemma* is_cobounded_under_le_of_tendsto



## [2020-07-26 09:05:46](https://github.com/leanprover-community/mathlib/commit/493a5b0)
feat(data/set/lattice): add lemmas `disjoint.union_left/right` etc ([#3554](https://github.com/leanprover-community/mathlib/pull/3554))
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *theorem* set.disjoint.union_left
- \+ *theorem* set.disjoint.union_right
- \+ *theorem* set.disjoint_union_left
- \+ *theorem* set.disjoint_union_right

Modified src/order/bounded_lattice.lean
- \+ *lemma* disjoint.sup_left
- \+ *lemma* disjoint.sup_right
- \+ *lemma* disjoint_sup_left
- \+ *lemma* disjoint_sup_right



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
- \- *lemma* continuous_multilinear_map.norm_zero

Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* continuous_linear_map.norm_zero

Modified src/measure_theory/bochner_integration.lean




## [2020-07-26 02:39:04](https://github.com/leanprover-community/mathlib/commit/11179d5)
feat(algebra/category/Group/*): compare categorical (co)kernels/images with the usual notions ([#3443](https://github.com/leanprover-community/mathlib/pull/3443))
#### Estimated changes
Modified src/algebra/category/Group/colimits.lean
- \+ *def* AddCommGroup.cokernel_iso_quotient

Modified src/algebra/category/Group/images.lean
- \+ *def* AddCommGroup.image_iso_range

Modified src/algebra/category/Group/limits.lean
- \+ *def* AddCommGroup.kernel_iso_ker
- \+ *lemma* AddCommGroup.kernel_iso_ker_hom_comp_subtype
- \+ *lemma* AddCommGroup.kernel_iso_ker_inv_comp_ι
- \+ *def* AddCommGroup.kernel_iso_ker_over

Modified src/category_theory/limits/concrete_category.lean


Added src/category_theory/limits/shapes/concrete_category.lean
- \+ *lemma* category_theory.limits.cokernel_condition_apply
- \+ *lemma* category_theory.limits.kernel_condition_apply



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
- \+/\- *lemma* dvd_iff_dvd_of_dvd_sub
- \+/\- *lemma* dvd_mul_sub_mul
- \+ *theorem* two_dvd_bit0
- \+ *theorem* two_dvd_bit1

Modified src/data/nat/basic.lean


Modified src/data/num/lemmas.lean
- \+ *theorem* pos_num.dvd_to_nat

Added src/data/num/prime.lean
- \+ *def* num.min_fac
- \+ *theorem* num.min_fac_to_nat
- \+ *def* num.prime
- \+ *def* pos_num.min_fac
- \+ *def* pos_num.min_fac_aux
- \+ *theorem* pos_num.min_fac_aux_to_nat
- \+ *theorem* pos_num.min_fac_to_nat
- \+ *def* pos_num.prime



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
- \+ *lemma* tangent_map_id
- \+ *lemma* tangent_map_within_congr
- \+ *lemma* tangent_map_within_id

Modified src/geometry/manifold/real_instances.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* embedding.continuous_on_iff
- \+ *lemma* inducing.continuous_on_iff

Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph.homeomorph_mk_coe
- \+ *lemma* homeomorph.homeomorph_mk_coe_symm

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.is_closed_sphere



## [2020-07-25 06:33:02](https://github.com/leanprover-community/mathlib/commit/12a7ce3)
feat(category_theory/isomorphism): lemmas about cancelling isomorphisms ([#3436](https://github.com/leanprover-community/mathlib/pull/3436))
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+ *lemma* category_theory.equivalence.cancel_counit_inv_right
- \+ *lemma* category_theory.equivalence.cancel_counit_inv_right_assoc'
- \+ *lemma* category_theory.equivalence.cancel_counit_inv_right_assoc
- \+ *lemma* category_theory.equivalence.cancel_counit_right
- \+ *lemma* category_theory.equivalence.cancel_unit_inv_right
- \+ *lemma* category_theory.equivalence.cancel_unit_right
- \+ *lemma* category_theory.equivalence.cancel_unit_right_assoc'
- \+ *lemma* category_theory.equivalence.cancel_unit_right_assoc

Modified src/category_theory/isomorphism.lean
- \+ *lemma* category_theory.iso.cancel_iso_hom_left
- \+ *lemma* category_theory.iso.cancel_iso_hom_right
- \+ *lemma* category_theory.iso.cancel_iso_hom_right_assoc
- \+ *lemma* category_theory.iso.cancel_iso_inv_left
- \+ *lemma* category_theory.iso.cancel_iso_inv_right
- \+ *lemma* category_theory.iso.cancel_iso_inv_right_assoc

Modified src/category_theory/natural_isomorphism.lean
- \+ *lemma* category_theory.nat_iso.cancel_nat_iso_hom_left
- \+ *lemma* category_theory.nat_iso.cancel_nat_iso_hom_right
- \+ *lemma* category_theory.nat_iso.cancel_nat_iso_hom_right_assoc
- \+ *lemma* category_theory.nat_iso.cancel_nat_iso_inv_left
- \+ *lemma* category_theory.nat_iso.cancel_nat_iso_inv_right
- \+ *lemma* category_theory.nat_iso.cancel_nat_iso_inv_right_assoc



## [2020-07-25 05:30:35](https://github.com/leanprover-community/mathlib/commit/2d29f80)
feat(data/finsupp): lattice structure on finsupp ([#3335](https://github.com/leanprover-community/mathlib/pull/3335))
adds facts about order_isos respecting lattice operations
defines lattice structures on finsupps to N
constructs an order_iso out of finsupp.to_multiset
#### Estimated changes
Modified src/algebra/ordered_group.lean


Added src/data/finsupp/lattice.lean
- \+ *lemma* finsupp.bot_eq_zero
- \+ *lemma* finsupp.disjoint_iff
- \+ *lemma* finsupp.inf_apply
- \+ *lemma* finsupp.le_def
- \+ *lemma* finsupp.monotone_to_fun
- \+ *lemma* finsupp.of_multiset_strict_mono
- \+ *def* finsupp.order_embedding_to_fun
- \+ *lemma* finsupp.order_embedding_to_fun_apply
- \+ *def* finsupp.order_iso_multiset
- \+ *lemma* finsupp.order_iso_multiset_apply
- \+ *lemma* finsupp.order_iso_multiset_symm_apply
- \+ *lemma* finsupp.sup_apply
- \+ *lemma* finsupp.support_inf
- \+ *lemma* finsupp.support_sup



## [2020-07-25 04:26:19](https://github.com/leanprover-community/mathlib/commit/8d55eda)
feat(topology/tactic): `continuity` tactic ([#2879](https://github.com/leanprover-community/mathlib/pull/2879))
#### Estimated changes
Modified docs/tutorial/category_theory/calculating_colimits_in_Top.lean
- \+/\- *def* f

Modified src/analysis/analytic/basic.lean


Modified src/analysis/normed_space/banach.lean


Modified src/data/complex/exponential.lean
- \+/\- *lemma* real.exp_monotone

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
- \+/\- *lemma* continuous.prod_mk
- \+/\- *lemma* continuous_fst
- \+/\- *lemma* continuous_inl
- \+/\- *lemma* continuous_inr
- \+/\- *lemma* continuous_quot_lift
- \+/\- *lemma* continuous_quot_mk
- \+/\- *lemma* continuous_snd
- \+/\- *lemma* continuous_subtype_mk
- \+/\- *lemma* continuous_subtype_val
- \+/\- *lemma* continuous_sum_rec
- \+/\- *lemma* continuous_ulift_down
- \+/\- *lemma* continuous_ulift_up

Modified src/topology/continuous_map.lean
- \+/\- *def* continuous_map.const
- \+/\- *def* continuous_map.id

Modified src/topology/homeomorph.lean


Modified src/topology/order.lean
- \+/\- *lemma* continuous_bot
- \+/\- *lemma* continuous_top

Added src/topology/tactic.lean


Added test/continuity.lean




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
- \+/\- *def* category_theory.prod.associator
- \+/\- *def* category_theory.prod.inverse_associator

Modified src/category_theory/products/basic.lean
- \+/\- *def* category_theory.evaluation_uncurried
- \+/\- *def* category_theory.functor.prod
- \+/\- *def* category_theory.nat_trans.prod
- \+/\- *def* category_theory.prod.fst
- \+/\- *def* category_theory.prod.sectl
- \+/\- *def* category_theory.prod.sectr
- \+/\- *def* category_theory.prod.snd
- \+/\- *def* category_theory.prod.swap
- \+/\- *def* category_theory.prod.symmetry

Modified src/meta/expr.lean


Modified src/tactic/core.lean


Modified src/tactic/simps.lean


Modified test/simps.lean
- \+ *def* coercing.Group.prod_Semigroup
- \+ *structure* coercing.Semigroup
- \+ *def* coercing.bar
- \+ *structure* coercing.equiv2
- \+ *def* coercing.foo2
- \+ *def* coercing.foo
- \+ *structure* coercing.foo_str
- \+ *def* coercing.new_bar
- \+ *def* coercing.voo2
- \+ *def* coercing.voo
- \+ *structure* coercing.voo_str
- \- *def* count_nested.nested1
- \- *def* count_nested.nested2
- \+ *def* equiv.trans
- \+ *structure* failty_manual_coercion.equiv
- \+ *def* foo.rfl2
- \+ *def* foo.rfl3
- \+ *def* manual_coercion.equiv.simps.inv_fun
- \+ *def* manual_coercion.equiv.symm
- \+ *structure* manual_coercion.equiv
- \+ *def* manual_initialize.equiv.simps.inv_fun
- \+ *def* manual_initialize.equiv.symm
- \+ *structure* manual_initialize.equiv
- \+ *def* my_nat_equiv
- \+ *structure* my_prod
- \+ *def* myprod.map
- \+ *def* nat_set_plus2
- \+ *def* nat_set_plus3
- \+ *def* nat_set_plus
- \+ *def* nested_non_fully_applied.equiv.symm2
- \+ *def* nested_non_fully_applied.equiv.symm3
- \+ *def* nested_non_fully_applied.equiv.symm
- \+ *structure* nested_non_fully_applied.equiv
- \+/\- *def* partially_applied_term
- \+ *def* pprod_equiv_prod
- \+ *structure* set_plus
- \+/\- *def* short_name1
- \+ *def* succeed_without_simplification_possible
- \+ *def* test_sneaky
- \+/\- *def* very_partially_applied_term

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
- \+ *lemma* algebraic_geometry.PresheafedSpace.comp_base
- \- *lemma* algebraic_geometry.PresheafedSpace.comp_coe
- \- *lemma* algebraic_geometry.PresheafedSpace.f_as_coe
- \- *lemma* algebraic_geometry.PresheafedSpace.hom_mk_coe
- \+ *lemma* algebraic_geometry.PresheafedSpace.id_base
- \- *lemma* algebraic_geometry.PresheafedSpace.id_coe
- \- *lemma* algebraic_geometry.PresheafedSpace.id_coe_fn

Modified src/algebraic_geometry/stalks.lean
- \+/\- *def* algebraic_geometry.PresheafedSpace.stalk_map



## [2020-07-24 13:04:01](https://github.com/leanprover-community/mathlib/commit/229cf6e)
feat(data/polynomial): irreducible_of_irreducible_mod_prime ([#3539](https://github.com/leanprover-community/mathlib/pull/3539))
I was waiting on this, an exercise from Johan's tutorial at LftCM, to see if a participant would PR it. Perhaps not, so I'll contribute this now.
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.irreducible_of_irreducible_map
- \+ *lemma* polynomial.is_unit_of_is_unit_leading_coeff_of_is_unit_map



## [2020-07-24 13:03:59](https://github.com/leanprover-community/mathlib/commit/579b142)
feat(field_theory/fixed): a field is normal over the fixed subfield under a group action ([#3520](https://github.com/leanprover-community/mathlib/pull/3520))
From my Galois theory repo.
#### Estimated changes
Modified src/algebra/group_action_hom.lean
- \+ *theorem* is_invariant_subring.coe_subtype_hom'
- \+ *theorem* is_invariant_subring.coe_subtype_hom
- \+ *def* is_invariant_subring.subtype_hom
- \+ *theorem* mul_semiring_action_hom.coe_polynomial

Modified src/algebra/group_ring_action.lean
- \+ *lemma* list.smul_prod
- \+ *lemma* multiset.smul_prod
- \+/\- *lemma* polynomial.coeff_smul'
- \+ *theorem* polynomial.eval_smul'
- \+/\- *lemma* polynomial.smul_C
- \+/\- *lemma* polynomial.smul_X
- \+ *theorem* polynomial.smul_eval
- \+ *theorem* polynomial.smul_eval_smul
- \+ *theorem* prod_X_sub_smul.coeff
- \+ *theorem* prod_X_sub_smul.eval
- \+ *theorem* prod_X_sub_smul.monic
- \+ *theorem* prod_X_sub_smul.smul
- \+ *lemma* smul_prod

Modified src/algebra/module/basic.lean
- \- *theorem* smul_neg
- \- *theorem* smul_sub

Modified src/data/polynomial/div.lean
- \+ *theorem* polynomial.map_dvd_map

Modified src/data/polynomial/field_division.lean
- \+ *theorem* polynomial.irreducible_of_monic
- \+ *theorem* polynomial.map_dvd_map'

Modified src/data/polynomial/ring_division.lean
- \+ *theorem* polynomial.eq_of_monic_of_associated

Added src/field_theory/fixed.lean
- \+ *theorem* fixed_points.coe_algebra_map
- \+ *theorem* fixed_points.is_integral
- \+ *theorem* fixed_points.minpoly.eval₂
- \+ *theorem* fixed_points.minpoly.irreducible
- \+ *theorem* fixed_points.minpoly.irreducible_aux
- \+ *theorem* fixed_points.minpoly.minimal_polynomial
- \+ *theorem* fixed_points.minpoly.monic
- \+ *theorem* fixed_points.minpoly.ne_one
- \+ *def* fixed_points.minpoly
- \+ *theorem* fixed_points.of_eval₂
- \+ *theorem* fixed_points.smul
- \+ *theorem* fixed_points.smul_polynomial

Modified src/field_theory/minimal_polynomial.lean
- \+ *theorem* minimal_polynomial.unique'

Added src/field_theory/normal.lean
- \+ *theorem* normal.exists_is_splitting_field
- \+ *theorem* normal.is_integral
- \+ *theorem* normal.splits
- \+ *def* normal

Modified src/group_theory/group_action.lean
- \+ *def* mul_action.fixed_by
- \+ *theorem* mul_action.fixed_eq_Inter_fixed_by
- \+/\- *def* mul_action.fixed_points
- \+ *theorem* mul_action.injective_of_quotient_stabilizer
- \+ *lemma* mul_action.mem_fixed_by
- \+ *def* mul_action.of_quotient_stabilizer
- \+ *theorem* mul_action.of_quotient_stabilizer_mem_orbit
- \+ *theorem* mul_action.of_quotient_stabilizer_mk
- \+ *theorem* mul_action.of_quotient_stabilizer_smul
- \+ *theorem* smul_neg
- \+ *theorem* smul_sub

Modified src/ring_theory/algebra.lean
- \+ *theorem* algebra.coe_top

Modified src/ring_theory/polynomial/basic.lean
- \+ *theorem* polynomial.map_to_subring



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
Added src/analysis/normed_space/indicator_function.lean
- \+ *lemma* indicator_norm_le_norm_self
- \+ *lemma* norm_indicator_eq_indicator_norm
- \+ *lemma* norm_indicator_le_norm_self
- \+ *lemma* norm_indicator_le_of_subset

Modified src/data/indicator_function.lean
- \+ *lemma* set.indicator_rel_indicator

Deleted src/measure_theory/indicator_function.lean
- \- *lemma* indicator_congr_ae
- \- *lemma* indicator_congr_of_set
- \- *lemma* indicator_le_indicator_ae
- \- *lemma* indicator_norm_le_norm_self
- \- *lemma* indicator_union_ae
- \- *lemma* norm_indicator_eq_indicator_norm
- \- *lemma* norm_indicator_le_norm_self
- \- *lemma* norm_indicator_le_of_subset
- \- *lemma* tendsto_indicator_bUnion_finset
- \- *lemma* tendsto_indicator_of_antimono
- \- *lemma* tendsto_indicator_of_monotone

Modified src/measure_theory/set_integral.lean


Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_eq.mem_iff
- \+ *lemma* filter.eventually_set_ext

Added src/order/filter/indicator_function.lean
- \+ *lemma* indicator_eventually_eq
- \+ *lemma* indicator_eventually_le_indicator
- \+ *lemma* indicator_union_eventually_eq
- \+ *lemma* tendsto_indicator_bUnion_finset
- \+ *lemma* tendsto_indicator_of_antimono
- \+ *lemma* tendsto_indicator_of_monotone



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
- \+ *lemma* equiv.coe_plift
- \+ *lemma* equiv.coe_plift_symm
- \+ *lemma* equiv.coe_ulift
- \+ *lemma* equiv.coe_ulift_symm

Modified src/data/finset/lattice.lean
- \+ *lemma* infi_eq_infi_finset'
- \+ *lemma* set.Inter_eq_Inter_finset'
- \+ *lemma* set.Union_eq_Union_finset'
- \+ *lemma* supr_eq_supr_finset'

Modified src/data/set/basic.lean
- \+/\- *lemma* function.surjective.range_comp

Modified src/linear_algebra/basis.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* function.surjective.infi_comp
- \+ *lemma* function.surjective.supr_comp
- \- *lemma* infi_congr
- \- *lemma* supr_congr

Modified src/order/filter/basic.lean
- \+ *lemma* filter.infi_sets_eq_finite'
- \+/\- *lemma* filter.infi_sets_eq_finite
- \+ *lemma* filter.mem_infi_finite'
- \+/\- *lemma* filter.mem_infi_finite

Modified src/set_theory/ordinal.lean




## [2020-07-24 08:19:54](https://github.com/leanprover-community/mathlib/commit/499cb9b)
refactor(data/nat/digits): refactor into sections ([#3527](https://github.com/leanprover-community/mathlib/pull/3527))
Refactor `data.nat.digits` into sections and grouping similar lemmas together.
#### Estimated changes
Modified src/data/nat/digits.lean




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
- \+/\- *def* direct_sum.mk
- \+/\- *def* direct_sum.of
- \+/\- *theorem* direct_sum.to_group.unique
- \+/\- *def* direct_sum.to_group

Modified src/linear_algebra/direct_sum/tensor_product.lean


Modified src/linear_algebra/direct_sum_module.lean
- \+/\- *lemma* direct_sum.apply_eq_component
- \+/\- *def* direct_sum.component
- \+/\- *lemma* direct_sum.ext
- \+/\- *lemma* direct_sum.ext_iff
- \+/\- *def* direct_sum.lmk
- \+/\- *def* direct_sum.lof
- \+/\- *theorem* direct_sum.to_module.ext
- \+/\- *theorem* direct_sum.to_module.unique
- \+/\- *def* direct_sum.to_module



## [2020-07-23 19:52:19](https://github.com/leanprover-community/mathlib/commit/289d17c)
chore(data/equiv/basic): avoid `λ ⟨a, b⟩` in some defs, add `simp` lemmas ([#3530](https://github.com/leanprover-community/mathlib/pull/3530))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.psigma_equiv_sigma_apply
- \+ *lemma* equiv.psigma_equiv_sigma_symm_apply
- \+/\- *def* equiv.sigma_congr_left
- \+ *lemma* equiv.sigma_congr_left_apply
- \+ *lemma* equiv.sigma_congr_right_apply
- \+ *lemma* equiv.sigma_congr_right_symm_apply
- \+/\- *def* equiv.sigma_equiv_prod
- \+ *lemma* equiv.sigma_equiv_prod_apply
- \+/\- *def* equiv.sigma_equiv_prod_of_equiv
- \+ *lemma* equiv.sigma_equiv_prod_symm_apply



## [2020-07-23 18:29:16](https://github.com/leanprover-community/mathlib/commit/2d395a9)
refactor(algebra/pi_instance): delete pi_instance file, and move instances to group/ring etc appropriately ([#3513](https://github.com/leanprover-community/mathlib/pull/3513))
#### Estimated changes
Modified src/algebra/add_torsor.lean


Added src/algebra/big_operators/pi.lean
- \+ *lemma* add_monoid_hom.functions_ext
- \+ *lemma* finset.prod_apply
- \+ *lemma* finset.univ_sum_single
- \+ *lemma* pi.list_prod_apply
- \+ *lemma* pi.multiset_prod_apply
- \+ *lemma* prod.fst_prod
- \+ *lemma* prod.snd_prod
- \+ *lemma* prod_mk_prod
- \+ *lemma* ring_hom.functions_ext

Modified src/algebra/category/CommRing/limits.lean


Modified src/algebra/category/Group/biproducts.lean


Modified src/algebra/category/Group/limits.lean


Modified src/algebra/char_p.lean


Modified src/algebra/default.lean


Modified src/algebra/field.lean


Added src/algebra/group/pi.lean
- \+ *def* add_monoid_hom.single
- \+ *lemma* add_monoid_hom.single_apply
- \+ *def* monoid_hom.apply
- \+ *lemma* monoid_hom.apply_apply
- \+ *lemma* pi.inv_apply
- \+ *lemma* pi.mul_apply
- \+ *lemma* pi.one_apply
- \+ *def* pi.single
- \+ *lemma* pi.single_eq_of_ne
- \+ *lemma* pi.single_eq_same
- \+ *lemma* pi.sub_apply

Modified src/algebra/group/with_one.lean


Modified src/algebra/midpoint.lean


Renamed src/algebra/module.lean to src/algebra/module/basic.lean


Added src/algebra/module/default.lean


Added src/algebra/module/pi.lean
- \+ *lemma* pi.smul_apply'
- \+ *lemma* pi.smul_apply

Added src/algebra/module/prod.lean
- \+ *theorem* prod.smul_fst
- \+ *theorem* prod.smul_mk
- \+ *theorem* prod.smul_snd

Deleted src/algebra/pi_instances.lean
- \- *lemma* add_monoid_hom.functions_ext
- \- *def* add_monoid_hom.single
- \- *lemma* add_monoid_hom.single_apply
- \- *lemma* finset.prod_apply
- \- *lemma* finset.prod_mk_prod
- \- *lemma* finset.univ_sum_single
- \- *def* monoid_hom.apply
- \- *lemma* monoid_hom.apply_apply
- \- *lemma* pi.finset_prod_apply
- \- *lemma* pi.inv_apply
- \- *lemma* pi.list_prod_apply
- \- *lemma* pi.mul_apply
- \- *lemma* pi.multiset_prod_apply
- \- *lemma* pi.one_apply
- \- *def* pi.single
- \- *lemma* pi.single_eq_of_ne
- \- *lemma* pi.single_eq_same
- \- *lemma* pi.smul_apply'
- \- *lemma* pi.smul_apply
- \- *lemma* pi.sub_apply
- \- *lemma* prod.fst.is_group_hom
- \- *lemma* prod.fst.is_monoid_hom
- \- *lemma* prod.fst_inl
- \- *lemma* prod.fst_inr
- \- *lemma* prod.fst_prod
- \- *def* prod.inl
- \- *lemma* prod.inl_eq_inl
- \- *lemma* prod.inl_eq_inr
- \- *lemma* prod.inl_injective
- \- *def* prod.inr
- \- *lemma* prod.inr_eq_inl
- \- *lemma* prod.inr_eq_inr
- \- *lemma* prod.inr_injective
- \- *theorem* prod.smul_fst
- \- *theorem* prod.smul_mk
- \- *theorem* prod.smul_snd
- \- *lemma* prod.snd.is_group_hom
- \- *lemma* prod.snd.is_monoid_hom
- \- *lemma* prod.snd_inl
- \- *lemma* prod.snd_inr
- \- *lemma* prod.snd_prod
- \- *def* ring_hom.apply
- \- *lemma* ring_hom.apply_apply
- \- *lemma* ring_hom.functions_ext

Modified src/algebra/pointwise.lean


Modified src/algebra/punit_instances.lean


Renamed src/algebra/ring.lean to src/algebra/ring/basic.lean


Added src/algebra/ring/default.lean


Added src/algebra/ring/pi.lean
- \+ *def* ring_hom.apply
- \+ *lemma* ring_hom.apply_apply

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
- \+/\- *def* linear_map.inl
- \+ *theorem* linear_map.inl_injective
- \+/\- *def* linear_map.inr
- \+ *theorem* linear_map.inr_injective

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
- \+ *lemma* measure_theory.integral_zero_meas

Modified src/measure_theory/l1_space.lean
- \+/\- *def* measure_theory.integrable

Modified src/measure_theory/measure_space.lean




## [2020-07-23 13:44:07](https://github.com/leanprover-community/mathlib/commit/396a66a)
chore(order/filter/*): use `[nonempty _]` instead of `(_ : nonempty _)` ([#3526](https://github.com/leanprover-community/mathlib/pull/3526))
In most cases Lean can find an instance automatically.
#### Estimated changes
Modified src/order/basic.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* filter.at_top_basis

Modified src/order/filter/bases.lean
- \+/\- *lemma* filter.has_basis_generate
- \+/\- *lemma* filter.has_basis_infi_principal

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.infi_ne_bot_of_directed'
- \+/\- *lemma* filter.infi_sets_eq
- \+/\- *lemma* filter.map_infi_eq
- \+/\- *lemma* filter.mem_infi

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


Added src/set_theory/cardinal_ordinal.lean
- \+ *lemma* cardinal.add_eq_left
- \+ *lemma* cardinal.add_eq_left_iff
- \+ *theorem* cardinal.add_eq_max
- \+ *lemma* cardinal.add_eq_right
- \+ *lemma* cardinal.add_eq_right_iff
- \+ *theorem* cardinal.add_eq_self
- \+ *theorem* cardinal.add_lt_of_lt
- \+ *lemma* cardinal.add_one_eq
- \+ *def* cardinal.aleph'.order_iso
- \+ *theorem* cardinal.aleph'.order_iso_coe
- \+ *def* cardinal.aleph'
- \+ *theorem* cardinal.aleph'_aleph_idx
- \+ *def* cardinal.aleph'_equiv
- \+ *theorem* cardinal.aleph'_is_normal
- \+ *theorem* cardinal.aleph'_le
- \+ *theorem* cardinal.aleph'_le_of_limit
- \+ *theorem* cardinal.aleph'_lt
- \+ *theorem* cardinal.aleph'_nat
- \+ *theorem* cardinal.aleph'_omega
- \+ *theorem* cardinal.aleph'_succ
- \+ *theorem* cardinal.aleph'_zero
- \+ *def* cardinal.aleph
- \+ *theorem* cardinal.aleph_idx.init
- \+ *def* cardinal.aleph_idx.initial_seg
- \+ *theorem* cardinal.aleph_idx.initial_seg_coe
- \+ *def* cardinal.aleph_idx.order_iso
- \+ *theorem* cardinal.aleph_idx.order_iso_coe
- \+ *def* cardinal.aleph_idx
- \+ *theorem* cardinal.aleph_idx_aleph'
- \+ *theorem* cardinal.aleph_idx_le
- \+ *theorem* cardinal.aleph_idx_lt
- \+ *theorem* cardinal.aleph_is_normal
- \+ *theorem* cardinal.aleph_le
- \+ *theorem* cardinal.aleph_lt
- \+ *theorem* cardinal.aleph_succ
- \+ *theorem* cardinal.aleph_zero
- \+ *theorem* cardinal.bit0_eq_self
- \+ *lemma* cardinal.bit0_le_bit0
- \+ *lemma* cardinal.bit0_le_bit1
- \+ *lemma* cardinal.bit0_lt_bit0
- \+ *lemma* cardinal.bit0_lt_bit1
- \+ *theorem* cardinal.bit0_lt_omega
- \+ *lemma* cardinal.bit0_ne_zero
- \+ *theorem* cardinal.bit1_eq_self_iff
- \+ *lemma* cardinal.bit1_le_bit0
- \+ *lemma* cardinal.bit1_le_bit1
- \+ *lemma* cardinal.bit1_lt_bit0
- \+ *lemma* cardinal.bit1_lt_bit1
- \+ *theorem* cardinal.bit1_lt_omega
- \+ *lemma* cardinal.bit1_ne_zero
- \+ *lemma* cardinal.eq_of_add_eq_of_omega_le
- \+ *theorem* cardinal.exists_aleph
- \+ *theorem* cardinal.extend_function
- \+ *theorem* cardinal.extend_function_finite
- \+ *theorem* cardinal.extend_function_of_lt
- \+ *lemma* cardinal.le_mul_left
- \+ *lemma* cardinal.le_mul_right
- \+ *lemma* cardinal.mk_bounded_set_le
- \+ *lemma* cardinal.mk_bounded_set_le_of_omega_le
- \+ *lemma* cardinal.mk_bounded_subset_le
- \+ *theorem* cardinal.mk_cardinal
- \+ *lemma* cardinal.mk_compl_eq_mk_compl_finite
- \+ *lemma* cardinal.mk_compl_eq_mk_compl_finite_lift
- \+ *lemma* cardinal.mk_compl_eq_mk_compl_finite_same
- \+ *lemma* cardinal.mk_compl_eq_mk_compl_infinite
- \+ *lemma* cardinal.mk_compl_finset_of_omega_le
- \+ *lemma* cardinal.mk_compl_of_omega_le
- \+ *theorem* cardinal.mk_list_eq_mk
- \+ *lemma* cardinal.mul_eq_left
- \+ *lemma* cardinal.mul_eq_left_iff
- \+ *theorem* cardinal.mul_eq_max
- \+ *lemma* cardinal.mul_eq_max_of_omega_le_left
- \+ *lemma* cardinal.mul_eq_right
- \+ *theorem* cardinal.mul_eq_self
- \+ *lemma* cardinal.mul_le_max_of_omega_le_left
- \+ *theorem* cardinal.mul_lt_of_lt
- \+ *theorem* cardinal.omega_le_aleph'
- \+ *theorem* cardinal.omega_le_aleph
- \+ *theorem* cardinal.omega_le_bit0
- \+ *theorem* cardinal.omega_le_bit1
- \+ *lemma* cardinal.one_le_bit0
- \+ *lemma* cardinal.one_le_bit1
- \+ *lemma* cardinal.one_le_one
- \+ *lemma* cardinal.one_lt_bit0
- \+ *lemma* cardinal.one_lt_bit1
- \+ *lemma* cardinal.one_lt_two
- \+ *theorem* cardinal.ord_aleph_is_limit
- \+ *theorem* cardinal.ord_is_limit
- \+ *theorem* cardinal.pow_le
- \+ *lemma* cardinal.power_nat_le
- \+ *lemma* cardinal.power_self_eq
- \+ *lemma* cardinal.powerlt_omega
- \+ *lemma* cardinal.powerlt_omega_le
- \+ *theorem* cardinal.type_cardinal
- \+ *lemma* cardinal.zero_lt_bit0
- \+ *lemma* cardinal.zero_lt_bit1

Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal.lean
- \- *lemma* cardinal.add_eq_left
- \- *lemma* cardinal.add_eq_left_iff
- \- *theorem* cardinal.add_eq_max
- \- *lemma* cardinal.add_eq_right
- \- *lemma* cardinal.add_eq_right_iff
- \- *theorem* cardinal.add_eq_self
- \- *theorem* cardinal.add_lt_of_lt
- \- *lemma* cardinal.add_one_eq
- \- *theorem* cardinal.add_one_of_omega_le
- \- *def* cardinal.aleph'.order_iso
- \- *theorem* cardinal.aleph'.order_iso_coe
- \- *def* cardinal.aleph'
- \- *theorem* cardinal.aleph'_aleph_idx
- \- *def* cardinal.aleph'_equiv
- \- *theorem* cardinal.aleph'_is_normal
- \- *theorem* cardinal.aleph'_le
- \- *theorem* cardinal.aleph'_le_of_limit
- \- *theorem* cardinal.aleph'_lt
- \- *theorem* cardinal.aleph'_nat
- \- *theorem* cardinal.aleph'_omega
- \- *theorem* cardinal.aleph'_succ
- \- *theorem* cardinal.aleph'_zero
- \- *def* cardinal.aleph
- \- *theorem* cardinal.aleph_idx.init
- \- *def* cardinal.aleph_idx.initial_seg
- \- *theorem* cardinal.aleph_idx.initial_seg_coe
- \- *def* cardinal.aleph_idx.order_iso
- \- *theorem* cardinal.aleph_idx.order_iso_coe
- \- *def* cardinal.aleph_idx
- \- *theorem* cardinal.aleph_idx_aleph'
- \- *theorem* cardinal.aleph_idx_le
- \- *theorem* cardinal.aleph_idx_lt
- \- *theorem* cardinal.aleph_is_normal
- \- *theorem* cardinal.aleph_le
- \- *theorem* cardinal.aleph_lt
- \- *theorem* cardinal.aleph_succ
- \- *theorem* cardinal.aleph_zero
- \- *theorem* cardinal.bit0_eq_self
- \- *lemma* cardinal.bit0_le_bit0
- \- *lemma* cardinal.bit0_le_bit1
- \- *lemma* cardinal.bit0_lt_bit0
- \- *lemma* cardinal.bit0_lt_bit1
- \- *theorem* cardinal.bit0_lt_omega
- \- *lemma* cardinal.bit0_ne_zero
- \- *theorem* cardinal.bit1_eq_self_iff
- \- *lemma* cardinal.bit1_le_bit0
- \- *lemma* cardinal.bit1_le_bit1
- \- *lemma* cardinal.bit1_lt_bit0
- \- *lemma* cardinal.bit1_lt_bit1
- \- *theorem* cardinal.bit1_lt_omega
- \- *lemma* cardinal.bit1_ne_zero
- \- *lemma* cardinal.eq_of_add_eq_of_omega_le
- \- *theorem* cardinal.exists_aleph
- \- *theorem* cardinal.extend_function
- \- *theorem* cardinal.extend_function_finite
- \- *theorem* cardinal.extend_function_of_lt
- \- *lemma* cardinal.le_mul_left
- \- *lemma* cardinal.le_mul_right
- \- *lemma* cardinal.mk_bounded_set_le
- \- *lemma* cardinal.mk_bounded_set_le_of_omega_le
- \- *lemma* cardinal.mk_bounded_subset_le
- \- *theorem* cardinal.mk_cardinal
- \- *lemma* cardinal.mk_compl_eq_mk_compl_finite
- \- *lemma* cardinal.mk_compl_eq_mk_compl_finite_lift
- \- *lemma* cardinal.mk_compl_eq_mk_compl_finite_same
- \- *lemma* cardinal.mk_compl_eq_mk_compl_infinite
- \- *lemma* cardinal.mk_compl_finset_of_omega_le
- \- *lemma* cardinal.mk_compl_of_omega_le
- \- *theorem* cardinal.mk_list_eq_mk
- \- *lemma* cardinal.mul_eq_left
- \- *lemma* cardinal.mul_eq_left_iff
- \- *theorem* cardinal.mul_eq_max
- \- *lemma* cardinal.mul_eq_max_of_omega_le_left
- \- *lemma* cardinal.mul_eq_right
- \- *theorem* cardinal.mul_eq_self
- \- *lemma* cardinal.mul_le_max_of_omega_le_left
- \- *theorem* cardinal.mul_lt_of_lt
- \- *theorem* cardinal.omega_le_aleph'
- \- *theorem* cardinal.omega_le_aleph
- \- *theorem* cardinal.omega_le_bit0
- \- *theorem* cardinal.omega_le_bit1
- \- *lemma* cardinal.one_le_bit0
- \- *lemma* cardinal.one_le_bit1
- \- *lemma* cardinal.one_le_one
- \- *lemma* cardinal.one_lt_bit0
- \- *lemma* cardinal.one_lt_bit1
- \- *lemma* cardinal.one_lt_two
- \- *theorem* cardinal.ord_aleph_is_limit
- \- *theorem* cardinal.ord_is_limit
- \- *theorem* cardinal.ord_omega
- \- *theorem* cardinal.pow_le
- \- *lemma* cardinal.power_nat_le
- \- *lemma* cardinal.power_self_eq
- \- *lemma* cardinal.powerlt_omega
- \- *lemma* cardinal.powerlt_omega_le
- \- *theorem* cardinal.type_cardinal
- \- *lemma* cardinal.zero_lt_bit0
- \- *lemma* cardinal.zero_lt_bit1
- \- *def* ordinal.CNF
- \- *theorem* ordinal.CNF_aux
- \- *theorem* ordinal.CNF_foldr
- \- *theorem* ordinal.CNF_fst_le
- \- *theorem* ordinal.CNF_fst_le_log
- \- *theorem* ordinal.CNF_ne_zero
- \- *theorem* ordinal.CNF_pairwise
- \- *theorem* ordinal.CNF_pairwise_aux
- \- *theorem* ordinal.CNF_rec_ne_zero
- \- *theorem* ordinal.CNF_rec_zero
- \- *theorem* ordinal.CNF_snd_lt
- \- *theorem* ordinal.CNF_sorted
- \- *theorem* ordinal.CNF_zero
- \- *theorem* ordinal.add_absorp
- \- *theorem* ordinal.add_absorp_iff
- \- *theorem* ordinal.add_is_limit
- \- *theorem* ordinal.add_is_normal
- \- *theorem* ordinal.add_le_add_iff_left
- \- *theorem* ordinal.add_le_add_iff_right
- \- *theorem* ordinal.add_le_of_limit
- \- *theorem* ordinal.add_left_cancel
- \- *theorem* ordinal.add_lt_add_iff_left
- \- *theorem* ordinal.add_lt_omega
- \- *theorem* ordinal.add_lt_omega_power
- \- *theorem* ordinal.add_mul_limit
- \- *theorem* ordinal.add_mul_limit_aux
- \- *theorem* ordinal.add_mul_succ
- \- *theorem* ordinal.add_omega
- \- *theorem* ordinal.add_omega_power
- \- *theorem* ordinal.add_right_cancel
- \- *theorem* ordinal.add_sub_add_cancel
- \- *theorem* ordinal.add_sub_cancel
- \- *theorem* ordinal.add_sub_cancel_of_le
- \- *theorem* ordinal.add_succ
- \- *def* ordinal.bsup
- \- *theorem* ordinal.bsup_id
- \- *theorem* ordinal.bsup_le
- \- *theorem* ordinal.bsup_type
- \- *theorem* ordinal.card_eq_nat
- \- *theorem* ordinal.card_eq_zero
- \- *theorem* ordinal.card_le_nat
- \- *theorem* ordinal.card_lt_nat
- \- *theorem* ordinal.card_mul
- \- *theorem* ordinal.card_succ
- \- *def* ordinal.deriv
- \- *theorem* ordinal.deriv_is_normal
- \- *theorem* ordinal.deriv_limit
- \- *theorem* ordinal.deriv_succ
- \- *theorem* ordinal.deriv_zero
- \- *theorem* ordinal.div_add_mod
- \- *lemma* ordinal.div_def
- \- *theorem* ordinal.div_eq_zero_of_lt
- \- *theorem* ordinal.div_le
- \- *theorem* ordinal.div_le_of_le_mul
- \- *theorem* ordinal.div_lt
- \- *theorem* ordinal.div_mul_cancel
- \- *theorem* ordinal.div_one
- \- *theorem* ordinal.div_self
- \- *theorem* ordinal.div_zero
- \- *theorem* ordinal.dvd_add
- \- *theorem* ordinal.dvd_add_iff
- \- *theorem* ordinal.dvd_antisymm
- \- *theorem* ordinal.dvd_def
- \- *theorem* ordinal.dvd_mul
- \- *theorem* ordinal.dvd_mul_of_dvd
- \- *theorem* ordinal.dvd_trans
- \- *theorem* ordinal.dvd_zero
- \- *theorem* ordinal.fintype_card
- \- *lemma* ordinal.has_succ_of_is_limit
- \- *theorem* ordinal.is_limit.nat_lt
- \- *theorem* ordinal.is_limit.one_lt
- \- *theorem* ordinal.is_limit.pos
- \- *def* ordinal.is_limit
- \- *theorem* ordinal.is_limit_add_iff
- \- *theorem* ordinal.is_limit_iff_omega_dvd
- \- *theorem* ordinal.is_normal.bsup
- \- *theorem* ordinal.is_normal.bsup_eq
- \- *theorem* ordinal.is_normal.deriv_fp
- \- *theorem* ordinal.is_normal.fp_iff_deriv
- \- *theorem* ordinal.is_normal.inj
- \- *theorem* ordinal.is_normal.is_limit
- \- *theorem* ordinal.is_normal.le_iff
- \- *theorem* ordinal.is_normal.le_nfp
- \- *theorem* ordinal.is_normal.le_self
- \- *theorem* ordinal.is_normal.le_set'
- \- *theorem* ordinal.is_normal.le_set
- \- *theorem* ordinal.is_normal.limit_le
- \- *theorem* ordinal.is_normal.limit_lt
- \- *theorem* ordinal.is_normal.lt_iff
- \- *theorem* ordinal.is_normal.lt_nfp
- \- *theorem* ordinal.is_normal.nfp_fp
- \- *theorem* ordinal.is_normal.nfp_le
- \- *theorem* ordinal.is_normal.nfp_le_fp
- \- *theorem* ordinal.is_normal.refl
- \- *theorem* ordinal.is_normal.sup
- \- *theorem* ordinal.is_normal.trans
- \- *def* ordinal.is_normal
- \- *theorem* ordinal.iterate_le_nfp
- \- *theorem* ordinal.le_add_sub
- \- *theorem* ordinal.le_bsup
- \- *theorem* ordinal.le_div
- \- *theorem* ordinal.le_log
- \- *theorem* ordinal.le_nfp_self
- \- *theorem* ordinal.le_of_dvd
- \- *theorem* ordinal.le_of_mul_le_mul_left
- \- *theorem* ordinal.le_power_self
- \- *theorem* ordinal.le_succ_of_is_limit
- \- *theorem* ordinal.le_sup
- \- *theorem* ordinal.lift_add
- \- *theorem* ordinal.lift_is_limit
- \- *theorem* ordinal.lift_is_succ
- \- *theorem* ordinal.lift_mul
- \- *theorem* ordinal.lift_nat_cast
- \- *theorem* ordinal.lift_pred
- \- *theorem* ordinal.lift_succ
- \- *theorem* ordinal.lift_type_fin
- \- *theorem* ordinal.limit_le
- \- *def* ordinal.limit_rec_on
- \- *theorem* ordinal.limit_rec_on_limit
- \- *theorem* ordinal.limit_rec_on_succ
- \- *theorem* ordinal.limit_rec_on_zero
- \- *def* ordinal.log
- \- *theorem* ordinal.log_def
- \- *theorem* ordinal.log_le_log
- \- *theorem* ordinal.log_le_self
- \- *theorem* ordinal.log_lt
- \- *theorem* ordinal.log_not_one_lt
- \- *theorem* ordinal.log_zero
- \- *theorem* ordinal.lt_bsup
- \- *theorem* ordinal.lt_div
- \- *theorem* ordinal.lt_limit
- \- *theorem* ordinal.lt_mul_div_add
- \- *theorem* ordinal.lt_mul_of_limit
- \- *theorem* ordinal.lt_mul_succ_div
- \- *theorem* ordinal.lt_of_add_lt_add_right
- \- *theorem* ordinal.lt_omega
- \- *theorem* ordinal.lt_power_of_limit
- \- *theorem* ordinal.lt_power_succ_log
- \- *theorem* ordinal.lt_pred
- \- *theorem* ordinal.lt_sub
- \- *theorem* ordinal.lt_succ
- \- *theorem* ordinal.lt_sup
- \- *lemma* ordinal.mk_initial_seg
- \- *theorem* ordinal.mod_def
- \- *theorem* ordinal.mod_eq_of_lt
- \- *theorem* ordinal.mod_lt
- \- *theorem* ordinal.mod_one
- \- *theorem* ordinal.mod_self
- \- *theorem* ordinal.mod_zero
- \- *theorem* ordinal.mul_add
- \- *theorem* ordinal.mul_add_div
- \- *theorem* ordinal.mul_add_one
- \- *theorem* ordinal.mul_div_cancel
- \- *theorem* ordinal.mul_div_le
- \- *theorem* ordinal.mul_is_limit
- \- *theorem* ordinal.mul_is_limit_left
- \- *theorem* ordinal.mul_is_normal
- \- *theorem* ordinal.mul_le_mul
- \- *theorem* ordinal.mul_le_mul_iff_left
- \- *theorem* ordinal.mul_le_mul_left
- \- *theorem* ordinal.mul_le_mul_right
- \- *theorem* ordinal.mul_le_of_limit
- \- *theorem* ordinal.mul_lt_mul_iff_left
- \- *theorem* ordinal.mul_lt_mul_of_pos_left
- \- *theorem* ordinal.mul_lt_of_lt_div
- \- *theorem* ordinal.mul_lt_omega
- \- *theorem* ordinal.mul_lt_omega_power
- \- *theorem* ordinal.mul_ne_zero
- \- *theorem* ordinal.mul_omega
- \- *theorem* ordinal.mul_omega_dvd
- \- *theorem* ordinal.mul_omega_power_power
- \- *theorem* ordinal.mul_pos
- \- *theorem* ordinal.mul_right_inj
- \- *theorem* ordinal.mul_sub
- \- *theorem* ordinal.mul_succ
- \- *theorem* ordinal.mul_zero
- \- *theorem* ordinal.nat_cast_div
- \- *theorem* ordinal.nat_cast_eq_zero
- \- *theorem* ordinal.nat_cast_inj
- \- *theorem* ordinal.nat_cast_le
- \- *theorem* ordinal.nat_cast_lt
- \- *theorem* ordinal.nat_cast_mod
- \- *theorem* ordinal.nat_cast_mul
- \- *theorem* ordinal.nat_cast_ne_zero
- \- *theorem* ordinal.nat_cast_pos
- \- *theorem* ordinal.nat_cast_power
- \- *theorem* ordinal.nat_cast_sub
- \- *theorem* ordinal.nat_cast_succ
- \- *theorem* ordinal.nat_le_card
- \- *theorem* ordinal.nat_lt_card
- \- *theorem* ordinal.nat_lt_limit
- \- *theorem* ordinal.nat_lt_omega
- \- *def* ordinal.nfp
- \- *theorem* ordinal.nfp_eq_self
- \- *theorem* ordinal.not_succ_is_limit
- \- *theorem* ordinal.not_succ_of_is_limit
- \- *theorem* ordinal.not_zero_is_limit
- \- *theorem* ordinal.omega_is_limit
- \- *theorem* ordinal.omega_le
- \- *theorem* ordinal.omega_le_of_is_limit
- \- *theorem* ordinal.omega_ne_zero
- \- *theorem* ordinal.omega_pos
- \- *theorem* ordinal.one_CNF
- \- *theorem* ordinal.one_add_of_omega_le
- \- *theorem* ordinal.one_add_omega
- \- *theorem* ordinal.one_dvd
- \- *theorem* ordinal.one_le_iff_ne_zero
- \- *theorem* ordinal.one_le_iff_pos
- \- *theorem* ordinal.one_lt_omega
- \- *theorem* ordinal.one_power
- \- *def* ordinal.power
- \- *theorem* ordinal.power_add
- \- *theorem* ordinal.power_dvd_power
- \- *theorem* ordinal.power_dvd_power_iff
- \- *theorem* ordinal.power_is_limit
- \- *theorem* ordinal.power_is_limit_left
- \- *theorem* ordinal.power_is_normal
- \- *theorem* ordinal.power_le_of_limit
- \- *theorem* ordinal.power_le_power_iff_right
- \- *theorem* ordinal.power_le_power_left
- \- *theorem* ordinal.power_le_power_right
- \- *theorem* ordinal.power_limit
- \- *theorem* ordinal.power_log_le
- \- *theorem* ordinal.power_lt_omega
- \- *theorem* ordinal.power_lt_power_iff_right
- \- *theorem* ordinal.power_lt_power_left_of_succ
- \- *theorem* ordinal.power_mul
- \- *theorem* ordinal.power_ne_zero
- \- *theorem* ordinal.power_omega
- \- *theorem* ordinal.power_one
- \- *theorem* ordinal.power_pos
- \- *theorem* ordinal.power_right_inj
- \- *theorem* ordinal.power_succ
- \- *theorem* ordinal.power_zero
- \- *def* ordinal.pred
- \- *theorem* ordinal.pred_eq_iff_not_succ
- \- *theorem* ordinal.pred_le
- \- *theorem* ordinal.pred_le_self
- \- *theorem* ordinal.pred_lt_iff_is_succ
- \- *theorem* ordinal.pred_succ
- \- *def* ordinal.sub
- \- *theorem* ordinal.sub_eq_of_add_eq
- \- *theorem* ordinal.sub_eq_zero_iff_le
- \- *theorem* ordinal.sub_is_limit
- \- *theorem* ordinal.sub_le
- \- *theorem* ordinal.sub_le_self
- \- *theorem* ordinal.sub_self
- \- *theorem* ordinal.sub_sub
- \- *theorem* ordinal.sub_zero
- \- *theorem* ordinal.succ_inj
- \- *theorem* ordinal.succ_le_succ
- \- *theorem* ordinal.succ_log_def
- \- *theorem* ordinal.succ_lt_of_is_limit
- \- *theorem* ordinal.succ_lt_of_not_succ
- \- *theorem* ordinal.succ_lt_succ
- \- *theorem* ordinal.succ_ne_zero
- \- *theorem* ordinal.succ_pos
- \- *theorem* ordinal.succ_pred_iff_is_succ
- \- *theorem* ordinal.succ_zero
- \- *def* ordinal.sup
- \- *theorem* ordinal.sup_le
- \- *theorem* ordinal.sup_ord
- \- *lemma* ordinal.sup_succ
- \- *theorem* ordinal.type_eq_zero_iff_empty
- \- *theorem* ordinal.type_fin
- \- *theorem* ordinal.type_mul
- \- *theorem* ordinal.type_ne_zero_iff_nonempty
- \- *lemma* ordinal.type_subrel_lt
- \- *lemma* ordinal.unbounded_range_of_sup_ge
- \- *theorem* ordinal.zero_CNF
- \- *theorem* ordinal.zero_div
- \- *theorem* ordinal.zero_dvd
- \- *theorem* ordinal.zero_lt_one
- \- *theorem* ordinal.zero_mod
- \- *theorem* ordinal.zero_mul
- \- *theorem* ordinal.zero_or_succ_or_limit
- \- *theorem* ordinal.zero_power'
- \- *theorem* ordinal.zero_power
- \- *theorem* ordinal.zero_sub

Added src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* cardinal.add_one_of_omega_le
- \+ *theorem* cardinal.ord_omega
- \+ *theorem* ordinal.CNF_aux
- \+ *theorem* ordinal.CNF_foldr
- \+ *theorem* ordinal.CNF_fst_le
- \+ *theorem* ordinal.CNF_fst_le_log
- \+ *theorem* ordinal.CNF_ne_zero
- \+ *theorem* ordinal.CNF_pairwise
- \+ *theorem* ordinal.CNF_pairwise_aux
- \+ *theorem* ordinal.CNF_rec_ne_zero
- \+ *theorem* ordinal.CNF_rec_zero
- \+ *theorem* ordinal.CNF_snd_lt
- \+ *theorem* ordinal.CNF_sorted
- \+ *theorem* ordinal.CNF_zero
- \+ *theorem* ordinal.add_absorp
- \+ *theorem* ordinal.add_absorp_iff
- \+ *theorem* ordinal.add_is_limit
- \+ *theorem* ordinal.add_is_normal
- \+ *theorem* ordinal.add_le_add_iff_left
- \+ *theorem* ordinal.add_le_add_iff_right
- \+ *theorem* ordinal.add_le_of_limit
- \+ *theorem* ordinal.add_left_cancel
- \+ *theorem* ordinal.add_lt_add_iff_left
- \+ *theorem* ordinal.add_lt_omega
- \+ *theorem* ordinal.add_lt_omega_power
- \+ *theorem* ordinal.add_mul_limit
- \+ *theorem* ordinal.add_mul_limit_aux
- \+ *theorem* ordinal.add_mul_succ
- \+ *theorem* ordinal.add_omega
- \+ *theorem* ordinal.add_omega_power
- \+ *theorem* ordinal.add_right_cancel
- \+ *theorem* ordinal.add_sub_add_cancel
- \+ *theorem* ordinal.add_sub_cancel
- \+ *theorem* ordinal.add_sub_cancel_of_le
- \+ *theorem* ordinal.add_succ
- \+ *def* ordinal.bsup
- \+ *theorem* ordinal.bsup_id
- \+ *theorem* ordinal.bsup_le
- \+ *theorem* ordinal.bsup_type
- \+ *theorem* ordinal.card_eq_nat
- \+ *theorem* ordinal.card_eq_zero
- \+ *theorem* ordinal.card_le_nat
- \+ *theorem* ordinal.card_lt_nat
- \+ *theorem* ordinal.card_mul
- \+ *theorem* ordinal.card_succ
- \+ *def* ordinal.deriv
- \+ *theorem* ordinal.deriv_is_normal
- \+ *theorem* ordinal.deriv_limit
- \+ *theorem* ordinal.deriv_succ
- \+ *theorem* ordinal.deriv_zero
- \+ *theorem* ordinal.div_add_mod
- \+ *lemma* ordinal.div_def
- \+ *theorem* ordinal.div_eq_zero_of_lt
- \+ *theorem* ordinal.div_le
- \+ *theorem* ordinal.div_le_of_le_mul
- \+ *theorem* ordinal.div_lt
- \+ *theorem* ordinal.div_mul_cancel
- \+ *theorem* ordinal.div_one
- \+ *theorem* ordinal.div_self
- \+ *theorem* ordinal.div_zero
- \+ *theorem* ordinal.dvd_add
- \+ *theorem* ordinal.dvd_add_iff
- \+ *theorem* ordinal.dvd_antisymm
- \+ *theorem* ordinal.dvd_def
- \+ *theorem* ordinal.dvd_mul
- \+ *theorem* ordinal.dvd_mul_of_dvd
- \+ *theorem* ordinal.dvd_trans
- \+ *theorem* ordinal.dvd_zero
- \+ *theorem* ordinal.fintype_card
- \+ *lemma* ordinal.has_succ_of_is_limit
- \+ *theorem* ordinal.is_limit.nat_lt
- \+ *theorem* ordinal.is_limit.one_lt
- \+ *theorem* ordinal.is_limit.pos
- \+ *def* ordinal.is_limit
- \+ *theorem* ordinal.is_limit_add_iff
- \+ *theorem* ordinal.is_limit_iff_omega_dvd
- \+ *theorem* ordinal.is_normal.bsup
- \+ *theorem* ordinal.is_normal.bsup_eq
- \+ *theorem* ordinal.is_normal.deriv_fp
- \+ *theorem* ordinal.is_normal.fp_iff_deriv
- \+ *theorem* ordinal.is_normal.inj
- \+ *theorem* ordinal.is_normal.is_limit
- \+ *theorem* ordinal.is_normal.le_iff
- \+ *theorem* ordinal.is_normal.le_nfp
- \+ *theorem* ordinal.is_normal.le_self
- \+ *theorem* ordinal.is_normal.le_set'
- \+ *theorem* ordinal.is_normal.le_set
- \+ *theorem* ordinal.is_normal.limit_le
- \+ *theorem* ordinal.is_normal.limit_lt
- \+ *theorem* ordinal.is_normal.lt_iff
- \+ *theorem* ordinal.is_normal.lt_nfp
- \+ *theorem* ordinal.is_normal.nfp_fp
- \+ *theorem* ordinal.is_normal.nfp_le
- \+ *theorem* ordinal.is_normal.nfp_le_fp
- \+ *theorem* ordinal.is_normal.refl
- \+ *theorem* ordinal.is_normal.sup
- \+ *theorem* ordinal.is_normal.trans
- \+ *def* ordinal.is_normal
- \+ *theorem* ordinal.iterate_le_nfp
- \+ *theorem* ordinal.le_add_sub
- \+ *theorem* ordinal.le_bsup
- \+ *theorem* ordinal.le_div
- \+ *theorem* ordinal.le_log
- \+ *theorem* ordinal.le_nfp_self
- \+ *theorem* ordinal.le_of_dvd
- \+ *theorem* ordinal.le_of_mul_le_mul_left
- \+ *theorem* ordinal.le_power_self
- \+ *theorem* ordinal.le_succ_of_is_limit
- \+ *theorem* ordinal.le_sup
- \+ *theorem* ordinal.lift_add
- \+ *theorem* ordinal.lift_is_limit
- \+ *theorem* ordinal.lift_is_succ
- \+ *theorem* ordinal.lift_mul
- \+ *theorem* ordinal.lift_nat_cast
- \+ *theorem* ordinal.lift_pred
- \+ *theorem* ordinal.lift_succ
- \+ *theorem* ordinal.lift_type_fin
- \+ *theorem* ordinal.limit_le
- \+ *def* ordinal.limit_rec_on
- \+ *theorem* ordinal.limit_rec_on_limit
- \+ *theorem* ordinal.limit_rec_on_succ
- \+ *theorem* ordinal.limit_rec_on_zero
- \+ *def* ordinal.log
- \+ *theorem* ordinal.log_def
- \+ *theorem* ordinal.log_le_log
- \+ *theorem* ordinal.log_le_self
- \+ *theorem* ordinal.log_lt
- \+ *theorem* ordinal.log_not_one_lt
- \+ *theorem* ordinal.log_zero
- \+ *theorem* ordinal.lt_bsup
- \+ *theorem* ordinal.lt_div
- \+ *theorem* ordinal.lt_limit
- \+ *theorem* ordinal.lt_mul_div_add
- \+ *theorem* ordinal.lt_mul_of_limit
- \+ *theorem* ordinal.lt_mul_succ_div
- \+ *theorem* ordinal.lt_of_add_lt_add_right
- \+ *theorem* ordinal.lt_omega
- \+ *theorem* ordinal.lt_power_of_limit
- \+ *theorem* ordinal.lt_power_succ_log
- \+ *theorem* ordinal.lt_pred
- \+ *theorem* ordinal.lt_sub
- \+ *theorem* ordinal.lt_succ
- \+ *theorem* ordinal.lt_sup
- \+ *lemma* ordinal.mk_initial_seg
- \+ *theorem* ordinal.mod_def
- \+ *theorem* ordinal.mod_eq_of_lt
- \+ *theorem* ordinal.mod_lt
- \+ *theorem* ordinal.mod_one
- \+ *theorem* ordinal.mod_self
- \+ *theorem* ordinal.mod_zero
- \+ *theorem* ordinal.mul_add
- \+ *theorem* ordinal.mul_add_div
- \+ *theorem* ordinal.mul_add_one
- \+ *theorem* ordinal.mul_div_cancel
- \+ *theorem* ordinal.mul_div_le
- \+ *theorem* ordinal.mul_is_limit
- \+ *theorem* ordinal.mul_is_limit_left
- \+ *theorem* ordinal.mul_is_normal
- \+ *theorem* ordinal.mul_le_mul
- \+ *theorem* ordinal.mul_le_mul_iff_left
- \+ *theorem* ordinal.mul_le_mul_left
- \+ *theorem* ordinal.mul_le_mul_right
- \+ *theorem* ordinal.mul_le_of_limit
- \+ *theorem* ordinal.mul_lt_mul_iff_left
- \+ *theorem* ordinal.mul_lt_mul_of_pos_left
- \+ *theorem* ordinal.mul_lt_of_lt_div
- \+ *theorem* ordinal.mul_lt_omega
- \+ *theorem* ordinal.mul_lt_omega_power
- \+ *theorem* ordinal.mul_ne_zero
- \+ *theorem* ordinal.mul_omega
- \+ *theorem* ordinal.mul_omega_dvd
- \+ *theorem* ordinal.mul_omega_power_power
- \+ *theorem* ordinal.mul_pos
- \+ *theorem* ordinal.mul_right_inj
- \+ *theorem* ordinal.mul_sub
- \+ *theorem* ordinal.mul_succ
- \+ *theorem* ordinal.mul_zero
- \+ *theorem* ordinal.nat_cast_div
- \+ *theorem* ordinal.nat_cast_eq_zero
- \+ *theorem* ordinal.nat_cast_inj
- \+ *theorem* ordinal.nat_cast_le
- \+ *theorem* ordinal.nat_cast_lt
- \+ *theorem* ordinal.nat_cast_mod
- \+ *theorem* ordinal.nat_cast_mul
- \+ *theorem* ordinal.nat_cast_ne_zero
- \+ *theorem* ordinal.nat_cast_pos
- \+ *theorem* ordinal.nat_cast_power
- \+ *theorem* ordinal.nat_cast_sub
- \+ *theorem* ordinal.nat_cast_succ
- \+ *theorem* ordinal.nat_le_card
- \+ *theorem* ordinal.nat_lt_card
- \+ *theorem* ordinal.nat_lt_limit
- \+ *theorem* ordinal.nat_lt_omega
- \+ *def* ordinal.nfp
- \+ *theorem* ordinal.nfp_eq_self
- \+ *theorem* ordinal.not_succ_is_limit
- \+ *theorem* ordinal.not_succ_of_is_limit
- \+ *theorem* ordinal.not_zero_is_limit
- \+ *theorem* ordinal.omega_is_limit
- \+ *theorem* ordinal.omega_le
- \+ *theorem* ordinal.omega_le_of_is_limit
- \+ *theorem* ordinal.omega_ne_zero
- \+ *theorem* ordinal.omega_pos
- \+ *theorem* ordinal.one_CNF
- \+ *theorem* ordinal.one_add_of_omega_le
- \+ *theorem* ordinal.one_add_omega
- \+ *theorem* ordinal.one_dvd
- \+ *theorem* ordinal.one_le_iff_ne_zero
- \+ *theorem* ordinal.one_le_iff_pos
- \+ *theorem* ordinal.one_lt_omega
- \+ *theorem* ordinal.one_power
- \+ *def* ordinal.power
- \+ *theorem* ordinal.power_add
- \+ *theorem* ordinal.power_dvd_power
- \+ *theorem* ordinal.power_dvd_power_iff
- \+ *theorem* ordinal.power_is_limit
- \+ *theorem* ordinal.power_is_limit_left
- \+ *theorem* ordinal.power_is_normal
- \+ *theorem* ordinal.power_le_of_limit
- \+ *theorem* ordinal.power_le_power_iff_right
- \+ *theorem* ordinal.power_le_power_left
- \+ *theorem* ordinal.power_le_power_right
- \+ *theorem* ordinal.power_limit
- \+ *theorem* ordinal.power_log_le
- \+ *theorem* ordinal.power_lt_omega
- \+ *theorem* ordinal.power_lt_power_iff_right
- \+ *theorem* ordinal.power_lt_power_left_of_succ
- \+ *theorem* ordinal.power_mul
- \+ *theorem* ordinal.power_ne_zero
- \+ *theorem* ordinal.power_omega
- \+ *theorem* ordinal.power_one
- \+ *theorem* ordinal.power_pos
- \+ *theorem* ordinal.power_right_inj
- \+ *theorem* ordinal.power_succ
- \+ *theorem* ordinal.power_zero
- \+ *def* ordinal.pred
- \+ *theorem* ordinal.pred_eq_iff_not_succ
- \+ *theorem* ordinal.pred_le
- \+ *theorem* ordinal.pred_le_self
- \+ *theorem* ordinal.pred_lt_iff_is_succ
- \+ *theorem* ordinal.pred_succ
- \+ *def* ordinal.sub
- \+ *theorem* ordinal.sub_eq_of_add_eq
- \+ *theorem* ordinal.sub_eq_zero_iff_le
- \+ *theorem* ordinal.sub_is_limit
- \+ *theorem* ordinal.sub_le
- \+ *theorem* ordinal.sub_le_self
- \+ *theorem* ordinal.sub_self
- \+ *theorem* ordinal.sub_sub
- \+ *theorem* ordinal.sub_zero
- \+ *theorem* ordinal.succ_inj
- \+ *theorem* ordinal.succ_le_succ
- \+ *theorem* ordinal.succ_log_def
- \+ *theorem* ordinal.succ_lt_of_is_limit
- \+ *theorem* ordinal.succ_lt_of_not_succ
- \+ *theorem* ordinal.succ_lt_succ
- \+ *theorem* ordinal.succ_ne_zero
- \+ *theorem* ordinal.succ_pos
- \+ *theorem* ordinal.succ_pred_iff_is_succ
- \+ *theorem* ordinal.succ_zero
- \+ *def* ordinal.sup
- \+ *theorem* ordinal.sup_le
- \+ *theorem* ordinal.sup_ord
- \+ *lemma* ordinal.sup_succ
- \+ *theorem* ordinal.type_eq_zero_iff_empty
- \+ *theorem* ordinal.type_fin
- \+ *theorem* ordinal.type_mul
- \+ *theorem* ordinal.type_ne_zero_iff_nonempty
- \+ *lemma* ordinal.type_subrel_lt
- \+ *lemma* ordinal.unbounded_range_of_sup_ge
- \+ *theorem* ordinal.zero_CNF
- \+ *theorem* ordinal.zero_div
- \+ *theorem* ordinal.zero_dvd
- \+ *theorem* ordinal.zero_lt_one
- \+ *theorem* ordinal.zero_mod
- \+ *theorem* ordinal.zero_mul
- \+ *theorem* ordinal.zero_or_succ_or_limit
- \+ *theorem* ordinal.zero_power'
- \+ *theorem* ordinal.zero_power
- \+ *theorem* ordinal.zero_sub

Modified src/set_theory/ordinal_notation.lean
- \+/\- *def* onote.NF
- \+/\- *theorem* onote.oadd_lt_oadd_1
- \+/\- *theorem* onote.oadd_lt_oadd_2
- \+/\- *theorem* onote.oadd_lt_oadd_3



## [2020-07-23 08:52:03](https://github.com/leanprover-community/mathlib/commit/79df8cc)
refactor(order/filter/at_top): import order.filter.bases ([#3523](https://github.com/leanprover-community/mathlib/pull/3523))
This way we can use facts about `filter.has_basis` in `filter.at_top`.
Also generalize `is_countably_generated_at_top_finset_nat`
to `at_top` filter on any `encodable` type.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.at_top_basis'
- \+ *lemma* filter.at_top_basis
- \+ *lemma* filter.at_top_countable_basis
- \+ *lemma* filter.has_antimono_basis.tendsto
- \+ *lemma* filter.is_countably_generated.subseq_tendsto
- \+ *lemma* filter.is_countably_generated.tendsto_iff_seq_tendsto
- \+ *lemma* filter.is_countably_generated.tendsto_of_seq_tendsto

Modified src/order/filter/bases.lean
- \- *lemma* filter.at_top_basis'
- \- *lemma* filter.at_top_basis
- \- *lemma* filter.has_antimono_basis.tendsto
- \+ *lemma* filter.has_countable_basis.is_countably_generated
- \- *lemma* filter.is_countably_generated.subseq_tendsto
- \- *lemma* filter.is_countably_generated.tendsto_iff_seq_tendsto
- \- *lemma* filter.is_countably_generated.tendsto_of_seq_tendsto
- \- *lemma* filter.is_countably_generated_at_top_finset_nat



## [2020-07-23 07:50:13](https://github.com/leanprover-community/mathlib/commit/d974457)
feat(ring_theory/ideal_over): a prime ideal lying over a maximal ideal is maximal ([#3488](https://github.com/leanprover-community/mathlib/pull/3488))
By making the results in `ideal_over.lean` a bit more general, we can transfer to quotient rings. This allows us to prove a strict inclusion `I < J` of ideals in `S` results in a strict inclusion `I.comap f < J.comap f` if `R` if `f : R ->+* S` is nice enough. As a corollary, a prime ideal lying over a maximal ideal is maximal.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.map_monic_eq_zero_iff

Modified src/ring_theory/ideal_operations.lean
- \+ *lemma* ideal.comap_eq_top_iff
- \+ *lemma* ideal.mem_quotient_iff_mem

Modified src/ring_theory/ideal_over.lean
- \+ *lemma* ideal.coeff_zero_mem_comap_of_root_mem_of_eval_mem
- \+ *lemma* ideal.comap_lt_comap_of_integral_mem_sdiff
- \+ *lemma* ideal.comap_lt_comap_of_root_mem_sdiff
- \+/\- *lemma* ideal.comap_ne_bot_of_algebraic_mem
- \+/\- *lemma* ideal.comap_ne_bot_of_integral_mem
- \+ *lemma* ideal.exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff
- \+ *lemma* ideal.exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem
- \+ *lemma* ideal.integral_closure.comap_lt_comap
- \+ *lemma* ideal.integral_closure.is_maximal_of_is_maximal_comap
- \+ *lemma* ideal.is_maximal_of_is_integral_of_is_maximal_comap
- \+ *lemma* ideal.mem_of_one_mem

Modified src/ring_theory/ideals.lean
- \+ *lemma* ideal.quotient.mk_surjective



## [2020-07-23 02:51:42](https://github.com/leanprover-community/mathlib/commit/7397db7)
chore(data/sym2) : simplify proofs ([#3522](https://github.com/leanprover-community/mathlib/pull/3522))
This shouldn't change any declarations, only proofs.
#### Estimated changes
Modified src/data/sym2.lean
- \+/\- *lemma* sym2.from_rel_proj_prop
- \+/\- *lemma* sym2.from_rel_prop
- \+/\- *def* sym2.is_diag
- \+/\- *lemma* sym2.map_comp
- \+/\- *lemma* sym2.map_id
- \+/\- *lemma* sym2.mk_has_mem
- \+/\- *lemma* sym2.rel.is_equivalence
- \+/\- *lemma* sym2.vmem_other_spec



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
- \+ *theorem* infi_of_empty
- \+ *theorem* supr_of_empty'
- \+ *theorem* supr_of_empty



## [2020-07-23 01:10:54](https://github.com/leanprover-community/mathlib/commit/827fcd0)
feat(analysis/convex/basic): add lemmas about convex combination of endpoints of intervals ([#3482](https://github.com/leanprover-community/mathlib/pull/3482))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex.combo_self
- \+ *lemma* convex.mem_Icc
- \+ *lemma* convex.mem_Ico
- \+ *lemma* convex.mem_Ioc
- \+ *lemma* convex.mem_Ioo



## [2020-07-22 23:58:19](https://github.com/leanprover-community/mathlib/commit/fbcd890)
chore(data/subtype,order/complete_lattice): use `coe` instead of `subtype.val` ([#3518](https://github.com/leanprover-community/mathlib/pull/3518))
#### Estimated changes
Modified src/data/subtype.lean


Modified src/measure_theory/measure_space.lean


Modified src/order/complete_lattice.lean


Modified src/order/filter/bases.lean
- \+/\- *lemma* filter.countable_binfi_eq_infi_seq

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
- \- *lemma* polynomial.C_inj
- \- *lemma* polynomial.C_mul'
- \- *lemma* polynomial.eval_mul
- \- *lemma* polynomial.eval_pow
- \- *lemma* polynomial.eval₂_hom
- \- *lemma* polynomial.root_mul_left_of_is_root
- \- *lemma* polynomial.root_mul_right_of_is_root

Modified src/data/polynomial/basic.lean


Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.C_mul'
- \+ *lemma* polynomial.finset_sum_coeff

Modified src/data/polynomial/default.lean


Modified src/data/polynomial/degree.lean
- \- *lemma* polynomial.X_pow_sub_C_ne_zero
- \- *theorem* polynomial.X_sub_C_ne_zero
- \- *lemma* polynomial.coeff_mul_degree_add_degree
- \- *lemma* polynomial.coeff_nat_degree_eq_zero_of_degree_lt
- \- *lemma* polynomial.degree_X_pow
- \- *lemma* polynomial.degree_X_pow_sub_C
- \- *lemma* polynomial.degree_X_sub_C
- \- *lemma* polynomial.degree_add_C
- \- *lemma* polynomial.degree_add_eq_of_degree_lt
- \- *lemma* polynomial.degree_add_eq_of_leading_coeff_add_ne_zero
- \- *lemma* polynomial.degree_add_le
- \- *lemma* polynomial.degree_erase_le
- \- *lemma* polynomial.degree_erase_lt
- \- *theorem* polynomial.degree_le_iff_coeff_zero
- \- *lemma* polynomial.degree_le_zero_iff
- \- *lemma* polynomial.degree_lt_degree_mul_X
- \- *lemma* polynomial.degree_mul'
- \- *lemma* polynomial.degree_mul
- \- *lemma* polynomial.degree_mul_le
- \- *lemma* polynomial.degree_nonneg_iff_ne_zero
- \- *lemma* polynomial.degree_pow'
- \- *lemma* polynomial.degree_pow
- \- *lemma* polynomial.degree_pow_le
- \- *lemma* polynomial.degree_sub_le
- \- *lemma* polynomial.degree_sub_lt
- \- *lemma* polynomial.degree_sum_le
- \- *lemma* polynomial.eq_C_of_degree_eq_zero
- \- *lemma* polynomial.eq_C_of_degree_le_zero
- \- *lemma* polynomial.eq_C_of_nat_degree_le_zero
- \- *lemma* polynomial.leading_coeff_C
- \- *lemma* polynomial.leading_coeff_X
- \- *lemma* polynomial.leading_coeff_X_pow
- \- *lemma* polynomial.leading_coeff_add_of_degree_eq
- \- *lemma* polynomial.leading_coeff_add_of_degree_lt
- \- *lemma* polynomial.leading_coeff_eq_zero
- \- *lemma* polynomial.leading_coeff_eq_zero_iff_deg_eq_bot
- \- *def* polynomial.leading_coeff_hom
- \- *lemma* polynomial.leading_coeff_hom_apply
- \- *lemma* polynomial.leading_coeff_monomial
- \- *lemma* polynomial.leading_coeff_mul'
- \- *lemma* polynomial.leading_coeff_mul
- \- *theorem* polynomial.leading_coeff_mul_X_pow
- \- *lemma* polynomial.leading_coeff_one
- \- *lemma* polynomial.leading_coeff_pow'
- \- *lemma* polynomial.leading_coeff_pow
- \- *lemma* polynomial.leading_coeff_zero
- \- *lemma* polynomial.monic.ne_zero
- \- *lemma* polynomial.monic.ne_zero_of_zero_ne_one
- \- *lemma* polynomial.monic_X
- \- *lemma* polynomial.monic_one
- \- *lemma* polynomial.nat_degree_X_pow_sub_C
- \- *lemma* polynomial.nat_degree_X_sub_C
- \- *lemma* polynomial.nat_degree_X_sub_C_le
- \- *lemma* polynomial.nat_degree_eq_zero_iff_degree_le_zero
- \- *lemma* polynomial.nat_degree_mul'
- \- *lemma* polynomial.nat_degree_mul_le
- \- *lemma* polynomial.nat_degree_pos_iff_degree_pos
- \- *lemma* polynomial.nat_degree_pow'
- \- *lemma* polynomial.ne_zero_of_degree_gt
- \- *lemma* polynomial.next_coeff_X_sub_C
- \- *theorem* polynomial.not_is_unit_X
- \- *lemma* polynomial.subsingleton_of_monic_zero
- \- *lemma* polynomial.zero_le_degree_iff

Modified src/data/polynomial/degree/basic.lean
- \+ *lemma* polynomial.X_pow_sub_C_ne_zero
- \+ *theorem* polynomial.X_sub_C_ne_zero
- \+ *lemma* polynomial.as_sum
- \+ *lemma* polynomial.coeff_mul_degree_add_degree
- \+ *lemma* polynomial.coeff_nat_degree_eq_zero_of_degree_lt
- \+ *lemma* polynomial.degree_X_pow
- \+ *lemma* polynomial.degree_X_pow_sub_C
- \+ *lemma* polynomial.degree_X_sub_C
- \+ *lemma* polynomial.degree_add_C
- \+ *lemma* polynomial.degree_add_eq_of_degree_lt
- \+ *lemma* polynomial.degree_add_eq_of_leading_coeff_add_ne_zero
- \+ *lemma* polynomial.degree_add_le
- \+ *lemma* polynomial.degree_erase_le
- \+ *lemma* polynomial.degree_erase_lt
- \+ *theorem* polynomial.degree_le_iff_coeff_zero
- \+ *lemma* polynomial.degree_le_zero_iff
- \+ *lemma* polynomial.degree_lt_degree_mul_X
- \+ *lemma* polynomial.degree_mul'
- \+ *lemma* polynomial.degree_mul
- \+ *lemma* polynomial.degree_mul_le
- \+ *lemma* polynomial.degree_nonneg_iff_ne_zero
- \+ *lemma* polynomial.degree_pow'
- \+ *lemma* polynomial.degree_pow
- \+ *lemma* polynomial.degree_pow_le
- \+ *lemma* polynomial.degree_sub_le
- \+ *lemma* polynomial.degree_sub_lt
- \+ *lemma* polynomial.degree_sum_le
- \+ *lemma* polynomial.eq_C_of_degree_eq_zero
- \+ *lemma* polynomial.eq_C_of_degree_le_zero
- \+ *lemma* polynomial.eq_C_of_nat_degree_le_zero
- \+ *lemma* polynomial.leading_coeff_C
- \+ *lemma* polynomial.leading_coeff_X
- \+ *lemma* polynomial.leading_coeff_X_pow
- \+ *lemma* polynomial.leading_coeff_add_of_degree_eq
- \+ *lemma* polynomial.leading_coeff_add_of_degree_lt
- \+ *lemma* polynomial.leading_coeff_eq_zero
- \+ *lemma* polynomial.leading_coeff_eq_zero_iff_deg_eq_bot
- \+ *def* polynomial.leading_coeff_hom
- \+ *lemma* polynomial.leading_coeff_hom_apply
- \+ *lemma* polynomial.leading_coeff_monomial
- \+ *lemma* polynomial.leading_coeff_mul'
- \+ *lemma* polynomial.leading_coeff_mul
- \+ *theorem* polynomial.leading_coeff_mul_X_pow
- \+ *lemma* polynomial.leading_coeff_one
- \+ *lemma* polynomial.leading_coeff_pow'
- \+ *lemma* polynomial.leading_coeff_pow
- \+ *lemma* polynomial.leading_coeff_zero
- \+ *lemma* polynomial.monic.ne_zero
- \+ *lemma* polynomial.monic.ne_zero_of_zero_ne_one
- \+ *lemma* polynomial.monic_X
- \+ *lemma* polynomial.monic_one
- \+ *lemma* polynomial.nat_degree_X_pow_sub_C
- \+ *lemma* polynomial.nat_degree_X_sub_C
- \+ *lemma* polynomial.nat_degree_X_sub_C_le
- \+ *lemma* polynomial.nat_degree_eq_zero_iff_degree_le_zero
- \+ *lemma* polynomial.nat_degree_mul'
- \+ *lemma* polynomial.nat_degree_mul_le
- \+ *lemma* polynomial.nat_degree_pos_iff_degree_pos
- \+ *lemma* polynomial.nat_degree_pow'
- \+ *lemma* polynomial.ne_zero_of_degree_gt
- \+ *lemma* polynomial.next_coeff_X_sub_C
- \+ *theorem* polynomial.not_is_unit_X
- \+ *lemma* polynomial.subsingleton_of_monic_zero
- \+ *lemma* polynomial.sum_over_range'
- \+ *lemma* polynomial.sum_over_range
- \+ *lemma* polynomial.zero_le_degree_iff

Modified src/data/polynomial/derivative.lean
- \- *lemma* polynomial.derivative_eval
- \- *lemma* polynomial.is_coprime_of_is_root_of_eval_derivative_ne_zero

Modified src/data/polynomial/div.lean


Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.eval_mul
- \+ *lemma* polynomial.eval_pow
- \+ *lemma* polynomial.eval₂_hom
- \+ *lemma* polynomial.root_mul_left_of_is_root
- \+ *lemma* polynomial.root_mul_right_of_is_root

Modified src/data/polynomial/field_division.lean
- \+ *lemma* polynomial.is_coprime_of_is_root_of_eval_derivative_ne_zero

Modified src/data/polynomial/identities.lean
- \+ *lemma* polynomial.derivative_eval

Modified src/data/polynomial/induction.lean
- \- *lemma* polynomial.as_sum
- \- *lemma* polynomial.finset_sum_coeff
- \- *lemma* polynomial.sum_over_range'
- \- *lemma* polynomial.sum_over_range

Added src/data/polynomial/integral_normalization.lean
- \+ *lemma* polynomial.integral_normalization_aeval_eq_zero
- \+ *lemma* polynomial.integral_normalization_coeff_degree
- \+ *lemma* polynomial.integral_normalization_coeff_nat_degree
- \+ *lemma* polynomial.integral_normalization_coeff_ne_degree
- \+ *lemma* polynomial.integral_normalization_coeff_ne_nat_degree
- \+ *lemma* polynomial.integral_normalization_eval₂_eq_zero
- \+ *lemma* polynomial.monic_integral_normalization
- \+ *lemma* polynomial.support_integral_normalization

Modified src/data/polynomial/monic.lean
- \- *lemma* polynomial.integral_normalization_aeval_eq_zero
- \- *lemma* polynomial.integral_normalization_coeff_degree
- \- *lemma* polynomial.integral_normalization_coeff_nat_degree
- \- *lemma* polynomial.integral_normalization_coeff_ne_degree
- \- *lemma* polynomial.integral_normalization_coeff_ne_nat_degree
- \- *lemma* polynomial.integral_normalization_eval₂_eq_zero
- \- *lemma* polynomial.monic_integral_normalization
- \- *lemma* polynomial.support_integral_normalization

Modified src/data/polynomial/monomial.lean
- \+ *lemma* polynomial.C_inj

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
- \+ *def* matrix.update_column
- \+ *lemma* matrix.update_column_ne
- \+ *lemma* matrix.update_column_self
- \+ *lemma* matrix.update_column_transpose
- \+ *lemma* matrix.update_column_val
- \+ *def* matrix.update_row
- \+ *lemma* matrix.update_row_ne
- \+ *lemma* matrix.update_row_self
- \+ *lemma* matrix.update_row_transpose
- \+ *lemma* matrix.update_row_val

Modified src/linear_algebra/nonsingular_inverse.lean
- \- *def* matrix.update_column
- \- *lemma* matrix.update_column_ne
- \- *lemma* matrix.update_column_self
- \- *lemma* matrix.update_column_val
- \- *def* matrix.update_row
- \- *lemma* matrix.update_row_ne
- \- *lemma* matrix.update_row_self
- \- *lemma* matrix.update_row_transpose
- \- *lemma* matrix.update_row_val



## [2020-07-22 11:32:56](https://github.com/leanprover-community/mathlib/commit/90d3386)
feat(category_theory/kernels): compute kernel (f ≫ g) when one is an iso ([#3438](https://github.com/leanprover-community/mathlib/pull/3438))
#### Estimated changes
Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.cokernel_comp_is_iso
- \+ *def* category_theory.limits.cokernel_is_iso_comp
- \+ *lemma* category_theory.limits.cokernel_π_comp_cokernel_comp_is_iso_hom
- \+ *lemma* category_theory.limits.cokernel_π_comp_cokernel_comp_is_iso_inv
- \+ *lemma* category_theory.limits.cokernel_π_comp_cokernel_is_iso_comp_hom
- \+ *lemma* category_theory.limits.cokernel_π_comp_cokernel_is_iso_comp_inv
- \+ *def* category_theory.limits.kernel_comp_is_iso
- \+ *lemma* category_theory.limits.kernel_comp_is_iso_hom_comp_kernel_ι
- \+ *lemma* category_theory.limits.kernel_comp_is_iso_inv_comp_kernel_ι
- \+ *def* category_theory.limits.kernel_is_iso_comp
- \+ *lemma* category_theory.limits.kernel_is_iso_comp_hom_comp_kernel_ι
- \+ *lemma* category_theory.limits.kernel_is_iso_comp_inv_comp_kernel_ι



## [2020-07-22 10:18:14](https://github.com/leanprover-community/mathlib/commit/39f8f02)
refactor(algebra/big_operators): split file, reduce imports ([#3495](https://github.com/leanprover-community/mathlib/pull/3495))
I've split up `algebra.big_operators`. It wasn't completely obvious how to divide it up, but this is an attempt to balance coherence / file size / minimal imports.
#### Estimated changes
Modified archive/100-theorems-list/42_inverse_triangle_sum.lean


Modified archive/sensitivity.lean


Renamed src/algebra/big_operators.lean to src/algebra/big_operators/basic.lean
- \- *theorem* directed.finset_le
- \- *lemma* finset.abs_sum_le_sum_abs
- \- *theorem* finset.card_le_mul_card_image
- \- *lemma* finset.card_pi
- \- *theorem* finset.dvd_sum
- \- *theorem* finset.exists_le
- \- *theorem* finset.exists_le_of_sum_le
- \- *lemma* finset.exists_pos_of_sum_zero_of_exists_nonzero
- \- *lemma* finset.le_sum_of_subadditive
- \- *lemma* finset.mul_sum
- \- *lemma* finset.prod_Ico_add
- \- *lemma* finset.prod_Ico_consecutive
- \- *lemma* finset.prod_Ico_eq_mul_inv
- \- *lemma* finset.prod_Ico_eq_prod_range
- \- *lemma* finset.prod_Ico_id_eq_fact
- \- *lemma* finset.prod_Ico_reflect
- \- *lemma* finset.prod_Ico_succ_top
- \- *lemma* finset.prod_add
- \- *lemma* finset.prod_eq_prod_Ico_succ_bot
- \- *lemma* finset.prod_le_prod'
- \- *lemma* finset.prod_le_prod
- \- *lemma* finset.prod_nat_cast
- \- *lemma* finset.prod_nonneg
- \- *lemma* finset.prod_pos
- \- *lemma* finset.prod_pow_eq_pow_sum
- \- *lemma* finset.prod_powerset_insert
- \- *lemma* finset.prod_range_mul_prod_Ico
- \- *lemma* finset.prod_range_reflect
- \- *lemma* finset.prod_sum
- \- *lemma* finset.single_le_sum
- \- *lemma* finset.sum_Ico_add
- \- *lemma* finset.sum_Ico_eq_sub
- \- *lemma* finset.sum_Ico_reflect
- \- *lemma* finset.sum_Ico_succ_top
- \- *lemma* finset.sum_boole_mul
- \- *lemma* finset.sum_div
- \- *lemma* finset.sum_eq_sum_Ico_succ_bot
- \- *lemma* finset.sum_eq_zero_iff
- \- *lemma* finset.sum_eq_zero_iff_of_nonneg
- \- *lemma* finset.sum_eq_zero_iff_of_nonpos
- \- *lemma* finset.sum_le_sum
- \- *lemma* finset.sum_le_sum_of_ne_zero
- \- *lemma* finset.sum_le_sum_of_subset
- \- *lemma* finset.sum_le_sum_of_subset_of_nonneg
- \- *theorem* finset.sum_lt_sum
- \- *lemma* finset.sum_lt_sum_of_nonempty
- \- *lemma* finset.sum_lt_sum_of_subset
- \- *lemma* finset.sum_mono_set
- \- *lemma* finset.sum_mono_set_of_nonneg
- \- *lemma* finset.sum_mul
- \- *lemma* finset.sum_mul_boole
- \- *lemma* finset.sum_mul_sum
- \- *lemma* finset.sum_nonneg
- \- *lemma* finset.sum_nonpos
- \- *lemma* finset.sum_pow_mul_eq_add_pow
- \- *lemma* finset.sum_range_id
- \- *lemma* finset.sum_range_id_mul_two
- \- *lemma* finset.sum_range_reflect
- \- *lemma* is_group_hom_finset_prod
- \- *lemma* with_top.op_sum
- \- *lemma* with_top.sum_eq_top_iff
- \- *lemma* with_top.sum_lt_top
- \- *lemma* with_top.sum_lt_top_iff
- \- *lemma* with_top.unop_sum

Added src/algebra/big_operators/default.lean


Added src/algebra/big_operators/intervals.lean
- \+ *lemma* finset.prod_Ico_add
- \+ *lemma* finset.prod_Ico_consecutive
- \+ *lemma* finset.prod_Ico_eq_mul_inv
- \+ *lemma* finset.prod_Ico_eq_prod_range
- \+ *lemma* finset.prod_Ico_id_eq_fact
- \+ *lemma* finset.prod_Ico_reflect
- \+ *lemma* finset.prod_Ico_succ_top
- \+ *lemma* finset.prod_eq_prod_Ico_succ_bot
- \+ *lemma* finset.prod_range_mul_prod_Ico
- \+ *lemma* finset.prod_range_reflect
- \+ *lemma* finset.sum_Ico_add
- \+ *lemma* finset.sum_Ico_eq_sub
- \+ *lemma* finset.sum_Ico_reflect
- \+ *lemma* finset.sum_Ico_succ_top
- \+ *lemma* finset.sum_eq_sum_Ico_succ_bot
- \+ *lemma* finset.sum_range_id
- \+ *lemma* finset.sum_range_id_mul_two
- \+ *lemma* finset.sum_range_reflect

Added src/algebra/big_operators/order.lean
- \+ *lemma* finset.abs_sum_le_sum_abs
- \+ *theorem* finset.card_le_mul_card_image
- \+ *theorem* finset.exists_le_of_sum_le
- \+ *lemma* finset.exists_pos_of_sum_zero_of_exists_nonzero
- \+ *lemma* finset.le_sum_of_subadditive
- \+ *lemma* finset.prod_le_prod'
- \+ *lemma* finset.prod_le_prod
- \+ *lemma* finset.prod_nonneg
- \+ *lemma* finset.prod_pos
- \+ *lemma* finset.single_le_sum
- \+ *lemma* finset.sum_eq_zero_iff
- \+ *lemma* finset.sum_eq_zero_iff_of_nonneg
- \+ *lemma* finset.sum_eq_zero_iff_of_nonpos
- \+ *lemma* finset.sum_le_sum
- \+ *lemma* finset.sum_le_sum_of_ne_zero
- \+ *lemma* finset.sum_le_sum_of_subset
- \+ *lemma* finset.sum_le_sum_of_subset_of_nonneg
- \+ *theorem* finset.sum_lt_sum
- \+ *lemma* finset.sum_lt_sum_of_nonempty
- \+ *lemma* finset.sum_lt_sum_of_subset
- \+ *lemma* finset.sum_mono_set
- \+ *lemma* finset.sum_mono_set_of_nonneg
- \+ *lemma* finset.sum_nonneg
- \+ *lemma* finset.sum_nonpos
- \+ *lemma* with_top.op_sum
- \+ *lemma* with_top.sum_eq_top_iff
- \+ *lemma* with_top.sum_lt_top
- \+ *lemma* with_top.sum_lt_top_iff
- \+ *lemma* with_top.unop_sum

Added src/algebra/big_operators/ring.lean
- \+ *theorem* finset.dvd_sum
- \+ *lemma* finset.mul_sum
- \+ *lemma* finset.prod_add
- \+ *lemma* finset.prod_nat_cast
- \+ *lemma* finset.prod_pow_eq_pow_sum
- \+ *lemma* finset.prod_powerset_insert
- \+ *lemma* finset.prod_sum
- \+ *lemma* finset.sum_boole_mul
- \+ *lemma* finset.sum_div
- \+ *lemma* finset.sum_mul
- \+ *lemma* finset.sum_mul_boole
- \+ *lemma* finset.sum_mul_sum
- \+ *lemma* finset.sum_pow_mul_eq_add_pow

Modified src/algebra/direct_limit.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/module.lean
- \- *theorem* finset.exists_card_smul_ge_sum
- \- *theorem* finset.exists_card_smul_le_sum
- \- *lemma* finset.sum_const'

Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/preadditive/default.lean


Added src/data/finset/order.lean
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
- \+/\- *def* Top.adj₁
- \+/\- *def* Top.adj₂

Modified src/topology/category/Top/basic.lean
- \+ *lemma* Top.comp_app

Modified src/topology/category/Top/limits.lean


Modified src/topology/category/Top/opens.lean
- \+/\- *lemma* topological_space.opens.map_obj

Modified src/topology/category/UniformSpace.lean


Modified src/topology/continuous_map.lean
- \+ *lemma* continuous_map.coe_inj
- \+ *def* continuous_map.comp
- \+ *def* continuous_map.id

Modified src/topology/sheaves/presheaf_of_functions.lean
- \- *lemma* Top.continuous_functions.add
- \+/\- *def* Top.continuous_functions.map
- \- *lemma* Top.continuous_functions.mul
- \- *lemma* Top.continuous_functions.one
- \- *lemma* Top.continuous_functions.zero



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
- \+ *def* list.bidirectional_rec
- \+ *def* list.bidirectional_rec_on
- \+ *theorem* list.init_append_last
- \+ *theorem* list.length_init



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
- \+ *theorem* dvd_dvd_iff_associated
- \+ *lemma* dvd_dvd_of_associated
- \+ *lemma* dvd_of_associated

Added src/ring_theory/discrete_valuation_ring.lean
- \+ *lemma* discrete_valuation_ring.associated_of_irreducible
- \+ *theorem* discrete_valuation_ring.exists_irreducible
- \+ *theorem* discrete_valuation_ring.iff_PID_with_one_nonzero_prime
- \+ *theorem* discrete_valuation_ring.irreducible_iff_uniformiser
- \+ *lemma* discrete_valuation_ring.not_a_field

Modified src/ring_theory/ideals.lean
- \+ *lemma* ideal.maximal_of_no_maximal
- \+ *lemma* ideal.span_singleton_eq_span_singleton
- \+ *lemma* ideal.span_singleton_mul_left_unit
- \+ *lemma* ideal.span_singleton_mul_right_unit
- \+ *lemma* local_of_unique_nonzero_prime
- \+ *lemma* local_ring.eq_maximal_ideal
- \+ *lemma* local_ring.le_maximal_ideal
- \- *lemma* local_ring.max_ideal_unique
- \+ *lemma* local_ring.maximal_ideal_unique



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
- \+ *def* unit_of_invertible
- \+ *lemma* unit_of_invertible_inv
- \+ *lemma* unit_of_invertible_val



## [2020-07-21 21:58:56](https://github.com/leanprover-community/mathlib/commit/2fb6a05)
feat(group_theory/semidirect_product): semidirect_product.map ([#3492](https://github.com/leanprover-community/mathlib/pull/3492))
#### Estimated changes
Modified src/group_theory/semidirect_product.lean
- \+ *def* semidirect_product.map
- \+ *lemma* semidirect_product.map_comp_inl
- \+ *lemma* semidirect_product.map_comp_inr
- \+ *lemma* semidirect_product.map_inl
- \+ *lemma* semidirect_product.map_inr
- \+ *lemma* semidirect_product.map_left
- \+ *lemma* semidirect_product.map_right
- \+ *lemma* semidirect_product.right_hom_comp_map



## [2020-07-21 21:29:16](https://github.com/leanprover-community/mathlib/commit/dfef07a)
chore(analysis/special_functions): moved trig vals out of real.pi, added new trig vals ([#3497](https://github.com/leanprover-community/mathlib/pull/3497))
Moved trigonometric lemmas from real.pi to analysis.special_functions.trigonometric. Also added two new trig lemmas, tan_pi_div_four and arctan_one, to analysis.special_functions.trigonometric.
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Trig.20function.20values
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* real.arctan_one
- \+ *lemma* real.cos_pi_div_eight
- \+ *lemma* real.cos_pi_div_four
- \+ *lemma* real.cos_pi_div_sixteen
- \+ *lemma* real.cos_pi_div_thirty_two
- \+ *lemma* real.cos_pi_over_two_pow
- \+ *lemma* real.sin_pi_div_eight
- \+ *lemma* real.sin_pi_div_four
- \+ *lemma* real.sin_pi_div_sixteen
- \+ *lemma* real.sin_pi_div_thirty_two
- \+ *lemma* real.sin_pi_over_two_pow_succ
- \+ *lemma* real.sin_square_pi_over_two_pow
- \+ *lemma* real.sin_square_pi_over_two_pow_succ
- \+ *lemma* real.sqrt_two_add_series_lt_two
- \+ *lemma* real.sqrt_two_add_series_monotone_left
- \+ *lemma* real.sqrt_two_add_series_nonneg
- \+ *lemma* real.sqrt_two_add_series_one
- \+ *lemma* real.sqrt_two_add_series_succ
- \+ *lemma* real.sqrt_two_add_series_two
- \+ *lemma* real.sqrt_two_add_series_zero
- \+ *lemma* real.sqrt_two_add_series_zero_nonneg
- \+ *lemma* real.tan_pi_div_four

Modified src/data/real/pi.lean
- \- *lemma* real.cos_pi_div_eight
- \- *lemma* real.cos_pi_div_four
- \- *lemma* real.cos_pi_div_sixteen
- \- *lemma* real.cos_pi_div_thirty_two
- \- *lemma* real.cos_pi_over_two_pow
- \- *lemma* real.sin_pi_div_eight
- \- *lemma* real.sin_pi_div_four
- \- *lemma* real.sin_pi_div_sixteen
- \- *lemma* real.sin_pi_div_thirty_two
- \- *lemma* real.sin_pi_over_two_pow_succ
- \- *lemma* real.sin_square_pi_over_two_pow
- \- *lemma* real.sin_square_pi_over_two_pow_succ
- \- *lemma* real.sqrt_two_add_series_lt_two
- \- *lemma* real.sqrt_two_add_series_monotone_left
- \- *lemma* real.sqrt_two_add_series_nonneg
- \- *lemma* real.sqrt_two_add_series_one
- \- *lemma* real.sqrt_two_add_series_succ
- \- *lemma* real.sqrt_two_add_series_two
- \- *lemma* real.sqrt_two_add_series_zero
- \- *lemma* real.sqrt_two_add_series_zero_nonneg



## [2020-07-21 16:25:32](https://github.com/leanprover-community/mathlib/commit/c47d1d0)
feat(data/{mv_}polynomial): make args to aeval implicit ([#3494](https://github.com/leanprover-community/mathlib/pull/3494))
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.aeval_C
- \+/\- *lemma* mv_polynomial.aeval_X
- \+/\- *theorem* mv_polynomial.aeval_def

Modified src/data/polynomial/algebra_map.lean
- \+/\- *lemma* polynomial.aeval_C
- \+/\- *lemma* polynomial.aeval_X
- \+/\- *theorem* polynomial.aeval_alg_hom
- \+/\- *theorem* polynomial.aeval_alg_hom_apply
- \+/\- *theorem* polynomial.aeval_def
- \+/\- *lemma* polynomial.coeff_zero_eq_aeval_zero

Modified src/data/polynomial/monic.lean


Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/minimal_polynomial.lean
- \+/\- *lemma* minimal_polynomial.aeval
- \+/\- *lemma* minimal_polynomial.dvd
- \+/\- *lemma* minimal_polynomial.min
- \+/\- *lemma* minimal_polynomial.unique

Modified src/ring_theory/adjoin.lean
- \+/\- *theorem* algebra.adjoin_singleton_eq_range

Modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* adjoin_root.aeval_eq

Modified src/ring_theory/algebra_tower.lean
- \+/\- *theorem* is_algebra_tower.aeval_apply

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \+/\- *lemma* is_integral_trans_aux

Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/rational_root.lean
- \+/\- *theorem* denom_dvd_of_is_root
- \+/\- *theorem* is_integer_of_is_root_of_monic
- \+/\- *theorem* num_dvd_of_is_root



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
- \+ *lemma* set.Icc_subset_Ici_self
- \+ *lemma* set.Icc_subset_Iic_self
- \+ *lemma* set.Icc_subset_Ioo
- \+ *lemma* set.Ioc_subset_Ioo_right

Modified src/topology/algebra/ordered.lean
- \+ *lemma* Icc_mem_nhds_within_Ici
- \+ *lemma* Icc_mem_nhds_within_Iic
- \+ *lemma* Ico_mem_nhds_within_Ici
- \+ *lemma* Ico_mem_nhds_within_Iic
- \+ *lemma* Ioc_mem_nhds_within_Ici
- \+ *lemma* Ioc_mem_nhds_within_Iic
- \+ *lemma* Ioo_mem_nhds_within_Ici
- \+ *lemma* Ioo_mem_nhds_within_Iic
- \+ *lemma* mem_nhds_within_Ici_iff_exists_Icc_subset'
- \+ *lemma* mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset
- \+ *lemma* mem_nhds_within_Iic_iff_exists_Icc_subset'
- \+ *lemma* mem_nhds_within_Iic_iff_exists_mem_Ico_Ioc_subset
- \+ *lemma* nhds_within_Icc_eq_nhds_within_Ici
- \+ *lemma* nhds_within_Icc_eq_nhds_within_Iic
- \+ *lemma* nhds_within_Ici_ne_bot
- \+ *lemma* nhds_within_Ici_self_ne_bot
- \+ *lemma* nhds_within_Ico_eq_nhds_within_Ici
- \+ *lemma* nhds_within_Iic_ne_bot
- \+ *lemma* nhds_within_Iic_self_ne_bot
- \+ *lemma* nhds_within_Ioc_eq_nhds_within_Iic
- \+ *lemma* tfae_mem_nhds_within_Ici
- \+ *lemma* tfae_mem_nhds_within_Iic



## [2020-07-21 12:58:53](https://github.com/leanprover-community/mathlib/commit/49049e4)
feat(topology): implemented continuous bundled maps ([#3486](https://github.com/leanprover-community/mathlib/pull/3486))
In this PR we defined continuous bundled maps, adapted the file `compact_open` accordingly, and proved instances of algebraic structures over the type `continuous_map` of continuous bundled maps. This feature was suggested on Zulip multiple times, see for example https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Continuous.20maps
#### Estimated changes
Modified src/topology/algebra/continuous_functions.lean
- \- *def* C
- \+ *def* continuous.C
- \+ *def* continuous_map.C

Modified src/topology/algebra/group.lean


Modified src/topology/compact_open.lean
- \+/\- *lemma* continuous_map.image_coev
- \+/\- *def* continuous_map.induced
- \- *def* continuous_map

Added src/topology/continuous_map.lean
- \+ *def* continuous_map.const
- \+ *theorem* continuous_map.ext
- \+ *structure* continuous_map



## [2020-07-21 11:50:25](https://github.com/leanprover-community/mathlib/commit/5c55e15)
feat(data/finset/intervals): Lemma about filter and Ico ([#3479](https://github.com/leanprover-community/mathlib/pull/3479))
Add "if you filter an Ico based on being less than or equal to its bottom element, you get the singleton bottom element".
#### Estimated changes
Modified src/data/finset/intervals.lean
- \+ *lemma* finset.Ico.filter_Ico_bot

Modified src/data/list/intervals.lean
- \+ *lemma* list.Ico.filter_le_of_bot
- \+ *lemma* list.Ico.filter_lt_of_succ_bot

Modified src/data/multiset/intervals.lean
- \+ *lemma* multiset.Ico.filter_le_of_bot



## [2020-07-21 10:37:37](https://github.com/leanprover-community/mathlib/commit/d57130b)
feat(field_theory/mv_polynomial): char_p instance ([#3491](https://github.com/leanprover-community/mathlib/pull/3491))
#### Estimated changes
Modified src/field_theory/mv_polynomial.lean




## [2020-07-21 09:25:11](https://github.com/leanprover-community/mathlib/commit/1a31e69)
chore(algebra/group/anti_hom): remove is_group_anti_hom ([#3485](https://github.com/leanprover-community/mathlib/pull/3485))
`is_group_anti_hom` is no longer used anywhere, so I'm going to count it as deprecated and propose removing it.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \- *theorem* inv_prod
- \- *theorem* is_group_anti_hom.map_prod

Deleted src/algebra/group/anti_hom.lean
- \- *theorem* inv_is_group_anti_hom
- \- *theorem* is_group_anti_hom.map_inv
- \- *theorem* is_group_anti_hom.map_one

Modified src/algebra/group/default.lean




## [2020-07-21 08:38:58](https://github.com/leanprover-community/mathlib/commit/3169970)
feat(category_theory/kernels): helper lemmas for constructing kernels ([#3439](https://github.com/leanprover-community/mathlib/pull/3439))
This does for kernels what [#3398](https://github.com/leanprover-community/mathlib/pull/3398) did for pullbacks.
#### Estimated changes
Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.is_colimit.of_π
- \+ *def* category_theory.limits.is_colimit_aux
- \+ *def* category_theory.limits.is_limit.of_ι
- \+ *def* category_theory.limits.is_limit_aux



## [2020-07-21 07:47:44](https://github.com/leanprover-community/mathlib/commit/d174d3d)
refactor(linear_algebra/*): postpone importing material on direct sums ([#3484](https://github.com/leanprover-community/mathlib/pull/3484))
This is just a refactor, to avoid needing to develop material on direct sums before we can even define an algebra.
#### Estimated changes
Modified src/algebra/direct_limit.lean


Modified src/algebra/lie_algebra.lean


Added src/linear_algebra/direct_sum/finsupp.lean
- \+ *def* finsupp_lequiv_direct_sum
- \+ *theorem* finsupp_lequiv_direct_sum_single
- \+ *theorem* finsupp_lequiv_direct_sum_symm_lof
- \+ *def* finsupp_tensor_finsupp
- \+ *theorem* finsupp_tensor_finsupp_single
- \+ *theorem* finsupp_tensor_finsupp_symm_single

Added src/linear_algebra/direct_sum/tensor_product.lean
- \+ *def* tensor_product.direct_sum
- \+ *theorem* tensor_product.direct_sum_lof_tmul_lof

Modified src/linear_algebra/finsupp.lean
- \- *def* finsupp_lequiv_direct_sum
- \- *theorem* finsupp_lequiv_direct_sum_single
- \- *theorem* finsupp_lequiv_direct_sum_symm_lof
- \- *def* finsupp_tensor_finsupp
- \- *theorem* finsupp_tensor_finsupp_single
- \- *theorem* finsupp_tensor_finsupp_symm_single

Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/tensor_product.lean
- \- *def* tensor_product.direct_sum
- \- *theorem* tensor_product.direct_sum_lof_tmul_lof



## [2020-07-21 04:06:36](https://github.com/leanprover-community/mathlib/commit/c71e67a)
feat(ring_theory/jacobson): definition of Jacobson rings ([#3404](https://github.com/leanprover-community/mathlib/pull/3404))
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.coe_ring_hom

Modified src/ring_theory/ideal_operations.lean
- \+ *theorem* ideal.comap.is_maximal
- \+ *lemma* ideal.comap_bot_le_of_injective
- \+ *lemma* ideal.comap_le_iff_le_map
- \- *theorem* ideal.is_local.le_jacobson
- \- *theorem* ideal.is_local.mem_jacobson_or_exists_inv
- \- *def* ideal.is_local
- \- *theorem* ideal.is_local_of_is_maximal_radical
- \- *theorem* ideal.is_primary_of_is_maximal_radical
- \- *def* ideal.jacobson
- \- *theorem* ideal.jacobson_eq_top_iff
- \+ *lemma* ideal.ker_le_comap
- \+ *lemma* ideal.le_map_of_comap_le_of_surjective
- \+ *theorem* ideal.map.is_maximal
- \+ *lemma* ideal.map_Inf
- \+ *theorem* ideal.map_eq_top_or_is_maximal_of_surjective
- \- *theorem* ideal.mem_jacobson_iff
- \+ *lemma* ideal.mem_map_iff_of_surjective
- \+ *def* ideal.order_iso_of_bijective

Modified src/ring_theory/ideals.lean
- \+ *lemma* ideal.bot_is_maximal

Added src/ring_theory/jacobson.lean
- \+ *def* ideal.is_jacobson
- \+ *lemma* ideal.is_jacobson_iff_Inf_maximal
- \+ *lemma* ideal.is_jacobson_iff_prime_eq
- \+ *lemma* ideal.is_jacobson_iso
- \+ *theorem* ideal.is_jacobson_of_surjective
- \+ *lemma* ideal.radical_eq_jacobson

Added src/ring_theory/jacobson_ideal.lean
- \+ *theorem* ideal.is_local.le_jacobson
- \+ *theorem* ideal.is_local.mem_jacobson_or_exists_inv
- \+ *def* ideal.is_local
- \+ *theorem* ideal.is_local_of_is_maximal_radical
- \+ *theorem* ideal.is_primary_of_is_maximal_radical
- \+ *lemma* ideal.jacobson.is_maximal
- \+ *def* ideal.jacobson
- \+ *lemma* ideal.jacobson_eq_bot
- \+ *theorem* ideal.jacobson_eq_top_iff
- \+ *lemma* ideal.jacobson_mono
- \+ *lemma* ideal.jacobson_top
- \+ *lemma* ideal.le_jacobson
- \+ *theorem* ideal.mem_jacobson_iff



## [2020-07-21 01:55:48](https://github.com/leanprover-community/mathlib/commit/0322d89)
refactor(topology/algebra/monoid): changed topological_monoid into has_continuous_mul ([#3481](https://github.com/leanprover-community/mathlib/pull/3481))
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/normed_space/basic.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* finset.measurable_prod
- \+/\- *lemma* measurable.mul
- \+/\- *lemma* measurable_mul

Modified src/topology/algebra/continuous_functions.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module.lean
- \+/\- *lemma* continuous_linear_map.add_comp
- \+/\- *lemma* continuous_linear_map.coe_coprod
- \+/\- *lemma* continuous_linear_map.comp_add
- \+/\- *def* continuous_linear_map.coprod
- \+/\- *lemma* continuous_linear_map.coprod_apply
- \+ *lemma* submodule.eq_top_of_nonempty_interior'
- \- *lemma* submodule.eq_top_of_nonempty_interior

Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/multilinear.lean


Modified src/topology/algebra/open_subgroup.lean
- \+/\- *lemma* open_subgroup.is_closed

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
- \+/\- *def* adjoin_root.mk

Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/ideals.lean
- \- *def* ideal.quotient.map_mk
- \+/\- *def* ideal.quotient.mk
- \- *lemma* ideal.quotient.mk_add
- \+ *theorem* ideal.quotient.mk_eq_mk
- \- *lemma* ideal.quotient.mk_eq_mk_hom
- \- *def* ideal.quotient.mk_hom
- \- *theorem* ideal.quotient.mk_mul
- \- *lemma* ideal.quotient.mk_neg
- \- *lemma* ideal.quotient.mk_one
- \- *lemma* ideal.quotient.mk_pow
- \- *lemma* ideal.quotient.mk_prod
- \- *lemma* ideal.quotient.mk_sub
- \- *lemma* ideal.quotient.mk_sum
- \- *lemma* ideal.quotient.mk_zero

Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/valuation/basic.lean




## [2020-07-21 01:05:07](https://github.com/leanprover-community/mathlib/commit/564ab02)
feat(category_theory/kernels): cokernel (image.ι f) ≅ cokernel f ([#3441](https://github.com/leanprover-community/mathlib/pull/3441))
#### Estimated changes
Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.cokernel_image_ι



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


Added test/library_search/filter.lean




## [2020-07-20 22:17:29](https://github.com/leanprover-community/mathlib/commit/2915fae)
feat(data/finset/basic): Cardinality of intersection with singleton ([#3480](https://github.com/leanprover-community/mathlib/pull/3480))
Intersecting with a singleton produces a set of cardinality either 0 or 1.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.card_singleton_inter



## [2020-07-20 20:30:53](https://github.com/leanprover-community/mathlib/commit/1f74ddd)
feat(topology/local_extr): add lemmas on composition with continuous functions ([#3459](https://github.com/leanprover-community/mathlib/pull/3459))
#### Estimated changes
Modified src/topology/local_extr.lean
- \+ *lemma* is_local_extr_on.comp_continuous_on
- \+ *lemma* is_local_max_on.comp_continuous_on
- \+ *lemma* is_local_min_on.comp_continuous_on



## [2020-07-20 18:42:24](https://github.com/leanprover-community/mathlib/commit/7aa85c2)
fix(algebra/group/units): add missing coe lemmas to units ([#3472](https://github.com/leanprover-community/mathlib/pull/3472))
Per @kbuzzard's suggestions [here](https://leanprover-community.github.io/archive/stream/113489-new-members/topic/Shortening.20proof.20on.20product.20of.20units.20in.20Z.html[#204406319](https://github.com/leanprover-community/mathlib/pull/204406319)):
- Add a new lemma `coe_eq_one` to `units` API
- Tag `eq_iff` with `norm_cast`
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* units.coe_eq_one
- \+ *theorem* units.eq_iff

Modified src/data/int/basic.lean




## [2020-07-20 17:56:13](https://github.com/leanprover-community/mathlib/commit/b66d1be)
feat(data/multivariate/qpf): definition ([#3395](https://github.com/leanprover-community/mathlib/pull/3395))
Part of [#3317](https://github.com/leanprover-community/mathlib/pull/3317)
#### Estimated changes
Modified src/control/functor/multivariate.lean


Added src/data/pfunctor/multivariate/basic.lean
- \+ *def* mvpfunctor.append_contents
- \+ *def* mvpfunctor.comp.get
- \+ *lemma* mvpfunctor.comp.get_map
- \+ *lemma* mvpfunctor.comp.get_mk
- \+ *def* mvpfunctor.comp.mk
- \+ *lemma* mvpfunctor.comp.mk_get
- \+ *def* mvpfunctor.comp
- \+ *theorem* mvpfunctor.comp_map
- \+ *def* mvpfunctor.const.get
- \+ *lemma* mvpfunctor.const.get_map
- \+ *lemma* mvpfunctor.const.get_mk
- \+ *def* mvpfunctor.const.mk
- \+ *lemma* mvpfunctor.const.mk_get
- \+ *def* mvpfunctor.const
- \+ *def* mvpfunctor.drop
- \+ *theorem* mvpfunctor.id_map
- \+ *def* mvpfunctor.last
- \+ *theorem* mvpfunctor.liftp_iff'
- \+ *theorem* mvpfunctor.liftp_iff
- \+ *theorem* mvpfunctor.liftr_iff
- \+ *def* mvpfunctor.map
- \+ *theorem* mvpfunctor.map_eq
- \+ *def* mvpfunctor.obj
- \+ *theorem* mvpfunctor.supp_eq
- \+ *structure* mvpfunctor

Modified src/data/pfunctor/univariate/basic.lean
- \+ *def* pfunctor.W.children
- \+ *def* pfunctor.W.head

Added src/data/qpf/multivariate/basic.lean
- \+ *theorem* mvqpf.comp_map
- \+ *theorem* mvqpf.has_good_supp_iff
- \+ *def* mvqpf.is_uniform
- \+ *theorem* mvqpf.liftp_iff
- \+ *theorem* mvqpf.liftp_iff_of_is_uniform
- \+ *def* mvqpf.liftp_preservation
- \+ *theorem* mvqpf.liftp_preservation_iff_uniform
- \+ *theorem* mvqpf.liftr_iff
- \+ *theorem* mvqpf.mem_supp
- \+ *theorem* mvqpf.supp_eq
- \+ *theorem* mvqpf.supp_eq_of_is_uniform
- \+ *theorem* mvqpf.supp_map
- \+ *def* mvqpf.supp_preservation
- \+ *theorem* mvqpf.supp_preservation_iff_liftp_preservation
- \+ *theorem* mvqpf.supp_preservation_iff_uniform



## [2020-07-20 15:42:49](https://github.com/leanprover-community/mathlib/commit/78f438b)
feat(tactic/squeeze_*): improve suggestions ([#3431](https://github.com/leanprover-community/mathlib/pull/3431))
This makes this gives `squeeze_simp`, `squeeze_simpa` and `squeeze_dsimp` the `?` optional argument that indicates that we should consider all `simp` lemmas that are also `_refl_lemma`
#### Estimated changes
Modified src/tactic/squeeze.lean




## [2020-07-20 14:17:48](https://github.com/leanprover-community/mathlib/commit/d0df6b8)
feat(data/equiv/mul_add): refl_apply and trans_apply ([#3470](https://github.com/leanprover-community/mathlib/pull/3470))
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *theorem* mul_equiv.refl_apply
- \+ *theorem* mul_equiv.trans_apply



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
- \+/\- *theorem* cardinal.one_lt_omega
- \+/\- *theorem* cardinal.zero_lt_one

Modified src/set_theory/ordinal.lean
- \+ *theorem* cardinal.bit0_eq_self
- \+ *lemma* cardinal.bit0_le_bit0
- \+ *lemma* cardinal.bit0_le_bit1
- \+ *lemma* cardinal.bit0_lt_bit0
- \+ *lemma* cardinal.bit0_lt_bit1
- \+ *theorem* cardinal.bit0_lt_omega
- \+ *lemma* cardinal.bit0_ne_zero
- \+ *theorem* cardinal.bit1_eq_self_iff
- \+ *lemma* cardinal.bit1_le_bit0
- \+ *lemma* cardinal.bit1_le_bit1
- \+ *lemma* cardinal.bit1_lt_bit0
- \+ *lemma* cardinal.bit1_lt_bit1
- \+ *theorem* cardinal.bit1_lt_omega
- \+ *lemma* cardinal.bit1_ne_zero
- \+ *theorem* cardinal.omega_le_bit0
- \+ *theorem* cardinal.omega_le_bit1
- \+ *lemma* cardinal.one_le_bit0
- \+ *lemma* cardinal.one_le_bit1
- \+ *lemma* cardinal.one_le_one
- \+ *lemma* cardinal.one_lt_bit0
- \+ *lemma* cardinal.one_lt_bit1
- \+ *lemma* cardinal.one_lt_two
- \+ *lemma* cardinal.zero_lt_bit0
- \+ *lemma* cardinal.zero_lt_bit1



## [2020-07-20 14:17:41](https://github.com/leanprover-community/mathlib/commit/9a92363)
feat(logic/basic): nonempty.some ([#3449](https://github.com/leanprover-community/mathlib/pull/3449))
Could we please have this? I've a number of times been annoyed by the difficulty of extracting an element from a `nonempty`.
(Criterion for alternative solutions: `library_search` solves `nonempty X -> X`.)
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* Exists.some_spec



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
- \+ *lemma* affine_space.affine_combination_mem_affine_span
- \+ *lemma* affine_space.affine_span_nonempty
- \+ *lemma* affine_space.eq_affine_combination_of_mem_affine_span
- \+ *lemma* affine_space.mem_affine_span_iff_eq_affine_combination
- \+ *lemma* affine_space.mem_vector_span_iff_eq_weighted_vsub
- \+ *lemma* affine_space.span_points_nonempty
- \- *lemma* affine_space.span_points_nonempty_of_nonempty
- \+ *lemma* affine_space.vector_span_empty
- \+ *lemma* affine_space.vector_span_eq_span_vsub_set_left
- \+ *lemma* affine_space.vector_span_eq_span_vsub_set_right
- \+ *lemma* affine_space.vector_span_range_eq_span_range_vsub_left
- \+ *lemma* affine_space.vector_span_range_eq_span_range_vsub_right
- \+ *lemma* affine_space.weighted_vsub_mem_vector_span
- \+ *lemma* finset.affine_combination_apply
- \+ *lemma* finset.affine_combination_indicator_subset
- \+ *lemma* finset.affine_combination_of_eq_one_of_eq_zero
- \+ *lemma* finset.weighted_vsub_empty
- \+ *lemma* finset.weighted_vsub_indicator_subset
- \+ *lemma* finset.weighted_vsub_of_point_indicator_subset



## [2020-07-20 12:54:49](https://github.com/leanprover-community/mathlib/commit/65208ed)
refactor(data/polynomial/*): further refactors ([#3435](https://github.com/leanprover-community/mathlib/pull/3435))
There's a lot further to go, but I need to do other things for a while so will PR what I have so far.
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.X_ne_zero
- \+ *lemma* polynomial.coeff_X
- \+ *lemma* polynomial.coeff_X_one
- \+ *lemma* polynomial.coeff_X_zero

Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.coeff_X_mul_zero
- \+/\- *lemma* polynomial.coeff_X_pow
- \+ *lemma* polynomial.coeff_X_pow_self
- \+/\- *lemma* polynomial.coeff_mul_X_zero

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
- \- *lemma* polynomial.X_ne_zero
- \- *lemma* polynomial.coeff_X
- \- *lemma* polynomial.coeff_X_one
- \- *lemma* polynomial.coeff_X_zero

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
- \+ *lemma* submodule.sum_smul_mem



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
- \- *def* test.library_search.lt_one
- \+ *theorem* test.library_search.nonzero_gt_one
- \- *lemma* test.library_search.zero_lt_one

Added test/library_search/nat.lean
- \+ *def* test.library_search.lt_one
- \+ *lemma* test.library_search.zero_lt_one



## [2020-07-20 06:04:37](https://github.com/leanprover-community/mathlib/commit/5080dd5)
feat(data/padics/padic_norm): lemmas about padic_val_nat ([#3230](https://github.com/leanprover-community/mathlib/pull/3230))
Collection of lemmas about `padic_val_nat`, culminating in `lemma prod_pow_prime_padic_val_nat : ∀ (n : nat) (s : n ≠ 0) (m : nat) (pr : n < m),  ∏ p in finset.filter nat.prime (finset.range m), pow p (padic_val_nat p n) = n`.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_multiset_count

Modified src/algebra/char_zero.lean
- \+ *theorem* nat.cast_dvd_char_zero

Modified src/data/nat/basic.lean
- \+ *lemma* nat.div_div_div_eq_div

Modified src/data/nat/cast.lean
- \+ *theorem* nat.cast_dvd

Modified src/data/nat/gcd.lean
- \+ *theorem* nat.coprime.coprime_div_left
- \+ *theorem* nat.coprime.coprime_div_right

Modified src/data/nat/prime.lean
- \+ *lemma* nat.factors_add_two
- \+ *theorem* nat.prime_dvd_prime_iff_eq

Modified src/data/padics/padic_norm.lean
- \+ *lemma* one_le_padic_val_nat_of_dvd
- \+ *lemma* padic_val_nat_eq_factors_count
- \+ *lemma* padic_val_nat_of_not_dvd
- \+ *lemma* padic_val_nat_one
- \+ *lemma* padic_val_nat_primes
- \+ *lemma* padic_val_nat_zero
- \+ *lemma* prod_pow_prime_padic_val_nat



## [2020-07-20 05:06:14](https://github.com/leanprover-community/mathlib/commit/84d4ea7)
feat(data/nat/digits): a bigger number has more digits ([#3457](https://github.com/leanprover-community/mathlib/pull/3457))
#### Estimated changes
Modified src/data/nat/digits.lean
- \+ *lemma* digits_len_le_digits_len_succ
- \+ *lemma* digits_one
- \+/\- *lemma* digits_one_succ
- \+ *lemma* digits_zero_succ
- \+ *lemma* digits_zero_zero
- \+ *lemma* le_digits_len_le



## [2020-07-20 05:06:12](https://github.com/leanprover-community/mathlib/commit/792f541)
feat(field_theory/tower): tower law ([#3355](https://github.com/leanprover-community/mathlib/pull/3355))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_extend_by_one

Modified src/algebra/pointwise.lean
- \+ *theorem* set.range_smul_range

Modified src/data/finset/basic.lean
- \+ *theorem* finset.subset_product

Added src/field_theory/tower.lean
- \+ *theorem* dim_mul_dim'
- \+ *theorem* dim_mul_dim
- \+ *theorem* finite_dimensional.findim_mul_findim
- \+ *theorem* finite_dimensional.trans

Modified src/linear_algebra/basis.lean
- \+ *theorem* linear_independent_iff''

Modified src/ring_theory/algebra_tower.lean
- \+/\- *theorem* is_algebra_tower.algebra_map_apply
- \+/\- *theorem* is_algebra_tower.algebra_map_eq
- \+ *theorem* is_algebra_tower.algebra_map_smul
- \+ *theorem* is_algebra_tower.smul_left_comm
- \+ *theorem* is_basis.smul
- \+ *theorem* linear_independent_smul
- \+ *def* submodule.restrict_scalars'
- \+ *theorem* submodule.restrict_scalars'_inj
- \+ *theorem* submodule.restrict_scalars'_injective
- \+ *theorem* submodule.restrict_scalars'_top
- \+ *theorem* submodule.smul_mem_span_smul'
- \+ *theorem* submodule.smul_mem_span_smul
- \+ *theorem* submodule.smul_mem_span_smul_of_mem
- \+ *theorem* submodule.span_smul



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


Added src/tactic/unfold_cases.lean


Added test/unfold_cases.lean
- \+ *def* balance_eqn_compiler
- \+ *def* balance_match
- \+ *def* bar
- \+ *def* baz
- \+ *inductive* color
- \+ *def* foo
- \+ *inductive* node



## [2020-07-20 00:16:06](https://github.com/leanprover-community/mathlib/commit/2975f93)
chore(tactic/interactive): move non-monadic part of `clean` to `expr.clean` ([#3461](https://github.com/leanprover-community/mathlib/pull/3461))
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/interactive.lean




## [2020-07-20 00:16:04](https://github.com/leanprover-community/mathlib/commit/db18144)
chore(order/bounded_lattice): add `is_compl.inf_left_eq_bot_iff` etc ([#3460](https://github.com/leanprover-community/mathlib/pull/3460))
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+ *lemma* is_compl.disjoint_left_iff
- \+ *lemma* is_compl.disjoint_right_iff
- \+ *lemma* is_compl.inf_left_eq_bot_iff
- \+ *lemma* is_compl.inf_right_eq_bot_iff

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
- \+ *lemma* normed_field.nhds_within_is_unit_ne_bot
- \- *lemma* submodule.eq_top_of_nonempty_interior

Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/specific_limits.lean


Modified src/data/padics/hensel.lean


Modified src/data/real/hyperreal.lean
- \+/\- *lemma* hyperreal.coe_le_coe

Modified src/data/set/basic.lean
- \+ *lemma* set.nonempty_of_not_subset

Modified src/data/set/finite.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/dynamics/fixed_points/topology.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* filter.at_top_ne_bot

Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.comap_ne_bot
- \+/\- *lemma* filter.comap_ne_bot_iff
- \- *lemma* filter.comap_ne_bot_of_image_mem
- \- *lemma* filter.comap_ne_bot_of_range_mem
- \- *lemma* filter.comap_ne_bot_of_surj
- \+/\- *lemma* filter.eventually.exists
- \+/\- *lemma* filter.eventually.frequently
- \+/\- *lemma* filter.eventually_const
- \+/\- *lemma* filter.frequently_const
- \+/\- *lemma* filter.frequently_imp_distrib_left
- \+/\- *lemma* filter.frequently_imp_distrib_right
- \+/\- *lemma* filter.frequently_of_forall
- \+/\- *lemma* filter.frequently_or_distrib_left
- \+/\- *lemma* filter.frequently_or_distrib_right
- \+/\- *lemma* filter.frequently_true_iff_ne_bot
- \+/\- *lemma* filter.infi_ne_bot_iff_of_directed'
- \+/\- *lemma* filter.infi_ne_bot_iff_of_directed
- \+/\- *lemma* filter.infi_ne_bot_of_directed'
- \- *lemma* filter.map_ne_bot
- \+/\- *lemma* filter.map_ne_bot_iff
- \+ *lemma* filter.ne_bot.comap_of_image_mem
- \+ *lemma* filter.ne_bot.comap_of_range_mem
- \+ *lemma* filter.ne_bot.comap_of_surj
- \+ *lemma* filter.ne_bot.map
- \+ *lemma* filter.ne_bot.mono
- \+ *lemma* filter.ne_bot.ne
- \+ *lemma* filter.ne_bot.nonempty_of_mem
- \+ *lemma* filter.ne_bot.prod
- \+ *def* filter.ne_bot
- \+ *lemma* filter.ne_bot_of_le
- \+/\- *lemma* filter.nonempty_of_mem_sets
- \+/\- *lemma* filter.nonempty_of_ne_bot
- \+/\- *lemma* filter.principal_ne_bot_iff
- \+/\- *lemma* filter.prod_ne_bot
- \- *lemma* filter.pure_ne_bot
- \+/\- *lemma* filter.tendsto.ne_bot

Modified src/order/filter/cofinite.lean
- \- *lemma* filter.cofinite_ne_bot

Modified src/order/filter/filter_product.lean


Modified src/order/filter/germ.lean
- \+/\- *lemma* filter.const_eventually_eq'
- \+/\- *lemma* filter.const_eventually_eq
- \+/\- *lemma* filter.germ.const_inj
- \+/\- *lemma* filter.germ.const_le_iff
- \+/\- *lemma* filter.germ.lift_pred_const_iff
- \+/\- *lemma* filter.germ.lift_rel_const_iff

Modified src/order/filter/lift.lean
- \+/\- *lemma* filter.lift'_ne_bot_iff
- \+/\- *lemma* filter.lift_ne_bot_iff

Modified src/order/filter/pointwise.lean
- \- *lemma* filter.mul_ne_bot
- \+ *lemma* filter.ne_bot.mul

Modified src/order/filter/ultrafilter.lean
- \+/\- *lemma* filter.exists_ultrafilter
- \+/\- *lemma* filter.exists_ultrafilter_iff
- \+/\- *lemma* filter.hyperfilter_ne_bot
- \+ *lemma* filter.is_ultrafilter.unique
- \+/\- *def* filter.is_ultrafilter
- \+/\- *lemma* filter.le_of_ultrafilter
- \+/\- *lemma* filter.ultrafilter_of_spec
- \+ *lemma* filter.ultrafilter_ultrafilter_of'
- \+/\- *lemma* filter.ultrafilter_ultrafilter_of
- \- *lemma* filter.ultrafilter_unique

Modified src/order/liminf_limsup.lean
- \+/\- *theorem* filter.Liminf_le_Limsup
- \+/\- *lemma* filter.is_cobounded_of_is_bounded
- \+/\- *lemma* filter.liminf_const
- \+/\- *lemma* filter.liminf_le_limsup
- \+/\- *lemma* filter.limsup_const

Modified src/order/zorn.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module.lean
- \- *lemma* submodule.eq_top_of_nonempty_interior'
- \+ *lemma* submodule.eq_top_of_nonempty_interior

Modified src/topology/algebra/ordered.lean
- \+/\- *theorem* Liminf_eq_of_le_nhds
- \+/\- *theorem* Limsup_eq_of_le_nhds
- \+/\- *theorem* filter.tendsto.liminf_eq
- \+/\- *theorem* filter.tendsto.limsup_eq
- \+/\- *lemma* ge_of_tendsto'
- \+/\- *lemma* ge_of_tendsto
- \+/\- *lemma* le_of_tendsto_of_tendsto'
- \+/\- *lemma* le_of_tendsto_of_tendsto

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean
- \+ *lemma* cluster_pt.ne_bot
- \+ *lemma* cluster_pt.of_le_nhds'
- \+/\- *lemma* cluster_pt.of_le_nhds
- \+/\- *def* cluster_pt
- \- *lemma* nhds_ne_bot

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/continuous_on.lean


Modified src/topology/dense_embedding.lean
- \+/\- *lemma* dense_inducing.comap_nhds_ne_bot
- \+ *lemma* dense_range.nhds_within_ne_bot

Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/cau_seq_filter.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/order.lean


Modified src/topology/separation.lean
- \+/\- *lemma* Lim_eq
- \+/\- *lemma* eq_of_nhds_ne_bot
- \+/\- *lemma* t2_iff_nhds
- \+ *lemma* tendsto_nhds_unique'

Modified src/topology/sequences.lean


Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean
- \+/\- *lemma* is_compact.inter_right
- \+/\- *lemma* is_compact.prod
- \+/\- *def* is_compact

Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy.comap'
- \+ *lemma* cauchy.comap
- \+ *lemma* cauchy.map
- \+ *lemma* cauchy.mono'
- \+ *lemma* cauchy.mono
- \+/\- *def* cauchy
- \- *lemma* cauchy_comap
- \- *lemma* cauchy_downwards
- \+/\- *lemma* cauchy_iff_exists_le_nhds
- \- *lemma* cauchy_map
- \+ *lemma* cauchy_map_iff'
- \+/\- *lemma* cauchy_map_iff_exists_tendsto
- \+/\- *def* sequentially_complete.seq
- \+ *lemma* totally_bounded.closure
- \+ *lemma* totally_bounded.image
- \- *lemma* totally_bounded_closure
- \- *lemma* totally_bounded_image

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
- \+ *lemma* local_homeomorph.image_open_of_open'
- \+ *lemma* local_homeomorph.source_preimage_target
- \+ *lemma* local_homeomorph.subtype_restr_coe
- \+ *lemma* local_homeomorph.subtype_restr_def
- \+ *lemma* local_homeomorph.subtype_restr_source
- \+ *lemma* local_homeomorph.subtype_restr_symm_trans_subtype_restr
- \+ *lemma* local_homeomorph.to_open_embedding
- \+ *lemma* open_embedding.continuous_inv_fun
- \+ *lemma* open_embedding.open_target
- \+ *lemma* open_embedding.source
- \+ *lemma* open_embedding.target
- \+ *lemma* open_embedding.to_local_equiv_coe
- \+ *lemma* open_embedding.to_local_equiv_source
- \+ *lemma* open_embedding.to_local_equiv_target
- \+ *lemma* open_embedding.to_local_homeomorph_coe
- \+ *lemma* topological_space.opens.local_homeomorph_subtype_coe_coe
- \+ *lemma* topological_space.opens.local_homeomorph_subtype_coe_source
- \+ *lemma* topological_space.opens.local_homeomorph_subtype_coe_target



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


Added test/apply_rules.lean


Modified test/tactics.lean




## [2020-07-19 15:29:48](https://github.com/leanprover-community/mathlib/commit/9b0435a)
fix(tactic/linarith): find correct zero_lt_one ([#3455](https://github.com/leanprover-community/mathlib/pull/3455))
Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/linarith.20and.20ordinal.20file
#### Estimated changes
Modified src/tactic/linarith/verification.lean


Modified test/linarith.lean
- \+ *lemma* T.works
- \+ *lemma* T.zero_lt_one



## [2020-07-19 14:44:28](https://github.com/leanprover-community/mathlib/commit/47ea2a6)
feat(topology, analysis) : add lemmas about `has_neg.neg` (preliminaries for L'Hopital's rule) ([#3392](https://github.com/leanprover-community/mathlib/pull/3392))
This PR contains a few lemmas about the `has_neg.neg` function, such as : 
- its limit along `at_top` and `at_bot`
- its limit along `nhds a`, `nhds_within a (Ioi a)` and similar filters
- its differentiability and derivative
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv.neg'
- \+ *lemma* deriv.neg
- \+ *lemma* deriv_neg''
- \+/\- *lemma* deriv_neg'
- \+/\- *lemma* deriv_neg
- \+ *lemma* deriv_within.neg
- \+/\- *lemma* deriv_within_neg
- \+ *lemma* differentiable_neg
- \+ *lemma* differentiable_on_neg
- \+ *theorem* has_deriv_at_filter_neg
- \+ *theorem* has_deriv_at_neg'
- \+ *theorem* has_deriv_at_neg
- \+ *theorem* has_deriv_within_at_neg
- \+ *theorem* has_strict_deriv_at_neg

Modified src/analysis/calculus/mean_value.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* filter.eventually.exists_forall_of_at_top
- \+/\- *lemma* filter.eventually_at_top
- \+ *lemma* filter.eventually_ge_at_top
- \+/\- *lemma* filter.frequently.forall_exists_of_at_top
- \+/\- *lemma* filter.frequently_at_top'
- \+/\- *lemma* filter.frequently_at_top
- \+ *lemma* filter.tendsto_at_bot'
- \+ *lemma* filter.tendsto_at_bot
- \+ *lemma* filter.tendsto_at_bot_at_bot
- \+ *lemma* filter.tendsto_at_bot_at_top
- \+/\- *lemma* filter.tendsto_at_top_at_bot
- \+/\- *lemma* filter.tendsto_at_top_at_top_of_monotone'
- \+/\- *lemma* filter.tendsto_at_top_embedding
- \+/\- *lemma* filter.tendsto_at_top_of_monotone_of_filter
- \+/\- *lemma* filter.tendsto_at_top_of_monotone_of_subseq
- \+/\- *lemma* filter.tendsto_at_top_pure
- \+ *lemma* filter.tendsto_neg_at_bot_at_top
- \+ *lemma* filter.tendsto_neg_at_top_at_bot
- \+/\- *lemma* filter.unbounded_of_tendsto_at_top

Modified src/topology/algebra/group.lean
- \+ *lemma* continuous_on_inv
- \+ *lemma* tendsto_inv

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_inv_nhds_within_Iio
- \+ *lemma* tendsto_inv_nhds_within_Iio_inv
- \+ *lemma* tendsto_inv_nhds_within_Ioi
- \+ *lemma* tendsto_inv_nhds_within_Ioi_inv



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
- \+/\- *lemma* submodule.span_singleton_eq_bot
- \+ *lemma* submodule.span_zero

Modified src/linear_algebra/basis.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideals.lean
- \+/\- *lemma* ideal.span_singleton_eq_bot
- \+ *lemma* ideal.span_zero



## [2020-07-19 06:24:31](https://github.com/leanprover-community/mathlib/commit/3354476)
feat(data/indicator_function): more lemmas ([#3424](https://github.com/leanprover-community/mathlib/pull/3424))
Add some lemmas of use when using `set.indicator` to manipulate
functions involved in summations.
#### Estimated changes
Modified src/data/indicator_function.lean
- \+ *lemma* set.mem_of_indicator_ne_zero
- \+ *lemma* set.sum_indicator_subset
- \+ *lemma* set.sum_indicator_subset_of_eq_zero



## [2020-07-19 05:43:15](https://github.com/leanprover-community/mathlib/commit/8312419)
refactor(data/polynomial): remove has_coe_to_fun, and @[reducible] on monomial ([#3420](https://github.com/leanprover-community/mathlib/pull/3420))
I'm going to refactor in stages, trying to clean up some of the cruftier aspects of `data/polynomial/*`.
This PR:
1. removes the `has_coe_to_fun` on polynomial
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \- *lemma* polynomial.apply_eq_coeff
- \- *def* polynomial.coeff_coe_to_fun
- \+ *lemma* polynomial.coeff_monomial
- \+/\- *lemma* polynomial.coeff_one_zero
- \+ *lemma* polynomial.monomial_mul_monomial

Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/degree/basic.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/div.lean
- \+ *lemma* polynomial.apply_eq_coeff
- \+ *def* polynomial.coeff_coe_to_fun

Modified src/data/polynomial/eval.lean


Modified src/data/polynomial/monomial.lean
- \+/\- *lemma* polynomial.coeff_C_zero
- \+/\- *lemma* polynomial.coeff_X
- \+/\- *lemma* polynomial.coeff_X_one
- \+/\- *lemma* polynomial.coeff_X_zero

Modified src/ring_theory/polynomial_algebra.lean




## [2020-07-19 04:53:42](https://github.com/leanprover-community/mathlib/commit/eca55c9)
feat(category_theory/equivalence): injectivity simp lemmas for equivalences ([#3437](https://github.com/leanprover-community/mathlib/pull/3437))
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+ *lemma* category_theory.equivalence.functor_map_inj_iff
- \+ *lemma* category_theory.equivalence.inverse_map_inj_iff



## [2020-07-19 04:53:40](https://github.com/leanprover-community/mathlib/commit/eb68f4c)
feat (linear_algebra/matrix): make diag and trace compatible with semirings ([#3433](https://github.com/leanprover-community/mathlib/pull/3433))
changes ring and related instances to semiring etc. in requirements for matrix.diag and matrix.trace
#### Estimated changes
Modified src/linear_algebra/matrix.lean
- \+/\- *def* matrix.diag
- \+/\- *def* matrix.trace



## [2020-07-19 04:53:38](https://github.com/leanprover-community/mathlib/commit/e6bfe18)
feat(topology/algebra/module): pi and proj for CLM ([#3430](https://github.com/leanprover-community/mathlib/pull/3430))
#### Estimated changes
Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.infi_ker_proj
- \+ *def* continuous_linear_map.infi_ker_proj_equiv
- \+ *def* continuous_linear_map.pi
- \+ *lemma* continuous_linear_map.pi_apply
- \+ *lemma* continuous_linear_map.pi_comp
- \+ *lemma* continuous_linear_map.pi_eq_zero
- \+ *lemma* continuous_linear_map.pi_zero
- \+ *def* continuous_linear_map.proj
- \+ *lemma* continuous_linear_map.proj_apply
- \+ *lemma* continuous_linear_map.proj_pi



## [2020-07-19 03:42:37](https://github.com/leanprover-community/mathlib/commit/f83cf57)
feat(data/equiv/mul_add): minor lemmas ([#3447](https://github.com/leanprover-community/mathlib/pull/3447))
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *lemma* add_aut.apply_inv_self
- \+ *lemma* add_aut.inv_apply_self
- \+ *lemma* mul_aut.apply_inv_self
- \+ *lemma* mul_aut.inv_apply_self



## [2020-07-19 03:42:35](https://github.com/leanprover-community/mathlib/commit/61bd966)
feat(data/list/basic): add concat lemmas ([#3445](https://github.com/leanprover-community/mathlib/pull/3445))
The first two are taken after the `head_eq_of_cons_eq` and `tail_eq_of_cons_eq` lemmas further up in the file.
The third, `reverse_concat`, is like `reverse_cons'` but with the `::` and `concat` swapped.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.init_eq_of_concat_eq
- \+ *theorem* list.last_eq_of_concat_eq
- \+ *theorem* list.reverse_concat



## [2020-07-19 03:15:24](https://github.com/leanprover-community/mathlib/commit/91ca927)
feat(geometry/manifold/local_invariant_properties):  local structomorphism is `local_invariant_prop` ([#3434](https://github.com/leanprover-community/mathlib/pull/3434))
For a groupoid `G`, define the property of being a local structomorphism; prove that if `G` is closed under restriction then this property satisfies `local_invariant_prop` (i.e., is local and `G`-invariant).
#### Estimated changes
Modified src/geometry/manifold/charted_space.lean
- \+ *lemma* closed_under_restriction'

Modified src/geometry/manifold/local_invariant_properties.lean
- \+ *def* structure_groupoid.is_local_structomorph_within_at
- \+ *lemma* structure_groupoid.is_local_structomorph_within_at_local_invariant_prop



## [2020-07-18 16:49:37](https://github.com/leanprover-community/mathlib/commit/4760a33)
feat(algebra/polynomial, data/polynomial): lemmas about monic polynomials ([#3402](https://github.com/leanprover-community/mathlib/pull/3402))
#### Estimated changes
Modified src/algebra/char_p.lean
- \+ *theorem* add_pow_char_of_commute

Deleted src/algebra/polynomial/basic.lean
- \- *lemma* polynomial.coe_aeval_eq_eval
- \- *lemma* polynomial.coeff_zero_eq_aeval_zero
- \- *def* polynomial.leading_coeff_hom
- \- *lemma* polynomial.leading_coeff_hom_apply

Modified src/algebra/polynomial/big_operators.lean
- \- *lemma* polynomial.monic_prod_of_monic
- \+ *lemma* polynomial.nat_degree_prod'
- \+ *lemma* polynomial.nat_degree_prod
- \- *lemma* polynomial.nat_degree_prod_eq'
- \- *lemma* polynomial.nat_degree_prod_eq
- \- *lemma* polynomial.nat_degree_prod_eq_of_monic
- \+ *lemma* polynomial.nat_degree_prod_of_monic
- \+ *lemma* polynomial.prod_X_sub_C_coeff_card_pred
- \+ *lemma* polynomial.prod_X_sub_C_next_coeff

Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* polynomial.coe_aeval_eq_eval
- \+ *lemma* polynomial.coeff_zero_eq_aeval_zero
- \+ *lemma* polynomial.pow_comp

Modified src/data/polynomial/degree.lean
- \+ *lemma* polynomial.degree_mul'
- \+ *lemma* polynomial.degree_mul
- \- *lemma* polynomial.degree_mul_eq'
- \+ *lemma* polynomial.degree_pow'
- \+ *lemma* polynomial.degree_pow
- \- *lemma* polynomial.degree_pow_eq'
- \+ *def* polynomial.leading_coeff_hom
- \+ *lemma* polynomial.leading_coeff_hom_apply
- \+ *lemma* polynomial.leading_coeff_mul
- \+ *lemma* polynomial.leading_coeff_pow
- \+ *lemma* polynomial.nat_degree_mul'
- \- *lemma* polynomial.nat_degree_mul_eq'
- \+ *lemma* polynomial.nat_degree_pow'
- \- *lemma* polynomial.nat_degree_pow_eq'
- \+ *lemma* polynomial.next_coeff_X_sub_C

Modified src/data/polynomial/degree/basic.lean
- \+ *def* polynomial.next_coeff
- \+ *lemma* polynomial.next_coeff_C_eq_zero
- \+ *lemma* polynomial.next_coeff_of_pos_nat_degree

Modified src/data/polynomial/div.lean


Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/monic.lean
- \+ *lemma* polynomial.monic.coeff_nat_degree
- \+ *lemma* polynomial.monic.degree_eq_zero_iff_eq_one
- \+ *lemma* polynomial.monic.nat_degree_mul
- \+ *lemma* polynomial.monic.next_coeff_mul
- \+ *lemma* polynomial.monic.next_coeff_prod
- \+ *lemma* polynomial.monic_prod_of_monic

Modified src/data/polynomial/ring_division.lean
- \- *lemma* polynomial.degree_mul_eq
- \- *lemma* polynomial.degree_pow_eq
- \- *lemma* polynomial.leading_coeff_mul
- \- *lemma* polynomial.leading_coeff_pow
- \+ *lemma* polynomial.nat_degree_mul
- \- *lemma* polynomial.nat_degree_mul_eq
- \+ *lemma* polynomial.nat_degree_pow
- \- *lemma* polynomial.nat_degree_pow_eq

Modified src/linear_algebra/lagrange.lean


Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/polynomial/basic.lean




## [2020-07-18 16:19:16](https://github.com/leanprover-community/mathlib/commit/37cf166)
feat(data/complex/exponential): added @[mono] tag to exp_le_exp and exp_lt_exp ([#3318](https://github.com/leanprover-community/mathlib/pull/3318))
added @[mono] tag to exp_le_exp and exp_lt_exp.
#### Estimated changes
Modified src/data/complex/exponential.lean
- \+ *lemma* real.exp_monotone



## [2020-07-18 12:28:11](https://github.com/leanprover-community/mathlib/commit/e3e0aa0)
chore(linear_algebra/direct_sum_module): add dosctrings ([#3418](https://github.com/leanprover-community/mathlib/pull/3418))
#### Estimated changes
Modified src/linear_algebra/direct_sum_module.lean
- \+/\- *def* direct_sum.lmk



## [2020-07-18 11:26:57](https://github.com/leanprover-community/mathlib/commit/21a1683)
feat(data/finsupp): sums over on_finset ([#3427](https://github.com/leanprover-community/mathlib/pull/3427))
There aren't many lemmas about `finsupp.on_finset`.  Add one that's
useful for manipulating sums over `on_finset`.
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* finsupp.on_finset_sum



## [2020-07-18 11:26:55](https://github.com/leanprover-community/mathlib/commit/4767b30)
feat(algebra/big_operators): more general prod_insert_one ([#3426](https://github.com/leanprover-community/mathlib/pull/3426))
I found I had a use for a slightly more general version of
`prod_insert_one` / `sum_insert_zero`.  Add that version and use it in
the proof of `prod_insert_one`.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_insert_of_eq_one_if_not_mem



## [2020-07-18 10:34:10](https://github.com/leanprover-community/mathlib/commit/f81568a)
feat(group_theory/semidirect_product): mk_eq_inl_mul_inr and hom_ext ([#3408](https://github.com/leanprover-community/mathlib/pull/3408))
#### Estimated changes
Modified src/group_theory/semidirect_product.lean
- \+ *lemma* semidirect_product.hom_ext
- \+ *lemma* semidirect_product.mk_eq_inl_mul_inr



## [2020-07-18 09:27:48](https://github.com/leanprover-community/mathlib/commit/907147a)
feat(linear_algebra/matrix): define equivalences for reindexing matrices with equivalent types ([#3409](https://github.com/leanprover-community/mathlib/pull/3409))
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+ *def* matrix.reindex_lie_equiv
- \+ *lemma* matrix.reindex_lie_equiv_apply
- \+ *lemma* matrix.reindex_lie_equiv_symm_apply

Modified src/linear_algebra/matrix.lean
- \+ *def* matrix.reindex
- \+ *def* matrix.reindex_alg_equiv
- \+ *lemma* matrix.reindex_alg_equiv_apply
- \+ *lemma* matrix.reindex_alg_equiv_symm_apply
- \+ *lemma* matrix.reindex_apply
- \+ *def* matrix.reindex_linear_equiv
- \+ *lemma* matrix.reindex_linear_equiv_apply
- \+ *lemma* matrix.reindex_linear_equiv_symm_apply
- \+ *lemma* matrix.reindex_mul
- \+ *lemma* matrix.reindex_symm_apply



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
- \+ *lemma* semidirect_product.inl_aut_inv
- \+/\- *lemma* semidirect_product.inl_left_mul_inr_right



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
- \- *theorem* rat.exists_mul_self
- \- *def* rat.sqrt
- \- *theorem* rat.sqrt_eq
- \- *theorem* rat.sqrt_nonneg

Added src/data/rat/sqrt.lean
- \+ *theorem* rat.exists_mul_self
- \+ *def* rat.sqrt
- \+ *theorem* rat.sqrt_eq
- \+ *theorem* rat.sqrt_nonneg

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
- \+ *lemma* finset.eq_empty_of_not_nonempty



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
- \+ *lemma* linear_map.coe_injective

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.extend_unique

Modified src/data/indicator_function.lean
- \+ *lemma* add_monoid_hom.map_indicator
- \+ *lemma* set.indicator_le'
- \+ *lemma* set.indicator_le
- \+ *lemma* set.indicator_le_self'
- \+ *lemma* set.indicator_le_self

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.coe_indicator

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.coe_indicator

Modified src/data/set/basic.lean
- \- *lemma* set.if_preimage
- \+ *theorem* set.set_of_true
- \- *theorem* set.univ_def

Modified src/data/set/function.lean
- \+ *lemma* set.piecewise_preimage

Modified src/measure_theory/ae_eq_fun.lean
- \- *lemma* measure_theory.ae_eq_fun.add_to_fun
- \- *lemma* measure_theory.ae_eq_fun.all_ae_mk_to_fun
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_comp
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_comp₂
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_const
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_edist
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_inv
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_le
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_mk
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_mul
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_one
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_pair
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_pos_part
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_smul
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_sub
- \+/\- *def* measure_theory.ae_eq_fun.comp
- \- *def* measure_theory.ae_eq_fun.comp_edist
- \- *lemma* measure_theory.ae_eq_fun.comp_edist_self
- \- *lemma* measure_theory.ae_eq_fun.comp_edist_to_fun
- \+ *lemma* measure_theory.ae_eq_fun.comp_eq_mk
- \- *lemma* measure_theory.ae_eq_fun.comp_eq_mk_to_fun
- \+/\- *lemma* measure_theory.ae_eq_fun.comp_mk
- \- *lemma* measure_theory.ae_eq_fun.comp_to_fun
- \+ *lemma* measure_theory.ae_eq_fun.comp_to_germ
- \+/\- *def* measure_theory.ae_eq_fun.comp₂
- \+ *lemma* measure_theory.ae_eq_fun.comp₂_eq_mk
- \- *lemma* measure_theory.ae_eq_fun.comp₂_eq_mk_to_fun
- \+ *lemma* measure_theory.ae_eq_fun.comp₂_eq_pair
- \- *lemma* measure_theory.ae_eq_fun.comp₂_to_fun
- \+ *lemma* measure_theory.ae_eq_fun.comp₂_to_germ
- \+/\- *def* measure_theory.ae_eq_fun.const
- \- *lemma* measure_theory.ae_eq_fun.const_to_fun
- \+ *lemma* measure_theory.ae_eq_fun.edist_add_right
- \- *lemma* measure_theory.ae_eq_fun.edist_eq_add_add
- \+ *lemma* measure_theory.ae_eq_fun.edist_eq_coe'
- \+ *lemma* measure_theory.ae_eq_fun.edist_eq_coe
- \+/\- *lemma* measure_theory.ae_eq_fun.edist_mk_mk
- \+/\- *lemma* measure_theory.ae_eq_fun.edist_smul
- \- *lemma* measure_theory.ae_eq_fun.edist_to_fun'
- \- *lemma* measure_theory.ae_eq_fun.edist_to_fun
- \+ *lemma* measure_theory.ae_eq_fun.edist_zero_eq_coe
- \- *lemma* measure_theory.ae_eq_fun.edist_zero_to_fun
- \- *def* measure_theory.ae_eq_fun.eintegral
- \- *lemma* measure_theory.ae_eq_fun.eintegral_add
- \- *lemma* measure_theory.ae_eq_fun.eintegral_eq_zero_iff
- \- *lemma* measure_theory.ae_eq_fun.eintegral_le_eintegral
- \- *lemma* measure_theory.ae_eq_fun.eintegral_mk
- \- *lemma* measure_theory.ae_eq_fun.eintegral_to_fun
- \- *lemma* measure_theory.ae_eq_fun.eintegral_zero
- \+/\- *lemma* measure_theory.ae_eq_fun.ext
- \+ *lemma* measure_theory.ae_eq_fun.induction_on
- \+ *lemma* measure_theory.ae_eq_fun.induction_on₂
- \+ *lemma* measure_theory.ae_eq_fun.induction_on₃
- \+ *lemma* measure_theory.ae_eq_fun.inv_mk
- \+ *lemma* measure_theory.ae_eq_fun.inv_to_germ
- \- *lemma* measure_theory.ae_eq_fun.le_iff_to_fun_le
- \+/\- *def* measure_theory.ae_eq_fun.lift_pred
- \+/\- *def* measure_theory.ae_eq_fun.lift_rel
- \+ *lemma* measure_theory.ae_eq_fun.lift_rel_iff_coe_fn
- \- *lemma* measure_theory.ae_eq_fun.lift_rel_iff_to_fun
- \+/\- *lemma* measure_theory.ae_eq_fun.lift_rel_mk_mk
- \+ *def* measure_theory.ae_eq_fun.lintegral
- \+ *lemma* measure_theory.ae_eq_fun.lintegral_add
- \+ *lemma* measure_theory.ae_eq_fun.lintegral_coe_fn
- \+ *lemma* measure_theory.ae_eq_fun.lintegral_eq_zero_iff
- \+ *lemma* measure_theory.ae_eq_fun.lintegral_mk
- \+ *lemma* measure_theory.ae_eq_fun.lintegral_mono
- \+ *lemma* measure_theory.ae_eq_fun.lintegral_zero
- \+/\- *def* measure_theory.ae_eq_fun.mk
- \- *lemma* measure_theory.ae_eq_fun.mk_add_mk
- \+ *lemma* measure_theory.ae_eq_fun.mk_coe_fn
- \+/\- *lemma* measure_theory.ae_eq_fun.mk_eq_mk
- \+/\- *lemma* measure_theory.ae_eq_fun.mk_le_mk
- \+ *lemma* measure_theory.ae_eq_fun.mk_mul_mk
- \+ *lemma* measure_theory.ae_eq_fun.mk_sub
- \- *lemma* measure_theory.ae_eq_fun.mk_sub_mk
- \+ *lemma* measure_theory.ae_eq_fun.mk_to_germ
- \+ *lemma* measure_theory.ae_eq_fun.mul_to_germ
- \- *lemma* measure_theory.ae_eq_fun.neg_mk
- \- *lemma* measure_theory.ae_eq_fun.neg_to_fun
- \+/\- *lemma* measure_theory.ae_eq_fun.one_def
- \- *lemma* measure_theory.ae_eq_fun.one_to_fun
- \+ *lemma* measure_theory.ae_eq_fun.one_to_germ
- \+ *def* measure_theory.ae_eq_fun.pair
- \+ *lemma* measure_theory.ae_eq_fun.pair_eq_mk
- \+ *lemma* measure_theory.ae_eq_fun.pair_mk_mk
- \+/\- *def* measure_theory.ae_eq_fun.pos_part
- \+ *lemma* measure_theory.ae_eq_fun.pos_part_mk
- \- *lemma* measure_theory.ae_eq_fun.pos_part_to_fun
- \+/\- *lemma* measure_theory.ae_eq_fun.quot_mk_eq_mk
- \+ *lemma* measure_theory.ae_eq_fun.quotient_out'_eq_coe_fn
- \- *lemma* measure_theory.ae_eq_fun.self_eq_mk
- \- *lemma* measure_theory.ae_eq_fun.smul_to_fun
- \+ *lemma* measure_theory.ae_eq_fun.smul_to_germ
- \- *lemma* measure_theory.ae_eq_fun.sub_to_fun
- \+ *def* measure_theory.ae_eq_fun.to_germ
- \+ *lemma* measure_theory.ae_eq_fun.to_germ_eq
- \+ *lemma* measure_theory.ae_eq_fun.to_germ_injective
- \- *lemma* measure_theory.ae_eq_fun.zero_def
- \- *lemma* measure_theory.ae_eq_fun.zero_to_fun
- \+/\- *def* measure_theory.ae_eq_fun
- \+ *def* measure_theory.measure.ae_eq_setoid

Modified src/measure_theory/bochner_integration.lean
- \+/\- *def* measure_theory.integral
- \+ *lemma* measure_theory.integral_add_meas
- \+/\- *lemma* measure_theory.integral_congr_ae
- \+ *lemma* measure_theory.integral_const
- \+/\- *lemma* measure_theory.integral_div
- \+/\- *lemma* measure_theory.integral_eq
- \+/\- *lemma* measure_theory.integral_eq_lintegral_of_nonneg_ae
- \+/\- *lemma* measure_theory.integral_finset_sum
- \- *lemma* measure_theory.integral_le_integral
- \- *lemma* measure_theory.integral_le_integral_ae
- \+ *lemma* measure_theory.integral_mono
- \+/\- *lemma* measure_theory.integral_mul_left
- \+/\- *lemma* measure_theory.integral_mul_right
- \+/\- *lemma* measure_theory.integral_neg
- \+/\- *lemma* measure_theory.integral_non_integrable
- \+/\- *lemma* measure_theory.integral_non_measurable
- \+/\- *lemma* measure_theory.integral_nonneg_of_ae
- \+/\- *lemma* measure_theory.integral_nonpos_of_nonpos_ae
- \+/\- *lemma* measure_theory.integral_smul
- \+/\- *lemma* measure_theory.integral_undef
- \+/\- *lemma* measure_theory.integral_zero
- \+/\- *def* measure_theory.l1.integral
- \+/\- *lemma* measure_theory.l1.integral_add
- \+/\- *def* measure_theory.l1.integral_clm
- \+/\- *lemma* measure_theory.l1.integral_eq
- \+/\- *lemma* measure_theory.l1.integral_eq_norm_pos_part_sub
- \+/\- *lemma* measure_theory.l1.integral_neg
- \+/\- *lemma* measure_theory.l1.integral_smul
- \+/\- *lemma* measure_theory.l1.integral_sub
- \+/\- *lemma* measure_theory.l1.integral_zero
- \+/\- *lemma* measure_theory.l1.norm_integral_le
- \+/\- *lemma* measure_theory.l1.simple_func.add_to_simple_func
- \+/\- *lemma* measure_theory.l1.simple_func.coe_add
- \+ *lemma* measure_theory.l1.simple_func.coe_coe
- \+/\- *lemma* measure_theory.l1.simple_func.coe_neg
- \+/\- *lemma* measure_theory.l1.simple_func.coe_neg_part
- \+/\- *lemma* measure_theory.l1.simple_func.coe_pos_part
- \+/\- *lemma* measure_theory.l1.simple_func.coe_smul
- \+/\- *lemma* measure_theory.l1.simple_func.coe_sub
- \+/\- *def* measure_theory.l1.simple_func.coe_to_l1
- \+/\- *lemma* measure_theory.l1.simple_func.coe_zero
- \+/\- *lemma* measure_theory.l1.simple_func.dist_eq
- \+/\- *lemma* measure_theory.l1.simple_func.dist_to_simple_func
- \+/\- *lemma* measure_theory.l1.simple_func.edist_eq
- \- *lemma* measure_theory.l1.simple_func.exists_simple_func_near
- \+/\- *def* measure_theory.l1.simple_func.integral
- \+/\- *lemma* measure_theory.l1.simple_func.integral_add
- \+/\- *def* measure_theory.l1.simple_func.integral_clm
- \+/\- *lemma* measure_theory.l1.simple_func.integral_congr
- \- *lemma* measure_theory.l1.simple_func.integral_eq_bintegral
- \+/\- *lemma* measure_theory.l1.simple_func.integral_eq_integral
- \+/\- *lemma* measure_theory.l1.simple_func.integral_eq_lintegral
- \+/\- *lemma* measure_theory.l1.simple_func.integral_eq_norm_pos_part_sub
- \+ *lemma* measure_theory.l1.simple_func.integral_l1_eq_integral
- \+/\- *lemma* measure_theory.l1.simple_func.integral_smul
- \+/\- *lemma* measure_theory.l1.simple_func.lintegral_edist_to_simple_func_lt_top
- \+/\- *def* measure_theory.l1.simple_func.neg_part
- \+/\- *lemma* measure_theory.l1.simple_func.neg_part_to_simple_func
- \+/\- *lemma* measure_theory.l1.simple_func.neg_to_simple_func
- \+/\- *lemma* measure_theory.l1.simple_func.norm_eq'
- \+/\- *lemma* measure_theory.l1.simple_func.norm_eq
- \- *lemma* measure_theory.l1.simple_func.norm_eq_bintegral
- \+ *lemma* measure_theory.l1.simple_func.norm_eq_integral
- \+/\- *lemma* measure_theory.l1.simple_func.norm_integral_le_norm
- \+/\- *lemma* measure_theory.l1.simple_func.norm_of_simple_func
- \+/\- *lemma* measure_theory.l1.simple_func.norm_to_simple_func
- \+/\- *def* measure_theory.l1.simple_func.of_simple_func
- \+/\- *lemma* measure_theory.l1.simple_func.of_simple_func_add
- \+/\- *lemma* measure_theory.l1.simple_func.of_simple_func_eq_mk
- \+/\- *lemma* measure_theory.l1.simple_func.of_simple_func_eq_of_fun
- \+/\- *lemma* measure_theory.l1.simple_func.of_simple_func_neg
- \+/\- *lemma* measure_theory.l1.simple_func.of_simple_func_smul
- \+/\- *lemma* measure_theory.l1.simple_func.of_simple_func_sub
- \+/\- *lemma* measure_theory.l1.simple_func.of_simple_func_to_simple_func
- \+/\- *lemma* measure_theory.l1.simple_func.of_simple_func_zero
- \+/\- *def* measure_theory.l1.simple_func.pos_part
- \+/\- *lemma* measure_theory.l1.simple_func.pos_part_to_simple_func
- \+/\- *lemma* measure_theory.l1.simple_func.smul_to_simple_func
- \+/\- *lemma* measure_theory.l1.simple_func.sub_to_simple_func
- \+/\- *def* measure_theory.l1.simple_func.to_simple_func
- \+/\- *lemma* measure_theory.l1.simple_func.to_simple_func_eq_to_fun
- \+/\- *lemma* measure_theory.l1.simple_func.to_simple_func_of_simple_func
- \+/\- *lemma* measure_theory.l1.simple_func.zero_to_simple_func
- \+/\- *def* measure_theory.l1.simple_func
- \+/\- *lemma* measure_theory.norm_integral_le_integral_norm
- \+/\- *lemma* measure_theory.norm_integral_le_lintegral_norm
- \- *def* measure_theory.simple_func.bintegral
- \- *lemma* measure_theory.simple_func.bintegral_add
- \- *lemma* measure_theory.simple_func.bintegral_congr
- \- *lemma* measure_theory.simple_func.bintegral_eq_integral'
- \- *lemma* measure_theory.simple_func.bintegral_eq_integral
- \- *lemma* measure_theory.simple_func.bintegral_eq_lintegral'
- \- *lemma* measure_theory.simple_func.bintegral_eq_lintegral
- \- *lemma* measure_theory.simple_func.bintegral_neg
- \- *lemma* measure_theory.simple_func.bintegral_smul
- \- *lemma* measure_theory.simple_func.bintegral_sub
- \+ *lemma* measure_theory.simple_func.fin_meas_supp.integrable
- \- *lemma* measure_theory.simple_func.fin_vol_supp_of_integrable
- \+ *lemma* measure_theory.simple_func.integrable_iff_fin_meas_supp
- \- *lemma* measure_theory.simple_func.integrable_iff_fin_vol_supp
- \- *lemma* measure_theory.simple_func.integrable_iff_integral_lt_top
- \- *lemma* measure_theory.simple_func.integrable_of_fin_vol_supp
- \+/\- *lemma* measure_theory.simple_func.integrable_pair
- \+ *def* measure_theory.simple_func.integral
- \+ *lemma* measure_theory.simple_func.integral_add
- \+ *lemma* measure_theory.simple_func.integral_add_meas
- \+ *lemma* measure_theory.simple_func.integral_congr
- \+ *lemma* measure_theory.simple_func.integral_eq_integral
- \+ *lemma* measure_theory.simple_func.integral_eq_lintegral'
- \+ *lemma* measure_theory.simple_func.integral_eq_lintegral
- \+ *lemma* measure_theory.simple_func.integral_eq_sum_filter
- \+ *lemma* measure_theory.simple_func.integral_neg
- \+ *lemma* measure_theory.simple_func.integral_smul
- \+ *lemma* measure_theory.simple_func.integral_sub
- \- *lemma* measure_theory.simple_func.map_bintegral
- \+ *lemma* measure_theory.simple_func.map_integral
- \+/\- *def* measure_theory.simple_func.neg_part
- \- *lemma* measure_theory.simple_func.norm_bintegral_le_bintegral_norm
- \+ *lemma* measure_theory.simple_func.norm_integral_le_integral_norm
- \+/\- *def* measure_theory.simple_func.pos_part
- \+/\- *theorem* measure_theory.tendsto_integral_of_dominated_convergence
- \+ *lemma* measure_theory.tendsto_integral_of_l1

Modified src/measure_theory/borel_space.lean
- \- *lemma* is_measurable_eq
- \- *lemma* is_measurable_singleton

Modified src/measure_theory/category/Meas.lean


Modified src/measure_theory/giry_monad.lean
- \- *lemma* measure_theory.measure.integral_bind
- \- *lemma* measure_theory.measure.integral_join
- \+ *lemma* measure_theory.measure.lintegral_bind
- \+ *lemma* measure_theory.measure.lintegral_join
- \- *lemma* measure_theory.measure.measurable_integral
- \+ *lemma* measure_theory.measure.measurable_lintegral

Modified src/measure_theory/indicator_function.lean
- \+/\- *lemma* indicator_congr_ae
- \+/\- *lemma* indicator_congr_of_set
- \+/\- *lemma* indicator_le_indicator_ae

Modified src/measure_theory/integration.lean
- \+/\- *def* measure_theory.lintegral
- \+ *lemma* measure_theory.lintegral_Union
- \+ *lemma* measure_theory.lintegral_Union_le
- \+ *lemma* measure_theory.lintegral_add_meas
- \+/\- *lemma* measure_theory.lintegral_congr_ae
- \+ *lemma* measure_theory.lintegral_const
- \+/\- *lemma* measure_theory.lintegral_const_mul_le
- \+ *lemma* measure_theory.lintegral_dirac
- \+/\- *lemma* measure_theory.lintegral_eq_nnreal
- \- *lemma* measure_theory.lintegral_eq_supr_eapprox_integral
- \+ *lemma* measure_theory.lintegral_eq_supr_eapprox_lintegral
- \+ *lemma* measure_theory.lintegral_indicator
- \- *lemma* measure_theory.lintegral_le_lintegral_ae
- \+ *lemma* measure_theory.lintegral_map
- \+ *lemma* measure_theory.lintegral_mono'
- \+/\- *lemma* measure_theory.lintegral_mono
- \+ *lemma* measure_theory.lintegral_mono_ae
- \+/\- *lemma* measure_theory.lintegral_rw₁
- \+/\- *lemma* measure_theory.lintegral_rw₂
- \+ *lemma* measure_theory.lintegral_smul_meas
- \+ *lemma* measure_theory.lintegral_sum_meas
- \- *lemma* measure_theory.lintegral_supr_const
- \+/\- *lemma* measure_theory.lintegral_zero
- \+ *lemma* measure_theory.lintegral_zero_meas
- \+ *lemma* measure_theory.meas_ge_le_lintegral_div
- \- *def* measure_theory.measure.integral
- \- *lemma* measure_theory.measure.integral_dirac
- \- *lemma* measure_theory.measure.integral_map
- \- *lemma* measure_theory.measure.integral_zero
- \+/\- *def* measure_theory.measure.with_density
- \- *lemma* measure_theory.measure.with_density_apply
- \+/\- *lemma* measure_theory.monotone_lintegral
- \+ *lemma* measure_theory.mul_meas_ge_le_lintegral
- \- *lemma* measure_theory.mul_volume_ge_le_lintegral
- \- *lemma* measure_theory.simple_func.add_integral
- \+ *lemma* measure_theory.simple_func.add_lintegral
- \+ *lemma* measure_theory.simple_func.coe_add
- \+ *theorem* measure_theory.simple_func.coe_const
- \+ *lemma* measure_theory.simple_func.coe_injective
- \+ *lemma* measure_theory.simple_func.coe_le
- \+/\- *theorem* measure_theory.simple_func.coe_map
- \+ *lemma* measure_theory.simple_func.coe_mul
- \+ *lemma* measure_theory.simple_func.coe_neg
- \+ *theorem* measure_theory.simple_func.coe_piecewise
- \+ *lemma* measure_theory.simple_func.coe_range
- \+ *theorem* measure_theory.simple_func.coe_restrict
- \+ *lemma* measure_theory.simple_func.coe_smul
- \+ *lemma* measure_theory.simple_func.coe_sub
- \+ *lemma* measure_theory.simple_func.coe_zero
- \+/\- *theorem* measure_theory.simple_func.const_apply
- \+ *lemma* measure_theory.simple_func.const_lintegral
- \+ *lemma* measure_theory.simple_func.const_lintegral_restrict
- \- *lemma* measure_theory.simple_func.const_mul_integral
- \+ *lemma* measure_theory.simple_func.const_mul_lintegral
- \+ *lemma* measure_theory.simple_func.const_zero
- \+ *lemma* measure_theory.simple_func.eq_zero_of_mem_range_zero
- \+ *lemma* measure_theory.simple_func.exists_range_iff
- \+ *lemma* measure_theory.simple_func.fin_meas_supp.iff_lintegral_lt_top
- \+ *lemma* measure_theory.simple_func.fin_meas_supp.lintegral_lt_top
- \+ *lemma* measure_theory.simple_func.fin_meas_supp.map_iff
- \+ *lemma* measure_theory.simple_func.fin_meas_supp.meas_preimage_singleton_ne_zero
- \+ *lemma* measure_theory.simple_func.fin_meas_supp.of_lintegral_lt_top
- \+ *lemma* measure_theory.simple_func.fin_meas_supp.of_map
- \+ *lemma* measure_theory.simple_func.fin_meas_supp_iff
- \+ *lemma* measure_theory.simple_func.fin_meas_supp_iff_support
- \- *lemma* measure_theory.simple_func.fin_vol_supp_map
- \- *lemma* measure_theory.simple_func.fin_vol_supp_of_fin_vol_supp_map
- \- *lemma* measure_theory.simple_func.fin_vol_supp_of_integral_lt_top
- \- *lemma* measure_theory.simple_func.fin_vol_supp_pair
- \+ *lemma* measure_theory.simple_func.finite_range
- \+ *lemma* measure_theory.simple_func.forall_range_iff
- \- *def* measure_theory.simple_func.integral
- \- *lemma* measure_theory.simple_func.integral_congr
- \- *lemma* measure_theory.simple_func.integral_le_integral
- \- *lemma* measure_theory.simple_func.integral_lt_top_of_fin_vol_supp
- \- *lemma* measure_theory.simple_func.integral_map
- \- *lemma* measure_theory.simple_func.integral_map_coe_lt_top
- \- *lemma* measure_theory.simple_func.integral_sup_le
- \+/\- *lemma* measure_theory.simple_func.is_measurable_cut
- \+ *lemma* measure_theory.simple_func.is_measurable_fiber
- \+ *theorem* measure_theory.simple_func.is_measurable_preimage
- \- *def* measure_theory.simple_func.ite
- \- *theorem* measure_theory.simple_func.ite_apply
- \+ *lemma* measure_theory.simple_func.le_sup_lintegral
- \+ *def* measure_theory.simple_func.lintegral
- \+ *lemma* measure_theory.simple_func.lintegral_add
- \+ *lemma* measure_theory.simple_func.lintegral_congr
- \- *theorem* measure_theory.simple_func.lintegral_eq_integral
- \+ *theorem* measure_theory.simple_func.lintegral_eq_lintegral
- \+ *lemma* measure_theory.simple_func.lintegral_eq_of_measure_preimage
- \+ *lemma* measure_theory.simple_func.lintegral_eq_of_subset
- \+/\- *lemma* measure_theory.simple_func.lintegral_map
- \+ *lemma* measure_theory.simple_func.lintegral_mono
- \+ *lemma* measure_theory.simple_func.lintegral_restrict
- \+ *lemma* measure_theory.simple_func.lintegral_smul
- \+ *lemma* measure_theory.simple_func.lintegral_sum
- \+ *lemma* measure_theory.simple_func.lintegral_zero
- \+ *def* measure_theory.simple_func.lintegralₗ
- \+/\- *theorem* measure_theory.simple_func.map_apply
- \+ *theorem* measure_theory.simple_func.map_coe_ennreal_restrict
- \+ *theorem* measure_theory.simple_func.map_coe_nnreal_restrict
- \+ *theorem* measure_theory.simple_func.map_const
- \- *lemma* measure_theory.simple_func.map_integral
- \+ *lemma* measure_theory.simple_func.map_lintegral
- \+ *theorem* measure_theory.simple_func.map_restrict_of_zero
- \+ *lemma* measure_theory.simple_func.mem_image_of_mem_range_restrict
- \+/\- *theorem* measure_theory.simple_func.mem_range
- \+ *theorem* measure_theory.simple_func.mem_range_of_measure_ne_zero
- \+ *theorem* measure_theory.simple_func.mem_range_self
- \+/\- *lemma* measure_theory.simple_func.mem_restrict_range
- \+/\- *lemma* measure_theory.simple_func.mul_apply
- \+ *lemma* measure_theory.simple_func.mul_eq_map₂
- \+ *def* measure_theory.simple_func.piecewise
- \+ *theorem* measure_theory.simple_func.piecewise_apply
- \+ *lemma* measure_theory.simple_func.piecewise_compl
- \+ *lemma* measure_theory.simple_func.piecewise_empty
- \+ *lemma* measure_theory.simple_func.piecewise_univ
- \- *theorem* measure_theory.simple_func.preimage_measurable
- \+/\- *lemma* measure_theory.simple_func.range_const
- \+ *lemma* measure_theory.simple_func.range_zero
- \+/\- *def* measure_theory.simple_func.restrict
- \+/\- *theorem* measure_theory.simple_func.restrict_apply
- \- *lemma* measure_theory.simple_func.restrict_const_integral
- \+ *lemma* measure_theory.simple_func.restrict_const_lintegral
- \+ *theorem* measure_theory.simple_func.restrict_empty
- \- *lemma* measure_theory.simple_func.restrict_integral
- \+ *lemma* measure_theory.simple_func.restrict_lintegral
- \+ *lemma* measure_theory.simple_func.restrict_lintegral_eq_lintegral_restrict
- \+ *lemma* measure_theory.simple_func.restrict_mono
- \+ *theorem* measure_theory.simple_func.restrict_of_not_measurable
- \- *lemma* measure_theory.simple_func.restrict_preimage'
- \+/\- *theorem* measure_theory.simple_func.restrict_preimage
- \+ *theorem* measure_theory.simple_func.restrict_preimage_singleton
- \+ *theorem* measure_theory.simple_func.restrict_univ
- \+/\- *lemma* measure_theory.simple_func.smul_eq_map
- \+/\- *lemma* measure_theory.simple_func.sup_apply
- \+ *lemma* measure_theory.simple_func.support_eq
- \+/\- *lemma* measure_theory.simple_func.supr_eapprox_apply
- \- *lemma* measure_theory.simple_func.volume_bUnion_preimage
- \- *lemma* measure_theory.simple_func.zero_integral
- \+ *lemma* measure_theory.simple_func.zero_lintegral
- \- *lemma* measure_theory.volume_ge_le_lintegral_div
- \+ *lemma* measure_theory.with_density_apply

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* measure_theory.ae_eq_fun.integrable.add
- \+/\- *lemma* measure_theory.ae_eq_fun.integrable.neg
- \+/\- *lemma* measure_theory.ae_eq_fun.integrable.smul
- \+/\- *lemma* measure_theory.ae_eq_fun.integrable.sub
- \+/\- *def* measure_theory.ae_eq_fun.integrable
- \+ *lemma* measure_theory.ae_eq_fun.integrable_coe_fn
- \- *lemma* measure_theory.ae_eq_fun.integrable_to_fun
- \+/\- *lemma* measure_theory.ae_eq_fun.integrable_zero
- \+/\- *lemma* measure_theory.all_ae_of_real_F_le_bound
- \+/\- *lemma* measure_theory.all_ae_of_real_f_le_bound
- \+/\- *lemma* measure_theory.all_ae_tendsto_of_real_norm
- \+ *lemma* measure_theory.integrable.add_meas
- \+ *lemma* measure_theory.integrable.congr
- \+ *lemma* measure_theory.integrable.left_of_add_meas
- \+/\- *lemma* measure_theory.integrable.max_zero
- \+/\- *lemma* measure_theory.integrable.min_zero
- \+ *lemma* measure_theory.integrable.mono
- \+ *lemma* measure_theory.integrable.mono_meas
- \+ *lemma* measure_theory.integrable.mono_set
- \+/\- *lemma* measure_theory.integrable.neg
- \+/\- *lemma* measure_theory.integrable.norm
- \+ *lemma* measure_theory.integrable.right_of_add_meas
- \+/\- *lemma* measure_theory.integrable.smul
- \+ *lemma* measure_theory.integrable.smul_meas
- \+ *lemma* measure_theory.integrable.union
- \+/\- *def* measure_theory.integrable
- \+ *lemma* measure_theory.integrable_congr
- \- *lemma* measure_theory.integrable_congr_ae
- \+ *lemma* measure_theory.integrable_const
- \+/\- *lemma* measure_theory.integrable_iff_edist
- \+/\- *lemma* measure_theory.integrable_iff_norm
- \+/\- *lemma* measure_theory.integrable_iff_of_real
- \+/\- *lemma* measure_theory.integrable_neg_iff
- \+/\- *lemma* measure_theory.integrable_norm_iff
- \- *lemma* measure_theory.integrable_of_ae_eq
- \+/\- *lemma* measure_theory.integrable_of_integrable_bound
- \- *lemma* measure_theory.integrable_of_le
- \- *lemma* measure_theory.integrable_of_le_ae
- \+/\- *lemma* measure_theory.integrable_zero
- \+/\- *lemma* measure_theory.l1.add_to_fun
- \+/\- *lemma* measure_theory.l1.coe_add
- \+ *lemma* measure_theory.l1.coe_coe
- \+/\- *lemma* measure_theory.l1.coe_neg
- \+/\- *lemma* measure_theory.l1.coe_pos_part
- \+/\- *lemma* measure_theory.l1.coe_smul
- \+/\- *lemma* measure_theory.l1.coe_sub
- \+/\- *lemma* measure_theory.l1.coe_zero
- \+/\- *lemma* measure_theory.l1.continuous_neg_part
- \+/\- *lemma* measure_theory.l1.continuous_pos_part
- \+/\- *lemma* measure_theory.l1.dist_eq
- \+/\- *lemma* measure_theory.l1.dist_to_fun
- \+/\- *lemma* measure_theory.l1.edist_eq
- \+/\- *lemma* measure_theory.l1.lintegral_edist_to_fun_lt_top
- \+/\- *lemma* measure_theory.l1.mk_to_fun
- \+/\- *def* measure_theory.l1.neg_part
- \+/\- *lemma* measure_theory.l1.neg_part_to_fun_eq_max
- \+/\- *lemma* measure_theory.l1.neg_part_to_fun_eq_min
- \+/\- *lemma* measure_theory.l1.neg_to_fun
- \+/\- *lemma* measure_theory.l1.norm_eq
- \+/\- *lemma* measure_theory.l1.norm_eq_nnnorm_to_fun
- \+/\- *lemma* measure_theory.l1.norm_eq_norm_to_fun
- \+/\- *lemma* measure_theory.l1.norm_le_norm_of_ae_le
- \+/\- *def* measure_theory.l1.of_fun
- \+/\- *lemma* measure_theory.l1.of_fun_eq_mk
- \+/\- *lemma* measure_theory.l1.of_fun_smul
- \+/\- *lemma* measure_theory.l1.of_fun_to_fun
- \+/\- *def* measure_theory.l1.pos_part
- \+/\- *lemma* measure_theory.l1.pos_part_to_fun
- \+/\- *lemma* measure_theory.l1.smul_to_fun
- \+/\- *lemma* measure_theory.l1.sub_to_fun
- \+/\- *lemma* measure_theory.l1.to_fun_of_fun
- \+/\- *lemma* measure_theory.l1.zero_to_fun
- \+/\- *def* measure_theory.l1
- \+/\- *lemma* measure_theory.lintegral_nnnorm_zero

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* is_measurable.compl_iff
- \+/\- *lemma* is_measurable.empty
- \+ *lemma* is_measurable.inl_image
- \+ *lemma* is_measurable.insert
- \+ *lemma* is_measurable.subtype_image
- \+/\- *lemma* is_measurable.univ
- \+ *lemma* is_measurable_eq
- \- *lemma* is_measurable_inl_image
- \+ *lemma* is_measurable_insert
- \- *lemma* is_measurable_subtype_image
- \- *lemma* measurable.if
- \+ *lemma* measurable.indicator
- \+ *lemma* measurable.piecewise
- \- *lemma* measurable.preimage
- \+ *lemma* measurable.sum_rec
- \+/\- *def* measurable
- \+/\- *lemma* measurable_const
- \+ *lemma* measurable_fst
- \+/\- *lemma* measurable_id
- \+ *lemma* measurable_iff_comap_le
- \+ *lemma* measurable_iff_le_map
- \+/\- *lemma* measurable_inl
- \+/\- *lemma* measurable_inr
- \+ *lemma* measurable_one
- \+ *lemma* measurable_snd
- \+ *lemma* measurable_subtype_coe
- \- *lemma* measurable_sum_rec
- \- *lemma* measurable_zero
- \+ *lemma* set.finite.is_measurable

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* measure_theory.ae_eq_refl
- \+/\- *lemma* measure_theory.ae_eq_symm
- \+/\- *lemma* measure_theory.ae_eq_trans
- \+/\- *lemma* measure_theory.ae_iff
- \+ *lemma* measure_theory.ae_map_iff
- \+/\- *lemma* measure_theory.ae_of_all
- \+ *lemma* measure_theory.ae_restrict_eq
- \+ *lemma* measure_theory.coe_to_outer_measure
- \+ *lemma* measure_theory.dirac_ae_eq
- \+ *lemma* measure_theory.eventually_dirac
- \+ *lemma* measure_theory.eventually_eq_dirac'
- \+ *lemma* measure_theory.eventually_eq_dirac
- \+ *lemma* measure_theory.exists_is_measurable_superset_iff_measure_eq_zero
- \+ *lemma* measure_theory.le_to_measure_apply
- \+/\- *theorem* measure_theory.measure.add_apply
- \+ *theorem* measure_theory.measure.coe_add
- \+ *theorem* measure_theory.measure.coe_smul
- \+ *theorem* measure_theory.measure.coe_zero
- \+ *def* measure_theory.measure.cofinite
- \+ *def* measure_theory.measure.comap
- \+ *lemma* measure_theory.measure.comap_apply
- \+ *lemma* measure_theory.measure.count_apply
- \+ *lemma* measure_theory.measure.count_apply_finset
- \+ *lemma* measure_theory.measure.dirac_apply'
- \+ *lemma* measure_theory.measure.dirac_apply_of_mem
- \+ *lemma* measure_theory.measure.eq_zero_of_not_nonempty
- \+ *lemma* measure_theory.measure.eventually_cofinite
- \+/\- *lemma* measure_theory.measure.ext
- \+ *lemma* measure_theory.measure.le_lift_linear_apply
- \+ *lemma* measure_theory.measure.le_restrict_apply
- \+ *def* measure_theory.measure.lift_linear
- \+ *lemma* measure_theory.measure.lift_linear_apply
- \+ *theorem* measure_theory.measure.lt_iff'
- \+ *theorem* measure_theory.measure.lt_iff
- \+/\- *def* measure_theory.measure.map
- \+/\- *theorem* measure_theory.measure.map_apply
- \+ *lemma* measure_theory.measure.map_comap_subtype_coe
- \+ *lemma* measure_theory.measure.mem_cofinite
- \+ *def* measure_theory.measure.restrict
- \+ *lemma* measure_theory.measure.restrict_Union
- \+ *lemma* measure_theory.measure.restrict_Union_apply
- \+ *lemma* measure_theory.measure.restrict_Union_le
- \+ *lemma* measure_theory.measure.restrict_add
- \+ *lemma* measure_theory.measure.restrict_apply
- \+ *lemma* measure_theory.measure.restrict_apply_eq_zero'
- \+ *lemma* measure_theory.measure.restrict_apply_eq_zero
- \+ *lemma* measure_theory.measure.restrict_empty
- \+ *lemma* measure_theory.measure.restrict_mono
- \+ *lemma* measure_theory.measure.restrict_smul
- \+ *lemma* measure_theory.measure.restrict_sum
- \+ *lemma* measure_theory.measure.restrict_union
- \+ *lemma* measure_theory.measure.restrict_union_apply
- \+ *lemma* measure_theory.measure.restrict_union_le
- \+ *lemma* measure_theory.measure.restrict_univ
- \+ *lemma* measure_theory.measure.restrict_zero
- \+ *def* measure_theory.measure.restrictₗ
- \+ *lemma* measure_theory.measure.restrictₗ_apply
- \- *theorem* measure_theory.measure.smul_apply
- \+ *theorem* measure_theory.measure.smul_to_outer_measure
- \+ *lemma* measure_theory.measure.sum_apply
- \+ *lemma* measure_theory.measure.sum_bool
- \+ *lemma* measure_theory.measure.to_outer_measure_injective
- \- *theorem* measure_theory.measure.zero_apply
- \+/\- *theorem* measure_theory.measure.zero_to_outer_measure
- \+ *lemma* measure_theory.measure_bUnion_finset_le
- \+ *lemma* measure_theory.measure_bUnion_le
- \+ *lemma* measure_theory.measure_congr
- \+ *lemma* measure_theory.measure_diff_of_ae_imp
- \+ *lemma* measure_theory.measure_le_of_ae_imp
- \+/\- *lemma* measure_theory.measure_zero_iff_ae_nmem
- \+/\- *lemma* measure_theory.mem_ae_iff
- \+ *lemma* measure_theory.mem_ae_map_iff
- \+ *lemma* measure_theory.mem_dirac_ae_iff
- \+ *lemma* measure_theory.nonempty_of_measure_ne_zero
- \+/\- *theorem* measure_theory.outer_measure.trim_eq_infi'
- \+ *theorem* measure_theory.outer_measure.trim_smul
- \- *lemma* measure_theory.outer_measure.trim_smul
- \+ *lemma* measure_theory.sum_measure_preimage_singleton
- \+/\- *lemma* measure_theory.to_measure_to_outer_measure
- \+/\- *lemma* measure_theory.to_outer_measure_apply
- \+/\- *lemma* measure_theory.to_outer_measure_to_measure
- \+ *lemma* measure_theory.tsum_measure_preimage_singleton

Modified src/measure_theory/outer_measure.lean
- \+/\- *theorem* measure_theory.outer_measure.add_apply
- \+ *theorem* measure_theory.outer_measure.coe_add
- \+ *lemma* measure_theory.outer_measure.coe_fn_injective
- \+ *lemma* measure_theory.outer_measure.coe_smul
- \+ *theorem* measure_theory.outer_measure.coe_zero
- \+ *def* measure_theory.outer_measure.comap
- \+ *lemma* measure_theory.outer_measure.comap_apply
- \+/\- *lemma* measure_theory.outer_measure.ext
- \+/\- *def* measure_theory.outer_measure.map
- \+/\- *lemma* measure_theory.outer_measure.measure_of_eq_coe
- \+ *def* measure_theory.outer_measure.restrict
- \+ *lemma* measure_theory.outer_measure.restrict_apply
- \+ *lemma* measure_theory.outer_measure.smul_apply
- \- *theorem* measure_theory.outer_measure.smul_apply
- \- *theorem* measure_theory.outer_measure.zero_apply

Modified src/measure_theory/set_integral.lean
- \- *lemma* integrable_on.add
- \- *lemma* integrable_on.divide
- \- *lemma* integrable_on.mul_left
- \- *lemma* integrable_on.mul_right
- \- *lemma* integrable_on.neg
- \- *lemma* integrable_on.smul
- \- *lemma* integrable_on.sub
- \- *lemma* integrable_on.subset
- \- *lemma* integrable_on.union
- \- *def* integrable_on
- \- *lemma* integrable_on_congr
- \- *lemma* integrable_on_congr_ae
- \- *lemma* integrable_on_empty
- \- *lemma* integrable_on_norm_iff
- \- *lemma* integral_on_Union
- \- *lemma* integral_on_add
- \- *lemma* integral_on_congr
- \- *lemma* integral_on_congr_of_ae_eq
- \- *lemma* integral_on_congr_of_set
- \- *lemma* integral_on_div
- \- *lemma* integral_on_le_integral_on
- \- *lemma* integral_on_le_integral_on_ae
- \- *lemma* integral_on_mul_left
- \- *lemma* integral_on_mul_right
- \- *lemma* integral_on_neg
- \- *lemma* integral_on_non_integrable
- \- *lemma* integral_on_non_measurable
- \- *lemma* integral_on_nonneg
- \- *lemma* integral_on_nonneg_of_ae
- \- *lemma* integral_on_nonpos
- \- *lemma* integral_on_nonpos_of_ae
- \- *lemma* integral_on_smul
- \- *lemma* integral_on_sub
- \- *lemma* integral_on_undef
- \- *lemma* integral_on_union
- \- *lemma* integral_on_union_ae
- \- *lemma* integral_on_zero
- \- *lemma* is_measurable.inter_preimage
- \- *lemma* measurable.measurable_on
- \- *lemma* measurable.measurable_on_univ
- \- *lemma* measurable_on.subset
- \- *lemma* measurable_on.union
- \- *def* measurable_on
- \- *lemma* measurable_on_empty
- \- *lemma* measurable_on_singleton
- \- *lemma* measure_theory.integrable.integrable_on
- \- *lemma* tendsto_integral_on_of_antimono
- \- *lemma* tendsto_integral_on_of_monotone

Modified src/measure_theory/simple_func_dense.lean
- \+/\- *lemma* measure_theory.simple_func_sequence_tendsto'

Modified src/order/complete_lattice.lean
- \+/\- *lemma* infi_eq_bot

Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_eq.prod_mk
- \+ *theorem* filter.eventually_inf_principal
- \+/\- *theorem* filter.mem_inf_principal

Modified src/order/filter/germ.lean
- \+ *lemma* filter.germ.map₂_coe

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tsum_subtype

Modified src/topology/algebra/module.lean
- \+ *theorem* continuous_linear_map.coe_injective'
- \+ *theorem* continuous_linear_map.coe_injective
- \+ *lemma* continuous_linear_map.coe_mk'
- \+ *lemma* continuous_linear_map.coe_mk

Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/continuous_on.lean


Modified src/topology/dense_embedding.lean
- \- *lemma* dense_inducing.extend_e_eq
- \+/\- *lemma* dense_inducing.extend_eq
- \+ *lemma* dense_inducing.extend_eq_at
- \- *lemma* dense_inducing.extend_eq_of_cont
- \+ *lemma* dense_inducing.extend_eq_of_tendsto
- \+ *lemma* dense_inducing.extend_unique
- \+ *lemma* dense_inducing.extend_unique_at

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
- \+ *lemma* order_embedding.le_map_sup
- \+ *lemma* order_embedding.map_inf_le
- \+ *lemma* order_iso.map_bot
- \+ *lemma* order_iso.map_inf
- \+ *lemma* order_iso.map_sup
- \+ *lemma* order_iso.map_top



## [2020-07-16 19:13:26](https://github.com/leanprover-community/mathlib/commit/33d45bf)
chore(data/polynomial): break up behemoth file ([#3407](https://github.com/leanprover-community/mathlib/pull/3407))
Polynomial refactor
The goal is to split `data/polynomial.lean` into several self-contained files in the same place. For the time being, the new place for all these files is `data/polynomial/`.
Future PRs may simplify proofs, remove duplicate lemmas, and move files out of the `data` directory.
#### Estimated changes
Deleted src/data/polynomial.lean
- \- *lemma* is_integral_domain.polynomial
- \- *def* polynomial.C
- \- *lemma* polynomial.C_0
- \- *lemma* polynomial.C_1
- \- *lemma* polynomial.C_add
- \- *lemma* polynomial.C_bit0
- \- *lemma* polynomial.C_bit1
- \- *lemma* polynomial.C_comp
- \- *lemma* polynomial.C_eq_algebra_map
- \- *lemma* polynomial.C_eq_int_cast
- \- *lemma* polynomial.C_eq_nat_cast
- \- *lemma* polynomial.C_inj
- \- *lemma* polynomial.C_mul'
- \- *lemma* polynomial.C_mul
- \- *lemma* polynomial.C_neg
- \- *lemma* polynomial.C_pow
- \- *lemma* polynomial.C_sub
- \- *def* polynomial.X
- \- *lemma* polynomial.X_comp
- \- *theorem* polynomial.X_dvd_iff
- \- *lemma* polynomial.X_mul
- \- *lemma* polynomial.X_ne_zero
- \- *lemma* polynomial.X_pow_mul
- \- *lemma* polynomial.X_pow_mul_assoc
- \- *lemma* polynomial.X_pow_sub_C_ne_zero
- \- *theorem* polynomial.X_sub_C_ne_zero
- \- *lemma* polynomial.add_comp
- \- *def* polynomial.aeval
- \- *lemma* polynomial.aeval_C
- \- *lemma* polynomial.aeval_X
- \- *theorem* polynomial.aeval_alg_hom
- \- *theorem* polynomial.aeval_alg_hom_apply
- \- *theorem* polynomial.aeval_def
- \- *lemma* polynomial.alg_hom_eval₂_algebra_map
- \- *lemma* polynomial.algebra_map_apply
- \- *lemma* polynomial.apply_eq_coeff
- \- *lemma* polynomial.as_sum
- \- *def* polynomial.binom_expansion
- \- *lemma* polynomial.card_nth_roots
- \- *lemma* polynomial.card_roots'
- \- *lemma* polynomial.card_roots
- \- *lemma* polynomial.card_roots_X_pow_sub_C
- \- *lemma* polynomial.card_roots_sub_C'
- \- *lemma* polynomial.card_roots_sub_C
- \- *lemma* polynomial.coe_eval₂_ring_hom
- \- *lemma* polynomial.coe_norm_unit
- \- *def* polynomial.coeff
- \- *lemma* polynomial.coeff_C
- \- *lemma* polynomial.coeff_C_mul
- \- *lemma* polynomial.coeff_C_mul_X
- \- *lemma* polynomial.coeff_C_zero
- \- *lemma* polynomial.coeff_X
- \- *lemma* polynomial.coeff_X_one
- \- *lemma* polynomial.coeff_X_pow
- \- *lemma* polynomial.coeff_X_zero
- \- *lemma* polynomial.coeff_add
- \- *def* polynomial.coeff_coe_to_fun
- \- *lemma* polynomial.coeff_coe_units_zero_ne_zero
- \- *lemma* polynomial.coeff_comp_degree_mul_degree
- \- *lemma* polynomial.coeff_derivative
- \- *lemma* polynomial.coeff_eq_zero_of_degree_lt
- \- *lemma* polynomial.coeff_eq_zero_of_nat_degree_lt
- \- *lemma* polynomial.coeff_inv_units
- \- *lemma* polynomial.coeff_map
- \- *lemma* polynomial.coeff_mk
- \- *theorem* polynomial.coeff_monomial_mul
- \- *theorem* polynomial.coeff_monomial_zero_mul
- \- *lemma* polynomial.coeff_mul
- \- *lemma* polynomial.coeff_mul_C
- \- *theorem* polynomial.coeff_mul_X
- \- *theorem* polynomial.coeff_mul_X_pow
- \- *lemma* polynomial.coeff_mul_X_sub_C
- \- *lemma* polynomial.coeff_mul_X_zero
- \- *lemma* polynomial.coeff_mul_degree_add_degree
- \- *theorem* polynomial.coeff_mul_monomial
- \- *theorem* polynomial.coeff_mul_monomial_zero
- \- *lemma* polynomial.coeff_nat_degree_eq_zero_of_degree_lt
- \- *lemma* polynomial.coeff_nat_degree_succ_eq_zero
- \- *lemma* polynomial.coeff_ne_zero_of_eq_degree
- \- *lemma* polynomial.coeff_neg
- \- *lemma* polynomial.coeff_one
- \- *lemma* polynomial.coeff_one_zero
- \- *lemma* polynomial.coeff_single
- \- *lemma* polynomial.coeff_smul
- \- *lemma* polynomial.coeff_sub
- \- *lemma* polynomial.coeff_sum
- \- *lemma* polynomial.coeff_zero
- \- *lemma* polynomial.coeff_zero_eq_eval_zero
- \- *def* polynomial.comp
- \- *lemma* polynomial.comp_C
- \- *lemma* polynomial.comp_X
- \- *lemma* polynomial.comp_one
- \- *lemma* polynomial.comp_zero
- \- *def* polynomial.decidable_dvd_monic
- \- *def* polynomial.degree
- \- *lemma* polynomial.degree_C
- \- *lemma* polynomial.degree_C_le
- \- *theorem* polynomial.degree_C_mul_X_pow_le
- \- *lemma* polynomial.degree_X
- \- *theorem* polynomial.degree_X_le
- \- *lemma* polynomial.degree_X_pow
- \- *theorem* polynomial.degree_X_pow_le
- \- *lemma* polynomial.degree_X_pow_sub_C
- \- *lemma* polynomial.degree_X_sub_C
- \- *lemma* polynomial.degree_add_C
- \- *lemma* polynomial.degree_add_div
- \- *lemma* polynomial.degree_add_div_by_monic
- \- *lemma* polynomial.degree_add_eq_of_degree_lt
- \- *lemma* polynomial.degree_add_eq_of_leading_coeff_add_ne_zero
- \- *lemma* polynomial.degree_add_le
- \- *lemma* polynomial.degree_coe_units
- \- *lemma* polynomial.degree_derivative_eq
- \- *theorem* polynomial.degree_derivative_le
- \- *theorem* polynomial.degree_derivative_lt
- \- *lemma* polynomial.degree_div_X_lt
- \- *lemma* polynomial.degree_div_by_monic_le
- \- *lemma* polynomial.degree_div_by_monic_lt
- \- *lemma* polynomial.degree_div_le
- \- *lemma* polynomial.degree_div_lt
- \- *lemma* polynomial.degree_eq_bot
- \- *lemma* polynomial.degree_eq_degree_of_associated
- \- *lemma* polynomial.degree_eq_iff_nat_degree_eq
- \- *lemma* polynomial.degree_eq_iff_nat_degree_eq_of_pos
- \- *lemma* polynomial.degree_eq_nat_degree
- \- *lemma* polynomial.degree_eq_one_of_irreducible_of_root
- \- *lemma* polynomial.degree_eq_zero_of_is_unit
- \- *lemma* polynomial.degree_erase_le
- \- *lemma* polynomial.degree_erase_lt
- \- *lemma* polynomial.degree_le_degree
- \- *theorem* polynomial.degree_le_iff_coeff_zero
- \- *lemma* polynomial.degree_le_mul_left
- \- *lemma* polynomial.degree_le_nat_degree
- \- *lemma* polynomial.degree_le_zero_iff
- \- *lemma* polynomial.degree_lt_degree_mul_X
- \- *lemma* polynomial.degree_lt_wf
- \- *lemma* polynomial.degree_map'
- \- *lemma* polynomial.degree_map
- \- *lemma* polynomial.degree_map_eq_of_injective
- \- *lemma* polynomial.degree_map_eq_of_leading_coeff_ne_zero
- \- *lemma* polynomial.degree_map_le
- \- *theorem* polynomial.degree_mod_by_monic_le
- \- *lemma* polynomial.degree_mod_by_monic_lt
- \- *lemma* polynomial.degree_monomial
- \- *lemma* polynomial.degree_monomial_le
- \- *lemma* polynomial.degree_mul_eq'
- \- *lemma* polynomial.degree_mul_eq
- \- *lemma* polynomial.degree_mul_le
- \- *lemma* polynomial.degree_mul_leading_coeff_inv
- \- *lemma* polynomial.degree_ne_of_nat_degree_ne
- \- *lemma* polynomial.degree_neg
- \- *lemma* polynomial.degree_nonneg_iff_ne_zero
- \- *lemma* polynomial.degree_normalize
- \- *lemma* polynomial.degree_one
- \- *lemma* polynomial.degree_one_le
- \- *lemma* polynomial.degree_pos_induction_on
- \- *lemma* polynomial.degree_pos_of_aeval_root
- \- *lemma* polynomial.degree_pos_of_eval₂_root
- \- *lemma* polynomial.degree_pos_of_ne_zero_of_nonunit
- \- *lemma* polynomial.degree_pos_of_root
- \- *lemma* polynomial.degree_pow_eq'
- \- *lemma* polynomial.degree_pow_eq
- \- *lemma* polynomial.degree_pow_le
- \- *lemma* polynomial.degree_sub_le
- \- *lemma* polynomial.degree_sub_lt
- \- *lemma* polynomial.degree_sum_le
- \- *lemma* polynomial.degree_zero
- \- *def* polynomial.derivative
- \- *lemma* polynomial.derivative_C
- \- *lemma* polynomial.derivative_X
- \- *lemma* polynomial.derivative_add
- \- *lemma* polynomial.derivative_eval
- \- *theorem* polynomial.derivative_eval₂_C
- \- *def* polynomial.derivative_hom
- \- *def* polynomial.derivative_lhom
- \- *theorem* polynomial.derivative_map
- \- *lemma* polynomial.derivative_monomial
- \- *lemma* polynomial.derivative_mul
- \- *lemma* polynomial.derivative_neg
- \- *lemma* polynomial.derivative_one
- \- *theorem* polynomial.derivative_pow
- \- *theorem* polynomial.derivative_pow_succ
- \- *lemma* polynomial.derivative_smul
- \- *lemma* polynomial.derivative_sub
- \- *lemma* polynomial.derivative_sum
- \- *lemma* polynomial.derivative_zero
- \- *def* polynomial.div
- \- *def* polynomial.div_X
- \- *lemma* polynomial.div_X_C
- \- *lemma* polynomial.div_X_add
- \- *lemma* polynomial.div_X_eq_zero_iff
- \- *lemma* polynomial.div_X_mul_X_add
- \- *def* polynomial.div_by_monic
- \- *lemma* polynomial.div_by_monic_eq_div
- \- *lemma* polynomial.div_by_monic_eq_of_not_monic
- \- *lemma* polynomial.div_by_monic_eq_zero_iff
- \- *lemma* polynomial.div_by_monic_mul_pow_root_multiplicity_eq
- \- *lemma* polynomial.div_by_monic_one
- \- *lemma* polynomial.div_by_monic_zero
- \- *lemma* polynomial.div_def
- \- *lemma* polynomial.div_eq_zero_iff
- \- *lemma* polynomial.div_mod_by_monic_unique
- \- *lemma* polynomial.div_wf_lemma
- \- *lemma* polynomial.dvd_iff_is_root
- \- *lemma* polynomial.dvd_iff_mod_by_monic_eq_zero
- \- *lemma* polynomial.dvd_term_of_dvd_eval_of_dvd_terms
- \- *lemma* polynomial.dvd_term_of_is_root_of_dvd_terms
- \- *lemma* polynomial.eq_C_of_degree_eq_zero
- \- *lemma* polynomial.eq_C_of_degree_le_zero
- \- *lemma* polynomial.eq_C_of_nat_degree_le_zero
- \- *lemma* polynomial.eq_X_add_C_of_degree_eq_one
- \- *lemma* polynomial.eq_X_add_C_of_degree_le_one
- \- *lemma* polynomial.eq_one_of_is_unit_of_monic
- \- *lemma* polynomial.eq_zero_of_eq_zero
- \- *def* polynomial.eval
- \- *lemma* polynomial.eval_C
- \- *lemma* polynomial.eval_X
- \- *lemma* polynomial.eval_add
- \- *lemma* polynomial.eval_bit0
- \- *lemma* polynomial.eval_bit1
- \- *lemma* polynomial.eval_comp
- \- *lemma* polynomial.eval_div_by_monic_pow_root_multiplicity_ne_zero
- \- *lemma* polynomial.eval_int_cast
- \- *lemma* polynomial.eval_map
- \- *lemma* polynomial.eval_monomial
- \- *lemma* polynomial.eval_mul
- \- *lemma* polynomial.eval_mul_X_sub_C
- \- *lemma* polynomial.eval_nat_cast
- \- *lemma* polynomial.eval_neg
- \- *lemma* polynomial.eval_one
- \- *lemma* polynomial.eval_pow
- \- *lemma* polynomial.eval_smul
- \- *lemma* polynomial.eval_sub
- \- *def* polynomial.eval_sub_factor
- \- *lemma* polynomial.eval_sum
- \- *theorem* polynomial.eval_unique
- \- *lemma* polynomial.eval_zero
- \- *def* polynomial.eval₂
- \- *lemma* polynomial.eval₂_C
- \- *lemma* polynomial.eval₂_X
- \- *lemma* polynomial.eval₂_X_pow
- \- *lemma* polynomial.eval₂_add
- \- *lemma* polynomial.eval₂_algebra_map_X
- \- *lemma* polynomial.eval₂_algebra_map_int_X
- \- *lemma* polynomial.eval₂_bit0
- \- *lemma* polynomial.eval₂_bit1
- \- *lemma* polynomial.eval₂_comp
- \- *lemma* polynomial.eval₂_eq_eval_map
- \- *lemma* polynomial.eval₂_hom
- \- *lemma* polynomial.eval₂_map
- \- *lemma* polynomial.eval₂_monomial
- \- *lemma* polynomial.eval₂_mul
- \- *lemma* polynomial.eval₂_nat_cast
- \- *lemma* polynomial.eval₂_neg
- \- *lemma* polynomial.eval₂_one
- \- *lemma* polynomial.eval₂_pow
- \- *def* polynomial.eval₂_ring_hom
- \- *lemma* polynomial.eval₂_smul
- \- *lemma* polynomial.eval₂_sub
- \- *lemma* polynomial.eval₂_sum
- \- *lemma* polynomial.eval₂_zero
- \- *lemma* polynomial.exists_finset_roots
- \- *lemma* polynomial.exists_root_of_degree_eq_one
- \- *lemma* polynomial.ext
- \- *theorem* polynomial.ext_iff
- \- *lemma* polynomial.finset_sum_coeff
- \- *lemma* polynomial.hom_eval₂
- \- *lemma* polynomial.integral_normalization_aeval_eq_zero
- \- *lemma* polynomial.integral_normalization_coeff_degree
- \- *lemma* polynomial.integral_normalization_coeff_nat_degree
- \- *lemma* polynomial.integral_normalization_coeff_ne_degree
- \- *lemma* polynomial.integral_normalization_coeff_ne_nat_degree
- \- *lemma* polynomial.integral_normalization_eval₂_eq_zero
- \- *theorem* polynomial.irreducible_X
- \- *theorem* polynomial.irreducible_X_sub_C
- \- *lemma* polynomial.irreducible_of_degree_eq_one
- \- *lemma* polynomial.irreducible_of_degree_eq_one_of_monic
- \- *lemma* polynomial.is_coprime_of_is_root_of_eval_derivative_ne_zero
- \- *lemma* polynomial.is_root.def
- \- *def* polynomial.is_root
- \- *lemma* polynomial.is_root_of_aeval_algebra_map_eq_zero
- \- *lemma* polynomial.is_root_of_eval₂_map_eq_zero
- \- *lemma* polynomial.is_unit_C
- \- *theorem* polynomial.is_unit_iff
- \- *lemma* polynomial.is_unit_iff_degree_eq_zero
- \- *lemma* polynomial.ite_le_nat_degree_coeff
- \- *def* polynomial.lcoeff
- \- *lemma* polynomial.lcoeff_apply
- \- *lemma* polynomial.le_degree_of_ne_zero
- \- *lemma* polynomial.le_nat_degree_of_ne_zero
- \- *def* polynomial.leading_coeff
- \- *lemma* polynomial.leading_coeff_C
- \- *lemma* polynomial.leading_coeff_X
- \- *lemma* polynomial.leading_coeff_X_pow
- \- *lemma* polynomial.leading_coeff_add_of_degree_eq
- \- *lemma* polynomial.leading_coeff_add_of_degree_lt
- \- *lemma* polynomial.leading_coeff_comp
- \- *lemma* polynomial.leading_coeff_eq_zero
- \- *lemma* polynomial.leading_coeff_eq_zero_iff_deg_eq_bot
- \- *lemma* polynomial.leading_coeff_map
- \- *lemma* polynomial.leading_coeff_monomial
- \- *lemma* polynomial.leading_coeff_mul'
- \- *lemma* polynomial.leading_coeff_mul
- \- *theorem* polynomial.leading_coeff_mul_X_pow
- \- *lemma* polynomial.leading_coeff_of_injective
- \- *lemma* polynomial.leading_coeff_one
- \- *lemma* polynomial.leading_coeff_pow'
- \- *lemma* polynomial.leading_coeff_pow
- \- *lemma* polynomial.leading_coeff_zero
- \- *def* polynomial.map
- \- *lemma* polynomial.map_C
- \- *lemma* polynomial.map_X
- \- *lemma* polynomial.map_add
- \- *lemma* polynomial.map_div
- \- *lemma* polynomial.map_div_by_monic
- \- *lemma* polynomial.map_eq_zero
- \- *lemma* polynomial.map_id
- \- *lemma* polynomial.map_injective
- \- *lemma* polynomial.map_map
- \- *lemma* polynomial.map_mod
- \- *lemma* polynomial.map_mod_by_monic
- \- *lemma* polynomial.map_mod_div_by_monic
- \- *lemma* polynomial.map_monomial
- \- *lemma* polynomial.map_mul
- \- *theorem* polynomial.map_nat_cast
- \- *lemma* polynomial.map_neg
- \- *lemma* polynomial.map_one
- \- *lemma* polynomial.map_pow
- \- *lemma* polynomial.map_sub
- \- *lemma* polynomial.map_zero
- \- *lemma* polynomial.mem_map_range
- \- *lemma* polynomial.mem_nth_roots
- \- *lemma* polynomial.mem_roots
- \- *lemma* polynomial.mem_roots_sub_C
- \- *lemma* polynomial.mem_support_derivative
- \- *def* polynomial.mod
- \- *lemma* polynomial.mod_X_sub_C_eq_C_eval
- \- *def* polynomial.mod_by_monic
- \- *lemma* polynomial.mod_by_monic_X
- \- *lemma* polynomial.mod_by_monic_X_sub_C_eq_C_eval
- \- *lemma* polynomial.mod_by_monic_add_div
- \- *lemma* polynomial.mod_by_monic_eq_mod
- \- *lemma* polynomial.mod_by_monic_eq_of_not_monic
- \- *lemma* polynomial.mod_by_monic_eq_self_iff
- \- *lemma* polynomial.mod_by_monic_eq_sub_mul_div
- \- *lemma* polynomial.mod_by_monic_one
- \- *lemma* polynomial.mod_by_monic_zero
- \- *lemma* polynomial.mod_def
- \- *lemma* polynomial.mod_eq_self_iff
- \- *lemma* polynomial.monic.as_sum
- \- *lemma* polynomial.monic.def
- \- *lemma* polynomial.monic.leading_coeff
- \- *lemma* polynomial.monic.ne_zero
- \- *lemma* polynomial.monic.ne_zero_of_zero_ne_one
- \- *def* polynomial.monic
- \- *lemma* polynomial.monic_X
- \- *theorem* polynomial.monic_X_add_C
- \- *theorem* polynomial.monic_X_pow_add
- \- *theorem* polynomial.monic_X_pow_sub
- \- *theorem* polynomial.monic_X_sub_C
- \- *lemma* polynomial.monic_integral_normalization
- \- *lemma* polynomial.monic_map
- \- *lemma* polynomial.monic_mul
- \- *lemma* polynomial.monic_mul_leading_coeff_inv
- \- *lemma* polynomial.monic_normalize
- \- *theorem* polynomial.monic_of_degree_le
- \- *lemma* polynomial.monic_of_injective
- \- *lemma* polynomial.monic_one
- \- *lemma* polynomial.monic_pow
- \- *def* polynomial.monomial
- \- *lemma* polynomial.monomial_add
- \- *lemma* polynomial.monomial_eq_smul_X
- \- *lemma* polynomial.monomial_one_eq_X_pow
- \- *lemma* polynomial.monomial_zero_left
- \- *lemma* polynomial.monomial_zero_right
- \- *theorem* polynomial.mul_X_pow_eq_zero
- \- *lemma* polynomial.mul_coeff_zero
- \- *lemma* polynomial.mul_comp
- \- *lemma* polynomial.mul_div_by_monic_eq_iff_is_root
- \- *lemma* polynomial.mul_div_eq_iff_is_root
- \- *lemma* polynomial.multiplicity_X_sub_C_finite
- \- *lemma* polynomial.multiplicity_finite_of_degree_pos_of_monic
- \- *def* polynomial.nat_degree
- \- *lemma* polynomial.nat_degree_C
- \- *lemma* polynomial.nat_degree_X
- \- *lemma* polynomial.nat_degree_X_le
- \- *lemma* polynomial.nat_degree_X_pow_sub_C
- \- *lemma* polynomial.nat_degree_X_sub_C
- \- *lemma* polynomial.nat_degree_X_sub_C_le
- \- *lemma* polynomial.nat_degree_coe_units
- \- *lemma* polynomial.nat_degree_comp
- \- *lemma* polynomial.nat_degree_comp_le
- \- *theorem* polynomial.nat_degree_derivative_lt
- \- *theorem* polynomial.nat_degree_div_by_monic
- \- *lemma* polynomial.nat_degree_eq_of_degree_eq
- \- *lemma* polynomial.nat_degree_eq_of_degree_eq_some
- \- *lemma* polynomial.nat_degree_eq_zero_iff_degree_le_zero
- \- *lemma* polynomial.nat_degree_int_cast
- \- *lemma* polynomial.nat_degree_le_nat_degree
- \- *theorem* polynomial.nat_degree_le_of_degree_le
- \- *theorem* polynomial.nat_degree_le_of_dvd
- \- *lemma* polynomial.nat_degree_map'
- \- *lemma* polynomial.nat_degree_map
- \- *lemma* polynomial.nat_degree_mul_eq'
- \- *lemma* polynomial.nat_degree_mul_eq
- \- *lemma* polynomial.nat_degree_mul_le
- \- *lemma* polynomial.nat_degree_nat_cast
- \- *lemma* polynomial.nat_degree_neg
- \- *lemma* polynomial.nat_degree_one
- \- *lemma* polynomial.nat_degree_pos_iff_degree_pos
- \- *lemma* polynomial.nat_degree_pos_of_aeval_root
- \- *lemma* polynomial.nat_degree_pos_of_eval₂_root
- \- *lemma* polynomial.nat_degree_pow_eq'
- \- *lemma* polynomial.nat_degree_pow_eq
- \- *lemma* polynomial.nat_degree_zero
- \- *lemma* polynomial.ne_zero_of_degree_gt
- \- *lemma* polynomial.ne_zero_of_monic
- \- *lemma* polynomial.ne_zero_of_monic_of_zero_ne_one
- \- *lemma* polynomial.ne_zero_of_ne_zero_of_monic
- \- *theorem* polynomial.nonzero.of_polynomial_ne
- \- *theorem* polynomial.not_is_unit_X
- \- *theorem* polynomial.not_is_unit_X_sub_C
- \- *lemma* polynomial.not_monic_zero
- \- *def* polynomial.nth_roots
- \- *theorem* polynomial.of_mem_support_derivative
- \- *lemma* polynomial.one_comp
- \- *theorem* polynomial.pairwise_coprime_X_sub
- \- *def* polynomial.pow_add_expansion
- \- *lemma* polynomial.pow_root_multiplicity_dvd
- \- *def* polynomial.pow_sub_pow_factor
- \- *theorem* polynomial.prime_X
- \- *theorem* polynomial.prime_X_sub_C
- \- *lemma* polynomial.prime_of_degree_eq_one
- \- *lemma* polynomial.prime_of_degree_eq_one_of_monic
- \- *lemma* polynomial.ring_hom_eval₂_algebra_map_int
- \- *lemma* polynomial.root_X_sub_C
- \- *lemma* polynomial.root_mul
- \- *lemma* polynomial.root_mul_left_of_is_root
- \- *lemma* polynomial.root_mul_right_of_is_root
- \- *def* polynomial.root_multiplicity
- \- *lemma* polynomial.root_multiplicity_eq_multiplicity
- \- *lemma* polynomial.root_or_root_of_root_mul
- \- *lemma* polynomial.roots_X_sub_C
- \- *lemma* polynomial.roots_mul
- \- *lemma* polynomial.single_eq_C_mul_X
- \- *lemma* polynomial.subsingleton_of_monic_zero
- \- *lemma* polynomial.sum_C_index
- \- *lemma* polynomial.sum_C_mul_X_eq
- \- *lemma* polynomial.sum_monomial_eq
- \- *lemma* polynomial.sum_over_range'
- \- *lemma* polynomial.sum_over_range
- \- *lemma* polynomial.support_integral_normalization
- \- *lemma* polynomial.support_zero
- \- *lemma* polynomial.zero_comp
- \- *lemma* polynomial.zero_div_by_monic
- \- *lemma* polynomial.zero_is_root_of_coeff_zero_eq_zero
- \- *lemma* polynomial.zero_le_degree_iff
- \- *lemma* polynomial.zero_mod_by_monic
- \- *def* polynomial

Added src/data/polynomial/algebra_map.lean
- \+ *lemma* polynomial.C_eq_algebra_map
- \+ *lemma* polynomial.C_inj
- \+ *lemma* polynomial.C_mul'
- \+ *def* polynomial.aeval
- \+ *lemma* polynomial.aeval_C
- \+ *lemma* polynomial.aeval_X
- \+ *theorem* polynomial.aeval_alg_hom
- \+ *theorem* polynomial.aeval_alg_hom_apply
- \+ *theorem* polynomial.aeval_def
- \+ *lemma* polynomial.alg_hom_eval₂_algebra_map
- \+ *lemma* polynomial.algebra_map_apply
- \+ *lemma* polynomial.dvd_term_of_dvd_eval_of_dvd_terms
- \+ *lemma* polynomial.dvd_term_of_is_root_of_dvd_terms
- \+ *lemma* polynomial.eval_comp
- \+ *lemma* polynomial.eval_mul
- \+ *lemma* polynomial.eval_mul_X_sub_C
- \+ *lemma* polynomial.eval_pow
- \+ *theorem* polynomial.eval_unique
- \+ *lemma* polynomial.eval₂_algebra_map_X
- \+ *lemma* polynomial.eval₂_algebra_map_int_X
- \+ *lemma* polynomial.eval₂_comp
- \+ *lemma* polynomial.eval₂_hom
- \+ *lemma* polynomial.is_root_of_aeval_algebra_map_eq_zero
- \+ *lemma* polynomial.is_root_of_eval₂_map_eq_zero
- \+ *lemma* polynomial.mul_comp
- \+ *theorem* polynomial.not_is_unit_X_sub_C
- \+ *lemma* polynomial.ring_hom_eval₂_algebra_map_int
- \+ *lemma* polynomial.root_mul_left_of_is_root
- \+ *lemma* polynomial.root_mul_right_of_is_root

Added src/data/polynomial/basic.lean
- \+ *def* polynomial.X
- \+ *lemma* polynomial.X_mul
- \+ *lemma* polynomial.X_pow_mul
- \+ *lemma* polynomial.X_pow_mul_assoc
- \+ *lemma* polynomial.apply_eq_coeff
- \+ *def* polynomial.coeff
- \+ *def* polynomial.coeff_coe_to_fun
- \+ *lemma* polynomial.coeff_mk
- \+ *lemma* polynomial.coeff_neg
- \+ *lemma* polynomial.coeff_one_zero
- \+ *lemma* polynomial.coeff_single
- \+ *lemma* polynomial.coeff_sub
- \+ *lemma* polynomial.coeff_zero
- \+ *lemma* polynomial.eq_zero_of_eq_zero
- \+ *lemma* polynomial.ext
- \+ *theorem* polynomial.ext_iff
- \+ *def* polynomial.monomial
- \+ *lemma* polynomial.monomial_add
- \+ *lemma* polynomial.monomial_zero_right
- \+ *lemma* polynomial.support_zero
- \+ *def* polynomial

Added src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.coeff_C_mul
- \+ *lemma* polynomial.coeff_C_mul_X
- \+ *lemma* polynomial.coeff_X_pow
- \+ *lemma* polynomial.coeff_add
- \+ *lemma* polynomial.coeff_mul
- \+ *lemma* polynomial.coeff_mul_C
- \+ *theorem* polynomial.coeff_mul_X
- \+ *theorem* polynomial.coeff_mul_X_pow
- \+ *lemma* polynomial.coeff_mul_X_zero
- \+ *lemma* polynomial.coeff_one
- \+ *lemma* polynomial.coeff_smul
- \+ *lemma* polynomial.coeff_sum
- \+ *def* polynomial.lcoeff
- \+ *lemma* polynomial.lcoeff_apply
- \+ *lemma* polynomial.monomial_eq_smul_X
- \+ *lemma* polynomial.monomial_one_eq_X_pow
- \+ *theorem* polynomial.mul_X_pow_eq_zero
- \+ *lemma* polynomial.mul_coeff_zero

Added src/data/polynomial/default.lean


Added src/data/polynomial/degree.lean
- \+ *lemma* polynomial.X_pow_sub_C_ne_zero
- \+ *theorem* polynomial.X_sub_C_ne_zero
- \+ *lemma* polynomial.coeff_mul_degree_add_degree
- \+ *lemma* polynomial.coeff_nat_degree_eq_zero_of_degree_lt
- \+ *lemma* polynomial.degree_X_pow
- \+ *lemma* polynomial.degree_X_pow_sub_C
- \+ *lemma* polynomial.degree_X_sub_C
- \+ *lemma* polynomial.degree_add_C
- \+ *lemma* polynomial.degree_add_eq_of_degree_lt
- \+ *lemma* polynomial.degree_add_eq_of_leading_coeff_add_ne_zero
- \+ *lemma* polynomial.degree_add_le
- \+ *lemma* polynomial.degree_erase_le
- \+ *lemma* polynomial.degree_erase_lt
- \+ *theorem* polynomial.degree_le_iff_coeff_zero
- \+ *lemma* polynomial.degree_le_zero_iff
- \+ *lemma* polynomial.degree_lt_degree_mul_X
- \+ *lemma* polynomial.degree_map'
- \+ *lemma* polynomial.degree_map_eq_of_injective
- \+ *lemma* polynomial.degree_map_eq_of_leading_coeff_ne_zero
- \+ *lemma* polynomial.degree_map_le
- \+ *lemma* polynomial.degree_mul_eq'
- \+ *lemma* polynomial.degree_mul_le
- \+ *lemma* polynomial.degree_nonneg_iff_ne_zero
- \+ *lemma* polynomial.degree_pos_of_eval₂_root
- \+ *lemma* polynomial.degree_pos_of_root
- \+ *lemma* polynomial.degree_pow_eq'
- \+ *lemma* polynomial.degree_pow_le
- \+ *lemma* polynomial.degree_sub_le
- \+ *lemma* polynomial.degree_sub_lt
- \+ *lemma* polynomial.degree_sum_le
- \+ *lemma* polynomial.eq_C_of_degree_eq_zero
- \+ *lemma* polynomial.eq_C_of_degree_le_zero
- \+ *lemma* polynomial.eq_C_of_nat_degree_le_zero
- \+ *lemma* polynomial.leading_coeff_C
- \+ *lemma* polynomial.leading_coeff_X
- \+ *lemma* polynomial.leading_coeff_X_pow
- \+ *lemma* polynomial.leading_coeff_add_of_degree_eq
- \+ *lemma* polynomial.leading_coeff_add_of_degree_lt
- \+ *lemma* polynomial.leading_coeff_eq_zero
- \+ *lemma* polynomial.leading_coeff_eq_zero_iff_deg_eq_bot
- \+ *lemma* polynomial.leading_coeff_monomial
- \+ *lemma* polynomial.leading_coeff_mul'
- \+ *theorem* polynomial.leading_coeff_mul_X_pow
- \+ *lemma* polynomial.leading_coeff_one
- \+ *lemma* polynomial.leading_coeff_pow'
- \+ *lemma* polynomial.leading_coeff_zero
- \+ *lemma* polynomial.monic.ne_zero
- \+ *lemma* polynomial.monic.ne_zero_of_zero_ne_one
- \+ *lemma* polynomial.monic_X
- \+ *lemma* polynomial.monic_one
- \+ *lemma* polynomial.nat_degree_X_pow_sub_C
- \+ *lemma* polynomial.nat_degree_X_sub_C
- \+ *lemma* polynomial.nat_degree_X_sub_C_le
- \+ *lemma* polynomial.nat_degree_comp_le
- \+ *lemma* polynomial.nat_degree_eq_zero_iff_degree_le_zero
- \+ *lemma* polynomial.nat_degree_map'
- \+ *lemma* polynomial.nat_degree_mul_eq'
- \+ *lemma* polynomial.nat_degree_mul_le
- \+ *lemma* polynomial.nat_degree_pos_iff_degree_pos
- \+ *lemma* polynomial.nat_degree_pos_of_eval₂_root
- \+ *lemma* polynomial.nat_degree_pow_eq'
- \+ *lemma* polynomial.ne_zero_of_degree_gt
- \+ *theorem* polynomial.not_is_unit_X
- \+ *lemma* polynomial.subsingleton_of_monic_zero
- \+ *lemma* polynomial.zero_le_degree_iff

Added src/data/polynomial/degree/basic.lean
- \+ *lemma* polynomial.C_eq_int_cast
- \+ *lemma* polynomial.coeff_eq_zero_of_degree_lt
- \+ *lemma* polynomial.coeff_eq_zero_of_nat_degree_lt
- \+ *lemma* polynomial.coeff_mul_X_sub_C
- \+ *lemma* polynomial.coeff_nat_degree_succ_eq_zero
- \+ *lemma* polynomial.coeff_ne_zero_of_eq_degree
- \+ *def* polynomial.degree
- \+ *lemma* polynomial.degree_C
- \+ *lemma* polynomial.degree_C_le
- \+ *theorem* polynomial.degree_C_mul_X_pow_le
- \+ *lemma* polynomial.degree_X
- \+ *theorem* polynomial.degree_X_le
- \+ *theorem* polynomial.degree_X_pow_le
- \+ *lemma* polynomial.degree_eq_bot
- \+ *lemma* polynomial.degree_eq_iff_nat_degree_eq
- \+ *lemma* polynomial.degree_eq_iff_nat_degree_eq_of_pos
- \+ *lemma* polynomial.degree_eq_nat_degree
- \+ *lemma* polynomial.degree_le_degree
- \+ *lemma* polynomial.degree_le_nat_degree
- \+ *lemma* polynomial.degree_lt_wf
- \+ *lemma* polynomial.degree_monomial
- \+ *lemma* polynomial.degree_monomial_le
- \+ *lemma* polynomial.degree_ne_of_nat_degree_ne
- \+ *lemma* polynomial.degree_neg
- \+ *lemma* polynomial.degree_one
- \+ *lemma* polynomial.degree_one_le
- \+ *lemma* polynomial.degree_zero
- \+ *lemma* polynomial.eq_X_add_C_of_degree_eq_one
- \+ *lemma* polynomial.eq_X_add_C_of_degree_le_one
- \+ *lemma* polynomial.ite_le_nat_degree_coeff
- \+ *lemma* polynomial.le_degree_of_ne_zero
- \+ *lemma* polynomial.le_nat_degree_of_ne_zero
- \+ *def* polynomial.leading_coeff
- \+ *lemma* polynomial.monic.def
- \+ *lemma* polynomial.monic.leading_coeff
- \+ *def* polynomial.monic
- \+ *def* polynomial.nat_degree
- \+ *lemma* polynomial.nat_degree_C
- \+ *lemma* polynomial.nat_degree_X
- \+ *lemma* polynomial.nat_degree_X_le
- \+ *lemma* polynomial.nat_degree_eq_of_degree_eq
- \+ *lemma* polynomial.nat_degree_eq_of_degree_eq_some
- \+ *lemma* polynomial.nat_degree_int_cast
- \+ *lemma* polynomial.nat_degree_le_nat_degree
- \+ *theorem* polynomial.nat_degree_le_of_degree_le
- \+ *lemma* polynomial.nat_degree_nat_cast
- \+ *lemma* polynomial.nat_degree_neg
- \+ *lemma* polynomial.nat_degree_one
- \+ *lemma* polynomial.nat_degree_zero

Added src/data/polynomial/derivative.lean
- \+ *lemma* polynomial.coeff_derivative
- \+ *lemma* polynomial.degree_derivative_eq
- \+ *theorem* polynomial.degree_derivative_le
- \+ *theorem* polynomial.degree_derivative_lt
- \+ *def* polynomial.derivative
- \+ *lemma* polynomial.derivative_C
- \+ *lemma* polynomial.derivative_X
- \+ *lemma* polynomial.derivative_add
- \+ *lemma* polynomial.derivative_eval
- \+ *theorem* polynomial.derivative_eval₂_C
- \+ *def* polynomial.derivative_hom
- \+ *def* polynomial.derivative_lhom
- \+ *theorem* polynomial.derivative_map
- \+ *lemma* polynomial.derivative_monomial
- \+ *lemma* polynomial.derivative_mul
- \+ *lemma* polynomial.derivative_neg
- \+ *lemma* polynomial.derivative_one
- \+ *theorem* polynomial.derivative_pow
- \+ *theorem* polynomial.derivative_pow_succ
- \+ *lemma* polynomial.derivative_smul
- \+ *lemma* polynomial.derivative_sub
- \+ *lemma* polynomial.derivative_sum
- \+ *lemma* polynomial.derivative_zero
- \+ *lemma* polynomial.is_coprime_of_is_root_of_eval_derivative_ne_zero
- \+ *lemma* polynomial.mem_support_derivative
- \+ *theorem* polynomial.nat_degree_derivative_lt
- \+ *theorem* polynomial.of_mem_support_derivative

Added src/data/polynomial/div.lean
- \+ *theorem* polynomial.X_dvd_iff
- \+ *def* polynomial.decidable_dvd_monic
- \+ *lemma* polynomial.degree_add_div_by_monic
- \+ *lemma* polynomial.degree_div_X_lt
- \+ *lemma* polynomial.degree_div_by_monic_le
- \+ *lemma* polynomial.degree_div_by_monic_lt
- \+ *theorem* polynomial.degree_mod_by_monic_le
- \+ *lemma* polynomial.degree_mod_by_monic_lt
- \+ *lemma* polynomial.degree_pos_induction_on
- \+ *def* polynomial.div_X
- \+ *lemma* polynomial.div_X_C
- \+ *lemma* polynomial.div_X_add
- \+ *lemma* polynomial.div_X_eq_zero_iff
- \+ *lemma* polynomial.div_X_mul_X_add
- \+ *def* polynomial.div_by_monic
- \+ *lemma* polynomial.div_by_monic_eq_of_not_monic
- \+ *lemma* polynomial.div_by_monic_eq_zero_iff
- \+ *lemma* polynomial.div_by_monic_mul_pow_root_multiplicity_eq
- \+ *lemma* polynomial.div_by_monic_one
- \+ *lemma* polynomial.div_by_monic_zero
- \+ *lemma* polynomial.div_mod_by_monic_unique
- \+ *lemma* polynomial.div_wf_lemma
- \+ *lemma* polynomial.dvd_iff_is_root
- \+ *lemma* polynomial.dvd_iff_mod_by_monic_eq_zero
- \+ *lemma* polynomial.eval_div_by_monic_pow_root_multiplicity_ne_zero
- \+ *lemma* polynomial.map_div_by_monic
- \+ *lemma* polynomial.map_mod_by_monic
- \+ *lemma* polynomial.map_mod_div_by_monic
- \+ *def* polynomial.mod_by_monic
- \+ *lemma* polynomial.mod_by_monic_X
- \+ *lemma* polynomial.mod_by_monic_X_sub_C_eq_C_eval
- \+ *lemma* polynomial.mod_by_monic_add_div
- \+ *lemma* polynomial.mod_by_monic_eq_of_not_monic
- \+ *lemma* polynomial.mod_by_monic_eq_self_iff
- \+ *lemma* polynomial.mod_by_monic_eq_sub_mul_div
- \+ *lemma* polynomial.mod_by_monic_one
- \+ *lemma* polynomial.mod_by_monic_zero
- \+ *lemma* polynomial.mul_div_by_monic_eq_iff_is_root
- \+ *lemma* polynomial.multiplicity_X_sub_C_finite
- \+ *lemma* polynomial.multiplicity_finite_of_degree_pos_of_monic
- \+ *theorem* polynomial.nat_degree_div_by_monic
- \+ *lemma* polynomial.pow_root_multiplicity_dvd
- \+ *def* polynomial.root_multiplicity
- \+ *lemma* polynomial.root_multiplicity_eq_multiplicity
- \+ *lemma* polynomial.zero_div_by_monic
- \+ *lemma* polynomial.zero_mod_by_monic

Added src/data/polynomial/eval.lean
- \+ *lemma* polynomial.C_comp
- \+ *lemma* polynomial.C_neg
- \+ *lemma* polynomial.C_sub
- \+ *lemma* polynomial.X_comp
- \+ *lemma* polynomial.add_comp
- \+ *lemma* polynomial.coe_eval₂_ring_hom
- \+ *lemma* polynomial.coeff_map
- \+ *lemma* polynomial.coeff_zero_eq_eval_zero
- \+ *def* polynomial.comp
- \+ *lemma* polynomial.comp_C
- \+ *lemma* polynomial.comp_X
- \+ *lemma* polynomial.comp_one
- \+ *lemma* polynomial.comp_zero
- \+ *def* polynomial.eval
- \+ *lemma* polynomial.eval_C
- \+ *lemma* polynomial.eval_X
- \+ *lemma* polynomial.eval_add
- \+ *lemma* polynomial.eval_bit0
- \+ *lemma* polynomial.eval_bit1
- \+ *lemma* polynomial.eval_int_cast
- \+ *lemma* polynomial.eval_map
- \+ *lemma* polynomial.eval_monomial
- \+ *lemma* polynomial.eval_nat_cast
- \+ *lemma* polynomial.eval_neg
- \+ *lemma* polynomial.eval_one
- \+ *lemma* polynomial.eval_smul
- \+ *lemma* polynomial.eval_sub
- \+ *lemma* polynomial.eval_sum
- \+ *lemma* polynomial.eval_zero
- \+ *def* polynomial.eval₂
- \+ *lemma* polynomial.eval₂_C
- \+ *lemma* polynomial.eval₂_X
- \+ *lemma* polynomial.eval₂_X_pow
- \+ *lemma* polynomial.eval₂_add
- \+ *lemma* polynomial.eval₂_bit0
- \+ *lemma* polynomial.eval₂_bit1
- \+ *lemma* polynomial.eval₂_eq_eval_map
- \+ *lemma* polynomial.eval₂_finset_sum
- \+ *lemma* polynomial.eval₂_map
- \+ *lemma* polynomial.eval₂_monomial
- \+ *lemma* polynomial.eval₂_mul
- \+ *lemma* polynomial.eval₂_nat_cast
- \+ *lemma* polynomial.eval₂_neg
- \+ *lemma* polynomial.eval₂_one
- \+ *lemma* polynomial.eval₂_pow
- \+ *def* polynomial.eval₂_ring_hom
- \+ *lemma* polynomial.eval₂_smul
- \+ *lemma* polynomial.eval₂_sub
- \+ *lemma* polynomial.eval₂_sum
- \+ *lemma* polynomial.eval₂_zero
- \+ *lemma* polynomial.hom_eval₂
- \+ *lemma* polynomial.is_root.def
- \+ *def* polynomial.is_root
- \+ *def* polynomial.map
- \+ *lemma* polynomial.map_C
- \+ *lemma* polynomial.map_X
- \+ *lemma* polynomial.map_add
- \+ *lemma* polynomial.map_id
- \+ *lemma* polynomial.map_injective
- \+ *lemma* polynomial.map_map
- \+ *lemma* polynomial.map_monomial
- \+ *lemma* polynomial.map_mul
- \+ *theorem* polynomial.map_nat_cast
- \+ *lemma* polynomial.map_neg
- \+ *lemma* polynomial.map_one
- \+ *lemma* polynomial.map_pow
- \+ *lemma* polynomial.map_sub
- \+ *lemma* polynomial.map_zero
- \+ *lemma* polynomial.mem_map_range
- \+ *lemma* polynomial.one_comp
- \+ *lemma* polynomial.root_X_sub_C
- \+ *lemma* polynomial.zero_comp
- \+ *lemma* polynomial.zero_is_root_of_coeff_zero_eq_zero

Added src/data/polynomial/field_division.lean
- \+ *lemma* polynomial.coe_norm_unit
- \+ *lemma* polynomial.coeff_inv_units
- \+ *lemma* polynomial.degree_add_div
- \+ *lemma* polynomial.degree_div_le
- \+ *lemma* polynomial.degree_div_lt
- \+ *lemma* polynomial.degree_map
- \+ *lemma* polynomial.degree_mul_leading_coeff_inv
- \+ *lemma* polynomial.degree_normalize
- \+ *lemma* polynomial.degree_pos_of_ne_zero_of_nonunit
- \+ *def* polynomial.div
- \+ *lemma* polynomial.div_by_monic_eq_div
- \+ *lemma* polynomial.div_def
- \+ *lemma* polynomial.div_eq_zero_iff
- \+ *lemma* polynomial.exists_root_of_degree_eq_one
- \+ *lemma* polynomial.irreducible_of_degree_eq_one
- \+ *lemma* polynomial.is_unit_iff_degree_eq_zero
- \+ *lemma* polynomial.leading_coeff_map
- \+ *lemma* polynomial.map_div
- \+ *lemma* polynomial.map_eq_zero
- \+ *lemma* polynomial.map_mod
- \+ *def* polynomial.mod
- \+ *lemma* polynomial.mod_X_sub_C_eq_C_eval
- \+ *lemma* polynomial.mod_by_monic_eq_mod
- \+ *lemma* polynomial.mod_def
- \+ *lemma* polynomial.mod_eq_self_iff
- \+ *lemma* polynomial.monic_mul_leading_coeff_inv
- \+ *lemma* polynomial.monic_normalize
- \+ *lemma* polynomial.mul_div_eq_iff_is_root
- \+ *lemma* polynomial.nat_degree_map
- \+ *theorem* polynomial.pairwise_coprime_X_sub
- \+ *lemma* polynomial.prime_of_degree_eq_one

Added src/data/polynomial/identities.lean
- \+ *def* polynomial.binom_expansion
- \+ *def* polynomial.eval_sub_factor
- \+ *def* polynomial.pow_add_expansion
- \+ *def* polynomial.pow_sub_pow_factor

Added src/data/polynomial/induction.lean
- \+ *lemma* polynomial.as_sum
- \+ *theorem* polynomial.coeff_monomial_mul
- \+ *theorem* polynomial.coeff_monomial_zero_mul
- \+ *theorem* polynomial.coeff_mul_monomial
- \+ *theorem* polynomial.coeff_mul_monomial_zero
- \+ *lemma* polynomial.finset_sum_coeff
- \+ *lemma* polynomial.sum_C_mul_X_eq
- \+ *lemma* polynomial.sum_monomial_eq
- \+ *lemma* polynomial.sum_over_range'
- \+ *lemma* polynomial.sum_over_range

Added src/data/polynomial/monic.lean
- \+ *lemma* polynomial.eq_one_of_is_unit_of_monic
- \+ *lemma* polynomial.integral_normalization_aeval_eq_zero
- \+ *lemma* polynomial.integral_normalization_coeff_degree
- \+ *lemma* polynomial.integral_normalization_coeff_nat_degree
- \+ *lemma* polynomial.integral_normalization_coeff_ne_degree
- \+ *lemma* polynomial.integral_normalization_coeff_ne_nat_degree
- \+ *lemma* polynomial.integral_normalization_eval₂_eq_zero
- \+ *lemma* polynomial.is_unit_C
- \+ *lemma* polynomial.leading_coeff_of_injective
- \+ *lemma* polynomial.monic.as_sum
- \+ *theorem* polynomial.monic_X_add_C
- \+ *theorem* polynomial.monic_X_pow_add
- \+ *theorem* polynomial.monic_X_pow_sub
- \+ *theorem* polynomial.monic_X_sub_C
- \+ *lemma* polynomial.monic_integral_normalization
- \+ *lemma* polynomial.monic_map
- \+ *lemma* polynomial.monic_mul
- \+ *theorem* polynomial.monic_of_degree_le
- \+ *lemma* polynomial.monic_of_injective
- \+ *lemma* polynomial.monic_pow
- \+ *lemma* polynomial.ne_zero_of_monic
- \+ *lemma* polynomial.ne_zero_of_monic_of_zero_ne_one
- \+ *lemma* polynomial.ne_zero_of_ne_zero_of_monic
- \+ *lemma* polynomial.not_monic_zero
- \+ *lemma* polynomial.support_integral_normalization

Added src/data/polynomial/monomial.lean
- \+ *def* polynomial.C
- \+ *lemma* polynomial.C_0
- \+ *lemma* polynomial.C_1
- \+ *lemma* polynomial.C_add
- \+ *lemma* polynomial.C_bit0
- \+ *lemma* polynomial.C_bit1
- \+ *lemma* polynomial.C_eq_nat_cast
- \+ *lemma* polynomial.C_mul
- \+ *lemma* polynomial.C_pow
- \+ *lemma* polynomial.X_ne_zero
- \+ *lemma* polynomial.coeff_C
- \+ *lemma* polynomial.coeff_C_zero
- \+ *lemma* polynomial.coeff_X
- \+ *lemma* polynomial.coeff_X_one
- \+ *lemma* polynomial.coeff_X_zero
- \+ *lemma* polynomial.monomial_zero_left
- \+ *theorem* polynomial.nonzero.of_polynomial_ne
- \+ *lemma* polynomial.single_eq_C_mul_X
- \+ *lemma* polynomial.sum_C_index

Added src/data/polynomial/ring_division.lean
- \+ *lemma* is_integral_domain.polynomial
- \+ *lemma* polynomial.card_nth_roots
- \+ *lemma* polynomial.card_roots'
- \+ *lemma* polynomial.card_roots
- \+ *lemma* polynomial.card_roots_X_pow_sub_C
- \+ *lemma* polynomial.card_roots_sub_C'
- \+ *lemma* polynomial.card_roots_sub_C
- \+ *lemma* polynomial.coeff_coe_units_zero_ne_zero
- \+ *lemma* polynomial.coeff_comp_degree_mul_degree
- \+ *lemma* polynomial.degree_coe_units
- \+ *lemma* polynomial.degree_eq_degree_of_associated
- \+ *lemma* polynomial.degree_eq_one_of_irreducible_of_root
- \+ *lemma* polynomial.degree_eq_zero_of_is_unit
- \+ *lemma* polynomial.degree_le_mul_left
- \+ *lemma* polynomial.degree_mul_eq
- \+ *lemma* polynomial.degree_pos_of_aeval_root
- \+ *lemma* polynomial.degree_pow_eq
- \+ *lemma* polynomial.exists_finset_roots
- \+ *theorem* polynomial.irreducible_X
- \+ *theorem* polynomial.irreducible_X_sub_C
- \+ *lemma* polynomial.irreducible_of_degree_eq_one_of_monic
- \+ *theorem* polynomial.is_unit_iff
- \+ *lemma* polynomial.leading_coeff_comp
- \+ *lemma* polynomial.leading_coeff_mul
- \+ *lemma* polynomial.leading_coeff_pow
- \+ *lemma* polynomial.mem_nth_roots
- \+ *lemma* polynomial.mem_roots
- \+ *lemma* polynomial.mem_roots_sub_C
- \+ *lemma* polynomial.nat_degree_coe_units
- \+ *lemma* polynomial.nat_degree_comp
- \+ *theorem* polynomial.nat_degree_le_of_dvd
- \+ *lemma* polynomial.nat_degree_mul_eq
- \+ *lemma* polynomial.nat_degree_pos_of_aeval_root
- \+ *lemma* polynomial.nat_degree_pow_eq
- \+ *def* polynomial.nth_roots
- \+ *theorem* polynomial.prime_X
- \+ *theorem* polynomial.prime_X_sub_C
- \+ *lemma* polynomial.prime_of_degree_eq_one_of_monic
- \+ *lemma* polynomial.root_mul
- \+ *lemma* polynomial.root_or_root_of_root_mul
- \+ *lemma* polynomial.roots_X_sub_C
- \+ *lemma* polynomial.roots_mul



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
- \+ *lemma* lt_base_pow_length_digits'
- \+ *lemma* lt_base_pow_length_digits
- \+ *lemma* of_digits_append
- \+ *lemma* of_digits_digits_append_digits
- \+ *lemma* of_digits_lt_base_pow_length'
- \+ *lemma* of_digits_lt_base_pow_length



## [2020-07-16 12:55:24](https://github.com/leanprover-community/mathlib/commit/a8c10e1)
chore(topology/algebra/ordered): rename `lim*_eq_of_tendsto` to `tendsto.lim*_eq` ([#3415](https://github.com/leanprover-community/mathlib/pull/3415))
Also add `tendsto_of_le_liminf_of_limsup_le`
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/measure_theory/integration.lean


Modified src/topology/algebra/ordered.lean
- \+ *theorem* filter.tendsto.liminf_eq
- \+ *theorem* filter.tendsto.limsup_eq
- \- *theorem* liminf_eq_of_tendsto
- \- *theorem* limsup_eq_of_tendsto
- \+ *theorem* tendsto_of_le_liminf_of_limsup_le



## [2020-07-16 07:53:56](https://github.com/leanprover-community/mathlib/commit/1311eb2)
feat(tactic/obviously): improve error reporting ([#3412](https://github.com/leanprover-community/mathlib/pull/3412))
If `obviously` (used for auto_params) fails, it now prints a more useful message than "chain tactic made no progress"
If the goal presented to obviously contains `sorry`, it just uses `sorry` to discard it.
#### Estimated changes
Modified src/category_theory/category/default.lean


Modified src/meta/expr.lean


Modified src/tactic/core.lean


Added src/tactic/obviously.lean




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


Added src/data/equiv/encodable/lattice.lean
- \+ *lemma* encodable.Union_decode2
- \+ *lemma* encodable.Union_decode2_cases
- \+ *theorem* encodable.Union_decode2_disjoint_on
- \+ *lemma* encodable.supr_decode2
- \+ *lemma* finset.nonempty_encodable

Modified src/data/rat/basic.lean


Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_compact.is_measurable

Modified src/measure_theory/measurable_space.lean
- \- *lemma* encodable.Union_decode2
- \- *lemma* encodable.Union_decode2_cases
- \- *theorem* measurable_space.Union_decode2_disjoint_on

Modified src/measure_theory/measure_space.lean
- \+ *theorem* measure_theory.measure.smul_apply
- \+ *lemma* measure_theory.outer_measure.exists_is_measurable_superset_of_trim_eq_zero
- \+ *lemma* measure_theory.outer_measure.trim_smul
- \+/\- *theorem* measure_theory.outer_measure.trim_zero

Modified src/measure_theory/outer_measure.lean
- \- *theorem* measure_theory.outer_measure.Union_aux
- \+ *lemma* measure_theory.outer_measure.le_inter_add_diff
- \+ *lemma* measure_theory.outer_measure.measure_of_eq_coe

Modified src/order/ideal.lean


Modified src/tactic/default.lean


Modified src/topology/algebra/infinite_sum.lean
- \+ *theorem* rel_sup_add
- \+ *theorem* rel_supr_sum
- \+ *theorem* rel_supr_tsum
- \+ *theorem* tsum_Union_decode2
- \+ *theorem* tsum_supr_decode2



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
- \+/\- *lemma* set.indicator_compl
- \+ *lemma* set.indicator_compl_add_self
- \+ *lemma* set.indicator_compl_add_self_apply
- \+ *lemma* set.indicator_self_add_compl
- \+ *lemma* set.indicator_self_add_compl_apply

Modified src/data/set/basic.lean
- \+ *theorem* set.eq_empty_of_not_nonempty
- \+ *lemma* set.insert_diff_self_of_not_mem

Modified src/data/support.lean
- \- *lemma* function.support_comp'
- \- *lemma* function.support_comp
- \- *lemma* function.support_comp_eq'
- \+ *lemma* function.support_comp_subset
- \+ *lemma* function.support_prod_mk
- \+ *lemma* function.support_subset_comp
- \+ *lemma* function.support_subset_iff'
- \+ *lemma* function.support_subset_iff

Modified src/logic/embedding.lean
- \+ *lemma* function.embedding.coe_subtype

Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/probability_mass_function.lean
- \+/\- *lemma* pmf.tsum_coe

Modified src/measure_theory/set_integral.lean


Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.map_at_top_finset_prod_le_of_prod_eq
- \+ *lemma* function.injective.map_at_top_finset_prod_eq

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* equiv.has_sum_iff_of_support
- \+ *lemma* equiv.summable_iff_of_has_sum_iff
- \+ *lemma* equiv.summable_iff_of_support
- \+ *lemma* equiv.tsum_eq
- \+ *lemma* equiv.tsum_eq_tsum_of_has_sum_iff_has_sum
- \+ *lemma* equiv.tsum_eq_tsum_of_support
- \+ *lemma* finset.tsum_subtype
- \+ *lemma* function.injective.has_sum_iff
- \+ *lemma* function.injective.summable_iff
- \+ *lemma* has_sum.add_compl
- \+ *lemma* has_sum.compl_add
- \+ *lemma* has_sum.has_sum_compl_iff
- \+ *lemma* has_sum.has_sum_iff_compl
- \- *lemma* has_sum.has_sum_ne_zero
- \+/\- *lemma* has_sum.has_sum_of_sum_eq
- \+/\- *lemma* has_sum.mul_left
- \+/\- *lemma* has_sum.neg
- \+ *lemma* has_sum.prod_fiberwise
- \+/\- *lemma* has_sum.sigma_of_has_sum
- \+ *lemma* has_sum.tsum_eq
- \+ *lemma* has_sum.unique
- \- *lemma* has_sum_hom
- \+/\- *lemma* has_sum_iff_has_sum
- \- *lemma* has_sum_iff_has_sum_of_iso
- \- *lemma* has_sum_iff_has_sum_of_ne_zero
- \+/\- *lemma* has_sum_iff_has_sum_of_ne_zero_bij
- \- *lemma* has_sum_iff_tendsto_nat_of_summable
- \- *lemma* has_sum_of_iso
- \- *lemma* has_sum_subtype_iff'
- \- *lemma* has_sum_subtype_iff
- \+ *lemma* has_sum_subtype_iff_indicator
- \- *lemma* has_sum_subtype_iff_of_eq_zero
- \+ *lemma* has_sum_subtype_iff_of_support_subset
- \+ *lemma* has_sum_subtype_support
- \- *lemma* has_sum_unique
- \+ *lemma* set.finite.summable_compl_iff
- \+ *lemma* sum_add_tsum_compl
- \- *lemma* sum_add_tsum_subtype
- \+ *lemma* summable.add_compl
- \+ *lemma* summable.comp_injective
- \+ *lemma* summable.compl_add
- \+ *lemma* summable.has_sum_iff_tendsto_nat
- \+ *lemma* summable.prod_factor
- \+ *lemma* summable.prod_symm
- \+ *lemma* summable.subtype
- \- *lemma* summable.summable_comp_of_injective
- \+ *lemma* summable.summable_compl_iff
- \+/\- *lemma* summable.summable_of_eq_zero_or_self
- \- *lemma* summable_iff_summable_ne_zero
- \- *lemma* summable_iff_summable_ne_zero_bij
- \+ *lemma* summable_of_ne_finset_zero
- \- *lemma* summable_subtype_iff
- \- *lemma* summable_sum_of_ne_finset_zero
- \+ *lemma* tsum_add_tsum_compl
- \+ *lemma* tsum_comm'
- \+ *lemma* tsum_comm
- \- *lemma* tsum_eq_has_sum
- \- *lemma* tsum_eq_tsum_of_iso
- \- *lemma* tsum_eq_tsum_of_ne_zero
- \+/\- *lemma* tsum_eq_tsum_of_ne_zero_bij
- \+/\- *lemma* tsum_eq_zero_add
- \- *lemma* tsum_equiv
- \+ *lemma* tsum_prod'
- \+ *lemma* tsum_prod
- \- *lemma* tsum_subtype_eq_sum
- \+/\- *lemma* tsum_zero

Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* nnreal.has_sum_coe
- \+/\- *lemma* nnreal.summable_coe



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
- \- *def* category_theory.limits.pullback_cone.is_limit.mk'
- \+/\- *def* category_theory.limits.pullback_cone.is_limit.mk
- \+ *def* category_theory.limits.pullback_cone.is_limit_aux'
- \+ *def* category_theory.limits.pullback_cone.is_limit_aux
- \- *def* category_theory.limits.pushout_cocone.is_colimit.mk'
- \+/\- *def* category_theory.limits.pushout_cocone.is_colimit.mk
- \+ *def* category_theory.limits.pushout_cocone.is_colimit_aux'
- \+ *def* category_theory.limits.pushout_cocone.is_colimit_aux



## [2020-07-15 00:57:03](https://github.com/leanprover-community/mathlib/commit/8495f76)
feat(geometry/manifold/times_cont_mdiff): smooth functions between manifolds ([#3387](https://github.com/leanprover-community/mathlib/pull/3387))
We define smooth functions between smooth manifolds, and prove their basic properties (including the facts that a composition of smooth functions is smooth, and that the tangent map of a smooth map is smooth).
To avoid reproving always the same stuff in manifolds, we build a general theory of local invariant properties in the model space (i.e., properties which are local, and invariant under the structure groupoids) and show that the lift of such properties to charted spaces automatically inherit all the good behavior of the original property. We apply this general machinery to prove most basic properties of smooth functions between manifolds.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean


Modified src/data/equiv/local_equiv.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/charted_space.lean
- \- *lemma* chart_at_model_space_eq
- \+ *lemma* chart_at_self_eq
- \+ *lemma* charted_space_self_atlas
- \+/\- *lemma* mem_groupoid_of_pregroupoid
- \- *lemma* model_space_atlas
- \+ *lemma* structure_groupoid.id_mem_maximal_atlas

Added src/geometry/manifold/local_invariant_properties.lean
- \+ *def* charted_space.lift_prop
- \+ *def* charted_space.lift_prop_at
- \+ *def* charted_space.lift_prop_on
- \+ *def* charted_space.lift_prop_within_at
- \+ *lemma* structure_groupoid.lift_prop_on_univ
- \+ *lemma* structure_groupoid.lift_prop_within_at_univ
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_at_chart
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_at_chart_symm
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_at_congr_iff_of_eventually_eq
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_at_congr_of_eventually_eq
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_at_of_lift_prop_within_at
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_at_of_mem_maximal_atlas
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_at_symm_of_mem_maximal_atlas
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_id
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_of_locally_lift_prop_on
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_on_chart
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_on_chart_symm
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_on_congr
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_on_congr_iff
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_on_indep_chart
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_on_mono
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_on_of_lift_prop
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_on_of_locally_lift_prop_on
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_on_of_mem_maximal_atlas
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_on_symm_of_mem_maximal_atlas
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_congr
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_congr_iff
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_congr_iff_of_eventually_eq
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_congr_of_eventually_eq
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_indep_chart
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_indep_chart_aux
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_inter'
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_inter
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_mono
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_of_lift_prop_at
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_of_lift_prop_at_of_mem_nhds
- \+ *structure* structure_groupoid.local_invariant_prop

Modified src/geometry/manifold/mfderiv.lean


Modified src/geometry/manifold/real_instances.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+/\- *lemma* ext_chart_preimage_inter_eq
- \+/\- *def* smooth_manifold_with_corners.maximal_atlas

Added src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* filter.eventually_eq.times_cont_mdiff_at_iff
- \+ *lemma* filter.eventually_eq.times_cont_mdiff_within_at_iff
- \+ *lemma* times_cont_diff_within_at_local_invariant_prop
- \+ *lemma* times_cont_diff_within_at_local_invariant_prop_id
- \+ *lemma* times_cont_diff_within_at_local_invariant_prop_mono
- \+ *def* times_cont_diff_within_at_prop
- \+ *lemma* times_cont_mdiff.comp
- \+ *lemma* times_cont_mdiff.continuous
- \+ *theorem* times_cont_mdiff.continuous_tangent_map
- \+ *lemma* times_cont_mdiff.mdifferentiable
- \+ *lemma* times_cont_mdiff.of_le
- \+ *lemma* times_cont_mdiff.of_succ
- \+ *lemma* times_cont_mdiff.times_cont_mdiff_at
- \+ *lemma* times_cont_mdiff.times_cont_mdiff_on
- \+ *theorem* times_cont_mdiff.times_cont_mdiff_tangent_map
- \+ *def* times_cont_mdiff
- \+ *lemma* times_cont_mdiff_at.comp
- \+ *lemma* times_cont_mdiff_at.congr_of_eventually_eq
- \+ *lemma* times_cont_mdiff_at.continuous_at
- \+ *lemma* times_cont_mdiff_at.mdifferentiable_at
- \+ *lemma* times_cont_mdiff_at.of_le
- \+ *lemma* times_cont_mdiff_at.of_succ
- \+ *lemma* times_cont_mdiff_at.times_cont_mdiff_within_at
- \+ *def* times_cont_mdiff_at
- \+ *lemma* times_cont_mdiff_at_const
- \+ *lemma* times_cont_mdiff_at_id
- \+ *lemma* times_cont_mdiff_at_iff_times_cont_diff_at
- \+ *lemma* times_cont_mdiff_at_iff_times_cont_mdiff_on_nhds
- \+ *lemma* times_cont_mdiff_at_top
- \+ *lemma* times_cont_mdiff_const
- \+ *lemma* times_cont_mdiff_id
- \+ *lemma* times_cont_mdiff_iff
- \+ *lemma* times_cont_mdiff_iff_times_cont_diff
- \+ *lemma* times_cont_mdiff_of_locally_times_cont_mdiff_on
- \+ *lemma* times_cont_mdiff_on.comp'
- \+ *lemma* times_cont_mdiff_on.comp
- \+ *lemma* times_cont_mdiff_on.congr
- \+ *lemma* times_cont_mdiff_on.continuous_on
- \+ *theorem* times_cont_mdiff_on.continuous_on_tangent_map_within
- \+ *lemma* times_cont_mdiff_on.continuous_on_tangent_map_within_aux
- \+ *lemma* times_cont_mdiff_on.mdifferentiable_on
- \+ *lemma* times_cont_mdiff_on.mono
- \+ *lemma* times_cont_mdiff_on.of_le
- \+ *lemma* times_cont_mdiff_on.of_succ
- \+ *theorem* times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within
- \+ *lemma* times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within_aux
- \+ *def* times_cont_mdiff_on
- \+ *lemma* times_cont_mdiff_on_chart
- \+ *lemma* times_cont_mdiff_on_chart_symm
- \+ *lemma* times_cont_mdiff_on_congr
- \+ *lemma* times_cont_mdiff_on_const
- \+ *lemma* times_cont_mdiff_on_id
- \+ *lemma* times_cont_mdiff_on_iff
- \+ *lemma* times_cont_mdiff_on_iff_times_cont_diff_on
- \+ *lemma* times_cont_mdiff_on_of_locally_times_cont_mdiff_on
- \+ *lemma* times_cont_mdiff_on_of_mem_maximal_atlas
- \+ *lemma* times_cont_mdiff_on_symm_of_mem_maximal_atlas
- \+ *lemma* times_cont_mdiff_on_top
- \+ *lemma* times_cont_mdiff_on_univ
- \+ *lemma* times_cont_mdiff_top
- \+ *lemma* times_cont_mdiff_within_at.comp'
- \+ *lemma* times_cont_mdiff_within_at.comp
- \+ *lemma* times_cont_mdiff_within_at.congr
- \+ *lemma* times_cont_mdiff_within_at.congr_of_eventually_eq
- \+ *lemma* times_cont_mdiff_within_at.continuous_within_at
- \+ *lemma* times_cont_mdiff_within_at.mdifferentiable_within_at
- \+ *lemma* times_cont_mdiff_within_at.mono
- \+ *lemma* times_cont_mdiff_within_at.of_le
- \+ *lemma* times_cont_mdiff_within_at.of_succ
- \+ *lemma* times_cont_mdiff_within_at.times_cont_mdiff_at
- \+ *def* times_cont_mdiff_within_at
- \+ *lemma* times_cont_mdiff_within_at_congr
- \+ *lemma* times_cont_mdiff_within_at_const
- \+ *lemma* times_cont_mdiff_within_at_id
- \+ *lemma* times_cont_mdiff_within_at_iff_nat
- \+ *lemma* times_cont_mdiff_within_at_iff_times_cont_diff_within_at
- \+ *lemma* times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds
- \+ *lemma* times_cont_mdiff_within_at_inter'
- \+ *lemma* times_cont_mdiff_within_at_inter
- \+ *lemma* times_cont_mdiff_within_at_top
- \+ *lemma* times_cont_mdiff_within_at_univ

Modified src/topology/basic.lean
- \+ *lemma* filter.eventually_eq.eq_of_nhds

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_within_at.congr_mono

Modified src/topology/local_homeomorph.lean
- \+/\- *lemma* local_homeomorph.of_set_trans_of_set
- \+/\- *lemma* local_homeomorph.of_set_univ_eq_refl
- \+ *lemma* local_homeomorph.preimage_open_of_open
- \+ *lemma* local_homeomorph.preimage_open_of_open_symm
- \+/\- *lemma* local_homeomorph.refl_local_equiv
- \+/\- *lemma* local_homeomorph.refl_symm



## [2020-07-14 16:40:34](https://github.com/leanprover-community/mathlib/commit/708e481)
chore(data/set/basic): simp attribute on set.image_subset_iff ([#3394](https://github.com/leanprover-community/mathlib/pull/3394))
see discussion here with @sgouezel :
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.233387.3A.20smooth.20functions.20on.20manifolds/near/203751071
#### Estimated changes
Modified src/data/analysis/filter.lean


Modified src/data/set/basic.lean
- \+/\- *theorem* set.image_subset_iff

Modified src/topology/basic.lean




## [2020-07-14 15:06:30](https://github.com/leanprover-community/mathlib/commit/6c1ae3b)
chore(category_theory/natural_isomorphism): move lemmas to correct namespace, add simp lemma ([#3401](https://github.com/leanprover-community/mathlib/pull/3401))
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/natural_isomorphism.lean
- \+/\- *def* category_theory.iso.app
- \+ *lemma* category_theory.iso.hom_inv_id_app
- \+ *lemma* category_theory.iso.inv_hom_id_app
- \- *lemma* category_theory.nat_iso.hom_app_inv_app_id
- \- *lemma* category_theory.nat_iso.hom_inv_id_app
- \- *lemma* category_theory.nat_iso.inv_app_hom_app_id
- \- *lemma* category_theory.nat_iso.inv_hom_id_app

Modified src/category_theory/opposites.lean


Modified src/category_theory/types.lean
- \+ *lemma* category_theory.functor_to_types.hom_inv_id_app_apply
- \+ *lemma* category_theory.functor_to_types.inv_hom_id_app_apply



## [2020-07-14 15:06:28](https://github.com/leanprover-community/mathlib/commit/f7825bf)
feat(algebra/polynomial): big_operators lemmas for polynomials ([#3378](https://github.com/leanprover-community/mathlib/pull/3378))
This starts a new folder algebra/polynomial. As we refactor data/polynomial.lean, much of that content should land in this folder.
#### Estimated changes
Added src/algebra/polynomial/basic.lean
- \+ *lemma* polynomial.coe_aeval_eq_eval
- \+ *lemma* polynomial.coeff_zero_eq_aeval_zero
- \+ *def* polynomial.leading_coeff_hom
- \+ *lemma* polynomial.leading_coeff_hom_apply

Added src/algebra/polynomial/big_operators.lean
- \+ *lemma* polynomial.leading_coeff_prod'
- \+ *lemma* polynomial.leading_coeff_prod
- \+ *lemma* polynomial.monic_prod_of_monic
- \+ *lemma* polynomial.nat_degree_prod_eq'
- \+ *lemma* polynomial.nat_degree_prod_eq
- \+ *lemma* polynomial.nat_degree_prod_eq_of_monic
- \+ *lemma* polynomial.nat_degree_prod_le



## [2020-07-14 14:42:05](https://github.com/leanprover-community/mathlib/commit/bcf61df)
feat(data/qpf): uniformity iff preservation of supp ([#3388](https://github.com/leanprover-community/mathlib/pull/3388))
#### Estimated changes
Modified src/data/pfunctor/univariate/basic.lean
- \+ *theorem* pfunctor.liftp_iff'
- \+ *theorem* pfunctor.supp_eq

Modified src/data/qpf/univariate/basic.lean
- \+ *def* qpf.liftp_preservation
- \+ *theorem* qpf.liftp_preservation_iff_uniform
- \+ *def* qpf.supp_preservation
- \+ *theorem* qpf.supp_preservation_iff_liftp_preservation
- \+ *theorem* qpf.supp_preservation_iff_uniform



## [2020-07-14 14:05:54](https://github.com/leanprover-community/mathlib/commit/02f2f94)
refactor(category_theory/finite_limits): missing piece of [#3320](https://github.com/leanprover-community/mathlib/pull/3320) ([#3400](https://github.com/leanprover-community/mathlib/pull/3400))
A recent PR [#3320](https://github.com/leanprover-community/mathlib/pull/3320) did some refactoring of special shapes of limits. It seems I forgot to include `wide_pullbacks` in that refactor, so I've done that here.
#### Estimated changes
Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \+ *def* category_theory.limits.wide_pullback_shape.diagram_iso_wide_cospan
- \+ *inductive* category_theory.limits.wide_pullback_shape.hom
- \+ *lemma* category_theory.limits.wide_pullback_shape.hom_id
- \+ *def* category_theory.limits.wide_pullback_shape.wide_cospan
- \+ *def* category_theory.limits.wide_pullback_shape
- \+ *def* category_theory.limits.wide_pushout_shape.diagram_iso_wide_span
- \+ *inductive* category_theory.limits.wide_pushout_shape.hom
- \+ *lemma* category_theory.limits.wide_pushout_shape.hom_id
- \+ *def* category_theory.limits.wide_pushout_shape.wide_span
- \+ *def* category_theory.limits.wide_pushout_shape
- \- *def* wide_pullback_shape.diagram_iso_wide_cospan
- \- *inductive* wide_pullback_shape.hom
- \- *lemma* wide_pullback_shape.hom_id
- \- *def* wide_pullback_shape.wide_cospan
- \- *def* wide_pullback_shape
- \- *def* wide_pushout_shape.diagram_iso_wide_span
- \- *inductive* wide_pushout_shape.hom
- \- *lemma* wide_pushout_shape.hom_id
- \- *def* wide_pushout_shape.wide_span
- \- *def* wide_pushout_shape



## [2020-07-14 11:42:20](https://github.com/leanprover-community/mathlib/commit/a0846da)
chore(category_theory/limits/over): split a slow file ([#3399](https://github.com/leanprover-community/mathlib/pull/3399))
This was previously the last file to finish compiling when compiling `category_theory/`. This PR splits it into some smaller pieces which can compile in parallel (and some pieces now come earlier in the import hierarchy).
No change to content.
#### Estimated changes
Modified src/category_theory/connected.lean


Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/over.lean
- \- *def* category_theory.over.construct_products.cones_equiv
- \- *def* category_theory.over.construct_products.cones_equiv_counit_iso
- \- *def* category_theory.over.construct_products.cones_equiv_functor
- \- *def* category_theory.over.construct_products.cones_equiv_inverse
- \- *def* category_theory.over.construct_products.cones_equiv_inverse_obj
- \- *def* category_theory.over.construct_products.cones_equiv_unit_iso
- \- *def* category_theory.over.construct_products.has_over_limit_discrete_of_wide_pullback_limit
- \- *def* category_theory.over.construct_products.over_binary_product_of_pullback
- \- *def* category_theory.over.construct_products.over_finite_products_of_finite_wide_pullbacks
- \- *def* category_theory.over.construct_products.over_product_of_wide_pullback
- \- *def* category_theory.over.construct_products.over_products_of_wide_pullbacks
- \- *def* category_theory.over.construct_products.wide_pullback_diagram_of_diagram_over
- \- *def* category_theory.over.creates_connected.nat_trans_in_over
- \- *def* category_theory.over.creates_connected.raise_cone
- \- *def* category_theory.over.creates_connected.raised_cone_is_limit
- \- *lemma* category_theory.over.creates_connected.raised_cone_lowers_to_original
- \- *def* category_theory.over.over_has_terminal

Added src/category_theory/limits/shapes/constructions/over/connected.lean
- \+ *def* category_theory.over.creates_connected.nat_trans_in_over
- \+ *def* category_theory.over.creates_connected.raise_cone
- \+ *def* category_theory.over.creates_connected.raised_cone_is_limit
- \+ *lemma* category_theory.over.creates_connected.raised_cone_lowers_to_original

Added src/category_theory/limits/shapes/constructions/over/default.lean


Added src/category_theory/limits/shapes/constructions/over/products.lean
- \+ *def* category_theory.over.construct_products.cones_equiv
- \+ *def* category_theory.over.construct_products.cones_equiv_counit_iso
- \+ *def* category_theory.over.construct_products.cones_equiv_functor
- \+ *def* category_theory.over.construct_products.cones_equiv_inverse
- \+ *def* category_theory.over.construct_products.cones_equiv_inverse_obj
- \+ *def* category_theory.over.construct_products.cones_equiv_unit_iso
- \+ *def* category_theory.over.construct_products.has_over_limit_discrete_of_wide_pullback_limit
- \+ *def* category_theory.over.construct_products.over_binary_product_of_pullback
- \+ *def* category_theory.over.construct_products.over_finite_products_of_finite_wide_pullbacks
- \+ *def* category_theory.over.construct_products.over_product_of_wide_pullback
- \+ *def* category_theory.over.construct_products.over_products_of_wide_pullbacks
- \+ *def* category_theory.over.construct_products.wide_pullback_diagram_of_diagram_over
- \+ *def* category_theory.over.over_has_terminal



## [2020-07-14 11:42:18](https://github.com/leanprover-community/mathlib/commit/0fff477)
feat(analysis/normed_space): complex Hahn-Banach theorem ([#3286](https://github.com/leanprover-community/mathlib/pull/3286))
This proves the complex Hahn-Banach theorem by reducing it to the real version.
The corollaries from [#3021](https://github.com/leanprover-community/mathlib/pull/3021) should be generalized as well at some point.
#### Estimated changes
Added src/analysis/normed_space/extend.lean
- \+ *lemma* norm_bound

Modified src/analysis/normed_space/hahn_banach.lean
- \+ *theorem* complex.exists_extension_norm_eq

Modified src/data/complex/basic.lean
- \+ *lemma* complex.I_mul
- \+ *lemma* complex.abs_ne_zero
- \+ *lemma* complex.of_real_smul



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
- \- *lemma* category_theory.limits.has_colimit.iso_of_nat_iso_hom_π
- \+ *lemma* category_theory.limits.has_colimit.iso_of_nat_iso_ι_hom

Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.coequalizer.iso_target_of_self
- \+ *lemma* category_theory.limits.coequalizer.iso_target_of_self_hom
- \+ *lemma* category_theory.limits.coequalizer.iso_target_of_self_inv
- \- *def* category_theory.limits.coequalizer.π_of_self
- \+ *def* category_theory.limits.equalizer.iso_source_of_self
- \+ *lemma* category_theory.limits.equalizer.iso_source_of_self_hom
- \+ *lemma* category_theory.limits.equalizer.iso_source_of_self_inv
- \- *def* category_theory.limits.equalizer.ι_of_self

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.cokernel_iso_of_eq
- \+ *lemma* category_theory.limits.cokernel_iso_of_eq_refl
- \+ *lemma* category_theory.limits.cokernel_iso_of_eq_trans
- \+ *def* category_theory.limits.cokernel_zero_iso_target
- \+ *lemma* category_theory.limits.cokernel_zero_iso_target_hom
- \+ *lemma* category_theory.limits.cokernel_zero_iso_target_inv
- \+ *def* category_theory.limits.kernel_iso_of_eq
- \+ *lemma* category_theory.limits.kernel_iso_of_eq_refl
- \+ *lemma* category_theory.limits.kernel_iso_of_eq_trans
- \+ *def* category_theory.limits.kernel_zero_iso_source
- \+ *lemma* category_theory.limits.kernel_zero_iso_source_hom
- \+ *lemma* category_theory.limits.kernel_zero_iso_source_inv



## [2020-07-14 09:01:17](https://github.com/leanprover-community/mathlib/commit/58dde5b)
chore(*): generalize tensor product to semirings ([#3389](https://github.com/leanprover-community/mathlib/pull/3389))
#### Estimated changes
Modified src/data/polynomial.lean


Modified src/linear_algebra/tensor_product.lean
- \+ *inductive* tensor_product.eqv
- \- *lemma* tensor_product.lift_aux.add
- \+/\- *lemma* tensor_product.lift_aux.smul
- \+/\- *def* tensor_product.lift_aux
- \+ *lemma* tensor_product.lift_aux_tmul
- \- *def* tensor_product.relators
- \+/\- *def* tensor_product.smul.aux
- \+ *theorem* tensor_product.smul.aux_of
- \+ *theorem* tensor_product.smul_tmul'
- \+/\- *def* tensor_product.tmul
- \+/\- *lemma* tensor_product.tmul_zero
- \+/\- *lemma* tensor_product.zero_tmul

Modified src/ring_theory/matrix_algebra.lean


Modified src/ring_theory/polynomial_algebra.lean


Modified src/ring_theory/tensor_product.lean




## [2020-07-14 01:25:26](https://github.com/leanprover-community/mathlib/commit/0410946)
chore(linear_algebra/nonsingular_inverse): swap update_row/column names ([#3393](https://github.com/leanprover-community/mathlib/pull/3393))
The names for `update_row` and `update_column` did not correspond to their definitions. Doing a global swap of the names keep all the proofs valid and makes the semantics match.
#### Estimated changes
Modified src/linear_algebra/nonsingular_inverse.lean
- \+/\- *lemma* matrix.cramer_apply
- \+/\- *def* matrix.cramer_map
- \+/\- *def* matrix.update_column
- \+/\- *lemma* matrix.update_column_ne
- \+/\- *lemma* matrix.update_column_self
- \- *lemma* matrix.update_column_transpose
- \+/\- *lemma* matrix.update_column_val
- \+/\- *def* matrix.update_row
- \+/\- *lemma* matrix.update_row_ne
- \+/\- *lemma* matrix.update_row_self
- \+ *lemma* matrix.update_row_transpose
- \+/\- *lemma* matrix.update_row_val



## [2020-07-13 20:57:57](https://github.com/leanprover-community/mathlib/commit/32c75d0)
feat(linear_algebra/affine_space): more lemmas on directions of affine subspaces ([#3377](https://github.com/leanprover-community/mathlib/pull/3377))
Add more lemmas on directions of affine subspaces, motivated by uses
for Euclidean geometry.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *lemma* affine_subspace.coe_direction_eq_vsub_set_left
- \+ *lemma* affine_subspace.coe_direction_eq_vsub_set_right
- \+ *lemma* affine_subspace.direction_le
- \+ *lemma* affine_subspace.direction_lt_of_nonempty
- \+ *lemma* affine_subspace.inter_eq_singleton_of_nonempty_of_is_compl
- \+ *lemma* affine_subspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
- \+ *lemma* affine_subspace.mem_direction_iff_eq_vsub_left
- \+ *lemma* affine_subspace.mem_direction_iff_eq_vsub_right
- \+ *lemma* affine_subspace.sup_direction_le
- \+ *lemma* affine_subspace.sup_direction_lt_of_nonempty_of_inter_empty
- \+ *lemma* affine_subspace.vsub_left_mem_direction_iff_mem
- \+ *lemma* affine_subspace.vsub_right_mem_direction_iff_mem



## [2020-07-13 20:02:35](https://github.com/leanprover-community/mathlib/commit/1132237)
feat(ring_theory/ideal_over): lemmas for nonzero ideals lying over nonzero ideals ([#3385](https://github.com/leanprover-community/mathlib/pull/3385))
Let `f` be a ring homomorphism from `R` to `S` and `I` be an ideal in `S`. To show that `I.comap f` is not the zero ideal, we can show `I` contains a non-zero root of some non-zero polynomial `p : polynomial R`. As a corollary, if `S` is algebraic over `R` (e.g. the integral closure of `R`), nonzero ideals in `S` lie over nonzero ideals in `R`.
I created a new file because `integral_closure.comap_ne_bot` depends on `comap_ne_bot_of_algebraic_mem`, but `ring_theory/algebraic.lean` imports `ring_theory/integral_closure.lean` and I didn't see any obvious join in the dependency graph where they both belonged.
#### Estimated changes
Modified src/linear_algebra/basic.lean


Added src/ring_theory/ideal_over.lean
- \+ *lemma* ideal.coeff_zero_mem_comap_of_root_mem
- \+ *lemma* ideal.comap_ne_bot_of_algebraic_mem
- \+ *lemma* ideal.comap_ne_bot_of_integral_mem
- \+ *lemma* ideal.comap_ne_bot_of_root_mem
- \+ *lemma* ideal.exists_coeff_ne_zero_mem_comap_of_root_mem
- \+ *lemma* ideal.integral_closure.comap_ne_bot
- \+ *lemma* ideal.integral_closure.eq_bot_of_comap_eq_bot

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
- \+ *lemma* submodule.inner_left_of_mem_orthogonal
- \+ *lemma* submodule.inner_right_of_mem_orthogonal
- \+ *lemma* submodule.is_compl_orthogonal_of_is_complete
- \+ *lemma* submodule.le_orthogonal_orthogonal
- \+ *lemma* submodule.mem_orthogonal'
- \+ *lemma* submodule.mem_orthogonal
- \+ *def* submodule.orthogonal
- \+ *lemma* submodule.orthogonal_disjoint
- \+ *lemma* submodule.sup_orthogonal_of_is_complete



## [2020-07-13 19:01:01](https://github.com/leanprover-community/mathlib/commit/2ae7ad8)
feat(functor): definition multivariate functors ([#3360](https://github.com/leanprover-community/mathlib/pull/3360))
One part of [#3317](https://github.com/leanprover-community/mathlib/pull/3317)
#### Estimated changes
Added src/control/functor/multivariate.lean
- \+ *lemma* mvfunctor.exists_iff_exists_of_mono
- \+ *lemma* mvfunctor.id_map'
- \+ *lemma* mvfunctor.id_map
- \+ *def* mvfunctor.liftp'
- \+ *def* mvfunctor.liftp
- \+ *lemma* mvfunctor.liftp_def
- \+ *lemma* mvfunctor.liftp_last_pred_iff
- \+ *def* mvfunctor.liftr'
- \+ *def* mvfunctor.liftr
- \+ *lemma* mvfunctor.liftr_def
- \+ *lemma* mvfunctor.liftr_last_rel_iff
- \+ *lemma* mvfunctor.map_map
- \+ *theorem* mvfunctor.of_mem_supp
- \+ *def* mvfunctor.supp

Added src/data/fin2.lean
- \+ *def* fin2.add
- \+ *def* fin2.elim0
- \+ *def* fin2.insert_perm
- \+ *def* fin2.left
- \+ *def* fin2.of_nat'
- \+ *def* fin2.opt_of_nat
- \+ *def* fin2.remap_left
- \+ *def* fin2.to_nat
- \+ *inductive* fin2

Added src/data/typevec.lean
- \+ *def* typevec.append1
- \+ *def* typevec.append1_cases
- \+ *theorem* typevec.append1_cases_append1
- \+ *theorem* typevec.append1_drop_last
- \+ *def* typevec.append_fun
- \+ *theorem* typevec.append_fun_aux
- \+ *lemma* typevec.append_fun_comp'
- \+ *lemma* typevec.append_fun_comp
- \+ *theorem* typevec.append_fun_comp_id
- \+ *theorem* typevec.append_fun_comp_split_fun
- \+ *theorem* typevec.append_fun_id_id
- \+ *theorem* typevec.append_fun_inj
- \+ *lemma* typevec.append_prod_append_fun
- \+ *def* typevec.arrow.mp
- \+ *def* typevec.arrow.mpr
- \+ *def* typevec.arrow
- \+ *def* typevec.comp
- \+ *theorem* typevec.comp_assoc
- \+ *theorem* typevec.comp_id
- \+ *lemma* typevec.const_append1
- \+ *lemma* typevec.const_iff_true
- \+ *lemma* typevec.const_nil
- \+ *def* typevec.curry
- \+ *def* typevec.diag_sub
- \+ *lemma* typevec.diag_sub_val
- \+ *def* typevec.drop
- \+ *theorem* typevec.drop_append1'
- \+ *theorem* typevec.drop_append1
- \+ *def* typevec.drop_fun
- \+ *theorem* typevec.drop_fun_append_fun
- \+ *theorem* typevec.drop_fun_comp
- \+ *theorem* typevec.drop_fun_split_fun
- \+ *def* typevec.drop_repeat
- \+ *lemma* typevec.eq_nil_fun
- \+ *theorem* typevec.eq_of_drop_last_eq
- \+ *theorem* typevec.fst_diag
- \+ *theorem* typevec.fst_prod_mk
- \+ *def* typevec.id
- \+ *theorem* typevec.id_comp
- \+ *lemma* typevec.id_eq_nil_fun
- \+ *def* typevec.last
- \+ *theorem* typevec.last_append1
- \+ *def* typevec.last_fun
- \+ *theorem* typevec.last_fun_append_fun
- \+ *theorem* typevec.last_fun_comp
- \+ *theorem* typevec.last_fun_split_fun
- \+ *def* typevec.nil_fun
- \+ *lemma* typevec.nil_fun_comp
- \+ *def* typevec.of_repeat
- \+ *def* typevec.of_subtype'
- \+ *def* typevec.of_subtype
- \+ *def* typevec.pred_last'
- \+ *def* typevec.pred_last
- \+ *def* typevec.prod.diag
- \+ *def* typevec.prod.fst
- \+ *def* typevec.prod.mk
- \+ *def* typevec.prod.snd
- \+ *def* typevec.prod
- \+ *lemma* typevec.prod_id
- \+ *def* typevec.rel_last'
- \+ *def* typevec.rel_last
- \+ *def* typevec.repeat
- \+ *def* typevec.repeat_eq
- \+ *lemma* typevec.repeat_eq_append1
- \+ *lemma* typevec.repeat_eq_iff_eq
- \+ *lemma* typevec.repeat_eq_nil
- \+ *theorem* typevec.snd_diag
- \+ *theorem* typevec.snd_prod_mk
- \+ *theorem* typevec.split_drop_fun_last_fun
- \+ *def* typevec.split_fun
- \+ *theorem* typevec.split_fun_comp
- \+ *theorem* typevec.split_fun_inj
- \+ *def* typevec.subtype_
- \+ *def* typevec.subtype_val
- \+ *lemma* typevec.subtype_val_nil
- \+ *def* typevec.to_append1_drop_last
- \+ *def* typevec.to_subtype'
- \+ *def* typevec.to_subtype
- \+ *def* typevec.typevec_cases_cons₂
- \+ *lemma* typevec.typevec_cases_cons₂_append_fun
- \+ *def* typevec.typevec_cases_cons₃
- \+ *def* typevec.typevec_cases_nil₂
- \+ *lemma* typevec.typevec_cases_nil₂_append_fun
- \+ *def* typevec.typevec_cases_nil₃
- \+ *def* typevec

Modified src/number_theory/dioph.lean
- \- *def* fin2.add
- \- *def* fin2.elim0
- \- *def* fin2.insert_perm
- \- *def* fin2.left
- \- *def* fin2.of_nat'
- \- *def* fin2.opt_of_nat
- \- *def* fin2.remap_left
- \- *def* fin2.to_nat
- \- *inductive* fin2



## [2020-07-13 12:37:11](https://github.com/leanprover-community/mathlib/commit/f034899)
feat(data/equiv/mul_add): conj as a mul_aut ([#3367](https://github.com/leanprover-community/mathlib/pull/3367))
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *lemma* add_aut.inv_def
- \+ *lemma* add_aut.mul_apply
- \+ *lemma* add_aut.mul_def
- \+ *lemma* add_aut.one_apply
- \+ *lemma* add_aut.one_def
- \+ *def* mul_aut.conj
- \+ *lemma* mul_aut.conj_apply
- \+ *lemma* mul_aut.conj_symm_apply
- \+ *lemma* mul_aut.inv_def
- \+ *lemma* mul_aut.mul_apply
- \+ *lemma* mul_aut.mul_def
- \+ *lemma* mul_aut.one_apply
- \+ *lemma* mul_aut.one_def

Modified src/group_theory/semidirect_product.lean




## [2020-07-13 09:46:22](https://github.com/leanprover-community/mathlib/commit/e26b459)
feat(data/polynomial): some lemmas about eval2 and algebra_map ([#3382](https://github.com/leanprover-community/mathlib/pull/3382))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.C_eq_algebra_map
- \+ *lemma* polynomial.alg_hom_eval₂_algebra_map
- \+ *lemma* polynomial.eval₂_algebra_map_X
- \+ *lemma* polynomial.eval₂_algebra_map_int_X
- \+ *lemma* polynomial.ring_hom_eval₂_algebra_map_int

Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra.algebra_ext
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
- \+ *lemma* AddCommGroup.image_map

Modified src/category_theory/arrow.lean
- \+ *def* category_theory.functor.map_arrow

Modified src/category_theory/limits/types.lean
- \+ *lemma* category_theory.limits.types.image_map



## [2020-07-12 09:02:34](https://github.com/leanprover-community/mathlib/commit/fa6c45a)
feat(data/polynomial): simp lemmas for bit0 / bit1 ([#3376](https://github.com/leanprover-community/mathlib/pull/3376))
Add lemmas on polynomials and bit0/bit1 (as suggested [here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Eval.20of.20constant.20polynomial))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.C_bit0
- \+ *lemma* polynomial.C_bit1
- \+ *lemma* polynomial.eval_bit0
- \+ *lemma* polynomial.eval_bit1
- \+ *lemma* polynomial.eval₂_bit0
- \+ *lemma* polynomial.eval₂_bit1



## [2020-07-12 07:43:26](https://github.com/leanprover-community/mathlib/commit/4e603f4)
feat(geometry/manifold/charted_space):  typeclass `closed_under_restriction` for structure groupoids ([#3347](https://github.com/leanprover-community/mathlib/pull/3347))
* Define a typeclass `closed_under_restriction` for structure groupoids.
* Prove that it is equivalent to requiring that the structure groupoid contain all local homeomorphisms equivalent to the restriction of the identity to an open subset.
* Verify that `continuous_groupoid` and `times_cont_diff_groupoid` satisfy `closed_under_restriction`.  
* Show that a charted space defined by a single chart is `has_groupoid` for any structure groupoid satisfying `closed_under_restriction`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Restriction.20in.20structure.20groupoid)
#### Estimated changes
Modified src/geometry/manifold/charted_space.lean
- \+ *lemma* closed_under_restriction_iff_id_le
- \+ *def* id_restr_groupoid
- \+ *lemma* id_restr_groupoid_mem
- \+ *def* singleton_charted_space
- \+ *lemma* singleton_charted_space_one_chart
- \+ *lemma* singleton_has_groupoid

Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.of_set_trans_of_set
- \+ *lemma* local_homeomorph.of_set_univ_eq_refl



## [2020-07-12 05:07:52](https://github.com/leanprover-community/mathlib/commit/0e1c2bc)
feat(algebra/add_torsor): more cancellation lemmas ([#3368](https://github.com/leanprover-community/mathlib/pull/3368))
Add more cancellation lemmas for `vsub`, similar to lemmas already
present for `vadd`.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* add_torsor.vsub_left_cancel
- \+ *lemma* add_torsor.vsub_left_cancel_iff
- \+ *lemma* add_torsor.vsub_right_cancel
- \+ *lemma* add_torsor.vsub_right_cancel_iff



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
- \+/\- *lemma* finset.prod_attach
- \+ *lemma* finset.prod_filter_of_ne

Modified src/data/finset/basic.lean
- \+ *theorem* finset.image_subset_iff

Modified src/data/finsupp.lean


Modified src/data/set/countable.lean


Modified src/data/set/finite.lean
- \+/\- *lemma* finset.image_preimage
- \+ *lemma* finset.image_preimage_of_bij
- \+ *lemma* finset.image_subset_iff_subset_preimage
- \+ *lemma* finset.map_subset_iff_subset_preimage
- \+ *lemma* finset.prod_preimage_of_bij

Modified src/data/set/function.lean
- \+ *theorem* set.bij_on.subset_range
- \+ *theorem* set.surj_on.subset_range

Modified src/linear_algebra/basis.lean


Modified src/logic/function/basic.lean
- \+/\- *theorem* function.inv_fun_on_eq'

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
Added src/category_theory/arrow.lean
- \+ *def* category_theory.arrow.hom_mk'
- \+ *def* category_theory.arrow.hom_mk
- \+ *lemma* category_theory.arrow.id_left
- \+ *lemma* category_theory.arrow.id_right
- \+ *lemma* category_theory.arrow.lift.fac_left
- \+ *lemma* category_theory.arrow.lift.fac_right
- \+ *abbreviation* category_theory.arrow.lift
- \+ *lemma* category_theory.arrow.lift_mk'_left
- \+ *lemma* category_theory.arrow.lift_mk'_right
- \+ *def* category_theory.arrow.mk
- \+ *lemma* category_theory.arrow.w
- \+ *def* category_theory.arrow

Modified src/category_theory/comma.lean
- \- *def* category_theory.arrow.hom_mk'
- \- *def* category_theory.arrow.hom_mk
- \- *lemma* category_theory.arrow.id_left
- \- *lemma* category_theory.arrow.id_right
- \- *lemma* category_theory.arrow.lift.fac_left
- \- *lemma* category_theory.arrow.lift.fac_right
- \- *abbreviation* category_theory.arrow.lift
- \- *lemma* category_theory.arrow.lift_mk'_left
- \- *lemma* category_theory.arrow.lift_mk'_right
- \- *def* category_theory.arrow.mk
- \- *lemma* category_theory.arrow.w
- \- *def* category_theory.arrow
- \- *lemma* category_theory.over.comp_left
- \- *def* category_theory.over.forget
- \- *lemma* category_theory.over.forget_map
- \- *lemma* category_theory.over.forget_obj
- \- *def* category_theory.over.hom_mk
- \- *lemma* category_theory.over.id_left
- \- *def* category_theory.over.iterated_slice_backward
- \- *lemma* category_theory.over.iterated_slice_backward_forget_forget
- \- *def* category_theory.over.iterated_slice_equiv
- \- *def* category_theory.over.iterated_slice_forward
- \- *lemma* category_theory.over.iterated_slice_forward_forget
- \- *def* category_theory.over.map
- \- *lemma* category_theory.over.map_map_left
- \- *lemma* category_theory.over.map_obj_hom
- \- *lemma* category_theory.over.map_obj_left
- \- *def* category_theory.over.mk
- \- *lemma* category_theory.over.mk_hom
- \- *lemma* category_theory.over.mk_left
- \- *lemma* category_theory.over.over_morphism.ext
- \- *lemma* category_theory.over.over_right
- \- *def* category_theory.over.post
- \- *lemma* category_theory.over.w
- \- *def* category_theory.over
- \- *lemma* category_theory.under.comp_right
- \- *def* category_theory.under.forget
- \- *lemma* category_theory.under.forget_map
- \- *lemma* category_theory.under.forget_obj
- \- *def* category_theory.under.hom_mk
- \- *lemma* category_theory.under.id_right
- \- *def* category_theory.under.map
- \- *lemma* category_theory.under.map_map_right
- \- *lemma* category_theory.under.map_obj_hom
- \- *lemma* category_theory.under.map_obj_right
- \- *def* category_theory.under.mk
- \- *def* category_theory.under.post
- \- *lemma* category_theory.under.under_left
- \- *lemma* category_theory.under.under_morphism.ext
- \- *lemma* category_theory.under.w
- \- *def* category_theory.under

Modified src/category_theory/elements.lean


Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/shapes/strong_epi.lean


Added src/category_theory/over.lean
- \+ *lemma* category_theory.over.comp_left
- \+ *def* category_theory.over.forget
- \+ *lemma* category_theory.over.forget_map
- \+ *lemma* category_theory.over.forget_obj
- \+ *def* category_theory.over.hom_mk
- \+ *lemma* category_theory.over.id_left
- \+ *def* category_theory.over.iterated_slice_backward
- \+ *lemma* category_theory.over.iterated_slice_backward_forget_forget
- \+ *def* category_theory.over.iterated_slice_equiv
- \+ *def* category_theory.over.iterated_slice_forward
- \+ *lemma* category_theory.over.iterated_slice_forward_forget
- \+ *def* category_theory.over.map
- \+ *lemma* category_theory.over.map_map_left
- \+ *lemma* category_theory.over.map_obj_hom
- \+ *lemma* category_theory.over.map_obj_left
- \+ *def* category_theory.over.mk
- \+ *lemma* category_theory.over.mk_hom
- \+ *lemma* category_theory.over.mk_left
- \+ *lemma* category_theory.over.over_morphism.ext
- \+ *lemma* category_theory.over.over_right
- \+ *def* category_theory.over.post
- \+ *lemma* category_theory.over.w
- \+ *def* category_theory.over
- \+ *lemma* category_theory.under.comp_right
- \+ *def* category_theory.under.forget
- \+ *lemma* category_theory.under.forget_map
- \+ *lemma* category_theory.under.forget_obj
- \+ *def* category_theory.under.hom_mk
- \+ *lemma* category_theory.under.id_right
- \+ *def* category_theory.under.map
- \+ *lemma* category_theory.under.map_map_right
- \+ *lemma* category_theory.under.map_obj_hom
- \+ *lemma* category_theory.under.map_obj_right
- \+ *def* category_theory.under.mk
- \+ *def* category_theory.under.post
- \+ *lemma* category_theory.under.under_left
- \+ *lemma* category_theory.under.under_morphism.ext
- \+ *lemma* category_theory.under.w
- \+ *def* category_theory.under



## [2020-07-11 08:43:40](https://github.com/leanprover-community/mathlib/commit/f742a3d)
refactor(tactic/push_neg): simp ¬ (p ∧ q) better ([#3362](https://github.com/leanprover-community/mathlib/pull/3362))
This simplifies `¬ (p ∧ q)` to `(p → ¬ q)` instead of `¬ p ∨ ¬ q`. This has better behavior when going between `\forall x, P -> Q` and `\exists x, P /\ Q'` where `Q` and `Q'` are opposite.
#### Estimated changes
Modified src/data/pequiv.lean


Modified src/order/filter/at_top_bot.lean


Modified src/tactic/push_neg.lean
- \+/\- *theorem* push_neg.not_and_eq

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


Added src/tactic/delta_instance.lean


Added src/tactic/fix_by_cases.lean


Modified src/tactic/omega/coeffs.lean


Modified src/topology/category/Top/basic.lean
- \+/\- *def* Top

Modified src/topology/category/UniformSpace.lean
- \+/\- *def* UniformSpace



## [2020-07-11 07:58:56](https://github.com/leanprover-community/mathlib/commit/75b9cfa)
feat(category/has_shift): missing simp lemmas ([#3365](https://github.com/leanprover-community/mathlib/pull/3365))
#### Estimated changes
Modified src/category_theory/graded_object.lean
- \+ *lemma* category_theory.graded_object.shift_functor_map_apply
- \+ *lemma* category_theory.graded_object.shift_functor_obj_apply



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
- \+ *def* functor.liftp
- \+ *def* functor.liftr
- \+ *theorem* functor.of_mem_supp
- \+ *def* functor.supp

Added src/data/pfunctor/univariate/M.lean
- \+ *lemma* pfunctor.M.R_is_bisimulation
- \+ *inductive* pfunctor.M.agree'
- \+ *lemma* pfunctor.M.agree'_refl
- \+ *lemma* pfunctor.M.agree_iff_agree'
- \+ *lemma* pfunctor.M.approx_mk
- \+ *theorem* pfunctor.M.bisim'
- \+ *lemma* pfunctor.M.bisim
- \+ *theorem* pfunctor.M.bisim_equiv
- \+ *lemma* pfunctor.M.cases_mk
- \+ *lemma* pfunctor.M.cases_on_mk'
- \+ *lemma* pfunctor.M.cases_on_mk
- \+ *def* pfunctor.M.children
- \+ *lemma* pfunctor.M.children_mk
- \+ *lemma* pfunctor.M.coinduction'
- \+ *lemma* pfunctor.M.coinduction
- \+ *def* pfunctor.M.corec'
- \+ *lemma* pfunctor.M.corec_def
- \+ *def* pfunctor.M.corec_on
- \+ *theorem* pfunctor.M.corec_unique
- \+ *def* pfunctor.M.corec₁
- \+ *lemma* pfunctor.M.default_consistent
- \+ *def* pfunctor.M.dest
- \+ *lemma* pfunctor.M.dest_corec
- \+ *lemma* pfunctor.M.dest_mk
- \+ *theorem* pfunctor.M.eq_of_bisim
- \+ *lemma* pfunctor.M.ext'
- \+ *lemma* pfunctor.M.ext
- \+ *lemma* pfunctor.M.ext_aux
- \+ *lemma* pfunctor.M.head'_eq_head
- \+ *def* pfunctor.M.head
- \+ *lemma* pfunctor.M.head_eq_head'
- \+ *lemma* pfunctor.M.head_mk
- \+ *lemma* pfunctor.M.head_succ
- \+ *def* pfunctor.M.ichildren
- \+ *lemma* pfunctor.M.ichildren_mk
- \+ *structure* pfunctor.M.is_bisimulation
- \+ *inductive* pfunctor.M.is_path
- \+ *lemma* pfunctor.M.is_path_cons'
- \+ *lemma* pfunctor.M.is_path_cons
- \+ *def* pfunctor.M.iselect
- \+ *lemma* pfunctor.M.iselect_cons
- \+ *lemma* pfunctor.M.iselect_eq_default
- \+ *lemma* pfunctor.M.iselect_nil
- \+ *def* pfunctor.M.isubtree
- \+ *lemma* pfunctor.M.isubtree_cons
- \+ *lemma* pfunctor.M.mk_dest
- \+ *lemma* pfunctor.M.mk_inj
- \+ *theorem* pfunctor.M.nth_of_bisim
- \+ *lemma* pfunctor.M.truncate_approx
- \+ *def* pfunctor.M
- \+ *structure* pfunctor.M_intl
- \+ *lemma* pfunctor.approx.P_corec
- \+ *inductive* pfunctor.approx.agree
- \+ *lemma* pfunctor.approx.agree_children
- \+ *lemma* pfunctor.approx.agree_trival
- \+ *def* pfunctor.approx.all_agree
- \+ *lemma* pfunctor.approx.approx_eta
- \+ *def* pfunctor.approx.children'
- \+ *inductive* pfunctor.approx.cofix_a
- \+ *lemma* pfunctor.approx.cofix_a_eq_zero
- \+ *def* pfunctor.approx.head'
- \+ *lemma* pfunctor.approx.head_succ'
- \+ *def* pfunctor.approx.path
- \+ *def* pfunctor.approx.s_corec
- \+ *def* pfunctor.approx.truncate
- \+ *lemma* pfunctor.approx.truncate_eq_of_agree

Added src/data/pfunctor/univariate/basic.lean
- \+ *def* pfunctor.Idx
- \+ *def* pfunctor.W.dest
- \+ *theorem* pfunctor.W.dest_mk
- \+ *def* pfunctor.W.mk
- \+ *theorem* pfunctor.W.mk_dest
- \+ *def* pfunctor.W
- \+ *def* pfunctor.comp.get
- \+ *def* pfunctor.comp.mk
- \+ *def* pfunctor.comp
- \+ *lemma* pfunctor.fst_map
- \+ *lemma* pfunctor.iget_map
- \+ *theorem* pfunctor.liftp_iff
- \+ *theorem* pfunctor.liftr_iff
- \+ *def* pfunctor.map
- \+ *def* pfunctor.obj.iget
- \+ *def* pfunctor.obj
- \+ *structure* pfunctor

Added src/data/pfunctor/univariate/default.lean


Added src/data/qpf/univariate/basic.lean
- \+ *def* qpf.Mcongr
- \+ *def* qpf.W_setoid
- \+ *theorem* qpf.Wequiv.abs'
- \+ *theorem* qpf.Wequiv.refl
- \+ *theorem* qpf.Wequiv.symm
- \+ *inductive* qpf.Wequiv
- \+ *def* qpf.Wrepr
- \+ *theorem* qpf.Wrepr_equiv
- \+ *theorem* qpf.cofix.bisim'
- \+ *theorem* qpf.cofix.bisim
- \+ *theorem* qpf.cofix.bisim_rel
- \+ *def* qpf.cofix.corec
- \+ *def* qpf.cofix.dest
- \+ *theorem* qpf.cofix.dest_corec
- \+ *def* qpf.cofix
- \+ *def* qpf.comp
- \+ *theorem* qpf.comp_map
- \+ *def* qpf.corecF
- \+ *theorem* qpf.corecF_eq
- \+ *def* qpf.fix.dest
- \+ *theorem* qpf.fix.dest_mk
- \+ *theorem* qpf.fix.ind
- \+ *theorem* qpf.fix.ind_aux
- \+ *theorem* qpf.fix.ind_rec
- \+ *def* qpf.fix.mk
- \+ *theorem* qpf.fix.mk_dest
- \+ *def* qpf.fix.rec
- \+ *theorem* qpf.fix.rec_eq
- \+ *theorem* qpf.fix.rec_unique
- \+ *def* qpf.fix
- \+ *def* qpf.fix_to_W
- \+ *theorem* qpf.has_good_supp_iff
- \+ *theorem* qpf.id_map
- \+ *theorem* qpf.is_lawful_functor
- \+ *def* qpf.is_precongr
- \+ *def* qpf.is_uniform
- \+ *theorem* qpf.liftp_iff'
- \+ *theorem* qpf.liftp_iff
- \+ *theorem* qpf.liftp_iff_of_is_uniform
- \+ *theorem* qpf.liftr_iff
- \+ *theorem* qpf.mem_supp
- \+ *def* qpf.quotient_qpf
- \+ *def* qpf.recF
- \+ *theorem* qpf.recF_eq'
- \+ *theorem* qpf.recF_eq
- \+ *theorem* qpf.recF_eq_of_Wequiv
- \+ *theorem* qpf.supp_eq
- \+ *theorem* qpf.supp_eq_of_is_uniform
- \+ *theorem* qpf.supp_map

Modified src/data/quot.lean
- \+ *def* quot.factor
- \+ *lemma* quot.factor_mk_eq

Modified src/data/sigma/basic.lean
- \+ *lemma* ext

Modified src/tactic/ext.lean


Added test/qpf.lean
- \+ *lemma* ex.equivalence_foo.R
- \+ *def* ex.foo.R
- \+ *def* ex.foo.map
- \+ *lemma* ex.foo.map_mk'
- \+ *lemma* ex.foo.map_mk
- \+ *lemma* ex.foo.map_tt
- \+ *def* ex.foo.mk
- \+ *def* ex.foo
- \+ *lemma* ex.foo_not_uniform
- \+ *def* ex.prod.pfunctor
- \+ *lemma* ex.supp_mk_ff'
- \+ *lemma* ex.supp_mk_ff₀
- \+ *lemma* ex.supp_mk_ff₁
- \+ *lemma* ex.supp_mk_tt'
- \+ *lemma* ex.supp_mk_tt
- \+ *def* qpf.box
- \+ *def* qpf.liftp'
- \+ *def* qpf.supp'



## [2020-07-10 12:28:46](https://github.com/leanprover-community/mathlib/commit/d1e63f3)
chore(category_theory/limits): remove an unnecessary import ([#3357](https://github.com/leanprover-community/mathlib/pull/3357))
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean




## [2020-07-10 12:28:40](https://github.com/leanprover-community/mathlib/commit/699c915)
feat(number_theory): pythagorean triples ([#3200](https://github.com/leanprover-community/mathlib/pull/3200))
The classification of pythagorean triples (one of the "100 theorems")
#### Estimated changes
Modified src/algebra/gcd_domain.lean
- \+ *theorem* int.exists_gcd_one'
- \+ *theorem* int.exists_gcd_one
- \+ *theorem* int.gcd_div_gcd_div_gcd
- \+ *theorem* int.ne_zero_of_gcd
- \+ *theorem* int.pow_dvd_pow_iff
- \+ *lemma* int.prime.dvd_mul'
- \+ *lemma* int.prime.dvd_mul
- \+ *lemma* prime_two_or_dvd_of_dvd_two_mul_pow_self_two

Modified src/algebra/group_power.lean
- \+ *lemma* eq_or_eq_neg_of_pow_two_eq_pow_two
- \+ *theorem* pow_dvd_pow_of_dvd
- \+ *theorem* pow_two_pos_of_ne_zero
- \+ *lemma* pow_two_sub_pow_two

Modified src/data/int/basic.lean
- \+ *lemma* int.sub_mod

Modified src/data/int/gcd.lean
- \+ *lemma* int.prime.dvd_nat_abs_of_coe_dvd_pow_two

Modified src/data/nat/prime.lean
- \+ *theorem* nat.prime.not_coprime_iff_dvd

Modified src/data/rat/basic.lean
- \+ *lemma* rat.denom_div_eq_of_coprime
- \+ *lemma* rat.div_int_inj
- \+ *lemma* rat.num_div_eq_of_coprime

Added src/number_theory/pythagorean_triples.lean
- \+ *lemma* circle_equiv_apply
- \+ *def* circle_equiv_gen
- \+ *lemma* circle_equiv_symm_apply
- \+ *theorem* pythagorean_triple.classification
- \+ *theorem* pythagorean_triple.classified
- \+ *theorem* pythagorean_triple.coprime_classification
- \+ *lemma* pythagorean_triple.coprime_of_coprime
- \+ *lemma* pythagorean_triple.eq
- \+ *lemma* pythagorean_triple.even_odd_of_coprime
- \+ *lemma* pythagorean_triple.gcd_dvd
- \+ *def* pythagorean_triple.is_classified
- \+ *lemma* pythagorean_triple.is_classified_of_is_primitive_classified
- \+ *lemma* pythagorean_triple.is_classified_of_normalize_is_primitive_classified
- \+ *def* pythagorean_triple.is_primitive_classified
- \+ *lemma* pythagorean_triple.is_primitive_classified_aux
- \+ *theorem* pythagorean_triple.is_primitive_classified_of_coprime
- \+ *theorem* pythagorean_triple.is_primitive_classified_of_coprime_of_odd_of_pos
- \+ *theorem* pythagorean_triple.is_primitive_classified_of_coprime_of_pos
- \+ *lemma* pythagorean_triple.is_primitive_classified_of_coprime_of_zero_left
- \+ *lemma* pythagorean_triple.mul
- \+ *lemma* pythagorean_triple.mul_iff
- \+ *lemma* pythagorean_triple.mul_is_classified
- \+ *lemma* pythagorean_triple.ne_zero_of_coprime
- \+ *lemma* pythagorean_triple.normalize
- \+ *lemma* pythagorean_triple.symm
- \+ *lemma* pythagorean_triple.zero
- \+ *def* pythagorean_triple
- \+ *lemma* pythagorean_triple_comm



## [2020-07-10 11:15:29](https://github.com/leanprover-community/mathlib/commit/e52108d)
chore(data/int/basic): move content requiring advanced imports ([#3334](https://github.com/leanprover-community/mathlib/pull/3334))
`data.int.basic` had grown to require substantial imports from `algebra.*`. This PR moves out the end of this file into separate files. As a consequence it's then possible to separate out `data.multiset.basic` into some further pieces.
#### Estimated changes
Modified src/algebra/euclidean_domain.lean


Modified src/algebra/group_power.lean


Modified src/data/fintype/basic.lean


Modified src/data/hash_map.lean


Modified src/data/int/basic.lean
- \- *theorem* add_monoid_hom.eq_int_cast
- \- *theorem* add_monoid_hom.eq_int_cast_hom
- \- *theorem* add_monoid_hom.ext_int
- \- *theorem* int.cast_abs
- \- *theorem* int.cast_add
- \- *def* int.cast_add_hom
- \- *theorem* int.cast_bit0
- \- *theorem* int.cast_bit1
- \- *theorem* int.cast_coe_nat'
- \- *theorem* int.cast_coe_nat
- \- *lemma* int.cast_commute
- \- *theorem* int.cast_eq_zero
- \- *theorem* int.cast_id
- \- *theorem* int.cast_inj
- \- *theorem* int.cast_injective
- \- *theorem* int.cast_le
- \- *theorem* int.cast_lt
- \- *theorem* int.cast_lt_zero
- \- *theorem* int.cast_max
- \- *theorem* int.cast_min
- \- *theorem* int.cast_mul
- \- *theorem* int.cast_ne_zero
- \- *theorem* int.cast_neg
- \- *theorem* int.cast_neg_of_nat
- \- *theorem* int.cast_neg_succ_of_nat
- \- *theorem* int.cast_nonneg
- \- *theorem* int.cast_nonpos
- \- *theorem* int.cast_of_nat
- \- *theorem* int.cast_one
- \- *theorem* int.cast_pos
- \- *def* int.cast_ring_hom
- \- *theorem* int.cast_sub
- \- *theorem* int.cast_sub_nat_nat
- \- *lemma* int.cast_two
- \- *theorem* int.cast_zero
- \- *lemma* int.coe_cast_add_hom
- \- *lemma* int.coe_cast_ring_hom
- \- *theorem* int.coe_nat_bit0
- \- *theorem* int.coe_nat_bit1
- \- *lemma* int.commute_cast
- \- *theorem* int.mem_range_iff
- \- *theorem* int.nat_cast_eq_coe_nat
- \- *def* int.of_nat_hom
- \- *def* int.range
- \- *lemma* ring_hom.eq_int_cast'
- \- *lemma* ring_hom.eq_int_cast
- \- *lemma* ring_hom.ext_int
- \- *lemma* ring_hom.map_int_cast

Added src/data/int/cast.lean
- \+ *theorem* add_monoid_hom.eq_int_cast
- \+ *theorem* add_monoid_hom.eq_int_cast_hom
- \+ *theorem* add_monoid_hom.ext_int
- \+ *theorem* int.cast_abs
- \+ *theorem* int.cast_add
- \+ *def* int.cast_add_hom
- \+ *theorem* int.cast_bit0
- \+ *theorem* int.cast_bit1
- \+ *theorem* int.cast_coe_nat'
- \+ *theorem* int.cast_coe_nat
- \+ *lemma* int.cast_commute
- \+ *theorem* int.cast_id
- \+ *theorem* int.cast_le
- \+ *theorem* int.cast_lt
- \+ *theorem* int.cast_lt_zero
- \+ *theorem* int.cast_max
- \+ *theorem* int.cast_min
- \+ *theorem* int.cast_mul
- \+ *theorem* int.cast_neg
- \+ *theorem* int.cast_neg_of_nat
- \+ *theorem* int.cast_neg_succ_of_nat
- \+ *theorem* int.cast_nonneg
- \+ *theorem* int.cast_nonpos
- \+ *theorem* int.cast_of_nat
- \+ *theorem* int.cast_one
- \+ *theorem* int.cast_pos
- \+ *def* int.cast_ring_hom
- \+ *theorem* int.cast_sub
- \+ *theorem* int.cast_sub_nat_nat
- \+ *lemma* int.cast_two
- \+ *theorem* int.cast_zero
- \+ *lemma* int.coe_cast_add_hom
- \+ *lemma* int.coe_cast_ring_hom
- \+ *theorem* int.coe_nat_bit0
- \+ *theorem* int.coe_nat_bit1
- \+ *lemma* int.commute_cast
- \+ *theorem* int.nat_cast_eq_coe_nat
- \+ *def* int.of_nat_hom
- \+ *lemma* ring_hom.eq_int_cast'
- \+ *lemma* ring_hom.eq_int_cast
- \+ *lemma* ring_hom.ext_int
- \+ *lemma* ring_hom.map_int_cast

Added src/data/int/char_zero.lean
- \+ *theorem* int.cast_eq_zero
- \+ *theorem* int.cast_inj
- \+ *theorem* int.cast_injective
- \+ *theorem* int.cast_ne_zero

Added src/data/int/range.lean
- \+ *theorem* int.mem_range_iff
- \+ *def* int.range

Modified src/data/list/basic.lean


Modified src/data/multiset/basic.lean
- \- *theorem* multiset.card_range
- \- *theorem* multiset.mem_range
- \- *theorem* multiset.not_mem_range_self
- \- *def* multiset.range
- \- *theorem* multiset.range_subset
- \- *theorem* multiset.range_succ
- \- *theorem* multiset.range_zero
- \- *theorem* multiset.self_mem_range_succ

Modified src/data/multiset/nodup.lean


Added src/data/multiset/range.lean
- \+ *theorem* multiset.card_range
- \+ *theorem* multiset.mem_range
- \+ *theorem* multiset.not_mem_range_self
- \+ *def* multiset.range
- \+ *theorem* multiset.range_subset
- \+ *theorem* multiset.range_succ
- \+ *theorem* multiset.range_zero
- \+ *theorem* multiset.self_mem_range_succ

Modified src/data/nat/prime.lean


Modified src/data/num/lemmas.lean


Modified src/data/rat/basic.lean
- \+/\- *lemma* rat.coe_int_inj

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
- \+/\- *lemma* compact_covered_by_mul_left_translates
- \+/\- *lemma* compact_open_separated_mul

Modified src/topology/algebra/ordered.lean
- \- *lemma* compact.Inf_mem
- \- *lemma* compact.Sup_mem
- \- *lemma* compact.bdd_above
- \- *lemma* compact.bdd_below
- \- *lemma* compact.exists_Inf_image_eq
- \- *lemma* compact.exists_Sup_image_eq
- \- *lemma* compact.exists_forall_ge
- \- *lemma* compact.exists_forall_le
- \- *lemma* compact.exists_is_glb
- \- *lemma* compact.exists_is_greatest
- \- *lemma* compact.exists_is_least
- \- *lemma* compact.exists_is_lub
- \- *lemma* compact.is_glb_Inf
- \- *lemma* compact.is_greatest_Sup
- \- *lemma* compact.is_least_Inf
- \- *lemma* compact.is_lub_Sup
- \+/\- *lemma* eq_Icc_of_connected_compact
- \+ *lemma* is_compact.Inf_mem
- \+ *lemma* is_compact.Sup_mem
- \+ *lemma* is_compact.bdd_above
- \+ *lemma* is_compact.bdd_below
- \+ *lemma* is_compact.exists_Inf_image_eq
- \+ *lemma* is_compact.exists_Sup_image_eq
- \+ *lemma* is_compact.exists_forall_ge
- \+ *lemma* is_compact.exists_forall_le
- \+ *lemma* is_compact.exists_is_glb
- \+ *lemma* is_compact.exists_is_greatest
- \+ *lemma* is_compact.exists_is_least
- \+ *lemma* is_compact.exists_is_lub
- \+ *lemma* is_compact.is_glb_Inf
- \+ *lemma* is_compact.is_greatest_Sup
- \+ *lemma* is_compact.is_least_Inf
- \+ *lemma* is_compact.is_lub_Sup

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/compact_open.lean


Modified src/topology/compacts.lean
- \+/\- *def* topological_space.compacts
- \+/\- *def* topological_space.nonempty_compacts
- \+/\- *def* topological_space.positive_compacts:

Modified src/topology/homeomorph.lean
- \+/\- *lemma* homeomorph.compact_image
- \+/\- *lemma* homeomorph.compact_preimage

Modified src/topology/instances/real.lean
- \+/\- *lemma* compact_Icc

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* metric.bounded_of_compact

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *lemma* emetric.countable_closure_of_compact

Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/separation.lean
- \- *lemma* compact.binary_compact_cover
- \- *lemma* compact.finite_compact_cover
- \- *lemma* compact.inter
- \- *lemma* compact.is_closed
- \+ *lemma* is_compact.binary_compact_cover
- \+ *lemma* is_compact.finite_compact_cover
- \+ *lemma* is_compact.inter
- \+ *lemma* is_compact.is_closed
- \+/\- *lemma* locally_compact_of_compact_nhds

Modified src/topology/sequences.lean
- \- *lemma* compact.seq_compact
- \- *lemma* compact.tendsto_subseq'
- \- *lemma* compact.tendsto_subseq
- \+ *lemma* is_compact.is_seq_compact
- \+ *lemma* is_compact.tendsto_subseq'
- \+ *lemma* is_compact.tendsto_subseq
- \+ *lemma* is_seq_compact.subseq_of_frequently_in
- \+ *lemma* is_seq_compact.totally_bounded
- \+ *def* is_seq_compact
- \+/\- *lemma* metric.compact_iff_seq_compact
- \- *lemma* seq_compact.subseq_of_frequently_in
- \- *lemma* seq_compact.totally_bounded
- \- *def* seq_compact

Modified src/topology/subset_properties.lean
- \- *lemma* compact.adherence_nhdset
- \- *lemma* compact.elim_finite_subcover
- \- *lemma* compact.elim_finite_subcover_image
- \- *lemma* compact.elim_finite_subfamily_closed
- \- *lemma* compact.image
- \- *lemma* compact.image_of_continuous_on
- \- *lemma* compact.inter_left
- \- *lemma* compact.inter_right
- \- *lemma* compact.nonempty_Inter_of_directed_nonempty_compact_closed
- \- *lemma* compact.nonempty_Inter_of_sequence_nonempty_compact_closed
- \- *lemma* compact.prod
- \- *lemma* compact.union
- \- *def* compact
- \+/\- *lemma* compact_diff
- \+/\- *lemma* compact_empty
- \+/\- *lemma* compact_iff_compact_space
- \+/\- *lemma* compact_iff_compact_univ
- \+/\- *lemma* compact_singleton
- \+/\- *lemma* compact_univ
- \+/\- *lemma* compact_univ_pi
- \+/\- *lemma* generalized_tube_lemma
- \+ *lemma* is_compact.adherence_nhdset
- \+ *lemma* is_compact.elim_finite_subcover
- \+ *lemma* is_compact.elim_finite_subcover_image
- \+ *lemma* is_compact.elim_finite_subfamily_closed
- \+ *lemma* is_compact.image
- \+ *lemma* is_compact.image_of_continuous_on
- \+ *lemma* is_compact.inter_left
- \+ *lemma* is_compact.inter_right
- \+ *lemma* is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
- \+ *lemma* is_compact.nonempty_Inter_of_sequence_nonempty_compact_closed
- \+ *lemma* is_compact.prod
- \+ *lemma* is_compact.union
- \+ *def* is_compact
- \+/\- *lemma* nhds_contain_boxes_of_compact
- \- *lemma* set.finite.compact
- \+ *lemma* set.finite.is_compact

Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/compact_separated.lean
- \- *lemma* compact.uniform_continuous_on_of_continuous'
- \- *lemma* compact.uniform_continuous_on_of_continuous
- \+ *lemma* is_compact.uniform_continuous_on_of_continuous'
- \+ *lemma* is_compact.uniform_continuous_on_of_continuous



## [2020-07-10 07:09:28](https://github.com/leanprover-community/mathlib/commit/79bb8b7)
feat(linear_algebra/cayley_hamilton): the Cayley-Hamilton theorem ([#3276](https://github.com/leanprover-community/mathlib/pull/3276))
The Cayley-Hamilton theorem, following the proof at http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf.
#### Estimated changes
Added src/linear_algebra/char_poly.lean
- \+ *def* char_matrix
- \+ *lemma* char_matrix_apply_eq
- \+ *lemma* char_matrix_apply_ne
- \+ *def* char_poly
- \+ *theorem* char_poly_map_eval_self
- \+ *lemma* mat_poly_equiv_char_matrix

Modified src/ring_theory/polynomial_algebra.lean




## [2020-07-10 06:31:16](https://github.com/leanprover-community/mathlib/commit/66db1ad)
refactor(algebra/homology): handle co/homology uniformly ([#3316](https://github.com/leanprover-community/mathlib/pull/3316))
A refactor of `algebra/homology` so homology and cohomology are handled uniformly, and factor out a file `image_to_kernel_map.lean` which gains some extra lemmas (which will be useful for talking about exact sequences).
#### Estimated changes
Modified src/algebra/homology/chain_complex.lean
- \- *lemma* chain_complex.comm
- \- *lemma* chain_complex.comm_at
- \- *lemma* chain_complex.d_squared
- \- *abbreviation* chain_complex.forget
- \- *lemma* cochain_complex.comm
- \- *lemma* cochain_complex.comm_at
- \- *lemma* cochain_complex.d_squared
- \- *abbreviation* cochain_complex.forget
- \+ *lemma* homological_complex.comm
- \+ *lemma* homological_complex.comm_at
- \+ *lemma* homological_complex.d_squared
- \+ *abbreviation* homological_complex.forget
- \+ *abbreviation* homological_complex

Modified src/algebra/homology/homology.lean
- \+ *abbreviation* cochain_complex.cohomology
- \- *def* cochain_complex.cohomology
- \- *def* cochain_complex.cohomology_functor
- \+ *abbreviation* cochain_complex.cohomology_group
- \+ *abbreviation* cochain_complex.cohomology_map
- \- *def* cochain_complex.cohomology_map
- \- *lemma* cochain_complex.cohomology_map_comp
- \- *lemma* cochain_complex.cohomology_map_condition
- \- *lemma* cochain_complex.cohomology_map_id
- \+ *abbreviation* cochain_complex.graded_cohomology
- \- *abbreviation* cochain_complex.image_map
- \- *lemma* cochain_complex.image_map_ι
- \- *def* cochain_complex.image_to_kernel_map
- \- *lemma* cochain_complex.image_to_kernel_map_condition
- \- *lemma* cochain_complex.induced_maps_commute
- \- *def* cochain_complex.kernel_functor
- \- *def* cochain_complex.kernel_map
- \- *lemma* cochain_complex.kernel_map_comp
- \- *lemma* cochain_complex.kernel_map_condition
- \- *lemma* cochain_complex.kernel_map_id
- \+ *def* homological_complex.graded_homology
- \+ *def* homological_complex.homology
- \+ *def* homological_complex.homology_group
- \+ *def* homological_complex.homology_map
- \+ *lemma* homological_complex.homology_map_comp
- \+ *lemma* homological_complex.homology_map_condition
- \+ *lemma* homological_complex.homology_map_id
- \+ *abbreviation* homological_complex.image_map
- \+ *lemma* homological_complex.image_map_ι
- \+ *def* homological_complex.image_to_kernel_map
- \+ *lemma* homological_complex.image_to_kernel_map_comp_kernel_map
- \+ *lemma* homological_complex.image_to_kernel_map_condition
- \+ *def* homological_complex.kernel_functor
- \+ *def* homological_complex.kernel_map
- \+ *lemma* homological_complex.kernel_map_comp
- \+ *lemma* homological_complex.kernel_map_condition
- \+ *lemma* homological_complex.kernel_map_id

Added src/algebra/homology/image_to_kernel_map.lean
- \+ *def* category_theory.image_to_kernel_map
- \+ *lemma* category_theory.image_to_kernel_map_epi_of_epi_of_zero
- \+ *lemma* category_theory.image_to_kernel_map_epi_of_zero_of_mono
- \+ *lemma* category_theory.image_to_kernel_map_zero_left
- \+ *lemma* category_theory.image_to_kernel_map_zero_right

Modified src/category_theory/limits/shapes/kernels.lean




## [2020-07-10 05:40:16](https://github.com/leanprover-community/mathlib/commit/bcf733f)
feat(data/matrix): add matrix.map and supporting lemmas ([#3352](https://github.com/leanprover-community/mathlib/pull/3352))
As [requested](https://github.com/leanprover-community/mathlib/pull/3276/files#r452366674).
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *def* add_monoid_hom.map_matrix
- \+ *lemma* add_monoid_hom.map_matrix_apply
- \+ *lemma* matrix.diagonal_map
- \- *lemma* matrix.elementary_eq_basis_mul_basis
- \+ *def* matrix.map
- \+ *lemma* matrix.map_add
- \+ *lemma* matrix.map_apply
- \+ *lemma* matrix.map_mul
- \+ *lemma* matrix.map_zero
- \- *lemma* matrix.matrix_eq_sum_elementary
- \+ *lemma* matrix.matrix_eq_sum_std_basis
- \+ *lemma* matrix.one_map
- \+ *lemma* matrix.std_basis_eq_basis_mul_basis
- \+ *lemma* matrix.transpose_map
- \+/\- *lemma* matrix.transpose_mul
- \+/\- *lemma* matrix.transpose_neg
- \+/\- *lemma* matrix.transpose_smul
- \+/\- *lemma* matrix.transpose_sub
- \+ *def* ring_hom.map_matrix
- \+ *lemma* ring_hom.map_matrix_apply

Modified src/ring_theory/matrix_algebra.lean
- \- *lemma* matrix_equiv_tensor_apply_elementary
- \+ *lemma* matrix_equiv_tensor_apply_std_basis

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
- \- *lemma* function.injective.prod
- \+ *lemma* function.injective.prod_map
- \+ *lemma* function.surjective.prod_map

Modified src/data/sigma/basic.lean
- \+ *lemma* function.injective.sigma_map
- \+ *lemma* function.surjective.sigma_map
- \+/\- *def* sigma.map
- \- *lemma* sigma_map_injective

Modified src/data/sum.lean
- \+ *lemma* function.injective.sum_map
- \+ *lemma* function.surjective.sum_map

Modified src/logic/embedding.lean
- \+ *lemma* function.embedding.coe_prod_map
- \+ *lemma* function.embedding.coe_sigma_map
- \+ *theorem* function.embedding.coe_sum_map
- \- *def* function.embedding.prod_congr
- \+ *def* function.embedding.prod_map
- \- *def* function.embedding.sigma_congr_right
- \+ *def* function.embedding.sigma_map
- \- *def* function.embedding.sum_congr
- \- *theorem* function.embedding.sum_congr_apply_inl
- \- *theorem* function.embedding.sum_congr_apply_inr
- \+ *def* function.embedding.sum_map

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
- \+ *theorem* set.bInter_mono'
- \+ *theorem* set.bInter_mono

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.comap_mono
- \+/\- *lemma* filter.map_mono
- \+/\- *lemma* filter.monotone_principal
- \+/\- *lemma* filter.prod_mono
- \+/\- *lemma* filter.seq_mono

Modified src/tactic/monotonicity/lemmas.lean




## [2020-07-09 21:17:53](https://github.com/leanprover-community/mathlib/commit/d6e9f97)
feat(topology/basic): yet another mem_closure ([#3348](https://github.com/leanprover-community/mathlib/pull/3348))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.comap_ne_bot
- \+ *lemma* filter.comap_ne_bot_iff

Modified src/topology/basic.lean
- \+ *theorem* mem_closure_iff_comap_ne_bot



## [2020-07-09 21:17:51](https://github.com/leanprover-community/mathlib/commit/ac62213)
chore(order/filter/at_top_bot): in `order_top` `at_top = pure ⊤` ([#3346](https://github.com/leanprover-community/mathlib/pull/3346))
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.order_top.at_top_eq
- \+ *lemma* filter.tendsto_at_top_pure

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
- \+/\- *lemma* set.indicator_le_indicator
- \+ *lemma* set.indicator_range_comp

Modified src/data/set/function.lean
- \+ *lemma* set.comp_eq_of_eq_on_range
- \+ *lemma* set.piecewise_compl
- \+ *lemma* set.piecewise_eq_on
- \+ *lemma* set.piecewise_eq_on_compl
- \+ *lemma* set.piecewise_range_comp



## [2020-07-09 16:34:14](https://github.com/leanprover-community/mathlib/commit/d6ecb44)
feat(topology/basic): closure in term of subtypes ([#3339](https://github.com/leanprover-community/mathlib/pull/3339))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.nonempty_inter_iff_exists_left
- \+ *lemma* set.nonempty_inter_iff_exists_right

Modified src/topology/basic.lean
- \+ *theorem* mem_closure_iff_nhds'



## [2020-07-09 15:24:02](https://github.com/leanprover-community/mathlib/commit/593a4c8)
fix(tactic/norm_cast): remove bad norm_cast lemma ([#3340](https://github.com/leanprover-community/mathlib/pull/3340))
This was identified as a move_cast lemma, which meant it was rewriting to the LHS which it couldn't reduce. It's better to let the conditional rewriting handle nat subtraction -- if the right inequality is in the context there's no need to go to `int.sub_nat_nat`.
#### Estimated changes
Modified src/data/int/basic.lean
- \+/\- *theorem* int.cast_sub_nat_nat

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
- \+/\- *def* int.sqrt

Modified src/data/nat/sqrt.lean
- \+/\- *def* nat.sqrt

Modified src/data/rat/order.lean
- \+/\- *def* rat.sqrt

Modified src/data/real/basic.lean




## [2020-07-09 05:00:10-07:00](https://github.com/leanprover-community/mathlib/commit/e4ecf14)
I'm just another maintainer
#### Estimated changes
Modified README.md




## [2020-07-09 10:43:05](https://github.com/leanprover-community/mathlib/commit/be2e42f)
chore(ring_theory/algebraic): speedup slow proof ([#3336](https://github.com/leanprover-community/mathlib/pull/3336))
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+ *lemma* subalgebra.val_apply

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
- \- *def* tidy.test.tidy_test_0



## [2020-07-09 03:35:05](https://github.com/leanprover-community/mathlib/commit/95cc1b1)
refactor(topology/dense_embedding): simplify proof ([#3329](https://github.com/leanprover-community/mathlib/pull/3329))
Using filter bases, we can give a cleaner proof of continuity of extension by continuity. Also switch to use the "new" `continuous_at` in the statement.
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* nhds_basis_opens'

Modified src/topology/dense_embedding.lean
- \+ *lemma* dense_inducing.continuous_at_extend
- \- *lemma* dense_inducing.tendsto_extend

Modified src/topology/separation.lean
- \+ *lemma* closed_nhds_basis



## [2020-07-09 03:35:03](https://github.com/leanprover-community/mathlib/commit/d5cfa87)
fix(tactic/lint/type_classes): add missing unfreeze_local_instances ([#3328](https://github.com/leanprover-community/mathlib/pull/3328))
#### Estimated changes
Modified src/tactic/cache.lean


Modified src/tactic/lint/simp.lean


Modified src/tactic/lint/type_classes.lean


Modified test/lint_coe_to_fun.lean
- \+ *structure* with_tc_param.equiv
- \+ *structure* with_tc_param.sparkling_equiv



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
- \+ *def* finset.fin_range
- \+ *lemma* finset.fin_range_card
- \+ *lemma* finset.mem_fin_range

Modified src/data/finset/sort.lean
- \+ *lemma* finset.mono_of_fin_unique'

Modified src/data/fintype/basic.lean
- \- *lemma* finset.mono_of_fin_unique'

Added src/data/fintype/sort.lean


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


Modified src/data/polynomial.lean
- \+ *theorem* polynomial.aeval_alg_hom
- \+ *theorem* polynomial.aeval_alg_hom_apply
- \+/\- *lemma* polynomial.dvd_term_of_dvd_eval_of_dvd_terms
- \+/\- *lemma* polynomial.dvd_term_of_is_root_of_dvd_terms

Modified src/field_theory/splitting_field.lean


Modified src/linear_algebra/tensor_product.lean
- \+/\- *theorem* linear_map.map_neg₂
- \+/\- *def* tensor_product.map
- \+/\- *def* tensor_product.mk

Modified src/ring_theory/adjoin.lean
- \+ *theorem* algebra.adjoin_eq_ring_closure
- \+/\- *theorem* algebra.adjoin_int
- \+/\- *theorem* algebra.adjoin_singleton_eq_range
- \+ *theorem* algebra.mem_adjoin_iff

Modified src/ring_theory/algebra.lean
- \+ *def* alg_hom_nat
- \+ *lemma* mem_subalgebra_of_subsemiring
- \+ *lemma* span_nat_eq
- \+ *lemma* span_nat_eq_add_group_closure
- \+ *theorem* subalgebra.add_mem
- \+ *theorem* subalgebra.algebra_map_mem
- \+ *theorem* subalgebra.coe_int_mem
- \+ *theorem* subalgebra.coe_nat_mem
- \+ *theorem* subalgebra.gsmul_mem
- \+ *theorem* subalgebra.list_prod_mem
- \+ *theorem* subalgebra.list_sum_mem
- \+ *lemma* subalgebra.mem_to_submodule
- \+ *theorem* subalgebra.mul_mem
- \- *lemma* subalgebra.mul_mem
- \+ *theorem* subalgebra.multiset_prod_mem
- \+ *theorem* subalgebra.multiset_sum_mem
- \+ *theorem* subalgebra.neg_mem
- \+ *theorem* subalgebra.nsmul_mem
- \+ *theorem* subalgebra.one_mem
- \+ *theorem* subalgebra.pow_mem
- \+ *theorem* subalgebra.prod_mem
- \+ *theorem* subalgebra.range_le
- \- *lemma* subalgebra.range_le
- \+ *theorem* subalgebra.range_subset
- \+ *theorem* subalgebra.smul_mem
- \+ *theorem* subalgebra.srange_le
- \+ *theorem* subalgebra.sub_mem
- \+ *theorem* subalgebra.sum_mem
- \+ *theorem* subalgebra.to_submodule_inj
- \+ *theorem* subalgebra.to_submodule_injective
- \+/\- *def* subalgebra.under
- \+ *theorem* subalgebra.zero_mem
- \+ *def* subalgebra_of_subsemiring

Modified src/ring_theory/algebra_operations.lean
- \+/\- *lemma* submodule.map_mul

Modified src/ring_theory/algebra_tower.lean
- \+ *theorem* is_algebra_tower.aeval_apply
- \+ *def* is_algebra_tower.restrict_base
- \+ *lemma* is_algebra_tower.restrict_base_apply
- \+ *lemma* is_algebra_tower.to_alg_hom_apply

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \+ *theorem* is_integral_alg_hom
- \+/\- *lemma* is_integral_trans_aux

Modified src/ring_theory/localization.lean
- \+/\- *lemma* fraction_map.comap_is_algebraic_iff
- \+/\- *def* integral_closure.fraction_map_of_finite_extension
- \+ *lemma* localization_map.algebra_map_eq
- \+/\- *lemma* localization_map.integer_normalization_aeval_eq_zero

Modified src/ring_theory/subsemiring.lean
- \+/\- *theorem* subsemiring.ext
- \+ *lemma* subsemiring.mem_closure_iff
- \+ *lemma* subsemiring.mem_closure_iff_exists_list



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
- \+/\- *def* add_monoid_algebra.algebra_map'
- \+/\- *def* monoid_algebra.algebra_map'

Modified src/data/polynomial.lean
- \+/\- *def* polynomial.C
- \+ *lemma* polynomial.algebra_map_apply

Added src/ring_theory/polynomial_algebra.lean
- \+ *lemma* mat_poly_equiv_coeff_apply
- \+ *lemma* mat_poly_equiv_coeff_apply_aux_1
- \+ *lemma* mat_poly_equiv_coeff_apply_aux_2
- \+ *lemma* mat_poly_equiv_smul_one
- \+ *lemma* mat_poly_equiv_symm_apply_coeff
- \+ *def* poly_equiv_tensor.equiv
- \+ *def* poly_equiv_tensor.inv_fun
- \+ *lemma* poly_equiv_tensor.inv_fun_add
- \+ *lemma* poly_equiv_tensor.left_inv
- \+ *lemma* poly_equiv_tensor.right_inv
- \+ *def* poly_equiv_tensor.to_fun
- \+ *def* poly_equiv_tensor.to_fun_alg_hom
- \+ *lemma* poly_equiv_tensor.to_fun_alg_hom_apply_tmul
- \+ *def* poly_equiv_tensor.to_fun_bilinear
- \+ *def* poly_equiv_tensor.to_fun_linear
- \+ *lemma* poly_equiv_tensor.to_fun_linear_algebra_map_tmul_one
- \+ *lemma* poly_equiv_tensor.to_fun_linear_mul_tmul_mul
- \+ *lemma* poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_1
- \+ *lemma* poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_2
- \+ *def* poly_equiv_tensor.to_fun_linear_right
- \+ *def* poly_equiv_tensor
- \+ *lemma* poly_equiv_tensor_apply
- \+ *lemma* poly_equiv_tensor_symm_apply_tmul

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
- \+ *lemma* category_theory.limits.cokernel.desc_zero
- \- *def* category_theory.limits.cokernel.π_zero_is_iso
- \+ *lemma* category_theory.limits.kernel.lift_zero
- \- *def* category_theory.limits.kernel.ι_zero_is_iso

Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* category_theory.limits.epi_of_target_iso_zero
- \+ *def* category_theory.limits.has_image.zero
- \- *lemma* category_theory.limits.has_zero_object.zero_of_from_zero
- \- *lemma* category_theory.limits.has_zero_object.zero_of_to_zero
- \+ *lemma* category_theory.limits.id_zero
- \+ *def* category_theory.limits.id_zero_equiv_iso_zero
- \+ *lemma* category_theory.limits.id_zero_equiv_iso_zero_apply_hom
- \+ *lemma* category_theory.limits.id_zero_equiv_iso_zero_apply_inv
- \+ *lemma* category_theory.limits.image.ι_zero'
- \+ *lemma* category_theory.limits.image.ι_zero
- \+ *def* category_theory.limits.image_zero'
- \+ *def* category_theory.limits.image_zero
- \+ *def* category_theory.limits.is_iso_zero_equiv
- \+ *def* category_theory.limits.is_iso_zero_equiv_iso_zero
- \+ *def* category_theory.limits.is_iso_zero_self_equiv
- \+ *def* category_theory.limits.is_iso_zero_self_equiv_iso_zero
- \+ *def* category_theory.limits.mono_factorisation_zero
- \+ *lemma* category_theory.limits.mono_of_source_iso_zero
- \+ *lemma* category_theory.limits.zero_of_from_zero
- \+ *lemma* category_theory.limits.zero_of_source_iso_zero
- \+ *lemma* category_theory.limits.zero_of_target_iso_zero
- \+ *lemma* category_theory.limits.zero_of_to_zero



## [2020-07-08 10:26:50](https://github.com/leanprover-community/mathlib/commit/fbb49cb)
refactor(*): place map_map in the functor namespace ([#3309](https://github.com/leanprover-community/mathlib/pull/3309))
Renames `_root_.map_map` to `functor.map_map` and `filter.comap_comap_comp` to `filter.comap_comap` (which is consistent with `filter.map_map`).
#### Estimated changes
Modified src/control/basic.lean
- \+ *theorem* functor.map_map

Modified src/order/filter/basic.lean
- \+ *lemma* filter.comap_comap
- \- *lemma* filter.comap_comap_comp

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
- \- *lemma* category_theory.limits.braid_natural
- \- *def* category_theory.limits.coprod.associator
- \- *lemma* category_theory.limits.coprod.associator_naturality
- \- *def* category_theory.limits.coprod.braiding
- \- *def* category_theory.limits.coprod.left_unitor
- \- *lemma* category_theory.limits.coprod.pentagon
- \- *def* category_theory.limits.coprod.right_unitor
- \- *lemma* category_theory.limits.coprod.symmetry'
- \- *lemma* category_theory.limits.coprod.symmetry
- \- *lemma* category_theory.limits.coprod.triangle
- \- *def* category_theory.limits.prod.associator
- \- *lemma* category_theory.limits.prod.associator_naturality
- \- *def* category_theory.limits.prod.braiding
- \- *def* category_theory.limits.prod.left_unitor
- \- *lemma* category_theory.limits.prod.pentagon
- \- *def* category_theory.limits.prod.right_unitor
- \- *lemma* category_theory.limits.prod.symmetry'
- \- *lemma* category_theory.limits.prod.symmetry
- \- *lemma* category_theory.limits.prod.triangle
- \- *def* category_theory.limits.prod_functor_left_comp
- \- *lemma* category_theory.limits.prod_left_unitor_hom_naturality
- \- *lemma* category_theory.limits.prod_left_unitor_inv_naturality
- \- *lemma* category_theory.limits.prod_right_unitor_hom_naturality
- \- *lemma* category_theory.limits.prod_right_unitor_inv_naturality

Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/constructions/binary_products.lean


Modified src/category_theory/limits/shapes/default.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \- *def* category_theory.limits.has_coequalizers_of_has_finite_colimits
- \- *def* category_theory.limits.has_equalizers_of_has_finite_limits

Modified src/category_theory/limits/shapes/finite_limits.lean
- \+ *def* category_theory.limits.has_coequalizers_of_has_finite_colimits
- \+ *def* category_theory.limits.has_equalizers_of_has_finite_limits
- \+ *def* category_theory.limits.has_finite_wide_pullbacks_of_has_finite_limits
- \+ *def* category_theory.limits.has_finite_wide_pushouts_of_has_finite_limits
- \+ *def* category_theory.limits.has_pullbacks_of_has_finite_limits
- \+ *def* category_theory.limits.has_pushouts_of_has_finite_colimits

Modified src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/kernels.lean
- \- *def* category_theory.limits.has_cokernels_of_has_finite_colimits
- \- *def* category_theory.limits.has_kernels_of_has_finite_limits

Modified src/category_theory/limits/shapes/pullbacks.lean
- \- *def* category_theory.limits.has_pullbacks_of_has_finite_limits
- \- *def* category_theory.limits.has_pushouts_of_has_finite_colimits

Modified src/category_theory/limits/shapes/terminal.lean


Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \- *def* has_finite_wide_pullbacks_of_has_finite_limits
- \- *def* has_finite_wide_pushouts_of_has_finite_limits

Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/monoidal/of_has_finite_products.lean
- \+ *lemma* category_theory.limits.braid_natural
- \+ *def* category_theory.limits.coprod.associator
- \+ *lemma* category_theory.limits.coprod.associator_naturality
- \+ *def* category_theory.limits.coprod.braiding
- \+ *def* category_theory.limits.coprod.left_unitor
- \+ *lemma* category_theory.limits.coprod.pentagon
- \+ *def* category_theory.limits.coprod.right_unitor
- \+ *lemma* category_theory.limits.coprod.symmetry'
- \+ *lemma* category_theory.limits.coprod.symmetry
- \+ *lemma* category_theory.limits.coprod.triangle
- \+ *def* category_theory.limits.prod.associator
- \+ *lemma* category_theory.limits.prod.associator_naturality
- \+ *def* category_theory.limits.prod.braiding
- \+ *def* category_theory.limits.prod.left_unitor
- \+ *lemma* category_theory.limits.prod.pentagon
- \+ *def* category_theory.limits.prod.right_unitor
- \+ *lemma* category_theory.limits.prod.symmetry'
- \+ *lemma* category_theory.limits.prod.symmetry
- \+ *lemma* category_theory.limits.prod.triangle
- \+ *def* category_theory.limits.prod_functor_left_comp
- \+ *lemma* category_theory.limits.prod_left_unitor_hom_naturality
- \+ *lemma* category_theory.limits.prod_left_unitor_inv_naturality
- \+ *lemma* category_theory.limits.prod_right_unitor_hom_naturality
- \+ *lemma* category_theory.limits.prod_right_unitor_inv_naturality

Modified src/category_theory/monoidal/types.lean


Modified src/category_theory/punit.lean




## [2020-07-08 07:12:45](https://github.com/leanprover-community/mathlib/commit/13eea4c)
chore(category_theory/images): cleanup ([#3314](https://github.com/leanprover-community/mathlib/pull/3314))
Just some cleanup, and adding two easy lemmas.
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* category_theory.limits.epi_image_of_epi
- \+ *lemma* category_theory.limits.image.eq_fac
- \+ *lemma* category_theory.limits.image.ext



## [2020-07-08 07:12:43](https://github.com/leanprover-community/mathlib/commit/eb271b2)
feat(data/int/basic): some lemmas ([#3313](https://github.com/leanprover-community/mathlib/pull/3313))
A few small lemmas about `to_nat` that I wanted while playing with exact sequences.
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.le_add_one
- \+ *lemma* int.to_nat_add
- \+ *lemma* int.to_nat_add_one
- \+ *lemma* int.to_nat_coe_nat_add_one
- \+ *lemma* int.to_nat_one
- \+ *lemma* int.to_nat_zero



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
- \+ *theorem* metric.closed_ball_mem_nhds



## [2020-07-07 17:45:54](https://github.com/leanprover-community/mathlib/commit/35940dd)
feat(linear_algebra/finite_dimensional): add dim_sup_add_dim_inf_eq ([#3304](https://github.com/leanprover-community/mathlib/pull/3304))
Adding a finite-dimensional version of dim(W+X)+dim(W \cap X)=dim(W)+dim(X)
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+ *theorem* submodule.dim_sup_add_dim_inf_eq



## [2020-07-07 16:39:23](https://github.com/leanprover-community/mathlib/commit/ea10944)
feat(data/list/defs): list.singleton_append and list.bind_singleton ([#3298](https://github.com/leanprover-community/mathlib/pull/3298))
I found these useful when working with palindromes and Fibonacci words respectively.
While `bind_singleton` is available as a monad law, I find the specialized version more convenient.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.bind_singleton
- \+ *lemma* list.singleton_append



## [2020-07-07 15:15:11](https://github.com/leanprover-community/mathlib/commit/11ba687)
chore(algebra/big_operators): use proper `*_with_zero` class in `prod_eq_zero(_iff)` ([#3303](https://github.com/leanprover-community/mathlib/pull/3303))
Also add a missing instance `comm_semiring → comm_monoid_with_zero`.
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/algebra/ring.lean


Modified src/data/support.lean
- \+ *lemma* function.mem_support
- \+/\- *lemma* function.support_prod
- \+ *lemma* function.support_prod_subset



## [2020-07-07 09:59:21](https://github.com/leanprover-community/mathlib/commit/12c2acb)
feat(algebra/continued_fractions): add first set of approximation lemmas ([#3218](https://github.com/leanprover-community/mathlib/pull/3218))
#### Estimated changes
Added src/algebra/continued_fractions/computation/approximations.lean
- \+ *lemma* generalized_continued_fraction.exists_int_eq_of_part_denom
- \+ *lemma* generalized_continued_fraction.fib_le_of_continuants_aux_b
- \+ *lemma* generalized_continued_fraction.int_fract_pair.nth_stream_fr_lt_one
- \+ *lemma* generalized_continued_fraction.int_fract_pair.nth_stream_fr_nonneg
- \+ *lemma* generalized_continued_fraction.int_fract_pair.nth_stream_fr_nonneg_lt_one
- \+ *lemma* generalized_continued_fraction.int_fract_pair.one_le_succ_nth_stream_b
- \+ *lemma* generalized_continued_fraction.int_fract_pair.succ_nth_stream_b_le_nth_stream_fr_inv
- \+ *theorem* generalized_continued_fraction.le_of_succ_nth_denom
- \+ *lemma* generalized_continued_fraction.le_of_succ_succ_nth_continuants_aux_b
- \+ *theorem* generalized_continued_fraction.of_denom_mono
- \+ *lemma* generalized_continued_fraction.of_one_le_nth_part_denom
- \+ *lemma* generalized_continued_fraction.of_part_num_eq_one
- \+ *lemma* generalized_continued_fraction.of_part_num_eq_one_and_exists_int_part_denom_eq
- \+ *lemma* generalized_continued_fraction.succ_nth_fib_le_of_nth_denom
- \+ *lemma* generalized_continued_fraction.zero_le_of_continuants_aux_b
- \+ *lemma* generalized_continued_fraction.zero_le_of_denom

Modified src/algebra/continued_fractions/computation/correctness_terminating.lean
- \- *lemma* generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_none
- \+ *lemma* generalized_continued_fraction.of_correctness_of_nth_stream_eq_none

Modified src/algebra/continued_fractions/computation/translations.lean
- \+ *lemma* generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_fr_zero
- \+ *lemma* generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some
- \- *lemma* generalized_continued_fraction.int_fract_pair.obtain_succ_nth_stream_of_fr_zero
- \- *lemma* generalized_continued_fraction.int_fract_pair.obtain_succ_nth_stream_of_gcf_of_nth_eq_some

Modified src/algebra/continued_fractions/continuants_recurrence.lean


Modified src/algebra/continued_fractions/convergents_equiv.lean


Modified src/algebra/continued_fractions/terminated_stable.lean


Modified src/algebra/continued_fractions/translations.lean
- \+ *lemma* generalized_continued_fraction.exists_conts_a_of_num
- \+ *lemma* generalized_continued_fraction.exists_conts_b_of_denom
- \+ *lemma* generalized_continued_fraction.exists_s_a_of_part_num
- \+ *lemma* generalized_continued_fraction.exists_s_b_of_part_denom
- \+ *lemma* generalized_continued_fraction.first_continuant_eq
- \+ *lemma* generalized_continued_fraction.first_denominator_eq
- \+ *lemma* generalized_continued_fraction.first_numerator_eq
- \- *lemma* generalized_continued_fraction.obtain_conts_a_of_num
- \- *lemma* generalized_continued_fraction.obtain_conts_b_of_denom
- \- *lemma* generalized_continued_fraction.obtain_s_a_of_part_num
- \- *lemma* generalized_continued_fraction.obtain_s_b_of_part_denom
- \+ *lemma* generalized_continued_fraction.second_continuant_aux_eq
- \+ *lemma* generalized_continued_fraction.zeroth_denominator_eq_one
- \+ *lemma* generalized_continued_fraction.zeroth_numerator_eq_h



## [2020-07-07 09:25:12](https://github.com/leanprover-community/mathlib/commit/08ffbbb)
feat(analysis/normed_space/operator_norm): normed algebra of continuous linear maps ([#3282](https://github.com/leanprover-community/mathlib/pull/3282))
Given a normed space `E`, its continuous linear endomorphisms form a normed ring, and a normed algebra if `E` is nonzero.  Moreover, the units of this ring are precisely the continuous linear equivalences.
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+ *def* continuous_linear_equiv.of_unit
- \+ *def* continuous_linear_equiv.to_unit
- \+ *def* continuous_linear_equiv.units_equiv
- \+ *lemma* continuous_linear_equiv.units_equiv_to_continuous_linear_map



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
- \+ *lemma* set.bot_eq_empty
- \+/\- *lemma* set.image_eq_range
- \+ *lemma* set.inf_eq_inter
- \+ *lemma* set.le_eq_subset
- \+ *lemma* set.lt_eq_ssubset
- \- *def* set.strict_subset
- \+ *lemma* set.sup_eq_union

Modified src/data/set/intervals/basic.lean


Modified src/data/set/lattice.lean
- \- *lemma* set.bot_eq_empty
- \- *lemma* set.inf_eq_inter
- \- *lemma* set.le_eq_subset
- \- *lemma* set.lt_eq_ssubset
- \- *lemma* set.sup_eq_union

Modified src/data/setoid/basic.lean


Modified src/group_theory/congruence.lean
- \+ *lemma* con.rel_eq_coe

Modified src/order/basic.lean
- \- *theorem* directed.mono
- \- *theorem* directed.mono_comp
- \- *def* directed
- \- *theorem* directed_comp
- \- *theorem* directed_on.mono
- \- *def* directed_on
- \- *theorem* directed_on_iff_directed
- \- *theorem* directed_on_image

Modified src/order/boolean_algebra.lean


Modified src/order/bounded_lattice.lean
- \+ *lemma* bot_apply
- \+ *lemma* inf_apply
- \+ *lemma* sup_apply
- \+ *lemma* top_apply

Modified src/order/complete_lattice.lean
- \- *def* Inf
- \+/\- *lemma* Inf_apply
- \- *def* Sup
- \+/\- *lemma* Sup_apply
- \+/\- *lemma* infi_apply
- \+/\- *lemma* supr_apply

Added src/order/directed.lean
- \+ *theorem* directed.mono
- \+ *theorem* directed.mono_comp
- \+ *def* directed
- \+ *theorem* directed_comp
- \+ *lemma* directed_of_inf
- \+ *lemma* directed_of_sup
- \+ *theorem* directed_on.mono
- \+ *def* directed_on
- \+ *theorem* directed_on_iff_directed
- \+ *theorem* directed_on_image

Modified src/order/filter/bases.lean


Modified src/order/lattice.lean
- \- *lemma* directed_of_inf
- \- *lemma* directed_of_mono
- \- *lemma* directed_of_sup

Modified src/order/order_iso.lean
- \- *def* order_embedding.nat_gt
- \- *def* order_embedding.nat_lt
- \- *theorem* order_embedding.well_founded_iff_no_descending_seq

Added src/order/order_iso_nat.lean
- \+ *def* order_embedding.nat_gt
- \+ *def* order_embedding.nat_lt
- \+ *theorem* order_embedding.well_founded_iff_no_descending_seq

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
- \+ *lemma* add_torsor.vsub_set_empty

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* affine_space.vector_span_def
- \+ *lemma* affine_subspace.affine_span_eq_Inf
- \+ *lemma* affine_subspace.bot_coe
- \+ *lemma* affine_subspace.direction_bot
- \+ *lemma* affine_subspace.direction_inf
- \+ *lemma* affine_subspace.direction_top
- \+ *lemma* affine_subspace.exists_of_lt
- \+ *lemma* affine_subspace.inf_coe
- \+ *lemma* affine_subspace.le_def'
- \+ *lemma* affine_subspace.le_def
- \+ *lemma* affine_subspace.lt_def
- \+ *lemma* affine_subspace.lt_iff_le_and_exists
- \+ *lemma* affine_subspace.mem_inf_iff
- \+ *lemma* affine_subspace.mem_top
- \- *lemma* affine_subspace.mem_univ
- \+ *lemma* affine_subspace.not_le_iff_exists
- \+ *lemma* affine_subspace.not_mem_bot
- \+ *lemma* affine_subspace.span_Union
- \+ *lemma* affine_subspace.span_empty
- \+ *lemma* affine_subspace.span_points_subset_coe_of_subset_coe
- \+ *lemma* affine_subspace.span_union
- \+ *lemma* affine_subspace.span_univ
- \+ *lemma* affine_subspace.top_coe
- \- *def* affine_subspace.univ
- \- *lemma* affine_subspace.univ_coe



## [2020-07-06 19:04:56](https://github.com/leanprover-community/mathlib/commit/edd29d0)
chore(ring_theory/power_series): weaken assumptions for nontrivial ([#3301](https://github.com/leanprover-community/mathlib/pull/3301))
#### Estimated changes
Modified src/logic/nontrivial.lean


Modified src/ring_theory/power_series.lean
- \+/\- *lemma* mv_power_series.X_inj



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
Added src/data/sym.lean
- \+ *def* sym.sym'
- \+ *def* sym.sym_equiv_sym'
- \+ *def* sym
- \+ *def* vector.perm.is_setoid

Added src/data/sym2.lean
- \+ *lemma* sym2.congr_right
- \+ *def* sym2.diag
- \+ *lemma* sym2.eq_iff
- \+ *lemma* sym2.eq_swap
- \+ *def* sym2.equiv_multiset
- \+ *def* sym2.equiv_sym
- \+ *def* sym2.from_rel
- \+ *lemma* sym2.from_rel_irreflexive
- \+ *lemma* sym2.from_rel_proj_prop
- \+ *lemma* sym2.from_rel_prop
- \+ *def* sym2.is_diag
- \+ *lemma* sym2.is_diag_iff_proj_eq
- \+ *def* sym2.map
- \+ *lemma* sym2.map_comp
- \+ *lemma* sym2.map_id
- \+ *def* sym2.mem
- \+ *lemma* sym2.mem_iff
- \+ *lemma* sym2.mem_other_spec
- \+ *lemma* sym2.mk_has_mem
- \+ *def* sym2.mk_has_vmem
- \+ *lemma* sym2.other_is_mem_other
- \+ *lemma* sym2.rel.is_equivalence
- \+ *lemma* sym2.rel.symm
- \+ *lemma* sym2.rel.trans
- \+ *inductive* sym2.rel
- \+ *def* sym2.sym2_equiv_sym'
- \+ *def* sym2.vmem.other
- \+ *def* sym2.vmem
- \+ *lemma* sym2.vmem_other_spec
- \+ *def* sym2



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
- \+/\- *lemma* char_p.false_of_nonzero_of_char_one
- \+/\- *lemma* char_p.ring_char_ne_one

Modified src/algebra/classical_lie_algebras.lean
- \+/\- *lemma* lie_algebra.special_linear.sl_non_abelian

Modified src/algebra/direct_limit.lean


Modified src/algebra/euclidean_domain.lean


Modified src/algebra/field.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/group_with_zero.lean
- \+/\- *lemma* is_unit.ne_zero
- \+/\- *theorem* not_is_unit_zero
- \+/\- *lemma* one_ne_zero
- \- *lemma* subsingleton_or_nonzero
- \+/\- *lemma* units.ne_zero
- \+/\- *lemma* zero_ne_one

Modified src/algebra/opposites.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/ring.lean
- \+/\- *structure* is_integral_domain
- \- *theorem* nonzero.of_ne
- \+/\- *lemma* pred_ne_self
- \+/\- *lemma* succ_ne_self
- \+/\- *lemma* units.coe_ne_zero

Modified src/analysis/normed_space/basic.lean
- \+/\- *theorem* frontier_closed_ball'
- \+/\- *theorem* interior_closed_ball'
- \+/\- *lemma* normed_algebra.to_nonzero
- \+/\- *lemma* units.norm_pos

Modified src/analysis/normed_space/hahn_banach.lean
- \+/\- *theorem* exists_dual_vector'

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* continuous_linear_equiv.norm_pos
- \+/\- *lemma* continuous_linear_equiv.norm_symm_pos
- \+/\- *lemma* continuous_linear_equiv.one_le_norm_mul_norm_symm
- \+/\- *lemma* continuous_linear_map.norm_id

Modified src/analysis/normed_space/units.lean


Modified src/data/complex/basic.lean


Modified src/data/equiv/ring.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_le_one_iff_subsingleton
- \+ *lemma* fintype.one_lt_card_iff_nontrivial

Modified src/data/int/basic.lean


Modified src/data/matrix/pequiv.lean
- \+/\- *lemma* pequiv.to_matrix_injective

Modified src/data/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.total_degree_X

Modified src/data/nat/basic.lean


Modified src/data/num/lemmas.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/polynomial.lean
- \+/\- *lemma* polynomial.monic.ne_zero
- \+/\- *theorem* polynomial.nonzero.of_polynomial_ne

Modified src/data/rat/basic.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/nnreal.lean


Modified src/data/zmod/basic.lean


Modified src/data/zsqrtd/basic.lean
- \+/\- *theorem* zsqrtd.conj_mul

Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/perfect_closure.lean


Modified src/field_theory/subfield.lean


Modified src/group_theory/free_abelian_group.lean
- \+ *lemma* free_abelian_group.mul_def

Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_pos
- \+/\- *lemma* dim_pos_iff_exists_ne_zero
- \+ *lemma* dim_pos_iff_nontrivial
- \+/\- *lemma* exists_mem_ne_zero_of_dim_pos
- \+/\- *theorem* is_basis.le_span

Added src/logic/nontrivial.lean
- \+ *lemma* exists_ne
- \+ *lemma* exists_pair_ne
- \+ *lemma* nontrivial_iff
- \+ *lemma* nontrivial_of_ne
- \+ *lemma* not_nontrivial_iff_subsingleton
- \+ *lemma* subsingleton_iff
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
- \+/\- *lemma* ring_hom.not_one_mem_ker

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
- \+ *theorem* cardinal.one_lt_iff_nontrivial

Modified src/set_theory/ordinal.lean


Modified src/topology/metric_space/isometry.lean




## [2020-07-06 13:27:20](https://github.com/leanprover-community/mathlib/commit/2c9d9bd)
chore(scripts/nolints_summary.sh): list number of nolints per file
#### Estimated changes
Added scripts/nolints_summary.sh




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
- \+ *lemma* finset.inf_coe
- \+ *lemma* finset.inf_def
- \- *lemma* finset.inf_val
- \+ *lemma* finset.sup_coe

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.div_lt_top
- \+ *lemma* ennreal.infi_mul
- \+ *lemma* ennreal.inv_lt_top
- \+ *lemma* ennreal.mul_infi
- \+ *lemma* ennreal.mul_pos

Modified src/order/bounded_lattice.lean


Modified src/topology/algebra/group.lean
- \+ *lemma* compact_covered_by_mul_left_translates
- \+ *lemma* compact_open_separated_mul
- \+ *lemma* one_open_separated_mul

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tsum_subtype_eq_sum

Modified src/topology/basic.lean
- \+ *lemma* is_closed.preimage
- \+ *lemma* is_open.preimage

Added src/topology/compacts.lean
- \+ *def* topological_space.closeds
- \+ *lemma* topological_space.compacts.bot_val
- \+ *lemma* topological_space.compacts.equiv_to_fun_val
- \+ *lemma* topological_space.compacts.finset_sup_val
- \+ *lemma* topological_space.compacts.map_val
- \+ *lemma* topological_space.compacts.sup_val
- \+ *def* topological_space.compacts
- \+ *def* topological_space.nonempty_compacts.to_closeds
- \+ *def* topological_space.nonempty_compacts
- \+ *def* topological_space.positive_compacts:

Modified src/topology/constructions.lean
- \+ *lemma* exists_nhds_square

Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph.is_open_preimage

Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/isometry.lean


Modified src/topology/opens.lean
- \- *def* continuous.comap
- \- *lemma* continuous.comap_id
- \- *lemma* continuous.comap_mono
- \- *def* topological_space.closeds
- \- *def* topological_space.nonempty_compacts.to_closeds
- \- *def* topological_space.nonempty_compacts
- \+ *def* topological_space.open_nhds_of
- \+/\- *lemma* topological_space.opens.Sup_s
- \+ *lemma* topological_space.opens.coe_comap
- \+ *def* topological_space.opens.comap
- \+ *lemma* topological_space.opens.comap_id
- \+ *lemma* topological_space.opens.comap_mono
- \+ *lemma* topological_space.opens.comap_val
- \+/\- *lemma* topological_space.opens.ext
- \+ *lemma* topological_space.opens.ext_iff
- \+/\- *lemma* topological_space.opens.gc
- \+/\- *def* topological_space.opens.gi
- \+/\- *def* topological_space.opens.is_basis
- \+ *lemma* topological_space.opens.supr_def
- \+ *lemma* topological_space.opens.val_eq_coe

Modified src/topology/separation.lean
- \+ *lemma* compact.binary_compact_cover
- \+ *lemma* compact.finite_compact_cover
- \+ *lemma* compact.inter
- \+ *lemma* exists_compact_superset
- \+ *lemma* exists_open_with_compact_closure

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
Added src/algebra/group/inj_surj.lean


Modified src/algebra/group_with_zero.lean


Deleted src/algebra/inj_surj.lean
- \- *def* comm_group_of_injective
- \- *def* comm_group_of_surjective
- \- *def* comm_monoid_of_injective
- \- *def* comm_monoid_of_surjective
- \- *def* comm_ring_of_injective
- \- *def* comm_ring_of_surjective
- \- *def* comm_semigroup_of_injective
- \- *def* comm_semigroup_of_surjective
- \- *def* comm_semiring_of_injective
- \- *def* comm_semiring_of_surjective
- \- *def* group_of_injective
- \- *def* group_of_surjective
- \- *def* monoid_of_injective
- \- *def* monoid_of_surjective
- \- *def* ring_of_injective
- \- *def* ring_of_surjective
- \- *def* semigroup_of_injective
- \- *def* semigroup_of_surjective
- \- *def* semiring_of_injective
- \- *def* semiring_of_surjective

Modified src/algebra/module.lean


Modified src/algebra/ring.lean
- \+/\- *lemma* ring_hom.cancel_left
- \+/\- *lemma* ring_hom.cancel_right

Modified src/group_theory/group_action.lean
- \- *lemma* mul_action.bijective

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* submonoid.coe_injective

Modified src/group_theory/submonoid/operations.lean


Modified src/logic/function/basic.lean
- \+ *theorem* function.injective.eq_iff'
- \+ *lemma* function.injective.ne_iff'
- \+ *theorem* function.surjective.exists
- \+ *theorem* function.surjective.exists₂
- \+ *theorem* function.surjective.exists₃
- \+ *theorem* function.surjective.forall
- \+ *theorem* function.surjective.forall₂
- \+ *theorem* function.surjective.forall₃



## [2020-07-06 04:31:33](https://github.com/leanprover-community/mathlib/commit/ffa504c)
fix(finset/lattice): undo removal of bUnion_preimage_singleton ([#3293](https://github.com/leanprover-community/mathlib/pull/3293))
In [#3189](https://github.com/leanprover-community/mathlib/pull/3189) I removed it, which was a mistake.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.bUnion_preimage_singleton



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
- \- *def* tactic.explode.head'
- \+/\- *inductive* tactic.explode.status



## [2020-07-05 10:13:00](https://github.com/leanprover-community/mathlib/commit/293287d)
chore(category_theory/over/limits): change instance to def ([#3281](https://github.com/leanprover-community/mathlib/pull/3281))
Having this as an instance causes confusion since it's a different terminal object to the one inferred by the other limit constructions in the file.
#### Estimated changes
Modified src/category_theory/limits/over.lean
- \+ *def* category_theory.over.over_has_terminal



## [2020-07-05 09:46:41](https://github.com/leanprover-community/mathlib/commit/f39e0d7)
chore(algebra/category): use preadditivity for biproducts ([#3280](https://github.com/leanprover-community/mathlib/pull/3280))
We can avoid some scary calculations thanks to abstract nonsense.
#### Estimated changes
Modified src/algebra/category/Group/biproducts.lean
- \- *def* AddCommGroup.has_colimit.desc
- \- *lemma* AddCommGroup.has_colimit.desc_apply



## [2020-07-04 19:11:32](https://github.com/leanprover-community/mathlib/commit/023d4f7)
feat(ring_theory/localization): order embedding of ideals, local ring instance ([#3287](https://github.com/leanprover-community/mathlib/pull/3287))
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/localization.lean
- \+ *def* ideal.prime_compl
- \+ *def* localization.at_prime
- \+ *def* localization_map.at_prime
- \+/\- *def* localization_map.codomain
- \+ *def* localization_map.le_order_embedding
- \+ *theorem* localization_map.map_comap
- \+ *lemma* localization_map.mk'_mul_mk'_eq_one'
- \+ *lemma* localization_map.mk'_mul_mk'_eq_one
- \+/\- *lemma* localization_map.mk'_self
- \+ *lemma* localization_map.mk'_surjective



## [2020-07-04 15:02:36](https://github.com/leanprover-community/mathlib/commit/08e1adc)
feat(data/pnat): basic pnat facts needed for perfect numbers (3094) ([#3274](https://github.com/leanprover-community/mathlib/pull/3274))
define pnat.coprime
add some basic lemmas pnats, mostly about coprime, gcd
designate some existing lemmas with @[simp]
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* pnat.coe_eq_one_iff
- \+ *lemma* pnat.coe_inj
- \+ *lemma* pnat.coprime.coprime_dvd_left
- \+ *lemma* pnat.coprime.factor_eq_gcd_left
- \+ *lemma* pnat.coprime.factor_eq_gcd_left_right
- \+ *lemma* pnat.coprime.factor_eq_gcd_right
- \+ *lemma* pnat.coprime.factor_eq_gcd_right_right
- \+ *lemma* pnat.coprime.gcd_mul
- \+ *lemma* pnat.coprime.gcd_mul_left_cancel
- \+ *lemma* pnat.coprime.gcd_mul_left_cancel_right
- \+ *lemma* pnat.coprime.gcd_mul_right_cancel
- \+ *lemma* pnat.coprime.gcd_mul_right_cancel_right
- \+ *lemma* pnat.coprime.mul
- \+ *lemma* pnat.coprime.mul_right
- \+ *lemma* pnat.coprime.pow
- \+ *lemma* pnat.coprime.symm
- \+ *def* pnat.coprime
- \+ *lemma* pnat.coprime_coe
- \+ *lemma* pnat.coprime_one
- \+ *lemma* pnat.dvd_prime
- \+ *lemma* pnat.eq_one_of_lt_two
- \+ *lemma* pnat.exists_prime_and_dvd
- \+ *lemma* pnat.gcd_comm
- \+ *lemma* pnat.gcd_eq_left
- \+ *lemma* pnat.gcd_eq_left_iff_dvd
- \+ *lemma* pnat.gcd_eq_right_iff_dvd
- \+ *lemma* pnat.gcd_one
- \+ *lemma* pnat.le_of_dvd
- \+ *lemma* pnat.not_prime_one
- \+ *lemma* pnat.one_coprime
- \+ *lemma* pnat.one_gcd
- \+ *lemma* pnat.prime.ne_one
- \+ *lemma* pnat.prime.not_dvd_one
- \+ *lemma* pnat.prime.one_lt
- \+ *lemma* pnat.prime_two

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
- \+ *lemma* with_top.op_sum
- \+ *lemma* with_top.unop_sum

Modified src/algebra/geom_sum.lean
- \+ *lemma* mul_geom_sum
- \+ *lemma* mul_neg_geom_sum
- \+ *lemma* op_geom_series

Modified src/algebra/group_power.lean
- \+ *lemma* units.op_pow
- \+ *lemma* units.unop_pow

Modified src/algebra/group_with_zero.lean
- \+ *lemma* subsingleton_or_nonzero

Modified src/algebra/opposites.lean
- \+ *lemma* opposite.coe_op_add_hom
- \+ *lemma* opposite.coe_unop_add_hom
- \+ *def* opposite.op_add_hom
- \+ *lemma* opposite.op_sub
- \+ *def* opposite.unop_add_hom
- \+ *lemma* opposite.unop_sub

Modified src/algebra/ring.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* add_monoid_hom.continuous_of_bound
- \+ *lemma* add_monoid_hom.lipschitz_of_bound
- \+ *lemma* eventually_norm_pow_le
- \+ *lemma* has_sum_of_bounded_monoid_hom_of_has_sum
- \+ *lemma* has_sum_of_bounded_monoid_hom_of_summable
- \+ *lemma* mul_left_bound
- \+ *lemma* mul_right_bound
- \+ *lemma* normed_algebra.norm_one
- \+ *lemma* normed_algebra.to_nonzero
- \+ *lemma* normed_algebra.zero_ne_one
- \+ *lemma* squeeze_zero_norm'
- \+ *lemma* squeeze_zero_norm
- \+ *lemma* summable_of_norm_bounded_eventually
- \+ *lemma* units.norm_pos

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.has_sum
- \+ *lemma* continuous_linear_map.has_sum_of_summable
- \+ *def* continuous_linear_map.lmul_left
- \+ *lemma* continuous_linear_map.lmul_left_apply
- \+ *def* continuous_linear_map.lmul_right
- \+ *lemma* continuous_linear_map.lmul_right_apply

Added src/analysis/normed_space/units.lean
- \+ *def* units.add
- \+ *lemma* units.add_coe
- \+ *lemma* units.is_open
- \+ *def* units.one_sub
- \+ *lemma* units.one_sub_coe
- \+ *def* units.unit_of_nearby
- \+ *lemma* units.unit_of_nearby_coe

Modified src/analysis/specific_limits.lean
- \+ *lemma* geom_series_mul_neg
- \+ *lemma* mul_neg_geom_series
- \+ *lemma* normed_ring.summable_geometric_of_norm_lt_1
- \+/\- *lemma* tendsto_pow_at_top_nhds_0_of_norm_lt_1

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
- \+ *lemma* dvd_symm_iff_of_irreducible
- \+ *lemma* dvd_symm_of_irreducible
- \+ *lemma* prime.dvd_of_dvd_pow

Modified src/algebra/field.lean
- \+ *lemma* ring_hom.map_units_inv

Modified src/algebra/group/units.lean
- \+ *lemma* is_unit.mul

Modified src/algebra/group_with_zero.lean
- \+ *lemma* monoid_hom.map_units_inv

Modified src/algebra/ring.lean
- \+ *lemma* is_unit.mul_left_dvd_of_dvd
- \+ *lemma* is_unit.mul_right_dvd_of_dvd

Modified src/data/polynomial.lean
- \+ *lemma* polynomial.dvd_term_of_dvd_eval_of_dvd_terms
- \+ *lemma* polynomial.dvd_term_of_is_root_of_dvd_terms
- \+ *lemma* polynomial.is_root_of_aeval_algebra_map_eq_zero
- \+ *lemma* polynomial.is_root_of_eval₂_map_eq_zero

Modified src/ring_theory/integral_domain.lean
- \+ *lemma* left_dvd_or_dvd_right_of_dvd_prime_mul

Modified src/ring_theory/localization.lean
- \+ *lemma* fraction_map.eq_zero_of_num_eq_zero
- \+ *lemma* fraction_map.exists_reduced_fraction
- \+ *lemma* fraction_map.is_integer_of_is_unit_denom
- \+ *lemma* fraction_map.is_unit_denom_of_num_eq_zero
- \+ *lemma* fraction_map.mk'_num_denom
- \+ *lemma* fraction_map.num_denom_reduced
- \+ *lemma* fraction_map.num_mul_denom_eq_num_iff_eq'
- \+ *lemma* fraction_map.num_mul_denom_eq_num_iff_eq
- \+ *lemma* fraction_map.num_mul_denom_eq_num_mul_denom_iff_eq
- \+ *lemma* mul_mem_non_zero_divisors

Added src/ring_theory/polynomial/rational_root.lean
- \+ *lemma* coeff_scale_roots
- \+ *lemma* coeff_scale_roots_nat_degree
- \+ *lemma* degree_scale_roots
- \+ *theorem* denom_dvd_of_is_root
- \+ *theorem* is_integer_of_is_root_of_monic
- \+ *lemma* monic_scale_roots_iff
- \+ *lemma* nat_degree_scale_roots
- \+ *theorem* num_dvd_of_is_root
- \+ *lemma* num_is_root_scale_roots_of_aeval_eq_zero
- \+ *lemma* scale_roots_aeval_eq_zero
- \+ *lemma* scale_roots_aeval_eq_zero_of_aeval_div_eq_zero
- \+ *lemma* scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero
- \+ *lemma* scale_roots_eval₂_eq_zero
- \+ *lemma* scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero
- \+ *lemma* scale_roots_ne_zero
- \+ *lemma* support_scale_roots_eq
- \+ *lemma* support_scale_roots_le
- \+ *lemma* unique_factorization_domain.integer_of_integral
- \+ *lemma* unique_factorization_domain.integrally_closed
- \+ *lemma* zero_scale_roots

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* unique_factorization_domain.dvd_of_dvd_mul_left_of_no_prime_factors
- \+ *lemma* unique_factorization_domain.dvd_of_dvd_mul_right_of_no_prime_factors
- \+ *lemma* unique_factorization_domain.exists_reduced_factors'
- \+ *lemma* unique_factorization_domain.exists_reduced_factors
- \+ *lemma* unique_factorization_domain.no_factors_of_no_prime_factors



## [2020-07-03 22:00:28](https://github.com/leanprover-community/mathlib/commit/c4bf9e4)
chore(algebra/ordered_group): deduplicate ([#3279](https://github.com/leanprover-community/mathlib/pull/3279))
For historical reasons we have some lemmas duplicated for `ordered_comm_monoid`
and `ordered_cancel_comm_monoid`. This PR merges some duplicates.
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/algebra/group_power.lean


Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/ordered_group.lean
- \- *lemma* le_mul_of_le_of_one_le'
- \- *lemma* le_mul_of_one_le_left''
- \- *lemma* le_mul_of_one_le_of_le'
- \- *lemma* le_mul_of_one_le_right''
- \- *lemma* lt_of_mul_lt_mul_left''
- \- *lemma* lt_of_mul_lt_mul_right''
- \- *lemma* mul_eq_one_iff_eq_one_and_eq_one_of_one_le_of_one_le
- \- *lemma* mul_le_mul_left''
- \+/\- *lemma* mul_le_mul_left'
- \- *lemma* mul_le_mul_right''
- \+/\- *lemma* mul_le_mul_right'
- \- *lemma* mul_le_one''
- \- *lemma* mul_le_one_of_le_one_of_le_one
- \- *lemma* mul_one_lt'
- \- *lemma* mul_one_lt
- \- *lemma* mul_one_lt_of_one_le_of_one_lt'
- \- *lemma* mul_one_lt_of_one_le_of_one_lt
- \- *lemma* mul_one_lt_of_one_lt_of_one_le'
- \- *lemma* mul_one_lt_of_one_lt_of_one_le
- \- *lemma* one_le_mul'
- \- *lemma* one_le_mul_of_one_le_of_one_le
- \+ *lemma* one_lt_mul'
- \+ *lemma* one_lt_mul_of_le_of_lt'
- \+ *lemma* one_lt_mul_of_lt_of_le'

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
- \+/\- *lemma* filter.tendsto_at_top_add_left_of_le'
- \+/\- *lemma* filter.tendsto_at_top_add_nonneg_left'
- \+/\- *lemma* filter.tendsto_at_top_add_nonneg_right'
- \+/\- *lemma* filter.tendsto_at_top_add_right_of_le'
- \+/\- *lemma* filter.tendsto_at_top_mono'
- \+/\- *lemma* filter.tendsto_at_top_of_add_bdd_above_left'
- \+/\- *lemma* filter.tendsto_at_top_of_add_bdd_above_right'

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
- \+ *theorem* polynomial.X_dvd_iff
- \+ *theorem* polynomial.X_sub_C_ne_zero
- \+ *theorem* polynomial.irreducible_X
- \+ *theorem* polynomial.irreducible_X_sub_C
- \+ *lemma* polynomial.nat_degree_X
- \+ *lemma* polynomial.nat_degree_X_le
- \+/\- *lemma* polynomial.nat_degree_X_sub_C
- \+ *theorem* polynomial.nat_degree_div_by_monic
- \+ *lemma* polynomial.nat_degree_le_nat_degree
- \+/\- *theorem* polynomial.nat_degree_le_of_degree_le
- \+ *theorem* polynomial.not_is_unit_X
- \+ *theorem* polynomial.not_is_unit_X_sub_C
- \+ *theorem* polynomial.prime_X
- \+ *theorem* polynomial.prime_X_sub_C
- \+ *lemma* polynomial.root_mul
- \+ *lemma* polynomial.roots_X_sub_C
- \+ *lemma* polynomial.roots_mul

Modified src/field_theory/splitting_field.lean
- \+ *theorem* polynomial.X_sub_C_mul_remove_factor
- \+ *def* polynomial.factor
- \+ *theorem* polynomial.factor_dvd_of_degree_ne_zero
- \+ *theorem* polynomial.factor_dvd_of_nat_degree_ne_zero
- \+ *theorem* polynomial.factor_dvd_of_not_is_unit
- \+ *theorem* polynomial.nat_degree_remove_factor'
- \+ *theorem* polynomial.nat_degree_remove_factor
- \+ *def* polynomial.remove_factor
- \+ *lemma* polynomial.splits_of_splits_of_dvd
- \+ *theorem* polynomial.splitting_field.adjoin_roots
- \+ *def* polynomial.splitting_field.lift
- \+ *def* polynomial.splitting_field
- \+ *theorem* polynomial.splitting_field_aux.adjoin_roots
- \+ *theorem* polynomial.splitting_field_aux.algebra_map_succ
- \+ *theorem* polynomial.splitting_field_aux.exists_lift
- \+ *theorem* polynomial.splitting_field_aux.succ
- \+ *def* polynomial.splitting_field_aux

Modified src/ring_theory/adjoin_root.lean
- \+ *theorem* adjoin_root.adjoin_root_eq_top
- \+ *lemma* adjoin_root.aeval_eq
- \+ *lemma* adjoin_root.algebra_map_eq
- \+ *theorem* adjoin_root.induction_on
- \+ *lemma* adjoin_root.lift_comp_of
- \+/\- *lemma* adjoin_root.lift_root
- \+ *lemma* adjoin_root.mk_X

Modified src/ring_theory/algebra.lean
- \+ *theorem* algebra.comap_top
- \+ *theorem* algebra.map_bot
- \+ *theorem* algebra.map_top
- \+ *def* subalgebra.comap'
- \+ *def* subalgebra.map
- \+ *theorem* subalgebra.map_le

Added src/ring_theory/algebra_tower.lean
- \+ *theorem* algebra.adjoin_algebra_map'
- \+ *theorem* algebra.adjoin_algebra_map
- \+ *lemma* is_algebra_tower.algebra.ext
- \+ *theorem* is_algebra_tower.algebra_map_apply
- \+ *theorem* is_algebra_tower.algebra_map_eq
- \+ *theorem* is_algebra_tower.comap_eq
- \+ *theorem* is_algebra_tower.of_algebra_map_eq
- \+ *theorem* is_algebra_tower.range_under_adjoin
- \+ *def* is_algebra_tower.subalgebra_comap
- \+ *theorem* is_algebra_tower.subalgebra_comap_top
- \+ *def* is_algebra_tower.to_alg_hom

Modified src/ring_theory/polynomial/basic.lean
- \+ *theorem* polynomial.exists_irreducible_of_degree_pos
- \+ *theorem* polynomial.exists_irreducible_of_nat_degree_ne_zero
- \+ *theorem* polynomial.exists_irreducible_of_nat_degree_pos



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
- \+/\- *lemma* mem_inv_smul_set_iff
- \+/\- *lemma* mem_smul_set_iff_inv_smul_mem
- \+ *lemma* set.Union_mul_left_image
- \+ *lemma* set.Union_mul_right_image
- \- *def* set.add_comm_monoid
- \- *def* set.comm_monoid
- \+ *lemma* set.compl_inv
- \+ *lemma* set.empty_mul
- \- *lemma* set.empty_pointwise_mul
- \+ *lemma* set.finite.mul
- \+ *def* set.fintype_mul
- \+ *lemma* set.image2_mul
- \+ *lemma* set.image2_smul
- \+ *def* set.image_hom
- \+ *lemma* set.image_inv
- \+ *lemma* set.image_mul
- \+ *lemma* set.image_mul_left'
- \+ *lemma* set.image_mul_left
- \+ *lemma* set.image_mul_prod
- \+ *lemma* set.image_mul_right'
- \+ *lemma* set.image_mul_right
- \+ *theorem* set.image_one
- \- *lemma* set.image_pointwise_mul
- \+ *lemma* set.image_smul
- \+ *lemma* set.image_smul_prod
- \+ *lemma* set.inter_inv
- \+ *lemma* set.inv_mem_inv
- \+ *lemma* set.inv_preimage
- \+ *lemma* set.mem_inv
- \+ *lemma* set.mem_mul
- \+ *lemma* set.mem_one
- \- *lemma* set.mem_pointwise_mul
- \- *lemma* set.mem_pointwise_one
- \+ *lemma* set.mem_smul
- \+/\- *lemma* set.mem_smul_set
- \+ *lemma* set.mul_empty
- \+ *lemma* set.mul_mem_mul
- \- *lemma* set.mul_mem_pointwise_mul
- \+ *lemma* set.mul_singleton
- \+ *lemma* set.mul_subset_mul
- \+ *lemma* set.mul_union
- \+ *lemma* set.nonempty.mul
- \- *lemma* set.nonempty.pointwise_mul
- \+ *lemma* set.one_mem_one
- \+ *theorem* set.one_nonempty
- \+ *theorem* set.one_subset
- \- *def* set.pointwise_add_fintype
- \- *def* set.pointwise_inv
- \- *def* set.pointwise_mul
- \- *def* set.pointwise_mul_comm_semiring
- \- *lemma* set.pointwise_mul_empty
- \- *lemma* set.pointwise_mul_eq_Union_mul_left
- \- *lemma* set.pointwise_mul_eq_Union_mul_right
- \- *lemma* set.pointwise_mul_eq_image
- \- *lemma* set.pointwise_mul_finite
- \- *def* set.pointwise_mul_fintype
- \- *def* set.pointwise_mul_image_ring_hom
- \- *def* set.pointwise_mul_monoid
- \- *def* set.pointwise_mul_semigroup
- \- *def* set.pointwise_mul_semiring
- \- *lemma* set.pointwise_mul_subset_mul
- \- *lemma* set.pointwise_mul_union
- \- *def* set.pointwise_one
- \- *def* set.pointwise_smul
- \+ *lemma* set.preimage_mul_left_one'
- \+ *lemma* set.preimage_mul_left_one
- \+ *lemma* set.preimage_mul_preimage_subset
- \+ *lemma* set.preimage_mul_right_one'
- \+ *lemma* set.preimage_mul_right_one
- \- *lemma* set.preimage_pointwise_mul_preimage_subset
- \+ *def* set.set_semiring
- \- *lemma* set.singleton.is_monoid_hom
- \+ *def* set.singleton_hom
- \+ *lemma* set.singleton_mul
- \+ *lemma* set.singleton_mul_singleton
- \+ *lemma* set.singleton_one
- \+ *lemma* set.singleton_smul
- \+/\- *lemma* set.smul_mem_smul_set
- \- *def* set.smul_set
- \- *def* set.smul_set_action
- \+/\- *lemma* set.smul_set_empty
- \- *lemma* set.smul_set_eq_image
- \- *lemma* set.smul_set_eq_pointwise_smul_singleton
- \+/\- *lemma* set.smul_set_mono
- \+/\- *lemma* set.smul_set_union
- \+ *lemma* set.union_inv
- \+ *lemma* set.union_mul
- \- *lemma* set.union_pointwise_mul
- \+ *lemma* set.univ_mul_univ
- \- *lemma* set.univ_pointwise_mul_univ
- \+/\- *lemma* zero_smul_set

Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/convex/topology.lean


Modified src/data/set/basic.lean
- \+ *def* set.image2
- \+ *lemma* set.image2_congr'
- \+ *lemma* set.image2_congr
- \+ *lemma* set.image2_empty_left
- \+ *lemma* set.image2_empty_right
- \+ *lemma* set.image2_image2_left
- \+ *lemma* set.image2_image2_right
- \+ *lemma* set.image2_image_left
- \+ *lemma* set.image2_image_right
- \+ *lemma* set.image2_inter_subset_left
- \+ *lemma* set.image2_inter_subset_right
- \+ *lemma* set.image2_left
- \+ *lemma* set.image2_right
- \+ *lemma* set.image2_singleton
- \+ *lemma* set.image2_singleton_left
- \+ *lemma* set.image2_singleton_right
- \+ *lemma* set.image2_subset
- \+ *lemma* set.image2_swap
- \+ *lemma* set.image2_union_left
- \+ *lemma* set.image2_union_right
- \+ *def* set.image3
- \+ *lemma* set.image3_congr'
- \+ *lemma* set.image3_congr
- \+ *lemma* set.image_eta
- \+ *lemma* set.image_image2
- \+ *lemma* set.image_prod
- \+ *lemma* set.mem_image2
- \+ *lemma* set.mem_image2_eq
- \+ *lemma* set.mem_image2_iff
- \+ *lemma* set.mem_image2_of_mem
- \+ *lemma* set.mem_image3
- \+ *lemma* set.nonempty.image2
- \+ *lemma* set.nonempty_def

Modified src/data/set/finite.lean
- \+ *lemma* set.finite.image2

Modified src/data/set/intervals/image_preimage.lean
- \+/\- *lemma* set.image_add_const_Ici
- \+/\- *lemma* set.image_add_const_Iic
- \+/\- *lemma* set.image_add_const_Iio
- \+/\- *lemma* set.image_add_const_Ioi
- \+/\- *lemma* set.image_neg_Icc
- \+/\- *lemma* set.image_neg_Ici
- \+/\- *lemma* set.image_neg_Ico
- \+/\- *lemma* set.image_neg_Iic
- \+/\- *lemma* set.image_neg_Iio
- \+/\- *lemma* set.image_neg_Ioc
- \+/\- *lemma* set.image_neg_Ioi
- \+/\- *lemma* set.image_neg_Ioo
- \+/\- *lemma* set.preimage_neg_Icc
- \+/\- *lemma* set.preimage_neg_Ici
- \+/\- *lemma* set.preimage_neg_Ico
- \+/\- *lemma* set.preimage_neg_Iic
- \+/\- *lemma* set.preimage_neg_Iio
- \+/\- *lemma* set.preimage_neg_Ioc
- \+/\- *lemma* set.preimage_neg_Ioi
- \+/\- *lemma* set.preimage_neg_Ioo

Modified src/data/set/lattice.lean
- \+ *lemma* set.Union_image_left
- \+ *lemma* set.Union_image_right

Modified src/group_theory/group_action.lean
- \+ *lemma* eq_inv_smul_iff
- \+ *lemma* inv_smul_eq_iff

Modified src/logic/function/basic.lean
- \+ *lemma* function.injective2.eq_iff
- \+ *def* function.injective2

Modified src/order/filter/pointwise.lean
- \+ *lemma* filter.map.is_monoid_hom
- \- *lemma* filter.map_pointwise_mul
- \- *lemma* filter.map_pointwise_one
- \+ *lemma* filter.mem_mul
- \+ *lemma* filter.mem_one
- \- *lemma* filter.mem_pointwise_mul
- \- *lemma* filter.mem_pointwise_one
- \+ *lemma* filter.mul_mem_mul
- \- *lemma* filter.mul_mem_pointwise_mul
- \+ *lemma* filter.mul_ne_bot
- \- *lemma* filter.pointwise_add_map_is_add_monoid_hom
- \- *def* filter.pointwise_mul
- \- *lemma* filter.pointwise_mul_assoc
- \- *lemma* filter.pointwise_mul_le_mul
- \- *lemma* filter.pointwise_mul_map_is_monoid_hom
- \- *def* filter.pointwise_mul_monoid
- \- *lemma* filter.pointwise_mul_ne_bot
- \- *lemma* filter.pointwise_mul_one
- \- *def* filter.pointwise_one
- \- *lemma* filter.pointwise_one_mul

Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/algebra_operations.lean
- \+/\- *lemma* submodule.mul_subset_mul
- \+/\- *lemma* submodule.pow_subset_pow
- \+/\- *lemma* submodule.smul_def
- \+/\- *lemma* submodule.smul_le_smul
- \+/\- *def* submodule.span.ring_hom

Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideals.lean
- \+/\- *lemma* ideal.span_singleton_one

Modified src/ring_theory/noetherian.lean


Modified src/topology/algebra/group.lean
- \+ *lemma* is_open_mul_left
- \+ *lemma* is_open_mul_right
- \- *lemma* is_open_pointwise_mul_left
- \- *lemma* is_open_pointwise_mul_right
- \+/\- *lemma* nhds_is_mul_hom
- \+ *lemma* nhds_mul
- \- *lemma* nhds_pointwise_mul

Modified src/topology/metric_space/gromov_hausdorff.lean




## [2020-07-03 15:04:51](https://github.com/leanprover-community/mathlib/commit/f9f0ca6)
feat(analysic/calculus/times_cont_diff): add times_cont_diff_within_at ([#3262](https://github.com/leanprover-community/mathlib/pull/3262))
I want to refactor manifolds, defining local properties in the model space and showing that they automatically inherit nice behavior in manifolds. 
In this PR, we modify a little bit the definition of smooth functions in vector spaces by introducing a predicate `times_cont_diff_within_at` (just like we already have `continuous_within_at` or `differentiable_within_at`) and using it in all definitions and proofs. This will be the basis of the locality argument in manifolds.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* continuous_linear_equiv.comp_times_cont_diff_within_at_iff
- \+ *lemma* continuous_linear_equiv.times_cont_diff_within_at_comp_iff
- \+ *lemma* filter.eventually_eq.times_cont_diff_within_at_iff
- \+ *lemma* times_cont_diff.times_cont_diff_at
- \+ *lemma* times_cont_diff_at.continuous_at
- \+ *lemma* times_cont_diff_at.continuous_linear_map_comp
- \+ *lemma* times_cont_diff_at.differentiable
- \+ *lemma* times_cont_diff_at.has_strict_fderiv_at
- \+ *lemma* times_cont_diff_at.of_le
- \+ *lemma* times_cont_diff_at.times_cont_diff_within_at
- \+ *def* times_cont_diff_at
- \+ *lemma* times_cont_diff_at_const
- \+ *lemma* times_cont_diff_at_top
- \+ *lemma* times_cont_diff_iff_times_cont_diff_at
- \+ *lemma* times_cont_diff_on.comp'
- \- *lemma* times_cont_diff_on.has_strict_fderiv_at
- \+ *lemma* times_cont_diff_on.times_cont_diff_within_at
- \- *lemma* times_cont_diff_on_nat
- \+ *lemma* times_cont_diff_within_at.comp'
- \+ *lemma* times_cont_diff_within_at.comp
- \+ *lemma* times_cont_diff_within_at.comp_continuous_linear_map
- \+ *lemma* times_cont_diff_within_at.congr
- \+ *lemma* times_cont_diff_within_at.congr_of_eventually_eq'
- \+ *lemma* times_cont_diff_within_at.congr_of_eventually_eq
- \+ *lemma* times_cont_diff_within_at.continuous_linear_map_comp
- \+ *lemma* times_cont_diff_within_at.continuous_within_at'
- \+ *lemma* times_cont_diff_within_at.continuous_within_at
- \+ *lemma* times_cont_diff_within_at.differentiable_within_at'
- \+ *lemma* times_cont_diff_within_at.differentiable_within_at
- \+ *lemma* times_cont_diff_within_at.mono
- \+ *lemma* times_cont_diff_within_at.of_le
- \+ *lemma* times_cont_diff_within_at.prod
- \+ *lemma* times_cont_diff_within_at.times_cont_diff_at
- \+ *lemma* times_cont_diff_within_at.times_cont_diff_on
- \+ *def* times_cont_diff_within_at
- \+ *lemma* times_cont_diff_within_at_const
- \+ *lemma* times_cont_diff_within_at_inter'
- \+ *lemma* times_cont_diff_within_at_inter
- \+ *lemma* times_cont_diff_within_at_nat
- \+ *theorem* times_cont_diff_within_at_succ_iff_has_fderiv_within_at
- \+ *lemma* times_cont_diff_within_at_top
- \+ *theorem* times_cont_diff_within_at_univ

Modified src/data/set/basic.lean
- \+ *lemma* set.insert_inter

Modified src/topology/continuous_on.lean
- \+ *lemma* mem_nhds_within_insert



## [2020-07-03 09:21:25](https://github.com/leanprover-community/mathlib/commit/53c1531)
feat(geometry/manifold/smooth_manifold_with_corners): product of smooth manifolds with corners ([#3250](https://github.com/leanprover-community/mathlib/pull/3250))
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_on.map_prod
- \+ *lemma* times_cont_diff_on_fst
- \+ *lemma* times_cont_diff_on_snd

Modified src/data/prod.lean
- \+/\- *lemma* prod.map_fst'
- \+/\- *lemma* prod.map_fst
- \+/\- *lemma* prod.map_snd'
- \+/\- *lemma* prod.map_snd
- \+ *lemma* prod_map

Modified src/geometry/manifold/basic_smooth_bundle.lean
- \+/\- *lemma* basic_smooth_bundle_core.mem_atlas_iff

Modified src/geometry/manifold/charted_space.lean
- \+ *def* model_prod
- \+ *lemma* model_prod_range_prod_id
- \+ *lemma* prod_charted_space_chart_at

Modified src/geometry/manifold/mfderiv.lean
- \+/\- *lemma* tangent_map_chart_symm

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* model_with_corners_prod_coe
- \+ *lemma* model_with_corners_prod_coe_symm
- \+ *lemma* model_with_corners_prod_to_local_equiv
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
- \+/\- *lemma* filter.eventually_of_forall

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
- \+/\- *lemma* inv_mul_cancel_left'
- \+/\- *lemma* inv_mul_cancel_right'
- \+/\- *lemma* mul_inv_cancel_left'
- \+/\- *lemma* mul_inv_cancel_right'

Modified src/ring_theory/valuation/basic.lean




## [2020-07-03 04:28:12](https://github.com/leanprover-community/mathlib/commit/303740d)
feat(category_theory/abelian): every abelian category is preadditive  ([#3247](https://github.com/leanprover-community/mathlib/pull/3247))
#### Estimated changes
Modified src/category_theory/abelian/basic.lean
- \+ *def* category_theory.abelian.has_finite_biproducts
- \+ *def* category_theory.non_preadditive_abelian.abelian

Added src/category_theory/abelian/non_preadditive.lean
- \+ *lemma* category_theory.non_preadditive_abelian.add_assoc
- \+ *lemma* category_theory.non_preadditive_abelian.add_comm
- \+ *lemma* category_theory.non_preadditive_abelian.add_comp
- \+ *lemma* category_theory.non_preadditive_abelian.add_def
- \+ *lemma* category_theory.non_preadditive_abelian.add_neg
- \+ *lemma* category_theory.non_preadditive_abelian.add_neg_self
- \+ *lemma* category_theory.non_preadditive_abelian.add_zero
- \+ *lemma* category_theory.non_preadditive_abelian.comp_add
- \+ *lemma* category_theory.non_preadditive_abelian.comp_sub
- \+ *def* category_theory.non_preadditive_abelian.epi_is_cokernel_of_kernel
- \+ *lemma* category_theory.non_preadditive_abelian.epi_of_zero_cancel
- \+ *lemma* category_theory.non_preadditive_abelian.epi_of_zero_cokernel
- \+ *def* category_theory.non_preadditive_abelian.has_add
- \+ *def* category_theory.non_preadditive_abelian.has_colimit_parallel_pair
- \+ *def* category_theory.non_preadditive_abelian.has_limit_parallel_pair
- \+ *def* category_theory.non_preadditive_abelian.has_neg
- \+ *def* category_theory.non_preadditive_abelian.has_sub
- \+ *def* category_theory.non_preadditive_abelian.is_colimit_σ
- \+ *def* category_theory.non_preadditive_abelian.is_iso_of_mono_of_epi
- \+ *lemma* category_theory.non_preadditive_abelian.lift_map
- \+ *lemma* category_theory.non_preadditive_abelian.lift_sub_lift
- \+ *lemma* category_theory.non_preadditive_abelian.lift_σ
- \+ *def* category_theory.non_preadditive_abelian.mono_is_kernel_of_cokernel
- \+ *lemma* category_theory.non_preadditive_abelian.mono_of_cancel_zero
- \+ *lemma* category_theory.non_preadditive_abelian.mono_of_zero_kernel
- \+ *lemma* category_theory.non_preadditive_abelian.neg_add
- \+ *lemma* category_theory.non_preadditive_abelian.neg_add_self
- \+ *lemma* category_theory.non_preadditive_abelian.neg_def
- \+ *lemma* category_theory.non_preadditive_abelian.neg_neg
- \+ *lemma* category_theory.non_preadditive_abelian.neg_sub'
- \+ *lemma* category_theory.non_preadditive_abelian.neg_sub
- \+ *def* category_theory.non_preadditive_abelian.preadditive
- \+ *def* category_theory.non_preadditive_abelian.pullback_of_mono
- \+ *def* category_theory.non_preadditive_abelian.pushout_of_epi
- \+ *abbreviation* category_theory.non_preadditive_abelian.r
- \+ *def* category_theory.non_preadditive_abelian.strong_epi_of_epi
- \+ *lemma* category_theory.non_preadditive_abelian.sub_add
- \+ *lemma* category_theory.non_preadditive_abelian.sub_comp
- \+ *lemma* category_theory.non_preadditive_abelian.sub_def
- \+ *lemma* category_theory.non_preadditive_abelian.sub_self
- \+ *lemma* category_theory.non_preadditive_abelian.sub_sub_sub
- \+ *lemma* category_theory.non_preadditive_abelian.sub_zero
- \+ *def* category_theory.non_preadditive_abelian.zero_cokernel_of_zero_cancel
- \+ *def* category_theory.non_preadditive_abelian.zero_kernel_of_cancel_zero
- \+ *abbreviation* category_theory.non_preadditive_abelian.Δ
- \+ *lemma* category_theory.non_preadditive_abelian.Δ_map
- \+ *lemma* category_theory.non_preadditive_abelian.Δ_σ
- \+ *abbreviation* category_theory.non_preadditive_abelian.σ
- \+ *lemma* category_theory.non_preadditive_abelian.σ_comp

Modified src/category_theory/discrete_category.lean
- \+ *def* category_theory.discrete.nat_iso_functor

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.has_finite_biproducts.of_has_finite_coproducts
- \+ *def* category_theory.limits.has_finite_biproducts.of_has_finite_products

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* category_theory.limits.cokernel_cofork.π_of_π
- \+ *lemma* category_theory.limits.kernel_fork.ι_of_ι



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
- \+ *def* category_theory.limits.fully_faithful_reflects_colimits
- \+ *def* category_theory.limits.fully_faithful_reflects_limits



## [2020-07-02 20:45:17](https://github.com/leanprover-community/mathlib/commit/838dc66)
feat(topology/basic): add `eventually_eventually_nhds` ([#3266](https://github.com/leanprover-community/mathlib/pull/3266))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.bind_inf_principal
- \+ *lemma* filter.bind_le
- \- *lemma* filter.bind_mono2
- \+/\- *lemma* filter.bind_mono
- \- *lemma* filter.bind_sup
- \+ *lemma* filter.eventually_bind
- \+ *lemma* filter.eventually_eq.le
- \+ *lemma* filter.eventually_eq.trans_le
- \+ *lemma* filter.eventually_eq_bind
- \+ *lemma* filter.eventually_le.antisymm
- \+ *lemma* filter.eventually_le.congr
- \+ *lemma* filter.eventually_le.refl
- \+ *lemma* filter.eventually_le.trans
- \+ *lemma* filter.eventually_le.trans_eq
- \+ *def* filter.eventually_le
- \+ *lemma* filter.eventually_le_bind
- \+ *lemma* filter.eventually_le_congr
- \+/\- *lemma* filter.inf_principal_ne_bot_iff
- \+ *lemma* filter.join_le
- \+ *lemma* filter.join_mono
- \+ *lemma* filter.mem_bind_sets'
- \+ *lemma* filter.sup_bind

Modified src/order/filter/germ.lean
- \- *lemma* filter.eventually_eq.le
- \- *lemma* filter.eventually_eq.trans_le
- \- *lemma* filter.eventually_le.antisymm
- \- *lemma* filter.eventually_le.congr
- \- *lemma* filter.eventually_le.refl
- \- *lemma* filter.eventually_le.trans
- \- *lemma* filter.eventually_le.trans_eq
- \- *def* filter.eventually_le
- \- *lemma* filter.eventually_le_congr

Modified src/topology/basic.lean
- \+ *lemma* cluster_pt_principal_iff
- \+ *lemma* eventually_eventually_eq_nhds
- \+ *lemma* eventually_eventually_le_nhds
- \+ *lemma* eventually_eventually_nhds
- \+ *lemma* eventually_nhds_iff
- \+ *lemma* filter.eventually.eventually_nhds
- \+ *lemma* filter.eventually_eq.eventually_eq_nhds
- \+ *lemma* filter.eventually_le.eventually_le_nhds
- \+ *lemma* nhds_bind_nhds

Modified src/topology/continuous_on.lean
- \+ *lemma* eventually_nhds_nhds_within
- \+ *lemma* eventually_nhds_within_iff
- \+ *lemma* eventually_nhds_within_nhds_within
- \+ *lemma* nhds_bind_nhds_within



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
- \+ *lemma* cardinal.mk_Icc_real
- \+ *lemma* cardinal.mk_Ici_real
- \+ *lemma* cardinal.mk_Ico_real
- \+ *lemma* cardinal.mk_Iic_real
- \+ *lemma* cardinal.mk_Iio_real
- \+ *lemma* cardinal.mk_Ioc_real
- \+ *lemma* cardinal.mk_Ioi_real
- \+ *lemma* cardinal.mk_Ioo_real
- \+ *lemma* cardinal.mk_univ_real

Modified src/data/set/intervals/image_preimage.lean
- \+ *lemma* set.image_inv_Ioo_0_left

Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.mk_union_le



## [2020-07-02 18:55:47](https://github.com/leanprover-community/mathlib/commit/e4fdc75)
refactor(analysis/calculus/*deriv): use eventually_eq in congruence statements ([#3261](https://github.com/leanprover-community/mathlib/pull/3261))
Use `eventually_eq` instead of `mem_sets` for congruence lemmas in continuity and differentiability statements.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \- *lemma* deriv_congr_of_mem_nhds
- \- *lemma* deriv_within_congr_of_mem_nhds_within
- \+ *lemma* filter.eventually_eq.deriv_eq
- \+ *lemma* filter.eventually_eq.deriv_within_eq
- \+ *theorem* filter.eventually_eq.has_deriv_at_filter_iff
- \+ *lemma* has_deriv_at.congr_of_eventually_eq
- \- *lemma* has_deriv_at.congr_of_mem_nhds
- \+ *lemma* has_deriv_at_filter.congr_of_eventually_eq
- \- *lemma* has_deriv_at_filter.congr_of_mem_sets
- \- *theorem* has_deriv_at_filter_congr_of_mem_sets
- \+ *lemma* has_deriv_within_at.congr_of_eventually_eq
- \- *lemma* has_deriv_within_at.congr_of_mem_nhds_within

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable_at.congr_of_eventually_eq
- \- *lemma* differentiable_at.congr_of_mem_nhds
- \+ *lemma* differentiable_within_at.comp'
- \+ *lemma* differentiable_within_at.congr_of_eventually_eq
- \- *lemma* differentiable_within_at.congr_of_mem_nhds_within
- \- *lemma* fderiv_congr_of_mem_nhds
- \- *lemma* fderiv_within_congr_of_mem_nhds_within
- \+ *lemma* filter.eventually_eq.fderiv_eq
- \+ *lemma* filter.eventually_eq.fderiv_within_eq
- \+ *theorem* filter.eventually_eq.has_fderiv_at_filter_iff
- \+ *theorem* filter.eventually_eq.has_strict_fderiv_at_iff
- \+ *lemma* has_fderiv_at.congr_of_eventually_eq
- \- *lemma* has_fderiv_at.congr_of_mem_nhds
- \+ *lemma* has_fderiv_at_filter.congr_of_eventually_eq
- \- *lemma* has_fderiv_at_filter.congr_of_mem_sets
- \- *theorem* has_fderiv_at_filter_congr_of_mem_sets
- \+ *lemma* has_fderiv_within_at.congr_of_eventually_eq
- \- *lemma* has_fderiv_within_at.congr_of_mem_nhds_within
- \+ *theorem* has_strict_fderiv_at.congr_of_eventually_eq
- \- *theorem* has_strict_fderiv_at.congr_of_mem_sets
- \- *theorem* has_strict_fderiv_at_congr_of_mem_sets

Modified src/analysis/calculus/inverse.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/special_functions/pow.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/mfderiv.lean
- \+ *lemma* filter.eventually_eq.mdifferentiable_within_at_iff
- \+ *lemma* filter.eventually_eq.mfderiv_eq
- \+ *lemma* filter.eventually_eq.mfderiv_within_eq
- \+ *lemma* has_mfderiv_at.congr_of_eventually_eq
- \- *lemma* has_mfderiv_at.congr_of_mem_nhds
- \+ *lemma* has_mfderiv_within_at.congr_of_eventually_eq
- \- *lemma* has_mfderiv_within_at.congr_of_mem_nhds_within
- \+ *lemma* mdifferentiable_at.congr_of_eventually_eq
- \- *lemma* mdifferentiable_at.congr_of_mem_nhds
- \+ *lemma* mdifferentiable_within_at.congr_of_eventually_eq
- \- *lemma* mdifferentiable_within_at.congr_of_mem_nhds_within
- \- *lemma* mdifferentiable_within_at_congr_of_mem_nhds_within
- \- *lemma* mfderiv_congr_of_mem_nhds
- \- *lemma* mfderiv_within_congr_of_mem_nhds_within

Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually.exists_mem
- \+ *lemma* filter.eventually_eq.exists_mem
- \+ *lemma* filter.eventually_eq_iff_exists_mem
- \+ *lemma* filter.eventually_eq_of_mem
- \+ *lemma* filter.eventually_iff_exists_mem

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.comp'
- \+ *lemma* continuous_within_at.comp'
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
- \+ *lemma* half_le_harmonic_double_sub_harmonic
- \+ *def* harmonic_series
- \+ *theorem* harmonic_tendsto_at_top
- \+ *lemma* mono_harmonic
- \+ *lemma* self_div_two_le_harmonic_two_pow

Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* filter.monotone.tendsto_at_top_finset
- \+/\- *lemma* filter.prod_at_top_at_top_eq
- \+/\- *lemma* filter.prod_map_at_top_eq
- \+ *lemma* filter.tendsto_at_top_at_top_iff_of_monotone
- \+ *lemma* filter.tendsto_at_top_at_top_of_monotone'
- \+/\- *lemma* filter.tendsto_at_top_at_top_of_monotone
- \+/\- *lemma* filter.tendsto_at_top_mono
- \+ *lemma* filter.tendsto_at_top_of_monotone_of_filter
- \+ *lemma* filter.tendsto_at_top_of_monotone_of_subseq
- \+/\- *lemma* filter.tendsto_finset_image_at_top_at_top
- \+ *lemma* filter.unbounded_of_tendsto_at_top

Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.filter_eq_bot_of_not_nonempty
- \+ *lemma* filter.tendsto_bot
- \+/\- *lemma* filter.tendsto_congr'
- \+ *lemma* filter.tendsto_of_not_nonempty

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


Added test/library_search/exp_le_exp.lean




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
- \+ *lemma* finset.prod_range_div'
- \+ *lemma* finset.sum_range_sub'

Modified src/data/polynomial.lean
- \- *lemma* polynomial.C_def
- \+ *theorem* polynomial.coeff_monomial_mul
- \+ *theorem* polynomial.coeff_monomial_zero_mul
- \+ *lemma* polynomial.coeff_mul_C
- \+/\- *theorem* polynomial.coeff_mul_X
- \+ *lemma* polynomial.coeff_mul_X_sub_C
- \+ *theorem* polynomial.coeff_mul_monomial
- \+ *theorem* polynomial.coeff_mul_monomial_zero
- \+ *lemma* polynomial.coeff_nat_degree_succ_eq_zero
- \+ *lemma* polynomial.eq_zero_of_eq_zero
- \+ *lemma* polynomial.eval_monomial
- \+ *lemma* polynomial.eval_mul_X_sub_C
- \+ *lemma* polynomial.eval₂_eq_eval_map
- \+/\- *lemma* polynomial.eval₂_sum
- \+ *lemma* polynomial.map_monomial
- \+ *lemma* polynomial.monomial_add
- \+ *lemma* polynomial.monomial_zero_left
- \+ *lemma* polynomial.monomial_zero_right
- \+ *lemma* polynomial.mul_coeff_zero
- \+ *lemma* polynomial.nat_degree_X_pow_sub_C
- \+ *lemma* polynomial.nat_degree_X_sub_C
- \+ *lemma* polynomial.nat_degree_X_sub_C_le
- \+ *lemma* polynomial.nat_degree_mul_le
- \+ *lemma* polynomial.sum_C_index
- \+ *lemma* polynomial.sum_monomial_eq
- \+ *lemma* polynomial.sum_over_range'
- \+ *lemma* polynomial.sum_over_range



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
- \- *lemma* div_eq_one_iff_eq
- \- *lemma* division_ring.inv_eq_iff
- \- *lemma* division_ring.inv_inj
- \- *lemma* eq_div_iff_mul_eq
- \- *lemma* eq_div_of_mul_eq
- \- *lemma* eq_of_div_eq_one
- \- *lemma* eq_of_one_div_eq_one_div
- \- *lemma* eq_one_div_of_mul_eq_one
- \- *lemma* eq_one_div_of_mul_eq_one_left
- \- *lemma* mul_eq_of_eq_div
- \- *lemma* mul_inv'
- \- *lemma* mul_mul_div
- \- *lemma* one_div_div
- \- *lemma* one_div_one_div
- \- *lemma* ring_hom.injective
- \+/\- *lemma* ring_hom.map_div
- \+/\- *lemma* ring_hom.map_eq_zero
- \+/\- *lemma* ring_hom.map_inv
- \+/\- *lemma* ring_hom.map_ne_zero

Modified src/algebra/gcd_domain.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/group/basic.lean
- \- *theorem* eq_of_inv_eq_inv
- \- *theorem* inv_inj'
- \+ *theorem* inv_inj
- \- *lemma* inv_inj
- \+ *lemma* inv_injective

Modified src/algebra/group/units.lean
- \- *lemma* units.inv_mul'
- \+ *lemma* units.inv_mul_of_eq
- \- *lemma* units.mul_inv'
- \+ *lemma* units.mul_inv_of_eq

Modified src/algebra/group_ring_action.lean


Modified src/algebra/group_with_zero.lean
- \- *lemma* coe_unit_inv_mul'
- \- *lemma* coe_unit_mul_inv'
- \- *lemma* div_div_div_cancel_right'
- \+ *lemma* div_div_div_cancel_right
- \+/\- *lemma* div_eq_mul_inv
- \+ *lemma* div_eq_of_eq_mul
- \+ *lemma* div_eq_one_iff_eq
- \+/\- *lemma* div_eq_zero_iff
- \- *lemma* div_mul_div_cancel'
- \+ *lemma* div_mul_div_cancel
- \- *lemma* div_right_comm'
- \+ *lemma* div_right_comm
- \+ *lemma* eq_div_iff_mul_eq
- \+ *lemma* eq_div_of_mul_eq
- \- *lemma* eq_inv_of_mul_left_eq_one'
- \+ *lemma* eq_inv_of_mul_left_eq_one
- \- *lemma* eq_inv_of_mul_right_eq_one'
- \+ *lemma* eq_inv_of_mul_right_eq_one
- \- *lemma* eq_mul_inv_of_mul_eq'
- \+ *lemma* eq_of_div_eq_one
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_left
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_right
- \- *lemma* eq_of_one_div_eq_one_div'
- \+ *lemma* eq_of_one_div_eq_one_div
- \+ *lemma* eq_of_zero_eq_one
- \- *lemma* eq_one_div_of_mul_eq_one'
- \+ *lemma* eq_one_div_of_mul_eq_one
- \- *lemma* eq_one_div_of_mul_eq_one_left'
- \+ *lemma* eq_one_div_of_mul_eq_one_left
- \+ *theorem* eq_zero_of_mul_eq_self_left
- \+ *theorem* eq_zero_of_mul_eq_self_right
- \+/\- *lemma* eq_zero_of_mul_self_eq_zero
- \+ *lemma* eq_zero_of_zero_eq_one
- \- *lemma* inv_inj''
- \+ *lemma* inv_inj'
- \- *lemma* inv_mul_cancel_assoc_left
- \- *lemma* inv_mul_cancel_assoc_right
- \+ *lemma* inv_mul_cancel_left'
- \+ *lemma* inv_mul_cancel_right'
- \+/\- *lemma* inv_one
- \+ *lemma* is_unit.mul_left_eq_zero
- \+ *lemma* is_unit.mul_right_eq_zero
- \+ *lemma* is_unit.ne_zero
- \+ *theorem* is_unit_zero_iff
- \+ *lemma* left_ne_zero_of_mul
- \+ *lemma* left_ne_zero_of_mul_eq_one
- \+ *lemma* monoid_hom.map_div
- \+ *lemma* monoid_hom.map_eq_zero
- \+ *lemma* monoid_hom.map_inv'
- \+ *lemma* monoid_hom.map_ne_zero
- \+ *lemma* mul_eq_zero_of_left
- \+ *lemma* mul_eq_zero_of_right
- \- *lemma* mul_inv''
- \+ *lemma* mul_inv'
- \- *lemma* mul_inv_cancel_assoc_left
- \- *lemma* mul_inv_cancel_assoc_right
- \+ *lemma* mul_inv_cancel_left'
- \+ *lemma* mul_inv_cancel_right'
- \- *lemma* mul_inv_eq_of_eq_mul'
- \+/\- *lemma* mul_left_cancel'
- \+/\- *lemma* mul_left_inj'
- \+ *lemma* mul_mul_div
- \+/\- *lemma* mul_right_cancel'
- \+ *lemma* mul_right_inj'
- \+/\- *lemma* mul_zero
- \+ *lemma* ne_zero_and_ne_zero_of_mul
- \+ *lemma* ne_zero_of_eq_one
- \- *lemma* ne_zero_of_mul_left_eq_one'
- \- *lemma* ne_zero_of_mul_right_eq_one'
- \+ *theorem* not_is_unit_zero
- \- *lemma* one_div_div'
- \+ *lemma* one_div_div
- \- *lemma* one_div_one_div'
- \+ *lemma* one_div_one_div
- \- *lemma* one_inv_eq
- \+/\- *lemma* one_ne_zero
- \+ *lemma* right_ne_zero_of_mul
- \+ *lemma* right_ne_zero_of_mul_eq_one
- \+ *theorem* subsingleton_of_zero_eq_one
- \+ *def* unique_of_zero_eq_one
- \- *lemma* unit_ne_zero
- \+ *lemma* units.coe_inv'
- \+/\- *lemma* units.exists_iff_ne_zero
- \- *theorem* units.inv_eq_inv
- \+ *lemma* units.inv_mul'
- \+ *lemma* units.mul_inv'
- \+ *lemma* units.mul_left_eq_zero
- \+ *lemma* units.mul_right_eq_zero
- \+ *lemma* units.ne_zero
- \+/\- *lemma* zero_mul
- \+/\- *lemma* zero_ne_one
- \+ *lemma* zero_ne_one_or_forall_eq_0

Modified src/algebra/group_with_zero_power.lean


Modified src/algebra/linear_ordered_comm_group_with_zero.lean
- \+ *lemma* units.zero_lt
- \- *lemma* zero_lt_unit

Modified src/algebra/ordered_field.lean


Modified src/algebra/quadratic_discriminant.lean


Modified src/algebra/ring.lean
- \- *theorem* domain.mul_left_inj
- \- *theorem* domain.mul_right_inj
- \- *lemma* eq_of_mul_eq_mul_left
- \- *theorem* eq_of_mul_eq_mul_left_of_ne_zero
- \- *lemma* eq_of_mul_eq_mul_right
- \- *theorem* eq_of_mul_eq_mul_right_of_ne_zero
- \- *theorem* eq_zero_of_mul_eq_self_left
- \- *theorem* eq_zero_of_mul_eq_self_right
- \- *lemma* eq_zero_of_zero_eq_one
- \- *theorem* is_unit.mul_left_eq_zero_iff_eq_zero
- \- *theorem* is_unit.mul_right_eq_zero_iff_eq_zero
- \+/\- *lemma* mul_self_eq_mul_self_iff
- \+/\- *lemma* mul_self_eq_one_iff
- \- *theorem* ne_zero_and_ne_zero_of_mul_ne_zero
- \- *lemma* ne_zero_of_mul_ne_zero_left
- \- *lemma* ne_zero_of_mul_ne_zero_right
- \- *lemma* ring.mul_zero
- \- *lemma* ring.zero_mul
- \- *theorem* subsingleton_of_zero_eq_one
- \- *theorem* units.mul_left_eq_zero_iff_eq_zero
- \- *theorem* units.mul_right_eq_zero_iff_eq_zero
- \- *lemma* zero_ne_one_or_forall_eq_0

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
- \+/\- *theorem* norm_num.inv_one

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
- \- *lemma* is_ring_hom.map_fpow

Modified src/algebra/pointwise.lean
- \- *lemma* set.pointwise_mul_image_is_semiring_hom
- \+ *def* set.pointwise_mul_image_ring_hom

Modified src/algebra/punit_instances.lean


Modified src/category_theory/conj.lean


Modified src/data/complex/basic.lean
- \+/\- *def* complex.conj
- \- *lemma* complex.conj_add
- \- *lemma* complex.conj_div
- \- *lemma* complex.conj_inv
- \- *lemma* complex.conj_mul
- \- *lemma* complex.conj_neg
- \- *lemma* complex.conj_one
- \- *lemma* complex.conj_pow
- \- *lemma* complex.conj_sub
- \- *lemma* complex.conj_zero

Modified src/data/complex/exponential.lean


Modified src/data/complex/module.lean


Modified src/data/equiv/ring.lean


Modified src/data/finsupp.lean
- \+ *def* finsupp.map_range.add_monoid_hom

Modified src/data/padics/padic_integers.lean
- \+ *def* padic_int.coe.ring_hom

Modified src/data/padics/padic_norm.lean


Modified src/data/pnat/factors.lean


Modified src/data/polynomial.lean


Modified src/data/zsqrtd/gaussian_int.lean
- \+/\- *def* gaussian_int.to_complex
- \+/\- *lemma* gaussian_int.to_complex_add
- \+/\- *lemma* gaussian_int.to_complex_mul
- \+/\- *lemma* gaussian_int.to_complex_neg
- \+/\- *lemma* gaussian_int.to_complex_one
- \+/\- *lemma* gaussian_int.to_complex_sub
- \+/\- *lemma* gaussian_int.to_complex_zero

Deleted src/deprecated/field.lean
- \- *lemma* is_ring_hom.injective
- \- *lemma* is_ring_hom.map_div
- \- *lemma* is_ring_hom.map_eq_zero
- \- *lemma* is_ring_hom.map_inv
- \- *lemma* is_ring_hom.map_ne_zero

Modified src/field_theory/minimal_polynomial.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean
- \+/\- *def* equiv.perm.of_subtype
- \- *lemma* equiv.perm.of_subtype_one

Modified src/ring_theory/algebra_operations.lean
- \+ *def* submodule.span.ring_hom

Modified src/ring_theory/power_series.lean
- \+ *def* mv_polynomial.coe_to_mv_power_series.ring_hom
- \+ *def* polynomial.coe_to_power_series.ring_hom

Modified src/ring_theory/subring.lean




## [2020-07-01 12:12:44](https://github.com/leanprover-community/mathlib/commit/e803c85)
feat(field_theory/separable): relating irreducibility and separability ([#3198](https://github.com/leanprover-community/mathlib/pull/3198))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *theorem* polynomial.degree_derivative_le
- \+ *theorem* polynomial.degree_derivative_lt
- \+ *theorem* polynomial.derivative_eval₂_C
- \+ *theorem* polynomial.derivative_map
- \+ *theorem* polynomial.derivative_pow
- \+ *theorem* polynomial.derivative_pow_succ
- \+ *lemma* polynomial.eval₂_nat_cast
- \+ *theorem* polynomial.is_unit_iff
- \+ *theorem* polynomial.map_nat_cast
- \+ *theorem* polynomial.nat_degree_derivative_lt
- \+ *theorem* polynomial.nat_degree_le_of_dvd
- \+ *theorem* polynomial.of_mem_support_derivative

Modified src/field_theory/separable.lean
- \+ *theorem* irreducible.separable
- \+ *lemma* polynomial.coe_expand
- \+ *theorem* polynomial.coeff_contract
- \+ *theorem* polynomial.coeff_expand
- \+ *theorem* polynomial.coeff_expand_mul'
- \+ *theorem* polynomial.coeff_expand_mul
- \+ *theorem* polynomial.derivative_expand
- \+ *theorem* polynomial.exists_separable_of_irreducible
- \+ *lemma* polynomial.expand_C
- \+ *lemma* polynomial.expand_X
- \+ *theorem* polynomial.expand_contract
- \+ *theorem* polynomial.expand_eq_C
- \+ *theorem* polynomial.expand_eq_map_domain
- \+ *theorem* polynomial.expand_eq_zero
- \+ *theorem* polynomial.expand_expand
- \+ *theorem* polynomial.expand_inj
- \+ *lemma* polynomial.expand_monomial
- \+ *theorem* polynomial.expand_mul
- \+ *theorem* polynomial.expand_one
- \+ *theorem* polynomial.expand_pow
- \+ *theorem* polynomial.is_local_ring_hom_expand
- \+ *theorem* polynomial.is_unit_or_eq_zero_of_separable_expand
- \+ *theorem* polynomial.nat_degree_expand
- \+ *theorem* polynomial.of_irreducible_expand
- \+ *theorem* polynomial.of_irreducible_expand_pow
- \+ *lemma* polynomial.separable.is_coprime
- \+ *theorem* polynomial.separable.map
- \+ *theorem* polynomial.separable.of_pow'
- \+ *theorem* polynomial.separable.of_pow
- \+ *lemma* polynomial.separable_C
- \+ *theorem* polynomial.separable_iff_derivative_ne_zero
- \+ *theorem* polynomial.separable_or
- \+ *theorem* polynomial.unique_separable_of_irreducible

Modified src/ring_theory/algebra.lean
- \+ *lemma* alg_hom.map_nat_cast

Modified src/ring_theory/ideals.lean
- \+ *theorem* of_irreducible_map

Modified src/ring_theory/polynomial/basic.lean




## [2020-07-01 10:05:14](https://github.com/leanprover-community/mathlib/commit/a7cdab5)
chore(data/set/basic): simp attribute on mem_range_self ([#3260](https://github.com/leanprover-community/mathlib/pull/3260))
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *theorem* set.mem_range_self



## [2020-07-01 10:05:12](https://github.com/leanprover-community/mathlib/commit/7bd19b3)
chore(data/finset, data/multiset): split into smaller files ([#3256](https://github.com/leanprover-community/mathlib/pull/3256))
This follows on from [#2341](https://github.com/leanprover-community/mathlib/pull/2341), which split the second half of `data.list.basic` into separate files. This now does the same (trying to follow a similar split) for `data.multiset` and `data.finset`.
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/algebra/big_operators.lean


Modified src/control/equiv_functor/instances.lean


Modified src/data/finmap.lean


Renamed src/data/finset.lean to src/data/finset/basic.lean
- \- *theorem* finset.Ico.card
- \- *lemma* finset.Ico.diff_left
- \- *lemma* finset.Ico.diff_right
- \- *lemma* finset.Ico.disjoint_consecutive
- \- *theorem* finset.Ico.eq_empty_iff
- \- *theorem* finset.Ico.eq_empty_of_le
- \- *lemma* finset.Ico.filter_le
- \- *lemma* finset.Ico.filter_le_of_le
- \- *lemma* finset.Ico.filter_le_of_le_bot
- \- *lemma* finset.Ico.filter_le_of_top_le
- \- *lemma* finset.Ico.filter_lt
- \- *lemma* finset.Ico.filter_lt_of_ge
- \- *lemma* finset.Ico.filter_lt_of_le_bot
- \- *lemma* finset.Ico.filter_lt_of_top_le
- \- *theorem* finset.Ico.image_add
- \- *lemma* finset.Ico.image_const_sub
- \- *theorem* finset.Ico.image_sub
- \- *theorem* finset.Ico.insert_succ_bot
- \- *lemma* finset.Ico.inter_consecutive
- \- *theorem* finset.Ico.mem
- \- *theorem* finset.Ico.not_mem_top
- \- *theorem* finset.Ico.pred_singleton
- \- *theorem* finset.Ico.self_eq_empty
- \- *theorem* finset.Ico.subset_iff
- \- *theorem* finset.Ico.succ_singleton
- \- *theorem* finset.Ico.succ_top'
- \- *theorem* finset.Ico.succ_top
- \- *theorem* finset.Ico.to_finset
- \- *lemma* finset.Ico.union_consecutive
- \- *theorem* finset.Ico.val
- \- *theorem* finset.Ico.zero_bot
- \- *def* finset.Ico
- \- *lemma* finset.Ico_ℤ.card
- \- *lemma* finset.Ico_ℤ.mem
- \- *def* finset.Ico_ℤ
- \- *theorem* finset.bInter_coe
- \- *lemma* finset.bInter_finset_image
- \- *lemma* finset.bInter_insert
- \- *lemma* finset.bInter_inter
- \- *theorem* finset.bInter_singleton
- \- *theorem* finset.bUnion_coe
- \- *lemma* finset.bUnion_finset_image
- \- *lemma* finset.bUnion_insert
- \- *theorem* finset.bUnion_singleton
- \- *lemma* finset.bUnion_union
- \- *theorem* finset.card_powerset
- \- *theorem* finset.card_powerset_len
- \- *lemma* finset.comp_inf_eq_inf_comp
- \- *lemma* finset.comp_inf_eq_inf_comp_of_is_total
- \- *lemma* finset.comp_sup_eq_sup_comp
- \- *lemma* finset.comp_sup_eq_sup_comp_of_is_total
- \- *theorem* finset.empty_mem_powerset
- \- *lemma* finset.exists_max_image
- \- *lemma* finset.exists_min_image
- \- *theorem* finset.exists_nat_subset_range
- \- *def* finset.fold
- \- *theorem* finset.fold_congr
- \- *theorem* finset.fold_empty
- \- *theorem* finset.fold_hom
- \- *theorem* finset.fold_image
- \- *theorem* finset.fold_insert
- \- *theorem* finset.fold_insert_idem
- \- *theorem* finset.fold_map
- \- *lemma* finset.fold_max_le
- \- *lemma* finset.fold_max_lt
- \- *lemma* finset.fold_min_le
- \- *lemma* finset.fold_min_lt
- \- *theorem* finset.fold_op_distrib
- \- *lemma* finset.fold_op_rel_iff_and
- \- *lemma* finset.fold_op_rel_iff_or
- \- *theorem* finset.fold_singleton
- \- *theorem* finset.fold_union_inter
- \- *def* finset.inf
- \- *theorem* finset.inf_congr
- \- *lemma* finset.inf_empty
- \- *lemma* finset.inf_eq_infi
- \- *lemma* finset.inf_insert
- \- *lemma* finset.inf_le
- \- *lemma* finset.inf_mono
- \- *lemma* finset.inf_mono_fun
- \- *lemma* finset.inf_singleton
- \- *lemma* finset.inf_union
- \- *lemma* finset.inf_val
- \- *lemma* finset.infi_coe
- \- *lemma* finset.infi_finset_image
- \- *lemma* finset.infi_insert
- \- *theorem* finset.infi_singleton
- \- *theorem* finset.infi_union
- \- *lemma* finset.le_fold_max
- \- *lemma* finset.le_fold_min
- \- *lemma* finset.le_inf
- \- *lemma* finset.le_inf_iff
- \- *theorem* finset.le_max'
- \- *theorem* finset.le_max_of_mem
- \- *theorem* finset.le_min'
- \- *lemma* finset.le_sup
- \- *theorem* finset.length_sort
- \- *lemma* finset.lt_fold_max
- \- *lemma* finset.lt_fold_min
- \- *lemma* finset.lt_inf_iff
- \- *def* finset.max'
- \- *theorem* finset.max'_le
- \- *theorem* finset.max'_mem
- \- *theorem* finset.max_empty
- \- *theorem* finset.max_eq_none
- \- *theorem* finset.max_eq_sup_with_bot
- \- *theorem* finset.max_insert
- \- *theorem* finset.max_of_mem
- \- *theorem* finset.max_of_nonempty
- \- *theorem* finset.max_singleton
- \- *theorem* finset.mem_of_max
- \- *theorem* finset.mem_of_min
- \- *lemma* finset.mem_pi
- \- *theorem* finset.mem_powerset
- \- *theorem* finset.mem_powerset_len
- \- *theorem* finset.mem_powerset_self
- \- *theorem* finset.mem_sort
- \- *def* finset.min'
- \- *theorem* finset.min'_le
- \- *theorem* finset.min'_lt_max'
- \- *lemma* finset.min'_lt_max'_of_card
- \- *theorem* finset.min'_mem
- \- *theorem* finset.min_empty
- \- *theorem* finset.min_eq_inf_with_top
- \- *theorem* finset.min_eq_none
- \- *theorem* finset.min_insert
- \- *theorem* finset.min_le_of_mem
- \- *theorem* finset.min_of_mem
- \- *theorem* finset.min_of_nonempty
- \- *theorem* finset.min_singleton
- \- *def* finset.mono_of_fin
- \- *lemma* finset.mono_of_fin_bij_on
- \- *lemma* finset.mono_of_fin_eq_mono_of_fin_iff
- \- *lemma* finset.mono_of_fin_injective
- \- *lemma* finset.mono_of_fin_last
- \- *lemma* finset.mono_of_fin_strict_mono
- \- *lemma* finset.mono_of_fin_unique
- \- *lemma* finset.mono_of_fin_zero
- \- *def* finset.nat.antidiagonal
- \- *lemma* finset.nat.antidiagonal_zero
- \- *lemma* finset.nat.card_antidiagonal
- \- *lemma* finset.nat.mem_antidiagonal
- \- *lemma* finset.not_mem_of_mem_powerset_of_not_mem
- \- *def* finset.pi.cons
- \- *lemma* finset.pi.cons_ne
- \- *lemma* finset.pi.cons_same
- \- *def* finset.pi.empty
- \- *def* finset.pi
- \- *lemma* finset.pi_cons_injective
- \- *lemma* finset.pi_disjoint_of_disjoint
- \- *lemma* finset.pi_empty
- \- *lemma* finset.pi_insert
- \- *lemma* finset.pi_subset
- \- *lemma* finset.pi_val
- \- *def* finset.powerset
- \- *lemma* finset.powerset_empty
- \- *lemma* finset.powerset_insert
- \- *def* finset.powerset_len
- \- *theorem* finset.powerset_len_mono
- \- *theorem* finset.powerset_mono
- \- *lemma* finset.range_eq_Ico
- \- *lemma* finset.range_image_pred_top_sub
- \- *def* finset.sort
- \- *theorem* finset.sort_eq
- \- *theorem* finset.sort_nodup
- \- *theorem* finset.sort_sorted
- \- *theorem* finset.sort_sorted_lt
- \- *theorem* finset.sort_to_finset
- \- *lemma* finset.sorted_last_eq_max'
- \- *lemma* finset.sorted_zero_eq_min'
- \- *theorem* finset.subset_range_sup_succ
- \- *def* finset.sup
- \- *theorem* finset.sup_congr
- \- *lemma* finset.sup_def
- \- *lemma* finset.sup_empty
- \- *lemma* finset.sup_eq_supr
- \- *lemma* finset.sup_insert
- \- *lemma* finset.sup_le
- \- *lemma* finset.sup_le_iff
- \- *lemma* finset.sup_lt_iff
- \- *lemma* finset.sup_mono
- \- *lemma* finset.sup_mono_fun
- \- *lemma* finset.sup_singleton
- \- *lemma* finset.sup_union
- \- *lemma* finset.supr_coe
- \- *lemma* finset.supr_finset_image
- \- *lemma* finset.supr_insert
- \- *theorem* finset.supr_singleton
- \- *theorem* finset.supr_union
- \- *lemma* infi_eq_infi_finset
- \- *lemma* multiset.count_sup
- \- *lemma* set.Inter_eq_Inter_finset
- \- *lemma* set.Union_eq_Union_finset
- \- *lemma* supr_eq_supr_finset

Added src/data/finset/default.lean


Added src/data/finset/fold.lean
- \+ *def* finset.fold
- \+ *theorem* finset.fold_congr
- \+ *theorem* finset.fold_empty
- \+ *theorem* finset.fold_hom
- \+ *theorem* finset.fold_image
- \+ *theorem* finset.fold_insert
- \+ *theorem* finset.fold_insert_idem
- \+ *theorem* finset.fold_map
- \+ *lemma* finset.fold_max_le
- \+ *lemma* finset.fold_max_lt
- \+ *lemma* finset.fold_min_le
- \+ *lemma* finset.fold_min_lt
- \+ *theorem* finset.fold_op_distrib
- \+ *lemma* finset.fold_op_rel_iff_and
- \+ *lemma* finset.fold_op_rel_iff_or
- \+ *theorem* finset.fold_singleton
- \+ *theorem* finset.fold_union_inter
- \+ *lemma* finset.le_fold_max
- \+ *lemma* finset.le_fold_min
- \+ *lemma* finset.lt_fold_max
- \+ *lemma* finset.lt_fold_min

Added src/data/finset/intervals.lean
- \+ *theorem* finset.Ico.card
- \+ *lemma* finset.Ico.diff_left
- \+ *lemma* finset.Ico.diff_right
- \+ *lemma* finset.Ico.disjoint_consecutive
- \+ *theorem* finset.Ico.eq_empty_iff
- \+ *theorem* finset.Ico.eq_empty_of_le
- \+ *lemma* finset.Ico.filter_le
- \+ *lemma* finset.Ico.filter_le_of_le
- \+ *lemma* finset.Ico.filter_le_of_le_bot
- \+ *lemma* finset.Ico.filter_le_of_top_le
- \+ *lemma* finset.Ico.filter_lt
- \+ *lemma* finset.Ico.filter_lt_of_ge
- \+ *lemma* finset.Ico.filter_lt_of_le_bot
- \+ *lemma* finset.Ico.filter_lt_of_top_le
- \+ *theorem* finset.Ico.image_add
- \+ *lemma* finset.Ico.image_const_sub
- \+ *theorem* finset.Ico.image_sub
- \+ *theorem* finset.Ico.insert_succ_bot
- \+ *lemma* finset.Ico.inter_consecutive
- \+ *theorem* finset.Ico.mem
- \+ *theorem* finset.Ico.not_mem_top
- \+ *theorem* finset.Ico.pred_singleton
- \+ *theorem* finset.Ico.self_eq_empty
- \+ *theorem* finset.Ico.subset_iff
- \+ *theorem* finset.Ico.succ_singleton
- \+ *theorem* finset.Ico.succ_top'
- \+ *theorem* finset.Ico.succ_top
- \+ *theorem* finset.Ico.to_finset
- \+ *lemma* finset.Ico.union_consecutive
- \+ *theorem* finset.Ico.val
- \+ *theorem* finset.Ico.zero_bot
- \+ *def* finset.Ico
- \+ *lemma* finset.Ico_ℤ.card
- \+ *lemma* finset.Ico_ℤ.mem
- \+ *def* finset.Ico_ℤ
- \+ *lemma* finset.range_eq_Ico
- \+ *lemma* finset.range_image_pred_top_sub

Added src/data/finset/lattice.lean
- \+ *theorem* finset.bInter_coe
- \+ *lemma* finset.bInter_finset_image
- \+ *lemma* finset.bInter_insert
- \+ *lemma* finset.bInter_inter
- \+ *theorem* finset.bInter_singleton
- \+ *theorem* finset.bUnion_coe
- \+ *lemma* finset.bUnion_finset_image
- \+ *lemma* finset.bUnion_insert
- \+ *theorem* finset.bUnion_singleton
- \+ *lemma* finset.bUnion_union
- \+ *lemma* finset.comp_inf_eq_inf_comp
- \+ *lemma* finset.comp_inf_eq_inf_comp_of_is_total
- \+ *lemma* finset.comp_sup_eq_sup_comp
- \+ *lemma* finset.comp_sup_eq_sup_comp_of_is_total
- \+ *lemma* finset.exists_max_image
- \+ *lemma* finset.exists_min_image
- \+ *theorem* finset.exists_nat_subset_range
- \+ *def* finset.inf
- \+ *theorem* finset.inf_congr
- \+ *lemma* finset.inf_empty
- \+ *lemma* finset.inf_eq_infi
- \+ *lemma* finset.inf_insert
- \+ *lemma* finset.inf_le
- \+ *lemma* finset.inf_mono
- \+ *lemma* finset.inf_mono_fun
- \+ *lemma* finset.inf_singleton
- \+ *lemma* finset.inf_union
- \+ *lemma* finset.inf_val
- \+ *lemma* finset.infi_coe
- \+ *lemma* finset.infi_finset_image
- \+ *lemma* finset.infi_insert
- \+ *theorem* finset.infi_singleton
- \+ *theorem* finset.infi_union
- \+ *lemma* finset.le_inf
- \+ *lemma* finset.le_inf_iff
- \+ *theorem* finset.le_max'
- \+ *theorem* finset.le_max_of_mem
- \+ *theorem* finset.le_min'
- \+ *lemma* finset.le_sup
- \+ *lemma* finset.lt_inf_iff
- \+ *def* finset.max'
- \+ *theorem* finset.max'_le
- \+ *theorem* finset.max'_mem
- \+ *theorem* finset.max_empty
- \+ *theorem* finset.max_eq_none
- \+ *theorem* finset.max_eq_sup_with_bot
- \+ *theorem* finset.max_insert
- \+ *theorem* finset.max_of_mem
- \+ *theorem* finset.max_of_nonempty
- \+ *theorem* finset.max_singleton
- \+ *theorem* finset.mem_of_max
- \+ *theorem* finset.mem_of_min
- \+ *def* finset.min'
- \+ *theorem* finset.min'_le
- \+ *theorem* finset.min'_lt_max'
- \+ *lemma* finset.min'_lt_max'_of_card
- \+ *theorem* finset.min'_mem
- \+ *theorem* finset.min_empty
- \+ *theorem* finset.min_eq_inf_with_top
- \+ *theorem* finset.min_eq_none
- \+ *theorem* finset.min_insert
- \+ *theorem* finset.min_le_of_mem
- \+ *theorem* finset.min_of_mem
- \+ *theorem* finset.min_of_nonempty
- \+ *theorem* finset.min_singleton
- \+ *theorem* finset.subset_range_sup_succ
- \+ *def* finset.sup
- \+ *theorem* finset.sup_congr
- \+ *lemma* finset.sup_def
- \+ *lemma* finset.sup_empty
- \+ *lemma* finset.sup_eq_supr
- \+ *lemma* finset.sup_insert
- \+ *lemma* finset.sup_le
- \+ *lemma* finset.sup_le_iff
- \+ *lemma* finset.sup_lt_iff
- \+ *lemma* finset.sup_mono
- \+ *lemma* finset.sup_mono_fun
- \+ *lemma* finset.sup_singleton
- \+ *lemma* finset.sup_union
- \+ *lemma* finset.supr_coe
- \+ *lemma* finset.supr_finset_image
- \+ *lemma* finset.supr_insert
- \+ *theorem* finset.supr_singleton
- \+ *theorem* finset.supr_union
- \+ *lemma* infi_eq_infi_finset
- \+ *lemma* multiset.count_sup
- \+ *lemma* set.Inter_eq_Inter_finset
- \+ *lemma* set.Union_eq_Union_finset
- \+ *lemma* supr_eq_supr_finset

Added src/data/finset/nat_antidiagonal.lean
- \+ *def* finset.nat.antidiagonal
- \+ *lemma* finset.nat.antidiagonal_zero
- \+ *lemma* finset.nat.card_antidiagonal
- \+ *lemma* finset.nat.mem_antidiagonal

Added src/data/finset/pi.lean
- \+ *lemma* finset.mem_pi
- \+ *def* finset.pi.cons
- \+ *lemma* finset.pi.cons_ne
- \+ *lemma* finset.pi.cons_same
- \+ *def* finset.pi.empty
- \+ *def* finset.pi
- \+ *lemma* finset.pi_cons_injective
- \+ *lemma* finset.pi_disjoint_of_disjoint
- \+ *lemma* finset.pi_empty
- \+ *lemma* finset.pi_insert
- \+ *lemma* finset.pi_subset
- \+ *lemma* finset.pi_val

Added src/data/finset/powerset.lean
- \+ *theorem* finset.card_powerset
- \+ *theorem* finset.card_powerset_len
- \+ *theorem* finset.empty_mem_powerset
- \+ *theorem* finset.mem_powerset
- \+ *theorem* finset.mem_powerset_len
- \+ *theorem* finset.mem_powerset_self
- \+ *lemma* finset.not_mem_of_mem_powerset_of_not_mem
- \+ *def* finset.powerset
- \+ *lemma* finset.powerset_empty
- \+ *lemma* finset.powerset_insert
- \+ *def* finset.powerset_len
- \+ *theorem* finset.powerset_len_mono
- \+ *theorem* finset.powerset_mono

Added src/data/finset/sort.lean
- \+ *theorem* finset.length_sort
- \+ *theorem* finset.mem_sort
- \+ *def* finset.mono_of_fin
- \+ *lemma* finset.mono_of_fin_bij_on
- \+ *lemma* finset.mono_of_fin_eq_mono_of_fin_iff
- \+ *lemma* finset.mono_of_fin_injective
- \+ *lemma* finset.mono_of_fin_last
- \+ *lemma* finset.mono_of_fin_strict_mono
- \+ *lemma* finset.mono_of_fin_unique
- \+ *lemma* finset.mono_of_fin_zero
- \+ *def* finset.sort
- \+ *theorem* finset.sort_eq
- \+ *theorem* finset.sort_nodup
- \+ *theorem* finset.sort_sorted
- \+ *theorem* finset.sort_sorted_lt
- \+ *theorem* finset.sort_to_finset
- \+ *lemma* finset.sorted_last_eq_max'
- \+ *lemma* finset.sorted_zero_eq_min'

Modified src/data/finsupp.lean


Modified src/data/fintype/basic.lean


Modified src/data/list/default.lean


Renamed src/data/list/antidiagonal.lean to src/data/list/nat_antidiagonal.lean


Added src/data/multiset/antidiagonal.lean
- \+ *def* multiset.antidiagonal
- \+ *theorem* multiset.antidiagonal_coe'
- \+ *theorem* multiset.antidiagonal_coe
- \+ *theorem* multiset.antidiagonal_cons
- \+ *theorem* multiset.antidiagonal_map_fst
- \+ *theorem* multiset.antidiagonal_map_snd
- \+ *theorem* multiset.antidiagonal_zero
- \+ *theorem* multiset.card_antidiagonal
- \+ *theorem* multiset.mem_antidiagonal
- \+ *lemma* multiset.prod_map_add

Renamed src/data/multiset.lean to src/data/multiset/basic.lean
- \- *lemma* multiset.Ico.add_consecutive
- \- *theorem* multiset.Ico.card
- \- *theorem* multiset.Ico.eq_cons
- \- *theorem* multiset.Ico.eq_zero_iff
- \- *theorem* multiset.Ico.eq_zero_of_le
- \- *lemma* multiset.Ico.filter_le
- \- *lemma* multiset.Ico.filter_le_of_le
- \- *lemma* multiset.Ico.filter_le_of_le_bot
- \- *lemma* multiset.Ico.filter_le_of_top_le
- \- *lemma* multiset.Ico.filter_lt
- \- *lemma* multiset.Ico.filter_lt_of_ge
- \- *lemma* multiset.Ico.filter_lt_of_le_bot
- \- *lemma* multiset.Ico.filter_lt_of_top_le
- \- *lemma* multiset.Ico.inter_consecutive
- \- *theorem* multiset.Ico.map_add
- \- *theorem* multiset.Ico.map_sub
- \- *theorem* multiset.Ico.mem
- \- *theorem* multiset.Ico.nodup
- \- *theorem* multiset.Ico.not_mem_top
- \- *theorem* multiset.Ico.pred_singleton
- \- *theorem* multiset.Ico.self_eq_zero
- \- *theorem* multiset.Ico.succ_singleton
- \- *theorem* multiset.Ico.succ_top
- \- *theorem* multiset.Ico.zero_bot
- \- *def* multiset.Ico
- \- *def* multiset.antidiagonal
- \- *theorem* multiset.antidiagonal_coe'
- \- *theorem* multiset.antidiagonal_coe
- \- *theorem* multiset.antidiagonal_cons
- \- *theorem* multiset.antidiagonal_map_fst
- \- *theorem* multiset.antidiagonal_map_snd
- \- *theorem* multiset.antidiagonal_zero
- \- *lemma* multiset.attach_ndinsert
- \- *lemma* multiset.bind_def
- \- *theorem* multiset.card_antidiagonal
- \- *lemma* multiset.card_pi
- \- *theorem* multiset.card_powerset
- \- *theorem* multiset.card_powerset_len
- \- *lemma* multiset.card_sections
- \- *theorem* multiset.coe_erase_dup
- \- *theorem* multiset.coe_fold_l
- \- *theorem* multiset.coe_fold_r
- \- *theorem* multiset.coe_ndinsert
- \- *theorem* multiset.coe_ndinter
- \- *theorem* multiset.coe_ndunion
- \- *theorem* multiset.coe_nodup
- \- *lemma* multiset.coe_sections
- \- *theorem* multiset.coe_sort
- \- *lemma* multiset.comp_traverse
- \- *theorem* multiset.cons_ndinter_of_mem
- \- *theorem* multiset.cons_ndunion
- \- *theorem* multiset.count_eq_one_of_mem
- \- *theorem* multiset.disjoint_ndinsert_left
- \- *theorem* multiset.disjoint_ndinsert_right
- \- *theorem* multiset.disjoint_of_nodup_add
- \- *def* multiset.erase_dup
- \- *theorem* multiset.erase_dup_add
- \- *theorem* multiset.erase_dup_cons
- \- *theorem* multiset.erase_dup_cons_of_mem
- \- *theorem* multiset.erase_dup_cons_of_not_mem
- \- *theorem* multiset.erase_dup_eq_self
- \- *theorem* multiset.erase_dup_eq_zero
- \- *theorem* multiset.erase_dup_ext
- \- *theorem* multiset.erase_dup_le
- \- *theorem* multiset.erase_dup_map_erase_dup_eq
- \- *theorem* multiset.erase_dup_singleton
- \- *theorem* multiset.erase_dup_subset'
- \- *theorem* multiset.erase_dup_subset
- \- *theorem* multiset.erase_dup_zero
- \- *lemma* multiset.fmap_def
- \- *def* multiset.fold
- \- *theorem* multiset.fold_add
- \- *theorem* multiset.fold_cons'_left
- \- *theorem* multiset.fold_cons'_right
- \- *theorem* multiset.fold_cons_left
- \- *theorem* multiset.fold_cons_right
- \- *theorem* multiset.fold_distrib
- \- *theorem* multiset.fold_eq_foldl
- \- *theorem* multiset.fold_eq_foldr
- \- *theorem* multiset.fold_erase_dup_idem
- \- *theorem* multiset.fold_hom
- \- *theorem* multiset.fold_singleton
- \- *theorem* multiset.fold_union_inter
- \- *theorem* multiset.fold_zero
- \- *lemma* multiset.forall_of_pairwise
- \- *lemma* multiset.id_traverse
- \- *def* multiset.inf
- \- *lemma* multiset.inf_add
- \- *lemma* multiset.inf_cons
- \- *lemma* multiset.inf_erase_dup
- \- *lemma* multiset.inf_le
- \- *lemma* multiset.inf_mono
- \- *lemma* multiset.inf_ndinsert
- \- *lemma* multiset.inf_ndunion
- \- *lemma* multiset.inf_singleton
- \- *lemma* multiset.inf_union
- \- *lemma* multiset.inf_zero
- \- *theorem* multiset.inter_le_ndinter
- \- *theorem* multiset.le_erase_dup
- \- *theorem* multiset.le_iff_subset
- \- *lemma* multiset.le_inf
- \- *theorem* multiset.le_ndinsert_self
- \- *theorem* multiset.le_ndinter
- \- *theorem* multiset.le_ndunion_left
- \- *theorem* multiset.le_ndunion_right
- \- *theorem* multiset.le_smul_erase_dup
- \- *lemma* multiset.le_sup
- \- *theorem* multiset.length_ndinsert_of_mem
- \- *theorem* multiset.length_ndinsert_of_not_mem
- \- *theorem* multiset.length_sort
- \- *lemma* multiset.lift_beta
- \- *lemma* multiset.map_comp_coe
- \- *lemma* multiset.map_eq_map_of_bij_of_nodup
- \- *theorem* multiset.map_single_le_powerset
- \- *lemma* multiset.map_traverse
- \- *theorem* multiset.mem_antidiagonal
- \- *theorem* multiset.mem_erase_dup
- \- *theorem* multiset.mem_erase_iff_of_nodup
- \- *theorem* multiset.mem_erase_of_nodup
- \- *theorem* multiset.mem_ndinsert
- \- *theorem* multiset.mem_ndinsert_of_mem
- \- *theorem* multiset.mem_ndinsert_self
- \- *theorem* multiset.mem_ndinter
- \- *theorem* multiset.mem_ndunion
- \- *lemma* multiset.mem_pi
- \- *theorem* multiset.mem_powerset
- \- *theorem* multiset.mem_powerset_aux
- \- *theorem* multiset.mem_powerset_len
- \- *theorem* multiset.mem_powerset_len_aux
- \- *lemma* multiset.mem_sections
- \- *theorem* multiset.mem_sort
- \- *theorem* multiset.mem_sub_of_nodup
- \- *def* multiset.nat.antidiagonal
- \- *lemma* multiset.nat.antidiagonal_zero
- \- *lemma* multiset.nat.card_antidiagonal
- \- *lemma* multiset.nat.mem_antidiagonal
- \- *lemma* multiset.nat.nodup_antidiagonal
- \- *lemma* multiset.naturality
- \- *def* multiset.ndinsert
- \- *theorem* multiset.ndinsert_le
- \- *theorem* multiset.ndinsert_of_mem
- \- *theorem* multiset.ndinsert_of_not_mem
- \- *theorem* multiset.ndinsert_zero
- \- *def* multiset.ndinter
- \- *theorem* multiset.ndinter_cons_of_not_mem
- \- *theorem* multiset.ndinter_eq_inter
- \- *theorem* multiset.ndinter_eq_zero_iff_disjoint
- \- *theorem* multiset.ndinter_le_left
- \- *theorem* multiset.ndinter_le_right
- \- *theorem* multiset.ndinter_subset_left
- \- *theorem* multiset.ndinter_subset_right
- \- *def* multiset.ndunion
- \- *theorem* multiset.ndunion_eq_union
- \- *theorem* multiset.ndunion_le
- \- *theorem* multiset.ndunion_le_add
- \- *theorem* multiset.ndunion_le_union
- \- *def* multiset.nodup
- \- *theorem* multiset.nodup_add
- \- *theorem* multiset.nodup_add_of_nodup
- \- *theorem* multiset.nodup_attach
- \- *lemma* multiset.nodup_bind
- \- *theorem* multiset.nodup_cons
- \- *theorem* multiset.nodup_cons_of_nodup
- \- *theorem* multiset.nodup_erase_dup
- \- *theorem* multiset.nodup_erase_eq_filter
- \- *theorem* multiset.nodup_erase_of_nodup
- \- *theorem* multiset.nodup_ext
- \- *theorem* multiset.nodup_filter
- \- *theorem* multiset.nodup_filter_map
- \- *theorem* multiset.nodup_iff_count_le_one
- \- *theorem* multiset.nodup_iff_le
- \- *theorem* multiset.nodup_inter_left
- \- *theorem* multiset.nodup_inter_right
- \- *theorem* multiset.nodup_map
- \- *theorem* multiset.nodup_map_on
- \- *theorem* multiset.nodup_ndinsert
- \- *theorem* multiset.nodup_ndinter
- \- *theorem* multiset.nodup_ndunion
- \- *theorem* multiset.nodup_of_le
- \- *theorem* multiset.nodup_of_nodup_cons
- \- *theorem* multiset.nodup_of_nodup_map
- \- *lemma* multiset.nodup_pi
- \- *theorem* multiset.nodup_pmap
- \- *theorem* multiset.nodup_powerset
- \- *theorem* multiset.nodup_powerset_len
- \- *theorem* multiset.nodup_product
- \- *theorem* multiset.nodup_range
- \- *theorem* multiset.nodup_sigma
- \- *theorem* multiset.nodup_singleton
- \- *theorem* multiset.nodup_union
- \- *theorem* multiset.nodup_zero
- \- *theorem* multiset.not_mem_of_nodup_cons
- \- *theorem* multiset.not_nodup_pair
- \- *lemma* multiset.pairwise_of_nodup
- \- *def* multiset.pi.cons
- \- *lemma* multiset.pi.cons_ne
- \- *lemma* multiset.pi.cons_same
- \- *lemma* multiset.pi.cons_swap
- \- *def* multiset.pi.empty
- \- *def* multiset.pi
- \- *lemma* multiset.pi_cons
- \- *lemma* multiset.pi_cons_injective
- \- *lemma* multiset.pi_zero
- \- *def* multiset.powerset
- \- *def* multiset.powerset_aux'
- \- *theorem* multiset.powerset_aux'_cons
- \- *theorem* multiset.powerset_aux'_nil
- \- *theorem* multiset.powerset_aux'_perm
- \- *def* multiset.powerset_aux
- \- *theorem* multiset.powerset_aux_eq_map_coe
- \- *theorem* multiset.powerset_aux_perm
- \- *theorem* multiset.powerset_aux_perm_powerset_aux'
- \- *theorem* multiset.powerset_coe'
- \- *theorem* multiset.powerset_coe
- \- *theorem* multiset.powerset_cons
- \- *def* multiset.powerset_len
- \- *def* multiset.powerset_len_aux
- \- *theorem* multiset.powerset_len_aux_cons
- \- *theorem* multiset.powerset_len_aux_eq_map_coe
- \- *theorem* multiset.powerset_len_aux_nil
- \- *theorem* multiset.powerset_len_aux_perm
- \- *theorem* multiset.powerset_len_aux_zero
- \- *theorem* multiset.powerset_len_coe'
- \- *theorem* multiset.powerset_len_coe
- \- *theorem* multiset.powerset_len_cons
- \- *theorem* multiset.powerset_len_le_powerset
- \- *theorem* multiset.powerset_len_mono
- \- *theorem* multiset.powerset_len_zero_left
- \- *theorem* multiset.powerset_len_zero_right
- \- *theorem* multiset.powerset_zero
- \- *lemma* multiset.prod_map_add
- \- *lemma* multiset.prod_map_sum
- \- *lemma* multiset.pure_def
- \- *theorem* multiset.range_le
- \- *theorem* multiset.revzip_powerset_aux'
- \- *theorem* multiset.revzip_powerset_aux
- \- *theorem* multiset.revzip_powerset_aux_lemma
- \- *theorem* multiset.revzip_powerset_aux_perm
- \- *theorem* multiset.revzip_powerset_aux_perm_aux'
- \- *def* multiset.sections
- \- *lemma* multiset.sections_add
- \- *lemma* multiset.sections_cons
- \- *lemma* multiset.sections_zero
- \- *def* multiset.sort
- \- *theorem* multiset.sort_eq
- \- *theorem* multiset.sort_sorted
- \- *theorem* multiset.subset_erase_dup'
- \- *theorem* multiset.subset_erase_dup
- \- *theorem* multiset.subset_ndunion_left
- \- *theorem* multiset.subset_ndunion_right
- \- *def* multiset.sup
- \- *lemma* multiset.sup_add
- \- *lemma* multiset.sup_cons
- \- *lemma* multiset.sup_erase_dup
- \- *lemma* multiset.sup_le
- \- *lemma* multiset.sup_mono
- \- *lemma* multiset.sup_ndinsert
- \- *lemma* multiset.sup_ndunion
- \- *lemma* multiset.sup_singleton
- \- *lemma* multiset.sup_union
- \- *lemma* multiset.sup_zero
- \- *def* multiset.traverse
- \- *lemma* multiset.traverse_map
- \- *theorem* multiset.zero_ndinter
- \- *theorem* multiset.zero_ndunion

Added src/data/multiset/default.lean


Added src/data/multiset/erase_dup.lean
- \+ *theorem* multiset.coe_erase_dup
- \+ *def* multiset.erase_dup
- \+ *theorem* multiset.erase_dup_cons_of_mem
- \+ *theorem* multiset.erase_dup_cons_of_not_mem
- \+ *theorem* multiset.erase_dup_eq_self
- \+ *theorem* multiset.erase_dup_eq_zero
- \+ *theorem* multiset.erase_dup_ext
- \+ *theorem* multiset.erase_dup_le
- \+ *theorem* multiset.erase_dup_map_erase_dup_eq
- \+ *theorem* multiset.erase_dup_singleton
- \+ *theorem* multiset.erase_dup_subset'
- \+ *theorem* multiset.erase_dup_subset
- \+ *theorem* multiset.erase_dup_zero
- \+ *theorem* multiset.le_erase_dup
- \+ *theorem* multiset.mem_erase_dup
- \+ *theorem* multiset.nodup_erase_dup
- \+ *theorem* multiset.subset_erase_dup'
- \+ *theorem* multiset.subset_erase_dup

Added src/data/multiset/finset_ops.lean
- \+ *lemma* multiset.attach_ndinsert
- \+ *theorem* multiset.coe_ndinsert
- \+ *theorem* multiset.coe_ndinter
- \+ *theorem* multiset.coe_ndunion
- \+ *theorem* multiset.cons_ndinter_of_mem
- \+ *theorem* multiset.cons_ndunion
- \+ *theorem* multiset.disjoint_ndinsert_left
- \+ *theorem* multiset.disjoint_ndinsert_right
- \+ *theorem* multiset.erase_dup_add
- \+ *theorem* multiset.erase_dup_cons
- \+ *theorem* multiset.inter_le_ndinter
- \+ *theorem* multiset.le_ndinsert_self
- \+ *theorem* multiset.le_ndinter
- \+ *theorem* multiset.le_ndunion_left
- \+ *theorem* multiset.le_ndunion_right
- \+ *theorem* multiset.length_ndinsert_of_mem
- \+ *theorem* multiset.length_ndinsert_of_not_mem
- \+ *theorem* multiset.mem_ndinsert
- \+ *theorem* multiset.mem_ndinsert_of_mem
- \+ *theorem* multiset.mem_ndinsert_self
- \+ *theorem* multiset.mem_ndinter
- \+ *theorem* multiset.mem_ndunion
- \+ *def* multiset.ndinsert
- \+ *theorem* multiset.ndinsert_le
- \+ *theorem* multiset.ndinsert_of_mem
- \+ *theorem* multiset.ndinsert_of_not_mem
- \+ *theorem* multiset.ndinsert_zero
- \+ *def* multiset.ndinter
- \+ *theorem* multiset.ndinter_cons_of_not_mem
- \+ *theorem* multiset.ndinter_eq_inter
- \+ *theorem* multiset.ndinter_eq_zero_iff_disjoint
- \+ *theorem* multiset.ndinter_le_left
- \+ *theorem* multiset.ndinter_le_right
- \+ *theorem* multiset.ndinter_subset_left
- \+ *theorem* multiset.ndinter_subset_right
- \+ *def* multiset.ndunion
- \+ *theorem* multiset.ndunion_eq_union
- \+ *theorem* multiset.ndunion_le
- \+ *theorem* multiset.ndunion_le_add
- \+ *theorem* multiset.ndunion_le_union
- \+ *theorem* multiset.nodup_ndinsert
- \+ *theorem* multiset.nodup_ndinter
- \+ *theorem* multiset.nodup_ndunion
- \+ *theorem* multiset.subset_ndunion_left
- \+ *theorem* multiset.subset_ndunion_right
- \+ *theorem* multiset.zero_ndinter
- \+ *theorem* multiset.zero_ndunion

Added src/data/multiset/fold.lean
- \+ *theorem* multiset.coe_fold_l
- \+ *theorem* multiset.coe_fold_r
- \+ *def* multiset.fold
- \+ *theorem* multiset.fold_add
- \+ *theorem* multiset.fold_cons'_left
- \+ *theorem* multiset.fold_cons'_right
- \+ *theorem* multiset.fold_cons_left
- \+ *theorem* multiset.fold_cons_right
- \+ *theorem* multiset.fold_distrib
- \+ *theorem* multiset.fold_eq_foldl
- \+ *theorem* multiset.fold_eq_foldr
- \+ *theorem* multiset.fold_erase_dup_idem
- \+ *theorem* multiset.fold_hom
- \+ *theorem* multiset.fold_singleton
- \+ *theorem* multiset.fold_union_inter
- \+ *theorem* multiset.fold_zero
- \+ *theorem* multiset.le_smul_erase_dup

Added src/data/multiset/functor.lean
- \+ *lemma* multiset.bind_def
- \+ *lemma* multiset.comp_traverse
- \+ *lemma* multiset.fmap_def
- \+ *lemma* multiset.id_traverse
- \+ *lemma* multiset.lift_beta
- \+ *lemma* multiset.map_comp_coe
- \+ *lemma* multiset.map_traverse
- \+ *lemma* multiset.naturality
- \+ *lemma* multiset.pure_def
- \+ *def* multiset.traverse
- \+ *lemma* multiset.traverse_map

Added src/data/multiset/intervals.lean
- \+ *lemma* multiset.Ico.add_consecutive
- \+ *theorem* multiset.Ico.card
- \+ *theorem* multiset.Ico.eq_cons
- \+ *theorem* multiset.Ico.eq_zero_iff
- \+ *theorem* multiset.Ico.eq_zero_of_le
- \+ *lemma* multiset.Ico.filter_le
- \+ *lemma* multiset.Ico.filter_le_of_le
- \+ *lemma* multiset.Ico.filter_le_of_le_bot
- \+ *lemma* multiset.Ico.filter_le_of_top_le
- \+ *lemma* multiset.Ico.filter_lt
- \+ *lemma* multiset.Ico.filter_lt_of_ge
- \+ *lemma* multiset.Ico.filter_lt_of_le_bot
- \+ *lemma* multiset.Ico.filter_lt_of_top_le
- \+ *lemma* multiset.Ico.inter_consecutive
- \+ *theorem* multiset.Ico.map_add
- \+ *theorem* multiset.Ico.map_sub
- \+ *theorem* multiset.Ico.mem
- \+ *theorem* multiset.Ico.nodup
- \+ *theorem* multiset.Ico.not_mem_top
- \+ *theorem* multiset.Ico.pred_singleton
- \+ *theorem* multiset.Ico.self_eq_zero
- \+ *theorem* multiset.Ico.succ_singleton
- \+ *theorem* multiset.Ico.succ_top
- \+ *theorem* multiset.Ico.zero_bot
- \+ *def* multiset.Ico

Added src/data/multiset/lattice.lean
- \+ *def* multiset.inf
- \+ *lemma* multiset.inf_add
- \+ *lemma* multiset.inf_cons
- \+ *lemma* multiset.inf_erase_dup
- \+ *lemma* multiset.inf_le
- \+ *lemma* multiset.inf_mono
- \+ *lemma* multiset.inf_ndinsert
- \+ *lemma* multiset.inf_ndunion
- \+ *lemma* multiset.inf_singleton
- \+ *lemma* multiset.inf_union
- \+ *lemma* multiset.inf_zero
- \+ *lemma* multiset.le_inf
- \+ *lemma* multiset.le_sup
- \+ *def* multiset.sup
- \+ *lemma* multiset.sup_add
- \+ *lemma* multiset.sup_cons
- \+ *lemma* multiset.sup_erase_dup
- \+ *lemma* multiset.sup_le
- \+ *lemma* multiset.sup_mono
- \+ *lemma* multiset.sup_ndinsert
- \+ *lemma* multiset.sup_ndunion
- \+ *lemma* multiset.sup_singleton
- \+ *lemma* multiset.sup_union
- \+ *lemma* multiset.sup_zero

Added src/data/multiset/nat_antidiagonal.lean
- \+ *def* multiset.nat.antidiagonal
- \+ *lemma* multiset.nat.antidiagonal_zero
- \+ *lemma* multiset.nat.card_antidiagonal
- \+ *lemma* multiset.nat.mem_antidiagonal
- \+ *lemma* multiset.nat.nodup_antidiagonal

Added src/data/multiset/nodup.lean
- \+ *theorem* multiset.coe_nodup
- \+ *theorem* multiset.count_eq_one_of_mem
- \+ *theorem* multiset.disjoint_of_nodup_add
- \+ *lemma* multiset.forall_of_pairwise
- \+ *theorem* multiset.le_iff_subset
- \+ *lemma* multiset.map_eq_map_of_bij_of_nodup
- \+ *theorem* multiset.mem_erase_iff_of_nodup
- \+ *theorem* multiset.mem_erase_of_nodup
- \+ *theorem* multiset.mem_sub_of_nodup
- \+ *def* multiset.nodup
- \+ *theorem* multiset.nodup_add
- \+ *theorem* multiset.nodup_add_of_nodup
- \+ *theorem* multiset.nodup_attach
- \+ *lemma* multiset.nodup_bind
- \+ *theorem* multiset.nodup_cons
- \+ *theorem* multiset.nodup_cons_of_nodup
- \+ *theorem* multiset.nodup_erase_eq_filter
- \+ *theorem* multiset.nodup_erase_of_nodup
- \+ *theorem* multiset.nodup_ext
- \+ *theorem* multiset.nodup_filter
- \+ *theorem* multiset.nodup_filter_map
- \+ *theorem* multiset.nodup_iff_count_le_one
- \+ *theorem* multiset.nodup_iff_le
- \+ *theorem* multiset.nodup_inter_left
- \+ *theorem* multiset.nodup_inter_right
- \+ *theorem* multiset.nodup_map
- \+ *theorem* multiset.nodup_map_on
- \+ *theorem* multiset.nodup_of_le
- \+ *theorem* multiset.nodup_of_nodup_cons
- \+ *theorem* multiset.nodup_of_nodup_map
- \+ *theorem* multiset.nodup_pmap
- \+ *theorem* multiset.nodup_powerset
- \+ *theorem* multiset.nodup_powerset_len
- \+ *theorem* multiset.nodup_product
- \+ *theorem* multiset.nodup_range
- \+ *theorem* multiset.nodup_sigma
- \+ *theorem* multiset.nodup_singleton
- \+ *theorem* multiset.nodup_union
- \+ *theorem* multiset.nodup_zero
- \+ *theorem* multiset.not_mem_of_nodup_cons
- \+ *theorem* multiset.not_nodup_pair
- \+ *lemma* multiset.pairwise_of_nodup
- \+ *theorem* multiset.range_le

Added src/data/multiset/pi.lean
- \+ *lemma* multiset.card_pi
- \+ *lemma* multiset.mem_pi
- \+ *lemma* multiset.nodup_pi
- \+ *def* multiset.pi.cons
- \+ *lemma* multiset.pi.cons_ne
- \+ *lemma* multiset.pi.cons_same
- \+ *lemma* multiset.pi.cons_swap
- \+ *def* multiset.pi.empty
- \+ *def* multiset.pi
- \+ *lemma* multiset.pi_cons
- \+ *lemma* multiset.pi_cons_injective
- \+ *lemma* multiset.pi_zero

Added src/data/multiset/powerset.lean
- \+ *theorem* multiset.card_powerset
- \+ *theorem* multiset.card_powerset_len
- \+ *theorem* multiset.map_single_le_powerset
- \+ *theorem* multiset.mem_powerset
- \+ *theorem* multiset.mem_powerset_aux
- \+ *theorem* multiset.mem_powerset_len
- \+ *theorem* multiset.mem_powerset_len_aux
- \+ *def* multiset.powerset
- \+ *def* multiset.powerset_aux'
- \+ *theorem* multiset.powerset_aux'_cons
- \+ *theorem* multiset.powerset_aux'_nil
- \+ *theorem* multiset.powerset_aux'_perm
- \+ *def* multiset.powerset_aux
- \+ *theorem* multiset.powerset_aux_eq_map_coe
- \+ *theorem* multiset.powerset_aux_perm
- \+ *theorem* multiset.powerset_aux_perm_powerset_aux'
- \+ *theorem* multiset.powerset_coe'
- \+ *theorem* multiset.powerset_coe
- \+ *theorem* multiset.powerset_cons
- \+ *def* multiset.powerset_len
- \+ *def* multiset.powerset_len_aux
- \+ *theorem* multiset.powerset_len_aux_cons
- \+ *theorem* multiset.powerset_len_aux_eq_map_coe
- \+ *theorem* multiset.powerset_len_aux_nil
- \+ *theorem* multiset.powerset_len_aux_perm
- \+ *theorem* multiset.powerset_len_aux_zero
- \+ *theorem* multiset.powerset_len_coe'
- \+ *theorem* multiset.powerset_len_coe
- \+ *theorem* multiset.powerset_len_cons
- \+ *theorem* multiset.powerset_len_le_powerset
- \+ *theorem* multiset.powerset_len_mono
- \+ *theorem* multiset.powerset_len_zero_left
- \+ *theorem* multiset.powerset_len_zero_right
- \+ *theorem* multiset.powerset_zero
- \+ *theorem* multiset.revzip_powerset_aux'
- \+ *theorem* multiset.revzip_powerset_aux
- \+ *theorem* multiset.revzip_powerset_aux_lemma
- \+ *theorem* multiset.revzip_powerset_aux_perm
- \+ *theorem* multiset.revzip_powerset_aux_perm_aux'

Added src/data/multiset/sections.lean
- \+ *lemma* multiset.card_sections
- \+ *lemma* multiset.coe_sections
- \+ *lemma* multiset.mem_sections
- \+ *lemma* multiset.prod_map_sum
- \+ *def* multiset.sections
- \+ *lemma* multiset.sections_add
- \+ *lemma* multiset.sections_cons
- \+ *lemma* multiset.sections_zero

Added src/data/multiset/sort.lean
- \+ *theorem* multiset.coe_sort
- \+ *theorem* multiset.length_sort
- \+ *theorem* multiset.mem_sort
- \+ *def* multiset.sort
- \+ *theorem* multiset.sort_eq
- \+ *theorem* multiset.sort_sorted

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
Added src/category_theory/preadditive/biproducts.lean
- \+ *lemma* category_theory.biprod.column_nonzero_of_iso
- \+ *def* category_theory.biprod.gaussian'
- \+ *def* category_theory.biprod.gaussian
- \+ *lemma* category_theory.biprod.inl_of_components
- \+ *lemma* category_theory.biprod.inr_of_components
- \+ *def* category_theory.biprod.iso_elim'
- \+ *def* category_theory.biprod.iso_elim
- \+ *def* category_theory.biprod.of_components
- \+ *lemma* category_theory.biprod.of_components_comp
- \+ *lemma* category_theory.biprod.of_components_eq
- \+ *lemma* category_theory.biprod.of_components_fst
- \+ *lemma* category_theory.biprod.of_components_snd
- \+ *def* category_theory.biprod.unipotent_lower
- \+ *def* category_theory.biprod.unipotent_upper
- \+ *lemma* category_theory.biproduct.column_nonzero_of_iso'
- \+ *def* category_theory.biproduct.column_nonzero_of_iso
- \+ *def* category_theory.is_iso_left_of_is_iso_biprod_map
- \+ *def* category_theory.is_iso_right_of_is_iso_biprod_map

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
- \+ *lemma* eq_one_of_pow_eq_one
- \+ *lemma* one_le_pow_iff
- \+ *lemma* one_le_pow_of_one_le'
- \+ *lemma* pow_eq_one_iff
- \+ *lemma* pow_le_one_iff
- \+ *lemma* pow_le_one_of_le_one

Modified src/algebra/ordered_group.lean
- \+ *lemma* mul_le_one_of_le_one_of_le_one
- \+ *lemma* one_le_mul_of_one_le_of_one_le

Added src/ring_theory/valuation/basic.lean
- \+ *lemma* valuation.coe_coe
- \+ *def* valuation.comap
- \+ *lemma* valuation.comap_comp
- \+ *lemma* valuation.comap_id
- \+ *lemma* valuation.comap_on_quot_eq
- \+ *lemma* valuation.comap_supp
- \+ *lemma* valuation.ext
- \+ *lemma* valuation.ext_iff
- \+ *lemma* valuation.is_equiv.comap
- \+ *lemma* valuation.is_equiv.map
- \+ *lemma* valuation.is_equiv.ne_zero
- \+ *lemma* valuation.is_equiv.of_eq
- \+ *lemma* valuation.is_equiv.refl
- \+ *lemma* valuation.is_equiv.symm
- \+ *lemma* valuation.is_equiv.trans
- \+ *lemma* valuation.is_equiv.val_eq
- \+ *def* valuation.is_equiv
- \+ *lemma* valuation.is_equiv_of_map_strict_mono
- \+ *lemma* valuation.is_equiv_of_val_le_one
- \+ *def* valuation.map
- \+ *lemma* valuation.map_add
- \+ *lemma* valuation.map_add_of_distinct_val
- \+ *lemma* valuation.map_add_supp
- \+ *lemma* valuation.map_eq_of_sub_lt
- \+ *lemma* valuation.map_inv
- \+ *lemma* valuation.map_mul
- \+ *lemma* valuation.map_neg
- \+ *theorem* valuation.map_neg_one
- \+ *lemma* valuation.map_one
- \+ *lemma* valuation.map_pow
- \+ *lemma* valuation.map_sub_le_max
- \+ *lemma* valuation.map_sub_swap
- \+ *lemma* valuation.map_units_inv
- \+ *lemma* valuation.map_zero
- \+ *lemma* valuation.mem_supp_iff
- \+ *lemma* valuation.ne_zero_iff
- \+ *def* valuation.on_quot
- \+ *lemma* valuation.on_quot_comap_eq
- \+ *def* valuation.on_quot_val
- \+ *lemma* valuation.self_le_supp_comap
- \+ *def* valuation.supp
- \+ *lemma* valuation.supp_quot
- \+ *lemma* valuation.supp_quot_supp
- \+ *def* valuation.to_preorder
- \+ *theorem* valuation.unit_map_eq
- \+ *lemma* valuation.zero_iff
- \+ *structure* valuation



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
- \+ *lemma* finset.prod_product'
- \+ *lemma* mul_equiv.map_prod

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.coe_scalar
- \+ *lemma* matrix.elementary_eq_basis_mul_basis
- \+ *lemma* matrix.matrix_eq_sum_elementary
- \+ *lemma* matrix.scalar_apply_eq
- \+ *lemma* matrix.scalar_apply_ne
- \+ *lemma* matrix.smul_std_basis_matrix
- \+ *def* matrix.std_basis_matrix
- \+ *lemma* matrix.std_basis_matrix_add
- \+ *lemma* matrix.std_basis_matrix_zero

Modified src/ring_theory/algebra.lean
- \+ *lemma* alg_equiv.map_sum
- \+ *lemma* alg_equiv.trans_apply

Modified src/ring_theory/matrix_algebra.lean
- \+ *lemma* matrix_equiv_tensor_apply_elementary



## [2020-07-01 00:02:51](https://github.com/leanprover-community/mathlib/commit/a40be98)
feat(category_theory/limits/shapes): simp lemmas to decompose pullback_cone.mk.fst ([#3249](https://github.com/leanprover-community/mathlib/pull/3249))
Decompose `(pullback_cone.mk _ _ _).fst` into its first component (+symmetrical and dual versions)
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* category_theory.limits.pullback_cone.mk_fst
- \+ *lemma* category_theory.limits.pullback_cone.mk_snd
- \+ *lemma* category_theory.limits.pushout_cocone.mk_inl
- \+ *lemma* category_theory.limits.pushout_cocone.mk_inr

