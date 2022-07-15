## [2019-03-31 21:33:03+02:00](https://github.com/leanprover-community/mathlib/commit/c91e6c2)
fix(ring_theory/algebra): remove duplicate theorems to fix build
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \- *lemma* complex.smul_im:
- \- *lemma* complex.smul_re:



## [2019-03-31 08:35:59-04:00](https://github.com/leanprover-community/mathlib/commit/9480df5)
refactor(computability): unpack fixed_point proof
#### Estimated changes
Modified src/computability/partrec_code.lean




## [2019-03-31 08:35:21-04:00](https://github.com/leanprover-community/mathlib/commit/359cac1)
feat(computability): computable_iff_re_compl_re
#### Estimated changes
Modified src/computability/halting.lean
- \+ *theorem* computable_pred.computable_iff
- \+ *theorem* computable_pred.computable_iff_re_compl_re
- \+ *theorem* computable_pred.to_re



## [2019-03-31 08:32:21-04:00](https://github.com/leanprover-community/mathlib/commit/514de77)
feat(data/finset): to_finset_eq_empty
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* multiset.to_finset_eq_empty

Modified src/data/multiset.lean
- \+ *theorem* multiset.erase_dup_eq_zero



## [2019-03-31 08:31:39-04:00](https://github.com/leanprover-community/mathlib/commit/72634d2)
feat(data/complex/basic): smul_re,im
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *lemma* complex.smul_im
- \+ *lemma* complex.smul_re



## [2019-03-31 00:48:41](https://github.com/leanprover-community/mathlib/commit/e1c035d)
feat(data/polynomial): eval₂_neg
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.eval₂_neg
- \+ *lemma* polynomial.eval₂_sub



## [2019-03-29 23:56:28](https://github.com/leanprover-community/mathlib/commit/c2bb4c5)
refactor(data/zsqrtd/basic): move zsqrtd out of pell and into data ([#861](https://github.com/leanprover-community/mathlib/pull/861))
#### Estimated changes
Added src/data/zsqrtd/basic.lean
- \+ *def* zsqrtd.add
- \+ *theorem* zsqrtd.add_def
- \+ *theorem* zsqrtd.add_im
- \+ *theorem* zsqrtd.add_re
- \+ *theorem* zsqrtd.bit0_im
- \+ *theorem* zsqrtd.bit0_re
- \+ *theorem* zsqrtd.bit1_im
- \+ *theorem* zsqrtd.bit1_re
- \+ *theorem* zsqrtd.coe_int_im
- \+ *theorem* zsqrtd.coe_int_re
- \+ *theorem* zsqrtd.coe_int_val
- \+ *theorem* zsqrtd.coe_nat_im
- \+ *theorem* zsqrtd.coe_nat_re
- \+ *theorem* zsqrtd.coe_nat_val
- \+ *def* zsqrtd.conj
- \+ *theorem* zsqrtd.conj_im
- \+ *theorem* zsqrtd.conj_mul
- \+ *theorem* zsqrtd.conj_re
- \+ *theorem* zsqrtd.d_pos
- \+ *theorem* zsqrtd.decompose
- \+ *theorem* zsqrtd.divides_sq_eq_zero
- \+ *theorem* zsqrtd.divides_sq_eq_zero_z
- \+ *theorem* zsqrtd.ext
- \+ *theorem* zsqrtd.le_antisymm
- \+ *theorem* zsqrtd.le_arch
- \+ *theorem* zsqrtd.le_of_le_le
- \+ *theorem* zsqrtd.le_refl
- \+ *def* zsqrtd.mul
- \+ *theorem* zsqrtd.mul_conj
- \+ *theorem* zsqrtd.mul_im
- \+ *theorem* zsqrtd.mul_re
- \+ *theorem* zsqrtd.muld_val
- \+ *def* zsqrtd.neg
- \+ *theorem* zsqrtd.neg_im
- \+ *theorem* zsqrtd.neg_re
- \+ *def* zsqrtd.nonneg
- \+ *theorem* zsqrtd.nonneg_add
- \+ *lemma* zsqrtd.nonneg_add_lem
- \+ *theorem* zsqrtd.nonneg_antisymm
- \+ *theorem* zsqrtd.nonneg_cases
- \+ *theorem* zsqrtd.nonneg_iff_zero_le
- \+ *theorem* zsqrtd.nonneg_mul
- \+ *theorem* zsqrtd.nonneg_mul_lem
- \+ *theorem* zsqrtd.nonneg_muld
- \+ *theorem* zsqrtd.nonneg_smul
- \+ *def* zsqrtd.nonnegg
- \+ *theorem* zsqrtd.nonnegg_cases_left
- \+ *theorem* zsqrtd.nonnegg_cases_right
- \+ *theorem* zsqrtd.nonnegg_comm
- \+ *theorem* zsqrtd.nonnegg_neg_pos
- \+ *theorem* zsqrtd.nonnegg_pos_neg
- \+ *def* zsqrtd.norm
- \+ *lemma* zsqrtd.norm_eq_mul_conj
- \+ *lemma* zsqrtd.norm_eq_one_iff
- \+ *lemma* zsqrtd.norm_int_cast
- \+ *lemma* zsqrtd.norm_mul
- \+ *lemma* zsqrtd.norm_nat_cast
- \+ *lemma* zsqrtd.norm_nonneg
- \+ *lemma* zsqrtd.norm_one
- \+ *lemma* zsqrtd.norm_zero
- \+ *theorem* zsqrtd.not_divides_square
- \+ *theorem* zsqrtd.not_sq_le_succ
- \+ *def* zsqrtd.of_int
- \+ *theorem* zsqrtd.of_int_eq_coe
- \+ *theorem* zsqrtd.of_int_im
- \+ *theorem* zsqrtd.of_int_re
- \+ *def* zsqrtd.one
- \+ *theorem* zsqrtd.one_im
- \+ *theorem* zsqrtd.one_re
- \+ *theorem* zsqrtd.smul_val
- \+ *theorem* zsqrtd.smuld_val
- \+ *def* zsqrtd.sq_le
- \+ *theorem* zsqrtd.sq_le_add
- \+ *theorem* zsqrtd.sq_le_add_mixed
- \+ *theorem* zsqrtd.sq_le_cancel
- \+ *theorem* zsqrtd.sq_le_mul
- \+ *theorem* zsqrtd.sq_le_of_le
- \+ *theorem* zsqrtd.sq_le_smul
- \+ *def* zsqrtd.sqrtd
- \+ *theorem* zsqrtd.sqrtd_im
- \+ *theorem* zsqrtd.sqrtd_re
- \+ *def* zsqrtd.zero
- \+ *theorem* zsqrtd.zero_im
- \+ *theorem* zsqrtd.zero_re

Renamed src/data/gaussian_int.lean to src/data/zsqrtd/gaussian_int.lean


Modified src/number_theory/pell.lean
- \- *def* zsqrtd.add
- \- *theorem* zsqrtd.add_def
- \- *theorem* zsqrtd.add_im
- \- *theorem* zsqrtd.add_re
- \- *theorem* zsqrtd.bit0_im
- \- *theorem* zsqrtd.bit0_re
- \- *theorem* zsqrtd.bit1_im
- \- *theorem* zsqrtd.bit1_re
- \- *theorem* zsqrtd.coe_int_im
- \- *theorem* zsqrtd.coe_int_re
- \- *theorem* zsqrtd.coe_int_val
- \- *theorem* zsqrtd.coe_nat_im
- \- *theorem* zsqrtd.coe_nat_re
- \- *theorem* zsqrtd.coe_nat_val
- \- *def* zsqrtd.conj
- \- *theorem* zsqrtd.conj_im
- \- *theorem* zsqrtd.conj_mul
- \- *theorem* zsqrtd.conj_re
- \- *theorem* zsqrtd.d_pos
- \- *theorem* zsqrtd.decompose
- \- *theorem* zsqrtd.divides_sq_eq_zero
- \- *theorem* zsqrtd.divides_sq_eq_zero_z
- \- *theorem* zsqrtd.ext
- \- *theorem* zsqrtd.le_antisymm
- \- *theorem* zsqrtd.le_arch
- \- *theorem* zsqrtd.le_of_le_le
- \- *theorem* zsqrtd.le_refl
- \- *def* zsqrtd.mul
- \- *theorem* zsqrtd.mul_conj
- \- *theorem* zsqrtd.mul_im
- \- *theorem* zsqrtd.mul_re
- \- *theorem* zsqrtd.muld_val
- \- *def* zsqrtd.neg
- \- *theorem* zsqrtd.neg_im
- \- *theorem* zsqrtd.neg_re
- \- *def* zsqrtd.nonneg
- \- *theorem* zsqrtd.nonneg_add
- \- *lemma* zsqrtd.nonneg_add_lem
- \- *theorem* zsqrtd.nonneg_antisymm
- \- *theorem* zsqrtd.nonneg_cases
- \- *theorem* zsqrtd.nonneg_iff_zero_le
- \- *theorem* zsqrtd.nonneg_mul
- \- *theorem* zsqrtd.nonneg_mul_lem
- \- *theorem* zsqrtd.nonneg_muld
- \- *theorem* zsqrtd.nonneg_smul
- \- *def* zsqrtd.nonnegg
- \- *theorem* zsqrtd.nonnegg_cases_left
- \- *theorem* zsqrtd.nonnegg_cases_right
- \- *theorem* zsqrtd.nonnegg_comm
- \- *theorem* zsqrtd.nonnegg_neg_pos
- \- *theorem* zsqrtd.nonnegg_pos_neg
- \- *def* zsqrtd.norm
- \- *lemma* zsqrtd.norm_eq_mul_conj
- \- *lemma* zsqrtd.norm_eq_one_iff
- \- *lemma* zsqrtd.norm_int_cast
- \- *lemma* zsqrtd.norm_mul
- \- *lemma* zsqrtd.norm_nat_cast
- \- *lemma* zsqrtd.norm_nonneg
- \- *lemma* zsqrtd.norm_one
- \- *lemma* zsqrtd.norm_zero
- \- *theorem* zsqrtd.not_divides_square
- \- *theorem* zsqrtd.not_sq_le_succ
- \- *def* zsqrtd.of_int
- \- *theorem* zsqrtd.of_int_eq_coe
- \- *theorem* zsqrtd.of_int_im
- \- *theorem* zsqrtd.of_int_re
- \- *def* zsqrtd.one
- \- *theorem* zsqrtd.one_im
- \- *theorem* zsqrtd.one_re
- \- *theorem* zsqrtd.smul_val
- \- *theorem* zsqrtd.smuld_val
- \- *def* zsqrtd.sq_le
- \- *theorem* zsqrtd.sq_le_add
- \- *theorem* zsqrtd.sq_le_add_mixed
- \- *theorem* zsqrtd.sq_le_cancel
- \- *theorem* zsqrtd.sq_le_mul
- \- *theorem* zsqrtd.sq_le_of_le
- \- *theorem* zsqrtd.sq_le_smul
- \- *def* zsqrtd.sqrtd
- \- *theorem* zsqrtd.sqrtd_im
- \- *theorem* zsqrtd.sqrtd_re
- \- *def* zsqrtd.zero
- \- *theorem* zsqrtd.zero_im
- \- *theorem* zsqrtd.zero_re

Modified src/number_theory/sum_two_squares.lean




## [2019-03-29 15:03:34-05:00](https://github.com/leanprover-community/mathlib/commit/dc7de46)
feat(analysis/convex): convex sets and functions ([#834](https://github.com/leanprover-community/mathlib/pull/834))
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* is_linear_map.is_linear_map_neg
- \+ *lemma* is_linear_map.is_linear_map_smul'
- \+ *lemma* is_linear_map.is_linear_map_smul

Added src/analysis/convex.lean
- \+ *def* convex
- \+ *lemma* convex_Icc
- \+ *lemma* convex_Ici
- \+ *lemma* convex_Ico
- \+ *lemma* convex_Iic
- \+ *lemma* convex_Iio
- \+ *lemma* convex_Inter
- \+ *lemma* convex_Ioc
- \+ *lemma* convex_Ioi
- \+ *lemma* convex_Ioo
- \+ *lemma* convex_add
- \+ *lemma* convex_affinity
- \+ *lemma* convex_ball
- \+ *lemma* convex_closed_ball
- \+ *lemma* convex_empty
- \+ *lemma* convex_halfplane
- \+ *lemma* convex_halfspace_ge
- \+ *lemma* convex_halfspace_gt
- \+ *lemma* convex_halfspace_im_gt
- \+ *lemma* convex_halfspace_im_le
- \+ *lemma* convex_halfspace_im_lge
- \+ *lemma* convex_halfspace_im_lt
- \+ *lemma* convex_halfspace_le
- \+ *lemma* convex_halfspace_lt
- \+ *lemma* convex_halfspace_re_gt
- \+ *lemma* convex_halfspace_re_le
- \+ *lemma* convex_halfspace_re_lge
- \+ *lemma* convex_halfspace_re_lt
- \+ *lemma* convex_iff:
- \+ *lemma* convex_iff_div:
- \+ *lemma* convex_inter
- \+ *lemma* convex_le_of_convex_on
- \+ *lemma* convex_linear_image'
- \+ *lemma* convex_linear_image
- \+ *lemma* convex_linear_preimage'
- \+ *lemma* convex_linear_preimage
- \+ *lemma* convex_lt_of_convex_on
- \+ *lemma* convex_neg
- \+ *lemma* convex_neg_preimage
- \+ *def* convex_on
- \+ *lemma* convex_on_add
- \+ *lemma* convex_on_dist
- \+ *lemma* convex_on_iff
- \+ *lemma* convex_on_iff_div:
- \+ *lemma* convex_on_linorder
- \+ *lemma* convex_on_smul
- \+ *lemma* convex_on_subset
- \+ *lemma* convex_on_sum
- \+ *lemma* convex_prod
- \+ *lemma* convex_segment
- \+ *lemma* convex_segment_iff
- \+ *lemma* convex_singleton
- \+ *lemma* convex_smul
- \+ *lemma* convex_smul_preimage
- \+ *lemma* convex_sub
- \+ *lemma* convex_sum
- \+ *lemma* convex_sum_iff
- \+ *lemma* convex_translation
- \+ *lemma* convex_univ
- \+ *lemma* le_on_interval_of_convex_on
- \+ *lemma* left_mem_segment
- \+ *lemma* mem_segment_iff'
- \+ *lemma* mem_segment_iff
- \+ *lemma* right_mem_segment
- \+ *def* segment
- \+ *lemma* segment_eq_Icc
- \+ *lemma* segment_symm
- \+ *lemma* segment_translate
- \+ *lemma* segment_translate_image

Modified src/data/set/intervals.lean
- \+ *lemma* set.image_neg_Iic
- \+ *lemma* set.image_neg_Iio

Modified src/linear_algebra/basic.lean
- \+ *lemma* is_linear_map.is_linear_map_add
- \+ *lemma* is_linear_map.is_linear_map_sub

Modified src/ring_theory/algebra.lean
- \+ *lemma* complex.smul_im:
- \+ *lemma* complex.smul_re:



## [2019-03-29 13:08:29-04:00](https://github.com/leanprover-community/mathlib/commit/171e913)
fix(scripts/remote-install-update-mathlib): add GitPython dependency ([#860](https://github.com/leanprover-community/mathlib/pull/860))
#### Estimated changes
Modified scripts/remote-install-update-mathlib.sh




## [2019-03-28 22:56:01-04:00](https://github.com/leanprover-community/mathlib/commit/2e7f009)
fix(scripts/deploy_nightly): pushing to the `lean-3.4.2` branch is sometimes blocked ([#859](https://github.com/leanprover-community/mathlib/pull/859))
#### Estimated changes
Modified scripts/deploy_nightly.sh




## [2019-03-28 22:11:15-04:00](https://github.com/leanprover-community/mathlib/commit/a4fd55c)
feat(library_search): a simple library_search function ([#839](https://github.com/leanprover-community/mathlib/pull/839))
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/basic.lean


Modified src/tactic/interactive.lean


Added src/tactic/library_search.lean
- \+ *def* tactic.library_search.head_symbol_match.to_string

Added test/library_search/basic.lean


Added test/library_search/ring_theory.lean




## [2019-03-28 20:04:39-04:00](https://github.com/leanprover-community/mathlib/commit/59caf11)
fix(scripts/update-mathlib): fix imports of python files
#### Estimated changes
Modified scripts/update-mathlib.py




## [2019-03-28 19:11:34-04:00](https://github.com/leanprover-community/mathlib/commit/6cd336c)
fix(scripts/update-mathlib): github authentication
#### Estimated changes
Modified scripts/update-mathlib.py




## [2019-03-28 16:32:00-04:00](https://github.com/leanprover-community/mathlib/commit/1c04a32)
fix(scripts/update-mathlib): update-mathlib shouldn't need github authentication
#### Estimated changes
Modified scripts/update-mathlib.py




## [2019-03-28 14:01:35-04:00](https://github.com/leanprover-community/mathlib/commit/48df321)
feat(category_theory/instances): category of groups ([#749](https://github.com/leanprover-community/mathlib/pull/749))
#### Estimated changes
Added src/category_theory/instances/groups.lean
- \+ *def* category_theory.instances.AddCommGroup.forget_to_Group
- \+ *def* category_theory.instances.AddCommGroup
- \+ *def* category_theory.instances.Group
- \+ *def* category_theory.instances.is_add_comm_group_hom



## [2019-03-28 16:25:01](https://github.com/leanprover-community/mathlib/commit/179d4d0)
refactor(*): unify group/monoid_action, make semimodule extend action ([#850](https://github.com/leanprover-community/mathlib/pull/850))
* refactor(*): unify group/monoid_action, use standard names, make semimodule extend action
* Rename action to mul_action
* Generalize lemmas. Also, add class for multiplicative action on additive structure
* Add pi-instances
* Dirty hacky fix
* Remove #print and set_option pp.all
* clean up proof, avoid diamonds
* Fix some build issues
* Fix build
* Rename mul_action_add to distrib_mul_action
* Bump up the type class search depth in some places
#### Estimated changes
Modified src/algebra/module.lean
- \- *theorem* mul_smul
- \- *theorem* one_smul
- \- *theorem* smul_add
- \- *theorem* smul_zero

Modified src/algebra/pi_instances.lean


Modified src/analysis/asymptotics.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/deriv.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/group_theory/group_action.lean
- \- *lemma* group_action.bijective
- \- *def* group_action.comp_hom
- \- *def* group_action.mul_left_cosets
- \- *lemma* group_action.orbit_eq_iff
- \- *def* group_action.orbit_rel
- \- *def* group_action.to_perm
- \- *def* monoid_action.comp_hom
- \- *def* monoid_action.fixed_points
- \- *lemma* monoid_action.mem_fixed_points'
- \- *lemma* monoid_action.mem_fixed_points
- \- *lemma* monoid_action.mem_orbit
- \- *lemma* monoid_action.mem_orbit_iff
- \- *lemma* monoid_action.mem_orbit_self
- \- *lemma* monoid_action.mem_stabilizer_iff
- \- *def* monoid_action.orbit
- \- *def* monoid_action.stabilizer
- \+ *lemma* mul_action.bijective
- \+ *def* mul_action.comp_hom
- \+ *def* mul_action.fixed_points
- \+ *lemma* mul_action.mem_fixed_points'
- \+ *lemma* mul_action.mem_fixed_points
- \+ *lemma* mul_action.mem_orbit
- \+ *lemma* mul_action.mem_orbit_iff
- \+ *lemma* mul_action.mem_orbit_self
- \+ *lemma* mul_action.mem_stabilizer_iff
- \+ *def* mul_action.mul_left_cosets
- \+ *def* mul_action.orbit
- \+ *lemma* mul_action.orbit_eq_iff
- \+ *def* mul_action.orbit_rel
- \+ *def* mul_action.stabilizer
- \+ *def* mul_action.to_perm
- \+ *theorem* mul_smul
- \+ *theorem* one_smul
- \+ *theorem* smul_add
- \+ *theorem* smul_zero

Modified src/group_theory/sylow.lean
- \- *lemma* group_action.card_modeq_card_fixed_points
- \- *lemma* group_action.mem_fixed_points_iff_card_orbit_eq_one
- \+ *lemma* mul_action.card_modeq_card_fixed_points
- \+ *lemma* mul_action.mem_fixed_points_iff_card_orbit_eq_one

Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/finsupp.lean


Modified src/ring_theory/algebra.lean




## [2019-03-27 21:28:39-04:00](https://github.com/leanprover-community/mathlib/commit/25bab56)
feat(scripts/cache_olean): cache and fetch olean binaries ([#766](https://github.com/leanprover-community/mathlib/pull/766))
* script setup and documentation
* fetch mathlib nightly when relevant
* use credentials to access `github.com`
* locate correct git directory, and add prompt
* add confirmation message to setup-dev-scripts
* adding --build-all option
#### Estimated changes
Modified .gitignore


Modified README.md


Modified docs/howto-contribute.md


Added scripts/cache-olean.py


Added scripts/post-checkout


Added scripts/post-commit


Modified scripts/remote-install-update-mathlib.sh


Added scripts/setup-dev-scripts.sh


Added scripts/setup-lean-git-hooks.sh


Deleted scripts/setup-update-mathlib.sh


Modified scripts/update-mathlib.py




## [2019-03-27 21:47:02+01:00](https://github.com/leanprover-community/mathlib/commit/8838ff3)
feat(algebra/field_power): add fpow_one, one_fpow, fpow_mul, mul_fpow (closes [#855](https://github.com/leanprover-community/mathlib/pull/855))
#### Estimated changes
Modified src/algebra/field.lean
- \+/\- *lemma* inv_eq_zero
- \+ *lemma* neg_inv'
- \+ *lemma* units.mk0_coe

Modified src/algebra/field_power.lean
- \+ *lemma* fpow_mul
- \+ *lemma* fpow_one
- \+ *lemma* mul_fpow
- \+ *lemma* one_fpow



## [2019-03-27 20:15:04+01:00](https://github.com/leanprover-community/mathlib/commit/8429354)
feat(analysis): add real.rpow_le_one
#### Estimated changes
Modified src/analysis/exponential.lean
- \+ *lemma* real.rpow_le_one



## [2019-03-27 20:15:04+01:00](https://github.com/leanprover-community/mathlib/commit/4305ad6)
feat(analysis): add rpow_pos_of_pos
#### Estimated changes
Modified src/analysis/exponential.lean
- \+ *lemma* real.rpow_pos_of_pos



## [2019-03-27 09:57:35-05:00](https://github.com/leanprover-community/mathlib/commit/02ca494)
Remove outparam in normed space ([#844](https://github.com/leanprover-community/mathlib/pull/844))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *lemma* is_bounded_linear_map.continuous
- \+/\- *lemma* is_bounded_linear_map.id
- \+/\- *theorem* is_bounded_linear_map.is_O_comp
- \+/\- *theorem* is_bounded_linear_map.is_O_id
- \+/\- *theorem* is_bounded_linear_map.is_O_sub
- \+/\- *lemma* is_bounded_linear_map.lim_zero_bounded_linear_map
- \+/\- *lemma* is_bounded_linear_map.neg
- \+/\- *lemma* is_bounded_linear_map.smul
- \+/\- *lemma* is_bounded_linear_map.sub
- \+/\- *lemma* is_bounded_linear_map.tendsto
- \+/\- *def* is_bounded_linear_map.to_linear_map
- \+/\- *lemma* is_bounded_linear_map.zero

Modified src/analysis/normed_space/deriv.lean
- \+/\- *theorem* has_fderiv_at.is_o
- \+/\- *theorem* has_fderiv_at_filter_id
- \+/\- *theorem* has_fderiv_at_id
- \+/\- *theorem* has_fderiv_at_within_id

Modified src/analysis/normed_space/operator_norm.lean




## [2019-03-27 08:20:35-04:00](https://github.com/leanprover-community/mathlib/commit/52fddda)
feat(algebra/archimedean): lemmas about powers of elements ([#802](https://github.com/leanprover-community/mathlib/pull/802))
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+ *lemma* exists_int_pow_near
- \+ *lemma* exists_nat_pow_near



## [2019-03-26 16:35:47-05:00](https://github.com/leanprover-community/mathlib/commit/17e40bb)
feat(tactic/congr): apply to `iff` propositions ([#833](https://github.com/leanprover-community/mathlib/pull/833))
#### Estimated changes
Modified src/tactic/interactive.lean


Modified test/tactics.lean




## [2019-03-26 21:53:30+01:00](https://github.com/leanprover-community/mathlib/commit/c3a9028)
fix(data/polynomial): (nat_)degree_map' assumed a comm_ring instead of a comm_semiring
#### Estimated changes
Modified src/data/polynomial.lean




## [2019-03-26 19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/a016652)
feat(data/finset): add range_add_one'
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* finset.range_add_one'



## [2019-03-26 19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/0ea37e9)
feat(algebra/big_operators): add prod_map, sum_map
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_map



## [2019-03-26 19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/d3c68fc)
feat(analysis/normed_space): tendsto_zero_iff_norm_tendsto_zero
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* continuous_norm
- \+/\- *lemma* lim_norm
- \+/\- *lemma* lim_norm_zero
- \+ *lemma* tendsto_zero_iff_norm_tendsto_zero



## [2019-03-26 19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/df08058)
refactor(analysis/normed_space): rename norm_mul -> norm_mul_le; use norm_mul for the equality in normed fields; and norm_mul_le for the inequality in normed_rings
#### Estimated changes
Modified src/analysis/asymptotics.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_mul
- \+ *lemma* norm_mul_le
- \+/\- *lemma* norm_pow
- \+ *lemma* norm_pow_le
- \+ *lemma* norm_prod
- \- *lemma* normed_field.norm_pow

Modified src/data/complex/basic.lean
- \+ *lemma* complex.abs_of_nat

Modified src/data/padics/padic_integers.lean




## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/bd21b0e)
feat(analyis/normed_space): add normed_field instance for ℂ
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* complex.norm_int
- \+ *lemma* complex.norm_int_of_nonneg
- \+ *lemma* complex.norm_nat
- \+ *lemma* complex.norm_rat
- \+ *lemma* complex.norm_real



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/a01cf86)
feat(data/multiset,data/finset): add multiset./finset.le_sum_of_additive
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* finset.abs_sum_le_sum_abs
- \+ *lemma* finset.le_sum_of_subadditive

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_triangle_sum

Modified src/data/multiset.lean
- \+ *lemma* multiset.abs_sum_le_sum_abs
- \+ *lemma* multiset.le_sum_of_subadditive



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/c912253)
feat(algebra/group_power): add lt_of_pow_lt_pow
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* lt_of_pow_lt_pow
- \+/\- *lemma* pow_le_pow_of_le_left



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/fd37f96)
feat(data/fin): add injective_cast_le
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.injective_cast_le



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/c0c2edb)
feat(algebra/big_operators): add Gauss' summation formula
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.sum_range_id
- \+ *lemma* finset.sum_range_id_mul_two



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/cfeb887)
feat(data/polynomial): degree_map', nat_degree_map' semiring variant of degree_map, nat_degree_map
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.degree_map'
- \+ *lemma* polynomial.nat_degree_map'



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/aa2c6e2)
feat(data/mv_polynomial): more about renaming
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* mv_polynomial.injective_rename
- \+ *lemma* mv_polynomial.rename_eq
- \+ *lemma* mv_polynomial.rename_monomial
- \+ *lemma* mv_polynomial.total_degree_rename_le



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/5b73f46)
chore(data/mv_polynomial): use type name as filename
#### Estimated changes
Modified src/category_theory/instances/rings.lean


Renamed src/data/multivariate_polynomial.lean to src/data/mv_polynomial.lean


Modified src/linear_algebra/finsupp.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/polynomial.lean




## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/8ccca3f)
feat(data/finsupp): add emb_domain
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *def* finsupp.emb_domain
- \+ *lemma* finsupp.emb_domain_apply
- \+ *lemma* finsupp.emb_domain_eq_map_domain
- \+ *lemma* finsupp.emb_domain_map_range
- \+ *lemma* finsupp.emb_domain_notin_range
- \+ *lemma* finsupp.emb_domain_zero
- \+ *lemma* finsupp.injective_map_domain
- \+ *lemma* finsupp.support_emb_domain



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/d7bd41f)
feat(linear_algebra/dimension): add exists_mem_ne_zero_of_dim_pos
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* exists_mem_ne_zero_of_dim_pos
- \+ *lemma* exists_mem_ne_zero_of_ne_bot



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/22352ff)
feat(linear_algebra/dimension): add dim_span_le; add rank_finset_sum_le
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_span_le
- \+ *lemma* dim_span_of_finset
- \+ *lemma* rank_finset_sum_le
- \+ *lemma* rank_zero



## [2019-03-26 17:46:31+01:00](https://github.com/leanprover-community/mathlib/commit/f882b8b)
feat(data/polynomial): rec_on_horner ([#739](https://github.com/leanprover-community/mathlib/pull/739))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.coeff_mk
- \+ *lemma* polynomial.degree_div_X_lt
- \+ *lemma* polynomial.degree_le_zero_iff
- \+ *lemma* polynomial.degree_lt_degree_mul_X
- \+ *lemma* polynomial.degree_pos_induction_on
- \+ *def* polynomial.div_X
- \+ *lemma* polynomial.div_X_C
- \+ *lemma* polynomial.div_X_add
- \+ *lemma* polynomial.div_X_eq_zero_iff
- \+ *lemma* polynomial.div_X_mul_X_add
- \+ *def* polynomial.nonzero_comm_semiring.of_polynomial_ne
- \+ *def* polynomial.rec_on_horner



## [2019-03-26 00:11:19](https://github.com/leanprover-community/mathlib/commit/410ae5d)
feat(group_theory/subgroup): add inv_iff_ker' and related ([#790](https://github.com/leanprover-community/mathlib/pull/790))
* feat(group_theory/subgroup): add inv_iff_ker' and related
* correcting spacing and adding to_additive attribute
* changing name to ker-mk
#### Estimated changes
Modified src/group_theory/quotient_group.lean
- \+ *lemma* quotient_group.ker_mk

Modified src/group_theory/subgroup.lean
- \+ *lemma* is_group_hom.inv_iff_ker'
- \+ *lemma* is_group_hom.inv_ker_one'
- \+ *lemma* is_group_hom.one_iff_ker_inv'
- \+ *lemma* is_group_hom.one_ker_inv'



## [2019-03-25 16:03:35-04:00](https://github.com/leanprover-community/mathlib/commit/0bb64a2)
feat(tactic/solve_by_elim): working with multiple goals ([#838](https://github.com/leanprover-community/mathlib/pull/838))
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/basic.lean


Modified src/tactic/interactive.lean


Modified test/solve_by_elim.lean




## [2019-03-25 19:21:49](https://github.com/leanprover-community/mathlib/commit/291a4f3)
refactor(algebra/group_action): use notation for monoid/group actions ([#846](https://github.com/leanprover-community/mathlib/pull/846))
* refactor(module_action): bundle and introduce notation
* fix(linear_algebra/determinant): fix the coercion issue using a local notation
* fix(linear_algebra/dimension): fix build
#### Estimated changes
Modified src/algebra/module.lean


Modified src/group_theory/group_action.lean
- \+ *lemma* group_action.bijective
- \+ *def* group_action.comp_hom
- \+ *def* group_action.mul_left_cosets
- \+ *lemma* group_action.orbit_eq_iff
- \+ *def* group_action.orbit_rel
- \+ *def* group_action.to_perm
- \- *lemma* is_group_action.bijective
- \- *lemma* is_group_action.comp_hom
- \- *def* is_group_action.mul_left_cosets
- \- *lemma* is_group_action.orbit_eq_iff
- \- *def* is_group_action.orbit_rel
- \- *def* is_group_action.to_perm
- \- *lemma* is_monoid_action.comp_hom
- \- *def* is_monoid_action.fixed_points
- \- *lemma* is_monoid_action.mem_fixed_points'
- \- *lemma* is_monoid_action.mem_fixed_points
- \- *lemma* is_monoid_action.mem_orbit
- \- *lemma* is_monoid_action.mem_orbit_iff
- \- *lemma* is_monoid_action.mem_orbit_self
- \- *lemma* is_monoid_action.mem_stabilizer_iff
- \- *def* is_monoid_action.orbit
- \- *def* is_monoid_action.stabilizer
- \+ *def* monoid_action.comp_hom
- \+ *def* monoid_action.fixed_points
- \+ *lemma* monoid_action.mem_fixed_points'
- \+ *lemma* monoid_action.mem_fixed_points
- \+ *lemma* monoid_action.mem_orbit
- \+ *lemma* monoid_action.mem_orbit_iff
- \+ *lemma* monoid_action.mem_orbit_self
- \+ *lemma* monoid_action.mem_stabilizer_iff
- \+ *def* monoid_action.orbit
- \+ *def* monoid_action.stabilizer

Modified src/group_theory/sylow.lean
- \+ *lemma* group_action.card_modeq_card_fixed_points
- \+ *lemma* group_action.mem_fixed_points_iff_card_orbit_eq_one
- \- *lemma* is_group_action.card_modeq_card_fixed_points
- \- *lemma* is_group_action.mem_fixed_points_iff_card_orbit_eq_one

Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/dimension.lean




## [2019-03-25 18:24:08](https://github.com/leanprover-community/mathlib/commit/a1158d8)
feat(algebra/module): every abelian group is a Z-module ([#848](https://github.com/leanprover-community/mathlib/pull/848))
#### Estimated changes
Modified src/algebra/module.lean




## [2019-03-25 16:59:27+01:00](https://github.com/leanprover-community/mathlib/commit/cb5e185)
refactor(data/equiv): equiv_injective_surjective ([#849](https://github.com/leanprover-community/mathlib/pull/849))
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/data/fintype.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/dimension.lean


Modified src/logic/embedding.lean


Modified src/order/order_iso.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/noetherian.lean


Modified src/set_theory/cofinality.lean


Modified src/topology/constructions.lean




## [2019-03-23 21:28:16+01:00](https://github.com/leanprover-community/mathlib/commit/cd7402d)
Minor clarification to simpa doc ([#842](https://github.com/leanprover-community/mathlib/pull/842))
#### Estimated changes
Modified docs/tactics.md




## [2019-03-23 12:56:54-04:00](https://github.com/leanprover-community/mathlib/commit/b0b33ab)
fix(import): remove relative imports
#### Estimated changes
Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/deriv.lean




## [2019-03-22 16:02:14](https://github.com/leanprover-community/mathlib/commit/c29769f)
fix(ring_theory/multiplicity): correct spelling mistake in docstring
#### Estimated changes
Modified src/ring_theory/multiplicity.lean




## [2019-03-22 13:22:43+01:00](https://github.com/leanprover-community/mathlib/commit/b5bb446)
fix(doc/extra/tactic_writing): fix a minor error ([#841](https://github.com/leanprover-community/mathlib/pull/841)) [ci-skip]
* fix(doc/extra/tactic_writing): fix a minor error
* comma splice
#### Estimated changes
Modified docs/extras/tactic_writing.md




## [2019-03-22 00:28:38](https://github.com/leanprover-community/mathlib/commit/989efab)
feat(data/equiv/algebra): add add_equiv and mul_equiv ([#789](https://github.com/leanprover-community/mathlib/pull/789))
* feat(data/equiv/algebra): add monoid_equiv and group_equiv
* refactor; now using mul_equiv; adding add_equiv
* tidy
* namechange broke my code; now fixed
* next effort
* switching is_mul_hom back to explicit args
* removing more implicits
* typo
* switching back to implicits (to fix mathlib breakage)
* Making is_mul_hom and is_add_hom classes
* adding more to_additive
#### Estimated changes
Modified src/algebra/group.lean
- \+ *lemma* is_mul_hom.comp'
- \+ *lemma* is_mul_hom.comp
- \+ *lemma* is_mul_hom.id
- \+ *lemma* units.map_comp'
- \+ *lemma* units.map_comp
- \+ *lemma* units.map_id

Modified src/data/equiv/algebra.lean
- \+ *def* add_equiv.refl
- \+ *def* add_equiv.symm
- \+ *def* add_equiv.trans
- \+ *lemma* mul_equiv.one
- \+ *def* mul_equiv.refl
- \+ *def* mul_equiv.symm
- \+ *def* mul_equiv.trans
- \+ *def* units.map_equiv



## [2019-03-21 23:44:25](https://github.com/leanprover-community/mathlib/commit/798a08d)
feat(group_theory/submonoid): add closure_singleton ([#810](https://github.com/leanprover-community/mathlib/pull/810))
* feat(group_theory/submonoid): add closure_singleton
* adding some to_additive
#### Estimated changes
Modified src/group_theory/submonoid.lean
- \+ *theorem* add_monoid.closure_singleton
- \+ *theorem* monoid.closure_singleton
- \+ *lemma* multiples.self_mem
- \+ *lemma* multiples.zero_mem
- \+ *lemma* powers.one_mem
- \+ *lemma* powers.self_mem



## [2019-03-20 10:16:08-04:00](https://github.com/leanprover-community/mathlib/commit/098c2cb)
feat(tactic/wlog): `discharger` defaults to classical `tauto` ([#836](https://github.com/leanprover-community/mathlib/pull/836))
#### Estimated changes
Modified src/tactic/wlog.lean




## [2019-03-18 00:04:29](https://github.com/leanprover-community/mathlib/commit/d60d161)
feat(linear_algebra/basic): add ring instance ([#823](https://github.com/leanprover-community/mathlib/pull/823))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \- *def* linear_map.endomorphism_ring
- \+/\- *def* linear_map.general_linear_group

Modified src/ring_theory/algebra.lean




## [2019-03-17 21:08:06](https://github.com/leanprover-community/mathlib/commit/9ff5e8d)
feat(algebra/punit_instances): punit instances ([#828](https://github.com/leanprover-community/mathlib/pull/828))
#### Estimated changes
Added src/algebra/punit_instances.lean
- \+ *lemma* punit.Inf_eq
- \+ *lemma* punit.Sup_eq
- \+ *lemma* punit.add_eq
- \+ *lemma* punit.bot_eq
- \+ *lemma* punit.inf_eq
- \+ *lemma* punit.inv_eq
- \+ *lemma* punit.mul_eq
- \+ *lemma* punit.neg_eq
- \+ *lemma* punit.not_lt
- \+ *lemma* punit.one_eq
- \+ *lemma* punit.smul_eq
- \+ *lemma* punit.sup_eq
- \+ *lemma* punit.top_eq
- \+ *lemma* punit.zero_eq



## [2019-03-17 21:07:14](https://github.com/leanprover-community/mathlib/commit/df996be)
fix(topology/algebra/group): fix binders for top group extensionality ([#826](https://github.com/leanprover-community/mathlib/pull/826))
#### Estimated changes
Modified src/topology/algebra/group.lean




## [2019-03-17 09:07:33-05:00](https://github.com/leanprover-community/mathlib/commit/e8bdc7f)
feat(order/filter/filter_product): build hyperreals ([#801](https://github.com/leanprover-community/mathlib/pull/801))
Construction of filter products, ultraproducts, some instances, hyperreal numbers.
#### Estimated changes
Modified src/algebra/field.lean
- \+ *lemma* inv_eq_zero

Added src/data/real/hyperreal.lean
- \+ *theorem* hyperreal.epsilon_eq_inv_omega
- \+ *lemma* hyperreal.epsilon_lt_pos
- \+ *theorem* hyperreal.epsilon_mul_omega
- \+ *lemma* hyperreal.epsilon_ne_zero
- \+ *lemma* hyperreal.epsilon_pos
- \+ *lemma* hyperreal.gt_of_tendsto_zero_of_neg
- \+ *def* hyperreal.infinitesimal
- \+ *theorem* hyperreal.infinitesimal_epsilon
- \+ *theorem* hyperreal.infinitesimal_of_tendsto_zero
- \+ *theorem* hyperreal.inv_epsilon_eq_omega
- \+ *def* hyperreal.is_st
- \+ *theorem* hyperreal.is_st_unique
- \+ *lemma* hyperreal.lt_of_tendsto_zero_of_pos
- \+ *lemma* hyperreal.neg_lt_of_tendsto_zero_of_neg
- \+ *lemma* hyperreal.omega_ne_zero
- \+ *lemma* hyperreal.omega_pos
- \+ *def* hyperreal

Modified src/data/real/nnreal.lean
- \- *lemma* inv_eq_zero

Modified src/data/set/basic.lean
- \+ *lemma* set.set_of_eq_eq_singleton

Modified src/order/filter/basic.lean
- \+ *lemma* filter.cofinite_ne_bot
- \+ *theorem* filter.compl_mem_hyperfilter_of_finite
- \+ *lemma* filter.hyperfilter_le_cofinite
- \+ *lemma* filter.is_ultrafilter_hyperfilter
- \+ *theorem* filter.mem_hyperfilter_of_finite_compl
- \+ *theorem* filter.nmem_hyperfilter_of_finite

Added src/order/filter/filter_product.lean
- \+ *def* filter.bigly_equal
- \+ *def* filter.filter_product.lift
- \+ *def* filter.filter_product.lift_rel
- \+ *def* filter.filter_product.lift_rel₂
- \+ *def* filter.filter_product.lift₂
- \+ *lemma* filter.filter_product.lt_def'
- \+ *lemma* filter.filter_product.lt_def
- \+ *def* filter.filter_product.of
- \+ *lemma* filter.filter_product.of_add
- \+ *lemma* filter.filter_product.of_eq
- \+ *lemma* filter.filter_product.of_eq_coe
- \+ *lemma* filter.filter_product.of_eq_zero
- \+ *lemma* filter.filter_product.of_id
- \+ *theorem* filter.filter_product.of_inj
- \+ *lemma* filter.filter_product.of_inv
- \+ *lemma* filter.filter_product.of_le
- \+ *lemma* filter.filter_product.of_le_of_le
- \+ *lemma* filter.filter_product.of_lt
- \+ *lemma* filter.filter_product.of_lt_of_lt
- \+ *lemma* filter.filter_product.of_mul
- \+ *lemma* filter.filter_product.of_ne
- \+ *lemma* filter.filter_product.of_ne_zero
- \+ *lemma* filter.filter_product.of_neg
- \+ *lemma* filter.filter_product.of_one
- \+ *lemma* filter.filter_product.of_rel
- \+ *lemma* filter.filter_product.of_rel_of_rel
- \+ *lemma* filter.filter_product.of_rel_of_rel₂
- \+ *lemma* filter.filter_product.of_rel₂
- \+ *def* filter.filter_product.of_seq
- \+ *lemma* filter.filter_product.of_seq_add
- \+ *theorem* filter.filter_product.of_seq_fun
- \+ *theorem* filter.filter_product.of_seq_fun₂
- \+ *lemma* filter.filter_product.of_seq_inv
- \+ *lemma* filter.filter_product.of_seq_mul
- \+ *lemma* filter.filter_product.of_seq_neg
- \+ *lemma* filter.filter_product.of_seq_one
- \+ *lemma* filter.filter_product.of_seq_zero
- \+ *lemma* filter.filter_product.of_zero
- \+ *def* filter.filterprod



## [2019-03-16 09:30:48-05:00](https://github.com/leanprover-community/mathlib/commit/0c2c2bd)
feat(group_theory/perm/cycles): cycle_factors ([#815](https://github.com/leanprover-community/mathlib/pull/815))
#### Estimated changes
Added src/group_theory/perm/cycles.lean
- \+ *lemma* equiv.perm.apply_eq_self_iff_of_same_cycle
- \+ *def* equiv.perm.cycle_factors
- \+ *def* equiv.perm.cycle_factors_aux
- \+ *def* equiv.perm.cycle_of
- \+ *lemma* equiv.perm.cycle_of_apply
- \+ *lemma* equiv.perm.cycle_of_apply_of_not_same_cycle
- \+ *lemma* equiv.perm.cycle_of_apply_of_same_cycle
- \+ *lemma* equiv.perm.cycle_of_apply_self
- \+ *lemma* equiv.perm.cycle_of_cycle
- \+ *lemma* equiv.perm.cycle_of_gpow_apply_self
- \+ *lemma* equiv.perm.cycle_of_inv
- \+ *lemma* equiv.perm.cycle_of_one
- \+ *lemma* equiv.perm.cycle_of_pow_apply_self
- \+ *lemma* equiv.perm.is_cycle_cycle_of
- \+ *lemma* equiv.perm.same_cycle.refl
- \+ *lemma* equiv.perm.same_cycle.symm
- \+ *lemma* equiv.perm.same_cycle.trans
- \+ *def* equiv.perm.same_cycle
- \+ *lemma* equiv.perm.same_cycle_apply
- \+ *lemma* equiv.perm.same_cycle_cycle
- \+ *lemma* equiv.perm.same_cycle_inv
- \+ *lemma* equiv.perm.same_cycle_inv_apply
- \+ *lemma* equiv.perm.same_cycle_of_is_cycle

Renamed src/group_theory/perm.lean to src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.card_support_swap_mul
- \+ *lemma* equiv.perm.disjoint.symm
- \+ *def* equiv.perm.disjoint
- \+ *lemma* equiv.perm.disjoint_comm
- \+ *lemma* equiv.perm.disjoint_mul_comm
- \+ *lemma* equiv.perm.disjoint_mul_left
- \+ *lemma* equiv.perm.disjoint_mul_right
- \+ *lemma* equiv.perm.disjoint_one_left
- \+ *lemma* equiv.perm.disjoint_one_right
- \+ *lemma* equiv.perm.disjoint_prod_perm
- \+ *lemma* equiv.perm.disjoint_prod_right
- \+ *lemma* equiv.perm.exists_gpow_eq_of_is_cycle
- \- *lemma* equiv.perm.exists_int_pow_eq_of_is_cycle
- \+ *lemma* equiv.perm.gpow_apply_eq_of_apply_apply_eq_self
- \+ *lemma* equiv.perm.gpow_apply_eq_self_of_apply_eq_self
- \+/\- *def* equiv.perm.is_cycle
- \+/\- *lemma* equiv.perm.is_cycle_inv
- \+ *lemma* equiv.perm.ne_and_ne_of_swap_mul_apply_ne_self
- \+ *lemma* equiv.perm.of_subtype_one
- \+ *lemma* equiv.perm.pow_apply_eq_of_apply_apply_eq_self
- \- *lemma* equiv.perm.pow_apply_eq_of_apply_apply_eq_self_int
- \- *lemma* equiv.perm.pow_apply_eq_of_apply_apply_eq_self_nat
- \+ *lemma* equiv.perm.pow_apply_eq_self_of_apply_eq_self
- \+ *lemma* equiv.perm.subtype_perm_one
- \- *lemma* equiv.perm.support_swap_mul
- \- *lemma* equiv.perm.support_swap_mul_cycle
- \+ *lemma* equiv.perm.support_swap_mul_eq
- \+ *lemma* equiv.perm.swap_induction_on

Modified src/linear_algebra/determinant.lean


Modified test/fin_cases.lean




## [2019-03-16 09:28:41-05:00](https://github.com/leanprover-community/mathlib/commit/7b001c9)
feat(data/set/intervals): add missing intervals + some lemmas ([#805](https://github.com/leanprover-community/mathlib/pull/805))
The lemmas about Icc ⊆ I** are important for convexity
#### Estimated changes
Modified src/data/set/intervals.lean
- \+ *lemma* set.Icc_subset_Icc_iff
- \+ *lemma* set.Icc_subset_Ici_iff
- \+ *lemma* set.Icc_subset_Ico_iff
- \+ *lemma* set.Icc_subset_Iic_iff
- \+ *lemma* set.Icc_subset_Iio_iff
- \+ *lemma* set.Icc_subset_Ioc_iff
- \+ *lemma* set.Icc_subset_Ioi_iff
- \+ *lemma* set.Icc_subset_Ioo_iff
- \+ *def* set.Ici
- \+ *lemma* set.Ici_ne_empty
- \+ *def* set.Iic
- \+ *lemma* set.Iic_ne_empty
- \+ *def* set.Ioc
- \+ *lemma* set.Ioc_eq_empty
- \+ *def* set.Ioi
- \+ *lemma* set.Ioi_ne_empty
- \+ *lemma* set.mem_Ici
- \+ *lemma* set.mem_Iic
- \+ *lemma* set.mem_Ioc
- \+ *lemma* set.mem_Ioi



## [2019-03-14 10:32:41+01:00](https://github.com/leanprover-community/mathlib/commit/2bf44d3)
refactor(*): rename metric_space_subtype to subtype.metric_space ([#817](https://github.com/leanprover-community/mathlib/pull/817))
#### Estimated changes
Modified src/data/padics/padic_integers.lean


Modified src/topology/metric_space/basic.lean




## [2019-03-14 10:31:53+01:00](https://github.com/leanprover-community/mathlib/commit/c5afc52)
feat(topology/metric_space/baire): Baire theorem ([#816](https://github.com/leanprover-community/mathlib/pull/816))
#### Estimated changes
Modified src/data/set/countable.lean
- \+ *lemma* set.countable_prod
- \+ *lemma* set.exists_surjective_of_countable

Modified src/data/set/lattice.lean
- \+ *lemma* set.bInter_image
- \+ *lemma* set.bInter_range
- \+ *lemma* set.bUnion_image
- \+ *lemma* set.bUnion_range
- \+ *lemma* set.sInter_bUnion
- \+ *theorem* set.sInter_range
- \+ *lemma* set.sInter_union_sInter
- \+ *lemma* set.sUnion_bUnion
- \+ *lemma* set.sUnion_inter_sUnion
- \+ *theorem* set.sUnion_range

Modified src/order/complete_boolean_algebra.lean
- \+ *theorem* lattice.Inf_sup_Inf
- \+ *theorem* lattice.Inf_sup_eq
- \+ *theorem* lattice.Sup_inf_Sup
- \+ *theorem* lattice.Sup_inf_eq

Modified src/order/complete_lattice.lean
- \+ *theorem* lattice.infi_le_infi_of_subset
- \+ *theorem* lattice.supr_le_supr_of_subset

Modified src/topology/basic.lean
- \+ *lemma* interior_frontier
- \+ *lemma* is_closed_frontier

Added src/topology/metric_space/baire.lean
- \+ *theorem* dense_Inter_of_Gδ
- \+ *theorem* dense_Inter_of_open
- \+ *theorem* dense_Inter_of_open_nat
- \+ *theorem* dense_Union_interior_of_closed
- \+ *theorem* dense_bInter_of_Gδ
- \+ *theorem* dense_bInter_of_open
- \+ *theorem* dense_bUnion_interior_of_closed
- \+ *theorem* dense_sInter_of_Gδ
- \+ *theorem* dense_sInter_of_open
- \+ *theorem* dense_sUnion_interior_of_closed
- \+ *lemma* is_Gδ.union
- \+ *def* is_Gδ
- \+ *lemma* is_Gδ_Inter_of_open
- \+ *lemma* is_Gδ_bInter_of_open
- \+ *lemma* is_Gδ_sInter
- \+ *lemma* is_open.is_Gδ
- \+ *theorem* nonempty_interior_of_Union_of_closed

Modified src/topology/metric_space/basic.lean
- \+ *theorem* metric.mem_closed_ball_self



## [2019-03-13 23:45:07-04:00](https://github.com/leanprover-community/mathlib/commit/72100bd)
feat(tactic/squeeze,hole): remove needless qualifications in names
#### Estimated changes
Modified src/meta/rb_map.lean


Modified src/tactic/basic.lean


Modified src/tactic/squeeze.lean




## [2019-03-12 13:37:46-04:00](https://github.com/leanprover-community/mathlib/commit/82f79a5)
feat(data/list|multiset|finset): lemmas about intervals in nat ([#795](https://github.com/leanprover-community/mathlib/pull/795))
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.Ico.image_add
- \+ *theorem* finset.Ico.image_sub
- \+ *lemma* finset.Ico.inter_consecutive
- \- *theorem* finset.Ico.map_add
- \+/\- *theorem* finset.Ico.pred_singleton
- \+ *theorem* finset.Ico.succ_top'

Modified src/data/list/basic.lean
- \+ *lemma* list.Ico.bag_inter_consecutive
- \+ *lemma* list.Ico.inter_consecutive
- \+ *theorem* list.Ico.map_sub
- \+/\- *theorem* list.Ico.pred_singleton
- \+ *theorem* list.map_sub_range'

Modified src/data/multiset.lean
- \+ *lemma* multiset.Ico.inter_consecutive
- \+ *theorem* multiset.Ico.map_sub
- \+/\- *theorem* multiset.Ico.pred_singleton



## [2019-03-12 13:53:34+01:00](https://github.com/leanprover-community/mathlib/commit/2738f9b)
chore(topology/*): @uniformity α _ becomes 𝓤 α ([#814](https://github.com/leanprover-community/mathlib/pull/814))
This is a binder type change and a local notation
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/uniform_group.lean
- \+/\- *lemma* uniformity_eq_comap_nhds_zero'
- \+/\- *lemma* uniformity_eq_comap_nhds_zero
- \+/\- *lemma* uniformity_translate

Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* metric.uniformity_dist'
- \+/\- *theorem* metric.uniformity_dist
- \+/\- *theorem* uniformity_edist

Modified src/topology/metric_space/cau_seq_filter.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* uniformity_edist''
- \+/\- *theorem* uniformity_edist'

Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* comp_le_uniformity
- \+/\- *lemma* comp_mem_uniformity_sets
- \+/\- *lemma* comp_symm_of_uniformity
- \+/\- *lemma* interior_mem_uniformity
- \+/\- *lemma* mem_nhds_left
- \+/\- *lemma* mem_nhds_right
- \+/\- *lemma* mem_uniformity_is_closed
- \+/\- *lemma* nhds_eq_comap_uniformity
- \+/\- *lemma* nhds_eq_uniformity
- \+/\- *lemma* nhdset_of_mem_uniformity
- \+/\- *lemma* refl_le_uniformity
- \+/\- *lemma* refl_mem_uniformity
- \+/\- *lemma* symm_le_uniformity
- \+/\- *lemma* symm_of_uniformity
- \+/\- *lemma* tendsto_const_uniformity
- \+/\- *lemma* tendsto_left_nhds_uniformity
- \+/\- *lemma* tendsto_right_nhds_uniformity
- \+/\- *lemma* tendsto_swap_uniformity
- \+/\- *def* uniformity
- \+/\- *lemma* uniformity_eq_symm
- \+/\- *lemma* uniformity_eq_uniformity_closure
- \+/\- *lemma* uniformity_eq_uniformity_interior
- \+/\- *lemma* uniformity_le_symm

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *def* cauchy
- \+/\- *lemma* cauchy_iff
- \+/\- *lemma* cauchy_map_iff

Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2019-03-12 01:04:54-04:00](https://github.com/leanprover-community/mathlib/commit/3360267)
feat(tactic/basic): folding over the environment, to get all declarations ([#798](https://github.com/leanprover-community/mathlib/pull/798))
#### Estimated changes
Modified src/tactic/basic.lean




## [2019-03-11 16:11:52-04:00](https://github.com/leanprover-community/mathlib/commit/bde8690)
feat(data/alist,data/finmap): union ([#750](https://github.com/leanprover-community/mathlib/pull/750))
#### Estimated changes
Modified src/data/finmap.lean
- \+ *theorem* finmap.ext_iff
- \+ *theorem* finmap.induction_on₂
- \+ *theorem* finmap.induction_on₃
- \+ *theorem* finmap.keys_union
- \+ *theorem* finmap.lookup_empty
- \+ *theorem* finmap.lookup_union_left
- \+ *theorem* finmap.lookup_union_right
- \+/\- *theorem* finmap.mem_insert
- \+ *theorem* finmap.mem_lookup_union
- \+ *theorem* finmap.mem_lookup_union_middle
- \+ *theorem* finmap.mem_union
- \+ *def* finmap.union
- \+ *theorem* finmap.union_to_finmap

Modified src/data/list/alist.lean
- \+ *theorem* alist.empty_entries
- \+ *theorem* alist.empty_union
- \+ *theorem* alist.lookup_empty
- \+/\- *theorem* alist.lookup_insert_ne
- \+ *theorem* alist.lookup_union_left
- \+ *theorem* alist.lookup_union_right
- \+/\- *theorem* alist.mem_insert
- \+ *theorem* alist.mem_lookup_union
- \+ *theorem* alist.mem_lookup_union_middle
- \+ *theorem* alist.mem_union
- \+ *theorem* alist.perm_union
- \+ *theorem* alist.singleton_entries
- \+ *def* alist.union
- \+ *theorem* alist.union_empty
- \+ *theorem* alist.union_entries

Modified src/data/list/sigma.lean
- \+ *theorem* list.kerase_append_left
- \+ *theorem* list.kerase_append_right
- \+ *theorem* list.kerase_comm
- \+ *def* list.kunion
- \+ *theorem* list.kunion_cons
- \+ *theorem* list.kunion_kerase
- \+ *theorem* list.kunion_nil
- \+ *theorem* list.kunion_nodupkeys
- \+/\- *theorem* list.lookup_kinsert_ne
- \+ *theorem* list.lookup_kunion_left
- \+ *theorem* list.lookup_kunion_right
- \+/\- *theorem* list.mem_keys_kinsert
- \+ *theorem* list.mem_keys_kunion
- \+ *theorem* list.mem_lookup_kunion
- \+ *theorem* list.mem_lookup_kunion_middle
- \+ *theorem* list.nil_kunion
- \+ *theorem* list.perm_kunion
- \+ *theorem* list.perm_kunion_left
- \+ *theorem* list.perm_kunion_right



## [2019-03-11 17:09:10+01:00](https://github.com/leanprover-community/mathlib/commit/eb96a25)
feat(topology/algebra/group): extensionality for top group structure
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* topological_group.ext



## [2019-03-11 14:06:20](https://github.com/leanprover-community/mathlib/commit/69249d8)
feat(topology/algebra/monoid): add is_submonoid.mem_nhds_one ([#809](https://github.com/leanprover-community/mathlib/pull/809))
#### Estimated changes
Modified src/topology/algebra/monoid.lean
- \+ *lemma* is_submonoid.mem_nhds_one



## [2019-03-09 17:49:20-05:00](https://github.com/leanprover-community/mathlib/commit/51c31ce)
refactor(data/list): rm redundant eq_nil_of_forall_not_mem ([#804](https://github.com/leanprover-community/mathlib/pull/804))
#### Estimated changes
Modified src/data/hash_map.lean


Modified src/data/list/basic.lean
- \- *theorem* list.eq_nil_of_forall_not_mem

Modified src/data/multiset.lean




## [2019-03-09 11:34:38](https://github.com/leanprover-community/mathlib/commit/e8818fa)
feat(data/set/finite): add finite_lt_nat ([#807](https://github.com/leanprover-community/mathlib/pull/807))
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* set.finite_lt_nat



## [2019-03-08 20:10:50](https://github.com/leanprover-community/mathlib/commit/7de57e8)
feat(ring_theory/noetherian): Nakayama's Lemma ([#778](https://github.com/leanprover-community/mathlib/pull/778))
* feat(ring_theory/noetherian): Nakayama's Lemma
* Update src/ring_theory/noetherian.lean
Co-Authored-By: kckennylau <kc_kennylau@yahoo.com.hk>
#### Estimated changes
Modified src/ring_theory/ideal_operations.lean
- \+ *theorem* submodule.mem_smul_span_singleton

Modified src/ring_theory/noetherian.lean
- \+ *theorem* submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul



## [2019-03-08 15:01:45+01:00](https://github.com/leanprover-community/mathlib/commit/1159fa9)
refactot(data/equiv/basic): rename apply_inverse_apply to apply_symm_apply ([#800](https://github.com/leanprover-community/mathlib/pull/800))
#### Estimated changes
Modified src/category_theory/adjunction.lean


Modified src/data/equiv/basic.lean
- \- *theorem* equiv.apply_inverse_apply
- \+ *theorem* equiv.apply_symm_apply
- \- *theorem* equiv.inverse_apply_apply
- \- *lemma* equiv.inverse_trans_apply
- \+ *theorem* equiv.symm_apply_apply
- \+ *lemma* equiv.symm_trans_apply

Modified src/data/equiv/denumerable.lean


Modified src/data/finsupp.lean


Modified src/data/multivariate_polynomial.lean


Modified src/field_theory/perfect_closure.lean


Modified src/order/order_iso.lean
- \- *theorem* order_iso.apply_inverse_apply
- \+ *theorem* order_iso.apply_symm_apply
- \- *theorem* order_iso.inverse_apply_apply
- \+ *theorem* order_iso.symm_apply_apply

Modified src/ring_theory/localization.lean


Modified src/set_theory/ordinal.lean




## [2019-03-08 13:42:54+01:00](https://github.com/leanprover-community/mathlib/commit/b1af140)
style(data/list/basic): clean up count_bag_inter
#### Estimated changes
Modified src/data/list/basic.lean




## [2019-03-08 08:46:58+01:00](https://github.com/leanprover-community/mathlib/commit/ffa6d69)
feat(*): has_mem (set α) (filter α) ([#799](https://github.com/leanprover-community/mathlib/pull/799))
#### Estimated changes
Modified src/analysis/asymptotics.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/deriv.lean


Modified src/analysis/specific_limits.lean


Modified src/data/analysis/filter.lean
- \+/\- *theorem* filter.realizer.mem_sets

Modified src/data/analysis/topology.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.simple_func.integral_congr

Modified src/measure_theory/measure_space.lean
- \+/\- *def* measure_theory.all_ae

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.bind_mono
- \+/\- *lemma* filter.congr_sets
- \+/\- *lemma* filter.empty_in_sets_eq_bot
- \+/\- *lemma* filter.exists_sets_subset_iff
- \+/\- *lemma* filter.image_mem_map
- \+/\- *lemma* filter.inf_principal_eq_bot
- \+/\- *lemma* filter.infi_sets_induct
- \+/\- *lemma* filter.inhabited_of_mem_sets
- \+/\- *lemma* filter.inter_mem_sets
- \+/\- *theorem* filter.le_def
- \+/\- *lemma* filter.le_map
- \+/\- *theorem* filter.le_map_comap_of_surjective'
- \+/\- *lemma* filter.le_principal_iff
- \+/\- *lemma* filter.map_comap
- \+/\- *theorem* filter.map_comap_of_surjective'
- \+/\- *lemma* filter.map_cong
- \+/\- *lemma* filter.map_inf'
- \+/\- *lemma* filter.mem_at_top
- \+/\- *lemma* filter.mem_bot_sets
- \+/\- *theorem* filter.mem_comap_sets
- \+/\- *lemma* filter.mem_inf_sets_of_left
- \+/\- *lemma* filter.mem_inf_sets_of_right
- \+ *lemma* filter.mem_infi
- \+ *lemma* filter.mem_infi_finite
- \+/\- *lemma* filter.mem_infi_sets
- \+/\- *lemma* filter.mem_map
- \+/\- *lemma* filter.mem_map_sets_iff
- \+/\- *lemma* filter.mem_or_mem_of_ultrafilter
- \+/\- *lemma* filter.mem_principal_self
- \+/\- *lemma* filter.mem_principal_sets
- \+/\- *lemma* filter.mem_pure
- \+/\- *lemma* filter.mem_pure_iff
- \+/\- *lemma* filter.mem_sets_of_neq_bot
- \+/\- *lemma* filter.mem_sets_of_superset
- \+/\- *lemma* filter.mem_top_sets
- \+/\- *lemma* filter.mem_top_sets_iff_forall
- \+/\- *lemma* filter.monotone_mem_sets
- \+/\- *lemma* filter.mp_sets
- \+/\- *theorem* filter.preimage_mem_comap
- \+/\- *lemma* filter.range_mem_map
- \+/\- *lemma* filter.singleton_mem_pure_sets
- \+/\- *lemma* filter.univ_mem_sets'
- \+/\- *lemma* filter.univ_mem_sets

Modified src/order/filter/partial.lean
- \+/\- *def* filter.mem_pmap
- \+/\- *theorem* filter.ptendsto'_of_ptendsto

Modified src/topology/algebra/group.lean
- \+/\- *lemma* add_group_with_zero_nhd.exists_Z_half
- \+/\- *lemma* exists_nhds_split4
- \+/\- *lemma* exists_nhds_split
- \+/\- *lemma* exists_nhds_split_inv

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* ge_mem_nhds
- \+/\- *lemma* gt_mem_nhds
- \+/\- *lemma* le_mem_nhds
- \+/\- *lemma* lt_mem_nhds
- \+/\- *lemma* mem_nhds_orderable_dest

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean
- \+/\- *lemma* is_open_iff_mem_nhds
- \+/\- *theorem* mem_closure_iff_nhds
- \+/\- *lemma* mem_of_nhds

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/compact_open.lean


Modified src/topology/constructions.lean
- \+/\- *lemma* map_nhds_subtype_val_eq

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* ennreal.coe_range_mem_nhds

Modified src/topology/maps.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* metric.ball_mem_nhds
- \+/\- *theorem* metric.mem_nhds_iff

Modified src/topology/metric_space/cau_seq_filter.lean
- \+/\- *lemma* sequentially_complete.set_seq_of_cau_filter_mem_sets

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* emetric.ball_mem_nhds
- \+/\- *theorem* emetric.mem_nhds_iff

Modified src/topology/order.lean
- \+/\- *lemma* map_nhds_induced_eq

Modified src/topology/separation.lean
- \+/\- *lemma* compl_singleton_mem_nhds
- \+/\- *lemma* nhds_is_closed

Modified src/topology/sequences.lean


Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* comp_mem_uniformity_sets
- \+/\- *lemma* comp_symm_of_uniformity
- \+/\- *lemma* interior_mem_uniformity
- \+ *lemma* mem_map_sets_iff'
- \+/\- *lemma* mem_uniformity_is_closed
- \+/\- *lemma* nhdset_of_mem_uniformity
- \+/\- *lemma* refl_mem_uniformity
- \+/\- *lemma* symm_of_uniformity

Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2019-03-07 23:35:39+01:00](https://github.com/leanprover-community/mathlib/commit/7e77967)
refactor(localization): shorten proofs ([#796](https://github.com/leanprover-community/mathlib/pull/796))
* feat(algebra/group): units.coe_map
* refactor(localization): shorten proofs
*  swap order of equality in ring_equiv.symm_to_equiv
#### Estimated changes
Modified src/data/equiv/algebra.lean
- \+ *lemma* ring_equiv.to_equiv_symm
- \+ *lemma* ring_equiv.to_equiv_symm_apply

Modified src/ring_theory/localization.lean
- \+/\- *lemma* localization.lift'_apply_coe
- \+ *lemma* localization.lift'_mk
- \+ *lemma* localization.map_comp_map
- \+ *lemma* localization.map_id
- \+ *lemma* localization.map_map



## [2019-03-07 10:17:21-05:00](https://github.com/leanprover-community/mathlib/commit/26bd400)
feat(data/list): lemmas about count and bag_inter ([#797](https://github.com/leanprover-community/mathlib/pull/797))
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* multiset.to_finset_inter

Modified src/data/list/basic.lean
- \+ *theorem* list.bag_inter_nil_iff_inter_nil
- \+ *theorem* list.count_bag_inter
- \+ *theorem* list.count_erase_of_ne
- \+ *theorem* list.count_erase_self
- \+/\- *theorem* list.mem_bag_inter

Modified src/data/multiset.lean
- \+ *theorem* multiset.coe_inter



## [2019-03-06 20:07:22-05:00](https://github.com/leanprover-community/mathlib/commit/181647b)
feat(tactic/basic): utility functions for names ([#791](https://github.com/leanprover-community/mathlib/pull/791))
#### Estimated changes
Modified src/tactic/basic.lean




## [2019-03-06 23:01:10](https://github.com/leanprover-community/mathlib/commit/48eaf05)
feat(algebra/group): units.coe_map
#### Estimated changes
Modified src/algebra/group.lean
- \+ *lemma* units.coe_map



## [2019-03-06 22:11:42](https://github.com/leanprover-community/mathlib/commit/e286452)
feat(data/nat/basic): some lemmas ([#792](https://github.com/leanprover-community/mathlib/pull/792))
* feat(data/nat/basic): some lemmas
* fixing namespace, moving lemma
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.le_pred_of_lt
- \+ *lemma* nat.one_le_of_lt
- \+ *lemma* nat.pred_one_add
- \+ *lemma* nat.sub_sub_sub_cancel_right



## [2019-03-06 10:16:34-05:00](https://github.com/leanprover-community/mathlib/commit/61e02dd)
feat(data/finset): missing fold_map lemma ([#794](https://github.com/leanprover-community/mathlib/pull/794))
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.fold_map



## [2019-03-06 14:21:24](https://github.com/leanprover-community/mathlib/commit/cc753d7)
feat(ring_theory/localization): adds induced ring hom between fraction rings ([#781](https://github.com/leanprover-community/mathlib/pull/781))
* feat(ring_theory/localization): adds induced ring hom between fraction rings
* Break some extremely long lines
* Put map in the fraction_ring namespace
* Move global variable into statements
* Rename rec to lift', make interface for lift, generalise map
* Improve simp-lemmas, add docstrings
* Rename circ to comp in lemma names
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+/\- *def* localization.at_prime
- \+ *lemma* localization.away.lift_coe
- \+ *lemma* localization.away.lift_comp_of
- \+ *lemma* localization.away.lift_of
- \+/\- *def* localization.away
- \+/\- *lemma* localization.coe_add
- \+ *lemma* localization.coe_is_unit'
- \+ *lemma* localization.coe_is_unit
- \+/\- *lemma* localization.coe_mul
- \+/\- *lemma* localization.coe_neg
- \+/\- *lemma* localization.coe_one
- \+/\- *lemma* localization.coe_pow
- \+/\- *lemma* localization.coe_sub
- \+/\- *lemma* localization.coe_zero
- \- *lemma* localization.eq_zero_of
- \- *lemma* localization.eq_zero_of_ne_zero_of_mul_eq_zero
- \+ *def* localization.equiv_of_equiv
- \+ *lemma* localization.fraction_ring.eq_zero_of
- \+ *lemma* localization.fraction_ring.eq_zero_of_ne_zero_of_mul_eq_zero
- \+ *def* localization.fraction_ring.equiv_of_equiv
- \+ *def* localization.fraction_ring.inv_aux
- \+ *def* localization.fraction_ring.map
- \+ *lemma* localization.fraction_ring.map_coe
- \+ *lemma* localization.fraction_ring.map_comp_of
- \+ *lemma* localization.fraction_ring.map_of
- \+ *lemma* localization.fraction_ring.mem_non_zero_divisors_iff_ne_zero
- \+ *lemma* localization.fraction_ring.mk_eq_div'
- \+ *lemma* localization.fraction_ring.mk_eq_div
- \+ *lemma* localization.fraction_ring.mk_inv'
- \+ *lemma* localization.fraction_ring.mk_inv
- \+ *lemma* localization.fraction_ring.of.injective
- \+/\- *def* localization.fraction_ring
- \- *def* localization.inv_aux
- \+ *def* localization.lift'
- \+ *lemma* localization.lift'_apply_coe
- \+ *lemma* localization.lift'_coe
- \+ *lemma* localization.lift'_comp_of
- \+ *lemma* localization.lift'_of
- \+ *lemma* localization.lift_apply_coe
- \+ *lemma* localization.lift_coe
- \+ *lemma* localization.lift_comp_of
- \+ *lemma* localization.lift_of
- \- *def* localization.loc
- \+ *def* localization.map
- \+ *lemma* localization.map_coe
- \+/\- *theorem* localization.map_comap
- \+ *lemma* localization.map_comp_of
- \+ *lemma* localization.map_of
- \- *lemma* localization.mem_non_zero_divisors_of_ne_zero
- \+/\- *def* localization.mk
- \+ *lemma* localization.mk_eq
- \- *lemma* localization.mk_eq_div
- \- *lemma* localization.ne_zero_of_mem_non_zero_divisors
- \+ *lemma* localization.non_zero_divisors_one_val
- \- *lemma* localization.of.injective
- \+/\- *def* localization.of
- \+/\- *lemma* localization.of_add
- \+ *lemma* localization.of_is_unit'
- \+ *lemma* localization.of_is_unit
- \+/\- *lemma* localization.of_mul
- \+/\- *lemma* localization.of_neg
- \+/\- *lemma* localization.of_one
- \+/\- *lemma* localization.of_pow
- \+/\- *lemma* localization.of_sub
- \+/\- *lemma* localization.of_zero
- \+ *def* localization.to_units
- \+ *lemma* localization.to_units_coe
- \+ *def* localization



## [2019-03-05 21:55:19+01:00](https://github.com/leanprover-community/mathlib/commit/1ec0a1f)
fix(tactic/linarith): correctly parse 0*0
#### Estimated changes
Modified src/tactic/linarith.lean


Modified test/linarith.lean




## [2019-03-05 14:15:40-05:00](https://github.com/leanprover-community/mathlib/commit/581cf19)
feat(topology): split uniform_space and topological_structure
#### Estimated changes
Modified src/algebra/module.lean


Modified src/analysis/exponential.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/data/equiv/basic.lean


Modified src/data/quot.lean


Modified src/logic/basic.lean
- \+ *lemma* {u}

Modified src/topology/algebra/group.lean
- \+ *lemma* continuous_inv'
- \+ *lemma* continuous_inv
- \+ *lemma* continuous_sub'
- \+ *lemma* continuous_sub
- \+ *lemma* exists_nhds_split4
- \+ *lemma* exists_nhds_split
- \+ *lemma* exists_nhds_split_inv
- \+ *lemma* is_open_map_mul_left
- \+ *lemma* is_open_map_mul_right
- \+ *lemma* nhds_one_symm
- \+ *lemma* nhds_translation
- \+ *lemma* nhds_translation_mul_inv
- \+ *lemma* quotient_group.open_coe
- \+ *lemma* quotient_group_saturate
- \+ *lemma* tendsto_inv
- \+ *lemma* tendsto_sub
- \- *lemma* to_uniform_space_eq
- \- *def* topological_add_group.to_uniform_space
- \- *lemma* topological_add_group_is_uniform
- \- *lemma* uniformity_eq_comap_nhds_zero'

Added src/topology/algebra/group_completion.lean
- \+ *lemma* coe_zero
- \+ *lemma* uniform_space.completion.coe_add
- \+ *lemma* uniform_space.completion.coe_neg
- \+ *lemma* uniform_space.completion.is_add_group_hom_extension
- \+ *lemma* uniform_space.completion.is_add_group_hom_map
- \+ *lemma* uniform_space.completion.is_add_group_hom_prod

Modified src/topology/algebra/infinite_sum.lean


Added src/topology/algebra/monoid.lean
- \+ *lemma* continuous_finset_prod
- \+ *lemma* continuous_list_prod
- \+ *lemma* continuous_mul'
- \+ *lemma* continuous_mul
- \+ *lemma* continuous_multiset_prod
- \+ *lemma* continuous_pow
- \+ *lemma* tendsto_finset_prod
- \+ *lemma* tendsto_list_prod
- \+ *lemma* tendsto_mul'
- \+ *lemma* tendsto_mul
- \+ *lemma* tendsto_multiset_prod

Renamed src/topology/algebra/topological_structures.lean to src/topology/algebra/ordered.lean
- \- *lemma* continuous_finset_prod
- \- *lemma* continuous_inv'
- \- *lemma* continuous_inv
- \- *lemma* continuous_list_prod
- \- *lemma* continuous_mul'
- \- *lemma* continuous_mul
- \- *lemma* continuous_multiset_prod
- \- *lemma* continuous_pow
- \- *lemma* continuous_sub'
- \- *lemma* continuous_sub
- \- *lemma* exists_nhds_split4
- \- *lemma* exists_nhds_split
- \- *lemma* exists_nhds_split_inv
- \- *lemma* group_separation_rel
- \- *def* ideal.closure
- \- *lemma* ideal.coe_closure
- \- *lemma* is_open_map_mul_left
- \- *lemma* is_open_map_mul_right
- \- *lemma* nhds_one_symm
- \- *lemma* nhds_translation
- \- *lemma* nhds_translation_mul_inv
- \- *lemma* tendsto_finset_prod
- \- *lemma* tendsto_inv
- \- *lemma* tendsto_list_prod
- \- *lemma* tendsto_mul'
- \- *lemma* tendsto_mul
- \- *lemma* tendsto_multiset_prod
- \- *lemma* tendsto_sub
- \- *theorem* uniform_add_group.mk'
- \- *lemma* uniform_continuous_add'
- \- *lemma* uniform_continuous_add
- \- *lemma* uniform_continuous_neg'
- \- *lemma* uniform_continuous_neg
- \- *lemma* uniform_continuous_of_continuous
- \- *lemma* uniform_continuous_of_tendsto_zero
- \- *lemma* uniform_continuous_sub'
- \- *lemma* uniform_continuous_sub
- \- *lemma* uniform_embedding_translate
- \- *lemma* uniformity_eq_comap_nhds_zero
- \- *lemma* uniformity_translate

Deleted src/topology/algebra/quotient.lean
- \- *lemma* quotient_group.open_coe
- \- *lemma* quotient_group_saturate
- \- *lemma* quotient_ring.is_open_map_coe
- \- *lemma* quotient_ring.quotient_map_coe_coe
- \- *lemma* quotient_ring_saturate
- \- *lemma* uniform_space.ring_sep_quot
- \- *lemma* uniform_space.ring_sep_rel
- \- *def* uniform_space.sep_quot_equiv_ring_quot
- \- *lemma* {u}

Added src/topology/algebra/ring.lean
- \+ *def* ideal.closure
- \+ *lemma* ideal.coe_closure
- \+ *lemma* quotient_ring.is_open_map_coe
- \+ *lemma* quotient_ring.quotient_map_coe_coe
- \+ *lemma* quotient_ring_saturate

Added src/topology/algebra/uniform_group.lean
- \+ *lemma* add_comm_group.is_Z_bilin.neg_left
- \+ *lemma* add_comm_group.is_Z_bilin.neg_right
- \+ *lemma* add_comm_group.is_Z_bilin.sub_left
- \+ *lemma* add_comm_group.is_Z_bilin.sub_right
- \+ *lemma* add_comm_group.is_Z_bilin.zero
- \+ *lemma* add_comm_group.is_Z_bilin.zero_left
- \+ *lemma* add_comm_group.is_Z_bilin.zero_right
- \+ *lemma* dense_embedding.continuous_extend_of_cauchy
- \+ *theorem* dense_embedding.extend_Z_bilin
- \+ *lemma* group_separation_rel
- \+ *lemma* is_Z_bilin.tendsto_zero_left
- \+ *lemma* is_Z_bilin.tendsto_zero_right
- \+ *lemma* tendsto_sub_comap_self
- \+ *lemma* to_uniform_space_eq
- \+ *def* topological_add_group.to_uniform_space
- \+ *lemma* topological_add_group_is_uniform
- \+ *theorem* uniform_add_group.mk'
- \+ *lemma* uniform_continuous_add'
- \+ *lemma* uniform_continuous_add
- \+ *lemma* uniform_continuous_neg'
- \+ *lemma* uniform_continuous_neg
- \+ *lemma* uniform_continuous_of_continuous
- \+ *lemma* uniform_continuous_of_tendsto_zero
- \+ *lemma* uniform_continuous_sub'
- \+ *lemma* uniform_continuous_sub
- \+ *lemma* uniform_embedding_translate
- \+ *lemma* uniformity_eq_comap_nhds_zero'
- \+ *lemma* uniformity_eq_comap_nhds_zero
- \+ *lemma* uniformity_translate

Added src/topology/algebra/uniform_ring.lean
- \+ *lemma* uniform_space.completion.coe_mul
- \+ *lemma* uniform_space.completion.coe_one
- \+ *lemma* uniform_space.completion.continuous_mul'
- \+ *lemma* uniform_space.completion.continuous_mul
- \+ *lemma* uniform_space.ring_sep_quot
- \+ *lemma* uniform_space.ring_sep_rel
- \+ *def* uniform_space.sep_quot_equiv_ring_quot

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/polynomial.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/uniform_space/basic.lean
- \- *def* cauchy
- \- *lemma* cauchy_comap
- \- *lemma* cauchy_downwards
- \- *lemma* cauchy_iff
- \- *lemma* cauchy_iff_exists_le_nhds
- \- *lemma* cauchy_map
- \- *lemma* cauchy_map_iff
- \- *lemma* cauchy_map_iff_exists_tendsto
- \- *lemma* cauchy_nhds
- \- *lemma* cauchy_of_totally_bounded_of_ultrafilter
- \- *lemma* cauchy_prod
- \- *lemma* cauchy_pure
- \- *def* cauchy_seq
- \- *lemma* cauchy_seq_iff_prod_map
- \- *theorem* cauchy_seq_tendsto_of_complete
- \- *lemma* closure_image_mem_nhds_of_uniform_embedding
- \- *lemma* compact_iff_totally_bounded_complete
- \- *lemma* compact_of_totally_bounded_is_closed
- \- *lemma* complete_space_extension
- \- *lemma* complete_space_of_is_complete_univ
- \- *lemma* complete_univ
- \- *lemma* dense_embedding.continuous_extend_of_cauchy
- \- *lemma* is_closed_of_is_complete
- \- *def* is_complete
- \- *lemma* is_complete_image_iff
- \- *lemma* is_complete_of_is_closed
- \- *lemma* le_nhds_iff_adhp_of_cauchy
- \- *theorem* le_nhds_lim_of_cauchy
- \- *lemma* le_nhds_of_cauchy_adhp
- \- *def* separated
- \- *theorem* separated_def'
- \- *theorem* separated_def
- \- *lemma* separated_equiv
- \- *def* totally_bounded
- \- *lemma* totally_bounded_closure
- \- *lemma* totally_bounded_empty
- \- *lemma* totally_bounded_iff_filter
- \- *theorem* totally_bounded_iff_subset
- \- *lemma* totally_bounded_iff_ultrafilter
- \- *lemma* totally_bounded_image
- \- *lemma* totally_bounded_preimage
- \- *lemma* totally_bounded_subset
- \- *lemma* uniform_continuous_uniformly_extend
- \- *lemma* uniform_embedding.dense_embedding
- \- *lemma* uniform_embedding.embedding
- \- *lemma* uniform_embedding.prod
- \- *lemma* uniform_embedding.uniform_continuous
- \- *lemma* uniform_embedding.uniform_continuous_iff
- \- *def* uniform_embedding
- \- *lemma* uniform_embedding_comap
- \- *theorem* uniform_embedding_def'
- \- *theorem* uniform_embedding_def
- \- *lemma* uniform_embedding_subtype_emb
- \- *lemma* uniform_extend_subtype
- \- *lemma* uniformly_extend_exists
- \- *lemma* uniformly_extend_of_emb
- \- *lemma* uniformly_extend_spec

Added src/topology/uniform_space/cauchy.lean
- \+ *def* cauchy
- \+ *lemma* cauchy_comap
- \+ *lemma* cauchy_downwards
- \+ *lemma* cauchy_iff
- \+ *lemma* cauchy_iff_exists_le_nhds
- \+ *lemma* cauchy_map
- \+ *lemma* cauchy_map_iff
- \+ *lemma* cauchy_map_iff_exists_tendsto
- \+ *lemma* cauchy_nhds
- \+ *lemma* cauchy_of_totally_bounded_of_ultrafilter
- \+ *lemma* cauchy_prod
- \+ *lemma* cauchy_pure
- \+ *def* cauchy_seq
- \+ *lemma* cauchy_seq_iff_prod_map
- \+ *theorem* cauchy_seq_tendsto_of_complete
- \+ *lemma* compact_iff_totally_bounded_complete
- \+ *lemma* compact_of_totally_bounded_is_closed
- \+ *lemma* complete_space_of_is_complete_univ
- \+ *lemma* complete_univ
- \+ *def* is_complete
- \+ *lemma* is_complete_of_is_closed
- \+ *lemma* le_nhds_iff_adhp_of_cauchy
- \+ *theorem* le_nhds_lim_of_cauchy
- \+ *lemma* le_nhds_of_cauchy_adhp
- \+ *def* totally_bounded
- \+ *lemma* totally_bounded_closure
- \+ *lemma* totally_bounded_empty
- \+ *lemma* totally_bounded_iff_filter
- \+ *theorem* totally_bounded_iff_subset
- \+ *lemma* totally_bounded_iff_ultrafilter
- \+ *lemma* totally_bounded_image
- \+ *lemma* totally_bounded_subset

Added src/topology/uniform_space/complete_separated.lean
- \+ *lemma* is_closed_of_is_complete

Modified src/topology/uniform_space/completion.lean
- \- *lemma* add_comm_group.is_Z_bilin.neg_left
- \- *lemma* add_comm_group.is_Z_bilin.neg_right
- \- *lemma* add_comm_group.is_Z_bilin.sub_left
- \- *lemma* add_comm_group.is_Z_bilin.sub_right
- \- *lemma* add_comm_group.is_Z_bilin.zero
- \- *lemma* add_comm_group.is_Z_bilin.zero_left
- \- *lemma* add_comm_group.is_Z_bilin.zero_right
- \- *theorem* dense_embedding.extend_Z_bilin
- \- *lemma* is_Z_bilin.tendsto_zero_left
- \- *lemma* is_Z_bilin.tendsto_zero_right
- \- *lemma* tendsto_sub_comap_self
- \- *lemma* uniform_space.comap_quotient_eq_uniformity
- \- *lemma* uniform_space.comap_quotient_le_uniformity
- \- *lemma* uniform_space.completion.coe_add
- \- *lemma* uniform_space.completion.coe_mul
- \- *lemma* uniform_space.completion.coe_neg
- \- *lemma* uniform_space.completion.coe_one
- \- *lemma* uniform_space.completion.coe_zero
- \- *lemma* uniform_space.completion.continuous_mul'
- \- *lemma* uniform_space.completion.continuous_mul
- \- *lemma* uniform_space.completion.is_add_group_hom_extension
- \- *lemma* uniform_space.completion.is_add_group_hom_map
- \- *lemma* uniform_space.completion.is_add_group_hom_prod
- \- *lemma* uniform_space.eq_of_separated_of_uniform_continuous
- \- *lemma* uniform_space.separated_of_uniform_continuous
- \- *lemma* uniform_space.separation_prod
- \- *def* uniform_space.separation_quotient.lift
- \- *lemma* uniform_space.separation_quotient.lift_mk
- \- *def* uniform_space.separation_quotient.map
- \- *lemma* uniform_space.separation_quotient.map_comp
- \- *lemma* uniform_space.separation_quotient.map_id
- \- *lemma* uniform_space.separation_quotient.map_mk
- \- *lemma* uniform_space.separation_quotient.map_unique
- \- *lemma* uniform_space.separation_quotient.uniform_continuous_lift
- \- *lemma* uniform_space.separation_quotient.uniform_continuous_map
- \- *def* uniform_space.separation_quotient
- \- *def* uniform_space.separation_setoid
- \- *lemma* uniform_space.uniform_continuous_quotient
- \- *lemma* uniform_space.uniform_continuous_quotient_lift
- \- *lemma* uniform_space.uniform_continuous_quotient_lift₂
- \- *lemma* uniform_space.uniform_continuous_quotient_mk
- \- *lemma* uniform_space.uniformity_quotient

Added src/topology/uniform_space/separation.lean
- \+ *def* separated
- \+ *theorem* separated_def'
- \+ *theorem* separated_def
- \+ *lemma* separated_equiv
- \+ *lemma* uniform_space.comap_quotient_eq_uniformity
- \+ *lemma* uniform_space.comap_quotient_le_uniformity
- \+ *lemma* uniform_space.eq_of_separated_of_uniform_continuous
- \+ *lemma* uniform_space.separated_of_uniform_continuous
- \+ *lemma* uniform_space.separation_prod
- \+ *def* uniform_space.separation_quotient.lift
- \+ *lemma* uniform_space.separation_quotient.lift_mk
- \+ *def* uniform_space.separation_quotient.map
- \+ *lemma* uniform_space.separation_quotient.map_comp
- \+ *lemma* uniform_space.separation_quotient.map_id
- \+ *lemma* uniform_space.separation_quotient.map_mk
- \+ *lemma* uniform_space.separation_quotient.map_unique
- \+ *lemma* uniform_space.separation_quotient.uniform_continuous_lift
- \+ *lemma* uniform_space.separation_quotient.uniform_continuous_map
- \+ *def* uniform_space.separation_quotient
- \+ *def* uniform_space.separation_setoid
- \+ *lemma* uniform_space.uniform_continuous_quotient
- \+ *lemma* uniform_space.uniform_continuous_quotient_lift
- \+ *lemma* uniform_space.uniform_continuous_quotient_lift₂
- \+ *lemma* uniform_space.uniform_continuous_quotient_mk
- \+ *lemma* uniform_space.uniformity_quotient

Added src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* closure_image_mem_nhds_of_uniform_embedding
- \+ *lemma* complete_space_extension
- \+ *lemma* is_complete_image_iff
- \+ *lemma* totally_bounded_preimage
- \+ *lemma* uniform_continuous_uniformly_extend
- \+ *lemma* uniform_embedding.dense_embedding
- \+ *lemma* uniform_embedding.embedding
- \+ *lemma* uniform_embedding.prod
- \+ *lemma* uniform_embedding.uniform_continuous
- \+ *lemma* uniform_embedding.uniform_continuous_iff
- \+ *def* uniform_embedding
- \+ *lemma* uniform_embedding_comap
- \+ *theorem* uniform_embedding_def'
- \+ *theorem* uniform_embedding_def
- \+ *lemma* uniform_embedding_subtype_emb
- \+ *lemma* uniform_extend_subtype
- \+ *lemma* uniformly_extend_exists
- \+ *lemma* uniformly_extend_of_emb
- \+ *lemma* uniformly_extend_spec



## [2019-03-05 09:50:45+01:00](https://github.com/leanprover-community/mathlib/commit/708c0cf)
feat(data/multiset): add monad instance ([#744](https://github.com/leanprover-community/mathlib/pull/744))
#### Estimated changes
Modified src/data/multiset.lean




## [2019-03-05 09:44:51+01:00](https://github.com/leanprover-community/mathlib/commit/3525d21)
refactor(topology/metric_space/lipschitz): Simplify proof in banach contraction ([#788](https://github.com/leanprover-community/mathlib/pull/788))
#### Estimated changes
Modified src/topology/metric_space/lipschitz.lean
- \- *lemma* lipschitz_with.dist_bound_of_contraction



## [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/b9f88d1)
feat(data/finset): add card_sdiff
#### Estimated changes
Modified src/data/finset.lean
- \+/\- *theorem* finset.card_disjoint_union
- \+ *theorem* finset.card_sdiff

Modified src/data/fintype.lean




## [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/682f4b5)
feat(linear_algebra): module (vector space) structure for finsupp, matrix, and mv polynomials
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *def* finsupp.equiv_fun_on_fintype
- \+ *lemma* finsupp.ext_iff
- \+ *lemma* finsupp.filter_curry
- \+ *lemma* finsupp.filter_sum
- \+ *lemma* finsupp.filter_zero
- \+ *lemma* finsupp.injective_single
- \+ *lemma* finsupp.map_domain_apply
- \+ *lemma* finsupp.map_domain_notin_range
- \+ *lemma* finsupp.map_range_finset_sum
- \+ *lemma* finsupp.map_range_multiset_sum
- \+ *def* finsupp.restrict_support_equiv
- \+ *lemma* finsupp.single_eq_single_iff
- \+ *lemma* finsupp.support_curry

Modified src/data/multivariate_polynomial.lean
- \+ *lemma* mv_polynomial.smul_eq_C_mul
- \+ *lemma* mv_polynomial.smul_eval

Modified src/field_theory/finite.lean
- \+/\- *def* finite_field.field_of_integral_domain
- \+ *lemma* finite_field.pow_card_sub_one_eq_one

Added src/field_theory/mv_polynomial.lean
- \+ *def* mv_polynomial.R
- \+ *lemma* mv_polynomial.degrees_indicator
- \+ *lemma* mv_polynomial.dim_R
- \+ *lemma* mv_polynomial.eq_zero_of_eval_eq_zero
- \+ *lemma* mv_polynomial.eval_indicator_apply_eq_one
- \+ *lemma* mv_polynomial.eval_indicator_apply_eq_zero
- \+ *def* mv_polynomial.evalᵢ
- \+ *def* mv_polynomial.evalₗ
- \+ *lemma* mv_polynomial.evalₗ_apply
- \+ *def* mv_polynomial.indicator
- \+ *lemma* mv_polynomial.indicator_mem_restrict_degree
- \+ *lemma* mv_polynomial.ker_evalₗ
- \+ *lemma* mv_polynomial.map_restrict_dom_evalₗ
- \+ *lemma* mv_polynomial.range_evalᵢ

Added src/linear_algebra/finsupp.lean
- \+ *lemma* cardinal_lt_omega_of_dim_lt_omega
- \+ *lemma* cardinal_mk_eq_cardinal_mk_field_pow_dim
- \+ *lemma* eq_bot_iff_dim_eq_zero
- \+ *lemma* equiv_of_dim_eq_dim
- \+ *lemma* finsupp.dim_eq
- \+ *lemma* finsupp.disjoint_lsingle_lsingle
- \+ *lemma* finsupp.infi_ker_lapply_le_bot
- \+ *lemma* finsupp.is_basis_single
- \+ *lemma* finsupp.ker_lsingle
- \+ *def* finsupp.lapply
- \+ *lemma* finsupp.lapply_apply
- \+ *lemma* finsupp.linear_independent_single
- \+ *def* finsupp.lmap_domain
- \+ *lemma* finsupp.lmap_domain_apply
- \+ *def* finsupp.lsingle
- \+ *lemma* finsupp.lsingle_apply
- \+ *lemma* finsupp.lsingle_range_le_ker_lapply
- \+ *def* finsupp.lsubtype_domain
- \+ *lemma* finsupp.lsubtype_domain_apply
- \+ *lemma* finsupp.mem_restrict_dom
- \+ *def* finsupp.restrict_dom
- \+ *def* finsupp.restrict_dom_equiv_finsupp
- \+ *lemma* finsupp.span_single_image
- \+ *lemma* finsupp.supr_lsingle_range
- \+ *lemma* injective_of_surjective
- \+ *lemma* mv_polynomial.dim_mv_polynomial
- \+ *lemma* mv_polynomial.is_basis_monomials
- \+ *lemma* mv_polynomial.map_range_eq_map
- \+ *lemma* mv_polynomial.mem_restrict_degree
- \+ *lemma* mv_polynomial.mem_restrict_degree_iff_sup
- \+ *lemma* mv_polynomial.mem_restrict_total_degree
- \+ *def* mv_polynomial.restrict_degree
- \+ *def* mv_polynomial.restrict_total_degree

Added src/linear_algebra/matrix.lean
- \+ *lemma* matrix.diagonal_comp_std_basis
- \+ *lemma* matrix.diagonal_to_lin
- \+ *def* matrix.eval
- \+ *lemma* matrix.ker_diagonal_to_lin
- \+ *lemma* matrix.mul_to_lin
- \+ *lemma* matrix.proj_diagonal
- \+ *lemma* matrix.range_diagonal
- \+ *lemma* matrix.rank_diagonal
- \+ *lemma* matrix.rank_vec_mul_vec
- \+ *def* matrix.to_lin
- \+ *lemma* matrix.to_lin_add
- \+ *lemma* matrix.to_lin_apply
- \+ *lemma* matrix.to_lin_zero



## [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/738778a)
feat(data/matrix): basic definitions: transpose; row & column matrix; vector/matrix multiplication
#### Estimated changes
Modified src/data/matrix.lean
- \+ *def* matrix.col
- \+ *def* matrix.mul_vec
- \+ *lemma* matrix.mul_vec_diagonal
- \+ *def* matrix.row
- \+ *def* matrix.transpose
- \+ *def* matrix.vec_mul
- \+ *def* matrix.vec_mul_vec
- \+ *lemma* matrix.vec_mul_vec_eq



## [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/528ff93)
refactor(linear_algebra): move multivariate_polynomial to data
#### Estimated changes
Modified src/category_theory/instances/rings.lean


Renamed src/linear_algebra/multivariate_polynomial.lean to src/data/multivariate_polynomial.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/polynomial.lean




## [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/891a192)
refactor(ring_theory): move matrix to data and determinant to linear_algebra
#### Estimated changes
Modified src/data/matrix.lean


Modified src/linear_algebra/determinant.lean




## [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/10a586b)
feat(linear_algebra): add module (vector_space) structure for function spaces
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *def* equiv.to_linear_equiv
- \+ *lemma* linear_equiv.eq_bot_of_equiv
- \+ *def* linear_equiv.smul_of_ne_zero
- \+ *def* linear_equiv.smul_of_unit
- \+ *lemma* linear_map.comp_cod_restrict
- \+ *def* linear_map.diag
- \+ *lemma* linear_map.disjoint_std_basis_std_basis
- \+ *lemma* linear_map.infi_ker_proj
- \+ *def* linear_map.infi_ker_proj_equiv
- \+ *lemma* linear_map.infi_ker_proj_le_supr_range_std_basis
- \+ *lemma* linear_map.ker_pi
- \+ *lemma* linear_map.ker_std_basis
- \+ *def* linear_map.pi
- \+ *lemma* linear_map.pi_apply
- \+ *lemma* linear_map.pi_comp
- \+ *lemma* linear_map.pi_eq_zero
- \+ *lemma* linear_map.pi_zero
- \+ *def* linear_map.proj
- \+ *lemma* linear_map.proj_apply
- \+ *lemma* linear_map.proj_comp_std_basis
- \+ *lemma* linear_map.proj_pi
- \+ *lemma* linear_map.proj_std_basis_ne
- \+ *lemma* linear_map.proj_std_basis_same
- \+ *def* linear_map.std_basis
- \+ *lemma* linear_map.std_basis_apply
- \+ *lemma* linear_map.std_basis_ne
- \+ *lemma* linear_map.std_basis_same
- \+ *lemma* linear_map.subtype_comp_cod_restrict
- \+ *lemma* linear_map.supr_range_std_basis
- \+ *lemma* linear_map.supr_range_std_basis_eq_infi_ker_proj
- \+ *lemma* linear_map.supr_range_std_basis_le_infi_ker_proj
- \+ *lemma* linear_map.update_apply
- \+ *lemma* submodule.disjoint_iff_comap_eq_bot
- \+ *lemma* submodule.eq_zero_of_bot_submodule
- \+ *lemma* submodule.mem_supr_of_mem
- \+ *lemma* submodule.span_univ

Modified src/linear_algebra/basis.lean
- \+ *lemma* linear_independent_Union_finite
- \+ *lemma* pi.is_basis_fun
- \+ *lemma* pi.is_basis_std_basis
- \+ *lemma* pi.linear_independent_std_basis

Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_fun'
- \+ *lemma* dim_fun
- \+ *lemma* dim_pi



## [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/332121d)
feat(data/fintype): card_univ and card_univ_diff
#### Estimated changes
Modified src/data/fintype.lean
- \+ *lemma* finset.card_univ
- \+ *lemma* finset.card_univ_diff



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c0b1eb1)
refactor(data/finset): correct name sdiff_disjoint -> disjoint_sdiff; add sdiff_disjoint
#### Estimated changes
Modified src/data/finset.lean
- \+/\- *lemma* finset.disjoint_sdiff
- \+ *lemma* finset.sdiff_disjoint

Modified src/topology/algebra/infinite_sum.lean




## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/b3c749b)
remove superflous parameter from bot_eq_zero
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+/\- *lemma* bot_eq_zero



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/73f1a08)
feat(data/finset): add filter_empty, filter_subset_filter, prod_filter
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_filter

Modified src/data/finset.lean
- \+ *lemma* finset.filter_empty
- \+ *lemma* finset.filter_subset_filter



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/b9ead4d)
feat(data/finset): add disjoint_bind_left/right
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* finset.disjoint_bind_left
- \+ *lemma* finset.disjoint_bind_right



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/f82f5f2)
refactor(algebra): canonically_ordered_monoid extends order_bot
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* bot_eq_zero

Modified src/algebra/ordered_ring.lean


Modified src/data/multiset.lean


Modified src/data/nat/enat.lean


Modified src/data/real/nnreal.lean


Modified src/set_theory/cardinal.lean




## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/f07a558)
feat(data/equiv): add subtype_pi_equiv_pi
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.subtype_pi_equiv_pi



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/8070c05)
feat(data/set/lattice): more rules for disjoint sets
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *theorem* set.disjoint_compl
- \+/\- *theorem* set.disjoint_diff
- \+ *theorem* set.disjoint_image_image
- \+ *theorem* set.disjoint_singleton_left
- \+ *theorem* set.disjoint_singleton_right



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c53ac41)
feat(data/set): relate range and image to Union
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.image_eq_Union
- \+ *lemma* set.range_eq_Union



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/41038ba)
feat(data/set): add exists_maximal_wrt
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* set.finite.exists_maximal_wrt



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/146d73c)
feat(data/set): add finite_image_iff_on
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *theorem* set.finite_image_iff_on
- \+/\- *theorem* set.finite_of_finite_image
- \+ *theorem* set.finite_of_finite_image_on



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/84a5f4d)
feat(data/set): add subset_image_iff and subset_range_iff
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* set.subset_image_iff
- \+ *lemma* set.subset_range_iff



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/cbe2f61)
feat(logic/function): add inv_fun_neg
#### Estimated changes
Modified src/logic/function.lean
- \+ *lemma* function.inv_fun_neg



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/73db4c7)
feat(logic/function): add injective.ne
#### Estimated changes
Modified src/logic/function.lean
- \+ *lemma* function.injective.ne



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c819617)
feat(logic): add plift.down_inj
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* plift.down_inj



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/985445f)
feat(linear_algebra/multivariate_polynomial): relate total_degree to degrees, add, zero, mul
#### Estimated changes
Modified src/linear_algebra/multivariate_polynomial.lean
- \+ *lemma* mv_polynomial.total_degree_C
- \+ *lemma* mv_polynomial.total_degree_add
- \+ *lemma* mv_polynomial.total_degree_eq
- \+ *lemma* mv_polynomial.total_degree_finset_prod
- \+ *lemma* mv_polynomial.total_degree_le_degrees_card
- \+ *lemma* mv_polynomial.total_degree_list_prod
- \+ *lemma* mv_polynomial.total_degree_mul
- \+ *lemma* mv_polynomial.total_degree_multiset_prod
- \+ *lemma* mv_polynomial.total_degree_one
- \+ *lemma* mv_polynomial.total_degree_zero



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/78fd58d)
feat(linear_algebra/multivariate_polynomial): add degrees
#### Estimated changes
Modified src/linear_algebra/multivariate_polynomial.lean
- \+/\- *def* mv_polynomial.degree_of
- \+ *def* mv_polynomial.degrees
- \+ *lemma* mv_polynomial.degrees_C
- \+ *lemma* mv_polynomial.degrees_X
- \+ *lemma* mv_polynomial.degrees_add
- \+ *lemma* mv_polynomial.degrees_monomial
- \+ *lemma* mv_polynomial.degrees_monomial_eq
- \+ *lemma* mv_polynomial.degrees_mul
- \+ *lemma* mv_polynomial.degrees_neg
- \+ *lemma* mv_polynomial.degrees_one
- \+ *lemma* mv_polynomial.degrees_pow
- \+ *lemma* mv_polynomial.degrees_prod
- \+ *lemma* mv_polynomial.degrees_sub
- \+ *lemma* mv_polynomial.degrees_sum
- \+ *lemma* mv_polynomial.degrees_zero
- \+/\- *def* mv_polynomial.vars



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c2d8bc2)
feat(data/finsupp): relatie to_multiset to 0, +, single, card, map, prod, and to_finset
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* finsupp.card_to_multiset
- \+ *lemma* finsupp.prod_to_multiset
- \+ *lemma* finsupp.to_finset_to_multiset
- \+ *lemma* finsupp.to_multiset_add
- \+ *lemma* finsupp.to_multiset_map
- \+ *lemma* finsupp.to_multiset_single
- \+ *lemma* finsupp.to_multiset_zero



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/857842d)
feat(data/finsupp): add support_mul
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* finsupp.support_mul



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/a77797f)
feat(data/multiset): add prod_smul
#### Estimated changes
Modified src/data/multiset.lean
- \+ *lemma* multiset.prod_smul



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/e924745)
feat(data/finset): add multiset.count_sup
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* multiset.count_sup



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/e07cac5)
feat(data/finset): add to_finset_smul
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* multiset.to_finset_smul



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/f24b01b)
feat(algebra/group_power): smul and pow are monoid homs
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *theorem* is_add_monoid_hom.map_smul
- \+ *theorem* is_monoid_hom.map_pow



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/32642e1)
feat(linear_algebra): add dim_sup_add_dim_inf_eq
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.range_of_le
- \+ *lemma* submodule.subtype_comp_of_le

Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_add_dim_split
- \+ *lemma* dim_sup_add_dim_inf_eq



## [2019-03-04 16:26:09+01:00](https://github.com/leanprover-community/mathlib/commit/f46f0a6)
feat(tactic/fin_cases): case bashing on finset, list, and fintype hypotheses. ([#775](https://github.com/leanprover-community/mathlib/pull/775))
#### Estimated changes
Modified docs/tactics.md


Modified src/data/int/basic.lean
- \+ *theorem* int.add_def
- \+ *theorem* int.mul_def

Modified src/data/nat/basic.lean
- \+ *theorem* nat.add_def
- \+ *theorem* nat.mul_def

Modified src/tactic/fin_cases.lean


Modified test/fin_cases.lean




## [2019-03-04 12:37:27+01:00](https://github.com/leanprover-community/mathlib/commit/6cd0341)
docs(extras/tactic_writing): add ``%%(reflect n)`` to the tactic writing guide ([#786](https://github.com/leanprover-community/mathlib/pull/786))
#### Estimated changes
Modified docs/extras/tactic_writing.md




## [2019-03-03 19:05:12+01:00](https://github.com/leanprover-community/mathlib/commit/201413b)
chore(topology): Splits topology.basic and topology.continuity ([#785](https://github.com/leanprover-community/mathlib/pull/785))
Also, the most basic aspects of continuity are now in topology.basic
#### Estimated changes
Modified src/category_theory/instances/topological_spaces.lean


Modified src/data/analysis/topology.lean


Modified src/topology/algebra/topological_structures.lean


Added src/topology/bases.lean
- \+ *lemma* topological_space.Union_basis_of_is_open
- \+ *lemma* topological_space.is_open_Union_countable
- \+ *lemma* topological_space.is_open_generated_countable_inter
- \+ *lemma* topological_space.is_open_of_is_topological_basis
- \+ *lemma* topological_space.is_open_sUnion_countable
- \+ *def* topological_space.is_topological_basis
- \+ *lemma* topological_space.is_topological_basis_of_open_of_nhds
- \+ *lemma* topological_space.is_topological_basis_of_subbasis
- \+ *lemma* topological_space.mem_basis_subset_of_mem_open
- \+ *lemma* topological_space.mem_nhds_of_is_topological_basis
- \+ *lemma* topological_space.sUnion_basis_of_is_open
- \+ *lemma* topological_space.second_countable_topology_induced

Modified src/topology/basic.lean
- \- *lemma* closure_singleton
- \- *lemma* coinduced_compose
- \- *lemma* coinduced_id
- \- *lemma* coinduced_inf
- \- *lemma* coinduced_infi
- \- *lemma* coinduced_mono
- \- *lemma* coinduced_top
- \- *def* compact
- \- *lemma* compact_Union_of_compact
- \- *lemma* compact_adherence_nhdset
- \- *lemma* compact_bUnion_of_compact
- \- *lemma* compact_diff
- \- *lemma* compact_elim_finite_subcover
- \- *lemma* compact_elim_finite_subcover_image
- \- *lemma* compact_empty
- \- *lemma* compact_iff_finite_subcover
- \- *lemma* compact_iff_ultrafilter_le_nhds
- \- *lemma* compact_inter
- \- *lemma* compact_of_closed
- \- *lemma* compact_of_finite
- \- *lemma* compact_of_finite_subcover
- \- *lemma* compact_of_is_closed_subset
- \- *lemma* compact_singleton
- \- *lemma* compact_union_of_compact
- \- *lemma* compact_univ
- \- *lemma* compl_singleton_mem_nhds
- \- *def* connected_component
- \+ *lemma* continuous.comp
- \+ *lemma* continuous.tendsto
- \+ *def* continuous
- \+ *def* continuous_at
- \+ *lemma* continuous_at_iff_ultrafilter
- \+ *def* continuous_at_within
- \+ *lemma* continuous_const
- \+ *lemma* continuous_id
- \+ *lemma* continuous_if
- \+ *lemma* continuous_iff_continuous_at
- \+ *lemma* continuous_iff_is_closed
- \+ *lemma* continuous_iff_ultrafilter
- \+ *def* continuous_on
- \- *theorem* eq_irreducible_component
- \- *lemma* eq_of_nhds_eq_nhds
- \- *lemma* eq_of_nhds_neq_bot
- \- *lemma* eq_top_of_singletons_open
- \- *theorem* exists_irreducible
- \- *theorem* exists_mem_inter
- \- *theorem* exists_open_singleton_of_fintype
- \- *lemma* gc_induced_coinduced
- \- *lemma* gc_nhds
- \- *lemma* generate_from_le
- \- *lemma* generate_from_le_iff_subset_is_open
- \- *lemma* generate_from_mono
- \- *def* gi_generate_from
- \+ *lemma* image_closure_subset_closure_image
- \- *lemma* induced_bot
- \- *lemma* induced_compose
- \- *lemma* induced_generate_from_eq
- \- *lemma* induced_id
- \- *lemma* induced_le_iff_le_coinduced
- \- *lemma* induced_mono
- \- *lemma* induced_sup
- \- *lemma* induced_supr
- \- *def* irreducible_component
- \- *theorem* irreducible_component_subset_connected_component
- \- *theorem* irreducible_exists_mem_inter
- \- *def* is_clopen
- \- *theorem* is_clopen_compl
- \- *theorem* is_clopen_compl_iff
- \- *theorem* is_clopen_diff
- \- *theorem* is_clopen_empty
- \- *theorem* is_clopen_iff
- \- *theorem* is_clopen_inter
- \- *theorem* is_clopen_union
- \- *theorem* is_clopen_univ
- \- *theorem* is_closed_connected_component
- \- *lemma* is_closed_induced_iff
- \- *theorem* is_closed_irreducible_component
- \- *lemma* is_closed_singleton
- \- *def* is_connected
- \- *theorem* is_connected_closure
- \- *theorem* is_connected_connected_component
- \- *theorem* is_connected_empty
- \- *theorem* is_connected_of_is_irreducible
- \- *theorem* is_connected_sUnion
- \- *theorem* is_connected_singleton
- \- *theorem* is_connected_union
- \- *def* is_irreducible
- \- *theorem* is_irreducible_closure
- \- *theorem* is_irreducible_empty
- \- *theorem* is_irreducible_irreducible_component
- \- *theorem* is_irreducible_singleton
- \- *lemma* is_open_coinduced
- \- *lemma* is_open_discrete
- \- *lemma* is_open_induced_iff
- \- *def* is_totally_disconnected
- \- *theorem* is_totally_disconnected_empty
- \- *theorem* is_totally_disconnected_of_is_totally_separated
- \- *theorem* is_totally_disconnected_singleton
- \- *def* is_totally_separated
- \- *theorem* is_totally_separated_empty
- \- *theorem* is_totally_separated_singleton
- \- *lemma* le_of_nhds_le_nhds
- \- *lemma* lim_eq
- \- *lemma* lim_nhds_eq
- \- *lemma* lim_nhds_eq_of_closure
- \- *theorem* map_nhds_induced_of_surjective
- \+ *lemma* mem_closure
- \- *theorem* mem_connected_component
- \- *theorem* mem_irreducible_component
- \- *theorem* mem_nhds_induced
- \- *theorem* mem_nhds_subtype
- \- *theorem* mem_nhds_within_subtype
- \- *lemma* mk_of_closure_sets
- \- *lemma* nhds_Sup
- \- *lemma* nhds_bot
- \- *lemma* nhds_cons
- \- *lemma* nhds_discrete
- \- *lemma* nhds_eq_nhds_iff
- \- *theorem* nhds_induced
- \- *lemma* nhds_is_closed
- \- *lemma* nhds_le_nhds_iff
- \- *lemma* nhds_list
- \- *lemma* nhds_mono
- \- *lemma* nhds_nil
- \- *theorem* nhds_subtype
- \- *lemma* nhds_sup
- \- *lemma* nhds_supr
- \- *lemma* nhds_top
- \- *theorem* nhds_within_eq_map_subtype_val
- \- *theorem* nhds_within_subtype
- \- *theorem* normal_separation
- \+ *lemma* open_dom_of_pcontinuous
- \+ *def* pcontinuous
- \+ *lemma* pcontinuous_iff'
- \- *theorem* principal_subtype
- \- *lemma* quotient_dense_of_dense
- \- *theorem* subset_connected_component
- \- *lemma* t2_iff_nhds
- \- *lemma* t2_iff_ultrafilter
- \- *lemma* t2_separation
- \- *lemma* tendsto_nhds_unique
- \- *theorem* tendsto_nhds_within_iff_subtype
- \- *lemma* topological_space.Union_basis_of_is_open
- \- *def* topological_space.closeds
- \- *def* topological_space.coinduced
- \- *def* topological_space.generate_from
- \- *def* topological_space.induced
- \- *lemma* topological_space.is_open_Union_countable
- \- *lemma* topological_space.is_open_generated_countable_inter
- \- *lemma* topological_space.is_open_of_is_topological_basis
- \- *lemma* topological_space.is_open_sUnion_countable
- \- *def* topological_space.is_topological_basis
- \- *lemma* topological_space.is_topological_basis_of_open_of_nhds
- \- *lemma* topological_space.is_topological_basis_of_subbasis
- \- *lemma* topological_space.mem_basis_subset_of_mem_open
- \- *lemma* topological_space.mem_nhds_of_is_topological_basis
- \- *lemma* topological_space.nhds_generate_from
- \- *lemma* topological_space.nhds_mk_of_nhds
- \- *def* topological_space.nonempty_compacts
- \- *lemma* topological_space.opens.Sup_s
- \- *lemma* topological_space.opens.empty_eq
- \- *lemma* topological_space.opens.ext
- \- *def* topological_space.opens.gc
- \- *def* topological_space.opens.gi
- \- *lemma* topological_space.opens.gi_choice_val
- \- *lemma* topological_space.opens.inter_eq
- \- *def* topological_space.opens.interior
- \- *def* topological_space.opens.is_basis
- \- *lemma* topological_space.opens.is_basis_iff_cover
- \- *lemma* topological_space.opens.is_basis_iff_nbhd
- \- *lemma* topological_space.opens.union_eq
- \- *def* topological_space.opens
- \- *lemma* topological_space.sUnion_basis_of_is_open
- \- *lemma* topological_space.second_countable_topology_induced
- \- *lemma* topological_space.tendsto_nhds_generate_from

Modified src/topology/compact_open.lean


Renamed src/topology/continuity.lean to src/topology/constructions.lean
- \- *lemma* closure_induced
- \- *lemma* compact_image
- \- *lemma* compact_range
- \- *lemma* continuous.comp
- \- *lemma* continuous.tendsto
- \- *def* continuous
- \- *lemma* continuous_Inf_dom
- \- *lemma* continuous_Inf_rng
- \- *lemma* continuous_Prop
- \- *lemma* continuous_Sup_dom
- \- *lemma* continuous_Sup_rng
- \- *def* continuous_at
- \- *lemma* continuous_at_iff_ultrafilter
- \- *theorem* continuous_at_within.tendsto_nhds_within_image
- \- *def* continuous_at_within
- \- *theorem* continuous_at_within_iff_continuous_at_restrict
- \- *theorem* continuous_at_within_iff_ptendsto_res
- \- *theorem* continuous_at_within_univ
- \- *lemma* continuous_bot
- \- *lemma* continuous_coinduced_dom
- \- *lemma* continuous_coinduced_rng
- \- *lemma* continuous_const
- \- *theorem* continuous_generated_from
- \- *lemma* continuous_id
- \- *lemma* continuous_if
- \- *lemma* continuous_iff_continuous_at
- \- *lemma* continuous_iff_induced_le
- \- *lemma* continuous_iff_is_closed
- \- *lemma* continuous_iff_le_coinduced
- \- *lemma* continuous_iff_ultrafilter
- \- *lemma* continuous_induced_dom
- \- *lemma* continuous_induced_rng
- \- *lemma* continuous_inf_dom
- \- *lemma* continuous_inf_rng_left
- \- *lemma* continuous_inf_rng_right
- \- *lemma* continuous_infi_dom
- \- *lemma* continuous_infi_rng
- \- *lemma* continuous_le_dom
- \- *lemma* continuous_le_rng
- \- *lemma* continuous_of_discrete_topology
- \- *def* continuous_on
- \- *theorem* continuous_on_iff'
- \- *theorem* continuous_on_iff
- \- *theorem* continuous_on_iff_continuous_restrict
- \- *lemma* continuous_sup_dom_left
- \- *lemma* continuous_sup_dom_right
- \- *lemma* continuous_sup_rng
- \- *lemma* continuous_supr_dom
- \- *lemma* continuous_supr_rng
- \- *lemma* continuous_top
- \- *lemma* dense_embedding.closure_image_nhds_of_nhds
- \- *lemma* dense_embedding.closure_range
- \- *lemma* dense_embedding.comap_nhds_neq_bot
- \- *lemma* dense_embedding.continuous_extend
- \- *def* dense_embedding.extend
- \- *lemma* dense_embedding.extend_e_eq
- \- *lemma* dense_embedding.extend_eq
- \- *lemma* dense_embedding.inj_iff
- \- *theorem* dense_embedding.mk'
- \- *lemma* dense_embedding.self_sub_closure_image_preimage_of_open
- \- *lemma* dense_embedding.tendsto_comap_nhds_nhds
- \- *lemma* dense_embedding.tendsto_extend
- \- *lemma* embedding.closure_eq_preimage_closure_image
- \- *lemma* embedding.continuous
- \- *lemma* embedding.continuous_iff
- \- *lemma* embedding.map_nhds_eq
- \- *lemma* embedding.tendsto_nhds_iff
- \- *def* embedding
- \- *lemma* embedding_compose
- \- *lemma* embedding_id
- \- *lemma* embedding_is_closed
- \- *lemma* embedding_of_embedding_compose
- \- *lemma* embedding_open
- \- *lemma* embedding_prod_mk
- \- *lemma* image_closure_subset_closure_image
- \- *theorem* is_open_induced
- \- *theorem* is_open_induced_eq
- \- *lemma* is_open_map.of_inverse
- \- *lemma* is_open_map.to_quotient_map
- \- *def* is_open_map
- \- *lemma* is_open_map_iff_nhds_le
- \- *lemma* is_open_singleton_true
- \- *lemma* map_nhds_induced_eq
- \- *lemma* mem_closure
- \- *lemma* nhds_induced_eq_comap
- \- *theorem* nhds_within_le_comap
- \- *def* nonempty_compacts.to_closeds
- \- *lemma* open_dom_of_pcontinuous
- \- *def* pcontinuous
- \- *lemma* pcontinuous_iff'
- \- *def* quotient_map

Added src/topology/maps.lean
- \+ *lemma* continuous_Prop
- \+ *lemma* dense_embedding.closure_image_nhds_of_nhds
- \+ *lemma* dense_embedding.closure_range
- \+ *lemma* dense_embedding.comap_nhds_neq_bot
- \+ *lemma* dense_embedding.continuous_extend
- \+ *def* dense_embedding.extend
- \+ *lemma* dense_embedding.extend_e_eq
- \+ *lemma* dense_embedding.extend_eq
- \+ *lemma* dense_embedding.inj_iff
- \+ *theorem* dense_embedding.mk'
- \+ *lemma* dense_embedding.self_sub_closure_image_preimage_of_open
- \+ *lemma* dense_embedding.tendsto_comap_nhds_nhds
- \+ *lemma* dense_embedding.tendsto_extend
- \+ *lemma* embedding.closure_eq_preimage_closure_image
- \+ *lemma* embedding.continuous
- \+ *lemma* embedding.continuous_iff
- \+ *lemma* embedding.map_nhds_eq
- \+ *lemma* embedding.tendsto_nhds_iff
- \+ *def* embedding
- \+ *lemma* embedding_compose
- \+ *lemma* embedding_id
- \+ *lemma* embedding_is_closed
- \+ *lemma* embedding_of_embedding_compose
- \+ *lemma* embedding_open
- \+ *lemma* embedding_prod_mk
- \+ *lemma* is_open_map.of_inverse
- \+ *lemma* is_open_map.to_quotient_map
- \+ *def* is_open_map
- \+ *lemma* is_open_map_iff_nhds_le
- \+ *lemma* is_open_singleton_true
- \+ *def* quotient_map

Modified src/topology/metric_space/closeds.lean


Added src/topology/opens.lean
- \+ *def* topological_space.closeds
- \+ *def* topological_space.nonempty_compacts.to_closeds
- \+ *def* topological_space.nonempty_compacts
- \+ *lemma* topological_space.opens.Sup_s
- \+ *lemma* topological_space.opens.empty_eq
- \+ *lemma* topological_space.opens.ext
- \+ *def* topological_space.opens.gc
- \+ *def* topological_space.opens.gi
- \+ *lemma* topological_space.opens.gi_choice_val
- \+ *lemma* topological_space.opens.inter_eq
- \+ *def* topological_space.opens.interior
- \+ *def* topological_space.opens.is_basis
- \+ *lemma* topological_space.opens.is_basis_iff_cover
- \+ *lemma* topological_space.opens.is_basis_iff_nbhd
- \+ *lemma* topological_space.opens.union_eq
- \+ *def* topological_space.opens

Added src/topology/order.lean
- \+ *lemma* closure_induced
- \+ *lemma* coinduced_compose
- \+ *lemma* coinduced_id
- \+ *lemma* coinduced_inf
- \+ *lemma* coinduced_infi
- \+ *lemma* coinduced_mono
- \+ *lemma* coinduced_top
- \+ *lemma* continuous_Inf_dom
- \+ *lemma* continuous_Inf_rng
- \+ *lemma* continuous_Sup_dom
- \+ *lemma* continuous_Sup_rng
- \+ *theorem* continuous_at_within.tendsto_nhds_within_image
- \+ *theorem* continuous_at_within_iff_continuous_at_restrict
- \+ *theorem* continuous_at_within_iff_ptendsto_res
- \+ *theorem* continuous_at_within_univ
- \+ *lemma* continuous_bot
- \+ *lemma* continuous_coinduced_dom
- \+ *lemma* continuous_coinduced_rng
- \+ *theorem* continuous_generated_from
- \+ *lemma* continuous_iff_induced_le
- \+ *lemma* continuous_iff_le_coinduced
- \+ *lemma* continuous_induced_dom
- \+ *lemma* continuous_induced_rng
- \+ *lemma* continuous_inf_dom
- \+ *lemma* continuous_inf_rng_left
- \+ *lemma* continuous_inf_rng_right
- \+ *lemma* continuous_infi_dom
- \+ *lemma* continuous_infi_rng
- \+ *lemma* continuous_le_dom
- \+ *lemma* continuous_le_rng
- \+ *lemma* continuous_of_discrete_topology
- \+ *theorem* continuous_on_iff'
- \+ *theorem* continuous_on_iff
- \+ *theorem* continuous_on_iff_continuous_restrict
- \+ *lemma* continuous_sup_dom_left
- \+ *lemma* continuous_sup_dom_right
- \+ *lemma* continuous_sup_rng
- \+ *lemma* continuous_supr_dom
- \+ *lemma* continuous_supr_rng
- \+ *lemma* continuous_top
- \+ *lemma* eq_of_nhds_eq_nhds
- \+ *lemma* eq_top_of_singletons_open
- \+ *lemma* gc_induced_coinduced
- \+ *lemma* gc_nhds
- \+ *lemma* generate_from_le
- \+ *lemma* generate_from_le_iff_subset_is_open
- \+ *lemma* generate_from_mono
- \+ *def* gi_generate_from
- \+ *lemma* induced_bot
- \+ *lemma* induced_compose
- \+ *lemma* induced_generate_from_eq
- \+ *lemma* induced_id
- \+ *lemma* induced_le_iff_le_coinduced
- \+ *lemma* induced_mono
- \+ *lemma* induced_sup
- \+ *lemma* induced_supr
- \+ *lemma* is_closed_induced_iff
- \+ *lemma* is_open_coinduced
- \+ *lemma* is_open_discrete
- \+ *theorem* is_open_induced
- \+ *theorem* is_open_induced_eq
- \+ *lemma* is_open_induced_iff
- \+ *lemma* le_of_nhds_le_nhds
- \+ *lemma* map_nhds_induced_eq
- \+ *theorem* map_nhds_induced_of_surjective
- \+ *theorem* mem_nhds_induced
- \+ *theorem* mem_nhds_subtype
- \+ *theorem* mem_nhds_within_subtype
- \+ *lemma* mk_of_closure_sets
- \+ *lemma* nhds_Sup
- \+ *lemma* nhds_bot
- \+ *lemma* nhds_cons
- \+ *lemma* nhds_discrete
- \+ *theorem* nhds_induced
- \+ *lemma* nhds_induced_eq_comap
- \+ *lemma* nhds_list
- \+ *lemma* nhds_mono
- \+ *lemma* nhds_nil
- \+ *theorem* nhds_subtype
- \+ *lemma* nhds_sup
- \+ *lemma* nhds_supr
- \+ *lemma* nhds_top
- \+ *theorem* nhds_within_eq_map_subtype_val
- \+ *theorem* nhds_within_le_comap
- \+ *theorem* nhds_within_subtype
- \+ *theorem* principal_subtype
- \+ *lemma* quotient_dense_of_dense
- \+ *theorem* tendsto_nhds_within_iff_subtype
- \+ *def* topological_space.coinduced
- \+ *def* topological_space.generate_from
- \+ *def* topological_space.induced
- \+ *lemma* topological_space.nhds_generate_from
- \+ *lemma* topological_space.nhds_mk_of_nhds
- \+ *lemma* topological_space.tendsto_nhds_generate_from

Added src/topology/separation.lean
- \+ *lemma* closure_singleton
- \+ *lemma* compl_singleton_mem_nhds
- \+ *lemma* eq_of_nhds_neq_bot
- \+ *theorem* exists_open_singleton_of_fintype
- \+ *lemma* is_closed_singleton
- \+ *lemma* lim_eq
- \+ *lemma* lim_nhds_eq
- \+ *lemma* lim_nhds_eq_of_closure
- \+ *lemma* nhds_eq_nhds_iff
- \+ *lemma* nhds_is_closed
- \+ *lemma* nhds_le_nhds_iff
- \+ *theorem* normal_separation
- \+ *lemma* t2_iff_nhds
- \+ *lemma* t2_iff_ultrafilter
- \+ *lemma* t2_separation
- \+ *lemma* tendsto_nhds_unique

Modified src/topology/sequences.lean


Modified src/topology/stone_cech.lean


Added src/topology/subset_properties.lean
- \+ *def* compact
- \+ *lemma* compact_Union_of_compact
- \+ *lemma* compact_adherence_nhdset
- \+ *lemma* compact_bUnion_of_compact
- \+ *lemma* compact_diff
- \+ *lemma* compact_elim_finite_subcover
- \+ *lemma* compact_elim_finite_subcover_image
- \+ *lemma* compact_empty
- \+ *lemma* compact_iff_finite_subcover
- \+ *lemma* compact_iff_ultrafilter_le_nhds
- \+ *lemma* compact_image
- \+ *lemma* compact_inter
- \+ *lemma* compact_of_closed
- \+ *lemma* compact_of_finite
- \+ *lemma* compact_of_finite_subcover
- \+ *lemma* compact_of_is_closed_subset
- \+ *lemma* compact_range
- \+ *lemma* compact_singleton
- \+ *lemma* compact_union_of_compact
- \+ *lemma* compact_univ
- \+ *def* connected_component
- \+ *theorem* eq_irreducible_component
- \+ *theorem* exists_irreducible
- \+ *theorem* exists_mem_inter
- \+ *def* irreducible_component
- \+ *theorem* irreducible_component_subset_connected_component
- \+ *theorem* irreducible_exists_mem_inter
- \+ *def* is_clopen
- \+ *theorem* is_clopen_compl
- \+ *theorem* is_clopen_compl_iff
- \+ *theorem* is_clopen_diff
- \+ *theorem* is_clopen_empty
- \+ *theorem* is_clopen_iff
- \+ *theorem* is_clopen_inter
- \+ *theorem* is_clopen_union
- \+ *theorem* is_clopen_univ
- \+ *theorem* is_closed_connected_component
- \+ *theorem* is_closed_irreducible_component
- \+ *def* is_connected
- \+ *theorem* is_connected_closure
- \+ *theorem* is_connected_connected_component
- \+ *theorem* is_connected_empty
- \+ *theorem* is_connected_of_is_irreducible
- \+ *theorem* is_connected_sUnion
- \+ *theorem* is_connected_singleton
- \+ *theorem* is_connected_union
- \+ *def* is_irreducible
- \+ *theorem* is_irreducible_closure
- \+ *theorem* is_irreducible_empty
- \+ *theorem* is_irreducible_irreducible_component
- \+ *theorem* is_irreducible_singleton
- \+ *def* is_totally_disconnected
- \+ *theorem* is_totally_disconnected_empty
- \+ *theorem* is_totally_disconnected_of_is_totally_separated
- \+ *theorem* is_totally_disconnected_singleton
- \+ *def* is_totally_separated
- \+ *theorem* is_totally_separated_empty
- \+ *theorem* is_totally_separated_singleton
- \+ *theorem* mem_connected_component
- \+ *theorem* mem_irreducible_component
- \+ *theorem* subset_connected_component

Modified src/topology/uniform_space/basic.lean




## [2019-03-03 11:01:43-05:00](https://github.com/leanprover-community/mathlib/commit/1084868)
feat(analysis/{specific_limits,infinite_sum}): Cauchy of geometric bound ([#753](https://github.com/leanprover-community/mathlib/pull/753))
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+ *lemma* cauchy_seq_of_le_geometric

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* cauchy_seq_of_has_sum_dist



## [2019-03-03 13:19:35](https://github.com/leanprover-community/mathlib/commit/1f90e18)
feat(ring_theory/ideal_operations): Chinese Remainder Theorem ([#774](https://github.com/leanprover-community/mathlib/pull/774))
#### Estimated changes
Modified src/ring_theory/ideal_operations.lean
- \+ *theorem* ideal.bijective_quotient_inf_to_pi_quotient
- \+ *theorem* ideal.exists_sub_mem
- \+ *theorem* ideal.exists_sub_one_mem_and_mem
- \+ *theorem* ideal.is_ring_hom_quotient_inf_to_pi_quotient
- \+ *def* ideal.quotient_inf_to_pi_quotient



## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/fb8001d)
hopefully fixed for good this time
#### Estimated changes
Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/182b2a3)
fix properly
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.nat_abs_mul_self'



## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/a4cc8b7)
fix build
#### Estimated changes
Modified src/data/gaussian_int.lean
- \+ *lemma* gaussian_int.nat_abs_norm_eq

Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/a75d57c)
fix build
#### Estimated changes
Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/8dcd071)
generalize norm to zsqrtd
#### Estimated changes
Modified src/data/gaussian_int.lean
- \+ *lemma* gaussian_int.coe_nat_abs_norm
- \+ *lemma* gaussian_int.nat_abs_norm_mod_lt
- \+ *lemma* gaussian_int.nat_cast_nat_abs_norm
- \- *def* gaussian_int.norm
- \- *lemma* gaussian_int.norm_eq_one_iff
- \+ *lemma* gaussian_int.norm_mod_lt
- \- *lemma* gaussian_int.norm_mul
- \- *lemma* gaussian_int.norm_nat_cast
- \+ *lemma* gaussian_int.norm_nonneg
- \- *lemma* gaussian_int.norm_one
- \- *lemma* gaussian_int.norm_zero

Modified src/number_theory/pell.lean
- \+ *def* zsqrtd.norm
- \+ *lemma* zsqrtd.norm_eq_mul_conj
- \+ *lemma* zsqrtd.norm_eq_one_iff
- \+ *lemma* zsqrtd.norm_int_cast
- \+ *lemma* zsqrtd.norm_mul
- \+ *lemma* zsqrtd.norm_nat_cast
- \+ *lemma* zsqrtd.norm_nonneg
- \+ *lemma* zsqrtd.norm_one
- \+ *lemma* zsqrtd.norm_zero

Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/d98cae7)
fix build
#### Estimated changes
Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/5cbd7fa)
changing names
#### Estimated changes
Modified src/data/gaussian_int.lean
- \- *lemma* gaussian_int.int_cast_im
- \- *lemma* gaussian_int.int_cast_re
- \- *lemma* gaussian_int.to_complex_im'
- \+ *lemma* gaussian_int.to_complex_im
- \- *lemma* gaussian_int.to_complex_re'
- \+ *lemma* gaussian_int.to_complex_re
- \+ *lemma* gaussian_int.to_real_im
- \+ *lemma* gaussian_int.to_real_re

Modified src/data/zmod/quadratic_reciprocity.lean
- \+ *lemma* zmodp.exists_pow_two_eq_neg_one_iff_mod_four_ne_three
- \+ *lemma* zmodp.exists_pow_two_eq_prime_iff_of_mod_four_eq_one
- \+ *lemma* zmodp.exists_pow_two_eq_prime_iff_of_mod_four_eq_three
- \- *lemma* zmodp.is_square_iff_is_not_square_of_mod_four_eq_three
- \- *lemma* zmodp.is_square_iff_is_square_of_mod_four_eq_one
- \- *lemma* zmodp.neg_one_is_square_iff_mod_four_ne_three



## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/a9dfaba)
The year is 2019
#### Estimated changes
Modified src/data/gaussian_int.lean


Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/c36470f)
put sum_two_squares in nat.prime namespace
#### Estimated changes
Modified src/number_theory/sum_two_squares.lean
- \+ *lemma* nat.prime.sum_two_squares
- \- *lemma* sum_two_squares



## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/d8f0921)
move lemmas to correct places
#### Estimated changes
Added src/data/gaussian_int.lean
- \+ *lemma* gaussian_int.div_def
- \+ *lemma* gaussian_int.int_cast_im
- \+ *lemma* gaussian_int.int_cast_re
- \+ *lemma* gaussian_int.mod_def
- \+ *lemma* gaussian_int.nat_cast_complex_norm
- \+ *lemma* gaussian_int.nat_cast_real_norm
- \+ *def* gaussian_int.norm
- \+ *lemma* gaussian_int.norm_eq_one_iff
- \+ *lemma* gaussian_int.norm_eq_zero
- \+ *lemma* gaussian_int.norm_le_norm_mul_left
- \+ *lemma* gaussian_int.norm_mul
- \+ *lemma* gaussian_int.norm_nat_cast
- \+ *lemma* gaussian_int.norm_one
- \+ *lemma* gaussian_int.norm_pos
- \+ *lemma* gaussian_int.norm_sq_div_sub_div_lt_one
- \+ *lemma* gaussian_int.norm_sq_le_norm_sq_of_re_le_of_im_le
- \+ *lemma* gaussian_int.norm_zero
- \+ *def* gaussian_int.to_complex
- \+ *lemma* gaussian_int.to_complex_add
- \+ *lemma* gaussian_int.to_complex_def'
- \+ *lemma* gaussian_int.to_complex_def
- \+ *lemma* gaussian_int.to_complex_def₂
- \+ *lemma* gaussian_int.to_complex_div_im
- \+ *lemma* gaussian_int.to_complex_div_re
- \+ *lemma* gaussian_int.to_complex_eq_zero
- \+ *lemma* gaussian_int.to_complex_im'
- \+ *lemma* gaussian_int.to_complex_inj
- \+ *lemma* gaussian_int.to_complex_mul
- \+ *lemma* gaussian_int.to_complex_neg
- \+ *lemma* gaussian_int.to_complex_one
- \+ *lemma* gaussian_int.to_complex_re'
- \+ *lemma* gaussian_int.to_complex_sub
- \+ *lemma* gaussian_int.to_complex_zero
- \+ *def* gaussian_int

Modified src/number_theory/sum_two_squares.lean
- \- *lemma* gaussian_int.div_def
- \- *lemma* gaussian_int.int_cast_im
- \- *lemma* gaussian_int.int_cast_re
- \- *lemma* gaussian_int.mod_def
- \- *lemma* gaussian_int.nat_cast_complex_norm
- \- *lemma* gaussian_int.nat_cast_real_norm
- \- *def* gaussian_int.norm
- \- *lemma* gaussian_int.norm_eq_one_iff
- \- *lemma* gaussian_int.norm_eq_zero
- \- *lemma* gaussian_int.norm_le_norm_mul_left
- \- *lemma* gaussian_int.norm_mul
- \- *lemma* gaussian_int.norm_nat_cast
- \- *lemma* gaussian_int.norm_one
- \- *lemma* gaussian_int.norm_pos
- \- *lemma* gaussian_int.norm_sq_div_sub_div_lt_one
- \- *lemma* gaussian_int.norm_sq_le_norm_sq_of_re_le_of_im_le
- \- *lemma* gaussian_int.norm_zero
- \- *def* gaussian_int.to_complex
- \- *lemma* gaussian_int.to_complex_add
- \- *lemma* gaussian_int.to_complex_def'
- \- *lemma* gaussian_int.to_complex_def
- \- *lemma* gaussian_int.to_complex_def₂
- \- *lemma* gaussian_int.to_complex_div_im
- \- *lemma* gaussian_int.to_complex_div_re
- \- *lemma* gaussian_int.to_complex_eq_zero
- \- *lemma* gaussian_int.to_complex_im'
- \- *lemma* gaussian_int.to_complex_inj
- \- *lemma* gaussian_int.to_complex_mul
- \- *lemma* gaussian_int.to_complex_neg
- \- *lemma* gaussian_int.to_complex_one
- \- *lemma* gaussian_int.to_complex_re'
- \- *lemma* gaussian_int.to_complex_sub
- \- *lemma* gaussian_int.to_complex_zero
- \- *def* gaussian_int



## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/4e48324)
fix build
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.add_eq_one_iff
- \+/\- *lemma* nat.le_induction
- \+ *lemma* nat.mul_eq_one_iff
- \+ *lemma* nat.mul_left_eq_self_iff
- \+ *lemma* nat.mul_right_eq_self_iff

Modified src/data/nat/prime.lean
- \- *lemma* nat.prime.mul_eq_prime_pow_two
- \+ *lemma* nat.prime.mul_eq_prime_pow_two_iff

Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/9c9aee4)
finish proof of sum two squares
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.prime.mul_eq_prime_pow_two

Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/number_theory/sum_two_squares.lean
- \+ *lemma* gaussian_int.norm_eq_one_iff
- \+ *lemma* gaussian_int.norm_le_norm_mul_left
- \+ *lemma* gaussian_int.norm_nat_cast
- \+ *lemma* gaussian_int.norm_one
- \+ *lemma* gaussian_int.norm_zero
- \+ *lemma* sum_two_squares



## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/bd86c0d)
commit properly
#### Estimated changes
Modified src/data/zmod/quadratic_reciprocity.lean
- \+ *lemma* zmodp.neg_one_is_square_iff_mod_four_ne_three

Modified src/number_theory/pell.lean


Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/49a85f4)
prove Z[i] is a euclidean_domain
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+ *lemma* abs_sub_round
- \+ *theorem* rat.cast_round
- \+ *def* round

Added src/number_theory/sum_two_squares.lean
- \+ *lemma* gaussian_int.div_def
- \+ *lemma* gaussian_int.int_cast_im
- \+ *lemma* gaussian_int.int_cast_re
- \+ *lemma* gaussian_int.mod_def
- \+ *lemma* gaussian_int.nat_cast_complex_norm
- \+ *lemma* gaussian_int.nat_cast_real_norm
- \+ *def* gaussian_int.norm
- \+ *lemma* gaussian_int.norm_eq_zero
- \+ *lemma* gaussian_int.norm_mul
- \+ *lemma* gaussian_int.norm_pos
- \+ *lemma* gaussian_int.norm_sq_div_sub_div_lt_one
- \+ *lemma* gaussian_int.norm_sq_le_norm_sq_of_re_le_of_im_le
- \+ *def* gaussian_int.to_complex
- \+ *lemma* gaussian_int.to_complex_add
- \+ *lemma* gaussian_int.to_complex_def'
- \+ *lemma* gaussian_int.to_complex_def
- \+ *lemma* gaussian_int.to_complex_def₂
- \+ *lemma* gaussian_int.to_complex_div_im
- \+ *lemma* gaussian_int.to_complex_div_re
- \+ *lemma* gaussian_int.to_complex_eq_zero
- \+ *lemma* gaussian_int.to_complex_im'
- \+ *lemma* gaussian_int.to_complex_inj
- \+ *lemma* gaussian_int.to_complex_mul
- \+ *lemma* gaussian_int.to_complex_neg
- \+ *lemma* gaussian_int.to_complex_one
- \+ *lemma* gaussian_int.to_complex_re'
- \+ *lemma* gaussian_int.to_complex_sub
- \+ *lemma* gaussian_int.to_complex_zero
- \+ *def* gaussian_int



## [2019-03-02 19:55:17](https://github.com/leanprover-community/mathlib/commit/1f4f2e4)
refactor(*): move matrix.lean to data/ and determinant.lean to linear_algebra/ ([#779](https://github.com/leanprover-community/mathlib/pull/779))
#### Estimated changes
Renamed src/ring_theory/matrix.lean to src/data/matrix.lean


Renamed src/ring_theory/determinant.lean to src/linear_algebra/determinant.lean




## [2019-03-01 22:25:45-05:00](https://github.com/leanprover-community/mathlib/commit/8fbf296)
feat(topology/metric_space/hausdorff_distance): Hausdorff distance
#### Estimated changes
Modified src/topology/basic.lean
- \+ *def* topological_space.closeds
- \+ *def* topological_space.nonempty_compacts

Modified src/topology/continuity.lean
- \+ *def* nonempty_compacts.to_closeds

Modified src/topology/metric_space/cau_seq_filter.lean
- \+ *lemma* ennreal.cauchy_seq_of_edist_le_half_pow
- \+ *lemma* ennreal.edist_le_two_mul_half_pow
- \+ *lemma* ennreal.half_pow_add_succ
- \+ *lemma* ennreal.half_pow_mono
- \+ *lemma* ennreal.half_pow_pos
- \+ *lemma* ennreal.half_pow_tendsto_zero
- \+ *lemma* sequentially_complete.B2_lim
- \+ *lemma* sequentially_complete.B2_pos
- \- *lemma* sequentially_complete.FB_lim
- \- *lemma* sequentially_complete.FB_pos
- \- *lemma* sequentially_complete.F_lim
- \- *lemma* sequentially_complete.F_pos

Added src/topology/metric_space/closeds.lean
- \+ *lemma* emetric.closeds.edist_eq
- \+ *lemma* emetric.continuous_inf_edist_Hausdorff_edist
- \+ *lemma* emetric.is_closed_subsets_of_is_closed
- \+ *lemma* emetric.nonempty_compacts.is_closed_in_closeds
- \+ *lemma* emetric.nonempty_compacts.to_closeds.uniform_embedding
- \+ *lemma* metric.nonempty_compacts.dist_eq
- \+ *lemma* metric.uniform_continuous_inf_dist_Hausdorff_dist

Added src/topology/metric_space/hausdorff_distance.lean
- \+ *def* emetric.Hausdorff_edist
- \+ *lemma* emetric.Hausdorff_edist_closure
- \+ *lemma* emetric.Hausdorff_edist_closure₁
- \+ *lemma* emetric.Hausdorff_edist_closure₂
- \+ *lemma* emetric.Hausdorff_edist_comm
- \+ *lemma* emetric.Hausdorff_edist_empty
- \+ *lemma* emetric.Hausdorff_edist_image
- \+ *lemma* emetric.Hausdorff_edist_le_ediam
- \+ *lemma* emetric.Hausdorff_edist_le_of_inf_edist
- \+ *lemma* emetric.Hausdorff_edist_le_of_mem_edist
- \+ *lemma* emetric.Hausdorff_edist_self
- \+ *lemma* emetric.Hausdorff_edist_self_closure
- \+ *lemma* emetric.Hausdorff_edist_triangle
- \+ *lemma* emetric.Hausdorff_edist_zero_iff_closure_eq_closure
- \+ *lemma* emetric.Hausdorff_edist_zero_iff_eq_of_closed
- \+ *lemma* emetric.continuous_inf_edist
- \+ *lemma* emetric.exists_edist_lt_of_Hausdorff_edist_lt
- \+ *lemma* emetric.exists_edist_lt_of_inf_edist_lt
- \+ *def* emetric.inf_edist
- \+ *lemma* emetric.inf_edist_closure
- \+ *lemma* emetric.inf_edist_empty
- \+ *lemma* emetric.inf_edist_image
- \+ *lemma* emetric.inf_edist_le_Hausdorff_edist_of_mem
- \+ *lemma* emetric.inf_edist_le_edist_of_mem
- \+ *lemma* emetric.inf_edist_le_inf_edist_add_Hausdorff_edist
- \+ *lemma* emetric.inf_edist_le_inf_edist_add_edist
- \+ *lemma* emetric.inf_edist_le_inf_edist_of_subset
- \+ *lemma* emetric.inf_edist_singleton
- \+ *lemma* emetric.inf_edist_union
- \+ *lemma* emetric.inf_edist_zero_of_mem
- \+ *lemma* emetric.mem_closure_iff_inf_edist_zero
- \+ *lemma* emetric.mem_iff_ind_edist_zero_of_closed
- \+ *lemma* emetric.ne_empty_of_Hausdorff_edist_ne_top
- \+ *def* metric.Hausdorff_dist
- \+ *lemma* metric.Hausdorff_dist_closure
- \+ *lemma* metric.Hausdorff_dist_closure₁
- \+ *lemma* metric.Hausdorff_dist_closure₂
- \+ *lemma* metric.Hausdorff_dist_comm
- \+ *lemma* metric.Hausdorff_dist_empty'
- \+ *lemma* metric.Hausdorff_dist_empty
- \+ *lemma* metric.Hausdorff_dist_image
- \+ *lemma* metric.Hausdorff_dist_le_diam
- \+ *lemma* metric.Hausdorff_dist_le_of_inf_dist
- \+ *lemma* metric.Hausdorff_dist_le_of_mem_dist
- \+ *lemma* metric.Hausdorff_dist_nonneg
- \+ *lemma* metric.Hausdorff_dist_self_closure
- \+ *lemma* metric.Hausdorff_dist_self_zero
- \+ *lemma* metric.Hausdorff_dist_triangle'
- \+ *lemma* metric.Hausdorff_dist_triangle
- \+ *lemma* metric.Hausdorff_dist_zero_iff_closure_eq_closure
- \+ *lemma* metric.Hausdorff_dist_zero_iff_eq_of_closed
- \+ *lemma* metric.Hausdorff_edist_ne_top_of_ne_empty_of_bounded
- \+ *lemma* metric.continuous_inf_dist
- \+ *lemma* metric.exists_dist_lt_of_Hausdorff_dist_lt'
- \+ *lemma* metric.exists_dist_lt_of_Hausdorff_dist_lt
- \+ *lemma* metric.exists_dist_lt_of_inf_dist_lt
- \+ *def* metric.inf_dist
- \+ *lemma* metric.inf_dist_empty
- \+ *lemma* metric.inf_dist_eq_closure
- \+ *lemma* metric.inf_dist_image
- \+ *lemma* metric.inf_dist_le_Hausdorff_dist_of_mem
- \+ *lemma* metric.inf_dist_le_dist_of_mem
- \+ *lemma* metric.inf_dist_le_inf_dist_add_Hausdorff_dist
- \+ *lemma* metric.inf_dist_le_inf_dist_add_dist
- \+ *lemma* metric.inf_dist_le_inf_dist_of_subset
- \+ *lemma* metric.inf_dist_nonneg
- \+ *lemma* metric.inf_dist_singleton
- \+ *lemma* metric.inf_dist_zero_of_mem
- \+ *lemma* metric.inf_edist_ne_top
- \+ *lemma* metric.mem_closure_iff_inf_dist_zero
- \+ *lemma* metric.mem_iff_ind_dist_zero_of_closed
- \+ *lemma* metric.uniform_continuous_inf_dist



## [2019-03-01 21:24:00-05:00](https://github.com/leanprover-community/mathlib/commit/be88cec)
feat(analysis/exponential): added inequality lemmas
#### Estimated changes
Modified src/analysis/exponential.lean
- \+ *lemma* real.log_le_log
- \+ *lemma* real.mul_rpow
- \+ *lemma* real.one_le_rpow
- \+/\- *lemma* real.pow_nat_rpow_nat_inv
- \+ *lemma* real.rpow_le_rpow

Modified src/data/complex/exponential.lean
- \+/\- *lemma* real.exp_le_exp



## [2019-03-01 21:15:38](https://github.com/leanprover-community/mathlib/commit/0bb0cec)
feat(group_theory): free_group and free_abelian_group are lawful monads ([#737](https://github.com/leanprover-community/mathlib/pull/737))
#### Estimated changes
Modified src/group_theory/free_abelian_group.lean
- \+ *lemma* free_abelian_group.add_bind
- \+ *lemma* free_abelian_group.add_seq
- \+ *lemma* free_abelian_group.map_add
- \+ *lemma* free_abelian_group.map_neg
- \+ *lemma* free_abelian_group.map_pure
- \+ *lemma* free_abelian_group.map_sub
- \+ *lemma* free_abelian_group.map_zero
- \+ *lemma* free_abelian_group.neg_bind
- \+ *lemma* free_abelian_group.neg_seq
- \+ *lemma* free_abelian_group.pure_bind
- \+ *lemma* free_abelian_group.pure_seq
- \+ *lemma* free_abelian_group.seq_add
- \+ *lemma* free_abelian_group.seq_neg
- \+ *lemma* free_abelian_group.seq_sub
- \+ *lemma* free_abelian_group.seq_zero
- \+ *lemma* free_abelian_group.sub_bind
- \+ *lemma* free_abelian_group.sub_seq
- \+ *lemma* free_abelian_group.zero_bind
- \+ *lemma* free_abelian_group.zero_seq

Modified src/group_theory/free_group.lean
- \+ *lemma* free_group.inv_bind
- \+/\- *theorem* free_group.map.comp
- \+ *lemma* free_group.map_inv
- \+ *lemma* free_group.map_mul
- \+ *lemma* free_group.map_one
- \+ *lemma* free_group.map_pure
- \+ *lemma* free_group.mul_bind
- \+ *lemma* free_group.one_bind
- \+ *lemma* free_group.pure_bind
- \+/\- *lemma* free_group.quot_lift_mk
- \+/\- *lemma* free_group.quot_lift_on_mk
- \+/\- *theorem* free_group.to_group_eq_prod_map
- \+/\- *def* free_group



## [2019-03-01 21:14:41](https://github.com/leanprover-community/mathlib/commit/116cfff)
feat(data/zmod/basic): cast_mod_nat' and cast_mod_int' ([#783](https://github.com/leanprover-community/mathlib/pull/783))
* cast_mod_int'
* cast_val_int'
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.cast_mod_int'
- \+ *lemma* zmod.cast_mod_nat'
- \+ *lemma* zmod.eq_iff_modeq_int'
- \+ *lemma* zmod.eq_iff_modeq_nat'



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/04b5f88)
refactor(analysis/asymptotics): minor formatting changes
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+/\- *theorem* asymptotics.is_O.add
- \+/\- *theorem* asymptotics.is_O.sub
- \+/\- *theorem* asymptotics.is_O.symm
- \+/\- *theorem* asymptotics.is_O_const_mul_left
- \+/\- *theorem* asymptotics.is_O_const_smul_left_iff
- \+/\- *theorem* asymptotics.is_O_refl
- \+/\- *theorem* asymptotics.is_o.add
- \+/\- *theorem* asymptotics.is_o.sub
- \+/\- *theorem* asymptotics.is_o.symm
- \+/\- *theorem* asymptotics.is_o.to_is_O
- \+/\- *theorem* asymptotics.is_o_const_smul_left
- \+/\- *theorem* asymptotics.tendsto_nhds_zero_of_is_o



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/6363212)
feat(analysis/normed_space/deriv): generalize to spaces over any normed field
#### Estimated changes
Modified src/analysis/normed_space/deriv.lean
- \- *theorem* has_fderiv_at_filter_equiv_aux
- \+ *theorem* has_fderiv_at_filter_real_equiv



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/89b8915)
feat(analysis/normed_space/deriv): add readable proof of chain rule
#### Estimated changes
Modified src/analysis/normed_space/deriv.lean




## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/5dd1ba5)
feat(analysis/*): is_bigo -> is_O, is_littleo -> is_o
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *theorem* asymptotics.is_O.add
- \+ *theorem* asymptotics.is_O.comp
- \+ *theorem* asymptotics.is_O.congr
- \+ *theorem* asymptotics.is_O.congr_left
- \+ *theorem* asymptotics.is_O.congr_of_sub
- \+ *theorem* asymptotics.is_O.congr_right
- \+ *theorem* asymptotics.is_O.mono
- \+ *theorem* asymptotics.is_O.sub
- \+ *theorem* asymptotics.is_O.symm
- \+ *theorem* asymptotics.is_O.trans
- \+ *theorem* asymptotics.is_O.trans_is_o
- \+ *theorem* asymptotics.is_O.trans_tendsto
- \+ *theorem* asymptotics.is_O.tri
- \+ *def* asymptotics.is_O
- \+ *theorem* asymptotics.is_O_comm
- \+ *theorem* asymptotics.is_O_congr
- \+ *theorem* asymptotics.is_O_congr_left
- \+ *theorem* asymptotics.is_O_congr_right
- \+ *theorem* asymptotics.is_O_const_mul_left
- \+ *theorem* asymptotics.is_O_const_mul_left_iff
- \+ *theorem* asymptotics.is_O_const_mul_right_iff
- \+ *theorem* asymptotics.is_O_const_one
- \+ *theorem* asymptotics.is_O_const_smul_left
- \+ *theorem* asymptotics.is_O_const_smul_left_iff
- \+ *theorem* asymptotics.is_O_const_smul_right
- \+ *theorem* asymptotics.is_O_iff
- \+ *theorem* asymptotics.is_O_join
- \+ *theorem* asymptotics.is_O_mul
- \+ *theorem* asymptotics.is_O_neg_left
- \+ *theorem* asymptotics.is_O_neg_right
- \+ *theorem* asymptotics.is_O_norm_left
- \+ *theorem* asymptotics.is_O_norm_right
- \+ *theorem* asymptotics.is_O_of_is_O_const_mul_right
- \+ *theorem* asymptotics.is_O_refl
- \+ *theorem* asymptotics.is_O_refl_left
- \+ *theorem* asymptotics.is_O_smul
- \+ *theorem* asymptotics.is_O_zero
- \+ *theorem* asymptotics.is_O_zero_right_iff
- \- *theorem* asymptotics.is_bigo.add
- \- *theorem* asymptotics.is_bigo.comp
- \- *theorem* asymptotics.is_bigo.congr
- \- *theorem* asymptotics.is_bigo.congr_left
- \- *theorem* asymptotics.is_bigo.congr_of_sub
- \- *theorem* asymptotics.is_bigo.congr_right
- \- *theorem* asymptotics.is_bigo.mono
- \- *theorem* asymptotics.is_bigo.sub
- \- *theorem* asymptotics.is_bigo.symm
- \- *theorem* asymptotics.is_bigo.trans
- \- *theorem* asymptotics.is_bigo.trans_is_littleo
- \- *theorem* asymptotics.is_bigo.trans_tendsto
- \- *theorem* asymptotics.is_bigo.tri
- \- *def* asymptotics.is_bigo
- \- *theorem* asymptotics.is_bigo_comm
- \- *theorem* asymptotics.is_bigo_congr
- \- *theorem* asymptotics.is_bigo_congr_left
- \- *theorem* asymptotics.is_bigo_congr_right
- \- *theorem* asymptotics.is_bigo_const_mul_left
- \- *theorem* asymptotics.is_bigo_const_mul_left_iff
- \- *theorem* asymptotics.is_bigo_const_mul_right_iff
- \- *theorem* asymptotics.is_bigo_const_one
- \- *theorem* asymptotics.is_bigo_const_smul_left
- \- *theorem* asymptotics.is_bigo_const_smul_left_iff
- \- *theorem* asymptotics.is_bigo_const_smul_right
- \- *theorem* asymptotics.is_bigo_iff
- \- *theorem* asymptotics.is_bigo_join
- \- *theorem* asymptotics.is_bigo_mul
- \- *theorem* asymptotics.is_bigo_neg_left
- \- *theorem* asymptotics.is_bigo_neg_right
- \- *theorem* asymptotics.is_bigo_norm_left
- \- *theorem* asymptotics.is_bigo_norm_right
- \- *theorem* asymptotics.is_bigo_of_is_bigo_const_mul_right
- \- *theorem* asymptotics.is_bigo_refl
- \- *theorem* asymptotics.is_bigo_refl_left
- \- *theorem* asymptotics.is_bigo_smul
- \- *theorem* asymptotics.is_bigo_zero
- \- *theorem* asymptotics.is_bigo_zero_right_iff
- \- *theorem* asymptotics.is_littleo.add
- \- *theorem* asymptotics.is_littleo.comp
- \- *theorem* asymptotics.is_littleo.congr
- \- *theorem* asymptotics.is_littleo.congr_left
- \- *theorem* asymptotics.is_littleo.congr_of_sub
- \- *theorem* asymptotics.is_littleo.congr_right
- \- *theorem* asymptotics.is_littleo.mono
- \- *theorem* asymptotics.is_littleo.sub
- \- *theorem* asymptotics.is_littleo.symm
- \- *theorem* asymptotics.is_littleo.to_is_bigo
- \- *theorem* asymptotics.is_littleo.trans
- \- *theorem* asymptotics.is_littleo.trans_is_bigo
- \- *theorem* asymptotics.is_littleo.trans_tendsto
- \- *theorem* asymptotics.is_littleo.tri
- \- *def* asymptotics.is_littleo
- \- *theorem* asymptotics.is_littleo_comm
- \- *theorem* asymptotics.is_littleo_congr
- \- *theorem* asymptotics.is_littleo_congr_left
- \- *theorem* asymptotics.is_littleo_congr_right
- \- *theorem* asymptotics.is_littleo_const_mul_left
- \- *theorem* asymptotics.is_littleo_const_mul_left_iff
- \- *theorem* asymptotics.is_littleo_const_mul_right
- \- *theorem* asymptotics.is_littleo_const_smul_left
- \- *theorem* asymptotics.is_littleo_const_smul_left_iff
- \- *theorem* asymptotics.is_littleo_const_smul_right
- \- *theorem* asymptotics.is_littleo_iff_tendsto
- \- *theorem* asymptotics.is_littleo_join
- \- *theorem* asymptotics.is_littleo_mul
- \- *theorem* asymptotics.is_littleo_mul_left
- \- *theorem* asymptotics.is_littleo_mul_right
- \- *theorem* asymptotics.is_littleo_neg_left
- \- *theorem* asymptotics.is_littleo_neg_right
- \- *theorem* asymptotics.is_littleo_norm_left
- \- *theorem* asymptotics.is_littleo_norm_right
- \- *theorem* asymptotics.is_littleo_of_is_littleo_const_mul_right
- \- *theorem* asymptotics.is_littleo_one_iff
- \- *theorem* asymptotics.is_littleo_refl_left
- \- *theorem* asymptotics.is_littleo_smul
- \- *theorem* asymptotics.is_littleo_zero
- \- *theorem* asymptotics.is_littleo_zero_right_iff
- \+ *theorem* asymptotics.is_o.add
- \+ *theorem* asymptotics.is_o.comp
- \+ *theorem* asymptotics.is_o.congr
- \+ *theorem* asymptotics.is_o.congr_left
- \+ *theorem* asymptotics.is_o.congr_of_sub
- \+ *theorem* asymptotics.is_o.congr_right
- \+ *theorem* asymptotics.is_o.mono
- \+ *theorem* asymptotics.is_o.sub
- \+ *theorem* asymptotics.is_o.symm
- \+ *theorem* asymptotics.is_o.to_is_O
- \+ *theorem* asymptotics.is_o.trans
- \+ *theorem* asymptotics.is_o.trans_is_O
- \+ *theorem* asymptotics.is_o.trans_tendsto
- \+ *theorem* asymptotics.is_o.tri
- \+ *def* asymptotics.is_o
- \+ *theorem* asymptotics.is_o_comm
- \+ *theorem* asymptotics.is_o_congr
- \+ *theorem* asymptotics.is_o_congr_left
- \+ *theorem* asymptotics.is_o_congr_right
- \+ *theorem* asymptotics.is_o_const_mul_left
- \+ *theorem* asymptotics.is_o_const_mul_left_iff
- \+ *theorem* asymptotics.is_o_const_mul_right
- \+ *theorem* asymptotics.is_o_const_smul_left
- \+ *theorem* asymptotics.is_o_const_smul_left_iff
- \+ *theorem* asymptotics.is_o_const_smul_right
- \+ *theorem* asymptotics.is_o_iff_tendsto
- \+ *theorem* asymptotics.is_o_join
- \+ *theorem* asymptotics.is_o_mul
- \+ *theorem* asymptotics.is_o_mul_left
- \+ *theorem* asymptotics.is_o_mul_right
- \+ *theorem* asymptotics.is_o_neg_left
- \+ *theorem* asymptotics.is_o_neg_right
- \+ *theorem* asymptotics.is_o_norm_left
- \+ *theorem* asymptotics.is_o_norm_right
- \+ *theorem* asymptotics.is_o_of_is_o_const_mul_right
- \+ *theorem* asymptotics.is_o_one_iff
- \+ *theorem* asymptotics.is_o_refl_left
- \+ *theorem* asymptotics.is_o_smul
- \+ *theorem* asymptotics.is_o_zero
- \+ *theorem* asymptotics.is_o_zero_right_iff
- \- *theorem* asymptotics.tendsto_nhds_zero_of_is_littleo
- \+ *theorem* asymptotics.tendsto_nhds_zero_of_is_o

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *theorem* is_bounded_linear_map.is_O_comp
- \+ *theorem* is_bounded_linear_map.is_O_id
- \+ *theorem* is_bounded_linear_map.is_O_sub
- \- *theorem* is_bounded_linear_map.is_bigo_comp
- \- *theorem* is_bounded_linear_map.is_bigo_id
- \- *theorem* is_bounded_linear_map.is_bigo_sub

Modified src/analysis/normed_space/deriv.lean
- \- *theorem* has_fderiv_at.is_littleo
- \+ *theorem* has_fderiv_at.is_o
- \+ *theorem* has_fderiv_at_filter.is_O_sub
- \- *theorem* has_fderiv_at_filter.is_bigo_sub
- \- *theorem* has_fderiv_at_filter.is_littleo
- \+ *theorem* has_fderiv_at_filter.is_o



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/49ecc7b)
fix(*): fix things from change tendsto_congr -> tendsto.congr'
#### Estimated changes
Modified src/analysis/normed_space/deriv.lean


Modified src/analysis/specific_limits.lean


Modified src/data/padics/hensel.lean


Modified src/order/filter/basic.lean
- \+ *theorem* filter.tendsto.congr'r
- \- *theorem* filter.tendsto_congr

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/instances/ennreal.lean




## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/d74804b)
add has_fderiv_at_filter
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *theorem* asymptotics.is_bigo.congr
- \+ *theorem* asymptotics.is_bigo.congr_of_sub
- \+ *theorem* asymptotics.is_bigo.symm
- \+ *theorem* asymptotics.is_bigo.trans_tendsto
- \+ *theorem* asymptotics.is_bigo.tri
- \+ *theorem* asymptotics.is_bigo_comm
- \+ *theorem* asymptotics.is_bigo_congr
- \+ *theorem* asymptotics.is_bigo_congr_left
- \+ *theorem* asymptotics.is_bigo_congr_right
- \+/\- *theorem* asymptotics.is_bigo_neg_left
- \+/\- *theorem* asymptotics.is_bigo_norm_left
- \+ *theorem* asymptotics.is_bigo_refl_left
- \+ *theorem* asymptotics.is_littleo.congr
- \+ *theorem* asymptotics.is_littleo.congr_of_sub
- \+ *theorem* asymptotics.is_littleo.symm
- \+ *theorem* asymptotics.is_littleo.trans_tendsto
- \+ *theorem* asymptotics.is_littleo.tri
- \+ *theorem* asymptotics.is_littleo_comm
- \+ *theorem* asymptotics.is_littleo_congr
- \+ *theorem* asymptotics.is_littleo_congr_left
- \+ *theorem* asymptotics.is_littleo_congr_right
- \+/\- *theorem* asymptotics.is_littleo_neg_left
- \+/\- *theorem* asymptotics.is_littleo_norm_left
- \+ *theorem* asymptotics.is_littleo_refl_left

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *theorem* is_bounded_linear_map.is_bigo_comp

Modified src/analysis/normed_space/deriv.lean
- \- *theorem* chain_rule
- \- *theorem* chain_rule_at_within
- \- *theorem* continuous_at_of_has_fderiv_at
- \- *theorem* continuous_at_within_of_has_fderiv_at_within
- \+ *theorem* has_fderiv_at.comp
- \+/\- *theorem* has_fderiv_at.congr
- \+ *theorem* has_fderiv_at.continuous_at
- \+/\- *theorem* has_fderiv_at_add
- \+ *theorem* has_fderiv_at_congr
- \+ *theorem* has_fderiv_at_filter.comp
- \+ *theorem* has_fderiv_at_filter.congr
- \+ *theorem* has_fderiv_at_filter.is_bigo_sub
- \+ *theorem* has_fderiv_at_filter.is_littleo
- \+ *theorem* has_fderiv_at_filter.mono
- \+ *theorem* has_fderiv_at_filter.tendsto_nhds
- \+ *def* has_fderiv_at_filter
- \+ *theorem* has_fderiv_at_filter_add
- \+ *theorem* has_fderiv_at_filter_congr'
- \+ *theorem* has_fderiv_at_filter_congr
- \+ *theorem* has_fderiv_at_filter_const
- \+ *theorem* has_fderiv_at_filter_equiv_aux
- \+ *theorem* has_fderiv_at_filter_id
- \+ *theorem* has_fderiv_at_filter_iff_tendsto
- \+ *theorem* has_fderiv_at_filter_neg
- \+ *theorem* has_fderiv_at_filter_of_has_fderiv_at
- \+ *theorem* has_fderiv_at_filter_smul
- \+ *theorem* has_fderiv_at_filter_sub
- \+/\- *theorem* has_fderiv_at_neg
- \+/\- *theorem* has_fderiv_at_sub
- \+ *theorem* has_fderiv_at_within.comp
- \+ *theorem* has_fderiv_at_within.continuous_at_within
- \+/\- *theorem* has_fderiv_at_within_add
- \+ *theorem* has_fderiv_at_within_congr
- \- *theorem* has_fderiv_at_within_equiv_aux
- \+/\- *theorem* has_fderiv_at_within_neg
- \+/\- *theorem* has_fderiv_at_within_of_has_fderiv_at
- \+/\- *theorem* has_fderiv_at_within_sub

Modified src/order/filter/basic.lean
- \+ *lemma* filter.congr_sets
- \+ *lemma* filter.tendsto.congr'
- \- *lemma* filter.tendsto_cong
- \+ *theorem* filter.tendsto_congr

Modified src/topology/continuity.lean
- \+ *theorem* continuous_at_within.tendsto_nhds_within_image



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/21b1fcc)
fix(asymptotics, deriv): minor formatting fixes
#### Estimated changes
Modified src/analysis/asymptotics.lean


Modified src/analysis/normed_space/deriv.lean




## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/16033bb)
feat(analysis/asymptotics,analysis/normed_space/deriv): improvements and additions
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *theorem* asymptotics.is_bigo.congr_left
- \+ *theorem* asymptotics.is_bigo.congr_right
- \+ *theorem* asymptotics.is_bigo.trans
- \+ *theorem* asymptotics.is_bigo.trans_is_littleo
- \+ *theorem* asymptotics.is_bigo_const_mul_left
- \+ *theorem* asymptotics.is_bigo_const_mul_left_iff
- \+ *theorem* asymptotics.is_bigo_const_mul_right_iff
- \+ *theorem* asymptotics.is_bigo_const_one
- \+ *theorem* asymptotics.is_bigo_const_smul_left
- \+ *theorem* asymptotics.is_bigo_const_smul_left_iff
- \+ *theorem* asymptotics.is_bigo_const_smul_right
- \+ *theorem* asymptotics.is_bigo_iff
- \- *theorem* asymptotics.is_bigo_iff_pos
- \+ *theorem* asymptotics.is_bigo_join
- \+ *theorem* asymptotics.is_bigo_mul
- \- *theorem* asymptotics.is_bigo_mul_left
- \- *theorem* asymptotics.is_bigo_mul_right
- \+ *theorem* asymptotics.is_bigo_of_is_bigo_const_mul_right
- \- *theorem* asymptotics.is_bigo_of_is_bigo_of_is_bigo
- \+ *theorem* asymptotics.is_bigo_refl
- \+ *theorem* asymptotics.is_bigo_smul
- \- *theorem* asymptotics.is_bigo_smul_left
- \- *theorem* asymptotics.is_bigo_smul_right
- \+/\- *theorem* asymptotics.is_bigo_zero
- \+ *theorem* asymptotics.is_bigo_zero_right_iff
- \+ *theorem* asymptotics.is_littleo.congr_left
- \+ *theorem* asymptotics.is_littleo.congr_right
- \+ *theorem* asymptotics.is_littleo.trans
- \+ *theorem* asymptotics.is_littleo.trans_is_bigo
- \+ *theorem* asymptotics.is_littleo_const_mul_left
- \+ *theorem* asymptotics.is_littleo_const_mul_left_iff
- \+ *theorem* asymptotics.is_littleo_const_mul_right
- \+ *theorem* asymptotics.is_littleo_const_smul_left
- \+ *theorem* asymptotics.is_littleo_const_smul_left_iff
- \+ *theorem* asymptotics.is_littleo_const_smul_right
- \- *theorem* asymptotics.is_littleo_iff_pos
- \+ *theorem* asymptotics.is_littleo_join
- \+ *theorem* asymptotics.is_littleo_mul
- \+/\- *theorem* asymptotics.is_littleo_mul_left
- \+/\- *theorem* asymptotics.is_littleo_mul_right
- \- *theorem* asymptotics.is_littleo_of_is_bigo_of_is_littleo
- \+ *theorem* asymptotics.is_littleo_of_is_littleo_const_mul_right
- \- *theorem* asymptotics.is_littleo_of_is_littleo_of_is_bigo
- \- *theorem* asymptotics.is_littleo_of_tendsto
- \+ *theorem* asymptotics.is_littleo_one_iff
- \+ *theorem* asymptotics.is_littleo_smul
- \- *theorem* asymptotics.is_littleo_smul_left
- \- *theorem* asymptotics.is_littleo_smul_right
- \+/\- *theorem* asymptotics.is_littleo_zero
- \+ *theorem* asymptotics.is_littleo_zero_right_iff
- \+/\- *theorem* asymptotics.tendsto_nhds_zero_of_is_littleo

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *def* is_bounded_linear_map.to_linear_map

Modified src/analysis/normed_space/deriv.lean
- \+/\- *theorem* chain_rule
- \+ *theorem* chain_rule_at_within
- \+ *theorem* continuous_at_of_has_fderiv_at
- \+ *theorem* continuous_at_within_of_has_fderiv_at_within
- \- *theorem* continuous_of_has_fderiv
- \- *theorem* has_fderiv_add
- \+ *theorem* has_fderiv_at.congr
- \+ *theorem* has_fderiv_at.is_littleo
- \+ *theorem* has_fderiv_at_add
- \+ *theorem* has_fderiv_at_const
- \+ *theorem* has_fderiv_at_id
- \+ *theorem* has_fderiv_at_iff_tendsto
- \+ *theorem* has_fderiv_at_neg
- \+ *theorem* has_fderiv_at_smul
- \+ *theorem* has_fderiv_at_sub
- \+/\- *theorem* has_fderiv_at_within.congr
- \+ *theorem* has_fderiv_at_within.mono
- \+ *theorem* has_fderiv_at_within_add
- \+ *theorem* has_fderiv_at_within_const
- \+ *theorem* has_fderiv_at_within_equiv_aux
- \+ *theorem* has_fderiv_at_within_id
- \+ *theorem* has_fderiv_at_within_iff_tendsto
- \- *def* has_fderiv_at_within_mono
- \+ *theorem* has_fderiv_at_within_neg
- \+ *theorem* has_fderiv_at_within_of_has_fderiv_at
- \+ *theorem* has_fderiv_at_within_smul
- \+ *theorem* has_fderiv_at_within_sub
- \- *theorem* has_fderiv_const
- \- *theorem* has_fderiv_equiv_aux
- \- *theorem* has_fderiv_id
- \- *theorem* has_fderiv_iff_littleo
- \- *theorem* has_fderiv_neg
- \- *theorem* has_fderiv_smul
- \- *theorem* has_fderiv_sub

Modified src/topology/basic.lean




## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/6265d26)
feat(analysis/normed_space/deriv): start on derivative
#### Estimated changes
Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *theorem* is_bounded_linear_map.is_bigo_id
- \+ *theorem* is_bounded_linear_map.is_bigo_sub
- \+ *def* is_bounded_linear_map.to_linear_map

Added src/analysis/normed_space/deriv.lean
- \+ *theorem* chain_rule
- \+ *theorem* continuous_of_has_fderiv
- \+ *theorem* has_fderiv_add
- \+ *def* has_fderiv_at
- \+ *theorem* has_fderiv_at_within.congr
- \+ *def* has_fderiv_at_within
- \+ *def* has_fderiv_at_within_mono
- \+ *theorem* has_fderiv_const
- \+ *theorem* has_fderiv_equiv_aux
- \+ *theorem* has_fderiv_id
- \+ *theorem* has_fderiv_iff_littleo
- \+ *theorem* has_fderiv_neg
- \+ *theorem* has_fderiv_smul
- \+ *theorem* has_fderiv_sub



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/92a5e0b)
feat(analysis/asymptotics): start on bigo and littlo
#### Estimated changes
Added src/analysis/asymptotics.lean
- \+ *theorem* asymptotics.is_bigo.add
- \+ *theorem* asymptotics.is_bigo.comp
- \+ *theorem* asymptotics.is_bigo.mono
- \+ *theorem* asymptotics.is_bigo.sub
- \+ *def* asymptotics.is_bigo
- \+ *theorem* asymptotics.is_bigo_iff_pos
- \+ *theorem* asymptotics.is_bigo_mul_left
- \+ *theorem* asymptotics.is_bigo_mul_right
- \+ *theorem* asymptotics.is_bigo_neg_left
- \+ *theorem* asymptotics.is_bigo_neg_right
- \+ *theorem* asymptotics.is_bigo_norm_left
- \+ *theorem* asymptotics.is_bigo_norm_right
- \+ *theorem* asymptotics.is_bigo_of_is_bigo_of_is_bigo
- \+ *theorem* asymptotics.is_bigo_smul_left
- \+ *theorem* asymptotics.is_bigo_smul_right
- \+ *theorem* asymptotics.is_bigo_zero
- \+ *theorem* asymptotics.is_littleo.add
- \+ *theorem* asymptotics.is_littleo.comp
- \+ *theorem* asymptotics.is_littleo.mono
- \+ *theorem* asymptotics.is_littleo.sub
- \+ *theorem* asymptotics.is_littleo.to_is_bigo
- \+ *def* asymptotics.is_littleo
- \+ *theorem* asymptotics.is_littleo_iff_pos
- \+ *theorem* asymptotics.is_littleo_iff_tendsto
- \+ *theorem* asymptotics.is_littleo_mul_left
- \+ *theorem* asymptotics.is_littleo_mul_right
- \+ *theorem* asymptotics.is_littleo_neg_left
- \+ *theorem* asymptotics.is_littleo_neg_right
- \+ *theorem* asymptotics.is_littleo_norm_left
- \+ *theorem* asymptotics.is_littleo_norm_right
- \+ *theorem* asymptotics.is_littleo_of_is_bigo_of_is_littleo
- \+ *theorem* asymptotics.is_littleo_of_is_littleo_of_is_bigo
- \+ *theorem* asymptotics.is_littleo_of_tendsto
- \+ *theorem* asymptotics.is_littleo_smul_left
- \+ *theorem* asymptotics.is_littleo_smul_right
- \+ *theorem* asymptotics.is_littleo_zero
- \+ *theorem* asymptotics.tendsto_nhds_zero_of_is_littleo



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/206a7a1)
feat(*): add various small lemmas
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_norm
- \+ *theorem* normed_space.tendsto_nhds_zero
- \+ *lemma* tendsto_smul_const

Modified src/order/filter/basic.lean
- \+ *lemma* filter.le_comap_top
- \+ *theorem* filter.tendsto.congr

Modified src/topology/basic.lean
- \- *theorem* tendsto_at_within_iff_subtype
- \+ *theorem* tendsto_nhds_within_iff_subtype
- \+ *theorem* tendsto_nhds_within_mono_left
- \+ *theorem* tendsto_nhds_within_mono_right
- \+ *theorem* tendsto_nhds_within_of_tendsto_nhds

Modified src/topology/continuity.lean
- \+ *theorem* nhds_within_le_comap



## [2019-03-01 13:10:17](https://github.com/leanprover-community/mathlib/commit/4f7853a)
feat(data/list/basic): mem_rotate
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.mem_rotate

