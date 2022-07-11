## [2019-03-31 21:33:03+02:00](https://github.com/leanprover-community/mathlib/commit/c91e6c2)
fix(ring_theory/algebra): remove duplicate theorems to fix build
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \- *lemma* smul_re:
- \- *lemma* smul_im:



## [2019-03-31 08:35:59-04:00](https://github.com/leanprover-community/mathlib/commit/9480df5)
refactor(computability): unpack fixed_point proof
#### Estimated changes
Modified src/computability/partrec_code.lean




## [2019-03-31 08:35:21-04:00](https://github.com/leanprover-community/mathlib/commit/359cac1)
feat(computability): computable_iff_re_compl_re
#### Estimated changes
Modified src/computability/halting.lean
- \+ *theorem* computable_iff
- \+ *theorem* to_re
- \+ *theorem* computable_iff_re_compl_re



## [2019-03-31 08:32:21-04:00](https://github.com/leanprover-community/mathlib/commit/514de77)
feat(data/finset): to_finset_eq_empty
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* to_finset_eq_empty

Modified src/data/multiset.lean
- \+ *theorem* erase_dup_eq_zero



## [2019-03-31 08:31:39-04:00](https://github.com/leanprover-community/mathlib/commit/72634d2)
feat(data/complex/basic): smul_re,im
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *lemma* smul_re
- \+ *lemma* smul_im



## [2019-03-31 00:48:41](https://github.com/leanprover-community/mathlib/commit/e1c035d)
feat(data/polynomial): eval₂_neg
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* eval₂_neg
- \+ *lemma* eval₂_sub



## [2019-03-29 23:56:28](https://github.com/leanprover-community/mathlib/commit/c2bb4c5)
refactor(data/zsqrtd/basic): move zsqrtd out of pell and into data ([#861](https://github.com/leanprover-community/mathlib/pull/861))
#### Estimated changes
Created src/data/zsqrtd/basic.lean
- \+ *lemma* norm_zero
- \+ *lemma* norm_one
- \+ *lemma* norm_int_cast
- \+ *lemma* norm_nat_cast
- \+ *lemma* norm_mul
- \+ *lemma* norm_eq_mul_conj
- \+ *lemma* norm_nonneg
- \+ *lemma* norm_eq_one_iff
- \+ *def* norm

Renamed src/data/gaussian_int.lean to src/data/zsqrtd/gaussian_int.lean


Modified src/number_theory/pell.lean
- \- *lemma* norm_zero
- \- *lemma* norm_one
- \- *lemma* norm_int_cast
- \- *lemma* norm_nat_cast
- \- *lemma* norm_mul
- \- *lemma* norm_eq_mul_conj
- \- *lemma* norm_nonneg
- \- *lemma* norm_eq_one_iff
- \- *def* norm

Modified src/number_theory/sum_two_squares.lean




## [2019-03-29 15:03:34-05:00](https://github.com/leanprover-community/mathlib/commit/dc7de46)
feat(analysis/convex): convex sets and functions ([#834](https://github.com/leanprover-community/mathlib/pull/834))
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* is_linear_map_neg
- \+ *lemma* is_linear_map_smul
- \+ *lemma* is_linear_map_smul'

Created src/analysis/convex.lean
- \+ *lemma* convex_iff:
- \+ *lemma* convex_iff_div:
- \+ *lemma* left_mem_segment
- \+ *lemma* right_mem_segment
- \+ *lemma* mem_segment_iff
- \+ *lemma* mem_segment_iff'
- \+ *lemma* segment_symm
- \+ *lemma* segment_eq_Icc
- \+ *lemma* segment_translate
- \+ *lemma* segment_translate_image
- \+ *lemma* convex_segment_iff
- \+ *lemma* convex_empty
- \+ *lemma* convex_singleton
- \+ *lemma* convex_univ
- \+ *lemma* convex_inter
- \+ *lemma* convex_Inter
- \+ *lemma* convex_prod
- \+ *lemma* convex_linear_image
- \+ *lemma* convex_linear_image'
- \+ *lemma* convex_linear_preimage
- \+ *lemma* convex_linear_preimage'
- \+ *lemma* convex_neg
- \+ *lemma* convex_neg_preimage
- \+ *lemma* convex_smul
- \+ *lemma* convex_smul_preimage
- \+ *lemma* convex_add
- \+ *lemma* convex_sub
- \+ *lemma* convex_translation
- \+ *lemma* convex_affinity
- \+ *lemma* convex_Iio
- \+ *lemma* convex_Iic
- \+ *lemma* convex_Ioi
- \+ *lemma* convex_Ici
- \+ *lemma* convex_Ioo
- \+ *lemma* convex_Ico
- \+ *lemma* convex_Ioc
- \+ *lemma* convex_Icc
- \+ *lemma* convex_segment
- \+ *lemma* convex_halfspace_lt
- \+ *lemma* convex_halfspace_le
- \+ *lemma* convex_halfspace_gt
- \+ *lemma* convex_halfspace_ge
- \+ *lemma* convex_halfplane
- \+ *lemma* convex_halfspace_re_lt
- \+ *lemma* convex_halfspace_re_le
- \+ *lemma* convex_halfspace_re_gt
- \+ *lemma* convex_halfspace_re_lge
- \+ *lemma* convex_halfspace_im_lt
- \+ *lemma* convex_halfspace_im_le
- \+ *lemma* convex_halfspace_im_gt
- \+ *lemma* convex_halfspace_im_lge
- \+ *lemma* convex_sum
- \+ *lemma* convex_sum_iff
- \+ *lemma* convex_on_iff
- \+ *lemma* convex_on_iff_div:
- \+ *lemma* convex_on_sum
- \+ *lemma* convex_on_linorder
- \+ *lemma* convex_on_subset
- \+ *lemma* convex_on_add
- \+ *lemma* convex_on_smul
- \+ *lemma* convex_le_of_convex_on
- \+ *lemma* convex_lt_of_convex_on
- \+ *lemma* le_on_interval_of_convex_on
- \+ *lemma* convex_on_dist
- \+ *lemma* convex_ball
- \+ *lemma* convex_closed_ball
- \+ *def* convex
- \+ *def* segment
- \+ *def* convex_on

Modified src/data/set/intervals.lean
- \+ *lemma* image_neg_Iio
- \+ *lemma* image_neg_Iic

Modified src/linear_algebra/basic.lean
- \+ *lemma* is_linear_map_add
- \+ *lemma* is_linear_map_sub

Modified src/ring_theory/algebra.lean
- \+ *lemma* smul_re:
- \+ *lemma* smul_im:



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


Created src/tactic/library_search.lean
- \+ *def* head_symbol_match.to_string

Created test/library_search/basic.lean


Created test/library_search/ring_theory.lean




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
Created src/category_theory/instances/groups.lean
- \+ *def* Group
- \+ *def* AddCommGroup
- \+ *def* is_add_comm_group_hom
- \+ *def* forget_to_Group



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
- \- *theorem* smul_add
- \- *theorem* mul_smul
- \- *theorem* smul_zero
- \- *theorem* one_smul

Modified src/algebra/pi_instances.lean


Modified src/analysis/asymptotics.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/deriv.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/group_theory/group_action.lean
- \+ *theorem* mul_smul
- \+ *theorem* one_smul
- \+ *theorem* smul_add
- \+ *theorem* smul_zero
- \- *def* comp_hom

Modified src/group_theory/sylow.lean


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


Created scripts/cache-olean.py
- \+ *def* auth_github():
- \+ *def* make_cache(fn):
- \+ *def* mathlib_asset(repo,
- \+ *def* fetch_mathlib(asset):

Created scripts/post-checkout


Created scripts/post-commit


Modified scripts/remote-install-update-mathlib.sh


Created scripts/setup-dev-scripts.sh


Created scripts/setup-lean-git-hooks.sh


Deleted scripts/setup-update-mathlib.sh


Modified scripts/update-mathlib.py
- \+ *def* auth_github():



## [2019-03-27 21:47:02+01:00](https://github.com/leanprover-community/mathlib/commit/8838ff3)
feat(algebra/field_power): add fpow_one, one_fpow, fpow_mul, mul_fpow (closes [#855](https://github.com/leanprover-community/mathlib/pull/855))
#### Estimated changes
Modified src/algebra/field.lean
- \+ *lemma* mk0_coe
- \+/\- *lemma* inv_eq_zero
- \+ *lemma* neg_inv'

Modified src/algebra/field_power.lean
- \+ *lemma* one_fpow
- \+ *lemma* fpow_one
- \+ *lemma* fpow_mul
- \+ *lemma* mul_fpow



## [2019-03-27 20:15:04+01:00](https://github.com/leanprover-community/mathlib/commit/8429354)
feat(analysis): add real.rpow_le_one
#### Estimated changes
Modified src/analysis/exponential.lean
- \+ *lemma* rpow_le_one



## [2019-03-27 20:15:04+01:00](https://github.com/leanprover-community/mathlib/commit/4305ad6)
feat(analysis): add rpow_pos_of_pos
#### Estimated changes
Modified src/analysis/exponential.lean
- \+ *lemma* rpow_pos_of_pos



## [2019-03-27 09:57:35-05:00](https://github.com/leanprover-community/mathlib/commit/02ca494)
Remove outparam in normed space ([#844](https://github.com/leanprover-community/mathlib/pull/844))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *lemma* zero
- \+/\- *lemma* id
- \+/\- *lemma* smul
- \+/\- *lemma* neg
- \+/\- *lemma* sub
- \+/\- *lemma* tendsto
- \+/\- *lemma* continuous
- \+/\- *lemma* lim_zero_bounded_linear_map
- \+/\- *theorem* is_O_id
- \+/\- *theorem* is_O_comp
- \+/\- *theorem* is_O_sub
- \+/\- *def* to_linear_map

Modified src/analysis/normed_space/deriv.lean
- \+/\- *theorem* has_fderiv_at.is_o
- \+/\- *theorem* has_fderiv_at_filter_id
- \+/\- *theorem* has_fderiv_at_within_id
- \+/\- *theorem* has_fderiv_at_id

Modified src/analysis/normed_space/operator_norm.lean




## [2019-03-27 08:20:35-04:00](https://github.com/leanprover-community/mathlib/commit/52fddda)
feat(algebra/archimedean): lemmas about powers of elements ([#802](https://github.com/leanprover-community/mathlib/pull/802))
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+ *lemma* exists_nat_pow_near
- \+ *lemma* exists_int_pow_near



## [2019-03-26 16:35:47-05:00](https://github.com/leanprover-community/mathlib/commit/17e40bb)
feat(tactic/congr): apply to `iff` propositions ([#833](https://github.com/leanprover-community/mathlib/pull/833))
#### Estimated changes
Modified src/tactic/interactive.lean


Modified test/tactics.lean




## [2019-03-26 21:53:30+01:00](https://github.com/leanprover-community/mathlib/commit/c3a9028)
fix(data/polynomial): (nat_)degree_map' assumed a comm_ring instead of a comm_semiring
#### Estimated changes
Modified src/data/polynomial.lean
- \+/\- *lemma* degree_map'
- \+/\- *lemma* nat_degree_map'



## [2019-03-26 19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/a016652)
feat(data/finset): add range_add_one'
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* range_add_one'



## [2019-03-26 19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/0ea37e9)
feat(algebra/big_operators): add prod_map, sum_map
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_map



## [2019-03-26 19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/d3c68fc)
feat(analysis/normed_space): tendsto_zero_iff_norm_tendsto_zero
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* tendsto_zero_iff_norm_tendsto_zero
- \+/\- *lemma* lim_norm
- \+/\- *lemma* lim_norm_zero
- \+/\- *lemma* continuous_norm



## [2019-03-26 19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/df08058)
refactor(analysis/normed_space): rename norm_mul -> norm_mul_le; use norm_mul for the equality in normed fields; and norm_mul_le for the inequality in normed_rings
#### Estimated changes
Modified src/analysis/asymptotics.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_mul_le
- \+ *lemma* norm_pow_le
- \+/\- *lemma* norm_mul
- \+/\- *lemma* norm_pow
- \+ *lemma* norm_prod
- \- *lemma* normed_field.norm_pow

Modified src/data/complex/basic.lean
- \+ *lemma* abs_of_nat

Modified src/data/padics/padic_integers.lean




## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/bd21b0e)
feat(analyis/normed_space): add normed_field instance for ℂ
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_real
- \+ *lemma* norm_rat
- \+ *lemma* norm_nat
- \+ *lemma* norm_int
- \+ *lemma* norm_int_of_nonneg



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/a01cf86)
feat(data/multiset,data/finset): add multiset./finset.le_sum_of_additive
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* le_sum_of_subadditive
- \+/\- *lemma* abs_sum_le_sum_abs

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_triangle_sum

Modified src/data/multiset.lean
- \+ *lemma* le_sum_of_subadditive
- \+ *lemma* abs_sum_le_sum_abs



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/c912253)
feat(algebra/group_power): add lt_of_pow_lt_pow
#### Estimated changes
Modified src/algebra/group_power.lean
- \+/\- *lemma* pow_le_pow_of_le_left
- \+ *lemma* lt_of_pow_lt_pow



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/fd37f96)
feat(data/fin): add injective_cast_le
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* injective_cast_le



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/c0c2edb)
feat(algebra/big_operators): add Gauss' summation formula
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* sum_range_id_mul_two
- \+ *lemma* sum_range_id



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/cfeb887)
feat(data/polynomial): degree_map', nat_degree_map' semiring variant of degree_map, nat_degree_map
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* degree_map'
- \+ *lemma* nat_degree_map'



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/aa2c6e2)
feat(data/mv_polynomial): more about renaming
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* rename_monomial
- \+ *lemma* rename_eq
- \+ *lemma* injective_rename
- \+ *lemma* total_degree_rename_le



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
- \+ *lemma* support_emb_domain
- \+ *lemma* emb_domain_zero
- \+ *lemma* emb_domain_apply
- \+ *lemma* emb_domain_notin_range
- \+ *lemma* emb_domain_map_range
- \+ *lemma* emb_domain_eq_map_domain
- \+ *lemma* injective_map_domain
- \+ *def* emb_domain



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/d7bd41f)
feat(linear_algebra/dimension): add exists_mem_ne_zero_of_dim_pos
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* exists_mem_ne_zero_of_ne_bot
- \+ *lemma* exists_mem_ne_zero_of_dim_pos



## [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/22352ff)
feat(linear_algebra/dimension): add dim_span_le; add rank_finset_sum_le
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_span_le
- \+ *lemma* dim_span_of_finset
- \+ *lemma* rank_zero
- \+ *lemma* rank_finset_sum_le



## [2019-03-26 17:46:31+01:00](https://github.com/leanprover-community/mathlib/commit/f882b8b)
feat(data/polynomial): rec_on_horner ([#739](https://github.com/leanprover-community/mathlib/pull/739))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* coeff_mk
- \+ *lemma* degree_le_zero_iff
- \+ *lemma* div_X_mul_X_add
- \+ *lemma* div_X_C
- \+ *lemma* div_X_eq_zero_iff
- \+ *lemma* div_X_add
- \+ *lemma* degree_lt_degree_mul_X
- \+ *lemma* degree_div_X_lt
- \+ *lemma* degree_pos_induction_on
- \+ *def* div_X
- \+ *def* nonzero_comm_semiring.of_polynomial_ne
- \+ *def* rec_on_horner



## [2019-03-26 00:11:19](https://github.com/leanprover-community/mathlib/commit/410ae5d)
feat(group_theory/subgroup): add inv_iff_ker' and related ([#790](https://github.com/leanprover-community/mathlib/pull/790))
* feat(group_theory/subgroup): add inv_iff_ker' and related
* correcting spacing and adding to_additive attribute
* changing name to ker-mk
#### Estimated changes
Modified src/group_theory/quotient_group.lean
- \+ *lemma* ker_mk

Modified src/group_theory/subgroup.lean
- \+ *lemma* one_ker_inv'
- \+ *lemma* inv_ker_one'
- \+ *lemma* one_iff_ker_inv'
- \+ *lemma* inv_iff_ker'



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
- \+/\- *lemma* mem_orbit_iff
- \+/\- *lemma* mem_orbit
- \+/\- *lemma* mem_orbit_self
- \+/\- *lemma* mem_stabilizer_iff
- \+/\- *lemma* mem_fixed_points
- \+/\- *lemma* mem_fixed_points'
- \+/\- *lemma* bijective
- \+/\- *lemma* orbit_eq_iff
- \- *lemma* comp_hom
- \+/\- *def* orbit
- \+/\- *def* stabilizer
- \+/\- *def* fixed_points
- \+ *def* comp_hom

Modified src/group_theory/sylow.lean
- \+/\- *lemma* mem_fixed_points_iff_card_orbit_eq_one
- \+/\- *lemma* card_modeq_card_fixed_points

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
- \+ *lemma* id
- \+ *lemma* comp
- \+ *lemma* comp'
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* map_comp'

Modified src/data/equiv/algebra.lean
- \+ *lemma* one
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans
- \+ *def* map_equiv



## [2019-03-21 23:44:25](https://github.com/leanprover-community/mathlib/commit/798a08d)
feat(group_theory/submonoid): add closure_singleton ([#810](https://github.com/leanprover-community/mathlib/pull/810))
* feat(group_theory/submonoid): add closure_singleton
* adding some to_additive
#### Estimated changes
Modified src/group_theory/submonoid.lean
- \+ *lemma* powers.one_mem
- \+ *lemma* multiples.zero_mem
- \+ *lemma* powers.self_mem
- \+ *lemma* multiples.self_mem
- \+ *theorem* closure_singleton



## [2019-03-20 10:16:08-04:00](https://github.com/leanprover-community/mathlib/commit/098c2cb)
feat(tactic/wlog): `discharger` defaults to classical `tauto` ([#836](https://github.com/leanprover-community/mathlib/pull/836))
#### Estimated changes
Modified src/tactic/wlog.lean




## [2019-03-18 00:04:29](https://github.com/leanprover-community/mathlib/commit/d60d161)
feat(linear_algebra/basic): add ring instance ([#823](https://github.com/leanprover-community/mathlib/pull/823))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *def* general_linear_group
- \- *def* endomorphism_ring

Modified src/ring_theory/algebra.lean




## [2019-03-17 21:08:06](https://github.com/leanprover-community/mathlib/commit/9ff5e8d)
feat(algebra/punit_instances): punit instances ([#828](https://github.com/leanprover-community/mathlib/pull/828))
#### Estimated changes
Created src/algebra/punit_instances.lean
- \+ *lemma* zero_eq
- \+ *lemma* one_eq
- \+ *lemma* add_eq
- \+ *lemma* mul_eq
- \+ *lemma* neg_eq
- \+ *lemma* inv_eq
- \+ *lemma* smul_eq
- \+ *lemma* top_eq
- \+ *lemma* bot_eq
- \+ *lemma* sup_eq
- \+ *lemma* inf_eq
- \+ *lemma* Sup_eq
- \+ *lemma* Inf_eq
- \+ *lemma* not_lt



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

Created src/data/real/hyperreal.lean
- \+ *lemma* epsilon_pos
- \+ *lemma* epsilon_ne_zero
- \+ *lemma* omega_pos
- \+ *lemma* omega_ne_zero
- \+ *lemma* lt_of_tendsto_zero_of_pos
- \+ *lemma* neg_lt_of_tendsto_zero_of_neg
- \+ *lemma* gt_of_tendsto_zero_of_neg
- \+ *lemma* epsilon_lt_pos
- \+ *theorem* epsilon_eq_inv_omega
- \+ *theorem* inv_epsilon_eq_omega
- \+ *theorem* epsilon_mul_omega
- \+ *theorem* is_st_unique
- \+ *theorem* infinitesimal_of_tendsto_zero
- \+ *theorem* infinitesimal_epsilon
- \+ *def* hyperreal
- \+ *def* is_st
- \+ *def* infinitesimal

Modified src/data/real/nnreal.lean
- \- *lemma* inv_eq_zero

Modified src/data/set/basic.lean
- \+ *lemma* set_of_eq_eq_singleton

Modified src/order/filter/basic.lean
- \+ *lemma* cofinite_ne_bot
- \+ *lemma* hyperfilter_le_cofinite
- \+ *lemma* is_ultrafilter_hyperfilter
- \+ *theorem* nmem_hyperfilter_of_finite
- \+ *theorem* compl_mem_hyperfilter_of_finite
- \+ *theorem* mem_hyperfilter_of_finite_compl

Created src/order/filter/filter_product.lean
- \+ *lemma* of_seq_zero
- \+ *lemma* of_seq_add
- \+ *lemma* of_seq_neg
- \+ *lemma* of_seq_one
- \+ *lemma* of_seq_mul
- \+ *lemma* of_seq_inv
- \+ *lemma* of_eq_coe
- \+ *lemma* of_id
- \+ *lemma* of_eq
- \+ *lemma* of_ne
- \+ *lemma* of_eq_zero
- \+ *lemma* of_ne_zero
- \+ *lemma* of_zero
- \+ *lemma* of_add
- \+ *lemma* of_neg
- \+ *lemma* of_one
- \+ *lemma* of_mul
- \+ *lemma* of_inv
- \+ *lemma* of_rel_of_rel
- \+ *lemma* of_rel
- \+ *lemma* of_rel_of_rel₂
- \+ *lemma* of_rel₂
- \+ *lemma* of_le_of_le
- \+ *lemma* of_le
- \+ *lemma* lt_def
- \+ *lemma* lt_def'
- \+ *lemma* of_lt_of_lt
- \+ *lemma* of_lt
- \+ *theorem* of_inj
- \+ *theorem* of_seq_fun
- \+ *theorem* of_seq_fun₂
- \+ *def* bigly_equal
- \+ *def* filterprod
- \+ *def* of_seq
- \+ *def* of
- \+ *def* lift
- \+ *def* lift₂
- \+ *def* lift_rel
- \+ *def* lift_rel₂



## [2019-03-16 09:30:48-05:00](https://github.com/leanprover-community/mathlib/commit/0c2c2bd)
feat(group_theory/perm/cycles): cycle_factors ([#815](https://github.com/leanprover-community/mathlib/pull/815))
#### Estimated changes
Created src/group_theory/perm/cycles.lean
- \+ *lemma* same_cycle.refl
- \+ *lemma* same_cycle.symm
- \+ *lemma* same_cycle.trans
- \+ *lemma* apply_eq_self_iff_of_same_cycle
- \+ *lemma* same_cycle_of_is_cycle
- \+ *lemma* same_cycle_apply
- \+ *lemma* same_cycle_cycle
- \+ *lemma* same_cycle_inv
- \+ *lemma* same_cycle_inv_apply
- \+ *lemma* cycle_of_apply
- \+ *lemma* cycle_of_inv
- \+ *lemma* cycle_of_pow_apply_self
- \+ *lemma* cycle_of_gpow_apply_self
- \+ *lemma* cycle_of_apply_of_same_cycle
- \+ *lemma* cycle_of_apply_of_not_same_cycle
- \+ *lemma* cycle_of_apply_self
- \+ *lemma* cycle_of_cycle
- \+ *lemma* cycle_of_one
- \+ *lemma* is_cycle_cycle_of
- \+ *def* same_cycle
- \+ *def* cycle_of
- \+ *def* cycle_factors_aux
- \+ *def* cycle_factors

Renamed src/group_theory/perm.lean to src/group_theory/perm/sign.lean
- \+ *lemma* subtype_perm_one
- \+ *lemma* of_subtype_one
- \+ *lemma* disjoint.symm
- \+ *lemma* disjoint_comm
- \+ *lemma* disjoint_mul_comm
- \+ *lemma* disjoint_one_left
- \+ *lemma* disjoint_one_right
- \+ *lemma* disjoint_mul_left
- \+ *lemma* disjoint_mul_right
- \+ *lemma* disjoint_prod_right
- \+ *lemma* disjoint_prod_perm
- \+ *lemma* pow_apply_eq_self_of_apply_eq_self
- \+ *lemma* gpow_apply_eq_self_of_apply_eq_self
- \+ *lemma* pow_apply_eq_of_apply_apply_eq_self
- \+ *lemma* gpow_apply_eq_of_apply_apply_eq_self
- \+ *lemma* ne_and_ne_of_swap_mul_apply_ne_self
- \+ *lemma* support_swap_mul_eq
- \+ *lemma* card_support_swap_mul
- \+ *lemma* swap_induction_on
- \+/\- *lemma* is_cycle_inv
- \+ *lemma* exists_gpow_eq_of_is_cycle
- \- *lemma* exists_int_pow_eq_of_is_cycle
- \- *lemma* pow_apply_eq_of_apply_apply_eq_self_nat
- \- *lemma* pow_apply_eq_of_apply_apply_eq_self_int
- \- *lemma* support_swap_mul
- \- *lemma* support_swap_mul_cycle
- \+ *def* disjoint
- \+/\- *def* is_cycle

Modified src/linear_algebra/determinant.lean


Modified test/fin_cases.lean




## [2019-03-16 09:28:41-05:00](https://github.com/leanprover-community/mathlib/commit/7b001c9)
feat(data/set/intervals): add missing intervals + some lemmas ([#805](https://github.com/leanprover-community/mathlib/pull/805))
The lemmas about Icc ⊆ I** are important for convexity
#### Estimated changes
Modified src/data/set/intervals.lean
- \+/\- *lemma* mem_Icc
- \+ *lemma* mem_Iic
- \+ *lemma* mem_Ioc
- \+ *lemma* mem_Ici
- \+ *lemma* mem_Ioi
- \+ *lemma* Ioc_eq_empty
- \+ *lemma* Ioi_ne_empty
- \+ *lemma* Iic_ne_empty
- \+ *lemma* Ici_ne_empty
- \+ *lemma* Icc_subset_Icc_iff
- \+ *lemma* Icc_subset_Ioo_iff
- \+ *lemma* Icc_subset_Ico_iff
- \+ *lemma* Icc_subset_Ioc_iff
- \+ *lemma* Icc_subset_Iio_iff
- \+ *lemma* Icc_subset_Ioi_iff
- \+ *lemma* Icc_subset_Iic_iff
- \+ *lemma* Icc_subset_Ici_iff
- \+/\- *def* Iio
- \+ *def* Iic
- \+ *def* Ioc
- \+ *def* Ici
- \+ *def* Ioi



## [2019-03-14 10:32:41+01:00](https://github.com/leanprover-community/mathlib/commit/2bf44d3)
refactor(*): rename metric_space_subtype to subtype.metric_space ([#817](https://github.com/leanprover-community/mathlib/pull/817))
#### Estimated changes
Modified src/data/padics/padic_integers.lean


Modified src/topology/metric_space/basic.lean




## [2019-03-14 10:31:53+01:00](https://github.com/leanprover-community/mathlib/commit/c5afc52)
feat(topology/metric_space/baire): Baire theorem ([#816](https://github.com/leanprover-community/mathlib/pull/816))
#### Estimated changes
Modified src/data/set/countable.lean
- \+ *lemma* exists_surjective_of_countable
- \+ *lemma* countable_prod

Modified src/data/set/lattice.lean
- \+ *lemma* sInter_union_sInter
- \+ *lemma* sUnion_inter_sUnion
- \+ *lemma* sInter_bUnion
- \+ *lemma* sUnion_bUnion
- \+ *lemma* bUnion_range
- \+ *lemma* bInter_range
- \+ *lemma* bUnion_image
- \+ *lemma* bInter_image
- \+ *theorem* sUnion_range
- \+ *theorem* sInter_range

Modified src/order/complete_boolean_algebra.lean
- \+ *theorem* Inf_sup_eq
- \+ *theorem* Sup_inf_eq
- \+ *theorem* Inf_sup_Inf
- \+ *theorem* Sup_inf_Sup

Modified src/order/complete_lattice.lean
- \+ *theorem* infi_le_infi_of_subset
- \+ *theorem* supr_le_supr_of_subset

Modified src/topology/basic.lean
- \+ *lemma* is_closed_frontier
- \+ *lemma* interior_frontier

Created src/topology/metric_space/baire.lean
- \+ *lemma* is_open.is_Gδ
- \+ *lemma* is_Gδ_bInter_of_open
- \+ *lemma* is_Gδ_Inter_of_open
- \+ *lemma* is_Gδ_sInter
- \+ *lemma* is_Gδ.union
- \+ *theorem* dense_Inter_of_open_nat
- \+ *theorem* dense_sInter_of_open
- \+ *theorem* dense_bInter_of_open
- \+ *theorem* dense_Inter_of_open
- \+ *theorem* dense_sInter_of_Gδ
- \+ *theorem* dense_bInter_of_Gδ
- \+ *theorem* dense_Inter_of_Gδ
- \+ *theorem* dense_bUnion_interior_of_closed
- \+ *theorem* dense_sUnion_interior_of_closed
- \+ *theorem* dense_Union_interior_of_closed
- \+ *theorem* nonempty_interior_of_Union_of_closed
- \+ *def* is_Gδ

Modified src/topology/metric_space/basic.lean
- \+ *theorem* mem_closed_ball_self



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
- \+ *lemma* inter_consecutive
- \+ *theorem* image_add
- \+ *theorem* image_sub
- \+ *theorem* succ_top'
- \+/\- *theorem* pred_singleton
- \- *theorem* map_add

Modified src/data/list/basic.lean
- \+ *lemma* inter_consecutive
- \+ *lemma* bag_inter_consecutive
- \+ *theorem* map_sub_range'
- \+/\- *theorem* map_add
- \+ *theorem* map_sub
- \+/\- *theorem* pred_singleton

Modified src/data/multiset.lean
- \+ *lemma* inter_consecutive
- \+ *theorem* map_sub
- \+/\- *theorem* pred_singleton



## [2019-03-12 13:53:34+01:00](https://github.com/leanprover-community/mathlib/commit/2738f9b)
chore(topology/*): @uniformity α _ becomes 𝓤 α ([#814](https://github.com/leanprover-community/mathlib/pull/814))
This is a binder type change and a local notation
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/uniform_group.lean
- \+/\- *lemma* uniformity_translate
- \+/\- *lemma* uniformity_eq_comap_nhds_zero
- \+/\- *lemma* uniformity_eq_comap_nhds_zero'

Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* uniformity_dist
- \+/\- *theorem* uniformity_dist'
- \+/\- *theorem* uniformity_edist

Modified src/topology/metric_space/cau_seq_filter.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* uniformity_edist'
- \+/\- *theorem* uniformity_edist''

Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* refl_le_uniformity
- \+/\- *lemma* refl_mem_uniformity
- \+/\- *lemma* symm_le_uniformity
- \+/\- *lemma* comp_le_uniformity
- \+/\- *lemma* tendsto_swap_uniformity
- \+/\- *lemma* tendsto_const_uniformity
- \+/\- *lemma* comp_mem_uniformity_sets
- \+/\- *lemma* symm_of_uniformity
- \+/\- *lemma* comp_symm_of_uniformity
- \+/\- *lemma* uniformity_le_symm
- \+/\- *lemma* uniformity_eq_symm
- \+/\- *lemma* nhds_eq_comap_uniformity
- \+/\- *lemma* nhds_eq_uniformity
- \+/\- *lemma* mem_nhds_left
- \+/\- *lemma* mem_nhds_right
- \+/\- *lemma* tendsto_right_nhds_uniformity
- \+/\- *lemma* tendsto_left_nhds_uniformity
- \+/\- *lemma* nhdset_of_mem_uniformity
- \+/\- *lemma* uniformity_eq_uniformity_closure
- \+/\- *lemma* uniformity_eq_uniformity_interior
- \+/\- *lemma* interior_mem_uniformity
- \+/\- *lemma* mem_uniformity_is_closed
- \+/\- *def* uniformity

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *lemma* cauchy_iff
- \+/\- *lemma* cauchy_map_iff
- \+/\- *def* cauchy

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
- \+ *theorem* induction_on₂
- \+ *theorem* induction_on₃
- \+ *theorem* ext_iff
- \+ *theorem* lookup_empty
- \+/\- *theorem* mem_insert
- \+ *theorem* mem_union
- \+ *theorem* union_to_finmap
- \+ *theorem* keys_union
- \+ *theorem* lookup_union_left
- \+ *theorem* lookup_union_right
- \+ *theorem* mem_lookup_union
- \+ *theorem* mem_lookup_union_middle
- \+ *def* union

Modified src/data/list/alist.lean
- \+ *theorem* empty_entries
- \+ *theorem* singleton_entries
- \+ *theorem* lookup_empty
- \+/\- *theorem* mem_insert
- \+/\- *theorem* lookup_insert_ne
- \+ *theorem* union_entries
- \+ *theorem* empty_union
- \+ *theorem* union_empty
- \+ *theorem* mem_union
- \+ *theorem* perm_union
- \+ *theorem* lookup_union_left
- \+ *theorem* lookup_union_right
- \+ *theorem* mem_lookup_union
- \+ *theorem* mem_lookup_union_middle
- \+ *def* union

Modified src/data/list/sigma.lean
- \+ *theorem* kerase_append_left
- \+ *theorem* kerase_append_right
- \+ *theorem* kerase_comm
- \+/\- *theorem* mem_keys_kinsert
- \+/\- *theorem* lookup_kinsert_ne
- \+ *theorem* nil_kunion
- \+ *theorem* kunion_nil
- \+ *theorem* kunion_cons
- \+ *theorem* mem_keys_kunion
- \+ *theorem* kunion_kerase
- \+ *theorem* kunion_nodupkeys
- \+ *theorem* perm_kunion_left
- \+ *theorem* perm_kunion_right
- \+ *theorem* perm_kunion
- \+ *theorem* lookup_kunion_left
- \+ *theorem* lookup_kunion_right
- \+ *theorem* mem_lookup_kunion
- \+ *theorem* mem_lookup_kunion_middle
- \+ *def* kunion



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
- \- *theorem* eq_nil_of_forall_not_mem

Modified src/data/multiset.lean




## [2019-03-09 11:34:38](https://github.com/leanprover-community/mathlib/commit/e8818fa)
feat(data/set/finite): add finite_lt_nat ([#807](https://github.com/leanprover-community/mathlib/pull/807))
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* finite_lt_nat



## [2019-03-08 20:10:50](https://github.com/leanprover-community/mathlib/commit/7de57e8)
feat(ring_theory/noetherian): Nakayama's Lemma ([#778](https://github.com/leanprover-community/mathlib/pull/778))
* feat(ring_theory/noetherian): Nakayama's Lemma
* Update src/ring_theory/noetherian.lean
Co-Authored-By: kckennylau <kc_kennylau@yahoo.com.hk>
#### Estimated changes
Modified src/ring_theory/ideal_operations.lean
- \+ *theorem* mem_smul_span_singleton

Modified src/ring_theory/noetherian.lean
- \+ *theorem* exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul



## [2019-03-08 15:01:45+01:00](https://github.com/leanprover-community/mathlib/commit/1159fa9)
refactot(data/equiv/basic): rename apply_inverse_apply to apply_symm_apply ([#800](https://github.com/leanprover-community/mathlib/pull/800))
#### Estimated changes
Modified src/category_theory/adjunction.lean


Modified src/data/equiv/basic.lean
- \+ *lemma* symm_trans_apply
- \- *lemma* inverse_trans_apply
- \+ *theorem* apply_symm_apply
- \+ *theorem* symm_apply_apply
- \- *theorem* apply_inverse_apply
- \- *theorem* inverse_apply_apply

Modified src/data/equiv/denumerable.lean


Modified src/data/finsupp.lean


Modified src/data/multivariate_polynomial.lean


Modified src/field_theory/perfect_closure.lean


Modified src/order/order_iso.lean
- \+ *theorem* apply_symm_apply
- \+ *theorem* symm_apply_apply
- \- *theorem* apply_inverse_apply
- \- *theorem* inverse_apply_apply

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
- \+/\- *theorem* mem_sets

Modified src/data/analysis/topology.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* integral_congr

Modified src/measure_theory/measure_space.lean
- \+/\- *def* all_ae

Modified src/order/filter/basic.lean
- \+/\- *lemma* univ_mem_sets
- \+/\- *lemma* mem_sets_of_superset
- \+/\- *lemma* inter_mem_sets
- \+/\- *lemma* univ_mem_sets'
- \+/\- *lemma* mp_sets
- \+/\- *lemma* congr_sets
- \+/\- *lemma* exists_sets_subset_iff
- \+/\- *lemma* monotone_mem_sets
- \+/\- *lemma* mem_principal_sets
- \+/\- *lemma* mem_principal_self
- \+/\- *lemma* mem_inf_sets_of_left
- \+/\- *lemma* mem_inf_sets_of_right
- \+/\- *lemma* mem_top_sets_iff_forall
- \+/\- *lemma* mem_top_sets
- \+/\- *lemma* mem_bot_sets
- \+/\- *lemma* le_principal_iff
- \+/\- *lemma* empty_in_sets_eq_bot
- \+/\- *lemma* inhabited_of_mem_sets
- \+/\- *lemma* mem_sets_of_neq_bot
- \+ *lemma* mem_infi
- \+ *lemma* mem_infi_finite
- \+/\- *lemma* inf_principal_eq_bot
- \+/\- *lemma* mem_map
- \+/\- *lemma* image_mem_map
- \+/\- *lemma* range_mem_map
- \+/\- *lemma* mem_map_sets_iff
- \+/\- *lemma* mem_pure
- \+/\- *lemma* mem_pure_iff
- \+/\- *lemma* map_comap
- \+/\- *lemma* map_cong
- \+/\- *lemma* map_inf'
- \+/\- *lemma* le_map
- \+/\- *lemma* singleton_mem_pure_sets
- \+/\- *lemma* bind_mono
- \+/\- *lemma* mem_infi_sets
- \+/\- *lemma* infi_sets_induct
- \+/\- *lemma* mem_at_top
- \+/\- *lemma* mem_or_mem_of_ultrafilter
- \+/\- *theorem* le_def
- \+/\- *theorem* mem_comap_sets
- \+/\- *theorem* preimage_mem_comap
- \+/\- *theorem* le_map_comap_of_surjective'
- \+/\- *theorem* map_comap_of_surjective'

Modified src/order/filter/partial.lean
- \+/\- *theorem* ptendsto'_of_ptendsto
- \+/\- *def* mem_pmap

Modified src/topology/algebra/group.lean
- \+/\- *lemma* exists_nhds_split
- \+/\- *lemma* exists_nhds_split_inv
- \+/\- *lemma* exists_nhds_split4
- \+/\- *lemma* exists_Z_half

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* lt_mem_nhds
- \+/\- *lemma* le_mem_nhds
- \+/\- *lemma* gt_mem_nhds
- \+/\- *lemma* ge_mem_nhds
- \+/\- *lemma* mem_nhds_orderable_dest

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean
- \+/\- *lemma* mem_of_nhds
- \+/\- *lemma* is_open_iff_mem_nhds
- \+/\- *theorem* mem_closure_iff_nhds

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/compact_open.lean


Modified src/topology/constructions.lean
- \+/\- *lemma* map_nhds_subtype_val_eq

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* coe_range_mem_nhds

Modified src/topology/maps.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* mem_nhds_iff
- \+/\- *theorem* ball_mem_nhds

Modified src/topology/metric_space/cau_seq_filter.lean
- \+/\- *lemma* set_seq_of_cau_filter_mem_sets

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* mem_nhds_iff
- \+/\- *theorem* ball_mem_nhds

Modified src/topology/order.lean
- \+/\- *lemma* map_nhds_induced_eq

Modified src/topology/separation.lean
- \+/\- *lemma* compl_singleton_mem_nhds
- \+/\- *lemma* nhds_is_closed

Modified src/topology/sequences.lean


Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* refl_mem_uniformity
- \+/\- *lemma* comp_mem_uniformity_sets
- \+/\- *lemma* symm_of_uniformity
- \+/\- *lemma* comp_symm_of_uniformity
- \+/\- *lemma* nhdset_of_mem_uniformity
- \+/\- *lemma* interior_mem_uniformity
- \+/\- *lemma* mem_uniformity_is_closed
- \+ *lemma* mem_map_sets_iff'

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
- \+ *lemma* to_equiv_symm
- \+ *lemma* to_equiv_symm_apply

Modified src/ring_theory/localization.lean
- \+ *lemma* lift'_mk
- \+/\- *lemma* lift'_apply_coe
- \+ *lemma* map_id
- \+ *lemma* map_comp_map
- \+ *lemma* map_map



## [2019-03-07 10:17:21-05:00](https://github.com/leanprover-community/mathlib/commit/26bd400)
feat(data/list): lemmas about count and bag_inter ([#797](https://github.com/leanprover-community/mathlib/pull/797))
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* to_finset_inter

Modified src/data/list/basic.lean
- \+ *theorem* count_erase_self
- \+ *theorem* count_erase_of_ne
- \+/\- *theorem* mem_bag_inter
- \+ *theorem* count_bag_inter
- \+ *theorem* bag_inter_nil_iff_inter_nil

Modified src/data/multiset.lean
- \+ *theorem* coe_inter



## [2019-03-06 20:07:22-05:00](https://github.com/leanprover-community/mathlib/commit/181647b)
feat(tactic/basic): utility functions for names ([#791](https://github.com/leanprover-community/mathlib/pull/791))
#### Estimated changes
Modified src/tactic/basic.lean




## [2019-03-06 23:01:10](https://github.com/leanprover-community/mathlib/commit/48eaf05)
feat(algebra/group): units.coe_map
#### Estimated changes
Modified src/algebra/group.lean
- \+ *lemma* coe_map



## [2019-03-06 22:11:42](https://github.com/leanprover-community/mathlib/commit/e286452)
feat(data/nat/basic): some lemmas ([#792](https://github.com/leanprover-community/mathlib/pull/792))
* feat(data/nat/basic): some lemmas
* fixing namespace, moving lemma
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* one_le_of_lt
- \+ *lemma* le_pred_of_lt
- \+ *lemma* pred_one_add
- \+ *lemma* sub_sub_sub_cancel_right



## [2019-03-06 10:16:34-05:00](https://github.com/leanprover-community/mathlib/commit/61e02dd)
feat(data/finset): missing fold_map lemma ([#794](https://github.com/leanprover-community/mathlib/pull/794))
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* fold_map



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
- \+ *lemma* to_units_coe
- \+/\- *lemma* of_zero
- \+/\- *lemma* of_one
- \+/\- *lemma* of_add
- \+/\- *lemma* of_sub
- \+/\- *lemma* of_mul
- \+/\- *lemma* of_neg
- \+/\- *lemma* of_pow
- \+ *lemma* of_is_unit
- \+ *lemma* of_is_unit'
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_pow
- \+ *lemma* coe_is_unit
- \+ *lemma* coe_is_unit'
- \+ *lemma* mk_eq
- \+ *lemma* lift'_of
- \+ *lemma* lift'_coe
- \+ *lemma* lift_of
- \+ *lemma* lift_coe
- \+ *lemma* lift'_comp_of
- \+ *lemma* lift_comp_of
- \+ *lemma* lift'_apply_coe
- \+ *lemma* lift_apply_coe
- \+ *lemma* map_of
- \+ *lemma* map_coe
- \+ *lemma* map_comp_of
- \+ *lemma* away.lift_of
- \+ *lemma* away.lift_coe
- \+ *lemma* away.lift_comp_of
- \+ *lemma* non_zero_divisors_one_val
- \+ *lemma* mem_non_zero_divisors_iff_ne_zero
- \+ *lemma* mk_inv
- \+ *lemma* mk_inv'
- \+ *lemma* mk_eq_div'
- \- *lemma* ne_zero_of_mem_non_zero_divisors
- \- *lemma* mem_non_zero_divisors_of_ne_zero
- \+/\- *theorem* map_comap
- \+ *def* localization
- \+/\- *def* mk
- \+/\- *def* of
- \+ *def* to_units
- \+ *def* lift'
- \+ *def* map
- \+ *def* equiv_of_equiv
- \+/\- *def* away
- \+/\- *def* at_prime
- \+/\- *def* fraction_ring
- \- *def* loc



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
- \+ *lemma* tendsto_inv
- \+ *lemma* is_open_map_mul_left
- \+ *lemma* is_open_map_mul_right
- \+ *lemma* exists_nhds_split
- \+ *lemma* exists_nhds_split_inv
- \+ *lemma* exists_nhds_split4
- \+ *lemma* nhds_one_symm
- \+ *lemma* nhds_translation_mul_inv
- \+ *lemma* quotient_group_saturate
- \+ *lemma* quotient_group.open_coe
- \+ *lemma* continuous_sub
- \+ *lemma* continuous_sub'
- \+ *lemma* tendsto_sub
- \+ *lemma* nhds_translation
- \- *lemma* uniformity_eq_comap_nhds_zero'
- \- *lemma* topological_add_group_is_uniform
- \- *lemma* to_uniform_space_eq
- \- *def* topological_add_group.to_uniform_space

Created src/topology/algebra/group_completion.lean
- \+ *lemma* coe_zero
- \+ *lemma* coe_neg
- \+ *lemma* coe_add
- \+ *lemma* is_add_group_hom_extension
- \+ *lemma* is_add_group_hom_map
- \+ *lemma* is_add_group_hom_prod

Modified src/topology/algebra/infinite_sum.lean


Created src/topology/algebra/monoid.lean
- \+ *lemma* continuous_mul'
- \+ *lemma* continuous_mul
- \+ *lemma* continuous_pow
- \+ *lemma* tendsto_mul'
- \+ *lemma* tendsto_mul
- \+ *lemma* tendsto_list_prod
- \+ *lemma* continuous_list_prod
- \+ *lemma* tendsto_multiset_prod
- \+ *lemma* tendsto_finset_prod
- \+ *lemma* continuous_multiset_prod
- \+ *lemma* continuous_finset_prod

Renamed src/topology/algebra/topological_structures.lean to src/topology/algebra/ordered.lean
- \- *lemma* continuous_mul'
- \- *lemma* continuous_mul
- \- *lemma* continuous_pow
- \- *lemma* tendsto_mul'
- \- *lemma* tendsto_mul
- \- *lemma* tendsto_list_prod
- \- *lemma* continuous_list_prod
- \- *lemma* tendsto_multiset_prod
- \- *lemma* tendsto_finset_prod
- \- *lemma* continuous_multiset_prod
- \- *lemma* continuous_finset_prod
- \- *lemma* continuous_inv'
- \- *lemma* continuous_inv
- \- *lemma* tendsto_inv
- \- *lemma* is_open_map_mul_left
- \- *lemma* is_open_map_mul_right
- \- *lemma* exists_nhds_split
- \- *lemma* exists_nhds_split_inv
- \- *lemma* exists_nhds_split4
- \- *lemma* nhds_one_symm
- \- *lemma* nhds_translation_mul_inv
- \- *lemma* continuous_sub
- \- *lemma* continuous_sub'
- \- *lemma* tendsto_sub
- \- *lemma* nhds_translation
- \- *lemma* uniform_continuous_sub'
- \- *lemma* uniform_continuous_sub
- \- *lemma* uniform_continuous_neg
- \- *lemma* uniform_continuous_neg'
- \- *lemma* uniform_continuous_add
- \- *lemma* uniform_continuous_add'
- \- *lemma* uniformity_translate
- \- *lemma* uniform_embedding_translate
- \- *lemma* uniformity_eq_comap_nhds_zero
- \- *lemma* group_separation_rel
- \- *lemma* uniform_continuous_of_tendsto_zero
- \- *lemma* uniform_continuous_of_continuous
- \- *lemma* ideal.coe_closure
- \- *theorem* uniform_add_group.mk'
- \- *def* ideal.closure

Deleted src/topology/algebra/quotient.lean
- \- *lemma* {u}
- \- *lemma* quotient_group_saturate
- \- *lemma* quotient_group.open_coe
- \- *lemma* quotient_ring_saturate
- \- *lemma* quotient_ring.is_open_map_coe
- \- *lemma* quotient_ring.quotient_map_coe_coe
- \- *lemma* ring_sep_rel
- \- *lemma* ring_sep_quot
- \- *def* comm_ring_congr
- \- *def* sep_quot_equiv_ring_quot

Created src/topology/algebra/ring.lean
- \+ *lemma* ideal.coe_closure
- \+ *lemma* quotient_ring_saturate
- \+ *lemma* quotient_ring.is_open_map_coe
- \+ *lemma* quotient_ring.quotient_map_coe_coe
- \+ *def* ideal.closure

Created src/topology/algebra/uniform_group.lean
- \+ *lemma* uniform_continuous_sub'
- \+ *lemma* uniform_continuous_sub
- \+ *lemma* uniform_continuous_neg
- \+ *lemma* uniform_continuous_neg'
- \+ *lemma* uniform_continuous_add
- \+ *lemma* uniform_continuous_add'
- \+ *lemma* uniformity_translate
- \+ *lemma* uniform_embedding_translate
- \+ *lemma* uniformity_eq_comap_nhds_zero
- \+ *lemma* group_separation_rel
- \+ *lemma* uniform_continuous_of_tendsto_zero
- \+ *lemma* uniform_continuous_of_continuous
- \+ *lemma* uniformity_eq_comap_nhds_zero'
- \+ *lemma* topological_add_group_is_uniform
- \+ *lemma* to_uniform_space_eq
- \+ *lemma* is_Z_bilin.zero_left
- \+ *lemma* is_Z_bilin.zero_right
- \+ *lemma* is_Z_bilin.zero
- \+ *lemma* is_Z_bilin.neg_left
- \+ *lemma* is_Z_bilin.neg_right
- \+ *lemma* is_Z_bilin.sub_left
- \+ *lemma* is_Z_bilin.sub_right
- \+ *lemma* is_Z_bilin.tendsto_zero_left
- \+ *lemma* is_Z_bilin.tendsto_zero_right
- \+ *lemma* tendsto_sub_comap_self
- \+ *lemma* continuous_extend_of_cauchy
- \+ *theorem* uniform_add_group.mk'
- \+ *theorem* extend_Z_bilin
- \+ *def* topological_add_group.to_uniform_space

Created src/topology/algebra/uniform_ring.lean
- \+ *lemma* coe_one
- \+ *lemma* continuous_mul'
- \+ *lemma* coe_mul
- \+ *lemma* continuous_mul
- \+ *lemma* ring_sep_rel
- \+ *lemma* ring_sep_quot
- \+ *def* sep_quot_equiv_ring_quot

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/polynomial.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/uniform_space/basic.lean
- \- *lemma* uniform_embedding.uniform_continuous
- \- *lemma* uniform_embedding.uniform_continuous_iff
- \- *lemma* uniform_embedding.embedding
- \- *lemma* uniform_embedding.dense_embedding
- \- *lemma* closure_image_mem_nhds_of_uniform_embedding
- \- *lemma* cauchy_iff
- \- *lemma* cauchy_map_iff
- \- *lemma* cauchy_downwards
- \- *lemma* cauchy_nhds
- \- *lemma* cauchy_pure
- \- *lemma* le_nhds_of_cauchy_adhp
- \- *lemma* le_nhds_iff_adhp_of_cauchy
- \- *lemma* cauchy_map
- \- *lemma* cauchy_comap
- \- *lemma* is_complete_image_iff
- \- *lemma* separated_equiv
- \- *lemma* is_closed_of_is_complete
- \- *lemma* totally_bounded_subset
- \- *lemma* totally_bounded_empty
- \- *lemma* totally_bounded_closure
- \- *lemma* totally_bounded_image
- \- *lemma* totally_bounded_preimage
- \- *lemma* cauchy_of_totally_bounded_of_ultrafilter
- \- *lemma* totally_bounded_iff_filter
- \- *lemma* totally_bounded_iff_ultrafilter
- \- *lemma* compact_iff_totally_bounded_complete
- \- *lemma* cauchy_seq_iff_prod_map
- \- *lemma* complete_univ
- \- *lemma* complete_space_of_is_complete_univ
- \- *lemma* cauchy_iff_exists_le_nhds
- \- *lemma* cauchy_map_iff_exists_tendsto
- \- *lemma* is_complete_of_is_closed
- \- *lemma* compact_of_totally_bounded_is_closed
- \- *lemma* complete_space_extension
- \- *lemma* uniformly_extend_of_emb
- \- *lemma* uniformly_extend_exists
- \- *lemma* uniformly_extend_spec
- \- *lemma* uniform_continuous_uniformly_extend
- \- *lemma* uniform_embedding_comap
- \- *lemma* uniform_embedding_subtype_emb
- \- *lemma* uniform_extend_subtype
- \- *lemma* cauchy_prod
- \- *lemma* uniform_embedding.prod
- \- *lemma* continuous_extend_of_cauchy
- \- *theorem* uniform_embedding_def
- \- *theorem* uniform_embedding_def'
- \- *theorem* separated_def
- \- *theorem* separated_def'
- \- *theorem* totally_bounded_iff_subset
- \- *theorem* cauchy_seq_tendsto_of_complete
- \- *theorem* le_nhds_lim_of_cauchy
- \- *def* uniform_embedding
- \- *def* cauchy
- \- *def* is_complete
- \- *def* separated
- \- *def* totally_bounded
- \- *def* cauchy_seq

Created src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy_iff
- \+ *lemma* cauchy_map_iff
- \+ *lemma* cauchy_downwards
- \+ *lemma* cauchy_nhds
- \+ *lemma* cauchy_pure
- \+ *lemma* le_nhds_of_cauchy_adhp
- \+ *lemma* le_nhds_iff_adhp_of_cauchy
- \+ *lemma* cauchy_map
- \+ *lemma* cauchy_comap
- \+ *lemma* cauchy_seq_iff_prod_map
- \+ *lemma* complete_univ
- \+ *lemma* cauchy_prod
- \+ *lemma* complete_space_of_is_complete_univ
- \+ *lemma* cauchy_iff_exists_le_nhds
- \+ *lemma* cauchy_map_iff_exists_tendsto
- \+ *lemma* is_complete_of_is_closed
- \+ *lemma* totally_bounded_subset
- \+ *lemma* totally_bounded_empty
- \+ *lemma* totally_bounded_closure
- \+ *lemma* totally_bounded_image
- \+ *lemma* cauchy_of_totally_bounded_of_ultrafilter
- \+ *lemma* totally_bounded_iff_filter
- \+ *lemma* totally_bounded_iff_ultrafilter
- \+ *lemma* compact_iff_totally_bounded_complete
- \+ *lemma* compact_of_totally_bounded_is_closed
- \+ *theorem* cauchy_seq_tendsto_of_complete
- \+ *theorem* le_nhds_lim_of_cauchy
- \+ *theorem* totally_bounded_iff_subset
- \+ *def* cauchy
- \+ *def* is_complete
- \+ *def* cauchy_seq
- \+ *def* totally_bounded

Created src/topology/uniform_space/complete_separated.lean
- \+ *lemma* is_closed_of_is_complete

Modified src/topology/uniform_space/completion.lean
- \- *lemma* uniformity_quotient
- \- *lemma* uniform_continuous_quotient_mk
- \- *lemma* uniform_continuous_quotient
- \- *lemma* uniform_continuous_quotient_lift
- \- *lemma* uniform_continuous_quotient_lift₂
- \- *lemma* comap_quotient_le_uniformity
- \- *lemma* comap_quotient_eq_uniformity
- \- *lemma* separated_of_uniform_continuous
- \- *lemma* eq_of_separated_of_uniform_continuous
- \- *lemma* lift_mk
- \- *lemma* uniform_continuous_lift
- \- *lemma* map_mk
- \- *lemma* uniform_continuous_map
- \- *lemma* map_unique
- \- *lemma* map_id
- \- *lemma* map_comp
- \- *lemma* separation_prod
- \- *lemma* coe_zero
- \- *lemma* coe_neg
- \- *lemma* coe_add
- \- *lemma* is_add_group_hom_extension
- \- *lemma* is_add_group_hom_map
- \- *lemma* is_add_group_hom_prod
- \- *lemma* is_Z_bilin.zero_left
- \- *lemma* is_Z_bilin.zero_right
- \- *lemma* is_Z_bilin.zero
- \- *lemma* is_Z_bilin.neg_left
- \- *lemma* is_Z_bilin.neg_right
- \- *lemma* is_Z_bilin.sub_left
- \- *lemma* is_Z_bilin.sub_right
- \- *lemma* is_Z_bilin.tendsto_zero_left
- \- *lemma* is_Z_bilin.tendsto_zero_right
- \- *lemma* tendsto_sub_comap_self
- \- *lemma* coe_one
- \- *lemma* continuous_mul'
- \- *lemma* coe_mul
- \- *lemma* continuous_mul
- \- *theorem* extend_Z_bilin
- \- *def* separation_setoid
- \- *def* separation_quotient
- \- *def* lift
- \- *def* map

Created src/topology/uniform_space/separation.lean
- \+ *lemma* separated_equiv
- \+ *lemma* uniformity_quotient
- \+ *lemma* uniform_continuous_quotient_mk
- \+ *lemma* uniform_continuous_quotient
- \+ *lemma* uniform_continuous_quotient_lift
- \+ *lemma* uniform_continuous_quotient_lift₂
- \+ *lemma* comap_quotient_le_uniformity
- \+ *lemma* comap_quotient_eq_uniformity
- \+ *lemma* separated_of_uniform_continuous
- \+ *lemma* eq_of_separated_of_uniform_continuous
- \+ *lemma* lift_mk
- \+ *lemma* uniform_continuous_lift
- \+ *lemma* map_mk
- \+ *lemma* uniform_continuous_map
- \+ *lemma* map_unique
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* separation_prod
- \+ *theorem* separated_def
- \+ *theorem* separated_def'
- \+ *def* separated
- \+ *def* separation_setoid
- \+ *def* separation_quotient
- \+ *def* lift
- \+ *def* map

Created src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* uniform_embedding.uniform_continuous
- \+ *lemma* uniform_embedding.uniform_continuous_iff
- \+ *lemma* uniform_embedding.embedding
- \+ *lemma* uniform_embedding.dense_embedding
- \+ *lemma* closure_image_mem_nhds_of_uniform_embedding
- \+ *lemma* uniform_embedding_comap
- \+ *lemma* uniform_embedding_subtype_emb
- \+ *lemma* uniform_embedding.prod
- \+ *lemma* is_complete_image_iff
- \+ *lemma* complete_space_extension
- \+ *lemma* totally_bounded_preimage
- \+ *lemma* uniformly_extend_of_emb
- \+ *lemma* uniformly_extend_exists
- \+ *lemma* uniformly_extend_spec
- \+ *lemma* uniform_continuous_uniformly_extend
- \+ *lemma* uniform_extend_subtype
- \+ *theorem* uniform_embedding_def
- \+ *theorem* uniform_embedding_def'
- \+ *def* uniform_embedding



## [2019-03-05 09:50:45+01:00](https://github.com/leanprover-community/mathlib/commit/708c0cf)
feat(data/multiset): add monad instance ([#744](https://github.com/leanprover-community/mathlib/pull/744))
#### Estimated changes
Modified src/data/multiset.lean




## [2019-03-05 09:44:51+01:00](https://github.com/leanprover-community/mathlib/commit/3525d21)
refactor(topology/metric_space/lipschitz): Simplify proof in banach contraction ([#788](https://github.com/leanprover-community/mathlib/pull/788))
#### Estimated changes
Modified src/topology/metric_space/lipschitz.lean
- \- *lemma* dist_bound_of_contraction



## [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/b9f88d1)
feat(data/finset): add card_sdiff
#### Estimated changes
Modified src/data/finset.lean
- \+/\- *theorem* card_disjoint_union
- \+ *theorem* card_sdiff

Modified src/data/fintype.lean




## [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/682f4b5)
feat(linear_algebra): module (vector space) structure for finsupp, matrix, and mv polynomials
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* ext_iff
- \+ *lemma* injective_single
- \+ *lemma* single_eq_single_iff
- \+ *lemma* map_range_multiset_sum
- \+ *lemma* map_range_finset_sum
- \+ *lemma* map_domain_apply
- \+ *lemma* map_domain_notin_range
- \+ *lemma* filter_zero
- \+ *lemma* filter_sum
- \+ *lemma* filter_curry
- \+ *lemma* support_curry
- \+ *def* equiv_fun_on_fintype
- \+ *def* restrict_support_equiv

Modified src/data/multivariate_polynomial.lean
- \+ *lemma* smul_eq_C_mul
- \+ *lemma* smul_eval

Modified src/field_theory/finite.lean
- \+/\- *lemma* card_nth_roots_subgroup_units
- \+/\- *lemma* card_units
- \+/\- *lemma* prod_univ_units_id_eq_neg_one
- \+ *lemma* pow_card_sub_one_eq_one
- \+/\- *def* field_of_integral_domain

Created src/field_theory/mv_polynomial.lean
- \+ *lemma* eval_indicator_apply_eq_one
- \+ *lemma* eval_indicator_apply_eq_zero
- \+ *lemma* degrees_indicator
- \+ *lemma* indicator_mem_restrict_degree
- \+ *lemma* evalₗ_apply
- \+ *lemma* map_restrict_dom_evalₗ
- \+ *lemma* dim_R
- \+ *lemma* range_evalᵢ
- \+ *lemma* ker_evalₗ
- \+ *lemma* eq_zero_of_eval_eq_zero
- \+ *def* indicator
- \+ *def* evalₗ
- \+ *def* R
- \+ *def* evalᵢ

Created src/linear_algebra/finsupp.lean
- \+ *lemma* lmap_domain_apply
- \+ *lemma* lsubtype_domain_apply
- \+ *lemma* lsingle_apply
- \+ *lemma* lapply_apply
- \+ *lemma* ker_lsingle
- \+ *lemma* lsingle_range_le_ker_lapply
- \+ *lemma* infi_ker_lapply_le_bot
- \+ *lemma* supr_lsingle_range
- \+ *lemma* disjoint_lsingle_lsingle
- \+ *lemma* span_single_image
- \+ *lemma* linear_independent_single
- \+ *lemma* mem_restrict_dom
- \+ *lemma* is_basis_single
- \+ *lemma* dim_eq
- \+ *lemma* equiv_of_dim_eq_dim
- \+ *lemma* eq_bot_iff_dim_eq_zero
- \+ *lemma* injective_of_surjective
- \+ *lemma* cardinal_mk_eq_cardinal_mk_field_pow_dim
- \+ *lemma* cardinal_lt_omega_of_dim_lt_omega
- \+ *lemma* mem_restrict_total_degree
- \+ *lemma* mem_restrict_degree
- \+ *lemma* mem_restrict_degree_iff_sup
- \+ *lemma* map_range_eq_map
- \+ *lemma* is_basis_monomials
- \+ *lemma* dim_mv_polynomial
- \+ *def* lsingle
- \+ *def* lapply
- \+ *def* lmap_domain
- \+ *def* lsubtype_domain
- \+ *def* restrict_dom
- \+ *def* restrict_dom_equiv_finsupp
- \+ *def* restrict_total_degree
- \+ *def* restrict_degree

Created src/linear_algebra/matrix.lean
- \+ *lemma* to_lin_add
- \+ *lemma* to_lin_zero
- \+ *lemma* to_lin_apply
- \+ *lemma* mul_to_lin
- \+ *lemma* proj_diagonal
- \+ *lemma* diagonal_comp_std_basis
- \+ *lemma* rank_vec_mul_vec
- \+ *lemma* diagonal_to_lin
- \+ *lemma* ker_diagonal_to_lin
- \+ *lemma* range_diagonal
- \+ *lemma* rank_diagonal
- \+ *def* eval
- \+ *def* to_lin



## [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/738778a)
feat(data/matrix): basic definitions: transpose; row & column matrix; vector/matrix multiplication
#### Estimated changes
Modified src/data/matrix.lean
- \+ *lemma* mul_vec_diagonal
- \+ *lemma* vec_mul_vec_eq
- \+ *def* transpose
- \+ *def* row
- \+ *def* col
- \+ *def* vec_mul_vec
- \+ *def* mul_vec
- \+ *def* vec_mul



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
- \+ *lemma* comp_cod_restrict
- \+ *lemma* subtype_comp_cod_restrict
- \+ *lemma* eq_zero_of_bot_submodule
- \+ *lemma* span_univ
- \+ *lemma* mem_supr_of_mem
- \+ *lemma* disjoint_iff_comap_eq_bot
- \+ *lemma* eq_bot_of_equiv
- \+ *lemma* pi_apply
- \+ *lemma* ker_pi
- \+ *lemma* pi_eq_zero
- \+ *lemma* pi_zero
- \+ *lemma* pi_comp
- \+ *lemma* proj_apply
- \+ *lemma* proj_pi
- \+ *lemma* infi_ker_proj
- \+ *lemma* update_apply
- \+ *lemma* std_basis_apply
- \+ *lemma* std_basis_same
- \+ *lemma* std_basis_ne
- \+ *lemma* ker_std_basis
- \+ *lemma* proj_comp_std_basis
- \+ *lemma* proj_std_basis_same
- \+ *lemma* proj_std_basis_ne
- \+ *lemma* supr_range_std_basis_le_infi_ker_proj
- \+ *lemma* infi_ker_proj_le_supr_range_std_basis
- \+ *lemma* supr_range_std_basis_eq_infi_ker_proj
- \+ *lemma* supr_range_std_basis
- \+ *lemma* disjoint_std_basis_std_basis
- \+ *def* smul_of_unit
- \+ *def* smul_of_ne_zero
- \+ *def* to_linear_equiv
- \+ *def* pi
- \+ *def* proj
- \+ *def* infi_ker_proj_equiv
- \+ *def* diag
- \+ *def* std_basis

Modified src/linear_algebra/basis.lean
- \+ *lemma* linear_independent_Union_finite
- \+ *lemma* linear_independent_std_basis
- \+ *lemma* is_basis_std_basis
- \+ *lemma* is_basis_fun

Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_pi
- \+ *lemma* dim_fun
- \+ *lemma* dim_fun'



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
- \+ *lemma* sdiff_disjoint
- \+/\- *lemma* disjoint_sdiff

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
- \+ *lemma* prod_filter

Modified src/data/finset.lean
- \+ *lemma* filter_empty
- \+ *lemma* filter_subset_filter



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/b9ead4d)
feat(data/finset): add disjoint_bind_left/right
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* disjoint_bind_left
- \+ *lemma* disjoint_bind_right



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
- \+ *def* subtype_pi_equiv_pi



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/8070c05)
feat(data/set/lattice): more rules for disjoint sets
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *theorem* disjoint_diff
- \+ *theorem* disjoint_compl
- \+ *theorem* disjoint_singleton_left
- \+ *theorem* disjoint_singleton_right
- \+ *theorem* disjoint_image_image
- \- *theorem* set.disjoint_diff



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c53ac41)
feat(data/set): relate range and image to Union
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* range_eq_Union
- \+ *lemma* image_eq_Union



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/41038ba)
feat(data/set): add exists_maximal_wrt
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* finite.exists_maximal_wrt



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/146d73c)
feat(data/set): add finite_image_iff_on
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *theorem* finite_of_finite_image_on
- \+ *theorem* finite_image_iff_on
- \+/\- *theorem* finite_of_finite_image



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/84a5f4d)
feat(data/set): add subset_image_iff and subset_range_iff
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* subset_image_iff
- \+ *lemma* subset_range_iff



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/cbe2f61)
feat(logic/function): add inv_fun_neg
#### Estimated changes
Modified src/logic/function.lean
- \+ *lemma* inv_fun_neg



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/73db4c7)
feat(logic/function): add injective.ne
#### Estimated changes
Modified src/logic/function.lean
- \+ *lemma* injective.ne



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c819617)
feat(logic): add plift.down_inj
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* plift.down_inj



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/985445f)
feat(linear_algebra/multivariate_polynomial): relate total_degree to degrees, add, zero, mul
#### Estimated changes
Modified src/linear_algebra/multivariate_polynomial.lean
- \+ *lemma* total_degree_eq
- \+ *lemma* total_degree_le_degrees_card
- \+ *lemma* total_degree_C
- \+ *lemma* total_degree_zero
- \+ *lemma* total_degree_one
- \+ *lemma* total_degree_add
- \+ *lemma* total_degree_mul
- \+ *lemma* total_degree_list_prod
- \+ *lemma* total_degree_multiset_prod
- \+ *lemma* total_degree_finset_prod



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/78fd58d)
feat(linear_algebra/multivariate_polynomial): add degrees
#### Estimated changes
Modified src/linear_algebra/multivariate_polynomial.lean
- \+ *lemma* degrees_monomial
- \+ *lemma* degrees_monomial_eq
- \+ *lemma* degrees_C
- \+ *lemma* degrees_X
- \+ *lemma* degrees_zero
- \+ *lemma* degrees_one
- \+ *lemma* degrees_add
- \+ *lemma* degrees_sum
- \+ *lemma* degrees_mul
- \+ *lemma* degrees_prod
- \+ *lemma* degrees_pow
- \+ *lemma* degrees_neg
- \+ *lemma* degrees_sub
- \+ *def* degrees
- \+/\- *def* vars
- \+/\- *def* degree_of



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c2d8bc2)
feat(data/finsupp): relatie to_multiset to 0, +, single, card, map, prod, and to_finset
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* to_multiset_zero
- \+ *lemma* to_multiset_add
- \+ *lemma* to_multiset_single
- \+ *lemma* card_to_multiset
- \+ *lemma* to_multiset_map
- \+ *lemma* prod_to_multiset
- \+ *lemma* to_finset_to_multiset



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/857842d)
feat(data/finsupp): add support_mul
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* support_mul



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/a77797f)
feat(data/multiset): add prod_smul
#### Estimated changes
Modified src/data/multiset.lean
- \+ *lemma* prod_smul



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/e924745)
feat(data/finset): add multiset.count_sup
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* count_sup



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/e07cac5)
feat(data/finset): add to_finset_smul
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* to_finset_smul



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/f24b01b)
feat(algebra/group_power): smul and pow are monoid homs
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *theorem* map_pow
- \+ *theorem* map_smul



## [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/32642e1)
feat(linear_algebra): add dim_sup_add_dim_inf_eq
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* subtype_comp_of_le
- \+ *lemma* range_of_le

Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_add_dim_split
- \+ *lemma* dim_sup_add_dim_inf_eq



## [2019-03-04 16:26:09+01:00](https://github.com/leanprover-community/mathlib/commit/f46f0a6)
feat(tactic/fin_cases): case bashing on finset, list, and fintype hypotheses. ([#775](https://github.com/leanprover-community/mathlib/pull/775))
#### Estimated changes
Modified docs/tactics.md


Modified src/data/int/basic.lean
- \+ *theorem* add_def
- \+ *theorem* mul_def

Modified src/data/nat/basic.lean
- \+ *theorem* add_def
- \+ *theorem* mul_def

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


Created src/topology/bases.lean
- \+ *lemma* is_topological_basis_of_subbasis
- \+ *lemma* is_topological_basis_of_open_of_nhds
- \+ *lemma* mem_nhds_of_is_topological_basis
- \+ *lemma* is_open_of_is_topological_basis
- \+ *lemma* mem_basis_subset_of_mem_open
- \+ *lemma* sUnion_basis_of_is_open
- \+ *lemma* Union_basis_of_is_open
- \+ *lemma* second_countable_topology_induced
- \+ *lemma* is_open_generated_countable_inter
- \+ *lemma* is_open_Union_countable
- \+ *lemma* is_open_sUnion_countable
- \+ *def* is_topological_basis

Modified src/topology/basic.lean
- \+/\- *lemma* lim_spec
- \+ *lemma* continuous_id
- \+ *lemma* continuous.comp
- \+ *lemma* continuous.tendsto
- \+ *lemma* continuous_iff_continuous_at
- \+ *lemma* continuous_const
- \+ *lemma* continuous_iff_is_closed
- \+ *lemma* continuous_at_iff_ultrafilter
- \+ *lemma* continuous_iff_ultrafilter
- \+ *lemma* continuous_if
- \+ *lemma* open_dom_of_pcontinuous
- \+ *lemma* pcontinuous_iff'
- \+ *lemma* image_closure_subset_closure_image
- \+ *lemma* mem_closure
- \- *lemma* compact_inter
- \- *lemma* compact_diff
- \- *lemma* compact_of_is_closed_subset
- \- *lemma* compact_adherence_nhdset
- \- *lemma* compact_iff_ultrafilter_le_nhds
- \- *lemma* compact_elim_finite_subcover
- \- *lemma* compact_elim_finite_subcover_image
- \- *lemma* compact_of_finite_subcover
- \- *lemma* compact_iff_finite_subcover
- \- *lemma* compact_empty
- \- *lemma* compact_singleton
- \- *lemma* compact_bUnion_of_compact
- \- *lemma* compact_Union_of_compact
- \- *lemma* compact_of_finite
- \- *lemma* compact_union_of_compact
- \- *lemma* compact_univ
- \- *lemma* compact_of_closed
- \- *lemma* is_closed_singleton
- \- *lemma* compl_singleton_mem_nhds
- \- *lemma* closure_singleton
- \- *lemma* t2_separation
- \- *lemma* eq_of_nhds_neq_bot
- \- *lemma* t2_iff_nhds
- \- *lemma* t2_iff_ultrafilter
- \- *lemma* nhds_eq_nhds_iff
- \- *lemma* nhds_le_nhds_iff
- \- *lemma* tendsto_nhds_unique
- \- *lemma* nhds_is_closed
- \- *lemma* nhds_generate_from
- \- *lemma* tendsto_nhds_generate_from
- \- *lemma* nhds_mk_of_nhds
- \- *lemma* generate_from_le_iff_subset_is_open
- \- *lemma* mk_of_closure_sets
- \- *lemma* generate_from_mono
- \- *lemma* is_open_discrete
- \- *lemma* nhds_top
- \- *lemma* nhds_discrete
- \- *lemma* le_of_nhds_le_nhds
- \- *lemma* eq_of_nhds_eq_nhds
- \- *lemma* eq_top_of_singletons_open
- \- *lemma* is_open_induced_iff
- \- *lemma* is_closed_induced_iff
- \- *lemma* is_open_coinduced
- \- *lemma* induced_le_iff_le_coinduced
- \- *lemma* gc_induced_coinduced
- \- *lemma* induced_mono
- \- *lemma* coinduced_mono
- \- *lemma* induced_bot
- \- *lemma* induced_sup
- \- *lemma* induced_supr
- \- *lemma* coinduced_top
- \- *lemma* coinduced_inf
- \- *lemma* coinduced_infi
- \- *lemma* induced_id
- \- *lemma* induced_compose
- \- *lemma* coinduced_id
- \- *lemma* coinduced_compose
- \- *lemma* nhds_list
- \- *lemma* nhds_nil
- \- *lemma* nhds_cons
- \- *lemma* quotient_dense_of_dense
- \- *lemma* generate_from_le
- \- *lemma* induced_generate_from_eq
- \- *lemma* gc_nhds
- \- *lemma* nhds_mono
- \- *lemma* nhds_supr
- \- *lemma* nhds_Sup
- \- *lemma* nhds_sup
- \- *lemma* nhds_bot
- \- *lemma* is_topological_basis_of_subbasis
- \- *lemma* is_topological_basis_of_open_of_nhds
- \- *lemma* mem_nhds_of_is_topological_basis
- \- *lemma* is_open_of_is_topological_basis
- \- *lemma* mem_basis_subset_of_mem_open
- \- *lemma* sUnion_basis_of_is_open
- \- *lemma* Union_basis_of_is_open
- \- *lemma* second_countable_topology_induced
- \- *lemma* is_open_generated_countable_inter
- \- *lemma* is_open_Union_countable
- \- *lemma* is_open_sUnion_countable
- \- *lemma* ext
- \- *lemma* gi_choice_val
- \- *lemma* inter_eq
- \- *lemma* union_eq
- \- *lemma* empty_eq
- \- *lemma* Sup_s
- \- *lemma* is_basis_iff_nbhd
- \- *lemma* is_basis_iff_cover
- \- *lemma* lim_eq
- \- *lemma* lim_nhds_eq
- \- *lemma* lim_nhds_eq_of_closure
- \- *theorem* is_clopen_union
- \- *theorem* is_clopen_inter
- \- *theorem* is_clopen_empty
- \- *theorem* is_clopen_univ
- \- *theorem* is_clopen_compl
- \- *theorem* is_clopen_compl_iff
- \- *theorem* is_clopen_diff
- \- *theorem* is_irreducible_empty
- \- *theorem* is_irreducible_singleton
- \- *theorem* is_irreducible_closure
- \- *theorem* exists_irreducible
- \- *theorem* is_irreducible_irreducible_component
- \- *theorem* mem_irreducible_component
- \- *theorem* eq_irreducible_component
- \- *theorem* is_closed_irreducible_component
- \- *theorem* irreducible_exists_mem_inter
- \- *theorem* is_connected_of_is_irreducible
- \- *theorem* is_connected_empty
- \- *theorem* is_connected_singleton
- \- *theorem* is_connected_sUnion
- \- *theorem* is_connected_union
- \- *theorem* is_connected_closure
- \- *theorem* is_connected_connected_component
- \- *theorem* mem_connected_component
- \- *theorem* subset_connected_component
- \- *theorem* is_closed_connected_component
- \- *theorem* irreducible_component_subset_connected_component
- \- *theorem* exists_mem_inter
- \- *theorem* is_clopen_iff
- \- *theorem* is_totally_disconnected_empty
- \- *theorem* is_totally_disconnected_singleton
- \- *theorem* is_totally_separated_empty
- \- *theorem* is_totally_separated_singleton
- \- *theorem* is_totally_disconnected_of_is_totally_separated
- \- *theorem* exists_open_singleton_of_fintype
- \- *theorem* normal_separation
- \- *theorem* mem_nhds_induced
- \- *theorem* nhds_induced
- \- *theorem* map_nhds_induced_of_surjective
- \- *theorem* mem_nhds_subtype
- \- *theorem* nhds_subtype
- \- *theorem* principal_subtype
- \- *theorem* mem_nhds_within_subtype
- \- *theorem* nhds_within_subtype
- \- *theorem* nhds_within_eq_map_subtype_val
- \- *theorem* tendsto_nhds_within_iff_subtype
- \+ *def* continuous
- \+ *def* continuous_at
- \+ *def* continuous_at_within
- \+ *def* continuous_on
- \+ *def* pcontinuous
- \- *def* compact
- \- *def* is_clopen
- \- *def* is_irreducible
- \- *def* irreducible_component
- \- *def* is_connected
- \- *def* connected_component
- \- *def* is_totally_disconnected
- \- *def* is_totally_separated
- \- *def* generate_from
- \- *def* gi_generate_from
- \- *def* topological_space.induced
- \- *def* topological_space.coinduced
- \- *def* is_topological_basis
- \- *def* opens
- \- *def* closeds
- \- *def* nonempty_compacts
- \- *def* interior
- \- *def* gc
- \- *def* gi
- \- *def* is_basis

Modified src/topology/compact_open.lean


Renamed src/topology/continuity.lean to src/topology/constructions.lean
- \+/\- *lemma* compact_iff_compact_image_of_embedding
- \- *lemma* continuous_id
- \- *lemma* continuous.comp
- \- *lemma* continuous.tendsto
- \- *lemma* continuous_iff_continuous_at
- \- *lemma* continuous_const
- \- *lemma* continuous_of_discrete_topology
- \- *lemma* continuous_iff_is_closed
- \- *lemma* continuous_at_iff_ultrafilter
- \- *lemma* continuous_iff_ultrafilter
- \- *lemma* continuous_if
- \- *lemma* open_dom_of_pcontinuous
- \- *lemma* pcontinuous_iff'
- \- *lemma* image_closure_subset_closure_image
- \- *lemma* mem_closure
- \- *lemma* compact_image
- \- *lemma* compact_range
- \- *lemma* continuous_iff_le_coinduced
- \- *lemma* continuous_iff_induced_le
- \- *lemma* continuous_induced_dom
- \- *lemma* continuous_induced_rng
- \- *lemma* continuous_coinduced_rng
- \- *lemma* continuous_coinduced_dom
- \- *lemma* continuous_le_dom
- \- *lemma* continuous_le_rng
- \- *lemma* continuous_inf_dom
- \- *lemma* continuous_inf_rng_left
- \- *lemma* continuous_inf_rng_right
- \- *lemma* continuous_Inf_dom
- \- *lemma* continuous_Inf_rng
- \- *lemma* continuous_infi_dom
- \- *lemma* continuous_infi_rng
- \- *lemma* continuous_sup_rng
- \- *lemma* continuous_sup_dom_left
- \- *lemma* continuous_sup_dom_right
- \- *lemma* continuous_Sup_dom
- \- *lemma* continuous_Sup_rng
- \- *lemma* continuous_supr_dom
- \- *lemma* continuous_supr_rng
- \- *lemma* continuous_top
- \- *lemma* continuous_bot
- \- *lemma* nhds_induced_eq_comap
- \- *lemma* map_nhds_induced_eq
- \- *lemma* closure_induced
- \- *lemma* embedding_id
- \- *lemma* embedding_compose
- \- *lemma* embedding_prod_mk
- \- *lemma* embedding_of_embedding_compose
- \- *lemma* embedding_open
- \- *lemma* embedding_is_closed
- \- *lemma* embedding.map_nhds_eq
- \- *lemma* embedding.tendsto_nhds_iff
- \- *lemma* embedding.continuous_iff
- \- *lemma* embedding.continuous
- \- *lemma* embedding.closure_eq_preimage_closure_image
- \- *lemma* is_open_map_iff_nhds_le
- \- *lemma* of_inverse
- \- *lemma* to_quotient_map
- \- *lemma* is_open_singleton_true
- \- *lemma* continuous_Prop
- \- *lemma* inj_iff
- \- *lemma* closure_range
- \- *lemma* self_sub_closure_image_preimage_of_open
- \- *lemma* closure_image_nhds_of_nhds
- \- *lemma* tendsto_comap_nhds_nhds
- \- *lemma* comap_nhds_neq_bot
- \- *lemma* extend_e_eq
- \- *lemma* extend_eq
- \- *lemma* tendsto_extend
- \- *lemma* continuous_extend
- \- *theorem* continuous_at_within_univ
- \- *theorem* continuous_at_within_iff_continuous_at_restrict
- \- *theorem* continuous_at_within.tendsto_nhds_within_image
- \- *theorem* continuous_on_iff
- \- *theorem* continuous_on_iff_continuous_restrict
- \- *theorem* continuous_on_iff'
- \- *theorem* nhds_within_le_comap
- \- *theorem* continuous_at_within_iff_ptendsto_res
- \- *theorem* continuous_generated_from
- \- *theorem* is_open_induced_eq
- \- *theorem* is_open_induced
- \- *theorem* dense_embedding.mk'
- \- *def* continuous
- \- *def* continuous_at
- \- *def* continuous_at_within
- \- *def* continuous_on
- \- *def* pcontinuous
- \- *def* embedding
- \- *def* quotient_map
- \- *def* is_open_map
- \- *def* nonempty_compacts.to_closeds
- \- *def* extend

Created src/topology/maps.lean
- \+ *lemma* embedding_id
- \+ *lemma* embedding_compose
- \+ *lemma* embedding_prod_mk
- \+ *lemma* embedding_of_embedding_compose
- \+ *lemma* embedding_open
- \+ *lemma* embedding_is_closed
- \+ *lemma* embedding.map_nhds_eq
- \+ *lemma* embedding.tendsto_nhds_iff
- \+ *lemma* embedding.continuous_iff
- \+ *lemma* embedding.continuous
- \+ *lemma* embedding.closure_eq_preimage_closure_image
- \+ *lemma* inj_iff
- \+ *lemma* closure_range
- \+ *lemma* self_sub_closure_image_preimage_of_open
- \+ *lemma* closure_image_nhds_of_nhds
- \+ *lemma* tendsto_comap_nhds_nhds
- \+ *lemma* comap_nhds_neq_bot
- \+ *lemma* extend_e_eq
- \+ *lemma* extend_eq
- \+ *lemma* tendsto_extend
- \+ *lemma* continuous_extend
- \+ *lemma* is_open_map_iff_nhds_le
- \+ *lemma* of_inverse
- \+ *lemma* to_quotient_map
- \+ *lemma* is_open_singleton_true
- \+ *lemma* continuous_Prop
- \+ *theorem* dense_embedding.mk'
- \+ *def* embedding
- \+ *def* extend
- \+ *def* quotient_map
- \+ *def* is_open_map

Modified src/topology/metric_space/closeds.lean


Created src/topology/opens.lean
- \+ *lemma* ext
- \+ *lemma* gi_choice_val
- \+ *lemma* inter_eq
- \+ *lemma* union_eq
- \+ *lemma* empty_eq
- \+ *lemma* Sup_s
- \+ *lemma* is_basis_iff_nbhd
- \+ *lemma* is_basis_iff_cover
- \+ *def* opens
- \+ *def* closeds
- \+ *def* nonempty_compacts
- \+ *def* nonempty_compacts.to_closeds
- \+ *def* interior
- \+ *def* gc
- \+ *def* gi
- \+ *def* is_basis

Created src/topology/order.lean
- \+ *lemma* nhds_generate_from
- \+ *lemma* tendsto_nhds_generate_from
- \+ *lemma* nhds_mk_of_nhds
- \+ *lemma* generate_from_le_iff_subset_is_open
- \+ *lemma* mk_of_closure_sets
- \+ *lemma* generate_from_mono
- \+ *lemma* is_open_discrete
- \+ *lemma* continuous_of_discrete_topology
- \+ *lemma* nhds_top
- \+ *lemma* nhds_discrete
- \+ *lemma* le_of_nhds_le_nhds
- \+ *lemma* eq_of_nhds_eq_nhds
- \+ *lemma* eq_top_of_singletons_open
- \+ *lemma* is_open_induced_iff
- \+ *lemma* is_closed_induced_iff
- \+ *lemma* is_open_coinduced
- \+ *lemma* induced_le_iff_le_coinduced
- \+ *lemma* gc_induced_coinduced
- \+ *lemma* induced_mono
- \+ *lemma* coinduced_mono
- \+ *lemma* induced_bot
- \+ *lemma* induced_sup
- \+ *lemma* induced_supr
- \+ *lemma* coinduced_top
- \+ *lemma* coinduced_inf
- \+ *lemma* coinduced_infi
- \+ *lemma* induced_id
- \+ *lemma* induced_compose
- \+ *lemma* coinduced_id
- \+ *lemma* coinduced_compose
- \+ *lemma* nhds_list
- \+ *lemma* nhds_nil
- \+ *lemma* nhds_cons
- \+ *lemma* quotient_dense_of_dense
- \+ *lemma* generate_from_le
- \+ *lemma* induced_generate_from_eq
- \+ *lemma* gc_nhds
- \+ *lemma* nhds_mono
- \+ *lemma* nhds_supr
- \+ *lemma* nhds_Sup
- \+ *lemma* nhds_sup
- \+ *lemma* nhds_bot
- \+ *lemma* continuous_iff_le_coinduced
- \+ *lemma* continuous_iff_induced_le
- \+ *lemma* continuous_induced_dom
- \+ *lemma* continuous_induced_rng
- \+ *lemma* continuous_coinduced_rng
- \+ *lemma* continuous_coinduced_dom
- \+ *lemma* continuous_le_dom
- \+ *lemma* continuous_le_rng
- \+ *lemma* continuous_inf_dom
- \+ *lemma* continuous_inf_rng_left
- \+ *lemma* continuous_inf_rng_right
- \+ *lemma* continuous_Inf_dom
- \+ *lemma* continuous_Inf_rng
- \+ *lemma* continuous_infi_dom
- \+ *lemma* continuous_infi_rng
- \+ *lemma* continuous_sup_rng
- \+ *lemma* continuous_sup_dom_left
- \+ *lemma* continuous_sup_dom_right
- \+ *lemma* continuous_Sup_dom
- \+ *lemma* continuous_Sup_rng
- \+ *lemma* continuous_supr_dom
- \+ *lemma* continuous_supr_rng
- \+ *lemma* continuous_top
- \+ *lemma* continuous_bot
- \+ *lemma* nhds_induced_eq_comap
- \+ *lemma* map_nhds_induced_eq
- \+ *lemma* closure_induced
- \+ *theorem* continuous_generated_from
- \+ *theorem* mem_nhds_induced
- \+ *theorem* nhds_induced
- \+ *theorem* map_nhds_induced_of_surjective
- \+ *theorem* mem_nhds_subtype
- \+ *theorem* nhds_subtype
- \+ *theorem* principal_subtype
- \+ *theorem* mem_nhds_within_subtype
- \+ *theorem* nhds_within_subtype
- \+ *theorem* nhds_within_eq_map_subtype_val
- \+ *theorem* tendsto_nhds_within_iff_subtype
- \+ *theorem* continuous_at_within_univ
- \+ *theorem* continuous_at_within_iff_continuous_at_restrict
- \+ *theorem* continuous_at_within.tendsto_nhds_within_image
- \+ *theorem* continuous_on_iff
- \+ *theorem* continuous_on_iff_continuous_restrict
- \+ *theorem* continuous_on_iff'
- \+ *theorem* nhds_within_le_comap
- \+ *theorem* continuous_at_within_iff_ptendsto_res
- \+ *theorem* is_open_induced_eq
- \+ *theorem* is_open_induced
- \+ *def* generate_from
- \+ *def* gi_generate_from
- \+ *def* topological_space.induced
- \+ *def* topological_space.coinduced

Created src/topology/separation.lean
- \+ *lemma* is_closed_singleton
- \+ *lemma* compl_singleton_mem_nhds
- \+ *lemma* closure_singleton
- \+ *lemma* t2_separation
- \+ *lemma* eq_of_nhds_neq_bot
- \+ *lemma* t2_iff_nhds
- \+ *lemma* t2_iff_ultrafilter
- \+ *lemma* nhds_eq_nhds_iff
- \+ *lemma* nhds_le_nhds_iff
- \+ *lemma* tendsto_nhds_unique
- \+ *lemma* lim_eq
- \+ *lemma* lim_nhds_eq
- \+ *lemma* lim_nhds_eq_of_closure
- \+ *lemma* nhds_is_closed
- \+ *theorem* exists_open_singleton_of_fintype
- \+ *theorem* normal_separation

Modified src/topology/sequences.lean


Modified src/topology/stone_cech.lean


Created src/topology/subset_properties.lean
- \+ *lemma* compact_inter
- \+ *lemma* compact_diff
- \+ *lemma* compact_of_is_closed_subset
- \+ *lemma* compact_adherence_nhdset
- \+ *lemma* compact_iff_ultrafilter_le_nhds
- \+ *lemma* compact_elim_finite_subcover
- \+ *lemma* compact_elim_finite_subcover_image
- \+ *lemma* compact_of_finite_subcover
- \+ *lemma* compact_iff_finite_subcover
- \+ *lemma* compact_empty
- \+ *lemma* compact_singleton
- \+ *lemma* compact_bUnion_of_compact
- \+ *lemma* compact_Union_of_compact
- \+ *lemma* compact_of_finite
- \+ *lemma* compact_union_of_compact
- \+ *lemma* compact_univ
- \+ *lemma* compact_of_closed
- \+ *lemma* compact_image
- \+ *lemma* compact_range
- \+ *theorem* is_clopen_union
- \+ *theorem* is_clopen_inter
- \+ *theorem* is_clopen_empty
- \+ *theorem* is_clopen_univ
- \+ *theorem* is_clopen_compl
- \+ *theorem* is_clopen_compl_iff
- \+ *theorem* is_clopen_diff
- \+ *theorem* is_irreducible_empty
- \+ *theorem* is_irreducible_singleton
- \+ *theorem* is_irreducible_closure
- \+ *theorem* exists_irreducible
- \+ *theorem* is_irreducible_irreducible_component
- \+ *theorem* mem_irreducible_component
- \+ *theorem* eq_irreducible_component
- \+ *theorem* is_closed_irreducible_component
- \+ *theorem* irreducible_exists_mem_inter
- \+ *theorem* is_connected_of_is_irreducible
- \+ *theorem* is_connected_empty
- \+ *theorem* is_connected_singleton
- \+ *theorem* is_connected_sUnion
- \+ *theorem* is_connected_union
- \+ *theorem* is_connected_closure
- \+ *theorem* is_connected_connected_component
- \+ *theorem* mem_connected_component
- \+ *theorem* subset_connected_component
- \+ *theorem* is_closed_connected_component
- \+ *theorem* irreducible_component_subset_connected_component
- \+ *theorem* exists_mem_inter
- \+ *theorem* is_clopen_iff
- \+ *theorem* is_totally_disconnected_empty
- \+ *theorem* is_totally_disconnected_singleton
- \+ *theorem* is_totally_separated_empty
- \+ *theorem* is_totally_separated_singleton
- \+ *theorem* is_totally_disconnected_of_is_totally_separated
- \+ *def* compact
- \+ *def* is_clopen
- \+ *def* is_irreducible
- \+ *def* irreducible_component
- \+ *def* is_connected
- \+ *def* connected_component
- \+ *def* is_totally_disconnected
- \+ *def* is_totally_separated

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
- \+ *theorem* exists_sub_one_mem_and_mem
- \+ *theorem* exists_sub_mem
- \+ *theorem* is_ring_hom_quotient_inf_to_pi_quotient
- \+ *theorem* bijective_quotient_inf_to_pi_quotient
- \+ *def* quotient_inf_to_pi_quotient



## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/fb8001d)
hopefully fixed for good this time
#### Estimated changes
Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/182b2a3)
fix properly
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* nat_abs_mul_self'



## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/a4cc8b7)
fix build
#### Estimated changes
Modified src/data/gaussian_int.lean
- \+ *lemma* nat_abs_norm_eq

Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/a75d57c)
fix build
#### Estimated changes
Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/8dcd071)
generalize norm to zsqrtd
#### Estimated changes
Modified src/data/gaussian_int.lean
- \+ *lemma* norm_nonneg
- \+ *lemma* coe_nat_abs_norm
- \+ *lemma* nat_cast_nat_abs_norm
- \+ *lemma* norm_mod_lt
- \+ *lemma* nat_abs_norm_mod_lt
- \- *lemma* norm_mul
- \- *lemma* norm_nat_cast
- \- *lemma* norm_one
- \- *lemma* norm_zero
- \- *lemma* norm_eq_one_iff
- \- *def* norm

Modified src/number_theory/pell.lean
- \+ *lemma* norm_zero
- \+ *lemma* norm_one
- \+ *lemma* norm_int_cast
- \+ *lemma* norm_nat_cast
- \+ *lemma* norm_mul
- \+ *lemma* norm_eq_mul_conj
- \+ *lemma* norm_nonneg
- \+ *lemma* norm_eq_one_iff
- \+ *def* norm

Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/d98cae7)
fix build
#### Estimated changes
Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/5cbd7fa)
changing names
#### Estimated changes
Modified src/data/gaussian_int.lean
- \+ *lemma* to_real_re
- \+ *lemma* to_real_im
- \+ *lemma* to_complex_re
- \+ *lemma* to_complex_im
- \- *lemma* int_cast_re
- \- *lemma* int_cast_im
- \- *lemma* to_complex_re'
- \- *lemma* to_complex_im'

Modified src/data/zmod/quadratic_reciprocity.lean
- \+ *lemma* exists_pow_two_eq_neg_one_iff_mod_four_ne_three
- \+ *lemma* exists_pow_two_eq_prime_iff_of_mod_four_eq_one
- \+ *lemma* exists_pow_two_eq_prime_iff_of_mod_four_eq_three
- \- *lemma* neg_one_is_square_iff_mod_four_ne_three
- \- *lemma* is_square_iff_is_square_of_mod_four_eq_one
- \- *lemma* is_square_iff_is_not_square_of_mod_four_eq_three



## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/a9dfaba)
The year is 2019
#### Estimated changes
Modified src/data/gaussian_int.lean


Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/c36470f)
put sum_two_squares in nat.prime namespace
#### Estimated changes
Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/d8f0921)
move lemmas to correct places
#### Estimated changes
Created src/data/gaussian_int.lean
- \+ *lemma* to_complex_def
- \+ *lemma* to_complex_def'
- \+ *lemma* to_complex_def₂
- \+ *lemma* int_cast_re
- \+ *lemma* int_cast_im
- \+ *lemma* to_complex_re'
- \+ *lemma* to_complex_im'
- \+ *lemma* to_complex_add
- \+ *lemma* to_complex_mul
- \+ *lemma* to_complex_one
- \+ *lemma* to_complex_zero
- \+ *lemma* to_complex_neg
- \+ *lemma* to_complex_sub
- \+ *lemma* to_complex_inj
- \+ *lemma* to_complex_eq_zero
- \+ *lemma* nat_cast_real_norm
- \+ *lemma* nat_cast_complex_norm
- \+ *lemma* norm_mul
- \+ *lemma* norm_eq_zero
- \+ *lemma* norm_pos
- \+ *lemma* norm_nat_cast
- \+ *lemma* norm_one
- \+ *lemma* norm_zero
- \+ *lemma* norm_eq_one_iff
- \+ *lemma* div_def
- \+ *lemma* to_complex_div_re
- \+ *lemma* to_complex_div_im
- \+ *lemma* norm_sq_le_norm_sq_of_re_le_of_im_le
- \+ *lemma* norm_sq_div_sub_div_lt_one
- \+ *lemma* mod_def
- \+ *lemma* norm_le_norm_mul_left
- \+ *def* gaussian_int
- \+ *def* norm
- \+ *def* to_complex

Modified src/number_theory/sum_two_squares.lean
- \- *lemma* to_complex_def
- \- *lemma* to_complex_def'
- \- *lemma* to_complex_def₂
- \- *lemma* int_cast_re
- \- *lemma* int_cast_im
- \- *lemma* to_complex_re'
- \- *lemma* to_complex_im'
- \- *lemma* to_complex_add
- \- *lemma* to_complex_mul
- \- *lemma* to_complex_one
- \- *lemma* to_complex_zero
- \- *lemma* to_complex_neg
- \- *lemma* to_complex_sub
- \- *lemma* to_complex_inj
- \- *lemma* to_complex_eq_zero
- \- *lemma* nat_cast_real_norm
- \- *lemma* nat_cast_complex_norm
- \- *lemma* norm_mul
- \- *lemma* norm_eq_zero
- \- *lemma* norm_pos
- \- *lemma* norm_nat_cast
- \- *lemma* norm_one
- \- *lemma* norm_zero
- \- *lemma* norm_eq_one_iff
- \- *lemma* div_def
- \- *lemma* to_complex_div_re
- \- *lemma* to_complex_div_im
- \- *lemma* norm_sq_le_norm_sq_of_re_le_of_im_le
- \- *lemma* norm_sq_div_sub_div_lt_one
- \- *lemma* mod_def
- \- *lemma* norm_le_norm_mul_left
- \- *def* gaussian_int
- \- *def* norm
- \- *def* to_complex



## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/4e48324)
fix build
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* add_eq_one_iff
- \+ *lemma* mul_eq_one_iff
- \+ *lemma* mul_right_eq_self_iff
- \+ *lemma* mul_left_eq_self_iff
- \+/\- *lemma* le_induction

Modified src/data/nat/prime.lean
- \+ *lemma* prime.mul_eq_prime_pow_two_iff
- \- *lemma* prime.mul_eq_prime_pow_two

Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/9c9aee4)
finish proof of sum two squares
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* prime.mul_eq_prime_pow_two

Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/number_theory/sum_two_squares.lean
- \+ *lemma* norm_nat_cast
- \+ *lemma* norm_one
- \+ *lemma* norm_zero
- \+ *lemma* norm_eq_one_iff
- \+ *lemma* norm_le_norm_mul_left
- \+ *lemma* sum_two_squares



## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/bd86c0d)
commit properly
#### Estimated changes
Modified src/data/zmod/quadratic_reciprocity.lean
- \+ *lemma* neg_one_is_square_iff_mod_four_ne_three

Modified src/number_theory/pell.lean


Modified src/number_theory/sum_two_squares.lean




## [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/49a85f4)
prove Z[i] is a euclidean_domain
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+ *lemma* abs_sub_round
- \+ *theorem* rat.cast_round
- \+ *def* round

Created src/number_theory/sum_two_squares.lean
- \+ *lemma* to_complex_def
- \+ *lemma* to_complex_def'
- \+ *lemma* to_complex_def₂
- \+ *lemma* int_cast_re
- \+ *lemma* int_cast_im
- \+ *lemma* to_complex_re'
- \+ *lemma* to_complex_im'
- \+ *lemma* to_complex_add
- \+ *lemma* to_complex_mul
- \+ *lemma* to_complex_one
- \+ *lemma* to_complex_zero
- \+ *lemma* to_complex_neg
- \+ *lemma* to_complex_sub
- \+ *lemma* to_complex_inj
- \+ *lemma* to_complex_eq_zero
- \+ *lemma* nat_cast_real_norm
- \+ *lemma* nat_cast_complex_norm
- \+ *lemma* norm_mul
- \+ *lemma* norm_eq_zero
- \+ *lemma* norm_pos
- \+ *lemma* div_def
- \+ *lemma* to_complex_div_re
- \+ *lemma* to_complex_div_im
- \+ *lemma* norm_sq_le_norm_sq_of_re_le_of_im_le
- \+ *lemma* norm_sq_div_sub_div_lt_one
- \+ *lemma* mod_def
- \+ *def* gaussian_int
- \+ *def* norm
- \+ *def* to_complex



## [2019-03-02 19:55:17](https://github.com/leanprover-community/mathlib/commit/1f4f2e4)
refactor(*): move matrix.lean to data/ and determinant.lean to linear_algebra/ ([#779](https://github.com/leanprover-community/mathlib/pull/779))
#### Estimated changes
Renamed src/ring_theory/matrix.lean to src/data/matrix.lean


Renamed src/ring_theory/determinant.lean to src/linear_algebra/determinant.lean




## [2019-03-01 22:25:45-05:00](https://github.com/leanprover-community/mathlib/commit/8fbf296)
feat(topology/metric_space/hausdorff_distance): Hausdorff distance
#### Estimated changes
Modified src/topology/basic.lean
- \+ *def* closeds
- \+ *def* nonempty_compacts

Modified src/topology/continuity.lean
- \+ *def* nonempty_compacts.to_closeds

Modified src/topology/metric_space/cau_seq_filter.lean
- \+ *lemma* half_pow_pos
- \+ *lemma* half_pow_tendsto_zero
- \+ *lemma* half_pow_add_succ
- \+ *lemma* half_pow_mono
- \+ *lemma* edist_le_two_mul_half_pow
- \+ *lemma* cauchy_seq_of_edist_le_half_pow
- \+ *lemma* B2_pos
- \+ *lemma* B2_lim
- \- *lemma* F_pos
- \- *lemma* F_lim
- \- *lemma* FB_pos
- \- *lemma* FB_lim

Created src/topology/metric_space/closeds.lean
- \+ *lemma* continuous_inf_edist_Hausdorff_edist
- \+ *lemma* is_closed_subsets_of_is_closed
- \+ *lemma* closeds.edist_eq
- \+ *lemma* nonempty_compacts.to_closeds.uniform_embedding
- \+ *lemma* nonempty_compacts.is_closed_in_closeds
- \+ *lemma* nonempty_compacts.dist_eq
- \+ *lemma* uniform_continuous_inf_dist_Hausdorff_dist

Created src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* inf_edist_empty
- \+ *lemma* inf_edist_union
- \+ *lemma* inf_edist_singleton
- \+ *lemma* inf_edist_le_edist_of_mem
- \+ *lemma* inf_edist_zero_of_mem
- \+ *lemma* inf_edist_le_inf_edist_of_subset
- \+ *lemma* exists_edist_lt_of_inf_edist_lt
- \+ *lemma* inf_edist_le_inf_edist_add_edist
- \+ *lemma* continuous_inf_edist
- \+ *lemma* inf_edist_closure
- \+ *lemma* mem_closure_iff_inf_edist_zero
- \+ *lemma* mem_iff_ind_edist_zero_of_closed
- \+ *lemma* inf_edist_image
- \+ *lemma* Hausdorff_edist_self
- \+ *lemma* Hausdorff_edist_comm
- \+ *lemma* Hausdorff_edist_le_of_inf_edist
- \+ *lemma* Hausdorff_edist_le_of_mem_edist
- \+ *lemma* inf_edist_le_Hausdorff_edist_of_mem
- \+ *lemma* exists_edist_lt_of_Hausdorff_edist_lt
- \+ *lemma* inf_edist_le_inf_edist_add_Hausdorff_edist
- \+ *lemma* Hausdorff_edist_image
- \+ *lemma* Hausdorff_edist_le_ediam
- \+ *lemma* Hausdorff_edist_triangle
- \+ *lemma* Hausdorff_edist_self_closure
- \+ *lemma* Hausdorff_edist_closure₁
- \+ *lemma* Hausdorff_edist_closure₂
- \+ *lemma* Hausdorff_edist_closure
- \+ *lemma* Hausdorff_edist_zero_iff_closure_eq_closure
- \+ *lemma* Hausdorff_edist_zero_iff_eq_of_closed
- \+ *lemma* Hausdorff_edist_empty
- \+ *lemma* ne_empty_of_Hausdorff_edist_ne_top
- \+ *lemma* inf_dist_nonneg
- \+ *lemma* inf_dist_empty
- \+ *lemma* inf_edist_ne_top
- \+ *lemma* inf_dist_zero_of_mem
- \+ *lemma* inf_dist_singleton
- \+ *lemma* inf_dist_le_dist_of_mem
- \+ *lemma* inf_dist_le_inf_dist_of_subset
- \+ *lemma* exists_dist_lt_of_inf_dist_lt
- \+ *lemma* inf_dist_le_inf_dist_add_dist
- \+ *lemma* uniform_continuous_inf_dist
- \+ *lemma* continuous_inf_dist
- \+ *lemma* inf_dist_eq_closure
- \+ *lemma* mem_closure_iff_inf_dist_zero
- \+ *lemma* mem_iff_ind_dist_zero_of_closed
- \+ *lemma* inf_dist_image
- \+ *lemma* Hausdorff_dist_nonneg
- \+ *lemma* Hausdorff_edist_ne_top_of_ne_empty_of_bounded
- \+ *lemma* Hausdorff_dist_self_zero
- \+ *lemma* Hausdorff_dist_comm
- \+ *lemma* Hausdorff_dist_empty
- \+ *lemma* Hausdorff_dist_empty'
- \+ *lemma* Hausdorff_dist_le_of_inf_dist
- \+ *lemma* Hausdorff_dist_le_of_mem_dist
- \+ *lemma* Hausdorff_dist_le_diam
- \+ *lemma* inf_dist_le_Hausdorff_dist_of_mem
- \+ *lemma* exists_dist_lt_of_Hausdorff_dist_lt
- \+ *lemma* exists_dist_lt_of_Hausdorff_dist_lt'
- \+ *lemma* inf_dist_le_inf_dist_add_Hausdorff_dist
- \+ *lemma* Hausdorff_dist_image
- \+ *lemma* Hausdorff_dist_triangle
- \+ *lemma* Hausdorff_dist_triangle'
- \+ *lemma* Hausdorff_dist_self_closure
- \+ *lemma* Hausdorff_dist_closure₁
- \+ *lemma* Hausdorff_dist_closure₂
- \+ *lemma* Hausdorff_dist_closure
- \+ *lemma* Hausdorff_dist_zero_iff_closure_eq_closure
- \+ *lemma* Hausdorff_dist_zero_iff_eq_of_closed
- \+ *def* inf_edist
- \+ *def* Hausdorff_edist
- \+ *def* inf_dist
- \+ *def* Hausdorff_dist



## [2019-03-01 21:24:00-05:00](https://github.com/leanprover-community/mathlib/commit/be88cec)
feat(analysis/exponential): added inequality lemmas
#### Estimated changes
Modified src/analysis/exponential.lean
- \+/\- *lemma* tendsto_exp_zero_one
- \+/\- *lemma* continuous_exp
- \+/\- *lemma* continuous_sin
- \+/\- *lemma* continuous_cos
- \+/\- *lemma* continuous_tan
- \+/\- *lemma* continuous_sinh
- \+/\- *lemma* continuous_cosh
- \+/\- *lemma* exists_exp_eq_of_pos
- \+/\- *lemma* exp_log
- \+/\- *lemma* log_exp
- \+/\- *lemma* log_zero
- \+/\- *lemma* log_one
- \+/\- *lemma* log_mul
- \+ *lemma* log_le_log
- \+/\- *lemma* exists_cos_eq_zero
- \+/\- *lemma* cos_pi_div_two
- \+/\- *lemma* one_le_pi_div_two
- \+/\- *lemma* pi_div_two_le_two
- \+/\- *lemma* two_le_pi
- \+/\- *lemma* pi_le_four
- \+/\- *lemma* pi_pos
- \+/\- *lemma* pi_div_two_pos
- \+/\- *lemma* two_pi_pos
- \+/\- *lemma* sin_pi
- \+/\- *lemma* cos_pi
- \+/\- *lemma* sin_two_pi
- \+/\- *lemma* cos_two_pi
- \+/\- *lemma* sin_add_pi
- \+/\- *lemma* sin_add_two_pi
- \+/\- *lemma* cos_add_two_pi
- \+/\- *lemma* sin_pi_sub
- \+/\- *lemma* cos_add_pi
- \+/\- *lemma* cos_pi_sub
- \+/\- *lemma* sin_pos_of_pos_of_lt_pi
- \+/\- *lemma* sin_nonneg_of_nonneg_of_le_pi
- \+/\- *lemma* sin_neg_of_neg_of_neg_pi_lt
- \+/\- *lemma* sin_nonpos_of_nonnpos_of_neg_pi_le
- \+/\- *lemma* sin_pi_div_two
- \+/\- *lemma* sin_add_pi_div_two
- \+/\- *lemma* sin_sub_pi_div_two
- \+/\- *lemma* sin_pi_div_two_sub
- \+/\- *lemma* cos_add_pi_div_two
- \+/\- *lemma* cos_sub_pi_div_two
- \+/\- *lemma* cos_pi_div_two_sub
- \+/\- *lemma* cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two
- \+/\- *lemma* cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two
- \+/\- *lemma* cos_neg_of_pi_div_two_lt_of_lt
- \+/\- *lemma* cos_nonpos_of_pi_div_two_le_of_le
- \+/\- *lemma* sin_nat_mul_pi
- \+/\- *lemma* sin_int_mul_pi
- \+/\- *lemma* cos_nat_mul_two_pi
- \+/\- *lemma* cos_int_mul_two_pi
- \+/\- *lemma* cos_int_mul_two_pi_add_pi
- \+/\- *lemma* sin_eq_zero_iff_of_lt_of_lt
- \+/\- *lemma* sin_eq_zero_iff
- \+/\- *lemma* sin_eq_zero_iff_cos_eq
- \+/\- *lemma* cos_eq_one_iff
- \+/\- *lemma* cos_eq_one_iff_of_lt_of_lt
- \+/\- *lemma* cos_lt_cos_of_nonneg_of_le_pi_div_two
- \+/\- *lemma* cos_lt_cos_of_nonneg_of_le_pi
- \+/\- *lemma* cos_le_cos_of_nonneg_of_le_pi
- \+/\- *lemma* sin_lt_sin_of_le_of_le_pi_div_two
- \+/\- *lemma* sin_le_sin_of_le_of_le_pi_div_two
- \+/\- *lemma* sin_inj_of_le_of_le_pi_div_two
- \+/\- *lemma* cos_inj_of_nonneg_of_le_pi
- \+/\- *lemma* exists_sin_eq
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_gsmul
- \+/\- *lemma* coe_two_pi
- \+/\- *lemma* angle_eq_iff_two_pi_dvd_sub
- \+/\- *lemma* arcsin_le_pi_div_two
- \+/\- *lemma* neg_pi_div_two_le_arcsin
- \+/\- *lemma* sin_arcsin
- \+/\- *lemma* arcsin_sin
- \+/\- *lemma* arcsin_inj
- \+/\- *lemma* arcsin_zero
- \+/\- *lemma* arcsin_one
- \+/\- *lemma* arcsin_neg
- \+/\- *lemma* arcsin_neg_one
- \+/\- *lemma* arcsin_nonneg
- \+/\- *lemma* arcsin_eq_zero_iff
- \+/\- *lemma* arcsin_pos
- \+/\- *lemma* arcsin_nonpos
- \+/\- *lemma* arccos_eq_pi_div_two_sub_arcsin
- \+/\- *lemma* arcsin_eq_pi_div_two_sub_arccos
- \+/\- *lemma* arccos_le_pi
- \+/\- *lemma* arccos_nonneg
- \+/\- *lemma* cos_arccos
- \+/\- *lemma* arccos_cos
- \+/\- *lemma* arccos_inj
- \+/\- *lemma* arccos_zero
- \+/\- *lemma* arccos_one
- \+/\- *lemma* arccos_neg_one
- \+/\- *lemma* arccos_neg
- \+/\- *lemma* cos_arcsin_nonneg
- \+/\- *lemma* cos_arcsin
- \+/\- *lemma* sin_arccos
- \+/\- *lemma* abs_div_sqrt_one_add_lt
- \+/\- *lemma* div_sqrt_one_add_lt_one
- \+/\- *lemma* neg_one_lt_div_sqrt_one_add
- \+/\- *lemma* tan_pos_of_pos_of_lt_pi_div_two
- \+/\- *lemma* tan_nonneg_of_nonneg_of_le_pi_div_two
- \+/\- *lemma* tan_neg_of_neg_of_pi_div_two_lt
- \+/\- *lemma* tan_nonpos_of_nonpos_of_neg_pi_div_two_le
- \+/\- *lemma* tan_lt_tan_of_nonneg_of_lt_pi_div_two
- \+/\- *lemma* tan_lt_tan_of_lt_of_lt_pi_div_two
- \+/\- *lemma* tan_inj_of_lt_of_lt_pi_div_two
- \+/\- *lemma* sin_arctan
- \+/\- *lemma* cos_arctan
- \+/\- *lemma* tan_arctan
- \+/\- *lemma* arctan_lt_pi_div_two
- \+/\- *lemma* neg_pi_div_two_lt_arctan
- \+/\- *lemma* tan_surjective
- \+/\- *lemma* arctan_tan
- \+/\- *lemma* arctan_zero
- \+/\- *lemma* arctan_neg
- \+/\- *lemma* arg_le_pi
- \+/\- *lemma* neg_pi_lt_arg
- \+/\- *lemma* arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg
- \+/\- *lemma* arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg
- \+/\- *lemma* arg_zero
- \+/\- *lemma* arg_one
- \+/\- *lemma* arg_neg_one
- \+/\- *lemma* arg_I
- \+/\- *lemma* arg_neg_I
- \+/\- *lemma* sin_arg
- \+/\- *lemma* cos_arg
- \+/\- *lemma* tan_arg
- \+/\- *lemma* arg_cos_add_sin_mul_I
- \+/\- *lemma* arg_eq_arg_iff
- \+/\- *lemma* arg_real_mul
- \+/\- *lemma* ext_abs_arg
- \+/\- *lemma* arg_of_real_of_nonneg
- \+/\- *lemma* arg_of_real_of_neg
- \+/\- *lemma* log_re
- \+/\- *lemma* log_im
- \+/\- *lemma* exp_inj_of_neg_pi_lt_of_le_pi
- \+/\- *lemma* of_real_log
- \+/\- *lemma* log_neg_one
- \+/\- *lemma* log_I
- \+/\- *lemma* log_neg_I
- \+/\- *lemma* exp_eq_one_iff
- \+/\- *lemma* exp_eq_exp_iff_exp_sub_eq_one
- \+/\- *lemma* exp_eq_exp_iff_exists_int
- \+/\- *lemma* cpow_def
- \+/\- *lemma* cpow_zero
- \+/\- *lemma* zero_cpow
- \+/\- *lemma* cpow_one
- \+/\- *lemma* one_cpow
- \+/\- *lemma* cpow_add
- \+/\- *lemma* cpow_mul
- \+/\- *lemma* cpow_neg
- \+/\- *lemma* cpow_nat_cast
- \+/\- *lemma* cpow_int_cast
- \+/\- *lemma* cpow_nat_inv_pow
- \+/\- *lemma* rpow_def
- \+/\- *lemma* rpow_def_of_nonneg
- \+/\- *lemma* of_real_cpow
- \+/\- *lemma* abs_cpow_real
- \+/\- *lemma* abs_cpow_inv_nat
- \+/\- *lemma* rpow_zero
- \+/\- *lemma* zero_rpow
- \+/\- *lemma* rpow_one
- \+/\- *lemma* one_rpow
- \+/\- *lemma* rpow_nonneg_of_nonneg
- \+/\- *lemma* rpow_add
- \+/\- *lemma* rpow_mul
- \+/\- *lemma* rpow_neg
- \+/\- *lemma* rpow_nat_cast
- \+/\- *lemma* rpow_int_cast
- \+ *lemma* mul_rpow
- \+ *lemma* one_le_rpow
- \+ *lemma* rpow_le_rpow
- \+/\- *lemma* pow_nat_rpow_nat_inv
- \+/\- *theorem* sin_sub_sin
- \+/\- *theorem* cos_eq_zero_iff
- \+/\- *theorem* cos_sub_cos
- \+/\- *theorem* cos_eq_iff_eq_or_eq_neg
- \+/\- *theorem* sin_eq_iff_eq_or_add_eq_pi
- \+/\- *theorem* cos_sin_inj
- \+/\- *def* angle

Modified src/data/complex/exponential.lean
- \+/\- *lemma* exp_le_exp



## [2019-03-01 21:15:38](https://github.com/leanprover-community/mathlib/commit/0bb0cec)
feat(group_theory): free_group and free_abelian_group are lawful monads ([#737](https://github.com/leanprover-community/mathlib/pull/737))
#### Estimated changes
Modified src/group_theory/free_abelian_group.lean
- \+ *lemma* map_pure
- \+ *lemma* map_zero
- \+ *lemma* map_add
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* pure_bind
- \+ *lemma* zero_bind
- \+ *lemma* add_bind
- \+ *lemma* neg_bind
- \+ *lemma* sub_bind
- \+ *lemma* pure_seq
- \+ *lemma* zero_seq
- \+ *lemma* add_seq
- \+ *lemma* neg_seq
- \+ *lemma* sub_seq
- \+ *lemma* seq_zero
- \+ *lemma* seq_add
- \+ *lemma* seq_neg
- \+ *lemma* seq_sub

Modified src/group_theory/free_group.lean
- \+/\- *lemma* quot_lift_mk
- \+/\- *lemma* quot_lift_on_mk
- \+ *lemma* map_pure
- \+ *lemma* map_one
- \+ *lemma* map_mul
- \+ *lemma* map_inv
- \+ *lemma* pure_bind
- \+ *lemma* one_bind
- \+ *lemma* mul_bind
- \+ *lemma* inv_bind
- \+/\- *theorem* map.comp
- \+/\- *theorem* to_group_eq_prod_map
- \+/\- *def* free_group



## [2019-03-01 21:14:41](https://github.com/leanprover-community/mathlib/commit/116cfff)
feat(data/zmod/basic): cast_mod_nat' and cast_mod_int' ([#783](https://github.com/leanprover-community/mathlib/pull/783))
* cast_mod_int'
* cast_val_int'
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* cast_mod_nat'
- \+ *lemma* cast_mod_int'
- \+ *lemma* eq_iff_modeq_nat'
- \+ *lemma* eq_iff_modeq_int'



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/04b5f88)
refactor(analysis/asymptotics): minor formatting changes
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+/\- *theorem* is_O_refl
- \+/\- *theorem* is_o.to_is_O
- \+/\- *theorem* is_O.add
- \+/\- *theorem* is_o.add
- \+/\- *theorem* is_O.sub
- \+/\- *theorem* is_o.sub
- \+/\- *theorem* is_O.symm
- \+/\- *theorem* is_o.symm
- \+/\- *theorem* is_O_const_mul_left
- \+/\- *theorem* is_O_const_smul_left_iff
- \+/\- *theorem* is_o_const_smul_left
- \+/\- *theorem* tendsto_nhds_zero_of_is_o



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/6363212)
feat(analysis/normed_space/deriv): generalize to spaces over any normed field
#### Estimated changes
Modified src/analysis/normed_space/deriv.lean
- \+ *theorem* has_fderiv_at_filter_real_equiv
- \- *theorem* has_fderiv_at_filter_equiv_aux



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/89b8915)
feat(analysis/normed_space/deriv): add readable proof of chain rule
#### Estimated changes
Modified src/analysis/normed_space/deriv.lean




## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/5dd1ba5)
feat(analysis/*): is_bigo -> is_O, is_littleo -> is_o
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *theorem* is_O_refl
- \+ *theorem* is_O.comp
- \+ *theorem* is_o.comp
- \+ *theorem* is_O.mono
- \+ *theorem* is_o.mono
- \+ *theorem* is_o.to_is_O
- \+ *theorem* is_O.trans
- \+ *theorem* is_o.trans_is_O
- \+ *theorem* is_O.trans_is_o
- \+ *theorem* is_o.trans
- \+ *theorem* is_o_join
- \+ *theorem* is_O_congr
- \+ *theorem* is_o_congr
- \+ *theorem* is_O.congr
- \+ *theorem* is_o.congr
- \+ *theorem* is_O_congr_left
- \+ *theorem* is_o_congr_left
- \+ *theorem* is_O.congr_left
- \+ *theorem* is_o.congr_left
- \+ *theorem* is_O_congr_right
- \+ *theorem* is_o_congr_right
- \+ *theorem* is_O.congr_right
- \+ *theorem* is_o.congr_right
- \+ *theorem* is_O_norm_right
- \+ *theorem* is_o_norm_right
- \+ *theorem* is_O_neg_right
- \+ *theorem* is_o_neg_right
- \+ *theorem* is_O_iff
- \+ *theorem* is_O_join
- \+ *theorem* is_O_norm_left
- \+ *theorem* is_o_norm_left
- \+ *theorem* is_O_neg_left
- \+ *theorem* is_o_neg_left
- \+ *theorem* is_O.add
- \+ *theorem* is_o.add
- \+ *theorem* is_O.sub
- \+ *theorem* is_o.sub
- \+ *theorem* is_O_comm
- \+ *theorem* is_O.symm
- \+ *theorem* is_O.tri
- \+ *theorem* is_O.congr_of_sub
- \+ *theorem* is_o_comm
- \+ *theorem* is_o.symm
- \+ *theorem* is_o.tri
- \+ *theorem* is_o.congr_of_sub
- \+ *theorem* is_O_zero
- \+ *theorem* is_O_refl_left
- \+ *theorem* is_O_zero_right_iff
- \+ *theorem* is_o_zero
- \+ *theorem* is_o_refl_left
- \+ *theorem* is_o_zero_right_iff
- \+ *theorem* is_O_const_one
- \+ *theorem* is_O_const_mul_left
- \+ *theorem* is_O_const_mul_left_iff
- \+ *theorem* is_o_const_mul_left
- \+ *theorem* is_o_const_mul_left_iff
- \+ *theorem* is_O_of_is_O_const_mul_right
- \+ *theorem* is_O_const_mul_right_iff
- \+ *theorem* is_o_of_is_o_const_mul_right
- \+ *theorem* is_o_const_mul_right
- \+ *theorem* is_o_one_iff
- \+ *theorem* is_O.trans_tendsto
- \+ *theorem* is_o.trans_tendsto
- \+ *theorem* is_O_mul
- \+ *theorem* is_o_mul_left
- \+ *theorem* is_o_mul_right
- \+ *theorem* is_o_mul
- \+ *theorem* is_O_const_smul_left
- \+ *theorem* is_O_const_smul_left_iff
- \+ *theorem* is_o_const_smul_left
- \+ *theorem* is_o_const_smul_left_iff
- \+ *theorem* is_O_const_smul_right
- \+ *theorem* is_o_const_smul_right
- \+ *theorem* is_O_smul
- \+ *theorem* is_o_smul
- \+ *theorem* tendsto_nhds_zero_of_is_o
- \+ *theorem* is_o_iff_tendsto
- \- *theorem* is_bigo_refl
- \- *theorem* is_bigo.comp
- \- *theorem* is_littleo.comp
- \- *theorem* is_bigo.mono
- \- *theorem* is_littleo.mono
- \- *theorem* is_littleo.to_is_bigo
- \- *theorem* is_bigo.trans
- \- *theorem* is_littleo.trans_is_bigo
- \- *theorem* is_bigo.trans_is_littleo
- \- *theorem* is_littleo.trans
- \- *theorem* is_littleo_join
- \- *theorem* is_bigo_congr
- \- *theorem* is_littleo_congr
- \- *theorem* is_bigo.congr
- \- *theorem* is_littleo.congr
- \- *theorem* is_bigo_congr_left
- \- *theorem* is_littleo_congr_left
- \- *theorem* is_bigo.congr_left
- \- *theorem* is_littleo.congr_left
- \- *theorem* is_bigo_congr_right
- \- *theorem* is_littleo_congr_right
- \- *theorem* is_bigo.congr_right
- \- *theorem* is_littleo.congr_right
- \- *theorem* is_bigo_norm_right
- \- *theorem* is_littleo_norm_right
- \- *theorem* is_bigo_neg_right
- \- *theorem* is_littleo_neg_right
- \- *theorem* is_bigo_iff
- \- *theorem* is_bigo_join
- \- *theorem* is_bigo_norm_left
- \- *theorem* is_littleo_norm_left
- \- *theorem* is_bigo_neg_left
- \- *theorem* is_littleo_neg_left
- \- *theorem* is_bigo.add
- \- *theorem* is_littleo.add
- \- *theorem* is_bigo.sub
- \- *theorem* is_littleo.sub
- \- *theorem* is_bigo_comm
- \- *theorem* is_bigo.symm
- \- *theorem* is_bigo.tri
- \- *theorem* is_bigo.congr_of_sub
- \- *theorem* is_littleo_comm
- \- *theorem* is_littleo.symm
- \- *theorem* is_littleo.tri
- \- *theorem* is_littleo.congr_of_sub
- \- *theorem* is_bigo_zero
- \- *theorem* is_bigo_refl_left
- \- *theorem* is_bigo_zero_right_iff
- \- *theorem* is_littleo_zero
- \- *theorem* is_littleo_refl_left
- \- *theorem* is_littleo_zero_right_iff
- \- *theorem* is_bigo_const_one
- \- *theorem* is_bigo_const_mul_left
- \- *theorem* is_bigo_const_mul_left_iff
- \- *theorem* is_littleo_const_mul_left
- \- *theorem* is_littleo_const_mul_left_iff
- \- *theorem* is_bigo_of_is_bigo_const_mul_right
- \- *theorem* is_bigo_const_mul_right_iff
- \- *theorem* is_littleo_of_is_littleo_const_mul_right
- \- *theorem* is_littleo_const_mul_right
- \- *theorem* is_littleo_one_iff
- \- *theorem* is_bigo.trans_tendsto
- \- *theorem* is_littleo.trans_tendsto
- \- *theorem* is_bigo_mul
- \- *theorem* is_littleo_mul_left
- \- *theorem* is_littleo_mul_right
- \- *theorem* is_littleo_mul
- \- *theorem* is_bigo_const_smul_left
- \- *theorem* is_bigo_const_smul_left_iff
- \- *theorem* is_littleo_const_smul_left
- \- *theorem* is_littleo_const_smul_left_iff
- \- *theorem* is_bigo_const_smul_right
- \- *theorem* is_littleo_const_smul_right
- \- *theorem* is_bigo_smul
- \- *theorem* is_littleo_smul
- \- *theorem* tendsto_nhds_zero_of_is_littleo
- \- *theorem* is_littleo_iff_tendsto
- \+ *def* is_O
- \+ *def* is_o
- \- *def* is_bigo
- \- *def* is_littleo

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *theorem* is_O_id
- \+ *theorem* is_O_comp
- \+ *theorem* is_O_sub
- \- *theorem* is_bigo_id
- \- *theorem* is_bigo_comp
- \- *theorem* is_bigo_sub

Modified src/analysis/normed_space/deriv.lean
- \+ *theorem* has_fderiv_at_filter.is_o
- \+ *theorem* has_fderiv_at.is_o
- \+ *theorem* has_fderiv_at_filter.is_O_sub
- \- *theorem* has_fderiv_at_filter.is_littleo
- \- *theorem* has_fderiv_at.is_littleo
- \- *theorem* has_fderiv_at_filter.is_bigo_sub



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/49ecc7b)
fix(*): fix things from change tendsto_congr -> tendsto.congr'
#### Estimated changes
Modified src/analysis/normed_space/deriv.lean


Modified src/analysis/specific_limits.lean


Modified src/data/padics/hensel.lean


Modified src/order/filter/basic.lean
- \+ *theorem* tendsto.congr'r
- \- *theorem* tendsto_congr

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/instances/ennreal.lean




## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/d74804b)
add has_fderiv_at_filter
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *theorem* is_bigo_congr
- \+ *theorem* is_littleo_congr
- \+ *theorem* is_bigo.congr
- \+ *theorem* is_littleo.congr
- \+ *theorem* is_bigo_congr_left
- \+ *theorem* is_littleo_congr_left
- \+ *theorem* is_bigo_congr_right
- \+ *theorem* is_littleo_congr_right
- \+/\- *theorem* is_bigo_norm_left
- \+/\- *theorem* is_littleo_norm_left
- \+/\- *theorem* is_bigo_neg_left
- \+/\- *theorem* is_littleo_neg_left
- \+ *theorem* is_bigo_comm
- \+ *theorem* is_bigo.symm
- \+ *theorem* is_bigo.tri
- \+ *theorem* is_bigo.congr_of_sub
- \+ *theorem* is_littleo_comm
- \+ *theorem* is_littleo.symm
- \+ *theorem* is_littleo.tri
- \+ *theorem* is_littleo.congr_of_sub
- \+ *theorem* is_bigo_refl_left
- \+ *theorem* is_littleo_refl_left
- \+ *theorem* is_bigo.trans_tendsto
- \+ *theorem* is_littleo.trans_tendsto

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *theorem* is_bigo_comp

Modified src/analysis/normed_space/deriv.lean
- \+ *theorem* has_fderiv_at_filter.is_littleo
- \+ *theorem* has_fderiv_at_filter_equiv_aux
- \+ *theorem* has_fderiv_at_filter_iff_tendsto
- \+/\- *theorem* has_fderiv_at_within_iff_tendsto
- \+ *theorem* has_fderiv_at_filter.mono
- \+/\- *theorem* has_fderiv_at_within.mono
- \+ *theorem* has_fderiv_at_filter_of_has_fderiv_at
- \+/\- *theorem* has_fderiv_at_within_of_has_fderiv_at
- \+ *theorem* has_fderiv_at_filter_congr'
- \+ *theorem* has_fderiv_at_filter_congr
- \+ *theorem* has_fderiv_at_filter.congr
- \+ *theorem* has_fderiv_at_within_congr
- \+ *theorem* has_fderiv_at_congr
- \+/\- *theorem* has_fderiv_at.congr
- \+ *theorem* has_fderiv_at_filter_id
- \+ *theorem* has_fderiv_at_filter_const
- \+ *theorem* has_fderiv_at_filter_smul
- \+ *theorem* has_fderiv_at_filter_add
- \+/\- *theorem* has_fderiv_at_within_add
- \+/\- *theorem* has_fderiv_at_add
- \+ *theorem* has_fderiv_at_filter_neg
- \+/\- *theorem* has_fderiv_at_within_neg
- \+/\- *theorem* has_fderiv_at_neg
- \+ *theorem* has_fderiv_at_filter_sub
- \+/\- *theorem* has_fderiv_at_within_sub
- \+/\- *theorem* has_fderiv_at_sub
- \+ *theorem* has_fderiv_at_filter.is_bigo_sub
- \+ *theorem* has_fderiv_at_filter.tendsto_nhds
- \+ *theorem* has_fderiv_at_within.continuous_at_within
- \+ *theorem* has_fderiv_at.continuous_at
- \+ *theorem* has_fderiv_at_filter.comp
- \+ *theorem* has_fderiv_at_within.comp
- \+ *theorem* has_fderiv_at.comp
- \- *theorem* has_fderiv_at_within_equiv_aux
- \- *theorem* continuous_at_within_of_has_fderiv_at_within
- \- *theorem* continuous_at_of_has_fderiv_at
- \- *theorem* chain_rule_at_within
- \- *theorem* chain_rule
- \+ *def* has_fderiv_at_filter
- \+/\- *def* has_fderiv_at_within

Modified src/order/filter/basic.lean
- \+ *lemma* congr_sets
- \+ *lemma* tendsto.congr'
- \- *lemma* tendsto_cong
- \+ *theorem* tendsto_congr

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
- \+ *theorem* is_bigo_refl
- \+ *theorem* is_bigo.trans
- \+ *theorem* is_littleo.trans_is_bigo
- \+ *theorem* is_bigo.trans_is_littleo
- \+ *theorem* is_littleo.trans
- \+ *theorem* is_littleo_join
- \+ *theorem* is_bigo.congr_left
- \+ *theorem* is_littleo.congr_left
- \+ *theorem* is_bigo.congr_right
- \+ *theorem* is_littleo.congr_right
- \+ *theorem* is_bigo_iff
- \+ *theorem* is_bigo_join
- \+/\- *theorem* is_littleo.add
- \+/\- *theorem* is_littleo.sub
- \+/\- *theorem* is_bigo_zero
- \+ *theorem* is_bigo_zero_right_iff
- \+/\- *theorem* is_littleo_zero
- \+ *theorem* is_littleo_zero_right_iff
- \+ *theorem* is_bigo_const_one
- \+ *theorem* is_bigo_const_mul_left
- \+ *theorem* is_bigo_const_mul_left_iff
- \+ *theorem* is_littleo_const_mul_left
- \+ *theorem* is_littleo_const_mul_left_iff
- \+ *theorem* is_bigo_of_is_bigo_const_mul_right
- \+ *theorem* is_bigo_const_mul_right_iff
- \+ *theorem* is_littleo_of_is_littleo_const_mul_right
- \+ *theorem* is_littleo_const_mul_right
- \+ *theorem* is_littleo_one_iff
- \+ *theorem* is_bigo_mul
- \+/\- *theorem* is_littleo_mul_left
- \+/\- *theorem* is_littleo_mul_right
- \+ *theorem* is_littleo_mul
- \+ *theorem* is_bigo_const_smul_left
- \+ *theorem* is_bigo_const_smul_left_iff
- \+ *theorem* is_littleo_const_smul_left
- \+ *theorem* is_littleo_const_smul_left_iff
- \+ *theorem* is_bigo_const_smul_right
- \+ *theorem* is_littleo_const_smul_right
- \+ *theorem* is_bigo_smul
- \+ *theorem* is_littleo_smul
- \+/\- *theorem* tendsto_nhds_zero_of_is_littleo
- \- *theorem* is_bigo_iff_pos
- \- *theorem* is_littleo_iff_pos
- \- *theorem* is_bigo_mul_left
- \- *theorem* is_bigo_mul_right
- \- *theorem* is_bigo_smul_left
- \- *theorem* is_littleo_smul_left
- \- *theorem* is_bigo_smul_right
- \- *theorem* is_littleo_smul_right
- \- *theorem* is_bigo_of_is_bigo_of_is_bigo
- \- *theorem* is_littleo_of_is_littleo_of_is_bigo
- \- *theorem* is_littleo_of_is_bigo_of_is_littleo
- \- *theorem* is_littleo_of_tendsto

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *def* to_linear_map

Modified src/analysis/normed_space/deriv.lean
- \+ *theorem* has_fderiv_at.is_littleo
- \+ *theorem* has_fderiv_at_within_equiv_aux
- \+ *theorem* has_fderiv_at_within_iff_tendsto
- \+ *theorem* has_fderiv_at_iff_tendsto
- \+ *theorem* has_fderiv_at_within.mono
- \+ *theorem* has_fderiv_at_within_of_has_fderiv_at
- \+/\- *theorem* has_fderiv_at_within.congr
- \+ *theorem* has_fderiv_at.congr
- \+ *theorem* has_fderiv_at_within_id
- \+ *theorem* has_fderiv_at_id
- \+ *theorem* has_fderiv_at_within_const
- \+ *theorem* has_fderiv_at_const
- \+ *theorem* has_fderiv_at_within_smul
- \+ *theorem* has_fderiv_at_smul
- \+ *theorem* has_fderiv_at_within_add
- \+ *theorem* has_fderiv_at_add
- \+ *theorem* has_fderiv_at_within_neg
- \+ *theorem* has_fderiv_at_neg
- \+ *theorem* has_fderiv_at_within_sub
- \+ *theorem* has_fderiv_at_sub
- \+ *theorem* continuous_at_within_of_has_fderiv_at_within
- \+ *theorem* continuous_at_of_has_fderiv_at
- \+ *theorem* chain_rule_at_within
- \+/\- *theorem* chain_rule
- \- *theorem* has_fderiv_equiv_aux
- \- *theorem* has_fderiv_iff_littleo
- \- *theorem* has_fderiv_id
- \- *theorem* has_fderiv_const
- \- *theorem* has_fderiv_smul
- \- *theorem* has_fderiv_add
- \- *theorem* has_fderiv_neg
- \- *theorem* has_fderiv_sub
- \- *theorem* continuous_of_has_fderiv
- \- *def* has_fderiv_at_within_mono

Modified src/topology/basic.lean




## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/6265d26)
feat(analysis/normed_space/deriv): start on derivative
#### Estimated changes
Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *theorem* is_bigo_id
- \+ *theorem* is_bigo_sub
- \+ *def* to_linear_map

Created src/analysis/normed_space/deriv.lean
- \+ *theorem* has_fderiv_equiv_aux
- \+ *theorem* has_fderiv_iff_littleo
- \+ *theorem* has_fderiv_at_within.congr
- \+ *theorem* has_fderiv_id
- \+ *theorem* has_fderiv_const
- \+ *theorem* has_fderiv_smul
- \+ *theorem* has_fderiv_add
- \+ *theorem* has_fderiv_neg
- \+ *theorem* has_fderiv_sub
- \+ *theorem* continuous_of_has_fderiv
- \+ *theorem* chain_rule
- \+ *def* has_fderiv_at_within
- \+ *def* has_fderiv_at
- \+ *def* has_fderiv_at_within_mono



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/92a5e0b)
feat(analysis/asymptotics): start on bigo and littlo
#### Estimated changes
Created src/analysis/asymptotics.lean
- \+ *theorem* is_bigo.comp
- \+ *theorem* is_littleo.comp
- \+ *theorem* is_bigo.mono
- \+ *theorem* is_littleo.mono
- \+ *theorem* is_littleo.to_is_bigo
- \+ *theorem* is_bigo_zero
- \+ *theorem* is_littleo_zero
- \+ *theorem* is_bigo_norm_right
- \+ *theorem* is_littleo_norm_right
- \+ *theorem* is_bigo_neg_right
- \+ *theorem* is_littleo_neg_right
- \+ *theorem* is_bigo_iff_pos
- \+ *theorem* is_bigo_norm_left
- \+ *theorem* is_littleo_norm_left
- \+ *theorem* is_bigo_neg_left
- \+ *theorem* is_littleo_neg_left
- \+ *theorem* is_bigo.add
- \+ *theorem* is_bigo.sub
- \+ *theorem* is_littleo_iff_pos
- \+ *theorem* is_littleo.add
- \+ *theorem* is_littleo.sub
- \+ *theorem* is_bigo_mul_left
- \+ *theorem* is_littleo_mul_left
- \+ *theorem* is_bigo_mul_right
- \+ *theorem* is_littleo_mul_right
- \+ *theorem* is_bigo_smul_left
- \+ *theorem* is_littleo_smul_left
- \+ *theorem* is_bigo_smul_right
- \+ *theorem* is_littleo_smul_right
- \+ *theorem* is_bigo_of_is_bigo_of_is_bigo
- \+ *theorem* is_littleo_of_is_littleo_of_is_bigo
- \+ *theorem* is_littleo_of_is_bigo_of_is_littleo
- \+ *theorem* tendsto_nhds_zero_of_is_littleo
- \+ *theorem* is_littleo_of_tendsto
- \+ *theorem* is_littleo_iff_tendsto
- \+ *def* is_bigo
- \+ *def* is_littleo



## [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/206a7a1)
feat(*): add various small lemmas
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_norm
- \+ *lemma* tendsto_smul_const
- \+ *theorem* normed_space.tendsto_nhds_zero

Modified src/order/filter/basic.lean
- \+ *lemma* le_comap_top
- \+ *theorem* tendsto.congr

Modified src/topology/basic.lean
- \+ *theorem* tendsto_nhds_within_mono_left
- \+ *theorem* tendsto_nhds_within_mono_right
- \+ *theorem* tendsto_nhds_within_of_tendsto_nhds
- \+ *theorem* tendsto_nhds_within_iff_subtype
- \- *theorem* tendsto_at_within_iff_subtype

Modified src/topology/continuity.lean
- \+ *theorem* nhds_within_le_comap



## [2019-03-01 13:10:17](https://github.com/leanprover-community/mathlib/commit/4f7853a)
feat(data/list/basic): mem_rotate
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* mem_rotate

