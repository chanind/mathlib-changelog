### [2019-03-31 21:33:03+02:00](https://github.com/leanprover-community/mathlib/commit/c91e6c2)
fix(ring_theory/algebra): remove duplicate theorems to fix build

### [2019-03-31 08:35:59-04:00](https://github.com/leanprover-community/mathlib/commit/9480df5)
refactor(computability): unpack fixed_point proof

### [2019-03-31 08:35:21-04:00](https://github.com/leanprover-community/mathlib/commit/359cac1)
feat(computability): computable_iff_re_compl_re

### [2019-03-31 08:32:21-04:00](https://github.com/leanprover-community/mathlib/commit/514de77)
feat(data/finset): to_finset_eq_empty

### [2019-03-31 08:31:39-04:00](https://github.com/leanprover-community/mathlib/commit/72634d2)
feat(data/complex/basic): smul_re,im

### [2019-03-31 00:48:41](https://github.com/leanprover-community/mathlib/commit/e1c035d)
feat(data/polynomial): eval₂_neg

### [2019-03-29 23:56:28](https://github.com/leanprover-community/mathlib/commit/c2bb4c5)
refactor(data/zsqrtd/basic): move zsqrtd out of pell and into data ([#861](https://github.com/leanprover-community/mathlib/pull/861))

### [2019-03-29 15:03:34-05:00](https://github.com/leanprover-community/mathlib/commit/dc7de46)
feat(analysis/convex): convex sets and functions ([#834](https://github.com/leanprover-community/mathlib/pull/834))

### [2019-03-29 13:08:29-04:00](https://github.com/leanprover-community/mathlib/commit/171e913)
fix(scripts/remote-install-update-mathlib): add GitPython dependency ([#860](https://github.com/leanprover-community/mathlib/pull/860))

### [2019-03-28 22:56:01-04:00](https://github.com/leanprover-community/mathlib/commit/2e7f009)
fix(scripts/deploy_nightly): pushing to the `lean-3.4.2` branch is sometimes blocked ([#859](https://github.com/leanprover-community/mathlib/pull/859))

### [2019-03-28 22:11:15-04:00](https://github.com/leanprover-community/mathlib/commit/a4fd55c)
feat(library_search): a simple library_search function ([#839](https://github.com/leanprover-community/mathlib/pull/839))

### [2019-03-28 20:04:39-04:00](https://github.com/leanprover-community/mathlib/commit/59caf11)
fix(scripts/update-mathlib): fix imports of python files

### [2019-03-28 19:11:34-04:00](https://github.com/leanprover-community/mathlib/commit/6cd336c)
fix(scripts/update-mathlib): github authentication

### [2019-03-28 16:32:00-04:00](https://github.com/leanprover-community/mathlib/commit/1c04a32)
fix(scripts/update-mathlib): update-mathlib shouldn't need github authentication

### [2019-03-28 14:01:35-04:00](https://github.com/leanprover-community/mathlib/commit/48df321)
feat(category_theory/instances): category of groups ([#749](https://github.com/leanprover-community/mathlib/pull/749))

### [2019-03-28 16:25:01](https://github.com/leanprover-community/mathlib/commit/179d4d0)
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

### [2019-03-27 21:28:39-04:00](https://github.com/leanprover-community/mathlib/commit/25bab56)
feat(scripts/cache_olean): cache and fetch olean binaries ([#766](https://github.com/leanprover-community/mathlib/pull/766))
* script setup and documentation
* fetch mathlib nightly when relevant
* use credentials to access `github.com`
* locate correct git directory, and add prompt
* add confirmation message to setup-dev-scripts
* adding --build-all option

### [2019-03-27 21:47:02+01:00](https://github.com/leanprover-community/mathlib/commit/8838ff3)
feat(algebra/field_power): add fpow_one, one_fpow, fpow_mul, mul_fpow (closes [#855](https://github.com/leanprover-community/mathlib/pull/855))

### [2019-03-27 20:15:04+01:00](https://github.com/leanprover-community/mathlib/commit/8429354)
feat(analysis): add real.rpow_le_one

### [2019-03-27 20:15:04+01:00](https://github.com/leanprover-community/mathlib/commit/4305ad6)
feat(analysis): add rpow_pos_of_pos

### [2019-03-27 09:57:35-05:00](https://github.com/leanprover-community/mathlib/commit/02ca494)
Remove outparam in normed space ([#844](https://github.com/leanprover-community/mathlib/pull/844))

### [2019-03-27 08:20:35-04:00](https://github.com/leanprover-community/mathlib/commit/52fddda)
feat(algebra/archimedean): lemmas about powers of elements ([#802](https://github.com/leanprover-community/mathlib/pull/802))

### [2019-03-26 16:35:47-05:00](https://github.com/leanprover-community/mathlib/commit/17e40bb)
feat(tactic/congr): apply to `iff` propositions ([#833](https://github.com/leanprover-community/mathlib/pull/833))

### [2019-03-26 21:53:30+01:00](https://github.com/leanprover-community/mathlib/commit/c3a9028)
fix(data/polynomial): (nat_)degree_map' assumed a comm_ring instead of a comm_semiring

### [2019-03-26 19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/a016652)
feat(data/finset): add range_add_one'

### [2019-03-26 19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/0ea37e9)
feat(algebra/big_operators): add prod_map, sum_map

### [2019-03-26 19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/d3c68fc)
feat(analysis/normed_space): tendsto_zero_iff_norm_tendsto_zero

### [2019-03-26 19:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/df08058)
refactor(analysis/normed_space): rename norm_mul -> norm_mul_le; use norm_mul for the equality in normed fields; and norm_mul_le for the inequality in normed_rings

### [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/bd21b0e)
feat(analyis/normed_space): add normed_field instance for ℂ

### [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/a01cf86)
feat(data/multiset,data/finset): add multiset./finset.le_sum_of_additive

### [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/c912253)
feat(algebra/group_power): add lt_of_pow_lt_pow

### [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/fd37f96)
feat(data/fin): add injective_cast_le

### [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/c0c2edb)
feat(algebra/big_operators): add Gauss' summation formula

### [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/cfeb887)
feat(data/polynomial): degree_map', nat_degree_map' semiring variant of degree_map, nat_degree_map

### [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/aa2c6e2)
feat(data/mv_polynomial): more about renaming

### [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/5b73f46)
chore(data/mv_polynomial): use type name as filename

### [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/8ccca3f)
feat(data/finsupp): add emb_domain

### [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/d7bd41f)
feat(linear_algebra/dimension): add exists_mem_ne_zero_of_dim_pos

### [2019-03-26 18:22:00+01:00](https://github.com/leanprover-community/mathlib/commit/22352ff)
feat(linear_algebra/dimension): add dim_span_le; add rank_finset_sum_le

### [2019-03-26 17:46:31+01:00](https://github.com/leanprover-community/mathlib/commit/f882b8b)
feat(data/polynomial): rec_on_horner ([#739](https://github.com/leanprover-community/mathlib/pull/739))

### [2019-03-26 00:11:19](https://github.com/leanprover-community/mathlib/commit/410ae5d)
feat(group_theory/subgroup): add inv_iff_ker' and related ([#790](https://github.com/leanprover-community/mathlib/pull/790))
* feat(group_theory/subgroup): add inv_iff_ker' and related
* correcting spacing and adding to_additive attribute
* changing name to ker-mk

### [2019-03-25 16:03:35-04:00](https://github.com/leanprover-community/mathlib/commit/0bb64a2)
feat(tactic/solve_by_elim): working with multiple goals ([#838](https://github.com/leanprover-community/mathlib/pull/838))

### [2019-03-25 19:21:49](https://github.com/leanprover-community/mathlib/commit/291a4f3)
refactor(algebra/group_action): use notation for monoid/group actions ([#846](https://github.com/leanprover-community/mathlib/pull/846))
* refactor(module_action): bundle and introduce notation
* fix(linear_algebra/determinant): fix the coercion issue using a local notation
* fix(linear_algebra/dimension): fix build

### [2019-03-25 18:24:08](https://github.com/leanprover-community/mathlib/commit/a1158d8)
feat(algebra/module): every abelian group is a Z-module ([#848](https://github.com/leanprover-community/mathlib/pull/848))

### [2019-03-25 16:59:27+01:00](https://github.com/leanprover-community/mathlib/commit/cb5e185)
refactor(data/equiv): equiv_injective_surjective ([#849](https://github.com/leanprover-community/mathlib/pull/849))

### [2019-03-23 21:28:16+01:00](https://github.com/leanprover-community/mathlib/commit/cd7402d)
Minor clarification to simpa doc ([#842](https://github.com/leanprover-community/mathlib/pull/842))

### [2019-03-23 12:56:54-04:00](https://github.com/leanprover-community/mathlib/commit/b0b33ab)
fix(import): remove relative imports

### [2019-03-22 16:02:14](https://github.com/leanprover-community/mathlib/commit/c29769f)
fix(ring_theory/multiplicity): correct spelling mistake in docstring

### [2019-03-22 13:22:43+01:00](https://github.com/leanprover-community/mathlib/commit/b5bb446)
fix(doc/extra/tactic_writing): fix a minor error ([#841](https://github.com/leanprover-community/mathlib/pull/841)) [ci-skip]
* fix(doc/extra/tactic_writing): fix a minor error
* comma splice

### [2019-03-22 00:28:38](https://github.com/leanprover-community/mathlib/commit/989efab)
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

### [2019-03-21 23:44:25](https://github.com/leanprover-community/mathlib/commit/798a08d)
feat(group_theory/submonoid): add closure_singleton ([#810](https://github.com/leanprover-community/mathlib/pull/810))
* feat(group_theory/submonoid): add closure_singleton
* adding some to_additive

### [2019-03-20 10:16:08-04:00](https://github.com/leanprover-community/mathlib/commit/098c2cb)
feat(tactic/wlog): `discharger` defaults to classical `tauto` ([#836](https://github.com/leanprover-community/mathlib/pull/836))

### [2019-03-18 00:04:29](https://github.com/leanprover-community/mathlib/commit/d60d161)
feat(linear_algebra/basic): add ring instance ([#823](https://github.com/leanprover-community/mathlib/pull/823))

### [2019-03-17 21:08:06](https://github.com/leanprover-community/mathlib/commit/9ff5e8d)
feat(algebra/punit_instances): punit instances ([#828](https://github.com/leanprover-community/mathlib/pull/828))

### [2019-03-17 21:07:14](https://github.com/leanprover-community/mathlib/commit/df996be)
fix(topology/algebra/group): fix binders for top group extensionality ([#826](https://github.com/leanprover-community/mathlib/pull/826))

### [2019-03-17 09:07:33-05:00](https://github.com/leanprover-community/mathlib/commit/e8bdc7f)
feat(order/filter/filter_product): build hyperreals ([#801](https://github.com/leanprover-community/mathlib/pull/801))
Construction of filter products, ultraproducts, some instances, hyperreal numbers.

### [2019-03-16 09:30:48-05:00](https://github.com/leanprover-community/mathlib/commit/0c2c2bd)
feat(group_theory/perm/cycles): cycle_factors ([#815](https://github.com/leanprover-community/mathlib/pull/815))

### [2019-03-16 09:28:41-05:00](https://github.com/leanprover-community/mathlib/commit/7b001c9)
feat(data/set/intervals): add missing intervals + some lemmas ([#805](https://github.com/leanprover-community/mathlib/pull/805))
The lemmas about Icc ⊆ I** are important for convexity

### [2019-03-14 10:32:41+01:00](https://github.com/leanprover-community/mathlib/commit/2bf44d3)
refactor(*): rename metric_space_subtype to subtype.metric_space ([#817](https://github.com/leanprover-community/mathlib/pull/817))

### [2019-03-14 10:31:53+01:00](https://github.com/leanprover-community/mathlib/commit/c5afc52)
feat(topology/metric_space/baire): Baire theorem ([#816](https://github.com/leanprover-community/mathlib/pull/816))

### [2019-03-13 23:45:07-04:00](https://github.com/leanprover-community/mathlib/commit/72100bd)
feat(tactic/squeeze,hole): remove needless qualifications in names

### [2019-03-12 13:37:46-04:00](https://github.com/leanprover-community/mathlib/commit/82f79a5)
feat(data/list|multiset|finset): lemmas about intervals in nat ([#795](https://github.com/leanprover-community/mathlib/pull/795))

### [2019-03-12 13:53:34+01:00](https://github.com/leanprover-community/mathlib/commit/2738f9b)
chore(topology/*): @uniformity α _ becomes 𝓤 α ([#814](https://github.com/leanprover-community/mathlib/pull/814))
This is a binder type change and a local notation

### [2019-03-12 01:04:54-04:00](https://github.com/leanprover-community/mathlib/commit/3360267)
feat(tactic/basic): folding over the environment, to get all declarations ([#798](https://github.com/leanprover-community/mathlib/pull/798))

### [2019-03-11 16:11:52-04:00](https://github.com/leanprover-community/mathlib/commit/bde8690)
feat(data/alist,data/finmap): union ([#750](https://github.com/leanprover-community/mathlib/pull/750))

### [2019-03-11 17:09:10+01:00](https://github.com/leanprover-community/mathlib/commit/eb96a25)
feat(topology/algebra/group): extensionality for top group structure

### [2019-03-11 14:06:20](https://github.com/leanprover-community/mathlib/commit/69249d8)
feat(topology/algebra/monoid): add is_submonoid.mem_nhds_one ([#809](https://github.com/leanprover-community/mathlib/pull/809))

### [2019-03-09 17:49:20-05:00](https://github.com/leanprover-community/mathlib/commit/51c31ce)
refactor(data/list): rm redundant eq_nil_of_forall_not_mem ([#804](https://github.com/leanprover-community/mathlib/pull/804))

### [2019-03-09 11:34:38](https://github.com/leanprover-community/mathlib/commit/e8818fa)
feat(data/set/finite): add finite_lt_nat ([#807](https://github.com/leanprover-community/mathlib/pull/807))

### [2019-03-08 20:10:50](https://github.com/leanprover-community/mathlib/commit/7de57e8)
feat(ring_theory/noetherian): Nakayama's Lemma ([#778](https://github.com/leanprover-community/mathlib/pull/778))
* feat(ring_theory/noetherian): Nakayama's Lemma
* Update src/ring_theory/noetherian.lean
Co-Authored-By: kckennylau <kc_kennylau@yahoo.com.hk>

### [2019-03-08 15:01:45+01:00](https://github.com/leanprover-community/mathlib/commit/1159fa9)
refactot(data/equiv/basic): rename apply_inverse_apply to apply_symm_apply ([#800](https://github.com/leanprover-community/mathlib/pull/800))

### [2019-03-08 13:42:54+01:00](https://github.com/leanprover-community/mathlib/commit/b1af140)
style(data/list/basic): clean up count_bag_inter

### [2019-03-08 08:46:58+01:00](https://github.com/leanprover-community/mathlib/commit/ffa6d69)
feat(*): has_mem (set α) (filter α) ([#799](https://github.com/leanprover-community/mathlib/pull/799))

### [2019-03-07 23:35:39+01:00](https://github.com/leanprover-community/mathlib/commit/7e77967)
refactor(localization): shorten proofs ([#796](https://github.com/leanprover-community/mathlib/pull/796))
* feat(algebra/group): units.coe_map
* refactor(localization): shorten proofs
*  swap order of equality in ring_equiv.symm_to_equiv

### [2019-03-07 10:17:21-05:00](https://github.com/leanprover-community/mathlib/commit/26bd400)
feat(data/list): lemmas about count and bag_inter ([#797](https://github.com/leanprover-community/mathlib/pull/797))

### [2019-03-06 20:07:22-05:00](https://github.com/leanprover-community/mathlib/commit/181647b)
feat(tactic/basic): utility functions for names ([#791](https://github.com/leanprover-community/mathlib/pull/791))

### [2019-03-06 23:01:10](https://github.com/leanprover-community/mathlib/commit/48eaf05)
feat(algebra/group): units.coe_map

### [2019-03-06 22:11:42](https://github.com/leanprover-community/mathlib/commit/e286452)
feat(data/nat/basic): some lemmas ([#792](https://github.com/leanprover-community/mathlib/pull/792))
* feat(data/nat/basic): some lemmas
* fixing namespace, moving lemma

### [2019-03-06 10:16:34-05:00](https://github.com/leanprover-community/mathlib/commit/61e02dd)
feat(data/finset): missing fold_map lemma ([#794](https://github.com/leanprover-community/mathlib/pull/794))

### [2019-03-06 14:21:24](https://github.com/leanprover-community/mathlib/commit/cc753d7)
feat(ring_theory/localization): adds induced ring hom between fraction rings ([#781](https://github.com/leanprover-community/mathlib/pull/781))
* feat(ring_theory/localization): adds induced ring hom between fraction rings
* Break some extremely long lines
* Put map in the fraction_ring namespace
* Move global variable into statements
* Rename rec to lift', make interface for lift, generalise map
* Improve simp-lemmas, add docstrings
* Rename circ to comp in lemma names

### [2019-03-05 21:55:19+01:00](https://github.com/leanprover-community/mathlib/commit/1ec0a1f)
fix(tactic/linarith): correctly parse 0*0

### [2019-03-05 14:15:40-05:00](https://github.com/leanprover-community/mathlib/commit/581cf19)
feat(topology): split uniform_space and topological_structure

### [2019-03-05 09:50:45+01:00](https://github.com/leanprover-community/mathlib/commit/708c0cf)
feat(data/multiset): add monad instance ([#744](https://github.com/leanprover-community/mathlib/pull/744))

### [2019-03-05 09:44:51+01:00](https://github.com/leanprover-community/mathlib/commit/3525d21)
refactor(topology/metric_space/lipschitz): Simplify proof in banach contraction ([#788](https://github.com/leanprover-community/mathlib/pull/788))

### [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/b9f88d1)
feat(data/finset): add card_sdiff

### [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/682f4b5)
feat(linear_algebra): module (vector space) structure for finsupp, matrix, and mv polynomials

### [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/738778a)
feat(data/matrix): basic definitions: transpose; row & column matrix; vector/matrix multiplication

### [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/528ff93)
refactor(linear_algebra): move multivariate_polynomial to data

### [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/891a192)
refactor(ring_theory): move matrix to data and determinant to linear_algebra

### [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/10a586b)
feat(linear_algebra): add module (vector_space) structure for function spaces

### [2019-03-05 09:21:46+01:00](https://github.com/leanprover-community/mathlib/commit/332121d)
feat(data/fintype): card_univ and card_univ_diff

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c0b1eb1)
refactor(data/finset): correct name sdiff_disjoint -> disjoint_sdiff; add sdiff_disjoint

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/b3c749b)
remove superflous parameter from bot_eq_zero

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/73f1a08)
feat(data/finset): add filter_empty, filter_subset_filter, prod_filter

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/b9ead4d)
feat(data/finset): add disjoint_bind_left/right

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/f82f5f2)
refactor(algebra): canonically_ordered_monoid extends order_bot

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/f07a558)
feat(data/equiv): add subtype_pi_equiv_pi

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/8070c05)
feat(data/set/lattice): more rules for disjoint sets

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c53ac41)
feat(data/set): relate range and image to Union

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/41038ba)
feat(data/set): add exists_maximal_wrt

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/146d73c)
feat(data/set): add finite_image_iff_on

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/84a5f4d)
feat(data/set): add subset_image_iff and subset_range_iff

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/cbe2f61)
feat(logic/function): add inv_fun_neg

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/73db4c7)
feat(logic/function): add injective.ne

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c819617)
feat(logic): add plift.down_inj

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/985445f)
feat(linear_algebra/multivariate_polynomial): relate total_degree to degrees, add, zero, mul

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/78fd58d)
feat(linear_algebra/multivariate_polynomial): add degrees

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/c2d8bc2)
feat(data/finsupp): relatie to_multiset to 0, +, single, card, map, prod, and to_finset

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/857842d)
feat(data/finsupp): add support_mul

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/a77797f)
feat(data/multiset): add prod_smul

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/e924745)
feat(data/finset): add multiset.count_sup

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/e07cac5)
feat(data/finset): add to_finset_smul

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/f24b01b)
feat(algebra/group_power): smul and pow are monoid homs

### [2019-03-05 09:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/32642e1)
feat(linear_algebra): add dim_sup_add_dim_inf_eq

### [2019-03-04 16:26:09+01:00](https://github.com/leanprover-community/mathlib/commit/f46f0a6)
feat(tactic/fin_cases): case bashing on finset, list, and fintype hypotheses. ([#775](https://github.com/leanprover-community/mathlib/pull/775))

### [2019-03-04 12:37:27+01:00](https://github.com/leanprover-community/mathlib/commit/6cd0341)
docs(extras/tactic_writing): add ``%%(reflect n)`` to the tactic writing guide ([#786](https://github.com/leanprover-community/mathlib/pull/786))

### [2019-03-03 19:05:12+01:00](https://github.com/leanprover-community/mathlib/commit/201413b)
chore(topology): Splits topology.basic and topology.continuity ([#785](https://github.com/leanprover-community/mathlib/pull/785))
Also, the most basic aspects of continuity are now in topology.basic

### [2019-03-03 11:01:43-05:00](https://github.com/leanprover-community/mathlib/commit/1084868)
feat(analysis/{specific_limits,infinite_sum}): Cauchy of geometric bound ([#753](https://github.com/leanprover-community/mathlib/pull/753))

### [2019-03-03 13:19:35](https://github.com/leanprover-community/mathlib/commit/1f90e18)
feat(ring_theory/ideal_operations): Chinese Remainder Theorem ([#774](https://github.com/leanprover-community/mathlib/pull/774))

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/fb8001d)
hopefully fixed for good this time

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/182b2a3)
fix properly

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/a4cc8b7)
fix build

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/a75d57c)
fix build

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/8dcd071)
generalize norm to zsqrtd

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/d98cae7)
fix build

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/5cbd7fa)
changing names

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/a9dfaba)
The year is 2019

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/c36470f)
put sum_two_squares in nat.prime namespace

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/d8f0921)
move lemmas to correct places

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/4e48324)
fix build

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/9c9aee4)
finish proof of sum two squares

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/bd86c0d)
commit properly

### [2019-03-02 17:42:14-05:00](https://github.com/leanprover-community/mathlib/commit/49a85f4)
prove Z[i] is a euclidean_domain

### [2019-03-02 19:55:17](https://github.com/leanprover-community/mathlib/commit/1f4f2e4)
refactor(*): move matrix.lean to data/ and determinant.lean to linear_algebra/ ([#779](https://github.com/leanprover-community/mathlib/pull/779))

### [2019-03-01 22:25:45-05:00](https://github.com/leanprover-community/mathlib/commit/8fbf296)
feat(topology/metric_space/hausdorff_distance): Hausdorff distance

### [2019-03-01 21:24:00-05:00](https://github.com/leanprover-community/mathlib/commit/be88cec)
feat(analysis/exponential): added inequality lemmas

### [2019-03-01 21:15:38](https://github.com/leanprover-community/mathlib/commit/0bb0cec)
feat(group_theory): free_group and free_abelian_group are lawful monads ([#737](https://github.com/leanprover-community/mathlib/pull/737))

### [2019-03-01 21:14:41](https://github.com/leanprover-community/mathlib/commit/116cfff)
feat(data/zmod/basic): cast_mod_nat' and cast_mod_int' ([#783](https://github.com/leanprover-community/mathlib/pull/783))
* cast_mod_int'
* cast_val_int'

### [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/04b5f88)
refactor(analysis/asymptotics): minor formatting changes

### [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/6363212)
feat(analysis/normed_space/deriv): generalize to spaces over any normed field

### [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/89b8915)
feat(analysis/normed_space/deriv): add readable proof of chain rule

### [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/5dd1ba5)
feat(analysis/*): is_bigo -> is_O, is_littleo -> is_o

### [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/49ecc7b)
fix(*): fix things from change tendsto_congr -> tendsto.congr'

### [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/d74804b)
add has_fderiv_at_filter

### [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/21b1fcc)
fix(asymptotics, deriv): minor formatting fixes

### [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/16033bb)
feat(analysis/asymptotics,analysis/normed_space/deriv): improvements and additions

### [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/6265d26)
feat(analysis/normed_space/deriv): start on derivative

### [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/92a5e0b)
feat(analysis/asymptotics): start on bigo and littlo

### [2019-03-01 10:20:26-05:00](https://github.com/leanprover-community/mathlib/commit/206a7a1)
feat(*): add various small lemmas

### [2019-03-01 13:10:17](https://github.com/leanprover-community/mathlib/commit/4f7853a)
feat(data/list/basic): mem_rotate