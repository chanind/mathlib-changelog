### [2019-02-28 20:55:23](https://github.com/leanprover-community/mathlib/commit/05449a0)
refactor(ring_theory/localization): rename of to mk, and define of ([#765](https://github.com/leanprover-community/mathlib/pull/765))
* refactor(ring_theory/localization): rename of to mk, and define of
* Make submonoid implicit variable of 'of'

### [2019-02-28 19:14:55](https://github.com/leanprover-community/mathlib/commit/eb033cf)
feat(ring_theory/ideals): make ideal.quotient.field a discrete_field ([#777](https://github.com/leanprover-community/mathlib/pull/777))

### [2019-02-28 17:20:01](https://github.com/leanprover-community/mathlib/commit/e6a3ca8)
refactor(algebra/group): generalise and extend the API for with_zero ([#762](https://github.com/leanprover-community/mathlib/pull/762))
* refactor(algebra/group): generalise and extend the API for with_zero
* Shorter proof. Thanks Chris
* Travis, try your best

### [2019-02-28 16:55:44](https://github.com/leanprover-community/mathlib/commit/781d187)
feat(group_theory/quotient_group): define ker_lift and prove simp-lemmas ([#764](https://github.com/leanprover-community/mathlib/pull/764))
* feat(group_theory/quotient_group): define ker_lift and prove simp-lemmas
* Add docstring

### [2019-02-28 11:09:35+01:00](https://github.com/leanprover-community/mathlib/commit/81f8530)
fix(tactic/linarith): typo

### [2019-02-28 10:33:40+01:00](https://github.com/leanprover-community/mathlib/commit/08d4d17)
feat(topology/basic): Add instances for subset/inter/union for opens(X) ([#763](https://github.com/leanprover-community/mathlib/pull/763))
* feat(topology/basic): Add instances for subset/inter/union for opens(X)

### [2019-02-27 23:53:37+01:00](https://github.com/leanprover-community/mathlib/commit/477338d)
refactor(data/subtype): organise in namespaces, use variables, add two simp-lemmas ([#760](https://github.com/leanprover-community/mathlib/pull/760))

### [2019-02-27 22:46:52](https://github.com/leanprover-community/mathlib/commit/af2cf74)
feat(group_theory/quotient_group): map is a group hom ([#761](https://github.com/leanprover-community/mathlib/pull/761))

### [2019-02-27 22:37:11](https://github.com/leanprover-community/mathlib/commit/dfa855c)
feat(data/finset) remove unnecessary assumption from card_eq_succ ([#772](https://github.com/leanprover-community/mathlib/pull/772))

### [2019-02-27 23:14:03+01:00](https://github.com/leanprover-community/mathlib/commit/cfde449)
fix(doc/tactics): linarith doc is outdated [ci-skip]

### [2019-02-27 21:33:02+01:00](https://github.com/leanprover-community/mathlib/commit/6c71ac0)
fix(tactic/linarith): fix bug in strengthening of strict nat/int inequalities

### [2019-02-27 15:25:19](https://github.com/leanprover-community/mathlib/commit/4667d2c)
feat(ring_theory/ideal_operations): ideals form a commutative semiring ([#771](https://github.com/leanprover-community/mathlib/pull/771))

### [2019-02-27 14:06:24](https://github.com/leanprover-community/mathlib/commit/05d1d33)
fix(algebra/archimedean): swap names of floor_add_fract and fract_add_floor ([#770](https://github.com/leanprover-community/mathlib/pull/770))

### [2019-02-27 12:02:24+01:00](https://github.com/leanprover-community/mathlib/commit/42d1ed7)
feat(linarith): improve handling of strict inequalities in nat and int ([#769](https://github.com/leanprover-community/mathlib/pull/769))
* feat(linarith): perform slightly better on ℕ and ℤ by strengthening t < 0 hyps to t + 1 ≤ 0
* remove already completed TODO item

### [2019-02-26 22:04:45+01:00](https://github.com/leanprover-community/mathlib/commit/3f47739)
fix(docs/howto-contribute): main repository has moved

### [2019-02-26 12:57:23-05:00](https://github.com/leanprover-community/mathlib/commit/7450cc5)
fix(scripts/update_mathlib): improve python style and error handling ([#759](https://github.com/leanprover-community/mathlib/pull/759))

### [2019-02-25 16:20:56-05:00](https://github.com/leanprover-community/mathlib/commit/71a7e1c)
fix(scripts/update-mathlib): cached archived were never expanded

### [2019-02-25 16:01:35-05:00](https://github.com/leanprover-community/mathlib/commit/4222483)
fix(scripts/update-mathlib): fix the commit check

### [2019-02-24 23:52:02-05:00](https://github.com/leanprover-community/mathlib/commit/e23553a)
doc(nat/decidable_prime): add docstrings explaining the two decidable_prime instances ([#757](https://github.com/leanprover-community/mathlib/pull/757))

### [2019-02-24 15:36:34](https://github.com/leanprover-community/mathlib/commit/f922086)
feat(ring_theory/polynomial): more operations on polynomials ([#679](https://github.com/leanprover-community/mathlib/pull/679))

### [2019-02-24 11:59:27](https://github.com/leanprover-community/mathlib/commit/c9b2d0e)
chore(linear_algebra/multivariate_polynomial): remove unnecessary decidable_eq assumption ([#755](https://github.com/leanprover-community/mathlib/pull/755))

### [2019-02-23 11:37:37](https://github.com/leanprover-community/mathlib/commit/ddc016c)
feat(*): polar co-ordinates, de moivre, trig identities, quotient group for angles ([#745](https://github.com/leanprover-community/mathlib/pull/745))
* feat(algebra/group_power): re-PRing polar co-ords
* Update group_power.lean
* feat(analysis/exponential): re-PRing polar stuff
* feat(data.complex.exponential): re-PR polar stuff
* fix(analysis.exponential): stylistic
* fix(data.complex.exponential): stylistic
* fix(analysis/exponential.lean): angle_eq_iff_two_pi_dvd_sub
* fix(analysis/exponential): angle_eq_iff_two_pi_dvd_sub

### [2019-02-23 00:41:40](https://github.com/leanprover-community/mathlib/commit/63fa61d)
fix(analysis/specific_limits): remove useless assumption ([#751](https://github.com/leanprover-community/mathlib/pull/751))

### [2019-02-21 21:35:05](https://github.com/leanprover-community/mathlib/commit/e739cf5)
feat(order_dual): instances for order_dual and shortening proofs ([#746](https://github.com/leanprover-community/mathlib/pull/746))
* feat(order_bot): instances for order_bot and shortening proofs
* fix(topological_structure); remove unused import

### [2019-02-21 16:24:47](https://github.com/leanprover-community/mathlib/commit/3c3a052)
feat(field_theory/subfield): closure of subset in field ([#742](https://github.com/leanprover-community/mathlib/pull/742))

### [2019-02-20 18:08:04-05:00](https://github.com/leanprover-community/mathlib/commit/9656485)
feat(data/finmap): lift_on₂ ([#716](https://github.com/leanprover-community/mathlib/pull/716))
* feat(data/finmap): define lift_on₂ with lift_on

### [2019-02-20 17:32:07](https://github.com/leanprover-community/mathlib/commit/8b8ae32)
fix(order/basic): give order_dual the correct lt ([#741](https://github.com/leanprover-community/mathlib/pull/741))

### [2019-02-20 12:33:02](https://github.com/leanprover-community/mathlib/commit/c7202e5)
feat(analysis/exponential): pow_nat_rpow_nat_inv ([#740](https://github.com/leanprover-community/mathlib/pull/740))

### [2019-02-18 18:07:10](https://github.com/leanprover-community/mathlib/commit/78ce6e4)
feat(data/fintype): fintype.of_injective

### [2019-02-18 09:48:21-05:00](https://github.com/leanprover-community/mathlib/commit/9a2c13a)
feat(data/alist,data/finmap): always insert key-value pair ([#722](https://github.com/leanprover-community/mathlib/pull/722))
* Change {alist,finmap}.insert to always insert the key-value pair
  instead of doing nothing if the inserted key is found. This allows for
  useful theorems such as lookup_insert.
* Add list.keys and used key membership instead of exists/forall. This
  makes proofs easier in some places.
* Add a few other useful theorems such as lookup_eq_none,
  lookup_erase, lookup_erase_ne.

### [2019-02-18 09:45:57](https://github.com/leanprover-community/mathlib/commit/6b4435b)
feat(data/polynomial): create nonzero_comm_semiring and generalize nonzero_comm_ring lemmas ([#736](https://github.com/leanprover-community/mathlib/pull/736))

### [2019-02-16 21:24:09](https://github.com/leanprover-community/mathlib/commit/c64b67e)
feat(ring_theory/localization): revamp, ideal embedding ([#481](https://github.com/leanprover-community/mathlib/pull/481))

### [2019-02-15 17:29:36-05:00](https://github.com/leanprover-community/mathlib/commit/17f9bef)
feat(category/monad/cont): continuation passing monad ([#728](https://github.com/leanprover-community/mathlib/pull/728))

### [2019-02-15 19:37:56](https://github.com/leanprover-community/mathlib/commit/0a6e705)
refactor(data/equiv/algebra): move polynomial lemmas from equiv/algebra to mv_polynomial ([#731](https://github.com/leanprover-community/mathlib/pull/731))
* refactor(data/equiv/algebra): move polynomial lemma from equiv/algebra to mv_polynomial
* remove update-mathlib.py

### [2019-02-15 14:26:25+01:00](https://github.com/leanprover-community/mathlib/commit/d80b03e)
chore(order/filter/basic): update documentation of filter_upwards

### [2019-02-15 07:40:09](https://github.com/leanprover-community/mathlib/commit/8730619)
chore(topology/algebra/topological_structures): remove unused import ([#729](https://github.com/leanprover-community/mathlib/pull/729))

### [2019-02-14 18:26:14+01:00](https://github.com/leanprover-community/mathlib/commit/ce580d7)
refactor(data/equiv): rename subtype_equiv_of_subtype to subtype_congr and subtype_congr to subtype_congr_prop

### [2019-02-14 18:04:51+01:00](https://github.com/leanprover-community/mathlib/commit/683519f)
feat(data/equiv/basic): generalise subtype_equiv_of_subtype ([#724](https://github.com/leanprover-community/mathlib/pull/724))

### [2019-02-14 18:04:24+01:00](https://github.com/leanprover-community/mathlib/commit/d4568a4)
fix(data/subtype): don't use pattern matching in subtype.map ([#725](https://github.com/leanprover-community/mathlib/pull/725))

### [2019-02-13 19:51:35-05:00](https://github.com/leanprover-community/mathlib/commit/5da8605)
chore(deploy): clean up deploy_nightly.sh ([#720](https://github.com/leanprover-community/mathlib/pull/720))

### [2019-02-13 23:30:38+01:00](https://github.com/leanprover-community/mathlib/commit/a6150a3)
refactor(data/real): move cau_seq_filter to analysis/metric_space ([#723](https://github.com/leanprover-community/mathlib/pull/723))

### [2019-02-13 17:01:08+01:00](https://github.com/leanprover-community/mathlib/commit/3fd0e60)
refactor(topology/algebra/infinite_sum): Cauchy condition for infinite sums generalized to complete topological groups

### [2019-02-12 22:44:40+01:00](https://github.com/leanprover-community/mathlib/commit/246c280)
feat(tactic/basic,tactic/interactive): improvements to set tactic ([#712](https://github.com/leanprover-community/mathlib/pull/712))
* feat(tactic/basic,tactic/interactive): improvements to set tactic
* feat(tactic/interactive): take optional explicit type in set tactic

### [2019-02-12 15:50:35-05:00](https://github.com/leanprover-community/mathlib/commit/f6ca16e)
fix(nightly): improve conditional ([#719](https://github.com/leanprover-community/mathlib/pull/719))

### [2019-02-12 20:15:49+01:00](https://github.com/leanprover-community/mathlib/commit/a4afa90)
refactor(analysis/specific_limits): generalize has_sum_of_absolute_convergence to normed_groups

### [2019-02-12 09:33:43-05:00](https://github.com/leanprover-community/mathlib/commit/503a423)
feat(update-mathlib): improve setup and error messages

### [2019-02-12 15:28:42+01:00](https://github.com/leanprover-community/mathlib/commit/b6a4763)
refactor(order/filter): replace tendsto_comp_succ_at_top_iff by tendsto_add_at_top_iff_nat

### [2019-02-12 08:46:53-05:00](https://github.com/leanprover-community/mathlib/commit/c4e8414)
fix(update-mathlib): install from anywhere in your directory structure

### [2019-02-12 14:09:42+01:00](https://github.com/leanprover-community/mathlib/commit/f5a85f1)
refactor(order/filter): move lift and lift' to separate file

### [2019-02-12 11:17:26+01:00](https://github.com/leanprover-community/mathlib/commit/253fe33)
refactor(order/filter): generalize map_succ_at_top_eq to arbitrary Galois insertions; generalize tendsto_coe_iff to arbitary order-preserving embeddings

### [2019-02-12 11:17:26+01:00](https://github.com/leanprover-community/mathlib/commit/c853c33)
chore(analysis/specific_limits): replace mul_add_one_le_pow by pow_ge_one_add_mul

### [2019-02-12 09:12:26](https://github.com/leanprover-community/mathlib/commit/41e3b6f)
refactor(data/list): add prop arg for easier usage ([#715](https://github.com/leanprover-community/mathlib/pull/715))

### [2019-02-11 20:48:17-05:00](https://github.com/leanprover-community/mathlib/commit/d1ef181)
feat(topology/metric_space/gluing): Gluing metric spaces ([#695](https://github.com/leanprover-community/mathlib/pull/695))

### [2019-02-11 15:43:36-05:00](https://github.com/leanprover-community/mathlib/commit/8243300)
build(nightly): fix nightly

### [2019-02-11 16:50:18](https://github.com/leanprover-community/mathlib/commit/fb7e42d)
fix(group_theory/quotient_group): remove duplicate group_hom instance ([#713](https://github.com/leanprover-community/mathlib/pull/713))

### [2019-02-11 10:13:54+01:00](https://github.com/leanprover-community/mathlib/commit/4b84aac)
fix(data/finsupp): duplicated instance

### [2019-02-10 21:50:00](https://github.com/leanprover-community/mathlib/commit/091cad7)
feat(algebra/gcd_domain): normalize ([#668](https://github.com/leanprover-community/mathlib/pull/668))

### [2019-02-10 12:36:00-05:00](https://github.com/leanprover-community/mathlib/commit/cfe582f)
Automate the deployment of nightly builds ([#707](https://github.com/leanprover-community/mathlib/pull/707))
* build(nightly): automate nightly releases of mathlib

### [2019-02-10 16:44:30](https://github.com/leanprover-community/mathlib/commit/9b28db0)
refactor(*): refactor associates ([#710](https://github.com/leanprover-community/mathlib/pull/710))

### [2019-02-10 14:25:05](https://github.com/leanprover-community/mathlib/commit/c25122b)
feat(algebra/archimedean): add fractional parts of floor_rings ([#709](https://github.com/leanprover-community/mathlib/pull/709))

### [2019-02-10 14:01:02+01:00](https://github.com/leanprover-community/mathlib/commit/d6f84da)
feat(tactic/tidy): add `tidy?` syntax for reporting a tactic script ([#704](https://github.com/leanprover-community/mathlib/pull/704))

### [2019-02-10 10:39:51](https://github.com/leanprover-community/mathlib/commit/ed4c536)
feat(data/polynomial): multiplicity of roots of polynomials ([#656](https://github.com/leanprover-community/mathlib/pull/656))
* feat(data/polynomial): multiplicity of roots of polynomials
* rename lemmas
* use section
* use `nonzero_comm_ring.of_ne`
* refactor(polynomial): weaken decidablility hypothesis
* indentation
* swap order of arguments

### [2019-02-09 15:41:40](https://github.com/leanprover-community/mathlib/commit/088f753)
refactor(geo_sum): remove duplicate proofs about geometric sums ([#706](https://github.com/leanprover-community/mathlib/pull/706))
* feat(data/finset): add range_add_one
* feat(algebra/big_operators): geometric sum for semiring, ring and division ring
* refactor(geo_sum): remove duplicate proofs about geometric sums

### [2019-02-09 15:38:37](https://github.com/leanprover-community/mathlib/commit/484d864)
add geometric sum ([#701](https://github.com/leanprover-community/mathlib/pull/701))
* feat(data/finset): add range_add_one
* feat(algebra/big_operators): geometric sum for semiring, ring and division ring

### [2019-02-08 20:56:33-05:00](https://github.com/leanprover-community/mathlib/commit/22c7179)
build(update-mathlib): adjust the header of python script

### [2019-02-08 18:41:17-05:00](https://github.com/leanprover-community/mathlib/commit/8b51017)
build(update-mathlib): fix installation and documentation

### [2019-02-08 17:13:15-05:00](https://github.com/leanprover-community/mathlib/commit/650237b)
build(update-mathlib): install update-mathlib into `~/.mathlib/bin`

### [2019-02-08 17:01:46-05:00](https://github.com/leanprover-community/mathlib/commit/814cb03)
build(update-mathlib): fix installation and documentation

### [2019-02-08 16:55:19-05:00](https://github.com/leanprover-community/mathlib/commit/64065f4)
build(update-mathlib): improve installation and documentation

### [2019-02-08 16:11:45-05:00](https://github.com/leanprover-community/mathlib/commit/4227f5c)
Deploy olean ([#697](https://github.com/leanprover-community/mathlib/pull/697))
* deploy(olean): deploy the olean files for every successful builds

### [2019-02-08 19:05:45](https://github.com/leanprover-community/mathlib/commit/11e19d8)
refactor(ring_theory/noetherian): make is_noetherian and is_noetherian_ring classes ([#689](https://github.com/leanprover-community/mathlib/pull/689))
* refactor(ring_theory/noetherian): make is_noetherian and is_noetherian_ring classes
* correct spelling mistake.
* add well_founded_submodule_gt

### [2019-02-08 13:11:06-05:00](https://github.com/leanprover-community/mathlib/commit/1f50e0d)
fix(build): fix the output keeping travis builds alive ([#702](https://github.com/leanprover-community/mathlib/pull/702))

### [2019-02-08 09:43:02-05:00](https://github.com/leanprover-community/mathlib/commit/0f2562e)
fix(build): fix the output keeping travis builds alive ([#700](https://github.com/leanprover-community/mathlib/pull/700))

### [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/cfd2b75)
feat(order/filter): break filter into smaller files

### [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/8db042f)
feat(data/rel): galois_connection (image r) (core r)

### [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/b2ba37c)
chore(*): fix errors introduced by rebasing

### [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/8e4aafa)
feat(analysis/metric): convergence wrt nhds_within

### [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/f5d73bd)
feat(analysis/topology/continuity): add some variations

### [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/e0b8253)
feat (analysis/topology/topological_space): properties of nhds, nhds_within

### [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/a96fa3b)
feat(order/filter): convergence for relations and partial functions

### [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/4444464)
feat(data/pfun): add restrict, preimage, core, etc.

### [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/cae5c8b)
fix(data/rel): make composition local notation

### [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/4779af7)
feat(data/rel): a type for binary relations

### [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/126d573)
feat(data/set/basic,logic/function): small additions and renamings

### [2019-02-07 22:32:47](https://github.com/leanprover-community/mathlib/commit/1ed7ad1)
feat(algebra/archimedean): abs_sub_lt_one_of_floor_eq_floor ([#693](https://github.com/leanprover-community/mathlib/pull/693))
* abs_diff_lt_one_of_floor_eq_floor
* better name

### [2019-02-07 19:37:17+01:00](https://github.com/leanprover-community/mathlib/commit/177b5eb)
feat(linear_algebra): dimension of the base field is 1

### [2019-02-07 19:36:51+01:00](https://github.com/leanprover-community/mathlib/commit/0f24030)
refactor(src/data/finset): supr/infi as a directed supr/infi of finite inf/sup

### [2019-02-07 15:56:26+01:00](https://github.com/leanprover-community/mathlib/commit/eeed321)
chore(linear_algebra/basic): relate map/comap/ker/range/comp with 0 and smul; use map/comap Galois connection

### [2019-02-07 14:58:25+01:00](https://github.com/leanprover-community/mathlib/commit/e98999e)
chore(algebra/pi_instances): generalize pi.list/multiset/finset_prod/sum_apply to dependent types

### [2019-02-07 14:58:25+01:00](https://github.com/leanprover-community/mathlib/commit/ad7ef86)
refactor(set_theory/cardinal): split up mk_Union_le_mk_sigma, add mk_Union_eq_mk_sigma; add equiv congruence for subtype

### [2019-02-07 13:13:39+01:00](https://github.com/leanprover-community/mathlib/commit/8a1de24)
feat(data/{list/alist,finmap}): implicit key type ([#662](https://github.com/leanprover-community/mathlib/pull/662))
* feat(data/{list/alist,finmap}): implicit key type
Make the key type α implicit in both alist and finmap. This brings these
types into line with the underlying sigma and simplifies usage since α
is inferred from the value function type β : α → Type v.
* doc(data/list/alist): alist is stored as a linked list

### [2019-02-07 13:02:53+01:00](https://github.com/leanprover-community/mathlib/commit/46d1009)
feat(analysis/metric_space): Isometries ([#657](https://github.com/leanprover-community/mathlib/pull/657))

### [2019-02-07 10:22:13](https://github.com/leanprover-community/mathlib/commit/8911b8c)
feat(algebra/order_functions): max_lt_max and min_lt_min ([#692](https://github.com/leanprover-community/mathlib/pull/692))

### [2019-02-06 20:15:47](https://github.com/leanprover-community/mathlib/commit/51f80a3)
feat(data/quot): quotient.ind' ([#691](https://github.com/leanprover-community/mathlib/pull/691))
* feat(data/quot): quotient.ind'
* correct elaborator tag; theorems not definitions

### [2019-02-06 10:58:04+01:00](https://github.com/leanprover-community/mathlib/commit/9615b38)
feat(data/real): completeness criterion for Cauchy sequences (closes [#654](https://github.com/leanprover-community/mathlib/pull/654))

### [2019-02-06 10:36:56+01:00](https://github.com/leanprover-community/mathlib/commit/3ac7967)
feat(analysis/metric_space): add premetric spaces (closes [#652](https://github.com/leanprover-community/mathlib/pull/652))

### [2019-02-06 10:29:32+01:00](https://github.com/leanprover-community/mathlib/commit/e93fa30)
feat(category/fold): `foldl` and `foldr` for `traversable` structures ([#376](https://github.com/leanprover-community/mathlib/pull/376))

### [2019-02-06 09:59:29+01:00](https://github.com/leanprover-community/mathlib/commit/c82243a)
feat(analysis/normed_space): bounded linear maps with the operator norm form a normed space (closes [#680](https://github.com/leanprover-community/mathlib/pull/680))

### [2019-02-05 19:47:08](https://github.com/leanprover-community/mathlib/commit/d5a1b46)
to_nat_le_to_nat ([#685](https://github.com/leanprover-community/mathlib/pull/685))

### [2019-02-05 14:26:19-05:00](https://github.com/leanprover-community/mathlib/commit/9f79d2e)
fix(tactic/h_generalize): fix name resolution in h_generalize ([#688](https://github.com/leanprover-community/mathlib/pull/688))

### [2019-02-05 14:13:55-05:00](https://github.com/leanprover-community/mathlib/commit/a0d8ae1)
feat(tactic/replaceable): supplement `def_replacer` with attribute `replaceable`

### [2019-02-04 19:35:17-05:00](https://github.com/leanprover-community/mathlib/commit/178c09d)
feat(natural_isomorphism): componentwise isos are isos ([#671](https://github.com/leanprover-community/mathlib/pull/671))

### [2019-02-04 20:49:37](https://github.com/leanprover-community/mathlib/commit/9a8f1b0)
feat(algebra/group_power): gpow_add_one ([#683](https://github.com/leanprover-community/mathlib/pull/683))
* feat(algebra/group_power): gpow_add_one
* feat(data/nat//basic): int.coe_nat_abs

### [2019-02-04 19:00:17](https://github.com/leanprover-community/mathlib/commit/5395232)
remove simp on set_coe_eq_subtype ([#682](https://github.com/leanprover-community/mathlib/pull/682))

### [2019-02-04 10:43:58+01:00](https://github.com/leanprover-community/mathlib/commit/5e5f1e2)
fix(data/*/Ico): succ_top is too aggressive as a simp lemma ([#678](https://github.com/leanprover-community/mathlib/pull/678))

### [2019-02-03 22:31:10](https://github.com/leanprover-community/mathlib/commit/2539251)
feat(data/nat/cast): abs_cast

### [2019-02-03 17:00:41-05:00](https://github.com/leanprover-community/mathlib/commit/d01e523)
feat(category_theory/kleisli): monoids, const applicative functor and kleisli categories ([#660](https://github.com/leanprover-community/mathlib/pull/660))
* feat(category_theory/kleisli): monoids, const applicative functor and
kleisli categories

### [2019-02-03 17:01:45+01:00](https://github.com/leanprover-community/mathlib/commit/f5bd340)
cleanup(*): removing uses of bare `have` ([#676](https://github.com/leanprover-community/mathlib/pull/676))

### [2019-02-03 02:14:48-05:00](https://github.com/leanprover-community/mathlib/commit/544f35c)
Update README.md

### [2019-02-03 02:06:28](https://github.com/leanprover-community/mathlib/commit/b3e1e6f)
fix(README): update URL for build status icon ([#681](https://github.com/leanprover-community/mathlib/pull/681))

### [2019-02-03 01:08:36](https://github.com/leanprover-community/mathlib/commit/044b6fa)
feat(algebra/euclidean_domain): discrete field to euclidean domain ([#674](https://github.com/leanprover-community/mathlib/pull/674))

### [2019-02-02 19:04:50-05:00](https://github.com/leanprover-community/mathlib/commit/3109c4b)
chore(purge_olean.sh): a few small improvements ([#661](https://github.com/leanprover-community/mathlib/pull/661))
* purge empty directories
* Only print if an .olean is rm'd. This reduces the noise and reduces the
script run time.
* use git top-level dir to make the script relocatable
* only affect src and test dirs
* use bash instead of sed

### [2019-02-02 18:43:29-05:00](https://github.com/leanprover-community/mathlib/commit/8590ff2)
fix(functor_category): remove superfluous coercions ([#670](https://github.com/leanprover-community/mathlib/pull/670))

### [2019-02-02 18:42:36-05:00](https://github.com/leanprover-community/mathlib/commit/a09dc9f)
cleanup(category_theory/cones): tidying up, after making opposites work better ([#675](https://github.com/leanprover-community/mathlib/pull/675))

### [2019-02-02 18:41:09-05:00](https://github.com/leanprover-community/mathlib/commit/b084cfc)
fix(category_theory/equivalence): duplicated namespace prefix ([#669](https://github.com/leanprover-community/mathlib/pull/669))

### [2019-02-02 17:59:12-05:00](https://github.com/leanprover-community/mathlib/commit/e501d02)
fix(replacer): better flow control in replacer when tactic fails ([#673](https://github.com/leanprover-community/mathlib/pull/673))
The main consequence is better error reporting.

### [2019-02-02 18:42:12](https://github.com/leanprover-community/mathlib/commit/0393ccb)
feat(ring_theory/algebra): subalgebra_of_subring ([#664](https://github.com/leanprover-community/mathlib/pull/664))

### [2019-02-01 23:00:55-05:00](https://github.com/leanprover-community/mathlib/commit/f529870)
feat(data/nat/gcd/coprime): some easy simp lemmas ([#677](https://github.com/leanprover-community/mathlib/pull/677))

### [2019-02-02 01:41:01](https://github.com/leanprover-community/mathlib/commit/6925e4d)
feat(algebra/euclidean_domain): lcm ([#665](https://github.com/leanprover-community/mathlib/pull/665))

### [2019-02-01 20:07:31-05:00](https://github.com/leanprover-community/mathlib/commit/fb60145)
cleanup: replace `begin intros ...` with lambdas ([#672](https://github.com/leanprover-community/mathlib/pull/672))

### [2019-02-01 22:48:10](https://github.com/leanprover-community/mathlib/commit/ed0d24a)
feat(algebra/euclidean_domain): add quotient_zero axiom to euclidean_domain ([#666](https://github.com/leanprover-community/mathlib/pull/666))

### [2019-02-01 12:26:22+01:00](https://github.com/leanprover-community/mathlib/commit/d8f6dc4)
feat(src/tactic/explode): improve printing of references

### [2019-02-01 12:26:22+01:00](https://github.com/leanprover-community/mathlib/commit/a32de36)
feat(src/tactic/explode): add printing for conclusions of sintros

### [2019-02-01 12:26:22+01:00](https://github.com/leanprover-community/mathlib/commit/a08c9a7)
add printing for conclusions of sintros

### [2019-02-01 12:13:59+01:00](https://github.com/leanprover-community/mathlib/commit/c9e4f8e)
fix(tactic/inarith): fix denominator normalization of products

### [2019-02-01 12:13:31+01:00](https://github.com/leanprover-community/mathlib/commit/52adfd7)
feat(tactic,tactic/interactive): add set tactic, a variant of let

### [2019-02-01 09:53:51+01:00](https://github.com/leanprover-community/mathlib/commit/89bc63c)
feat(ring_theory/noetherian): is_noetherian_ring_range

### [2019-02-01 00:30:09](https://github.com/leanprover-community/mathlib/commit/8e381f6)
feat(ring_theory/algebra_operations): multiplication of submodules of an algebra ([#658](https://github.com/leanprover-community/mathlib/pull/658))