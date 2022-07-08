### [2019-01-30 18:20:41-05:00](https://github.com/leanprover-community/mathlib/commit/50a03f7)
chore(test): fix test directory structure

### [2019-01-30 18:20:41-05:00](https://github.com/leanprover-community/mathlib/commit/12be0aa)
refactor(category_theory/instances): rename `examples` to `instances`

### [2019-01-30 17:15:23-05:00](https://github.com/leanprover-community/mathlib/commit/829b49b)
chore(.travis.yml): use git clean to clean out untracked files ([#659](https://github.com/leanprover-community/mathlib/pull/659))
* chore(.travis.yml): use git clean to clean out untracked files and delete more obsolete olean files
PR [#641](https://github.com/leanprover-community/mathlib/pull/641) involved renaming a directory. The old directory was still
present in the cache, and in this situation `git status` lists the
directory as a whole as untracked, so the grep did not find any
`.lean` files.

### [2019-01-30 17:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/0eb9db6)
chore(linear_algebra/multivariate_polynomial): move rename to the right place

### [2019-01-30 16:37:18+01:00](https://github.com/leanprover-community/mathlib/commit/a480160)
feat(data/polynomial): generalize theorems from nonzero_comm_ring to comm_ring ([#653](https://github.com/leanprover-community/mathlib/pull/653))

### [2019-01-30 16:32:15+01:00](https://github.com/leanprover-community/mathlib/commit/065f083)
feat(group_theory): monoid / group closure of union

### [2019-01-30 16:16:31+01:00](https://github.com/leanprover-community/mathlib/commit/f7b9d6b)
refactor(data/equiv/algebra): mv_polynomial mv_polynomial (β ⊕ γ) α ≃r mv_polynomial β (mv_polynomial γ α)

### [2019-01-30 10:26:08+01:00](https://github.com/leanprover-community/mathlib/commit/aa944bf)
feat(analysis/exponential): real powers, `cpow_nat_inv_pow` ([#647](https://github.com/leanprover-community/mathlib/pull/647))

### [2019-01-30 09:57:02+01:00](https://github.com/leanprover-community/mathlib/commit/626489a)
feat(topology/metric_space): diameter of a set in metric spaces ([#651](https://github.com/leanprover-community/mathlib/pull/651))

### [2019-01-30 09:55:58+01:00](https://github.com/leanprover-community/mathlib/commit/ef35c6c)
second countability criteria in metric spaces

### [2019-01-30 09:54:34+01:00](https://github.com/leanprover-community/mathlib/commit/30649f5)
cleanup instances/ennreal

### [2019-01-30 09:49:08+01:00](https://github.com/leanprover-community/mathlib/commit/afa535e)
feat(ring_theory/polynomial): hilbert basis theorem

### [2019-01-29 19:13:38+01:00](https://github.com/leanprover-community/mathlib/commit/860eba6)
chore(.): change occurrences of tests directory to test

### [2019-01-29 19:07:10+01:00](https://github.com/leanprover-community/mathlib/commit/247dcb2)
feat(linear_algebra): rules for kernel of `of_le`, `cod_restrict`, and `pair`

### [2019-01-29 18:32:34+01:00](https://github.com/leanprover-community/mathlib/commit/4fb6c7d)
chore(test): rename the test directory so that `leanpkg` will find it

### [2019-01-29 17:18:52+01:00](https://github.com/leanprover-community/mathlib/commit/fc529b6)
feat(data/complex/basic): of_real_fpow ([#640](https://github.com/leanprover-community/mathlib/pull/640))

### [2019-01-29 17:15:53+01:00](https://github.com/leanprover-community/mathlib/commit/d7d90fa)
docs(tactic/monotonicity/interactive): fix `mono` documentation [ci-skip]

### [2019-01-29 17:15:30+01:00](https://github.com/leanprover-community/mathlib/commit/0924ac0)
fix build

### [2019-01-29 17:15:30+01:00](https://github.com/leanprover-community/mathlib/commit/a0e2de9)
refactor(*): use decidable_linear_order.lift

### [2019-01-29 17:15:15+01:00](https://github.com/leanprover-community/mathlib/commit/7cfcce3)
feat(data/equiv/algebra): ring equiv for mv_polynomial

### [2019-01-29 13:20:33+01:00](https://github.com/leanprover-community/mathlib/commit/54f4b29)
feat(tactic/interactive.lean): clear_aux_decl

### [2019-01-29 13:20:13+01:00](https://github.com/leanprover-community/mathlib/commit/8faf8df)
feat(field_theory/splitting_field): splits predicate on polynomials

### [2019-01-29 13:17:09+01:00](https://github.com/leanprover-community/mathlib/commit/8ee4f2d)
move continuous_of_lipschitz around

### [2019-01-29 11:39:45+01:00](https://github.com/leanprover-community/mathlib/commit/83edba4)
feat(measure_theory): integral is equal and monotone almost-everywhere and for measurable functions it is a.e. strict at 0

### [2019-01-29 09:37:59+01:00](https://github.com/leanprover-community/mathlib/commit/cd41aca)
Move tendsto_div to a better place

### [2019-01-28 20:15:38+01:00](https://github.com/leanprover-community/mathlib/commit/042c290)
refactor(category_theory/opposites): Make `opposite` irreducible

### [2019-01-28 20:11:16+01:00](https://github.com/leanprover-community/mathlib/commit/d1b7d91)
feat(category_theory/limits/cones): forgetful functors

### [2019-01-28 19:59:32+01:00](https://github.com/leanprover-community/mathlib/commit/b39d6d8)
feat(*) refactor module

### [2019-01-28 19:52:47+01:00](https://github.com/leanprover-community/mathlib/commit/fd3e5a1)
fix(topology/instances/ennreal): fix merge

### [2019-01-28 19:34:07+01:00](https://github.com/leanprover-community/mathlib/commit/e62c534)
add ennreal.to_real

### [2019-01-28 17:14:45+01:00](https://github.com/leanprover-community/mathlib/commit/8572c6b)
feat(topology): prove continuity of nndist and edist; `ball a r` is a metric space

### [2019-01-28 10:14:51+01:00](https://github.com/leanprover-community/mathlib/commit/afa31be)
refactor(linear_algebra/direct_sum_module): move to algebra/direct_sum

### [2019-01-28 08:02:17+01:00](https://github.com/leanprover-community/mathlib/commit/7199bb3)
chore(linear_algebra/dimension): simplify dim_add_le_dim_add_dim

### [2019-01-27 22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/038e0b2)
feat(ring_theory/algebra): remove out_param

### [2019-01-27 22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/af7a7ee)
feat(ring_theory/algebra): remove of_core

### [2019-01-27 22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/79ba61c)
feat(ring_theory/algebra): make algebra a class

### [2019-01-27 22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/a0b6cae)
feat(ring_theory/algebra): define algebra over a commutative ring

### [2019-01-27 22:44:50+01:00](https://github.com/leanprover-community/mathlib/commit/1d2eda7)
feat(category_theory/isomorphism): as_iso
Also clean up some proofs.

### [2019-01-27 22:43:45+01:00](https://github.com/leanprover-community/mathlib/commit/ccd895f)
feat(category_theory/types): conversions between iso and equiv

### [2019-01-27 22:42:53+01:00](https://github.com/leanprover-community/mathlib/commit/d074b51)
refactor(category_theory/concrete_category): move `bundled` to own file

### [2019-01-27 22:40:37+01:00](https://github.com/leanprover-community/mathlib/commit/50398e5)
feat(category_theory/full_subcategory): induced categories

### [2019-01-27 22:37:46+01:00](https://github.com/leanprover-community/mathlib/commit/19c2f68)
feat(analysis/exponential): complex powers

### [2019-01-27 22:33:10+01:00](https://github.com/leanprover-community/mathlib/commit/c057758)
feat(data/complex/exponential): exp_eq_one_iff

### [2019-01-27 22:32:41+01:00](https://github.com/leanprover-community/mathlib/commit/db69173)
refactor(algebra/field_power): notation for fpow

### [2019-01-27 22:31:44+01:00](https://github.com/leanprover-community/mathlib/commit/d359aa8)
feat(order/conditionally_complete_lattice): cinfi_const ([#634](https://github.com/leanprover-community/mathlib/pull/634))

### [2019-01-27 22:30:58+01:00](https://github.com/leanprover-community/mathlib/commit/06eba7f)
update authors on expr.lean (I don't know who's responsible for what)

### [2019-01-27 22:30:58+01:00](https://github.com/leanprover-community/mathlib/commit/be5dba9)
fix(tactic/norm_num): only check core norm_num output up to numeral structure

### [2019-01-27 22:30:58+01:00](https://github.com/leanprover-community/mathlib/commit/daa7684)
refactor(tactic/basic): move non-tactic decls to meta folder

### [2019-01-27 22:28:46+01:00](https://github.com/leanprover-community/mathlib/commit/6781ff0)
feat(tactic/linarith): prefer type of goal if there are multiple types

### [2019-01-27 22:28:46+01:00](https://github.com/leanprover-community/mathlib/commit/8affebd)
fix(tactic/linarith): remove unused code

### [2019-01-27 22:28:46+01:00](https://github.com/leanprover-community/mathlib/commit/92508dc)
fix(tactic/linarith): properly handle problems with inequalities in multiple types
When problems have inequalities over multiple types, it's almost safe to process everything at once, since none of the
variables overlap. But linarith deals with constants by homogenizing them and the "constant" variables do overlap.
This fix creates one call to linarith for each type that appears in a hypothesis.

### [2019-01-27 00:35:53-05:00](https://github.com/leanprover-community/mathlib/commit/84d1c45)
feat(tactic/match-stub): use Lean holes to create a pattern matching skeleton ([#630](https://github.com/leanprover-community/mathlib/pull/630))
* feat(tactic/match-stub): use Lean holes to create a pattern matching skeleton
* feat(tactic/match-stub): add hole for listing relevant constructors

### [2019-01-25 17:50:12+01:00](https://github.com/leanprover-community/mathlib/commit/315a642)
feat(measure_theory): add Hahn decomposition

### [2019-01-24 16:02:42+01:00](https://github.com/leanprover-community/mathlib/commit/ed2ab1a)
feat(measure_theory): measures form a complete lattice

### [2019-01-24 09:18:32+01:00](https://github.com/leanprover-community/mathlib/commit/4aacae3)
feat(data/equiv/algebra): instances for transporting algebra across an equiv ([#618](https://github.com/leanprover-community/mathlib/pull/618))

### [2019-01-24 09:17:37+01:00](https://github.com/leanprover-community/mathlib/commit/c49e89d)
feat(category_theory/adjunction): definitions, basic proofs, and examples ([#619](https://github.com/leanprover-community/mathlib/pull/619))

### [2019-01-23 16:35:39+01:00](https://github.com/leanprover-community/mathlib/commit/0e6c358)
feat(set_theory/cardinal): more lemmas on cardinality ([#595](https://github.com/leanprover-community/mathlib/pull/595))

### [2019-01-23 14:24:28+01:00](https://github.com/leanprover-community/mathlib/commit/9be8905)
refactor(topology/sequences): restructure proofs

### [2019-01-23 14:24:12+01:00](https://github.com/leanprover-community/mathlib/commit/4018daf)
feat(topology): sequences, sequential spaces, and sequential continuity (closes [#440](https://github.com/leanprover-community/mathlib/pull/440))
Co-Authored-By: Reid Barton <rwbarton@gmail.com>

### [2019-01-23 13:24:31+01:00](https://github.com/leanprover-community/mathlib/commit/c06fb67)
refactor(category_theory/category): split off has_hom
This gives a little more flexibility when defining a category,
which will be used for opposite categories. It should also be
useful for defining the free category on a graph.

### [2019-01-23 12:52:40+01:00](https://github.com/leanprover-community/mathlib/commit/2c95d2a)
maintain(vscode): add ruler at 100 in editor

### [2019-01-23 12:52:40+01:00](https://github.com/leanprover-community/mathlib/commit/b2700dd)
maintain(.vscode): add default settings

### [2019-01-23 12:45:23+01:00](https://github.com/leanprover-community/mathlib/commit/6da9b21)
le_induction

### [2019-01-23 12:38:43+01:00](https://github.com/leanprover-community/mathlib/commit/60efaec)
chore(topology): move contraction_mapping to metric_space/lipschitz

### [2019-01-23 11:48:36+01:00](https://github.com/leanprover-community/mathlib/commit/5317b59)
refactor(contraction_mapping): add more proves about Lipschitz continuous functions; cleanup proofs

### [2019-01-23 11:48:20+01:00](https://github.com/leanprover-community/mathlib/commit/96198b9)
feat(contraction_mapping): proof the Banach fixed-point theorem (closes [#553](https://github.com/leanprover-community/mathlib/pull/553))

### [2019-01-23 11:43:23+01:00](https://github.com/leanprover-community/mathlib/commit/8a0fd0b)
feat(order): add order instances for prod

### [2019-01-23 08:09:04+01:00](https://github.com/leanprover-community/mathlib/commit/2ae2cf0)
feat(linear_algebra/multivariate_polynomial): C_mul'

### [2019-01-22 17:23:23-05:00](https://github.com/leanprover-community/mathlib/commit/8d44fee)
style(category_theory): adjust precedence of ⥤ ([#616](https://github.com/leanprover-community/mathlib/pull/616))

### [2019-01-22 17:21:55-05:00](https://github.com/leanprover-community/mathlib/commit/c9a0b33)
refactor(category_theory/fully_faithful): move preimage_id ([#615](https://github.com/leanprover-community/mathlib/pull/615))

### [2019-01-22 16:49:24+01:00](https://github.com/leanprover-community/mathlib/commit/edfa206)
feat(linear_algebra/dimension): more dimension theorems; rank of a linear map

### [2019-01-22 16:02:10+01:00](https://github.com/leanprover-community/mathlib/commit/6e4c9ba)
feat(linear_algebra/linear_combination): lc lifts vector spaces

### [2019-01-22 16:00:18+01:00](https://github.com/leanprover-community/mathlib/commit/d5a302f)
chore(linear_algebra): rename file lc to linear_combination

### [2019-01-22 15:32:49+01:00](https://github.com/leanprover-community/mathlib/commit/7baf093)
feat(data/list,data/multiset,data/finset): add Ico intervals (closes [#496](https://github.com/leanprover-community/mathlib/pull/496))

### [2019-01-21 20:02:01-05:00](https://github.com/leanprover-community/mathlib/commit/3dc9935)
fix(tactic/instance_stub): extend the applicability of instance_stub ([#612](https://github.com/leanprover-community/mathlib/pull/612))

### [2019-01-21 11:12:50+01:00](https://github.com/leanprover-community/mathlib/commit/bc163a6)
fix(.travis.yml): produce mathlib.txt only from src/

### [2019-01-20 22:50:48-05:00](https://github.com/leanprover-community/mathlib/commit/c1e594b)
feat(meta, logic, tactic): lean 3.4.2: migrate coinductive_predicates, transfer, relator ([#610](https://github.com/leanprover-community/mathlib/pull/610))

### [2019-01-20 20:42:15-05:00](https://github.com/leanprover-community/mathlib/commit/2c5bc21)
feat(topology/emetric_space): basic facts for emetric spaces ([#608](https://github.com/leanprover-community/mathlib/pull/608))

### [2019-01-19 18:43:24-05:00](https://github.com/leanprover-community/mathlib/commit/fa2e399)
feat(topology/bounded_continuous_function): constructor in normed groups ([#607](https://github.com/leanprover-community/mathlib/pull/607))

### [2019-01-18 19:50:09-05:00](https://github.com/leanprover-community/mathlib/commit/3fcba7d)
feat(logic/basic): add class 'unique' for uniquely inhabited types ([#605](https://github.com/leanprover-community/mathlib/pull/605))

### [2019-01-18 16:30:23-05:00](https://github.com/leanprover-community/mathlib/commit/41b3fdd)
feat(topology/real): bounded iff bounded below above ([#606](https://github.com/leanprover-community/mathlib/pull/606))

### [2019-01-18 15:36:40+01:00](https://github.com/leanprover-community/mathlib/commit/eb1253f)
feat(measure_theory): add Giry monad

### [2019-01-18 14:10:04+01:00](https://github.com/leanprover-community/mathlib/commit/739d28a)
refactor(ring_theory/multiplicity): replace padic_val with multiplicity ([#495](https://github.com/leanprover-community/mathlib/pull/495))

### [2019-01-18 13:28:37+01:00](https://github.com/leanprover-community/mathlib/commit/6144710)
feat(measure_theory): add equivalence of measurable spaces

### [2019-01-18 13:26:32+01:00](https://github.com/leanprover-community/mathlib/commit/b352d2c)
refactor(topology): topological_space.induced resembles set.image; second_countable_topology on subtypes; simplify filter.map_comap

### [2019-01-18 13:20:03+01:00](https://github.com/leanprover-community/mathlib/commit/6b6b04a)
feat(order/complete_lattice): add rules for supr/infi under image and under propositions

### [2019-01-18 11:13:09+01:00](https://github.com/leanprover-community/mathlib/commit/f0f06ca)
refactor(*): analysis reorganization ([#598](https://github.com/leanprover-community/mathlib/pull/598))
* split `measure_theory` and `topology` out of analysis
* add `instances` sub directories for theories around type class instances

### [2019-01-17 19:21:33-05:00](https://github.com/leanprover-community/mathlib/commit/c1f162c)
fix(tactic/linarith): don't reject expressions with division by variables ([#604](https://github.com/leanprover-community/mathlib/pull/604))
norm_hyp_aux should have succeeded (without changing the type of h') in the case where lhs contains 1/x. But mk_single_comp_zero_pf is too clever when given the coeff 1. norm_hyp_aux will still do unnecessary work when it finds e.g. 1/(2*x), but shouldn't fail.

### [2019-01-17 14:37:38-05:00](https://github.com/leanprover-community/mathlib/commit/ae610a0)
feat(ring_theory/adjoin_root): adjoin roots to polynomials ([#603](https://github.com/leanprover-community/mathlib/pull/603))

### [2019-01-16 08:50:38-05:00](https://github.com/leanprover-community/mathlib/commit/5c37507)
doc(elan.md): fix msys2 setup ([#594](https://github.com/leanprover-community/mathlib/pull/594)) [ci-skip]
For me, adding the suggested line to .profile did not change my path, even after restarting the terminal.
Moreover, elan is installed in $USERPROFILE/.elan/bin, not in $HOME/.elan/bin.
Adding $USERPROFILE/.elan/bin to the path did not work for me, so I give the full path.

### [2019-01-16 08:33:19-05:00](https://github.com/leanprover-community/mathlib/commit/5dd9998)
doc(docs/tactics): document `convert` ([#601](https://github.com/leanprover-community/mathlib/pull/601)) [ci-skip]

### [2019-01-16 08:14:44-05:00](https://github.com/leanprover-community/mathlib/commit/ab5849e)
style(category_theory/opposites): increase binding power of ᵒᵖ ([#600](https://github.com/leanprover-community/mathlib/pull/600))

### [2019-01-15 17:43:36-05:00](https://github.com/leanprover-community/mathlib/commit/024da40)
refactor(logic/schroeder_bernstein): move to set_theory/ ([#599](https://github.com/leanprover-community/mathlib/pull/599))

### [2019-01-15 12:05:23-05:00](https://github.com/leanprover-community/mathlib/commit/d4f80f6)
refactor(*): Try again moving everything to src ([#597](https://github.com/leanprover-community/mathlib/pull/597))

### [2019-01-15 10:51:04-05:00](https://github.com/leanprover-community/mathlib/commit/78f1949)
refactor(*): move everything into `src` ([#583](https://github.com/leanprover-community/mathlib/pull/583))

### [2019-01-15 11:15:57+01:00](https://github.com/leanprover-community/mathlib/commit/0c71016)
feat(logic/basic): nonempty.map

### [2019-01-14 14:48:02+01:00](https://github.com/leanprover-community/mathlib/commit/667dcf3)
feat(group_theory/sylow): first sylow theorem (closes [#591](https://github.com/leanprover-community/mathlib/pull/591))

### [2019-01-14 14:05:58+01:00](https://github.com/leanprover-community/mathlib/commit/f63fb54)
doc(tactic/simpa): rewrite simpa doc

### [2019-01-14 13:34:42+01:00](https://github.com/leanprover-community/mathlib/commit/49c059a)
refactor(analysis): add metric namespace
combines changes from @sgouezel, @PatrickMassot, and @digama0

### [2019-01-14 13:34:16+01:00](https://github.com/leanprover-community/mathlib/commit/2f9f3df)
doc(tactic/simpa): update simpa documentation

### [2019-01-14 13:34:16+01:00](https://github.com/leanprover-community/mathlib/commit/263e8a0)
fix(tactic/simpa): only try given expression in "simpa using"

### [2019-01-14 12:27:12+01:00](https://github.com/leanprover-community/mathlib/commit/4de9682)
fix(PULL_REQUEST_TEMPLATE): use absolute urls
The relative urls do not resolve correctly.

### [2019-01-14 12:03:28+01:00](https://github.com/leanprover-community/mathlib/commit/c7f13fd)
feat(.vscode): add copyright snippet

### [2019-01-13 19:02:05+01:00](https://github.com/leanprover-community/mathlib/commit/b03c0aa)
feat(group_theory/sylow): Cauchy's theorem ([#458](https://github.com/leanprover-community/mathlib/pull/458))
* feat(group_theory): adding add_subgroup and add_submonoid
* feat(data/list/basic): rotate a list

### [2019-01-12 10:19:18-05:00](https://github.com/leanprover-community/mathlib/commit/dc6c38a)
fix(field_theory/subfield): is_subfield should be a Prop ([#588](https://github.com/leanprover-community/mathlib/pull/588))

### [2019-01-11 19:01:39+01:00](https://github.com/leanprover-community/mathlib/commit/e61a464)
feat(ring_theory/euclidean_domain): add more specific Euclidean domain stuff ([#527](https://github.com/leanprover-community/mathlib/pull/527))

### [2019-01-11 18:59:19+01:00](https://github.com/leanprover-community/mathlib/commit/5c323cd)
feat(category_theory): over and under categories  ([#549](https://github.com/leanprover-community/mathlib/pull/549))

### [2019-01-11 18:17:13+01:00](https://github.com/leanprover-community/mathlib/commit/c19b4be)
feat(meta/rb_map): add some monadic filtering

### [2019-01-11 17:06:02+01:00](https://github.com/leanprover-community/mathlib/commit/7a9b2e4)
Update PULL_REQUEST_TEMPLATE.md

### [2019-01-11 17:04:58+01:00](https://github.com/leanprover-community/mathlib/commit/6516c34)
doc(README): elect new maintainers

### [2019-01-11 15:35:42+01:00](https://github.com/leanprover-community/mathlib/commit/4f3f86d)
chore(ring_theory/subring): remove unused import

### [2019-01-11 11:37:17+01:00](https://github.com/leanprover-community/mathlib/commit/4578796)
feat(data/polynomial): various lemmas about degree and monic and coeff

### [2019-01-10 15:26:30-05:00](https://github.com/leanprover-community/mathlib/commit/b1684fe)
fix(principal_ideal_domain): correct spelling mistake ([#582](https://github.com/leanprover-community/mathlib/pull/582))

### [2019-01-10 12:11:24+01:00](https://github.com/leanprover-community/mathlib/commit/6e97721)
refactor(principal_ideal_domain): simplify proof of PID -> UFD

### [2019-01-10 12:11:24+01:00](https://github.com/leanprover-community/mathlib/commit/f5bf277)
refactor(unique_factorization_domain): simplify definition of UFD

### [2019-01-10 09:46:28+01:00](https://github.com/leanprover-community/mathlib/commit/8b66ebd)
functions and cardinality ([#556](https://github.com/leanprover-community/mathlib/pull/556))

### [2019-01-09 10:08:23+01:00](https://github.com/leanprover-community/mathlib/commit/f488635)
chore(tactic/monotonicity/interactive) use derive for has_reflect ([#578](https://github.com/leanprover-community/mathlib/pull/578))

### [2019-01-09 10:07:56+01:00](https://github.com/leanprover-community/mathlib/commit/af735a5)
feat(field_theory/finite): field_of_integral_domain ([#579](https://github.com/leanprover-community/mathlib/pull/579))

### [2019-01-09 09:48:35+01:00](https://github.com/leanprover-community/mathlib/commit/d0532c1)
feat(data/polynomial): lemmas about map ([#530](https://github.com/leanprover-community/mathlib/pull/530))

### [2019-01-05 16:41:07-05:00](https://github.com/leanprover-community/mathlib/commit/2e63635)
feat(group_theory/subgroup): simple groups ([#572](https://github.com/leanprover-community/mathlib/pull/572))

### [2019-01-05 16:38:38-05:00](https://github.com/leanprover-community/mathlib/commit/d19c9bc)
feat(data/fintype): decidable_left_inverse_fintype ([#575](https://github.com/leanprover-community/mathlib/pull/575))

### [2019-01-05 16:37:57-05:00](https://github.com/leanprover-community/mathlib/commit/395aadd)
feat(group_theory/sign): sign_surjective ([#576](https://github.com/leanprover-community/mathlib/pull/576))

### [2019-01-05 14:19:05-05:00](https://github.com/leanprover-community/mathlib/commit/b9c5eb0)
feat(ring_theory/multiplicity): multiplicity of elements of a ring ([#523](https://github.com/leanprover-community/mathlib/pull/523))

### [2019-01-05 14:17:10-05:00](https://github.com/leanprover-community/mathlib/commit/bc96eca)
feat(group_theory/quotient_group): quotient_ker_equiv_range ([#574](https://github.com/leanprover-community/mathlib/pull/574))

### [2019-01-05 14:13:47-05:00](https://github.com/leanprover-community/mathlib/commit/3ff5e93)
feat(data/polynomial): polynomials over a field are a normalization domain ([#560](https://github.com/leanprover-community/mathlib/pull/560))

### [2019-01-05 14:12:49-05:00](https://github.com/leanprover-community/mathlib/commit/87bf618)
feat(data/polynomial): C_neg and C_sub ([#561](https://github.com/leanprover-community/mathlib/pull/561))

### [2019-01-05 14:12:25-05:00](https://github.com/leanprover-community/mathlib/commit/78d0ebf)
feat(data/multiset): prod_hom and exists_mem_of_rel_of_mem ([#562](https://github.com/leanprover-community/mathlib/pull/562))

### [2019-01-05 14:11:58-05:00](https://github.com/leanprover-community/mathlib/commit/4e509a8)
feat(ring_theory/noetherian): irreducible_induction_on ([#563](https://github.com/leanprover-community/mathlib/pull/563))

### [2019-01-05 14:10:24-05:00](https://github.com/leanprover-community/mathlib/commit/ea0ff05)
doc(category_theory): update `category_theory` documentation ([#564](https://github.com/leanprover-community/mathlib/pull/564)) [ci-skip]

### [2019-01-05 14:09:18-05:00](https://github.com/leanprover-community/mathlib/commit/33df7ec)
feat(data/nat/enat): has_well_founded for enat ([#565](https://github.com/leanprover-community/mathlib/pull/565))

### [2019-01-05 14:06:39-05:00](https://github.com/leanprover-community/mathlib/commit/4bacdf2)
feat(logic/basic): inhabited_of_nonempty with instance parameter ([#566](https://github.com/leanprover-community/mathlib/pull/566))

### [2019-01-05 14:05:50-05:00](https://github.com/leanprover-community/mathlib/commit/125feb6)
feat(data/multiset): forall_of_pairwise ([#569](https://github.com/leanprover-community/mathlib/pull/569))

### [2019-01-05 14:05:30-05:00](https://github.com/leanprover-community/mathlib/commit/da6ec21)
feat(algebra/group): is_conj_one_right ([#570](https://github.com/leanprover-community/mathlib/pull/570))

### [2019-01-05 14:05:06-05:00](https://github.com/leanprover-community/mathlib/commit/a32fa18)
feat(data/finset): finset.card_eq_one ([#571](https://github.com/leanprover-community/mathlib/pull/571))

### [2019-01-05 04:49:24-05:00](https://github.com/leanprover-community/mathlib/commit/40fa9ad)
fix(analysis/measure_theory): fix build

### [2019-01-04 20:28:21-05:00](https://github.com/leanprover-community/mathlib/commit/93a330e)
fix(data/real/cau_seq_filter): fix build

### [2019-01-04 19:43:43-05:00](https://github.com/leanprover-community/mathlib/commit/19e7b1f)
feat(analysis/topology): Bounded continuous functions ([#464](https://github.com/leanprover-community/mathlib/pull/464))

### [2019-01-02 10:12:17-05:00](https://github.com/leanprover-community/mathlib/commit/dcd0466)
feat(analysis/topology): complete sets, minor modifications ([#557](https://github.com/leanprover-community/mathlib/pull/557))

### [2019-01-02 08:57:30-05:00](https://github.com/leanprover-community/mathlib/commit/f59f5d5)
feat(data/real/ennreal): minor additions to ennreal ([#558](https://github.com/leanprover-community/mathlib/pull/558))

### [2019-01-02 06:39:37-05:00](https://github.com/leanprover-community/mathlib/commit/50583b9)
feat(algebra/order): additional theorems on cmp