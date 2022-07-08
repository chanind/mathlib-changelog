### [2018-05-31 03:00:24-04:00](https://github.com/leanprover-community/mathlib/commit/b375264)
feat(computability/turing_machine): add TMs and reductions

### [2018-05-30 15:29:43-04:00](https://github.com/leanprover-community/mathlib/commit/bdd54ac)
feat(data/computablility): reduced partrec

### [2018-05-29 18:57:49-04:00](https://github.com/leanprover-community/mathlib/commit/00a2eb4)
feat(algebra/group_power): mul_two_nonneg

### [2018-05-29 17:20:24-04:00](https://github.com/leanprover-community/mathlib/commit/40bd947)
feat(computability/primrec): add traditional primrec definition
This shows that the pairing function with its square roots does not give any additional power.

### [2018-05-29 17:20:24-04:00](https://github.com/leanprover-community/mathlib/commit/5fea16e)
feat(category/basic): $< notation for reversed application

### [2018-05-29 15:48:54+02:00](https://github.com/leanprover-community/mathlib/commit/a2d2537)
feat(analysis/probability_mass_function): add bernoulli

### [2018-05-29 15:08:43+02:00](https://github.com/leanprover-community/mathlib/commit/4f9e951)
feat(analysis): add probability mass functions

### [2018-05-29 04:19:54-04:00](https://github.com/leanprover-community/mathlib/commit/eaa1b93)
feat(data.list.basic): forall_mem_singleton, forall_mem_append

### [2018-05-29 03:47:46-04:00](https://github.com/leanprover-community/mathlib/commit/a6be523)
feat(data/list/basic): map_erase, map_diff, map_union

### [2018-05-28 15:36:19+02:00](https://github.com/leanprover-community/mathlib/commit/0022068)
fix(tactics/wlog): allow union instead of disjunction; assume disjunction in strict associcated order; fix discharger

### [2018-05-28 14:30:41+02:00](https://github.com/leanprover-community/mathlib/commit/1dbd8c6)
feat(data/equiv): image, preimage under equivalences; simp rules for perm.val  ([#102](https://github.com/leanprover-community/mathlib/pull/102))

### [2018-05-27 22:50:42-04:00](https://github.com/leanprover-community/mathlib/commit/c53f9f1)
refactor(algebra/euclidean_domain): clean up proofs

### [2018-05-27 19:47:56-04:00](https://github.com/leanprover-community/mathlib/commit/9f0d1d8)
fix(analysis/limits): fix ambiguous import (fin)set.range

### [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/ad92a9b)
feat(algebra/group,...): add with_zero, with_one structures
other ways to add an element to an algebraic structure:
* Add a top or bottom to an order (with_top, with_bot)
* add a unit to a semigroup (with_zero, with_one)
* add a zero to a multiplicative semigroup (with_zero)
* add an infinite element to an additive semigroup (with_top)

### [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/431d997)
feat(nat/basic): mod_mod

### [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/4c1a826)
refactor(data/set/finite): use hypotheses for fintype assumptions
in simp rules

### [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/f563ac8)
chore(data/pnat): remove nat -> pnat coercion

### [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/b7012fb)
fix(tactic/norm_num): use norm_num to discharge simp goals

### [2018-05-25 16:15:06+02:00](https://github.com/leanprover-community/mathlib/commit/6811f13)
fix(data/list/perm): remove unused code ([#143](https://github.com/leanprover-community/mathlib/pull/143))

### [2018-05-25 05:57:39-04:00](https://github.com/leanprover-community/mathlib/commit/bcec475)
chore(leanpkg.toml): update version to 3.4.1

### [2018-05-25 05:55:41-04:00](https://github.com/leanprover-community/mathlib/commit/1991869)
feat(order/bounded_lattice): with_bot, with_top structures

### [2018-05-25 01:14:13-04:00](https://github.com/leanprover-community/mathlib/commit/94dc067)
refactor(order/lattice): move top/bot to bounded_lattice

### [2018-05-25 01:14:13-04:00](https://github.com/leanprover-community/mathlib/commit/4117ff4)
refactor(algebra/order_functions): reorganize new lemmas

### [2018-05-24 15:55:26+02:00](https://github.com/leanprover-community/mathlib/commit/9303bc0)
feat(analysis/ennreal): add further type class instances for nonnegative reals

### [2018-05-24 15:55:26+02:00](https://github.com/leanprover-community/mathlib/commit/02f8f48)
feat(analysis/nnreal): define the nonnegative reals
NB: This file has a lot in common with `ennreal.lean`, the extended nonnegative reals.

### [2018-05-24 09:39:41+02:00](https://github.com/leanprover-community/mathlib/commit/2c94668)
fix(data/fin): rename raise_fin -> fin.raise; simp lemmas for fin ([#138](https://github.com/leanprover-community/mathlib/pull/138))

### [2018-05-23 19:20:55+02:00](https://github.com/leanprover-community/mathlib/commit/d91a267)
fix(data/list/basic): protected list.sigma ([#140](https://github.com/leanprover-community/mathlib/pull/140))

### [2018-05-23 19:20:25+02:00](https://github.com/leanprover-community/mathlib/commit/94a4b07)
doc(docs/extras): some notes on well founded recursion ([#127](https://github.com/leanprover-community/mathlib/pull/127))

### [2018-05-23 19:16:42+02:00](https://github.com/leanprover-community/mathlib/commit/23bd3f2)
doc(docs/extra/simp): adding reference to simpa ([#106](https://github.com/leanprover-community/mathlib/pull/106))

### [2018-05-23 18:54:35+02:00](https://github.com/leanprover-community/mathlib/commit/add172d)
chore(tactic/default): move split_ifs import to tactic.interactive

### [2018-05-23 18:54:35+02:00](https://github.com/leanprover-community/mathlib/commit/d442907)
fix(tactic/split_if): clarify behavior

### [2018-05-23 18:54:35+02:00](https://github.com/leanprover-community/mathlib/commit/509934f)
feat(tactic/split_ifs): add if-splitter

### [2018-05-23 17:29:32+02:00](https://github.com/leanprover-community/mathlib/commit/f458eef)
feat(analysis/topology): add tendsto and continuity rules for big operators

### [2018-05-23 17:17:56+02:00](https://github.com/leanprover-community/mathlib/commit/a54be05)
feat(analysis/topology): add continuity rules for supr, Sup, and pi spaces

### [2018-05-23 15:22:09+02:00](https://github.com/leanprover-community/mathlib/commit/cff886b)
feat(data/finset): max and min

### [2018-05-23 15:22:09+02:00](https://github.com/leanprover-community/mathlib/commit/d1ea272)
feat(data/option): lift_or_get

### [2018-05-22 05:26:41-04:00](https://github.com/leanprover-community/mathlib/commit/d62bf56)
feat(computability/halting): halting problem

### [2018-05-21 11:44:37-04:00](https://github.com/leanprover-community/mathlib/commit/f0bcba5)
feat(computability/partrec_code): Kleene normal form theorem
among other things

### [2018-05-21 11:41:40-04:00](https://github.com/leanprover-community/mathlib/commit/fe5c86c)
fix(tactic/interactive): fix congr bug, rename congr_n to congr'

### [2018-05-20 06:37:12-04:00](https://github.com/leanprover-community/mathlib/commit/741469a)
fix(tactic/interactive): make rcases handle nested constructors correctly
The line changed by this commit was wrong because `k` might contain
further constructors, which also need to be "inverted".
Fixes [#56](https://github.com/leanprover-community/mathlib/pull/56).
* doc(tactic): Internal documentation for rcases
* style(tactic/rcases): eliminate an unused recursive parameter
* style(*): use rcases more

### [2018-05-19 21:28:26-04:00](https://github.com/leanprover-community/mathlib/commit/fc20442)
feat(computability/partrec): partial recursion, Godel numbering

### [2018-05-18 05:14:19-04:00](https://github.com/leanprover-community/mathlib/commit/38d5536)
feat(computability/partrec): starting work on partial recursive funcs

### [2018-05-18 05:10:04-04:00](https://github.com/leanprover-community/mathlib/commit/92feaf9)
feat(computability/primrec): list definitions are primrec

### [2018-05-17 04:23:08-04:00](https://github.com/leanprover-community/mathlib/commit/e017f0f)
feat(data/computability): primrec, denumerable

### [2018-05-16 10:16:22+02:00](https://github.com/leanprover-community/mathlib/commit/fe7d573)
refactor(data/set/enumerate): proof enumeration_inj using wlog

### [2018-05-16 10:16:22+02:00](https://github.com/leanprover-community/mathlib/commit/d8c33e8)
feat(tactic): generalize wlog to support multiple variables and cases, allow to provide case rule

### [2018-05-10 15:29:47+02:00](https://github.com/leanprover-community/mathlib/commit/2cd640a)
feat(data/multiset): add sections

### [2018-05-10 15:29:29+02:00](https://github.com/leanprover-community/mathlib/commit/62833ca)
feat(data/multiset): add relator

### [2018-05-10 12:12:25+02:00](https://github.com/leanprover-community/mathlib/commit/d10c3bb)
fix(order/complete_boolean_algebra): replace finish proof by simp (finish was very slow)

### [2018-05-09 06:19:46-04:00](https://github.com/leanprover-community/mathlib/commit/fc6f57a)
feat(data/list/basic): list.forall2, list.sections

### [2018-05-09 06:04:38-04:00](https://github.com/leanprover-community/mathlib/commit/42f5ea0)
feat(data/semiquot): semiquotient types

### [2018-05-09 06:04:38-04:00](https://github.com/leanprover-community/mathlib/commit/b31c30d)
refactor(logic/function): constructive proof of cantor_injective

### [2018-05-09 11:41:31+02:00](https://github.com/leanprover-community/mathlib/commit/54df4d9)
feat(linear_algebra/multivariate_polynomial): change order of eval arguments; show that eval is ring homomorphism
(closes https://github.com/leanprover/mathlib/pull/134)

### [2018-05-09 10:46:03+02:00](https://github.com/leanprover-community/mathlib/commit/b5eddd8)
fix(data/set/basic): mark subset.refl as @[refl]

### [2018-05-04 16:10:27+02:00](https://github.com/leanprover-community/mathlib/commit/e4c64fd)
feat(tactic/mk_iff_of_inductive_prop): add tactic to represent inductives using logical connectives

### [2018-05-03 13:46:52-04:00](https://github.com/leanprover-community/mathlib/commit/fa7a180)
feat(tactic/solve_by_elim): make solve_by_elim easier to use correctly ([#131](https://github.com/leanprover-community/mathlib/pull/131))

### [2018-05-03 14:41:35+02:00](https://github.com/leanprover-community/mathlib/commit/ef43edf)
feat(data/finset): add list.to_finset theorems

### [2018-05-03 11:23:10+02:00](https://github.com/leanprover-community/mathlib/commit/02c2b56)
feat(analysis/topology/topological_space): t2 instances for constructions of limit type