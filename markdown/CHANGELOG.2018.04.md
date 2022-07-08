### [2018-04-29 01:27:12-04:00](https://github.com/leanprover-community/mathlib/commit/a97101d)
fix(docs/naming): use names in use ([#122](https://github.com/leanprover-community/mathlib/pull/122))

### [2018-04-26 18:29:10+02:00](https://github.com/leanprover-community/mathlib/commit/48485a2)
refactor(logic/relation,group_theory/free_group): add theory for reflextive/transitive relations & use them for the free group reduction

### [2018-04-25 14:35:58+02:00](https://github.com/leanprover-community/mathlib/commit/5df2ee7)
style(group_theory): move free_group from algebra to group_theory

### [2018-04-25 14:28:21+02:00](https://github.com/leanprover-community/mathlib/commit/716decc)
feat(algebra): add free groups ([#89](https://github.com/leanprover-community/mathlib/pull/89))

### [2018-04-25 13:44:07+02:00](https://github.com/leanprover-community/mathlib/commit/e6264eb)
feat(order/conditionally_complete_lattice): add instance complete_linear_order -> conditionally_complete_linear_order; add cSup/cInf_interval

### [2018-04-25 13:06:49+02:00](https://github.com/leanprover-community/mathlib/commit/bf04127)
feat(order): add liminf and limsup over filters (c.f. Sébastien Gouëzel's [#115](https://github.com/leanprover-community/mathlib/pull/115))

### [2018-04-24 22:18:49-04:00](https://github.com/leanprover-community/mathlib/commit/78d28c5)
fix(*): update to lean

### [2018-04-24 21:11:29-04:00](https://github.com/leanprover-community/mathlib/commit/44271cf)
feat(tactic/interactive): add `clean` tactic
for removing identity junk and annotations added to terms by common tactics like dsimp

### [2018-04-24 20:17:52-04:00](https://github.com/leanprover-community/mathlib/commit/e4c09d4)
feat(analysis/topology/topological_space): a finite union of compact sets is compact ([#117](https://github.com/leanprover-community/mathlib/pull/117))

### [2018-04-24 20:16:10-04:00](https://github.com/leanprover-community/mathlib/commit/e4e4659)
feat(tactic/generalize_hyp): a version of `generalize` that also applies to assumptions ([#110](https://github.com/leanprover-community/mathlib/pull/110))

### [2018-04-24 17:00:19-04:00](https://github.com/leanprover-community/mathlib/commit/f87135b)
feat(algebra/pi_instances): Adds pi instances for common algebraic structures

### [2018-04-24 15:57:06-04:00](https://github.com/leanprover-community/mathlib/commit/3b73ea1)
feat(tactic/convert): tactic similar to `refine` ([#116](https://github.com/leanprover-community/mathlib/pull/116))
... but which generates equality proof obligations for every discrepancy between the goal and
the type of the rule

### [2018-04-24 14:30:20-04:00](https://github.com/leanprover-community/mathlib/commit/7dcd6f5)
feat(tactic/interactive): adding a discharger argument to solve_by_elim ([#108](https://github.com/leanprover-community/mathlib/pull/108))

### [2018-04-24 14:26:32-04:00](https://github.com/leanprover-community/mathlib/commit/009968e)
feat(docs/tactic): document congr_n and unfold_coes ([#105](https://github.com/leanprover-community/mathlib/pull/105))

### [2018-04-24 14:25:48-04:00](https://github.com/leanprover-community/mathlib/commit/44391c9)
doc(docs/elan.md): a short setup guide
A short guide on getting started with Lean, mathlib and elan.
Adds a link to docs/elan.md in README.md

### [2018-04-24 14:24:59-04:00](https://github.com/leanprover-community/mathlib/commit/23c07fd)
feat(docs/extras/cc) Documents the cc tactic
From explanations and experiments by Simon, Gabriel and Kenny at
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/cc.20is.20so.20powerful

### [2018-04-24 14:22:35-04:00](https://github.com/leanprover-community/mathlib/commit/e2c7421)
feat(tactic/ext): new `ext` tactic and corresponding `extensionality` attribute

### [2018-04-24 14:15:55-04:00](https://github.com/leanprover-community/mathlib/commit/d862939)
fix(tactic/wlog): in the proof of completeness, useful assumptions were not visible

### [2018-04-19 08:49:27-04:00](https://github.com/leanprover-community/mathlib/commit/c13c5ea)
fix(ordinal): fix looping simp

### [2018-04-19 07:58:36-04:00](https://github.com/leanprover-community/mathlib/commit/2d935cb)
refactor(lebesgue_measure): clean up proofs

### [2018-04-19 04:40:28-04:00](https://github.com/leanprover-community/mathlib/commit/7d1ab38)
feat(list/basic,...): minor modifications & additions
based on Zulip conversations and requests

### [2018-04-17 21:08:42-04:00](https://github.com/leanprover-community/mathlib/commit/ed09867)
feat(data/list/basic): prefix_or_prefix

### [2018-04-17 01:53:53-04:00](https://github.com/leanprover-community/mathlib/commit/d9daa10)
chore(group_theory): fixups

### [2018-04-16 19:39:05-04:00](https://github.com/leanprover-community/mathlib/commit/4f42fbf)
feat(data/option): more option stuff

### [2018-04-16 19:01:44-04:00](https://github.com/leanprover-community/mathlib/commit/d5c73c0)
chore(*): trailing spaces

### [2018-04-16 19:00:13-04:00](https://github.com/leanprover-community/mathlib/commit/b7db508)
feat(analysis/topology/topological_space): basis elements are open

### [2018-04-16 19:00:13-04:00](https://github.com/leanprover-community/mathlib/commit/6dd2bc0)
feat(data/option): more option decidability

### [2018-04-16 20:29:17+02:00](https://github.com/leanprover-community/mathlib/commit/f2361dc)
fix(group_theory/coset): left_cosets.left_cosets -> left_cosets.eq_class_eq_left_coset is now a theorem

### [2018-04-16 20:09:50+02:00](https://github.com/leanprover-community/mathlib/commit/910de7e)
refactor(group_theory/coset): left_cosets is now a quotient ([#103](https://github.com/leanprover-community/mathlib/pull/103))

### [2018-04-15 17:58:13+02:00](https://github.com/leanprover-community/mathlib/commit/479a122)
doc(doc): add topological space doc ([#101](https://github.com/leanprover-community/mathlib/pull/101))

### [2018-04-15 17:41:57+02:00](https://github.com/leanprover-community/mathlib/commit/c34f202)
Adding some notes on calc

### [2018-04-15 17:39:03+02:00](https://github.com/leanprover-community/mathlib/commit/21d5618)
feat(docs/styles): Some more indentation guidelines ([#95](https://github.com/leanprover-community/mathlib/pull/95))
Fixed also a typo pointed out by Scott

### [2018-04-15 17:36:59+02:00](https://github.com/leanprover-community/mathlib/commit/f1179bd)
feat(algebra/big_operators): update prod_bij_ne_one ([#100](https://github.com/leanprover-community/mathlib/pull/100))

### [2018-04-13 19:25:49+02:00](https://github.com/leanprover-community/mathlib/commit/5605233)
feat(algebra/big_operators): add prod_sum (equating the product over a sum to the sum of all combinations)

### [2018-04-11 17:11:19+02:00](https://github.com/leanprover-community/mathlib/commit/f1e46e1)
fix(.travis.yml): fix some elan

### [2018-04-11 16:41:07+02:00](https://github.com/leanprover-community/mathlib/commit/b13f404)
chore(.travis.yml): show some elan

### [2018-04-11 15:17:30+02:00](https://github.com/leanprover-community/mathlib/commit/5f360e3)
feat(group_theory): add group.closure, the subgroup generated by a set

### [2018-04-11 14:49:46+02:00](https://github.com/leanprover-community/mathlib/commit/fea2491)
chore(group_theory): move order_of into its own file; base costes on left_coset

### [2018-04-11 13:50:33+02:00](https://github.com/leanprover-community/mathlib/commit/d2ab199)
chore(group_theory): simplify proofs; generalize some theorems

### [2018-04-11 10:25:21+02:00](https://github.com/leanprover-community/mathlib/commit/ea0fb11)
style(group_theory): try to follow conventions (calc indentation, lowercase names, ...)

### [2018-04-11 10:24:33+02:00](https://github.com/leanprover-community/mathlib/commit/fa86d34)
feat(group_theory): add left/right cosets and normal subgroups

### [2018-04-10 14:38:56+02:00](https://github.com/leanprover-community/mathlib/commit/f85330a)
feat(group_theory/submonoid): relate monoid closure to list product

### [2018-04-10 13:58:37+02:00](https://github.com/leanprover-community/mathlib/commit/4a15503)
refactor(ring_theory): unify monoid closure in ring theory with the one in group theory

### [2018-04-10 13:13:52+02:00](https://github.com/leanprover-community/mathlib/commit/ec18563)
feat(group_theory): add subtype instanes for group and monoid; monoid closure

### [2018-04-10 13:02:43+02:00](https://github.com/leanprover-community/mathlib/commit/88960f0)
refactor(algebra): move is_submonoid to group_theory and base is_subgroup on is_submonoid

### [2018-04-09 14:39:12-04:00](https://github.com/leanprover-community/mathlib/commit/bd0a555)
fix(algebra/group_power): remove has_smul
This was causing notation overload problems with module smul

### [2018-04-09 11:32:20+02:00](https://github.com/leanprover-community/mathlib/commit/b02733d)
fix(data/finset): change argument order of finset.induction(_on) so that the induction tactic accepts them

### [2018-04-09 10:30:13+02:00](https://github.com/leanprover-community/mathlib/commit/018cfdd)
feat(linear_algebra/multivariate_polynomial): make theory computational

### [2018-04-08 01:00:54-04:00](https://github.com/leanprover-community/mathlib/commit/2bd5e21)
feat(data/int/modeq): Modular arithmetic for integers

### [2018-04-08 00:45:25-04:00](https://github.com/leanprover-community/mathlib/commit/6815830)
chore(measure_theory/measure_space): add coe_fn instance

### [2018-04-08 00:35:55-04:00](https://github.com/leanprover-community/mathlib/commit/03d5bd9)
fix(*): update to lean

### [2018-04-07 22:38:50-04:00](https://github.com/leanprover-community/mathlib/commit/e9b9014)
feat(data/erased): VM-erased data type

### [2018-04-05 01:29:34-04:00](https://github.com/leanprover-community/mathlib/commit/22e671c)
fix(travis.yml): fix travis setup for new nightlies

### [2018-04-05 01:05:02-04:00](https://github.com/leanprover-community/mathlib/commit/81264ec)
fix(leanpkg.toml): remove lean_version
I will keep marking the nightly version here, but I will leave it commented out until I can figure out how to make travis work with it

### [2018-04-05 00:59:52-04:00](https://github.com/leanprover-community/mathlib/commit/08f19fd)
chore(data/nat/prime): style and minor modifications

### [2018-04-05 00:35:23-04:00](https://github.com/leanprover-community/mathlib/commit/efa4f92)
feat(data/nat/prime): lemmas about nat.factors

### [2018-04-05 00:22:45-04:00](https://github.com/leanprover-community/mathlib/commit/2d370e9)
feat(algebra/euclidean_domain): euclidean domains / euclidean algorithm

### [2018-04-05 00:16:34-04:00](https://github.com/leanprover-community/mathlib/commit/467f60f)
feat(data/nat/basic): add div_le_div_right
Based on [#91](https://github.com/leanprover-community/mathlib/pull/91) by @MonoidMusician

### [2018-04-05 00:13:56-04:00](https://github.com/leanprover-community/mathlib/commit/47f1384)
doc(docs/extras): Adding notes on simp

### [2018-04-05 00:12:09-04:00](https://github.com/leanprover-community/mathlib/commit/73d481a)
adding explanation of "change"

### [2018-04-05 00:07:53-04:00](https://github.com/leanprover-community/mathlib/commit/c87f1e6)
fix(*): finish lean update

### [2018-04-03 21:23:26-04:00](https://github.com/leanprover-community/mathlib/commit/5717986)
fix(*): update to lean
also add mathlib nightly version to leanpkg.toml

### [2018-04-01 22:10:37-04:00](https://github.com/leanprover-community/mathlib/commit/777f6b4)
feat(data/set/basic): add some more set lemmas

### [2018-04-01 21:30:17-04:00](https://github.com/leanprover-community/mathlib/commit/d80ca59)
feat(data/fin): add fz/fs recursor for fin