### [2018-10-31 21:17:26+01:00](https://github.com/leanprover-community/mathlib/commit/74ae8ce)
fix(data/real,data/rat): make orders on real and rat irreducible

### [2018-10-30 12:26:55-04:00](https://github.com/leanprover-community/mathlib/commit/58909bd)
feat(*): monovariate and multivariate eval\2 now do not take is_semiring_hom as an argument

### [2018-10-30 12:24:35-04:00](https://github.com/leanprover-community/mathlib/commit/90982d7)
feat(tactic/fin_cases): a tactic to case bash on `fin n` ([#352](https://github.com/leanprover-community/mathlib/pull/352))
* feat(tactic/fin_cases): a tactic to case bash on `fin n`
* using core is_numeral
* removing guard
just rely on eval_expr to decide if we have an explicit nat
* add parsing, tests, documentation
* don't fail if the rewrite fails
* fixes

### [2018-10-30 12:23:50-04:00](https://github.com/leanprover-community/mathlib/commit/e585bed)
feat(data/int/basic): bounded forall is decidable for integers

### [2018-10-30 12:23:04-04:00](https://github.com/leanprover-community/mathlib/commit/489050b)
feat(tactic/tauto): add an option for `tauto` to work in classical logic

### [2018-10-19 00:14:30+02:00](https://github.com/leanprover-community/mathlib/commit/ed84298)
feat(analysis/topology): add continuity rules for list and vector insert/remove_nth

### [2018-10-19 00:03:08+02:00](https://github.com/leanprover-community/mathlib/commit/f6812d5)
feat(analysis/topology): add type class for discrete topological spaces

### [2018-10-18 23:05:00+02:00](https://github.com/leanprover-community/mathlib/commit/99e14cd)
feat(group_theory/quotient_group): add map : quotient N -> quotient M

### [2018-10-18 23:02:03+02:00](https://github.com/leanprover-community/mathlib/commit/f52d2cc)
chore(group_theory/free_abelian_group, abelianization): rename to_comm_group, to_add_comm_group -> lift

### [2018-10-18 13:48:14+02:00](https://github.com/leanprover-community/mathlib/commit/c3e489c)
chore(data/fin): add cast_add

### [2018-10-18 09:43:01+02:00](https://github.com/leanprover-community/mathlib/commit/f2beca8)
feat(ring_theory): prove principal_ideal_domain is unique factorization domain

### [2018-10-18 09:41:00+02:00](https://github.com/leanprover-community/mathlib/commit/7b876a2)
cleanup(data/nat/choose,binomial): move binomial into choose

### [2018-10-18 09:08:54+02:00](https://github.com/leanprover-community/mathlib/commit/a46e8f7)
cleanup(ring_theory/principal_ideal_domain): restructure

### [2018-10-18 00:33:42+02:00](https://github.com/leanprover-community/mathlib/commit/a3ac630)
feat(algebra,group_theory): add various closure properties of subgroup and is_group_hom w.r.t gsmul, prod, sum

### [2018-10-17 23:01:03+02:00](https://github.com/leanprover-community/mathlib/commit/ea962a7)
chore(analysis/topology/continuity): locally_compact_space is Prop

### [2018-10-17 22:49:26+02:00](https://github.com/leanprover-community/mathlib/commit/bac655d)
feature(data/vector2, data/list): add insert_nth for vectors and lists

### [2018-10-17 20:57:36+02:00](https://github.com/leanprover-community/mathlib/commit/085b1bc)
cleanup(algebra/group_power): remove inactive to_additive

### [2018-10-17 20:56:45+02:00](https://github.com/leanprover-community/mathlib/commit/1008f08)
cleanup(tactic): remove example

### [2018-10-17 16:12:26+02:00](https://github.com/leanprover-community/mathlib/commit/5a8e28d)
doc(docs/tactic): unify choose doc ([#426](https://github.com/leanprover-community/mathlib/pull/426))

### [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/72308d8)
chore(data/fin): use uniform names; restructure

### [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/d2b3940)
feat(data/fin): ascend / descend for fin

### [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/f789969)
feat(data/finset): add min' / max' for non-empty finset

### [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/ef9566d)
feat(data/equiv): equivalences for fin * fin and fin + fin

### [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/b085915)
feat(data/list): length_attach, nth_le_attach, nth_le_range, of_fn_eq_pmap, nodup_of_fn (by @kckennylau)

### [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/b454dae)
feat(group_theory/perm): swap_mul_swal / swap_swap_apply (by @kckennylau)

### [2018-10-17 09:46:54+02:00](https://github.com/leanprover-community/mathlib/commit/530e1d1)
refactor (data/finset): explicit arguments for subset_union_* and inter_subset_*
This change makes them a little easier to apply, and also makes them consistent with their analogues in set.basic.

### [2018-10-17 09:25:02+02:00](https://github.com/leanprover-community/mathlib/commit/b5cd974)
feat(*): trigonometric functions: exp, log, sin, cos, tan, sinh, cosh, tanh, pi, arcsin, argcos, arg ([#386](https://github.com/leanprover-community/mathlib/pull/386))
* `floor_ring` now is parameterized on a `linear_ordered_ring` instead of extending it.
*

### [2018-10-16 13:07:50+02:00](https://github.com/leanprover-community/mathlib/commit/792c673)
feat(order/galois_connection): make arguemnts to dual implicit

### [2018-10-15 17:21:09+02:00](https://github.com/leanprover-community/mathlib/commit/80d688e)
feat(data/nat/choose): nat.prime.dvd_choose ([#419](https://github.com/leanprover-community/mathlib/pull/419))
* feat(data/nat/choose): nat/prime.dvd_choose
* use nat namespace
* Update prime.lean
* improve readability

### [2018-10-15 15:12:23+02:00](https://github.com/leanprover-community/mathlib/commit/c5930f5)
feat(group_theory.order_of_element): subgroups of cyclic groups are cyclic ([#423](https://github.com/leanprover-community/mathlib/pull/423))
* feat(group_theory.order_of_element): subgroups of cyclic groups are cyclic
* delete new line

### [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/a33ab12)
refactor(analysis/topology): move separation ring to quotient_topological_structures

### [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/1308077)
feature(data/equiv/algebra): add mul left/right and inverse as equivalences

### [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/c8ecae8)
feature(analysis/topology/continuity): start homeomorphism

### [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/af434b5)
refactor(analysis/topology): move is_open_map to continuity

### [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/29675ad)
refactor(analysis/topology/topological_structures): use to_additive to derive topological_add_monoid and topological_add_group

### [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/75046c2)
chore(data/quot): add setoid.ext

### [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/2395183)
feat(analysis/topology/quotient_topological_structures): endow quotient
of topological groups, add groups and rings with a topological whatever
structure
This is not yet sorted. I'd like to push completions before cleaning
this.

### [2018-10-15 13:35:49+02:00](https://github.com/leanprover-community/mathlib/commit/7358605)
feat(analysis/topology/completion): comm_ring on separation quotient, completion (separation_quotient A) is equivalent to completion A

### [2018-10-15 13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/13be74f)
feat(analysis/topology/topological_structure): ideal closure is ideal

### [2018-10-15 13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/7697a84)
feat(analysis/topology/topological_groups): construct topologies out of a group and a neighbourhood filter at 0

### [2018-10-15 13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/96d3f95)
doc(analysis/topology/completion): document changed organization

### [2018-10-15 13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/fbb6e9b)
feat(analysis/topology): group completion

### [2018-10-14 23:27:04-04:00](https://github.com/leanprover-community/mathlib/commit/8150f19)
feat(logic/basic): classical.not_not ([#418](https://github.com/leanprover-community/mathlib/pull/418))
* feat(logic/basic): classical.not_not
* mark as protected

### [2018-10-12 23:59:58+02:00](https://github.com/leanprover-community/mathlib/commit/019b236)
fix(category_theory/open_set): Restore the correct order on open_set

### [2018-10-12 10:55:25+02:00](https://github.com/leanprover-community/mathlib/commit/131cf14)
feat(group_theory/quotient_group): add to_additive attribute

### [2018-10-12 10:54:58+02:00](https://github.com/leanprover-community/mathlib/commit/c8d3c96)
feat(tactic/interactive): congr' tries harder

### [2018-10-11 08:53:11-04:00](https://github.com/leanprover-community/mathlib/commit/62451d3)
cleanup(data/polynomial): simplify proof of coeff_mul_left ([#414](https://github.com/leanprover-community/mathlib/pull/414))

### [2018-10-11 13:22:43+02:00](https://github.com/leanprover-community/mathlib/commit/0fe2849)
chore(analysis/measure_theory): finish characterization of lintegral

### [2018-10-10 22:50:06+02:00](https://github.com/leanprover-community/mathlib/commit/40f5565)
feat(analysis/measure_theory): lower Lebesgue integral under addition, supremum

### [2018-10-10 22:50:06+02:00](https://github.com/leanprover-community/mathlib/commit/a25e4a8)
feat(analysis/measure_theory/integration): lebesgue integration [WIP]

### [2018-10-10 12:53:24-04:00](https://github.com/leanprover-community/mathlib/commit/4dbe0cd)
doc(elan): further improvements to installation instructions ([#412](https://github.com/leanprover-community/mathlib/pull/412)) [ci-skip]

### [2018-10-10 04:04:54-04:00](https://github.com/leanprover-community/mathlib/commit/979e238)
fix(*): fix build continued

### [2018-10-10 03:27:18-04:00](https://github.com/leanprover-community/mathlib/commit/1a4156d)
fix(data/nat): fix build

### [2018-10-10 03:03:09-04:00](https://github.com/leanprover-community/mathlib/commit/fedee98)
feat(data/nat/basic): a few choiceless proofs
not sure I can take this much farther without modifying core...

### [2018-10-10 03:01:34-04:00](https://github.com/leanprover-community/mathlib/commit/1daf4a8)
fix(data/set/lattice): fixing simp lemmas for set monad

### [2018-10-09 22:59:15-04:00](https://github.com/leanprover-community/mathlib/commit/d867240)
feat(data/set/finite): finiteness of set monad ops

### [2018-10-09 01:14:15-04:00](https://github.com/leanprover-community/mathlib/commit/5c209ed)
fix(linear_algebra/dimension): fix build

### [2018-10-08 15:17:51-04:00](https://github.com/leanprover-community/mathlib/commit/2c11641)
refactor(data/polynomial): consistently use coeff not apply ([#409](https://github.com/leanprover-community/mathlib/pull/409))

### [2018-10-08 14:51:29-04:00](https://github.com/leanprover-community/mathlib/commit/a694628)
fix(tactic/rcases): declare ? token

### [2018-10-08 14:30:13-04:00](https://github.com/leanprover-community/mathlib/commit/3aeb64c)
refactor(*): touching up proofs from 'faster' branch

### [2018-10-08 14:30:12-04:00](https://github.com/leanprover-community/mathlib/commit/f02a88b)
chore(*): replace rec_on with induction and match for readability

### [2018-10-08 14:30:12-04:00](https://github.com/leanprover-community/mathlib/commit/cc2e1ec)
refactor(*): making mathlib faster again

### [2018-10-08 04:07:24-04:00](https://github.com/leanprover-community/mathlib/commit/136ef25)
feat(ring_theory/determinants): det is a monoid_hom ([#406](https://github.com/leanprover-community/mathlib/pull/406))

### [2018-10-08 03:07:28-04:00](https://github.com/leanprover-community/mathlib/commit/61d8776)
fix(ring_theory/determinant): remove #print ([#405](https://github.com/leanprover-community/mathlib/pull/405))

### [2018-10-08 00:49:30-04:00](https://github.com/leanprover-community/mathlib/commit/13febee)
fix(group_theory/perm): fix to_additive use

### [2018-10-07 21:29:00-04:00](https://github.com/leanprover-community/mathlib/commit/73f51b8)
feat(ring_theory/determinant): determinants ([#404](https://github.com/leanprover-community/mathlib/pull/404))
* clean up determinant PR
* remove unnecessary type annotations
* update copyright
* add additive version of prod_attach_univ

### [2018-10-07 21:27:20-04:00](https://github.com/leanprover-community/mathlib/commit/04d8c15)
feat(solve_by_elim): improve backtracking behaviour when there are multiple subgoals ([#393](https://github.com/leanprover-community/mathlib/pull/393))

### [2018-10-07 09:22:24-04:00](https://github.com/leanprover-community/mathlib/commit/8c68fd1)
feat(tactic/auto_cases): split `iff`s into two implications ([#344](https://github.com/leanprover-community/mathlib/pull/344))
* feat(tactic/auto_cases): split `iff`s into two implications
* add Johan's test case

### [2018-10-07 09:17:40-04:00](https://github.com/leanprover-community/mathlib/commit/49fea31)
feat(tactics/solve_by_elim): add or remove lemmas from the set to apply, with `simp`-like parsing ([#382](https://github.com/leanprover-community/mathlib/pull/382))
* feat(tactic/solve_by_elim): modify set of lemmas to apply using `simp`-like syntax
* update to syntax: use `with attr` to request all lemmas tagged with an attribute
* use non-interactive solve_by_elim in tfae
* fix parser

### [2018-10-07 09:12:40-04:00](https://github.com/leanprover-community/mathlib/commit/3b09151)
feat(tactic/squeeze): squeeze_simp tactic ([#396](https://github.com/leanprover-community/mathlib/pull/396))
* feat(tactic/squeeze): just the squeeze_simp tactic
* docs(tactic/squeeze): add header comments and documentation
* Provide a means for other tactics to use squeeze

### [2018-10-07 09:09:49-04:00](https://github.com/leanprover-community/mathlib/commit/c1f13c0)
fix(data/int.basic): rename sub_one_le_iff ([#394](https://github.com/leanprover-community/mathlib/pull/394))

### [2018-10-07 09:09:28-04:00](https://github.com/leanprover-community/mathlib/commit/d1e34fd)
fix(algebra/big_operators): remove `comm_monoid` assumption from `sum_nat_cast` ([#401](https://github.com/leanprover-community/mathlib/pull/401))

### [2018-10-07 09:08:52-04:00](https://github.com/leanprover-community/mathlib/commit/276c472)
fix(algebra/ring): delete duplicate lemma zero_dvd_iff_eq_zero ([#399](https://github.com/leanprover-community/mathlib/pull/399))

### [2018-10-07 07:16:14-04:00](https://github.com/leanprover-community/mathlib/commit/e4ce469)
fix(docs/elan): fix homebrew instructions for macOS ([#395](https://github.com/leanprover-community/mathlib/pull/395))

### [2018-10-07 07:15:56-04:00](https://github.com/leanprover-community/mathlib/commit/64431ae)
doc(hole/instance_stub) ([#400](https://github.com/leanprover-community/mathlib/pull/400))

### [2018-10-07 06:35:55-04:00](https://github.com/leanprover-community/mathlib/commit/46a37a7)
feat(hole/instance_stub): tool support for providing snippets ([#397](https://github.com/leanprover-community/mathlib/pull/397))

### [2018-10-07 02:28:18-04:00](https://github.com/leanprover-community/mathlib/commit/0ddb58c)
workaround(tactic/tfae): tfae is broken, comment out its tests ([#398](https://github.com/leanprover-community/mathlib/pull/398))

### [2018-10-06 22:41:00-04:00](https://github.com/leanprover-community/mathlib/commit/2bf7b4b)
refactor(tactic/tfae): minor tfae modifications

### [2018-10-06 22:33:52-04:00](https://github.com/leanprover-community/mathlib/commit/568e405)
feat(data/finset): embedding properties of finset.map

### [2018-10-05 02:18:56-04:00](https://github.com/leanprover-community/mathlib/commit/74f52f1)
Expand and contract fin ([#387](https://github.com/leanprover-community/mathlib/pull/387))

### [2018-10-04 15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/9ec21e4)
perf(tactic/scc): produce smaller proofs

### [2018-10-04 15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/025b73a)
chore(tactic/scc): small cleanup

### [2018-10-04 15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/ff12b35)
docs(tactic/tfae): move doc string

### [2018-10-04 15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/d935519)
docs(tactic/tfae): fix oversights

### [2018-10-04 15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/b7d314f)
feat(tactic/tfae): tactic for decomposing a proof into a set of
equivalent propositions which can be proved equivalent by cyclical
implications

### [2018-10-03 12:54:45+02:00](https://github.com/leanprover-community/mathlib/commit/a243126)
chore(*): replace more axiom_of_choice, classical.some and classical.choice using the choose tactic

### [2018-10-03 11:24:50+02:00](https://github.com/leanprover-community/mathlib/commit/c1f9f2e)
refactor(tactics/interactive, *): rename choice to choose and change syntax; use chooose instead of cases of axiom_of_choice

### [2018-10-03 09:30:54+02:00](https://github.com/leanprover-community/mathlib/commit/0cfbf5a)
feat(tactic/linarith): handle negations of linear hypotheses

### [2018-10-02 22:17:27+02:00](https://github.com/leanprover-community/mathlib/commit/fff12f5)
chore(analysis/topology): remove duplicate theorems interior_compl_eq and closure_compl_eq (as discovered by @kckennylau)

### [2018-10-02 22:13:59+02:00](https://github.com/leanprover-community/mathlib/commit/c2df6b1)
feat(tactics/interactive): add choice (closes [#38](https://github.com/leanprover-community/mathlib/pull/38))

### [2018-10-02 15:12:09+02:00](https://github.com/leanprover-community/mathlib/commit/b84e2db)
feat(docs/theories): document padics development (close [#337](https://github.com/leanprover-community/mathlib/pull/337))
(it hurts to write "maths in lean")

### [2018-10-02 14:08:34+02:00](https://github.com/leanprover-community/mathlib/commit/1562cc2)
feat(data/padics): use prime typeclass

### [2018-10-02 14:08:34+02:00](https://github.com/leanprover-community/mathlib/commit/e6a1bc3)
feat(data/real/cau_seq): relate cauchy sequence completeness and filter completeness

### [2018-10-02 14:08:34+02:00](https://github.com/leanprover-community/mathlib/commit/e0b0c53)
feat(data/padics): prove Hensel's lemma

### [2018-10-02 14:02:23+02:00](https://github.com/leanprover-community/mathlib/commit/f040aef)
feat(data/padics): use has_norm typeclasses for padics

### [2018-10-02 13:38:45+02:00](https://github.com/leanprover-community/mathlib/commit/963fc83)
doc(docs/elan.md): instructions for building all of a dependency
Closes [#308](https://github.com/leanprover-community/mathlib/pull/308).

### [2018-10-02 13:38:05+02:00](https://github.com/leanprover-community/mathlib/commit/9339754)
docs(elan): updating documentation on installing via elan ([#371](https://github.com/leanprover-community/mathlib/pull/371))
* updating documentation for elan
* minor
* further update of elan docs
* update instructions for elan 0.7.1
* noting additional prerequisite on macOS

### [2018-10-02 13:36:09+02:00](https://github.com/leanprover-community/mathlib/commit/28443c8)
feat(ring_theory/noetherian): zero ring (and finite rings) are Noetherian (closes [#341](https://github.com/leanprover-community/mathlib/pull/341))

### [2018-10-02 11:34:24+02:00](https://github.com/leanprover-community/mathlib/commit/44b55e6)
feat(category_theory/groupoid): groupoids

### [2018-10-02 11:34:04+02:00](https://github.com/leanprover-community/mathlib/commit/efa9459)
feat(category_theory/whiskering): whiskering nat_trans by functors ([#360](https://github.com/leanprover-community/mathlib/pull/360))
* feat(category_theory/whiskering): whiskering nat_trans by functors
* simplify whiskering

### [2018-10-02 08:05:06+02:00](https://github.com/leanprover-community/mathlib/commit/470b6da)
feat(data/sum): add monad instance

### [2018-10-01 20:53:49+02:00](https://github.com/leanprover-community/mathlib/commit/dbb3ff0)
feat(data/zmod/quadratic_reciprocity): quadratic reciprocity ([#327](https://github.com/leanprover-community/mathlib/pull/327))
* multiplicative group of finite field is cyclic
* more stuff
* change chinese remainder to def
* get rid of nonsense
* delete extra line break
* one prod_bij left
* move lemmas to correct places
* delete prod_instances
* almost done
* move lamms to correct places
* more moving lemmas
* finished off moving lemmas
* fix build
* move quadratic reciprocity to zmod
* improve readability
* remove unnecessary alphas
* move `prod_range_id`
* fix build
* fix build
* fix build
* fix build
* delete mk_of_ne_zero
* move odd_mul_odd_div_two
* extra a few lemmas
* improving readability
* delete duplicate lemmas
* forgot to save
* delete duplicate lemma
* indent calc proofs
* fix build
* fix build
* forgot to save
* fix build

### [2018-10-01 20:35:10+02:00](https://github.com/leanprover-community/mathlib/commit/f3850c2)
feat(algebra/group): add units.map and prove that it is a group hom ([#374](https://github.com/leanprover-community/mathlib/pull/374))

### [2018-10-01 20:34:14+02:00](https://github.com/leanprover-community/mathlib/commit/decb030)
style(tactic/*): minor simplifications to tidy-related tactics

### [2018-10-01 20:26:32+02:00](https://github.com/leanprover-community/mathlib/commit/87a963b)
feat(tactic/ext): add apply_cfg argument to ext1 ([#346](https://github.com/leanprover-community/mathlib/pull/346))
* feat(tactics/ext): use `applyc _ {new_goals := new_goals.all}`
This causes goals to appear in the same order they appear as hypotheses of the
`@[extensionality]` lemma, rather than being reordered to put dependent
goals first.
This doesn't appear to affect any uses of `ext` in mathlib,
but is occasionally helpful in the development of category theory.
(Indeed, I have been running into tactic mode proofs that fail to
typecheck, when using ext, and this avoids the problem)
* adding configuration to non-interactive ext1
and a wrapper so tidy can sometimes produce shorter tactic scripts

### [2018-10-01 20:24:42+02:00](https://github.com/leanprover-community/mathlib/commit/1923c23)
feat(data/polynomial): interface general coefficients of a polynomial ([#339](https://github.com/leanprover-community/mathlib/pull/339))
* feat(data/polynomial): interface general coefficients of a polynomial
* fix(data/polynomial): fixing the code I broke when defining polynomial.ext
* fix(data/polynomial): tidy up comments
* Update polynomial.lean
* adding interface for scalar multiplication and coefficients
* feat(data/polynomial): coeff is R-linear

### [2018-10-01 20:19:59+02:00](https://github.com/leanprover-community/mathlib/commit/282754c)
fix(tactic/linarith): symmetric case

### [2018-10-01 20:19:59+02:00](https://github.com/leanprover-community/mathlib/commit/31ef46a)
feat(tactic/linarith): don't reject nonlinear hypotheses

### [2018-10-01 18:10:17+02:00](https://github.com/leanprover-community/mathlib/commit/4ba7f23)
cleanup(data/holor)

### [2018-10-01 14:51:42+02:00](https://github.com/leanprover-community/mathlib/commit/7c361fa)
feat(data/holor): holor library

### [2018-10-01 14:40:27+02:00](https://github.com/leanprover-community/mathlib/commit/b66614d)
refactor(analysis/topology): renamed compact_open to continuous_map; moved locally_compact to a more general position