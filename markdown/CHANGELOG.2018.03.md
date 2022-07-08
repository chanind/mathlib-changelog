### [2018-03-30 14:05:43+02:00](https://github.com/leanprover-community/mathlib/commit/162edc3)
feat(order): add complete lattice of fixed points (Knaster-Tarski) by Kenny Lau https://github.com/leanprover/mathlib/pull/88

### [2018-03-29 17:23:46+02:00](https://github.com/leanprover-community/mathlib/commit/c54d431)
fix(.): unit is now an abbreviation: unit := punit.{1}

### [2018-03-25 19:59:40-04:00](https://github.com/leanprover-community/mathlib/commit/d84af03)
fix(data/option): revert to lean commit 28f414

### [2018-03-22 14:08:02+01:00](https://github.com/leanprover-community/mathlib/commit/e5c1c5e)
fix(number_theory/dipoh): has_map.map -> functor.map

### [2018-03-22 11:27:24+01:00](https://github.com/leanprover-community/mathlib/commit/a357b79)
feat(analysis): measurable_if

### [2018-03-21 19:31:04-04:00](https://github.com/leanprover-community/mathlib/commit/868bbc6)
fix(*): update to lean

### [2018-03-21 19:31:04-04:00](https://github.com/leanprover-community/mathlib/commit/638265c)
fix(set_theory/zfc): improve pSet.equiv.eq
I claimed in the comment that this converse was not provable, but it is (because equiv is embedded in the definition of mem). Thanks to Vinoth Kumar Raman for bringing this to my attention.

### [2018-03-21 19:31:04-04:00](https://github.com/leanprover-community/mathlib/commit/f3660df)
chore(logic/basic): protect classical logic theorems
You can't use these theorems with `open classical` anyway, because of disambiguation with the `_root_` theorems of the same name.

### [2018-03-21 18:56:23-04:00](https://github.com/leanprover-community/mathlib/commit/486e4ed)
fix(test suite): remove `sorry` warning in test suite

### [2018-03-15 00:57:20-04:00](https://github.com/leanprover-community/mathlib/commit/f7977ff)
feat(data/finset): add finset.powerset

### [2018-03-13 05:57:49-04:00](https://github.com/leanprover-community/mathlib/commit/4ceb545)
feat(data/list/basic): stuff about `list.sublists`

### [2018-03-12 20:45:43+01:00](https://github.com/leanprover-community/mathlib/commit/5f8c26c)
feat(analysis/measure_theory): measures are embedded in outer measures; add map, dirac, and sum measures

### [2018-03-12 17:09:31+01:00](https://github.com/leanprover-community/mathlib/commit/36a061b)
feat(analysis/measure_theory): outer_measures form a complete lattice

### [2018-03-11 14:26:05+01:00](https://github.com/leanprover-community/mathlib/commit/64a8d56)
chore(order/filter): simplify definition of filter.prod; cleanup

### [2018-03-10 20:37:53+01:00](https://github.com/leanprover-community/mathlib/commit/b154092)
feat(data/finsupp): make finsupp computable; add induction rule; removed comap_domain

### [2018-03-10 13:38:59+01:00](https://github.com/leanprover-community/mathlib/commit/b97b7c3)
feat(group_theory): add a little bit of group theory; prove of Lagrange's theorem

### [2018-03-10 12:39:38+01:00](https://github.com/leanprover-community/mathlib/commit/d010717)
chore(linear_algebra): flatten hierarchy, move algebra/linear_algebra to linear_algebra

### [2018-03-09 15:55:09+01:00](https://github.com/leanprover-community/mathlib/commit/d78c8ea)
chore(ring_theory): cleaned up ideals

### [2018-03-09 14:39:42+01:00](https://github.com/leanprover-community/mathlib/commit/06c54b3)
chore(ring_theory): introduce r_of_eq for localization

### [2018-03-09 14:39:42+01:00](https://github.com/leanprover-community/mathlib/commit/e658d36)
chore(ring_theory): fix indentation

### [2018-03-08 16:21:02+01:00](https://github.com/leanprover-community/mathlib/commit/a6960f5)
chore(ring_theory): add copyright headers

### [2018-03-08 13:57:16+01:00](https://github.com/leanprover-community/mathlib/commit/fe0f2a3)
fix(analysis/topology/topological_structures): remove unnecessary hypothesis

### [2018-03-08 11:45:04+01:00](https://github.com/leanprover-community/mathlib/commit/a7d8c5f)
feat(tactic): add `wlog` (without loss of generality), `tauto`, `auto` and `xassumption`
* `tauto`: for simple tautologies;
* `auto`: discharging the goals that follow directly from a few assumption applications;
* `xassumption`: similar to `assumption` but matches against the head of assumptions instead of the whole thing

### [2018-03-08 11:25:28+01:00](https://github.com/leanprover-community/mathlib/commit/c852939)
feat(ring_theory): move localization

### [2018-03-08 10:42:28+01:00](https://github.com/leanprover-community/mathlib/commit/0b81b24)
feat(analysis/topological_structures): add tendsto_of_tendsto_of_tendsto_of_le_of_le

### [2018-03-08 09:55:42+01:00](https://github.com/leanprover-community/mathlib/commit/353c494)
fix(docs): more converter -> conversion

### [2018-03-08 09:51:03+01:00](https://github.com/leanprover-community/mathlib/commit/fa25539)
feat(docs/extras/conv): Documents conv mode ([#73](https://github.com/leanprover-community/mathlib/pull/73))

### [2018-03-07 13:47:04+01:00](https://github.com/leanprover-community/mathlib/commit/22237f4)
feat(data/fintype): pi is closed under fintype & decidable_eq

### [2018-03-07 13:47:00+01:00](https://github.com/leanprover-community/mathlib/commit/e6afbf5)
feat(data/finset): add Cartesian product over dependent functions

### [2018-03-07 13:46:54+01:00](https://github.com/leanprover-community/mathlib/commit/10cf239)
feat(data/multiset): add Cartesian product over dependent functions

### [2018-03-07 13:46:54+01:00](https://github.com/leanprover-community/mathlib/commit/be4a35f)
feat(data/multiset): add dependent recursor for multisets

### [2018-03-07 13:46:39+01:00](https://github.com/leanprover-community/mathlib/commit/eef3a4d)
feat(data/multiset): add map_hcongr, bind_hcongr, bind_bind, attach_zero, and attach_cons

### [2018-03-07 13:46:39+01:00](https://github.com/leanprover-community/mathlib/commit/bbd0203)
feat(data/multiset): decidable equality for functions whose domain is bounded by multisets

### [2018-03-07 13:46:32+01:00](https://github.com/leanprover-community/mathlib/commit/dc8c35f)
feat(logic/function): add hfunext and funext_iff

### [2018-03-06 16:12:46-05:00](https://github.com/leanprover-community/mathlib/commit/33be7dc)
doc(docs/theories): Description of other set-like types
From [#75](https://github.com/leanprover-community/mathlib/pull/75)

### [2018-03-05 21:58:36+01:00](https://github.com/leanprover-community/mathlib/commit/65cab91)
doc(order/filter): add documentation for `filter_upward`

### [2018-03-05 18:18:38+01:00](https://github.com/leanprover-community/mathlib/commit/5193194)
feat(order/filter): reorder filter theory; add filter_upwards tactic

### [2018-03-05 17:55:59+01:00](https://github.com/leanprover-community/mathlib/commit/0487a32)
chore(*): cleanup

### [2018-03-05 16:11:22+01:00](https://github.com/leanprover-community/mathlib/commit/ec9dac3)
chore(*): update to Lean d6d44a19