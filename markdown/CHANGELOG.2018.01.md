### [2018-01-26 03:15:01-05:00](https://github.com/leanprover-community/mathlib/commit/edd62de)
fix(set_theory/zfc): update to lean

### [2018-01-26 02:52:13-05:00](https://github.com/leanprover-community/mathlib/commit/f46d32b)
feat(algebra/archimedean): generalize real thms to archimedean fields

### [2018-01-25 01:34:48-05:00](https://github.com/leanprover-community/mathlib/commit/0e42187)
fix(algebra/module): fix module typeclass resolution
Before this change, any looping typeclass instance on `ring` (like `ring A -> ring (f A)`) would cause unrelated typeclass problems such as `has_add B` to search for `module ?M B` and then `ring ?M`, leading to an infinite number of applications of the looping ring instance. leanprover/lean[#1881](https://github.com/leanprover-community/mathlib/pull/1881) promises to fix this, but until then here is a workaround.

### [2018-01-24 14:25:32-05:00](https://github.com/leanprover-community/mathlib/commit/7fba1af)
fix(analysis/metric_space): remove superfluous typeclass assumptions

### [2018-01-23 03:30:58-05:00](https://github.com/leanprover-community/mathlib/commit/acb9093)
feat(analysis/complex): complex numbers are a top ring

### [2018-01-23 03:07:52-05:00](https://github.com/leanprover-community/mathlib/commit/65c5cb9)
refactor(data/real): generalize cau_seq to arbitrary metrics
the intent is to use this also for the complex numbers

### [2018-01-23 00:14:20-05:00](https://github.com/leanprover-community/mathlib/commit/5fe8fbf)
feat(data/complex): properties of the complex absolute value function

### [2018-01-21 23:57:42-05:00](https://github.com/leanprover-community/mathlib/commit/5a65212)
feat(data/real): real square root function, sqrt 2 is irrational

### [2018-01-20 21:28:43-05:00](https://github.com/leanprover-community/mathlib/commit/ffafdc6)
feat(tactic/ring): extend ring tactic to allow division by constants

### [2018-01-20 17:03:57-05:00](https://github.com/leanprover-community/mathlib/commit/bcbf0d5)
refactor(data/complex): clean up proofs

### [2018-01-19 17:05:43-05:00](https://github.com/leanprover-community/mathlib/commit/baa4b09)
feat(analysis/real): swap out the definition of real, shorten proofs

### [2018-01-19 16:18:40-05:00](https://github.com/leanprover-community/mathlib/commit/bb1a9f2)
feat(data/real,*): supporting material for metric spaces

### [2018-01-17 17:53:52-05:00](https://github.com/leanprover-community/mathlib/commit/0ac694c)
fix(tactic/interactive): update to lean

### [2018-01-16 16:08:50-05:00](https://github.com/leanprover-community/mathlib/commit/e11da6e)
feat(data/real): variants on archimedean property

### [2018-01-16 05:29:44-05:00](https://github.com/leanprover-community/mathlib/commit/d84dfb1)
feat(data/real): completeness of the (new) real numbers

### [2018-01-15 07:59:59-05:00](https://github.com/leanprover-community/mathlib/commit/04cac95)
feat(data/real): reals from first principles
This is beginning work on a simpler implementation of real numbers, based on Cauchy sequences, to help alleviate some of the issues we have seen with loading times and timeouts when working with real numbers. If everything goes according to plan, `analysis/real.lean` will be the development for the topology of the reals, but the initial construction will have no topology prerequisites.

### [2018-01-14 21:59:50-05:00](https://github.com/leanprover-community/mathlib/commit/65db966)
feat(algebra/field): more division lemmas

### [2018-01-14 17:36:13-05:00](https://github.com/leanprover-community/mathlib/commit/0d6d12a)
feat(tactic/interactive): replace tactic

### [2018-01-14 01:53:04-05:00](https://github.com/leanprover-community/mathlib/commit/edde6f5)
feat(tactic/ring): use `ring` for rewriting into pretty print format

### [2018-01-13 19:43:41-05:00](https://github.com/leanprover-community/mathlib/commit/c75b072)
fix(*): update to lean

### [2018-01-13 10:22:46-05:00](https://github.com/leanprover-community/mathlib/commit/df7175f)
fix(tactic/ring): bugfix

### [2018-01-13 04:32:47-05:00](https://github.com/leanprover-community/mathlib/commit/341fd51)
fix(tactic/ring): bugfix

### [2018-01-13 03:25:35-05:00](https://github.com/leanprover-community/mathlib/commit/2e2d89b)
feat(tactic/ring): tactic for ring equality

### [2018-01-12 13:08:48-05:00](https://github.com/leanprover-community/mathlib/commit/c39b43f)
feat(analysis/metric_space): sup metric for product of metric spaces

### [2018-01-11 23:22:32-05:00](https://github.com/leanprover-community/mathlib/commit/1dddcf6)
doc(*): blurbs galore
Document all `def`, `class`, and `inductive` that are reasonably public-facing

### [2018-01-11 16:26:08-05:00](https://github.com/leanprover-community/mathlib/commit/2ffd72c)
refactor(order/basic): remove "increasing/decreasing" unusual defs

### [2018-01-11 16:21:21-05:00](https://github.com/leanprover-community/mathlib/commit/09e0899)
fix(analysis/ennreal): fix long-running proofs

### [2018-01-11 12:23:27-05:00](https://github.com/leanprover-community/mathlib/commit/7fd7ea8)
fix(analysis/real): more irreducible

### [2018-01-11 06:57:19-05:00](https://github.com/leanprover-community/mathlib/commit/27920e9)
fix(data/list/basic,...): update to lean

### [2018-01-10 03:03:39-05:00](https://github.com/leanprover-community/mathlib/commit/dc28573)
fix(number_theory/pell,...): update to lean

### [2018-01-07 14:32:08-05:00](https://github.com/leanprover-community/mathlib/commit/5ff51dc)
feat(analysis/complex): complex numbers as a field

### [2018-01-06 18:57:25-05:00](https://github.com/leanprover-community/mathlib/commit/182c303)
feat(set_theory/cofinality): regular/inaccessible cards, Konig's theorem, next fixpoint function

### [2018-01-06 00:50:12+01:00](https://github.com/leanprover-community/mathlib/commit/4f7835e)
feat(analysis): add default setup for uniform space of metric space

### [2018-01-04 09:05:50-05:00](https://github.com/leanprover-community/mathlib/commit/0b7b912)
feat(set_theory/ordinal_notation): correctness of ordinal power

### [2018-01-04 09:05:02-05:00](https://github.com/leanprover-community/mathlib/commit/3f2435e)
refactor(algebra/group): clean up PR commit

### [2018-01-02 16:52:49-05:00](https://github.com/leanprover-community/mathlib/commit/12bd22b)
Group morphisms ([#30](https://github.com/leanprover-community/mathlib/pull/30))
* feat(algebra/group): morphisms and antimorphisms
Definitions, image of one and inverses,
and computation on a product of more than two elements in big_operators.

### [2018-01-02 04:28:01-05:00](https://github.com/leanprover-community/mathlib/commit/37c3120)
feat(set_theory/ordinal_notation): ordinal notations for ordinals < e0
This allows us to compute with small countable ordinals using trees of nats.