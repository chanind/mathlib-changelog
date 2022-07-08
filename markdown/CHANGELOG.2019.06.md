### [2019-06-29 16:56:28](https://github.com/leanprover-community/mathlib/commit/469da29)
feat(data/list/basic): map_nil and map_eq_nil ([#1161](https://github.com/leanprover-community/mathlib/pull/1161))
* feat(data/list/basic): map_nil and map_eq_nil
* Update basic.lean
* make Simon's changes

### [2019-06-29 13:28:56](https://github.com/leanprover-community/mathlib/commit/0858157)
refactor(category_theory/category): reorder arguments of `End.has_mul` ([#1128](https://github.com/leanprover-community/mathlib/pull/1128))
* Reorder arguments of `End.has_mul` and `Aut.has_mul`, adjust `category/fold`
* clean up proofs in `category.fold`

### [2019-06-29 12:31:13](https://github.com/leanprover-community/mathlib/commit/e310349)
refactor(ring_theory/ideals): refactor local rings, add local ring homs ([#1102](https://github.com/leanprover-community/mathlib/pull/1102))
* WIP
* refactor(ring_theory/ideals): refactor local rings, add local ring homs
* residue_field.map is a field hom
* make is_local_ring_hom extends is_ring_hom
* refactor local_ring
* tiny changes
* Bump instance search depth

### [2019-06-28 15:11:00](https://github.com/leanprover-community/mathlib/commit/4a5a1a5)
fix(data/list/min_max): correct names of mem_maximum and mem_minimum ([#1162](https://github.com/leanprover-community/mathlib/pull/1162))
* fix(data/list/min_max): correct names of mem_maximum and mem_minimum
* Update denumerable.lean

### [2019-06-28 09:09:55](https://github.com/leanprover-community/mathlib/commit/7d56447)
feat(logic/unique): fin 1 is unique ([#1158](https://github.com/leanprover-community/mathlib/pull/1158))

### [2019-06-27 11:12:29](https://github.com/leanprover-community/mathlib/commit/6bc930a)
chore(src/tactic/interactive): `convert` docstring ([#1148](https://github.com/leanprover-community/mathlib/pull/1148))
* chore(src/tactic/interactive): `convert` docstring 
The `using` option to `convert` was not mentioned in the docstring, and I often struggle to remember the (perhaps slightly exotic?) `using` catchphrase
* Update src/tactic/interactive.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update interactive.lean

### [2019-06-26 12:11:33](https://github.com/leanprover-community/mathlib/commit/9b0fd36)
feat(data/fintype): unique.fintype ([#1154](https://github.com/leanprover-community/mathlib/pull/1154))

### [2019-06-25 14:30:39](https://github.com/leanprover-community/mathlib/commit/7484ab4)
fix(data/matrix): add brackets to mul_neg and neg_mul to correct statement ([#1151](https://github.com/leanprover-community/mathlib/pull/1151))
* fix(data/matrix): add brackets to mul_neg and neg_mul to correct statement
Each side of `mul_neg` was identical.
* fix

### [2019-06-25 13:00:33](https://github.com/leanprover-community/mathlib/commit/a2aeabb)
feat(data/finset): length_sort ([#1150](https://github.com/leanprover-community/mathlib/pull/1150))

### [2019-06-25 13:54:02+02:00](https://github.com/leanprover-community/mathlib/commit/c4a4f79)
feat(algebra/pi_instances): pi.ordered_comm_group ([#1152](https://github.com/leanprover-community/mathlib/pull/1152))

### [2019-06-24 12:33:51](https://github.com/leanprover-community/mathlib/commit/c7ee110)
feat(meta/expr): `simp` and `dsimp` an expr ([#1147](https://github.com/leanprover-community/mathlib/pull/1147))
* feat(meta/expr): `simp` and `dsimp` an expr
* removing def that we don't need yet

### [2019-06-23 02:01:56](https://github.com/leanprover-community/mathlib/commit/d7283d7)
feat(string): `split_on` a `char` ([#1145](https://github.com/leanprover-community/mathlib/pull/1145))
* lib: string
* type

### [2019-06-20 08:30:31](https://github.com/leanprover-community/mathlib/commit/a35d682)
feat(topology/order): more facts on continuous_on ([#1140](https://github.com/leanprover-community/mathlib/pull/1140))

### [2019-06-19 21:00:28](https://github.com/leanprover-community/mathlib/commit/e598894)
chore(topology/*): reverse order on topological and uniform spaces ([#1138](https://github.com/leanprover-community/mathlib/pull/1138))
* chore(topology/*): reverse order on topological and uniform spaces
* fix(topology/order): private lemma hiding partial order oscillation,
following Mario's suggestion
* change a temporary name
Co-Authored-By: Johan Commelin <johan@commelin.net>
* forgotten rename

### [2019-06-19 08:03:18](https://github.com/leanprover-community/mathlib/commit/b1cb48d)
feat(data/set): simple lemmas, renaming ([#1137](https://github.com/leanprover-community/mathlib/pull/1137))
* feat(data/set): simple lemmas, renaming
* improve projection lemmas
* arguments order

### [2019-06-18 22:06:30](https://github.com/leanprover-community/mathlib/commit/235b899)
fix(category_theory/types): rename lemma `ulift_functor.map` ([#1133](https://github.com/leanprover-community/mathlib/pull/1133))
* fix(category_theory/types): avoid shadowing `ulift_functor.map` by a lemma
Now we can use `ulift_functor.map` in the sense `functor.map ulift_functor`.
* `ulift_functor.map_spec` → `ulift_functor_map`
as suggested by @semorrison in https://github.com/leanprover-community/mathlib/pull/1133#pullrequestreview-250179914

### [2019-06-17 13:09:55](https://github.com/leanprover-community/mathlib/commit/d8d25e9)
refactor(analysis/normed_space/deriv): split and move to calculus folder ([#1135](https://github.com/leanprover-community/mathlib/pull/1135))

### [2019-06-16 19:28:43](https://github.com/leanprover-community/mathlib/commit/7b715eb)
Direct limit of modules, abelian groups, rings, and fields. ([#754](https://github.com/leanprover-community/mathlib/pull/754))
* stuff
* stuff
* more stuff
* pre merge commit
* prove of_zero.exact
* remove silly rewrite
* slightly shorten proof
* direct limit of modules
* upgrade mathlib
* direct limit of rings
* direct limit of fields (WIP)
* trying to prove zero_exact for rings
* use sqrt 2 instead of F4
* direct limit of field
* cleanup for mathlib
* remove ununsed lemmas
* clean up
* docstrings
* local
* fix build
* Replace real with polynomial int in proof
* Update basic.lean

### [2019-06-16 19:04:52](https://github.com/leanprover-community/mathlib/commit/38d5c12)
feat(ring_theory/integral_closure): integral closure ([#1087](https://github.com/leanprover-community/mathlib/pull/1087))
* feat(ring_theory/integral_closure): integral closure
* update

### [2019-06-15 01:30:00](https://github.com/leanprover-community/mathlib/commit/3ad3522)
feat(data/rat/denumerable): computable denumerability of Q ([#1104](https://github.com/leanprover-community/mathlib/pull/1104))
* feat(data/rat/denumerable): computable denumerability of Q
* blah
* fix build
* remove unnecessary decidable_eq
* add header
* delete rat.lean and update imports
* fix build
* prove exists_not_mem_finset
* massively speed up encode
* minor change

### [2019-06-14 17:40:58](https://github.com/leanprover-community/mathlib/commit/5040c81)
feat(measure_theory/integration): dominated convergence theorem ([#1123](https://github.com/leanprover-community/mathlib/pull/1123))
* Create .DS_Store
* Revert "Create .DS_Store"
This reverts commit 5612886d493aef59205eddc5a34a75e6e5ba22c1.
* feat(measure_theory/integration): dominated convergence theorem
* Changes to styles
* Update ordered.lean
* Changes to styles
* Update integration.lean
* Changes to styles

### [2019-06-14 13:35:52](https://github.com/leanprover-community/mathlib/commit/5a183f0)
provide some proof terms explicitly ([#1132](https://github.com/leanprover-community/mathlib/pull/1132))

### [2019-06-12 04:45:45](https://github.com/leanprover-community/mathlib/commit/0c627fb)
chore(algebra/group/hom): drop unused section variables ([#1130](https://github.com/leanprover-community/mathlib/pull/1130))

### [2019-06-11 21:06:39](https://github.com/leanprover-community/mathlib/commit/3492206)
feat(data/mv_polynomial): misc lemmas on rename, map, and eval2 ([#1127](https://github.com/leanprover-community/mathlib/pull/1127))

### [2019-06-11 19:10:13](https://github.com/leanprover-community/mathlib/commit/953c612)
fix(category_theory): simplifying universes ([#1122](https://github.com/leanprover-community/mathlib/pull/1122))

### [2019-06-11 17:46:50](https://github.com/leanprover-community/mathlib/commit/98ece77)
refactor(algebra/group): split into smaller files ([#1121](https://github.com/leanprover-community/mathlib/pull/1121))
* rename `src/algebra/group.lean` → `src/algebra/group/default.lean`
* Split algebra/group/default into smaller files
No code changes, except for variables declaration and imports
* Fix compile
* fix compile error: import `anti_hom` in `algebra/group/default`
* Drop unused imports

### [2019-06-11 12:53:04-04:00](https://github.com/leanprover-community/mathlib/commit/8d0e719)
chore(mergify): don't dismiss reviews [ci-skip] ([#1124](https://github.com/leanprover-community/mathlib/pull/1124))

### [2019-06-11 04:39:39](https://github.com/leanprover-community/mathlib/commit/abfaf8d)
refactor(group_theory/abelianization): simplify abelianization  ([#1126](https://github.com/leanprover-community/mathlib/pull/1126))
* feat(group_theory/conjugates) : define conjugates
define group conjugates and normal closure
* feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/1022))
* trying to merge
* feat(group_theory\presented_group):  define presented groups
Presented groups are defined as a quotient of a free group by the normal subgroup  the relations generate.
* feat(group_theory\presented_group): define presented groups
Presented groups are defined as a quotient of a free group by the normal subgroup  the relations generate
* Update src/group_theory/presented_group.lean
Co-Authored-By: Keeley Hoek <keeley@hoek.io>
* Uniqueness of extension
* Tidied up to_group.unique
* Removed unnecessary line
* Changed naming
* refactor(group_theory/abelianization): simplify abelianization
The commutator of a group was previously defined using lists.
Now it is defined using `normal_closure`.
This change simplifies some of the proofs

### [2019-06-10 13:38:37](https://github.com/leanprover-community/mathlib/commit/bd2f35f)
feat(group_theory/presented_group): define presented groups ([#1118](https://github.com/leanprover-community/mathlib/pull/1118))
* feat(group_theory/conjugates) : define conjugates
define group conjugates and normal closure
* feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/1022))
* trying to merge
* feat(group_theory\presented_group):  define presented groups
Presented groups are defined as a quotient of a free group by the normal subgroup  the relations generate.
* feat(group_theory\presented_group): define presented groups
Presented groups are defined as a quotient of a free group by the normal subgroup  the relations generate
* Update src/group_theory/presented_group.lean
Co-Authored-By: Keeley Hoek <keeley@hoek.io>
* Uniqueness of extension
* Tidied up to_group.unique
* Removed unnecessary line
* Changed naming

### [2019-06-10 08:38:52+01:00](https://github.com/leanprover-community/mathlib/commit/004e0b3)
feat (data/pnat): extensions to pnat  ([#1073](https://github.com/leanprover-community/mathlib/pull/1073))
* Extended API, especially divisibility and primes
* Positive euclidean algorithm
* Disambiguate overloaded ::
* Tweak broken proof of flip_is_special
* Change to mathlib style
* Update src/data/pnat.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/data/pnat.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Adjust style for mathlib
* Moved and renamed
* Move some material from basic.lean to prime.lean
* Move some material from basic.lean to factors.lean
* Update import to data.pnat.basic.
* Update import to data.pnat.basic
* Fix import of data.pnat.basic
* Use monoid.pow instead of nat.pow
* Fix pnat.pow_succ -> pow_succ; stylistic changes
* More systematic use of coercion
* More consistent use of coercion
* Formatting; change flip' to prod.swap

### [2019-06-08 23:11:29](https://github.com/leanprover-community/mathlib/commit/3f9916e)
feat(tactic/rewrite_all): tactic to perform the nth occurrence of a rewrite ([#999](https://github.com/leanprover-community/mathlib/pull/999))
* feat(tactic/rewrite_all): tactic to perform the nth occurrence of a rewrite
* formatting
* formatting
* perhaps a little bit easier to read?
* try renaming
* there was a duplicate definition, just not the one lean complained about
* Namespaces
* I think kabstract works now
* Fix
* Test
* Fix guard
* updating test to reflect difference between congr and kabstract
* oops
* adding Keeley's example
* remove kabstract implementation for now
* cleanup test file
* rename common to basic
* Update src/tactic/rewrite_all/default.lean

### [2019-06-07 16:54:39](https://github.com/leanprover-community/mathlib/commit/b55e44d)
refactor(analysis/normed_space/basic): change normed_space definition ([#1112](https://github.com/leanprover-community/mathlib/pull/1112))

### [2019-06-07 15:21:25](https://github.com/leanprover-community/mathlib/commit/85ed958)
feat(data/quot): quot.map: act on non-id maps ([#1120](https://github.com/leanprover-community/mathlib/pull/1120))
* old version renamed to `quot.map_right`
* similar changes to `quot.congr` and `quotient.congr`

### [2019-06-06 16:45:38](https://github.com/leanprover-community/mathlib/commit/f36fdfb)
refactor(category_theory/equivalence): simplify equivalence.trans ([#1114](https://github.com/leanprover-community/mathlib/pull/1114))

### [2019-06-05 07:54:30](https://github.com/leanprover-community/mathlib/commit/a7524b6)
refactor(analysis/normed_space/operator_norm): topological modules ([#1085](https://github.com/leanprover-community/mathlib/pull/1085))
* refactor(analysis/normed_space/operator_norm): topological modules
* remove useless typeclass in definition of topological module
* refactor(analysis/normed_space/operator_norm): style

### [2019-06-04 20:49:06](https://github.com/leanprover-community/mathlib/commit/a152f3a)
chore(doc/install/macos): improve mac install instructions ([#1106](https://github.com/leanprover-community/mathlib/pull/1106))
* tweaking install instructions
* minor
* minor
* minor
* minor
* small icon
* improve instructions for installing the extension on all OSes
* minor

### [2019-06-04 14:48:57+01:00](https://github.com/leanprover-community/mathlib/commit/542d25d)
fix(data/logic/basic): Use a Sort for classical.some_spec2 ([#1111](https://github.com/leanprover-community/mathlib/pull/1111))

### [2019-06-03 22:11:39](https://github.com/leanprover-community/mathlib/commit/dd832f0)
feat(topology/basic): is_open_Inter and others ([#1108](https://github.com/leanprover-community/mathlib/pull/1108))

### [2019-06-03 20:36:09](https://github.com/leanprover-community/mathlib/commit/504c0ad)
feat(data/set/basic): union_inter_distrib lemmas ([#1107](https://github.com/leanprover-community/mathlib/pull/1107))
* feat(data/set/basic): union_inter_distrib lemmas
* add parentheses

### [2019-06-03 18:05:35](https://github.com/leanprover-community/mathlib/commit/4263b2b)
fix(data/nat/gcd): correct order of arguments in nat.coprime_mul_iff_right ([#1105](https://github.com/leanprover-community/mathlib/pull/1105))
* Not sure how this works
* Fix order for coprime_mul_iff_right
* Remove spurious file

### [2019-06-01 20:38:34](https://github.com/leanprover-community/mathlib/commit/38b8054)
feat(data/mv_polynomial): add coeff for mv_polynomial ([#1101](https://github.com/leanprover-community/mathlib/pull/1101))