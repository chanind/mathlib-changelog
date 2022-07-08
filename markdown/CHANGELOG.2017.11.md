### [2017-11-30 22:10:19-05:00](https://github.com/leanprover-community/mathlib/commit/f57e59f)
feat(data/analysis): calculations with filters / topologies + misc

### [2017-11-30 22:10:19-05:00](https://github.com/leanprover-community/mathlib/commit/b207991)
refactor(data/multiset): move multiset, finset, ordered_monoid

### [2017-11-30 22:10:19-05:00](https://github.com/leanprover-community/mathlib/commit/f9b6671)
Revert "fix(algebra/group): workaround for [#1871](https://github.com/leanprover-community/mathlib/pull/1871)"
This reverts commit b9dcc64a998c417551d95f3b0d9b8ee8b690d21b.

### [2017-11-28 19:14:05+01:00](https://github.com/leanprover-community/mathlib/commit/67aecac)
fix(data/option): adapt to https://github.com/leanprover/lean/commit/f6b113849b367d49fc4a506f0698c7f1e062851e

### [2017-11-24 05:22:02-05:00](https://github.com/leanprover-community/mathlib/commit/2c84af1)
feat(data/set/finite): unify fintype and finite developments
Here fintype is the "constructive" one, which exhibits a list enumerating the set (quotiented over permutations), while "finite" merely states the existence of such a list.

### [2017-11-24 05:19:35-05:00](https://github.com/leanprover-community/mathlib/commit/e576429)
feat(data/multiset): filter_map

### [2017-11-24 05:18:50-05:00](https://github.com/leanprover-community/mathlib/commit/bade51a)
feat(data/quot): add trunc type (like nonempty in Type)
It is named after the propositional truncation operator in HoTT, although of course the behavior is a bit different in a proof irrelevant setting.

### [2017-11-23 23:33:09-05:00](https://github.com/leanprover-community/mathlib/commit/16d40d7)
feat(data/finset): fintype, multiset.sort, list.pmap

### [2017-11-23 22:09:45-05:00](https://github.com/leanprover-community/mathlib/commit/c03c16d)
feat(algebra/group_power): remove overloaded ^ notation, add smul

### [2017-11-23 06:50:37-05:00](https://github.com/leanprover-community/mathlib/commit/33aa50b)
feat(tactic/generalize_proofs): generalize proofs tactic
Borrowed from leanprover/lean[#1704](https://github.com/leanprover-community/mathlib/pull/1704)

### [2017-11-22 05:33:59-05:00](https://github.com/leanprover-community/mathlib/commit/902b94d)
refactor(data/finset): redefine finsets as subtype of multisets

### [2017-11-22 05:32:47-05:00](https://github.com/leanprover-community/mathlib/commit/df546eb)
feat(data/set/basic): add coercion from set to type

### [2017-11-22 05:26:27-05:00](https://github.com/leanprover-community/mathlib/commit/d548725)
feat(tactic/rcases): support 'rfl' in rcases patterns for subst
Using the special keyword `rfl` in an rcases pattern, as in `rcases h with ⟨a, rfl⟩ | b`, will now perform `subst` on the indicated argument, when it is an equality.

### [2017-11-20 20:36:26-05:00](https://github.com/leanprover-community/mathlib/commit/b9dcc64)
fix(algebra/group): workaround for [#1871](https://github.com/leanprover-community/mathlib/pull/1871)
Currently, user attributes are not stored in `olean` files, which leads to segfault issues when referencing them using `user_attribute.get_param`. To work around this, we duplicate the stored data in an extra `def`, which *is* stored in the `olean` file.

### [2017-11-20 01:30:51-05:00](https://github.com/leanprover-community/mathlib/commit/40d2b50)
fix(algebra/order): update to lean
The new `not_lt_of_lt` in core is not substitutable for this one because it is in the new algebraic hierarchy and mathlib is still on the old one. But this isn't used anywhere, so I'll just remove it instead of renaming.

### [2017-11-20 01:09:21-05:00](https://github.com/leanprover-community/mathlib/commit/f467c81)
feat(data/multiset): disjoint, nodup, finset ops

### [2017-11-19 21:14:37-05:00](https://github.com/leanprover-community/mathlib/commit/76a5fea)
fix(*): finish converting structure notation to {, ..s} style

### [2017-11-19 19:49:02-05:00](https://github.com/leanprover-community/mathlib/commit/5d65b0a)
fix(algebra/ring): update to lean

### [2017-11-19 05:53:48-05:00](https://github.com/leanprover-community/mathlib/commit/8067812)
feat(data/multiset): filter, count, distrib lattice

### [2017-11-19 00:41:14-05:00](https://github.com/leanprover-community/mathlib/commit/f9de183)
feat(data/multiset): working on multisets, fix rcases bug

### [2017-11-18 23:18:32-05:00](https://github.com/leanprover-community/mathlib/commit/d579a56)
fix(*): update to lean

### [2017-11-15 13:52:33-05:00](https://github.com/leanprover-community/mathlib/commit/6e9d2d5)
fix(data/num): update to lean

### [2017-11-10 11:32:15+01:00](https://github.com/leanprover-community/mathlib/commit/afddab6)
chore(algebra/module): hide ring parameters, vector_space is no a proper class, remove dual, change variables to implicits
the ring type is often unnecessary it can be computed from the module instance. Also a lot of parameters to lemmas should be implicits as they can be computed from assumptions or the expteced type..
@kckennylau: I removed `dual` as it does not make sense to take about all possible *module structures* possible on the function space `linear_map α β α`. I guess `dual` should be just `linear_map α β α`.

### [2017-11-10 05:26:42-05:00](https://github.com/leanprover-community/mathlib/commit/0f8a5c8)
refactor(algebra/group): Use a user attr for to_additive
Parts of this commit are redundant pending leanprover/lean[#1857](https://github.com/leanprover-community/mathlib/pull/1857) .

### [2017-11-09 12:33:00+01:00](https://github.com/leanprover-community/mathlib/commit/04dd132)
feat(algebra/big_operators): exists_ne_(one|zero)_of_(prod|sum)_ne_(one|zero)

### [2017-11-09 12:33:00+01:00](https://github.com/leanprover-community/mathlib/commit/5923cd0)
feat(data/set/finite): finite_of_finite_image

### [2017-11-07 19:26:04-05:00](https://github.com/leanprover-community/mathlib/commit/d95bff0)
refactor(data/hash_map): improve hash_map proof
Decrease dependence on implementation details of `array`

### [2017-11-07 06:09:41-05:00](https://github.com/leanprover-community/mathlib/commit/4ae6a57)
fix(data/array): update to lean

### [2017-11-06 11:35:36+01:00](https://github.com/leanprover-community/mathlib/commit/2bc7fd4)
feat(data/cardinal): theory for cardinal arithmetic

### [2017-11-06 03:28:38-05:00](https://github.com/leanprover-community/mathlib/commit/d62cefd)
refactor(algebra/module): clean up PR commit

### [2017-11-06 01:31:01-05:00](https://github.com/leanprover-community/mathlib/commit/5cb7fb0)
feat(algebra/vector_space): modules and vector spaces, linear spaces

### [2017-11-06 01:26:58-05:00](https://github.com/leanprover-community/mathlib/commit/0947f96)
feat(data/multiset): working on multiset.union

### [2017-11-05 17:42:46-05:00](https://github.com/leanprover-community/mathlib/commit/2aa6c87)
feat(tactic/norm_num): add support for inv and locations in norm_num

### [2017-11-05 01:30:21-04:00](https://github.com/leanprover-community/mathlib/commit/d743fdf)
feat(data/sigma): duplicate sigma basics for psigma

### [2017-11-05 00:29:59-05:00](https://github.com/leanprover-community/mathlib/commit/8e99f98)
fix(algebra/field): update to lean

### [2017-11-02 17:13:43-04:00](https://github.com/leanprover-community/mathlib/commit/2da9bef)
feat(data/nat/cast,...): add char_zero typeclass for cast_inj
As pointed out by @kbuzzard, the complex numbers are an important example of an unordered characteristic zero field for which we will want cast_inj to be available.

### [2017-11-02 02:32:37-04:00](https://github.com/leanprover-community/mathlib/commit/2883c1b)
feat(data/num/lemmas): finish znum isomorphism proof

### [2017-11-02 00:06:37-04:00](https://github.com/leanprover-community/mathlib/commit/efb37f8)
fix(theories/set_theory): workaround for noncomputability bug in lean

### [2017-11-01 22:19:53-04:00](https://github.com/leanprover-community/mathlib/commit/0c0c007)
test(tests/norm_num): more tests from [#16](https://github.com/leanprover-community/mathlib/pull/16)

### [2017-11-01 22:14:14-04:00](https://github.com/leanprover-community/mathlib/commit/7339f59)
fix(tactic/norm_num): bugfix

### [2017-11-01 21:23:52-04:00](https://github.com/leanprover-community/mathlib/commit/5a262df)
fix(tactic/norm_num): fix performance bug in norm_num

### [2017-11-01 04:36:53-04:00](https://github.com/leanprover-community/mathlib/commit/6eedc0e)
feat(tactic/norm_num): rewrite norm_num to use simp instead of reflection

### [2017-11-01 04:35:13-04:00](https://github.com/leanprover-community/mathlib/commit/0663945)
feat(data/num,data/multiset): more properties of binary numbers, begin multisets