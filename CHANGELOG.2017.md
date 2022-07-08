### [2017-12-31T16:53:38-05:00](https://github.com/leanprover-community/mathlib/commit/1bc2ac7aa0aa2c7e5df6238761e0a2c088905f8f)
feat(data/ordinal): is_normal, omin, power/log, CNF, indecomposables,

addition and multiplication of infinite cardinals

### [2017-12-23T10:06:18-05:00](https://github.com/leanprover-community/mathlib/commit/0abe0860e64fd7f6dd64183bb77822941e265a82)
feat(data/ordinal): mul, div, mod, dvd, sub, power

### [2017-12-21T06:51:34-05:00](https://github.com/leanprover-community/mathlib/commit/5f4d89097e6034af7077882e2e9061f49c0e0b24)
feat(data/ordinal): omega is least limit ordinal

### [2017-12-20T23:25:17-05:00](https://github.com/leanprover-community/mathlib/commit/49a63b7464df04e216ad1ff353b306ca157119f8)
refactor(data/ordinal): rearrange files, more cofinality

### [2017-12-19T04:59:43-05:00](https://github.com/leanprover-community/mathlib/commit/7726a92f0b17a3295aed61e3a362ce7ef21c7fb0)
feat(data/ordinal): sup, cofinality, subtraction

### [2017-12-18T08:38:41-05:00](https://github.com/leanprover-community/mathlib/commit/f6bbca7100b9c5e2f3a96d9998504ba365b7d80c)
feat(data/ordinal): universe lifts, alephs

### [2017-12-17T14:11:42-05:00](https://github.com/leanprover-community/mathlib/commit/52330fa0043382e907d9a54ac1f2baae89d0fc00)
fix(data/ordinal): update to lean

### [2017-12-17T04:47:45-05:00](https://github.com/leanprover-community/mathlib/commit/dba8d0e5fe1328e9272c7021092ce2ef224d8ab5)
fix(data/ordinal): fix unsound proof

here's hoping lean will notice that the last proof is not correct

### [2017-12-17T02:45:25-05:00](https://github.com/leanprover-community/mathlib/commit/b19c222c0b267a4ecc9ae869cd072f4efecb2f96)
feat(data/ordinal): ordinal collapse, ordinals ordering,

### [2017-12-15T22:45:11-05:00](https://github.com/leanprover-community/mathlib/commit/95507bfb8a7751e5ed940d514a9ddb3bf8819f9d)
chore(algebra/module): update to lean

inout => out_param

### [2017-12-15T13:40:09+01:00](https://github.com/leanprover-community/mathlib/commit/01f1d23078c861148b910e52c6fe644780494794)
refactor(style.md): copy naming conventions from the library_dev repository.

### [2017-12-14T21:29:14+01:00](https://github.com/leanprover-community/mathlib/commit/79483182abffcac3a1ddd7098d47a475e75a5ed2)
feat(logic/basic): add rewrite rules for nonempty

### [2017-12-14T12:50:11+01:00](https://github.com/leanprover-community/mathlib/commit/d27f7ac4a122418d8ef6e77659d47508b9c0ba11)
chore(style.md): rename and some cleanup

### [2017-12-14T12:42:51+01:00](https://github.com/leanprover-community/mathlib/commit/f8476fd98d5a896e89f3eaf1771ded647a759844)
feat(library_style): resurrecting Jeremy's library_style.org as md file

### [2017-12-14T11:39:08+01:00](https://github.com/leanprover-community/mathlib/commit/0f50ba7abd907ce61185d0f64679bb6da7236796)
feat(.travis.yml): export and run leanchecker

This should detect multiple definitions with the same name as in [#27](https://github.com/leanprover-community/mathlib/pull/#27).

### [2017-12-14T11:13:01+01:00](https://github.com/leanprover-community/mathlib/commit/86e494d90e5a20a2e2e76afaf0d7ec69eafc7cba)
fix(data/encodable): make decidable_eq_of_encodable priority 0

### [2017-12-14T11:08:41+01:00](https://github.com/leanprover-community/mathlib/commit/2dbf07a8467fa691f0cdbb2f1ea2aef62bac4541)
chore(.): adapt to change `by_cases t with h` to  `by_cases h : t` 746134d11ceec378a53ffd3b7ab8626fb291f3bd

### [2017-12-13T17:34:22+01:00](https://github.com/leanprover-community/mathlib/commit/ea197760de6d7c3dae284cfa1a47c55ff7716959)
refactor(data/finsupp): generalize module construction for finsupp

### [2017-12-13T16:52:33+01:00](https://github.com/leanprover-community/mathlib/commit/b29ab1b5fa5f4690b16bf440eed63be25ee5dbf2)
feat(data/finsupp): add support_neg

### [2017-12-13T13:09:54+01:00](https://github.com/leanprover-community/mathlib/commit/a2d61482871148f09429132bae0834ac3cec1d26)
feat(algebra/linear_algebra): add multivariate polynomials

### [2017-12-13T13:09:17+01:00](https://github.com/leanprover-community/mathlib/commit/8369c7d833caa932133ff40eaab5d0c691489329)
feat(data/finsupp): big product over finsupp (big sum is now derived from it)

### [2017-12-13T12:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/421c332e990317e0429ea17a025d06723c25e248)
fix(algebra/big_operators): congruence rules need to provide equations for all rewritable positions

### [2017-12-13T12:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/81908b045d31e0bc07f9357e4f2037f32f528a72)
chore(algebra/linear_algebra): second isomorphism proof

### [2017-12-13T04:31:56-05:00](https://github.com/leanprover-community/mathlib/commit/a2437102ac0045a6c639f70d3d93308d7c784e4b)
feat(data/ordinal): well ordering theorem

Note to self: this proof seems more cumbersome than it should be. I will see if the proof is easier if we bypass Zorn's lemma.

### [2017-12-12T16:06:26-05:00](https://github.com/leanprover-community/mathlib/commit/bd99ad7e8b7f1e74cc80f94a00941322efb6daec)
feat(data/fin): fin.succ.inj

### [2017-12-11T23:34:49-05:00](https://github.com/leanprover-community/mathlib/commit/d3149badf73c869774e0bbf44c60642304ceff0b)
fix(*): update to lean

### [2017-12-11T12:19:07-05:00](https://github.com/leanprover-community/mathlib/commit/6b10d8d67b240711e7569c56f99144e9f6f304c4)
chore(tests/finish3): rename definition with same name

### [2017-12-11T12:19:07-05:00](https://github.com/leanprover-community/mathlib/commit/be79f9f38130ec30ef23e068dfb755b0eb6bf41c)
chore(data/cardinal): put embedding into cardinal namespace

### [2017-12-11T14:09:28+01:00](https://github.com/leanprover-community/mathlib/commit/ee7ede9e4a35f392c6df5b6fa55eb2f424c59c3d)
feat(algebra/linear_algebra): proof first and second isomorphism laws

### [2017-12-11T14:09:28+01:00](https://github.com/leanprover-community/mathlib/commit/01c3b8f36307571f68bc7dfb0a1d469190332769)
feature(algebra/linear_algebra): define linear equivalence

### [2017-12-11T14:09:28+01:00](https://github.com/leanprover-community/mathlib/commit/85a16677042a24864493475734bbb55907d1dc2a)
refactor(data/equiv): state refl, symm, and trans rules for equiv using projection. This gives more powerful rfl rules

### [2017-12-11T05:07:46-05:00](https://github.com/leanprover-community/mathlib/commit/03074f197cb6f832eade66220f49ed999deec768)
feat(data/ordinal): more ordinals

### [2017-12-10T08:36:32-05:00](https://github.com/leanprover-community/mathlib/commit/a758ffb3f743eca79da54b13f1ced916d5cdbacf)
feat(data/ordinal): ordinal numbers

### [2017-12-09T22:14:32-05:00](https://github.com/leanprover-community/mathlib/commit/aef5c88d9d99a115133f362061746488f790ddfb)
feat(algebra/group_power): more gpow lemmas

### [2017-12-08T17:29:17+01:00](https://github.com/leanprover-community/mathlib/commit/8cfcef09db80f8c57f2ca30da3221815560a149f)
feat(algebra/linear_algebra): add product construction for modules

### [2017-12-08T17:29:17+01:00](https://github.com/leanprover-community/mathlib/commit/8fab107c0cfb35f580c126eb736b993616be6adf)
refactor(algebra/module): split of type constructions and move quotient, subtype and linear_map to their own theories in algebra/linear_algebra

### [2017-12-08T17:29:17+01:00](https://github.com/leanprover-community/mathlib/commit/fccc5d3219cec479b8b9c337ac35799f3ddfc6eb)
refactor(algebra/linear_algebra): move zero_not_mem_of_linear_independent from vector_space to module (zero_ne_one should be a typeclass in Prop not in Type)

### [2017-12-08T08:32:13-05:00](https://github.com/leanprover-community/mathlib/commit/bd013e8089378e8057dc7e93c9eaf2c8ebaf25a2)
feat(data/dardinal): wellordering of cardinals

### [2017-12-08T10:51:42+01:00](https://github.com/leanprover-community/mathlib/commit/b547de03076755ef33bc354c0362e74745bbb42d)
chore(data/finsupp): replace { n with ... } syntax with { ..., .. n } (the former is deprecated)

### [2017-12-08T10:48:54+01:00](https://github.com/leanprover-community/mathlib/commit/e1e80b499a465703f59612938ad0749d942a5fa1)
chore(.): replace ginduction by induction; changed in lean revision 49e7a642c35e83ed16cbc573deef5bd3b6dfc627

### [2017-12-07T17:25:25+01:00](https://github.com/leanprover-community/mathlib/commit/c32d01d7ffa15f67e06b08daa340e273590f5e8b)
feat(algebra/linear_algebra): add basic theory on linear algebra

### [2017-12-07T17:24:30+01:00](https://github.com/leanprover-community/mathlib/commit/f09abb1c47a846c33c0e996ffa9bf12951b40b15)
feat(data/finsupp): add type of functions with finite support

### [2017-12-07T17:22:37+01:00](https://github.com/leanprover-community/mathlib/commit/fcf0bfa8a6fb3eb5a550675b83c4aeb78458f275)
feat(data/set/finite): add finite_to_set, finset.coe_to_finset

### [2017-12-07T17:18:54+01:00](https://github.com/leanprover-community/mathlib/commit/5e42425d0e0af031441f4df207703009b08ad7a1)
fix(algebra/module): fix type universes in is_linear_map.sum

### [2017-12-07T14:42:09+01:00](https://github.com/leanprover-community/mathlib/commit/0995ac197ea4ce1fb57c3d94647427456604bb85)
feat(algebra/module): the inverse of a linear map is linear

### [2017-12-07T14:04:24+01:00](https://github.com/leanprover-community/mathlib/commit/645bf6049528d8bc0d2c853289e0e28979047a69)
core(algebra/module): generalize map_smul_left; add is_submodule.range

### [2017-12-07T00:39:32-05:00](https://github.com/leanprover-community/mathlib/commit/5f642d8346e5b31e898ef3419d7b1a8616c9630c)
refactor(*): remove local simp AC lemmas

Using local simp lemmas everywhere for mul_assoc and friends defeats the purpose of the change in core. Now theorems are proven with only the AC lemmas actually used in the proof.

### [2017-12-06T17:16:14+01:00](https://github.com/leanprover-community/mathlib/commit/a3a2faa916c983360999051f7f6af471faa498c0)
feat(algebra/big_operators): add renameing rules under bijection

### [2017-12-06T16:48:38+01:00](https://github.com/leanprover-community/mathlib/commit/e5c4eb1b4a6eee879a321a15807e74f8cd709cbb)
feat(data/set): add lift converting finset to set

### [2017-12-06T16:42:20+01:00](https://github.com/leanprover-community/mathlib/commit/7f9dd51f4694406774c2c213ec4cd70319a37f2e)
feat(data/finset): add strong induction rules for finset

### [2017-12-06T16:21:41+01:00](https://github.com/leanprover-community/mathlib/commit/81e53e8325923130bf29fb9680a4a1dc0a91a324)
feat(data/finset): add ssubset

### [2017-12-06T13:30:50+01:00](https://github.com/leanprover-community/mathlib/commit/f9b39eb160e052adfce9c240ce0547da468309da)
feature(.): add various theorems

### [2017-12-06T06:02:26-05:00](https://github.com/leanprover-community/mathlib/commit/fd803b665515f4eb0e7dc5100cad1ec6a4a0563e)
chore(.): adapt to change bc89ebc19c93392419b7bab8b68271db12855dc5 (improve how induction hypotheses are named)

### [2017-12-05T15:23:53-05:00](https://github.com/leanprover-community/mathlib/commit/c43e01321f24f6e58f9f24e7ebefac0e76c87421)
fix(theories/number_theory/pell,*): fix broken proofs, less simp AC

### [2017-12-05T18:39:28+01:00](https://github.com/leanprover-community/mathlib/commit/e9e51dba1ac40cc660451c67a689a73cb64c1d26)
fix(data/sigma): use Sort for psigma

### [2017-12-05T18:13:32+01:00](https://github.com/leanprover-community/mathlib/commit/0e3b1567f4988bb62cb24e2e656284119aed5b08)
fix(algebra/module): remove instance endomorphism_ring, it breaks real.lean

### [2017-12-05T18:03:32+01:00](https://github.com/leanprover-community/mathlib/commit/394d7213131e8c63a1675b68ca401943db1e6fa8)
feat(algebra/module): add quotient module

### [2017-12-05T17:24:36+01:00](https://github.com/leanprover-community/mathlib/commit/dcfb9a01868dd633ab5d07cd8385cf11697b483e)
refactor(algebra/module): add is_linear_map as predicate

### [2017-12-05T14:35:49+01:00](https://github.com/leanprover-community/mathlib/commit/88202b6c30d26ec39915699848f74fd790a10295)
refactor(algebra/module): clean up is_submodule projections

### [2017-12-05T14:15:07+01:00](https://github.com/leanprover-community/mathlib/commit/90ed0ab121e340397c3105a12ce89df77da14c69)
refactor(algebra/module): rename submodule -> is_submodule, smul_left_distrib -> smul_add, smul_right_distrib -> add_smul, smul_sub_left_distrib -> smul_sub, sub_smul_right_distrib -> sub_smul

### [2017-12-05T12:33:55+01:00](https://github.com/leanprover-community/mathlib/commit/6ebe286e56dd8180533afb326e253296d734af17)
refactor(.): use new funext tactic

### [2017-12-05T12:04:46+01:00](https://github.com/leanprover-community/mathlib/commit/827353636bf6b46026e266c55c453764db16e0f3)
chore(.): adapt to change 6d96741010f5f36f2f4f046e4b2b8276eb2b04d4 (provide names for constructor arguments)

### [2017-12-05T11:24:13+01:00](https://github.com/leanprover-community/mathlib/commit/f6474f0c6ed4cf35d21ee6f77900dde9a8fc37f8)
chore(.): adapt to change b7322e28c12d274ccec992b7fc49d35b2e56a2a4 (remove AC simp rules)

### [2017-12-04T23:24:01-05:00](https://github.com/leanprover-community/mathlib/commit/2dadfdbb4d72b01918a32ac375cce2c617e3120d)
feat(tactic/norm_num): add {nat,int}.mod

### [2017-12-04T23:05:57-05:00](https://github.com/leanprover-community/mathlib/commit/8d27f70b1c241925406184a34a1a18cc0fa79249)
feat(tactic/norm_num): add support for {nat,int}.div

### [2017-12-04T21:23:11-05:00](https://github.com/leanprover-community/mathlib/commit/b1981c9407c467f40679179bb63b5b925fe5dbc9)
chore(theories/number_theory/dioph): cleanup

### [2017-12-01T08:02:15-05:00](https://github.com/leanprover-community/mathlib/commit/7191e39163e5d2338b85cf8d71848e55dd6b07ad)
feat(theories/number_theory/dioph): Pell equation, diophantine equations

### [2017-11-30T22:10:19-05:00](https://github.com/leanprover-community/mathlib/commit/f57e59f4100d5485ee840e114624886f1a37c985)
feat(data/analysis): calculations with filters / topologies + misc

### [2017-11-30T22:10:19-05:00](https://github.com/leanprover-community/mathlib/commit/b207991ba00491e98ec65d00b90bdede8f2a1ef0)
refactor(data/multiset): move multiset, finset, ordered_monoid

### [2017-11-30T22:10:19-05:00](https://github.com/leanprover-community/mathlib/commit/f9b66717082ca8f0c7ba015fbd7dfddd9ef206f3)
Revert "fix(algebra/group): workaround for [#1871](https://github.com/leanprover-community/mathlib/pull/#1871)"

This reverts commit b9dcc64a998c417551d95f3b0d9b8ee8b690d21b.

### [2017-11-28T19:14:05+01:00](https://github.com/leanprover-community/mathlib/commit/67aecac0925c6d45dae94a765aff20008997ae24)
fix(data/option): adapt to https://github.com/leanprover/lean/commit/f6b113849b367d49fc4a506f0698c7f1e062851e

### [2017-11-24T05:22:02-05:00](https://github.com/leanprover-community/mathlib/commit/2c84af163dbc83c6eb6a94a03d5c25f25b6b8623)
feat(data/set/finite): unify fintype and finite developments

Here fintype is the "constructive" one, which exhibits a list enumerating the set (quotiented over permutations), while "finite" merely states the existence of such a list.

### [2017-11-24T05:19:35-05:00](https://github.com/leanprover-community/mathlib/commit/e57642914857d1255d8dd86f94ccb75612ceec33)
feat(data/multiset): filter_map

### [2017-11-24T05:18:50-05:00](https://github.com/leanprover-community/mathlib/commit/bade51a03d37af8af135ada7688b5c5c42feca06)
feat(data/quot): add trunc type (like nonempty in Type)

It is named after the propositional truncation operator in HoTT, although of course the behavior is a bit different in a proof irrelevant setting.

### [2017-11-23T23:33:09-05:00](https://github.com/leanprover-community/mathlib/commit/16d40d7491d1fe8a733d21e90e516e0dd3f41c5b)
feat(data/finset): fintype, multiset.sort, list.pmap

### [2017-11-23T22:09:45-05:00](https://github.com/leanprover-community/mathlib/commit/c03c16d6fb81d23761227a56e6f39d7baddb9bc1)
feat(algebra/group_power): remove overloaded ^ notation, add smul

### [2017-11-23T06:50:37-05:00](https://github.com/leanprover-community/mathlib/commit/33aa50bf6759ea33a19ea243e6dd1d1e5b36ca1d)
feat(tactic/generalize_proofs): generalize proofs tactic

Borrowed from leanprover/lean[#1704](https://github.com/leanprover-community/mathlib/pull/#1704)

### [2017-11-22T05:33:59-05:00](https://github.com/leanprover-community/mathlib/commit/902b94d3075b44601d2ee4bd74898510a0aa26ed)
refactor(data/finset): redefine finsets as subtype of multisets

### [2017-11-22T05:32:47-05:00](https://github.com/leanprover-community/mathlib/commit/df546eb0ad8991b170561dbdcfcad36aa983ccec)
feat(data/set/basic): add coercion from set to type

### [2017-11-22T05:26:27-05:00](https://github.com/leanprover-community/mathlib/commit/d548725593006da2c31b3032c80119f4b48c35d3)
feat(tactic/rcases): support 'rfl' in rcases patterns for subst

Using the special keyword `rfl` in an rcases pattern, as in `rcases h with ⟨a, rfl⟩ | b`, will now perform `subst` on the indicated argument, when it is an equality.

### [2017-11-20T20:36:26-05:00](https://github.com/leanprover-community/mathlib/commit/b9dcc64a998c417551d95f3b0d9b8ee8b690d21b)
fix(algebra/group): workaround for [#1871](https://github.com/leanprover-community/mathlib/pull/#1871)

Currently, user attributes are not stored in `olean` files, which leads to segfault issues when referencing them using `user_attribute.get_param`. To work around this, we duplicate the stored data in an extra `def`, which *is* stored in the `olean` file.

### [2017-11-20T01:30:51-05:00](https://github.com/leanprover-community/mathlib/commit/40d2b505181d1be50fc948d4d0e0591bfa14e2fe)
fix(algebra/order): update to lean

The new `not_lt_of_lt` in core is not substitutable for this one because it is in the new algebraic hierarchy and mathlib is still on the old one. But this isn't used anywhere, so I'll just remove it instead of renaming.

### [2017-11-20T01:09:21-05:00](https://github.com/leanprover-community/mathlib/commit/f467c816439123a4616412c228c3a0ddb5e885f1)
feat(data/multiset): disjoint, nodup, finset ops

### [2017-11-19T21:14:37-05:00](https://github.com/leanprover-community/mathlib/commit/76a5fea5d82d40cf273b5e04b7f724e460155a71)
fix(*): finish converting structure notation to {, ..s} style

### [2017-11-19T19:49:02-05:00](https://github.com/leanprover-community/mathlib/commit/5d65b0a22d3b756b791080be994af5de3f0618ea)
fix(algebra/ring): update to lean

### [2017-11-19T05:53:48-05:00](https://github.com/leanprover-community/mathlib/commit/8067812e89fe608133d6435620c9b8928598b48a)
feat(data/multiset): filter, count, distrib lattice

### [2017-11-19T00:41:14-05:00](https://github.com/leanprover-community/mathlib/commit/f9de18397dc1a43817803c2fe5d84b282287ed0d)
feat(data/multiset): working on multisets, fix rcases bug

### [2017-11-18T23:18:32-05:00](https://github.com/leanprover-community/mathlib/commit/d579a56f322bed25580501a744e8aa7515c3230f)
fix(*): update to lean

### [2017-11-15T13:52:33-05:00](https://github.com/leanprover-community/mathlib/commit/6e9d2d529a212cf87865f81984ffa5be79435c0a)
fix(data/num): update to lean

### [2017-11-10T11:32:15+01:00](https://github.com/leanprover-community/mathlib/commit/afddab63fdbf128e589c0f6b229f929003fd8315)
chore(algebra/module): hide ring parameters, vector_space is no a proper class, remove dual, change variables to implicits

the ring type is often unnecessary it can be computed from the module instance. Also a lot of parameters to lemmas should be implicits as they can be computed from assumptions or the expteced type..

@kckennylau: I removed `dual` as it does not make sense to take about all possible *module structures* possible on the function space `linear_map α β α`. I guess `dual` should be just `linear_map α β α`.

### [2017-11-10T05:26:42-05:00](https://github.com/leanprover-community/mathlib/commit/0f8a5c8d6d77b249c7cae7d050ffc1b97b8a456b)
refactor(algebra/group): Use a user attr for to_additive

Parts of this commit are redundant pending leanprover/lean[#1857](https://github.com/leanprover-community/mathlib/pull/#1857) .

### [2017-11-09T12:33:00+01:00](https://github.com/leanprover-community/mathlib/commit/04dd132790aca853ab47e440aad4ec1f9fc1657d)
feat(algebra/big_operators): exists_ne_(one|zero)_of_(prod|sum)_ne_(one|zero)

### [2017-11-09T12:33:00+01:00](https://github.com/leanprover-community/mathlib/commit/5923cd09f5f3c08547600b72f8c6bb034d319d72)
feat(data/set/finite): finite_of_finite_image

### [2017-11-07T19:26:04-05:00](https://github.com/leanprover-community/mathlib/commit/d95bff068a5373593a9a3d779f75bafe3c2868e7)
refactor(data/hash_map): improve hash_map proof

Decrease dependence on implementation details of `array`

### [2017-11-07T06:09:41-05:00](https://github.com/leanprover-community/mathlib/commit/4ae6a578bca0fa007cda0859b4559afd607ac45e)
fix(data/array): update to lean

### [2017-11-06T11:35:36+01:00](https://github.com/leanprover-community/mathlib/commit/2bc7fd48e14c0d8bf4909a5a54d589e52e365a5f)
feat(data/cardinal): theory for cardinal arithmetic

### [2017-11-06T03:28:38-05:00](https://github.com/leanprover-community/mathlib/commit/d62cefd4ee82aeebc4dfa14378babc2c0e9768bf)
refactor(algebra/module): clean up PR commit

### [2017-11-06T01:31:01-05:00](https://github.com/leanprover-community/mathlib/commit/5cb7fb084d7be417f1c1af752ec023aedc712087)
feat(algebra/vector_space): modules and vector spaces, linear spaces

### [2017-11-06T01:26:58-05:00](https://github.com/leanprover-community/mathlib/commit/0947f962efe5a95a8291c6ac28464694e3ac5015)
feat(data/multiset): working on multiset.union

### [2017-11-05T17:42:46-05:00](https://github.com/leanprover-community/mathlib/commit/2aa6c87767347c6a0dc43fce955f891c894f2a1f)
feat(tactic/norm_num): add support for inv and locations in norm_num

### [2017-11-05T01:30:21-04:00](https://github.com/leanprover-community/mathlib/commit/d743fdfab7accc7d590caa6fb6ed3abda6dd89e0)
feat(data/sigma): duplicate sigma basics for psigma

### [2017-11-05T00:29:59-05:00](https://github.com/leanprover-community/mathlib/commit/8e99f9878d83cb7b3d9dff6e1ece4351b2503d92)
fix(algebra/field): update to lean

### [2017-11-02T17:13:43-04:00](https://github.com/leanprover-community/mathlib/commit/2da9bef02746be00369473865f089a2c7c3765b6)
feat(data/nat/cast,...): add char_zero typeclass for cast_inj

As pointed out by @kbuzzard, the complex numbers are an important example of an unordered characteristic zero field for which we will want cast_inj to be available.

### [2017-11-02T02:32:37-04:00](https://github.com/leanprover-community/mathlib/commit/2883c1bb3ccc9d68fe0950ff1c3a5d7fc9827e70)
feat(data/num/lemmas): finish znum isomorphism proof

### [2017-11-02T00:06:37-04:00](https://github.com/leanprover-community/mathlib/commit/efb37f8d2331d0b83a9491a5b201e026d28ac3ee)
fix(theories/set_theory): workaround for noncomputability bug in lean

### [2017-11-01T22:19:53-04:00](https://github.com/leanprover-community/mathlib/commit/0c0c007d88e580810d70aa4d757722c61256f7d1)
test(tests/norm_num): more tests from [#16](https://github.com/leanprover-community/mathlib/pull/#16)

### [2017-11-01T22:14:14-04:00](https://github.com/leanprover-community/mathlib/commit/7339f59b59bee9db2642448e49a504bdaf326624)
fix(tactic/norm_num): bugfix

### [2017-11-01T21:23:52-04:00](https://github.com/leanprover-community/mathlib/commit/5a262df2dba527b8b709634c93acf5cd6d98aa49)
fix(tactic/norm_num): fix performance bug in norm_num

### [2017-11-01T04:36:53-04:00](https://github.com/leanprover-community/mathlib/commit/6eedc0e75c72ea16ab1ae361056638837cdd99f2)
feat(tactic/norm_num): rewrite norm_num to use simp instead of reflection

### [2017-11-01T04:35:13-04:00](https://github.com/leanprover-community/mathlib/commit/0663945f55335e51c2b9b3a0177a84262dd87eaf)
feat(data/num,data/multiset): more properties of binary numbers, begin multisets

### [2017-10-25T22:24:56-04:00](https://github.com/leanprover-community/mathlib/commit/ff4369151862ddb9ae46385bf316536b4f15633d)
fix(analysis/real): remove import for old file

note: exists_subtype is now subtype.exists in logic/basic

### [2017-10-25T21:55:10-04:00](https://github.com/leanprover-community/mathlib/commit/3cd6229063d4402c62073e6fea664ff7503ce4b0)
refactor(analysis/real): use more coe instead of of_rat

### [2017-10-24T22:57:22-04:00](https://github.com/leanprover-community/mathlib/commit/2dd035a6e8ab6c3519142c39af6c6eedffcac470)
Merge remote-tracking branch 'cipher1024/master'

### [2017-10-24T22:31:12-04:00](https://github.com/leanprover-community/mathlib/commit/dd9f766f279522de930cee65ddab887f54179ff5)
feat(data/num,data/nat/cast,...): nat,num,int,rat.cast, list stuff

### [2017-10-17T00:02:03-04:00](https://github.com/leanprover-community/mathlib/commit/2e7651aafc350432a7c3e5d5aaf02576374be8f8)
feat(data/num): add tactics for evaluating arithmetic expressions made of literals, including `x \le y` and `x ^ y`

### [2017-10-15T02:26:24-04:00](https://github.com/leanprover-community/mathlib/commit/5ad8020f67eb13896a41cc7691d072c9331b1f76)
Merge remote-tracking branch 'minchaowu/master'

### [2017-10-15T01:58:58-04:00](https://github.com/leanprover-community/mathlib/commit/8f4327ae0c45ed36037beb1449f8285cae1ebe9c)
feat(*): working on list/basic, robusting simp proofs

### [2017-10-02T00:06:27-05:00](https://github.com/leanprover-community/mathlib/commit/e951a752a59a7879f3992dd957387f2f583c985d)
Merge branch 'master' into master

### [2017-09-28T19:28:00-04:00](https://github.com/leanprover-community/mathlib/commit/e7b2a0f7a959ebab86d56f66761d5585280f460a)
style(analysis): renames the topology directory to analysis and introduced topology and measure_theory subdirectories

### [2017-09-28T19:16:36-04:00](https://github.com/leanprover-community/mathlib/commit/afefdcbb46f85e471ca258373d33e92a9d2dd61c)
chore(topology): move general theorems to the corresponding theories

### [2017-09-28T18:16:44-04:00](https://github.com/leanprover-community/mathlib/commit/7e7c6f58d80f1d1754b7e51f98e6309daad82b49)
feat(topology): various additions (preparation for the nonnegative integral)

### [2017-09-28T18:08:23-04:00](https://github.com/leanprover-community/mathlib/commit/c3aeb53b6a43f0ae235865163bb5d01cc5494164)
feat(topology): add Lebesgue measure

### [2017-09-28T18:07:43-04:00](https://github.com/leanprover-community/mathlib/commit/4297eebb6d2318b0ea14fe5c6008fda5bc0afc71)
feat(topology): add Borel spaces

### [2017-09-22T12:52:07-05:00](https://github.com/leanprover-community/mathlib/commit/865ba360f23f252eea00f4c4e5a355eaeace9268)
feat(data/set): add functions over sets

### [2017-09-22T12:31:19-04:00](https://github.com/leanprover-community/mathlib/commit/e0abdabefe2b601e3aba0d28e5213a62ae501d95)
feat(topology/topological_space): add countablility and separability axioms for topological spaces

### [2017-09-21T15:10:53-05:00](https://github.com/leanprover-community/mathlib/commit/d5e009f9153fb773200f4a3ca4c11ef75299ad80)
Merge branch 'master' of https://github.com/leanprover/mathlib

### [2017-09-21T13:22:44-04:00](https://github.com/leanprover-community/mathlib/commit/5bb145efc1d505d5a5514ec9747275453862c5d1)
feat(topology/lebesgue_measure): add Lebesgue outer measure; show that the lower half open interval is measurable

### [2017-09-21T10:33:23-05:00](https://github.com/leanprover-community/mathlib/commit/d9865aeeac236e86f4384ccd96af3da8d81a5abb)
Merge branch 'master' of https://github.com/leanprover/mathlib

### [2017-09-20T20:02:04-04:00](https://github.com/leanprover-community/mathlib/commit/4235594794872c8deb30b199c4977221f7657baa)
feat(topology/outer_measure): add outer measures and tools for Caratheodorys extension method

### [2017-09-20T18:29:06-04:00](https://github.com/leanprover-community/mathlib/commit/46988284d30750ee42086ce3e46165496981193e)
feat(topology): prove geometric series

### [2017-09-19T02:55:14-04:00](https://github.com/leanprover-community/mathlib/commit/6b93e932d64b6b939c34b8ce6cfe29d31553ff70)
refactor(data/equiv,encodable): refactor/simplify proofs

### [2017-09-18T22:41:41-04:00](https://github.com/leanprover-community/mathlib/commit/1e4c869d28fe218d40074d0836e6119bacfdf7d9)
doc(tactic/interactive): rename simpf -> simpa, document rcases and simpa

### [2017-09-18T22:08:42-04:00](https://github.com/leanprover-community/mathlib/commit/cb4a92e32c1a55967f06bc8938343d79c2bee43d)
chore(algebra/ordered_ring): fix names, update to lean

### [2017-09-18T21:57:48-04:00](https://github.com/leanprover-community/mathlib/commit/06e797b4399d3e6d07c710d2c5b2daf236da4888)
refactor(data/nat/pairing): improve proof readability

in response to review comments on 0acdf1c

### [2017-09-17T15:38:03-04:00](https://github.com/leanprover-community/mathlib/commit/0acdf1cc6d0032af9e3b1697900fcb6b120d97dc)
feat(data/nat): better sqrt + pairing, prime numbers, renames...

### [2017-09-16T03:26:54-04:00](https://github.com/leanprover-community/mathlib/commit/f542d423f8e86a88319cc21340c8cd8b59ef99ab)
chore(algebra/ordered_ring): update to lean

### [2017-09-16T02:55:01-04:00](https://github.com/leanprover-community/mathlib/commit/fe1ad4b0854fd61bdbce556974fed48027fd1816)
feat(data/rat): derive properties of rat floor and ceil

### [2017-09-16T02:53:53-04:00](https://github.com/leanprover-community/mathlib/commit/a1c3e2defc89c1bc792cb34caf9947dd77aabd3f)
feat(algebra): new algebra theorems (more iff)

### [2017-09-16T02:51:50-04:00](https://github.com/leanprover-community/mathlib/commit/a967d8d880937e1a658af4498bb5e585933a6627)
feat(tactic/interactive): allow exprs in simpf, interactive try_for

### [2017-09-13T17:34:12-04:00](https://github.com/leanprover-community/mathlib/commit/f705963c812680897bf4ddc5504f33dcf2e60fad)
feat(topology/measure): introduce measures

### [2017-09-13T14:20:42-04:00](https://github.com/leanprover-community/mathlib/commit/0b163365050155a2aef12e7ab36a43faabc8100b)
feat(topology/infinite_sum): strengten bijection proof

### [2017-09-13T14:19:50-04:00](https://github.com/leanprover-community/mathlib/commit/e9b077c309b695191522bbfafbdfe94a57f01599)
chore(data/equiv): use has_coe_to_fun

### [2017-09-11T21:55:00-04:00](https://github.com/leanprover-community/mathlib/commit/bf58bf4451f26b88c776586865e6840cd1495f64)
feat(topology/measurable_space): induction rule for sigma-algebras with intersection-stable generators; uses Dynkin systems

### [2017-09-11T14:57:55-04:00](https://github.com/leanprover-community/mathlib/commit/74c3e6e983a6ed9510f6ad09daca5f6036185e1c)
feat(topology/measurable_space): measurable sets invariant under (countable) set operations

### [2017-09-11T13:56:06-04:00](https://github.com/leanprover-community/mathlib/commit/b8904250df6dc6fa9127cb114a9a0cf316a14a4d)
feat(topology/ennreal): ennreal forms a topological monoid

### [2017-09-11T11:58:16-04:00](https://github.com/leanprover-community/mathlib/commit/8ed673d010a6940f0b74d4df55f3f17f83ee7ccc)
feat(data/set/countable): finite sets are countable

### [2017-09-11T11:32:25-04:00](https://github.com/leanprover-community/mathlib/commit/28b46a2158b598678a1e41ae38eefbac2ba856e1)
fix(data/set/countable): finish proof countable_sUnion

### [2017-09-10T23:28:41-04:00](https://github.com/leanprover-community/mathlib/commit/8ee2629054d8c2264055f964827574dbc766b522)
feat(data/set): add countable sets

### [2017-09-10T20:33:16-04:00](https://github.com/leanprover-community/mathlib/commit/7e06124ce98784cf1c563141ae9b3811fa927ca0)
feat(logic): add small theory on inverse functions

### [2017-09-09T12:48:22-04:00](https://github.com/leanprover-community/mathlib/commit/a5f32d27ae141da1db5511d7d9e1992fe5e3c81d)
feat(data/encodable): port countable choice from Lean2

### [2017-09-08T20:06:26-04:00](https://github.com/leanprover-community/mathlib/commit/3399baa978aa79ebf7f48fc8e908235e3260ae0a)
feat(data/encodable): ported data/encodable.lean from Lean2

### [2017-09-08T18:07:24-04:00](https://github.com/leanprover-community/mathlib/commit/741065bc5cbbf1b2dd6b218b46aacf2802157cc9)
chore(data/equiv): using nat pairing

### [2017-09-08T18:05:53-04:00](https://github.com/leanprover-community/mathlib/commit/22c8faedf41ad13754d63c50812bc5e78db2ca43)
feat(data/nat/pairing): ported data/nat/pairing.lean from Lean2

### [2017-09-08T17:19:17-04:00](https://github.com/leanprover-community/mathlib/commit/7c67c2965e2368dc5d90b75887ca0ae163f7f158)
feat(data/nat/sqrt): ported data/nat/sqrt.lean from Lean2

### [2017-09-08T14:50:51-04:00](https://github.com/leanprover-community/mathlib/commit/445a5a45813080f460ba33686012029fece4d2eb)
fix(topology/real): remove (unnecessary) admit

### [2017-09-08T14:49:07-04:00](https://github.com/leanprover-community/mathlib/commit/8ef8f819db997ec070ca45266273f6e89a3737ae)
feat(data/equiv): port data/equiv.lean from Lean2

### [2017-09-07T20:38:33-04:00](https://github.com/leanprover-community/mathlib/commit/ddeefb87e8a345749339657cdada93cefcd5334c)
feat(topology/topological_structures,ennreal): show continuity of of_ennreal and of_real

### [2017-09-06T19:31:17-04:00](https://github.com/leanprover-community/mathlib/commit/32f3f452ec1f2dc2470921bb5caee129c6384a4a)
feat(topology): restructure order topologies; (start) proof that ennreal is a topological monoid

### [2017-09-06T16:19:02-04:00](https://github.com/leanprover-community/mathlib/commit/17e48db6efb4ccb303d044a312543acc14c612c2)
fix(data/list/comb): implement fix from rlewis1988

### [2017-09-05T22:38:07-04:00](https://github.com/leanprover-community/mathlib/commit/f80ae1f87628723e596e31a657b970cd2be5d5be)
feat(topology/infinite_sum): add tsum (with ∑ notation) and has_sum; add lemmas for different algebraic structures

### [2017-09-05T19:48:25-04:00](https://github.com/leanprover-community/mathlib/commit/1e4f6cce27aa4a1c55e18a120bcd3d10e25ee2f5)
chore(data/seq,data/hash_map): adapt to changes in injection tactic (https://github.com/leanprover/lean/commit/8a10d4c72c948cd1b7af02f316e553e202b1368f)

### [2017-09-05T19:32:31-04:00](https://github.com/leanprover-community/mathlib/commit/c6747eea869bd8d56ecf6f2d5a51f509216448d4)
chore(topology/uniform_space): use Type* and Sort*

### [2017-09-05T19:32:31-04:00](https://github.com/leanprover-community/mathlib/commit/7c38416b67c3eb519ffb811d5c138bf39f55a910)
feat(data/sigma,data/finset,algebra): add support for the sigma type to finset and big operators

### [2017-09-05T19:24:56-04:00](https://github.com/leanprover-community/mathlib/commit/7d8e3f3a6de70da504406727dbe7697b2f7a62ee)
feat(algebra): add ordered (non-cancellative) additive monoid; use for sum-big operator

### [2017-09-05T15:09:41-04:00](https://github.com/leanprover-community/mathlib/commit/fde992f09796c9c458455130b172c3128df3ca0e)
chore(*): use `induction generalizing`

### [2017-09-05T15:05:29-04:00](https://github.com/leanprover-community/mathlib/commit/a8a1a91b3df1d9790c9ee29c6020ac2f95658254)
chore(topology/uniform_space): simplify proof (suggested by @gebner)

### [2017-09-05T14:15:01-04:00](https://github.com/leanprover-community/mathlib/commit/ba95269a65a77c8ab5eae075f842fdad0c0a7aaf)
feat(topology): introduce infinite sums on topological monoids

### [2017-09-05T12:47:49-05:00](https://github.com/leanprover-community/mathlib/commit/6c321fee70e5a163ca9a8cce31614f5b3715bb7f)
Merge branch 'master' of https://github.com/leanprover/mathlib

### [2017-09-05T10:33:20-04:00](https://github.com/leanprover-community/mathlib/commit/c7a3c75dc301ef29d3977b14212385ba9a1bd1e8)
fix(data/seq): option_bind, option_map -> option.bind, option.map (changed in Lean)

### [2017-09-04T12:33:01-04:00](https://github.com/leanprover-community/mathlib/commit/80e14742b3994be6ab2e4d35dbb654be93d57753)
fix(logic/basic): fix simp performance issue

Having `forall_true_iff'` as a simp lemma caused way too much backtracking, so only the 2 and 3 implication versions are added as simp lemmas, and the user can add `forall_true_iff'` to their simp set if they need to reduce more.

### [2017-09-03T23:13:00-04:00](https://github.com/leanprover-community/mathlib/commit/086ac36f6cbc5ef2459c661098ed7abc8b957ab0)
feat(tactic/interactive): simpf tactic, more logic refactor

### [2017-09-03T20:55:23-04:00](https://github.com/leanprover-community/mathlib/commit/8faac5f83387fdc7056f658a1108ecf1b24826e1)
refactor(logic/basic): refactor logic theorems

### [2017-09-02T19:56:17-04:00](https://github.com/leanprover-community/mathlib/commit/74cfa9348522917ae4e4142456124a3061618f69)
fix(data/list/perm): fix broken match

This reverts commit 3d817686fdb02eba0f51ab303a4d5b50ac2a9f5e.

### [2017-08-30T20:12:20-04:00](https://github.com/leanprover-community/mathlib/commit/dbc8f869db43dec94f54198cebb7f572d2feac45)
feat(topology/measurable_space): measurability is closed under id and comp

### [2017-08-30T18:33:58-04:00](https://github.com/leanprover-community/mathlib/commit/4ef0ea8a87a2653f19a8843f8a8196191fe94619)
feat(topology/ennreal): add subtraction

### [2017-08-30T11:17:07-05:00](https://github.com/leanprover-community/mathlib/commit/f93f7e774512907fbbdeaa95f38591a836a0c742)
Merge branch 'master' of https://github.com/leanprover/mathlib

### [2017-08-29T23:40:45-04:00](https://github.com/leanprover-community/mathlib/commit/cb7fb9ba4fcddefd8e275afa3ea77e7460ef5cdc)
feat(topology): basic setup for measurable spaces

### [2017-08-29T19:20:11-04:00](https://github.com/leanprover-community/mathlib/commit/51042cde36e3ff513866c7ee6a1909650ba7396e)
feat(topology/ennreal): add extended non-negative real numbers

### [2017-08-28T21:34:47-04:00](https://github.com/leanprover-community/mathlib/commit/76ae12c7a11a38816634404572e977b633532649)
fix(algbera/big_operators): remove simp attr for sum/mul-distributivity rules

### [2017-08-28T21:30:00-04:00](https://github.com/leanprover-community/mathlib/commit/edfbf3cfb0a8bef56d7b4c058383ca31b5f74731)
feat(algebra/big_operators): add semiring and integral_domain rules

### [2017-08-28T19:34:30-04:00](https://github.com/leanprover-community/mathlib/commit/50ed0e4c7a8df04c2667a1e249fe049eacfd7663)
feat(algebra/big_operators): add congruence rule and morphism laws

### [2017-08-28T18:34:33-04:00](https://github.com/leanprover-community/mathlib/commit/4ed43d95ce4d7eaa2f533b4528b6549c9e03ecab)
feat(data/finset): add fold; add simp rules for insert, empty, singleton and mem

### [2017-08-28T12:56:25-05:00](https://github.com/leanprover-community/mathlib/commit/1aa7efa333e8b71ad7863d0e5a3c5d60213defb9)
Merge remote-tracking branch 'upstream/master'

### [2017-08-27T20:58:30-04:00](https://github.com/leanprover-community/mathlib/commit/b031441fa4b7ca428ca7dd3267a4cb9472fab284)
feat(algebra): add small theory of big operators on commutative monoids

### [2017-08-27T20:57:59-04:00](https://github.com/leanprover-community/mathlib/commit/c17d11b7a21cc731849805a8fda53cc3a03198fc)
fix(data/finset): use the type class projections for insert; hide most constants using protected; add image of finset

### [2017-08-27T13:33:07-04:00](https://github.com/leanprover-community/mathlib/commit/f2b4d2e84cffcb32588835f78416c6ac78de3b9e)
refactor(data/finset): use generic set notation for finsets

### [2017-08-27T13:33:07-04:00](https://github.com/leanprover-community/mathlib/commit/79ed1c390dff0b4c5b77f726d5d414c948ab76cf)
refactor(data/finset): add type class instances

### [2017-08-27T13:33:07-04:00](https://github.com/leanprover-community/mathlib/commit/73ae11bc3fb93cd50482c6809d145f38889c95e1)
refactor(data/finset): fix formatting issues

### [2017-08-27T13:33:07-04:00](https://github.com/leanprover-community/mathlib/commit/8dbee5b1ca9680a22ffe90751654f51d6852d7f0)
feat(data/finset): add basics for finsets

### [2017-08-27T12:30:11-05:00](https://github.com/leanprover-community/mathlib/commit/e67853193f08aa3d16f501d645256f41b6bf0ba0)
refactor(data/finset): use generic set notation for finsets

### [2017-08-27T12:05:34-05:00](https://github.com/leanprover-community/mathlib/commit/b64eb68eb54655eb0b4b8abb1ae602dc2fd9d119)
refactor(data/finset): use generic set notation for finsets

### [2017-08-27T12:05:00-05:00](https://github.com/leanprover-community/mathlib/commit/5292cf1f7f3b20eb79e3e346d631631f4d150fd6)
Merge branch 'master' of https://github.com/leanprover/mathlib

### [2017-08-27T12:26:42-04:00](https://github.com/leanprover-community/mathlib/commit/1f992c929dade0a34f07a35cad733da5692b4434)
fix(.): adapt to Lean changes: type class parameters to structures are now type class parameters in the projections and constructor

### [2017-08-26T15:40:07-04:00](https://github.com/leanprover-community/mathlib/commit/5b3b136accaa8cad6d32a006ee4aa171eb9a061c)
feat(topology): port metric space from lean2

### [2017-08-26T15:40:07-04:00](https://github.com/leanprover-community/mathlib/commit/f1fba68d444538fd939e7221107d99c40349041b)
feat(algebra): porting modules from lean2

### [2017-08-26T15:40:07-04:00](https://github.com/leanprover-community/mathlib/commit/d1cbb8f0c6d79928a652ee27804edbd598b208c4)
fix(algebra/group): add every transport theorem from main Lean repository

### [2017-08-26T13:03:40-05:00](https://github.com/leanprover-community/mathlib/commit/67a2f3983594c50d24d8a41902b58c7d2235e5b8)
refactor(data/finset): add type class instances

### [2017-08-26T12:24:58-05:00](https://github.com/leanprover-community/mathlib/commit/cde1bd87b44cb101c56f1c74e0f71dc13e016f10)
Merge branch 'master' of https://github.com/leanprover/mathlib

### [2017-08-25T13:00:17-05:00](https://github.com/leanprover-community/mathlib/commit/dff0ffd636cec9c6372dbe40563a79dbeb8d139d)
refactor(data/finset): fix formatting issues

### [2017-08-24T19:09:36-04:00](https://github.com/leanprover-community/mathlib/commit/7c72de2be1a07dcd00d343d720162c105d48107b)
feat(topology): add topological structures for groups, ring, and linear orders; add instances for rat and real

### [2017-08-24T16:21:01-05:00](https://github.com/leanprover-community/mathlib/commit/7df585efd26476e78c0a5e569b7cf7b3eeec7b25)
feat(data/finset): add basics for finsets

### [2017-08-24T13:50:09-04:00](https://github.com/leanprover-community/mathlib/commit/33b22b0a2f2cabf853ddacb66fb24feaa0f7fa4c)
data/option: add filter

### [2017-08-24T13:46:34-04:00](https://github.com/leanprover-community/mathlib/commit/4320c41797cdc539656d17c3875cb15f476e7326)
chore(*): rename stdlib to mathlib

### [2017-08-24T13:34:45-04:00](https://github.com/leanprover-community/mathlib/commit/9566a5bff2c20f973128c252b8a7ef64384e57a4)
Merge pull request [#10](https://github.com/leanprover-community/mathlib/pull/#10) from johoelzl/repair

rat is order-dense in real; cleanup continuity proof for inv

### [2017-08-23T16:42:36-04:00](https://github.com/leanprover-community/mathlib/commit/963bcad82952d0314b5b2df3de78b9a01b63aa1a)
rat is order-dense in real; cleanup continuity proof for inv

### [2017-08-23T16:41:48-04:00](https://github.com/leanprover-community/mathlib/commit/d7084898644182d2a205cc2ca2975b4450ba3ffb)
adapt to Lean changes

### [2017-08-22T17:03:16-04:00](https://github.com/leanprover-community/mathlib/commit/3d817686fdb02eba0f51ab303a4d5b50ac2a9f5e)
fix(data/list/perm): replace broken match with cases proof

### [2017-08-22T16:36:24-04:00](https://github.com/leanprover-community/mathlib/commit/2780e70e50389193968b9c52ada45e3091d2a26a)
Adapt to changes in equation compiler:

* Names are not necessary propagated when `rfl` is eliminated on two
  variables. Replace `rfl` by `eq.refl n`.

* it looks like that delta, beta, eta conversion rules are applied later now,
  so some statements of the form `assume <x, (h : t), ...` do not work anymore.

* there is still a problem in `data/list/perm.lean`

### [2017-08-18T03:14:49-04:00](https://github.com/leanprover-community/mathlib/commit/c5c5b504b918a6c5e91e372ee29ed754b0513e85)
feat(tactic/rcases): recursive cases (with patterns)

This variant on `cases` (which I hope will eventually replace `cases`) allows the specification of patterns for the `with` clause, composed of anonymous constructors and vertical bars, as in `rcases (t : a ∧ b ∨ c ∧ (d ∨ e)) with ⟨ha, hb⟩ | ⟨hc, hd | he⟩`. As with destructuring `let`, if too many arguments are given to a constructor it is treated as a right-associative nested case, i.e. `⟨ha, hb, hc⟩` becomes `⟨ha, ⟨hb, hc⟩⟩` and `ha | hb | hc` becomes `ha | ⟨hb |  hc⟩`.

### [2017-08-16T14:06:45-07:00](https://github.com/leanprover-community/mathlib/commit/fb6bab2728058cc2d605c910d936a7e6693e95df)
fix(data/list/perm): pending issues

### [2017-08-16T14:05:41-07:00](https://github.com/leanprover-community/mathlib/commit/11bcaeb6df4c0772f905d99f880a8b0c42df14b2)
refactor(data/lazy_list): lazy_list was moved back to core lib

### [2017-08-16T13:48:22-07:00](https://github.com/leanprover-community/mathlib/commit/af0b10c0ac0272ac8a8797c51d274a67f3416fba)
fix(data/num/basic): vector and bitvec are not in the init folder anymore

### [2017-08-16T13:47:32-07:00](https://github.com/leanprover-community/mathlib/commit/9b2b11f17b2556376e404aa72a09766e3fc1412b)
refactor(data): stream library was moved back to core lib

### [2017-08-11T19:03:01-04:00](https://github.com/leanprover-community/mathlib/commit/6d9072821b60d6a4a7293c943c07fba65041f25e)
use Galois connections in filter library

### [2017-08-11T18:26:35-04:00](https://github.com/leanprover-community/mathlib/commit/ce09c18f3f4d6ffe2dbae3d2f875c7b933b1eaa6)
add Galois connection, also add a couple of order theoretic results

### [2017-08-11T18:14:46-04:00](https://github.com/leanprover-community/mathlib/commit/2e8bd34884e5cdfae3068958a003b2c5b660d388)
add set.range function

`range` is stronger than `f '' univ`, as `f` can be a function from an arbitrary `Sort` instead of `Type`

### [2017-08-11T18:06:23-04:00](https://github.com/leanprover-community/mathlib/commit/e27aae81f7efcf34b3631098aa2fe64584397ede)
introduce top level dir `order`: move `algebra.order` and content of `algebra.lattice`

### [2017-08-11T17:57:57-04:00](https://github.com/leanprover-community/mathlib/commit/218c1dd308f1f67dec3ebfd6957f3cccc419b69f)
algebra/lattice/filter: cleanup move theorems to appropriate places

### [2017-08-10T16:50:12-04:00](https://github.com/leanprover-community/mathlib/commit/178e7467e882bfdf1b679f00457b70a6b55652e1)
rename towards -> tendsto

### [2017-08-10T16:41:03-04:00](https://github.com/leanprover-community/mathlib/commit/2ac1f20a7ebbc5eeb5d007ef69e5f00b68649054)
rename open -> is_open, closed -> is_closed

### [2017-08-10T16:36:59-04:00](https://github.com/leanprover-community/mathlib/commit/7882677de6cdb4f0044726054e16a535407256c0)
construct reals as complete, linear ordered field

### [2017-08-02T22:32:47+01:00](https://github.com/leanprover-community/mathlib/commit/64b61515b750c85ccb4f9871a6508bdc16e9dddc)
refactor(data/set/basic,*): vimage -> preimage, add notation

### [2017-08-02T22:17:36+01:00](https://github.com/leanprover-community/mathlib/commit/41a23769736afb5fe547cfc0122e0a64a23c73bc)
refactor(algebra/group,group_power): clean up proofs

### [2017-08-02T16:24:02+01:00](https://github.com/leanprover-community/mathlib/commit/3e9e4b68b5e8bf88fc4e7ca6bd9ed8db21a84ce4)
refactor(*): move theorems and do minor polishing

### [2017-08-02T16:21:24+01:00](https://github.com/leanprover-community/mathlib/commit/da0c346bc04216c37bee65c66ad45ba62295b663)
fix(*): fix wrt changes in lean

### [2017-08-02T15:24:33+01:00](https://github.com/leanprover-community/mathlib/commit/6392b05a0cf51a65b50fddd89e0e3f010764213b)
refactor(*): switch from order_pair to partial_order

### [2017-08-01T03:44:00+01:00](https://github.com/leanprover-community/mathlib/commit/fe811868cde6d751f61b50e9e92f18868f8f371c)
fix(tactic/alias): autogenerated alias names

### [2017-08-01T02:30:49+01:00](https://github.com/leanprover-community/mathlib/commit/1191b4d325b815a03272c55712497762fc79e654)
feat(tactic/alias): support biconditional aliases

### [2017-08-01T00:53:25+01:00](https://github.com/leanprover-community/mathlib/commit/fb21c1aea5ec9d909b8973da100cf5b22b6b39f5)
feat(tactic/alias): alias command

### [2017-07-30T00:50:04+01:00](https://github.com/leanprover-community/mathlib/commit/8f6549653e85b61b23d84a464299b79ce4308ee6)
feat(data/fp): first pass at a floating point model

Hopefully this will be eventually moved to init so it can get a native representation.

### [2017-07-30T00:48:02+01:00](https://github.com/leanprover-community/mathlib/commit/bce43b3c6b1110687f7fa49d1a9ea15e68982064)
feat(data/rat): new rat representation using canonical elements

This yields better performance in long rational computations provided the numbers can be simplified.

### [2017-07-28T16:56:17+01:00](https://github.com/leanprover-community/mathlib/commit/bfe2db7fab697d37b1590f98e30b25ae36857a22)
fix(*): adapt to lean

### [2017-07-27T14:02:57+01:00](https://github.com/leanprover-community/mathlib/commit/b37966e074482310803c96ae08fd2185327d64e9)
chore(.travis.yml): add Travis CI support

### [2017-07-26T14:25:09+01:00](https://github.com/leanprover-community/mathlib/commit/b8ea20f7b0278ae5f8644641a6f3108f8baf51af)
fix(data): bitvec and vector are in the main repo

### [2017-07-25T13:51:39+01:00](https://github.com/leanprover-community/mathlib/commit/94510873ae170401758196cf196d9a4527e02787)
refactor(*): move in list lemmas, adapt to change in list.union

### [2017-07-24T00:42:20+01:00](https://github.com/leanprover-community/mathlib/commit/aa78466db187769dcd1777ca1c18672e1307190d)
refactor(*): move in some nat lemmas

and other lemmas from init

### [2017-07-23T19:02:57+01:00](https://github.com/leanprover-community/mathlib/commit/1b6322ff3ec9ea26fbb4b040425f43a3cefa8b76)
chore(*): rfl-lemmas on same line

### [2017-07-23T18:59:39+01:00](https://github.com/leanprover-community/mathlib/commit/4a285354d9ddb6e2878d77c9ca09d1ceb27e10f4)
refactor(*): attributes on same line

### [2017-07-23T18:39:51+01:00](https://github.com/leanprover-community/mathlib/commit/a4b157b92a35ec06726d2bd80bdb77a97f4861e0)
chore(data/nat): remove addl

### [2017-07-23T18:29:16+01:00](https://github.com/leanprover-community/mathlib/commit/5816424b5cf35e552c7d4d901c46aaa0b8461c03)
refactor(*): use 'lemma' iff statement is private

### [2017-07-23T18:13:37+01:00](https://github.com/leanprover-community/mathlib/commit/b9f1d641725fe3ad90f150bb1426dcaba74414dd)
refactor(*): use . instead of ^.

### [2017-07-23T18:07:49+01:00](https://github.com/leanprover-community/mathlib/commit/9d01cb8bc06a91283fc7fd109fbcd55e114f7798)
refactor(algebra/lattice): use *experiment files, move set.lattice to .basic

### [2017-07-23T15:39:35+01:00](https://github.com/leanprover-community/mathlib/commit/32beb92a46ba57228d100c737bc0f368e3d31ac6)
refactor(*): tools -> tactic, remove experimental stuff

### [2017-07-23T15:31:56+01:00](https://github.com/leanprover-community/mathlib/commit/bb8b8f8061f34e8d907442234e74a301122bf0c6)
refactor(tests): consolidate tests

### [2017-07-23T15:24:21+01:00](https://github.com/leanprover-community/mathlib/commit/ae656439269b271ecbcb8e22c9fd07bf2baca32c)
refactor(*): use absolute paths

### [2017-07-23T15:16:51+01:00](https://github.com/leanprover-community/mathlib/commit/deb168147d4ede8848940a797753f026648501a4)
refactor(*): import content from lean/library/data and library_dev

### [2017-07-21T01:02:10-07:00](https://github.com/leanprover-community/mathlib/commit/21aca921c66c5ba975a221b453d0c9fc6dfe9c80)
Initial commit