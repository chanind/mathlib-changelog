### [2018-11-29 22:13:08-05:00](https://github.com/leanprover-community/mathlib/commit/2a86b06)
fix(order/filter): tendsto_at_top only requires preorder not partial_order

### [2018-11-29 17:33:38-05:00](https://github.com/leanprover-community/mathlib/commit/9e6572f)
fix(group_theory/group_action): make is_group_action Prop

### [2018-11-28 05:03:07-05:00](https://github.com/leanprover-community/mathlib/commit/1c0c39c)
fix(category_theory/equivalences): fixed import
(and some docs, and some clumsy proofs)

### [2018-11-28 04:36:21-05:00](https://github.com/leanprover-community/mathlib/commit/b02bea6)
feat(category_theory/equivalence): equivalences, slice tactic ([#479](https://github.com/leanprover-community/mathlib/pull/479))

### [2018-11-28 01:31:22-05:00](https://github.com/leanprover-community/mathlib/commit/131b46f)
feat(data/list): separate out list defs into `data.lists.defs`

### [2018-11-27 05:19:28-05:00](https://github.com/leanprover-community/mathlib/commit/98eacf8)
feat(tactic/basic,tactic/interactive): generalize use tactic ([#497](https://github.com/leanprover-community/mathlib/pull/497))

### [2018-11-24 03:58:50-05:00](https://github.com/leanprover-community/mathlib/commit/452c9a2)
feat(data/polynomial): nat_degree_comp ([#477](https://github.com/leanprover-community/mathlib/pull/477))

### [2018-11-24 03:57:05-05:00](https://github.com/leanprover-community/mathlib/commit/e628a2c)
feat(data/finmap): finite maps ([#487](https://github.com/leanprover-community/mathlib/pull/487))
* feat(data/list/basic): erasep
* feat(data/list/basic): lookup, ndkeys
* feat(data/list/sigma,alist): basic functions on association lists
* feat(data/finmap): finite maps on multisets
* doc(data/finmap): docstrings [ci-skip]
* refactor(data/list/{alist,sigma},data/finmap): renaming
* knodup -> nodupkeys
* val -> entries
* nd -> nodupkeys
* feat(data/finmap): change keys to finset
* fix(data/list/basic): fix build
* fix(analysis/{emetric-space,measure-theory/integration}): fix build

### [2018-11-24 03:56:32-05:00](https://github.com/leanprover-community/mathlib/commit/e19cd0f)
fix(*): adding a few @[simp] attributes ([#492](https://github.com/leanprover-community/mathlib/pull/492))
* some additional simp lemmas
* nat.add_sub_cancel

### [2018-11-24 03:53:52-05:00](https://github.com/leanprover-community/mathlib/commit/beff80a)
feat(category_theory): preliminaries for limits ([#488](https://github.com/leanprover-community/mathlib/pull/488))
* style(category_theory): avoid long lines
* style(category_theory): rename embedding -> fully_faithful
* feat(category_theory/opposites): opposite of a functor
* style(category_theory/yoneda): minor changes
* make category argument implicit
* reverse order of arguments in yoneda_lemma
* avoid long lines
* feat(category_theory/functor_category): functor.flip
* feat(category_theory/isomorphism): eq_to_hom
* feat(category_theory/comma): comma categories
* feat(category_theory): pempty, punit categories
* feat(category_theory/products): add curried evaluation bifunctor
It will be used later, to prove that (co)limits in diagram categories
are computed pointwise.
* fixing order of definitions in opposites
* constructing fully_faithful instances

### [2018-11-22 23:51:18-05:00](https://github.com/leanprover-community/mathlib/commit/de8985c)
fix(finsupp): remove superfluous typeclass argument ([#490](https://github.com/leanprover-community/mathlib/pull/490))

### [2018-11-21 09:56:05-05:00](https://github.com/leanprover-community/mathlib/commit/e793967)
feat(tactic/interactive): add use tactic ([#486](https://github.com/leanprover-community/mathlib/pull/486))

### [2018-11-21 05:53:45-05:00](https://github.com/leanprover-community/mathlib/commit/0d56447)
fix(tactic/linarith): nat preprocessing was rejecting negated hypotheses ([#485](https://github.com/leanprover-community/mathlib/pull/485))

### [2018-11-19 16:03:29-05:00](https://github.com/leanprover-community/mathlib/commit/bfe7318)
* feat(tactic/mono): new mono and ac_mono tactics ([#85](https://github.com/leanprover-community/mathlib/pull/85))
* feat(tactic/mono): new mono and ac_mono tactics
* docs(tactic/mono): improve explanation, examples and syntax
* feat(tactic/mono): cache the list of mono lemma to facilitate matching
* fix(tactic/mono): fix conflict with `has_lt`
* update mathlib
* move lemmas from ordered ring to monotonicity
* rename `monotonic` attribute to `mono`
* address PR comments
* fix build

### [2018-11-17 21:37:06-05:00](https://github.com/leanprover-community/mathlib/commit/8c385bc)
feat(category_theory): associator and unitors for functors ([#478](https://github.com/leanprover-community/mathlib/pull/478))
also check pentagon and triangle

### [2018-11-16 19:49:32-05:00](https://github.com/leanprover-community/mathlib/commit/1c60f5b)
fix(ring_theory/subring): unnecessary classical ([#482](https://github.com/leanprover-community/mathlib/pull/482))

### [2018-11-15 23:08:53+01:00](https://github.com/leanprover-community/mathlib/commit/47b3477)
feat(category_theory/whiskering): more whiskering lemmas

### [2018-11-15 23:02:43+01:00](https://github.com/leanprover-community/mathlib/commit/c834715)
style(category_theory/natural_transformation): fix hcomp/vcomp notation ([#470](https://github.com/leanprover-community/mathlib/pull/470))

### [2018-11-15 15:29:36-05:00](https://github.com/leanprover-community/mathlib/commit/fce8e7c)
refactor(algebra/euclidean_domain): euclidean_domain extends nonzero_comm_ring ([#476](https://github.com/leanprover-community/mathlib/pull/476))
The euclidean domain axioms imply integral domain, given `nonzero_comm_ring`. Therefore it should extend `nonzero_comm_ring` instead, and an `integral_domain` instance is proven for Euclidean domains.

### [2018-11-14 20:17:14-05:00](https://github.com/leanprover-community/mathlib/commit/c7c0d2a)
fix(analysis/topology/topological_structures): remove useless decidability assumption ([#475](https://github.com/leanprover-community/mathlib/pull/475))

### [2018-11-14 15:24:47+01:00](https://github.com/leanprover-community/mathlib/commit/baf59c8)
refactor(order/complete_lattice): define supr and infi with range ([#474](https://github.com/leanprover-community/mathlib/pull/474))

### [2018-11-13 18:48:00+01:00](https://github.com/leanprover-community/mathlib/commit/291015d)
fix(tactic/basic): use `lean.parser.of_tactic'` instead of builtin

### [2018-11-13 18:45:11+01:00](https://github.com/leanprover-community/mathlib/commit/3e78b85)
refactor(order/complete_lattice): make supr and infi available in has_Sup and has_Inf ([#472](https://github.com/leanprover-community/mathlib/pull/472))

### [2018-11-10 18:16:37+01:00](https://github.com/leanprover-community/mathlib/commit/4a013fb)
feat(analysis): sequential completeness

### [2018-11-10 17:25:26+01:00](https://github.com/leanprover-community/mathlib/commit/b83fe1e)
feat(analysis): metric spaces are first countable

### [2018-11-09 13:51:33+01:00](https://github.com/leanprover-community/mathlib/commit/891dfbb)
chore(*): clean up uses of zorn

### [2018-11-09 10:43:01+01:00](https://github.com/leanprover-community/mathlib/commit/4fc67f8)
feat(data/fintype): add choose_unique and construct inverses to bijections ([#421](https://github.com/leanprover-community/mathlib/pull/421))

### [2018-11-09 10:22:08+01:00](https://github.com/leanprover-community/mathlib/commit/9f5099e)
refactor(analysis): add uniform_embedding_comap

### [2018-11-09 10:22:08+01:00](https://github.com/leanprover-community/mathlib/commit/6273837)
feat(analysis): add emetric spaces

### [2018-11-09 09:39:52+01:00](https://github.com/leanprover-community/mathlib/commit/ff8bd5b)
fix(data/multiset): remove unused argument from `range_zero` ([#466](https://github.com/leanprover-community/mathlib/pull/466))

### [2018-11-08 10:16:03+01:00](https://github.com/leanprover-community/mathlib/commit/b0564b2)
feat(category_theory): propose removing coercions from category_theory/ ([#463](https://github.com/leanprover-community/mathlib/pull/463))

### [2018-11-08 09:29:40+01:00](https://github.com/leanprover-community/mathlib/commit/2f38ed7)
feat(ring_theory/ideal_operations): define ideal operations (multiplication and radical) ([#462](https://github.com/leanprover-community/mathlib/pull/462))

### [2018-11-08 09:28:27+01:00](https://github.com/leanprover-community/mathlib/commit/41e8eb3)
feat(ring_theory/localization): quotient ring of integral domain is discrete field

### [2018-11-06 12:40:58+01:00](https://github.com/leanprover-community/mathlib/commit/89431cf)
feat(linear_algebra): direct sum

### [2018-11-05 13:32:36-05:00](https://github.com/leanprover-community/mathlib/commit/0963290)
fix(data/real/irrational): fix build

### [2018-11-05 17:58:46+01:00](https://github.com/leanprover-community/mathlib/commit/21d4d1c)
feat(field_theory/perfect_closure): define the perfect closure of a field

### [2018-11-05 17:58:46+01:00](https://github.com/leanprover-community/mathlib/commit/8eac03c)
feat(algebra/char_p): define the characteristic of a semiring

### [2018-11-05 17:46:35+01:00](https://github.com/leanprover-community/mathlib/commit/53d4883)
refactor(cau_seq): unify real.lim, complex.lim and cau_seq.lim ([#433](https://github.com/leanprover-community/mathlib/pull/433))

### [2018-11-05 17:44:01+01:00](https://github.com/leanprover-community/mathlib/commit/17da277)
feat(group_theory/eckmann_hilton): add Eckmann-Hilton ([#335](https://github.com/leanprover-community/mathlib/pull/335))

### [2018-11-05 17:40:57+01:00](https://github.com/leanprover-community/mathlib/commit/efcb1fb)
feat(analysis/topology/topological_space): more about discrete spaces

### [2018-11-05 17:40:31+01:00](https://github.com/leanprover-community/mathlib/commit/1a4d938)
hotifx(analysis/topology/continuity): difference with disjoint and `s ∩ t = ∅`

### [2018-11-05 17:00:44+01:00](https://github.com/leanprover-community/mathlib/commit/14d99a3)
hotfix(data/real/irrational): cast problem

### [2018-11-05 10:47:04-05:00](https://github.com/leanprover-community/mathlib/commit/a12d5a1)
feat(linear_algebra,ring_theory): refactoring modules ([#456](https://github.com/leanprover-community/mathlib/pull/456))
Co-authored with Kenny Lau. See also
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/module.20refactoring for discussion.
Major changes made:
- `semimodule α β` and `module α β` and `vector_space α β` now take one more argument, that `β` is an `add_comm_group`, i.e. before making an instance of a module, you need to prove that it's an abelian group first.
- vector space is no longer over a field, but a discrete field.
- The idiom for making an instance `module α β` (after proving that `β` is an abelian group) is `module.of_core { smul := sorry, smul_add  := sorry, add_smul := sorry, mul_smul := sorry, one_smul := sorry }`.
- `is_linear_map` and `linear_map` are now both structures, and they are independent, meaning that `linear_map` is no longer defined as `subtype is_linear_map`. The idiom for making `linear_map` from `is_linear_map` is `is_linear_map.mk' (f : M -> N) (sorry : is_linear_map f)`, and the idiom for making `is_linear_map` from `linear_map` is `f.is_linear` (i.e. `linear_map.is_linear f`).
- `is_linear_map.add` etc no longer exist. instead, you can now add two linear maps together, etc.
- the class`is_submodule` is gone, replaced by the structure `submodule` which contains a carrier, i.e. if `N : submodule R M` then `N.carrier` is a type. And there is an instance `module R N` in the same situation.
- similarly, the class `is_ideal` is gone, replaced by the structure `ideal`, which also contains a carrier.
- endomorphism ring and general linear group are defined.
- submodules form a complete lattice. the trivial ideal is now idiomatically the bottom element, and the universal ideal the top element.
- `linear_algebra/quotient_module.lean` is deleted, and it's now `submodule.quotient` (so if `N : submodule R M` then `submodule R N.quotient`) Similarly, `quotient_ring.quotient` is replaced by `ideal.quotient`. The canonical map from `N` to `N.quotient` is `submodule.quotient.mk`, and the canonical map from the ideal `I` to `I.quotient` is `ideal.quotient.mk I`.
- `linear_equiv` is now based on a linear map and an equiv, and the difference being that now you need to prove that the inverse is also linear, and there is currently no interface to get around that.
- Everything you want to know about linear independence and basis is now in the newly created file `linear_algebra/basis.lean`.
- Everything you want to know about linear combinations is now in the newly created file `linear_algebra/lc.lean`.
- `linear_algebra/linear_map_module.lean` and `linear_algebra/prod_module.lean` and `linear_algebra/quotient_module.lean` and `linear_algebra/submodule.lean` and `linear_algebra/subtype_module.lean` are deleted (with their contents placed elsewhere).
squashed commits:
* feat(linear_algebra/basic): product modules, cat/lat structure
* feat(linear_algebra/basic): refactoring quotient_module
* feat(linear_algebra/basic): merge in submodule.lean
* feat(linear_algebra/basic): merge in linear_map_module.lean
* refactor(linear_algebra/dimension): update for new modules
* feat(ring_theory/ideals): convert ideals
* refactor tensor product
* simplify local ring proof for Zp
* refactor(ring_theory/noetherian)
* refactor(ring_theory/localization)
* refactor(linear_algebra/tensor_product)
* feat(data/polynomial): lcoeff

### [2018-11-05 10:08:52-05:00](https://github.com/leanprover-community/mathlib/commit/37c0d53)
refactor(field_theory/finite): generalize proofs ([#429](https://github.com/leanprover-community/mathlib/pull/429))

### [2018-11-05 09:56:33-05:00](https://github.com/leanprover-community/mathlib/commit/a64be8d)
feat(category/bifunctor): Bifunctor and bitraversable ([#255](https://github.com/leanprover-community/mathlib/pull/255))

### [2018-11-05 09:50:04-05:00](https://github.com/leanprover-community/mathlib/commit/d556d6a)
refactor(topology/topological_space): rename open_set to opens and unbundle it ([#427](https://github.com/leanprover-community/mathlib/pull/427))

### [2018-11-05 09:43:52-05:00](https://github.com/leanprover-community/mathlib/commit/dcd90a3)
feat(order/filter): ultrafilter monad and the Stone-Cech compactification ([#434](https://github.com/leanprover-community/mathlib/pull/434))
* feat(order/filter): simplify theory of ultrafilters slightly
Introduce an alternate characterization of ultrafilters, and use it
to prove ultrafilter_map and ultrafilter_pure.
* chore(*): rename ultrafilter to is_ultrafilter
* feat(order/filter): the ultrafilter monad
* feat(analysis/topology): closure, continuous maps and T2 spaces via ultrafilters
For these, first prove that a filter is the intersection of the ultrafilters
containing it.
* feat(analysis/topology): Normal spaces. Compact Hausdorff spaces are normal.
* feat(analysis/topology/stone_cech): the Stone-Čech compactification

### [2018-11-05 09:39:57-05:00](https://github.com/leanprover-community/mathlib/commit/62538c8)
feat(analysis/metric_spaces): Compact and proper spaces ([#430](https://github.com/leanprover-community/mathlib/pull/430))

### [2018-11-05 09:03:45-05:00](https://github.com/leanprover-community/mathlib/commit/47a0a22)
fix(algebra/ordered_group): make instances defeq ([#442](https://github.com/leanprover-community/mathlib/pull/442))

### [2018-11-05 09:03:15-05:00](https://github.com/leanprover-community/mathlib/commit/8ae3fb8)
feat(ring_theory/subring): ring.closure ([#444](https://github.com/leanprover-community/mathlib/pull/444))

### [2018-11-05 09:01:57-05:00](https://github.com/leanprover-community/mathlib/commit/849d2a4)
feat(analysis/topology/topological_space): define T0 spaces, T4 spaces, connected and irreducible sets and components ([#448](https://github.com/leanprover-community/mathlib/pull/448))

### [2018-11-05 08:59:28-05:00](https://github.com/leanprover-community/mathlib/commit/8898f0e)
feat(data/real/irrational): add basic irrational facts ([#453](https://github.com/leanprover-community/mathlib/pull/453))
Joint work by Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Kenny Lau, and Chris Hughes

### [2018-11-05 08:57:04-05:00](https://github.com/leanprover-community/mathlib/commit/94b09d6)
refactor(data/real/basic): make real irreducible ([#454](https://github.com/leanprover-community/mathlib/pull/454))

### [2018-11-05 08:56:18-05:00](https://github.com/leanprover-community/mathlib/commit/c57a9a6)
fix(category_theory/isomorphism): use `category_theory.inv` in simp lemmas
`category_theory.is_iso.inv` is not the preferred name for this.

### [2018-11-05 08:53:41-05:00](https://github.com/leanprover-community/mathlib/commit/354d59e)
feat(data/nat/basic,algebra/ring): adding two lemmas about division ([#385](https://github.com/leanprover-community/mathlib/pull/385))

### [2018-11-05 13:47:01+01:00](https://github.com/leanprover-community/mathlib/commit/279b9ed)
feat(ring_theory/matrix): add minor, sub_[left|right|up|down], sub_[left|right]_[up][down] ([#389](https://github.com/leanprover-community/mathlib/pull/389))
Also add fin.nat_add.

### [2018-11-05 11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/c56bb3b)
feat(tactic/norm_num): permit `norm_num(1)` inside `conv`

### [2018-11-05 11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/b092755)
doc(docs/conv): document additions

### [2018-11-05 11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/fb57843)
feat(tactic/ring(2)): permit `ring` and `ring2` inside `conv`

### [2018-11-05 11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/d560431)
feat(tactic/basic): add `lock_tactic_state`
For state-preserving tactic invocations (extracting the result)

### [2018-11-05 11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/350e6e2)
feat(tactic/conv): add `erw`, `conv_lhs`, and `conv_rhs`

### [2018-11-05 05:21:48-05:00](https://github.com/leanprover-community/mathlib/commit/aed8194)
feat(docs/extras) add doc about coercions between number types ([#443](https://github.com/leanprover-community/mathlib/pull/443))

### [2018-11-05 05:20:29-05:00](https://github.com/leanprover-community/mathlib/commit/072a11e)
feat(data/polynomial): polynomial.comp ([#441](https://github.com/leanprover-community/mathlib/pull/441))

### [2018-11-05 05:19:00-05:00](https://github.com/leanprover-community/mathlib/commit/1cadd48)
feat(data/list): mfoldl, mfoldr theorems; reverse_foldl

### [2018-11-05 05:07:45-05:00](https://github.com/leanprover-community/mathlib/commit/b934956)
feat(data/int/basic): make coe_nat_le, coe_nat_lt, coe_nat_inj' into simp lemmas

### [2018-11-05 05:07:04-05:00](https://github.com/leanprover-community/mathlib/commit/f5ce71f)
fix(tactic/eval_expr): often crashes when reflecting expressions ([#358](https://github.com/leanprover-community/mathlib/pull/358))

### [2018-11-05 05:03:22-05:00](https://github.com/leanprover-community/mathlib/commit/f00ed77)
feat(data/complex/basic): I_ne_zero and cast_re, cast_im lemmas

### [2018-11-03 20:19:22-04:00](https://github.com/leanprover-community/mathlib/commit/3f5ec68)
fix(*): make three `trans_apply`s rfl-lemmas