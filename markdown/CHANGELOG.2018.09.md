### [2018-09-29 09:32:55-04:00](https://github.com/leanprover-community/mathlib/commit/b5d8fbe)
fix(data/nat/prime): fix build, add simp attr

### [2018-09-29 07:48:43-04:00](https://github.com/leanprover-community/mathlib/commit/6997caf)
feat(data/nat/basic): remove superfluous assumptions

### [2018-09-24 21:31:25+02:00](https://github.com/leanprover-community/mathlib/commit/6434658)
feat(analysis/topology): locally compact spaces and the compact-open topology

### [2018-09-24 15:33:35+02:00](https://github.com/leanprover-community/mathlib/commit/68acd76)
feat(group_theory/perm): perm.fintype and card_perm (closed [#366](https://github.com/leanprover-community/mathlib/pull/366))

### [2018-09-24 08:48:09+02:00](https://github.com/leanprover-community/mathlib/commit/cbfe372)
fix(category_theory/functor): make obj_eq_coe a rfl-lemma
This is needed to, for example, let `dsimp` turn `𝟙 (F.obj X)` into `𝟙 (F X)`.

### [2018-09-23 19:54:43-04:00](https://github.com/leanprover-community/mathlib/commit/ce43eae)
fix(topological_structures): fix imports

### [2018-09-23 18:55:03-04:00](https://github.com/leanprover-community/mathlib/commit/8c76cac)
fix(*): tweaks to 7944cc

### [2018-09-23 09:40:57+02:00](https://github.com/leanprover-community/mathlib/commit/e7c7552)
feat(analysis/topology/continuity): compactness and embeddings

### [2018-09-23 09:40:57+02:00](https://github.com/leanprover-community/mathlib/commit/ab20b5f)
style(analysis/topology/continuity): minor reorganizations

### [2018-09-21 17:57:07+02:00](https://github.com/leanprover-community/mathlib/commit/ca7f118)
fix(docs/tactics.md): missing backquote, formatting
I think I never previewed when I updated the `linarith` doc before, sorry.

### [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/9a7a611)
feat(analysis/topology, order/filter): theorems for the applicative structure on filter; add list topology

### [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/568a15f)
refactor(category/traversable): proofs about list instance for traverse, simplify multiset.traverse

### [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/618aac9)
feat(data/set): add set.seq (use it for the appliative.seq instance for set)

### [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/a62ec36)
refactor(order/filter): remove monad instance on filters; add applicative instance inducing the expected products

### [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/f53c776)
feat(analysis/topology): pi-spaces: topolopgy generation, prove second countability

### [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/da7bbd7)
feat(data/set): add set.pi

### [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/7944cc5)
fix(*): fix some problems introduced with 98152392bcd4b3f783602d030a5ab6a9e47e0088 and 9aec1d18d3c4cbad400d7ddcdd63b94d647b0a01

### [2018-09-21 00:09:04-04:00](https://github.com/leanprover-community/mathlib/commit/2485d8e)
fix(*): fix build

### [2018-09-20 19:46:48-04:00](https://github.com/leanprover-community/mathlib/commit/a4108eb)
fix(algebra/pi_instances): bugfix

### [2018-09-20 19:21:02-04:00](https://github.com/leanprover-community/mathlib/commit/9aec1d1)
refactor(algebra/pi_instances): move prod instances to pi_instances file

### [2018-09-20 17:49:40-04:00](https://github.com/leanprover-community/mathlib/commit/3ba4e82)
feat(data/set/finite): finite_subset_Union, disjoint_mono

### [2018-09-20 17:48:53-04:00](https://github.com/leanprover-community/mathlib/commit/bd26b06)
refactor(linear_algebra/basic): move some lemmas to the right place

### [2018-09-20 17:46:38-04:00](https://github.com/leanprover-community/mathlib/commit/1758092)
feat(data/subtype): subtype.coe_ext

### [2018-09-20 17:45:33-04:00](https://github.com/leanprover-community/mathlib/commit/9815239)
feat(logic/basic): more coe_trans instances

### [2018-09-20 17:44:42-04:00](https://github.com/leanprover-community/mathlib/commit/0d6bae7)
refactor(order/filter): move directed to order.basic, swap definition
directed means containing upper bounds, not lower bounds

### [2018-09-20 17:41:18-04:00](https://github.com/leanprover-community/mathlib/commit/e054277)
feat(order/bounded_lattice): eq_top_mono

### [2018-09-20 17:40:57-04:00](https://github.com/leanprover-community/mathlib/commit/84024be)
feat(order/zorn): more zorn's lemma variants

### [2018-09-20 16:00:07+02:00](https://github.com/leanprover-community/mathlib/commit/1da8cc5)
feat(analysis/topology/uniform_structure): uniform_space.comap extra
lemmas

### [2018-09-20 10:45:52+02:00](https://github.com/leanprover-community/mathlib/commit/d0f1b21)
feat(data/prod): add id_prod

### [2018-09-19 11:24:25+02:00](https://github.com/leanprover-community/mathlib/commit/318ec36)
feat(group_theory/perm): sign_cycle and sign_bij ([#347](https://github.com/leanprover-community/mathlib/pull/347))

### [2018-09-19 11:19:01+02:00](https://github.com/leanprover-community/mathlib/commit/ad9309f)
feat(data/polynomial): C_inj and dvd_iff_is_root ([#359](https://github.com/leanprover-community/mathlib/pull/359))

### [2018-09-18 23:07:02-04:00](https://github.com/leanprover-community/mathlib/commit/ae0da3d)
feat(algebra/group_power): zero_pow et al
written by Chris Hughes

### [2018-09-18 18:27:23-04:00](https://github.com/leanprover-community/mathlib/commit/61d0c65)
refactor(ring_theory/matrix): use pi instances

### [2018-09-18 17:03:51-04:00](https://github.com/leanprover-community/mathlib/commit/5260ab8)
feat(ring_theory/matrix): diagonal matrices
Joint work with Johan Commelin

### [2018-09-18 13:08:42-04:00](https://github.com/leanprover-community/mathlib/commit/a72807f)
feat(ring_theory/matrix): (finally!) adding matrices ([#334](https://github.com/leanprover-community/mathlib/pull/334))
Joint work by: Ellen Arlt, Blair Shi, Sean Leather, Scott Morrison, Johan Commelin, Kenny Lau, Johannes Hölzl, Mario Carneiro

### [2018-09-18 15:20:04+02:00](https://github.com/leanprover-community/mathlib/commit/7dedf3c)
feat(analysis/topology): injective_separated_pure_cauchy

### [2018-09-17 14:40:15-04:00](https://github.com/leanprover-community/mathlib/commit/2e204f2)
feat(category/functor): make `sum` `functor` instance more universe polymorphic

### [2018-09-17 14:39:36-04:00](https://github.com/leanprover-community/mathlib/commit/9d28f8b)
feat(tactic/ext): remove lambda abstractions when inferring a type's name

### [2018-09-17 13:25:46+02:00](https://github.com/leanprover-community/mathlib/commit/62c69b7)
feat(tactic/linarith): option to prove arbitrary goals by exfalso, enabled by default

### [2018-09-17 11:58:19+02:00](https://github.com/leanprover-community/mathlib/commit/e9af59d)
feat(algebra/order_functions): add simp rules for min/max_eq_left/right (closes [#306](https://github.com/leanprover-community/mathlib/pull/306))

### [2018-09-17 09:15:23+02:00](https://github.com/leanprover-community/mathlib/commit/cf260ca)
feat(category_theory/*): some lemmas about universes

### [2018-09-15 17:30:09+02:00](https://github.com/leanprover-community/mathlib/commit/04c4abf)
fix(algebra/group): fix bit0_zero to use (0 : alpha) not (0 : nat)

### [2018-09-15 17:29:12+02:00](https://github.com/leanprover-community/mathlib/commit/39bab47)
feat(linear_algebra): dimension theorem ([#345](https://github.com/leanprover-community/mathlib/pull/345))
* dimension theorem
* more theorems about dimension
* cardinal stuff
* fix error
* move A/S x S = A to quotient_module.lean
* remove pempty_equiv_empty

### [2018-09-14 14:57:58+02:00](https://github.com/leanprover-community/mathlib/commit/52bc8b6)
fix(analysis/normed_space): Add instance showing that normed field is a normed space over itself

### [2018-09-14 14:51:33+02:00](https://github.com/leanprover-community/mathlib/commit/9daf78b)
feat(tactic/linarith): basic support for nat ([#343](https://github.com/leanprover-community/mathlib/pull/343))
* feat(tactic/linarith): basic support for nats
* fix(tactic/linarith): typo

### [2018-09-14 14:47:42+02:00](https://github.com/leanprover-community/mathlib/commit/21233b7)
fix(category_theory/*): several minor fixes, preparatory to presheaves ([#342](https://github.com/leanprover-community/mathlib/pull/342))
* fix(category_theory/*): several minor fixes, preparatory to PR’ing the category of presheaves
In category.lean, better proofs in `instance [preorder α] : small_category α := …`.
In natural_isomorphism.lean, some rfl lemmas, natural isomorphisms describing functor composition, and formatting
In examples/topological_spaces.lean, deciding to reverse the arrows in `open_set X` (the category of open sets, with restrictions), to reduce using opposites later, as well as describing the functoriality of `open_set`.
* additional simp lemmas

### [2018-09-13 13:42:52-04:00](https://github.com/leanprover-community/mathlib/commit/a770ee5)
fix(data/padics/padic_rationals): fix proof

### [2018-09-13 12:28:42-04:00](https://github.com/leanprover-community/mathlib/commit/46502df)
feat(algebra/ordered_ring): mul_self_pos

### [2018-09-13 12:07:41-04:00](https://github.com/leanprover-community/mathlib/commit/bebe170)
feat(data/int/order): delete int.order and prove all commented out lemmas ([#348](https://github.com/leanprover-community/mathlib/pull/348))

### [2018-09-11 13:05:07+02:00](https://github.com/leanprover-community/mathlib/commit/1206356)
fix(doc/tactics): fix typo in documentation of `ext`

### [2018-09-11 10:40:33+02:00](https://github.com/leanprover-community/mathlib/commit/36a82cb)
feat(tactic/ext): use `rcases` patterns to intro `ext` variables

### [2018-09-11 10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/ffc6bc0)
feat(tactic/ext): add support for propext

### [2018-09-11 10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/c25ca3b)
feat(tactic/ext): address reviewers' comments

### [2018-09-11 10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/4e3b89c)
feat(tactic/ext): make the attribute incremental

### [2018-09-11 10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/6557f51)
feat(tactic/ext): add indexing of extensionality lemmas

### [2018-09-11 10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/4efdbdb)
feat(tactic/ext): match extensionality lemma more exactly

### [2018-09-11 10:07:19+02:00](https://github.com/leanprover-community/mathlib/commit/ba7bd74)
feat(category_theory): Yoneda, basic facts about natural isomorphisms, and an extensionality lemma using Yoneda lemma ([#326](https://github.com/leanprover-community/mathlib/pull/326))
* feat(category_theory/yoneda_lemma)
* feat(category_theory/natural_isomorphisms): basic facts about natural isomorphisms, and an extensionality lemma using Yoneda

### [2018-09-10 20:50:08-04:00](https://github.com/leanprover-community/mathlib/commit/40a365a)
feat(tactic/replacer): add support for parameters in replacer

### [2018-09-10 22:46:23+02:00](https://github.com/leanprover-community/mathlib/commit/a7995c9)
fix(set_theory/cofinality): fix type of omega_is_regular

### [2018-09-10 22:44:42+02:00](https://github.com/leanprover-community/mathlib/commit/0e06944)
feat(data/equiv/basic): quot_equiv_of_quot(')
quot_equiv_of_quot matches matches the existing subtype_equiv_of_subtype,
but quot_equiv_of_quot' is useful in practice and this definition is careful
to use eq.rec only in proofs.

### [2018-09-10 22:40:31+02:00](https://github.com/leanprover-community/mathlib/commit/61f4827)
fix(logic/basic): remove unnecessary hypothesis from proof_irrel_heq

### [2018-09-10 13:57:55-04:00](https://github.com/leanprover-community/mathlib/commit/b33764d)
feat(algebra/module): semimodules

### [2018-09-10 03:23:58-04:00](https://github.com/leanprover-community/mathlib/commit/56c4919)
feat(tactic/abel): decision procedure for comm groups

### [2018-09-09 23:23:59-04:00](https://github.com/leanprover-community/mathlib/commit/f10e7ad)
refactor(tactic/ring): remove unnecessary rat from horner_expr

### [2018-09-09 23:23:53-04:00](https://github.com/leanprover-community/mathlib/commit/eab064e)
refactor(tactic/ring): use horner_expr instead of destruct on expr

### [2018-09-09 23:23:45-04:00](https://github.com/leanprover-community/mathlib/commit/484afdf)
test(tests/ring): add test file for ring

### [2018-09-09 20:45:05-04:00](https://github.com/leanprover-community/mathlib/commit/181905e)
refactor(tactic/linarith): refactoring

### [2018-09-09 18:34:27+02:00](https://github.com/leanprover-community/mathlib/commit/4be1ef1)
fix

### [2018-09-09 18:34:27+02:00](https://github.com/leanprover-community/mathlib/commit/5b7edec)
feat(category_theory): redesign of concrete categories
Also exercising it further with `def forget_to_Mon : CommRing ⥤ Mon := …`

### [2018-09-09 18:32:02+02:00](https://github.com/leanprover-community/mathlib/commit/aaa113a)
fix(tactic/linarith): improve earlier fix

### [2018-09-09 18:32:02+02:00](https://github.com/leanprover-community/mathlib/commit/fa747b0)
fix(tactic/linarith): proper handling of 0 coefficients in input

### [2018-09-09 18:32:02+02:00](https://github.com/leanprover-community/mathlib/commit/675c235)
fix(tactic/linarith): make more use of equality hypotheses

### [2018-09-09 15:01:18+02:00](https://github.com/leanprover-community/mathlib/commit/53cc7ce)
refactor(data/polynomial): generalize leading_coeff_X_pow ([#329](https://github.com/leanprover-community/mathlib/pull/329))
Generalize `leading_coeff_X_pow` to `comm_semiring`

### [2018-09-08 19:25:06-04:00](https://github.com/leanprover-community/mathlib/commit/fc1fd3d)
feat(set_theory/cofinality): sum_lt_of_is_regular

### [2018-09-08 20:54:21+02:00](https://github.com/leanprover-community/mathlib/commit/73abe2e)
fix(category_theory/products): fix types of inl/inr/fst/snd ([#320](https://github.com/leanprover-community/mathlib/pull/320))

### [2018-09-08 20:17:26+02:00](https://github.com/leanprover-community/mathlib/commit/5613d2e)
feat(tactic): add support for quotients to rcases

### [2018-09-08 11:44:06+02:00](https://github.com/leanprover-community/mathlib/commit/1b9b139)
refactor(linear_algebra/prod_module): move prod.ring ([#322](https://github.com/leanprover-community/mathlib/pull/322))

### [2018-09-07 17:43:56+02:00](https://github.com/leanprover-community/mathlib/commit/5aa65d6)
order(filter): rename `vmap` to `comap`

### [2018-09-07 17:32:23+02:00](https://github.com/leanprover-community/mathlib/commit/2524dba)
fix(algebra/big_operators): change name of `sum_attach` to `finset.sum_attach`

### [2018-09-07 17:30:25+02:00](https://github.com/leanprover-community/mathlib/commit/8f89324)
style(linear_algebra/submodule): changed import order; added product construction

### [2018-09-07 17:30:25+02:00](https://github.com/leanprover-community/mathlib/commit/085c012)
refactor(linear_algebra, ring_theory): rework submodules; move them to linear_algebra

### [2018-09-07 17:30:25+02:00](https://github.com/leanprover-community/mathlib/commit/4421f46)
feat(ring_theory): submodules and quotients of Noetherian modules are Noetherian

### [2018-09-07 17:27:38+02:00](https://github.com/leanprover-community/mathlib/commit/dce0e64)
fix(algebra/big_operators): change name of `sum_eq_single` to `finset.sum_eq_single` ([#321](https://github.com/leanprover-community/mathlib/pull/321))

### [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/4085ca1)
feat(category_theory): add measurable space example

### [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/c2a4cf9)
feat(category_theory): lift morphism map proof to concrete categories

### [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/93e9043)
style(category_theory): concrete categories as type class

### [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/5c48489)
feat(category_theory): construction for a concrete category

### [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/840a733)
removing unnecessary class

### [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/d91428c)
feat(category_theory): the category of topological spaces, and of neighbourhoods of a point. also the category of commutative rings

### [2018-09-07 09:20:27+02:00](https://github.com/leanprover-community/mathlib/commit/e95111d)
fix(tactic/tidy): fix interactive tidy ignoring cfg

### [2018-09-06 15:59:41-04:00](https://github.com/leanprover-community/mathlib/commit/77e104c)
fix(tests/tactics): remove test
I don't think this test demonstrates reasonable/expected behavior of `wlog`, and it is not maintained by the modification, so I've removed it.

### [2018-09-06 15:39:55-04:00](https://github.com/leanprover-community/mathlib/commit/ea61c21)
fix(tactic/wlog): fix segfault

### [2018-09-06 20:28:13+02:00](https://github.com/leanprover-community/mathlib/commit/3842244)
fix(linear_algebra/subtype): simplify lifted operations by using projections instead of match

### [2018-09-06 01:04:28+02:00](https://github.com/leanprover-community/mathlib/commit/f262a07)
fix(linear_algebra/quotient_module): ring parameter for base ring of quotient module needs to be implicit, otherwise type class search loops

### [2018-09-05 23:46:03+02:00](https://github.com/leanprover-community/mathlib/commit/e24f54e)
fix(linear_algebra/prod): field is implicit parameter of the module / vector space product instances

### [2018-09-05 21:44:40+02:00](https://github.com/leanprover-community/mathlib/commit/016f538)
fix(algebra/module): add out_param to base field of vector spaces

### [2018-09-05 14:33:30+02:00](https://github.com/leanprover-community/mathlib/commit/3a3249e)
feat(data/finsupp): multiset_map_sum/_sum_sum/_index

### [2018-09-05 14:19:36+02:00](https://github.com/leanprover-community/mathlib/commit/92b9a00)
feat(data/finsupp): to_/of_multiset, curry/uncurry

### [2018-09-05 14:05:50+02:00](https://github.com/leanprover-community/mathlib/commit/e105c9e)
feat(data/multiset): add prod_map_add

### [2018-09-05 14:04:54+02:00](https://github.com/leanprover-community/mathlib/commit/abd6ab5)
refactor(data/prod): add map_fst, map_snd

### [2018-09-05 13:15:42+02:00](https://github.com/leanprover-community/mathlib/commit/ac4f7b1)
Revert "doc(docs/elan.md): Clarify instructions for leanpkg build"
This reverts commit 89e8cfee313b8bffe70362949577bd575cd09ea5.

### [2018-09-05 11:54:07+02:00](https://github.com/leanprover-community/mathlib/commit/9ea38e1)
feat(data/finset): option.to_finset

### [2018-09-05 11:53:36+02:00](https://github.com/leanprover-community/mathlib/commit/2997ce6)
feat(logic/embedding): embedding into option

### [2018-09-05 11:52:47+02:00](https://github.com/leanprover-community/mathlib/commit/a2acc61)
doc(docs/howto-contribute.md): fix broken links

### [2018-09-05 11:51:46+02:00](https://github.com/leanprover-community/mathlib/commit/89e8cfe)
doc(docs/elan.md): Clarify instructions for leanpkg build

### [2018-09-05 11:51:18+02:00](https://github.com/leanprover-community/mathlib/commit/97cd01b)
refactor(linear_algebra/quotient_module): avoid using type class inference for setoids ([#310](https://github.com/leanprover-community/mathlib/pull/310))
Continuation of [#212](https://github.com/leanprover-community/mathlib/pull/212) . Avoid using type class inference for quotient modules, and introduce a version of `quotient.mk` specifically for quotient modules, whose output type is `quotient β s` rather than `quotient (quotient_rel s)`, which should help type class inference.

### [2018-09-05 11:49:04+02:00](https://github.com/leanprover-community/mathlib/commit/681c98f)
feat(category_theory): full subcategories, preorders, Aut, and End

### [2018-09-05 09:08:50+02:00](https://github.com/leanprover-community/mathlib/commit/600d3cf)
cleanup(data/polynomial): shorten some proofs

### [2018-09-04 19:56:23+02:00](https://github.com/leanprover-community/mathlib/commit/76de588)
feat(data/polynomial): prove degree_derivative_eq

### [2018-09-04 10:43:33+02:00](https://github.com/leanprover-community/mathlib/commit/eb20fd0)
feat(data/polynomial): derivative on polynomials

### [2018-09-04 02:25:20-04:00](https://github.com/leanprover-community/mathlib/commit/fd43fe0)
fix(data/polynomial): fix proofs

### [2018-09-04 01:53:38-04:00](https://github.com/leanprover-community/mathlib/commit/7a4125b)
feat(algebra/field): field homs

### [2018-09-04 01:49:52-04:00](https://github.com/leanprover-community/mathlib/commit/2dd78b8)
feat(data/polynomial): add eval2 for univariate polys

### [2018-09-04 00:35:50-04:00](https://github.com/leanprover-community/mathlib/commit/b8ea49b)
fix(ring_theory/ufd): fix simpa uses

### [2018-09-03 18:31:34-04:00](https://github.com/leanprover-community/mathlib/commit/4de119e)
fix(*): fix simpa uses

### [2018-09-03 16:58:55-04:00](https://github.com/leanprover-community/mathlib/commit/2021a1b)
perf(tactic/ring): don't do any implicit unfolds

### [2018-09-03 16:58:38-04:00](https://github.com/leanprover-community/mathlib/commit/1edb79a)
refactor(ring_theory/associated): rename associated_elements

### [2018-09-03 16:58:38-04:00](https://github.com/leanprover-community/mathlib/commit/956398c)
refactor(tactic/interactive): improve error reporting for simpa
also make simpa fail on no goals or when applied where simp will work

### [2018-09-03 12:33:54+02:00](https://github.com/leanprover-community/mathlib/commit/36dd78e)
feat(category_theory): full and faithful functors, switching products
also the evaluation functor, and replace the ↝ arrow with ⥤, by request

### [2018-09-03 12:32:04+02:00](https://github.com/leanprover-community/mathlib/commit/6ddc3fc)
feat(data/finset): max_of_ne_empty, min_of_ne_empty

### [2018-09-03 01:27:28+02:00](https://github.com/leanprover-community/mathlib/commit/7ee7614)
feat(category_theory/isomorphisms): introduce isomorphisms ([#278](https://github.com/leanprover-community/mathlib/pull/278))
* refactor(category_theory): renaming `ulift` to `ulift_functor` to avoid name clashes
* feat(category_theory): introduce isomorphisms
* doc(category_theory): rewrite
* Resolving issues raised by Johannes
* moving heterogenous_identity.lean into isomorphism.lean
* remove unnecessary `obviously` replacement
* refactor(category_theory): using tidy in the category theory library

### [2018-09-03 00:10:15+02:00](https://github.com/leanprover-community/mathlib/commit/0df6f77)
style(linear_algebra/tensor_product): rename of -> tmul and ⊗ₛ -> ⊗ₜ; some cleanup in free_abelian_group

### [2018-09-02 23:49:36+02:00](https://github.com/leanprover-community/mathlib/commit/40ef7a2)
doc(ring_theory/unique_factorization_domain): add document strings

### [2018-09-02 16:35:13-04:00](https://github.com/leanprover-community/mathlib/commit/b3afef5)
perf(tactic/ring): fix long-running mk_app invocations

### [2018-09-02 20:50:34+02:00](https://github.com/leanprover-community/mathlib/commit/dd0c0ae)
feat(ring_theory): add unique factorization domain

### [2018-09-02 20:50:34+02:00](https://github.com/leanprover-community/mathlib/commit/5f8fafc)
feat(ring_theory): add associated elements

### [2018-09-02 20:07:13+02:00](https://github.com/leanprover-community/mathlib/commit/059f937)
feat(tactic): add linear arithmetic tactic ([#301](https://github.com/leanprover-community/mathlib/pull/301))
* feat(data/list, tactic): small helper functions
* feat(meta/rb_map): extra operations on native rb_maps
* feat(tactic/linarith): add tactic for solving linear arithmetic goals
* doc(tactic/linarith): add documentation and tests
* chore(tactic/linarith): add copyright
* feat(tactic/linarith): allow products of coefficients
* feat(tactic/linarith): cut off search early if contradiction is found
* feat(tests/linarith_tests): add test
* doc(doc/tactics): update doc
* feat(tactic/linarith): add config options
* feat(tactic/linarith): support equality goals
* chore(tactic/linarith): move non-tactic code out of tactic monad
* feat(tactic/linarith): support rational coefficients
* doc(tactic/linarith): update doc
* feat(tactic/linarith): fix obvious inefficiency in canceling denoms
* feat(tactic/linarith): efficiency improvements
* fix(tactic/linarith): remove unnecessary import and dead code
* fix(data/list/basic, meta/rb_map): shorter proofs

### [2018-09-02 19:58:41+02:00](https://github.com/leanprover-community/mathlib/commit/8c19da7)
feat(data/polynomial): has_repr for polynomials ([#302](https://github.com/leanprover-community/mathlib/pull/302))
Not sure if I should change this so that it will always return a string that will not cause any problems if copied and pasted into a lemma. It does this for rationals and integers, although for rationals, it returns something equal to the polynomial you would like, but probably not the polynomial you actually want, i.e. `(2 / 3 : polynomial ℚ)` more or less gives you `(C 2 / C 3)`, rather than `C (2 / 3)`. These expressions are def eq, but not in any reasonable amount of time as soon as the size gets slightly larger.

### [2018-09-02 19:54:22+02:00](https://github.com/leanprover-community/mathlib/commit/2594f48)
style(linear_algebra/tensor_product): renaming and changing some proofs

### [2018-09-02 19:54:22+02:00](https://github.com/leanprover-community/mathlib/commit/4b5ad0e)
feat(linear_algebra,group_theory): add tensor product and supporting material

### [2018-09-02 13:36:43-04:00](https://github.com/leanprover-community/mathlib/commit/dd6b035)
feat(data/option): add simp lemmas for orelse

### [2018-09-02 17:21:22](https://github.com/leanprover-community/mathlib/commit/3de3cfb)
feat(tactic/subtype_instance): generating subtype instances

### [2018-09-01 13:10:14+02:00](https://github.com/leanprover-community/mathlib/commit/b7b05fb)
style(ring_theory): rename PID to principal_ideal_domain