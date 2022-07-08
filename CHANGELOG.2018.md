### [2018-12-28T02:49:24-05:00](https://github.com/leanprover-community/mathlib/commit/17d6263016445f1df63f9e38af28278058196977)
refactor(category_theory): minimize the amount of universe annotations in category_theory ([#552](https://github.com/leanprover-community/mathlib/pull/#552))

### [2018-12-26T19:45:48-05:00](https://github.com/leanprover-community/mathlib/commit/a71628aa5d840750e6dca5c069e5ddbc1d4771a0)
feat(algebra/order,...): material on orders ([#554](https://github.com/leanprover-community/mathlib/pull/#554))

### [2018-12-24T20:12:21-05:00](https://github.com/leanprover-community/mathlib/commit/a04c7e20c8a19018201bc772c414f7b2cd0d00b9)
feat(analysis/topology): miscellaneous topology ([#484](https://github.com/leanprover-community/mathlib/pull/#484))

* miscellaneous topology

* C is a proper metric space

* Sum of metric spaces is a def instead of instance

* refactor(analysis): shorten/simplify proofs

### [2018-12-22T01:10:55-05:00](https://github.com/leanprover-community/mathlib/commit/3eb7424a39a1e64a15acc77f6d931cac638ed576)
refactor(data/set/basic): remove unused hypotheses in union_inter_cancel_* ([#551](https://github.com/leanprover-community/mathlib/pull/#551))

### [2018-12-21T04:05:56-05:00](https://github.com/leanprover-community/mathlib/commit/cdab35d9c4643a71eccc1c93752bae9cf121a4bf)
fix(category_theory/punit): fix regression ([#550](https://github.com/leanprover-community/mathlib/pull/#550))

### [2018-12-21T03:12:01-05:00](https://github.com/leanprover-community/mathlib/commit/b11b83b247e68502fd3c38c31894d78c882f57fe)
feat(data/list/basic): rotate a list ([#542](https://github.com/leanprover-community/mathlib/pull/#542))

### [2018-12-21T02:35:06-05:00](https://github.com/leanprover-community/mathlib/commit/d7cea06145ca69ce727fb2331f9d52b758274f5a)
feat (ring_theory/noetherian) various lemmas ([#548](https://github.com/leanprover-community/mathlib/pull/#548))

### [2018-12-20T23:14:00-05:00](https://github.com/leanprover-community/mathlib/commit/3762d96ab7fef25caf6cfe7aeec6a33060ac2433)
feat(ring_theory/ideals): lift for quotient rings ([#529](https://github.com/leanprover-community/mathlib/pull/#529))

### [2018-12-20T23:12:51-05:00](https://github.com/leanprover-community/mathlib/commit/73933b732ce7bcdeacdaad9827abb346cf2edbf2)
feat(category_theory): assorted small changes from the old limits PR ([#512](https://github.com/leanprover-community/mathlib/pull/#512))

### [2018-12-20T09:31:22-05:00](https://github.com/leanprover-community/mathlib/commit/1854dd93a57306e91b23b5440ca90c8cfb68ff6b)
feat(group_theory/order_of_element): lemmas about card of subgroups and normalizer ([#545](https://github.com/leanprover-community/mathlib/pull/#545))

### [2018-12-20T09:30:12-05:00](https://github.com/leanprover-community/mathlib/commit/95bdce8c433d435583535d3a1d753a0fc5d58ae3)
feat(data/set/finite): card_range_of_injective ([#543](https://github.com/leanprover-community/mathlib/pull/#543))

### [2018-12-20T09:29:35-05:00](https://github.com/leanprover-community/mathlib/commit/0882f8ebf4efff5738858622659cdecfc6056d1b)
feat(data/fintype): exists_ne_of_card_gt_one ([#544](https://github.com/leanprover-community/mathlib/pull/#544))

### [2018-12-20T09:28:29-05:00](https://github.com/leanprover-community/mathlib/commit/433538050e01cad7b6f8b1ccd779699f1b85066e)
feat(data/vector2): vector_zero_subsingleton ([#547](https://github.com/leanprover-community/mathlib/pull/#547))

### [2018-12-20T08:15:19-05:00](https://github.com/leanprover-community/mathlib/commit/402e71ef1811d40ff20f4e25965f66c60be6cb9d)
feat(order/filter): tendsto_at_top_at_top ([#540](https://github.com/leanprover-community/mathlib/pull/#540))

### [2018-12-20T08:14:46-05:00](https://github.com/leanprover-community/mathlib/commit/f64b9aae8924fbddd6c1920d5159f54d8be27837)
feat(data/finsupp): frange ([#537](https://github.com/leanprover-community/mathlib/pull/#537))

### [2018-12-20T08:13:39-05:00](https://github.com/leanprover-community/mathlib/commit/bc21f62e96ad40b31be735ac336b864796bffdee)
feat(ring_theory/ideal_operations): correspondence under surjection ([#534](https://github.com/leanprover-community/mathlib/pull/#534))

### [2018-12-20T08:12:52-05:00](https://github.com/leanprover-community/mathlib/commit/f7697ce3db3f835201d1c62c6de2120c0bb966e3)
feat(data/equiv/algebra): ring_equiv ([#533](https://github.com/leanprover-community/mathlib/pull/#533))

### [2018-12-20T08:12:00-05:00](https://github.com/leanprover-community/mathlib/commit/fc90e009c17f2c8e0c9477197a3649f0907b81e1)
feat(ring_theory/subring) various lemmas ([#532](https://github.com/leanprover-community/mathlib/pull/#532))

new lemmas:
- is_ring_hom.is_subring_set_range
- ring.in_closure.rec_on
- ring.closure_mono
changed:
- ring.exists_list_of_mem_closure

### [2018-12-20T08:10:59-05:00](https://github.com/leanprover-community/mathlib/commit/35ed7f4c3edad7d7bc51b749a6b325ac682cad5f)
feat(data/int/basic) int.cast is ring hom ([#531](https://github.com/leanprover-community/mathlib/pull/#531))

### [2018-12-20T04:57:06-05:00](https://github.com/leanprover-community/mathlib/commit/ddd137626de68c287d732309882e2f2eb578360d)
fix(group_theory/coset): remove bad attributes

### [2018-12-20T03:40:45-05:00](https://github.com/leanprover-community/mathlib/commit/caa2076038e2d5a84fd05e9988fbe31d01a7f6ba)
feat(command): Add `#where` command, dumping environment info ([#489](https://github.com/leanprover-community/mathlib/pull/#489))

The command tells you your current namespace (wherever you write it),
the current `include`s, and the current `variables` which have been
used at least once.

### [2018-12-18T00:51:12-05:00](https://github.com/leanprover-community/mathlib/commit/293ba83ffda500f1548519f31c1a649edb9c2043)
feat(category_theory/examples/topological_spaces): limits and colimits ([#518](https://github.com/leanprover-community/mathlib/pull/#518))

### [2018-12-18T00:48:52-05:00](https://github.com/leanprover-community/mathlib/commit/3d4297b357e3bedf53fc68884c0563bfd17d3dd0)
feat(category_theory/eq_to_hom): equality of functors; more simp lemmas ([#526](https://github.com/leanprover-community/mathlib/pull/#526))

### [2018-12-18T00:45:47-05:00](https://github.com/leanprover-community/mathlib/commit/76a4b15738b9d144a292c4b857dcf627670d1bca)
feat(data/set/basic): make subtype_val_range a simp lemma ([#524](https://github.com/leanprover-community/mathlib/pull/#524))

### [2018-12-17T15:19:10-05:00](https://github.com/leanprover-community/mathlib/commit/2bc9354be695747112b36aedb63f01d1d7496cad)
feat(data/nat/enat): extended natural numbers ([#522](https://github.com/leanprover-community/mathlib/pull/#522))

### [2018-12-17T15:10:48-05:00](https://github.com/leanprover-community/mathlib/commit/418c11681174e691dab5a99ac82ffd99d9656760)
feat(data/polynomial): degree_map ([#517](https://github.com/leanprover-community/mathlib/pull/#517))

### [2018-12-17T14:47:05-05:00](https://github.com/leanprover-community/mathlib/commit/d947a3ae32c6645b07dc2d7a762ab0923766a197)
refactor(analysis/topology/continuity): use subtype.val_injective ([#525](https://github.com/leanprover-community/mathlib/pull/#525))

### [2018-12-17T12:40:24-05:00](https://github.com/leanprover-community/mathlib/commit/21ce53186eba0bde86720583d39ec4efd7d4a189)
fix(data/list): fix build

### [2018-12-17T12:35:03-05:00](https://github.com/leanprover-community/mathlib/commit/b405158539f04070248d9970beb40771bd08256b)
feat(tactic/explode): improve readability & support proofs using 'suffices' ([#516](https://github.com/leanprover-community/mathlib/pull/#516))

* improve readability & support proofs using 'suffices'

* feat(tactic/explode): improve readability & support proofs using 'suffices'

### [2018-12-17T11:35:44-05:00](https://github.com/leanprover-community/mathlib/commit/a4b699c772cd54a60ba662f561a6078f8718c4f3)
feat(order/basic): antisymm_of_asymm

### [2018-12-17T11:35:42-05:00](https://github.com/leanprover-community/mathlib/commit/ebf3008ba84fec5363334fa77a947f43bd71a965)
feat(tactic/elide): hide subterms of complicated expressions

### [2018-12-17T11:35:41-05:00](https://github.com/leanprover-community/mathlib/commit/b7d74c43a9e6f9c2c0bfbfad5a77d898a12eed19)
feat(data/list): list.chain' for empty chains

### [2018-12-17T11:01:50-05:00](https://github.com/leanprover-community/mathlib/commit/e9be5c183ac266330ae918dde701e518331d8c63)
fix(category/traversable/instances): fix build

### [2018-12-17T10:50:58-05:00](https://github.com/leanprover-community/mathlib/commit/53b08c1cf16a4601c128cc2a7a393270831a885b)
fix(*): untangle dependency hierarchy

### [2018-12-17T09:19:16-05:00](https://github.com/leanprover-community/mathlib/commit/3ee1071e1bc5348ea43bf747b9bb4edc045b239d)
feat(data/polynomial): lemmas relating unit and irreducible with degree ([#514](https://github.com/leanprover-community/mathlib/pull/#514))

### [2018-12-17T09:15:28-05:00](https://github.com/leanprover-community/mathlib/commit/d4d05e3511d9754467c54b06cf679770f24672bd)
feat(docs/extras/tactic_writing): Tactic writing tutorial ([#513](https://github.com/leanprover-community/mathlib/pull/#513))

### [2018-12-17T09:14:26-05:00](https://github.com/leanprover-community/mathlib/commit/e6065a7e253a532890bf4e4075acce3a889e2409)
chore(tactic/interactive): make squeeze_simp available by default ([#521](https://github.com/leanprover-community/mathlib/pull/#521))

### [2018-12-17T09:08:53-05:00](https://github.com/leanprover-community/mathlib/commit/b140a0793f64906df3f483d9b544a6e6e024a246)
chore(category_theory/limits/limits): Add missing lemmas ([#520](https://github.com/leanprover-community/mathlib/pull/#520))

### [2018-12-17T08:59:28-05:00](https://github.com/leanprover-community/mathlib/commit/218fe1f4ecde6dd641d743a52320677c19371716)
feat(category_theory/opposites): opposites of full and faithful functors ([#504](https://github.com/leanprover-community/mathlib/pull/#504))

### [2018-12-15T12:33:43-05:00](https://github.com/leanprover-community/mathlib/commit/9506e6c6c9fdc1f7f5f5de9fdd159e7920bccffb)
feat(category_theory): functoriality of (co)cones ([#507](https://github.com/leanprover-community/mathlib/pull/#507))

### [2018-12-15T12:32:06-05:00](https://github.com/leanprover-community/mathlib/commit/072e1ba50fe1a568702ae75983090ea0427081df)
feat(category_theory/const): Constant functor of object from punit ([#508](https://github.com/leanprover-community/mathlib/pull/#508))

### [2018-12-15T12:31:24-05:00](https://github.com/leanprover-community/mathlib/commit/b1d05010ae1b039588ab115922a68222f59eeb23)
fix(analysis/topology/topological_space): Improve the lattice structure on opens ([#511](https://github.com/leanprover-community/mathlib/pull/#511))

### [2018-12-15T12:18:12-05:00](https://github.com/leanprover-community/mathlib/commit/1f72be1fb3aac2f3a428784ab77a5977fe89b0db)
feat(category_theory/whiskering): simp-lemmas for unitors and associators ([#505](https://github.com/leanprover-community/mathlib/pull/#505))

### [2018-12-15T12:17:49-05:00](https://github.com/leanprover-community/mathlib/commit/28909a89036b8cb2c2a93f3b52cb41371cd0add5)
feat(category_theory/commas): add simp-lemmas for comma categories ([#503](https://github.com/leanprover-community/mathlib/pull/#503))

### [2018-12-10T17:44:27-05:00](https://github.com/leanprover-community/mathlib/commit/3ddfc239ddd757aa60cfa5a6f106bc68c5b8e1fc)
fix(order/basic): define preorder.lift lt by restriction

This makes it definitionally equal to `inv_image (<) f`, which appears
for example in the type of `inv_image.wf`.

### [2018-12-05T12:45:33-05:00](https://github.com/leanprover-community/mathlib/commit/257fd84fe98927ff4a5ffe044f68c4e9d235cc75)
doc(data/list/basic): improve docstrings [ci-skip]

### [2018-12-05T08:55:27-05:00](https://github.com/leanprover-community/mathlib/commit/b0d47ead02a61b7ec72295ab38da611ec1c01d55)
refactor(set_theory/ordinal): minor simplifications

### [2018-12-05T08:54:06-05:00](https://github.com/leanprover-community/mathlib/commit/843a1c3ab90a8fdbc71c6e47cc183f3787f2bcf0)
fix(tactic/norm_num): uninstantiated mvars can confuse things

### [2018-12-05T08:42:51-05:00](https://github.com/leanprover-community/mathlib/commit/94d9ac136b25cbe8c997ca618634681380e5f895)
fix(finset): removing bad simp lemmas ([#491](https://github.com/leanprover-community/mathlib/pull/#491))

### [2018-12-02T17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/585645937ee940ea5934e7e754af532567f79858)
fix(category_theory/limits): add subsingleton instances in preserves.lean

### [2018-12-02T17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/af6ee0925a23b3efc415857a0aeb5382195ee584)
fix(category_theory/limits): adding Type annotations in preserves.lean

### [2018-12-02T17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/74b65e21d7d1ba854e4cde85ca3e4c6a2a020bd2)
fix(category_theory/limits): change argument order on
cones.precompose/whisker

### [2018-12-02T17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/4b0a82c34f735688b8365d0a596ad16eb702d69a)
feat(category_theory): preservation of (co)limits, (co)limits in functor categories

### [2018-12-02T17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/6267717954be85d9ca40ddd607b3275d3c0f674e)
fix(category_theory/limits): namespaces for is_(co)limit

### [2018-12-02T17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/de4f6897435d9347252eedfc9e48f621df47ea30)
feat(category_theory/limits): (co)limits, and (co)limits in Type

### [2018-12-02T17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/a5e2ebe963ec16a01c55fc306ec6077eaecf1611)
feat(category_theory/limits/cones): (co)cones on a diagram

### [2018-12-02T17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/68c98eb762858d7c0cdb9969c104d9acafb19dec)
feat(category_theory/isomorphism): lemmas for manipulating isomorphisms

### [2018-12-02T17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/382abaf1db2839042f082786b6938a56904abce7)
feat(category_theory/const): constant functors

### [2018-12-02T06:41:58-05:00](https://github.com/leanprover-community/mathlib/commit/51afb41c46d25d37acea19658d229c8674572960)
fix(category_theory/yoneda): add componentwise lemma ([#480](https://github.com/leanprover-community/mathlib/pull/#480))

### [2018-11-29T22:13:08-05:00](https://github.com/leanprover-community/mathlib/commit/2a86b06b1853493ab4fb381514e7d1a3f4dfc54b)
fix(order/filter): tendsto_at_top only requires preorder not partial_order

### [2018-11-29T17:33:38-05:00](https://github.com/leanprover-community/mathlib/commit/9e6572fab47b7e2a576682aaa3dd8394ce0613de)
fix(group_theory/group_action): make is_group_action Prop

### [2018-11-28T05:03:07-05:00](https://github.com/leanprover-community/mathlib/commit/1c0c39cec9f548f521ed0f898f2f2b0330da2552)
fix(category_theory/equivalences): fixed import
(and some docs, and some clumsy proofs)

### [2018-11-28T04:36:21-05:00](https://github.com/leanprover-community/mathlib/commit/b02bea6e68eaccce7b51cb28200642b068c06129)
feat(category_theory/equivalence): equivalences, slice tactic ([#479](https://github.com/leanprover-community/mathlib/pull/#479))

### [2018-11-28T01:31:22-05:00](https://github.com/leanprover-community/mathlib/commit/131b46f1cdf6bfb56b18307aa66a7be0a3c1b6ed)
feat(data/list): separate out list defs into `data.lists.defs`

### [2018-11-27T05:19:28-05:00](https://github.com/leanprover-community/mathlib/commit/98eacf82fa1ab4d5dcc390501f792a63d7827c95)
feat(tactic/basic,tactic/interactive): generalize use tactic ([#497](https://github.com/leanprover-community/mathlib/pull/#497))

### [2018-11-24T03:58:50-05:00](https://github.com/leanprover-community/mathlib/commit/452c9a29dcf791e9e9f156ca9ce23e795f0a584f)
feat(data/polynomial): nat_degree_comp ([#477](https://github.com/leanprover-community/mathlib/pull/#477))

### [2018-11-24T03:57:05-05:00](https://github.com/leanprover-community/mathlib/commit/e628a2c6b91335e56890b00a66e9bd420af6322f)
feat(data/finmap): finite maps ([#487](https://github.com/leanprover-community/mathlib/pull/#487))

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

### [2018-11-24T03:56:32-05:00](https://github.com/leanprover-community/mathlib/commit/e19cd0f5bbded99c0edc2ad0bbbfbd00bb6edf74)
fix(*): adding a few @[simp] attributes ([#492](https://github.com/leanprover-community/mathlib/pull/#492))

* some additional simp lemmas

* nat.add_sub_cancel

### [2018-11-24T03:53:52-05:00](https://github.com/leanprover-community/mathlib/commit/beff80a7f986d34064d5ea1b62b7bfc2f2a4d9a2)
feat(category_theory): preliminaries for limits ([#488](https://github.com/leanprover-community/mathlib/pull/#488))

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

### [2018-11-22T23:51:18-05:00](https://github.com/leanprover-community/mathlib/commit/de8985c958f376ef2f85616d5d8e2dd11d77187d)
fix(finsupp): remove superfluous typeclass argument ([#490](https://github.com/leanprover-community/mathlib/pull/#490))

### [2018-11-21T09:56:05-05:00](https://github.com/leanprover-community/mathlib/commit/e793967313bcc744be026249b867314fdcbe3669)
feat(tactic/interactive): add use tactic ([#486](https://github.com/leanprover-community/mathlib/pull/#486))

### [2018-11-21T05:53:45-05:00](https://github.com/leanprover-community/mathlib/commit/0d56447e096bf27f3aeb5d9eb94547f20974bbe3)
fix(tactic/linarith): nat preprocessing was rejecting negated hypotheses ([#485](https://github.com/leanprover-community/mathlib/pull/#485))

### [2018-11-19T16:03:29-05:00](https://github.com/leanprover-community/mathlib/commit/bfe731880b8018f6065c62129c4697c4c51e6aee)
* feat(tactic/mono): new mono and ac_mono tactics ([#85](https://github.com/leanprover-community/mathlib/pull/#85))

* feat(tactic/mono): new mono and ac_mono tactics

* docs(tactic/mono): improve explanation, examples and syntax

* feat(tactic/mono): cache the list of mono lemma to facilitate matching

* fix(tactic/mono): fix conflict with `has_lt`

* update mathlib

* move lemmas from ordered ring to monotonicity

* rename `monotonic` attribute to `mono`

* address PR comments

* fix build

### [2018-11-17T21:37:06-05:00](https://github.com/leanprover-community/mathlib/commit/8c385bc404640d7f131ffaf2611eeeb7943dc7f6)
feat(category_theory): associator and unitors for functors ([#478](https://github.com/leanprover-community/mathlib/pull/#478))

also check pentagon and triangle

### [2018-11-16T19:49:32-05:00](https://github.com/leanprover-community/mathlib/commit/1c60f5b8b7015ed35f642d735d415b23aa85caec)
fix(ring_theory/subring): unnecessary classical ([#482](https://github.com/leanprover-community/mathlib/pull/#482))

### [2018-11-15T23:08:53+01:00](https://github.com/leanprover-community/mathlib/commit/47b3477e20ffb5a06588dd3abb01fe0fe3205646)
feat(category_theory/whiskering): more whiskering lemmas

### [2018-11-15T23:02:43+01:00](https://github.com/leanprover-community/mathlib/commit/c834715a5de49e2e3df6918bdc2016d705d01136)
style(category_theory/natural_transformation): fix hcomp/vcomp notation ([#470](https://github.com/leanprover-community/mathlib/pull/#470))

### [2018-11-15T15:29:36-05:00](https://github.com/leanprover-community/mathlib/commit/fce8e7c22badfa918a07ecd555d43a316a5ca443)
refactor(algebra/euclidean_domain): euclidean_domain extends nonzero_comm_ring ([#476](https://github.com/leanprover-community/mathlib/pull/#476))

The euclidean domain axioms imply integral domain, given `nonzero_comm_ring`. Therefore it should extend `nonzero_comm_ring` instead, and an `integral_domain` instance is proven for Euclidean domains.

### [2018-11-14T20:17:14-05:00](https://github.com/leanprover-community/mathlib/commit/c7c0d2a1bb2f0ba353bbcb0510352a25c80fc186)
fix(analysis/topology/topological_structures): remove useless decidability assumption ([#475](https://github.com/leanprover-community/mathlib/pull/#475))

### [2018-11-14T15:24:47+01:00](https://github.com/leanprover-community/mathlib/commit/baf59c8d03a14ea94c43d050dfbc4050ddf33923)
refactor(order/complete_lattice): define supr and infi with range ([#474](https://github.com/leanprover-community/mathlib/pull/#474))

### [2018-11-13T18:48:00+01:00](https://github.com/leanprover-community/mathlib/commit/291015d86cb29eb96246344fbaa35a1644283583)
fix(tactic/basic): use `lean.parser.of_tactic'` instead of builtin

### [2018-11-13T18:45:11+01:00](https://github.com/leanprover-community/mathlib/commit/3e78b858bbfd0b4906b4dabb46ccb1aeca92a875)
refactor(order/complete_lattice): make supr and infi available in has_Sup and has_Inf ([#472](https://github.com/leanprover-community/mathlib/pull/#472))

### [2018-11-10T18:16:37+01:00](https://github.com/leanprover-community/mathlib/commit/4a013fb04d6e504be8582ad610016d8dcce3e5f3)
feat(analysis): sequential completeness

### [2018-11-10T17:25:26+01:00](https://github.com/leanprover-community/mathlib/commit/b83fe1eecb6c09cb6e879942ab54e4a6dca370b3)
feat(analysis): metric spaces are first countable

### [2018-11-09T13:51:33+01:00](https://github.com/leanprover-community/mathlib/commit/891dfbbebba8a0269072460785172c294935af22)
chore(*): clean up uses of zorn

### [2018-11-09T10:43:01+01:00](https://github.com/leanprover-community/mathlib/commit/4fc67f8f219d4de0680113fb8f6ee2a860b3aa79)
feat(data/fintype): add choose_unique and construct inverses to bijections ([#421](https://github.com/leanprover-community/mathlib/pull/#421))

### [2018-11-09T10:22:08+01:00](https://github.com/leanprover-community/mathlib/commit/9f5099ec2cd933822ba3d422e74189d3508e5d0e)
refactor(analysis): add uniform_embedding_comap

### [2018-11-09T10:22:08+01:00](https://github.com/leanprover-community/mathlib/commit/6273837f37ad18621db070741870f810a9d7b94d)
feat(analysis): add emetric spaces

### [2018-11-09T09:39:52+01:00](https://github.com/leanprover-community/mathlib/commit/ff8bd5b29629ec9d0b4443007a3275aebd134c35)
fix(data/multiset): remove unused argument from `range_zero` ([#466](https://github.com/leanprover-community/mathlib/pull/#466))

### [2018-11-08T10:16:03+01:00](https://github.com/leanprover-community/mathlib/commit/b0564b2bf915ec27e06af1c4feb3076979336bc7)
feat(category_theory): propose removing coercions from category_theory/ ([#463](https://github.com/leanprover-community/mathlib/pull/#463))

### [2018-11-08T09:29:40+01:00](https://github.com/leanprover-community/mathlib/commit/2f38ed7af429d02ce031172e3f210bbfa072764b)
feat(ring_theory/ideal_operations): define ideal operations (multiplication and radical) ([#462](https://github.com/leanprover-community/mathlib/pull/#462))

### [2018-11-08T09:28:27+01:00](https://github.com/leanprover-community/mathlib/commit/41e8eb328e0bccf27e87ca502405f6f00bffe4f9)
feat(ring_theory/localization): quotient ring of integral domain is discrete field

### [2018-11-06T12:40:58+01:00](https://github.com/leanprover-community/mathlib/commit/89431cf4f01ff0f6b4005f96795a23571258cbf0)
feat(linear_algebra): direct sum

### [2018-11-05T13:32:36-05:00](https://github.com/leanprover-community/mathlib/commit/0963290490890914b044be025298d303d86c43b9)
fix(data/real/irrational): fix build

### [2018-11-05T17:58:46+01:00](https://github.com/leanprover-community/mathlib/commit/21d4d1c2cef95e016c9a6533c507454320bf5c11)
feat(field_theory/perfect_closure): define the perfect closure of a field

### [2018-11-05T17:58:46+01:00](https://github.com/leanprover-community/mathlib/commit/8eac03c6313a327b29d15b8d485cba618a9de163)
feat(algebra/char_p): define the characteristic of a semiring

### [2018-11-05T17:46:35+01:00](https://github.com/leanprover-community/mathlib/commit/53d4883f92f976249d821be5e7b3565445a221fe)
refactor(cau_seq): unify real.lim, complex.lim and cau_seq.lim ([#433](https://github.com/leanprover-community/mathlib/pull/#433))

### [2018-11-05T17:44:01+01:00](https://github.com/leanprover-community/mathlib/commit/17da2776ccb9e3d3c862b011aa0ff9f9b50044d3)
feat(group_theory/eckmann_hilton): add Eckmann-Hilton ([#335](https://github.com/leanprover-community/mathlib/pull/#335))

### [2018-11-05T17:40:57+01:00](https://github.com/leanprover-community/mathlib/commit/efcb1fb878c49bb305b6840663b8d8ed454922de)
feat(analysis/topology/topological_space): more about discrete spaces

### [2018-11-05T17:40:31+01:00](https://github.com/leanprover-community/mathlib/commit/1a4d938abe3652377309367f91a2ae4dc5fc2221)
hotifx(analysis/topology/continuity): difference with disjoint and `s ∩ t = ∅`

### [2018-11-05T17:00:44+01:00](https://github.com/leanprover-community/mathlib/commit/14d99a379e77a76d7b5f6a9e70f7cf23e8c921c8)
hotfix(data/real/irrational): cast problem

### [2018-11-05T10:47:04-05:00](https://github.com/leanprover-community/mathlib/commit/a12d5a192f5923016752f638d19fc1a51610f163)
feat(linear_algebra,ring_theory): refactoring modules ([#456](https://github.com/leanprover-community/mathlib/pull/#456))

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

### [2018-11-05T10:08:52-05:00](https://github.com/leanprover-community/mathlib/commit/37c0d53957906dfeac586d389f1416e9321dd231)
refactor(field_theory/finite): generalize proofs ([#429](https://github.com/leanprover-community/mathlib/pull/#429))

### [2018-11-05T09:56:33-05:00](https://github.com/leanprover-community/mathlib/commit/a64be8dc5cb1762606e6b92459c760ebd5361e20)
feat(category/bifunctor): Bifunctor and bitraversable ([#255](https://github.com/leanprover-community/mathlib/pull/#255))

### [2018-11-05T09:50:04-05:00](https://github.com/leanprover-community/mathlib/commit/d556d6af54495a00abd6350f7b9246e6a21ca1c9)
refactor(topology/topological_space): rename open_set to opens and unbundle it ([#427](https://github.com/leanprover-community/mathlib/pull/#427))

### [2018-11-05T09:43:52-05:00](https://github.com/leanprover-community/mathlib/commit/dcd90a3a19110bf4211bed354e61ddca907936f9)
feat(order/filter): ultrafilter monad and the Stone-Cech compactification ([#434](https://github.com/leanprover-community/mathlib/pull/#434))

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

### [2018-11-05T09:39:57-05:00](https://github.com/leanprover-community/mathlib/commit/62538c8cc921034909d4576a28558f779cbfb66e)
feat(analysis/metric_spaces): Compact and proper spaces ([#430](https://github.com/leanprover-community/mathlib/pull/#430))

### [2018-11-05T09:03:45-05:00](https://github.com/leanprover-community/mathlib/commit/47a0a22dcf9350efb96ce16753386112239a9284)
fix(algebra/ordered_group): make instances defeq ([#442](https://github.com/leanprover-community/mathlib/pull/#442))

### [2018-11-05T09:03:15-05:00](https://github.com/leanprover-community/mathlib/commit/8ae3fb86f09daab0a48a4b81e19c1eee7552be10)
feat(ring_theory/subring): ring.closure ([#444](https://github.com/leanprover-community/mathlib/pull/#444))

### [2018-11-05T09:01:57-05:00](https://github.com/leanprover-community/mathlib/commit/849d2a41a46f58a7abfe9f03b7966d245ef9db8e)
feat(analysis/topology/topological_space): define T0 spaces, T4 spaces, connected and irreducible sets and components ([#448](https://github.com/leanprover-community/mathlib/pull/#448))

### [2018-11-05T08:59:28-05:00](https://github.com/leanprover-community/mathlib/commit/8898f0e233ef95319ad56d3a093036dc66e55404)
feat(data/real/irrational): add basic irrational facts ([#453](https://github.com/leanprover-community/mathlib/pull/#453))

Joint work by Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Kenny Lau, and Chris Hughes

### [2018-11-05T08:57:04-05:00](https://github.com/leanprover-community/mathlib/commit/94b09d65120f384e51ed88d7c123d307703a6b08)
refactor(data/real/basic): make real irreducible ([#454](https://github.com/leanprover-community/mathlib/pull/#454))

### [2018-11-05T08:56:18-05:00](https://github.com/leanprover-community/mathlib/commit/c57a9a6d1019a0db2e078b800fc9919323c40823)
fix(category_theory/isomorphism): use `category_theory.inv` in simp lemmas

`category_theory.is_iso.inv` is not the preferred name for this.

### [2018-11-05T08:53:41-05:00](https://github.com/leanprover-community/mathlib/commit/354d59e1fa8214ca9c26b492ccacdbf76a446fb2)
feat(data/nat/basic,algebra/ring): adding two lemmas about division ([#385](https://github.com/leanprover-community/mathlib/pull/#385))

### [2018-11-05T13:47:01+01:00](https://github.com/leanprover-community/mathlib/commit/279b9edabda82ea7c94e7bdf925236ff6d173bd7)
feat(ring_theory/matrix): add minor, sub_[left|right|up|down], sub_[left|right]_[up][down] ([#389](https://github.com/leanprover-community/mathlib/pull/#389))

Also add fin.nat_add.

### [2018-11-05T11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/c56bb3b8bd8d593fee01c9cd05f2a335685e9485)
feat(tactic/norm_num): permit `norm_num(1)` inside `conv`

### [2018-11-05T11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/b092755cf5718f99311cfabeca8aebd42d759b11)
doc(docs/conv): document additions

### [2018-11-05T11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/fb57843db5a79445e6974d36589e2112fb5e452f)
feat(tactic/ring(2)): permit `ring` and `ring2` inside `conv`

### [2018-11-05T11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/d5604310d3e2770f448247069e7bb7791c0d59c3)
feat(tactic/basic): add `lock_tactic_state`

For state-preserving tactic invocations (extracting the result)

### [2018-11-05T11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/350e6e240b5e07fd300b2435b9d3664c4c34c8fb)
feat(tactic/conv): add `erw`, `conv_lhs`, and `conv_rhs`

### [2018-11-05T05:21:48-05:00](https://github.com/leanprover-community/mathlib/commit/aed8194c97aefffcdad80a4016c421ed433bc5b0)
feat(docs/extras) add doc about coercions between number types ([#443](https://github.com/leanprover-community/mathlib/pull/#443))

### [2018-11-05T05:20:29-05:00](https://github.com/leanprover-community/mathlib/commit/072a11eed4a88c76f9120cc18e7b0f5fbe517f0f)
feat(data/polynomial): polynomial.comp ([#441](https://github.com/leanprover-community/mathlib/pull/#441))

### [2018-11-05T05:19:00-05:00](https://github.com/leanprover-community/mathlib/commit/1cadd482aa1b680fe352612a4b2284ef6d52d422)
feat(data/list): mfoldl, mfoldr theorems; reverse_foldl

### [2018-11-05T05:07:45-05:00](https://github.com/leanprover-community/mathlib/commit/b934956c967e93c9e6bc51d29f477d2e3f298361)
feat(data/int/basic): make coe_nat_le, coe_nat_lt, coe_nat_inj' into simp lemmas

### [2018-11-05T05:07:04-05:00](https://github.com/leanprover-community/mathlib/commit/f5ce71f05f898a67127f595a6443a4afd34e71a9)
fix(tactic/eval_expr): often crashes when reflecting expressions ([#358](https://github.com/leanprover-community/mathlib/pull/#358))

### [2018-11-05T05:03:22-05:00](https://github.com/leanprover-community/mathlib/commit/f00ed77490547f573e62c1437a5e3613081db1e1)
feat(data/complex/basic): I_ne_zero and cast_re, cast_im lemmas

### [2018-11-03T20:19:22-04:00](https://github.com/leanprover-community/mathlib/commit/3f5ec68c14c06aa9721b31460a7bde3da7660076)
fix(*): make three `trans_apply`s rfl-lemmas

### [2018-10-31T21:17:26+01:00](https://github.com/leanprover-community/mathlib/commit/74ae8ce703c06bb0365e6ae8e438939955591eea)
fix(data/real,data/rat): make orders on real and rat irreducible

### [2018-10-30T12:26:55-04:00](https://github.com/leanprover-community/mathlib/commit/58909bd424209739a2214961eefaa012fb8a18d2)
feat(*): monovariate and multivariate eval\2 now do not take is_semiring_hom as an argument

### [2018-10-30T12:24:35-04:00](https://github.com/leanprover-community/mathlib/commit/90982d7cd9a9081b53ce7244c0131ec2e82b7caf)
feat(tactic/fin_cases): a tactic to case bash on `fin n` ([#352](https://github.com/leanprover-community/mathlib/pull/#352))

* feat(tactic/fin_cases): a tactic to case bash on `fin n`

* using core is_numeral

* removing guard

just rely on eval_expr to decide if we have an explicit nat

* add parsing, tests, documentation

* don't fail if the rewrite fails

* fixes

### [2018-10-30T12:23:50-04:00](https://github.com/leanprover-community/mathlib/commit/e585bed2d0ebea0e26d622328cc7d34431abba67)
feat(data/int/basic): bounded forall is decidable for integers

### [2018-10-30T12:23:04-04:00](https://github.com/leanprover-community/mathlib/commit/489050b850437309f1f8533398ef448215eff942)
feat(tactic/tauto): add an option for `tauto` to work in classical logic

### [2018-10-19T00:14:30+02:00](https://github.com/leanprover-community/mathlib/commit/ed84298169eeacb26c3350f13070143674e2c40a)
feat(analysis/topology): add continuity rules for list and vector insert/remove_nth

### [2018-10-19T00:03:08+02:00](https://github.com/leanprover-community/mathlib/commit/f6812d5a881b1bca826808e6bd40eb3e75979d2a)
feat(analysis/topology): add type class for discrete topological spaces

### [2018-10-18T23:05:00+02:00](https://github.com/leanprover-community/mathlib/commit/99e14cd4d1ca90322e036d12492c6f961a235d3a)
feat(group_theory/quotient_group): add map : quotient N -> quotient M

### [2018-10-18T23:02:03+02:00](https://github.com/leanprover-community/mathlib/commit/f52d2cc2a72db915bb8ad6200ce57efdcd892e47)
chore(group_theory/free_abelian_group, abelianization): rename to_comm_group, to_add_comm_group -> lift

### [2018-10-18T13:48:14+02:00](https://github.com/leanprover-community/mathlib/commit/c3e489c4fbbe0fb1f7d00be3169979474449ee96)
chore(data/fin): add cast_add

### [2018-10-18T09:43:01+02:00](https://github.com/leanprover-community/mathlib/commit/f2beca809321e92b1cb543c2bcac2b031754da43)
feat(ring_theory): prove principal_ideal_domain is unique factorization domain

### [2018-10-18T09:41:00+02:00](https://github.com/leanprover-community/mathlib/commit/7b876a2b99290344bcee46218d94eaa63f71624a)
cleanup(data/nat/choose,binomial): move binomial into choose

### [2018-10-18T09:08:54+02:00](https://github.com/leanprover-community/mathlib/commit/a46e8f7a03bcbc3ad7d4afc3ef3596eaa55132ea)
cleanup(ring_theory/principal_ideal_domain): restructure

### [2018-10-18T00:33:42+02:00](https://github.com/leanprover-community/mathlib/commit/a3ac630e1b7f2b404a5e3a5a6d8b7b012b97fce5)
feat(algebra,group_theory): add various closure properties of subgroup and is_group_hom w.r.t gsmul, prod, sum

### [2018-10-17T23:01:03+02:00](https://github.com/leanprover-community/mathlib/commit/ea962a75b65e8151dd4138794a3b285fc2b70347)
chore(analysis/topology/continuity): locally_compact_space is Prop

### [2018-10-17T22:49:26+02:00](https://github.com/leanprover-community/mathlib/commit/bac655d3ad38cf95870986d819162df33f91d1a1)
feature(data/vector2, data/list): add insert_nth for vectors and lists

### [2018-10-17T20:57:36+02:00](https://github.com/leanprover-community/mathlib/commit/085b1bcfe59ebb3957442c6be39e75a4c76d505b)
cleanup(algebra/group_power): remove inactive to_additive

### [2018-10-17T20:56:45+02:00](https://github.com/leanprover-community/mathlib/commit/1008f0828007213cc29c597cf5b565112ba9c059)
cleanup(tactic): remove example

### [2018-10-17T16:12:26+02:00](https://github.com/leanprover-community/mathlib/commit/5a8e28d29af3550beb53a88c3fb773a2c5ad0b68)
doc(docs/tactic): unify choose doc ([#426](https://github.com/leanprover-community/mathlib/pull/#426))

### [2018-10-17T13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/72308d854a9d0190a854c0a027d0e233833dd58e)
chore(data/fin): use uniform names; restructure

### [2018-10-17T13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/d2b39404f2216bdf985bb0eed27247d04a73a01f)
feat(data/fin): ascend / descend for fin

### [2018-10-17T13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/f7899692bd711bdef0f469080f350e6ae619d09d)
feat(data/finset): add min' / max' for non-empty finset

### [2018-10-17T13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/ef9566d311ee7b2e62807809fd4edd3d91bf0943)
feat(data/equiv): equivalences for fin * fin and fin + fin

### [2018-10-17T13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/b08591554ad94b91e1e48f3debfbc1833b627f60)
feat(data/list): length_attach, nth_le_attach, nth_le_range, of_fn_eq_pmap, nodup_of_fn (by @kckennylau)

### [2018-10-17T13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/b454daed08fbe3a45778c15b5b8dde9cca383afa)
feat(group_theory/perm): swap_mul_swal / swap_swap_apply (by @kckennylau)

### [2018-10-17T09:46:54+02:00](https://github.com/leanprover-community/mathlib/commit/530e1d13e0925e05146b320e44f9e9a145f8d7ad)
refactor (data/finset): explicit arguments for subset_union_* and inter_subset_*

This change makes them a little easier to apply, and also makes them consistent with their analogues in set.basic.

### [2018-10-17T09:25:02+02:00](https://github.com/leanprover-community/mathlib/commit/b5cd9746ae350a0c0600f4c3aa3ba4637cbb7d9c)
feat(*): trigonometric functions: exp, log, sin, cos, tan, sinh, cosh, tanh, pi, arcsin, argcos, arg ([#386](https://github.com/leanprover-community/mathlib/pull/#386))

* `floor_ring` now is parameterized on a `linear_ordered_ring` instead of extending it.
*

### [2018-10-16T13:07:50+02:00](https://github.com/leanprover-community/mathlib/commit/792c673188f8da5be51848db3f82f96871ed86b9)
feat(order/galois_connection): make arguemnts to dual implicit

### [2018-10-15T17:21:09+02:00](https://github.com/leanprover-community/mathlib/commit/80d688e3ae2a721ab61f4cd000ea3e336158b04f)
feat(data/nat/choose): nat.prime.dvd_choose ([#419](https://github.com/leanprover-community/mathlib/pull/#419))

* feat(data/nat/choose): nat/prime.dvd_choose

* use nat namespace

* Update prime.lean

* improve readability

### [2018-10-15T15:12:23+02:00](https://github.com/leanprover-community/mathlib/commit/c5930f574c54e3fd157b1ef8b93da8b1f50c8ed4)
feat(group_theory.order_of_element): subgroups of cyclic groups are cyclic ([#423](https://github.com/leanprover-community/mathlib/pull/#423))

* feat(group_theory.order_of_element): subgroups of cyclic groups are cyclic

* delete new line

### [2018-10-15T13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/a33ab1294b386f5fc6465b7221d48a052412bcd8)
refactor(analysis/topology): move separation ring to quotient_topological_structures

### [2018-10-15T13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/130807762c3559467685e0ccc158b2fd4fabef27)
feature(data/equiv/algebra): add mul left/right and inverse as equivalences

### [2018-10-15T13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/c8ecae8fc35aad0d16f79ee744eff9f234c45e94)
feature(analysis/topology/continuity): start homeomorphism

### [2018-10-15T13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/af434b54a50c9973984d058c6ac01bf532a1d580)
refactor(analysis/topology): move is_open_map to continuity

### [2018-10-15T13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/29675ad2c1dd90a153520c5fce4db4042d19c164)
refactor(analysis/topology/topological_structures): use to_additive to derive topological_add_monoid and topological_add_group

### [2018-10-15T13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/75046c2b43f0b550572c2fb91b8a92053a16f8fa)
chore(data/quot): add setoid.ext

### [2018-10-15T13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/2395183b5b424371d5170f6c7bca691a654ae5bb)
feat(analysis/topology/quotient_topological_structures): endow quotient
of topological groups, add groups and rings with a topological whatever
structure

This is not yet sorted. I'd like to push completions before cleaning
this.

### [2018-10-15T13:35:49+02:00](https://github.com/leanprover-community/mathlib/commit/735860538f5ba534e9a751199aa9d7b7227413fc)
feat(analysis/topology/completion): comm_ring on separation quotient, completion (separation_quotient A) is equivalent to completion A

### [2018-10-15T13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/13be74f76bf07b2615acf89f5eb8eb6a151161f4)
feat(analysis/topology/topological_structure): ideal closure is ideal

### [2018-10-15T13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/7697a84d70525d597da9be753d96dfbf453ee474)
feat(analysis/topology/topological_groups): construct topologies out of a group and a neighbourhood filter at 0

### [2018-10-15T13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/96d3f9505666502b67d73ebd0dd0cc360c3418a7)
doc(analysis/topology/completion): document changed organization

### [2018-10-15T13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/fbb6e9bcc90e8a75101439fa2284c83b5bf5e7ce)
feat(analysis/topology): group completion

### [2018-10-14T23:27:04-04:00](https://github.com/leanprover-community/mathlib/commit/8150f191a0c158eacfa68bc4685ed1f744d18bf8)
feat(logic/basic): classical.not_not ([#418](https://github.com/leanprover-community/mathlib/pull/#418))

* feat(logic/basic): classical.not_not

* mark as protected

### [2018-10-12T23:59:58+02:00](https://github.com/leanprover-community/mathlib/commit/019b2364cadb1dd8b30c9f13c602d61c19d3b6ea)
fix(category_theory/open_set): Restore the correct order on open_set

### [2018-10-12T10:55:25+02:00](https://github.com/leanprover-community/mathlib/commit/131cf148c21546ec8cf1d2012f39757917a1390e)
feat(group_theory/quotient_group): add to_additive attribute

### [2018-10-12T10:54:58+02:00](https://github.com/leanprover-community/mathlib/commit/c8d3c96498c53214958481a34004fe302dbd95ac)
feat(tactic/interactive): congr' tries harder

### [2018-10-11T08:53:11-04:00](https://github.com/leanprover-community/mathlib/commit/62451d3e1287dce239911b97f1cd2966aad664e0)
cleanup(data/polynomial): simplify proof of coeff_mul_left ([#414](https://github.com/leanprover-community/mathlib/pull/#414))

### [2018-10-11T13:22:43+02:00](https://github.com/leanprover-community/mathlib/commit/0fe284916a73ce92227f77826ad9655b1329eb83)
chore(analysis/measure_theory): finish characterization of lintegral

### [2018-10-10T22:50:06+02:00](https://github.com/leanprover-community/mathlib/commit/40f556575140cbd5a28936be22c1227f1d4d519c)
feat(analysis/measure_theory): lower Lebesgue integral under addition, supremum

### [2018-10-10T22:50:06+02:00](https://github.com/leanprover-community/mathlib/commit/a25e4a815d16f7d41fa6bc224b13c831ebc61a4e)
feat(analysis/measure_theory/integration): lebesgue integration [WIP]

### [2018-10-10T12:53:24-04:00](https://github.com/leanprover-community/mathlib/commit/4dbe0cdfaee201cc15cd2a74fbe8731f8bd4642a)
doc(elan): further improvements to installation instructions ([#412](https://github.com/leanprover-community/mathlib/pull/#412)) [ci-skip]

### [2018-10-10T04:04:54-04:00](https://github.com/leanprover-community/mathlib/commit/979e23832296cea6daef46b6a68e93199afa4152)
fix(*): fix build continued

### [2018-10-10T03:27:18-04:00](https://github.com/leanprover-community/mathlib/commit/1a4156daa0a5d89fd56512b040e1e06840d3f6d3)
fix(data/nat): fix build

### [2018-10-10T03:03:09-04:00](https://github.com/leanprover-community/mathlib/commit/fedee9835e73df24a367163e87c9c70284acf4f2)
feat(data/nat/basic): a few choiceless proofs

not sure I can take this much farther without modifying core...

### [2018-10-10T03:01:34-04:00](https://github.com/leanprover-community/mathlib/commit/1daf4a81c76b92d5dd99971b9c4050bcb4559e81)
fix(data/set/lattice): fixing simp lemmas for set monad

### [2018-10-09T22:59:15-04:00](https://github.com/leanprover-community/mathlib/commit/d8672405afc8168973c04a0f6a7789b4aa8e1c32)
feat(data/set/finite): finiteness of set monad ops

### [2018-10-09T01:14:15-04:00](https://github.com/leanprover-community/mathlib/commit/5c209edb7eb616a26f64efe3500f2b1ba95b8d55)
fix(linear_algebra/dimension): fix build

### [2018-10-08T15:17:51-04:00](https://github.com/leanprover-community/mathlib/commit/2c11641974a9c4981029c27a224d606f6cf1848c)
refactor(data/polynomial): consistently use coeff not apply ([#409](https://github.com/leanprover-community/mathlib/pull/#409))

### [2018-10-08T14:51:29-04:00](https://github.com/leanprover-community/mathlib/commit/a694628cea68d728434253a9540316df299febea)
fix(tactic/rcases): declare ? token

### [2018-10-08T14:30:13-04:00](https://github.com/leanprover-community/mathlib/commit/3aeb64ca294649346ffeda8cb19478c68e52b49d)
refactor(*): touching up proofs from 'faster' branch

### [2018-10-08T14:30:12-04:00](https://github.com/leanprover-community/mathlib/commit/f02a88b817a86450ce95514851f582dc9bdc460e)
chore(*): replace rec_on with induction and match for readability

### [2018-10-08T14:30:12-04:00](https://github.com/leanprover-community/mathlib/commit/cc2e1ece435f556c27fda3c4ed9bfdabab216c36)
refactor(*): making mathlib faster again

### [2018-10-08T04:07:24-04:00](https://github.com/leanprover-community/mathlib/commit/136ef25409874a4b7be216eb0dab5b2de7f2bba0)
feat(ring_theory/determinants): det is a monoid_hom ([#406](https://github.com/leanprover-community/mathlib/pull/#406))

### [2018-10-08T03:07:28-04:00](https://github.com/leanprover-community/mathlib/commit/61d877605f9a094f0c467f6f1e60f1925f828d02)
fix(ring_theory/determinant): remove #print ([#405](https://github.com/leanprover-community/mathlib/pull/#405))

### [2018-10-08T00:49:30-04:00](https://github.com/leanprover-community/mathlib/commit/13febeece20be0b6bed64c3c01299e04e5f1796d)
fix(group_theory/perm): fix to_additive use

### [2018-10-07T21:29:00-04:00](https://github.com/leanprover-community/mathlib/commit/73f51b8e6b2c9cd2f6e306ab381770771478d995)
feat(ring_theory/determinant): determinants ([#404](https://github.com/leanprover-community/mathlib/pull/#404))

* clean up determinant PR

* remove unnecessary type annotations

* update copyright

* add additive version of prod_attach_univ

### [2018-10-07T21:27:20-04:00](https://github.com/leanprover-community/mathlib/commit/04d8c15f1c366c211370fd7369fc445bfd8f1902)
feat(solve_by_elim): improve backtracking behaviour when there are multiple subgoals ([#393](https://github.com/leanprover-community/mathlib/pull/#393))

### [2018-10-07T09:22:24-04:00](https://github.com/leanprover-community/mathlib/commit/8c68fd1784a54965bd17d8b9c0cd2a23f7301f5c)
feat(tactic/auto_cases): split `iff`s into two implications ([#344](https://github.com/leanprover-community/mathlib/pull/#344))

* feat(tactic/auto_cases): split `iff`s into two implications

* add Johan's test case

### [2018-10-07T09:17:40-04:00](https://github.com/leanprover-community/mathlib/commit/49fea31325ac8322fd046dafc2af57dfd00cd766)
feat(tactics/solve_by_elim): add or remove lemmas from the set to apply, with `simp`-like parsing ([#382](https://github.com/leanprover-community/mathlib/pull/#382))

* feat(tactic/solve_by_elim): modify set of lemmas to apply using `simp`-like syntax

* update to syntax: use `with attr` to request all lemmas tagged with an attribute

* use non-interactive solve_by_elim in tfae

* fix parser

### [2018-10-07T09:12:40-04:00](https://github.com/leanprover-community/mathlib/commit/3b0915191d97ef0cc4b8a16880db4d8e0a2d982f)
feat(tactic/squeeze): squeeze_simp tactic ([#396](https://github.com/leanprover-community/mathlib/pull/#396))

* feat(tactic/squeeze): just the squeeze_simp tactic

* docs(tactic/squeeze): add header comments and documentation

* Provide a means for other tactics to use squeeze

### [2018-10-07T09:09:49-04:00](https://github.com/leanprover-community/mathlib/commit/c1f13c03af06f10ee402773de25a1cae0b39dfa0)
fix(data/int.basic): rename sub_one_le_iff ([#394](https://github.com/leanprover-community/mathlib/pull/#394))

### [2018-10-07T09:09:28-04:00](https://github.com/leanprover-community/mathlib/commit/d1e34fdaf9352bf8378966ed10c9db37bce0ec37)
fix(algebra/big_operators): remove `comm_monoid` assumption from `sum_nat_cast` ([#401](https://github.com/leanprover-community/mathlib/pull/#401))

### [2018-10-07T09:08:52-04:00](https://github.com/leanprover-community/mathlib/commit/276c47237500fa933e7749c61e5753a076a02d15)
fix(algebra/ring): delete duplicate lemma zero_dvd_iff_eq_zero ([#399](https://github.com/leanprover-community/mathlib/pull/#399))

### [2018-10-07T07:16:14-04:00](https://github.com/leanprover-community/mathlib/commit/e4ce46916335fd4de5d187f4c11cff9d6bac87a1)
fix(docs/elan): fix homebrew instructions for macOS ([#395](https://github.com/leanprover-community/mathlib/pull/#395))

### [2018-10-07T07:15:56-04:00](https://github.com/leanprover-community/mathlib/commit/64431ae841f14108f0d1c4a6c3f519c23e95fb80)
doc(hole/instance_stub) ([#400](https://github.com/leanprover-community/mathlib/pull/#400))

### [2018-10-07T06:35:55-04:00](https://github.com/leanprover-community/mathlib/commit/46a37a732e024f9cf2c27eb227f97c5c714d005d)
feat(hole/instance_stub): tool support for providing snippets ([#397](https://github.com/leanprover-community/mathlib/pull/#397))

### [2018-10-07T02:28:18-04:00](https://github.com/leanprover-community/mathlib/commit/0ddb58cfdea29db0e23ab2939d4fad805514f2aa)
workaround(tactic/tfae): tfae is broken, comment out its tests ([#398](https://github.com/leanprover-community/mathlib/pull/#398))

### [2018-10-06T22:41:00-04:00](https://github.com/leanprover-community/mathlib/commit/2bf7b4bc74769c087b4931e1fa8cbd2d2118fff8)
refactor(tactic/tfae): minor tfae modifications

### [2018-10-06T22:33:52-04:00](https://github.com/leanprover-community/mathlib/commit/568e405d3348f7fcc47ed12f15cc3ce821f5735a)
feat(data/finset): embedding properties of finset.map

### [2018-10-05T02:18:56-04:00](https://github.com/leanprover-community/mathlib/commit/74f52f1e7e13c4ec1ba06ace2fbcfea05cf2568e)
Expand and contract fin ([#387](https://github.com/leanprover-community/mathlib/pull/#387))

### [2018-10-04T15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/9ec21e44c474b058d3ff9ec7c4411386b29b694d)
perf(tactic/scc): produce smaller proofs

### [2018-10-04T15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/025b73abbe63969d1e3f7c467f5716ff9695b21f)
chore(tactic/scc): small cleanup

### [2018-10-04T15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/ff12b35567ce25d4b7f3d3d0a88d1c835706e2ba)
docs(tactic/tfae): move doc string

### [2018-10-04T15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/d935519fa2c2d80be90483a200b0e2ffd2e64911)
docs(tactic/tfae): fix oversights

### [2018-10-04T15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/b7d314f3f2f4b18a491b359aaeb889b5c83640bc)
feat(tactic/tfae): tactic for decomposing a proof into a set of
equivalent propositions which can be proved equivalent by cyclical
implications

### [2018-10-03T12:54:45+02:00](https://github.com/leanprover-community/mathlib/commit/a243126efbd7ddef878876bb5a1bb3af89f2e33b)
chore(*): replace more axiom_of_choice, classical.some and classical.choice using the choose tactic

### [2018-10-03T11:24:50+02:00](https://github.com/leanprover-community/mathlib/commit/c1f9f2e2977c0f6cb1cfd949bee8c3817cce0489)
refactor(tactics/interactive, *): rename choice to choose and change syntax; use chooose instead of cases of axiom_of_choice

### [2018-10-03T09:30:54+02:00](https://github.com/leanprover-community/mathlib/commit/0cfbf5a78d5f33b609cef6bc0409a914e255f350)
feat(tactic/linarith): handle negations of linear hypotheses

### [2018-10-02T22:17:27+02:00](https://github.com/leanprover-community/mathlib/commit/fff12f5889c7cd5a9169b42433eb14f3b53e7614)
chore(analysis/topology): remove duplicate theorems interior_compl_eq and closure_compl_eq (as discovered by @kckennylau)

### [2018-10-02T22:13:59+02:00](https://github.com/leanprover-community/mathlib/commit/c2df6b1f3f62575649dbe128a2c5fc9e2de26ffb)
feat(tactics/interactive): add choice (closes [#38](https://github.com/leanprover-community/mathlib/pull/#38))

### [2018-10-02T15:12:09+02:00](https://github.com/leanprover-community/mathlib/commit/b84e2dbb643b5732b91d56336f0d225526bc9f32)
feat(docs/theories): document padics development (close [#337](https://github.com/leanprover-community/mathlib/pull/#337))

(it hurts to write "maths in lean")

### [2018-10-02T14:08:34+02:00](https://github.com/leanprover-community/mathlib/commit/1562cc2cbe325ba847bd552a5676bcc5a9e1676d)
feat(data/padics): use prime typeclass

### [2018-10-02T14:08:34+02:00](https://github.com/leanprover-community/mathlib/commit/e6a1bc355b21377858b6d724a9dc8ba3e0456159)
feat(data/real/cau_seq): relate cauchy sequence completeness and filter completeness

### [2018-10-02T14:08:34+02:00](https://github.com/leanprover-community/mathlib/commit/e0b0c537eea19cf1b9e94c5235b6c1fdbebe18bf)
feat(data/padics): prove Hensel's lemma

### [2018-10-02T14:02:23+02:00](https://github.com/leanprover-community/mathlib/commit/f040aef2426447899e17224f6df6a73bf4b66767)
feat(data/padics): use has_norm typeclasses for padics

### [2018-10-02T13:38:45+02:00](https://github.com/leanprover-community/mathlib/commit/963fc835c64341e541331ee4dbb9db0d285f7d21)
doc(docs/elan.md): instructions for building all of a dependency

Closes [#308](https://github.com/leanprover-community/mathlib/pull/#308).

### [2018-10-02T13:38:05+02:00](https://github.com/leanprover-community/mathlib/commit/9339754cf3af7c260b8c46d45a495a5347ffed92)
docs(elan): updating documentation on installing via elan ([#371](https://github.com/leanprover-community/mathlib/pull/#371))

* updating documentation for elan

* minor

* further update of elan docs

* update instructions for elan 0.7.1

* noting additional prerequisite on macOS

### [2018-10-02T13:36:09+02:00](https://github.com/leanprover-community/mathlib/commit/28443c8bb41f3811dc592e2e686a57980cd9eeef)
feat(ring_theory/noetherian): zero ring (and finite rings) are Noetherian (closes [#341](https://github.com/leanprover-community/mathlib/pull/#341))

### [2018-10-02T11:34:24+02:00](https://github.com/leanprover-community/mathlib/commit/44b55e69ca9014741c557cac633231b8dbe78ec1)
feat(category_theory/groupoid): groupoids

### [2018-10-02T11:34:04+02:00](https://github.com/leanprover-community/mathlib/commit/efa9459041a56f92e5923ff0059cf747f83ee9df)
feat(category_theory/whiskering): whiskering nat_trans by functors ([#360](https://github.com/leanprover-community/mathlib/pull/#360))

* feat(category_theory/whiskering): whiskering nat_trans by functors

* simplify whiskering

### [2018-10-02T08:05:06+02:00](https://github.com/leanprover-community/mathlib/commit/470b6daae5d7d99af576e63f8c62d2e3dad13212)
feat(data/sum): add monad instance

### [2018-10-01T20:53:49+02:00](https://github.com/leanprover-community/mathlib/commit/dbb3ff0b5b2e42aa71d8167d7efdb3aa12d6e483)
feat(data/zmod/quadratic_reciprocity): quadratic reciprocity ([#327](https://github.com/leanprover-community/mathlib/pull/#327))

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

### [2018-10-01T20:35:10+02:00](https://github.com/leanprover-community/mathlib/commit/f3850c2255403010f0a56aa1e80dc97451219148)
feat(algebra/group): add units.map and prove that it is a group hom ([#374](https://github.com/leanprover-community/mathlib/pull/#374))

### [2018-10-01T20:34:14+02:00](https://github.com/leanprover-community/mathlib/commit/decb0302869ac70069ba26708367e460695683cb)
style(tactic/*): minor simplifications to tidy-related tactics

### [2018-10-01T20:26:32+02:00](https://github.com/leanprover-community/mathlib/commit/87a963be58e7870d36b3c2803873b4bc004c4fe2)
feat(tactic/ext): add apply_cfg argument to ext1 ([#346](https://github.com/leanprover-community/mathlib/pull/#346))

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

### [2018-10-01T20:24:42+02:00](https://github.com/leanprover-community/mathlib/commit/1923c2351419e1e58feec432eeda7f03ce91657d)
feat(data/polynomial): interface general coefficients of a polynomial ([#339](https://github.com/leanprover-community/mathlib/pull/#339))

* feat(data/polynomial): interface general coefficients of a polynomial

* fix(data/polynomial): fixing the code I broke when defining polynomial.ext

* fix(data/polynomial): tidy up comments

* Update polynomial.lean

* adding interface for scalar multiplication and coefficients

* feat(data/polynomial): coeff is R-linear

### [2018-10-01T20:19:59+02:00](https://github.com/leanprover-community/mathlib/commit/282754c26b2aa6ccab0dab555a0afcd0280f37c2)
fix(tactic/linarith): symmetric case

### [2018-10-01T20:19:59+02:00](https://github.com/leanprover-community/mathlib/commit/31ef46a976485d0472558e181c845585041f2154)
feat(tactic/linarith): don't reject nonlinear hypotheses

### [2018-10-01T18:10:17+02:00](https://github.com/leanprover-community/mathlib/commit/4ba7f23489a2f939166f3f1d872ca49a77ef342f)
cleanup(data/holor)

### [2018-10-01T14:51:42+02:00](https://github.com/leanprover-community/mathlib/commit/7c361fa07c6ea37e70d76f59b607b1a6b64f424b)
feat(data/holor): holor library

### [2018-10-01T14:40:27+02:00](https://github.com/leanprover-community/mathlib/commit/b66614d17c296b262ba1a2061e9a39d7e32b70de)
refactor(analysis/topology): renamed compact_open to continuous_map; moved locally_compact to a more general position

### [2018-09-29T09:32:55-04:00](https://github.com/leanprover-community/mathlib/commit/b5d8fbe872d9f4117a937a981d9b08da9621abcf)
fix(data/nat/prime): fix build, add simp attr

### [2018-09-29T07:48:43-04:00](https://github.com/leanprover-community/mathlib/commit/6997cafbd3a7325af5cb318561768c316ceb7757)
feat(data/nat/basic): remove superfluous assumptions

### [2018-09-24T21:31:25+02:00](https://github.com/leanprover-community/mathlib/commit/6434658c6f59377afbee48dfa7158dbd4d91d46e)
feat(analysis/topology): locally compact spaces and the compact-open topology

### [2018-09-24T15:33:35+02:00](https://github.com/leanprover-community/mathlib/commit/68acd760b61ce3b7498438c294114acbb92402fc)
feat(group_theory/perm): perm.fintype and card_perm (closed [#366](https://github.com/leanprover-community/mathlib/pull/#366))

### [2018-09-24T08:48:09+02:00](https://github.com/leanprover-community/mathlib/commit/cbfe372d1d8e80c558ceb8645929d929bd0f07d7)
fix(category_theory/functor): make obj_eq_coe a rfl-lemma

This is needed to, for example, let `dsimp` turn `𝟙 (F.obj X)` into `𝟙 (F X)`.

### [2018-09-23T19:54:43-04:00](https://github.com/leanprover-community/mathlib/commit/ce43eae8ae5e274e6d56d524d9bb03f48604839d)
fix(topological_structures): fix imports

### [2018-09-23T18:55:03-04:00](https://github.com/leanprover-community/mathlib/commit/8c76cace9db0cbda2a80ba3118d325e2e08453f9)
fix(*): tweaks to 7944cc

### [2018-09-23T09:40:57+02:00](https://github.com/leanprover-community/mathlib/commit/e7c755275921d02e7e49a64deeda3f8791778700)
feat(analysis/topology/continuity): compactness and embeddings

### [2018-09-23T09:40:57+02:00](https://github.com/leanprover-community/mathlib/commit/ab20b5ffe950d999bf2bdba9a79fe01007b6e9ad)
style(analysis/topology/continuity): minor reorganizations

### [2018-09-21T17:57:07+02:00](https://github.com/leanprover-community/mathlib/commit/ca7f118058342a2f077e836e643d26e0ad1f3ca6)
fix(docs/tactics.md): missing backquote, formatting

I think I never previewed when I updated the `linarith` doc before, sorry.

### [2018-09-21T17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/9a7a611c426c90f3894addba8a38cf4f9f3d8775)
feat(analysis/topology, order/filter): theorems for the applicative structure on filter; add list topology

### [2018-09-21T17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/568a15f8c67b6b24cf5dddd722c8d78604f9a1c4)
refactor(category/traversable): proofs about list instance for traverse, simplify multiset.traverse

### [2018-09-21T17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/618aac901e0560a6a66ef51166717775628b4e77)
feat(data/set): add set.seq (use it for the appliative.seq instance for set)

### [2018-09-21T17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/a62ec36d45b622e2cc75a2812b4c42d18de2a40f)
refactor(order/filter): remove monad instance on filters; add applicative instance inducing the expected products

### [2018-09-21T17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/f53c776c2e09eff5358c5de6902e402c641a1673)
feat(analysis/topology): pi-spaces: topolopgy generation, prove second countability

### [2018-09-21T17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/da7bbd7fc2c80a785f7992bb7751304f6cafe235)
feat(data/set): add set.pi

### [2018-09-21T17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/7944cc556e30ed630f7535e209a3d1ef5d08ae24)
fix(*): fix some problems introduced with 98152392bcd4b3f783602d030a5ab6a9e47e0088 and 9aec1d18d3c4cbad400d7ddcdd63b94d647b0a01

### [2018-09-21T00:09:04-04:00](https://github.com/leanprover-community/mathlib/commit/2485d8e92cc2ac6efb1daba413cc279a4cc06258)
fix(*): fix build

### [2018-09-20T19:46:48-04:00](https://github.com/leanprover-community/mathlib/commit/a4108eb41402de0f8e547469050ceee05f82fcb8)
fix(algebra/pi_instances): bugfix

### [2018-09-20T19:21:02-04:00](https://github.com/leanprover-community/mathlib/commit/9aec1d18d3c4cbad400d7ddcdd63b94d647b0a01)
refactor(algebra/pi_instances): move prod instances to pi_instances file

### [2018-09-20T17:49:40-04:00](https://github.com/leanprover-community/mathlib/commit/3ba4e827f607cb72bcecbc50a8afab933abf8ecb)
feat(data/set/finite): finite_subset_Union, disjoint_mono

### [2018-09-20T17:48:53-04:00](https://github.com/leanprover-community/mathlib/commit/bd26b0652a17dbd87d046cdafb0f2085e9f2a567)
refactor(linear_algebra/basic): move some lemmas to the right place

### [2018-09-20T17:46:38-04:00](https://github.com/leanprover-community/mathlib/commit/175809252dbb4802bfe4628b3d5fc0e39b02e8f5)
feat(data/subtype): subtype.coe_ext

### [2018-09-20T17:45:33-04:00](https://github.com/leanprover-community/mathlib/commit/98152392bcd4b3f783602d030a5ab6a9e47e0088)
feat(logic/basic): more coe_trans instances

### [2018-09-20T17:44:42-04:00](https://github.com/leanprover-community/mathlib/commit/0d6bae76b2003766a71d1b0b6d8a9c1b49966c4a)
refactor(order/filter): move directed to order.basic, swap definition

directed means containing upper bounds, not lower bounds

### [2018-09-20T17:41:18-04:00](https://github.com/leanprover-community/mathlib/commit/e0542773a595dddd3affc6f450cca69cd602dac8)
feat(order/bounded_lattice): eq_top_mono

### [2018-09-20T17:40:57-04:00](https://github.com/leanprover-community/mathlib/commit/84024be20b77622d4625e32475763f21bf31af19)
feat(order/zorn): more zorn's lemma variants

### [2018-09-20T16:00:07+02:00](https://github.com/leanprover-community/mathlib/commit/1da8cc51854c2e75f456878b195b162dc8dbb130)
feat(analysis/topology/uniform_structure): uniform_space.comap extra
lemmas

### [2018-09-20T10:45:52+02:00](https://github.com/leanprover-community/mathlib/commit/d0f1b21a9df64f48a8d28203bf292eb80e05a6da)
feat(data/prod): add id_prod

### [2018-09-19T11:24:25+02:00](https://github.com/leanprover-community/mathlib/commit/318ec36d528e3f3c0ca7f43a0615d0116abf9c0f)
feat(group_theory/perm): sign_cycle and sign_bij ([#347](https://github.com/leanprover-community/mathlib/pull/#347))

### [2018-09-19T11:19:01+02:00](https://github.com/leanprover-community/mathlib/commit/ad9309f764968592af57e248cb3873323fa03731)
feat(data/polynomial): C_inj and dvd_iff_is_root ([#359](https://github.com/leanprover-community/mathlib/pull/#359))

### [2018-09-18T23:07:02-04:00](https://github.com/leanprover-community/mathlib/commit/ae0da3d34e0706a3cc33a1d454f5de96da8f656d)
feat(algebra/group_power): zero_pow et al

written by Chris Hughes

### [2018-09-18T18:27:23-04:00](https://github.com/leanprover-community/mathlib/commit/61d0c65a18b60df823edbb6e383d07f14274fcdb)
refactor(ring_theory/matrix): use pi instances

### [2018-09-18T17:03:51-04:00](https://github.com/leanprover-community/mathlib/commit/5260ab8e3669910516f3cbb8daa04d958a24856a)
feat(ring_theory/matrix): diagonal matrices

Joint work with Johan Commelin

### [2018-09-18T13:08:42-04:00](https://github.com/leanprover-community/mathlib/commit/a72807fa9f61b8ce48039ad870f7a53857e57f81)
feat(ring_theory/matrix): (finally!) adding matrices ([#334](https://github.com/leanprover-community/mathlib/pull/#334))

Joint work by: Ellen Arlt, Blair Shi, Sean Leather, Scott Morrison, Johan Commelin, Kenny Lau, Johannes Hölzl, Mario Carneiro

### [2018-09-18T15:20:04+02:00](https://github.com/leanprover-community/mathlib/commit/7dedf3ca65f4a183909f51879cffddd6edc6e20a)
feat(analysis/topology): injective_separated_pure_cauchy

### [2018-09-17T14:40:15-04:00](https://github.com/leanprover-community/mathlib/commit/2e204f29aa18ed425e167e727205223aba54cefc)
feat(category/functor): make `sum` `functor` instance more universe polymorphic

### [2018-09-17T14:39:36-04:00](https://github.com/leanprover-community/mathlib/commit/9d28f8b61c23e0c8427b4b4dbd1f029b39ccf4f2)
feat(tactic/ext): remove lambda abstractions when inferring a type's name

### [2018-09-17T13:25:46+02:00](https://github.com/leanprover-community/mathlib/commit/62c69b76a5facd1e0d479a404ce3dbf8aa95bd29)
feat(tactic/linarith): option to prove arbitrary goals by exfalso, enabled by default

### [2018-09-17T11:58:19+02:00](https://github.com/leanprover-community/mathlib/commit/e9af59dec3155f4db967a36bc42b9096b065970b)
feat(algebra/order_functions): add simp rules for min/max_eq_left/right (closes [#306](https://github.com/leanprover-community/mathlib/pull/#306))

### [2018-09-17T09:15:23+02:00](https://github.com/leanprover-community/mathlib/commit/cf260cabb91cc14ea9352da066d3d97fe0117054)
feat(category_theory/*): some lemmas about universes

### [2018-09-15T17:30:09+02:00](https://github.com/leanprover-community/mathlib/commit/04c4abf13e75e254265313dd63678209ce40d90d)
fix(algebra/group): fix bit0_zero to use (0 : alpha) not (0 : nat)

### [2018-09-15T17:29:12+02:00](https://github.com/leanprover-community/mathlib/commit/39bab47fb21756b2ca4b6438b8fb1efdf864f0bc)
feat(linear_algebra): dimension theorem ([#345](https://github.com/leanprover-community/mathlib/pull/#345))

* dimension theorem

* more theorems about dimension

* cardinal stuff

* fix error

* move A/S x S = A to quotient_module.lean

* remove pempty_equiv_empty

### [2018-09-14T14:57:58+02:00](https://github.com/leanprover-community/mathlib/commit/52bc8b692a87c2811bca81c3771a3132ff218cdf)
fix(analysis/normed_space): Add instance showing that normed field is a normed space over itself

### [2018-09-14T14:51:33+02:00](https://github.com/leanprover-community/mathlib/commit/9daf78bcb711476999611277dd65ea42ab89ab52)
feat(tactic/linarith): basic support for nat ([#343](https://github.com/leanprover-community/mathlib/pull/#343))

* feat(tactic/linarith): basic support for nats

* fix(tactic/linarith): typo

### [2018-09-14T14:47:42+02:00](https://github.com/leanprover-community/mathlib/commit/21233b7ab677cfc57cdaf07ff8db23b64e83be72)
fix(category_theory/*): several minor fixes, preparatory to presheaves ([#342](https://github.com/leanprover-community/mathlib/pull/#342))

* fix(category_theory/*): several minor fixes, preparatory to PR’ing the category of presheaves

In category.lean, better proofs in `instance [preorder α] : small_category α := …`.
In natural_isomorphism.lean, some rfl lemmas, natural isomorphisms describing functor composition, and formatting
In examples/topological_spaces.lean, deciding to reverse the arrows in `open_set X` (the category of open sets, with restrictions), to reduce using opposites later, as well as describing the functoriality of `open_set`.

* additional simp lemmas

### [2018-09-13T13:42:52-04:00](https://github.com/leanprover-community/mathlib/commit/a770ee5a5a46973494b2ad41e672e21cecba4471)
fix(data/padics/padic_rationals): fix proof

### [2018-09-13T12:28:42-04:00](https://github.com/leanprover-community/mathlib/commit/46502df9a61b131ee5e9265ec2593ab87b654b94)
feat(algebra/ordered_ring): mul_self_pos

### [2018-09-13T12:07:41-04:00](https://github.com/leanprover-community/mathlib/commit/bebe170786365c7d0d035a5ed7fbec4fefefb045)
feat(data/int/order): delete int.order and prove all commented out lemmas ([#348](https://github.com/leanprover-community/mathlib/pull/#348))

### [2018-09-11T13:05:07+02:00](https://github.com/leanprover-community/mathlib/commit/120635628368ec261e031cefc6d30e0304088b03)
fix(doc/tactics): fix typo in documentation of `ext`

### [2018-09-11T10:40:33+02:00](https://github.com/leanprover-community/mathlib/commit/36a82cb589c509b5731b932dcaa99bf0de6e66f6)
feat(tactic/ext): use `rcases` patterns to intro `ext` variables

### [2018-09-11T10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/ffc6bc075aaa6677098143139149dbf69f0813b9)
feat(tactic/ext): add support for propext

### [2018-09-11T10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/c25ca3b5a8c643ede14ee5e46cdd22eca423251e)
feat(tactic/ext): address reviewers' comments

### [2018-09-11T10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/4e3b89c32ee5f1109f447a6b39cff85bb9fb98af)
feat(tactic/ext): make the attribute incremental

### [2018-09-11T10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/6557f51305faea01b646c88897d5fc6de0f2cee5)
feat(tactic/ext): add indexing of extensionality lemmas

### [2018-09-11T10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/4efdbdb04150b62665ff6fbb3cde6167471d269c)
feat(tactic/ext): match extensionality lemma more exactly

### [2018-09-11T10:07:19+02:00](https://github.com/leanprover-community/mathlib/commit/ba7bd742702a78cfe99bf71e58a2750593fa5fea)
feat(category_theory): Yoneda, basic facts about natural isomorphisms, and an extensionality lemma using Yoneda lemma ([#326](https://github.com/leanprover-community/mathlib/pull/#326))

* feat(category_theory/yoneda_lemma)
* feat(category_theory/natural_isomorphisms): basic facts about natural isomorphisms, and an extensionality lemma using Yoneda

### [2018-09-10T20:50:08-04:00](https://github.com/leanprover-community/mathlib/commit/40a365acc8ad64820d2a54620aafe1f489920a68)
feat(tactic/replacer): add support for parameters in replacer

### [2018-09-10T22:46:23+02:00](https://github.com/leanprover-community/mathlib/commit/a7995c96f14c590e762e878286e6df505e52d7bb)
fix(set_theory/cofinality): fix type of omega_is_regular

### [2018-09-10T22:44:42+02:00](https://github.com/leanprover-community/mathlib/commit/0e069447d0b8b69ed59d7101de8728525ee59202)
feat(data/equiv/basic): quot_equiv_of_quot(')

quot_equiv_of_quot matches matches the existing subtype_equiv_of_subtype,
but quot_equiv_of_quot' is useful in practice and this definition is careful
to use eq.rec only in proofs.

### [2018-09-10T22:40:31+02:00](https://github.com/leanprover-community/mathlib/commit/61f4827db6d3471a127e75a7b910bfdc8993a766)
fix(logic/basic): remove unnecessary hypothesis from proof_irrel_heq

### [2018-09-10T13:57:55-04:00](https://github.com/leanprover-community/mathlib/commit/b33764d942dc8b1b7f55cace89429c948c1a4b2f)
feat(algebra/module): semimodules

### [2018-09-10T03:23:58-04:00](https://github.com/leanprover-community/mathlib/commit/56c4919a9ba35a3052544f53ab85ae57acf1c04c)
feat(tactic/abel): decision procedure for comm groups

### [2018-09-09T23:23:59-04:00](https://github.com/leanprover-community/mathlib/commit/f10e7adbedb01d95dfed407f8fcf76ce6329cbf8)
refactor(tactic/ring): remove unnecessary rat from horner_expr

### [2018-09-09T23:23:53-04:00](https://github.com/leanprover-community/mathlib/commit/eab064e84a50a3a765b8c0cdd68a8f0bc6066dd3)
refactor(tactic/ring): use horner_expr instead of destruct on expr

### [2018-09-09T23:23:45-04:00](https://github.com/leanprover-community/mathlib/commit/484afdf3555dec4edf5cda797bcde915682c06a0)
test(tests/ring): add test file for ring

### [2018-09-09T20:45:05-04:00](https://github.com/leanprover-community/mathlib/commit/181905e0d2a304f21dbe241db9c9d05dd67e2e24)
refactor(tactic/linarith): refactoring

### [2018-09-09T18:34:27+02:00](https://github.com/leanprover-community/mathlib/commit/4be1ef1af8f948ed2dda37e7de70a5cd1e8c360e)
fix

### [2018-09-09T18:34:27+02:00](https://github.com/leanprover-community/mathlib/commit/5b7edecf37abf8e9fc142470bfd5fb62a8ff81b1)
feat(category_theory): redesign of concrete categories

Also exercising it further with `def forget_to_Mon : CommRing ⥤ Mon := …`

### [2018-09-09T18:32:02+02:00](https://github.com/leanprover-community/mathlib/commit/aaa113a919886ad10dd4bfe5a997b645faec9e87)
fix(tactic/linarith): improve earlier fix

### [2018-09-09T18:32:02+02:00](https://github.com/leanprover-community/mathlib/commit/fa747b08a0690b576e223b958458cf1624618226)
fix(tactic/linarith): proper handling of 0 coefficients in input

### [2018-09-09T18:32:02+02:00](https://github.com/leanprover-community/mathlib/commit/675c235754ae8ebf0c1309eec805b4072c39e827)
fix(tactic/linarith): make more use of equality hypotheses

### [2018-09-09T15:01:18+02:00](https://github.com/leanprover-community/mathlib/commit/53cc7ced4c79a54fb7ca1a679578007dcefa84b6)
refactor(data/polynomial): generalize leading_coeff_X_pow ([#329](https://github.com/leanprover-community/mathlib/pull/#329))

Generalize `leading_coeff_X_pow` to `comm_semiring`

### [2018-09-08T19:25:06-04:00](https://github.com/leanprover-community/mathlib/commit/fc1fd3dcda346617f633cb07f2f10e0d734f8bce)
feat(set_theory/cofinality): sum_lt_of_is_regular

### [2018-09-08T20:54:21+02:00](https://github.com/leanprover-community/mathlib/commit/73abe2e1b74531a70230bf2f7c141dbbe9550318)
fix(category_theory/products): fix types of inl/inr/fst/snd ([#320](https://github.com/leanprover-community/mathlib/pull/#320))

### [2018-09-08T20:17:26+02:00](https://github.com/leanprover-community/mathlib/commit/5613d2ecc92ce8fae9555745bd94756dec61a323)
feat(tactic): add support for quotients to rcases

### [2018-09-08T11:44:06+02:00](https://github.com/leanprover-community/mathlib/commit/1b9b139657fef4185a3c2c2fb7a0e6fa9cec1540)
refactor(linear_algebra/prod_module): move prod.ring ([#322](https://github.com/leanprover-community/mathlib/pull/#322))

### [2018-09-07T17:43:56+02:00](https://github.com/leanprover-community/mathlib/commit/5aa65d6dd2827a10766eba91fcd37ca52f2d3d78)
order(filter): rename `vmap` to `comap`

### [2018-09-07T17:32:23+02:00](https://github.com/leanprover-community/mathlib/commit/2524dbadebf830b692f2b6ac6d756079a87e3f93)
fix(algebra/big_operators): change name of `sum_attach` to `finset.sum_attach`

### [2018-09-07T17:30:25+02:00](https://github.com/leanprover-community/mathlib/commit/8f8932444abc933ef142724a760a983eb7a38bd8)
style(linear_algebra/submodule): changed import order; added product construction

### [2018-09-07T17:30:25+02:00](https://github.com/leanprover-community/mathlib/commit/085c0125015c29058ce5a418e88a791cb232ee4b)
refactor(linear_algebra, ring_theory): rework submodules; move them to linear_algebra

### [2018-09-07T17:30:25+02:00](https://github.com/leanprover-community/mathlib/commit/4421f46dc2e0ec818344bcd897c1ee75ff82cbad)
feat(ring_theory): submodules and quotients of Noetherian modules are Noetherian

Co-authored-by: Kevin Buzzard <k.buzzard@imperial.ac.uk>
Co-authored-by: Johan Commelin <johan@commelin.net>
Co-authored-by: Johannes Hölzl <johannes.hoelzl@gmx.de>
Co-authored-by: Mario Carneiro <di.gama@gmail.com>

### [2018-09-07T17:27:38+02:00](https://github.com/leanprover-community/mathlib/commit/dce0e64967ca1c48ae2d9fb8625a164c46a4107c)
fix(algebra/big_operators): change name of `sum_eq_single` to `finset.sum_eq_single` ([#321](https://github.com/leanprover-community/mathlib/pull/#321))

### [2018-09-07T11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/4085ca138a1305c7803e6cc4b491e0cc486e6067)
feat(category_theory): add measurable space example

### [2018-09-07T11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/c2a4cf9e67c544842fe0c05694c6a0be6cd50d6c)
feat(category_theory): lift morphism map proof to concrete categories

### [2018-09-07T11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/93e90432734034912f47fece682ffaf07fab3665)
style(category_theory): concrete categories as type class

### [2018-09-07T11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/5c484898fba1ee8cdd2e1c51bca1732de0091707)
feat(category_theory): construction for a concrete category

### [2018-09-07T11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/840a733cb7938b5a2327b0e408d85c4ed1d39135)
removing unnecessary class

### [2018-09-07T11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/d91428c2d3e52384a94f0c33ce94ec7f6a90c844)
feat(category_theory): the category of topological spaces, and of neighbourhoods of a point. also the category of commutative rings

### [2018-09-07T09:20:27+02:00](https://github.com/leanprover-community/mathlib/commit/e95111d38c0b2d666f70624ce25a5d728e0db376)
fix(tactic/tidy): fix interactive tidy ignoring cfg

### [2018-09-06T15:59:41-04:00](https://github.com/leanprover-community/mathlib/commit/77e104ce5cdea1c969044046e1c97c68fc2104ab)
fix(tests/tactics): remove test

I don't think this test demonstrates reasonable/expected behavior of `wlog`, and it is not maintained by the modification, so I've removed it.

### [2018-09-06T15:39:55-04:00](https://github.com/leanprover-community/mathlib/commit/ea61c21262bbb27a547993b6a54f3dad59658d83)
fix(tactic/wlog): fix segfault

### [2018-09-06T20:28:13+02:00](https://github.com/leanprover-community/mathlib/commit/384224495f87af97b9d80839877bc4b3ff4e9236)
fix(linear_algebra/subtype): simplify lifted operations by using projections instead of match

### [2018-09-06T01:04:28+02:00](https://github.com/leanprover-community/mathlib/commit/f262a07c33b7e5a244c60af11a5bcf544932bd81)
fix(linear_algebra/quotient_module): ring parameter for base ring of quotient module needs to be implicit, otherwise type class search loops

### [2018-09-05T23:46:03+02:00](https://github.com/leanprover-community/mathlib/commit/e24f54e82b2878812becf52c5161505ed1a730af)
fix(linear_algebra/prod): field is implicit parameter of the module / vector space product instances

### [2018-09-05T21:44:40+02:00](https://github.com/leanprover-community/mathlib/commit/016f5386612f1cf1b05d2294eb9e6a35a0244c7a)
fix(algebra/module): add out_param to base field of vector spaces

### [2018-09-05T14:33:30+02:00](https://github.com/leanprover-community/mathlib/commit/3a3249eaf9e54ac8c030d37f90f62b0e5059b1b8)
feat(data/finsupp): multiset_map_sum/_sum_sum/_index

### [2018-09-05T14:19:36+02:00](https://github.com/leanprover-community/mathlib/commit/92b9a00d65ef3685ddef8193c7df4b4114a5e3be)
feat(data/finsupp): to_/of_multiset, curry/uncurry

### [2018-09-05T14:05:50+02:00](https://github.com/leanprover-community/mathlib/commit/e105c9eabf081714fd75ed9efb70ef331a8f36d8)
feat(data/multiset): add prod_map_add

### [2018-09-05T14:04:54+02:00](https://github.com/leanprover-community/mathlib/commit/abd6ab59d2865767a2d71e73ccec6e4b4f748add)
refactor(data/prod): add map_fst, map_snd

### [2018-09-05T13:15:42+02:00](https://github.com/leanprover-community/mathlib/commit/ac4f7b166c4ad302bece9618ff90e16a2adb5e01)
Revert "doc(docs/elan.md): Clarify instructions for leanpkg build"

This reverts commit 89e8cfee313b8bffe70362949577bd575cd09ea5.

### [2018-09-05T11:54:07+02:00](https://github.com/leanprover-community/mathlib/commit/9ea38e1e0d662f5f9931e89493e43c6e9299d21f)
feat(data/finset): option.to_finset

### [2018-09-05T11:53:36+02:00](https://github.com/leanprover-community/mathlib/commit/2997ce6d490c10f494fd0ca30a85a7ac6fb7ca60)
feat(logic/embedding): embedding into option

### [2018-09-05T11:52:47+02:00](https://github.com/leanprover-community/mathlib/commit/a2acc6116006d3019186f7be67d30d7b68e2844b)
doc(docs/howto-contribute.md): fix broken links

### [2018-09-05T11:51:46+02:00](https://github.com/leanprover-community/mathlib/commit/89e8cfee313b8bffe70362949577bd575cd09ea5)
doc(docs/elan.md): Clarify instructions for leanpkg build

### [2018-09-05T11:51:18+02:00](https://github.com/leanprover-community/mathlib/commit/97cd01b019ea2cd9464731aad61071c3c1309301)
refactor(linear_algebra/quotient_module): avoid using type class inference for setoids ([#310](https://github.com/leanprover-community/mathlib/pull/#310))

Continuation of [#212](https://github.com/leanprover-community/mathlib/pull/#212) . Avoid using type class inference for quotient modules, and introduce a version of `quotient.mk` specifically for quotient modules, whose output type is `quotient β s` rather than `quotient (quotient_rel s)`, which should help type class inference.

### [2018-09-05T11:49:04+02:00](https://github.com/leanprover-community/mathlib/commit/681c98f301d2f0b10c75cba6a850712d4c51fb8a)
feat(category_theory): full subcategories, preorders, Aut, and End

### [2018-09-05T09:08:50+02:00](https://github.com/leanprover-community/mathlib/commit/600d3cf6a9dd897f4d7c9b0cdbdd0b79a480397f)
cleanup(data/polynomial): shorten some proofs

### [2018-09-04T19:56:23+02:00](https://github.com/leanprover-community/mathlib/commit/76de588dd96934d3055f3a6a31b6b6cde0000820)
feat(data/polynomial): prove degree_derivative_eq

### [2018-09-04T10:43:33+02:00](https://github.com/leanprover-community/mathlib/commit/eb20fd059017bda423612b7b19a525f95c4593b4)
feat(data/polynomial): derivative on polynomials

### [2018-09-04T02:25:20-04:00](https://github.com/leanprover-community/mathlib/commit/fd43fe08c88149c7a05cfc6ec24a60b16bb1fad8)
fix(data/polynomial): fix proofs

### [2018-09-04T01:53:38-04:00](https://github.com/leanprover-community/mathlib/commit/7a4125bc8d36e42cf649ab09212623e7c399d38d)
feat(algebra/field): field homs

### [2018-09-04T01:49:52-04:00](https://github.com/leanprover-community/mathlib/commit/2dd78b8d6ed23c434c4022fd3d402ea108a9b785)
feat(data/polynomial): add eval2 for univariate polys

### [2018-09-04T00:35:50-04:00](https://github.com/leanprover-community/mathlib/commit/b8ea49bd812fa7f399920c2a5699be8a4ec40a5f)
fix(ring_theory/ufd): fix simpa uses

### [2018-09-03T18:31:34-04:00](https://github.com/leanprover-community/mathlib/commit/4de119e5a16b9a27febbfe74d6f908a1d152e740)
fix(*): fix simpa uses

### [2018-09-03T16:58:55-04:00](https://github.com/leanprover-community/mathlib/commit/2021a1bea348365a8e535bd348d5bd15dff8f6d3)
perf(tactic/ring): don't do any implicit unfolds

### [2018-09-03T16:58:38-04:00](https://github.com/leanprover-community/mathlib/commit/1edb79aec525a90b54bf5fbc5c76b254dbe81381)
refactor(ring_theory/associated): rename associated_elements

### [2018-09-03T16:58:38-04:00](https://github.com/leanprover-community/mathlib/commit/956398c7704f90cf759b4d41c1b137ebe5038c9f)
refactor(tactic/interactive): improve error reporting for simpa

also make simpa fail on no goals or when applied where simp will work

### [2018-09-03T12:33:54+02:00](https://github.com/leanprover-community/mathlib/commit/36dd78ee328b93f7bbf36b001807060efb562822)
feat(category_theory): full and faithful functors, switching products

also the evaluation functor, and replace the ↝ arrow with ⥤, by request

### [2018-09-03T12:32:04+02:00](https://github.com/leanprover-community/mathlib/commit/6ddc3fc032d526db839b7adac1b9fbbbb62ddd88)
feat(data/finset): max_of_ne_empty, min_of_ne_empty

### [2018-09-03T01:27:28+02:00](https://github.com/leanprover-community/mathlib/commit/7ee76148e81ae25d832a27f81dc4d47b22800128)
feat(category_theory/isomorphisms): introduce isomorphisms ([#278](https://github.com/leanprover-community/mathlib/pull/#278))

* refactor(category_theory): renaming `ulift` to `ulift_functor` to avoid name clashes

* feat(category_theory): introduce isomorphisms

* doc(category_theory): rewrite

* Resolving issues raised by Johannes

* moving heterogenous_identity.lean into isomorphism.lean

* remove unnecessary `obviously` replacement

* refactor(category_theory): using tidy in the category theory library

### [2018-09-03T00:10:15+02:00](https://github.com/leanprover-community/mathlib/commit/0df6f7783f45bc73572a4bc611b029068af846bb)
style(linear_algebra/tensor_product): rename of -> tmul and ⊗ₛ -> ⊗ₜ; some cleanup in free_abelian_group

### [2018-09-02T23:49:36+02:00](https://github.com/leanprover-community/mathlib/commit/40ef7a2bae7bba9b8e65888ca3c756e0607a1a61)
doc(ring_theory/unique_factorization_domain): add document strings

### [2018-09-02T16:35:13-04:00](https://github.com/leanprover-community/mathlib/commit/b3afef56cf5ae48047e3fd551a448955e2edd1a4)
perf(tactic/ring): fix long-running mk_app invocations

### [2018-09-02T20:50:34+02:00](https://github.com/leanprover-community/mathlib/commit/dd0c0aeefcaf6a438ab4273d7a1f42e1b8225847)
feat(ring_theory): add unique factorization domain

### [2018-09-02T20:50:34+02:00](https://github.com/leanprover-community/mathlib/commit/5f8fafcfee4e64a57d9c7322458eac794803581f)
feat(ring_theory): add associated elements

### [2018-09-02T20:07:13+02:00](https://github.com/leanprover-community/mathlib/commit/059f9374d9dc79375368e61054f12e1800aad253)
feat(tactic): add linear arithmetic tactic ([#301](https://github.com/leanprover-community/mathlib/pull/#301))

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

### [2018-09-02T19:58:41+02:00](https://github.com/leanprover-community/mathlib/commit/8c19da7e4ca6f9e0678c582e5db28401e682480d)
feat(data/polynomial): has_repr for polynomials ([#302](https://github.com/leanprover-community/mathlib/pull/#302))

Not sure if I should change this so that it will always return a string that will not cause any problems if copied and pasted into a lemma. It does this for rationals and integers, although for rationals, it returns something equal to the polynomial you would like, but probably not the polynomial you actually want, i.e. `(2 / 3 : polynomial ℚ)` more or less gives you `(C 2 / C 3)`, rather than `C (2 / 3)`. These expressions are def eq, but not in any reasonable amount of time as soon as the size gets slightly larger.

### [2018-09-02T19:54:22+02:00](https://github.com/leanprover-community/mathlib/commit/2594f48f20392f84b0743eb0867c030913eca627)
style(linear_algebra/tensor_product): renaming and changing some proofs

### [2018-09-02T19:54:22+02:00](https://github.com/leanprover-community/mathlib/commit/4b5ad0ea6e111e55a2af714e8d8e623fd139e2d3)
feat(linear_algebra,group_theory): add tensor product and supporting material

### [2018-09-02T13:36:43-04:00](https://github.com/leanprover-community/mathlib/commit/dd6b0351034e61509fbcee9ebe167a85ea88b372)
feat(data/option): add simp lemmas for orelse

### [2018-09-02T17:21:22+00:00](https://github.com/leanprover-community/mathlib/commit/3de3cfb3b6cba608e62a365fdaae40d50cb4b6da)
feat(tactic/subtype_instance): generating subtype instances

### [2018-09-01T13:10:14+02:00](https://github.com/leanprover-community/mathlib/commit/b7b05fbb7dc76f7dbbc93549d3ac1c34ce7a78a7)
style(ring_theory): rename PID to principal_ideal_domain

### [2018-08-31T17:48:25+02:00](https://github.com/leanprover-community/mathlib/commit/20b4143976dad48e664c4847b75a85237dca0a89)
feat(algebra): add normalization and GCD domain; setup for int

### [2018-08-31T17:48:25+02:00](https://github.com/leanprover-community/mathlib/commit/5df7cacba431bf8d9946f79dc02479c417281335)
refactor(data/int/gcd): move int gcd proofs to the GCD theory

### [2018-08-31T17:48:25+02:00](https://github.com/leanprover-community/mathlib/commit/a89f28e0c41f9f03fec691dbd86ad356baf3219d)
feat(data/int/gcd): extended gcd to integers ([#218](https://github.com/leanprover-community/mathlib/pull/#218))

Resurrected by @johoelzl. The original commit was not available anymore.

### [2018-08-31T14:44:58+02:00](https://github.com/leanprover-community/mathlib/commit/ee9bf5c921a18c0d4ff32bd33eb1a7aa6608a61e)
feat(data/equiv): equiv_congr and perm_congr

### [2018-08-31T09:14:34+02:00](https://github.com/leanprover-community/mathlib/commit/4068d00510be3285b03e88d76af2a31e30f1e054)
feat(data/nat): simp rules for find_greatest

### [2018-08-31T01:45:14+02:00](https://github.com/leanprover-community/mathlib/commit/2946088eb40a0df9588cc9a24522fb1c175b1b25)
feat(tactic/explode): line by line proof display for proof terms

### [2018-08-30T18:39:48+02:00](https://github.com/leanprover-community/mathlib/commit/86c955eb424b70b493aa5b9594a91a0a14ba462d)
feat(data/nat): find_greatest is always bounded

### [2018-08-30T17:30:19+02:00](https://github.com/leanprover-community/mathlib/commit/c238aadbefe720d2f30913b87c1e2d2d6a500d2c)
refactor(data/nat): simplify find_greatest; fix namespace nat.nat.find_greatest -> nat.find_greatest

### [2018-08-30T15:34:45+02:00](https://github.com/leanprover-community/mathlib/commit/83edcc06081343fc29e1f21f3fd35af825572858)
refactor(data/nat,int): separate int from nat, i.e. do not import any int theory in nat

### [2018-08-30T14:55:56+02:00](https://github.com/leanprover-community/mathlib/commit/d2451658af16093c8fe2c84e64e18cf4dcad87d7)
refactor(algebra): add more facts about units

### [2018-08-30T13:27:07+02:00](https://github.com/leanprover-community/mathlib/commit/b4b05dd2fba74daaafffe8684b155b8e11c3329a)
feat(logic/basic): introduce pempty

### [2018-08-29T15:07:11+02:00](https://github.com/leanprover-community/mathlib/commit/afd1c063638d611fda65db7499ccbd7257c90870)
feat(algebra/group): is_add_group_hom

### [2018-08-29T14:48:07+02:00](https://github.com/leanprover-community/mathlib/commit/b0aadaaa473f0250a9faa2d87a73c1d8d6fe6af7)
cleanup(analysis/bounded_linear_maps): some reorganization

### [2018-08-29T14:48:07+02:00](https://github.com/leanprover-community/mathlib/commit/21a935525eaa57fb318ba2c157bc5e74f8159a23)
feat(analysis/continuous_linear_maps)

### [2018-08-29T14:38:32+02:00](https://github.com/leanprover-community/mathlib/commit/49f700c77704e3162cb46252fb48545bf8066565)
feat(analysis/topology/uniform_space): prepare for completions ([#297](https://github.com/leanprover-community/mathlib/pull/#297))

### [2018-08-29T02:55:13+02:00](https://github.com/leanprover-community/mathlib/commit/0c11112c966e60e4aaa3cad158fa0c10e303dee0)
feat(logic/function): adds uncurry_def ([#293](https://github.com/leanprover-community/mathlib/pull/#293))

### [2018-08-29T02:53:42+02:00](https://github.com/leanprover-community/mathlib/commit/b82ba3c12d7422694734c08eccf9294acd18760b)
feat(data/multiset): multisets are traversable using commutative, applicative functors ([#220](https://github.com/leanprover-community/mathlib/pull/#220))

### [2018-08-29T02:46:53+02:00](https://github.com/leanprover-community/mathlib/commit/3e38b7339266f07896f2bc47acc84e567054e83e)
feat(analysis/topology): density and continuity lemmas ([#292](https://github.com/leanprover-community/mathlib/pull/#292))

Still from the perfectoid project

### [2018-08-29T02:45:15+02:00](https://github.com/leanprover-community/mathlib/commit/4eca29f3b657bde7a1d55b8906cd62c6b2aa2bcd)
doc(docs/howto-contribute.md): How to contribute to mathlib ([#291](https://github.com/leanprover-community/mathlib/pull/#291))

### [2018-08-29T02:42:39+02:00](https://github.com/leanprover-community/mathlib/commit/79bb95c52a06a91f5f93020a9f0a78c10d2b7350)
feat(analysis/topology, data/set): some zerology ([#295](https://github.com/leanprover-community/mathlib/pull/#295))

### [2018-08-29T02:26:04+02:00](https://github.com/leanprover-community/mathlib/commit/49fb2db36ad782cc92b58d43d9de23ea55531317)
fix(docs/style): precise a style rule and fixes a github markdown issue ([#290](https://github.com/leanprover-community/mathlib/pull/#290))

### [2018-08-29T00:28:03+02:00](https://github.com/leanprover-community/mathlib/commit/bab38133803b6fb252211d174de612745c9cc56f)
feat(ring_theory/PID): PIDs and xgcd for ED ([#298](https://github.com/leanprover-community/mathlib/pull/#298))

### [2018-08-28T20:10:13+02:00](https://github.com/leanprover-community/mathlib/commit/cd731156a1964ac8d9803012a794bf2211a1b246)
refactor(data/set/basic): clean up [#288](https://github.com/leanprover-community/mathlib/pull/#288) and [#289](https://github.com/leanprover-community/mathlib/pull/#289)

### [2018-08-28T20:09:53+02:00](https://github.com/leanprover-community/mathlib/commit/8d3bd80b9817ec11ea644d77181bf911042c9a06)
feat(tactic/tidy): add tidy tactic ([#285](https://github.com/leanprover-community/mathlib/pull/#285))

### [2018-08-28T19:40:10+02:00](https://github.com/leanprover-community/mathlib/commit/9ad32e72da18a3194ad3ae85aed954957cdffcc5)
feat(order/filter): More lemmas from perfectoid project ([#289](https://github.com/leanprover-community/mathlib/pull/#289))

### [2018-08-28T19:38:58+02:00](https://github.com/leanprover-community/mathlib/commit/3f65a93088ea9fd3794497f75f7adc09aa555d2d)
fix(tactic/restate_axiom): change default naming in restate_axiom ([#286](https://github.com/leanprover-community/mathlib/pull/#286))

* beginning renaming

* modifying names in restate_axiom

* removing ematch attributes from category_theory

* improving behaviour of `restate_axiom`, documenting and testing

* oops

### [2018-08-28T17:33:14+02:00](https://github.com/leanprover-community/mathlib/commit/ed5a33890b7e4b43cae7e15034381dfd62867c21)
feat(data/set/basic): some more basic set lemmas ([#288](https://github.com/leanprover-community/mathlib/pull/#288))

### [2018-08-28T15:08:37+02:00](https://github.com/leanprover-community/mathlib/commit/39ffeab1c28041c3f444fded8edce1a606b29cb2)
feat(analysis): add normed spaces

### [2018-08-28T15:05:42+02:00](https://github.com/leanprover-community/mathlib/commit/2b9c9a803225492fc6061614360a4c37ee5bb601)
refactor(analysis): add nndist; add finite product of metric spaces; prepare for normed spaces

### [2018-08-28T15:05:42+02:00](https://github.com/leanprover-community/mathlib/commit/41f567485f0415df0f2bf1352dea86fc4bf1512a)
fix(algebra/pi_modules): pi instance for module shouldn't search for the ring structure

### [2018-08-28T14:39:03+02:00](https://github.com/leanprover-community/mathlib/commit/5c221a31d964d68273520d83efe273ebb2ce8c14)
feat(order/conditionally_complete_lattic): nat is a conditionally complete linear order with bottom

### [2018-08-28T10:22:25+02:00](https://github.com/leanprover-community/mathlib/commit/de67f542344d1d6f4c94724d28a4f1abe2405cbc)
feat(data/real): cauchy sequence limit lemmas ([#61](https://github.com/leanprover-community/mathlib/pull/#61))

### [2018-08-28T00:08:50+02:00](https://github.com/leanprover-community/mathlib/commit/c420885d8a30102cb77966634e44d7331812a219)
fix(tactic/interactive): try reflexivity after substs ([#275](https://github.com/leanprover-community/mathlib/pull/#275))

This brings `substs` closer to being equivalent to a sequence of `subst`.

### [2018-08-28T00:06:47+02:00](https://github.com/leanprover-community/mathlib/commit/bca8d491eecf0e5186c0424baf937ea294d01419)
chore(data/array, data/buffer): Array and buffer cleanup ([#277](https://github.com/leanprover-community/mathlib/pull/#277))

### [2018-08-27T23:02:59+02:00](https://github.com/leanprover-community/mathlib/commit/c52b317f85e63b47c6ade2b1aac5849ba904b4fa)
refactor(data/finsupp): generalise finsupp.to_module ([#284](https://github.com/leanprover-community/mathlib/pull/#284))

### [2018-08-27T16:48:59+02:00](https://github.com/leanprover-community/mathlib/commit/9aa2bb0c8aad2fab749e977d1c4804c5f7413d8f)
feat(data/fin): last ([#273](https://github.com/leanprover-community/mathlib/pull/#273))

### [2018-08-27T16:48:29+02:00](https://github.com/leanprover-community/mathlib/commit/a3a9e2496b8ac8ed170f8be43d214996f92b2f4d)
bug(tactic/interactive): make `solve_by_elim` fail on no goals ([#279](https://github.com/leanprover-community/mathlib/pull/#279))

### [2018-08-27T16:46:13+02:00](https://github.com/leanprover-community/mathlib/commit/c13a7711450835bd8e53c128f12909615a5a1d90)
feat(data/list): join_eq_nil, join_repeat_nil ([#274](https://github.com/leanprover-community/mathlib/pull/#274))

### [2018-08-27T14:37:37+02:00](https://github.com/leanprover-community/mathlib/commit/92e9d64c9da5e6e1c52bbb690b4bef7a19d4cc18)
feat(category_theory): restating functor.map and nat_trans.app ([#268](https://github.com/leanprover-community/mathlib/pull/#268))

### [2018-08-27T14:18:50+02:00](https://github.com/leanprover-community/mathlib/commit/e95589746746cd6c74037a07ce1c55899dbd5bd6)
fix(travis.yml): adding a third stage to the travis build ([#281](https://github.com/leanprover-community/mathlib/pull/#281))

### [2018-08-22T19:50:16+02:00](https://github.com/leanprover-community/mathlib/commit/58cfe9f84feae93ed9b894754e60e2a3d049a251)
bug(ext): failure on ext lemmas with no hypotheses ([#269](https://github.com/leanprover-community/mathlib/pull/#269))

### [2018-08-22T19:48:06+02:00](https://github.com/leanprover-community/mathlib/commit/d18a3a8215aed0458d1909a50647d2165746e18e)
doc(docs/tactics): add information on congr' ([#270](https://github.com/leanprover-community/mathlib/pull/#270)) [ci-skip]

### [2018-08-22T19:46:57+02:00](https://github.com/leanprover-community/mathlib/commit/0934d7d9d03e7737dabca48b15c932b2c0dd7dca)
refactor(data/nat/prime): mem_factors_iff_dvd ([#272](https://github.com/leanprover-community/mathlib/pull/#272))

### [2018-08-22T19:37:12+02:00](https://github.com/leanprover-community/mathlib/commit/974987cead1f45eba98980ec4bf839835c75ebb8)
refactor(data/nat/prime): cleanup exists_infinite_primes ([#271](https://github.com/leanprover-community/mathlib/pull/#271))

* removing unnecessary initial step
* giving names to ambiguous copies of `this`

### [2018-08-21T22:05:08+02:00](https://github.com/leanprover-community/mathlib/commit/b3fc801318bdb28121f3e3974b287cdcf4d63032)
refactor(data/real/nnreal): derive order structure for ennreal from with_top nnreal

### [2018-08-21T21:22:03+02:00](https://github.com/leanprover-community/mathlib/commit/82512ee8c1b7d1c7552d3e61fbe5e0bf5f1ca5d3)
refactor(analysis/ennreal): use canonically_ordered_comm_semiring (with_top α)

### [2018-08-21T21:22:03+02:00](https://github.com/leanprover-community/mathlib/commit/6f316375a289a3ec391a74976366a574994dd154)
refactor(analysis/nnreal): split up into data.real and analysis part

### [2018-08-21T21:22:03+02:00](https://github.com/leanprover-community/mathlib/commit/ca1b2d1d667093c5bda828a7664e535f08f50315)
refactor(analysis/measure_theory/measurable_space): derive complete lattice structure from Galois insertion

### [2018-08-18T12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/29ad1c8ff2ea87620f99840ce6f03f40f759b2b2)
feat(order/complete_lattice): add rewrite rules for Inf/Sup/infi/supr for pi and Prop

### [2018-08-18T12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/202ac15b33193b0dbd794c658eb5450fdf6f76b3)
refactor(analysis/topology/topological_space): simplify proof of nhds_supr using Galois connection

### [2018-08-18T12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/6cab92ee379320a5cce8d43f978de5db2b5b9b52)
refactor(analysis/topology/topological_space): derive complete lattice structure from Galois insertion

### [2018-08-18T12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/f9434fa101fd285dbf59f17928c95b8f9cb16e14)
refactor(order/filter): derive complete lattice structure from Galois insertion

### [2018-08-18T12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/a423cc75c9bab0b9eb3478b28d8f7625a8d66433)
refactor(order/filter): simplify filter structure

### [2018-08-18T12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/849ed4f9bc23aaf35f1464438b36a0ad51695940)
feat(order/galois_connection): add Galois insertion and lattice lifts along a Galois insertion

### [2018-08-18T01:02:27-04:00](https://github.com/leanprover-community/mathlib/commit/0ff11df2f6d66151241797d592d19f32c2a747af)
refactor(group_theory/order_of_element): use gpowers instead of range ([#265](https://github.com/leanprover-community/mathlib/pull/#265))

### [2018-08-18T01:00:59-04:00](https://github.com/leanprover-community/mathlib/commit/29508f27f68f128fceddc114ba0d077e7e6e2715)
doc(tactic/solve_by_elim): update doc ([#266](https://github.com/leanprover-community/mathlib/pull/#266)) [ci-skip]

### [2018-08-18T01:00:24-04:00](https://github.com/leanprover-community/mathlib/commit/157004cdda01aae2ec8c3fbc625e27f94f64a796)
feat(data/list/basic): some more theorems about sublist ([#264](https://github.com/leanprover-community/mathlib/pull/#264))

### [2018-08-18T00:57:52-04:00](https://github.com/leanprover-community/mathlib/commit/dfc9f8ee03fbad10963f18c6934d7b2342e29f03)
chore(build): prune deleted .lean files and their .olean files

### [2018-08-18T00:55:17-04:00](https://github.com/leanprover-community/mathlib/commit/cfb27cbef6325464446bdce0a5c2dc20d6dde155)
feat(category_theory): opposites, and the category of types ([#249](https://github.com/leanprover-community/mathlib/pull/#249))

### [2018-08-16T11:32:39-04:00](https://github.com/leanprover-community/mathlib/commit/12d103c2be5228087e61f02fb3414ca10b6dc69b)
fix(padics/padic_norm): remove spurious import

### [2018-08-16T11:31:57-04:00](https://github.com/leanprover-community/mathlib/commit/1bca59b01a734e825e4ccd33ea9a6993241991a6)
refactor(tactic/basic): simplify definition

### [2018-08-16T11:23:04-04:00](https://github.com/leanprover-community/mathlib/commit/93817f176e52f04afd2654de6e1ed15cca6f1cc8)
feat(data/padics): p-adic numbers ([#262](https://github.com/leanprover-community/mathlib/pull/#262))

### [2018-08-16T07:09:33-04:00](https://github.com/leanprover-community/mathlib/commit/47a377d2aff88cd3bbfcbeb2994aca8e9626a095)
refactor(group_theory/quotient_group): remove duplicate definition ([#259](https://github.com/leanprover-community/mathlib/pull/#259))

### [2018-08-16T06:58:15-04:00](https://github.com/leanprover-community/mathlib/commit/032e21decea172084981b579355607d984eed1c5)
feat(topological_structures): frontier_lt_subset_eq

Based on a suggestion by Luca Gerolla

### [2018-08-15T20:54:08-04:00](https://github.com/leanprover-community/mathlib/commit/d468921eac06b02767dd2b507a7f9e0cfa40cdfc)
fix(tactic/basic): fix build

### [2018-08-15T20:47:08-04:00](https://github.com/leanprover-community/mathlib/commit/bde213286841324928e2d32af041e12fa2678148)
feat(category/traversable): derive traversable instances

Authors: Simon Hudon, Mario Carneiro

### [2018-08-15T20:29:33-04:00](https://github.com/leanprover-community/mathlib/commit/d288f07d16dc4493db86e029c91b51a5358246e1)
feat(docs/*): Docs theories ([#251](https://github.com/leanprover-community/mathlib/pull/#251))

Authors: Patrick Massot, Kevin Buzzard, Chris Hughes, Scott Morrison

### [2018-08-15T20:25:34-04:00](https://github.com/leanprover-community/mathlib/commit/5d791c6babff9fb6e95d00634788dcbf51b105b4)
feat(data/polynomial): nth_roots ([#260](https://github.com/leanprover-community/mathlib/pull/#260))

### [2018-08-15T20:22:47-04:00](https://github.com/leanprover-community/mathlib/commit/6e21c48e3cafb41f2b6f5cf745b86569fe3b02fa)
feat(data/multiset): count_filter

### [2018-08-15T18:43:52-04:00](https://github.com/leanprover-community/mathlib/commit/46229d2a86799b85724d5bccc86ee6ba9414a7cf)
feat(data/multiset): filter_congr, filter_filter

### [2018-08-15T18:17:20-04:00](https://github.com/leanprover-community/mathlib/commit/4c843f2049cd0479ddef0892b547bf1937a4a76e)
refactor(category/basic): move {list,option}.traverse to category.basic

### [2018-08-15T18:16:17-04:00](https://github.com/leanprover-community/mathlib/commit/1aae37cbd8791ce7a0af03308008b964f4e6641f)
refactor(tactic/basic): move meta.expr to tactic.basic, cleanup

### [2018-08-15T18:14:01-04:00](https://github.com/leanprover-community/mathlib/commit/0738d4e062aae9b5d5b4b6aad8f4e04c98606ca0)
feat(tactic/basic): environment.is_structure

### [2018-08-15T15:47:27-04:00](https://github.com/leanprover-community/mathlib/commit/4a7103dd54f1a789996d0b323910ccbfbf83c4d7)
refactor(topology/uniform_space): proof simplification / extension

### [2018-08-15T10:16:37-04:00](https://github.com/leanprover-community/mathlib/commit/b4dc0a553fb811e4010f997939c41710cd2e1f4c)
feat(analysis/metric_space): Lebesgue number lemma for uniform spaces and metric spaces ([#237](https://github.com/leanprover-community/mathlib/pull/#237))

### [2018-08-14T13:14:13-04:00](https://github.com/leanprover-community/mathlib/commit/7c1d3b4d7805f3ee6d7d2bbb5bcc5bb87640fe8e)
refactor(data/equiv/basic): simplify definition of `equiv.of_bijective`

### [2018-08-14T16:11:37+02:00](https://github.com/leanprover-community/mathlib/commit/add16e97388a486a25569d8a905d29b5c293f3fb)
feat(order): add order_dual (similar to with_top/with_bot) and dual order instances

### [2018-08-14T05:14:40-04:00](https://github.com/leanprover-community/mathlib/commit/f81c764e7ece30508581d327d066061b20590781)
doc(data/rat): todo [ci-skip]

### [2018-08-14T05:07:05-04:00](https://github.com/leanprover-community/mathlib/commit/6359010c7ea61f34ff69254052315a13ae6f28da)
feat(data/list/perm): subperm_cons_diff and subset_cons_diff ([#256](https://github.com/leanprover-community/mathlib/pull/#256))

### [2018-08-14T04:59:55-04:00](https://github.com/leanprover-community/mathlib/commit/e53c2bbb95c0eb9d3e612536d97a1eafb521e8a9)
perf(data/rat): add more extra typeclass instances

### [2018-08-14T01:44:16-04:00](https://github.com/leanprover-community/mathlib/commit/638b7fd49002bdaa8488a9de7021a3dbc69b9430)
feat(set_theory/cardinal): finite lower bound on cardinality

### [2018-08-14T01:42:29-04:00](https://github.com/leanprover-community/mathlib/commit/9699f8dc98c29e2b1ae27d4a1044a16cae1003b9)
feat(data/multiset): some more theorems about diagonal

### [2018-08-14T01:41:49-04:00](https://github.com/leanprover-community/mathlib/commit/d016186fd8028db4d1bd0219672548bc5c763b6a)
fix(tactic/norm_num): make norm_num only apply to current goal

### [2018-08-13T07:53:08-04:00](https://github.com/leanprover-community/mathlib/commit/8692959b9be95d064ac892e0a3f01d7f1d93cb14)
feat(data/list/basic): diff_sublist_of_sublist

### [2018-08-13T11:25:34+02:00](https://github.com/leanprover-community/mathlib/commit/4bc2287191615118298652834f5008a8bd88cc21)
fix(.): fix up ext usages (c.f. 7cfc299fcdcae715dc0ac33cba0cd1aefa9777cd)

### [2018-08-13T03:50:00-04:00](https://github.com/leanprover-community/mathlib/commit/89d71ad04dce3c0363d8428d3e73adfb7af107e9)
fix(tactic/basic): make `try_intros` not fail given too few names

### [2018-08-13T03:05:01-04:00](https://github.com/leanprover-community/mathlib/commit/9ea932410509691360ecca272d490248f5a73f0c)
fix(category/basic): change "try" to "mtry"

### [2018-08-13T02:53:31-04:00](https://github.com/leanprover-community/mathlib/commit/771463247b2f696e5ecf7f3891e7519eaf018c70)
fix(category/basic): fix build

### [2018-08-13T02:46:45-04:00](https://github.com/leanprover-community/mathlib/commit/7cfc299fcdcae715dc0ac33cba0cd1aefa9777cd)
refactor(tactic/interactive): minor cleanup, change `ext` notation

### [2018-08-12T08:52:56-04:00](https://github.com/leanprover-community/mathlib/commit/522d3ea7295ca7d2f8552256ba61ef704d17e091)
refactor(data/list/basic): simplify proof

### [2018-08-12T17:09:22+10:00](https://github.com/leanprover-community/mathlib/commit/26ef0a0238486fba061e566ddf289688ac6ffabf)
feat(data/list/basic): diff_subset and mem_diff_of_mem

### [2018-08-11T03:59:51-04:00](https://github.com/leanprover-community/mathlib/commit/6bf879d2c6b974401bcf402746ff3d529e31901b)
fix(category_theory): consistent use of coercions, consistent naming ([#248](https://github.com/leanprover-community/mathlib/pull/#248))

### [2018-08-10T14:02:33-04:00](https://github.com/leanprover-community/mathlib/commit/e34fec87e49ffe66dac1fb37a0e48436bebd4a9a)
fix(tests/examples): fix test

### [2018-08-10T12:44:38-04:00](https://github.com/leanprover-community/mathlib/commit/57194fa57e76721a517d6969ee88a6007f0722b3)
fix(tactic/wlog): fix issue causing segfault

### [2018-08-10T12:44:38-04:00](https://github.com/leanprover-community/mathlib/commit/a679c9843ab0c4f6b66acd4bac5e7d2fb28212f1)
refactor(data/multiset): shorten proof

### [2018-08-10T10:05:03-04:00](https://github.com/leanprover-community/mathlib/commit/24aeeaff24d1c3a5b1f32e79f5cbd77afedee5eb)
feat(data/zmod): integers mod n ([#159](https://github.com/leanprover-community/mathlib/pull/#159))

### [2018-08-10T09:44:20-04:00](https://github.com/leanprover-community/mathlib/commit/e1312b4d3635ebe90b6fbe1707f515707d68c959)
feat(group_theory/perm): signatures of permutations ([#231](https://github.com/leanprover-community/mathlib/pull/#231))

### [2018-08-10T09:14:19-04:00](https://github.com/leanprover-community/mathlib/commit/251a8c367bec656a85a70894b169a1e555efd2bd)
feat(tactic/assoc_rewrite): new tactic for implicitly applying associativity before rewriting ([#228](https://github.com/leanprover-community/mathlib/pull/#228))

### [2018-08-10T09:07:20-04:00](https://github.com/leanprover-community/mathlib/commit/ff250839fef5de2845e0bea714eb3b250c6c1087)
feat(data/list/basic): nil_diff and diff_sublist ([#235](https://github.com/leanprover-community/mathlib/pull/#235))

### [2018-08-10T09:06:41-04:00](https://github.com/leanprover-community/mathlib/commit/26ef4192497bfefd3ba0e1d37e8a05e2c9f98a51)
feat(data/fintype): fintype and decidable_eq for partial functions ([#236](https://github.com/leanprover-community/mathlib/pull/#236))

### [2018-08-10T09:04:15-04:00](https://github.com/leanprover-community/mathlib/commit/e2521c31d3907dcecfa3e08b1f14fb9e01087648)
feat(data/set/finite): card_image_of_injective and other minor lemmas ([#245](https://github.com/leanprover-community/mathlib/pull/#245))

### [2018-08-10T08:52:34-04:00](https://github.com/leanprover-community/mathlib/commit/d40051018ac7504d440cb1cb6e510cb33fd032bc)
feat(data/nat/binomial): the binomial theorem ([#214](https://github.com/leanprover-community/mathlib/pull/#214))

### [2018-08-10T08:50:52-04:00](https://github.com/leanprover-community/mathlib/commit/54ce15b598f6b90c80584fc3810568cbef7a9ef8)
refactor(ring_theory/ideals): avoid using type class inference for setoids in quotient rings and groups ([#212](https://github.com/leanprover-community/mathlib/pull/#212))

### [2018-08-10T07:12:29-04:00](https://github.com/leanprover-community/mathlib/commit/5b9914b544c86935926813e0ca6b760060e9d306)
style(group_theory/quotient_group): code style

### [2018-08-10T07:05:33-04:00](https://github.com/leanprover-community/mathlib/commit/d279ddb99fb70a3525f700a9c3bc27df767482a6)
feat(group_theory): adding basic theory of quotient groups

### [2018-08-10T07:04:00-04:00](https://github.com/leanprover-community/mathlib/commit/0f42b279865753eb3c79f3504783c7dbd81dfc7e)
feat(group_theory/submonoid,subgroup): merge with add_* versions

### [2018-08-10T07:04:00-04:00](https://github.com/leanprover-community/mathlib/commit/1d5dd0d43f445ea1699992d404052425af5e9f81)
feat(group_theory): adding add_subgroup and add_submonoid

### [2018-08-10T05:37:13-04:00](https://github.com/leanprover-community/mathlib/commit/e1d92c27f23a66ba388182898ae2a484b394292b)
fix(tactic/replacer): fix tests

### [2018-08-09T12:09:07-04:00](https://github.com/leanprover-community/mathlib/commit/bf3dde12dc73814b00f9a66891641c4bca4b9d41)
refactor(set_theory/cardinal): remove noncomputable theory

### [2018-08-09T12:09:07-04:00](https://github.com/leanprover-community/mathlib/commit/a995a3ad42d6a6e94a022005d4f4182c13dfb208)
perf(tactic/replacer): use if instead of match

### [2018-08-09T12:06:27-04:00](https://github.com/leanprover-community/mathlib/commit/55c2cfd15c7d1dbf7d6dc432d71252edf0facb7f)
fix(docs/theories/integers): typo pointed out by Bryan Gin-ge Chen ([#244](https://github.com/leanprover-community/mathlib/pull/#244))

### [2018-08-09T02:41:57-04:00](https://github.com/leanprover-community/mathlib/commit/a52c2400402658fe10e999db35afe43cddad89ab)
doc(replacer): documentation and test ([#243](https://github.com/leanprover-community/mathlib/pull/#243))

### [2018-08-08T14:39:58-04:00](https://github.com/leanprover-community/mathlib/commit/a91781031732c50df8fc76e5f249102718b20ee5)
refactor(tactic/interactive): merge rcases_hint -> rcases?

### [2018-08-08T10:51:30-04:00](https://github.com/leanprover-community/mathlib/commit/8a19a9846b8d5266838de8c913da48e4d516520e)
feat(tactic/replacer): replaceable tactics

### [2018-08-08T06:57:37-04:00](https://github.com/leanprover-community/mathlib/commit/732ec0efaca37955bf08d656f1b47a065d45bf7f)
feat(tactic/rcases): rcases_hint, rintro_hint

### [2018-08-08T00:44:37-04:00](https://github.com/leanprover-community/mathlib/commit/fe7cd33c7b01d489c95deb94900786c0b91e66cf)
refactor(category_theory/products): tweak PR after merge

### [2018-08-08T00:32:10-04:00](https://github.com/leanprover-community/mathlib/commit/02cf7a614969ec67d83083457643b345cea576bf)
feat(category_theory): product categories and functor categories ([#239](https://github.com/leanprover-community/mathlib/pull/#239))

### [2018-08-08T00:29:39-04:00](https://github.com/leanprover-community/mathlib/commit/47a6a6fbd90057ec3b08ef35b44280b7b078e386)
fix(tactic/interactive): try_for should fail if the tactic fails

### [2018-08-08T00:29:39-04:00](https://github.com/leanprover-community/mathlib/commit/417f29aeac5065cbd6259ff60a2e5d64b3f66c35)
fix(linear_algebra/multivariate_polynomial): remove some @[simp]

### [2018-08-07T20:28:50-04:00](https://github.com/leanprover-community/mathlib/commit/bd7f1b06e7410247dfc730bf19fe84b99bc0e16d)
feat(data/fintype): injective_iff_surjective ([#240](https://github.com/leanprover-community/mathlib/pull/#240))

### [2018-08-07T06:43:17-04:00](https://github.com/leanprover-community/mathlib/commit/9b1be732e122d371100b0df479ca000c2a3f73b0)
feat(category_theory): basic definitions ([#152](https://github.com/leanprover-community/mathlib/pull/#152))

* feat(category_theory): basic definitions

* fixing formatting in documentation

* corrections from review

* removing second ematch attribute on associativity_lemma

* being slightly more careful about variables

(I don't think there were any actual errors,
but I was sometimes using an argument
when there was a variable of the same
name available.)

* fix(notation): transformation components

Using `@>` per @rwbarton's suggestion.

* fix(notation): more conventional notation for composition

* adjusting namespaces, capitalisation, and headers

* move functor/default.lean to functor.lean

(Later PRs will add more files to the functor/ directory, but that can wait.)

* oops

* fixing indentation

* namespace for instances

* removing unnecessary `@>` notation for natural transformations

* renaming, namespacing, and removing a spurious attribute

* better naming, namespaces, and coercions

* updating documentation

* renaming id

* reordering definitions

* rfl lemmas for has_one

* formatting

* formatting

* renaming: snake_case

* renaming coe rfl lemmas

* functoriality -> map_comp

* rfl lemmas for identity C and identity F (reducing both to `1`)

* renaming ext lemma to `ext`

* rename `natural_transformation` to `nat_trans`

* rename `make_lemma` to `restate_axiom`

* renaming nat_trans.components to nat_trans.app

* oops, fix import

* adding doc_comments, and `protected`

* formatting

* removing `has_one` instances, per zulip chat, and adding a `vcomp.assoc` lemma

* removing the attribute that `restate_axiom` used to add

(it was causing a problem on travis, but not locally? anyway it's useless)

* fixing names

### [2018-08-07T05:51:20-04:00](https://github.com/leanprover-community/mathlib/commit/235129a87ccec75fd1ce265f09f46ee10d17100c)
feat(linear_algebra/multivariate_polynomial): Add `_sub` and `_neg` lemmas, and make them simp. ([#238](https://github.com/leanprover-community/mathlib/pull/#238))

### [2018-08-06T20:05:15-04:00](https://github.com/leanprover-community/mathlib/commit/8dc0393ca40efe9c74e6737724c3aa7688683081)
feat(data/multiset): adding two lemmas about singletons ([#234](https://github.com/leanprover-community/mathlib/pull/#234))

### [2018-08-06T11:05:42-04:00](https://github.com/leanprover-community/mathlib/commit/18bd6148832f6b4841978872a114534f2a2c6e6f)
feat(algebra/group_power): adding various cast power lemmas for nat and int ([#230](https://github.com/leanprover-community/mathlib/pull/#230))

### [2018-08-06T06:43:02-04:00](https://github.com/leanprover-community/mathlib/commit/cf0bf2afba4e39ac568e67f504890f020e29174b)
fix(data/seq/wseq): fix build

### [2018-08-06T05:08:26-04:00](https://github.com/leanprover-community/mathlib/commit/8d13bb9d1d3dd8ab5a8e9f2d59e5697f2fcbff93)
feat(list/basic,multiset): list.revzip, multiset.diagonal

### [2018-08-05T22:52:53-04:00](https://github.com/leanprover-community/mathlib/commit/e4b652f60bb902f30400d74352902f270c57cd27)
refactor(data/real/basic): rename for consistency

### [2018-08-05T22:50:26-04:00](https://github.com/leanprover-community/mathlib/commit/e7f110312ea45a035419bce270cae6ecb68c1790)
fix(topology/topological_structures): remove decidability assumption

### [2018-08-05T22:48:47-04:00](https://github.com/leanprover-community/mathlib/commit/599df281cfa0ba6f7697c179bb0683f59170b261)
feat(linear_algebra/mv_polynomial): composition lemmas

### [2018-08-04T19:53:15-04:00](https://github.com/leanprover-community/mathlib/commit/2d0eb8cca8d485e849db871bb5076909d1b6dea3)
feat(linear_algebra/mv_polynomial): map function, map2

### [2018-08-04T18:47:15-04:00](https://github.com/leanprover-community/mathlib/commit/1b93719739909042c98628187a5f81b38acd4221)
feat(algebra/ring): units.neg and associated matter

### [2018-08-04T18:43:51-04:00](https://github.com/leanprover-community/mathlib/commit/e40bee56897e171b3b92e404e10c83daa70217fe)
feat(algebra/ring): semiring homs

### [2018-08-04T18:40:37-04:00](https://github.com/leanprover-community/mathlib/commit/7ec5e87fc6cbe493089c17bf94d26dab2cf9153b)
feat(set_theory/lists): finite ZFA

### [2018-08-03T05:53:29-04:00](https://github.com/leanprover-community/mathlib/commit/873178981173bccc5bf967646fc8908ecfeabfa7)
feat(data/vector2): vector.ext ([#232](https://github.com/leanprover-community/mathlib/pull/#232))

### [2018-07-30T20:35:12+02:00](https://github.com/leanprover-community/mathlib/commit/cecbf2b9c6bccc34d0f72d843938e611bd784068)
doc(tactics/pi_instance): add description in `tactics.md` ([#229](https://github.com/leanprover-community/mathlib/pull/#229))

### [2018-07-30T12:01:49+02:00](https://github.com/leanprover-community/mathlib/commit/fed6c5878a878191341d4ad0c134c45e17954319)
feat(algebra/euclidean_domain): change definition of ED and instance for polynomials ([#211](https://github.com/leanprover-community/mathlib/pull/#211))

### [2018-07-30T11:48:54+02:00](https://github.com/leanprover-community/mathlib/commit/08e0e1d3e9a0bb71540eba1a8897e174a9628aad)
feat(category/traversable): instances for various collections ([#217](https://github.com/leanprover-community/mathlib/pull/#217))

### [2018-07-30T11:27:47+02:00](https://github.com/leanprover-community/mathlib/commit/7dc1f5d2dbda9dd412bb58636f4261bb259ad106)
feat(algebra/pi_instances): more automation ([#222](https://github.com/leanprover-community/mathlib/pull/#222))

### [2018-07-30T11:06:42+02:00](https://github.com/leanprover-community/mathlib/commit/fc88dd41c036666a4b5caf462444a1ce3fb9724f)
fix(tactic/split_ifs): do not process the same condition twice ([#224](https://github.com/leanprover-community/mathlib/pull/#224))

### [2018-07-30T11:01:09+02:00](https://github.com/leanprover-community/mathlib/commit/22d811d18d9b56e02338750deacb953253a9a2ab)
chore(doc/style): mention how to handle ';'

### [2018-07-30T10:56:07+02:00](https://github.com/leanprover-community/mathlib/commit/0371f6e9fd36372440617b073707369ce357cde8)
feat(data/equiv/basic): basic equiv lemmas and decidable_eq ([#225](https://github.com/leanprover-community/mathlib/pull/#225))

### [2018-07-30T10:41:45+02:00](https://github.com/leanprover-community/mathlib/commit/e67f2adfd22efafc7e0bfe9190583a3716bde495)
chore(analysis/topology/uniform_space): remove redundant prod_uniformity (redundant to uniformity_prod)

### [2018-07-30T10:25:10+02:00](https://github.com/leanprover-community/mathlib/commit/8d4f582c64511e0cf4b380f22c9ef7ae060a1f75)
chore(data/list): add prod.erase; cleanup

### [2018-07-27T23:51:05-04:00](https://github.com/leanprover-community/mathlib/commit/460df5effff8e9b882fb3b67bf4780d9db18dd4b)
feat(tactic/norm_num): add support for primality proving

### [2018-07-27T13:21:15-04:00](https://github.com/leanprover-community/mathlib/commit/4d8ce7e01c113bccbb455830373c1f8c34b1b1cf)
feat(data/fin): linear order and eta ([#223](https://github.com/leanprover-community/mathlib/pull/#223))

### [2018-07-25T19:05:48+02:00](https://github.com/leanprover-community/mathlib/commit/85bc75aa67526cc93277916a99233a17e6c41188)
fix(data/list/basic): typo in pariwise_iff

### [2018-07-24T16:33:28+02:00](https://github.com/leanprover-community/mathlib/commit/f9cf9d39d310e3804299af1841403232ad25e233)
feat(category/traversable): basic classes for traversable collections

### [2018-07-24T05:15:31-04:00](https://github.com/leanprover-community/mathlib/commit/8270475f3837d9c13aba3798f2b0159476f536ee)
doc(wip): finite map ([#215](https://github.com/leanprover-community/mathlib/pull/#215)) [ci-skip]

### [2018-07-23T20:06:20-04:00](https://github.com/leanprover-community/mathlib/commit/6abb0d4c60013ed8c95ca75e8c02172fdf794bf5)
feat(algebra/pi_instances): more pi instances

### [2018-07-22T15:03:49-04:00](https://github.com/leanprover-community/mathlib/commit/e74ff76ccac882018e9c1fd70772fd7c88ae06f5)
refactor(data/nat/gcd): simplify proof of pow_dvd_pow_iff

### [2018-07-22T14:37:11-04:00](https://github.com/leanprover-community/mathlib/commit/ffb72292b04ffdbd8fc45a6ec1c1448a02db3bb3)
feat(data/nat/gcd): dvd_of_pow_dvd_pow

### [2018-07-21T14:23:10-04:00](https://github.com/leanprover-community/mathlib/commit/e429aacecf0a003eb1d36e08b5950ac2b269e2c7)
fix(computability/turing_machine): missed a spot

### [2018-07-21T14:02:13-04:00](https://github.com/leanprover-community/mathlib/commit/8bf72b2fbce8d2fc9d9656cd36201fbd9872da6c)
chore(tactic/interactive): change swap so it does what it says

it is supposed to move the nth goal to the front, not rotate all the goals

### [2018-07-21T13:58:02-04:00](https://github.com/leanprover-community/mathlib/commit/682025f031c9ca6be8c14f3f7cfb54572397301a)
fix(*): fix build, use rw consistently

### [2018-07-21T12:10:36-04:00](https://github.com/leanprover-community/mathlib/commit/e7321bbd18c40d3e644064cb94da143284e7f3cb)
fix(data/option): fix universe levels in option.map_some etc.

### [2018-07-21T02:09:53-04:00](https://github.com/leanprover-community/mathlib/commit/fb952fe46b621f93f402eebd43e67830f0be2526)
refactor(analysis/ennreal): split and move to data.real

### [2018-07-20T01:17:21-04:00](https://github.com/leanprover-community/mathlib/commit/23a5591fca0d43ee5d49d89f6f0ee07a24a6ca29)
feat(tactic/h_generalize): remove `cast` expressions from goal ([#198](https://github.com/leanprover-community/mathlib/pull/#198))

### [2018-07-19T15:34:44-04:00](https://github.com/leanprover-community/mathlib/commit/29639b31a9808f601fa434aeed0f5756f040f0e8)
feat(analysis/measure_theory): optimize proofs; trim, is_complete

### [2018-07-19T10:10:59-04:00](https://github.com/leanprover-community/mathlib/commit/bd90a935000e33d84e90ae995a76a51b97508260)
fix(group_theory/group_action): move is_group_action out of namespace

### [2018-07-19T09:29:24-04:00](https://github.com/leanprover-community/mathlib/commit/2b9780ada05046fc663c1f8dce31fcc252db149d)
feat(data/finset): disjoint_val ([#206](https://github.com/leanprover-community/mathlib/pull/#206))

### [2018-07-19T09:29:24-04:00](https://github.com/leanprover-community/mathlib/commit/1e0c38b01bb3d6de9397658bd3a7fd1690750cc1)
feat(data/multiset): sup and inf for multisets

### [2018-07-19T06:54:38-04:00](https://github.com/leanprover-community/mathlib/commit/50f18e68048e1ccfae63c695e8b9edd26d171316)
feat(group_theory/group_action): group actions and orbit stabilizer ([#204](https://github.com/leanprover-community/mathlib/pull/#204))

### [2018-07-19T03:56:30-04:00](https://github.com/leanprover-community/mathlib/commit/9f7930918c22f18aba81405fae9ecaf7bf99f76a)
fix(data/multiset): fix build, cleanup mem_pi

### [2018-07-19T03:18:09-04:00](https://github.com/leanprover-community/mathlib/commit/37f3e3230102c1e1ca510499072056bede7538d4)
fix(algebra/big_operators): fix build

### [2018-07-19T02:36:49-04:00](https://github.com/leanprover-community/mathlib/commit/aedbc12eaf71fb3505b07802bc4417284439fc65)
feat(data/fintype): card lemmas ([#168](https://github.com/leanprover-community/mathlib/pull/#168))

### [2018-07-19T00:25:14-04:00](https://github.com/leanprover-community/mathlib/commit/c2f54ad03652faccd688b9c2db699a923c2f665d)
fix(tactic/refine_struct): fix support for source structures

### [2018-07-18T14:10:50+02:00](https://github.com/leanprover-community/mathlib/commit/9a302352552874c96e986cc07e1440a2f2663b70)
chore(data/polynomial): move auxiliary definitions/theorems to appropriate places

### [2018-07-18T14:10:50+02:00](https://github.com/leanprover-community/mathlib/commit/d9daeff0f5b838ac55af039ac0115c1016855ff9)
refactor(data/polynomial): move polynomials to data; replace monomial by `C a * X^n`

### [2018-07-18T14:10:50+02:00](https://github.com/leanprover-community/mathlib/commit/ce990c59db140b1cda8076cfd6780715e23d66b1)
feat(linear_algebra/univariate_polynomial): univariate polynomials

### [2018-07-17T22:43:01-04:00](https://github.com/leanprover-community/mathlib/commit/a0dd286aea964d2319eb201a109aa7c9922a7978)
fix(*): fix build

### [2018-07-17T18:00:59-04:00](https://github.com/leanprover-community/mathlib/commit/7f8b0880feda5059023d147404449c9e8712a5c0)
feat(tactic/basic): fix environment.in_current_file

### [2018-07-17T17:16:55-04:00](https://github.com/leanprover-community/mathlib/commit/980a01e805471f7f1a6167832564b8b3dc94c5a7)
feat(ring_theory/ideals): quotient rings ([#196](https://github.com/leanprover-community/mathlib/pull/#196))

### [2018-07-17T01:32:25-04:00](https://github.com/leanprover-community/mathlib/commit/421a1cda8fdd42cb19860ea878e34c659950325d)
fix(measure_theory/measure_space): fix build

### [2018-07-17T00:35:02-04:00](https://github.com/leanprover-community/mathlib/commit/f92d23947c6dc0438677d53421fde7cdc170c5d3)
chore(travis.yml): checkout old files in both stages

### [2018-07-17T00:30:54-04:00](https://github.com/leanprover-community/mathlib/commit/b267edc364cc54e29fcfcac25d63b139ba7a3e12)
refactor(data/set/countable): define countable in terms of encodable

### [2018-07-16T23:17:06-04:00](https://github.com/leanprover-community/mathlib/commit/ee4ff473d062dd7f9706e51ba63198794f7184b1)
chore(travis.yml): update lean files before pre-build

### [2018-07-16T22:13:58-04:00](https://github.com/leanprover-community/mathlib/commit/95a3c47e1251230b5cfde25d4cac3c2f903dbc1f)
fix(.): fix build

### [2018-07-16T20:46:11-04:00](https://github.com/leanprover-community/mathlib/commit/bdc90f6cef3040751df213455c02a0b520b56c50)
feat(data/set/basic): more set theorems, normalize naming

### [2018-07-16T20:17:22-04:00](https://github.com/leanprover-community/mathlib/commit/9f6bcd092261cca51ab5bf26a03b99992ce0d028)
refactor(data/bool): decidable forall bool

### [2018-07-16T20:16:24-04:00](https://github.com/leanprover-community/mathlib/commit/8685bf2d3bbdaac71f35a60cd88c7d033c1026eb)
refactor(topology/continuity): remove inhabited from dense extend

### [2018-07-16T20:03:13-04:00](https://github.com/leanprover-community/mathlib/commit/57f07e0785f5710b43e9ad8a46fdb3e3caacf54e)
refactor(data/set/basic): rename set.set_eq_def -> set.ext_iff

### [2018-07-16T19:52:54-04:00](https://github.com/leanprover-community/mathlib/commit/4c6d7e29a1dbd517c5b214d75955d0f132d73c77)
feat(tactic/interactive): add apply_rules tactic ([#190](https://github.com/leanprover-community/mathlib/pull/#190))

### [2018-07-16T19:44:31-04:00](https://github.com/leanprover-community/mathlib/commit/6495c2056eed57b4310a2136f1ae04234625e7bc)
feat(algebra/order_functions): abs_eq

### [2018-07-16T19:42:41-04:00](https://github.com/leanprover-community/mathlib/commit/b0de694cab7af0503afb32ed4678269a91afcbbf)
feat(tactic/tauto): improve coverage and performances of tauto ([#180](https://github.com/leanprover-community/mathlib/pull/#180))

### [2018-07-16T19:40:28-04:00](https://github.com/leanprover-community/mathlib/commit/c3e24f34ec9d65b2dcd8a193408b1632c2a00cdc)
docs(code-review): add check list ([#195](https://github.com/leanprover-community/mathlib/pull/#195)) [ci-skip]

### [2018-07-16T19:39:17-04:00](https://github.com/leanprover-community/mathlib/commit/3a79975e46a1c007acd3bf9a5f1e77b16e2a834e)
feat(data/quot): quot.hrec_on₂, quotient.hrec_on₂ ([#197](https://github.com/leanprover-community/mathlib/pull/#197))

### [2018-07-16T19:34:21-04:00](https://github.com/leanprover-community/mathlib/commit/dd6cc576fa5a55fdc4c6042c046da50db514e56f)
chore(build): make travis build fail quicker when errors are found

### [2018-07-16T19:33:09-04:00](https://github.com/leanprover-community/mathlib/commit/631207be61c6c72dc4c90a2348f6759779756d23)
feat(data/multiset,...): card_eq_one

based on [#200](https://github.com/leanprover-community/mathlib/pull/#200)

### [2018-07-16T19:25:02-04:00](https://github.com/leanprover-community/mathlib/commit/ab8813a8dce3b030d58fe8fc5a3cb2cfcb18aadb)
feat(tactic/interactive): alias "rintros" for "rintro"

### [2018-07-16T15:11:29+01:00](https://github.com/leanprover-community/mathlib/commit/df8fc18fa66ddaa9060b1c5b876af5365c1c0f38)
feat(data/list/perm): extract cons_subperm_of_mem from subperm_of_subset_nodup ([#173](https://github.com/leanprover-community/mathlib/pull/#173))

### [2018-07-16T14:06:55+02:00](https://github.com/leanprover-community/mathlib/commit/20fca1ced72cce7896d0a53911c5a87c40ae736f)
feat(data/finset): disjoint finsets

### [2018-07-16T12:59:35+01:00](https://github.com/leanprover-community/mathlib/commit/844c665b6e54685fe16a251e2f5972c37a8b36f3)
feat(category/applicative): `id` and `comp` functors; proofs by `norm` ([#184](https://github.com/leanprover-community/mathlib/pull/#184))

### [2018-07-12T18:02:46-04:00](https://github.com/leanprover-community/mathlib/commit/8dda9cdcbeff26af4bf2530a4f0cbb99721544ae)
fix(analysis/topology/continuity): remove an extraneous constraint

### [2018-07-12T18:00:11-04:00](https://github.com/leanprover-community/mathlib/commit/42ba0983a2165d536353701d0dcba458b79c330d)
feat(data/set/basic): diff_subset_iff, diff_subset_comm

### [2018-07-12T17:59:05-04:00](https://github.com/leanprover-community/mathlib/commit/17bf1ae20bafb1f93b3ccdbdb5ca09755177f606)
feat(analysis/topology/continuity): embedding_inl, embedding_inr

### [2018-07-12T08:42:03-04:00](https://github.com/leanprover-community/mathlib/commit/21b918b3083ce42c495ab48b7ea19e486e3eae6b)
feat(data/fintype): decidable forall and exists ([#189](https://github.com/leanprover-community/mathlib/pull/#189))

### [2018-07-11T21:00:56-04:00](https://github.com/leanprover-community/mathlib/commit/b1a314fc495ed540722458469568e1641dc0b5c4)
chore(build): Break build process into two parts

### [2018-07-11T01:33:37-04:00](https://github.com/leanprover-community/mathlib/commit/8d72f62c8a89175404c5e93d81e6c49a17233739)
Revert "chore(build): Break build process into two parts"

This reverts commit 890847df6618c5559a4170c36d61bf693f57086d.

### [2018-07-11T00:08:43-04:00](https://github.com/leanprover-community/mathlib/commit/890847df6618c5559a4170c36d61bf693f57086d)
chore(build): Break build process into two parts

### [2018-07-08T15:26:47-04:00](https://github.com/leanprover-community/mathlib/commit/c8ad5cfd793153bff38c49c54940f04d86cb7616)
fix(computability/turing_machine): fix import

### [2018-07-08T14:39:57-04:00](https://github.com/leanprover-community/mathlib/commit/e5d5abd9fe844b1c40267b937b8e0fbabd663d39)
feat(data/pfun,...): add some isomorphism theorems

### [2018-07-07T02:03:44-04:00](https://github.com/leanprover-community/mathlib/commit/71953e0bbc3c4004635517123af8b2a05f85ad22)
feat(order/basic): add extensionality for order structures

### [2018-07-06T09:04:17-04:00](https://github.com/leanprover-community/mathlib/commit/ab1861ab37d593e9e6c8ea220534b53dff65472e)
feat(data/subtype): setoid (subtype p)

### [2018-07-06T09:04:17-04:00](https://github.com/leanprover-community/mathlib/commit/d54950a813ad4bb0ac547831c499b98265bfaa8d)
refactor(data/subtype): move out of data/sigma/basic.lean

### [2018-07-06T03:46:34-04:00](https://github.com/leanprover-community/mathlib/commit/d194f38983b800a010697d2d73f25a5a3ad08c64)
refactor(tactic/rcases): use haveI in tactic.cache

### [2018-07-06T03:44:23-04:00](https://github.com/leanprover-community/mathlib/commit/28e011d41f95b22f7f7d9b8509a7e9aa9a890174)
feat(tactic/cache): split cache related tactics off from `tactic.interactive`

### [2018-07-06T03:44:23-04:00](https://github.com/leanprover-community/mathlib/commit/06f477831ef90f513c75672faafd1fec82e01506)
feat(tactic/tauto): handle `or` in goal

### [2018-07-06T02:31:12-04:00](https://github.com/leanprover-community/mathlib/commit/b4a85486504fbb4b5be707b761e847c694e5914a)
feat(tactic/rcases): add rintro tactic

### [2018-07-04T13:08:30-04:00](https://github.com/leanprover-community/mathlib/commit/a7846022507b531a8ab53b8af8a91953fceafd3a)
feat(tactic/tauto): consider `true` and `false`

### [2018-07-02T18:50:42-04:00](https://github.com/leanprover-community/mathlib/commit/a2e847d2bce258406f14ce7970e1cdbffc8a26e7)
fix(algebra/ordered_group): define (0:with_bot) to unfold correctly

### [2018-07-02T07:22:16-04:00](https://github.com/leanprover-community/mathlib/commit/ff4eeed77f05c1b561ec8e9c34777c00b394b52f)
feat(computability/turing_machine): reduce to 2-symbol TMs

### [2018-07-02T13:11:51+02:00](https://github.com/leanprover-community/mathlib/commit/b5e07ad7433e00e3ec224977f6e2934bea01af84)
fix(analysis/topology): prod.ext is now prod.ext_iff

### [2018-07-02T11:47:11+02:00](https://github.com/leanprover-community/mathlib/commit/3f66b3a2534268f93b8614ef85edad6723eab46a)
feat(analysis/topology/continuity): generalized tube lemma and some corollaries

### [2018-07-02T11:47:11+02:00](https://github.com/leanprover-community/mathlib/commit/225dd84e1935ee86ef65b5d14c49eca39116b789)
feat(data/set/lattice): add more lemmas pertaining to bInter, bUnion

### [2018-06-30T23:04:40-04:00](https://github.com/leanprover-community/mathlib/commit/7b0c1508ceefcf57360db755452314fc9311ad54)
refactor(data/equiv): reorganize data.equiv deps

### [2018-06-30T00:43:36-04:00](https://github.com/leanprover-community/mathlib/commit/913f702a5712d30324a41631d40330a351caf6a3)
feat(computability/turing_machine): rework proofs, simplify TM lang

### [2018-06-30T00:36:55-04:00](https://github.com/leanprover-community/mathlib/commit/cfb5dfda177fa6e98e924a9e162e54f602fde0f3)
refactor(data/finset): use partial_order to define lattice structure

### [2018-06-30T00:36:27-04:00](https://github.com/leanprover-community/mathlib/commit/ddbb81389b6d6cd3d0395f474896dcd59e1ed9e4)
feat(data/fintype): finite choices, computably

### [2018-06-25T20:05:43-04:00](https://github.com/leanprover-community/mathlib/commit/a7b749f0a743ab467e1cb7d688e4a8a0f7a82874)
fix(order/boolean_algebra): neg_unique: replace rsimp proof, speed up build

### [2018-06-25T05:45:48-04:00](https://github.com/leanprover-community/mathlib/commit/97a1d1b722587705f65b446b648e160e2cc8bf5b)
feat(data/fintype): more fintype instances ([#145](https://github.com/leanprover-community/mathlib/pull/#145))

### [2018-06-25T05:43:26-04:00](https://github.com/leanprover-community/mathlib/commit/90aeb8e80415ad38112b25d4e8044b6da4881f0c)
feat(tactic/solve_by_elim): writing a symm_apply tactic for solve_by_elim ([#164](https://github.com/leanprover-community/mathlib/pull/#164))

writing a symm_apply tactic, and have solve_by_elim use it, per discussion with @SimonHudon

### [2018-06-25T05:42:30-04:00](https://github.com/leanprover-community/mathlib/commit/a39c5ca6c7d5b7b4a0f2bac02d96f95a6bc60b3f)
correcting comment

### [2018-06-25T05:41:01-04:00](https://github.com/leanprover-community/mathlib/commit/0a13c0500a62d4322e44debff5d20f618c26056f)
feat(list/basic): map_subset

from [#166](https://github.com/leanprover-community/mathlib/pull/#166)

### [2018-06-25T05:35:22-04:00](https://github.com/leanprover-community/mathlib/commit/4ec65f53d0bdeb754b0e128a678cb897f6cfa9ae)
fix(data/list/basic): simplify last_append, speed up build

### [2018-06-25T05:29:11-04:00](https://github.com/leanprover-community/mathlib/commit/516b254d287f8bcfcd07d29ae7d7a37ca11f15ba)
feat(tactic/ring2): alternative ring tactic

### [2018-06-21T08:06:52-04:00](https://github.com/leanprover-community/mathlib/commit/4082136efa01e53e4e67e71e6623fcfba71498f7)
feat(tactic/refine_struct): match `{ .. }` in subexpressions ([#162](https://github.com/leanprover-community/mathlib/pull/#162))

### [2018-06-21T08:05:27-04:00](https://github.com/leanprover-community/mathlib/commit/aa55cbaf361ec9c5285d66070d795bc5e10f0118)
fix(order/lattice): typo

### [2018-06-20T22:42:18-04:00](https://github.com/leanprover-community/mathlib/commit/905345a2ceaa5d0c7bc2f6310026961416b2cae4)
fix(data/array/lemmas,...): fix build

### [2018-06-20T21:42:57-04:00](https://github.com/leanprover-community/mathlib/commit/a30b7c773db17cf7d1b551ba0f24645079296628)
feat(data/string): fix string_lt, add repr for multiset, pnat

### [2018-06-19T14:32:22-04:00](https://github.com/leanprover-community/mathlib/commit/fbe1047bac98323c37673a3f861550ea297937c1)
feat(tactic/refine_struct): add `refine_struct` to use goal tags ([#147](https://github.com/leanprover-community/mathlib/pull/#147))

### [2018-06-19T09:53:45-04:00](https://github.com/leanprover-community/mathlib/commit/2216460cbbfe84986fc9077b5afab26fb81484da)
Merge branch 'master' of github.com:leanprover/mathlib

### [2018-06-19T08:25:55-04:00](https://github.com/leanprover-community/mathlib/commit/f22285c5760f9cc5f78c120456afad3b6079ec4c)
feat(algebra/pi_instances): add apply lemmas ([#149](https://github.com/leanprover-community/mathlib/pull/#149))

### [2018-06-19T08:19:49-04:00](https://github.com/leanprover-community/mathlib/commit/0a0e8a53f2a97827c0879507740e07a020a4f03a)
feat(tactic/ext): `ext` now applies to `prod`; fix `ext` on function types ([#158](https://github.com/leanprover-community/mathlib/pull/#158))

### [2018-06-19T08:17:52-04:00](https://github.com/leanprover-community/mathlib/commit/0087c2ce0aa5e0172ff82a1bb0aea007ffa986d1)
feat(analysis/topology): quotient spaces and quotient maps ([#155](https://github.com/leanprover-community/mathlib/pull/#155))

* style(analysis/topology): simplify induced_mono and induced_sup

* style(analysis/topology/topological_space): reorganize section constructions

* feat(analysis/topology/topological_space): add more galois connection lemmas

* feat(analysis/topology): quotient spaces and quotient maps

### [2018-06-19T08:13:31-04:00](https://github.com/leanprover-community/mathlib/commit/5e0b13781e4e392ad39191778e6c7edc2f4457dd)
feat (group_theory/coset): quotient by normal subgroup is a group

### [2018-06-19T08:12:39-04:00](https://github.com/leanprover-community/mathlib/commit/8609a3d36cba9bc88fda6bb7a49b85a84eb9e3fb)
feat(split_ifs): fail if no progress ([#153](https://github.com/leanprover-community/mathlib/pull/#153))

### [2018-06-19T08:11:25-04:00](https://github.com/leanprover-community/mathlib/commit/f8e396564c8acd72a30617b528ea969a01718bc5)
blah

### [2018-06-19T08:09:27-04:00](https://github.com/leanprover-community/mathlib/commit/4e2aea5b50f8ac436d8fe59aa7cbcd36fb69ef1d)
feat(data/option): is_some and is_none simp theorems

### [2018-06-19T08:08:36-04:00](https://github.com/leanprover-community/mathlib/commit/e1f795d0d929fa6b5458a04bd6bb5889e503b0bf)
chore(data/list/basic): minor cleanup of find variables ([#137](https://github.com/leanprover-community/mathlib/pull/#137))

### [2018-06-17T10:20:07-04:00](https://github.com/leanprover-community/mathlib/commit/896455c33eb95b538c252bf3d4d863833759d18e)
feat(category): add functor_norm simp_attr, and class is_comm_applicative

### [2018-06-16T17:39:03-04:00](https://github.com/leanprover-community/mathlib/commit/85bc56ad5f98801cd4aedef4cbcdb2dd0c630ff3)
feat(computability/turing_machine): finish stack machine proof

### [2018-06-15T05:11:08+07:00](https://github.com/leanprover-community/mathlib/commit/fba4d8921e6f482962c907628d62dc78b230c749)
fix(analysis/topology/continuity): remove unused code

### [2018-06-13T01:28:56+07:00](https://github.com/leanprover-community/mathlib/commit/fe590ca272a41bb321a13be505964e78cad1e731)
fix(data/num/lemmas): fix formatting

### [2018-06-13T00:32:23+07:00](https://github.com/leanprover-community/mathlib/commit/4f32a4bc884af5b5c01867f4a00cdcb6b92bd818)
feat(data/num/basic): to_nat' function for efficient nat -> num in VM

### [2018-06-12T22:37:08+07:00](https://github.com/leanprover-community/mathlib/commit/99101eacaf3791135df942b350cfc0e34249a1c0)
feat(data/num/basic): add div,mod,gcd for num,znum

### [2018-06-12T22:37:08+07:00](https://github.com/leanprover-community/mathlib/commit/3c554a34e72aeb87bc29b554268c69ec9f5888b9)
refactor(data/equiv): move subtype.map

### [2018-06-12T22:37:08+07:00](https://github.com/leanprover-community/mathlib/commit/0865bce5557284959c0e5407ff350aa3e6ea56e6)
fix(tactic/ring): fix normalization bugs

fixes [#84](https://github.com/leanprover-community/mathlib/pull/#84)

### [2018-06-11T14:05:37+07:00](https://github.com/leanprover-community/mathlib/commit/90fc9125bcf502645b60f0070ee5e36551dd7116)
feat(data/list): add parametricity for perm

### [2018-06-11T14:05:37+07:00](https://github.com/leanprover-community/mathlib/commit/9546e62558f2294b0d8118a4cd2649a77328f314)
feat(data/list): add parametricity rules for list operations

### [2018-06-11T14:05:09+07:00](https://github.com/leanprover-community/mathlib/commit/1416ebbb7e0520a05d60b4217842dbf46664e35d)
feat(data/option): add relator option.rel

### [2018-06-11T14:04:44+07:00](https://github.com/leanprover-community/mathlib/commit/205e3b4ec0f5755b9ec7ef497ce662249b160e70)
feat(logic/relation): add relation composition, map, and bi_unique

### [2018-06-02T10:36:21-04:00](https://github.com/leanprover-community/mathlib/commit/344192a9696e7089b520f28e7ed8c78aa32e48dc)
refactor(computability): move out of data directory

### [2018-06-02T10:36:16-04:00](https://github.com/leanprover-community/mathlib/commit/56035953b1aa9ba60d6a6c67954a21fc316ed4d3)
feat(computability/turing_machine): proving the TM reductions

### [2018-06-01T22:49:29-04:00](https://github.com/leanprover-community/mathlib/commit/dd1c55861b207655a684d33775def0ebcbbe293d)
feat(algebra/ordered_group): with_bot as an ordered monoid

### [2018-06-01T22:48:49-04:00](https://github.com/leanprover-community/mathlib/commit/372bdab5d8577f161d770edff19fe97b911b5741)
feat(algebra/archimedean): some more floor thms

### [2018-05-31T03:00:24-04:00](https://github.com/leanprover-community/mathlib/commit/b37526407ed1846f29dcdfb976554daf7f8a983e)
feat(computability/turing_machine): add TMs and reductions

### [2018-05-30T15:29:43-04:00](https://github.com/leanprover-community/mathlib/commit/bdd54acda358f535b42951b784757135213dcf52)
feat(data/computablility): reduced partrec

### [2018-05-29T18:57:49-04:00](https://github.com/leanprover-community/mathlib/commit/00a2eb4119d27761c8a6ee38eb1eae532cd3ac19)
feat(algebra/group_power): mul_two_nonneg

### [2018-05-29T17:20:24-04:00](https://github.com/leanprover-community/mathlib/commit/40bd9478f150d3042823ceea78a576ab5ba49427)
feat(computability/primrec): add traditional primrec definition

This shows that the pairing function with its square roots does not give any additional power.

### [2018-05-29T17:20:24-04:00](https://github.com/leanprover-community/mathlib/commit/5fea16e6f97be5987907335f527b5791be0e287e)
feat(category/basic): $< notation for reversed application

### [2018-05-29T15:48:54+02:00](https://github.com/leanprover-community/mathlib/commit/a2d2537c8afd708bc7c79196c39f098803df4d94)
feat(analysis/probability_mass_function): add bernoulli

### [2018-05-29T15:08:43+02:00](https://github.com/leanprover-community/mathlib/commit/4f9e951fbf403eb66d0814279bf929e37fec4fc0)
feat(analysis): add probability mass functions

### [2018-05-29T04:19:54-04:00](https://github.com/leanprover-community/mathlib/commit/eaa1b931410784b43c0ae3c1770bf8230bb0ab83)
feat(data.list.basic): forall_mem_singleton, forall_mem_append

### [2018-05-29T03:47:46-04:00](https://github.com/leanprover-community/mathlib/commit/a6be52359af1b851ea8a2401492e2841c21f047d)
feat(data/list/basic): map_erase, map_diff, map_union

### [2018-05-28T15:36:19+02:00](https://github.com/leanprover-community/mathlib/commit/00220680481960c1de446cd3e70951bcbf54e5c8)
fix(tactics/wlog): allow union instead of disjunction; assume disjunction in strict associcated order; fix discharger

### [2018-05-28T14:30:41+02:00](https://github.com/leanprover-community/mathlib/commit/1dbd8c6d147c974bef9b8ad355c3e346bc5c1762)
feat(data/equiv): image, preimage under equivalences; simp rules for perm.val  ([#102](https://github.com/leanprover-community/mathlib/pull/#102))

### [2018-05-27T22:50:42-04:00](https://github.com/leanprover-community/mathlib/commit/c53f9f172be9a79443e27913e73af1e7b2fdf145)
refactor(algebra/euclidean_domain): clean up proofs

### [2018-05-27T19:47:56-04:00](https://github.com/leanprover-community/mathlib/commit/9f0d1d8cdd508a4187126d966a055f75b6bd8bde)
fix(analysis/limits): fix ambiguous import (fin)set.range

### [2018-05-27T18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/ad92a9ba47f417916aab365d13db653fa8991a84)
feat(algebra/group,...): add with_zero, with_one structures

other ways to add an element to an algebraic structure:
* Add a top or bottom to an order (with_top, with_bot)
* add a unit to a semigroup (with_zero, with_one)
* add a zero to a multiplicative semigroup (with_zero)
* add an infinite element to an additive semigroup (with_top)

### [2018-05-27T18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/431d997a9dd68fc5b1653f9f51f572851f9e1d50)
feat(nat/basic): mod_mod

### [2018-05-27T18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/4c1a82686f7f80c6c3bf3cf95a54346bdc1b3d6a)
refactor(data/set/finite): use hypotheses for fintype assumptions

in simp rules

### [2018-05-27T18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/f563ac80980f4a72724eab228948b0579dcdc785)
chore(data/pnat): remove nat -> pnat coercion

### [2018-05-27T18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/b7012fb876a6677c08759bfe0cfe028eacb355de)
fix(tactic/norm_num): use norm_num to discharge simp goals

### [2018-05-25T16:15:06+02:00](https://github.com/leanprover-community/mathlib/commit/6811f1399cfff3506d2e8803576d9142659e4f73)
fix(data/list/perm): remove unused code ([#143](https://github.com/leanprover-community/mathlib/pull/#143))

### [2018-05-25T05:57:39-04:00](https://github.com/leanprover-community/mathlib/commit/bcec475a70954b7e5776493c5df96aaa4f982cf3)
chore(leanpkg.toml): update version to 3.4.1

### [2018-05-25T05:55:41-04:00](https://github.com/leanprover-community/mathlib/commit/1991869fcea72822aef0b3509d5c4f63fec48453)
feat(order/bounded_lattice): with_bot, with_top structures

### [2018-05-25T01:14:13-04:00](https://github.com/leanprover-community/mathlib/commit/94dc067735a290ec384d94c16090b74a710fa2b3)
refactor(order/lattice): move top/bot to bounded_lattice

### [2018-05-25T01:14:13-04:00](https://github.com/leanprover-community/mathlib/commit/4117ff40bae2051a947b368bed56fc655e85ea62)
refactor(algebra/order_functions): reorganize new lemmas

### [2018-05-24T15:55:26+02:00](https://github.com/leanprover-community/mathlib/commit/9303bc024fccb60cfcdb4f8f9ba6459b02deec3b)
feat(analysis/ennreal): add further type class instances for nonnegative reals

### [2018-05-24T15:55:26+02:00](https://github.com/leanprover-community/mathlib/commit/02f8f4818cdb40b31ef175faef2ccad4f2e3724e)
feat(analysis/nnreal): define the nonnegative reals

NB: This file has a lot in common with `ennreal.lean`, the extended nonnegative reals.

### [2018-05-24T09:39:41+02:00](https://github.com/leanprover-community/mathlib/commit/2c94668b7d574691b6fc37061312cc4eb6005eab)
fix(data/fin): rename raise_fin -> fin.raise; simp lemmas for fin ([#138](https://github.com/leanprover-community/mathlib/pull/#138))

### [2018-05-23T19:20:55+02:00](https://github.com/leanprover-community/mathlib/commit/d91a267fa07412317f276f41121b95817bb4c363)
fix(data/list/basic): protected list.sigma ([#140](https://github.com/leanprover-community/mathlib/pull/#140))

### [2018-05-23T19:20:25+02:00](https://github.com/leanprover-community/mathlib/commit/94a4b0745009690347af2b2ebcba9c73bde72481)
doc(docs/extras): some notes on well founded recursion ([#127](https://github.com/leanprover-community/mathlib/pull/#127))

### [2018-05-23T19:16:42+02:00](https://github.com/leanprover-community/mathlib/commit/23bd3f2ed6a097bb7aec7a637207436b363c0aaa)
doc(docs/extra/simp): adding reference to simpa ([#106](https://github.com/leanprover-community/mathlib/pull/#106))

### [2018-05-23T18:54:35+02:00](https://github.com/leanprover-community/mathlib/commit/add172ddc03b10734cb34bdcab77861c94235504)
chore(tactic/default): move split_ifs import to tactic.interactive

### [2018-05-23T18:54:35+02:00](https://github.com/leanprover-community/mathlib/commit/d442907620c914f95c210acebac0655a3388bf86)
fix(tactic/split_if): clarify behavior

### [2018-05-23T18:54:35+02:00](https://github.com/leanprover-community/mathlib/commit/509934ffa9eeac4a36bf222fec198b4bc6bce897)
feat(tactic/split_ifs): add if-splitter

### [2018-05-23T17:29:32+02:00](https://github.com/leanprover-community/mathlib/commit/f458eef3e78a91510c62f0c4f9e7d8027113f33d)
feat(analysis/topology): add tendsto and continuity rules for big operators

### [2018-05-23T17:17:56+02:00](https://github.com/leanprover-community/mathlib/commit/a54be050238844220c08bbe2ae8dd2df0b07306c)
feat(analysis/topology): add continuity rules for supr, Sup, and pi spaces

### [2018-05-23T15:22:09+02:00](https://github.com/leanprover-community/mathlib/commit/cff886bb77704cd6cac6473496c6fffb247ad9a6)
feat(data/finset): max and min

### [2018-05-23T15:22:09+02:00](https://github.com/leanprover-community/mathlib/commit/d1ea2726dafcf29baf029a476bd19526490e074c)
feat(data/option): lift_or_get

### [2018-05-22T05:26:41-04:00](https://github.com/leanprover-community/mathlib/commit/d62bf5605ec8971d446a01af40abf9183447cb42)
feat(computability/halting): halting problem

### [2018-05-21T11:44:37-04:00](https://github.com/leanprover-community/mathlib/commit/f0bcba56f90e5a26fcb537988224a43170942ae8)
feat(computability/partrec_code): Kleene normal form theorem

among other things

### [2018-05-21T11:41:40-04:00](https://github.com/leanprover-community/mathlib/commit/fe5c86c0830250a8049f8789baf32d1217b3456d)
fix(tactic/interactive): fix congr bug, rename congr_n to congr'

### [2018-05-20T06:37:12-04:00](https://github.com/leanprover-community/mathlib/commit/741469abee41d7117002b40d30529b5a374c59b4)
fix(tactic/interactive): make rcases handle nested constructors correctly

The line changed by this commit was wrong because `k` might contain
further constructors, which also need to be "inverted".

Fixes [#56](https://github.com/leanprover-community/mathlib/pull/#56).

* doc(tactic): Internal documentation for rcases

* style(tactic/rcases): eliminate an unused recursive parameter

* style(*): use rcases more

### [2018-05-19T21:28:26-04:00](https://github.com/leanprover-community/mathlib/commit/fc20442e90d96e092feda32dc51ad05c4122f3d4)
feat(computability/partrec): partial recursion, Godel numbering

### [2018-05-18T05:14:19-04:00](https://github.com/leanprover-community/mathlib/commit/38d553694351f4c23a8a8216038c7c8abcb7cd32)
feat(computability/partrec): starting work on partial recursive funcs

### [2018-05-18T05:10:04-04:00](https://github.com/leanprover-community/mathlib/commit/92feaf95b750c04c3d1967beb0de00f137f8f29b)
feat(computability/primrec): list definitions are primrec

### [2018-05-17T04:23:08-04:00](https://github.com/leanprover-community/mathlib/commit/e017f0f1e63c9bba9f776c2defbfc5a86149c409)
feat(data/computability): primrec, denumerable

### [2018-05-16T10:16:22+02:00](https://github.com/leanprover-community/mathlib/commit/fe7d5738417aeaf835790af2101b98d1758ad8fe)
refactor(data/set/enumerate): proof enumeration_inj using wlog

### [2018-05-16T10:16:22+02:00](https://github.com/leanprover-community/mathlib/commit/d8c33e84276256aed43fdd530bb9fdf63aeca376)
feat(tactic): generalize wlog to support multiple variables and cases, allow to provide case rule

### [2018-05-10T15:29:47+02:00](https://github.com/leanprover-community/mathlib/commit/2cd640a5953ce6f6b3688f6f0eb2cac709fc583c)
feat(data/multiset): add sections

### [2018-05-10T15:29:29+02:00](https://github.com/leanprover-community/mathlib/commit/62833ca5dd435a5948a905101189882a710120ed)
feat(data/multiset): add relator

### [2018-05-10T12:12:25+02:00](https://github.com/leanprover-community/mathlib/commit/d10c3bb2d52b76bb13b9c9c5769706eaf20b95c1)
fix(order/complete_boolean_algebra): replace finish proof by simp (finish was very slow)

### [2018-05-09T06:19:46-04:00](https://github.com/leanprover-community/mathlib/commit/fc6f57af2fceb52a97dba773425d0d33ebd5ec22)
feat(data/list/basic): list.forall2, list.sections

### [2018-05-09T06:04:38-04:00](https://github.com/leanprover-community/mathlib/commit/42f5ea06618c8e191824f1a746e1b59cbfb70f3f)
feat(data/semiquot): semiquotient types

### [2018-05-09T06:04:38-04:00](https://github.com/leanprover-community/mathlib/commit/b31c30dbe8d00b8089c3f7503e0b04179fa5abab)
refactor(logic/function): constructive proof of cantor_injective

### [2018-05-09T11:41:31+02:00](https://github.com/leanprover-community/mathlib/commit/54df4d9ce041f010b75100a8a5cc2659fb5b8b44)
feat(linear_algebra/multivariate_polynomial): change order of eval arguments; show that eval is ring homomorphism

(closes https://github.com/leanprover/mathlib/pull/134)

### [2018-05-09T10:46:03+02:00](https://github.com/leanprover-community/mathlib/commit/b5eddd80bd451aadab8fba6c594536ab658f320f)
fix(data/set/basic): mark subset.refl as @[refl]

### [2018-05-04T16:10:27+02:00](https://github.com/leanprover-community/mathlib/commit/e4c64fd9323ac487b429e1554219c93d8223b1cf)
feat(tactic/mk_iff_of_inductive_prop): add tactic to represent inductives using logical connectives

### [2018-05-03T13:46:52-04:00](https://github.com/leanprover-community/mathlib/commit/fa7a180cbd44f5168aa6a21acc629a6d5e5a05f4)
feat(tactic/solve_by_elim): make solve_by_elim easier to use correctly ([#131](https://github.com/leanprover-community/mathlib/pull/#131))

### [2018-05-03T14:41:35+02:00](https://github.com/leanprover-community/mathlib/commit/ef43edfd1e7fb79914c71424ef4715cc60f3a756)
feat(data/finset): add list.to_finset theorems

### [2018-05-03T11:23:10+02:00](https://github.com/leanprover-community/mathlib/commit/02c2b56a3358223fce559b7d2969b1ccb84d789f)
feat(analysis/topology/topological_space): t2 instances for constructions of limit type

### [2018-04-29T01:27:12-04:00](https://github.com/leanprover-community/mathlib/commit/a97101d2df5d186848075a2d0452f6a04d8a13eb)
fix(docs/naming): use names in use ([#122](https://github.com/leanprover-community/mathlib/pull/#122))

### [2018-04-26T18:29:10+02:00](https://github.com/leanprover-community/mathlib/commit/48485a2e6ef3554a2c619f8437017bccde201659)
refactor(logic/relation,group_theory/free_group): add theory for reflextive/transitive relations & use them for the free group reduction

### [2018-04-25T14:35:58+02:00](https://github.com/leanprover-community/mathlib/commit/5df2ee70cfd576e6fa11359496a8a06c029151c9)
style(group_theory): move free_group from algebra to group_theory

### [2018-04-25T14:28:21+02:00](https://github.com/leanprover-community/mathlib/commit/716decc00ec15ebf8d9ca3c5c9c27a08e072e926)
feat(algebra): add free groups ([#89](https://github.com/leanprover-community/mathlib/pull/#89))

### [2018-04-25T13:44:07+02:00](https://github.com/leanprover-community/mathlib/commit/e6264eb4b2c17d2b3563638d14164b6134056be2)
feat(order/conditionally_complete_lattice): add instance complete_linear_order -> conditionally_complete_linear_order; add cSup/cInf_interval

### [2018-04-25T13:06:49+02:00](https://github.com/leanprover-community/mathlib/commit/bf04127507c65c476bbf0d44f1d8fdcdd7f89f8f)
feat(order): add liminf and limsup over filters (c.f. Sébastien Gouëzel's [#115](https://github.com/leanprover-community/mathlib/pull/#115))

### [2018-04-24T22:18:49-04:00](https://github.com/leanprover-community/mathlib/commit/78d28c5cb58f6a22fbb8fc940cc6f97bc0111602)
fix(*): update to lean

### [2018-04-24T21:11:29-04:00](https://github.com/leanprover-community/mathlib/commit/44271cffbcb60028a3ee7932cfd7ba4ebb09cc11)
feat(tactic/interactive): add `clean` tactic

for removing identity junk and annotations added to terms by common tactics like dsimp

### [2018-04-24T20:17:52-04:00](https://github.com/leanprover-community/mathlib/commit/e4c09d4e7a6fd97ca42c1a49a999d3f566fb44cb)
feat(analysis/topology/topological_space): a finite union of compact sets is compact ([#117](https://github.com/leanprover-community/mathlib/pull/#117))

### [2018-04-24T20:16:10-04:00](https://github.com/leanprover-community/mathlib/commit/e4e465925b37617ed3dc63220ab6e640f7bfcaad)
feat(tactic/generalize_hyp): a version of `generalize` that also applies to assumptions ([#110](https://github.com/leanprover-community/mathlib/pull/#110))

### [2018-04-24T17:00:19-04:00](https://github.com/leanprover-community/mathlib/commit/f87135b3e75be782bc97adfa246c046a94d3743e)
feat(algebra/pi_instances): Adds pi instances for common algebraic structures

### [2018-04-24T15:57:06-04:00](https://github.com/leanprover-community/mathlib/commit/3b73ea110c8081789a8cf5217b2ac885238946cd)
feat(tactic/convert): tactic similar to `refine` ([#116](https://github.com/leanprover-community/mathlib/pull/#116))

... but which generates equality proof obligations for every discrepancy between the goal and
the type of the rule

### [2018-04-24T14:30:20-04:00](https://github.com/leanprover-community/mathlib/commit/7dcd6f51f3c310ff66a466d5a219f5c079a8da2e)
feat(tactic/interactive): adding a discharger argument to solve_by_elim ([#108](https://github.com/leanprover-community/mathlib/pull/#108))

### [2018-04-24T14:26:32-04:00](https://github.com/leanprover-community/mathlib/commit/009968eae72d4246e352092a7cf3c9a5276589d9)
feat(docs/tactic): document congr_n and unfold_coes ([#105](https://github.com/leanprover-community/mathlib/pull/#105))

### [2018-04-24T14:25:48-04:00](https://github.com/leanprover-community/mathlib/commit/44391c956338ac8a08873d3e85c890c478046235)
doc(docs/elan.md): a short setup guide

A short guide on getting started with Lean, mathlib and elan.
Adds a link to docs/elan.md in README.md

### [2018-04-24T14:24:59-04:00](https://github.com/leanprover-community/mathlib/commit/23c07fd795c8431aa8ae0e2e8f220aec6aab8138)
feat(docs/extras/cc) Documents the cc tactic

From explanations and experiments by Simon, Gabriel and Kenny at
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/cc.20is.20so.20powerful

### [2018-04-24T14:22:35-04:00](https://github.com/leanprover-community/mathlib/commit/e2c7421558ac37afe6caaf9e23a9705a974b5ab4)
feat(tactic/ext): new `ext` tactic and corresponding `extensionality` attribute

### [2018-04-24T14:15:55-04:00](https://github.com/leanprover-community/mathlib/commit/d862939b1d2b148b032fec14d1155525449d332b)
fix(tactic/wlog): in the proof of completeness, useful assumptions were not visible

### [2018-04-19T08:49:27-04:00](https://github.com/leanprover-community/mathlib/commit/c13c5ea701bb1eec057e0a242d9f480a079105e9)
fix(ordinal): fix looping simp

### [2018-04-19T07:58:36-04:00](https://github.com/leanprover-community/mathlib/commit/2d935cbc4d3bc07b0445b4178dad9f9ac0e75af6)
refactor(lebesgue_measure): clean up proofs

### [2018-04-19T04:40:28-04:00](https://github.com/leanprover-community/mathlib/commit/7d1ab388bb097db5d631d11892e8f110e1f2e9cd)
feat(list/basic,...): minor modifications & additions

based on Zulip conversations and requests

### [2018-04-17T21:08:42-04:00](https://github.com/leanprover-community/mathlib/commit/ed0986768115ade2d44fc367db9d907580c40b06)
feat(data/list/basic): prefix_or_prefix

### [2018-04-17T01:53:53-04:00](https://github.com/leanprover-community/mathlib/commit/d9daa1020125952236374a6ec02d379f9a38221c)
chore(group_theory): fixups

### [2018-04-16T19:39:05-04:00](https://github.com/leanprover-community/mathlib/commit/4f42fbf1a60d6c7ebcd56de8975a38c4db68a3e7)
feat(data/option): more option stuff

### [2018-04-16T19:01:44-04:00](https://github.com/leanprover-community/mathlib/commit/d5c73c0b372d1181ca386e3264497e2c56077d93)
chore(*): trailing spaces

### [2018-04-16T19:00:13-04:00](https://github.com/leanprover-community/mathlib/commit/b7db508080ff495a8f3b7d7dfef7132d7af688d1)
feat(analysis/topology/topological_space): basis elements are open

### [2018-04-16T19:00:13-04:00](https://github.com/leanprover-community/mathlib/commit/6dd2bc0e4ae08cdbb3819f55e8eafb82b5f6a60f)
feat(data/option): more option decidability

### [2018-04-16T20:29:17+02:00](https://github.com/leanprover-community/mathlib/commit/f2361dc21f6d5798ea075a80a6846eea63b48279)
fix(group_theory/coset): left_cosets.left_cosets -> left_cosets.eq_class_eq_left_coset is now a theorem

### [2018-04-16T20:09:50+02:00](https://github.com/leanprover-community/mathlib/commit/910de7ec35d474e2076e89856f62df85abd9ad2c)
refactor(group_theory/coset): left_cosets is now a quotient ([#103](https://github.com/leanprover-community/mathlib/pull/#103))

### [2018-04-15T17:58:13+02:00](https://github.com/leanprover-community/mathlib/commit/479a12267bc8a6175f6b4c32e3a8f07d47d9a7ec)
doc(doc): add topological space doc ([#101](https://github.com/leanprover-community/mathlib/pull/#101))

### [2018-04-15T17:41:57+02:00](https://github.com/leanprover-community/mathlib/commit/c34f2027c45be232650d41abc8d4a57a26379ea2)
Adding some notes on calc

### [2018-04-15T17:39:03+02:00](https://github.com/leanprover-community/mathlib/commit/21d561827b09e2956dc9c8e6adaa3a48ec909e72)
feat(docs/styles): Some more indentation guidelines ([#95](https://github.com/leanprover-community/mathlib/pull/#95))

Fixed also a typo pointed out by Scott

### [2018-04-15T17:36:59+02:00](https://github.com/leanprover-community/mathlib/commit/f1179bd92f268ec1690e34f06bcb50677742b2e7)
feat(algebra/big_operators): update prod_bij_ne_one ([#100](https://github.com/leanprover-community/mathlib/pull/#100))

### [2018-04-13T19:25:49+02:00](https://github.com/leanprover-community/mathlib/commit/560523350737e9b4e500aba168923c2678384702)
feat(algebra/big_operators): add prod_sum (equating the product over a sum to the sum of all combinations)

### [2018-04-11T17:11:19+02:00](https://github.com/leanprover-community/mathlib/commit/f1e46e1fa17a027c900e77144d8231a089be9227)
fix(.travis.yml): fix some elan

### [2018-04-11T16:41:07+02:00](https://github.com/leanprover-community/mathlib/commit/b13f404665953779a29f225a6504bfba21f55a5c)
chore(.travis.yml): show some elan

### [2018-04-11T15:17:30+02:00](https://github.com/leanprover-community/mathlib/commit/5f360e3e0168e36e52eef1742452fc9b4f96bc18)
feat(group_theory): add group.closure, the subgroup generated by a set

### [2018-04-11T14:49:46+02:00](https://github.com/leanprover-community/mathlib/commit/fea249167f1bd788fabd02449f1aca9f615e40fc)
chore(group_theory): move order_of into its own file; base costes on left_coset

### [2018-04-11T13:50:33+02:00](https://github.com/leanprover-community/mathlib/commit/d2ab199faa45479050e536a30682c900b9d3cc98)
chore(group_theory): simplify proofs; generalize some theorems

### [2018-04-11T10:25:21+02:00](https://github.com/leanprover-community/mathlib/commit/ea0fb11bbdfd3ef67ecf5445bccdc75612bdfad1)
style(group_theory): try to follow conventions (calc indentation, lowercase names, ...)

### [2018-04-11T10:24:33+02:00](https://github.com/leanprover-community/mathlib/commit/fa86d349527766c2d0fc3173fcda302cdd5673f3)
feat(group_theory): add left/right cosets and normal subgroups

### [2018-04-10T14:38:56+02:00](https://github.com/leanprover-community/mathlib/commit/f85330a8db3a4af3daebd039d6eaa6526efdbadb)
feat(group_theory/submonoid): relate monoid closure to list product

### [2018-04-10T13:58:37+02:00](https://github.com/leanprover-community/mathlib/commit/4a15503128250442ed5c81a6a925b9643a9c0225)
refactor(ring_theory): unify monoid closure in ring theory with the one in group theory

### [2018-04-10T13:13:52+02:00](https://github.com/leanprover-community/mathlib/commit/ec185633f06495212d26647c44be5a9e3309e049)
feat(group_theory): add subtype instanes for group and monoid; monoid closure

### [2018-04-10T13:02:43+02:00](https://github.com/leanprover-community/mathlib/commit/88960f08c9dbcd2f11fc016b816ad803dc0c33f3)
refactor(algebra): move is_submonoid to group_theory and base is_subgroup on is_submonoid

### [2018-04-09T14:39:12-04:00](https://github.com/leanprover-community/mathlib/commit/bd0a555d4aa018099883c29b1a12fa8615860977)
fix(algebra/group_power): remove has_smul

This was causing notation overload problems with module smul

### [2018-04-09T11:32:20+02:00](https://github.com/leanprover-community/mathlib/commit/b02733df242aa632cb917f68b36c44a3c29175b2)
fix(data/finset): change argument order of finset.induction(_on) so that the induction tactic accepts them

### [2018-04-09T10:30:13+02:00](https://github.com/leanprover-community/mathlib/commit/018cfddb492723561b9ae74f79e7adc54c9bc490)
feat(linear_algebra/multivariate_polynomial): make theory computational

### [2018-04-08T01:00:54-04:00](https://github.com/leanprover-community/mathlib/commit/2bd5e2159d20a8f20d04fc4d382e65eea775ed39)
feat(data/int/modeq): Modular arithmetic for integers

### [2018-04-08T00:45:25-04:00](https://github.com/leanprover-community/mathlib/commit/68158304af5dc0ce44a9ab169a53693d1e3c030e)
chore(measure_theory/measure_space): add coe_fn instance

### [2018-04-08T00:35:55-04:00](https://github.com/leanprover-community/mathlib/commit/03d5bd975eaef356e010e43feffd7919ae9ab1cd)
fix(*): update to lean

### [2018-04-07T22:38:50-04:00](https://github.com/leanprover-community/mathlib/commit/e9b9014bb45def5e87048a20b92d0833f5610317)
feat(data/erased): VM-erased data type

### [2018-04-05T01:29:34-04:00](https://github.com/leanprover-community/mathlib/commit/22e671c5ed5fd1b891fb73aa10c9425d1c6cfd3d)
fix(travis.yml): fix travis setup for new nightlies

### [2018-04-05T01:05:02-04:00](https://github.com/leanprover-community/mathlib/commit/81264ec71652a8d9cc57a4f08f6762f121202196)
fix(leanpkg.toml): remove lean_version

I will keep marking the nightly version here, but I will leave it commented out until I can figure out how to make travis work with it

### [2018-04-05T00:59:52-04:00](https://github.com/leanprover-community/mathlib/commit/08f19fde695d20cf1bd899969a1c59b350dd9e43)
chore(data/nat/prime): style and minor modifications

### [2018-04-05T00:35:23-04:00](https://github.com/leanprover-community/mathlib/commit/efa4f92ef5db8dffe7c2013a8edc333e96716a2b)
feat(data/nat/prime): lemmas about nat.factors

### [2018-04-05T00:22:45-04:00](https://github.com/leanprover-community/mathlib/commit/2d370e9d9b3241f9dd9cfcc29f62a119bd6217c8)
feat(algebra/euclidean_domain): euclidean domains / euclidean algorithm

### [2018-04-05T00:16:34-04:00](https://github.com/leanprover-community/mathlib/commit/467f60ffe91a9a1eeb97ff36ea7df0202893bde4)
feat(data/nat/basic): add div_le_div_right

Based on [#91](https://github.com/leanprover-community/mathlib/pull/#91) by @MonoidMusician

### [2018-04-05T00:13:56-04:00](https://github.com/leanprover-community/mathlib/commit/47f1384b9eef7eac2af3cba619a51da37edfceab)
doc(docs/extras): Adding notes on simp

### [2018-04-05T00:12:09-04:00](https://github.com/leanprover-community/mathlib/commit/73d481a2bdd8dcc635e3eaad128fe792f6016d49)
adding explanation of "change"

### [2018-04-05T00:07:53-04:00](https://github.com/leanprover-community/mathlib/commit/c87f1e6ee59d1db3f490aa91e5e0f29e35c3e4b8)
fix(*): finish lean update

### [2018-04-03T21:23:26-04:00](https://github.com/leanprover-community/mathlib/commit/5717986f4949d4c0838b894d655bc57e3618accb)
fix(*): update to lean

also add mathlib nightly version to leanpkg.toml

### [2018-04-01T22:10:37-04:00](https://github.com/leanprover-community/mathlib/commit/777f6b406b6e0c4b977876c4ac17ab5dc5abe09f)
feat(data/set/basic): add some more set lemmas

### [2018-04-01T21:30:17-04:00](https://github.com/leanprover-community/mathlib/commit/d80ca5926c00e25bb6a1381e5739f7e2dc064bd8)
feat(data/fin): add fz/fs recursor for fin

### [2018-03-30T14:05:43+02:00](https://github.com/leanprover-community/mathlib/commit/162edc3f5cccd1cfd53aec35c1c0f3c6a1f37f42)
feat(order): add complete lattice of fixed points (Knaster-Tarski) by Kenny Lau https://github.com/leanprover/mathlib/pull/88

### [2018-03-29T17:23:46+02:00](https://github.com/leanprover-community/mathlib/commit/c54d431d366f5965ec9a1b3cfcbe072779e155ca)
fix(.): unit is now an abbreviation: unit := punit.{1}

### [2018-03-25T19:59:40-04:00](https://github.com/leanprover-community/mathlib/commit/d84af03bdb8ec4e02c96b6262e7b78c8f3de412b)
fix(data/option): revert to lean commit 28f414

### [2018-03-22T14:08:02+01:00](https://github.com/leanprover-community/mathlib/commit/e5c1c5e1b4867846e323af07ca2ee5791b414dff)
fix(number_theory/dipoh): has_map.map -> functor.map

### [2018-03-22T11:27:24+01:00](https://github.com/leanprover-community/mathlib/commit/a357b7954bbfe709eba8f2f77e6888ba2bb24674)
feat(analysis): measurable_if

### [2018-03-21T19:31:04-04:00](https://github.com/leanprover-community/mathlib/commit/868bbc6e93d844a27b6e7f6f3bc2046659a9c468)
fix(*): update to lean

### [2018-03-21T19:31:04-04:00](https://github.com/leanprover-community/mathlib/commit/638265c054a280f3947aff34c2c728b29b8ed0a4)
fix(set_theory/zfc): improve pSet.equiv.eq

I claimed in the comment that this converse was not provable, but it is (because equiv is embedded in the definition of mem). Thanks to Vinoth Kumar Raman for bringing this to my attention.

### [2018-03-21T19:31:04-04:00](https://github.com/leanprover-community/mathlib/commit/f3660dfcebeea53ad179efb307f5313ab533a53d)
chore(logic/basic): protect classical logic theorems

You can't use these theorems with `open classical` anyway, because of disambiguation with the `_root_` theorems of the same name.

### [2018-03-21T18:56:23-04:00](https://github.com/leanprover-community/mathlib/commit/486e4ed9d30d82e2634218a99822ea37bd0f4aa6)
fix(test suite): remove `sorry` warning in test suite

### [2018-03-15T00:57:20-04:00](https://github.com/leanprover-community/mathlib/commit/f7977ff5a6bcf7e5c54eec908364ceb40dafc795)
feat(data/finset): add finset.powerset

### [2018-03-13T05:57:49-04:00](https://github.com/leanprover-community/mathlib/commit/4ceb545f7e07431263e1131a9c9524a28de99472)
feat(data/list/basic): stuff about `list.sublists`

### [2018-03-12T20:45:43+01:00](https://github.com/leanprover-community/mathlib/commit/5f8c26ce49211e34bfd85c15dfbfbe5d405ab106)
feat(analysis/measure_theory): measures are embedded in outer measures; add map, dirac, and sum measures

### [2018-03-12T17:09:31+01:00](https://github.com/leanprover-community/mathlib/commit/36a061b6e1eb1b1d898628fa0a5e4512e01ab1d5)
feat(analysis/measure_theory): outer_measures form a complete lattice

### [2018-03-11T14:26:05+01:00](https://github.com/leanprover-community/mathlib/commit/64a8d564674608dc10539e97036767165d3fb51f)
chore(order/filter): simplify definition of filter.prod; cleanup

### [2018-03-10T20:37:53+01:00](https://github.com/leanprover-community/mathlib/commit/b15409291946da55671fcb61b4cc80ae3e533a66)
feat(data/finsupp): make finsupp computable; add induction rule; removed comap_domain

### [2018-03-10T13:38:59+01:00](https://github.com/leanprover-community/mathlib/commit/b97b7c38416d4f6f258882f807458d4f980976ef)
feat(group_theory): add a little bit of group theory; prove of Lagrange's theorem

### [2018-03-10T12:39:38+01:00](https://github.com/leanprover-community/mathlib/commit/d010717f089a7c1e53fa5d5098cf2bb4f65a061a)
chore(linear_algebra): flatten hierarchy, move algebra/linear_algebra to linear_algebra

### [2018-03-09T15:55:09+01:00](https://github.com/leanprover-community/mathlib/commit/d78c8ea201ddf8da3f4356a63f65332a8037c3a6)
chore(ring_theory): cleaned up ideals

### [2018-03-09T14:39:42+01:00](https://github.com/leanprover-community/mathlib/commit/06c54b33c7dc9e81ece45a24f2918d253b914db8)
chore(ring_theory): introduce r_of_eq for localization

### [2018-03-09T14:39:42+01:00](https://github.com/leanprover-community/mathlib/commit/e658d369d85cd61e305168a44bacdb57cd11980a)
chore(ring_theory): fix indentation

### [2018-03-08T16:21:02+01:00](https://github.com/leanprover-community/mathlib/commit/a6960f53d9eeccdaacdbbcf71476e674b4b371fb)
chore(ring_theory): add copyright headers

### [2018-03-08T13:57:16+01:00](https://github.com/leanprover-community/mathlib/commit/fe0f2a34b2bc71d480c5fc7766d889e0a4de3ccd)
fix(analysis/topology/topological_structures): remove unnecessary hypothesis

### [2018-03-08T11:45:04+01:00](https://github.com/leanprover-community/mathlib/commit/a7d8c5f818313b338b5af986a463224bc1b80542)
feat(tactic): add `wlog` (without loss of generality), `tauto`, `auto` and `xassumption`

* `tauto`: for simple tautologies;
* `auto`: discharging the goals that follow directly from a few assumption applications;
* `xassumption`: similar to `assumption` but matches against the head of assumptions instead of the whole thing

### [2018-03-08T11:25:28+01:00](https://github.com/leanprover-community/mathlib/commit/c852939f5fcb3a1f0ebe38d8eebc6aede22b9e25)
feat(ring_theory): move localization

### [2018-03-08T10:42:28+01:00](https://github.com/leanprover-community/mathlib/commit/0b81b249f35a630adf89fe73ba2cc329d65e5f97)
feat(analysis/topological_structures): add tendsto_of_tendsto_of_tendsto_of_le_of_le

### [2018-03-08T09:55:42+01:00](https://github.com/leanprover-community/mathlib/commit/353c4948273e516af373ba3f96e5f92ea34e7ce1)
fix(docs): more converter -> conversion

### [2018-03-08T09:51:03+01:00](https://github.com/leanprover-community/mathlib/commit/fa255396ff01ea2c0aaef1a2a1000fb03f217468)
feat(docs/extras/conv): Documents conv mode ([#73](https://github.com/leanprover-community/mathlib/pull/#73))

### [2018-03-07T13:47:04+01:00](https://github.com/leanprover-community/mathlib/commit/22237f41029bcdb879a8ce6323971da1c2caf587)
feat(data/fintype): pi is closed under fintype & decidable_eq

### [2018-03-07T13:47:00+01:00](https://github.com/leanprover-community/mathlib/commit/e6afbf540ffb888a436b5ac899792fbf9d0608da)
feat(data/finset): add Cartesian product over dependent functions

### [2018-03-07T13:46:54+01:00](https://github.com/leanprover-community/mathlib/commit/10cf239eb397f254670b6a3ea15bd257469844ba)
feat(data/multiset): add Cartesian product over dependent functions

### [2018-03-07T13:46:54+01:00](https://github.com/leanprover-community/mathlib/commit/be4a35fdcbc4858940fb7e75eb1f01707cd12d47)
feat(data/multiset): add dependent recursor for multisets

### [2018-03-07T13:46:39+01:00](https://github.com/leanprover-community/mathlib/commit/eef3a4d5b276b3db0011bd09c5c2bafa8bf716bc)
feat(data/multiset): add map_hcongr, bind_hcongr, bind_bind, attach_zero, and attach_cons

### [2018-03-07T13:46:39+01:00](https://github.com/leanprover-community/mathlib/commit/bbd0203bd49f8ea7f072c5091d6b0baa39ae44e2)
feat(data/multiset): decidable equality for functions whose domain is bounded by multisets

### [2018-03-07T13:46:32+01:00](https://github.com/leanprover-community/mathlib/commit/dc8c35f7267f261387a8ccd5b1628104f35dcde6)
feat(logic/function): add hfunext and funext_iff

### [2018-03-06T16:12:46-05:00](https://github.com/leanprover-community/mathlib/commit/33be7dcc99c089554d45dd3d8a183ac4b832f209)
doc(docs/theories): Description of other set-like types

From [#75](https://github.com/leanprover-community/mathlib/pull/#75)

### [2018-03-05T21:58:36+01:00](https://github.com/leanprover-community/mathlib/commit/65cab91050c626039a0d2154c8c4dbf974a41458)
doc(order/filter): add documentation for `filter_upward`

### [2018-03-05T18:18:38+01:00](https://github.com/leanprover-community/mathlib/commit/5193194e954b419e417e3efc84c0e1ebae98e111)
feat(order/filter): reorder filter theory; add filter_upwards tactic

### [2018-03-05T17:55:59+01:00](https://github.com/leanprover-community/mathlib/commit/0487a3203e1c12df6db87f49ae63e123f9456437)
chore(*): cleanup

### [2018-03-05T16:11:22+01:00](https://github.com/leanprover-community/mathlib/commit/ec9dac3ada9aa2107d5f3fceb3d28eee113278b8)
chore(*): update to Lean d6d44a19

### [2018-02-26T19:33:33-05:00](https://github.com/leanprover-community/mathlib/commit/f98626c519c3d0e436cddf52772f3669ed9a10c7)
chore(.travis.yml): add notification hook

### [2018-02-25T08:41:54-05:00](https://github.com/leanprover-community/mathlib/commit/8f680d0818cd3a1e1bf6d9e51c4e07eac08458f5)
fix(docs/tactics): update instance cache tactics doc ([#70](https://github.com/leanprover-community/mathlib/pull/#70))

### [2018-02-25T05:09:48-05:00](https://github.com/leanprover-community/mathlib/commit/14e10bbda42f928bdc6f9664e8d9826e598a68fe)
fix(*): update to lean

### [2018-02-25T00:08:30-05:00](https://github.com/leanprover-community/mathlib/commit/c88a9e61f9d723f9dde178a3e2bc462d156e3f9a)
doc(docs/tactics): Document the find command ([#67](https://github.com/leanprover-community/mathlib/pull/#67))

### [2018-02-22T19:42:03-05:00](https://github.com/leanprover-community/mathlib/commit/1630725861c6db8d73bf66019386594915771cf2)
feat(data/finset): insert_union_distrib ([#66](https://github.com/leanprover-community/mathlib/pull/#66))

* chore(data/finset): match style guide

* feat(data/finset): insert_union_distrib

### [2018-02-22T15:14:26-05:00](https://github.com/leanprover-community/mathlib/commit/49b196c47abf021b2d35ad5005d5ae25e0b3e000)
feat(data/multiset): erase_lt

### [2018-02-22T14:08:57-05:00](https://github.com/leanprover-community/mathlib/commit/d68c8ae05f3347962559ed3504ea716bf95b3ab9)
feat(set_theory/cardinal): some missing power theorems

### [2018-02-21T20:14:45-05:00](https://github.com/leanprover-community/mathlib/commit/22a52c398c6ca7f2e4505809b22c31a3c2f728db)
fix(tactic/find): update to lean

### [2018-02-21T04:29:29-05:00](https://github.com/leanprover-community/mathlib/commit/8ae1cefba42b341fd6eaa24b18b3e1e226055859)
feat(tactic/find): add @Kha's #find command

### [2018-02-20T22:14:23-05:00](https://github.com/leanprover-community/mathlib/commit/e2a562a8df52c2b0fffad361605fcbc03cb99b4b)
refactor(analysis/topology): simplify is_topological_basis_of_open_of_nhds

### [2018-02-20T22:12:18-05:00](https://github.com/leanprover-community/mathlib/commit/ebcbb6bb6d6a186b565f5aefcb159ed238d83f7f)
doc(.): MD documentation ([#58](https://github.com/leanprover-community/mathlib/pull/#58))

### [2018-02-20T15:36:49+01:00](https://github.com/leanprover-community/mathlib/commit/140c6728d6474eb259e7ddbd5c2d440426ff0f9a)
feat(algebra/order_functions): add abs_le_max_abs_abs; and relations between mul and max / min (suggested by @PatrickMassot)

### [2018-02-20T15:22:36+01:00](https://github.com/leanprover-community/mathlib/commit/3e683f413c0d80196e2418d44aaa8eafd96f443c)
chore(algebra,order): cleanup min / max using the lattice theory

### [2018-02-20T10:43:29+01:00](https://github.com/leanprover-community/mathlib/commit/504a2dc888dcabad28f78f0ece90cc08b08e2bcb)
Create choose.lean ([#48](https://github.com/leanprover-community/mathlib/pull/#48))

deat(data/nat): add choose function to compute the binomial coefficients

### [2018-02-19T11:00:25+01:00](https://github.com/leanprover-community/mathlib/commit/3c25d94a50d601026dbcd86c58173bc7404b0257)
feat(algebra/archimedean): pow_unbounded_of_gt_one ([#50](https://github.com/leanprover-community/mathlib/pull/#50))

### [2018-02-19T10:55:46+01:00](https://github.com/leanprover-community/mathlib/commit/500dcc92d81be3b99b4d6f4802680fafb29277ba)
feat(analysis/metric_space): add tendsto_iff_dist_tendsto_zero

### [2018-02-19T10:38:12+01:00](https://github.com/leanprover-community/mathlib/commit/3ef7c7df9a62536276adc4e1d29322d8c8713269)
fix(analysis/metric_space): remove unnecessary topological_space assumption from tendsto_dist

### [2018-02-18T00:16:10-05:00](https://github.com/leanprover-community/mathlib/commit/9b306b2eb7c2bc0e0e7243a7eb43b836d2c867b7)
feat(option.to_list)

### [2018-02-15T11:21:33+01:00](https://github.com/leanprover-community/mathlib/commit/ff4af0d4bd7942d2d14083a1a787af26e66d91db)
feat(data/list): add append_eq_nil and update_nth_eq_nil

### [2018-02-15T10:43:12+01:00](https://github.com/leanprover-community/mathlib/commit/c0153c11f8a72d1fe16c72f39c011bef335bdd74)
feat(data/multiset): add smielattie_sup_bot instance; add disjoint_union_left/_right

### [2018-02-15T09:34:21+01:00](https://github.com/leanprover-community/mathlib/commit/8741b647e2eaac8156350ffef26756c240c7e56e)
feat(algebra/group_power): add pow_inv and pow_abs

### [2018-02-14T13:33:17+01:00](https://github.com/leanprover-community/mathlib/commit/eb32bfb1db29f3089b5437b2a8005d69b0dfe002)
feat(data/multiset): disjoint_ndinsert theorems

### [2018-02-12T07:11:07-05:00](https://github.com/leanprover-community/mathlib/commit/6ff5f3edbb3fec18c3f2a5b2c7124714156b59e5)
feat(data/equiv): generalize list_equiv_of_equiv over universes ([#52](https://github.com/leanprover-community/mathlib/pull/#52))

### [2018-02-08T22:50:08-05:00](https://github.com/leanprover-community/mathlib/commit/5dd341920a487e16af657178ee2ad0e3243168e7)
feat(order/conditionally_complete_lattice): Conditionally complete lattices

### [2018-02-08T22:39:23-05:00](https://github.com/leanprover-community/mathlib/commit/6ef721ea181e62b26d1bf22142cff44ba0487938)
feat(data/finset): not_mem theorems

Adapted from [#44](https://github.com/leanprover-community/mathlib/pull/#44)

### [2018-02-06T17:03:30-05:00](https://github.com/leanprover-community/mathlib/commit/14a19bf3d2589a9801ef281808d8e4faa90db2b1)
fix(*): update to lean

Adding typeclasses to the context must now be done with `haveI`, `introsI`, etc.

### [2018-02-05T01:47:42-05:00](https://github.com/leanprover-community/mathlib/commit/5da3eb031bbd567178c0bda04281b78605a351e0)
Fix universe parameter in permutation group

### [2018-02-05T01:47:42-05:00](https://github.com/leanprover-community/mathlib/commit/cb4449f1c4628a97373c9ffbe977edb96f3b443b)
Permutation group instance for any type

### [2018-02-01T22:14:26-05:00](https://github.com/leanprover-community/mathlib/commit/03fefd43615ffcd59ed39bb08a891bc76f65b07b)
Create localization.lean

### [2018-02-01T19:43:27-05:00](https://github.com/leanprover-community/mathlib/commit/e0539dd9619e7d0c8d3460912002e75bf93b4079)
fix(data/hash_map,...): update to lean

### [2018-01-26T03:15:01-05:00](https://github.com/leanprover-community/mathlib/commit/edd62de51a714ecd3bf26839748e67050aa87a08)
fix(set_theory/zfc): update to lean

### [2018-01-26T02:52:13-05:00](https://github.com/leanprover-community/mathlib/commit/f46d32b0eb40424f9b7e9e8fb46e3e8b3f55ea4b)
feat(algebra/archimedean): generalize real thms to archimedean fields

### [2018-01-25T01:34:48-05:00](https://github.com/leanprover-community/mathlib/commit/0e4218747eea51d1245c20ca2639c967466b1532)
fix(algebra/module): fix module typeclass resolution

Before this change, any looping typeclass instance on `ring` (like `ring A -> ring (f A)`) would cause unrelated typeclass problems such as `has_add B` to search for `module ?M B` and then `ring ?M`, leading to an infinite number of applications of the looping ring instance. leanprover/lean[#1881](https://github.com/leanprover-community/mathlib/pull/#1881) promises to fix this, but until then here is a workaround.

### [2018-01-24T14:25:32-05:00](https://github.com/leanprover-community/mathlib/commit/7fba1afab85765fde363aed39525b5ff1bb74b66)
fix(analysis/metric_space): remove superfluous typeclass assumptions

### [2018-01-23T03:30:58-05:00](https://github.com/leanprover-community/mathlib/commit/acb9093feb56870cdb4f2473ab20303a6c383634)
feat(analysis/complex): complex numbers are a top ring

### [2018-01-23T03:07:52-05:00](https://github.com/leanprover-community/mathlib/commit/65c5cb92ba27e9587eafb4102dde8fc0f3be7104)
refactor(data/real): generalize cau_seq to arbitrary metrics

the intent is to use this also for the complex numbers

### [2018-01-23T00:14:20-05:00](https://github.com/leanprover-community/mathlib/commit/5fe8fbf1b42bfa80385b7140a495930f23cd1d18)
feat(data/complex): properties of the complex absolute value function

### [2018-01-21T23:57:42-05:00](https://github.com/leanprover-community/mathlib/commit/5a6521233343b52e97a7f5353260c07076835e03)
feat(data/real): real square root function, sqrt 2 is irrational

### [2018-01-20T21:28:43-05:00](https://github.com/leanprover-community/mathlib/commit/ffafdc69b87dbeed2e9b3bdf35f33e46d2e6b74c)
feat(tactic/ring): extend ring tactic to allow division by constants

### [2018-01-20T17:03:57-05:00](https://github.com/leanprover-community/mathlib/commit/bcbf0d56a7bc4552283f2b21fd84320f4b5727a7)
refactor(data/complex): clean up proofs

### [2018-01-19T17:05:43-05:00](https://github.com/leanprover-community/mathlib/commit/baa4b09ef00190aef0a547d6a12a6212babd3b2e)
feat(analysis/real): swap out the definition of real, shorten proofs

### [2018-01-19T16:18:40-05:00](https://github.com/leanprover-community/mathlib/commit/bb1a9f2cc8d9b95305eb56d9a13406586eea2ae0)
feat(data/real,*): supporting material for metric spaces

### [2018-01-17T17:53:52-05:00](https://github.com/leanprover-community/mathlib/commit/0ac694c04ab68428e65671f20cf0696280689b56)
fix(tactic/interactive): update to lean

### [2018-01-16T16:08:50-05:00](https://github.com/leanprover-community/mathlib/commit/e11da6eca6ab1896e76ff0a0b327dbee1707bfee)
feat(data/real): variants on archimedean property

### [2018-01-16T05:29:44-05:00](https://github.com/leanprover-community/mathlib/commit/d84dfb17b9cfbb29e0f728fd22b4f5176f7bd0a9)
feat(data/real): completeness of the (new) real numbers

### [2018-01-15T07:59:59-05:00](https://github.com/leanprover-community/mathlib/commit/04cac9587e1d32479935a0cf132b140b28bbac2b)
feat(data/real): reals from first principles

This is beginning work on a simpler implementation of real numbers, based on Cauchy sequences, to help alleviate some of the issues we have seen with loading times and timeouts when working with real numbers. If everything goes according to plan, `analysis/real.lean` will be the development for the topology of the reals, but the initial construction will have no topology prerequisites.

### [2018-01-14T21:59:50-05:00](https://github.com/leanprover-community/mathlib/commit/65db96689e7baf5abf5d95154a7bec24d7406145)
feat(algebra/field): more division lemmas

### [2018-01-14T17:36:13-05:00](https://github.com/leanprover-community/mathlib/commit/0d6d12aab141afd1cbd338c13269648f5bbaaf7c)
feat(tactic/interactive): replace tactic

### [2018-01-14T01:53:04-05:00](https://github.com/leanprover-community/mathlib/commit/edde6f572a330a0491ffa0dc96146bef5c1a84f7)
feat(tactic/ring): use `ring` for rewriting into pretty print format

### [2018-01-13T19:43:41-05:00](https://github.com/leanprover-community/mathlib/commit/c75b07219b45c6c46b9f1e9beca9129fb94cce57)
fix(*): update to lean

### [2018-01-13T10:22:46-05:00](https://github.com/leanprover-community/mathlib/commit/df7175f38dc40e6fc698ea69cb6957aa06518718)
fix(tactic/ring): bugfix

### [2018-01-13T04:32:47-05:00](https://github.com/leanprover-community/mathlib/commit/341fd517d4bbf071061cd1bb5867f2a8fd799c90)
fix(tactic/ring): bugfix

### [2018-01-13T03:25:35-05:00](https://github.com/leanprover-community/mathlib/commit/2e2d89ba615d743c46f97727fa1bfbe7b700bd74)
feat(tactic/ring): tactic for ring equality

### [2018-01-12T13:08:48-05:00](https://github.com/leanprover-community/mathlib/commit/c39b43fb5c803039a1c8ef427cc446a6697af04b)
feat(analysis/metric_space): sup metric for product of metric spaces

### [2018-01-11T23:22:32-05:00](https://github.com/leanprover-community/mathlib/commit/1dddcf69ecd7edfa3c9ebc4faf0723df8ff128ca)
doc(*): blurbs galore

Document all `def`, `class`, and `inductive` that are reasonably public-facing

### [2018-01-11T16:26:08-05:00](https://github.com/leanprover-community/mathlib/commit/2ffd72ce4c1bdfefcd40c6d9ce05a32589b40035)
refactor(order/basic): remove "increasing/decreasing" unusual defs

### [2018-01-11T16:21:21-05:00](https://github.com/leanprover-community/mathlib/commit/09e08991934a796053bb3e0b3e20205e4b4a2bd9)
fix(analysis/ennreal): fix long-running proofs

### [2018-01-11T12:23:27-05:00](https://github.com/leanprover-community/mathlib/commit/7fd7ea8c323c5f622bda6bc8de6dd352cc2732a8)
fix(analysis/real): more irreducible

### [2018-01-11T06:57:19-05:00](https://github.com/leanprover-community/mathlib/commit/27920e9b771d9b19dbc9696b24ae9e1a87f13783)
fix(data/list/basic,...): update to lean

### [2018-01-10T03:03:39-05:00](https://github.com/leanprover-community/mathlib/commit/dc2857366cdd50ee710b8127866d96cb91791251)
fix(number_theory/pell,...): update to lean

### [2018-01-07T14:32:08-05:00](https://github.com/leanprover-community/mathlib/commit/5ff51dc6993990e600ddee4857a2e207e62f35d1)
feat(analysis/complex): complex numbers as a field

### [2018-01-06T18:57:25-05:00](https://github.com/leanprover-community/mathlib/commit/182c3035667a5ccdbd5059738f978e023b006b9c)
feat(set_theory/cofinality): regular/inaccessible cards, Konig's theorem, next fixpoint function

### [2018-01-06T00:50:12+01:00](https://github.com/leanprover-community/mathlib/commit/4f7835ebe2d634b68cf176877adb46441f8d9a9d)
feat(analysis): add default setup for uniform space of metric space

### [2018-01-04T09:05:50-05:00](https://github.com/leanprover-community/mathlib/commit/0b7b912a9b8ca902afaa64868cd5dc136e2cba68)
feat(set_theory/ordinal_notation): correctness of ordinal power

### [2018-01-04T09:05:02-05:00](https://github.com/leanprover-community/mathlib/commit/3f2435e53800d985ad65f52d901976a4938aff04)
refactor(algebra/group): clean up PR commit

### [2018-01-02T16:52:49-05:00](https://github.com/leanprover-community/mathlib/commit/12bd22bfe8a6efa2ad9f55bbcb619b5f3f088698)
Group morphisms ([#30](https://github.com/leanprover-community/mathlib/pull/#30))

* feat(algebra/group): morphisms and antimorphisms

Definitions, image of one and inverses,
and computation on a product of more than two elements in big_operators.

### [2018-01-02T04:28:01-05:00](https://github.com/leanprover-community/mathlib/commit/37c312094c49b145efc58f2156faa9ea3f91910c)
feat(set_theory/ordinal_notation): ordinal notations for ordinals < e0

This allows us to compute with small countable ordinals using trees of nats.