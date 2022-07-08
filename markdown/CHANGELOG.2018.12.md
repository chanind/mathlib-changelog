### [2018-12-28 02:49:24-05:00](https://github.com/leanprover-community/mathlib/commit/17d6263)
refactor(category_theory): minimize the amount of universe annotations in category_theory ([#552](https://github.com/leanprover-community/mathlib/pull/552))

### [2018-12-26 19:45:48-05:00](https://github.com/leanprover-community/mathlib/commit/a71628a)
feat(algebra/order,...): material on orders ([#554](https://github.com/leanprover-community/mathlib/pull/554))

### [2018-12-24 20:12:21-05:00](https://github.com/leanprover-community/mathlib/commit/a04c7e2)
feat(analysis/topology): miscellaneous topology ([#484](https://github.com/leanprover-community/mathlib/pull/484))
* miscellaneous topology
* C is a proper metric space
* Sum of metric spaces is a def instead of instance
* refactor(analysis): shorten/simplify proofs

### [2018-12-22 01:10:55-05:00](https://github.com/leanprover-community/mathlib/commit/3eb7424)
refactor(data/set/basic): remove unused hypotheses in union_inter_cancel_* ([#551](https://github.com/leanprover-community/mathlib/pull/551))

### [2018-12-21 04:05:56-05:00](https://github.com/leanprover-community/mathlib/commit/cdab35d)
fix(category_theory/punit): fix regression ([#550](https://github.com/leanprover-community/mathlib/pull/550))

### [2018-12-21 03:12:01-05:00](https://github.com/leanprover-community/mathlib/commit/b11b83b)
feat(data/list/basic): rotate a list ([#542](https://github.com/leanprover-community/mathlib/pull/542))

### [2018-12-21 02:35:06-05:00](https://github.com/leanprover-community/mathlib/commit/d7cea06)
feat (ring_theory/noetherian) various lemmas ([#548](https://github.com/leanprover-community/mathlib/pull/548))

### [2018-12-20 23:14:00-05:00](https://github.com/leanprover-community/mathlib/commit/3762d96)
feat(ring_theory/ideals): lift for quotient rings ([#529](https://github.com/leanprover-community/mathlib/pull/529))

### [2018-12-20 23:12:51-05:00](https://github.com/leanprover-community/mathlib/commit/73933b7)
feat(category_theory): assorted small changes from the old limits PR ([#512](https://github.com/leanprover-community/mathlib/pull/512))

### [2018-12-20 09:31:22-05:00](https://github.com/leanprover-community/mathlib/commit/1854dd9)
feat(group_theory/order_of_element): lemmas about card of subgroups and normalizer ([#545](https://github.com/leanprover-community/mathlib/pull/545))

### [2018-12-20 09:30:12-05:00](https://github.com/leanprover-community/mathlib/commit/95bdce8)
feat(data/set/finite): card_range_of_injective ([#543](https://github.com/leanprover-community/mathlib/pull/543))

### [2018-12-20 09:29:35-05:00](https://github.com/leanprover-community/mathlib/commit/0882f8e)
feat(data/fintype): exists_ne_of_card_gt_one ([#544](https://github.com/leanprover-community/mathlib/pull/544))

### [2018-12-20 09:28:29-05:00](https://github.com/leanprover-community/mathlib/commit/4335380)
feat(data/vector2): vector_zero_subsingleton ([#547](https://github.com/leanprover-community/mathlib/pull/547))

### [2018-12-20 08:15:19-05:00](https://github.com/leanprover-community/mathlib/commit/402e71e)
feat(order/filter): tendsto_at_top_at_top ([#540](https://github.com/leanprover-community/mathlib/pull/540))

### [2018-12-20 08:14:46-05:00](https://github.com/leanprover-community/mathlib/commit/f64b9aa)
feat(data/finsupp): frange ([#537](https://github.com/leanprover-community/mathlib/pull/537))

### [2018-12-20 08:13:39-05:00](https://github.com/leanprover-community/mathlib/commit/bc21f62)
feat(ring_theory/ideal_operations): correspondence under surjection ([#534](https://github.com/leanprover-community/mathlib/pull/534))

### [2018-12-20 08:12:52-05:00](https://github.com/leanprover-community/mathlib/commit/f7697ce)
feat(data/equiv/algebra): ring_equiv ([#533](https://github.com/leanprover-community/mathlib/pull/533))

### [2018-12-20 08:12:00-05:00](https://github.com/leanprover-community/mathlib/commit/fc90e00)
feat(ring_theory/subring) various lemmas ([#532](https://github.com/leanprover-community/mathlib/pull/532))
new lemmas:
- is_ring_hom.is_subring_set_range
- ring.in_closure.rec_on
- ring.closure_mono
changed:
- ring.exists_list_of_mem_closure

### [2018-12-20 08:10:59-05:00](https://github.com/leanprover-community/mathlib/commit/35ed7f4)
feat(data/int/basic) int.cast is ring hom ([#531](https://github.com/leanprover-community/mathlib/pull/531))

### [2018-12-20 04:57:06-05:00](https://github.com/leanprover-community/mathlib/commit/ddd1376)
fix(group_theory/coset): remove bad attributes

### [2018-12-20 03:40:45-05:00](https://github.com/leanprover-community/mathlib/commit/caa2076)
feat(command): Add `#where` command, dumping environment info ([#489](https://github.com/leanprover-community/mathlib/pull/489))
The command tells you your current namespace (wherever you write it),
the current `include`s, and the current `variables` which have been
used at least once.

### [2018-12-18 00:51:12-05:00](https://github.com/leanprover-community/mathlib/commit/293ba83)
feat(category_theory/examples/topological_spaces): limits and colimits ([#518](https://github.com/leanprover-community/mathlib/pull/518))

### [2018-12-18 00:48:52-05:00](https://github.com/leanprover-community/mathlib/commit/3d4297b)
feat(category_theory/eq_to_hom): equality of functors; more simp lemmas ([#526](https://github.com/leanprover-community/mathlib/pull/526))

### [2018-12-18 00:45:47-05:00](https://github.com/leanprover-community/mathlib/commit/76a4b15)
feat(data/set/basic): make subtype_val_range a simp lemma ([#524](https://github.com/leanprover-community/mathlib/pull/524))

### [2018-12-17 15:19:10-05:00](https://github.com/leanprover-community/mathlib/commit/2bc9354)
feat(data/nat/enat): extended natural numbers ([#522](https://github.com/leanprover-community/mathlib/pull/522))

### [2018-12-17 15:10:48-05:00](https://github.com/leanprover-community/mathlib/commit/418c116)
feat(data/polynomial): degree_map ([#517](https://github.com/leanprover-community/mathlib/pull/517))

### [2018-12-17 14:47:05-05:00](https://github.com/leanprover-community/mathlib/commit/d947a3a)
refactor(analysis/topology/continuity): use subtype.val_injective ([#525](https://github.com/leanprover-community/mathlib/pull/525))

### [2018-12-17 12:40:24-05:00](https://github.com/leanprover-community/mathlib/commit/21ce531)
fix(data/list): fix build

### [2018-12-17 12:35:03-05:00](https://github.com/leanprover-community/mathlib/commit/b405158)
feat(tactic/explode): improve readability & support proofs using 'suffices' ([#516](https://github.com/leanprover-community/mathlib/pull/516))
* improve readability & support proofs using 'suffices'
* feat(tactic/explode): improve readability & support proofs using 'suffices'

### [2018-12-17 11:35:44-05:00](https://github.com/leanprover-community/mathlib/commit/a4b699c)
feat(order/basic): antisymm_of_asymm

### [2018-12-17 11:35:42-05:00](https://github.com/leanprover-community/mathlib/commit/ebf3008)
feat(tactic/elide): hide subterms of complicated expressions

### [2018-12-17 11:35:41-05:00](https://github.com/leanprover-community/mathlib/commit/b7d74c4)
feat(data/list): list.chain' for empty chains

### [2018-12-17 11:01:50-05:00](https://github.com/leanprover-community/mathlib/commit/e9be5c1)
fix(category/traversable/instances): fix build

### [2018-12-17 10:50:58-05:00](https://github.com/leanprover-community/mathlib/commit/53b08c1)
fix(*): untangle dependency hierarchy

### [2018-12-17 09:19:16-05:00](https://github.com/leanprover-community/mathlib/commit/3ee1071)
feat(data/polynomial): lemmas relating unit and irreducible with degree ([#514](https://github.com/leanprover-community/mathlib/pull/514))

### [2018-12-17 09:15:28-05:00](https://github.com/leanprover-community/mathlib/commit/d4d05e3)
feat(docs/extras/tactic_writing): Tactic writing tutorial ([#513](https://github.com/leanprover-community/mathlib/pull/513))

### [2018-12-17 09:14:26-05:00](https://github.com/leanprover-community/mathlib/commit/e6065a7)
chore(tactic/interactive): make squeeze_simp available by default ([#521](https://github.com/leanprover-community/mathlib/pull/521))

### [2018-12-17 09:08:53-05:00](https://github.com/leanprover-community/mathlib/commit/b140a07)
chore(category_theory/limits/limits): Add missing lemmas ([#520](https://github.com/leanprover-community/mathlib/pull/520))

### [2018-12-17 08:59:28-05:00](https://github.com/leanprover-community/mathlib/commit/218fe1f)
feat(category_theory/opposites): opposites of full and faithful functors ([#504](https://github.com/leanprover-community/mathlib/pull/504))

### [2018-12-15 12:33:43-05:00](https://github.com/leanprover-community/mathlib/commit/9506e6c)
feat(category_theory): functoriality of (co)cones ([#507](https://github.com/leanprover-community/mathlib/pull/507))

### [2018-12-15 12:32:06-05:00](https://github.com/leanprover-community/mathlib/commit/072e1ba)
feat(category_theory/const): Constant functor of object from punit ([#508](https://github.com/leanprover-community/mathlib/pull/508))

### [2018-12-15 12:31:24-05:00](https://github.com/leanprover-community/mathlib/commit/b1d0501)
fix(analysis/topology/topological_space): Improve the lattice structure on opens ([#511](https://github.com/leanprover-community/mathlib/pull/511))

### [2018-12-15 12:18:12-05:00](https://github.com/leanprover-community/mathlib/commit/1f72be1)
feat(category_theory/whiskering): simp-lemmas for unitors and associators ([#505](https://github.com/leanprover-community/mathlib/pull/505))

### [2018-12-15 12:17:49-05:00](https://github.com/leanprover-community/mathlib/commit/28909a8)
feat(category_theory/commas): add simp-lemmas for comma categories ([#503](https://github.com/leanprover-community/mathlib/pull/503))

### [2018-12-10 17:44:27-05:00](https://github.com/leanprover-community/mathlib/commit/3ddfc23)
fix(order/basic): define preorder.lift lt by restriction
This makes it definitionally equal to `inv_image (<) f`, which appears
for example in the type of `inv_image.wf`.

### [2018-12-05 12:45:33-05:00](https://github.com/leanprover-community/mathlib/commit/257fd84)
doc(data/list/basic): improve docstrings [ci-skip]

### [2018-12-05 08:55:27-05:00](https://github.com/leanprover-community/mathlib/commit/b0d47ea)
refactor(set_theory/ordinal): minor simplifications

### [2018-12-05 08:54:06-05:00](https://github.com/leanprover-community/mathlib/commit/843a1c3)
fix(tactic/norm_num): uninstantiated mvars can confuse things

### [2018-12-05 08:42:51-05:00](https://github.com/leanprover-community/mathlib/commit/94d9ac1)
fix(finset): removing bad simp lemmas ([#491](https://github.com/leanprover-community/mathlib/pull/491))

### [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/5856459)
fix(category_theory/limits): add subsingleton instances in preserves.lean

### [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/af6ee09)
fix(category_theory/limits): adding Type annotations in preserves.lean

### [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/74b65e2)
fix(category_theory/limits): change argument order on
cones.precompose/whisker

### [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/4b0a82c)
feat(category_theory): preservation of (co)limits, (co)limits in functor categories

### [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/6267717)
fix(category_theory/limits): namespaces for is_(co)limit

### [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/de4f689)
feat(category_theory/limits): (co)limits, and (co)limits in Type

### [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/a5e2ebe)
feat(category_theory/limits/cones): (co)cones on a diagram

### [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/68c98eb)
feat(category_theory/isomorphism): lemmas for manipulating isomorphisms

### [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/382abaf)
feat(category_theory/const): constant functors

### [2018-12-02 06:41:58-05:00](https://github.com/leanprover-community/mathlib/commit/51afb41)
fix(category_theory/yoneda): add componentwise lemma ([#480](https://github.com/leanprover-community/mathlib/pull/480))