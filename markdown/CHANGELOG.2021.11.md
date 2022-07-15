## [2021-11-30 16:52:36](https://github.com/leanprover-community/mathlib/commit/49f8b6b)
chore(analysis/mean_inequalities[_pow]): use vector notation ([#10546](https://github.com/leanprover-community/mathlib/pull/10546))
Several elementary inequalities in the library are expressed both in arbitrary n-ary versions and in explicit binary, ternary etc versions, with the latter deduced from the former.  This PR introduces vector notation to the proof terms deducing the latter from the former, which shortens them, and also makes them more readable.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean


Modified src/analysis/mean_inequalities_pow.lean




## [2021-11-30 16:52:35](https://github.com/leanprover-community/mathlib/commit/b876e76)
feat(algebra/char_p/two): couple more lemmas + 🏌️ ([#10467](https://github.com/leanprover-community/mathlib/pull/10467))
#### Estimated changes
Modified src/algebra/char_p/two.lean
- \+ *lemma* neg_one_eq_one_iff
- \+ *lemma* order_of_neg_one

Modified src/ring_theory/roots_of_unity.lean
- \+/\- *lemma* is_primitive_root.neg_one



## [2021-11-30 15:07:49](https://github.com/leanprover-community/mathlib/commit/cd69351)
doc(data/stream/defs): add docstrings to most defs ([#10547](https://github.com/leanprover-community/mathlib/pull/10547))
Also move 1 def from `basic` to `defs`.
#### Estimated changes
Modified src/control/random.lean


Modified src/data/stream/basic.lean
- \- *def* stream.corec_state

Modified src/data/stream/defs.lean
- \+ *def* stream.corec_state
- \+/\- *def* stream.head
- \+/\- *def* stream.nth



## [2021-11-30 15:07:48](https://github.com/leanprover-community/mathlib/commit/8bce7eb)
refactor(algebra/group/basic): Migrate `add_group` section into `group` section ([#10532](https://github.com/leanprover-community/mathlib/pull/10532))
#### Estimated changes
Modified src/algebra/group/basic.lean
- \- *lemma* add_eq_of_eq_sub
- \- *lemma* add_sub
- \- *lemma* add_sub_add_right_eq_sub
- \- *lemma* add_sub_assoc
- \- *lemma* add_sub_cancel
- \+ *theorem* div_div_assoc_swap
- \+ *lemma* div_div_div_cancel_right'
- \+ *theorem* div_eq_iff_eq_mul
- \+ *lemma* div_eq_of_eq_mul''
- \+ *theorem* div_eq_one
- \+ *theorem* div_eq_self
- \+ *lemma* div_inv_eq_mul
- \+ *lemma* div_left_inj
- \+ *lemma* div_mul_div_cancel'
- \+ *lemma* div_mul_eq_div_div_swap
- \+ *theorem* div_ne_one
- \+ *lemma* div_ne_one_of_ne
- \+ *lemma* div_right_inj
- \+ *lemma* div_self'
- \- *lemma* eq_add_of_sub_eq
- \+ *theorem* eq_div_iff_mul_eq'
- \+ *lemma* eq_div_of_mul_eq'
- \+ *theorem* eq_iff_eq_of_div_eq_div
- \- *theorem* eq_iff_eq_of_sub_eq_sub
- \+ *lemma* eq_mul_of_div_eq
- \+ *lemma* eq_of_div_eq_one'
- \- *lemma* eq_of_sub_eq_zero
- \- *theorem* eq_sub_iff_add_eq
- \- *lemma* eq_sub_of_add_eq
- \- *theorem* left_inverse_add_left_sub
- \- *theorem* left_inverse_add_right_neg_add
- \+ *theorem* left_inverse_div_mul_left
- \+ *theorem* left_inverse_inv_mul_mul_right
- \+ *theorem* left_inverse_mul_left_div
- \+ *theorem* left_inverse_mul_right_inv_mul
- \- *theorem* left_inverse_neg_add_add_right
- \- *theorem* left_inverse_sub_add_left
- \+ *lemma* mul_div
- \+/\- *lemma* mul_div_assoc
- \+ *lemma* mul_div_cancel''
- \+ *lemma* mul_div_mul_right_eq_div
- \+ *lemma* mul_eq_of_eq_div
- \- *lemma* sub_add_eq_sub_sub_swap
- \- *lemma* sub_add_sub_cancel
- \- *theorem* sub_eq_iff_eq_add
- \- *lemma* sub_eq_of_eq_add
- \- *theorem* sub_eq_self
- \- *theorem* sub_eq_zero
- \- *lemma* sub_left_inj
- \- *theorem* sub_ne_zero
- \- *lemma* sub_ne_zero_of_ne
- \- *lemma* sub_neg_eq_add
- \- *lemma* sub_right_inj
- \- *lemma* sub_self
- \- *theorem* sub_sub_assoc_swap
- \- *lemma* sub_sub_sub_cancel_right



## [2021-11-30 13:24:44](https://github.com/leanprover-community/mathlib/commit/41fa32b)
feat(data/nat/pairing): add an `equiv` version of `nat.mkpair`/`nat.unpair` ([#10520](https://github.com/leanprover-community/mathlib/pull/10520))
#### Estimated changes
Modified src/data/nat/pairing.lean
- \+ *lemma* nat.mkpair_eq_mkpair
- \+ *def* nat.mkpair_equiv



## [2021-11-30 13:24:43](https://github.com/leanprover-community/mathlib/commit/af5c778)
feat(topology/[continuous_function, path_connected]): add bundled versions of prod_mk and prod_map ([#10512](https://github.com/leanprover-community/mathlib/pull/10512))
I also added a definition for pointwise addition of paths, but I'm not sure it would be really useful in general (my use case is the Sphere eversion project, where I need to add together two paths living in complement subspaces of a real TVS).
#### Estimated changes
Modified src/topology/continuous_function/basic.lean
- \+ *def* continuous_map.prod_map
- \+ *def* continuous_map.prod_mk

Modified src/topology/path_connected.lean




## [2021-11-30 13:24:41](https://github.com/leanprover-community/mathlib/commit/4d90ff9)
feat(topology/connected): Connectedness in sum and sigma type ([#10511](https://github.com/leanprover-community/mathlib/pull/10511))
This provides the `compact_space` and `totally_disconnected_space` instances for `α ⊕ β` and `Σ i, π i`.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.sigma.univ

Modified src/topology/connected.lean
- \+/\- *theorem* is_connected_univ_pi
- \+/\- *theorem* is_preconnected_univ_pi
- \+ *lemma* sigma.is_connected_iff
- \+ *lemma* sigma.is_preconnected_iff
- \+ *lemma* sum.is_connected_iff
- \+ *lemma* sum.is_preconnected_iff

Modified src/topology/constructions.lean
- \+ *lemma* is_open_sigma_fst_preimage

Modified src/topology/subset_properties.lean
- \+ *lemma* clopen_range_sigma_mk



## [2021-11-30 13:24:39](https://github.com/leanprover-community/mathlib/commit/7356269)
feat(linear_algebra/affine_space/basis): upgrade `affine_basis.coords` to an affine map ([#10452](https://github.com/leanprover-community/mathlib/pull/10452))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/affine_space/basis.lean
- \+ *lemma* affine_basis.coe_linear



## [2021-11-30 12:39:15](https://github.com/leanprover-community/mathlib/commit/35574bb)
fix(*): replace "the the" by "the" ([#10548](https://github.com/leanprover-community/mathlib/pull/10548))
#### Estimated changes
Modified src/linear_algebra/affine_space/basis.lean


Modified src/topology/sheaves/sheaf_condition/sites.lean




## [2021-11-30 11:49:06](https://github.com/leanprover-community/mathlib/commit/1077f34)
feat(algebraic_geometry): Generalized basic open for arbitrary sections ([#10515](https://github.com/leanprover-community/mathlib/pull/10515))
#### Estimated changes
Modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.preimage_basic_open

Modified src/algebraic_geometry/ringed_space.lean
- \+/\- *def* algebraic_geometry.RingedSpace.basic_open
- \+ *lemma* algebraic_geometry.RingedSpace.basic_open_res
- \+ *lemma* algebraic_geometry.RingedSpace.basic_open_subset
- \+/\- *lemma* algebraic_geometry.RingedSpace.is_unit_res_basic_open
- \+/\- *lemma* algebraic_geometry.RingedSpace.mem_basic_open



## [2021-11-30 10:08:21](https://github.com/leanprover-community/mathlib/commit/6102d77)
feat(group_theory/submonoid/pointwise): pointwise inverse of a submonoid ([#10451](https://github.com/leanprover-community/mathlib/pull/10451))
This also adds `order_iso.map_{supr,infi,Sup,Inf}` which are used here to provide some short proofs.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* set.Inter_inv
- \+ *lemma* set.Union_inv

Modified src/group_theory/submonoid/pointwise.lean
- \+ *lemma* submonoid.closure_inv
- \+ *lemma* submonoid.coe_inv
- \+ *lemma* submonoid.inv_bot
- \+ *lemma* submonoid.inv_inf
- \+ *lemma* submonoid.inv_infi
- \+ *lemma* submonoid.inv_le
- \+ *lemma* submonoid.inv_le_inv
- \+ *def* submonoid.inv_order_iso
- \+ *lemma* submonoid.inv_sup
- \+ *lemma* submonoid.inv_supr
- \+ *lemma* submonoid.inv_top
- \+ *lemma* submonoid.mem_inv

Modified src/order/complete_lattice.lean
- \+ *lemma* order_iso.map_Inf
- \+ *lemma* order_iso.map_Sup
- \+ *lemma* order_iso.map_infi
- \+ *lemma* order_iso.map_supr



## [2021-11-30 07:29:05](https://github.com/leanprover-community/mathlib/commit/4a9aa27)
feat(analysis/normed_space/spectrum and algebra/algebra/spectrum): prove properties of spectrum in a Banach algebra ([#10530](https://github.com/leanprover-community/mathlib/pull/10530))
Prove that the `spectrum` of an element in a Banach algebra is closed and bounded, hence compact when the scalar field is                               
proper. Compute the derivative of the `resolvent a` function in preparation for showing that the spectrum is nonempty when  the base field is ℂ. Define the `spectral_radius` and prove that it is bounded by the norm. Also rename the resolvent set to `resolvent_set` instead of `resolvent` so that it doesn't clash with the function name.
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \- *def* resolvent
- \+ *def* resolvent_set
- \- *lemma* spectrum.mem_resolvent_iff
- \- *lemma* spectrum.mem_resolvent_of_left_right_inverse
- \+ *lemma* spectrum.mem_resolvent_set_iff
- \+ *lemma* spectrum.mem_resolvent_set_of_left_right_inverse
- \+ *lemma* spectrum.resolvent_eq

Added src/analysis/normed_space/spectrum.lean
- \+ *theorem* spectrum.has_deriv_at_resolvent
- \+ *lemma* spectrum.is_bounded
- \+ *lemma* spectrum.is_closed
- \+ *theorem* spectrum.is_compact
- \+ *lemma* spectrum.is_open_resolvent_set
- \+ *lemma* spectrum.mem_resolvent_of_norm_lt
- \+ *lemma* spectrum.norm_le_norm_of_mem
- \+ *theorem* spectrum.spectral_radius_le_nnnorm
- \+ *lemma* spectrum.subset_closed_ball_norm



## [2021-11-30 06:50:40](https://github.com/leanprover-community/mathlib/commit/f11d505)
feat(category_theory/sites/compatible_*): Compatibility of plus and sheafification with composition. ([#10510](https://github.com/leanprover-community/mathlib/pull/10510))
Compatibility of sheafification with composition. This will be used later to obtain adjunctions between categories of sheaves.
#### Estimated changes
Added src/category_theory/sites/compatible_plus.lean
- \+ *def* category_theory.grothendieck_topology.diagram_comp_iso
- \+ *lemma* category_theory.grothendieck_topology.diagram_comp_iso_hom_ι
- \+ *def* category_theory.grothendieck_topology.plus_comp_iso
- \+ *lemma* category_theory.grothendieck_topology.plus_comp_iso_inv_eq_plus_lift
- \+ *lemma* category_theory.grothendieck_topology.plus_comp_iso_whisker_left
- \+ *lemma* category_theory.grothendieck_topology.plus_comp_iso_whisker_right
- \+ *def* category_theory.grothendieck_topology.plus_functor_whisker_left_iso
- \+ *def* category_theory.grothendieck_topology.plus_functor_whisker_right_iso
- \+ *lemma* category_theory.grothendieck_topology.to_plus_comp_plus_comp_iso_inv
- \+ *lemma* category_theory.grothendieck_topology.whisker_right_to_plus_comp_plus_comp_iso_hom
- \+ *lemma* category_theory.grothendieck_topology.ι_plus_comp_iso_hom

Added src/category_theory/sites/compatible_sheafification.lean
- \+ *def* category_theory.grothendieck_topology.sheafification_whisker_left_iso
- \+ *lemma* category_theory.grothendieck_topology.sheafification_whisker_left_iso_hom_app
- \+ *lemma* category_theory.grothendieck_topology.sheafification_whisker_left_iso_inv_app
- \+ *def* category_theory.grothendieck_topology.sheafification_whisker_right_iso
- \+ *lemma* category_theory.grothendieck_topology.sheafification_whisker_right_iso_hom_app
- \+ *lemma* category_theory.grothendieck_topology.sheafification_whisker_right_iso_inv_app
- \+ *def* category_theory.grothendieck_topology.sheafify_comp_iso
- \+ *lemma* category_theory.grothendieck_topology.sheafify_comp_iso_inv_eq_sheafify_lift
- \+ *lemma* category_theory.grothendieck_topology.to_sheafify_comp_sheafify_comp_iso_inv
- \+ *lemma* category_theory.grothendieck_topology.whisker_right_to_sheafify_sheafify_comp_iso_hom

Modified src/category_theory/sites/plus.lean
- \+ *def* category_theory.grothendieck_topology.diagram_nat_trans
- \+ *lemma* category_theory.grothendieck_topology.diagram_nat_trans_comp
- \+ *lemma* category_theory.grothendieck_topology.diagram_nat_trans_id
- \+ *lemma* category_theory.grothendieck_topology.plus_map_comp
- \+ *lemma* category_theory.grothendieck_topology.plus_map_id
- \+ *lemma* category_theory.grothendieck_topology.to_plus_naturality

Modified src/category_theory/sites/sheafification.lean
- \+ *lemma* category_theory.grothendieck_topology.sheafification_map_sheafify_lift
- \+ *lemma* category_theory.grothendieck_topology.sheafify_is_sheaf

Modified src/category_theory/sites/whiskering.lean
- \+ *lemma* category_theory.grothendieck_topology.cover.multicospan_comp_hom_inv_left
- \+ *lemma* category_theory.grothendieck_topology.cover.multicospan_comp_hom_inv_right



## [2021-11-30 02:52:47](https://github.com/leanprover-community/mathlib/commit/396351b)
chore(scripts): update nolints.txt ([#10545](https://github.com/leanprover-community/mathlib/pull/10545))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-11-29 21:29:13](https://github.com/leanprover-community/mathlib/commit/04fc415)
feat(algebra/char_p/two): lemmas about characteristic two ([#10442](https://github.com/leanprover-community/mathlib/pull/10442))
#### Estimated changes
Modified src/algebra/char_p/basic.lean
- \+ *lemma* list_sum_pow_char
- \+ *lemma* multiset_sum_pow_char
- \+ *lemma* sum_pow_char

Added src/algebra/char_p/two.lean
- \+ *lemma* char_two.add_mul_self
- \+ *lemma* char_two.add_self_eq_zero
- \+ *lemma* char_two.add_sq
- \+ *lemma* char_two.bit0_eq_zero
- \+ *lemma* char_two.bit1_eq_one
- \+ *lemma* char_two.list_sum_mul_self
- \+ *lemma* char_two.list_sum_sq
- \+ *lemma* char_two.multiset_sum_mul_self
- \+ *lemma* char_two.multiset_sum_sq
- \+ *lemma* char_two.neg_eq'
- \+ *lemma* char_two.neg_eq
- \+ *lemma* char_two.sub_eq_add'
- \+ *lemma* char_two.sub_eq_add
- \+ *lemma* char_two.sum_mul_self
- \+ *lemma* char_two.sum_sq
- \+ *lemma* char_two.two_eq_zero



## [2021-11-29 19:42:43](https://github.com/leanprover-community/mathlib/commit/f798f22)
refactor(order/filter/bases): drop `p` in `has_antitone_basis` ([#10499](https://github.com/leanprover-community/mathlib/pull/10499))
We never use `has_antitone_basis` for `p ≠ λ _, true` in `mathlib`.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* filter.subseq_tendsto_of_ne_bot

Modified src/order/filter/bases.lean
- \- *lemma* filter.exists_antitone_eq_infi_principal
- \+/\- *structure* filter.has_antitone_basis
- \+/\- *structure* filter.is_antitone_basis

Modified src/topology/G_delta.lean


Modified src/topology/sequences.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean




## [2021-11-29 17:49:24](https://github.com/leanprover-community/mathlib/commit/da6aceb)
chore(order): fix-ups after [#9891](https://github.com/leanprover-community/mathlib/pull/9891) ([#10538](https://github.com/leanprover-community/mathlib/pull/10538))
#### Estimated changes
Modified src/combinatorics/simple_graph/subgraph.lean


Modified src/data/fin/basic.lean


Modified src/order/bounded_order.lean
- \+/\- *lemma* inf_eq_bot_iff_le_compl

Modified src/order/filter/germ.lean




## [2021-11-29 17:49:23](https://github.com/leanprover-community/mathlib/commit/7545909)
chore(logic/function): allow `Sort*` in `function.inv_fun` ([#10526](https://github.com/leanprover-community/mathlib/pull/10526))
#### Estimated changes
Modified src/logic/function/basic.lean
- \+/\- *theorem* function.inv_fun_eq
- \+/\- *lemma* function.inv_fun_neg



## [2021-11-29 17:49:21](https://github.com/leanprover-community/mathlib/commit/3ac9ae7)
chore(data/stream): dedup `take` and `approx` ([#10525](https://github.com/leanprover-community/mathlib/pull/10525))
`stream.take` and `stream.approx` were propositionally equal. Merge
them into one function `stream.take`; the definition comes from the old `stream.approx`.
#### Estimated changes
Modified src/data/stream/basic.lean
- \- *lemma* stream.length_take

Modified src/data/stream/defs.lean
- \- *def* stream.approx
- \+/\- *def* stream.take

Modified src/data/stream/init.lean
- \- *theorem* stream.append_approx_drop
- \+ *theorem* stream.append_take_drop
- \- *theorem* stream.approx_succ
- \- *theorem* stream.approx_zero
- \+ *theorem* stream.length_take
- \- *theorem* stream.nth_approx
- \+/\- *theorem* stream.nth_inits
- \+ *theorem* stream.nth_take_succ
- \+ *theorem* stream.take_succ
- \+/\- *theorem* stream.take_theorem
- \+ *theorem* stream.take_zero



## [2021-11-29 17:49:20](https://github.com/leanprover-community/mathlib/commit/bc4ed5c)
chore(*): cleanup unneeded uses of by_cases across the library ([#10523](https://github.com/leanprover-community/mathlib/pull/10523))
Many proofs in the library do case splits but then never use the introduced assumption in one of the cases, meaning the case split can be removed and replaced with the general argument.
Its easy to either accidentally introduce these more complicated than needed arguments when writing proofs, or in some cases presumably refactors made assumptions unnecessary, we golf / simplify several of these to simplify these proofs.
Similar things happen for `split_ifs` and explicit `if ... then` proofs.
Rather remarkably the changes to `uniformly_extend_spec` make the separated space assumption unnecessary too, and removing this removes this assumption from around 10 other lemmas in the library too.
Some more random golfs were added in the review process
Found with a work in progress linter.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/fintype/basic.lean


Modified src/data/list/intervals.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/rbtree/insert.lean


Modified src/deprecated/subfield.lean


Modified src/field_theory/ratfunc.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/concrete_cycle.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/list.lean


Modified src/group_theory/perm/option.lean


Modified src/linear_algebra/matrix/transvection.lean


Modified src/linear_algebra/matrix/zpow.lean


Modified src/linear_algebra/trace.lean


Modified src/measure_theory/integral/set_integral.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/order/compactly_generated.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/polynomial/cyclotomic.lean


Modified src/set_theory/ordinal_arithmetic.lean


Modified src/topology/uniform_space/abstract_completion.lean


Modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* uniform_space.completion.extension_coe

Modified src/topology/uniform_space/uniform_embedding.lean




## [2021-11-29 17:49:19](https://github.com/leanprover-community/mathlib/commit/5601833)
chore(*): a few facts about `pprod` ([#10519](https://github.com/leanprover-community/mathlib/pull/10519))
Add `equiv.pprod_equiv_prod` and `function.embedding.pprod_map`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.pprod_equiv_prod

Modified src/data/pprod.lean
- \+ *lemma* function.injective.pprod_map

Modified src/logic/embedding.lean
- \+ *def* function.embedding.pprod_map



## [2021-11-29 17:49:18](https://github.com/leanprover-community/mathlib/commit/be48f95)
refactor(algebra.order.group): Convert abs_eq_sup_neg to multiplicative form ([#10505](https://github.com/leanprover-community/mathlib/pull/10505))
refactor(algebra.order.group): Convert abs_eq_sup_neg to multiplicative form
#### Estimated changes
Modified src/algebra/order/group.lean
- \+ *lemma* abs_eq_sup_inv
- \- *lemma* abs_eq_sup_neg



## [2021-11-29 17:49:17](https://github.com/leanprover-community/mathlib/commit/2ed7c0f)
doc(field_theory/galois): add comment that separable extensions are a… ([#10500](https://github.com/leanprover-community/mathlib/pull/10500))
…lgebraic
I teach my students that a Galois extension is algebraic, normal and separable, and was
just taken aback when I read the mathlib definition which omits "algebraic". Apparently
there are two conventions for the definition of separability, one implying algebraic and the other not:
https://en.wikipedia.org/wiki/Separable_extension#Separability_of_transcendental_extensions .
Right now we have separability implies algebraic in mathlib so mathematically we're fine; I just
add a note to clarify what's going on. In particular if we act on the TODO in
the separability definition, we may (perhaps unwittingly) break the definition of
`is_galois`; hopefully this note lessens the chance that this happens.
#### Estimated changes
Modified src/field_theory/galois.lean


Modified src/field_theory/separable.lean




## [2021-11-29 17:49:15](https://github.com/leanprover-community/mathlib/commit/fcbe714)
refactor(data/nat/fib): use `nat.iterate` ([#10489](https://github.com/leanprover-community/mathlib/pull/10489))
The main drawback of the new definition is that `fib (n + 2) = fib n + fib (n + 1)` is no longer `rfl` but I think that we should have one API for iterates.
See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60nat.2Eiterate.60.20vs.20.60stream.2Eiterate.60
#### Estimated changes
Modified archive/imo/imo1981_q3.lean


Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/data/nat/fib.lean
- \+/\- *def* nat.fib
- \+ *lemma* nat.fib_add_two
- \+/\- *lemma* nat.fib_le_fib_succ
- \+ *lemma* nat.fib_lt_fib_succ
- \- *lemma* nat.fib_succ_succ

Modified src/data/nat/gcd.lean
- \+ *theorem* nat.coprime_add_self_left
- \+ *theorem* nat.coprime_add_self_right
- \+ *theorem* nat.coprime_self_add_left
- \+ *theorem* nat.coprime_self_add_right
- \+/\- *lemma* nat.gcd_add_mul_self
- \+ *lemma* nat.gcd_add_self_left
- \+ *lemma* nat.gcd_add_self_right
- \+/\- *theorem* nat.gcd_eq_zero_iff
- \+ *lemma* nat.gcd_self_add_left
- \+ *lemma* nat.gcd_self_add_right

Modified src/data/real/golden_ratio.lean




## [2021-11-29 17:11:51](https://github.com/leanprover-community/mathlib/commit/b849b3c)
feat(number_theory/padics/padic_norm): prime powers in divisors ([#10481](https://github.com/leanprover-community/mathlib/pull/10481))
#### Estimated changes
Modified src/number_theory/padics/padic_norm.lean
- \+ *lemma* range_pow_padic_val_nat_subset_divisors'
- \+ *lemma* range_pow_padic_val_nat_subset_divisors



## [2021-11-29 09:57:02](https://github.com/leanprover-community/mathlib/commit/957fa4b)
feat(order/locally_finite): `with_top α`/`with_bot α` are locally finite orders ([#10202](https://github.com/leanprover-community/mathlib/pull/10202))
This provides the two instances `locally_finite_order (with_top α)` and `locally_finite_order (with_bot α)`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.mem_cons_self

Modified src/data/option/defs.lean
- \+ *lemma* option.mem_iff

Modified src/logic/embedding.lean
- \+ *def* function.embedding.coe_option
- \+ *def* function.embedding.coe_with_top

Modified src/order/locally_finite.lean
- \+ *lemma* with_bot.Icc_bot_coe
- \+ *lemma* with_bot.Icc_coe_coe
- \+ *lemma* with_bot.Ico_bot_coe
- \+ *lemma* with_bot.Ico_coe_coe
- \+ *lemma* with_bot.Ioc_bot_coe
- \+ *lemma* with_bot.Ioc_coe_coe
- \+ *lemma* with_bot.Ioo_bot_coe
- \+ *lemma* with_bot.Ioo_coe_coe
- \+ *lemma* with_top.Icc_coe_coe
- \+ *lemma* with_top.Icc_coe_top
- \+ *lemma* with_top.Ico_coe_coe
- \+ *lemma* with_top.Ico_coe_top
- \+ *lemma* with_top.Ioc_coe_coe
- \+ *lemma* with_top.Ioc_coe_top
- \+ *lemma* with_top.Ioo_coe_coe
- \+ *lemma* with_top.Ioo_coe_top



## [2021-11-29 06:52:12](https://github.com/leanprover-community/mathlib/commit/202ca0b)
feat(*/is_R_or_C): deduplicate ([#10522](https://github.com/leanprover-community/mathlib/pull/10522))
I noticed that the same argument, that in a normed space over `is_R_or_C` an element can be normalized, appears in a couple of different places in the library.  I have deduplicated and placed it in `analysis/normed_space/is_R_or_C`.
#### Estimated changes
Modified src/analysis/inner_product_space/projection.lean


Modified src/analysis/normed_space/is_R_or_C.lean
- \+/\- *lemma* linear_map.bound_of_ball_bound
- \+ *lemma* norm_smul_inv_norm'
- \+ *lemma* norm_smul_inv_norm

Modified src/data/complex/is_R_or_C.lean
- \- *lemma* norm_smul_inv_norm



## [2021-11-29 06:52:11](https://github.com/leanprover-community/mathlib/commit/a53da16)
feat(data/int/basic): `nat_abs_dvd_iff_dvd` ([#10469](https://github.com/leanprover-community/mathlib/pull/10469))
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.nat_abs_dvd_iff_dvd



## [2021-11-29 06:04:28](https://github.com/leanprover-community/mathlib/commit/50cc57b)
chore(category_theory/limits/shapes/wide_pullbacks): speed up `wide_cospan` ([#10535](https://github.com/leanprover-community/mathlib/pull/10535))
#### Estimated changes
Modified src/category_theory/limits/shapes/wide_pullbacks.lean




## [2021-11-29 01:36:13](https://github.com/leanprover-community/mathlib/commit/16daabf)
chore(algebra/group_power): golf a few proofs ([#10498](https://github.com/leanprover-community/mathlib/pull/10498))
* move `pow_lt_pow_of_lt_one` and `pow_lt_pow_iff_of_lt_one` from
  `algebra.group_power.lemmas` to `algebra.group_power.order`;
* add `strict_anti_pow`, use it to golf the proofs of the two lemmas
  above;
* golf a few other proofs;
* add `nnreal.exists_pow_lt_of_lt_one`.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \- *lemma* pow_lt_pow_iff_of_lt_one
- \- *lemma* pow_lt_pow_of_lt_one

Modified src/algebra/group_power/order.lean
- \+/\- *lemma* one_lt_pow
- \+ *lemma* pow_lt_pow_iff_of_lt_one
- \+ *lemma* pow_lt_pow_of_lt_one
- \+ *lemma* strict_anti_pow

Modified src/algebra/order/ring.lean


Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.exists_pow_lt_of_lt_one



## [2021-11-28 23:50:39](https://github.com/leanprover-community/mathlib/commit/77ba0c4)
chore(logic): allow `Sort*` args in 2 lemmas ([#10517](https://github.com/leanprover-community/mathlib/pull/10517))
#### Estimated changes
Modified src/logic/basic.lean
- \+/\- *lemma* congr_arg2

Modified src/logic/embedding.lean
- \+/\- *lemma* function.embedding.apply_eq_iff_eq



## [2021-11-28 23:50:38](https://github.com/leanprover-community/mathlib/commit/c058607)
chore(order): generalize `min_top_left` ([#10486](https://github.com/leanprover-community/mathlib/pull/10486))
As well as its relative `min_top_right`.
Also provide `max_bot_(left|right)`.
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \- *lemma* min_top_left
- \- *lemma* min_top_right

Modified src/order/bounded_order.lean
- \+ *lemma* max_bot_left
- \+ *lemma* max_bot_right
- \+ *lemma* min_top_left
- \+ *lemma* min_top_right



## [2021-11-28 23:50:37](https://github.com/leanprover-community/mathlib/commit/43519fc)
feat(tactic/lint/misc): unused arguments checks for more sorry's ([#10431](https://github.com/leanprover-community/mathlib/pull/10431))
* The `unused_arguments` linter now checks whether `sorry` occurs in any of the `_proof_i` declarations and will not raise an error if this is the case
* Two minor changes: `open tactic` in all of `meta.expr` and fix a typo.
* I cannot add a test without adding a `sorry` to the test suite, but this succeeds without linter warning:
```lean
import tactic.lint
/-- dummy doc -/
def one (h : 0 < 1) : {n : ℕ // 0 < n} := ⟨1, sorry⟩
#lint
```
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/core.lean


Modified src/tactic/lint/misc.lean




## [2021-11-28 22:06:26](https://github.com/leanprover-community/mathlib/commit/dfa98e0)
chore(algebra/opposites): split out lemmas about rings and groups ([#10457](https://github.com/leanprover-community/mathlib/pull/10457))
All these lemmas are just moved.
The advantage of this is that `algebra.opposites` becomes a much lighter-weight import, allowing us to use the `has_mul` and `has_scalar` instance on opposite types earlier in the import hierarchy.
It also matches how we structure the instances on `prod` and `pi` types.
This follows on from [#10383](https://github.com/leanprover-community/mathlib/pull/10383)
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/algebra/field/opposite.lean


Added src/algebra/group/opposite.lean
- \+ *def* add_equiv.op
- \+ *def* add_equiv.unop
- \+ *def* add_monoid_hom.op
- \+ *lemma* add_monoid_hom.op_ext
- \+ *def* add_monoid_hom.unop
- \+ *def* monoid_hom.op
- \+ *def* monoid_hom.to_opposite
- \+ *def* monoid_hom.unop
- \+ *def* mul_equiv.inv'
- \+ *def* mul_equiv.op
- \+ *def* mul_equiv.unop
- \+ *lemma* mul_opposite.commute.op
- \+ *lemma* mul_opposite.commute.unop
- \+ *lemma* mul_opposite.commute_op
- \+ *lemma* mul_opposite.commute_unop
- \+ *def* mul_opposite.op_add_equiv
- \+ *lemma* mul_opposite.op_add_equiv_to_equiv
- \+ *lemma* mul_opposite.semiconj_by.op
- \+ *lemma* mul_opposite.semiconj_by.unop
- \+ *lemma* mul_opposite.semiconj_by_op
- \+ *lemma* mul_opposite.semiconj_by_unop
- \+ *lemma* units.coe_op_equiv_symm
- \+ *lemma* units.coe_unop_op_equiv
- \+ *def* units.op_equiv

Modified src/algebra/group/prod.lean


Modified src/algebra/opposites.lean
- \- *def* add_equiv.op
- \- *def* add_equiv.unop
- \- *def* add_monoid_hom.op
- \- *lemma* add_monoid_hom.op_ext
- \- *def* add_monoid_hom.unop
- \- *def* monoid_hom.op
- \- *def* monoid_hom.to_opposite
- \- *def* monoid_hom.unop
- \- *def* mul_equiv.inv'
- \- *def* mul_equiv.op
- \- *def* mul_equiv.unop
- \- *lemma* mul_opposite.commute.op
- \- *lemma* mul_opposite.commute.unop
- \- *lemma* mul_opposite.commute_op
- \- *lemma* mul_opposite.commute_unop
- \- *def* mul_opposite.op_add_equiv
- \- *lemma* mul_opposite.op_add_equiv_to_equiv
- \- *lemma* mul_opposite.semiconj_by.op
- \- *lemma* mul_opposite.semiconj_by.unop
- \- *lemma* mul_opposite.semiconj_by_op
- \- *lemma* mul_opposite.semiconj_by_unop
- \- *def* ring_hom.op
- \- *def* ring_hom.to_opposite
- \- *def* ring_hom.unop
- \- *lemma* units.coe_op_equiv_symm
- \- *lemma* units.coe_unop_op_equiv
- \- *def* units.op_equiv

Modified src/algebra/quaternion.lean


Added src/algebra/ring/opposite.lean
- \+ *def* ring_hom.op
- \+ *def* ring_hom.to_opposite
- \+ *def* ring_hom.unop

Modified src/algebra/smul_with_zero.lean


Modified src/data/equiv/ring.lean


Modified src/group_theory/group_action/opposite.lean


Modified src/ring_theory/ring_invo.lean




## [2021-11-28 20:23:10](https://github.com/leanprover-community/mathlib/commit/f684721)
chore(data/nat/prime): `fact (2.prime)` ([#10441](https://github.com/leanprover-community/mathlib/pull/10441))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.fact_prime_three
- \+ *lemma* nat.fact_prime_two

Modified src/logic/basic.lean


Modified src/number_theory/quadratic_reciprocity.lean
- \- *lemma* zmod.fact_prime_two



## [2021-11-28 19:36:10](https://github.com/leanprover-community/mathlib/commit/a2e6bf8)
chore(algebraic_topology/cech_nerve): An attempt to speed up the proofs... ([#10521](https://github.com/leanprover-community/mathlib/pull/10521))
Let's hope this works!
See [zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2310312.20timeouts.20in.20cech_nerve/near/262587999)
#### Estimated changes
Modified src/algebraic_topology/cech_nerve.lean
- \+ *def* category_theory.arrow.map_augmented_cech_conerve
- \+ *def* category_theory.arrow.map_augmented_cech_nerve
- \+ *def* category_theory.arrow.map_cech_conerve
- \+ *def* category_theory.arrow.map_cech_nerve



## [2021-11-28 07:21:28](https://github.com/leanprover-community/mathlib/commit/044f532)
chore(analysis/normed_space/hahn_banach): remove `norm'` ([#10527](https://github.com/leanprover-community/mathlib/pull/10527))
For a normed space over `ℝ`-algebra `𝕜`, `norm'` is currently defined to be `algebra_map ℝ 𝕜 ∥x∥`.  I believe this was introduced before the `is_R_or_C` construct (including the coercion from `ℝ` to `𝕜` for `[is_R_or_C 𝕜]`) joined mathlib.  Now that we have these things, it's easy to just say `(∥x∥ : 𝕜)` instead of `norm' 𝕜 ∥x∥`, so I don't really think `norm'` needs to exist any more.
(In principle, `norm'` is more general, since it works for all `ℝ`-algebras `𝕜` rather than just `[is_R_or_C 𝕜]`.  But I can only really think of applications in the`is_R_or_C` case, and that's the only way it's used in the library.)
#### Estimated changes
Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/hahn_banach.lean
- \+/\- *lemma* coord_norm'
- \+/\- *theorem* exists_dual_vector
- \- *lemma* norm'_def
- \- *lemma* norm'_eq_zero_iff
- \- *lemma* norm_norm'

Modified src/measure_theory/function/ae_eq_of_integral.lean




## [2021-11-28 07:21:27](https://github.com/leanprover-community/mathlib/commit/099fb0f)
feat(data/nat/prime): lemma eq_of_eq_count_factors ([#10493](https://github.com/leanprover-community/mathlib/pull/10493))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.eq_of_count_factors_eq
- \+ *lemma* nat.eq_of_perm_factors



## [2021-11-28 06:12:10](https://github.com/leanprover-community/mathlib/commit/45d45ef)
feat(data/nat/prime): lemma count_factors_mul_of_coprime ([#10492](https://github.com/leanprover-community/mathlib/pull/10492))
Adding lemma `count_factors_mul_of_coprime` and using it to simplify the proof of `factors_count_eq_of_coprime_left`.
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.count_factors_mul_of_coprime



## [2021-11-28 03:39:40](https://github.com/leanprover-community/mathlib/commit/b1f9067)
feat(group_theory/group_action/units): add a `mul_distrib_mul_action` instance ([#10480](https://github.com/leanprover-community/mathlib/pull/10480))
This doesn't add any new "data" instances, it just shows the existing instance satisfies stronger properties with stronger assumptions.
#### Estimated changes
Modified src/group_theory/group_action/units.lean




## [2021-11-27 09:46:17](https://github.com/leanprover-community/mathlib/commit/b8af491)
feat(category_theory/sites/whiskering): Functors between sheaf categories induced by compositiion ([#10496](https://github.com/leanprover-community/mathlib/pull/10496))
We construct the functor `Sheaf J A` to `Sheaf J B` induced by a functor `A` to `B` which preserves the appropriate limits.
#### Estimated changes
Added src/category_theory/sites/whiskering.lean
- \+ *def* category_theory.Sheaf_compose
- \+ *def* category_theory.Sheaf_compose_map
- \+ *lemma* category_theory.Sheaf_compose_map_app
- \+ *lemma* category_theory.Sheaf_compose_map_app_app
- \+ *lemma* category_theory.Sheaf_compose_map_comp
- \+ *lemma* category_theory.Sheaf_compose_map_id
- \+ *lemma* category_theory.Sheaf_compose_map_to_presheaf
- \+ *lemma* category_theory.Sheaf_compose_obj_to_presheaf
- \+ *def* category_theory.grothendieck_topology.cover.map_multifork
- \+ *def* category_theory.grothendieck_topology.cover.multicospan_comp
- \+ *lemma* category_theory.grothendieck_topology.cover.multicospan_comp_app_left
- \+ *lemma* category_theory.grothendieck_topology.cover.multicospan_comp_app_right
- \+ *lemma* category_theory.grothendieck_topology.cover.multicospan_comp_hom_app_left
- \+ *lemma* category_theory.grothendieck_topology.cover.multicospan_comp_hom_app_right
- \+ *lemma* category_theory.presheaf.is_sheaf.comp



## [2021-11-27 08:42:32](https://github.com/leanprover-community/mathlib/commit/fcb3790)
feat(topology/algebra/matrix): the determinant is a continuous map ([#10503](https://github.com/leanprover-community/mathlib/pull/10503))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* matrix.coe_det_is_empty

Added src/topology/algebra/matrix.lean
- \+ *lemma* continuous_det

Modified src/topology/constructions.lean
- \+ *lemma* continuous_apply_apply



## [2021-11-27 07:02:21](https://github.com/leanprover-community/mathlib/commit/d36a67c)
feat(ring_theory/euclidean_domain): generalize lemmas to PIDs ([#10324](https://github.com/leanprover-community/mathlib/pull/10324))
This moves the existing lemmas to the `euclidean_domain` namespace.
#### Estimated changes
Modified src/data/polynomial/field_division.lean


Modified src/field_theory/separable.lean


Modified src/ring_theory/euclidean_domain.lean
- \- *theorem* dvd_or_coprime
- \+ *theorem* euclidean_domain.dvd_or_coprime
- \+ *theorem* euclidean_domain.gcd_is_unit_iff
- \+ *def* euclidean_domain.gcd_monoid
- \+ *theorem* euclidean_domain.is_coprime_of_dvd
- \+ *theorem* euclidean_domain.span_gcd
- \- *theorem* gcd_is_unit_iff
- \- *theorem* is_coprime_of_dvd
- \- *theorem* span_gcd

Modified src/ring_theory/principal_ideal_domain.lean
- \+ *theorem* dvd_or_coprime
- \+ *theorem* gcd_is_unit_iff
- \+ *theorem* is_coprime_of_dvd
- \+ *theorem* span_gcd



## [2021-11-27 02:49:59](https://github.com/leanprover-community/mathlib/commit/150b217)
chore(scripts): update nolints.txt ([#10513](https://github.com/leanprover-community/mathlib/pull/10513))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-11-26 23:08:10](https://github.com/leanprover-community/mathlib/commit/7a19aa1)
feat(group_theory/order_of_element): linear ordered rings ([#10473](https://github.com/leanprover-community/mathlib/pull/10473))
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* linear_ordered_ring.order_of_le_two
- \+ *lemma* order_of_abs_ne_one
- \+ *lemma* order_of_eq_zero_iff'



## [2021-11-26 21:40:36](https://github.com/leanprover-community/mathlib/commit/7348f1b)
Adding a matching TODO back ([#10506](https://github.com/leanprover-community/mathlib/pull/10506))
Because we were careless and removed it too early:
https://github.com/leanprover-community/mathlib/pull/10210#discussion_r757640946
#### Estimated changes
Modified src/combinatorics/simple_graph/matching.lean




## [2021-11-26 17:50:35](https://github.com/leanprover-community/mathlib/commit/deb5692)
refactor(combinatorics/simple_graph): use subgraphs to represent matchings ([#10210](https://github.com/leanprover-community/mathlib/pull/10210))
#### Estimated changes
Modified docs/overview.yaml


Modified src/combinatorics/simple_graph/matching.lean
- \- *def* simple_graph.matching.is_perfect
- \- *lemma* simple_graph.matching.is_perfect_iff
- \- *def* simple_graph.matching.support
- \- *structure* simple_graph.matching
- \+ *lemma* simple_graph.subgraph.is_matching.support_eq_verts
- \+ *def* simple_graph.subgraph.is_matching
- \+ *def* simple_graph.subgraph.is_perfect_matching
- \+ *lemma* simple_graph.subgraph.is_perfect_matching_iff

Modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* simple_graph.subgraph.is_spanning_iff
- \+ *lemma* simple_graph.subgraph.mem_support
- \+ *def* simple_graph.subgraph.support
- \+ *lemma* simple_graph.subgraph.support_mono
- \+ *lemma* simple_graph.subgraph.support_subset_verts



## [2021-11-26 16:20:00](https://github.com/leanprover-community/mathlib/commit/dabb58b)
chore(algebra/module/pi): split out `group_theory/group_action/pi` to match `group_theory/group_action/prod` ([#10485](https://github.com/leanprover-community/mathlib/pull/10485))
These declarations are copied without modification.
#### Estimated changes
Modified src/algebra/module/pi.lean
- \- *lemma* function.extend_smul
- \- *lemma* function.update_smul
- \- *lemma* pi.has_faithful_scalar_at
- \- *lemma* pi.single_smul'
- \- *lemma* pi.single_smul
- \- *lemma* pi.single_smul₀
- \- *lemma* pi.smul_apply'
- \- *lemma* pi.smul_apply
- \- *lemma* pi.smul_def
- \- *lemma* set.piecewise_smul

Modified src/data/fin/vec_notation.lean


Added src/group_theory/group_action/pi.lean
- \+ *lemma* function.extend_smul
- \+ *lemma* function.update_smul
- \+ *lemma* pi.has_faithful_scalar_at
- \+ *lemma* pi.single_smul'
- \+ *lemma* pi.single_smul
- \+ *lemma* pi.single_smul₀
- \+ *lemma* pi.smul_apply'
- \+ *lemma* pi.smul_apply
- \+ *lemma* pi.smul_def
- \+ *lemma* set.piecewise_smul



## [2021-11-26 16:19:59](https://github.com/leanprover-community/mathlib/commit/ea52ec1)
feat(ring_theory/ideal/operations): add lemmas about comap ([#10418](https://github.com/leanprover-community/mathlib/pull/10418))
This also adds `ring_hom.to_semilinear_map` and `ring_equiv.to_semilinear_equiv`.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *def* ring_hom.to_semilinear_map

Modified src/data/equiv/module.lean
- \+ *def* ring_equiv.to_semilinear_equiv

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.comap_le_map_of_inv_on
- \+ *lemma* ideal.comap_le_map_of_inverse
- \+ *lemma* ideal.map_le_comap_of_inv_on
- \+ *lemma* ideal.map_le_comap_of_inverse
- \+ *lemma* ring_hom.comap_ker



## [2021-11-26 15:44:03](https://github.com/leanprover-community/mathlib/commit/9cfa33a)
feat(algebra/lie): implement `set_like` for `lie_submodule` ([#10488](https://github.com/leanprover-community/mathlib/pull/10488))
This PR provides a `set_like` instance for `lie_submodule` and uses it to define `has_mem` and `has_le` for Lie submodules / ideals.
#### Estimated changes
Modified src/algebra/lie/submodule.lean
- \+/\- *lemma* lie_submodule.ext
- \- *lemma* lie_submodule.le_def



## [2021-11-26 12:59:28](https://github.com/leanprover-community/mathlib/commit/83bce9f)
feat(category_theory/adjunction/whiskering): Whiskering adjunctions. ([#10495](https://github.com/leanprover-community/mathlib/pull/10495))
Construct adjunctions between functor categories induced by whiskering (both left and right).
This will be used later to construct adjunctions between categories of sheaves.
#### Estimated changes
Added src/category_theory/adjunction/whiskering.lean




## [2021-11-26 11:59:16](https://github.com/leanprover-community/mathlib/commit/61e8aa8)
feat(topology/algebra/[X]): sub[X] of a topological [X] is itself a topological [X] ([#10491](https://github.com/leanprover-community/mathlib/pull/10491))
#### Estimated changes
Modified src/topology/algebra/group.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/ring.lean




## [2021-11-26 11:04:50](https://github.com/leanprover-community/mathlib/commit/36f33d0)
chore(category_theory/limits): Generalize universes for limits ([#10243](https://github.com/leanprover-community/mathlib/pull/10243))
#### Estimated changes
Modified src/algebra/category/Algebra/limits.lean
- \+/\- *def* Algebra.has_limits.limit_cone

Modified src/algebra/category/CommRing/limits.lean
- \+/\- *def* SemiRing.has_limits.limit_cone

Modified src/algebra/category/Module/limits.lean
- \+/\- *def* Module.has_limits.limit_cone

Modified src/algebra/category/Mon/limits.lean
- \+/\- *def* Mon.has_limits.limit_cone

Modified src/category_theory/category/ulift.lean
- \- *def* category_theory.ulift.down
- \+ *def* category_theory.ulift.down_functor
- \- *def* category_theory.ulift.up
- \+ *def* category_theory.ulift.up_functor
- \+ *def* category_theory.{v'

Modified src/category_theory/discrete_category.lean
- \+/\- *def* category_theory.discrete.equiv_of_equivalence
- \+/\- *def* category_theory.discrete.equivalence

Modified src/category_theory/fin_category.lean
- \+ *abbreviation* category_theory.fin_category.as_type
- \+ *abbreviation* category_theory.fin_category.obj_as_type
- \+ *def* category_theory.fin_category.obj_as_type_equiv_as_type

Modified src/category_theory/graded_object.lean


Modified src/category_theory/is_connected.lean


Modified src/category_theory/limits/comma.lean


Modified src/category_theory/limits/cones.lean
- \+/\- *def* category_theory.cocones
- \+/\- *def* category_theory.cones
- \+/\- *def* category_theory.functor.cocones
- \+/\- *def* category_theory.functor.cones
- \+/\- *def* category_theory.limits.cocone.extensions

Modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean


Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/has_limits.lean
- \+/\- *def* category_theory.limits.colim_coyoneda
- \+/\- *def* category_theory.limits.colimit.hom_iso
- \+/\- *lemma* category_theory.limits.colimit.hom_iso_hom
- \+/\- *lemma* category_theory.limits.colimit.map_post
- \+/\- *lemma* category_theory.limits.colimit.pre_post
- \+/\- *lemma* category_theory.limits.has_colimit.of_cocones_iso
- \+ *lemma* category_theory.limits.has_colimits.has_limits_of_shape
- \+ *abbreviation* category_theory.limits.has_colimits
- \+/\- *lemma* category_theory.limits.has_colimits_of_shape_of_equivalence
- \+ *lemma* category_theory.limits.has_colimits_of_size_shrink
- \+/\- *lemma* category_theory.limits.has_limit.of_cones_iso
- \+ *lemma* category_theory.limits.has_limits.has_limits_of_shape
- \+ *abbreviation* category_theory.limits.has_limits
- \+/\- *lemma* category_theory.limits.has_limits_of_shape_of_equivalence
- \+ *lemma* category_theory.limits.has_limits_of_size_shrink
- \+/\- *def* category_theory.limits.lim_yoneda
- \+/\- *def* category_theory.limits.limit.hom_iso
- \+/\- *lemma* category_theory.limits.limit.hom_iso_hom
- \+/\- *lemma* category_theory.limits.limit.map_post
- \+/\- *lemma* category_theory.limits.limit.pre_post

Modified src/category_theory/limits/is_limit.lean
- \+/\- *def* category_theory.limits.is_colimit.hom_iso
- \+/\- *lemma* category_theory.limits.is_colimit.hom_iso_hom
- \+/\- *def* category_theory.limits.is_colimit.map_cocone_equiv
- \+/\- *def* category_theory.limits.is_colimit.nat_iso
- \+/\- *def* category_theory.limits.is_colimit.of_cocone_equiv
- \+/\- *lemma* category_theory.limits.is_colimit.of_cocone_equiv_apply_desc
- \+/\- *lemma* category_theory.limits.is_colimit.of_cocone_equiv_symm_apply_desc
- \+/\- *def* category_theory.limits.is_colimit.of_faithful
- \+/\- *def* category_theory.limits.is_colimit.of_left_adjoint
- \+/\- *def* category_theory.limits.is_colimit.of_nat_iso.hom_of_cocone
- \+/\- *def* category_theory.limits.is_colimit.of_nat_iso
- \+/\- *def* category_theory.limits.is_limit.hom_iso
- \+/\- *lemma* category_theory.limits.is_limit.hom_iso_hom
- \+/\- *def* category_theory.limits.is_limit.map_cone_equiv
- \+/\- *def* category_theory.limits.is_limit.nat_iso
- \+/\- *def* category_theory.limits.is_limit.of_cone_equiv
- \+/\- *lemma* category_theory.limits.is_limit.of_cone_equiv_apply_desc
- \+/\- *lemma* category_theory.limits.is_limit.of_cone_equiv_symm_apply_desc
- \+/\- *def* category_theory.limits.is_limit.of_faithful
- \+/\- *def* category_theory.limits.is_limit.of_nat_iso.hom_of_cone
- \+/\- *def* category_theory.limits.is_limit.of_nat_iso
- \+/\- *def* category_theory.limits.is_limit.of_right_adjoint

Modified src/category_theory/limits/opposites.lean
- \+/\- *lemma* category_theory.limits.has_colimits_op_of_has_limits
- \+/\- *lemma* category_theory.limits.has_limits_op_of_has_colimits

Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves/shapes/binary_products.lean


Modified src/category_theory/limits/preserves/shapes/equalizers.lean


Modified src/category_theory/limits/preserves/shapes/pullbacks.lean


Modified src/category_theory/limits/preserves/shapes/terminal.lean


Modified src/category_theory/limits/presheaf.lean


Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *lemma* category_theory.limits.coprod.map_comp_inl_inr_codiag
- \+/\- *abbreviation* category_theory.limits.has_binary_coproducts
- \+/\- *abbreviation* category_theory.limits.has_binary_products
- \+/\- *def* category_theory.limits.pair
- \+/\- *lemma* category_theory.limits.prod.diag_map_fst_snd_comp

Modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *abbreviation* category_theory.limits.has_coequalizers
- \+/\- *abbreviation* category_theory.limits.has_equalizers

Modified src/category_theory/limits/shapes/finite_limits.lean
- \+/\- *lemma* category_theory.limits.has_finite_limits_of_has_limits

Modified src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/normal_mono.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *abbreviation* category_theory.limits.has_pullbacks
- \+/\- *abbreviation* category_theory.limits.has_pushouts

Modified src/category_theory/limits/shapes/terminal.lean
- \+/\- *abbreviation* category_theory.limits.has_initial
- \+/\- *abbreviation* category_theory.limits.has_terminal

Modified src/category_theory/limits/shapes/wide_equalizers.lean
- \+/\- *abbreviation* category_theory.limits.has_wide_coequalizers
- \+/\- *abbreviation* category_theory.limits.has_wide_equalizers

Modified src/category_theory/limits/shapes/wide_pullbacks.lean


Modified src/category_theory/monad/monadicity.lean


Modified src/category_theory/sites/limits.lean


Modified src/topology/category/Top/limits.lean
- \+/\- *lemma* Top.coequalizer_is_open_iff

Modified src/topology/sheaves/forget.lean


Modified src/topology/sheaves/sheaf_condition/sites.lean




## [2021-11-26 07:20:19](https://github.com/leanprover-community/mathlib/commit/0b9d332)
feat(data/complex/basic): `of_real_injective` ([#10464](https://github.com/leanprover-community/mathlib/pull/10464))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *theorem* complex.of_real_injective



## [2021-11-26 07:20:18](https://github.com/leanprover-community/mathlib/commit/e742fce)
feat(data/nat/prime): `nat.{eq/ne}_one_iff` ([#10463](https://github.com/leanprover-community/mathlib/pull/10463))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.eq_one_iff_not_exists_prime_dvd
- \+ *lemma* nat.ne_one_iff_exists_prime_dvd



## [2021-11-26 07:20:17](https://github.com/leanprover-community/mathlib/commit/71bc7f4)
feat(set_theory/ordinal_notation): nonote is well founded ([#10462](https://github.com/leanprover-community/mathlib/pull/10462))
#### Estimated changes
Modified src/set_theory/ordinal_notation.lean
- \+ *theorem* nonote.wf



## [2021-11-26 07:20:16](https://github.com/leanprover-community/mathlib/commit/cdb3819)
feat(algebraic_geometry): `of_restrict` is mono. ([#10460](https://github.com/leanprover-community/mathlib/pull/10460))
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean


Modified src/category_theory/adjunction/fully_faithful.lean


Modified src/topology/category/Top/opens.lean




## [2021-11-26 07:20:15](https://github.com/leanprover-community/mathlib/commit/757aa6f)
chore(data/stream): move most defs to a new file ([#10458](https://github.com/leanprover-community/mathlib/pull/10458))
#### Estimated changes
Modified src/data/stream/basic.lean
- \- *def* stream.take

Added src/data/stream/defs.lean
- \+ *def* stream.all
- \+ *def* stream.any
- \+ *def* stream.append_stream
- \+ *def* stream.apply
- \+ *def* stream.approx
- \+ *def* stream.cons
- \+ *def* stream.const
- \+ *def* stream.corec'
- \+ *def* stream.corec
- \+ *def* stream.corec_on
- \+ *def* stream.cycle
- \+ *def* stream.drop
- \+ *def* stream.even
- \+ *def* stream.head
- \+ *def* stream.inits
- \+ *def* stream.inits_core
- \+ *def* stream.interleave
- \+ *def* stream.iterate
- \+ *def* stream.map
- \+ *def* stream.nats
- \+ *def* stream.nth
- \+ *def* stream.odd
- \+ *def* stream.pure
- \+ *def* stream.tail
- \+ *def* stream.tails
- \+ *def* stream.take
- \+ *def* stream.unfolds
- \+ *def* stream.zip
- \+ *def* stream

Modified src/data/stream/init.lean
- \- *def* stream.all
- \- *def* stream.any
- \- *def* stream.append_stream
- \- *def* stream.apply
- \- *def* stream.approx
- \- *def* stream.cons
- \- *def* stream.const
- \- *def* stream.corec'
- \- *def* stream.corec
- \- *def* stream.corec_on
- \- *def* stream.cycle
- \- *def* stream.drop
- \- *def* stream.even
- \- *def* stream.head
- \- *def* stream.inits
- \- *def* stream.inits_core
- \- *def* stream.interleave
- \- *def* stream.iterate
- \- *def* stream.map
- \- *def* stream.nats
- \- *def* stream.nth
- \- *def* stream.odd
- \- *def* stream.pure
- \- *def* stream.tail
- \- *def* stream.tails
- \- *def* stream.unfolds
- \- *def* stream.zip
- \- *def* stream



## [2021-11-26 07:20:14](https://github.com/leanprover-community/mathlib/commit/3dfa349)
feat(topology/uniform_space/completion) : add injective_coe ([#10454](https://github.com/leanprover-community/mathlib/pull/10454))
#### Estimated changes
Modified src/topology/uniform_space/completion.lean
- \+ *lemma* uniform_space.completion.coe_injective



## [2021-11-26 07:20:13](https://github.com/leanprover-community/mathlib/commit/cbe1d37)
feat(ring_theory/valuation/basic): add valuation.map_zpow ([#10453](https://github.com/leanprover-community/mathlib/pull/10453))
#### Estimated changes
Modified src/ring_theory/valuation/basic.lean
- \+ *lemma* valuation.map_zpow



## [2021-11-26 07:20:12](https://github.com/leanprover-community/mathlib/commit/9249e1e)
chore(linear_algebra/affine_space/barycentric_coords): rename file `barycentric_coords` to `basis` ([#10449](https://github.com/leanprover-community/mathlib/pull/10449))
Follow up from https://github.com/leanprover-community/mathlib/pull/10320#discussion_r748936743
#### Estimated changes
Modified src/analysis/convex/combination.lean


Modified src/analysis/normed_space/add_torsor_bases.lean


Renamed src/linear_algebra/affine_space/barycentric_coords.lean to src/linear_algebra/affine_space/basis.lean




## [2021-11-26 07:20:11](https://github.com/leanprover-community/mathlib/commit/28d9a5b)
feat(data/equiv/basic): add lemmas characterising `equiv.Pi_congr` and `equiv.Pi_congr'` ([#10432](https://github.com/leanprover-community/mathlib/pull/10432))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.Pi_congr'_apply
- \+ *lemma* equiv.Pi_congr'_symm_apply_symm_apply
- \+ *lemma* equiv.Pi_congr_apply_apply
- \+ *lemma* equiv.Pi_congr_symm_apply
- \+ *lemma* equiv.coe_Pi_congr'
- \+ *lemma* equiv.coe_Pi_congr_symm



## [2021-11-26 06:45:43](https://github.com/leanprover-community/mathlib/commit/be9b96e)
feat(computablility/halting): halting problem is r.e. ([#10459](https://github.com/leanprover-community/mathlib/pull/10459))
This is a minor oversight from the original formalization, pointed out by Keji Neri.
#### Estimated changes
Modified src/computability/halting.lean
- \+ *theorem* computable_pred.computable_iff_re_compl_re'
- \+ *theorem* computable_pred.halting_problem_not_re
- \+ *theorem* computable_pred.halting_problem_re
- \+ *theorem* partrec.dom_re
- \+ *theorem* re_pred.of_eq



## [2021-11-26 02:32:10](https://github.com/leanprover-community/mathlib/commit/f55a284)
feat(topology): normal topological space with second countable topology is metrizable ([#10402](https://github.com/leanprover-community/mathlib/pull/10402))
Also prove that a regular topological space with second countable topology is a normal space.
#### Estimated changes
Modified src/logic/is_empty.lean
- \+ *lemma* function.extend_of_empty

Modified src/topology/bases.lean


Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.bounded_image
- \+/\- *lemma* bounded_continuous_function.bounded_range
- \+ *lemma* bounded_continuous_function.coe_injective
- \+ *lemma* bounded_continuous_function.dist_eq_supr
- \+ *lemma* bounded_continuous_function.dist_extend_extend
- \+ *def* bounded_continuous_function.extend
- \+ *lemma* bounded_continuous_function.extend_apply'
- \+ *lemma* bounded_continuous_function.extend_apply
- \+ *lemma* bounded_continuous_function.extend_comp
- \+ *lemma* bounded_continuous_function.extend_of_empty
- \+ *lemma* bounded_continuous_function.isometry_extend

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.bounded.union
- \+/\- *lemma* metric.bounded_union

Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/isometry.lean
- \+ *theorem* isometry.embedding

Added src/topology/metric_space/metrizable.lean
- \+ *lemma* topological_space.exists_embedding_l_infty

Modified src/topology/separation.lean
- \+ *lemma* normal_space_of_regular_second_countable
- \+ *lemma* topological_space.is_topological_basis.exists_closure_subset
- \+ *lemma* topological_space.is_topological_basis.nhds_basis_closure

Modified src/topology/uniform_space/basic.lean
- \+ *def* uniform_space.replace_topology
- \+ *lemma* uniform_space.replace_topology_eq



## [2021-11-25 18:25:14](https://github.com/leanprover-community/mathlib/commit/ee71ddf)
feat(ring_theory/graded_algebra): definition of type class `graded_algebra` ([#10115](https://github.com/leanprover-community/mathlib/pull/10115))
This is largely written by @eric-wieser. Thank you.
#### Estimated changes
Added src/ring_theory/graded_algebra/basic.lean
- \+ *lemma* graded_algebra.decompose'_def
- \+ *def* graded_algebra.decompose
- \+ *lemma* graded_algebra.decompose_symm_of
- \+ *lemma* graded_ring.is_internal



## [2021-11-25 16:03:28](https://github.com/leanprover-community/mathlib/commit/644591f)
chore(algebra/group/basic): + 2 simp lemmas about `a - b` ([#10478](https://github.com/leanprover-community/mathlib/pull/10478))
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* sub_add_cancel'



## [2021-11-25 12:14:38](https://github.com/leanprover-community/mathlib/commit/7d8a1e0)
feat(data/polynomial/eval): random `eval` lemmas ([#10470](https://github.com/leanprover-community/mathlib/pull/10470))
note that the `geom_sum` import only adds the `geom_sum` file itself; all other files were imported already
#### Estimated changes
Modified src/algebra/geom_sum.lean
- \+ *lemma* one_geom_sum
- \+/\- *lemma* op_geom_sum
- \+/\- *lemma* op_geom_sum₂

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.eval_dvd
- \+ *lemma* polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
- \+ *lemma* polynomial.eval_geom_sum



## [2021-11-25 07:53:00](https://github.com/leanprover-community/mathlib/commit/5b767aa)
feat(measure_theory/integral/integral_eq_improper): weaken measurability assumptions  ([#10387](https://github.com/leanprover-community/mathlib/pull/10387))
As suggested by @fpvandoorn, this removes a.e. measurability assumptions which could be deduced from integrability assumptions. More of them could be removed assuming the codomain is a `borel_space` and not only an `open_measurable_space`, but I’m not sure wether or not it would be a good idea.
#### Estimated changes
Modified src/measure_theory/integral/integrable_on.lean


Modified src/measure_theory/integral/integral_eq_improper.lean
- \+ *lemma* measure_theory.ae_cover.ae_measurable

Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.restrict_congr_set
- \+ *lemma* measure_theory.measure.restrict_eq_self_of_ae_mem
- \+ *lemma* measure_theory.measure.restrict_mono_ae
- \- *lemma* measure_theory.restrict_congr_set
- \- *lemma* measure_theory.restrict_mono_ae



## [2021-11-25 03:11:34](https://github.com/leanprover-community/mathlib/commit/7dfd7e8)
chore(scripts): update nolints.txt ([#10484](https://github.com/leanprover-community/mathlib/pull/10484))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-11-25 01:40:31](https://github.com/leanprover-community/mathlib/commit/d04f5a5)
feat(algebra/pointwise): lemmas about multiplication of finsets ([#10455](https://github.com/leanprover-community/mathlib/pull/10455))
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+/\- *lemma* finset.coe_mul
- \+ *lemma* finset.empty_mul
- \+/\- *lemma* finset.mem_mul
- \+/\- *lemma* finset.mul_card_le
- \+/\- *lemma* finset.mul_def
- \+ *lemma* finset.mul_empty
- \+/\- *lemma* finset.mul_mem_mul
- \+ *lemma* finset.mul_nonempty_iff
- \+ *lemma* finset.mul_singleton_zero
- \+ *lemma* finset.mul_subset_mul
- \+ *lemma* finset.singleton_zero_mul



## [2021-11-24 18:18:56](https://github.com/leanprover-community/mathlib/commit/daf30fd)
feat(analysis/asymptotics): Generalize superpolynomial decay using limits instead of big O ([#10296](https://github.com/leanprover-community/mathlib/pull/10296))
This PR generalizes the definition of `superpolynomial_decay` in terms of `filter.tendsto` instead of `asymptotics.is_O`.
#### Estimated changes
Modified src/analysis/asymptotics/superpolynomial_decay.lean
- \- *lemma* asymptotics.is_O.trans_superpolynomial_decay
- \+/\- *lemma* asymptotics.superpolynomial_decay.add
- \- *lemma* asymptotics.superpolynomial_decay.algebra_map_mul
- \- *lemma* asymptotics.superpolynomial_decay.algebra_map_pow_mul
- \+ *lemma* asymptotics.superpolynomial_decay.congr'
- \+ *lemma* asymptotics.superpolynomial_decay.congr
- \+/\- *lemma* asymptotics.superpolynomial_decay.const_mul
- \- *lemma* asymptotics.superpolynomial_decay.eventually_le
- \- *lemma* asymptotics.superpolynomial_decay.eventually_mono
- \+ *lemma* asymptotics.superpolynomial_decay.inv_param_mul
- \- *lemma* asymptotics.superpolynomial_decay.mono
- \+/\- *lemma* asymptotics.superpolynomial_decay.mul
- \+/\- *lemma* asymptotics.superpolynomial_decay.mul_const
- \- *lemma* asymptotics.superpolynomial_decay.mul_is_O
- \- *lemma* asymptotics.superpolynomial_decay.mul_is_O_polynomial
- \+ *lemma* asymptotics.superpolynomial_decay.mul_param
- \+ *lemma* asymptotics.superpolynomial_decay.mul_param_pow
- \+ *lemma* asymptotics.superpolynomial_decay.mul_param_zpow
- \+ *lemma* asymptotics.superpolynomial_decay.mul_polynomial
- \+ *lemma* asymptotics.superpolynomial_decay.param_inv_mul
- \+ *lemma* asymptotics.superpolynomial_decay.param_mul
- \+ *lemma* asymptotics.superpolynomial_decay.param_pow_mul
- \+ *lemma* asymptotics.superpolynomial_decay.param_zpow_mul
- \+ *lemma* asymptotics.superpolynomial_decay.polynomial_mul
- \- *theorem* asymptotics.superpolynomial_decay.polynomial_mul
- \- *lemma* asymptotics.superpolynomial_decay.tendsto_zero
- \+ *lemma* asymptotics.superpolynomial_decay.trans_abs_le
- \+ *lemma* asymptotics.superpolynomial_decay.trans_eventually_abs_le
- \+ *lemma* asymptotics.superpolynomial_decay.trans_eventually_le
- \+/\- *def* asymptotics.superpolynomial_decay
- \- *lemma* asymptotics.superpolynomial_decay_const_iff
- \+/\- *lemma* asymptotics.superpolynomial_decay_const_mul_iff
- \- *lemma* asymptotics.superpolynomial_decay_const_mul_iff_of_ne_zero
- \+ *lemma* asymptotics.superpolynomial_decay_iff_abs_is_bounded_under
- \+ *lemma* asymptotics.superpolynomial_decay_iff_abs_tendsto_zero
- \+ *lemma* asymptotics.superpolynomial_decay_iff_is_O
- \- *theorem* asymptotics.superpolynomial_decay_iff_is_bounded_under
- \+ *lemma* asymptotics.superpolynomial_decay_iff_is_o
- \- *theorem* asymptotics.superpolynomial_decay_iff_is_o
- \+ *lemma* asymptotics.superpolynomial_decay_iff_norm_tendsto_zero
- \- *theorem* asymptotics.superpolynomial_decay_iff_norm_tendsto_zero
- \+ *lemma* asymptotics.superpolynomial_decay_iff_superpolynomial_decay_abs
- \+ *lemma* asymptotics.superpolynomial_decay_iff_superpolynomial_decay_norm
- \- *lemma* asymptotics.superpolynomial_decay_iff_tendsto_zero
- \+ *lemma* asymptotics.superpolynomial_decay_iff_zpow_tendsto_zero
- \+/\- *lemma* asymptotics.superpolynomial_decay_mul_const_iff
- \- *lemma* asymptotics.superpolynomial_decay_mul_const_iff_of_ne_zero
- \+ *lemma* asymptotics.superpolynomial_decay_mul_param_iff
- \+ *lemma* asymptotics.superpolynomial_decay_mul_param_pow_iff
- \- *lemma* asymptotics.superpolynomial_decay_of_eventually_is_O
- \- *lemma* asymptotics.superpolynomial_decay_of_is_O_zpow_le
- \- *lemma* asymptotics.superpolynomial_decay_of_is_O_zpow_lt
- \+ *lemma* asymptotics.superpolynomial_decay_param_mul_iff
- \+ *lemma* asymptotics.superpolynomial_decay_param_pow_mul_iff
- \- *lemma* asymptotics.superpolynomial_decay_zero'
- \+/\- *lemma* asymptotics.superpolynomial_decay_zero

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.eventually_ne_of_tendsto_at_bot
- \+ *lemma* filter.eventually_ne_of_tendsto_at_top

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* tendsto_zero_iff_abs_tendsto_zero



## [2021-11-24 14:56:57](https://github.com/leanprover-community/mathlib/commit/18e5510)
fix(tactic/cancel_denoms): remove debug code ([#10434](https://github.com/leanprover-community/mathlib/pull/10434))
This code must not be used -- worth keeping, as it's a potentially useful function, but it shouldn't trace anything.
#### Estimated changes
Modified src/tactic/cancel_denoms.lean




## [2021-11-24 12:24:42](https://github.com/leanprover-community/mathlib/commit/b29b952)
feat(measure_theory/group/fundamental_domain): prove equality of integrals ([#10448](https://github.com/leanprover-community/mathlib/pull/10448))
#### Estimated changes
Modified src/dynamics/ergodic/measure_preserving.lean
- \+ *lemma* measure_theory.measure_preserving.ae_measurable_comp_iff

Modified src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* measure_theory.is_fundamental_domain.lintegral_eq_tsum_of_ac
- \+ *lemma* measure_theory.is_fundamental_domain.measure_eq_tsum_of_ac
- \+ *lemma* measure_theory.is_fundamental_domain.mono
- \+ *lemma* measure_theory.is_fundamental_domain.set_lintegral_eq_tsum'
- \+ *lemma* measure_theory.is_fundamental_domain.set_lintegral_eq_tsum
- \+ *lemma* measure_theory.is_fundamental_domain.sum_restrict_of_ac



## [2021-11-24 12:24:41](https://github.com/leanprover-community/mathlib/commit/563f8c4)
feat(measure_theory/integral): dominated convergence for a series ([#10398](https://github.com/leanprover-community/mathlib/pull/10398))
#### Estimated changes
Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.has_sum_integral_of_dominated_convergence

Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* interval_integral.has_sum_integral_of_dominated_convergence
- \+ *lemma* interval_integral.tendsto_integral_filter_of_dominated_convergence



## [2021-11-24 10:42:43](https://github.com/leanprover-community/mathlib/commit/132833b)
refactor(algebra.abs): Introduce `has_pos_part` and `has_neg_part` classes ([#10420](https://github.com/leanprover-community/mathlib/pull/10420))
refactor(algebra.abs): Introduce `has_pos_part` and `has_neg_part` classes
#### Estimated changes
Modified src/algebra/abs.lean


Modified src/algebra/lattice_ordered_group.lean
- \+ *lemma* lattice_ordered_comm_group.m_neg_part_def
- \+ *lemma* lattice_ordered_comm_group.m_pos_part_def
- \- *def* lattice_ordered_comm_group.mneg
- \- *def* lattice_ordered_comm_group.mpos
- \+/\- *lemma* lattice_ordered_comm_group.neg_eq_pos_inv



## [2021-11-24 09:23:46](https://github.com/leanprover-community/mathlib/commit/09b4bfc)
feat(linear_algebra/multilinear/basic): multilinear maps with respect to an empty family are all constant ([#10433](https://github.com/leanprover-community/mathlib/pull/10433))
This seemingly-innocuous statement is valuable as a base case for induction.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/multilinear/basic.lean
- \+ *def* multilinear_map.const_linear_equiv_of_is_empty
- \+ *lemma* multilinear_map.mk_coe



## [2021-11-24 07:49:21](https://github.com/leanprover-community/mathlib/commit/d487d65)
refactor(topology,algebraic_geometry): use bundled maps here and there ([#10447](https://github.com/leanprover-community/mathlib/pull/10447))
* `opens.comap` now takes a `continuous_map` and returns a `preorder_hom`;
* `prime_spectrum.comap` is now a bundled `continuous_map`.
#### Estimated changes
Modified src/algebraic_geometry/Spec.lean
- \+/\- *def* algebraic_geometry.Spec.Top_map

Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+/\- *def* prime_spectrum.comap
- \- *lemma* prime_spectrum.comap_continuous
- \+/\- *lemma* prime_spectrum.comap_id
- \+ *lemma* prime_spectrum.preimage_comap_zero_locus_aux

Modified src/algebraic_geometry/prime_spectrum/is_open_comap_C.lean


Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/measure_theory/measure/content.lean


Modified src/topology/opens.lean
- \+/\- *lemma* topological_space.opens.coe_comap
- \+/\- *def* topological_space.opens.comap
- \+/\- *lemma* topological_space.opens.comap_id
- \+/\- *lemma* topological_space.opens.comap_mono
- \+/\- *lemma* topological_space.opens.comap_val



## [2021-11-24 07:49:20](https://github.com/leanprover-community/mathlib/commit/3590dc2)
feat(topology/uniform_space/uniform_convergence): slightly generalize theorems ([#10444](https://github.com/leanprover-community/mathlib/pull/10444))
* add `protected` to some theorems;
* assume `∀ᶠ n, continuous (F n)` instead of `∀ n, continuous (F n)`;
* get rid of `F n` in lemmas like `continuous_within_at_of_locally_uniform_approx_of_continuous_within_at`; instead, assume that there exists a continuous `F` that approximates `f`.
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \- *lemma* analytic_at.continuous_at
- \- *lemma* has_fpower_series_at.continuous_at
- \- *lemma* has_fpower_series_on_ball.continuous_on

Modified src/topology/continuous_function/bounded.lean


Modified src/topology/uniform_space/uniform_convergence.lean
- \- *lemma* continuous_of_locally_uniform_approx_of_continuous
- \+ *lemma* continuous_of_locally_uniform_approx_of_continuous_at
- \+/\- *lemma* continuous_of_uniform_approx_of_continuous
- \- *lemma* continuous_on_of_locally_uniform_approx_of_continuous_on
- \+ *lemma* continuous_on_of_locally_uniform_approx_of_continuous_within_at
- \- *lemma* tendsto_locally_uniformly.continuous
- \- *lemma* tendsto_locally_uniformly_on.continuous_on
- \- *lemma* tendsto_uniformly.continuous
- \- *lemma* tendsto_uniformly.tendsto_locally_uniformly
- \- *lemma* tendsto_uniformly.tendsto_uniformly_on
- \- *lemma* tendsto_uniformly_on.continuous_on
- \- *lemma* tendsto_uniformly_on.tendsto_locally_uniformly_on



## [2021-11-24 07:49:19](https://github.com/leanprover-community/mathlib/commit/8d07dbf)
feat(topology/sheaves): Generalized some lemmas. ([#10440](https://github.com/leanprover-community/mathlib/pull/10440))
Generalizes some lemmas and explicitly stated that for `f` to be an iso on `U`, it suffices that the stalk map is an iso for all `x : U`.
#### Estimated changes
Modified src/topology/sheaves/stalks.lean
- \+ *lemma* Top.presheaf.app_is_iso_of_stalk_functor_map_iso



## [2021-11-24 07:49:18](https://github.com/leanprover-community/mathlib/commit/a086daa)
chore(ring_theory/polynomial/cyclotomic): use `ratfunc` ([#10421](https://github.com/leanprover-community/mathlib/pull/10421))
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic.lean
- \+/\- *lemma* polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius



## [2021-11-24 07:49:17](https://github.com/leanprover-community/mathlib/commit/6cb52e6)
feat(category_theory/limits): Results about (co)limits in Top ([#9985](https://github.com/leanprover-community/mathlib/pull/9985))
- Provided the explicit topologies for limits and colimits, and specialized this result onto some shapes.
- Provided the isomorphism between the (co)limits and the constructions in `topology/constructions.lean`.
- Provided conditions about whether `prod.map` and `pullback_map` are inducing, embedding, etc.
#### Estimated changes
Modified src/topology/category/Top/limits.lean
- \+ *lemma* Top.coequalizer_is_open_iff
- \+ *lemma* Top.coinduced_of_is_colimit
- \+ *lemma* Top.colimit_is_open_iff
- \+ *lemma* Top.colimit_topology
- \+ *lemma* Top.embedding_of_pullback_embeddings
- \+ *lemma* Top.embedding_prod_map
- \+ *lemma* Top.embedding_pullback_to_prod
- \+ *lemma* Top.fst_embedding_of_right_embedding
- \+ *lemma* Top.fst_iso_of_right_embedding_range_subset
- \+ *lemma* Top.fst_open_embedding_of_right_open_embedding
- \+ *lemma* Top.induced_of_is_limit
- \+ *lemma* Top.inducing_prod_map
- \+ *lemma* Top.inducing_pullback_to_prod
- \+ *lemma* Top.limit_topology
- \+ *lemma* Top.open_embedding_of_pullback_open_embeddings
- \+ *def* Top.pi_fan
- \+ *def* Top.pi_fan_is_limit
- \+ *def* Top.pi_iso_pi
- \+ *lemma* Top.pi_iso_pi_hom_apply
- \+ *lemma* Top.pi_iso_pi_inv_π
- \+ *lemma* Top.pi_iso_pi_inv_π_apply
- \+ *abbreviation* Top.pi_π
- \+ *def* Top.prod_binary_fan
- \+ *def* Top.prod_binary_fan_is_limit
- \+ *abbreviation* Top.prod_fst
- \+ *def* Top.prod_iso_prod
- \+ *lemma* Top.prod_iso_prod_hom_apply
- \+ *lemma* Top.prod_iso_prod_hom_fst
- \+ *lemma* Top.prod_iso_prod_hom_snd
- \+ *lemma* Top.prod_iso_prod_inv_fst
- \+ *lemma* Top.prod_iso_prod_inv_snd
- \+ *abbreviation* Top.prod_snd
- \+ *lemma* Top.prod_topology
- \+ *def* Top.pullback_cone
- \+ *def* Top.pullback_cone_is_limit
- \+ *abbreviation* Top.pullback_fst
- \+ *lemma* Top.pullback_fst_range
- \+ *def* Top.pullback_iso_prod_subtype
- \+ *lemma* Top.pullback_iso_prod_subtype_hom_apply
- \+ *lemma* Top.pullback_iso_prod_subtype_hom_fst
- \+ *lemma* Top.pullback_iso_prod_subtype_hom_snd
- \+ *lemma* Top.pullback_iso_prod_subtype_inv_fst
- \+ *lemma* Top.pullback_iso_prod_subtype_inv_fst_apply
- \+ *lemma* Top.pullback_iso_prod_subtype_inv_snd
- \+ *lemma* Top.pullback_iso_prod_subtype_inv_snd_apply
- \+ *lemma* Top.pullback_map_embedding_of_embeddings
- \+ *lemma* Top.pullback_map_open_embedding_of_open_embeddings
- \+ *abbreviation* Top.pullback_snd
- \+ *lemma* Top.pullback_snd_range
- \+ *lemma* Top.pullback_topology
- \+ *lemma* Top.range_prod_map
- \+ *lemma* Top.range_pullback_map
- \+ *lemma* Top.range_pullback_to_prod
- \+ *def* Top.sigma_cofan
- \+ *def* Top.sigma_cofan_is_colimit
- \+ *def* Top.sigma_iso_sigma
- \+ *lemma* Top.sigma_iso_sigma_hom_ι
- \+ *lemma* Top.sigma_iso_sigma_hom_ι_apply
- \+ *lemma* Top.sigma_iso_sigma_inv_apply
- \+ *abbreviation* Top.sigma_ι
- \+ *lemma* Top.snd_embedding_of_left_embedding
- \+ *lemma* Top.snd_iso_of_left_embedding_range_subset
- \+ *lemma* Top.snd_open_embedding_of_left_open_embedding

Modified src/topology/homeomorph.lean




## [2021-11-24 06:51:50](https://github.com/leanprover-community/mathlib/commit/d267b6c)
chore(topology): add 2 missing `inhabited` instances ([#10446](https://github.com/leanprover-community/mathlib/pull/10446))
Also add an instance from `discrete_topology` to `topological_ring`.
#### Estimated changes
Modified src/topology/algebra/ring.lean


Modified src/topology/category/Top/open_nhds.lean


Modified src/topology/category/TopCommRing.lean




## [2021-11-24 03:16:10](https://github.com/leanprover-community/mathlib/commit/1c00179)
chore(scripts): update nolints.txt ([#10445](https://github.com/leanprover-community/mathlib/pull/10445))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-11-24 02:33:03](https://github.com/leanprover-community/mathlib/commit/f578d1d)
feat(measure_theory): TC for smul-invariant measures ([#10325](https://github.com/leanprover-community/mathlib/pull/10325))
#### Estimated changes
Modified src/dynamics/ergodic/measure_preserving.lean
- \+ *lemma* measure_theory.measure_preserving.measure_preimage_emb

Added src/measure_theory/group/action.lean
- \+ *lemma* measure_theory.is_locally_finite_measure_of_smul_invariant
- \+ *lemma* measure_theory.map_smul
- \+ *lemma* measure_theory.measure_eq_zero_iff_eq_empty_of_smul_invariant
- \+ *lemma* measure_theory.measure_is_open_pos_of_smul_invariant_of_compact_ne_zero
- \+ *lemma* measure_theory.measure_is_open_pos_of_smul_invariant_of_ne_zero
- \+ *lemma* measure_theory.measure_pos_iff_nonempty_of_smul_invariant
- \+ *lemma* measure_theory.measure_preimage_smul
- \+ *lemma* measure_theory.measure_preserving_smul
- \+ *lemma* measure_theory.measure_smul_set
- \+ *lemma* measure_theory.smul_invariant_measure_tfae

Added src/measure_theory/group/fundamental_domain.lean
- \+ *structure* measure_theory.is_add_fundamental_domain
- \+ *lemma* measure_theory.is_fundamental_domain.Union_smul_ae_eq
- \+ *lemma* measure_theory.is_fundamental_domain.measurable_set_smul
- \+ *lemma* measure_theory.is_fundamental_domain.measure_eq_tsum'
- \+ *lemma* measure_theory.is_fundamental_domain.measure_eq_tsum
- \+ *lemma* measure_theory.is_fundamental_domain.pairwise_ae_disjoint
- \+ *structure* measure_theory.is_fundamental_domain

Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measure/measure_space_def.lean
- \+/\- *lemma* measure_theory.measure_Union_null_iff
- \+ *lemma* measure_theory.measure_sUnion_null_iff



## [2021-11-23 22:42:46](https://github.com/leanprover-community/mathlib/commit/0cbba1a)
feat(ring_theory/adjoin/basic): add adjoin_induction' and adjoin_adjoin_coe_preimage ([#10427](https://github.com/leanprover-community/mathlib/pull/10427))
From FLT-regular.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.closure_closure_coe_preimage

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid.closure_closure_coe_preimage

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.span_induction'
- \+ *lemma* submodule.span_span_coe_preimage

Modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* algebra.adjoin_adjoin_coe_preimage
- \+ *lemma* algebra.adjoin_induction'



## [2021-11-23 22:42:45](https://github.com/leanprover-community/mathlib/commit/c192937)
feat(analysis): derivative of a parametric interval integral ([#10404](https://github.com/leanprover-community/mathlib/pull/10404))
#### Estimated changes
Added src/analysis/calculus/parametric_interval_integral.lean
- \+ *lemma* interval_integral.has_deriv_at_integral_of_dominated_loc_of_deriv_le
- \+ *lemma* interval_integral.has_deriv_at_integral_of_dominated_loc_of_lip
- \+ *lemma* interval_integral.has_fderiv_at_integral_of_dominated_loc_of_lip
- \+ *lemma* interval_integral.has_fderiv_at_integral_of_dominated_of_fderiv_le

Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* measurable_set_interval_oc



## [2021-11-23 21:34:42](https://github.com/leanprover-community/mathlib/commit/ac283c2)
feat(data/nat/prime): some lemmas about prime factors ([#10385](https://github.com/leanprover-community/mathlib/pull/10385))
A few small lemmas about prime factors, for use in future PRs on prime factorisations and the Euler product formula for totient
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.factors_count_eq_of_coprime_left
- \+ *lemma* nat.factors_count_eq_of_coprime_right
- \+ *lemma* nat.le_factors_count_mul_left
- \+ *lemma* nat.le_factors_count_mul_right
- \+ *lemma* nat.mem_factors_mul_left
- \+ *lemma* nat.mem_factors_mul_right
- \+ *lemma* nat.perm_factors_mul_of_coprime
- \+ *lemma* nat.perm_factors_mul_of_pos



## [2021-11-23 20:50:39](https://github.com/leanprover-community/mathlib/commit/eb8b1b8)
feat(linear_algebra/affine_space/barycentric_coords): characterise affine bases in terms of coordinate matrices ([#10370](https://github.com/leanprover-community/mathlib/pull/10370))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* affine_basis.affine_independent_of_to_matrix_right_inv
- \+ *lemma* affine_basis.affine_span_eq_top_of_to_matrix_left_inv
- \+ *lemma* affine_basis.ext_elem
- \+ *lemma* affine_basis.is_unit_to_matrix_iff
- \+ *lemma* affine_basis.to_matrix_row_sum_one

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent_iff_eq_of_fintype_affine_combination_eq



## [2021-11-23 19:47:54](https://github.com/leanprover-community/mathlib/commit/fb82d0a)
feat(data/mv_polynomial/basic): add a symmetric version of coeff_X_mul and generalize to monomials ([#10429](https://github.com/leanprover-community/mathlib/pull/10429))
#### Estimated changes
Modified src/algebra/monoid_algebra/basic.lean
- \+ *lemma* add_monoid_algebra.support_single_mul
- \+ *lemma* monoid_algebra.support_single_mul

Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.coeff_X_mul'
- \+ *lemma* mv_polynomial.coeff_X_mul
- \+ *lemma* mv_polynomial.coeff_monomial_mul'
- \+ *lemma* mv_polynomial.coeff_monomial_mul
- \+ *lemma* mv_polynomial.coeff_mul_monomial'
- \+ *lemma* mv_polynomial.coeff_mul_monomial
- \+/\- *lemma* mv_polynomial.map_alg_hom_coe_ring_hom
- \+ *lemma* mv_polynomial.support_X_mul



## [2021-11-23 19:47:53](https://github.com/leanprover-community/mathlib/commit/ba43124)
feat(category_theory/sites/*): Comparison lemma ([#9785](https://github.com/leanprover-community/mathlib/pull/9785))
#### Estimated changes
Modified src/category_theory/sites/cover_lifting.lean
- \+/\- *theorem* category_theory.Ran_is_sheaf_of_cover_lifting
- \+ *lemma* category_theory.comp_cover_lifting
- \- *def* category_theory.comp_cover_lifting
- \+/\- *structure* category_theory.cover_lifting
- \+ *lemma* category_theory.id_cover_lifting
- \- *def* category_theory.id_cover_lifting
- \+ *def* category_theory.sites.copullback
- \+ *def* category_theory.sites.pullback_copullback_adjunction

Modified src/category_theory/sites/dense_subsite.lean
- \+ *def* category_theory.cover_dense.Sheaf_equiv_of_cover_preserving_cover_lifting
- \+ *lemma* category_theory.cover_dense.compatible_preserving

Added src/category_theory/sites/induced_topology.lean
- \+ *def* category_theory.cover_dense.Sheaf_equiv
- \+ *abbreviation* category_theory.cover_dense.induced_topology
- \+ *lemma* category_theory.cover_dense.locally_cover_dense
- \+ *def* category_theory.locally_cover_dense.induced_topology
- \+ *lemma* category_theory.locally_cover_dense.induced_topology_cover_lifting
- \+ *lemma* category_theory.locally_cover_dense.induced_topology_cover_preserving
- \+ *lemma* category_theory.locally_cover_dense.pushforward_cover_iff_cover_pullback
- \+ *def* category_theory.locally_cover_dense
- \+ *lemma* category_theory.over_forget_locally_cover_dense

Modified src/category_theory/sites/sieves.lean
- \+/\- *lemma* category_theory.sieve.functor_pushforward_bot
- \+ *lemma* category_theory.sieve.functor_pushforward_top



## [2021-11-23 18:21:04](https://github.com/leanprover-community/mathlib/commit/a779f6c)
feat(topology/algebra/ordered): convergent sequence is bounded above/below ([#10424](https://github.com/leanprover-community/mathlib/pull/10424))
Also move lemmas `Ixx_mem_nhds` up to generalize them from
`[linear_order α] [order_topology α]` to
`[linear_order α] [order_closed_topology α]`.
#### Estimated changes
Modified src/order/liminf_limsup.lean
- \+ *lemma* filter.is_bounded_under.bdd_above_range
- \+ *lemma* filter.is_bounded_under.bdd_above_range_of_cofinite
- \+ *lemma* filter.is_bounded_under.bdd_below_range
- \+ *lemma* filter.is_bounded_under.bdd_below_range_of_cofinite
- \+/\- *lemma* filter.not_is_bounded_under_of_tendsto_at_bot
- \+/\- *lemma* filter.not_is_bounded_under_of_tendsto_at_top

Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/algebra/ordered/liminf_limsup.lean
- \+ *lemma* filter.tendsto.bdd_above_range
- \+ *lemma* filter.tendsto.bdd_above_range_of_cofinite
- \+ *lemma* filter.tendsto.bdd_below_range
- \+ *lemma* filter.tendsto.bdd_below_range_of_cofinite



## [2021-11-23 18:21:02](https://github.com/leanprover-community/mathlib/commit/1dd3ae1)
feat(algebra/big_operators/order): Bounding on a sum of cards by double counting ([#10389](https://github.com/leanprover-community/mathlib/pull/10389))
If every element of `s` is in at least/most `n` finsets of `B : finset (finset α)`, then the sum of `(s ∩ t).card` over `t ∈ B` is at most/least `s.card * n`.
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *lemma* finset.le_sum_card
- \+ *lemma* finset.le_sum_card_inter
- \+ *lemma* finset.sum_card
- \+ *lemma* finset.sum_card_inter
- \+ *lemma* finset.sum_card_inter_le
- \+ *lemma* finset.sum_card_le



## [2021-11-23 16:49:25](https://github.com/leanprover-community/mathlib/commit/b14f22e)
chore(algebra/algebra and group_theory/group_action): move a lemma ([#10425](https://github.com/leanprover-community/mathlib/pull/10425))
Move a lemma about the action of a group on the units of a monoid
to a more appropriate place. It accidentally ended up in
`algebra/algebra/spectrum` but a better place is
`group_theory/group_action/units`.
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \- *lemma* is_unit.smul_iff

Modified src/group_theory/group_action/group.lean
- \+ *lemma* is_unit_smul_iff

Modified src/group_theory/group_action/units.lean
- \+ *lemma* is_unit.smul



## [2021-11-23 16:49:24](https://github.com/leanprover-community/mathlib/commit/7c4f395)
feat(measure_theory): add `is_R_or_C.measurable_space` ([#10417](https://github.com/leanprover-community/mathlib/pull/10417))
Don't remove specific instances because otherwise Lean fails to generate `borel_space (ι → ℝ)`.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/function/conditional_expectation.lean
- \+/\- *lemma* measure_theory.ae_measurable'.const_inner
- \+/\- *lemma* measure_theory.norm_condexp_L2_le_one

Modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* measure_theory.integrable.of_real
- \+/\- *lemma* measure_theory.integrable.re_im_iff

Modified src/measure_theory/function/l2_space.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/function/special_functions.lean


Modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* continuous_linear_map.continuous_integral_comp_L1
- \+/\- *def* measure_theory.Lp_to_Lp_restrict_clm
- \+/\- *lemma* measure_theory.Lp_to_Lp_restrict_clm_coe_fn
- \+/\- *lemma* measure_theory.Lp_to_Lp_restrict_smul



## [2021-11-23 16:49:23](https://github.com/leanprover-community/mathlib/commit/a1338d6)
feat(linear_algebra/affine_space/barycentric_coords): affine bases exist over fields ([#10333](https://github.com/leanprover-community/mathlib/pull/10333))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* affine_basis.exists_affine_basis
- \+ *lemma* affine_basis.exists_affine_basis_of_finite_dimensional



## [2021-11-23 16:49:22](https://github.com/leanprover-community/mathlib/commit/7a6e6d8)
feat(group_theory/schur_zassenhaus): Prove the full Schur-Zassenhaus theorem ([#10283](https://github.com/leanprover-community/mathlib/pull/10283))
Previously, the Schur-Zassenhaus theorem was only proved for abelian normal subgroups. This PR removes the abelian assumption.
#### Estimated changes
Modified src/group_theory/schur_zassenhaus.lean
- \+/\- *theorem* subgroup.exists_left_complement'_of_coprime
- \+ *theorem* subgroup.exists_left_complement'_of_coprime_of_fintype
- \+/\- *theorem* subgroup.exists_right_complement'_of_coprime
- \+ *theorem* subgroup.exists_right_complement'_of_coprime_of_fintype
- \+ *lemma* subgroup.schur_zassenhaus_induction.step7



## [2021-11-23 16:49:21](https://github.com/leanprover-community/mathlib/commit/97186fe)
feat(combinatorics): Hindman's theorem on finite sums ([#10029](https://github.com/leanprover-community/mathlib/pull/10029))
A short proof of Hindman's theorem using idempotent ultrafilters.
#### Estimated changes
Added src/combinatorics/hindman.lean
- \+ *lemma* hindman.FP.finset_prod
- \+ *lemma* hindman.FP.mul
- \+ *lemma* hindman.FP.mul_two
- \+ *lemma* hindman.FP.singleton
- \+ *inductive* hindman.FP
- \+ *lemma* hindman.FP_drop_subset_FP
- \+ *lemma* hindman.FP_partition_regular
- \+ *inductive* hindman.FS
- \+ *lemma* hindman.exists_FP_of_finite_cover
- \+ *lemma* hindman.exists_FP_of_large
- \+ *lemma* hindman.exists_idempotent_ultrafilter_le_FP
- \+ *structure* on
- \+ *lemma* ultrafilter.continuous_mul_left
- \+ *lemma* ultrafilter.eventually_mul
- \+ *def* ultrafilter.has_mul
- \+ *def* ultrafilter.semigroup

Modified src/data/stream/basic.lean
- \+ *lemma* stream.head_drop

Modified src/order/filter/ultrafilter.lean


Added src/topology/algebra/semigroup.lean
- \+ *lemma* exists_idempotent_in_compact_subsemigroup
- \+ *lemma* exists_idempotent_of_compact_t2_of_continuous_mul_left



## [2021-11-23 15:06:10](https://github.com/leanprover-community/mathlib/commit/050482c)
doc(measure_theory/decomposition/jordan): typo ([#10430](https://github.com/leanprover-community/mathlib/pull/10430))
#### Estimated changes
Modified src/measure_theory/decomposition/jordan.lean




## [2021-11-23 15:06:08](https://github.com/leanprover-community/mathlib/commit/53bd9d7)
feat(field_theory): generalize `ratfunc K` to `comm_ring K`/`is_domain K` ([#10428](https://github.com/leanprover-community/mathlib/pull/10428))
Fixes one of the TODO's from the original ratfunc PR: apply all the easy generalizations where `K` doesn't need to be a field, only a `is_domain K` or even just `comm_ring K`.
This would allow us to use `ratfunc` in [#10421](https://github.com/leanprover-community/mathlib/pull/10421).
#### Estimated changes
Modified src/field_theory/ratfunc.lean




## [2021-11-23 15:06:07](https://github.com/leanprover-community/mathlib/commit/7958251)
doc(field_theory/abel_ruffini): update module doc ([#10426](https://github.com/leanprover-community/mathlib/pull/10426))
#### Estimated changes
Modified src/field_theory/abel_ruffini.lean




## [2021-11-23 15:06:06](https://github.com/leanprover-community/mathlib/commit/2b75493)
refactor(algebra.group.basic): Convert sub_add_cancel and neg_sub to multaplicative form ([#10419](https://github.com/leanprover-community/mathlib/pull/10419))
Currently mathlib has a rich set of lemmas connecting the addition, subtraction and negation additive group operations, but a far thinner collection of results for multiplication, division and inverse multiplicative group operations, despite the fact that the former can be generated easily from the latter via `to_additive`.
In  [#9548](https://github.com/leanprover-community/mathlib/pull/9548) I require multiplicative forms of the existing `sub_add_cancel` and `neg_sub` lemmas. This PR refactors them as the equivalent multiplicative results and then recovers `sub_add_cancel` and `neg_sub` via `to_additive`. There is a complication in that unfortunately `group_with_zero` already has lemmas named `inv_div` and `div_mul_cancel`. I have worked around this by naming the lemmas in this PR `inv_div'` and `div_mul_cancel'` and then manually overriding the names generated by `to_additive`. Other suggestions as to how to approach this welcome.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* div_mul_cancel'
- \+ *lemma* inv_div'
- \- *lemma* neg_sub
- \- *lemma* sub_add_cancel



## [2021-11-23 15:06:04](https://github.com/leanprover-community/mathlib/commit/d0e454a)
feat(logic/function/basic): add `function.{in,sur,bi}jective.comp_left` ([#10406](https://github.com/leanprover-community/mathlib/pull/10406))
As far as I can tell we don't have these variations.
Note that the `surjective` and `bijective` versions do not appear next to the other composition statements, as they require `surj_inv` to concisely prove.
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *lemma* function.bijective.comp_left
- \+ *lemma* function.injective.comp_left
- \+ *lemma* function.surjective.comp_left



## [2021-11-23 13:11:55](https://github.com/leanprover-community/mathlib/commit/d9e40b4)
chore(measure_theory/integral): generalize `interval_integral.norm_integral_le_integral_norm` ([#10412](https://github.com/leanprover-community/mathlib/pull/10412))
It was formulated only for functions `f : α → ℝ`; generalize to `f : α → E`.
#### Estimated changes
Modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* interval_integral.norm_integral_le_integral_norm



## [2021-11-23 13:11:54](https://github.com/leanprover-community/mathlib/commit/2817788)
chore(measure_theory/integral): add `integrable_const` for `interval_integral` ([#10410](https://github.com/leanprover-community/mathlib/pull/10410))
#### Estimated changes
Modified src/measure_theory/integral/integrable_on.lean
- \+/\- *lemma* measure_theory.integrable_on_const

Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* interval_integrable_const
- \+ *lemma* interval_integrable_const_iff

Modified src/measure_theory/measure/measure_space.lean




## [2021-11-23 13:11:53](https://github.com/leanprover-community/mathlib/commit/3b13744)
chore(measure_theory/integral): more versions of `integral_finset_sum` ([#10394](https://github.com/leanprover-community/mathlib/pull/10394))
* fix assumptions in existing lemmas (`∀ i ∈ s` instead of `∀ i`);
* add a version for interval integrals.
#### Estimated changes
Modified src/measure_theory/function/l1_space.lean


Modified src/measure_theory/integral/bochner.lean
- \+/\- *lemma* measure_theory.integral_finset_sum

Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* interval_integral.integral_finset_sum



## [2021-11-23 13:11:52](https://github.com/leanprover-community/mathlib/commit/2ec6de7)
feat(topology/connected): sufficient conditions for the preimage of a connected set to be connected ([#10289](https://github.com/leanprover-community/mathlib/pull/10289))
and other simple connectedness results
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.nonempty.preimage'

Modified src/data/set/lattice.lean
- \+ *lemma* disjoint.subset_left_of_subset_union
- \+ *lemma* disjoint.subset_right_of_subset_union

Modified src/topology/connected.lean
- \+ *lemma* is_connected.preimage_of_closed_map
- \+ *lemma* is_connected.preimage_of_open_map
- \+ *lemma* is_preconnected.preimage_of_closed_map
- \+ *lemma* is_preconnected.preimage_of_open_map
- \+ *lemma* is_preconnected.subset_left_of_subset_union
- \+ *lemma* is_preconnected.subset_or_subset
- \+ *lemma* is_preconnected.subset_right_of_subset_union



## [2021-11-23 13:11:50](https://github.com/leanprover-community/mathlib/commit/e8386bd)
feat(group_theory/exponent): Define the exponent of a group ([#10249](https://github.com/leanprover-community/mathlib/pull/10249))
This PR provides the definition and some very basic API for the exponent of a group/monoid.
#### Estimated changes
Modified src/algebra/gcd_monoid/finset.lean
- \+ *theorem* finset.lcm_eq_zero_iff

Modified src/algebra/gcd_monoid/multiset.lean
- \+ *theorem* multiset.lcm_eq_zero_iff

Added src/group_theory/exponent.lean
- \+ *lemma* monoid.exp_eq_one_of_subsingleton
- \+ *lemma* monoid.exponent_dvd_of_forall_pow_eq_one
- \+ *def* monoid.exponent_exists
- \+ *lemma* monoid.exponent_min'
- \+ *lemma* monoid.exponent_min
- \+ *lemma* monoid.exponent_pos_of_exists
- \+ *lemma* monoid.lcm_order_eq_exponent
- \+ *lemma* monoid.lcm_order_of_dvd_exponent
- \+ *lemma* monoid.order_dvd_exponent
- \+ *lemma* monoid.pow_eq_mod_exponent
- \+ *lemma* monoid.pow_exponent_eq_one



## [2021-11-23 13:11:48](https://github.com/leanprover-community/mathlib/commit/cf91773)
refactor(*): split `order_{top,bot}` from `lattice` hierarchy ([#9891](https://github.com/leanprover-community/mathlib/pull/9891))
Rename `bounded_lattice` to `bounded_order`.
Split out `order_{top,bot}` and `bounded_order` from the order hierarchy.
That means that we no longer have `semilattice_{sup,inf}_{top,bot}`, but use the `[order_top]` as a mixin to `semilattice_inf`, for example.
Similarly, `lattice` and `bounded_order` instead of what was before `bounded_lattice`.
Similarly, `distrib_lattice` and `bounded_order` instead of what was before `bounded_distrib_lattice`.
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/associated.lean


Modified src/algebra/big_operators/basic.lean


Modified src/algebra/order/monoid.lean


Modified src/algebra/order/nonneg.lean


Modified src/algebra/tropical/basic.lean


Modified src/analysis/box_integral/box/basic.lean


Modified src/analysis/box_integral/partition/basic.lean


Modified src/analysis/box_integral/partition/filter.lean


Modified src/analysis/normed_space/enorm.lean


Modified src/category_theory/filtered.lean


Modified src/category_theory/limits/lattice.lean
- \+/\- *lemma* category_theory.limits.complete_lattice.coprod_eq_sup
- \+/\- *def* category_theory.limits.complete_lattice.finite_colimit_cocone
- \+/\- *lemma* category_theory.limits.complete_lattice.finite_colimit_eq_finset_univ_sup
- \+/\- *lemma* category_theory.limits.complete_lattice.finite_coproduct_eq_finset_sup
- \+/\- *def* category_theory.limits.complete_lattice.finite_limit_cone
- \+/\- *lemma* category_theory.limits.complete_lattice.finite_limit_eq_finset_univ_inf
- \+/\- *lemma* category_theory.limits.complete_lattice.finite_product_eq_finset_inf
- \+/\- *lemma* category_theory.limits.complete_lattice.prod_eq_inf
- \+/\- *lemma* category_theory.limits.complete_lattice.pullback_eq_inf
- \+/\- *lemma* category_theory.limits.complete_lattice.pushout_eq_sup

Modified src/category_theory/sites/grothendieck.lean
- \+ *lemma* category_theory.grothendieck_topology.le_def

Modified src/category_theory/sites/plus.lean


Modified src/category_theory/sites/pretopology.lean
- \+ *lemma* category_theory.pretopology.le_def

Modified src/category_theory/sites/sheafification.lean


Modified src/category_theory/subobject/lattice.lean


Modified src/combinatorics/colex.lean


Modified src/combinatorics/simple_graph/subgraph.lean


Modified src/data/fin/basic.lean


Modified src/data/finset/basic.lean


Modified src/data/finset/lattice.lean
- \+/\- *lemma* finset.comp_inf_eq_inf_comp
- \+/\- *lemma* finset.comp_inf_eq_inf_comp_of_is_total
- \+/\- *lemma* finset.comp_sup_eq_sup_comp
- \+/\- *lemma* finset.comp_sup_eq_sup_comp_of_is_total
- \+/\- *lemma* finset.disjoint_sup_left
- \+/\- *lemma* finset.disjoint_sup_right
- \+/\- *lemma* finset.sup_finset_image
- \+/\- *lemma* finset.sup_le_of_le_directed

Modified src/data/finset/pairwise.lean
- \+/\- *lemma* set.pairwise_disjoint.image_finset_of_le

Modified src/data/finsupp/basic.lean


Modified src/data/finsupp/lattice.lean
- \+/\- *lemma* finsupp.support_sup

Modified src/data/fintype/basic.lean


Modified src/data/list/min_max.lean


Modified src/data/multiset/basic.lean


Modified src/data/multiset/lattice.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/enat.lean


Modified src/data/part.lean


Modified src/data/pequiv.lean


Modified src/data/pnat/factors.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean


Modified src/data/semiquot.lean


Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* set.Icc_bot_top

Modified src/data/set/pairwise.lean
- \+/\- *lemma* pairwise_disjoint_on
- \+/\- *lemma* pairwise_disjoint_on_bool

Modified src/linear_algebra/linear_pmap.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/function/l1_space.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* measure_theory.simple_func.finset_sup_apply

Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measurable_space_def.lean
- \+ *lemma* measurable_space.le_def

Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/pi_system.lean
- \+ *lemma* measurable_space.dynkin_system.le_def

Modified src/measure_theory/probability_mass_function/basic.lean


Modified src/order/atoms.lean
- \+/\- *lemma* is_atom.disjoint_of_ne
- \+/\- *lemma* is_atom.inf_eq_bot_of_ne
- \+/\- *lemma* is_atom_dual_iff_is_coatom
- \+/\- *lemma* is_coatom.sup_eq_top_of_ne
- \+/\- *lemma* is_coatom_dual_iff_is_atom
- \+/\- *theorem* is_simple_lattice_iff_is_atom_top
- \+/\- *theorem* is_simple_lattice_iff_is_coatom_bot
- \+/\- *theorem* is_simple_lattice_iff_is_simple_lattice_order_dual
- \+/\- *lemma* order_iso.is_atom_iff
- \+/\- *lemma* order_iso.is_atomic_iff
- \+/\- *lemma* order_iso.is_coatom_iff
- \+/\- *lemma* order_iso.is_coatomic_iff
- \+/\- *lemma* order_iso.is_simple_lattice
- \+/\- *lemma* order_iso.is_simple_lattice_iff
- \+/\- *theorem* set.is_simple_lattice_Ici_iff_is_coatom
- \+/\- *theorem* set.is_simple_lattice_Iic_iff_is_atom

Modified src/order/basic.lean
- \+/\- *lemma* pi.le_def

Modified src/order/boolean_algebra.lean
- \+ *def* boolean_algebra.core.sdiff
- \+ *lemma* boolean_algebra.core.sdiff_eq
- \+/\- *lemma* pi.compl_apply

Renamed src/order/bounded_lattice.lean to src/order/bounded_order.lean
- \- *theorem* bounded_lattice.ext
- \+ *theorem* bounded_order.ext
- \+/\- *lemma* eq_bot_of_bot_eq_top
- \+/\- *lemma* eq_top_of_bot_eq_top
- \+ *lemma* inf_eq_bot_iff_le_compl
- \+/\- *structure* is_compl
- \+/\- *lemma* is_compl_bot_top
- \+/\- *lemma* is_compl_top_bot
- \+/\- *theorem* order_bot.ext
- \+/\- *theorem* order_bot.ext_bot
- \+/\- *theorem* order_top.ext
- \+/\- *lemma* subsingleton_iff_bot_eq_top
- \+/\- *lemma* subsingleton_of_bot_eq_top
- \+/\- *lemma* subsingleton_of_top_le_bot

Modified src/order/complete_boolean_algebra.lean


Modified src/order/complete_lattice.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/copy.lean
- \- *def* bounded_lattice.copy
- \+ *def* bounded_order.copy
- \+ *def* lattice.copy

Modified src/order/filter/basic.lean


Modified src/order/filter/germ.lean


Modified src/order/galois_connection.lean
- \- *def* galois_coinsertion.lift_bounded_lattice
- \+ *def* galois_coinsertion.lift_bounded_order
- \- *def* galois_insertion.lift_bounded_lattice
- \+ *def* galois_insertion.lift_bounded_order

Modified src/order/lattice_intervals.lean
- \- *def* set.Icc.bounded_lattice
- \+ *def* set.Icc.bounded_order
- \+/\- *def* set.Icc.order_bot
- \+/\- *def* set.Icc.order_top
- \- *def* set.Icc.semilattice_inf_bot
- \- *def* set.Icc.semilattice_inf_top
- \- *def* set.Icc.semilattice_sup_bot
- \- *def* set.Icc.semilattice_sup_top
- \- *def* set.Ico.semilattice_inf_bot
- \- *def* set.Ioc.semilattice_sup_top

Modified src/order/modular_lattice.lean


Modified src/order/partial_sups.lean
- \+/\- *lemma* partial_sups_disjoint_of_disjoint
- \+/\- *lemma* partial_sups_eq_sup_range

Modified src/order/preorder_hom.lean


Modified src/order/rel_iso.lean
- \+/\- *lemma* disjoint.map_order_iso
- \+/\- *lemma* disjoint_map_order_iso_iff

Modified src/order/succ_pred.lean


Modified src/order/sup_indep.lean
- \+/\- *lemma* finset.sup_indep.bUnion
- \+/\- *lemma* finset.sup_indep.sup
- \+/\- *lemma* finset.sup_indep_iff_pairwise_disjoint

Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/tactic/monotonicity/basic.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* nhds_bot_basis
- \+/\- *lemma* nhds_bot_basis_Iic
- \+/\- *lemma* nhds_top_basis
- \+/\- *lemma* nhds_top_basis_Ici

Modified src/topology/compacts.lean


Modified src/topology/dense_embedding.lean


Modified src/topology/discrete_quotient.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/metric_space/contracting.lean


Modified src/topology/order.lean


Modified test/transport/basic.lean
- \+ *def* sup.map
- \- *def* sup_top.map



## [2021-11-23 11:49:18](https://github.com/leanprover-community/mathlib/commit/3fee4b9)
chore(control/random): Move from `system.random.basic` ([#10408](https://github.com/leanprover-community/mathlib/pull/10408))
The top folder `system` contains a single file, apparently because it mimics Lean core's organisation. This moves it under `control.` and gets rid of one top folder.
#### Estimated changes
Renamed src/system/random/basic.lean to src/control/random.lean


Modified src/testing/slim_check/gen.lean


Modified test/random.lean




## [2021-11-23 11:49:16](https://github.com/leanprover-community/mathlib/commit/b1a9c2e)
feat(analysis/normed_space/multilinear): add `norm_mk_pi_field` ([#10396](https://github.com/leanprover-community/mathlib/pull/10396))
Also upgrade the corresponding equivalence to a `linear_isometry`.
#### Estimated changes
Modified src/analysis/calculus/iterated_deriv.lean


Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.self_comp_symm
- \+ *lemma* linear_isometry_equiv.symm_comp_self

Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* continuous_multilinear_map.norm_mk_pi_field



## [2021-11-23 11:49:15](https://github.com/leanprover-community/mathlib/commit/87b0084)
chore(field_theory/separable): generalize theorems ([#10337](https://github.com/leanprover-community/mathlib/pull/10337))
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+/\- *theorem* polynomial.not_is_unit_X_sub_C

Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/finite/basic.lean


Modified src/field_theory/primitive_element.lean


Modified src/field_theory/separable.lean
- \+/\- *theorem* irreducible.separable
- \+/\- *theorem* polynomial.coeff_contract
- \+ *theorem* polynomial.contract_expand
- \+/\- *lemma* polynomial.count_roots_le_one
- \+/\- *lemma* polynomial.eq_X_sub_C_of_separable_of_root_eq
- \+/\- *theorem* polynomial.exists_separable_of_irreducible
- \+/\- *theorem* polynomial.expand_char
- \+/\- *theorem* polynomial.expand_contract
- \+ *theorem* polynomial.expand_zero
- \+/\- *theorem* polynomial.is_unit_or_eq_zero_of_separable_expand
- \+/\- *theorem* polynomial.map_expand_pow_char
- \+/\- *lemma* polynomial.multiplicity_le_one_of_separable
- \+/\- *lemma* polynomial.nodup_of_separable_prod
- \+/\- *lemma* polynomial.nodup_roots
- \- *lemma* polynomial.not_unit_X_sub_C
- \+/\- *theorem* polynomial.of_irreducible_expand
- \+/\- *theorem* polynomial.of_irreducible_expand_pow
- \+/\- *lemma* polynomial.root_multiplicity_le_one_of_separable
- \+/\- *lemma* polynomial.separable.squarefree
- \+/\- *lemma* polynomial.separable_X_pow_sub_C_unit
- \+ *lemma* polynomial.separable_of_subsingleton
- \- *lemma* polynomial.squarefree_X_pow_sub_C
- \+/\- *theorem* polynomial.unique_separable_of_irreducible

Modified src/field_theory/separable_degree.lean


Modified src/ring_theory/norm.lean


Modified src/ring_theory/polynomial/cyclotomic.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/trace.lean




## [2021-11-23 11:49:14](https://github.com/leanprover-community/mathlib/commit/9cf6766)
feat(order/filter/pi): define `filter.pi` and prove some properties ([#10323](https://github.com/leanprover-community/mathlib/pull/10323))
#### Estimated changes
Modified src/analysis/box_integral/box/subbox_induction.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/constructions/pi.lean
- \- *lemma* measure_theory.measure.ae_pi_le_infi_comap
- \+ *lemma* measure_theory.measure.ae_pi_le_pi

Modified src/measure_theory/constructions/prod.lean


Modified src/measure_theory/function/strongly_measurable.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/order/filter/basic.lean
- \- *lemma* filter.Coprod_mono
- \- *lemma* filter.Coprod_ne_bot
- \- *lemma* filter.Coprod_ne_bot_iff'
- \- *lemma* filter.Coprod_ne_bot_iff
- \- *lemma* filter.compl_mem_Coprod_iff
- \- *lemma* filter.map_pi_map_Coprod_le
- \- *lemma* filter.mem_Coprod_iff
- \- *lemma* filter.ne_bot.Coprod
- \- *lemma* filter.tendsto.pi_map_Coprod

Modified src/order/filter/cofinite.lean


Added src/order/filter/pi.lean
- \+ *lemma* filter.Coprod_mono
- \+ *lemma* filter.Coprod_ne_bot
- \+ *lemma* filter.Coprod_ne_bot_iff'
- \+ *lemma* filter.Coprod_ne_bot_iff
- \+ *lemma* filter.compl_mem_Coprod_iff
- \+ *lemma* filter.le_pi
- \+ *lemma* filter.map_pi_map_Coprod_le
- \+ *lemma* filter.mem_Coprod_iff
- \+ *lemma* filter.mem_of_pi_mem_pi
- \+ *lemma* filter.mem_pi'
- \+ *lemma* filter.mem_pi
- \+ *lemma* filter.mem_pi_of_mem
- \+ *lemma* filter.ne_bot.Coprod
- \+ *def* filter.pi
- \+ *lemma* filter.pi_eq_bot
- \+ *lemma* filter.pi_inf_principal_pi_eq_bot
- \+ *lemma* filter.pi_inf_principal_pi_ne_bot
- \+ *lemma* filter.pi_inf_principal_univ_pi_eq_bot
- \+ *lemma* filter.pi_inf_principal_univ_pi_ne_bot
- \+ *lemma* filter.pi_mem_pi
- \+ *lemma* filter.pi_mem_pi_iff
- \+ *lemma* filter.pi_mono
- \+ *lemma* filter.pi_ne_bot
- \+ *lemma* filter.tendsto.pi_map_Coprod
- \+ *lemma* filter.tendsto_eval_pi
- \+ *lemma* filter.tendsto_pi

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/algebra/ordered/monotone_convergence.lean


Modified src/topology/algebra/weak_dual_topology.lean


Modified src/topology/bases.lean


Modified src/topology/constructions.lean
- \+/\- *lemma* interior_pi_set
- \+ *lemma* mem_nhds_of_pi_mem_nhds
- \- *lemma* mem_nhds_pi
- \+/\- *lemma* set_pi_mem_nhds_iff
- \- *lemma* tendsto_pi
- \+ *lemma* tendsto_pi_nhds

Modified src/topology/continuous_on.lean
- \- *lemma* nhds_within_pi_univ_eq_bot

Modified src/topology/sequences.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/pi.lean




## [2021-11-23 11:49:13](https://github.com/leanprover-community/mathlib/commit/33ea401)
feat(linear_algebra/affine_space/barycentric_coords): barycentric coordinates are ratio of determinants ([#10320](https://github.com/leanprover-community/mathlib/pull/10320))
The main goal of this PR is the new lemma `affine_basis.det_smul_coords_eq_camer_coords`
A secondary goal is a minor refactor of barycentric coordinates so that they are associated to a new structure `affine_basis`. As well as making the API for affine spaces more similar to that of modules, this enables an extremely useful dot notation.
The work here could easily be split into two PRs and I will happily do so if requested.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/analysis/convex/combination.lean
- \+/\- *lemma* convex_hull_affine_basis_eq_nonneg_barycentric

Modified src/analysis/normed_space/add_torsor_bases.lean
- \+/\- *lemma* continuous_barycentric_coord

Modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* affine_basis.affine_combination_coord_eq_self
- \+ *lemma* affine_basis.basis_of_apply
- \+ *lemma* affine_basis.coe_coord_of_subsingleton_eq_one
- \+ *lemma* affine_basis.coord_apply
- \+ *lemma* affine_basis.coord_apply_combination_of_mem
- \+ *lemma* affine_basis.coord_apply_combination_of_not_mem
- \+ *lemma* affine_basis.coord_apply_eq
- \+ *lemma* affine_basis.coord_apply_neq
- \+ *lemma* affine_basis.coords_apply
- \+ *lemma* affine_basis.det_smul_coords_eq_cramer_coords
- \+ *lemma* affine_basis.is_unit_to_matrix
- \+ *lemma* affine_basis.sum_coord_apply_eq_one
- \+ *lemma* affine_basis.surjective_coord
- \+ *lemma* affine_basis.to_matrix_apply
- \+ *lemma* affine_basis.to_matrix_inv_vec_mul_to_matrix
- \+ *lemma* affine_basis.to_matrix_mul_to_matrix
- \+ *lemma* affine_basis.to_matrix_self
- \+ *lemma* affine_basis.to_matrix_vec_mul_coords
- \+ *structure* affine_basis
- \- *lemma* affine_combination_barycentric_coord_eq_self
- \- *lemma* barycentric_coord_apply
- \- *lemma* barycentric_coord_apply_combination_of_mem
- \- *lemma* barycentric_coord_apply_combination_of_not_mem
- \- *lemma* barycentric_coord_apply_eq
- \- *lemma* barycentric_coord_apply_neq
- \- *lemma* basis_of_aff_ind_span_eq_top_apply
- \- *lemma* coe_barycentric_coord_of_subsingleton_eq_one
- \- *lemma* sum_barycentric_coord_apply_eq_one
- \- *lemma* surjective_barycentric_coord

Modified src/linear_algebra/affine_space/basic.lean


Modified src/linear_algebra/matrix/adjugate.lean
- \+ *lemma* matrix.cramer_transpose_apply

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.det_smul_inv_vec_mul_eq_cramer_transpose



## [2021-11-23 11:49:12](https://github.com/leanprover-community/mathlib/commit/d94772b)
feat(algebra/big_operators/finprod): add finprod_div_distrib and finsum_sub_distrib ([#10044](https://github.com/leanprover-community/mathlib/pull/10044))
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_div_distrib
- \+ *lemma* finprod_mem_div_distrib
- \+ *lemma* finprod_mem_inv_distrib
- \+ *lemma* mul_equiv.map_finprod_mem



## [2021-11-23 09:38:33](https://github.com/leanprover-community/mathlib/commit/ac71292)
chore(measure_theory/integral): generalize `integral_smul_const` ([#10411](https://github.com/leanprover-community/mathlib/pull/10411))
* generalize to `is_R_or_C`;
* add an `interval_integral` version.
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \- *lemma* interval_integral.integral_const_mul
- \- *lemma* interval_integral.integral_div
- \- *lemma* interval_integral.integral_mul_const

Modified src/measure_theory/function/conditional_expectation.lean


Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* interval_integral.integral_const_mul
- \+ *lemma* interval_integral.integral_div
- \+ *lemma* interval_integral.integral_mul_const
- \+ *lemma* interval_integral.integral_smul_const

Modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* integral_smul_const



## [2021-11-23 09:38:32](https://github.com/leanprover-community/mathlib/commit/8f681f1)
chore(data/complex): add a few simp lemmas ([#10395](https://github.com/leanprover-community/mathlib/pull/10395))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *lemma* complex.abs_pow
- \+ *lemma* complex.abs_zpow

Modified src/data/complex/exponential.lean
- \+/\- *lemma* complex.abs_cos_add_sin_mul_I
- \+ *lemma* complex.abs_exp_of_real_mul_I



## [2021-11-23 09:38:31](https://github.com/leanprover-community/mathlib/commit/4d5d770)
feat(data/complex/exponential): Add lemma add_one_le_exp ([#10358](https://github.com/leanprover-community/mathlib/pull/10358))
This PR resolves https://github.com/leanprover-community/mathlib/blob/master/src/data/complex/exponential.lean#L1140
#### Estimated changes
Modified src/analysis/special_functions/exp.lean


Modified src/data/complex/exponential.lean
- \+ *lemma* real.add_one_le_exp
- \+ *lemma* real.add_one_le_exp_of_nonpos
- \+ *lemma* real.exp_bound'
- \+ *lemma* real.exp_bound_div_one_sub_of_interval
- \+ *lemma* real.exp_bound_div_one_sub_of_interval_approx
- \+ *lemma* real.one_sub_le_exp_minus_of_pos



## [2021-11-23 07:23:05](https://github.com/leanprover-community/mathlib/commit/6050f9d)
feat(algebraic_geometry, category_theory): SheafedSpace has colimits ([#10401](https://github.com/leanprover-community/mathlib/pull/10401))
#### Estimated changes
Modified src/algebraic_geometry/sheafed_space.lean


Modified src/category_theory/limits/creates.lean
- \+ *def* category_theory.creates_colimit_of_fully_faithful_of_iso
- \+ *def* category_theory.creates_colimit_of_fully_faithful_of_lift

Modified src/topology/sheaves/limits.lean
- \+ *lemma* Top.is_sheaf_of_is_limit
- \+ *lemma* Top.limit_is_sheaf

Modified src/topology/sheaves/sheaf_condition/sites.lean
- \+ *def* Top.presheaf.Sheaf_spaces_equiv_sheaf_sites
- \+ *def* Top.presheaf.Sheaf_spaces_equiv_sheaf_sites_functor_forget
- \+ *def* Top.presheaf.Sheaf_spaces_equiv_sheaf_sites_inverse_forget
- \- *def* Top.presheaf.Sheaf_spaces_equivelence_sheaf_sites



## [2021-11-23 07:23:04](https://github.com/leanprover-community/mathlib/commit/ca7347c)
refactor(ring_theory/sub[semi]ring): move pointwise instances to their own file ([#10347](https://github.com/leanprover-community/mathlib/pull/10347))
This matches how we have separate pointwise files for `submonoid` and `subgroup`.
All the new lemmas are direct copies of the subgroup lemmas.
#### Estimated changes
Modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean


Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/category/CommRing/limits.lean


Modified src/algebra/char_p/subring.lean


Modified src/algebra/group_ring_action.lean
- \- *lemma* subring.coe_pointwise_smul
- \- *lemma* subring.pointwise_smul_to_add_subgroup
- \- *lemma* subring.pointwise_smul_to_subsemiring
- \- *lemma* subring.smul_mem_pointwise_smul
- \- *lemma* subsemiring.coe_pointwise_smul
- \- *lemma* subsemiring.pointwise_smul_to_add_submonoid
- \- *lemma* subsemiring.smul_mem_pointwise_smul

Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/deprecated/subring.lean


Modified src/ring_theory/perfection.lean


Renamed src/ring_theory/subring.lean to src/ring_theory/subring/basic.lean


Added src/ring_theory/subring/pointwise.lean
- \+ *lemma* subring.coe_pointwise_smul
- \+ *lemma* subring.le_pointwise_smul_iff₀
- \+ *lemma* subring.mem_inv_pointwise_smul_iff
- \+ *lemma* subring.mem_inv_pointwise_smul_iff₀
- \+ *lemma* subring.mem_pointwise_smul_iff_inv_smul_mem
- \+ *lemma* subring.mem_pointwise_smul_iff_inv_smul_mem₀
- \+ *lemma* subring.pointwise_smul_def
- \+ *lemma* subring.pointwise_smul_le_iff₀
- \+ *lemma* subring.pointwise_smul_le_pointwise_smul_iff
- \+ *lemma* subring.pointwise_smul_le_pointwise_smul_iff₀
- \+ *lemma* subring.pointwise_smul_subset_iff
- \+ *lemma* subring.pointwise_smul_to_add_subgroup
- \+ *lemma* subring.pointwise_smul_to_subsemiring
- \+ *lemma* subring.smul_mem_pointwise_smul
- \+ *lemma* subring.smul_mem_pointwise_smul_iff
- \+ *lemma* subring.smul_mem_pointwise_smul_iff₀
- \+ *lemma* subring.subset_pointwise_smul_iff

Renamed src/ring_theory/subsemiring.lean to src/ring_theory/subsemiring/basic.lean


Added src/ring_theory/subsemiring/pointwise.lean
- \+ *lemma* subsemiring.coe_pointwise_smul
- \+ *lemma* subsemiring.le_pointwise_smul_iff₀
- \+ *lemma* subsemiring.mem_inv_pointwise_smul_iff
- \+ *lemma* subsemiring.mem_inv_pointwise_smul_iff₀
- \+ *lemma* subsemiring.mem_pointwise_smul_iff_inv_smul_mem
- \+ *lemma* subsemiring.mem_pointwise_smul_iff_inv_smul_mem₀
- \+ *lemma* subsemiring.pointwise_smul_def
- \+ *lemma* subsemiring.pointwise_smul_le_iff₀
- \+ *lemma* subsemiring.pointwise_smul_le_pointwise_smul_iff
- \+ *lemma* subsemiring.pointwise_smul_le_pointwise_smul_iff₀
- \+ *lemma* subsemiring.pointwise_smul_subset_iff
- \+ *lemma* subsemiring.pointwise_smul_to_add_submonoid
- \+ *lemma* subsemiring.smul_mem_pointwise_smul
- \+ *lemma* subsemiring.smul_mem_pointwise_smul_iff
- \+ *lemma* subsemiring.smul_mem_pointwise_smul_iff₀
- \+ *lemma* subsemiring.subset_pointwise_smul_iff

Modified src/topology/algebra/ring.lean


Modified src/topology/instances/real.lean




## [2021-11-23 07:23:02](https://github.com/leanprover-community/mathlib/commit/a586681)
feat(category_theory/limits/shapes): Multiequalizer is the equalizer ([#10267](https://github.com/leanprover-community/mathlib/pull/10267))
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/multiequalizer.lean
- \+ *def* category_theory.limits.multicoequalizer.iso_coequalizer
- \+ *def* category_theory.limits.multicoequalizer.sigma_π
- \+ *lemma* category_theory.limits.multicoequalizer.ι_sigma_π
- \+ *def* category_theory.limits.multicofork.of_sigma_cofork
- \+ *lemma* category_theory.limits.multicofork.of_sigma_cofork_ι_app_left
- \+ *lemma* category_theory.limits.multicofork.of_sigma_cofork_ι_app_right
- \+ *lemma* category_theory.limits.multicofork.sigma_condition
- \+ *def* category_theory.limits.multicofork.to_sigma_cofork
- \+ *lemma* category_theory.limits.multicofork.to_sigma_cofork_ι_app_one
- \+ *lemma* category_theory.limits.multicofork.to_sigma_cofork_ι_app_zero
- \+ *abbreviation* category_theory.limits.multicofork
- \- *def* category_theory.limits.multicofork
- \+ *def* category_theory.limits.multicospan_index.fst_pi_map
- \+ *lemma* category_theory.limits.multicospan_index.fst_pi_map_π
- \+ *def* category_theory.limits.multicospan_index.multifork_equiv_pi_fork
- \+ *def* category_theory.limits.multicospan_index.of_pi_fork_functor
- \+ *def* category_theory.limits.multicospan_index.parallel_pair_diagram
- \+ *def* category_theory.limits.multicospan_index.snd_pi_map
- \+ *lemma* category_theory.limits.multicospan_index.snd_pi_map_π
- \+ *def* category_theory.limits.multicospan_index.to_pi_fork_functor
- \+ *def* category_theory.limits.multiequalizer.iso_equalizer
- \+ *def* category_theory.limits.multiequalizer.ι_pi
- \+ *lemma* category_theory.limits.multiequalizer.ι_pi_π
- \+ *def* category_theory.limits.multifork.of_pi_fork
- \+ *lemma* category_theory.limits.multifork.of_pi_fork_π_app_left
- \+ *lemma* category_theory.limits.multifork.of_pi_fork_π_app_right
- \+ *lemma* category_theory.limits.multifork.pi_condition
- \+ *def* category_theory.limits.multifork.to_pi_fork
- \+ *lemma* category_theory.limits.multifork.to_pi_fork_π_app_one
- \+ *lemma* category_theory.limits.multifork.to_pi_fork_π_app_zero
- \+ *abbreviation* category_theory.limits.multifork
- \- *def* category_theory.limits.multifork
- \+ *def* category_theory.limits.multispan_index.fst_sigma_map
- \+ *def* category_theory.limits.multispan_index.multicofork_equiv_sigma_cofork
- \+ *def* category_theory.limits.multispan_index.of_sigma_cofork_functor
- \+ *abbreviation* category_theory.limits.multispan_index.parallel_pair_diagram
- \+ *def* category_theory.limits.multispan_index.snd_sigma_map
- \+ *def* category_theory.limits.multispan_index.to_sigma_cofork_functor
- \+ *lemma* category_theory.limits.multispan_index.ι_fst_sigma_map
- \+ *lemma* category_theory.limits.multispan_index.ι_snd_sigma_map



## [2021-11-23 05:35:13](https://github.com/leanprover-community/mathlib/commit/6dddef2)
feat(topology/metric_space): range of a cauchy seq is bounded ([#10423](https://github.com/leanprover-community/mathlib/pull/10423))
#### Estimated changes
Modified src/order/filter/cofinite.lean
- \+ *lemma* filter.has_basis_cofinite

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.bounded_range_of_cauchy_map_cofinite
- \+ *lemma* metric.bounded_range_of_tendsto_cofinite
- \+ *lemma* metric.bounded_range_of_tendsto_cofinite_uniformity

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *lemma* filter.has_basis.cauchy_iff



## [2021-11-23 01:33:14](https://github.com/leanprover-community/mathlib/commit/f684f61)
feat(algebra/algebra/spectrum): define spectrum and prove basic prope... ([#10390](https://github.com/leanprover-community/mathlib/pull/10390))
…rties
Define the resolvent set and the spectrum of an element of an algebra as
a set of elements in the scalar ring. We prove a few basic facts
including that additive cosets of the spectrum commute with the
spectrum, that is, r + σ a = σ (r ⬝ 1 + a). Similarly, multiplicative
cosets of the spectrum also commute when the element r is a unit of
the scalar ring R. Finally, we also show that the units of R in
σ (a*b) coincide with those of σ (b*a).
#### Estimated changes
Added src/algebra/algebra/spectrum.lean
- \+ *lemma* is_unit.smul_iff
- \+ *lemma* is_unit.smul_sub_iff_sub_inv_smul
- \+ *def* resolvent
- \+ *lemma* spectrum.add_mem_iff
- \+ *theorem* spectrum.left_add_coset_eq
- \+ *lemma* spectrum.mem_iff
- \+ *lemma* spectrum.mem_resolvent_iff
- \+ *lemma* spectrum.mem_resolvent_of_left_right_inverse
- \+ *lemma* spectrum.not_mem_iff
- \+ *theorem* spectrum.preimage_units_mul_eq_swap_mul
- \+ *theorem* spectrum.smul_eq_smul
- \+ *lemma* spectrum.smul_mem_smul_iff
- \+ *theorem* spectrum.unit_mem_mul_iff_mem_swap_mul
- \+ *def* spectrum



## [2021-11-22 22:48:19](https://github.com/leanprover-community/mathlib/commit/e59e03f)
feat(measure_theory/integral/interval_integral): add an alternative definition ([#10380](https://github.com/leanprover-community/mathlib/pull/10380))
Prove that `∫ x in a..b, f x ∂μ = sgn a b • ∫ x in Ι a b, f x ∂μ`,
where `sgn a b = if a ≤ b then 1 else -1`.
#### Estimated changes
Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* interval_integral.interval_integral_eq_integral_interval_oc



## [2021-11-22 19:46:14](https://github.com/leanprover-community/mathlib/commit/2f5af98)
feat(data/nat/prime): prime divisors ([#10318](https://github.com/leanprover-community/mathlib/pull/10318))
Adding some basic lemmas about `factors` and `factors.to_finset`
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* list.to_finset_repeat_of_ne_zero

Modified src/data/nat/gcd.lean
- \+ *lemma* nat.eq_one_of_dvd_coprimes

Modified src/data/nat/prime.lean
- \+ *lemma* nat.coprime_factors_disjoint
- \+ *lemma* nat.dvd_of_mem_factors
- \+ *lemma* nat.factors_mul_of_coprime
- \+ *lemma* nat.factors_mul_of_pos
- \+ *lemma* nat.mem_factors_mul_of_pos
- \+ *lemma* nat.prime_pow_prime_divisor

Modified src/number_theory/divisors.lean
- \+ *lemma* nat.prime_divisors_eq_to_filter_divisors_prime



## [2021-11-22 18:50:52](https://github.com/leanprover-community/mathlib/commit/317483a)
feat(analysis/calculus/parametric_integral): generalize, rename ([#10397](https://github.com/leanprover-community/mathlib/pull/10397))
* add `integral` to lemma names;
* a bit more general
  `has_fderiv_at_integral_of_dominated_loc_of_lip'`: only require an
  estimate on `∥F x a - F x₀ a∥` instead of `∥F x a - F y a∥`;
* generalize the `deriv` lemmas to `F : 𝕜 → α → E`, `[is_R_or_C 𝕜]`.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at.le_of_lip'

Modified src/analysis/calculus/parametric_integral.lean
- \+ *lemma* has_deriv_at_integral_of_dominated_loc_of_deriv_le
- \+ *lemma* has_deriv_at_integral_of_dominated_loc_of_lip
- \- *lemma* has_deriv_at_of_dominated_loc_of_deriv_le
- \- *lemma* has_deriv_at_of_dominated_loc_of_lip
- \+ *lemma* has_fderiv_at_integral_of_dominated_loc_of_lip'
- \+ *lemma* has_fderiv_at_integral_of_dominated_loc_of_lip
- \+ *lemma* has_fderiv_at_integral_of_dominated_of_fderiv_le
- \- *lemma* has_fderiv_at_of_dominated_loc_of_lip'
- \- *lemma* has_fderiv_at_of_dominated_loc_of_lip
- \- *lemma* has_fderiv_at_of_dominated_of_fderiv_le

Modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* continuous_linear_map.integrable_comp
- \+/\- *lemma* measure_theory.integrable.apply_continuous_linear_map

Modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* continuous_linear_map.integral_apply



## [2021-11-22 16:51:24](https://github.com/leanprover-community/mathlib/commit/d2ebcad)
fix(undergrad.yaml): reinstate deleted entry ([#10416](https://github.com/leanprover-community/mathlib/pull/10416))
Revert an (I assume accidental?) deletion in [#10415](https://github.com/leanprover-community/mathlib/pull/10415).
cc @PatrickMassot
#### Estimated changes
Modified docs/undergrad.yaml




## [2021-11-22 13:14:41](https://github.com/leanprover-community/mathlib/commit/c896162)
feat(data/finset/basic) eq_of_mem_singleton ([#10414](https://github.com/leanprover-community/mathlib/pull/10414))
The `finset` equivalent of [set.eq_of_mem_singleton](https://leanprover-community.github.io/mathlib_docs/find/set.eq_of_mem_singleton/src)
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* finset.eq_of_mem_singleton



## [2021-11-22 11:23:11](https://github.com/leanprover-community/mathlib/commit/d8d0c59)
chore(algebra/opposites): split group actions and division_ring into their own files ([#10383](https://github.com/leanprover-community/mathlib/pull/10383))
This splits out `group_theory.group_action.opposite` and `algebra.field.opposite` from `algebra.opposites`.
The motivation is to make opposite actions available slightly earlier in the import graph.
We probably want to split out `ring` at some point too, but that's likely a more annoying change so I've left it for future work.
These lemmas are just moved, and some `_root_` prefixes eliminated by removing the surrounding `namespace`.
#### Estimated changes
Modified src/algebra/char_p/invertible.lean


Modified src/algebra/continued_fractions/basic.lean


Modified src/algebra/euclidean_domain.lean


Renamed src/algebra/field.lean to src/algebra/field/basic.lean


Added src/algebra/field/opposite.lean


Modified src/algebra/module/opposites.lean


Modified src/algebra/opposites.lean
- \- *lemma* mul_opposite.op_smul_eq_mul

Modified src/algebra/order/field.lean


Modified src/algebra/periodic.lean


Modified src/algebra/smul_with_zero.lean


Modified src/algebra/star/basic.lean


Modified src/data/equiv/ring.lean


Modified src/data/equiv/transfer_instance.lean


Added src/group_theory/group_action/opposite.lean
- \+ *lemma* op_smul_eq_mul

Modified src/group_theory/group_action/prod.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/number_theory/number_field.lean


Modified src/number_theory/pythagorean_triples.lean




## [2021-11-22 11:23:10](https://github.com/leanprover-community/mathlib/commit/2aea996)
feat(data): define a `fun_like` class of bundled homs (function + proofs) ([#10286](https://github.com/leanprover-community/mathlib/pull/10286))
This PR introduces a class `fun_like` for types of bundled homomorphisms, like `set_like` is for bundled subobjects. This should be useful by itself, but an important use I see for it is the per-morphism class refactor, see [#9888](https://github.com/leanprover-community/mathlib/pull/9888).
Also, `coe_fn_coe_base` now has an appropriately low priority, so it doesn't take precedence over `fun_like.has_coe_to_fun`.
#### Estimated changes
Added src/data/fun_like.lean
- \+ *structure* cooler_hom
- \+ *lemma* do_something
- \+ *theorem* fun_like.coe_fn_eq
- \+ *theorem* fun_like.coe_injective
- \+ *theorem* fun_like.ext'
- \+ *theorem* fun_like.ext'_iff
- \+ *theorem* fun_like.ext
- \+ *theorem* fun_like.ext_iff
- \+ *lemma* map_cool
- \+ *lemma* map_op



## [2021-11-22 09:54:52](https://github.com/leanprover-community/mathlib/commit/7a5fac3)
feat(ring_theory/roots_of_unity): primitive root lemmas ([#10356](https://github.com/leanprover-community/mathlib/pull/10356))
From the flt-regular project.
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* is_primitive_root.eq_order_of
- \+ *lemma* is_primitive_root.map_iff_of_injective
- \+ *lemma* is_primitive_root.map_of_injective
- \+ *lemma* is_primitive_root.of_map_of_injective
- \+ *lemma* is_primitive_root.of_subsingleton
- \+ *lemma* is_primitive_root.unique
- \+ *lemma* is_primitive_root.zero



## [2021-11-22 08:59:57](https://github.com/leanprover-community/mathlib/commit/9f07579)
docs(undergrad): add urls in linear algebra ([#10415](https://github.com/leanprover-community/mathlib/pull/10415))
This uses the new possibility to put urls in `undergrad.yaml` hoping to help describing what is meant to be formalized. We should probably create wiki pages for some cases that are not so clear even with a url. There is one case where I could find only a French page and some cases where I couldn't find anything. Amazingly "endormorphism exponential" is such a case, but hopefully this example is already clear. Another kind of problematic item is the "example" item in the representation section. Presumably it should be removed and replaced with a couple of explicit examples such as "standard representation of a matrix group" or "permutation representation".
#### Estimated changes
Modified docs/undergrad.yaml




## [2021-11-22 00:26:55](https://github.com/leanprover-community/mathlib/commit/9277d4b)
chore(data/finset/basic): finset.prod -> finset.product in module docstring ([#10413](https://github.com/leanprover-community/mathlib/pull/10413))
#### Estimated changes
Modified src/data/finset/basic.lean




## [2021-11-21 22:33:27](https://github.com/leanprover-community/mathlib/commit/d17db71)
chore(*): golf proofs about `filter.Coprod` ([#10400](https://github.com/leanprover-community/mathlib/pull/10400))
Also add some supporting lemmas.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.coe_pi_finset

Modified src/data/pi.lean
- \+ *lemma* function.bijective_pi_map
- \+ *lemma* function.injective_pi_map
- \+ *lemma* function.surjective_pi_map

Modified src/data/set/finite.lean


Modified src/order/boolean_algebra.lean
- \+ *theorem* compl_surjective

Modified src/order/filter/basic.lean
- \+ *lemma* filter.compl_mem_Coprod_iff

Modified src/order/filter/cofinite.lean


Modified src/topology/subset_properties.lean




## [2021-11-21 22:33:26](https://github.com/leanprover-community/mathlib/commit/d98b8e0)
feat(linear_algebra/bilinear_map): semilinearize bilinear maps ([#10373](https://github.com/leanprover-community/mathlib/pull/10373))
This PR generalizes most of `linear_algebra/bilinear_map` to semilinear maps. Along the way, we introduce an instance for `module S (E →ₛₗ[σ] F)`, with `σ : R →+* S`. This allows us to define "semibilinear" maps of type `E →ₛₗ[σ] F →ₛₗ[ρ] G`, where `E`, `F` and `G` are modules over `R₁`, `R₂` and `R₃` respectively, and `σ : R₁ →+* R₃` and `ρ : R₂ →+* R₃`. See `mk₂'ₛₗ` to see how to construct such a map.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+/\- *lemma* linear_map.coe_smul
- \+/\- *theorem* linear_map.comp_smul
- \+/\- *lemma* linear_map.smul_apply
- \+/\- *theorem* linear_map.smul_comp

Modified src/linear_algebra/bilinear_map.lean
- \+/\- *def* linear_map.compl₂
- \+/\- *theorem* linear_map.compl₂_apply
- \+/\- *def* linear_map.compr₂
- \+/\- *theorem* linear_map.compr₂_apply
- \+/\- *theorem* linear_map.ext₂
- \+/\- *def* linear_map.flip
- \+/\- *theorem* linear_map.flip_apply
- \+/\- *theorem* linear_map.flip_inj
- \+/\- *def* linear_map.lcomp
- \+/\- *theorem* linear_map.lcomp_apply
- \+ *def* linear_map.lcompₛₗ
- \+ *theorem* linear_map.lcompₛₗ_apply
- \+/\- *def* linear_map.lflip
- \+/\- *def* linear_map.llcomp
- \+/\- *theorem* linear_map.llcomp_apply
- \+/\- *theorem* linear_map.map_add₂
- \+/\- *theorem* linear_map.map_neg₂
- \+/\- *theorem* linear_map.map_smul₂
- \+ *theorem* linear_map.map_smulₛₗ₂
- \+/\- *theorem* linear_map.map_sub₂
- \+/\- *theorem* linear_map.map_sum₂
- \+/\- *theorem* linear_map.map_zero₂
- \+/\- *def* linear_map.mk₂'
- \+ *def* linear_map.mk₂'ₛₗ
- \+ *theorem* linear_map.mk₂'ₛₗ_apply
- \+/\- *def* linear_map.mk₂



## [2021-11-21 21:47:34](https://github.com/leanprover-community/mathlib/commit/8f07d75)
feat(measure_theory/covering/differentiation): differentiation of measures ([#10101](https://github.com/leanprover-community/mathlib/pull/10101))
If `ρ` and `μ` are two Radon measures on a finite-dimensional normed real vector space, then for `μ`-almost every `x`, the ratio `ρ (B (x, r)) / μ (B(x,r))` converges when `r` tends to `0`, towards the Radon-Nikodym derivative of `ρ` with respect to `μ`. This is the main theorem on differentiation of measures.
The convergence in fact holds for more general families of sets than balls, called Vitali families (the fact that balls form a Vitali family is a restatement of the Besicovitch covering theorem). The general version of the differentation of measures theorem is proved in this PR, following [Federer, geometric measure theory].
#### Estimated changes
Added src/measure_theory/covering/differentiation.lean
- \+ *theorem* vitali_family.ae_eventually_measure_pos
- \+ *lemma* vitali_family.ae_eventually_measure_zero_of_singular
- \+ *theorem* vitali_family.ae_measurable_lim_ratio
- \+ *theorem* vitali_family.ae_tendsto_div
- \+ *lemma* vitali_family.ae_tendsto_lim_ratio
- \+ *lemma* vitali_family.ae_tendsto_lim_ratio_meas
- \+ *theorem* vitali_family.ae_tendsto_rn_deriv
- \+ *theorem* vitali_family.ae_tendsto_rn_deriv_of_absolutely_continuous
- \+ *theorem* vitali_family.eventually_measure_lt_top
- \+ *lemma* vitali_family.exists_measurable_supersets_lim_ratio
- \+ *lemma* vitali_family.le_mul_with_density
- \+ *lemma* vitali_family.lim_ratio_meas_measurable
- \+ *lemma* vitali_family.measure_le_mul_of_subset_lim_ratio_meas_lt
- \+ *theorem* vitali_family.measure_le_of_frequently_le
- \+ *lemma* vitali_family.measure_lim_ratio_meas_top
- \+ *lemma* vitali_family.measure_lim_ratio_meas_zero
- \+ *lemma* vitali_family.mul_measure_le_of_subset_lt_lim_ratio_meas
- \+ *theorem* vitali_family.null_of_frequently_le_of_frequently_ge
- \+ *lemma* vitali_family.with_density_le_mul
- \+ *theorem* vitali_family.with_density_lim_ratio_meas_eq

Modified src/measure_theory/covering/vitali_family.lean




## [2021-11-21 20:56:17](https://github.com/leanprover-community/mathlib/commit/8ee634b)
feat(measure_theory): define volume on `complex` ([#10403](https://github.com/leanprover-community/mathlib/pull/10403))
#### Estimated changes
Added src/measure_theory/measure/complex_lebesgue.lean
- \+ *def* complex.measurable_equiv_pi
- \+ *def* complex.measurable_equiv_real_prod
- \+ *lemma* complex.volume_preserving_equiv_pi
- \+ *lemma* complex.volume_preserving_equiv_real_prod



## [2021-11-21 18:40:48](https://github.com/leanprover-community/mathlib/commit/2168297)
feat(analysis/inner_product_space/projection): orthogonal group is generated by reflections ([#10381](https://github.com/leanprover-community/mathlib/pull/10381))
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* mem_orthogonal_singleton_of_inner_left
- \+ *lemma* mem_orthogonal_singleton_of_inner_right

Modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* linear_isometry_equiv.reflections_generate
- \+ *lemma* linear_isometry_equiv.reflections_generate_dim
- \+ *lemma* linear_isometry_equiv.reflections_generate_dim_aux
- \+ *lemma* reflection_sub
- \+ *lemma* reflection_trans_reflection
- \+/\- *lemma* submodule.finrank_add_finrank_orthogonal



## [2021-11-21 16:46:44](https://github.com/leanprover-community/mathlib/commit/e0c0d84)
feat(topology/separation): removing a finite set from a dense set preserves density ([#10405](https://github.com/leanprover-community/mathlib/pull/10405))
Also add the fact that one can find a dense set containing neither top nor bottom in a nontrivial dense linear order.
#### Estimated changes
Modified src/measure_theory/function/ae_measurable_order.lean


Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* dense.exists_countable_dense_subset_no_bot_top
- \+ *lemma* exists_countable_dense_no_bot_top

Modified src/topology/bases.lean


Modified src/topology/basic.lean


Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.exists_countable_dense_no_zero_top

Modified src/topology/separation.lean
- \+ *lemma* dense.diff_finite
- \+ *lemma* dense.diff_finset
- \+ *lemma* dense.diff_singleton
- \+/\- *lemma* finite.is_closed



## [2021-11-21 11:11:05](https://github.com/leanprover-community/mathlib/commit/55b81f8)
feat(measure_theory): measure preserving maps and integrals ([#10326](https://github.com/leanprover-community/mathlib/pull/10326))
If `f` is a measure preserving map, then `∫ y, g y ∂ν = ∫ x, g (f x) ∂μ`. It was two rewrites with the old API (`hf.map_eq`, then a lemma about integral over map measure); it's one `rw` now.
Also add versions for special cases when `f` is a measurable embedding (in this case we don't need to assume measurability of `g`).
#### Estimated changes
Modified src/data/equiv/fin.lean
- \+ *lemma* fin.preimage_apply_01_prod'
- \+ *lemma* fin.preimage_apply_01_prod

Modified src/dynamics/ergodic/measure_preserving.lean
- \+ *lemma* measure_theory.measure_preserving.restrict_image_emb
- \+ *lemma* measure_theory.measure_preserving.restrict_preimage
- \+ *lemma* measure_theory.measure_preserving.restrict_preimage_emb

Modified src/measure_theory/constructions/pi.lean
- \- *lemma* measure_theory.integral_fin_two_arrow'
- \- *lemma* measure_theory.integral_fin_two_arrow
- \- *lemma* measure_theory.integral_fin_two_arrow_pi'
- \- *lemma* measure_theory.integral_fin_two_arrow_pi
- \- *lemma* measure_theory.integral_fun_unique'
- \- *lemma* measure_theory.integral_fun_unique
- \- *lemma* measure_theory.integral_fun_unique_pi'
- \- *lemma* measure_theory.integral_fun_unique_pi
- \- *lemma* measure_theory.measure.map_fun_unique
- \- *lemma* measure_theory.measure.pi_unique_eq_map
- \- *lemma* measure_theory.measure.prod_eq_map_fin_two_arrow
- \- *lemma* measure_theory.measure.prod_eq_map_fin_two_arrow_same
- \- *lemma* measure_theory.measure.{u}
- \+ *lemma* measure_theory.measure_preserving_fin_two_arrow
- \+ *lemma* measure_theory.measure_preserving_fin_two_arrow_vec
- \+ *lemma* measure_theory.measure_preserving_fun_unique
- \+ *lemma* measure_theory.measure_preserving_pi_empty
- \+ *lemma* measure_theory.measure_preserving_pi_fin_two
- \- *lemma* measure_theory.set_integral_fin_two_arrow'
- \- *lemma* measure_theory.set_integral_fin_two_arrow
- \- *lemma* measure_theory.set_integral_fin_two_arrow_pi'
- \- *lemma* measure_theory.set_integral_fin_two_arrow_pi
- \- *lemma* measure_theory.set_integral_fun_unique'
- \- *lemma* measure_theory.set_integral_fun_unique
- \- *lemma* measure_theory.set_integral_fun_unique_pi'
- \- *lemma* measure_theory.set_integral_fun_unique_pi
- \+ *lemma* measure_theory.volume_preserving_fin_two_arrow
- \+ *lemma* measure_theory.volume_preserving_fun_unique
- \+ *lemma* measure_theory.volume_preserving_pi_empty
- \+ *lemma* measure_theory.volume_preserving_pi_fin_two

Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.measure_preserving.integrable_comp
- \+ *lemma* measure_theory.measure_preserving.integrable_comp_emb

Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.measure_preserving.integral_comp

Modified src/measure_theory/integral/integrable_on.lean
- \+ *lemma* measure_theory.measure_preserving.integrable_on_comp_preimage
- \+ *lemma* measure_theory.measure_preserving.integrable_on_image

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.measure_preserving.lintegral_comp
- \+ *lemma* measure_theory.measure_preserving.lintegral_comp_emb
- \+ *lemma* measure_theory.measure_preserving.set_lintegral_comp_emb
- \+ *lemma* measure_theory.measure_preserving.set_lintegral_comp_preimage
- \+ *lemma* measure_theory.measure_preserving.set_lintegral_comp_preimage_emb

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.measure_preserving.set_integral_image_emb
- \+ *lemma* measure_theory.measure_preserving.set_integral_preimage_emb

Modified src/measure_theory/measure/measure_space.lean




## [2021-11-20 23:37:29](https://github.com/leanprover-community/mathlib/commit/2a28652)
feat(data/finset/basic): add filter_erase ([#10384](https://github.com/leanprover-community/mathlib/pull/10384))
Like `filter_insert`, but for `erase`
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.erase_idem
- \+ *lemma* finset.erase_right_comm
- \+ *theorem* finset.filter_erase



## [2021-11-20 21:22:54](https://github.com/leanprover-community/mathlib/commit/32c0507)
feat(data/nat/interval): add Ico_succ_left_eq_erase ([#10386](https://github.com/leanprover-community/mathlib/pull/10386))
Adds `Ico_succ_left_eq_erase`. Also adds a few order lemmas needed for this.
See [this discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Ico_succ_left_eq_erase_Ico/near/259180476)
#### Estimated changes
Modified src/data/nat/interval.lean
- \+ *lemma* nat.Ico_succ_left_eq_erase_Ico

Modified src/order/basic.lean
- \+ *lemma* ne_of_not_le



## [2021-11-20 13:22:08](https://github.com/leanprover-community/mathlib/commit/b3538bf)
feat(topology/algebra/infinite_sum): add `has_sum.smul_const` etc ([#10393](https://github.com/leanprover-community/mathlib/pull/10393))
Rename old `*.smul` to `*.const_smul`.
#### Estimated changes
Modified src/measure_theory/measure/vector_measure.lean


Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.const_smul
- \- *lemma* has_sum.smul
- \+ *lemma* has_sum.smul_const
- \+ *lemma* summable.const_smul
- \- *lemma* summable.smul
- \+ *lemma* summable.smul_const
- \+ *lemma* tsum_const_smul
- \- *lemma* tsum_smul
- \+ *lemma* tsum_smul_const



## [2021-11-20 11:30:32](https://github.com/leanprover-community/mathlib/commit/618447f)
feat(analysis/special_functions/complex/arg): review, golf, lemmas ([#10365](https://github.com/leanprover-community/mathlib/pull/10365))
* add `|z| * exp (arg z * I) = z`;
* reorder theorems to help golfing;
* prove formulas for `arg z` in terms of `arccos (re z / abs z)` in cases `0 < im z` and `im z < 0`;
* use them to golf continuity of `arg`.
#### Estimated changes
Modified src/algebra/order/ring.lean
- \+ *theorem* mul_nonneg_iff_left_nonneg_of_pos
- \+/\- *theorem* mul_nonneg_iff_right_nonneg_of_pos

Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* complex.abs_mul_cos_add_sin_mul_I
- \+ *lemma* complex.abs_mul_exp_arg_mul_I
- \+/\- *lemma* complex.arg_cos_add_sin_mul_I
- \+ *lemma* complex.arg_eq_neg_pi_div_two_iff
- \+ *lemma* complex.arg_eq_nhds_of_im_neg
- \+ *lemma* complex.arg_eq_nhds_of_im_pos
- \+ *lemma* complex.arg_eq_pi_div_two_iff
- \+ *lemma* complex.arg_mem_Ioc
- \+ *lemma* complex.arg_mul_cos_add_sin_mul_I
- \+ *lemma* complex.arg_neg_iff
- \+ *lemma* complex.arg_nonneg_iff
- \+ *lemma* complex.arg_of_im_neg
- \+ *lemma* complex.arg_of_im_nonneg_of_ne_zero
- \+ *lemma* complex.arg_of_im_pos
- \- *lemma* complex.arg_of_re_zero_of_im_neg
- \- *lemma* complex.arg_of_re_zero_of_im_pos
- \+/\- *lemma* complex.arg_zero
- \- *lemma* complex.continuous_at_arg_of_re_neg_of_im_neg
- \- *lemma* complex.continuous_at_arg_of_re_neg_of_im_pos
- \- *lemma* complex.continuous_at_arg_of_re_pos
- \- *lemma* complex.continuous_at_arg_of_re_zero
- \+ *lemma* complex.ext_abs_arg_iff
- \+ *lemma* complex.range_arg
- \+/\- *lemma* complex.tan_arg

Modified src/analysis/special_functions/complex/circle.lean


Modified src/analysis/special_functions/complex/log.lean


Modified src/data/complex/basic.lean
- \+ *lemma* complex.norm_sq_add_mul_I
- \+ *lemma* complex.sq_abs
- \+ *lemma* complex.sq_abs_sub_sq_im
- \+ *lemma* complex.sq_abs_sub_sq_re

Modified src/geometry/euclidean/triangle.lean




## [2021-11-20 02:42:14](https://github.com/leanprover-community/mathlib/commit/bd6c6d5)
chore(scripts): update nolints.txt ([#10391](https://github.com/leanprover-community/mathlib/pull/10391))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-11-19 15:45:43](https://github.com/leanprover-community/mathlib/commit/db926f0)
chore(category_theory/limits/shapes/pullbacks): fix diagrams in docs ([#10379](https://github.com/leanprover-community/mathlib/pull/10379))
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean




## [2021-11-19 14:34:11](https://github.com/leanprover-community/mathlib/commit/7638fe2)
doc(topology/separation): two typos ([#10382](https://github.com/leanprover-community/mathlib/pull/10382))
#### Estimated changes
Modified src/topology/separation.lean




## [2021-11-19 12:03:57](https://github.com/leanprover-community/mathlib/commit/e8858fd)
refactor(algebra/opposites): use mul_opposite for multiplicative opposite ([#10302](https://github.com/leanprover-community/mathlib/pull/10302))
Split out `mul_opposite` from `opposite`, to leave room for an `add_opposite` in future.
Multiplicative opposites are now spelt `Aᵐᵒᵖ` instead of `Aᵒᵖ`. `Aᵒᵖ` now refers to the categorical opposite.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* mul_opposite.algebra_map_apply
- \- *lemma* opposite.algebra_map_apply

Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.unop_sum
- \+/\- *lemma* ring_hom.unop_map_list_prod

Modified src/algebra/free_algebra.lean
- \+/\- *def* free_algebra.star_hom

Modified src/algebra/geom_sum.lean


Modified src/algebra/group/prod.lean
- \+/\- *def* embed_product

Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* mul_opposite.op_pow
- \+ *lemma* mul_opposite.op_zpow
- \+ *lemma* mul_opposite.unop_pow
- \+ *lemma* mul_opposite.unop_zpow
- \- *lemma* opposite.op_pow
- \- *lemma* opposite.op_zpow
- \- *lemma* opposite.unop_pow
- \- *lemma* opposite.unop_zpow

Modified src/algebra/hierarchy_design.lean


Modified src/algebra/module/basic.lean


Modified src/algebra/module/opposites.lean
- \+ *lemma* mul_opposite.coe_op_linear_equiv
- \+ *lemma* mul_opposite.coe_op_linear_equiv_symm
- \+ *lemma* mul_opposite.coe_op_linear_equiv_symm_to_linear_map
- \+ *lemma* mul_opposite.coe_op_linear_equiv_to_linear_map
- \+ *def* mul_opposite.op_linear_equiv
- \+ *lemma* mul_opposite.op_linear_equiv_symm_to_add_equiv
- \+ *lemma* mul_opposite.op_linear_equiv_to_add_equiv
- \- *lemma* opposite.coe_op_linear_equiv
- \- *lemma* opposite.coe_op_linear_equiv_symm
- \- *lemma* opposite.coe_op_linear_equiv_symm_to_linear_map
- \- *lemma* opposite.coe_op_linear_equiv_to_linear_map
- \- *def* opposite.op_linear_equiv
- \- *lemma* opposite.op_linear_equiv_symm_to_add_equiv
- \- *lemma* opposite.op_linear_equiv_to_add_equiv

Modified src/algebra/monoid_algebra/basic.lean
- \+/\- *lemma* add_monoid_algebra.op_ring_equiv_symm_single
- \+/\- *lemma* monoid_algebra.op_ring_equiv_symm_single

Modified src/algebra/opposites.lean
- \+/\- *def* mul_equiv.inv'
- \+ *lemma* mul_opposite.commute.op
- \+ *lemma* mul_opposite.commute.unop
- \+ *lemma* mul_opposite.commute_op
- \+ *lemma* mul_opposite.commute_unop
- \+ *def* mul_opposite.op
- \+ *lemma* mul_opposite.op_add
- \+ *def* mul_opposite.op_add_equiv
- \+ *lemma* mul_opposite.op_add_equiv_to_equiv
- \+ *lemma* mul_opposite.op_bijective
- \+ *lemma* mul_opposite.op_comp_unop
- \+ *lemma* mul_opposite.op_eq_one_iff
- \+ *lemma* mul_opposite.op_eq_zero_iff
- \+ *def* mul_opposite.op_equiv
- \+ *lemma* mul_opposite.op_inj
- \+ *lemma* mul_opposite.op_injective
- \+ *lemma* mul_opposite.op_inv
- \+ *lemma* mul_opposite.op_mul
- \+ *lemma* mul_opposite.op_ne_zero_iff
- \+ *lemma* mul_opposite.op_neg
- \+ *lemma* mul_opposite.op_one
- \+ *lemma* mul_opposite.op_smul
- \+ *lemma* mul_opposite.op_smul_eq_mul
- \+ *lemma* mul_opposite.op_sub
- \+ *lemma* mul_opposite.op_surjective
- \+ *lemma* mul_opposite.op_unop
- \+ *lemma* mul_opposite.op_zero
- \+ *lemma* mul_opposite.semiconj_by.op
- \+ *lemma* mul_opposite.semiconj_by.unop
- \+ *lemma* mul_opposite.semiconj_by_op
- \+ *lemma* mul_opposite.semiconj_by_unop
- \+ *def* mul_opposite.unop
- \+ *lemma* mul_opposite.unop_add
- \+ *lemma* mul_opposite.unop_bijective
- \+ *lemma* mul_opposite.unop_comp_op
- \+ *lemma* mul_opposite.unop_eq_one_iff
- \+ *lemma* mul_opposite.unop_eq_zero_iff
- \+ *lemma* mul_opposite.unop_inj
- \+ *lemma* mul_opposite.unop_injective
- \+ *lemma* mul_opposite.unop_inv
- \+ *lemma* mul_opposite.unop_mul
- \+ *lemma* mul_opposite.unop_ne_zero_iff
- \+ *lemma* mul_opposite.unop_neg
- \+ *lemma* mul_opposite.unop_one
- \+ *lemma* mul_opposite.unop_op
- \+ *lemma* mul_opposite.unop_smul
- \+ *lemma* mul_opposite.unop_sub
- \+ *lemma* mul_opposite.unop_surjective
- \+ *lemma* mul_opposite.unop_zero
- \+ *def* mul_opposite
- \- *lemma* opposite.coe_op_add_equiv
- \- *lemma* opposite.coe_op_add_equiv_symm
- \- *lemma* opposite.commute.op
- \- *lemma* opposite.commute.unop
- \- *lemma* opposite.commute_op
- \- *lemma* opposite.commute_unop
- \- *lemma* opposite.op_add
- \- *def* opposite.op_add_equiv
- \- *lemma* opposite.op_add_equiv_to_equiv
- \- *lemma* opposite.op_eq_one_iff
- \- *lemma* opposite.op_eq_zero_iff
- \- *lemma* opposite.op_inv
- \- *lemma* opposite.op_mul
- \- *lemma* opposite.op_ne_zero_iff
- \- *lemma* opposite.op_neg
- \- *lemma* opposite.op_one
- \- *lemma* opposite.op_smul
- \- *lemma* opposite.op_smul_eq_mul
- \- *lemma* opposite.op_sub
- \- *lemma* opposite.op_zero
- \- *lemma* opposite.semiconj_by.op
- \- *lemma* opposite.semiconj_by.unop
- \- *lemma* opposite.semiconj_by_op
- \- *lemma* opposite.semiconj_by_unop
- \- *lemma* opposite.unop_add
- \- *lemma* opposite.unop_eq_one_iff
- \- *lemma* opposite.unop_eq_zero_iff
- \- *lemma* opposite.unop_inv
- \- *lemma* opposite.unop_mul
- \- *lemma* opposite.unop_ne_zero_iff
- \- *lemma* opposite.unop_neg
- \- *lemma* opposite.unop_one
- \- *lemma* opposite.unop_smul
- \- *lemma* opposite.unop_sub
- \- *lemma* opposite.unop_zero
- \+/\- *lemma* units.coe_op_equiv_symm
- \+/\- *lemma* units.coe_unop_op_equiv
- \+/\- *def* units.op_equiv

Modified src/algebra/periodic.lean


Modified src/algebra/quandle.lean


Modified src/algebra/quaternion.lean
- \+/\- *lemma* quaternion.coe_conj_ae
- \+/\- *def* quaternion.conj_ae
- \+/\- *def* quaternion_algebra.conj_ae

Modified src/algebra/regular/smul.lean
- \+/\- *lemma* is_smul_regular.is_right_regular

Modified src/algebra/smul_with_zero.lean


Modified src/algebra/star/basic.lean
- \+ *lemma* mul_opposite.op_star
- \+ *lemma* mul_opposite.unop_star
- \- *lemma* opposite.op_star
- \- *lemma* opposite.unop_star
- \+/\- *def* star_mul_equiv
- \+/\- *def* star_ring_equiv

Modified src/algebra/star/module.lean


Modified src/analysis/normed/group/SemiNormedGroup/completion.lean


Modified src/analysis/normed_space/units.lean


Modified src/category_theory/monoidal/opposite.lean
- \+/\- *def* category_theory.monoidal_opposite.mop
- \+/\- *lemma* category_theory.monoidal_opposite.mop_unmop
- \+/\- *lemma* category_theory.monoidal_opposite.op_injective
- \+/\- *def* category_theory.monoidal_opposite.unmop
- \+/\- *lemma* category_theory.monoidal_opposite.unop_inj_iff
- \+/\- *lemma* category_theory.monoidal_opposite.unop_injective
- \+/\- *lemma* category_theory.mop_id_unmop
- \+/\- *lemma* category_theory.mop_tensor_obj
- \+/\- *lemma* category_theory.mop_tensor_unit
- \+/\- *lemma* category_theory.mop_unmop
- \+/\- *lemma* category_theory.unmop_comp
- \+/\- *lemma* category_theory.unmop_id
- \+/\- *lemma* category_theory.unmop_inj
- \+/\- *def* quiver.hom.mop
- \+/\- *def* quiver.hom.unmop

Modified src/computability/turing_machine.lean


Modified src/control/fold.lean
- \+/\- *def* monoid.foldl

Modified src/data/complex/is_R_or_C.lean
- \+/\- *abbreviation* is_R_or_C.conj_to_ring_equiv

Modified src/data/equiv/mul_add.lean


Modified src/data/equiv/ring.lean
- \+/\- *lemma* ring_equiv.to_add_equiv_eq_coe
- \+/\- *lemma* ring_equiv.to_mul_equiv_eq_coe
- \+/\- *def* ring_equiv.to_opposite
- \+/\- *lemma* ring_equiv.to_opposite_symm_apply
- \+/\- *lemma* ring_equiv.unop_map_list_prod

Modified src/data/list/big_operators.lean
- \+/\- *lemma* monoid_hom.unop_map_list_prod
- \+ *lemma* mul_opposite.op_list_prod
- \+ *lemma* mul_opposite.unop_list_prod
- \- *lemma* opposite.op_list_prod
- \- *lemma* opposite.unop_list_prod

Modified src/data/matrix/basic.lean
- \+/\- *def* matrix.transpose_ring_equiv

Modified src/data/opposite.lean


Modified src/data/polynomial/basic.lean
- \+/\- *def* polynomial.op_ring_equiv

Modified src/data/prod.lean
- \+ *lemma* prod.fst_comp_mk
- \+ *lemma* prod.snd_comp_mk

Modified src/group_theory/free_product.lean
- \+/\- *lemma* free_product.inv_def

Modified src/linear_algebra/clifford_algebra/conjugation.lean


Modified src/linear_algebra/sesquilinear_form.lean
- \+/\- *structure* sesq_form

Modified src/logic/unique.lean
- \+/\- *def* unique.mk'

Modified src/measure_theory/group/arithmetic.lean
- \+/\- *lemma* measurable_op
- \+/\- *lemma* measurable_unop

Modified src/number_theory/arithmetic_function.lean


Modified src/ring_theory/ring_invo.lean
- \+/\- *def* ring_invo.mk'
- \+/\- *structure* ring_invo

Modified src/topology/algebra/monoid.lean
- \+/\- *lemma* continuous_op
- \+/\- *lemma* continuous_unop



## [2021-11-19 10:10:47](https://github.com/leanprover-community/mathlib/commit/d6814c5)
feat(*): Reduce imports to only those necessary in the entire library ([#10349](https://github.com/leanprover-community/mathlib/pull/10349))
We reduce imports of many files in the library to only those actually needed by the content of the file, this is done by inspecting the declarations and attributes used by declarations in a file, and then computing a minimal set of imports that includes all of the necessary content. (A tool to do this was written by @jcommelin and I for this purpose).
The point of doing this is to reduce unnecessary recompilation when files that aren't needed for some file higher up the import graph are changed and everything in between gets recompiled. 
Another side benefit might be slightly faster simp / library_searches / tc lookups in some files as there may be less random declarations in the environment that aren't too relevant to the file.
The exception is that we do not remove any tactic file imports (in this run at least) as that requires more care to get right.
We also skip any `default.lean` files as the point of these is to provide a convenient way of importing a large chunk of the library (though arguably no mathlib file should import a default file that has no non-import content).
Some OLD statistics (not 100% accurate as several things changed since then):
The average number of imports of each file in the library reduces by around 2, (this equals the average number of dependencies of each file) raw numbers are `806748 / 2033` (total number of transitive links/total number files before) to `802710 / 2033` (after)
The length of the longest chain of imports in mathlib decreases from 139 to 130.
The imports (transitively) removed from the most from other files are as follows (file, decrease in number of files importing):
```
data.polynomial.degree.trailing_degree 13
linear_algebra.quotient 13
ring_theory.principal_ideal_domain 13
data.int.gcd 14
data.polynomial.div 14
data.list.rotate 15
data.nat.modeq 15
data.fin.interval 17
data.int.interval 17
data.pnat.interval 17
```
The original script generated by an import-reducing tool is at https://github.com/alexjbest/dag-tools though I did clean up the output and some weirdness after running this script
In touched files the imports are put into alphabetical order, we tried not to touch too many files that don't have their imports changed, but some were in the many merges and iterations on this.
There are a couple of changes to mathlib not to an import line (compared to master) that I couldn't resist doing that became apparent when the tool recommended deletions of imports containing named simp lemmas in the file, that weren't firing and so the tool was right to remove the import.
Another sort of issue  is discussed in https://github.com/leanprover-community/mathlib/blob/master/src/algebraic_geometry/presheafed_space/has_colimits.lean#L253, this is discussed at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Reordering.20ext.20lemmas/near/261581547 and there seems to be currently no good way to avoid this so we just fix the proof. One can verify this with the command ` git diff origin/master -I import`
At a later point we hope to modify this tooling to suggest splits in long files by their prerequisites, but getting the library into a more minimal state w.r.t file imports seems to be important for such a tool to work well.
#### Estimated changes
Modified archive/100-theorems-list/16_abel_ruffini.lean


Modified src/algebra/algebra/basic.lean


Modified src/algebra/algebra/bilinear.lean


Modified src/algebra/big_operators/finsupp.lean


Modified src/algebra/category/CommRing/adjunctions.lean


Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/Group/biproducts.lean


Modified src/algebra/category/Module/basic.lean


Modified src/algebra/category/Module/colimits.lean


Modified src/algebra/category/Module/epi_mono.lean


Modified src/algebra/category/Module/filtered_colimits.lean


Modified src/algebra/category/Module/projective.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/category/Mon/limits.lean


Modified src/algebra/category/Semigroup/basic.lean


Modified src/algebra/char_p/basic.lean


Modified src/algebra/char_p/quotient.lean


Modified src/algebra/continued_fractions/computation/approximation_corollaries.lean


Modified src/algebra/continued_fractions/computation/basic.lean


Modified src/algebra/continued_fractions/computation/correctness_terminating.lean


Modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean


Modified src/algebra/direct_sum/algebra.lean


Modified src/algebra/direct_sum/internal.lean


Modified src/algebra/direct_sum/ring.lean


Modified src/algebra/divisibility.lean


Modified src/algebra/field.lean


Modified src/algebra/free_algebra.lean


Modified src/algebra/gcd_monoid/basic.lean


Modified src/algebra/graded_monoid.lean


Modified src/algebra/group_action_hom.lean


Modified src/algebra/group_with_zero/power.lean


Modified src/algebra/homology/augment.lean


Modified src/algebra/homology/complex_shape.lean


Modified src/algebra/lie/base_change.lean


Modified src/algebra/lie/basic.lean


Modified src/algebra/lie/cartan_matrix.lean


Modified src/algebra/lie/classical.lean


Modified src/algebra/lie/direct_sum.lean


Modified src/algebra/linear_recurrence.lean


Modified src/algebra/module/ulift.lean


Modified src/algebra/monoid_algebra/grading.lean


Modified src/algebra/order/algebra.lean


Modified src/algebra/order/archimedean.lean


Modified src/algebra/order/smul.lean


Modified src/algebra/order/with_zero.lean


Modified src/algebra/pempty_instances.lean


Modified src/algebra/periodic.lean


Modified src/algebra/pointwise.lean


Modified src/algebra/polynomial/big_operators.lean


Modified src/algebra/star/chsh.lean


Modified src/algebraic_geometry/EllipticCurve.lean


Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/algebraic_geometry/presheafed_space/has_colimits.lean


Modified src/algebraic_geometry/ringed_space.lean


Modified src/algebraic_topology/Moore_complex.lean


Modified src/algebraic_topology/simplex_category.lean


Modified src/algebraic_topology/simplicial_object.lean


Modified src/algebraic_topology/simplicial_set.lean


Modified src/algebraic_topology/topological_simplex.lean


Modified src/analysis/ODE/picard_lindelof.lean


Modified src/analysis/asymptotics/superpolynomial_decay.lean


Modified src/analysis/box_integral/box/basic.lean


Modified src/analysis/box_integral/partition/filter.lean


Modified src/analysis/calculus/darboux.lean


Modified src/analysis/calculus/inverse.lean


Modified src/analysis/complex/roots_of_unity.lean


Modified src/analysis/convex/extrema.lean


Modified src/analysis/normed_space/affine_isometry.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/conformal_linear_map.lean


Modified src/analysis/normed_space/exponential.lean


Modified src/analysis/normed_space/indicator_function.lean


Modified src/analysis/normed_space/is_R_or_C.lean


Modified src/analysis/normed_space/lattice_ordered_group.lean


Modified src/analysis/normed_space/linear_isometry.lean


Modified src/analysis/normed_space/star.lean


Modified src/analysis/seminorm.lean


Modified src/analysis/special_functions/trigonometric/arctan.lean


Modified src/analysis/special_functions/trigonometric/chebyshev.lean


Modified src/analysis/special_functions/trigonometric/deriv.lean


Modified src/category_theory/Fintype.lean


Modified src/category_theory/abelian/projective.lean


Modified src/category_theory/adjunction/comma.lean


Modified src/category_theory/adjunction/lifting.lean


Modified src/category_theory/adjunction/mates.lean


Modified src/category_theory/adjunction/over.lean


Modified src/category_theory/adjunction/reflective.lean


Modified src/category_theory/category/Cat.lean


Modified src/category_theory/category/Quiv.lean


Modified src/category_theory/category/pairwise.lean


Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/comma.lean


Modified src/category_theory/concrete_category/bundled.lean


Modified src/category_theory/conj.lean


Modified src/category_theory/differential_object.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/hom_functor.lean


Modified src/category_theory/isomorphism_classes.lean


Modified src/category_theory/lifting_properties.lean


Modified src/category_theory/limits/comma.lean


Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean


Modified src/category_theory/limits/constructions/over/connected.lean


Modified src/category_theory/limits/constructions/over/default.lean


Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/kan_extension.lean


Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/preserves/filtered.lean


Modified src/category_theory/limits/preserves/functor_category.lean


Modified src/category_theory/limits/preserves/shapes/terminal.lean


Modified src/category_theory/limits/presheaf.lean


Modified src/category_theory/limits/shapes/disjoint_coproduct.lean


Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/normal_mono.lean


Modified src/category_theory/limits/shapes/reflexive.lean


Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/coequalizer.lean


Modified src/category_theory/monad/kleisli.lean


Modified src/category_theory/monad/monadicity.lean


Modified src/category_theory/monad/products.lean


Modified src/category_theory/monoidal/free/basic.lean


Modified src/category_theory/monoidal/free/coherence.lean


Modified src/category_theory/monoidal/types.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/pi/basic.lean


Modified src/category_theory/preadditive/Mat.lean


Modified src/category_theory/sigma/basic.lean


Modified src/category_theory/sites/sheaf.lean


Modified src/category_theory/sites/sieves.lean


Modified src/category_theory/subterminal.lean


Modified src/category_theory/triangulated/basic.lean


Modified src/category_theory/triangulated/pretriangulated.lean


Modified src/category_theory/triangulated/rotate.lean


Modified src/category_theory/whiskering.lean


Modified src/combinatorics/colex.lean


Modified src/combinatorics/hales_jewett.lean


Modified src/combinatorics/hall/finite.lean


Modified src/computability/language.lean


Modified src/computability/regular_expressions.lean


Modified src/control/bifunctor.lean


Modified src/control/equiv_functor.lean


Modified src/control/fix.lean


Modified src/control/monad/cont.lean


Modified src/control/monad/writer.lean


Modified src/control/traversable/derive.lean


Modified src/control/traversable/instances.lean


Modified src/data/buffer/parser/numeral.lean


Modified src/data/complex/module.lean


Modified src/data/equiv/basic.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/embedding.lean


Modified src/data/equiv/mul_add.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/fin/basic.lean


Modified src/data/finset/basic.lean


Modified src/data/fp/basic.lean


Modified src/data/int/absolute_value.lean


Modified src/data/int/interval.lean


Modified src/data/list/basic.lean


Modified src/data/list/cycle.lean


Modified src/data/list/duplicate.lean


Modified src/data/list/prod_monoid.lean


Modified src/data/list/sigma.lean


Modified src/data/list/sort.lean


Modified src/data/matrix/basic.lean


Modified src/data/matrix/basis.lean


Modified src/data/matrix/hadamard.lean


Modified src/data/mv_polynomial/basic.lean


Modified src/data/nat/choose/central.lean


Modified src/data/nat/choose/vandermonde.lean


Modified src/data/nat/enat.lean


Modified src/data/nat/fib.lean


Modified src/data/nat/gcd.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/prime.lean


Modified src/data/option/basic.lean


Modified src/data/pequiv.lean


Modified src/data/pfunctor/multivariate/M.lean


Modified src/data/pfunctor/multivariate/basic.lean


Modified src/data/pnat/basic.lean


Modified src/data/pnat/factors.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/div.lean


Modified src/data/polynomial/erase_lead.lean


Modified src/data/polynomial/lifts.lean


Modified src/data/polynomial/reverse.lean


Modified src/data/qpf/univariate/basic.lean


Modified src/data/rat/denumerable.lean


Modified src/data/real/basic.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/irrational.lean


Modified src/data/real/pi/leibniz.lean


Modified src/data/seq/computation.lean


Modified src/data/seq/seq.lean


Modified src/data/seq/wseq.lean


Modified src/data/set/basic.lean


Modified src/data/set/pairwise.lean


Modified src/data/setoid/basic.lean


Modified src/data/subtype.lean


Modified src/data/sym/basic.lean


Modified src/data/sym/card.lean


Modified src/dynamics/periodic_pts.lean


Modified src/field_theory/chevalley_warning.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/field_theory/primitive_element.lean


Modified src/field_theory/separable.lean


Modified src/field_theory/separable_degree.lean


Modified src/field_theory/splitting_field.lean


Modified src/geometry/manifold/bump_function.lean


Modified src/geometry/manifold/instances/real.lean


Modified src/geometry/manifold/instances/sphere.lean


Modified src/geometry/manifold/local_invariant_properties.lean


Modified src/geometry/manifold/partition_of_unity.lean


Modified src/geometry/manifold/whitney_embedding.lean


Modified src/group_theory/complement.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/eckmann_hilton.lean


Modified src/group_theory/monoid_localization.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/p_group.lean


Modified src/group_theory/perm/basic.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/perm/support.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/schur_zassenhaus.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/linear_algebra/adic_completion.lean


Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/linear_algebra/affine_space/affine_subspace.lean


Modified src/linear_algebra/coevaluation.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/free_module/pid.lean


Modified src/linear_algebra/general_linear_group.lean


Modified src/linear_algebra/lagrange.lean


Modified src/linear_algebra/matrix/adjugate.lean


Modified src/linear_algebra/matrix/block.lean


Modified src/linear_algebra/matrix/charpoly/basic.lean


Modified src/linear_algebra/matrix/charpoly/coeff.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean


Modified src/linear_algebra/matrix/polynomial.lean


Modified src/linear_algebra/matrix/transvection.lean


Modified src/linear_algebra/quadratic_form/basic.lean


Modified src/linear_algebra/quotient.lean


Modified src/linear_algebra/sesquilinear_form.lean


Modified src/linear_algebra/special_linear_group.lean


Modified src/linear_algebra/tensor_product_basis.lean


Modified src/linear_algebra/unitary_group.lean


Modified src/logic/is_empty.lean


Modified src/logic/nontrivial.lean


Modified src/logic/relation.lean


Modified src/measure_theory/category/Meas.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/decomposition/jordan.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/function/ae_measurable_sequence.lean


Modified src/measure_theory/integral/divergence_theorem.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measurable_space_def.lean


Modified src/measure_theory/measure/complex.lean


Modified src/measure_theory/measure/lebesgue.lean


Modified src/measure_theory/measure/vector_measure.lean


Modified src/measure_theory/tactic.lean


Modified src/meta/expr.lean


Modified src/meta/expr_lens.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/bernoulli_polynomials.lean


Modified src/number_theory/class_number/admissible_abs.lean


Modified src/number_theory/class_number/admissible_absolute_value.lean


Modified src/number_theory/class_number/admissible_card_pow_degree.lean


Modified src/number_theory/class_number/finite.lean


Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/lucas_primality.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/number_theory/padics/ring_homs.lean


Modified src/order/category/NonemptyFinLinOrd.lean


Modified src/order/category/Preorder.lean


Modified src/order/closure.lean


Modified src/order/compactly_generated.lean


Modified src/order/countable_dense_linear_order.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/ultrafilter.lean


Modified src/order/liminf_limsup.lean


Modified src/order/omega_complete_partial_order.lean


Modified src/order/pilex.lean


Modified src/order/preorder_hom.lean


Modified src/order/rel_classes.lean


Modified src/order/succ_pred.lean


Modified src/probability_theory/notation.lean


Modified src/ring_theory/adjoin/fg.lean


Modified src/ring_theory/adjoin/polynomial.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/derivation.lean


Modified src/ring_theory/fintype.lean


Modified src/ring_theory/flat.lean


Modified src/ring_theory/free_ring.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/nakayama.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/norm.lean


Modified src/ring_theory/perfection.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/bernstein.lean


Modified src/ring_theory/polynomial/homogeneous.lean


Modified src/ring_theory/polynomial/scale_roots.lean


Modified src/ring_theory/polynomial/vieta.lean


Modified src/ring_theory/polynomial_algebra.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/valuation/basic.lean


Modified src/ring_theory/witt_vector/structure_polynomial.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/surreal/basic.lean


Modified src/set_theory/surreal/dyadic.lean


Modified src/system/random/basic.lean


Modified src/tactic/choose.lean


Modified src/tactic/clear.lean


Modified src/tactic/converter/binders.lean


Modified src/tactic/core.lean


Modified src/tactic/dependencies.lean


Modified src/tactic/elementwise.lean


Modified src/tactic/equiv_rw.lean


Modified src/tactic/explode.lean


Modified src/tactic/ext.lean


Modified src/tactic/find_unused.lean


Modified src/tactic/interval_cases.lean


Modified src/tactic/linarith/datatypes.lean


Modified src/tactic/lint/frontend.lean


Modified src/tactic/lint/misc.lean


Modified src/tactic/lint/type_classes.lean


Modified src/tactic/localized.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified src/tactic/nth_rewrite/congr.lean


Modified src/tactic/restate_axiom.lean


Modified src/tactic/rewrite_all/basic.lean


Modified src/tactic/rewrite_search/search.lean


Modified src/tactic/ring.lean


Modified src/tactic/scc.lean


Modified src/tactic/simps.lean


Modified src/tactic/slim_check.lean


Modified src/tactic/subtype_instance.lean


Modified src/tactic/suggest.lean


Modified src/tactic/zify.lean


Modified src/testing/slim_check/functions.lean


Modified src/topology/G_delta.lean


Modified src/topology/algebra/affine.lean


Modified src/topology/algebra/group_with_zero.lean


Modified src/topology/algebra/mul_action.lean


Modified src/topology/algebra/nonarchimedean/bases.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/polynomial.lean


Modified src/topology/category/Top/basic.lean


Modified src/topology/category/Top/open_nhds.lean


Modified src/topology/category/Top/opens.lean


Modified src/topology/category/UniformSpace.lean


Modified src/topology/continuous_function/locally_constant.lean


Modified src/topology/homotopy/fundamental_groupoid.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/irrational.lean


Modified src/topology/list.lean


Modified src/topology/locally_constant/algebra.lean


Modified src/topology/metric_space/algebra.lean


Modified src/topology/semicontinuous.lean


Modified src/topology/sheaves/forget.lean


Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/presheaf.lean


Modified src/topology/sheaves/sheaf.lean


Modified src/topology/sheaves/sheaf_condition/equalizer_products.lean


Modified src/topology/sheaves/sheaf_condition/unique_gluing.lean


Modified src/topology/sheaves/sheaf_of_functions.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/separation.lean


Modified test/equiv_rw.lean


Modified test/monotonicity/test_cases.lean


Modified test/simps.lean


Modified test/slim_check.lean




## [2021-11-19 08:56:27](https://github.com/leanprover-community/mathlib/commit/5000fb0)
feat(data/polynomial/eval): is_root_(prod/map) ([#10360](https://github.com/leanprover-community/mathlib/pull/10360))
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.is_root.eq_zero
- \+ *lemma* polynomial.is_root.map
- \+ *lemma* polynomial.is_root.of_map
- \+ *lemma* polynomial.is_root_map_iff
- \+ *lemma* polynomial.is_root_prod



## [2021-11-19 08:01:42](https://github.com/leanprover-community/mathlib/commit/784fe06)
feat(analysis/calculus/deriv): generalize lemmas about deriv and `smul` ([#10378](https://github.com/leanprover-community/mathlib/pull/10378))
Allow scalar multiplication by numbers from a different field.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* deriv_const_smul
- \+/\- *theorem* has_deriv_at.const_smul
- \+ *theorem* has_deriv_at_filter.const_smul
- \+ *theorem* has_deriv_at_mul_const
- \+ *theorem* has_strict_deriv_at.const_smul

Modified src/analysis/calculus/fderiv_symmetric.lean




## [2021-11-18 21:48:21](https://github.com/leanprover-community/mathlib/commit/f3f4442)
feat(logic/basic): define exists_unique_eq as a simp lemma ([#10364](https://github.com/leanprover-community/mathlib/pull/10364))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *theorem* exists_unique_eq'
- \+ *theorem* exists_unique_eq



## [2021-11-18 20:52:43](https://github.com/leanprover-community/mathlib/commit/d5d2c4f)
feat(field_theory/splitting_field): add a more general algebra instance as a def ([#10220](https://github.com/leanprover-community/mathlib/pull/10220))
Unfortunately this def results in the following non-defeq diamonds in `splitting_field_aux.algebra` and `splitting_field.algebra`:
```lean
example
  (n : ℕ) {K : Type u} [field K] {f : polynomial K} (hfn : f.nat_degree = n) :
    (add_comm_monoid.nat_module : module ℕ (splitting_field_aux n f hfn)) =
  @algebra.to_module _ _ _ _ (splitting_field_aux.algebra n _ hfn) :=
rfl --fail
example : (add_comm_group.int_module _ : module ℤ (splitting_field_aux n f hfn)) =
  @algebra.to_module _ _ _ _ (splitting_field_aux.algebra f) :=
rfl --fail
```
For this reason, we do not make `splitting_field.algebra` an instance by default. The `splitting_field_aux.algebra` instance is less harmful as it is an implementation detail.
However, the new def is still perfectly good for recovering the old less-general instance, and avoids the need for `restrict_scalars.algebra`.
#### Estimated changes
Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* adjoin_root.algebra_map_eq'



## [2021-11-18 17:07:15](https://github.com/leanprover-community/mathlib/commit/9654071)
feat(topology/algebra/module): add `is_scalar_tower` and `smul_comm_class` instances for `continuous_linear_map` ([#10375](https://github.com/leanprover-community/mathlib/pull/10375))
Also generalize some instances about `smul`.
#### Estimated changes
Modified src/topology/algebra/module.lean




## [2021-11-18 15:50:36](https://github.com/leanprover-community/mathlib/commit/0d09e99)
feat(measure_theory/integral/{set_to_l1,bochner}): generalize results about integrals to `set_to_fun` ([#10369](https://github.com/leanprover-community/mathlib/pull/10369))
The Bochner integral is a particular case of the `set_to_fun` construction. We generalize some lemmas which were proved for integrals to `set_to_fun`, notably the Lebesgue dominated convergence theorem.
#### Estimated changes
Modified src/measure_theory/integral/bochner.lean


Modified src/measure_theory/integral/set_to_l1.lean
- \+ *lemma* measure_theory.L1.norm_set_to_L1_le'
- \+ *lemma* measure_theory.L1.norm_set_to_L1_le
- \+ *lemma* measure_theory.L1.norm_set_to_L1_le_mul_norm'
- \+ *lemma* measure_theory.L1.norm_set_to_L1_le_mul_norm
- \+ *lemma* measure_theory.L1.norm_set_to_L1_le_norm_set_to_L1s_clm
- \+/\- *lemma* measure_theory.L1.set_to_L1_eq_set_to_L1s_clm
- \+ *lemma* measure_theory.L1.set_to_L1_lipschitz
- \+ *lemma* measure_theory.L1.simple_func.norm_set_to_L1s_clm_le'
- \+ *lemma* measure_theory.L1.simple_func.norm_set_to_L1s_clm_le
- \+ *lemma* measure_theory.L1.tendsto_set_to_L1
- \+ *lemma* measure_theory.continuous_at_set_to_fun_of_dominated
- \+ *lemma* measure_theory.continuous_set_to_fun
- \+ *lemma* measure_theory.continuous_set_to_fun_of_dominated
- \+ *lemma* measure_theory.norm_set_to_fun_le'
- \+ *lemma* measure_theory.norm_set_to_fun_le
- \+ *lemma* measure_theory.norm_set_to_fun_le_mul_norm'
- \+ *lemma* measure_theory.norm_set_to_fun_le_mul_norm
- \+ *lemma* measure_theory.set_to_fun_to_L1
- \+ *lemma* measure_theory.tendsto_set_to_fun_filter_of_dominated_convergence
- \+ *theorem* measure_theory.tendsto_set_to_fun_of_dominated_convergence



## [2021-11-18 14:41:58](https://github.com/leanprover-community/mathlib/commit/0ededd5)
chore(analysis/calculus): use `is_R_or_C` in several lemmas ([#10376](https://github.com/leanprover-community/mathlib/pull/10376))
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean
- \+/\- *lemma* convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at
- \+/\- *lemma* convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt
- \+/\- *theorem* convex.is_const_of_fderiv_within_eq_zero
- \+/\- *theorem* convex.lipschitz_on_with_of_nnnorm_deriv_le
- \+/\- *theorem* convex.lipschitz_on_with_of_nnnorm_deriv_within_le
- \+/\- *theorem* convex.lipschitz_on_with_of_nnnorm_fderiv_le
- \+/\- *theorem* convex.lipschitz_on_with_of_nnnorm_fderiv_within_le
- \+/\- *theorem* convex.lipschitz_on_with_of_nnnorm_has_deriv_within_le
- \+/\- *theorem* convex.lipschitz_on_with_of_nnnorm_has_fderiv_within_le
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_deriv_le
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_deriv_within_le
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_fderiv_le'
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_fderiv_le
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_fderiv_within_le'
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_fderiv_within_le
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_has_deriv_within_le
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_has_fderiv_within_le'
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_has_fderiv_within_le
- \+/\- *theorem* is_const_of_fderiv_eq_zero



## [2021-11-18 12:48:11](https://github.com/leanprover-community/mathlib/commit/198ed6b)
doc(order/monotone): fix 2 typos ([#10377](https://github.com/leanprover-community/mathlib/pull/10377))
#### Estimated changes
Modified src/order/monotone.lean




## [2021-11-18 02:36:10](https://github.com/leanprover-community/mathlib/commit/2f3b185)
chore(scripts): update nolints.txt ([#10374](https://github.com/leanprover-community/mathlib/pull/10374))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-11-17 19:11:23](https://github.com/leanprover-community/mathlib/commit/f8cbb3e)
chore(.docker): don't install unnecessary toolchains ([#10363](https://github.com/leanprover-community/mathlib/pull/10363))
#### Estimated changes
Modified .docker/debian/lean/Dockerfile


Modified .docker/gitpod/mathlib/Dockerfile




## [2021-11-17 19:11:22](https://github.com/leanprover-community/mathlib/commit/5d1363e)
feat(data/nat/parity): add lemmas ([#10352](https://github.com/leanprover-community/mathlib/pull/10352))
From FLT-regular.
#### Estimated changes
Modified src/data/nat/parity.lean
- \+ *lemma* nat.even_mul_self_pred
- \+ *lemma* nat.even_sub_one_of_prime_ne_two



## [2021-11-17 18:15:31](https://github.com/leanprover-community/mathlib/commit/276ab17)
feat(linear_algebra/bilinear_form): add lemmas ([#10353](https://github.com/leanprover-community/mathlib/pull/10353))
From FLT-regular.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean
- \+ *theorem* bilin_form.nondegenerate.to_matrix'
- \+ *theorem* bilin_form.nondegenerate.to_matrix
- \+ *lemma* bilin_form.nondegenerate_iff_det_ne_zero
- \- *theorem* bilin_form.nondegenerate_of_det_ne_zero'
- \+ *lemma* bilin_form.nondegenerate_to_bilin'_iff_det_ne_zero
- \+ *theorem* bilin_form.nondegenerate_to_bilin'_of_det_ne_zero'
- \+ *theorem* bilin_form.nondegenerate_to_matrix'_iff
- \+ *theorem* bilin_form.nondegenerate_to_matrix_iff
- \+ *lemma* matrix.nondegenerate_to_bilin'_iff
- \+ *lemma* matrix.nondegenerate_to_bilin'_iff_nondegenerate_to_bilin
- \+ *lemma* matrix.nondegenerate_to_bilin_iff



## [2021-11-17 15:37:37](https://github.com/leanprover-community/mathlib/commit/6f793bb)
chore(measure_theory/group/basic): drop measurability assumption ([#10367](https://github.com/leanprover-community/mathlib/pull/10367))
#### Estimated changes
Modified src/measure_theory/group/basic.lean
- \+/\- *lemma* measure_theory.measure.inv_apply



## [2021-11-17 14:46:00](https://github.com/leanprover-community/mathlib/commit/e14e87a)
chore(category_theory/filtered): slightly golf two proofs ([#10368](https://github.com/leanprover-community/mathlib/pull/10368))
#### Estimated changes
Modified src/category_theory/filtered.lean




## [2021-11-17 09:02:09](https://github.com/leanprover-community/mathlib/commit/c7441af)
feat(linear_algebra/bilinear_form): add lemmas about congr ([#10362](https://github.com/leanprover-community/mathlib/pull/10362))
With these some of the `nondegenerate` proofs can be golfed to oblivion, rather than reproving variants of the same statement over and over again.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean
- \+/\- *lemma* bilin_form.comp_congr
- \+/\- *lemma* bilin_form.congr_comp
- \+ *lemma* bilin_form.congr_congr
- \+ *lemma* bilin_form.congr_refl
- \+ *lemma* bilin_form.congr_trans
- \+ *lemma* bilin_form.nondegenerate.congr
- \+ *lemma* bilin_form.nondegenerate_congr_iff
- \+ *theorem* matrix.nondegenerate.to_bilin



## [2021-11-17 09:02:08](https://github.com/leanprover-community/mathlib/commit/568435c)
chore(analysis/inner_product_space/projection): typeclass inference for completeness ([#10357](https://github.com/leanprover-community/mathlib/pull/10357))
As of [#5408](https://github.com/leanprover-community/mathlib/pull/5408), most lemmas about orthogonal projection onto a subspace `K` / reflection through a subspace `K` / orthogonal complement of `K` which require `K` to be complete phrase this in terms of `complete_space K` rather than `is_complete K`, so that it can be found by typeclass inference.  A few still used the old way; this PR completes the switch.
#### Estimated changes
Modified src/analysis/inner_product_space/dual.lean


Modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* sub_orthogonal_projection_mem_orthogonal
- \+ *lemma* submodule.is_compl_orthogonal_of_complete_space
- \- *lemma* submodule.is_compl_orthogonal_of_is_complete
- \+/\- *lemma* submodule.orthogonal_eq_bot_iff
- \+ *lemma* submodule.sup_orthogonal_inf_of_complete_space
- \- *lemma* submodule.sup_orthogonal_inf_of_is_complete
- \- *lemma* submodule.sup_orthogonal_of_is_complete

Modified src/geometry/euclidean/basic.lean




## [2021-11-17 09:02:07](https://github.com/leanprover-community/mathlib/commit/d5c2b34)
chore(analysis/mean_inequalities): split mean_inequalities into two files ([#10355](https://github.com/leanprover-community/mathlib/pull/10355))
This PR puts all results related to power functions into a new file.
Currently, we prove convexity of `exp` and `pow`, then use those properties in `mean_inequalities`. I am refactoring some parts of the analysis library to reduce the use of derivatives. I want to prove convexity of exp without derivatives (in a future PR), prove Holder's inequality, then use it to prove the convexity of pow. This requires Holder's inequality to be in a file that does not use convexity of pow, hence the split.
I needed to change the proof of Holder's inequality since it used the generalized mean inequality (hence `pow`). I switched to the second possible proof mentioned in the file docstring.
I also moved some lemmas in `mean_inequalities` to have three main sections: AM-GM, then Young and a final section with Holder and Minkowski.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \- *lemma* ennreal.add_rpow_le_rpow_add
- \- *lemma* ennreal.rpow_add_le_add_rpow
- \- *theorem* ennreal.rpow_add_rpow_le
- \- *lemma* ennreal.rpow_add_rpow_le_add
- \- *theorem* ennreal.rpow_arith_mean_le_arith_mean2_rpow
- \- *theorem* ennreal.rpow_arith_mean_le_arith_mean_rpow
- \- *theorem* nnreal.arith_mean_le_rpow_mean
- \- *theorem* nnreal.pow_arith_mean_le_arith_mean_pow
- \- *theorem* nnreal.rpow_arith_mean_le_arith_mean2_rpow
- \- *theorem* nnreal.rpow_arith_mean_le_arith_mean_rpow
- \- *theorem* real.arith_mean_le_rpow_mean
- \- *theorem* real.pow_arith_mean_le_arith_mean_pow
- \- *theorem* real.pow_arith_mean_le_arith_mean_pow_of_even
- \- *theorem* real.rpow_arith_mean_le_arith_mean_rpow
- \- *theorem* real.zpow_arith_mean_le_arith_mean_zpow

Added src/analysis/mean_inequalities_pow.lean
- \+ *lemma* ennreal.add_rpow_le_rpow_add
- \+ *lemma* ennreal.rpow_add_le_add_rpow
- \+ *theorem* ennreal.rpow_add_rpow_le
- \+ *lemma* ennreal.rpow_add_rpow_le_add
- \+ *theorem* ennreal.rpow_arith_mean_le_arith_mean2_rpow
- \+ *theorem* ennreal.rpow_arith_mean_le_arith_mean_rpow
- \+ *theorem* nnreal.arith_mean_le_rpow_mean
- \+ *theorem* nnreal.pow_arith_mean_le_arith_mean_pow
- \+ *theorem* nnreal.rpow_arith_mean_le_arith_mean2_rpow
- \+ *theorem* nnreal.rpow_arith_mean_le_arith_mean_rpow
- \+ *theorem* real.arith_mean_le_rpow_mean
- \+ *theorem* real.pow_arith_mean_le_arith_mean_pow
- \+ *theorem* real.pow_arith_mean_le_arith_mean_pow_of_even
- \+ *theorem* real.rpow_arith_mean_le_arith_mean_rpow
- \+ *theorem* real.zpow_arith_mean_le_arith_mean_zpow

Modified src/measure_theory/integral/mean_inequalities.lean




## [2021-11-17 09:02:05](https://github.com/leanprover-community/mathlib/commit/60363a4)
feat(finset/basic): Adding `list.to_finset_union` and `list.to_finset_inter` ([#10351](https://github.com/leanprover-community/mathlib/pull/10351))
Two tiny lemmas, matching their counterparts for `multiset`
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* list.to_finset_inter
- \+ *lemma* list.to_finset_union



## [2021-11-17 07:06:12](https://github.com/leanprover-community/mathlib/commit/8f6fd1b)
lint(*): curly braces linter ([#10280](https://github.com/leanprover-community/mathlib/pull/10280))
This PR:
1. Adds a style linter for curly braces: a line shall never end with `{` or start with `}` (modulo white space)
2. Adds `scripts/cleanup-braces.{sh,py}` to reflow lines that violate (1)
3. Runs the scripts from (2) to generate a boatload of changes in mathlib
4. Fixes one line that became to long due to (3)
#### Estimated changes
Modified archive/imo/imo1960_q1.lean


Modified archive/imo/imo1988_q6.lean


Modified archive/sensitivity.lean


Added scripts/cleanup-braces.py


Added scripts/cleanup-braces.sh


Modified scripts/lint-style.py


Modified src/algebra/algebra/basic.lean
- \+/\- *def* algebra.semiring_to_ring

Modified src/algebra/algebra/operations.lean


Modified src/algebra/category/CommRing/pushout.lean
- \+/\- *lemma* CommRing.pushout_cocone_X
- \+/\- *lemma* CommRing.pushout_cocone_inl
- \+/\- *lemma* CommRing.pushout_cocone_inr

Modified src/algebra/category/Group/images.lean


Modified src/algebra/category/Mon/adjunctions.lean


Modified src/algebra/continued_fractions/convergents_equiv.lean


Modified src/algebra/direct_sum/ring.lean


Modified src/algebra/free_algebra.lean


Modified src/algebra/gcd_monoid/basic.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/units.lean


Modified src/algebra/group_with_zero/basic.lean


Modified src/algebra/lattice_ordered_group.lean


Modified src/algebra/lie/of_associative.lean


Modified src/algebra/lie/subalgebra.lean


Modified src/algebra/module/basic.lean


Modified src/algebra/module/linear_map.lean


Modified src/algebra/module/submodule_lattice.lean


Modified src/algebra/monoid_algebra/basic.lean


Modified src/algebra/order/monoid.lean


Modified src/algebra/star/chsh.lean


Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/algebraic_topology/cech_nerve.lean


Modified src/analysis/inner_product_space/basic.lean


Modified src/analysis/inner_product_space/projection.lean


Modified src/analysis/normed_space/lattice_ordered_group.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/special_functions/bernstein.lean


Modified src/category_theory/limits/concrete_category.lean


Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/monoidal/Mon_.lean


Modified src/category_theory/monoidal/rigid.lean


Modified src/category_theory/sites/sheafification.lean


Modified src/combinatorics/colex.lean


Modified src/computability/halting.lean


Modified src/computability/partrec.lean


Modified src/computability/partrec_code.lean


Modified src/computability/primrec.lean


Modified src/computability/regular_expressions.lean


Modified src/computability/tm_to_partrec.lean


Modified src/computability/turing_machine.lean


Modified src/control/traversable/derive.lean


Modified src/data/buffer/parser/numeral.lean


Modified src/data/equiv/basic.lean


Modified src/data/equiv/module.lean


Modified src/data/equiv/set.lean


Modified src/data/finsupp/basic.lean


Modified src/data/int/basic.lean


Modified src/data/list/basic.lean


Modified src/data/list/defs.lean


Modified src/data/list/perm.lean


Modified src/data/list/sigma.lean


Modified src/data/list/sort.lean


Modified src/data/mllist.lean


Modified src/data/multiset/basic.lean


Modified src/data/multiset/functor.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/gcd.lean


Modified src/data/nat/sqrt.lean


Modified src/data/num/lemmas.lean


Modified src/data/pequiv.lean


Modified src/data/pfunctor/multivariate/M.lean


Modified src/data/pnat/basic.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/qpf/multivariate/constructions/cofix.lean


Modified src/data/qpf/multivariate/constructions/const.lean


Modified src/data/qpf/multivariate/constructions/sigma.lean


Modified src/data/qpf/univariate/basic.lean


Modified src/data/rat/basic.lean


Modified src/data/rat/order.lean


Modified src/data/rbmap/default.lean


Modified src/data/rbtree/basic.lean


Modified src/data/rbtree/find.lean


Modified src/data/rbtree/insert.lean


Modified src/data/rbtree/main.lean


Modified src/data/rbtree/min_max.lean


Modified src/data/set/enumerate.lean


Modified src/data/set/intervals/basic.lean


Modified src/data/vector3.lean


Modified src/deprecated/subfield.lean


Modified src/deprecated/subring.lean


Modified src/field_theory/adjoin.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/galois.lean


Modified src/field_theory/perfect_closure.lean


Modified src/field_theory/separable.lean


Modified src/geometry/manifold/charted_space.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/concrete_cycle.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/basic.lean


Modified src/linear_algebra/affine_space/combination.lean


Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/clifford_algebra/basic.lean


Modified src/linear_algebra/clifford_algebra/equivs.lean


Modified src/linear_algebra/dfinsupp.lean


Modified src/linear_algebra/exterior_algebra.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/lagrange.lean


Modified src/linear_algebra/matrix/polynomial.lean


Modified src/linear_algebra/matrix/to_linear_equiv.lean


Modified src/linear_algebra/multilinear/basic.lean


Modified src/linear_algebra/multilinear/basis.lean


Modified src/linear_algebra/pi_tensor_product.lean


Modified src/linear_algebra/tensor_algebra.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/logic/relation.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/measure_theory/tactic.lean


Modified src/meta/expr_lens.lean


Modified src/model_theory/basic.lean


Modified src/number_theory/dioph.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/number_theory/pell.lean


Modified src/number_theory/zsqrtd/basic.lean


Modified src/order/atoms.lean


Modified src/order/bounded_lattice.lean


Modified src/order/filter/basic.lean


Modified src/order/lattice.lean


Modified src/order/well_founded_set.lean


Modified src/order/zorn.lean


Modified src/representation_theory/maschke.lean


Modified src/ring_theory/derivation.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/bernstein.lean


Modified src/ring_theory/polynomial/pochhammer.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/valuation/basic.lean


Modified src/ring_theory/witt_vector/is_poly.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean


Modified src/set_theory/lists.lean


Modified src/set_theory/ordinal_notation.lean


Modified src/tactic/alias.lean


Modified src/tactic/apply.lean


Modified src/tactic/apply_fun.lean


Modified src/tactic/chain.lean


Modified src/tactic/converter/apply_congr.lean


Modified src/tactic/converter/old_conv.lean


Modified src/tactic/core.lean


Modified src/tactic/dependencies.lean


Modified src/tactic/doc_commands.lean


Modified src/tactic/explode.lean


Modified src/tactic/ext.lean


Modified src/tactic/fresh_names.lean


Modified src/tactic/generalizes.lean


Modified src/tactic/hint.lean


Modified src/tactic/induction.lean


Modified src/tactic/interactive.lean


Modified src/tactic/interactive_expr.lean


Modified src/tactic/itauto.lean


Modified src/tactic/lift.lean


Modified src/tactic/lint/basic.lean


Modified src/tactic/lint/type_classes.lean


Modified src/tactic/local_cache.lean


Modified src/tactic/localized.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/norm_cast.lean


Modified src/tactic/norm_num.lean


Modified src/tactic/restate_axiom.lean


Modified src/tactic/simp_command.lean


Modified src/tactic/simpa.lean


Modified src/tactic/simps.lean


Modified src/tactic/squeeze.lean


Modified src/tactic/tidy.lean


Modified src/tactic/transfer.lean


Modified src/tactic/transform_decl.lean


Modified src/tactic/unify_equations.lean


Modified src/testing/slim_check/functions.lean


Modified src/testing/slim_check/testable.lean


Modified src/topology/category/Profinite/cofiltered_limit.lean


Modified src/topology/constructions.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/list.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/sheaves/sheaf_condition/sites.lean


Modified src/topology/tactic.lean


Modified src/topology/uniform_space/basic.lean




## [2021-11-17 04:51:54](https://github.com/leanprover-community/mathlib/commit/2bdadb4)
feat(order/imp): define `lattice.imp` and `lattice.biimp` ([#10327](https://github.com/leanprover-community/mathlib/pull/10327))
#### Estimated changes
Modified src/order/boolean_algebra.lean
- \+/\- *lemma* sdiff_eq_bot_iff

Added src/order/imp.lean
- \+ *def* lattice.biimp
- \+ *lemma* lattice.biimp_comm
- \+ *lemma* lattice.biimp_eq_iff
- \+ *lemma* lattice.biimp_eq_top_iff
- \+ *lemma* lattice.biimp_mp
- \+ *lemma* lattice.biimp_mpr
- \+ *lemma* lattice.biimp_self
- \+ *lemma* lattice.biimp_symm
- \+ *lemma* lattice.bot_imp
- \+ *lemma* lattice.compl_biimp
- \+ *lemma* lattice.compl_biimp_compl
- \+ *lemma* lattice.compl_imp
- \+ *lemma* lattice.compl_imp_compl
- \+ *lemma* lattice.compl_sdiff
- \+ *lemma* lattice.compl_symm_diff
- \+ *def* lattice.imp
- \+ *lemma* lattice.imp_bot
- \+ *lemma* lattice.imp_eq_arrow
- \+ *lemma* lattice.imp_eq_bot_iff
- \+ *lemma* lattice.imp_eq_top_iff
- \+ *lemma* lattice.imp_inf_le
- \+ *lemma* lattice.imp_mono
- \+ *lemma* lattice.imp_self
- \+ *lemma* lattice.imp_top
- \+ *lemma* lattice.inf_imp_eq
- \+ *lemma* lattice.inf_imp_eq_imp_imp
- \+ *lemma* lattice.le_imp_iff
- \+ *lemma* lattice.top_imp

Modified src/order/lattice.lean




## [2021-11-16 23:48:06](https://github.com/leanprover-community/mathlib/commit/0a2a922)
feat(combinatorics/set_family/shadow): Shadow of a set family ([#10223](https://github.com/leanprover-community/mathlib/pull/10223))
This defines `shadow 𝒜` where `𝒜 : finset (finset α))`.
#### Estimated changes
Added src/combinatorics/set_family/shadow.lean
- \+ *lemma* finset.erase_mem_shadow
- \+ *lemma* finset.exists_subset_of_mem_shadow
- \+ *lemma* finset.mem_shadow_iff
- \+ *lemma* finset.mem_shadow_iff_exists_mem_card_add
- \+ *lemma* finset.mem_shadow_iff_exists_mem_card_add_one
- \+ *lemma* finset.mem_shadow_iff_insert_mem
- \+ *def* finset.shadow
- \+ *lemma* finset.shadow_empty
- \+ *lemma* finset.shadow_monotone



## [2021-11-16 23:48:05](https://github.com/leanprover-community/mathlib/commit/7fec401)
feat(topology/metric_space/hausdorff_distance): add definition and lemmas about open thickenings of subsets ([#10188](https://github.com/leanprover-community/mathlib/pull/10188))
Add definition and basic API about open thickenings of subsets in metric spaces, in preparation for the portmanteau theorem on characterizations of weak convergence of Borel probability measures.
#### Estimated changes
Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* metric.is_open_thickening
- \+ *lemma* metric.mem_thickening_iff
- \+ *def* metric.thickening
- \+ *lemma* metric.thickening_empty
- \+ *lemma* metric.thickening_eq_bUnion_ball
- \+ *lemma* metric.thickening_eq_preimage_inf_edist
- \+ *lemma* metric.thickening_mono
- \+ *lemma* metric.thickening_subset_of_subset



## [2021-11-16 21:57:02](https://github.com/leanprover-community/mathlib/commit/bce0ede)
feat(number_theory/divisors): mem_divisors_self ([#10359](https://github.com/leanprover-community/mathlib/pull/10359))
From flt-regular.
#### Estimated changes
Modified src/number_theory/divisors.lean
- \+ *lemma* nat.mem_divisors_self



## [2021-11-16 21:57:00](https://github.com/leanprover-community/mathlib/commit/8f7971a)
refactor(linear_algebra/bilinear_form): Change namespace of is_refl, is_symm, and is_alt ([#10338](https://github.com/leanprover-community/mathlib/pull/10338))
The propositions `is_refl`, `is_symm`, and `is_alt` are now in the
namespace `bilin_form`. Moreover, `is_sym` is now renamed to `is_symm`.
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/linear_algebra/bilinear_form.lean
- \- *def* alt_bilin_form.is_alt
- \- *lemma* alt_bilin_form.is_refl
- \- *lemma* alt_bilin_form.neg
- \- *lemma* alt_bilin_form.ortho_sym
- \- *lemma* alt_bilin_form.self_eq_zero
- \+ *lemma* bilin_form.is_alt.is_refl
- \+ *lemma* bilin_form.is_alt.neg
- \+ *lemma* bilin_form.is_alt.ortho_comm
- \+ *lemma* bilin_form.is_alt.self_eq_zero
- \+ *def* bilin_form.is_alt
- \+ *lemma* bilin_form.is_refl.eq_zero
- \+ *lemma* bilin_form.is_refl.ortho_comm
- \+ *def* bilin_form.is_refl
- \+ *lemma* bilin_form.is_symm.is_refl
- \+ *lemma* bilin_form.is_symm.ortho_comm
- \+ *def* bilin_form.is_symm
- \+ *lemma* bilin_form.is_symm_iff_flip'
- \+/\- *lemma* bilin_form.le_orthogonal_orthogonal
- \- *lemma* bilin_form.restrict_sym
- \+ *lemma* bilin_form.restrict_symm
- \- *lemma* refl_bilin_form.eq_zero
- \- *def* refl_bilin_form.is_refl
- \- *lemma* refl_bilin_form.ortho_sym
- \- *lemma* sym_bilin_form.is_refl
- \- *def* sym_bilin_form.is_sym
- \- *lemma* sym_bilin_form.is_sym_iff_flip'
- \- *lemma* sym_bilin_form.ortho_sym
- \- *lemma* sym_bilin_form.sym

Modified src/linear_algebra/quadratic_form/basic.lean
- \- *lemma* quadratic_form.associated_is_sym
- \+ *lemma* quadratic_form.associated_is_symm
- \+/\- *lemma* quadratic_form.associated_left_inverse

Modified src/ring_theory/trace.lean
- \- *lemma* algebra.trace_form_is_sym
- \+ *lemma* algebra.trace_form_is_symm



## [2021-11-16 21:56:59](https://github.com/leanprover-community/mathlib/commit/698eb1e)
feat(data/fin/basic): add lemmas about fin.cast ([#10329](https://github.com/leanprover-community/mathlib/pull/10329))
#### Estimated changes
Modified src/data/fin/basic.lean
- \+ *lemma* fin.add_nat_cast
- \+ *lemma* fin.cast_add_cast
- \+ *lemma* fin.cast_add_nat_left
- \+ *lemma* fin.cast_add_nat_right
- \+ *lemma* fin.cast_add_nat_zero
- \+ *lemma* fin.cast_cast_add_left
- \+ *lemma* fin.cast_cast_add_right
- \+ *lemma* fin.cast_nat_add_left
- \+ *lemma* fin.cast_nat_add_right
- \+ *lemma* fin.cast_nat_add_zero
- \+ *lemma* fin.cast_succ_eq
- \+ *lemma* fin.nat_add_cast
- \+ *lemma* fin.succ_cast_eq



## [2021-11-16 18:44:35](https://github.com/leanprover-community/mathlib/commit/9fa14a6)
feat(topology/uniform_space): properties of uniform convergence ([#9958](https://github.com/leanprover-community/mathlib/pull/9958))
* From the sphere eversion project
* multiple proofs were golfed by @PatrickMassot 
* Probably some proofs can be golfed quite heavily
Co-authored by: Patrick Massot <patrickmassot@free.fr>
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* imp_forall_iff

Modified src/order/filter/basic.lean
- \+ *lemma* filter.mem_prod_principal
- \+ *lemma* filter.mem_prod_top

Modified src/topology/uniform_space/compact_separated.lean
- \+ *lemma* continuous.tendsto_uniformly
- \+ *lemma* continuous_on.tendsto_uniformly

Modified src/topology/uniform_space/separation.lean
- \+ *lemma* is_separated.eq_of_uniform_continuous
- \+ *lemma* is_separated.mono
- \+ *lemma* is_separated.prod

Modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* tendsto_prod_top_iff
- \+ *lemma* tendsto_uniformly_iff_tendsto
- \+ *lemma* tendsto_uniformly_on_iff_tendsto
- \+ *lemma* uniform_continuous_on.tendsto_uniformly
- \+ *lemma* uniform_continuous₂.tendsto_uniformly



## [2021-11-16 18:44:34](https://github.com/leanprover-community/mathlib/commit/d6b83d8)
feat(number_theory): define the class number ([#9071](https://github.com/leanprover-community/mathlib/pull/9071))
We instantiate the finiteness proof of the class group for rings of integers, and define the class number of a number field, or of a separable function field, as the finite cardinality of the class group.
Co-Authored-By: Ashvni <ashvni.n@gmail.com>
Co-Authored-By: Filippo A. E. Nuccio <filippo.nuccio@univ-st-etienne.fr>
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \+ *lemma* polynomial.normalize_monic

Modified src/number_theory/class_number/finite.lean


Added src/number_theory/class_number/function_field.lean
- \+ *theorem* function_field.class_number_eq_one_iff

Added src/number_theory/class_number/number_field.lean
- \+ *theorem* number_field.class_number_eq_one_iff
- \+ *theorem* rat.class_number_eq

Modified src/number_theory/function_field.lean


Modified src/number_theory/number_field.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *lemma* ufm_of_gcd_of_wf_dvd_monoid



## [2021-11-16 15:57:33](https://github.com/leanprover-community/mathlib/commit/f780788)
feat(dynamics): define `{mul,add}_action.is_minimal` ([#10311](https://github.com/leanprover-community/mathlib/pull/10311))
#### Estimated changes
Added src/dynamics/minimal.lean
- \+ *lemma* dense_of_nonempty_smul_invariant
- \+ *lemma* dense_range_smul
- \+ *lemma* eq_empty_or_univ_of_smul_invariant_closed
- \+ *lemma* is_compact.exists_finite_cover_smul
- \+ *lemma* is_minimal_iff_closed_smul_invariant
- \+ *lemma* is_open.Union_preimage_smul
- \+ *lemma* is_open.Union_smul
- \+ *lemma* is_open.exists_smul_mem
- \+ *lemma* mul_action.dense_orbit

Modified src/group_theory/group_action/basic.lean
- \+ *lemma* mul_action.orbit_nonempty



## [2021-11-16 12:48:56](https://github.com/leanprover-community/mathlib/commit/d36f17f)
feat(linear_algebra/sesquilinear_form): Add is_refl for sesq_form.is_alt ([#10341](https://github.com/leanprover-community/mathlib/pull/10341))
Lemma `is_refl` shows that an alternating sesquilinear form is reflexive.
Refactored `sesquilinear_form` in a similar way as `bilinear_form` will be in [#10338](https://github.com/leanprover-community/mathlib/pull/10338).
#### Estimated changes
Modified src/linear_algebra/sesquilinear_form.lean
- \- *def* alt_sesq_form.is_alt
- \- *lemma* alt_sesq_form.neg
- \- *lemma* alt_sesq_form.self_eq_zero
- \- *lemma* refl_sesq_form.eq_zero
- \- *def* refl_sesq_form.is_refl
- \- *lemma* refl_sesq_form.ortho_sym
- \+ *lemma* sesq_form.is_alt.is_refl
- \+ *lemma* sesq_form.is_alt.neg
- \+ *lemma* sesq_form.is_alt.ortho_comm
- \+ *lemma* sesq_form.is_alt.self_eq_zero
- \+ *def* sesq_form.is_alt
- \+ *lemma* sesq_form.is_refl.eq_zero
- \+ *lemma* sesq_form.is_refl.ortho_comm
- \+ *def* sesq_form.is_refl
- \+ *lemma* sesq_form.is_symm.is_refl
- \+ *lemma* sesq_form.is_symm.ortho_comm
- \+ *def* sesq_form.is_symm
- \- *lemma* sym_sesq_form.is_refl
- \- *def* sym_sesq_form.is_sym
- \- *lemma* sym_sesq_form.ortho_sym
- \- *lemma* sym_sesq_form.sym



## [2021-11-16 12:48:55](https://github.com/leanprover-community/mathlib/commit/7f4b91b)
feat(linear_algebra/determinant): the determinant associated to the standard basis of the free module is the usual matrix determinant ([#10278](https://github.com/leanprover-community/mathlib/pull/10278))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* pi.basis_fun_det

Modified src/linear_algebra/matrix/basis.lean
- \+ *lemma* basis.coe_pi_basis_fun.to_matrix_eq_transpose

Modified src/linear_algebra/matrix/determinant.lean
- \+ *def* matrix.det_row_alternating
- \- *def* matrix.det_row_multilinear



## [2021-11-16 12:48:54](https://github.com/leanprover-community/mathlib/commit/e20af15)
feat(field_theory): define the field of rational functions `ratfunc` ([#9563](https://github.com/leanprover-community/mathlib/pull/9563))
This PR defines `ratfunc K` as the field of rational functions over a field `K`, in terms of `fraction_ring (polynomial K)`. I have been careful to use `structure`s and `@[irreducible] def`s. Not only does that make for a nicer API, it also helps quite a bit with unification since the check can stop at `ratfunc` and doesn't have to start unfolding along the lines of `fraction_field.field → localization.comm_ring → localization.comm_monoid → localization.has_mul` and/or `polynomial.integral_domain → polynomial.comm_ring → polynomial.ring → polynomial.semiring`.
Most of the API is automatically derived from the (components of the) `is_fraction_ring` instance: the map `polynomial K → ratpoly K` is `algebra_map`, the isomorphism to `fraction_ring (polynomial K)` is `is_localization.alg_equiv`, ...
As a first application to verify that the definitions work, I rewrote `function_field` in terms of `ratfunc`.
#### Estimated changes
Modified docs/undergrad.yaml


Added src/field_theory/ratfunc.lean
- \+ *def* ratfunc.C
- \+ *def* ratfunc.X
- \+ *lemma* ratfunc.algebra_map_C
- \+ *lemma* ratfunc.algebra_map_X
- \+ *lemma* ratfunc.algebra_map_comp_C
- \+ *lemma* ratfunc.algebra_map_eq_C
- \+ *lemma* ratfunc.algebra_map_eq_zero_iff
- \+ *lemma* ratfunc.algebra_map_injective
- \+ *lemma* ratfunc.algebra_map_ne_zero
- \+ *def* ratfunc.aux_equiv
- \+ *lemma* ratfunc.aux_equiv_eq
- \+ *def* ratfunc.denom
- \+ *lemma* ratfunc.denom_C
- \+ *lemma* ratfunc.denom_X
- \+ *lemma* ratfunc.denom_add_dvd
- \+ *lemma* ratfunc.denom_algebra_map
- \+ *lemma* ratfunc.denom_div
- \+ *lemma* ratfunc.denom_div_dvd
- \+ *lemma* ratfunc.denom_dvd
- \+ *lemma* ratfunc.denom_mul_dvd
- \+ *lemma* ratfunc.denom_ne_zero
- \+ *lemma* ratfunc.denom_one
- \+ *lemma* ratfunc.denom_zero
- \+ *def* ratfunc.eval
- \+ *lemma* ratfunc.eval_C
- \+ *lemma* ratfunc.eval_X
- \+ *lemma* ratfunc.eval_add
- \+ *lemma* ratfunc.eval_algebra_map
- \+ *lemma* ratfunc.eval_eq_zero_of_eval₂_denom_eq_zero
- \+ *lemma* ratfunc.eval_mul
- \+ *lemma* ratfunc.eval_one
- \+ *lemma* ratfunc.eval_zero
- \+ *lemma* ratfunc.eval₂_denom_ne_zero
- \+ *lemma* ratfunc.lift_on'_div
- \+ *lemma* ratfunc.lift_on'_mk
- \+ *lemma* ratfunc.lift_on_div
- \+ *lemma* ratfunc.lift_on_mk
- \+ *lemma* ratfunc.mk_coe_def
- \+ *lemma* ratfunc.mk_def_of_mem
- \+ *lemma* ratfunc.mk_def_of_ne
- \+ *lemma* ratfunc.mk_eq_div'
- \+ *lemma* ratfunc.mk_eq_div
- \+ *lemma* ratfunc.mk_eq_localization_mk
- \+ *lemma* ratfunc.mk_eq_mk
- \+ *lemma* ratfunc.mk_one'
- \+ *lemma* ratfunc.mk_one
- \+ *lemma* ratfunc.mk_smul
- \+ *lemma* ratfunc.mk_zero
- \+ *lemma* ratfunc.monic_denom
- \+ *lemma* ratfunc.mul_inv_cancel
- \+ *def* ratfunc.num
- \+ *lemma* ratfunc.num_C
- \+ *lemma* ratfunc.num_X
- \+ *lemma* ratfunc.num_algebra_map
- \+ *def* ratfunc.num_denom
- \+ *lemma* ratfunc.num_denom_add
- \+ *lemma* ratfunc.num_denom_div
- \+ *lemma* ratfunc.num_denom_mul
- \+ *lemma* ratfunc.num_div
- \+ *lemma* ratfunc.num_div_denom
- \+ *lemma* ratfunc.num_div_dvd
- \+ *lemma* ratfunc.num_dvd
- \+ *lemma* ratfunc.num_eq_zero_iff
- \+ *lemma* ratfunc.num_mul_dvd
- \+ *lemma* ratfunc.num_mul_eq_mul_denom_iff
- \+ *lemma* ratfunc.num_ne_zero
- \+ *lemma* ratfunc.num_one
- \+ *lemma* ratfunc.num_zero
- \+ *lemma* ratfunc.of_fraction_ring_add
- \+ *lemma* ratfunc.of_fraction_ring_algebra_map
- \+ *lemma* ratfunc.of_fraction_ring_comp_algebra_map
- \+ *lemma* ratfunc.of_fraction_ring_div
- \+ *lemma* ratfunc.of_fraction_ring_eq
- \+ *lemma* ratfunc.of_fraction_ring_injective
- \+ *lemma* ratfunc.of_fraction_ring_inv
- \+ *lemma* ratfunc.of_fraction_ring_mk'
- \+ *lemma* ratfunc.of_fraction_ring_mul
- \+ *lemma* ratfunc.of_fraction_ring_neg
- \+ *lemma* ratfunc.of_fraction_ring_one
- \+ *lemma* ratfunc.of_fraction_ring_sub
- \+ *lemma* ratfunc.of_fraction_ring_zero
- \+ *lemma* ratfunc.to_fraction_ring_eq
- \+ *lemma* ratfunc.to_fraction_ring_injective
- \+ *structure* ratfunc

Modified src/group_theory/group_action/defs.lean


Modified src/number_theory/function_field.lean
- \+/\- *abbreviation* function_field



## [2021-11-16 08:37:36](https://github.com/leanprover-community/mathlib/commit/f01399c)
chore(order/filter/basic): add 2 trivial `simp` lemmas ([#10344](https://github.com/leanprover-community/mathlib/pull/10344))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_eq_univ
- \+ *lemma* filter.eventually_mem_set



## [2021-11-16 08:37:35](https://github.com/leanprover-community/mathlib/commit/1181c99)
feat(algebra/order/archimedean): upgrade some `∃` to `∃!` ([#10343](https://github.com/leanprover-community/mathlib/pull/10343))
#### Estimated changes
Modified src/algebra/order/archimedean.lean
- \- *lemma* exists_add_int_smul_mem_Ico
- \- *lemma* exists_add_int_smul_mem_Ioc
- \- *lemma* exists_int_smul_near_of_pos'
- \- *lemma* exists_int_smul_near_of_pos
- \+ *lemma* exists_unique_add_zsmul_mem_Ico
- \+ *lemma* exists_unique_add_zsmul_mem_Ioc
- \+ *lemma* exists_unique_zsmul_near_of_pos'
- \+ *lemma* exists_unique_zsmul_near_of_pos

Modified src/algebra/periodic.lean


Modified src/group_theory/archimedean.lean


Modified src/logic/function/basic.lean
- \- *lemma* function.bijective.exists_unique
- \+ *lemma* function.bijective.exists_unique_iff
- \- *theorem* function.surjective.exists
- \- *theorem* function.surjective.exists₂
- \- *theorem* function.surjective.exists₃
- \- *theorem* function.surjective.forall
- \- *theorem* function.surjective.forall₂
- \- *theorem* function.surjective.forall₃



## [2021-11-16 06:43:17](https://github.com/leanprover-community/mathlib/commit/30abde6)
chore(*): clean up some unused open statements and extra simps ([#10342](https://github.com/leanprover-community/mathlib/pull/10342))
We clean up some specific statements that are essentially no-ops in the library, i.e. opening a namespace and then never using it and using a simp-set larger than actually needed.
This is a preparatory miscellany of small fixes for a larger PR upcoming from me and Johan to reduce imports in the library.
Hopefully merging this first will make the content of that PR clearer.
#### Estimated changes
Modified src/category_theory/triangulated/basic.lean


Modified src/data/list/basic.lean


Modified src/data/matrix/basic.lean


Modified src/measure_theory/measurable_space_def.lean


Modified src/tactic/restate_axiom.lean




## [2021-11-16 04:55:57](https://github.com/leanprover-community/mathlib/commit/979f0e8)
feat(data/fin/basic): extract `div_nat`  and `mod_nat` from `fin_prod_fin_equiv` ([#10339](https://github.com/leanprover-community/mathlib/pull/10339))
This makes it a little easier to tell which component is div and which is mod from the docs alone, and also makes these available earlier than `data/equiv/fin`.
#### Estimated changes
Modified src/data/equiv/fin.lean


Modified src/data/fin/basic.lean
- \+ *lemma* fin.coe_div_nat
- \+ *lemma* fin.coe_mod_nat
- \+ *def* fin.div_nat
- \+ *def* fin.mod_nat



## [2021-11-16 03:17:25](https://github.com/leanprover-community/mathlib/commit/bd80b33)
chore(ring_theory/subring): fix stale docstring ([#10340](https://github.com/leanprover-community/mathlib/pull/10340))
Oversight from https://github.com/leanprover-community/mathlib/pull/10332
#### Estimated changes
Modified src/ring_theory/subring.lean




## [2021-11-16 02:30:50](https://github.com/leanprover-community/mathlib/commit/9264f30)
feat(analysis/calculus/times_cont_diff): continuous affine maps are smooth ([#10335](https://github.com/leanprover-community/mathlib/pull/10335))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Added src/analysis/calculus/affine_map.lean
- \+ *lemma* continuous_affine_map.times_cont_diff



## [2021-11-16 00:29:07](https://github.com/leanprover-community/mathlib/commit/bff69c9)
feat(data/nat/lattice): add ```Inf_add``` lemma  ([#10008](https://github.com/leanprover-community/mathlib/pull/10008))
Adds a lemma about Inf on natural numbers. It will be needed for the count PR.
#### Estimated changes
Modified src/data/nat/lattice.lean
- \+ *lemma* nat.Inf_add'
- \+ *lemma* nat.Inf_add
- \+ *lemma* nat.Inf_empty



## [2021-11-16 00:29:05](https://github.com/leanprover-community/mathlib/commit/ddb6c75)
feat(algebra/homology/exact): preadditive.exact_iff_exact_of_iso ([#9979](https://github.com/leanprover-community/mathlib/pull/9979))
#### Estimated changes
Modified src/algebra/homology/exact.lean
- \+ *lemma* category_theory.preadditive.exact_iff_exact_of_iso
- \+ *lemma* category_theory.preadditive.exact_of_iso_of_exact

Modified src/category_theory/arrow.lean
- \+ *lemma* category_theory.arrow.inv_left_hom_right
- \+ *lemma* category_theory.arrow.left_hom_inv_right



## [2021-11-15 22:46:44](https://github.com/leanprover-community/mathlib/commit/9074095)
chore(linear_algebra/pi_tensor_product): add reindex_reindex ([#10336](https://github.com/leanprover-community/mathlib/pull/10336))
#### Estimated changes
Modified src/linear_algebra/pi_tensor_product.lean
- \+ *lemma* pi_tensor_product.reindex_reindex



## [2021-11-15 22:46:43](https://github.com/leanprover-community/mathlib/commit/a0f2c47)
feat(logic/relation): induction principles for `trans_gen` ([#10331](https://github.com/leanprover-community/mathlib/pull/10331))
Corresponding induction principles already exist for `refl_trans_gen`.
#### Estimated changes
Modified src/logic/relation.lean
- \+ *lemma* relation.trans_gen.head_induction_on
- \+ *lemma* relation.trans_gen.trans_induction_on



## [2021-11-15 22:46:41](https://github.com/leanprover-community/mathlib/commit/65ff54c)
feat(data/fintype/basic): add fin_injective ([#10330](https://github.com/leanprover-community/mathlib/pull/10330))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *theorem* fin.cast_eq_cast'
- \+ *lemma* fin_injective



## [2021-11-15 21:01:46](https://github.com/leanprover-community/mathlib/commit/93047c5)
feat(linear_algebra/determinant): linear coordinates are ratio of determinants ([#10261](https://github.com/leanprover-community/mathlib/pull/10261))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.mk_coord_apply
- \+ *lemma* basis.mk_coord_apply_eq
- \+ *lemma* basis.mk_coord_apply_ne

Modified src/linear_algebra/determinant.lean
- \+ *lemma* basis.det_smul_mk_coord_eq_det_update

Modified src/linear_algebra/multilinear/basic.lean
- \+/\- *def* multilinear_map.to_linear_map



## [2021-11-15 21:01:45](https://github.com/leanprover-community/mathlib/commit/7ccc7ae)
feat(topology/homotopy/fundamental_groupoid): The functor from `Top` to `Groupoid` ([#10195](https://github.com/leanprover-community/mathlib/pull/10195))
I have no idea if the ways I've done things is the right way, eg. I don't know if I need to be thinking about universes when defining the functor, so comments about that are definitely welcome.
#### Estimated changes
Modified src/data/quot.lean
- \+ *lemma* quotient.map₂_mk

Modified src/topology/homotopy/basic.lean
- \+/\- *lemma* continuous_map.homotopic.symm
- \+/\- *lemma* continuous_map.homotopic_rel.symm

Modified src/topology/homotopy/fundamental_groupoid.lean
- \+ *lemma* fundamental_groupoid.comp_eq
- \+ *def* fundamental_groupoid.fundamental_groupoid_functor

Modified src/topology/homotopy/path.lean
- \+ *lemma* path.homotopic.hcomp
- \+ *lemma* path.homotopic.map
- \+/\- *lemma* path.homotopic.symm
- \+ *def* path.homotopy.map

Modified src/topology/path_connected.lean
- \+ *lemma* path.map_id
- \+ *lemma* path.map_map
- \+ *lemma* path.map_symm
- \+ *lemma* path.map_trans



## [2021-11-15 21:01:44](https://github.com/leanprover-community/mathlib/commit/9c03e9d)
feat(data/fintype): computable trunc bijection from fin ([#10141](https://github.com/leanprover-community/mathlib/pull/10141))
When a type `X` lacks decidable equality, there is still computably a bijection `fin (card X) -> X` using `trunc`.
Also, move `fintype.equiv_fin_of_forall_mem_list` to `list.nodup.nth_le_equiv_of_forall_mem_list`.
#### Estimated changes
Modified src/data/equiv/list.lean


Modified src/data/fintype/basic.lean
- \- *def* fintype.equiv_fin_of_forall_mem_list
- \+ *def* fintype.trunc_fin_bijection

Modified src/data/list/nodup_equiv_fin.lean
- \- *lemma* list.nodup.coe_nth_le_equiv_apply
- \- *lemma* list.nodup.coe_nth_le_equiv_symm_apply
- \+ *def* list.nodup.nth_le_bijection_of_forall_mem_list
- \+ *def* list.nodup.nth_le_equiv_of_forall_mem_list



## [2021-11-15 19:12:05](https://github.com/leanprover-community/mathlib/commit/7b60768)
feat(ring_theory/subring): weaken typeclass assumption for `units.pos_subgroup` ([#10332](https://github.com/leanprover-community/mathlib/pull/10332))
#### Estimated changes
Modified src/ring_theory/subring.lean
- \+/\- *lemma* units.mem_pos_subgroup
- \+/\- *def* units.pos_subgroup



## [2021-11-15 19:12:03](https://github.com/leanprover-community/mathlib/commit/7803884)
feat(data/pi): Composition of addition/subtraction/... of functions ([#10305](https://github.com/leanprover-community/mathlib/pull/10305))
#### Estimated changes
Modified src/algebra/group/pi.lean
- \- *lemma* pi.comp_one
- \- *lemma* pi.const_one
- \- *lemma* pi.one_comp

Modified src/data/pi.lean
- \+ *lemma* pi.comp_one
- \+ *lemma* pi.const_div
- \+ *lemma* pi.const_inv
- \+ *lemma* pi.const_mul
- \+ *lemma* pi.const_one
- \+ *lemma* pi.div_comp
- \+ *lemma* pi.inv_comp
- \+ *lemma* pi.mul_comp
- \+ *lemma* pi.one_comp



## [2021-11-15 19:12:01](https://github.com/leanprover-community/mathlib/commit/43ef578)
feat(category_theory/limits): Random results about limits. ([#10285](https://github.com/leanprover-community/mathlib/pull/10285))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *abbreviation* category_theory.limits.pullback.map
- \+ *abbreviation* category_theory.limits.pushout.map

Modified src/category_theory/limits/shapes/types.lean
- \+ *def* category_theory.limits.types.coequalizer_colimit
- \+ *inductive* category_theory.limits.types.coequalizer_rel



## [2021-11-15 19:11:58](https://github.com/leanprover-community/mathlib/commit/1a47cfc)
feat(data/finset/basic): A finset has card two iff it's `{x, y}` for some `x ≠ y` ([#10252](https://github.com/leanprover-community/mathlib/pull/10252))
and the similar result for card three. Dumb but surprisingly annoying!
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.card_eq_three
- \+ *lemma* finset.card_eq_two

Modified src/data/list/basic.lean
- \+ *lemma* list.length_eq_three
- \+ *lemma* list.length_eq_two

Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.card_eq_three
- \+ *lemma* multiset.card_eq_two



## [2021-11-15 19:11:56](https://github.com/leanprover-community/mathlib/commit/9fe0cbc)
feat(category_theory/preadditive/additive_functor): map_zero' is a redundant field, remove it ([#10229](https://github.com/leanprover-community/mathlib/pull/10229))
The map_zero' field in the definition of an additive functor can be deduced from the map_add' field. So we remove it.
#### Estimated changes
Modified src/algebra/category/Module/adjunctions.lean


Modified src/algebra/homology/additive.lean


Modified src/analysis/normed/group/SemiNormedGroup/completion.lean


Modified src/category_theory/preadditive/additive_functor.lean




## [2021-11-15 17:27:15](https://github.com/leanprover-community/mathlib/commit/64418d7)
fix(logic/basic): remove `noncomputable lemma` ([#10292](https://github.com/leanprover-community/mathlib/pull/10292))
It's been three years since this was discussed according to the zulip archive link in the library note.
According to CI, the reason is no longer relevant. Leaving these as `noncomputable lemma` is harmful as it results in non-defeq instance diamonds sometimes as lean was not able to unfold the lemmas to get to the data underneath.
Since these are now `def`s, the linter requires them to have docstrings.
#### Estimated changes
Modified src/logic/basic.lean


Modified src/tactic/lint/misc.lean




## [2021-11-15 17:27:13](https://github.com/leanprover-community/mathlib/commit/d5d6071)
chore(analysis/special_functions/trigonometric/arctan): put lemmas about derivatives into a new file ([#10157](https://github.com/leanprover-community/mathlib/pull/10157))
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean


Modified src/analysis/special_functions/trigonometric/arctan.lean
- \- *lemma* deriv_arctan
- \- *lemma* deriv_within_arctan
- \- *lemma* differentiable.arctan
- \- *lemma* differentiable_at.arctan
- \- *lemma* differentiable_on.arctan
- \- *lemma* differentiable_within_at.arctan
- \- *lemma* fderiv_arctan
- \- *lemma* fderiv_within_arctan
- \- *lemma* has_deriv_at.arctan
- \- *lemma* has_deriv_within_at.arctan
- \- *lemma* has_fderiv_at.arctan
- \- *lemma* has_fderiv_within_at.arctan
- \- *lemma* has_strict_deriv_at.arctan
- \- *lemma* has_strict_fderiv_at.arctan
- \- *lemma* real.continuous_at_tan
- \- *lemma* real.deriv_arctan
- \- *lemma* real.deriv_tan
- \- *lemma* real.differentiable_arctan
- \- *lemma* real.differentiable_at_arctan
- \- *lemma* real.differentiable_at_tan
- \- *lemma* real.differentiable_at_tan_of_mem_Ioo
- \- *lemma* real.has_deriv_at_arctan
- \- *lemma* real.has_deriv_at_tan
- \- *lemma* real.has_deriv_at_tan_of_mem_Ioo
- \- *lemma* real.has_strict_deriv_at_arctan
- \- *lemma* real.has_strict_deriv_at_tan
- \- *lemma* real.tendsto_abs_tan_at_top
- \- *lemma* real.tendsto_abs_tan_of_cos_eq_zero
- \- *lemma* real.times_cont_diff_arctan
- \- *lemma* real.times_cont_diff_at_tan
- \- *lemma* times_cont_diff.arctan
- \- *lemma* times_cont_diff_at.arctan
- \- *lemma* times_cont_diff_on.arctan
- \- *lemma* times_cont_diff_within_at.arctan

Added src/analysis/special_functions/trigonometric/arctan_deriv.lean
- \+ *lemma* deriv_arctan
- \+ *lemma* deriv_within_arctan
- \+ *lemma* differentiable.arctan
- \+ *lemma* differentiable_at.arctan
- \+ *lemma* differentiable_on.arctan
- \+ *lemma* differentiable_within_at.arctan
- \+ *lemma* fderiv_arctan
- \+ *lemma* fderiv_within_arctan
- \+ *lemma* has_deriv_at.arctan
- \+ *lemma* has_deriv_within_at.arctan
- \+ *lemma* has_fderiv_at.arctan
- \+ *lemma* has_fderiv_within_at.arctan
- \+ *lemma* has_strict_deriv_at.arctan
- \+ *lemma* has_strict_fderiv_at.arctan
- \+ *lemma* real.continuous_at_tan
- \+ *lemma* real.deriv_arctan
- \+ *lemma* real.deriv_tan
- \+ *lemma* real.differentiable_arctan
- \+ *lemma* real.differentiable_at_arctan
- \+ *lemma* real.differentiable_at_tan
- \+ *lemma* real.differentiable_at_tan_of_mem_Ioo
- \+ *lemma* real.has_deriv_at_arctan
- \+ *lemma* real.has_deriv_at_tan
- \+ *lemma* real.has_deriv_at_tan_of_mem_Ioo
- \+ *lemma* real.has_strict_deriv_at_arctan
- \+ *lemma* real.has_strict_deriv_at_tan
- \+ *lemma* real.tendsto_abs_tan_at_top
- \+ *lemma* real.tendsto_abs_tan_of_cos_eq_zero
- \+ *lemma* real.times_cont_diff_arctan
- \+ *lemma* real.times_cont_diff_at_tan
- \+ *lemma* times_cont_diff.arctan
- \+ *lemma* times_cont_diff_at.arctan
- \+ *lemma* times_cont_diff_on.arctan
- \+ *lemma* times_cont_diff_within_at.arctan

Modified src/data/real/pi/leibniz.lean




## [2021-11-15 16:52:02](https://github.com/leanprover-community/mathlib/commit/02100d8)
feat(category_theory/sites/limits): `Sheaf J D` has colimits. ([#10334](https://github.com/leanprover-community/mathlib/pull/10334))
We show that the category of sheaves has colimits obtained by sheafifying colimits on the level of presheaves.
#### Estimated changes
Modified src/category_theory/sites/limits.lean
- \+ *def* category_theory.Sheaf.is_colimit_sheafify_cocone
- \+ *def* category_theory.Sheaf.sheafify_cocone



## [2021-11-15 14:41:25](https://github.com/leanprover-community/mathlib/commit/bf06854)
feat(algebra/big_operators/basic): Sum over a product of finsets, right version ([#10124](https://github.com/leanprover-community/mathlib/pull/10124))
This adds `finset.sum_prod_right` and renames `finset.sum_prod` to `finset.sum_prod_left`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_product_right'
- \+ *lemma* finset.prod_product_right

Modified src/linear_algebra/matrix/determinant.lean


Modified src/ring_theory/algebra_tower.lean




## [2021-11-15 12:56:47](https://github.com/leanprover-community/mathlib/commit/ca5c4b3)
feat(group_theory/group_action): add a few instances ([#10310](https://github.com/leanprover-community/mathlib/pull/10310))
* regular and opposite regular actions of a group on itself are transitive;
* the action of a group on an orbit is transitive.
#### Estimated changes
Modified src/algebra/opposites.lean


Modified src/group_theory/group_action/basic.lean
- \- *lemma* mul_action.exists_smul_eq
- \+/\- *lemma* mul_action.orbit_eq_univ
- \- *lemma* mul_action.surjective_smul

Modified src/group_theory/group_action/defs.lean
- \+ *lemma* mul_action.exists_smul_eq
- \+ *lemma* mul_action.surjective_smul



## [2021-11-15 10:57:56](https://github.com/leanprover-community/mathlib/commit/ca61dbf)
feat(order/sup_indep): Finite supremum independence ([#9867](https://github.com/leanprover-community/mathlib/pull/9867))
This defines supremum independence of indexed finsets.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.disjoint_sup_left
- \+ *lemma* finset.disjoint_sup_right

Added src/order/sup_indep.lean
- \+ *lemma* complete_lattice.independent_iff_sup_indep
- \+ *lemma* finset.sup_indep.attach
- \+ *lemma* finset.sup_indep.bUnion
- \+ *lemma* finset.sup_indep.pairwise_disjoint
- \+ *lemma* finset.sup_indep.subset
- \+ *lemma* finset.sup_indep.sup
- \+ *def* finset.sup_indep
- \+ *lemma* finset.sup_indep_empty
- \+ *lemma* finset.sup_indep_iff_pairwise_disjoint
- \+ *lemma* finset.sup_indep_singleton



## [2021-11-15 08:05:28](https://github.com/leanprover-community/mathlib/commit/60bc370)
feat(category_theory/sites/limits): `Sheaf_to_presheaf` creates limits ([#10328](https://github.com/leanprover-community/mathlib/pull/10328))
As a consequence, we obtain that sheaves have limits (of a given shape) when the target category does, and that these limit sheaves are computed on each object of the site "pointwise".
#### Estimated changes
Modified src/category_theory/limits/shapes/multiequalizer.lean
- \+ *def* category_theory.limits.multicofork.is_colimit.mk
- \+ *def* category_theory.limits.multifork.is_limit.mk

Added src/category_theory/sites/limits.lean
- \+ *def* category_theory.Sheaf.is_limit_multifork_of_is_limit
- \+ *lemma* category_theory.Sheaf.is_sheaf_of_is_limit
- \+ *def* category_theory.Sheaf.multifork_evaluation_cone



## [2021-11-15 05:07:52](https://github.com/leanprover-community/mathlib/commit/189e066)
feat(category_theory/sites/sheafification): The sheafification of a presheaf. ([#10303](https://github.com/leanprover-community/mathlib/pull/10303))
We construct the sheafification of a presheaf `P` taking values in a concrete category `D` with enough (co)limits, where the forgetful functor preserves the appropriate (co)limits and reflects isomorphisms.
We follow the construction on the stacks project https://stacks.math.columbia.edu/tag/00W1
**Note:** There are two very long proofs here, so I added several comments explaining what's going on.
#### Estimated changes
Modified src/category_theory/limits/concrete_category.lean
- \+ *def* category_theory.limits.concrete.multiequalizer_equiv
- \+ *lemma* category_theory.limits.concrete.multiequalizer_equiv_apply
- \+ *def* category_theory.limits.concrete.multiequalizer_equiv_aux

Modified src/category_theory/sites/grothendieck.lean
- \+ *def* category_theory.grothendieck_topology.cover.arrow.from_middle
- \+ *lemma* category_theory.grothendieck_topology.cover.arrow.from_middle_condition
- \+ *lemma* category_theory.grothendieck_topology.cover.arrow.middle_spec
- \+ *def* category_theory.grothendieck_topology.cover.arrow.to_middle
- \+ *lemma* category_theory.grothendieck_topology.cover.arrow.to_middle_condition
- \+ *def* category_theory.grothendieck_topology.cover.bind
- \+ *def* category_theory.grothendieck_topology.cover.bind_to_base

Modified src/category_theory/sites/plus.lean
- \+ *def* category_theory.grothendieck_topology.iso_to_plus
- \+ *lemma* category_theory.grothendieck_topology.plus_hom_ext
- \+ *def* category_theory.grothendieck_topology.plus_lift
- \+ *lemma* category_theory.grothendieck_topology.plus_lift_unique
- \+ *lemma* category_theory.grothendieck_topology.to_plus_plus_lift

Added src/category_theory/sites/sheafification.lean
- \+ *lemma* category_theory.grothendieck_topology.is_iso_to_sheafify
- \+ *def* category_theory.grothendieck_topology.iso_sheafify
- \+ *lemma* category_theory.grothendieck_topology.plus.eq_mk_iff_exists
- \+ *theorem* category_theory.grothendieck_topology.plus.exists_of_sep
- \+ *lemma* category_theory.grothendieck_topology.plus.exists_rep
- \+ *lemma* category_theory.grothendieck_topology.plus.inj_of_sep
- \+ *theorem* category_theory.grothendieck_topology.plus.is_sheaf_of_sep
- \+ *theorem* category_theory.grothendieck_topology.plus.is_sheaf_plus_plus
- \+ *def* category_theory.grothendieck_topology.plus.meq_of_sep
- \+ *def* category_theory.grothendieck_topology.plus.mk
- \+ *lemma* category_theory.grothendieck_topology.plus.res_mk_eq_mk_pullback
- \+ *theorem* category_theory.grothendieck_topology.plus.sep
- \+ *lemma* category_theory.grothendieck_topology.plus.to_plus_apply
- \+ *lemma* category_theory.grothendieck_topology.plus.to_plus_eq_mk
- \+ *lemma* category_theory.grothendieck_topology.plus.to_plus_mk
- \+ *def* category_theory.grothendieck_topology.sheafification
- \+ *lemma* category_theory.grothendieck_topology.sheafification_obj
- \+ *def* category_theory.grothendieck_topology.sheafify
- \+ *lemma* category_theory.grothendieck_topology.sheafify_hom_ext
- \+ *def* category_theory.grothendieck_topology.sheafify_lift
- \+ *lemma* category_theory.grothendieck_topology.sheafify_lift_unique
- \+ *def* category_theory.grothendieck_topology.to_sheafification
- \+ *lemma* category_theory.grothendieck_topology.to_sheafification_app
- \+ *def* category_theory.grothendieck_topology.to_sheafify
- \+ *lemma* category_theory.grothendieck_topology.to_sheafify_sheafify_lift
- \+ *lemma* category_theory.meq.condition
- \+ *def* category_theory.meq.equiv
- \+ *lemma* category_theory.meq.equiv_apply
- \+ *lemma* category_theory.meq.equiv_symm_eq_apply
- \+ *lemma* category_theory.meq.ext
- \+ *def* category_theory.meq.mk
- \+ *lemma* category_theory.meq.mk_apply
- \+ *def* category_theory.meq.pullback
- \+ *lemma* category_theory.meq.pullback_apply
- \+ *lemma* category_theory.meq.pullback_refine
- \+ *def* category_theory.meq.refine
- \+ *lemma* category_theory.meq.refine_apply
- \+ *def* category_theory.meq
- \+ *def* category_theory.presheaf_to_Sheaf
- \+ *def* category_theory.sheafification_adjunction
- \+ *def* category_theory.sheafification_iso
- \+ *lemma* category_theory.sheafification_iso_hom
- \+ *lemma* category_theory.sheafification_iso_inv



## [2021-11-15 04:19:49](https://github.com/leanprover-community/mathlib/commit/62992fa)
feat(analysis/inner_product_space/spectrum): more concrete diagonalization theorem ([#10317](https://github.com/leanprover-community/mathlib/pull/10317))
This is a second version of the diagonalization theorem for self-adjoint operators on finite-dimensional inner product spaces, stating that a self-adjoint operator admits an orthonormal basis of eigenvectors, and deducing the standard consequences (when expressed with respect to this basis the operator acts diagonally).
I have also updated `undergrad.yaml` and `overview.yaml` to cover the diagonalization theorem and other things proved in the library about Hilbert spaces.
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* basis.coe_isometry_euclidean_of_orthonormal
- \+ *lemma* basis.coe_isometry_euclidean_of_orthonormal_symm

Modified src/analysis/inner_product_space/spectrum.lean
- \+ *lemma* is_self_adjoint.apply_eigenvector_basis
- \+ *lemma* is_self_adjoint.diagonalization_basis_apply_self_apply
- \+ *lemma* is_self_adjoint.diagonalization_basis_symm_apply
- \+ *lemma* is_self_adjoint.eigenvector_basis_orthonormal
- \+ *lemma* is_self_adjoint.has_eigenvector_eigenvector_basis



## [2021-11-14 20:27:17](https://github.com/leanprover-community/mathlib/commit/0c8f53e)
feat(linear_algebra/trace): add lemmas about trace of linear maps ([#10279](https://github.com/leanprover-community/mathlib/pull/10279))
Lemmas for the trace of the identity and the trace of a conjugation
#### Estimated changes
Modified src/linear_algebra/trace.lean
- \+ *theorem* linear_map.trace_conj'
- \+ *theorem* linear_map.trace_conj
- \+ *theorem* linear_map.trace_one



## [2021-11-14 18:03:48](https://github.com/leanprover-community/mathlib/commit/1b51fe0)
feat(linear_algebra/alternating): add alternating_map.comp_linear_map ([#10314](https://github.com/leanprover-community/mathlib/pull/10314))
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* alternating_map.add_comp_linear_map
- \+ *lemma* alternating_map.coe_comp_linear_map
- \+ *def* alternating_map.comp_linear_map
- \+ *lemma* alternating_map.comp_linear_map_apply
- \+ *lemma* alternating_map.comp_linear_map_zero
- \+ *lemma* alternating_map.zero_comp_linear_map



## [2021-11-14 17:03:13](https://github.com/leanprover-community/mathlib/commit/8728e85)
feat(measure_theory): drop some unneeded assumptions ([#10319](https://github.com/leanprover-community/mathlib/pull/10319))
Prove that for a nontrivial countably generated filter there exists a sequence that converges to this filter. Use this lemma to drop some assumptions.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+/\- *lemma* measurable_of_tendsto_metric'
- \+/\- *lemma* measurable_of_tendsto_nnreal'

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.exists_seq_tendsto



## [2021-11-14 15:22:16](https://github.com/leanprover-community/mathlib/commit/5307dc1)
feat(data/equiv/module): add module.to_module_End ([#10300](https://github.com/leanprover-community/mathlib/pull/10300))
The new definitions are:
* `distrib_mul_action.to_module_End`
* `distrib_mul_action.to_module_aut`
* `module.to_module_End`
Everything else is a move.
This also moves the group structure on linear_equiv earlier in the import heirarchy.
This is more consistent with where it is for `linear_map`.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *def* distrib_mul_action.to_linear_map
- \+ *def* distrib_mul_action.to_module_End
- \+ *def* module.to_module_End

Modified src/data/equiv/module.lean
- \- *def* distrib_mul_action.to_linear_map
- \+ *def* distrib_mul_action.to_module_aut
- \+ *def* linear_equiv.automorphism_group.to_linear_map_monoid_hom

Modified src/linear_algebra/basic.lean
- \- *def* linear_equiv.automorphism_group.to_linear_map_monoid_hom



## [2021-11-14 15:22:15](https://github.com/leanprover-community/mathlib/commit/299af47)
chore(data/fin/basic): move tuple stuff to a new file ([#10295](https://github.com/leanprover-community/mathlib/pull/10295))
There are almost 600 lines of tuple stuff, which is definitely sufficient to justify a standalone file.
The author information has been guessed from the git history.
Floris is responsible for `cons` and `tail` which came first in [#1294](https://github.com/leanprover-community/mathlib/pull/1294), Chris added find, and Yury and Sébastien were involved all over the place.
This is simply a cut-and-paste job, with the exception of the new module docstring which has been merged with the docstring for the tuple subheading.
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified src/data/fin/basic.lean
- \- *def* fin.append
- \- *lemma* fin.comp_cons
- \- *lemma* fin.comp_init
- \- *lemma* fin.comp_snoc
- \- *lemma* fin.comp_tail
- \- *def* fin.cons
- \- *lemma* fin.cons_le
- \- *lemma* fin.cons_self_tail
- \- *lemma* fin.cons_snoc_eq_snoc_cons
- \- *lemma* fin.cons_succ
- \- *lemma* fin.cons_update
- \- *lemma* fin.cons_zero
- \- *lemma* fin.eq_insert_nth_iff
- \- *lemma* fin.fin_append_apply_zero
- \- *def* fin.find
- \- *lemma* fin.find_eq_none_iff
- \- *lemma* fin.find_eq_some_iff
- \- *lemma* fin.find_min'
- \- *lemma* fin.find_min
- \- *lemma* fin.find_spec
- \- *lemma* fin.forall_iff_succ_above
- \- *def* fin.init
- \- *lemma* fin.init_def
- \- *lemma* fin.init_snoc
- \- *lemma* fin.init_update_cast_succ
- \- *lemma* fin.init_update_last
- \- *def* fin.insert_nth
- \- *lemma* fin.insert_nth_add
- \- *lemma* fin.insert_nth_apply_above
- \- *lemma* fin.insert_nth_apply_below
- \- *lemma* fin.insert_nth_apply_same
- \- *lemma* fin.insert_nth_apply_succ_above
- \- *lemma* fin.insert_nth_binop
- \- *lemma* fin.insert_nth_comp_succ_above
- \- *lemma* fin.insert_nth_div
- \- *lemma* fin.insert_nth_eq_iff
- \- *lemma* fin.insert_nth_last'
- \- *lemma* fin.insert_nth_last
- \- *lemma* fin.insert_nth_le_iff
- \- *lemma* fin.insert_nth_mem_Icc
- \- *lemma* fin.insert_nth_mul
- \- *lemma* fin.insert_nth_sub
- \- *lemma* fin.insert_nth_sub_same
- \- *lemma* fin.insert_nth_zero'
- \- *lemma* fin.insert_nth_zero
- \- *lemma* fin.insert_nth_zero_right
- \- *lemma* fin.is_some_find_iff
- \- *lemma* fin.le_cons
- \- *lemma* fin.le_insert_nth_iff
- \- *lemma* fin.mem_find_iff
- \- *lemma* fin.mem_find_of_unique
- \- *lemma* fin.nat_find_mem_find
- \- *lemma* fin.preimage_insert_nth_Icc_of_mem
- \- *lemma* fin.preimage_insert_nth_Icc_of_not_mem
- \- *lemma* fin.range_cons
- \- *def* fin.snoc
- \- *lemma* fin.snoc_cast_succ
- \- *lemma* fin.snoc_init_self
- \- *lemma* fin.snoc_last
- \- *lemma* fin.snoc_update
- \- *def* fin.succ_above_cases
- \- *lemma* fin.succ_above_cases_eq_insert_nth
- \- *def* fin.tail
- \- *lemma* fin.tail_cons
- \- *lemma* fin.tail_def
- \- *lemma* fin.tail_init_eq_init_tail
- \- *lemma* fin.tail_update_succ
- \- *lemma* fin.tail_update_zero
- \- *lemma* fin.tuple0_le
- \- *lemma* fin.update_cons_zero
- \- *lemma* fin.update_snoc_last

Added src/data/fin/tuple.lean
- \+ *def* fin.append
- \+ *lemma* fin.comp_cons
- \+ *lemma* fin.comp_init
- \+ *lemma* fin.comp_snoc
- \+ *lemma* fin.comp_tail
- \+ *def* fin.cons
- \+ *lemma* fin.cons_le
- \+ *lemma* fin.cons_self_tail
- \+ *lemma* fin.cons_snoc_eq_snoc_cons
- \+ *lemma* fin.cons_succ
- \+ *lemma* fin.cons_update
- \+ *lemma* fin.cons_zero
- \+ *lemma* fin.eq_insert_nth_iff
- \+ *lemma* fin.fin_append_apply_zero
- \+ *def* fin.find
- \+ *lemma* fin.find_eq_none_iff
- \+ *lemma* fin.find_eq_some_iff
- \+ *lemma* fin.find_min'
- \+ *lemma* fin.find_min
- \+ *lemma* fin.find_spec
- \+ *lemma* fin.forall_iff_succ_above
- \+ *def* fin.init
- \+ *lemma* fin.init_def
- \+ *lemma* fin.init_snoc
- \+ *lemma* fin.init_update_cast_succ
- \+ *lemma* fin.init_update_last
- \+ *def* fin.insert_nth
- \+ *lemma* fin.insert_nth_add
- \+ *lemma* fin.insert_nth_apply_above
- \+ *lemma* fin.insert_nth_apply_below
- \+ *lemma* fin.insert_nth_apply_same
- \+ *lemma* fin.insert_nth_apply_succ_above
- \+ *lemma* fin.insert_nth_binop
- \+ *lemma* fin.insert_nth_comp_succ_above
- \+ *lemma* fin.insert_nth_div
- \+ *lemma* fin.insert_nth_eq_iff
- \+ *lemma* fin.insert_nth_last'
- \+ *lemma* fin.insert_nth_last
- \+ *lemma* fin.insert_nth_le_iff
- \+ *lemma* fin.insert_nth_mem_Icc
- \+ *lemma* fin.insert_nth_mul
- \+ *lemma* fin.insert_nth_sub
- \+ *lemma* fin.insert_nth_sub_same
- \+ *lemma* fin.insert_nth_zero'
- \+ *lemma* fin.insert_nth_zero
- \+ *lemma* fin.insert_nth_zero_right
- \+ *lemma* fin.is_some_find_iff
- \+ *lemma* fin.le_cons
- \+ *lemma* fin.le_insert_nth_iff
- \+ *lemma* fin.mem_find_iff
- \+ *lemma* fin.mem_find_of_unique
- \+ *lemma* fin.nat_find_mem_find
- \+ *lemma* fin.preimage_insert_nth_Icc_of_mem
- \+ *lemma* fin.preimage_insert_nth_Icc_of_not_mem
- \+ *lemma* fin.range_cons
- \+ *def* fin.snoc
- \+ *lemma* fin.snoc_cast_succ
- \+ *lemma* fin.snoc_init_self
- \+ *lemma* fin.snoc_last
- \+ *lemma* fin.snoc_update
- \+ *def* fin.succ_above_cases
- \+ *lemma* fin.succ_above_cases_eq_insert_nth
- \+ *def* fin.tail
- \+ *lemma* fin.tail_cons
- \+ *lemma* fin.tail_def
- \+ *lemma* fin.tail_init_eq_init_tail
- \+ *lemma* fin.tail_update_succ
- \+ *lemma* fin.tail_update_zero
- \+ *lemma* fin.tuple0_le
- \+ *lemma* fin.update_cons_zero
- \+ *lemma* fin.update_snoc_last

Modified src/data/fin/vec_notation.lean


Modified src/linear_algebra/multilinear/basic.lean


Modified src/topology/constructions.lean




## [2021-11-14 15:22:14](https://github.com/leanprover-community/mathlib/commit/7dc33bf)
feat(data/nat/basic): Some `nat.find` lemmas ([#10263](https://github.com/leanprover-community/mathlib/pull/10263))
This proves `nat.find_le` and `nat.find_add` and renames the current `nat.find_le` to `nat.find_mono`.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.find_add
- \+ *lemma* nat.find_le
- \- *theorem* nat.find_le
- \+ *theorem* nat.find_mono

Modified src/ring_theory/multiplicity.lean




## [2021-11-14 13:46:33](https://github.com/leanprover-community/mathlib/commit/dd72ebc)
feat(data/list/big_operators): When `list.sum` is strictly positive ([#10282](https://github.com/leanprover-community/mathlib/pull/10282))
#### Estimated changes
Modified src/data/list/big_operators.lean
- \+ *lemma* list.one_lt_prod_of_one_lt



## [2021-11-14 09:32:09](https://github.com/leanprover-community/mathlib/commit/bca8278)
feat(algebra/lie/basic): add missing `@[ext]` and `@[simp]` lemmas ([#10316](https://github.com/leanprover-community/mathlib/pull/10316))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \- *lemma* lie_equiv.bijective
- \+ *lemma* lie_equiv.coe_injective
- \+ *lemma* lie_equiv.coe_linear_equiv_injective
- \- *lemma* lie_equiv.coe_to_lie_equiv
- \+ *lemma* lie_equiv.coe_to_lie_hom
- \+ *lemma* lie_equiv.ext
- \- *lemma* lie_equiv.injective
- \+ *lemma* lie_equiv.self_trans_symm
- \- *lemma* lie_equiv.surjective
- \+ *lemma* lie_equiv.symm_trans
- \- *lemma* lie_equiv.symm_trans_apply
- \+ *lemma* lie_equiv.symm_trans_self
- \+ *lemma* lie_equiv.to_linear_equiv_mk
- \+ *lemma* lie_module_equiv.self_trans_symm
- \+ *lemma* lie_module_equiv.symm_trans
- \- *lemma* lie_module_equiv.symm_trans_apply
- \+ *lemma* lie_module_equiv.symm_trans_self

Modified src/data/equiv/module.lean
- \+ *lemma* linear_equiv.coe_injective



## [2021-11-13 21:34:57](https://github.com/leanprover-community/mathlib/commit/3b5edd0)
refactor(set_theory/cardinal_ordinal): use TC assumptions instead of inequalities ([#10313](https://github.com/leanprover-community/mathlib/pull/10313))
Assume `[fintype α]` or `[infinite α]` instead of `#α < ω` or `ω ≤ #α`.
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \+/\- *theorem* cardinal.extend_function_finite
- \+ *lemma* cardinal.mk_bounded_set_le_of_infinite
- \- *lemma* cardinal.mk_bounded_set_le_of_omega_le
- \+/\- *lemma* cardinal.mk_compl_eq_mk_compl_finite
- \+/\- *lemma* cardinal.mk_compl_eq_mk_compl_finite_lift
- \+/\- *lemma* cardinal.mk_compl_eq_mk_compl_finite_same
- \+/\- *lemma* cardinal.mk_compl_eq_mk_compl_infinite
- \+ *lemma* cardinal.mk_compl_finset_of_infinite
- \- *lemma* cardinal.mk_compl_finset_of_omega_le
- \+ *lemma* cardinal.mk_compl_of_infinite
- \- *lemma* cardinal.mk_compl_of_omega_le
- \+/\- *lemma* cardinal.powerlt_omega



## [2021-11-13 19:05:20](https://github.com/leanprover-community/mathlib/commit/d8c8725)
feat(ring_theory,algebraic_geometry): Miscellaneous lemmas/def/typo corrections ([#10307](https://github.com/leanprover-community/mathlib/pull/10307))
Split out from [#9802](https://github.com/leanprover-community/mathlib/pull/9802) since I'm aiming at more general version.
#### Estimated changes
Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *def* local_ring.closed_point
- \+ *lemma* local_ring.local_hom_iff_comap_closed_point
- \+ *lemma* prime_spectrum.is_basis_basic_opens

Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/category_theory/sites/sheaf_of_types.lean


Modified src/category_theory/structured_arrow.lean


Modified src/ring_theory/ideal/local_ring.lean
- \+ *theorem* local_ring.local_hom_tfae

Modified src/ring_theory/localization.lean
- \+ *lemma* is_localization.iso_comp

Modified src/topology/sheaves/sheaf_condition/sites.lean
- \+ *lemma* Top.opens.cover_dense_iff_is_basis
- \+ *lemma* Top.opens.cover_dense_induced_functor
- \+ *lemma* Top.sheaf.extend_hom_app
- \+ *lemma* Top.sheaf.hom_ext
- \+ *def* Top.sheaf.restrict_hom_equiv_hom



## [2021-11-13 17:25:11](https://github.com/leanprover-community/mathlib/commit/ca56c5a)
feat(measure_theory/group): define a few `measurable_equiv`s ([#10299](https://github.com/leanprover-community/mathlib/pull/10299))
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *lemma* equiv.inv_symm₀

Added src/measure_theory/group/measurable_equiv.lean
- \+ *lemma* measurable_embedding_const_smul
- \+ *lemma* measurable_embedding_const_smul₀
- \+ *lemma* measurable_embedding_mul_left
- \+ *lemma* measurable_embedding_mul_left₀
- \+ *lemma* measurable_embedding_mul_right
- \+ *lemma* measurable_embedding_mul_right₀
- \+ *lemma* measurable_equiv.coe_mul_left
- \+ *lemma* measurable_equiv.coe_mul_left₀
- \+ *lemma* measurable_equiv.coe_mul_right
- \+ *lemma* measurable_equiv.coe_mul_right₀
- \+ *lemma* measurable_equiv.coe_smul₀
- \+ *def* measurable_equiv.inv
- \+ *def* measurable_equiv.inv₀
- \+ *def* measurable_equiv.mul_left
- \+ *def* measurable_equiv.mul_left₀
- \+ *def* measurable_equiv.mul_right
- \+ *def* measurable_equiv.mul_right₀
- \+ *def* measurable_equiv.smul
- \+ *def* measurable_equiv.smul₀
- \+ *lemma* measurable_equiv.symm_inv
- \+ *lemma* measurable_equiv.symm_inv₀
- \+ *lemma* measurable_equiv.symm_mul_left
- \+ *lemma* measurable_equiv.symm_mul_left₀
- \+ *lemma* measurable_equiv.symm_mul_right
- \+ *lemma* measurable_equiv.symm_mul_right₀
- \+ *lemma* measurable_equiv.symm_smul
- \+ *lemma* measurable_equiv.symm_smul₀
- \+ *lemma* measurable_equiv.to_equiv_mul_left
- \+ *lemma* measurable_equiv.to_equiv_mul_left₀
- \+ *lemma* measurable_equiv.to_equiv_mul_right
- \+ *lemma* measurable_equiv.to_equiv_mul_right₀



## [2021-11-13 16:06:16](https://github.com/leanprover-community/mathlib/commit/3578403)
feat(*/{group,mul}_action): more lemmas ([#10308](https://github.com/leanprover-community/mathlib/pull/10308))
* add several lemmas about orbits and pointwise scalar multiplication;
* generalize `mul_action.orbit.mul_action` to a monoid action;
* more lemmas about pretransitive actions, use `to_additive` more;
* add dot notation lemmas `is_open.smul` and `is_closed.smul`.
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \- *lemma* add_action.exists_vadd_eq
- \+ *lemma* mul_action.maps_to_smul_orbit
- \+/\- *lemma* mul_action.mem_orbit_smul
- \+ *lemma* mul_action.orbit_eq_univ
- \+ *lemma* mul_action.orbit_smul
- \+ *lemma* mul_action.orbit_smul_subset
- \+/\- *lemma* mul_action.smul_mem_orbit_smul
- \+ *lemma* mul_action.smul_orbit
- \+ *lemma* mul_action.smul_orbit_subset
- \+ *lemma* mul_action.surjective_smul

Modified src/topology/algebra/mul_action.lean
- \+ *lemma* is_closed.smul
- \+ *lemma* is_open.smul
- \+ *lemma* smul_closure_orbit_subset
- \+ *lemma* smul_closure_subset



## [2021-11-13 14:24:59](https://github.com/leanprover-community/mathlib/commit/b91d344)
chore(data/equiv/*): rename `trans_symm` and `symm_trans` to `self_trans_symm` and `symm_trans_self`. ([#10309](https://github.com/leanprover-community/mathlib/pull/10309))
This frees up `symm_trans` to state `(a.trans b).symm = a.symm.trans b.symm`.
These names are consistent with `self_comp_symm` and `symm_comp_self`.
#### Estimated changes
Modified src/analysis/normed_space/affine_isometry.lean
- \+ *lemma* affine_isometry_equiv.self_trans_symm
- \- *lemma* affine_isometry_equiv.symm_trans
- \+ *lemma* affine_isometry_equiv.symm_trans_self
- \- *lemma* affine_isometry_equiv.trans_symm

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.self_trans_symm
- \- *lemma* linear_isometry_equiv.symm_trans
- \+ *lemma* linear_isometry_equiv.symm_trans_self
- \- *lemma* linear_isometry_equiv.trans_symm

Modified src/data/equiv/basic.lean
- \+ *theorem* equiv.self_trans_symm
- \- *theorem* equiv.symm_trans
- \+ *theorem* equiv.symm_trans_self
- \- *theorem* equiv.trans_symm

Modified src/data/equiv/module.lean
- \+ *lemma* linear_equiv.self_trans_symm
- \- *lemma* linear_equiv.symm_trans
- \+ *lemma* linear_equiv.symm_trans_self
- \- *lemma* linear_equiv.trans_symm

Modified src/data/equiv/ring.lean
- \+ *theorem* ring_equiv.self_trans_symm
- \- *theorem* ring_equiv.symm_trans
- \+ *theorem* ring_equiv.symm_trans_self
- \- *theorem* ring_equiv.trans_symm

Modified src/data/finsupp/basic.lean


Modified src/data/pequiv.lean
- \+ *lemma* pequiv.self_trans_symm
- \- *lemma* pequiv.symm_trans
- \+ *lemma* pequiv.symm_trans_self
- \- *lemma* pequiv.trans_symm

Modified src/field_theory/splitting_field.lean


Modified src/geometry/manifold/diffeomorph.lean
- \+ *lemma* diffeomorph.self_trans_symm
- \- *lemma* diffeomorph.symm_trans
- \+ *lemma* diffeomorph.symm_trans_self
- \- *lemma* diffeomorph.trans_symm

Modified src/group_theory/perm/basic.lean
- \- *lemma* equiv.perm.inv_trans
- \+ *lemma* equiv.perm.inv_trans_self
- \+/\- *lemma* equiv.perm.mul_symm
- \+ *lemma* equiv.perm.self_trans_inv
- \+/\- *lemma* equiv.perm.symm_mul
- \- *lemma* equiv.perm.trans_inv

Modified src/group_theory/perm/sign.lean


Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+ *lemma* affine_equiv.self_trans_symm
- \- *lemma* affine_equiv.symm_trans
- \+ *lemma* affine_equiv.symm_trans_self
- \- *lemma* affine_equiv.trans_symm

Modified src/linear_algebra/determinant.lean




## [2021-11-13 10:27:54](https://github.com/leanprover-community/mathlib/commit/869cb32)
chore(measure_theory/probability_mass_function): Refactor the `pmf` file into a definitions file and a constructions file ([#10298](https://github.com/leanprover-community/mathlib/pull/10298))
#### Estimated changes
Added src/measure_theory/probability_mass_function/basic.lean
- \+ *lemma* pmf.apply_eq_zero_iff
- \+ *def* pmf.bind
- \+ *lemma* pmf.bind_apply
- \+ *lemma* pmf.bind_bind
- \+ *lemma* pmf.bind_comm
- \+ *lemma* pmf.bind_pure
- \+ *lemma* pmf.coe_bind_apply
- \+ *lemma* pmf.coe_le_one
- \+ *lemma* pmf.has_sum_coe_one
- \+ *lemma* pmf.mem_support_iff
- \+ *lemma* pmf.mem_support_pure_iff
- \+ *def* pmf.pure
- \+ *lemma* pmf.pure_apply
- \+ *lemma* pmf.pure_bind
- \+ *lemma* pmf.summable_coe
- \+ *def* pmf.support
- \+ *def* pmf.to_measure
- \+ *lemma* pmf.to_measure_apply'
- \+ *lemma* pmf.to_measure_apply
- \+ *lemma* pmf.to_measure_apply_eq_to_outer_measure_apply
- \+ *lemma* pmf.to_measure_apply_finset
- \+ *lemma* pmf.to_measure_apply_fintype
- \+ *lemma* pmf.to_measure_apply_of_finite
- \+ *def* pmf.to_outer_measure
- \+ *lemma* pmf.to_outer_measure_apply'
- \+ *lemma* pmf.to_outer_measure_apply
- \+ *lemma* pmf.to_outer_measure_apply_eq_zero_iff
- \+ *lemma* pmf.to_outer_measure_apply_finset
- \+ *lemma* pmf.to_outer_measure_apply_fintype
- \+ *lemma* pmf.to_outer_measure_apply_le_to_measure_apply
- \+ *lemma* pmf.to_outer_measure_caratheodory
- \+ *lemma* pmf.tsum_coe
- \+ *def* {u}

Renamed src/measure_theory/probability_mass_function.lean to src/measure_theory/probability_mass_function/constructions.lean
- \- *def* pmf.bind
- \- *lemma* pmf.bind_apply
- \- *lemma* pmf.bind_bind
- \- *lemma* pmf.bind_comm
- \- *lemma* pmf.bind_pure
- \- *lemma* pmf.coe_bind_apply
- \- *lemma* pmf.coe_le_one
- \- *lemma* pmf.has_sum_coe_one
- \- *lemma* pmf.mem_support_iff
- \- *lemma* pmf.mem_support_pure_iff
- \- *def* pmf.pure
- \- *lemma* pmf.pure_apply
- \- *lemma* pmf.pure_bind
- \- *lemma* pmf.summable_coe
- \- *def* pmf.support
- \- *def* pmf.to_measure
- \- *lemma* pmf.to_measure_apply'
- \- *lemma* pmf.to_measure_apply
- \- *lemma* pmf.to_measure_apply_eq_to_outer_measure_apply
- \- *lemma* pmf.to_measure_apply_finset
- \- *lemma* pmf.to_measure_apply_fintype
- \- *lemma* pmf.to_measure_apply_of_finite
- \- *def* pmf.to_outer_measure
- \- *lemma* pmf.to_outer_measure_apply'
- \- *lemma* pmf.to_outer_measure_apply
- \- *lemma* pmf.to_outer_measure_apply_eq_zero_iff
- \- *lemma* pmf.to_outer_measure_apply_finset
- \- *lemma* pmf.to_outer_measure_apply_fintype
- \- *lemma* pmf.to_outer_measure_apply_le_to_measure_apply
- \- *lemma* pmf.to_outer_measure_caratheodory
- \- *lemma* pmf.tsum_coe
- \- *def* {u}



## [2021-11-13 09:09:36](https://github.com/leanprover-community/mathlib/commit/a7e38a0)
feat(linear_algebra/bilinear_form): add is_refl and ortho_sym for alt_bilin_form ([#10304](https://github.com/leanprover-community/mathlib/pull/10304))
Lemma `is_refl` shows that every alternating bilinear form is reflexive.
Lemma `ortho_sym` shows that being orthogonal with respect to an alternating bilinear form is symmetric.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* alt_bilin_form.is_refl
- \+ *lemma* alt_bilin_form.ortho_sym



## [2021-11-13 02:46:06](https://github.com/leanprover-community/mathlib/commit/a232366)
feat(analysis/inner_product_space/projection): orthonormal basis subordinate to an `orthogonal_family` ([#10208](https://github.com/leanprover-community/mathlib/pull/10208))
In a finite-dimensional inner product space of `E`, there exists an orthonormal basis subordinate to a given direct sum decomposition into an `orthogonal_family` of subspaces `E`.
#### Estimated changes
Modified src/algebra/direct_sum/module.lean
- \+ *lemma* direct_sum.submodule_is_internal.collected_basis_coe
- \+ *lemma* direct_sum.submodule_is_internal.collected_basis_mem

Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* direct_sum.submodule_is_internal.collected_basis_orthonormal
- \+ *lemma* orthogonal_family.orthonormal_sigma_orthonormal

Modified src/analysis/inner_product_space/projection.lean
- \+/\- *lemma* coe_orthonormal_basis
- \+ *def* direct_sum.submodule_is_internal.sigma_orthonormal_basis_index_equiv
- \+ *def* direct_sum.submodule_is_internal.subordinate_orthonormal_basis
- \+ *def* direct_sum.submodule_is_internal.subordinate_orthonormal_basis_index
- \+ *lemma* direct_sum.submodule_is_internal.subordinate_orthonormal_basis_orthonormal
- \+ *lemma* direct_sum.submodule_is_internal.subordinate_orthonormal_basis_subordinate
- \+/\- *def* fin_orthonormal_basis
- \+/\- *lemma* fin_orthonormal_basis_orthonormal
- \+/\- *def* orthonormal_basis
- \+/\- *def* orthonormal_basis_index
- \+/\- *lemma* orthonormal_basis_orthonormal

Modified src/data/finsupp/to_dfinsupp.lean
- \+ *lemma* sigma_finsupp_equiv_dfinsupp_single



## [2021-11-12 23:21:30](https://github.com/leanprover-community/mathlib/commit/8bb0b6f)
feat(category_theory/sites/plus): If P is a sheaf, then the map from P to P^+ is an isomorphism. ([#10297](https://github.com/leanprover-community/mathlib/pull/10297))
Also adds some simple results about (co)limits where the morphisms in the diagram are isomorphisms.
#### Estimated changes
Modified src/category_theory/category/preorder.lean


Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* category_theory.limits.cocone_of_diagram_initial
- \+ *def* category_theory.limits.colimit_of_diagram_initial
- \+ *def* category_theory.limits.colimit_of_initial
- \+ *def* category_theory.limits.cone_of_diagram_terminal
- \+ *def* category_theory.limits.is_initial_bot
- \+ *lemma* category_theory.limits.is_iso_ι_of_is_initial
- \+ *lemma* category_theory.limits.is_iso_π_of_is_terminal
- \+ *def* category_theory.limits.is_terminal_top
- \+ *def* category_theory.limits.limit_of_diagram_terminal
- \+ *def* category_theory.limits.limit_of_terminal

Modified src/category_theory/sites/plus.lean
- \+ *lemma* category_theory.grothendieck_topology.is_iso_to_plus_of_is_sheaf



## [2021-11-12 21:42:51](https://github.com/leanprover-community/mathlib/commit/55534c4)
feat(data/nat/basic): recursion for set nat ([#10273](https://github.com/leanprover-community/mathlib/pull/10273))
Adding a special case of `nat.le_rec_on` where the predicate is membership of a subset.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.set_eq_univ
- \+ *lemma* nat.set_induction
- \+ *lemma* nat.set_induction_bounded



## [2021-11-12 20:02:20](https://github.com/leanprover-community/mathlib/commit/6afda88)
feat(analysis/inner_product_space/spectrum): diagonalization of self-adjoint endomorphisms (finite dimension) ([#9995](https://github.com/leanprover-community/mathlib/pull/9995))
Diagonalization of a self-adjoint endomorphism `T` of a finite-dimensional inner product space `E` over either `ℝ` or `ℂ`:  construct a linear isometry `T.diagonalization` from `E` to the direct sum of `T`'s eigenspaces, such that `T` conjugated by `T.diagonalization` is diagonal:
```lean
lemma diagonalization_apply_self_apply (v : E) (μ : eigenvalues T) :
  hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ
```
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* is_self_adjoint.restrict_invariant
- \+ *lemma* orthogonal_family.comp

Modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* direct_sum.submodule_is_internal.isometry_L2_of_orthogonal_family_symm_apply

Modified src/analysis/inner_product_space/projection.lean
- \+/\- *lemma* orthogonal_family.submodule_is_internal_iff

Modified src/analysis/inner_product_space/rayleigh.lean
- \+ *lemma* is_self_adjoint.subsingleton_of_no_eigenvalue_finite_dimensional

Added src/analysis/inner_product_space/spectrum.lean
- \+ *lemma* is_self_adjoint.conj_eigenvalue_eq_self
- \+ *lemma* is_self_adjoint.diagonalization_apply_self_apply
- \+ *lemma* is_self_adjoint.diagonalization_symm_apply
- \+ *lemma* is_self_adjoint.direct_sum_submodule_is_internal
- \+ *lemma* is_self_adjoint.invariant_orthogonal_eigenspace
- \+ *lemma* is_self_adjoint.orthogonal_family_eigenspaces'
- \+ *lemma* is_self_adjoint.orthogonal_family_eigenspaces
- \+ *lemma* is_self_adjoint.orthogonal_supr_eigenspaces
- \+ *lemma* is_self_adjoint.orthogonal_supr_eigenspaces_eq_bot'
- \+ *lemma* is_self_adjoint.orthogonal_supr_eigenspaces_eq_bot
- \+ *lemma* is_self_adjoint.orthogonal_supr_eigenspaces_invariant

Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.prod_eq_prod_fintype

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.infi_invariant

Modified src/order/complete_lattice.lean
- \+ *lemma* infi_ne_top_subtype
- \+ *lemma* supr_ne_bot_subtype



## [2021-11-12 17:48:18](https://github.com/leanprover-community/mathlib/commit/f0a9849)
feat(category_theory/sites/sheaf): Add sheaf conditions in terms of multiforks/multiequalizers. ([#10294](https://github.com/leanprover-community/mathlib/pull/10294))
Another PR toward sheafification.
#### Estimated changes
Modified src/category_theory/sites/sheaf.lean
- \+ *def* category_theory.presheaf.is_limit_of_is_sheaf
- \+ *def* category_theory.presheaf.is_sheaf.amalgamate
- \+ *lemma* category_theory.presheaf.is_sheaf.amalgamate_map
- \+ *lemma* category_theory.presheaf.is_sheaf.hom_ext
- \+ *lemma* category_theory.presheaf.is_sheaf_iff_multiequalizer
- \+ *lemma* category_theory.presheaf.is_sheaf_iff_multifork



## [2021-11-12 17:08:23](https://github.com/leanprover-community/mathlib/commit/adb5c2d)
chore(analysis/special_functions/trigonometric/complex): put results about derivatives into a new file ([#10156](https://github.com/leanprover-community/mathlib/pull/10156))
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/arctan.lean


Modified src/analysis/special_functions/trigonometric/complex.lean
- \- *lemma* complex.continuous_at_tan
- \- *lemma* complex.deriv_tan
- \- *lemma* complex.differentiable_at_tan
- \- *lemma* complex.has_deriv_at_tan
- \- *lemma* complex.has_strict_deriv_at_tan
- \- *lemma* complex.tendsto_abs_tan_at_top
- \- *lemma* complex.tendsto_abs_tan_of_cos_eq_zero
- \- *lemma* complex.times_cont_diff_at_tan

Added src/analysis/special_functions/trigonometric/complex_deriv.lean
- \+ *lemma* complex.continuous_at_tan
- \+ *lemma* complex.deriv_tan
- \+ *lemma* complex.differentiable_at_tan
- \+ *lemma* complex.has_deriv_at_tan
- \+ *lemma* complex.has_strict_deriv_at_tan
- \+ *lemma* complex.tendsto_abs_tan_at_top
- \+ *lemma* complex.tendsto_abs_tan_of_cos_eq_zero
- \+ *lemma* complex.times_cont_diff_at_tan



## [2021-11-12 16:30:34](https://github.com/leanprover-community/mathlib/commit/6262165)
feat(analysis/normed_space/continuous_affine_map): isometry from space of continuous affine maps to product of codomain with space of continuous linear maps ([#10201](https://github.com/leanprover-community/mathlib/pull/10201))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/analysis/normed_space/continuous_affine_map.lean
- \+ *lemma* continuous_affine_map.add_cont_linear
- \+ *lemma* continuous_affine_map.coe_cont_linear
- \+/\- *lemma* continuous_affine_map.coe_linear_eq_coe_cont_linear
- \+ *lemma* continuous_affine_map.comp_cont_linear
- \+ *lemma* continuous_affine_map.decomp
- \+ *lemma* continuous_affine_map.neg_cont_linear
- \+ *lemma* continuous_affine_map.norm_comp_le
- \+ *lemma* continuous_affine_map.norm_cont_linear_le
- \+ *lemma* continuous_affine_map.norm_def
- \+ *lemma* continuous_affine_map.norm_eq
- \+ *lemma* continuous_affine_map.norm_image_zero_le
- \+ *lemma* continuous_affine_map.smul_cont_linear
- \+ *lemma* continuous_affine_map.sub_cont_linear
- \+ *lemma* continuous_affine_map.to_affine_map_cont_linear
- \+ *lemma* continuous_affine_map.to_const_prod_continuous_linear_map_fst
- \+ *lemma* continuous_affine_map.to_const_prod_continuous_linear_map_snd
- \+ *lemma* continuous_affine_map.zero_cont_linear

Modified src/topology/algebra/continuous_affine_map.lean
- \+ *lemma* continuous_affine_map.add_apply
- \+ *lemma* continuous_affine_map.coe_add
- \+ *lemma* continuous_affine_map.coe_neg
- \+ *lemma* continuous_affine_map.coe_smul
- \+ *lemma* continuous_affine_map.coe_sub
- \+ *lemma* continuous_affine_map.coe_zero
- \+ *lemma* continuous_affine_map.neg_apply
- \+ *lemma* continuous_affine_map.smul_apply
- \+ *lemma* continuous_affine_map.sub_apply
- \+ *lemma* continuous_affine_map.zero_apply
- \+ *lemma* continuous_linear_map.coe_to_continuous_affine_map
- \+ *def* continuous_linear_map.to_continuous_affine_map
- \+ *lemma* continuous_linear_map.to_continuous_affine_map_map_zero



## [2021-11-12 15:38:34](https://github.com/leanprover-community/mathlib/commit/b9f7b4d)
fix(algebra/graded_monoid): correct nonexistent names in tactic defaults ([#10293](https://github.com/leanprover-community/mathlib/pull/10293))
These were left by a bad rename by me in the past, and resulted in the default values not actually working.
#### Estimated changes
Modified src/algebra/graded_monoid.lean




## [2021-11-12 15:38:33](https://github.com/leanprover-community/mathlib/commit/d7b5ffa)
chore(linear_algebra/multilinear): add const_of_is_empty ([#10291](https://github.com/leanprover-community/mathlib/pull/10291))
This is extracted from `pi_tensor_product.is_empty_equiv`
#### Estimated changes
Modified src/linear_algebra/multilinear/basic.lean
- \+ *def* multilinear_map.const_of_is_empty

Modified src/linear_algebra/pi_tensor_product.lean




## [2021-11-12 15:38:31](https://github.com/leanprover-community/mathlib/commit/c5027c9)
doc(field_theory/separable): typo ([#10290](https://github.com/leanprover-community/mathlib/pull/10290))
#### Estimated changes
Modified src/field_theory/separable.lean




## [2021-11-12 15:04:38](https://github.com/leanprover-community/mathlib/commit/6cd6320)
feat(group_theory/complement): `is_complement'.sup_eq_top` ([#10230](https://github.com/leanprover-community/mathlib/pull/10230))
If `H` and `K` are complementary subgroups, then `H ⊔ K = ⊤`.
#### Estimated changes
Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.is_complement'.is_compl
- \+ *lemma* subgroup.is_complement'.sup_eq_top



## [2021-11-12 12:24:46](https://github.com/leanprover-community/mathlib/commit/07be904)
doc(README): add list of emeritus maintainers ([#10288](https://github.com/leanprover-community/mathlib/pull/10288))
#### Estimated changes
Modified README.md




## [2021-11-12 11:49:22](https://github.com/leanprover-community/mathlib/commit/b51335c)
feat(category_theory/sites/plus): `P⁺` for a presheaf `P`. ([#10284](https://github.com/leanprover-community/mathlib/pull/10284))
This file adds the construction of `P⁺`, for a presheaf `P : Cᵒᵖ ⥤ D`, whenever `C` has a Grothendieck topology `J` and `D` has the appropriate (co)limits.
Later, we will show that `P⁺⁺` is the sheafification of `P`, under certain additional hypotheses on `D`.
See https://stacks.math.columbia.edu/tag/00W1
#### Estimated changes
Modified src/category_theory/sites/grothendieck.lean
- \+ *def* category_theory.grothendieck_topology.cover.arrow.base
- \+ *def* category_theory.grothendieck_topology.cover.arrow.map
- \+ *structure* category_theory.grothendieck_topology.cover.arrow
- \+ *lemma* category_theory.grothendieck_topology.cover.coe_fun_coe
- \+ *lemma* category_theory.grothendieck_topology.cover.coe_pullback
- \+ *lemma* category_theory.grothendieck_topology.cover.condition
- \+ *lemma* category_theory.grothendieck_topology.cover.ext
- \+ *def* category_theory.grothendieck_topology.cover.index
- \+ *abbreviation* category_theory.grothendieck_topology.cover.multifork
- \+ *def* category_theory.grothendieck_topology.cover.pullback
- \+ *def* category_theory.grothendieck_topology.cover.pullback_comp
- \+ *def* category_theory.grothendieck_topology.cover.pullback_id
- \+ *def* category_theory.grothendieck_topology.cover.relation.base
- \+ *lemma* category_theory.grothendieck_topology.cover.relation.base_fst
- \+ *lemma* category_theory.grothendieck_topology.cover.relation.base_snd
- \+ *def* category_theory.grothendieck_topology.cover.relation.fst
- \+ *def* category_theory.grothendieck_topology.cover.relation.map
- \+ *lemma* category_theory.grothendieck_topology.cover.relation.map_fst
- \+ *lemma* category_theory.grothendieck_topology.cover.relation.map_snd
- \+ *def* category_theory.grothendieck_topology.cover.relation.snd
- \+ *structure* category_theory.grothendieck_topology.cover.relation
- \+ *abbreviation* category_theory.grothendieck_topology.cover.to_multiequalizer
- \+ *def* category_theory.grothendieck_topology.cover
- \+ *def* category_theory.grothendieck_topology.pullback
- \+ *def* category_theory.grothendieck_topology.pullback_comp
- \+ *def* category_theory.grothendieck_topology.pullback_id

Added src/category_theory/sites/plus.lean
- \+ *def* category_theory.grothendieck_topology.diagram
- \+ *def* category_theory.grothendieck_topology.diagram_pullback
- \+ *def* category_theory.grothendieck_topology.plus_functor
- \+ *def* category_theory.grothendieck_topology.plus_map
- \+ *lemma* category_theory.grothendieck_topology.plus_map_to_plus
- \+ *def* category_theory.grothendieck_topology.plus_obj
- \+ *def* category_theory.grothendieck_topology.to_plus
- \+ *def* category_theory.grothendieck_topology.to_plus_nat_trans



## [2021-11-12 10:27:58](https://github.com/leanprover-community/mathlib/commit/e679093)
feat(measure_theory): define `measurable_space` instance on a quotient ([#10275](https://github.com/leanprover-community/mathlib/pull/10275))
#### Estimated changes
Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_from_quotient
- \+ *lemma* measurable_quot_mk
- \+ *lemma* measurable_quotient_mk'
- \+ *lemma* measurable_quotient_mk
- \+ *lemma* measurable_set_quotient
- \+ *lemma* quotient_group.measurable_coe
- \+ *lemma* quotient_group.measurable_from_quotient



## [2021-11-12 09:37:57](https://github.com/leanprover-community/mathlib/commit/c45e70a)
chore(analysis/special_functions/pow): put lemmas about derivatives into a new file ([#10153](https://github.com/leanprover-community/mathlib/pull/10153))
In order to keep results about continuity of the power function in the original file, we prove some continuity results directly (these were previously proved using derivatives).
#### Estimated changes
Modified archive/100-theorems-list/9_area_of_a_circle.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/special_functions/pow.lean
- \- *lemma* complex.has_fderiv_at_cpow
- \- *lemma* complex.has_strict_deriv_at_const_cpow
- \- *lemma* complex.has_strict_deriv_at_cpow_const
- \- *lemma* complex.has_strict_fderiv_at_cpow'
- \- *lemma* complex.has_strict_fderiv_at_cpow
- \+ *lemma* continuous_at_const_cpow'
- \+ *lemma* continuous_at_const_cpow
- \+ *lemma* continuous_at_cpow
- \+ *lemma* continuous_at_cpow_const
- \+ *lemma* cpow_eq_nhds'
- \+ *lemma* cpow_eq_nhds
- \- *lemma* deriv_rpow_const
- \- *lemma* deriv_within_rpow_const
- \- *lemma* differentiable.rpow
- \- *lemma* differentiable.rpow_const
- \- *lemma* differentiable_at.const_cpow
- \- *lemma* differentiable_at.cpow
- \- *lemma* differentiable_at.rpow
- \- *lemma* differentiable_at.rpow_const
- \- *lemma* differentiable_on.rpow
- \- *lemma* differentiable_on.rpow_const
- \- *lemma* differentiable_within_at.const_cpow
- \- *lemma* differentiable_within_at.cpow
- \- *lemma* differentiable_within_at.rpow
- \- *lemma* differentiable_within_at.rpow_const
- \- *lemma* has_deriv_at.const_cpow
- \- *lemma* has_deriv_at.cpow
- \- *lemma* has_deriv_at.cpow_const
- \- *lemma* has_deriv_at.rpow
- \- *lemma* has_deriv_at.rpow_const
- \- *lemma* has_deriv_within_at.const_cpow
- \- *lemma* has_deriv_within_at.cpow
- \- *lemma* has_deriv_within_at.cpow_const
- \- *lemma* has_deriv_within_at.rpow
- \- *lemma* has_deriv_within_at.rpow_const
- \- *lemma* has_fderiv_at.const_cpow
- \- *lemma* has_fderiv_at.const_rpow
- \- *lemma* has_fderiv_at.cpow
- \- *lemma* has_fderiv_at.rpow
- \- *lemma* has_fderiv_at.rpow_const
- \- *lemma* has_fderiv_within_at.const_cpow
- \- *lemma* has_fderiv_within_at.const_rpow
- \- *lemma* has_fderiv_within_at.cpow
- \- *lemma* has_fderiv_within_at.rpow
- \- *lemma* has_fderiv_within_at.rpow_const
- \- *lemma* has_strict_deriv_at.const_cpow
- \- *lemma* has_strict_deriv_at.cpow
- \- *lemma* has_strict_deriv_at.cpow_const
- \- *lemma* has_strict_deriv_at.rpow
- \- *lemma* has_strict_fderiv_at.const_cpow
- \- *lemma* has_strict_fderiv_at.const_rpow
- \- *lemma* has_strict_fderiv_at.cpow
- \- *lemma* has_strict_fderiv_at.rpow
- \- *lemma* has_strict_fderiv_at.rpow_const
- \+ *lemma* real.continuous_at_const_rpow'
- \+ *lemma* real.continuous_at_const_rpow
- \- *lemma* real.deriv_rpow_const'
- \- *lemma* real.deriv_rpow_const
- \- *lemma* real.differentiable_at_rpow_of_ne
- \- *lemma* real.differentiable_rpow_const
- \- *lemma* real.has_deriv_at_rpow_const
- \- *lemma* real.has_strict_deriv_at_const_rpow
- \- *lemma* real.has_strict_deriv_at_const_rpow_of_neg
- \- *lemma* real.has_strict_deriv_at_rpow_const
- \- *lemma* real.has_strict_deriv_at_rpow_const_of_ne
- \- *lemma* real.has_strict_fderiv_at_rpow_of_neg
- \- *lemma* real.has_strict_fderiv_at_rpow_of_pos
- \+ *lemma* real.rpow_eq_nhds_of_neg
- \+ *lemma* real.rpow_eq_nhds_of_pos
- \- *lemma* real.times_cont_diff_at_rpow_const
- \- *lemma* real.times_cont_diff_at_rpow_const_of_le
- \- *lemma* real.times_cont_diff_at_rpow_const_of_ne
- \- *lemma* real.times_cont_diff_at_rpow_of_ne
- \- *lemma* real.times_cont_diff_rpow_const_of_le
- \- *lemma* tendsto_one_plus_div_pow_exp
- \- *lemma* tendsto_one_plus_div_rpow_exp
- \- *lemma* times_cont_diff.rpow
- \- *lemma* times_cont_diff.rpow_const_of_le
- \- *lemma* times_cont_diff.rpow_const_of_ne
- \- *lemma* times_cont_diff_at.rpow
- \- *lemma* times_cont_diff_at.rpow_const_of_le
- \- *lemma* times_cont_diff_at.rpow_const_of_ne
- \- *lemma* times_cont_diff_on.rpow
- \- *lemma* times_cont_diff_on.rpow_const_of_le
- \- *lemma* times_cont_diff_on.rpow_const_of_ne
- \- *lemma* times_cont_diff_within_at.rpow
- \- *lemma* times_cont_diff_within_at.rpow_const_of_le
- \- *lemma* times_cont_diff_within_at.rpow_const_of_ne
- \+ *lemma* zero_cpow_eq_nhds

Added src/analysis/special_functions/pow_deriv.lean
- \+ *lemma* complex.has_fderiv_at_cpow
- \+ *lemma* complex.has_strict_deriv_at_const_cpow
- \+ *lemma* complex.has_strict_deriv_at_cpow_const
- \+ *lemma* complex.has_strict_fderiv_at_cpow'
- \+ *lemma* complex.has_strict_fderiv_at_cpow
- \+ *lemma* deriv_rpow_const
- \+ *lemma* deriv_within_rpow_const
- \+ *lemma* differentiable.rpow
- \+ *lemma* differentiable.rpow_const
- \+ *lemma* differentiable_at.const_cpow
- \+ *lemma* differentiable_at.cpow
- \+ *lemma* differentiable_at.rpow
- \+ *lemma* differentiable_at.rpow_const
- \+ *lemma* differentiable_on.rpow
- \+ *lemma* differentiable_on.rpow_const
- \+ *lemma* differentiable_within_at.const_cpow
- \+ *lemma* differentiable_within_at.cpow
- \+ *lemma* differentiable_within_at.rpow
- \+ *lemma* differentiable_within_at.rpow_const
- \+ *lemma* has_deriv_at.const_cpow
- \+ *lemma* has_deriv_at.cpow
- \+ *lemma* has_deriv_at.cpow_const
- \+ *lemma* has_deriv_at.rpow
- \+ *lemma* has_deriv_at.rpow_const
- \+ *lemma* has_deriv_within_at.const_cpow
- \+ *lemma* has_deriv_within_at.cpow
- \+ *lemma* has_deriv_within_at.cpow_const
- \+ *lemma* has_deriv_within_at.rpow
- \+ *lemma* has_deriv_within_at.rpow_const
- \+ *lemma* has_fderiv_at.const_cpow
- \+ *lemma* has_fderiv_at.const_rpow
- \+ *lemma* has_fderiv_at.cpow
- \+ *lemma* has_fderiv_at.rpow
- \+ *lemma* has_fderiv_at.rpow_const
- \+ *lemma* has_fderiv_within_at.const_cpow
- \+ *lemma* has_fderiv_within_at.const_rpow
- \+ *lemma* has_fderiv_within_at.cpow
- \+ *lemma* has_fderiv_within_at.rpow
- \+ *lemma* has_fderiv_within_at.rpow_const
- \+ *lemma* has_strict_deriv_at.const_cpow
- \+ *lemma* has_strict_deriv_at.cpow
- \+ *lemma* has_strict_deriv_at.cpow_const
- \+ *lemma* has_strict_deriv_at.rpow
- \+ *lemma* has_strict_fderiv_at.const_cpow
- \+ *lemma* has_strict_fderiv_at.const_rpow
- \+ *lemma* has_strict_fderiv_at.cpow
- \+ *lemma* has_strict_fderiv_at.rpow
- \+ *lemma* has_strict_fderiv_at.rpow_const
- \+ *lemma* real.deriv_rpow_const'
- \+ *lemma* real.deriv_rpow_const
- \+ *lemma* real.differentiable_at_rpow_of_ne
- \+ *lemma* real.differentiable_rpow_const
- \+ *lemma* real.has_deriv_at_rpow_const
- \+ *lemma* real.has_strict_deriv_at_const_rpow
- \+ *lemma* real.has_strict_deriv_at_const_rpow_of_neg
- \+ *lemma* real.has_strict_deriv_at_rpow_const
- \+ *lemma* real.has_strict_deriv_at_rpow_const_of_ne
- \+ *lemma* real.has_strict_fderiv_at_rpow_of_neg
- \+ *lemma* real.has_strict_fderiv_at_rpow_of_pos
- \+ *lemma* real.times_cont_diff_at_rpow_const
- \+ *lemma* real.times_cont_diff_at_rpow_const_of_le
- \+ *lemma* real.times_cont_diff_at_rpow_const_of_ne
- \+ *lemma* real.times_cont_diff_at_rpow_of_ne
- \+ *lemma* real.times_cont_diff_rpow_const_of_le
- \+ *lemma* tendsto_one_plus_div_pow_exp
- \+ *lemma* tendsto_one_plus_div_rpow_exp
- \+ *lemma* times_cont_diff.rpow
- \+ *lemma* times_cont_diff.rpow_const_of_le
- \+ *lemma* times_cont_diff.rpow_const_of_ne
- \+ *lemma* times_cont_diff_at.rpow
- \+ *lemma* times_cont_diff_at.rpow_const_of_le
- \+ *lemma* times_cont_diff_at.rpow_const_of_ne
- \+ *lemma* times_cont_diff_on.rpow
- \+ *lemma* times_cont_diff_on.rpow_const_of_le
- \+ *lemma* times_cont_diff_on.rpow_const_of_ne
- \+ *lemma* times_cont_diff_within_at.rpow
- \+ *lemma* times_cont_diff_within_at.rpow_const_of_le
- \+ *lemma* times_cont_diff_within_at.rpow_const_of_ne

Modified src/analysis/special_functions/trigonometric/complex.lean




## [2021-11-12 07:59:47](https://github.com/leanprover-community/mathlib/commit/75207e9)
refactor(linear_algebra/eigenspace): refactor `eigenvectors_linearly_independent` ([#10198](https://github.com/leanprover-community/mathlib/pull/10198))
This refactors the proof of the lemma
```lean
lemma eigenvectors_linear_independent (f : End K V) (μs : set K) (xs : μs → V)
  (h_eigenvec : ∀ μ : μs, f.has_eigenvector μ (xs μ)) :
  linear_independent K xs
```
to extract the formulation
```lean
lemma eigenspaces_independent (f : End K V) : complete_lattice.independent f.eigenspace
```
from which `eigenvectors_linear_independent` follows as a 1-liner.
I don't need this for anything (although it might have applications -- for example, cardinality lemmas) -- just think it's a possibly more elegant statement.
#### Estimated changes
Modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* dfinsupp.sum_map_range_index.linear_map

Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* module.End.eigenspaces_independent



## [2021-11-12 07:59:46](https://github.com/leanprover-community/mathlib/commit/1019dd6)
feat(measure_theory/probability_mass_function): Define a measure assosiated to a pmf ([#9966](https://github.com/leanprover-community/mathlib/pull/9966))
This PR defines `pmf.to_outer_measure` and `pmf.to_measure`, where the measure of a set is given by the total probability of elements of the set, and shows that this is a probability measure.
#### Estimated changes
Modified src/measure_theory/probability_mass_function.lean
- \+/\- *def* pmf.support
- \+ *def* pmf.to_measure
- \+ *lemma* pmf.to_measure_apply'
- \+ *lemma* pmf.to_measure_apply
- \+ *lemma* pmf.to_measure_apply_eq_to_outer_measure_apply
- \+ *lemma* pmf.to_measure_apply_finset
- \+ *lemma* pmf.to_measure_apply_fintype
- \+ *lemma* pmf.to_measure_apply_of_finite
- \+ *def* pmf.to_outer_measure
- \+ *lemma* pmf.to_outer_measure_apply'
- \+ *lemma* pmf.to_outer_measure_apply
- \+ *lemma* pmf.to_outer_measure_apply_eq_zero_iff
- \+ *lemma* pmf.to_outer_measure_apply_finset
- \+ *lemma* pmf.to_outer_measure_apply_fintype
- \+ *lemma* pmf.to_outer_measure_apply_le_to_measure_apply
- \+ *lemma* pmf.to_outer_measure_caratheodory



## [2021-11-12 07:25:31](https://github.com/leanprover-community/mathlib/commit/9e1e4f0)
feat(category_theory/sites/*): Dense subsite ([#9694](https://github.com/leanprover-community/mathlib/pull/9694))
Defined `cover_dense` functors as functors into sites such that each object can be covered by images of the functor.
Proved that for a `cover_dense` functor `G`, any morphisms of presheaves `G ⋙ ℱ ⟶ G ⋙ ℱ'` can be glued into a 
morphism `ℱ ⟶ ℱ'`.
#### Estimated changes
Added src/category_theory/sites/dense_subsite.lean
- \+ *lemma* category_theory.cover_dense.ext
- \+ *lemma* category_theory.cover_dense.functor_pullback_pushforward_covering
- \+ *def* category_theory.cover_dense.hom_over
- \+ *lemma* category_theory.cover_dense.iso_of_restrict_iso
- \+ *def* category_theory.cover_dense.iso_over
- \+ *def* category_theory.cover_dense.presheaf_iso
- \+ *def* category_theory.cover_dense.restrict_hom_equiv_hom
- \+ *def* category_theory.cover_dense.sheaf_coyoneda_hom
- \+ *lemma* category_theory.cover_dense.sheaf_eq_amalgamation
- \+ *def* category_theory.cover_dense.sheaf_hom
- \+ *lemma* category_theory.cover_dense.sheaf_hom_eq
- \+ *lemma* category_theory.cover_dense.sheaf_hom_restrict_eq
- \+ *def* category_theory.cover_dense.sheaf_iso
- \+ *def* category_theory.cover_dense.sheaf_yoneda_hom
- \+ *def* category_theory.cover_dense.types.app_hom
- \+ *lemma* category_theory.cover_dense.types.app_hom_restrict
- \+ *lemma* category_theory.cover_dense.types.app_hom_valid_glue
- \+ *def* category_theory.cover_dense.types.app_iso
- \+ *def* category_theory.cover_dense.types.presheaf_hom
- \+ *def* category_theory.cover_dense.types.presheaf_iso
- \+ *def* category_theory.cover_dense.types.pushforward_family
- \+ *lemma* category_theory.cover_dense.types.pushforward_family_apply
- \+ *lemma* category_theory.cover_dense.types.pushforward_family_compatible
- \+ *def* category_theory.cover_dense.types.sheaf_iso
- \+ *structure* category_theory.cover_dense
- \+ *def* category_theory.presieve.cover_by_image
- \+ *structure* category_theory.presieve.cover_by_image_structure
- \+ *lemma* category_theory.presieve.in_cover_by_image
- \+ *def* category_theory.sieve.cover_by_image



## [2021-11-12 04:52:56](https://github.com/leanprover-community/mathlib/commit/6fd688b)
chore(measure_theory): move `mutually_singular` to a new file ([#10281](https://github.com/leanprover-community/mathlib/pull/10281))
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \- *lemma* measure_theory.measure.mutually_singular.add_left
- \- *lemma* measure_theory.measure.mutually_singular.add_left_iff
- \- *lemma* measure_theory.measure.mutually_singular.add_right
- \- *lemma* measure_theory.measure.mutually_singular.add_right_iff
- \- *lemma* measure_theory.measure.mutually_singular.comm
- \- *lemma* measure_theory.measure.mutually_singular.mk
- \- *lemma* measure_theory.measure.mutually_singular.mono
- \- *lemma* measure_theory.measure.mutually_singular.mono_ac
- \- *lemma* measure_theory.measure.mutually_singular.smul
- \- *lemma* measure_theory.measure.mutually_singular.smul_nnreal
- \- *lemma* measure_theory.measure.mutually_singular.sum_left
- \- *lemma* measure_theory.measure.mutually_singular.sum_right
- \- *lemma* measure_theory.measure.mutually_singular.symm
- \- *lemma* measure_theory.measure.mutually_singular.zero_left
- \- *lemma* measure_theory.measure.mutually_singular.zero_right
- \- *def* measure_theory.measure.mutually_singular

Added src/measure_theory/measure/mutually_singular.lean
- \+ *lemma* measure_theory.measure.mutually_singular.add_left
- \+ *lemma* measure_theory.measure.mutually_singular.add_left_iff
- \+ *lemma* measure_theory.measure.mutually_singular.add_right
- \+ *lemma* measure_theory.measure.mutually_singular.add_right_iff
- \+ *lemma* measure_theory.measure.mutually_singular.comm
- \+ *lemma* measure_theory.measure.mutually_singular.mk
- \+ *lemma* measure_theory.measure.mutually_singular.mono
- \+ *lemma* measure_theory.measure.mutually_singular.mono_ac
- \+ *lemma* measure_theory.measure.mutually_singular.smul
- \+ *lemma* measure_theory.measure.mutually_singular.smul_nnreal
- \+ *lemma* measure_theory.measure.mutually_singular.sum_left
- \+ *lemma* measure_theory.measure.mutually_singular.sum_right
- \+ *lemma* measure_theory.measure.mutually_singular.symm
- \+ *lemma* measure_theory.measure.mutually_singular.zero_left
- \+ *lemma* measure_theory.measure.mutually_singular.zero_right
- \+ *def* measure_theory.measure.mutually_singular



## [2021-11-12 04:52:54](https://github.com/leanprover-community/mathlib/commit/d7e320e)
feat(category_theory/limits): Cone limiting iff terminal. ([#10266](https://github.com/leanprover-community/mathlib/pull/10266))
#### Estimated changes
Added src/category_theory/limits/cone_category.lean
- \+ *def* category_theory.limits.cocone.is_colimit_equiv_is_initial
- \+ *def* category_theory.limits.cone.is_limit_equiv_is_terminal
- \+ *lemma* category_theory.limits.is_colimit.desc_cocone_morphism_eq_is_initial_to
- \+ *def* category_theory.limits.is_colimit.of_preserves_cocone_initial
- \+ *def* category_theory.limits.is_colimit.of_reflects_cocone_initial
- \+ *lemma* category_theory.limits.is_initial.to_eq_desc_cocone_morphism
- \+ *lemma* category_theory.limits.is_limit.lift_cone_morphism_eq_is_terminal_from
- \+ *def* category_theory.limits.is_limit.of_preserves_cone_terminal
- \+ *def* category_theory.limits.is_limit.of_reflects_cone_terminal
- \+ *lemma* category_theory.limits.is_terminal.from_eq_lift_cone_morphism

Modified src/category_theory/limits/preserves/shapes/terminal.lean
- \+ *lemma* category_theory.limits.has_initial_of_has_initial_of_preserves_colimit
- \+ *def* category_theory.limits.is_colimit_map_cocone_empty_cocone_equiv
- \+ *def* category_theory.limits.is_colimit_of_has_initial_of_preserves_colimit
- \+ *def* category_theory.limits.is_initial.is_initial_obj
- \+ *def* category_theory.limits.is_initial.is_initial_of_obj
- \+ *def* category_theory.limits.is_terminal.is_terminal_obj
- \+ *def* category_theory.limits.is_terminal.is_terminal_of_obj
- \- *def* category_theory.limits.is_terminal_obj_of_is_terminal
- \- *def* category_theory.limits.is_terminal_of_is_terminal_obj
- \+ *def* category_theory.limits.preserves_initial.iso
- \+ *lemma* category_theory.limits.preserves_initial.iso_hom
- \+ *def* category_theory.limits.preserves_initial.of_iso_comparison
- \+ *def* category_theory.limits.preserves_initial_of_is_iso
- \+ *def* category_theory.limits.preserves_initial_of_iso



## [2021-11-12 03:51:22](https://github.com/leanprover-community/mathlib/commit/e5a79a7)
feat(analysis/normed_space/star): introduce C*-algebras ([#10145](https://github.com/leanprover-community/mathlib/pull/10145))
This PR introduces normed star rings/algebras and C*-rings/algebras, as well as a version of `star` bundled as a linear isometric equivalence.
#### Estimated changes
Modified src/algebra/star/module.lean
- \+/\- *def* star_linear_equiv

Added src/analysis/normed_space/star.lean
- \+ *lemma* coe_starₗᵢ
- \+ *lemma* cstar_ring.norm_self_mul_star
- \+ *lemma* cstar_ring.norm_star_mul_self'
- \+ *def* starₗᵢ
- \+ *lemma* starₗᵢ_apply



## [2021-11-12 00:55:58](https://github.com/leanprover-community/mathlib/commit/d6056ee)
feat(field_theory/splitting_field): add eval_root_derivative_of_split ([#10224](https://github.com/leanprover-community/mathlib/pull/10224))
From flt-regular.
#### Estimated changes
Modified src/data/polynomial/derivative.lean
- \+ *theorem* polynomial.derivative_prod
- \+ *lemma* polynomial.eval_multiset_prod_X_sub_C_derivative

Modified src/field_theory/splitting_field.lean
- \+ *lemma* polynomial.aeval_root_derivative_of_splits



## [2021-11-12 00:19:41](https://github.com/leanprover-community/mathlib/commit/73b2b65)
feat(category_theory/limits/concrete_category): A lemma about concrete multiequalizers ([#10277](https://github.com/leanprover-community/mathlib/pull/10277))
#### Estimated changes
Modified src/category_theory/limits/concrete_category.lean
- \+ *lemma* category_theory.limits.concrete.multiequalizer_ext



## [2021-11-11 23:18:38](https://github.com/leanprover-community/mathlib/commit/0b4c540)
feat(field_theory/separable): X^n - 1 is separable iff ↑n ≠ 0. ([#9779](https://github.com/leanprover-community/mathlib/pull/9779))
Most of the proof actually due to @Vierkantor!
#### Estimated changes
Modified src/data/polynomial/monic.lean
- \+ *lemma* polynomial.not_is_unit_X_pow_sub_one

Modified src/field_theory/separable.lean
- \+ *lemma* polynomial.X_pow_sub_one_separable_iff
- \+ *lemma* polynomial.separable_X_pow_sub_C_unit



## [2021-11-11 19:35:48](https://github.com/leanprover-community/mathlib/commit/8cd5f0e)
chore(category_theory/isomorphisms): Adjust priority for is_iso.comp_is_iso ([#10276](https://github.com/leanprover-community/mathlib/pull/10276))
[See Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/iso.20to.20is_iso.20for.20types/near/261122457)
Given `f : X ≅ Y` with `X Y : Type u`, without this change, typeclass inference cannot deduce `is_iso f.hom` because `f.hom` is defeq to `(λ x, x) ≫ f.hom`, triggering a loop.
#### Estimated changes
Modified src/category_theory/isomorphism.lean




## [2021-11-11 19:35:47](https://github.com/leanprover-community/mathlib/commit/d686025)
feat(linear_algebra/pi_tensor_product): add subsingleton_equiv ([#10274](https://github.com/leanprover-community/mathlib/pull/10274))
This is useful for constructing the tensor product of a single module, which we will ultimately need to show an isomorphism to `tensor_algebra`.
This also refactors `pempty_equiv` to use `is_empty`, which probably didn't exist at the time. This eliminates a surprising universe variable that was parameterizing `pempty`.
#### Estimated changes
Modified src/linear_algebra/pi_tensor_product.lean
- \+ *def* pi_tensor_product.is_empty_equiv
- \+ *lemma* pi_tensor_product.is_empty_equiv_apply_tprod
- \- *def* pi_tensor_product.pempty_equiv
- \+ *def* pi_tensor_product.subsingleton_equiv
- \+ *lemma* pi_tensor_product.subsingleton_equiv_apply_tprod



## [2021-11-11 19:35:45](https://github.com/leanprover-community/mathlib/commit/f99d638)
feat(measure_theory): integral over a family of pairwise a.e. disjoint sets ([#10268](https://github.com/leanprover-community/mathlib/pull/10268))
Also golf a few proofs
#### Estimated changes
Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.has_sum_integral_Union_of_null_inter
- \+ *lemma* measure_theory.integral_Union_of_null_inter

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.exists_subordinate_pairwise_disjoint



## [2021-11-11 19:35:44](https://github.com/leanprover-community/mathlib/commit/12c868a)
refactor(group_theory/complement): Generalize `card_mul` to from subgroups to subsets ([#10264](https://github.com/leanprover-community/mathlib/pull/10264))
Adds `is_complement.card_mul`, which generalizes `is_complement'.card_mul`.
#### Estimated changes
Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.is_complement.card_mul



## [2021-11-11 19:35:42](https://github.com/leanprover-community/mathlib/commit/72ca0d3)
feat(linear_algebra/pi_tensor_prod): generalize actions and provide missing smul_comm_class and is_scalar_tower instance ([#10262](https://github.com/leanprover-community/mathlib/pull/10262))
Also squeezes some `simp`s.
#### Estimated changes
Modified src/linear_algebra/pi_tensor_product.lean
- \+/\- *lemma* pi_tensor_product.smul_tprod_coeff'
- \+/\- *lemma* pi_tensor_product.smul_tprod_coeff



## [2021-11-11 19:35:41](https://github.com/leanprover-community/mathlib/commit/c7f3e5c)
feat(group_theory/submonoid/membership): `exists_multiset_of_mem_closure` ([#10256](https://github.com/leanprover-community/mathlib/pull/10256))
Version of `exists_list_of_mem_closure` for `comm_monoid`.
#### Estimated changes
Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* submonoid.exists_multiset_of_mem_closure



## [2021-11-11 19:35:40](https://github.com/leanprover-community/mathlib/commit/9a30dcf)
feat(data/finset/pairwise): Interaction of `set.pairwise_disjoint` with `finset` ([#10244](https://github.com/leanprover-community/mathlib/pull/10244))
This proves a few results about `set.pairwise_disjoint` and `finset` that couldn't go `data.set.pairwise` because of cyclic imports.
#### Estimated changes
Added src/data/finset/pairwise.lean
- \+ *lemma* finset.pairwise_disjoint_range_singleton
- \+ *lemma* set.pairwise_disjoint.bUnion_finset
- \+ *lemma* set.pairwise_disjoint.elim_finset
- \+ *lemma* set.pairwise_disjoint.image_finset_of_le

Modified src/data/set/pairwise.lean
- \+ *lemma* set.pairwise_disjoint.bUnion



## [2021-11-11 19:35:38](https://github.com/leanprover-community/mathlib/commit/820f8d7)
feat(group_theory/index): Index of `subgroup.map` ([#10232](https://github.com/leanprover-community/mathlib/pull/10232))
Proves `(H.map f).index = H.index`, assuming `function.surjective f` and `f.ker ≤ H`.
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* subgroup.dvd_index_map
- \+ *lemma* subgroup.index_map
- \+ *lemma* subgroup.index_map_dvd
- \+ *lemma* subgroup.index_map_eq



## [2021-11-11 19:35:37](https://github.com/leanprover-community/mathlib/commit/4b1a057)
feat(algebra/order/sub): An `add_group` has ordered subtraction ([#10225](https://github.com/leanprover-community/mathlib/pull/10225))
This wraps up `sub_le_iff_le_add` in an `has_ordered_sub` instance.
#### Estimated changes
Modified src/algebra/order/group.lean


Modified src/data/real/ennreal.lean




## [2021-11-11 19:35:36](https://github.com/leanprover-community/mathlib/commit/a9c3ab5)
feat(data/polynomial): assorted lemmas on division and gcd of polynomials ([#9600](https://github.com/leanprover-community/mathlib/pull/9600))
This PR provides a couple of lemmas involving the division and gcd operators of polynomials that I needed for [#9563](https://github.com/leanprover-community/mathlib/pull/9563). The ones that generalized to `euclidean_domain` and/or `gcd_monoid` are provided in the respective files.
#### Estimated changes
Modified src/algebra/euclidean_domain.lean
- \+ *lemma* euclidean_domain.div_dvd_of_dvd
- \+ *lemma* euclidean_domain.div_one
- \+ *lemma* euclidean_domain.mul_div_mul_cancel

Modified src/data/polynomial/field_division.lean
- \+ *lemma* polynomial.C_mul_dvd
- \+ *lemma* polynomial.div_C_mul
- \+ *lemma* polynomial.dvd_C_mul
- \+ *lemma* polynomial.leading_coeff_div

Modified src/ring_theory/euclidean_domain.lean
- \+ *lemma* left_div_gcd_ne_zero
- \+ *lemma* right_div_gcd_ne_zero

Modified src/ring_theory/polynomial/content.lean
- \+ *lemma* polynomial.degree_gcd_le_left
- \+ *lemma* polynomial.degree_gcd_le_right



## [2021-11-11 19:02:03](https://github.com/leanprover-community/mathlib/commit/01e7b20)
feat(analysis/subadditive): prove that, if u_n is subadditive, then u_n / n converges. ([#10258](https://github.com/leanprover-community/mathlib/pull/10258))
#### Estimated changes
Added src/analysis/subadditive.lean
- \+ *lemma* subadditive.apply_mul_add_le
- \+ *lemma* subadditive.eventually_div_lt_of_div_lt
- \+ *lemma* subadditive.lim_le_div
- \+ *theorem* subadditive.tendsto_lim
- \+ *def* subadditive



## [2021-11-11 14:48:45](https://github.com/leanprover-community/mathlib/commit/4df3cd7)
chore(analysis/special_functions/complex/log): move results about derivatives to a new file ([#10117](https://github.com/leanprover-community/mathlib/pull/10117))
#### Estimated changes
Modified src/analysis/special_functions/complex/log.lean
- \- *def* complex.exp_local_homeomorph
- \- *lemma* complex.has_strict_deriv_at_log
- \- *lemma* complex.has_strict_fderiv_at_log_real
- \- *lemma* complex.times_cont_diff_at_log
- \+ *lemma* continuous_at_clog
- \- *lemma* differentiable.clog
- \- *lemma* differentiable_at.clog
- \- *lemma* differentiable_on.clog
- \- *lemma* differentiable_within_at.clog
- \- *lemma* has_deriv_at.clog
- \- *lemma* has_deriv_at.clog_real
- \- *lemma* has_deriv_within_at.clog
- \- *lemma* has_deriv_within_at.clog_real
- \- *lemma* has_fderiv_at.clog
- \- *lemma* has_fderiv_within_at.clog
- \- *lemma* has_strict_deriv_at.clog
- \- *lemma* has_strict_deriv_at.clog_real
- \- *lemma* has_strict_fderiv_at.clog

Added src/analysis/special_functions/complex/log_deriv.lean
- \+ *def* complex.exp_local_homeomorph
- \+ *lemma* complex.has_strict_deriv_at_log
- \+ *lemma* complex.has_strict_fderiv_at_log_real
- \+ *lemma* complex.times_cont_diff_at_log
- \+ *lemma* differentiable.clog
- \+ *lemma* differentiable_at.clog
- \+ *lemma* differentiable_on.clog
- \+ *lemma* differentiable_within_at.clog
- \+ *lemma* has_deriv_at.clog
- \+ *lemma* has_deriv_at.clog_real
- \+ *lemma* has_deriv_within_at.clog
- \+ *lemma* has_deriv_within_at.clog_real
- \+ *lemma* has_fderiv_at.clog
- \+ *lemma* has_fderiv_within_at.clog
- \+ *lemma* has_strict_deriv_at.clog
- \+ *lemma* has_strict_deriv_at.clog_real
- \+ *lemma* has_strict_fderiv_at.clog

Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/trigonometric/complex.lean




## [2021-11-11 14:04:29](https://github.com/leanprover-community/mathlib/commit/6e268cd)
chore(probability_theory/notation): change `volume` to `measure_theory.measure.volume` ([#10272](https://github.com/leanprover-community/mathlib/pull/10272))
#### Estimated changes
Modified src/probability_theory/notation.lean




## [2021-11-11 13:22:36](https://github.com/leanprover-community/mathlib/commit/270c644)
feat(measure_theory): add `ae_measurable.sum_measure` ([#10271](https://github.com/leanprover-community/mathlib/pull/10271))
Also add a few supporting lemmas.
#### Estimated changes
Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_of_subsingleton_codomain

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* ae_measurable.sum_measure
- \+ *lemma* ae_measurable_Union_iff
- \+/\- *lemma* ae_measurable_add_measure_iff
- \+ *lemma* ae_measurable_of_subsingleton_codomain
- \+ *lemma* ae_measurable_sum_measure_iff
- \+ *lemma* measure_theory.measure.ae_sum_eq
- \+ *lemma* measure_theory.measure.ae_sum_iff'
- \+ *lemma* measure_theory.measure.ae_sum_iff
- \+ *lemma* measure_theory.measure.restrict_Union_ae
- \+ *lemma* measure_theory.measure.restrict_Union_apply_ae
- \+ *lemma* measure_theory.measure.sum_apply_eq_zero'
- \+ *lemma* measure_theory.measure.sum_apply_eq_zero



## [2021-11-11 11:44:13](https://github.com/leanprover-community/mathlib/commit/c062d9e)
feat(*): more bundled versions of `(fin 2 → α) ≃ (α × α)` ([#10214](https://github.com/leanprover-community/mathlib/pull/10214))
Also ensure that the inverse function uses vector notation when possible.
#### Estimated changes
Modified src/data/equiv/fin.lean
- \+/\- *def* fin_two_arrow_equiv

Modified src/linear_algebra/pi.lean
- \+ *def* linear_equiv.fin_two_arrow
- \+ *def* linear_equiv.pi_fin_two

Modified src/topology/algebra/module.lean
- \+ *def* continuous_linear_equiv.fin_two_arrow
- \+ *def* continuous_linear_equiv.pi_fin_two
- \+ *def* continuous_linear_equiv.simps.apply
- \+ *def* continuous_linear_equiv.simps.symm_apply
- \+ *def* continuous_linear_map.simps.apply
- \+ *def* continuous_linear_map.simps.coe

Modified src/topology/homeomorph.lean
- \+ *def* homeomorph.fin_two_arrow
- \+ *def* homeomorph.{u}



## [2021-11-11 10:26:15](https://github.com/leanprover-community/mathlib/commit/e4a882d)
feat(measure_theory): a file about null measurable sets/functions ([#10231](https://github.com/leanprover-community/mathlib/pull/10231))
* Move definitions and lemmas about `null_measurable` to a new file.
* Redefine, rename, review API.
#### Estimated changes
Modified docs/overview.yaml


Modified src/algebra/support.lean
- \+ *lemma* function.mul_support_eq_preimage

Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/measure/measure_space.lean
- \- *def* completion
- \- *lemma* measurable.ae_eq
- \- *theorem* measurable_set.diff_null
- \- *theorem* measurable_set.null_measurable_set
- \- *theorem* measure_theory.measure.is_complete.out
- \- *theorem* measure_theory.measure.is_complete_iff
- \+ *lemma* measure_theory.measure.restrict_apply₀
- \- *lemma* measure_theory.measure_Union
- \+ *lemma* measure_theory.null_measurable_set.mono
- \+ *lemma* measure_theory.null_measurable_set.mono_ac
- \+ *lemma* measure_theory.to_measure_apply₀
- \- *def* null_measurable
- \- *theorem* null_measurable_set.Union_nat
- \- *theorem* null_measurable_set.compl
- \- *theorem* null_measurable_set.diff_null
- \- *theorem* null_measurable_set.union_null
- \- *def* null_measurable_set
- \- *theorem* null_measurable_set_iff
- \- *theorem* null_measurable_set_iff_ae
- \- *theorem* null_measurable_set_iff_sandwich
- \- *theorem* null_measurable_set_measure_eq
- \- *theorem* null_measurable_set_of_complete
- \- *theorem* null_null_measurable_set
- \- *lemma* restrict_apply_of_null_measurable_set

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_theory.ae_le_to_measurable

Added src/measure_theory/measure/null_measurable.lean
- \+ *lemma* finset.null_measurable_set_bInter
- \+ *lemma* finset.null_measurable_set_bUnion
- \+ *lemma* measurable.congr_ae
- \+ *lemma* measurable_set.null_measurable_set
- \+ *lemma* measure_theory.measurable.comp_null_measurable
- \+ *theorem* measure_theory.measurable_set_of_null
- \+ *lemma* measure_theory.measure.coe_completion
- \+ *def* measure_theory.measure.completion
- \+ *lemma* measure_theory.measure.completion_apply
- \+ *theorem* measure_theory.measure.is_complete.out
- \+ *theorem* measure_theory.measure.is_complete_iff
- \+ *lemma* measure_theory.measure_Union
- \+ *lemma* measure_theory.measure_Union₀
- \+ *lemma* measure_theory.measure_union₀
- \+ *lemma* measure_theory.null_measurable.congr
- \+ *theorem* measure_theory.null_measurable.measurable_of_complete
- \+ *def* measure_theory.null_measurable
- \+ *lemma* measure_theory.null_measurable_set.Inter_Prop
- \+ *lemma* measure_theory.null_measurable_set.Inter_fintype
- \+ *lemma* measure_theory.null_measurable_set.Union_Prop
- \+ *lemma* measure_theory.null_measurable_set.Union_fintype
- \+ *lemma* measure_theory.null_measurable_set.compl
- \+ *lemma* measure_theory.null_measurable_set.compl_iff
- \+ *lemma* measure_theory.null_measurable_set.compl_to_measurable_compl_ae_eq
- \+ *lemma* measure_theory.null_measurable_set.exists_measurable_subset_ae_eq
- \+ *lemma* measure_theory.null_measurable_set.exists_measurable_superset_ae_eq
- \+ *theorem* measure_theory.null_measurable_set.measurable_of_complete
- \+ *lemma* measure_theory.null_measurable_set.of_compl
- \+ *lemma* measure_theory.null_measurable_set.of_null
- \+ *lemma* measure_theory.null_measurable_set.of_subsingleton
- \+ *lemma* measure_theory.null_measurable_set.to_measurable_ae_eq
- \+ *def* measure_theory.null_measurable_set
- \+ *lemma* measure_theory.null_measurable_set_empty
- \+ *lemma* measure_theory.null_measurable_set_eq
- \+ *lemma* measure_theory.null_measurable_set_insert
- \+ *lemma* measure_theory.null_measurable_set_singleton
- \+ *lemma* measure_theory.null_measurable_set_to_measurable
- \+ *lemma* measure_theory.null_measurable_set_univ
- \+ *def* measure_theory.null_measurable_space
- \+ *lemma* set.finite.null_measurable_set_bInter
- \+ *lemma* set.finite.null_measurable_set_bUnion
- \+ *lemma* set.finite.null_measurable_set_sInter
- \+ *lemma* set.finite.null_measurable_set_sUnion



## [2021-11-11 09:29:24](https://github.com/leanprover-community/mathlib/commit/d5964a9)
feat(measure_theory): `int.floor` etc are measurable ([#10265](https://github.com/leanprover-community/mathlib/pull/10265))
## API changes
### `algebra/order/archimedean`
* rename `rat.cast_floor` to `rat.floor_cast` to reflect the order of operations;
* same for `rat.cast_ceil` and `rat.cast_round`;
* add `rat.cast_fract`.
### `algebra/order/floor`
* add `@[simp]` to `nat.floor_eq_zero`;
* add `nat.floor_eq_iff'`, `nat.preimage_floor_zero`, and `nat.preimage_floor_of_ne_zero`;
* add `nat.ceil_eq_iff`, `nat.preimage_ceil_zero`, and `nat.preimage_ceil_of_ne_zero`;
* add `int.preimage_floor_singleton`;
* add `int.self_sub_floor`, `int.fract_int_add`, `int.preimage_fract`, `int.image_fract`;
* add `int.preimage_ceil_singleton`.
### `measure_theory/function/floor`
New file. Prove that the functions defined in `algebra.order.floor` are measurable.
#### Estimated changes
Modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean


Modified src/algebra/order/archimedean.lean
- \- *theorem* rat.cast_ceil
- \- *theorem* rat.cast_floor
- \+ *theorem* rat.cast_fract
- \- *theorem* rat.cast_round
- \+ *theorem* rat.ceil_cast
- \+ *theorem* rat.floor_cast
- \+ *theorem* rat.round_cast

Modified src/algebra/order/floor.lean
- \+/\- *lemma* int.fract_add_int
- \+ *lemma* int.fract_int_add
- \+/\- *lemma* int.fract_sub_int
- \+ *lemma* int.image_fract
- \+ *lemma* int.preimage_ceil_singleton
- \+ *lemma* int.preimage_floor_singleton
- \+ *lemma* int.preimage_fract
- \+ *lemma* int.self_sub_floor
- \+ *lemma* nat.ceil_eq_iff
- \+ *lemma* nat.floor_eq_iff'
- \+/\- *lemma* nat.floor_eq_zero
- \+ *lemma* nat.preimage_ceil_of_ne_zero
- \+ *lemma* nat.preimage_ceil_zero
- \+ *lemma* nat.preimage_floor_of_ne_zero
- \+ *lemma* nat.preimage_floor_zero

Added src/measure_theory/function/floor.lean
- \+ *lemma* int.measurable_ceil
- \+ *lemma* int.measurable_floor
- \+ *lemma* measurable.ceil
- \+ *lemma* measurable.floor
- \+ *lemma* measurable.fract
- \+ *lemma* measurable.nat_ceil
- \+ *lemma* measurable.nat_floor
- \+ *lemma* measurable_fract
- \+ *lemma* measurable_set.image_fract
- \+ *lemma* nat.measurable_ceil
- \+ *lemma* nat.measurable_floor

Modified src/number_theory/zsqrtd/gaussian_int.lean




## [2021-11-11 07:23:55](https://github.com/leanprover-community/mathlib/commit/8c1fa70)
feat(category_theory/limits/concrete_category): Some lemmas about filtered colimits ([#10270](https://github.com/leanprover-community/mathlib/pull/10270))
This PR adds some lemmas about (filtered) colimits in concrete categories which are preserved under the forgetful functor.
This will be used later for the sheafification construction.
#### Estimated changes
Modified src/category_theory/limits/concrete_category.lean
- \+ *lemma* category_theory.limits.concrete.colimit_exists_of_rep_eq
- \+ *theorem* category_theory.limits.concrete.colimit_rep_eq_iff_exists
- \+ *lemma* category_theory.limits.concrete.colimit_rep_eq_of_exists
- \+ *lemma* category_theory.limits.concrete.is_colimit_exists_of_rep_eq
- \+ *theorem* category_theory.limits.concrete.is_colimit_rep_eq_iff_exists
- \+ *lemma* category_theory.limits.concrete.is_colimit_rep_eq_of_exists



## [2021-11-10 21:52:09](https://github.com/leanprover-community/mathlib/commit/dfa7363)
feat(analysis/normed_space/finite_dimension): finite-dimensionality of spaces of continuous linear map ([#10259](https://github.com/leanprover-community/mathlib/pull/10259))
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* inner_product_space.of_core.inner_self_eq_norm_mul_norm
- \- *lemma* inner_product_space.of_core.inner_self_eq_norm_sq
- \+ *lemma* inner_self_eq_norm_mul_norm
- \+/\- *lemma* inner_self_eq_norm_sq
- \+ *lemma* real_inner_self_eq_norm_mul_norm
- \+/\- *lemma* real_inner_self_eq_norm_sq

Modified src/analysis/inner_product_space/calculus.lean


Modified src/analysis/inner_product_space/dual.lean
- \+ *lemma* inner_product_space.to_dual_symm_apply

Modified src/analysis/inner_product_space/rayleigh.lean


Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/quaternion.lean


Modified src/geometry/euclidean/basic.lean


Modified src/geometry/euclidean/circumcenter.lean


Modified src/geometry/euclidean/triangle.lean


Modified src/geometry/manifold/instances/sphere.lean


Modified src/topology/algebra/module.lean
- \+ *def* continuous_linear_map.coe_lm



## [2021-11-10 20:44:38](https://github.com/leanprover-community/mathlib/commit/3c2bc2e)
lint(scripts/lint-style.py): add indentation linter ([#10257](https://github.com/leanprover-community/mathlib/pull/10257))
#### Estimated changes
Modified scripts/lint-style.py




## [2021-11-10 17:25:44](https://github.com/leanprover-community/mathlib/commit/6f10557)
refactor(order): order_{top,bot} as mixin ([#10097](https://github.com/leanprover-community/mathlib/pull/10097))
This changes `order_top α` / `order_bot α` to _require_ `has_le α` instead of _extending_ `partial_order α`.
As a result, `order_top` can be combined with other lattice typeclasses. This lends itself to more refactors downstream, such as phrasing lemmas that currently require orders/semilattices and top/bot to provide them as separate TC inference, instead of "bundled" classes like `semilattice_inf_top`.
This refactor also provides the basis for making more consistent the "extended" algebraic classes, like "e(nn)real", "enat", etc. Some proof terms for lemmas about `nnreal` and `ennreal` have been switched to rely on more direct coercions from the underlying non-extended type or other (semi)rings.
Modify `semilattice_{inf,sup}_{top,bot}` to not directly inherit from
`order_{top,bot}`. Instead, they are now extending from `has_{top,bot}`. Extending `order_{top,bot}` is now only possible is `has_le` is provided to the TC cache at `extends` declaration time, when using `old_structure_cmd true`. That is,
```
set_option old_structure_cmd true
class mnwe (α : Type u) extends semilattice_inf α, order_top α.
```
errors with
```
type mismatch at application
  @semilattice_inf.to_partial_order α top
term
  top
has type
  α
but is expected to have type
  semilattice_inf α
```
One can make this work through one of three ways:
No `old_structure_cmd`, which is unfriendly to the rest of the class hierarchy
Require `has_le` in `class mwe (α : Type u) [has_le α] extends semilattice_inf α, order_top α.`, which is unfriendly to the existing hierarchy and how lemmas are stated.
Provide an additional axiom on top of a "data-only" TC and have a low-priority instance:
```
class semilattice_inf_top (α : Type u) extends semilattice_inf α, has_top α :=
(le_top : ∀ a : α, a ≤ ⊤)
@[priority 100]
instance semilattice_inf_top.to_order_top : order_top α :=
{ top := ⊤,  le_top := semilattice_inf_top.le_top }
```
The third option is chosen in this refactor.
Pulled out from [#9891](https://github.com/leanprover-community/mathlib/pull/9891), without the semilattice refactor.
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/algebra/module/submodule_lattice.lean


Modified src/algebra/order/monoid.lean


Modified src/algebra/order/nonneg.lean
- \+ *lemma* nonneg.bot_eq

Modified src/algebra/tropical/basic.lean
- \+/\- *lemma* tropical.le_zero

Modified src/analysis/box_integral/partition/basic.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/normed/group/basic.lean


Modified src/analysis/normed_space/enorm.lean


Modified src/analysis/specific_limits.lean


Modified src/category_theory/sites/pretopology.lean


Modified src/category_theory/subobject/lattice.lean


Modified src/combinatorics/colex.lean


Modified src/control/lawful_fix.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/finset/basic.lean
- \+/\- *lemma* finset.bot_eq_empty

Modified src/data/finset/locally_finite.lean


Modified src/data/finsupp/lattice.lean


Modified src/data/fintype/basic.lean


Modified src/data/multiset/basic.lean


Modified src/data/nat/enat.lean


Modified src/data/part.lean


Modified src/data/pequiv.lean


Modified src/data/pnat/basic.lean


Modified src/data/real/ereal.lean


Modified src/data/semiquot.lean


Modified src/data/set/intervals/basic.lean
- \+/\- *def* order_iso.Ici_bot
- \+/\- *def* order_iso.Iic_top
- \+/\- *lemma* set.Ici_bot
- \+/\- *lemma* set.Ici_top
- \+/\- *lemma* set.Iic_bot

Modified src/data/set/lattice.lean


Modified src/data/setoid/basic.lean


Modified src/field_theory/adjoin.lean


Modified src/geometry/manifold/charted_space.lean


Modified src/linear_algebra/linear_pmap.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measure/outer_measure.lean
- \+ *theorem* measure_theory.outer_measure.coe_bot

Modified src/order/atoms.lean
- \+/\- *lemma* order_iso.is_atom_iff
- \+/\- *lemma* order_iso.is_atomic_iff
- \+/\- *lemma* order_iso.is_coatom_iff
- \+/\- *lemma* order_iso.is_coatomic_iff
- \+/\- *lemma* order_iso.is_simple_lattice
- \+/\- *lemma* order_iso.is_simple_lattice_iff

Modified src/order/bounded_lattice.lean
- \+/\- *theorem* bot_le
- \+/\- *theorem* le_top
- \+/\- *theorem* not_lt_bot
- \+/\- *theorem* not_top_lt
- \+/\- *theorem* order_bot.ext
- \+/\- *theorem* order_bot.ext_bot
- \+/\- *theorem* order_top.ext
- \+/\- *theorem* order_top.ext_top
- \+/\- *lemma* strict_mono.maximal_preimage_top
- \+/\- *lemma* strict_mono.minimal_preimage_bot
- \+/\- *lemma* with_bot.get_or_else_bot_le_iff

Modified src/order/bounds.lean
- \+/\- *lemma* is_glb_empty
- \+/\- *lemma* is_glb_univ
- \+/\- *lemma* is_greatest_univ
- \+/\- *lemma* is_least_univ
- \+/\- *lemma* is_lub_empty
- \+/\- *lemma* is_lub_univ
- \+/\- *lemma* order_bot.lower_bounds_univ
- \+/\- *lemma* order_top.upper_bounds_univ

Modified src/order/category/NonemptyFinLinOrd.lean


Modified src/order/closure.lean
- \+/\- *lemma* lower_adjoint.closure_top

Modified src/order/compactly_generated.lean


Modified src/order/complete_lattice.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* filter.order_bot.at_bot_eq
- \+/\- *lemma* filter.order_top.at_top_eq
- \+/\- *lemma* filter.tendsto_at_bot_pure
- \+/\- *lemma* filter.tendsto_at_top_pure

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.eventually.lt_top_iff_ne_top
- \+/\- *lemma* filter.eventually.lt_top_of_ne
- \+/\- *lemma* filter.eventually.ne_top_of_lt

Modified src/order/filter/germ.lean


Modified src/order/galois_connection.lean
- \+/\- *def* galois_coinsertion.lift_order_bot
- \+/\- *def* galois_connection.lift_order_bot
- \+/\- *def* galois_connection.lift_order_top
- \+/\- *def* galois_insertion.lift_order_top
- \+/\- *def* with_bot.gi_get_or_else_bot

Modified src/order/ideal.lean


Modified src/order/lattice_intervals.lean
- \+/\- *lemma* set.Ici.coe_top
- \+/\- *lemma* set.Iic.coe_bot

Modified src/order/liminf_limsup.lean
- \+/\- *lemma* filter.is_bounded_ge_of_bot
- \+/\- *lemma* filter.is_bounded_le_of_top
- \+/\- *lemma* filter.is_cobounded_ge_of_top
- \+/\- *lemma* filter.is_cobounded_le_of_bot

Modified src/order/locally_finite.lean


Modified src/order/pfilter.lean


Modified src/order/preorder_hom.lean


Modified src/order/rel_iso.lean
- \+/\- *lemma* order_iso.map_bot'
- \+/\- *lemma* order_iso.map_bot
- \+/\- *lemma* order_iso.map_top'
- \+/\- *lemma* order_iso.map_top

Modified src/order/succ_pred.lean


Modified src/order/symm_diff.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/noetherian.lean


Modified src/set_theory/cardinal.lean


Modified src/tactic/interval_cases.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* nhds_bot_order
- \+/\- *lemma* nhds_top_order
- \+/\- *lemma* tendsto_nhds_bot_mono'
- \+/\- *lemma* tendsto_nhds_bot_mono
- \+/\- *lemma* tendsto_nhds_top_mono'
- \+/\- *lemma* tendsto_nhds_top_mono

Modified src/topology/basic.lean
- \+/\- *lemma* order_top.tendsto_at_top_nhds

Modified src/topology/category/Top/open_nhds.lean


Modified src/topology/discrete_quotient.lean


Modified src/topology/metric_space/emetric_space.lean




## [2021-11-10 16:26:10](https://github.com/leanprover-community/mathlib/commit/cd5cb44)
chore(set_theory/cardinal_ordinal): golf some proofs ([#10260](https://github.com/leanprover-community/mathlib/pull/10260))
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean




## [2021-11-10 14:52:29](https://github.com/leanprover-community/mathlib/commit/8aadbcb)
feat(linear_algebra/*_algebra): add some simp lemmas about the algebra map and generators of free constructions ([#10247](https://github.com/leanprover-community/mathlib/pull/10247))
These are quite repetitive, but I'm not sure how to generalize
#### Estimated changes
Modified src/algebra/free_algebra.lean
- \+ *lemma* free_algebra.algebra_map_eq_one_iff
- \+ *lemma* free_algebra.algebra_map_eq_zero_iff
- \+ *lemma* free_algebra.algebra_map_inj
- \+ *lemma* free_algebra.ι_inj
- \+ *lemma* free_algebra.ι_ne_algebra_map
- \+ *lemma* free_algebra.ι_ne_one
- \+ *lemma* free_algebra.ι_ne_zero

Modified src/linear_algebra/exterior_algebra.lean
- \+ *lemma* exterior_algebra.algebra_map_eq_one_iff
- \+ *lemma* exterior_algebra.algebra_map_eq_zero_iff
- \+ *lemma* exterior_algebra.algebra_map_inj
- \+ *def* exterior_algebra.to_triv_sq_zero_ext
- \+ *lemma* exterior_algebra.to_triv_sq_zero_ext_ι
- \+ *lemma* exterior_algebra.ι_eq_algebra_map_iff
- \+ *lemma* exterior_algebra.ι_eq_zero_iff
- \+ *lemma* exterior_algebra.ι_inj
- \+ *lemma* exterior_algebra.ι_ne_one
- \+ *lemma* exterior_algebra.ι_range_disjoint_one

Modified src/linear_algebra/tensor_algebra.lean
- \+ *lemma* tensor_algebra.algebra_map_eq_one_iff
- \+ *lemma* tensor_algebra.algebra_map_eq_zero_iff
- \+ *lemma* tensor_algebra.algebra_map_inj
- \+ *def* tensor_algebra.to_triv_sq_zero_ext
- \+ *lemma* tensor_algebra.to_triv_sq_zero_ext_ι
- \+ *lemma* tensor_algebra.ι_eq_algebra_map_iff
- \+ *lemma* tensor_algebra.ι_eq_zero_iff
- \+ *lemma* tensor_algebra.ι_inj
- \+ *lemma* tensor_algebra.ι_ne_one
- \+ *lemma* tensor_algebra.ι_range_disjoint_one



## [2021-11-10 14:52:28](https://github.com/leanprover-community/mathlib/commit/543fcef)
chore(algebra/group_power/lemmas): minimize imports ([#10246](https://github.com/leanprover-community/mathlib/pull/10246))
Most of these were imported transitively anyway, but `data.list.basic` is unneeded.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean




## [2021-11-10 14:52:26](https://github.com/leanprover-community/mathlib/commit/444b596)
doc(ring_theory/norm) `norm_eq_prod_embeddings` docstring ([#10242](https://github.com/leanprover-community/mathlib/pull/10242))
#### Estimated changes
Modified src/ring_theory/norm.lean




## [2021-11-10 14:52:24](https://github.com/leanprover-community/mathlib/commit/bbbefe4)
feat(measure_theory/constructions/{pi,prod}): drop some measurability assumptions ([#10241](https://github.com/leanprover-community/mathlib/pull/10241))
Some lemmas (most notably `prod_prod` and `pi_pi`) are true for non-measurable sets as well.
#### Estimated changes
Modified src/data/equiv/list.lean
- \+/\- *theorem* encodable.length_sorted_univ
- \+/\- *theorem* encodable.mem_sorted_univ
- \+/\- *theorem* encodable.sorted_univ_nodup
- \+ *theorem* encodable.sorted_univ_to_finset

Modified src/measure_theory/constructions/pi.lean
- \+ *lemma* measure_theory.measure.pi'_eq_pi
- \+/\- *lemma* measure_theory.measure.pi'_pi
- \- *lemma* measure_theory.measure.pi'_pi_le
- \+/\- *lemma* measure_theory.measure.pi_ball
- \+/\- *lemma* measure_theory.measure.pi_closed_ball
- \+/\- *lemma* measure_theory.measure.pi_pi
- \+ *lemma* measure_theory.measure.pi_pi_aux
- \+/\- *lemma* measure_theory.measure.pi_univ
- \- *lemma* measure_theory.measure.tprod_tprod_le

Modified src/measure_theory/constructions/prod.lean
- \+/\- *lemma* measure_theory.measure.prod_prod
- \- *lemma* measure_theory.measure.prod_prod_le
- \+/\- *lemma* measure_theory.measure.prod_restrict
- \+/\- *lemma* measure_theory.measure.restrict_prod_eq_prod_univ
- \+ *lemma* measure_theory.set_integral_prod

Modified src/measure_theory/group/arithmetic.lean
- \+ *lemma* measurable_set.inv

Modified src/measure_theory/group/prod.lean
- \+/\- *lemma* measure_theory.measure_inv_null
- \+/\- *lemma* measure_theory.measure_mul_right_ne_zero
- \+/\- *lemma* measure_theory.measure_mul_right_null
- \- *lemma* measure_theory.measure_null_of_measure_inv_null
- \+ *lemma* measure_theory.quasi_measure_preserving_inv

Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/measure_theory/measure/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.quasi_measure_preserving.preimage_null



## [2021-11-10 14:52:23](https://github.com/leanprover-community/mathlib/commit/eadd440)
feat(group_theory/index): `card_mul_index` ([#10228](https://github.com/leanprover-community/mathlib/pull/10228))
Proves `nat.card H * H.index = nat.card G` as the special case of `K.relindex H * H.index = K.index` when `K = ⊥`.
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* subgroup.card_mul_index



## [2021-11-10 14:52:21](https://github.com/leanprover-community/mathlib/commit/2b57ee7)
fix(*): fix many indentation mistakes ([#10163](https://github.com/leanprover-community/mathlib/pull/10163))
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified archive/miu_language/decision_nec.lean


Modified src/algebra/category/CommRing/pushout.lean


Modified src/algebra/geom_sum.lean


Modified src/algebraic_geometry/Spec.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/convex/combination.lean


Modified src/analysis/convex/function.lean


Modified src/analysis/inner_product_space/basic.lean


Modified src/data/buffer/parser/basic.lean


Modified src/data/fin/basic.lean


Modified src/data/list/nodup.lean


Modified src/data/list/rotate.lean


Modified src/data/list/tfae.lean


Modified src/data/mv_polynomial/rename.lean


Modified src/data/nat/digits.lean


Modified src/data/polynomial/eval.lean


Modified src/data/rbmap/default.lean


Modified src/data/rbtree/basic.lean


Modified src/data/rbtree/insert.lean


Modified src/data/rbtree/min_max.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/pi/bounds.lean


Modified src/data/stream/init.lean


Modified src/data/vector/basic.lean


Modified src/field_theory/primitive_element.lean


Modified src/group_theory/monoid_localization.lean


Modified src/group_theory/perm/list.lean


Modified src/group_theory/perm/support.lean


Modified src/group_theory/specific_groups/dihedral.lean


Modified src/linear_algebra/dimension.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/number_theory/bernoulli_polynomials.lean


Modified src/number_theory/fermat4.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/symmetric.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/tensor_product.lean


Modified src/set_theory/game.lean


Modified src/tactic/omega/int/dnf.lean


Modified src/topology/algebra/valuation.lean


Modified src/topology/sheaves/forget.lean




## [2021-11-10 14:52:20](https://github.com/leanprover-community/mathlib/commit/f41854e)
feat(ring_theory/ideal/over): algebra structure on R/p → S/P for `P` lying over `p` ([#9858](https://github.com/leanprover-community/mathlib/pull/9858))
This PR shows `P` lies over `p` if there is an injective map completing the square `R/p ← R —f→ S → S/P`, and conversely that there is a (not necessarily injective, since `f` doesn't have to be) map completing the square if `P` lies over `p`. Then we specialize this to the case where `P = map f p` to provide an `algebra p.quotient (map f p).quotient` instance.
This algebra instance is useful if you want to study the extension `R → S` locally at `p`, e.g. to show `R/p : S/pS` has the same dimension as `Frac(R) : Frac(S)` if `p` is prime.
#### Estimated changes
Modified src/ring_theory/ideal/over.lean
- \+ *lemma* ideal.comap_eq_of_scalar_tower_quotient
- \+ *lemma* ideal.quotient.algebra_map_quotient_map_quotient
- \+ *def* ideal.quotient.algebra_quotient_of_le_comap
- \+ *lemma* ideal.quotient.mk_smul_mk_quotient_map_quotient



## [2021-11-10 14:52:18](https://github.com/leanprover-community/mathlib/commit/e1fea3a)
feat(ring_theory/ideal): the product and infimum of principal ideals ([#9852](https://github.com/leanprover-community/mathlib/pull/9852))
Three useful lemmas for applying the Chinese remainder theorem when an ideal is generated by one, non-prime, element.
#### Estimated changes
Modified src/algebra/algebra/operations.lean
- \+ *lemma* submodule.prod_span
- \+ *lemma* submodule.prod_span_singleton

Modified src/algebra/module/submodule_lattice.lean
- \+ *theorem* submodule.finset_inf_coe
- \+ *theorem* submodule.mem_finset_inf

Modified src/algebra/pointwise.lean
- \+ *lemma* set.finset_prod_singleton

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.finset_inf_span_singleton
- \+ *lemma* ideal.infi_span_singleton
- \+ *lemma* ideal.prod_span
- \+ *lemma* ideal.prod_span_singleton

Modified src/ring_theory/multiplicity.lean




## [2021-11-10 13:12:51](https://github.com/leanprover-community/mathlib/commit/bfd3a89)
doc(algebra/ring/basic): fix typo ([#10250](https://github.com/leanprover-community/mathlib/pull/10250))
#### Estimated changes
Modified src/algebra/ring/basic.lean




## [2021-11-10 06:43:42](https://github.com/leanprover-community/mathlib/commit/18412ef)
feat(data/nat/cast): Cast of natural division is less than division of casts ([#10251](https://github.com/leanprover-community/mathlib/pull/10251))
#### Estimated changes
Modified src/data/nat/cast.lean
- \+ *lemma* nat.cast_div_le



## [2021-11-10 02:49:27](https://github.com/leanprover-community/mathlib/commit/3f173e1)
feat(group_theory/complement): iff-lemmas for when bottom and top subgroups are complementary ([#10143](https://github.com/leanprover-community/mathlib/pull/10143))
Adds iff lemmas for when bottom and top subgroups are complementary.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *lemma* set.eq_singleton_iff_nonempty_unique_mem
- \+/\- *lemma* set.eq_singleton_iff_unique_mem
- \+ *lemma* set.exists_eq_singleton_iff_nonempty_unique_mem

Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.is_complement'_bot_left
- \+ *lemma* subgroup.is_complement'_bot_right
- \+ *lemma* subgroup.is_complement'_bot_top
- \+ *lemma* subgroup.is_complement'_top_bot
- \+ *lemma* subgroup.is_complement'_top_left
- \+ *lemma* subgroup.is_complement'_top_right
- \+ *lemma* subgroup.is_complement_singleton_left
- \+ *lemma* subgroup.is_complement_singleton_right
- \+/\- *lemma* subgroup.is_complement_singleton_top
- \+ *lemma* subgroup.is_complement_top_left
- \+ *lemma* subgroup.is_complement_top_right
- \+/\- *lemma* subgroup.is_complement_top_singleton

Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.coe_eq_singleton
- \+ *lemma* subgroup.coe_eq_univ



## [2021-11-09 23:52:35](https://github.com/leanprover-community/mathlib/commit/64289fe)
chore(group_theory/order_of_element): fix weird lemma name ([#10245](https://github.com/leanprover-community/mathlib/pull/10245))
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \- *lemma* pow_eq_one_of_lt_order_of'
- \+ *lemma* pow_ne_one_of_lt_order_of'



## [2021-11-09 23:52:33](https://github.com/leanprover-community/mathlib/commit/10d3d25)
chore(set_theory/cardinal): fix name & reorder universes ([#10236](https://github.com/leanprover-community/mathlib/pull/10236))
* add `cardinal.lift_injective`, `cardinal.lift_eq_zero`;
* reorder universe arguments in `cardinal.lift_nat_cast` to match
`cardinal.lift` and `ulift`;
* rename `cardinal.nat_eq_lift_eq_iff` to `cardinal.nat_eq_lift_iff`;
* add `@[simp]` to `cardinal.lift_eq_zero`,
`cardinal.lift_eq_nat_iff`, and `cardinal.nat_eq_lift_iff`.
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/matrix/to_lin.lean


Modified src/set_theory/cardinal.lean
- \+/\- *lemma* cardinal.lift_eq_nat_iff
- \+ *theorem* cardinal.lift_eq_zero
- \+ *theorem* cardinal.lift_injective
- \+/\- *theorem* cardinal.lift_nat_cast
- \- *lemma* cardinal.nat_eq_lift_eq_iff
- \+ *lemma* cardinal.nat_eq_lift_iff

Modified src/set_theory/cardinal_ordinal.lean




## [2021-11-09 23:52:32](https://github.com/leanprover-community/mathlib/commit/7bdb6b3)
feat(algebra/module/linear_map,linear_algebra/alternating,linear_algebra/multilinear/basic): no_zero_smul_divisors instances ([#10234](https://github.com/leanprover-community/mathlib/pull/10234))
Add `no_zero_smul_divisors` instances for linear, multilinear and alternating maps, given such instances for the codomain of the maps.
This also adds some missing `coe_smul` lemmas on these types.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* function.injective.no_zero_smul_divisors

Modified src/algebra/module/linear_map.lean
- \+ *lemma* linear_map.coe_smul

Modified src/linear_algebra/alternating.lean
- \+ *lemma* alternating_map.coe_fn_smul

Modified src/linear_algebra/multilinear/basic.lean
- \+ *lemma* multilinear_map.coe_smul



## [2021-11-09 17:02:26](https://github.com/leanprover-community/mathlib/commit/a2810d9)
feat(data/int/basic): coercion subtraction inequality ([#10054](https://github.com/leanprover-community/mathlib/pull/10054))
Adding to simp a subtraction inequality over coercion from int to nat
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.le_coe_nat_sub



## [2021-11-09 14:26:32](https://github.com/leanprover-community/mathlib/commit/35d574e)
feat(linear_algebra/determinant): alternating maps as multiples of determinant ([#10233](https://github.com/leanprover-community/mathlib/pull/10233))
Add the lemma that any alternating map with the same type as the
determinant map with respect to a basis is a multiple of the
determinant map (given by the value of the alternating map applied to
the basis vectors).
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* alternating_map.map_eq_zero_of_not_injective
- \+ *lemma* basis.ext_alternating

Modified src/linear_algebra/determinant.lean
- \+ *lemma* alternating_map.eq_smul_basis_det



## [2021-11-09 10:46:44](https://github.com/leanprover-community/mathlib/commit/00d9b9f)
feast(ring_theory/norm): add norm_eq_prod_embeddings ([#10226](https://github.com/leanprover-community/mathlib/pull/10226))
We prove that the norm equals the product of the embeddings in an algebraically closed field.
Note that we follow a slightly different path than for the trace, since transitivity of the norm is more delicate, and we avoid it.
From flt-regular.
#### Estimated changes
Modified src/ring_theory/norm.lean
- \+ *lemma* algebra.norm_eq_norm_adjoin
- \+ *lemma* algebra.norm_eq_prod_embeddings
- \+ *lemma* algebra.norm_eq_prod_embeddings_gen
- \+ *lemma* algebra.prod_embeddings_eq_finrank_pow



## [2021-11-09 09:20:22](https://github.com/leanprover-community/mathlib/commit/11ced18)
feat(algebra/lie/classical): Use computable matrix inverses where possible ([#10218](https://github.com/leanprover-community/mathlib/pull/10218))
#### Estimated changes
Modified src/algebra/lie/classical.lean
- \+/\- *lemma* lie_algebra.orthogonal.PB_inv
- \+ *def* lie_algebra.orthogonal.invertible_Pso
- \- *lemma* lie_algebra.orthogonal.is_unit_PB
- \- *lemma* lie_algebra.orthogonal.is_unit_PD
- \- *lemma* lie_algebra.orthogonal.is_unit_Pso
- \+ *def* lie_algebra.orthogonal.so_indefinite_equiv
- \+ *def* lie_algebra.orthogonal.type_B_equiv_so'
- \+ *def* lie_algebra.orthogonal.type_D_equiv_so'

Modified src/algebra/lie/matrix.lean
- \+ *def* matrix.lie_conj
- \+/\- *lemma* matrix.lie_conj_apply
- \+/\- *lemma* matrix.lie_conj_symm_apply

Modified src/algebra/lie/skew_adjoint.lean
- \+ *def* skew_adjoint_matrices_lie_subalgebra_equiv

Modified src/linear_algebra/matrix/to_linear_equiv.lean
- \+ *def* matrix.to_linear_equiv'
- \+/\- *lemma* matrix.to_linear_equiv'_apply
- \+/\- *lemma* matrix.to_linear_equiv'_symm_apply



## [2021-11-09 09:20:21](https://github.com/leanprover-community/mathlib/commit/8614615)
refactor(data/nat/interval): simp for Ico_zero_eq_range ([#10211](https://github.com/leanprover-community/mathlib/pull/10211))
This PR makes two changes: It refactors `nat.Ico_zero_eq_range` from `Ico 0 a = range a` to `Ico 0 = range`, and makes the lemma a simp lemma.
These changes feel good to me, but feel free to close this if this is not the direction we want to go with this lemma.
#### Estimated changes
Modified src/algebra/big_operators/intervals.lean


Modified src/data/nat/interval.lean
- \+/\- *lemma* finset.range_eq_Ico
- \+/\- *lemma* nat.Ico_zero_eq_range

Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean




## [2021-11-09 07:29:49](https://github.com/leanprover-community/mathlib/commit/0b093e6)
feat(order/bounded_lattice): a couple of basic instances about with_bot still not having a top if the original preorder didn't and vice versa ([#10215](https://github.com/leanprover-community/mathlib/pull/10215))
Used in the flt-regular project.
#### Estimated changes
Modified src/order/bounded_lattice.lean




## [2021-11-09 03:25:48](https://github.com/leanprover-community/mathlib/commit/6af6f67)
chore(scripts): update nolints.txt ([#10240](https://github.com/leanprover-community/mathlib/pull/10240))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-11-09 03:25:47](https://github.com/leanprover-community/mathlib/commit/9d49c4a)
doc(data/finset/fold): fix typo ([#10239](https://github.com/leanprover-community/mathlib/pull/10239))
#### Estimated changes
Modified src/data/finset/fold.lean




## [2021-11-09 03:25:45](https://github.com/leanprover-community/mathlib/commit/223f659)
chore(linear_algebra/basic): remove a duplicate proof, generalize map_span_le ([#10219](https://github.com/leanprover-community/mathlib/pull/10219))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *lemma* submodule.map_span_le



## [2021-11-09 01:42:52](https://github.com/leanprover-community/mathlib/commit/424012a)
chore(*): bump to Lean 3.35.1 ([#10237](https://github.com/leanprover-community/mathlib/pull/10237))
#### Estimated changes
Modified leanpkg.toml




## [2021-11-08 22:17:41](https://github.com/leanprover-community/mathlib/commit/440163b)
chore(topology/algebra/mul_action): define `has_continuous_vadd` using `to_additive` ([#10227](https://github.com/leanprover-community/mathlib/pull/10227))
Make additive version of the theory of `has_continuous_smul`, i.e., `has_continuous_vadd`, using `to_additive`.  I've been fairly conservative in adding `to_additive` tags -- I left them off lemmas that didn't seem like they'd be relevant for typical additive actions, like those about `units` or `group_with_zero`.
Also make `normed_add_torsor` an instance of `has_continuous_vadd` and use this to establish some of its continuity API.
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean
- \- *lemma* continuous.vadd
- \- *lemma* continuous_at.vadd
- \- *lemma* continuous_vadd
- \- *lemma* continuous_within_at.vadd
- \- *lemma* filter.tendsto.vadd

Modified src/topology/algebra/mul_action.lean




## [2021-11-08 16:03:11](https://github.com/leanprover-community/mathlib/commit/2e4813d)
feat(linear_algebra/matrix/nonsingular_inverse): add invertible_equiv_det_invertible ([#10222](https://github.com/leanprover-community/mathlib/pull/10222))
#### Estimated changes
Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *def* matrix.invertible_equiv_det_invertible



## [2021-11-08 16:03:10](https://github.com/leanprover-community/mathlib/commit/1519cd7)
chore(set_theory/cardinal): more simp, fix LHS/RHS ([#10212](https://github.com/leanprover-community/mathlib/pull/10212))
While `coe (fintype.card α)` is a larger expression than `#α`, it allows us to compute the cardinality of a finite type provided that we have a `simp` lemma for `fintype.card α`. It also plays well with lemmas about coercions from `nat` and `cardinal.lift`.
* rename `cardinal.fintype_card` to `cardinal.mk_fintype`, make it a `@[simp]` lemma;
* deduce other cases (`bool`, `Prop`, `unique`, `is_empty`) from it;
* rename `cardinal.finset_card` to `cardinal.mk_finset`, swap LHS/RHS;
* rename `ordinal.fintype_card` to `ordinal.type_fintype`.
#### Estimated changes
Modified archive/100-theorems-list/16_abel_ruffini.lean


Modified archive/sensitivity.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_Prop
- \+ *lemma* fintype.induction_empty_option'

Modified src/field_theory/finite/polynomial.lean


Modified src/field_theory/finiteness.lean
- \+/\- *lemma* is_noetherian.dim_lt_omega
- \+/\- *lemma* is_noetherian.iff_dim_lt_omega

Modified src/field_theory/fixed.lean


Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* basis.finite_of_vector_space_index_of_dim_lt_omega

Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/free_module/finite/rank.lean


Modified src/linear_algebra/matrix/to_lin.lean


Modified src/set_theory/cardinal.lean
- \- *lemma* cardinal.finset_card
- \- *theorem* cardinal.fintype_card
- \+/\- *theorem* cardinal.mk_Prop
- \+/\- *theorem* cardinal.mk_bool
- \+/\- *lemma* cardinal.mk_eq_one
- \+/\- *lemma* cardinal.mk_eq_zero
- \+/\- *theorem* cardinal.mk_fin
- \+ *lemma* cardinal.mk_finset
- \+ *lemma* cardinal.mk_fintype
- \+/\- *lemma* cardinal.mk_to_nat_eq_card

Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.fintype_card
- \+ *theorem* ordinal.type_fintype



## [2021-11-08 16:03:09](https://github.com/leanprover-community/mathlib/commit/66dea29)
feat(analysis/convex/specific_functions): Strict convexity of `exp`, `log` and `pow` ([#10123](https://github.com/leanprover-community/mathlib/pull/10123))
This strictifies the results of convexity/concavity of `exp`/`log` and add the strict versions for `pow`, `zpow`, `rpow`.
I'm also renaming `convex_on_pow_of_even` to `even.convex_on_pow` for dot notation.
#### Estimated changes
Modified src/analysis/convex/specific_functions.lean
- \- *lemma* concave_on_log_Iio
- \- *lemma* concave_on_log_Ioi
- \+/\- *lemma* convex_on_exp
- \- *lemma* convex_on_pow_of_even
- \+ *lemma* even.convex_on_pow
- \+ *lemma* even.strict_convex_on_pow
- \+ *lemma* int_prod_range_pos
- \+ *lemma* strict_concave_on_log_Iio
- \+ *lemma* strict_concave_on_log_Ioi
- \+ *lemma* strict_convex_on_exp
- \+ *lemma* strict_convex_on_pow
- \+ *lemma* strict_convex_on_rpow
- \+ *lemma* strict_convex_on_zpow

Modified src/analysis/mean_inequalities.lean




## [2021-11-08 16:03:08](https://github.com/leanprover-community/mathlib/commit/ef68f55)
feat(linear_algebra/multilinear/basis): multilinear maps on basis vectors ([#10090](https://github.com/leanprover-community/mathlib/pull/10090))
Add two versions of the fact that a multilinear map on finitely many
arguments is determined by its values on basis vectors.  The precise
requirements for each version follow from the results used in the
proof: `basis.ext_multilinear_fin` uses the `curry` and `uncurry`
results to deduce it from `basis.ext` and thus works for multilinear
maps on a family of modules indexed by `fin n`, while
`basis.ext_multilinear` works for an arbitrary `fintype` index type
but is limited to the case where the modules for all the arguments
(and the bases used for those modules) are the same, since it's
derived from the previous result using `dom_dom_congr` which only
handles the case where all the modules are the same.
This is in preparation for proving a corresponding result for
alternating maps, for which the case of all argument modules the same
suffices.
There is probably room for making results more general.
#### Estimated changes
Modified src/linear_algebra/multilinear/basic.lean
- \+ *lemma* multilinear_map.dom_dom_congr_eq_iff

Added src/linear_algebra/multilinear/basis.lean
- \+ *lemma* basis.ext_multilinear
- \+ *lemma* basis.ext_multilinear_fin



## [2021-11-08 14:15:15](https://github.com/leanprover-community/mathlib/commit/eb67834)
chore(ring_theory/noetherian): golf and generalize map_fg_of_fg ([#10217](https://github.com/leanprover-community/mathlib/pull/10217))
#### Estimated changes
Modified src/ring_theory/noetherian.lean
- \+/\- *lemma* submodule.map_fg_of_fg



## [2021-11-08 14:15:14](https://github.com/leanprover-community/mathlib/commit/5ba41d8)
feat(algebra/direct_sum): specialize `submodule_is_internal.independent` to add_subgroup ([#10108](https://github.com/leanprover-community/mathlib/pull/10108))
This adds the lemmas `disjoint.map_order_iso` and `complete_lattice.independent.map_order_iso` (and `iff` versions), and uses them to transfer some results on `submodule`s to `add_submonoid`s and `add_subgroup`s.
#### Estimated changes
Modified src/algebra/direct_sum/module.lean
- \+ *lemma* direct_sum.add_subgroup_is_internal.independent
- \+ *lemma* direct_sum.add_submonoid_is_internal.independent

Modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* complete_lattice.independent.dfinsupp_sum_add_hom_injective
- \+ *lemma* complete_lattice.independent_iff_dfinsupp_sum_add_hom_injective
- \+ *lemma* complete_lattice.independent_of_dfinsupp_sum_add_hom_injective'
- \+ *lemma* complete_lattice.independent_of_dfinsupp_sum_add_hom_injective

Modified src/order/complete_lattice.lean
- \+ *lemma* complete_lattice.independent.map_order_iso
- \+ *lemma* complete_lattice.independent_map_order_iso_iff

Modified src/order/rel_iso.lean
- \+ *lemma* disjoint.map_order_iso
- \+ *lemma* disjoint_map_order_iso_iff



## [2021-11-08 13:14:28](https://github.com/leanprover-community/mathlib/commit/0dabcb8)
chore(ring_theory/ideal/operations): relax the base ring of algebras from comm_ring to comm_semiring ([#10024](https://github.com/leanprover-community/mathlib/pull/10024))
This also tidies up some variables and consistently uses `B` instead of `S` for the second algebra.
One proof in `ring_theory/finiteness.lean` has to be redone because typeclass search times out where it previously did not.
Thankfully, the new proof is shorter anyway.
#### Estimated changes
Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* ideal.algebra_map_quotient_injective
- \+/\- *lemma* ideal.ker_lift.map_smul
- \+/\- *def* ideal.ker_lift_alg
- \+/\- *lemma* ideal.ker_lift_alg_injective
- \+/\- *lemma* ideal.ker_lift_alg_mk
- \+/\- *lemma* ideal.ker_lift_alg_to_ring_hom
- \+/\- *lemma* ideal.quotient.mk_algebra_map
- \+/\- *def* ideal.quotient.mkₐ
- \+/\- *lemma* ideal.quotient.mkₐ_ker
- \+/\- *lemma* ideal.quotient.mkₐ_surjective
- \+/\- *def* ideal.quotient_equiv_alg
- \+/\- *lemma* ideal.quotient_ker_alg_equiv_of_right_inverse.apply
- \+/\- *lemma* ideal.quotient_ker_alg_equiv_of_right_inverse_symm.apply
- \+/\- *lemma* ideal.quotient_map_comp_mkₐ
- \+/\- *lemma* ideal.quotient_map_mkₐ
- \+/\- *def* ideal.quotient_mapₐ



## [2021-11-08 11:43:24](https://github.com/leanprover-community/mathlib/commit/b4a5b01)
feat(data/finset/basic): add card_insert_eq_ite ([#10209](https://github.com/leanprover-community/mathlib/pull/10209))
Adds the lemma `card_insert_eq_ite` combining the functionality of `card_insert_of_not_mem` and `card_insert_of_mem`, analogous to how `card_erase_eq_ite`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* finset.card_insert_eq_ite



## [2021-11-08 11:43:23](https://github.com/leanprover-community/mathlib/commit/2fd6a77)
chore(algebra/algebra/basic): add `algebra.coe_linear_map` ([#10204](https://github.com/leanprover-community/mathlib/pull/10204))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra.coe_linear_map



## [2021-11-08 11:43:20](https://github.com/leanprover-community/mathlib/commit/4dd7eca)
feat(analysis/{seminorm, convex/specific_functions}): A seminorm is convex ([#10203](https://github.com/leanprover-community/mathlib/pull/10203))
This proves `seminorm.convex_on`, `convex_on_norm` (which is morally a special case of the former) and leverages it to golf `seminorm.convex_ball`.
This also fixes the explicitness of arguments of `convex_on.translate_left` and friends.
#### Estimated changes
Modified src/analysis/convex/function.lean
- \+/\- *lemma* concave_on.translate_left
- \+/\- *lemma* concave_on.translate_right
- \+/\- *lemma* convex_on.translate_left
- \+/\- *lemma* convex_on.translate_right
- \+/\- *lemma* strict_concave_on.translate_left
- \+/\- *lemma* strict_concave_on.translate_right
- \+/\- *lemma* strict_convex_on.translate_left
- \+/\- *lemma* strict_convex_on.translate_right

Modified src/analysis/convex/specific_functions.lean
- \+ *lemma* convex_on_norm

Modified src/analysis/seminorm.lean




## [2021-11-08 11:43:19](https://github.com/leanprover-community/mathlib/commit/e44aa6e)
feat(linear_algebra/basic): some lemmas about span and restrict_scalars ([#10167](https://github.com/leanprover-community/mathlib/pull/10167))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* submodule.span_le_restrict_scalars

Modified src/algebra/module/submodule.lean
- \+ *lemma* submodule.coe_restrict_scalars
- \+/\- *lemma* submodule.restrict_scalars_mem
- \+ *lemma* submodule.restrict_scalars_self

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.span_coe_eq_restrict_scalars
- \+/\- *lemma* submodule.span_eq
- \+ *lemma* submodule.span_le_restrict_scalars
- \+ *lemma* submodule.span_span_of_tower
- \+ *lemma* submodule.span_subset_span

Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/pi.lean


Modified src/ring_theory/finiteness.lean




## [2021-11-08 11:43:18](https://github.com/leanprover-community/mathlib/commit/fb0cfbd)
feat(measure_theory/measure/complex): define complex measures ([#10166](https://github.com/leanprover-community/mathlib/pull/10166))
Complex measures was defined to be a vector measure over ℂ without any API. This PR adds some basic definitions about complex measures and proves the complex version of the Lebesgue decomposition theorem.
#### Estimated changes
Modified src/measure_theory/decomposition/lebesgue.lean
- \+ *lemma* measure_theory.complex_measure.integrable_rn_deriv
- \+ *def* measure_theory.complex_measure.rn_deriv
- \+ *def* measure_theory.complex_measure.singular_part
- \+ *theorem* measure_theory.complex_measure.singular_part_add_with_density_rn_deriv_eq
- \+/\- *lemma* measure_theory.signed_measure.singular_part_smul

Added src/measure_theory/measure/complex.lean
- \+ *lemma* measure_theory.complex_measure.absolutely_continuous_ennreal_iff
- \+ *def* measure_theory.complex_measure.equiv_signed_measure
- \+ *def* measure_theory.complex_measure.equiv_signed_measureₗ
- \+ *def* measure_theory.complex_measure.im
- \+ *def* measure_theory.complex_measure.re
- \+ *lemma* measure_theory.complex_measure.to_complex_measure_to_signed_measure
- \+ *lemma* measure_theory.signed_measure.im_to_complex_measure
- \+ *lemma* measure_theory.signed_measure.re_to_complex_measure
- \+ *def* measure_theory.signed_measure.to_complex_measure
- \+ *lemma* measure_theory.signed_measure.to_complex_measure_apply

Modified src/measure_theory/measure/vector_measure.lean
- \+ *def* measure_theory.vector_measure.map_range
- \+ *lemma* measure_theory.vector_measure.map_range_add
- \+ *lemma* measure_theory.vector_measure.map_range_apply
- \+ *def* measure_theory.vector_measure.map_range_hom
- \+ *lemma* measure_theory.vector_measure.map_range_id
- \+ *lemma* measure_theory.vector_measure.map_range_zero
- \+ *def* measure_theory.vector_measure.map_rangeₗ



## [2021-11-08 11:43:17](https://github.com/leanprover-community/mathlib/commit/e4a1e80)
feat(analysis/convex/combination): Convex hull of a `set.prod` and `set.pi` ([#10125](https://github.com/leanprover-community/mathlib/pull/10125))
This proves
* `(∀ i, convex 𝕜 (t i)) → convex 𝕜 (s.pi t)`
* `convex_hull 𝕜 (s.prod t) = (convex_hull 𝕜 s).prod (convex_hull 𝕜 t)`
* `convex_hull 𝕜 (s.pi t) = s.pi (convex_hull 𝕜 ∘ t)`
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex_pi

Modified src/analysis/convex/combination.lean
- \+ *lemma* convex_hull_prod



## [2021-11-08 11:43:16](https://github.com/leanprover-community/mathlib/commit/1fac00e)
feat(analysis): lemmas about `arg` and `exp_map_circle` ([#10066](https://github.com/leanprover-community/mathlib/pull/10066))
#### Estimated changes
Modified src/analysis/complex/circle.lean
- \+ *lemma* exp_map_circle_sub

Added src/analysis/special_functions/complex/circle.lean
- \+ *lemma* arg_exp_map_circle
- \+ *lemma* circle.arg_eq_arg
- \+ *lemma* circle.injective_arg
- \+ *lemma* exp_map_circle_add_two_pi
- \+ *lemma* exp_map_circle_arg
- \+ *lemma* exp_map_circle_eq_exp_map_circle
- \+ *lemma* exp_map_circle_sub_two_pi
- \+ *lemma* exp_map_circle_two_pi
- \+ *lemma* inv_on_arg_exp_map_circle
- \+ *lemma* left_inverse_exp_map_circle_arg
- \+ *lemma* periodic_exp_map_circle
- \+ *lemma* surj_on_exp_map_circle_neg_pi_pi



## [2021-11-08 11:43:15](https://github.com/leanprover-community/mathlib/commit/48abaed)
feat(analysis/special_functions/complex/arg): continuity of arg outside of the negative real half-line ([#9500](https://github.com/leanprover-community/mathlib/pull/9500))
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* complex.arg_eq_nhds_of_re_neg_of_im_neg
- \+ *lemma* complex.arg_eq_nhds_of_re_neg_of_im_pos
- \+ *lemma* complex.arg_eq_nhds_of_re_pos
- \+ *lemma* complex.arg_of_re_neg_of_im_neg
- \+ *lemma* complex.arg_of_re_neg_of_im_nonneg
- \+ *lemma* complex.arg_of_re_nonneg
- \+ *lemma* complex.arg_of_re_zero_of_im_neg
- \+ *lemma* complex.arg_of_re_zero_of_im_pos
- \+ *lemma* complex.continuous_at_arg
- \+ *lemma* complex.continuous_at_arg_of_re_neg_of_im_neg
- \+ *lemma* complex.continuous_at_arg_of_re_neg_of_im_pos
- \+ *lemma* complex.continuous_at_arg_of_re_pos
- \+ *lemma* complex.continuous_at_arg_of_re_zero



## [2021-11-08 10:06:42](https://github.com/leanprover-community/mathlib/commit/32c8445)
split(data/list/*): split off `data.list.basic` ([#10164](https://github.com/leanprover-community/mathlib/pull/10164))
Killing the giants. This moves 700 lines off `data.list.basic` that were about
* `list.sum` and `list.product` into `data.list.big_operators`
* `list.countp` and `list.count` into `data.list.count`
* `list.sigma` and `list.prod` into `data.list.sigma_prod`
#### Estimated changes
Modified src/computability/language.lean


Modified src/computability/primrec.lean


Modified src/data/fin_enum.lean


Modified src/data/hash_map.lean


Modified src/data/list/basic.lean
- \- *lemma* list.all_one_of_le_one_le_of_prod_eq_one
- \- *lemma* list.alternating_prod_cons_cons
- \- *lemma* list.alternating_prod_nil
- \- *lemma* list.alternating_prod_singleton
- \- *lemma* list.alternating_sum_cons_cons
- \- *theorem* list.count_append
- \- *lemma* list.count_bind
- \- *theorem* list.count_concat
- \- *theorem* list.count_cons'
- \- *theorem* list.count_cons
- \- *theorem* list.count_cons_of_ne
- \- *theorem* list.count_cons_self
- \- *theorem* list.count_eq_zero_of_not_mem
- \- *theorem* list.count_erase_of_ne
- \- *theorem* list.count_erase_self
- \- *theorem* list.count_filter
- \- *theorem* list.count_le_count_cons
- \- *theorem* list.count_le_of_sublist
- \- *lemma* list.count_map_map
- \- *theorem* list.count_nil
- \- *theorem* list.count_pos
- \- *theorem* list.count_repeat
- \- *theorem* list.count_singleton
- \- *theorem* list.count_tail
- \- *theorem* list.countp_append
- \- *theorem* list.countp_cons_of_neg
- \- *theorem* list.countp_cons_of_pos
- \- *theorem* list.countp_eq_length_filter
- \- *theorem* list.countp_filter
- \- *theorem* list.countp_le_of_sublist
- \- *theorem* list.countp_nil
- \- *theorem* list.countp_pos
- \- *lemma* list.drop_sum_join
- \- *lemma* list.drop_take_succ_eq_cons_nth_le
- \- *lemma* list.drop_take_succ_join_eq_nth_le
- \- *lemma* list.dvd_prod
- \- *theorem* list.dvd_sum
- \- *theorem* list.eq_iff_join_eq
- \- *lemma* list.eq_of_sum_take_eq
- \- *lemma* list.exists_le_of_sum_le
- \- *lemma* list.exists_lt_of_sum_lt
- \- *lemma* list.head_add_tail_sum
- \- *lemma* list.head_le_sum
- \- *lemma* list.head_mul_tail_prod_of_ne_nil
- \- *theorem* list.join_append
- \- *theorem* list.join_eq_nil
- \- *theorem* list.join_filter_empty_eq_ff
- \- *theorem* list.join_filter_ne_nil
- \- *lemma* list.join_join
- \- *lemma* list.join_nil
- \- *theorem* list.le_count_iff_repeat_sublist
- \- *theorem* list.length_bind
- \- *theorem* list.length_eq_countp_add_countp
- \- *theorem* list.length_filter_lt_length_iff_exists
- \- *theorem* list.length_join
- \- *lemma* list.length_le_sum_of_one_le
- \- *lemma* list.length_pos_of_prod_ne_one
- \- *lemma* list.length_pos_of_sum_pos
- \- *theorem* list.length_product
- \- *theorem* list.length_sigma
- \+/\- *theorem* list.mem_map_swap
- \- *theorem* list.mem_product
- \- *theorem* list.mem_sigma
- \- *lemma* list.monotone_sum_take
- \- *theorem* list.nil_product
- \- *theorem* list.nil_sigma
- \- *theorem* list.not_mem_of_count_eq_zero
- \- *lemma* list.nth_le_join
- \- *lemma* list.nth_zero_mul_tail_prod
- \- *lemma* list.one_le_prod_of_one_le
- \- *theorem* list.prod_append
- \- *theorem* list.prod_concat
- \- *theorem* list.prod_cons
- \- *lemma* list.prod_drop_succ
- \- *theorem* list.prod_eq_foldr
- \- *theorem* list.prod_eq_zero
- \- *theorem* list.prod_eq_zero_iff
- \- *theorem* list.prod_erase
- \- *theorem* list.prod_hom
- \- *theorem* list.prod_hom_rel
- \- *lemma* list.prod_inv
- \- *lemma* list.prod_inv_reverse
- \- *lemma* list.prod_is_unit
- \- *theorem* list.prod_join
- \- *theorem* list.prod_map_hom
- \- *theorem* list.prod_ne_zero
- \- *theorem* list.prod_nil
- \- *lemma* list.prod_pos
- \- *lemma* list.prod_reverse_noncomm
- \- *theorem* list.prod_singleton
- \- *lemma* list.prod_take_mul_prod_drop
- \- *lemma* list.prod_take_succ
- \- *lemma* list.prod_update_nth'
- \- *lemma* list.prod_update_nth
- \- *theorem* list.product_cons
- \- *theorem* list.product_nil
- \- *theorem* list.repeat_count_eq_of_count_eq_length
- \- *theorem* list.sigma_cons
- \- *theorem* list.sigma_nil
- \- *lemma* list.single_le_prod
- \+/\- *lemma* list.sizeof_slice_lt
- \+/\- *lemma* list.slice_eq
- \- *theorem* list.sum_const_nat
- \- *lemma* list.sum_eq_zero_iff
- \- *lemma* list.sum_le_foldr_max
- \- *theorem* list.sum_map_mul_left
- \- *theorem* list.sum_map_mul_right
- \- *lemma* list.sum_take_map_length_lt1
- \- *lemma* list.sum_take_map_length_lt2
- \- *lemma* list.tail_sum
- \- *lemma* list.take_sum_join
- \- *theorem* monoid_hom.map_list_prod
- \- *lemma* monoid_hom.unop_map_list_prod
- \- *lemma* opposite.op_list_prod
- \- *lemma* opposite.unop_list_prod

Added src/data/list/big_operators.lean
- \+ *lemma* list.all_one_of_le_one_le_of_prod_eq_one
- \+ *lemma* list.alternating_prod_cons_cons
- \+ *lemma* list.alternating_prod_nil
- \+ *lemma* list.alternating_prod_singleton
- \+ *lemma* list.alternating_sum_cons_cons
- \+ *lemma* list.dvd_prod
- \+ *lemma* list.dvd_sum
- \+ *lemma* list.eq_of_sum_take_eq
- \+ *lemma* list.exists_le_of_sum_le
- \+ *lemma* list.exists_lt_of_sum_lt
- \+ *lemma* list.head_add_tail_sum
- \+ *lemma* list.head_le_sum
- \+ *lemma* list.head_mul_tail_prod_of_ne_nil
- \+ *lemma* list.length_le_sum_of_one_le
- \+ *lemma* list.length_pos_of_prod_ne_one
- \+ *lemma* list.length_pos_of_sum_pos
- \+ *lemma* list.monotone_sum_take
- \+ *lemma* list.nth_zero_mul_tail_prod
- \+ *lemma* list.one_le_prod_of_one_le
- \+ *lemma* list.prod_append
- \+ *lemma* list.prod_concat
- \+ *lemma* list.prod_cons
- \+ *lemma* list.prod_drop_succ
- \+ *lemma* list.prod_eq_foldr
- \+ *lemma* list.prod_eq_zero
- \+ *lemma* list.prod_eq_zero_iff
- \+ *lemma* list.prod_erase
- \+ *lemma* list.prod_hom
- \+ *lemma* list.prod_hom_rel
- \+ *lemma* list.prod_inv
- \+ *lemma* list.prod_inv_reverse
- \+ *lemma* list.prod_is_unit
- \+ *lemma* list.prod_join
- \+ *lemma* list.prod_map_hom
- \+ *lemma* list.prod_ne_zero
- \+ *lemma* list.prod_nil
- \+ *lemma* list.prod_pos
- \+ *lemma* list.prod_reverse_noncomm
- \+ *lemma* list.prod_singleton
- \+ *lemma* list.prod_take_mul_prod_drop
- \+ *lemma* list.prod_take_succ
- \+ *lemma* list.prod_update_nth'
- \+ *lemma* list.prod_update_nth
- \+ *lemma* list.single_le_prod
- \+ *lemma* list.sum_const_nat
- \+ *lemma* list.sum_eq_zero_iff
- \+ *lemma* list.sum_le_foldr_max
- \+ *lemma* list.sum_map_mul_left
- \+ *lemma* list.sum_map_mul_right
- \+ *lemma* list.tail_sum
- \+ *lemma* monoid_hom.map_list_prod
- \+ *lemma* monoid_hom.unop_map_list_prod
- \+ *lemma* opposite.op_list_prod
- \+ *lemma* opposite.unop_list_prod

Added src/data/list/count.lean
- \+ *lemma* list.count_append
- \+ *lemma* list.count_bind
- \+ *lemma* list.count_concat
- \+ *lemma* list.count_cons'
- \+ *lemma* list.count_cons
- \+ *lemma* list.count_cons_of_ne
- \+ *lemma* list.count_cons_self
- \+ *lemma* list.count_eq_zero_of_not_mem
- \+ *lemma* list.count_erase_of_ne
- \+ *lemma* list.count_erase_self
- \+ *lemma* list.count_filter
- \+ *lemma* list.count_le_count_cons
- \+ *lemma* list.count_map_map
- \+ *lemma* list.count_nil
- \+ *lemma* list.count_pos
- \+ *lemma* list.count_repeat
- \+ *lemma* list.count_singleton
- \+ *lemma* list.count_tail
- \+ *lemma* list.countp_append
- \+ *lemma* list.countp_cons_of_neg
- \+ *lemma* list.countp_cons_of_pos
- \+ *lemma* list.countp_eq_length_filter
- \+ *lemma* list.countp_filter
- \+ *lemma* list.countp_nil
- \+ *lemma* list.countp_pos
- \+ *lemma* list.le_count_iff_repeat_sublist
- \+ *lemma* list.length_eq_countp_add_countp
- \+ *lemma* list.length_filter_lt_length_iff_exists
- \+ *lemma* list.not_mem_of_count_eq_zero
- \+ *lemma* list.repeat_count_eq_of_count_eq_length
- \+ *lemma* list.sublist.count_le
- \+ *lemma* list.sublist.countp_le

Added src/data/list/join.lean
- \+ *lemma* list.drop_sum_join
- \+ *lemma* list.drop_take_succ_eq_cons_nth_le
- \+ *lemma* list.drop_take_succ_join_eq_nth_le
- \+ *theorem* list.eq_iff_join_eq
- \+ *lemma* list.join_append
- \+ *lemma* list.join_eq_nil
- \+ *lemma* list.join_filter_empty_eq_ff
- \+ *lemma* list.join_filter_ne_nil
- \+ *lemma* list.join_join
- \+ *lemma* list.join_nil
- \+ *lemma* list.length_bind
- \+ *lemma* list.length_join
- \+ *lemma* list.nth_le_join
- \+ *lemma* list.sum_take_map_length_lt1
- \+ *lemma* list.sum_take_map_length_lt2
- \+ *lemma* list.take_sum_join

Modified src/data/list/lattice.lean


Modified src/data/list/pairwise.lean


Modified src/data/list/perm.lean


Modified src/data/list/permutation.lean


Modified src/data/list/prod_monoid.lean


Added src/data/list/prod_sigma.lean
- \+ *lemma* list.length_product
- \+ *lemma* list.length_sigma
- \+ *lemma* list.mem_product
- \+ *lemma* list.mem_sigma
- \+ *lemma* list.nil_product
- \+ *lemma* list.nil_sigma
- \+ *lemma* list.product_cons
- \+ *lemma* list.product_nil
- \+ *lemma* list.sigma_cons
- \+ *lemma* list.sigma_nil

Modified src/data/list/zip.lean


Modified src/data/multiset/basic.lean


Modified src/tactic/omega/int/dnf.lean


Modified src/tactic/omega/nat/dnf.lean




## [2021-11-08 08:27:27](https://github.com/leanprover-community/mathlib/commit/380d6ca)
chore(algebra/direct_sum/module): extract out common `variables` ([#10207](https://github.com/leanprover-community/mathlib/pull/10207))
Slight reorganization to extract out repeatedly-used variable declarations, and update module docstring.  No changes to the content.
#### Estimated changes
Modified src/algebra/direct_sum/module.lean
- \+/\- *def* direct_sum.submodule_coe
- \+/\- *lemma* direct_sum.submodule_coe_of
- \+/\- *lemma* direct_sum.submodule_is_internal.independent
- \+/\- *lemma* direct_sum.submodule_is_internal.supr_eq_top
- \+/\- *lemma* direct_sum.submodule_is_internal.to_add_subgroup
- \+/\- *lemma* direct_sum.submodule_is_internal.to_add_submonoid
- \+/\- *def* direct_sum.submodule_is_internal
- \+/\- *lemma* direct_sum.submodule_is_internal_iff_independent_and_supr_eq_top
- \+/\- *lemma* direct_sum.submodule_is_internal_of_independent_of_supr_eq_top



## [2021-11-08 08:27:25](https://github.com/leanprover-community/mathlib/commit/bf242b7)
feat(algebra/order/with_zero): add le lemmas ([#10183](https://github.com/leanprover-community/mathlib/pull/10183))
#### Estimated changes
Modified src/algebra/order/with_zero.lean
- \+ *lemma* div_le_div_right₀
- \+ *lemma* div_le_iff₀
- \+ *lemma* le_div_iff₀
- \+ *lemma* le_mul_inv_iff₀
- \+ *lemma* mul_inv_le_iff₀
- \+ *lemma* mul_le_mul_right₀



## [2021-11-08 08:27:23](https://github.com/leanprover-community/mathlib/commit/e0aa9f0)
refactor(linear_algebra/matrix/nonsingular_inverse): clean up ([#10175](https://github.com/leanprover-community/mathlib/pull/10175))
This file is a mess, and switches back and forth between three different inverses, proving the same things over and over again.
This pulls all the `invertible` versions of these statements to the top, and uses them here and there to golf proofs.
The lemmas `nonsing_inv_left_right` and `nonsing_inv_right_left` are merged into a single lemma `mul_eq_one_comm`.
The lemma `inv_eq_nonsing_inv_of_invertible` has been renamed to `inv_of_eq_nonsing_inv`
This also adds two new lemmas `inv_of_eq` and `det_inv_of`, both of which have trivial proofs.
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *lemma* ring.inverse_invertible

Modified src/algebra/lie/classical.lean


Modified src/linear_algebra/general_linear_group.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.det_inv_of
- \- *lemma* matrix.inv_eq_nonsing_inv_of_invertible
- \+ *lemma* matrix.inv_of_eq
- \+ *lemma* matrix.inv_of_eq_nonsing_inv
- \+/\- *def* matrix.invertible_of_left_inverse
- \+/\- *def* matrix.invertible_of_right_inverse
- \+/\- *lemma* matrix.left_inv_eq_left_inv
- \+ *lemma* matrix.mul_eq_one_comm
- \- *lemma* matrix.nonsing_inv_left_right
- \- *lemma* matrix.nonsing_inv_right_left
- \+/\- *lemma* matrix.right_inv_eq_left_inv
- \+/\- *lemma* matrix.right_inv_eq_right_inv

Modified src/linear_algebra/unitary_group.lean




## [2021-11-08 08:27:21](https://github.com/leanprover-community/mathlib/commit/bc55cd7)
feat(archive/imo) : Add solution to IMO 1994 Q1 ([#10171](https://github.com/leanprover-community/mathlib/pull/10171))
IMO 1994 Q1
#### Estimated changes
Added archive/imo/imo1994_q1.lean
- \+ *theorem* imo1994_q1
- \+ *lemma* tedious



## [2021-11-08 08:27:20](https://github.com/leanprover-community/mathlib/commit/62f94ad)
feat(measure_theory/measurable_space): define `measurable_embedding` ([#10023](https://github.com/leanprover-community/mathlib/pull/10023))
This way we can generalize our theorems about `measurable_equiv` and `closed_embedding`s.
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* set.range_extend
- \+ *lemma* set.range_extend_subset

Modified src/measure_theory/constructions/borel_space.lean
- \- *lemma* ae_measurable_comp_iff_of_closed_embedding
- \- *lemma* ae_measurable_comp_right_iff_of_closed_embedding
- \- *lemma* closed_embedding.measurable_inv_fun
- \- *lemma* measurable_comp_iff_of_closed_embedding

Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measurable_embedding.integrable_map_iff

Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* closed_embedding.integral_map
- \+ *lemma* measurable_embedding.integral_map
- \- *lemma* measure_theory.integral_map_of_closed_embedding

Modified src/measure_theory/integral/integrable_on.lean
- \+ *lemma* measurable_embedding.integrable_on_map_iff

Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measurable_embedding.lintegral_map
- \+ *def* measure_theory.simple_func.extend
- \+ *lemma* measure_theory.simple_func.extend_apply
- \+ *lemma* measure_theory.simple_func.extend_comp_eq'
- \+ *lemma* measure_theory.simple_func.extend_comp_eq
- \+ *lemma* measure_theory.simple_func.lintegral_map'
- \+/\- *lemma* measure_theory.simple_func.lintegral_map
- \- *lemma* measure_theory.simple_func.lintegral_map_equiv

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* closed_embedding.set_integral_map
- \+ *lemma* measurable_embedding.set_integral_map
- \- *lemma* measure_theory.set_integral_map_of_closed_embedding

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable.dite
- \+ *lemma* measurable_embedding.comp
- \+ *lemma* measurable_embedding.exists_measurable_extend
- \+ *lemma* measurable_embedding.id
- \+ *lemma* measurable_embedding.measurable_comp_iff
- \+ *lemma* measurable_embedding.measurable_extend
- \+ *lemma* measurable_embedding.measurable_range_splitting
- \+ *lemma* measurable_embedding.measurable_set_image
- \+ *lemma* measurable_embedding.measurable_set_preimage
- \+ *lemma* measurable_embedding.measurable_set_range
- \+ *lemma* measurable_embedding.of_measurable_inverse
- \+ *lemma* measurable_embedding.of_measurable_inverse_on_range
- \+ *lemma* measurable_embedding.subtype_coe
- \+ *structure* measurable_embedding
- \+ *theorem* measurable_equiv.image_eq_preimage
- \+ *theorem* measurable_equiv.measurable_set_image
- \+ *theorem* measurable_equiv.measurable_set_preimage
- \+ *theorem* measurable_equiv.symm_preimage_preimage
- \+ *lemma* measurable_of_restrict_of_restrict_compl
- \+ *lemma* measurable_set.exists_measurable_proj

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* ae_measurable.subtype_mk
- \+ *lemma* ae_measurable_restrict_iff_comap_subtype
- \+ *lemma* ae_restrict_iff_subtype
- \+ *lemma* comap_subtype_coe_apply
- \+ *lemma* map_comap_subtype_coe
- \+ *lemma* measurable_embedding.ae_map_iff
- \+ *lemma* measurable_embedding.ae_measurable_comp_iff
- \+ *lemma* measurable_embedding.ae_measurable_map_iff
- \+ *lemma* measurable_embedding.comap_apply
- \+ *theorem* measurable_embedding.map_apply
- \+ *lemma* measurable_embedding.map_comap
- \+ *lemma* measurable_embedding.restrict_map
- \+ *lemma* measurable_set.map_coe_volume
- \- *lemma* measure_theory.measure.map_comap_subtype_coe
- \+ *lemma* volume_image_subtype_coe
- \+ *lemma* volume_set_coe_def



## [2021-11-08 06:58:20](https://github.com/leanprover-community/mathlib/commit/c50c2c3)
docs(algebra/big_operators): correct documentation for prod ([#10206](https://github.com/leanprover-community/mathlib/pull/10206))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean




## [2021-11-07 10:12:36](https://github.com/leanprover-community/mathlib/commit/ae98aad)
chore(measure_theory/measure): review API of `mutually_singular` ([#10186](https://github.com/leanprover-community/mathlib/pull/10186))
#### Estimated changes
Modified src/measure_theory/decomposition/jordan.lean


Modified src/measure_theory/decomposition/lebesgue.lean
- \- *def* measure_theory.signed_measure.singular_part(s
- \+ *def* measure_theory.signed_measure.singular_part

Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \- *lemma* measure_theory.measure.mutually_singular.add
- \- *lemma* measure_theory.measure.mutually_singular.add_iff
- \+ *lemma* measure_theory.measure.mutually_singular.add_left
- \+ *lemma* measure_theory.measure.mutually_singular.add_left_iff
- \+ *lemma* measure_theory.measure.mutually_singular.add_right
- \+ *lemma* measure_theory.measure.mutually_singular.add_right_iff
- \+ *lemma* measure_theory.measure.mutually_singular.comm
- \+ *lemma* measure_theory.measure.mutually_singular.mk
- \+ *lemma* measure_theory.measure.mutually_singular.mono
- \+ *lemma* measure_theory.measure.mutually_singular.mono_ac
- \- *lemma* measure_theory.measure.mutually_singular.of_absolutely_continuous
- \+/\- *lemma* measure_theory.measure.mutually_singular.smul
- \+ *lemma* measure_theory.measure.mutually_singular.smul_nnreal
- \+ *lemma* measure_theory.measure.mutually_singular.sum_left
- \+ *lemma* measure_theory.measure.mutually_singular.sum_right
- \+/\- *lemma* measure_theory.measure.mutually_singular.symm
- \+/\- *lemma* measure_theory.measure.mutually_singular.zero_left
- \+/\- *lemma* measure_theory.measure.mutually_singular.zero_right
- \+ *lemma* measure_theory.measure.sum_of_empty

Modified src/topology/instances/ennreal.lean




## [2021-11-07 09:34:49](https://github.com/leanprover-community/mathlib/commit/7a8a914)
refactor(measure_theory/function/l1_space): remove hypothesis ([#10185](https://github.com/leanprover-community/mathlib/pull/10185))
* from `tendsto_lintegral_norm_of_dominated_convergence`
* Missed this in [#10181](https://github.com/leanprover-community/mathlib/pull/10181)
* Add comment about the ability to weaker `bound_integrable`.
#### Estimated changes
Modified src/measure_theory/function/l1_space.lean


Modified src/measure_theory/integral/bochner.lean




## [2021-11-07 05:17:04](https://github.com/leanprover-community/mathlib/commit/7d240ce)
chore(data/matrix/notation): split into 2 files ([#10199](https://github.com/leanprover-community/mathlib/pull/10199))
I want to use `![a, b]` notation in some files that don't need to import `data.matrix.basic`.
#### Estimated changes
Modified src/data/complex/module.lean


Added src/data/fin/vec_notation.lean
- \+ *lemma* matrix.add_cons
- \+ *lemma* matrix.cons_add
- \+ *lemma* matrix.cons_append
- \+ *lemma* matrix.cons_eq_zero_iff
- \+ *lemma* matrix.cons_fin_one
- \+ *lemma* matrix.cons_head_tail
- \+ *lemma* matrix.cons_nonzero_iff
- \+ *lemma* matrix.cons_sub
- \+ *lemma* matrix.cons_val_fin_one
- \+ *lemma* matrix.cons_val_one
- \+ *lemma* matrix.cons_val_succ'
- \+ *lemma* matrix.cons_val_succ
- \+ *lemma* matrix.cons_val_zero'
- \+ *lemma* matrix.cons_val_zero
- \+ *lemma* matrix.cons_vec_alt0
- \+ *lemma* matrix.cons_vec_alt1
- \+ *lemma* matrix.cons_vec_bit0_eq_alt0
- \+ *lemma* matrix.cons_vec_bit1_eq_alt1
- \+ *lemma* matrix.cons_zero_zero
- \+ *lemma* matrix.empty_add_empty
- \+ *lemma* matrix.empty_append
- \+ *lemma* matrix.empty_eq
- \+ *lemma* matrix.empty_sub_empty
- \+ *lemma* matrix.empty_val'
- \+ *lemma* matrix.empty_vec_alt0
- \+ *lemma* matrix.empty_vec_alt1
- \+ *lemma* matrix.head_add
- \+ *lemma* matrix.head_cons
- \+ *lemma* matrix.head_fin_const
- \+ *lemma* matrix.head_neg
- \+ *lemma* matrix.head_sub
- \+ *lemma* matrix.head_zero
- \+ *lemma* matrix.neg_cons
- \+ *lemma* matrix.neg_empty
- \+ *lemma* matrix.range_cons
- \+ *lemma* matrix.range_empty
- \+ *lemma* matrix.smul_cons
- \+ *lemma* matrix.smul_empty
- \+ *lemma* matrix.sub_cons
- \+ *lemma* matrix.tail_add
- \+ *lemma* matrix.tail_cons
- \+ *lemma* matrix.tail_neg
- \+ *lemma* matrix.tail_sub
- \+ *lemma* matrix.tail_zero
- \+ *def* matrix.vec_alt0
- \+ *lemma* matrix.vec_alt0_append
- \+ *def* matrix.vec_alt1
- \+ *lemma* matrix.vec_alt1_append
- \+ *def* matrix.vec_cons
- \+ *lemma* matrix.vec_cons_const
- \+ *def* matrix.vec_empty
- \+ *def* matrix.vec_head
- \+ *lemma* matrix.vec_head_vec_alt0
- \+ *lemma* matrix.vec_head_vec_alt1
- \+ *lemma* matrix.vec_single_eq_const
- \+ *def* matrix.vec_tail
- \+ *lemma* matrix.zero_empty

Modified src/data/matrix/notation.lean
- \- *lemma* matrix.add_cons
- \- *lemma* matrix.cons_add
- \- *lemma* matrix.cons_append
- \- *lemma* matrix.cons_eq_zero_iff
- \- *lemma* matrix.cons_fin_one
- \- *lemma* matrix.cons_head_tail
- \- *lemma* matrix.cons_nonzero_iff
- \- *lemma* matrix.cons_sub
- \- *lemma* matrix.cons_val_fin_one
- \- *lemma* matrix.cons_val_one
- \- *lemma* matrix.cons_val_succ'
- \- *lemma* matrix.cons_val_succ
- \- *lemma* matrix.cons_val_zero'
- \- *lemma* matrix.cons_val_zero
- \- *lemma* matrix.cons_vec_alt0
- \- *lemma* matrix.cons_vec_alt1
- \- *lemma* matrix.cons_vec_bit0_eq_alt0
- \- *lemma* matrix.cons_vec_bit1_eq_alt1
- \- *lemma* matrix.cons_zero_zero
- \- *lemma* matrix.empty_add_empty
- \- *lemma* matrix.empty_append
- \- *lemma* matrix.empty_eq
- \- *lemma* matrix.empty_sub_empty
- \- *lemma* matrix.empty_val'
- \- *lemma* matrix.empty_vec_alt0
- \- *lemma* matrix.empty_vec_alt1
- \- *lemma* matrix.head_add
- \- *lemma* matrix.head_cons
- \- *lemma* matrix.head_fin_const
- \- *lemma* matrix.head_neg
- \- *lemma* matrix.head_sub
- \- *lemma* matrix.head_zero
- \- *lemma* matrix.neg_cons
- \- *lemma* matrix.neg_empty
- \- *lemma* matrix.range_cons
- \- *lemma* matrix.range_empty
- \- *lemma* matrix.smul_cons
- \- *lemma* matrix.smul_empty
- \- *lemma* matrix.sub_cons
- \- *lemma* matrix.tail_add
- \- *lemma* matrix.tail_cons
- \- *lemma* matrix.tail_neg
- \- *lemma* matrix.tail_sub
- \- *lemma* matrix.tail_zero
- \- *def* matrix.vec_alt0
- \- *lemma* matrix.vec_alt0_append
- \- *def* matrix.vec_alt1
- \- *lemma* matrix.vec_alt1_append
- \- *def* matrix.vec_cons
- \- *lemma* matrix.vec_cons_const
- \- *def* matrix.vec_empty
- \- *def* matrix.vec_head
- \- *lemma* matrix.vec_head_vec_alt0
- \- *lemma* matrix.vec_head_vec_alt1
- \- *lemma* matrix.vec_single_eq_const
- \- *def* matrix.vec_tail
- \- *lemma* matrix.zero_empty

Modified src/data/real/golden_ratio.lean


Modified src/group_theory/solvable.lean


Modified src/linear_algebra/affine_space/independent.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/ring_theory/witt_vector/structure_polynomial.lean




## [2021-11-06 22:22:28](https://github.com/leanprover-community/mathlib/commit/daac854)
feat(analysis/special_functions/log): Relating `log`-inequalities and `exp`-inequalities ([#10191](https://github.com/leanprover-community/mathlib/pull/10191))
This proves `log x ≤ y ↔ x ≤ exp y` and `x ≤ log y ↔ exp x ≤ y`.
#### Estimated changes
Modified src/analysis/special_functions/log.lean
- \+ *lemma* real.le_log_iff_exp_le
- \+ *lemma* real.log_le_iff_le_exp
- \+ *lemma* real.log_lt_iff_lt_exp
- \+ *lemma* real.lt_log_iff_exp_lt



## [2021-11-06 20:27:44](https://github.com/leanprover-community/mathlib/commit/169bb29)
feat(algebra/group/with_one): cleanup algebraic instances ([#10194](https://github.com/leanprover-community/mathlib/pull/10194))
This:
* adds a `has_neg (with_zero α)` instance which sends `0` to `0` and otherwise uses the underlying negation (and the same for `has_inv (with_one α)`).
* replaces the `has_div (with_zero α)`,  `has_pow (with_zero α) ℕ`, and `has_pow (with_zero α) ℤ` instances in order to produce better definitional properties than the previous default ones.
#### Estimated changes
Modified src/algebra/group/with_one.lean
- \+ *lemma* with_one.coe_inv
- \+ *lemma* with_zero.coe_div
- \+ *lemma* with_zero.coe_pow
- \+ *lemma* with_zero.coe_zpow
- \- *lemma* with_zero.div_coe



## [2021-11-06 20:27:43](https://github.com/leanprover-community/mathlib/commit/56a9228)
feat(analysis/normed_space/continuous_affine_map): define bundled continuous affine maps ([#10161](https://github.com/leanprover-community/mathlib/pull/10161))
I want to use the result the evaluation map `Hom(E, F) × E → F` is smooth in a category with continuous affine maps as morphisms. It is convenient to have a bundled type for this, despite the necessary boilerplate (proposed here).
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Added src/analysis/normed_space/continuous_affine_map.lean
- \+ *lemma* continuous_affine_map.coe_cont_linear_eq_linear
- \+ *lemma* continuous_affine_map.coe_linear_eq_coe_cont_linear
- \+ *lemma* continuous_affine_map.coe_mk_const_linear_eq_linear
- \+ *lemma* continuous_affine_map.const_cont_linear
- \+ *def* continuous_affine_map.cont_linear
- \+ *lemma* continuous_affine_map.cont_linear_eq_zero_iff_exists_const
- \+ *lemma* continuous_affine_map.cont_linear_map_vsub
- \+ *lemma* continuous_affine_map.map_vadd

Modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* affine_map.linear_eq_zero_iff_exists_const

Added src/topology/algebra/continuous_affine_map.lean
- \+ *lemma* continuous_affine_map.coe_affine_map_mk
- \+ *lemma* continuous_affine_map.coe_comp
- \+ *lemma* continuous_affine_map.coe_const
- \+ *lemma* continuous_affine_map.coe_continuous_map_mk
- \+ *lemma* continuous_affine_map.coe_injective
- \+ *lemma* continuous_affine_map.coe_mk
- \+ *lemma* continuous_affine_map.coe_to_affine_map
- \+ *lemma* continuous_affine_map.coe_to_continuous_map
- \+ *def* continuous_affine_map.comp
- \+ *lemma* continuous_affine_map.comp_apply
- \+ *lemma* continuous_affine_map.congr_fun
- \+ *def* continuous_affine_map.const
- \+ *lemma* continuous_affine_map.ext
- \+ *lemma* continuous_affine_map.ext_iff
- \+ *lemma* continuous_affine_map.mk_coe
- \+ *lemma* continuous_affine_map.to_affine_map_eq_coe
- \+ *lemma* continuous_affine_map.to_affine_map_injective
- \+ *def* continuous_affine_map.to_continuous_map
- \+ *lemma* continuous_affine_map.to_continuous_map_coe
- \+ *lemma* continuous_affine_map.to_continuous_map_injective
- \+ *lemma* continuous_affine_map.to_fun_eq_coe
- \+ *structure* continuous_affine_map



## [2021-11-06 20:27:42](https://github.com/leanprover-community/mathlib/commit/26c0c23)
feat(algebra/homology/image_to_kernel): homology.map_iso ([#9978](https://github.com/leanprover-community/mathlib/pull/9978))
#### Estimated changes
Modified src/algebra/homology/image_to_kernel.lean
- \+ *lemma* homology.comp_right_eq_comp_left
- \+ *lemma* homology.map_comp
- \+ *lemma* homology.map_id
- \+ *def* homology.map_iso



## [2021-11-06 18:49:17](https://github.com/leanprover-community/mathlib/commit/f18278d)
chore(algebra/opposites): use `injective.*` constructors ([#10200](https://github.com/leanprover-community/mathlib/pull/10200))
#### Estimated changes
Modified src/algebra/opposites.lean
- \+/\- *lemma* opposite.op_sub
- \+/\- *lemma* opposite.unop_sub



## [2021-11-06 18:49:16](https://github.com/leanprover-community/mathlib/commit/38caa50)
feat(data/nat/basic): `a < a / b * b + b` ([#10193](https://github.com/leanprover-community/mathlib/pull/10193))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.lt_div_mul_add



## [2021-11-06 18:49:15](https://github.com/leanprover-community/mathlib/commit/ebe7951)
feat(algebra/big_operators/order): Bound on a product from a pointwise bound ([#10190](https://github.com/leanprover-community/mathlib/pull/10190))
This proves `finset.le_prod_of_forall_le` which is the dual of `finset.prod_le_of_forall_le`.
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+/\- *lemma* finset.card_bUnion_le_card_mul
- \+ *lemma* finset.le_prod_of_forall_le
- \+/\- *lemma* finset.prod_le_of_forall_le



## [2021-11-06 18:49:14](https://github.com/leanprover-community/mathlib/commit/be412c3)
fix(README): update specialties of maintainers ([#10086](https://github.com/leanprover-community/mathlib/pull/10086))
#### Estimated changes
Modified README.md




## [2021-11-06 18:15:19](https://github.com/leanprover-community/mathlib/commit/0c54c57)
feat(data/set/equitable): A singleton is equitable ([#10192](https://github.com/leanprover-community/mathlib/pull/10192))
Prove `set.subsingleton.equitable_on` and `set.equitable_on_singleton`.
#### Estimated changes
Modified src/data/set/equitable.lean
- \+/\- *lemma* set.equitable_on_empty
- \+ *lemma* set.equitable_on_singleton
- \+ *lemma* set.subsingleton.equitable_on



## [2021-11-06 12:54:31](https://github.com/leanprover-community/mathlib/commit/af36f1a)
chore(algebra/group/ulift): use injective.* to define instances ([#10172](https://github.com/leanprover-community/mathlib/pull/10172))
Also rename `ulift.mul_equiv` to `mul_equiv.ulift` and add some
missing instances.
#### Estimated changes
Modified src/algebra/group/ulift.lean
- \+ *def* mul_equiv.ulift
- \- *def* ulift.mul_equiv

Modified src/algebra/module/ulift.lean




## [2021-11-06 11:24:11](https://github.com/leanprover-community/mathlib/commit/4b14ef4)
feat(data/fintype): instances for `infinite (α ⊕ β)` and `infinite (α × β)` ([#10196](https://github.com/leanprover-community/mathlib/pull/10196))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* infinite_prod
- \+ *lemma* infinite_sum



## [2021-11-06 09:47:22](https://github.com/leanprover-community/mathlib/commit/239bf05)
feat(data/list/basic): list products ([#10184](https://github.com/leanprover-community/mathlib/pull/10184))
Adding a couple of lemmas about list products. The first is a simpler variant of `head_mul_tail_prod'` in the case where the list is not empty.  The other is a variant of `list.prod_ne_zero` for `list ℕ`.
#### Estimated changes
Modified src/data/list/basic.lean
- \- *lemma* list.head_mul_tail_prod'
- \+ *lemma* list.head_mul_tail_prod_of_ne_nil
- \+ *lemma* list.nth_zero_mul_tail_prod
- \+ *lemma* list.prod_pos



## [2021-11-06 08:31:55](https://github.com/leanprover-community/mathlib/commit/051cb61)
feat(data/sym/sym2): Induction on `sym2` ([#10189](https://github.com/leanprover-community/mathlib/pull/10189))
A few basics about `sym2` that were blatantly missing.
#### Estimated changes
Modified src/data/sym/sym2.lean




## [2021-11-06 02:12:53](https://github.com/leanprover-community/mathlib/commit/4341fff)
chore(set_theory/cardinal_ordinal): use notation ω ([#10197](https://github.com/leanprover-community/mathlib/pull/10197))
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \+/\- *lemma* cardinal.add_eq_left
- \+/\- *lemma* cardinal.add_eq_left_iff
- \+/\- *theorem* cardinal.add_eq_max
- \+/\- *lemma* cardinal.add_eq_right
- \+/\- *lemma* cardinal.add_eq_right_iff
- \+/\- *theorem* cardinal.add_eq_self
- \+/\- *theorem* cardinal.add_lt_of_lt
- \+/\- *lemma* cardinal.add_one_eq
- \+/\- *theorem* cardinal.aleph'_omega
- \+/\- *theorem* cardinal.aleph_zero
- \+/\- *theorem* cardinal.bit0_eq_self
- \+/\- *lemma* cardinal.bit0_lt_bit1
- \+/\- *theorem* cardinal.bit0_lt_omega
- \+/\- *theorem* cardinal.bit1_eq_self_iff
- \+/\- *lemma* cardinal.bit1_le_bit0
- \+/\- *theorem* cardinal.bit1_lt_omega
- \+/\- *lemma* cardinal.eq_of_add_eq_of_omega_le
- \+/\- *theorem* cardinal.exists_aleph
- \+/\- *lemma* cardinal.mk_bounded_set_le_of_omega_le
- \+/\- *lemma* cardinal.mk_compl_eq_mk_compl_finite_same
- \+/\- *lemma* cardinal.mk_compl_eq_mk_compl_infinite
- \+/\- *lemma* cardinal.mk_compl_finset_of_omega_le
- \+/\- *lemma* cardinal.mk_compl_of_omega_le
- \+/\- *lemma* cardinal.mul_eq_left
- \+/\- *lemma* cardinal.mul_eq_left_iff
- \+/\- *theorem* cardinal.mul_eq_max
- \+/\- *lemma* cardinal.mul_eq_max_of_omega_le_left
- \+/\- *lemma* cardinal.mul_eq_right
- \+/\- *theorem* cardinal.mul_eq_self
- \+/\- *lemma* cardinal.mul_le_max_of_omega_le_left
- \+/\- *theorem* cardinal.mul_lt_of_lt
- \+/\- *theorem* cardinal.omega_le_aleph'
- \+/\- *theorem* cardinal.omega_le_aleph
- \+/\- *theorem* cardinal.omega_le_bit0
- \+/\- *theorem* cardinal.omega_le_bit1
- \+/\- *theorem* cardinal.ord_is_limit
- \+/\- *lemma* cardinal.powerlt_omega
- \+/\- *lemma* cardinal.powerlt_omega_le



## [2021-11-05 23:39:17](https://github.com/leanprover-community/mathlib/commit/8174bd0)
feat(analysis/inner_product_space/rayleigh): Rayleigh quotient produces eigenvectors ([#9840](https://github.com/leanprover-community/mathlib/pull/9840))
Define `self_adjoint` for an operator `T` to mean `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.  (This doesn't require a definition of `adjoint`, although that will come soon.). Prove that a local extremum of the Rayleigh quotient of a self-adjoint operator on the unit sphere is an eigenvector, and use this to prove that in finite dimension a self-adjoint operator has an eigenvector.
#### Estimated changes
Modified src/analysis/calculus/lagrange_multipliers.lean
- \+ *lemma* is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at_1d

Modified src/analysis/inner_product_space/basic.lean
- \+ *def* continuous_linear_map.re_apply_inner_self
- \+ *lemma* continuous_linear_map.re_apply_inner_self_apply
- \+ *lemma* continuous_linear_map.re_apply_inner_self_continuous
- \+ *lemma* continuous_linear_map.re_apply_inner_self_smul
- \+ *lemma* is_self_adjoint.apply_clm
- \+ *lemma* is_self_adjoint.coe_re_apply_inner_self_apply
- \+ *lemma* is_self_adjoint.conj_inner_sym
- \+ *def* is_self_adjoint
- \+ *lemma* is_self_adjoint_iff_bilin_form

Modified src/analysis/inner_product_space/calculus.lean
- \+ *lemma* has_strict_fderiv_at.inner
- \+ *lemma* has_strict_fderiv_at_norm_sq

Added src/analysis/inner_product_space/rayleigh.lean
- \+ *lemma* continuous_linear_map.image_rayleigh_eq_image_rayleigh_sphere
- \+ *lemma* continuous_linear_map.infi_rayleigh_eq_infi_rayleigh_sphere
- \+ *lemma* continuous_linear_map.rayleigh_smul
- \+ *lemma* continuous_linear_map.supr_rayleigh_eq_supr_rayleigh_sphere
- \+ *lemma* is_self_adjoint.eq_smul_self_of_is_local_extr_on
- \+ *lemma* is_self_adjoint.eq_smul_self_of_is_local_extr_on_real
- \+ *lemma* is_self_adjoint.has_eigenvalue_infi_of_finite_dimensional
- \+ *lemma* is_self_adjoint.has_eigenvalue_supr_of_finite_dimensional
- \+ *lemma* is_self_adjoint.has_eigenvector_of_is_local_extr_on
- \+ *lemma* is_self_adjoint.has_eigenvector_of_is_max_on
- \+ *lemma* is_self_adjoint.has_eigenvector_of_is_min_on
- \+ *lemma* is_self_adjoint.has_strict_fderiv_at_re_apply_inner_self
- \+ *lemma* is_self_adjoint.linearly_dependent_of_is_local_extr_on

Modified src/order/filter/extr.lean
- \+ *lemma* is_max_on.supr_eq
- \+ *lemma* is_min_on.infi_eq



## [2021-11-05 19:40:53](https://github.com/leanprover-community/mathlib/commit/6cd6975)
feat(order/lattice): add `inf_lt_sup` ([#10178](https://github.com/leanprover-community/mathlib/pull/10178))
Also add `inf_le_sup`, `lt_or_lt_iff_ne`, and `min_lt_max`.
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* lt_or_lt_iff_ne

Modified src/order/lattice.lean
- \+ *lemma* inf_le_sup
- \+ *lemma* inf_lt_sup

Modified src/order/min_max.lean
- \+ *lemma* min_lt_max



## [2021-11-05 19:40:52](https://github.com/leanprover-community/mathlib/commit/85f6420)
feat(algebra/group/inj_surj): add `injective.monoid_pow` etc ([#10152](https://github.com/leanprover-community/mathlib/pull/10152))
Add versions of some constructors that take `pow`/`zpow`/`nsmul`/`zsmul` as explicit arguments.
#### Estimated changes
Modified src/algebra/group/inj_surj.lean




## [2021-11-05 19:07:04](https://github.com/leanprover-community/mathlib/commit/d69501f)
feat(category_theory/limits/shapes/multiequalizer): Multi(co)equalizers ([#10169](https://github.com/leanprover-community/mathlib/pull/10169))
This PR adds another special shape to the limits library, which directly generalizes shapes for many other special limits (like pullbacks, equalizers, etc.).  A `multiequalizer` can be thought of an an equalizer of two maps between two products. This will be used later on in the context of sheafification.
I don't know if there is a standard name for the gadgets this PR introduces. I would be happy to change the names if needed.
#### Estimated changes
Added src/category_theory/limits/shapes/multiequalizer.lean
- \+ *abbreviation* category_theory.limits.has_multicoequalizer
- \+ *abbreviation* category_theory.limits.has_multiequalizer
- \+ *lemma* category_theory.limits.multicoequalizer.condition
- \+ *abbreviation* category_theory.limits.multicoequalizer.desc
- \+ *lemma* category_theory.limits.multicoequalizer.hom_ext
- \+ *abbreviation* category_theory.limits.multicoequalizer.multicofork
- \+ *lemma* category_theory.limits.multicoequalizer.multicofork_ι_app_right
- \+ *lemma* category_theory.limits.multicoequalizer.multicofork_π
- \+ *abbreviation* category_theory.limits.multicoequalizer.π
- \+ *lemma* category_theory.limits.multicoequalizer.π_desc
- \+ *abbreviation* category_theory.limits.multicoequalizer
- \+ *lemma* category_theory.limits.multicofork.condition
- \+ *lemma* category_theory.limits.multicofork.fst_app_right
- \+ *def* category_theory.limits.multicofork.of_π
- \+ *lemma* category_theory.limits.multicofork.snd_app_right
- \+ *def* category_theory.limits.multicofork.π
- \+ *lemma* category_theory.limits.multicofork.π_eq_app_right
- \+ *def* category_theory.limits.multicofork
- \+ *def* category_theory.limits.multicospan_index.multicospan
- \+ *lemma* category_theory.limits.multicospan_index.multicospan_map_fst
- \+ *lemma* category_theory.limits.multicospan_index.multicospan_map_snd
- \+ *lemma* category_theory.limits.multicospan_index.multicospan_obj_left
- \+ *lemma* category_theory.limits.multicospan_index.multicospan_obj_right
- \+ *structure* category_theory.limits.multicospan_index
- \+ *lemma* category_theory.limits.multiequalizer.condition
- \+ *lemma* category_theory.limits.multiequalizer.hom_ext
- \+ *abbreviation* category_theory.limits.multiequalizer.lift
- \+ *lemma* category_theory.limits.multiequalizer.lift_ι
- \+ *abbreviation* category_theory.limits.multiequalizer.multifork
- \+ *lemma* category_theory.limits.multiequalizer.multifork_ι
- \+ *lemma* category_theory.limits.multiequalizer.multifork_π_app_left
- \+ *abbreviation* category_theory.limits.multiequalizer.ι
- \+ *abbreviation* category_theory.limits.multiequalizer
- \+ *lemma* category_theory.limits.multifork.app_left_fst
- \+ *lemma* category_theory.limits.multifork.app_left_snd
- \+ *lemma* category_theory.limits.multifork.condition
- \+ *def* category_theory.limits.multifork.of_ι
- \+ *def* category_theory.limits.multifork.ι
- \+ *lemma* category_theory.limits.multifork.ι_eq_app_left
- \+ *def* category_theory.limits.multifork
- \+ *def* category_theory.limits.multispan_index.multispan
- \+ *lemma* category_theory.limits.multispan_index.multispan_map_fst
- \+ *lemma* category_theory.limits.multispan_index.multispan_map_snd
- \+ *lemma* category_theory.limits.multispan_index.multispan_obj_left
- \+ *lemma* category_theory.limits.multispan_index.multispan_obj_right
- \+ *structure* category_theory.limits.multispan_index
- \+ *def* category_theory.limits.walking_multicospan.hom.comp
- \+ *inductive* category_theory.limits.walking_multicospan.hom
- \+ *inductive* category_theory.limits.walking_multicospan
- \+ *def* category_theory.limits.walking_multispan.hom.comp
- \+ *inductive* category_theory.limits.walking_multispan.hom
- \+ *inductive* category_theory.limits.walking_multispan



## [2021-11-05 17:51:20](https://github.com/leanprover-community/mathlib/commit/cc59673)
chore(*complex*): add a few simp lemmas ([#10187](https://github.com/leanprover-community/mathlib/pull/10187))
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/basic.lean
- \+ *lemma* complex.exp_add_pi_mul_I
- \+/\- *lemma* complex.exp_int_mul_two_pi_mul_I
- \+/\- *lemma* complex.exp_nat_mul_two_pi_mul_I
- \+/\- *lemma* complex.exp_pi_mul_I
- \+ *lemma* complex.exp_sub_pi_mul_I
- \+/\- *lemma* complex.exp_two_pi_mul_I

Modified src/data/complex/basic.lean
- \+ *lemma* complex.norm_sq_mk

Modified src/data/complex/exponential.lean
- \+ *lemma* complex.exp_of_real_mul_I_im
- \+ *lemma* complex.exp_of_real_mul_I_re



## [2021-11-05 17:51:18](https://github.com/leanprover-community/mathlib/commit/a71bfdc)
feat(analysis/calculus/times_cont_diff): `equiv.prod_assoc` is smooth. ([#10165](https://github.com/leanprover-community/mathlib/pull/10165))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_prod_assoc
- \+ *lemma* times_cont_diff_prod_assoc_symm

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.coe_prod_assoc
- \+ *lemma* linear_isometry_equiv.coe_prod_assoc_symm



## [2021-11-05 17:51:17](https://github.com/leanprover-community/mathlib/commit/d9a80ee)
refactor(data/multiset/locally_finite): Generalize `multiset.Ico` to locally finite orders ([#10031](https://github.com/leanprover-community/mathlib/pull/10031))
This deletes `data.multiset.intervals` entirely, redefines `multiset.Ico` using `locally_finite_order` and restores the lemmas in their correct generality:
* `multiset.Ico.map_add` → `multiset.map_add_left_Ico`, `multiset.map_add_right_Ico`
* `multiset.Ico.eq_zero_of_le` → `multiset.Ico_eq_zero_of_le `
* `multiset.Ico.self_eq_zero` → `multiset.Ico_self`
* `multiset.Ico.nodup` → `multiset.nodup_Ico`
* `multiset.Ico.mem` → `multiset.mem_Ico`
* `multiset.Ico.not_mem_top` → `multiset.right_not_mem_Ico`
* `multiset.Ico.inter_consecutive` → `multiset.Ico_inter_Ico_of_le`
* `multiset.Ico.filter_something` → `multiset.filter_Ico_something`
* `multiset.Ico.eq_cons` → `multiset.Ioo_cons_left`
* `multiset.Ico.succ_top` →`multiset.Ico_cons_right`
`open set multiset` now causes a (minor) clash. This explains the changes to `analysis.box_integral.divergence_theorem` and `measure_theory.integral.divergence_theorem`
#### Estimated changes
Modified src/data/finset/locally_finite.lean
- \+/\- *lemma* finset.Ico_filter_le_left
- \+/\- *lemma* finset.Ico_filter_le_of_le_left
- \+/\- *lemma* finset.Ico_filter_le_of_left_le
- \+/\- *lemma* finset.Ico_filter_le_of_right_le
- \+/\- *lemma* finset.Ico_filter_lt_of_le_left
- \+/\- *lemma* finset.Ico_filter_lt_of_le_right
- \+/\- *lemma* finset.Ico_filter_lt_of_right_le

Modified src/data/multiset/default.lean


Deleted src/data/multiset/intervals.lean
- \- *lemma* multiset.Ico.add_consecutive
- \- *theorem* multiset.Ico.card
- \- *theorem* multiset.Ico.eq_cons
- \- *theorem* multiset.Ico.eq_zero_iff
- \- *theorem* multiset.Ico.eq_zero_of_le
- \- *lemma* multiset.Ico.filter_le
- \- *lemma* multiset.Ico.filter_le_of_bot
- \- *lemma* multiset.Ico.filter_le_of_le
- \- *lemma* multiset.Ico.filter_le_of_le_bot
- \- *lemma* multiset.Ico.filter_le_of_top_le
- \- *lemma* multiset.Ico.filter_lt
- \- *lemma* multiset.Ico.filter_lt_of_ge
- \- *lemma* multiset.Ico.filter_lt_of_le_bot
- \- *lemma* multiset.Ico.filter_lt_of_top_le
- \- *lemma* multiset.Ico.inter_consecutive
- \- *theorem* multiset.Ico.map_add
- \- *theorem* multiset.Ico.map_sub
- \- *theorem* multiset.Ico.mem
- \- *theorem* multiset.Ico.nodup
- \- *theorem* multiset.Ico.not_mem_top
- \- *theorem* multiset.Ico.pred_singleton
- \- *theorem* multiset.Ico.self_eq_zero
- \- *theorem* multiset.Ico.succ_singleton
- \- *theorem* multiset.Ico.succ_top
- \- *theorem* multiset.Ico.zero_bot
- \- *def* multiset.Ico

Modified src/data/multiset/locally_finite.lean
- \+ *lemma* multiset.Ico_add_Ico_eq_Ico
- \+ *lemma* multiset.Ico_cons_right
- \+ *lemma* multiset.Ico_disjoint_Ico
- \+ *lemma* multiset.Ico_eq_zero_iff
- \+ *lemma* multiset.Ico_eq_zero_of_le
- \+ *lemma* multiset.Ico_filter_le
- \+ *lemma* multiset.Ico_filter_le_left
- \+ *lemma* multiset.Ico_filter_le_of_le_left
- \+ *lemma* multiset.Ico_filter_le_of_left_le
- \+ *lemma* multiset.Ico_filter_le_of_right_le
- \+ *lemma* multiset.Ico_filter_lt
- \+ *lemma* multiset.Ico_filter_lt_of_le_left
- \+ *lemma* multiset.Ico_filter_lt_of_le_right
- \+ *lemma* multiset.Ico_filter_lt_of_right_le
- \+ *lemma* multiset.Ico_inter_Ico
- \+ *lemma* multiset.Ico_inter_Ico_of_le
- \+ *lemma* multiset.Ico_self
- \+ *lemma* multiset.Ico_sub_Ico_left
- \+ *lemma* multiset.Ico_sub_Ico_right
- \+ *lemma* multiset.Ico_subset_Ico_iff
- \+ *lemma* multiset.Ioo_cons_left
- \+ *lemma* multiset.left_mem_Icc
- \+ *lemma* multiset.left_mem_Ico
- \+ *lemma* multiset.left_not_mem_Ioc
- \+ *lemma* multiset.left_not_mem_Ioo
- \+ *lemma* multiset.map_add_left_Ico
- \+ *lemma* multiset.map_add_right_Ico
- \+ *lemma* multiset.nodup_Ico
- \+ *lemma* multiset.right_mem_Icc
- \+ *lemma* multiset.right_mem_Ioc
- \+ *lemma* multiset.right_not_mem_Ico
- \+ *lemma* multiset.right_not_mem_Ioo

Modified src/data/nat/interval.lean
- \+/\- *lemma* nat.Icc_succ_left
- \+/\- *lemma* nat.Ico_succ_left
- \+/\- *lemma* nat.Ico_succ_right
- \+/\- *lemma* nat.Ico_succ_singleton
- \+/\- *lemma* nat.Ico_zero_eq_range
- \+/\- *lemma* nat.Iio_eq_range
- \+/\- *lemma* nat.image_sub_const_Ico
- \+/\- *lemma* nat.range_image_pred_top_sub

Modified src/order/locally_finite.lean
- \+ *def* multiset.Ico
- \+ *lemma* multiset.mem_Ico
- \+/\- *lemma* set.finite_Icc
- \+/\- *lemma* set.finite_Ico
- \+/\- *lemma* set.finite_Ioc
- \+/\- *lemma* set.finite_Ioo



## [2021-11-05 16:25:14](https://github.com/leanprover-community/mathlib/commit/5f5ce2b)
feat(combinatorics/simple_graph): adding simple_graph.support and mem_support / support_mono lemmas ([#10176](https://github.com/leanprover-community/mathlib/pull/10176))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* simple_graph.mem_support
- \+ *def* simple_graph.support
- \+ *lemma* simple_graph.support_mono

Modified src/data/rel.lean
- \+ *lemma* rel.dom_mono



## [2021-11-05 15:19:39](https://github.com/leanprover-community/mathlib/commit/8ac2fa0)
chore(linear_algebra/affine_space/affine_map): make `affine_map.coe_sub` true by definition ([#10182](https://github.com/leanprover-community/mathlib/pull/10182))
This makes life slightly easier in some work following on from https://github.com/leanprover-community/mathlib/pull/10161
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_map.lean
- \+/\- *lemma* affine_map.add_linear
- \+/\- *lemma* affine_map.coe_sub
- \+ *lemma* affine_map.neg_linear
- \+ *lemma* affine_map.sub_linear



## [2021-11-05 15:19:38](https://github.com/leanprover-community/mathlib/commit/b22a7c7)
refactor(measure_theory/integral/bochner): remove superfluous hypothesis ([#10181](https://github.com/leanprover-community/mathlib/pull/10181))
* Remove hypothesis from `tendsto_integral_of_dominated_convergence` that was superfluous
* This results in simplifying some proofs, and removing some hypotheses from other lemmas
* Also remove some `ae_measurable` hypotheses for functions that were also assumed to be `integrable`.
#### Estimated changes
Modified src/analysis/calculus/parametric_integral.lean


Modified src/measure_theory/constructions/prod.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/measure_theory/integral/integral_eq_improper.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/set_integral.lean




## [2021-11-05 15:19:37](https://github.com/leanprover-community/mathlib/commit/88b4ce7)
feat(algebra/order/with_zero): add with_zero.linear_ordered_comm_grou… ([#10180](https://github.com/leanprover-community/mathlib/pull/10180))
…p_with_zero
#### Estimated changes
Modified src/algebra/order/with_zero.lean




## [2021-11-05 13:33:49](https://github.com/leanprover-community/mathlib/commit/b31af6d)
refactor(algebra/group): move `monoid.has_pow` etc to `algebra.group.defs` ([#10147](https://github.com/leanprover-community/mathlib/pull/10147))
This way we can state theorems about `pow`/`nsmul` using notation `^` and `•` right away.
Also move some `ext` lemmas to a new file and rewrite proofs using properties of `monoid_hom`s.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_zpow
- \- *lemma* finset.zsmul_sum

Modified src/algebra/group/commute.lean
- \+/\- *lemma* commute.is_unit_mul_iff
- \+ *theorem* commute.pow_left
- \+ *theorem* commute.pow_pow
- \+ *theorem* commute.pow_pow_self
- \+ *theorem* commute.pow_right
- \+ *theorem* commute.pow_self
- \+ *theorem* commute.self_pow
- \+/\- *theorem* commute.units_inv_left
- \+ *theorem* commute.units_inv_left_iff:
- \- *theorem* commute.units_inv_left_iff
- \+/\- *theorem* commute.units_inv_right
- \+/\- *theorem* commute.units_inv_right_iff
- \+/\- *lemma* is_unit_mul_self_iff
- \+ *theorem* pow_succ'

Modified src/algebra/group/defs.lean
- \- *lemma* cancel_comm_monoid.ext
- \- *lemma* cancel_comm_monoid.to_comm_monoid_injective
- \- *lemma* cancel_monoid.ext
- \- *lemma* cancel_monoid.to_left_cancel_monoid_injective
- \- *lemma* comm_group.ext
- \- *lemma* comm_monoid.ext
- \- *lemma* comm_monoid.to_monoid_injective
- \- *lemma* div_inv_monoid.ext
- \- *lemma* group.ext
- \- *lemma* left_cancel_monoid.ext
- \- *lemma* left_cancel_monoid.to_monoid_injective
- \- *lemma* monoid.ext
- \- *lemma* npow_add
- \+ *lemma* npow_eq_pow
- \- *lemma* npow_one
- \+ *theorem* pow_succ
- \+ *theorem* pow_zero
- \- *lemma* right_cancel_monoid.ext
- \- *lemma* right_cancel_monoid.to_monoid_injective
- \+ *theorem* zpow_coe_nat
- \+ *lemma* zpow_eq_pow
- \+ *theorem* zpow_neg_succ_of_nat
- \+ *theorem* zpow_of_nat
- \+ *theorem* zpow_zero

Added src/algebra/group/ext.lean
- \+ *lemma* cancel_comm_monoid.ext
- \+ *lemma* cancel_comm_monoid.to_comm_monoid_injective
- \+ *lemma* cancel_monoid.ext
- \+ *lemma* cancel_monoid.to_left_cancel_monoid_injective
- \+ *lemma* comm_group.ext
- \+ *lemma* comm_monoid.ext
- \+ *lemma* comm_monoid.to_monoid_injective
- \+ *lemma* div_inv_monoid.ext
- \+ *lemma* group.ext
- \+ *lemma* left_cancel_monoid.ext
- \+ *lemma* left_cancel_monoid.to_monoid_injective
- \+ *lemma* monoid.ext
- \+ *lemma* right_cancel_monoid.ext
- \+ *lemma* right_cancel_monoid.to_monoid_injective

Modified src/algebra/group/hom.lean
- \+ *theorem* monoid_hom.map_div'
- \+ *theorem* monoid_hom.map_pow
- \+ *theorem* monoid_hom.map_zpow'
- \+ *theorem* monoid_hom.map_zpow

Modified src/algebra/group/hom_instances.lean


Modified src/algebra/group/pi.lean


Modified src/algebra/group/semiconj.lean
- \+ *lemma* semiconj_by.pow_right

Modified src/algebra/group/type_tags.lean


Modified src/algebra/group/ulift.lean


Modified src/algebra/group_power/basic.lean
- \- *theorem* commute.pow_left
- \- *theorem* commute.pow_pow
- \- *theorem* commute.pow_pow_self
- \- *theorem* commute.pow_right
- \- *theorem* commute.pow_self
- \- *theorem* commute.self_pow
- \- *theorem* monoid_hom.map_pow
- \- *lemma* npow_eq_pow
- \- *theorem* pow_succ'
- \- *theorem* pow_succ
- \- *theorem* pow_zero
- \- *lemma* semiconj_by.pow_right
- \- *theorem* zpow_coe_nat
- \- *lemma* zpow_eq_pow
- \- *theorem* zpow_neg_succ_of_nat
- \- *theorem* zpow_of_nat
- \- *theorem* zpow_zero

Modified src/algebra/group_power/lemmas.lean
- \- *theorem* monoid_hom.map_zpow

Modified src/algebra/opposites.lean


Modified src/algebra/order/archimedean.lean


Modified src/algebra/order/pi.lean


Modified src/algebra/periodic.lean


Modified src/algebra/ring/pi.lean


Modified src/algebra/ring/ulift.lean


Modified src/analysis/normed_space/basic.lean


Modified src/category_theory/preadditive/schur.lean


Modified src/data/finsupp/basic.lean


Modified src/data/holor.lean


Modified src/group_theory/group_action/defs.lean


Modified src/group_theory/subgroup/basic.lean
- \+/\- *def* subgroup.saturated

Modified src/group_theory/submonoid/membership.lean


Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/quotient.lean


Modified src/ring_theory/localization.lean


Modified src/tactic/abel.lean


Modified src/topology/algebra/module.lean




## [2021-11-05 10:08:26](https://github.com/leanprover-community/mathlib/commit/16af388)
feat(data/quot): add `quotient.lift₂_mk` ([#10173](https://github.com/leanprover-community/mathlib/pull/10173))
#### Estimated changes
Modified src/data/quot.lean
- \+ *lemma* quotient.lift₂_mk



## [2021-11-05 08:27:18](https://github.com/leanprover-community/mathlib/commit/35d3628)
chore(data/bool): add `bool.lt_iff` ([#10179](https://github.com/leanprover-community/mathlib/pull/10179))
#### Estimated changes
Modified src/data/bool.lean
- \+/\- *lemma* bool.ff_lt_tt
- \+ *lemma* bool.lt_iff



## [2021-11-05 06:48:59](https://github.com/leanprover-community/mathlib/commit/8991f28)
feat(measure_theory/covering/vitali_family): define Vitali families ([#10057](https://github.com/leanprover-community/mathlib/pull/10057))
Vitali families are families of sets (for instance balls around each point in vector spaces) that satisfy covering theorems. Their main feature is that differentiation of measure theorems hold along Vitali families. This PR is a stub defining Vitali families, and giving examples of them thanks to the Besicovitch and Vitali covering theorems.
The differentiation theorem is left for another PR.
#### Estimated changes
Modified src/data/set/pairwise.lean
- \+ *lemma* pairwise_subtype_iff_pairwise_set
- \+/\- *lemma* set.pairwise_disjoint_empty
- \+/\- *lemma* set.pairwise_disjoint_singleton

Modified src/measure_theory/covering/besicovitch.lean


Modified src/measure_theory/covering/vitali.lean


Added src/measure_theory/covering/vitali_family.lean
- \+ *lemma* vitali_family.eventually_filter_at_iff
- \+ *lemma* vitali_family.eventually_filter_at_mem_sets
- \+ *lemma* vitali_family.eventually_filter_at_subset_of_nhds
- \+ *def* vitali_family.filter_at
- \+ *lemma* vitali_family.fine_subfamily_on.covering_disjoint
- \+ *lemma* vitali_family.fine_subfamily_on.covering_disjoint_subtype
- \+ *lemma* vitali_family.fine_subfamily_on.covering_mem
- \+ *lemma* vitali_family.fine_subfamily_on.covering_mem_family
- \+ *theorem* vitali_family.fine_subfamily_on.exists_disjoint_covering_ae
- \+ *lemma* vitali_family.fine_subfamily_on.index_countable
- \+ *lemma* vitali_family.fine_subfamily_on.index_subset
- \+ *lemma* vitali_family.fine_subfamily_on.measure_diff_bUnion
- \+ *lemma* vitali_family.fine_subfamily_on.measure_le_tsum
- \+ *lemma* vitali_family.fine_subfamily_on.measure_le_tsum_of_absolutely_continuous
- \+ *def* vitali_family.fine_subfamily_on
- \+ *lemma* vitali_family.fine_subfamily_on_of_frequently
- \+ *lemma* vitali_family.frequently_filter_at_iff
- \+ *lemma* vitali_family.mem_filter_at_iff
- \+ *def* vitali_family.mono
- \+ *structure* vitali_family



## [2021-11-05 06:00:09](https://github.com/leanprover-community/mathlib/commit/6f9ec12)
doc(group_theory/sylow): Expand Frattini's argument docstring ([#10174](https://github.com/leanprover-community/mathlib/pull/10174))
Expands the docstring for Frattini's argument.
#### Estimated changes
Modified src/group_theory/sylow.lean




## [2021-11-05 02:24:22](https://github.com/leanprover-community/mathlib/commit/8490f2a)
chore(scripts): update nolints.txt ([#10177](https://github.com/leanprover-community/mathlib/pull/10177))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-11-05 00:43:55](https://github.com/leanprover-community/mathlib/commit/41a820d)
feat(number_theory/lucas_primality): Add theorem for Lucas primality test ([#8820](https://github.com/leanprover-community/mathlib/pull/8820))
This is a PR for adding the [Lucas primality test](https://en.wikipedia.org/wiki/Lucas_primality_test) to mathlib. This tells us that a number `p` is prime when an element `a : zmod p` has order `p-1` .
#### Estimated changes
Modified src/algebra/divisibility.lean
- \+ *lemma* dvd_iff_exists_eq_mul_left

Modified src/data/nat/totient.lean
- \+ *lemma* nat.card_units_zmod_lt_sub_one
- \+ *lemma* nat.prime_iff_card_units
- \+ *lemma* nat.totient_lt
- \+/\- *lemma* zmod.card_units_eq_totient

Modified src/group_theory/order_of_element.lean
- \+ *theorem* order_of_eq_of_pow_and_pow_div_prime

Added src/number_theory/lucas_primality.lean
- \+ *theorem* lucas_primality



## [2021-11-04 22:36:42](https://github.com/leanprover-community/mathlib/commit/d6a57f8)
feat(data/finset/prod): When `finset.product` is nonempty ([#10170](https://github.com/leanprover-community/mathlib/pull/10170))
and two lemmas about how it interacts with the union.
#### Estimated changes
Modified src/data/finset/prod.lean
- \+ *lemma* finset.nonempty.fst
- \+ *lemma* finset.nonempty.product
- \+ *lemma* finset.nonempty.snd
- \+ *lemma* finset.nonempty_product
- \+ *lemma* finset.product_union
- \+ *lemma* finset.union_product



## [2021-11-04 22:36:40](https://github.com/leanprover-community/mathlib/commit/b064622)
feat(data/fin/interval): Cardinality of `finset.Ixi`/`finset.Iix` in `fin` ([#10168](https://github.com/leanprover-community/mathlib/pull/10168))
This proves `(Ici a).card = n + 1 - a`, `(Ioi a).card = n - a`, `(Iic b).card = b + 1`, `(Iio b).card = b` where `a b : fin (n + 1)` (and also `a b : ℕ` for the last two).
#### Estimated changes
Modified src/data/fin/interval.lean
- \+ *lemma* fin.Ici_eq_finset_subtype
- \+ *lemma* fin.Iic_eq_finset_subtype
- \+ *lemma* fin.Iio_eq_finset_subtype
- \+ *lemma* fin.Ioi_eq_finset_subtype
- \+ *lemma* fin.card_Ici
- \+ *lemma* fin.card_Iic
- \+ *lemma* fin.card_Iio
- \+ *lemma* fin.card_Ioi
- \+ *lemma* fin.card_fintype_Ici
- \+ *lemma* fin.card_fintype_Iic
- \+ *lemma* fin.card_fintype_Iio
- \+ *lemma* fin.card_fintype_Ioi
- \+ *lemma* fin.map_subtype_embedding_Ici
- \+ *lemma* fin.map_subtype_embedding_Iic
- \+ *lemma* fin.map_subtype_embedding_Iio
- \+ *lemma* fin.map_subtype_embedding_Ioi

Modified src/data/nat/interval.lean
- \+ *lemma* nat.card_Iic
- \+ *lemma* nat.card_Iio
- \+ *lemma* nat.card_fintype_Iic
- \+ *lemma* nat.card_fintype_Iio



## [2021-11-04 22:36:39](https://github.com/leanprover-community/mathlib/commit/fab61c9)
chore(topology/continuous_function/bounded): add simple lemmas ([#10149](https://github.com/leanprover-community/mathlib/pull/10149))
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.add_comp_continuous
- \+ *lemma* bounded_continuous_function.coe_to_continuous_fun
- \+ *lemma* bounded_continuous_function.continuous_comp_continuous
- \+ *lemma* bounded_continuous_function.eq_of_empty
- \+ *lemma* bounded_continuous_function.lipschitz_comp_continuous
- \+ *lemma* bounded_continuous_function.zero_comp_continuous



## [2021-11-04 22:36:37](https://github.com/leanprover-community/mathlib/commit/466fd27)
feat(algebra/group_with_zero/basic): relax some commutativity assumptions ([#10075](https://github.com/leanprover-community/mathlib/pull/10075))
Moving some lemmas so they require group_with_zero instead of comm_group_with_zero, using the generalization linter.
#### Estimated changes
Modified archive/imo/imo2008_q4.lean


Modified src/algebra/group_with_zero/basic.lean




## [2021-11-04 22:36:36](https://github.com/leanprover-community/mathlib/commit/ce0e058)
feat(data/equiv/mul_add): add lemmas about multiplication and addition on a group being bijective and finite cancel_monoid_with_zeros ([#10046](https://github.com/leanprover-community/mathlib/pull/10046))
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *lemma* group.mul_left_bijective
- \+ *lemma* group.mul_right_bijective
- \+ *lemma* mul_left_bijective₀
- \+ *lemma* mul_right_bijective₀
- \+ *lemma* units.mul_left_bijective
- \+ *lemma* units.mul_right_bijective

Modified src/ring_theory/integral_domain.lean
- \+ *def* group_with_zero_of_fintype
- \+ *lemma* mul_left_bijective_of_fintype₀
- \- *lemma* mul_left_bijective₀
- \+ *lemma* mul_right_bijective_of_fintype₀
- \- *lemma* mul_right_bijective₀



## [2021-11-04 21:07:34](https://github.com/leanprover-community/mathlib/commit/773a7a4)
feat(analysis/ODE): prove Picard-Lindelöf/Cauchy-Lipschitz Theorem ([#9791](https://github.com/leanprover-community/mathlib/pull/9791))
#### Estimated changes
Modified docs/undergrad.yaml


Added src/analysis/ODE/picard_lindelof.lean
- \+ *lemma* exists_forall_deriv_within_Icc_eq_of_lipschitz_of_continuous
- \+ *lemma* picard_lindelof.continuous_proj
- \+ *lemma* picard_lindelof.dist_t₀_le
- \+ *lemma* picard_lindelof.exists_contracting_iterate
- \+ *lemma* picard_lindelof.exists_fixed
- \+ *lemma* picard_lindelof.exists_solution
- \+ *lemma* picard_lindelof.fun_space.continuous_v_comp
- \+ *lemma* picard_lindelof.fun_space.dist_apply_le_dist
- \+ *lemma* picard_lindelof.fun_space.dist_iterate_next_apply_le
- \+ *lemma* picard_lindelof.fun_space.dist_iterate_next_le
- \+ *lemma* picard_lindelof.fun_space.dist_le_of_forall
- \+ *lemma* picard_lindelof.fun_space.dist_next_apply_le_of_le
- \+ *lemma* picard_lindelof.fun_space.has_deriv_within_at_next
- \+ *lemma* picard_lindelof.fun_space.interval_integrable_v_comp
- \+ *lemma* picard_lindelof.fun_space.map_t₀
- \+ *def* picard_lindelof.fun_space.next
- \+ *lemma* picard_lindelof.fun_space.next_apply
- \+ *lemma* picard_lindelof.fun_space.norm_v_comp_le
- \+ *lemma* picard_lindelof.fun_space.range_to_continuous_map
- \+ *def* picard_lindelof.fun_space.to_continuous_map
- \+ *lemma* picard_lindelof.fun_space.uniform_inducing_to_continuous_map
- \+ *def* picard_lindelof.fun_space.v_comp
- \+ *lemma* picard_lindelof.fun_space.v_comp_apply_coe
- \+ *structure* picard_lindelof.fun_space
- \+ *lemma* picard_lindelof.norm_le
- \+ *def* picard_lindelof.proj
- \+ *lemma* picard_lindelof.proj_coe
- \+ *lemma* picard_lindelof.proj_of_mem
- \+ *def* picard_lindelof.t_dist
- \+ *lemma* picard_lindelof.t_dist_nonneg
- \+ *lemma* picard_lindelof.t_min_le_t_max
- \+ *structure* picard_lindelof

Modified src/data/set/intervals/unordered_interval.lean
- \+ *lemma* set.interval_subset_Icc

Modified src/topology/order.lean




## [2021-11-04 20:30:13](https://github.com/leanprover-community/mathlib/commit/74c27b2)
feat(topology/sheaves): Pullback of presheaf ([#9961](https://github.com/leanprover-community/mathlib/pull/9961))
Defined the pullback of a presheaf along a continuous map, and proved that it is adjoint to pushforwards
and it preserves stalks.
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean


Modified src/topology/sheaves/presheaf.lean
- \+/\- *lemma* Top.presheaf.id_pushforward
- \+ *def* Top.presheaf.pullback.id
- \+ *lemma* Top.presheaf.pullback.id_inv_app
- \+ *def* Top.presheaf.pullback
- \+ *def* Top.presheaf.pullback_map
- \+ *def* Top.presheaf.pullback_obj
- \+ *def* Top.presheaf.pullback_obj_obj_of_image_open
- \+ *def* Top.presheaf.pushforward_pullback_adjunction

Modified src/topology/sheaves/stalks.lean
- \+ *def* Top.presheaf.germ_to_pullback_stalk
- \+ *def* Top.presheaf.stalk_pullback_hom
- \+ *def* Top.presheaf.stalk_pullback_inv
- \+ *def* Top.presheaf.stalk_pullback_iso



## [2021-11-04 18:49:13](https://github.com/leanprover-community/mathlib/commit/79eb934)
chore(data/mv_polynomial/basic): add `map_alg_hom_coe_ring_hom` ([#10158](https://github.com/leanprover-community/mathlib/pull/10158))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.map_alg_hom_coe_ring_hom



## [2021-11-04 18:49:11](https://github.com/leanprover-community/mathlib/commit/11439d8)
chore(algebra/direct_sum/internal): add missing simp lemmas ([#10154](https://github.com/leanprover-community/mathlib/pull/10154))
These previously weren't needed when these were `@[reducible] def`s as `simp` saw right through them.
#### Estimated changes
Modified src/algebra/direct_sum/internal.lean
- \+ *lemma* submodule.set_like.coe_galgebra_to_fun

Modified src/algebra/graded_monoid.lean
- \+ *lemma* set_like.coe_ghas_mul
- \+ *lemma* set_like.coe_ghas_one
- \+ *lemma* set_like.coe_gpow



## [2021-11-04 18:49:10](https://github.com/leanprover-community/mathlib/commit/828e100)
feat(data/finset/interval): `finset α` is a locally finite order ([#9963](https://github.com/leanprover-community/mathlib/pull/9963))
#### Estimated changes
Modified src/analysis/box_integral/divergence_theorem.lean


Modified src/data/finset/basic.lean


Added src/data/finset/interval.lean
- \+ *lemma* finset.Icc_eq_filter_powerset
- \+ *lemma* finset.Icc_eq_image_powerset
- \+ *lemma* finset.Ico_eq_filter_ssubsets
- \+ *lemma* finset.Ico_eq_image_ssubsets
- \+ *lemma* finset.Iic_eq_powerset
- \+ *lemma* finset.Iio_eq_ssubsets
- \+ *lemma* finset.Ioc_eq_filter_powerset
- \+ *lemma* finset.Ioo_eq_filter_ssubsets
- \+ *lemma* finset.card_Icc_finset
- \+ *lemma* finset.card_Ico_finset
- \+ *lemma* finset.card_Ioc_finset
- \+ *lemma* finset.card_Ioo_finset

Modified src/data/finset/locally_finite.lean
- \+ *lemma* finset.Icc_erase_left
- \+ *lemma* finset.Icc_erase_right
- \+/\- *lemma* finset.Ico_disjoint_Ico_consecutive
- \+/\- *lemma* finset.Ico_insert_right
- \+/\- *lemma* finset.Ico_inter_Ico_consecutive
- \+/\- *lemma* finset.Ioo_insert_left
- \+ *lemma* finset.card_Ico_eq_card_Icc_sub_one
- \+ *lemma* finset.card_Ioc_eq_card_Icc_sub_one
- \+ *lemma* finset.card_Ioo_eq_card_Icc_sub_two
- \+ *lemma* finset.card_Ioo_eq_card_Ico_sub_one
- \+ *lemma* finset.left_mem_Icc
- \+ *lemma* finset.left_mem_Ico
- \+ *lemma* finset.left_not_mem_Ioc
- \+ *lemma* finset.left_not_mem_Ioo
- \+ *lemma* finset.right_mem_Icc
- \+ *lemma* finset.right_mem_Ioc
- \+/\- *lemma* finset.right_not_mem_Ico
- \+ *lemma* finset.right_not_mem_Ioo

Modified src/data/set/basic.lean


Modified src/measure_theory/integral/divergence_theorem.lean


Modified src/order/boolean_algebra.lean
- \+ *lemma* sdiff_le_sdiff_left
- \+ *lemma* sdiff_le_sdiff_of_sup_le_sup_left
- \+ *lemma* sdiff_le_sdiff_of_sup_le_sup_right
- \+ *lemma* sdiff_le_sdiff_right
- \- *lemma* sdiff_le_sdiff_self
- \- *lemma* sdiff_le_self_sdiff
- \+ *lemma* sdiff_lt_sdiff_right
- \+ *lemma* sdiff_sup_cancel
- \+ *lemma* sup_le_of_le_sdiff_left
- \+ *lemma* sup_le_of_le_sdiff_right
- \+ *lemma* sup_lt_of_lt_sdiff_left
- \+ *lemma* sup_lt_of_lt_sdiff_right
- \+ *lemma* sup_sdiff_cancel_right
- \- *lemma* sup_sdiff_of_le

Modified src/order/locally_finite.lean


Modified src/order/symm_diff.lean




## [2021-11-04 17:11:43](https://github.com/leanprover-community/mathlib/commit/cf2ff03)
feat(group_theory/sylow): Sylow subgroups are nontrivial! ([#10144](https://github.com/leanprover-community/mathlib/pull/10144))
These lemmas (finally!) connect the work of @ChrisHughes24 with the recent definition of Sylow subgroups, to show that Sylow subgroups are actually nontrivial!
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.dvd_card_of_dvd_card
- \+ *lemma* sylow.ne_bot_of_dvd_card
- \+ *lemma* sylow.pow_dvd_card_of_pow_dvd_card



## [2021-11-04 17:11:42](https://github.com/leanprover-community/mathlib/commit/52cd445)
refactor(data/set/pairwise): Indexed sets as arguments to `set.pairwise_disjoint` ([#9898](https://github.com/leanprover-community/mathlib/pull/9898))
This will allow to express the bind operation: you can't currently express that the pairwise disjoint union of pairwise disjoint sets pairwise disjoint. Here's the corresponding statement with `finset.sup_indep` (defined in [#9867](https://github.com/leanprover-community/mathlib/pull/9867)):
```lean
lemma sup_indep.sup {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.sup g).sup_indep f :=
```
You currently can't do `set.pairwise_disjoint s (λ i, ⋃ x ∈ g i, f x)`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.prod_bUnion

Modified src/algebra/big_operators/ring.lean


Modified src/data/set/pairwise.lean
- \+/\- *lemma* set.bUnion_diff_bUnion_eq
- \+ *lemma* set.inj_on.pairwise_disjoint_image
- \+/\- *lemma* set.pairwise_disjoint.elim'
- \+/\- *lemma* set.pairwise_disjoint.elim
- \+/\- *lemma* set.pairwise_disjoint.elim_set
- \+/\- *lemma* set.pairwise_disjoint.image_of_le
- \+/\- *lemma* set.pairwise_disjoint.insert
- \+ *lemma* set.pairwise_disjoint.mono
- \+ *lemma* set.pairwise_disjoint.mono_on
- \+/\- *lemma* set.pairwise_disjoint.range
- \+/\- *lemma* set.pairwise_disjoint.subset
- \+ *lemma* set.pairwise_disjoint.union
- \+/\- *def* set.pairwise_disjoint
- \+ *lemma* set.pairwise_disjoint_Union
- \+/\- *lemma* set.pairwise_disjoint_empty
- \+/\- *lemma* set.pairwise_disjoint_fiber
- \+/\- *lemma* set.pairwise_disjoint_insert
- \- *lemma* set.pairwise_disjoint_on_mono
- \+/\- *lemma* set.pairwise_disjoint_range_singleton
- \+ *lemma* set.pairwise_disjoint_sUnion
- \+/\- *lemma* set.pairwise_disjoint_singleton
- \+ *lemma* set.pairwise_disjoint_union

Modified src/data/setoid/partition.lean


Modified src/measure_theory/covering/besicovitch.lean


Modified src/measure_theory/covering/vitali.lean


Modified src/ring_theory/polynomial/cyclotomic.lean


Modified src/topology/bases.lean
- \+ *lemma* set.pairwise_disjoint.countable_of_is_open
- \+ *lemma* set.pairwise_disjoint.countable_of_nonempty_interior
- \- *lemma* topological_space.countable_of_is_open_of_disjoint
- \- *lemma* topological_space.countable_of_nonempty_interior_of_disjoint



## [2021-11-04 15:29:36](https://github.com/leanprover-community/mathlib/commit/5187a42)
feat(linear_algebra/affine_space/affine_map): decomposition of an affine map between modules as an equiv ([#10162](https://github.com/leanprover-community/mathlib/pull/10162))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* affine_map.smul_linear
- \+ *def* affine_map.to_const_prod_linear_map



## [2021-11-04 15:29:34](https://github.com/leanprover-community/mathlib/commit/22ec295)
chore(data/set): lemmas about `disjoint` ([#10148](https://github.com/leanprover-community/mathlib/pull/10148))
#### Estimated changes
Modified src/data/set/intervals/disjoint.lean
- \+ *lemma* set.Ici_disjoint_Iic
- \+ *lemma* set.Iic_disjoint_Ici

Modified src/data/set/lattice.lean
- \+ *lemma* set.disjoint_image_of_injective
- \+ *lemma* set.disjoint_preimage



## [2021-11-04 15:29:33](https://github.com/leanprover-community/mathlib/commit/69189d4)
split(data/finset/prod): split off `data.finset.basic` ([#10142](https://github.com/leanprover-community/mathlib/pull/10142))
Killing the giants. This moves `finset.product`, `finset.diag`, `finset.off_diag` to their own file, the theme being "finsets on `α × β`".
The copyright header now credits:
* Johannes Hölzl for ba95269a65a77c8ab5eae075f842fdad0c0a7aaf
* Mario Carneiro
* Oliver Nash for [#4502](https://github.com/leanprover-community/mathlib/pull/4502)
#### Estimated changes
Modified src/data/finset/basic.lean
- \- *theorem* finset.card_product
- \- *def* finset.diag
- \- *lemma* finset.diag_card
- \- *lemma* finset.diag_empty
- \- *lemma* finset.empty_product
- \- *theorem* finset.filter_product
- \- *lemma* finset.filter_product_card
- \- *lemma* finset.mem_diag
- \- *lemma* finset.mem_off_diag
- \- *theorem* finset.mem_product
- \- *def* finset.off_diag
- \- *lemma* finset.off_diag_card
- \- *lemma* finset.off_diag_empty
- \- *lemma* finset.product_bUnion
- \- *lemma* finset.product_empty
- \- *theorem* finset.product_eq_bUnion
- \- *lemma* finset.product_subset_product
- \- *lemma* finset.product_subset_product_left
- \- *lemma* finset.product_subset_product_right
- \- *theorem* finset.product_val
- \- *theorem* finset.subset_product

Added src/data/finset/prod.lean
- \+ *lemma* finset.card_product
- \+ *def* finset.diag
- \+ *lemma* finset.diag_card
- \+ *lemma* finset.diag_empty
- \+ *lemma* finset.empty_product
- \+ *lemma* finset.filter_product
- \+ *lemma* finset.filter_product_card
- \+ *lemma* finset.mem_diag
- \+ *lemma* finset.mem_off_diag
- \+ *lemma* finset.mem_product
- \+ *def* finset.off_diag
- \+ *lemma* finset.off_diag_card
- \+ *lemma* finset.off_diag_empty
- \+ *lemma* finset.product_bUnion
- \+ *lemma* finset.product_empty
- \+ *lemma* finset.product_eq_bUnion
- \+ *lemma* finset.product_subset_product
- \+ *lemma* finset.product_subset_product_left
- \+ *lemma* finset.product_subset_product_right
- \+ *lemma* finset.product_val
- \+ *lemma* finset.subset_product

Modified src/data/fintype/basic.lean




## [2021-11-04 13:04:54](https://github.com/leanprover-community/mathlib/commit/de79226)
feat(ring_theory/polynomial/basic): `polynomial.ker_map_ring_hom` and `mv_polynomial.ker_map` ([#10160](https://github.com/leanprover-community/mathlib/pull/10160))
#### Estimated changes
Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* mv_polynomial.ker_map
- \+ *lemma* polynomial.ker_map_ring_hom



## [2021-11-04 13:04:53](https://github.com/leanprover-community/mathlib/commit/2129d05)
chore(measure_theory/function/special_functions): import inner_product_space.basic instead of inner_product_space.calculus ([#10159](https://github.com/leanprover-community/mathlib/pull/10159))
Right now this changes almost nothing because other imports like `analysis.special_functions.pow` depend on calculus, but I am changing that in other PRs. `measure_theory/function/special_functions` will soon not depend on calculus at all.
#### Estimated changes
Modified src/measure_theory/function/special_functions.lean




## [2021-11-04 13:04:51](https://github.com/leanprover-community/mathlib/commit/b890836)
chore(analysis/calculus/times_cont_diff): rename `linear_isometry_map.times_cont_diff`; drop `_map` ([#10155](https://github.com/leanprover-community/mathlib/pull/10155))
I think the old name is a typo; the new name enables dot notation.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* linear_isometry.times_cont_diff
- \- *lemma* linear_isometry_map.times_cont_diff



## [2021-11-04 13:04:50](https://github.com/leanprover-community/mathlib/commit/3cbe0fe)
feat(linear_algebra/matrix/nonsingular_inverse): determinant of inverse is inverse of determinant ([#10038](https://github.com/leanprover-community/mathlib/pull/10038))
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *theorem* inv_pow_sub

Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* is_unit.ring_inverse
- \+ *lemma* is_unit_ring_inverse

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.conj_transpose_nonsing_inv
- \+ *lemma* matrix.det_nonsing_inv
- \+ *lemma* matrix.det_nonsing_inv_mul_det
- \+/\- *lemma* matrix.is_unit_nonsing_inv_det_iff
- \- *lemma* matrix.nonsing_inv_det
- \+ *lemma* matrix.nonsing_inv_eq_ring_inverse



## [2021-11-04 13:04:48](https://github.com/leanprover-community/mathlib/commit/17afc5c)
feat(topology/algebra/group_with_zero): continuity lemma for division ([#9959](https://github.com/leanprover-community/mathlib/pull/9959))
* This even applies when dividing by `0`.
* From the sphere eversion project.
* This PR mentions `filter.tendsto_prod_top_iff` which is added by [#9958](https://github.com/leanprover-community/mathlib/pull/9958)
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.prod_top

Modified src/topology/algebra/group_with_zero.lean
- \+ *lemma* continuous.comp_div_cases
- \+ *lemma* continuous_at.comp_div_cases



## [2021-11-04 11:24:16](https://github.com/leanprover-community/mathlib/commit/211bdff)
feat(data/nat/choose/basic): add some inequalities showing that choose is monotonic in the first argument ([#10102](https://github.com/leanprover-community/mathlib/pull/10102))
From flt-regular
#### Estimated changes
Modified src/data/nat/choose/basic.lean
- \+ *lemma* nat.choose_le_add
- \+ *lemma* nat.choose_le_choose
- \+ *lemma* nat.choose_le_succ
- \+ *lemma* nat.choose_mono



## [2021-11-04 11:24:14](https://github.com/leanprover-community/mathlib/commit/1f0d878)
feat(data/list): standardize list prefixes and suffixes ([#10052](https://github.com/leanprover-community/mathlib/pull/10052))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.drop_sublist
- \+ *theorem* list.drop_subset
- \+ *theorem* list.init_prefix
- \+ *theorem* list.init_sublist
- \+ *theorem* list.init_subset
- \+ *theorem* list.mem_of_mem_drop
- \- *lemma* list.mem_of_mem_drop
- \+ *theorem* list.mem_of_mem_init
- \+ *theorem* list.mem_of_mem_tail
- \- *lemma* list.mem_of_mem_tail
- \+ *theorem* list.mem_of_mem_take
- \+ *theorem* list.tail_sublist
- \- *lemma* list.tail_sublist
- \+ *theorem* list.take_sublist
- \+ *theorem* list.take_subset



## [2021-11-04 11:24:13](https://github.com/leanprover-community/mathlib/commit/4c0b6ad)
feat(topology/homotopy/basic): add `homotopic` for `continuous_map`s. ([#9865](https://github.com/leanprover-community/mathlib/pull/9865))
#### Estimated changes
Modified src/topology/homotopy/basic.lean
- \+ *lemma* continuous_map.homotopic.equivalence
- \+ *lemma* continuous_map.homotopic.hcomp
- \+ *lemma* continuous_map.homotopic.refl
- \+ *lemma* continuous_map.homotopic.symm
- \+ *lemma* continuous_map.homotopic.trans
- \+ *def* continuous_map.homotopic
- \+ *lemma* continuous_map.homotopic_rel.equivalence
- \+ *lemma* continuous_map.homotopic_rel.refl
- \+ *lemma* continuous_map.homotopic_rel.symm
- \+ *lemma* continuous_map.homotopic_rel.trans
- \+ *def* continuous_map.homotopic_rel
- \+ *lemma* continuous_map.homotopic_with.refl
- \+ *lemma* continuous_map.homotopic_with.symm
- \+ *lemma* continuous_map.homotopic_with.trans
- \+ *def* continuous_map.homotopic_with
- \+ *def* continuous_map.homotopy.hcomp

Modified src/topology/homotopy/path.lean




## [2021-11-04 09:43:52](https://github.com/leanprover-community/mathlib/commit/d219e6b)
chore(data/equiv/mul_add): DRY ([#10150](https://github.com/leanprover-community/mathlib/pull/10150))
use `units.mul_left`/`units.mul_right` to define
`equiv.mul_left₀`/`equiv.mul_right₀`.
#### Estimated changes
Modified src/data/equiv/mul_add.lean




## [2021-11-04 09:43:51](https://github.com/leanprover-community/mathlib/commit/76ba1b6)
chore(ring_theory/finiteness): make `finite_presentation.{quotient,mv_polynomial}` protected ([#10091](https://github.com/leanprover-community/mathlib/pull/10091))
This lets us clean up some `_root_`s
This also golfs a proof
#### Estimated changes
Modified src/ring_theory/finiteness.lean
- \- *lemma* algebra.finite_presentation.mv_polynomial
- \- *lemma* algebra.finite_presentation.quotient



## [2021-11-04 07:56:27](https://github.com/leanprover-community/mathlib/commit/8658f40)
feat(algebra/group_power/order): Sign of an odd/even power without linearity ([#10122](https://github.com/leanprover-community/mathlib/pull/10122))
This proves that `a < 0 → 0 < a ^ bit0 n` and `a < 0 → a ^ bit1 n < 0` in an `ordered_semiring`.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* odd.strict_mono_pow
- \+/\- *theorem* one_add_mul_le_pow'
- \+/\- *lemma* pow_le_of_le_one
- \+/\- *lemma* pow_le_pow_of_le_one
- \+/\- *lemma* pow_lt_pow_iff_of_lt_one
- \+/\- *lemma* pow_lt_pow_of_lt_one
- \+/\- *lemma* sq_le

Modified src/algebra/group_power/order.lean
- \+/\- *theorem* one_le_pow_of_one_le
- \+/\- *lemma* one_lt_pow
- \+/\- *theorem* pow_add_pow_le
- \+ *lemma* pow_bit0_pos_of_neg
- \+ *lemma* pow_bit1_neg
- \+/\- *lemma* pow_le_one
- \+/\- *theorem* pow_le_pow
- \+/\- *lemma* pow_lt_one
- \+/\- *lemma* pow_lt_pow
- \+/\- *lemma* pow_lt_pow_iff
- \+/\- *theorem* pow_lt_pow_of_lt_left
- \+/\- *lemma* pow_mono
- \+/\- *theorem* pow_nonneg
- \+/\- *theorem* pow_pos
- \+ *lemma* sq_pos_of_neg
- \+ *lemma* sq_pos_of_pos
- \+/\- *theorem* strict_mono_on_pow
- \+/\- *lemma* strict_mono_pow



## [2021-11-04 02:36:27](https://github.com/leanprover-community/mathlib/commit/4770a6a)
chore(scripts): update nolints.txt ([#10146](https://github.com/leanprover-community/mathlib/pull/10146))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-11-04 00:15:53](https://github.com/leanprover-community/mathlib/commit/0fac080)
refactor(analysis/calculus/mean_value): Remove useless hypotheses ([#10129](https://github.com/leanprover-community/mathlib/pull/10129))
Because the junk value of `deriv` is `0`, assuming `∀ x, 0 < deriv f x` implies that `f` is derivable. We thus remove all those redundant derivability assumptions.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* differentiable_at_of_deriv_ne_zero
- \+ *lemma* differentiable_within_at_of_deriv_within_ne_zero

Modified src/analysis/calculus/mean_value.lean
- \+/\- *theorem* strict_anti_of_deriv_neg
- \+/\- *theorem* strict_mono_of_deriv_pos

Modified src/analysis/special_functions/trigonometric/deriv.lean




## [2021-11-03 22:10:14](https://github.com/leanprover-community/mathlib/commit/fed57b5)
refactor(algebra/direct_sum): rework internally-graded objects ([#10127](https://github.com/leanprover-community/mathlib/pull/10127))
This is a replacement for the `graded_ring.core` typeclass in [#10115](https://github.com/leanprover-community/mathlib/pull/10115), which is called `set_like.graded_monoid` here. The advantage of this approach is that we can use the same typeclass for graded semirings, graded rings, and graded algebras.
Largely, this change replaces a bunch of `def`s with `instances`, by bundling up the arguments to those defs to a new typeclass. This seems to make life easier for the few global `gmonoid` instance we already provide for direct sums of submodules, suggesting this API change is a useful one.
In principle the new `[set_like.graded_monoid A]` typeclass is useless, as the same effect can be achieved with `[set_like.has_graded_one A] [set_like.has_graded_mul A]`; pragmatically though this is painfully verbose, and probably results in larger term sizes. We can always remove it later if it causes problems.
#### Estimated changes
Modified src/algebra/direct_sum/algebra.lean


Added src/algebra/direct_sum/internal.lean
- \+ *def* direct_sum.subgroup_coe_ring_hom
- \+ *lemma* direct_sum.subgroup_coe_ring_hom_of
- \+ *def* direct_sum.submodule_coe_alg_hom
- \+ *lemma* direct_sum.submodule_coe_alg_hom_of
- \+ *def* direct_sum.submonoid_coe_ring_hom
- \+ *lemma* direct_sum.submonoid_coe_ring_hom_of

Modified src/algebra/direct_sum/ring.lean
- \- *def* direct_sum.gcomm_semiring.of_add_subgroups
- \- *def* direct_sum.gcomm_semiring.of_add_submonoids
- \- *def* direct_sum.gcomm_semiring.of_submodules
- \- *def* direct_sum.gsemiring.of_add_subgroups
- \- *def* direct_sum.gsemiring.of_add_submonoids
- \- *def* direct_sum.gsemiring.of_submodules

Modified src/algebra/graded_monoid.lean
- \- *def* graded_monoid.gcomm_monoid.of_subobjects
- \- *def* graded_monoid.ghas_mul.of_subobjects
- \- *def* graded_monoid.ghas_one.of_subobjects
- \- *def* graded_monoid.gmonoid.of_subobjects

Modified src/algebra/monoid_algebra/grading.lean


Modified src/ring_theory/polynomial/homogeneous.lean




## [2021-11-03 20:00:44](https://github.com/leanprover-community/mathlib/commit/6433c1c)
feat(group_theory/sylow): Sylow subgroups are isomorphic ([#10059](https://github.com/leanprover-community/mathlib/pull/10059))
Constructs `sylow.mul_equiv`.
#### Estimated changes
Modified src/group_theory/subgroup/pointwise.lean
- \+ *def* subgroup.equiv_smul

Modified src/group_theory/submonoid/operations.lean


Modified src/group_theory/sylow.lean
- \+ *def* sylow.equiv_smul



## [2021-11-03 20:00:42](https://github.com/leanprover-community/mathlib/commit/5541b25)
refactor(group_theory/complement): Introduce abbreviation for subgroups ([#10009](https://github.com/leanprover-community/mathlib/pull/10009))
Introduces abbreviation for `is_complement (H : set G) (K : set G)`.
#### Estimated changes
Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.is_complement'.card_mul
- \+ *lemma* subgroup.is_complement'.disjoint
- \+ *lemma* subgroup.is_complement'.symm
- \+ *abbreviation* subgroup.is_complement'
- \+ *lemma* subgroup.is_complement'_comm
- \+ *lemma* subgroup.is_complement'_def
- \+ *lemma* subgroup.is_complement'_iff_card_mul_and_disjoint
- \+ *lemma* subgroup.is_complement'_of_card_mul_and_disjoint
- \+ *lemma* subgroup.is_complement'_of_coprime
- \- *lemma* subgroup.is_complement.card_mul
- \- *lemma* subgroup.is_complement.disjoint
- \- *lemma* subgroup.is_complement.symm
- \- *lemma* subgroup.is_complement_comm
- \- *lemma* subgroup.is_complement_iff_card_mul_and_disjoint
- \- *lemma* subgroup.is_complement_of_card_mul_and_disjoint
- \- *lemma* subgroup.is_complement_of_coprime

Modified src/group_theory/schur_zassenhaus.lean
- \+ *theorem* subgroup.exists_left_complement'_of_coprime
- \- *theorem* subgroup.exists_left_complement_of_coprime
- \+ *theorem* subgroup.exists_right_complement'_of_coprime
- \- *theorem* subgroup.exists_right_complement_of_coprime
- \+ *lemma* subgroup.is_complement'_stabilizer_of_coprime
- \- *lemma* subgroup.is_complement_stabilizer_of_coprime



## [2021-11-03 17:56:43](https://github.com/leanprover-community/mathlib/commit/3a0b0d1)
chore(order/lattice): add `exists_lt_of_sup/inf` ([#10133](https://github.com/leanprover-community/mathlib/pull/10133))
#### Estimated changes
Modified src/order/lattice.lean
- \+ *theorem* exists_lt_of_inf
- \+ *theorem* exists_lt_of_sup



## [2021-11-03 17:56:42](https://github.com/leanprover-community/mathlib/commit/8f7ffec)
chore(analysis/special_functions/trigonometric/inverse): move results about derivatives to a new file ([#10110](https://github.com/leanprover-community/mathlib/pull/10110))
This is part of a refactor of the `analysis/special_functions` folder, in which I will isolate all lemmas about derivatives. The result will be a definition of Lp spaces that does not import derivatives.
#### Estimated changes
Modified src/analysis/special_functions/complex/log.lean


Modified src/analysis/special_functions/trigonometric/inverse.lean
- \- *lemma* real.deriv_arccos
- \- *lemma* real.deriv_arcsin
- \- *lemma* real.deriv_arcsin_aux
- \- *lemma* real.differentiable_at_arccos
- \- *lemma* real.differentiable_at_arcsin
- \- *lemma* real.differentiable_on_arccos
- \- *lemma* real.differentiable_on_arcsin
- \- *lemma* real.differentiable_within_at_arccos_Ici
- \- *lemma* real.differentiable_within_at_arccos_Iic
- \- *lemma* real.differentiable_within_at_arcsin_Ici
- \- *lemma* real.differentiable_within_at_arcsin_Iic
- \- *lemma* real.has_deriv_at_arccos
- \- *lemma* real.has_deriv_at_arcsin
- \- *lemma* real.has_deriv_within_at_arccos_Ici
- \- *lemma* real.has_deriv_within_at_arccos_Iic
- \- *lemma* real.has_deriv_within_at_arcsin_Ici
- \- *lemma* real.has_deriv_within_at_arcsin_Iic
- \- *lemma* real.has_strict_deriv_at_arccos
- \- *lemma* real.has_strict_deriv_at_arcsin
- \- *lemma* real.times_cont_diff_at_arccos
- \- *lemma* real.times_cont_diff_at_arccos_iff
- \- *lemma* real.times_cont_diff_at_arcsin
- \- *lemma* real.times_cont_diff_at_arcsin_iff
- \- *lemma* real.times_cont_diff_on_arccos
- \- *lemma* real.times_cont_diff_on_arcsin

Added src/analysis/special_functions/trigonometric/inverse_deriv.lean
- \+ *lemma* real.deriv_arccos
- \+ *lemma* real.deriv_arcsin
- \+ *lemma* real.deriv_arcsin_aux
- \+ *lemma* real.differentiable_at_arccos
- \+ *lemma* real.differentiable_at_arcsin
- \+ *lemma* real.differentiable_on_arccos
- \+ *lemma* real.differentiable_on_arcsin
- \+ *lemma* real.differentiable_within_at_arccos_Ici
- \+ *lemma* real.differentiable_within_at_arccos_Iic
- \+ *lemma* real.differentiable_within_at_arcsin_Ici
- \+ *lemma* real.differentiable_within_at_arcsin_Iic
- \+ *lemma* real.has_deriv_at_arccos
- \+ *lemma* real.has_deriv_at_arcsin
- \+ *lemma* real.has_deriv_within_at_arccos_Ici
- \+ *lemma* real.has_deriv_within_at_arccos_Iic
- \+ *lemma* real.has_deriv_within_at_arcsin_Ici
- \+ *lemma* real.has_deriv_within_at_arcsin_Iic
- \+ *lemma* real.has_strict_deriv_at_arccos
- \+ *lemma* real.has_strict_deriv_at_arcsin
- \+ *lemma* real.times_cont_diff_at_arccos
- \+ *lemma* real.times_cont_diff_at_arccos_iff
- \+ *lemma* real.times_cont_diff_at_arcsin
- \+ *lemma* real.times_cont_diff_at_arcsin_iff
- \+ *lemma* real.times_cont_diff_on_arccos
- \+ *lemma* real.times_cont_diff_on_arcsin

Modified src/data/complex/basic.lean
- \+/\- *lemma* complex.conj_bit0
- \+/\- *lemma* complex.conj_bit1
- \+/\- *lemma* complex.conj_of_real

Modified src/geometry/euclidean/basic.lean




## [2021-11-03 17:56:41](https://github.com/leanprover-community/mathlib/commit/00a1022)
chore(logic/relation): rename to permit dot notation ([#10105](https://github.com/leanprover-community/mathlib/pull/10105))
#### Estimated changes
Modified src/category_theory/is_connected.lean


Modified src/category_theory/limits/types.lean


Modified src/data/pfunctor/multivariate/M.lean


Modified src/group_theory/free_group.lean


Modified src/logic/relation.lean
- \+ *lemma* equivalence.eqv_gen_eq
- \+ *lemma* equivalence.eqv_gen_iff
- \+ *lemma* eqv_gen.mono
- \- *lemma* relation.eqv_gen_eq_of_equivalence
- \- *lemma* relation.eqv_gen_iff_of_equivalence
- \- *lemma* relation.eqv_gen_mono
- \+ *lemma* relation.refl_trans_gen.lift'
- \+ *lemma* relation.refl_trans_gen.lift
- \+ *lemma* relation.refl_trans_gen.mono
- \- *lemma* relation.refl_trans_gen_lift'
- \- *lemma* relation.refl_trans_gen_lift
- \- *lemma* relation.refl_trans_gen_mono
- \+ *lemma* relation.trans_gen.closed
- \+ *lemma* relation.trans_gen.lift'
- \+ *lemma* relation.trans_gen.lift
- \- *lemma* relation.trans_gen.trans_gen_closed
- \- *lemma* relation.trans_gen.trans_gen_eq_self
- \- *lemma* relation.trans_gen.trans_gen_idem
- \- *lemma* relation.trans_gen.trans_gen_lift'
- \- *lemma* relation.trans_gen.trans_gen_lift
- \- *lemma* relation.trans_gen.transitive_trans_gen
- \+ *lemma* relation.trans_gen_eq_self
- \+ *lemma* relation.trans_gen_idem
- \+ *lemma* relation.transitive_trans_gen

Modified test/qpf.lean




## [2021-11-03 17:56:40](https://github.com/leanprover-community/mathlib/commit/6993e6f)
feat(measure_theory/constructions/borel_space): decomposing the measure of a set into slices ([#10096](https://github.com/leanprover-community/mathlib/pull/10096))
Also add the fact that `μ (to_measurable μ t ∩ s) = μ (t ∩ s)`, and useful variations around this fact.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* measure_eq_measure_preimage_add_measure_tsum_Ico_zpow

Modified src/measure_theory/measure/finite_measure_weak_convergence.lean


Modified src/measure_theory/measure/measure_space.lean
- \+ *theorem* measure_theory.measure.coe_nnreal_smul_apply
- \+ *lemma* measure_theory.measure.measure_eq_left_of_subset_of_measure_add_eq
- \+ *lemma* measure_theory.measure.measure_eq_right_of_subset_of_measure_add_eq
- \+ *lemma* measure_theory.measure.measure_inter_eq_of_measure_eq
- \+ *lemma* measure_theory.measure.measure_to_measurable_add_inter_left
- \+ *lemma* measure_theory.measure.measure_to_measurable_add_inter_right
- \+ *lemma* measure_theory.measure.measure_to_measurable_inter
- \+/\- *theorem* measure_theory.measure.smul_apply

Modified src/measure_theory/measure/measure_space_def.lean


Modified src/measure_theory/measure/regular.lean
- \+ *lemma* set.exists_is_open_le_add



## [2021-11-03 17:56:38](https://github.com/leanprover-community/mathlib/commit/b51f18f)
feat(topology): properties about intervals and paths ([#9914](https://github.com/leanprover-community/mathlib/pull/9914))
* From the sphere eversion project
* Properties about paths, the interval, and `proj_Icc`
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/inverse.lean


Modified src/data/set/intervals/proj_Icc.lean
- \+ *lemma* set.proj_Icc_eq_left
- \+ *lemma* set.proj_Icc_eq_right

Modified src/topology/algebra/ordered/proj_Icc.lean
- \+ *lemma* continuous.Icc_extend'
- \+/\- *lemma* continuous.Icc_extend
- \+ *lemma* continuous_at.Icc_extend
- \+ *lemma* filter.tendsto.Icc_extend

Modified src/topology/path_connected.lean
- \+ *lemma* continuous.path_extend
- \+ *lemma* continuous_at.path_extend
- \+ *lemma* filter.tendsto.path_extend
- \+/\- *lemma* path.refl_range
- \+/\- *lemma* path.refl_symm
- \+/\- *lemma* path.symm_range

Modified src/topology/unit_interval.lean
- \+ *lemma* proj_Icc_eq_one
- \+ *lemma* proj_Icc_eq_zero
- \+ *lemma* unit_interval.coe_eq_one
- \+ *lemma* unit_interval.coe_eq_zero
- \+ *lemma* unit_interval.coe_mul
- \+ *lemma* unit_interval.coe_ne_one
- \+ *lemma* unit_interval.coe_ne_zero
- \+ *lemma* unit_interval.le_one'
- \+ *lemma* unit_interval.mul_le_left
- \+ *lemma* unit_interval.mul_le_right
- \+ *lemma* unit_interval.mul_mem
- \+ *lemma* unit_interval.nonneg'



## [2021-11-03 16:54:02](https://github.com/leanprover-community/mathlib/commit/8d52be4)
feat(measure_theory/function/ae_measurable_order): an ae measurability criterion for ennreal-valued functions ([#10072](https://github.com/leanprover-community/mathlib/pull/10072))
#### Estimated changes
Added src/measure_theory/function/ae_measurable_order.lean
- \+ *theorem* ennreal.ae_measurable_of_exist_almost_disjoint_supersets
- \+ *theorem* measure_theory.ae_measurable_of_exist_almost_disjoint_supersets

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* dense_iff_forall_lt_exists_mem
- \+ *lemma* is_open.exists_Ioo_subset



## [2021-11-03 16:10:04](https://github.com/leanprover-community/mathlib/commit/4f033b7)
feat(analysis/seminorm): define the Minkowski functional ([#9097](https://github.com/leanprover-community/mathlib/pull/9097))
This defines the gauge of a set, aka the Minkowski functional, in a vector space over a real normed field.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* absorbent.gauge_set_nonempty
- \+ *lemma* absorbent.subset
- \+/\- *def* absorbent
- \+/\- *lemma* absorbent_iff_forall_absorbs_singleton
- \+ *lemma* absorbent_iff_nonneg_lt
- \+/\- *def* absorbs
- \+ *lemma* balanced.smul_eq
- \+ *lemma* balanced.subset_smul
- \+ *lemma* convex.gauge_le_one
- \+ *lemma* exists_lt_of_gauge_lt
- \+ *def* gauge
- \+ *lemma* gauge_add_le
- \+ *lemma* gauge_def'
- \+ *lemma* gauge_def
- \+ *lemma* gauge_le_of_mem
- \+ *lemma* gauge_le_one_eq'
- \+ *lemma* gauge_le_one_eq
- \+ *lemma* gauge_le_one_of_mem
- \+ *lemma* gauge_lt_one_eq'
- \+ *lemma* gauge_lt_one_eq
- \+ *lemma* gauge_lt_one_eq_self_of_open
- \+ *lemma* gauge_lt_one_of_mem_of_open
- \+ *lemma* gauge_lt_one_subset_self
- \+ *lemma* gauge_neg
- \+ *lemma* gauge_nonneg
- \+ *def* gauge_seminorm
- \+ *lemma* gauge_smul
- \+ *lemma* gauge_smul_of_nonneg
- \+ *lemma* gauge_zero
- \+ *lemma* interior_subset_gauge_lt_one
- \+ *lemma* one_le_gauge_of_not_mem
- \+ *lemma* self_subset_gauge_le_one
- \+ *lemma* seminorm.absorbent_ball
- \+ *lemma* seminorm.absorbent_ball_zero
- \+ *lemma* seminorm.convex_ball
- \+ *lemma* seminorm.ext
- \+ *lemma* seminorm.gauge_ball
- \+ *lemma* seminorm.gauge_seminorm_ball
- \+ *lemma* seminorm.symmetric_ball_zero



## [2021-11-03 14:39:55](https://github.com/leanprover-community/mathlib/commit/95cdeba)
doc(linear_algebra): fix wrong docstring ([#10139](https://github.com/leanprover-community/mathlib/pull/10139))
#### Estimated changes
Modified src/linear_algebra/prod.lean




## [2021-11-03 14:39:53](https://github.com/leanprover-community/mathlib/commit/2b87435)
feat(ring_theory/trace): remove a useless assumption ([#10138](https://github.com/leanprover-community/mathlib/pull/10138))
We remove an assumption that is always true.
#### Estimated changes
Modified src/ring_theory/trace.lean




## [2021-11-03 14:39:52](https://github.com/leanprover-community/mathlib/commit/93cec25)
chore(*): replace `exact calc` by `calc` ([#10137](https://github.com/leanprover-community/mathlib/pull/10137))
This PR is the result of a sed script that replaces
* `exact calc` by `calc`
* `refine calc` by `calc`
#### Estimated changes
Modified src/analysis/inner_product_space/projection.lean


Modified src/data/complex/exponential.lean


Modified src/data/nat/log.lean


Modified src/group_theory/group_action/basic.lean


Modified src/order/filter/pointwise.lean


Modified src/set_theory/ordinal_notation.lean


Modified src/topology/continuous_function/bounded.lean




## [2021-11-03 13:35:53](https://github.com/leanprover-community/mathlib/commit/eaf2a16)
fix(scripts/lint-style.py): typo in error reporting ([#10135](https://github.com/leanprover-community/mathlib/pull/10135))
#### Estimated changes
Modified scripts/lint-style.py




## [2021-11-03 13:35:52](https://github.com/leanprover-community/mathlib/commit/1e7f3ca)
feat(data/zmod/basic): add nat_coe_eq_nat_coe_iff' ([#10128](https://github.com/leanprover-community/mathlib/pull/10128))
To match the int version, from flt-regular
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.nat_coe_eq_nat_coe_iff'



## [2021-11-03 09:01:33](https://github.com/leanprover-community/mathlib/commit/e5c66a0)
chore(topology/continuous_function/bounded): add `comp_continuous` ([#10134](https://github.com/leanprover-community/mathlib/pull/10134))
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean
- \+ *def* bounded_continuous_function.comp_continuous
- \+ *def* bounded_continuous_function.restrict



## [2021-11-03 07:31:37](https://github.com/leanprover-community/mathlib/commit/e5acda4)
chore(order/conditionally_complete_lattice): drop an unneeded `nonempty` assumption ([#10132](https://github.com/leanprover-community/mathlib/pull/10132))
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* csupr_mem_Inter_Icc_of_antitone_Icc
- \+/\- *lemma* monotone.csupr_mem_Inter_Icc_of_antitone



## [2021-11-03 02:56:05](https://github.com/leanprover-community/mathlib/commit/5f2e527)
chore(scripts): update nolints.txt ([#10130](https://github.com/leanprover-community/mathlib/pull/10130))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-11-02 23:57:01](https://github.com/leanprover-community/mathlib/commit/123db5e)
feat(linear_algebra/determinant): basis.det_ne_zero ([#10126](https://github.com/leanprover-community/mathlib/pull/10126))
Add the trivial lemma that the determinant with respect to a basis is
not the zero map (if the ring is nontrivial).
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* basis.det_ne_zero



## [2021-11-02 23:57:00](https://github.com/leanprover-community/mathlib/commit/86ed02f)
chore(algebra/order/floor): add a few trivial lemmas ([#10120](https://github.com/leanprover-community/mathlib/pull/10120))
#### Estimated changes
Modified src/algebra/order/floor.lean
- \+/\- *lemma* int.ceil_add_one
- \+/\- *lemma* int.ceil_sub_int
- \+ *lemma* int.ceil_sub_one
- \+ *lemma* int.fract_add_int
- \+ *lemma* int.fract_eq_self
- \+ *lemma* int.fract_sub_int
- \+ *lemma* int.fract_sub_self
- \+ *lemma* int.self_sub_fract



## [2021-11-02 23:56:58](https://github.com/leanprover-community/mathlib/commit/1dec85c)
doc(topology): three module docstrings ([#10107](https://github.com/leanprover-community/mathlib/pull/10107))
#### Estimated changes
Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/category/Top/open_nhds.lean




## [2021-11-02 21:57:35](https://github.com/leanprover-community/mathlib/commit/d49636e)
doc(topology/open_subgroup): add module docstring ([#10111](https://github.com/leanprover-community/mathlib/pull/10111))
Also add a lattice instance.
#### Estimated changes
Modified src/topology/algebra/open_subgroup.lean




## [2021-11-02 21:57:34](https://github.com/leanprover-community/mathlib/commit/70ed9dc)
chore(analysis/special_functions/trigonometric/basic): move results about derivatives to a new file ([#10109](https://github.com/leanprover-community/mathlib/pull/10109))
This is part of a refactor of the `analysis/special_functions` folder, in which I will isolate all lemmas about derivatives. The result will be a definition of Lp spaces that does not import derivatives.
#### Estimated changes
Modified src/analysis/special_functions/arsinh.lean


Modified src/analysis/special_functions/trigonometric/basic.lean
- \- *lemma* complex.deriv_cos'
- \- *lemma* complex.deriv_cos
- \- *lemma* complex.deriv_cosh
- \- *lemma* complex.deriv_sin
- \- *lemma* complex.deriv_sinh
- \- *lemma* complex.differentiable_at_cos
- \- *lemma* complex.differentiable_at_cosh
- \- *lemma* complex.differentiable_at_sin
- \- *lemma* complex.differentiable_at_sinh
- \- *lemma* complex.differentiable_cos
- \- *lemma* complex.differentiable_cosh
- \- *lemma* complex.differentiable_sin
- \- *lemma* complex.differentiable_sinh
- \- *lemma* complex.has_deriv_at_cos
- \- *lemma* complex.has_deriv_at_cosh
- \- *lemma* complex.has_deriv_at_sin
- \- *lemma* complex.has_deriv_at_sinh
- \- *lemma* complex.has_strict_deriv_at_cos
- \- *lemma* complex.has_strict_deriv_at_cosh
- \- *lemma* complex.has_strict_deriv_at_sin
- \- *lemma* complex.has_strict_deriv_at_sinh
- \- *lemma* complex.times_cont_diff_cos
- \- *lemma* complex.times_cont_diff_cosh
- \- *lemma* complex.times_cont_diff_sin
- \- *lemma* complex.times_cont_diff_sinh
- \- *lemma* deriv_ccos
- \- *lemma* deriv_ccosh
- \- *lemma* deriv_cos
- \- *lemma* deriv_cosh
- \- *lemma* deriv_csin
- \- *lemma* deriv_csinh
- \- *lemma* deriv_sin
- \- *lemma* deriv_sinh
- \- *lemma* deriv_within_ccos
- \- *lemma* deriv_within_ccosh
- \- *lemma* deriv_within_cos
- \- *lemma* deriv_within_cosh
- \- *lemma* deriv_within_csin
- \- *lemma* deriv_within_csinh
- \- *lemma* deriv_within_sin
- \- *lemma* deriv_within_sinh
- \- *lemma* differentiable.ccos
- \- *lemma* differentiable.ccosh
- \- *lemma* differentiable.cos
- \- *lemma* differentiable.cosh
- \- *lemma* differentiable.csin
- \- *lemma* differentiable.csinh
- \- *lemma* differentiable.sin
- \- *lemma* differentiable.sinh
- \- *lemma* differentiable_at.ccos
- \- *lemma* differentiable_at.ccosh
- \- *lemma* differentiable_at.cos
- \- *lemma* differentiable_at.cosh
- \- *lemma* differentiable_at.csin
- \- *lemma* differentiable_at.csinh
- \- *lemma* differentiable_at.sin
- \- *lemma* differentiable_at.sinh
- \- *lemma* differentiable_on.ccos
- \- *lemma* differentiable_on.ccosh
- \- *lemma* differentiable_on.cos
- \- *lemma* differentiable_on.cosh
- \- *lemma* differentiable_on.csin
- \- *lemma* differentiable_on.csinh
- \- *lemma* differentiable_on.sin
- \- *lemma* differentiable_on.sinh
- \- *lemma* differentiable_within_at.ccos
- \- *lemma* differentiable_within_at.ccosh
- \- *lemma* differentiable_within_at.cos
- \- *lemma* differentiable_within_at.cosh
- \- *lemma* differentiable_within_at.csin
- \- *lemma* differentiable_within_at.csinh
- \- *lemma* differentiable_within_at.sin
- \- *lemma* differentiable_within_at.sinh
- \- *lemma* fderiv_ccos
- \- *lemma* fderiv_ccosh
- \- *lemma* fderiv_cos
- \- *lemma* fderiv_cosh
- \- *lemma* fderiv_csin
- \- *lemma* fderiv_csinh
- \- *lemma* fderiv_sin
- \- *lemma* fderiv_sinh
- \- *lemma* fderiv_within_ccos
- \- *lemma* fderiv_within_ccosh
- \- *lemma* fderiv_within_cos
- \- *lemma* fderiv_within_cosh
- \- *lemma* fderiv_within_csin
- \- *lemma* fderiv_within_csinh
- \- *lemma* fderiv_within_sin
- \- *lemma* fderiv_within_sinh
- \- *lemma* has_deriv_at.ccos
- \- *lemma* has_deriv_at.ccosh
- \- *lemma* has_deriv_at.cos
- \- *lemma* has_deriv_at.cosh
- \- *lemma* has_deriv_at.csin
- \- *lemma* has_deriv_at.csinh
- \- *lemma* has_deriv_at.sin
- \- *lemma* has_deriv_at.sinh
- \- *lemma* has_deriv_within_at.ccos
- \- *lemma* has_deriv_within_at.ccosh
- \- *lemma* has_deriv_within_at.cos
- \- *lemma* has_deriv_within_at.cosh
- \- *lemma* has_deriv_within_at.csin
- \- *lemma* has_deriv_within_at.csinh
- \- *lemma* has_deriv_within_at.sin
- \- *lemma* has_deriv_within_at.sinh
- \- *lemma* has_fderiv_at.ccos
- \- *lemma* has_fderiv_at.ccosh
- \- *lemma* has_fderiv_at.cos
- \- *lemma* has_fderiv_at.cosh
- \- *lemma* has_fderiv_at.csin
- \- *lemma* has_fderiv_at.csinh
- \- *lemma* has_fderiv_at.sin
- \- *lemma* has_fderiv_at.sinh
- \- *lemma* has_fderiv_within_at.ccos
- \- *lemma* has_fderiv_within_at.ccosh
- \- *lemma* has_fderiv_within_at.cos
- \- *lemma* has_fderiv_within_at.cosh
- \- *lemma* has_fderiv_within_at.csin
- \- *lemma* has_fderiv_within_at.csinh
- \- *lemma* has_fderiv_within_at.sin
- \- *lemma* has_fderiv_within_at.sinh
- \- *lemma* has_strict_deriv_at.ccos
- \- *lemma* has_strict_deriv_at.ccosh
- \- *lemma* has_strict_deriv_at.cos
- \- *lemma* has_strict_deriv_at.cosh
- \- *lemma* has_strict_deriv_at.csin
- \- *lemma* has_strict_deriv_at.csinh
- \- *lemma* has_strict_deriv_at.sin
- \- *lemma* has_strict_deriv_at.sinh
- \- *lemma* has_strict_fderiv_at.ccos
- \- *lemma* has_strict_fderiv_at.ccosh
- \- *lemma* has_strict_fderiv_at.cos
- \- *lemma* has_strict_fderiv_at.cosh
- \- *lemma* has_strict_fderiv_at.csin
- \- *lemma* has_strict_fderiv_at.csinh
- \- *lemma* has_strict_fderiv_at.sin
- \- *lemma* has_strict_fderiv_at.sinh
- \- *lemma* real.deriv_cos'
- \- *lemma* real.deriv_cos
- \- *lemma* real.deriv_cosh
- \- *lemma* real.deriv_sin
- \- *lemma* real.deriv_sinh
- \- *lemma* real.differentiable_at_cos
- \- *lemma* real.differentiable_at_cosh
- \- *lemma* real.differentiable_at_sin
- \- *lemma* real.differentiable_at_sinh
- \- *lemma* real.differentiable_cos
- \- *lemma* real.differentiable_cosh
- \- *lemma* real.differentiable_sin
- \- *lemma* real.differentiable_sinh
- \- *lemma* real.has_deriv_at_cos
- \- *lemma* real.has_deriv_at_cosh
- \- *lemma* real.has_deriv_at_sin
- \- *lemma* real.has_deriv_at_sinh
- \- *lemma* real.has_strict_deriv_at_cos
- \- *lemma* real.has_strict_deriv_at_cosh
- \- *lemma* real.has_strict_deriv_at_sin
- \- *lemma* real.has_strict_deriv_at_sinh
- \- *lemma* real.sinh_strict_mono
- \- *lemma* real.times_cont_diff_cos
- \- *lemma* real.times_cont_diff_cosh
- \- *lemma* real.times_cont_diff_sin
- \- *lemma* real.times_cont_diff_sinh
- \- *lemma* times_cont_diff.ccos
- \- *lemma* times_cont_diff.ccosh
- \- *lemma* times_cont_diff.cos
- \- *lemma* times_cont_diff.cosh
- \- *lemma* times_cont_diff.csin
- \- *lemma* times_cont_diff.csinh
- \- *lemma* times_cont_diff.sin
- \- *lemma* times_cont_diff.sinh
- \- *lemma* times_cont_diff_at.ccos
- \- *lemma* times_cont_diff_at.ccosh
- \- *lemma* times_cont_diff_at.cos
- \- *lemma* times_cont_diff_at.cosh
- \- *lemma* times_cont_diff_at.csin
- \- *lemma* times_cont_diff_at.csinh
- \- *lemma* times_cont_diff_at.sin
- \- *lemma* times_cont_diff_at.sinh
- \- *lemma* times_cont_diff_on.ccos
- \- *lemma* times_cont_diff_on.ccosh
- \- *lemma* times_cont_diff_on.cos
- \- *lemma* times_cont_diff_on.cosh
- \- *lemma* times_cont_diff_on.csin
- \- *lemma* times_cont_diff_on.csinh
- \- *lemma* times_cont_diff_on.sin
- \- *lemma* times_cont_diff_on.sinh
- \- *lemma* times_cont_diff_within_at.ccos
- \- *lemma* times_cont_diff_within_at.ccosh
- \- *lemma* times_cont_diff_within_at.cos
- \- *lemma* times_cont_diff_within_at.cosh
- \- *lemma* times_cont_diff_within_at.csin
- \- *lemma* times_cont_diff_within_at.csinh
- \- *lemma* times_cont_diff_within_at.sin
- \- *lemma* times_cont_diff_within_at.sinh

Added src/analysis/special_functions/trigonometric/deriv.lean
- \+ *lemma* complex.deriv_cos'
- \+ *lemma* complex.deriv_cos
- \+ *lemma* complex.deriv_cosh
- \+ *lemma* complex.deriv_sin
- \+ *lemma* complex.deriv_sinh
- \+ *lemma* complex.differentiable_at_cos
- \+ *lemma* complex.differentiable_at_cosh
- \+ *lemma* complex.differentiable_at_sin
- \+ *lemma* complex.differentiable_at_sinh
- \+ *lemma* complex.differentiable_cos
- \+ *lemma* complex.differentiable_cosh
- \+ *lemma* complex.differentiable_sin
- \+ *lemma* complex.differentiable_sinh
- \+ *lemma* complex.has_deriv_at_cos
- \+ *lemma* complex.has_deriv_at_cosh
- \+ *lemma* complex.has_deriv_at_sin
- \+ *lemma* complex.has_deriv_at_sinh
- \+ *lemma* complex.has_strict_deriv_at_cos
- \+ *lemma* complex.has_strict_deriv_at_cosh
- \+ *lemma* complex.has_strict_deriv_at_sin
- \+ *lemma* complex.has_strict_deriv_at_sinh
- \+ *lemma* complex.times_cont_diff_cos
- \+ *lemma* complex.times_cont_diff_cosh
- \+ *lemma* complex.times_cont_diff_sin
- \+ *lemma* complex.times_cont_diff_sinh
- \+ *lemma* deriv_ccos
- \+ *lemma* deriv_ccosh
- \+ *lemma* deriv_cos
- \+ *lemma* deriv_cosh
- \+ *lemma* deriv_csin
- \+ *lemma* deriv_csinh
- \+ *lemma* deriv_sin
- \+ *lemma* deriv_sinh
- \+ *lemma* deriv_within_ccos
- \+ *lemma* deriv_within_ccosh
- \+ *lemma* deriv_within_cos
- \+ *lemma* deriv_within_cosh
- \+ *lemma* deriv_within_csin
- \+ *lemma* deriv_within_csinh
- \+ *lemma* deriv_within_sin
- \+ *lemma* deriv_within_sinh
- \+ *lemma* differentiable.ccos
- \+ *lemma* differentiable.ccosh
- \+ *lemma* differentiable.cos
- \+ *lemma* differentiable.cosh
- \+ *lemma* differentiable.csin
- \+ *lemma* differentiable.csinh
- \+ *lemma* differentiable.sin
- \+ *lemma* differentiable.sinh
- \+ *lemma* differentiable_at.ccos
- \+ *lemma* differentiable_at.ccosh
- \+ *lemma* differentiable_at.cos
- \+ *lemma* differentiable_at.cosh
- \+ *lemma* differentiable_at.csin
- \+ *lemma* differentiable_at.csinh
- \+ *lemma* differentiable_at.sin
- \+ *lemma* differentiable_at.sinh
- \+ *lemma* differentiable_on.ccos
- \+ *lemma* differentiable_on.ccosh
- \+ *lemma* differentiable_on.cos
- \+ *lemma* differentiable_on.cosh
- \+ *lemma* differentiable_on.csin
- \+ *lemma* differentiable_on.csinh
- \+ *lemma* differentiable_on.sin
- \+ *lemma* differentiable_on.sinh
- \+ *lemma* differentiable_within_at.ccos
- \+ *lemma* differentiable_within_at.ccosh
- \+ *lemma* differentiable_within_at.cos
- \+ *lemma* differentiable_within_at.cosh
- \+ *lemma* differentiable_within_at.csin
- \+ *lemma* differentiable_within_at.csinh
- \+ *lemma* differentiable_within_at.sin
- \+ *lemma* differentiable_within_at.sinh
- \+ *lemma* fderiv_ccos
- \+ *lemma* fderiv_ccosh
- \+ *lemma* fderiv_cos
- \+ *lemma* fderiv_cosh
- \+ *lemma* fderiv_csin
- \+ *lemma* fderiv_csinh
- \+ *lemma* fderiv_sin
- \+ *lemma* fderiv_sinh
- \+ *lemma* fderiv_within_ccos
- \+ *lemma* fderiv_within_ccosh
- \+ *lemma* fderiv_within_cos
- \+ *lemma* fderiv_within_cosh
- \+ *lemma* fderiv_within_csin
- \+ *lemma* fderiv_within_csinh
- \+ *lemma* fderiv_within_sin
- \+ *lemma* fderiv_within_sinh
- \+ *lemma* has_deriv_at.ccos
- \+ *lemma* has_deriv_at.ccosh
- \+ *lemma* has_deriv_at.cos
- \+ *lemma* has_deriv_at.cosh
- \+ *lemma* has_deriv_at.csin
- \+ *lemma* has_deriv_at.csinh
- \+ *lemma* has_deriv_at.sin
- \+ *lemma* has_deriv_at.sinh
- \+ *lemma* has_deriv_within_at.ccos
- \+ *lemma* has_deriv_within_at.ccosh
- \+ *lemma* has_deriv_within_at.cos
- \+ *lemma* has_deriv_within_at.cosh
- \+ *lemma* has_deriv_within_at.csin
- \+ *lemma* has_deriv_within_at.csinh
- \+ *lemma* has_deriv_within_at.sin
- \+ *lemma* has_deriv_within_at.sinh
- \+ *lemma* has_fderiv_at.ccos
- \+ *lemma* has_fderiv_at.ccosh
- \+ *lemma* has_fderiv_at.cos
- \+ *lemma* has_fderiv_at.cosh
- \+ *lemma* has_fderiv_at.csin
- \+ *lemma* has_fderiv_at.csinh
- \+ *lemma* has_fderiv_at.sin
- \+ *lemma* has_fderiv_at.sinh
- \+ *lemma* has_fderiv_within_at.ccos
- \+ *lemma* has_fderiv_within_at.ccosh
- \+ *lemma* has_fderiv_within_at.cos
- \+ *lemma* has_fderiv_within_at.cosh
- \+ *lemma* has_fderiv_within_at.csin
- \+ *lemma* has_fderiv_within_at.csinh
- \+ *lemma* has_fderiv_within_at.sin
- \+ *lemma* has_fderiv_within_at.sinh
- \+ *lemma* has_strict_deriv_at.ccos
- \+ *lemma* has_strict_deriv_at.ccosh
- \+ *lemma* has_strict_deriv_at.cos
- \+ *lemma* has_strict_deriv_at.cosh
- \+ *lemma* has_strict_deriv_at.csin
- \+ *lemma* has_strict_deriv_at.csinh
- \+ *lemma* has_strict_deriv_at.sin
- \+ *lemma* has_strict_deriv_at.sinh
- \+ *lemma* has_strict_fderiv_at.ccos
- \+ *lemma* has_strict_fderiv_at.ccosh
- \+ *lemma* has_strict_fderiv_at.cos
- \+ *lemma* has_strict_fderiv_at.cosh
- \+ *lemma* has_strict_fderiv_at.csin
- \+ *lemma* has_strict_fderiv_at.csinh
- \+ *lemma* has_strict_fderiv_at.sin
- \+ *lemma* has_strict_fderiv_at.sinh
- \+ *lemma* real.deriv_cos'
- \+ *lemma* real.deriv_cos
- \+ *lemma* real.deriv_cosh
- \+ *lemma* real.deriv_sin
- \+ *lemma* real.deriv_sinh
- \+ *lemma* real.differentiable_at_cos
- \+ *lemma* real.differentiable_at_cosh
- \+ *lemma* real.differentiable_at_sin
- \+ *lemma* real.differentiable_at_sinh
- \+ *lemma* real.differentiable_cos
- \+ *lemma* real.differentiable_cosh
- \+ *lemma* real.differentiable_sin
- \+ *lemma* real.differentiable_sinh
- \+ *lemma* real.has_deriv_at_cos
- \+ *lemma* real.has_deriv_at_cosh
- \+ *lemma* real.has_deriv_at_sin
- \+ *lemma* real.has_deriv_at_sinh
- \+ *lemma* real.has_strict_deriv_at_cos
- \+ *lemma* real.has_strict_deriv_at_cosh
- \+ *lemma* real.has_strict_deriv_at_sin
- \+ *lemma* real.has_strict_deriv_at_sinh
- \+ *lemma* real.sinh_strict_mono
- \+ *lemma* real.times_cont_diff_cos
- \+ *lemma* real.times_cont_diff_cosh
- \+ *lemma* real.times_cont_diff_sin
- \+ *lemma* real.times_cont_diff_sinh
- \+ *lemma* times_cont_diff.ccos
- \+ *lemma* times_cont_diff.ccosh
- \+ *lemma* times_cont_diff.cos
- \+ *lemma* times_cont_diff.cosh
- \+ *lemma* times_cont_diff.csin
- \+ *lemma* times_cont_diff.csinh
- \+ *lemma* times_cont_diff.sin
- \+ *lemma* times_cont_diff.sinh
- \+ *lemma* times_cont_diff_at.ccos
- \+ *lemma* times_cont_diff_at.ccosh
- \+ *lemma* times_cont_diff_at.cos
- \+ *lemma* times_cont_diff_at.cosh
- \+ *lemma* times_cont_diff_at.csin
- \+ *lemma* times_cont_diff_at.csinh
- \+ *lemma* times_cont_diff_at.sin
- \+ *lemma* times_cont_diff_at.sinh
- \+ *lemma* times_cont_diff_on.ccos
- \+ *lemma* times_cont_diff_on.ccosh
- \+ *lemma* times_cont_diff_on.cos
- \+ *lemma* times_cont_diff_on.cosh
- \+ *lemma* times_cont_diff_on.csin
- \+ *lemma* times_cont_diff_on.csinh
- \+ *lemma* times_cont_diff_on.sin
- \+ *lemma* times_cont_diff_on.sinh
- \+ *lemma* times_cont_diff_within_at.ccos
- \+ *lemma* times_cont_diff_within_at.ccosh
- \+ *lemma* times_cont_diff_within_at.cos
- \+ *lemma* times_cont_diff_within_at.cosh
- \+ *lemma* times_cont_diff_within_at.csin
- \+ *lemma* times_cont_diff_within_at.csinh
- \+ *lemma* times_cont_diff_within_at.sin
- \+ *lemma* times_cont_diff_within_at.sinh

Modified src/analysis/special_functions/trigonometric/inverse.lean


Modified test/differentiable.lean


Modified test/simp_command.lean




## [2021-11-02 21:57:33](https://github.com/leanprover-community/mathlib/commit/d43daf0)
feat(algebra/big_operators/order): add unbundled is_absolute_value.sum_le and map_prod ([#10104](https://github.com/leanprover-community/mathlib/pull/10104))
Add unbundled versions of two existing lemmas.
Additionally generalize a few typeclass assumptions in an earlier file.
From the flt-regular project
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *lemma* is_absolute_value.abv_sum
- \+ *lemma* is_absolute_value.map_prod

Modified src/algebra/order/absolute_value.lean




## [2021-11-02 21:57:32](https://github.com/leanprover-community/mathlib/commit/3accc5e)
feat(data/bool): bnot_iff_not ([#10095](https://github.com/leanprover-community/mathlib/pull/10095))
#### Estimated changes
Modified src/data/bool.lean
- \+ *theorem* bool.bnot_iff_not



## [2021-11-02 19:48:57](https://github.com/leanprover-community/mathlib/commit/00064bd)
feat(logic/relation): add equivalence.comap ([#10103](https://github.com/leanprover-community/mathlib/pull/10103))
#### Estimated changes
Modified src/data/setoid/basic.lean


Modified src/group_theory/congruence.lean


Modified src/logic/relation.lean
- \+ *lemma* equivalence.comap



## [2021-11-02 19:05:42](https://github.com/leanprover-community/mathlib/commit/2d8be73)
chore(measure_theory/probability_mass_function): avoid non-terminal simp in coe_le_one ([#10112](https://github.com/leanprover-community/mathlib/pull/10112))
#### Estimated changes
Modified src/measure_theory/probability_mass_function.lean




## [2021-11-02 16:26:32](https://github.com/leanprover-community/mathlib/commit/6df3143)
chore(combinatorics/choose/bounds): move to nat namespace ([#10106](https://github.com/leanprover-community/mathlib/pull/10106))
There are module docstrings elsewhere that expect this to be in the `nat` namespace with the other `choose` lemmas.
#### Estimated changes
Modified src/combinatorics/choose/bounds.lean
- \- *lemma* choose_le_pow
- \+ *lemma* nat.choose_le_pow
- \+ *lemma* nat.pow_le_choose
- \- *lemma* pow_le_choose



## [2021-11-02 15:51:48](https://github.com/leanprover-community/mathlib/commit/0dcb184)
style(testing/slim_check): fix line length ([#10114](https://github.com/leanprover-community/mathlib/pull/10114))
#### Estimated changes
Modified src/testing/slim_check/testable.lean




## [2021-11-02 14:14:07](https://github.com/leanprover-community/mathlib/commit/796a051)
feat(measure_theory/decomposition/lebesgue): more on Radon-Nikodym derivatives ([#10070](https://github.com/leanprover-community/mathlib/pull/10070))
We show that the density in the Lebesgue decomposition theorem (aka the Radon-Nikodym derivative) is unique. Previously, uniqueness of the absolutely continuous part was known, but not of its density. We also show that the Radon-Nikodym derivative is almost everywhere finite. Plus some cleanup of the whole file.
#### Estimated changes
Modified src/measure_theory/decomposition/jordan.lean


Modified src/measure_theory/decomposition/lebesgue.lean
- \+/\- *theorem* measure_theory.measure.eq_rn_deriv
- \+ *theorem* measure_theory.measure.eq_with_density_rn_deriv
- \+ *lemma* measure_theory.measure.lintegral_rn_deriv_lt_top_of_measure_ne_top
- \+ *theorem* measure_theory.measure.rn_deriv_lt_top
- \+ *theorem* measure_theory.measure.rn_deriv_with_density
- \+/\- *lemma* measure_theory.measure.singular_part_le
- \+ *lemma* measure_theory.measure.singular_part_with_density

Modified src/measure_theory/function/ae_eq_of_integral.lean
- \+ *lemma* measure_theory.ae_eq_of_forall_set_lintegral_eq_of_sigma_finite
- \+ *lemma* measure_theory.ae_le_of_forall_set_lintegral_le_of_sigma_finite
- \+/\- *lemma* measure_theory.ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.ae_of_forall_measure_lt_top_ae_restrict
- \+ *lemma* measure_theory.eventually_mem_spanning_sets
- \+ *lemma* measure_theory.measure.is_locally_finite_measure_of_le
- \- *lemma* measure_theory.measure.mutually_singular.zero
- \+ *lemma* measure_theory.measure.mutually_singular.zero_left
- \+ *lemma* measure_theory.measure.mutually_singular.zero_right
- \+ *lemma* measure_theory.mem_spanning_sets_of_index_le

Modified src/probability_theory/density.lean




## [2021-11-02 12:07:49](https://github.com/leanprover-community/mathlib/commit/da6706d)
feat(data/mv_polynomial/basic): lemmas about map ([#10092](https://github.com/leanprover-community/mathlib/pull/10092))
This adds `map_alg_hom`, which fills the gap between `map` and `map_alg_equiv`.
The only new proof here is `map_surjective`; everything else is just a reworked existing proof.
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *def* mv_polynomial.map_alg_hom
- \+ *lemma* mv_polynomial.map_alg_hom_id
- \+ *lemma* mv_polynomial.map_left_inverse
- \+ *lemma* mv_polynomial.map_right_inverse
- \+ *lemma* mv_polynomial.map_surjective

Modified src/data/mv_polynomial/equiv.lean
- \- *lemma* mv_polynomial.map_alg_equiv_apply



## [2021-11-02 10:26:34](https://github.com/leanprover-community/mathlib/commit/80dc445)
refactor(order/bounded_lattice): generalize le on with_{top,bot} ([#10085](https://github.com/leanprover-community/mathlib/pull/10085))
Before, some lemmas assumed `preorder` even when they were true for
just the underlying `le`. In the case of `with_bot`, the missing
underlying `has_le` instance is defined.
For both `with_{top,bot}`, a few lemmas are generalized accordingly.
#### Estimated changes
Modified src/data/nat/cast.lean


Modified src/order/bounded_lattice.lean
- \+/\- *theorem* with_bot.coe_le
- \+/\- *theorem* with_bot.coe_le_coe
- \+/\- *lemma* with_bot.coe_lt_coe
- \+/\- *theorem* with_bot.some_le_some
- \+/\- *theorem* with_top.coe_le_coe
- \+/\- *lemma* with_top.coe_lt_coe
- \+/\- *lemma* with_top.coe_lt_top
- \+/\- *theorem* with_top.le_coe



## [2021-11-02 10:26:33](https://github.com/leanprover-community/mathlib/commit/658a3d7)
refactor(algebra/algebra): remove subalgebra.under ([#10081](https://github.com/leanprover-community/mathlib/pull/10081))
This removes `subalgebra.under`, and replaces `subalgebra.of_under` with `subalgebra.of_restrict_scalars`.
Lemmas associated with `under` have been renamed accordingly.
#### Estimated changes
Modified src/algebra/algebra/tower.lean
- \+ *theorem* is_scalar_tower.adjoin_range_to_alg_hom
- \- *theorem* is_scalar_tower.range_under_adjoin
- \- *lemma* subalgebra.mem_under
- \+ *def* subalgebra.of_restrict_scalars
- \- *def* subalgebra.of_under
- \- *def* subalgebra.under

Modified src/field_theory/is_alg_closed/basic.lean


Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/adjoin/basic.lean
- \+ *theorem* algebra.adjoin_union_eq_adjoin_adjoin
- \- *theorem* algebra.adjoin_union_eq_under

Modified src/ring_theory/adjoin/fg.lean


Modified src/ring_theory/algebra_tower.lean




## [2021-11-02 10:26:32](https://github.com/leanprover-community/mathlib/commit/541df8a)
feat(topology/algebra/ordered/liminf_limsup): convergence of a sequence which does not oscillate infinitely ([#10073](https://github.com/leanprover-community/mathlib/pull/10073))
If, for all `a < b`, a sequence is not frequently below `a` and frequently above `b`, then it has to converge. This is a useful convergence criterion (called no upcrossings), used for instance in martingales.
Also generalize several statements on liminfs and limsups from complete linear orders to conditionally complete linear orders.
#### Estimated changes
Modified src/order/liminf_limsup.lean
- \+ *lemma* filter.is_bounded.is_cobounded_ge
- \+ *lemma* filter.is_bounded.is_cobounded_le
- \+/\- *lemma* filter.liminf_le_limsup

Modified src/topology/algebra/ordered/liminf_limsup.lean
- \+ *lemma* tendsto_of_no_upcrossings



## [2021-11-02 10:26:31](https://github.com/leanprover-community/mathlib/commit/880182d)
chore(analysis/normed/group): add `cauchy_seq_finset_of_norm_bounded_eventually` ([#10060](https://github.com/leanprover-community/mathlib/pull/10060))
Add `cauchy_seq_finset_of_norm_bounded_eventually`, use it to golf some proofs.
#### Estimated changes
Modified src/analysis/normed/group/infinite_sum.lean
- \+ *lemma* cauchy_seq_finset_of_norm_bounded_eventually



## [2021-11-02 10:26:30](https://github.com/leanprover-community/mathlib/commit/fc12ca8)
feat(measure_theory/probability_mass_function): Define uniform pmf on an inhabited fintype ([#9920](https://github.com/leanprover-community/mathlib/pull/9920))
This PR defines uniform probability mass functions on nonempty finsets and inhabited fintypes.
#### Estimated changes
Modified src/measure_theory/probability_mass_function.lean
- \+ *lemma* pmf.bernuolli_apply
- \+ *def* pmf.of_finset
- \+ *lemma* pmf.of_finset_apply
- \+ *lemma* pmf.of_finset_apply_of_not_mem
- \+ *lemma* pmf.of_fintype_apply
- \+ *lemma* pmf.of_multiset_apply
- \+ *lemma* pmf.of_multiset_apply_of_not_mem
- \+ *def* pmf.uniform_of_finset
- \+ *lemma* pmf.uniform_of_finset_apply
- \+ *lemma* pmf.uniform_of_finset_apply_of_mem
- \+ *lemma* pmf.uniform_of_finset_apply_of_not_mem
- \+ *def* pmf.uniform_of_fintype
- \+ *lemma* pmf.uniform_of_fintype_apply



## [2021-11-02 09:31:35](https://github.com/leanprover-community/mathlib/commit/f6894c4)
chore(ring_theory/adjoin/fg): generalize ring to semiring in a few places ([#10089](https://github.com/leanprover-community/mathlib/pull/10089))
#### Estimated changes
Modified src/ring_theory/adjoin/fg.lean




## [2021-11-02 08:23:22](https://github.com/leanprover-community/mathlib/commit/26bdcac)
chore(coinductive_predicates): remove private and use of import_private ([#10084](https://github.com/leanprover-community/mathlib/pull/10084))
Remove a `private` modifier (I think this had previously been ported from core by @bryangingechen).
Then remove the only use of `import_private` from the library. (Besides another use in `tests/`, which we're not porting.)
(In mathlib4 we have `OpenPrivate` as an alternative. Removing `import_private` is one less thing for mathport to care about.)
#### Estimated changes
Modified src/algebra/lie/weights.lean


Modified src/meta/coinductive_predicates.lean


Modified test/coinductive.lean




## [2021-11-02 08:23:21](https://github.com/leanprover-community/mathlib/commit/1852840)
feat(analysis/calculus/mean_value): Strict convexity from derivatives ([#10034](https://github.com/leanprover-community/mathlib/pull/10034))
This duplicates all the results relating convex/concave function and their derivatives to strictly convex/strictly concave functions.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean
- \- *theorem* antitone.concave_on_univ
- \+ *theorem* antitone.concave_on_univ_of_deriv
- \+ *theorem* antitone_on.concave_on_of_deriv
- \- *theorem* concave_on_of_deriv_antitone_on
- \- *theorem* convex_on_of_deriv_monotone_on
- \- *theorem* convex_on_univ_of_deriv_monotone
- \+ *theorem* monotone.convex_on_univ_of_deriv
- \+ *theorem* monotone_on.convex_on_of_deriv
- \+ *lemma* strict_anti.strict_concave_on_univ_of_deriv
- \+ *lemma* strict_anti_on.strict_concave_on_of_deriv
- \+ *lemma* strict_concave_on_of_deriv2_neg
- \+ *lemma* strict_concave_on_open_of_deriv2_neg
- \+ *lemma* strict_concave_on_univ_of_deriv2_neg
- \+ *lemma* strict_convex_on_of_deriv2_pos
- \+ *lemma* strict_convex_on_open_of_deriv2_pos
- \+ *lemma* strict_convex_on_univ_of_deriv2_pos
- \+ *lemma* strict_mono.strict_convex_on_univ_of_deriv
- \+ *lemma* strict_mono_on.strict_convex_on_of_deriv



## [2021-11-02 06:43:08](https://github.com/leanprover-community/mathlib/commit/6d2af9a)
chore(data/list/defs): remove unneeded open ([#10100](https://github.com/leanprover-community/mathlib/pull/10100))
#### Estimated changes
Modified src/data/list/defs.lean




## [2021-11-02 02:55:19](https://github.com/leanprover-community/mathlib/commit/d926ac7)
chore(scripts): update nolints.txt ([#10098](https://github.com/leanprover-community/mathlib/pull/10098))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-11-01 21:07:30](https://github.com/leanprover-community/mathlib/commit/fd783e3)
chore(algebra/free_algebra): remove a heavy and unecessary import ([#10093](https://github.com/leanprover-community/mathlib/pull/10093))
`transfer_instance` pulls in category theory, which is overkill
#### Estimated changes
Modified src/algebra/free_algebra.lean




## [2021-11-01 20:14:44](https://github.com/leanprover-community/mathlib/commit/b1d5446)
chore(analysis/normed_space/operator_norm): remove an import to data.equiv.transfer_instance ([#10094](https://github.com/leanprover-community/mathlib/pull/10094))
This import isn't needed, and the spelling without it is shorter.
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean




## [2021-11-01 12:55:31](https://github.com/leanprover-community/mathlib/commit/0144b6c)
chore({data/finset,data/multiset,order}/locally_finite): Better line wraps ([#10087](https://github.com/leanprover-community/mathlib/pull/10087))
#### Estimated changes
Modified src/data/finset/locally_finite.lean
- \+/\- *lemma* finset.Icc_eq_empty_of_lt
- \+/\- *lemma* finset.Icc_self
- \+/\- *lemma* finset.Ico_eq_empty_of_le
- \+/\- *lemma* finset.Ico_self
- \+/\- *lemma* finset.Ioc_eq_empty_of_le
- \+/\- *lemma* finset.Ioc_self
- \+/\- *lemma* finset.Ioo_eq_empty_of_le
- \+/\- *lemma* finset.Ioo_self

Modified src/data/multiset/locally_finite.lean
- \+/\- *lemma* multiset.Icc_eq_zero_of_lt
- \+/\- *lemma* multiset.Icc_self
- \+/\- *lemma* multiset.Ioc_eq_zero_of_le
- \+/\- *lemma* multiset.Ioc_self
- \+/\- *lemma* multiset.Ioo_eq_zero_of_le
- \+/\- *lemma* multiset.Ioo_self

Modified src/order/locally_finite.lean
- \+/\- *def* finset.Icc
- \+/\- *def* finset.Ico
- \+/\- *theorem* finset.Ico_subset_Ico
- \+/\- *def* finset.Iic
- \+/\- *def* finset.Iio
- \+/\- *def* finset.Ioc
- \+/\- *def* finset.Ioo
- \+/\- *lemma* finset.mem_Ici
- \+/\- *lemma* finset.mem_Iic
- \+/\- *lemma* finset.mem_Iio
- \+/\- *lemma* finset.mem_Ioi
- \+/\- *def* multiset.Icc
- \+/\- *def* multiset.Ici
- \+/\- *def* multiset.Iic
- \+/\- *def* multiset.Iio
- \+/\- *def* multiset.Ioc
- \+/\- *def* multiset.Ioi
- \+/\- *def* multiset.Ioo
- \+/\- *lemma* multiset.mem_Ici
- \+/\- *lemma* multiset.mem_Iic
- \+/\- *lemma* multiset.mem_Iio
- \+/\- *lemma* multiset.mem_Ioi
- \+/\- *lemma* set.finite_Ici
- \+/\- *lemma* set.finite_Iic
- \+/\- *lemma* set.finite_Iio
- \+/\- *lemma* set.finite_Ioi



## [2021-11-01 12:22:20](https://github.com/leanprover-community/mathlib/commit/fef1535)
chore(category_theory/limits): reuse a previous result ([#10088](https://github.com/leanprover-community/mathlib/pull/10088))
#### Estimated changes
Modified src/category_theory/limits/shapes/kernel_pair.lean




## [2021-11-01 11:06:34](https://github.com/leanprover-community/mathlib/commit/9ef310f)
chore(algebra/algebra): implement subalgebra.under in terms of restrict_scalars ([#10080](https://github.com/leanprover-community/mathlib/pull/10080))
We should probably remove `subalgebra.under` entirely, but that's likely a lot more work.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \- *lemma* subalgebra.mem_under
- \- *def* subalgebra.under

Modified src/algebra/algebra/tower.lean
- \+ *lemma* subalgebra.mem_under
- \+ *def* subalgebra.under

Modified src/ring_theory/adjoin/basic.lean
- \+/\- *theorem* algebra.adjoin_induction



## [2021-11-01 11:06:33](https://github.com/leanprover-community/mathlib/commit/17ebcf0)
chore(ring_theory/algebra_tower): relax typeclasses ([#10078](https://github.com/leanprover-community/mathlib/pull/10078))
This generalizes some `comm_ring`s to `comm_semiring`s.
Split from [#10024](https://github.com/leanprover-community/mathlib/pull/10024)
#### Estimated changes
Modified src/ring_theory/algebra_tower.lean
- \+/\- *lemma* algebra.fg_trans'
- \+/\- *lemma* basis.algebra_map_injective



## [2021-11-01 10:12:40](https://github.com/leanprover-community/mathlib/commit/23892a0)
chore(analysis/normed_space/operator_norm): semilinearize part of the file ([#10076](https://github.com/leanprover-community/mathlib/pull/10076))
This PR generalizes part of the `operator_norm` file to semilinear maps. Only the first section (`semi_normed`) is done, which allows us to construct continuous semilinear maps using `linear_map.mk_continuous`.
The rest of the file is trickier, since we need specify how the ring hom interacts with the norm. I'd rather leave it to a future PR since I don't need the rest now.
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* continuous_of_linear_of_bound
- \+ *lemma* continuous_of_linear_of_boundₛₗ
- \+/\- *def* linear_map.mk_continuous
- \+/\- *def* linear_map.mk_continuous_of_exists_bound

Modified src/measure_theory/integral/set_integral.lean




## [2021-11-01 07:01:57](https://github.com/leanprover-community/mathlib/commit/85fe90e)
feat(algebra/direct_sum/module) : coe and internal ([#10004](https://github.com/leanprover-community/mathlib/pull/10004))
This extracts the following `def`s from within the various `is_internal` properties:
* `direct_sum.add_submonoid_coe`
* `direct_sum.add_subgroup_coe`
* `direct_sum.submodule_coe`
Packing these into a def makes things more concise, and avoids some annoying elaboration issues.
#### Estimated changes
Modified src/algebra/direct_sum/basic.lean
- \+ *def* direct_sum.add_subgroup_coe
- \+ *lemma* direct_sum.add_subgroup_coe_of
- \+ *def* direct_sum.add_submonoid_coe
- \+ *lemma* direct_sum.add_submonoid_coe_of

Modified src/algebra/direct_sum/module.lean
- \+ *def* direct_sum.submodule_coe
- \+ *lemma* direct_sum.submodule_coe_of



## [2021-11-01 05:31:03](https://github.com/leanprover-community/mathlib/commit/acc504e)
docs(category_theory/*): add missing module docs ([#9990](https://github.com/leanprover-community/mathlib/pull/9990))
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/fully_faithful.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/full_subcategory.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/products/bifunctor.lean




## [2021-11-01 02:38:33](https://github.com/leanprover-community/mathlib/commit/e8fa232)
chore(scripts): update nolints.txt ([#10083](https://github.com/leanprover-community/mathlib/pull/10083))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-11-01 00:38:30](https://github.com/leanprover-community/mathlib/commit/cd457a5)
fix(data/{rbtree,rbmap}): fix some lint errors ([#10036](https://github.com/leanprover-community/mathlib/pull/10036))
#### Estimated changes
Modified src/data/rbmap/default.lean
- \+/\- *lemma* rbmap.eq_leaf_of_max_eq_none
- \+/\- *lemma* rbmap.eq_leaf_of_min_eq_none

Modified src/data/rbtree/basic.lean
- \+/\- *lemma* rbnode.balanced
- \+/\- *lemma* rbnode.depth_min

Modified src/data/rbtree/find.lean
- \+/\- *lemma* rbnode.eqv_of_find_some

Modified src/data/rbtree/insert.lean
- \+/\- *lemma* rbnode.equiv_or_mem_of_mem_ins
- \+/\- *lemma* rbnode.equiv_or_mem_of_mem_insert
- \+/\- *lemma* rbnode.find_balance1_node
- \+/\- *lemma* rbnode.find_balance2_node
- \+/\- *lemma* rbnode.find_black_eq_find_red
- \+/\- *lemma* rbnode.find_ins_of_eqv
- \+/\- *lemma* rbnode.find_insert_of_disj
- \+/\- *lemma* rbnode.find_insert_of_eqv
- \+/\- *lemma* rbnode.find_insert_of_not_eqv
- \+/\- *lemma* rbnode.find_mk_insert_result
- \+/\- *lemma* rbnode.find_red_of_gt
- \+/\- *lemma* rbnode.find_red_of_incomp
- \+/\- *lemma* rbnode.find_red_of_lt
- \+/\- *lemma* rbnode.ins.induction
- \+/\- *lemma* rbnode.ins_ne_leaf
- \+/\- *lemma* rbnode.insert_ne_leaf
- \+/\- *lemma* rbnode.is_searchable_ins
- \+/\- *lemma* rbnode.is_searchable_insert
- \+/\- *lemma* rbnode.ite_eq_of_not_lt
- \+/\- *lemma* rbnode.mem_ins_of_incomp
- \+/\- *lemma* rbnode.mem_ins_of_mem
- \+/\- *lemma* rbnode.mem_insert_of_incomp
- \+/\- *lemma* rbnode.mem_insert_of_mem
- \+/\- *lemma* rbnode.of_mem_balance1_node
- \+/\- *lemma* rbnode.of_mem_balance2_node

Modified src/data/rbtree/main.lean
- \+/\- *lemma* rbtree.balanced
- \+/\- *lemma* rbtree.eq_leaf_of_max_eq_none
- \+/\- *lemma* rbtree.eq_leaf_of_min_eq_none

Modified src/data/rbtree/min_max.lean




## [2021-11-01 00:38:28](https://github.com/leanprover-community/mathlib/commit/bf82122)
feat(algebra/direct_sum/basic): some lemmas about `direct_sum.of` ([#10003](https://github.com/leanprover-community/mathlib/pull/10003))
Some small lemmas about `direct_sum.of` that are handy.
#### Estimated changes
Modified src/algebra/direct_sum/basic.lean
- \+ *lemma* direct_sum.of_eq_of_ne
- \+ *lemma* direct_sum.of_eq_same
- \+ *lemma* direct_sum.sum_support_of
- \+ *lemma* direct_sum.support_of
- \+ *lemma* direct_sum.support_of_subset
- \+ *lemma* direct_sum.support_zero

