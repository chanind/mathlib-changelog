## [2021-11-30 16:52:36](https://github.com/leanprover-community/mathlib/commit/49f8b6b)
chore(analysis/mean_inequalities[_pow]): use vector notation ([#10546](https://github.com/leanprover-community/mathlib/pull/10546))
Several elementary inequalities in the library are expressed both in arbitrary n-ary versions and in explicit binary, ternary etc versions, with the latter deduced from the former.  This PR introduces vector notation to the proof terms deducing the latter from the former, which shortens them, and also makes them more readable.
#### Estimated changes
modified src/analysis/mean_inequalities.lean

modified src/analysis/mean_inequalities_pow.lean



## [2021-11-30 16:52:35](https://github.com/leanprover-community/mathlib/commit/b876e76)
feat(algebra/char_p/two): couple more lemmas + 🏌️ ([#10467](https://github.com/leanprover-community/mathlib/pull/10467))
#### Estimated changes
modified src/algebra/char_p/two.lean
- \+ *lemma* neg_one_eq_one_iff
- \+ *lemma* order_of_neg_one

modified src/ring_theory/roots_of_unity.lean
- \+/\- *lemma* neg_one
- \+/\- *lemma* neg_one



## [2021-11-30 15:07:49](https://github.com/leanprover-community/mathlib/commit/cd69351)
doc(data/stream/defs): add docstrings to most defs ([#10547](https://github.com/leanprover-community/mathlib/pull/10547))
Also move 1 def from `basic` to `defs`.
#### Estimated changes
modified src/control/random.lean

modified src/data/stream/basic.lean
- \- *def* corec_state

modified src/data/stream/defs.lean
- \+/\- *def* head
- \+/\- *def* nth
- \+ *def* corec_state
- \+/\- *def* head
- \+/\- *def* nth



## [2021-11-30 15:07:48](https://github.com/leanprover-community/mathlib/commit/8bce7eb)
refactor(algebra/group/basic): Migrate `add_group` section into `group` section ([#10532](https://github.com/leanprover-community/mathlib/pull/10532))
#### Estimated changes
modified src/algebra/group/basic.lean
- \+/\- *lemma* mul_div_assoc
- \+ *lemma* div_self'
- \+ *lemma* mul_div_cancel''
- \+ *lemma* eq_of_div_eq_one'
- \+ *lemma* div_ne_one_of_ne
- \+ *lemma* div_inv_eq_mul
- \+ *lemma* mul_div
- \+ *lemma* div_mul_eq_div_div_swap
- \+ *lemma* mul_div_mul_right_eq_div
- \+ *lemma* eq_div_of_mul_eq'
- \+ *lemma* div_eq_of_eq_mul''
- \+ *lemma* eq_mul_of_div_eq
- \+ *lemma* mul_eq_of_eq_div
- \+ *lemma* div_right_inj
- \+ *lemma* div_left_inj
- \+ *lemma* div_mul_div_cancel'
- \+ *lemma* div_div_div_cancel_right'
- \+/\- *lemma* mul_div_assoc
- \- *lemma* sub_self
- \- *lemma* add_sub_cancel
- \- *lemma* add_sub_assoc
- \- *lemma* eq_of_sub_eq_zero
- \- *lemma* sub_ne_zero_of_ne
- \- *lemma* sub_neg_eq_add
- \- *lemma* add_sub
- \- *lemma* sub_add_eq_sub_sub_swap
- \- *lemma* add_sub_add_right_eq_sub
- \- *lemma* eq_sub_of_add_eq
- \- *lemma* sub_eq_of_eq_add
- \- *lemma* eq_add_of_sub_eq
- \- *lemma* add_eq_of_eq_sub
- \- *lemma* sub_right_inj
- \- *lemma* sub_left_inj
- \- *lemma* sub_add_sub_cancel
- \- *lemma* sub_sub_sub_cancel_right
- \+ *theorem* div_div_assoc_swap
- \+ *theorem* div_eq_one
- \+ *theorem* div_ne_one
- \+ *theorem* div_eq_self
- \+ *theorem* eq_div_iff_mul_eq'
- \+ *theorem* div_eq_iff_eq_mul
- \+ *theorem* eq_iff_eq_of_div_eq_div
- \+ *theorem* left_inverse_div_mul_left
- \+ *theorem* left_inverse_mul_left_div
- \+ *theorem* left_inverse_mul_right_inv_mul
- \+ *theorem* left_inverse_inv_mul_mul_right
- \- *theorem* sub_sub_assoc_swap
- \- *theorem* sub_eq_zero
- \- *theorem* sub_ne_zero
- \- *theorem* sub_eq_self
- \- *theorem* eq_sub_iff_add_eq
- \- *theorem* sub_eq_iff_eq_add
- \- *theorem* eq_iff_eq_of_sub_eq_sub
- \- *theorem* left_inverse_sub_add_left
- \- *theorem* left_inverse_add_left_sub
- \- *theorem* left_inverse_add_right_neg_add
- \- *theorem* left_inverse_neg_add_add_right



## [2021-11-30 13:24:44](https://github.com/leanprover-community/mathlib/commit/41fa32b)
feat(data/nat/pairing): add an `equiv` version of `nat.mkpair`/`nat.unpair` ([#10520](https://github.com/leanprover-community/mathlib/pull/10520))
#### Estimated changes
modified src/data/nat/pairing.lean
- \+ *lemma* mkpair_eq_mkpair
- \+ *def* mkpair_equiv



## [2021-11-30 13:24:43](https://github.com/leanprover-community/mathlib/commit/af5c778)
feat(topology/[continuous_function, path_connected]): add bundled versions of prod_mk and prod_map ([#10512](https://github.com/leanprover-community/mathlib/pull/10512))
I also added a definition for pointwise addition of paths, but I'm not sure it would be really useful in general (my use case is the Sphere eversion project, where I need to add together two paths living in complement subspaces of a real TVS).
#### Estimated changes
modified src/topology/continuous_function/basic.lean
- \+ *def* prod_mk
- \+ *def* prod_map

modified src/topology/path_connected.lean



## [2021-11-30 13:24:41](https://github.com/leanprover-community/mathlib/commit/4d90ff9)
feat(topology/connected): Connectedness in sum and sigma type ([#10511](https://github.com/leanprover-community/mathlib/pull/10511))
This provides the `compact_space` and `totally_disconnected_space` instances for `α ⊕ β` and `Σ i, π i`.
#### Estimated changes
modified src/data/set/lattice.lean
- \+ *lemma* sigma.univ

modified src/topology/connected.lean
- \+ *lemma* sigma.is_connected_iff
- \+ *lemma* sigma.is_preconnected_iff
- \+ *lemma* sum.is_connected_iff
- \+ *lemma* sum.is_preconnected_iff
- \+/\- *theorem* is_preconnected_univ_pi
- \+/\- *theorem* is_connected_univ_pi
- \+/\- *theorem* is_preconnected_univ_pi
- \+/\- *theorem* is_connected_univ_pi

modified src/topology/constructions.lean
- \+ *lemma* is_open_sigma_fst_preimage

modified src/topology/subset_properties.lean
- \+ *lemma* clopen_range_sigma_mk



## [2021-11-30 13:24:39](https://github.com/leanprover-community/mathlib/commit/7356269)
feat(linear_algebra/affine_space/basis): upgrade `affine_basis.coords` to an affine map ([#10452](https://github.com/leanprover-community/mathlib/pull/10452))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/linear_algebra/affine_space/basis.lean
- \+ *lemma* coe_linear



## [2021-11-30 12:39:15](https://github.com/leanprover-community/mathlib/commit/35574bb)
fix(*): replace "the the" by "the" ([#10548](https://github.com/leanprover-community/mathlib/pull/10548))
#### Estimated changes
modified src/linear_algebra/affine_space/basis.lean

modified src/topology/sheaves/sheaf_condition/sites.lean



## [2021-11-30 11:49:06](https://github.com/leanprover-community/mathlib/commit/1077f34)
feat(algebraic_geometry): Generalized basic open for arbitrary sections ([#10515](https://github.com/leanprover-community/mathlib/pull/10515))
#### Estimated changes
modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *lemma* preimage_basic_open

modified src/algebraic_geometry/ringed_space.lean
- \+/\- *lemma* mem_basic_open
- \+ *lemma* basic_open_subset
- \+/\- *lemma* is_unit_res_basic_open
- \+ *lemma* basic_open_res
- \+/\- *lemma* mem_basic_open
- \+/\- *lemma* is_unit_res_basic_open
- \+/\- *def* basic_open
- \+/\- *def* basic_open



## [2021-11-30 10:08:21](https://github.com/leanprover-community/mathlib/commit/6102d77)
feat(group_theory/submonoid/pointwise): pointwise inverse of a submonoid ([#10451](https://github.com/leanprover-community/mathlib/pull/10451))
This also adds `order_iso.map_{supr,infi,Sup,Inf}` which are used here to provide some short proofs.
#### Estimated changes
modified src/algebra/pointwise.lean
- \+ *lemma* Inter_inv
- \+ *lemma* Union_inv

modified src/group_theory/submonoid/pointwise.lean
- \+ *lemma* coe_inv
- \+ *lemma* mem_inv
- \+ *lemma* inv_le_inv
- \+ *lemma* inv_le
- \+ *lemma* closure_inv
- \+ *lemma* inv_inf
- \+ *lemma* inv_sup
- \+ *lemma* inv_bot
- \+ *lemma* inv_top
- \+ *lemma* inv_infi
- \+ *lemma* inv_supr
- \+ *def* inv_order_iso

modified src/order/complete_lattice.lean
- \+ *lemma* order_iso.map_supr
- \+ *lemma* order_iso.map_Sup
- \+ *lemma* order_iso.map_infi
- \+ *lemma* order_iso.map_Inf



## [2021-11-30 07:29:05](https://github.com/leanprover-community/mathlib/commit/4a9aa27)
feat(analysis/normed_space/spectrum and algebra/algebra/spectrum): prove properties of spectrum in a Banach algebra ([#10530](https://github.com/leanprover-community/mathlib/pull/10530))
Prove that the `spectrum` of an element in a Banach algebra is closed and bounded, hence compact when the scalar field is                               
proper. Compute the derivative of the `resolvent a` function in preparation for showing that the spectrum is nonempty when  the base field is ℂ. Define the `spectral_radius` and prove that it is bounded by the norm. Also rename the resolvent set to `resolvent_set` instead of `resolvent` so that it doesn't clash with the function name.
#### Estimated changes
modified src/algebra/algebra/spectrum.lean
- \+ *lemma* mem_resolvent_set_of_left_right_inverse
- \+ *lemma* mem_resolvent_set_iff
- \+ *lemma* resolvent_eq
- \- *lemma* mem_resolvent_of_left_right_inverse
- \- *lemma* mem_resolvent_iff
- \+ *def* resolvent_set
- \- *def* resolvent

created src/analysis/normed_space/spectrum.lean
- \+ *lemma* is_open_resolvent_set
- \+ *lemma* is_closed
- \+ *lemma* mem_resolvent_of_norm_lt
- \+ *lemma* norm_le_norm_of_mem
- \+ *lemma* subset_closed_ball_norm
- \+ *lemma* is_bounded
- \+ *theorem* is_compact
- \+ *theorem* spectral_radius_le_nnnorm
- \+ *theorem* has_deriv_at_resolvent



## [2021-11-30 06:50:40](https://github.com/leanprover-community/mathlib/commit/f11d505)
feat(category_theory/sites/compatible_*): Compatibility of plus and sheafification with composition. ([#10510](https://github.com/leanprover-community/mathlib/pull/10510))
Compatibility of sheafification with composition. This will be used later to obtain adjunctions between categories of sheaves.
#### Estimated changes
created src/category_theory/sites/compatible_plus.lean
- \+ *lemma* diagram_comp_iso_hom_ι
- \+ *lemma* ι_plus_comp_iso_hom
- \+ *lemma* plus_comp_iso_whisker_left
- \+ *lemma* plus_comp_iso_whisker_right
- \+ *lemma* whisker_right_to_plus_comp_plus_comp_iso_hom
- \+ *lemma* to_plus_comp_plus_comp_iso_inv
- \+ *lemma* plus_comp_iso_inv_eq_plus_lift
- \+ *def* diagram_comp_iso
- \+ *def* plus_comp_iso
- \+ *def* plus_functor_whisker_left_iso
- \+ *def* plus_functor_whisker_right_iso

created src/category_theory/sites/compatible_sheafification.lean
- \+ *lemma* sheafification_whisker_left_iso_hom_app
- \+ *lemma* sheafification_whisker_left_iso_inv_app
- \+ *lemma* sheafification_whisker_right_iso_hom_app
- \+ *lemma* sheafification_whisker_right_iso_inv_app
- \+ *lemma* whisker_right_to_sheafify_sheafify_comp_iso_hom
- \+ *lemma* to_sheafify_comp_sheafify_comp_iso_inv
- \+ *lemma* sheafify_comp_iso_inv_eq_sheafify_lift
- \+ *def* sheafify_comp_iso
- \+ *def* sheafification_whisker_left_iso
- \+ *def* sheafification_whisker_right_iso

modified src/category_theory/sites/plus.lean
- \+ *lemma* diagram_nat_trans_id
- \+ *lemma* diagram_nat_trans_comp
- \+ *lemma* plus_map_id
- \+ *lemma* plus_map_comp
- \+ *lemma* to_plus_naturality
- \+ *def* diagram_nat_trans

modified src/category_theory/sites/sheafification.lean
- \+ *lemma* sheafification_map_sheafify_lift
- \+ *lemma* grothendieck_topology.sheafify_is_sheaf

modified src/category_theory/sites/whiskering.lean
- \+ *lemma* multicospan_comp_hom_inv_left
- \+ *lemma* multicospan_comp_hom_inv_right



## [2021-11-30 02:52:47](https://github.com/leanprover-community/mathlib/commit/396351b)
chore(scripts): update nolints.txt ([#10545](https://github.com/leanprover-community/mathlib/pull/10545))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2021-11-29 21:29:13](https://github.com/leanprover-community/mathlib/commit/04fc415)
feat(algebra/char_p/two): lemmas about characteristic two ([#10442](https://github.com/leanprover-community/mathlib/pull/10442))
#### Estimated changes
modified src/algebra/char_p/basic.lean
- \+ *lemma* list_sum_pow_char
- \+ *lemma* multiset_sum_pow_char
- \+ *lemma* sum_pow_char

created src/algebra/char_p/two.lean
- \+ *lemma* two_eq_zero
- \+ *lemma* add_self_eq_zero
- \+ *lemma* bit0_eq_zero
- \+ *lemma* bit1_eq_one
- \+ *lemma* neg_eq
- \+ *lemma* neg_eq'
- \+ *lemma* sub_eq_add
- \+ *lemma* sub_eq_add'
- \+ *lemma* add_sq
- \+ *lemma* add_mul_self
- \+ *lemma* list_sum_sq
- \+ *lemma* list_sum_mul_self
- \+ *lemma* multiset_sum_sq
- \+ *lemma* multiset_sum_mul_self
- \+ *lemma* sum_sq
- \+ *lemma* sum_mul_self



## [2021-11-29 19:42:43](https://github.com/leanprover-community/mathlib/commit/f798f22)
refactor(order/filter/bases): drop `p` in `has_antitone_basis` ([#10499](https://github.com/leanprover-community/mathlib/pull/10499))
We never use `has_antitone_basis` for `p ≠ λ _, true` in `mathlib`.
#### Estimated changes
modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* exists_seq_tendsto
- \+/\- *lemma* subseq_tendsto_of_ne_bot
- \+/\- *lemma* exists_seq_tendsto
- \+/\- *lemma* subseq_tendsto_of_ne_bot

modified src/order/filter/bases.lean
- \- *lemma* exists_antitone_eq_infi_principal

modified src/topology/G_delta.lean

modified src/topology/sequences.lean

modified src/topology/uniform_space/basic.lean

modified src/topology/uniform_space/cauchy.lean



## [2021-11-29 17:49:24](https://github.com/leanprover-community/mathlib/commit/da6aceb)
chore(order): fix-ups after [#9891](https://github.com/leanprover-community/mathlib/pull/9891) ([#10538](https://github.com/leanprover-community/mathlib/pull/10538))
#### Estimated changes
modified src/combinatorics/simple_graph/subgraph.lean

modified src/data/fin/basic.lean

modified src/order/bounded_order.lean
- \+/\- *lemma* inf_eq_bot_iff_le_compl
- \+/\- *lemma* inf_eq_bot_iff_le_compl

modified src/order/filter/germ.lean



## [2021-11-29 17:49:23](https://github.com/leanprover-community/mathlib/commit/7545909)
chore(logic/function): allow `Sort*` in `function.inv_fun` ([#10526](https://github.com/leanprover-community/mathlib/pull/10526))
#### Estimated changes
modified src/logic/function/basic.lean
- \+/\- *lemma* inv_fun_neg
- \+/\- *lemma* inv_fun_neg
- \+/\- *theorem* inv_fun_eq
- \+/\- *theorem* inv_fun_eq



## [2021-11-29 17:49:21](https://github.com/leanprover-community/mathlib/commit/3ac9ae7)
chore(data/stream): dedup `take` and `approx` ([#10525](https://github.com/leanprover-community/mathlib/pull/10525))
`stream.take` and `stream.approx` were propositionally equal. Merge
them into one function `stream.take`; the definition comes from the old `stream.approx`.
#### Estimated changes
modified src/data/stream/basic.lean
- \- *lemma* length_take

modified src/data/stream/defs.lean
- \+/\- *def* take
- \- *def* approx
- \+/\- *def* take

modified src/data/stream/init.lean
- \+ *theorem* take_zero
- \+ *theorem* take_succ
- \+ *theorem* length_take
- \+ *theorem* nth_take_succ
- \+ *theorem* append_take_drop
- \+/\- *theorem* take_theorem
- \+/\- *theorem* nth_inits
- \- *theorem* approx_zero
- \- *theorem* approx_succ
- \- *theorem* nth_approx
- \- *theorem* append_approx_drop
- \+/\- *theorem* take_theorem
- \+/\- *theorem* nth_inits



## [2021-11-29 17:49:20](https://github.com/leanprover-community/mathlib/commit/bc4ed5c)
chore(*): cleanup unneeded uses of by_cases across the library ([#10523](https://github.com/leanprover-community/mathlib/pull/10523))
Many proofs in the library do case splits but then never use the introduced assumption in one of the cases, meaning the case split can be removed and replaced with the general argument.
Its easy to either accidentally introduce these more complicated than needed arguments when writing proofs, or in some cases presumably refactors made assumptions unnecessary, we golf / simplify several of these to simplify these proofs.
Similar things happen for `split_ifs` and explicit `if ... then` proofs.
Rather remarkably the changes to `uniformly_extend_spec` make the separated space assumption unnecessary too, and removing this removes this assumption from around 10 other lemmas in the library too.
Some more random golfs were added in the review process
Found with a work in progress linter.
#### Estimated changes
modified src/analysis/special_functions/pow.lean

modified src/data/complex/is_R_or_C.lean

modified src/data/fintype/basic.lean

modified src/data/list/intervals.lean

modified src/data/polynomial/algebra_map.lean

modified src/data/rbtree/insert.lean

modified src/deprecated/subfield.lean

modified src/field_theory/ratfunc.lean

modified src/group_theory/order_of_element.lean

modified src/group_theory/perm/concrete_cycle.lean

modified src/group_theory/perm/cycles.lean

modified src/group_theory/perm/list.lean

modified src/group_theory/perm/option.lean

modified src/linear_algebra/matrix/transvection.lean

modified src/linear_algebra/matrix/zpow.lean

modified src/linear_algebra/trace.lean

modified src/measure_theory/integral/set_integral.lean

modified src/number_theory/pythagorean_triples.lean

modified src/order/compactly_generated.lean

modified src/ring_theory/discrete_valuation_ring.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/polynomial/content.lean

modified src/ring_theory/polynomial/cyclotomic.lean

modified src/set_theory/ordinal_arithmetic.lean

modified src/topology/uniform_space/abstract_completion.lean

modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* extension_coe
- \+/\- *lemma* extension_coe

modified src/topology/uniform_space/uniform_embedding.lean
- \+/\- *lemma* uniformly_extend_of_ind
- \+/\- *lemma* uniformly_extend_unique
- \+/\- *lemma* uniformly_extend_of_ind
- \+/\- *lemma* uniformly_extend_unique



## [2021-11-29 17:49:19](https://github.com/leanprover-community/mathlib/commit/5601833)
chore(*): a few facts about `pprod` ([#10519](https://github.com/leanprover-community/mathlib/pull/10519))
Add `equiv.pprod_equiv_prod` and `function.embedding.pprod_map`.
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *def* pprod_equiv_prod

modified src/data/pprod.lean
- \+ *lemma* function.injective.pprod_map

modified src/logic/embedding.lean
- \+ *def* pprod_map



## [2021-11-29 17:49:18](https://github.com/leanprover-community/mathlib/commit/be48f95)
refactor(algebra.order.group): Convert abs_eq_sup_neg to multiplicative form ([#10505](https://github.com/leanprover-community/mathlib/pull/10505))
refactor(algebra.order.group): Convert abs_eq_sup_neg to multiplicative form
#### Estimated changes
modified src/algebra/order/group.lean
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
modified src/field_theory/galois.lean

modified src/field_theory/separable.lean



## [2021-11-29 17:49:15](https://github.com/leanprover-community/mathlib/commit/fcbe714)
refactor(data/nat/fib): use `nat.iterate` ([#10489](https://github.com/leanprover-community/mathlib/pull/10489))
The main drawback of the new definition is that `fib (n + 2) = fib n + fib (n + 1)` is no longer `rfl` but I think that we should have one API for iterates.
See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60nat.2Eiterate.60.20vs.20.60stream.2Eiterate.60
#### Estimated changes
modified archive/imo/imo1981_q3.lean

modified src/algebra/continued_fractions/computation/approximations.lean

modified src/data/nat/fib.lean
- \+ *lemma* fib_add_two
- \+/\- *lemma* fib_le_fib_succ
- \+/\- *lemma* fib_pos
- \+ *lemma* fib_lt_fib_succ
- \- *lemma* fib_succ_succ
- \+/\- *lemma* fib_pos
- \+/\- *lemma* fib_le_fib_succ
- \+/\- *def* fib
- \+/\- *def* fib

modified src/data/nat/gcd.lean
- \+/\- *lemma* gcd_add_mul_self
- \+ *lemma* gcd_add_self_right
- \+ *lemma* gcd_add_self_left
- \+ *lemma* gcd_self_add_left
- \+ *lemma* gcd_self_add_right
- \+/\- *lemma* gcd_add_mul_self
- \+/\- *theorem* gcd_eq_zero_iff
- \+ *theorem* coprime_add_self_right
- \+ *theorem* coprime_self_add_right
- \+ *theorem* coprime_add_self_left
- \+ *theorem* coprime_self_add_left
- \+/\- *theorem* gcd_eq_zero_iff

modified src/data/real/golden_ratio.lean



## [2021-11-29 17:11:51](https://github.com/leanprover-community/mathlib/commit/b849b3c)
feat(number_theory/padics/padic_norm): prime powers in divisors ([#10481](https://github.com/leanprover-community/mathlib/pull/10481))
#### Estimated changes
modified src/number_theory/padics/padic_norm.lean
- \+ *lemma* range_pow_padic_val_nat_subset_divisors
- \+ *lemma* range_pow_padic_val_nat_subset_divisors'



## [2021-11-29 09:57:02](https://github.com/leanprover-community/mathlib/commit/957fa4b)
feat(order/locally_finite): `with_top α`/`with_bot α` are locally finite orders ([#10202](https://github.com/leanprover-community/mathlib/pull/10202))
This provides the two instances `locally_finite_order (with_top α)` and `locally_finite_order (with_bot α)`.
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* mem_cons_self

modified src/data/option/defs.lean
- \+ *lemma* mem_iff

modified src/logic/embedding.lean
- \+ *def* coe_option
- \+ *def* coe_with_top

modified src/order/locally_finite.lean
- \+ *lemma* Icc_coe_top
- \+ *lemma* Icc_coe_coe
- \+ *lemma* Ico_coe_top
- \+ *lemma* Ico_coe_coe
- \+ *lemma* Ioc_coe_top
- \+ *lemma* Ioc_coe_coe
- \+ *lemma* Ioo_coe_top
- \+ *lemma* Ioo_coe_coe
- \+ *lemma* Icc_bot_coe
- \+ *lemma* Icc_coe_coe
- \+ *lemma* Ico_bot_coe
- \+ *lemma* Ico_coe_coe
- \+ *lemma* Ioc_bot_coe
- \+ *lemma* Ioc_coe_coe
- \+ *lemma* Ioo_bot_coe
- \+ *lemma* Ioo_coe_coe



## [2021-11-29 06:52:12](https://github.com/leanprover-community/mathlib/commit/202ca0b)
feat(*/is_R_or_C): deduplicate ([#10522](https://github.com/leanprover-community/mathlib/pull/10522))
I noticed that the same argument, that in a normed space over `is_R_or_C` an element can be normalized, appears in a couple of different places in the library.  I have deduplicated and placed it in `analysis/normed_space/is_R_or_C`.
#### Estimated changes
modified src/analysis/inner_product_space/projection.lean

modified src/analysis/normed_space/is_R_or_C.lean
- \+ *lemma* norm_smul_inv_norm
- \+ *lemma* norm_smul_inv_norm'
- \+/\- *lemma* linear_map.bound_of_ball_bound
- \+/\- *lemma* linear_map.bound_of_ball_bound

modified src/data/complex/is_R_or_C.lean
- \- *lemma* norm_smul_inv_norm



## [2021-11-29 06:52:11](https://github.com/leanprover-community/mathlib/commit/a53da16)
feat(data/int/basic): `nat_abs_dvd_iff_dvd` ([#10469](https://github.com/leanprover-community/mathlib/pull/10469))
#### Estimated changes
modified src/data/int/basic.lean
- \+ *lemma* nat_abs_dvd_iff_dvd



## [2021-11-29 06:04:28](https://github.com/leanprover-community/mathlib/commit/50cc57b)
chore(category_theory/limits/shapes/wide_pullbacks): speed up `wide_cospan` ([#10535](https://github.com/leanprover-community/mathlib/pull/10535))
#### Estimated changes
modified src/category_theory/limits/shapes/wide_pullbacks.lean



## [2021-11-29 01:36:13](https://github.com/leanprover-community/mathlib/commit/16daabf)
chore(algebra/group_power): golf a few proofs ([#10498](https://github.com/leanprover-community/mathlib/pull/10498))
* move `pow_lt_pow_of_lt_one` and `pow_lt_pow_iff_of_lt_one` from
  `algebra.group_power.lemmas` to `algebra.group_power.order`;
* add `strict_anti_pow`, use it to golf the proofs of the two lemmas
  above;
* golf a few other proofs;
* add `nnreal.exists_pow_lt_of_lt_one`.
#### Estimated changes
modified src/algebra/group_power/lemmas.lean
- \- *lemma* pow_lt_pow_of_lt_one
- \- *lemma* pow_lt_pow_iff_of_lt_one

modified src/algebra/group_power/order.lean
- \+ *lemma* strict_anti_pow
- \+ *lemma* pow_lt_pow_iff_of_lt_one
- \+ *lemma* pow_lt_pow_of_lt_one
- \+/\- *lemma* one_lt_pow
- \+/\- *lemma* one_lt_pow

modified src/algebra/order/ring.lean

modified src/data/real/nnreal.lean
- \+ *lemma* exists_pow_lt_of_lt_one



## [2021-11-28 23:50:39](https://github.com/leanprover-community/mathlib/commit/77ba0c4)
chore(logic): allow `Sort*` args in 2 lemmas ([#10517](https://github.com/leanprover-community/mathlib/pull/10517))
#### Estimated changes
modified src/logic/basic.lean
- \+/\- *lemma* congr_arg2
- \+/\- *lemma* congr_arg2

modified src/logic/embedding.lean
- \+/\- *lemma* apply_eq_iff_eq
- \+/\- *lemma* apply_eq_iff_eq



## [2021-11-28 23:50:38](https://github.com/leanprover-community/mathlib/commit/c058607)
chore(order): generalize `min_top_left` ([#10486](https://github.com/leanprover-community/mathlib/pull/10486))
As well as its relative `min_top_right`.
Also provide `max_bot_(left|right)`.
#### Estimated changes
modified src/algebra/order/monoid.lean
- \- *lemma* min_top_left
- \- *lemma* min_top_right

modified src/order/bounded_order.lean
- \+ *lemma* min_top_left
- \+ *lemma* min_top_right
- \+ *lemma* max_bot_left
- \+ *lemma* max_bot_right



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
modified src/meta/expr.lean

modified src/tactic/core.lean

modified src/tactic/lint/misc.lean



## [2021-11-28 22:06:26](https://github.com/leanprover-community/mathlib/commit/dfa98e0)
chore(algebra/opposites): split out lemmas about rings and groups ([#10457](https://github.com/leanprover-community/mathlib/pull/10457))
All these lemmas are just moved.
The advantage of this is that `algebra.opposites` becomes a much lighter-weight import, allowing us to use the `has_mul` and `has_scalar` instance on opposite types earlier in the import hierarchy.
It also matches how we structure the instances on `prod` and `pi` types.
This follows on from [#10383](https://github.com/leanprover-community/mathlib/pull/10383)
#### Estimated changes
modified src/algebra/big_operators/basic.lean

modified src/algebra/field/opposite.lean

created src/algebra/group/opposite.lean
- \+ *lemma* semiconj_by.op
- \+ *lemma* semiconj_by.unop
- \+ *lemma* semiconj_by_op
- \+ *lemma* semiconj_by_unop
- \+ *lemma* commute.op
- \+ *lemma* commute.unop
- \+ *lemma* commute_op
- \+ *lemma* commute_unop
- \+ *lemma* op_add_equiv_to_equiv
- \+ *lemma* units.coe_unop_op_equiv
- \+ *lemma* units.coe_op_equiv_symm
- \+ *lemma* add_monoid_hom.op_ext
- \+ *def* op_add_equiv
- \+ *def* mul_equiv.inv'
- \+ *def* monoid_hom.to_opposite
- \+ *def* units.op_equiv
- \+ *def* monoid_hom.op
- \+ *def* monoid_hom.unop
- \+ *def* add_monoid_hom.op
- \+ *def* add_monoid_hom.unop
- \+ *def* add_equiv.op
- \+ *def* add_equiv.unop
- \+ *def* mul_equiv.op
- \+ *def* mul_equiv.unop

modified src/algebra/group/prod.lean

modified src/algebra/opposites.lean
- \- *lemma* semiconj_by.op
- \- *lemma* semiconj_by.unop
- \- *lemma* semiconj_by_op
- \- *lemma* semiconj_by_unop
- \- *lemma* commute.op
- \- *lemma* commute.unop
- \- *lemma* commute_op
- \- *lemma* commute_unop
- \- *lemma* op_add_equiv_to_equiv
- \- *lemma* units.coe_unop_op_equiv
- \- *lemma* units.coe_op_equiv_symm
- \- *lemma* add_monoid_hom.op_ext
- \- *def* op_add_equiv
- \- *def* mul_equiv.inv'
- \- *def* monoid_hom.to_opposite
- \- *def* ring_hom.to_opposite
- \- *def* units.op_equiv
- \- *def* monoid_hom.op
- \- *def* monoid_hom.unop
- \- *def* add_monoid_hom.op
- \- *def* add_monoid_hom.unop
- \- *def* ring_hom.op
- \- *def* ring_hom.unop
- \- *def* add_equiv.op
- \- *def* add_equiv.unop
- \- *def* mul_equiv.op
- \- *def* mul_equiv.unop

modified src/algebra/quaternion.lean

created src/algebra/ring/opposite.lean
- \+ *def* ring_hom.to_opposite
- \+ *def* ring_hom.op
- \+ *def* ring_hom.unop

modified src/algebra/smul_with_zero.lean

modified src/data/equiv/ring.lean

modified src/group_theory/group_action/opposite.lean

modified src/ring_theory/ring_invo.lean



## [2021-11-28 20:23:10](https://github.com/leanprover-community/mathlib/commit/f684721)
chore(data/nat/prime): `fact (2.prime)` ([#10441](https://github.com/leanprover-community/mathlib/pull/10441))
#### Estimated changes
modified src/data/nat/prime.lean
- \+ *lemma* fact_prime_two
- \+ *lemma* fact_prime_three

modified src/logic/basic.lean

modified src/number_theory/quadratic_reciprocity.lean
- \- *lemma* fact_prime_two



## [2021-11-28 19:36:10](https://github.com/leanprover-community/mathlib/commit/a2e6bf8)
chore(algebraic_topology/cech_nerve): An attempt to speed up the proofs... ([#10521](https://github.com/leanprover-community/mathlib/pull/10521))
Let's hope this works!
See [zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2310312.20timeouts.20in.20cech_nerve/near/262587999)
#### Estimated changes
modified src/algebraic_topology/cech_nerve.lean
- \+ *def* map_cech_nerve
- \+ *def* map_augmented_cech_nerve
- \+ *def* map_cech_conerve
- \+ *def* map_augmented_cech_conerve



## [2021-11-28 07:21:28](https://github.com/leanprover-community/mathlib/commit/044f532)
chore(analysis/normed_space/hahn_banach): remove `norm'` ([#10527](https://github.com/leanprover-community/mathlib/pull/10527))
For a normed space over `ℝ`-algebra `𝕜`, `norm'` is currently defined to be `algebra_map ℝ 𝕜 ∥x∥`.  I believe this was introduced before the `is_R_or_C` construct (including the coercion from `ℝ` to `𝕜` for `[is_R_or_C 𝕜]`) joined mathlib.  Now that we have these things, it's easy to just say `(∥x∥ : 𝕜)` instead of `norm' 𝕜 ∥x∥`, so I don't really think `norm'` needs to exist any more.
(In principle, `norm'` is more general, since it works for all `ℝ`-algebras `𝕜` rather than just `[is_R_or_C 𝕜]`.  But I can only really think of applications in the`is_R_or_C` case, and that's the only way it's used in the library.)
#### Estimated changes
modified src/analysis/normed_space/dual.lean

modified src/analysis/normed_space/hahn_banach.lean
- \+/\- *lemma* coord_norm'
- \- *lemma* norm'_def
- \- *lemma* norm_norm'
- \- *lemma* norm'_eq_zero_iff
- \+/\- *lemma* coord_norm'
- \+/\- *theorem* exists_dual_vector
- \+/\- *theorem* exists_dual_vector

modified src/measure_theory/function/ae_eq_of_integral.lean



## [2021-11-28 07:21:27](https://github.com/leanprover-community/mathlib/commit/099fb0f)
feat(data/nat/prime): lemma eq_of_eq_count_factors ([#10493](https://github.com/leanprover-community/mathlib/pull/10493))
#### Estimated changes
modified src/data/nat/prime.lean
- \+ *lemma* eq_of_perm_factors
- \+ *lemma* eq_of_count_factors_eq



## [2021-11-28 06:12:10](https://github.com/leanprover-community/mathlib/commit/45d45ef)
feat(data/nat/prime): lemma count_factors_mul_of_coprime ([#10492](https://github.com/leanprover-community/mathlib/pull/10492))
Adding lemma `count_factors_mul_of_coprime` and using it to simplify the proof of `factors_count_eq_of_coprime_left`.
#### Estimated changes
modified src/data/nat/prime.lean
- \+ *lemma* count_factors_mul_of_coprime



## [2021-11-28 03:39:40](https://github.com/leanprover-community/mathlib/commit/b1f9067)
feat(group_theory/group_action/units): add a `mul_distrib_mul_action` instance ([#10480](https://github.com/leanprover-community/mathlib/pull/10480))
This doesn't add any new "data" instances, it just shows the existing instance satisfies stronger properties with stronger assumptions.
#### Estimated changes
modified src/group_theory/group_action/units.lean



## [2021-11-27 09:46:17](https://github.com/leanprover-community/mathlib/commit/b8af491)
feat(category_theory/sites/whiskering): Functors between sheaf categories induced by compositiion ([#10496](https://github.com/leanprover-community/mathlib/pull/10496))
We construct the functor `Sheaf J A` to `Sheaf J B` induced by a functor `A` to `B` which preserves the appropriate limits.
#### Estimated changes
created src/category_theory/sites/whiskering.lean
- \+ *lemma* multicospan_comp_app_left
- \+ *lemma* multicospan_comp_app_right
- \+ *lemma* multicospan_comp_hom_app_left
- \+ *lemma* multicospan_comp_hom_app_right
- \+ *lemma* presheaf.is_sheaf.comp
- \+ *lemma* Sheaf_compose_obj_to_presheaf
- \+ *lemma* Sheaf_compose_map_to_presheaf
- \+ *lemma* Sheaf_compose_map_app
- \+ *lemma* Sheaf_compose_map_app_app
- \+ *lemma* Sheaf_compose_map_id
- \+ *lemma* Sheaf_compose_map_comp
- \+ *def* multicospan_comp
- \+ *def* map_multifork
- \+ *def* Sheaf_compose
- \+ *def* Sheaf_compose_map



## [2021-11-27 08:42:32](https://github.com/leanprover-community/mathlib/commit/fcb3790)
feat(topology/algebra/matrix): the determinant is a continuous map ([#10503](https://github.com/leanprover-community/mathlib/pull/10503))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* coe_det_is_empty

created src/topology/algebra/matrix.lean
- \+ *lemma* continuous_det

modified src/topology/constructions.lean
- \+ *lemma* continuous_apply_apply



## [2021-11-27 07:02:21](https://github.com/leanprover-community/mathlib/commit/d36a67c)
feat(ring_theory/euclidean_domain): generalize lemmas to PIDs ([#10324](https://github.com/leanprover-community/mathlib/pull/10324))
This moves the existing lemmas to the `euclidean_domain` namespace.
#### Estimated changes
modified src/data/polynomial/field_division.lean

modified src/field_theory/separable.lean

modified src/ring_theory/euclidean_domain.lean
- \+ *def* gcd_monoid

modified src/ring_theory/principal_ideal_domain.lean
- \+ *theorem* span_gcd
- \+ *theorem* gcd_is_unit_iff
- \+ *theorem* is_coprime_of_dvd
- \+ *theorem* dvd_or_coprime



## [2021-11-27 02:49:59](https://github.com/leanprover-community/mathlib/commit/150b217)
chore(scripts): update nolints.txt ([#10513](https://github.com/leanprover-community/mathlib/pull/10513))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2021-11-26 23:08:10](https://github.com/leanprover-community/mathlib/commit/7a19aa1)
feat(group_theory/order_of_element): linear ordered rings ([#10473](https://github.com/leanprover-community/mathlib/pull/10473))
#### Estimated changes
modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_eq_zero_iff'
- \+ *lemma* order_of_abs_ne_one
- \+ *lemma* linear_ordered_ring.order_of_le_two



## [2021-11-26 21:40:36](https://github.com/leanprover-community/mathlib/commit/7348f1b)
Adding a matching TODO back ([#10506](https://github.com/leanprover-community/mathlib/pull/10506))
Because we were careless and removed it too early:
https://github.com/leanprover-community/mathlib/pull/10210#discussion_r757640946
#### Estimated changes
modified src/combinatorics/simple_graph/matching.lean



## [2021-11-26 17:50:35](https://github.com/leanprover-community/mathlib/commit/deb5692)
refactor(combinatorics/simple_graph): use subgraphs to represent matchings ([#10210](https://github.com/leanprover-community/mathlib/pull/10210))
#### Estimated changes
modified docs/overview.yaml

modified src/combinatorics/simple_graph/matching.lean
- \+ *lemma* is_matching.support_eq_verts
- \+ *lemma* is_perfect_matching_iff
- \- *lemma* matching.is_perfect_iff
- \+ *def* is_matching
- \+ *def* is_perfect_matching
- \- *def* matching.support
- \- *def* matching.is_perfect

modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* is_spanning_iff
- \+ *lemma* mem_support
- \+ *lemma* support_subset_verts
- \+ *lemma* support_mono
- \+ *def* support



## [2021-11-26 16:20:00](https://github.com/leanprover-community/mathlib/commit/dabb58b)
chore(algebra/module/pi): split out `group_theory/group_action/pi` to match `group_theory/group_action/prod` ([#10485](https://github.com/leanprover-community/mathlib/pull/10485))
These declarations are copied without modification.
#### Estimated changes
modified src/algebra/module/pi.lean
- \- *lemma* smul_def
- \- *lemma* smul_apply
- \- *lemma* smul_apply'
- \- *lemma* has_faithful_scalar_at
- \- *lemma* single_smul
- \- *lemma* single_smul'
- \- *lemma* single_smul₀
- \- *lemma* update_smul
- \- *lemma* piecewise_smul
- \- *lemma* function.extend_smul

modified src/data/fin/vec_notation.lean

created src/group_theory/group_action/pi.lean
- \+ *lemma* smul_def
- \+ *lemma* smul_apply
- \+ *lemma* smul_apply'
- \+ *lemma* has_faithful_scalar_at
- \+ *lemma* single_smul
- \+ *lemma* single_smul'
- \+ *lemma* single_smul₀
- \+ *lemma* update_smul
- \+ *lemma* piecewise_smul
- \+ *lemma* function.extend_smul



## [2021-11-26 16:19:59](https://github.com/leanprover-community/mathlib/commit/ea52ec1)
feat(ring_theory/ideal/operations): add lemmas about comap ([#10418](https://github.com/leanprover-community/mathlib/pull/10418))
This also adds `ring_hom.to_semilinear_map` and `ring_equiv.to_semilinear_equiv`.
#### Estimated changes
modified src/algebra/module/linear_map.lean
- \+ *def* _root_.ring_hom.to_semilinear_map

modified src/data/equiv/module.lean
- \+ *def* _root_.ring_equiv.to_semilinear_equiv

modified src/ring_theory/ideal/operations.lean
- \+ *lemma* map_le_comap_of_inv_on
- \+ *lemma* comap_le_map_of_inv_on
- \+ *lemma* map_le_comap_of_inverse
- \+ *lemma* comap_le_map_of_inverse
- \+ *lemma* comap_ker



## [2021-11-26 15:44:03](https://github.com/leanprover-community/mathlib/commit/9cfa33a)
feat(algebra/lie): implement `set_like` for `lie_submodule` ([#10488](https://github.com/leanprover-community/mathlib/pull/10488))
This PR provides a `set_like` instance for `lie_submodule` and uses it to define `has_mem` and `has_le` for Lie submodules / ideals.
#### Estimated changes
modified src/algebra/lie/submodule.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext
- \- *lemma* le_def



## [2021-11-26 12:59:28](https://github.com/leanprover-community/mathlib/commit/83bce9f)
feat(category_theory/adjunction/whiskering): Whiskering adjunctions. ([#10495](https://github.com/leanprover-community/mathlib/pull/10495))
Construct adjunctions between functor categories induced by whiskering (both left and right).
This will be used later to construct adjunctions between categories of sheaves.
#### Estimated changes
created src/category_theory/adjunction/whiskering.lean



## [2021-11-26 11:59:16](https://github.com/leanprover-community/mathlib/commit/61e8aa8)
feat(topology/algebra/[X]): sub[X] of a topological [X] is itself a topological [X] ([#10491](https://github.com/leanprover-community/mathlib/pull/10491))
#### Estimated changes
modified src/topology/algebra/group.lean

modified src/topology/algebra/module.lean

modified src/topology/algebra/monoid.lean

modified src/topology/algebra/ring.lean



## [2021-11-26 11:04:50](https://github.com/leanprover-community/mathlib/commit/36f33d0)
chore(category_theory/limits): Generalize universes for limits ([#10243](https://github.com/leanprover-community/mathlib/pull/10243))
#### Estimated changes
modified src/algebra/category/Algebra/limits.lean
- \+/\- *def* limit_cone
- \+/\- *def* limit_cone

modified src/algebra/category/CommRing/limits.lean
- \+/\- *def* limit_cone
- \+/\- *def* limit_cone

modified src/algebra/category/Module/limits.lean
- \+/\- *def* limit_cone
- \+/\- *def* limit_cone

modified src/algebra/category/Mon/limits.lean
- \+/\- *def* limit_cone
- \+/\- *def* limit_cone

modified src/category_theory/category/ulift.lean
- \+ *def* ulift.up_functor
- \+ *def* ulift.down_functor
- \+ *def* {v'
- \- *def* ulift.up
- \- *def* ulift.down

modified src/category_theory/discrete_category.lean
- \+/\- *def* equivalence
- \+/\- *def* equiv_of_equivalence
- \+/\- *def* equivalence
- \+/\- *def* equiv_of_equivalence

modified src/category_theory/fin_category.lean
- \+ *def* obj_as_type_equiv_as_type

modified src/category_theory/graded_object.lean

modified src/category_theory/is_connected.lean

modified src/category_theory/limits/comma.lean

modified src/category_theory/limits/cones.lean
- \+/\- *def* cones
- \+/\- *def* cocones
- \+/\- *def* cones
- \+/\- *def* cocones
- \+/\- *def* extensions
- \+/\- *def* cones
- \+/\- *def* cocones
- \+/\- *def* cones
- \+/\- *def* cocones
- \+/\- *def* extensions

modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean

modified src/category_theory/limits/creates.lean

modified src/category_theory/limits/functor_category.lean

modified src/category_theory/limits/has_limits.lean
- \+ *lemma* has_limits.has_limits_of_shape
- \+/\- *lemma* limit.hom_iso_hom
- \+/\- *lemma* has_limit.of_cones_iso
- \+/\- *lemma* limit.pre_post
- \+/\- *lemma* limit.map_post
- \+/\- *lemma* has_limits_of_shape_of_equivalence
- \+ *lemma* has_limits_of_size_shrink
- \+ *lemma* has_colimits.has_limits_of_shape
- \+/\- *lemma* colimit.hom_iso_hom
- \+/\- *lemma* has_colimit.of_cocones_iso
- \+/\- *lemma* colimit.pre_post
- \+/\- *lemma* colimit.map_post
- \+/\- *lemma* has_colimits_of_shape_of_equivalence
- \+ *lemma* has_colimits_of_size_shrink
- \+/\- *lemma* limit.hom_iso_hom
- \+/\- *lemma* has_limit.of_cones_iso
- \+/\- *lemma* limit.pre_post
- \+/\- *lemma* limit.map_post
- \+/\- *lemma* has_limits_of_shape_of_equivalence
- \+/\- *lemma* colimit.hom_iso_hom
- \+/\- *lemma* has_colimit.of_cocones_iso
- \+/\- *lemma* colimit.pre_post
- \+/\- *lemma* colimit.map_post
- \+/\- *lemma* has_colimits_of_shape_of_equivalence
- \+/\- *def* limit.hom_iso
- \+/\- *def* lim_yoneda
- \+/\- *def* colimit.hom_iso
- \+/\- *def* colim_coyoneda
- \+/\- *def* limit.hom_iso
- \+/\- *def* lim_yoneda
- \+/\- *def* colimit.hom_iso
- \+/\- *def* colim_coyoneda

modified src/category_theory/limits/is_limit.lean
- \+/\- *lemma* of_cone_equiv_apply_desc
- \+/\- *lemma* of_cone_equiv_symm_apply_desc
- \+/\- *lemma* hom_iso_hom
- \+/\- *lemma* of_cocone_equiv_apply_desc
- \+/\- *lemma* of_cocone_equiv_symm_apply_desc
- \+/\- *lemma* hom_iso_hom
- \+/\- *lemma* of_cone_equiv_apply_desc
- \+/\- *lemma* of_cone_equiv_symm_apply_desc
- \+/\- *lemma* hom_iso_hom
- \+/\- *lemma* of_cocone_equiv_apply_desc
- \+/\- *lemma* of_cocone_equiv_symm_apply_desc
- \+/\- *lemma* hom_iso_hom
- \+/\- *def* of_right_adjoint
- \+/\- *def* of_cone_equiv
- \+/\- *def* hom_iso
- \+/\- *def* nat_iso
- \+/\- *def* of_faithful
- \+/\- *def* map_cone_equiv
- \+/\- *def* hom_of_cone
- \+/\- *def* of_nat_iso
- \+/\- *def* of_left_adjoint
- \+/\- *def* of_cocone_equiv
- \+/\- *def* hom_iso
- \+/\- *def* nat_iso
- \+/\- *def* of_faithful
- \+/\- *def* map_cocone_equiv
- \+/\- *def* hom_of_cocone
- \+/\- *def* of_nat_iso
- \+/\- *def* of_right_adjoint
- \+/\- *def* of_cone_equiv
- \+/\- *def* hom_iso
- \+/\- *def* nat_iso
- \+/\- *def* of_faithful
- \+/\- *def* map_cone_equiv
- \+/\- *def* hom_of_cone
- \+/\- *def* of_nat_iso
- \+/\- *def* of_left_adjoint
- \+/\- *def* of_cocone_equiv
- \+/\- *def* hom_iso
- \+/\- *def* nat_iso
- \+/\- *def* of_faithful
- \+/\- *def* map_cocone_equiv
- \+/\- *def* hom_of_cocone
- \+/\- *def* of_nat_iso

modified src/category_theory/limits/opposites.lean
- \+/\- *lemma* has_limits_op_of_has_colimits
- \+/\- *lemma* has_colimits_op_of_has_limits
- \+/\- *lemma* has_limits_op_of_has_colimits
- \+/\- *lemma* has_colimits_op_of_has_limits

modified src/category_theory/limits/over.lean

modified src/category_theory/limits/preserves/shapes/binary_products.lean

modified src/category_theory/limits/preserves/shapes/equalizers.lean

modified src/category_theory/limits/preserves/shapes/pullbacks.lean

modified src/category_theory/limits/preserves/shapes/terminal.lean

modified src/category_theory/limits/presheaf.lean

modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *lemma* prod.diag_map_fst_snd_comp
- \+/\- *lemma* coprod.map_comp_inl_inr_codiag
- \+/\- *lemma* prod.diag_map_fst_snd_comp
- \+/\- *lemma* coprod.map_comp_inl_inr_codiag
- \+/\- *def* pair
- \+/\- *def* pair

modified src/category_theory/limits/shapes/equalizers.lean

modified src/category_theory/limits/shapes/finite_limits.lean
- \+/\- *lemma* has_finite_limits_of_has_limits
- \+/\- *lemma* has_finite_limits_of_has_limits

modified src/category_theory/limits/shapes/finite_products.lean

modified src/category_theory/limits/shapes/normal_mono.lean

modified src/category_theory/limits/shapes/products.lean

modified src/category_theory/limits/shapes/pullbacks.lean

modified src/category_theory/limits/shapes/terminal.lean

modified src/category_theory/limits/shapes/wide_equalizers.lean

modified src/category_theory/limits/shapes/wide_pullbacks.lean

modified src/category_theory/monad/monadicity.lean

modified src/category_theory/sites/limits.lean

modified src/topology/category/Top/limits.lean
- \+/\- *lemma* coequalizer_is_open_iff
- \+/\- *lemma* coequalizer_is_open_iff

modified src/topology/sheaves/forget.lean

modified src/topology/sheaves/sheaf_condition/sites.lean



## [2021-11-26 07:20:19](https://github.com/leanprover-community/mathlib/commit/0b9d332)
feat(data/complex/basic): `of_real_injective` ([#10464](https://github.com/leanprover-community/mathlib/pull/10464))
#### Estimated changes
modified src/data/complex/basic.lean
- \+ *theorem* of_real_injective



## [2021-11-26 07:20:18](https://github.com/leanprover-community/mathlib/commit/e742fce)
feat(data/nat/prime): `nat.{eq/ne}_one_iff` ([#10463](https://github.com/leanprover-community/mathlib/pull/10463))
#### Estimated changes
modified src/data/nat/prime.lean
- \+ *lemma* ne_one_iff_exists_prime_dvd
- \+ *lemma* eq_one_iff_not_exists_prime_dvd



## [2021-11-26 07:20:17](https://github.com/leanprover-community/mathlib/commit/71bc7f4)
feat(set_theory/ordinal_notation): nonote is well founded ([#10462](https://github.com/leanprover-community/mathlib/pull/10462))
#### Estimated changes
modified src/set_theory/ordinal_notation.lean
- \+ *theorem* wf



## [2021-11-26 07:20:16](https://github.com/leanprover-community/mathlib/commit/cdb3819)
feat(algebraic_geometry): `of_restrict` is mono. ([#10460](https://github.com/leanprover-community/mathlib/pull/10460))
#### Estimated changes
modified src/algebraic_geometry/presheafed_space.lean

modified src/category_theory/adjunction/fully_faithful.lean

modified src/topology/category/Top/opens.lean



## [2021-11-26 07:20:15](https://github.com/leanprover-community/mathlib/commit/757aa6f)
chore(data/stream): move most defs to a new file ([#10458](https://github.com/leanprover-community/mathlib/pull/10458))
#### Estimated changes
modified src/data/stream/basic.lean
- \- *def* take

created src/data/stream/defs.lean
- \+ *def* stream
- \+ *def* cons
- \+ *def* head
- \+ *def* tail
- \+ *def* drop
- \+ *def* nth
- \+ *def* all
- \+ *def* any
- \+ *def* map
- \+ *def* zip
- \+ *def* const
- \+ *def* iterate
- \+ *def* corec
- \+ *def* corec_on
- \+ *def* corec'
- \+ *def* unfolds
- \+ *def* interleave
- \+ *def* even
- \+ *def* odd
- \+ *def* append_stream
- \+ *def* approx
- \+ *def* take
- \+ *def* cycle
- \+ *def* tails
- \+ *def* inits_core
- \+ *def* inits
- \+ *def* pure
- \+ *def* apply
- \+ *def* nats

modified src/data/stream/init.lean
- \- *def* stream
- \- *def* cons
- \- *def* head
- \- *def* tail
- \- *def* drop
- \- *def* nth
- \- *def* all
- \- *def* any
- \- *def* map
- \- *def* zip
- \- *def* const
- \- *def* iterate
- \- *def* corec
- \- *def* corec_on
- \- *def* corec'
- \- *def* unfolds
- \- *def* interleave
- \- *def* even
- \- *def* odd
- \- *def* append_stream
- \- *def* approx
- \- *def* cycle
- \- *def* tails
- \- *def* inits_core
- \- *def* inits
- \- *def* pure
- \- *def* apply
- \- *def* nats



## [2021-11-26 07:20:14](https://github.com/leanprover-community/mathlib/commit/3dfa349)
feat(topology/uniform_space/completion) : add injective_coe ([#10454](https://github.com/leanprover-community/mathlib/pull/10454))
#### Estimated changes
modified src/topology/uniform_space/completion.lean
- \+ *lemma* coe_injective



## [2021-11-26 07:20:13](https://github.com/leanprover-community/mathlib/commit/cbe1d37)
feat(ring_theory/valuation/basic): add valuation.map_zpow ([#10453](https://github.com/leanprover-community/mathlib/pull/10453))
#### Estimated changes
modified src/ring_theory/valuation/basic.lean
- \+ *lemma* map_zpow



## [2021-11-26 07:20:12](https://github.com/leanprover-community/mathlib/commit/9249e1e)
chore(linear_algebra/affine_space/barycentric_coords): rename file `barycentric_coords` to `basis` ([#10449](https://github.com/leanprover-community/mathlib/pull/10449))
Follow up from https://github.com/leanprover-community/mathlib/pull/10320#discussion_r748936743
#### Estimated changes
modified src/analysis/convex/combination.lean

modified src/analysis/normed_space/add_torsor_bases.lean

renamed src/linear_algebra/affine_space/barycentric_coords.lean to src/linear_algebra/affine_space/basis.lean



## [2021-11-26 07:20:11](https://github.com/leanprover-community/mathlib/commit/28d9a5b)
feat(data/equiv/basic): add lemmas characterising `equiv.Pi_congr` and `equiv.Pi_congr'` ([#10432](https://github.com/leanprover-community/mathlib/pull/10432))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *lemma* coe_Pi_congr_symm
- \+ *lemma* Pi_congr_symm_apply
- \+ *lemma* Pi_congr_apply_apply
- \+ *lemma* coe_Pi_congr'
- \+ *lemma* Pi_congr'_apply
- \+ *lemma* Pi_congr'_symm_apply_symm_apply



## [2021-11-26 06:45:43](https://github.com/leanprover-community/mathlib/commit/be9b96e)
feat(computablility/halting): halting problem is r.e. ([#10459](https://github.com/leanprover-community/mathlib/pull/10459))
This is a minor oversight from the original formalization, pointed out by Keji Neri.
#### Estimated changes
modified src/computability/halting.lean
- \+ *theorem* re_pred.of_eq
- \+ *theorem* partrec.dom_re
- \+ *theorem* halting_problem_re
- \+ *theorem* computable_iff_re_compl_re'
- \+ *theorem* halting_problem_not_re



## [2021-11-26 02:32:10](https://github.com/leanprover-community/mathlib/commit/f55a284)
feat(topology): normal topological space with second countable topology is metrizable ([#10402](https://github.com/leanprover-community/mathlib/pull/10402))
Also prove that a regular topological space with second countable topology is a normal space.
#### Estimated changes
modified src/logic/is_empty.lean
- \+ *lemma* function.extend_of_empty

modified src/topology/bases.lean

modified src/topology/continuous_function/bounded.lean
- \+ *lemma* coe_injective
- \+/\- *lemma* bounded_range
- \+ *lemma* bounded_image
- \+ *lemma* dist_eq_supr
- \+ *lemma* extend_apply
- \+ *lemma* extend_comp
- \+ *lemma* extend_apply'
- \+ *lemma* extend_of_empty
- \+ *lemma* dist_extend_extend
- \+ *lemma* isometry_extend
- \+/\- *lemma* bounded_range
- \+ *def* extend

modified src/topology/metric_space/basic.lean
- \+ *lemma* bounded.union
- \+/\- *lemma* bounded_union
- \+/\- *lemma* bounded_union

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/metric_space/isometry.lean
- \+ *theorem* isometry.embedding

created src/topology/metric_space/metrizable.lean
- \+ *lemma* exists_embedding_l_infty

modified src/topology/separation.lean
- \+ *lemma* topological_space.is_topological_basis.exists_closure_subset
- \+ *lemma* topological_space.is_topological_basis.nhds_basis_closure
- \+ *lemma* normal_space_of_regular_second_countable

modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniform_space.replace_topology_eq
- \+ *def* uniform_space.replace_topology



## [2021-11-25 18:25:14](https://github.com/leanprover-community/mathlib/commit/ee71ddf)
feat(ring_theory/graded_algebra): definition of type class `graded_algebra` ([#10115](https://github.com/leanprover-community/mathlib/pull/10115))
This is largely written by @eric-wieser. Thank you.
#### Estimated changes
created src/ring_theory/graded_algebra/basic.lean
- \+ *lemma* graded_ring.is_internal
- \+ *lemma* graded_algebra.decompose'_def
- \+ *lemma* graded_algebra.decompose_symm_of
- \+ *def* graded_algebra.decompose



## [2021-11-25 16:03:28](https://github.com/leanprover-community/mathlib/commit/644591f)
chore(algebra/group/basic): + 2 simp lemmas about `a - b` ([#10478](https://github.com/leanprover-community/mathlib/pull/10478))
#### Estimated changes
modified src/algebra/group/basic.lean
- \+ *lemma* sub_add_cancel'



## [2021-11-25 12:14:38](https://github.com/leanprover-community/mathlib/commit/7d8a1e0)
feat(data/polynomial/eval): random `eval` lemmas ([#10470](https://github.com/leanprover-community/mathlib/pull/10470))
note that the `geom_sum` import only adds the `geom_sum` file itself; all other files were imported already
#### Estimated changes
modified src/algebra/geom_sum.lean
- \+ *lemma* one_geom_sum
- \+/\- *lemma* op_geom_sum
- \+/\- *lemma* op_geom_sum₂
- \+/\- *lemma* op_geom_sum
- \+/\- *lemma* op_geom_sum₂

modified src/data/polynomial/eval.lean
- \+ *lemma* eval_dvd
- \+ *lemma* eval_eq_zero_of_dvd_of_eval_eq_zero
- \+ *lemma* eval_geom_sum



## [2021-11-25 07:53:00](https://github.com/leanprover-community/mathlib/commit/5b767aa)
feat(measure_theory/integral/integral_eq_improper): weaken measurability assumptions  ([#10387](https://github.com/leanprover-community/mathlib/pull/10387))
As suggested by @fpvandoorn, this removes a.e. measurability assumptions which could be deduced from integrability assumptions. More of them could be removed assuming the codomain is a `borel_space` and not only an `open_measurable_space`, but I’m not sure wether or not it would be a good idea.
#### Estimated changes
modified src/measure_theory/integral/integrable_on.lean

modified src/measure_theory/integral/integral_eq_improper.lean
- \+ *lemma* ae_cover.ae_measurable

modified src/measure_theory/integral/interval_integral.lean

modified src/measure_theory/integral/lebesgue.lean

modified src/measure_theory/integral/set_integral.lean

modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* restrict_mono_ae
- \+/\- *lemma* restrict_congr_set
- \+ *lemma* restrict_eq_self_of_ae_mem
- \+/\- *lemma* restrict_mono_ae
- \+/\- *lemma* restrict_congr_set



## [2021-11-25 03:11:34](https://github.com/leanprover-community/mathlib/commit/7dfd7e8)
chore(scripts): update nolints.txt ([#10484](https://github.com/leanprover-community/mathlib/pull/10484))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2021-11-25 01:40:31](https://github.com/leanprover-community/mathlib/commit/d04f5a5)
feat(algebra/pointwise): lemmas about multiplication of finsets ([#10455](https://github.com/leanprover-community/mathlib/pull/10455))
#### Estimated changes
modified src/algebra/pointwise.lean
- \+/\- *lemma* mul_def
- \+/\- *lemma* mem_mul
- \+/\- *lemma* coe_mul
- \+/\- *lemma* mul_mem_mul
- \+/\- *lemma* mul_card_le
- \+ *lemma* empty_mul
- \+ *lemma* mul_empty
- \+ *lemma* mul_nonempty_iff
- \+ *lemma* mul_subset_mul
- \+ *lemma* mul_singleton_zero
- \+ *lemma* singleton_zero_mul
- \+/\- *lemma* mul_def
- \+/\- *lemma* mem_mul
- \+/\- *lemma* coe_mul
- \+/\- *lemma* mul_mem_mul
- \+/\- *lemma* mul_card_le



## [2021-11-24 18:18:56](https://github.com/leanprover-community/mathlib/commit/daf30fd)
feat(analysis/asymptotics): Generalize superpolynomial decay using limits instead of big O ([#10296](https://github.com/leanprover-community/mathlib/pull/10296))
This PR generalizes the definition of `superpolynomial_decay` in terms of `filter.tendsto` instead of `asymptotics.is_O`.
#### Estimated changes
modified src/analysis/asymptotics/superpolynomial_decay.lean
- \+ *lemma* superpolynomial_decay.congr'
- \+ *lemma* superpolynomial_decay.congr
- \+/\- *lemma* superpolynomial_decay_zero
- \+/\- *lemma* superpolynomial_decay.add
- \+/\- *lemma* superpolynomial_decay.mul
- \+/\- *lemma* superpolynomial_decay.mul_const
- \+/\- *lemma* superpolynomial_decay.const_mul
- \+ *lemma* superpolynomial_decay.param_mul
- \+ *lemma* superpolynomial_decay.mul_param
- \+ *lemma* superpolynomial_decay.param_pow_mul
- \+ *lemma* superpolynomial_decay.mul_param_pow
- \+ *lemma* superpolynomial_decay.polynomial_mul
- \+ *lemma* superpolynomial_decay.mul_polynomial
- \+ *lemma* superpolynomial_decay.trans_eventually_le
- \+ *lemma* superpolynomial_decay_iff_abs_tendsto_zero
- \+ *lemma* superpolynomial_decay_iff_superpolynomial_decay_abs
- \+ *lemma* superpolynomial_decay.trans_eventually_abs_le
- \+ *lemma* superpolynomial_decay.trans_abs_le
- \+/\- *lemma* superpolynomial_decay_mul_const_iff
- \+/\- *lemma* superpolynomial_decay_const_mul_iff
- \+ *lemma* superpolynomial_decay_iff_abs_is_bounded_under
- \+ *lemma* superpolynomial_decay_iff_zpow_tendsto_zero
- \+ *lemma* superpolynomial_decay.param_zpow_mul
- \+ *lemma* superpolynomial_decay.mul_param_zpow
- \+ *lemma* superpolynomial_decay.inv_param_mul
- \+ *lemma* superpolynomial_decay.param_inv_mul
- \+ *lemma* superpolynomial_decay_param_mul_iff
- \+ *lemma* superpolynomial_decay_mul_param_iff
- \+ *lemma* superpolynomial_decay_param_pow_mul_iff
- \+ *lemma* superpolynomial_decay_mul_param_pow_iff
- \+ *lemma* superpolynomial_decay_iff_norm_tendsto_zero
- \+ *lemma* superpolynomial_decay_iff_superpolynomial_decay_norm
- \+ *lemma* superpolynomial_decay_iff_is_O
- \+ *lemma* superpolynomial_decay_iff_is_o
- \- *lemma* superpolynomial_decay_iff_tendsto_zero
- \- *lemma* is_O.trans_superpolynomial_decay
- \- *lemma* superpolynomial_decay.mono
- \- *lemma* superpolynomial_decay.eventually_mono
- \+/\- *lemma* superpolynomial_decay_zero
- \- *lemma* superpolynomial_decay_zero'
- \+/\- *lemma* superpolynomial_decay.add
- \+/\- *lemma* superpolynomial_decay.const_mul
- \+/\- *lemma* superpolynomial_decay.mul_const
- \- *lemma* superpolynomial_decay_const_mul_iff_of_ne_zero
- \- *lemma* superpolynomial_decay_mul_const_iff_of_ne_zero
- \+/\- *lemma* superpolynomial_decay_const_mul_iff
- \+/\- *lemma* superpolynomial_decay_mul_const_iff
- \- *lemma* superpolynomial_decay.algebra_map_mul
- \- *lemma* superpolynomial_decay.algebra_map_pow_mul
- \- *lemma* superpolynomial_decay.mul_is_O_polynomial
- \- *lemma* superpolynomial_decay.mul_is_O
- \+/\- *lemma* superpolynomial_decay.mul
- \- *lemma* superpolynomial_decay_of_eventually_is_O
- \- *lemma* superpolynomial_decay_of_is_O_zpow_le
- \- *lemma* superpolynomial_decay_of_is_O_zpow_lt
- \- *lemma* superpolynomial_decay.tendsto_zero
- \- *lemma* superpolynomial_decay.eventually_le
- \- *lemma* superpolynomial_decay_const_iff
- \- *theorem* superpolynomial_decay_iff_is_bounded_under
- \- *theorem* superpolynomial_decay_iff_is_o
- \- *theorem* superpolynomial_decay_iff_norm_tendsto_zero
- \- *theorem* superpolynomial_decay.polynomial_mul
- \+/\- *def* superpolynomial_decay
- \+/\- *def* superpolynomial_decay

modified src/order/filter/at_top_bot.lean
- \+ *lemma* eventually_ne_of_tendsto_at_top
- \+ *lemma* eventually_ne_of_tendsto_at_bot

modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* tendsto_zero_iff_abs_tendsto_zero



## [2021-11-24 14:56:57](https://github.com/leanprover-community/mathlib/commit/18e5510)
fix(tactic/cancel_denoms): remove debug code ([#10434](https://github.com/leanprover-community/mathlib/pull/10434))
This code must not be used -- worth keeping, as it's a potentially useful function, but it shouldn't trace anything.
#### Estimated changes
modified src/tactic/cancel_denoms.lean



## [2021-11-24 12:24:42](https://github.com/leanprover-community/mathlib/commit/b29b952)
feat(measure_theory/group/fundamental_domain): prove equality of integrals ([#10448](https://github.com/leanprover-community/mathlib/pull/10448))
#### Estimated changes
modified src/dynamics/ergodic/measure_preserving.lean
- \+ *lemma* ae_measurable_comp_iff

modified src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* mono
- \+ *lemma* sum_restrict_of_ac
- \+ *lemma* lintegral_eq_tsum_of_ac
- \+ *lemma* set_lintegral_eq_tsum'
- \+ *lemma* set_lintegral_eq_tsum
- \+ *lemma* measure_eq_tsum_of_ac



## [2021-11-24 12:24:41](https://github.com/leanprover-community/mathlib/commit/563f8c4)
feat(measure_theory/integral): dominated convergence for a series ([#10398](https://github.com/leanprover-community/mathlib/pull/10398))
#### Estimated changes
modified src/measure_theory/integral/bochner.lean
- \+ *lemma* has_sum_integral_of_dominated_convergence

modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* tendsto_integral_filter_of_dominated_convergence
- \+ *lemma* has_sum_integral_of_dominated_convergence



## [2021-11-24 10:42:43](https://github.com/leanprover-community/mathlib/commit/132833b)
refactor(algebra.abs): Introduce `has_pos_part` and `has_neg_part` classes ([#10420](https://github.com/leanprover-community/mathlib/pull/10420))
refactor(algebra.abs): Introduce `has_pos_part` and `has_neg_part` classes
#### Estimated changes
modified src/algebra/abs.lean

modified src/algebra/lattice_ordered_group.lean
- \+ *lemma* m_pos_part_def
- \+ *lemma* m_neg_part_def
- \+/\- *lemma* neg_eq_pos_inv
- \+/\- *lemma* neg_eq_pos_inv
- \- *def* mpos
- \- *def* mneg



## [2021-11-24 09:23:46](https://github.com/leanprover-community/mathlib/commit/09b4bfc)
feat(linear_algebra/multilinear/basic): multilinear maps with respect to an empty family are all constant ([#10433](https://github.com/leanprover-community/mathlib/pull/10433))
This seemingly-innocuous statement is valuable as a base case for induction.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/linear_algebra/multilinear/basic.lean
- \+ *lemma* mk_coe
- \+ *def* const_linear_equiv_of_is_empty



## [2021-11-24 07:49:21](https://github.com/leanprover-community/mathlib/commit/d487d65)
refactor(topology,algebraic_geometry): use bundled maps here and there ([#10447](https://github.com/leanprover-community/mathlib/pull/10447))
* `opens.comap` now takes a `continuous_map` and returns a `preorder_hom`;
* `prime_spectrum.comap` is now a bundled `continuous_map`.
#### Estimated changes
modified src/algebraic_geometry/Spec.lean
- \+/\- *def* Spec.Top_map
- \+/\- *def* Spec.Top_map

modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *lemma* preimage_comap_zero_locus_aux
- \+/\- *lemma* comap_id
- \+/\- *lemma* comap_id
- \- *lemma* comap_continuous
- \+/\- *def* comap
- \+/\- *def* comap

modified src/algebraic_geometry/prime_spectrum/is_open_comap_C.lean

modified src/algebraic_geometry/structure_sheaf.lean

modified src/measure_theory/measure/content.lean

modified src/topology/opens.lean
- \+/\- *lemma* comap_id
- \+/\- *lemma* comap_mono
- \+/\- *lemma* coe_comap
- \+/\- *lemma* comap_val
- \+/\- *lemma* comap_id
- \+/\- *lemma* comap_mono
- \+/\- *lemma* coe_comap
- \+/\- *lemma* comap_val
- \+/\- *def* comap
- \+/\- *def* comap



## [2021-11-24 07:49:20](https://github.com/leanprover-community/mathlib/commit/3590dc2)
feat(topology/uniform_space/uniform_convergence): slightly generalize theorems ([#10444](https://github.com/leanprover-community/mathlib/pull/10444))
* add `protected` to some theorems;
* assume `∀ᶠ n, continuous (F n)` instead of `∀ n, continuous (F n)`;
* get rid of `F n` in lemmas like `continuous_within_at_of_locally_uniform_approx_of_continuous_within_at`; instead, assume that there exists a continuous `F` that approximates `f`.
#### Estimated changes
modified src/analysis/analytic/basic.lean
- \- *lemma* has_fpower_series_on_ball.continuous_on
- \- *lemma* has_fpower_series_at.continuous_at
- \- *lemma* analytic_at.continuous_at

modified src/topology/continuous_function/bounded.lean

modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* continuous_on_of_locally_uniform_approx_of_continuous_within_at
- \+ *lemma* continuous_of_locally_uniform_approx_of_continuous_at
- \+/\- *lemma* continuous_of_uniform_approx_of_continuous
- \- *lemma* tendsto_uniformly.tendsto_uniformly_on
- \- *lemma* tendsto_uniformly_on.tendsto_locally_uniformly_on
- \- *lemma* tendsto_uniformly.tendsto_locally_uniformly
- \- *lemma* continuous_on_of_locally_uniform_approx_of_continuous_on
- \- *lemma* continuous_of_locally_uniform_approx_of_continuous
- \+/\- *lemma* continuous_of_uniform_approx_of_continuous
- \- *lemma* tendsto_locally_uniformly_on.continuous_on
- \- *lemma* tendsto_uniformly_on.continuous_on
- \- *lemma* tendsto_locally_uniformly.continuous
- \- *lemma* tendsto_uniformly.continuous



## [2021-11-24 07:49:19](https://github.com/leanprover-community/mathlib/commit/8d07dbf)
feat(topology/sheaves): Generalized some lemmas. ([#10440](https://github.com/leanprover-community/mathlib/pull/10440))
Generalizes some lemmas and explicitly stated that for `f` to be an iso on `U`, it suffices that the stalk map is an iso for all `x : U`.
#### Estimated changes
modified src/topology/sheaves/stalks.lean
- \+ *lemma* app_is_iso_of_stalk_functor_map_iso



## [2021-11-24 07:49:18](https://github.com/leanprover-community/mathlib/commit/a086daa)
chore(ring_theory/polynomial/cyclotomic): use `ratfunc` ([#10421](https://github.com/leanprover-community/mathlib/pull/10421))
#### Estimated changes
modified src/ring_theory/polynomial/cyclotomic.lean
- \+/\- *lemma* cyclotomic_eq_prod_X_pow_sub_one_pow_moebius
- \+/\- *lemma* cyclotomic_eq_prod_X_pow_sub_one_pow_moebius



## [2021-11-24 07:49:17](https://github.com/leanprover-community/mathlib/commit/6cb52e6)
feat(category_theory/limits): Results about (co)limits in Top ([#9985](https://github.com/leanprover-community/mathlib/pull/9985))
- Provided the explicit topologies for limits and colimits, and specialized this result onto some shapes.
- Provided the isomorphism between the (co)limits and the constructions in `topology/constructions.lean`.
- Provided conditions about whether `prod.map` and `pullback_map` are inducing, embedding, etc.
#### Estimated changes
modified src/topology/category/Top/limits.lean
- \+ *lemma* pi_iso_pi_inv_π
- \+ *lemma* pi_iso_pi_inv_π_apply
- \+ *lemma* pi_iso_pi_hom_apply
- \+ *lemma* sigma_iso_sigma_hom_ι
- \+ *lemma* sigma_iso_sigma_hom_ι_apply
- \+ *lemma* sigma_iso_sigma_inv_apply
- \+ *lemma* induced_of_is_limit
- \+ *lemma* limit_topology
- \+ *lemma* prod_iso_prod_hom_fst
- \+ *lemma* prod_iso_prod_hom_snd
- \+ *lemma* prod_iso_prod_hom_apply
- \+ *lemma* prod_iso_prod_inv_fst
- \+ *lemma* prod_iso_prod_inv_snd
- \+ *lemma* prod_topology
- \+ *lemma* range_prod_map
- \+ *lemma* inducing_prod_map
- \+ *lemma* embedding_prod_map
- \+ *lemma* pullback_iso_prod_subtype_inv_fst
- \+ *lemma* pullback_iso_prod_subtype_inv_fst_apply
- \+ *lemma* pullback_iso_prod_subtype_inv_snd
- \+ *lemma* pullback_iso_prod_subtype_inv_snd_apply
- \+ *lemma* pullback_iso_prod_subtype_hom_fst
- \+ *lemma* pullback_iso_prod_subtype_hom_snd
- \+ *lemma* pullback_iso_prod_subtype_hom_apply
- \+ *lemma* pullback_topology
- \+ *lemma* range_pullback_to_prod
- \+ *lemma* inducing_pullback_to_prod
- \+ *lemma* embedding_pullback_to_prod
- \+ *lemma* range_pullback_map
- \+ *lemma* pullback_fst_range
- \+ *lemma* pullback_snd_range
- \+ *lemma* pullback_map_embedding_of_embeddings
- \+ *lemma* pullback_map_open_embedding_of_open_embeddings
- \+ *lemma* snd_embedding_of_left_embedding
- \+ *lemma* fst_embedding_of_right_embedding
- \+ *lemma* embedding_of_pullback_embeddings
- \+ *lemma* snd_open_embedding_of_left_open_embedding
- \+ *lemma* fst_open_embedding_of_right_open_embedding
- \+ *lemma* open_embedding_of_pullback_open_embeddings
- \+ *lemma* fst_iso_of_right_embedding_range_subset
- \+ *lemma* snd_iso_of_left_embedding_range_subset
- \+ *lemma* coinduced_of_is_colimit
- \+ *lemma* colimit_topology
- \+ *lemma* colimit_is_open_iff
- \+ *lemma* coequalizer_is_open_iff
- \+ *def* pi_fan
- \+ *def* pi_fan_is_limit
- \+ *def* pi_iso_pi
- \+ *def* sigma_cofan
- \+ *def* sigma_cofan_is_colimit
- \+ *def* sigma_iso_sigma
- \+ *def* prod_binary_fan
- \+ *def* prod_binary_fan_is_limit
- \+ *def* prod_iso_prod
- \+ *def* pullback_cone
- \+ *def* pullback_cone_is_limit
- \+ *def* pullback_iso_prod_subtype

modified src/topology/homeomorph.lean



## [2021-11-24 06:51:50](https://github.com/leanprover-community/mathlib/commit/d267b6c)
chore(topology): add 2 missing `inhabited` instances ([#10446](https://github.com/leanprover-community/mathlib/pull/10446))
Also add an instance from `discrete_topology` to `topological_ring`.
#### Estimated changes
modified src/topology/algebra/ring.lean

modified src/topology/category/Top/open_nhds.lean

modified src/topology/category/TopCommRing.lean



## [2021-11-24 03:16:10](https://github.com/leanprover-community/mathlib/commit/1c00179)
chore(scripts): update nolints.txt ([#10445](https://github.com/leanprover-community/mathlib/pull/10445))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2021-11-24 02:33:03](https://github.com/leanprover-community/mathlib/commit/f578d1d)
feat(measure_theory): TC for smul-invariant measures ([#10325](https://github.com/leanprover-community/mathlib/pull/10325))
#### Estimated changes
modified src/dynamics/ergodic/measure_preserving.lean
- \+ *lemma* measure_preimage_emb

created src/measure_theory/group/action.lean
- \+ *lemma* smul_invariant_measure_tfae
- \+ *lemma* measure_preserving_smul
- \+ *lemma* map_smul
- \+ *lemma* measure_preimage_smul
- \+ *lemma* measure_smul_set
- \+ *lemma* measure_is_open_pos_of_smul_invariant_of_compact_ne_zero
- \+ *lemma* is_locally_finite_measure_of_smul_invariant
- \+ *lemma* measure_is_open_pos_of_smul_invariant_of_ne_zero
- \+ *lemma* measure_pos_iff_nonempty_of_smul_invariant
- \+ *lemma* measure_eq_zero_iff_eq_empty_of_smul_invariant

created src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* Union_smul_ae_eq
- \+ *lemma* measurable_set_smul
- \+ *lemma* pairwise_ae_disjoint
- \+ *lemma* measure_eq_tsum'
- \+ *lemma* measure_eq_tsum

modified src/measure_theory/integral/lebesgue.lean

modified src/measure_theory/measure/measure_space_def.lean
- \+/\- *lemma* measure_Union_null_iff
- \+ *lemma* measure_sUnion_null_iff
- \+/\- *lemma* measure_Union_null_iff



## [2021-11-23 22:42:46](https://github.com/leanprover-community/mathlib/commit/0cbba1a)
feat(ring_theory/adjoin/basic): add adjoin_induction' and adjoin_adjoin_coe_preimage ([#10427](https://github.com/leanprover-community/mathlib/pull/10427))
From FLT-regular.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* closure_closure_coe_preimage

modified src/group_theory/submonoid/operations.lean
- \+ *lemma* closure_closure_coe_preimage

modified src/linear_algebra/basic.lean
- \+ *lemma* span_induction'
- \+ *lemma* span_span_coe_preimage

modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* adjoin_induction'
- \+ *lemma* adjoin_adjoin_coe_preimage



## [2021-11-23 22:42:45](https://github.com/leanprover-community/mathlib/commit/c192937)
feat(analysis): derivative of a parametric interval integral ([#10404](https://github.com/leanprover-community/mathlib/pull/10404))
#### Estimated changes
created src/analysis/calculus/parametric_interval_integral.lean
- \+ *lemma* has_fderiv_at_integral_of_dominated_loc_of_lip
- \+ *lemma* has_fderiv_at_integral_of_dominated_of_fderiv_le
- \+ *lemma* has_deriv_at_integral_of_dominated_loc_of_lip
- \+ *lemma* has_deriv_at_integral_of_dominated_loc_of_deriv_le

modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* measurable_set_interval_oc



## [2021-11-23 21:34:42](https://github.com/leanprover-community/mathlib/commit/ac283c2)
feat(data/nat/prime): some lemmas about prime factors ([#10385](https://github.com/leanprover-community/mathlib/pull/10385))
A few small lemmas about prime factors, for use in future PRs on prime factorisations and the Euler product formula for totient
#### Estimated changes
modified src/data/nat/prime.lean
- \+ *lemma* perm_factors_mul_of_pos
- \+ *lemma* perm_factors_mul_of_coprime
- \+ *lemma* le_factors_count_mul_left
- \+ *lemma* le_factors_count_mul_right
- \+ *lemma* mem_factors_mul_left
- \+ *lemma* mem_factors_mul_right
- \+ *lemma* factors_count_eq_of_coprime_left
- \+ *lemma* factors_count_eq_of_coprime_right



## [2021-11-23 20:50:39](https://github.com/leanprover-community/mathlib/commit/eb8b1b8)
feat(linear_algebra/affine_space/barycentric_coords): characterise affine bases in terms of coordinate matrices ([#10370](https://github.com/leanprover-community/mathlib/pull/10370))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* ext_elem
- \+ *lemma* to_matrix_row_sum_one
- \+ *lemma* affine_independent_of_to_matrix_right_inv
- \+ *lemma* affine_span_eq_top_of_to_matrix_left_inv
- \+ *lemma* is_unit_to_matrix_iff

modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent_iff_eq_of_fintype_affine_combination_eq



## [2021-11-23 19:47:54](https://github.com/leanprover-community/mathlib/commit/fb82d0a)
feat(data/mv_polynomial/basic): add a symmetric version of coeff_X_mul and generalize to monomials ([#10429](https://github.com/leanprover-community/mathlib/pull/10429))
#### Estimated changes
modified src/algebra/monoid_algebra/basic.lean
- \+ *lemma* support_single_mul
- \+ *lemma* support_single_mul

modified src/data/mv_polynomial/basic.lean
- \+ *lemma* coeff_mul_monomial
- \+ *lemma* coeff_monomial_mul
- \+ *lemma* coeff_X_mul
- \+ *lemma* support_X_mul
- \+ *lemma* coeff_mul_monomial'
- \+ *lemma* coeff_monomial_mul'
- \+/\- *lemma* coeff_mul_X'
- \+ *lemma* coeff_X_mul'
- \+/\- *lemma* map_alg_hom_coe_ring_hom
- \+/\- *lemma* coeff_mul_X'
- \+/\- *lemma* map_alg_hom_coe_ring_hom



## [2021-11-23 19:47:53](https://github.com/leanprover-community/mathlib/commit/ba43124)
feat(category_theory/sites/*): Comparison lemma ([#9785](https://github.com/leanprover-community/mathlib/pull/9785))
#### Estimated changes
modified src/category_theory/sites/cover_lifting.lean
- \+ *lemma* id_cover_lifting
- \+ *lemma* comp_cover_lifting
- \+/\- *theorem* Ran_is_sheaf_of_cover_lifting
- \+/\- *theorem* Ran_is_sheaf_of_cover_lifting
- \+ *def* sites.copullback
- \+ *def* sites.pullback_copullback_adjunction
- \- *def* id_cover_lifting
- \- *def* comp_cover_lifting

modified src/category_theory/sites/dense_subsite.lean
- \+ *lemma* compatible_preserving
- \+ *def* Sheaf_equiv_of_cover_preserving_cover_lifting

created src/category_theory/sites/induced_topology.lean
- \+ *lemma* +
- \+ *lemma* pushforward_cover_iff_cover_pullback
- \+ *lemma* induced_topology_cover_lifting
- \+ *lemma* induced_topology_cover_preserving
- \+ *lemma* cover_dense.locally_cover_dense
- \+ *lemma* over_forget_locally_cover_dense
- \+ *def* locally_cover_dense
- \+ *def* induced_topology
- \+ *def* cover_dense.Sheaf_equiv

modified src/category_theory/sites/sieves.lean
- \+/\- *lemma* functor_pushforward_bot
- \+ *lemma* functor_pushforward_top
- \+/\- *lemma* functor_pushforward_bot



## [2021-11-23 18:21:04](https://github.com/leanprover-community/mathlib/commit/a779f6c)
feat(topology/algebra/ordered): convergent sequence is bounded above/below ([#10424](https://github.com/leanprover-community/mathlib/pull/10424))
Also move lemmas `Ixx_mem_nhds` up to generalize them from
`[linear_order α] [order_topology α]` to
`[linear_order α] [order_closed_topology α]`.
#### Estimated changes
modified src/order/liminf_limsup.lean
- \+/\- *lemma* not_is_bounded_under_of_tendsto_at_top
- \+/\- *lemma* not_is_bounded_under_of_tendsto_at_bot
- \+ *lemma* is_bounded_under.bdd_above_range_of_cofinite
- \+ *lemma* is_bounded_under.bdd_below_range_of_cofinite
- \+ *lemma* is_bounded_under.bdd_above_range
- \+ *lemma* is_bounded_under.bdd_below_range
- \+/\- *lemma* not_is_bounded_under_of_tendsto_at_top
- \+/\- *lemma* not_is_bounded_under_of_tendsto_at_bot

modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* Iio_mem_nhds
- \+/\- *lemma* Ioi_mem_nhds
- \+/\- *lemma* Iic_mem_nhds
- \+/\- *lemma* Ici_mem_nhds
- \+/\- *lemma* Ioo_mem_nhds
- \+/\- *lemma* Ioc_mem_nhds
- \+/\- *lemma* Ico_mem_nhds
- \+/\- *lemma* Icc_mem_nhds
- \+/\- *lemma* Iio_mem_nhds
- \+/\- *lemma* Ioi_mem_nhds
- \+/\- *lemma* Iic_mem_nhds
- \+/\- *lemma* Ici_mem_nhds
- \+/\- *lemma* Ioo_mem_nhds
- \+/\- *lemma* Ioc_mem_nhds
- \+/\- *lemma* Ico_mem_nhds
- \+/\- *lemma* Icc_mem_nhds

modified src/topology/algebra/ordered/liminf_limsup.lean
- \+ *lemma* filter.tendsto.bdd_above_range_of_cofinite
- \+ *lemma* filter.tendsto.bdd_above_range
- \+ *lemma* filter.tendsto.bdd_below_range_of_cofinite
- \+ *lemma* filter.tendsto.bdd_below_range



## [2021-11-23 18:21:02](https://github.com/leanprover-community/mathlib/commit/1dd3ae1)
feat(algebra/big_operators/order): Bounding on a sum of cards by double counting ([#10389](https://github.com/leanprover-community/mathlib/pull/10389))
If every element of `s` is in at least/most `n` finsets of `B : finset (finset α)`, then the sum of `(s ∩ t).card` over `t ∈ B` is at most/least `s.card * n`.
#### Estimated changes
modified src/algebra/big_operators/order.lean
- \+ *lemma* sum_card_inter_le
- \+ *lemma* sum_card_le
- \+ *lemma* le_sum_card_inter
- \+ *lemma* le_sum_card
- \+ *lemma* sum_card_inter
- \+ *lemma* sum_card



## [2021-11-23 16:49:25](https://github.com/leanprover-community/mathlib/commit/b14f22e)
chore(algebra/algebra and group_theory/group_action): move a lemma ([#10425](https://github.com/leanprover-community/mathlib/pull/10425))
Move a lemma about the action of a group on the units of a monoid
to a more appropriate place. It accidentally ended up in
`algebra/algebra/spectrum` but a better place is
`group_theory/group_action/units`.
#### Estimated changes
modified src/algebra/algebra/spectrum.lean
- \- *lemma* is_unit.smul_iff

modified src/group_theory/group_action/group.lean
- \+ *lemma* is_unit_smul_iff

modified src/group_theory/group_action/units.lean
- \+ *lemma* is_unit.smul



## [2021-11-23 16:49:24](https://github.com/leanprover-community/mathlib/commit/7c4f395)
feat(measure_theory): add `is_R_or_C.measurable_space` ([#10417](https://github.com/leanprover-community/mathlib/pull/10417))
Don't remove specific instances because otherwise Lean fails to generate `borel_space (ι → ℝ)`.
#### Estimated changes
modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/function/conditional_expectation.lean
- \+/\- *lemma* const_inner
- \+/\- *lemma* norm_condexp_L2_le_one
- \+/\- *lemma* const_inner
- \+/\- *lemma* norm_condexp_L2_le_one

modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* integrable.of_real
- \+/\- *lemma* integrable.re_im_iff
- \+/\- *lemma* integrable.of_real
- \+/\- *lemma* integrable.re_im_iff

modified src/measure_theory/function/l2_space.lean

modified src/measure_theory/function/lp_space.lean

modified src/measure_theory/function/special_functions.lean

modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* Lp_to_Lp_restrict_smul
- \+/\- *lemma* Lp_to_Lp_restrict_clm_coe_fn
- \+/\- *lemma* continuous_integral_comp_L1
- \+/\- *lemma* Lp_to_Lp_restrict_smul
- \+/\- *lemma* Lp_to_Lp_restrict_clm_coe_fn
- \+/\- *lemma* continuous_integral_comp_L1
- \+/\- *def* Lp_to_Lp_restrict_clm
- \+/\- *def* Lp_to_Lp_restrict_clm



## [2021-11-23 16:49:23](https://github.com/leanprover-community/mathlib/commit/a1338d6)
feat(linear_algebra/affine_space/barycentric_coords): affine bases exist over fields ([#10333](https://github.com/leanprover-community/mathlib/pull/10333))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* exists_affine_basis
- \+ *lemma* exists_affine_basis_of_finite_dimensional



## [2021-11-23 16:49:22](https://github.com/leanprover-community/mathlib/commit/7a6e6d8)
feat(group_theory/schur_zassenhaus): Prove the full Schur-Zassenhaus theorem ([#10283](https://github.com/leanprover-community/mathlib/pull/10283))
Previously, the Schur-Zassenhaus theorem was only proved for abelian normal subgroups. This PR removes the abelian assumption.
#### Estimated changes
modified src/group_theory/schur_zassenhaus.lean
- \+ *lemma* step7
- \+ *theorem* exists_right_complement'_of_coprime_of_fintype
- \+/\- *theorem* exists_right_complement'_of_coprime
- \+ *theorem* exists_left_complement'_of_coprime_of_fintype
- \+/\- *theorem* exists_left_complement'_of_coprime
- \+/\- *theorem* exists_right_complement'_of_coprime
- \+/\- *theorem* exists_left_complement'_of_coprime



## [2021-11-23 16:49:21](https://github.com/leanprover-community/mathlib/commit/97186fe)
feat(combinatorics): Hindman's theorem on finite sums ([#10029](https://github.com/leanprover-community/mathlib/pull/10029))
A short proof of Hindman's theorem using idempotent ultrafilters.
#### Estimated changes
created src/combinatorics/hindman.lean
- \+ *lemma* ultrafilter.eventually_mul
- \+ *lemma* ultrafilter.continuous_mul_left
- \+ *lemma* FP.mul
- \+ *lemma* exists_idempotent_ultrafilter_le_FP
- \+ *lemma* exists_FP_of_large
- \+ *lemma* FP_partition_regular
- \+ *lemma* exists_FP_of_finite_cover
- \+ *lemma* FP_drop_subset_FP
- \+ *lemma* FP.singleton
- \+ *lemma* FP.mul_two
- \+ *lemma* FP.finset_prod
- \+ *theorem* asserts
- \+ *def* ultrafilter.has_mul
- \+ *def* ultrafilter.semigroup

modified src/data/stream/basic.lean
- \+ *lemma* head_drop

modified src/order/filter/ultrafilter.lean

created src/topology/algebra/semigroup.lean
- \+ *lemma* exists_idempotent_of_compact_t2_of_continuous_mul_left
- \+ *lemma* exists_idempotent_in_compact_subsemigroup



## [2021-11-23 15:06:10](https://github.com/leanprover-community/mathlib/commit/050482c)
doc(measure_theory/decomposition/jordan): typo ([#10430](https://github.com/leanprover-community/mathlib/pull/10430))
#### Estimated changes
modified src/measure_theory/decomposition/jordan.lean



## [2021-11-23 15:06:08](https://github.com/leanprover-community/mathlib/commit/53bd9d7)
feat(field_theory): generalize `ratfunc K` to `comm_ring K`/`is_domain K` ([#10428](https://github.com/leanprover-community/mathlib/pull/10428))
Fixes one of the TODO's from the original ratfunc PR: apply all the easy generalizations where `K` doesn't need to be a field, only a `is_domain K` or even just `comm_ring K`.
This would allow us to use `ratfunc` in [#10421](https://github.com/leanprover-community/mathlib/pull/10421).
#### Estimated changes
modified src/field_theory/ratfunc.lean
- \+/\- *lemma* num_C
- \+/\- *lemma* denom_C
- \+/\- *lemma* num_C
- \+/\- *lemma* denom_C



## [2021-11-23 15:06:07](https://github.com/leanprover-community/mathlib/commit/7958251)
doc(field_theory/abel_ruffini): update module doc ([#10426](https://github.com/leanprover-community/mathlib/pull/10426))
#### Estimated changes
modified src/field_theory/abel_ruffini.lean



## [2021-11-23 15:06:06](https://github.com/leanprover-community/mathlib/commit/2b75493)
refactor(algebra.group.basic): Convert sub_add_cancel and neg_sub to multaplicative form ([#10419](https://github.com/leanprover-community/mathlib/pull/10419))
Currently mathlib has a rich set of lemmas connecting the addition, subtraction and negation additive group operations, but a far thinner collection of results for multiplication, division and inverse multiplicative group operations, despite the fact that the former can be generated easily from the latter via `to_additive`.
In  [#9548](https://github.com/leanprover-community/mathlib/pull/9548) I require multiplicative forms of the existing `sub_add_cancel` and `neg_sub` lemmas. This PR refactors them as the equivalent multiplicative results and then recovers `sub_add_cancel` and `neg_sub` via `to_additive`. There is a complication in that unfortunately `group_with_zero` already has lemmas named `inv_div` and `div_mul_cancel`. I have worked around this by naming the lemmas in this PR `inv_div'` and `div_mul_cancel'` and then manually overriding the names generated by `to_additive`. Other suggestions as to how to approach this welcome.
#### Estimated changes
modified src/algebra/group/basic.lean
- \+ *lemma* inv_div'
- \+ *lemma* div_mul_cancel'
- \- *lemma* sub_add_cancel
- \- *lemma* neg_sub



## [2021-11-23 15:06:04](https://github.com/leanprover-community/mathlib/commit/d0e454a)
feat(logic/function/basic): add `function.{in,sur,bi}jective.comp_left` ([#10406](https://github.com/leanprover-community/mathlib/pull/10406))
As far as I can tell we don't have these variations.
Note that the `surjective` and `bijective` versions do not appear next to the other composition statements, as they require `surj_inv` to concisely prove.
#### Estimated changes
modified src/logic/function/basic.lean
- \+ *lemma* injective.comp_left
- \+ *lemma* surjective.comp_left
- \+ *lemma* bijective.comp_left



## [2021-11-23 13:11:55](https://github.com/leanprover-community/mathlib/commit/d9e40b4)
chore(measure_theory/integral): generalize `interval_integral.norm_integral_le_integral_norm` ([#10412](https://github.com/leanprover-community/mathlib/pull/10412))
It was formulated only for functions `f : α → ℝ`; generalize to `f : α → E`.
#### Estimated changes
modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* norm_integral_le_integral_norm
- \+/\- *lemma* norm_integral_le_integral_norm



## [2021-11-23 13:11:54](https://github.com/leanprover-community/mathlib/commit/2817788)
chore(measure_theory/integral): add `integrable_const` for `interval_integral` ([#10410](https://github.com/leanprover-community/mathlib/pull/10410))
#### Estimated changes
modified src/measure_theory/integral/integrable_on.lean
- \+/\- *lemma* integrable_on_const
- \+/\- *lemma* integrable_on_const

modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* interval_integrable_const_iff
- \+ *lemma* interval_integrable_const

modified src/measure_theory/measure/measure_space.lean



## [2021-11-23 13:11:53](https://github.com/leanprover-community/mathlib/commit/3b13744)
chore(measure_theory/integral): more versions of `integral_finset_sum` ([#10394](https://github.com/leanprover-community/mathlib/pull/10394))
* fix assumptions in existing lemmas (`∀ i ∈ s` instead of `∀ i`);
* add a version for interval integrals.
#### Estimated changes
modified src/measure_theory/function/l1_space.lean

modified src/measure_theory/integral/bochner.lean
- \+/\- *lemma* integral_finset_sum
- \+/\- *lemma* integral_finset_sum

modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* integral_finset_sum



## [2021-11-23 13:11:52](https://github.com/leanprover-community/mathlib/commit/2ec6de7)
feat(topology/connected): sufficient conditions for the preimage of a connected set to be connected ([#10289](https://github.com/leanprover-community/mathlib/pull/10289))
and other simple connectedness results
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* nonempty.preimage'

modified src/data/set/lattice.lean
- \+ *lemma* subset_left_of_subset_union
- \+ *lemma* subset_right_of_subset_union

modified src/topology/connected.lean
- \+ *lemma* is_preconnected.preimage_of_open_map
- \+ *lemma* is_preconnected.preimage_of_closed_map
- \+ *lemma* is_connected.preimage_of_open_map
- \+ *lemma* is_connected.preimage_of_closed_map
- \+ *lemma* is_preconnected.subset_or_subset
- \+ *lemma* is_preconnected.subset_left_of_subset_union
- \+ *lemma* is_preconnected.subset_right_of_subset_union



## [2021-11-23 13:11:50](https://github.com/leanprover-community/mathlib/commit/e8386bd)
feat(group_theory/exponent): Define the exponent of a group ([#10249](https://github.com/leanprover-community/mathlib/pull/10249))
This PR provides the definition and some very basic API for the exponent of a group/monoid.
#### Estimated changes
modified src/algebra/gcd_monoid/finset.lean
- \+ *theorem* lcm_eq_zero_iff

modified src/algebra/gcd_monoid/multiset.lean
- \+ *theorem* lcm_eq_zero_iff

created src/group_theory/exponent.lean
- \+ *lemma* pow_exponent_eq_one
- \+ *lemma* pow_eq_mod_exponent
- \+ *lemma* exponent_pos_of_exists
- \+ *lemma* exponent_min'
- \+ *lemma* exponent_min
- \+ *lemma* exp_eq_one_of_subsingleton
- \+ *lemma* order_dvd_exponent
- \+ *lemma* exponent_dvd_of_forall_pow_eq_one
- \+ *lemma* lcm_order_of_dvd_exponent
- \+ *lemma* lcm_order_eq_exponent
- \+ *def* exponent_exists



## [2021-11-23 13:11:48](https://github.com/leanprover-community/mathlib/commit/cf91773)
refactor(*): split `order_{top,bot}` from `lattice` hierarchy ([#9891](https://github.com/leanprover-community/mathlib/pull/9891))
Rename `bounded_lattice` to `bounded_order`.
Split out `order_{top,bot}` and `bounded_order` from the order hierarchy.
That means that we no longer have `semilattice_{sup,inf}_{top,bot}`, but use the `[order_top]` as a mixin to `semilattice_inf`, for example.
Similarly, `lattice` and `bounded_order` instead of what was before `bounded_lattice`.
Similarly, `distrib_lattice` and `bounded_order` instead of what was before `bounded_distrib_lattice`.
#### Estimated changes
modified scripts/nolints.txt

modified src/algebra/associated.lean

modified src/algebra/big_operators/basic.lean

modified src/algebra/order/monoid.lean

modified src/algebra/order/nonneg.lean

modified src/algebra/tropical/basic.lean

modified src/analysis/box_integral/box/basic.lean

modified src/analysis/box_integral/partition/basic.lean

modified src/analysis/box_integral/partition/filter.lean

modified src/analysis/normed_space/enorm.lean

modified src/category_theory/filtered.lean

modified src/category_theory/limits/lattice.lean
- \+/\- *lemma* finite_limit_eq_finset_univ_inf
- \+/\- *lemma* finite_colimit_eq_finset_univ_sup
- \+/\- *lemma* finite_product_eq_finset_inf
- \+/\- *lemma* finite_coproduct_eq_finset_sup
- \+/\- *lemma* prod_eq_inf
- \+/\- *lemma* coprod_eq_sup
- \+/\- *lemma* pullback_eq_inf
- \+/\- *lemma* pushout_eq_sup
- \+/\- *lemma* finite_limit_eq_finset_univ_inf
- \+/\- *lemma* finite_colimit_eq_finset_univ_sup
- \+/\- *lemma* finite_product_eq_finset_inf
- \+/\- *lemma* finite_coproduct_eq_finset_sup
- \+/\- *lemma* prod_eq_inf
- \+/\- *lemma* coprod_eq_sup
- \+/\- *lemma* pullback_eq_inf
- \+/\- *lemma* pushout_eq_sup
- \+/\- *def* finite_limit_cone
- \+/\- *def* finite_colimit_cocone
- \+/\- *def* finite_limit_cone
- \+/\- *def* finite_colimit_cocone

modified src/category_theory/sites/grothendieck.lean
- \+ *lemma* le_def

modified src/category_theory/sites/plus.lean

modified src/category_theory/sites/pretopology.lean
- \+ *lemma* le_def

modified src/category_theory/sites/sheafification.lean

modified src/category_theory/subobject/lattice.lean

modified src/combinatorics/colex.lean

modified src/combinatorics/simple_graph/subgraph.lean

modified src/data/fin/basic.lean

modified src/data/finset/basic.lean

modified src/data/finset/lattice.lean
- \+/\- *lemma* comp_sup_eq_sup_comp
- \+/\- *lemma* comp_sup_eq_sup_comp_of_is_total
- \+/\- *lemma* sup_le_of_le_directed
- \+/\- *lemma* disjoint_sup_right
- \+/\- *lemma* disjoint_sup_left
- \+/\- *lemma* comp_inf_eq_inf_comp
- \+/\- *lemma* comp_inf_eq_inf_comp_of_is_total
- \+/\- *lemma* sup_finset_image
- \+/\- *lemma* comp_sup_eq_sup_comp
- \+/\- *lemma* comp_sup_eq_sup_comp_of_is_total
- \+/\- *lemma* sup_le_of_le_directed
- \+/\- *lemma* disjoint_sup_right
- \+/\- *lemma* disjoint_sup_left
- \+/\- *lemma* comp_inf_eq_inf_comp
- \+/\- *lemma* comp_inf_eq_inf_comp_of_is_total
- \+/\- *lemma* sup_finset_image

modified src/data/finset/pairwise.lean
- \+/\- *lemma* pairwise_disjoint.image_finset_of_le
- \+/\- *lemma* pairwise_disjoint.image_finset_of_le

modified src/data/finsupp/basic.lean

modified src/data/finsupp/lattice.lean
- \+/\- *lemma* support_sup
- \+/\- *lemma* support_sup

modified src/data/fintype/basic.lean

modified src/data/list/min_max.lean

modified src/data/multiset/basic.lean

modified src/data/multiset/lattice.lean

modified src/data/mv_polynomial/variables.lean

modified src/data/nat/basic.lean

modified src/data/nat/enat.lean

modified src/data/part.lean

modified src/data/pequiv.lean

modified src/data/pnat/factors.lean

modified src/data/real/ennreal.lean

modified src/data/real/nnreal.lean

modified src/data/semiquot.lean

modified src/data/set/intervals/basic.lean
- \+/\- *lemma* Icc_bot_top
- \+/\- *lemma* Icc_bot_top

modified src/data/set/pairwise.lean
- \+/\- *lemma* pairwise_disjoint_on_bool
- \+/\- *lemma* pairwise_disjoint_on
- \+/\- *lemma* pairwise_disjoint_on_bool
- \+/\- *lemma* pairwise_disjoint_on

modified src/linear_algebra/linear_pmap.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/function/l1_space.lean

modified src/measure_theory/integral/bochner.lean

modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* finset_sup_apply
- \+/\- *lemma* finset_sup_apply

modified src/measure_theory/measurable_space.lean

modified src/measure_theory/measurable_space_def.lean
- \+ *lemma* le_def

modified src/measure_theory/measure/measure_space.lean

modified src/measure_theory/pi_system.lean
- \+ *lemma* le_def

modified src/measure_theory/probability_mass_function/basic.lean

modified src/order/atoms.lean
- \+/\- *lemma* is_atom.inf_eq_bot_of_ne
- \+/\- *lemma* is_atom.disjoint_of_ne
- \+/\- *lemma* is_coatom.sup_eq_top_of_ne
- \+/\- *lemma* is_coatom_dual_iff_is_atom
- \+/\- *lemma* is_atom_dual_iff_is_coatom
- \+/\- *lemma* is_atom_iff
- \+/\- *lemma* is_coatom_iff
- \+/\- *lemma* is_simple_lattice_iff
- \+/\- *lemma* is_simple_lattice
- \+/\- *lemma* is_atomic_iff
- \+/\- *lemma* is_coatomic_iff
- \+/\- *lemma* is_atom.inf_eq_bot_of_ne
- \+/\- *lemma* is_atom.disjoint_of_ne
- \+/\- *lemma* is_coatom.sup_eq_top_of_ne
- \+/\- *lemma* is_coatom_dual_iff_is_atom
- \+/\- *lemma* is_atom_dual_iff_is_coatom
- \+/\- *lemma* is_atom_iff
- \+/\- *lemma* is_coatom_iff
- \+/\- *lemma* is_simple_lattice_iff
- \+/\- *lemma* is_simple_lattice
- \+/\- *lemma* is_atomic_iff
- \+/\- *lemma* is_coatomic_iff
- \+/\- *theorem* is_simple_lattice_iff_is_simple_lattice_order_dual
- \+/\- *theorem* is_simple_lattice_iff_is_atom_top
- \+/\- *theorem* is_simple_lattice_iff_is_coatom_bot
- \+/\- *theorem* is_simple_lattice_Iic_iff_is_atom
- \+/\- *theorem* is_simple_lattice_Ici_iff_is_coatom
- \+/\- *theorem* is_simple_lattice_iff_is_simple_lattice_order_dual
- \+/\- *theorem* is_simple_lattice_iff_is_atom_top
- \+/\- *theorem* is_simple_lattice_iff_is_coatom_bot
- \+/\- *theorem* is_simple_lattice_Iic_iff_is_atom
- \+/\- *theorem* is_simple_lattice_Ici_iff_is_coatom

modified src/order/basic.lean
- \+/\- *lemma* pi.le_def
- \+/\- *lemma* pi.le_def

modified src/order/boolean_algebra.lean
- \+ *lemma* boolean_algebra.core.sdiff_eq
- \+/\- *lemma* pi.compl_apply
- \+/\- *lemma* pi.compl_apply
- \+ *def* boolean_algebra.core.sdiff

renamed src/order/bounded_lattice.lean to src/order/bounded_order.lean
- \+ *lemma* inf_eq_bot_iff_le_compl
- \+/\- *lemma* eq_bot_of_bot_eq_top
- \+/\- *lemma* eq_top_of_bot_eq_top
- \+/\- *lemma* subsingleton_of_top_le_bot
- \+/\- *lemma* subsingleton_of_bot_eq_top
- \+/\- *lemma* subsingleton_iff_bot_eq_top
- \+/\- *lemma* is_compl_bot_top
- \+/\- *lemma* is_compl_top_bot
- \+/\- *lemma* eq_bot_of_bot_eq_top
- \+/\- *lemma* eq_top_of_bot_eq_top
- \+/\- *lemma* subsingleton_of_top_le_bot
- \+/\- *lemma* subsingleton_of_bot_eq_top
- \+/\- *lemma* subsingleton_iff_bot_eq_top
- \+/\- *lemma* is_compl_bot_top
- \+/\- *lemma* is_compl_top_bot
- \+/\- *theorem* order_top.ext
- \+/\- *theorem* order_bot.ext_bot
- \+/\- *theorem* order_bot.ext
- \+ *theorem* bounded_order.ext
- \+/\- *theorem* order_top.ext
- \+/\- *theorem* order_bot.ext_bot
- \+/\- *theorem* order_bot.ext
- \- *theorem* bounded_lattice.ext

modified src/order/complete_boolean_algebra.lean

modified src/order/complete_lattice.lean

modified src/order/conditionally_complete_lattice.lean

modified src/order/copy.lean
- \+ *def* bounded_order.copy
- \+ *def* lattice.copy
- \- *def* bounded_lattice.copy

modified src/order/filter/basic.lean

modified src/order/filter/germ.lean

modified src/order/galois_connection.lean
- \+ *def* lift_bounded_order
- \+ *def* lift_bounded_order
- \- *def* lift_bounded_lattice
- \- *def* lift_bounded_lattice

modified src/order/lattice_intervals.lean
- \+/\- *def* order_bot
- \+/\- *def* order_top
- \+ *def* bounded_order
- \- *def* semilattice_inf_bot
- \- *def* semilattice_sup_top
- \+/\- *def* order_bot
- \+/\- *def* order_top
- \- *def* semilattice_inf_bot
- \- *def* semilattice_inf_top
- \- *def* semilattice_sup_bot
- \- *def* semilattice_sup_top
- \- *def* bounded_lattice

modified src/order/modular_lattice.lean

modified src/order/partial_sups.lean
- \+/\- *lemma* partial_sups_eq_sup_range
- \+/\- *lemma* partial_sups_disjoint_of_disjoint
- \+/\- *lemma* partial_sups_eq_sup_range
- \+/\- *lemma* partial_sups_disjoint_of_disjoint

modified src/order/preorder_hom.lean

modified src/order/rel_iso.lean
- \+/\- *lemma* disjoint.map_order_iso
- \+/\- *lemma* disjoint_map_order_iso_iff
- \+/\- *lemma* disjoint.map_order_iso
- \+/\- *lemma* disjoint_map_order_iso_iff

modified src/order/succ_pred.lean

modified src/order/sup_indep.lean
- \+/\- *lemma* sup_indep.sup
- \+/\- *lemma* sup_indep.bUnion
- \+/\- *lemma* sup_indep_iff_pairwise_disjoint
- \+/\- *lemma* sup_indep.sup
- \+/\- *lemma* sup_indep.bUnion
- \+/\- *lemma* sup_indep_iff_pairwise_disjoint

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/unique_factorization_domain.lean

modified src/tactic/monotonicity/basic.lean

modified src/topology/algebra/open_subgroup.lean

modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* nhds_top_basis
- \+/\- *lemma* nhds_bot_basis
- \+/\- *lemma* nhds_top_basis_Ici
- \+/\- *lemma* nhds_bot_basis_Iic
- \+/\- *lemma* nhds_top_basis
- \+/\- *lemma* nhds_bot_basis
- \+/\- *lemma* nhds_top_basis_Ici
- \+/\- *lemma* nhds_bot_basis_Iic

modified src/topology/compacts.lean

modified src/topology/dense_embedding.lean

modified src/topology/discrete_quotient.lean

modified src/topology/instances/nnreal.lean

modified src/topology/metric_space/contracting.lean

modified src/topology/order.lean

modified test/transport/basic.lean
- \+ *def* sup.map
- \- *def* sup_top.map



## [2021-11-23 11:49:18](https://github.com/leanprover-community/mathlib/commit/3fee4b9)
chore(control/random): Move from `system.random.basic` ([#10408](https://github.com/leanprover-community/mathlib/pull/10408))
The top folder `system` contains a single file, apparently because it mimics Lean core's organisation. This moves it under `control.` and gets rid of one top folder.
#### Estimated changes
renamed src/system/random/basic.lean to src/control/random.lean

modified src/testing/slim_check/gen.lean

modified test/random.lean



## [2021-11-23 11:49:16](https://github.com/leanprover-community/mathlib/commit/b1a9c2e)
feat(analysis/normed_space/multilinear): add `norm_mk_pi_field` ([#10396](https://github.com/leanprover-community/mathlib/pull/10396))
Also upgrade the corresponding equivalence to a `linear_isometry`.
#### Estimated changes
modified src/analysis/calculus/iterated_deriv.lean

modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* symm_comp_self
- \+ *lemma* self_comp_symm

modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* norm_mk_pi_field



## [2021-11-23 11:49:15](https://github.com/leanprover-community/mathlib/commit/87b0084)
chore(field_theory/separable): generalize theorems ([#10337](https://github.com/leanprover-community/mathlib/pull/10337))
#### Estimated changes
modified src/data/polynomial/algebra_map.lean
- \+/\- *theorem* not_is_unit_X_sub_C
- \+/\- *theorem* not_is_unit_X_sub_C

modified src/data/polynomial/ring_division.lean

modified src/field_theory/finite/basic.lean

modified src/field_theory/primitive_element.lean

modified src/field_theory/separable.lean
- \+ *lemma* separable_of_subsingleton
- \+/\- *lemma* is_unit_of_self_mul_dvd_separable
- \+/\- *lemma* multiplicity_le_one_of_separable
- \+/\- *lemma* separable.squarefree
- \+/\- *lemma* nodup_of_separable_prod
- \+/\- *lemma* separable_X_pow_sub_C_unit
- \+/\- *lemma* root_multiplicity_le_one_of_separable
- \+/\- *lemma* count_roots_le_one
- \+/\- *lemma* nodup_roots
- \+/\- *lemma* separable_prod_X_sub_C_iff'
- \+/\- *lemma* separable_prod_X_sub_C_iff
- \+/\- *lemma* eq_X_sub_C_of_separable_of_root_eq
- \+/\- *lemma* is_unit_of_self_mul_dvd_separable
- \+/\- *lemma* separable_prod_X_sub_C_iff'
- \+/\- *lemma* separable_prod_X_sub_C_iff
- \- *lemma* not_unit_X_sub_C
- \+/\- *lemma* nodup_of_separable_prod
- \+/\- *lemma* multiplicity_le_one_of_separable
- \+/\- *lemma* separable.squarefree
- \+/\- *lemma* separable_X_pow_sub_C_unit
- \- *lemma* squarefree_X_pow_sub_C
- \+/\- *lemma* root_multiplicity_le_one_of_separable
- \+/\- *lemma* count_roots_le_one
- \+/\- *lemma* nodup_roots
- \+/\- *lemma* eq_X_sub_C_of_separable_of_root_eq
- \+ *theorem* expand_zero
- \+/\- *theorem* coeff_contract
- \+ *theorem* contract_expand
- \+/\- *theorem* expand_contract
- \+/\- *theorem* expand_char
- \+/\- *theorem* map_expand_pow_char
- \+/\- *theorem* of_irreducible_expand
- \+/\- *theorem* of_irreducible_expand_pow
- \+/\- *theorem* exists_separable_of_irreducible
- \+/\- *theorem* is_unit_or_eq_zero_of_separable_expand
- \+/\- *theorem* unique_separable_of_irreducible
- \+ *theorem* _root_.irreducible.separable
- \+/\- *theorem* coeff_contract
- \+/\- *theorem* of_irreducible_expand
- \+/\- *theorem* of_irreducible_expand_pow
- \+/\- *theorem* expand_char
- \+/\- *theorem* map_expand_pow_char
- \+/\- *theorem* expand_contract
- \+/\- *theorem* exists_separable_of_irreducible
- \+/\- *theorem* is_unit_or_eq_zero_of_separable_expand
- \+/\- *theorem* unique_separable_of_irreducible
- \- *theorem* irreducible.separable

modified src/field_theory/separable_degree.lean

modified src/ring_theory/norm.lean

modified src/ring_theory/polynomial/cyclotomic.lean

modified src/ring_theory/roots_of_unity.lean

modified src/ring_theory/trace.lean



## [2021-11-23 11:49:14](https://github.com/leanprover-community/mathlib/commit/9cf6766)
feat(order/filter/pi): define `filter.pi` and prove some properties ([#10323](https://github.com/leanprover-community/mathlib/pull/10323))
#### Estimated changes
modified src/analysis/box_integral/box/subbox_induction.lean

modified src/analysis/calculus/tangent_cone.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/constructions/pi.lean
- \+ *lemma* ae_pi_le_pi
- \- *lemma* ae_pi_le_infi_comap

modified src/measure_theory/constructions/prod.lean

modified src/measure_theory/function/strongly_measurable.lean

modified src/measure_theory/measure/haar_lebesgue.lean

modified src/order/filter/basic.lean
- \- *lemma* mem_Coprod_iff
- \- *lemma* compl_mem_Coprod_iff
- \- *lemma* Coprod_ne_bot_iff'
- \- *lemma* Coprod_ne_bot_iff
- \- *lemma* ne_bot.Coprod
- \- *lemma* Coprod_ne_bot
- \- *lemma* Coprod_mono
- \- *lemma* map_pi_map_Coprod_le
- \- *lemma* tendsto.pi_map_Coprod

modified src/order/filter/cofinite.lean

created src/order/filter/pi.lean
- \+ *lemma* tendsto_eval_pi
- \+ *lemma* tendsto_pi
- \+ *lemma* le_pi
- \+ *lemma* pi_mono
- \+ *lemma* mem_pi_of_mem
- \+ *lemma* pi_mem_pi
- \+ *lemma* mem_pi
- \+ *lemma* mem_pi'
- \+ *lemma* mem_of_pi_mem_pi
- \+ *lemma* pi_mem_pi_iff
- \+ *lemma* pi_inf_principal_univ_pi_eq_bot
- \+ *lemma* pi_inf_principal_pi_eq_bot
- \+ *lemma* pi_inf_principal_univ_pi_ne_bot
- \+ *lemma* pi_inf_principal_pi_ne_bot
- \+ *lemma* pi_eq_bot
- \+ *lemma* pi_ne_bot
- \+ *lemma* mem_Coprod_iff
- \+ *lemma* compl_mem_Coprod_iff
- \+ *lemma* Coprod_ne_bot_iff'
- \+ *lemma* Coprod_ne_bot_iff
- \+ *lemma* ne_bot.Coprod
- \+ *lemma* Coprod_ne_bot
- \+ *lemma* Coprod_mono
- \+ *lemma* map_pi_map_Coprod_le
- \+ *lemma* tendsto.pi_map_Coprod
- \+ *def* pi

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/ordered/basic.lean

modified src/topology/algebra/ordered/monotone_convergence.lean

modified src/topology/algebra/weak_dual_topology.lean

modified src/topology/bases.lean

modified src/topology/constructions.lean
- \+ *lemma* tendsto_pi_nhds
- \+ *lemma* mem_nhds_of_pi_mem_nhds
- \+/\- *lemma* set_pi_mem_nhds_iff
- \+/\- *lemma* interior_pi_set
- \- *lemma* tendsto_pi
- \- *lemma* mem_nhds_pi
- \+/\- *lemma* set_pi_mem_nhds_iff
- \+/\- *lemma* interior_pi_set

modified src/topology/continuous_on.lean
- \- *lemma* nhds_within_pi_univ_eq_bot

modified src/topology/sequences.lean

modified src/topology/subset_properties.lean

modified src/topology/uniform_space/pi.lean



## [2021-11-23 11:49:13](https://github.com/leanprover-community/mathlib/commit/33ea401)
feat(linear_algebra/affine_space/barycentric_coords): barycentric coordinates are ratio of determinants ([#10320](https://github.com/leanprover-community/mathlib/pull/10320))
The main goal of this PR is the new lemma `affine_basis.det_smul_coords_eq_camer_coords`
A secondary goal is a minor refactor of barycentric coordinates so that they are associated to a new structure `affine_basis`. As well as making the API for affine spaces more similar to that of modules, this enables an extremely useful dot notation.
The work here could easily be split into two PRs and I will happily do so if requested.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/analysis/convex/combination.lean
- \+/\- *lemma* convex_hull_affine_basis_eq_nonneg_barycentric
- \+/\- *lemma* convex_hull_affine_basis_eq_nonneg_barycentric

modified src/analysis/normed_space/add_torsor_bases.lean
- \+/\- *lemma* continuous_barycentric_coord
- \+/\- *lemma* continuous_barycentric_coord

modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* basis_of_apply
- \+ *lemma* coord_apply_eq
- \+ *lemma* coord_apply_neq
- \+ *lemma* coord_apply
- \+ *lemma* coord_apply_combination_of_mem
- \+ *lemma* coord_apply_combination_of_not_mem
- \+ *lemma* sum_coord_apply_eq_one
- \+ *lemma* affine_combination_coord_eq_self
- \+ *lemma* coe_coord_of_subsingleton_eq_one
- \+ *lemma* surjective_coord
- \+ *lemma* coords_apply
- \+ *lemma* to_matrix_apply
- \+ *lemma* to_matrix_self
- \+ *lemma* to_matrix_vec_mul_coords
- \+ *lemma* to_matrix_mul_to_matrix
- \+ *lemma* is_unit_to_matrix
- \+ *lemma* to_matrix_inv_vec_mul_to_matrix
- \+ *lemma* det_smul_coords_eq_cramer_coords
- \- *lemma* basis_of_aff_ind_span_eq_top_apply
- \- *lemma* barycentric_coord_apply_eq
- \- *lemma* barycentric_coord_apply_neq
- \- *lemma* barycentric_coord_apply
- \- *lemma* barycentric_coord_apply_combination_of_mem
- \- *lemma* barycentric_coord_apply_combination_of_not_mem
- \- *lemma* sum_barycentric_coord_apply_eq_one
- \- *lemma* affine_combination_barycentric_coord_eq_self
- \- *lemma* coe_barycentric_coord_of_subsingleton_eq_one
- \- *lemma* surjective_barycentric_coord

modified src/linear_algebra/affine_space/basic.lean

modified src/linear_algebra/matrix/adjugate.lean
- \+ *lemma* cramer_transpose_apply

modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* det_smul_inv_vec_mul_eq_cramer_transpose



## [2021-11-23 11:49:12](https://github.com/leanprover-community/mathlib/commit/d94772b)
feat(algebra/big_operators/finprod): add finprod_div_distrib and finsum_sub_distrib ([#10044](https://github.com/leanprover-community/mathlib/pull/10044))
#### Estimated changes
modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_div_distrib
- \+ *lemma* mul_equiv.map_finprod_mem
- \+ *lemma* finprod_mem_inv_distrib
- \+ *lemma* finprod_mem_div_distrib



## [2021-11-23 09:38:33](https://github.com/leanprover-community/mathlib/commit/ac71292)
chore(measure_theory/integral): generalize `integral_smul_const` ([#10411](https://github.com/leanprover-community/mathlib/pull/10411))
* generalize to `is_R_or_C`;
* add an `interval_integral` version.
#### Estimated changes
modified src/analysis/special_functions/integrals.lean
- \- *lemma* integral_const_mul
- \- *lemma* integral_mul_const
- \- *lemma* integral_div

modified src/measure_theory/function/conditional_expectation.lean

modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* integral_smul_const
- \+ *lemma* integral_const_mul
- \+ *lemma* integral_mul_const
- \+ *lemma* integral_div

modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* integral_smul_const
- \+/\- *lemma* integral_smul_const



## [2021-11-23 09:38:32](https://github.com/leanprover-community/mathlib/commit/8f681f1)
chore(data/complex): add a few simp lemmas ([#10395](https://github.com/leanprover-community/mathlib/pull/10395))
#### Estimated changes
modified src/data/complex/basic.lean
- \+ *lemma* abs_pow
- \+ *lemma* abs_zpow

modified src/data/complex/exponential.lean
- \+/\- *lemma* abs_cos_add_sin_mul_I
- \+ *lemma* abs_exp_of_real_mul_I
- \+/\- *lemma* abs_cos_add_sin_mul_I



## [2021-11-23 09:38:31](https://github.com/leanprover-community/mathlib/commit/4d5d770)
feat(data/complex/exponential): Add lemma add_one_le_exp ([#10358](https://github.com/leanprover-community/mathlib/pull/10358))
This PR resolves https://github.com/leanprover-community/mathlib/blob/master/src/data/complex/exponential.lean#L1140
#### Estimated changes
modified src/analysis/special_functions/exp.lean

modified src/data/complex/exponential.lean
- \+ *lemma* exp_bound'
- \+ *lemma* exp_bound_div_one_sub_of_interval_approx
- \+ *lemma* exp_bound_div_one_sub_of_interval
- \+ *lemma* one_sub_le_exp_minus_of_pos
- \+ *lemma* add_one_le_exp_of_nonpos
- \+ *lemma* add_one_le_exp



## [2021-11-23 07:23:05](https://github.com/leanprover-community/mathlib/commit/6050f9d)
feat(algebraic_geometry, category_theory): SheafedSpace has colimits ([#10401](https://github.com/leanprover-community/mathlib/pull/10401))
#### Estimated changes
modified src/algebraic_geometry/sheafed_space.lean

modified src/category_theory/limits/creates.lean
- \+ *def* creates_colimit_of_fully_faithful_of_lift
- \+ *def* creates_colimit_of_fully_faithful_of_iso

modified src/topology/sheaves/limits.lean
- \+ *lemma* is_sheaf_of_is_limit
- \+ *lemma* limit_is_sheaf

modified src/topology/sheaves/sheaf_condition/sites.lean
- \+ *def* Sheaf_spaces_equiv_sheaf_sites
- \+ *def* Sheaf_spaces_equiv_sheaf_sites_functor_forget
- \+ *def* Sheaf_spaces_equiv_sheaf_sites_inverse_forget
- \- *def* Sheaf_spaces_equivelence_sheaf_sites



## [2021-11-23 07:23:04](https://github.com/leanprover-community/mathlib/commit/ca7347c)
refactor(ring_theory/sub[semi]ring): move pointwise instances to their own file ([#10347](https://github.com/leanprover-community/mathlib/pull/10347))
This matches how we have separate pointwise files for `submonoid` and `subgroup`.
All the new lemmas are direct copies of the subgroup lemmas.
#### Estimated changes
modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean

modified src/algebra/algebra/subalgebra.lean

modified src/algebra/category/CommRing/limits.lean

modified src/algebra/char_p/subring.lean

modified src/algebra/group_ring_action.lean
- \- *lemma* coe_pointwise_smul
- \- *lemma* pointwise_smul_to_add_submonoid
- \- *lemma* smul_mem_pointwise_smul
- \- *lemma* coe_pointwise_smul
- \- *lemma* pointwise_smul_to_add_subgroup
- \- *lemma* pointwise_smul_to_subsemiring
- \- *lemma* smul_mem_pointwise_smul

modified src/algebraic_geometry/structure_sheaf.lean

modified src/deprecated/subring.lean

modified src/ring_theory/perfection.lean

renamed src/ring_theory/subring.lean to src/ring_theory/subring/basic.lean

created src/ring_theory/subring/pointwise.lean
- \+ *lemma* pointwise_smul_def
- \+ *lemma* coe_pointwise_smul
- \+ *lemma* pointwise_smul_to_add_subgroup
- \+ *lemma* pointwise_smul_to_subsemiring
- \+ *lemma* smul_mem_pointwise_smul
- \+ *lemma* smul_mem_pointwise_smul_iff
- \+ *lemma* mem_pointwise_smul_iff_inv_smul_mem
- \+ *lemma* mem_inv_pointwise_smul_iff
- \+ *lemma* pointwise_smul_le_pointwise_smul_iff
- \+ *lemma* pointwise_smul_subset_iff
- \+ *lemma* subset_pointwise_smul_iff
- \+ *lemma* smul_mem_pointwise_smul_iff₀
- \+ *lemma* mem_pointwise_smul_iff_inv_smul_mem₀
- \+ *lemma* mem_inv_pointwise_smul_iff₀
- \+ *lemma* pointwise_smul_le_pointwise_smul_iff₀
- \+ *lemma* pointwise_smul_le_iff₀
- \+ *lemma* le_pointwise_smul_iff₀

renamed src/ring_theory/subsemiring.lean to src/ring_theory/subsemiring/basic.lean

created src/ring_theory/subsemiring/pointwise.lean
- \+ *lemma* pointwise_smul_def
- \+ *lemma* coe_pointwise_smul
- \+ *lemma* pointwise_smul_to_add_submonoid
- \+ *lemma* smul_mem_pointwise_smul
- \+ *lemma* smul_mem_pointwise_smul_iff
- \+ *lemma* mem_pointwise_smul_iff_inv_smul_mem
- \+ *lemma* mem_inv_pointwise_smul_iff
- \+ *lemma* pointwise_smul_le_pointwise_smul_iff
- \+ *lemma* pointwise_smul_subset_iff
- \+ *lemma* subset_pointwise_smul_iff
- \+ *lemma* smul_mem_pointwise_smul_iff₀
- \+ *lemma* mem_pointwise_smul_iff_inv_smul_mem₀
- \+ *lemma* mem_inv_pointwise_smul_iff₀
- \+ *lemma* pointwise_smul_le_pointwise_smul_iff₀
- \+ *lemma* pointwise_smul_le_iff₀
- \+ *lemma* le_pointwise_smul_iff₀

modified src/topology/algebra/ring.lean

modified src/topology/instances/real.lean



## [2021-11-23 07:23:02](https://github.com/leanprover-community/mathlib/commit/a586681)
feat(category_theory/limits/shapes): Multiequalizer is the equalizer ([#10267](https://github.com/leanprover-community/mathlib/pull/10267))
#### Estimated changes
modified src/category_theory/limits/shapes/equalizers.lean

modified src/category_theory/limits/shapes/multiequalizer.lean
- \+ *lemma* fst_pi_map_π
- \+ *lemma* snd_pi_map_π
- \+ *lemma* ι_fst_sigma_map
- \+ *lemma* ι_snd_sigma_map
- \+ *lemma* pi_condition
- \+ *lemma* to_pi_fork_π_app_zero
- \+ *lemma* to_pi_fork_π_app_one
- \+ *lemma* of_pi_fork_π_app_left
- \+ *lemma* of_pi_fork_π_app_right
- \+ *lemma* sigma_condition
- \+ *lemma* to_sigma_cofork_ι_app_zero
- \+ *lemma* to_sigma_cofork_ι_app_one
- \+ *lemma* of_sigma_cofork_ι_app_left
- \+ *lemma* of_sigma_cofork_ι_app_right
- \+ *lemma* ι_pi_π
- \+ *lemma* ι_sigma_π
- \+ *def* fst_pi_map
- \+ *def* snd_pi_map
- \+ *def* parallel_pair_diagram
- \+ *def* fst_sigma_map
- \+ *def* snd_sigma_map
- \+ *def* to_pi_fork
- \+ *def* of_pi_fork
- \+ *def* to_pi_fork_functor
- \+ *def* of_pi_fork_functor
- \+ *def* multifork_equiv_pi_fork
- \+ *def* to_sigma_cofork
- \+ *def* of_sigma_cofork
- \+ *def* to_sigma_cofork_functor
- \+ *def* of_sigma_cofork_functor
- \+ *def* multicofork_equiv_sigma_cofork
- \+ *def* iso_equalizer
- \+ *def* ι_pi
- \+ *def* iso_coequalizer
- \+ *def* sigma_π
- \- *def* multifork
- \- *def* multicofork



## [2021-11-23 05:35:13](https://github.com/leanprover-community/mathlib/commit/6dddef2)
feat(topology/metric_space): range of a cauchy seq is bounded ([#10423](https://github.com/leanprover-community/mathlib/pull/10423))
#### Estimated changes
modified src/order/filter/cofinite.lean
- \+ *lemma* has_basis_cofinite

modified src/topology/metric_space/basic.lean
- \+ *lemma* bounded_range_of_tendsto_cofinite_uniformity
- \+ *lemma* bounded_range_of_cauchy_map_cofinite
- \+ *lemma* bounded_range_of_tendsto_cofinite

modified src/topology/uniform_space/cauchy.lean
- \+/\- *lemma* filter.has_basis.cauchy_iff
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
created src/algebra/algebra/spectrum.lean
- \+ *lemma* is_unit.smul_iff
- \+ *lemma* is_unit.smul_sub_iff_sub_inv_smul
- \+ *lemma* mem_iff
- \+ *lemma* not_mem_iff
- \+ *lemma* mem_resolvent_of_left_right_inverse
- \+ *lemma* mem_resolvent_iff
- \+ *lemma* add_mem_iff
- \+ *lemma* smul_mem_smul_iff
- \+ *theorem* smul_eq_smul
- \+ *theorem* left_add_coset_eq
- \+ *theorem* unit_mem_mul_iff_mem_swap_mul
- \+ *theorem* preimage_units_mul_eq_swap_mul
- \+ *def* resolvent
- \+ *def* spectrum



## [2021-11-22 22:48:19](https://github.com/leanprover-community/mathlib/commit/e59e03f)
feat(measure_theory/integral/interval_integral): add an alternative definition ([#10380](https://github.com/leanprover-community/mathlib/pull/10380))
Prove that `∫ x in a..b, f x ∂μ = sgn a b • ∫ x in Ι a b, f x ∂μ`,
where `sgn a b = if a ≤ b then 1 else -1`.
#### Estimated changes
modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* interval_integral_eq_integral_interval_oc



## [2021-11-22 19:46:14](https://github.com/leanprover-community/mathlib/commit/2f5af98)
feat(data/nat/prime): prime divisors ([#10318](https://github.com/leanprover-community/mathlib/pull/10318))
Adding some basic lemmas about `factors` and `factors.to_finset`
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* to_finset_repeat_of_ne_zero

modified src/data/nat/gcd.lean
- \+ *lemma* eq_one_of_dvd_coprimes

modified src/data/nat/prime.lean
- \+ *lemma* dvd_of_mem_factors
- \+ *lemma* prime_pow_prime_divisor
- \+ *lemma* mem_factors_mul_of_pos
- \+ *lemma* factors_mul_of_pos
- \+ *lemma* coprime_factors_disjoint
- \+ *lemma* factors_mul_of_coprime

modified src/number_theory/divisors.lean
- \+ *lemma* prime_divisors_eq_to_filter_divisors_prime



## [2021-11-22 18:50:52](https://github.com/leanprover-community/mathlib/commit/317483a)
feat(analysis/calculus/parametric_integral): generalize, rename ([#10397](https://github.com/leanprover-community/mathlib/pull/10397))
* add `integral` to lemma names;
* a bit more general
  `has_fderiv_at_integral_of_dominated_loc_of_lip'`: only require an
  estimate on `∥F x a - F x₀ a∥` instead of `∥F x a - F y a∥`;
* generalize the `deriv` lemmas to `F : 𝕜 → α → E`, `[is_R_or_C 𝕜]`.
#### Estimated changes
modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at.le_of_lip'
- \+/\- *lemma* has_fderiv_at.le_of_lip
- \+/\- *lemma* has_fderiv_at.le_of_lip

modified src/analysis/calculus/parametric_integral.lean
- \+ *lemma* has_fderiv_at_integral_of_dominated_loc_of_lip'
- \+ *lemma* has_fderiv_at_integral_of_dominated_loc_of_lip
- \+ *lemma* has_fderiv_at_integral_of_dominated_of_fderiv_le
- \+ *lemma* has_deriv_at_integral_of_dominated_loc_of_lip
- \+ *lemma* has_deriv_at_integral_of_dominated_loc_of_deriv_le
- \- *lemma* has_fderiv_at_of_dominated_loc_of_lip'
- \- *lemma* has_fderiv_at_of_dominated_loc_of_lip
- \- *lemma* has_fderiv_at_of_dominated_of_fderiv_le
- \- *lemma* has_deriv_at_of_dominated_loc_of_lip
- \- *lemma* has_deriv_at_of_dominated_loc_of_deriv_le

modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* measure_theory.integrable.apply_continuous_linear_map
- \+/\- *lemma* continuous_linear_map.integrable_comp
- \+/\- *lemma* measure_theory.integrable.apply_continuous_linear_map
- \+/\- *lemma* continuous_linear_map.integrable_comp

modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* integral_apply
- \+/\- *lemma* integral_apply



## [2021-11-22 16:51:24](https://github.com/leanprover-community/mathlib/commit/d2ebcad)
fix(undergrad.yaml): reinstate deleted entry ([#10416](https://github.com/leanprover-community/mathlib/pull/10416))
Revert an (I assume accidental?) deletion in [#10415](https://github.com/leanprover-community/mathlib/pull/10415).
cc @PatrickMassot
#### Estimated changes
modified docs/undergrad.yaml



## [2021-11-22 13:14:41](https://github.com/leanprover-community/mathlib/commit/c896162)
feat(data/finset/basic) eq_of_mem_singleton ([#10414](https://github.com/leanprover-community/mathlib/pull/10414))
The `finset` equivalent of [set.eq_of_mem_singleton](https://leanprover-community.github.io/mathlib_docs/find/set.eq_of_mem_singleton/src)
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *theorem* eq_of_mem_singleton



## [2021-11-22 11:23:11](https://github.com/leanprover-community/mathlib/commit/d8d0c59)
chore(algebra/opposites): split group actions and division_ring into their own files ([#10383](https://github.com/leanprover-community/mathlib/pull/10383))
This splits out `group_theory.group_action.opposite` and `algebra.field.opposite` from `algebra.opposites`.
The motivation is to make opposite actions available slightly earlier in the import graph.
We probably want to split out `ring` at some point too, but that's likely a more annoying change so I've left it for future work.
These lemmas are just moved, and some `_root_` prefixes eliminated by removing the surrounding `namespace`.
#### Estimated changes
modified src/algebra/char_p/invertible.lean

modified src/algebra/continued_fractions/basic.lean

modified src/algebra/euclidean_domain.lean

renamed src/algebra/field.lean to src/algebra/field/basic.lean

created src/algebra/field/opposite.lean

modified src/algebra/module/opposites.lean

modified src/algebra/opposites.lean
- \- *lemma* op_smul_eq_mul

modified src/algebra/order/field.lean

modified src/algebra/periodic.lean

modified src/algebra/smul_with_zero.lean

modified src/algebra/star/basic.lean

modified src/data/equiv/ring.lean

modified src/data/equiv/transfer_instance.lean

created src/group_theory/group_action/opposite.lean
- \+ *lemma* op_smul_eq_mul

modified src/group_theory/group_action/prod.lean

modified src/group_theory/submonoid/operations.lean

modified src/number_theory/number_field.lean

modified src/number_theory/pythagorean_triples.lean



## [2021-11-22 11:23:10](https://github.com/leanprover-community/mathlib/commit/2aea996)
feat(data): define a `fun_like` class of bundled homs (function + proofs) ([#10286](https://github.com/leanprover-community/mathlib/pull/10286))
This PR introduces a class `fun_like` for types of bundled homomorphisms, like `set_like` is for bundled subobjects. This should be useful by itself, but an important use I see for it is the per-morphism class refactor, see [#9888](https://github.com/leanprover-community/mathlib/pull/9888).
Also, `coe_fn_coe_base` now has an appropriately low priority, so it doesn't take precedence over `fun_like.has_coe_to_fun`.
#### Estimated changes
created src/data/fun_like.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* map_op
- \+ *lemma* map_cool
- \+ *lemma* do_something
- \+ *theorem* ext
- \+ *theorem* coe_injective
- \+ *theorem* coe_fn_eq
- \+ *theorem* ext'
- \+ *theorem* ext'_iff
- \+ *theorem* ext
- \+ *theorem* ext_iff



## [2021-11-22 09:54:52](https://github.com/leanprover-community/mathlib/commit/7a5fac3)
feat(ring_theory/roots_of_unity): primitive root lemmas ([#10356](https://github.com/leanprover-community/mathlib/pull/10356))
From the flt-regular project.
#### Estimated changes
modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* of_subsingleton
- \+ *lemma* unique
- \+ *lemma* eq_order_of
- \+ *lemma* zero
- \+ *lemma* map_of_injective
- \+ *lemma* of_map_of_injective
- \+ *lemma* map_iff_of_injective



## [2021-11-22 08:59:57](https://github.com/leanprover-community/mathlib/commit/9f07579)
docs(undergrad): add urls in linear algebra ([#10415](https://github.com/leanprover-community/mathlib/pull/10415))
This uses the new possibility to put urls in `undergrad.yaml` hoping to help describing what is meant to be formalized. We should probably create wiki pages for some cases that are not so clear even with a url. There is one case where I could find only a French page and some cases where I couldn't find anything. Amazingly "endormorphism exponential" is such a case, but hopefully this example is already clear. Another kind of problematic item is the "example" item in the representation section. Presumably it should be removed and replaced with a couple of explicit examples such as "standard representation of a matrix group" or "permutation representation".
#### Estimated changes
modified docs/undergrad.yaml



## [2021-11-22 00:26:55](https://github.com/leanprover-community/mathlib/commit/9277d4b)
chore(data/finset/basic): finset.prod -> finset.product in module docstring ([#10413](https://github.com/leanprover-community/mathlib/pull/10413))
#### Estimated changes
modified src/data/finset/basic.lean



## [2021-11-21 22:33:27](https://github.com/leanprover-community/mathlib/commit/d17db71)
chore(*): golf proofs about `filter.Coprod` ([#10400](https://github.com/leanprover-community/mathlib/pull/10400))
Also add some supporting lemmas.
#### Estimated changes
modified src/data/fintype/basic.lean
- \+ *lemma* coe_pi_finset

modified src/data/pi.lean
- \+ *lemma* surjective_pi_map
- \+ *lemma* injective_pi_map
- \+ *lemma* bijective_pi_map

modified src/data/set/finite.lean

modified src/order/boolean_algebra.lean
- \+ *theorem* compl_surjective

modified src/order/filter/basic.lean
- \+ *lemma* compl_mem_Coprod_iff

modified src/order/filter/cofinite.lean

modified src/topology/subset_properties.lean



## [2021-11-21 22:33:26](https://github.com/leanprover-community/mathlib/commit/d98b8e0)
feat(linear_algebra/bilinear_map): semilinearize bilinear maps ([#10373](https://github.com/leanprover-community/mathlib/pull/10373))
This PR generalizes most of `linear_algebra/bilinear_map` to semilinear maps. Along the way, we introduce an instance for `module S (E →ₛₗ[σ] F)`, with `σ : R →+* S`. This allows us to define "semibilinear" maps of type `E →ₛₗ[σ] F →ₛₗ[ρ] G`, where `E`, `F` and `G` are modules over `R₁`, `R₂` and `R₃` respectively, and `σ : R₁ →+* R₃` and `ρ : R₂ →+* R₃`. See `mk₂'ₛₗ` to see how to construct such a map.
#### Estimated changes
modified src/algebra/module/linear_map.lean
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *theorem* smul_comp
- \+/\- *theorem* comp_smul
- \+/\- *theorem* smul_comp
- \+/\- *theorem* comp_smul

modified src/linear_algebra/bilinear_map.lean
- \+ *theorem* mk₂'ₛₗ_apply
- \+/\- *theorem* ext₂
- \+/\- *theorem* flip_apply
- \+/\- *theorem* flip_inj
- \+/\- *theorem* map_zero₂
- \+/\- *theorem* map_neg₂
- \+/\- *theorem* map_sub₂
- \+/\- *theorem* map_add₂
- \+/\- *theorem* map_smul₂
- \+ *theorem* map_smulₛₗ₂
- \+/\- *theorem* map_sum₂
- \+/\- *theorem* lcomp_apply
- \+ *theorem* lcompₛₗ_apply
- \+/\- *theorem* llcomp_apply
- \+/\- *theorem* compl₂_apply
- \+/\- *theorem* compr₂_apply
- \+/\- *theorem* ext₂
- \+/\- *theorem* flip_apply
- \+/\- *theorem* flip_inj
- \+/\- *theorem* map_zero₂
- \+/\- *theorem* map_neg₂
- \+/\- *theorem* map_sub₂
- \+/\- *theorem* map_add₂
- \+/\- *theorem* map_smul₂
- \+/\- *theorem* map_sum₂
- \+/\- *theorem* lcomp_apply
- \+/\- *theorem* llcomp_apply
- \+/\- *theorem* compl₂_apply
- \+/\- *theorem* compr₂_apply
- \+ *def* mk₂'ₛₗ
- \+/\- *def* mk₂'
- \+/\- *def* flip
- \+/\- *def* mk₂
- \+/\- *def* lflip
- \+/\- *def* lcomp
- \+ *def* lcompₛₗ
- \+/\- *def* llcomp
- \+/\- *def* compl₂
- \+/\- *def* compr₂
- \+/\- *def* mk₂'
- \+/\- *def* flip
- \+/\- *def* mk₂
- \+/\- *def* lflip
- \+/\- *def* lcomp
- \+/\- *def* llcomp
- \+/\- *def* compl₂
- \+/\- *def* compr₂



## [2021-11-21 21:47:34](https://github.com/leanprover-community/mathlib/commit/8f07d75)
feat(measure_theory/covering/differentiation): differentiation of measures ([#10101](https://github.com/leanprover-community/mathlib/pull/10101))
If `ρ` and `μ` are two Radon measures on a finite-dimensional normed real vector space, then for `μ`-almost every `x`, the ratio `ρ (B (x, r)) / μ (B(x,r))` converges when `r` tends to `0`, towards the Radon-Nikodym derivative of `ρ` with respect to `μ`. This is the main theorem on differentiation of measures.
The convergence in fact holds for more general families of sets than balls, called Vitali families (the fact that balls form a Vitali family is a restatement of the Besicovitch covering theorem). The general version of the differentation of measures theorem is proved in this PR, following [Federer, geometric measure theory].
#### Estimated changes
created src/measure_theory/covering/differentiation.lean
- \+ *lemma* ae_eventually_measure_zero_of_singular
- \+ *lemma* ae_tendsto_lim_ratio
- \+ *lemma* exists_measurable_supersets_lim_ratio
- \+ *lemma* lim_ratio_meas_measurable
- \+ *lemma* ae_tendsto_lim_ratio_meas
- \+ *lemma* measure_le_mul_of_subset_lim_ratio_meas_lt
- \+ *lemma* mul_measure_le_of_subset_lt_lim_ratio_meas
- \+ *lemma* measure_lim_ratio_meas_top
- \+ *lemma* measure_lim_ratio_meas_zero
- \+ *lemma* with_density_le_mul
- \+ *lemma* le_mul_with_density
- \+ *theorem* ae_eventually_measure_pos
- \+ *theorem* eventually_measure_lt_top
- \+ *theorem* measure_le_of_frequently_le
- \+ *theorem* null_of_frequently_le_of_frequently_ge
- \+ *theorem* ae_tendsto_div
- \+ *theorem* ae_measurable_lim_ratio
- \+ *theorem* with_density_lim_ratio_meas_eq
- \+ *theorem* ae_tendsto_rn_deriv_of_absolutely_continuous
- \+ *theorem* ae_tendsto_rn_deriv

modified src/measure_theory/covering/vitali_family.lean



## [2021-11-21 20:56:17](https://github.com/leanprover-community/mathlib/commit/8ee634b)
feat(measure_theory): define volume on `complex` ([#10403](https://github.com/leanprover-community/mathlib/pull/10403))
#### Estimated changes
created src/measure_theory/measure/complex_lebesgue.lean
- \+ *lemma* volume_preserving_equiv_pi
- \+ *lemma* volume_preserving_equiv_real_prod
- \+ *def* measurable_equiv_pi
- \+ *def* measurable_equiv_real_prod



## [2021-11-21 18:40:48](https://github.com/leanprover-community/mathlib/commit/2168297)
feat(analysis/inner_product_space/projection): orthogonal group is generated by reflections ([#10381](https://github.com/leanprover-community/mathlib/pull/10381))
#### Estimated changes
modified docs/undergrad.yaml

modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* mem_orthogonal_singleton_of_inner_right
- \+ *lemma* mem_orthogonal_singleton_of_inner_left

modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* reflection_trans_reflection
- \+ *lemma* reflection_sub
- \+/\- *lemma* submodule.finrank_add_finrank_orthogonal
- \+ *lemma* linear_isometry_equiv.reflections_generate_dim_aux
- \+ *lemma* linear_isometry_equiv.reflections_generate_dim
- \+ *lemma* linear_isometry_equiv.reflections_generate
- \+/\- *lemma* submodule.finrank_add_finrank_orthogonal



## [2021-11-21 16:46:44](https://github.com/leanprover-community/mathlib/commit/e0c0d84)
feat(topology/separation): removing a finite set from a dense set preserves density ([#10405](https://github.com/leanprover-community/mathlib/pull/10405))
Also add the fact that one can find a dense set containing neither top nor bottom in a nontrivial dense linear order.
#### Estimated changes
modified src/measure_theory/function/ae_measurable_order.lean

modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* dense.exists_countable_dense_subset_no_bot_top
- \+ *lemma* exists_countable_dense_no_bot_top

modified src/topology/bases.lean

modified src/topology/basic.lean

modified src/topology/instances/ennreal.lean
- \+ *lemma* exists_countable_dense_no_zero_top

modified src/topology/separation.lean
- \+/\- *lemma* finite.is_closed
- \+ *lemma* dense.diff_singleton
- \+ *lemma* dense.diff_finset
- \+ *lemma* dense.diff_finite
- \+/\- *lemma* finite.is_closed



## [2021-11-21 11:11:05](https://github.com/leanprover-community/mathlib/commit/55b81f8)
feat(measure_theory): measure preserving maps and integrals ([#10326](https://github.com/leanprover-community/mathlib/pull/10326))
If `f` is a measure preserving map, then `∫ y, g y ∂ν = ∫ x, g (f x) ∂μ`. It was two rewrites with the old API (`hf.map_eq`, then a lemma about integral over map measure); it's one `rw` now.
Also add versions for special cases when `f` is a measurable embedding (in this case we don't need to assume measurability of `g`).
#### Estimated changes
modified src/data/equiv/fin.lean
- \+ *lemma* fin.preimage_apply_01_prod
- \+ *lemma* fin.preimage_apply_01_prod'

modified src/dynamics/ergodic/measure_preserving.lean
- \+ *lemma* restrict_preimage
- \+ *lemma* restrict_preimage_emb
- \+ *lemma* restrict_image_emb

modified src/measure_theory/constructions/pi.lean
- \+ *lemma* measure_preserving_fun_unique
- \+ *lemma* volume_preserving_fun_unique
- \+ *lemma* measure_preserving_pi_fin_two
- \+ *lemma* volume_preserving_pi_fin_two
- \+ *lemma* measure_preserving_fin_two_arrow_vec
- \+ *lemma* measure_preserving_fin_two_arrow
- \+ *lemma* volume_preserving_fin_two_arrow
- \+ *lemma* measure_preserving_pi_empty
- \+ *lemma* volume_preserving_pi_empty
- \- *lemma* pi_unique_eq_map
- \- *lemma* map_fun_unique
- \- *lemma* {u}
- \- *lemma* {u}
- \- *lemma* prod_eq_map_fin_two_arrow
- \- *lemma* prod_eq_map_fin_two_arrow_same
- \- *lemma* integral_fun_unique_pi
- \- *lemma* integral_fun_unique_pi'
- \- *lemma* integral_fun_unique
- \- *lemma* integral_fun_unique'
- \- *lemma* set_integral_fun_unique_pi
- \- *lemma* set_integral_fun_unique_pi'
- \- *lemma* set_integral_fun_unique
- \- *lemma* set_integral_fun_unique'
- \- *lemma* integral_fin_two_arrow_pi
- \- *lemma* integral_fin_two_arrow_pi'
- \- *lemma* integral_fin_two_arrow
- \- *lemma* integral_fin_two_arrow'
- \- *lemma* set_integral_fin_two_arrow_pi
- \- *lemma* set_integral_fin_two_arrow_pi'
- \- *lemma* set_integral_fin_two_arrow
- \- *lemma* set_integral_fin_two_arrow'

modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_preserving.integrable_comp
- \+ *lemma* measure_preserving.integrable_comp_emb

modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_preserving.integral_comp

modified src/measure_theory/integral/integrable_on.lean
- \+ *lemma* measure_preserving.integrable_on_comp_preimage
- \+ *lemma* measure_preserving.integrable_on_image

modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_preserving.lintegral_comp
- \+ *lemma* measure_preserving.lintegral_comp_emb
- \+ *lemma* measure_preserving.set_lintegral_comp_preimage
- \+ *lemma* measure_preserving.set_lintegral_comp_preimage_emb
- \+ *lemma* measure_preserving.set_lintegral_comp_emb

modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_preserving.set_integral_preimage_emb
- \+ *lemma* measure_preserving.set_integral_image_emb

modified src/measure_theory/measure/measure_space.lean



## [2021-11-20 23:37:29](https://github.com/leanprover-community/mathlib/commit/2a28652)
feat(data/finset/basic): add filter_erase ([#10384](https://github.com/leanprover-community/mathlib/pull/10384))
Like `filter_insert`, but for `erase`
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* erase_idem
- \+ *lemma* erase_right_comm
- \+ *theorem* filter_erase



## [2021-11-20 21:22:54](https://github.com/leanprover-community/mathlib/commit/32c0507)
feat(data/nat/interval): add Ico_succ_left_eq_erase ([#10386](https://github.com/leanprover-community/mathlib/pull/10386))
Adds `Ico_succ_left_eq_erase`. Also adds a few order lemmas needed for this.
See [this discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Ico_succ_left_eq_erase_Ico/near/259180476)
#### Estimated changes
modified src/data/nat/interval.lean
- \+ *lemma* Ico_succ_left_eq_erase_Ico

modified src/order/basic.lean
- \+ *lemma* ne_of_not_le



## [2021-11-20 13:22:08](https://github.com/leanprover-community/mathlib/commit/b3538bf)
feat(topology/algebra/infinite_sum): add `has_sum.smul_const` etc ([#10393](https://github.com/leanprover-community/mathlib/pull/10393))
Rename old `*.smul` to `*.const_smul`.
#### Estimated changes
modified src/measure_theory/measure/vector_measure.lean

modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.const_smul
- \+ *lemma* summable.const_smul
- \+ *lemma* tsum_const_smul
- \+ *lemma* has_sum.smul_const
- \+ *lemma* summable.smul_const
- \+ *lemma* tsum_smul_const
- \- *lemma* has_sum.smul
- \- *lemma* summable.smul
- \- *lemma* tsum_smul



## [2021-11-20 11:30:32](https://github.com/leanprover-community/mathlib/commit/618447f)
feat(analysis/special_functions/complex/arg): review, golf, lemmas ([#10365](https://github.com/leanprover-community/mathlib/pull/10365))
* add `|z| * exp (arg z * I) = z`;
* reorder theorems to help golfing;
* prove formulas for `arg z` in terms of `arccos (re z / abs z)` in cases `0 < im z` and `im z < 0`;
* use them to golf continuity of `arg`.
#### Estimated changes
modified src/algebra/order/ring.lean
- \+/\- *theorem* mul_nonneg_iff_right_nonneg_of_pos
- \+ *theorem* mul_nonneg_iff_left_nonneg_of_pos
- \+/\- *theorem* mul_nonneg_iff_right_nonneg_of_pos

modified src/analysis/special_functions/complex/arg.lean
- \+/\- *lemma* sin_arg
- \+/\- *lemma* cos_arg
- \+ *lemma* abs_mul_exp_arg_mul_I
- \+ *lemma* abs_mul_cos_add_sin_mul_I
- \+ *lemma* arg_mul_cos_add_sin_mul_I
- \+/\- *lemma* arg_cos_add_sin_mul_I
- \+/\- *lemma* arg_zero
- \+/\- *lemma* ext_abs_arg
- \+ *lemma* ext_abs_arg_iff
- \+ *lemma* arg_mem_Ioc
- \+ *lemma* range_arg
- \+ *lemma* arg_nonneg_iff
- \+ *lemma* arg_neg_iff
- \+/\- *lemma* arg_real_mul
- \+/\- *lemma* arg_eq_arg_iff
- \+/\- *lemma* tan_arg
- \+ *lemma* arg_eq_pi_div_two_iff
- \+ *lemma* arg_eq_neg_pi_div_two_iff
- \+/\- *lemma* arg_of_re_nonneg
- \+ *lemma* arg_of_im_nonneg_of_ne_zero
- \+ *lemma* arg_of_im_pos
- \+ *lemma* arg_of_im_neg
- \+ *lemma* arg_eq_nhds_of_im_pos
- \+ *lemma* arg_eq_nhds_of_im_neg
- \+/\- *lemma* arg_zero
- \+/\- *lemma* sin_arg
- \+/\- *lemma* cos_arg
- \+/\- *lemma* tan_arg
- \+/\- *lemma* arg_cos_add_sin_mul_I
- \+/\- *lemma* arg_eq_arg_iff
- \+/\- *lemma* arg_real_mul
- \+/\- *lemma* ext_abs_arg
- \+/\- *lemma* arg_of_re_nonneg
- \- *lemma* arg_of_re_zero_of_im_pos
- \- *lemma* arg_of_re_zero_of_im_neg
- \- *lemma* continuous_at_arg_of_re_pos
- \- *lemma* continuous_at_arg_of_re_neg_of_im_pos
- \- *lemma* continuous_at_arg_of_re_neg_of_im_neg
- \- *lemma* continuous_at_arg_of_re_zero

modified src/analysis/special_functions/complex/circle.lean

modified src/analysis/special_functions/complex/log.lean
- \+/\- *lemma* log_exp
- \+/\- *lemma* log_exp

modified src/data/complex/basic.lean
- \+ *lemma* norm_sq_add_mul_I
- \+ *lemma* sq_abs
- \+ *lemma* sq_abs_sub_sq_re
- \+ *lemma* sq_abs_sub_sq_im

modified src/geometry/euclidean/triangle.lean



## [2021-11-20 02:42:14](https://github.com/leanprover-community/mathlib/commit/bd6c6d5)
chore(scripts): update nolints.txt ([#10391](https://github.com/leanprover-community/mathlib/pull/10391))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/style-exceptions.txt



## [2021-11-19 15:45:43](https://github.com/leanprover-community/mathlib/commit/db926f0)
chore(category_theory/limits/shapes/pullbacks): fix diagrams in docs ([#10379](https://github.com/leanprover-community/mathlib/pull/10379))
#### Estimated changes
modified src/category_theory/limits/shapes/pullbacks.lean



## [2021-11-19 14:34:11](https://github.com/leanprover-community/mathlib/commit/7638fe2)
doc(topology/separation): two typos ([#10382](https://github.com/leanprover-community/mathlib/pull/10382))
#### Estimated changes
modified src/topology/separation.lean



## [2021-11-19 12:03:57](https://github.com/leanprover-community/mathlib/commit/e8858fd)
refactor(algebra/opposites): use mul_opposite for multiplicative opposite ([#10302](https://github.com/leanprover-community/mathlib/pull/10302))
Split out `mul_opposite` from `opposite`, to leave room for an `add_opposite` in future.
Multiplicative opposites are now spelt `Aᵐᵒᵖ` instead of `Aᵒᵖ`. `Aᵒᵖ` now refers to the categorical opposite.
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+/\- *lemma* algebra_map_apply
- \+/\- *lemma* algebra_map_apply

modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* ring_hom.unop_map_list_prod
- \+/\- *lemma* unop_sum
- \+/\- *lemma* ring_hom.unop_map_list_prod
- \+/\- *lemma* unop_sum

modified src/algebra/free_algebra.lean
- \+/\- *def* star_hom
- \+/\- *def* star_hom

modified src/algebra/geom_sum.lean

modified src/algebra/group/prod.lean
- \+/\- *def* embed_product
- \+/\- *def* embed_product

modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* unop_pow
- \+/\- *lemma* unop_zpow
- \+/\- *lemma* unop_pow
- \+/\- *lemma* unop_zpow

modified src/algebra/hierarchy_design.lean

modified src/algebra/module/basic.lean

modified src/algebra/module/opposites.lean
- \+/\- *def* op_linear_equiv
- \+/\- *def* op_linear_equiv

modified src/algebra/monoid_algebra/basic.lean
- \+/\- *lemma* op_ring_equiv_symm_single
- \+/\- *lemma* op_ring_equiv_symm_single
- \+/\- *lemma* op_ring_equiv_symm_single
- \+/\- *lemma* op_ring_equiv_symm_single

modified src/algebra/opposites.lean
- \+ *lemma* unop_op
- \+ *lemma* op_unop
- \+ *lemma* op_comp_unop
- \+ *lemma* unop_comp_op
- \+ *lemma* op_bijective
- \+ *lemma* unop_bijective
- \+ *lemma* op_injective
- \+ *lemma* op_surjective
- \+ *lemma* unop_injective
- \+ *lemma* unop_surjective
- \+ *lemma* op_inj
- \+ *lemma* unop_inj
- \+/\- *lemma* unop_zero
- \+/\- *lemma* unop_one
- \+/\- *lemma* unop_add
- \+/\- *lemma* unop_neg
- \+/\- *lemma* unop_mul
- \+/\- *lemma* unop_inv
- \+/\- *lemma* unop_sub
- \+/\- *lemma* unop_smul
- \+/\- *lemma* unop_eq_zero_iff
- \+/\- *lemma* op_eq_zero_iff
- \+/\- *lemma* unop_ne_zero_iff
- \+/\- *lemma* op_ne_zero_iff
- \+/\- *lemma* unop_eq_one_iff
- \+/\- *lemma* semiconj_by.unop
- \+/\- *lemma* semiconj_by_unop
- \+/\- *lemma* commute.unop
- \+/\- *lemma* commute_unop
- \+/\- *lemma* units.coe_unop_op_equiv
- \+/\- *lemma* units.coe_op_equiv_symm
- \+/\- *lemma* unop_zero
- \+/\- *lemma* unop_one
- \+/\- *lemma* unop_add
- \+/\- *lemma* unop_neg
- \+/\- *lemma* unop_mul
- \+/\- *lemma* unop_inv
- \+/\- *lemma* unop_sub
- \+/\- *lemma* unop_smul
- \+/\- *lemma* unop_eq_zero_iff
- \+/\- *lemma* op_eq_zero_iff
- \+/\- *lemma* unop_ne_zero_iff
- \+/\- *lemma* op_ne_zero_iff
- \+/\- *lemma* unop_eq_one_iff
- \+/\- *lemma* semiconj_by.unop
- \+/\- *lemma* semiconj_by_unop
- \+/\- *lemma* commute.unop
- \+/\- *lemma* commute_unop
- \- *lemma* coe_op_add_equiv
- \- *lemma* coe_op_add_equiv_symm
- \+/\- *lemma* units.coe_unop_op_equiv
- \+/\- *lemma* units.coe_op_equiv_symm
- \+ *def* mul_opposite
- \+ *def* op
- \+ *def* unop
- \+ *def* op_equiv
- \+/\- *def* op_add_equiv
- \+/\- *def* mul_equiv.inv'
- \+/\- *def* units.op_equiv
- \+/\- *def* op_add_equiv
- \+/\- *def* mul_equiv.inv'
- \+/\- *def* units.op_equiv

modified src/algebra/periodic.lean

modified src/algebra/quandle.lean

modified src/algebra/quaternion.lean
- \+/\- *lemma* coe_conj_ae
- \+/\- *lemma* coe_conj_ae
- \+/\- *def* conj_ae
- \+/\- *def* conj_ae
- \+/\- *def* conj_ae
- \+/\- *def* conj_ae

modified src/algebra/regular/smul.lean
- \+/\- *lemma* is_right_regular
- \+/\- *lemma* is_right_regular

modified src/algebra/smul_with_zero.lean

modified src/algebra/star/basic.lean
- \+/\- *lemma* unop_star
- \+/\- *lemma* unop_star
- \+/\- *def* star_mul_equiv
- \+/\- *def* star_ring_equiv
- \+/\- *def* star_mul_equiv
- \+/\- *def* star_ring_equiv

modified src/algebra/star/module.lean

modified src/analysis/normed/group/SemiNormedGroup/completion.lean

modified src/analysis/normed_space/units.lean

modified src/category_theory/monoidal/opposite.lean
- \+/\- *lemma* op_injective
- \+/\- *lemma* unop_injective
- \+/\- *lemma* unop_inj_iff
- \+/\- *lemma* mop_unmop
- \+/\- *lemma* unmop_inj
- \+/\- *lemma* mop_unmop
- \+/\- *lemma* unmop_comp
- \+/\- *lemma* unmop_id
- \+/\- *lemma* mop_id_unmop
- \+/\- *lemma* mop_tensor_obj
- \+/\- *lemma* mop_tensor_unit
- \+/\- *lemma* op_injective
- \+/\- *lemma* unop_injective
- \+/\- *lemma* unop_inj_iff
- \+/\- *lemma* mop_unmop
- \+/\- *lemma* unmop_inj
- \+/\- *lemma* mop_unmop
- \+/\- *lemma* unmop_comp
- \+/\- *lemma* unmop_id
- \+/\- *lemma* mop_id_unmop
- \+/\- *lemma* mop_tensor_obj
- \+/\- *lemma* mop_tensor_unit
- \+/\- *def* mop
- \+/\- *def* unmop
- \+/\- *def* quiver.hom.mop
- \+/\- *def* quiver.hom.unmop
- \+/\- *def* mop
- \+/\- *def* unmop
- \+/\- *def* quiver.hom.mop
- \+/\- *def* quiver.hom.unmop

modified src/computability/turing_machine.lean

modified src/control/fold.lean
- \+/\- *def* foldl
- \+/\- *def* foldl

modified src/data/complex/is_R_or_C.lean

modified src/data/equiv/mul_add.lean

modified src/data/equiv/ring.lean
- \+/\- *lemma* to_add_equiv_eq_coe
- \+/\- *lemma* to_mul_equiv_eq_coe
- \+/\- *lemma* to_opposite_symm_apply
- \+/\- *lemma* unop_map_list_prod
- \+/\- *lemma* to_add_equiv_eq_coe
- \+/\- *lemma* to_mul_equiv_eq_coe
- \+/\- *lemma* to_opposite_symm_apply
- \+/\- *lemma* unop_map_list_prod
- \+/\- *def* to_opposite
- \+/\- *def* to_opposite

modified src/data/list/big_operators.lean
- \+ *lemma* _root_.mul_opposite.op_list_prod
- \+ *lemma* _root_.mul_opposite.unop_list_prod
- \+/\- *lemma* _root_.monoid_hom.unop_map_list_prod
- \- *lemma* _root_.opposite.op_list_prod
- \- *lemma* _root_.opposite.unop_list_prod
- \+/\- *lemma* _root_.monoid_hom.unop_map_list_prod

modified src/data/matrix/basic.lean
- \+/\- *def* transpose_ring_equiv
- \+/\- *def* transpose_ring_equiv

modified src/data/opposite.lean

modified src/data/polynomial/basic.lean
- \+/\- *def* op_ring_equiv
- \+/\- *def* op_ring_equiv

modified src/data/prod.lean
- \+ *lemma* snd_comp_mk
- \+ *lemma* fst_comp_mk

modified src/group_theory/free_product.lean
- \+/\- *lemma* inv_def
- \+/\- *lemma* inv_def

modified src/linear_algebra/clifford_algebra/conjugation.lean

modified src/linear_algebra/sesquilinear_form.lean

modified src/logic/unique.lean
- \+/\- *def* mk'
- \+/\- *def* mk'

modified src/measure_theory/group/arithmetic.lean
- \+/\- *lemma* measurable_op
- \+/\- *lemma* measurable_unop
- \+/\- *lemma* measurable_op
- \+/\- *lemma* measurable_unop

modified src/number_theory/arithmetic_function.lean

modified src/ring_theory/ring_invo.lean
- \+/\- *def* mk'
- \+/\- *def* mk'

modified src/topology/algebra/monoid.lean
- \+/\- *lemma* continuous_unop
- \+/\- *lemma* continuous_op
- \+/\- *lemma* continuous_unop
- \+/\- *lemma* continuous_op



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
modified archive/100-theorems-list/16_abel_ruffini.lean

modified src/algebra/algebra/basic.lean

modified src/algebra/algebra/bilinear.lean

modified src/algebra/big_operators/finsupp.lean

modified src/algebra/category/CommRing/adjunctions.lean

modified src/algebra/category/CommRing/basic.lean

modified src/algebra/category/Group/biproducts.lean

modified src/algebra/category/Module/basic.lean

modified src/algebra/category/Module/colimits.lean

modified src/algebra/category/Module/epi_mono.lean

modified src/algebra/category/Module/filtered_colimits.lean

modified src/algebra/category/Module/projective.lean

modified src/algebra/category/Mon/basic.lean

modified src/algebra/category/Mon/limits.lean

modified src/algebra/category/Semigroup/basic.lean

modified src/algebra/char_p/basic.lean

modified src/algebra/char_p/quotient.lean

modified src/algebra/continued_fractions/computation/approximation_corollaries.lean

modified src/algebra/continued_fractions/computation/basic.lean

modified src/algebra/continued_fractions/computation/correctness_terminating.lean

modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean

modified src/algebra/direct_sum/algebra.lean

modified src/algebra/direct_sum/internal.lean

modified src/algebra/direct_sum/ring.lean

modified src/algebra/divisibility.lean

modified src/algebra/field.lean

modified src/algebra/free_algebra.lean

modified src/algebra/gcd_monoid/basic.lean

modified src/algebra/graded_monoid.lean

modified src/algebra/group_action_hom.lean

modified src/algebra/group_with_zero/power.lean

modified src/algebra/homology/augment.lean

modified src/algebra/homology/complex_shape.lean

modified src/algebra/lie/base_change.lean

modified src/algebra/lie/basic.lean

modified src/algebra/lie/cartan_matrix.lean

modified src/algebra/lie/classical.lean

modified src/algebra/lie/direct_sum.lean

modified src/algebra/linear_recurrence.lean

modified src/algebra/module/ulift.lean

modified src/algebra/monoid_algebra/grading.lean

modified src/algebra/order/algebra.lean

modified src/algebra/order/archimedean.lean

modified src/algebra/order/smul.lean

modified src/algebra/order/with_zero.lean

modified src/algebra/pempty_instances.lean

modified src/algebra/periodic.lean

modified src/algebra/pointwise.lean

modified src/algebra/polynomial/big_operators.lean

modified src/algebra/star/chsh.lean

modified src/algebraic_geometry/EllipticCurve.lean

modified src/algebraic_geometry/locally_ringed_space.lean

modified src/algebraic_geometry/presheafed_space/has_colimits.lean

modified src/algebraic_geometry/ringed_space.lean

modified src/algebraic_topology/Moore_complex.lean

modified src/algebraic_topology/simplex_category.lean

modified src/algebraic_topology/simplicial_object.lean

modified src/algebraic_topology/simplicial_set.lean

modified src/algebraic_topology/topological_simplex.lean

modified src/analysis/ODE/picard_lindelof.lean

modified src/analysis/asymptotics/superpolynomial_decay.lean

modified src/analysis/box_integral/box/basic.lean

modified src/analysis/box_integral/partition/filter.lean

modified src/analysis/calculus/darboux.lean

modified src/analysis/calculus/inverse.lean

modified src/analysis/complex/roots_of_unity.lean

modified src/analysis/convex/extrema.lean

modified src/analysis/normed_space/affine_isometry.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/conformal_linear_map.lean

modified src/analysis/normed_space/exponential.lean

modified src/analysis/normed_space/indicator_function.lean

modified src/analysis/normed_space/is_R_or_C.lean

modified src/analysis/normed_space/lattice_ordered_group.lean

modified src/analysis/normed_space/linear_isometry.lean

modified src/analysis/normed_space/star.lean

modified src/analysis/seminorm.lean

modified src/analysis/special_functions/trigonometric/arctan.lean

modified src/analysis/special_functions/trigonometric/chebyshev.lean

modified src/analysis/special_functions/trigonometric/deriv.lean

modified src/category_theory/Fintype.lean

modified src/category_theory/abelian/projective.lean

modified src/category_theory/adjunction/comma.lean

modified src/category_theory/adjunction/lifting.lean

modified src/category_theory/adjunction/mates.lean

modified src/category_theory/adjunction/over.lean

modified src/category_theory/adjunction/reflective.lean

modified src/category_theory/category/Cat.lean

modified src/category_theory/category/Quiv.lean

modified src/category_theory/category/pairwise.lean

modified src/category_theory/closed/cartesian.lean

modified src/category_theory/comma.lean

modified src/category_theory/concrete_category/bundled.lean

modified src/category_theory/conj.lean

modified src/category_theory/differential_object.lean

modified src/category_theory/functor.lean

modified src/category_theory/graded_object.lean

modified src/category_theory/hom_functor.lean

modified src/category_theory/isomorphism_classes.lean

modified src/category_theory/lifting_properties.lean

modified src/category_theory/limits/comma.lean

modified src/category_theory/limits/connected.lean

modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean

modified src/category_theory/limits/constructions/over/connected.lean

modified src/category_theory/limits/constructions/over/default.lean

modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean

modified src/category_theory/limits/functor_category.lean

modified src/category_theory/limits/kan_extension.lean

modified src/category_theory/limits/lattice.lean

modified src/category_theory/limits/opposites.lean

modified src/category_theory/limits/preserves/filtered.lean

modified src/category_theory/limits/preserves/functor_category.lean

modified src/category_theory/limits/preserves/shapes/terminal.lean

modified src/category_theory/limits/presheaf.lean

modified src/category_theory/limits/shapes/disjoint_coproduct.lean

modified src/category_theory/limits/shapes/finite_limits.lean

modified src/category_theory/limits/shapes/finite_products.lean

modified src/category_theory/limits/shapes/normal_mono.lean

modified src/category_theory/limits/shapes/reflexive.lean

modified src/category_theory/limits/shapes/regular_mono.lean

modified src/category_theory/monad/adjunction.lean

modified src/category_theory/monad/coequalizer.lean

modified src/category_theory/monad/kleisli.lean

modified src/category_theory/monad/monadicity.lean

modified src/category_theory/monad/products.lean

modified src/category_theory/monoidal/free/basic.lean

modified src/category_theory/monoidal/free/coherence.lean

modified src/category_theory/monoidal/types.lean

modified src/category_theory/opposites.lean

modified src/category_theory/pi/basic.lean

modified src/category_theory/preadditive/Mat.lean

modified src/category_theory/sigma/basic.lean

modified src/category_theory/sites/sheaf.lean

modified src/category_theory/sites/sieves.lean

modified src/category_theory/subterminal.lean

modified src/category_theory/triangulated/basic.lean

modified src/category_theory/triangulated/pretriangulated.lean

modified src/category_theory/triangulated/rotate.lean

modified src/category_theory/whiskering.lean

modified src/combinatorics/colex.lean

modified src/combinatorics/hales_jewett.lean

modified src/combinatorics/hall/finite.lean

modified src/computability/language.lean

modified src/computability/regular_expressions.lean

modified src/control/bifunctor.lean

modified src/control/equiv_functor.lean

modified src/control/fix.lean

modified src/control/monad/cont.lean

modified src/control/monad/writer.lean

modified src/control/traversable/derive.lean

modified src/control/traversable/instances.lean

modified src/data/buffer/parser/numeral.lean

modified src/data/complex/module.lean

modified src/data/equiv/basic.lean

modified src/data/equiv/denumerable.lean

modified src/data/equiv/embedding.lean

modified src/data/equiv/mul_add.lean

modified src/data/equiv/transfer_instance.lean

modified src/data/fin/basic.lean

modified src/data/finset/basic.lean

modified src/data/fp/basic.lean

modified src/data/int/absolute_value.lean

modified src/data/int/interval.lean

modified src/data/list/basic.lean

modified src/data/list/cycle.lean

modified src/data/list/duplicate.lean

modified src/data/list/prod_monoid.lean

modified src/data/list/sigma.lean

modified src/data/list/sort.lean

modified src/data/matrix/basic.lean

modified src/data/matrix/basis.lean

modified src/data/matrix/hadamard.lean

modified src/data/mv_polynomial/basic.lean

modified src/data/nat/choose/central.lean

modified src/data/nat/choose/vandermonde.lean

modified src/data/nat/enat.lean

modified src/data/nat/fib.lean

modified src/data/nat/gcd.lean

modified src/data/nat/multiplicity.lean

modified src/data/nat/prime.lean

modified src/data/option/basic.lean

modified src/data/pequiv.lean

modified src/data/pfunctor/multivariate/M.lean

modified src/data/pfunctor/multivariate/basic.lean

modified src/data/pnat/basic.lean

modified src/data/pnat/factors.lean

modified src/data/polynomial/derivative.lean

modified src/data/polynomial/div.lean

modified src/data/polynomial/erase_lead.lean

modified src/data/polynomial/lifts.lean

modified src/data/polynomial/reverse.lean

modified src/data/qpf/univariate/basic.lean

modified src/data/rat/denumerable.lean

modified src/data/real/basic.lean

modified src/data/real/ennreal.lean

modified src/data/real/irrational.lean

modified src/data/real/pi/leibniz.lean

modified src/data/seq/computation.lean

modified src/data/seq/seq.lean

modified src/data/seq/wseq.lean

modified src/data/set/basic.lean

modified src/data/set/pairwise.lean

modified src/data/setoid/basic.lean

modified src/data/subtype.lean

modified src/data/sym/basic.lean

modified src/data/sym/card.lean

modified src/dynamics/periodic_pts.lean

modified src/field_theory/chevalley_warning.lean

modified src/field_theory/finite/polynomial.lean

modified src/field_theory/fixed.lean

modified src/field_theory/polynomial_galois_group.lean

modified src/field_theory/primitive_element.lean

modified src/field_theory/separable.lean

modified src/field_theory/separable_degree.lean

modified src/field_theory/splitting_field.lean

modified src/geometry/manifold/bump_function.lean

modified src/geometry/manifold/instances/real.lean

modified src/geometry/manifold/instances/sphere.lean

modified src/geometry/manifold/local_invariant_properties.lean

modified src/geometry/manifold/partition_of_unity.lean

modified src/geometry/manifold/whitney_embedding.lean

modified src/group_theory/complement.lean

modified src/group_theory/congruence.lean

modified src/group_theory/eckmann_hilton.lean

modified src/group_theory/monoid_localization.lean

modified src/group_theory/order_of_element.lean

modified src/group_theory/p_group.lean

modified src/group_theory/perm/basic.lean

modified src/group_theory/perm/cycles.lean

modified src/group_theory/perm/sign.lean

modified src/group_theory/perm/support.lean

modified src/group_theory/quotient_group.lean

modified src/group_theory/schur_zassenhaus.lean

modified src/group_theory/subgroup/basic.lean

modified src/linear_algebra/adic_completion.lean

modified src/linear_algebra/affine_space/affine_map.lean

modified src/linear_algebra/affine_space/affine_subspace.lean

modified src/linear_algebra/coevaluation.lean

modified src/linear_algebra/determinant.lean

modified src/linear_algebra/finsupp_vector_space.lean

modified src/linear_algebra/free_module/pid.lean

modified src/linear_algebra/general_linear_group.lean

modified src/linear_algebra/lagrange.lean

modified src/linear_algebra/matrix/adjugate.lean

modified src/linear_algebra/matrix/block.lean

modified src/linear_algebra/matrix/charpoly/basic.lean

modified src/linear_algebra/matrix/charpoly/coeff.lean

modified src/linear_algebra/matrix/nonsingular_inverse.lean

modified src/linear_algebra/matrix/polynomial.lean

modified src/linear_algebra/matrix/transvection.lean

modified src/linear_algebra/quadratic_form/basic.lean

modified src/linear_algebra/quotient.lean

modified src/linear_algebra/sesquilinear_form.lean

modified src/linear_algebra/special_linear_group.lean

modified src/linear_algebra/tensor_product_basis.lean

modified src/linear_algebra/unitary_group.lean

modified src/logic/is_empty.lean

modified src/logic/nontrivial.lean

modified src/logic/relation.lean

modified src/measure_theory/category/Meas.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/decomposition/jordan.lean

modified src/measure_theory/decomposition/lebesgue.lean

modified src/measure_theory/function/ae_measurable_sequence.lean

modified src/measure_theory/integral/divergence_theorem.lean

modified src/measure_theory/integral/interval_integral.lean

modified src/measure_theory/measurable_space.lean

modified src/measure_theory/measurable_space_def.lean

modified src/measure_theory/measure/complex.lean

modified src/measure_theory/measure/lebesgue.lean

modified src/measure_theory/measure/vector_measure.lean

modified src/measure_theory/tactic.lean

modified src/meta/expr.lean

modified src/meta/expr_lens.lean

modified src/number_theory/bernoulli.lean

modified src/number_theory/bernoulli_polynomials.lean

modified src/number_theory/class_number/admissible_abs.lean

modified src/number_theory/class_number/admissible_absolute_value.lean

modified src/number_theory/class_number/admissible_card_pow_degree.lean

modified src/number_theory/class_number/finite.lean

modified src/number_theory/lucas_lehmer.lean

modified src/number_theory/lucas_primality.lean

modified src/number_theory/padics/padic_integers.lean

modified src/number_theory/padics/ring_homs.lean

modified src/order/category/NonemptyFinLinOrd.lean

modified src/order/category/Preorder.lean

modified src/order/closure.lean

modified src/order/compactly_generated.lean

modified src/order/countable_dense_linear_order.lean

modified src/order/filter/basic.lean

modified src/order/filter/ultrafilter.lean

modified src/order/liminf_limsup.lean

modified src/order/omega_complete_partial_order.lean

modified src/order/pilex.lean

modified src/order/preorder_hom.lean

modified src/order/rel_classes.lean

modified src/order/succ_pred.lean

modified src/probability_theory/notation.lean

modified src/ring_theory/adjoin/fg.lean

modified src/ring_theory/adjoin/polynomial.lean

modified src/ring_theory/algebra_tower.lean

modified src/ring_theory/derivation.lean

modified src/ring_theory/fintype.lean

modified src/ring_theory/flat.lean

modified src/ring_theory/free_ring.lean

modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/jacobson.lean

modified src/ring_theory/nakayama.lean

modified src/ring_theory/noetherian.lean

modified src/ring_theory/norm.lean

modified src/ring_theory/perfection.lean

modified src/ring_theory/polynomial/basic.lean

modified src/ring_theory/polynomial/bernstein.lean

modified src/ring_theory/polynomial/homogeneous.lean

modified src/ring_theory/polynomial/scale_roots.lean

modified src/ring_theory/polynomial/vieta.lean

modified src/ring_theory/polynomial_algebra.lean

modified src/ring_theory/power_series/basic.lean

modified src/ring_theory/roots_of_unity.lean

modified src/ring_theory/unique_factorization_domain.lean

modified src/ring_theory/valuation/basic.lean

modified src/ring_theory/witt_vector/structure_polynomial.lean

modified src/set_theory/cardinal.lean

modified src/set_theory/surreal/basic.lean

modified src/set_theory/surreal/dyadic.lean

modified src/system/random/basic.lean

modified src/tactic/choose.lean

modified src/tactic/clear.lean

modified src/tactic/converter/binders.lean

modified src/tactic/core.lean

modified src/tactic/dependencies.lean

modified src/tactic/elementwise.lean

modified src/tactic/equiv_rw.lean

modified src/tactic/explode.lean

modified src/tactic/ext.lean

modified src/tactic/find_unused.lean

modified src/tactic/interval_cases.lean

modified src/tactic/linarith/datatypes.lean

modified src/tactic/lint/frontend.lean

modified src/tactic/lint/misc.lean

modified src/tactic/lint/type_classes.lean

modified src/tactic/localized.lean

modified src/tactic/monotonicity/interactive.lean

modified src/tactic/monotonicity/lemmas.lean

modified src/tactic/nth_rewrite/congr.lean

modified src/tactic/restate_axiom.lean

modified src/tactic/rewrite_all/basic.lean

modified src/tactic/rewrite_search/search.lean

modified src/tactic/ring.lean

modified src/tactic/scc.lean

modified src/tactic/simps.lean

modified src/tactic/slim_check.lean

modified src/tactic/subtype_instance.lean

modified src/tactic/suggest.lean

modified src/tactic/zify.lean

modified src/testing/slim_check/functions.lean

modified src/topology/G_delta.lean

modified src/topology/algebra/affine.lean

modified src/topology/algebra/group_with_zero.lean

modified src/topology/algebra/mul_action.lean

modified src/topology/algebra/nonarchimedean/bases.lean

modified src/topology/algebra/open_subgroup.lean

modified src/topology/algebra/polynomial.lean

modified src/topology/category/Top/basic.lean

modified src/topology/category/Top/open_nhds.lean

modified src/topology/category/Top/opens.lean

modified src/topology/category/UniformSpace.lean

modified src/topology/continuous_function/locally_constant.lean

modified src/topology/homotopy/fundamental_groupoid.lean

modified src/topology/instances/ennreal.lean

modified src/topology/instances/irrational.lean

modified src/topology/list.lean

modified src/topology/locally_constant/algebra.lean

modified src/topology/metric_space/algebra.lean

modified src/topology/semicontinuous.lean

modified src/topology/sheaves/forget.lean

modified src/topology/sheaves/local_predicate.lean

modified src/topology/sheaves/presheaf.lean

modified src/topology/sheaves/sheaf.lean

modified src/topology/sheaves/sheaf_condition/equalizer_products.lean

modified src/topology/sheaves/sheaf_condition/unique_gluing.lean

modified src/topology/sheaves/sheaf_of_functions.lean

modified src/topology/uniform_space/basic.lean

modified src/topology/uniform_space/cauchy.lean

modified src/topology/uniform_space/separation.lean

modified test/equiv_rw.lean

modified test/monotonicity/test_cases.lean

modified test/simps.lean

modified test/slim_check.lean



## [2021-11-19 08:56:27](https://github.com/leanprover-community/mathlib/commit/5000fb0)
feat(data/polynomial/eval): is_root_(prod/map) ([#10360](https://github.com/leanprover-community/mathlib/pull/10360))
#### Estimated changes
modified src/data/polynomial/eval.lean
- \+ *lemma* is_root.eq_zero
- \+ *lemma* is_root_prod
- \+ *lemma* is_root.map
- \+ *lemma* is_root.of_map
- \+ *lemma* is_root_map_iff



## [2021-11-19 08:01:42](https://github.com/leanprover-community/mathlib/commit/784fe06)
feat(analysis/calculus/deriv): generalize lemmas about deriv and `smul` ([#10378](https://github.com/leanprover-community/mathlib/pull/10378))
Allow scalar multiplication by numbers from a different field.
#### Estimated changes
modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* deriv_const_smul
- \+/\- *lemma* deriv_const_smul
- \+ *theorem* has_strict_deriv_at.const_smul
- \+ *theorem* has_deriv_at_filter.const_smul
- \+/\- *theorem* has_deriv_at.const_smul
- \+ *theorem* has_deriv_at_mul_const
- \+/\- *theorem* has_deriv_at.const_smul

modified src/analysis/calculus/fderiv_symmetric.lean



## [2021-11-18 21:48:21](https://github.com/leanprover-community/mathlib/commit/f3f4442)
feat(logic/basic): define exists_unique_eq as a simp lemma ([#10364](https://github.com/leanprover-community/mathlib/pull/10364))
#### Estimated changes
modified src/logic/basic.lean
- \+ *theorem* exists_unique_eq
- \+ *theorem* exists_unique_eq'



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
modified src/field_theory/splitting_field.lean
- \+ *def* cases_twice

modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* algebra_map_eq'
- \+/\- *lemma* algebra_map_eq'



## [2021-11-18 17:07:15](https://github.com/leanprover-community/mathlib/commit/9654071)
feat(topology/algebra/module): add `is_scalar_tower` and `smul_comm_class` instances for `continuous_linear_map` ([#10375](https://github.com/leanprover-community/mathlib/pull/10375))
Also generalize some instances about `smul`.
#### Estimated changes
modified src/topology/algebra/module.lean



## [2021-11-18 15:50:36](https://github.com/leanprover-community/mathlib/commit/0d09e99)
feat(measure_theory/integral/{set_to_l1,bochner}): generalize results about integrals to `set_to_fun` ([#10369](https://github.com/leanprover-community/mathlib/pull/10369))
The Bochner integral is a particular case of the `set_to_fun` construction. We generalize some lemmas which were proved for integrals to `set_to_fun`, notably the Lebesgue dominated convergence theorem.
#### Estimated changes
modified src/measure_theory/integral/bochner.lean

modified src/measure_theory/integral/set_to_l1.lean
- \+ *lemma* norm_set_to_L1s_clm_le
- \+ *lemma* norm_set_to_L1s_clm_le'
- \+/\- *lemma* set_to_L1_eq_set_to_L1s_clm
- \+ *lemma* norm_set_to_L1_le_norm_set_to_L1s_clm
- \+ *lemma* norm_set_to_L1_le_mul_norm
- \+ *lemma* norm_set_to_L1_le_mul_norm'
- \+ *lemma* norm_set_to_L1_le
- \+ *lemma* norm_set_to_L1_le'
- \+ *lemma* set_to_L1_lipschitz
- \+ *lemma* tendsto_set_to_L1
- \+ *lemma* set_to_fun_to_L1
- \+ *lemma* continuous_set_to_fun
- \+ *lemma* norm_set_to_fun_le_mul_norm
- \+ *lemma* norm_set_to_fun_le_mul_norm'
- \+ *lemma* norm_set_to_fun_le
- \+ *lemma* norm_set_to_fun_le'
- \+ *lemma* tendsto_set_to_fun_filter_of_dominated_convergence
- \+ *lemma* continuous_at_set_to_fun_of_dominated
- \+ *lemma* continuous_set_to_fun_of_dominated
- \+/\- *lemma* set_to_L1_eq_set_to_L1s_clm
- \+ *theorem* tendsto_set_to_fun_of_dominated_convergence



## [2021-11-18 14:41:58](https://github.com/leanprover-community/mathlib/commit/0ededd5)
chore(analysis/calculus): use `is_R_or_C` in several lemmas ([#10376](https://github.com/leanprover-community/mathlib/pull/10376))
#### Estimated changes
modified src/analysis/calculus/mean_value.lean
- \+ *lemma* exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt
- \+ *lemma* exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at
- \- *lemma* convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt
- \- *lemma* convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at
- \+ *theorem* norm_image_sub_le_of_norm_has_fderiv_within_le
- \+ *theorem* lipschitz_on_with_of_nnnorm_has_fderiv_within_le
- \+ *theorem* norm_image_sub_le_of_norm_fderiv_within_le
- \+ *theorem* lipschitz_on_with_of_nnnorm_fderiv_within_le
- \+ *theorem* norm_image_sub_le_of_norm_fderiv_le
- \+ *theorem* lipschitz_on_with_of_nnnorm_fderiv_le
- \+ *theorem* norm_image_sub_le_of_norm_has_fderiv_within_le'
- \+ *theorem* norm_image_sub_le_of_norm_fderiv_within_le'
- \+ *theorem* norm_image_sub_le_of_norm_fderiv_le'
- \+ *theorem* is_const_of_fderiv_within_eq_zero
- \+ *theorem* _root_.is_const_of_fderiv_eq_zero
- \+ *theorem* norm_image_sub_le_of_norm_has_deriv_within_le
- \+ *theorem* lipschitz_on_with_of_nnnorm_has_deriv_within_le
- \+ *theorem* norm_image_sub_le_of_norm_deriv_within_le
- \+ *theorem* lipschitz_on_with_of_nnnorm_deriv_within_le
- \+ *theorem* norm_image_sub_le_of_norm_deriv_le
- \+ *theorem* lipschitz_on_with_of_nnnorm_deriv_le
- \- *theorem* convex.norm_image_sub_le_of_norm_has_fderiv_within_le
- \- *theorem* convex.lipschitz_on_with_of_nnnorm_has_fderiv_within_le
- \- *theorem* convex.norm_image_sub_le_of_norm_fderiv_within_le
- \- *theorem* convex.lipschitz_on_with_of_nnnorm_fderiv_within_le
- \- *theorem* convex.norm_image_sub_le_of_norm_fderiv_le
- \- *theorem* convex.lipschitz_on_with_of_nnnorm_fderiv_le
- \- *theorem* convex.norm_image_sub_le_of_norm_has_fderiv_within_le'
- \- *theorem* convex.norm_image_sub_le_of_norm_fderiv_within_le'
- \- *theorem* convex.norm_image_sub_le_of_norm_fderiv_le'
- \- *theorem* convex.is_const_of_fderiv_within_eq_zero
- \- *theorem* is_const_of_fderiv_eq_zero
- \- *theorem* convex.norm_image_sub_le_of_norm_has_deriv_within_le
- \- *theorem* convex.lipschitz_on_with_of_nnnorm_has_deriv_within_le
- \- *theorem* convex.norm_image_sub_le_of_norm_deriv_within_le
- \- *theorem* convex.lipschitz_on_with_of_nnnorm_deriv_within_le
- \- *theorem* convex.norm_image_sub_le_of_norm_deriv_le
- \- *theorem* convex.lipschitz_on_with_of_nnnorm_deriv_le



## [2021-11-18 12:48:11](https://github.com/leanprover-community/mathlib/commit/198ed6b)
doc(order/monotone): fix 2 typos ([#10377](https://github.com/leanprover-community/mathlib/pull/10377))
#### Estimated changes
modified src/order/monotone.lean



## [2021-11-18 02:36:10](https://github.com/leanprover-community/mathlib/commit/2f3b185)
chore(scripts): update nolints.txt ([#10374](https://github.com/leanprover-community/mathlib/pull/10374))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/style-exceptions.txt



## [2021-11-17 19:11:23](https://github.com/leanprover-community/mathlib/commit/f8cbb3e)
chore(.docker): don't install unnecessary toolchains ([#10363](https://github.com/leanprover-community/mathlib/pull/10363))
#### Estimated changes
modified .docker/debian/lean/Dockerfile

modified .docker/gitpod/mathlib/Dockerfile



## [2021-11-17 19:11:22](https://github.com/leanprover-community/mathlib/commit/5d1363e)
feat(data/nat/parity): add lemmas ([#10352](https://github.com/leanprover-community/mathlib/pull/10352))
From FLT-regular.
#### Estimated changes
modified src/data/nat/parity.lean
- \+ *lemma* even_mul_self_pred
- \+ *lemma* even_sub_one_of_prime_ne_two



## [2021-11-17 18:15:31](https://github.com/leanprover-community/mathlib/commit/276ab17)
feat(linear_algebra/bilinear_form): add lemmas ([#10353](https://github.com/leanprover-community/mathlib/pull/10353))
From FLT-regular.
#### Estimated changes
modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* _root_.matrix.nondegenerate_to_bilin'_iff_nondegenerate_to_bilin
- \+ *lemma* _root_.matrix.nondegenerate_to_bilin'_iff
- \+ *lemma* _root_.matrix.nondegenerate_to_bilin_iff
- \+ *lemma* nondegenerate_to_bilin'_iff_det_ne_zero
- \+ *lemma* nondegenerate_iff_det_ne_zero
- \+ *theorem* nondegenerate_to_matrix'_iff
- \+ *theorem* nondegenerate.to_matrix'
- \+ *theorem* nondegenerate_to_matrix_iff
- \+ *theorem* nondegenerate.to_matrix
- \+ *theorem* nondegenerate_to_bilin'_of_det_ne_zero'
- \- *theorem* nondegenerate_of_det_ne_zero'



## [2021-11-17 15:37:37](https://github.com/leanprover-community/mathlib/commit/6f793bb)
chore(measure_theory/group/basic): drop measurability assumption ([#10367](https://github.com/leanprover-community/mathlib/pull/10367))
#### Estimated changes
modified src/measure_theory/group/basic.lean
- \+/\- *lemma* inv_apply
- \+/\- *lemma* inv_apply



## [2021-11-17 14:46:00](https://github.com/leanprover-community/mathlib/commit/e14e87a)
chore(category_theory/filtered): slightly golf two proofs ([#10368](https://github.com/leanprover-community/mathlib/pull/10368))
#### Estimated changes
modified src/category_theory/filtered.lean



## [2021-11-17 09:02:09](https://github.com/leanprover-community/mathlib/commit/c7441af)
feat(linear_algebra/bilinear_form): add lemmas about congr ([#10362](https://github.com/leanprover-community/mathlib/pull/10362))
With these some of the `nondegenerate` proofs can be golfed to oblivion, rather than reproving variants of the same statement over and over again.
#### Estimated changes
modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* congr_refl
- \+ *lemma* congr_trans
- \+ *lemma* congr_congr
- \+/\- *lemma* congr_comp
- \+/\- *lemma* comp_congr
- \+ *lemma* nondegenerate.congr
- \+ *lemma* nondegenerate_congr_iff
- \+/\- *lemma* congr_comp
- \+/\- *lemma* comp_congr
- \+ *theorem* _root_.matrix.nondegenerate.to_bilin



## [2021-11-17 09:02:08](https://github.com/leanprover-community/mathlib/commit/568435c)
chore(analysis/inner_product_space/projection): typeclass inference for completeness ([#10357](https://github.com/leanprover-community/mathlib/pull/10357))
As of [#5408](https://github.com/leanprover-community/mathlib/pull/5408), most lemmas about orthogonal projection onto a subspace `K` / reflection through a subspace `K` / orthogonal complement of `K` which require `K` to be complete phrase this in terms of `complete_space K` rather than `is_complete K`, so that it can be found by typeclass inference.  A few still used the old way; this PR completes the switch.
#### Estimated changes
modified src/analysis/inner_product_space/dual.lean

modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* sub_orthogonal_projection_mem_orthogonal
- \+ *lemma* submodule.sup_orthogonal_inf_of_complete_space
- \+/\- *lemma* submodule.sup_orthogonal_of_complete_space
- \+ *lemma* submodule.is_compl_orthogonal_of_complete_space
- \+/\- *lemma* submodule.orthogonal_eq_bot_iff
- \- *lemma* submodule.sup_orthogonal_inf_of_is_complete
- \- *lemma* submodule.sup_orthogonal_of_is_complete
- \+/\- *lemma* submodule.sup_orthogonal_of_complete_space
- \- *lemma* submodule.is_compl_orthogonal_of_is_complete
- \+/\- *lemma* submodule.orthogonal_eq_bot_iff

modified src/geometry/euclidean/basic.lean



## [2021-11-17 09:02:07](https://github.com/leanprover-community/mathlib/commit/d5c2b34)
chore(analysis/mean_inequalities): split mean_inequalities into two files ([#10355](https://github.com/leanprover-community/mathlib/pull/10355))
This PR puts all results related to power functions into a new file.
Currently, we prove convexity of `exp` and `pow`, then use those properties in `mean_inequalities`. I am refactoring some parts of the analysis library to reduce the use of derivatives. I want to prove convexity of exp without derivatives (in a future PR), prove Holder's inequality, then use it to prove the convexity of pow. This requires Holder's inequality to be in a file that does not use convexity of pow, hence the split.
I needed to change the proof of Holder's inequality since it used the generalized mean inequality (hence `pow`). I switched to the second possible proof mentioned in the file docstring.
I also moved some lemmas in `mean_inequalities` to have three main sections: AM-GM, then Young and a final section with Holder and Minkowski.
#### Estimated changes
modified src/analysis/mean_inequalities.lean
- \- *lemma* add_rpow_le_rpow_add
- \- *lemma* rpow_add_rpow_le_add
- \- *lemma* rpow_add_le_add_rpow
- \+/\- *theorem* young_inequality
- \- *theorem* pow_arith_mean_le_arith_mean_pow
- \- *theorem* pow_arith_mean_le_arith_mean_pow_of_even
- \- *theorem* zpow_arith_mean_le_arith_mean_zpow
- \- *theorem* rpow_arith_mean_le_arith_mean_rpow
- \- *theorem* arith_mean_le_rpow_mean
- \- *theorem* pow_arith_mean_le_arith_mean_pow
- \- *theorem* rpow_arith_mean_le_arith_mean_rpow
- \- *theorem* rpow_arith_mean_le_arith_mean2_rpow
- \- *theorem* arith_mean_le_rpow_mean
- \- *theorem* rpow_arith_mean_le_arith_mean_rpow
- \- *theorem* rpow_arith_mean_le_arith_mean2_rpow
- \+/\- *theorem* young_inequality
- \- *theorem* rpow_add_rpow_le

created src/analysis/mean_inequalities_pow.lean
- \+ *lemma* add_rpow_le_rpow_add
- \+ *lemma* rpow_add_rpow_le_add
- \+ *lemma* rpow_add_le_add_rpow
- \+ *theorem* pow_arith_mean_le_arith_mean_pow
- \+ *theorem* pow_arith_mean_le_arith_mean_pow_of_even
- \+ *theorem* zpow_arith_mean_le_arith_mean_zpow
- \+ *theorem* rpow_arith_mean_le_arith_mean_rpow
- \+ *theorem* arith_mean_le_rpow_mean
- \+ *theorem* pow_arith_mean_le_arith_mean_pow
- \+ *theorem* rpow_arith_mean_le_arith_mean_rpow
- \+ *theorem* rpow_arith_mean_le_arith_mean2_rpow
- \+ *theorem* arith_mean_le_rpow_mean
- \+ *theorem* rpow_arith_mean_le_arith_mean_rpow
- \+ *theorem* rpow_arith_mean_le_arith_mean2_rpow
- \+ *theorem* rpow_add_rpow_le

modified src/measure_theory/integral/mean_inequalities.lean



## [2021-11-17 09:02:05](https://github.com/leanprover-community/mathlib/commit/60363a4)
feat(finset/basic): Adding `list.to_finset_union` and `list.to_finset_inter` ([#10351](https://github.com/leanprover-community/mathlib/pull/10351))
Two tiny lemmas, matching their counterparts for `multiset`
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* to_finset_union
- \+ *lemma* to_finset_inter



## [2021-11-17 07:06:12](https://github.com/leanprover-community/mathlib/commit/8f6fd1b)
lint(*): curly braces linter ([#10280](https://github.com/leanprover-community/mathlib/pull/10280))
This PR:
1. Adds a style linter for curly braces: a line shall never end with `{` or start with `}` (modulo white space)
2. Adds `scripts/cleanup-braces.{sh,py}` to reflow lines that violate (1)
3. Runs the scripts from (2) to generate a boatload of changes in mathlib
4. Fixes one line that became to long due to (3)
#### Estimated changes
modified archive/imo/imo1960_q1.lean

modified archive/imo/imo1988_q6.lean

modified archive/sensitivity.lean

created scripts/cleanup-braces.py
- \+ *def* fix_brace_o(a,
- \+ *def* fix_brace_c(a,
- \+ *def* fix_brace_pair(a,
- \+ *def* fix_braces(filename):

created scripts/cleanup-braces.sh

modified scripts/lint-style.py
- \+ *def* braces_check(lines,

modified src/algebra/algebra/basic.lean
- \+/\- *def* semiring_to_ring
- \+/\- *def* semiring_to_ring

modified src/algebra/algebra/operations.lean

modified src/algebra/category/CommRing/pushout.lean
- \+/\- *lemma* pushout_cocone_inl
- \+/\- *lemma* pushout_cocone_inr
- \+/\- *lemma* pushout_cocone_X
- \+/\- *lemma* pushout_cocone_inl
- \+/\- *lemma* pushout_cocone_inr
- \+/\- *lemma* pushout_cocone_X

modified src/algebra/category/Group/images.lean

modified src/algebra/category/Mon/adjunctions.lean

modified src/algebra/continued_fractions/convergents_equiv.lean

modified src/algebra/direct_sum/ring.lean

modified src/algebra/free_algebra.lean

modified src/algebra/gcd_monoid/basic.lean

modified src/algebra/geom_sum.lean

modified src/algebra/group/to_additive.lean

modified src/algebra/group/units.lean

modified src/algebra/group_with_zero/basic.lean

modified src/algebra/lattice_ordered_group.lean

modified src/algebra/lie/of_associative.lean

modified src/algebra/lie/subalgebra.lean

modified src/algebra/module/basic.lean

modified src/algebra/module/linear_map.lean

modified src/algebra/module/submodule_lattice.lean

modified src/algebra/monoid_algebra/basic.lean

modified src/algebra/order/monoid.lean

modified src/algebra/star/chsh.lean

modified src/algebraic_geometry/structure_sheaf.lean

modified src/algebraic_topology/cech_nerve.lean

modified src/analysis/inner_product_space/basic.lean

modified src/analysis/inner_product_space/projection.lean

modified src/analysis/normed_space/lattice_ordered_group.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/analysis/special_functions/bernstein.lean

modified src/category_theory/limits/concrete_category.lean

modified src/category_theory/limits/shapes/images.lean

modified src/category_theory/monoidal/Mon_.lean

modified src/category_theory/monoidal/rigid.lean

modified src/category_theory/sites/sheafification.lean

modified src/combinatorics/colex.lean

modified src/computability/halting.lean

modified src/computability/partrec.lean

modified src/computability/partrec_code.lean

modified src/computability/primrec.lean

modified src/computability/regular_expressions.lean

modified src/computability/tm_to_partrec.lean

modified src/computability/turing_machine.lean

modified src/control/traversable/derive.lean

modified src/data/buffer/parser/numeral.lean

modified src/data/equiv/basic.lean

modified src/data/equiv/module.lean

modified src/data/equiv/set.lean

modified src/data/finsupp/basic.lean

modified src/data/int/basic.lean

modified src/data/list/basic.lean

modified src/data/list/defs.lean

modified src/data/list/perm.lean

modified src/data/list/sigma.lean

modified src/data/list/sort.lean

modified src/data/mllist.lean

modified src/data/multiset/basic.lean

modified src/data/multiset/functor.lean

modified src/data/nat/basic.lean

modified src/data/nat/gcd.lean

modified src/data/nat/sqrt.lean

modified src/data/num/lemmas.lean

modified src/data/pequiv.lean

modified src/data/pfunctor/multivariate/M.lean

modified src/data/pnat/basic.lean

modified src/data/polynomial/algebra_map.lean

modified src/data/qpf/multivariate/constructions/cofix.lean

modified src/data/qpf/multivariate/constructions/const.lean

modified src/data/qpf/multivariate/constructions/sigma.lean

modified src/data/qpf/univariate/basic.lean

modified src/data/rat/basic.lean

modified src/data/rat/order.lean

modified src/data/rbmap/default.lean

modified src/data/rbtree/basic.lean

modified src/data/rbtree/find.lean

modified src/data/rbtree/insert.lean

modified src/data/rbtree/main.lean

modified src/data/rbtree/min_max.lean

modified src/data/set/enumerate.lean

modified src/data/set/intervals/basic.lean

modified src/data/vector3.lean

modified src/deprecated/subfield.lean

modified src/deprecated/subring.lean

modified src/field_theory/adjoin.lean

modified src/field_theory/fixed.lean

modified src/field_theory/galois.lean

modified src/field_theory/perfect_closure.lean

modified src/field_theory/separable.lean

modified src/geometry/manifold/charted_space.lean

modified src/group_theory/free_group.lean

modified src/group_theory/order_of_element.lean

modified src/group_theory/perm/concrete_cycle.lean

modified src/group_theory/perm/cycles.lean

modified src/group_theory/perm/sign.lean

modified src/group_theory/subgroup/basic.lean

modified src/group_theory/submonoid/basic.lean

modified src/linear_algebra/affine_space/combination.lean

modified src/linear_algebra/alternating.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/clifford_algebra/basic.lean

modified src/linear_algebra/clifford_algebra/equivs.lean

modified src/linear_algebra/dfinsupp.lean

modified src/linear_algebra/exterior_algebra.lean

modified src/linear_algebra/finsupp.lean

modified src/linear_algebra/lagrange.lean

modified src/linear_algebra/matrix/polynomial.lean

modified src/linear_algebra/matrix/to_linear_equiv.lean

modified src/linear_algebra/multilinear/basic.lean

modified src/linear_algebra/multilinear/basis.lean

modified src/linear_algebra/pi_tensor_product.lean

modified src/linear_algebra/tensor_algebra.lean

modified src/linear_algebra/tensor_product.lean

modified src/logic/relation.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/decomposition/lebesgue.lean

modified src/measure_theory/measure/measure_space.lean

modified src/measure_theory/measure/outer_measure.lean

modified src/measure_theory/tactic.lean

modified src/meta/expr_lens.lean

modified src/model_theory/basic.lean

modified src/number_theory/dioph.lean

modified src/number_theory/padics/padic_norm.lean

modified src/number_theory/pell.lean

modified src/number_theory/zsqrtd/basic.lean

modified src/order/atoms.lean

modified src/order/bounded_lattice.lean

modified src/order/filter/basic.lean

modified src/order/lattice.lean

modified src/order/well_founded_set.lean

modified src/order/zorn.lean

modified src/representation_theory/maschke.lean

modified src/ring_theory/derivation.lean

modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/int/basic.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/polynomial/basic.lean

modified src/ring_theory/polynomial/bernstein.lean

modified src/ring_theory/polynomial/pochhammer.lean

modified src/ring_theory/power_series/basic.lean

modified src/ring_theory/unique_factorization_domain.lean

modified src/ring_theory/valuation/basic.lean

modified src/ring_theory/witt_vector/is_poly.lean

modified src/ring_theory/witt_vector/witt_polynomial.lean

modified src/set_theory/lists.lean

modified src/set_theory/ordinal_notation.lean

modified src/tactic/alias.lean

modified src/tactic/apply.lean

modified src/tactic/apply_fun.lean

modified src/tactic/chain.lean

modified src/tactic/converter/apply_congr.lean

modified src/tactic/converter/old_conv.lean

modified src/tactic/core.lean

modified src/tactic/dependencies.lean

modified src/tactic/doc_commands.lean

modified src/tactic/explode.lean

modified src/tactic/ext.lean

modified src/tactic/fresh_names.lean

modified src/tactic/generalizes.lean

modified src/tactic/hint.lean

modified src/tactic/induction.lean

modified src/tactic/interactive.lean

modified src/tactic/interactive_expr.lean

modified src/tactic/itauto.lean

modified src/tactic/lift.lean

modified src/tactic/lint/basic.lean

modified src/tactic/lint/type_classes.lean

modified src/tactic/local_cache.lean

modified src/tactic/localized.lean

modified src/tactic/monotonicity/interactive.lean

modified src/tactic/norm_cast.lean

modified src/tactic/norm_num.lean

modified src/tactic/restate_axiom.lean

modified src/tactic/simp_command.lean

modified src/tactic/simpa.lean

modified src/tactic/simps.lean

modified src/tactic/squeeze.lean

modified src/tactic/tidy.lean

modified src/tactic/transfer.lean

modified src/tactic/transform_decl.lean

modified src/tactic/unify_equations.lean

modified src/testing/slim_check/functions.lean

modified src/testing/slim_check/testable.lean

modified src/topology/category/Profinite/cofiltered_limit.lean

modified src/topology/constructions.lean

modified src/topology/instances/ennreal.lean

modified src/topology/list.lean

modified src/topology/metric_space/emetric_space.lean

modified src/topology/sheaves/sheaf_condition/sites.lean

modified src/topology/tactic.lean

modified src/topology/uniform_space/basic.lean



## [2021-11-17 04:51:54](https://github.com/leanprover-community/mathlib/commit/2bdadb4)
feat(order/imp): define `lattice.imp` and `lattice.biimp` ([#10327](https://github.com/leanprover-community/mathlib/pull/10327))
#### Estimated changes
modified src/order/boolean_algebra.lean
- \+/\- *lemma* sdiff_eq_bot_iff
- \+/\- *lemma* sdiff_eq_bot_iff

created src/order/imp.lean
- \+ *lemma* imp_eq_arrow
- \+ *lemma* biimp_eq_iff
- \+ *lemma* compl_imp
- \+ *lemma* compl_sdiff
- \+ *lemma* imp_mono
- \+ *lemma* inf_imp_eq
- \+ *lemma* imp_eq_top_iff
- \+ *lemma* imp_eq_bot_iff
- \+ *lemma* imp_bot
- \+ *lemma* top_imp
- \+ *lemma* bot_imp
- \+ *lemma* imp_top
- \+ *lemma* imp_self
- \+ *lemma* compl_imp_compl
- \+ *lemma* imp_inf_le
- \+ *lemma* inf_imp_eq_imp_imp
- \+ *lemma* le_imp_iff
- \+ *lemma* biimp_mp
- \+ *lemma* biimp_mpr
- \+ *lemma* biimp_comm
- \+ *lemma* biimp_eq_top_iff
- \+ *lemma* biimp_self
- \+ *lemma* biimp_symm
- \+ *lemma* compl_symm_diff
- \+ *lemma* compl_biimp
- \+ *lemma* compl_biimp_compl
- \+ *def* imp
- \+ *def* biimp

modified src/order/lattice.lean



## [2021-11-16 23:48:06](https://github.com/leanprover-community/mathlib/commit/0a2a922)
feat(combinatorics/set_family/shadow): Shadow of a set family ([#10223](https://github.com/leanprover-community/mathlib/pull/10223))
This defines `shadow 𝒜` where `𝒜 : finset (finset α))`.
#### Estimated changes
created src/combinatorics/set_family/shadow.lean
- \+ *lemma* shadow_empty
- \+ *lemma* shadow_monotone
- \+ *lemma* mem_shadow_iff
- \+ *lemma* erase_mem_shadow
- \+ *lemma* mem_shadow_iff_insert_mem
- \+ *lemma* mem_shadow_iff_exists_mem_card_add_one
- \+ *lemma* exists_subset_of_mem_shadow
- \+ *lemma* mem_shadow_iff_exists_mem_card_add
- \+ *def* shadow



## [2021-11-16 23:48:05](https://github.com/leanprover-community/mathlib/commit/7fec401)
feat(topology/metric_space/hausdorff_distance): add definition and lemmas about open thickenings of subsets ([#10188](https://github.com/leanprover-community/mathlib/pull/10188))
Add definition and basic API about open thickenings of subsets in metric spaces, in preparation for the portmanteau theorem on characterizations of weak convergence of Borel probability measures.
#### Estimated changes
modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* thickening_eq_preimage_inf_edist
- \+ *lemma* is_open_thickening
- \+ *lemma* thickening_empty
- \+ *lemma* thickening_mono
- \+ *lemma* thickening_subset_of_subset
- \+ *lemma* mem_thickening_iff
- \+ *lemma* thickening_eq_bUnion_ball
- \+ *def* thickening



## [2021-11-16 21:57:02](https://github.com/leanprover-community/mathlib/commit/bce0ede)
feat(number_theory/divisors): mem_divisors_self ([#10359](https://github.com/leanprover-community/mathlib/pull/10359))
From flt-regular.
#### Estimated changes
modified src/number_theory/divisors.lean
- \+ *lemma* mem_divisors_self



## [2021-11-16 21:57:00](https://github.com/leanprover-community/mathlib/commit/8f7971a)
refactor(linear_algebra/bilinear_form): Change namespace of is_refl, is_symm, and is_alt ([#10338](https://github.com/leanprover-community/mathlib/pull/10338))
The propositions `is_refl`, `is_symm`, and `is_alt` are now in the
namespace `bilin_form`. Moreover, `is_sym` is now renamed to `is_symm`.
#### Estimated changes
modified docs/overview.yaml

modified docs/undergrad.yaml

modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* ortho_comm
- \+/\- *lemma* is_refl
- \+ *lemma* ortho_comm
- \+ *lemma* is_symm_iff_flip'
- \+/\- *lemma* self_eq_zero
- \+/\- *lemma* neg
- \+/\- *lemma* is_refl
- \+ *lemma* ortho_comm
- \+/\- *lemma* le_orthogonal_orthogonal
- \+ *lemma* restrict_symm
- \- *lemma* ortho_sym
- \- *lemma* sym
- \+/\- *lemma* is_refl
- \- *lemma* ortho_sym
- \- *lemma* is_sym_iff_flip'
- \+/\- *lemma* self_eq_zero
- \+/\- *lemma* neg
- \+/\- *lemma* is_refl
- \- *lemma* ortho_sym
- \+/\- *lemma* le_orthogonal_orthogonal
- \- *lemma* restrict_sym
- \+ *def* is_symm
- \- *def* is_sym

modified src/linear_algebra/quadratic_form/basic.lean
- \+ *lemma* associated_is_symm
- \+/\- *lemma* associated_left_inverse
- \- *lemma* associated_is_sym
- \+/\- *lemma* associated_left_inverse

modified src/ring_theory/trace.lean
- \+ *lemma* trace_form_is_symm
- \- *lemma* trace_form_is_sym



## [2021-11-16 21:56:59](https://github.com/leanprover-community/mathlib/commit/698eb1e)
feat(data/fin/basic): add lemmas about fin.cast ([#10329](https://github.com/leanprover-community/mathlib/pull/10329))
#### Estimated changes
modified src/data/fin/basic.lean
- \+ *lemma* cast_add_cast
- \+ *lemma* cast_cast_add_left
- \+ *lemma* cast_cast_add_right
- \+ *lemma* cast_succ_eq
- \+ *lemma* succ_cast_eq
- \+ *lemma* cast_add_nat_zero
- \+ *lemma* add_nat_cast
- \+ *lemma* cast_add_nat_left
- \+ *lemma* cast_add_nat_right
- \+ *lemma* nat_add_cast
- \+ *lemma* cast_nat_add_right
- \+ *lemma* cast_nat_add_left
- \+ *lemma* cast_nat_add_zero



## [2021-11-16 18:44:35](https://github.com/leanprover-community/mathlib/commit/9fa14a6)
feat(topology/uniform_space): properties of uniform convergence ([#9958](https://github.com/leanprover-community/mathlib/pull/9958))
* From the sphere eversion project
* multiple proofs were golfed by @PatrickMassot 
* Probably some proofs can be golfed quite heavily
Co-authored by: Patrick Massot <patrickmassot@free.fr>
#### Estimated changes
modified src/logic/basic.lean
- \+ *lemma* imp_forall_iff

modified src/order/filter/basic.lean
- \+ *lemma* mem_prod_principal
- \+ *lemma* mem_prod_top

modified src/topology/uniform_space/compact_separated.lean
- \+ *lemma* continuous_on.tendsto_uniformly
- \+ *lemma* continuous.tendsto_uniformly

modified src/topology/uniform_space/separation.lean
- \+ *lemma* is_separated.mono
- \+ *lemma* _root_.is_separated.eq_of_uniform_continuous
- \+ *lemma* _root_.is_separated.prod

modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* tendsto_uniformly_on_iff_tendsto
- \+ *lemma* tendsto_uniformly_iff_tendsto
- \+ *lemma* tendsto_prod_top_iff
- \+ *lemma* uniform_continuous_on.tendsto_uniformly
- \+ *lemma* uniform_continuous₂.tendsto_uniformly



## [2021-11-16 18:44:34](https://github.com/leanprover-community/mathlib/commit/d6b83d8)
feat(number_theory): define the class number ([#9071](https://github.com/leanprover-community/mathlib/pull/9071))
We instantiate the finiteness proof of the class group for rings of integers, and define the class number of a number field, or of a separable function field, as the finite cardinality of the class group.
Co-Authored-By: Ashvni <ashvni.n@gmail.com>
Co-Authored-By: Filippo A. E. Nuccio <filippo.nuccio@univ-st-etienne.fr>
#### Estimated changes
modified src/data/polynomial/field_division.lean
- \+ *lemma* normalize_monic

modified src/number_theory/class_number/finite.lean

created src/number_theory/class_number/function_field.lean
- \+ *theorem* class_number_eq_one_iff

created src/number_theory/class_number/number_field.lean
- \+ *theorem* class_number_eq_one_iff
- \+ *theorem* class_number_eq

modified src/number_theory/function_field.lean

modified src/number_theory/number_field.lean

modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *lemma* ufm_of_gcd_of_wf_dvd_monoid
- \+/\- *lemma* ufm_of_gcd_of_wf_dvd_monoid



## [2021-11-16 15:57:33](https://github.com/leanprover-community/mathlib/commit/f780788)
feat(dynamics): define `{mul,add}_action.is_minimal` ([#10311](https://github.com/leanprover-community/mathlib/pull/10311))
#### Estimated changes
created src/dynamics/minimal.lean
- \+ *lemma* mul_action.dense_orbit
- \+ *lemma* dense_range_smul
- \+ *lemma* is_open.exists_smul_mem
- \+ *lemma* is_open.Union_preimage_smul
- \+ *lemma* is_open.Union_smul
- \+ *lemma* is_compact.exists_finite_cover_smul
- \+ *lemma* dense_of_nonempty_smul_invariant
- \+ *lemma* eq_empty_or_univ_of_smul_invariant_closed
- \+ *lemma* is_minimal_iff_closed_smul_invariant

modified src/group_theory/group_action/basic.lean
- \+ *lemma* orbit_nonempty



## [2021-11-16 12:48:56](https://github.com/leanprover-community/mathlib/commit/d36f17f)
feat(linear_algebra/sesquilinear_form): Add is_refl for sesq_form.is_alt ([#10341](https://github.com/leanprover-community/mathlib/pull/10341))
Lemma `is_refl` shows that an alternating sesquilinear form is reflexive.
Refactored `sesquilinear_form` in a similar way as `bilinear_form` will be in [#10338](https://github.com/leanprover-community/mathlib/pull/10338).
#### Estimated changes
modified src/linear_algebra/sesquilinear_form.lean
- \+/\- *lemma* eq_zero
- \+ *lemma* ortho_comm
- \+/\- *lemma* is_refl
- \+ *lemma* ortho_comm
- \+/\- *lemma* is_refl
- \+ *lemma* ortho_comm
- \+/\- *lemma* eq_zero
- \- *lemma* ortho_sym
- \- *lemma* sym
- \+/\- *lemma* is_refl
- \- *lemma* ortho_sym
- \+ *def* is_symm
- \- *def* is_sym



## [2021-11-16 12:48:55](https://github.com/leanprover-community/mathlib/commit/7f4b91b)
feat(linear_algebra/determinant): the determinant associated to the standard basis of the free module is the usual matrix determinant ([#10278](https://github.com/leanprover-community/mathlib/pull/10278))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/linear_algebra/determinant.lean
- \+ *lemma* pi.basis_fun_det

modified src/linear_algebra/matrix/basis.lean
- \+ *lemma* coe_pi_basis_fun.to_matrix_eq_transpose

modified src/linear_algebra/matrix/determinant.lean
- \+ *def* det_row_alternating
- \- *def* det_row_multilinear



## [2021-11-16 12:48:54](https://github.com/leanprover-community/mathlib/commit/e20af15)
feat(field_theory): define the field of rational functions `ratfunc` ([#9563](https://github.com/leanprover-community/mathlib/pull/9563))
This PR defines `ratfunc K` as the field of rational functions over a field `K`, in terms of `fraction_ring (polynomial K)`. I have been careful to use `structure`s and `@[irreducible] def`s. Not only does that make for a nicer API, it also helps quite a bit with unification since the check can stop at `ratfunc` and doesn't have to start unfolding along the lines of `fraction_field.field → localization.comm_ring → localization.comm_monoid → localization.has_mul` and/or `polynomial.integral_domain → polynomial.comm_ring → polynomial.ring → polynomial.semiring`.
Most of the API is automatically derived from the (components of the) `is_fraction_ring` instance: the map `polynomial K → ratpoly K` is `algebra_map`, the isomorphism to `fraction_ring (polynomial K)` is `is_localization.alg_equiv`, ...
As a first application to verify that the definitions work, I rewrote `function_field` in terms of `ratfunc`.
#### Estimated changes
modified docs/undergrad.yaml

created src/field_theory/ratfunc.lean
- \+ *lemma* of_fraction_ring_injective
- \+ *lemma* to_fraction_ring_injective
- \+ *lemma* mk_eq_div'
- \+ *lemma* mk_zero
- \+ *lemma* mk_coe_def
- \+ *lemma* mk_def_of_mem
- \+ *lemma* mk_def_of_ne
- \+ *lemma* mk_eq_localization_mk
- \+ *lemma* mk_one'
- \+ *lemma* mk_eq_mk
- \+ *lemma* lift_on_mk
- \+ *lemma* lift_on'_mk
- \+ *lemma* of_fraction_ring_zero
- \+ *lemma* of_fraction_ring_add
- \+ *lemma* of_fraction_ring_sub
- \+ *lemma* of_fraction_ring_neg
- \+ *lemma* of_fraction_ring_one
- \+ *lemma* of_fraction_ring_mul
- \+ *lemma* of_fraction_ring_div
- \+ *lemma* of_fraction_ring_inv
- \+ *lemma* mul_inv_cancel
- \+ *lemma* mk_smul
- \+ *lemma* mk_one
- \+ *lemma* of_fraction_ring_algebra_map
- \+ *lemma* mk_eq_div
- \+ *lemma* of_fraction_ring_comp_algebra_map
- \+ *lemma* algebra_map_injective
- \+ *lemma* algebra_map_eq_zero_iff
- \+ *lemma* algebra_map_ne_zero
- \+ *lemma* lift_on_div
- \+ *lemma* lift_on'_div
- \+ *lemma* of_fraction_ring_mk'
- \+ *lemma* of_fraction_ring_eq
- \+ *lemma* to_fraction_ring_eq
- \+ *lemma* aux_equiv_eq
- \+ *lemma* num_denom_div
- \+ *lemma* num_div
- \+ *lemma* num_zero
- \+ *lemma* num_one
- \+ *lemma* num_algebra_map
- \+ *lemma* num_div_dvd
- \+ *lemma* denom_div
- \+ *lemma* monic_denom
- \+ *lemma* denom_ne_zero
- \+ *lemma* denom_zero
- \+ *lemma* denom_one
- \+ *lemma* denom_algebra_map
- \+ *lemma* denom_div_dvd
- \+ *lemma* num_div_denom
- \+ *lemma* num_eq_zero_iff
- \+ *lemma* num_ne_zero
- \+ *lemma* num_mul_eq_mul_denom_iff
- \+ *lemma* num_denom_add
- \+ *lemma* num_denom_mul
- \+ *lemma* num_dvd
- \+ *lemma* denom_dvd
- \+ *lemma* num_mul_dvd
- \+ *lemma* denom_mul_dvd
- \+ *lemma* denom_add_dvd
- \+ *lemma* algebra_map_eq_C
- \+ *lemma* algebra_map_C
- \+ *lemma* algebra_map_comp_C
- \+ *lemma* num_C
- \+ *lemma* denom_C
- \+ *lemma* algebra_map_X
- \+ *lemma* num_X
- \+ *lemma* denom_X
- \+ *lemma* eval_eq_zero_of_eval₂_denom_eq_zero
- \+ *lemma* eval₂_denom_ne_zero
- \+ *lemma* eval_C
- \+ *lemma* eval_X
- \+ *lemma* eval_zero
- \+ *lemma* eval_one
- \+ *lemma* eval_algebra_map
- \+ *lemma* eval_add
- \+ *lemma* eval_mul
- \+ *def* aux_equiv
- \+ *def* num_denom
- \+ *def* num
- \+ *def* denom
- \+ *def* C
- \+ *def* X
- \+ *def* eval

modified src/group_theory/group_action/defs.lean

modified src/number_theory/function_field.lean



## [2021-11-16 08:37:36](https://github.com/leanprover-community/mathlib/commit/f01399c)
chore(order/filter/basic): add 2 trivial `simp` lemmas ([#10344](https://github.com/leanprover-community/mathlib/pull/10344))
#### Estimated changes
modified src/order/filter/basic.lean
- \+ *lemma* eventually_mem_set
- \+ *lemma* eventually_eq_univ



## [2021-11-16 08:37:35](https://github.com/leanprover-community/mathlib/commit/1181c99)
feat(algebra/order/archimedean): upgrade some `∃` to `∃!` ([#10343](https://github.com/leanprover-community/mathlib/pull/10343))
#### Estimated changes
modified src/algebra/order/archimedean.lean
- \+ *lemma* exists_unique_zsmul_near_of_pos
- \+ *lemma* exists_unique_zsmul_near_of_pos'
- \+ *lemma* exists_unique_add_zsmul_mem_Ico
- \+ *lemma* exists_unique_add_zsmul_mem_Ioc
- \- *lemma* exists_int_smul_near_of_pos
- \- *lemma* exists_int_smul_near_of_pos'
- \- *lemma* exists_add_int_smul_mem_Ico
- \- *lemma* exists_add_int_smul_mem_Ioc

modified src/algebra/periodic.lean

modified src/group_theory/archimedean.lean

modified src/logic/function/basic.lean
- \+ *lemma* bijective.exists_unique_iff
- \- *lemma* bijective.exists_unique
- \- *theorem* surjective.forall
- \- *theorem* surjective.forall₂
- \- *theorem* surjective.forall₃
- \- *theorem* surjective.exists
- \- *theorem* surjective.exists₂
- \- *theorem* surjective.exists₃



## [2021-11-16 06:43:17](https://github.com/leanprover-community/mathlib/commit/30abde6)
chore(*): clean up some unused open statements and extra simps ([#10342](https://github.com/leanprover-community/mathlib/pull/10342))
We clean up some specific statements that are essentially no-ops in the library, i.e. opening a namespace and then never using it and using a simp-set larger than actually needed.
This is a preparatory miscellany of small fixes for a larger PR upcoming from me and Johan to reduce imports in the library.
Hopefully merging this first will make the content of that PR clearer.
#### Estimated changes
modified src/category_theory/triangulated/basic.lean

modified src/data/list/basic.lean

modified src/data/matrix/basic.lean

modified src/measure_theory/measurable_space_def.lean

modified src/tactic/restate_axiom.lean



## [2021-11-16 04:55:57](https://github.com/leanprover-community/mathlib/commit/979f0e8)
feat(data/fin/basic): extract `div_nat`  and `mod_nat` from `fin_prod_fin_equiv` ([#10339](https://github.com/leanprover-community/mathlib/pull/10339))
This makes it a little easier to tell which component is div and which is mod from the docs alone, and also makes these available earlier than `data/equiv/fin`.
#### Estimated changes
modified src/data/equiv/fin.lean

modified src/data/fin/basic.lean
- \+ *lemma* coe_div_nat
- \+ *lemma* coe_mod_nat
- \+ *def* div_nat
- \+ *def* mod_nat



## [2021-11-16 03:17:25](https://github.com/leanprover-community/mathlib/commit/bd80b33)
chore(ring_theory/subring): fix stale docstring ([#10340](https://github.com/leanprover-community/mathlib/pull/10340))
Oversight from https://github.com/leanprover-community/mathlib/pull/10332
#### Estimated changes
modified src/ring_theory/subring.lean



## [2021-11-16 02:30:50](https://github.com/leanprover-community/mathlib/commit/9264f30)
feat(analysis/calculus/times_cont_diff): continuous affine maps are smooth ([#10335](https://github.com/leanprover-community/mathlib/pull/10335))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
created src/analysis/calculus/affine_map.lean
- \+ *lemma* times_cont_diff



## [2021-11-16 00:29:07](https://github.com/leanprover-community/mathlib/commit/bff69c9)
feat(data/nat/lattice): add ```Inf_add``` lemma  ([#10008](https://github.com/leanprover-community/mathlib/pull/10008))
Adds a lemma about Inf on natural numbers. It will be needed for the count PR.
#### Estimated changes
modified src/data/nat/lattice.lean
- \+ *lemma* Inf_empty
- \+ *lemma* Inf_add
- \+ *lemma* Inf_add'



## [2021-11-16 00:29:05](https://github.com/leanprover-community/mathlib/commit/ddb6c75)
feat(algebra/homology/exact): preadditive.exact_iff_exact_of_iso ([#9979](https://github.com/leanprover-community/mathlib/pull/9979))
#### Estimated changes
modified src/algebra/homology/exact.lean
- \+ *lemma* preadditive.exact_of_iso_of_exact
- \+ *lemma* preadditive.exact_iff_exact_of_iso

modified src/category_theory/arrow.lean
- \+ *lemma* left_hom_inv_right
- \+ *lemma* inv_left_hom_right



## [2021-11-15 22:46:44](https://github.com/leanprover-community/mathlib/commit/9074095)
chore(linear_algebra/pi_tensor_product): add reindex_reindex ([#10336](https://github.com/leanprover-community/mathlib/pull/10336))
#### Estimated changes
modified src/linear_algebra/pi_tensor_product.lean
- \+ *lemma* reindex_reindex



## [2021-11-15 22:46:43](https://github.com/leanprover-community/mathlib/commit/a0f2c47)
feat(logic/relation): induction principles for `trans_gen` ([#10331](https://github.com/leanprover-community/mathlib/pull/10331))
Corresponding induction principles already exist for `refl_trans_gen`.
#### Estimated changes
modified src/logic/relation.lean
- \+/\- *lemma* head
- \+ *lemma* head_induction_on
- \+ *lemma* trans_induction_on
- \+/\- *lemma* head



## [2021-11-15 22:46:41](https://github.com/leanprover-community/mathlib/commit/65ff54c)
feat(data/fintype/basic): add fin_injective ([#10330](https://github.com/leanprover-community/mathlib/pull/10330))
#### Estimated changes
modified src/data/fintype/basic.lean
- \+ *lemma* fin_injective
- \+ *theorem* fin.cast_eq_cast'



## [2021-11-15 21:01:46](https://github.com/leanprover-community/mathlib/commit/93047c5)
feat(linear_algebra/determinant): linear coordinates are ratio of determinants ([#10261](https://github.com/leanprover-community/mathlib/pull/10261))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/linear_algebra/basis.lean
- \+ *lemma* mk_coord_apply_eq
- \+ *lemma* mk_coord_apply_ne
- \+ *lemma* mk_coord_apply

modified src/linear_algebra/determinant.lean
- \+ *lemma* basis.det_smul_mk_coord_eq_det_update

modified src/linear_algebra/multilinear/basic.lean
- \+/\- *def* to_linear_map
- \+/\- *def* to_linear_map



## [2021-11-15 21:01:45](https://github.com/leanprover-community/mathlib/commit/7ccc7ae)
feat(topology/homotopy/fundamental_groupoid): The functor from `Top` to `Groupoid` ([#10195](https://github.com/leanprover-community/mathlib/pull/10195))
I have no idea if the ways I've done things is the right way, eg. I don't know if I need to be thinking about universes when defining the functor, so comments about that are definitely welcome.
#### Estimated changes
modified src/data/quot.lean
- \+ *lemma* map₂_mk

modified src/topology/homotopy/basic.lean
- \+/\- *lemma* symm
- \+/\- *lemma* symm
- \+/\- *lemma* symm
- \+/\- *lemma* symm

modified src/topology/homotopy/fundamental_groupoid.lean
- \+ *lemma* comp_eq
- \+ *def* fundamental_groupoid_functor

modified src/topology/homotopy/path.lean
- \+/\- *lemma* symm
- \+ *lemma* map
- \+ *lemma* hcomp
- \+/\- *lemma* symm
- \+ *def* map

modified src/topology/path_connected.lean
- \+ *lemma* map_symm
- \+ *lemma* map_trans
- \+ *lemma* map_id
- \+ *lemma* map_map



## [2021-11-15 21:01:44](https://github.com/leanprover-community/mathlib/commit/9c03e9d)
feat(data/fintype): computable trunc bijection from fin ([#10141](https://github.com/leanprover-community/mathlib/pull/10141))
When a type `X` lacks decidable equality, there is still computably a bijection `fin (card X) -> X` using `trunc`.
Also, move `fintype.equiv_fin_of_forall_mem_list` to `list.nodup.nth_le_equiv_of_forall_mem_list`.
#### Estimated changes
modified src/data/equiv/list.lean

modified src/data/fintype/basic.lean
- \+ *def* trunc_fin_bijection
- \- *def* equiv_fin_of_forall_mem_list

modified src/data/list/nodup_equiv_fin.lean
- \- *lemma* coe_nth_le_equiv_apply
- \- *lemma* coe_nth_le_equiv_symm_apply
- \+ *def* nth_le_bijection_of_forall_mem_list
- \+ *def* nth_le_equiv_of_forall_mem_list



## [2021-11-15 19:12:05](https://github.com/leanprover-community/mathlib/commit/7b60768)
feat(ring_theory/subring): weaken typeclass assumption for `units.pos_subgroup` ([#10332](https://github.com/leanprover-community/mathlib/pull/10332))
#### Estimated changes
modified src/ring_theory/subring.lean
- \+/\- *lemma* units.mem_pos_subgroup
- \+/\- *lemma* units.mem_pos_subgroup
- \+/\- *def* units.pos_subgroup
- \+/\- *def* units.pos_subgroup



## [2021-11-15 19:12:03](https://github.com/leanprover-community/mathlib/commit/7803884)
feat(data/pi): Composition of addition/subtraction/... of functions ([#10305](https://github.com/leanprover-community/mathlib/pull/10305))
#### Estimated changes
modified src/algebra/group/pi.lean
- \- *lemma* const_one
- \- *lemma* comp_one
- \- *lemma* one_comp

modified src/data/pi.lean
- \+ *lemma* const_one
- \+ *lemma* one_comp
- \+ *lemma* comp_one
- \+ *lemma* const_mul
- \+ *lemma* mul_comp
- \+ *lemma* const_inv
- \+ *lemma* inv_comp
- \+ *lemma* div_comp
- \+ *lemma* const_div



## [2021-11-15 19:12:01](https://github.com/leanprover-community/mathlib/commit/43ef578)
feat(category_theory/limits): Random results about limits. ([#10285](https://github.com/leanprover-community/mathlib/pull/10285))
#### Estimated changes
modified src/category_theory/limits/shapes/binary_products.lean

modified src/category_theory/limits/shapes/pullbacks.lean

modified src/category_theory/limits/shapes/types.lean
- \+ *def* coequalizer_colimit



## [2021-11-15 19:11:58](https://github.com/leanprover-community/mathlib/commit/1a47cfc)
feat(data/finset/basic): A finset has card two iff it's `{x, y}` for some `x ≠ y` ([#10252](https://github.com/leanprover-community/mathlib/pull/10252))
and the similar result for card three. Dumb but surprisingly annoying!
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* card_eq_two
- \+ *lemma* card_eq_three

modified src/data/list/basic.lean
- \+ *lemma* length_eq_two
- \+ *lemma* length_eq_three

modified src/data/multiset/basic.lean
- \+ *lemma* card_eq_two
- \+ *lemma* card_eq_three



## [2021-11-15 19:11:56](https://github.com/leanprover-community/mathlib/commit/9fe0cbc)
feat(category_theory/preadditive/additive_functor): map_zero' is a redundant field, remove it ([#10229](https://github.com/leanprover-community/mathlib/pull/10229))
The map_zero' field in the definition of an additive functor can be deduced from the map_add' field. So we remove it.
#### Estimated changes
modified src/algebra/category/Module/adjunctions.lean

modified src/algebra/homology/additive.lean

modified src/analysis/normed/group/SemiNormedGroup/completion.lean

modified src/category_theory/preadditive/additive_functor.lean
- \+/\- *lemma* coe_map_add_hom
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_zero
- \+/\- *lemma* coe_map_add_hom
- \+/\- *def* map_add_hom
- \+/\- *def* map_add_hom



## [2021-11-15 17:27:15](https://github.com/leanprover-community/mathlib/commit/64418d7)
fix(logic/basic): remove `noncomputable lemma` ([#10292](https://github.com/leanprover-community/mathlib/pull/10292))
It's been three years since this was discussed according to the zulip archive link in the library note.
According to CI, the reason is no longer relevant. Leaving these as `noncomputable lemma` is harmful as it results in non-defeq instance diamonds sometimes as lean was not able to unfold the lemmas to get to the data underneath.
Since these are now `def`s, the linter requires them to have docstrings.
#### Estimated changes
modified src/logic/basic.lean

modified src/tactic/lint/misc.lean



## [2021-11-15 17:27:13](https://github.com/leanprover-community/mathlib/commit/d5d6071)
chore(analysis/special_functions/trigonometric/arctan): put lemmas about derivatives into a new file ([#10157](https://github.com/leanprover-community/mathlib/pull/10157))
#### Estimated changes
modified src/analysis/special_functions/integrals.lean

modified src/analysis/special_functions/trigonometric/arctan.lean
- \+/\- *lemma* continuous_on_tan
- \- *lemma* has_strict_deriv_at_tan
- \- *lemma* has_deriv_at_tan
- \- *lemma* tendsto_abs_tan_of_cos_eq_zero
- \- *lemma* tendsto_abs_tan_at_top
- \- *lemma* continuous_at_tan
- \- *lemma* differentiable_at_tan
- \- *lemma* deriv_tan
- \- *lemma* times_cont_diff_at_tan
- \+/\- *lemma* continuous_on_tan
- \- *lemma* has_deriv_at_tan_of_mem_Ioo
- \- *lemma* differentiable_at_tan_of_mem_Ioo
- \- *lemma* has_strict_deriv_at_arctan
- \- *lemma* has_deriv_at_arctan
- \- *lemma* differentiable_at_arctan
- \- *lemma* differentiable_arctan
- \- *lemma* deriv_arctan
- \- *lemma* times_cont_diff_arctan
- \- *lemma* has_strict_deriv_at.arctan
- \- *lemma* has_deriv_at.arctan
- \- *lemma* has_deriv_within_at.arctan
- \- *lemma* deriv_within_arctan
- \- *lemma* deriv_arctan
- \- *lemma* has_strict_fderiv_at.arctan
- \- *lemma* has_fderiv_at.arctan
- \- *lemma* has_fderiv_within_at.arctan
- \- *lemma* fderiv_within_arctan
- \- *lemma* fderiv_arctan
- \- *lemma* differentiable_within_at.arctan
- \- *lemma* differentiable_at.arctan
- \- *lemma* differentiable_on.arctan
- \- *lemma* differentiable.arctan
- \- *lemma* times_cont_diff_at.arctan
- \- *lemma* times_cont_diff.arctan
- \- *lemma* times_cont_diff_within_at.arctan
- \- *lemma* times_cont_diff_on.arctan

created src/analysis/special_functions/trigonometric/arctan_deriv.lean
- \+ *lemma* has_strict_deriv_at_tan
- \+ *lemma* has_deriv_at_tan
- \+ *lemma* tendsto_abs_tan_of_cos_eq_zero
- \+ *lemma* tendsto_abs_tan_at_top
- \+ *lemma* continuous_at_tan
- \+ *lemma* differentiable_at_tan
- \+ *lemma* deriv_tan
- \+ *lemma* times_cont_diff_at_tan
- \+ *lemma* has_deriv_at_tan_of_mem_Ioo
- \+ *lemma* differentiable_at_tan_of_mem_Ioo
- \+ *lemma* has_strict_deriv_at_arctan
- \+ *lemma* has_deriv_at_arctan
- \+ *lemma* differentiable_at_arctan
- \+ *lemma* differentiable_arctan
- \+ *lemma* deriv_arctan
- \+ *lemma* times_cont_diff_arctan
- \+ *lemma* has_strict_deriv_at.arctan
- \+ *lemma* has_deriv_at.arctan
- \+ *lemma* has_deriv_within_at.arctan
- \+ *lemma* deriv_within_arctan
- \+ *lemma* deriv_arctan
- \+ *lemma* has_strict_fderiv_at.arctan
- \+ *lemma* has_fderiv_at.arctan
- \+ *lemma* has_fderiv_within_at.arctan
- \+ *lemma* fderiv_within_arctan
- \+ *lemma* fderiv_arctan
- \+ *lemma* differentiable_within_at.arctan
- \+ *lemma* differentiable_at.arctan
- \+ *lemma* differentiable_on.arctan
- \+ *lemma* differentiable.arctan
- \+ *lemma* times_cont_diff_at.arctan
- \+ *lemma* times_cont_diff.arctan
- \+ *lemma* times_cont_diff_within_at.arctan
- \+ *lemma* times_cont_diff_on.arctan

modified src/data/real/pi/leibniz.lean



## [2021-11-15 16:52:02](https://github.com/leanprover-community/mathlib/commit/02100d8)
feat(category_theory/sites/limits): `Sheaf J D` has colimits. ([#10334](https://github.com/leanprover-community/mathlib/pull/10334))
We show that the category of sheaves has colimits obtained by sheafifying colimits on the level of presheaves.
#### Estimated changes
modified src/category_theory/sites/limits.lean
- \+ *def* sheafify_cocone
- \+ *def* is_colimit_sheafify_cocone



## [2021-11-15 14:41:25](https://github.com/leanprover-community/mathlib/commit/bf06854)
feat(algebra/big_operators/basic): Sum over a product of finsets, right version ([#10124](https://github.com/leanprover-community/mathlib/pull/10124))
This adds `finset.sum_prod_right` and renames `finset.sum_prod` to `finset.sum_prod_left`.
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_product_right
- \+ *lemma* prod_product_right'

modified src/linear_algebra/matrix/determinant.lean

modified src/ring_theory/algebra_tower.lean



## [2021-11-15 12:56:47](https://github.com/leanprover-community/mathlib/commit/ca5c4b3)
feat(group_theory/group_action): add a few instances ([#10310](https://github.com/leanprover-community/mathlib/pull/10310))
* regular and opposite regular actions of a group on itself are transitive;
* the action of a group on an orbit is transitive.
#### Estimated changes
modified src/algebra/opposites.lean

modified src/group_theory/group_action/basic.lean
- \+/\- *lemma* orbit_eq_univ
- \- *lemma* exists_smul_eq
- \- *lemma* surjective_smul
- \+/\- *lemma* orbit_eq_univ

modified src/group_theory/group_action/defs.lean
- \+ *lemma* exists_smul_eq
- \+ *lemma* surjective_smul



## [2021-11-15 10:57:56](https://github.com/leanprover-community/mathlib/commit/ca61dbf)
feat(order/sup_indep): Finite supremum independence ([#9867](https://github.com/leanprover-community/mathlib/pull/9867))
This defines supremum independence of indexed finsets.
#### Estimated changes
modified src/data/finset/lattice.lean
- \+ *lemma* disjoint_sup_right
- \+ *lemma* disjoint_sup_left

created src/order/sup_indep.lean
- \+ *lemma* sup_indep.subset
- \+ *lemma* sup_indep_empty
- \+ *lemma* sup_indep_singleton
- \+ *lemma* sup_indep.attach
- \+ *lemma* sup_indep.sup
- \+ *lemma* sup_indep.bUnion
- \+ *lemma* sup_indep.pairwise_disjoint
- \+ *lemma* sup_indep_iff_pairwise_disjoint
- \+ *lemma* complete_lattice.independent_iff_sup_indep
- \+ *def* sup_indep



## [2021-11-15 08:05:28](https://github.com/leanprover-community/mathlib/commit/60bc370)
feat(category_theory/sites/limits): `Sheaf_to_presheaf` creates limits ([#10328](https://github.com/leanprover-community/mathlib/pull/10328))
As a consequence, we obtain that sheaves have limits (of a given shape) when the target category does, and that these limit sheaves are computed on each object of the site "pointwise".
#### Estimated changes
modified src/category_theory/limits/shapes/multiequalizer.lean
- \+ *def* is_limit.mk
- \+ *def* is_colimit.mk

created src/category_theory/sites/limits.lean
- \+ *lemma* is_sheaf_of_is_limit
- \+ *def* multifork_evaluation_cone
- \+ *def* is_limit_multifork_of_is_limit



## [2021-11-15 05:07:52](https://github.com/leanprover-community/mathlib/commit/189e066)
feat(category_theory/sites/sheafification): The sheafification of a presheaf. ([#10303](https://github.com/leanprover-community/mathlib/pull/10303))
We construct the sheafification of a presheaf `P` taking values in a concrete category `D` with enough (co)limits, where the forgetful functor preserves the appropriate (co)limits and reflects isomorphisms.
We follow the construction on the stacks project https://stacks.math.columbia.edu/tag/00W1
**Note:** There are two very long proofs here, so I added several comments explaining what's going on.
#### Estimated changes
modified src/category_theory/limits/concrete_category.lean
- \+ *lemma* concrete.multiequalizer_equiv_apply
- \+ *def* concrete.multiequalizer_equiv_aux
- \+ *def* concrete.multiequalizer_equiv

modified src/category_theory/sites/grothendieck.lean
- \+ *lemma* arrow.from_middle_condition
- \+ *lemma* arrow.to_middle_condition
- \+ *lemma* arrow.middle_spec
- \+ *def* bind
- \+ *def* bind_to_base
- \+ *def* arrow.from_middle
- \+ *def* arrow.to_middle

modified src/category_theory/sites/plus.lean
- \+ *lemma* to_plus_plus_lift
- \+ *lemma* plus_lift_unique
- \+ *lemma* plus_hom_ext
- \+ *def* iso_to_plus
- \+ *def* plus_lift

created src/category_theory/sites/sheafification.lean
- \+ *lemma* ext
- \+ *lemma* condition
- \+ *lemma* refine_apply
- \+ *lemma* pullback_apply
- \+ *lemma* pullback_refine
- \+ *lemma* mk_apply
- \+ *lemma* equiv_apply
- \+ *lemma* equiv_symm_eq_apply
- \+ *lemma* res_mk_eq_mk_pullback
- \+ *lemma* to_plus_mk
- \+ *lemma* to_plus_apply
- \+ *lemma* to_plus_eq_mk
- \+ *lemma* exists_rep
- \+ *lemma* eq_mk_iff_exists
- \+ *lemma* inj_of_sep
- \+ *lemma* sheafification_obj
- \+ *lemma* to_sheafification_app
- \+ *lemma* is_iso_to_sheafify
- \+ *lemma* to_sheafify_sheafify_lift
- \+ *lemma* sheafify_lift_unique
- \+ *lemma* sheafify_hom_ext
- \+ *lemma* sheafification_iso_hom
- \+ *lemma* sheafification_iso_inv
- \+ *theorem* sep
- \+ *theorem* exists_of_sep
- \+ *theorem* is_sheaf_of_sep
- \+ *theorem* is_sheaf_plus_plus
- \+ *def* meq
- \+ *def* refine
- \+ *def* pullback
- \+ *def* mk
- \+ *def* equiv
- \+ *def* mk
- \+ *def* meq_of_sep
- \+ *def* sheafify
- \+ *def* to_sheafify
- \+ *def* sheafification
- \+ *def* to_sheafification
- \+ *def* iso_sheafify
- \+ *def* sheafify_lift
- \+ *def* presheaf_to_Sheaf
- \+ *def* sheafification_adjunction
- \+ *def* sheafification_iso



## [2021-11-15 04:19:49](https://github.com/leanprover-community/mathlib/commit/62992fa)
feat(analysis/inner_product_space/spectrum): more concrete diagonalization theorem ([#10317](https://github.com/leanprover-community/mathlib/pull/10317))
This is a second version of the diagonalization theorem for self-adjoint operators on finite-dimensional inner product spaces, stating that a self-adjoint operator admits an orthonormal basis of eigenvectors, and deducing the standard consequences (when expressed with respect to this basis the operator acts diagonally).
I have also updated `undergrad.yaml` and `overview.yaml` to cover the diagonalization theorem and other things proved in the library about Hilbert spaces.
#### Estimated changes
modified docs/overview.yaml

modified docs/undergrad.yaml

modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* basis.coe_isometry_euclidean_of_orthonormal
- \+ *lemma* basis.coe_isometry_euclidean_of_orthonormal_symm

modified src/analysis/inner_product_space/spectrum.lean
- \+ *lemma* eigenvector_basis_orthonormal
- \+ *lemma* has_eigenvector_eigenvector_basis
- \+ *lemma* apply_eigenvector_basis
- \+ *lemma* diagonalization_basis_symm_apply
- \+ *lemma* diagonalization_basis_apply_self_apply



## [2021-11-14 20:27:17](https://github.com/leanprover-community/mathlib/commit/0c8f53e)
feat(linear_algebra/trace): add lemmas about trace of linear maps ([#10279](https://github.com/leanprover-community/mathlib/pull/10279))
Lemmas for the trace of the identity and the trace of a conjugation
#### Estimated changes
modified src/linear_algebra/trace.lean
- \+ *theorem* trace_conj
- \+ *theorem* trace_conj'
- \+ *theorem* trace_one



## [2021-11-14 18:03:48](https://github.com/leanprover-community/mathlib/commit/1b51fe0)
feat(linear_algebra/alternating): add alternating_map.comp_linear_map ([#10314](https://github.com/leanprover-community/mathlib/pull/10314))
#### Estimated changes
modified src/linear_algebra/alternating.lean
- \+ *lemma* coe_comp_linear_map
- \+ *lemma* comp_linear_map_apply
- \+ *lemma* zero_comp_linear_map
- \+ *lemma* add_comp_linear_map
- \+ *lemma* comp_linear_map_zero
- \+ *def* comp_linear_map



## [2021-11-14 17:03:13](https://github.com/leanprover-community/mathlib/commit/8728e85)
feat(measure_theory): drop some unneeded assumptions ([#10319](https://github.com/leanprover-community/mathlib/pull/10319))
Prove that for a nontrivial countably generated filter there exists a sequence that converges to this filter. Use this lemma to drop some assumptions.
#### Estimated changes
modified src/measure_theory/constructions/borel_space.lean
- \+/\- *lemma* measurable_of_tendsto_nnreal'
- \+/\- *lemma* measurable_of_tendsto_metric'
- \+/\- *lemma* measurable_of_tendsto_nnreal'
- \+/\- *lemma* measurable_of_tendsto_metric'

modified src/order/filter/at_top_bot.lean
- \+ *lemma* exists_seq_tendsto



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
modified src/algebra/module/linear_map.lean
- \+ *def* to_linear_map
- \+ *def* to_module_End
- \+ *def* to_module_End

modified src/data/equiv/module.lean
- \+ *def* automorphism_group.to_linear_map_monoid_hom
- \+ *def* to_module_aut
- \- *def* to_linear_map

modified src/linear_algebra/basic.lean
- \- *def* automorphism_group.to_linear_map_monoid_hom



## [2021-11-14 15:22:15](https://github.com/leanprover-community/mathlib/commit/299af47)
chore(data/fin/basic): move tuple stuff to a new file ([#10295](https://github.com/leanprover-community/mathlib/pull/10295))
There are almost 600 lines of tuple stuff, which is definitely sufficient to justify a standalone file.
The author information has been guessed from the git history.
Floris is responsible for `cons` and `tail` which came first in [#1294](https://github.com/leanprover-community/mathlib/pull/1294), Chris added find, and Yury and Sébastien were involved all over the place.
This is simply a cut-and-paste job, with the exception of the new module docstring which has been merged with the docstring for the tuple subheading.
#### Estimated changes
modified archive/100-theorems-list/82_cubing_a_cube.lean

modified src/data/fin/basic.lean
- \- *lemma* tuple0_le
- \- *lemma* tail_def
- \- *lemma* tail_cons
- \- *lemma* cons_succ
- \- *lemma* cons_zero
- \- *lemma* cons_update
- \- *lemma* update_cons_zero
- \- *lemma* cons_self_tail
- \- *lemma* tail_update_zero
- \- *lemma* tail_update_succ
- \- *lemma* comp_cons
- \- *lemma* comp_tail
- \- *lemma* le_cons
- \- *lemma* cons_le
- \- *lemma* range_cons
- \- *lemma* fin_append_apply_zero
- \- *lemma* init_def
- \- *lemma* init_snoc
- \- *lemma* snoc_cast_succ
- \- *lemma* snoc_last
- \- *lemma* snoc_update
- \- *lemma* update_snoc_last
- \- *lemma* snoc_init_self
- \- *lemma* init_update_last
- \- *lemma* init_update_cast_succ
- \- *lemma* tail_init_eq_init_tail
- \- *lemma* cons_snoc_eq_snoc_cons
- \- *lemma* comp_snoc
- \- *lemma* comp_init
- \- *lemma* forall_iff_succ_above
- \- *lemma* insert_nth_apply_same
- \- *lemma* insert_nth_apply_succ_above
- \- *lemma* succ_above_cases_eq_insert_nth
- \- *lemma* insert_nth_comp_succ_above
- \- *lemma* insert_nth_eq_iff
- \- *lemma* eq_insert_nth_iff
- \- *lemma* insert_nth_apply_below
- \- *lemma* insert_nth_apply_above
- \- *lemma* insert_nth_zero
- \- *lemma* insert_nth_zero'
- \- *lemma* insert_nth_last
- \- *lemma* insert_nth_last'
- \- *lemma* insert_nth_zero_right
- \- *lemma* insert_nth_binop
- \- *lemma* insert_nth_mul
- \- *lemma* insert_nth_add
- \- *lemma* insert_nth_div
- \- *lemma* insert_nth_sub
- \- *lemma* insert_nth_sub_same
- \- *lemma* insert_nth_le_iff
- \- *lemma* le_insert_nth_iff
- \- *lemma* insert_nth_mem_Icc
- \- *lemma* preimage_insert_nth_Icc_of_mem
- \- *lemma* preimage_insert_nth_Icc_of_not_mem
- \- *lemma* find_spec
- \- *lemma* is_some_find_iff
- \- *lemma* find_eq_none_iff
- \- *lemma* find_min
- \- *lemma* find_min'
- \- *lemma* nat_find_mem_find
- \- *lemma* mem_find_iff
- \- *lemma* find_eq_some_iff
- \- *lemma* mem_find_of_unique
- \- *def* tail
- \- *def* cons
- \- *def* append
- \- *def* init
- \- *def* snoc
- \- *def* succ_above_cases
- \- *def* insert_nth
- \- *def* find

created src/data/fin/tuple.lean
- \+ *lemma* tuple0_le
- \+ *lemma* tail_def
- \+ *lemma* tail_cons
- \+ *lemma* cons_succ
- \+ *lemma* cons_zero
- \+ *lemma* cons_update
- \+ *lemma* update_cons_zero
- \+ *lemma* cons_self_tail
- \+ *lemma* tail_update_zero
- \+ *lemma* tail_update_succ
- \+ *lemma* comp_cons
- \+ *lemma* comp_tail
- \+ *lemma* le_cons
- \+ *lemma* cons_le
- \+ *lemma* range_cons
- \+ *lemma* fin_append_apply_zero
- \+ *lemma* init_def
- \+ *lemma* init_snoc
- \+ *lemma* snoc_cast_succ
- \+ *lemma* snoc_last
- \+ *lemma* snoc_update
- \+ *lemma* update_snoc_last
- \+ *lemma* snoc_init_self
- \+ *lemma* init_update_last
- \+ *lemma* init_update_cast_succ
- \+ *lemma* tail_init_eq_init_tail
- \+ *lemma* cons_snoc_eq_snoc_cons
- \+ *lemma* comp_snoc
- \+ *lemma* comp_init
- \+ *lemma* forall_iff_succ_above
- \+ *lemma* insert_nth_apply_same
- \+ *lemma* insert_nth_apply_succ_above
- \+ *lemma* succ_above_cases_eq_insert_nth
- \+ *lemma* insert_nth_comp_succ_above
- \+ *lemma* insert_nth_eq_iff
- \+ *lemma* eq_insert_nth_iff
- \+ *lemma* insert_nth_apply_below
- \+ *lemma* insert_nth_apply_above
- \+ *lemma* insert_nth_zero
- \+ *lemma* insert_nth_zero'
- \+ *lemma* insert_nth_last
- \+ *lemma* insert_nth_last'
- \+ *lemma* insert_nth_zero_right
- \+ *lemma* insert_nth_binop
- \+ *lemma* insert_nth_mul
- \+ *lemma* insert_nth_add
- \+ *lemma* insert_nth_div
- \+ *lemma* insert_nth_sub
- \+ *lemma* insert_nth_sub_same
- \+ *lemma* insert_nth_le_iff
- \+ *lemma* le_insert_nth_iff
- \+ *lemma* insert_nth_mem_Icc
- \+ *lemma* preimage_insert_nth_Icc_of_mem
- \+ *lemma* preimage_insert_nth_Icc_of_not_mem
- \+ *lemma* find_spec
- \+ *lemma* is_some_find_iff
- \+ *lemma* find_eq_none_iff
- \+ *lemma* find_min
- \+ *lemma* find_min'
- \+ *lemma* nat_find_mem_find
- \+ *lemma* mem_find_iff
- \+ *lemma* find_eq_some_iff
- \+ *lemma* mem_find_of_unique
- \+ *def* tail
- \+ *def* cons
- \+ *def* append
- \+ *def* init
- \+ *def* snoc
- \+ *def* succ_above_cases
- \+ *def* insert_nth
- \+ *def* find

modified src/data/fin/vec_notation.lean

modified src/linear_algebra/multilinear/basic.lean

modified src/topology/constructions.lean



## [2021-11-14 15:22:14](https://github.com/leanprover-community/mathlib/commit/7dc33bf)
feat(data/nat/basic): Some `nat.find` lemmas ([#10263](https://github.com/leanprover-community/mathlib/pull/10263))
This proves `nat.find_le` and `nat.find_add` and renames the current `nat.find_le` to `nat.find_mono`.
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* find_le
- \+ *lemma* find_add
- \+ *theorem* find_mono
- \- *theorem* find_le

modified src/ring_theory/multiplicity.lean



## [2021-11-14 13:46:33](https://github.com/leanprover-community/mathlib/commit/dd72ebc)
feat(data/list/big_operators): When `list.sum` is strictly positive ([#10282](https://github.com/leanprover-community/mathlib/pull/10282))
#### Estimated changes
modified src/data/list/big_operators.lean
- \+ *lemma* one_lt_prod_of_one_lt



## [2021-11-14 09:32:09](https://github.com/leanprover-community/mathlib/commit/bca8278)
feat(algebra/lie/basic): add missing `@[ext]` and `@[simp]` lemmas ([#10316](https://github.com/leanprover-community/mathlib/pull/10316))
#### Estimated changes
modified src/algebra/lie/basic.lean
- \+ *lemma* coe_to_lie_hom
- \+ *lemma* to_linear_equiv_mk
- \+ *lemma* coe_linear_equiv_injective
- \+ *lemma* coe_injective
- \+ *lemma* ext
- \+ *lemma* self_trans_symm
- \+ *lemma* symm_trans_self
- \+ *lemma* symm_trans
- \+ *lemma* symm_trans
- \+ *lemma* self_trans_symm
- \+ *lemma* symm_trans_self
- \- *lemma* coe_to_lie_equiv
- \- *lemma* symm_trans_apply
- \- *lemma* bijective
- \- *lemma* injective
- \- *lemma* surjective
- \- *lemma* symm_trans_apply

modified src/data/equiv/module.lean
- \+ *lemma* coe_injective



## [2021-11-13 21:34:57](https://github.com/leanprover-community/mathlib/commit/3b5edd0)
refactor(set_theory/cardinal_ordinal): use TC assumptions instead of inequalities ([#10313](https://github.com/leanprover-community/mathlib/pull/10313))
Assume `[fintype α]` or `[infinite α]` instead of `#α < ω` or `ω ≤ #α`.
#### Estimated changes
modified src/set_theory/cardinal_ordinal.lean
- \+/\- *lemma* powerlt_omega
- \+ *lemma* mk_bounded_set_le_of_infinite
- \+ *lemma* mk_compl_of_infinite
- \+ *lemma* mk_compl_finset_of_infinite
- \+/\- *lemma* mk_compl_eq_mk_compl_infinite
- \+/\- *lemma* mk_compl_eq_mk_compl_finite_lift
- \+/\- *lemma* mk_compl_eq_mk_compl_finite
- \+/\- *lemma* mk_compl_eq_mk_compl_finite_same
- \+/\- *lemma* powerlt_omega
- \- *lemma* mk_bounded_set_le_of_omega_le
- \- *lemma* mk_compl_of_omega_le
- \- *lemma* mk_compl_finset_of_omega_le
- \+/\- *lemma* mk_compl_eq_mk_compl_infinite
- \+/\- *lemma* mk_compl_eq_mk_compl_finite_lift
- \+/\- *lemma* mk_compl_eq_mk_compl_finite
- \+/\- *lemma* mk_compl_eq_mk_compl_finite_same
- \+/\- *theorem* extend_function_finite
- \+/\- *theorem* extend_function_finite



## [2021-11-13 19:05:20](https://github.com/leanprover-community/mathlib/commit/d8c8725)
feat(ring_theory,algebraic_geometry): Miscellaneous lemmas/def/typo corrections ([#10307](https://github.com/leanprover-community/mathlib/pull/10307))
Split out from [#9802](https://github.com/leanprover-community/mathlib/pull/9802) since I'm aiming at more general version.
#### Estimated changes
modified src/algebraic_geometry/locally_ringed_space.lean

modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *lemma* is_basis_basic_opens
- \+ *lemma* local_hom_iff_comap_closed_point
- \+ *def* closed_point

modified src/algebraic_geometry/structure_sheaf.lean

modified src/category_theory/sites/sheaf_of_types.lean

modified src/category_theory/structured_arrow.lean

modified src/ring_theory/ideal/local_ring.lean
- \+ *theorem* local_hom_tfae

modified src/ring_theory/localization.lean
- \+ *lemma* iso_comp

modified src/topology/sheaves/sheaf_condition/sites.lean
- \+ *lemma* cover_dense_iff_is_basis
- \+ *lemma* cover_dense_induced_functor
- \+ *lemma* extend_hom_app
- \+ *lemma* hom_ext
- \+ *def* restrict_hom_equiv_hom



## [2021-11-13 17:25:11](https://github.com/leanprover-community/mathlib/commit/ca56c5a)
feat(measure_theory/group): define a few `measurable_equiv`s ([#10299](https://github.com/leanprover-community/mathlib/pull/10299))
#### Estimated changes
modified src/data/equiv/mul_add.lean
- \+ *lemma* inv_symm₀

created src/measure_theory/group/measurable_equiv.lean
- \+ *lemma* _root_.measurable_embedding_const_smul
- \+ *lemma* symm_smul
- \+ *lemma* coe_smul₀
- \+ *lemma* symm_smul₀
- \+ *lemma* _root_.measurable_embedding_const_smul₀
- \+ *lemma* coe_mul_left
- \+ *lemma* symm_mul_left
- \+ *lemma* to_equiv_mul_left
- \+ *lemma* _root_.measurable_embedding_mul_left
- \+ *lemma* _root_.measurable_embedding_mul_right
- \+ *lemma* coe_mul_right
- \+ *lemma* symm_mul_right
- \+ *lemma* to_equiv_mul_right
- \+ *lemma* _root_.measurable_embedding_mul_left₀
- \+ *lemma* coe_mul_left₀
- \+ *lemma* symm_mul_left₀
- \+ *lemma* to_equiv_mul_left₀
- \+ *lemma* _root_.measurable_embedding_mul_right₀
- \+ *lemma* coe_mul_right₀
- \+ *lemma* symm_mul_right₀
- \+ *lemma* to_equiv_mul_right₀
- \+ *lemma* symm_inv
- \+ *lemma* symm_inv₀
- \+ *def* smul
- \+ *def* smul₀
- \+ *def* mul_left
- \+ *def* mul_right
- \+ *def* mul_left₀
- \+ *def* mul_right₀
- \+ *def* inv
- \+ *def* inv₀



## [2021-11-13 16:06:16](https://github.com/leanprover-community/mathlib/commit/3578403)
feat(*/{group,mul}_action): more lemmas ([#10308](https://github.com/leanprover-community/mathlib/pull/10308))
* add several lemmas about orbits and pointwise scalar multiplication;
* generalize `mul_action.orbit.mul_action` to a monoid action;
* more lemmas about pretransitive actions, use `to_additive` more;
* add dot notation lemmas `is_open.smul` and `is_closed.smul`.
#### Estimated changes
modified src/group_theory/group_action/basic.lean
- \+ *lemma* maps_to_smul_orbit
- \+ *lemma* smul_orbit_subset
- \+ *lemma* orbit_smul_subset
- \+/\- *lemma* orbit.coe_smul
- \+ *lemma* surjective_smul
- \+ *lemma* orbit_eq_univ
- \+ *lemma* smul_orbit
- \+ *lemma* orbit_smul
- \+/\- *lemma* orbit_eq_iff
- \+/\- *lemma* mem_orbit_smul
- \+/\- *lemma* smul_mem_orbit_smul
- \- *lemma* exists_vadd_eq
- \+/\- *lemma* orbit_eq_iff
- \+/\- *lemma* orbit.coe_smul
- \+/\- *lemma* mem_orbit_smul
- \+/\- *lemma* smul_mem_orbit_smul

modified src/topology/algebra/mul_action.lean
- \+ *lemma* smul_closure_subset
- \+ *lemma* smul_closure_orbit_subset
- \+ *lemma* is_open.smul
- \+ *lemma* is_closed.smul



## [2021-11-13 14:24:59](https://github.com/leanprover-community/mathlib/commit/b91d344)
chore(data/equiv/*): rename `trans_symm` and `symm_trans` to `self_trans_symm` and `symm_trans_self`. ([#10309](https://github.com/leanprover-community/mathlib/pull/10309))
This frees up `symm_trans` to state `(a.trans b).symm = a.symm.trans b.symm`.
These names are consistent with `self_comp_symm` and `symm_comp_self`.
#### Estimated changes
modified src/analysis/normed_space/affine_isometry.lean
- \+ *lemma* self_trans_symm
- \+ *lemma* symm_trans_self
- \- *lemma* trans_symm
- \- *lemma* symm_trans

modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* self_trans_symm
- \+ *lemma* symm_trans_self
- \- *lemma* trans_symm
- \- *lemma* symm_trans

modified src/data/equiv/basic.lean
- \+ *theorem* symm_trans_self
- \+ *theorem* self_trans_symm
- \- *theorem* symm_trans
- \- *theorem* trans_symm

modified src/data/equiv/module.lean
- \+ *lemma* self_trans_symm
- \+ *lemma* symm_trans_self
- \- *lemma* trans_symm
- \- *lemma* symm_trans

modified src/data/equiv/ring.lean
- \+ *theorem* self_trans_symm
- \+ *theorem* symm_trans_self
- \- *theorem* trans_symm
- \- *theorem* symm_trans

modified src/data/finsupp/basic.lean

modified src/data/pequiv.lean
- \+ *lemma* self_trans_symm
- \+ *lemma* symm_trans_self
- \- *lemma* trans_symm
- \- *lemma* symm_trans

modified src/field_theory/splitting_field.lean

modified src/geometry/manifold/diffeomorph.lean
- \+ *lemma* self_trans_symm
- \+ *lemma* symm_trans_self
- \- *lemma* trans_symm
- \- *lemma* symm_trans

modified src/group_theory/perm/basic.lean
- \+ *lemma* inv_trans_self
- \+/\- *lemma* mul_symm
- \+ *lemma* self_trans_inv
- \+/\- *lemma* symm_mul
- \- *lemma* inv_trans
- \+/\- *lemma* mul_symm
- \- *lemma* trans_inv
- \+/\- *lemma* symm_mul

modified src/group_theory/perm/sign.lean

modified src/linear_algebra/affine_space/affine_equiv.lean
- \+ *lemma* self_trans_symm
- \+ *lemma* symm_trans_self
- \- *lemma* trans_symm
- \- *lemma* symm_trans

modified src/linear_algebra/determinant.lean



## [2021-11-13 10:27:54](https://github.com/leanprover-community/mathlib/commit/869cb32)
chore(measure_theory/probability_mass_function): Refactor the `pmf` file into a definitions file and a constructions file ([#10298](https://github.com/leanprover-community/mathlib/pull/10298))
#### Estimated changes
created src/measure_theory/probability_mass_function/basic.lean
- \+ *lemma* has_sum_coe_one
- \+ *lemma* summable_coe
- \+ *lemma* tsum_coe
- \+ *lemma* mem_support_iff
- \+ *lemma* apply_eq_zero_iff
- \+ *lemma* coe_le_one
- \+ *lemma* pure_apply
- \+ *lemma* mem_support_pure_iff
- \+ *lemma* bind_apply
- \+ *lemma* coe_bind_apply
- \+ *lemma* pure_bind
- \+ *lemma* bind_pure
- \+ *lemma* bind_bind
- \+ *lemma* bind_comm
- \+ *lemma* to_outer_measure_apply
- \+ *lemma* to_outer_measure_apply'
- \+ *lemma* to_outer_measure_apply_finset
- \+ *lemma* to_outer_measure_apply_fintype
- \+ *lemma* to_outer_measure_apply_eq_zero_iff
- \+ *lemma* to_outer_measure_caratheodory
- \+ *lemma* to_measure_apply_eq_to_outer_measure_apply
- \+ *lemma* to_outer_measure_apply_le_to_measure_apply
- \+ *lemma* to_measure_apply
- \+ *lemma* to_measure_apply'
- \+ *lemma* to_measure_apply_finset
- \+ *lemma* to_measure_apply_of_finite
- \+ *lemma* to_measure_apply_fintype
- \+ *def* {u}
- \+ *def* support
- \+ *def* pure
- \+ *def* bind
- \+ *def* to_outer_measure
- \+ *def* to_measure

renamed src/measure_theory/probability_mass_function.lean to src/measure_theory/probability_mass_function/constructions.lean
- \+/\- *lemma* bind_on_support_apply
- \+/\- *lemma* bind_on_support_eq_bind
- \+/\- *lemma* coe_bind_on_support_apply
- \+/\- *lemma* mem_support_bind_on_support_iff
- \+/\- *lemma* bind_on_support_eq_zero_iff
- \+/\- *lemma* pure_bind_on_support
- \+/\- *lemma* bind_on_support_pure
- \+/\- *lemma* bind_on_support_bind_on_support
- \+/\- *lemma* bind_on_support_comm
- \- *lemma* has_sum_coe_one
- \- *lemma* summable_coe
- \- *lemma* tsum_coe
- \- *lemma* mem_support_iff
- \- *lemma* coe_le_one
- \- *lemma* pure_apply
- \- *lemma* mem_support_pure_iff
- \- *lemma* bind_apply
- \- *lemma* coe_bind_apply
- \- *lemma* pure_bind
- \- *lemma* bind_pure
- \- *lemma* bind_bind
- \- *lemma* bind_comm
- \+/\- *lemma* bind_on_support_apply
- \+/\- *lemma* bind_on_support_eq_bind
- \+/\- *lemma* coe_bind_on_support_apply
- \+/\- *lemma* mem_support_bind_on_support_iff
- \+/\- *lemma* bind_on_support_eq_zero_iff
- \+/\- *lemma* pure_bind_on_support
- \+/\- *lemma* bind_on_support_pure
- \+/\- *lemma* bind_on_support_bind_on_support
- \+/\- *lemma* bind_on_support_comm
- \- *lemma* to_outer_measure_apply
- \- *lemma* to_outer_measure_apply'
- \- *lemma* to_outer_measure_apply_finset
- \- *lemma* to_outer_measure_apply_fintype
- \- *lemma* to_outer_measure_apply_eq_zero_iff
- \- *lemma* to_outer_measure_caratheodory
- \- *lemma* to_measure_apply_eq_to_outer_measure_apply
- \- *lemma* to_outer_measure_apply_le_to_measure_apply
- \- *lemma* to_measure_apply
- \- *lemma* to_measure_apply'
- \- *lemma* to_measure_apply_finset
- \- *lemma* to_measure_apply_of_finite
- \- *lemma* to_measure_apply_fintype
- \+/\- *def* bind_on_support
- \- *def* {u}
- \- *def* support
- \- *def* pure
- \- *def* bind
- \+/\- *def* bind_on_support
- \- *def* to_outer_measure
- \- *def* to_measure



## [2021-11-13 09:09:36](https://github.com/leanprover-community/mathlib/commit/a7e38a0)
feat(linear_algebra/bilinear_form): add is_refl and ortho_sym for alt_bilin_form ([#10304](https://github.com/leanprover-community/mathlib/pull/10304))
Lemma `is_refl` shows that every alternating bilinear form is reflexive.
Lemma `ortho_sym` shows that being orthogonal with respect to an alternating bilinear form is symmetric.
#### Estimated changes
modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* is_refl
- \+ *lemma* ortho_sym



## [2021-11-13 02:46:06](https://github.com/leanprover-community/mathlib/commit/a232366)
feat(analysis/inner_product_space/projection): orthonormal basis subordinate to an `orthogonal_family` ([#10208](https://github.com/leanprover-community/mathlib/pull/10208))
In a finite-dimensional inner product space of `E`, there exists an orthonormal basis subordinate to a given direct sum decomposition into an `orthogonal_family` of subspaces `E`.
#### Estimated changes
modified src/algebra/direct_sum/module.lean
- \+ *lemma* submodule_is_internal.collected_basis_coe
- \+ *lemma* submodule_is_internal.collected_basis_mem

modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* orthogonal_family.orthonormal_sigma_orthonormal
- \+ *lemma* direct_sum.submodule_is_internal.collected_basis_orthonormal

modified src/analysis/inner_product_space/projection.lean
- \+/\- *lemma* orthonormal_basis_orthonormal
- \+/\- *lemma* coe_orthonormal_basis
- \+/\- *lemma* fin_orthonormal_basis_orthonormal
- \+ *lemma* direct_sum.submodule_is_internal.subordinate_orthonormal_basis_orthonormal
- \+ *lemma* direct_sum.submodule_is_internal.subordinate_orthonormal_basis_subordinate
- \+/\- *lemma* orthonormal_basis_orthonormal
- \+/\- *lemma* coe_orthonormal_basis
- \+/\- *lemma* fin_orthonormal_basis_orthonormal
- \+/\- *def* orthonormal_basis_index
- \+/\- *def* orthonormal_basis
- \+/\- *def* fin_orthonormal_basis
- \+ *def* direct_sum.submodule_is_internal.sigma_orthonormal_basis_index_equiv
- \+ *def* direct_sum.submodule_is_internal.subordinate_orthonormal_basis
- \+ *def* direct_sum.submodule_is_internal.subordinate_orthonormal_basis_index
- \+/\- *def* orthonormal_basis_index
- \+/\- *def* orthonormal_basis
- \+/\- *def* fin_orthonormal_basis

modified src/data/finsupp/to_dfinsupp.lean
- \+ *lemma* sigma_finsupp_equiv_dfinsupp_single



## [2021-11-12 23:21:30](https://github.com/leanprover-community/mathlib/commit/8bb0b6f)
feat(category_theory/sites/plus): If P is a sheaf, then the map from P to P^+ is an isomorphism. ([#10297](https://github.com/leanprover-community/mathlib/pull/10297))
Also adds some simple results about (co)limits where the morphisms in the diagram are isomorphisms.
#### Estimated changes
modified src/category_theory/category/preorder.lean

modified src/category_theory/limits/shapes/terminal.lean
- \+ *lemma* is_iso_π_of_is_terminal
- \+ *lemma* is_iso_ι_of_is_initial
- \+ *def* is_terminal_top
- \+ *def* is_initial_bot
- \+ *def* cone_of_diagram_terminal
- \+ *def* limit_of_diagram_terminal
- \+ *def* limit_of_terminal
- \+ *def* cocone_of_diagram_initial
- \+ *def* colimit_of_diagram_initial
- \+ *def* colimit_of_initial

modified src/category_theory/sites/plus.lean
- \+ *lemma* is_iso_to_plus_of_is_sheaf



## [2021-11-12 21:42:51](https://github.com/leanprover-community/mathlib/commit/55534c4)
feat(data/nat/basic): recursion for set nat ([#10273](https://github.com/leanprover-community/mathlib/pull/10273))
Adding a special case of `nat.le_rec_on` where the predicate is membership of a subset.
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* set_induction_bounded
- \+ *lemma* set_induction
- \+ *lemma* set_eq_univ



## [2021-11-12 20:02:20](https://github.com/leanprover-community/mathlib/commit/6afda88)
feat(analysis/inner_product_space/spectrum): diagonalization of self-adjoint endomorphisms (finite dimension) ([#9995](https://github.com/leanprover-community/mathlib/pull/9995))
Diagonalization of a self-adjoint endomorphism `T` of a finite-dimensional inner product space `E` over either `ℝ` or `ℂ`:  construct a linear isometry `T.diagonalization` from `E` to the direct sum of `T`'s eigenspaces, such that `T` conjugated by `T.diagonalization` is diagonal:
```lean
lemma diagonalization_apply_self_apply (v : E) (μ : eigenvalues T) :
  hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ
```
#### Estimated changes
modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* orthogonal_family.comp
- \+ *lemma* is_self_adjoint.restrict_invariant

modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* direct_sum.submodule_is_internal.isometry_L2_of_orthogonal_family_symm_apply

modified src/analysis/inner_product_space/projection.lean
- \+/\- *lemma* orthogonal_family.submodule_is_internal_iff
- \+/\- *lemma* orthogonal_family.submodule_is_internal_iff

modified src/analysis/inner_product_space/rayleigh.lean
- \+ *lemma* subsingleton_of_no_eigenvalue_finite_dimensional

created src/analysis/inner_product_space/spectrum.lean
- \+ *lemma* invariant_orthogonal_eigenspace
- \+ *lemma* conj_eigenvalue_eq_self
- \+ *lemma* orthogonal_family_eigenspaces
- \+ *lemma* orthogonal_family_eigenspaces'
- \+ *lemma* orthogonal_supr_eigenspaces_invariant
- \+ *lemma* orthogonal_supr_eigenspaces
- \+ *lemma* orthogonal_supr_eigenspaces_eq_bot
- \+ *lemma* orthogonal_supr_eigenspaces_eq_bot'
- \+ *lemma* direct_sum_submodule_is_internal
- \+ *lemma* diagonalization_symm_apply
- \+ *lemma* diagonalization_apply_self_apply

modified src/data/dfinsupp.lean
- \+ *lemma* prod_eq_prod_fintype

modified src/linear_algebra/basic.lean
- \+ *lemma* _root_.linear_map.infi_invariant

modified src/order/complete_lattice.lean
- \+ *lemma* supr_ne_bot_subtype
- \+ *lemma* infi_ne_top_subtype



## [2021-11-12 17:48:18](https://github.com/leanprover-community/mathlib/commit/f0a9849)
feat(category_theory/sites/sheaf): Add sheaf conditions in terms of multiforks/multiequalizers. ([#10294](https://github.com/leanprover-community/mathlib/pull/10294))
Another PR toward sheafification.
#### Estimated changes
modified src/category_theory/sites/sheaf.lean
- \+ *lemma* is_sheaf.amalgamate_map
- \+ *lemma* is_sheaf.hom_ext
- \+ *lemma* is_sheaf_iff_multifork
- \+ *lemma* is_sheaf_iff_multiequalizer
- \+ *def* is_sheaf.amalgamate
- \+ *def* is_limit_of_is_sheaf



## [2021-11-12 17:08:23](https://github.com/leanprover-community/mathlib/commit/adb5c2d)
chore(analysis/special_functions/trigonometric/complex): put results about derivatives into a new file ([#10156](https://github.com/leanprover-community/mathlib/pull/10156))
#### Estimated changes
modified src/analysis/special_functions/trigonometric/arctan.lean

modified src/analysis/special_functions/trigonometric/complex.lean
- \- *lemma* has_strict_deriv_at_tan
- \- *lemma* has_deriv_at_tan
- \- *lemma* tendsto_abs_tan_of_cos_eq_zero
- \- *lemma* tendsto_abs_tan_at_top
- \- *lemma* continuous_at_tan
- \- *lemma* differentiable_at_tan
- \- *lemma* deriv_tan
- \- *lemma* times_cont_diff_at_tan

created src/analysis/special_functions/trigonometric/complex_deriv.lean
- \+ *lemma* has_strict_deriv_at_tan
- \+ *lemma* has_deriv_at_tan
- \+ *lemma* tendsto_abs_tan_of_cos_eq_zero
- \+ *lemma* tendsto_abs_tan_at_top
- \+ *lemma* continuous_at_tan
- \+ *lemma* differentiable_at_tan
- \+ *lemma* deriv_tan
- \+ *lemma* times_cont_diff_at_tan



## [2021-11-12 16:30:34](https://github.com/leanprover-community/mathlib/commit/6262165)
feat(analysis/normed_space/continuous_affine_map): isometry from space of continuous affine maps to product of codomain with space of continuous linear maps ([#10201](https://github.com/leanprover-community/mathlib/pull/10201))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/analysis/normed_space/continuous_affine_map.lean
- \+ *lemma* coe_cont_linear
- \+/\- *lemma* coe_linear_eq_coe_cont_linear
- \+ *lemma* comp_cont_linear
- \+ *lemma* to_affine_map_cont_linear
- \+ *lemma* zero_cont_linear
- \+ *lemma* add_cont_linear
- \+ *lemma* sub_cont_linear
- \+ *lemma* neg_cont_linear
- \+ *lemma* smul_cont_linear
- \+ *lemma* decomp
- \+ *lemma* norm_def
- \+ *lemma* norm_cont_linear_le
- \+ *lemma* norm_image_zero_le
- \+ *lemma* norm_eq
- \+ *lemma* norm_comp_le
- \+ *lemma* to_const_prod_continuous_linear_map_fst
- \+ *lemma* to_const_prod_continuous_linear_map_snd
- \+/\- *lemma* coe_linear_eq_coe_cont_linear

modified src/topology/algebra/continuous_affine_map.lean
- \+ *lemma* coe_zero
- \+ *lemma* zero_apply
- \+ *lemma* coe_smul
- \+ *lemma* smul_apply
- \+ *lemma* coe_add
- \+ *lemma* add_apply
- \+ *lemma* coe_sub
- \+ *lemma* sub_apply
- \+ *lemma* coe_neg
- \+ *lemma* neg_apply
- \+ *lemma* coe_to_continuous_affine_map
- \+ *lemma* to_continuous_affine_map_map_zero
- \+ *def* to_continuous_affine_map



## [2021-11-12 15:38:34](https://github.com/leanprover-community/mathlib/commit/b9f7b4d)
fix(algebra/graded_monoid): correct nonexistent names in tactic defaults ([#10293](https://github.com/leanprover-community/mathlib/pull/10293))
These were left by a bad rename by me in the past, and resulted in the default values not actually working.
#### Estimated changes
modified src/algebra/graded_monoid.lean



## [2021-11-12 15:38:33](https://github.com/leanprover-community/mathlib/commit/d7b5ffa)
chore(linear_algebra/multilinear): add const_of_is_empty ([#10291](https://github.com/leanprover-community/mathlib/pull/10291))
This is extracted from `pi_tensor_product.is_empty_equiv`
#### Estimated changes
modified src/linear_algebra/multilinear/basic.lean
- \+ *def* const_of_is_empty

modified src/linear_algebra/pi_tensor_product.lean



## [2021-11-12 15:38:31](https://github.com/leanprover-community/mathlib/commit/c5027c9)
doc(field_theory/separable): typo ([#10290](https://github.com/leanprover-community/mathlib/pull/10290))
#### Estimated changes
modified src/field_theory/separable.lean



## [2021-11-12 15:04:38](https://github.com/leanprover-community/mathlib/commit/6cd6320)
feat(group_theory/complement): `is_complement'.sup_eq_top` ([#10230](https://github.com/leanprover-community/mathlib/pull/10230))
If `H` and `K` are complementary subgroups, then `H ⊔ K = ⊤`.
#### Estimated changes
modified src/group_theory/complement.lean
- \+ *lemma* is_complement'.is_compl
- \+ *lemma* is_complement'.sup_eq_top
- \+/\- *lemma* is_complement'.disjoint
- \+/\- *lemma* is_complement'.disjoint



## [2021-11-12 12:24:46](https://github.com/leanprover-community/mathlib/commit/07be904)
doc(README): add list of emeritus maintainers ([#10288](https://github.com/leanprover-community/mathlib/pull/10288))
#### Estimated changes
modified README.md



## [2021-11-12 11:49:22](https://github.com/leanprover-community/mathlib/commit/b51335c)
feat(category_theory/sites/plus): `P⁺` for a presheaf `P`. ([#10284](https://github.com/leanprover-community/mathlib/pull/10284))
This file adds the construction of `P⁺`, for a presheaf `P : Cᵒᵖ ⥤ D`, whenever `C` has a Grothendieck topology `J` and `D` has the appropriate (co)limits.
Later, we will show that `P⁺⁺` is the sheafification of `P`, under certain additional hypotheses on `D`.
See https://stacks.math.columbia.edu/tag/00W1
#### Estimated changes
modified src/category_theory/sites/grothendieck.lean
- \+ *lemma* coe_fun_coe
- \+ *lemma* condition
- \+ *lemma* ext
- \+ *lemma* relation.map_fst
- \+ *lemma* relation.map_snd
- \+ *lemma* relation.base_fst
- \+ *lemma* relation.base_snd
- \+ *lemma* coe_pullback
- \+ *def* cover
- \+ *def* arrow.map
- \+ *def* relation.map
- \+ *def* relation.fst
- \+ *def* relation.snd
- \+ *def* pullback
- \+ *def* arrow.base
- \+ *def* relation.base
- \+ *def* pullback_id
- \+ *def* pullback_comp
- \+ *def* index
- \+ *def* pullback
- \+ *def* pullback_id
- \+ *def* pullback_comp

created src/category_theory/sites/plus.lean
- \+ *lemma* plus_map_to_plus
- \+ *def* diagram
- \+ *def* diagram_pullback
- \+ *def* plus_obj
- \+ *def* plus_map
- \+ *def* plus_functor
- \+ *def* to_plus
- \+ *def* to_plus_nat_trans



## [2021-11-12 10:27:58](https://github.com/leanprover-community/mathlib/commit/e679093)
feat(measure_theory): define `measurable_space` instance on a quotient ([#10275](https://github.com/leanprover-community/mathlib/pull/10275))
#### Estimated changes
modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_set_quotient
- \+ *lemma* measurable_from_quotient
- \+ *lemma* measurable_quotient_mk
- \+ *lemma* measurable_quotient_mk'
- \+ *lemma* measurable_quot_mk
- \+ *lemma* quotient_group.measurable_coe
- \+ *lemma* quotient_group.measurable_from_quotient



## [2021-11-12 09:37:57](https://github.com/leanprover-community/mathlib/commit/c45e70a)
chore(analysis/special_functions/pow): put lemmas about derivatives into a new file ([#10153](https://github.com/leanprover-community/mathlib/pull/10153))
In order to keep results about continuity of the power function in the original file, we prove some continuity results directly (these were previously proved using derivatives).
#### Estimated changes
modified archive/100-theorems-list/9_area_of_a_circle.lean

modified src/analysis/complex/polynomial.lean

modified src/analysis/convex/specific_functions.lean

modified src/analysis/special_functions/pow.lean
- \+ *lemma* zero_cpow_eq_nhds
- \+ *lemma* cpow_eq_nhds
- \+ *lemma* cpow_eq_nhds'
- \+ *lemma* continuous_at_const_cpow
- \+ *lemma* continuous_at_const_cpow'
- \+ *lemma* continuous_at_cpow_const
- \+ *lemma* continuous_at_cpow
- \+ *lemma* continuous_at_const_rpow
- \+ *lemma* continuous_at_const_rpow'
- \+ *lemma* rpow_eq_nhds_of_neg
- \+ *lemma* rpow_eq_nhds_of_pos
- \+/\- *lemma* continuous_at_rpow_of_ne
- \- *lemma* has_strict_fderiv_at_cpow
- \- *lemma* has_strict_fderiv_at_cpow'
- \- *lemma* has_strict_deriv_at_const_cpow
- \- *lemma* has_fderiv_at_cpow
- \- *lemma* has_strict_fderiv_at.cpow
- \- *lemma* has_strict_fderiv_at.const_cpow
- \- *lemma* has_fderiv_at.cpow
- \- *lemma* has_fderiv_at.const_cpow
- \- *lemma* has_fderiv_within_at.cpow
- \- *lemma* has_fderiv_within_at.const_cpow
- \- *lemma* differentiable_at.cpow
- \- *lemma* differentiable_at.const_cpow
- \- *lemma* differentiable_within_at.cpow
- \- *lemma* differentiable_within_at.const_cpow
- \- *lemma* has_strict_deriv_at.cpow
- \- *lemma* has_strict_deriv_at.const_cpow
- \- *lemma* complex.has_strict_deriv_at_cpow_const
- \- *lemma* has_strict_deriv_at.cpow_const
- \- *lemma* has_deriv_at.cpow
- \- *lemma* has_deriv_at.const_cpow
- \- *lemma* has_deriv_at.cpow_const
- \- *lemma* has_deriv_within_at.cpow
- \- *lemma* has_deriv_within_at.const_cpow
- \- *lemma* has_deriv_within_at.cpow_const
- \- *lemma* has_strict_fderiv_at_rpow_of_pos
- \- *lemma* has_strict_fderiv_at_rpow_of_neg
- \- *lemma* times_cont_diff_at_rpow_of_ne
- \- *lemma* differentiable_at_rpow_of_ne
- \+/\- *lemma* continuous_at_rpow_of_ne
- \- *lemma* _root_.has_strict_deriv_at.rpow
- \- *lemma* has_strict_deriv_at_rpow_const_of_ne
- \- *lemma* has_strict_deriv_at_const_rpow
- \- *lemma* has_strict_deriv_at_const_rpow_of_neg
- \- *lemma* has_deriv_at_rpow_const
- \- *lemma* differentiable_rpow_const
- \- *lemma* deriv_rpow_const
- \- *lemma* deriv_rpow_const'
- \- *lemma* times_cont_diff_at_rpow_const_of_ne
- \- *lemma* times_cont_diff_rpow_const_of_le
- \- *lemma* times_cont_diff_at_rpow_const_of_le
- \- *lemma* times_cont_diff_at_rpow_const
- \- *lemma* has_strict_deriv_at_rpow_const
- \- *lemma* has_fderiv_within_at.rpow
- \- *lemma* has_fderiv_at.rpow
- \- *lemma* has_strict_fderiv_at.rpow
- \- *lemma* differentiable_within_at.rpow
- \- *lemma* differentiable_at.rpow
- \- *lemma* differentiable_on.rpow
- \- *lemma* differentiable.rpow
- \- *lemma* has_fderiv_within_at.rpow_const
- \- *lemma* has_fderiv_at.rpow_const
- \- *lemma* has_strict_fderiv_at.rpow_const
- \- *lemma* differentiable_within_at.rpow_const
- \- *lemma* differentiable_at.rpow_const
- \- *lemma* differentiable_on.rpow_const
- \- *lemma* differentiable.rpow_const
- \- *lemma* has_fderiv_within_at.const_rpow
- \- *lemma* has_fderiv_at.const_rpow
- \- *lemma* has_strict_fderiv_at.const_rpow
- \- *lemma* times_cont_diff_within_at.rpow
- \- *lemma* times_cont_diff_at.rpow
- \- *lemma* times_cont_diff_on.rpow
- \- *lemma* times_cont_diff.rpow
- \- *lemma* times_cont_diff_within_at.rpow_const_of_ne
- \- *lemma* times_cont_diff_at.rpow_const_of_ne
- \- *lemma* times_cont_diff_on.rpow_const_of_ne
- \- *lemma* times_cont_diff.rpow_const_of_ne
- \- *lemma* times_cont_diff_within_at.rpow_const_of_le
- \- *lemma* times_cont_diff_at.rpow_const_of_le
- \- *lemma* times_cont_diff_on.rpow_const_of_le
- \- *lemma* times_cont_diff.rpow_const_of_le
- \- *lemma* has_deriv_within_at.rpow
- \- *lemma* has_deriv_at.rpow
- \- *lemma* has_deriv_within_at.rpow_const
- \- *lemma* has_deriv_at.rpow_const
- \- *lemma* deriv_within_rpow_const
- \- *lemma* deriv_rpow_const
- \- *lemma* tendsto_one_plus_div_rpow_exp
- \- *lemma* tendsto_one_plus_div_pow_exp

created src/analysis/special_functions/pow_deriv.lean
- \+ *lemma* has_strict_fderiv_at_cpow
- \+ *lemma* has_strict_fderiv_at_cpow'
- \+ *lemma* has_strict_deriv_at_const_cpow
- \+ *lemma* has_fderiv_at_cpow
- \+ *lemma* has_strict_fderiv_at.cpow
- \+ *lemma* has_strict_fderiv_at.const_cpow
- \+ *lemma* has_fderiv_at.cpow
- \+ *lemma* has_fderiv_at.const_cpow
- \+ *lemma* has_fderiv_within_at.cpow
- \+ *lemma* has_fderiv_within_at.const_cpow
- \+ *lemma* differentiable_at.cpow
- \+ *lemma* differentiable_at.const_cpow
- \+ *lemma* differentiable_within_at.cpow
- \+ *lemma* differentiable_within_at.const_cpow
- \+ *lemma* has_strict_deriv_at.cpow
- \+ *lemma* has_strict_deriv_at.const_cpow
- \+ *lemma* complex.has_strict_deriv_at_cpow_const
- \+ *lemma* has_strict_deriv_at.cpow_const
- \+ *lemma* has_deriv_at.cpow
- \+ *lemma* has_deriv_at.const_cpow
- \+ *lemma* has_deriv_at.cpow_const
- \+ *lemma* has_deriv_within_at.cpow
- \+ *lemma* has_deriv_within_at.const_cpow
- \+ *lemma* has_deriv_within_at.cpow_const
- \+ *lemma* has_strict_fderiv_at_rpow_of_pos
- \+ *lemma* has_strict_fderiv_at_rpow_of_neg
- \+ *lemma* times_cont_diff_at_rpow_of_ne
- \+ *lemma* differentiable_at_rpow_of_ne
- \+ *lemma* _root_.has_strict_deriv_at.rpow
- \+ *lemma* has_strict_deriv_at_rpow_const_of_ne
- \+ *lemma* has_strict_deriv_at_const_rpow
- \+ *lemma* has_strict_deriv_at_const_rpow_of_neg
- \+ *lemma* has_deriv_at_rpow_const
- \+ *lemma* differentiable_rpow_const
- \+ *lemma* deriv_rpow_const
- \+ *lemma* deriv_rpow_const'
- \+ *lemma* times_cont_diff_at_rpow_const_of_ne
- \+ *lemma* times_cont_diff_rpow_const_of_le
- \+ *lemma* times_cont_diff_at_rpow_const_of_le
- \+ *lemma* times_cont_diff_at_rpow_const
- \+ *lemma* has_strict_deriv_at_rpow_const
- \+ *lemma* has_fderiv_within_at.rpow
- \+ *lemma* has_fderiv_at.rpow
- \+ *lemma* has_strict_fderiv_at.rpow
- \+ *lemma* differentiable_within_at.rpow
- \+ *lemma* differentiable_at.rpow
- \+ *lemma* differentiable_on.rpow
- \+ *lemma* differentiable.rpow
- \+ *lemma* has_fderiv_within_at.rpow_const
- \+ *lemma* has_fderiv_at.rpow_const
- \+ *lemma* has_strict_fderiv_at.rpow_const
- \+ *lemma* differentiable_within_at.rpow_const
- \+ *lemma* differentiable_at.rpow_const
- \+ *lemma* differentiable_on.rpow_const
- \+ *lemma* differentiable.rpow_const
- \+ *lemma* has_fderiv_within_at.const_rpow
- \+ *lemma* has_fderiv_at.const_rpow
- \+ *lemma* has_strict_fderiv_at.const_rpow
- \+ *lemma* times_cont_diff_within_at.rpow
- \+ *lemma* times_cont_diff_at.rpow
- \+ *lemma* times_cont_diff_on.rpow
- \+ *lemma* times_cont_diff.rpow
- \+ *lemma* times_cont_diff_within_at.rpow_const_of_ne
- \+ *lemma* times_cont_diff_at.rpow_const_of_ne
- \+ *lemma* times_cont_diff_on.rpow_const_of_ne
- \+ *lemma* times_cont_diff.rpow_const_of_ne
- \+ *lemma* times_cont_diff_within_at.rpow_const_of_le
- \+ *lemma* times_cont_diff_at.rpow_const_of_le
- \+ *lemma* times_cont_diff_on.rpow_const_of_le
- \+ *lemma* times_cont_diff.rpow_const_of_le
- \+ *lemma* has_deriv_within_at.rpow
- \+ *lemma* has_deriv_at.rpow
- \+ *lemma* has_deriv_within_at.rpow_const
- \+ *lemma* has_deriv_at.rpow_const
- \+ *lemma* deriv_within_rpow_const
- \+ *lemma* deriv_rpow_const
- \+ *lemma* tendsto_one_plus_div_rpow_exp
- \+ *lemma* tendsto_one_plus_div_pow_exp

modified src/analysis/special_functions/trigonometric/complex.lean



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
modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* sum_map_range_index.linear_map

modified src/linear_algebra/eigenspace.lean
- \+ *lemma* eigenspaces_independent
- \+/\- *lemma* eigenvectors_linear_independent
- \+/\- *lemma* eigenvectors_linear_independent



## [2021-11-12 07:59:46](https://github.com/leanprover-community/mathlib/commit/1019dd6)
feat(measure_theory/probability_mass_function): Define a measure assosiated to a pmf ([#9966](https://github.com/leanprover-community/mathlib/pull/9966))
This PR defines `pmf.to_outer_measure` and `pmf.to_measure`, where the measure of a set is given by the total probability of elements of the set, and shows that this is a probability measure.
#### Estimated changes
modified src/measure_theory/probability_mass_function.lean
- \+ *lemma* to_outer_measure_apply
- \+ *lemma* to_outer_measure_apply'
- \+ *lemma* to_outer_measure_apply_finset
- \+ *lemma* to_outer_measure_apply_fintype
- \+ *lemma* to_outer_measure_apply_eq_zero_iff
- \+ *lemma* to_outer_measure_caratheodory
- \+ *lemma* to_measure_apply_eq_to_outer_measure_apply
- \+ *lemma* to_outer_measure_apply_le_to_measure_apply
- \+ *lemma* to_measure_apply
- \+ *lemma* to_measure_apply'
- \+ *lemma* to_measure_apply_finset
- \+ *lemma* to_measure_apply_of_finite
- \+ *lemma* to_measure_apply_fintype
- \+/\- *def* support
- \+ *def* to_outer_measure
- \+ *def* to_measure
- \+/\- *def* support



## [2021-11-12 07:25:31](https://github.com/leanprover-community/mathlib/commit/9e1e4f0)
feat(category_theory/sites/*): Dense subsite ([#9694](https://github.com/leanprover-community/mathlib/pull/9694))
Defined `cover_dense` functors as functors into sites such that each object can be covered by images of the functor.
Proved that for a `cover_dense` functor `G`, any morphisms of presheaves `G ⋙ ℱ ⟶ G ⋙ ℱ'` can be glued into a 
morphism `ℱ ⟶ ℱ'`.
#### Estimated changes
created src/category_theory/sites/dense_subsite.lean
- \+ *lemma* +
- \+ *lemma* presieve.in_cover_by_image
- \+ *lemma* ext
- \+ *lemma* functor_pullback_pushforward_covering
- \+ *lemma* sheaf_eq_amalgamation
- \+ *lemma* pushforward_family_compatible
- \+ *lemma* pushforward_family_apply
- \+ *lemma* app_hom_restrict
- \+ *lemma* app_hom_valid_glue
- \+ *lemma* sheaf_hom_restrict_eq
- \+ *lemma* sheaf_hom_eq
- \+ *lemma* iso_of_restrict_iso
- \+ *def* presieve.cover_by_image
- \+ *def* sieve.cover_by_image
- \+ *def* hom_over
- \+ *def* iso_over
- \+ *def* pushforward_family
- \+ *def* app_hom
- \+ *def* app_iso
- \+ *def* presheaf_hom
- \+ *def* presheaf_iso
- \+ *def* sheaf_iso
- \+ *def* sheaf_coyoneda_hom
- \+ *def* sheaf_yoneda_hom
- \+ *def* sheaf_hom
- \+ *def* presheaf_iso
- \+ *def* sheaf_iso
- \+ *def* restrict_hom_equiv_hom



## [2021-11-12 04:52:56](https://github.com/leanprover-community/mathlib/commit/6fd688b)
chore(measure_theory): move `mutually_singular` to a new file ([#10281](https://github.com/leanprover-community/mathlib/pull/10281))
#### Estimated changes
modified src/measure_theory/integral/lebesgue.lean

modified src/measure_theory/measure/measure_space.lean
- \- *lemma* mk
- \- *lemma* zero_right
- \- *lemma* symm
- \- *lemma* comm
- \- *lemma* zero_left
- \- *lemma* mono_ac
- \- *lemma* mono
- \- *lemma* sum_left
- \- *lemma* sum_right
- \- *lemma* add_left_iff
- \- *lemma* add_right_iff
- \- *lemma* add_left
- \- *lemma* add_right
- \- *lemma* smul
- \- *lemma* smul_nnreal
- \- *def* mutually_singular

created src/measure_theory/measure/mutually_singular.lean
- \+ *lemma* mk
- \+ *lemma* zero_right
- \+ *lemma* symm
- \+ *lemma* comm
- \+ *lemma* zero_left
- \+ *lemma* mono_ac
- \+ *lemma* mono
- \+ *lemma* sum_left
- \+ *lemma* sum_right
- \+ *lemma* add_left_iff
- \+ *lemma* add_right_iff
- \+ *lemma* add_left
- \+ *lemma* add_right
- \+ *lemma* smul
- \+ *lemma* smul_nnreal
- \+ *def* mutually_singular



## [2021-11-12 04:52:54](https://github.com/leanprover-community/mathlib/commit/d7e320e)
feat(category_theory/limits): Cone limiting iff terminal. ([#10266](https://github.com/leanprover-community/mathlib/pull/10266))
#### Estimated changes
created src/category_theory/limits/cone_category.lean
- \+ *lemma* is_limit.lift_cone_morphism_eq_is_terminal_from
- \+ *lemma* is_terminal.from_eq_lift_cone_morphism
- \+ *lemma* is_colimit.desc_cocone_morphism_eq_is_initial_to
- \+ *lemma* is_initial.to_eq_desc_cocone_morphism
- \+ *def* cone.is_limit_equiv_is_terminal
- \+ *def* is_limit.of_preserves_cone_terminal
- \+ *def* is_limit.of_reflects_cone_terminal
- \+ *def* cocone.is_colimit_equiv_is_initial
- \+ *def* is_colimit.of_preserves_cocone_initial
- \+ *def* is_colimit.of_reflects_cocone_initial

modified src/category_theory/limits/preserves/shapes/terminal.lean
- \+ *lemma* has_initial_of_has_initial_of_preserves_colimit
- \+ *lemma* preserves_initial.iso_hom
- \+ *def* is_terminal.is_terminal_obj
- \+ *def* is_terminal.is_terminal_of_obj
- \+ *def* is_colimit_map_cocone_empty_cocone_equiv
- \+ *def* is_initial.is_initial_obj
- \+ *def* is_initial.is_initial_of_obj
- \+ *def* is_colimit_of_has_initial_of_preserves_colimit
- \+ *def* preserves_initial.of_iso_comparison
- \+ *def* preserves_initial_of_is_iso
- \+ *def* preserves_initial_of_iso
- \+ *def* preserves_initial.iso
- \- *def* is_terminal_obj_of_is_terminal
- \- *def* is_terminal_of_is_terminal_obj



## [2021-11-12 03:51:22](https://github.com/leanprover-community/mathlib/commit/e5a79a7)
feat(analysis/normed_space/star): introduce C*-algebras ([#10145](https://github.com/leanprover-community/mathlib/pull/10145))
This PR introduces normed star rings/algebras and C*-rings/algebras, as well as a version of `star` bundled as a linear isometric equivalence.
#### Estimated changes
modified src/algebra/star/module.lean
- \+/\- *def* star_linear_equiv
- \+/\- *def* star_linear_equiv

created src/analysis/normed_space/star.lean
- \+ *lemma* cstar_ring.norm_self_mul_star
- \+ *lemma* cstar_ring.norm_star_mul_self'
- \+ *lemma* coe_starₗᵢ
- \+ *lemma* starₗᵢ_apply
- \+ *def* starₗᵢ



## [2021-11-12 00:55:58](https://github.com/leanprover-community/mathlib/commit/d6056ee)
feat(field_theory/splitting_field): add eval_root_derivative_of_split ([#10224](https://github.com/leanprover-community/mathlib/pull/10224))
From flt-regular.
#### Estimated changes
modified src/data/polynomial/derivative.lean
- \+ *lemma* eval_multiset_prod_X_sub_C_derivative
- \+ *theorem* derivative_prod

modified src/field_theory/splitting_field.lean
- \+ *lemma* aeval_root_derivative_of_splits



## [2021-11-12 00:19:41](https://github.com/leanprover-community/mathlib/commit/73b2b65)
feat(category_theory/limits/concrete_category): A lemma about concrete multiequalizers ([#10277](https://github.com/leanprover-community/mathlib/pull/10277))
#### Estimated changes
modified src/category_theory/limits/concrete_category.lean
- \+ *lemma* concrete.multiequalizer_ext



## [2021-11-11 23:18:38](https://github.com/leanprover-community/mathlib/commit/0b4c540)
feat(field_theory/separable): X^n - 1 is separable iff ↑n ≠ 0. ([#9779](https://github.com/leanprover-community/mathlib/pull/9779))
Most of the proof actually due to @Vierkantor!
#### Estimated changes
modified src/data/polynomial/monic.lean
- \+ *lemma* not_is_unit_X_pow_sub_one

modified src/field_theory/separable.lean
- \+ *lemma* separable_X_pow_sub_C_unit
- \+ *lemma* X_pow_sub_one_separable_iff



## [2021-11-11 19:35:48](https://github.com/leanprover-community/mathlib/commit/8cd5f0e)
chore(category_theory/isomorphisms): Adjust priority for is_iso.comp_is_iso ([#10276](https://github.com/leanprover-community/mathlib/pull/10276))
[See Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/iso.20to.20is_iso.20for.20types/near/261122457)
Given `f : X ≅ Y` with `X Y : Type u`, without this change, typeclass inference cannot deduce `is_iso f.hom` because `f.hom` is defeq to `(λ x, x) ≫ f.hom`, triggering a loop.
#### Estimated changes
modified src/category_theory/isomorphism.lean



## [2021-11-11 19:35:47](https://github.com/leanprover-community/mathlib/commit/d686025)
feat(linear_algebra/pi_tensor_product): add subsingleton_equiv ([#10274](https://github.com/leanprover-community/mathlib/pull/10274))
This is useful for constructing the tensor product of a single module, which we will ultimately need to show an isomorphism to `tensor_algebra`.
This also refactors `pempty_equiv` to use `is_empty`, which probably didn't exist at the time. This eliminates a surprising universe variable that was parameterizing `pempty`.
#### Estimated changes
modified src/linear_algebra/pi_tensor_product.lean
- \+ *lemma* is_empty_equiv_apply_tprod
- \+ *lemma* subsingleton_equiv_apply_tprod
- \+ *def* is_empty_equiv
- \+ *def* subsingleton_equiv
- \- *def* pempty_equiv



## [2021-11-11 19:35:45](https://github.com/leanprover-community/mathlib/commit/f99d638)
feat(measure_theory): integral over a family of pairwise a.e. disjoint sets ([#10268](https://github.com/leanprover-community/mathlib/pull/10268))
Also golf a few proofs
#### Estimated changes
modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* has_sum_integral_Union_of_null_inter
- \+ *lemma* integral_Union_of_null_inter

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* exists_subordinate_pairwise_disjoint



## [2021-11-11 19:35:44](https://github.com/leanprover-community/mathlib/commit/12c868a)
refactor(group_theory/complement): Generalize `card_mul` to from subgroups to subsets ([#10264](https://github.com/leanprover-community/mathlib/pull/10264))
Adds `is_complement.card_mul`, which generalizes `is_complement'.card_mul`.
#### Estimated changes
modified src/group_theory/complement.lean
- \+ *lemma* is_complement.card_mul



## [2021-11-11 19:35:42](https://github.com/leanprover-community/mathlib/commit/72ca0d3)
feat(linear_algebra/pi_tensor_prod): generalize actions and provide missing smul_comm_class and is_scalar_tower instance ([#10262](https://github.com/leanprover-community/mathlib/pull/10262))
Also squeezes some `simp`s.
#### Estimated changes
modified src/linear_algebra/pi_tensor_product.lean
- \+/\- *lemma* smul_tprod_coeff
- \+/\- *lemma* smul_tprod_coeff'
- \+/\- *lemma* smul_tprod_coeff
- \+/\- *lemma* smul_tprod_coeff'



## [2021-11-11 19:35:41](https://github.com/leanprover-community/mathlib/commit/c7f3e5c)
feat(group_theory/submonoid/membership): `exists_multiset_of_mem_closure` ([#10256](https://github.com/leanprover-community/mathlib/pull/10256))
Version of `exists_list_of_mem_closure` for `comm_monoid`.
#### Estimated changes
modified src/group_theory/submonoid/membership.lean
- \+ *lemma* exists_multiset_of_mem_closure



## [2021-11-11 19:35:40](https://github.com/leanprover-community/mathlib/commit/9a30dcf)
feat(data/finset/pairwise): Interaction of `set.pairwise_disjoint` with `finset` ([#10244](https://github.com/leanprover-community/mathlib/pull/10244))
This proves a few results about `set.pairwise_disjoint` and `finset` that couldn't go `data.set.pairwise` because of cyclic imports.
#### Estimated changes
created src/data/finset/pairwise.lean
- \+ *lemma* finset.pairwise_disjoint_range_singleton
- \+ *lemma* pairwise_disjoint.elim_finset
- \+ *lemma* pairwise_disjoint.image_finset_of_le
- \+ *lemma* pairwise_disjoint.bUnion_finset

modified src/data/set/pairwise.lean
- \+ *lemma* pairwise_disjoint.bUnion



## [2021-11-11 19:35:38](https://github.com/leanprover-community/mathlib/commit/820f8d7)
feat(group_theory/index): Index of `subgroup.map` ([#10232](https://github.com/leanprover-community/mathlib/pull/10232))
Proves `(H.map f).index = H.index`, assuming `function.surjective f` and `f.ker ≤ H`.
#### Estimated changes
modified src/group_theory/index.lean
- \+ *lemma* index_map
- \+ *lemma* index_map_dvd
- \+ *lemma* dvd_index_map
- \+ *lemma* index_map_eq



## [2021-11-11 19:35:37](https://github.com/leanprover-community/mathlib/commit/4b1a057)
feat(algebra/order/sub): An `add_group` has ordered subtraction ([#10225](https://github.com/leanprover-community/mathlib/pull/10225))
This wraps up `sub_le_iff_le_add` in an `has_ordered_sub` instance.
#### Estimated changes
modified src/algebra/order/group.lean

modified src/data/real/ennreal.lean



## [2021-11-11 19:35:36](https://github.com/leanprover-community/mathlib/commit/a9c3ab5)
feat(data/polynomial): assorted lemmas on division and gcd of polynomials ([#9600](https://github.com/leanprover-community/mathlib/pull/9600))
This PR provides a couple of lemmas involving the division and gcd operators of polynomials that I needed for [#9563](https://github.com/leanprover-community/mathlib/pull/9563). The ones that generalized to `euclidean_domain` and/or `gcd_monoid` are provided in the respective files.
#### Estimated changes
modified src/algebra/euclidean_domain.lean
- \+ *lemma* div_one
- \+ *lemma* div_dvd_of_dvd
- \+ *lemma* mul_div_mul_cancel

modified src/data/polynomial/field_division.lean
- \+ *lemma* leading_coeff_div
- \+ *lemma* div_C_mul
- \+ *lemma* C_mul_dvd
- \+ *lemma* dvd_C_mul

modified src/ring_theory/euclidean_domain.lean
- \+ *lemma* left_div_gcd_ne_zero
- \+ *lemma* right_div_gcd_ne_zero

modified src/ring_theory/polynomial/content.lean
- \+ *lemma* degree_gcd_le_left
- \+ *lemma* degree_gcd_le_right



## [2021-11-11 19:02:03](https://github.com/leanprover-community/mathlib/commit/01e7b20)
feat(analysis/subadditive): prove that, if u_n is subadditive, then u_n / n converges. ([#10258](https://github.com/leanprover-community/mathlib/pull/10258))
#### Estimated changes
created src/analysis/subadditive.lean
- \+ *lemma* lim_le_div
- \+ *lemma* apply_mul_add_le
- \+ *lemma* eventually_div_lt_of_div_lt
- \+ *theorem* tendsto_lim
- \+ *def* subadditive



## [2021-11-11 14:48:45](https://github.com/leanprover-community/mathlib/commit/4df3cd7)
chore(analysis/special_functions/complex/log): move results about derivatives to a new file ([#10117](https://github.com/leanprover-community/mathlib/pull/10117))
#### Estimated changes
modified src/analysis/special_functions/complex/log.lean
- \+ *lemma* continuous_at_clog
- \- *lemma* has_strict_deriv_at_log
- \- *lemma* has_strict_fderiv_at_log_real
- \- *lemma* times_cont_diff_at_log
- \- *lemma* has_strict_fderiv_at.clog
- \- *lemma* has_strict_deriv_at.clog
- \- *lemma* has_strict_deriv_at.clog_real
- \- *lemma* has_fderiv_at.clog
- \- *lemma* has_deriv_at.clog
- \- *lemma* has_deriv_at.clog_real
- \- *lemma* differentiable_at.clog
- \- *lemma* has_fderiv_within_at.clog
- \- *lemma* has_deriv_within_at.clog
- \- *lemma* has_deriv_within_at.clog_real
- \- *lemma* differentiable_within_at.clog
- \- *lemma* differentiable_on.clog
- \- *lemma* differentiable.clog
- \- *def* exp_local_homeomorph

created src/analysis/special_functions/complex/log_deriv.lean
- \+ *lemma* has_strict_deriv_at_log
- \+ *lemma* has_strict_fderiv_at_log_real
- \+ *lemma* times_cont_diff_at_log
- \+ *lemma* has_strict_fderiv_at.clog
- \+ *lemma* has_strict_deriv_at.clog
- \+ *lemma* has_strict_deriv_at.clog_real
- \+ *lemma* has_fderiv_at.clog
- \+ *lemma* has_deriv_at.clog
- \+ *lemma* has_deriv_at.clog_real
- \+ *lemma* differentiable_at.clog
- \+ *lemma* has_fderiv_within_at.clog
- \+ *lemma* has_deriv_within_at.clog
- \+ *lemma* has_deriv_within_at.clog_real
- \+ *lemma* differentiable_within_at.clog
- \+ *lemma* differentiable_on.clog
- \+ *lemma* differentiable.clog
- \+ *def* exp_local_homeomorph

modified src/analysis/special_functions/pow.lean

modified src/analysis/special_functions/trigonometric/complex.lean



## [2021-11-11 14:04:29](https://github.com/leanprover-community/mathlib/commit/6e268cd)
chore(probability_theory/notation): change `volume` to `measure_theory.measure.volume` ([#10272](https://github.com/leanprover-community/mathlib/pull/10272))
#### Estimated changes
modified src/probability_theory/notation.lean



## [2021-11-11 13:22:36](https://github.com/leanprover-community/mathlib/commit/270c644)
feat(measure_theory): add `ae_measurable.sum_measure` ([#10271](https://github.com/leanprover-community/mathlib/pull/10271))
Also add a few supporting lemmas.
#### Estimated changes
modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_of_subsingleton_codomain

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* restrict_Union_apply_ae
- \+/\- *lemma* restrict_Union_apply
- \+ *lemma* sum_apply_eq_zero
- \+ *lemma* sum_apply_eq_zero'
- \+ *lemma* ae_sum_iff
- \+ *lemma* ae_sum_iff'
- \+ *lemma* ae_sum_eq
- \+ *lemma* restrict_Union_ae
- \+ *lemma* ae_measurable_of_subsingleton_codomain
- \+ *lemma* sum_measure
- \+ *lemma* _root_.ae_measurable_sum_measure_iff
- \+ *lemma* _root_.ae_measurable_add_measure_iff
- \+ *lemma* _root_.ae_measurable_Union_iff
- \+/\- *lemma* restrict_Union_apply
- \- *lemma* ae_measurable_add_measure_iff



## [2021-11-11 11:44:13](https://github.com/leanprover-community/mathlib/commit/c062d9e)
feat(*): more bundled versions of `(fin 2 → α) ≃ (α × α)` ([#10214](https://github.com/leanprover-community/mathlib/pull/10214))
Also ensure that the inverse function uses vector notation when possible.
#### Estimated changes
modified src/data/equiv/fin.lean
- \+/\- *def* fin_two_arrow_equiv
- \+/\- *def* fin_two_arrow_equiv

modified src/linear_algebra/pi.lean
- \+ *def* pi_fin_two
- \+ *def* fin_two_arrow

modified src/topology/algebra/module.lean
- \+ *def* simps.apply
- \+ *def* simps.coe
- \+ *def* simps.apply
- \+ *def* simps.symm_apply
- \+ *def* pi_fin_two
- \+ *def* fin_two_arrow

modified src/topology/homeomorph.lean
- \+ *def* {u}
- \+ *def* fin_two_arrow



## [2021-11-11 10:26:15](https://github.com/leanprover-community/mathlib/commit/e4a882d)
feat(measure_theory): a file about null measurable sets/functions ([#10231](https://github.com/leanprover-community/mathlib/pull/10231))
* Move definitions and lemmas about `null_measurable` to a new file.
* Redefine, rename, review API.
#### Estimated changes
modified docs/overview.yaml

modified src/algebra/support.lean
- \+ *lemma* mul_support_eq_preimage

modified src/measure_theory/integral/set_integral.lean

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* to_measure_apply₀
- \+ *lemma* restrict_apply₀
- \+ *lemma* null_measurable_set.mono_ac
- \+ *lemma* null_measurable_set.mono
- \+/\- *lemma* ae_measurable_iff_measurable
- \- *lemma* measure_Union
- \- *lemma* restrict_apply_of_null_measurable_set
- \- *lemma* measurable.ae_eq
- \+/\- *lemma* ae_measurable_iff_measurable
- \- *theorem* measure_theory.measure.is_complete_iff
- \- *theorem* measure_theory.measure.is_complete.out
- \- *theorem* null_measurable_set_iff
- \- *theorem* null_measurable_set_measure_eq
- \- *theorem* measurable_set.null_measurable_set
- \- *theorem* null_measurable_set_of_complete
- \- *theorem* null_measurable_set.union_null
- \- *theorem* null_null_measurable_set
- \- *theorem* null_measurable_set.Union_nat
- \- *theorem* measurable_set.diff_null
- \- *theorem* null_measurable_set.diff_null
- \- *theorem* null_measurable_set.compl
- \- *theorem* null_measurable_set_iff_ae
- \- *theorem* null_measurable_set_iff_sandwich
- \- *def* null_measurable_set
- \- *def* null_measurable
- \- *def* completion

modified src/measure_theory/measure/measure_space_def.lean
- \+/\- *lemma* subset_to_measurable
- \+ *lemma* ae_le_to_measurable
- \+/\- *lemma* measurable_set_to_measurable
- \+/\- *lemma* measure_to_measurable
- \+/\- *lemma* subset_to_measurable
- \+/\- *lemma* measurable_set_to_measurable
- \+/\- *lemma* measure_to_measurable
- \+/\- *def* to_measurable
- \+/\- *def* to_measurable

created src/measure_theory/measure/null_measurable.lean
- \+ *lemma* _root_.measurable_set.null_measurable_set
- \+ *lemma* null_measurable_set_empty
- \+ *lemma* null_measurable_set_univ
- \+ *lemma* of_null
- \+ *lemma* compl
- \+ *lemma* of_compl
- \+ *lemma* compl_iff
- \+ *lemma* of_subsingleton
- \+ *lemma* Union_Prop
- \+ *lemma* Union_fintype
- \+ *lemma* Inter_Prop
- \+ *lemma* Inter_fintype
- \+ *lemma* exists_measurable_superset_ae_eq
- \+ *lemma* to_measurable_ae_eq
- \+ *lemma* compl_to_measurable_compl_ae_eq
- \+ *lemma* exists_measurable_subset_ae_eq
- \+ *lemma* measure_Union
- \+ *lemma* measure_Union₀
- \+ *lemma* measure_union₀
- \+ *lemma* null_measurable_set_singleton
- \+ *lemma* null_measurable_set_insert
- \+ *lemma* null_measurable_set_eq
- \+ *lemma* _root_.set.finite.null_measurable_set_bUnion
- \+ *lemma* _root_.finset.null_measurable_set_bUnion
- \+ *lemma* _root_.set.finite.null_measurable_set_sUnion
- \+ *lemma* _root_.set.finite.null_measurable_set_bInter
- \+ *lemma* _root_.finset.null_measurable_set_bInter
- \+ *lemma* _root_.set.finite.null_measurable_set_sInter
- \+ *lemma* null_measurable_set_to_measurable
- \+ *lemma* measurable.comp_null_measurable
- \+ *lemma* null_measurable.congr
- \+ *lemma* _root_.measurable.congr_ae
- \+ *lemma* coe_completion
- \+ *lemma* completion_apply
- \+ *theorem* measure.is_complete_iff
- \+ *theorem* measure.is_complete.out
- \+ *theorem* measurable_set_of_null
- \+ *theorem* null_measurable_set.measurable_of_complete
- \+ *theorem* null_measurable.measurable_of_complete
- \+ *def* null_measurable_space
- \+ *def* null_measurable_set
- \+ *def* null_measurable
- \+ *def* completion



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
modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean

modified src/algebra/order/archimedean.lean
- \+ *theorem* rat.floor_cast
- \+ *theorem* rat.ceil_cast
- \+ *theorem* rat.round_cast
- \+ *theorem* rat.cast_fract
- \- *theorem* rat.cast_floor
- \- *theorem* rat.cast_ceil
- \- *theorem* rat.cast_round

modified src/algebra/order/floor.lean
- \+/\- *lemma* floor_eq_zero
- \+ *lemma* floor_eq_iff'
- \+ *lemma* preimage_floor_zero
- \+ *lemma* preimage_floor_of_ne_zero
- \+ *lemma* ceil_eq_iff
- \+ *lemma* preimage_ceil_zero
- \+ *lemma* preimage_ceil_of_ne_zero
- \+ *lemma* preimage_floor_singleton
- \+ *lemma* self_sub_floor
- \+/\- *lemma* fract_add_int
- \+/\- *lemma* fract_sub_int
- \+ *lemma* fract_int_add
- \+ *lemma* preimage_fract
- \+ *lemma* image_fract
- \+ *lemma* preimage_ceil_singleton
- \+/\- *lemma* floor_eq_zero
- \+/\- *lemma* fract_add_int
- \+/\- *lemma* fract_sub_int

created src/measure_theory/function/floor.lean
- \+ *lemma* int.measurable_floor
- \+ *lemma* measurable.floor
- \+ *lemma* int.measurable_ceil
- \+ *lemma* measurable.ceil
- \+ *lemma* measurable_fract
- \+ *lemma* measurable.fract
- \+ *lemma* measurable_set.image_fract
- \+ *lemma* nat.measurable_floor
- \+ *lemma* measurable.nat_floor
- \+ *lemma* nat.measurable_ceil
- \+ *lemma* measurable.nat_ceil

modified src/number_theory/zsqrtd/gaussian_int.lean



## [2021-11-11 07:23:55](https://github.com/leanprover-community/mathlib/commit/8c1fa70)
feat(category_theory/limits/concrete_category): Some lemmas about filtered colimits ([#10270](https://github.com/leanprover-community/mathlib/pull/10270))
This PR adds some lemmas about (filtered) colimits in concrete categories which are preserved under the forgetful functor.
This will be used later for the sheafification construction.
#### Estimated changes
modified src/category_theory/limits/concrete_category.lean
- \+ *lemma* concrete.is_colimit_rep_eq_of_exists
- \+ *lemma* concrete.colimit_rep_eq_of_exists
- \+ *lemma* concrete.is_colimit_exists_of_rep_eq
- \+ *lemma* concrete.colimit_exists_of_rep_eq
- \+ *theorem* concrete.is_colimit_rep_eq_iff_exists
- \+ *theorem* concrete.colimit_rep_eq_iff_exists



## [2021-11-10 21:52:09](https://github.com/leanprover-community/mathlib/commit/dfa7363)
feat(analysis/normed_space/finite_dimension): finite-dimensionality of spaces of continuous linear map ([#10259](https://github.com/leanprover-community/mathlib/pull/10259))
#### Estimated changes
modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* inner_self_eq_norm_mul_norm
- \+ *lemma* inner_self_eq_norm_mul_norm
- \+/\- *lemma* inner_self_eq_norm_sq
- \+ *lemma* real_inner_self_eq_norm_mul_norm
- \+/\- *lemma* real_inner_self_eq_norm_sq
- \+/\- *lemma* inner_self_eq_norm_sq
- \+/\- *lemma* inner_self_eq_norm_sq
- \+/\- *lemma* real_inner_self_eq_norm_sq

modified src/analysis/inner_product_space/calculus.lean

modified src/analysis/inner_product_space/dual.lean
- \+ *lemma* to_dual_symm_apply

modified src/analysis/inner_product_space/rayleigh.lean

modified src/analysis/normed_space/dual.lean

modified src/analysis/normed_space/finite_dimension.lean

modified src/analysis/quaternion.lean

modified src/geometry/euclidean/basic.lean

modified src/geometry/euclidean/circumcenter.lean

modified src/geometry/euclidean/triangle.lean

modified src/geometry/manifold/instances/sphere.lean

modified src/topology/algebra/module.lean
- \+ *def* coe_lm



## [2021-11-10 20:44:38](https://github.com/leanprover-community/mathlib/commit/3c2bc2e)
lint(scripts/lint-style.py): add indentation linter ([#10257](https://github.com/leanprover-community/mathlib/pull/10257))
#### Estimated changes
modified scripts/lint-style.py
- \+ *def* indent_check(lines,



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
modified src/algebra/associated.lean

modified src/algebra/module/submodule_lattice.lean

modified src/algebra/order/monoid.lean

modified src/algebra/order/nonneg.lean
- \+ *lemma* bot_eq

modified src/algebra/tropical/basic.lean
- \+/\- *lemma* le_zero
- \+/\- *lemma* le_zero

modified src/analysis/box_integral/partition/basic.lean

modified src/analysis/convex/cone.lean

modified src/analysis/normed/group/basic.lean

modified src/analysis/normed_space/enorm.lean

modified src/analysis/specific_limits.lean

modified src/category_theory/sites/pretopology.lean

modified src/category_theory/subobject/lattice.lean

modified src/combinatorics/colex.lean

modified src/control/lawful_fix.lean

modified src/data/equiv/denumerable.lean

modified src/data/finset/basic.lean
- \+/\- *lemma* bot_eq_empty
- \+/\- *lemma* bot_eq_empty

modified src/data/finset/locally_finite.lean

modified src/data/finsupp/lattice.lean

modified src/data/fintype/basic.lean

modified src/data/multiset/basic.lean

modified src/data/nat/enat.lean

modified src/data/part.lean

modified src/data/pequiv.lean

modified src/data/pnat/basic.lean

modified src/data/real/ereal.lean

modified src/data/semiquot.lean

modified src/data/set/intervals/basic.lean
- \+/\- *lemma* Ici_top
- \+/\- *lemma* Iic_bot
- \+/\- *lemma* Ici_bot
- \+/\- *lemma* Ici_top
- \+/\- *lemma* Iic_bot
- \+/\- *lemma* Ici_bot
- \+/\- *def* Iic_top
- \+/\- *def* Ici_bot
- \+/\- *def* Iic_top
- \+/\- *def* Ici_bot

modified src/data/set/lattice.lean

modified src/data/setoid/basic.lean

modified src/field_theory/adjoin.lean

modified src/geometry/manifold/charted_space.lean

modified src/linear_algebra/linear_pmap.lean

modified src/measure_theory/integral/bochner.lean

modified src/measure_theory/integral/lebesgue.lean

modified src/measure_theory/measure/outer_measure.lean
- \+ *theorem* coe_bot

modified src/order/atoms.lean
- \+/\- *lemma* is_atom_iff
- \+/\- *lemma* is_coatom_iff
- \+/\- *lemma* is_simple_lattice_iff
- \+/\- *lemma* is_simple_lattice
- \+/\- *lemma* is_atomic_iff
- \+/\- *lemma* is_coatomic_iff
- \+/\- *lemma* is_atom_iff
- \+/\- *lemma* is_coatom_iff
- \+/\- *lemma* is_simple_lattice_iff
- \+/\- *lemma* is_simple_lattice
- \+/\- *lemma* is_atomic_iff
- \+/\- *lemma* is_coatomic_iff

modified src/order/bounded_lattice.lean
- \+/\- *lemma* strict_mono.maximal_preimage_top
- \+/\- *lemma* strict_mono.minimal_preimage_bot
- \+/\- *lemma* get_or_else_bot_le_iff
- \+/\- *lemma* strict_mono.maximal_preimage_top
- \+/\- *lemma* strict_mono.minimal_preimage_bot
- \+/\- *lemma* get_or_else_bot_le_iff
- \+/\- *theorem* le_top
- \+/\- *theorem* not_top_lt
- \+/\- *theorem* order_top.ext_top
- \+/\- *theorem* order_top.ext
- \+/\- *theorem* bot_le
- \+/\- *theorem* not_lt_bot
- \+/\- *theorem* order_bot.ext_bot
- \+/\- *theorem* order_bot.ext
- \+/\- *theorem* le_top
- \+/\- *theorem* not_top_lt
- \+/\- *theorem* order_top.ext_top
- \+/\- *theorem* order_top.ext
- \+/\- *theorem* bot_le
- \+/\- *theorem* not_lt_bot
- \+/\- *theorem* order_bot.ext_bot
- \+/\- *theorem* order_bot.ext

modified src/order/bounds.lean
- \+/\- *lemma* is_greatest_univ
- \+/\- *lemma* order_top.upper_bounds_univ
- \+/\- *lemma* is_lub_univ
- \+/\- *lemma* order_bot.lower_bounds_univ
- \+/\- *lemma* is_least_univ
- \+/\- *lemma* is_glb_univ
- \+/\- *lemma* is_glb_empty
- \+/\- *lemma* is_lub_empty
- \+/\- *lemma* is_greatest_univ
- \+/\- *lemma* order_top.upper_bounds_univ
- \+/\- *lemma* is_lub_univ
- \+/\- *lemma* order_bot.lower_bounds_univ
- \+/\- *lemma* is_least_univ
- \+/\- *lemma* is_glb_univ
- \+/\- *lemma* is_glb_empty
- \+/\- *lemma* is_lub_empty

modified src/order/category/NonemptyFinLinOrd.lean

modified src/order/closure.lean
- \+/\- *lemma* closure_top
- \+/\- *lemma* closure_top

modified src/order/compactly_generated.lean

modified src/order/complete_lattice.lean

modified src/order/conditionally_complete_lattice.lean

modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* order_top.at_top_eq
- \+/\- *lemma* order_bot.at_bot_eq
- \+/\- *lemma* tendsto_at_top_pure
- \+/\- *lemma* tendsto_at_bot_pure
- \+/\- *lemma* order_top.at_top_eq
- \+/\- *lemma* order_bot.at_bot_eq
- \+/\- *lemma* tendsto_at_top_pure
- \+/\- *lemma* tendsto_at_bot_pure

modified src/order/filter/basic.lean
- \+/\- *lemma* eventually.ne_top_of_lt
- \+/\- *lemma* eventually.lt_top_of_ne
- \+/\- *lemma* eventually.lt_top_iff_ne_top
- \+/\- *lemma* eventually.ne_top_of_lt
- \+/\- *lemma* eventually.lt_top_of_ne
- \+/\- *lemma* eventually.lt_top_iff_ne_top

modified src/order/filter/germ.lean

modified src/order/galois_connection.lean
- \+/\- *def* galois_connection.lift_order_bot
- \+/\- *def* lift_order_top
- \+/\- *def* galois_connection.lift_order_top
- \+/\- *def* lift_order_bot
- \+/\- *def* with_bot.gi_get_or_else_bot
- \+/\- *def* galois_connection.lift_order_bot
- \+/\- *def* lift_order_top
- \+/\- *def* galois_connection.lift_order_top
- \+/\- *def* lift_order_bot
- \+/\- *def* with_bot.gi_get_or_else_bot

modified src/order/ideal.lean

modified src/order/lattice_intervals.lean
- \+/\- *lemma* coe_bot
- \+/\- *lemma* coe_top
- \+/\- *lemma* coe_bot
- \+/\- *lemma* coe_top

modified src/order/liminf_limsup.lean
- \+/\- *lemma* is_cobounded_le_of_bot
- \+/\- *lemma* is_cobounded_ge_of_top
- \+/\- *lemma* is_bounded_le_of_top
- \+/\- *lemma* is_bounded_ge_of_bot
- \+/\- *lemma* is_cobounded_le_of_bot
- \+/\- *lemma* is_cobounded_ge_of_top
- \+/\- *lemma* is_bounded_le_of_top
- \+/\- *lemma* is_bounded_ge_of_bot

modified src/order/locally_finite.lean

modified src/order/pfilter.lean

modified src/order/preorder_hom.lean

modified src/order/rel_iso.lean
- \+/\- *lemma* order_iso.map_bot'
- \+/\- *lemma* order_iso.map_bot
- \+/\- *lemma* order_iso.map_top'
- \+/\- *lemma* order_iso.map_top
- \+/\- *lemma* order_iso.map_bot'
- \+/\- *lemma* order_iso.map_bot
- \+/\- *lemma* order_iso.map_top'
- \+/\- *lemma* order_iso.map_top

modified src/order/succ_pred.lean

modified src/order/symm_diff.lean

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/noetherian.lean

modified src/set_theory/cardinal.lean

modified src/tactic/interval_cases.lean

modified src/topology/algebra/open_subgroup.lean

modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* nhds_top_order
- \+/\- *lemma* nhds_bot_order
- \+/\- *lemma* tendsto_nhds_top_mono
- \+/\- *lemma* tendsto_nhds_bot_mono
- \+/\- *lemma* tendsto_nhds_top_mono'
- \+/\- *lemma* tendsto_nhds_bot_mono'
- \+/\- *lemma* nhds_top_order
- \+/\- *lemma* nhds_bot_order
- \+/\- *lemma* tendsto_nhds_top_mono
- \+/\- *lemma* tendsto_nhds_bot_mono
- \+/\- *lemma* tendsto_nhds_top_mono'
- \+/\- *lemma* tendsto_nhds_bot_mono'

modified src/topology/basic.lean
- \+/\- *lemma* order_top.tendsto_at_top_nhds
- \+/\- *lemma* order_top.tendsto_at_top_nhds

modified src/topology/category/Top/open_nhds.lean

modified src/topology/discrete_quotient.lean

modified src/topology/metric_space/emetric_space.lean



## [2021-11-10 16:26:10](https://github.com/leanprover-community/mathlib/commit/cd5cb44)
chore(set_theory/cardinal_ordinal): golf some proofs ([#10260](https://github.com/leanprover-community/mathlib/pull/10260))
#### Estimated changes
modified src/set_theory/cardinal_ordinal.lean



## [2021-11-10 14:52:29](https://github.com/leanprover-community/mathlib/commit/8aadbcb)
feat(linear_algebra/*_algebra): add some simp lemmas about the algebra map and generators of free constructions ([#10247](https://github.com/leanprover-community/mathlib/pull/10247))
These are quite repetitive, but I'm not sure how to generalize
#### Estimated changes
modified src/algebra/free_algebra.lean
- \+ *lemma* algebra_map_inj
- \+ *lemma* algebra_map_eq_zero_iff
- \+ *lemma* algebra_map_eq_one_iff
- \+ *lemma* ι_inj
- \+ *lemma* ι_ne_algebra_map
- \+ *lemma* ι_ne_zero
- \+ *lemma* ι_ne_one

modified src/linear_algebra/exterior_algebra.lean
- \+ *lemma* algebra_map_inj
- \+ *lemma* algebra_map_eq_zero_iff
- \+ *lemma* algebra_map_eq_one_iff
- \+ *lemma* to_triv_sq_zero_ext_ι
- \+ *lemma* ι_inj
- \+ *lemma* ι_eq_zero_iff
- \+ *lemma* ι_eq_algebra_map_iff
- \+ *lemma* ι_ne_one
- \+ *lemma* ι_range_disjoint_one
- \+ *def* to_triv_sq_zero_ext

modified src/linear_algebra/tensor_algebra.lean
- \+ *lemma* algebra_map_inj
- \+ *lemma* algebra_map_eq_zero_iff
- \+ *lemma* algebra_map_eq_one_iff
- \+ *lemma* to_triv_sq_zero_ext_ι
- \+ *lemma* ι_inj
- \+ *lemma* ι_eq_zero_iff
- \+ *lemma* ι_eq_algebra_map_iff
- \+ *lemma* ι_ne_one
- \+ *lemma* ι_range_disjoint_one
- \+ *def* to_triv_sq_zero_ext



## [2021-11-10 14:52:28](https://github.com/leanprover-community/mathlib/commit/543fcef)
chore(algebra/group_power/lemmas): minimize imports ([#10246](https://github.com/leanprover-community/mathlib/pull/10246))
Most of these were imported transitively anyway, but `data.list.basic` is unneeded.
#### Estimated changes
modified src/algebra/group_power/lemmas.lean



## [2021-11-10 14:52:26](https://github.com/leanprover-community/mathlib/commit/444b596)
doc(ring_theory/norm) `norm_eq_prod_embeddings` docstring ([#10242](https://github.com/leanprover-community/mathlib/pull/10242))
#### Estimated changes
modified src/ring_theory/norm.lean



## [2021-11-10 14:52:24](https://github.com/leanprover-community/mathlib/commit/bbbefe4)
feat(measure_theory/constructions/{pi,prod}): drop some measurability assumptions ([#10241](https://github.com/leanprover-community/mathlib/pull/10241))
Some lemmas (most notably `prod_prod` and `pi_pi`) are true for non-measurable sets as well.
#### Estimated changes
modified src/data/equiv/list.lean
- \+/\- *theorem* mem_sorted_univ
- \+/\- *theorem* length_sorted_univ
- \+/\- *theorem* sorted_univ_nodup
- \+ *theorem* sorted_univ_to_finset
- \+/\- *theorem* mem_sorted_univ
- \+/\- *theorem* length_sorted_univ
- \+/\- *theorem* sorted_univ_nodup

modified src/measure_theory/constructions/pi.lean
- \+/\- *lemma* pi'_pi
- \+ *lemma* pi_pi_aux
- \+ *lemma* pi'_eq_pi
- \+/\- *lemma* pi_pi
- \+/\- *lemma* pi_univ
- \+/\- *lemma* pi_ball
- \+/\- *lemma* pi_closed_ball
- \+/\- *lemma* pi_unique_eq_map
- \+/\- *lemma* map_fun_unique
- \- *lemma* tprod_tprod_le
- \+/\- *lemma* pi'_pi
- \- *lemma* pi'_pi_le
- \+/\- *lemma* pi_pi
- \+/\- *lemma* pi_univ
- \+/\- *lemma* pi_ball
- \+/\- *lemma* pi_closed_ball
- \+/\- *lemma* pi_unique_eq_map
- \+/\- *lemma* map_fun_unique

modified src/measure_theory/constructions/prod.lean
- \+/\- *lemma* prod_prod
- \+/\- *lemma* prod_restrict
- \+/\- *lemma* restrict_prod_eq_prod_univ
- \+ *lemma* set_integral_prod
- \+/\- *lemma* prod_prod
- \- *lemma* prod_prod_le
- \+/\- *lemma* prod_restrict
- \+/\- *lemma* restrict_prod_eq_prod_univ

modified src/measure_theory/group/arithmetic.lean
- \+ *lemma* measurable_set.inv

modified src/measure_theory/group/prod.lean
- \+ *lemma* quasi_measure_preserving_inv
- \+/\- *lemma* measure_inv_null
- \+/\- *lemma* measure_mul_right_null
- \+/\- *lemma* measure_mul_right_ne_zero
- \- *lemma* measure_null_of_measure_inv_null
- \+/\- *lemma* measure_inv_null
- \+/\- *lemma* measure_mul_right_null
- \+/\- *lemma* measure_mul_right_ne_zero

modified src/measure_theory/measure/haar_lebesgue.lean

modified src/measure_theory/measure/hausdorff.lean

modified src/measure_theory/measure/lebesgue.lean

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* preimage_null



## [2021-11-10 14:52:23](https://github.com/leanprover-community/mathlib/commit/eadd440)
feat(group_theory/index): `card_mul_index` ([#10228](https://github.com/leanprover-community/mathlib/pull/10228))
Proves `nat.card H * H.index = nat.card G` as the special case of `K.relindex H * H.index = K.index` when `K = ⊥`.
#### Estimated changes
modified src/group_theory/index.lean
- \+ *lemma* card_mul_index



## [2021-11-10 14:52:21](https://github.com/leanprover-community/mathlib/commit/2b57ee7)
fix(*): fix many indentation mistakes ([#10163](https://github.com/leanprover-community/mathlib/pull/10163))
#### Estimated changes
modified archive/100-theorems-list/82_cubing_a_cube.lean

modified archive/miu_language/decision_nec.lean

modified src/algebra/category/CommRing/pushout.lean

modified src/algebra/geom_sum.lean

modified src/algebraic_geometry/Spec.lean

modified src/analysis/calculus/specific_functions.lean

modified src/analysis/convex/combination.lean

modified src/analysis/convex/function.lean

modified src/analysis/inner_product_space/basic.lean

modified src/data/buffer/parser/basic.lean

modified src/data/fin/basic.lean

modified src/data/list/nodup.lean

modified src/data/list/rotate.lean

modified src/data/list/tfae.lean

modified src/data/mv_polynomial/rename.lean

modified src/data/nat/digits.lean

modified src/data/polynomial/eval.lean

modified src/data/rbmap/default.lean

modified src/data/rbtree/basic.lean

modified src/data/rbtree/insert.lean

modified src/data/rbtree/min_max.lean

modified src/data/real/cau_seq.lean

modified src/data/real/pi/bounds.lean

modified src/data/stream/init.lean

modified src/data/vector/basic.lean

modified src/field_theory/primitive_element.lean

modified src/group_theory/monoid_localization.lean

modified src/group_theory/perm/list.lean

modified src/group_theory/perm/support.lean

modified src/group_theory/specific_groups/dihedral.lean

modified src/linear_algebra/dimension.lean

modified src/measure_theory/function/lp_space.lean

modified src/number_theory/arithmetic_function.lean

modified src/number_theory/bernoulli_polynomials.lean

modified src/number_theory/fermat4.lean

modified src/number_theory/padics/padic_norm.lean

modified src/number_theory/pythagorean_triples.lean

modified src/number_theory/quadratic_reciprocity.lean

modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/polynomial/basic.lean

modified src/ring_theory/polynomial/symmetric.lean

modified src/ring_theory/power_series/basic.lean

modified src/ring_theory/tensor_product.lean

modified src/set_theory/game.lean

modified src/tactic/omega/int/dnf.lean

modified src/topology/algebra/valuation.lean

modified src/topology/sheaves/forget.lean



## [2021-11-10 14:52:20](https://github.com/leanprover-community/mathlib/commit/f41854e)
feat(ring_theory/ideal/over): algebra structure on R/p → S/P for `P` lying over `p` ([#9858](https://github.com/leanprover-community/mathlib/pull/9858))
This PR shows `P` lies over `p` if there is an injective map completing the square `R/p ← R —f→ S → S/P`, and conversely that there is a (not necessarily injective, since `f` doesn't have to be) map completing the square if `P` lies over `p`. Then we specialize this to the case where `P = map f p` to provide an `algebra p.quotient (map f p).quotient` instance.
This algebra instance is useful if you want to study the extension `R → S` locally at `p`, e.g. to show `R/p : S/pS` has the same dimension as `Frac(R) : Frac(S)` if `p` is prime.
#### Estimated changes
modified src/ring_theory/ideal/over.lean
- \+ *lemma* comap_eq_of_scalar_tower_quotient
- \+ *lemma* quotient.algebra_map_quotient_map_quotient
- \+ *lemma* quotient.mk_smul_mk_quotient_map_quotient
- \+ *def* quotient.algebra_quotient_of_le_comap



## [2021-11-10 14:52:18](https://github.com/leanprover-community/mathlib/commit/e1fea3a)
feat(ring_theory/ideal): the product and infimum of principal ideals ([#9852](https://github.com/leanprover-community/mathlib/pull/9852))
Three useful lemmas for applying the Chinese remainder theorem when an ideal is generated by one, non-prime, element.
#### Estimated changes
modified src/algebra/algebra/operations.lean
- \+ *lemma* prod_span
- \+ *lemma* prod_span_singleton

modified src/algebra/module/submodule_lattice.lean
- \+ *theorem* finset_inf_coe
- \+ *theorem* mem_finset_inf

modified src/algebra/pointwise.lean
- \+ *lemma* finset_prod_singleton

modified src/ring_theory/ideal/operations.lean
- \+ *lemma* prod_span
- \+ *lemma* prod_span_singleton
- \+ *lemma* finset_inf_span_singleton
- \+ *lemma* infi_span_singleton

modified src/ring_theory/multiplicity.lean



## [2021-11-10 13:12:51](https://github.com/leanprover-community/mathlib/commit/bfd3a89)
doc(algebra/ring/basic): fix typo ([#10250](https://github.com/leanprover-community/mathlib/pull/10250))
#### Estimated changes
modified src/algebra/ring/basic.lean



## [2021-11-10 06:43:42](https://github.com/leanprover-community/mathlib/commit/18412ef)
feat(data/nat/cast): Cast of natural division is less than division of casts ([#10251](https://github.com/leanprover-community/mathlib/pull/10251))
#### Estimated changes
modified src/data/nat/cast.lean
- \+ *lemma* cast_div_le



## [2021-11-10 02:49:27](https://github.com/leanprover-community/mathlib/commit/3f173e1)
feat(group_theory/complement): iff-lemmas for when bottom and top subgroups are complementary ([#10143](https://github.com/leanprover-community/mathlib/pull/10143))
Adds iff lemmas for when bottom and top subgroups are complementary.
#### Estimated changes
modified src/data/set/basic.lean
- \+/\- *lemma* eq_singleton_iff_unique_mem
- \+/\- *lemma* eq_singleton_iff_nonempty_unique_mem
- \+ *lemma* exists_eq_singleton_iff_nonempty_unique_mem
- \+/\- *lemma* eq_singleton_iff_unique_mem
- \+/\- *lemma* eq_singleton_iff_nonempty_unique_mem

modified src/group_theory/complement.lean
- \+/\- *lemma* is_complement_top_singleton
- \+/\- *lemma* is_complement_singleton_top
- \+ *lemma* is_complement_singleton_left
- \+ *lemma* is_complement_singleton_right
- \+ *lemma* is_complement_top_left
- \+ *lemma* is_complement_top_right
- \+ *lemma* is_complement'_top_bot
- \+ *lemma* is_complement'_bot_top
- \+ *lemma* is_complement'_bot_left
- \+ *lemma* is_complement'_bot_right
- \+ *lemma* is_complement'_top_left
- \+ *lemma* is_complement'_top_right
- \+/\- *lemma* is_complement_top_singleton
- \+/\- *lemma* is_complement_singleton_top

modified src/group_theory/subgroup/basic.lean
- \+ *lemma* coe_eq_univ
- \+ *lemma* coe_eq_singleton



## [2021-11-09 23:52:35](https://github.com/leanprover-community/mathlib/commit/64289fe)
chore(group_theory/order_of_element): fix weird lemma name ([#10245](https://github.com/leanprover-community/mathlib/pull/10245))
#### Estimated changes
modified src/group_theory/order_of_element.lean
- \+ *lemma* pow_ne_one_of_lt_order_of'
- \- *lemma* pow_eq_one_of_lt_order_of'



## [2021-11-09 23:52:33](https://github.com/leanprover-community/mathlib/commit/10d3d25)
chore(set_theory/cardinal): fix name & reorder universes ([#10236](https://github.com/leanprover-community/mathlib/pull/10236))
* add `cardinal.lift_injective`, `cardinal.lift_eq_zero`;
* reorder universe arguments in `cardinal.lift_nat_cast` to match
`cardinal.lift` and `ulift`;
* rename `cardinal.nat_eq_lift_eq_iff` to `cardinal.nat_eq_lift_iff`;
* add `@[simp]` to `cardinal.lift_eq_zero`,
`cardinal.lift_eq_nat_iff`, and `cardinal.nat_eq_lift_iff`.
#### Estimated changes
modified src/linear_algebra/finite_dimensional.lean

modified src/linear_algebra/matrix/to_lin.lean

modified src/set_theory/cardinal.lean
- \+/\- *lemma* lift_eq_nat_iff
- \+ *lemma* nat_eq_lift_iff
- \+/\- *lemma* lift_eq_nat_iff
- \- *lemma* nat_eq_lift_eq_iff
- \+ *theorem* lift_injective
- \+ *theorem* lift_eq_zero
- \+/\- *theorem* lift_nat_cast
- \+/\- *theorem* lift_nat_cast

modified src/set_theory/cardinal_ordinal.lean



## [2021-11-09 23:52:32](https://github.com/leanprover-community/mathlib/commit/7bdb6b3)
feat(algebra/module/linear_map,linear_algebra/alternating,linear_algebra/multilinear/basic): no_zero_smul_divisors instances ([#10234](https://github.com/leanprover-community/mathlib/pull/10234))
Add `no_zero_smul_divisors` instances for linear, multilinear and alternating maps, given such instances for the codomain of the maps.
This also adds some missing `coe_smul` lemmas on these types.
#### Estimated changes
modified src/algebra/module/basic.lean
- \+ *lemma* function.injective.no_zero_smul_divisors

modified src/algebra/module/linear_map.lean
- \+ *lemma* coe_smul

modified src/linear_algebra/alternating.lean
- \+ *lemma* coe_fn_smul

modified src/linear_algebra/multilinear/basic.lean
- \+ *lemma* coe_smul



## [2021-11-09 17:02:26](https://github.com/leanprover-community/mathlib/commit/a2810d9)
feat(data/int/basic): coercion subtraction inequality ([#10054](https://github.com/leanprover-community/mathlib/pull/10054))
Adding to simp a subtraction inequality over coercion from int to nat
#### Estimated changes
modified src/data/int/basic.lean
- \+ *lemma* le_coe_nat_sub



## [2021-11-09 14:26:32](https://github.com/leanprover-community/mathlib/commit/35d574e)
feat(linear_algebra/determinant): alternating maps as multiples of determinant ([#10233](https://github.com/leanprover-community/mathlib/pull/10233))
Add the lemma that any alternating map with the same type as the
determinant map with respect to a basis is a multiple of the
determinant map (given by the value of the alternating map applied to
the basis vectors).
#### Estimated changes
modified src/linear_algebra/alternating.lean
- \+ *lemma* map_eq_zero_of_not_injective
- \+ *lemma* basis.ext_alternating

modified src/linear_algebra/determinant.lean
- \+ *lemma* alternating_map.eq_smul_basis_det



## [2021-11-09 10:46:44](https://github.com/leanprover-community/mathlib/commit/00d9b9f)
feast(ring_theory/norm): add norm_eq_prod_embeddings ([#10226](https://github.com/leanprover-community/mathlib/pull/10226))
We prove that the norm equals the product of the embeddings in an algebraically closed field.
Note that we follow a slightly different path than for the trace, since transitivity of the norm is more delicate, and we avoid it.
From flt-regular.
#### Estimated changes
modified src/ring_theory/norm.lean
- \+ *lemma* norm_eq_norm_adjoin
- \+ *lemma* norm_eq_prod_embeddings_gen
- \+ *lemma* prod_embeddings_eq_finrank_pow
- \+ *lemma* norm_eq_prod_embeddings



## [2021-11-09 09:20:22](https://github.com/leanprover-community/mathlib/commit/11ced18)
feat(algebra/lie/classical): Use computable matrix inverses where possible ([#10218](https://github.com/leanprover-community/mathlib/pull/10218))
#### Estimated changes
modified src/algebra/lie/classical.lean
- \+/\- *lemma* PB_inv
- \- *lemma* is_unit_Pso
- \- *lemma* is_unit_PD
- \+/\- *lemma* PB_inv
- \- *lemma* is_unit_PB
- \+ *def* invertible_Pso
- \+ *def* so_indefinite_equiv
- \+ *def* type_D_equiv_so'
- \+ *def* type_B_equiv_so'

modified src/algebra/lie/matrix.lean
- \+/\- *lemma* matrix.lie_conj_apply
- \+/\- *lemma* matrix.lie_conj_symm_apply
- \+/\- *lemma* matrix.lie_conj_apply
- \+/\- *lemma* matrix.lie_conj_symm_apply
- \+ *def* matrix.lie_conj

modified src/algebra/lie/skew_adjoint.lean
- \+ *def* skew_adjoint_matrices_lie_subalgebra_equiv

modified src/linear_algebra/matrix/to_linear_equiv.lean
- \+/\- *lemma* to_linear_equiv'_apply
- \+/\- *lemma* to_linear_equiv'_symm_apply
- \+/\- *lemma* to_linear_equiv'_apply
- \+/\- *lemma* to_linear_equiv'_symm_apply
- \+ *def* to_linear_equiv'



## [2021-11-09 09:20:21](https://github.com/leanprover-community/mathlib/commit/8614615)
refactor(data/nat/interval): simp for Ico_zero_eq_range ([#10211](https://github.com/leanprover-community/mathlib/pull/10211))
This PR makes two changes: It refactors `nat.Ico_zero_eq_range` from `Ico 0 a = range a` to `Ico 0 = range`, and makes the lemma a simp lemma.
These changes feel good to me, but feel free to close this if this is not the direction we want to go with this lemma.
#### Estimated changes
modified src/algebra/big_operators/intervals.lean

modified src/data/nat/interval.lean
- \+/\- *lemma* Ico_zero_eq_range
- \+/\- *lemma* _root_.finset.range_eq_Ico
- \+/\- *lemma* Ico_zero_eq_range
- \+/\- *lemma* _root_.finset.range_eq_Ico

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/emetric_space.lean



## [2021-11-09 07:29:49](https://github.com/leanprover-community/mathlib/commit/0b093e6)
feat(order/bounded_lattice): a couple of basic instances about with_bot still not having a top if the original preorder didn't and vice versa ([#10215](https://github.com/leanprover-community/mathlib/pull/10215))
Used in the flt-regular project.
#### Estimated changes
modified src/order/bounded_lattice.lean



## [2021-11-09 03:25:48](https://github.com/leanprover-community/mathlib/commit/6af6f67)
chore(scripts): update nolints.txt ([#10240](https://github.com/leanprover-community/mathlib/pull/10240))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/style-exceptions.txt



## [2021-11-09 03:25:47](https://github.com/leanprover-community/mathlib/commit/9d49c4a)
doc(data/finset/fold): fix typo ([#10239](https://github.com/leanprover-community/mathlib/pull/10239))
#### Estimated changes
modified src/data/finset/fold.lean



## [2021-11-09 03:25:45](https://github.com/leanprover-community/mathlib/commit/223f659)
chore(linear_algebra/basic): remove a duplicate proof, generalize map_span_le ([#10219](https://github.com/leanprover-community/mathlib/pull/10219))
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+/\- *lemma* map_span_le
- \+/\- *lemma* map_span_le



## [2021-11-09 01:42:52](https://github.com/leanprover-community/mathlib/commit/424012a)
chore(*): bump to Lean 3.35.1 ([#10237](https://github.com/leanprover-community/mathlib/pull/10237))
#### Estimated changes
modified leanpkg.toml



## [2021-11-08 22:17:41](https://github.com/leanprover-community/mathlib/commit/440163b)
chore(topology/algebra/mul_action): define `has_continuous_vadd` using `to_additive` ([#10227](https://github.com/leanprover-community/mathlib/pull/10227))
Make additive version of the theory of `has_continuous_smul`, i.e., `has_continuous_vadd`, using `to_additive`.  I've been fairly conservative in adding `to_additive` tags -- I left them off lemmas that didn't seem like they'd be relevant for typical additive actions, like those about `units` or `group_with_zero`.
Also make `normed_add_torsor` an instance of `has_continuous_vadd` and use this to establish some of its continuity API.
#### Estimated changes
modified src/analysis/normed_space/add_torsor.lean
- \- *lemma* continuous_vadd
- \- *lemma* filter.tendsto.vadd
- \- *lemma* continuous.vadd
- \- *lemma* continuous_at.vadd
- \- *lemma* continuous_within_at.vadd

modified src/topology/algebra/mul_action.lean



## [2021-11-08 16:03:11](https://github.com/leanprover-community/mathlib/commit/2e4813d)
feat(linear_algebra/matrix/nonsingular_inverse): add invertible_equiv_det_invertible ([#10222](https://github.com/leanprover-community/mathlib/pull/10222))
#### Estimated changes
modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *def* invertible_equiv_det_invertible



## [2021-11-08 16:03:10](https://github.com/leanprover-community/mathlib/commit/1519cd7)
chore(set_theory/cardinal): more simp, fix LHS/RHS ([#10212](https://github.com/leanprover-community/mathlib/pull/10212))
While `coe (fintype.card α)` is a larger expression than `#α`, it allows us to compute the cardinality of a finite type provided that we have a `simp` lemma for `fintype.card α`. It also plays well with lemmas about coercions from `nat` and `cardinal.lift`.
* rename `cardinal.fintype_card` to `cardinal.mk_fintype`, make it a `@[simp]` lemma;
* deduce other cases (`bool`, `Prop`, `unique`, `is_empty`) from it;
* rename `cardinal.finset_card` to `cardinal.mk_finset`, swap LHS/RHS;
* rename `ordinal.fintype_card` to `ordinal.type_fintype`.
#### Estimated changes
modified archive/100-theorems-list/16_abel_ruffini.lean

modified archive/sensitivity.lean

modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_Prop
- \+ *lemma* induction_empty_option'

modified src/field_theory/finite/polynomial.lean

modified src/field_theory/finiteness.lean
- \+/\- *lemma* iff_dim_lt_omega
- \+/\- *lemma* dim_lt_omega
- \+/\- *lemma* iff_dim_lt_omega
- \+/\- *lemma* dim_lt_omega

modified src/field_theory/fixed.lean

modified src/linear_algebra/dimension.lean
- \+/\- *lemma* basis.finite_of_vector_space_index_of_dim_lt_omega
- \+/\- *lemma* basis.finite_of_vector_space_index_of_dim_lt_omega

modified src/linear_algebra/finite_dimensional.lean

modified src/linear_algebra/free_module/finite/rank.lean

modified src/linear_algebra/matrix/to_lin.lean

modified src/set_theory/cardinal.lean
- \+/\- *lemma* mk_eq_zero
- \+/\- *lemma* mk_eq_one
- \+ *lemma* mk_fintype
- \+ *lemma* mk_finset
- \+/\- *lemma* mk_to_nat_eq_card
- \+/\- *lemma* mk_eq_zero
- \+/\- *lemma* mk_eq_one
- \+/\- *lemma* mk_to_nat_eq_card
- \- *lemma* finset_card
- \+/\- *theorem* mk_bool
- \+/\- *theorem* mk_Prop
- \+/\- *theorem* mk_fin
- \+/\- *theorem* mk_bool
- \+/\- *theorem* mk_Prop
- \+/\- *theorem* mk_fin
- \- *theorem* fintype_card

modified src/set_theory/cofinality.lean

modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* type_fintype
- \- *theorem* fintype_card



## [2021-11-08 16:03:09](https://github.com/leanprover-community/mathlib/commit/66dea29)
feat(analysis/convex/specific_functions): Strict convexity of `exp`, `log` and `pow` ([#10123](https://github.com/leanprover-community/mathlib/pull/10123))
This strictifies the results of convexity/concavity of `exp`/`log` and add the strict versions for `pow`, `zpow`, `rpow`.
I'm also renaming `convex_on_pow_of_even` to `even.convex_on_pow` for dot notation.
#### Estimated changes
modified src/analysis/convex/specific_functions.lean
- \+ *lemma* strict_convex_on_exp
- \+/\- *lemma* convex_on_exp
- \+ *lemma* even.convex_on_pow
- \+ *lemma* even.strict_convex_on_pow
- \+ *lemma* strict_convex_on_pow
- \+ *lemma* int_prod_range_pos
- \+ *lemma* strict_convex_on_zpow
- \+ *lemma* strict_convex_on_rpow
- \+ *lemma* strict_concave_on_log_Ioi
- \+ *lemma* strict_concave_on_log_Iio
- \+/\- *lemma* convex_on_exp
- \- *lemma* convex_on_pow_of_even
- \- *lemma* concave_on_log_Ioi
- \- *lemma* concave_on_log_Iio

modified src/analysis/mean_inequalities.lean



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
modified src/linear_algebra/multilinear/basic.lean
- \+ *lemma* dom_dom_congr_eq_iff

created src/linear_algebra/multilinear/basis.lean
- \+ *lemma* basis.ext_multilinear_fin
- \+ *lemma* basis.ext_multilinear



## [2021-11-08 14:15:15](https://github.com/leanprover-community/mathlib/commit/eb67834)
chore(ring_theory/noetherian): golf and generalize map_fg_of_fg ([#10217](https://github.com/leanprover-community/mathlib/pull/10217))
#### Estimated changes
modified src/ring_theory/noetherian.lean
- \+/\- *lemma* map_fg_of_fg
- \+/\- *lemma* map_fg_of_fg



## [2021-11-08 14:15:14](https://github.com/leanprover-community/mathlib/commit/5ba41d8)
feat(algebra/direct_sum): specialize `submodule_is_internal.independent` to add_subgroup ([#10108](https://github.com/leanprover-community/mathlib/pull/10108))
This adds the lemmas `disjoint.map_order_iso` and `complete_lattice.independent.map_order_iso` (and `iff` versions), and uses them to transfer some results on `submodule`s to `add_submonoid`s and `add_subgroup`s.
#### Estimated changes
modified src/algebra/direct_sum/module.lean
- \+ *lemma* add_submonoid_is_internal.independent
- \+ *lemma* add_subgroup_is_internal.independent

modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* independent_of_dfinsupp_sum_add_hom_injective
- \+ *lemma* independent_of_dfinsupp_sum_add_hom_injective'
- \+ *lemma* independent.dfinsupp_sum_add_hom_injective
- \+ *lemma* independent_iff_dfinsupp_sum_add_hom_injective

modified src/order/complete_lattice.lean
- \+ *lemma* independent.map_order_iso
- \+ *lemma* independent_map_order_iso_iff

modified src/order/rel_iso.lean
- \+ *lemma* disjoint.map_order_iso
- \+ *lemma* disjoint_map_order_iso_iff



## [2021-11-08 13:14:28](https://github.com/leanprover-community/mathlib/commit/0dabcb8)
chore(ring_theory/ideal/operations): relax the base ring of algebras from comm_ring to comm_semiring ([#10024](https://github.com/leanprover-community/mathlib/pull/10024))
This also tidies up some variables and consistently uses `B` instead of `S` for the second algebra.
One proof in `ring_theory/finiteness.lean` has to be redone because typeclass search times out where it previously did not.
Thankfully, the new proof is shorter anyway.
#### Estimated changes
modified src/ring_theory/finiteness.lean

modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* quotient.mk_algebra_map
- \+/\- *lemma* quotient.mkₐ_surjective
- \+/\- *lemma* quotient.mkₐ_ker
- \+/\- *lemma* ker_lift.map_smul
- \+/\- *lemma* ker_lift_alg_mk
- \+/\- *lemma* ker_lift_alg_to_ring_hom
- \+/\- *lemma* ker_lift_alg_injective
- \+/\- *lemma* quotient_ker_alg_equiv_of_right_inverse.apply
- \+/\- *lemma* quotient_ker_alg_equiv_of_right_inverse_symm.apply
- \+/\- *lemma* quotient_map_mkₐ
- \+/\- *lemma* quotient_map_comp_mkₐ
- \+/\- *lemma* algebra_map_quotient_injective
- \+/\- *lemma* quotient.mk_algebra_map
- \+/\- *lemma* quotient.mkₐ_surjective
- \+/\- *lemma* quotient.mkₐ_ker
- \+/\- *lemma* ker_lift.map_smul
- \+/\- *lemma* ker_lift_alg_mk
- \+/\- *lemma* ker_lift_alg_to_ring_hom
- \+/\- *lemma* ker_lift_alg_injective
- \+/\- *lemma* quotient_ker_alg_equiv_of_right_inverse.apply
- \+/\- *lemma* quotient_ker_alg_equiv_of_right_inverse_symm.apply
- \+/\- *lemma* quotient_map_mkₐ
- \+/\- *lemma* quotient_map_comp_mkₐ
- \+/\- *lemma* algebra_map_quotient_injective
- \+/\- *def* quotient.mkₐ
- \+/\- *def* ker_lift_alg
- \+/\- *def* quotient_mapₐ
- \+/\- *def* quotient_equiv_alg
- \+/\- *def* quotient.mkₐ
- \+/\- *def* ker_lift_alg
- \+/\- *def* quotient_mapₐ
- \+/\- *def* quotient_equiv_alg



## [2021-11-08 11:43:24](https://github.com/leanprover-community/mathlib/commit/b4a5b01)
feat(data/finset/basic): add card_insert_eq_ite ([#10209](https://github.com/leanprover-community/mathlib/pull/10209))
Adds the lemma `card_insert_eq_ite` combining the functionality of `card_insert_of_not_mem` and `card_insert_of_mem`, analogous to how `card_erase_eq_ite`.
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *theorem* card_insert_eq_ite



## [2021-11-08 11:43:23](https://github.com/leanprover-community/mathlib/commit/2fd6a77)
chore(algebra/algebra/basic): add `algebra.coe_linear_map` ([#10204](https://github.com/leanprover-community/mathlib/pull/10204))
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* coe_linear_map



## [2021-11-08 11:43:20](https://github.com/leanprover-community/mathlib/commit/4dd7eca)
feat(analysis/{seminorm, convex/specific_functions}): A seminorm is convex ([#10203](https://github.com/leanprover-community/mathlib/pull/10203))
This proves `seminorm.convex_on`, `convex_on_norm` (which is morally a special case of the former) and leverages it to golf `seminorm.convex_ball`.
This also fixes the explicitness of arguments of `convex_on.translate_left` and friends.
#### Estimated changes
modified src/analysis/convex/function.lean
- \+/\- *lemma* convex_on.translate_right
- \+/\- *lemma* concave_on.translate_right
- \+/\- *lemma* convex_on.translate_left
- \+/\- *lemma* concave_on.translate_left
- \+/\- *lemma* strict_convex_on.translate_right
- \+/\- *lemma* strict_concave_on.translate_right
- \+/\- *lemma* strict_convex_on.translate_left
- \+/\- *lemma* strict_concave_on.translate_left
- \+/\- *lemma* convex_on.translate_right
- \+/\- *lemma* concave_on.translate_right
- \+/\- *lemma* convex_on.translate_left
- \+/\- *lemma* concave_on.translate_left
- \+/\- *lemma* strict_convex_on.translate_right
- \+/\- *lemma* strict_concave_on.translate_right
- \+/\- *lemma* strict_convex_on.translate_left
- \+/\- *lemma* strict_concave_on.translate_left

modified src/analysis/convex/specific_functions.lean
- \+ *lemma* convex_on_norm

modified src/analysis/seminorm.lean



## [2021-11-08 11:43:19](https://github.com/leanprover-community/mathlib/commit/e44aa6e)
feat(linear_algebra/basic): some lemmas about span and restrict_scalars ([#10167](https://github.com/leanprover-community/mathlib/pull/10167))
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \- *lemma* span_le_restrict_scalars

modified src/algebra/module/submodule.lean
- \+ *lemma* coe_restrict_scalars
- \+/\- *lemma* restrict_scalars_mem
- \+ *lemma* restrict_scalars_self
- \+/\- *lemma* restrict_scalars_mem

modified src/linear_algebra/basic.lean
- \+/\- *lemma* span_eq
- \+ *lemma* span_coe_eq_restrict_scalars
- \+ *lemma* span_le_restrict_scalars
- \+ *lemma* span_subset_span
- \+ *lemma* span_span_of_tower
- \+/\- *lemma* span_eq

modified src/linear_algebra/finsupp.lean

modified src/linear_algebra/pi.lean

modified src/ring_theory/finiteness.lean



## [2021-11-08 11:43:18](https://github.com/leanprover-community/mathlib/commit/fb0cfbd)
feat(measure_theory/measure/complex): define complex measures ([#10166](https://github.com/leanprover-community/mathlib/pull/10166))
Complex measures was defined to be a vector measure over ℂ without any API. This PR adds some basic definitions about complex measures and proves the complex version of the Lebesgue decomposition theorem.
#### Estimated changes
modified src/measure_theory/decomposition/lebesgue.lean
- \+/\- *lemma* singular_part_smul
- \+ *lemma* integrable_rn_deriv
- \+/\- *lemma* singular_part_smul
- \+ *theorem* singular_part_add_with_density_rn_deriv_eq
- \+ *def* singular_part
- \+ *def* rn_deriv

created src/measure_theory/measure/complex.lean
- \+ *lemma* _root_.measure_theory.signed_measure.to_complex_measure_apply
- \+ *lemma* to_complex_measure_to_signed_measure
- \+ *lemma* _root_.measure_theory.signed_measure.re_to_complex_measure
- \+ *lemma* _root_.measure_theory.signed_measure.im_to_complex_measure
- \+ *lemma* absolutely_continuous_ennreal_iff
- \+ *def* re
- \+ *def* im
- \+ *def* _root_.measure_theory.signed_measure.to_complex_measure
- \+ *def* equiv_signed_measure
- \+ *def* equiv_signed_measureₗ

modified src/measure_theory/measure/vector_measure.lean
- \+ *lemma* map_range_apply
- \+ *lemma* map_range_id
- \+ *lemma* map_range_zero
- \+ *lemma* map_range_add
- \+ *def* map_range
- \+ *def* map_range_hom
- \+ *def* map_rangeₗ



## [2021-11-08 11:43:17](https://github.com/leanprover-community/mathlib/commit/e4a1e80)
feat(analysis/convex/combination): Convex hull of a `set.prod` and `set.pi` ([#10125](https://github.com/leanprover-community/mathlib/pull/10125))
This proves
* `(∀ i, convex 𝕜 (t i)) → convex 𝕜 (s.pi t)`
* `convex_hull 𝕜 (s.prod t) = (convex_hull 𝕜 s).prod (convex_hull 𝕜 t)`
* `convex_hull 𝕜 (s.pi t) = s.pi (convex_hull 𝕜 ∘ t)`
#### Estimated changes
modified src/analysis/convex/basic.lean
- \+ *lemma* convex_pi

modified src/analysis/convex/combination.lean
- \+ *lemma* convex_hull_prod



## [2021-11-08 11:43:16](https://github.com/leanprover-community/mathlib/commit/1fac00e)
feat(analysis): lemmas about `arg` and `exp_map_circle` ([#10066](https://github.com/leanprover-community/mathlib/pull/10066))
#### Estimated changes
modified src/analysis/complex/circle.lean
- \+ *lemma* exp_map_circle_sub

created src/analysis/special_functions/complex/circle.lean
- \+ *lemma* injective_arg
- \+ *lemma* arg_eq_arg
- \+ *lemma* arg_exp_map_circle
- \+ *lemma* exp_map_circle_arg
- \+ *lemma* left_inverse_exp_map_circle_arg
- \+ *lemma* inv_on_arg_exp_map_circle
- \+ *lemma* surj_on_exp_map_circle_neg_pi_pi
- \+ *lemma* exp_map_circle_eq_exp_map_circle
- \+ *lemma* periodic_exp_map_circle
- \+ *lemma* exp_map_circle_two_pi
- \+ *lemma* exp_map_circle_sub_two_pi
- \+ *lemma* exp_map_circle_add_two_pi



## [2021-11-08 11:43:15](https://github.com/leanprover-community/mathlib/commit/48abaed)
feat(analysis/special_functions/complex/arg): continuity of arg outside of the negative real half-line ([#9500](https://github.com/leanprover-community/mathlib/pull/9500))
#### Estimated changes
modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* arg_of_re_nonneg
- \+ *lemma* arg_of_re_zero_of_im_pos
- \+ *lemma* arg_of_re_zero_of_im_neg
- \+ *lemma* arg_of_re_neg_of_im_nonneg
- \+ *lemma* arg_of_re_neg_of_im_neg
- \+ *lemma* arg_eq_nhds_of_re_pos
- \+ *lemma* arg_eq_nhds_of_re_neg_of_im_pos
- \+ *lemma* arg_eq_nhds_of_re_neg_of_im_neg
- \+ *lemma* continuous_at_arg_of_re_pos
- \+ *lemma* continuous_at_arg_of_re_neg_of_im_pos
- \+ *lemma* continuous_at_arg_of_re_neg_of_im_neg
- \+ *lemma* continuous_at_arg_of_re_zero
- \+ *lemma* continuous_at_arg



## [2021-11-08 10:06:42](https://github.com/leanprover-community/mathlib/commit/32c8445)
split(data/list/*): split off `data.list.basic` ([#10164](https://github.com/leanprover-community/mathlib/pull/10164))
Killing the giants. This moves 700 lines off `data.list.basic` that were about
* `list.sum` and `list.product` into `data.list.big_operators`
* `list.countp` and `list.count` into `data.list.count`
* `list.sigma` and `list.prod` into `data.list.sigma_prod`
#### Estimated changes
modified src/computability/language.lean

modified src/computability/primrec.lean

modified src/data/fin_enum.lean

modified src/data/hash_map.lean

modified src/data/list/basic.lean
- \+/\- *lemma* slice_eq
- \+/\- *lemma* sizeof_slice_lt
- \- *lemma* prod_is_unit
- \- *lemma* prod_take_mul_prod_drop
- \- *lemma* prod_take_succ
- \- *lemma* length_pos_of_prod_ne_one
- \- *lemma* prod_update_nth
- \- *lemma* _root_.opposite.op_list_prod
- \- *lemma* _root_.opposite.unop_list_prod
- \- *lemma* prod_inv_reverse
- \- *lemma* prod_reverse_noncomm
- \- *lemma* prod_drop_succ
- \- *lemma* prod_inv
- \- *lemma* prod_update_nth'
- \- *lemma* eq_of_sum_take_eq
- \- *lemma* monotone_sum_take
- \- *lemma* one_le_prod_of_one_le
- \- *lemma* single_le_prod
- \- *lemma* all_one_of_le_one_le_of_prod_eq_one
- \- *lemma* sum_eq_zero_iff
- \- *lemma* length_le_sum_of_one_le
- \- *lemma* length_pos_of_sum_pos
- \- *lemma* sum_le_foldr_max
- \- *lemma* dvd_prod
- \- *lemma* exists_lt_of_sum_lt
- \- *lemma* exists_le_of_sum_le
- \- *lemma* nth_zero_mul_tail_prod
- \- *lemma* head_mul_tail_prod_of_ne_nil
- \- *lemma* prod_pos
- \- *lemma* head_add_tail_sum
- \- *lemma* head_le_sum
- \- *lemma* tail_sum
- \- *lemma* alternating_prod_nil
- \- *lemma* alternating_prod_singleton
- \- *lemma* alternating_prod_cons_cons
- \- *lemma* alternating_sum_cons_cons
- \- *lemma* join_nil
- \- *lemma* join_join
- \- *lemma* take_sum_join
- \- *lemma* drop_sum_join
- \- *lemma* drop_take_succ_eq_cons_nth_le
- \- *lemma* drop_take_succ_join_eq_nth_le
- \- *lemma* sum_take_map_length_lt1
- \- *lemma* sum_take_map_length_lt2
- \- *lemma* nth_le_join
- \- *lemma* count_bind
- \- *lemma* count_map_map
- \- *lemma* monoid_hom.unop_map_list_prod
- \+/\- *lemma* slice_eq
- \+/\- *lemma* sizeof_slice_lt
- \+/\- *theorem* mem_map_swap
- \- *theorem* prod_nil
- \- *theorem* prod_singleton
- \- *theorem* prod_cons
- \- *theorem* prod_append
- \- *theorem* prod_concat
- \- *theorem* prod_join
- \- *theorem* prod_eq_zero
- \- *theorem* prod_eq_zero_iff
- \- *theorem* prod_ne_zero
- \- *theorem* prod_eq_foldr
- \- *theorem* prod_hom_rel
- \- *theorem* prod_hom
- \- *theorem* prod_erase
- \- *theorem* sum_const_nat
- \- *theorem* dvd_sum
- \- *theorem* length_join
- \- *theorem* length_bind
- \- *theorem* join_eq_nil
- \- *theorem* join_append
- \- *theorem* join_filter_empty_eq_ff
- \- *theorem* join_filter_ne_nil
- \- *theorem* eq_iff_join_eq
- \- *theorem* countp_nil
- \- *theorem* countp_cons_of_pos
- \- *theorem* countp_cons_of_neg
- \- *theorem* length_eq_countp_add_countp
- \- *theorem* countp_eq_length_filter
- \- *theorem* countp_append
- \- *theorem* countp_pos
- \- *theorem* length_filter_lt_length_iff_exists
- \- *theorem* countp_le_of_sublist
- \- *theorem* countp_filter
- \- *theorem* count_nil
- \- *theorem* count_cons
- \- *theorem* count_cons'
- \- *theorem* count_cons_self
- \- *theorem* count_cons_of_ne
- \- *theorem* count_tail
- \- *theorem* count_le_of_sublist
- \- *theorem* count_le_count_cons
- \- *theorem* count_singleton
- \- *theorem* count_append
- \- *theorem* count_concat
- \- *theorem* count_pos
- \- *theorem* count_eq_zero_of_not_mem
- \- *theorem* not_mem_of_count_eq_zero
- \- *theorem* count_repeat
- \- *theorem* le_count_iff_repeat_sublist
- \- *theorem* repeat_count_eq_of_count_eq_length
- \- *theorem* count_filter
- \- *theorem* count_erase_self
- \- *theorem* count_erase_of_ne
- \- *theorem* nil_product
- \- *theorem* product_cons
- \- *theorem* product_nil
- \- *theorem* mem_product
- \- *theorem* length_product
- \- *theorem* nil_sigma
- \- *theorem* sigma_cons
- \- *theorem* sigma_nil
- \- *theorem* mem_sigma
- \- *theorem* length_sigma
- \- *theorem* monoid_hom.map_list_prod
- \- *theorem* prod_map_hom
- \- *theorem* sum_map_mul_left
- \- *theorem* sum_map_mul_right
- \+/\- *theorem* mem_map_swap

created src/data/list/big_operators.lean
- \+ *lemma* prod_nil
- \+ *lemma* prod_singleton
- \+ *lemma* prod_cons
- \+ *lemma* prod_append
- \+ *lemma* prod_concat
- \+ *lemma* prod_join
- \+ *lemma* prod_eq_zero
- \+ *lemma* prod_eq_zero_iff
- \+ *lemma* prod_ne_zero
- \+ *lemma* prod_eq_foldr
- \+ *lemma* prod_hom_rel
- \+ *lemma* prod_hom
- \+ *lemma* prod_is_unit
- \+ *lemma* prod_take_mul_prod_drop
- \+ *lemma* prod_take_succ
- \+ *lemma* length_pos_of_prod_ne_one
- \+ *lemma* prod_update_nth
- \+ *lemma* _root_.opposite.op_list_prod
- \+ *lemma* _root_.opposite.unop_list_prod
- \+ *lemma* prod_inv_reverse
- \+ *lemma* prod_reverse_noncomm
- \+ *lemma* prod_drop_succ
- \+ *lemma* prod_inv
- \+ *lemma* prod_update_nth'
- \+ *lemma* eq_of_sum_take_eq
- \+ *lemma* monotone_sum_take
- \+ *lemma* one_le_prod_of_one_le
- \+ *lemma* single_le_prod
- \+ *lemma* all_one_of_le_one_le_of_prod_eq_one
- \+ *lemma* sum_eq_zero_iff
- \+ *lemma* length_le_sum_of_one_le
- \+ *lemma* length_pos_of_sum_pos
- \+ *lemma* sum_le_foldr_max
- \+ *lemma* prod_erase
- \+ *lemma* dvd_prod
- \+ *lemma* sum_const_nat
- \+ *lemma* dvd_sum
- \+ *lemma* exists_lt_of_sum_lt
- \+ *lemma* exists_le_of_sum_le
- \+ *lemma* nth_zero_mul_tail_prod
- \+ *lemma* head_mul_tail_prod_of_ne_nil
- \+ *lemma* prod_pos
- \+ *lemma* head_add_tail_sum
- \+ *lemma* head_le_sum
- \+ *lemma* tail_sum
- \+ *lemma* alternating_prod_nil
- \+ *lemma* alternating_prod_singleton
- \+ *lemma* alternating_prod_cons_cons
- \+ *lemma* alternating_sum_cons_cons
- \+ *lemma* _root_.monoid_hom.map_list_prod
- \+ *lemma* _root_.monoid_hom.unop_map_list_prod
- \+ *lemma* prod_map_hom
- \+ *lemma* sum_map_mul_left
- \+ *lemma* sum_map_mul_right

created src/data/list/count.lean
- \+ *lemma* countp_nil
- \+ *lemma* countp_cons_of_pos
- \+ *lemma* countp_cons_of_neg
- \+ *lemma* length_eq_countp_add_countp
- \+ *lemma* countp_eq_length_filter
- \+ *lemma* countp_append
- \+ *lemma* countp_pos
- \+ *lemma* length_filter_lt_length_iff_exists
- \+ *lemma* sublist.countp_le
- \+ *lemma* countp_filter
- \+ *lemma* count_nil
- \+ *lemma* count_cons
- \+ *lemma* count_cons'
- \+ *lemma* count_cons_self
- \+ *lemma* count_cons_of_ne
- \+ *lemma* count_tail
- \+ *lemma* sublist.count_le
- \+ *lemma* count_le_count_cons
- \+ *lemma* count_singleton
- \+ *lemma* count_append
- \+ *lemma* count_concat
- \+ *lemma* count_pos
- \+ *lemma* count_eq_zero_of_not_mem
- \+ *lemma* not_mem_of_count_eq_zero
- \+ *lemma* count_repeat
- \+ *lemma* le_count_iff_repeat_sublist
- \+ *lemma* repeat_count_eq_of_count_eq_length
- \+ *lemma* count_filter
- \+ *lemma* count_bind
- \+ *lemma* count_map_map
- \+ *lemma* count_erase_self
- \+ *lemma* count_erase_of_ne

created src/data/list/join.lean
- \+ *lemma* join_nil
- \+ *lemma* join_eq_nil
- \+ *lemma* join_append
- \+ *lemma* join_filter_empty_eq_ff
- \+ *lemma* join_filter_ne_nil
- \+ *lemma* join_join
- \+ *lemma* length_join
- \+ *lemma* length_bind
- \+ *lemma* take_sum_join
- \+ *lemma* drop_sum_join
- \+ *lemma* drop_take_succ_eq_cons_nth_le
- \+ *lemma* drop_take_succ_join_eq_nth_le
- \+ *lemma* sum_take_map_length_lt1
- \+ *lemma* sum_take_map_length_lt2
- \+ *lemma* nth_le_join
- \+ *theorem* eq_iff_join_eq

modified src/data/list/lattice.lean

modified src/data/list/pairwise.lean

modified src/data/list/perm.lean

modified src/data/list/permutation.lean

modified src/data/list/prod_monoid.lean

created src/data/list/prod_sigma.lean
- \+ *lemma* nil_product
- \+ *lemma* product_cons
- \+ *lemma* product_nil
- \+ *lemma* mem_product
- \+ *lemma* length_product
- \+ *lemma* nil_sigma
- \+ *lemma* sigma_cons
- \+ *lemma* sigma_nil
- \+ *lemma* mem_sigma
- \+ *lemma* length_sigma

modified src/data/list/zip.lean

modified src/data/multiset/basic.lean

modified src/tactic/omega/int/dnf.lean

modified src/tactic/omega/nat/dnf.lean



## [2021-11-08 08:27:27](https://github.com/leanprover-community/mathlib/commit/380d6ca)
chore(algebra/direct_sum/module): extract out common `variables` ([#10207](https://github.com/leanprover-community/mathlib/pull/10207))
Slight reorganization to extract out repeatedly-used variable declarations, and update module docstring.  No changes to the content.
#### Estimated changes
modified src/algebra/direct_sum/module.lean
- \+/\- *lemma* submodule_coe_of
- \+/\- *lemma* submodule_is_internal.to_add_submonoid
- \+/\- *lemma* submodule_is_internal.supr_eq_top
- \+/\- *lemma* submodule_is_internal.independent
- \+/\- *lemma* submodule_is_internal.to_add_subgroup
- \+/\- *lemma* submodule_is_internal_of_independent_of_supr_eq_top
- \+/\- *lemma* submodule_is_internal_iff_independent_and_supr_eq_top
- \+/\- *lemma* submodule_coe_of
- \+/\- *lemma* submodule_is_internal.to_add_submonoid
- \+/\- *lemma* submodule_is_internal.to_add_subgroup
- \+/\- *lemma* submodule_is_internal.supr_eq_top
- \+/\- *lemma* submodule_is_internal.independent
- \+/\- *lemma* submodule_is_internal_of_independent_of_supr_eq_top
- \+/\- *lemma* submodule_is_internal_iff_independent_and_supr_eq_top
- \+/\- *def* submodule_coe
- \+/\- *def* submodule_is_internal
- \+/\- *def* submodule_coe
- \+/\- *def* submodule_is_internal



## [2021-11-08 08:27:25](https://github.com/leanprover-community/mathlib/commit/bf242b7)
feat(algebra/order/with_zero): add le lemmas ([#10183](https://github.com/leanprover-community/mathlib/pull/10183))
#### Estimated changes
modified src/algebra/order/with_zero.lean
- \+ *lemma* le_mul_inv_iff₀
- \+ *lemma* mul_inv_le_iff₀
- \+ *lemma* mul_le_mul_right₀
- \+ *lemma* div_le_div_right₀
- \+ *lemma* le_div_iff₀
- \+ *lemma* div_le_iff₀



## [2021-11-08 08:27:23](https://github.com/leanprover-community/mathlib/commit/e0aa9f0)
refactor(linear_algebra/matrix/nonsingular_inverse): clean up ([#10175](https://github.com/leanprover-community/mathlib/pull/10175))
This file is a mess, and switches back and forth between three different inverses, proving the same things over and over again.
This pulls all the `invertible` versions of these statements to the top, and uses them here and there to golf proofs.
The lemmas `nonsing_inv_left_right` and `nonsing_inv_right_left` are merged into a single lemma `mul_eq_one_comm`.
The lemma `inv_eq_nonsing_inv_of_invertible` has been renamed to `inv_of_eq_nonsing_inv`
This also adds two new lemmas `inv_of_eq` and `det_inv_of`, both of which have trivial proofs.
#### Estimated changes
modified src/algebra/invertible.lean
- \+ *lemma* ring.inverse_invertible

modified src/algebra/lie/classical.lean

modified src/linear_algebra/general_linear_group.lean

modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* inv_of_eq
- \+ *lemma* det_inv_of
- \+ *lemma* mul_eq_one_comm
- \+/\- *lemma* is_unit_iff_is_unit_det
- \+/\- *lemma* is_unit_det_of_invertible
- \+/\- *lemma* is_unit_det_of_left_inverse
- \+/\- *lemma* is_unit_det_of_right_inverse
- \+/\- *lemma* det_ne_zero_of_left_inverse
- \+/\- *lemma* det_ne_zero_of_right_inverse
- \+ *lemma* inv_of_eq_nonsing_inv
- \+/\- *lemma* nonsing_inv_eq_ring_inverse
- \+/\- *lemma* mul_inv_of_invertible
- \+/\- *lemma* inv_mul_of_invertible
- \+/\- *lemma* left_inv_eq_left_inv
- \+/\- *lemma* right_inv_eq_right_inv
- \+/\- *lemma* right_inv_eq_left_inv
- \+/\- *lemma* is_unit_iff_is_unit_det
- \+/\- *lemma* nonsing_inv_eq_ring_inverse
- \+/\- *lemma* is_unit_det_of_invertible
- \- *lemma* inv_eq_nonsing_inv_of_invertible
- \+/\- *lemma* is_unit_det_of_left_inverse
- \+/\- *lemma* is_unit_det_of_right_inverse
- \+/\- *lemma* det_ne_zero_of_left_inverse
- \+/\- *lemma* det_ne_zero_of_right_inverse
- \- *lemma* nonsing_inv_left_right
- \- *lemma* nonsing_inv_right_left
- \+/\- *lemma* left_inv_eq_left_inv
- \+/\- *lemma* right_inv_eq_right_inv
- \+/\- *lemma* right_inv_eq_left_inv
- \+/\- *lemma* mul_inv_of_invertible
- \+/\- *lemma* inv_mul_of_invertible
- \+/\- *def* invertible_of_det_invertible
- \+/\- *def* det_invertible_of_left_inverse
- \+/\- *def* det_invertible_of_right_inverse
- \+/\- *def* det_invertible_of_invertible
- \+/\- *def* invertible_of_left_inverse
- \+/\- *def* invertible_of_right_inverse
- \+/\- *def* unit_of_det_invertible
- \+/\- *def* invertible_of_det_invertible
- \+/\- *def* det_invertible_of_left_inverse
- \+/\- *def* det_invertible_of_right_inverse
- \+/\- *def* det_invertible_of_invertible
- \+/\- *def* unit_of_det_invertible
- \+/\- *def* invertible_of_left_inverse
- \+/\- *def* invertible_of_right_inverse

modified src/linear_algebra/unitary_group.lean



## [2021-11-08 08:27:21](https://github.com/leanprover-community/mathlib/commit/bc55cd7)
feat(archive/imo) : Add solution to IMO 1994 Q1 ([#10171](https://github.com/leanprover-community/mathlib/pull/10171))
IMO 1994 Q1
#### Estimated changes
created archive/imo/imo1994_q1.lean
- \+ *lemma* tedious
- \+ *theorem* imo1994_q1



## [2021-11-08 08:27:20](https://github.com/leanprover-community/mathlib/commit/62f94ad)
feat(measure_theory/measurable_space): define `measurable_embedding` ([#10023](https://github.com/leanprover-community/mathlib/pull/10023))
This way we can generalize our theorems about `measurable_equiv` and `closed_embedding`s.
#### Estimated changes
modified src/data/set/function.lean
- \+ *lemma* range_extend_subset
- \+ *lemma* range_extend

modified src/measure_theory/constructions/borel_space.lean
- \- *lemma* closed_embedding.measurable_inv_fun
- \- *lemma* measurable_comp_iff_of_closed_embedding
- \- *lemma* ae_measurable_comp_iff_of_closed_embedding
- \- *lemma* ae_measurable_comp_right_iff_of_closed_embedding

modified src/measure_theory/function/l1_space.lean
- \+ *lemma* _root_.measurable_embedding.integrable_map_iff

modified src/measure_theory/function/lp_space.lean

modified src/measure_theory/integral/bochner.lean
- \+ *lemma* _root_.measurable_embedding.integral_map
- \+ *lemma* _root_.closed_embedding.integral_map
- \- *lemma* integral_map_of_closed_embedding

modified src/measure_theory/integral/integrable_on.lean
- \+ *lemma* _root_.measurable_embedding.integrable_on_map_iff

modified src/measure_theory/integral/interval_integral.lean

modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* extend_apply
- \+ *lemma* extend_comp_eq'
- \+ *lemma* extend_comp_eq
- \+ *lemma* lintegral_map'
- \+/\- *lemma* lintegral_map
- \+ *lemma* _root_.measurable_embedding.lintegral_map
- \+/\- *lemma* lintegral_map
- \- *lemma* lintegral_map_equiv
- \+ *def* extend

modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* _root_.measurable_embedding.set_integral_map
- \+ *lemma* _root_.closed_embedding.set_integral_map
- \- *lemma* set_integral_map_of_closed_embedding

modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_of_restrict_of_restrict_compl
- \+ *lemma* measurable.dite
- \+ *lemma* measurable_set_image
- \+ *lemma* id
- \+ *lemma* comp
- \+ *lemma* subtype_coe
- \+ *lemma* measurable_set_range
- \+ *lemma* measurable_set_preimage
- \+ *lemma* measurable_range_splitting
- \+ *lemma* measurable_extend
- \+ *lemma* exists_measurable_extend
- \+ *lemma* measurable_comp_iff
- \+ *lemma* measurable_set.exists_measurable_proj
- \+ *lemma* of_measurable_inverse_on_range
- \+ *lemma* of_measurable_inverse
- \+ *theorem* symm_preimage_preimage
- \+ *theorem* image_eq_preimage
- \+ *theorem* measurable_set_preimage
- \+ *theorem* measurable_set_image

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* map_comap
- \+ *lemma* comap_apply
- \+ *lemma* ae_map_iff
- \+ *lemma* restrict_map
- \+ *lemma* comap_subtype_coe_apply
- \+/\- *lemma* map_comap_subtype_coe
- \+ *lemma* ae_restrict_iff_subtype
- \+ *lemma* volume_set_coe_def
- \+ *lemma* measurable_set.map_coe_volume
- \+ *lemma* volume_image_subtype_coe
- \+ *lemma* subtype_mk
- \+ *lemma* measurable_embedding.ae_measurable_map_iff
- \+ *lemma* measurable_embedding.ae_measurable_comp_iff
- \+ *lemma* ae_measurable_restrict_iff_comap_subtype
- \+/\- *lemma* map_comap_subtype_coe
- \+ *theorem* map_apply



## [2021-11-08 06:58:20](https://github.com/leanprover-community/mathlib/commit/c50c2c3)
docs(algebra/big_operators): correct documentation for prod ([#10206](https://github.com/leanprover-community/mathlib/pull/10206))
#### Estimated changes
modified src/algebra/big_operators/basic.lean



## [2021-11-07 10:12:36](https://github.com/leanprover-community/mathlib/commit/ae98aad)
chore(measure_theory/measure): review API of `mutually_singular` ([#10186](https://github.com/leanprover-community/mathlib/pull/10186))
#### Estimated changes
modified src/measure_theory/decomposition/jordan.lean

modified src/measure_theory/decomposition/lebesgue.lean
- \+ *def* singular_part
- \- *def* singular_part(s

modified src/measure_theory/integral/lebesgue.lean

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* sum_of_empty
- \+ *lemma* mk
- \+/\- *lemma* zero_right
- \+/\- *lemma* symm
- \+ *lemma* comm
- \+/\- *lemma* zero_left
- \+ *lemma* mono_ac
- \+ *lemma* mono
- \+ *lemma* sum_left
- \+ *lemma* sum_right
- \+ *lemma* add_left_iff
- \+ *lemma* add_right_iff
- \+ *lemma* add_left
- \+ *lemma* add_right
- \+/\- *lemma* smul
- \+ *lemma* smul_nnreal
- \+/\- *lemma* zero_right
- \+/\- *lemma* symm
- \+/\- *lemma* zero_left
- \- *lemma* add
- \- *lemma* add_iff
- \+/\- *lemma* smul
- \- *lemma* of_absolutely_continuous

modified src/topology/instances/ennreal.lean



## [2021-11-07 09:34:49](https://github.com/leanprover-community/mathlib/commit/7a8a914)
refactor(measure_theory/function/l1_space): remove hypothesis ([#10185](https://github.com/leanprover-community/mathlib/pull/10185))
* from `tendsto_lintegral_norm_of_dominated_convergence`
* Missed this in [#10181](https://github.com/leanprover-community/mathlib/pull/10181)
* Add comment about the ability to weaker `bound_integrable`.
#### Estimated changes
modified src/measure_theory/function/l1_space.lean

modified src/measure_theory/integral/bochner.lean



## [2021-11-07 05:17:04](https://github.com/leanprover-community/mathlib/commit/7d240ce)
chore(data/matrix/notation): split into 2 files ([#10199](https://github.com/leanprover-community/mathlib/pull/10199))
I want to use `![a, b]` notation in some files that don't need to import `data.matrix.basic`.
#### Estimated changes
modified src/data/complex/module.lean

created src/data/fin/vec_notation.lean
- \+ *lemma* empty_eq
- \+ *lemma* head_fin_const
- \+ *lemma* cons_val_zero
- \+ *lemma* cons_val_zero'
- \+ *lemma* cons_val_succ
- \+ *lemma* cons_val_succ'
- \+ *lemma* head_cons
- \+ *lemma* tail_cons
- \+ *lemma* empty_val'
- \+ *lemma* cons_head_tail
- \+ *lemma* range_cons
- \+ *lemma* range_empty
- \+ *lemma* vec_cons_const
- \+ *lemma* vec_single_eq_const
- \+ *lemma* cons_val_one
- \+ *lemma* cons_val_fin_one
- \+ *lemma* cons_fin_one
- \+ *lemma* empty_append
- \+ *lemma* cons_append
- \+ *lemma* vec_alt0_append
- \+ *lemma* vec_alt1_append
- \+ *lemma* vec_head_vec_alt0
- \+ *lemma* vec_head_vec_alt1
- \+ *lemma* cons_vec_bit0_eq_alt0
- \+ *lemma* cons_vec_bit1_eq_alt1
- \+ *lemma* cons_vec_alt0
- \+ *lemma* empty_vec_alt0
- \+ *lemma* cons_vec_alt1
- \+ *lemma* empty_vec_alt1
- \+ *lemma* smul_empty
- \+ *lemma* smul_cons
- \+ *lemma* empty_add_empty
- \+ *lemma* cons_add
- \+ *lemma* add_cons
- \+ *lemma* head_add
- \+ *lemma* tail_add
- \+ *lemma* empty_sub_empty
- \+ *lemma* cons_sub
- \+ *lemma* sub_cons
- \+ *lemma* head_sub
- \+ *lemma* tail_sub
- \+ *lemma* zero_empty
- \+ *lemma* cons_zero_zero
- \+ *lemma* head_zero
- \+ *lemma* tail_zero
- \+ *lemma* cons_eq_zero_iff
- \+ *lemma* cons_nonzero_iff
- \+ *lemma* neg_empty
- \+ *lemma* neg_cons
- \+ *lemma* head_neg
- \+ *lemma* tail_neg
- \+ *def* vec_empty
- \+ *def* vec_cons
- \+ *def* vec_head
- \+ *def* vec_tail
- \+ *def* vec_alt0
- \+ *def* vec_alt1

modified src/data/matrix/notation.lean
- \- *lemma* empty_eq
- \- *lemma* head_fin_const
- \- *lemma* cons_val_zero
- \- *lemma* cons_val_zero'
- \- *lemma* cons_val_succ
- \- *lemma* cons_val_succ'
- \- *lemma* head_cons
- \- *lemma* tail_cons
- \- *lemma* empty_val'
- \- *lemma* cons_head_tail
- \- *lemma* range_cons
- \- *lemma* range_empty
- \- *lemma* vec_cons_const
- \- *lemma* vec_single_eq_const
- \- *lemma* cons_val_one
- \- *lemma* cons_val_fin_one
- \- *lemma* cons_fin_one
- \- *lemma* empty_append
- \- *lemma* cons_append
- \- *lemma* vec_alt0_append
- \- *lemma* vec_alt1_append
- \- *lemma* vec_head_vec_alt0
- \- *lemma* vec_head_vec_alt1
- \- *lemma* cons_vec_bit0_eq_alt0
- \- *lemma* cons_vec_bit1_eq_alt1
- \- *lemma* cons_vec_alt0
- \- *lemma* empty_vec_alt0
- \- *lemma* cons_vec_alt1
- \- *lemma* empty_vec_alt1
- \- *lemma* smul_empty
- \- *lemma* smul_cons
- \- *lemma* empty_add_empty
- \- *lemma* cons_add
- \- *lemma* add_cons
- \- *lemma* head_add
- \- *lemma* tail_add
- \- *lemma* empty_sub_empty
- \- *lemma* cons_sub
- \- *lemma* sub_cons
- \- *lemma* head_sub
- \- *lemma* tail_sub
- \- *lemma* zero_empty
- \- *lemma* cons_zero_zero
- \- *lemma* head_zero
- \- *lemma* tail_zero
- \- *lemma* cons_eq_zero_iff
- \- *lemma* cons_nonzero_iff
- \- *lemma* neg_empty
- \- *lemma* neg_cons
- \- *lemma* head_neg
- \- *lemma* tail_neg
- \- *def* vec_empty
- \- *def* vec_cons
- \- *def* vec_head
- \- *def* vec_tail
- \- *def* vec_alt0
- \- *def* vec_alt1

modified src/data/real/golden_ratio.lean

modified src/group_theory/solvable.lean

modified src/linear_algebra/affine_space/independent.lean

modified src/measure_theory/measure/outer_measure.lean

modified src/ring_theory/witt_vector/structure_polynomial.lean



## [2021-11-06 22:22:28](https://github.com/leanprover-community/mathlib/commit/daac854)
feat(analysis/special_functions/log): Relating `log`-inequalities and `exp`-inequalities ([#10191](https://github.com/leanprover-community/mathlib/pull/10191))
This proves `log x ≤ y ↔ x ≤ exp y` and `x ≤ log y ↔ exp x ≤ y`.
#### Estimated changes
modified src/analysis/special_functions/log.lean
- \+ *lemma* log_le_iff_le_exp
- \+ *lemma* log_lt_iff_lt_exp
- \+ *lemma* le_log_iff_exp_le
- \+ *lemma* lt_log_iff_exp_lt



## [2021-11-06 20:27:44](https://github.com/leanprover-community/mathlib/commit/169bb29)
feat(algebra/group/with_one): cleanup algebraic instances ([#10194](https://github.com/leanprover-community/mathlib/pull/10194))
This:
* adds a `has_neg (with_zero α)` instance which sends `0` to `0` and otherwise uses the underlying negation (and the same for `has_inv (with_one α)`).
* replaces the `has_div (with_zero α)`,  `has_pow (with_zero α) ℕ`, and `has_pow (with_zero α) ℤ` instances in order to produce better definitional properties than the previous default ones.
#### Estimated changes
modified src/algebra/group/with_one.lean
- \+ *lemma* coe_inv
- \+ *lemma* coe_pow
- \+ *lemma* coe_div
- \+ *lemma* coe_zpow
- \- *lemma* div_coe



## [2021-11-06 20:27:43](https://github.com/leanprover-community/mathlib/commit/56a9228)
feat(analysis/normed_space/continuous_affine_map): define bundled continuous affine maps ([#10161](https://github.com/leanprover-community/mathlib/pull/10161))
I want to use the result the evaluation map `Hom(E, F) × E → F` is smooth in a category with continuous affine maps as morphisms. It is convenient to have a bundled type for this, despite the necessary boilerplate (proposed here).
Formalized as part of the Sphere Eversion project.
#### Estimated changes
created src/analysis/normed_space/continuous_affine_map.lean
- \+ *lemma* coe_cont_linear_eq_linear
- \+ *lemma* coe_mk_const_linear_eq_linear
- \+ *lemma* coe_linear_eq_coe_cont_linear
- \+ *lemma* map_vadd
- \+ *lemma* cont_linear_map_vsub
- \+ *lemma* const_cont_linear
- \+ *lemma* cont_linear_eq_zero_iff_exists_const
- \+ *def* cont_linear

modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* linear_eq_zero_iff_exists_const

created src/topology/algebra/continuous_affine_map.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_injective
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* congr_fun
- \+ *lemma* to_affine_map_eq_coe
- \+ *lemma* to_continuous_map_coe
- \+ *lemma* coe_to_affine_map
- \+ *lemma* coe_to_continuous_map
- \+ *lemma* to_affine_map_injective
- \+ *lemma* to_continuous_map_injective
- \+ *lemma* coe_affine_map_mk
- \+ *lemma* coe_continuous_map_mk
- \+ *lemma* coe_mk
- \+ *lemma* mk_coe
- \+ *lemma* coe_const
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *def* to_continuous_map
- \+ *def* const
- \+ *def* comp



## [2021-11-06 20:27:42](https://github.com/leanprover-community/mathlib/commit/26c0c23)
feat(algebra/homology/image_to_kernel): homology.map_iso ([#9978](https://github.com/leanprover-community/mathlib/pull/9978))
#### Estimated changes
modified src/algebra/homology/image_to_kernel.lean
- \+ *lemma* homology.map_id
- \+ *lemma* homology.comp_right_eq_comp_left
- \+ *lemma* homology.map_comp
- \+ *def* homology.map_iso



## [2021-11-06 18:49:17](https://github.com/leanprover-community/mathlib/commit/f18278d)
chore(algebra/opposites): use `injective.*` constructors ([#10200](https://github.com/leanprover-community/mathlib/pull/10200))
#### Estimated changes
modified src/algebra/opposites.lean
- \+/\- *lemma* op_sub
- \+/\- *lemma* unop_sub
- \+/\- *lemma* op_sub
- \+/\- *lemma* unop_sub



## [2021-11-06 18:49:16](https://github.com/leanprover-community/mathlib/commit/38caa50)
feat(data/nat/basic): `a < a / b * b + b` ([#10193](https://github.com/leanprover-community/mathlib/pull/10193))
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* lt_div_mul_add



## [2021-11-06 18:49:15](https://github.com/leanprover-community/mathlib/commit/ebe7951)
feat(algebra/big_operators/order): Bound on a product from a pointwise bound ([#10190](https://github.com/leanprover-community/mathlib/pull/10190))
This proves `finset.le_prod_of_forall_le` which is the dual of `finset.prod_le_of_forall_le`.
#### Estimated changes
modified src/algebra/big_operators/order.lean
- \+/\- *lemma* prod_le_of_forall_le
- \+ *lemma* le_prod_of_forall_le
- \+/\- *lemma* card_bUnion_le_card_mul
- \+/\- *lemma* prod_le_of_forall_le
- \+/\- *lemma* card_bUnion_le_card_mul



## [2021-11-06 18:49:14](https://github.com/leanprover-community/mathlib/commit/be412c3)
fix(README): update specialties of maintainers ([#10086](https://github.com/leanprover-community/mathlib/pull/10086))
#### Estimated changes
modified README.md



## [2021-11-06 18:15:19](https://github.com/leanprover-community/mathlib/commit/0c54c57)
feat(data/set/equitable): A singleton is equitable ([#10192](https://github.com/leanprover-community/mathlib/pull/10192))
Prove `set.subsingleton.equitable_on` and `set.equitable_on_singleton`.
#### Estimated changes
modified src/data/set/equitable.lean
- \+/\- *lemma* equitable_on_empty
- \+ *lemma* subsingleton.equitable_on
- \+ *lemma* equitable_on_singleton
- \+/\- *lemma* equitable_on_empty



## [2021-11-06 12:54:31](https://github.com/leanprover-community/mathlib/commit/af36f1a)
chore(algebra/group/ulift): use injective.* to define instances ([#10172](https://github.com/leanprover-community/mathlib/pull/10172))
Also rename `ulift.mul_equiv` to `mul_equiv.ulift` and add some
missing instances.
#### Estimated changes
modified src/algebra/group/ulift.lean
- \+ *def* _root_.mul_equiv.ulift
- \- *def* mul_equiv

modified src/algebra/module/ulift.lean



## [2021-11-06 11:24:11](https://github.com/leanprover-community/mathlib/commit/4b14ef4)
feat(data/fintype): instances for `infinite (α ⊕ β)` and `infinite (α × β)` ([#10196](https://github.com/leanprover-community/mathlib/pull/10196))
#### Estimated changes
modified src/data/fintype/basic.lean
- \+ *lemma* infinite_sum
- \+ *lemma* infinite_prod



## [2021-11-06 09:47:22](https://github.com/leanprover-community/mathlib/commit/239bf05)
feat(data/list/basic): list products ([#10184](https://github.com/leanprover-community/mathlib/pull/10184))
Adding a couple of lemmas about list products. The first is a simpler variant of `head_mul_tail_prod'` in the case where the list is not empty.  The other is a variant of `list.prod_ne_zero` for `list ℕ`.
#### Estimated changes
modified src/data/list/basic.lean
- \+ *lemma* nth_zero_mul_tail_prod
- \+ *lemma* head_mul_tail_prod_of_ne_nil
- \+ *lemma* prod_pos
- \- *lemma* head_mul_tail_prod'



## [2021-11-06 08:31:55](https://github.com/leanprover-community/mathlib/commit/051cb61)
feat(data/sym/sym2): Induction on `sym2` ([#10189](https://github.com/leanprover-community/mathlib/pull/10189))
A few basics about `sym2` that were blatantly missing.
#### Estimated changes
modified src/data/sym/sym2.lean



## [2021-11-06 02:12:53](https://github.com/leanprover-community/mathlib/commit/4341fff)
chore(set_theory/cardinal_ordinal): use notation ω ([#10197](https://github.com/leanprover-community/mathlib/pull/10197))
#### Estimated changes
modified src/set_theory/cardinal_ordinal.lean
- \+/\- *lemma* mul_le_max_of_omega_le_left
- \+/\- *lemma* mul_eq_max_of_omega_le_left
- \+/\- *lemma* mul_eq_left
- \+/\- *lemma* mul_eq_right
- \+/\- *lemma* mul_eq_left_iff
- \+/\- *lemma* eq_of_add_eq_of_omega_le
- \+/\- *lemma* add_eq_left
- \+/\- *lemma* add_eq_right
- \+/\- *lemma* add_eq_left_iff
- \+/\- *lemma* add_eq_right_iff
- \+/\- *lemma* add_one_eq
- \+/\- *lemma* powerlt_omega
- \+/\- *lemma* powerlt_omega_le
- \+/\- *lemma* mk_bounded_set_le_of_omega_le
- \+/\- *lemma* mk_compl_of_omega_le
- \+/\- *lemma* mk_compl_finset_of_omega_le
- \+/\- *lemma* mk_compl_eq_mk_compl_infinite
- \+/\- *lemma* mk_compl_eq_mk_compl_finite_same
- \+/\- *lemma* bit1_le_bit0
- \+/\- *lemma* bit0_lt_bit1
- \+/\- *lemma* mul_le_max_of_omega_le_left
- \+/\- *lemma* mul_eq_max_of_omega_le_left
- \+/\- *lemma* mul_eq_left
- \+/\- *lemma* mul_eq_right
- \+/\- *lemma* mul_eq_left_iff
- \+/\- *lemma* eq_of_add_eq_of_omega_le
- \+/\- *lemma* add_eq_left
- \+/\- *lemma* add_eq_right
- \+/\- *lemma* add_eq_left_iff
- \+/\- *lemma* add_eq_right_iff
- \+/\- *lemma* add_one_eq
- \+/\- *lemma* powerlt_omega
- \+/\- *lemma* powerlt_omega_le
- \+/\- *lemma* mk_bounded_set_le_of_omega_le
- \+/\- *lemma* mk_compl_of_omega_le
- \+/\- *lemma* mk_compl_finset_of_omega_le
- \+/\- *lemma* mk_compl_eq_mk_compl_infinite
- \+/\- *lemma* mk_compl_eq_mk_compl_finite_same
- \+/\- *lemma* bit1_le_bit0
- \+/\- *lemma* bit0_lt_bit1
- \+/\- *theorem* ord_is_limit
- \+/\- *theorem* aleph'_omega
- \+/\- *theorem* aleph_zero
- \+/\- *theorem* omega_le_aleph'
- \+/\- *theorem* omega_le_aleph
- \+/\- *theorem* exists_aleph
- \+/\- *theorem* mul_eq_self
- \+/\- *theorem* mul_eq_max
- \+/\- *theorem* mul_lt_of_lt
- \+/\- *theorem* add_eq_self
- \+/\- *theorem* add_eq_max
- \+/\- *theorem* add_lt_of_lt
- \+/\- *theorem* bit0_eq_self
- \+/\- *theorem* bit0_lt_omega
- \+/\- *theorem* omega_le_bit0
- \+/\- *theorem* bit1_eq_self_iff
- \+/\- *theorem* bit1_lt_omega
- \+/\- *theorem* omega_le_bit1
- \+/\- *theorem* ord_is_limit
- \+/\- *theorem* aleph'_omega
- \+/\- *theorem* aleph_zero
- \+/\- *theorem* omega_le_aleph'
- \+/\- *theorem* omega_le_aleph
- \+/\- *theorem* exists_aleph
- \+/\- *theorem* mul_eq_self
- \+/\- *theorem* mul_eq_max
- \+/\- *theorem* mul_lt_of_lt
- \+/\- *theorem* add_eq_self
- \+/\- *theorem* add_eq_max
- \+/\- *theorem* add_lt_of_lt
- \+/\- *theorem* bit0_eq_self
- \+/\- *theorem* bit0_lt_omega
- \+/\- *theorem* omega_le_bit0
- \+/\- *theorem* bit1_eq_self_iff
- \+/\- *theorem* bit1_lt_omega
- \+/\- *theorem* omega_le_bit1



## [2021-11-05 23:39:17](https://github.com/leanprover-community/mathlib/commit/8174bd0)
feat(analysis/inner_product_space/rayleigh): Rayleigh quotient produces eigenvectors ([#9840](https://github.com/leanprover-community/mathlib/pull/9840))
Define `self_adjoint` for an operator `T` to mean `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.  (This doesn't require a definition of `adjoint`, although that will come soon.). Prove that a local extremum of the Rayleigh quotient of a self-adjoint operator on the unit sphere is an eigenvector, and use this to prove that in finite dimension a self-adjoint operator has an eigenvector.
#### Estimated changes
modified src/analysis/calculus/lagrange_multipliers.lean
- \+ *lemma* is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at_1d

modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* continuous_linear_map.re_apply_inner_self_apply
- \+ *lemma* continuous_linear_map.re_apply_inner_self_continuous
- \+ *lemma* continuous_linear_map.re_apply_inner_self_smul
- \+ *lemma* is_self_adjoint_iff_bilin_form
- \+ *lemma* is_self_adjoint.conj_inner_sym
- \+ *lemma* is_self_adjoint.apply_clm
- \+ *lemma* is_self_adjoint.coe_re_apply_inner_self_apply
- \+ *def* continuous_linear_map.re_apply_inner_self
- \+ *def* is_self_adjoint

modified src/analysis/inner_product_space/calculus.lean
- \+ *lemma* has_strict_fderiv_at.inner
- \+ *lemma* has_strict_fderiv_at_norm_sq

created src/analysis/inner_product_space/rayleigh.lean
- \+ *lemma* rayleigh_smul
- \+ *lemma* image_rayleigh_eq_image_rayleigh_sphere
- \+ *lemma* supr_rayleigh_eq_supr_rayleigh_sphere
- \+ *lemma* infi_rayleigh_eq_infi_rayleigh_sphere
- \+ *lemma* has_strict_fderiv_at_re_apply_inner_self
- \+ *lemma* linearly_dependent_of_is_local_extr_on
- \+ *lemma* eq_smul_self_of_is_local_extr_on_real
- \+ *lemma* eq_smul_self_of_is_local_extr_on
- \+ *lemma* has_eigenvector_of_is_local_extr_on
- \+ *lemma* has_eigenvector_of_is_max_on
- \+ *lemma* has_eigenvector_of_is_min_on
- \+ *lemma* has_eigenvalue_supr_of_finite_dimensional
- \+ *lemma* has_eigenvalue_infi_of_finite_dimensional

modified src/order/filter/extr.lean
- \+ *lemma* is_max_on.supr_eq
- \+ *lemma* is_min_on.infi_eq



## [2021-11-05 19:40:53](https://github.com/leanprover-community/mathlib/commit/6cd6975)
feat(order/lattice): add `inf_lt_sup` ([#10178](https://github.com/leanprover-community/mathlib/pull/10178))
Also add `inf_le_sup`, `lt_or_lt_iff_ne`, and `min_lt_max`.
#### Estimated changes
modified src/order/basic.lean
- \+ *lemma* lt_or_lt_iff_ne

modified src/order/lattice.lean
- \+ *lemma* inf_le_sup
- \+ *lemma* inf_lt_sup

modified src/order/min_max.lean
- \+ *lemma* min_lt_max



## [2021-11-05 19:40:52](https://github.com/leanprover-community/mathlib/commit/85f6420)
feat(algebra/group/inj_surj): add `injective.monoid_pow` etc ([#10152](https://github.com/leanprover-community/mathlib/pull/10152))
Add versions of some constructors that take `pow`/`zpow`/`nsmul`/`zsmul` as explicit arguments.
#### Estimated changes
modified src/algebra/group/inj_surj.lean



## [2021-11-05 19:07:04](https://github.com/leanprover-community/mathlib/commit/d69501f)
feat(category_theory/limits/shapes/multiequalizer): Multi(co)equalizers ([#10169](https://github.com/leanprover-community/mathlib/pull/10169))
This PR adds another special shape to the limits library, which directly generalizes shapes for many other special limits (like pullbacks, equalizers, etc.).  A `multiequalizer` can be thought of an an equalizer of two maps between two products. This will be used later on in the context of sheafification.
I don't know if there is a standard name for the gadgets this PR introduces. I would be happy to change the names if needed.
#### Estimated changes
created src/category_theory/limits/shapes/multiequalizer.lean
- \+ *lemma* multicospan_obj_left
- \+ *lemma* multicospan_obj_right
- \+ *lemma* multicospan_map_fst
- \+ *lemma* multicospan_map_snd
- \+ *lemma* multispan_obj_left
- \+ *lemma* multispan_obj_right
- \+ *lemma* multispan_map_fst
- \+ *lemma* multispan_map_snd
- \+ *lemma* ι_eq_app_left
- \+ *lemma* app_left_fst
- \+ *lemma* app_left_snd
- \+ *lemma* condition
- \+ *lemma* π_eq_app_right
- \+ *lemma* fst_app_right
- \+ *lemma* snd_app_right
- \+ *lemma* condition
- \+ *lemma* multifork_ι
- \+ *lemma* multifork_π_app_left
- \+ *lemma* condition
- \+ *lemma* lift_ι
- \+ *lemma* hom_ext
- \+ *lemma* multicofork_π
- \+ *lemma* multicofork_ι_app_right
- \+ *lemma* condition
- \+ *lemma* π_desc
- \+ *lemma* hom_ext
- \+ *def* hom.comp
- \+ *def* hom.comp
- \+ *def* multicospan
- \+ *def* multispan
- \+ *def* multifork
- \+ *def* multicofork
- \+ *def* ι
- \+ *def* of_ι
- \+ *def* π
- \+ *def* of_π



## [2021-11-05 17:51:20](https://github.com/leanprover-community/mathlib/commit/cc59673)
chore(*complex*): add a few simp lemmas ([#10187](https://github.com/leanprover-community/mathlib/pull/10187))
#### Estimated changes
modified src/analysis/special_functions/trigonometric/basic.lean
- \+/\- *lemma* exp_pi_mul_I
- \+/\- *lemma* exp_two_pi_mul_I
- \+/\- *lemma* exp_nat_mul_two_pi_mul_I
- \+/\- *lemma* exp_int_mul_two_pi_mul_I
- \+ *lemma* exp_add_pi_mul_I
- \+ *lemma* exp_sub_pi_mul_I
- \+/\- *lemma* exp_pi_mul_I
- \+/\- *lemma* exp_two_pi_mul_I
- \+/\- *lemma* exp_nat_mul_two_pi_mul_I
- \+/\- *lemma* exp_int_mul_two_pi_mul_I

modified src/data/complex/basic.lean
- \+ *lemma* norm_sq_mk

modified src/data/complex/exponential.lean
- \+ *lemma* exp_of_real_mul_I_re
- \+ *lemma* exp_of_real_mul_I_im



## [2021-11-05 17:51:18](https://github.com/leanprover-community/mathlib/commit/a71bfdc)
feat(analysis/calculus/times_cont_diff): `equiv.prod_assoc` is smooth. ([#10165](https://github.com/leanprover-community/mathlib/pull/10165))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_prod_assoc
- \+ *lemma* times_cont_diff_prod_assoc_symm

modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* coe_prod_assoc
- \+ *lemma* coe_prod_assoc_symm



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
modified src/data/finset/locally_finite.lean
- \+/\- *lemma* Ico_filter_lt_of_le_left
- \+/\- *lemma* Ico_filter_lt_of_right_le
- \+/\- *lemma* Ico_filter_lt_of_le_right
- \+/\- *lemma* Ico_filter_le_of_le_left
- \+/\- *lemma* Ico_filter_le_of_right_le
- \+/\- *lemma* Ico_filter_le_of_left_le
- \+/\- *lemma* Ico_filter_le_left
- \+/\- *lemma* Ico_filter_lt_of_le_left
- \+/\- *lemma* Ico_filter_lt_of_right_le
- \+/\- *lemma* Ico_filter_lt_of_le_right
- \+/\- *lemma* Ico_filter_le_of_le_left
- \+/\- *lemma* Ico_filter_le_of_right_le
- \+/\- *lemma* Ico_filter_le_of_left_le
- \+/\- *lemma* Ico_filter_le_left

modified src/data/multiset/default.lean

deleted src/data/multiset/intervals.lean
- \- *lemma* add_consecutive
- \- *lemma* inter_consecutive
- \- *lemma* filter_lt_of_top_le
- \- *lemma* filter_lt_of_le_bot
- \- *lemma* filter_le_of_bot
- \- *lemma* filter_lt_of_ge
- \- *lemma* filter_lt
- \- *lemma* filter_le_of_le_bot
- \- *lemma* filter_le_of_top_le
- \- *lemma* filter_le_of_le
- \- *lemma* filter_le
- \- *theorem* map_add
- \- *theorem* map_sub
- \- *theorem* zero_bot
- \- *theorem* card
- \- *theorem* nodup
- \- *theorem* mem
- \- *theorem* eq_zero_of_le
- \- *theorem* self_eq_zero
- \- *theorem* eq_zero_iff
- \- *theorem* succ_singleton
- \- *theorem* succ_top
- \- *theorem* eq_cons
- \- *theorem* pred_singleton
- \- *theorem* not_mem_top
- \- *def* Ico

modified src/data/multiset/locally_finite.lean
- \+ *lemma* nodup_Ico
- \+ *lemma* Ico_eq_zero_iff
- \+ *lemma* Ico_eq_zero_of_le
- \+ *lemma* Ico_self
- \+ *lemma* left_mem_Icc
- \+ *lemma* left_mem_Ico
- \+ *lemma* right_mem_Icc
- \+ *lemma* right_mem_Ioc
- \+ *lemma* left_not_mem_Ioc
- \+ *lemma* left_not_mem_Ioo
- \+ *lemma* right_not_mem_Ico
- \+ *lemma* right_not_mem_Ioo
- \+ *lemma* Ico_filter_lt_of_le_left
- \+ *lemma* Ico_filter_lt_of_right_le
- \+ *lemma* Ico_filter_lt_of_le_right
- \+ *lemma* Ico_filter_le_of_le_left
- \+ *lemma* Ico_filter_le_of_right_le
- \+ *lemma* Ico_filter_le_of_left_le
- \+ *lemma* Ico_cons_right
- \+ *lemma* Ioo_cons_left
- \+ *lemma* Ico_disjoint_Ico
- \+ *lemma* Ico_inter_Ico_of_le
- \+ *lemma* Ico_filter_le_left
- \+ *lemma* Ico_subset_Ico_iff
- \+ *lemma* Ico_add_Ico_eq_Ico
- \+ *lemma* Ico_inter_Ico
- \+ *lemma* Ico_filter_lt
- \+ *lemma* Ico_filter_le
- \+ *lemma* Ico_sub_Ico_left
- \+ *lemma* Ico_sub_Ico_right
- \+ *lemma* map_add_left_Ico
- \+ *lemma* map_add_right_Ico

modified src/data/nat/interval.lean
- \+/\- *lemma* Iio_eq_range
- \+/\- *lemma* Ico_zero_eq_range
- \+/\- *lemma* Icc_succ_left
- \+/\- *lemma* Ico_succ_right
- \+/\- *lemma* Ico_succ_left
- \+/\- *lemma* Ico_succ_singleton
- \+/\- *lemma* image_sub_const_Ico
- \+/\- *lemma* range_image_pred_top_sub
- \+/\- *lemma* Iio_eq_range
- \+/\- *lemma* Ico_zero_eq_range
- \+/\- *lemma* Icc_succ_left
- \+/\- *lemma* Ico_succ_right
- \+/\- *lemma* Ico_succ_left
- \+/\- *lemma* Ico_succ_singleton
- \+/\- *lemma* image_sub_const_Ico
- \+/\- *lemma* range_image_pred_top_sub

modified src/order/locally_finite.lean
- \+ *lemma* mem_Ico
- \+/\- *lemma* finite_Icc
- \+/\- *lemma* finite_Ico
- \+/\- *lemma* finite_Ioc
- \+/\- *lemma* finite_Ioo
- \+/\- *lemma* finite_Icc
- \+/\- *lemma* finite_Ico
- \+/\- *lemma* finite_Ioc
- \+/\- *lemma* finite_Ioo
- \+ *def* Ico



## [2021-11-05 16:25:14](https://github.com/leanprover-community/mathlib/commit/5f5ce2b)
feat(combinatorics/simple_graph): adding simple_graph.support and mem_support / support_mono lemmas ([#10176](https://github.com/leanprover-community/mathlib/pull/10176))
#### Estimated changes
modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* mem_support
- \+ *lemma* support_mono
- \+ *def* support

modified src/data/rel.lean
- \+ *lemma* dom_mono



## [2021-11-05 15:19:39](https://github.com/leanprover-community/mathlib/commit/8ac2fa0)
chore(linear_algebra/affine_space/affine_map): make `affine_map.coe_sub` true by definition ([#10182](https://github.com/leanprover-community/mathlib/pull/10182))
This makes life slightly easier in some work following on from https://github.com/leanprover-community/mathlib/pull/10161
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/linear_algebra/affine_space/affine_map.lean
- \+/\- *lemma* coe_sub
- \+/\- *lemma* add_linear
- \+ *lemma* sub_linear
- \+ *lemma* neg_linear
- \+/\- *lemma* coe_sub
- \+/\- *lemma* add_linear



## [2021-11-05 15:19:38](https://github.com/leanprover-community/mathlib/commit/b22a7c7)
refactor(measure_theory/integral/bochner): remove superfluous hypothesis ([#10181](https://github.com/leanprover-community/mathlib/pull/10181))
* Remove hypothesis from `tendsto_integral_of_dominated_convergence` that was superfluous
* This results in simplifying some proofs, and removing some hypotheses from other lemmas
* Also remove some `ae_measurable` hypotheses for functions that were also assumed to be `integrable`.
#### Estimated changes
modified src/analysis/calculus/parametric_integral.lean

modified src/measure_theory/constructions/prod.lean

modified src/measure_theory/integral/bochner.lean

modified src/measure_theory/integral/integral_eq_improper.lean

modified src/measure_theory/integral/interval_integral.lean

modified src/measure_theory/integral/set_integral.lean



## [2021-11-05 15:19:37](https://github.com/leanprover-community/mathlib/commit/88b4ce7)
feat(algebra/order/with_zero): add with_zero.linear_ordered_comm_grou… ([#10180](https://github.com/leanprover-community/mathlib/pull/10180))
…p_with_zero
#### Estimated changes
modified src/algebra/order/with_zero.lean



## [2021-11-05 13:33:49](https://github.com/leanprover-community/mathlib/commit/b31af6d)
refactor(algebra/group): move `monoid.has_pow` etc to `algebra.group.defs` ([#10147](https://github.com/leanprover-community/mathlib/pull/10147))
This way we can state theorems about `pow`/`nsmul` using notation `^` and `•` right away.
Also move some `ext` lemmas to a new file and rewrite proofs using properties of `monoid_hom`s.
#### Estimated changes
modified src/algebra/algebra/subalgebra.lean

modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_zpow
- \- *lemma* zsmul_sum

modified src/algebra/group/commute.lean
- \+/\- *lemma* is_unit_mul_iff
- \+/\- *lemma* _root_.is_unit_mul_self_iff
- \+/\- *lemma* is_unit_mul_iff
- \+/\- *lemma* _root_.is_unit_mul_self_iff
- \+ *theorem* pow_right
- \+ *theorem* pow_left
- \+ *theorem* pow_pow
- \+ *theorem* self_pow
- \+ *theorem* pow_self
- \+ *theorem* pow_pow_self
- \+ *theorem* _root_.pow_succ'
- \+/\- *theorem* units_inv_right
- \+/\- *theorem* units_inv_right_iff
- \+/\- *theorem* units_inv_left
- \+ *theorem* units_inv_left_iff:
- \+/\- *theorem* units_inv_right
- \+/\- *theorem* units_inv_right_iff
- \+/\- *theorem* units_inv_left
- \- *theorem* units_inv_left_iff

modified src/algebra/group/defs.lean
- \+ *lemma* npow_eq_pow
- \+ *lemma* zpow_eq_pow
- \- *lemma* monoid.ext
- \- *lemma* npow_one
- \- *lemma* npow_add
- \- *lemma* comm_monoid.to_monoid_injective
- \- *lemma* comm_monoid.ext
- \- *lemma* left_cancel_monoid.to_monoid_injective
- \- *lemma* left_cancel_monoid.ext
- \- *lemma* right_cancel_monoid.to_monoid_injective
- \- *lemma* right_cancel_monoid.ext
- \- *lemma* cancel_monoid.to_left_cancel_monoid_injective
- \- *lemma* cancel_monoid.ext
- \- *lemma* cancel_comm_monoid.to_comm_monoid_injective
- \- *lemma* cancel_comm_monoid.ext
- \- *lemma* div_inv_monoid.ext
- \- *lemma* group.ext
- \- *lemma* comm_group.ext
- \+ *theorem* pow_zero
- \+ *theorem* pow_succ
- \+ *theorem* zpow_zero
- \+ *theorem* zpow_coe_nat
- \+ *theorem* zpow_of_nat
- \+ *theorem* zpow_neg_succ_of_nat

created src/algebra/group/ext.lean
- \+ *lemma* monoid.ext
- \+ *lemma* comm_monoid.to_monoid_injective
- \+ *lemma* comm_monoid.ext
- \+ *lemma* left_cancel_monoid.to_monoid_injective
- \+ *lemma* left_cancel_monoid.ext
- \+ *lemma* right_cancel_monoid.to_monoid_injective
- \+ *lemma* right_cancel_monoid.ext
- \+ *lemma* cancel_monoid.to_left_cancel_monoid_injective
- \+ *lemma* cancel_monoid.ext
- \+ *lemma* cancel_comm_monoid.to_comm_monoid_injective
- \+ *lemma* cancel_comm_monoid.ext
- \+ *lemma* div_inv_monoid.ext
- \+ *lemma* group.ext
- \+ *lemma* comm_group.ext

modified src/algebra/group/hom.lean
- \+ *theorem* monoid_hom.map_pow
- \+ *theorem* monoid_hom.map_zpow'
- \+ *theorem* monoid_hom.map_div'
- \+ *theorem* map_zpow

modified src/algebra/group/hom_instances.lean

modified src/algebra/group/pi.lean

modified src/algebra/group/semiconj.lean
- \+ *lemma* pow_right

modified src/algebra/group/type_tags.lean

modified src/algebra/group/ulift.lean

modified src/algebra/group_power/basic.lean
- \- *lemma* npow_eq_pow
- \- *lemma* zpow_eq_pow
- \- *lemma* pow_right
- \+/\- *theorem* pow_one
- \- *theorem* pow_right
- \- *theorem* pow_left
- \- *theorem* pow_pow
- \- *theorem* self_pow
- \- *theorem* pow_self
- \- *theorem* pow_pow_self
- \- *theorem* pow_zero
- \- *theorem* pow_succ
- \- *theorem* pow_succ'
- \+/\- *theorem* pow_one
- \- *theorem* monoid_hom.map_pow
- \- *theorem* zpow_coe_nat
- \- *theorem* zpow_of_nat
- \- *theorem* zpow_neg_succ_of_nat
- \- *theorem* zpow_zero

modified src/algebra/group_power/lemmas.lean
- \- *theorem* monoid_hom.map_zpow

modified src/algebra/opposites.lean

modified src/algebra/order/archimedean.lean

modified src/algebra/order/pi.lean

modified src/algebra/periodic.lean

modified src/algebra/ring/pi.lean

modified src/algebra/ring/ulift.lean

modified src/analysis/normed_space/basic.lean

modified src/category_theory/preadditive/schur.lean

modified src/data/finsupp/basic.lean

modified src/data/holor.lean

modified src/group_theory/group_action/defs.lean

modified src/group_theory/subgroup/basic.lean
- \+/\- *def* saturated
- \+/\- *def* saturated

modified src/group_theory/submonoid/membership.lean

modified src/linear_algebra/alternating.lean

modified src/linear_algebra/quotient.lean

modified src/ring_theory/localization.lean

modified src/tactic/abel.lean

modified src/topology/algebra/module.lean



## [2021-11-05 10:08:26](https://github.com/leanprover-community/mathlib/commit/16af388)
feat(data/quot): add `quotient.lift₂_mk` ([#10173](https://github.com/leanprover-community/mathlib/pull/10173))
#### Estimated changes
modified src/data/quot.lean
- \+ *lemma* quotient.lift₂_mk



## [2021-11-05 08:27:18](https://github.com/leanprover-community/mathlib/commit/35d3628)
chore(data/bool): add `bool.lt_iff` ([#10179](https://github.com/leanprover-community/mathlib/pull/10179))
#### Estimated changes
modified src/data/bool.lean
- \+ *lemma* lt_iff
- \+/\- *lemma* ff_lt_tt
- \+/\- *lemma* ff_lt_tt



## [2021-11-05 06:48:59](https://github.com/leanprover-community/mathlib/commit/8991f28)
feat(measure_theory/covering/vitali_family): define Vitali families ([#10057](https://github.com/leanprover-community/mathlib/pull/10057))
Vitali families are families of sets (for instance balls around each point in vector spaces) that satisfy covering theorems. Their main feature is that differentiation of measure theorems hold along Vitali families. This PR is a stub defining Vitali families, and giving examples of them thanks to the Besicovitch and Vitali covering theorems.
The differentiation theorem is left for another PR.
#### Estimated changes
modified src/data/set/pairwise.lean
- \+ *lemma* pairwise_subtype_iff_pairwise_set
- \+/\- *lemma* pairwise_disjoint_empty
- \+/\- *lemma* pairwise_disjoint_singleton
- \+/\- *lemma* pairwise_disjoint_empty
- \+/\- *lemma* pairwise_disjoint_singleton

modified src/measure_theory/covering/besicovitch.lean

modified src/measure_theory/covering/vitali.lean

created src/measure_theory/covering/vitali_family.lean
- \+ *lemma* index_subset
- \+ *lemma* covering_disjoint
- \+ *lemma* covering_disjoint_subtype
- \+ *lemma* covering_mem
- \+ *lemma* covering_mem_family
- \+ *lemma* measure_diff_bUnion
- \+ *lemma* index_countable
- \+ *lemma* measure_le_tsum_of_absolutely_continuous
- \+ *lemma* measure_le_tsum
- \+ *lemma* mem_filter_at_iff
- \+ *lemma* eventually_filter_at_iff
- \+ *lemma* eventually_filter_at_mem_sets
- \+ *lemma* frequently_filter_at_iff
- \+ *lemma* eventually_filter_at_subset_of_nhds
- \+ *lemma* fine_subfamily_on_of_frequently
- \+ *theorem* exists_disjoint_covering_ae
- \+ *def* mono
- \+ *def* fine_subfamily_on
- \+ *def* filter_at



## [2021-11-05 06:00:09](https://github.com/leanprover-community/mathlib/commit/6f9ec12)
doc(group_theory/sylow): Expand Frattini's argument docstring ([#10174](https://github.com/leanprover-community/mathlib/pull/10174))
Expands the docstring for Frattini's argument.
#### Estimated changes
modified src/group_theory/sylow.lean



## [2021-11-05 02:24:22](https://github.com/leanprover-community/mathlib/commit/8490f2a)
chore(scripts): update nolints.txt ([#10177](https://github.com/leanprover-community/mathlib/pull/10177))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2021-11-05 00:43:55](https://github.com/leanprover-community/mathlib/commit/41a820d)
feat(number_theory/lucas_primality): Add theorem for Lucas primality test ([#8820](https://github.com/leanprover-community/mathlib/pull/8820))
This is a PR for adding the [Lucas primality test](https://en.wikipedia.org/wiki/Lucas_primality_test) to mathlib. This tells us that a number `p` is prime when an element `a : zmod p` has order `p-1` .
#### Estimated changes
modified src/algebra/divisibility.lean
- \+ *lemma* dvd_iff_exists_eq_mul_left

modified src/data/nat/totient.lean
- \+ *lemma* totient_lt
- \+/\- *lemma* _root_.zmod.card_units_eq_totient
- \+ *lemma* card_units_zmod_lt_sub_one
- \+ *lemma* prime_iff_card_units
- \+/\- *lemma* _root_.zmod.card_units_eq_totient

modified src/group_theory/order_of_element.lean
- \+ *theorem* order_of_eq_of_pow_and_pow_div_prime

created src/number_theory/lucas_primality.lean
- \+ *theorem* lucas_primality



## [2021-11-04 22:36:42](https://github.com/leanprover-community/mathlib/commit/d6a57f8)
feat(data/finset/prod): When `finset.product` is nonempty ([#10170](https://github.com/leanprover-community/mathlib/pull/10170))
and two lemmas about how it interacts with the union.
#### Estimated changes
modified src/data/finset/prod.lean
- \+ *lemma* nonempty.product
- \+ *lemma* nonempty.fst
- \+ *lemma* nonempty.snd
- \+ *lemma* nonempty_product
- \+ *lemma* union_product
- \+ *lemma* product_union



## [2021-11-04 22:36:40](https://github.com/leanprover-community/mathlib/commit/b064622)
feat(data/fin/interval): Cardinality of `finset.Ixi`/`finset.Iix` in `fin` ([#10168](https://github.com/leanprover-community/mathlib/pull/10168))
This proves `(Ici a).card = n + 1 - a`, `(Ioi a).card = n - a`, `(Iic b).card = b + 1`, `(Iio b).card = b` where `a b : fin (n + 1)` (and also `a b : ℕ` for the last two).
#### Estimated changes
modified src/data/fin/interval.lean
- \+ *lemma* Ici_eq_finset_subtype
- \+ *lemma* Ioi_eq_finset_subtype
- \+ *lemma* Iic_eq_finset_subtype
- \+ *lemma* Iio_eq_finset_subtype
- \+ *lemma* map_subtype_embedding_Ici
- \+ *lemma* map_subtype_embedding_Ioi
- \+ *lemma* map_subtype_embedding_Iic
- \+ *lemma* map_subtype_embedding_Iio
- \+ *lemma* card_Ici
- \+ *lemma* card_Ioi
- \+ *lemma* card_Iic
- \+ *lemma* card_Iio
- \+ *lemma* card_fintype_Ici
- \+ *lemma* card_fintype_Ioi
- \+ *lemma* card_fintype_Iic
- \+ *lemma* card_fintype_Iio

modified src/data/nat/interval.lean
- \+ *lemma* card_Iic
- \+ *lemma* card_Iio
- \+ *lemma* card_fintype_Iic
- \+ *lemma* card_fintype_Iio



## [2021-11-04 22:36:39](https://github.com/leanprover-community/mathlib/commit/fab61c9)
chore(topology/continuous_function/bounded): add simple lemmas ([#10149](https://github.com/leanprover-community/mathlib/pull/10149))
#### Estimated changes
modified src/topology/continuous_function/bounded.lean
- \+ *lemma* coe_to_continuous_fun
- \+ *lemma* eq_of_empty
- \+/\- *lemma* dist_zero_of_empty
- \+ *lemma* lipschitz_comp_continuous
- \+ *lemma* continuous_comp_continuous
- \+ *lemma* zero_comp_continuous
- \+ *lemma* add_comp_continuous
- \+/\- *lemma* dist_zero_of_empty



## [2021-11-04 22:36:37](https://github.com/leanprover-community/mathlib/commit/466fd27)
feat(algebra/group_with_zero/basic): relax some commutativity assumptions ([#10075](https://github.com/leanprover-community/mathlib/pull/10075))
Moving some lemmas so they require group_with_zero instead of comm_group_with_zero, using the generalization linter.
#### Estimated changes
modified archive/imo/imo2008_q4.lean

modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* div_div_eq_mul_div
- \+/\- *lemma* div_div_self
- \+/\- *lemma* ne_zero_of_one_div_ne_zero
- \+/\- *lemma* eq_zero_of_one_div_eq_zero
- \+/\- *lemma* div_div_div_cancel_right
- \+/\- *lemma* div_mul_div_cancel
- \+/\- *lemma* eq_div_iff
- \+/\- *lemma* div_eq_iff
- \+/\- *lemma* div_div_eq_mul_div
- \+/\- *lemma* div_div_self
- \+/\- *lemma* ne_zero_of_one_div_ne_zero
- \+/\- *lemma* eq_zero_of_one_div_eq_zero
- \+/\- *lemma* div_div_div_cancel_right
- \+/\- *lemma* div_mul_div_cancel
- \+/\- *lemma* div_eq_iff
- \+/\- *lemma* eq_div_iff



## [2021-11-04 22:36:36](https://github.com/leanprover-community/mathlib/commit/ce0e058)
feat(data/equiv/mul_add): add lemmas about multiplication and addition on a group being bijective and finite cancel_monoid_with_zeros ([#10046](https://github.com/leanprover-community/mathlib/pull/10046))
#### Estimated changes
modified src/data/equiv/mul_add.lean
- \+ *lemma* mul_left_bijective
- \+ *lemma* mul_right_bijective
- \+ *lemma* _root_.group.mul_left_bijective
- \+ *lemma* _root_.group.mul_right_bijective
- \+ *lemma* _root_.mul_left_bijective₀
- \+ *lemma* _root_.mul_right_bijective₀

modified src/ring_theory/integral_domain.lean
- \+ *lemma* mul_right_bijective_of_fintype₀
- \+ *lemma* mul_left_bijective_of_fintype₀
- \- *lemma* mul_right_bijective₀
- \- *lemma* mul_left_bijective₀
- \+ *def* group_with_zero_of_fintype



## [2021-11-04 21:07:34](https://github.com/leanprover-community/mathlib/commit/773a7a4)
feat(analysis/ODE): prove Picard-Lindelöf/Cauchy-Lipschitz Theorem ([#9791](https://github.com/leanprover-community/mathlib/pull/9791))
#### Estimated changes
modified docs/undergrad.yaml

created src/analysis/ODE/picard_lindelof.lean
- \+ *lemma* t_min_le_t_max
- \+ *lemma* norm_le
- \+ *lemma* t_dist_nonneg
- \+ *lemma* dist_t₀_le
- \+ *lemma* proj_coe
- \+ *lemma* proj_of_mem
- \+ *lemma* continuous_proj
- \+ *lemma* uniform_inducing_to_continuous_map
- \+ *lemma* range_to_continuous_map
- \+ *lemma* map_t₀
- \+ *lemma* v_comp_apply_coe
- \+ *lemma* continuous_v_comp
- \+ *lemma* norm_v_comp_le
- \+ *lemma* dist_apply_le_dist
- \+ *lemma* dist_le_of_forall
- \+ *lemma* interval_integrable_v_comp
- \+ *lemma* next_apply
- \+ *lemma* has_deriv_within_at_next
- \+ *lemma* dist_next_apply_le_of_le
- \+ *lemma* dist_iterate_next_apply_le
- \+ *lemma* dist_iterate_next_le
- \+ *lemma* exists_contracting_iterate
- \+ *lemma* exists_fixed
- \+ *lemma* exists_solution
- \+ *lemma* exists_forall_deriv_within_Icc_eq_of_lipschitz_of_continuous
- \+ *def* t_dist
- \+ *def* proj
- \+ *def* to_continuous_map
- \+ *def* v_comp
- \+ *def* next

modified src/data/set/intervals/unordered_interval.lean
- \+ *lemma* interval_subset_Icc

modified src/topology/order.lean



## [2021-11-04 20:30:13](https://github.com/leanprover-community/mathlib/commit/74c27b2)
feat(topology/sheaves): Pullback of presheaf ([#9961](https://github.com/leanprover-community/mathlib/pull/9961))
Defined the pullback of a presheaf along a continuous map, and proved that it is adjoint to pushforwards
and it preserves stalks.
#### Estimated changes
modified src/algebraic_geometry/presheafed_space.lean

modified src/topology/sheaves/presheaf.lean
- \+ *lemma* id_inv_app
- \+/\- *lemma* id_pushforward
- \+/\- *lemma* id_pushforward
- \+ *def* pullback_obj
- \+ *def* pullback_map
- \+ *def* pullback_obj_obj_of_image_open
- \+ *def* id
- \+ *def* pullback
- \+ *def* pushforward_pullback_adjunction

modified src/topology/sheaves/stalks.lean
- \+ *def* stalk_pullback_hom
- \+ *def* germ_to_pullback_stalk
- \+ *def* stalk_pullback_inv
- \+ *def* stalk_pullback_iso



## [2021-11-04 18:49:13](https://github.com/leanprover-community/mathlib/commit/79eb934)
chore(data/mv_polynomial/basic): add `map_alg_hom_coe_ring_hom` ([#10158](https://github.com/leanprover-community/mathlib/pull/10158))
#### Estimated changes
modified src/data/mv_polynomial/basic.lean
- \+ *lemma* map_alg_hom_coe_ring_hom



## [2021-11-04 18:49:11](https://github.com/leanprover-community/mathlib/commit/11439d8)
chore(algebra/direct_sum/internal): add missing simp lemmas ([#10154](https://github.com/leanprover-community/mathlib/pull/10154))
These previously weren't needed when these were `@[reducible] def`s as `simp` saw right through them.
#### Estimated changes
modified src/algebra/direct_sum/internal.lean
- \+ *lemma* set_like.coe_galgebra_to_fun

modified src/algebra/graded_monoid.lean
- \+ *lemma* set_like.coe_ghas_one
- \+ *lemma* set_like.coe_ghas_mul
- \+ *lemma* set_like.coe_gpow



## [2021-11-04 18:49:10](https://github.com/leanprover-community/mathlib/commit/828e100)
feat(data/finset/interval): `finset α` is a locally finite order ([#9963](https://github.com/leanprover-community/mathlib/pull/9963))
#### Estimated changes
modified src/analysis/box_integral/divergence_theorem.lean

modified src/data/finset/basic.lean

created src/data/finset/interval.lean
- \+ *lemma* Icc_eq_filter_powerset
- \+ *lemma* Ico_eq_filter_ssubsets
- \+ *lemma* Ioc_eq_filter_powerset
- \+ *lemma* Ioo_eq_filter_ssubsets
- \+ *lemma* Iic_eq_powerset
- \+ *lemma* Iio_eq_ssubsets
- \+ *lemma* Icc_eq_image_powerset
- \+ *lemma* Ico_eq_image_ssubsets
- \+ *lemma* card_Icc_finset
- \+ *lemma* card_Ico_finset
- \+ *lemma* card_Ioc_finset
- \+ *lemma* card_Ioo_finset

modified src/data/finset/locally_finite.lean
- \+ *lemma* left_mem_Icc
- \+ *lemma* left_mem_Ico
- \+ *lemma* right_mem_Icc
- \+ *lemma* right_mem_Ioc
- \+ *lemma* left_not_mem_Ioc
- \+ *lemma* left_not_mem_Ioo
- \+/\- *lemma* right_not_mem_Ico
- \+ *lemma* right_not_mem_Ioo
- \+ *lemma* Icc_erase_left
- \+ *lemma* Icc_erase_right
- \+/\- *lemma* Ico_insert_right
- \+/\- *lemma* Ioo_insert_left
- \+/\- *lemma* Ico_inter_Ico_consecutive
- \+/\- *lemma* Ico_disjoint_Ico_consecutive
- \+ *lemma* card_Ico_eq_card_Icc_sub_one
- \+ *lemma* card_Ioc_eq_card_Icc_sub_one
- \+ *lemma* card_Ioo_eq_card_Ico_sub_one
- \+ *lemma* card_Ioo_eq_card_Icc_sub_two
- \+/\- *lemma* right_not_mem_Ico
- \+/\- *lemma* Ico_insert_right
- \+/\- *lemma* Ioo_insert_left
- \+/\- *lemma* Ico_inter_Ico_consecutive
- \+/\- *lemma* Ico_disjoint_Ico_consecutive

modified src/data/set/basic.lean

modified src/measure_theory/integral/divergence_theorem.lean

modified src/order/boolean_algebra.lean
- \+ *lemma* sup_sdiff_cancel_right
- \+ *lemma* sdiff_sup_cancel
- \+ *lemma* sup_le_of_le_sdiff_left
- \+ *lemma* sup_le_of_le_sdiff_right
- \+ *lemma* sdiff_le_sdiff_left
- \+ *lemma* sdiff_le_sdiff_right
- \+ *lemma* sdiff_lt_sdiff_right
- \+ *lemma* sdiff_le_sdiff_of_sup_le_sup_left
- \+ *lemma* sdiff_le_sdiff_of_sup_le_sup_right
- \+ *lemma* sup_lt_of_lt_sdiff_left
- \+ *lemma* sup_lt_of_lt_sdiff_right
- \- *lemma* sup_sdiff_of_le
- \- *lemma* sdiff_le_sdiff_self
- \- *lemma* sdiff_le_self_sdiff

modified src/order/locally_finite.lean

modified src/order/symm_diff.lean



## [2021-11-04 17:11:43](https://github.com/leanprover-community/mathlib/commit/cf2ff03)
feat(group_theory/sylow): Sylow subgroups are nontrivial! ([#10144](https://github.com/leanprover-community/mathlib/pull/10144))
These lemmas (finally!) connect the work of @ChrisHughes24 with the recent definition of Sylow subgroups, to show that Sylow subgroups are actually nontrivial!
#### Estimated changes
modified src/group_theory/sylow.lean
- \+ *lemma* pow_dvd_card_of_pow_dvd_card
- \+ *lemma* dvd_card_of_dvd_card
- \+ *lemma* ne_bot_of_dvd_card



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
modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* prod_bUnion
- \+/\- *lemma* prod_bUnion

modified src/algebra/big_operators/ring.lean

modified src/data/set/pairwise.lean
- \+/\- *lemma* pairwise_disjoint.subset
- \+ *lemma* pairwise_disjoint.mono_on
- \+ *lemma* pairwise_disjoint.mono
- \+/\- *lemma* pairwise_disjoint_empty
- \+/\- *lemma* pairwise_disjoint_singleton
- \+/\- *lemma* pairwise_disjoint_insert
- \+/\- *lemma* pairwise_disjoint.insert
- \+/\- *lemma* pairwise_disjoint.image_of_le
- \+ *lemma* inj_on.pairwise_disjoint_image
- \+/\- *lemma* pairwise_disjoint.range
- \+ *lemma* pairwise_disjoint_union
- \+ *lemma* pairwise_disjoint.union
- \+ *lemma* pairwise_disjoint_Union
- \+ *lemma* pairwise_disjoint_sUnion
- \+/\- *lemma* pairwise_disjoint.elim
- \+/\- *lemma* pairwise_disjoint.elim'
- \+/\- *lemma* pairwise_disjoint_range_singleton
- \+/\- *lemma* pairwise_disjoint_fiber
- \+/\- *lemma* pairwise_disjoint.elim_set
- \+/\- *lemma* bUnion_diff_bUnion_eq
- \+/\- *lemma* pairwise_disjoint_fiber
- \- *lemma* pairwise_disjoint_on_mono
- \+/\- *lemma* pairwise_disjoint_fiber
- \+/\- *lemma* pairwise_disjoint_fiber
- \+/\- *lemma* pairwise_disjoint.subset
- \+/\- *lemma* pairwise_disjoint_empty
- \+/\- *lemma* pairwise_disjoint_singleton
- \+/\- *lemma* pairwise_disjoint_insert
- \+/\- *lemma* pairwise_disjoint.insert
- \+/\- *lemma* pairwise_disjoint.image_of_le
- \+/\- *lemma* pairwise_disjoint.range
- \+/\- *lemma* pairwise_disjoint.elim
- \+/\- *lemma* pairwise_disjoint.elim'
- \+/\- *lemma* pairwise_disjoint_range_singleton
- \+/\- *lemma* pairwise_disjoint.elim_set
- \+/\- *lemma* bUnion_diff_bUnion_eq
- \+/\- *def* pairwise_disjoint
- \+/\- *def* pairwise_disjoint

modified src/data/setoid/partition.lean

modified src/measure_theory/covering/besicovitch.lean

modified src/measure_theory/covering/vitali.lean

modified src/ring_theory/polynomial/cyclotomic.lean

modified src/topology/bases.lean
- \+ *lemma* _root_.set.pairwise_disjoint.countable_of_is_open
- \+ *lemma* _root_.set.pairwise_disjoint.countable_of_nonempty_interior
- \- *lemma* countable_of_is_open_of_disjoint
- \- *lemma* countable_of_nonempty_interior_of_disjoint



## [2021-11-04 15:29:36](https://github.com/leanprover-community/mathlib/commit/5187a42)
feat(linear_algebra/affine_space/affine_map): decomposition of an affine map between modules as an equiv ([#10162](https://github.com/leanprover-community/mathlib/pull/10162))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* smul_linear
- \+ *def* to_const_prod_linear_map



## [2021-11-04 15:29:34](https://github.com/leanprover-community/mathlib/commit/22ec295)
chore(data/set): lemmas about `disjoint` ([#10148](https://github.com/leanprover-community/mathlib/pull/10148))
#### Estimated changes
modified src/data/set/intervals/disjoint.lean
- \+ *lemma* Ici_disjoint_Iic
- \+ *lemma* Iic_disjoint_Ici

modified src/data/set/lattice.lean
- \+ *lemma* disjoint_image_of_injective
- \+ *lemma* disjoint_preimage



## [2021-11-04 15:29:33](https://github.com/leanprover-community/mathlib/commit/69189d4)
split(data/finset/prod): split off `data.finset.basic` ([#10142](https://github.com/leanprover-community/mathlib/pull/10142))
Killing the giants. This moves `finset.product`, `finset.diag`, `finset.off_diag` to their own file, the theme being "finsets on `α × β`".
The copyright header now credits:
* Johannes Hölzl for ba95269a65a77c8ab5eae075f842fdad0c0a7aaf
* Mario Carneiro
* Oliver Nash for [#4502](https://github.com/leanprover-community/mathlib/pull/4502)
#### Estimated changes
modified src/data/finset/basic.lean
- \- *lemma* product_subset_product
- \- *lemma* product_subset_product_left
- \- *lemma* product_subset_product_right
- \- *lemma* product_bUnion
- \- *lemma* filter_product_card
- \- *lemma* empty_product
- \- *lemma* product_empty
- \- *lemma* mem_diag
- \- *lemma* mem_off_diag
- \- *lemma* diag_card
- \- *lemma* off_diag_card
- \- *lemma* diag_empty
- \- *lemma* off_diag_empty
- \- *theorem* product_val
- \- *theorem* mem_product
- \- *theorem* subset_product
- \- *theorem* product_eq_bUnion
- \- *theorem* card_product
- \- *theorem* filter_product
- \- *def* diag
- \- *def* off_diag

created src/data/finset/prod.lean
- \+ *lemma* product_val
- \+ *lemma* mem_product
- \+ *lemma* subset_product
- \+ *lemma* product_subset_product
- \+ *lemma* product_subset_product_left
- \+ *lemma* product_subset_product_right
- \+ *lemma* product_eq_bUnion
- \+ *lemma* product_bUnion
- \+ *lemma* card_product
- \+ *lemma* filter_product
- \+ *lemma* filter_product_card
- \+ *lemma* empty_product
- \+ *lemma* product_empty
- \+ *lemma* mem_diag
- \+ *lemma* mem_off_diag
- \+ *lemma* diag_card
- \+ *lemma* off_diag_card
- \+ *lemma* diag_empty
- \+ *lemma* off_diag_empty
- \+ *def* diag
- \+ *def* off_diag

modified src/data/fintype/basic.lean



## [2021-11-04 13:04:54](https://github.com/leanprover-community/mathlib/commit/de79226)
feat(ring_theory/polynomial/basic): `polynomial.ker_map_ring_hom` and `mv_polynomial.ker_map` ([#10160](https://github.com/leanprover-community/mathlib/pull/10160))
#### Estimated changes
modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* _root_.polynomial.ker_map_ring_hom
- \+ *lemma* ker_map



## [2021-11-04 13:04:53](https://github.com/leanprover-community/mathlib/commit/2129d05)
chore(measure_theory/function/special_functions): import inner_product_space.basic instead of inner_product_space.calculus ([#10159](https://github.com/leanprover-community/mathlib/pull/10159))
Right now this changes almost nothing because other imports like `analysis.special_functions.pow` depend on calculus, but I am changing that in other PRs. `measure_theory/function/special_functions` will soon not depend on calculus at all.
#### Estimated changes
modified src/measure_theory/function/special_functions.lean



## [2021-11-04 13:04:51](https://github.com/leanprover-community/mathlib/commit/b890836)
chore(analysis/calculus/times_cont_diff): rename `linear_isometry_map.times_cont_diff`; drop `_map` ([#10155](https://github.com/leanprover-community/mathlib/pull/10155))
I think the old name is a typo; the new name enables dot notation.
#### Estimated changes
modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* linear_isometry.times_cont_diff
- \- *lemma* linear_isometry_map.times_cont_diff



## [2021-11-04 13:04:50](https://github.com/leanprover-community/mathlib/commit/3cbe0fe)
feat(linear_algebra/matrix/nonsingular_inverse): determinant of inverse is inverse of determinant ([#10038](https://github.com/leanprover-community/mathlib/pull/10038))
#### Estimated changes
modified src/algebra/group_power/basic.lean
- \+ *theorem* inv_pow_sub

modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* is_unit.ring_inverse
- \+ *lemma* is_unit_ring_inverse

modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* conj_transpose_nonsing_inv
- \+ *lemma* det_nonsing_inv_mul_det
- \+ *lemma* det_nonsing_inv
- \+/\- *lemma* is_unit_nonsing_inv_det_iff
- \+ *lemma* nonsing_inv_eq_ring_inverse
- \- *lemma* nonsing_inv_det
- \+/\- *lemma* is_unit_nonsing_inv_det_iff



## [2021-11-04 13:04:48](https://github.com/leanprover-community/mathlib/commit/17afc5c)
feat(topology/algebra/group_with_zero): continuity lemma for division ([#9959](https://github.com/leanprover-community/mathlib/pull/9959))
* This even applies when dividing by `0`.
* From the sphere eversion project.
* This PR mentions `filter.tendsto_prod_top_iff` which is added by [#9958](https://github.com/leanprover-community/mathlib/pull/9958)
#### Estimated changes
modified src/order/filter/basic.lean
- \+ *lemma* prod_top

modified src/topology/algebra/group_with_zero.lean
- \+ *lemma* continuous_at.comp_div_cases
- \+ *lemma* continuous.comp_div_cases



## [2021-11-04 11:24:16](https://github.com/leanprover-community/mathlib/commit/211bdff)
feat(data/nat/choose/basic): add some inequalities showing that choose is monotonic in the first argument ([#10102](https://github.com/leanprover-community/mathlib/pull/10102))
From flt-regular
#### Estimated changes
modified src/data/nat/choose/basic.lean
- \+ *lemma* choose_le_succ
- \+ *lemma* choose_le_add
- \+ *lemma* choose_le_choose
- \+ *lemma* choose_mono



## [2021-11-04 11:24:14](https://github.com/leanprover-community/mathlib/commit/1f0d878)
feat(data/list): standardize list prefixes and suffixes ([#10052](https://github.com/leanprover-community/mathlib/pull/10052))
#### Estimated changes
modified src/data/list/basic.lean
- \- *lemma* mem_of_mem_drop
- \- *lemma* tail_sublist
- \- *lemma* mem_of_mem_tail
- \+ *theorem* take_sublist
- \+ *theorem* take_subset
- \+ *theorem* mem_of_mem_take
- \+ *theorem* drop_sublist
- \+ *theorem* drop_subset
- \+ *theorem* mem_of_mem_drop
- \+ *theorem* init_prefix
- \+ *theorem* init_sublist
- \+ *theorem* init_subset
- \+ *theorem* mem_of_mem_init
- \+ *theorem* tail_sublist
- \+ *theorem* mem_of_mem_tail



## [2021-11-04 11:24:13](https://github.com/leanprover-community/mathlib/commit/4c0b6ad)
feat(topology/homotopy/basic): add `homotopic` for `continuous_map`s. ([#9865](https://github.com/leanprover-community/mathlib/pull/9865))
#### Estimated changes
modified src/topology/homotopy/basic.lean
- \+ *lemma* refl
- \+ *lemma* symm
- \+ *lemma* trans
- \+ *lemma* hcomp
- \+ *lemma* equivalence
- \+ *lemma* refl
- \+ *lemma* symm
- \+ *lemma* trans
- \+ *lemma* refl
- \+ *lemma* symm
- \+ *lemma* trans
- \+ *lemma* equivalence
- \+ *def* hcomp
- \+ *def* homotopic
- \+ *def* homotopic_with
- \+ *def* homotopic_rel

modified src/topology/homotopy/path.lean



## [2021-11-04 09:43:52](https://github.com/leanprover-community/mathlib/commit/d219e6b)
chore(data/equiv/mul_add): DRY ([#10150](https://github.com/leanprover-community/mathlib/pull/10150))
use `units.mul_left`/`units.mul_right` to define
`equiv.mul_left₀`/`equiv.mul_right₀`.
#### Estimated changes
modified src/data/equiv/mul_add.lean



## [2021-11-04 09:43:51](https://github.com/leanprover-community/mathlib/commit/76ba1b6)
chore(ring_theory/finiteness): make `finite_presentation.{quotient,mv_polynomial}` protected ([#10091](https://github.com/leanprover-community/mathlib/pull/10091))
This lets us clean up some `_root_`s
This also golfs a proof
#### Estimated changes
modified src/ring_theory/finiteness.lean
- \- *lemma* mv_polynomial
- \- *lemma* quotient



## [2021-11-04 07:56:27](https://github.com/leanprover-community/mathlib/commit/8658f40)
feat(algebra/group_power/order): Sign of an odd/even power without linearity ([#10122](https://github.com/leanprover-community/mathlib/pull/10122))
This proves that `a < 0 → 0 < a ^ bit0 n` and `a < 0 → a ^ bit1 n < 0` in an `ordered_semiring`.
#### Estimated changes
modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* pow_lt_pow_of_lt_one
- \+/\- *lemma* pow_lt_pow_iff_of_lt_one
- \+/\- *lemma* pow_le_pow_of_le_one
- \+/\- *lemma* pow_le_of_le_one
- \+/\- *lemma* sq_le
- \+ *lemma* odd.strict_mono_pow
- \+/\- *lemma* pow_lt_pow_of_lt_one
- \+/\- *lemma* pow_lt_pow_iff_of_lt_one
- \+/\- *lemma* pow_le_pow_of_le_one
- \+/\- *lemma* pow_le_of_le_one
- \+/\- *lemma* sq_le
- \+/\- *theorem* one_add_mul_le_pow'
- \+/\- *theorem* one_add_mul_le_pow'

modified src/algebra/group_power/order.lean
- \+/\- *lemma* pow_lt_one
- \+/\- *lemma* pow_mono
- \+/\- *lemma* strict_mono_pow
- \+/\- *lemma* pow_lt_pow
- \+/\- *lemma* pow_lt_pow_iff
- \+/\- *lemma* one_lt_pow
- \+/\- *lemma* pow_le_one
- \+ *lemma* sq_pos_of_pos
- \+ *lemma* sq_pos_of_neg
- \+ *lemma* pow_bit0_pos_of_neg
- \+ *lemma* pow_bit1_neg
- \+/\- *lemma* pow_lt_one
- \+/\- *lemma* pow_mono
- \+/\- *lemma* strict_mono_pow
- \+/\- *lemma* pow_lt_pow
- \+/\- *lemma* pow_lt_pow_iff
- \+/\- *lemma* one_lt_pow
- \+/\- *lemma* pow_le_one
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_nonneg
- \+/\- *theorem* pow_add_pow_le
- \+/\- *theorem* pow_lt_pow_of_lt_left
- \+/\- *theorem* strict_mono_on_pow
- \+/\- *theorem* one_le_pow_of_one_le
- \+/\- *theorem* pow_le_pow
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_nonneg
- \+/\- *theorem* pow_add_pow_le
- \+/\- *theorem* pow_lt_pow_of_lt_left
- \+/\- *theorem* strict_mono_on_pow
- \+/\- *theorem* one_le_pow_of_one_le
- \+/\- *theorem* pow_le_pow



## [2021-11-04 02:36:27](https://github.com/leanprover-community/mathlib/commit/4770a6a)
chore(scripts): update nolints.txt ([#10146](https://github.com/leanprover-community/mathlib/pull/10146))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/style-exceptions.txt



## [2021-11-04 00:15:53](https://github.com/leanprover-community/mathlib/commit/0fac080)
refactor(analysis/calculus/mean_value): Remove useless hypotheses ([#10129](https://github.com/leanprover-community/mathlib/pull/10129))
Because the junk value of `deriv` is `0`, assuming `∀ x, 0 < deriv f x` implies that `f` is derivable. We thus remove all those redundant derivability assumptions.
#### Estimated changes
modified src/analysis/calculus/deriv.lean
- \+ *lemma* differentiable_within_at_of_deriv_within_ne_zero
- \+ *lemma* differentiable_at_of_deriv_ne_zero

modified src/analysis/calculus/mean_value.lean
- \+/\- *theorem* strict_mono_of_deriv_pos
- \+/\- *theorem* strict_anti_of_deriv_neg
- \+/\- *theorem* strict_mono_of_deriv_pos
- \+/\- *theorem* strict_anti_of_deriv_neg

modified src/analysis/special_functions/trigonometric/deriv.lean



## [2021-11-03 22:10:14](https://github.com/leanprover-community/mathlib/commit/fed57b5)
refactor(algebra/direct_sum): rework internally-graded objects ([#10127](https://github.com/leanprover-community/mathlib/pull/10127))
This is a replacement for the `graded_ring.core` typeclass in [#10115](https://github.com/leanprover-community/mathlib/pull/10115), which is called `set_like.graded_monoid` here. The advantage of this approach is that we can use the same typeclass for graded semirings, graded rings, and graded algebras.
Largely, this change replaces a bunch of `def`s with `instances`, by bundling up the arguments to those defs to a new typeclass. This seems to make life easier for the few global `gmonoid` instance we already provide for direct sums of submodules, suggesting this API change is a useful one.
In principle the new `[set_like.graded_monoid A]` typeclass is useless, as the same effect can be achieved with `[set_like.has_graded_one A] [set_like.has_graded_mul A]`; pragmatically though this is painfully verbose, and probably results in larger term sizes. We can always remove it later if it causes problems.
#### Estimated changes
modified src/algebra/direct_sum/algebra.lean

created src/algebra/direct_sum/internal.lean
- \+ *lemma* direct_sum.submonoid_coe_ring_hom_of
- \+ *lemma* direct_sum.subgroup_coe_ring_hom_of
- \+ *lemma* direct_sum.submodule_coe_alg_hom_of
- \+ *def* direct_sum.submonoid_coe_ring_hom
- \+ *def* direct_sum.subgroup_coe_ring_hom
- \+ *def* direct_sum.submodule_coe_alg_hom

modified src/algebra/direct_sum/ring.lean
- \- *def* gsemiring.of_add_submonoids
- \- *def* gcomm_semiring.of_add_submonoids
- \- *def* gsemiring.of_add_subgroups
- \- *def* gcomm_semiring.of_add_subgroups
- \- *def* gsemiring.of_submodules
- \- *def* gcomm_semiring.of_submodules

modified src/algebra/graded_monoid.lean
- \- *def* ghas_one.of_subobjects
- \- *def* ghas_mul.of_subobjects
- \- *def* gmonoid.of_subobjects
- \- *def* gcomm_monoid.of_subobjects

modified src/algebra/monoid_algebra/grading.lean

modified src/ring_theory/polynomial/homogeneous.lean



## [2021-11-03 20:00:44](https://github.com/leanprover-community/mathlib/commit/6433c1c)
feat(group_theory/sylow): Sylow subgroups are isomorphic ([#10059](https://github.com/leanprover-community/mathlib/pull/10059))
Constructs `sylow.mul_equiv`.
#### Estimated changes
modified src/group_theory/subgroup/pointwise.lean
- \+ *def* equiv_smul

modified src/group_theory/submonoid/operations.lean

modified src/group_theory/sylow.lean
- \+ *def* sylow.equiv_smul



## [2021-11-03 20:00:42](https://github.com/leanprover-community/mathlib/commit/5541b25)
refactor(group_theory/complement): Introduce abbreviation for subgroups ([#10009](https://github.com/leanprover-community/mathlib/pull/10009))
Introduces abbreviation for `is_complement (H : set G) (K : set G)`.
#### Estimated changes
modified src/group_theory/complement.lean
- \+ *lemma* is_complement'_def
- \+ *lemma* is_complement'.symm
- \+ *lemma* is_complement'_comm
- \+ *lemma* is_complement'.card_mul
- \+ *lemma* is_complement'.disjoint
- \+ *lemma* is_complement'_of_card_mul_and_disjoint
- \+ *lemma* is_complement'_iff_card_mul_and_disjoint
- \+ *lemma* is_complement'_of_coprime
- \- *lemma* is_complement.symm
- \- *lemma* is_complement_comm
- \- *lemma* is_complement.card_mul
- \- *lemma* is_complement.disjoint
- \- *lemma* is_complement_of_card_mul_and_disjoint
- \- *lemma* is_complement_iff_card_mul_and_disjoint
- \- *lemma* is_complement_of_coprime

modified src/group_theory/schur_zassenhaus.lean
- \+ *lemma* is_complement'_stabilizer_of_coprime
- \- *lemma* is_complement_stabilizer_of_coprime
- \+ *theorem* exists_right_complement'_of_coprime
- \+ *theorem* exists_left_complement'_of_coprime
- \- *theorem* exists_right_complement_of_coprime
- \- *theorem* exists_left_complement_of_coprime



## [2021-11-03 17:56:43](https://github.com/leanprover-community/mathlib/commit/3a0b0d1)
chore(order/lattice): add `exists_lt_of_sup/inf` ([#10133](https://github.com/leanprover-community/mathlib/pull/10133))
#### Estimated changes
modified src/order/lattice.lean
- \+ *theorem* exists_lt_of_sup
- \+ *theorem* exists_lt_of_inf



## [2021-11-03 17:56:42](https://github.com/leanprover-community/mathlib/commit/8f7ffec)
chore(analysis/special_functions/trigonometric/inverse): move results about derivatives to a new file ([#10110](https://github.com/leanprover-community/mathlib/pull/10110))
This is part of a refactor of the `analysis/special_functions` folder, in which I will isolate all lemmas about derivatives. The result will be a definition of Lp spaces that does not import derivatives.
#### Estimated changes
modified src/analysis/special_functions/complex/log.lean

modified src/analysis/special_functions/trigonometric/inverse.lean
- \- *lemma* deriv_arcsin_aux
- \- *lemma* has_strict_deriv_at_arcsin
- \- *lemma* has_deriv_at_arcsin
- \- *lemma* times_cont_diff_at_arcsin
- \- *lemma* has_deriv_within_at_arcsin_Ici
- \- *lemma* has_deriv_within_at_arcsin_Iic
- \- *lemma* differentiable_within_at_arcsin_Ici
- \- *lemma* differentiable_within_at_arcsin_Iic
- \- *lemma* differentiable_at_arcsin
- \- *lemma* deriv_arcsin
- \- *lemma* differentiable_on_arcsin
- \- *lemma* times_cont_diff_on_arcsin
- \- *lemma* times_cont_diff_at_arcsin_iff
- \- *lemma* has_strict_deriv_at_arccos
- \- *lemma* has_deriv_at_arccos
- \- *lemma* times_cont_diff_at_arccos
- \- *lemma* has_deriv_within_at_arccos_Ici
- \- *lemma* has_deriv_within_at_arccos_Iic
- \- *lemma* differentiable_within_at_arccos_Ici
- \- *lemma* differentiable_within_at_arccos_Iic
- \- *lemma* differentiable_at_arccos
- \- *lemma* deriv_arccos
- \- *lemma* differentiable_on_arccos
- \- *lemma* times_cont_diff_on_arccos
- \- *lemma* times_cont_diff_at_arccos_iff

created src/analysis/special_functions/trigonometric/inverse_deriv.lean
- \+ *lemma* deriv_arcsin_aux
- \+ *lemma* has_strict_deriv_at_arcsin
- \+ *lemma* has_deriv_at_arcsin
- \+ *lemma* times_cont_diff_at_arcsin
- \+ *lemma* has_deriv_within_at_arcsin_Ici
- \+ *lemma* has_deriv_within_at_arcsin_Iic
- \+ *lemma* differentiable_within_at_arcsin_Ici
- \+ *lemma* differentiable_within_at_arcsin_Iic
- \+ *lemma* differentiable_at_arcsin
- \+ *lemma* deriv_arcsin
- \+ *lemma* differentiable_on_arcsin
- \+ *lemma* times_cont_diff_on_arcsin
- \+ *lemma* times_cont_diff_at_arcsin_iff
- \+ *lemma* has_strict_deriv_at_arccos
- \+ *lemma* has_deriv_at_arccos
- \+ *lemma* times_cont_diff_at_arccos
- \+ *lemma* has_deriv_within_at_arccos_Ici
- \+ *lemma* has_deriv_within_at_arccos_Iic
- \+ *lemma* differentiable_within_at_arccos_Ici
- \+ *lemma* differentiable_within_at_arccos_Iic
- \+ *lemma* differentiable_at_arccos
- \+ *lemma* deriv_arccos
- \+ *lemma* differentiable_on_arccos
- \+ *lemma* times_cont_diff_on_arccos
- \+ *lemma* times_cont_diff_at_arccos_iff

modified src/data/complex/basic.lean
- \+/\- *lemma* conj_of_real
- \+/\- *lemma* conj_bit0
- \+/\- *lemma* conj_bit1
- \+/\- *lemma* conj_of_real
- \+/\- *lemma* conj_bit0
- \+/\- *lemma* conj_bit1

modified src/geometry/euclidean/basic.lean



## [2021-11-03 17:56:41](https://github.com/leanprover-community/mathlib/commit/00a1022)
chore(logic/relation): rename to permit dot notation ([#10105](https://github.com/leanprover-community/mathlib/pull/10105))
#### Estimated changes
modified src/category_theory/is_connected.lean

modified src/category_theory/limits/types.lean

modified src/data/pfunctor/multivariate/M.lean

modified src/group_theory/free_group.lean

modified src/logic/relation.lean
- \+ *lemma* trans_gen.lift
- \+ *lemma* trans_gen.lift'
- \+ *lemma* trans_gen.closed
- \+ *lemma* refl_trans_gen.lift
- \+ *lemma* refl_trans_gen.mono
- \+ *lemma* refl_trans_gen.lift'
- \+ *lemma* equivalence.eqv_gen_iff
- \+ *lemma* equivalence.eqv_gen_eq
- \+ *lemma* eqv_gen.mono
- \- *lemma* trans_gen_lift
- \- *lemma* trans_gen_lift'
- \- *lemma* trans_gen_closed
- \- *lemma* refl_trans_gen_lift
- \- *lemma* refl_trans_gen_mono
- \- *lemma* refl_trans_gen_lift'
- \- *lemma* eqv_gen_iff_of_equivalence
- \- *lemma* eqv_gen_mono
- \- *lemma* eqv_gen_eq_of_equivalence

modified test/qpf.lean



## [2021-11-03 17:56:40](https://github.com/leanprover-community/mathlib/commit/6993e6f)
feat(measure_theory/constructions/borel_space): decomposing the measure of a set into slices ([#10096](https://github.com/leanprover-community/mathlib/pull/10096))
Also add the fact that `μ (to_measurable μ t ∩ s) = μ (t ∩ s)`, and useful variations around this fact.
#### Estimated changes
modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* measure_eq_measure_preimage_add_measure_tsum_Ico_zpow

modified src/measure_theory/measure/finite_measure_weak_convergence.lean

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_inter_eq_of_measure_eq
- \+ *lemma* measure_to_measurable_inter
- \+ *lemma* measure_eq_left_of_subset_of_measure_add_eq
- \+ *lemma* measure_eq_right_of_subset_of_measure_add_eq
- \+ *lemma* measure_to_measurable_add_inter_left
- \+ *lemma* measure_to_measurable_add_inter_right
- \+/\- *theorem* smul_apply
- \+ *theorem* coe_nnreal_smul_apply
- \+/\- *theorem* smul_apply

modified src/measure_theory/measure/measure_space_def.lean

modified src/measure_theory/measure/regular.lean
- \+ *lemma* _root_.set.exists_is_open_le_add



## [2021-11-03 17:56:38](https://github.com/leanprover-community/mathlib/commit/b51f18f)
feat(topology): properties about intervals and paths ([#9914](https://github.com/leanprover-community/mathlib/pull/9914))
* From the sphere eversion project
* Properties about paths, the interval, and `proj_Icc`
#### Estimated changes
modified src/analysis/special_functions/trigonometric/inverse.lean

modified src/data/set/intervals/proj_Icc.lean
- \+ *lemma* proj_Icc_eq_left
- \+ *lemma* proj_Icc_eq_right

modified src/topology/algebra/ordered/proj_Icc.lean
- \+ *lemma* filter.tendsto.Icc_extend
- \+/\- *lemma* continuous.Icc_extend
- \+ *lemma* continuous.Icc_extend'
- \+ *lemma* continuous_at.Icc_extend
- \+/\- *lemma* continuous.Icc_extend

modified src/topology/path_connected.lean
- \+/\- *lemma* refl_range
- \+/\- *lemma* refl_symm
- \+/\- *lemma* symm_range
- \+ *lemma* _root_.continuous.path_extend
- \+ *lemma* _root_.filter.tendsto.path_extend
- \+ *lemma* _root_.continuous_at.path_extend
- \+/\- *lemma* refl_range
- \+/\- *lemma* refl_symm
- \+/\- *lemma* symm_range

modified src/topology/unit_interval.lean
- \+ *lemma* coe_eq_zero
- \+ *lemma* coe_ne_zero
- \+ *lemma* coe_eq_one
- \+ *lemma* coe_ne_one
- \+ *lemma* mul_mem
- \+ *lemma* coe_mul
- \+ *lemma* mul_le_left
- \+ *lemma* mul_le_right
- \+ *lemma* nonneg'
- \+ *lemma* le_one'
- \+ *lemma* proj_Icc_eq_zero
- \+ *lemma* proj_Icc_eq_one



## [2021-11-03 16:54:02](https://github.com/leanprover-community/mathlib/commit/8d52be4)
feat(measure_theory/function/ae_measurable_order): an ae measurability criterion for ennreal-valued functions ([#10072](https://github.com/leanprover-community/mathlib/pull/10072))
#### Estimated changes
created src/measure_theory/function/ae_measurable_order.lean
- \+ *theorem* measure_theory.ae_measurable_of_exist_almost_disjoint_supersets
- \+ *theorem* ennreal.ae_measurable_of_exist_almost_disjoint_supersets

modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* is_open.exists_Ioo_subset
- \+ *lemma* dense_iff_forall_lt_exists_mem



## [2021-11-03 16:10:04](https://github.com/leanprover-community/mathlib/commit/4f033b7)
feat(analysis/seminorm): define the Minkowski functional ([#9097](https://github.com/leanprover-community/mathlib/pull/9097))
This defines the gauge of a set, aka the Minkowski functional, in a vector space over a real normed field.
#### Estimated changes
modified src/analysis/seminorm.lean
- \+ *lemma* balanced.subset_smul
- \+ *lemma* balanced.smul_eq
- \+ *lemma* absorbent.subset
- \+/\- *lemma* absorbent_iff_forall_absorbs_singleton
- \+ *lemma* absorbent_iff_nonneg_lt
- \+ *lemma* ext
- \+ *lemma* absorbent_ball_zero
- \+ *lemma* absorbent_ball
- \+ *lemma* symmetric_ball_zero
- \+ *lemma* convex_ball
- \+ *lemma* gauge_def
- \+ *lemma* gauge_def'
- \+ *lemma* absorbent.gauge_set_nonempty
- \+ *lemma* exists_lt_of_gauge_lt
- \+ *lemma* gauge_zero
- \+ *lemma* gauge_nonneg
- \+ *lemma* gauge_neg
- \+ *lemma* gauge_le_of_mem
- \+ *lemma* gauge_le_one_eq'
- \+ *lemma* gauge_le_one_eq
- \+ *lemma* gauge_lt_one_eq'
- \+ *lemma* gauge_lt_one_eq
- \+ *lemma* gauge_lt_one_subset_self
- \+ *lemma* gauge_le_one_of_mem
- \+ *lemma* self_subset_gauge_le_one
- \+ *lemma* convex.gauge_le_one
- \+ *lemma* interior_subset_gauge_lt_one
- \+ *lemma* gauge_lt_one_eq_self_of_open
- \+ *lemma* gauge_lt_one_of_mem_of_open
- \+ *lemma* one_le_gauge_of_not_mem
- \+ *lemma* gauge_smul_of_nonneg
- \+ *lemma* gauge_smul
- \+ *lemma* gauge_add_le
- \+ *lemma* seminorm.gauge_ball
- \+ *lemma* seminorm.gauge_seminorm_ball
- \+/\- *lemma* absorbent_iff_forall_absorbs_singleton
- \+/\- *def* absorbs
- \+/\- *def* absorbent
- \+ *def* gauge
- \+ *def* gauge_seminorm
- \+/\- *def* absorbs
- \+/\- *def* absorbent



## [2021-11-03 14:39:55](https://github.com/leanprover-community/mathlib/commit/95cdeba)
doc(linear_algebra): fix wrong docstring ([#10139](https://github.com/leanprover-community/mathlib/pull/10139))
#### Estimated changes
modified src/linear_algebra/prod.lean



## [2021-11-03 14:39:53](https://github.com/leanprover-community/mathlib/commit/2b87435)
feat(ring_theory/trace): remove a useless assumption ([#10138](https://github.com/leanprover-community/mathlib/pull/10138))
We remove an assumption that is always true.
#### Estimated changes
modified src/ring_theory/trace.lean



## [2021-11-03 14:39:52](https://github.com/leanprover-community/mathlib/commit/93cec25)
chore(*): replace `exact calc` by `calc` ([#10137](https://github.com/leanprover-community/mathlib/pull/10137))
This PR is the result of a sed script that replaces
* `exact calc` by `calc`
* `refine calc` by `calc`
#### Estimated changes
modified src/analysis/inner_product_space/projection.lean

modified src/data/complex/exponential.lean

modified src/data/nat/log.lean

modified src/group_theory/group_action/basic.lean

modified src/order/filter/pointwise.lean

modified src/set_theory/ordinal_notation.lean

modified src/topology/continuous_function/bounded.lean



## [2021-11-03 13:35:53](https://github.com/leanprover-community/mathlib/commit/eaf2a16)
fix(scripts/lint-style.py): typo in error reporting ([#10135](https://github.com/leanprover-community/mathlib/pull/10135))
#### Estimated changes
modified scripts/lint-style.py



## [2021-11-03 13:35:52](https://github.com/leanprover-community/mathlib/commit/1e7f3ca)
feat(data/zmod/basic): add nat_coe_eq_nat_coe_iff' ([#10128](https://github.com/leanprover-community/mathlib/pull/10128))
To match the int version, from flt-regular
#### Estimated changes
modified src/data/zmod/basic.lean
- \+ *lemma* nat_coe_eq_nat_coe_iff'



## [2021-11-03 09:01:33](https://github.com/leanprover-community/mathlib/commit/e5c66a0)
chore(topology/continuous_function/bounded): add `comp_continuous` ([#10134](https://github.com/leanprover-community/mathlib/pull/10134))
#### Estimated changes
modified src/topology/continuous_function/bounded.lean
- \+ *def* comp_continuous
- \+ *def* restrict



## [2021-11-03 07:31:37](https://github.com/leanprover-community/mathlib/commit/e5acda4)
chore(order/conditionally_complete_lattice): drop an unneeded `nonempty` assumption ([#10132](https://github.com/leanprover-community/mathlib/pull/10132))
#### Estimated changes
modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* monotone.csupr_mem_Inter_Icc_of_antitone
- \+/\- *lemma* csupr_mem_Inter_Icc_of_antitone_Icc
- \+/\- *lemma* monotone.csupr_mem_Inter_Icc_of_antitone
- \+/\- *lemma* csupr_mem_Inter_Icc_of_antitone_Icc



## [2021-11-03 02:56:05](https://github.com/leanprover-community/mathlib/commit/5f2e527)
chore(scripts): update nolints.txt ([#10130](https://github.com/leanprover-community/mathlib/pull/10130))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/style-exceptions.txt



## [2021-11-02 23:57:01](https://github.com/leanprover-community/mathlib/commit/123db5e)
feat(linear_algebra/determinant): basis.det_ne_zero ([#10126](https://github.com/leanprover-community/mathlib/pull/10126))
Add the trivial lemma that the determinant with respect to a basis is
not the zero map (if the ring is nontrivial).
#### Estimated changes
modified src/linear_algebra/determinant.lean
- \+ *lemma* basis.det_ne_zero



## [2021-11-02 23:57:00](https://github.com/leanprover-community/mathlib/commit/86ed02f)
chore(algebra/order/floor): add a few trivial lemmas ([#10120](https://github.com/leanprover-community/mathlib/pull/10120))
#### Estimated changes
modified src/algebra/order/floor.lean
- \+ *lemma* fract_add_int
- \+ *lemma* fract_sub_int
- \+ *lemma* self_sub_fract
- \+ *lemma* fract_sub_self
- \+ *lemma* fract_eq_self
- \+/\- *lemma* ceil_add_one
- \+/\- *lemma* ceil_sub_int
- \+ *lemma* ceil_sub_one
- \+/\- *lemma* ceil_add_one
- \+/\- *lemma* ceil_sub_int



## [2021-11-02 23:56:58](https://github.com/leanprover-community/mathlib/commit/1dec85c)
doc(topology): three module docstrings ([#10107](https://github.com/leanprover-community/mathlib/pull/10107))
#### Estimated changes
modified src/topology/algebra/group_completion.lean

modified src/topology/algebra/uniform_ring.lean

modified src/topology/category/Top/open_nhds.lean



## [2021-11-02 21:57:35](https://github.com/leanprover-community/mathlib/commit/d49636e)
doc(topology/open_subgroup): add module docstring ([#10111](https://github.com/leanprover-community/mathlib/pull/10111))
Also add a lattice instance.
#### Estimated changes
modified src/topology/algebra/open_subgroup.lean



## [2021-11-02 21:57:34](https://github.com/leanprover-community/mathlib/commit/70ed9dc)
chore(analysis/special_functions/trigonometric/basic): move results about derivatives to a new file ([#10109](https://github.com/leanprover-community/mathlib/pull/10109))
This is part of a refactor of the `analysis/special_functions` folder, in which I will isolate all lemmas about derivatives. The result will be a definition of Lp spaces that does not import derivatives.
#### Estimated changes
modified src/analysis/special_functions/arsinh.lean

modified src/analysis/special_functions/trigonometric/basic.lean
- \- *lemma* has_strict_deriv_at_sin
- \- *lemma* has_deriv_at_sin
- \- *lemma* times_cont_diff_sin
- \- *lemma* differentiable_sin
- \- *lemma* differentiable_at_sin
- \- *lemma* deriv_sin
- \- *lemma* has_strict_deriv_at_cos
- \- *lemma* has_deriv_at_cos
- \- *lemma* times_cont_diff_cos
- \- *lemma* differentiable_cos
- \- *lemma* differentiable_at_cos
- \- *lemma* deriv_cos
- \- *lemma* deriv_cos'
- \- *lemma* has_strict_deriv_at_sinh
- \- *lemma* has_deriv_at_sinh
- \- *lemma* times_cont_diff_sinh
- \- *lemma* differentiable_sinh
- \- *lemma* differentiable_at_sinh
- \- *lemma* deriv_sinh
- \- *lemma* has_strict_deriv_at_cosh
- \- *lemma* has_deriv_at_cosh
- \- *lemma* times_cont_diff_cosh
- \- *lemma* differentiable_cosh
- \- *lemma* differentiable_at_cosh
- \- *lemma* deriv_cosh
- \- *lemma* has_strict_deriv_at.ccos
- \- *lemma* has_deriv_at.ccos
- \- *lemma* has_deriv_within_at.ccos
- \- *lemma* deriv_within_ccos
- \- *lemma* deriv_ccos
- \- *lemma* has_strict_deriv_at.csin
- \- *lemma* has_deriv_at.csin
- \- *lemma* has_deriv_within_at.csin
- \- *lemma* deriv_within_csin
- \- *lemma* deriv_csin
- \- *lemma* has_strict_deriv_at.ccosh
- \- *lemma* has_deriv_at.ccosh
- \- *lemma* has_deriv_within_at.ccosh
- \- *lemma* deriv_within_ccosh
- \- *lemma* deriv_ccosh
- \- *lemma* has_strict_deriv_at.csinh
- \- *lemma* has_deriv_at.csinh
- \- *lemma* has_deriv_within_at.csinh
- \- *lemma* deriv_within_csinh
- \- *lemma* deriv_csinh
- \- *lemma* has_strict_fderiv_at.ccos
- \- *lemma* has_fderiv_at.ccos
- \- *lemma* has_fderiv_within_at.ccos
- \- *lemma* differentiable_within_at.ccos
- \- *lemma* differentiable_at.ccos
- \- *lemma* differentiable_on.ccos
- \- *lemma* differentiable.ccos
- \- *lemma* fderiv_within_ccos
- \- *lemma* fderiv_ccos
- \- *lemma* times_cont_diff.ccos
- \- *lemma* times_cont_diff_at.ccos
- \- *lemma* times_cont_diff_on.ccos
- \- *lemma* times_cont_diff_within_at.ccos
- \- *lemma* has_strict_fderiv_at.csin
- \- *lemma* has_fderiv_at.csin
- \- *lemma* has_fderiv_within_at.csin
- \- *lemma* differentiable_within_at.csin
- \- *lemma* differentiable_at.csin
- \- *lemma* differentiable_on.csin
- \- *lemma* differentiable.csin
- \- *lemma* fderiv_within_csin
- \- *lemma* fderiv_csin
- \- *lemma* times_cont_diff.csin
- \- *lemma* times_cont_diff_at.csin
- \- *lemma* times_cont_diff_on.csin
- \- *lemma* times_cont_diff_within_at.csin
- \- *lemma* has_strict_fderiv_at.ccosh
- \- *lemma* has_fderiv_at.ccosh
- \- *lemma* has_fderiv_within_at.ccosh
- \- *lemma* differentiable_within_at.ccosh
- \- *lemma* differentiable_at.ccosh
- \- *lemma* differentiable_on.ccosh
- \- *lemma* differentiable.ccosh
- \- *lemma* fderiv_within_ccosh
- \- *lemma* fderiv_ccosh
- \- *lemma* times_cont_diff.ccosh
- \- *lemma* times_cont_diff_at.ccosh
- \- *lemma* times_cont_diff_on.ccosh
- \- *lemma* times_cont_diff_within_at.ccosh
- \- *lemma* has_strict_fderiv_at.csinh
- \- *lemma* has_fderiv_at.csinh
- \- *lemma* has_fderiv_within_at.csinh
- \- *lemma* differentiable_within_at.csinh
- \- *lemma* differentiable_at.csinh
- \- *lemma* differentiable_on.csinh
- \- *lemma* differentiable.csinh
- \- *lemma* fderiv_within_csinh
- \- *lemma* fderiv_csinh
- \- *lemma* times_cont_diff.csinh
- \- *lemma* times_cont_diff_at.csinh
- \- *lemma* times_cont_diff_on.csinh
- \- *lemma* times_cont_diff_within_at.csinh
- \- *lemma* has_strict_deriv_at_sin
- \- *lemma* has_deriv_at_sin
- \- *lemma* times_cont_diff_sin
- \- *lemma* differentiable_sin
- \- *lemma* differentiable_at_sin
- \- *lemma* deriv_sin
- \- *lemma* has_strict_deriv_at_cos
- \- *lemma* has_deriv_at_cos
- \- *lemma* times_cont_diff_cos
- \- *lemma* differentiable_cos
- \- *lemma* differentiable_at_cos
- \- *lemma* deriv_cos
- \- *lemma* deriv_cos'
- \- *lemma* has_strict_deriv_at_sinh
- \- *lemma* has_deriv_at_sinh
- \- *lemma* times_cont_diff_sinh
- \- *lemma* differentiable_sinh
- \- *lemma* differentiable_at_sinh
- \- *lemma* deriv_sinh
- \- *lemma* has_strict_deriv_at_cosh
- \- *lemma* has_deriv_at_cosh
- \- *lemma* times_cont_diff_cosh
- \- *lemma* differentiable_cosh
- \- *lemma* differentiable_at_cosh
- \- *lemma* deriv_cosh
- \- *lemma* sinh_strict_mono
- \- *lemma* has_strict_deriv_at.cos
- \- *lemma* has_deriv_at.cos
- \- *lemma* has_deriv_within_at.cos
- \- *lemma* deriv_within_cos
- \- *lemma* deriv_cos
- \- *lemma* has_strict_deriv_at.sin
- \- *lemma* has_deriv_at.sin
- \- *lemma* has_deriv_within_at.sin
- \- *lemma* deriv_within_sin
- \- *lemma* deriv_sin
- \- *lemma* has_strict_deriv_at.cosh
- \- *lemma* has_deriv_at.cosh
- \- *lemma* has_deriv_within_at.cosh
- \- *lemma* deriv_within_cosh
- \- *lemma* deriv_cosh
- \- *lemma* has_strict_deriv_at.sinh
- \- *lemma* has_deriv_at.sinh
- \- *lemma* has_deriv_within_at.sinh
- \- *lemma* deriv_within_sinh
- \- *lemma* deriv_sinh
- \- *lemma* has_strict_fderiv_at.cos
- \- *lemma* has_fderiv_at.cos
- \- *lemma* has_fderiv_within_at.cos
- \- *lemma* differentiable_within_at.cos
- \- *lemma* differentiable_at.cos
- \- *lemma* differentiable_on.cos
- \- *lemma* differentiable.cos
- \- *lemma* fderiv_within_cos
- \- *lemma* fderiv_cos
- \- *lemma* times_cont_diff.cos
- \- *lemma* times_cont_diff_at.cos
- \- *lemma* times_cont_diff_on.cos
- \- *lemma* times_cont_diff_within_at.cos
- \- *lemma* has_strict_fderiv_at.sin
- \- *lemma* has_fderiv_at.sin
- \- *lemma* has_fderiv_within_at.sin
- \- *lemma* differentiable_within_at.sin
- \- *lemma* differentiable_at.sin
- \- *lemma* differentiable_on.sin
- \- *lemma* differentiable.sin
- \- *lemma* fderiv_within_sin
- \- *lemma* fderiv_sin
- \- *lemma* times_cont_diff.sin
- \- *lemma* times_cont_diff_at.sin
- \- *lemma* times_cont_diff_on.sin
- \- *lemma* times_cont_diff_within_at.sin
- \- *lemma* has_strict_fderiv_at.cosh
- \- *lemma* has_fderiv_at.cosh
- \- *lemma* has_fderiv_within_at.cosh
- \- *lemma* differentiable_within_at.cosh
- \- *lemma* differentiable_at.cosh
- \- *lemma* differentiable_on.cosh
- \- *lemma* differentiable.cosh
- \- *lemma* fderiv_within_cosh
- \- *lemma* fderiv_cosh
- \- *lemma* times_cont_diff.cosh
- \- *lemma* times_cont_diff_at.cosh
- \- *lemma* times_cont_diff_on.cosh
- \- *lemma* times_cont_diff_within_at.cosh
- \- *lemma* has_strict_fderiv_at.sinh
- \- *lemma* has_fderiv_at.sinh
- \- *lemma* has_fderiv_within_at.sinh
- \- *lemma* differentiable_within_at.sinh
- \- *lemma* differentiable_at.sinh
- \- *lemma* differentiable_on.sinh
- \- *lemma* differentiable.sinh
- \- *lemma* fderiv_within_sinh
- \- *lemma* fderiv_sinh
- \- *lemma* times_cont_diff.sinh
- \- *lemma* times_cont_diff_at.sinh
- \- *lemma* times_cont_diff_on.sinh
- \- *lemma* times_cont_diff_within_at.sinh

created src/analysis/special_functions/trigonometric/deriv.lean
- \+ *lemma* has_strict_deriv_at_sin
- \+ *lemma* has_deriv_at_sin
- \+ *lemma* times_cont_diff_sin
- \+ *lemma* differentiable_sin
- \+ *lemma* differentiable_at_sin
- \+ *lemma* deriv_sin
- \+ *lemma* has_strict_deriv_at_cos
- \+ *lemma* has_deriv_at_cos
- \+ *lemma* times_cont_diff_cos
- \+ *lemma* differentiable_cos
- \+ *lemma* differentiable_at_cos
- \+ *lemma* deriv_cos
- \+ *lemma* deriv_cos'
- \+ *lemma* has_strict_deriv_at_sinh
- \+ *lemma* has_deriv_at_sinh
- \+ *lemma* times_cont_diff_sinh
- \+ *lemma* differentiable_sinh
- \+ *lemma* differentiable_at_sinh
- \+ *lemma* deriv_sinh
- \+ *lemma* has_strict_deriv_at_cosh
- \+ *lemma* has_deriv_at_cosh
- \+ *lemma* times_cont_diff_cosh
- \+ *lemma* differentiable_cosh
- \+ *lemma* differentiable_at_cosh
- \+ *lemma* deriv_cosh
- \+ *lemma* has_strict_deriv_at.ccos
- \+ *lemma* has_deriv_at.ccos
- \+ *lemma* has_deriv_within_at.ccos
- \+ *lemma* deriv_within_ccos
- \+ *lemma* deriv_ccos
- \+ *lemma* has_strict_deriv_at.csin
- \+ *lemma* has_deriv_at.csin
- \+ *lemma* has_deriv_within_at.csin
- \+ *lemma* deriv_within_csin
- \+ *lemma* deriv_csin
- \+ *lemma* has_strict_deriv_at.ccosh
- \+ *lemma* has_deriv_at.ccosh
- \+ *lemma* has_deriv_within_at.ccosh
- \+ *lemma* deriv_within_ccosh
- \+ *lemma* deriv_ccosh
- \+ *lemma* has_strict_deriv_at.csinh
- \+ *lemma* has_deriv_at.csinh
- \+ *lemma* has_deriv_within_at.csinh
- \+ *lemma* deriv_within_csinh
- \+ *lemma* deriv_csinh
- \+ *lemma* has_strict_fderiv_at.ccos
- \+ *lemma* has_fderiv_at.ccos
- \+ *lemma* has_fderiv_within_at.ccos
- \+ *lemma* differentiable_within_at.ccos
- \+ *lemma* differentiable_at.ccos
- \+ *lemma* differentiable_on.ccos
- \+ *lemma* differentiable.ccos
- \+ *lemma* fderiv_within_ccos
- \+ *lemma* fderiv_ccos
- \+ *lemma* times_cont_diff.ccos
- \+ *lemma* times_cont_diff_at.ccos
- \+ *lemma* times_cont_diff_on.ccos
- \+ *lemma* times_cont_diff_within_at.ccos
- \+ *lemma* has_strict_fderiv_at.csin
- \+ *lemma* has_fderiv_at.csin
- \+ *lemma* has_fderiv_within_at.csin
- \+ *lemma* differentiable_within_at.csin
- \+ *lemma* differentiable_at.csin
- \+ *lemma* differentiable_on.csin
- \+ *lemma* differentiable.csin
- \+ *lemma* fderiv_within_csin
- \+ *lemma* fderiv_csin
- \+ *lemma* times_cont_diff.csin
- \+ *lemma* times_cont_diff_at.csin
- \+ *lemma* times_cont_diff_on.csin
- \+ *lemma* times_cont_diff_within_at.csin
- \+ *lemma* has_strict_fderiv_at.ccosh
- \+ *lemma* has_fderiv_at.ccosh
- \+ *lemma* has_fderiv_within_at.ccosh
- \+ *lemma* differentiable_within_at.ccosh
- \+ *lemma* differentiable_at.ccosh
- \+ *lemma* differentiable_on.ccosh
- \+ *lemma* differentiable.ccosh
- \+ *lemma* fderiv_within_ccosh
- \+ *lemma* fderiv_ccosh
- \+ *lemma* times_cont_diff.ccosh
- \+ *lemma* times_cont_diff_at.ccosh
- \+ *lemma* times_cont_diff_on.ccosh
- \+ *lemma* times_cont_diff_within_at.ccosh
- \+ *lemma* has_strict_fderiv_at.csinh
- \+ *lemma* has_fderiv_at.csinh
- \+ *lemma* has_fderiv_within_at.csinh
- \+ *lemma* differentiable_within_at.csinh
- \+ *lemma* differentiable_at.csinh
- \+ *lemma* differentiable_on.csinh
- \+ *lemma* differentiable.csinh
- \+ *lemma* fderiv_within_csinh
- \+ *lemma* fderiv_csinh
- \+ *lemma* times_cont_diff.csinh
- \+ *lemma* times_cont_diff_at.csinh
- \+ *lemma* times_cont_diff_on.csinh
- \+ *lemma* times_cont_diff_within_at.csinh
- \+ *lemma* has_strict_deriv_at_sin
- \+ *lemma* has_deriv_at_sin
- \+ *lemma* times_cont_diff_sin
- \+ *lemma* differentiable_sin
- \+ *lemma* differentiable_at_sin
- \+ *lemma* deriv_sin
- \+ *lemma* has_strict_deriv_at_cos
- \+ *lemma* has_deriv_at_cos
- \+ *lemma* times_cont_diff_cos
- \+ *lemma* differentiable_cos
- \+ *lemma* differentiable_at_cos
- \+ *lemma* deriv_cos
- \+ *lemma* deriv_cos'
- \+ *lemma* has_strict_deriv_at_sinh
- \+ *lemma* has_deriv_at_sinh
- \+ *lemma* times_cont_diff_sinh
- \+ *lemma* differentiable_sinh
- \+ *lemma* differentiable_at_sinh
- \+ *lemma* deriv_sinh
- \+ *lemma* has_strict_deriv_at_cosh
- \+ *lemma* has_deriv_at_cosh
- \+ *lemma* times_cont_diff_cosh
- \+ *lemma* differentiable_cosh
- \+ *lemma* differentiable_at_cosh
- \+ *lemma* deriv_cosh
- \+ *lemma* sinh_strict_mono
- \+ *lemma* has_strict_deriv_at.cos
- \+ *lemma* has_deriv_at.cos
- \+ *lemma* has_deriv_within_at.cos
- \+ *lemma* deriv_within_cos
- \+ *lemma* deriv_cos
- \+ *lemma* has_strict_deriv_at.sin
- \+ *lemma* has_deriv_at.sin
- \+ *lemma* has_deriv_within_at.sin
- \+ *lemma* deriv_within_sin
- \+ *lemma* deriv_sin
- \+ *lemma* has_strict_deriv_at.cosh
- \+ *lemma* has_deriv_at.cosh
- \+ *lemma* has_deriv_within_at.cosh
- \+ *lemma* deriv_within_cosh
- \+ *lemma* deriv_cosh
- \+ *lemma* has_strict_deriv_at.sinh
- \+ *lemma* has_deriv_at.sinh
- \+ *lemma* has_deriv_within_at.sinh
- \+ *lemma* deriv_within_sinh
- \+ *lemma* deriv_sinh
- \+ *lemma* has_strict_fderiv_at.cos
- \+ *lemma* has_fderiv_at.cos
- \+ *lemma* has_fderiv_within_at.cos
- \+ *lemma* differentiable_within_at.cos
- \+ *lemma* differentiable_at.cos
- \+ *lemma* differentiable_on.cos
- \+ *lemma* differentiable.cos
- \+ *lemma* fderiv_within_cos
- \+ *lemma* fderiv_cos
- \+ *lemma* times_cont_diff.cos
- \+ *lemma* times_cont_diff_at.cos
- \+ *lemma* times_cont_diff_on.cos
- \+ *lemma* times_cont_diff_within_at.cos
- \+ *lemma* has_strict_fderiv_at.sin
- \+ *lemma* has_fderiv_at.sin
- \+ *lemma* has_fderiv_within_at.sin
- \+ *lemma* differentiable_within_at.sin
- \+ *lemma* differentiable_at.sin
- \+ *lemma* differentiable_on.sin
- \+ *lemma* differentiable.sin
- \+ *lemma* fderiv_within_sin
- \+ *lemma* fderiv_sin
- \+ *lemma* times_cont_diff.sin
- \+ *lemma* times_cont_diff_at.sin
- \+ *lemma* times_cont_diff_on.sin
- \+ *lemma* times_cont_diff_within_at.sin
- \+ *lemma* has_strict_fderiv_at.cosh
- \+ *lemma* has_fderiv_at.cosh
- \+ *lemma* has_fderiv_within_at.cosh
- \+ *lemma* differentiable_within_at.cosh
- \+ *lemma* differentiable_at.cosh
- \+ *lemma* differentiable_on.cosh
- \+ *lemma* differentiable.cosh
- \+ *lemma* fderiv_within_cosh
- \+ *lemma* fderiv_cosh
- \+ *lemma* times_cont_diff.cosh
- \+ *lemma* times_cont_diff_at.cosh
- \+ *lemma* times_cont_diff_on.cosh
- \+ *lemma* times_cont_diff_within_at.cosh
- \+ *lemma* has_strict_fderiv_at.sinh
- \+ *lemma* has_fderiv_at.sinh
- \+ *lemma* has_fderiv_within_at.sinh
- \+ *lemma* differentiable_within_at.sinh
- \+ *lemma* differentiable_at.sinh
- \+ *lemma* differentiable_on.sinh
- \+ *lemma* differentiable.sinh
- \+ *lemma* fderiv_within_sinh
- \+ *lemma* fderiv_sinh
- \+ *lemma* times_cont_diff.sinh
- \+ *lemma* times_cont_diff_at.sinh
- \+ *lemma* times_cont_diff_on.sinh
- \+ *lemma* times_cont_diff_within_at.sinh

modified src/analysis/special_functions/trigonometric/inverse.lean

modified test/differentiable.lean

modified test/simp_command.lean



## [2021-11-02 21:57:33](https://github.com/leanprover-community/mathlib/commit/d43daf0)
feat(algebra/big_operators/order): add unbundled is_absolute_value.sum_le and map_prod ([#10104](https://github.com/leanprover-community/mathlib/pull/10104))
Add unbundled versions of two existing lemmas.
Additionally generalize a few typeclass assumptions in an earlier file.
From the flt-regular project
#### Estimated changes
modified src/algebra/big_operators/order.lean
- \+ *lemma* is_absolute_value.abv_sum
- \+ *lemma* is_absolute_value.map_prod

modified src/algebra/order/absolute_value.lean



## [2021-11-02 21:57:32](https://github.com/leanprover-community/mathlib/commit/3accc5e)
feat(data/bool): bnot_iff_not ([#10095](https://github.com/leanprover-community/mathlib/pull/10095))
#### Estimated changes
modified src/data/bool.lean
- \+ *theorem* bnot_iff_not



## [2021-11-02 19:48:57](https://github.com/leanprover-community/mathlib/commit/00064bd)
feat(logic/relation): add equivalence.comap ([#10103](https://github.com/leanprover-community/mathlib/pull/10103))
#### Estimated changes
modified src/data/setoid/basic.lean

modified src/group_theory/congruence.lean

modified src/logic/relation.lean
- \+ *lemma* equivalence.comap



## [2021-11-02 19:05:42](https://github.com/leanprover-community/mathlib/commit/2d8be73)
chore(measure_theory/probability_mass_function): avoid non-terminal simp in coe_le_one ([#10112](https://github.com/leanprover-community/mathlib/pull/10112))
#### Estimated changes
modified src/measure_theory/probability_mass_function.lean



## [2021-11-02 16:26:32](https://github.com/leanprover-community/mathlib/commit/6df3143)
chore(combinatorics/choose/bounds): move to nat namespace ([#10106](https://github.com/leanprover-community/mathlib/pull/10106))
There are module docstrings elsewhere that expect this to be in the `nat` namespace with the other `choose` lemmas.
#### Estimated changes
modified src/combinatorics/choose/bounds.lean



## [2021-11-02 15:51:48](https://github.com/leanprover-community/mathlib/commit/0dcb184)
style(testing/slim_check): fix line length ([#10114](https://github.com/leanprover-community/mathlib/pull/10114))
#### Estimated changes
modified src/testing/slim_check/testable.lean



## [2021-11-02 14:14:07](https://github.com/leanprover-community/mathlib/commit/796a051)
feat(measure_theory/decomposition/lebesgue): more on Radon-Nikodym derivatives ([#10070](https://github.com/leanprover-community/mathlib/pull/10070))
We show that the density in the Lebesgue decomposition theorem (aka the Radon-Nikodym derivative) is unique. Previously, uniqueness of the absolutely continuous part was known, but not of its density. We also show that the Radon-Nikodym derivative is almost everywhere finite. Plus some cleanup of the whole file.
#### Estimated changes
modified src/measure_theory/decomposition/jordan.lean

modified src/measure_theory/decomposition/lebesgue.lean
- \+/\- *lemma* singular_part_le
- \+ *lemma* lintegral_rn_deriv_lt_top_of_measure_ne_top
- \+/\- *lemma* lintegral_rn_deriv_lt_top
- \+ *lemma* singular_part_with_density
- \+/\- *lemma* singular_part_le
- \+/\- *lemma* lintegral_rn_deriv_lt_top
- \+ *theorem* rn_deriv_lt_top
- \+ *theorem* eq_with_density_rn_deriv
- \+/\- *theorem* eq_rn_deriv
- \+ *theorem* rn_deriv_with_density
- \+/\- *theorem* eq_rn_deriv

modified src/measure_theory/function/ae_eq_of_integral.lean
- \+ *lemma* ae_le_of_forall_set_lintegral_le_of_sigma_finite
- \+ *lemma* ae_eq_of_forall_set_lintegral_eq_of_sigma_finite
- \+/\- *lemma* ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite
- \+/\- *lemma* ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* zero_right
- \+ *lemma* zero_left
- \+ *lemma* mem_spanning_sets_of_index_le
- \+ *lemma* eventually_mem_spanning_sets
- \+ *lemma* ae_of_forall_measure_lt_top_ae_restrict
- \+ *lemma* is_locally_finite_measure_of_le
- \- *lemma* zero

modified src/probability_theory/density.lean



## [2021-11-02 12:07:49](https://github.com/leanprover-community/mathlib/commit/da6706d)
feat(data/mv_polynomial/basic): lemmas about map ([#10092](https://github.com/leanprover-community/mathlib/pull/10092))
This adds `map_alg_hom`, which fills the gap between `map` and `map_alg_equiv`.
The only new proof here is `map_surjective`; everything else is just a reworked existing proof.
#### Estimated changes
modified src/data/mv_polynomial/basic.lean
- \+ *lemma* map_surjective
- \+ *lemma* map_left_inverse
- \+ *lemma* map_right_inverse
- \+ *lemma* map_alg_hom_id
- \+ *def* map_alg_hom

modified src/data/mv_polynomial/equiv.lean
- \- *lemma* map_alg_equiv_apply



## [2021-11-02 10:26:34](https://github.com/leanprover-community/mathlib/commit/80dc445)
refactor(order/bounded_lattice): generalize le on with_{top,bot} ([#10085](https://github.com/leanprover-community/mathlib/pull/10085))
Before, some lemmas assumed `preorder` even when they were true for
just the underlying `le`. In the case of `with_bot`, the missing
underlying `has_le` instance is defined.
For both `with_{top,bot}`, a few lemmas are generalized accordingly.
#### Estimated changes
modified src/data/nat/cast.lean

modified src/order/bounded_lattice.lean
- \+/\- *lemma* coe_lt_coe
- \+/\- *lemma* coe_lt_coe
- \+/\- *lemma* coe_lt_top
- \+/\- *lemma* coe_lt_coe
- \+/\- *lemma* coe_lt_coe
- \+/\- *lemma* coe_lt_top
- \+/\- *theorem* coe_le_coe
- \+/\- *theorem* some_le_some
- \+/\- *theorem* coe_le
- \+/\- *theorem* coe_le_coe
- \+/\- *theorem* le_coe
- \+/\- *theorem* coe_le_coe
- \+/\- *theorem* some_le_some
- \+/\- *theorem* coe_le
- \+/\- *theorem* coe_le_coe
- \+/\- *theorem* le_coe



## [2021-11-02 10:26:33](https://github.com/leanprover-community/mathlib/commit/658a3d7)
refactor(algebra/algebra): remove subalgebra.under ([#10081](https://github.com/leanprover-community/mathlib/pull/10081))
This removes `subalgebra.under`, and replaces `subalgebra.of_under` with `subalgebra.of_restrict_scalars`.
Lemmas associated with `under` have been renamed accordingly.
#### Estimated changes
modified src/algebra/algebra/tower.lean
- \- *lemma* mem_under
- \+ *theorem* adjoin_range_to_alg_hom
- \- *theorem* range_under_adjoin
- \+ *def* of_restrict_scalars
- \- *def* under
- \- *def* of_under

modified src/field_theory/is_alg_closed/basic.lean

modified src/field_theory/splitting_field.lean

modified src/ring_theory/adjoin/basic.lean
- \+ *theorem* adjoin_union_eq_adjoin_adjoin
- \- *theorem* adjoin_union_eq_under

modified src/ring_theory/adjoin/fg.lean

modified src/ring_theory/algebra_tower.lean



## [2021-11-02 10:26:32](https://github.com/leanprover-community/mathlib/commit/541df8a)
feat(topology/algebra/ordered/liminf_limsup): convergence of a sequence which does not oscillate infinitely ([#10073](https://github.com/leanprover-community/mathlib/pull/10073))
If, for all `a < b`, a sequence is not frequently below `a` and frequently above `b`, then it has to converge. This is a useful convergence criterion (called no upcrossings), used for instance in martingales.
Also generalize several statements on liminfs and limsups from complete linear orders to conditionally complete linear orders.
#### Estimated changes
modified src/order/liminf_limsup.lean
- \+ *lemma* is_bounded.is_cobounded_ge
- \+ *lemma* is_bounded.is_cobounded_le
- \+/\- *lemma* liminf_le_limsup
- \+/\- *lemma* liminf_le_limsup

modified src/topology/algebra/ordered/liminf_limsup.lean
- \+ *lemma* tendsto_of_no_upcrossings



## [2021-11-02 10:26:31](https://github.com/leanprover-community/mathlib/commit/880182d)
chore(analysis/normed/group): add `cauchy_seq_finset_of_norm_bounded_eventually` ([#10060](https://github.com/leanprover-community/mathlib/pull/10060))
Add `cauchy_seq_finset_of_norm_bounded_eventually`, use it to golf some proofs.
#### Estimated changes
modified src/analysis/normed/group/infinite_sum.lean
- \+ *lemma* cauchy_seq_finset_of_norm_bounded_eventually



## [2021-11-02 10:26:30](https://github.com/leanprover-community/mathlib/commit/fc12ca8)
feat(measure_theory/probability_mass_function): Define uniform pmf on an inhabited fintype ([#9920](https://github.com/leanprover-community/mathlib/pull/9920))
This PR defines uniform probability mass functions on nonempty finsets and inhabited fintypes.
#### Estimated changes
modified src/measure_theory/probability_mass_function.lean
- \+/\- *lemma* coe_le_one
- \+ *lemma* of_finset_apply
- \+ *lemma* of_finset_apply_of_not_mem
- \+ *lemma* of_fintype_apply
- \+ *lemma* of_multiset_apply
- \+ *lemma* of_multiset_apply_of_not_mem
- \+ *lemma* uniform_of_finset_apply
- \+ *lemma* uniform_of_finset_apply_of_mem
- \+ *lemma* uniform_of_finset_apply_of_not_mem
- \+ *lemma* uniform_of_fintype_apply
- \+ *lemma* bernuolli_apply
- \+/\- *lemma* coe_le_one
- \+ *def* of_finset
- \+/\- *def* of_fintype
- \+ *def* uniform_of_finset
- \+ *def* uniform_of_fintype
- \+/\- *def* of_fintype



## [2021-11-02 09:31:35](https://github.com/leanprover-community/mathlib/commit/f6894c4)
chore(ring_theory/adjoin/fg): generalize ring to semiring in a few places ([#10089](https://github.com/leanprover-community/mathlib/pull/10089))
#### Estimated changes
modified src/ring_theory/adjoin/fg.lean



## [2021-11-02 08:23:22](https://github.com/leanprover-community/mathlib/commit/26bdcac)
chore(coinductive_predicates): remove private and use of import_private ([#10084](https://github.com/leanprover-community/mathlib/pull/10084))
Remove a `private` modifier (I think this had previously been ported from core by @bryangingechen).
Then remove the only use of `import_private` from the library. (Besides another use in `tests/`, which we're not porting.)
(In mathlib4 we have `OpenPrivate` as an alternative. Removing `import_private` is one less thing for mathport to care about.)
#### Estimated changes
modified src/algebra/lie/weights.lean

modified src/meta/coinductive_predicates.lean

modified test/coinductive.lean



## [2021-11-02 08:23:21](https://github.com/leanprover-community/mathlib/commit/1852840)
feat(analysis/calculus/mean_value): Strict convexity from derivatives ([#10034](https://github.com/leanprover-community/mathlib/pull/10034))
This duplicates all the results relating convex/concave function and their derivatives to strictly convex/strictly concave functions.
#### Estimated changes
modified src/analysis/calculus/mean_value.lean
- \+ *lemma* strict_mono_on.strict_convex_on_of_deriv
- \+ *lemma* strict_anti_on.strict_concave_on_of_deriv
- \+ *lemma* strict_mono.strict_convex_on_univ_of_deriv
- \+ *lemma* strict_anti.strict_concave_on_univ_of_deriv
- \+ *lemma* strict_convex_on_of_deriv2_pos
- \+ *lemma* strict_concave_on_of_deriv2_neg
- \+ *lemma* strict_convex_on_open_of_deriv2_pos
- \+ *lemma* strict_concave_on_open_of_deriv2_neg
- \+ *lemma* strict_convex_on_univ_of_deriv2_pos
- \+ *lemma* strict_concave_on_univ_of_deriv2_neg
- \+ *theorem* monotone_on.convex_on_of_deriv
- \+ *theorem* antitone_on.concave_on_of_deriv
- \+ *theorem* monotone.convex_on_univ_of_deriv
- \+ *theorem* antitone.concave_on_univ_of_deriv
- \- *theorem* convex_on_of_deriv_monotone_on
- \- *theorem* concave_on_of_deriv_antitone_on
- \- *theorem* convex_on_univ_of_deriv_monotone
- \- *theorem* antitone.concave_on_univ



## [2021-11-02 06:43:08](https://github.com/leanprover-community/mathlib/commit/6d2af9a)
chore(data/list/defs): remove unneeded open ([#10100](https://github.com/leanprover-community/mathlib/pull/10100))
#### Estimated changes
modified src/data/list/defs.lean



## [2021-11-02 02:55:19](https://github.com/leanprover-community/mathlib/commit/d926ac7)
chore(scripts): update nolints.txt ([#10098](https://github.com/leanprover-community/mathlib/pull/10098))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt

modified scripts/style-exceptions.txt



## [2021-11-01 21:07:30](https://github.com/leanprover-community/mathlib/commit/fd783e3)
chore(algebra/free_algebra): remove a heavy and unecessary import ([#10093](https://github.com/leanprover-community/mathlib/pull/10093))
`transfer_instance` pulls in category theory, which is overkill
#### Estimated changes
modified src/algebra/free_algebra.lean



## [2021-11-01 20:14:44](https://github.com/leanprover-community/mathlib/commit/b1d5446)
chore(analysis/normed_space/operator_norm): remove an import to data.equiv.transfer_instance ([#10094](https://github.com/leanprover-community/mathlib/pull/10094))
This import isn't needed, and the spelling without it is shorter.
#### Estimated changes
modified src/analysis/normed_space/operator_norm.lean



## [2021-11-01 12:55:31](https://github.com/leanprover-community/mathlib/commit/0144b6c)
chore({data/finset,data/multiset,order}/locally_finite): Better line wraps ([#10087](https://github.com/leanprover-community/mathlib/pull/10087))
#### Estimated changes
modified src/data/finset/locally_finite.lean
- \+/\- *lemma* Icc_eq_empty_of_lt
- \+/\- *lemma* Ico_eq_empty_of_le
- \+/\- *lemma* Ioc_eq_empty_of_le
- \+/\- *lemma* Ioo_eq_empty_of_le
- \+/\- *lemma* Ico_self
- \+/\- *lemma* Ioc_self
- \+/\- *lemma* Ioo_self
- \+/\- *lemma* Icc_self
- \+/\- *lemma* Icc_eq_empty_of_lt
- \+/\- *lemma* Ico_eq_empty_of_le
- \+/\- *lemma* Ioc_eq_empty_of_le
- \+/\- *lemma* Ioo_eq_empty_of_le
- \+/\- *lemma* Ico_self
- \+/\- *lemma* Ioc_self
- \+/\- *lemma* Ioo_self
- \+/\- *lemma* Icc_self

modified src/data/multiset/locally_finite.lean
- \+/\- *lemma* Icc_eq_zero_of_lt
- \+/\- *lemma* Ioc_eq_zero_of_le
- \+/\- *lemma* Ioo_eq_zero_of_le
- \+/\- *lemma* Ioc_self
- \+/\- *lemma* Ioo_self
- \+/\- *lemma* Icc_self
- \+/\- *lemma* Icc_eq_zero_of_lt
- \+/\- *lemma* Ioc_eq_zero_of_le
- \+/\- *lemma* Ioo_eq_zero_of_le
- \+/\- *lemma* Ioc_self
- \+/\- *lemma* Ioo_self
- \+/\- *lemma* Icc_self

modified src/order/locally_finite.lean
- \+/\- *lemma* mem_Ici
- \+/\- *lemma* mem_Ioi
- \+/\- *lemma* mem_Iic
- \+/\- *lemma* mem_Iio
- \+/\- *lemma* mem_Ici
- \+/\- *lemma* mem_Ioi
- \+/\- *lemma* mem_Iic
- \+/\- *lemma* mem_Iio
- \+/\- *lemma* finite_Ici
- \+/\- *lemma* finite_Ioi
- \+/\- *lemma* finite_Iic
- \+/\- *lemma* finite_Iio
- \+/\- *lemma* mem_Ici
- \+/\- *lemma* mem_Ioi
- \+/\- *lemma* mem_Iic
- \+/\- *lemma* mem_Iio
- \+/\- *lemma* mem_Ici
- \+/\- *lemma* mem_Ioi
- \+/\- *lemma* mem_Iic
- \+/\- *lemma* mem_Iio
- \+/\- *lemma* finite_Ici
- \+/\- *lemma* finite_Ioi
- \+/\- *lemma* finite_Iic
- \+/\- *lemma* finite_Iio
- \+/\- *theorem* Ico_subset_Ico
- \+/\- *theorem* Ico_subset_Ico
- \+/\- *def* Icc
- \+/\- *def* Ico
- \+/\- *def* Ioc
- \+/\- *def* Ioo
- \+/\- *def* Iic
- \+/\- *def* Iio
- \+/\- *def* Icc
- \+/\- *def* Ioc
- \+/\- *def* Ioo
- \+/\- *def* Ici
- \+/\- *def* Ioi
- \+/\- *def* Iic
- \+/\- *def* Iio
- \+/\- *def* Icc
- \+/\- *def* Ico
- \+/\- *def* Ioc
- \+/\- *def* Ioo
- \+/\- *def* Iic
- \+/\- *def* Iio
- \+/\- *def* Icc
- \+/\- *def* Ioc
- \+/\- *def* Ioo
- \+/\- *def* Ici
- \+/\- *def* Ioi
- \+/\- *def* Iic
- \+/\- *def* Iio



## [2021-11-01 12:22:20](https://github.com/leanprover-community/mathlib/commit/fef1535)
chore(category_theory/limits): reuse a previous result ([#10088](https://github.com/leanprover-community/mathlib/pull/10088))
#### Estimated changes
modified src/category_theory/limits/shapes/kernel_pair.lean



## [2021-11-01 11:06:34](https://github.com/leanprover-community/mathlib/commit/9ef310f)
chore(algebra/algebra): implement subalgebra.under in terms of restrict_scalars ([#10080](https://github.com/leanprover-community/mathlib/pull/10080))
We should probably remove `subalgebra.under` entirely, but that's likely a lot more work.
#### Estimated changes
modified src/algebra/algebra/subalgebra.lean
- \- *lemma* mem_under
- \- *def* under

modified src/algebra/algebra/tower.lean
- \+ *lemma* mem_under
- \+ *def* under

modified src/ring_theory/adjoin/basic.lean
- \+/\- *theorem* adjoin_induction
- \+/\- *theorem* adjoin_induction



## [2021-11-01 11:06:33](https://github.com/leanprover-community/mathlib/commit/17ebcf0)
chore(ring_theory/algebra_tower): relax typeclasses ([#10078](https://github.com/leanprover-community/mathlib/pull/10078))
This generalizes some `comm_ring`s to `comm_semiring`s.
Split from [#10024](https://github.com/leanprover-community/mathlib/pull/10024)
#### Estimated changes
modified src/ring_theory/algebra_tower.lean
- \+/\- *lemma* algebra.fg_trans'
- \+/\- *lemma* basis.algebra_map_injective
- \+/\- *lemma* algebra.fg_trans'
- \+/\- *lemma* basis.algebra_map_injective



## [2021-11-01 10:12:40](https://github.com/leanprover-community/mathlib/commit/23892a0)
chore(analysis/normed_space/operator_norm): semilinearize part of the file ([#10076](https://github.com/leanprover-community/mathlib/pull/10076))
This PR generalizes part of the `operator_norm` file to semilinear maps. Only the first section (`semi_normed`) is done, which allows us to construct continuous semilinear maps using `linear_map.mk_continuous`.
The rest of the file is trickier, since we need specify how the ring hom interacts with the norm. I'd rather leave it to a future PR since I don't need the rest now.
#### Estimated changes
modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_of_linear_of_boundₛₗ
- \+/\- *lemma* continuous_of_linear_of_bound
- \+/\- *lemma* continuous_of_linear_of_bound
- \+/\- *def* linear_map.mk_continuous
- \+/\- *def* linear_map.mk_continuous_of_exists_bound
- \+/\- *def* linear_map.mk_continuous
- \+/\- *def* linear_map.mk_continuous_of_exists_bound

modified src/measure_theory/integral/set_integral.lean



## [2021-11-01 07:01:57](https://github.com/leanprover-community/mathlib/commit/85fe90e)
feat(algebra/direct_sum/module) : coe and internal ([#10004](https://github.com/leanprover-community/mathlib/pull/10004))
This extracts the following `def`s from within the various `is_internal` properties:
* `direct_sum.add_submonoid_coe`
* `direct_sum.add_subgroup_coe`
* `direct_sum.submodule_coe`
Packing these into a def makes things more concise, and avoids some annoying elaboration issues.
#### Estimated changes
modified src/algebra/direct_sum/basic.lean
- \+ *lemma* add_submonoid_coe_of
- \+ *lemma* add_subgroup_coe_of
- \+ *def* add_submonoid_coe
- \+ *def* add_subgroup_coe

modified src/algebra/direct_sum/module.lean
- \+ *lemma* submodule_coe_of
- \+ *def* submodule_coe



## [2021-11-01 05:31:03](https://github.com/leanprover-community/mathlib/commit/acc504e)
docs(category_theory/*): add missing module docs ([#9990](https://github.com/leanprover-community/mathlib/pull/9990))
#### Estimated changes
modified src/category_theory/adjunction/basic.lean

modified src/category_theory/adjunction/fully_faithful.lean

modified src/category_theory/adjunction/limits.lean

modified src/category_theory/full_subcategory.lean

modified src/category_theory/fully_faithful.lean

modified src/category_theory/limits/functor_category.lean

modified src/category_theory/limits/lattice.lean

modified src/category_theory/limits/opposites.lean

modified src/category_theory/limits/shapes/finite_products.lean

modified src/category_theory/products/bifunctor.lean



## [2021-11-01 02:38:33](https://github.com/leanprover-community/mathlib/commit/e8fa232)
chore(scripts): update nolints.txt ([#10083](https://github.com/leanprover-community/mathlib/pull/10083))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2021-11-01 00:38:30](https://github.com/leanprover-community/mathlib/commit/cd457a5)
fix(data/{rbtree,rbmap}): fix some lint errors ([#10036](https://github.com/leanprover-community/mathlib/pull/10036))
#### Estimated changes
modified src/data/rbmap/default.lean
- \+/\- *lemma* mem_of_mem_of_eqv
- \+/\- *lemma* eq_leaf_of_min_eq_none
- \+/\- *lemma* eq_leaf_of_max_eq_none
- \+/\- *lemma* mem_of_mem_of_eqv
- \+/\- *lemma* eq_leaf_of_min_eq_none
- \+/\- *lemma* eq_leaf_of_max_eq_none

modified src/data/rbtree/basic.lean
- \+/\- *lemma* depth_min
- \+/\- *lemma* balanced
- \+/\- *lemma* depth_min
- \+/\- *lemma* balanced

modified src/data/rbtree/find.lean
- \+/\- *lemma* eqv_of_find_some
- \+/\- *lemma* eqv_of_find_some

modified src/data/rbtree/insert.lean
- \+/\- *lemma* ins.induction
- \+/\- *lemma* is_searchable_ins
- \+/\- *lemma* is_searchable_insert
- \+/\- *lemma* ins_ne_leaf
- \+/\- *lemma* insert_ne_leaf
- \+/\- *lemma* mem_ins_of_incomp
- \+/\- *lemma* mem_ins_of_mem
- \+/\- *lemma* mem_insert_of_incomp
- \+/\- *lemma* mem_insert_of_mem
- \+/\- *lemma* of_mem_balance1_node
- \+/\- *lemma* of_mem_balance2_node
- \+/\- *lemma* equiv_or_mem_of_mem_ins
- \+/\- *lemma* equiv_or_mem_of_mem_insert
- \+/\- *lemma* find_balance1_node
- \+/\- *lemma* find_balance2_node
- \+/\- *lemma* ite_eq_of_not_lt
- \+/\- *lemma* find_ins_of_eqv
- \+/\- *lemma* find_mk_insert_result
- \+/\- *lemma* find_insert_of_eqv
- \+/\- *lemma* find_black_eq_find_red
- \+/\- *lemma* find_red_of_lt
- \+/\- *lemma* find_red_of_gt
- \+/\- *lemma* find_red_of_incomp
- \+/\- *lemma* find_insert_of_disj
- \+/\- *lemma* find_insert_of_not_eqv
- \+/\- *lemma* ins.induction
- \+/\- *lemma* is_searchable_ins
- \+/\- *lemma* is_searchable_insert
- \+/\- *lemma* ins_ne_leaf
- \+/\- *lemma* insert_ne_leaf
- \+/\- *lemma* mem_ins_of_incomp
- \+/\- *lemma* mem_ins_of_mem
- \+/\- *lemma* mem_insert_of_incomp
- \+/\- *lemma* mem_insert_of_mem
- \+/\- *lemma* of_mem_balance1_node
- \+/\- *lemma* of_mem_balance2_node
- \+/\- *lemma* equiv_or_mem_of_mem_ins
- \+/\- *lemma* equiv_or_mem_of_mem_insert
- \+/\- *lemma* find_balance1_node
- \+/\- *lemma* find_balance2_node
- \+/\- *lemma* ite_eq_of_not_lt
- \+/\- *lemma* find_ins_of_eqv
- \+/\- *lemma* find_mk_insert_result
- \+/\- *lemma* find_insert_of_eqv
- \+/\- *lemma* find_black_eq_find_red
- \+/\- *lemma* find_red_of_lt
- \+/\- *lemma* find_red_of_gt
- \+/\- *lemma* find_red_of_incomp
- \+/\- *lemma* find_insert_of_disj
- \+/\- *lemma* find_insert_of_not_eqv

modified src/data/rbtree/main.lean
- \+/\- *lemma* balanced
- \+/\- *lemma* eq_leaf_of_min_eq_none
- \+/\- *lemma* eq_leaf_of_max_eq_none
- \+/\- *lemma* balanced
- \+/\- *lemma* eq_leaf_of_min_eq_none
- \+/\- *lemma* eq_leaf_of_max_eq_none

modified src/data/rbtree/min_max.lean



## [2021-11-01 00:38:28](https://github.com/leanprover-community/mathlib/commit/bf82122)
feat(algebra/direct_sum/basic): some lemmas about `direct_sum.of` ([#10003](https://github.com/leanprover-community/mathlib/pull/10003))
Some small lemmas about `direct_sum.of` that are handy.
#### Estimated changes
modified src/algebra/direct_sum/basic.lean
- \+ *lemma* of_eq_same
- \+ *lemma* of_eq_of_ne
- \+ *lemma* support_zero
- \+ *lemma* support_of
- \+ *lemma* support_of_subset
- \+ *lemma* sum_support_of

