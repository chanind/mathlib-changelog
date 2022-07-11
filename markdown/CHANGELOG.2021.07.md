## [2021-07-31 21:11:47](https://github.com/leanprover-community/mathlib/commit/4c2edb0)
feat(data/equiv/mul_add): add `units.coe_inv` ([#8477](https://github.com/leanprover-community/mathlib/pull/8477))
* rename old `units.coe_inv` to `units.coe_inv''`;
* add new `@[simp, norm_cast, to_additive] lemma units.coe_inv` about
  coercion of units of a group;
* add missing `coe_to_units`.
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* coe_inv''
- \- *lemma* coe_inv

Modified src/data/equiv/mul_add.lean
- \+ *lemma* coe_to_units
- \+ *lemma* coe_inv
- \+/\- *def* to_units



## [2021-07-31 21:11:46](https://github.com/leanprover-community/mathlib/commit/6c6dd04)
feat(logic/relation): add `*.comap` for `reflexive`, `symmetric`, and `transitive` ([#8469](https://github.com/leanprover-community/mathlib/pull/8469))
#### Estimated changes
Modified src/logic/relation.lean
- \+ *lemma* reflexive.comap
- \+ *lemma* symmetric.comap
- \+ *lemma* transitive.comap



## [2021-07-31 20:17:15](https://github.com/leanprover-community/mathlib/commit/0827f3a)
feat(topology/metric_space/holder): add `holder_on_with` ([#8454](https://github.com/leanprover-community/mathlib/pull/8454))
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* tendsto_const_mul_rpow_nhds_zero_of_pos

Modified src/topology/metric_space/holder.lean
- \+ *lemma* holder_on_with_empty
- \+ *lemma* holder_on_with_singleton
- \+ *lemma* set.subsingleton.holder_on_with
- \+ *lemma* holder_on_with_univ
- \+ *lemma* holder_on_with_one
- \+ *lemma* edist_le
- \+ *lemma* edist_le_of_le
- \+ *lemma* comp
- \+ *lemma* comp_holder_with
- \+ *lemma* ediam_image_le_of_le
- \+ *lemma* ediam_image_le
- \+ *lemma* ediam_image_le_of_subset
- \+ *lemma* ediam_image_le_of_subset_of_le
- \+ *lemma* ediam_image_inter_le_of_le
- \+ *lemma* ediam_image_inter_le
- \+ *lemma* comp_holder_on_with
- \+ *def* holder_on_with

Modified src/topology/metric_space/lipschitz.lean


Modified src/topology/uniform_space/basic.lean
- \+ *theorem* uniform_continuous_on_univ



## [2021-07-31 18:55:07](https://github.com/leanprover-community/mathlib/commit/b3943dc)
feat(algebra/archimedean): `order_dual α` is archimedean ([#8476](https://github.com/leanprover-community/mathlib/pull/8476))
#### Estimated changes
Modified src/algebra/archimedean.lean




## [2021-07-31 16:29:04](https://github.com/leanprover-community/mathlib/commit/339a122)
chore(data/sym): move `data.sym` and `data.sym2` to `data.sym.basic` and `data.sym.sym2` ([#8471](https://github.com/leanprover-community/mathlib/pull/8471))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean


Modified src/combinatorics/simple_graph/matching.lean


Modified src/data/fintype/basic.lean


Renamed src/data/sym.lean to src/data/sym/basic.lean


Renamed src/data/sym2.lean to src/data/sym/sym2.lean




## [2021-07-31 13:15:04](https://github.com/leanprover-community/mathlib/commit/0a48016)
doc(analysis/calculus/conformal): fix a docstring ([#8479](https://github.com/leanprover-community/mathlib/pull/8479))
Fix a grammar mistake
#### Estimated changes
Modified src/analysis/calculus/conformal.lean




## [2021-07-30 16:11:00](https://github.com/leanprover-community/mathlib/commit/6e400b9)
feat(data/matrix/basic): update_{column,row}_subsingleton ([#8422](https://github.com/leanprover-community/mathlib/pull/8422))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* update_column_subsingleton
- \+ *lemma* update_row_subsingleton



## [2021-07-30 12:33:57](https://github.com/leanprover-community/mathlib/commit/977063f)
chore(group_theory/congruence): a few `simp` lemmas ([#8452](https://github.com/leanprover-community/mathlib/pull/8452))
* add `con.comap_rel`;
* add `@[simp]` to `con.ker_rel`;
* replace `con.comp_mk'_apply` with `con.coe_mk'`;
* [unrelated] add `commute.semiconj_by`.
#### Estimated changes
Modified src/algebra/group/commute.lean


Modified src/group_theory/congruence.lean
- \+ *lemma* comap_rel
- \+ *lemma* coe_mk'
- \- *lemma* comp_mk'_apply



## [2021-07-30 07:20:29](https://github.com/leanprover-community/mathlib/commit/98b0d18)
feat(analysis/normed_space/SemiNormedGroup/kernel): Fix universes + add explicit ([#8467](https://github.com/leanprover-community/mathlib/pull/8467))
See associated discussion from [zulip](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/for_mathlib/near/247575730)
#### Estimated changes
Modified src/analysis/normed_space/SemiNormedGroup/kernels.lean
- \+ *lemma* comp_explicit_cokernel_π
- \+ *lemma* explicit_cokernel_π_desc
- \+ *lemma* explicit_cokernel_desc_unique
- \+ *lemma* explicit_cokernel_hom_ext
- \+ *lemma* is_quotient_explicit_cokernel_π
- \+ *lemma* norm_noninc_explicit_cokernel_π
- \+ *lemma* explicit_cokernel_desc_norm_le_of_norm_le
- \+ *lemma* explicit_cokernel_desc_norm_le
- \+ *lemma* explicit_cokernel_iso_hom_π
- \+ *lemma* explicit_cokernel_iso_inv_π
- \+ *lemma* explicit_cokernel_iso_hom_desc
- \+/\- *def* cokernel_cocone
- \+/\- *def* cokernel_lift
- \+ *def* is_colimit_cokernel_cocone
- \+ *def* explicit_cokernel
- \+ *def* explicit_cokernel_desc
- \+ *def* explicit_cokernel_π
- \+ *def* explicit_cokernel_iso



## [2021-07-30 02:40:20](https://github.com/leanprover-community/mathlib/commit/8c89a52)
feat(algebra/ordered_monoid_lemmas): add one `strict_mono` lemma and a few doc-strings ([#8465](https://github.com/leanprover-community/mathlib/pull/8465))
The product of strictly monotone functions is strictly monotone (and some doc-strings).
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/monotonicity.20for.20sums.20and.20products.20of.20monotone.20functions)
#### Estimated changes
Modified src/algebra/ordered_monoid_lemmas.lean
- \+ *lemma* strict_mono.mul'



## [2021-07-29 15:02:31](https://github.com/leanprover-community/mathlib/commit/a4f1653)
feat(ring_theory): Dedekind domains have invertible fractional ideals  ([#8396](https://github.com/leanprover-community/mathlib/pull/8396))
This PR proves the other side of the equivalence `is_dedekind_domain → is_dedekind_domain_inv`, and uses this to provide a `comm_group_with_zero (fractional_ideal A⁰ K)` instance.
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean
- \+ *lemma* mem_inv_iff
- \+ *lemma* inv_anti_mono
- \+ *lemma* le_self_mul_inv
- \+ *lemma* coe_ideal_le_self_mul_inv
- \+ *lemma* fractional_ideal.one_inv
- \+ *lemma* exists_multiset_prod_cons_le_and_prod_not_le
- \+ *lemma* exists_not_mem_one_of_ne_bot
- \+ *lemma* one_mem_inv_coe_ideal
- \+ *lemma* mul_inv_cancel_of_le_one
- \+ *lemma* coe_ideal_mul_inv
- \+ *theorem* mul_inv_cancel
- \+ *theorem* is_dedekind_domain_iff_is_dedekind_domain_inv

Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* eq_zero_or_one
- \+ *lemma* eq_zero_or_one_of_is_field



## [2021-07-29 13:21:06](https://github.com/leanprover-community/mathlib/commit/69e3c79)
feat(logic/unique): unique_of_subsingleton ([#8415](https://github.com/leanprover-community/mathlib/pull/8415))
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/group_theory/perm/basic.lean


Modified src/logic/unique.lean
- \+ *def* unique_of_subsingleton



## [2021-07-29 11:52:13](https://github.com/leanprover-community/mathlib/commit/7a89150)
doc(data/nat/pairing): fix ascii table markdown ([#8460](https://github.com/leanprover-community/mathlib/pull/8460))
#### Estimated changes
Modified src/data/nat/pairing.lean




## [2021-07-29 06:51:42](https://github.com/leanprover-community/mathlib/commit/cd6f272)
feat(order/*): a bunch of lemmas about `order_iso` ([#8451](https://github.com/leanprover-community/mathlib/pull/8451))
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/order/bounds.lean
- \+ *lemma* is_lub_image
- \+ *lemma* is_glb_image
- \+ *lemma* is_lub_preimage
- \+ *lemma* is_glb_preimage

Modified src/order/rel_iso.lean
- \+ *lemma* symm_image_image
- \+ *lemma* image_symm_image
- \+ *lemma* image_eq_preimage
- \+ *lemma* preimage_symm_preimage
- \+ *lemma* symm_preimage_preimage
- \+ *lemma* image_preimage
- \+ *lemma* preimage_image
- \+ *lemma* le_symm_apply

Modified src/order/semiconj_Sup.lean
- \+ *lemma* right_mono
- \+ *lemma* order_iso_comp
- \+ *lemma* comp_order_iso
- \- *lemma* is_order_right_adjoint.unique
- \- *lemma* is_order_right_adjoint.right_mono



## [2021-07-28 22:58:41](https://github.com/leanprover-community/mathlib/commit/6d3e936)
feat(measure_theory): add @[to_additive] ([#8142](https://github.com/leanprover-community/mathlib/pull/8142))
This PR adds `@[to_additive]` to `haar_measure` and everything that depends on. This will allow us to define the Lebesgue measure on `ℝ` and `ℝ ^ n` as the Haar measure (or just show that it is equal to it).
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/measure_theory/arithmetic.lean
- \+/\- *lemma* list.measurable_prod'
- \+/\- *lemma* list.ae_measurable_prod'
- \+/\- *lemma* list.measurable_prod
- \+/\- *lemma* list.ae_measurable_prod
- \+/\- *lemma* multiset.measurable_prod'
- \+/\- *lemma* multiset.ae_measurable_prod'
- \+/\- *lemma* multiset.measurable_prod
- \+/\- *lemma* multiset.ae_measurable_prod
- \+/\- *lemma* finset.measurable_prod'
- \+/\- *lemma* finset.measurable_prod
- \+/\- *lemma* finset.ae_measurable_prod'
- \+/\- *lemma* finset.ae_measurable_prod

Modified src/measure_theory/conditional_expectation.lean


Modified src/measure_theory/content.lean


Modified src/measure_theory/group.lean


Modified src/measure_theory/haar_measure.lean
- \+/\- *lemma* mem_prehaar_empty
- \+ *theorem* regular_of_is_mul_left_invariant
- \- *theorem* regular_of_left_invariant

Modified src/measure_theory/lp_space.lean
- \+/\- *lemma* snorm'_const_smul

Modified src/measure_theory/prod_group.lean


Modified src/topology/algebra/group.lean




## [2021-07-28 21:04:18](https://github.com/leanprover-community/mathlib/commit/870b9d8)
ci(bors.toml): add merge-conflict to block_labels ([#8455](https://github.com/leanprover-community/mathlib/pull/8455))
#### Estimated changes
Modified bors.toml




## [2021-07-28 21:04:17](https://github.com/leanprover-community/mathlib/commit/92a5be8)
feat(ring,group,monoid): map_equiv lemmas for different structures ([#8453](https://github.com/leanprover-community/mathlib/pull/8453))
There is some inconsistency in the statements of these lemmas because there is a coercion from `ring_equiv` to `ring_hom`, but not `mul_equiv` to `monoid_hom`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* _root_.set.mem_image_equiv
- \+ *lemma* _root_.set.image_equiv_eq_preimage_symm
- \+ *lemma* _root_.set.preimage_equiv_eq_image_symm

Modified src/group_theory/subgroup.lean
- \+ *lemma* mem_map_equiv
- \+ *lemma* map_equiv_eq_comap_symm
- \+ *lemma* comap_equiv_eq_map_symm

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* mem_map_equiv
- \+ *lemma* map_equiv_eq_comap_symm
- \+ *lemma* comap_equiv_eq_map_symm

Modified src/linear_algebra/basic.lean
- \+ *lemma* map_equiv_eq_comap_symm
- \+ *lemma* comap_equiv_eq_map_symm

Modified src/ring_theory/subring.lean
- \+ *lemma* mem_map_equiv
- \+ *lemma* map_equiv_eq_comap_symm
- \+ *lemma* comap_equiv_eq_map_symm

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* mem_map_equiv
- \+ *lemma* map_equiv_eq_comap_symm
- \+ *lemma* comap_equiv_eq_map_symm



## [2021-07-28 19:44:39](https://github.com/leanprover-community/mathlib/commit/7180d2f)
feat(group_theory/coset): Show that `quotient_group.left_rel` and `left_coset_equivalence` are the same thing ([#8382](https://github.com/leanprover-community/mathlib/pull/8382))
#### Estimated changes
Modified src/group_theory/coset.lean
- \+ *lemma* left_coset_eq_iff
- \+ *lemma* right_coset_eq_iff
- \+ *lemma* left_rel_r_eq_left_coset_equivalence
- \+ *lemma* right_rel_r_eq_right_coset_equivalence
- \+/\- *def* left_rel
- \+/\- *def* quotient
- \+/\- *def* right_rel



## [2021-07-28 17:10:49](https://github.com/leanprover-community/mathlib/commit/32c8227)
feat(analysis/normed_space/basic): define inclusion `locally_constant X G → C(X, G)` as various types of bundled morphism ([#8448](https://github.com/leanprover-community/mathlib/pull/8448))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *def* to_continuous_map_monoid_hom
- \+ *def* to_continuous_map_linear_map
- \+ *def* to_continuous_map_alg_hom

Modified src/topology/locally_constant/algebra.lean
- \+ *lemma* coe_algebra_map
- \+ *def* const_monoid_hom
- \+ *def* const_ring_hom

Modified src/topology/locally_constant/basic.lean
- \+ *lemma* coe_const



## [2021-07-28 14:08:17](https://github.com/leanprover-community/mathlib/commit/b71d38c)
feat(algebra/big_operators/basic): add lemmas about prod and sum of finset.erase ([#8449](https://github.com/leanprover-community/mathlib/pull/8449))
This adds:
* `finset.prod_erase_mul`
* `finset.mul_prod_erase`
* `finset.sum_erase_add`
* `finset.add_sum_erase`
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* mul_prod_erase
- \+ *lemma* prod_erase_mul



## [2021-07-28 14:08:16](https://github.com/leanprover-community/mathlib/commit/0ccd2f6)
feat(data/dfinsupp): add simp lemma `single_eq_zero` ([#8447](https://github.com/leanprover-community/mathlib/pull/8447))
This matches `finsupp.single_eq_zero`.
Also adds `dfinsupp.ext_iff`, and changes some lemma arguments to be explicit.
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* ext_iff
- \+/\- *lemma* single_zero
- \+ *lemma* single_eq_zero
- \+/\- *lemma* single_add



## [2021-07-28 11:16:48](https://github.com/leanprover-community/mathlib/commit/4acfa92)
chore(algebra/floor): add a few trivial `simp` lemmas about `floor` ([#8450](https://github.com/leanprover-community/mathlib/pull/8450))
#### Estimated changes
Modified src/algebra/floor.lean
- \+/\- *theorem* floor_mono
- \+ *theorem* floor_int_add
- \+ *theorem* floor_add_nat
- \+ *theorem* floor_nat_add
- \+/\- *theorem* floor_sub_int
- \+ *theorem* floor_sub_nat



## [2021-07-28 09:02:05](https://github.com/leanprover-community/mathlib/commit/30ff935)
feat(topology/algebra): topological fields ([#8316](https://github.com/leanprover-community/mathlib/pull/8316))
Including the completion of completeable topological fields.
From the perfectoid spaces project.
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* map_comm
- \+ *lemma* comap_comm

Modified src/topology/algebra/field.lean
- \+ *lemma* units_topology_eq
- \+ *lemma* induced_units.continuous_coe
- \+ *lemma* units_embedding
- \+ *lemma* units_top_group
- \+ *lemma* continuous_units_inv
- \+ *def* topological_space_units

Created src/topology/algebra/uniform_field.lean
- \+ *lemma* continuous_hat_inv
- \+ *lemma* hat_inv_extends
- \+ *lemma* coe_inv
- \+ *lemma* mul_hat_inv_cancel
- \+ *def* hat_inv

Modified src/topology/basic.lean
- \+ *lemma* mem_closure_of_mem_closure_union
- \+ *lemma* mem_closure_image

Modified src/topology/constructions.lean
- \+ *lemma* prod_induced_induced



## [2021-07-28 02:23:58](https://github.com/leanprover-community/mathlib/commit/52e6e4c)
chore(scripts): update nolints.txt ([#8446](https://github.com/leanprover-community/mathlib/pull/8446))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-07-28 00:40:18](https://github.com/leanprover-community/mathlib/commit/7c5fa72)
refactor(group_theory/sylow): Extract a lemma from the proof of Cauchy's theorem ([#8376](https://github.com/leanprover-community/mathlib/pull/8376))
Also added one other consequence of card_modeq_card_fixed_points.
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* nonempty_fixed_point_of_prime_not_dvd_card
- \+ *lemma* exists_fixed_point_of_prime_dvd_card_of_fixed_point



## [2021-07-28 00:40:17](https://github.com/leanprover-community/mathlib/commit/37fc4cf)
feat(group_theory/subgroup): equiv_map_of_injective ([#8371](https://github.com/leanprover-community/mathlib/pull/8371))
Also for rings and submonoids. The version for modules, `submodule.equiv_map_of_injective`, was already there.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* coe_equiv_map_of_injective_apply

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* coe_equiv_map_of_injective_apply

Modified src/linear_algebra/basic.lean
- \+ *lemma* coe_equiv_map_of_injective_apply

Modified src/ring_theory/subring.lean
- \+ *lemma* coe_equiv_map_of_injective_apply

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* coe_equiv_map_of_injective_apply



## [2021-07-27 23:02:33](https://github.com/leanprover-community/mathlib/commit/cc7627a)
feat(analysis/normed_space/basic): define `normed_group` structure induced by injective group homomorphism ([#8443](https://github.com/leanprover-community/mathlib/pull/8443))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *def* semi_normed_group.induced
- \+ *def* normed_group.induced



## [2021-07-27 23:02:32](https://github.com/leanprover-community/mathlib/commit/1b0391a)
feat(data/nat/totient): totient_mul ([#8441](https://github.com/leanprover-community/mathlib/pull/8441))
Also made `data/nat/totient` import `data/zmod/basic` instead of the other way round because I think people are more likely to want `zmod` but not `totient` than `totient` but not `zmod`.
Also deleted the deprecated `gpowers` because it caused a name clash in `group_theory/subgroup` when the imports were changed.
#### Estimated changes
Modified src/data/nat/totient.lean
- \+ *lemma* _root_.zmod.card_units_eq_totient
- \+ *lemma* totient_mul

Modified src/data/zmod/basic.lean
- \- *lemma* card_units_eq_totient

Modified src/deprecated/subgroup.lean
- \- *lemma* is_subgroup.gpow_mem
- \- *lemma* is_add_subgroup.gsmul_mem
- \- *lemma* gpowers_subset
- \- *lemma* gmultiples_subset
- \- *lemma* mem_gpowers
- \- *lemma* mem_gmultiples
- \- *theorem* gpowers_eq_closure
- \- *def* gpowers
- \- *def* gmultiples

Modified src/linear_algebra/free_module_pid.lean




## [2021-07-27 23:02:31](https://github.com/leanprover-community/mathlib/commit/a445c45)
feat(measure_theory/interval_integrable): a monotone function is interval integrable ([#8398](https://github.com/leanprover-community/mathlib/pull/8398))
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integrable_of_monotone_on
- \+ *lemma* interval_integrable_of_antimono_on
- \+ *lemma* interval_integrable_of_monotone
- \+ *lemma* interval_integrable_of_antimono



## [2021-07-27 19:34:42](https://github.com/leanprover-community/mathlib/commit/9f75dc8)
feat(measure_theory/lebesgue_measure): volume s ≤ diam s ([#8437](https://github.com/leanprover-community/mathlib/pull/8437))
* for `s : set real`, `volume s ≤ diam s`;
* for `s : set (ι → real)`, `volume s ≤ ∏ i, diam (eval i '' s) ≤ diam s ^ fintype.card ι`.
#### Estimated changes
Modified src/measure_theory/lebesgue_measure.lean
- \+ *lemma* volume_le_diam
- \+ *lemma* volume_pi_le_prod_diam
- \+ *lemma* volume_pi_le_diam_pow

Modified src/topology/metric_space/basic.lean
- \+ *lemma* ediam_of_unbounded

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* edist_le_pi_edist

Modified src/topology/metric_space/lipschitz.lean




## [2021-07-27 19:34:41](https://github.com/leanprover-community/mathlib/commit/5375918)
feat(topology/metric_space/antilipschitz): ediam of image/preimage ([#8435](https://github.com/leanprover-community/mathlib/pull/8435))
Also review API
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* div_le_of_le_mul'
- \+ *lemma* mul_le_of_le_div
- \+ *lemma* mul_le_of_le_div'

Modified src/data/real/nnreal.lean
- \+ *lemma* div_le_of_le_mul
- \+ *lemma* div_le_of_le_mul'

Modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* antilipschitz_with_iff_le_mul_nndist
- \+/\- *lemma* antilipschitz_with_iff_le_mul_dist
- \+ *lemma* mul_le_nndist
- \+ *lemma* mul_le_dist
- \+ *lemma* ediam_preimage_le
- \+ *lemma* le_mul_ediam_image
- \- *lemma* antilipschitz_with.mul_le_dist



## [2021-07-27 19:34:40](https://github.com/leanprover-community/mathlib/commit/d57b6f9)
chore(data/dfinsupp): add yet more map_dfinsupp_sum lemmas ([#8400](https://github.com/leanprover-community/mathlib/pull/8400))
As always, the one of quadratically many combinations of `FOO_hom.map_BAR_sum` is never there when you need it.
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+/\- *lemma* prod_sum_index
- \+ *lemma* map_dfinsupp_prod
- \+ *lemma* map_dfinsupp_sum
- \+/\- *lemma* map_dfinsupp_sum_add_hom
- \+/\- *lemma* dfinsupp_sum_add_hom_apply
- \+/\- *lemma* coe_dfinsupp_sum_add_hom

Modified src/linear_algebra/basic.lean
- \+ *lemma* map_dfinsupp_sum_add_hom
- \+ *lemma* map_finsupp_sum
- \+ *lemma* map_dfinsupp_sum



## [2021-07-27 19:34:39](https://github.com/leanprover-community/mathlib/commit/aea21af)
feat(ring_theory): `is_dedekind_domain_inv` implies `is_dedekind_domain` ([#8315](https://github.com/leanprover-community/mathlib/pull/8315))
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean
- \+ *lemma* mul_inv_cancel_iff_is_unit
- \+/\- *lemma* is_dedekind_domain_inv_iff
- \+ *lemma* fractional_ideal.adjoin_integral_eq_one_of_is_unit
- \+ *lemma* mul_inv_eq_one
- \+ *lemma* inv_mul_eq_one
- \+ *lemma* is_noetherian_ring
- \+ *lemma* integrally_closed
- \+ *lemma* dimension_le_one
- \+ *theorem* is_dedekind_domain

Modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* mem_coe
- \+ *lemma* mem_coe_ideal_of_mem

Modified src/ring_theory/principal_ideal_domain.lean
- \+ *lemma* is_field.is_principal_ideal_ring



## [2021-07-27 19:34:38](https://github.com/leanprover-community/mathlib/commit/a052dd6)
doc(algebra/invertible): implementation notes about `invertible` instances ([#8197](https://github.com/leanprover-community/mathlib/pull/8197))
In the discussion on [#8195](https://github.com/leanprover-community/mathlib/pull/8195), I suggested to add these implementation notes. Creating a new PR should allow for a bit more direct discussion on the use of and plans for `invertible`.
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *def* something_that_needs_inverses
- \+ *def* something_one



## [2021-07-27 19:34:37](https://github.com/leanprover-community/mathlib/commit/2ea73d1)
feat(analysis/normed_space/SemiNormedGroup): has_cokernels ([#7628](https://github.com/leanprover-community/mathlib/pull/7628))
# Cokernels in SemiNormedGroup₁ and SemiNormedGroup
We show that `SemiNormedGroup₁` has cokernels
(for which of course the `cokernel.π f` maps are norm non-increasing),
as well as the easier result that `SemiNormedGroup` has cokernels.
So far, I don't see a way to state nicely what we really want:
`SemiNormedGroup` has cokernels, and `cokernel.π f` is norm non-increasing.
The problem is that the limits API doesn't promise you any particular model of the cokernel,
and in `SemiNormedGroup` one can always take a cokernel and rescale its norm
(and hence making `cokernel.π f` arbitrarily large in norm), obtaining another categorical cokernel.
#### Estimated changes
Created src/analysis/normed_space/SemiNormedGroup/kernels.lean
- \+ *def* cokernel_cocone
- \+ *def* cokernel_lift

Modified src/analysis/normed_space/normed_group_quotient.lean
- \+/\- *lemma* lift_mk
- \+ *lemma* lift_norm_le
- \+ *lemma* lift_norm_noninc



## [2021-07-27 16:37:38](https://github.com/leanprover-community/mathlib/commit/768980a)
feat(topology/locally_constant/basic): coercion of locally-constant function to continuous map ([#8444](https://github.com/leanprover-community/mathlib/pull/8444))
#### Estimated changes
Modified src/topology/locally_constant/basic.lean
- \+ *lemma* to_continuous_map_eq_coe
- \+ *lemma* coe_continuous_map
- \+ *lemma* to_continuous_map_injective
- \+ *def* to_continuous_map



## [2021-07-27 16:37:36](https://github.com/leanprover-community/mathlib/commit/3faee06)
feat(algebra/order_functions): max/min commutative and other props ([#8416](https://github.com/leanprover-community/mathlib/pull/8416))
The statements of the commutivity, associativity, and left commutativity of min and max are stated only in the rewrite lemmas, and not in their "commutative" synonyms.
This prevents them from being discoverable by suggest and related tactics. We now provide the synonyms explicitly.
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* max_commutative
- \+ *lemma* max_associative
- \+ *lemma* max_left_commutative
- \+ *lemma* min_commutative
- \+ *lemma* min_associative
- \+ *lemma* min_left_commutative



## [2021-07-27 16:37:35](https://github.com/leanprover-community/mathlib/commit/6c2f80c)
feat(category_theory/limits): disjoint coproducts ([#8380](https://github.com/leanprover-community/mathlib/pull/8380))
Towards a more detailed hierarchy of categorical properties.
#### Estimated changes
Created src/category_theory/limits/shapes/disjoint_coproduct.lean
- \+ *lemma* initial_mono_class_of_disjoint_coproducts
- \+ *def* is_initial_of_is_pullback_of_is_coproduct



## [2021-07-27 16:37:34](https://github.com/leanprover-community/mathlib/commit/bb44e1a)
feat(category_theory/subobject): generalise bot of subobject lattice ([#8232](https://github.com/leanprover-community/mathlib/pull/8232))
#### Estimated changes
Modified src/algebra/homology/homology.lean


Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/limits/shapes/zero.lean
- \- *lemma* has_initial
- \- *lemma* has_terminal
- \+ *def* zero_is_initial
- \+ *def* zero_is_terminal
- \+ *def* has_zero_object_of_has_initial_object
- \+ *def* has_zero_object_of_has_terminal_object

Modified src/category_theory/subobject/factor_thru.lean
- \+/\- *def* factors
- \+/\- *def* factor_thru

Modified src/category_theory/subobject/lattice.lean
- \+/\- *lemma* bot_left
- \+/\- *lemma* bot_arrow
- \+ *lemma* bot_arrow_eq_zero
- \+ *lemma* bot_eq_initial_to
- \+/\- *lemma* map_bot
- \+/\- *lemma* bot_eq_zero
- \+/\- *def* bot_coe_iso_zero
- \+ *def* bot_coe_iso_initial

Modified src/category_theory/subobject/limits.lean
- \+/\- *lemma* image_subobject_comp_le
- \+/\- *lemma* image_subobject_zero_arrow
- \+/\- *lemma* image_subobject_zero



## [2021-07-27 13:18:35](https://github.com/leanprover-community/mathlib/commit/b61ce02)
feat(number_theory/padics/padic_norm): add p^v(n) | n ([#8442](https://github.com/leanprover-community/mathlib/pull/8442))
Add some API for `padic_val_nat` (a convenient function for e.g. Sylow theory).
#### Estimated changes
Modified src/number_theory/padics/padic_norm.lean
- \+ *lemma* pow_padic_val_nat_dvd
- \+ *lemma* pow_succ_padic_val_nat_not_dvd

Modified src/ring_theory/multiplicity.lean
- \+ *lemma* ne_top_iff_finite
- \+ *lemma* lt_top_iff_finite



## [2021-07-27 10:18:45](https://github.com/leanprover-community/mathlib/commit/7ae8da4)
fix(algebra/big_operators/ring): `finset.sum_mul_sum` is true in a non-assoc non-unital semiring ([#8436](https://github.com/leanprover-community/mathlib/pull/8436))
#### Estimated changes
Modified src/algebra/big_operators/ring.lean
- \+/\- *lemma* sum_mul_sum



## [2021-07-27 10:18:44](https://github.com/leanprover-community/mathlib/commit/3b590f3)
feat(logic/embedding): add a coe instance from equiv to embeddings ([#8323](https://github.com/leanprover-community/mathlib/pull/8323))
#### Estimated changes
Modified src/logic/embedding.lean
- \+ *lemma* equiv.coe_eq_to_embedding
- \+/\- *def* equiv.as_embedding

Created test/equiv.lean
- \+ *def* s
- \+ *def* f



## [2021-07-27 08:42:12](https://github.com/leanprover-community/mathlib/commit/23e7c84)
fix(algebra/ordered_group): add missing `to_additive`, fix `simps` ([#8429](https://github.com/leanprover-community/mathlib/pull/8429))
* Add `order_iso.add_left` and `order_iso.add_right`.
* Use `to_equiv :=` instead of `..` to ensure
  `rfl : (order_iso.mul_right a).to_equiv = equiv.mul_right a`.
* Simplify unapplied `(order_iso.mul_left a).symm` etc.
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* order_iso.mul_right_symm
- \+ *lemma* order_iso.mul_left_symm



## [2021-07-27 08:42:11](https://github.com/leanprover-community/mathlib/commit/391746b)
feat(data/zmod/basic): chinese remainder theorem ([#8356](https://github.com/leanprover-community/mathlib/pull/8356))
#### Estimated changes
Modified src/algebra/char_p/basic.lean


Modified src/algebra/ring/prod.lean
- \+ *def* prod_zero_ring
- \+ *def* zero_ring_prod

Modified src/data/fintype/basic.lean
- \+ *lemma* right_inverse_of_left_inverse_of_card_le
- \+ *lemma* left_inverse_of_right_inverse_of_card_le

Modified src/data/int/cast.lean
- \+ *lemma* fst_int_cast
- \+ *lemma* snd_int_cast

Modified src/data/nat/cast.lean
- \+ *lemma* fst_nat_cast
- \+ *lemma* snd_nat_cast

Modified src/data/nat/gcd.lean
- \+ *lemma* lcm_dvd_iff
- \+ *lemma* coprime.eq_of_mul_eq_zero

Modified src/data/zmod/basic.lean
- \+/\- *lemma* card
- \+ *lemma* _root_.prod.fst_zmod_cast
- \+ *lemma* _root_.prod.snd_zmod_cast
- \+ *def* chinese_remainder



## [2021-07-27 08:42:10](https://github.com/leanprover-community/mathlib/commit/65006d2)
feat(linear_algebra/linear_independent): finsupp.total is not equal to a vector outside the support of the coefficients ([#8338](https://github.com/leanprover-community/mathlib/pull/8338))
…
#### Estimated changes
Modified src/linear_algebra/finsupp.lean
- \+ *lemma* mem_supported_support

Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.not_mem_span_image
- \+ *lemma* linear_independent.total_ne_of_not_mem_support



## [2021-07-27 08:42:09](https://github.com/leanprover-community/mathlib/commit/7e37f20)
feat(group_theory/perm/cycles): more lemmas ([#8175](https://github.com/leanprover-community/mathlib/pull/8175))
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_eq_zero_iff
- \+ *lemma* pow_inj_iff_of_order_of_eq_zero
- \+ *lemma* pow_inj_mod
- \+ *lemma* nsmul_inj_mod

Modified src/group_theory/perm/cycles.lean
- \+ *lemma* not_is_cycle_one
- \+ *lemma* is_cycle.exists_pow_eq_one
- \+ *lemma* is_cycle_of_is_cycle_pow
- \+/\- *lemma* is_cycle_of_is_cycle_gpow
- \+ *lemma* nodup_of_pairwise_disjoint_cycles
- \+ *lemma* same_cycle.nat'
- \+ *lemma* same_cycle.nat''
- \+ *lemma* same_cycle_pow_left_iff
- \+ *lemma* is_cycle.support_pow_eq_iff
- \+ *lemma* is_cycle.pow_iff
- \+ *lemma* is_cycle.pow_eq_one_iff
- \+ *lemma* is_cycle.mem_support_pos_pow_iff_of_lt_order_of
- \+ *lemma* is_cycle.is_cycle_pow_pos_of_lt_prime_order
- \+ *lemma* cycle_of_apply_apply_gpow_self
- \+ *lemma* cycle_of_apply_apply_pow_self
- \+ *lemma* cycle_of_apply_apply_self
- \+ *lemma* pow_apply_eq_pow_mod_order_of_cycle_of_apply
- \+ *lemma* cycle_of_mul_of_apply_right_eq_self
- \+ *lemma* disjoint.cycle_of_mul_distrib
- \+ *lemma* support_cycle_of_eq_nil_iff
- \+ *lemma* mem_support_cycle_of_iff
- \+/\- *lemma* cycle_factors_finset_noncomm_prod
- \+ *lemma* cycle_of_mem_cycle_factors_finset_iff
- \+ *lemma* mem_cycle_factors_finset_support_le
- \+/\- *lemma* cycle_factors_finset_eq_empty_iff
- \+ *lemma* cycle_factors_finset_one
- \+/\- *lemma* cycle_factors_finset_eq_singleton_self_iff
- \+ *lemma* is_cycle.cycle_factors_finset_eq_singleton
- \+/\- *lemma* cycle_factors_finset_eq_singleton_iff
- \+ *lemma* disjoint.disjoint_cycle_factors_finset
- \+ *lemma* disjoint.cycle_factors_finset_mul_eq_union
- \+ *lemma* disjoint_mul_inv_of_mem_cycle_factors_finset
- \+ *lemma* cycle_factors_finset_mul_inv_mem_eq_sdiff
- \+ *lemma* same_cycle.nat_of_mem_support
- \+ *lemma* same_cycle.nat

Modified src/group_theory/perm/support.lean
- \+ *lemma* disjoint.mono



## [2021-07-27 07:49:28](https://github.com/leanprover-community/mathlib/commit/d99788a)
feat(measure_theory/borel_space): lemmas about `is_pi_system_Ioo` and `finite_spanning_sets_in` ([#8434](https://github.com/leanprover-community/mathlib/pull/8434))
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_pi_system_Ioo_mem
- \+ *lemma* is_pi_system_Ioo
- \+ *lemma* is_pi_system_Ioo_rat
- \+ *def* finite_spanning_sets_in_Ioo_rat



## [2021-07-27 07:49:27](https://github.com/leanprover-community/mathlib/commit/eae3ead)
feat(topology/instances/ennreal): diameter of `s : set real` ([#8433](https://github.com/leanprover-community/mathlib/pull/8433))
#### Estimated changes
Modified src/data/real/basic.lean
- \+ *lemma* add_neg_lt_Sup
- \+ *lemma* Inf_le_Sup
- \- *lemma* add_pos_lt_Sup
- \+/\- *theorem* Sup_empty
- \+/\- *theorem* Inf_empty

Modified src/topology/instances/ennreal.lean
- \+ *lemma* metric.diam_closure
- \+ *lemma* real.ediam_eq
- \+ *lemma* real.diam_eq

Modified src/topology/instances/real.lean
- \+ *lemma* real.subset_Icc_Inf_Sup_of_bounded

Modified src/topology/metric_space/basic.lean




## [2021-07-27 06:14:26](https://github.com/leanprover-community/mathlib/commit/fb815d7)
feat(algebra/ring/basic): coercions of ring_hom.id ([#8439](https://github.com/leanprover-community/mathlib/pull/8439))
Two basic lemmas about the identity map as a ring hom, split off from [#3292](https://github.com/leanprover-community/mathlib/pull/3292) at @eric-wieser's suggestion.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* coe_add_monoid_hom_id
- \+ *lemma* coe_monoid_hom_id



## [2021-07-26 23:52:54](https://github.com/leanprover-community/mathlib/commit/e9309e3)
chore(data/equiv/list): rename `encodable.fintype.encodable` to `fintype.encodable` ([#8428](https://github.com/leanprover-community/mathlib/pull/8428))
#### Estimated changes
Modified src/data/equiv/list.lean


Modified src/measure_theory/measure_space.lean




## [2021-07-26 22:05:39](https://github.com/leanprover-community/mathlib/commit/26528b7)
chore(data/set): add a couple of lemmas ([#8430](https://github.com/leanprover-community/mathlib/pull/8430))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* subsingleton.preimage

Modified src/data/set/lattice.lean
- \+ *lemma* image_bUnion



## [2021-07-26 15:58:30](https://github.com/leanprover-community/mathlib/commit/0190177)
feat(group_theory/subgroup): eq_top_of_le_card and eq_bot_of_card_le ([#8414](https://github.com/leanprover-community/mathlib/pull/8414))
Slight strengthenings of the lemmas `eq_top_of_card_eq` and `eq_bot_of_card_eq`.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* eq_top_of_le_card
- \+ *lemma* eq_bot_of_card_le



## [2021-07-26 15:58:29](https://github.com/leanprover-community/mathlib/commit/d8fc081)
chore(data/pnat/basic): rename `bot_eq_zero` to `bot_eq_one`, generalize from `Prop` to `Sort*` ([#8412](https://github.com/leanprover-community/mathlib/pull/8412))
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+/\- *lemma* coe_le_coe
- \+/\- *lemma* coe_lt_coe
- \+ *lemma* bot_eq_one
- \+/\- *lemma* exists_eq_succ_of_ne_one
- \- *lemma* bot_eq_zero
- \- *lemma* strong_induction_on
- \- *lemma* case_strong_induction_on
- \+/\- *theorem* ne_zero
- \+/\- *theorem* rec_on_succ
- \+ *def* strong_induction_on
- \+ *def* case_strong_induction_on
- \+/\- *def* rec_on



## [2021-07-26 15:58:28](https://github.com/leanprover-community/mathlib/commit/1dc4bef)
feat(ring_theory): shortcut lemmas for `coe : ideal R → fractional_ideal R⁰ K` ([#8395](https://github.com/leanprover-community/mathlib/pull/8395))
These results were already available, but in a less convenient form that e.g. asked you to prove an inclusion of submonoids `S ≤ R⁰`. Specializing them to the common case where the fractional ideal is in the field of fractions should save a bit of headache in the common cases.
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* coe_ideal_le_coe_ideal'
- \+ *lemma* coe_ideal_le_coe_ideal
- \+ *lemma* coe_ideal_injective
- \+ *lemma* coe_ideal_eq_zero_iff
- \+ *lemma* coe_ideal_ne_zero_iff
- \+ *lemma* coe_ideal_ne_zero



## [2021-07-26 15:58:27](https://github.com/leanprover-community/mathlib/commit/708b25d)
feat(ring_theory): (fractional) ideals are finitely generated if they are invertible ([#8294](https://github.com/leanprover-community/mathlib/pull/8294))
This is one of the three steps in showing `is_dedekind_domain_inv` implies `is_dedekind_domain`.
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* mem_span_mul_finite_of_mem_mul
- \+ *lemma* coe_ideal_fg
- \+ *lemma* fg_unit
- \+ *lemma* fg_of_is_unit
- \+ *lemma* _root_.ideal.fg_of_is_unit

Modified src/ring_theory/localization.lean
- \+ *lemma* coe_submodule_fg



## [2021-07-26 14:30:57](https://github.com/leanprover-community/mathlib/commit/4ca0a8b)
feat(data/fintype/basic): provide a `fintype` instance for `sym α n` ([#8427](https://github.com/leanprover-community/mathlib/pull/8427))
This also provides `fintype (sym.sym' α n)` as an intermediate step.
Note we make `vector.perm.is_setoid` reducible as `quotient.fintype _` requires either this or `local attribute [instance] vector.perm.is_setoid` to be accepted by the elaborator.
The referenced library note suggests making it reducible is fine.
#### Estimated changes
Modified src/data/fintype/basic.lean


Modified src/data/sym.lean




## [2021-07-26 07:37:51](https://github.com/leanprover-community/mathlib/commit/740b41b)
feat(data/fintype/basic): add `finset.(sup|inf)_univ_eq_(supr|infi)` ([#8397](https://github.com/leanprover-community/mathlib/pull/8397))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* sup_univ_eq_supr
- \+ *lemma* inf_univ_eq_infi



## [2021-07-25 15:51:33](https://github.com/leanprover-community/mathlib/commit/0c024a6)
chore(*): standardize Prop/Type instance names ([#8360](https://github.com/leanprover-community/mathlib/pull/8360))
autogenerated names for these instances mention `sort.` instead of `Prop.`
#### Estimated changes
Modified src/category_theory/preadditive/projective.lean


Modified src/order/boolean_algebra.lean


Modified src/order/bounded_lattice.lean


Modified src/order/complete_boolean_algebra.lean


Modified src/order/complete_lattice.lean


Modified src/tactic/has_variable_names.lean


Modified src/testing/slim_check/sampleable.lean




## [2021-07-25 15:12:53](https://github.com/leanprover-community/mathlib/commit/2440330)
feat(linear_algebra/matrix/determinant): det_pow ([#8421](https://github.com/leanprover-community/mathlib/pull/8421))
#### Estimated changes
Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* det_pow



## [2021-07-25 07:06:29](https://github.com/leanprover-community/mathlib/commit/fff96e5)
feat(measure_theory/vector_measure): add partial order instance to vector measures ([#8410](https://github.com/leanprover-community/mathlib/pull/8410))
#### Estimated changes
Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/vector_measure.lean
- \+ *lemma* le_iff
- \+ *lemma* le_iff'



## [2021-07-24 22:55:28](https://github.com/leanprover-community/mathlib/commit/02b37b5)
feat(group_theory/subgroup): eq_bot_of_card_eq ([#8413](https://github.com/leanprover-community/mathlib/pull/8413))
Companion lemma to `eq_top_of_card_eq`.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* eq_bot_of_card_eq



## [2021-07-24 15:30:35](https://github.com/leanprover-community/mathlib/commit/8a0d5e0)
feat(group_theory/complement): define subgroup complement, prove Schur-Zassenhaus ([#8008](https://github.com/leanprover-community/mathlib/pull/8008))
Defines complements, and proves Schur-Zassenhaus for abelian normal subgroups.
#### Estimated changes
Created src/group_theory/complement.lean
- \+ *lemma* is_complement_iff_exists_unique
- \+ *lemma* is_complement.exists_unique
- \+ *lemma* is_complement.symm
- \+ *lemma* is_complement_comm
- \+ *lemma* mem_left_transversals_iff_exists_unique_inv_mul_mem
- \+ *lemma* mem_right_transversals_iff_exists_unique_mul_inv_mem
- \+ *lemma* mem_left_transversals_iff_exists_unique_quotient_mk'_eq
- \+ *lemma* mem_right_transversals_iff_exists_unique_quotient_mk'_eq
- \+ *lemma* mem_left_transversals_iff_bijective
- \+ *lemma* mem_right_transversals_iff_bijective
- \+ *lemma* is_complement_of_disjoint
- \+ *lemma* is_complement_of_coprime
- \+ *lemma* smul_symm_apply_eq_mul_symm_apply_inv_smul
- \+ *lemma* diff_mul_diff
- \+ *lemma* diff_self
- \+ *lemma* diff_inv
- \+ *lemma* smul_diff_smul
- \+ *lemma* smul_diff
- \+ *lemma* exists_smul_eq
- \+ *lemma* smul_injective
- \+ *lemma* is_complement_stabilizer_of_coprime
- \+ *theorem* exists_right_complement_of_coprime
- \+ *theorem* exists_left_complement_of_coprime
- \+ *def* is_complement
- \+ *def* left_transversals
- \+ *def* right_transversals
- \+ *def* quotient_diff

Modified src/group_theory/order_of_element.lean
- \+ *lemma* inf_eq_bot_of_coprime

Modified src/group_theory/subgroup.lean




## [2021-07-24 14:21:11](https://github.com/leanprover-community/mathlib/commit/3d11f2d)
refactor(data/set/disjointed): split into `data.set.pairwise` and `order.disjointed` ([#8411](https://github.com/leanprover-community/mathlib/pull/8411))
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified src/algebra/big_operators/finprod.lean


Modified src/data/equiv/encodable/lattice.lean


Modified src/data/mv_polynomial/variables.lean


Created src/data/set/pairwise.lean
- \+ *theorem* set.pairwise_on_univ
- \+ *theorem* set.pairwise_on.on_injective
- \+ *theorem* pairwise.mono
- \+ *theorem* pairwise_on_bool
- \+ *theorem* pairwise_disjoint_on_bool
- \+ *theorem* pairwise_on_nat
- \+ *theorem* pairwise_disjoint_on_nat
- \+ *theorem* pairwise.pairwise_on
- \+ *theorem* pairwise_disjoint_fiber
- \+ *def* pairwise

Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measurable_space_def.lean


Renamed src/data/set/disjointed.lean to src/order/disjointed.lean
- \- *theorem* set.pairwise_on_univ
- \- *theorem* set.pairwise_on.on_injective
- \- *theorem* pairwise.mono
- \- *theorem* pairwise_on_bool
- \- *theorem* pairwise_disjoint_on_bool
- \- *theorem* pairwise_on_nat
- \- *theorem* pairwise_disjoint_on_nat
- \- *theorem* pairwise.pairwise_on
- \- *theorem* pairwise_disjoint_fiber
- \- *def* pairwise

Modified src/order/partial_sups.lean


Modified src/ring_theory/coprime.lean


Modified src/topology/algebra/ordered/basic.lean




## [2021-07-23 17:15:08](https://github.com/leanprover-community/mathlib/commit/dfa95ab)
feat(analysis/normed_space/linear_isometry): add an upgrade from linear isometries between finite dimensional spaces of eq finrank to linear isometry equivs ([#8406](https://github.com/leanprover-community/mathlib/pull/8406))
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* coe_to_linear_isometry_equiv
- \+ *lemma* to_linear_isometry_equiv_apply



## [2021-07-23 11:58:54](https://github.com/leanprover-community/mathlib/commit/8062521)
feat(topology/locally_constant): Adding a module structure to locally constant functions ([#8384](https://github.com/leanprover-community/mathlib/pull/8384))
We add an A-module structure to locally constant functions from a topological space to a semiring A.
This also adds the lemmas `coe_zero`, `coe_add`, `coe_neg`, `coe_sub`, `coe_one`, `coe_mul`, `coe_div`, `coe_inv` to match the new `coe_smul` lemma.
#### Estimated changes
Modified src/topology/locally_constant/algebra.lean
- \+ *lemma* coe_one
- \+/\- *lemma* one_apply
- \+ *lemma* coe_inv
- \+/\- *lemma* inv_apply
- \+ *lemma* coe_mul
- \+/\- *lemma* mul_apply
- \+ *lemma* coe_div
- \+ *lemma* coe_smul
- \+ *lemma* smul_apply
- \+ *def* coe_fn_monoid_hom



## [2021-07-23 10:09:40](https://github.com/leanprover-community/mathlib/commit/f2f6228)
feat(set/basic): range_splitting f : range f → α ([#8340](https://github.com/leanprover-community/mathlib/pull/8340))
We use choice to provide an arbitrary injective splitting `range f → α` for any `f : α → β`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* range_factorization_coe
- \+ *lemma* apply_range_splitting
- \+ *lemma* comp_range_splitting
- \+ *lemma* left_inverse_range_splitting
- \+ *lemma* range_splitting_injective



## [2021-07-23 09:02:53](https://github.com/leanprover-community/mathlib/commit/6efc3e9)
fix(data/polynomial): Resolve a has_scalar instance diamond ([#8392](https://github.com/leanprover-community/mathlib/pull/8392))
Without this change, the following fails to close the diamond between `units.distrib_mul_action` and`polynomial.distrib_mul_action`:
```lean
example (R α : Type*) (β : α → Type*) [monoid R] [semiring α] [distrib_mul_action R α] :
  (units.distrib_mul_action : distrib_mul_action (units R) (polynomial α)) =
    polynomial.distrib_mul_action :=
rfl
```
This was because both used `polynomial.smul`, which was:
* `@[irreducible]`, which means that typeclass search is unable to unfold it to see there is no diamond
* Defined using a pattern match, which means that even if it were not reducible, it does not unfold as needed.
This adds a new test file with this diamond and some other diamonds to verify they are defeq.
Unfortunately this means `simps` now aggressively unfolds `•` on polynomials into `finsupp`s, so we need to tell `simps` precisely what lemma we actually want. This only happens in one place though.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/units.2Ehas_scalar.20and.20polynomial.2Ehas_scalar.20diamond/near/246800881)
#### Estimated changes
Modified src/data/polynomial/basic.lean


Modified src/ring_theory/polynomial_algebra.lean


Created test/instance_diamonds.lean




## [2021-07-23 09:02:52](https://github.com/leanprover-community/mathlib/commit/ced1f12)
feat(analysis/calculus): strictly differentiable (or C^1) map is locally Lipschitz ([#8362](https://github.com/leanprover-community/mathlib/pull/8362))
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_strict_fderiv_at.exists_lipschitz_on_with_of_nnnorm_lt
- \+ *lemma* has_strict_fderiv_at.exists_lipschitz_on_with

Modified src/analysis/calculus/mean_value.lean
- \+ *lemma* convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt
- \+ *lemma* convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at
- \- *lemma* convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_continuous_within_at

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* has_ftaylor_series_up_to_on.exists_lipschitz_on_with_of_nnnorm_lt
- \+ *lemma* has_ftaylor_series_up_to_on.exists_lipschitz_on_with
- \+ *lemma* times_cont_diff_within_at.exists_lipschitz_on_with
- \+ *lemma* times_cont_diff_at.exists_lipschitz_on_with_of_nnnorm_lt
- \+ *lemma* times_cont_diff_at.exists_lipschitz_on_with

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* add_monoid_hom.lipschitz_of_bound
- \+ *lemma* lipschitz_with_iff_norm_sub_le
- \+ *lemma* add_monoid_hom.lipschitz_of_bound_nnnorm

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* linear_map.lipschitz_of_bound_nnnorm
- \+ *theorem* le_op_nnnorm
- \+/\- *theorem* lipschitz
- \+ *theorem* is_O_with_id
- \+/\- *theorem* is_O_id
- \+ *theorem* is_O_with_comp
- \+/\- *theorem* is_O_comp
- \+ *theorem* is_O_with_sub
- \+/\- *theorem* is_O_sub



## [2021-07-23 09:02:51](https://github.com/leanprover-community/mathlib/commit/1dafd0f)
feat(measure_theory/integrable_on): a monotone function is integrable on any compact subset ([#8336](https://github.com/leanprover-community/mathlib/pull/8336))
#### Estimated changes
Modified src/measure_theory/integrable_on.lean
- \+ *lemma* integrable_on_compact_of_monotone_on
- \+ *lemma* integrable_on_compact_of_antimono_on
- \+ *lemma* integrable_on_compact_of_monotone
- \+ *lemma* integrable_on_compact_of_antimono



## [2021-07-23 08:09:01](https://github.com/leanprover-community/mathlib/commit/970b17b)
refactor(topology/metric_space): move lemmas about `paracompact_space` and the shrinking lemma to separate files ([#8404](https://github.com/leanprover-community/mathlib/pull/8404))
Only a few files in `mathlib` actually depend on results about `paracompact_space`. With this refactor, only a few files depend on `topology/paracompact_space` and `topology/shrinking_lemma`. The main side effects are that `paracompact_of_emetric` and `normal_of_emetric` instances are not available without importing `topology.metric_space.emetric_paracompact` and the shrinking lemma for balls in a proper metric space is not available without `import topology.metric_space.shrinking_lemma`.
#### Estimated changes
Modified src/analysis/fourier.lean


Modified src/geometry/manifold/partition_of_unity.lean


Modified src/topology/metric_space/basic.lean
- \- *lemma* exists_subset_Union_ball_radius_lt
- \- *lemma* exists_Union_ball_eq_radius_lt
- \- *lemma* exists_subset_Union_ball_radius_pos_lt
- \- *lemma* exists_Union_ball_eq_radius_pos_lt
- \- *lemma* exists_locally_finite_subset_Union_ball_radius_lt
- \- *lemma* exists_locally_finite_Union_eq_ball_radius_lt

Created src/topology/metric_space/emetric_paracompact.lean


Modified src/topology/metric_space/emetric_space.lean


Created src/topology/metric_space/shrinking_lemma.lean
- \+ *lemma* exists_subset_Union_ball_radius_lt
- \+ *lemma* exists_Union_ball_eq_radius_lt
- \+ *lemma* exists_subset_Union_ball_radius_pos_lt
- \+ *lemma* exists_Union_ball_eq_radius_pos_lt
- \+ *lemma* exists_locally_finite_subset_Union_ball_radius_lt
- \+ *lemma* exists_locally_finite_Union_eq_ball_radius_lt



## [2021-07-23 04:48:50](https://github.com/leanprover-community/mathlib/commit/0dd81c1)
chore(topology/urysohns_lemma): use bundled `C(X, ℝ)` ([#8402](https://github.com/leanprover-community/mathlib/pull/8402))
#### Estimated changes
Modified src/measure_theory/continuous_map_dense.lean


Modified src/topology/urysohns_lemma.lean




## [2021-07-23 02:11:57](https://github.com/leanprover-community/mathlib/commit/88de9b5)
chore(scripts): update nolints.txt ([#8403](https://github.com/leanprover-community/mathlib/pull/8403))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-07-23 00:02:46](https://github.com/leanprover-community/mathlib/commit/316d69f)
feat(measure_theory/measure_space): add measurable set lemma for symmetric differences ([#8401](https://github.com/leanprover-community/mathlib/pull/8401))
#### Estimated changes
Modified src/measure_theory/measurable_space_def.lean
- \+ *lemma* measurable_set.symm_diff
- \+ *lemma* measurable_set.cond

Modified src/measure_theory/measure_space.lean
- \- *lemma* cond

Modified src/measure_theory/tactic.lean




## [2021-07-22 21:19:37](https://github.com/leanprover-community/mathlib/commit/0cbc6f3)
feat(linear_algebra/matrix/determinant): generalize det_fin_zero to det_eq_one_of_is_empty ([#8387](https://github.com/leanprover-community/mathlib/pull/8387))
Also golfs a nearby proof
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* univ_is_empty
- \+ *lemma* card_eq_one_iff_nonempty_unique
- \+/\- *theorem* univ_of_is_empty

Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* det_is_empty
- \- *lemma* det_fin_zero



## [2021-07-22 17:40:08](https://github.com/leanprover-community/mathlib/commit/468328d)
chore(group_theory/subgroup): the range of a monoid/group/ring/module hom from a finite type is finite ([#8293](https://github.com/leanprover-community/mathlib/pull/8293))
We have this fact for maps of types, but when changing `is_group_hom` etc from classes to structures one needs it for other bundled maps. The proofs use the power of the `copy` trick.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/field_theory/subfield.lean


Modified src/group_theory/subgroup.lean


Modified src/linear_algebra/basic.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/subsemiring.lean




## [2021-07-22 16:15:21](https://github.com/leanprover-community/mathlib/commit/0bc800c)
feat(algebra/algebra/basic) new bit0/1_smul_one lemmas ([#8394](https://github.com/leanprover-community/mathlib/pull/8394))
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Import.20impacts.20simp.3F/near/246713984, these lemmas should result in better behaviour with numerals
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* bit0_smul_one
- \+ *lemma* bit0_smul_one'
- \+/\- *lemma* bit1_smul_one
- \+ *lemma* bit1_smul_one'



## [2021-07-22 16:15:20](https://github.com/leanprover-community/mathlib/commit/7cdd702)
chore(ring_theory): `set_like` instance for fractional ideals ([#8275](https://github.com/leanprover-community/mathlib/pull/8275))
This PR does a bit of cleanup in `fractional_ideal.lean` by using `set_like` to define `has_mem` and the coe to set.
As a bonus, it removes the `namespace ring` at the top of the file, that has been bugging me ever after I added it in the original fractional ideal PR.
#### Estimated changes
Modified docs/overview.yaml


Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* ext
- \+/\- *lemma* val_eq_coe
- \+/\- *lemma* coe_mk
- \+ *lemma* mem_coe
- \+ *lemma* coe_to_submodule_injective
- \+ *lemma* is_fractional_of_le_one
- \+/\- *lemma* fractional_sup
- \+/\- *lemma* fractional_inf
- \+/\- *lemma* fractional_mul
- \- *lemma* coe_injective
- \- *lemma* ext_iff
- \- *lemma* fractional_of_subset_one
- \- *lemma* le_iff_mem



## [2021-07-22 14:12:58](https://github.com/leanprover-community/mathlib/commit/38ac9ba)
chore(algebra/module/submodule): add submodule.coe_sum ([#8393](https://github.com/leanprover-community/mathlib/pull/8393))
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *lemma* coe_sum



## [2021-07-22 14:12:57](https://github.com/leanprover-community/mathlib/commit/e2cda0b)
chore(*): Prevent lemmas about the injectivity of `coe_fn` introducing un-reduced lambda terms ([#8386](https://github.com/leanprover-community/mathlib/pull/8386))
This follows on from [#6344](https://github.com/leanprover-community/mathlib/pull/6344), and fixes every result for `function.injective (λ` that is about coe_fn.
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+/\- *lemma* coe_injective

Modified src/analysis/normed_space/enorm.lean
- \+/\- *lemma* coe_fn_injective

Modified src/data/equiv/basic.lean
- \+/\- *theorem* coe_fn_injective

Modified src/linear_algebra/affine_space/affine_map.lean
- \+/\- *lemma* coe_fn_injective

Modified src/order/rel_iso.lean
- \+/\- *theorem* coe_fn_injective

Modified src/topology/algebra/module.lean
- \+/\- *theorem* coe_fn_injective

Modified src/topology/locally_constant/basic.lean
- \+/\- *theorem* coe_injective



## [2021-07-22 14:12:56](https://github.com/leanprover-community/mathlib/commit/54adb19)
doc(algebra/to_additive): Add troubleshooting section ([#8143](https://github.com/leanprover-community/mathlib/pull/8143))
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/tactic/transform_decl.lean




## [2021-07-22 12:14:07](https://github.com/leanprover-community/mathlib/commit/791d51c)
feat(group_theory/group_action): a monoid action determines a monoid hom ([#8253](https://github.com/leanprover-community/mathlib/pull/8253))
Defines the monoid hom `M -> category_theory.End X` (the latter is the monoid `X -> X`) corresponding to an action `mul_action M X` and vice versa.
Split off from [#7395](https://github.com/leanprover-community/mathlib/pull/7395)
#### Estimated changes
Modified src/group_theory/group_action/defs.lean
- \+ *lemma* function.End.smul_def
- \+ *def* mul_action.to_End_hom
- \+ *def* mul_action.of_End_hom
- \+ *def* add_action.to_End_hom
- \+ *def* add_action.of_End_hom

Modified src/group_theory/group_action/group.lean
- \+ *lemma* equiv.perm.smul_def



## [2021-07-22 11:40:10](https://github.com/leanprover-community/mathlib/commit/6f88eec)
feat(algebra/lie/{submodule,subalgebra}): `lie_span`, `coe` form a Galois insertion ([#8213](https://github.com/leanprover-community/mathlib/pull/8213))
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* span_empty
- \+ *lemma* span_univ
- \+ *lemma* span_union
- \+ *lemma* span_Union

Modified src/algebra/lie/submodule.lean
- \+ *lemma* span_empty
- \+ *lemma* span_univ
- \+ *lemma* span_union
- \+ *lemma* span_Union



## [2021-07-22 07:37:52](https://github.com/leanprover-community/mathlib/commit/c9593dc)
feat(algebra/lie/direct_sum): define `direct_sum.lie_of`, `direct_sum.to_lie_algebra`, `direct_sum.lie_algebra_is_internal` ([#8369](https://github.com/leanprover-community/mathlib/pull/8369))
Various other minor improvements.
#### Estimated changes
Modified src/algebra/lie/direct_sum.lean
- \+ *lemma* lie_algebra_ext
- \+ *lemma* lie_of_of_ne
- \+ *lemma* lie_of_of_eq
- \+ *lemma* lie_of
- \+/\- *def* lie_algebra_of
- \+/\- *def* lie_algebra_component
- \+ *def* to_lie_algebra
- \+ *def* lie_algebra_is_internal

Modified src/linear_algebra/direct_sum_module.lean
- \+ *lemma* coe_to_module_eq_coe_to_add_monoid



## [2021-07-22 06:50:48](https://github.com/leanprover-community/mathlib/commit/df50b6c)
feat(category_theory/limits): strict initial objects are initial mono ([#8267](https://github.com/leanprover-community/mathlib/pull/8267))
- [x] depends on: [#8094](https://github.com/leanprover-community/mathlib/pull/8094) 
- [x] depends on: [#8099](https://github.com/leanprover-community/mathlib/pull/8099)
#### Estimated changes
Modified src/category_theory/limits/shapes/strict_initial.lean


Modified src/category_theory/limits/shapes/terminal.lean




## [2021-07-22 02:19:36](https://github.com/leanprover-community/mathlib/commit/bc65818)
chore(scripts): update nolints.txt ([#8390](https://github.com/leanprover-community/mathlib/pull/8390))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-07-21 22:22:58](https://github.com/leanprover-community/mathlib/commit/9e35530)
fix(order/lattice, tactic.simps): add missing `notation_class` attributes to `has_(bot,top,inf,sup,compl)` ([#8381](https://github.com/leanprover-community/mathlib/pull/8381))
From the docs for `simps`:
> `@[notation_class]` should be added to all classes that define notation, like `has_mul` and
> `has_zero`. This specifies that the projections that `@[simps]` used are the projections from
> these notation classes instead of the projections of the superclasses.
> Example: if `has_mul` is tagged with `@[notation_class]` then the projection used for `semigroup`
> will be `λ α hα, @has_mul.mul α (@semigroup.to_has_mul α hα)` instead of `@semigroup.mul`.
#### Estimated changes
Modified src/order/boolean_algebra.lean


Modified src/order/bounded_lattice.lean


Modified src/order/lattice.lean




## [2021-07-21 22:22:56](https://github.com/leanprover-community/mathlib/commit/f118c14)
feat(order): if `f x ≤ f y → x ≤ y`, then `f` is injective ([#8373](https://github.com/leanprover-community/mathlib/pull/8373))
I couldn't find this specific result, not assuming linear orders, anywhere and [the Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/If.20.60f.20x.20.E2.89.A4.20f.20y.20.E2.86.92.20x.20.E2.89.A4.20y.60.2C.20then.20.60f.60.20is.20injective) didn't get any responses, so I decided to PR the result.
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* injective_of_le_imp_le



## [2021-07-21 21:31:53](https://github.com/leanprover-community/mathlib/commit/3e6c367)
chore(topology/algebra/module): harmless generalization ([#8389](https://github.com/leanprover-community/mathlib/pull/8389))
#### Estimated changes
Modified src/topology/algebra/module.lean




## [2021-07-21 17:32:53](https://github.com/leanprover-community/mathlib/commit/ae1c7ee)
docs(analysis/normed_space/bounded_linear_map): add module docstring ([#8263](https://github.com/leanprover-community/mathlib/pull/8263))
#### Estimated changes
Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *lemma* continuous_linear_map.is_bounded_linear_map_comp_left
- \+/\- *lemma* continuous_linear_map.is_bounded_linear_map_comp_right
- \+/\- *def* is_bounded_bilinear_map.deriv



## [2021-07-21 15:58:51](https://github.com/leanprover-community/mathlib/commit/9fa82b0)
feat(combinatorics/colex): order is decidable ([#8378](https://github.com/leanprover-community/mathlib/pull/8378))
Show that the colex ordering is decidable.
#### Estimated changes
Modified src/combinatorics/colex.lean




## [2021-07-21 12:21:17](https://github.com/leanprover-community/mathlib/commit/28b8593)
feat(combinatorics/simple_graph): `boolean_algebra` for `simple_graph`s. ([#8330](https://github.com/leanprover-community/mathlib/pull/8330))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+/\- *lemma* irrefl
- \+/\- *lemma* adj_comm
- \+/\- *lemma* adj_symm
- \+/\- *lemma* ne_of_adj
- \+ *lemma* is_subgraph_eq_le
- \+ *lemma* sup_adj
- \+ *lemma* inf_adj
- \+/\- *lemma* compl_adj
- \+ *lemma* sdiff_adj
- \+ *lemma* top_adj
- \+ *lemma* bot_adj
- \+ *lemma* complete_graph_eq_top
- \+ *lemma* empty_graph_eq_bot
- \+/\- *lemma* compl_neighbor_set_disjoint
- \+/\- *lemma* neighbor_set_union_compl_neighbor_set_eq
- \- *lemma* compl_compl
- \- *lemma* compl_involutive
- \+/\- *def* complete_graph
- \+/\- *def* empty_graph
- \+ *def* is_subgraph
- \- *def* compl

Modified src/combinatorics/simple_graph/strongly_regular.lean


Modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* spanning_coe_adj_sub
- \+ *lemma* _root_.simple_graph.to_subgraph.is_spanning
- \+ *lemma* spanning_coe.is_subgraph_of_is_subgraph
- \+ *def* spanning_coe
- \+ *def* spanning_coe_equiv_coe_of_spanning
- \+/\- *def* is_subgraph
- \+ *def* _root_.simple_graph.to_subgraph
- \+/\- *def* bot_equiv



## [2021-07-21 10:58:03](https://github.com/leanprover-community/mathlib/commit/fb58e05)
refactor(measure_theory/decomposition): move `decomposition` into a folder  ([#8374](https://github.com/leanprover-community/mathlib/pull/8374))
#### Estimated changes
Renamed src/measure_theory/decomposition.lean to src/measure_theory/decomposition/unsigned_hahn.lean




## [2021-07-21 07:30:27](https://github.com/leanprover-community/mathlib/commit/b45acc9)
feat(combinatorics/colex): top of the colex ordering on finite types ([#8379](https://github.com/leanprover-community/mathlib/pull/8379))
#### Estimated changes
Modified src/combinatorics/colex.lean




## [2021-07-21 04:59:20](https://github.com/leanprover-community/mathlib/commit/02a5696)
feat(analysis/normed_space): Define conformal maps on inner product spaces; define the groupoid of conformal maps ([#8367](https://github.com/leanprover-community/mathlib/pull/8367))
#### Estimated changes
Created src/analysis/calculus/conformal.lean
- \+ *lemma* conformal_at_id
- \+ *lemma* conformal_at_const_smul
- \+ *lemma* conformal_at_iff_is_conformal_map_fderiv
- \+ *lemma* conformal_at_iff'
- \+ *lemma* conformal_at_iff
- \+ *lemma* differentiable_at
- \+ *lemma* congr
- \+ *lemma* comp
- \+ *lemma* const_smul
- \+ *lemma* conformal_factor_at_pos
- \+ *lemma* conformal_factor_at_inner_eq_mul_inner'
- \+ *lemma* conformal_factor_at_inner_eq_mul_inner
- \+ *lemma* preserves_angle
- \+ *lemma* conformal_id
- \+ *lemma* conformal_const_smul
- \+ *lemma* conformal_at
- \+ *lemma* differentiable
- \+ *def* conformal_at
- \+ *def* conformal_factor_at
- \+ *def* conformal

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at_of_subsingleton

Created src/analysis/normed_space/conformal_linear_map.lean
- \+ *lemma* is_conformal_map_id
- \+ *lemma* is_conformal_map_const_smul
- \+ *lemma* is_conformal_map_iff
- \+ *lemma* is_conformal_map_of_subsingleton
- \+ *lemma* comp
- \+ *lemma* injective
- \+ *lemma* preserves_angle
- \+ *def* is_conformal_map

Created src/geometry/manifold/conformal_groupoid.lean
- \+ *def* conformal_pregroupoid
- \+ *def* conformal_groupoid



## [2021-07-20 20:10:32](https://github.com/leanprover-community/mathlib/commit/899bb5f)
feat(data/multiset): `(s.erase x).map f = (s.map f).erase (f x)` ([#8375](https://github.com/leanprover-community/mathlib/pull/8375))
A little lemma that I needed for Dedekind domains.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* map_erase



## [2021-07-20 18:13:44](https://github.com/leanprover-community/mathlib/commit/4676b31)
feat(data/sym2): add the universal property, and make `sym2.is_diag ⟦(x, y)⟧ ↔ x = y` true definitionally ([#8358](https://github.com/leanprover-community/mathlib/pull/8358))
#### Estimated changes
Modified src/data/sym2.lean
- \+ *lemma* lift_mk
- \+ *lemma* coe_lift_symm_apply
- \+ *lemma* is_diag_iff_eq
- \+/\- *lemma* diag_is_diag
- \+ *lemma* is_diag.mem_range_diag
- \+ *lemma* is_diag_iff_mem_range_diag
- \+ *def* lift
- \+/\- *def* is_diag



## [2021-07-20 16:22:25](https://github.com/leanprover-community/mathlib/commit/6ac3059)
feat(combinatorics/colex): golf and generalise ([#8301](https://github.com/leanprover-community/mathlib/pull/8301))
Miscellaneous fixes about colex: Gives `le` versions of some `lt` lemmas, fixes a TODO, restores some names etc.
#### Estimated changes
Modified src/combinatorics/colex.lean
- \+ *lemma* nat.sum_two_pow_lt
- \+ *lemma* hom_lt_iff
- \+ *lemma* hom_fin_lt_iff
- \+ *lemma* hom_le_iff
- \+ *lemma* hom_fin_le_iff
- \+/\- *lemma* lt_singleton_iff_mem_lt
- \+/\- *lemma* mem_le_of_singleton_le
- \+/\- *lemma* singleton_lt_iff_lt
- \+ *lemma* singleton_le_iff_le
- \+ *lemma* sdiff_le_sdiff_iff_le
- \+ *lemma* empty_to_colex_lt
- \+ *lemma* colex_lt_of_ssubset
- \+ *lemma* empty_to_colex_le
- \+ *lemma* colex_le_of_subset
- \+ *lemma* sum_two_pow_lt_iff_lt
- \+ *lemma* sum_two_pow_le_iff_lt
- \- *lemma* nat.sum_sq_lt
- \- *lemma* hom
- \- *lemma* hom_fin
- \- *lemma* sum_sq_lt_iff_lt
- \+ *def* to_colex_rel_hom



## [2021-07-20 11:23:09](https://github.com/leanprover-community/mathlib/commit/ed8d597)
fix(data/matrix/basic): remove an accidental requirement for a matrix to be square ([#8372](https://github.com/leanprover-community/mathlib/pull/8372))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *theorem* mul_apply'



## [2021-07-20 10:51:34](https://github.com/leanprover-community/mathlib/commit/fce38f1)
feat(ring_theory): define `fractional_ideal.adjoin_integral` ([#8296](https://github.com/leanprover-community/mathlib/pull/8296))
This PR shows if `x` is integral over `R`, then `R[x]` is a fractional ideal, and proves some of the essential properties of this fractional ideal.
This is an important step towards showing `is_dedekind_domain_inv` implies that the ring is integrally closed.
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* is_fractional_adjoin_integral
- \+ *lemma* mem_adjoin_integral_self
- \+ *def* adjoin_integral



## [2021-07-20 09:52:16](https://github.com/leanprover-community/mathlib/commit/c05c15f)
feat(group_theory/order_of_element): pow_eq_mod_card ([#8354](https://github.com/leanprover-community/mathlib/pull/8354))
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* pow_eq_mod_card
- \+ *lemma* gpow_eq_mod_card



## [2021-07-20 08:59:36](https://github.com/leanprover-community/mathlib/commit/0f9b754)
feat(measure_theory/borel_space): generalize `monotone.measurable` to monotone on set ([#8365](https://github.com/leanprover-community/mathlib/pull/8365))
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measurable_of_monotone
- \+ *lemma* ae_measurable_restrict_of_monotone_on
- \+/\- *lemma* measurable_of_antimono
- \+ *lemma* ae_measurable_restrict_of_antimono_on



## [2021-07-20 08:59:35](https://github.com/leanprover-community/mathlib/commit/1589318)
feat(topology/continuous_function/bounded): prove `norm_eq_supr_norm` ([#8288](https://github.com/leanprover-community/mathlib/pull/8288))
More precisely we prove both:
 * `bounded_continuous_function.norm_eq_supr_norm`
 * `continuous_map.norm_eq_supr_norm`
We also introduce one new definition: `bounded_continuous_function.norm_comp`.
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* norm_eq_of_nonempty
- \+ *lemma* norm_eq_zero_of_empty
- \+ *lemma* coe_norm_comp
- \+ *lemma* norm_norm_comp
- \+ *lemma* bdd_above_range_norm_comp
- \+ *lemma* norm_eq_supr_norm
- \+ *def* norm_comp

Modified src/topology/continuous_function/compact.lean
- \+ *lemma* _root_.bounded_continuous_function.norm_forget_boundedness_eq
- \+ *lemma* norm_eq_supr_norm



## [2021-07-20 08:59:34](https://github.com/leanprover-community/mathlib/commit/f5d25b4)
feat(measure_theory/vector_measure): introduce vector-valued measures ([#8247](https://github.com/leanprover-community/mathlib/pull/8247))
This PR introduces vector-valued measures and provides a method of creating signed measures without the summability requirement.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_of_nonpos

Modified src/data/real/ennreal.lean
- \+ *lemma* coe_smul
- \+ *lemma* to_real_smul

Modified src/measure_theory/measure_space.lean
- \+ *lemma* summable_measure_to_real

Created src/measure_theory/vector_measure.lean
- \+ *lemma* measure_of_eq_coe
- \+ *lemma* empty
- \+ *lemma* not_measurable
- \+ *lemma* m_Union
- \+ *lemma* of_disjoint_Union_nat
- \+ *lemma* coe_injective
- \+ *lemma* ext_iff'
- \+ *lemma* ext_iff
- \+ *lemma* ext
- \+ *lemma* has_sum_of_disjoint_Union
- \+ *lemma* of_disjoint_Union
- \+ *lemma* of_union
- \+ *lemma* of_add_of_diff
- \+ *lemma* of_diff
- \+ *lemma* of_Union_nonneg
- \+ *lemma* of_Union_nonpos
- \+ *lemma* of_nonneg_disjoint_union_eq_zero
- \+ *lemma* of_nonpos_disjoint_union_eq_zero
- \+ *lemma* coe_zero
- \+ *lemma* zero_apply
- \+ *lemma* coe_add
- \+ *lemma* add_apply
- \+ *lemma* coe_neg
- \+ *lemma* neg_apply
- \+ *lemma* coe_sub
- \+ *lemma* sub_apply
- \+ *lemma* coe_smul
- \+ *lemma* smul_apply
- \+ *lemma* to_signed_measure_apply_measurable
- \+ *lemma* to_signed_measure_zero
- \+ *lemma* to_signed_measure_add
- \+ *lemma* to_signed_measure_smul
- \+ *lemma* to_ennreal_vector_measure_apply_measurable
- \+ *lemma* to_ennreal_vector_measure_zero
- \+ *lemma* to_ennreal_vector_measure_add
- \+ *lemma* sub_to_signed_measure_apply
- \+ *def* add
- \+ *def* coe_fn_add_monoid_hom
- \+ *def* neg
- \+ *def* sub
- \+ *def* smul
- \+ *def* to_signed_measure
- \+ *def* to_ennreal_vector_measure
- \+ *def* sub_to_signed_measure

Modified src/topology/instances/ennreal.lean
- \+ *lemma* summable_to_real

Modified src/topology/instances/nnreal.lean




## [2021-07-20 07:56:49](https://github.com/leanprover-community/mathlib/commit/0f58e13)
chore(topology/continuous_function, analysis/normed_space): use `is_empty α` instead of `¬nonempty α` ([#8352](https://github.com/leanprover-community/mathlib/pull/8352))
Two lemmas with their assumptions changed, and some proofs golfed using the new forms of these and other lemmas.
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \+/\- *lemma* norm_mk_pi_algebra_of_empty

Modified src/order/filter/at_top_bot.lean


Modified src/topology/continuous_function/bounded.lean
- \+/\- *lemma* dist_zero_of_empty



## [2021-07-20 04:14:22](https://github.com/leanprover-community/mathlib/commit/b3fbcec)
chore(.docker): add missing library ([#8370](https://github.com/leanprover-community/mathlib/pull/8370))
Something must have changed that now needs this library. It's only installed in an intemediate build, anyway.
#### Estimated changes
Modified .docker/debian/lean/Dockerfile




## [2021-07-20 03:37:36](https://github.com/leanprover-community/mathlib/commit/e0467bd)
feat(algebra.homology): homology f g w ≅ cokernel (kernel.lift g f w) ([#8355](https://github.com/leanprover-community/mathlib/pull/8355))
Per [zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Challenge.20with.20homology).
I'm not certain this completely resolves the issue: perhaps we should really change the definition of `homology`. But at least this bridges the gap.
#### Estimated changes
Modified src/algebra/homology/image_to_kernel.lean
- \+ *lemma* image_subobject_iso_image_to_kernel'
- \+ *lemma* image_to_kernel'_kernel_subobject_iso
- \+ *def* image_to_kernel'
- \+ *def* homology_iso_cokernel_image_to_kernel'
- \+ *def* homology_iso_cokernel_lift



## [2021-07-19 22:25:50](https://github.com/leanprover-community/mathlib/commit/11af02c)
feat(analysis/convex): convex sets with zero ([#8234](https://github.com/leanprover-community/mathlib/pull/8234))
Split off from [#7288](https://github.com/leanprover-community/mathlib/pull/7288)
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex.smul_mem_of_zero_mem
- \+ *lemma* convex.mem_smul_of_zero_mem



## [2021-07-19 22:25:49](https://github.com/leanprover-community/mathlib/commit/0821e6e)
feat(category_theory/limits): strict initial objects ([#8094](https://github.com/leanprover-community/mathlib/pull/8094))
- [x] depends on: [#8084](https://github.com/leanprover-community/mathlib/pull/8084)
[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/from-referrer/)
#### Estimated changes
Created src/category_theory/limits/shapes/strict_initial.lean
- \+ *lemma* is_initial.is_iso_to
- \+ *lemma* is_initial.strict_hom_ext
- \+ *lemma* is_initial.subsingleton_to
- \+ *lemma* mul_is_initial_inv
- \+ *lemma* is_initial_mul_inv
- \+ *lemma* initial.hom_ext
- \+ *lemma* initial.subsingleton_to
- \+ *lemma* mul_initial_inv
- \+ *lemma* initial_mul_inv
- \+ *lemma* has_strict_initial_objects_of_initial_is_strict



## [2021-07-19 19:25:13](https://github.com/leanprover-community/mathlib/commit/afd0f92)
feat(category_theory/limits/pullbacks): generalise pullback mono lemmas ([#8302](https://github.com/leanprover-community/mathlib/pull/8302))
Generalises results to use `is_limit` rather than the canonical limit.
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* mono_snd_of_is_pullback_of_mono
- \+ *lemma* mono_fst_of_is_pullback_of_mono
- \+ *lemma* epi_inr_of_is_pushout_of_epi
- \+ *lemma* epi_inl_of_is_pushout_of_epi



## [2021-07-19 15:59:39](https://github.com/leanprover-community/mathlib/commit/739b353)
chore(.gitignore): ignore lock files ([#8368](https://github.com/leanprover-community/mathlib/pull/8368))
Two reasons:
1. Sometimes these accidentally make it into PRs  (e.g. [#8344](https://github.com/leanprover-community/mathlib/pull/8344))
2. Some editor plugins (like the git in vscode) update very frequently causing these files to appear and disappear quickly in the sidebar whenever lean compiles which is annoying
#### Estimated changes
Modified .gitignore




## [2021-07-19 14:20:44](https://github.com/leanprover-community/mathlib/commit/ad7ab8d)
feat(linear_algebra/finsupp): `span.repr` gives an arbitrarily representation of `x : span R w` as a linear combination over `w` ([#8339](https://github.com/leanprover-community/mathlib/pull/8339))
It's convenient to be able to get hold of such a representation, even when it is not unique. We prove the only lemma about this, then mark the definition is irreducible.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *theorem* of_injective_symm_apply

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* span.finsupp_total_repr
- \+/\- *theorem* total_emb_domain
- \+ *theorem* total_equiv_map_domain
- \+ *def* span.repr

Modified src/linear_algebra/linear_independent.lean
- \+/\- *lemma* linear_independent.total_repr
- \+ *lemma* linear_independent.span_repr_eq
- \+/\- *def* linear_independent.total_equiv



## [2021-07-19 13:17:09](https://github.com/leanprover-community/mathlib/commit/02ecb62)
feat(analysis/fourier): span of monomials is dense in L^p ([#8328](https://github.com/leanprover-community/mathlib/pull/8328))
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/analysis/fourier.lean
- \+/\- *lemma* span_fourier_closure_eq_top
- \+ *lemma* span_fourier_Lp_closure_eq_top
- \+/\- *lemma* orthonormal_fourier

Modified src/measure_theory/continuous_map_dense.lean


Modified src/topology/algebra/group.lean
- \+ *lemma* subgroup.topological_closure_coe
- \+ *lemma* dense_range.topological_closure_map_subgroup

Modified src/topology/algebra/module.lean
- \+ *lemma* _root_.dense_range.topological_closure_map_submodule



## [2021-07-19 12:28:13](https://github.com/leanprover-community/mathlib/commit/5ccf2bf)
feat(topology/metric_space/basic): an order-bounded set is metric-bounded ([#8335](https://github.com/leanprover-community/mathlib/pull/8335))
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* _root_.totally_bounded.bounded
- \+ *lemma* _root_.is_compact.bounded
- \+ *lemma* bounded_Icc
- \+ *lemma* bounded_Ico
- \+ *lemma* bounded_Ioc
- \+ *lemma* bounded_Ioo
- \+ *lemma* bounded_of_bdd_above_of_bdd_below
- \- *lemma* bounded_of_compact

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean




## [2021-07-19 10:21:46](https://github.com/leanprover-community/mathlib/commit/3e67932)
feat(topology/algebra/ordered): an `order_closed_topology` restricted to a subset is an `order_closed_topology` ([#8364](https://github.com/leanprover-community/mathlib/pull/8364))
#### Estimated changes
Modified src/topology/algebra/ordered/basic.lean




## [2021-07-19 07:28:12](https://github.com/leanprover-community/mathlib/commit/dd9f1c3)
chore(order/basic): whitespaces and caps ([#8359](https://github.com/leanprover-community/mathlib/pull/8359))
#### Estimated changes
Modified src/order/basic.lean
- \+/\- *lemma* monotone_of_monotone_nat
- \+/\- *lemma* pi.le_def
- \+/\- *lemma* pi.lt_def
- \+/\- *lemma* le_update_iff
- \+/\- *lemma* update_le_iff
- \+/\- *lemma* update_le_update_iff
- \+/\- *lemma* no_top
- \+/\- *lemma* no_bot
- \+/\- *lemma* exists_between
- \+/\- *theorem* monotone_id
- \+/\- *theorem* monotone_const
- \+/\- *theorem* monotone_lam
- \+/\- *theorem* monotone_app
- \+/\- *def* order.preimage
- \+/\- *def* monotone
- \+/\- *def* order_dual



## [2021-07-19 02:21:30](https://github.com/leanprover-community/mathlib/commit/6a20dd6)
chore(scripts): update nolints.txt ([#8366](https://github.com/leanprover-community/mathlib/pull/8366))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-07-18 22:22:27](https://github.com/leanprover-community/mathlib/commit/ee60711)
feat(data/finset/basic): product, bUnion, sdiff lemmas ([#8321](https://github.com/leanprover-community/mathlib/pull/8321))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* sdiff_ssubset
- \+ *lemma* bUnion_bUnion
- \+ *lemma* bUnion_subset_iff_forall_subset
- \+ *lemma* product_bUnion

Modified src/order/boolean_algebra.lean
- \+ *lemma* sdiff_lt



## [2021-07-18 17:02:30](https://github.com/leanprover-community/mathlib/commit/c2d042c)
chore(analysis/*): remove unnecessary imports ([#8344](https://github.com/leanprover-community/mathlib/pull/8344))
#### Estimated changes
Modified src/algebra/indicator_function.lean


Modified src/analysis/ODE/gronwall.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/asymptotics/asymptotic_equivalent.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/fderiv_measurable.lean


Modified src/analysis/calculus/fderiv_symmetric.lean


Modified src/analysis/calculus/formal_multilinear_series.lean


Modified src/analysis/calculus/lagrange_multipliers.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/complex/circle.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/complex/roots_of_unity.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/caratheodory.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/convex/exposed.lean


Modified src/analysis/convex/extrema.lean


Modified src/analysis/convex/extreme.lean


Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/hofer.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/SemiNormedGroup.lean


Modified src/analysis/normed_space/add_torsor.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/hahn_banach.lean


Modified src/analysis/normed_space/inner_product.lean


Modified src/analysis/normed_space/int.lean


Modified src/analysis/normed_space/normed_group_hom.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/ordered.lean


Modified src/analysis/normed_space/units.lean


Modified src/analysis/special_functions/bernstein.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/special_functions/polynomials.lean


Modified src/analysis/special_functions/sqrt.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/analysis/specific_limits.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/data/complex/exponential.lean


Modified src/data/complex/module.lean


Modified src/measure_theory/lp_space.lean


Modified src/ring_theory/polynomial/chebyshev.lean


Modified src/topology/continuous_function/weierstrass.lean


Modified src/topology/sequences.lean




## [2021-07-18 17:02:29](https://github.com/leanprover-community/mathlib/commit/b02b919)
feat(measure_theory): add lemmas of equality of measures under assumptions of null difference, in particular null frontier ([#8332](https://github.com/leanprover-community/mathlib/pull/8332))
Adding lemmas in `measure_theory/measure_space` and `measure_theory/borel_space` about equality of measures of sets under the assumption that the difference of the largest to the smallest has null measure.
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* meas_interior_of_null_bdry
- \+ *lemma* meas_closure_of_null_bdry

Modified src/measure_theory/measure_space.lean
- \+ *lemma* meas_eq_meas_of_null_diff
- \+ *lemma* meas_eq_meas_of_between_null_diff
- \+ *lemma* meas_eq_meas_smaller_of_between_null_diff
- \+ *lemma* meas_eq_meas_larger_of_between_null_diff



## [2021-07-18 17:02:28](https://github.com/leanprover-community/mathlib/commit/048263d)
feat(topology/basic): add two lemmas about frontier and two lemmas about preimages under continuous maps ([#8329](https://github.com/leanprover-community/mathlib/pull/8329))
Adding four lemmas: `frontier_eq_inter_compl_interior`, `compl_frontier_eq_union_interior`, `continuous.closure_preimage_subset`, `continuous.frontier_preimage_subset` to `topology/basic`.
These were discussed on Zulip <https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Portmanteau.20theorem/near/246037950>. The formulations closely follow Patrick's suggestions.
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* frontier_eq_inter_compl_interior
- \+ *lemma* compl_frontier_eq_union_interior
- \+ *lemma* continuous.closure_preimage_subset
- \+ *lemma* continuous.frontier_preimage_subset



## [2021-07-18 15:12:25](https://github.com/leanprover-community/mathlib/commit/865e36b)
chore(order/boolean_algebra) : `compl_involutive` ([#8357](https://github.com/leanprover-community/mathlib/pull/8357))
#### Estimated changes
Modified src/order/boolean_algebra.lean
- \+ *theorem* compl_involutive
- \+ *theorem* compl_bijective



## [2021-07-17 21:38:09](https://github.com/leanprover-community/mathlib/commit/f45df47)
feat(measure_theory/hausdorff_measure): `dimH_{s,b,}Union`, `dimH_union` ([#8351](https://github.com/leanprover-community/mathlib/pull/8351))
#### Estimated changes
Modified src/measure_theory/hausdorff_measure.lean
- \+ *lemma* le_dimH_of_hausdorff_measure_eq_top
- \+ *lemma* dimH_mono
- \+ *lemma* dimH_Union
- \+ *lemma* dimH_bUnion
- \+ *lemma* dimH_sUnion
- \+ *lemma* dimH_union



## [2021-07-17 19:58:11](https://github.com/leanprover-community/mathlib/commit/ad5afc2)
feat(combinatorics/hales_jewett): Hales-Jewett and Van der Waerden ([#8019](https://github.com/leanprover-community/mathlib/pull/8019))
Proves the Hales-Jewett theorem (a fundamental result in Ramsey theory on combinatorial lines) and deduces (a generalised version of) Van der Waerden's theorem on arithmetic progressions.
#### Estimated changes
Created src/combinatorics/hales_jewett.lean
- \+ *lemma* apply
- \+ *lemma* apply_none
- \+ *lemma* apply_of_ne_none
- \+ *lemma* map_apply
- \+ *lemma* vertical_apply
- \+ *lemma* horizontal_apply
- \+ *lemma* prod_apply
- \+ *lemma* diagonal_apply
- \+ *theorem* exists_mono_in_high_dimension
- \+ *theorem* exists_mono_homothetic_copy
- \+ *def* is_mono
- \+ *def* diagonal
- \+ *def* map
- \+ *def* vertical
- \+ *def* horizontal
- \+ *def* prod

Modified src/data/list/basic.lean


Modified src/data/option/basic.lean
- \+ *lemma* get_or_else_none
- \+ *lemma* get_or_else_map



## [2021-07-17 17:47:12](https://github.com/leanprover-community/mathlib/commit/398027d)
feat(topology/subset_properties): add `countable_cover_nhds_within_of_sigma_compact` ([#8350](https://github.com/leanprover-community/mathlib/pull/8350))
This is a version of `countable_cover_nhds_of_sigma_compact` for a
covering of a closed set instead of the whole space.
#### Estimated changes
Modified src/topology/subset_properties.lean
- \+ *lemma* exists_mem_compact_covering
- \+ *lemma* countable_cover_nhds_within_of_sigma_compact



## [2021-07-17 17:47:11](https://github.com/leanprover-community/mathlib/commit/7d754e0)
chore(analysis/calculus/mean_value): use `nnnorm` in a few lemmas ([#8348](https://github.com/leanprover-community/mathlib/pull/8348))
Use `nnnorm` instead of `norm` and `C : nnreal` in lemmas about `lipschitz_on_with`. This way we can use them to prove any statement of the form `lipschitz_on_with C f s`, not only something of the form `lipschitz_on_with (real.to_nnreal C) f s`.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean
- \+ *lemma* convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_continuous_within_at
- \+ *theorem* convex.lipschitz_on_with_of_nnnorm_has_fderiv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_nnnorm_fderiv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_nnnorm_fderiv_le
- \+ *theorem* convex.lipschitz_on_with_of_nnnorm_has_deriv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_nnnorm_deriv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_nnnorm_deriv_le
- \- *theorem* convex.lipschitz_on_with_of_norm_has_fderiv_within_le
- \- *theorem* convex.lipschitz_on_with_of_norm_fderiv_within_le
- \- *theorem* convex.lipschitz_on_with_of_norm_fderiv_le
- \- *theorem* convex.lipschitz_on_with_of_norm_has_deriv_within_le
- \- *theorem* convex.lipschitz_on_with_of_norm_deriv_within_le
- \- *theorem* convex.lipschitz_on_with_of_norm_deriv_le

Modified src/analysis/calculus/parametric_integral.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* nnnorm_smul_right_apply

Modified src/data/real/nnreal.lean




## [2021-07-17 16:55:13](https://github.com/leanprover-community/mathlib/commit/3782c19)
feat(topology/algebra/ordered): add `nhds_top_basis_Ici` and `nhds_bot_basis_Iic` ([#8349](https://github.com/leanprover-community/mathlib/pull/8349))
Also add `ennreal.nhds_zero_basis_Iic` and `ennreal.supr_div`.
#### Estimated changes
Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* nhds_top_basis_Ici
- \+ *lemma* nhds_bot_basis_Iic

Modified src/topology/instances/ennreal.lean
- \+ *lemma* nhds_zero_basis_Iic
- \+ *lemma* supr_div



## [2021-07-17 16:20:16](https://github.com/leanprover-community/mathlib/commit/8139d7e)
feat(measure_theory/hausdorff_measure): μH and dimH of a `subsingleton` ([#8347](https://github.com/leanprover-community/mathlib/pull/8347))
#### Estimated changes
Modified src/measure_theory/hausdorff_measure.lean
- \+ *lemma* dimH_subsingleton
- \+ *lemma* dimH_empty
- \+ *lemma* dimH_singleton

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_subsingleton



## [2021-07-17 14:00:00](https://github.com/leanprover-community/mathlib/commit/fcde3f0)
chore(data/real/ennreal): move `x ≠ 0` case of `mul_infi` to `mul_infi_of_ne` ([#8345](https://github.com/leanprover-community/mathlib/pull/8345))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* infi_mul_of_ne
- \+ *lemma* mul_infi_of_ne



## [2021-07-17 13:14:10](https://github.com/leanprover-community/mathlib/commit/bd56531)
chore(analysis/normed_space/operator_norm): use `norm_one_class` ([#8346](https://github.com/leanprover-community/mathlib/pull/8346))
* turn `continuous_linear_map.norm_id` into a `simp` lemma;
* drop its particular case `continuous_linear_map.norm_id_field`;
* replace `continuous_linear_map.norm_id_field'` with a
  `norm_one_class` instance.
#### Estimated changes
Modified src/analysis/calculus/parametric_integral.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* norm_id_of_nontrivial_seminorm
- \+/\- *lemma* norm_id
- \- *lemma* norm_id_field
- \- *lemma* norm_id_field'



## [2021-07-17 11:26:47](https://github.com/leanprover-community/mathlib/commit/93a3764)
chore(algebra/ring/basic): drop commutativity assumptions from some division lemmas ([#8334](https://github.com/leanprover-community/mathlib/pull/8334))
* Removes `dvd_neg_iff_dvd`, `neg_dvd_iff_dvd` which duplicated `dvd_neg`, `neg_dvd`.
* Generalizes `two_dvd_bit0` to non-commutative semirings.
* Generalizes a bunch of lemmas from `comm_ring` to `ring`.
* Adds `even_neg` for `ring` to replace `int.even_neg`.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+/\- *lemma* dvd_neg
- \+/\- *lemma* neg_dvd
- \+/\- *lemma* dvd_iff_dvd_of_dvd_sub
- \+/\- *lemma* mul_self_sub_one
- \+/\- *theorem* two_dvd_bit0
- \+ *theorem* even_neg
- \+/\- *theorem* mul_self_sub_mul_self
- \- *theorem* dvd_neg_iff_dvd
- \- *theorem* neg_dvd_iff_dvd

Modified src/data/int/basic.lean


Modified src/data/int/parity.lean
- \- *theorem* even_neg



## [2021-07-17 09:38:56](https://github.com/leanprover-community/mathlib/commit/d4c0a11)
refactor(analysis/analytic/basic): refactor `change_origin` ([#8282](https://github.com/leanprover-community/mathlib/pull/8282))
Now each term of `change_origin` is defined as a sum of a formal power series, so it is clear that each term is an analytic function.
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+/\- *lemma* le_radius_of_bound
- \+/\- *lemma* le_radius_of_bound_nnreal
- \+ *lemma* le_radius_of_eventually_le
- \+ *lemma* le_radius_of_summable_nnnorm
- \+ *lemma* le_radius_of_summable
- \+ *lemma* formal_multilinear_series.summable_norm_mul_pow
- \+ *lemma* formal_multilinear_series.summable_nnnorm_mul_pow
- \+ *lemma* change_origin_series_term_apply
- \+ *lemma* norm_change_origin_series_term
- \+ *lemma* nnnorm_change_origin_series_term
- \+ *lemma* nnnorm_change_origin_series_term_apply_le
- \+ *lemma* nnnorm_change_origin_series_le_tsum
- \+ *lemma* nnnorm_change_origin_series_apply_le_tsum
- \+ *lemma* change_origin_series_summable_aux₁
- \+ *lemma* change_origin_series_summable_aux₂
- \+ *lemma* change_origin_series_summable_aux₃
- \+ *lemma* le_change_origin_series_radius
- \+ *lemma* nnnorm_change_origin_le
- \+/\- *lemma* change_origin_radius
- \+ *lemma* has_fpower_series_on_ball_change_origin
- \- *lemma* formal_multilinear_series.has_fpower_series_on_ball
- \- *lemma* formal_multilinear_series.continuous_on
- \- *lemma* change_origin_summable_aux1
- \- *lemma* change_origin_summable_aux2
- \- *lemma* change_origin_summable_aux_j_injective
- \- *lemma* change_origin_summable_aux3
- \- *lemma* change_origin_has_sum
- \+/\- *theorem* change_origin_eval
- \+ *def* change_origin_series_term
- \+ *def* change_origin_series
- \+ *def* change_origin_index_equiv
- \- *def* change_origin_summable_aux_j

Modified src/data/real/ennreal.lean
- \+ *lemma* le_of_forall_pos_nnreal_lt

Modified src/data/subtype.lean
- \+ *lemma* heq_iff_coe_heq

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* summable.div_const



## [2021-07-17 04:19:35](https://github.com/leanprover-community/mathlib/commit/0cb634f)
feat(category_theory/subobject): subobject category equivalent to mono over category ([#8304](https://github.com/leanprover-community/mathlib/pull/8304))
#### Estimated changes
Modified src/category_theory/essentially_small.lean


Modified src/category_theory/monoidal/skeleton.lean


Modified src/category_theory/skeletal.lean


Modified src/category_theory/subobject/basic.lean


Modified src/category_theory/subobject/mono_over.lean




## [2021-07-17 02:01:37](https://github.com/leanprover-community/mathlib/commit/e67e50f)
feat(algebra/group_theory/lemmas): add int.pow_right_injective ([#8278](https://github.com/leanprover-community/mathlib/pull/8278))
Suggested here: https://github.com/leanprover-community/mathlib/pull/7843#discussion_r668167163
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* pow_right_injective



## [2021-07-16 22:47:45](https://github.com/leanprover-community/mathlib/commit/10975e6)
docs(measure_theory/integral_eq_improper): fix lemma names in docs ([#8333](https://github.com/leanprover-community/mathlib/pull/8333))
#### Estimated changes
Modified src/measure_theory/integral_eq_improper.lean




## [2021-07-16 17:58:03](https://github.com/leanprover-community/mathlib/commit/8e3d9ce)
feat(measure_theory/continuous_map_dense): continuous functions are dense in Lp ([#8306](https://github.com/leanprover-community/mathlib/pull/8306))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup_of_range_eq_of_le

Created src/measure_theory/continuous_map_dense.lean
- \+ *lemma* bounded_continuous_function_dense
- \+ *lemma* to_Lp_dense_range

Modified src/measure_theory/lp_space.lean
- \+ *lemma* measure_theory.Lp.mem_bounded_continuous_function_iff
- \+ *lemma* range_to_Lp_hom
- \+ *lemma* range_to_Lp
- \+ *def* measure_theory.Lp.bounded_continuous_function

Modified src/measure_theory/vitali_caratheodory.lean


Modified src/topology/algebra/group.lean
- \+/\- *lemma* subgroup.subgroup_topological_closure
- \+/\- *lemma* subgroup.is_closed_topological_closure
- \+/\- *lemma* subgroup.topological_closure_minimal



## [2021-07-16 17:58:00](https://github.com/leanprover-community/mathlib/commit/a895300)
chore(ring_theory/fractional_ideal): prefer `(⊤ : ideal R)` over `1` ([#8298](https://github.com/leanprover-community/mathlib/pull/8298))
`fractional_ideal.lean` sometimes used `1` to denote the ideal of `R` containing each element of `R`. This PR should replace all remaining usages with `⊤ : ideal R`, following the convention in the rest of mathlib.
Also a little `simp` lemma `coe_ideal_top` which was the motivation, since the proof should have been, and is now `by refl`.
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* coe_ideal_top
- \+ *lemma* coe_one_eq_coe_submodule_top
- \- *lemma* coe_one_eq_coe_submodule_one



## [2021-07-16 17:03:24](https://github.com/leanprover-community/mathlib/commit/42f7ca0)
chore(linear_algebra/linear_independent): use `is_empty ι` instead of `¬nonempty ι` ([#8331](https://github.com/leanprover-community/mathlib/pull/8331))
#### Estimated changes
Modified src/field_theory/fixed.lean


Modified src/linear_algebra/linear_independent.lean
- \+/\- *lemma* linear_independent_empty_type

Modified src/ring_theory/polynomial/bernstein.lean




## [2021-07-16 16:03:11](https://github.com/leanprover-community/mathlib/commit/9061ecc)
feat(topology/metric_space/holder): define Hölder continuity ([#8309](https://github.com/leanprover-community/mathlib/pull/8309))
Add definitions and some basic facts about Hölder continuous functions.
#### Estimated changes
Created src/topology/metric_space/holder.lean
- \+ *lemma* holder_with_one
- \+ *lemma* holder_with_id
- \+ *lemma* edist_le
- \+ *lemma* edist_le_of_le
- \+ *lemma* comp
- \+ *lemma* ediam_image_le
- \+ *lemma* nndist_le_of_le
- \+ *lemma* nndist_le
- \+ *lemma* dist_le_of_le
- \+ *lemma* dist_le
- \+ *def* holder_with



## [2021-07-16 15:14:22](https://github.com/leanprover-community/mathlib/commit/35a8d93)
chore(topology/algebra/infinite_sum): relax the requirements on `has_sum.smul` ([#8312](https://github.com/leanprover-community/mathlib/pull/8312))
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean




## [2021-07-16 13:09:51](https://github.com/leanprover-community/mathlib/commit/162221f)
chore(set_theory/*): use `is_empty α` instead of `¬nonempty α` ([#8276](https://github.com/leanprover-community/mathlib/pull/8276))
Split from [#7826](https://github.com/leanprover-community/mathlib/pull/7826)
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+/\- *theorem* sup_eq_zero

Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* type_eq_zero_of_empty
- \+ *theorem* type_eq_zero_iff_is_empty
- \- *theorem* type_eq_zero_iff_empty



## [2021-07-16 11:35:29](https://github.com/leanprover-community/mathlib/commit/9a801ef)
docs(order/rel_iso): add module docstring ([#8249](https://github.com/leanprover-community/mathlib/pull/8249))
#### Estimated changes
Modified src/order/rel_iso.lean
- \+/\- *theorem* apply_symm_apply



## [2021-07-16 09:16:30](https://github.com/leanprover-community/mathlib/commit/e35d976)
chore(algebra/quaternion): add `smul_mk` ([#8126](https://github.com/leanprover-community/mathlib/pull/8126))
This follows the pattern set by `mk_mul_mk` and `mk_add_mk`.
#### Estimated changes
Modified src/algebra/quaternion.lean
- \+ *lemma* smul_mk



## [2021-07-16 09:16:29](https://github.com/leanprover-community/mathlib/commit/610fab7)
feat(set_theory/cofinality): more infinite pigeonhole principles ([#7879](https://github.com/leanprover-community/mathlib/pull/7879))
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* union_finset_finite_of_range_finite

Modified src/set_theory/cofinality.lean
- \+ *lemma* le_range_of_union_finset_eq_top
- \+ *theorem* infinite_pigeonhole_card_lt
- \+ *theorem* exists_infinite_fiber



## [2021-07-16 07:34:18](https://github.com/leanprover-community/mathlib/commit/e6ff367)
feat(logic/embedding): simp lemma for injectivity for embeddings ([#7881](https://github.com/leanprover-community/mathlib/pull/7881))
#### Estimated changes
Modified src/logic/embedding.lean
- \+ *lemma* apply_eq_iff_eq



## [2021-07-16 05:22:17](https://github.com/leanprover-community/mathlib/commit/728eefe)
docs(data/fintype/basic): add module docstring ([#8081](https://github.com/leanprover-community/mathlib/pull/8081))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+/\- *lemma* piecewise_univ
- \+/\- *lemma* exists_max
- \+/\- *lemma* mem_pi_finset
- \+/\- *lemma* pi_finset_subset
- \+/\- *lemma* mem_perms_of_list_of_mem
- \+/\- *theorem* subtype_card
- \+/\- *theorem* card_of_subtype
- \+/\- *def* of_multiset
- \+/\- *def* of_list
- \+/\- *def* pi_finset



## [2021-07-16 00:27:05](https://github.com/leanprover-community/mathlib/commit/4ae9792)
chore(data/matrix/basic): add lemmas about dot_product and mul_vec ([#8325](https://github.com/leanprover-community/mathlib/pull/8325))
This renames:
* `mul_vec_one` to `one_mul_vec`
* `mul_vec_zero` to `zero_mul_vec`
and adds the new lemmas:
* `sub_mul_vec`
* `mul_vec_sub`
* `zero_mul_vec`
* `mul_vec_zero`
* `sub_dot_product`
* `dot_product_sub`
Some existing lemmas have had their variables extracted to sections.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* dot_product_zero
- \+/\- *lemma* dot_product_zero'
- \+/\- *lemma* zero_dot_product
- \+/\- *lemma* zero_dot_product'
- \+/\- *lemma* add_dot_product
- \+/\- *lemma* dot_product_add
- \+/\- *lemma* diagonal_dot_product
- \+/\- *lemma* dot_product_diagonal
- \+/\- *lemma* dot_product_diagonal'
- \+/\- *lemma* neg_dot_product
- \+/\- *lemma* dot_product_neg
- \+ *lemma* sub_dot_product
- \+ *lemma* dot_product_sub
- \+/\- *lemma* smul_dot_product
- \+/\- *lemma* dot_product_smul
- \+/\- *lemma* star_dot_product_star
- \+/\- *lemma* star_dot_product
- \+/\- *lemma* dot_product_star
- \+ *lemma* zero_vec_mul
- \+ *lemma* zero_mul_vec
- \+/\- *lemma* vec_mul_zero
- \+ *lemma* one_mul_vec
- \- *lemma* mul_vec_one

Modified src/linear_algebra/matrix/nonsingular_inverse.lean




## [2021-07-15 21:23:27](https://github.com/leanprover-community/mathlib/commit/b577bb2)
feat(measure_theory/conditional_expectation): define condexp_L2, conditional expectation of L2 functions ([#8324](https://github.com/leanprover-community/mathlib/pull/8324))
#### Estimated changes
Modified src/measure_theory/conditional_expectation.lean
- \+ *lemma* mem_Lp_meas_indicator_const_Lp
- \+ *lemma* integrable_on_condexp_L2_of_measure_ne_top
- \+ *lemma* integrable_condexp_L2_of_finite_measure
- \+ *lemma* norm_condexp_L2_le_one
- \+ *lemma* norm_condexp_L2_le
- \+ *lemma* snorm_condexp_L2_le
- \+ *lemma* norm_condexp_L2_coe_le
- \+ *lemma* inner_condexp_L2_left_eq_right
- \+ *lemma* condexp_L2_indicator_of_measurable
- \+ *lemma* inner_condexp_L2_eq_inner_fun
- \+ *def* condexp_L2



## [2021-07-15 17:38:21](https://github.com/leanprover-community/mathlib/commit/79fbd46)
feat(ring_theory/ideal): generalize two results from finset to multiset ([#8320](https://github.com/leanprover-community/mathlib/pull/8320))
Nothing exciting going on here, just copied two proofs, replaced all `finset.insert` with `multiset.cons` and `finset.prod` with `(multiset.map _).prod`, and used those to show the original results.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *theorem* multiset_prod_le_inf
- \+/\- *theorem* prod_le_inf
- \+ *theorem* is_prime.multiset_prod_le
- \+ *theorem* is_prime.multiset_prod_map_le
- \+/\- *theorem* is_prime.prod_le



## [2021-07-15 16:32:09](https://github.com/leanprover-community/mathlib/commit/a783a47)
feat(data/matrix/{basic, block}): missing lemmas on conj_transpose ([#8303](https://github.com/leanprover-community/mathlib/pull/8303))
This also moves some imports around to make the star operator on vectors available in matrix/basic.lean
This is a follow up to [#8291](https://github.com/leanprover-community/mathlib/pull/8291)
#### Estimated changes
Modified src/algebra/star/algebra.lean


Modified src/algebra/star/pi.lean


Modified src/data/matrix/basic.lean
- \+ *lemma* star_dot_product_star
- \+ *lemma* star_dot_product
- \+ *lemma* dot_product_star
- \+/\- *lemma* transpose_col
- \+/\- *lemma* transpose_row
- \+ *lemma* conj_transpose_col
- \+ *lemma* conj_transpose_row
- \+ *lemma* map_update_row
- \+ *lemma* map_update_column
- \+ *lemma* update_row_conj_transpose
- \+ *lemma* update_column_conj_transpose

Modified src/data/matrix/block.lean
- \+ *lemma* from_blocks_map
- \+ *lemma* from_blocks_conj_transpose
- \+ *lemma* block_diagonal_map
- \+ *lemma* block_diagonal_conj_transpose
- \+ *lemma* block_diagonal'_map
- \+ *lemma* block_diagonal'_conj_transpose



## [2021-07-15 16:32:08](https://github.com/leanprover-community/mathlib/commit/66055dd)
feat(algebra/lie/cartan_matrix): define the exceptional Lie algebras ([#8299](https://github.com/leanprover-community/mathlib/pull/8299))
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/lie/cartan_matrix.lean
- \+ *def* E₆
- \+ *def* E₇
- \+ *def* E₈
- \+ *def* F₄
- \+ *def* G₂



## [2021-07-15 15:05:29](https://github.com/leanprover-community/mathlib/commit/bc1f145)
feat(data/multiset): `<` on multisets is well-founded ([#8319](https://github.com/leanprover-community/mathlib/pull/8319))
This is vaguely related to [#5783](https://github.com/leanprover-community/mathlib/pull/5783), in that it tries to solve a similar goal of finding a minimal multiset with some property.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* well_founded_lt



## [2021-07-15 13:15:59](https://github.com/leanprover-community/mathlib/commit/0597b1d)
feat(analysis/normed_space/normed_group_hom): add equalizer ([#8228](https://github.com/leanprover-community/mathlib/pull/8228))
From LTE.
We add equalizer of `normed_group_homs`.
#### Estimated changes
Modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* comp_ι_eq
- \+ *lemma* ι_comp_lift
- \+ *lemma* ι_comp_map
- \+ *lemma* map_id
- \+ *lemma* comm_sq₂
- \+ *lemma* map_comp_map
- \+ *lemma* ι_norm_noninc
- \+ *lemma* lift_norm_noninc
- \+ *lemma* norm_lift_le
- \+ *lemma* map_norm_noninc
- \+ *lemma* norm_map_le
- \+ *def* equalizer
- \+ *def* ι
- \+ *def* lift
- \+ *def* lift_equiv
- \+ *def* map



## [2021-07-15 09:20:51](https://github.com/leanprover-community/mathlib/commit/7e5be02)
chore(algebra/*): make non-instance typeclasses reducible. ([#8322](https://github.com/leanprover-community/mathlib/pull/8322))
A follow up to [#7835](https://github.com/leanprover-community/mathlib/pull/7835)
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/module/basic.lean
- \+/\- *def* module.comp_hom

Modified src/group_theory/group_action/defs.lean
- \+/\- *def* comp_hom
- \+/\- *def* distrib_mul_action.comp_hom



## [2021-07-15 05:43:19](https://github.com/leanprover-community/mathlib/commit/e42af8d)
refactor(topology/category/Profinite): define Profinite as a subcategory of CompHaus ([#8314](https://github.com/leanprover-community/mathlib/pull/8314))
This adjusts the definition of Profinite to explicitly be a subcategory of CompHaus rather than a subcategory of Top which embeds into CompHaus. Essentially this means it's easier to construct an element of Profinite from an element of CompHaus.
#### Estimated changes
Modified src/topology/category/Profinite/cofiltered_limit.lean


Modified src/topology/category/Profinite/default.lean
- \+ *lemma* coe_to_CompHaus
- \- *lemma* coe_to_Top
- \+ *def* Profinite_to_CompHaus
- \+ *def* Profinite.to_Top
- \+/\- *def* to_Profinite_adj_to_CompHaus
- \- *def* Profinite_to_Top
- \- *def* Profinite.to_CompHaus



## [2021-07-14 22:10:52](https://github.com/leanprover-community/mathlib/commit/e343609)
feat(measure_theory/simple_func_dense): induction lemmas for Lp.simple_func and Lp ([#8300](https://github.com/leanprover-community/mathlib/pull/8300))
The new lemmas, `Lp.simple_func.induction`, `Lp.induction`, allow one to prove a predicate for all elements of `Lp.simple_func` / `Lp` (here p < ∞), by proving it for characteristic functions and then checking it behaves appropriately under addition, and, in the second case, taking limits.  They are modelled on existing lemmas such as `simple_func.induction`, `mem_ℒp.induction`, `integrable.induction`.
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* mul_indicator_empty'

Modified src/algebra/support.lean
- \+ *lemma* mul_support_const

Modified src/measure_theory/integration.lean
- \+ *lemma* support_indicator

Modified src/measure_theory/lp_space.lean
- \+ *lemma* indicator_const_empty

Modified src/measure_theory/simple_func_dense.lean
- \+ *lemma* measure_lt_top_of_mem_ℒp_indicator
- \+ *lemma* coe_indicator_const
- \+ *lemma* to_simple_func_indicator_const
- \+ *lemma* Lp.induction
- \+ *def* indicator_const



## [2021-07-14 18:22:17](https://github.com/leanprover-community/mathlib/commit/19a156a)
refactor(algebra/ordered_ring): use `mul_le_mul'` for `canonically_ordered_comm_semiring` ([#8284](https://github.com/leanprover-community/mathlib/pull/8284))
* use `canonically_ordered_comm_semiring`, not `canonically_ordered_semiring` as a namespace;
* add an instance `canonically_ordered_comm_semiring.to_covariant_mul_le`;
* drop `canonically_ordered_semiring.mul_le_mul` etc in favor of `mul_le_mul'` etc.
#### Estimated changes
Modified src/algebra/big_operators/order.lean


Modified src/algebra/group_power/order.lean


Modified src/algebra/ordered_ring.lean
- \- *lemma* mul_le_mul
- \- *lemma* mul_le_mul_left'
- \- *lemma* mul_le_mul_right'

Modified src/algebra/squarefree.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/specific_limits.lean


Modified src/data/nat/pow.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean


Modified src/measure_theory/integration.lean


Modified src/ring_theory/perfection.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/cofinality.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/lipschitz.lean




## [2021-07-14 17:41:56](https://github.com/leanprover-community/mathlib/commit/e9b1fbd)
feat(combinatorics/simple_graph): add maps and subgraphs ([#8223](https://github.com/leanprover-community/mathlib/pull/8223))
Add graph homomorphisms, isomorphisms, and embeddings.  Define subgraphs and supporting lemmas and definitions.  Also renamed `edge_symm` to `adj_comm`.
#### Estimated changes
Modified src/combinatorics/simple_graph/adj_matrix.lean


Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* adj_comm
- \+ *lemma* adj_symm
- \+ *lemma* map_adj
- \+ *lemma* map_mem_edge_set
- \+ *lemma* apply_mem_neighbor_set
- \+ *lemma* map_edge_set.injective
- \+ *lemma* coe_comp
- \+ *lemma* map_adj_iff
- \+ *lemma* map_mem_edge_set_iff
- \+ *lemma* apply_mem_neighbor_set_iff
- \+ *lemma* card_eq_of_iso
- \- *lemma* edge_symm
- \- *lemma* edge_symm'
- \+ *def* empty_graph
- \+ *def* map_edge_set
- \+ *def* map_neighbor_set

Created src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* adj_comm
- \+ *lemma* adj_symm
- \+ *lemma* coe_adj_sub
- \+ *lemma* neighbor_set_subset
- \+ *lemma* mem_neighbor_set
- \+ *lemma* edge_set_subset
- \+ *lemma* mem_edge_set
- \+ *lemma* mem_verts_if_mem_edge
- \+ *lemma* incidence_set_subset_incidence_set
- \+ *lemma* incidence_set_subset
- \+ *lemma* copy_eq
- \+ *lemma* map.injective
- \+ *lemma* map_top.injective
- \+ *lemma* map_top_to_fun
- \+ *lemma* neighbor_set_subset_of_subgraph
- \+ *lemma* degree_le
- \+ *lemma* degree_le'
- \+ *lemma* coe_degree
- \+ *def* coe
- \+ *def* is_spanning
- \+ *def* is_induced
- \+ *def* neighbor_set
- \+ *def* coe_neighbor_set_equiv
- \+ *def* edge_set
- \+ *def* incidence_set
- \+ *def* vert
- \+ *def* copy
- \+ *def* union
- \+ *def* inter
- \+ *def* top
- \+ *def* bot
- \+ *def* is_subgraph
- \+ *def* top_equiv
- \+ *def* bot_equiv
- \+ *def* map
- \+ *def* map_top
- \+ *def* finite_at_of_subgraph
- \+ *def* degree

Modified src/data/sym2.lean
- \+/\- *lemma* eq_iff
- \+ *lemma* map_map
- \+/\- *lemma* map_pair_eq
- \+ *lemma* map.injective



## [2021-07-14 15:21:29](https://github.com/leanprover-community/mathlib/commit/bcc35c7)
feat(group_theory/submonoid/operations): `add_equiv.of_left_inverse` to match `linear_equiv.of_left_inverse` ([#8279](https://github.com/leanprover-community/mathlib/pull/8279))
#### Estimated changes
Modified src/group_theory/submonoid/operations.lean
- \+ *def* of_left_inverse'



## [2021-07-14 13:57:59](https://github.com/leanprover-community/mathlib/commit/375dd53)
refactor(geometry/manifold): split `bump_function` into 3 files ([#8313](https://github.com/leanprover-community/mathlib/pull/8313))
This is the a part of [#8309](https://github.com/leanprover-community/mathlib/pull/8309). Both code and comments were moved with
almost no modifications: added/removed `variables`/`section`s,
slightly adjusted comments to glue them together.
#### Estimated changes
Modified src/geometry/manifold/bump_function.lean
- \- *lemma* coe_mk
- \- *lemma* exists_is_subordinate
- \- *lemma* mem_chart_at_source_of_eq_one
- \- *lemma* mem_ext_chart_at_source_of_eq_one
- \- *lemma* eventually_eq_one
- \- *lemma* apply_ind
- \- *lemma* mem_support_ind
- \- *lemma* mem_chart_at_ind_source
- \- *lemma* mem_ext_chart_at_ind_source
- \- *lemma* embedding_pi_tangent_inj_on
- \- *lemma* embedding_pi_tangent_injective
- \- *lemma* comp_embedding_pi_tangent_mfderiv
- \- *lemma* embedding_pi_tangent_ker_mfderiv
- \- *lemma* embedding_pi_tangent_injective_mfderiv
- \- *lemma* exists_immersion_finrank
- \- *lemma* exists_embedding_finrank_of_compact
- \- *def* is_subordinate
- \- *def* choice_set
- \- *def* choice
- \- *def* ind
- \- *def* embedding_pi_tangent

Created src/geometry/manifold/partition_of_unity.lean
- \+ *lemma* coe_mk
- \+ *lemma* exists_is_subordinate
- \+ *lemma* mem_chart_at_source_of_eq_one
- \+ *lemma* mem_ext_chart_at_source_of_eq_one
- \+ *lemma* eventually_eq_one
- \+ *lemma* apply_ind
- \+ *lemma* mem_support_ind
- \+ *lemma* mem_chart_at_ind_source
- \+ *lemma* mem_ext_chart_at_ind_source
- \+ *def* is_subordinate
- \+ *def* choice_set
- \+ *def* choice
- \+ *def* ind

Created src/geometry/manifold/whitney_embedding.lean
- \+ *lemma* embedding_pi_tangent_inj_on
- \+ *lemma* embedding_pi_tangent_injective
- \+ *lemma* comp_embedding_pi_tangent_mfderiv
- \+ *lemma* embedding_pi_tangent_ker_mfderiv
- \+ *lemma* embedding_pi_tangent_injective_mfderiv
- \+ *lemma* exists_immersion_finrank
- \+ *lemma* exists_embedding_finrank_of_compact
- \+ *def* embedding_pi_tangent



## [2021-07-14 13:57:58](https://github.com/leanprover-community/mathlib/commit/5bac21a)
chore(algebra/module/pi): add `pi.smul_def` ([#8311](https://github.com/leanprover-community/mathlib/pull/8311))
Sometimes it is useful to rewrite unapplied `s • x` (I need it in a branch that is not yet ready for review).
We already have `pi.zero_def`, `pi.add_def`, etc.
#### Estimated changes
Modified src/algebra/module/pi.lean
- \+ *lemma* smul_def



## [2021-07-14 13:57:57](https://github.com/leanprover-community/mathlib/commit/7fccf40)
feat(algebraic_topology/topological_simplex): This defines the natural functor from Top to sSet. ([#8305](https://github.com/leanprover-community/mathlib/pull/8305))
This PR also provides the geometric realization functor and the associated adjunction.
#### Estimated changes
Modified src/algebraic_topology/simplicial_set.lean


Created src/algebraic_topology/topological_simplex.lean
- \+ *lemma* to_Top_obj.ext
- \+ *lemma* coe_to_Top_map
- \+ *lemma* continuous_to_Top_map
- \+ *def* to_Top_obj
- \+ *def* to_Top_map
- \+ *def* to_Top



## [2021-07-14 13:57:56](https://github.com/leanprover-community/mathlib/commit/7d53431)
feat(measure_theory/integration): if a function has bounded integral on all sets of finite measure, then it is integrable ([#8297](https://github.com/leanprover-community/mathlib/pull/8297))
If the measure is sigma-finite and a function has integral bounded by some C for all measurable sets with finite measure, then its integral over the whole space is bounded by that same C. This can be used to show that a function is integrable.
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *lemma* univ_le_of_forall_fin_meas_le
- \+ *lemma* lintegral_le_of_forall_fin_meas_le_of_measurable
- \+ *lemma* lintegral_le_of_forall_fin_meas_le'
- \+ *lemma* lintegral_le_of_forall_fin_meas_le

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable_of_forall_fin_meas_le'
- \+ *lemma* integrable_of_forall_fin_meas_le

Modified src/measure_theory/measurable_space_def.lean




## [2021-07-14 12:56:52](https://github.com/leanprover-community/mathlib/commit/3b7e7bd)
feat(normed_space): controlled_sum_of_mem_closure ([#8310](https://github.com/leanprover-community/mathlib/pull/8310))
From LTE
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* controlled_sum_of_mem_closure
- \+ *lemma* controlled_sum_of_mem_closure_range

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* _root_.strict_mono.tendsto_at_top
- \- *lemma* strict_mono_tendsto_at_top



## [2021-07-14 11:55:45](https://github.com/leanprover-community/mathlib/commit/2e9aa83)
chore(analysis/special_functions/pow): golf a few proofs ([#8308](https://github.com/leanprover-community/mathlib/pull/8308))
* add `ennreal.zero_rpow_mul_self` and `ennreal.mul_rpow_eq_ite`;
* use the latter lemma to golf other proofs about `(x * y) ^ z`;
* drop unneeded argument in `ennreal.inv_rpow_of_pos`, rename it to
  `ennreal.inv_rpow`;
* add `ennreal.strict_mono_rpow_of_pos` and
  `ennreal.monotone_rpow_of_nonneg`, use themm to golf some proofs.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* zero_rpow_mul_self
- \+ *lemma* mul_rpow_eq_ite
- \+/\- *lemma* coe_mul_rpow
- \+ *lemma* inv_rpow
- \+ *lemma* strict_mono_rpow_of_pos
- \+ *lemma* monotone_rpow_of_nonneg
- \- *lemma* inv_rpow_of_pos

Modified src/data/real/ennreal.lean
- \+ *lemma* eq_inv_of_mul_eq_one

Modified src/measure_theory/mean_inequalities.lean




## [2021-07-14 10:14:23](https://github.com/leanprover-community/mathlib/commit/743209c)
chore(algebra/big_operators/basic): spaces around binders ([#8307](https://github.com/leanprover-community/mathlib/pull/8307))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* prod_congr
- \+/\- *lemma* prod_eq_one
- \+/\- *lemma* exists_ne_one_of_prod_ne_one
- \+/\- *lemma* sum_const_nat
- \+/\- *lemma* prod_eq_zero_iff



## [2021-07-14 10:14:22](https://github.com/leanprover-community/mathlib/commit/e6731de)
feat(algebra/pointwise): `smul_comm_class` instances for `set` ([#8292](https://github.com/leanprover-community/mathlib/pull/8292))
I'm not very familiar with `smul_comm_class`, so these instances might need to be tweaked slightly.
#### Estimated changes
Modified src/algebra/pointwise.lean




## [2021-07-14 10:14:21](https://github.com/leanprover-community/mathlib/commit/656722c)
refactor(measure_theory/measure_space): use `covariant_class` instead of `add_le_add` ([#8285](https://github.com/leanprover-community/mathlib/pull/8285))
#### Estimated changes
Modified src/measure_theory/measure_space.lean




## [2021-07-14 10:14:18](https://github.com/leanprover-community/mathlib/commit/51cc43e)
feat(measure_theory/borel_space): a monotone function is measurable ([#8045](https://github.com/leanprover-community/mathlib/pull/8045))
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* measurable_of_monotone
- \+ *lemma* measurable_of_antimono



## [2021-07-14 08:37:24](https://github.com/leanprover-community/mathlib/commit/8e5af43)
chore(algebra/big_operators/basic): rename sum_(nat/int)_cast and (nat/int).coe_prod ([#8264](https://github.com/leanprover-community/mathlib/pull/8264))
The current names aren't great because
1. For `sum_nat_cast` and `sum_int_cast`, the LHS isn't a sum of casts but a cast of sums, and it doesn't follow any other naming convention (`nat.cast_...` or `....coe_sum`).
2. For `.coe_prod`, the coercion from `ℕ` or `ℤ` should be called `cast`.
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified src/algebra/big_operators/basic.lean
- \+ *lemma* nat.cast_sum
- \+ *lemma* int.cast_sum
- \+ *lemma* nat.cast_prod
- \+ *lemma* int.cast_prod
- \+/\- *lemma* units.coe_prod
- \- *lemma* sum_nat_cast
- \- *lemma* sum_int_cast
- \- *lemma* nat.coe_prod
- \- *lemma* int.coe_prod

Modified src/combinatorics/simple_graph/degree_sum.lean


Modified src/field_theory/chevalley_warning.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/matrix/determinant.lean


Modified src/measure_theory/probability_mass_function.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/number_theory/quadratic_reciprocity.lean




## [2021-07-14 06:54:06](https://github.com/leanprover-community/mathlib/commit/4709e61)
doc(*): bold a few more named theorems ([#8252](https://github.com/leanprover-community/mathlib/pull/8252))
#### Estimated changes
Modified src/analysis/calculus/darboux.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/convex/caratheodory.lean


Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/vitali_caratheodory.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/dioph.lean


Modified src/representation_theory/maschke.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/topology/continuous_function/stone_weierstrass.lean


Modified src/topology/continuous_function/weierstrass.lean


Modified src/topology/subset_properties.lean




## [2021-07-13 21:48:55](https://github.com/leanprover-community/mathlib/commit/5021c1f)
feat(data/int): conditionally complete linear order ([#8149](https://github.com/leanprover-community/mathlib/pull/8149))
Prove that the integers form a conditionally complete linear order.
I do not have a specific goal in mind for this, but it would have been helpful to formulate one of the Proof Ground problems using this.
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* coe_least_of_bdd_eq
- \+ *lemma* coe_greatest_of_bdd_eq

Created src/data/int/order.lean
- \+ *lemma* cSup_eq_greatest_of_bdd
- \+ *lemma* cSup_empty
- \+ *lemma* cSup_of_not_bdd_above
- \+ *lemma* cInf_eq_least_of_bdd
- \+ *lemma* cInf_empty
- \+ *lemma* cInf_of_not_bdd_below
- \+ *lemma* cSup_mem
- \+ *lemma* cInf_mem



## [2021-07-13 20:14:44](https://github.com/leanprover-community/mathlib/commit/29b63a7)
feat(data/matrix/basic): add conj_transpose ([#8291](https://github.com/leanprover-community/mathlib/pull/8291))
As requested by Eric Wieser, I pulled one single change of [#8289](https://github.com/leanprover-community/mathlib/pull/8289) out into a new PR. As such, this PR will not block anything in [#8289](https://github.com/leanprover-community/mathlib/pull/8289).
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* conj_transpose_apply
- \+ *lemma* conj_transpose_conj_transpose
- \+ *lemma* conj_transpose_zero
- \+ *lemma* conj_transpose_one
- \+ *lemma* conj_transpose_add
- \+ *lemma* conj_transpose_sub
- \+ *lemma* conj_transpose_smul
- \+ *lemma* conj_transpose_mul
- \+ *lemma* conj_transpose_neg
- \+ *lemma* star_eq_conj_transpose
- \+/\- *lemma* star_apply
- \+/\- *lemma* star_mul
- \+ *lemma* conj_transpose_minor
- \+ *lemma* conj_transpose_reindex
- \+ *def* conj_transpose



## [2021-07-13 20:14:43](https://github.com/leanprover-community/mathlib/commit/63266ff)
feat(group_theory/free_product): the free product of an indexed family of monoids ([#8256](https://github.com/leanprover-community/mathlib/pull/8256))
Defines the free product (categorical coproduct) of an indexed family of monoids. Proves its universal property. The free product of groups is a group.
Split off from [#7395](https://github.com/leanprover-community/mathlib/pull/7395)
#### Estimated changes
Modified docs/references.bib


Created src/group_theory/free_product.lean
- \+ *lemma* of_apply
- \+ *lemma* ext_hom
- \+ *lemma* lift_of
- \+ *lemma* induction_on
- \+ *lemma* of_left_inverse
- \+ *lemma* of_injective
- \+ *lemma* inv_def
- \+ *def* free_product
- \+ *def* of
- \+ *def* lift



## [2021-07-13 18:51:54](https://github.com/leanprover-community/mathlib/commit/905b875)
chore(data/matrix/block): move block matrices into their own file ([#8290](https://github.com/leanprover-community/mathlib/pull/8290))
This is a straight cut-and-paste, with no reordering or renaming.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/import.20fails/near/245802618)
#### Estimated changes
Modified src/data/matrix/basic.lean
- \- *lemma* from_blocks_apply₁₁
- \- *lemma* from_blocks_apply₁₂
- \- *lemma* from_blocks_apply₂₁
- \- *lemma* from_blocks_apply₂₂
- \- *lemma* from_blocks_to_blocks
- \- *lemma* to_blocks_from_blocks₁₁
- \- *lemma* to_blocks_from_blocks₁₂
- \- *lemma* to_blocks_from_blocks₂₁
- \- *lemma* to_blocks_from_blocks₂₂
- \- *lemma* from_blocks_transpose
- \- *lemma* to_block_apply
- \- *lemma* to_square_block_def
- \- *lemma* to_square_block_def'
- \- *lemma* to_square_block_prop_def
- \- *lemma* from_blocks_smul
- \- *lemma* from_blocks_add
- \- *lemma* from_blocks_multiply
- \- *lemma* from_blocks_diagonal
- \- *lemma* from_blocks_one
- \- *lemma* block_diagonal_apply
- \- *lemma* block_diagonal_apply_eq
- \- *lemma* block_diagonal_apply_ne
- \- *lemma* block_diagonal_transpose
- \- *lemma* block_diagonal_zero
- \- *lemma* block_diagonal_diagonal
- \- *lemma* block_diagonal_one
- \- *lemma* block_diagonal_add
- \- *lemma* block_diagonal_neg
- \- *lemma* block_diagonal_sub
- \- *lemma* block_diagonal_mul
- \- *lemma* block_diagonal_smul
- \- *lemma* block_diagonal'_eq_block_diagonal
- \- *lemma* block_diagonal'_minor_eq_block_diagonal
- \- *lemma* block_diagonal'_apply
- \- *lemma* block_diagonal'_apply_eq
- \- *lemma* block_diagonal'_apply_ne
- \- *lemma* block_diagonal'_transpose
- \- *lemma* block_diagonal'_zero
- \- *lemma* block_diagonal'_diagonal
- \- *lemma* block_diagonal'_one
- \- *lemma* block_diagonal'_add
- \- *lemma* block_diagonal'_neg
- \- *lemma* block_diagonal'_sub
- \- *lemma* block_diagonal'_mul
- \- *lemma* block_diagonal'_smul
- \- *def* from_blocks
- \- *def* to_blocks₁₁
- \- *def* to_blocks₁₂
- \- *def* to_blocks₂₁
- \- *def* to_blocks₂₂
- \- *def* to_block
- \- *def* to_square_block
- \- *def* to_square_block'
- \- *def* to_square_block_prop
- \- *def* block_diagonal
- \- *def* block_diagonal'

Created src/data/matrix/block.lean
- \+ *lemma* from_blocks_apply₁₁
- \+ *lemma* from_blocks_apply₁₂
- \+ *lemma* from_blocks_apply₂₁
- \+ *lemma* from_blocks_apply₂₂
- \+ *lemma* from_blocks_to_blocks
- \+ *lemma* to_blocks_from_blocks₁₁
- \+ *lemma* to_blocks_from_blocks₁₂
- \+ *lemma* to_blocks_from_blocks₂₁
- \+ *lemma* to_blocks_from_blocks₂₂
- \+ *lemma* from_blocks_transpose
- \+ *lemma* to_block_apply
- \+ *lemma* to_square_block_def
- \+ *lemma* to_square_block_def'
- \+ *lemma* to_square_block_prop_def
- \+ *lemma* from_blocks_smul
- \+ *lemma* from_blocks_add
- \+ *lemma* from_blocks_multiply
- \+ *lemma* from_blocks_diagonal
- \+ *lemma* from_blocks_one
- \+ *lemma* block_diagonal_apply
- \+ *lemma* block_diagonal_apply_eq
- \+ *lemma* block_diagonal_apply_ne
- \+ *lemma* block_diagonal_transpose
- \+ *lemma* block_diagonal_zero
- \+ *lemma* block_diagonal_diagonal
- \+ *lemma* block_diagonal_one
- \+ *lemma* block_diagonal_add
- \+ *lemma* block_diagonal_neg
- \+ *lemma* block_diagonal_sub
- \+ *lemma* block_diagonal_mul
- \+ *lemma* block_diagonal_smul
- \+ *lemma* block_diagonal'_eq_block_diagonal
- \+ *lemma* block_diagonal'_minor_eq_block_diagonal
- \+ *lemma* block_diagonal'_apply
- \+ *lemma* block_diagonal'_apply_eq
- \+ *lemma* block_diagonal'_apply_ne
- \+ *lemma* block_diagonal'_transpose
- \+ *lemma* block_diagonal'_zero
- \+ *lemma* block_diagonal'_diagonal
- \+ *lemma* block_diagonal'_one
- \+ *lemma* block_diagonal'_add
- \+ *lemma* block_diagonal'_neg
- \+ *lemma* block_diagonal'_sub
- \+ *lemma* block_diagonal'_mul
- \+ *lemma* block_diagonal'_smul
- \+ *def* from_blocks
- \+ *def* to_blocks₁₁
- \+ *def* to_blocks₁₂
- \+ *def* to_blocks₂₁
- \+ *def* to_blocks₂₂
- \+ *def* to_block
- \+ *def* to_square_block
- \+ *def* to_square_block'
- \+ *def* to_square_block_prop
- \+ *def* block_diagonal
- \+ *def* block_diagonal'

Modified src/linear_algebra/matrix/determinant.lean


Modified src/linear_algebra/matrix/to_lin.lean




## [2021-07-13 18:51:53](https://github.com/leanprover-community/mathlib/commit/461130b)
feat(category_theory/monoidal): the definition of Tor ([#7512](https://github.com/leanprover-community/mathlib/pull/7512))
# Tor, the left-derived functor of tensor product
We define `tor C n : C ⥤ C ⥤ C`, by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`.
For now we have almost nothing to say about it!
It would be good to show that this is naturally isomorphic to the functor obtained
by left-deriving in the first factor, instead.
#### Estimated changes
Modified src/category_theory/monoidal/category.lean
- \+ *def* tensoring_left
- \+/\- *def* tensoring_right

Created src/category_theory/monoidal/preadditive.lean


Created src/category_theory/monoidal/tor.lean
- \+ *def* Tor
- \+ *def* Tor'
- \+ *def* Tor_succ_of_projective
- \+ *def* Tor'_succ_of_projective



## [2021-07-13 17:32:47](https://github.com/leanprover-community/mathlib/commit/b091c3f)
feat(algebra/direct_sum): the submodules of an internal direct sum satisfy `supr A = ⊤` ([#8274](https://github.com/leanprover-community/mathlib/pull/8274))
The main results here are:
* `direct_sum.add_submonoid_is_internal.supr_eq_top`
* `direct_sum.submodule_is_internal.supr_eq_top`
Which we prove using the new lemmas
* `add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom`
* `submodule.supr_eq_range_dfinsupp_lsum`
There's no obvious way to reuse the proofs between the two, but thankfully all four proofs are quite short anyway.
These should aid in shortening [#8246](https://github.com/leanprover-community/mathlib/pull/8246).
#### Estimated changes
Modified src/algebra/direct_sum.lean
- \+ *lemma* add_submonoid_is_internal.supr_eq_top

Modified src/data/dfinsupp.lean
- \+ *lemma* _root_.add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom
- \+ *lemma* _root_.add_submonoid.mem_supr_iff_exists_dfinsupp
- \+ *lemma* _root_.add_submonoid.mem_supr_iff_exists_dfinsupp'

Modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* dfinsupp_sum_mem
- \+ *lemma* dfinsupp_sum_add_hom_mem
- \+ *lemma* supr_eq_range_dfinsupp_lsum
- \+ *lemma* mem_supr_iff_exists_dfinsupp
- \+ *lemma* mem_supr_iff_exists_dfinsupp'
- \- *lemma* submodule.dfinsupp_sum_mem
- \- *lemma* submodule.dfinsupp_sum_add_hom_mem

Modified src/linear_algebra/direct_sum_module.lean
- \+ *lemma* submodule_is_internal.supr_eq_top



## [2021-07-13 16:48:04](https://github.com/leanprover-community/mathlib/commit/3a0ef3c)
feat(ring_theory): (strict) monotonicity of `coe_submodule` ([#8273](https://github.com/leanprover-community/mathlib/pull/8273))
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* coe_submodule_mono
- \+ *lemma* coe_submodule_le_coe_submodule
- \+ *lemma* coe_submodule_strict_mono



## [2021-07-13 16:48:02](https://github.com/leanprover-community/mathlib/commit/8be0eda)
chore(ring_theory): allow Dedekind domains to be fields ([#8271](https://github.com/leanprover-community/mathlib/pull/8271))
During the Dedekind domain project, we found that the `¬ is_field R` condition is almost never needed, and it gets in the way when proving rings of integers are Dedekind domains. This PR removes this assumption from the three definitions.
Co-Authored-By: Ashvni <ashvni.n@gmail.com>
Co-Authored-By: Filippo A. E. Nuccio <filippo.nuccio@univ-st-etienne.fr>
#### Estimated changes
Modified docs/references.bib


Modified src/ring_theory/dedekind_domain.lean
- \+ *def* is_dedekind_domain_inv



## [2021-07-13 15:34:19](https://github.com/leanprover-community/mathlib/commit/815e91f)
chore(data/nat/prime): fix + add missing lemmas ([#8066](https://github.com/leanprover-community/mathlib/pull/8066))
I fixed up some indents as well, as they were bothering me quite a bit. The only "new" content is 597 - 617.
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* min_fac_le_div
- \+ *lemma* min_fac_sq_le_self
- \+ *lemma* min_fac_eq_one_iff
- \+ *lemma* min_fac_eq_two_iff
- \+ *lemma* factors_subset_right
- \+ *lemma* factors_subset_of_dvd
- \+ *theorem* min_fac_zero
- \+ *theorem* min_fac_one
- \+ *theorem* min_fac_eq
- \+ *theorem* min_fac_aux_has_prop
- \+ *theorem* min_fac_has_prop
- \+ *theorem* min_fac_dvd
- \+ *theorem* min_fac_prime
- \+ *theorem* min_fac_le_of_dvd
- \+ *theorem* min_fac_pos
- \+ *theorem* min_fac_le
- \+ *theorem* le_min_fac
- \+ *theorem* le_min_fac'
- \+ *theorem* prime_def_min_fac
- \+ *theorem* not_prime_iff_min_fac_lt
- \+ *def* min_fac_aux
- \+ *def* min_fac



## [2021-07-13 12:28:43](https://github.com/leanprover-community/mathlib/commit/bf86834)
chore(probability_theory/integration): style changes. Make arguments implicit, remove spaces, etc. ([#8286](https://github.com/leanprover-community/mathlib/pull/8286))
- make the measurable_space arguments of indep_fun implicit again. They were made explicit to accommodate the way `lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun` was written, with explicit `(borel ennreal)` arguments. Those arguments are not needed and are removed.
- use `measurable_set T` instead of `M.measurable_set' T`.
- write the type of several `have` explicitly.
- remove some spaces
- ensure there is only one tactic per line
- use `exact` instead of `apply` when the tactic is finishing
#### Estimated changes
Modified src/probability_theory/independence.lean
- \+/\- *def* indep_fun

Modified src/probability_theory/integration.lean
- \+/\- *lemma* lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun



## [2021-07-13 12:28:42](https://github.com/leanprover-community/mathlib/commit/f1e27d2)
feat(linear_algebra/finsupp): mem_supr_iff_exists_finset ([#8268](https://github.com/leanprover-community/mathlib/pull/8268))
This is an `iff` version of `exists_finset_of_mem_supr`
#### Estimated changes
Modified src/linear_algebra/finsupp.lean
- \+ *lemma* submodule.mem_supr_iff_exists_finset



## [2021-07-13 12:28:40](https://github.com/leanprover-community/mathlib/commit/3e56439)
chore(data/set/intervals): relax linear_order to preorder in the proofs of `Ixx_eq_empty_iff` ([#8071](https://github.com/leanprover-community/mathlib/pull/8071))
The previous formulations of `Ixx_eq_empty(_iff)` are basically a chaining of this formulation plus `not_lt` or `not_le`. But `not_lt` and `not_le` require `linear_order`. Removing them allows relaxing the typeclasses assumptions on `Ixx_eq_empty_iff` and slightly generalising `Ixx_eq_empty`.
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean


Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* Icc_eq_empty
- \+/\- *lemma* Ico_eq_empty
- \+/\- *lemma* Ioc_eq_empty
- \+/\- *lemma* Ioo_eq_empty
- \+ *lemma* Icc_eq_empty_of_lt
- \+ *lemma* Ico_eq_empty_of_le
- \+ *lemma* Ioc_eq_empty_of_le
- \+ *lemma* Ioo_eq_empty_of_le
- \+/\- *lemma* Ico_self
- \+/\- *lemma* Ioc_self
- \+/\- *lemma* Ioo_self
- \+/\- *lemma* Icc_eq_empty_iff
- \+/\- *lemma* Ico_eq_empty_iff
- \+ *lemma* Ioc_eq_empty_iff
- \+/\- *lemma* Ioo_eq_empty_iff

Modified src/data/set/intervals/disjoint.lean


Modified src/data/set/intervals/surj_on.lean


Modified src/measure_theory/interval_integral.lean




## [2021-07-13 11:23:36](https://github.com/leanprover-community/mathlib/commit/bb53a92)
chore(data/mv_polynomial/basic): use `is_empty σ` instead of `¬nonempty σ` ([#8277](https://github.com/leanprover-community/mathlib/pull/8277))
Split from [#7826](https://github.com/leanprover-community/mathlib/pull/7826)
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* C_surjective
- \- *lemma* C_surjective_fin_0

Modified src/ring_theory/jacobson.lean




## [2021-07-13 10:08:14](https://github.com/leanprover-community/mathlib/commit/dd9a0ea)
feat(geometry/manifold): add `charted_space` and `model_with_corners` for pi types ([#6578](https://github.com/leanprover-community/mathlib/pull/6578))
Also use `set.image2` in the `charted_space` instance for `model_prod`.
#### Estimated changes
Modified src/data/equiv/local_equiv.lean


Modified src/geometry/manifold/charted_space.lean
- \+ *lemma* pi_charted_space_chart_at
- \+ *def* model_pi

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *def* model_with_corners.pi



## [2021-07-13 09:28:15](https://github.com/leanprover-community/mathlib/commit/7bed785)
refactor(topology/metric/gromov_hausdorff_realized): speed up a proof ([#8287](https://github.com/leanprover-community/mathlib/pull/8287))
#### Estimated changes
Modified src/topology/metric_space/gromov_hausdorff_realized.lean




## [2021-07-13 07:40:48](https://github.com/leanprover-community/mathlib/commit/f1f4084)
feat(topology/algebra/ordered/basic): basis for the neighbourhoods of `top`/`bot` ([#8283](https://github.com/leanprover-community/mathlib/pull/8283))
#### Estimated changes
Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* nhds_top_basis
- \+ *lemma* nhds_bot_basis

Modified src/topology/instances/ennreal.lean
- \+ *lemma* nhds_top_basis
- \+ *lemma* nhds_zero_basis

Modified src/topology/instances/nnreal.lean
- \+ *lemma* nhds_zero
- \+ *lemma* nhds_zero_basis



## [2021-07-13 07:09:10](https://github.com/leanprover-community/mathlib/commit/f302c97)
feat(measure_theory/l2_space): the inner product of indicator_const_Lp and a function is the set_integral ([#8229](https://github.com/leanprover-community/mathlib/pull/8229))
#### Estimated changes
Modified src/measure_theory/integrable_on.lean
- \+ *lemma* integrable_on_Lp_of_measure_ne_top

Modified src/measure_theory/l2_space.lean
- \+ *lemma* inner_indicator_const_Lp_eq_set_integral_inner
- \+ *lemma* inner_indicator_const_Lp_eq_inner_set_integral
- \+ *lemma* inner_indicator_const_Lp_one

Modified src/measure_theory/set_integral.lean
- \+ *lemma* integral_inner
- \+ *lemma* integral_eq_zero_of_forall_integral_inner_eq_zero



## [2021-07-12 22:46:15](https://github.com/leanprover-community/mathlib/commit/9dfb9a6)
chore(topology/topological_fiber_bundle): renaming ([#8270](https://github.com/leanprover-community/mathlib/pull/8270))
In this PR I changed
- `prebundle_trivialization` to `topological_fiber_bundle.pretrivialization`
- `bundle_trivialization` to `topological_fiber_bundle.trivialization`
so to make names consistent with `vector_bundle`. I also changed the name of the file for consistency.
#### Estimated changes
Modified src/geometry/manifold/basic_smooth_bundle.lean


Renamed src/topology/topological_fiber_bundle.lean to src/topology/fiber_bundle.lean
- \+/\- *lemma* continuous_coord_change
- \+ *lemma* is_image_preimage_prod
- \+ *lemma* frontier_preimage
- \+ *lemma* _root_.is_topological_fiber_bundle.exists_trivialization_Icc_subset
- \+ *lemma* continuous_symm_pretrivialization_at
- \+ *lemma* is_open_source_pretrivialization_at
- \+ *lemma* is_open_target_pretrivialization_at_inter
- \- *lemma* bundle_trivialization.is_image_preimage_prod
- \- *lemma* bundle_trivialization.frontier_preimage
- \- *lemma* is_topological_fiber_bundle.exists_trivialization_Icc_subset
- \- *lemma* continuous_symm_trivialization_at
- \- *lemma* is_open_source_trivialization_at
- \- *lemma* is_open_target_trivialization_at_inter
- \+ *def* to_pretrivialization
- \+/\- *def* coord_change
- \+ *def* restr_open
- \+/\- *def* local_triv
- \+/\- *def* local_triv_at
- \+ *def* trivialization_at
- \- *def* to_prebundle_trivialization
- \- *def* bundle_trivialization.restr_open
- \- *def* bundle_trivialization_at

Modified src/topology/vector_bundle.lean
- \+/\- *lemma* trivialization.coe_fst
- \+ *lemma* continuous_linear_equiv_at_apply
- \+ *lemma* continuous_linear_equiv_at_apply'
- \- *lemma* trivialization.continuous_linear_equiv_at_apply
- \- *lemma* trivialization.continuous_linear_equiv_at_apply'
- \+ *def* continuous_linear_equiv_at
- \+ *def* trivial_topological_vector_bundle.trivialization
- \- *def* trivialization.continuous_linear_equiv_at
- \- *def* trivial_bundle_trivialization



## [2021-07-12 22:46:14](https://github.com/leanprover-community/mathlib/commit/cde5748)
feat(measure_theory/measure_space): add `finite_measure_sub` instance ([#8239](https://github.com/leanprover-community/mathlib/pull/8239))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* sub_le



## [2021-07-12 21:10:34](https://github.com/leanprover-community/mathlib/commit/5ea9a07)
feat(measure_theory/integration): add `lintegral_union` ([#8238](https://github.com/leanprover-community/mathlib/pull/8238))
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_union

Modified src/measure_theory/measure_space.lean
- \+ *lemma* cond

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tsum_bool



## [2021-07-12 21:10:33](https://github.com/leanprover-community/mathlib/commit/4cd6179)
refactor(measure_theory/simple_func_dense): generalize L1.simple_func.dense_embedding to Lp ([#8209](https://github.com/leanprover-community/mathlib/pull/8209))
This PR generalizes all the more abstract results about approximation by simple functions, from L1 to Lp (`p ≠ ∞`).  Notably, this includes 
* the definition `Lp.simple_func`, the `add_subgroup` of `Lp` of classes containing a simple representative
* the coercion `Lp.simple_func.coe_to_Lp` from this subgroup to `Lp`, as a continuous linear map
* `Lp.simple_func.dense_embedding`, this subgroup is dense in `Lp`
* `mem_ℒp.induction`, to prove a predicate holds for `mem_ℒp` functions it suffices to prove that it behaves appropriately on `mem_ℒp` simple functions
Many lemmas get renamed from `L1.simple_func.*` to `Lp.simple_func.*`, and have hypotheses or conclusions changed from `integrable` to `mem_ℒp`.
I take the opportunity to streamline the construction by deleting some instances which typeclass inference can find, and some lemmas which are re-statements of more general results about `add_subgroup`s in normed groups.  In my opinion, this extra material obscures the structure of the construction.  Here is a list of the definitions deleted:
- `instance : has_coe (α →₁ₛ[μ] E) (α →₁[μ] E)`
- `instance : has_coe_to_fun (α →₁ₛ[μ] E)`
- `instance : inhabited (α →₁ₛ[μ] E)`
- `protected def normed_group : normed_group (α →₁ₛ[μ] E)`
and lemmas deleted (in the `L1.simple_func` namespace unless specified):
- `simple_func.tendsto_approx_on_univ_L1`
- `eq`
- `eq_iff`
- `eq_iff'`
- `coe_zero`
- `coe_add`
- `coe_neg`
- `coe_sub`
- `edist_eq`
- `dist_eq`
- `norm_eq`
- `lintegral_edist_to_simple_func_lt_top`
- `dist_to_simple_func`
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* coe_div

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/integrable_on.lean
- \+ *lemma* integrable_add_of_disjoint
- \- *lemma* integrable_add

Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_indicator_le
- \+ *lemma* mem_ℒp.indicator
- \+ *lemma* mem_ℒp_add_of_disjoint

Modified src/measure_theory/simple_func_dense.lean
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_smul
- \+ *lemma* to_Lp_eq_to_Lp
- \+ *lemma* to_Lp_eq_mk
- \+ *lemma* to_Lp_zero
- \+ *lemma* to_Lp_add
- \+ *lemma* to_Lp_neg
- \+ *lemma* to_Lp_sub
- \+ *lemma* to_Lp_smul
- \+ *lemma* norm_to_Lp
- \+/\- *lemma* to_simple_func_eq_to_fun
- \+ *lemma* to_Lp_to_simple_func
- \+ *lemma* to_simple_func_to_Lp
- \+/\- *lemma* zero_to_simple_func
- \+/\- *lemma* add_to_simple_func
- \+/\- *lemma* neg_to_simple_func
- \+/\- *lemma* sub_to_simple_func
- \+/\- *lemma* smul_to_simple_func
- \+/\- *lemma* norm_to_simple_func
- \+ *lemma* mem_ℒp.induction
- \+ *lemma* L1.simple_func.to_Lp_one_eq_to_L1
- \- *lemma* tendsto_approx_on_univ_L1
- \- *lemma* coe_zero
- \- *lemma* coe_add
- \- *lemma* coe_neg
- \- *lemma* coe_sub
- \- *lemma* edist_eq
- \- *lemma* dist_eq
- \- *lemma* norm_eq
- \- *lemma* to_L1_eq_to_L1
- \- *lemma* to_L1_eq_mk
- \- *lemma* to_L1_zero
- \- *lemma* to_L1_add
- \- *lemma* to_L1_neg
- \- *lemma* to_L1_sub
- \- *lemma* to_L1_smul
- \- *lemma* norm_to_L1
- \- *lemma* to_L1_to_simple_func
- \- *lemma* to_simple_func_to_L1
- \- *lemma* lintegral_edist_to_simple_func_lt_top
- \- *lemma* dist_to_simple_func
- \+/\- *def* simple_func
- \+ *def* to_Lp
- \+/\- *def* to_simple_func
- \+ *def* coe_to_Lp
- \- *def* to_L1
- \- *def* coe_to_L1



## [2021-07-12 18:54:39](https://github.com/leanprover-community/mathlib/commit/a9cb722)
docs(data/rel): add module docstring ([#8248](https://github.com/leanprover-community/mathlib/pull/8248))
#### Estimated changes
Modified src/data/rel.lean
- \+/\- *def* rel



## [2021-07-12 17:16:06](https://github.com/leanprover-community/mathlib/commit/a2b00f3)
feat(algebra/opposites): functoriality of the opposite monoid ([#8254](https://github.com/leanprover-community/mathlib/pull/8254))
A hom `α →* β` can equivalently be viewed as a hom `αᵒᵖ →* βᵒᵖ`.
Split off from [#7395](https://github.com/leanprover-community/mathlib/pull/7395)
#### Estimated changes
Modified src/algebra/opposites.lean
- \+ *def* monoid_hom.op
- \+ *def* monoid_hom.unop
- \+ *def* add_monoid_hom.op
- \+ *def* add_monoid_hom.unop
- \+ *def* ring_hom.op
- \+ *def* ring_hom.unop



## [2021-07-12 16:03:49](https://github.com/leanprover-community/mathlib/commit/6fa678f)
feat(ring_theory): `coe_submodule S (⊤ : ideal R) = 1` ([#8272](https://github.com/leanprover-community/mathlib/pull/8272))
A little `simp` lemma and its dependencies. As I was implementing it, I saw the definition of `has_one (submodule R A)` can be cleaned up a bit.
#### Estimated changes
Modified src/algebra/algebra/operations.lean
- \+ *lemma* algebra_map_mem
- \+ *lemma* mem_one
- \+ *theorem* one_eq_range
- \- *theorem* one_eq_map_top

Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean
- \+ *lemma* coe_submodule_top



## [2021-07-12 14:22:14](https://github.com/leanprover-community/mathlib/commit/0a8e3ed)
feat(data/equiv/fin): fin_order_iso_subtype ([#8258](https://github.com/leanprover-community/mathlib/pull/8258))
Promote a `fin n` into a larger `fin m`, as a subtype where the underlying
values are retained. This is the `order_iso` version of `fin.cast_le`.
#### Estimated changes
Modified src/data/equiv/fin.lean
- \+ *def* fin.cast_le_order_iso



## [2021-07-12 14:22:13](https://github.com/leanprover-community/mathlib/commit/66cc624)
feat(data/list/basic): more lemmas about permutations_aux2 ([#8198](https://github.com/leanprover-community/mathlib/pull/8198))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* permutations_aux2_snd_eq
- \+ *theorem* permutations_aux2_comp_append
- \+/\- *theorem* map_permutations_aux2'
- \+/\- *theorem* map_permutations_aux2
- \+ *theorem* map_map_permutations_aux2



## [2021-07-12 12:59:26](https://github.com/leanprover-community/mathlib/commit/695cb07)
feat({data,linear_algebra}/{finsupp,dfinsupp}): add `{add_submonoid,submodule}.[d]finsupp_sum_mem` ([#8269](https://github.com/leanprover-community/mathlib/pull/8269))
These lemmas are trivial consequences of the finset lemmas, but having them avoids having to unfold `[d]finsupp.sum`.
`dfinsupp_sum_add_hom_mem` is particularly useful because this one has some messy decidability arguments to eliminate.
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* _root_.submonoid.dfinsupp_prod_mem
- \+ *lemma* _root_.add_submonoid.dfinsupp_sum_add_hom_mem

Modified src/data/finsupp/basic.lean
- \+ *lemma* _root_.submonoid.finsupp_prod_mem

Modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* submodule.dfinsupp_sum_mem
- \+ *lemma* submodule.dfinsupp_sum_add_hom_mem

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* submodule.finsupp_sum_mem



## [2021-07-12 10:54:32](https://github.com/leanprover-community/mathlib/commit/40ffaa5)
feat(linear_algebra/free_module): add module.free.resolution ([#8231](https://github.com/leanprover-community/mathlib/pull/8231))
Any module is a quotient of a free module. This is stated as surjectivity of `finsupp.total M M R id : (M →₀ R) →ₗ[R] M`.
#### Estimated changes
Modified src/algebra/module/projective.lean


Modified src/linear_algebra/finsupp.lean
- \+ *lemma* total_surjective
- \+ *lemma* total_id_surjective
- \+ *theorem* total_range

Modified src/linear_algebra/free_module.lean




## [2021-07-12 07:00:28](https://github.com/leanprover-community/mathlib/commit/e1c649d)
feat(category_theory/abelian): the five lemma ([#8265](https://github.com/leanprover-community/mathlib/pull/8265))
#### Estimated changes
Modified src/algebra/homology/exact.lean


Modified src/category_theory/abelian/basic.lean
- \+ *lemma* comp_coimage_π_eq_zero
- \+ *lemma* epi_snd_of_is_limit
- \+ *lemma* epi_fst_of_is_limit
- \+ *lemma* epi_fst_of_factor_thru_epi_mono_factorization
- \+ *lemma* mono_inr_of_is_colimit
- \+ *lemma* mono_inl_of_is_colimit
- \+ *lemma* mono_inl_of_factor_thru_epi_mono_factorization

Modified src/category_theory/abelian/diagram_lemmas/four.lean
- \+ *lemma* epi_of_epi_of_epi_of_mono
- \+ *lemma* is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso

Modified src/category_theory/abelian/exact.lean
- \+ *def* is_colimit_coimage
- \+ *def* is_colimit_image

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* is_limit_of_factors
- \+ *def* is_colimit_of_factors

Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* comp_factor_thru_image_eq_zero

Modified src/category_theory/subobject/limits.lean
- \+ *lemma* factor_thru_kernel_subobject_comp_kernel_subobject_iso



## [2021-07-12 06:15:32](https://github.com/leanprover-community/mathlib/commit/92d0dd8)
feat(category_theory/limits): monomorphisms from initial ([#8099](https://github.com/leanprover-community/mathlib/pull/8099))
Defines a class for categories where every morphism from initial is a monomorphism. If the category has a terminal object, this is equivalent to saying the unique morphism from initial to terminal is a monomorphism, so this is essentially a "zero_le_one" for categories. I'm happy to change the name of this class!
This axiom does not appear to have a common name, though it is (equivalent to) the second of Freyd's AT axioms: specifically it is a property shared by abelian categories and pretoposes. The main advantage to this class is that it is the precise condition required for the subobject lattice to have a bottom element, resolving the discussion here: https://github.com/leanprover-community/mathlib/pull/6278#discussion_r577702542
I've also made some minor changes to later parts of this file, essentially de-duplicating arguments, and moving the `comparison` section up so that all the results about terminal objects in index categories of limits are together rather than split in two.
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean
- \+ *lemma* is_initial.mono_from
- \+ *lemma* initial_mono_class.of_is_initial
- \+ *lemma* initial_mono_class.of_initial
- \+ *lemma* initial_mono_class.of_is_terminal
- \+ *lemma* initial_mono_class.of_terminal
- \+ *def* is_terminal.unique_up_to_iso
- \+ *def* is_initial.unique_up_to_iso
- \+/\- *def* terminal_comparison
- \+/\- *def* initial_comparison
- \+/\- *def* cone_of_diagram_initial
- \+/\- *def* limit_of_diagram_initial
- \+/\- *def* limit_of_initial
- \+/\- *def* cocone_of_diagram_terminal
- \+/\- *def* colimit_of_diagram_terminal
- \+/\- *def* colimit_of_terminal



## [2021-07-12 04:01:46](https://github.com/leanprover-community/mathlib/commit/e22789e)
feat(algebra/big_operators/finprod): add a few lemmas ([#8261](https://github.com/leanprover-community/mathlib/pull/8261))
* add `finprod_eq_single` and `finsum_eq_single`;
* add `finprod_induction` and `finsum_induction`;
* add `single_le_finprod` and `single_le_finsum`;
* add `one_le_finprod'` and `finsum_nonneg`.
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_eq_single
- \+/\- *lemma* finprod_unique
- \+ *lemma* finprod_induction
- \+/\- *lemma* finprod_nonneg
- \+ *lemma* one_le_finprod'
- \+ *lemma* single_le_finprod

Modified src/data/equiv/basic.lean
- \+ *lemma* plift.eq_up_iff_down_eq



## [2021-07-12 01:47:08](https://github.com/leanprover-community/mathlib/commit/d5c6f61)
feat(algebra/group/hom): monoid_hom.injective_iff in iff form ([#8259](https://github.com/leanprover-community/mathlib/pull/8259))
Interpret the injectivity of a group hom as triviality of the kernel,
in iff form. This helps make explicit simp lemmas about
the application of such homs,
as in the added `extend_domain_eq_one_iff` lemma.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* injective_iff'

Modified src/group_theory/perm/basic.lean
- \+ *lemma* extend_domain_eq_one_iff



## [2021-07-11 20:46:12](https://github.com/leanprover-community/mathlib/commit/24d7a8c)
feat(group_theory/quotient_group): lemmas for quotients involving `subgroup_of` ([#8111](https://github.com/leanprover-community/mathlib/pull/8111))
#### Estimated changes
Modified src/group_theory/quotient_group.lean
- \+ *def* quotient_map_subgroup_of_of_le
- \+ *def* equiv_quotient_subgroup_of_of_eq



## [2021-07-11 20:13:23](https://github.com/leanprover-community/mathlib/commit/19beb12)
feat(measure_theory/{lp_space,set_integral}): extend linear map lemmas from R to is_R_or_C ([#8210](https://github.com/leanprover-community/mathlib/pull/8210))
#### Estimated changes
Modified src/analysis/calculus/parametric_integral.lean


Modified src/measure_theory/lp_space.lean
- \+/\- *lemma* coe_fn_comp_Lp
- \+/\- *lemma* norm_comp_Lp_le
- \+/\- *lemma* norm_compLpL_le
- \+/\- *def* comp_Lp
- \+/\- *def* comp_Lpₗ
- \+/\- *def* comp_LpL

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* integral_comp_Lp
- \+/\- *lemma* continuous_integral_comp_L1
- \+/\- *lemma* integral_comp_comm
- \+/\- *lemma* integral_comp_comm'
- \+/\- *lemma* integral_comp_L1_comm
- \+/\- *lemma* integral_of_real
- \+ *lemma* integral_re
- \+ *lemma* integral_im
- \+/\- *lemma* integral_conj



## [2021-07-11 19:28:27](https://github.com/leanprover-community/mathlib/commit/6d200cb)
feat(analysis/normed_space/inner_product): Bessel's inequality ([#8251](https://github.com/leanprover-community/mathlib/pull/8251))
A proof both of Bessel's inequality and that the infinite sum defined by Bessel's inequality converges.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* orthonormal.inner_left_right_finset
- \+ *lemma* orthonormal.sum_inner_products_le
- \+ *lemma* orthonormal.tsum_inner_products_le
- \+ *lemma* orthonormal.inner_products_summable



## [2021-07-11 14:37:02](https://github.com/leanprover-community/mathlib/commit/bee165a)
feat(category_theory/abelian/opposite): Adds some op-related isomorphism for (co)kernels. ([#8255](https://github.com/leanprover-community/mathlib/pull/8255))
#### Estimated changes
Modified src/category_theory/abelian/opposite.lean
- \+ *def* kernel_op_unop
- \+ *def* cokernel_op_unop
- \+ *def* kernel_unop_op
- \+ *def* cokernel_unop_op
- \+ *def* kernel_op_op
- \+ *def* cokernel_op_op
- \+ *def* kernel_unop_unop
- \+ *def* cokernel_unop_unop



## [2021-07-11 13:10:23](https://github.com/leanprover-community/mathlib/commit/1e62218)
feat(data/int/gcd): norm_num extension for gcd ([#8053](https://github.com/leanprover-community/mathlib/pull/8053))
Implements a `norm_num` plugin to evaluate terms like `nat.gcd 6 8 = 2`, `nat.coprime 127 128`, and so on for `{nat, int}.{gcd, lcm, coprime}`.
#### Estimated changes
Modified src/data/int/gcd.lean
- \+ *lemma* int_gcd_helper'
- \+ *lemma* nat_gcd_helper_dvd_left
- \+ *lemma* nat_gcd_helper_dvd_right
- \+ *lemma* nat_gcd_helper_2
- \+ *lemma* nat_gcd_helper_1
- \+ *lemma* nat_lcm_helper
- \+ *lemma* nat_coprime_helper_zero_left
- \+ *lemma* nat_coprime_helper_zero_right
- \+ *lemma* nat_coprime_helper_1
- \+ *lemma* nat_coprime_helper_2
- \+ *lemma* nat_not_coprime_helper
- \+ *lemma* int_gcd_helper
- \+ *lemma* int_gcd_helper_neg_left
- \+ *lemma* int_gcd_helper_neg_right
- \+ *lemma* int_lcm_helper
- \+ *lemma* int_lcm_helper_neg_left
- \+ *lemma* int_lcm_helper_neg_right

Modified src/data/nat/gcd.lean
- \+ *theorem* not_coprime_zero_zero

Modified test/norm_num.lean


Created test/norm_num_ext.lean




## [2021-07-11 10:44:09](https://github.com/leanprover-community/mathlib/commit/14f324b)
chore(data/set/basic): remove set.decidable_mem ([#8240](https://github.com/leanprover-community/mathlib/pull/8240))
The only purpose of this instance was to enable the spelling `[decidable_pred s]` when what is actually needed is `decidable_pred (∈ s)`, which is a bad idea.
This is a follow-up to [#8211](https://github.com/leanprover-community/mathlib/pull/8211).
Only two proofs needed this instance, and both were using completely the wrong lemmas anyway.
#### Estimated changes
Modified src/data/equiv/fintype.lean


Modified src/data/set/basic.lean




## [2021-07-11 02:16:20](https://github.com/leanprover-community/mathlib/commit/850928d)
chore(scripts): update nolints.txt ([#8257](https://github.com/leanprover-community/mathlib/pull/8257))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-07-11 01:40:33](https://github.com/leanprover-community/mathlib/commit/e627394)
feat(analysis/special_functions): limit of (1+1/x)^x ([#8243](https://github.com/leanprover-community/mathlib/pull/8243))
Resolves https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/e.20as.20limit.20of.20.281.2B1.2Fn.29.5En.
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* tendsto_mul_log_one_plus_div_at_top

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* tendsto_one_plus_div_rpow_exp
- \+ *lemma* tendsto_one_plus_div_pow_exp



## [2021-07-10 20:40:14](https://github.com/leanprover-community/mathlib/commit/90d8d46)
feat(category_theory/monad): monad forget is monadic ([#8161](https://github.com/leanprover-community/mathlib/pull/8161))
cc @adamtopaz 
wip since I need to dualise
#### Estimated changes
Modified src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/algebraic_topology/simplex_category.lean


Modified src/category_theory/Fintype.lean


Modified src/category_theory/adjunction/lifting.lean


Modified src/category_theory/connected_components.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/monad/adjunction.lean
- \+ *lemma* monad.left_comparison
- \+ *lemma* comonad.left_comparison
- \+/\- *def* to_monad
- \+/\- *def* to_comonad
- \+ *def* adj_to_monad_iso
- \+ *def* adj_to_comonad_iso
- \+/\- *def* monad.comparison
- \+/\- *def* monad.comparison_forget
- \+/\- *def* comonad.comparison
- \+ *def* comonad.comparison_forget
- \- *def* comparison_forget

Modified src/category_theory/monad/algebra.lean
- \+ *lemma* left_adjoint_forget
- \+ *lemma* of_right_adjoint_forget
- \+/\- *lemma* coalgebra_iso_of_iso
- \+ *lemma* right_adjoint_forget
- \+ *lemma* of_left_adjoint_forget
- \+/\- *def* adj

Modified src/category_theory/monad/basic.lean
- \+ *lemma* monad_to_functor_map_iso_monad_iso_mk
- \+ *lemma* comonad_to_functor_map_iso_comonad_iso_mk
- \+ *def* monad_iso.mk
- \+ *def* comonad_iso.mk

Modified src/category_theory/skeletal.lean


Modified src/topology/category/Compactum.lean




## [2021-07-10 18:38:10](https://github.com/leanprover-community/mathlib/commit/8b4628e)
feat(data/fintype/basic): induction principle for finite types ([#8158](https://github.com/leanprover-community/mathlib/pull/8158))
This lets us prove things about finite types by induction, analogously to proving things about natural numbers by induction. Here `pempty` plays the role of `0` and `option` plays the role of `nat.succ`. We need an extra hypothesis that our statement is invariant under equivalence of types. Used in [#8019](https://github.com/leanprover-community/mathlib/pull/8019).
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* induction_empty_option
- \+ *def* trunc_rec_empty_option



## [2021-07-10 08:01:40](https://github.com/leanprover-community/mathlib/commit/aa78feb)
feat(category_theory/is_connected): constant functor is full ([#8233](https://github.com/leanprover-community/mathlib/pull/8233))
Shows the constant functor on a connected category is full.
Also golfs a later proof slightly.
#### Estimated changes
Modified src/category_theory/is_connected.lean




## [2021-07-10 08:01:39](https://github.com/leanprover-community/mathlib/commit/b1806d1)
chore(analysis/normed_space/banach): speed up the proof ([#8230](https://github.com/leanprover-community/mathlib/pull/8230))
This proof has timed out in multiple refactor PRs I've made. This splits out an auxiliary definition.
The new definition takes about 3.5s to elaborate, and the two lemmas are <500ms each.
The old lemma took 45s.
#### Estimated changes
Modified src/analysis/normed_space/banach.lean
- \+ *lemma* coe_of_bijective
- \+ *lemma* range_eq_map_coprod_subtypeL_equiv_of_is_compl



## [2021-07-10 07:14:29](https://github.com/leanprover-community/mathlib/commit/9e0462c)
feat(topology/algebra/infinite_sum): summable_empty ([#8241](https://github.com/leanprover-community/mathlib/pull/8241))
Every function over an empty type is summable.
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum_empty
- \+ *lemma* summable_empty
- \+ *lemma* tsum_empty



## [2021-07-10 04:07:29](https://github.com/leanprover-community/mathlib/commit/e18b3a8)
feat(category_theory/limits): transfer limit creation along diagram iso ([#8237](https://github.com/leanprover-community/mathlib/pull/8237))
#### Estimated changes
Modified src/category_theory/limits/creates.lean
- \+ *def* creates_limit_of_iso_diagram
- \+ *def* creates_colimit_of_iso_diagram



## [2021-07-10 03:32:13](https://github.com/leanprover-community/mathlib/commit/d0e09dd)
feat(linear_algebra/matrix/nonsingular_inverse): more lemmas ([#8216](https://github.com/leanprover-community/mathlib/pull/8216))
add more defs and lemmas
#### Estimated changes
Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* is_unit_det_of_invertible
- \+ *lemma* inv_eq_nonsing_inv_of_invertible
- \+/\- *lemma* is_unit_det_of_left_inverse
- \+/\- *lemma* is_unit_det_of_right_inverse
- \+/\- *lemma* nonsing_inv_left_right
- \+/\- *lemma* nonsing_inv_right_left
- \+ *lemma* inv_eq_left_inv
- \+ *lemma* inv_eq_right_inv
- \+ *lemma* left_inv_eq_left_inv
- \+ *lemma* right_inv_eq_right_inv
- \+ *lemma* right_inv_eq_left_inv
- \+ *lemma* mul_inv_of_invertible
- \+ *lemma* inv_mul_of_invertible
- \+/\- *def* det_invertible_of_left_inverse
- \+/\- *def* det_invertible_of_right_inverse
- \+ *def* invertible_of_left_inverse
- \+ *def* invertible_of_right_inverse

Modified src/linear_algebra/unitary_group.lean




## [2021-07-10 02:13:42](https://github.com/leanprover-community/mathlib/commit/b52c1f0)
chore(scripts): update nolints.txt ([#8245](https://github.com/leanprover-community/mathlib/pull/8245))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-07-09 22:11:36](https://github.com/leanprover-community/mathlib/commit/70320f7)
feat(category_theory/category/Kleisli): Fix lint errors ([#8244](https://github.com/leanprover-community/mathlib/pull/8244))
Fixes some lint errors for this file: unused arguments, module doc, inhabited instances
#### Estimated changes
Modified src/category_theory/category/Kleisli.lean
- \+/\- *lemma* Kleisli.id_def
- \+/\- *lemma* Kleisli.comp_def
- \+/\- *def* Kleisli
- \+/\- *def* Kleisli.mk



## [2021-07-09 19:00:53](https://github.com/leanprover-community/mathlib/commit/a444e81)
feat(measure_theory/borel_space): a preconnected set is measurable ([#8044](https://github.com/leanprover-community/mathlib/pull/8044))
In a conditionally complete linear order equipped with the order topology and the corresponding borel σ-algebra, any preconnected set is measurable.
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* set.finite_of_forall_between_eq_endpoints

Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measurable_set_lt'
- \+/\- *lemma* measurable_set_lt
- \+ *lemma* set.ord_connected.measurable_set
- \+ *lemma* is_preconnected.measurable_set

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* is_preconnected.ord_connected
- \+ *lemma* set.ord_connected.is_preconnected



## [2021-07-09 15:19:06](https://github.com/leanprover-community/mathlib/commit/bcd61b1)
feat(algebra/category): provide right adjoint instances for forget ([#8235](https://github.com/leanprover-community/mathlib/pull/8235))
Also adds some universe variables since they weren't inferred sensibly.
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean
- \+/\- *def* of
- \+/\- *def* of_self_iso
- \+/\- *def* free
- \+/\- *def* adj

Modified src/algebra/category/CommRing/adjunctions.lean
- \+/\- *def* free
- \+/\- *def* adj

Modified src/algebra/category/Group/adjunctions.lean


Modified src/algebra/category/Module/adjunctions.lean


Modified src/algebra/category/Mon/adjunctions.lean
- \+ *def* free
- \+ *def* adj

Modified src/topology/category/Top/adjunctions.lean




## [2021-07-09 13:36:51](https://github.com/leanprover-community/mathlib/commit/ee01817)
chore(data/set/basic): use `decidable_pred (∈ s)` instead of `decidable_pred s`. ([#8211](https://github.com/leanprover-community/mathlib/pull/8211))
The latter exploits the fact that sets are functions to Prop, and is an annoying form as lemmas are never stated about it.
In future we should consider removing the `set.decidable_mem` instance which encourages this misuse.
Making this change reveals a collection of pointless decidable arguments requiring that finset membership be decidable; something which is always true anyway.
Two proofs in `data/pequiv` caused a crash inside the C++ portion of the `finish` tactic; it was easier to just write the simple proofs manually than to debug the C++ code.
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \+/\- *def* curry_fin_finset

Modified src/combinatorics/simple_graph/basic.lean


Modified src/data/equiv/basic.lean
- \+/\- *lemma* insert_symm_apply_inl
- \+/\- *lemma* insert_symm_apply_inr
- \+/\- *lemma* insert_apply_left
- \+/\- *lemma* insert_apply_right
- \+/\- *lemma* sum_compl_apply_inl
- \+/\- *lemma* sum_compl_apply_inr
- \+/\- *lemma* sum_compl_symm_apply_of_mem
- \+/\- *lemma* sum_compl_symm_apply_of_not_mem
- \+/\- *lemma* sum_compl_symm_apply

Modified src/data/equiv/denumerable.lean
- \+/\- *def* of_nat
- \+/\- *def* denumerable

Modified src/data/equiv/encodable/basic.lean
- \+/\- *def* decidable_range_encode

Modified src/data/fintype/sort.lean


Modified src/data/nat/basic.lean


Modified src/data/pequiv.lean
- \+/\- *lemma* mem_of_set_self_iff
- \+/\- *lemma* mem_of_set_iff
- \+/\- *lemma* of_set_eq_some_iff
- \+/\- *lemma* of_set_eq_some_self_iff
- \+/\- *lemma* of_set_eq_refl
- \+/\- *def* of_set

Modified src/data/pfun.lean
- \+/\- *def* eval_opt

Modified src/data/set/basic.lean


Modified src/data/set/finite.lean
- \+/\- *def* fintype_subset

Modified src/data/sym2.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/group_theory/coset.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/subgroup.lean


Modified src/group_theory/subgroup.lean


Modified src/linear_algebra/multilinear.lean
- \+/\- *lemma* curry_fin_finset_apply
- \+/\- *def* curry_fin_finset

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable.piecewise

Modified src/order/order_iso_nat.lean


Modified src/ring_theory/free_comm_ring.lean
- \+/\- *theorem* map_subtype_val_restriction
- \+/\- *def* restriction



## [2021-07-09 13:36:49](https://github.com/leanprover-community/mathlib/commit/a312e7e)
chore(topology/topological_fiber_bundle): reorganizing the code ([#7938](https://github.com/leanprover-community/mathlib/pull/7938))
What I do here:
 - Get rid of `local_triv`: it is not needed.
 - Change `local_triv_ext` to `local_triv`
 - Rename `local_triv'` as `local_triv_as_local_equiv` (name suggested by @sgouezel)
 - Improve type class inference by getting rid of `dsimp` in instances
 - Move results about `bundle` that do not need the topology in an appropriate file
 - Update docs accordingly.
Nothing else.
#### Estimated changes
Created src/data/bundle.lean
- \+ *lemma* coe_fst
- \+ *lemma* to_total_space_coe
- \+ *lemma* coe_snd_map_apply
- \+ *lemma* coe_snd_map_smul
- \+ *def* total_space
- \+ *def* proj
- \+ *def* total_space_mk
- \+ *def* trivial
- \+ *def* trivial.proj_snd

Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_at.comp_continuous_within_at
- \+ *lemma* continuous_within_at.fst
- \+ *lemma* continuous_within_at.snd
- \+ *lemma* continuous_within_at_prod_iff

Modified src/topology/topological_fiber_bundle.lean
- \+ *lemma* source_inter_preimage_target_inter
- \+ *lemma* mem_local_triv_as_local_equiv_source
- \+ *lemma* mem_local_triv_as_local_equiv_target
- \+ *lemma* local_triv_as_local_equiv_apply
- \+ *lemma* local_triv_as_local_equiv_trans
- \+/\- *lemma* open_source'
- \+ *lemma* local_triv_at_def
- \+ *lemma* local_triv_as_local_equiv_coe
- \+ *lemma* local_triv_as_local_equiv_source
- \+ *lemma* local_triv_as_local_equiv_target
- \+ *lemma* local_triv_as_local_equiv_symm
- \+/\- *lemma* base_set_at
- \+/\- *lemma* local_triv_apply
- \+/\- *lemma* mem_local_triv_source
- \+/\- *lemma* mem_local_triv_target
- \+/\- *lemma* local_triv_symm_fst
- \+ *lemma* mem_local_triv_at_base_set
- \- *lemma* coe_fst
- \- *lemma* to_total_space_coe
- \- *lemma* coe_snd_map_apply
- \- *lemma* coe_snd_map_smul
- \- *lemma* mem_local_triv'_source
- \- *lemma* mem_local_triv'_target
- \- *lemma* local_triv'_apply
- \- *lemma* local_triv'_symm_apply
- \- *lemma* local_triv'_trans
- \- *lemma* open_target'
- \- *lemma* local_triv'_coe
- \- *lemma* local_triv'_source
- \- *lemma* local_triv'_target
- \- *lemma* local_triv_trans
- \- *lemma* local_triv_at_ext_def
- \- *lemma* local_triv_coe
- \- *lemma* local_triv_source
- \- *lemma* local_triv_target
- \- *lemma* local_triv_symm
- \- *lemma* local_triv_ext_apply
- \- *lemma* local_triv_ext_symm_apply
- \- *lemma* mem_local_triv_ext_source
- \- *lemma* mem_local_triv_ext_target
- \- *lemma* local_triv_ext_symm_fst
- \- *lemma* mem_local_triv_at_ext_base_set
- \+ *def* local_triv_as_local_equiv
- \+/\- *def* local_triv
- \+ *def* local_triv_at
- \- *def* total_space
- \- *def* proj
- \- *def* total_space_mk
- \- *def* trivial
- \- *def* trivial.proj_snd
- \- *def* local_triv'
- \- *def* local_triv_ext
- \- *def* local_triv_at_ext

Modified src/topology/vector_bundle.lean




## [2021-07-09 12:52:46](https://github.com/leanprover-community/mathlib/commit/abde210)
feat(analysis/complex/isometry): restate result more abstractly ([#7908](https://github.com/leanprover-community/mathlib/pull/7908))
Define `rotation` as a group homomorphism from the circle to the isometry group of `ℂ`.  State the classification of isometries of `ℂ` more abstractly, using this construction.  Also golf some proofs.
#### Estimated changes
Modified src/analysis/complex/isometry.lean
- \+ *lemma* rotation_apply
- \+/\- *lemma* linear_isometry_complex_aux
- \+/\- *lemma* linear_isometry_complex
- \- *lemma* linear_isometry.abs_apply_sub_one_eq_abs_sub_one
- \+ *def* rotation_aux
- \+ *def* rotation

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* coe_to_continuous_linear_equiv
- \+ *def* to_continuous_linear_equiv



## [2021-07-09 09:42:47](https://github.com/leanprover-community/mathlib/commit/1134865)
feat(category_theory/limits): finite products from finite limits ([#8236](https://github.com/leanprover-community/mathlib/pull/8236))
Adds instances for finite products from finite limits.
#### Estimated changes
Modified src/category_theory/limits/shapes/finite_products.lean
- \- *lemma* has_finite_products_of_has_finite_limits
- \- *lemma* has_finite_coproducts_of_has_finite_colimits



## [2021-07-08 23:05:26](https://github.com/leanprover-community/mathlib/commit/e46447b)
feat(measure_theory/measure_space): prob_le_one ([#7913](https://github.com/leanprover-community/mathlib/pull/7913))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* prob_add_prob_compl
- \+ *lemma* prob_le_one



## [2021-07-08 18:57:18](https://github.com/leanprover-community/mathlib/commit/9d40a59)
feat(group_theory,linear_algebra): third isomorphism theorem for groups and modules ([#8203](https://github.com/leanprover-community/mathlib/pull/8203))
This PR proves the third isomorphism theorem for (additive) groups and modules, and also adds a few `simp` lemmas that I needed.
#### Estimated changes
Modified docs/overview.yaml


Modified src/group_theory/quotient_group.lean
- \+ *lemma* map_coe
- \+ *lemma* map_mk'
- \+ *lemma* quotient_quotient_equiv_quotient_aux_coe
- \+ *lemma* quotient_quotient_equiv_quotient_aux_coe_coe
- \+ *def* quotient_quotient_equiv_quotient_aux
- \+ *def* quotient_quotient_equiv_quotient

Modified src/linear_algebra/basic.lean
- \+ *lemma* quotient_quotient_equiv_quotient_aux_mk
- \+ *lemma* quotient_quotient_equiv_quotient_aux_mk_mk
- \+ *def* quotient_quotient_equiv_quotient_aux
- \+ *def* quotient_quotient_equiv_quotient



## [2021-07-08 17:14:02](https://github.com/leanprover-community/mathlib/commit/a7b660e)
feat(linear_algebra/prod): add coprod_map_prod ([#8220](https://github.com/leanprover-community/mathlib/pull/8220))
This also adds `submodule.coe_sup` and `set.mem_finset_prod`. The latter was intended to be used to show `submodule.coe_supr`, but I didn't really need that and it was hard to prove.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* mem_finset_prod
- \+ *lemma* mem_fintype_prod
- \+ *lemma* finset_prod_mem_finset_prod
- \+ *lemma* finset_prod_subset_finset_prod

Modified src/linear_algebra/basic.lean
- \+ *lemma* coe_sup

Modified src/linear_algebra/prod.lean
- \+ *lemma* coprod_map_prod



## [2021-07-08 16:41:12](https://github.com/leanprover-community/mathlib/commit/13486fe)
chore(measure_theory/measure_space): untangle `probability_measure`, `finite_measure`, and `has_no_atoms` ([#8222](https://github.com/leanprover-community/mathlib/pull/8222))
This only moves existing lemmas around. Putting all the instance together up front seems to result in lemmas being added in adhoc places - by adding `section`s, this should guide future contributions.
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* measure.restrict_singleton'



## [2021-07-08 14:46:44](https://github.com/leanprover-community/mathlib/commit/b10062e)
feat(data/finset/noncomm_prod): noncomm_prod_union_of_disjoint ([#8169](https://github.com/leanprover-community/mathlib/pull/8169))
#### Estimated changes
Modified src/data/finset/noncomm_prod.lean
- \+ *lemma* noncomm_prod_union_of_disjoint



## [2021-07-08 13:06:54](https://github.com/leanprover-community/mathlib/commit/a4b0b48)
feat(data/nat/basic): lt_one_iff ([#8224](https://github.com/leanprover-community/mathlib/pull/8224))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* lt_one_iff



## [2021-07-08 11:22:43](https://github.com/leanprover-community/mathlib/commit/fb22ae3)
refactor(order/rel_iso): move statements about intervals to data/set/intervals ([#8150](https://github.com/leanprover-community/mathlib/pull/8150))
This means that we can talk about `rel_iso` without needing to transitively import `ordered_group`s
This PR takes advantage of this to define `order_iso.mul_(left|right)[']` to mirror `equiv.mul_(left|right)[']`.
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *def* order_iso.mul_left'
- \+ *def* order_iso.mul_right'

Modified src/algebra/ordered_group.lean
- \+ *def* order_iso.mul_right
- \+ *def* order_iso.mul_left

Modified src/data/set/intervals/basic.lean
- \+ *lemma* preimage_Iic
- \+ *lemma* preimage_Ici
- \+ *lemma* preimage_Iio
- \+ *lemma* preimage_Ioi
- \+ *lemma* preimage_Icc
- \+ *lemma* preimage_Ico
- \+ *lemma* preimage_Ioc
- \+ *lemma* preimage_Ioo
- \+ *def* Iic_top
- \+ *def* Ici_bot

Modified src/order/rel_iso.lean
- \- *lemma* preimage_Iic
- \- *lemma* preimage_Ici
- \- *lemma* preimage_Iio
- \- *lemma* preimage_Ioi
- \- *lemma* preimage_Icc
- \- *lemma* preimage_Ico
- \- *lemma* preimage_Ioc
- \- *lemma* preimage_Ioo
- \- *def* order_iso.Iic_top
- \- *def* order_iso.Ici_bot



## [2021-07-08 09:27:54](https://github.com/leanprover-community/mathlib/commit/03e2cbd)
chore(group_theory/perm/support): support_pow_le over nat ([#8225](https://github.com/leanprover-community/mathlib/pull/8225))
Previously, both `support_pow_le` and `support_gpow_le` had the
power as an `int`. Now we properly differentiate the two and avoid
slow defeq checks.
#### Estimated changes
Modified src/group_theory/perm/cycles.lean
- \+ *lemma* is_cycle_of_is_cycle_gpow
- \- *lemma* is_cycle_of_is_cycle_pow

Modified src/group_theory/perm/support.lean
- \+/\- *lemma* support_pow_le



## [2021-07-08 02:02:10](https://github.com/leanprover-community/mathlib/commit/0ee238c)
chore(scripts): update nolints.txt ([#8227](https://github.com/leanprover-community/mathlib/pull/8227))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-07-07 20:50:25](https://github.com/leanprover-community/mathlib/commit/70aef28)
feat(group_theory/perm/list): concrete permutations from a list ([#7451](https://github.com/leanprover-community/mathlib/pull/7451))
#### Estimated changes
Created src/group_theory/perm/list.lean
- \+ *lemma* form_perm_nil
- \+ *lemma* form_perm_singleton
- \+ *lemma* form_perm_cons_cons
- \+ *lemma* form_perm_pair
- \+ *lemma* form_perm_apply_of_not_mem
- \+ *lemma* form_perm_apply_mem_of_mem
- \+ *lemma* form_perm_cons_concat_apply_last
- \+ *lemma* form_perm_apply_last
- \+ *lemma* form_perm_apply_nth_le_length
- \+ *lemma* form_perm_apply_head
- \+ *lemma* form_perm_apply_nth_le_zero
- \+ *lemma* form_perm_eq_head_iff_eq_last
- \+ *lemma* zip_with_swap_prod_support'
- \+ *lemma* zip_with_swap_prod_support
- \+ *lemma* support_form_perm_le'
- \+ *lemma* support_form_perm_le
- \+ *lemma* form_perm_apply_lt
- \+ *lemma* form_perm_apply_nth_le
- \+ *lemma* support_form_perm_of_nodup'
- \+ *lemma* support_form_perm_of_nodup
- \+ *lemma* form_perm_rotate_one
- \+ *lemma* form_perm_rotate
- \+ *lemma* form_perm_eq_of_is_rotated
- \+ *lemma* form_perm_reverse
- \+ *lemma* form_perm_pow_apply_nth_le
- \+ *lemma* form_perm_ext_iff
- \+ *def* form_perm



## [2021-07-07 17:46:10](https://github.com/leanprover-community/mathlib/commit/5f2358c)
fix(data/complex/basic): ensure `algebra ℝ ℂ` is computable ([#8166](https://github.com/leanprover-community/mathlib/pull/8166))
Without this `complex.ring` instance, `ring ℂ` is found via `division_ring.to_ring` and `field.to_division_ring`, and `complex.field` is non-computable.
The non-computable-ness previously contaminated `distrib_mul_action R ℂ` and even some properties of `finset.sum` on complex numbers! To avoid this type of mistake again, we remove `noncomputable theory` and manually flag the parts we actually expect to be computable.
#### Estimated changes
Modified src/data/complex/basic.lean


Modified src/data/complex/module.lean
- \+ *def* lift
- \- *def* basis_one_I



## [2021-07-07 15:54:45](https://github.com/leanprover-community/mathlib/commit/e0ca853)
feat(algebra/group/units): teach `simps` about `units` ([#8204](https://github.com/leanprover-community/mathlib/pull/8204))
This also introduces `units.copy` to match `invertible.copy`, and uses it to make some lemmas in normed_space/units true by `rfl` (and generated by `simps`).
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* copy_eq
- \+ *def* simps.coe
- \+ *def* simps.coe_inv
- \+ *def* copy

Modified src/algebra/invertible.lean
- \- *lemma* unit_of_invertible_val
- \- *lemma* unit_of_invertible_inv

Modified src/algebra/lie/classical.lean


Modified src/analysis/normed_space/units.lean
- \- *lemma* one_sub_coe
- \- *lemma* add_coe
- \- *lemma* unit_of_nearby_coe



## [2021-07-07 15:54:44](https://github.com/leanprover-community/mathlib/commit/ce3d53b)
fix(data/real/basic): provide a computable `module` instance ([#8164](https://github.com/leanprover-community/mathlib/pull/8164))
Without this instance, `normed_field.to_normed_space` and `normed_space.to_module` is tried first, but this results in a noncomputable instance.
#### Estimated changes
Modified src/data/real/basic.lean


Modified src/geometry/manifold/instances/real.lean




## [2021-07-07 15:11:09](https://github.com/leanprover-community/mathlib/commit/05e8ed2)
chore(feat/algebra/lie/from_cartan_matrix): rename file ([#8219](https://github.com/leanprover-community/mathlib/pull/8219))
#### Estimated changes
Renamed src/algebra/lie/from_cartan_matrix.lean to src/algebra/lie/cartan_matrix.lean




## [2021-07-07 15:11:08](https://github.com/leanprover-community/mathlib/commit/836c549)
docs(category_theory/limits/shapes/products): add module docstring ([#8212](https://github.com/leanprover-community/mathlib/pull/8212))
Also resolves some TODOs.
#### Estimated changes
Modified src/category_theory/limits/shapes/products.lean




## [2021-07-07 14:30:42](https://github.com/leanprover-community/mathlib/commit/5145261)
feat(data/fintype/list): induced fintype on nodup lists ([#8171](https://github.com/leanprover-community/mathlib/pull/8171))
#### Estimated changes
Created src/data/fintype/list.lean
- \+ *lemma* lists_coe
- \+ *lemma* mem_lists_iff
- \+ *def* lists

Modified src/data/list/cycle.lean
- \+ *lemma* nontrivial_coe_nodup_iff
- \+ *lemma* nodup.nontrivial_iff
- \+ *def* decidable_nontrivial_coe



## [2021-07-07 13:35:19](https://github.com/leanprover-community/mathlib/commit/5796783)
chore(category_theory): homogenise usage of notation for terminal objects ([#8106](https://github.com/leanprover-community/mathlib/pull/8106))
I went with the option that is used more frequently, but I'm also happy to switch to the space-less option if people prefer it.
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean
- \+/\- *def* exp_terminal_iso_self
- \+/\- *def* internalize_hom

Modified src/category_theory/limits/shapes/terminal.lean




## [2021-07-07 12:02:07](https://github.com/leanprover-community/mathlib/commit/bb5ab1e)
chore(measure_theory/measure_space): add missing `finite_measure` instances ([#8214](https://github.com/leanprover-community/mathlib/pull/8214))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *theorem* coe_nnreal_smul



## [2021-07-07 12:02:05](https://github.com/leanprover-community/mathlib/commit/41ec92e)
feat(algebra/lie/from_cartan_matrix): construction of a Lie algebra from a Cartan matrix ([#8206](https://github.com/leanprover-community/mathlib/pull/8206))
#### Estimated changes
Modified docs/references.bib


Created src/algebra/lie/from_cartan_matrix.lean
- \+ *def* HH
- \+ *def* EF
- \+ *def* HE
- \+ *def* HF
- \+ *def* ad_E
- \+ *def* ad_F
- \+ *def* to_set
- \+ *def* to_ideal
- \+ *def* matrix.to_lie_algebra



## [2021-07-07 12:02:02](https://github.com/leanprover-community/mathlib/commit/126a7b6)
feat(data/multiset/basic): add_eq_union_iff_disjoint ([#8173](https://github.com/leanprover-community/mathlib/pull/8173))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* add_eq_union_iff_disjoint

Modified src/data/nat/basic.lean
- \+ *lemma* min_eq_zero_iff
- \+ *lemma* max_eq_zero_iff
- \+ *lemma* add_eq_max_iff
- \+ *lemma* add_eq_min_iff



## [2021-07-07 10:24:57](https://github.com/leanprover-community/mathlib/commit/29beb1f)
feat(analysis/normed_space/int): norms of (units of) integers ([#8136](https://github.com/leanprover-community/mathlib/pull/8136))
From LTE
#### Estimated changes
Created src/analysis/normed_space/int.lean
- \+ *lemma* nnnorm_coe_units
- \+ *lemma* norm_coe_units
- \+ *lemma* nnnorm_coe_nat
- \+ *lemma* norm_coe_nat
- \+ *lemma* to_nat_add_to_nat_neg_eq_nnnorm
- \+ *lemma* to_nat_add_to_nat_neg_eq_norm

Modified src/data/fintype/basic.lean
- \+ *lemma* units_int.univ

Modified src/data/int/basic.lean
- \+ *lemma* to_nat_sub_to_nat_neg
- \+ *lemma* to_nat_add_to_nat_neg_eq_nat_abs



## [2021-07-07 10:24:56](https://github.com/leanprover-community/mathlib/commit/89e1837)
fix(tactic/core): add subst' ([#8129](https://github.com/leanprover-community/mathlib/pull/8129))
`tactic.subst'` gives a better error message when the substituted variable is a local definition.
It is hard to fix this in core (without touching C++ code), since `tactic.is_local_def` is in mathlib
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified src/tactic/rcases.lean


Modified test/lift.lean




## [2021-07-07 10:24:54](https://github.com/leanprover-community/mathlib/commit/47c7c01)
feat(measure_theory/measure_space): if `f` restricted to `s` is measurable, then `f` is `ae_measurable` wrt `μ.restrict s` ([#8098](https://github.com/leanprover-community/mathlib/pull/8098))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* ae_measurable_restrict_of_measurable_subtype



## [2021-07-07 08:47:55](https://github.com/leanprover-community/mathlib/commit/06f0d51)
refactor(algebra/ordered_group): another step in the `order` refactor -- ordered groups ([#8060](https://github.com/leanprover-community/mathlib/pull/8060))
This PR represents another wave of generalization of proofs, following from the `order` refactor.  It is another step towards [#7645](https://github.com/leanprover-community/mathlib/pull/7645).
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* left.inv_le_one_iff
- \+ *lemma* left.one_le_inv_iff
- \+/\- *lemma* le_inv_mul_iff_mul_le
- \+/\- *lemma* inv_mul_le_iff_le_mul
- \+/\- *lemma* inv_le_iff_one_le_mul'
- \+ *lemma* le_inv_iff_mul_le_one_left
- \+ *lemma* le_inv_mul_iff_le
- \+ *lemma* inv_mul_le_one_iff
- \+ *lemma* left.one_lt_inv_iff
- \+ *lemma* left.inv_lt_one_iff
- \+/\- *lemma* lt_inv_mul_iff_mul_lt
- \+/\- *lemma* inv_mul_lt_iff_lt_mul
- \+/\- *lemma* inv_lt_iff_one_lt_mul'
- \+/\- *lemma* lt_inv_iff_mul_lt_one'
- \+ *lemma* lt_inv_mul_iff_lt
- \+ *lemma* inv_mul_lt_one_iff
- \+ *lemma* right.inv_le_one_iff
- \+ *lemma* right.one_le_inv_iff
- \+/\- *lemma* inv_le_iff_one_le_mul
- \+ *lemma* le_inv_iff_mul_le_one_right
- \+/\- *lemma* mul_inv_le_iff_le_mul
- \+ *lemma* le_mul_inv_iff_mul_le
- \+ *lemma* mul_inv_le_one_iff_le
- \+ *lemma* le_mul_inv_iff_le
- \+ *lemma* mul_inv_le_one_iff
- \+ *lemma* right.inv_lt_one_iff
- \+ *lemma* right.one_lt_inv_iff
- \+/\- *lemma* inv_lt_iff_one_lt_mul
- \+/\- *lemma* lt_inv_iff_mul_lt_one
- \+ *lemma* mul_inv_lt_iff_lt_mul
- \+ *lemma* lt_mul_inv_iff_mul_lt
- \+ *lemma* inv_mul_lt_one_iff_lt
- \+ *lemma* lt_mul_inv_iff_lt
- \+ *lemma* mul_inv_lt_one_iff
- \+/\- *lemma* inv_le_of_inv_le
- \+ *lemma* mul_inv_le_inv_mul_iff
- \+/\- *lemma* div_le_self_iff
- \+/\- *lemma* inv_lt_inv_iff
- \+/\- *lemma* lt_inv_of_lt_inv
- \+/\- *lemma* inv_lt_of_inv_lt
- \+/\- *lemma* inv_lt'
- \+/\- *lemma* lt_inv'
- \+ *lemma* mul_inv_lt_inv_mul_iff
- \+/\- *lemma* div_lt_self_iff
- \+ *lemma* left.inv_le_self
- \+ *lemma* left.self_le_inv
- \+ *lemma* left.inv_lt_self
- \+ *lemma* left.self_lt_inv
- \+ *lemma* right.inv_le_self
- \+ *lemma* right.self_le_inv
- \+ *lemma* right.inv_lt_self
- \+ *lemma* right.self_lt_inv
- \+/\- *lemma* mul_inv_le_iff_le_mul'
- \+/\- *lemma* mul_inv_le_mul_inv_iff'
- \+ *lemma* inv_mul_lt_iff_lt_mul'
- \+ *lemma* mul_inv_lt_iff_le_mul'
- \+ *lemma* mul_inv_lt_mul_inv_iff'
- \+ *lemma* div_le_div_iff_right
- \+ *lemma* div_le_div_right'
- \+ *lemma* one_le_div'
- \+ *lemma* div_le_one'
- \+ *lemma* le_div_iff_mul_le
- \+ *lemma* div_le_iff_le_mul
- \+ *lemma* div_le_div_iff_left
- \+ *lemma* div_le_div_left'
- \+ *lemma* div_le_div_iff'
- \+ *lemma* le_div_iff_mul_le'
- \+ *lemma* div_le_iff_le_mul'
- \+ *lemma* inv_le_div_iff_le_mul
- \+ *lemma* inv_le_div_iff_le_mul'
- \+ *lemma* div_le''
- \+ *lemma* le_div''
- \+ *lemma* div_le_div''
- \+ *lemma* div_lt_div_iff_right
- \+ *lemma* div_lt_div_right'
- \+ *lemma* one_lt_div'
- \+ *lemma* div_lt_one'
- \+ *lemma* lt_div_iff_mul_lt
- \+ *lemma* div_lt_iff_lt_mul
- \+ *lemma* div_lt_div_iff_left
- \+ *lemma* inv_lt_div_iff_lt_mul
- \+ *lemma* div_lt_div_left'
- \+ *lemma* div_lt_div_iff'
- \+ *lemma* lt_div_iff_mul_lt'
- \+ *lemma* div_lt_iff_lt_mul'
- \+ *lemma* inv_lt_div_iff_lt_mul'
- \+ *lemma* div_lt''
- \+ *lemma* lt_div''
- \+ *lemma* div_lt_div''
- \+ *lemma* le_of_forall_one_lt_lt_mul
- \+ *lemma* le_iff_forall_one_lt_lt_mul
- \+ *lemma* div_le_inv_mul_iff
- \+ *lemma* div_le_div_flip
- \+ *lemma* max_one_div_max_inv_one_eq_self
- \+ *lemma* le_of_forall_one_lt_le_mul
- \+ *lemma* le_iff_forall_one_lt_le_mul
- \+/\- *lemma* abs_choice
- \+/\- *lemma* abs_le'
- \+/\- *lemma* le_abs
- \+/\- *lemma* le_abs_self
- \+/\- *lemma* neg_le_abs_self
- \+/\- *lemma* lt_abs
- \+/\- *lemma* abs_by_cases
- \+/\- *lemma* abs_neg
- \+/\- *lemma* eq_or_eq_neg_of_abs_eq
- \+/\- *lemma* abs_eq_abs
- \+/\- *lemma* abs_sub_comm
- \+/\- *lemma* abs_le
- \+/\- *lemma* neg_le_of_abs_le
- \+/\- *lemma* le_of_abs_le
- \+/\- *lemma* abs_max_sub_max_le_abs
- \+/\- *lemma* inv_le_inv'
- \+/\- *lemma* inv_lt_inv'
- \+/\- *lemma* inv_le_one_of_one_le
- \+/\- *lemma* one_le_inv_of_le_one
- \- *lemma* le_of_inv_le_inv
- \- *lemma* one_le_of_inv_le_one
- \- *lemma* le_one_of_one_le_inv
- \- *lemma* lt_of_inv_lt_inv
- \- *lemma* one_lt_of_inv_inv
- \- *lemma* inv_inv_of_one_lt
- \- *lemma* inv_of_one_lt_inv
- \- *lemma* one_lt_inv_of_inv
- \- *lemma* le_inv_of_le_inv
- \- *lemma* mul_le_of_le_inv_mul
- \- *lemma* le_inv_mul_of_mul_le
- \- *lemma* le_mul_of_inv_mul_le
- \- *lemma* inv_mul_le_of_le_mul
- \- *lemma* le_mul_of_inv_mul_le_left
- \- *lemma* inv_mul_le_left_of_le_mul
- \- *lemma* le_mul_of_inv_mul_le_right
- \- *lemma* inv_mul_le_right_of_le_mul
- \- *lemma* mul_lt_of_lt_inv_mul
- \- *lemma* lt_inv_mul_of_mul_lt
- \- *lemma* lt_mul_of_inv_mul_lt
- \- *lemma* inv_mul_lt_of_lt_mul
- \- *lemma* lt_mul_of_inv_mul_lt_left
- \- *lemma* inv_mul_lt_left_of_lt_mul
- \- *lemma* lt_mul_of_inv_mul_lt_right
- \- *lemma* inv_mul_lt_right_of_lt_mul
- \- *lemma* inv_lt_one_iff_one_lt
- \- *lemma* le_inv_iff_mul_le_one
- \- *lemma* le_inv_iff_mul_le_one'
- \- *lemma* inv_le_one'
- \- *lemma* one_le_inv'
- \- *lemma* inv_le_self
- \- *lemma* self_le_inv
- \- *lemma* inv_lt_one'
- \- *lemma* one_lt_inv'
- \- *lemma* inv_lt_self
- \- *lemma* inv_mul_lt_iff_lt_mul_right
- \- *lemma* sub_le_sub
- \- *lemma* sub_lt_sub
- \- *lemma* sub_le_sub_iff
- \- *lemma* sub_le_sub_iff_left
- \- *lemma* sub_le_sub_left
- \- *lemma* sub_le_sub_iff_right
- \- *lemma* sub_le_sub_right
- \- *lemma* sub_lt_sub_iff_left
- \- *lemma* sub_lt_sub_left
- \- *lemma* sub_lt_sub_iff_right
- \- *lemma* sub_lt_sub_right
- \- *lemma* sub_nonneg
- \- *lemma* sub_nonpos
- \- *lemma* sub_pos
- \- *lemma* sub_lt_zero
- \- *lemma* le_sub_iff_add_le'
- \- *lemma* le_sub_iff_add_le
- \- *lemma* sub_le_iff_le_add'
- \- *lemma* sub_le_iff_le_add
- \- *lemma* neg_le_sub_iff_le_add
- \- *lemma* neg_le_sub_iff_le_add'
- \- *lemma* sub_le
- \- *lemma* lt_sub_iff_add_lt'
- \- *lemma* lt_sub_iff_add_lt
- \- *lemma* sub_lt_iff_lt_add'
- \- *lemma* sub_lt_iff_lt_add
- \- *lemma* neg_lt_sub_iff_lt_add
- \- *lemma* neg_lt_sub_iff_lt_add'
- \- *lemma* sub_lt
- \- *lemma* max_one_div_eq_self'
- \- *lemma* sub_le_sub_flip
- \- *lemma* max_zero_sub_max_neg_zero_eq_self
- \- *lemma* le_of_forall_pos_le_add
- \- *lemma* le_iff_forall_pos_le_add
- \- *lemma* le_of_forall_pos_lt_add
- \- *lemma* le_iff_forall_pos_lt_add
- \+/\- *theorem* abs_le_abs
- \+ *theorem* inv_lt_one_of_one_lt
- \- *theorem* le_sub
- \- *theorem* lt_sub
- \+/\- *def* function.injective.ordered_comm_group
- \+/\- *def* abs

Modified src/analysis/analytic/basic.lean


Modified src/topology/algebra/ordered/basic.lean




## [2021-07-07 02:20:39](https://github.com/leanprover-community/mathlib/commit/20d8e83)
chore(scripts): update nolints.txt ([#8217](https://github.com/leanprover-community/mathlib/pull/8217))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-07-06 18:26:45](https://github.com/leanprover-community/mathlib/commit/d7653b8)
chore(category_theory/monad/algebra): lint and golf ([#8160](https://github.com/leanprover-community/mathlib/pull/8160))
Adds a module docstring and golfs some proofs, including removing `erw`.
#### Estimated changes
Modified src/category_theory/monad/algebra.lean
- \+/\- *def* iso_mk

Modified src/category_theory/monad/limits.lean
- \+/\- *def* γ
- \+/\- *def* new_cone



## [2021-07-06 16:15:28](https://github.com/leanprover-community/mathlib/commit/03c8904)
doc(data/set/function): add set. prefixes for doc-gen ([#8215](https://github.com/leanprover-community/mathlib/pull/8215))
This means these names will be linked.
#### Estimated changes
Modified src/data/set/function.lean




## [2021-07-06 14:26:27](https://github.com/leanprover-community/mathlib/commit/ec07293)
doc(*): add bold in doc strings for named theorems i.e. **mean value theorem** ([#8182](https://github.com/leanprover-community/mathlib/pull/8182))
#### Estimated changes
Modified archive/100-theorems-list/16_abel_ruffini.lean


Modified archive/100-theorems-list/42_inverse_triangle_sum.lean


Modified archive/100-theorems-list/57_herons_formula.lean


Modified archive/100-theorems-list/70_perfect_numbers.lean


Modified archive/100-theorems-list/73_ascending_descending_sequences.lean


Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified archive/100-theorems-list/93_birthday_problem.lean


Modified archive/100-theorems-list/9_area_of_a_circle.lean


Modified archive/arithcc.lean


Modified archive/sensitivity.lean


Modified counterexamples/girard.lean


Modified docs/100.yaml


Modified src/algebra/euclidean_domain.lean


Modified src/algebra/ordered_group.lean


Modified src/analysis/calculus/lhopital.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/inner_product.lean


Modified src/analysis/normed_space/mazur_ulam.lean


Modified src/analysis/p_series.lean


Modified src/analysis/specific_limits.lean


Modified src/category_theory/preadditive/schur.lean


Modified src/combinatorics/hall.lean


Modified src/combinatorics/simple_graph/matching.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/finset/powerset.lean


Modified src/data/int/gcd.lean


Modified src/data/nat/choose/sum.lean


Modified src/data/nat/digits.lean


Modified src/data/nat/prime.lean


Modified src/data/rat/denumerable.lean


Modified src/data/real/cardinality.lean


Modified src/data/real/irrational.lean


Modified src/data/real/pi.lean


Modified src/field_theory/abel_ruffini.lean


Modified src/field_theory/finite/basic.lean


Modified src/field_theory/primitive_element.lean


Modified src/geometry/euclidean/sphere.lean


Modified src/geometry/euclidean/triangle.lean


Modified src/group_theory/coset.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/char_poly/basic.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean


Modified src/logic/function/basic.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/interval_integral.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/pi_system.lean


Modified src/measure_theory/prod.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/liouville/basic.lean


Modified src/number_theory/pell.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/number_theory/sum_two_squares.lean


Modified src/order/fixed_points.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/simple_module.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/schroeder_bernstein.lean


Modified src/topology/algebra/ordered/basic.lean




## [2021-07-06 13:47:12](https://github.com/leanprover-community/mathlib/commit/1399997)
feat(category_theory/closed): Exponential ideals ([#4930](https://github.com/leanprover-community/mathlib/pull/4930))
Define exponential ideals.
#### Estimated changes
Created src/category_theory/closed/ideal.lean
- \+ *lemma* exponential_ideal.mk'
- \+ *lemma* exponential_ideal.mk_of_iso
- \+ *lemma* reflective_products
- \+ *lemma* bijection_symm_apply_id
- \+ *lemma* bijection_natural
- \+ *lemma* prod_comparison_iso
- \+ *def* exponential_ideal_reflective
- \+ *def* cartesian_closed_of_reflective



## [2021-07-06 11:32:50](https://github.com/leanprover-community/mathlib/commit/98e8408)
feat(geometry/manifold/algebra): `left_invariant_derivation` ([#8108](https://github.com/leanprover-community/mathlib/pull/8108))
In this PR we prove that left-invariant derivations are a Lie algebra.
#### Estimated changes
Created src/geometry/manifold/algebra/left_invariant_derivation.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_to_linear_map
- \+ *lemma* to_derivation_eq_coe
- \+ *lemma* coe_injective
- \+ *lemma* coe_derivation
- \+ *lemma* coe_derivation_injective
- \+ *lemma* left_invariant'
- \+ *lemma* map_add
- \+ *lemma* map_zero
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* map_smul
- \+ *lemma* leibniz
- \+ *lemma* coe_add
- \+ *lemma* coe_zero
- \+ *lemma* coe_neg
- \+ *lemma* coe_sub
- \+ *lemma* lift_add
- \+ *lemma* lift_zero
- \+ *lemma* coe_smul
- \+ *lemma* lift_smul
- \+ *lemma* eval_at_apply
- \+ *lemma* eval_at_coe
- \+ *lemma* left_invariant
- \+ *lemma* eval_at_mul
- \+ *lemma* comp_L
- \+ *lemma* commutator_coe_derivation
- \+ *lemma* commutator_apply
- \+ *theorem* ext
- \+ *def* coe_fn_add_monoid_hom
- \+ *def* eval_at

Modified src/geometry/manifold/algebra/monoid.lean
- \+ *lemma* smooth_left_mul_one
- \+ *lemma* smooth_right_mul_one

Modified src/geometry/manifold/derivation_bundle.lean
- \+/\- *lemma* apply_fdifferential
- \+ *lemma* apply_hfdifferential
- \+ *def* hfdifferential
- \+/\- *def* fdifferential
- \- *def* fdifferential_map

Modified src/ring_theory/derivation.lean
- \+ *lemma* congr_fun



## [2021-07-06 10:58:03](https://github.com/leanprover-community/mathlib/commit/23d22e4)
feat(category_theory/abelian/ext): Defines Ext functors. ([#8186](https://github.com/leanprover-community/mathlib/pull/8186))
See my comment from [#7525](https://github.com/leanprover-community/mathlib/pull/7525)
#### Estimated changes
Created src/category_theory/abelian/ext.lean
- \+ *def* Ext
- \+ *def* Ext_succ_of_projective



## [2021-07-06 08:21:53](https://github.com/leanprover-community/mathlib/commit/2f72023)
chore(measure_theory/decomposition): change statement to use the `finite_measure` instance ([#8207](https://github.com/leanprover-community/mathlib/pull/8207))
#### Estimated changes
Modified src/measure_theory/decomposition.lean
- \+/\- *lemma* hahn_decomposition



## [2021-07-06 05:05:33](https://github.com/leanprover-community/mathlib/commit/6365c6c)
feat(algebra/invertible): construction from is_unit ([#8205](https://github.com/leanprover-community/mathlib/pull/8205))
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *lemma* is_unit.nonempty_invertible
- \+ *lemma* nonempty_invertible_iff_is_unit
- \+/\- *def* invertible.copy



## [2021-07-06 02:10:44](https://github.com/leanprover-community/mathlib/commit/27841bb)
chore(scripts): update nolints.txt ([#8208](https://github.com/leanprover-community/mathlib/pull/8208))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-07-05 17:24:46](https://github.com/leanprover-community/mathlib/commit/77e1e3b)
feat(linear_algebra/nonsingular_inverse): add lemmas about `invertible` ([#8201](https://github.com/leanprover-community/mathlib/pull/8201))
#### Estimated changes
Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* unit_of_det_invertible_eq_nonsing_inv_unit
- \+ *def* invertible_of_det_invertible
- \+ *def* det_invertible_of_left_inverse
- \+ *def* det_invertible_of_right_inverse
- \+ *def* det_invertible_of_invertible
- \+ *def* unit_of_det_invertible



## [2021-07-05 17:24:45](https://github.com/leanprover-community/mathlib/commit/9d99833)
feat(category_theory/linear/yoneda): A linear version of Yoneda. ([#8199](https://github.com/leanprover-community/mathlib/pull/8199))
#### Estimated changes
Created src/category_theory/linear/yoneda.lean
- \+ *def* linear_yoneda



## [2021-07-05 17:24:44](https://github.com/leanprover-community/mathlib/commit/b6bf7a3)
feat(measure_theory/lp_space): define the Lp function corresponding to the indicator of a set ([#8193](https://github.com/leanprover-community/mathlib/pull/8193))
I also moved some measurability lemmas from the integrable_on file to measure_space. I needed them and lp_space is before integrable_on in the import graph.
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* comp_mul_indicator_const

Modified src/measure_theory/integrable_on.lean
- \+ *lemma* integrable_indicator_const_Lp
- \- *lemma* piecewise_ae_eq_restrict
- \- *lemma* piecewise_ae_eq_restrict_compl
- \- *lemma* indicator_ae_eq_restrict
- \- *lemma* indicator_ae_eq_restrict_compl
- \- *lemma* ae_measurable_indicator_iff
- \- *lemma* ae_measurable.restrict
- \- *lemma* ae_measurable.indicator

Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_ess_sup_indicator_le
- \+ *lemma* snorm_ess_sup_indicator_const_le
- \+ *lemma* snorm_ess_sup_indicator_const_eq
- \+ *lemma* snorm_indicator_const
- \+ *lemma* snorm_indicator_const'
- \+ *lemma* mem_ℒp_indicator_const
- \+ *lemma* indicator_const_Lp_coe_fn
- \+ *lemma* indicator_const_Lp_coe_fn_mem
- \+ *lemma* indicator_const_Lp_coe_fn_nmem
- \+ *lemma* norm_indicator_const_Lp
- \+ *lemma* norm_indicator_const_Lp_top
- \+ *lemma* norm_indicator_const_Lp'
- \+ *lemma* indicator_const_Lp_disjoint_union
- \+ *def* indicator_const_Lp

Modified src/measure_theory/measure_space.lean
- \+ *lemma* piecewise_ae_eq_restrict
- \+ *lemma* piecewise_ae_eq_restrict_compl
- \+ *lemma* ae_measurable.restrict
- \+ *lemma* indicator_ae_eq_restrict
- \+ *lemma* indicator_ae_eq_restrict_compl
- \+ *lemma* ae_measurable_indicator_iff
- \+ *lemma* ae_measurable.indicator



## [2021-07-05 17:24:43](https://github.com/leanprover-community/mathlib/commit/7eab080)
feat(topology/instances/ennreal): add tsum lemmas for ennreal.to_real ([#8184](https://github.com/leanprover-community/mathlib/pull/8184))
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *lemma* tsum_coe_ne_top_iff_summable_coe
- \+ *lemma* tsum_coe_eq_top_iff_not_summable_coe
- \+ *lemma* tsum_to_real_eq



## [2021-07-05 15:47:16](https://github.com/leanprover-community/mathlib/commit/38a6f26)
feat(algebra/to_additive): map pow to smul ([#7888](https://github.com/leanprover-community/mathlib/pull/7888))
* Allows `@[to_additive]` to reorder consecutive arguments of specified identifiers.
* This can be specified with the attribute `@[to_additive_reorder n m ...]` to swap arguments `n` and `n+1`, arguments `m` and `m+1` etc. (start counting from 1).
* The only two attributes currently in use are:
```lean
attribute [to_additive_reorder 1] has_pow
attribute [to_additive_reorder 1 4] has_pow.pow
```
* It will  eta-expand all expressions that have as head a declaration with attribute `to_additive_reorder` until they have the required number of arguments. This is required to correctly deal with partially applied terms.
* Hack: if the first two arguments are reordered, then the first two universe variables are also reordered (this happens to be the correct behavior for `has_pow` and `has_pow.pow`). It might be cleaner to have a separate attribute for that, but that given the low amount of times that I expect that we use `to_additive_reorder`, this seems unnecessary.
* This PR also allows the user to write `@[to_additive?]` to trace the generated declaration.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* prod_const_one
- \- *lemma* sum_const_zero
- \- *lemma* sum_multiset_count

Modified src/algebra/big_operators/ring.lean
- \- *lemma* sum_powerset

Modified src/algebra/group/to_additive.lean


Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* npow_eq_pow
- \+/\- *lemma* gpow_eq_pow
- \+/\- *lemma* pow_right
- \- *lemma* nsmul_eq_smul
- \- *lemma* gsmul_eq_smul
- \+/\- *theorem* pow_right
- \+/\- *theorem* pow_left
- \+/\- *theorem* pow_pow
- \+/\- *theorem* self_pow
- \+/\- *theorem* pow_self
- \+/\- *theorem* pow_pow_self
- \+/\- *theorem* pow_zero
- \+/\- *theorem* pow_one
- \+/\- *theorem* one_pow
- \+/\- *theorem* monoid_hom.map_pow
- \+/\- *theorem* gpow_coe_nat
- \+/\- *theorem* gpow_neg_succ_of_nat
- \+/\- *theorem* gpow_zero
- \+/\- *theorem* gpow_one
- \+/\- *theorem* inv_pow
- \+/\- *theorem* one_gpow
- \+/\- *theorem* gpow_neg
- \+ *theorem* div_gpow
- \- *theorem* zero_nsmul
- \- *theorem* succ_nsmul
- \- *theorem* two_nsmul
- \- *theorem* nsmul_add_comm'
- \- *theorem* succ_nsmul'
- \- *theorem* add_nsmul
- \- *theorem* one_nsmul
- \- *theorem* nsmul_zero
- \- *theorem* mul_nsmul'
- \- *theorem* mul_nsmul
- \- *theorem* nsmul_add_sub_nsmul
- \- *theorem* sub_nsmul_nsmul_add
- \- *theorem* bit0_nsmul
- \- *theorem* bit1_nsmul
- \- *theorem* nsmul_add_comm
- \- *theorem* add_monoid_hom.map_nsmul
- \- *theorem* is_add_monoid_hom.map_nsmul
- \- *theorem* bit0_nsmul'
- \- *theorem* bit1_nsmul'
- \- *theorem* nsmul_add
- \- *theorem* neg_nsmul
- \- *theorem* nsmul_sub
- \- *theorem* nsmul_neg_comm
- \- *theorem* gsmul_coe_nat
- \- *theorem* gsmul_of_nat
- \- *theorem* gsmul_neg_succ_of_nat
- \- *theorem* zero_gsmul
- \- *theorem* one_gsmul
- \- *theorem* gsmul_zero
- \- *theorem* neg_gsmul
- \- *theorem* neg_one_gsmul
- \- *theorem* gsmul_neg
- \- *theorem* gsmul_add
- \- *theorem* gsmul_sub

Modified src/analysis/calculus/extend_deriv.lean


Modified src/data/list/basic.lean
- \- *theorem* sum_repeat

Modified src/data/multiset/basic.lean
- \- *lemma* sum_map_zero
- \- *lemma* sum_map_sum_map
- \+/\- *theorem* prod_repeat
- \- *theorem* sum_repeat

Modified src/group_theory/group_action/defs.lean


Modified src/meta/expr.lean


Modified src/tactic/transform_decl.lean


Created test/to_additive.lean
- \+ *lemma* foo4_test
- \+ *def* foo0
- \+ *def* foo1
- \+ *def* foo2
- \+ *def* foo3
- \+ *def* {a
- \+ *def* foo5
- \+ *def* foo6
- \+ *def* foo7



## [2021-07-05 14:57:50](https://github.com/leanprover-community/mathlib/commit/f2edc5a)
feat(category_theory/preadditive/opposite): Adds some instances and lemmas ([#8202](https://github.com/leanprover-community/mathlib/pull/8202))
This PR adds some instances and lemmas related to opposites and additivity of functors.
#### Estimated changes
Modified src/category_theory/opposites.lean
- \+ *lemma* left_op_id
- \+ *lemma* left_op_comp
- \+ *lemma* right_op_id
- \+ *lemma* right_op_comp

Modified src/category_theory/preadditive/opposite.lean
- \+ *lemma* op_zero
- \+ *lemma* op_add



## [2021-07-05 14:14:01](https://github.com/leanprover-community/mathlib/commit/0b0d8e7)
refactor(ring_theory): turn `localization_map` into a typeclass ([#8119](https://github.com/leanprover-community/mathlib/pull/8119))
This PR replaces the previous `localization_map (M : submodule R) Rₘ` definition (a ring hom `R →+* Rₘ` that presents `Rₘ` as the localization of `R` at `M`) with a new `is_localization M Rₘ` typeclass that puts these requirements on `algebra_map R Rₘ` instead. An important benefit is that we no longer need to mess with `localization_map.codomain` to put an `R`-algebra structure on `Rₘ`, we can just work with `Rₘ` directly.
The important API changes are in commit 0de78dc, all other commits are simply fixes to the dependent files.
Main changes:
 * `localization_map` has been replaced with `is_localization`, similarly `away_map` -> `is_localization.away`, `localization_map.at_prime` -> `is_localization.at_prime` and `fraction_map` -> `is_fraction_ring`
 * many declarations taking the `localization_map` as a parameter now take `R` and/or `M` and/or `Rₘ`, depending on what can be inferred easily
 * `localization_map.to_map` has been replaced with `algebra_map R Rₘ`
 * `localization_map.codomain` and its instances have been removed (you can now directly use `Rₘ`)
 * `is_localization.alg_equiv` generalizes `fraction_map.alg_equiv_of_quotient` (which has been renamed to `is_fraction_ring.alg_equiv`)
 * `is_localization.sec` has been introduced to replace `(to_localization_map _ _).sec`
 * `localization.of` have been replaced with `algebra` and `is_localization` instances on `localization`, similarly for `localization.away.of`, `localization.at_prime.of` and `fraction_ring.of`.
 * `int.fraction_map` is now an instance `rat.is_fraction_ring`
 * All files depending on the above definitions have had fixes. These were mostly straightforward, except:
 * [Some category-theory arrows in `algebraic_geometry/structure.sheaf` are now plain `ring_hom`s. This change was suggested by @justus-springer in order to help the elaborator figure out the arguments to  `is_localization`.](https://github.com/leanprover-community/mathlib/commit/cf3acc925467cc06237a13dbe4264529f9a58850)
 * Deleted `minpoly.over_int_eq_over_rat` and `minpoly.integer_dvd`, now you can just use `gcd_domain_eq_field_fractions` or `gcd_domain_dvd` respectively. [This removes code duplication in `minpoly.lean`](https://github.com/leanprover-community/mathlib/commit/5695924d85710f98ac60a7df91d7dbf27408ca26)
 * `fractional_ideal` does not need to assume `is_localization` everywhere, only for certain specific definitions
Things that stay the same:
 * `localization`, `localization.away`, `localization.at_prime` and `fraction_ring` are still a construction of localizations (although see above for `{localization,localization.away,localization.at_prime,fraction_ring}.of`)
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Refactoring.20.60localization_map.60
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/algebra/char_p/algebra.lean
- \+ *lemma* char_p_of_is_fraction_ring
- \+ *lemma* char_zero_of_is_fraction_ring

Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* to_open_apply
- \+/\- *lemma* to_basic_open_to_map
- \+/\- *def* to_open
- \+/\- *def* to_basic_open

Modified src/field_theory/minpoly.lean
- \+/\- *lemma* gcd_domain_eq_field_fractions
- \+/\- *lemma* gcd_domain_dvd
- \- *lemma* over_int_eq_over_rat
- \- *lemma* integer_dvd

Modified src/ring_theory/dedekind_domain.lean
- \+/\- *lemma* is_dedekind_domain_iff
- \+/\- *lemma* inv_zero'
- \+/\- *lemma* inv_nonzero
- \+/\- *lemma* coe_inv_of_nonzero
- \+/\- *lemma* map_inv
- \+/\- *lemma* span_singleton_inv
- \+/\- *lemma* mul_generator_self_inv
- \+/\- *lemma* invertible_of_principal
- \+/\- *lemma* invertible_iff_generator_nonzero
- \+/\- *lemma* is_principal_inv
- \+/\- *lemma* is_dedekind_domain_inv_iff
- \+/\- *theorem* right_inverse_eq
- \+/\- *theorem* mul_inv_cancel_iff

Modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* val_eq_coe
- \+/\- *lemma* coe_mk
- \+ *lemma* coe_injective
- \+/\- *lemma* ext_iff
- \+/\- *lemma* ext
- \+/\- *lemma* fractional_of_subset_one
- \+/\- *lemma* is_fractional_of_le
- \+/\- *lemma* mem_coe_ideal
- \+/\- *lemma* mem_zero_iff
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_to_fractional_ideal_bot
- \+/\- *lemma* coe_to_submodule_eq_bot
- \+/\- *lemma* coe_to_submodule_ne_bot
- \+/\- *lemma* mem_one_iff
- \+/\- *lemma* coe_mem_one
- \+/\- *lemma* one_mem_one
- \+/\- *lemma* le_iff_mem
- \+/\- *lemma* coe_le_coe
- \+/\- *lemma* zero_le
- \+/\- *lemma* bot_eq_zero
- \+/\- *lemma* le_zero_iff
- \+/\- *lemma* eq_zero_iff
- \+/\- *lemma* fractional_sup
- \+/\- *lemma* fractional_inf
- \+/\- *lemma* sup_eq_add
- \+/\- *lemma* coe_add
- \+/\- *lemma* fractional_mul
- \+/\- *lemma* mul_eq_mul
- \+/\- *lemma* coe_mul
- \+/\- *lemma* mul_left_mono
- \+/\- *lemma* mul_right_mono
- \+/\- *lemma* mul_mem_mul
- \+/\- *lemma* mul_le
- \+/\- *lemma* add_le_add_left
- \+/\- *lemma* mul_le_mul_left
- \+/\- *lemma* le_self_mul_self
- \+/\- *lemma* mul_self_le_self
- \+/\- *lemma* coe_ideal_le_one
- \+/\- *lemma* le_one_iff_exists_coe_ideal
- \+/\- *lemma* fractional_map
- \+/\- *lemma* coe_map
- \+/\- *lemma* mem_map
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_map_symm
- \+/\- *lemma* map_symm_map
- \+/\- *lemma* coe_fun_map_equiv
- \+/\- *lemma* map_equiv_apply
- \+/\- *lemma* map_equiv_symm
- \+/\- *lemma* is_fractional_span_iff
- \+/\- *lemma* is_fractional_of_fg
- \+/\- *lemma* mem_canonical_equiv_apply
- \+/\- *lemma* canonical_equiv_symm
- \+/\- *lemma* canonical_equiv_flip
- \+/\- *lemma* fractional_div_of_nonzero
- \+/\- *lemma* div_zero
- \+/\- *lemma* div_nonzero
- \+/\- *lemma* coe_div
- \+/\- *lemma* mem_div_iff_of_nonzero
- \+/\- *lemma* mul_one_div_le_one
- \+/\- *lemma* le_self_mul_one_div
- \+/\- *lemma* le_div_iff_of_nonzero
- \+/\- *lemma* le_div_iff_mul_le
- \+/\- *lemma* div_one
- \+/\- *lemma* ne_zero_of_mul_eq_one
- \+/\- *lemma* map_div
- \+/\- *lemma* map_one_div
- \+/\- *lemma* is_fractional_span_singleton
- \+/\- *lemma* coe_span_singleton
- \+/\- *lemma* mem_span_singleton
- \+/\- *lemma* mem_span_singleton_self
- \+/\- *lemma* eq_span_singleton_of_principal
- \+/\- *lemma* is_principal_iff
- \+/\- *lemma* span_singleton_zero
- \+/\- *lemma* span_singleton_eq_zero_iff
- \+/\- *lemma* span_singleton_ne_zero_iff
- \+/\- *lemma* span_singleton_one
- \+/\- *lemma* span_singleton_mul_span_singleton
- \+/\- *lemma* canonical_equiv_span_singleton
- \+/\- *lemma* mem_singleton_mul
- \+/\- *lemma* one_div_span_singleton
- \+/\- *lemma* div_span_singleton
- \+/\- *lemma* exists_eq_span_singleton_mul
- \+/\- *lemma* is_noetherian_zero
- \+/\- *lemma* is_noetherian_iff
- \+/\- *lemma* is_noetherian_coe_to_fractional_ideal
- \+/\- *lemma* is_noetherian_span_singleton_inv_to_map_mul
- \+/\- *theorem* eq_one_div_of_mul_eq_one
- \+/\- *theorem* mul_div_self_cancel_iff
- \+/\- *theorem* is_noetherian
- \+/\- *def* is_fractional
- \+/\- *def* mul
- \+/\- *def* map
- \+/\- *def* map_equiv
- \+/\- *def* span_singleton

Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/jacobson.lean
- \+/\- *lemma* is_jacobson_localization
- \+ *lemma* is_integral_is_localization_polynomial_quotient
- \- *lemma* is_integral_localization_map_polynomial_quotient

Modified src/ring_theory/laurent_series.lean
- \+ *lemma* coe_algebra_map
- \- *def* of_power_series_localization

Modified src/ring_theory/localization.lean
- \+ *lemma* to_localization_map_to_map
- \+ *lemma* to_localization_map_to_map_apply
- \+/\- *lemma* is_integer_zero
- \+/\- *lemma* is_integer_one
- \+/\- *lemma* is_integer_add
- \+/\- *lemma* is_integer_mul
- \+/\- *lemma* is_integer_smul
- \+ *lemma* to_localization_map_sec
- \+/\- *lemma* sec_spec
- \+/\- *lemma* sec_spec'
- \+/\- *lemma* map_right_cancel
- \+/\- *lemma* map_left_cancel
- \+/\- *lemma* mk'_one
- \+/\- *lemma* mk'_surjective
- \+/\- *lemma* mk'_mem_iff
- \+/\- *lemma* eq_iff_eq
- \+/\- *lemma* mk'_eq_iff_mk'_eq
- \+/\- *lemma* mk'_self
- \+/\- *lemma* mk'_self'
- \+/\- *lemma* mk'_self''
- \+/\- *lemma* eq_of_eq
- \+/\- *lemma* lift_comp
- \+/\- *lemma* epic_of_localization_map
- \+/\- *lemma* lift_id
- \+/\- *lemma* map_id
- \+/\- *lemma* map_unique
- \+/\- *lemma* ring_equiv_of_ring_equiv_mk'
- \+ *lemma* alg_equiv_mk'
- \+ *lemma* alg_equiv_symm_mk'
- \+ *lemma* monoid_of_eq_algebra_map
- \+ *lemma* mk_one_eq_algebra_map
- \+/\- *lemma* mk_eq_mk'_apply
- \+/\- *lemma* mk_eq_mk'
- \+ *lemma* alg_equiv_mk
- \+ *lemma* alg_equiv_symm_mk
- \+/\- *lemma* surjective_quotient_map_of_maximal_of_localization
- \+/\- *lemma* map_smul
- \+/\- *lemma* is_noetherian_ring
- \+/\- *lemma* coeff_integer_normalization_of_not_mem_support
- \+/\- *lemma* coeff_integer_normalization_mem_support
- \+/\- *lemma* integer_normalization_coeff
- \+/\- *lemma* integer_normalization_spec
- \+/\- *lemma* integer_normalization_map_to_map
- \+/\- *lemma* integer_normalization_eval₂_eq_zero
- \+/\- *lemma* integer_normalization_aeval_eq_zero
- \+/\- *lemma* to_map_eq_zero_iff
- \+/\- *lemma* map_injective_of_injective
- \+ *lemma* is_unit_to_map_iff
- \+ *lemma* to_map_mem_maximal_iff
- \+ *lemma* is_unit_mk'_iff
- \+ *lemma* mk'_mem_maximal_iff
- \+ *lemma* le_comap_prime_compl_iff
- \+/\- *lemma* local_ring_hom_to_map
- \+/\- *lemma* local_ring_hom_mk'
- \+/\- *lemma* local_ring_hom_unique
- \+/\- *lemma* local_ring_hom_comp
- \+ *lemma* mk'_mk_eq_div
- \+/\- *lemma* mk'_eq_div
- \+/\- *lemma* lift_mk'
- \+/\- *lemma* integer_normalization_eq_zero_iff
- \+/\- *lemma* comap_is_algebraic_iff
- \+/\- *lemma* exists_reduced_fraction
- \+/\- *lemma* num_denom_reduced
- \+/\- *lemma* mk'_num_denom
- \+/\- *lemma* num_mul_denom_eq_num_iff_eq
- \+/\- *lemma* num_mul_denom_eq_num_iff_eq'
- \+/\- *lemma* num_mul_denom_eq_num_mul_denom_iff_eq
- \+/\- *lemma* eq_zero_of_num_eq_zero
- \+/\- *lemma* is_integer_of_is_unit_denom
- \+/\- *lemma* is_unit_denom_of_num_eq_zero
- \+ *lemma* is_fraction_ring_of_algebraic
- \+ *lemma* is_fraction_ring_of_finite_extension
- \- *lemma* map_units
- \- *lemma* surj
- \- *lemma* eq_iff_exists
- \- *lemma* ext
- \- *lemma* ext_iff
- \- *lemma* to_map_injective
- \- *lemma* lift_left_inverse
- \- *lemma* ring_equiv_of_ring_equiv_eq_map_apply
- \- *lemma* monoid_of_eq_of
- \- *lemma* mk_one_eq_of
- \- *lemma* ring_equiv_of_quotient_apply
- \- *lemma* ring_equiv_of_quotient_mk'
- \- *lemma* ring_equiv_of_quotient_mk
- \- *lemma* ring_equiv_of_quotient_of
- \- *lemma* ring_equiv_of_quotient_symm_mk'
- \- *lemma* ring_equiv_of_quotient_symm_mk
- \- *lemma* ring_equiv_of_quotient_symm_of
- \- *lemma* away.mk_eq_mk'
- \- *lemma* of_id
- \- *lemma* algebra_map_eq
- \- *lemma* lin_coe_apply
- \- *lemma* alg_equiv_of_quotient_apply
- \- *lemma* alg_equiv_of_quotient_symm_apply
- \- *lemma* injective
- \- *lemma* at_prime.is_unit_to_map_iff
- \- *lemma* at_prime.to_map_mem_maximal_iff
- \- *lemma* at_prime.is_unit_mk'_iff
- \- *lemma* at_prime.mk'_mem_maximal_iff
- \+ *theorem* at_prime.local_ring
- \+ *theorem* mem_map_algebra_map_iff
- \- *theorem* mem_map_to_map_iff
- \+/\- *def* to_localization_map
- \+/\- *def* is_integer
- \+/\- *def* order_iso_of_prime
- \+/\- *def* coe_submodule
- \+/\- *def* integral_domain_of_le_non_zero_divisors
- \+/\- *def* to_integral_domain
- \- *def* submonoid.localization_map.to_ring_localization
- \- *def* codomain
- \- *def* away_map
- \- *def* of
- \- *def* away.of
- \- *def* at_prime
- \- *def* lin_coe
- \- *def* fraction_map
- \- *def* int.fraction_map
- \- *def* fraction_map_of_algebraic
- \- *def* fraction_map_of_finite_extension

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+/\- *lemma* cyclotomic_eq_prod_X_pow_sub_one_pow_moebius

Modified src/ring_theory/polynomial/dickson.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/polynomial/rational_root.lean
- \+/\- *lemma* integer_of_integral
- \+/\- *lemma* integrally_closed
- \+/\- *theorem* num_dvd_of_is_root
- \+/\- *theorem* denom_dvd_of_is_root
- \+/\- *theorem* is_integer_of_is_root_of_monic

Modified src/ring_theory/roots_of_unity.lean




## [2021-07-05 13:27:54](https://github.com/leanprover-community/mathlib/commit/6bad4c6)
feat(ring_theory/trace): the composition of `trace`s is `trace` ([#8078](https://github.com/leanprover-community/mathlib/pull/8078))
A little group of lemmas from the Dedekind domain project.
#### Estimated changes
Modified src/ring_theory/trace.lean
- \+ *lemma* trace_apply
- \+ *lemma* trace_trace_of_basis
- \+ *lemma* trace_comp_trace_of_basis
- \+ *lemma* trace_trace
- \+ *lemma* trace_comp_trace



## [2021-07-05 11:54:51](https://github.com/leanprover-community/mathlib/commit/8ba94ab)
chore(algebra/invertible): units coerced to their monoid are invertible ([#8195](https://github.com/leanprover-community/mathlib/pull/8195))
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *lemma* inv_of_units
- \+ *def* units.invertible



## [2021-07-05 10:29:14](https://github.com/leanprover-community/mathlib/commit/63c8d33)
feat(linear_algebra/matrix/reindex): generalize reindex_linear_equiv to operate on an arbitrary ring ([#8159](https://github.com/leanprover-community/mathlib/pull/8159))
This changes `reindex_linear_equiv eₘ eₙ : matrix m m R ≃ₗ[R] matrix n n R` to `reindex_linear_equiv R A eₘ eₙ : matrix m m A ≃ₗ[R] matrix n n A`, which both works for a larger range of types, and eliminates the need for type ascriptions that was previously caused by the implicitness of `R`.
We cannot yet make the same generalization for `reindex_alg_equiv` as the `algebra R (matrix m m A)` structure implied by `algebra R A` is not in mathlib yet.
#### Estimated changes
Modified src/algebra/lie/classical.lean


Modified src/algebra/lie/matrix.lean


Modified src/linear_algebra/matrix/basis.lean


Modified src/linear_algebra/matrix/reindex.lean
- \+/\- *lemma* reindex_linear_equiv_apply
- \+/\- *lemma* reindex_linear_equiv_symm
- \+/\- *lemma* reindex_linear_equiv_refl_refl
- \+/\- *lemma* reindex_linear_equiv_trans
- \+/\- *lemma* reindex_linear_equiv_comp
- \+/\- *lemma* reindex_linear_equiv_comp_apply
- \+/\- *lemma* reindex_linear_equiv_one
- \+/\- *lemma* reindex_linear_equiv_mul
- \+/\- *lemma* mul_reindex_linear_equiv_one
- \+/\- *lemma* reindex_alg_equiv_apply
- \+/\- *lemma* reindex_alg_equiv_symm
- \+/\- *lemma* reindex_alg_equiv_refl
- \+/\- *lemma* reindex_alg_equiv_mul
- \+/\- *lemma* det_reindex_linear_equiv_self
- \+/\- *lemma* det_reindex_alg_equiv
- \+/\- *def* reindex_linear_equiv
- \+/\- *def* reindex_alg_equiv



## [2021-07-05 09:56:32](https://github.com/leanprover-community/mathlib/commit/a8f60eb)
feat(algebra/lie/free): the universal enveloping algebra of the free Lie algebra is the free associative algebra ([#8183](https://github.com/leanprover-community/mathlib/pull/8183))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_one
- \+ *lemma* one_apply
- \+ *lemma* congr_fun
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *def* id

Modified src/algebra/lie/free.lean
- \+ *def* universal_enveloping_equiv_free_algebra

Modified src/algebra/lie/of_associative.lean
- \+ *lemma* to_lie_hom_coe
- \+ *lemma* coe_to_lie_hom
- \+ *lemma* to_lie_hom_apply
- \+ *lemma* to_lie_hom_id
- \+ *lemma* to_lie_hom_comp
- \+ *lemma* to_lie_hom_injective
- \- *lemma* of_associative_algebra_hom_id
- \- *lemma* of_associative_algebra_hom_apply
- \- *lemma* of_associative_algebra_hom_comp
- \+ *def* to_lie_hom
- \- *def* of_associative_algebra_hom

Modified src/algebra/lie/universal_enveloping.lean




## [2021-07-04 16:29:14](https://github.com/leanprover-community/mathlib/commit/4ace3b7)
feat(measure_theory/conditional_expectation): define the Lp subspace of functions measurable wrt a sigma-algebra, prove completeness ([#7945](https://github.com/leanprover-community/mathlib/pull/7945))
This is the first step towards defining the conditional expectation:
- in this PR a subspace of L^p is shown to be complete, which is necessary to define an orthogonal projection on that subspace;
- the conditional expectation of functions in L^2 will be the orthogonal projection;
- the definition will be extended to L^1 through simple functions (as is done for the integral definition).
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* range_eq_univ

Modified src/measure_theory/arithmetic.lean
- \+ *lemma* ae_eq_trim_of_measurable

Created src/measure_theory/conditional_expectation.lean
- \+ *lemma* congr
- \+ *lemma* add
- \+ *lemma* const_smul
- \+ *lemma* ae_measurable'_of_ae_measurable'_trim
- \+ *lemma* mem_Lp_meas_iff_ae_measurable'
- \+ *lemma* Lp_meas.ae_measurable'
- \+ *lemma* mem_Lp_meas_self
- \+ *lemma* Lp_meas_coe
- \+ *lemma* mem_ℒp_trim_of_mem_Lp_meas
- \+ *lemma* mem_Lp_meas_to_Lp_of_trim
- \+ *lemma* Lp_meas_to_Lp_trim_ae_eq
- \+ *lemma* Lp_trim_to_Lp_meas_ae_eq
- \+ *lemma* Lp_meas_to_Lp_trim_right_inv
- \+ *lemma* Lp_meas_to_Lp_trim_left_inv
- \+ *lemma* Lp_meas_to_Lp_trim_add
- \+ *lemma* Lp_meas_to_Lp_trim_smul
- \+ *lemma* Lp_meas_to_Lp_trim_norm_map
- \+ *def* ae_measurable'
- \+ *def* Lp_meas
- \+ *def* Lp_meas_to_Lp_trim
- \+ *def* Lp_trim_to_Lp_meas
- \+ *def* Lp_meas_to_Lp_trim_lie

Modified src/measure_theory/lp_space.lean
- \+/\- *lemma* snorm'_trim
- \+/\- *lemma* limsup_trim
- \+/\- *lemma* ess_sup_trim
- \+/\- *lemma* snorm_ess_sup_trim
- \+/\- *lemma* snorm_trim
- \+ *lemma* snorm_trim_ae
- \+ *lemma* mem_ℒp_of_mem_ℒp_trim

Modified src/topology/metric_space/isometry.lean
- \+ *lemma* complete_space_iff



## [2021-07-04 15:19:05](https://github.com/leanprover-community/mathlib/commit/01b062a)
chore(category_theory/abelian/diagram_lemmas/four): Make the diagram into a code block ([#8192](https://github.com/leanprover-community/mathlib/pull/8192))
Currently on mathlib docs, it looks like this
![image](https://user-images.githubusercontent.com/15098580/124386872-4c869d00-dcd4-11eb-9c5c-ce6a29e4e607.png)
Making it into a code block should mean that it will render correctly on mathlib docs
#### Estimated changes
Modified src/category_theory/abelian/diagram_lemmas/four.lean




## [2021-07-04 13:54:21](https://github.com/leanprover-community/mathlib/commit/d819e36)
feat(data/finset/basic): sdiff_val, disjoint_to_finset_iff_disjoint ([#8168](https://github.com/leanprover-community/mathlib/pull/8168))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* sdiff_val
- \+/\- *lemma* disjoint_to_finset
- \+ *lemma* disjoint_to_finset_iff_disjoint
- \+/\- *theorem* to_finset_card_of_nodup



## [2021-07-04 13:20:09](https://github.com/leanprover-community/mathlib/commit/2ebd96c)
doc(measure_theory/measurable_space): correct tiny misprints in two doc-strings ([#8187](https://github.com/leanprover-community/mathlib/pull/8187))
Modifying doc-strings of `measurable_space.comap` and `measurable_space.map`: changing "measure space" to "measurable space" in both.
#### Estimated changes
Modified src/measure_theory/measurable_space.lean




## [2021-07-04 11:49:30](https://github.com/leanprover-community/mathlib/commit/7135c96)
chore(data/list/perm): make `perm_nil` a simp lemma ([#8191](https://github.com/leanprover-community/mathlib/pull/8191))
#### Estimated changes
Modified src/data/list/perm.lean
- \+ *theorem* nil_perm



## [2021-07-04 09:30:33](https://github.com/leanprover-community/mathlib/commit/a9db7ce)
chore(measure_theory/{bochner_integration, simple_func_dense}): Move construction of embedding of L1 simple funcs ([#8185](https://github.com/leanprover-community/mathlib/pull/8185))
At the moment, there is a low-level construction in `measure_theory/simple_func_dense` for the approximation of an element of L1 by simple functions, and this is generalized to a more abstract version (with a normed space `L1.simple_func` and a dense linear embedding of this into `L1`) in `measure_theory/bochner_integration`.  [#8114](https://github.com/leanprover-community/mathlib/pull/8114) generalized the low-level construction, and I am thinking of rewriting the more abstract version to apply to `Lp`, too.
But since this will all be more generally useful than in the construction of the Bochner integral, and since the Bochner integral file is very long, I propose moving all this material into `measure_theory/simple_func_dense`.  This PR shows what it would look like.  There are no mathematical changes.
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \- *lemma* exists_forall_norm_le
- \- *lemma* mem_ℒp_zero
- \- *lemma* mem_ℒp_top
- \- *lemma* measure_preimage_lt_top_of_mem_ℒp
- \- *lemma* mem_ℒp_of_finite_measure_preimage
- \- *lemma* mem_ℒp_iff
- \- *lemma* integrable_iff
- \- *lemma* mem_ℒp_iff_integrable
- \- *lemma* mem_ℒp_iff_fin_meas_supp
- \- *lemma* integrable_iff_fin_meas_supp
- \- *lemma* fin_meas_supp.integrable
- \- *lemma* integrable_pair
- \- *lemma* mem_ℒp_of_finite_measure
- \- *lemma* integrable_of_finite_measure
- \- *lemma* measure_preimage_lt_top_of_integrable
- \- *lemma* coe_coe
- \- *lemma* coe_zero
- \- *lemma* coe_add
- \- *lemma* coe_neg
- \- *lemma* coe_sub
- \- *lemma* edist_eq
- \- *lemma* dist_eq
- \- *lemma* norm_eq
- \- *lemma* coe_smul
- \- *lemma* to_L1_eq_to_L1
- \- *lemma* to_L1_eq_mk
- \- *lemma* to_L1_zero
- \- *lemma* to_L1_add
- \- *lemma* to_L1_neg
- \- *lemma* to_L1_sub
- \- *lemma* to_L1_smul
- \- *lemma* norm_to_L1
- \- *lemma* to_L1_to_simple_func
- \- *lemma* to_simple_func_to_L1
- \- *lemma* to_simple_func_eq_to_fun
- \- *lemma* zero_to_simple_func
- \- *lemma* add_to_simple_func
- \- *lemma* neg_to_simple_func
- \- *lemma* sub_to_simple_func
- \- *lemma* smul_to_simple_func
- \- *lemma* lintegral_edist_to_simple_func_lt_top
- \- *lemma* dist_to_simple_func
- \- *lemma* norm_to_simple_func
- \- *def* simple_func
- \- *def* to_L1
- \- *def* to_simple_func
- \- *def* coe_to_L1

Modified src/measure_theory/set_integral.lean
- \- *lemma* integrable.induction

Modified src/measure_theory/simple_func_dense.lean
- \+ *lemma* exists_forall_norm_le
- \+ *lemma* mem_ℒp_zero
- \+ *lemma* mem_ℒp_top
- \+ *lemma* measure_preimage_lt_top_of_mem_ℒp
- \+ *lemma* mem_ℒp_of_finite_measure_preimage
- \+ *lemma* mem_ℒp_iff
- \+ *lemma* integrable_iff
- \+ *lemma* mem_ℒp_iff_integrable
- \+ *lemma* mem_ℒp_iff_fin_meas_supp
- \+ *lemma* integrable_iff_fin_meas_supp
- \+ *lemma* fin_meas_supp.integrable
- \+ *lemma* integrable_pair
- \+ *lemma* mem_ℒp_of_finite_measure
- \+ *lemma* integrable_of_finite_measure
- \+ *lemma* measure_preimage_lt_top_of_integrable
- \+ *lemma* coe_coe
- \+ *lemma* coe_zero
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* coe_sub
- \+ *lemma* edist_eq
- \+ *lemma* dist_eq
- \+ *lemma* norm_eq
- \+ *lemma* coe_smul
- \+ *lemma* to_L1_eq_to_L1
- \+ *lemma* to_L1_eq_mk
- \+ *lemma* to_L1_zero
- \+ *lemma* to_L1_add
- \+ *lemma* to_L1_neg
- \+ *lemma* to_L1_sub
- \+ *lemma* to_L1_smul
- \+ *lemma* norm_to_L1
- \+ *lemma* to_L1_to_simple_func
- \+ *lemma* to_simple_func_to_L1
- \+ *lemma* to_simple_func_eq_to_fun
- \+ *lemma* zero_to_simple_func
- \+ *lemma* add_to_simple_func
- \+ *lemma* neg_to_simple_func
- \+ *lemma* sub_to_simple_func
- \+ *lemma* smul_to_simple_func
- \+ *lemma* lintegral_edist_to_simple_func_lt_top
- \+ *lemma* dist_to_simple_func
- \+ *lemma* norm_to_simple_func
- \+ *lemma* integrable.induction
- \+ *def* simple_func
- \+ *def* to_L1
- \+ *def* to_simple_func
- \+ *def* coe_to_L1



## [2021-07-04 09:30:32](https://github.com/leanprover-community/mathlib/commit/180d004)
ci(.github/workflows/*): switch to self-hosted runners ([#8177](https://github.com/leanprover-community/mathlib/pull/8177))
With this PR, mathlib builds on all branches will use the self-hosted runners that have the "pr" tag. One self-hosted runner is reserved for bors staging branch builds and does not have that tag.
The `build_fork` workflow has been added for use by external forks (and other Lean projects which might want to copy mathlib's CI).
#### Estimated changes
Modified .github/workflows/bors.yml


Modified .github/workflows/build.yml


Modified .github/workflows/build.yml.in


Created .github/workflows/build_fork.yml


Modified .github/workflows/mk_build_yml.sh


Modified bors.toml




## [2021-07-04 07:58:33](https://github.com/leanprover-community/mathlib/commit/863f007)
feat(data/list/basic): map_permutations ([#8188](https://github.com/leanprover-community/mathlib/pull/8188))
As [requested on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/perm.20of.20permutations/near/244821779).
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* map_bind
- \+ *theorem* permutations_aux2_fst
- \+ *theorem* permutations_aux2_snd_nil
- \+ *theorem* permutations_aux2_snd_cons
- \+ *theorem* permutations_aux2_append
- \+ *theorem* mem_permutations_aux2
- \+ *theorem* mem_permutations_aux2'
- \+ *theorem* length_permutations_aux2
- \+ *theorem* foldr_permutations_aux2
- \+ *theorem* mem_foldr_permutations_aux2
- \+ *theorem* length_foldr_permutations_aux2
- \+ *theorem* length_foldr_permutations_aux2'
- \+ *theorem* map_permutations_aux2'
- \+ *theorem* map_permutations_aux2
- \+ *theorem* map_permutations_aux
- \+ *theorem* map_permutations

Modified src/data/list/perm.lean
- \- *theorem* permutations_aux2_fst
- \- *theorem* permutations_aux2_snd_nil
- \- *theorem* permutations_aux2_snd_cons
- \- *theorem* permutations_aux2_append
- \- *theorem* mem_permutations_aux2
- \- *theorem* mem_permutations_aux2'
- \- *theorem* length_permutations_aux2
- \- *theorem* foldr_permutations_aux2
- \- *theorem* mem_foldr_permutations_aux2
- \- *theorem* length_foldr_permutations_aux2
- \- *theorem* length_foldr_permutations_aux2'



## [2021-07-04 02:26:45](https://github.com/leanprover-community/mathlib/commit/cdb44df)
chore(scripts): update nolints.txt ([#8189](https://github.com/leanprover-community/mathlib/pull/8189))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-07-03 16:33:31](https://github.com/leanprover-community/mathlib/commit/531d850)
feat(category_theory): left-derived functors ([#7487](https://github.com/leanprover-community/mathlib/pull/7487))
# Left-derived functors
We define the left-derived functors `F.left_derived n : C ⥤ D` for any additive functor `F`
out of a category with projective resolutions.
The definition is
```
projective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n
```
that is, we pick a projective resolution (thought of as an object of the homotopy category),
we apply `F` objectwise, and compute `n`-th homology.
We show that these left-derived functors can be calculated
on objects using any choice of projective resolution,
and on morphisms by any choice of lift to a chain map between chosen projective resolutions.
Similarly we define natural transformations between left-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.
## Implementation
We don't assume the categories involved are abelian
(just preadditive, and have equalizers, cokernels, and image maps),
or that the functors are right exact.
None of these assumptions are needed yet.
It is often convenient, of course, to work with `[abelian C] [enough_projectives C] [abelian D]`
which (assuming the results from `category_theory.abelian.projective`) are enough to
provide all the typeclass hypotheses assumed here.
#### Estimated changes
Modified src/algebra/homology/homology.lean
- \+/\- *def* homology_functor

Created src/category_theory/derived.lean
- \+ *lemma* functor.left_derived_map_eq
- \+ *lemma* nat_trans.left_derived_id
- \+ *lemma* nat_trans.left_derived_comp
- \+ *lemma* nat_trans.left_derived_eq
- \+ *def* functor.left_derived
- \+ *def* functor.left_derived_obj_iso
- \+ *def* functor.left_derived_obj_projective_zero
- \+ *def* functor.left_derived_obj_projective_succ
- \+ *def* nat_trans.left_derived



## [2021-07-03 13:08:36](https://github.com/leanprover-community/mathlib/commit/74a0f67)
refactor(measure_theory/simple_func_dense): generalize approximation results from L^1 to L^p ([#8114](https://github.com/leanprover-community/mathlib/pull/8114))
Simple functions are dense in L^p.  The argument for `1 ≤ p < ∞` is exactly the same as for `p = 1`, which was already in mathlib:  construct a suitable sequence of pointwise approximations and apply the Dominated Convergence Theorem.  This PR refactors to provide the general-`p` result.
The argument for `p = ∞` requires finite-dimensionality of `E` and a different approximating sequence, so is left for another PR.
#### Estimated changes
Modified src/analysis/convex/integral.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/lp_space.lean
- \+ *lemma* lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top
- \+ *lemma* snorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top
- \+/\- *lemma* tendsto_Lp_iff_tendsto_ℒp'
- \+/\- *lemma* tendsto_Lp_iff_tendsto_ℒp
- \+ *lemma* tendsto_Lp_iff_tendsto_ℒp''

Modified src/measure_theory/prod.lean


Modified src/measure_theory/simple_func_dense.lean
- \+ *lemma* nnnorm_approx_on_le
- \+ *lemma* norm_approx_on_y₀_le
- \+ *lemma* tendsto_approx_on_Lp_snorm
- \+ *lemma* mem_ℒp_approx_on
- \+ *lemma* tendsto_approx_on_univ_Lp_snorm
- \+ *lemma* mem_ℒp_approx_on_univ
- \+ *lemma* tendsto_approx_on_univ_Lp
- \+ *lemma* tendsto_approx_on_L1_nnnorm
- \+ *lemma* tendsto_approx_on_univ_L1_nnnorm
- \- *lemma* tendsto_approx_on_L1_edist
- \- *lemma* tendsto_approx_on_univ_L1_edist



## [2021-07-03 10:46:49](https://github.com/leanprover-community/mathlib/commit/a022bb7)
feat(algebra/invertible): add a missing lemma `inv_of_eq_left_inv` ([#8179](https://github.com/leanprover-community/mathlib/pull/8179))
add "inv_of_eq_left_inv"
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *lemma* inv_of_eq_left_inv



## [2021-07-03 10:46:48](https://github.com/leanprover-community/mathlib/commit/111ac5c)
feat(group_theory/perm/basic): of_subtype_apply_of_mem ([#8174](https://github.com/leanprover-community/mathlib/pull/8174))
#### Estimated changes
Modified src/group_theory/perm/basic.lean
- \+ *lemma* of_subtype_apply_of_mem
- \+/\- *lemma* of_subtype_apply_coe



## [2021-07-03 10:46:47](https://github.com/leanprover-community/mathlib/commit/25d042c)
feat(algebra/periodic): a few more periodicity lemmas ([#8062](https://github.com/leanprover-community/mathlib/pull/8062))
A few more lemmas about periodic functions that I realized are useful.
#### Estimated changes
Modified src/algebra/periodic.lean
- \+ *lemma* periodic.funext
- \+ *lemma* antiperiodic.funext
- \+ *lemma* antiperiodic.funext'



## [2021-07-03 09:58:05](https://github.com/leanprover-community/mathlib/commit/915902e)
feat(topology/algebra/multilinear): add a linear_equiv version of pi ([#8064](https://github.com/leanprover-community/mathlib/pull/8064))
This is a weaker version of `continuous_multilinear_map.piₗᵢ` that requires weaker typeclasses.
Unfortunately I don't understand why the typeclass system continues not to cooperate here, but I suspect it's the same class of problem that plagues `dfinsupp`.
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean


Modified src/topology/algebra/mul_action.lean


Modified src/topology/algebra/multilinear.lean
- \+/\- *lemma* coe_pi
- \+/\- *lemma* pi_apply
- \+ *lemma* _root_.continuous_linear_map.comp_continuous_multilinear_map_coe
- \- *lemma* comp_continuous_multilinear_map_coe
- \+/\- *def* pi
- \+ *def* _root_.continuous_linear_map.comp_continuous_multilinear_map
- \+ *def* pi_equiv
- \+ *def* pi_linear_equiv
- \- *def* comp_continuous_multilinear_map



## [2021-07-03 03:02:44](https://github.com/leanprover-community/mathlib/commit/edb72b4)
docs(data/real/*): add module docstrings ([#8145](https://github.com/leanprover-community/mathlib/pull/8145))
#### Estimated changes
Modified src/data/real/basic.lean


Modified src/data/real/cau_seq_completion.lean




## [2021-07-02 22:04:07](https://github.com/leanprover-community/mathlib/commit/10f6c2c)
feat(data/real/nnreal): cast_nat_abs_eq_nnabs_cast ([#8121](https://github.com/leanprover-community/mathlib/pull/8121))
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* cast_nat_abs_eq_nnabs_cast



## [2021-07-02 20:58:33](https://github.com/leanprover-community/mathlib/commit/f8ca790)
chore(group_theory/congruence): fix docstring ([#8162](https://github.com/leanprover-community/mathlib/pull/8162))
This fixes a docstring which didn't match the code.
#### Estimated changes
Modified src/group_theory/congruence.lean




## [2021-07-02 20:21:24](https://github.com/leanprover-community/mathlib/commit/f5a8b8a)
fix(topology/continuous_function/basic): fix `continuous_map.id_coe` ([#8180](https://github.com/leanprover-community/mathlib/pull/8180))
#### Estimated changes
Modified src/topology/continuous_function/basic.lean
- \+/\- *lemma* id_coe



## [2021-07-02 19:46:00](https://github.com/leanprover-community/mathlib/commit/9e9dfc2)
feat(category_theory/adjunction/fully_faithful): Converses to `unit_is_iso_of_L_fully_faithful` and `counit_is_iso_of_R_fully_faithful` ([#8181](https://github.com/leanprover-community/mathlib/pull/8181))
Add a converse to `unit_is_iso_of_L_fully_faithful` and to `counit_is_iso_of_R_fully_faithful`
#### Estimated changes
Modified src/category_theory/adjunction/fully_faithful.lean
- \+ *lemma* inv_map_unit
- \+ *lemma* inv_counit_map
- \+ *lemma* L_faithful_of_unit_is_iso
- \+ *lemma* R_faithful_of_counit_is_iso
- \+ *def* L_full_of_unit_is_iso
- \+ *def* R_full_of_counit_is_iso



## [2021-07-02 18:29:36](https://github.com/leanprover-community/mathlib/commit/ea924e5)
feat(data/nat/choose/bounds): exponential bounds on binomial coefficients ([#8095](https://github.com/leanprover-community/mathlib/pull/8095))
#### Estimated changes
Created src/combinatorics/choose/bounds.lean
- \+ *lemma* choose_le_pow
- \+ *lemma* pow_le_choose



## [2021-07-02 16:37:34](https://github.com/leanprover-community/mathlib/commit/67c72b4)
feat(data/list/cycle): lift next_prev to cycle ([#8172](https://github.com/leanprover-community/mathlib/pull/8172))
#### Estimated changes
Modified src/data/list/cycle.lean
- \+ *lemma* prev_next
- \+ *lemma* next_prev



## [2021-07-02 10:55:24](https://github.com/leanprover-community/mathlib/commit/d6a7c3b)
chore(algebra/algebra/basic): add `alg_hom.of_linear_map` and lemmas ([#8151](https://github.com/leanprover-community/mathlib/pull/8151))
This lets me golf `complex.lift` a little
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* to_linear_map_id
- \+ *lemma* of_linear_map_to_linear_map
- \+ *lemma* to_linear_map_of_linear_map
- \+ *lemma* of_linear_map_id
- \+ *def* of_linear_map

Modified src/data/complex/module.lean




## [2021-07-02 08:19:35](https://github.com/leanprover-community/mathlib/commit/dfc42f9)
feat(data/equiv/basic): swap_apply_ne_self_iff ([#8167](https://github.com/leanprover-community/mathlib/pull/8167))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* swap_apply_ne_self_iff



## [2021-07-02 05:56:27](https://github.com/leanprover-community/mathlib/commit/f5f8a20)
feat(analysis/calculus/fderiv_symmetric): prove that the second derivative is symmetric ([#8104](https://github.com/leanprover-community/mathlib/pull/8104))
We show that, if a function is differentiable over the reals around a point `x`, and is second-differentiable at `x`, then the second derivative is symmetric. In fact, we even prove a stronger statement for functions differentiable within a convex set, to be able to apply it for functions on the half-plane or the quadrant.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *theorem* is_o_const_const_iff

Created src/analysis/calculus/fderiv_symmetric.lean
- \+ *lemma* convex.taylor_approx_two_segment
- \+ *lemma* convex.is_o_alternate_sum_square
- \+ *lemma* convex.second_derivative_within_at_symmetric_of_mem_interior
- \+ *theorem* convex.second_derivative_within_at_symmetric
- \+ *theorem* second_derivative_symmetric_of_eventually
- \+ *theorem* second_derivative_symmetric

Modified src/analysis/convex/basic.lean
- \+ *lemma* convex.add_smul_sub_mem
- \+ *lemma* convex.add_smul_mem

Modified src/analysis/convex/topology.lean
- \+ *lemma* convex.add_smul_sub_mem_interior
- \+ *lemma* convex.add_smul_mem_interior

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* add_mem_ball_iff_norm
- \+ *lemma* add_mem_closed_ball_iff_norm



## [2021-07-01 21:10:28](https://github.com/leanprover-community/mathlib/commit/92b64a0)
feat(data/list/duplicate): prop that element is a duplicate ([#7824](https://github.com/leanprover-community/mathlib/pull/7824))
As discussed in https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/nodup.20and.20decidability and [#7587](https://github.com/leanprover-community/mathlib/pull/7587)
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* sublist_nil_iff_eq_nil

Created src/data/list/duplicate.lean
- \+ *lemma* mem.duplicate_cons_self
- \+ *lemma* duplicate.duplicate_cons
- \+ *lemma* duplicate.mem
- \+ *lemma* duplicate.mem_cons_self
- \+ *lemma* duplicate_cons_self_iff
- \+ *lemma* duplicate.ne_nil
- \+ *lemma* not_duplicate_nil
- \+ *lemma* duplicate.ne_singleton
- \+ *lemma* not_duplicate_singleton
- \+ *lemma* duplicate.elim_nil
- \+ *lemma* duplicate.elim_singleton
- \+ *lemma* duplicate_cons_iff
- \+ *lemma* duplicate.of_duplicate_cons
- \+ *lemma* duplicate_cons_iff_of_ne
- \+ *lemma* duplicate.mono_sublist
- \+ *lemma* duplicate_iff_sublist
- \+ *lemma* nodup_iff_forall_not_duplicate
- \+ *lemma* exists_duplicate_iff_not_nodup
- \+ *lemma* duplicate.not_nodup
- \+ *lemma* duplicate_iff_two_le_count

Modified src/data/list/nodup_equiv_fin.lean
- \+ *lemma* sublist_of_order_embedding_nth_eq
- \+ *lemma* sublist_iff_exists_order_embedding_nth_eq
- \+ *lemma* sublist_iff_exists_fin_order_embedding_nth_le_eq
- \+ *lemma* duplicate_iff_exists_distinct_nth_le



## [2021-07-01 19:34:23](https://github.com/leanprover-community/mathlib/commit/5945ca3)
chore(*): update to lean 3.31.0c ([#8122](https://github.com/leanprover-community/mathlib/pull/8122))
#### Estimated changes
Modified leanpkg.toml


Modified src/combinatorics/composition.lean


Created src/data/lazy_list.lean
- \+ *def* singleton
- \+ *def* of_list
- \+ *def* to_list
- \+ *def* head
- \+ *def* tail
- \+ *def* append
- \+ *def* map
- \+ *def* map₂
- \+ *def* zip
- \+ *def* join
- \+ *def* for
- \+ *def* approx
- \+ *def* filter
- \+ *def* nth

Modified src/data/lazy_list/basic.lean




## [2021-07-01 18:15:23](https://github.com/leanprover-community/mathlib/commit/395d871)
chore(algebra/lie/free): tidy up after [#8153](https://github.com/leanprover-community/mathlib/pull/8153) ([#8163](https://github.com/leanprover-community/mathlib/pull/8163))
@eric-wieser had some further comments and suggestions which didn't make it into [#8153](https://github.com/leanprover-community/mathlib/pull/8153)
#### Estimated changes
Modified src/algebra/free_non_unital_non_assoc_algebra.lean


Modified src/algebra/lie/free.lean
- \+ *lemma* rel.neg
- \+/\- *lemma* hom_ext

Modified src/algebra/lie/non_unital_non_assoc_algebra.lean
- \+ *lemma* to_non_unital_alg_hom_injective
- \+ *def* to_non_unital_alg_hom
- \- *def* lie_hom.to_non_unital_alg_hom



## [2021-07-01 16:37:06](https://github.com/leanprover-community/mathlib/commit/1571290)
feat(logic/is_empty): add some simp lemmas and unique instances ([#7832](https://github.com/leanprover-community/mathlib/pull/7832))
There are a handful of lemmas about `(h : ¬nonempty a)` that if restated in terms of `[is_empty a]` become suitable for `simp` or as `instance`s. This adjusts some of those lemmas.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* eq_empty_of_is_empty

Modified src/data/matrix/basic.lean
- \+/\- *lemma* subsingleton_of_empty_left
- \+/\- *lemma* subsingleton_of_empty_right

Modified src/data/matrix/dmatrix.lean
- \+/\- *lemma* subsingleton_of_empty_left
- \+/\- *lemma* subsingleton_of_empty_right

Modified src/data/set/basic.lean
- \+ *theorem* eq_empty_of_is_empty
- \+ *def* unique_empty

Modified src/linear_algebra/char_poly/coeff.lean


Modified src/logic/embedding.lean


Modified src/logic/is_empty.lean
- \+ *lemma* subtype.is_empty_of_false

Modified src/order/filter/basic.lean
- \+ *lemma* filter_eq_bot_of_is_empty

Modified src/set_theory/cardinal.lean
- \+ *lemma* eq_zero_of_is_empty

Modified src/set_theory/ordinal.lean




## [2021-07-01 14:19:24](https://github.com/leanprover-community/mathlib/commit/3d2e5ac)
chore(linear_algebra/matrix/determinant): golf a proof ([#8157](https://github.com/leanprover-community/mathlib/pull/8157))
#### Estimated changes
Modified src/linear_algebra/matrix/determinant.lean




## [2021-07-01 14:19:23](https://github.com/leanprover-community/mathlib/commit/ca30bd2)
feat(analysis/fourier): span of monomials is dense in C^0 ([#8035](https://github.com/leanprover-community/mathlib/pull/8035))
Prove that the span of the monomials `λ z, z ^ n` is dense in `C(circle, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows from the Stone-Weierstrass theorem after checking that it is a subalgebra, closed under conjugation, and
separates points.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* to_ring_hom_eq_coe

Modified src/analysis/fourier.lean
- \+ *lemma* fourier_subalgebra_coe
- \+ *lemma* fourier_subalgebra_separates_points
- \+ *lemma* fourier_subalgebra_conj_invariant
- \+ *lemma* fourier_subalgebra_closure_eq_top
- \+ *lemma* span_fourier_closure_eq_top
- \+ *def* fourier_subalgebra

Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* quotient.mkₐ_ker



## [2021-07-01 12:58:30](https://github.com/leanprover-community/mathlib/commit/3fa61ea)
feat(algebra/lie/free): construction of free Lie algebras ([#8153](https://github.com/leanprover-community/mathlib/pull/8153))
#### Estimated changes
Created src/algebra/lie/free.lean
- \+ *lemma* rel.add_left
- \+ *lemma* lift_aux_map_smul
- \+ *lemma* lift_aux_map_add
- \+ *lemma* lift_aux_map_mul
- \+ *lemma* lift_aux_spec
- \+ *lemma* lift_symm_apply
- \+ *lemma* of_comp_lift
- \+ *lemma* lift_unique
- \+ *lemma* lift_of_apply
- \+ *lemma* lift_comp_of
- \+ *lemma* hom_ext
- \+ *def* free_lie_algebra
- \+ *def* of
- \+ *def* lift_aux
- \+ *def* mk
- \+ *def* lift

Created src/algebra/lie/non_unital_non_assoc_algebra.lean
- \+ *def* lie_ring.to_non_unital_non_assoc_semiring
- \+ *def* lie_hom.to_non_unital_alg_hom

Modified src/algebra/non_unital_alg_hom.lean
- \+ *lemma* congr_fun



## [2021-07-01 12:58:29](https://github.com/leanprover-community/mathlib/commit/4d24172)
docs(order/zorn): explain how to use Zorn's lemma ([#8125](https://github.com/leanprover-community/mathlib/pull/8125))
#### Estimated changes
Modified src/order/zorn.lean
- \+ *lemma* zorny_lemma



## [2021-07-01 12:58:27](https://github.com/leanprover-community/mathlib/commit/7cbca35)
feat(data/fintype/intervals): fintype instances for set.{Icc,Ioc,Ioo} ([#8123](https://github.com/leanprover-community/mathlib/pull/8123))
#### Estimated changes
Modified src/data/fintype/intervals.lean
- \+/\- *lemma* Ico_ℤ_finite
- \+/\- *lemma* Ioo_ℤ_finite
- \+/\- *lemma* Icc_ℤ_finite
- \+/\- *lemma* Ioc_ℤ_finite
- \+ *lemma* Ioo_ℤ_card
- \+ *lemma* Icc_ℤ_card
- \+ *lemma* Ioc_ℤ_card



## [2021-07-01 11:10:36](https://github.com/leanprover-community/mathlib/commit/6e0d2d3)
feat(logic/basic): add two simp lemmas ([#8148](https://github.com/leanprover-community/mathlib/pull/8148))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* iff_self_and
- \+ *lemma* iff_and_self



## [2021-07-01 07:48:35](https://github.com/leanprover-community/mathlib/commit/8986c4f)
chore(linear_algebra/matrix/determinant): squeeze some simps for speed up ([#8156](https://github.com/leanprover-community/mathlib/pull/8156))
I simply squeezed some simps in `linear_algebra/matrix/determinant` to obtain two much faster proofs.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews)
#### Estimated changes
Modified src/linear_algebra/matrix/determinant.lean




## [2021-07-01 07:48:34](https://github.com/leanprover-community/mathlib/commit/582ee9e)
feat(logic/basic): subtype.subsingleton ([#8138](https://github.com/leanprover-community/mathlib/pull/8138))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* subtype.subsingleton



## [2021-07-01 07:48:33](https://github.com/leanprover-community/mathlib/commit/aabb900)
feat(order/preorder_hom): preorder_hom_eq_id ([#8135](https://github.com/leanprover-community/mathlib/pull/8135))
From LTE
#### Estimated changes
Modified src/order/preorder_hom.lean
- \+ *lemma* preorder_hom_eq_id
- \+ *def* unique



## [2021-07-01 07:48:32](https://github.com/leanprover-community/mathlib/commit/4a75876)
feat(category_theory/limits/concrete_category): Some lemmas about limits in concrete categories ([#8130](https://github.com/leanprover-community/mathlib/pull/8130))
Generalizes some lemmas from LTE. 
See zulip discussion [here](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/for_mathlib.2Fwide_pullback/near/244298079).
#### Estimated changes
Modified src/category_theory/limits/concrete_category.lean
- \+ *lemma* concrete.to_product_injective_of_is_limit
- \+ *lemma* concrete.is_limit_ext
- \+ *lemma* concrete.limit_ext
- \+ *lemma* concrete.wide_pullback_ext
- \+ *lemma* concrete.wide_pullback_ext'
- \+ *lemma* concrete.from_union_surjective_of_is_colimit
- \+ *lemma* concrete.is_colimit_exists_rep
- \+ *lemma* concrete.colimit_exists_rep
- \+ *lemma* concrete.wide_pushout_exists_rep
- \+ *lemma* concrete.wide_pushout_exists_rep'

Modified src/topology/category/Profinite/default.lean




## [2021-07-01 06:12:12](https://github.com/leanprover-community/mathlib/commit/2df573a)
feat(data/int/basic): int.eq_zero_of_div_eq_zero ([#8134](https://github.com/leanprover-community/mathlib/pull/8134))
#### Estimated changes
Modified src/data/int/basic.lean




## [2021-07-01 02:20:40](https://github.com/leanprover-community/mathlib/commit/b972280)
chore(scripts): update nolints.txt ([#8155](https://github.com/leanprover-community/mathlib/pull/8155))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt


