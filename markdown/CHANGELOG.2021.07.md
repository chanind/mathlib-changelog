## [2021-07-31 21:11:47](https://github.com/leanprover-community/mathlib/commit/4c2edb0)
feat(data/equiv/mul_add): add `units.coe_inv` ([#8477](https://github.com/leanprover-community/mathlib/pull/8477))
* rename old `units.coe_inv` to `units.coe_inv''`;
* add new `@[simp, norm_cast, to_additive] lemma units.coe_inv` about
  coercion of units of a group;
* add missing `coe_to_units`.
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* units.coe_inv''
- \- *lemma* units.coe_inv

Modified src/data/equiv/mul_add.lean
- \+ *lemma* coe_to_units
- \+/\- *def* to_units
- \+ *lemma* units.coe_inv



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
- \+ *lemma* ennreal.tendsto_const_mul_rpow_nhds_zero_of_pos

Modified src/topology/metric_space/holder.lean
- \+ *lemma* holder_on_with.comp
- \+ *lemma* holder_on_with.comp_holder_with
- \+ *lemma* holder_on_with.ediam_image_inter_le
- \+ *lemma* holder_on_with.ediam_image_inter_le_of_le
- \+ *lemma* holder_on_with.ediam_image_le
- \+ *lemma* holder_on_with.ediam_image_le_of_le
- \+ *lemma* holder_on_with.ediam_image_le_of_subset
- \+ *lemma* holder_on_with.ediam_image_le_of_subset_of_le
- \+ *lemma* holder_on_with.edist_le
- \+ *lemma* holder_on_with.edist_le_of_le
- \+ *def* holder_on_with
- \+ *lemma* holder_on_with_empty
- \+ *lemma* holder_on_with_one
- \+ *lemma* holder_on_with_singleton
- \+ *lemma* holder_on_with_univ
- \+ *lemma* holder_with.comp_holder_on_with
- \+ *lemma* set.subsingleton.holder_on_with

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
- \+ *lemma* matrix.update_column_subsingleton
- \+ *lemma* matrix.update_row_subsingleton



## [2021-07-30 12:33:57](https://github.com/leanprover-community/mathlib/commit/977063f)
chore(group_theory/congruence): a few `simp` lemmas ([#8452](https://github.com/leanprover-community/mathlib/pull/8452))
* add `con.comap_rel`;
* add `@[simp]` to `con.ker_rel`;
* replace `con.comp_mk'_apply` with `con.coe_mk'`;
* [unrelated] add `commute.semiconj_by`.
#### Estimated changes
Modified src/algebra/group/commute.lean


Modified src/group_theory/congruence.lean
- \+ *lemma* con.coe_mk'
- \+ *lemma* con.comap_rel
- \- *lemma* con.comp_mk'_apply



## [2021-07-30 07:20:29](https://github.com/leanprover-community/mathlib/commit/98b0d18)
feat(analysis/normed_space/SemiNormedGroup/kernel): Fix universes + add explicit ([#8467](https://github.com/leanprover-community/mathlib/pull/8467))
See associated discussion from [zulip](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/for_mathlib/near/247575730)
#### Estimated changes
Modified src/analysis/normed_space/SemiNormedGroup/kernels.lean
- \+ *def* SemiNormedGroup.cokernel_cocone
- \+ *def* SemiNormedGroup.cokernel_lift
- \+ *lemma* SemiNormedGroup.comp_explicit_cokernel_π
- \+ *def* SemiNormedGroup.explicit_cokernel
- \+ *def* SemiNormedGroup.explicit_cokernel_desc
- \+ *lemma* SemiNormedGroup.explicit_cokernel_desc_norm_le
- \+ *lemma* SemiNormedGroup.explicit_cokernel_desc_norm_le_of_norm_le
- \+ *lemma* SemiNormedGroup.explicit_cokernel_desc_unique
- \+ *lemma* SemiNormedGroup.explicit_cokernel_hom_ext
- \+ *def* SemiNormedGroup.explicit_cokernel_iso
- \+ *lemma* SemiNormedGroup.explicit_cokernel_iso_hom_desc
- \+ *lemma* SemiNormedGroup.explicit_cokernel_iso_hom_π
- \+ *lemma* SemiNormedGroup.explicit_cokernel_iso_inv_π
- \+ *def* SemiNormedGroup.explicit_cokernel_π
- \+ *lemma* SemiNormedGroup.explicit_cokernel_π_desc
- \+ *def* SemiNormedGroup.is_colimit_cokernel_cocone
- \+ *lemma* SemiNormedGroup.is_quotient_explicit_cokernel_π
- \+ *lemma* SemiNormedGroup.norm_noninc_explicit_cokernel_π
- \+/\- *def* SemiNormedGroup₁.cokernel_cocone
- \+/\- *def* SemiNormedGroup₁.cokernel_lift



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
- \+ *lemma* coe_ideal_le_self_mul_inv
- \+ *lemma* exists_multiset_prod_cons_le_and_prod_not_le
- \+ *lemma* fractional_ideal.coe_ideal_mul_inv
- \+ *lemma* fractional_ideal.exists_not_mem_one_of_ne_bot
- \+ *theorem* fractional_ideal.mul_inv_cancel
- \+ *lemma* fractional_ideal.mul_inv_cancel_of_le_one
- \+ *lemma* fractional_ideal.one_inv
- \+ *lemma* fractional_ideal.one_mem_inv_coe_ideal
- \+ *lemma* inv_anti_mono
- \+ *theorem* is_dedekind_domain_iff_is_dedekind_domain_inv
- \+ *lemma* le_self_mul_inv
- \+ *lemma* mem_inv_iff

Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.eq_zero_or_one
- \+ *lemma* fractional_ideal.eq_zero_or_one_of_is_field



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
- \+ *lemma* order_iso.is_glb_image
- \+ *lemma* order_iso.is_glb_preimage
- \+ *lemma* order_iso.is_lub_image
- \+ *lemma* order_iso.is_lub_preimage

Modified src/order/rel_iso.lean
- \+ *lemma* order_iso.image_eq_preimage
- \+ *lemma* order_iso.image_preimage
- \+ *lemma* order_iso.image_symm_image
- \+ *lemma* order_iso.le_symm_apply
- \+ *lemma* order_iso.preimage_image
- \+ *lemma* order_iso.preimage_symm_preimage
- \+ *lemma* order_iso.symm_image_image
- \+ *lemma* order_iso.symm_preimage_preimage

Modified src/order/semiconj_Sup.lean
- \+ *lemma* is_order_right_adjoint.comp_order_iso
- \+ *lemma* is_order_right_adjoint.order_iso_comp
- \+/\- *lemma* is_order_right_adjoint.right_mono
- \- *lemma* is_order_right_adjoint.unique



## [2021-07-28 22:58:41](https://github.com/leanprover-community/mathlib/commit/6d3e936)
feat(measure_theory): add @[to_additive] ([#8142](https://github.com/leanprover-community/mathlib/pull/8142))
This PR adds `@[to_additive]` to `haar_measure` and everything that depends on. This will allow us to define the Lebesgue measure on `ℝ` and `ℝ ^ n` as the Haar measure (or just show that it is equal to it).
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/measure_theory/arithmetic.lean
- \+/\- *lemma* finset.ae_measurable_prod'
- \+/\- *lemma* finset.ae_measurable_prod
- \+/\- *lemma* finset.measurable_prod'
- \+/\- *lemma* finset.measurable_prod
- \+/\- *lemma* list.ae_measurable_prod'
- \+/\- *lemma* list.ae_measurable_prod
- \+/\- *lemma* list.measurable_prod'
- \+/\- *lemma* list.measurable_prod
- \+/\- *lemma* multiset.ae_measurable_prod'
- \+/\- *lemma* multiset.ae_measurable_prod
- \+/\- *lemma* multiset.measurable_prod'
- \+/\- *lemma* multiset.measurable_prod

Modified src/measure_theory/conditional_expectation.lean


Modified src/measure_theory/content.lean


Modified src/measure_theory/group.lean


Modified src/measure_theory/haar_measure.lean
- \+/\- *lemma* measure_theory.measure.haar.mem_prehaar_empty
- \+ *theorem* measure_theory.measure.regular_of_is_mul_left_invariant
- \- *theorem* measure_theory.measure.regular_of_left_invariant

Modified src/measure_theory/lp_space.lean
- \+/\- *lemma* measure_theory.snorm'_const_smul

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
- \+ *lemma* set.image_equiv_eq_preimage_symm
- \+ *lemma* set.mem_image_equiv
- \+ *lemma* set.preimage_equiv_eq_image_symm

Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.comap_equiv_eq_map_symm
- \+ *lemma* subgroup.map_equiv_eq_comap_symm
- \+ *lemma* subgroup.mem_map_equiv

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid.comap_equiv_eq_map_symm
- \+ *lemma* submonoid.map_equiv_eq_comap_symm
- \+ *lemma* submonoid.mem_map_equiv

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.comap_equiv_eq_map_symm
- \+ *lemma* submodule.map_equiv_eq_comap_symm

Modified src/ring_theory/subring.lean
- \+ *lemma* subring.comap_equiv_eq_map_symm
- \+ *lemma* subring.map_equiv_eq_comap_symm
- \+ *lemma* subring.mem_map_equiv

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* subsemiring.comap_equiv_eq_map_symm
- \+ *lemma* subsemiring.map_equiv_eq_comap_symm
- \+ *lemma* subsemiring.mem_map_equiv



## [2021-07-28 19:44:39](https://github.com/leanprover-community/mathlib/commit/7180d2f)
feat(group_theory/coset): Show that `quotient_group.left_rel` and `left_coset_equivalence` are the same thing ([#8382](https://github.com/leanprover-community/mathlib/pull/8382))
#### Estimated changes
Modified src/group_theory/coset.lean
- \+ *lemma* left_coset_eq_iff
- \+/\- *def* quotient_group.left_rel
- \+ *lemma* quotient_group.left_rel_r_eq_left_coset_equivalence
- \+/\- *def* quotient_group.quotient
- \+/\- *def* quotient_group.right_rel
- \+ *lemma* quotient_group.right_rel_r_eq_right_coset_equivalence
- \+ *lemma* right_coset_eq_iff



## [2021-07-28 17:10:49](https://github.com/leanprover-community/mathlib/commit/32c8227)
feat(analysis/normed_space/basic): define inclusion `locally_constant X G → C(X, G)` as various types of bundled morphism ([#8448](https://github.com/leanprover-community/mathlib/pull/8448))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *def* locally_constant.to_continuous_map_alg_hom
- \+ *def* locally_constant.to_continuous_map_linear_map
- \+ *def* locally_constant.to_continuous_map_monoid_hom

Modified src/topology/locally_constant/algebra.lean
- \+ *lemma* locally_constant.coe_algebra_map
- \+ *def* locally_constant.const_monoid_hom
- \+ *def* locally_constant.const_ring_hom

Modified src/topology/locally_constant/basic.lean
- \+ *lemma* locally_constant.coe_const



## [2021-07-28 14:08:17](https://github.com/leanprover-community/mathlib/commit/b71d38c)
feat(algebra/big_operators/basic): add lemmas about prod and sum of finset.erase ([#8449](https://github.com/leanprover-community/mathlib/pull/8449))
This adds:
* `finset.prod_erase_mul`
* `finset.mul_prod_erase`
* `finset.sum_erase_add`
* `finset.add_sum_erase`
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.mul_prod_erase
- \+ *lemma* finset.prod_erase_mul



## [2021-07-28 14:08:16](https://github.com/leanprover-community/mathlib/commit/0ccd2f6)
feat(data/dfinsupp): add simp lemma `single_eq_zero` ([#8447](https://github.com/leanprover-community/mathlib/pull/8447))
This matches `finsupp.single_eq_zero`.
Also adds `dfinsupp.ext_iff`, and changes some lemma arguments to be explicit.
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.ext_iff
- \+/\- *lemma* dfinsupp.single_add
- \+ *lemma* dfinsupp.single_eq_zero
- \+/\- *lemma* dfinsupp.single_zero



## [2021-07-28 11:16:48](https://github.com/leanprover-community/mathlib/commit/4acfa92)
chore(algebra/floor): add a few trivial `simp` lemmas about `floor` ([#8450](https://github.com/leanprover-community/mathlib/pull/8450))
#### Estimated changes
Modified src/algebra/floor.lean
- \+ *theorem* floor_add_nat
- \+ *theorem* floor_int_add
- \+/\- *theorem* floor_mono
- \+ *theorem* floor_nat_add
- \+/\- *theorem* floor_sub_int
- \+ *theorem* floor_sub_nat



## [2021-07-28 09:02:05](https://github.com/leanprover-community/mathlib/commit/30ff935)
feat(topology/algebra): topological fields ([#8316](https://github.com/leanprover-community/mathlib/pull/8316))
Including the completion of completeable topological fields.
From the perfectoid spaces project.
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.comap_comm
- \+ *lemma* filter.map_comm

Modified src/topology/algebra/field.lean
- \+ *lemma* topological_division_ring.continuous_units_inv
- \+ *lemma* topological_division_ring.units_top_group
- \+ *lemma* topological_ring.induced_units.continuous_coe
- \+ *def* topological_ring.topological_space_units
- \+ *lemma* topological_ring.units_embedding
- \+ *lemma* topological_ring.units_topology_eq

Added src/topology/algebra/uniform_field.lean
- \+ *lemma* coe_inv
- \+ *lemma* continuous_hat_inv
- \+ *def* hat_inv
- \+ *lemma* hat_inv_extends
- \+ *lemma* mul_hat_inv_cancel

Modified src/topology/basic.lean
- \+ *lemma* mem_closure_image
- \+ *lemma* mem_closure_of_mem_closure_union

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
- \+ *lemma* mul_action.exists_fixed_point_of_prime_dvd_card_of_fixed_point
- \+ *lemma* mul_action.nonempty_fixed_point_of_prime_not_dvd_card



## [2021-07-28 00:40:17](https://github.com/leanprover-community/mathlib/commit/37fc4cf)
feat(group_theory/subgroup): equiv_map_of_injective ([#8371](https://github.com/leanprover-community/mathlib/pull/8371))
Also for rings and submonoids. The version for modules, `submodule.equiv_map_of_injective`, was already there.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.coe_equiv_map_of_injective_apply

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid.coe_equiv_map_of_injective_apply

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.coe_equiv_map_of_injective_apply

Modified src/ring_theory/subring.lean
- \+ *lemma* subring.coe_equiv_map_of_injective_apply

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* subsemiring.coe_equiv_map_of_injective_apply



## [2021-07-27 23:02:33](https://github.com/leanprover-community/mathlib/commit/cc7627a)
feat(analysis/normed_space/basic): define `normed_group` structure induced by injective group homomorphism ([#8443](https://github.com/leanprover-community/mathlib/pull/8443))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *def* normed_group.induced
- \+ *def* semi_normed_group.induced



## [2021-07-27 23:02:32](https://github.com/leanprover-community/mathlib/commit/1b0391a)
feat(data/nat/totient): totient_mul ([#8441](https://github.com/leanprover-community/mathlib/pull/8441))
Also made `data/nat/totient` import `data/zmod/basic` instead of the other way round because I think people are more likely to want `zmod` but not `totient` than `totient` but not `zmod`.
Also deleted the deprecated `gpowers` because it caused a name clash in `group_theory/subgroup` when the imports were changed.
#### Estimated changes
Modified src/data/nat/totient.lean
- \+ *lemma* nat.totient_mul
- \+ *lemma* zmod.card_units_eq_totient

Modified src/data/zmod/basic.lean
- \- *lemma* zmod.card_units_eq_totient

Modified src/deprecated/subgroup.lean
- \- *def* gmultiples
- \- *lemma* gmultiples_subset
- \- *def* gpowers
- \- *lemma* gpowers_subset
- \- *theorem* group.gpowers_eq_closure
- \- *lemma* is_add_subgroup.gsmul_mem
- \- *lemma* is_subgroup.gpow_mem
- \- *lemma* mem_gmultiples
- \- *lemma* mem_gpowers

Modified src/linear_algebra/free_module_pid.lean




## [2021-07-27 23:02:31](https://github.com/leanprover-community/mathlib/commit/a445c45)
feat(measure_theory/interval_integrable): a monotone function is interval integrable ([#8398](https://github.com/leanprover-community/mathlib/pull/8398))
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integrable_of_antimono
- \+ *lemma* interval_integrable_of_antimono_on
- \+ *lemma* interval_integrable_of_monotone
- \+ *lemma* interval_integrable_of_monotone_on



## [2021-07-27 19:34:42](https://github.com/leanprover-community/mathlib/commit/9f75dc8)
feat(measure_theory/lebesgue_measure): volume s ≤ diam s ([#8437](https://github.com/leanprover-community/mathlib/pull/8437))
* for `s : set real`, `volume s ≤ diam s`;
* for `s : set (ι → real)`, `volume s ≤ ∏ i, diam (eval i '' s) ≤ diam s ^ fintype.card ι`.
#### Estimated changes
Modified src/measure_theory/lebesgue_measure.lean
- \+ *lemma* real.volume_le_diam
- \+ *lemma* real.volume_pi_le_diam_pow
- \+ *lemma* real.volume_pi_le_prod_diam

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.ediam_of_unbounded

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* edist_le_pi_edist

Modified src/topology/metric_space/lipschitz.lean




## [2021-07-27 19:34:41](https://github.com/leanprover-community/mathlib/commit/5375918)
feat(topology/metric_space/antilipschitz): ediam of image/preimage ([#8435](https://github.com/leanprover-community/mathlib/pull/8435))
Also review API
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.div_le_of_le_mul'
- \+ *lemma* ennreal.mul_le_of_le_div'
- \+ *lemma* ennreal.mul_le_of_le_div

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.div_le_of_le_mul'
- \+ *lemma* nnreal.div_le_of_le_mul

Modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* antilipschitz_with.ediam_preimage_le
- \+ *lemma* antilipschitz_with.le_mul_ediam_image
- \+/\- *lemma* antilipschitz_with.mul_le_dist
- \+ *lemma* antilipschitz_with.mul_le_nndist
- \+/\- *lemma* antilipschitz_with_iff_le_mul_dist
- \+ *lemma* antilipschitz_with_iff_le_mul_nndist



## [2021-07-27 19:34:40](https://github.com/leanprover-community/mathlib/commit/d57b6f9)
chore(data/dfinsupp): add yet more map_dfinsupp_sum lemmas ([#8400](https://github.com/leanprover-community/mathlib/pull/8400))
As always, the one of quadratically many combinations of `FOO_hom.map_BAR_sum` is never there when you need it.
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* add_equiv.map_dfinsupp_sum_add_hom
- \+/\- *lemma* add_monoid_hom.coe_dfinsupp_sum_add_hom
- \+/\- *lemma* add_monoid_hom.dfinsupp_sum_add_hom_apply
- \+/\- *lemma* add_monoid_hom.map_dfinsupp_sum_add_hom
- \+/\- *lemma* dfinsupp.prod_sum_index
- \+ *lemma* mul_equiv.map_dfinsupp_prod
- \+ *lemma* ring_hom.map_dfinsupp_prod
- \+ *lemma* ring_hom.map_dfinsupp_sum
- \+ *lemma* ring_hom.map_dfinsupp_sum_add_hom

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.map_dfinsupp_sum
- \+ *lemma* linear_equiv.map_dfinsupp_sum_add_hom
- \+ *lemma* linear_equiv.map_finsupp_sum
- \+ *lemma* linear_map.map_dfinsupp_sum_add_hom



## [2021-07-27 19:34:39](https://github.com/leanprover-community/mathlib/commit/aea21af)
feat(ring_theory): `is_dedekind_domain_inv` implies `is_dedekind_domain` ([#8315](https://github.com/leanprover-community/mathlib/pull/8315))
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean
- \+ *lemma* fractional_ideal.adjoin_integral_eq_one_of_is_unit
- \+ *lemma* is_dedekind_domain_inv.dimension_le_one
- \+ *lemma* is_dedekind_domain_inv.integrally_closed
- \+ *lemma* is_dedekind_domain_inv.inv_mul_eq_one
- \+ *theorem* is_dedekind_domain_inv.is_dedekind_domain
- \+ *lemma* is_dedekind_domain_inv.is_noetherian_ring
- \+ *lemma* is_dedekind_domain_inv.mul_inv_eq_one
- \+/\- *lemma* is_dedekind_domain_inv_iff
- \+ *lemma* mul_inv_cancel_iff_is_unit

Modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* fractional_ideal.mem_coe
- \+ *lemma* fractional_ideal.mem_coe_ideal_of_mem

Modified src/ring_theory/principal_ideal_domain.lean
- \+ *lemma* is_field.is_principal_ideal_ring



## [2021-07-27 19:34:38](https://github.com/leanprover-community/mathlib/commit/a052dd6)
doc(algebra/invertible): implementation notes about `invertible` instances ([#8197](https://github.com/leanprover-community/mathlib/pull/8197))
In the discussion on [#8195](https://github.com/leanprover-community/mathlib/pull/8195), I suggested to add these implementation notes. Creating a new PR should allow for a bit more direct discussion on the use of and plans for `invertible`.
#### Estimated changes
Modified src/algebra/invertible.lean




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
Added src/analysis/normed_space/SemiNormedGroup/kernels.lean
- \+ *def* SemiNormedGroup₁.cokernel_cocone
- \+ *def* SemiNormedGroup₁.cokernel_lift

Modified src/analysis/normed_space/normed_group_quotient.lean
- \+/\- *lemma* normed_group_hom.lift_mk
- \+ *lemma* normed_group_hom.lift_norm_le
- \+ *lemma* normed_group_hom.lift_norm_noninc



## [2021-07-27 16:37:38](https://github.com/leanprover-community/mathlib/commit/768980a)
feat(topology/locally_constant/basic): coercion of locally-constant function to continuous map ([#8444](https://github.com/leanprover-community/mathlib/pull/8444))
#### Estimated changes
Modified src/topology/locally_constant/basic.lean
- \+ *lemma* locally_constant.coe_continuous_map
- \+ *def* locally_constant.to_continuous_map
- \+ *lemma* locally_constant.to_continuous_map_eq_coe
- \+ *lemma* locally_constant.to_continuous_map_injective



## [2021-07-27 16:37:36](https://github.com/leanprover-community/mathlib/commit/3faee06)
feat(algebra/order_functions): max/min commutative and other props ([#8416](https://github.com/leanprover-community/mathlib/pull/8416))
The statements of the commutivity, associativity, and left commutativity of min and max are stated only in the rewrite lemmas, and not in their "commutative" synonyms.
This prevents them from being discoverable by suggest and related tactics. We now provide the synonyms explicitly.
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* max_associative
- \+ *lemma* max_commutative
- \+ *lemma* max_left_commutative
- \+ *lemma* min_associative
- \+ *lemma* min_commutative
- \+ *lemma* min_left_commutative



## [2021-07-27 16:37:35](https://github.com/leanprover-community/mathlib/commit/6c2f80c)
feat(category_theory/limits): disjoint coproducts ([#8380](https://github.com/leanprover-community/mathlib/pull/8380))
Towards a more detailed hierarchy of categorical properties.
#### Estimated changes
Added src/category_theory/limits/shapes/disjoint_coproduct.lean
- \+ *lemma* category_theory.limits.initial_mono_class_of_disjoint_coproducts
- \+ *def* category_theory.limits.is_initial_of_is_pullback_of_is_coproduct



## [2021-07-27 16:37:34](https://github.com/leanprover-community/mathlib/commit/bb44e1a)
feat(category_theory/subobject): generalise bot of subobject lattice ([#8232](https://github.com/leanprover-community/mathlib/pull/8232))
#### Estimated changes
Modified src/algebra/homology/homology.lean


Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/limits/shapes/zero.lean
- \- *lemma* category_theory.limits.has_zero_object.has_initial
- \- *lemma* category_theory.limits.has_zero_object.has_terminal
- \+ *def* category_theory.limits.has_zero_object.zero_is_initial
- \+ *def* category_theory.limits.has_zero_object.zero_is_terminal
- \+ *def* category_theory.limits.has_zero_object_of_has_initial_object
- \+ *def* category_theory.limits.has_zero_object_of_has_terminal_object

Modified src/category_theory/subobject/factor_thru.lean
- \+/\- *def* category_theory.mono_over.factor_thru
- \+/\- *def* category_theory.mono_over.factors

Modified src/category_theory/subobject/lattice.lean
- \+/\- *lemma* category_theory.mono_over.bot_arrow
- \+ *lemma* category_theory.mono_over.bot_arrow_eq_zero
- \+ *def* category_theory.mono_over.bot_coe_iso_zero
- \+/\- *lemma* category_theory.mono_over.bot_left
- \+ *def* category_theory.subobject.bot_coe_iso_initial
- \+/\- *def* category_theory.subobject.bot_coe_iso_zero
- \+ *lemma* category_theory.subobject.bot_eq_initial_to
- \+/\- *lemma* category_theory.subobject.bot_eq_zero

Modified src/category_theory/subobject/limits.lean
- \+/\- *lemma* category_theory.limits.image_subobject_zero
- \+/\- *lemma* category_theory.limits.image_subobject_zero_arrow



## [2021-07-27 13:18:35](https://github.com/leanprover-community/mathlib/commit/b61ce02)
feat(number_theory/padics/padic_norm): add p^v(n) | n ([#8442](https://github.com/leanprover-community/mathlib/pull/8442))
Add some API for `padic_val_nat` (a convenient function for e.g. Sylow theory).
#### Estimated changes
Modified src/number_theory/padics/padic_norm.lean
- \+ *lemma* pow_padic_val_nat_dvd
- \+ *lemma* pow_succ_padic_val_nat_not_dvd

Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity.lt_top_iff_finite
- \+ *lemma* multiplicity.ne_top_iff_finite



## [2021-07-27 10:18:45](https://github.com/leanprover-community/mathlib/commit/7ae8da4)
fix(algebra/big_operators/ring): `finset.sum_mul_sum` is true in a non-assoc non-unital semiring ([#8436](https://github.com/leanprover-community/mathlib/pull/8436))
#### Estimated changes
Modified src/algebra/big_operators/ring.lean




## [2021-07-27 10:18:44](https://github.com/leanprover-community/mathlib/commit/3b590f3)
feat(logic/embedding): add a coe instance from equiv to embeddings ([#8323](https://github.com/leanprover-community/mathlib/pull/8323))
#### Estimated changes
Modified src/logic/embedding.lean
- \+/\- *def* equiv.as_embedding
- \+ *lemma* equiv.coe_eq_to_embedding

Added test/equiv.lean
- \+ *def* f
- \+ *def* s



## [2021-07-27 08:42:12](https://github.com/leanprover-community/mathlib/commit/23e7c84)
fix(algebra/ordered_group): add missing `to_additive`, fix `simps` ([#8429](https://github.com/leanprover-community/mathlib/pull/8429))
* Add `order_iso.add_left` and `order_iso.add_right`.
* Use `to_equiv :=` instead of `..` to ensure
  `rfl : (order_iso.mul_right a).to_equiv = equiv.mul_right a`.
* Simplify unapplied `(order_iso.mul_left a).symm` etc.
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* order_iso.mul_left_symm
- \+ *lemma* order_iso.mul_right_symm



## [2021-07-27 08:42:11](https://github.com/leanprover-community/mathlib/commit/391746b)
feat(data/zmod/basic): chinese remainder theorem ([#8356](https://github.com/leanprover-community/mathlib/pull/8356))
#### Estimated changes
Modified src/algebra/char_p/basic.lean


Modified src/algebra/ring/prod.lean
- \+ *def* ring_equiv.prod_zero_ring
- \+ *def* ring_equiv.zero_ring_prod

Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.left_inverse_of_right_inverse_of_card_le
- \+ *lemma* fintype.right_inverse_of_left_inverse_of_card_le

Modified src/data/int/cast.lean
- \+ *lemma* prod.fst_int_cast
- \+ *lemma* prod.snd_int_cast

Modified src/data/nat/cast.lean
- \+ *lemma* prod.fst_nat_cast
- \+ *lemma* prod.snd_nat_cast

Modified src/data/nat/gcd.lean
- \+ *lemma* nat.coprime.eq_of_mul_eq_zero
- \+ *lemma* nat.lcm_dvd_iff

Modified src/data/zmod/basic.lean
- \+ *lemma* prod.fst_zmod_cast
- \+ *lemma* prod.snd_zmod_cast
- \+/\- *lemma* zmod.card
- \+ *def* zmod.chinese_remainder



## [2021-07-27 08:42:10](https://github.com/leanprover-community/mathlib/commit/65006d2)
feat(linear_algebra/linear_independent): finsupp.total is not equal to a vector outside the support of the coefficients ([#8338](https://github.com/leanprover-community/mathlib/pull/8338))
…
#### Estimated changes
Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.mem_supported_support

Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.not_mem_span_image
- \+ *lemma* linear_independent.total_ne_of_not_mem_support



## [2021-07-27 08:42:09](https://github.com/leanprover-community/mathlib/commit/7e37f20)
feat(group_theory/perm/cycles): more lemmas ([#8175](https://github.com/leanprover-community/mathlib/pull/8175))
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* nsmul_inj_mod
- \+ *lemma* order_of_eq_zero_iff
- \+ *lemma* pow_inj_iff_of_order_of_eq_zero
- \+ *lemma* pow_inj_mod

Modified src/group_theory/perm/cycles.lean
- \+/\- *lemma* equiv.perm.cycle_factors_finset_eq_empty_iff
- \+/\- *lemma* equiv.perm.cycle_factors_finset_eq_singleton_iff
- \+/\- *lemma* equiv.perm.cycle_factors_finset_eq_singleton_self_iff
- \+ *lemma* equiv.perm.cycle_factors_finset_mul_inv_mem_eq_sdiff
- \+/\- *lemma* equiv.perm.cycle_factors_finset_noncomm_prod
- \+ *lemma* equiv.perm.cycle_factors_finset_one
- \+ *lemma* equiv.perm.cycle_of_apply_apply_gpow_self
- \+ *lemma* equiv.perm.cycle_of_apply_apply_pow_self
- \+ *lemma* equiv.perm.cycle_of_apply_apply_self
- \+ *lemma* equiv.perm.cycle_of_mem_cycle_factors_finset_iff
- \+ *lemma* equiv.perm.cycle_of_mul_of_apply_right_eq_self
- \+ *lemma* equiv.perm.disjoint.cycle_factors_finset_mul_eq_union
- \+ *lemma* equiv.perm.disjoint.cycle_of_mul_distrib
- \+ *lemma* equiv.perm.disjoint.disjoint_cycle_factors_finset
- \+ *lemma* equiv.perm.disjoint_mul_inv_of_mem_cycle_factors_finset
- \+ *lemma* equiv.perm.is_cycle.cycle_factors_finset_eq_singleton
- \+ *lemma* equiv.perm.is_cycle.exists_pow_eq_one
- \+ *lemma* equiv.perm.is_cycle.is_cycle_pow_pos_of_lt_prime_order
- \+ *lemma* equiv.perm.is_cycle.mem_support_pos_pow_iff_of_lt_order_of
- \+ *lemma* equiv.perm.is_cycle.pow_eq_one_iff
- \+ *lemma* equiv.perm.is_cycle.pow_iff
- \+ *lemma* equiv.perm.is_cycle.support_pow_eq_iff
- \+ *lemma* equiv.perm.is_cycle_of_is_cycle_pow
- \+ *lemma* equiv.perm.mem_cycle_factors_finset_support_le
- \+ *lemma* equiv.perm.mem_support_cycle_of_iff
- \+ *lemma* equiv.perm.nodup_of_pairwise_disjoint_cycles
- \+ *lemma* equiv.perm.not_is_cycle_one
- \+ *lemma* equiv.perm.pow_apply_eq_pow_mod_order_of_cycle_of_apply
- \+ *lemma* equiv.perm.same_cycle.nat''
- \+ *lemma* equiv.perm.same_cycle.nat'
- \+ *lemma* equiv.perm.same_cycle.nat
- \+ *lemma* equiv.perm.same_cycle.nat_of_mem_support
- \+ *lemma* equiv.perm.same_cycle_pow_left_iff
- \+ *lemma* equiv.perm.support_cycle_of_eq_nil_iff

Modified src/group_theory/perm/support.lean
- \+ *lemma* equiv.perm.disjoint.mono



## [2021-07-27 07:49:28](https://github.com/leanprover-community/mathlib/commit/d99788a)
feat(measure_theory/borel_space): lemmas about `is_pi_system_Ioo` and `finite_spanning_sets_in` ([#8434](https://github.com/leanprover-community/mathlib/pull/8434))
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_pi_system_Ioo
- \+ *lemma* is_pi_system_Ioo_mem
- \+ *def* real.finite_spanning_sets_in_Ioo_rat
- \+ *lemma* real.is_pi_system_Ioo_rat



## [2021-07-27 07:49:27](https://github.com/leanprover-community/mathlib/commit/eae3ead)
feat(topology/instances/ennreal): diameter of `s : set real` ([#8433](https://github.com/leanprover-community/mathlib/pull/8433))
#### Estimated changes
Modified src/data/real/basic.lean
- \+/\- *theorem* real.Inf_empty
- \+ *lemma* real.Inf_le_Sup
- \+/\- *theorem* real.Sup_empty
- \+ *lemma* real.add_neg_lt_Sup
- \- *lemma* real.add_pos_lt_Sup

Modified src/topology/instances/ennreal.lean
- \+ *lemma* metric.diam_closure
- \+ *lemma* real.diam_eq
- \+ *lemma* real.ediam_eq

Modified src/topology/instances/real.lean
- \+ *lemma* real.subset_Icc_Inf_Sup_of_bounded

Modified src/topology/metric_space/basic.lean




## [2021-07-27 06:14:26](https://github.com/leanprover-community/mathlib/commit/fb815d7)
feat(algebra/ring/basic): coercions of ring_hom.id ([#8439](https://github.com/leanprover-community/mathlib/pull/8439))
Two basic lemmas about the identity map as a ring hom, split off from [#3292](https://github.com/leanprover-community/mathlib/pull/3292) at @eric-wieser's suggestion.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* ring_hom.coe_add_monoid_hom_id
- \+ *lemma* ring_hom.coe_monoid_hom_id



## [2021-07-26 23:52:54](https://github.com/leanprover-community/mathlib/commit/e9309e3)
chore(data/equiv/list): rename `encodable.fintype.encodable` to `fintype.encodable` ([#8428](https://github.com/leanprover-community/mathlib/pull/8428))
#### Estimated changes
Modified src/data/equiv/list.lean


Modified src/measure_theory/measure_space.lean




## [2021-07-26 22:05:39](https://github.com/leanprover-community/mathlib/commit/26528b7)
chore(data/set): add a couple of lemmas ([#8430](https://github.com/leanprover-community/mathlib/pull/8430))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.subsingleton.preimage

Modified src/data/set/lattice.lean
- \+ *lemma* set.image_bUnion



## [2021-07-26 15:58:30](https://github.com/leanprover-community/mathlib/commit/0190177)
feat(group_theory/subgroup): eq_top_of_le_card and eq_bot_of_card_le ([#8414](https://github.com/leanprover-community/mathlib/pull/8414))
Slight strengthenings of the lemmas `eq_top_of_card_eq` and `eq_bot_of_card_eq`.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.eq_bot_of_card_le
- \+ *lemma* subgroup.eq_top_of_le_card



## [2021-07-26 15:58:29](https://github.com/leanprover-community/mathlib/commit/d8fc081)
chore(data/pnat/basic): rename `bot_eq_zero` to `bot_eq_one`, generalize from `Prop` to `Sort*` ([#8412](https://github.com/leanprover-community/mathlib/pull/8412))
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* pnat.bot_eq_one
- \- *lemma* pnat.bot_eq_zero
- \+ *def* pnat.case_strong_induction_on
- \- *lemma* pnat.case_strong_induction_on
- \+/\- *lemma* pnat.coe_le_coe
- \+/\- *lemma* pnat.coe_lt_coe
- \+/\- *lemma* pnat.exists_eq_succ_of_ne_one
- \+/\- *theorem* pnat.ne_zero
- \+/\- *def* pnat.rec_on
- \+/\- *theorem* pnat.rec_on_succ
- \+ *def* pnat.strong_induction_on
- \- *lemma* pnat.strong_induction_on



## [2021-07-26 15:58:28](https://github.com/leanprover-community/mathlib/commit/1dc4bef)
feat(ring_theory): shortcut lemmas for `coe : ideal R → fractional_ideal R⁰ K` ([#8395](https://github.com/leanprover-community/mathlib/pull/8395))
These results were already available, but in a less convenient form that e.g. asked you to prove an inclusion of submonoids `S ≤ R⁰`. Specializing them to the common case where the fractional ideal is in the field of fractions should save a bit of headache in the common cases.
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.coe_ideal_eq_zero_iff
- \+ *lemma* fractional_ideal.coe_ideal_injective
- \+ *lemma* fractional_ideal.coe_ideal_le_coe_ideal'
- \+ *lemma* fractional_ideal.coe_ideal_le_coe_ideal
- \+ *lemma* fractional_ideal.coe_ideal_ne_zero
- \+ *lemma* fractional_ideal.coe_ideal_ne_zero_iff



## [2021-07-26 15:58:27](https://github.com/leanprover-community/mathlib/commit/708b25d)
feat(ring_theory): (fractional) ideals are finitely generated if they are invertible ([#8294](https://github.com/leanprover-community/mathlib/pull/8294))
This is one of the three steps in showing `is_dedekind_domain_inv` implies `is_dedekind_domain`.
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.coe_ideal_fg
- \+ *lemma* fractional_ideal.fg_of_is_unit
- \+ *lemma* fractional_ideal.fg_unit
- \+ *lemma* fractional_ideal.mem_span_mul_finite_of_mem_mul
- \+ *lemma* ideal.fg_of_is_unit

Modified src/ring_theory/localization.lean
- \+ *lemma* is_localization.coe_submodule_fg



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
- \+ *lemma* finset.inf_univ_eq_infi
- \+ *lemma* finset.sup_univ_eq_supr



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
- \+ *lemma* matrix.det_pow



## [2021-07-25 07:06:29](https://github.com/leanprover-community/mathlib/commit/fff96e5)
feat(measure_theory/vector_measure): add partial order instance to vector measures ([#8410](https://github.com/leanprover-community/mathlib/pull/8410))
#### Estimated changes
Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/vector_measure.lean
- \+ *lemma* measure_theory.vector_measure.le_iff'
- \+ *lemma* measure_theory.vector_measure.le_iff



## [2021-07-24 22:55:28](https://github.com/leanprover-community/mathlib/commit/02b37b5)
feat(group_theory/subgroup): eq_bot_of_card_eq ([#8413](https://github.com/leanprover-community/mathlib/pull/8413))
Companion lemma to `eq_top_of_card_eq`.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.eq_bot_of_card_eq



## [2021-07-24 15:30:35](https://github.com/leanprover-community/mathlib/commit/8a0d5e0)
feat(group_theory/complement): define subgroup complement, prove Schur-Zassenhaus ([#8008](https://github.com/leanprover-community/mathlib/pull/8008))
Defines complements, and proves Schur-Zassenhaus for abelian normal subgroups.
#### Estimated changes
Added src/group_theory/complement.lean
- \+ *lemma* subgroup.diff_inv
- \+ *lemma* subgroup.diff_mul_diff
- \+ *lemma* subgroup.diff_self
- \+ *theorem* subgroup.exists_left_complement_of_coprime
- \+ *theorem* subgroup.exists_right_complement_of_coprime
- \+ *lemma* subgroup.exists_smul_eq
- \+ *lemma* subgroup.is_complement.exists_unique
- \+ *lemma* subgroup.is_complement.symm
- \+ *def* subgroup.is_complement
- \+ *lemma* subgroup.is_complement_comm
- \+ *lemma* subgroup.is_complement_iff_exists_unique
- \+ *lemma* subgroup.is_complement_of_coprime
- \+ *lemma* subgroup.is_complement_of_disjoint
- \+ *lemma* subgroup.is_complement_stabilizer_of_coprime
- \+ *def* subgroup.left_transversals
- \+ *lemma* subgroup.mem_left_transversals_iff_bijective
- \+ *lemma* subgroup.mem_left_transversals_iff_exists_unique_inv_mul_mem
- \+ *lemma* subgroup.mem_left_transversals_iff_exists_unique_quotient_mk'_eq
- \+ *lemma* subgroup.mem_right_transversals_iff_bijective
- \+ *lemma* subgroup.mem_right_transversals_iff_exists_unique_mul_inv_mem
- \+ *lemma* subgroup.mem_right_transversals_iff_exists_unique_quotient_mk'_eq
- \+ *def* subgroup.quotient_diff
- \+ *def* subgroup.right_transversals
- \+ *lemma* subgroup.smul_diff
- \+ *lemma* subgroup.smul_diff_smul
- \+ *lemma* subgroup.smul_injective
- \+ *lemma* subgroup.smul_symm_apply_eq_mul_symm_apply_inv_smul

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


Added src/data/set/pairwise.lean
- \+ *theorem* pairwise.mono
- \+ *theorem* pairwise.pairwise_on
- \+ *def* pairwise
- \+ *theorem* pairwise_disjoint_fiber
- \+ *theorem* pairwise_disjoint_on_bool
- \+ *theorem* pairwise_disjoint_on_nat
- \+ *theorem* pairwise_on_bool
- \+ *theorem* pairwise_on_nat
- \+ *theorem* set.pairwise_on.on_injective
- \+ *theorem* set.pairwise_on_univ

Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measurable_space_def.lean


Renamed src/data/set/disjointed.lean to src/order/disjointed.lean
- \- *theorem* pairwise.mono
- \- *theorem* pairwise.pairwise_on
- \- *def* pairwise
- \- *theorem* pairwise_disjoint_fiber
- \- *theorem* pairwise_disjoint_on_bool
- \- *theorem* pairwise_disjoint_on_nat
- \- *theorem* pairwise_on_bool
- \- *theorem* pairwise_on_nat
- \- *theorem* set.pairwise_on.on_injective
- \- *theorem* set.pairwise_on_univ

Modified src/order/partial_sups.lean


Modified src/ring_theory/coprime.lean


Modified src/topology/algebra/ordered/basic.lean




## [2021-07-23 17:15:08](https://github.com/leanprover-community/mathlib/commit/dfa95ab)
feat(analysis/normed_space/linear_isometry): add an upgrade from linear isometries between finite dimensional spaces of eq finrank to linear isometry equivs ([#8406](https://github.com/leanprover-community/mathlib/pull/8406))
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry.coe_to_linear_isometry_equiv
- \+ *lemma* linear_isometry.to_linear_isometry_equiv_apply



## [2021-07-23 11:58:54](https://github.com/leanprover-community/mathlib/commit/8062521)
feat(topology/locally_constant): Adding a module structure to locally constant functions ([#8384](https://github.com/leanprover-community/mathlib/pull/8384))
We add an A-module structure to locally constant functions from a topological space to a semiring A.
This also adds the lemmas `coe_zero`, `coe_add`, `coe_neg`, `coe_sub`, `coe_one`, `coe_mul`, `coe_div`, `coe_inv` to match the new `coe_smul` lemma.
#### Estimated changes
Modified src/topology/locally_constant/algebra.lean
- \+ *lemma* locally_constant.coe_div
- \+ *def* locally_constant.coe_fn_monoid_hom
- \+ *lemma* locally_constant.coe_inv
- \+ *lemma* locally_constant.coe_mul
- \+ *lemma* locally_constant.coe_one
- \+ *lemma* locally_constant.coe_smul
- \+/\- *lemma* locally_constant.inv_apply
- \+/\- *lemma* locally_constant.mul_apply
- \+/\- *lemma* locally_constant.one_apply
- \+ *lemma* locally_constant.smul_apply



## [2021-07-23 10:09:40](https://github.com/leanprover-community/mathlib/commit/f2f6228)
feat(set/basic): range_splitting f : range f → α ([#8340](https://github.com/leanprover-community/mathlib/pull/8340))
We use choice to provide an arbitrary injective splitting `range f → α` for any `f : α → β`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.apply_range_splitting
- \+ *lemma* set.comp_range_splitting
- \+ *lemma* set.left_inverse_range_splitting
- \+ *lemma* set.range_factorization_coe
- \+ *lemma* set.range_splitting_injective



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


Added test/instance_diamonds.lean




## [2021-07-23 09:02:52](https://github.com/leanprover-community/mathlib/commit/ced1f12)
feat(analysis/calculus): strictly differentiable (or C^1) map is locally Lipschitz ([#8362](https://github.com/leanprover-community/mathlib/pull/8362))
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_strict_fderiv_at.exists_lipschitz_on_with
- \+ *lemma* has_strict_fderiv_at.exists_lipschitz_on_with_of_nnnorm_lt

Modified src/analysis/calculus/mean_value.lean
- \+ *lemma* convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at
- \- *lemma* convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_continuous_within_at
- \+ *lemma* convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* has_ftaylor_series_up_to_on.exists_lipschitz_on_with
- \+ *lemma* has_ftaylor_series_up_to_on.exists_lipschitz_on_with_of_nnnorm_lt
- \+ *lemma* times_cont_diff_at.exists_lipschitz_on_with
- \+ *lemma* times_cont_diff_at.exists_lipschitz_on_with_of_nnnorm_lt
- \+ *lemma* times_cont_diff_within_at.exists_lipschitz_on_with

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* add_monoid_hom.lipschitz_of_bound
- \+ *lemma* add_monoid_hom.lipschitz_of_bound_nnnorm
- \+ *lemma* lipschitz_with_iff_norm_sub_le

Modified src/analysis/normed_space/operator_norm.lean
- \+ *theorem* continuous_linear_map.is_O_with_comp
- \+ *theorem* continuous_linear_map.is_O_with_id
- \+ *theorem* continuous_linear_map.is_O_with_sub
- \+ *theorem* continuous_linear_map.le_op_nnnorm
- \+/\- *theorem* continuous_linear_map.lipschitz
- \+ *lemma* linear_map.lipschitz_of_bound_nnnorm



## [2021-07-23 09:02:51](https://github.com/leanprover-community/mathlib/commit/1dafd0f)
feat(measure_theory/integrable_on): a monotone function is integrable on any compact subset ([#8336](https://github.com/leanprover-community/mathlib/pull/8336))
#### Estimated changes
Modified src/measure_theory/integrable_on.lean
- \+ *lemma* integrable_on_compact_of_antimono
- \+ *lemma* integrable_on_compact_of_antimono_on
- \+ *lemma* integrable_on_compact_of_monotone
- \+ *lemma* integrable_on_compact_of_monotone_on



## [2021-07-23 08:09:01](https://github.com/leanprover-community/mathlib/commit/970b17b)
refactor(topology/metric_space): move lemmas about `paracompact_space` and the shrinking lemma to separate files ([#8404](https://github.com/leanprover-community/mathlib/pull/8404))
Only a few files in `mathlib` actually depend on results about `paracompact_space`. With this refactor, only a few files depend on `topology/paracompact_space` and `topology/shrinking_lemma`. The main side effects are that `paracompact_of_emetric` and `normal_of_emetric` instances are not available without importing `topology.metric_space.emetric_paracompact` and the shrinking lemma for balls in a proper metric space is not available without `import topology.metric_space.shrinking_lemma`.
#### Estimated changes
Modified src/analysis/fourier.lean


Modified src/geometry/manifold/partition_of_unity.lean


Modified src/topology/metric_space/basic.lean
- \- *lemma* exists_Union_ball_eq_radius_lt
- \- *lemma* exists_Union_ball_eq_radius_pos_lt
- \- *lemma* exists_locally_finite_Union_eq_ball_radius_lt
- \- *lemma* exists_locally_finite_subset_Union_ball_radius_lt
- \- *lemma* exists_subset_Union_ball_radius_lt
- \- *lemma* exists_subset_Union_ball_radius_pos_lt

Added src/topology/metric_space/emetric_paracompact.lean


Modified src/topology/metric_space/emetric_space.lean


Added src/topology/metric_space/shrinking_lemma.lean
- \+ *lemma* exists_Union_ball_eq_radius_lt
- \+ *lemma* exists_Union_ball_eq_radius_pos_lt
- \+ *lemma* exists_locally_finite_Union_eq_ball_radius_lt
- \+ *lemma* exists_locally_finite_subset_Union_ball_radius_lt
- \+ *lemma* exists_subset_Union_ball_radius_lt
- \+ *lemma* exists_subset_Union_ball_radius_pos_lt



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
- \+ *lemma* measurable_set.cond
- \+ *lemma* measurable_set.symm_diff

Modified src/measure_theory/measure_space.lean
- \- *lemma* measurable_set.cond

Modified src/measure_theory/tactic.lean




## [2021-07-22 21:19:37](https://github.com/leanprover-community/mathlib/commit/0cbc6f3)
feat(linear_algebra/matrix/determinant): generalize det_fin_zero to det_eq_one_of_is_empty ([#8387](https://github.com/leanprover-community/mathlib/pull/8387))
Also golfs a nearby proof
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_eq_one_iff_nonempty_unique
- \+/\- *theorem* fintype.univ_of_is_empty
- \+ *lemma* univ_is_empty

Modified src/linear_algebra/matrix/determinant.lean
- \- *lemma* matrix.det_fin_zero
- \+ *lemma* matrix.det_is_empty



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
- \+ *lemma* algebra.bit0_smul_one'
- \+/\- *lemma* algebra.bit0_smul_one
- \+ *lemma* algebra.bit1_smul_one'
- \+/\- *lemma* algebra.bit1_smul_one



## [2021-07-22 16:15:20](https://github.com/leanprover-community/mathlib/commit/7cdd702)
chore(ring_theory): `set_like` instance for fractional ideals ([#8275](https://github.com/leanprover-community/mathlib/pull/8275))
This PR does a bit of cleanup in `fractional_ideal.lean` by using `set_like` to define `has_mem` and the coe to set.
As a bonus, it removes the `namespace ring` at the top of the file, that has been bugging me ever after I added it in the original fractional ideal PR.
#### Estimated changes
Modified docs/overview.yaml


Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.add_le_add_left
- \+ *def* fractional_ideal.adjoin_integral
- \+ *lemma* fractional_ideal.bot_eq_zero
- \+ *lemma* fractional_ideal.canonical_equiv_flip
- \+ *lemma* fractional_ideal.canonical_equiv_span_singleton
- \+ *lemma* fractional_ideal.canonical_equiv_symm
- \+ *lemma* fractional_ideal.coe_add
- \+ *lemma* fractional_ideal.coe_coe_ideal
- \+ *lemma* fractional_ideal.coe_div
- \+ *lemma* fractional_ideal.coe_fun_map_equiv
- \+ *lemma* fractional_ideal.coe_ideal_le_one
- \+ *lemma* fractional_ideal.coe_ideal_span_singleton
- \+ *lemma* fractional_ideal.coe_ideal_top
- \+ *lemma* fractional_ideal.coe_le_coe
- \+ *lemma* fractional_ideal.coe_map
- \+ *lemma* fractional_ideal.coe_mem_one
- \+ *lemma* fractional_ideal.coe_mk
- \+ *lemma* fractional_ideal.coe_mul
- \+ *lemma* fractional_ideal.coe_one
- \+ *lemma* fractional_ideal.coe_one_eq_coe_submodule_top
- \+ *lemma* fractional_ideal.coe_span_singleton
- \+ *lemma* fractional_ideal.coe_to_fractional_ideal_bot
- \+ *lemma* fractional_ideal.coe_to_fractional_ideal_eq_zero
- \+ *lemma* fractional_ideal.coe_to_fractional_ideal_injective
- \+ *lemma* fractional_ideal.coe_to_fractional_ideal_ne_zero
- \+ *lemma* fractional_ideal.coe_to_submodule_eq_bot
- \+ *lemma* fractional_ideal.coe_to_submodule_injective
- \+ *lemma* fractional_ideal.coe_to_submodule_ne_bot
- \+ *lemma* fractional_ideal.coe_zero
- \+ *lemma* fractional_ideal.div_nonzero
- \+ *lemma* fractional_ideal.div_one
- \+ *lemma* fractional_ideal.div_span_singleton
- \+ *lemma* fractional_ideal.div_zero
- \+ *theorem* fractional_ideal.eq_one_div_of_mul_eq_one
- \+ *lemma* fractional_ideal.eq_span_singleton_of_principal
- \+ *lemma* fractional_ideal.eq_zero_iff
- \+ *lemma* fractional_ideal.exists_eq_span_singleton_mul
- \+ *lemma* fractional_ideal.exists_mem_to_map_eq
- \+ *lemma* fractional_ideal.exists_ne_zero_mem_is_integer
- \+ *lemma* fractional_ideal.ext
- \+ *lemma* fractional_ideal.fractional_div_of_nonzero
- \+ *lemma* fractional_ideal.fractional_inf
- \+ *lemma* fractional_ideal.fractional_map
- \+ *lemma* fractional_ideal.fractional_mul
- \+ *lemma* fractional_ideal.fractional_sup
- \+ *lemma* fractional_ideal.is_fractional_adjoin_integral
- \+ *lemma* fractional_ideal.is_fractional_of_fg
- \+ *lemma* fractional_ideal.is_fractional_of_le
- \+ *lemma* fractional_ideal.is_fractional_of_le_one
- \+ *lemma* fractional_ideal.is_fractional_span_iff
- \+ *lemma* fractional_ideal.is_fractional_span_singleton
- \+ *theorem* fractional_ideal.is_noetherian
- \+ *lemma* fractional_ideal.is_noetherian_coe_to_fractional_ideal
- \+ *lemma* fractional_ideal.is_noetherian_iff
- \+ *lemma* fractional_ideal.is_noetherian_span_singleton_inv_to_map_mul
- \+ *lemma* fractional_ideal.is_noetherian_zero
- \+ *lemma* fractional_ideal.is_principal_iff
- \+ *lemma* fractional_ideal.le_div_iff_mul_le
- \+ *lemma* fractional_ideal.le_div_iff_of_nonzero
- \+ *lemma* fractional_ideal.le_one_iff_exists_coe_ideal
- \+ *lemma* fractional_ideal.le_self_mul_one_div
- \+ *lemma* fractional_ideal.le_self_mul_self
- \+ *lemma* fractional_ideal.le_zero_iff
- \+ *def* fractional_ideal.map
- \+ *lemma* fractional_ideal.map_add
- \+ *lemma* fractional_ideal.map_coe_ideal
- \+ *lemma* fractional_ideal.map_comp
- \+ *lemma* fractional_ideal.map_div
- \+ *lemma* fractional_ideal.map_eq_zero_iff
- \+ *def* fractional_ideal.map_equiv
- \+ *lemma* fractional_ideal.map_equiv_apply
- \+ *lemma* fractional_ideal.map_equiv_refl
- \+ *lemma* fractional_ideal.map_equiv_symm
- \+ *lemma* fractional_ideal.map_id
- \+ *lemma* fractional_ideal.map_map_symm
- \+ *lemma* fractional_ideal.map_mul
- \+ *lemma* fractional_ideal.map_ne_zero
- \+ *lemma* fractional_ideal.map_one
- \+ *lemma* fractional_ideal.map_one_div
- \+ *lemma* fractional_ideal.map_symm_map
- \+ *lemma* fractional_ideal.map_zero
- \+ *lemma* fractional_ideal.mem_adjoin_integral_self
- \+ *lemma* fractional_ideal.mem_canonical_equiv_apply
- \+ *lemma* fractional_ideal.mem_coe
- \+ *lemma* fractional_ideal.mem_coe_ideal
- \+ *lemma* fractional_ideal.mem_div_iff_of_nonzero
- \+ *lemma* fractional_ideal.mem_map
- \+ *lemma* fractional_ideal.mem_one_iff
- \+ *lemma* fractional_ideal.mem_singleton_mul
- \+ *lemma* fractional_ideal.mem_span_singleton
- \+ *lemma* fractional_ideal.mem_span_singleton_self
- \+ *lemma* fractional_ideal.mem_zero_iff
- \+ *def* fractional_ideal.mul
- \+ *theorem* fractional_ideal.mul_div_self_cancel_iff
- \+ *lemma* fractional_ideal.mul_eq_mul
- \+ *lemma* fractional_ideal.mul_le
- \+ *lemma* fractional_ideal.mul_le_mul_left
- \+ *lemma* fractional_ideal.mul_left_mono
- \+ *lemma* fractional_ideal.mul_mem_mul
- \+ *lemma* fractional_ideal.mul_one_div_le_one
- \+ *lemma* fractional_ideal.mul_right_mono
- \+ *lemma* fractional_ideal.mul_self_le_self
- \+ *lemma* fractional_ideal.ne_zero_of_mul_eq_one
- \+ *lemma* fractional_ideal.one_div_span_singleton
- \+ *lemma* fractional_ideal.one_mem_one
- \+ *def* fractional_ideal.span_singleton
- \+ *lemma* fractional_ideal.span_singleton_eq_zero_iff
- \+ *lemma* fractional_ideal.span_singleton_mul_span_singleton
- \+ *lemma* fractional_ideal.span_singleton_ne_zero_iff
- \+ *lemma* fractional_ideal.span_singleton_one
- \+ *lemma* fractional_ideal.span_singleton_zero
- \+ *lemma* fractional_ideal.sup_eq_add
- \+ *lemma* fractional_ideal.val_eq_coe
- \+ *lemma* fractional_ideal.zero_le
- \+ *def* fractional_ideal
- \+ *def* is_fractional
- \- *lemma* ring.fractional_ideal.add_le_add_left
- \- *def* ring.fractional_ideal.adjoin_integral
- \- *lemma* ring.fractional_ideal.bot_eq_zero
- \- *lemma* ring.fractional_ideal.canonical_equiv_flip
- \- *lemma* ring.fractional_ideal.canonical_equiv_span_singleton
- \- *lemma* ring.fractional_ideal.canonical_equiv_symm
- \- *lemma* ring.fractional_ideal.coe_add
- \- *lemma* ring.fractional_ideal.coe_coe_ideal
- \- *lemma* ring.fractional_ideal.coe_div
- \- *lemma* ring.fractional_ideal.coe_fun_map_equiv
- \- *lemma* ring.fractional_ideal.coe_ideal_le_one
- \- *lemma* ring.fractional_ideal.coe_ideal_span_singleton
- \- *lemma* ring.fractional_ideal.coe_ideal_top
- \- *lemma* ring.fractional_ideal.coe_injective
- \- *lemma* ring.fractional_ideal.coe_le_coe
- \- *lemma* ring.fractional_ideal.coe_map
- \- *lemma* ring.fractional_ideal.coe_mem_one
- \- *lemma* ring.fractional_ideal.coe_mk
- \- *lemma* ring.fractional_ideal.coe_mul
- \- *lemma* ring.fractional_ideal.coe_one
- \- *lemma* ring.fractional_ideal.coe_one_eq_coe_submodule_top
- \- *lemma* ring.fractional_ideal.coe_span_singleton
- \- *lemma* ring.fractional_ideal.coe_to_fractional_ideal_bot
- \- *lemma* ring.fractional_ideal.coe_to_fractional_ideal_eq_zero
- \- *lemma* ring.fractional_ideal.coe_to_fractional_ideal_injective
- \- *lemma* ring.fractional_ideal.coe_to_fractional_ideal_ne_zero
- \- *lemma* ring.fractional_ideal.coe_to_submodule_eq_bot
- \- *lemma* ring.fractional_ideal.coe_to_submodule_ne_bot
- \- *lemma* ring.fractional_ideal.coe_zero
- \- *lemma* ring.fractional_ideal.div_nonzero
- \- *lemma* ring.fractional_ideal.div_one
- \- *lemma* ring.fractional_ideal.div_span_singleton
- \- *lemma* ring.fractional_ideal.div_zero
- \- *theorem* ring.fractional_ideal.eq_one_div_of_mul_eq_one
- \- *lemma* ring.fractional_ideal.eq_span_singleton_of_principal
- \- *lemma* ring.fractional_ideal.eq_zero_iff
- \- *lemma* ring.fractional_ideal.exists_eq_span_singleton_mul
- \- *lemma* ring.fractional_ideal.exists_mem_to_map_eq
- \- *lemma* ring.fractional_ideal.exists_ne_zero_mem_is_integer
- \- *lemma* ring.fractional_ideal.ext
- \- *lemma* ring.fractional_ideal.ext_iff
- \- *lemma* ring.fractional_ideal.fractional_div_of_nonzero
- \- *lemma* ring.fractional_ideal.fractional_inf
- \- *lemma* ring.fractional_ideal.fractional_map
- \- *lemma* ring.fractional_ideal.fractional_mul
- \- *lemma* ring.fractional_ideal.fractional_of_subset_one
- \- *lemma* ring.fractional_ideal.fractional_sup
- \- *lemma* ring.fractional_ideal.is_fractional_adjoin_integral
- \- *lemma* ring.fractional_ideal.is_fractional_of_fg
- \- *lemma* ring.fractional_ideal.is_fractional_of_le
- \- *lemma* ring.fractional_ideal.is_fractional_span_iff
- \- *lemma* ring.fractional_ideal.is_fractional_span_singleton
- \- *theorem* ring.fractional_ideal.is_noetherian
- \- *lemma* ring.fractional_ideal.is_noetherian_coe_to_fractional_ideal
- \- *lemma* ring.fractional_ideal.is_noetherian_iff
- \- *lemma* ring.fractional_ideal.is_noetherian_span_singleton_inv_to_map_mul
- \- *lemma* ring.fractional_ideal.is_noetherian_zero
- \- *lemma* ring.fractional_ideal.is_principal_iff
- \- *lemma* ring.fractional_ideal.le_div_iff_mul_le
- \- *lemma* ring.fractional_ideal.le_div_iff_of_nonzero
- \- *lemma* ring.fractional_ideal.le_iff_mem
- \- *lemma* ring.fractional_ideal.le_one_iff_exists_coe_ideal
- \- *lemma* ring.fractional_ideal.le_self_mul_one_div
- \- *lemma* ring.fractional_ideal.le_self_mul_self
- \- *lemma* ring.fractional_ideal.le_zero_iff
- \- *def* ring.fractional_ideal.map
- \- *lemma* ring.fractional_ideal.map_add
- \- *lemma* ring.fractional_ideal.map_coe_ideal
- \- *lemma* ring.fractional_ideal.map_comp
- \- *lemma* ring.fractional_ideal.map_div
- \- *lemma* ring.fractional_ideal.map_eq_zero_iff
- \- *def* ring.fractional_ideal.map_equiv
- \- *lemma* ring.fractional_ideal.map_equiv_apply
- \- *lemma* ring.fractional_ideal.map_equiv_refl
- \- *lemma* ring.fractional_ideal.map_equiv_symm
- \- *lemma* ring.fractional_ideal.map_id
- \- *lemma* ring.fractional_ideal.map_map_symm
- \- *lemma* ring.fractional_ideal.map_mul
- \- *lemma* ring.fractional_ideal.map_ne_zero
- \- *lemma* ring.fractional_ideal.map_one
- \- *lemma* ring.fractional_ideal.map_one_div
- \- *lemma* ring.fractional_ideal.map_symm_map
- \- *lemma* ring.fractional_ideal.map_zero
- \- *lemma* ring.fractional_ideal.mem_adjoin_integral_self
- \- *lemma* ring.fractional_ideal.mem_canonical_equiv_apply
- \- *lemma* ring.fractional_ideal.mem_coe_ideal
- \- *lemma* ring.fractional_ideal.mem_div_iff_of_nonzero
- \- *lemma* ring.fractional_ideal.mem_map
- \- *lemma* ring.fractional_ideal.mem_one_iff
- \- *lemma* ring.fractional_ideal.mem_singleton_mul
- \- *lemma* ring.fractional_ideal.mem_span_singleton
- \- *lemma* ring.fractional_ideal.mem_span_singleton_self
- \- *lemma* ring.fractional_ideal.mem_zero_iff
- \- *def* ring.fractional_ideal.mul
- \- *theorem* ring.fractional_ideal.mul_div_self_cancel_iff
- \- *lemma* ring.fractional_ideal.mul_eq_mul
- \- *lemma* ring.fractional_ideal.mul_le
- \- *lemma* ring.fractional_ideal.mul_le_mul_left
- \- *lemma* ring.fractional_ideal.mul_left_mono
- \- *lemma* ring.fractional_ideal.mul_mem_mul
- \- *lemma* ring.fractional_ideal.mul_one_div_le_one
- \- *lemma* ring.fractional_ideal.mul_right_mono
- \- *lemma* ring.fractional_ideal.mul_self_le_self
- \- *lemma* ring.fractional_ideal.ne_zero_of_mul_eq_one
- \- *lemma* ring.fractional_ideal.one_div_span_singleton
- \- *lemma* ring.fractional_ideal.one_mem_one
- \- *def* ring.fractional_ideal.span_singleton
- \- *lemma* ring.fractional_ideal.span_singleton_eq_zero_iff
- \- *lemma* ring.fractional_ideal.span_singleton_mul_span_singleton
- \- *lemma* ring.fractional_ideal.span_singleton_ne_zero_iff
- \- *lemma* ring.fractional_ideal.span_singleton_one
- \- *lemma* ring.fractional_ideal.span_singleton_zero
- \- *lemma* ring.fractional_ideal.sup_eq_add
- \- *lemma* ring.fractional_ideal.val_eq_coe
- \- *lemma* ring.fractional_ideal.zero_le
- \- *def* ring.fractional_ideal
- \- *def* ring.is_fractional



## [2021-07-22 14:12:58](https://github.com/leanprover-community/mathlib/commit/38ac9ba)
chore(algebra/module/submodule): add submodule.coe_sum ([#8393](https://github.com/leanprover-community/mathlib/pull/8393))
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *lemma* submodule.coe_sum



## [2021-07-22 14:12:57](https://github.com/leanprover-community/mathlib/commit/e2cda0b)
chore(*): Prevent lemmas about the injectivity of `coe_fn` introducing un-reduced lambda terms ([#8386](https://github.com/leanprover-community/mathlib/pull/8386))
This follows on from [#6344](https://github.com/leanprover-community/mathlib/pull/6344), and fixes every result for `function.injective (λ` that is about coe_fn.
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+/\- *lemma* lie_hom.coe_injective
- \+/\- *lemma* lie_module_hom.coe_injective

Modified src/analysis/normed_space/enorm.lean
- \+/\- *lemma* enorm.coe_fn_injective

Modified src/data/equiv/basic.lean
- \+/\- *theorem* equiv.coe_fn_injective

Modified src/linear_algebra/affine_space/affine_map.lean
- \+/\- *lemma* affine_map.coe_fn_injective

Modified src/order/rel_iso.lean
- \+/\- *theorem* rel_iso.coe_fn_injective

Modified src/topology/algebra/module.lean
- \+/\- *theorem* continuous_linear_map.coe_fn_injective

Modified src/topology/locally_constant/basic.lean
- \+/\- *theorem* locally_constant.coe_injective



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
- \+ *def* add_action.of_End_hom
- \+ *def* add_action.to_End_hom
- \+ *lemma* function.End.smul_def
- \+ *def* mul_action.of_End_hom
- \+ *def* mul_action.to_End_hom

Modified src/group_theory/group_action/group.lean
- \+ *lemma* equiv.perm.smul_def



## [2021-07-22 11:40:10](https://github.com/leanprover-community/mathlib/commit/6f88eec)
feat(algebra/lie/{submodule,subalgebra}): `lie_span`, `coe` form a Galois insertion ([#8213](https://github.com/leanprover-community/mathlib/pull/8213))
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_subalgebra.span_Union
- \+ *lemma* lie_subalgebra.span_empty
- \+ *lemma* lie_subalgebra.span_union
- \+ *lemma* lie_subalgebra.span_univ

Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_submodule.span_Union
- \+ *lemma* lie_submodule.span_empty
- \+ *lemma* lie_submodule.span_union
- \+ *lemma* lie_submodule.span_univ



## [2021-07-22 07:37:52](https://github.com/leanprover-community/mathlib/commit/c9593dc)
feat(algebra/lie/direct_sum): define `direct_sum.lie_of`, `direct_sum.to_lie_algebra`, `direct_sum.lie_algebra_is_internal` ([#8369](https://github.com/leanprover-community/mathlib/pull/8369))
Various other minor improvements.
#### Estimated changes
Modified src/algebra/lie/direct_sum.lean
- \+/\- *def* direct_sum.lie_algebra_component
- \+ *lemma* direct_sum.lie_algebra_ext
- \+ *def* direct_sum.lie_algebra_is_internal
- \+/\- *def* direct_sum.lie_algebra_of
- \+ *lemma* direct_sum.lie_of
- \+ *lemma* direct_sum.lie_of_of_eq
- \+ *lemma* direct_sum.lie_of_of_ne
- \+ *def* direct_sum.to_lie_algebra

Modified src/linear_algebra/direct_sum_module.lean
- \+ *lemma* direct_sum.coe_to_module_eq_coe_to_add_monoid



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
- \+/\- *def* complete_graph
- \+/\- *def* empty_graph
- \+ *lemma* simple_graph.bot_adj
- \- *def* simple_graph.compl
- \+/\- *lemma* simple_graph.compl_adj
- \- *lemma* simple_graph.compl_compl
- \- *lemma* simple_graph.compl_involutive
- \+ *lemma* simple_graph.complete_graph_eq_top
- \+ *lemma* simple_graph.empty_graph_eq_bot
- \+ *lemma* simple_graph.inf_adj
- \+ *def* simple_graph.is_subgraph
- \+ *lemma* simple_graph.is_subgraph_eq_le
- \+ *lemma* simple_graph.sdiff_adj
- \+ *lemma* simple_graph.sup_adj
- \+ *lemma* simple_graph.top_adj

Modified src/combinatorics/simple_graph/strongly_regular.lean


Modified src/combinatorics/simple_graph/subgraph.lean
- \+/\- *def* simple_graph.subgraph.bot_equiv
- \+/\- *def* simple_graph.subgraph.is_subgraph
- \+ *lemma* simple_graph.subgraph.spanning_coe.is_subgraph_of_is_subgraph
- \+ *def* simple_graph.subgraph.spanning_coe
- \+ *lemma* simple_graph.subgraph.spanning_coe_adj_sub
- \+ *def* simple_graph.subgraph.spanning_coe_equiv_coe_of_spanning
- \+ *lemma* simple_graph.to_subgraph.is_spanning
- \+ *def* simple_graph.to_subgraph



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
Added src/analysis/calculus/conformal.lean
- \+ *lemma* conformal.comp
- \+ *lemma* conformal.conformal_at
- \+ *lemma* conformal.const_smul
- \+ *lemma* conformal.differentiable
- \+ *def* conformal
- \+ *lemma* conformal_at.comp
- \+ *def* conformal_at.conformal_factor_at
- \+ *lemma* conformal_at.conformal_factor_at_inner_eq_mul_inner'
- \+ *lemma* conformal_at.conformal_factor_at_inner_eq_mul_inner
- \+ *lemma* conformal_at.conformal_factor_at_pos
- \+ *lemma* conformal_at.congr
- \+ *lemma* conformal_at.const_smul
- \+ *lemma* conformal_at.differentiable_at
- \+ *lemma* conformal_at.preserves_angle
- \+ *def* conformal_at
- \+ *lemma* conformal_at_const_smul
- \+ *lemma* conformal_at_id
- \+ *lemma* conformal_at_iff'
- \+ *lemma* conformal_at_iff
- \+ *lemma* conformal_at_iff_is_conformal_map_fderiv
- \+ *lemma* conformal_const_smul
- \+ *lemma* conformal_id

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at_of_subsingleton

Added src/analysis/normed_space/conformal_linear_map.lean
- \+ *lemma* is_conformal_map.comp
- \+ *lemma* is_conformal_map.injective
- \+ *lemma* is_conformal_map.preserves_angle
- \+ *def* is_conformal_map
- \+ *lemma* is_conformal_map_const_smul
- \+ *lemma* is_conformal_map_id
- \+ *lemma* is_conformal_map_iff
- \+ *lemma* is_conformal_map_of_subsingleton

Added src/geometry/manifold/conformal_groupoid.lean
- \+ *def* conformal_groupoid
- \+ *def* conformal_pregroupoid



## [2021-07-20 20:10:32](https://github.com/leanprover-community/mathlib/commit/899bb5f)
feat(data/multiset): `(s.erase x).map f = (s.map f).erase (f x)` ([#8375](https://github.com/leanprover-community/mathlib/pull/8375))
A little lemma that I needed for Dedekind domains.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.map_erase



## [2021-07-20 18:13:44](https://github.com/leanprover-community/mathlib/commit/4676b31)
feat(data/sym2): add the universal property, and make `sym2.is_diag ⟦(x, y)⟧ ↔ x = y` true definitionally ([#8358](https://github.com/leanprover-community/mathlib/pull/8358))
#### Estimated changes
Modified src/data/sym2.lean
- \+ *lemma* sym2.coe_lift_symm_apply
- \+ *lemma* sym2.is_diag.mem_range_diag
- \+/\- *def* sym2.is_diag
- \+ *lemma* sym2.is_diag_iff_eq
- \+ *lemma* sym2.is_diag_iff_mem_range_diag
- \+ *def* sym2.lift
- \+ *lemma* sym2.lift_mk



## [2021-07-20 16:22:25](https://github.com/leanprover-community/mathlib/commit/6ac3059)
feat(combinatorics/colex): golf and generalise ([#8301](https://github.com/leanprover-community/mathlib/pull/8301))
Miscellaneous fixes about colex: Gives `le` versions of some `lt` lemmas, fixes a TODO, restores some names etc.
#### Estimated changes
Modified src/combinatorics/colex.lean
- \+ *lemma* colex.colex_le_of_subset
- \+ *lemma* colex.colex_lt_of_ssubset
- \+ *lemma* colex.empty_to_colex_le
- \+ *lemma* colex.empty_to_colex_lt
- \- *lemma* colex.hom
- \- *lemma* colex.hom_fin
- \+ *lemma* colex.hom_fin_le_iff
- \+ *lemma* colex.hom_fin_lt_iff
- \+ *lemma* colex.hom_le_iff
- \+ *lemma* colex.hom_lt_iff
- \+/\- *lemma* colex.lt_singleton_iff_mem_lt
- \+ *lemma* colex.sdiff_le_sdiff_iff_le
- \+ *lemma* colex.singleton_le_iff_le
- \- *lemma* colex.sum_sq_lt_iff_lt
- \+ *lemma* colex.sum_two_pow_le_iff_lt
- \+ *lemma* colex.sum_two_pow_lt_iff_lt
- \+ *def* colex.to_colex_rel_hom
- \- *lemma* nat.sum_sq_lt
- \+ *lemma* nat.sum_two_pow_lt



## [2021-07-20 11:23:09](https://github.com/leanprover-community/mathlib/commit/ed8d597)
fix(data/matrix/basic): remove an accidental requirement for a matrix to be square ([#8372](https://github.com/leanprover-community/mathlib/pull/8372))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *theorem* matrix.mul_apply'



## [2021-07-20 10:51:34](https://github.com/leanprover-community/mathlib/commit/fce38f1)
feat(ring_theory): define `fractional_ideal.adjoin_integral` ([#8296](https://github.com/leanprover-community/mathlib/pull/8296))
This PR shows if `x` is integral over `R`, then `R[x]` is a fractional ideal, and proves some of the essential properties of this fractional ideal.
This is an important step towards showing `is_dedekind_domain_inv` implies that the ring is integrally closed.
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *def* ring.fractional_ideal.adjoin_integral
- \+ *lemma* ring.fractional_ideal.is_fractional_adjoin_integral
- \+ *lemma* ring.fractional_ideal.mem_adjoin_integral_self



## [2021-07-20 09:52:16](https://github.com/leanprover-community/mathlib/commit/c05c15f)
feat(group_theory/order_of_element): pow_eq_mod_card ([#8354](https://github.com/leanprover-community/mathlib/pull/8354))
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* gpow_eq_mod_card
- \+ *lemma* pow_eq_mod_card



## [2021-07-20 08:59:36](https://github.com/leanprover-community/mathlib/commit/0f9b754)
feat(measure_theory/borel_space): generalize `monotone.measurable` to monotone on set ([#8365](https://github.com/leanprover-community/mathlib/pull/8365))
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* ae_measurable_restrict_of_antimono_on
- \+ *lemma* ae_measurable_restrict_of_monotone_on
- \+/\- *lemma* measurable_of_antimono
- \+/\- *lemma* measurable_of_monotone



## [2021-07-20 08:59:35](https://github.com/leanprover-community/mathlib/commit/1589318)
feat(topology/continuous_function/bounded): prove `norm_eq_supr_norm` ([#8288](https://github.com/leanprover-community/mathlib/pull/8288))
More precisely we prove both:
 * `bounded_continuous_function.norm_eq_supr_norm`
 * `continuous_map.norm_eq_supr_norm`
We also introduce one new definition: `bounded_continuous_function.norm_comp`.
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.bdd_above_range_norm_comp
- \+ *lemma* bounded_continuous_function.coe_norm_comp
- \+ *def* bounded_continuous_function.norm_comp
- \+ *lemma* bounded_continuous_function.norm_eq_of_nonempty
- \+ *lemma* bounded_continuous_function.norm_eq_supr_norm
- \+ *lemma* bounded_continuous_function.norm_eq_zero_of_empty
- \+ *lemma* bounded_continuous_function.norm_norm_comp

Modified src/topology/continuous_function/compact.lean
- \+ *lemma* bounded_continuous_function.norm_forget_boundedness_eq
- \+ *lemma* continuous_map.norm_eq_supr_norm



## [2021-07-20 08:59:34](https://github.com/leanprover-community/mathlib/commit/f5d25b4)
feat(measure_theory/vector_measure): introduce vector-valued measures ([#8247](https://github.com/leanprover-community/mathlib/pull/8247))
This PR introduces vector-valued measures and provides a method of creating signed measures without the summability requirement.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* real.norm_of_nonpos

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.coe_smul
- \+ *lemma* ennreal.to_real_smul

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.summable_measure_to_real

Added src/measure_theory/vector_measure.lean
- \+ *def* measure_theory.measure.sub_to_signed_measure
- \+ *lemma* measure_theory.measure.sub_to_signed_measure_apply
- \+ *def* measure_theory.measure.to_ennreal_vector_measure
- \+ *lemma* measure_theory.measure.to_ennreal_vector_measure_add
- \+ *lemma* measure_theory.measure.to_ennreal_vector_measure_apply_measurable
- \+ *lemma* measure_theory.measure.to_ennreal_vector_measure_zero
- \+ *def* measure_theory.measure.to_signed_measure
- \+ *lemma* measure_theory.measure.to_signed_measure_add
- \+ *lemma* measure_theory.measure.to_signed_measure_apply_measurable
- \+ *lemma* measure_theory.measure.to_signed_measure_smul
- \+ *lemma* measure_theory.measure.to_signed_measure_zero
- \+ *def* measure_theory.vector_measure.add
- \+ *lemma* measure_theory.vector_measure.add_apply
- \+ *lemma* measure_theory.vector_measure.coe_add
- \+ *def* measure_theory.vector_measure.coe_fn_add_monoid_hom
- \+ *lemma* measure_theory.vector_measure.coe_injective
- \+ *lemma* measure_theory.vector_measure.coe_neg
- \+ *lemma* measure_theory.vector_measure.coe_smul
- \+ *lemma* measure_theory.vector_measure.coe_sub
- \+ *lemma* measure_theory.vector_measure.coe_zero
- \+ *lemma* measure_theory.vector_measure.empty
- \+ *lemma* measure_theory.vector_measure.ext
- \+ *lemma* measure_theory.vector_measure.ext_iff'
- \+ *lemma* measure_theory.vector_measure.ext_iff
- \+ *lemma* measure_theory.vector_measure.has_sum_of_disjoint_Union
- \+ *lemma* measure_theory.vector_measure.m_Union
- \+ *lemma* measure_theory.vector_measure.measure_of_eq_coe
- \+ *def* measure_theory.vector_measure.neg
- \+ *lemma* measure_theory.vector_measure.neg_apply
- \+ *lemma* measure_theory.vector_measure.not_measurable
- \+ *lemma* measure_theory.vector_measure.of_Union_nonneg
- \+ *lemma* measure_theory.vector_measure.of_Union_nonpos
- \+ *lemma* measure_theory.vector_measure.of_add_of_diff
- \+ *lemma* measure_theory.vector_measure.of_diff
- \+ *lemma* measure_theory.vector_measure.of_disjoint_Union
- \+ *lemma* measure_theory.vector_measure.of_disjoint_Union_nat
- \+ *lemma* measure_theory.vector_measure.of_nonneg_disjoint_union_eq_zero
- \+ *lemma* measure_theory.vector_measure.of_nonpos_disjoint_union_eq_zero
- \+ *lemma* measure_theory.vector_measure.of_union
- \+ *def* measure_theory.vector_measure.smul
- \+ *lemma* measure_theory.vector_measure.smul_apply
- \+ *def* measure_theory.vector_measure.sub
- \+ *lemma* measure_theory.vector_measure.sub_apply
- \+ *lemma* measure_theory.vector_measure.zero_apply

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.summable_to_real

Modified src/topology/instances/nnreal.lean




## [2021-07-20 07:56:49](https://github.com/leanprover-community/mathlib/commit/0f58e13)
chore(topology/continuous_function, analysis/normed_space): use `is_empty α` instead of `¬nonempty α` ([#8352](https://github.com/leanprover-community/mathlib/pull/8352))
Two lemmas with their assumptions changed, and some proofs golfed using the new forms of these and other lemmas.
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \+/\- *lemma* continuous_multilinear_map.norm_mk_pi_algebra_of_empty

Modified src/order/filter/at_top_bot.lean


Modified src/topology/continuous_function/bounded.lean
- \+/\- *lemma* bounded_continuous_function.dist_zero_of_empty



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
- \+ *def* homology_iso_cokernel_image_to_kernel'
- \+ *def* homology_iso_cokernel_lift
- \+ *lemma* image_subobject_iso_image_to_kernel'
- \+ *def* image_to_kernel'
- \+ *lemma* image_to_kernel'_kernel_subobject_iso



## [2021-07-19 22:25:50](https://github.com/leanprover-community/mathlib/commit/11af02c)
feat(analysis/convex): convex sets with zero ([#8234](https://github.com/leanprover-community/mathlib/pull/8234))
Split off from [#7288](https://github.com/leanprover-community/mathlib/pull/7288)
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex.mem_smul_of_zero_mem
- \+ *lemma* convex.smul_mem_of_zero_mem



## [2021-07-19 22:25:49](https://github.com/leanprover-community/mathlib/commit/0821e6e)
feat(category_theory/limits): strict initial objects ([#8094](https://github.com/leanprover-community/mathlib/pull/8094))
- [x] depends on: [#8084](https://github.com/leanprover-community/mathlib/pull/8084)
[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/from-referrer/)
#### Estimated changes
Added src/category_theory/limits/shapes/strict_initial.lean
- \+ *lemma* category_theory.limits.has_strict_initial_objects_of_initial_is_strict
- \+ *lemma* category_theory.limits.initial.hom_ext
- \+ *lemma* category_theory.limits.initial.subsingleton_to
- \+ *lemma* category_theory.limits.initial_mul_inv
- \+ *lemma* category_theory.limits.is_initial.is_iso_to
- \+ *lemma* category_theory.limits.is_initial.strict_hom_ext
- \+ *lemma* category_theory.limits.is_initial.subsingleton_to
- \+ *lemma* category_theory.limits.is_initial_mul_inv
- \+ *lemma* category_theory.limits.mul_initial_inv
- \+ *lemma* category_theory.limits.mul_is_initial_inv



## [2021-07-19 19:25:13](https://github.com/leanprover-community/mathlib/commit/afd0f92)
feat(category_theory/limits/pullbacks): generalise pullback mono lemmas ([#8302](https://github.com/leanprover-community/mathlib/pull/8302))
Generalises results to use `is_limit` rather than the canonical limit.
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* category_theory.limits.pullback_cone.mono_fst_of_is_pullback_of_mono
- \+ *lemma* category_theory.limits.pullback_cone.mono_snd_of_is_pullback_of_mono
- \+ *lemma* category_theory.limits.pushout_cocone.epi_inl_of_is_pushout_of_epi
- \+ *lemma* category_theory.limits.pushout_cocone.epi_inr_of_is_pushout_of_epi



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
- \+ *theorem* equiv.of_injective_symm_apply

Modified src/linear_algebra/finsupp.lean
- \+/\- *theorem* finsupp.total_emb_domain
- \+ *theorem* finsupp.total_equiv_map_domain
- \+ *lemma* span.finsupp_total_repr
- \+ *def* span.repr

Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.span_repr_eq
- \+/\- *def* linear_independent.total_equiv
- \+/\- *lemma* linear_independent.total_repr



## [2021-07-19 13:17:09](https://github.com/leanprover-community/mathlib/commit/02ecb62)
feat(analysis/fourier): span of monomials is dense in L^p ([#8328](https://github.com/leanprover-community/mathlib/pull/8328))
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/analysis/fourier.lean
- \+/\- *lemma* orthonormal_fourier
- \+ *lemma* span_fourier_Lp_closure_eq_top
- \+/\- *lemma* span_fourier_closure_eq_top

Modified src/measure_theory/continuous_map_dense.lean


Modified src/topology/algebra/group.lean
- \+ *lemma* dense_range.topological_closure_map_subgroup
- \+ *lemma* subgroup.topological_closure_coe

Modified src/topology/algebra/module.lean
- \+ *lemma* dense_range.topological_closure_map_submodule



## [2021-07-19 12:28:13](https://github.com/leanprover-community/mathlib/commit/5ccf2bf)
feat(topology/metric_space/basic): an order-bounded set is metric-bounded ([#8335](https://github.com/leanprover-community/mathlib/pull/8335))
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* is_compact.bounded
- \+ *lemma* metric.bounded_Icc
- \+ *lemma* metric.bounded_Ico
- \+ *lemma* metric.bounded_Ioc
- \+ *lemma* metric.bounded_Ioo
- \+ *lemma* metric.bounded_of_bdd_above_of_bdd_below
- \- *lemma* metric.bounded_of_compact
- \+ *lemma* totally_bounded.bounded

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
- \+/\- *lemma* exists_between
- \+/\- *lemma* le_update_iff
- \+/\- *def* monotone
- \+/\- *theorem* monotone_app
- \+/\- *theorem* monotone_const
- \+/\- *theorem* monotone_id
- \+/\- *theorem* monotone_lam
- \+/\- *lemma* monotone_of_monotone_nat
- \+/\- *lemma* no_bot
- \+/\- *lemma* no_top
- \+/\- *def* order.preimage
- \+/\- *def* order_dual
- \+/\- *lemma* pi.le_def
- \+/\- *lemma* pi.lt_def
- \+/\- *lemma* update_le_iff
- \+/\- *lemma* update_le_update_iff



## [2021-07-19 02:21:30](https://github.com/leanprover-community/mathlib/commit/6a20dd6)
chore(scripts): update nolints.txt ([#8366](https://github.com/leanprover-community/mathlib/pull/8366))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-07-18 22:22:27](https://github.com/leanprover-community/mathlib/commit/ee60711)
feat(data/finset/basic): product, bUnion, sdiff lemmas ([#8321](https://github.com/leanprover-community/mathlib/pull/8321))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.bUnion_bUnion
- \+ *lemma* finset.bUnion_subset_iff_forall_subset
- \+ *lemma* finset.product_bUnion
- \+ *lemma* finset.sdiff_ssubset

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
- \+ *lemma* meas_closure_of_null_bdry
- \+ *lemma* meas_interior_of_null_bdry

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.meas_eq_meas_larger_of_between_null_diff
- \+ *lemma* measure_theory.meas_eq_meas_of_between_null_diff
- \+ *lemma* measure_theory.meas_eq_meas_of_null_diff
- \+ *lemma* measure_theory.meas_eq_meas_smaller_of_between_null_diff



## [2021-07-18 17:02:28](https://github.com/leanprover-community/mathlib/commit/048263d)
feat(topology/basic): add two lemmas about frontier and two lemmas about preimages under continuous maps ([#8329](https://github.com/leanprover-community/mathlib/pull/8329))
Adding four lemmas: `frontier_eq_inter_compl_interior`, `compl_frontier_eq_union_interior`, `continuous.closure_preimage_subset`, `continuous.frontier_preimage_subset` to `topology/basic`.
These were discussed on Zulip <https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Portmanteau.20theorem/near/246037950>. The formulations closely follow Patrick's suggestions.
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* compl_frontier_eq_union_interior
- \+ *lemma* continuous.closure_preimage_subset
- \+ *lemma* continuous.frontier_preimage_subset
- \+ *lemma* frontier_eq_inter_compl_interior



## [2021-07-18 15:12:25](https://github.com/leanprover-community/mathlib/commit/865e36b)
chore(order/boolean_algebra) : `compl_involutive` ([#8357](https://github.com/leanprover-community/mathlib/pull/8357))
#### Estimated changes
Modified src/order/boolean_algebra.lean
- \+ *theorem* compl_bijective
- \+ *theorem* compl_involutive



## [2021-07-17 21:38:09](https://github.com/leanprover-community/mathlib/commit/f45df47)
feat(measure_theory/hausdorff_measure): `dimH_{s,b,}Union`, `dimH_union` ([#8351](https://github.com/leanprover-community/mathlib/pull/8351))
#### Estimated changes
Modified src/measure_theory/hausdorff_measure.lean
- \+ *lemma* measure_theory.dimH_Union
- \+ *lemma* measure_theory.dimH_bUnion
- \+ *lemma* measure_theory.dimH_mono
- \+ *lemma* measure_theory.dimH_sUnion
- \+ *lemma* measure_theory.dimH_union
- \+ *lemma* measure_theory.le_dimH_of_hausdorff_measure_eq_top



## [2021-07-17 19:58:11](https://github.com/leanprover-community/mathlib/commit/ad5afc2)
feat(combinatorics/hales_jewett): Hales-Jewett and Van der Waerden ([#8019](https://github.com/leanprover-community/mathlib/pull/8019))
Proves the Hales-Jewett theorem (a fundamental result in Ramsey theory on combinatorial lines) and deduces (a generalised version of) Van der Waerden's theorem on arithmetic progressions.
#### Estimated changes
Added src/combinatorics/hales_jewett.lean
- \+ *theorem* combinatorics.exists_mono_homothetic_copy
- \+ *lemma* combinatorics.line.apply
- \+ *lemma* combinatorics.line.apply_none
- \+ *lemma* combinatorics.line.apply_of_ne_none
- \+ *def* combinatorics.line.diagonal
- \+ *lemma* combinatorics.line.diagonal_apply
- \+ *theorem* combinatorics.line.exists_mono_in_high_dimension
- \+ *def* combinatorics.line.horizontal
- \+ *lemma* combinatorics.line.horizontal_apply
- \+ *def* combinatorics.line.is_mono
- \+ *def* combinatorics.line.map
- \+ *lemma* combinatorics.line.map_apply
- \+ *def* combinatorics.line.prod
- \+ *lemma* combinatorics.line.prod_apply
- \+ *def* combinatorics.line.vertical
- \+ *lemma* combinatorics.line.vertical_apply

Modified src/data/list/basic.lean


Modified src/data/option/basic.lean
- \+ *lemma* option.get_or_else_map
- \+ *lemma* option.get_or_else_none



## [2021-07-17 17:47:12](https://github.com/leanprover-community/mathlib/commit/398027d)
feat(topology/subset_properties): add `countable_cover_nhds_within_of_sigma_compact` ([#8350](https://github.com/leanprover-community/mathlib/pull/8350))
This is a version of `countable_cover_nhds_of_sigma_compact` for a
covering of a closed set instead of the whole space.
#### Estimated changes
Modified src/topology/subset_properties.lean
- \+ *lemma* countable_cover_nhds_within_of_sigma_compact
- \+ *lemma* exists_mem_compact_covering



## [2021-07-17 17:47:11](https://github.com/leanprover-community/mathlib/commit/7d754e0)
chore(analysis/calculus/mean_value): use `nnnorm` in a few lemmas ([#8348](https://github.com/leanprover-community/mathlib/pull/8348))
Use `nnnorm` instead of `norm` and `C : nnreal` in lemmas about `lipschitz_on_with`. This way we can use them to prove any statement of the form `lipschitz_on_with C f s`, not only something of the form `lipschitz_on_with (real.to_nnreal C) f s`.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean
- \+ *lemma* convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_continuous_within_at
- \+ *theorem* convex.lipschitz_on_with_of_nnnorm_deriv_le
- \+ *theorem* convex.lipschitz_on_with_of_nnnorm_deriv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_nnnorm_fderiv_le
- \+ *theorem* convex.lipschitz_on_with_of_nnnorm_fderiv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_nnnorm_has_deriv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_nnnorm_has_fderiv_within_le
- \- *theorem* convex.lipschitz_on_with_of_norm_deriv_le
- \- *theorem* convex.lipschitz_on_with_of_norm_deriv_within_le
- \- *theorem* convex.lipschitz_on_with_of_norm_fderiv_le
- \- *theorem* convex.lipschitz_on_with_of_norm_fderiv_within_le
- \- *theorem* convex.lipschitz_on_with_of_norm_has_deriv_within_le
- \- *theorem* convex.lipschitz_on_with_of_norm_has_fderiv_within_le

Modified src/analysis/calculus/parametric_integral.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.nnnorm_smul_right_apply

Modified src/data/real/nnreal.lean




## [2021-07-17 16:55:13](https://github.com/leanprover-community/mathlib/commit/3782c19)
feat(topology/algebra/ordered): add `nhds_top_basis_Ici` and `nhds_bot_basis_Iic` ([#8349](https://github.com/leanprover-community/mathlib/pull/8349))
Also add `ennreal.nhds_zero_basis_Iic` and `ennreal.supr_div`.
#### Estimated changes
Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* nhds_bot_basis_Iic
- \+ *lemma* nhds_top_basis_Ici

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.nhds_zero_basis_Iic
- \+ *lemma* ennreal.supr_div



## [2021-07-17 16:20:16](https://github.com/leanprover-community/mathlib/commit/8139d7e)
feat(measure_theory/hausdorff_measure): μH and dimH of a `subsingleton` ([#8347](https://github.com/leanprover-community/mathlib/pull/8347))
#### Estimated changes
Modified src/measure_theory/hausdorff_measure.lean
- \+ *lemma* measure_theory.dimH_empty
- \+ *lemma* measure_theory.dimH_singleton
- \+ *lemma* measure_theory.dimH_subsingleton

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure_subsingleton



## [2021-07-17 14:00:00](https://github.com/leanprover-community/mathlib/commit/fcde3f0)
chore(data/real/ennreal): move `x ≠ 0` case of `mul_infi` to `mul_infi_of_ne` ([#8345](https://github.com/leanprover-community/mathlib/pull/8345))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.infi_mul_of_ne
- \+ *lemma* ennreal.mul_infi_of_ne



## [2021-07-17 13:14:10](https://github.com/leanprover-community/mathlib/commit/bd56531)
chore(analysis/normed_space/operator_norm): use `norm_one_class` ([#8346](https://github.com/leanprover-community/mathlib/pull/8346))
* turn `continuous_linear_map.norm_id` into a `simp` lemma;
* drop its particular case `continuous_linear_map.norm_id_field`;
* replace `continuous_linear_map.norm_id_field'` with a
  `norm_one_class` instance.
#### Estimated changes
Modified src/analysis/calculus/parametric_integral.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* continuous_linear_map.norm_id
- \- *lemma* continuous_linear_map.norm_id_field'
- \- *lemma* continuous_linear_map.norm_id_field
- \+/\- *lemma* continuous_linear_map.norm_id_of_nontrivial_seminorm



## [2021-07-17 11:26:47](https://github.com/leanprover-community/mathlib/commit/93a3764)
chore(algebra/ring/basic): drop commutativity assumptions from some division lemmas ([#8334](https://github.com/leanprover-community/mathlib/pull/8334))
* Removes `dvd_neg_iff_dvd`, `neg_dvd_iff_dvd` which duplicated `dvd_neg`, `neg_dvd`.
* Generalizes `two_dvd_bit0` to non-commutative semirings.
* Generalizes a bunch of lemmas from `comm_ring` to `ring`.
* Adds `even_neg` for `ring` to replace `int.even_neg`.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \- *theorem* dvd_neg_iff_dvd
- \+ *theorem* even_neg
- \- *theorem* neg_dvd_iff_dvd

Modified src/data/int/basic.lean


Modified src/data/int/parity.lean
- \- *theorem* int.even_neg



## [2021-07-17 09:38:56](https://github.com/leanprover-community/mathlib/commit/d4c0a11)
refactor(analysis/analytic/basic): refactor `change_origin` ([#8282](https://github.com/leanprover-community/mathlib/pull/8282))
Now each term of `change_origin` is defined as a sum of a formal power series, so it is clear that each term is an analytic function.
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+/\- *theorem* formal_multilinear_series.change_origin_eval
- \- *lemma* formal_multilinear_series.change_origin_has_sum
- \+ *def* formal_multilinear_series.change_origin_index_equiv
- \+/\- *lemma* formal_multilinear_series.change_origin_radius
- \+ *def* formal_multilinear_series.change_origin_series
- \+ *lemma* formal_multilinear_series.change_origin_series_summable_aux₁
- \+ *lemma* formal_multilinear_series.change_origin_series_summable_aux₂
- \+ *lemma* formal_multilinear_series.change_origin_series_summable_aux₃
- \+ *def* formal_multilinear_series.change_origin_series_term
- \+ *lemma* formal_multilinear_series.change_origin_series_term_apply
- \- *lemma* formal_multilinear_series.change_origin_summable_aux1
- \- *lemma* formal_multilinear_series.change_origin_summable_aux2
- \- *lemma* formal_multilinear_series.change_origin_summable_aux3
- \- *def* formal_multilinear_series.change_origin_summable_aux_j
- \- *lemma* formal_multilinear_series.change_origin_summable_aux_j_injective
- \- *lemma* formal_multilinear_series.continuous_on
- \- *lemma* formal_multilinear_series.has_fpower_series_on_ball
- \+ *lemma* formal_multilinear_series.has_fpower_series_on_ball_change_origin
- \+ *lemma* formal_multilinear_series.le_change_origin_series_radius
- \+/\- *lemma* formal_multilinear_series.le_radius_of_bound
- \+/\- *lemma* formal_multilinear_series.le_radius_of_bound_nnreal
- \+ *lemma* formal_multilinear_series.le_radius_of_eventually_le
- \+ *lemma* formal_multilinear_series.le_radius_of_summable
- \+ *lemma* formal_multilinear_series.le_radius_of_summable_nnnorm
- \+ *lemma* formal_multilinear_series.nnnorm_change_origin_le
- \+ *lemma* formal_multilinear_series.nnnorm_change_origin_series_apply_le_tsum
- \+ *lemma* formal_multilinear_series.nnnorm_change_origin_series_le_tsum
- \+ *lemma* formal_multilinear_series.nnnorm_change_origin_series_term
- \+ *lemma* formal_multilinear_series.nnnorm_change_origin_series_term_apply_le
- \+ *lemma* formal_multilinear_series.norm_change_origin_series_term
- \+ *lemma* formal_multilinear_series.summable_nnnorm_mul_pow
- \+ *lemma* formal_multilinear_series.summable_norm_mul_pow

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.le_of_forall_pos_nnreal_lt

Modified src/data/subtype.lean
- \+ *lemma* subtype.heq_iff_coe_heq

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
- \+ *lemma* int.pow_right_injective



## [2021-07-16 22:47:45](https://github.com/leanprover-community/mathlib/commit/10975e6)
docs(measure_theory/integral_eq_improper): fix lemma names in docs ([#8333](https://github.com/leanprover-community/mathlib/pull/8333))
#### Estimated changes
Modified src/measure_theory/integral_eq_improper.lean




## [2021-07-16 17:58:03](https://github.com/leanprover-community/mathlib/commit/8e3d9ce)
feat(measure_theory/continuous_map_dense): continuous functions are dense in Lp ([#8306](https://github.com/leanprover-community/mathlib/pull/8306))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* monoid_hom.subgroup_of_range_eq_of_le

Added src/measure_theory/continuous_map_dense.lean
- \+ *lemma* bounded_continuous_function.to_Lp_dense_range
- \+ *lemma* continuous_map.to_Lp_dense_range
- \+ *lemma* measure_theory.Lp.bounded_continuous_function_dense

Modified src/measure_theory/lp_space.lean
- \+ *lemma* bounded_continuous_function.range_to_Lp
- \+ *lemma* bounded_continuous_function.range_to_Lp_hom
- \+ *lemma* continuous_map.range_to_Lp
- \+ *def* measure_theory.Lp.bounded_continuous_function
- \+ *lemma* measure_theory.Lp.mem_bounded_continuous_function_iff

Modified src/measure_theory/vitali_caratheodory.lean


Modified src/topology/algebra/group.lean
- \+/\- *lemma* subgroup.is_closed_topological_closure
- \+/\- *lemma* subgroup.subgroup_topological_closure
- \+/\- *lemma* subgroup.topological_closure_minimal



## [2021-07-16 17:58:00](https://github.com/leanprover-community/mathlib/commit/a895300)
chore(ring_theory/fractional_ideal): prefer `(⊤ : ideal R)` over `1` ([#8298](https://github.com/leanprover-community/mathlib/pull/8298))
`fractional_ideal.lean` sometimes used `1` to denote the ideal of `R` containing each element of `R`. This PR should replace all remaining usages with `⊤ : ideal R`, following the convention in the rest of mathlib.
Also a little `simp` lemma `coe_ideal_top` which was the motivation, since the proof should have been, and is now `by refl`.
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* ring.fractional_ideal.coe_ideal_top
- \- *lemma* ring.fractional_ideal.coe_one_eq_coe_submodule_one
- \+ *lemma* ring.fractional_ideal.coe_one_eq_coe_submodule_top



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
Added src/topology/metric_space/holder.lean
- \+ *lemma* holder_with.comp
- \+ *lemma* holder_with.dist_le
- \+ *lemma* holder_with.dist_le_of_le
- \+ *lemma* holder_with.ediam_image_le
- \+ *lemma* holder_with.edist_le
- \+ *lemma* holder_with.edist_le_of_le
- \+ *lemma* holder_with.nndist_le
- \+ *lemma* holder_with.nndist_le_of_le
- \+ *def* holder_with
- \+ *lemma* holder_with_id
- \+ *lemma* holder_with_one



## [2021-07-16 15:14:22](https://github.com/leanprover-community/mathlib/commit/35a8d93)
chore(topology/algebra/infinite_sum): relax the requirements on `has_sum.smul` ([#8312](https://github.com/leanprover-community/mathlib/pull/8312))
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean




## [2021-07-16 13:09:51](https://github.com/leanprover-community/mathlib/commit/162221f)
chore(set_theory/*): use `is_empty α` instead of `¬nonempty α` ([#8276](https://github.com/leanprover-community/mathlib/pull/8276))
Split from [#7826](https://github.com/leanprover-community/mathlib/pull/7826)
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.sup_eq_zero

Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.type_eq_zero_iff_empty
- \+ *theorem* ordinal.type_eq_zero_iff_is_empty
- \+ *theorem* ordinal.type_eq_zero_of_empty



## [2021-07-16 11:35:29](https://github.com/leanprover-community/mathlib/commit/9a801ef)
docs(order/rel_iso): add module docstring ([#8249](https://github.com/leanprover-community/mathlib/pull/8249))
#### Estimated changes
Modified src/order/rel_iso.lean
- \+/\- *theorem* rel_iso.apply_symm_apply



## [2021-07-16 09:16:30](https://github.com/leanprover-community/mathlib/commit/e35d976)
chore(algebra/quaternion): add `smul_mk` ([#8126](https://github.com/leanprover-community/mathlib/pull/8126))
This follows the pattern set by `mk_mul_mk` and `mk_add_mk`.
#### Estimated changes
Modified src/algebra/quaternion.lean
- \+ *lemma* quaternion_algebra.smul_mk



## [2021-07-16 09:16:29](https://github.com/leanprover-community/mathlib/commit/610fab7)
feat(set_theory/cofinality): more infinite pigeonhole principles ([#7879](https://github.com/leanprover-community/mathlib/pull/7879))
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* set.union_finset_finite_of_range_finite

Modified src/set_theory/cofinality.lean
- \+ *theorem* cardinal.exists_infinite_fiber
- \+ *theorem* cardinal.infinite_pigeonhole_card_lt
- \+ *lemma* cardinal.le_range_of_union_finset_eq_top



## [2021-07-16 07:34:18](https://github.com/leanprover-community/mathlib/commit/e6ff367)
feat(logic/embedding): simp lemma for injectivity for embeddings ([#7881](https://github.com/leanprover-community/mathlib/pull/7881))
#### Estimated changes
Modified src/logic/embedding.lean
- \+ *lemma* function.embedding.apply_eq_iff_eq



## [2021-07-16 05:22:17](https://github.com/leanprover-community/mathlib/commit/728eefe)
docs(data/fintype/basic): add module docstring ([#8081](https://github.com/leanprover-community/mathlib/pull/8081))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+/\- *lemma* finset.piecewise_univ
- \+/\- *theorem* fintype.card_of_subtype
- \+/\- *lemma* fintype.exists_max
- \+/\- *lemma* fintype.mem_pi_finset
- \+/\- *def* fintype.of_list
- \+/\- *def* fintype.of_multiset
- \+/\- *def* fintype.pi_finset
- \+/\- *lemma* fintype.pi_finset_subset
- \+/\- *theorem* fintype.subtype_card
- \+/\- *lemma* mem_perms_of_list_of_mem



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
- \+/\- *lemma* matrix.add_dot_product
- \+/\- *lemma* matrix.diagonal_dot_product
- \+/\- *lemma* matrix.dot_product_add
- \+/\- *lemma* matrix.dot_product_diagonal'
- \+/\- *lemma* matrix.dot_product_diagonal
- \+/\- *lemma* matrix.dot_product_neg
- \+/\- *lemma* matrix.dot_product_smul
- \+/\- *lemma* matrix.dot_product_star
- \+ *lemma* matrix.dot_product_sub
- \+/\- *lemma* matrix.dot_product_zero'
- \+/\- *lemma* matrix.dot_product_zero
- \- *lemma* matrix.mul_vec_one
- \+/\- *lemma* matrix.neg_dot_product
- \+ *lemma* matrix.one_mul_vec
- \+/\- *lemma* matrix.smul_dot_product
- \+/\- *lemma* matrix.star_dot_product
- \+/\- *lemma* matrix.star_dot_product_star
- \+ *lemma* matrix.sub_dot_product
- \+/\- *lemma* matrix.vec_mul_zero
- \+/\- *lemma* matrix.zero_dot_product'
- \+/\- *lemma* matrix.zero_dot_product
- \+ *lemma* matrix.zero_mul_vec
- \+ *lemma* matrix.zero_vec_mul

Modified src/linear_algebra/matrix/nonsingular_inverse.lean




## [2021-07-15 21:23:27](https://github.com/leanprover-community/mathlib/commit/b577bb2)
feat(measure_theory/conditional_expectation): define condexp_L2, conditional expectation of L2 functions ([#8324](https://github.com/leanprover-community/mathlib/pull/8324))
#### Estimated changes
Modified src/measure_theory/conditional_expectation.lean
- \+ *def* measure_theory.condexp_L2
- \+ *lemma* measure_theory.condexp_L2_indicator_of_measurable
- \+ *lemma* measure_theory.inner_condexp_L2_eq_inner_fun
- \+ *lemma* measure_theory.inner_condexp_L2_left_eq_right
- \+ *lemma* measure_theory.integrable_condexp_L2_of_finite_measure
- \+ *lemma* measure_theory.integrable_on_condexp_L2_of_measure_ne_top
- \+ *lemma* measure_theory.mem_Lp_meas_indicator_const_Lp
- \+ *lemma* measure_theory.norm_condexp_L2_coe_le
- \+ *lemma* measure_theory.norm_condexp_L2_le
- \+ *lemma* measure_theory.norm_condexp_L2_le_one
- \+ *lemma* measure_theory.snorm_condexp_L2_le



## [2021-07-15 17:38:21](https://github.com/leanprover-community/mathlib/commit/79fbd46)
feat(ring_theory/ideal): generalize two results from finset to multiset ([#8320](https://github.com/leanprover-community/mathlib/pull/8320))
Nothing exciting going on here, just copied two proofs, replaced all `finset.insert` with `multiset.cons` and `finset.prod` with `(multiset.map _).prod`, and used those to show the original results.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *theorem* ideal.is_prime.multiset_prod_le
- \+ *theorem* ideal.is_prime.multiset_prod_map_le
- \+ *theorem* ideal.multiset_prod_le_inf



## [2021-07-15 16:32:09](https://github.com/leanprover-community/mathlib/commit/a783a47)
feat(data/matrix/{basic, block}): missing lemmas on conj_transpose ([#8303](https://github.com/leanprover-community/mathlib/pull/8303))
This also moves some imports around to make the star operator on vectors available in matrix/basic.lean
This is a follow up to [#8291](https://github.com/leanprover-community/mathlib/pull/8291)
#### Estimated changes
Modified src/algebra/star/algebra.lean


Modified src/algebra/star/pi.lean


Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.conj_transpose_col
- \+ *lemma* matrix.conj_transpose_row
- \+ *lemma* matrix.dot_product_star
- \+ *lemma* matrix.map_update_column
- \+ *lemma* matrix.map_update_row
- \+ *lemma* matrix.star_dot_product
- \+ *lemma* matrix.star_dot_product_star
- \+/\- *lemma* matrix.transpose_col
- \+/\- *lemma* matrix.transpose_row
- \+ *lemma* matrix.update_column_conj_transpose
- \+ *lemma* matrix.update_row_conj_transpose

Modified src/data/matrix/block.lean
- \+ *lemma* matrix.block_diagonal'_conj_transpose
- \+ *lemma* matrix.block_diagonal'_map
- \+ *lemma* matrix.block_diagonal_conj_transpose
- \+ *lemma* matrix.block_diagonal_map
- \+ *lemma* matrix.from_blocks_conj_transpose
- \+ *lemma* matrix.from_blocks_map



## [2021-07-15 16:32:08](https://github.com/leanprover-community/mathlib/commit/66055dd)
feat(algebra/lie/cartan_matrix): define the exceptional Lie algebras ([#8299](https://github.com/leanprover-community/mathlib/pull/8299))
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/lie/cartan_matrix.lean
- \+ *def* cartan_matrix.E₆
- \+ *def* cartan_matrix.E₇
- \+ *def* cartan_matrix.E₈
- \+ *def* cartan_matrix.F₄
- \+ *def* cartan_matrix.G₂



## [2021-07-15 15:05:29](https://github.com/leanprover-community/mathlib/commit/bc1f145)
feat(data/multiset): `<` on multisets is well-founded ([#8319](https://github.com/leanprover-community/mathlib/pull/8319))
This is vaguely related to [#5783](https://github.com/leanprover-community/mathlib/pull/5783), in that it tries to solve a similar goal of finding a minimal multiset with some property.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.well_founded_lt



## [2021-07-15 13:15:59](https://github.com/leanprover-community/mathlib/commit/0597b1d)
feat(analysis/normed_space/normed_group_hom): add equalizer ([#8228](https://github.com/leanprover-community/mathlib/pull/8228))
From LTE.
We add equalizer of `normed_group_homs`.
#### Estimated changes
Modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* normed_group_hom.equalizer.comm_sq₂
- \+ *lemma* normed_group_hom.equalizer.comp_ι_eq
- \+ *def* normed_group_hom.equalizer.lift
- \+ *def* normed_group_hom.equalizer.lift_equiv
- \+ *lemma* normed_group_hom.equalizer.lift_norm_noninc
- \+ *def* normed_group_hom.equalizer.map
- \+ *lemma* normed_group_hom.equalizer.map_comp_map
- \+ *lemma* normed_group_hom.equalizer.map_id
- \+ *lemma* normed_group_hom.equalizer.map_norm_noninc
- \+ *lemma* normed_group_hom.equalizer.norm_lift_le
- \+ *lemma* normed_group_hom.equalizer.norm_map_le
- \+ *def* normed_group_hom.equalizer.ι
- \+ *lemma* normed_group_hom.equalizer.ι_comp_lift
- \+ *lemma* normed_group_hom.equalizer.ι_comp_map
- \+ *lemma* normed_group_hom.equalizer.ι_norm_noninc
- \+ *def* normed_group_hom.equalizer



## [2021-07-15 09:20:51](https://github.com/leanprover-community/mathlib/commit/7e5be02)
chore(algebra/*): make non-instance typeclasses reducible. ([#8322](https://github.com/leanprover-community/mathlib/pull/8322))
A follow up to [#7835](https://github.com/leanprover-community/mathlib/pull/7835)
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/module/basic.lean
- \+/\- *def* module.comp_hom

Modified src/group_theory/group_action/defs.lean
- \+/\- *def* distrib_mul_action.comp_hom
- \+/\- *def* mul_action.comp_hom



## [2021-07-15 05:43:19](https://github.com/leanprover-community/mathlib/commit/e42af8d)
refactor(topology/category/Profinite): define Profinite as a subcategory of CompHaus ([#8314](https://github.com/leanprover-community/mathlib/pull/8314))
This adjusts the definition of Profinite to explicitly be a subcategory of CompHaus rather than a subcategory of Top which embeds into CompHaus. Essentially this means it's easier to construct an element of Profinite from an element of CompHaus.
#### Estimated changes
Modified src/topology/category/Profinite/cofiltered_limit.lean


Modified src/topology/category/Profinite/default.lean
- \+ *lemma* Profinite.coe_to_CompHaus
- \- *lemma* Profinite.coe_to_Top
- \- *def* Profinite.to_CompHaus
- \+/\- *def* Profinite.to_Profinite_adj_to_CompHaus
- \+ *def* Profinite.to_Top
- \+ *def* Profinite_to_CompHaus
- \- *def* Profinite_to_Top



## [2021-07-14 22:10:52](https://github.com/leanprover-community/mathlib/commit/e343609)
feat(measure_theory/simple_func_dense): induction lemmas for Lp.simple_func and Lp ([#8300](https://github.com/leanprover-community/mathlib/pull/8300))
The new lemmas, `Lp.simple_func.induction`, `Lp.induction`, allow one to prove a predicate for all elements of `Lp.simple_func` / `Lp` (here p < ∞), by proving it for characteristic functions and then checking it behaves appropriately under addition, and, in the second case, taking limits.  They are modelled on existing lemmas such as `simple_func.induction`, `mem_ℒp.induction`, `integrable.induction`.
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* set.mul_indicator_empty'

Modified src/algebra/support.lean
- \+ *lemma* function.mul_support_const

Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.simple_func.support_indicator

Modified src/measure_theory/lp_space.lean
- \+ *lemma* measure_theory.indicator_const_empty

Modified src/measure_theory/simple_func_dense.lean
- \+ *lemma* measure_theory.Lp.induction
- \+ *lemma* measure_theory.Lp.simple_func.coe_indicator_const
- \+ *def* measure_theory.Lp.simple_func.indicator_const
- \+ *lemma* measure_theory.Lp.simple_func.to_simple_func_indicator_const
- \+ *lemma* measure_theory.simple_func.measure_lt_top_of_mem_ℒp_indicator



## [2021-07-14 18:22:17](https://github.com/leanprover-community/mathlib/commit/19a156a)
refactor(algebra/ordered_ring): use `mul_le_mul'` for `canonically_ordered_comm_semiring` ([#8284](https://github.com/leanprover-community/mathlib/pull/8284))
* use `canonically_ordered_comm_semiring`, not `canonically_ordered_semiring` as a namespace;
* add an instance `canonically_ordered_comm_semiring.to_covariant_mul_le`;
* drop `canonically_ordered_semiring.mul_le_mul` etc in favor of `mul_le_mul'` etc.
#### Estimated changes
Modified src/algebra/big_operators/order.lean


Modified src/algebra/group_power/order.lean
- \+ *theorem* canonically_ordered_comm_semiring.one_le_pow_of_one_le
- \+ *theorem* canonically_ordered_comm_semiring.pow_le_one
- \+ *lemma* canonically_ordered_comm_semiring.pow_le_pow_of_le_left
- \+ *theorem* canonically_ordered_comm_semiring.pow_pos
- \- *theorem* canonically_ordered_semiring.one_le_pow_of_one_le
- \- *theorem* canonically_ordered_semiring.pow_le_one
- \- *lemma* canonically_ordered_semiring.pow_le_pow_of_le_left
- \- *theorem* canonically_ordered_semiring.pow_pos

Modified src/algebra/ordered_ring.lean
- \+ *lemma* canonically_ordered_comm_semiring.mul_pos
- \+ *lemma* canonically_ordered_comm_semiring.zero_lt_one
- \- *lemma* canonically_ordered_semiring.mul_le_mul
- \- *lemma* canonically_ordered_semiring.mul_le_mul_left'
- \- *lemma* canonically_ordered_semiring.mul_le_mul_right'
- \- *lemma* canonically_ordered_semiring.mul_pos
- \- *lemma* canonically_ordered_semiring.zero_lt_one

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
- \+ *def* empty_graph
- \+ *lemma* simple_graph.adj_comm
- \+ *lemma* simple_graph.adj_symm
- \- *lemma* simple_graph.edge_symm'
- \- *lemma* simple_graph.edge_symm
- \+ *lemma* simple_graph.embedding.apply_mem_neighbor_set_iff
- \+ *lemma* simple_graph.embedding.coe_comp
- \+ *lemma* simple_graph.embedding.map_adj_iff
- \+ *def* simple_graph.embedding.map_edge_set
- \+ *lemma* simple_graph.embedding.map_mem_edge_set_iff
- \+ *def* simple_graph.embedding.map_neighbor_set
- \+ *lemma* simple_graph.hom.apply_mem_neighbor_set
- \+ *lemma* simple_graph.hom.coe_comp
- \+ *lemma* simple_graph.hom.map_adj
- \+ *lemma* simple_graph.hom.map_edge_set.injective
- \+ *def* simple_graph.hom.map_edge_set
- \+ *lemma* simple_graph.hom.map_mem_edge_set
- \+ *def* simple_graph.hom.map_neighbor_set
- \+ *lemma* simple_graph.iso.apply_mem_neighbor_set_iff
- \+ *lemma* simple_graph.iso.card_eq_of_iso
- \+ *lemma* simple_graph.iso.coe_comp
- \+ *lemma* simple_graph.iso.map_adj_iff
- \+ *def* simple_graph.iso.map_edge_set
- \+ *lemma* simple_graph.iso.map_mem_edge_set_iff
- \+ *def* simple_graph.iso.map_neighbor_set

Added src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* simple_graph.subgraph.adj_comm
- \+ *lemma* simple_graph.subgraph.adj_symm
- \+ *def* simple_graph.subgraph.bot
- \+ *def* simple_graph.subgraph.bot_equiv
- \+ *def* simple_graph.subgraph.coe
- \+ *lemma* simple_graph.subgraph.coe_adj_sub
- \+ *lemma* simple_graph.subgraph.coe_degree
- \+ *def* simple_graph.subgraph.coe_neighbor_set_equiv
- \+ *def* simple_graph.subgraph.copy
- \+ *lemma* simple_graph.subgraph.copy_eq
- \+ *def* simple_graph.subgraph.degree
- \+ *lemma* simple_graph.subgraph.degree_le'
- \+ *lemma* simple_graph.subgraph.degree_le
- \+ *def* simple_graph.subgraph.edge_set
- \+ *lemma* simple_graph.subgraph.edge_set_subset
- \+ *def* simple_graph.subgraph.finite_at_of_subgraph
- \+ *def* simple_graph.subgraph.incidence_set
- \+ *lemma* simple_graph.subgraph.incidence_set_subset
- \+ *lemma* simple_graph.subgraph.incidence_set_subset_incidence_set
- \+ *def* simple_graph.subgraph.inter
- \+ *def* simple_graph.subgraph.is_induced
- \+ *def* simple_graph.subgraph.is_spanning
- \+ *def* simple_graph.subgraph.is_subgraph
- \+ *lemma* simple_graph.subgraph.map.injective
- \+ *def* simple_graph.subgraph.map
- \+ *lemma* simple_graph.subgraph.map_top.injective
- \+ *def* simple_graph.subgraph.map_top
- \+ *lemma* simple_graph.subgraph.map_top_to_fun
- \+ *lemma* simple_graph.subgraph.mem_edge_set
- \+ *lemma* simple_graph.subgraph.mem_neighbor_set
- \+ *lemma* simple_graph.subgraph.mem_verts_if_mem_edge
- \+ *def* simple_graph.subgraph.neighbor_set
- \+ *lemma* simple_graph.subgraph.neighbor_set_subset
- \+ *lemma* simple_graph.subgraph.neighbor_set_subset_of_subgraph
- \+ *def* simple_graph.subgraph.top
- \+ *def* simple_graph.subgraph.top_equiv
- \+ *def* simple_graph.subgraph.union
- \+ *def* simple_graph.subgraph.vert

Modified src/data/sym2.lean
- \+ *lemma* sym2.map.injective
- \+ *lemma* sym2.map_map
- \+/\- *lemma* sym2.map_pair_eq



## [2021-07-14 15:21:29](https://github.com/leanprover-community/mathlib/commit/bcc35c7)
feat(group_theory/submonoid/operations): `add_equiv.of_left_inverse` to match `linear_equiv.of_left_inverse` ([#8279](https://github.com/leanprover-community/mathlib/pull/8279))
#### Estimated changes
Modified src/group_theory/submonoid/operations.lean
- \+ *def* mul_equiv.of_left_inverse'



## [2021-07-14 13:57:59](https://github.com/leanprover-community/mathlib/commit/375dd53)
refactor(geometry/manifold): split `bump_function` into 3 files ([#8313](https://github.com/leanprover-community/mathlib/pull/8313))
This is the a part of [#8309](https://github.com/leanprover-community/mathlib/pull/8309). Both code and comments were moved with
almost no modifications: added/removed `variables`/`section`s,
slightly adjusted comments to glue them together.
#### Estimated changes
Modified src/geometry/manifold/bump_function.lean
- \- *lemma* exists_embedding_finrank_of_compact
- \- *lemma* smooth_bump_covering.apply_ind
- \- *def* smooth_bump_covering.choice
- \- *def* smooth_bump_covering.choice_set
- \- *lemma* smooth_bump_covering.coe_mk
- \- *lemma* smooth_bump_covering.comp_embedding_pi_tangent_mfderiv
- \- *def* smooth_bump_covering.embedding_pi_tangent
- \- *lemma* smooth_bump_covering.embedding_pi_tangent_inj_on
- \- *lemma* smooth_bump_covering.embedding_pi_tangent_injective
- \- *lemma* smooth_bump_covering.embedding_pi_tangent_injective_mfderiv
- \- *lemma* smooth_bump_covering.embedding_pi_tangent_ker_mfderiv
- \- *lemma* smooth_bump_covering.eventually_eq_one
- \- *lemma* smooth_bump_covering.exists_immersion_finrank
- \- *lemma* smooth_bump_covering.exists_is_subordinate
- \- *def* smooth_bump_covering.ind
- \- *def* smooth_bump_covering.is_subordinate
- \- *lemma* smooth_bump_covering.mem_chart_at_ind_source
- \- *lemma* smooth_bump_covering.mem_chart_at_source_of_eq_one
- \- *lemma* smooth_bump_covering.mem_ext_chart_at_ind_source
- \- *lemma* smooth_bump_covering.mem_ext_chart_at_source_of_eq_one
- \- *lemma* smooth_bump_covering.mem_support_ind

Added src/geometry/manifold/partition_of_unity.lean
- \+ *lemma* smooth_bump_covering.apply_ind
- \+ *def* smooth_bump_covering.choice
- \+ *def* smooth_bump_covering.choice_set
- \+ *lemma* smooth_bump_covering.coe_mk
- \+ *lemma* smooth_bump_covering.eventually_eq_one
- \+ *lemma* smooth_bump_covering.exists_is_subordinate
- \+ *def* smooth_bump_covering.ind
- \+ *def* smooth_bump_covering.is_subordinate
- \+ *lemma* smooth_bump_covering.mem_chart_at_ind_source
- \+ *lemma* smooth_bump_covering.mem_chart_at_source_of_eq_one
- \+ *lemma* smooth_bump_covering.mem_ext_chart_at_ind_source
- \+ *lemma* smooth_bump_covering.mem_ext_chart_at_source_of_eq_one
- \+ *lemma* smooth_bump_covering.mem_support_ind

Added src/geometry/manifold/whitney_embedding.lean
- \+ *lemma* exists_embedding_finrank_of_compact
- \+ *lemma* smooth_bump_covering.comp_embedding_pi_tangent_mfderiv
- \+ *def* smooth_bump_covering.embedding_pi_tangent
- \+ *lemma* smooth_bump_covering.embedding_pi_tangent_inj_on
- \+ *lemma* smooth_bump_covering.embedding_pi_tangent_injective
- \+ *lemma* smooth_bump_covering.embedding_pi_tangent_injective_mfderiv
- \+ *lemma* smooth_bump_covering.embedding_pi_tangent_ker_mfderiv
- \+ *lemma* smooth_bump_covering.exists_immersion_finrank



## [2021-07-14 13:57:58](https://github.com/leanprover-community/mathlib/commit/5bac21a)
chore(algebra/module/pi): add `pi.smul_def` ([#8311](https://github.com/leanprover-community/mathlib/pull/8311))
Sometimes it is useful to rewrite unapplied `s • x` (I need it in a branch that is not yet ready for review).
We already have `pi.zero_def`, `pi.add_def`, etc.
#### Estimated changes
Modified src/algebra/module/pi.lean
- \+ *lemma* pi.smul_def



## [2021-07-14 13:57:57](https://github.com/leanprover-community/mathlib/commit/7fccf40)
feat(algebraic_topology/topological_simplex): This defines the natural functor from Top to sSet. ([#8305](https://github.com/leanprover-community/mathlib/pull/8305))
This PR also provides the geometric realization functor and the associated adjunction.
#### Estimated changes
Modified src/algebraic_topology/simplicial_set.lean


Added src/algebraic_topology/topological_simplex.lean
- \+ *lemma* simplex_category.coe_to_Top_map
- \+ *lemma* simplex_category.continuous_to_Top_map
- \+ *def* simplex_category.to_Top
- \+ *def* simplex_category.to_Top_map
- \+ *lemma* simplex_category.to_Top_obj.ext
- \+ *def* simplex_category.to_Top_obj



## [2021-07-14 13:57:56](https://github.com/leanprover-community/mathlib/commit/7d53431)
feat(measure_theory/integration): if a function has bounded integral on all sets of finite measure, then it is integrable ([#8297](https://github.com/leanprover-community/mathlib/pull/8297))
If the measure is sigma-finite and a function has integral bounded by some C for all measurable sets with finite measure, then its integral over the whole space is bounded by that same C. This can be used to show that a function is integrable.
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.lintegral_le_of_forall_fin_meas_le'
- \+ *lemma* measure_theory.lintegral_le_of_forall_fin_meas_le
- \+ *lemma* measure_theory.lintegral_le_of_forall_fin_meas_le_of_measurable
- \+ *lemma* measure_theory.univ_le_of_forall_fin_meas_le

Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.integrable_of_forall_fin_meas_le'
- \+ *lemma* measure_theory.integrable_of_forall_fin_meas_le

Modified src/measure_theory/measurable_space_def.lean




## [2021-07-14 12:56:52](https://github.com/leanprover-community/mathlib/commit/3b7e7bd)
feat(normed_space): controlled_sum_of_mem_closure ([#8310](https://github.com/leanprover-community/mathlib/pull/8310))
From LTE
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* controlled_sum_of_mem_closure
- \+ *lemma* controlled_sum_of_mem_closure_range

Modified src/order/filter/at_top_bot.lean
- \- *lemma* filter.strict_mono_tendsto_at_top
- \+ *lemma* strict_mono.tendsto_at_top



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
- \+ *lemma* ennreal.inv_rpow
- \- *lemma* ennreal.inv_rpow_of_pos
- \+ *lemma* ennreal.monotone_rpow_of_nonneg
- \+ *lemma* ennreal.mul_rpow_eq_ite
- \+ *lemma* ennreal.strict_mono_rpow_of_pos
- \+ *lemma* ennreal.zero_rpow_mul_self

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.eq_inv_of_mul_eq_one

Modified src/measure_theory/mean_inequalities.lean




## [2021-07-14 10:14:23](https://github.com/leanprover-community/mathlib/commit/743209c)
chore(algebra/big_operators/basic): spaces around binders ([#8307](https://github.com/leanprover-community/mathlib/pull/8307))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.exists_ne_one_of_prod_ne_one
- \+/\- *lemma* finset.prod_congr
- \+/\- *lemma* finset.prod_eq_one
- \+/\- *lemma* finset.prod_eq_zero_iff
- \+/\- *lemma* finset.sum_const_nat



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
- \+ *lemma* measurable_of_antimono
- \+ *lemma* measurable_of_monotone



## [2021-07-14 08:37:24](https://github.com/leanprover-community/mathlib/commit/8e5af43)
chore(algebra/big_operators/basic): rename sum_(nat/int)_cast and (nat/int).coe_prod ([#8264](https://github.com/leanprover-community/mathlib/pull/8264))
The current names aren't great because
1. For `sum_nat_cast` and `sum_int_cast`, the LHS isn't a sum of casts but a cast of sums, and it doesn't follow any other naming convention (`nat.cast_...` or `....coe_sum`).
2. For `.coe_prod`, the coercion from `ℕ` or `ℤ` should be called `cast`.
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified src/algebra/big_operators/basic.lean
- \- *lemma* finset.sum_int_cast
- \- *lemma* finset.sum_nat_cast
- \+ *lemma* int.cast_prod
- \+ *lemma* int.cast_sum
- \- *lemma* int.coe_prod
- \+ *lemma* nat.cast_prod
- \+ *lemma* nat.cast_sum
- \- *lemma* nat.coe_prod
- \+/\- *lemma* units.coe_prod

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
- \+ *lemma* int.coe_greatest_of_bdd_eq
- \+ *lemma* int.coe_least_of_bdd_eq

Added src/data/int/order.lean
- \+ *lemma* int.cInf_empty
- \+ *lemma* int.cInf_eq_least_of_bdd
- \+ *lemma* int.cInf_mem
- \+ *lemma* int.cInf_of_not_bdd_below
- \+ *lemma* int.cSup_empty
- \+ *lemma* int.cSup_eq_greatest_of_bdd
- \+ *lemma* int.cSup_mem
- \+ *lemma* int.cSup_of_not_bdd_above



## [2021-07-13 20:14:44](https://github.com/leanprover-community/mathlib/commit/29b63a7)
feat(data/matrix/basic): add conj_transpose ([#8291](https://github.com/leanprover-community/mathlib/pull/8291))
As requested by Eric Wieser, I pulled one single change of [#8289](https://github.com/leanprover-community/mathlib/pull/8289) out into a new PR. As such, this PR will not block anything in [#8289](https://github.com/leanprover-community/mathlib/pull/8289).
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *def* matrix.conj_transpose
- \+ *lemma* matrix.conj_transpose_add
- \+ *lemma* matrix.conj_transpose_apply
- \+ *lemma* matrix.conj_transpose_conj_transpose
- \+ *lemma* matrix.conj_transpose_minor
- \+ *lemma* matrix.conj_transpose_mul
- \+ *lemma* matrix.conj_transpose_neg
- \+ *lemma* matrix.conj_transpose_one
- \+ *lemma* matrix.conj_transpose_reindex
- \+ *lemma* matrix.conj_transpose_smul
- \+ *lemma* matrix.conj_transpose_sub
- \+ *lemma* matrix.conj_transpose_zero
- \+/\- *lemma* matrix.star_apply
- \+ *lemma* matrix.star_eq_conj_transpose
- \+/\- *lemma* matrix.star_mul



## [2021-07-13 20:14:43](https://github.com/leanprover-community/mathlib/commit/63266ff)
feat(group_theory/free_product): the free product of an indexed family of monoids ([#8256](https://github.com/leanprover-community/mathlib/pull/8256))
Defines the free product (categorical coproduct) of an indexed family of monoids. Proves its universal property. The free product of groups is a group.
Split off from [#7395](https://github.com/leanprover-community/mathlib/pull/7395)
#### Estimated changes
Modified docs/references.bib


Added src/group_theory/free_product.lean
- \+ *lemma* free_product.ext_hom
- \+ *lemma* free_product.induction_on
- \+ *lemma* free_product.inv_def
- \+ *def* free_product.lift
- \+ *lemma* free_product.lift_of
- \+ *def* free_product.of
- \+ *lemma* free_product.of_apply
- \+ *lemma* free_product.of_injective
- \+ *lemma* free_product.of_left_inverse
- \+ *def* free_product



## [2021-07-13 18:51:54](https://github.com/leanprover-community/mathlib/commit/905b875)
chore(data/matrix/block): move block matrices into their own file ([#8290](https://github.com/leanprover-community/mathlib/pull/8290))
This is a straight cut-and-paste, with no reordering or renaming.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/import.20fails/near/245802618)
#### Estimated changes
Modified src/data/matrix/basic.lean
- \- *def* matrix.block_diagonal'
- \- *lemma* matrix.block_diagonal'_add
- \- *lemma* matrix.block_diagonal'_apply
- \- *lemma* matrix.block_diagonal'_apply_eq
- \- *lemma* matrix.block_diagonal'_apply_ne
- \- *lemma* matrix.block_diagonal'_diagonal
- \- *lemma* matrix.block_diagonal'_eq_block_diagonal
- \- *lemma* matrix.block_diagonal'_minor_eq_block_diagonal
- \- *lemma* matrix.block_diagonal'_mul
- \- *lemma* matrix.block_diagonal'_neg
- \- *lemma* matrix.block_diagonal'_one
- \- *lemma* matrix.block_diagonal'_smul
- \- *lemma* matrix.block_diagonal'_sub
- \- *lemma* matrix.block_diagonal'_transpose
- \- *lemma* matrix.block_diagonal'_zero
- \- *def* matrix.block_diagonal
- \- *lemma* matrix.block_diagonal_add
- \- *lemma* matrix.block_diagonal_apply
- \- *lemma* matrix.block_diagonal_apply_eq
- \- *lemma* matrix.block_diagonal_apply_ne
- \- *lemma* matrix.block_diagonal_diagonal
- \- *lemma* matrix.block_diagonal_mul
- \- *lemma* matrix.block_diagonal_neg
- \- *lemma* matrix.block_diagonal_one
- \- *lemma* matrix.block_diagonal_smul
- \- *lemma* matrix.block_diagonal_sub
- \- *lemma* matrix.block_diagonal_transpose
- \- *lemma* matrix.block_diagonal_zero
- \- *def* matrix.from_blocks
- \- *lemma* matrix.from_blocks_add
- \- *lemma* matrix.from_blocks_apply₁₁
- \- *lemma* matrix.from_blocks_apply₁₂
- \- *lemma* matrix.from_blocks_apply₂₁
- \- *lemma* matrix.from_blocks_apply₂₂
- \- *lemma* matrix.from_blocks_diagonal
- \- *lemma* matrix.from_blocks_multiply
- \- *lemma* matrix.from_blocks_one
- \- *lemma* matrix.from_blocks_smul
- \- *lemma* matrix.from_blocks_to_blocks
- \- *lemma* matrix.from_blocks_transpose
- \- *def* matrix.to_block
- \- *lemma* matrix.to_block_apply
- \- *lemma* matrix.to_blocks_from_blocks₁₁
- \- *lemma* matrix.to_blocks_from_blocks₁₂
- \- *lemma* matrix.to_blocks_from_blocks₂₁
- \- *lemma* matrix.to_blocks_from_blocks₂₂
- \- *def* matrix.to_blocks₁₁
- \- *def* matrix.to_blocks₁₂
- \- *def* matrix.to_blocks₂₁
- \- *def* matrix.to_blocks₂₂
- \- *def* matrix.to_square_block'
- \- *def* matrix.to_square_block
- \- *lemma* matrix.to_square_block_def'
- \- *lemma* matrix.to_square_block_def
- \- *def* matrix.to_square_block_prop
- \- *lemma* matrix.to_square_block_prop_def

Added src/data/matrix/block.lean
- \+ *def* matrix.block_diagonal'
- \+ *lemma* matrix.block_diagonal'_add
- \+ *lemma* matrix.block_diagonal'_apply
- \+ *lemma* matrix.block_diagonal'_apply_eq
- \+ *lemma* matrix.block_diagonal'_apply_ne
- \+ *lemma* matrix.block_diagonal'_diagonal
- \+ *lemma* matrix.block_diagonal'_eq_block_diagonal
- \+ *lemma* matrix.block_diagonal'_minor_eq_block_diagonal
- \+ *lemma* matrix.block_diagonal'_mul
- \+ *lemma* matrix.block_diagonal'_neg
- \+ *lemma* matrix.block_diagonal'_one
- \+ *lemma* matrix.block_diagonal'_smul
- \+ *lemma* matrix.block_diagonal'_sub
- \+ *lemma* matrix.block_diagonal'_transpose
- \+ *lemma* matrix.block_diagonal'_zero
- \+ *def* matrix.block_diagonal
- \+ *lemma* matrix.block_diagonal_add
- \+ *lemma* matrix.block_diagonal_apply
- \+ *lemma* matrix.block_diagonal_apply_eq
- \+ *lemma* matrix.block_diagonal_apply_ne
- \+ *lemma* matrix.block_diagonal_diagonal
- \+ *lemma* matrix.block_diagonal_mul
- \+ *lemma* matrix.block_diagonal_neg
- \+ *lemma* matrix.block_diagonal_one
- \+ *lemma* matrix.block_diagonal_smul
- \+ *lemma* matrix.block_diagonal_sub
- \+ *lemma* matrix.block_diagonal_transpose
- \+ *lemma* matrix.block_diagonal_zero
- \+ *def* matrix.from_blocks
- \+ *lemma* matrix.from_blocks_add
- \+ *lemma* matrix.from_blocks_apply₁₁
- \+ *lemma* matrix.from_blocks_apply₁₂
- \+ *lemma* matrix.from_blocks_apply₂₁
- \+ *lemma* matrix.from_blocks_apply₂₂
- \+ *lemma* matrix.from_blocks_diagonal
- \+ *lemma* matrix.from_blocks_multiply
- \+ *lemma* matrix.from_blocks_one
- \+ *lemma* matrix.from_blocks_smul
- \+ *lemma* matrix.from_blocks_to_blocks
- \+ *lemma* matrix.from_blocks_transpose
- \+ *def* matrix.to_block
- \+ *lemma* matrix.to_block_apply
- \+ *lemma* matrix.to_blocks_from_blocks₁₁
- \+ *lemma* matrix.to_blocks_from_blocks₁₂
- \+ *lemma* matrix.to_blocks_from_blocks₂₁
- \+ *lemma* matrix.to_blocks_from_blocks₂₂
- \+ *def* matrix.to_blocks₁₁
- \+ *def* matrix.to_blocks₁₂
- \+ *def* matrix.to_blocks₂₁
- \+ *def* matrix.to_blocks₂₂
- \+ *def* matrix.to_square_block'
- \+ *def* matrix.to_square_block
- \+ *lemma* matrix.to_square_block_def'
- \+ *lemma* matrix.to_square_block_def
- \+ *def* matrix.to_square_block_prop
- \+ *lemma* matrix.to_square_block_prop_def

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
- \+ *def* category_theory.monoidal_category.tensoring_left
- \+/\- *def* category_theory.monoidal_category.tensoring_right

Added src/category_theory/monoidal/preadditive.lean


Added src/category_theory/monoidal/tor.lean
- \+ *def* category_theory.Tor'
- \+ *def* category_theory.Tor'_succ_of_projective
- \+ *def* category_theory.Tor
- \+ *def* category_theory.Tor_succ_of_projective



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
- \+ *lemma* direct_sum.add_submonoid_is_internal.supr_eq_top

Modified src/data/dfinsupp.lean
- \+ *lemma* add_submonoid.mem_supr_iff_exists_dfinsupp'
- \+ *lemma* add_submonoid.mem_supr_iff_exists_dfinsupp
- \+ *lemma* add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom

Modified src/linear_algebra/dfinsupp.lean
- \+/\- *lemma* submodule.dfinsupp_sum_add_hom_mem
- \+/\- *lemma* submodule.dfinsupp_sum_mem
- \+ *lemma* submodule.mem_supr_iff_exists_dfinsupp'
- \+ *lemma* submodule.mem_supr_iff_exists_dfinsupp
- \+ *lemma* submodule.supr_eq_range_dfinsupp_lsum

Modified src/linear_algebra/direct_sum_module.lean
- \+ *lemma* direct_sum.submodule_is_internal.supr_eq_top



## [2021-07-13 16:48:04](https://github.com/leanprover-community/mathlib/commit/3a0ef3c)
feat(ring_theory): (strict) monotonicity of `coe_submodule` ([#8273](https://github.com/leanprover-community/mathlib/pull/8273))
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* is_fraction_ring.coe_submodule_le_coe_submodule
- \+ *lemma* is_fraction_ring.coe_submodule_strict_mono
- \+ *lemma* is_localization.coe_submodule_le_coe_submodule
- \+ *lemma* is_localization.coe_submodule_mono
- \+ *lemma* is_localization.coe_submodule_strict_mono



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
- \+ *lemma* nat.factors_subset_of_dvd
- \+ *lemma* nat.factors_subset_right
- \+/\- *theorem* nat.le_min_fac'
- \+/\- *theorem* nat.le_min_fac
- \+/\- *def* nat.min_fac
- \+/\- *def* nat.min_fac_aux
- \+/\- *theorem* nat.min_fac_aux_has_prop
- \+/\- *theorem* nat.min_fac_dvd
- \+/\- *theorem* nat.min_fac_eq
- \+/\- *lemma* nat.min_fac_eq_one_iff
- \+/\- *lemma* nat.min_fac_eq_two_iff
- \+/\- *theorem* nat.min_fac_has_prop
- \+/\- *theorem* nat.min_fac_le
- \+/\- *lemma* nat.min_fac_le_div
- \+/\- *theorem* nat.min_fac_le_of_dvd
- \+/\- *theorem* nat.min_fac_one
- \+/\- *theorem* nat.min_fac_pos
- \+/\- *theorem* nat.min_fac_prime
- \+/\- *lemma* nat.min_fac_sq_le_self
- \+/\- *theorem* nat.min_fac_zero
- \+/\- *theorem* nat.not_prime_iff_min_fac_lt
- \+/\- *theorem* nat.prime_def_min_fac



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
- \+/\- *def* probability_theory.indep_fun

Modified src/probability_theory/integration.lean
- \+/\- *lemma* probability_theory.lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun



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
- \+/\- *lemma* set.Icc_eq_empty
- \+/\- *lemma* set.Icc_eq_empty_iff
- \+ *lemma* set.Icc_eq_empty_of_lt
- \+/\- *lemma* set.Ico_eq_empty
- \+/\- *lemma* set.Ico_eq_empty_iff
- \+ *lemma* set.Ico_eq_empty_of_le
- \+/\- *lemma* set.Ico_self
- \+/\- *lemma* set.Ioc_eq_empty
- \+ *lemma* set.Ioc_eq_empty_iff
- \+ *lemma* set.Ioc_eq_empty_of_le
- \+/\- *lemma* set.Ioc_self
- \+/\- *lemma* set.Ioo_eq_empty
- \+/\- *lemma* set.Ioo_eq_empty_iff
- \+ *lemma* set.Ioo_eq_empty_of_le
- \+/\- *lemma* set.Ioo_self

Modified src/data/set/intervals/disjoint.lean


Modified src/data/set/intervals/surj_on.lean


Modified src/measure_theory/interval_integral.lean




## [2021-07-13 11:23:36](https://github.com/leanprover-community/mathlib/commit/bb53a92)
chore(data/mv_polynomial/basic): use `is_empty σ` instead of `¬nonempty σ` ([#8277](https://github.com/leanprover-community/mathlib/pull/8277))
Split from [#7826](https://github.com/leanprover-community/mathlib/pull/7826)
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.C_surjective
- \- *lemma* mv_polynomial.C_surjective_fin_0

Modified src/ring_theory/jacobson.lean




## [2021-07-13 10:08:14](https://github.com/leanprover-community/mathlib/commit/dd9a0ea)
feat(geometry/manifold): add `charted_space` and `model_with_corners` for pi types ([#6578](https://github.com/leanprover-community/mathlib/pull/6578))
Also use `set.image2` in the `charted_space` instance for `model_prod`.
#### Estimated changes
Modified src/data/equiv/local_equiv.lean


Modified src/geometry/manifold/charted_space.lean
- \+ *def* model_pi
- \+ *lemma* pi_charted_space_chart_at

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
- \+ *lemma* nhds_bot_basis
- \+ *lemma* nhds_top_basis

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.nhds_top_basis
- \+ *lemma* ennreal.nhds_zero_basis

Modified src/topology/instances/nnreal.lean
- \+ *lemma* nnreal.nhds_zero
- \+ *lemma* nnreal.nhds_zero_basis



## [2021-07-13 07:09:10](https://github.com/leanprover-community/mathlib/commit/f302c97)
feat(measure_theory/l2_space): the inner product of indicator_const_Lp and a function is the set_integral ([#8229](https://github.com/leanprover-community/mathlib/pull/8229))
#### Estimated changes
Modified src/measure_theory/integrable_on.lean
- \+ *lemma* measure_theory.integrable_on_Lp_of_measure_ne_top

Modified src/measure_theory/l2_space.lean
- \+ *lemma* measure_theory.L2.inner_indicator_const_Lp_eq_inner_set_integral
- \+ *lemma* measure_theory.L2.inner_indicator_const_Lp_eq_set_integral_inner
- \+ *lemma* measure_theory.L2.inner_indicator_const_Lp_one

Modified src/measure_theory/set_integral.lean
- \+ *lemma* integral_eq_zero_of_forall_integral_inner_eq_zero
- \+ *lemma* integral_inner



## [2021-07-12 22:46:15](https://github.com/leanprover-community/mathlib/commit/9dfb9a6)
chore(topology/topological_fiber_bundle): renaming ([#8270](https://github.com/leanprover-community/mathlib/pull/8270))
In this PR I changed
- `prebundle_trivialization` to `topological_fiber_bundle.pretrivialization`
- `bundle_trivialization` to `topological_fiber_bundle.trivialization`
so to make names consistent with `vector_bundle`. I also changed the name of the file for consistency.
#### Estimated changes
Modified src/geometry/manifold/basic_smooth_bundle.lean


Renamed src/topology/topological_fiber_bundle.lean to src/topology/fiber_bundle.lean
- \- *lemma* bundle_trivialization.apply_symm_apply'
- \- *lemma* bundle_trivialization.apply_symm_apply
- \- *lemma* bundle_trivialization.coe_coe
- \- *lemma* bundle_trivialization.coe_fst'
- \- *lemma* bundle_trivialization.coe_fst
- \- *lemma* bundle_trivialization.coe_fst_eventually_eq_proj'
- \- *lemma* bundle_trivialization.coe_fst_eventually_eq_proj
- \- *lemma* bundle_trivialization.coe_mk
- \- *def* bundle_trivialization.comp_homeomorph
- \- *lemma* bundle_trivialization.continuous_at_proj
- \- *lemma* bundle_trivialization.continuous_coord_change
- \- *def* bundle_trivialization.coord_change
- \- *lemma* bundle_trivialization.coord_change_apply_snd
- \- *lemma* bundle_trivialization.coord_change_coord_change
- \- *def* bundle_trivialization.coord_change_homeomorph
- \- *lemma* bundle_trivialization.coord_change_homeomorph_coe
- \- *lemma* bundle_trivialization.coord_change_same
- \- *lemma* bundle_trivialization.coord_change_same_apply
- \- *lemma* bundle_trivialization.frontier_preimage
- \- *lemma* bundle_trivialization.is_image_preimage_prod
- \- *lemma* bundle_trivialization.map_proj_nhds
- \- *lemma* bundle_trivialization.map_target
- \- *lemma* bundle_trivialization.mem_source
- \- *lemma* bundle_trivialization.mem_target
- \- *lemma* bundle_trivialization.mk_coord_change
- \- *lemma* bundle_trivialization.mk_proj_snd'
- \- *lemma* bundle_trivialization.mk_proj_snd
- \- *lemma* bundle_trivialization.proj_symm_apply'
- \- *lemma* bundle_trivialization.proj_symm_apply
- \- *def* bundle_trivialization.restr_open
- \- *lemma* bundle_trivialization.source_inter_preimage_target_inter
- \- *lemma* bundle_trivialization.symm_apply_mk_proj
- \- *def* bundle_trivialization.to_prebundle_trivialization
- \- *def* bundle_trivialization.trans_fiber_homeomorph
- \- *lemma* bundle_trivialization.trans_fiber_homeomorph_apply
- \+/\- *lemma* is_topological_fiber_bundle.exists_trivialization_Icc_subset
- \- *lemma* prebundle_trivialization.apply_symm_apply'
- \- *lemma* prebundle_trivialization.apply_symm_apply
- \- *lemma* prebundle_trivialization.coe_coe
- \- *lemma* prebundle_trivialization.coe_fst'
- \- *lemma* prebundle_trivialization.coe_fst
- \- *lemma* prebundle_trivialization.mem_source
- \- *lemma* prebundle_trivialization.mem_target
- \- *lemma* prebundle_trivialization.mk_proj_snd'
- \- *lemma* prebundle_trivialization.mk_proj_snd
- \- *lemma* prebundle_trivialization.preimage_symm_proj_base_set
- \- *lemma* prebundle_trivialization.preimage_symm_proj_inter
- \- *lemma* prebundle_trivialization.proj_symm_apply'
- \- *lemma* prebundle_trivialization.proj_symm_apply
- \- *def* prebundle_trivialization.set_symm
- \- *lemma* prebundle_trivialization.symm_apply_mk_proj
- \+ *lemma* topological_fiber_bundle.pretrivialization.apply_symm_apply'
- \+ *lemma* topological_fiber_bundle.pretrivialization.apply_symm_apply
- \+ *lemma* topological_fiber_bundle.pretrivialization.coe_coe
- \+ *lemma* topological_fiber_bundle.pretrivialization.coe_fst'
- \+ *lemma* topological_fiber_bundle.pretrivialization.coe_fst
- \+ *lemma* topological_fiber_bundle.pretrivialization.mem_source
- \+ *lemma* topological_fiber_bundle.pretrivialization.mem_target
- \+ *lemma* topological_fiber_bundle.pretrivialization.mk_proj_snd'
- \+ *lemma* topological_fiber_bundle.pretrivialization.mk_proj_snd
- \+ *lemma* topological_fiber_bundle.pretrivialization.preimage_symm_proj_base_set
- \+ *lemma* topological_fiber_bundle.pretrivialization.preimage_symm_proj_inter
- \+ *lemma* topological_fiber_bundle.pretrivialization.proj_symm_apply'
- \+ *lemma* topological_fiber_bundle.pretrivialization.proj_symm_apply
- \+ *def* topological_fiber_bundle.pretrivialization.set_symm
- \+ *lemma* topological_fiber_bundle.pretrivialization.symm_apply_mk_proj
- \+ *lemma* topological_fiber_bundle.trivialization.apply_symm_apply'
- \+ *lemma* topological_fiber_bundle.trivialization.apply_symm_apply
- \+ *lemma* topological_fiber_bundle.trivialization.coe_coe
- \+ *lemma* topological_fiber_bundle.trivialization.coe_fst'
- \+ *lemma* topological_fiber_bundle.trivialization.coe_fst
- \+ *lemma* topological_fiber_bundle.trivialization.coe_fst_eventually_eq_proj'
- \+ *lemma* topological_fiber_bundle.trivialization.coe_fst_eventually_eq_proj
- \+ *lemma* topological_fiber_bundle.trivialization.coe_mk
- \+ *def* topological_fiber_bundle.trivialization.comp_homeomorph
- \+ *lemma* topological_fiber_bundle.trivialization.continuous_at_proj
- \+ *lemma* topological_fiber_bundle.trivialization.continuous_coord_change
- \+ *def* topological_fiber_bundle.trivialization.coord_change
- \+ *lemma* topological_fiber_bundle.trivialization.coord_change_apply_snd
- \+ *lemma* topological_fiber_bundle.trivialization.coord_change_coord_change
- \+ *def* topological_fiber_bundle.trivialization.coord_change_homeomorph
- \+ *lemma* topological_fiber_bundle.trivialization.coord_change_homeomorph_coe
- \+ *lemma* topological_fiber_bundle.trivialization.coord_change_same
- \+ *lemma* topological_fiber_bundle.trivialization.coord_change_same_apply
- \+ *lemma* topological_fiber_bundle.trivialization.frontier_preimage
- \+ *lemma* topological_fiber_bundle.trivialization.is_image_preimage_prod
- \+ *lemma* topological_fiber_bundle.trivialization.map_proj_nhds
- \+ *lemma* topological_fiber_bundle.trivialization.map_target
- \+ *lemma* topological_fiber_bundle.trivialization.mem_source
- \+ *lemma* topological_fiber_bundle.trivialization.mem_target
- \+ *lemma* topological_fiber_bundle.trivialization.mk_coord_change
- \+ *lemma* topological_fiber_bundle.trivialization.mk_proj_snd'
- \+ *lemma* topological_fiber_bundle.trivialization.mk_proj_snd
- \+ *lemma* topological_fiber_bundle.trivialization.proj_symm_apply'
- \+ *lemma* topological_fiber_bundle.trivialization.proj_symm_apply
- \+ *def* topological_fiber_bundle.trivialization.restr_open
- \+ *lemma* topological_fiber_bundle.trivialization.source_inter_preimage_target_inter
- \+ *lemma* topological_fiber_bundle.trivialization.symm_apply_mk_proj
- \+ *def* topological_fiber_bundle.trivialization.to_pretrivialization
- \+ *def* topological_fiber_bundle.trivialization.trans_fiber_homeomorph
- \+ *lemma* topological_fiber_bundle.trivialization.trans_fiber_homeomorph_apply
- \+/\- *def* topological_fiber_bundle_core.local_triv
- \+/\- *def* topological_fiber_bundle_core.local_triv_at
- \- *def* topological_fiber_prebundle.bundle_trivialization_at
- \+ *lemma* topological_fiber_prebundle.continuous_symm_pretrivialization_at
- \- *lemma* topological_fiber_prebundle.continuous_symm_trivialization_at
- \+ *lemma* topological_fiber_prebundle.is_open_source_pretrivialization_at
- \- *lemma* topological_fiber_prebundle.is_open_source_trivialization_at
- \+ *lemma* topological_fiber_prebundle.is_open_target_pretrivialization_at_inter
- \- *lemma* topological_fiber_prebundle.is_open_target_trivialization_at_inter
- \+ *def* topological_fiber_prebundle.trivialization_at

Modified src/topology/vector_bundle.lean
- \- *def* topological_vector_bundle.trivial_bundle_trivialization
- \+ *def* topological_vector_bundle.trivial_topological_vector_bundle.trivialization
- \+/\- *lemma* topological_vector_bundle.trivialization.coe_fst
- \+/\- *def* topological_vector_bundle.trivialization.continuous_linear_equiv_at
- \+/\- *lemma* topological_vector_bundle.trivialization.continuous_linear_equiv_at_apply'
- \+/\- *lemma* topological_vector_bundle.trivialization.continuous_linear_equiv_at_apply



## [2021-07-12 22:46:14](https://github.com/leanprover-community/mathlib/commit/cde5748)
feat(measure_theory/measure_space): add `finite_measure_sub` instance ([#8239](https://github.com/leanprover-community/mathlib/pull/8239))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.sub_le



## [2021-07-12 21:10:34](https://github.com/leanprover-community/mathlib/commit/5ea9a07)
feat(measure_theory/integration): add `lintegral_union` ([#8238](https://github.com/leanprover-community/mathlib/pull/8238))
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.lintegral_union

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measurable_set.cond

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
- \+ *lemma* subgroup.coe_div

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/integrable_on.lean
- \- *lemma* measure_theory.integrable_add
- \+ *lemma* measure_theory.integrable_add_of_disjoint

Modified src/measure_theory/lp_space.lean
- \+ *lemma* measure_theory.mem_ℒp.indicator
- \+ *lemma* measure_theory.mem_ℒp_add_of_disjoint
- \+ *lemma* measure_theory.snorm_indicator_le

Modified src/measure_theory/simple_func_dense.lean
- \- *lemma* measure_theory.L1.simple_func.add_to_simple_func
- \- *lemma* measure_theory.L1.simple_func.coe_add
- \- *lemma* measure_theory.L1.simple_func.coe_coe
- \- *lemma* measure_theory.L1.simple_func.coe_neg
- \- *lemma* measure_theory.L1.simple_func.coe_smul
- \- *lemma* measure_theory.L1.simple_func.coe_sub
- \- *def* measure_theory.L1.simple_func.coe_to_L1
- \- *lemma* measure_theory.L1.simple_func.coe_zero
- \- *lemma* measure_theory.L1.simple_func.dist_eq
- \- *lemma* measure_theory.L1.simple_func.dist_to_simple_func
- \- *lemma* measure_theory.L1.simple_func.edist_eq
- \- *lemma* measure_theory.L1.simple_func.lintegral_edist_to_simple_func_lt_top
- \- *lemma* measure_theory.L1.simple_func.neg_to_simple_func
- \- *lemma* measure_theory.L1.simple_func.norm_eq
- \- *lemma* measure_theory.L1.simple_func.norm_to_L1
- \- *lemma* measure_theory.L1.simple_func.norm_to_simple_func
- \- *lemma* measure_theory.L1.simple_func.smul_to_simple_func
- \- *lemma* measure_theory.L1.simple_func.sub_to_simple_func
- \- *def* measure_theory.L1.simple_func.to_L1
- \- *lemma* measure_theory.L1.simple_func.to_L1_add
- \- *lemma* measure_theory.L1.simple_func.to_L1_eq_mk
- \- *lemma* measure_theory.L1.simple_func.to_L1_eq_to_L1
- \- *lemma* measure_theory.L1.simple_func.to_L1_neg
- \- *lemma* measure_theory.L1.simple_func.to_L1_smul
- \- *lemma* measure_theory.L1.simple_func.to_L1_sub
- \- *lemma* measure_theory.L1.simple_func.to_L1_to_simple_func
- \- *lemma* measure_theory.L1.simple_func.to_L1_zero
- \+ *lemma* measure_theory.L1.simple_func.to_Lp_one_eq_to_L1
- \- *def* measure_theory.L1.simple_func.to_simple_func
- \- *lemma* measure_theory.L1.simple_func.to_simple_func_eq_to_fun
- \- *lemma* measure_theory.L1.simple_func.to_simple_func_to_L1
- \- *lemma* measure_theory.L1.simple_func.zero_to_simple_func
- \- *def* measure_theory.L1.simple_func
- \+ *lemma* measure_theory.Lp.simple_func.add_to_simple_func
- \+ *lemma* measure_theory.Lp.simple_func.coe_coe
- \+ *lemma* measure_theory.Lp.simple_func.coe_smul
- \+ *def* measure_theory.Lp.simple_func.coe_to_Lp
- \+ *lemma* measure_theory.Lp.simple_func.neg_to_simple_func
- \+ *lemma* measure_theory.Lp.simple_func.norm_to_Lp
- \+ *lemma* measure_theory.Lp.simple_func.norm_to_simple_func
- \+ *lemma* measure_theory.Lp.simple_func.smul_to_simple_func
- \+ *lemma* measure_theory.Lp.simple_func.sub_to_simple_func
- \+ *def* measure_theory.Lp.simple_func.to_Lp
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_add
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_eq_mk
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_eq_to_Lp
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_neg
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_smul
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_sub
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_to_simple_func
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_zero
- \+ *def* measure_theory.Lp.simple_func.to_simple_func
- \+ *lemma* measure_theory.Lp.simple_func.to_simple_func_eq_to_fun
- \+ *lemma* measure_theory.Lp.simple_func.to_simple_func_to_Lp
- \+ *lemma* measure_theory.Lp.simple_func.zero_to_simple_func
- \+ *def* measure_theory.Lp.simple_func
- \+ *lemma* measure_theory.mem_ℒp.induction
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_univ_L1



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
- \+ *def* add_monoid_hom.op
- \+ *def* add_monoid_hom.unop
- \+ *def* monoid_hom.op
- \+ *def* monoid_hom.unop
- \+ *def* ring_hom.op
- \+ *def* ring_hom.unop



## [2021-07-12 16:03:49](https://github.com/leanprover-community/mathlib/commit/6fa678f)
feat(ring_theory): `coe_submodule S (⊤ : ideal R) = 1` ([#8272](https://github.com/leanprover-community/mathlib/pull/8272))
A little `simp` lemma and its dependencies. As I was implementing it, I saw the definition of `has_one (submodule R A)` can be cleaned up a bit.
#### Estimated changes
Modified src/algebra/algebra/operations.lean
- \+ *lemma* submodule.algebra_map_mem
- \+ *lemma* submodule.mem_one
- \- *theorem* submodule.one_eq_map_top
- \+ *theorem* submodule.one_eq_range

Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean
- \+ *lemma* is_localization.coe_submodule_top



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
- \+ *theorem* list.map_map_permutations_aux2
- \+/\- *theorem* list.map_permutations_aux2
- \+ *theorem* list.permutations_aux2_comp_append
- \+ *lemma* list.permutations_aux2_snd_eq



## [2021-07-12 12:59:26](https://github.com/leanprover-community/mathlib/commit/695cb07)
feat({data,linear_algebra}/{finsupp,dfinsupp}): add `{add_submonoid,submodule}.[d]finsupp_sum_mem` ([#8269](https://github.com/leanprover-community/mathlib/pull/8269))
These lemmas are trivial consequences of the finset lemmas, but having them avoids having to unfold `[d]finsupp.sum`.
`dfinsupp_sum_add_hom_mem` is particularly useful because this one has some messy decidability arguments to eliminate.
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* add_submonoid.dfinsupp_sum_add_hom_mem
- \+ *lemma* submonoid.dfinsupp_prod_mem

Modified src/data/finsupp/basic.lean
- \+ *lemma* submonoid.finsupp_prod_mem

Modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* submodule.dfinsupp_sum_add_hom_mem
- \+ *lemma* submodule.dfinsupp_sum_mem

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* submodule.finsupp_sum_mem



## [2021-07-12 10:54:32](https://github.com/leanprover-community/mathlib/commit/40ffaa5)
feat(linear_algebra/free_module): add module.free.resolution ([#8231](https://github.com/leanprover-community/mathlib/pull/8231))
Any module is a quotient of a free module. This is stated as surjectivity of `finsupp.total M M R id : (M →₀ R) →ₗ[R] M`.
#### Estimated changes
Modified src/algebra/module/projective.lean


Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.total_id_surjective
- \+ *theorem* finsupp.total_range
- \+ *lemma* finsupp.total_surjective

Modified src/linear_algebra/free_module.lean




## [2021-07-12 07:00:28](https://github.com/leanprover-community/mathlib/commit/e1c649d)
feat(category_theory/abelian): the five lemma ([#8265](https://github.com/leanprover-community/mathlib/pull/8265))
#### Estimated changes
Modified src/algebra/homology/exact.lean


Modified src/category_theory/abelian/basic.lean
- \+ *lemma* category_theory.abelian.coimages.comp_coimage_π_eq_zero
- \+ *lemma* category_theory.abelian.epi_fst_of_factor_thru_epi_mono_factorization
- \+ *lemma* category_theory.abelian.epi_fst_of_is_limit
- \+ *lemma* category_theory.abelian.epi_snd_of_is_limit
- \+ *lemma* category_theory.abelian.mono_inl_of_factor_thru_epi_mono_factorization
- \+ *lemma* category_theory.abelian.mono_inl_of_is_colimit
- \+ *lemma* category_theory.abelian.mono_inr_of_is_colimit

Modified src/category_theory/abelian/diagram_lemmas/four.lean
- \+ *lemma* category_theory.abelian.epi_of_epi_of_epi_of_mono
- \+ *lemma* category_theory.abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso

Modified src/category_theory/abelian/exact.lean
- \+ *def* category_theory.abelian.is_colimit_coimage
- \+ *def* category_theory.abelian.is_colimit_image

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* category_theory.limits.pullback_cone.is_limit_of_factors
- \+ *def* category_theory.limits.pushout_cocone.is_colimit_of_factors

Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* category_theory.limits.comp_factor_thru_image_eq_zero

Modified src/category_theory/subobject/limits.lean
- \+ *lemma* category_theory.limits.factor_thru_kernel_subobject_comp_kernel_subobject_iso



## [2021-07-12 06:15:32](https://github.com/leanprover-community/mathlib/commit/92d0dd8)
feat(category_theory/limits): monomorphisms from initial ([#8099](https://github.com/leanprover-community/mathlib/pull/8099))
Defines a class for categories where every morphism from initial is a monomorphism. If the category has a terminal object, this is equivalent to saying the unique morphism from initial to terminal is a monomorphism, so this is essentially a "zero_le_one" for categories. I'm happy to change the name of this class!
This axiom does not appear to have a common name, though it is (equivalent to) the second of Freyd's AT axioms: specifically it is a property shared by abelian categories and pretoposes. The main advantage to this class is that it is the precise condition required for the subobject lattice to have a bottom element, resolving the discussion here: https://github.com/leanprover-community/mathlib/pull/6278#discussion_r577702542
I've also made some minor changes to later parts of this file, essentially de-duplicating arguments, and moving the `comparison` section up so that all the results about terminal objects in index categories of limits are together rather than split in two.
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean
- \+/\- *def* category_theory.limits.cocone_of_diagram_terminal
- \+/\- *def* category_theory.limits.colimit_of_diagram_terminal
- \+/\- *def* category_theory.limits.colimit_of_terminal
- \+/\- *def* category_theory.limits.cone_of_diagram_initial
- \+ *lemma* category_theory.limits.initial_mono_class.of_initial
- \+ *lemma* category_theory.limits.initial_mono_class.of_is_initial
- \+ *lemma* category_theory.limits.initial_mono_class.of_is_terminal
- \+ *lemma* category_theory.limits.initial_mono_class.of_terminal
- \+ *lemma* category_theory.limits.is_initial.mono_from
- \+ *def* category_theory.limits.is_initial.unique_up_to_iso
- \+ *def* category_theory.limits.is_terminal.unique_up_to_iso
- \+/\- *def* category_theory.limits.limit_of_diagram_initial
- \+/\- *def* category_theory.limits.limit_of_initial



## [2021-07-12 04:01:46](https://github.com/leanprover-community/mathlib/commit/e22789e)
feat(algebra/big_operators/finprod): add a few lemmas ([#8261](https://github.com/leanprover-community/mathlib/pull/8261))
* add `finprod_eq_single` and `finsum_eq_single`;
* add `finprod_induction` and `finsum_induction`;
* add `single_le_finprod` and `single_le_finsum`;
* add `one_le_finprod'` and `finsum_nonneg`.
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_eq_single
- \+ *lemma* finprod_induction
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
- \+ *lemma* monoid_hom.injective_iff'

Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.perm.extend_domain_eq_one_iff



## [2021-07-11 20:46:12](https://github.com/leanprover-community/mathlib/commit/24d7a8c)
feat(group_theory/quotient_group): lemmas for quotients involving `subgroup_of` ([#8111](https://github.com/leanprover-community/mathlib/pull/8111))
#### Estimated changes
Modified src/group_theory/quotient_group.lean
- \+ *def* quotient_group.equiv_quotient_subgroup_of_of_eq
- \+ *def* quotient_group.quotient_map_subgroup_of_of_le



## [2021-07-11 20:13:23](https://github.com/leanprover-community/mathlib/commit/19beb12)
feat(measure_theory/{lp_space,set_integral}): extend linear map lemmas from R to is_R_or_C ([#8210](https://github.com/leanprover-community/mathlib/pull/8210))
#### Estimated changes
Modified src/analysis/calculus/parametric_integral.lean


Modified src/measure_theory/lp_space.lean
- \+/\- *lemma* continuous_linear_map.coe_fn_comp_Lp
- \+/\- *def* continuous_linear_map.comp_Lp
- \+/\- *def* continuous_linear_map.comp_LpL
- \+/\- *def* continuous_linear_map.comp_Lpₗ
- \+/\- *lemma* continuous_linear_map.norm_compLpL_le
- \+/\- *lemma* continuous_linear_map.norm_comp_Lp_le

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* continuous_linear_map.continuous_integral_comp_L1
- \+/\- *lemma* continuous_linear_map.integral_comp_L1_comm
- \+/\- *lemma* continuous_linear_map.integral_comp_Lp
- \+/\- *lemma* continuous_linear_map.integral_comp_comm'
- \+/\- *lemma* continuous_linear_map.integral_comp_comm
- \+/\- *lemma* integral_conj
- \+ *lemma* integral_im
- \+/\- *lemma* integral_of_real
- \+ *lemma* integral_re
- \+/\- *lemma* linear_isometry.integral_comp_comm



## [2021-07-11 19:28:27](https://github.com/leanprover-community/mathlib/commit/6d200cb)
feat(analysis/normed_space/inner_product): Bessel's inequality ([#8251](https://github.com/leanprover-community/mathlib/pull/8251))
A proof both of Bessel's inequality and that the infinite sum defined by Bessel's inequality converges.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* orthonormal.inner_left_right_finset
- \+ *lemma* orthonormal.inner_products_summable
- \+ *lemma* orthonormal.sum_inner_products_le
- \+ *lemma* orthonormal.tsum_inner_products_le



## [2021-07-11 14:37:02](https://github.com/leanprover-community/mathlib/commit/bee165a)
feat(category_theory/abelian/opposite): Adds some op-related isomorphism for (co)kernels. ([#8255](https://github.com/leanprover-community/mathlib/pull/8255))
#### Estimated changes
Modified src/category_theory/abelian/opposite.lean
- \+ *def* category_theory.cokernel_op_op
- \+ *def* category_theory.cokernel_op_unop
- \+ *def* category_theory.cokernel_unop_op
- \+ *def* category_theory.cokernel_unop_unop
- \+ *def* category_theory.kernel_op_op
- \+ *def* category_theory.kernel_op_unop
- \+ *def* category_theory.kernel_unop_op
- \+ *def* category_theory.kernel_unop_unop



## [2021-07-11 13:10:23](https://github.com/leanprover-community/mathlib/commit/1e62218)
feat(data/int/gcd): norm_num extension for gcd ([#8053](https://github.com/leanprover-community/mathlib/pull/8053))
Implements a `norm_num` plugin to evaluate terms like `nat.gcd 6 8 = 2`, `nat.coprime 127 128`, and so on for `{nat, int}.{gcd, lcm, coprime}`.
#### Estimated changes
Modified src/data/int/gcd.lean
- \+ *lemma* tactic.norm_num.int_gcd_helper'
- \+ *lemma* tactic.norm_num.int_gcd_helper
- \+ *lemma* tactic.norm_num.int_gcd_helper_neg_left
- \+ *lemma* tactic.norm_num.int_gcd_helper_neg_right
- \+ *lemma* tactic.norm_num.int_lcm_helper
- \+ *lemma* tactic.norm_num.int_lcm_helper_neg_left
- \+ *lemma* tactic.norm_num.int_lcm_helper_neg_right
- \+ *lemma* tactic.norm_num.nat_coprime_helper_1
- \+ *lemma* tactic.norm_num.nat_coprime_helper_2
- \+ *lemma* tactic.norm_num.nat_coprime_helper_zero_left
- \+ *lemma* tactic.norm_num.nat_coprime_helper_zero_right
- \+ *lemma* tactic.norm_num.nat_gcd_helper_1
- \+ *lemma* tactic.norm_num.nat_gcd_helper_2
- \+ *lemma* tactic.norm_num.nat_gcd_helper_dvd_left
- \+ *lemma* tactic.norm_num.nat_gcd_helper_dvd_right
- \+ *lemma* tactic.norm_num.nat_lcm_helper
- \+ *lemma* tactic.norm_num.nat_not_coprime_helper

Modified src/data/nat/gcd.lean
- \+ *theorem* nat.not_coprime_zero_zero

Modified test/norm_num.lean


Added test/norm_num_ext.lean




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
- \+ *lemma* real.tendsto_mul_log_one_plus_div_at_top

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* tendsto_one_plus_div_pow_exp
- \+ *lemma* tendsto_one_plus_div_rpow_exp



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
- \+ *def* category_theory.adjunction.adj_to_comonad_iso
- \+ *def* category_theory.adjunction.adj_to_monad_iso
- \+/\- *def* category_theory.adjunction.to_comonad
- \+/\- *def* category_theory.adjunction.to_monad
- \+/\- *def* category_theory.comonad.comparison
- \+ *def* category_theory.comonad.comparison_forget
- \+ *lemma* category_theory.comonad.left_comparison
- \- *def* category_theory.comparison_forget
- \+/\- *def* category_theory.monad.comparison
- \+/\- *def* category_theory.monad.comparison_forget
- \+ *lemma* category_theory.monad.left_comparison

Modified src/category_theory/monad/algebra.lean
- \+/\- *def* category_theory.comonad.adj
- \+ *lemma* category_theory.comonad.of_left_adjoint_forget
- \+ *lemma* category_theory.comonad.right_adjoint_forget
- \+ *lemma* category_theory.monad.left_adjoint_forget
- \+ *lemma* category_theory.monad.of_right_adjoint_forget

Modified src/category_theory/monad/basic.lean
- \+ *def* category_theory.comonad_iso.mk
- \+ *lemma* category_theory.comonad_to_functor_map_iso_comonad_iso_mk
- \+ *def* category_theory.monad_iso.mk
- \+ *lemma* category_theory.monad_to_functor_map_iso_monad_iso_mk

Modified src/category_theory/skeletal.lean


Modified src/topology/category/Compactum.lean




## [2021-07-10 18:38:10](https://github.com/leanprover-community/mathlib/commit/8b4628e)
feat(data/fintype/basic): induction principle for finite types ([#8158](https://github.com/leanprover-community/mathlib/pull/8158))
This lets us prove things about finite types by induction, analogously to proving things about natural numbers by induction. Here `pempty` plays the role of `0` and `option` plays the role of `nat.succ`. We need an extra hypothesis that our statement is invariant under equivalence of types. Used in [#8019](https://github.com/leanprover-community/mathlib/pull/8019).
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.induction_empty_option
- \+ *def* fintype.trunc_rec_empty_option



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
- \+ *lemma* continuous_linear_equiv.coe_of_bijective
- \+ *lemma* continuous_linear_map.range_eq_map_coprod_subtypeL_equiv_of_is_compl



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
- \+ *def* category_theory.creates_colimit_of_iso_diagram
- \+ *def* category_theory.creates_limit_of_iso_diagram



## [2021-07-10 03:32:13](https://github.com/leanprover-community/mathlib/commit/d0e09dd)
feat(linear_algebra/matrix/nonsingular_inverse): more lemmas ([#8216](https://github.com/leanprover-community/mathlib/pull/8216))
add more defs and lemmas
#### Estimated changes
Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+/\- *def* matrix.det_invertible_of_left_inverse
- \+/\- *def* matrix.det_invertible_of_right_inverse
- \+ *lemma* matrix.inv_eq_left_inv
- \+ *lemma* matrix.inv_eq_nonsing_inv_of_invertible
- \+ *lemma* matrix.inv_eq_right_inv
- \+ *lemma* matrix.inv_mul_of_invertible
- \+ *def* matrix.invertible_of_left_inverse
- \+ *def* matrix.invertible_of_right_inverse
- \+ *lemma* matrix.is_unit_det_of_invertible
- \+/\- *lemma* matrix.is_unit_det_of_left_inverse
- \+/\- *lemma* matrix.is_unit_det_of_right_inverse
- \+ *lemma* matrix.left_inv_eq_left_inv
- \+ *lemma* matrix.mul_inv_of_invertible
- \+/\- *lemma* matrix.nonsing_inv_left_right
- \+/\- *lemma* matrix.nonsing_inv_right_left
- \+ *lemma* matrix.right_inv_eq_left_inv
- \+ *lemma* matrix.right_inv_eq_right_inv

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
- \+/\- *lemma* category_theory.Kleisli.comp_def
- \+/\- *lemma* category_theory.Kleisli.id_def
- \+/\- *def* category_theory.Kleisli.mk
- \+/\- *def* category_theory.Kleisli



## [2021-07-09 19:00:53](https://github.com/leanprover-community/mathlib/commit/a444e81)
feat(measure_theory/borel_space): a preconnected set is measurable ([#8044](https://github.com/leanprover-community/mathlib/pull/8044))
In a conditionally complete linear order equipped with the order topology and the corresponding borel σ-algebra, any preconnected set is measurable.
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* set.finite_of_forall_between_eq_endpoints

Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_preconnected.measurable_set
- \+/\- *lemma* measurable_set_lt'
- \+/\- *lemma* measurable_set_lt
- \+ *lemma* set.ord_connected.measurable_set

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* is_preconnected.ord_connected
- \+ *lemma* set.ord_connected.is_preconnected



## [2021-07-09 15:19:06](https://github.com/leanprover-community/mathlib/commit/bcd61b1)
feat(algebra/category): provide right adjoint instances for forget ([#8235](https://github.com/leanprover-community/mathlib/pull/8235))
Also adds some universe variables since they weren't inferred sensibly.
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean
- \+/\- *def* Algebra.adj
- \+/\- *def* Algebra.free
- \+/\- *def* Algebra.of
- \+/\- *def* Algebra.of_self_iso

Modified src/algebra/category/CommRing/adjunctions.lean
- \+/\- *def* CommRing.adj
- \+/\- *def* CommRing.free

Modified src/algebra/category/Group/adjunctions.lean


Modified src/algebra/category/Module/adjunctions.lean


Modified src/algebra/category/Mon/adjunctions.lean
- \+ *def* adj
- \+ *def* free

Modified src/topology/category/Top/adjunctions.lean




## [2021-07-09 13:36:51](https://github.com/leanprover-community/mathlib/commit/ee01817)
chore(data/set/basic): use `decidable_pred (∈ s)` instead of `decidable_pred s`. ([#8211](https://github.com/leanprover-community/mathlib/pull/8211))
The latter exploits the fact that sets are functions to Prop, and is an annoying form as lemmas are never stated about it.
In future we should consider removing the `set.decidable_mem` instance which encourages this misuse.
Making this change reveals a collection of pointless decidable arguments requiring that finset membership be decidable; something which is always true anyway.
Two proofs in `data/pequiv` caused a crash inside the C++ portion of the `finish` tactic; it was easier to just write the simple proofs manually than to debug the C++ code.
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \+/\- *def* continuous_multilinear_map.curry_fin_finset

Modified src/combinatorics/simple_graph/basic.lean


Modified src/data/equiv/basic.lean
- \+/\- *lemma* equiv.set.insert_apply_left
- \+/\- *lemma* equiv.set.insert_apply_right
- \+/\- *lemma* equiv.set.insert_symm_apply_inl
- \+/\- *lemma* equiv.set.insert_symm_apply_inr
- \+/\- *lemma* equiv.set.sum_compl_apply_inl
- \+/\- *lemma* equiv.set.sum_compl_apply_inr
- \+/\- *lemma* equiv.set.sum_compl_symm_apply
- \+/\- *lemma* equiv.set.sum_compl_symm_apply_of_mem
- \+/\- *lemma* equiv.set.sum_compl_symm_apply_of_not_mem

Modified src/data/equiv/denumerable.lean
- \+/\- *def* nat.subtype.denumerable
- \+/\- *def* nat.subtype.of_nat

Modified src/data/equiv/encodable/basic.lean
- \+/\- *def* encodable.decidable_range_encode

Modified src/data/fintype/sort.lean


Modified src/data/nat/basic.lean


Modified src/data/pequiv.lean
- \+/\- *lemma* pequiv.mem_of_set_iff
- \+/\- *lemma* pequiv.mem_of_set_self_iff
- \+/\- *def* pequiv.of_set
- \+/\- *lemma* pequiv.of_set_eq_refl
- \+/\- *lemma* pequiv.of_set_eq_some_iff
- \+/\- *lemma* pequiv.of_set_eq_some_self_iff

Modified src/data/pfun.lean
- \+/\- *def* pfun.eval_opt

Modified src/data/set/basic.lean


Modified src/data/set/finite.lean
- \+/\- *def* set.fintype_subset

Modified src/data/sym2.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/group_theory/coset.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/subgroup.lean


Modified src/group_theory/subgroup.lean


Modified src/linear_algebra/multilinear.lean
- \+/\- *def* multilinear_map.curry_fin_finset
- \+/\- *lemma* multilinear_map.curry_fin_finset_apply

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable.piecewise

Modified src/order/order_iso_nat.lean


Modified src/ring_theory/free_comm_ring.lean
- \+/\- *theorem* free_comm_ring.map_subtype_val_restriction
- \+/\- *def* free_comm_ring.restriction



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
Added src/data/bundle.lean
- \+ *lemma* bundle.coe_fst
- \+ *lemma* bundle.coe_snd_map_apply
- \+ *lemma* bundle.coe_snd_map_smul
- \+ *def* bundle.proj
- \+ *lemma* bundle.to_total_space_coe
- \+ *def* bundle.total_space
- \+ *def* bundle.total_space_mk
- \+ *def* bundle.trivial.proj_snd
- \+ *def* bundle.trivial

Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_at.comp_continuous_within_at
- \+ *lemma* continuous_within_at.fst
- \+ *lemma* continuous_within_at.snd
- \+ *lemma* continuous_within_at_prod_iff

Modified src/topology/topological_fiber_bundle.lean
- \- *lemma* bundle.coe_fst
- \- *lemma* bundle.coe_snd_map_apply
- \- *lemma* bundle.coe_snd_map_smul
- \- *def* bundle.proj
- \- *lemma* bundle.to_total_space_coe
- \- *def* bundle.total_space
- \- *def* bundle.total_space_mk
- \- *def* bundle.trivial.proj_snd
- \- *def* bundle.trivial
- \+ *lemma* bundle_trivialization.source_inter_preimage_target_inter
- \+/\- *lemma* topological_fiber_bundle_core.base_set_at
- \- *def* topological_fiber_bundle_core.local_triv'
- \- *lemma* topological_fiber_bundle_core.local_triv'_apply
- \- *lemma* topological_fiber_bundle_core.local_triv'_coe
- \- *lemma* topological_fiber_bundle_core.local_triv'_source
- \- *lemma* topological_fiber_bundle_core.local_triv'_symm_apply
- \- *lemma* topological_fiber_bundle_core.local_triv'_target
- \- *lemma* topological_fiber_bundle_core.local_triv'_trans
- \+/\- *def* topological_fiber_bundle_core.local_triv
- \+/\- *lemma* topological_fiber_bundle_core.local_triv_apply
- \+ *def* topological_fiber_bundle_core.local_triv_as_local_equiv
- \+ *lemma* topological_fiber_bundle_core.local_triv_as_local_equiv_apply
- \+ *lemma* topological_fiber_bundle_core.local_triv_as_local_equiv_coe
- \+ *lemma* topological_fiber_bundle_core.local_triv_as_local_equiv_source
- \+ *lemma* topological_fiber_bundle_core.local_triv_as_local_equiv_symm
- \+ *lemma* topological_fiber_bundle_core.local_triv_as_local_equiv_target
- \+ *lemma* topological_fiber_bundle_core.local_triv_as_local_equiv_trans
- \+ *def* topological_fiber_bundle_core.local_triv_at
- \+ *lemma* topological_fiber_bundle_core.local_triv_at_def
- \- *def* topological_fiber_bundle_core.local_triv_at_ext
- \- *lemma* topological_fiber_bundle_core.local_triv_at_ext_def
- \- *lemma* topological_fiber_bundle_core.local_triv_coe
- \- *def* topological_fiber_bundle_core.local_triv_ext
- \- *lemma* topological_fiber_bundle_core.local_triv_ext_apply
- \- *lemma* topological_fiber_bundle_core.local_triv_ext_symm_apply
- \- *lemma* topological_fiber_bundle_core.local_triv_ext_symm_fst
- \- *lemma* topological_fiber_bundle_core.local_triv_source
- \- *lemma* topological_fiber_bundle_core.local_triv_symm
- \+/\- *lemma* topological_fiber_bundle_core.local_triv_symm_fst
- \- *lemma* topological_fiber_bundle_core.local_triv_target
- \- *lemma* topological_fiber_bundle_core.local_triv_trans
- \- *lemma* topological_fiber_bundle_core.mem_local_triv'_source
- \- *lemma* topological_fiber_bundle_core.mem_local_triv'_target
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv_as_local_equiv_source
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv_as_local_equiv_target
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv_at_base_set
- \- *lemma* topological_fiber_bundle_core.mem_local_triv_at_ext_base_set
- \- *lemma* topological_fiber_bundle_core.mem_local_triv_ext_source
- \- *lemma* topological_fiber_bundle_core.mem_local_triv_ext_target
- \+/\- *lemma* topological_fiber_bundle_core.mem_local_triv_source
- \+/\- *lemma* topological_fiber_bundle_core.mem_local_triv_target
- \+/\- *lemma* topological_fiber_bundle_core.open_source'
- \- *lemma* topological_fiber_bundle_core.open_target'

Modified src/topology/vector_bundle.lean




## [2021-07-09 12:52:46](https://github.com/leanprover-community/mathlib/commit/abde210)
feat(analysis/complex/isometry): restate result more abstractly ([#7908](https://github.com/leanprover-community/mathlib/pull/7908))
Define `rotation` as a group homomorphism from the circle to the isometry group of `ℂ`.  State the classification of isometries of `ℂ` more abstractly, using this construction.  Also golf some proofs.
#### Estimated changes
Modified src/analysis/complex/isometry.lean
- \- *lemma* linear_isometry.abs_apply_sub_one_eq_abs_sub_one
- \+/\- *lemma* linear_isometry_complex
- \+/\- *lemma* linear_isometry_complex_aux
- \+ *def* rotation
- \+ *lemma* rotation_apply
- \+ *def* rotation_aux

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.coe_to_continuous_linear_equiv
- \+ *def* linear_isometry_equiv.to_continuous_linear_equiv



## [2021-07-09 09:42:47](https://github.com/leanprover-community/mathlib/commit/1134865)
feat(category_theory/limits): finite products from finite limits ([#8236](https://github.com/leanprover-community/mathlib/pull/8236))
Adds instances for finite products from finite limits.
#### Estimated changes
Modified src/category_theory/limits/shapes/finite_products.lean
- \- *lemma* category_theory.limits.has_finite_coproducts_of_has_finite_colimits
- \- *lemma* category_theory.limits.has_finite_products_of_has_finite_limits



## [2021-07-08 23:05:26](https://github.com/leanprover-community/mathlib/commit/e46447b)
feat(measure_theory/measure_space): prob_le_one ([#7913](https://github.com/leanprover-community/mathlib/pull/7913))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.prob_add_prob_compl
- \+ *lemma* measure_theory.prob_le_one



## [2021-07-08 18:57:18](https://github.com/leanprover-community/mathlib/commit/9d40a59)
feat(group_theory,linear_algebra): third isomorphism theorem for groups and modules ([#8203](https://github.com/leanprover-community/mathlib/pull/8203))
This PR proves the third isomorphism theorem for (additive) groups and modules, and also adds a few `simp` lemmas that I needed.
#### Estimated changes
Modified docs/overview.yaml


Modified src/group_theory/quotient_group.lean
- \+ *lemma* quotient_group.map_coe
- \+ *lemma* quotient_group.map_mk'
- \+ *def* quotient_group.quotient_quotient_equiv_quotient
- \+ *def* quotient_group.quotient_quotient_equiv_quotient_aux
- \+ *lemma* quotient_group.quotient_quotient_equiv_quotient_aux_coe
- \+ *lemma* quotient_group.quotient_quotient_equiv_quotient_aux_coe_coe

Modified src/linear_algebra/basic.lean
- \+ *def* submodule.quotient_quotient_equiv_quotient
- \+ *def* submodule.quotient_quotient_equiv_quotient_aux
- \+ *lemma* submodule.quotient_quotient_equiv_quotient_aux_mk
- \+ *lemma* submodule.quotient_quotient_equiv_quotient_aux_mk_mk



## [2021-07-08 17:14:02](https://github.com/leanprover-community/mathlib/commit/a7b660e)
feat(linear_algebra/prod): add coprod_map_prod ([#8220](https://github.com/leanprover-community/mathlib/pull/8220))
This also adds `submodule.coe_sup` and `set.mem_finset_prod`. The latter was intended to be used to show `submodule.coe_supr`, but I didn't really need that and it was hard to prove.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* set.finset_prod_mem_finset_prod
- \+ *lemma* set.finset_prod_subset_finset_prod
- \+ *lemma* set.mem_finset_prod
- \+ *lemma* set.mem_fintype_prod

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.coe_sup

Modified src/linear_algebra/prod.lean
- \+ *lemma* linear_map.coprod_map_prod



## [2021-07-08 16:41:12](https://github.com/leanprover-community/mathlib/commit/13486fe)
chore(measure_theory/measure_space): untangle `probability_measure`, `finite_measure`, and `has_no_atoms` ([#8222](https://github.com/leanprover-community/mathlib/pull/8222))
This only moves existing lemmas around. Putting all the instance together up front seems to result in lemmas being added in adhoc places - by adding `section`s, this should guide future contributions.
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* measure_theory.measure.restrict_singleton'



## [2021-07-08 14:46:44](https://github.com/leanprover-community/mathlib/commit/b10062e)
feat(data/finset/noncomm_prod): noncomm_prod_union_of_disjoint ([#8169](https://github.com/leanprover-community/mathlib/pull/8169))
#### Estimated changes
Modified src/data/finset/noncomm_prod.lean
- \+ *lemma* finset.noncomm_prod_union_of_disjoint



## [2021-07-08 13:06:54](https://github.com/leanprover-community/mathlib/commit/a4b0b48)
feat(data/nat/basic): lt_one_iff ([#8224](https://github.com/leanprover-community/mathlib/pull/8224))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.lt_one_iff



## [2021-07-08 11:22:43](https://github.com/leanprover-community/mathlib/commit/fb22ae3)
refactor(order/rel_iso): move statements about intervals to data/set/intervals ([#8150](https://github.com/leanprover-community/mathlib/pull/8150))
This means that we can talk about `rel_iso` without needing to transitively import `ordered_group`s
This PR takes advantage of this to define `order_iso.mul_(left|right)[']` to mirror `equiv.mul_(left|right)[']`.
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *def* order_iso.mul_left'
- \+ *def* order_iso.mul_right'

Modified src/algebra/ordered_group.lean
- \+ *def* order_iso.mul_left
- \+ *def* order_iso.mul_right

Modified src/data/set/intervals/basic.lean
- \+ *def* order_iso.Ici_bot
- \+ *def* order_iso.Iic_top
- \+ *lemma* order_iso.preimage_Icc
- \+ *lemma* order_iso.preimage_Ici
- \+ *lemma* order_iso.preimage_Ico
- \+ *lemma* order_iso.preimage_Iic
- \+ *lemma* order_iso.preimage_Iio
- \+ *lemma* order_iso.preimage_Ioc
- \+ *lemma* order_iso.preimage_Ioi
- \+ *lemma* order_iso.preimage_Ioo

Modified src/order/rel_iso.lean
- \- *def* order_iso.Ici_bot
- \- *def* order_iso.Iic_top
- \- *lemma* order_iso.preimage_Icc
- \- *lemma* order_iso.preimage_Ici
- \- *lemma* order_iso.preimage_Ico
- \- *lemma* order_iso.preimage_Iic
- \- *lemma* order_iso.preimage_Iio
- \- *lemma* order_iso.preimage_Ioc
- \- *lemma* order_iso.preimage_Ioi
- \- *lemma* order_iso.preimage_Ioo



## [2021-07-08 09:27:54](https://github.com/leanprover-community/mathlib/commit/03e2cbd)
chore(group_theory/perm/support): support_pow_le over nat ([#8225](https://github.com/leanprover-community/mathlib/pull/8225))
Previously, both `support_pow_le` and `support_gpow_le` had the
power as an `int`. Now we properly differentiate the two and avoid
slow defeq checks.
#### Estimated changes
Modified src/group_theory/perm/cycles.lean
- \+ *lemma* equiv.perm.is_cycle_of_is_cycle_gpow
- \- *lemma* equiv.perm.is_cycle_of_is_cycle_pow

Modified src/group_theory/perm/support.lean
- \+/\- *lemma* equiv.perm.support_pow_le



## [2021-07-08 02:02:10](https://github.com/leanprover-community/mathlib/commit/0ee238c)
chore(scripts): update nolints.txt ([#8227](https://github.com/leanprover-community/mathlib/pull/8227))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-07-07 20:50:25](https://github.com/leanprover-community/mathlib/commit/70aef28)
feat(group_theory/perm/list): concrete permutations from a list ([#7451](https://github.com/leanprover-community/mathlib/pull/7451))
#### Estimated changes
Added src/group_theory/perm/list.lean
- \+ *def* list.form_perm
- \+ *lemma* list.form_perm_apply_head
- \+ *lemma* list.form_perm_apply_last
- \+ *lemma* list.form_perm_apply_lt
- \+ *lemma* list.form_perm_apply_mem_of_mem
- \+ *lemma* list.form_perm_apply_nth_le
- \+ *lemma* list.form_perm_apply_nth_le_length
- \+ *lemma* list.form_perm_apply_nth_le_zero
- \+ *lemma* list.form_perm_apply_of_not_mem
- \+ *lemma* list.form_perm_cons_concat_apply_last
- \+ *lemma* list.form_perm_cons_cons
- \+ *lemma* list.form_perm_eq_head_iff_eq_last
- \+ *lemma* list.form_perm_eq_of_is_rotated
- \+ *lemma* list.form_perm_ext_iff
- \+ *lemma* list.form_perm_nil
- \+ *lemma* list.form_perm_pair
- \+ *lemma* list.form_perm_pow_apply_nth_le
- \+ *lemma* list.form_perm_reverse
- \+ *lemma* list.form_perm_rotate
- \+ *lemma* list.form_perm_rotate_one
- \+ *lemma* list.form_perm_singleton
- \+ *lemma* list.support_form_perm_le'
- \+ *lemma* list.support_form_perm_le
- \+ *lemma* list.support_form_perm_of_nodup'
- \+ *lemma* list.support_form_perm_of_nodup
- \+ *lemma* list.zip_with_swap_prod_support'
- \+ *lemma* list.zip_with_swap_prod_support



## [2021-07-07 17:46:10](https://github.com/leanprover-community/mathlib/commit/5f2358c)
fix(data/complex/basic): ensure `algebra ℝ ℂ` is computable ([#8166](https://github.com/leanprover-community/mathlib/pull/8166))
Without this `complex.ring` instance, `ring ℂ` is found via `division_ring.to_ring` and `field.to_division_ring`, and `complex.field` is non-computable.
The non-computable-ness previously contaminated `distrib_mul_action R ℂ` and even some properties of `finset.sum` on complex numbers! To avoid this type of mistake again, we remove `noncomputable theory` and manually flag the parts we actually expect to be computable.
#### Estimated changes
Modified src/data/complex/basic.lean


Modified src/data/complex/module.lean
- \- *def* complex.basis_one_I
- \+ *def* complex.lift



## [2021-07-07 15:54:45](https://github.com/leanprover-community/mathlib/commit/e0ca853)
feat(algebra/group/units): teach `simps` about `units` ([#8204](https://github.com/leanprover-community/mathlib/pull/8204))
This also introduces `units.copy` to match `invertible.copy`, and uses it to make some lemmas in normed_space/units true by `rfl` (and generated by `simps`).
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *def* units.copy
- \+ *lemma* units.copy_eq
- \+ *def* units.simps.coe
- \+ *def* units.simps.coe_inv

Modified src/algebra/invertible.lean
- \- *lemma* unit_of_invertible_inv
- \- *lemma* unit_of_invertible_val

Modified src/algebra/lie/classical.lean


Modified src/analysis/normed_space/units.lean
- \- *lemma* units.add_coe
- \- *lemma* units.one_sub_coe
- \- *lemma* units.unit_of_nearby_coe



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
Added src/data/fintype/list.lean
- \+ *def* multiset.lists
- \+ *lemma* multiset.lists_coe
- \+ *lemma* multiset.mem_lists_iff

Modified src/data/list/cycle.lean
- \+ *def* cycle.decidable_nontrivial_coe
- \+ *lemma* cycle.nodup.nontrivial_iff
- \+ *lemma* cycle.nontrivial_coe_nodup_iff



## [2021-07-07 13:35:19](https://github.com/leanprover-community/mathlib/commit/5796783)
chore(category_theory): homogenise usage of notation for terminal objects ([#8106](https://github.com/leanprover-community/mathlib/pull/8106))
I went with the option that is used more frequently, but I'm also happy to switch to the space-less option if people prefer it.
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean
- \+/\- *def* category_theory.exp_terminal_iso_self
- \+/\- *def* category_theory.internalize_hom

Modified src/category_theory/limits/shapes/terminal.lean




## [2021-07-07 12:02:07](https://github.com/leanprover-community/mathlib/commit/bb5ab1e)
chore(measure_theory/measure_space): add missing `finite_measure` instances ([#8214](https://github.com/leanprover-community/mathlib/pull/8214))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *theorem* measure_theory.measure.coe_nnreal_smul



## [2021-07-07 12:02:05](https://github.com/leanprover-community/mathlib/commit/41ec92e)
feat(algebra/lie/from_cartan_matrix): construction of a Lie algebra from a Cartan matrix ([#8206](https://github.com/leanprover-community/mathlib/pull/8206))
#### Estimated changes
Modified docs/references.bib


Added src/algebra/lie/from_cartan_matrix.lean
- \+ *def* cartan_matrix.relations.EF
- \+ *def* cartan_matrix.relations.HE
- \+ *def* cartan_matrix.relations.HF
- \+ *def* cartan_matrix.relations.HH
- \+ *def* cartan_matrix.relations.ad_E
- \+ *def* cartan_matrix.relations.ad_F
- \+ *def* cartan_matrix.relations.to_ideal
- \+ *def* cartan_matrix.relations.to_set
- \+ *def* matrix.to_lie_algebra



## [2021-07-07 12:02:02](https://github.com/leanprover-community/mathlib/commit/126a7b6)
feat(data/multiset/basic): add_eq_union_iff_disjoint ([#8173](https://github.com/leanprover-community/mathlib/pull/8173))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.add_eq_union_iff_disjoint

Modified src/data/nat/basic.lean
- \+ *lemma* nat.add_eq_max_iff
- \+ *lemma* nat.add_eq_min_iff
- \+ *lemma* nat.max_eq_zero_iff
- \+ *lemma* nat.min_eq_zero_iff



## [2021-07-07 10:24:57](https://github.com/leanprover-community/mathlib/commit/29beb1f)
feat(analysis/normed_space/int): norms of (units of) integers ([#8136](https://github.com/leanprover-community/mathlib/pull/8136))
From LTE
#### Estimated changes
Added src/analysis/normed_space/int.lean
- \+ *lemma* int.nnnorm_coe_nat
- \+ *lemma* int.nnnorm_coe_units
- \+ *lemma* int.norm_coe_nat
- \+ *lemma* int.norm_coe_units
- \+ *lemma* int.to_nat_add_to_nat_neg_eq_nnnorm
- \+ *lemma* int.to_nat_add_to_nat_neg_eq_norm

Modified src/data/fintype/basic.lean
- \+ *lemma* units_int.univ

Modified src/data/int/basic.lean
- \+ *lemma* int.to_nat_add_to_nat_neg_eq_nat_abs
- \+ *lemma* int.to_nat_sub_to_nat_neg



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
- \+/\- *def* abs
- \+/\- *lemma* abs_eq_abs
- \+ *lemma* div_le''
- \+ *lemma* div_le_div''
- \+ *lemma* div_le_div_flip
- \+ *lemma* div_le_div_iff'
- \+ *lemma* div_le_div_iff_left
- \+ *lemma* div_le_div_iff_right
- \+ *lemma* div_le_div_left'
- \+ *lemma* div_le_div_right'
- \+ *lemma* div_le_iff_le_mul'
- \+ *lemma* div_le_iff_le_mul
- \+ *lemma* div_le_inv_mul_iff
- \+ *lemma* div_le_one'
- \+ *lemma* div_lt''
- \+ *lemma* div_lt_div''
- \+ *lemma* div_lt_div_iff'
- \+ *lemma* div_lt_div_iff_left
- \+ *lemma* div_lt_div_iff_right
- \+ *lemma* div_lt_div_left'
- \+ *lemma* div_lt_div_right'
- \+ *lemma* div_lt_iff_lt_mul'
- \+ *lemma* div_lt_iff_lt_mul
- \+ *lemma* div_lt_one'
- \+/\- *lemma* eq_or_eq_neg_of_abs_eq
- \+/\- *def* function.injective.ordered_comm_group
- \- *lemma* inv_inv_of_one_lt
- \+ *lemma* inv_le_div_iff_le_mul'
- \+ *lemma* inv_le_div_iff_le_mul
- \+/\- *lemma* inv_le_inv'
- \- *lemma* inv_le_one'
- \+/\- *lemma* inv_le_one_of_one_le
- \- *lemma* inv_le_self
- \+ *lemma* inv_lt_div_iff_lt_mul'
- \+ *lemma* inv_lt_div_iff_lt_mul
- \+/\- *lemma* inv_lt_inv'
- \- *lemma* inv_lt_one'
- \- *lemma* inv_lt_one_iff_one_lt
- \+ *theorem* inv_lt_one_of_one_lt
- \- *lemma* inv_lt_self
- \- *lemma* inv_mul_le_left_of_le_mul
- \- *lemma* inv_mul_le_of_le_mul
- \+ *lemma* inv_mul_le_one_iff
- \- *lemma* inv_mul_le_right_of_le_mul
- \+ *lemma* inv_mul_lt_iff_lt_mul'
- \- *lemma* inv_mul_lt_iff_lt_mul_right
- \- *lemma* inv_mul_lt_left_of_lt_mul
- \- *lemma* inv_mul_lt_of_lt_mul
- \+ *lemma* inv_mul_lt_one_iff
- \+ *lemma* inv_mul_lt_one_iff_lt
- \- *lemma* inv_mul_lt_right_of_lt_mul
- \- *lemma* inv_of_one_lt_inv
- \+ *lemma* le_div''
- \+ *lemma* le_div_iff_mul_le'
- \+ *lemma* le_div_iff_mul_le
- \+ *lemma* le_iff_forall_one_lt_le_mul
- \+ *lemma* le_iff_forall_one_lt_lt_mul
- \- *lemma* le_iff_forall_pos_le_add
- \- *lemma* le_iff_forall_pos_lt_add
- \- *lemma* le_inv_iff_mul_le_one'
- \- *lemma* le_inv_iff_mul_le_one
- \+ *lemma* le_inv_iff_mul_le_one_left
- \+ *lemma* le_inv_iff_mul_le_one_right
- \+ *lemma* le_inv_mul_iff_le
- \- *lemma* le_inv_mul_of_mul_le
- \- *lemma* le_inv_of_le_inv
- \+ *lemma* le_mul_inv_iff_le
- \+ *lemma* le_mul_inv_iff_mul_le
- \- *lemma* le_mul_of_inv_mul_le
- \- *lemma* le_mul_of_inv_mul_le_left
- \- *lemma* le_mul_of_inv_mul_le_right
- \+ *lemma* le_of_forall_one_lt_le_mul
- \+ *lemma* le_of_forall_one_lt_lt_mul
- \- *lemma* le_of_forall_pos_le_add
- \- *lemma* le_of_forall_pos_lt_add
- \- *lemma* le_of_inv_le_inv
- \- *lemma* le_one_of_one_le_inv
- \- *theorem* le_sub
- \- *lemma* le_sub_iff_add_le'
- \- *lemma* le_sub_iff_add_le
- \+ *lemma* left.inv_le_one_iff
- \+ *lemma* left.inv_le_self
- \+ *lemma* left.inv_lt_one_iff
- \+ *lemma* left.inv_lt_self
- \+ *lemma* left.one_le_inv_iff
- \+ *lemma* left.one_lt_inv_iff
- \+ *lemma* left.self_le_inv
- \+ *lemma* left.self_lt_inv
- \+ *lemma* lt_div''
- \+ *lemma* lt_div_iff_mul_lt'
- \+ *lemma* lt_div_iff_mul_lt
- \+ *lemma* lt_inv_mul_iff_lt
- \- *lemma* lt_inv_mul_of_mul_lt
- \+ *lemma* lt_mul_inv_iff_lt
- \+ *lemma* lt_mul_inv_iff_mul_lt
- \- *lemma* lt_mul_of_inv_mul_lt
- \- *lemma* lt_mul_of_inv_mul_lt_left
- \- *lemma* lt_mul_of_inv_mul_lt_right
- \- *lemma* lt_of_inv_lt_inv
- \- *theorem* lt_sub
- \- *lemma* lt_sub_iff_add_lt'
- \- *lemma* lt_sub_iff_add_lt
- \- *lemma* max_one_div_eq_self'
- \+ *lemma* max_one_div_max_inv_one_eq_self
- \- *lemma* max_zero_sub_max_neg_zero_eq_self
- \+/\- *lemma* mul_inv_le_iff_le_mul
- \+ *lemma* mul_inv_le_inv_mul_iff
- \+ *lemma* mul_inv_le_one_iff
- \+ *lemma* mul_inv_le_one_iff_le
- \+ *lemma* mul_inv_lt_iff_le_mul'
- \+ *lemma* mul_inv_lt_iff_lt_mul
- \+ *lemma* mul_inv_lt_inv_mul_iff
- \+ *lemma* mul_inv_lt_mul_inv_iff'
- \+ *lemma* mul_inv_lt_one_iff
- \- *lemma* mul_le_of_le_inv_mul
- \- *lemma* mul_lt_of_lt_inv_mul
- \- *lemma* neg_le_sub_iff_le_add'
- \- *lemma* neg_le_sub_iff_le_add
- \- *lemma* neg_lt_sub_iff_lt_add'
- \- *lemma* neg_lt_sub_iff_lt_add
- \+ *lemma* one_le_div'
- \- *lemma* one_le_inv'
- \+/\- *lemma* one_le_inv_of_le_one
- \- *lemma* one_le_of_inv_le_one
- \+ *lemma* one_lt_div'
- \- *lemma* one_lt_inv'
- \- *lemma* one_lt_inv_of_inv
- \- *lemma* one_lt_of_inv_inv
- \+ *lemma* right.inv_le_one_iff
- \+ *lemma* right.inv_le_self
- \+ *lemma* right.inv_lt_one_iff
- \+ *lemma* right.inv_lt_self
- \+ *lemma* right.one_le_inv_iff
- \+ *lemma* right.one_lt_inv_iff
- \+ *lemma* right.self_le_inv
- \+ *lemma* right.self_lt_inv
- \- *lemma* self_le_inv
- \- *lemma* sub_le
- \- *lemma* sub_le_iff_le_add'
- \- *lemma* sub_le_iff_le_add
- \- *lemma* sub_le_sub
- \- *lemma* sub_le_sub_flip
- \- *lemma* sub_le_sub_iff
- \- *lemma* sub_le_sub_iff_left
- \- *lemma* sub_le_sub_iff_right
- \- *lemma* sub_le_sub_left
- \- *lemma* sub_le_sub_right
- \- *lemma* sub_lt
- \- *lemma* sub_lt_iff_lt_add'
- \- *lemma* sub_lt_iff_lt_add
- \- *lemma* sub_lt_sub
- \- *lemma* sub_lt_sub_iff_left
- \- *lemma* sub_lt_sub_iff_right
- \- *lemma* sub_lt_sub_left
- \- *lemma* sub_lt_sub_right
- \- *lemma* sub_lt_zero
- \- *lemma* sub_nonneg
- \- *lemma* sub_nonpos
- \- *lemma* sub_pos

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
- \+/\- *def* category_theory.comonad.coalgebra.iso_mk
- \+/\- *def* category_theory.monad.algebra.iso_mk

Modified src/category_theory/monad/limits.lean
- \+/\- *def* category_theory.monad.forget_creates_limits.new_cone
- \+/\- *def* category_theory.monad.forget_creates_limits.γ



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
Added src/category_theory/closed/ideal.lean
- \+ *lemma* category_theory.bijection_natural
- \+ *lemma* category_theory.bijection_symm_apply_id
- \+ *def* category_theory.cartesian_closed_of_reflective
- \+ *lemma* category_theory.exponential_ideal.mk'
- \+ *lemma* category_theory.exponential_ideal.mk_of_iso
- \+ *def* category_theory.exponential_ideal_reflective
- \+ *lemma* category_theory.prod_comparison_iso
- \+ *lemma* category_theory.reflective_products



## [2021-07-06 11:32:50](https://github.com/leanprover-community/mathlib/commit/98e8408)
feat(geometry/manifold/algebra): `left_invariant_derivation` ([#8108](https://github.com/leanprover-community/mathlib/pull/8108))
In this PR we prove that left-invariant derivations are a Lie algebra.
#### Estimated changes
Added src/geometry/manifold/algebra/left_invariant_derivation.lean
- \+ *lemma* left_invariant_derivation.coe_add
- \+ *lemma* left_invariant_derivation.coe_derivation
- \+ *lemma* left_invariant_derivation.coe_derivation_injective
- \+ *def* left_invariant_derivation.coe_fn_add_monoid_hom
- \+ *lemma* left_invariant_derivation.coe_injective
- \+ *lemma* left_invariant_derivation.coe_neg
- \+ *lemma* left_invariant_derivation.coe_smul
- \+ *lemma* left_invariant_derivation.coe_sub
- \+ *lemma* left_invariant_derivation.coe_to_linear_map
- \+ *lemma* left_invariant_derivation.coe_zero
- \+ *lemma* left_invariant_derivation.commutator_apply
- \+ *lemma* left_invariant_derivation.commutator_coe_derivation
- \+ *lemma* left_invariant_derivation.comp_L
- \+ *def* left_invariant_derivation.eval_at
- \+ *lemma* left_invariant_derivation.eval_at_apply
- \+ *lemma* left_invariant_derivation.eval_at_coe
- \+ *lemma* left_invariant_derivation.eval_at_mul
- \+ *theorem* left_invariant_derivation.ext
- \+ *lemma* left_invariant_derivation.left_invariant'
- \+ *lemma* left_invariant_derivation.left_invariant
- \+ *lemma* left_invariant_derivation.leibniz
- \+ *lemma* left_invariant_derivation.lift_add
- \+ *lemma* left_invariant_derivation.lift_smul
- \+ *lemma* left_invariant_derivation.lift_zero
- \+ *lemma* left_invariant_derivation.map_add
- \+ *lemma* left_invariant_derivation.map_neg
- \+ *lemma* left_invariant_derivation.map_smul
- \+ *lemma* left_invariant_derivation.map_sub
- \+ *lemma* left_invariant_derivation.map_zero
- \+ *lemma* left_invariant_derivation.to_derivation_eq_coe
- \+ *lemma* left_invariant_derivation.to_fun_eq_coe

Modified src/geometry/manifold/algebra/monoid.lean
- \+ *lemma* smooth_left_mul_one
- \+ *lemma* smooth_right_mul_one

Modified src/geometry/manifold/derivation_bundle.lean
- \+/\- *lemma* apply_fdifferential
- \+ *lemma* apply_hfdifferential
- \- *def* fdifferential_map
- \+ *def* hfdifferential

Modified src/ring_theory/derivation.lean
- \+ *lemma* derivation.congr_fun



## [2021-07-06 10:58:03](https://github.com/leanprover-community/mathlib/commit/23d22e4)
feat(category_theory/abelian/ext): Defines Ext functors. ([#8186](https://github.com/leanprover-community/mathlib/pull/8186))
See my comment from [#7525](https://github.com/leanprover-community/mathlib/pull/7525)
#### Estimated changes
Added src/category_theory/abelian/ext.lean
- \+ *def* Ext
- \+ *def* Ext_succ_of_projective



## [2021-07-06 08:21:53](https://github.com/leanprover-community/mathlib/commit/2f72023)
chore(measure_theory/decomposition): change statement to use the `finite_measure` instance ([#8207](https://github.com/leanprover-community/mathlib/pull/8207))
#### Estimated changes
Modified src/measure_theory/decomposition.lean
- \+/\- *lemma* measure_theory.hahn_decomposition



## [2021-07-06 05:05:33](https://github.com/leanprover-community/mathlib/commit/6365c6c)
feat(algebra/invertible): construction from is_unit ([#8205](https://github.com/leanprover-community/mathlib/pull/8205))
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *lemma* is_unit.nonempty_invertible
- \+ *lemma* nonempty_invertible_iff_is_unit



## [2021-07-06 02:10:44](https://github.com/leanprover-community/mathlib/commit/27841bb)
chore(scripts): update nolints.txt ([#8208](https://github.com/leanprover-community/mathlib/pull/8208))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-07-05 17:24:46](https://github.com/leanprover-community/mathlib/commit/77e1e3b)
feat(linear_algebra/nonsingular_inverse): add lemmas about `invertible` ([#8201](https://github.com/leanprover-community/mathlib/pull/8201))
#### Estimated changes
Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *def* matrix.det_invertible_of_invertible
- \+ *def* matrix.det_invertible_of_left_inverse
- \+ *def* matrix.det_invertible_of_right_inverse
- \+ *def* matrix.invertible_of_det_invertible
- \+ *def* matrix.unit_of_det_invertible
- \+ *lemma* matrix.unit_of_det_invertible_eq_nonsing_inv_unit



## [2021-07-05 17:24:45](https://github.com/leanprover-community/mathlib/commit/9d99833)
feat(category_theory/linear/yoneda): A linear version of Yoneda. ([#8199](https://github.com/leanprover-community/mathlib/pull/8199))
#### Estimated changes
Added src/category_theory/linear/yoneda.lean
- \+ *def* category_theory.linear_yoneda



## [2021-07-05 17:24:44](https://github.com/leanprover-community/mathlib/commit/b6bf7a3)
feat(measure_theory/lp_space): define the Lp function corresponding to the indicator of a set ([#8193](https://github.com/leanprover-community/mathlib/pull/8193))
I also moved some measurability lemmas from the integrable_on file to measure_space. I needed them and lp_space is before integrable_on in the import graph.
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* set.comp_mul_indicator_const

Modified src/measure_theory/integrable_on.lean
- \- *lemma* ae_measurable.indicator
- \- *lemma* ae_measurable.restrict
- \- *lemma* ae_measurable_indicator_iff
- \- *lemma* indicator_ae_eq_restrict
- \- *lemma* indicator_ae_eq_restrict_compl
- \+ *lemma* measure_theory.integrable_indicator_const_Lp
- \- *lemma* piecewise_ae_eq_restrict
- \- *lemma* piecewise_ae_eq_restrict_compl

Modified src/measure_theory/lp_space.lean
- \+ *def* measure_theory.indicator_const_Lp
- \+ *lemma* measure_theory.indicator_const_Lp_coe_fn
- \+ *lemma* measure_theory.indicator_const_Lp_coe_fn_mem
- \+ *lemma* measure_theory.indicator_const_Lp_coe_fn_nmem
- \+ *lemma* measure_theory.indicator_const_Lp_disjoint_union
- \+ *lemma* measure_theory.mem_ℒp_indicator_const
- \+ *lemma* measure_theory.norm_indicator_const_Lp'
- \+ *lemma* measure_theory.norm_indicator_const_Lp
- \+ *lemma* measure_theory.norm_indicator_const_Lp_top
- \+ *lemma* measure_theory.snorm_ess_sup_indicator_const_eq
- \+ *lemma* measure_theory.snorm_ess_sup_indicator_const_le
- \+ *lemma* measure_theory.snorm_ess_sup_indicator_le
- \+ *lemma* measure_theory.snorm_indicator_const'
- \+ *lemma* measure_theory.snorm_indicator_const

Modified src/measure_theory/measure_space.lean
- \+ *lemma* ae_measurable.indicator
- \+ *lemma* ae_measurable.restrict
- \+ *lemma* ae_measurable_indicator_iff
- \+ *lemma* indicator_ae_eq_restrict
- \+ *lemma* indicator_ae_eq_restrict_compl
- \+ *lemma* piecewise_ae_eq_restrict
- \+ *lemma* piecewise_ae_eq_restrict_compl



## [2021-07-05 17:24:43](https://github.com/leanprover-community/mathlib/commit/7eab080)
feat(topology/instances/ennreal): add tsum lemmas for ennreal.to_real ([#8184](https://github.com/leanprover-community/mathlib/pull/8184))
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.tsum_coe_eq_top_iff_not_summable_coe
- \+ *lemma* ennreal.tsum_coe_ne_top_iff_summable_coe
- \+ *lemma* ennreal.tsum_to_real_eq



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
- \+/\- *lemma* finset.prod_const_one
- \- *lemma* finset.sum_const_zero
- \- *lemma* finset.sum_multiset_count

Modified src/algebra/big_operators/ring.lean
- \- *lemma* finset.sum_powerset

Modified src/algebra/group/to_additive.lean


Modified src/algebra/group_power/basic.lean
- \- *theorem* add_monoid_hom.map_nsmul
- \- *theorem* add_nsmul
- \- *theorem* bit0_nsmul'
- \- *theorem* bit0_nsmul
- \- *theorem* bit1_nsmul'
- \- *theorem* bit1_nsmul
- \+/\- *theorem* commute.pow_left
- \+/\- *theorem* commute.pow_pow
- \+/\- *theorem* commute.pow_pow_self
- \+/\- *theorem* commute.pow_right
- \+/\- *theorem* commute.pow_self
- \+/\- *theorem* commute.self_pow
- \+ *theorem* div_gpow
- \+/\- *theorem* gpow_coe_nat
- \+/\- *lemma* gpow_eq_pow
- \+/\- *theorem* gpow_neg
- \+/\- *theorem* gpow_neg_succ_of_nat
- \+/\- *theorem* gpow_one
- \+/\- *theorem* gpow_zero
- \- *theorem* gsmul_add
- \- *theorem* gsmul_coe_nat
- \- *lemma* gsmul_eq_smul
- \- *theorem* gsmul_neg
- \- *theorem* gsmul_neg_succ_of_nat
- \- *theorem* gsmul_of_nat
- \- *theorem* gsmul_sub
- \- *theorem* gsmul_zero
- \+/\- *theorem* inv_pow
- \- *theorem* is_add_monoid_hom.map_nsmul
- \+/\- *theorem* monoid_hom.map_pow
- \- *theorem* mul_nsmul'
- \- *theorem* mul_nsmul
- \- *theorem* neg_gsmul
- \- *theorem* neg_nsmul
- \- *theorem* neg_one_gsmul
- \+/\- *lemma* npow_eq_pow
- \- *theorem* nsmul_add
- \- *theorem* nsmul_add_comm'
- \- *theorem* nsmul_add_comm
- \- *theorem* nsmul_add_sub_nsmul
- \- *lemma* nsmul_eq_smul
- \- *theorem* nsmul_neg_comm
- \- *theorem* nsmul_sub
- \- *theorem* nsmul_zero
- \+/\- *theorem* one_gpow
- \- *theorem* one_gsmul
- \- *theorem* one_nsmul
- \+/\- *theorem* one_pow
- \+/\- *theorem* pow_one
- \+/\- *theorem* pow_zero
- \+/\- *lemma* semiconj_by.pow_right
- \- *theorem* sub_nsmul_nsmul_add
- \- *theorem* succ_nsmul'
- \- *theorem* succ_nsmul
- \- *theorem* two_nsmul
- \- *theorem* zero_gsmul
- \- *theorem* zero_nsmul

Modified src/analysis/calculus/extend_deriv.lean


Modified src/data/list/basic.lean
- \- *theorem* list.sum_repeat

Modified src/data/multiset/basic.lean
- \+/\- *theorem* multiset.prod_repeat
- \- *lemma* multiset.sum_map_sum_map
- \- *lemma* multiset.sum_map_zero
- \- *theorem* multiset.sum_repeat

Modified src/group_theory/group_action/defs.lean


Modified src/meta/expr.lean


Modified src/tactic/transform_decl.lean


Added test/to_additive.lean
- \+ *def* foo0
- \+ *def* foo1
- \+ *def* foo2
- \+ *def* foo3
- \+ *lemma* foo4_test
- \+ *def* foo5
- \+ *def* foo6
- \+ *def* foo7
- \+ *def* {a



## [2021-07-05 14:57:50](https://github.com/leanprover-community/mathlib/commit/f2edc5a)
feat(category_theory/preadditive/opposite): Adds some instances and lemmas ([#8202](https://github.com/leanprover-community/mathlib/pull/8202))
This PR adds some instances and lemmas related to opposites and additivity of functors.
#### Estimated changes
Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.nat_trans.left_op_comp
- \+ *lemma* category_theory.nat_trans.left_op_id
- \+ *lemma* category_theory.nat_trans.right_op_comp
- \+ *lemma* category_theory.nat_trans.right_op_id

Modified src/category_theory/preadditive/opposite.lean
- \+ *lemma* category_theory.op_add
- \+ *lemma* category_theory.op_zero



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
- \+ *lemma* is_fraction_ring.char_p_of_is_fraction_ring
- \+ *lemma* is_fraction_ring.char_zero_of_is_fraction_ring

Modified src/algebraic_geometry/structure_sheaf.lean
- \+/\- *def* algebraic_geometry.structure_sheaf.to_basic_open
- \+/\- *lemma* algebraic_geometry.structure_sheaf.to_basic_open_to_map
- \+/\- *def* algebraic_geometry.structure_sheaf.to_open
- \+ *lemma* algebraic_geometry.structure_sheaf.to_open_apply

Modified src/field_theory/minpoly.lean
- \+/\- *lemma* minpoly.gcd_domain_dvd
- \+/\- *lemma* minpoly.gcd_domain_eq_field_fractions
- \- *lemma* minpoly.integer_dvd
- \- *lemma* minpoly.over_int_eq_over_rat

Modified src/ring_theory/dedekind_domain.lean
- \+/\- *lemma* coe_inv_of_nonzero
- \+/\- *lemma* inv_nonzero
- \+/\- *lemma* inv_zero'
- \+/\- *lemma* invertible_iff_generator_nonzero
- \+/\- *lemma* invertible_of_principal
- \+/\- *lemma* is_dedekind_domain_iff
- \+/\- *lemma* is_dedekind_domain_inv_iff
- \+/\- *lemma* is_principal_inv
- \+/\- *lemma* map_inv
- \+/\- *lemma* mul_generator_self_inv
- \+/\- *theorem* mul_inv_cancel_iff
- \+/\- *theorem* right_inverse_eq
- \+/\- *lemma* span_singleton_inv

Modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* ring.fractional_ideal.add_le_add_left
- \+/\- *lemma* ring.fractional_ideal.bot_eq_zero
- \+/\- *lemma* ring.fractional_ideal.canonical_equiv_flip
- \+/\- *lemma* ring.fractional_ideal.canonical_equiv_span_singleton
- \+/\- *lemma* ring.fractional_ideal.canonical_equiv_symm
- \+/\- *lemma* ring.fractional_ideal.coe_add
- \+/\- *lemma* ring.fractional_ideal.coe_div
- \+/\- *lemma* ring.fractional_ideal.coe_fun_map_equiv
- \+/\- *lemma* ring.fractional_ideal.coe_ideal_le_one
- \+ *lemma* ring.fractional_ideal.coe_injective
- \+/\- *lemma* ring.fractional_ideal.coe_le_coe
- \+/\- *lemma* ring.fractional_ideal.coe_map
- \+/\- *lemma* ring.fractional_ideal.coe_mem_one
- \+/\- *lemma* ring.fractional_ideal.coe_mk
- \+/\- *lemma* ring.fractional_ideal.coe_mul
- \+/\- *lemma* ring.fractional_ideal.coe_span_singleton
- \+/\- *lemma* ring.fractional_ideal.coe_to_fractional_ideal_bot
- \+/\- *lemma* ring.fractional_ideal.coe_to_submodule_eq_bot
- \+/\- *lemma* ring.fractional_ideal.coe_to_submodule_ne_bot
- \+/\- *lemma* ring.fractional_ideal.coe_zero
- \+/\- *lemma* ring.fractional_ideal.div_nonzero
- \+/\- *lemma* ring.fractional_ideal.div_one
- \+/\- *lemma* ring.fractional_ideal.div_span_singleton
- \+/\- *lemma* ring.fractional_ideal.div_zero
- \+/\- *theorem* ring.fractional_ideal.eq_one_div_of_mul_eq_one
- \+/\- *lemma* ring.fractional_ideal.eq_span_singleton_of_principal
- \+/\- *lemma* ring.fractional_ideal.eq_zero_iff
- \+/\- *lemma* ring.fractional_ideal.exists_eq_span_singleton_mul
- \+/\- *lemma* ring.fractional_ideal.ext
- \+/\- *lemma* ring.fractional_ideal.ext_iff
- \+/\- *lemma* ring.fractional_ideal.fractional_div_of_nonzero
- \+/\- *lemma* ring.fractional_ideal.fractional_inf
- \+/\- *lemma* ring.fractional_ideal.fractional_map
- \+/\- *lemma* ring.fractional_ideal.fractional_mul
- \+/\- *lemma* ring.fractional_ideal.fractional_of_subset_one
- \+/\- *lemma* ring.fractional_ideal.fractional_sup
- \+/\- *lemma* ring.fractional_ideal.is_fractional_of_fg
- \+/\- *lemma* ring.fractional_ideal.is_fractional_of_le
- \+/\- *lemma* ring.fractional_ideal.is_fractional_span_iff
- \+/\- *lemma* ring.fractional_ideal.is_fractional_span_singleton
- \+/\- *theorem* ring.fractional_ideal.is_noetherian
- \+/\- *lemma* ring.fractional_ideal.is_noetherian_coe_to_fractional_ideal
- \+/\- *lemma* ring.fractional_ideal.is_noetherian_iff
- \+/\- *lemma* ring.fractional_ideal.is_noetherian_span_singleton_inv_to_map_mul
- \+/\- *lemma* ring.fractional_ideal.is_noetherian_zero
- \+/\- *lemma* ring.fractional_ideal.is_principal_iff
- \+/\- *lemma* ring.fractional_ideal.le_div_iff_mul_le
- \+/\- *lemma* ring.fractional_ideal.le_div_iff_of_nonzero
- \+/\- *lemma* ring.fractional_ideal.le_iff_mem
- \+/\- *lemma* ring.fractional_ideal.le_one_iff_exists_coe_ideal
- \+/\- *lemma* ring.fractional_ideal.le_self_mul_one_div
- \+/\- *lemma* ring.fractional_ideal.le_self_mul_self
- \+/\- *lemma* ring.fractional_ideal.le_zero_iff
- \+/\- *def* ring.fractional_ideal.map
- \+/\- *lemma* ring.fractional_ideal.map_comp
- \+/\- *lemma* ring.fractional_ideal.map_div
- \+/\- *def* ring.fractional_ideal.map_equiv
- \+/\- *lemma* ring.fractional_ideal.map_equiv_apply
- \+/\- *lemma* ring.fractional_ideal.map_equiv_symm
- \+/\- *lemma* ring.fractional_ideal.map_map_symm
- \+/\- *lemma* ring.fractional_ideal.map_one_div
- \+/\- *lemma* ring.fractional_ideal.map_symm_map
- \+/\- *lemma* ring.fractional_ideal.mem_canonical_equiv_apply
- \+/\- *lemma* ring.fractional_ideal.mem_coe_ideal
- \+/\- *lemma* ring.fractional_ideal.mem_div_iff_of_nonzero
- \+/\- *lemma* ring.fractional_ideal.mem_map
- \+/\- *lemma* ring.fractional_ideal.mem_one_iff
- \+/\- *lemma* ring.fractional_ideal.mem_singleton_mul
- \+/\- *lemma* ring.fractional_ideal.mem_span_singleton
- \+/\- *lemma* ring.fractional_ideal.mem_span_singleton_self
- \+/\- *lemma* ring.fractional_ideal.mem_zero_iff
- \+/\- *def* ring.fractional_ideal.mul
- \+/\- *theorem* ring.fractional_ideal.mul_div_self_cancel_iff
- \+/\- *lemma* ring.fractional_ideal.mul_eq_mul
- \+/\- *lemma* ring.fractional_ideal.mul_le
- \+/\- *lemma* ring.fractional_ideal.mul_le_mul_left
- \+/\- *lemma* ring.fractional_ideal.mul_left_mono
- \+/\- *lemma* ring.fractional_ideal.mul_mem_mul
- \+/\- *lemma* ring.fractional_ideal.mul_one_div_le_one
- \+/\- *lemma* ring.fractional_ideal.mul_right_mono
- \+/\- *lemma* ring.fractional_ideal.mul_self_le_self
- \+/\- *lemma* ring.fractional_ideal.ne_zero_of_mul_eq_one
- \+/\- *lemma* ring.fractional_ideal.one_div_span_singleton
- \+/\- *lemma* ring.fractional_ideal.one_mem_one
- \+/\- *def* ring.fractional_ideal.span_singleton
- \+/\- *lemma* ring.fractional_ideal.span_singleton_eq_zero_iff
- \+/\- *lemma* ring.fractional_ideal.span_singleton_mul_span_singleton
- \+/\- *lemma* ring.fractional_ideal.span_singleton_ne_zero_iff
- \+/\- *lemma* ring.fractional_ideal.span_singleton_one
- \+/\- *lemma* ring.fractional_ideal.span_singleton_zero
- \+/\- *lemma* ring.fractional_ideal.sup_eq_add
- \+/\- *lemma* ring.fractional_ideal.val_eq_coe
- \+/\- *lemma* ring.fractional_ideal.zero_le
- \+/\- *def* ring.is_fractional

Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/jacobson.lean
- \+/\- *lemma* ideal.is_jacobson_localization
- \+ *lemma* ideal.polynomial.is_integral_is_localization_polynomial_quotient
- \- *lemma* ideal.polynomial.is_integral_localization_map_polynomial_quotient

Modified src/ring_theory/laurent_series.lean
- \+ *lemma* laurent_series.coe_algebra_map
- \- *def* laurent_series.of_power_series_localization

Modified src/ring_theory/localization.lean
- \- *lemma* fraction_map.comap_is_algebraic_iff
- \- *lemma* fraction_map.eq_zero_of_num_eq_zero
- \- *lemma* fraction_map.exists_reduced_fraction
- \- *def* fraction_map.int.fraction_map
- \- *lemma* fraction_map.integer_normalization_eq_zero_iff
- \- *lemma* fraction_map.is_integer_of_is_unit_denom
- \- *lemma* fraction_map.is_unit_denom_of_num_eq_zero
- \- *lemma* fraction_map.is_unit_map_of_injective
- \- *lemma* fraction_map.lift_mk'
- \- *lemma* fraction_map.mk'_eq_div
- \- *lemma* fraction_map.mk'_num_denom
- \- *lemma* fraction_map.num_denom_reduced
- \- *lemma* fraction_map.num_mul_denom_eq_num_iff_eq'
- \- *lemma* fraction_map.num_mul_denom_eq_num_iff_eq
- \- *lemma* fraction_map.num_mul_denom_eq_num_mul_denom_iff_eq
- \- *def* fraction_map.to_integral_domain
- \- *lemma* fraction_map.to_map_eq_zero_iff
- \- *def* fraction_map
- \- *def* fraction_ring.of
- \- *def* integral_closure.fraction_map_of_algebraic
- \- *def* integral_closure.fraction_map_of_finite_extension
- \+ *lemma* integral_closure.is_fraction_ring_of_algebraic
- \+ *lemma* integral_closure.is_fraction_ring_of_finite_extension
- \+ *lemma* is_fraction_ring.comap_is_algebraic_iff
- \+ *lemma* is_fraction_ring.eq_zero_of_num_eq_zero
- \+ *lemma* is_fraction_ring.exists_reduced_fraction
- \+ *lemma* is_fraction_ring.integer_normalization_eq_zero_iff
- \+ *lemma* is_fraction_ring.is_integer_of_is_unit_denom
- \+ *lemma* is_fraction_ring.is_unit_denom_of_num_eq_zero
- \+ *lemma* is_fraction_ring.is_unit_map_of_injective
- \+ *lemma* is_fraction_ring.lift_mk'
- \+ *lemma* is_fraction_ring.mk'_eq_div
- \+ *lemma* is_fraction_ring.mk'_mk_eq_div
- \+ *lemma* is_fraction_ring.mk'_num_denom
- \+ *lemma* is_fraction_ring.num_denom_reduced
- \+ *lemma* is_fraction_ring.num_mul_denom_eq_num_iff_eq'
- \+ *lemma* is_fraction_ring.num_mul_denom_eq_num_iff_eq
- \+ *lemma* is_fraction_ring.num_mul_denom_eq_num_mul_denom_iff_eq
- \+ *def* is_fraction_ring.to_integral_domain
- \+ *lemma* is_fraction_ring.to_map_eq_zero_iff
- \+ *lemma* is_localization.alg_equiv_mk'
- \+ *lemma* is_localization.alg_equiv_symm_mk'
- \+ *lemma* is_localization.at_prime.is_unit_mk'_iff
- \+ *lemma* is_localization.at_prime.is_unit_to_map_iff
- \+ *theorem* is_localization.at_prime.local_ring
- \+ *lemma* is_localization.at_prime.mk'_mem_maximal_iff
- \+ *lemma* is_localization.at_prime.to_map_mem_maximal_iff
- \+ *lemma* is_localization.away.away_map.lift_comp
- \+ *lemma* is_localization.away.away_map.lift_eq
- \+ *def* is_localization.coe_submodule
- \+ *lemma* is_localization.coeff_integer_normalization_mem_support
- \+ *lemma* is_localization.coeff_integer_normalization_of_not_mem_support
- \+ *theorem* is_localization.comap_map_of_is_prime_disjoint
- \+ *lemma* is_localization.epic_of_localization_map
- \+ *lemma* is_localization.eq_iff_eq
- \+ *theorem* is_localization.eq_mk'_iff_mul_eq
- \+ *lemma* is_localization.eq_of_eq
- \+ *lemma* is_localization.eq_zero_of_fst_eq_zero
- \+ *lemma* is_localization.exist_integer_multiples_of_finset
- \+ *lemma* is_localization.exists_integer_multiple'
- \+ *lemma* is_localization.exists_integer_multiple
- \+ *lemma* is_localization.integer_normalization_aeval_eq_zero
- \+ *lemma* is_localization.integer_normalization_coeff
- \+ *lemma* is_localization.integer_normalization_eval₂_eq_zero
- \+ *lemma* is_localization.integer_normalization_map_to_map
- \+ *lemma* is_localization.integer_normalization_spec
- \+ *def* is_localization.integral_domain_localization
- \+ *def* is_localization.integral_domain_of_le_non_zero_divisors
- \+ *def* is_localization.is_integer
- \+ *lemma* is_localization.is_integer_add
- \+ *lemma* is_localization.is_integer_mul
- \+ *lemma* is_localization.is_integer_one
- \+ *lemma* is_localization.is_integer_smul
- \+ *lemma* is_localization.is_integer_zero
- \+ *lemma* is_localization.is_noetherian_ring
- \+ *lemma* is_localization.is_prime_iff_is_prime_disjoint
- \+ *lemma* is_localization.is_prime_of_is_prime_disjoint
- \+ *lemma* is_localization.is_unit_comp
- \+ *lemma* is_localization.lift_comp
- \+ *lemma* is_localization.lift_eq
- \+ *lemma* is_localization.lift_eq_iff
- \+ *lemma* is_localization.lift_id
- \+ *lemma* is_localization.lift_injective_iff
- \+ *lemma* is_localization.lift_mk'
- \+ *lemma* is_localization.lift_mk'_spec
- \+ *lemma* is_localization.lift_of_comp
- \+ *lemma* is_localization.lift_surjective_iff
- \+ *lemma* is_localization.lift_unique
- \+ *theorem* is_localization.map_comap
- \+ *lemma* is_localization.map_comp
- \+ *lemma* is_localization.map_comp_map
- \+ *lemma* is_localization.map_eq
- \+ *lemma* is_localization.map_id
- \+ *lemma* is_localization.map_injective_of_injective
- \+ *lemma* is_localization.map_left_cancel
- \+ *lemma* is_localization.map_map
- \+ *lemma* is_localization.map_mk'
- \+ *lemma* is_localization.map_right_cancel
- \+ *lemma* is_localization.map_smul
- \+ *lemma* is_localization.map_unique
- \+ *lemma* is_localization.mem_coe_submodule
- \+ *theorem* is_localization.mem_map_algebra_map_iff
- \+ *lemma* is_localization.mk'_add
- \+ *lemma* is_localization.mk'_eq_iff_eq
- \+ *theorem* is_localization.mk'_eq_iff_eq_mul
- \+ *lemma* is_localization.mk'_eq_iff_mk'_eq
- \+ *lemma* is_localization.mk'_eq_mul_mk'_one
- \+ *lemma* is_localization.mk'_eq_of_eq
- \+ *lemma* is_localization.mk'_mem_iff
- \+ *lemma* is_localization.mk'_mul
- \+ *lemma* is_localization.mk'_mul_cancel_left
- \+ *lemma* is_localization.mk'_mul_cancel_right
- \+ *lemma* is_localization.mk'_mul_mk'_eq_one'
- \+ *lemma* is_localization.mk'_mul_mk'_eq_one
- \+ *lemma* is_localization.mk'_one
- \+ *lemma* is_localization.mk'_sec
- \+ *lemma* is_localization.mk'_self''
- \+ *lemma* is_localization.mk'_self'
- \+ *lemma* is_localization.mk'_self
- \+ *lemma* is_localization.mk'_spec'
- \+ *lemma* is_localization.mk'_spec
- \+ *lemma* is_localization.mk'_surjective
- \+ *lemma* is_localization.mul_mk'_eq_mk'_of_mul
- \+ *def* is_localization.order_embedding
- \+ *def* is_localization.order_iso_of_prime
- \+ *lemma* is_localization.ring_equiv_of_ring_equiv_eq
- \+ *lemma* is_localization.ring_equiv_of_ring_equiv_eq_map
- \+ *lemma* is_localization.ring_equiv_of_ring_equiv_mk'
- \+ *lemma* is_localization.sec_spec'
- \+ *lemma* is_localization.sec_spec
- \+ *lemma* is_localization.surjective_quotient_map_of_maximal_of_localization
- \+ *def* is_localization.to_localization_map
- \+ *lemma* is_localization.to_localization_map_sec
- \+ *lemma* is_localization.to_localization_map_to_map
- \+ *lemma* is_localization.to_localization_map_to_map_apply
- \+ *lemma* is_localization.to_map_eq_zero_iff
- \+ *lemma* localization.alg_equiv_mk'
- \+ *lemma* localization.alg_equiv_mk
- \- *lemma* localization.alg_equiv_of_quotient_apply
- \- *lemma* localization.alg_equiv_of_quotient_symm_apply
- \+ *lemma* localization.alg_equiv_symm_mk'
- \+ *lemma* localization.alg_equiv_symm_mk
- \- *def* localization.at_prime
- \- *lemma* localization.away.mk_eq_mk'
- \- *def* localization.away.of
- \+ *lemma* localization.le_comap_prime_compl_iff
- \+/\- *lemma* localization.local_ring_hom_comp
- \+/\- *lemma* localization.local_ring_hom_mk'
- \+/\- *lemma* localization.local_ring_hom_to_map
- \+/\- *lemma* localization.local_ring_hom_unique
- \+/\- *lemma* localization.mk_eq_mk'
- \+/\- *lemma* localization.mk_eq_mk'_apply
- \+ *lemma* localization.mk_one_eq_algebra_map
- \- *lemma* localization.mk_one_eq_of
- \+ *lemma* localization.monoid_of_eq_algebra_map
- \- *lemma* localization.monoid_of_eq_of
- \- *def* localization.of
- \- *lemma* localization.ring_equiv_of_quotient_apply
- \- *lemma* localization.ring_equiv_of_quotient_mk'
- \- *lemma* localization.ring_equiv_of_quotient_mk
- \- *lemma* localization.ring_equiv_of_quotient_of
- \- *lemma* localization.ring_equiv_of_quotient_symm_mk'
- \- *lemma* localization.ring_equiv_of_quotient_symm_mk
- \- *lemma* localization.ring_equiv_of_quotient_symm_of
- \- *lemma* localization_map.algebra_map_eq
- \- *lemma* localization_map.at_prime.is_unit_mk'_iff
- \- *lemma* localization_map.at_prime.is_unit_to_map_iff
- \- *lemma* localization_map.at_prime.mk'_mem_maximal_iff
- \- *lemma* localization_map.at_prime.to_map_mem_maximal_iff
- \- *def* localization_map.at_prime
- \- *lemma* localization_map.away_map.lift_comp
- \- *lemma* localization_map.away_map.lift_eq
- \- *def* localization_map.away_map
- \- *def* localization_map.codomain
- \- *def* localization_map.coe_submodule
- \- *lemma* localization_map.coeff_integer_normalization_mem_support
- \- *lemma* localization_map.coeff_integer_normalization_of_not_mem_support
- \- *theorem* localization_map.comap_map_of_is_prime_disjoint
- \- *lemma* localization_map.epic_of_localization_map
- \- *lemma* localization_map.eq_iff_eq
- \- *lemma* localization_map.eq_iff_exists
- \- *theorem* localization_map.eq_mk'_iff_mul_eq
- \- *lemma* localization_map.eq_of_eq
- \- *lemma* localization_map.eq_zero_of_fst_eq_zero
- \- *lemma* localization_map.exist_integer_multiples_of_finset
- \- *lemma* localization_map.exists_integer_multiple'
- \- *lemma* localization_map.exists_integer_multiple
- \- *lemma* localization_map.ext
- \- *lemma* localization_map.ext_iff
- \- *lemma* localization_map.injective
- \- *lemma* localization_map.integer_normalization_aeval_eq_zero
- \- *lemma* localization_map.integer_normalization_coeff
- \- *lemma* localization_map.integer_normalization_eval₂_eq_zero
- \- *lemma* localization_map.integer_normalization_map_to_map
- \- *lemma* localization_map.integer_normalization_spec
- \- *def* localization_map.integral_domain_localization
- \- *def* localization_map.integral_domain_of_le_non_zero_divisors
- \- *def* localization_map.is_integer
- \- *lemma* localization_map.is_integer_add
- \- *lemma* localization_map.is_integer_mul
- \- *lemma* localization_map.is_integer_one
- \- *lemma* localization_map.is_integer_smul
- \- *lemma* localization_map.is_integer_zero
- \- *lemma* localization_map.is_noetherian_ring
- \- *lemma* localization_map.is_prime_iff_is_prime_disjoint
- \- *lemma* localization_map.is_prime_of_is_prime_disjoint
- \- *lemma* localization_map.is_unit_comp
- \- *lemma* localization_map.lift_comp
- \- *lemma* localization_map.lift_eq
- \- *lemma* localization_map.lift_eq_iff
- \- *lemma* localization_map.lift_id
- \- *lemma* localization_map.lift_injective_iff
- \- *lemma* localization_map.lift_left_inverse
- \- *lemma* localization_map.lift_mk'
- \- *lemma* localization_map.lift_mk'_spec
- \- *lemma* localization_map.lift_of_comp
- \- *lemma* localization_map.lift_surjective_iff
- \- *lemma* localization_map.lift_unique
- \- *def* localization_map.lin_coe
- \- *lemma* localization_map.lin_coe_apply
- \- *theorem* localization_map.map_comap
- \- *lemma* localization_map.map_comp
- \- *lemma* localization_map.map_comp_map
- \- *lemma* localization_map.map_eq
- \- *lemma* localization_map.map_id
- \- *lemma* localization_map.map_left_cancel
- \- *lemma* localization_map.map_map
- \- *lemma* localization_map.map_mk'
- \- *lemma* localization_map.map_right_cancel
- \- *lemma* localization_map.map_smul
- \- *lemma* localization_map.map_unique
- \- *lemma* localization_map.map_units
- \- *lemma* localization_map.mem_coe_submodule
- \- *theorem* localization_map.mem_map_to_map_iff
- \- *lemma* localization_map.mk'_add
- \- *lemma* localization_map.mk'_eq_iff_eq
- \- *theorem* localization_map.mk'_eq_iff_eq_mul
- \- *lemma* localization_map.mk'_eq_iff_mk'_eq
- \- *lemma* localization_map.mk'_eq_mul_mk'_one
- \- *lemma* localization_map.mk'_eq_of_eq
- \- *lemma* localization_map.mk'_mem_iff
- \- *lemma* localization_map.mk'_mul
- \- *lemma* localization_map.mk'_mul_cancel_left
- \- *lemma* localization_map.mk'_mul_cancel_right
- \- *lemma* localization_map.mk'_mul_mk'_eq_one'
- \- *lemma* localization_map.mk'_mul_mk'_eq_one
- \- *lemma* localization_map.mk'_one
- \- *lemma* localization_map.mk'_sec
- \- *lemma* localization_map.mk'_self''
- \- *lemma* localization_map.mk'_self'
- \- *lemma* localization_map.mk'_self
- \- *lemma* localization_map.mk'_spec'
- \- *lemma* localization_map.mk'_spec
- \- *lemma* localization_map.mk'_surjective
- \- *lemma* localization_map.mul_mk'_eq_mk'_of_mul
- \- *lemma* localization_map.of_id
- \- *def* localization_map.order_embedding
- \- *def* localization_map.order_iso_of_prime
- \- *lemma* localization_map.ring_equiv_of_ring_equiv_eq
- \- *lemma* localization_map.ring_equiv_of_ring_equiv_eq_map
- \- *lemma* localization_map.ring_equiv_of_ring_equiv_eq_map_apply
- \- *lemma* localization_map.ring_equiv_of_ring_equiv_mk'
- \- *lemma* localization_map.sec_spec'
- \- *lemma* localization_map.sec_spec
- \- *lemma* localization_map.surj
- \- *lemma* localization_map.surjective_quotient_map_of_maximal_of_localization
- \- *lemma* localization_map.to_map_eq_zero_iff
- \- *lemma* localization_map.to_map_injective
- \- *lemma* map_injective_of_injective
- \- *def* ring_hom.to_localization_map
- \- *def* submonoid.localization_map.to_ring_localization

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+/\- *lemma* polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius

Modified src/ring_theory/polynomial/dickson.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/polynomial/rational_root.lean
- \+/\- *theorem* denom_dvd_of_is_root
- \+/\- *theorem* is_integer_of_is_root_of_monic
- \+/\- *theorem* num_dvd_of_is_root
- \+/\- *lemma* unique_factorization_monoid.integer_of_integral
- \+/\- *lemma* unique_factorization_monoid.integrally_closed

Modified src/ring_theory/roots_of_unity.lean




## [2021-07-05 13:27:54](https://github.com/leanprover-community/mathlib/commit/6bad4c6)
feat(ring_theory/trace): the composition of `trace`s is `trace` ([#8078](https://github.com/leanprover-community/mathlib/pull/8078))
A little group of lemmas from the Dedekind domain project.
#### Estimated changes
Modified src/ring_theory/trace.lean
- \+ *lemma* algebra.trace_apply
- \+ *lemma* algebra.trace_comp_trace
- \+ *lemma* algebra.trace_comp_trace_of_basis
- \+ *lemma* algebra.trace_trace
- \+ *lemma* algebra.trace_trace_of_basis



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
- \+/\- *lemma* matrix.det_reindex_alg_equiv
- \+/\- *lemma* matrix.det_reindex_linear_equiv_self
- \+/\- *lemma* matrix.mul_reindex_linear_equiv_one
- \+/\- *def* matrix.reindex_alg_equiv
- \+/\- *lemma* matrix.reindex_alg_equiv_apply
- \+/\- *lemma* matrix.reindex_alg_equiv_mul
- \+/\- *lemma* matrix.reindex_alg_equiv_refl
- \+/\- *lemma* matrix.reindex_alg_equiv_symm
- \+/\- *def* matrix.reindex_linear_equiv
- \+/\- *lemma* matrix.reindex_linear_equiv_apply
- \+/\- *lemma* matrix.reindex_linear_equiv_comp
- \+/\- *lemma* matrix.reindex_linear_equiv_comp_apply
- \+/\- *lemma* matrix.reindex_linear_equiv_mul
- \+/\- *lemma* matrix.reindex_linear_equiv_one
- \+/\- *lemma* matrix.reindex_linear_equiv_refl_refl
- \+/\- *lemma* matrix.reindex_linear_equiv_symm
- \+/\- *lemma* matrix.reindex_linear_equiv_trans



## [2021-07-05 09:56:32](https://github.com/leanprover-community/mathlib/commit/a8f60eb)
feat(algebra/lie/free): the universal enveloping algebra of the free Lie algebra is the free associative algebra ([#8183](https://github.com/leanprover-community/mathlib/pull/8183))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* lie_hom.coe_id
- \+ *lemma* lie_hom.coe_one
- \+ *lemma* lie_hom.comp_id
- \+ *lemma* lie_hom.congr_fun
- \+ *def* lie_hom.id
- \+ *lemma* lie_hom.id_apply
- \+ *lemma* lie_hom.id_comp
- \+ *lemma* lie_hom.one_apply
- \+ *lemma* lie_hom.to_fun_eq_coe

Modified src/algebra/lie/free.lean
- \+ *def* free_lie_algebra.universal_enveloping_equiv_free_algebra

Modified src/algebra/lie/of_associative.lean
- \+ *lemma* alg_hom.coe_to_lie_hom
- \+ *def* alg_hom.to_lie_hom
- \+ *lemma* alg_hom.to_lie_hom_apply
- \+ *lemma* alg_hom.to_lie_hom_coe
- \+ *lemma* alg_hom.to_lie_hom_comp
- \+ *lemma* alg_hom.to_lie_hom_id
- \+ *lemma* alg_hom.to_lie_hom_injective
- \- *def* lie_algebra.of_associative_algebra_hom
- \- *lemma* lie_algebra.of_associative_algebra_hom_apply
- \- *lemma* lie_algebra.of_associative_algebra_hom_comp
- \- *lemma* lie_algebra.of_associative_algebra_hom_id

Modified src/algebra/lie/universal_enveloping.lean




## [2021-07-04 16:29:14](https://github.com/leanprover-community/mathlib/commit/4ace3b7)
feat(measure_theory/conditional_expectation): define the Lp subspace of functions measurable wrt a sigma-algebra, prove completeness ([#7945](https://github.com/leanprover-community/mathlib/pull/7945))
This is the first step towards defining the conditional expectation:
- in this PR a subspace of L^p is shown to be complete, which is necessary to define an orthogonal projection on that subspace;
- the conditional expectation of functions in L^2 will be the orthogonal projection;
- the definition will be extended to L^1 through simple functions (as is done for the integral definition).
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.range_eq_univ

Modified src/measure_theory/arithmetic.lean
- \+ *lemma* ae_eq_trim_of_measurable

Added src/measure_theory/conditional_expectation.lean
- \+ *lemma* measure_theory.Lp_meas.ae_measurable'
- \+ *def* measure_theory.Lp_meas
- \+ *lemma* measure_theory.Lp_meas_coe
- \+ *def* measure_theory.Lp_meas_to_Lp_trim
- \+ *lemma* measure_theory.Lp_meas_to_Lp_trim_add
- \+ *lemma* measure_theory.Lp_meas_to_Lp_trim_ae_eq
- \+ *lemma* measure_theory.Lp_meas_to_Lp_trim_left_inv
- \+ *def* measure_theory.Lp_meas_to_Lp_trim_lie
- \+ *lemma* measure_theory.Lp_meas_to_Lp_trim_norm_map
- \+ *lemma* measure_theory.Lp_meas_to_Lp_trim_right_inv
- \+ *lemma* measure_theory.Lp_meas_to_Lp_trim_smul
- \+ *def* measure_theory.Lp_trim_to_Lp_meas
- \+ *lemma* measure_theory.Lp_trim_to_Lp_meas_ae_eq
- \+ *lemma* measure_theory.ae_measurable'.add
- \+ *lemma* measure_theory.ae_measurable'.congr
- \+ *lemma* measure_theory.ae_measurable'.const_smul
- \+ *def* measure_theory.ae_measurable'
- \+ *lemma* measure_theory.ae_measurable'_of_ae_measurable'_trim
- \+ *lemma* measure_theory.mem_Lp_meas_iff_ae_measurable'
- \+ *lemma* measure_theory.mem_Lp_meas_self
- \+ *lemma* measure_theory.mem_Lp_meas_to_Lp_of_trim
- \+ *lemma* measure_theory.mem_ℒp_trim_of_mem_Lp_meas

Modified src/measure_theory/lp_space.lean
- \+/\- *lemma* measure_theory.ess_sup_trim
- \+/\- *lemma* measure_theory.limsup_trim
- \+ *lemma* measure_theory.mem_ℒp_of_mem_ℒp_trim
- \+/\- *lemma* measure_theory.snorm'_trim
- \+/\- *lemma* measure_theory.snorm_ess_sup_trim
- \+/\- *lemma* measure_theory.snorm_trim
- \+ *lemma* measure_theory.snorm_trim_ae

Modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometric.complete_space_iff



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
- \+ *lemma* finset.sdiff_val
- \+ *lemma* list.disjoint_to_finset_iff_disjoint
- \+/\- *lemma* multiset.disjoint_to_finset



## [2021-07-04 13:20:09](https://github.com/leanprover-community/mathlib/commit/2ebd96c)
doc(measure_theory/measurable_space): correct tiny misprints in two doc-strings ([#8187](https://github.com/leanprover-community/mathlib/pull/8187))
Modifying doc-strings of `measurable_space.comap` and `measurable_space.map`: changing "measure space" to "measurable space" in both.
#### Estimated changes
Modified src/measure_theory/measurable_space.lean




## [2021-07-04 11:49:30](https://github.com/leanprover-community/mathlib/commit/7135c96)
chore(data/list/perm): make `perm_nil` a simp lemma ([#8191](https://github.com/leanprover-community/mathlib/pull/8191))
#### Estimated changes
Modified src/data/list/perm.lean
- \+ *theorem* list.nil_perm



## [2021-07-04 09:30:33](https://github.com/leanprover-community/mathlib/commit/a9db7ce)
chore(measure_theory/{bochner_integration, simple_func_dense}): Move construction of embedding of L1 simple funcs ([#8185](https://github.com/leanprover-community/mathlib/pull/8185))
At the moment, there is a low-level construction in `measure_theory/simple_func_dense` for the approximation of an element of L1 by simple functions, and this is generalized to a more abstract version (with a normed space `L1.simple_func` and a dense linear embedding of this into `L1`) in `measure_theory/bochner_integration`.  [#8114](https://github.com/leanprover-community/mathlib/pull/8114) generalized the low-level construction, and I am thinking of rewriting the more abstract version to apply to `Lp`, too.
But since this will all be more generally useful than in the construction of the Bochner integral, and since the Bochner integral file is very long, I propose moving all this material into `measure_theory/simple_func_dense`.  This PR shows what it would look like.  There are no mathematical changes.
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \- *lemma* measure_theory.L1.simple_func.add_to_simple_func
- \- *lemma* measure_theory.L1.simple_func.coe_add
- \- *lemma* measure_theory.L1.simple_func.coe_coe
- \- *lemma* measure_theory.L1.simple_func.coe_neg
- \- *lemma* measure_theory.L1.simple_func.coe_smul
- \- *lemma* measure_theory.L1.simple_func.coe_sub
- \- *def* measure_theory.L1.simple_func.coe_to_L1
- \- *lemma* measure_theory.L1.simple_func.coe_zero
- \- *lemma* measure_theory.L1.simple_func.dist_eq
- \- *lemma* measure_theory.L1.simple_func.dist_to_simple_func
- \- *lemma* measure_theory.L1.simple_func.edist_eq
- \- *lemma* measure_theory.L1.simple_func.lintegral_edist_to_simple_func_lt_top
- \- *lemma* measure_theory.L1.simple_func.neg_to_simple_func
- \- *lemma* measure_theory.L1.simple_func.norm_eq
- \- *lemma* measure_theory.L1.simple_func.norm_to_L1
- \- *lemma* measure_theory.L1.simple_func.norm_to_simple_func
- \- *lemma* measure_theory.L1.simple_func.smul_to_simple_func
- \- *lemma* measure_theory.L1.simple_func.sub_to_simple_func
- \- *def* measure_theory.L1.simple_func.to_L1
- \- *lemma* measure_theory.L1.simple_func.to_L1_add
- \- *lemma* measure_theory.L1.simple_func.to_L1_eq_mk
- \- *lemma* measure_theory.L1.simple_func.to_L1_eq_to_L1
- \- *lemma* measure_theory.L1.simple_func.to_L1_neg
- \- *lemma* measure_theory.L1.simple_func.to_L1_smul
- \- *lemma* measure_theory.L1.simple_func.to_L1_sub
- \- *lemma* measure_theory.L1.simple_func.to_L1_to_simple_func
- \- *lemma* measure_theory.L1.simple_func.to_L1_zero
- \- *def* measure_theory.L1.simple_func.to_simple_func
- \- *lemma* measure_theory.L1.simple_func.to_simple_func_eq_to_fun
- \- *lemma* measure_theory.L1.simple_func.to_simple_func_to_L1
- \- *lemma* measure_theory.L1.simple_func.zero_to_simple_func
- \- *def* measure_theory.L1.simple_func
- \- *lemma* measure_theory.simple_func.exists_forall_norm_le
- \- *lemma* measure_theory.simple_func.fin_meas_supp.integrable
- \- *lemma* measure_theory.simple_func.integrable_iff
- \- *lemma* measure_theory.simple_func.integrable_iff_fin_meas_supp
- \- *lemma* measure_theory.simple_func.integrable_of_finite_measure
- \- *lemma* measure_theory.simple_func.integrable_pair
- \- *lemma* measure_theory.simple_func.measure_preimage_lt_top_of_integrable
- \- *lemma* measure_theory.simple_func.measure_preimage_lt_top_of_mem_ℒp
- \- *lemma* measure_theory.simple_func.mem_ℒp_iff
- \- *lemma* measure_theory.simple_func.mem_ℒp_iff_fin_meas_supp
- \- *lemma* measure_theory.simple_func.mem_ℒp_iff_integrable
- \- *lemma* measure_theory.simple_func.mem_ℒp_of_finite_measure
- \- *lemma* measure_theory.simple_func.mem_ℒp_of_finite_measure_preimage
- \- *lemma* measure_theory.simple_func.mem_ℒp_top
- \- *lemma* measure_theory.simple_func.mem_ℒp_zero

Modified src/measure_theory/set_integral.lean
- \- *lemma* measure_theory.integrable.induction

Modified src/measure_theory/simple_func_dense.lean
- \+ *lemma* measure_theory.L1.simple_func.add_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.coe_add
- \+ *lemma* measure_theory.L1.simple_func.coe_coe
- \+ *lemma* measure_theory.L1.simple_func.coe_neg
- \+ *lemma* measure_theory.L1.simple_func.coe_smul
- \+ *lemma* measure_theory.L1.simple_func.coe_sub
- \+ *def* measure_theory.L1.simple_func.coe_to_L1
- \+ *lemma* measure_theory.L1.simple_func.coe_zero
- \+ *lemma* measure_theory.L1.simple_func.dist_eq
- \+ *lemma* measure_theory.L1.simple_func.dist_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.edist_eq
- \+ *lemma* measure_theory.L1.simple_func.lintegral_edist_to_simple_func_lt_top
- \+ *lemma* measure_theory.L1.simple_func.neg_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.norm_eq
- \+ *lemma* measure_theory.L1.simple_func.norm_to_L1
- \+ *lemma* measure_theory.L1.simple_func.norm_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.smul_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.sub_to_simple_func
- \+ *def* measure_theory.L1.simple_func.to_L1
- \+ *lemma* measure_theory.L1.simple_func.to_L1_add
- \+ *lemma* measure_theory.L1.simple_func.to_L1_eq_mk
- \+ *lemma* measure_theory.L1.simple_func.to_L1_eq_to_L1
- \+ *lemma* measure_theory.L1.simple_func.to_L1_neg
- \+ *lemma* measure_theory.L1.simple_func.to_L1_smul
- \+ *lemma* measure_theory.L1.simple_func.to_L1_sub
- \+ *lemma* measure_theory.L1.simple_func.to_L1_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.to_L1_zero
- \+ *def* measure_theory.L1.simple_func.to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.to_simple_func_eq_to_fun
- \+ *lemma* measure_theory.L1.simple_func.to_simple_func_to_L1
- \+ *lemma* measure_theory.L1.simple_func.zero_to_simple_func
- \+ *def* measure_theory.L1.simple_func
- \+ *lemma* measure_theory.integrable.induction
- \+ *lemma* measure_theory.simple_func.exists_forall_norm_le
- \+ *lemma* measure_theory.simple_func.fin_meas_supp.integrable
- \+ *lemma* measure_theory.simple_func.integrable_iff
- \+ *lemma* measure_theory.simple_func.integrable_iff_fin_meas_supp
- \+ *lemma* measure_theory.simple_func.integrable_of_finite_measure
- \+ *lemma* measure_theory.simple_func.integrable_pair
- \+ *lemma* measure_theory.simple_func.measure_preimage_lt_top_of_integrable
- \+ *lemma* measure_theory.simple_func.measure_preimage_lt_top_of_mem_ℒp
- \+ *lemma* measure_theory.simple_func.mem_ℒp_iff
- \+ *lemma* measure_theory.simple_func.mem_ℒp_iff_fin_meas_supp
- \+ *lemma* measure_theory.simple_func.mem_ℒp_iff_integrable
- \+ *lemma* measure_theory.simple_func.mem_ℒp_of_finite_measure
- \+ *lemma* measure_theory.simple_func.mem_ℒp_of_finite_measure_preimage
- \+ *lemma* measure_theory.simple_func.mem_ℒp_top
- \+ *lemma* measure_theory.simple_func.mem_ℒp_zero



## [2021-07-04 09:30:32](https://github.com/leanprover-community/mathlib/commit/180d004)
ci(.github/workflows/*): switch to self-hosted runners ([#8177](https://github.com/leanprover-community/mathlib/pull/8177))
With this PR, mathlib builds on all branches will use the self-hosted runners that have the "pr" tag. One self-hosted runner is reserved for bors staging branch builds and does not have that tag.
The `build_fork` workflow has been added for use by external forks (and other Lean projects which might want to copy mathlib's CI).
#### Estimated changes
Modified .github/workflows/bors.yml


Modified .github/workflows/build.yml


Modified .github/workflows/build.yml.in


Added .github/workflows/build_fork.yml


Modified .github/workflows/mk_build_yml.sh


Modified bors.toml




## [2021-07-04 07:58:33](https://github.com/leanprover-community/mathlib/commit/863f007)
feat(data/list/basic): map_permutations ([#8188](https://github.com/leanprover-community/mathlib/pull/8188))
As [requested on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/perm.20of.20permutations/near/244821779).
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.foldr_permutations_aux2
- \+ *theorem* list.length_foldr_permutations_aux2'
- \+ *theorem* list.length_foldr_permutations_aux2
- \+ *theorem* list.length_permutations_aux2
- \+ *lemma* list.map_bind
- \+ *theorem* list.map_permutations
- \+ *theorem* list.map_permutations_aux2'
- \+ *theorem* list.map_permutations_aux2
- \+ *theorem* list.map_permutations_aux
- \+ *theorem* list.mem_foldr_permutations_aux2
- \+ *theorem* list.mem_permutations_aux2'
- \+ *theorem* list.mem_permutations_aux2
- \+ *theorem* list.permutations_aux2_append
- \+ *theorem* list.permutations_aux2_fst
- \+ *theorem* list.permutations_aux2_snd_cons
- \+ *theorem* list.permutations_aux2_snd_nil

Modified src/data/list/perm.lean
- \- *theorem* list.foldr_permutations_aux2
- \- *theorem* list.length_foldr_permutations_aux2'
- \- *theorem* list.length_foldr_permutations_aux2
- \- *theorem* list.length_permutations_aux2
- \- *theorem* list.mem_foldr_permutations_aux2
- \- *theorem* list.mem_permutations_aux2'
- \- *theorem* list.mem_permutations_aux2
- \- *theorem* list.permutations_aux2_append
- \- *theorem* list.permutations_aux2_fst
- \- *theorem* list.permutations_aux2_snd_cons
- \- *theorem* list.permutations_aux2_snd_nil



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

Added src/category_theory/derived.lean
- \+ *def* category_theory.functor.left_derived
- \+ *lemma* category_theory.functor.left_derived_map_eq
- \+ *def* category_theory.functor.left_derived_obj_iso
- \+ *def* category_theory.functor.left_derived_obj_projective_succ
- \+ *def* category_theory.functor.left_derived_obj_projective_zero
- \+ *def* category_theory.nat_trans.left_derived
- \+ *lemma* category_theory.nat_trans.left_derived_comp
- \+ *lemma* category_theory.nat_trans.left_derived_eq
- \+ *lemma* category_theory.nat_trans.left_derived_id



## [2021-07-03 13:08:36](https://github.com/leanprover-community/mathlib/commit/74a0f67)
refactor(measure_theory/simple_func_dense): generalize approximation results from L^1 to L^p ([#8114](https://github.com/leanprover-community/mathlib/pull/8114))
Simple functions are dense in L^p.  The argument for `1 ≤ p < ∞` is exactly the same as for `p = 1`, which was already in mathlib:  construct a suitable sequence of pointwise approximations and apply the Dominated Convergence Theorem.  This PR refactors to provide the general-`p` result.
The argument for `p = ∞` requires finite-dimensionality of `E` and a different approximating sequence, so is left for another PR.
#### Estimated changes
Modified src/analysis/convex/integral.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/lp_space.lean
- \+ *lemma* measure_theory.Lp.tendsto_Lp_iff_tendsto_ℒp''
- \+/\- *lemma* measure_theory.Lp.tendsto_Lp_iff_tendsto_ℒp'
- \+/\- *lemma* measure_theory.Lp.tendsto_Lp_iff_tendsto_ℒp
- \+ *lemma* measure_theory.lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top
- \+ *lemma* measure_theory.snorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top

Modified src/measure_theory/prod.lean


Modified src/measure_theory/simple_func_dense.lean
- \+ *lemma* measure_theory.simple_func.mem_ℒp_approx_on
- \+ *lemma* measure_theory.simple_func.mem_ℒp_approx_on_univ
- \+ *lemma* measure_theory.simple_func.nnnorm_approx_on_le
- \+ *lemma* measure_theory.simple_func.norm_approx_on_y₀_le
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_L1_edist
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_L1_nnnorm
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_Lp_snorm
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_univ_L1_edist
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_univ_L1_nnnorm
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_univ_Lp
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_univ_Lp_snorm



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
- \+/\- *lemma* equiv.perm.of_subtype_apply_coe
- \+ *lemma* equiv.perm.of_subtype_apply_of_mem



## [2021-07-03 10:46:47](https://github.com/leanprover-community/mathlib/commit/25d042c)
feat(algebra/periodic): a few more periodicity lemmas ([#8062](https://github.com/leanprover-community/mathlib/pull/8062))
A few more lemmas about periodic functions that I realized are useful.
#### Estimated changes
Modified src/algebra/periodic.lean
- \+ *lemma* function.antiperiodic.funext'
- \+ *lemma* function.antiperiodic.funext
- \+ *lemma* function.periodic.funext



## [2021-07-03 09:58:05](https://github.com/leanprover-community/mathlib/commit/915902e)
feat(topology/algebra/multilinear): add a linear_equiv version of pi ([#8064](https://github.com/leanprover-community/mathlib/pull/8064))
This is a weaker version of `continuous_multilinear_map.piₗᵢ` that requires weaker typeclasses.
Unfortunately I don't understand why the typeclass system continues not to cooperate here, but I suspect it's the same class of problem that plagues `dfinsupp`.
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean


Modified src/topology/algebra/mul_action.lean


Modified src/topology/algebra/multilinear.lean
- \+/\- *def* continuous_linear_map.comp_continuous_multilinear_map
- \+/\- *lemma* continuous_linear_map.comp_continuous_multilinear_map_coe
- \+/\- *lemma* continuous_multilinear_map.coe_pi
- \+/\- *def* continuous_multilinear_map.pi
- \+/\- *lemma* continuous_multilinear_map.pi_apply
- \+ *def* continuous_multilinear_map.pi_equiv
- \+ *def* continuous_multilinear_map.pi_linear_equiv



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
- \+/\- *lemma* continuous_map.id_coe



## [2021-07-02 19:46:00](https://github.com/leanprover-community/mathlib/commit/9e9dfc2)
feat(category_theory/adjunction/fully_faithful): Converses to `unit_is_iso_of_L_fully_faithful` and `counit_is_iso_of_R_fully_faithful` ([#8181](https://github.com/leanprover-community/mathlib/pull/8181))
Add a converse to `unit_is_iso_of_L_fully_faithful` and to `counit_is_iso_of_R_fully_faithful`
#### Estimated changes
Modified src/category_theory/adjunction/fully_faithful.lean
- \+ *lemma* category_theory.L_faithful_of_unit_is_iso
- \+ *def* category_theory.L_full_of_unit_is_iso
- \+ *lemma* category_theory.R_faithful_of_counit_is_iso
- \+ *def* category_theory.R_full_of_counit_is_iso
- \+ *lemma* category_theory.inv_counit_map
- \+ *lemma* category_theory.inv_map_unit



## [2021-07-02 18:29:36](https://github.com/leanprover-community/mathlib/commit/ea924e5)
feat(data/nat/choose/bounds): exponential bounds on binomial coefficients ([#8095](https://github.com/leanprover-community/mathlib/pull/8095))
#### Estimated changes
Added src/combinatorics/choose/bounds.lean
- \+ *lemma* choose_le_pow
- \+ *lemma* pow_le_choose



## [2021-07-02 16:37:34](https://github.com/leanprover-community/mathlib/commit/67c72b4)
feat(data/list/cycle): lift next_prev to cycle ([#8172](https://github.com/leanprover-community/mathlib/pull/8172))
#### Estimated changes
Modified src/data/list/cycle.lean
- \+ *lemma* cycle.next_prev
- \+ *lemma* cycle.prev_next



## [2021-07-02 10:55:24](https://github.com/leanprover-community/mathlib/commit/d6a7c3b)
chore(algebra/algebra/basic): add `alg_hom.of_linear_map` and lemmas ([#8151](https://github.com/leanprover-community/mathlib/pull/8151))
This lets me golf `complex.lift` a little
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* alg_hom.of_linear_map
- \+ *lemma* alg_hom.of_linear_map_id
- \+ *lemma* alg_hom.of_linear_map_to_linear_map
- \+ *lemma* alg_hom.to_linear_map_id
- \+ *lemma* alg_hom.to_linear_map_of_linear_map

Modified src/data/complex/module.lean




## [2021-07-02 08:19:35](https://github.com/leanprover-community/mathlib/commit/dfc42f9)
feat(data/equiv/basic): swap_apply_ne_self_iff ([#8167](https://github.com/leanprover-community/mathlib/pull/8167))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.swap_apply_ne_self_iff



## [2021-07-02 05:56:27](https://github.com/leanprover-community/mathlib/commit/f5f8a20)
feat(analysis/calculus/fderiv_symmetric): prove that the second derivative is symmetric ([#8104](https://github.com/leanprover-community/mathlib/pull/8104))
We show that, if a function is differentiable over the reals around a point `x`, and is second-differentiable at `x`, then the second derivative is symmetric. In fact, we even prove a stronger statement for functions differentiable within a convex set, to be able to apply it for functions on the half-plane or the quadrant.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *theorem* asymptotics.is_o_const_const_iff

Added src/analysis/calculus/fderiv_symmetric.lean
- \+ *lemma* convex.is_o_alternate_sum_square
- \+ *theorem* convex.second_derivative_within_at_symmetric
- \+ *lemma* convex.second_derivative_within_at_symmetric_of_mem_interior
- \+ *lemma* convex.taylor_approx_two_segment
- \+ *theorem* second_derivative_symmetric
- \+ *theorem* second_derivative_symmetric_of_eventually

Modified src/analysis/convex/basic.lean
- \+ *lemma* convex.add_smul_mem
- \+ *lemma* convex.add_smul_sub_mem

Modified src/analysis/convex/topology.lean
- \+ *lemma* convex.add_smul_mem_interior
- \+ *lemma* convex.add_smul_sub_mem_interior

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* add_mem_ball_iff_norm
- \+ *lemma* add_mem_closed_ball_iff_norm



## [2021-07-01 21:10:28](https://github.com/leanprover-community/mathlib/commit/92b64a0)
feat(data/list/duplicate): prop that element is a duplicate ([#7824](https://github.com/leanprover-community/mathlib/pull/7824))
As discussed in https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/nodup.20and.20decidability and [#7587](https://github.com/leanprover-community/mathlib/pull/7587)
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.sublist_nil_iff_eq_nil

Added src/data/list/duplicate.lean
- \+ *lemma* list.duplicate.duplicate_cons
- \+ *lemma* list.duplicate.elim_nil
- \+ *lemma* list.duplicate.elim_singleton
- \+ *lemma* list.duplicate.mem
- \+ *lemma* list.duplicate.mem_cons_self
- \+ *lemma* list.duplicate.mono_sublist
- \+ *lemma* list.duplicate.ne_nil
- \+ *lemma* list.duplicate.ne_singleton
- \+ *lemma* list.duplicate.not_nodup
- \+ *lemma* list.duplicate.of_duplicate_cons
- \+ *lemma* list.duplicate_cons_iff
- \+ *lemma* list.duplicate_cons_iff_of_ne
- \+ *lemma* list.duplicate_cons_self_iff
- \+ *lemma* list.duplicate_iff_sublist
- \+ *lemma* list.duplicate_iff_two_le_count
- \+ *lemma* list.exists_duplicate_iff_not_nodup
- \+ *lemma* list.mem.duplicate_cons_self
- \+ *lemma* list.nodup_iff_forall_not_duplicate
- \+ *lemma* list.not_duplicate_nil
- \+ *lemma* list.not_duplicate_singleton

Modified src/data/list/nodup_equiv_fin.lean
- \+ *lemma* list.duplicate_iff_exists_distinct_nth_le
- \+ *lemma* list.sublist_iff_exists_fin_order_embedding_nth_le_eq
- \+ *lemma* list.sublist_iff_exists_order_embedding_nth_eq
- \+ *lemma* list.sublist_of_order_embedding_nth_eq



## [2021-07-01 19:34:23](https://github.com/leanprover-community/mathlib/commit/5945ca3)
chore(*): update to lean 3.31.0c ([#8122](https://github.com/leanprover-community/mathlib/pull/8122))
#### Estimated changes
Modified leanpkg.toml


Modified src/combinatorics/composition.lean


Added src/data/lazy_list.lean
- \+ *def* lazy_list.append
- \+ *def* lazy_list.approx
- \+ *def* lazy_list.filter
- \+ *def* lazy_list.for
- \+ *def* lazy_list.head
- \+ *def* lazy_list.join
- \+ *def* lazy_list.map
- \+ *def* lazy_list.map₂
- \+ *def* lazy_list.nth
- \+ *def* lazy_list.of_list
- \+ *def* lazy_list.singleton
- \+ *def* lazy_list.tail
- \+ *def* lazy_list.to_list
- \+ *def* lazy_list.zip

Modified src/data/lazy_list/basic.lean




## [2021-07-01 18:15:23](https://github.com/leanprover-community/mathlib/commit/395d871)
chore(algebra/lie/free): tidy up after [#8153](https://github.com/leanprover-community/mathlib/pull/8153) ([#8163](https://github.com/leanprover-community/mathlib/pull/8163))
@eric-wieser had some further comments and suggestions which didn't make it into [#8153](https://github.com/leanprover-community/mathlib/pull/8153)
#### Estimated changes
Modified src/algebra/free_non_unital_non_assoc_algebra.lean


Modified src/algebra/lie/free.lean
- \+/\- *lemma* free_lie_algebra.hom_ext
- \+ *lemma* free_lie_algebra.rel.neg

Modified src/algebra/lie/non_unital_non_assoc_algebra.lean
- \+/\- *def* lie_hom.to_non_unital_alg_hom
- \+ *lemma* lie_hom.to_non_unital_alg_hom_injective



## [2021-07-01 16:37:06](https://github.com/leanprover-community/mathlib/commit/1571290)
feat(logic/is_empty): add some simp lemmas and unique instances ([#7832](https://github.com/leanprover-community/mathlib/pull/7832))
There are a handful of lemmas about `(h : ¬nonempty a)` that if restated in terms of `[is_empty a]` become suitable for `simp` or as `instance`s. This adjusts some of those lemmas.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.eq_empty_of_is_empty

Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.subsingleton_of_empty_left
- \+/\- *lemma* matrix.subsingleton_of_empty_right

Modified src/data/matrix/dmatrix.lean
- \+/\- *lemma* dmatrix.subsingleton_of_empty_left
- \+/\- *lemma* dmatrix.subsingleton_of_empty_right

Modified src/data/set/basic.lean
- \+ *theorem* set.eq_empty_of_is_empty
- \+ *def* set.unique_empty

Modified src/linear_algebra/char_poly/coeff.lean


Modified src/logic/embedding.lean


Modified src/logic/is_empty.lean
- \+ *lemma* subtype.is_empty_of_false

Modified src/order/filter/basic.lean
- \+ *lemma* filter.filter_eq_bot_of_is_empty

Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.eq_zero_of_is_empty

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
- \+ *lemma* alg_hom.to_ring_hom_eq_coe

Modified src/analysis/fourier.lean
- \+ *def* fourier_subalgebra
- \+ *lemma* fourier_subalgebra_closure_eq_top
- \+ *lemma* fourier_subalgebra_coe
- \+ *lemma* fourier_subalgebra_conj_invariant
- \+ *lemma* fourier_subalgebra_separates_points
- \+ *lemma* span_fourier_closure_eq_top

Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* ideal.quotient.mkₐ_ker



## [2021-07-01 12:58:30](https://github.com/leanprover-community/mathlib/commit/3fa61ea)
feat(algebra/lie/free): construction of free Lie algebras ([#8153](https://github.com/leanprover-community/mathlib/pull/8153))
#### Estimated changes
Added src/algebra/lie/free.lean
- \+ *lemma* free_lie_algebra.hom_ext
- \+ *def* free_lie_algebra.lift
- \+ *def* free_lie_algebra.lift_aux
- \+ *lemma* free_lie_algebra.lift_aux_map_add
- \+ *lemma* free_lie_algebra.lift_aux_map_mul
- \+ *lemma* free_lie_algebra.lift_aux_map_smul
- \+ *lemma* free_lie_algebra.lift_aux_spec
- \+ *lemma* free_lie_algebra.lift_comp_of
- \+ *lemma* free_lie_algebra.lift_of_apply
- \+ *lemma* free_lie_algebra.lift_symm_apply
- \+ *lemma* free_lie_algebra.lift_unique
- \+ *def* free_lie_algebra.mk
- \+ *def* free_lie_algebra.of
- \+ *lemma* free_lie_algebra.of_comp_lift
- \+ *lemma* free_lie_algebra.rel.add_left
- \+ *def* free_lie_algebra

Added src/algebra/lie/non_unital_non_assoc_algebra.lean
- \+ *def* lie_hom.to_non_unital_alg_hom
- \+ *def* lie_ring.to_non_unital_non_assoc_semiring

Modified src/algebra/non_unital_alg_hom.lean
- \+ *lemma* non_unital_alg_hom.congr_fun



## [2021-07-01 12:58:29](https://github.com/leanprover-community/mathlib/commit/4d24172)
docs(order/zorn): explain how to use Zorn's lemma ([#8125](https://github.com/leanprover-community/mathlib/pull/8125))
#### Estimated changes
Modified src/order/zorn.lean




## [2021-07-01 12:58:27](https://github.com/leanprover-community/mathlib/commit/7cbca35)
feat(data/fintype/intervals): fintype instances for set.{Icc,Ioc,Ioo} ([#8123](https://github.com/leanprover-community/mathlib/pull/8123))
#### Estimated changes
Modified src/data/fintype/intervals.lean
- \+ *lemma* set.Icc_ℤ_card
- \+/\- *lemma* set.Icc_ℤ_finite
- \+ *lemma* set.Ioc_ℤ_card
- \+/\- *lemma* set.Ioc_ℤ_finite
- \+ *lemma* set.Ioo_ℤ_card
- \+/\- *lemma* set.Ioo_ℤ_finite



## [2021-07-01 11:10:36](https://github.com/leanprover-community/mathlib/commit/6e0d2d3)
feat(logic/basic): add two simp lemmas ([#8148](https://github.com/leanprover-community/mathlib/pull/8148))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* iff_and_self
- \+ *lemma* iff_self_and



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
- \+ *lemma* preorder_hom.preorder_hom_eq_id
- \+ *def* preorder_hom.unique



## [2021-07-01 07:48:32](https://github.com/leanprover-community/mathlib/commit/4a75876)
feat(category_theory/limits/concrete_category): Some lemmas about limits in concrete categories ([#8130](https://github.com/leanprover-community/mathlib/pull/8130))
Generalizes some lemmas from LTE. 
See zulip discussion [here](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/for_mathlib.2Fwide_pullback/near/244298079).
#### Estimated changes
Modified src/category_theory/limits/concrete_category.lean
- \+ *lemma* category_theory.limits.concrete.colimit_exists_rep
- \+ *lemma* category_theory.limits.concrete.from_union_surjective_of_is_colimit
- \+ *lemma* category_theory.limits.concrete.is_colimit_exists_rep
- \+ *lemma* category_theory.limits.concrete.is_limit_ext
- \+ *lemma* category_theory.limits.concrete.limit_ext
- \+ *lemma* category_theory.limits.concrete.to_product_injective_of_is_limit
- \+ *lemma* category_theory.limits.concrete.wide_pullback_ext'
- \+ *lemma* category_theory.limits.concrete.wide_pullback_ext
- \+ *lemma* category_theory.limits.concrete.wide_pushout_exists_rep'
- \+ *lemma* category_theory.limits.concrete.wide_pushout_exists_rep

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


