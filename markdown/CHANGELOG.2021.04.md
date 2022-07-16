## [2021-04-30 20:11:22](https://github.com/leanprover-community/mathlib/commit/16c8f7f)
feat(algebraic_geometry/prime_spectrum): Basic opens are compact ([#7411](https://github.com/leanprover-community/mathlib/pull/7411))
This proves that basic opens are compact in the zariski topology. Compactness of the whole space is then realized as a special case. Also adds a few lemmas about zero loci.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean
- \+ *lemma* prime_spectrum.basic_open_le_basic_open_iff
- \+ *lemma* prime_spectrum.basic_open_mul_le_left
- \+ *lemma* prime_spectrum.basic_open_mul_le_right
- \+ *lemma* prime_spectrum.is_compact_basic_open
- \+ *lemma* prime_spectrum.zero_locus_subset_zero_locus_iff
- \+ *lemma* prime_spectrum.zero_locus_subset_zero_locus_singleton_iff

Modified src/ring_theory/ideal/operations.lean
- \+ *theorem* ideal.radical_le_radical_iff



## [2021-04-30 20:11:21](https://github.com/leanprover-community/mathlib/commit/aebe755)
refactor(algebra/group_power): put lemmas about order and power in their own file ([#7398](https://github.com/leanprover-community/mathlib/pull/7398))
This means `group_power/basic` has fewer dependencies, making it accessible earlier in the import graph.
The first two lemmas in this `basic` were moved to the end of `order`, but otherwise lemmas have been moved without modification and kept in the same order.
The new imports added in other files are the ones needed to make this build.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \- *theorem* abs_le_abs_of_sq_le_sq
- \- *theorem* abs_le_of_sq_le_sq'
- \- *theorem* abs_le_of_sq_le_sq
- \- *theorem* abs_lt_abs_of_sq_lt_sq
- \- *theorem* abs_lt_of_sq_lt_sq'
- \- *theorem* abs_lt_of_sq_lt_sq
- \- *lemma* abs_neg_one_pow
- \- *theorem* abs_sq
- \- *theorem* canonically_ordered_semiring.one_le_pow_of_one_le
- \- *theorem* canonically_ordered_semiring.pow_le_one
- \- *lemma* canonically_ordered_semiring.pow_le_pow_of_le_left
- \- *theorem* canonically_ordered_semiring.pow_pos
- \- *lemma* eq_of_sq_eq_sq
- \- *theorem* gsmul_nonneg
- \- *lemma* le_of_pow_le_pow
- \- *lemma* lt_of_pow_lt_pow
- \- *theorem* nsmul_le_nsmul
- \- *lemma* nsmul_le_nsmul_of_le_right
- \- *theorem* nsmul_lt_nsmul
- \- *theorem* nsmul_nonneg
- \- *lemma* nsmul_pos
- \- *theorem* one_le_pow_of_one_le
- \- *lemma* pow_abs
- \- *theorem* pow_add_pow_le
- \- *theorem* pow_bit0_nonneg
- \- *theorem* pow_bit0_pos
- \- *theorem* pow_le_pow
- \- *lemma* pow_le_pow_of_le_left
- \- *theorem* pow_left_inj
- \- *lemma* pow_lt_pow
- \- *lemma* pow_lt_pow_iff
- \- *theorem* pow_lt_pow_of_lt_left
- \- *lemma* pow_mono
- \- *theorem* pow_nonneg
- \- *theorem* pow_pos
- \- *theorem* sq_abs
- \- *theorem* sq_le_sq'
- \- *theorem* sq_le_sq
- \- *theorem* sq_lt_sq'
- \- *theorem* sq_lt_sq
- \- *theorem* sq_nonneg
- \- *theorem* sq_pos_of_ne_zero
- \- *theorem* strict_mono_incr_on_pow
- \- *lemma* strict_mono_pow
- \- *lemma* two_mul_le_add_sq

Modified src/algebra/group_power/lemmas.lean


Added src/algebra/group_power/order.lean
- \+ *theorem* abs_le_abs_of_sq_le_sq
- \+ *theorem* abs_le_of_sq_le_sq'
- \+ *theorem* abs_le_of_sq_le_sq
- \+ *theorem* abs_lt_abs_of_sq_lt_sq
- \+ *theorem* abs_lt_of_sq_lt_sq'
- \+ *theorem* abs_lt_of_sq_lt_sq
- \+ *lemma* abs_neg_one_pow
- \+ *theorem* abs_sq
- \+ *theorem* canonically_ordered_semiring.one_le_pow_of_one_le
- \+ *theorem* canonically_ordered_semiring.pow_le_one
- \+ *lemma* canonically_ordered_semiring.pow_le_pow_of_le_left
- \+ *theorem* canonically_ordered_semiring.pow_pos
- \+ *lemma* eq_of_sq_eq_sq
- \+ *theorem* gsmul_nonneg
- \+ *lemma* le_of_pow_le_pow
- \+ *lemma* lt_of_pow_lt_pow
- \+ *theorem* nsmul_le_nsmul
- \+ *lemma* nsmul_le_nsmul_of_le_right
- \+ *theorem* nsmul_lt_nsmul
- \+ *theorem* nsmul_nonneg
- \+ *lemma* nsmul_pos
- \+ *theorem* one_le_pow_of_one_le
- \+ *lemma* pow_abs
- \+ *theorem* pow_add_pow_le
- \+ *theorem* pow_bit0_nonneg
- \+ *theorem* pow_bit0_pos
- \+ *theorem* pow_le_pow
- \+ *lemma* pow_le_pow_of_le_left
- \+ *theorem* pow_left_inj
- \+ *lemma* pow_lt_pow
- \+ *lemma* pow_lt_pow_iff
- \+ *theorem* pow_lt_pow_of_lt_left
- \+ *lemma* pow_mono
- \+ *theorem* pow_nonneg
- \+ *theorem* pow_pos
- \+ *theorem* sq_abs
- \+ *theorem* sq_le_sq'
- \+ *theorem* sq_le_sq
- \+ *theorem* sq_lt_sq'
- \+ *theorem* sq_lt_sq
- \+ *theorem* sq_nonneg
- \+ *theorem* sq_pos_of_ne_zero
- \+ *theorem* strict_mono_incr_on_pow
- \+ *lemma* strict_mono_pow
- \+ *lemma* two_mul_le_add_sq

Modified src/data/nat/basic.lean




## [2021-04-30 20:11:19](https://github.com/leanprover-community/mathlib/commit/6d5a120)
refactor(linear_algebra/eigenspace): cleanup proof ([#7337](https://github.com/leanprover-community/mathlib/pull/7337))
At some point we changed the proof of `exists_eigenvalue` so that it used the fact that any endomorphism of a vector space is integral. This means we don't actually need to pick a nonzero vector at any point, but the proof had been left in a hybrid state, which I've now cleaned up.
In a later PR I'll generalise this proof so it proves Schur's lemma.
#### Estimated changes
Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/eigenspace.lean




## [2021-04-30 20:11:18](https://github.com/leanprover-community/mathlib/commit/5800f69)
feat(category_theory/Quiv): the free/forgetful adjunction between Cat and Quiv ([#7158](https://github.com/leanprover-community/mathlib/pull/7158))
#### Estimated changes
Added src/category_theory/category/Quiv.lean
- \+ *def* category_theory.Cat.free
- \+ *def* category_theory.Quiv.adj
- \+ *def* category_theory.Quiv.forget
- \+ *def* category_theory.Quiv.lift
- \+ *def* category_theory.Quiv.of
- \+ *def* category_theory.Quiv

Modified src/category_theory/functor.lean
- \+/\- *structure* category_theory.functor

Added src/category_theory/path_category.lean
- \+ *def* category_theory.compose_path
- \+ *lemma* category_theory.compose_path_comp
- \+ *def* category_theory.paths.of
- \+ *def* category_theory.paths
- \+ *lemma* category_theory.prefunctor.map_path_comp'

Modified src/combinatorics/quiver.lean
- \+ *def* prefunctor.comp
- \+ *def* prefunctor.id
- \+ *def* prefunctor.map_path
- \+ *lemma* prefunctor.map_path_comp
- \+ *lemma* prefunctor.map_path_cons
- \+ *lemma* prefunctor.map_path_nil
- \+ *structure* prefunctor
- \+/\- *inductive* quiver.path



## [2021-04-30 14:55:00](https://github.com/leanprover-community/mathlib/commit/64fdfc7)
feat(category_theory/sites): construct a presieve from an indexed family of arrows ([#7413](https://github.com/leanprover-community/mathlib/pull/7413))
For the LTE: alternate constructors for presieves which can be more convenient.
#### Estimated changes
Modified src/category_theory/sites/pretopology.lean
- \- *inductive* category_theory.pullback_arrows
- \- *lemma* category_theory.pullback_arrows_comm
- \- *lemma* category_theory.pullback_singleton

Modified src/category_theory/sites/sieves.lean
- \+ *inductive* category_theory.presieve.of_arrows
- \+ *lemma* category_theory.presieve.of_arrows_bind
- \+ *lemma* category_theory.presieve.of_arrows_pullback
- \+ *lemma* category_theory.presieve.of_arrows_punit
- \+ *inductive* category_theory.presieve.pullback_arrows
- \+ *lemma* category_theory.presieve.pullback_singleton
- \+ *lemma* category_theory.sieve.pullback_arrows_comm

Modified src/category_theory/sites/spaces.lean




## [2021-04-30 10:14:07](https://github.com/leanprover-community/mathlib/commit/4722dd4)
feat(ring_theory/finiteness): add add_monoid_algebra.ft_of_fg ([#7265](https://github.com/leanprover-community/mathlib/pull/7265))
This is from `lean_liquid`. We prove `add_monoid_algebra.ft_of_fg`: if `M` is a finitely generated monoid then `add_monoid_algebra R M` if finitely generated as `R-alg`.
The converse is also true, but the proof is longer and I wanted to keep the PR small.
- [x] depends on: [#7279](https://github.com/leanprover-community/mathlib/pull/7279)
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *theorem* submodule.mem_to_add_submonoid

Modified src/algebra/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.induction_on
- \+ *def* add_monoid_algebra.to_multiplicative_alg_equiv
- \+ *lemma* monoid_algebra.induction_on
- \+ *def* monoid_algebra.to_additive_alg_equiv

Modified src/ring_theory/finiteness.lean
- \+ *lemma* add_monoid_algebra.mv_polynomial_aeval_of_surjective_of_closure
- \+ *lemma* monoid_algebra.mv_polynomial_aeval_of_surjective_of_closure



## [2021-04-30 10:14:06](https://github.com/leanprover-community/mathlib/commit/4a94b28)
feat(category_theory/sites): Sheaves of structures ([#5927](https://github.com/leanprover-community/mathlib/pull/5927))
Define sheaves on a site taking values in an arbitrary category.
Joint with @kbuzzard. cc: @jcommelin, this is a step towards condensed abelian groups.
I don't love the names here, design advice (particularly from those who'll use this) more than appreciated.
The main points are:
- An `A`-valued presheaf `P : C^op => A` is defined to be a sheaf (for the topology J) iff for every `X : A`, the type-valued presheaves of sets given by sending `U : C^op` to `Hom_{A}(X, P U)` are all sheaves of sets.
- When `A = Type`, this recovers the basic definition of sheaves of sets.
- An alternate definition when `C` is small, has pullbacks and `A` has products is given by an equalizer condition `is_sheaf'`.
- This is equivalent to the earlier definition.
- When `A = Type`, this is definitionally equal to the equalizer condition for presieves in sheaf_of_types.lean
- When `A` has limits and there is a functor `s : A => Type` which is faithful, reflects isomorphisms and preserves limits, then `P : C^op => A` is a sheaf iff the underlying presheaf of types `P >>> s : C^op => Type` is a sheaf. (cf https://stacks.math.columbia.edu/tag/0073, which is a weaker version of this statement (it's only over spaces, not sites) and https://stacks.math.columbia.edu/tag/00YR (a), which additionally assumes filtered colimits).
A couple of questions for reviewers:
- We've now got a ton of equivalent ways of showing something's a sheaf, and it's not the easiest to navigate between them. Is there a nice way around this? I think it's still valuable to have all the ways, since each can be helpful in different contexts but it makes the API a bit opaque. There's also a bit of inconsistency - there's a definition `yoneda_sheaf_condition` which is the same as `is_sheaf_for` but the equalizer conditions at the bottom of sheaf_of_types aren't named, they're just some `nonempty (is_limit (fork.of_ι _ (w P R)))` even though they're also equivalent.
- The name `presieve.is_sheaf` is stupid, I think I was just lazy with namespaces. I think `presieve.family_of_elements` and `presieve.is_sheaf_for` are still sensible, since they are relative to a presieve, but `is_sheaf` doesn't have any reference to presieves in its type. 
- The equalizer condition of sheaves of types is definitionally the same as the equalizer condition for sheaves of structures, so is there any point in having the former version in the library - the latter is just more general (the same doesn't apply to the actual def of sheaves of structures since that's defined in terms of sheaves of types). The main downside I can see is that it might make the proofs of `equalizer_sheaf_condition` a bit trickier, but that's about it
#### Estimated changes
Added src/category_theory/sites/sheaf.lean
- \+ *def* category_theory.Sheaf
- \+ *def* category_theory.Sheaf_equiv_SheafOfTypes
- \+ *def* category_theory.Sheaf_to_presheaf
- \+ *lemma* category_theory.is_sheaf_iff_is_sheaf_of_type
- \+ *def* category_theory.presheaf.first_map
- \+ *def* category_theory.presheaf.first_obj
- \+ *def* category_theory.presheaf.fork_map
- \+ *def* category_theory.presheaf.is_sheaf'
- \+ *def* category_theory.presheaf.is_sheaf
- \+ *def* category_theory.presheaf.is_sheaf_for_is_sheaf_for'
- \+ *theorem* category_theory.presheaf.is_sheaf_iff_is_sheaf'
- \+ *lemma* category_theory.presheaf.is_sheaf_iff_is_sheaf_forget
- \+ *def* category_theory.presheaf.second_map
- \+ *def* category_theory.presheaf.second_obj
- \+ *lemma* category_theory.presheaf.w

Modified src/category_theory/sites/sheaf_of_types.lean


Modified src/category_theory/sites/sieves.lean
- \+ *lemma* category_theory.sieve.generate_sieve



## [2021-04-30 05:44:03](https://github.com/leanprover-community/mathlib/commit/f36cc16)
chore(topology/category): some lemmas for Profinite functions ([#7414](https://github.com/leanprover-community/mathlib/pull/7414))
Adds `concrete_category`  and `has_forget₂` instances for Profinite, and `id_app` and `comp_app` lemmas.
#### Estimated changes
Modified src/topology/category/Profinite.lean
- \+ *lemma* Profinite.coe_comp
- \+ *lemma* Profinite.coe_id
- \+/\- *def* Profinite_to_Top



## [2021-04-30 05:44:02](https://github.com/leanprover-community/mathlib/commit/c914e8f)
refactor(data/fin): define neg like sub ([#7408](https://github.com/leanprover-community/mathlib/pull/7408))
Define negation on fin in the same way as subtraction, i.e., using nat.mod (instead of computing it in the integers).
#### Estimated changes
Modified src/data/fin.lean
- \+/\- *lemma* fin.cast_pred_one



## [2021-04-30 05:44:01](https://github.com/leanprover-community/mathlib/commit/39a1cf0)
feat(group/hom_instances): add composition operators ([#7407](https://github.com/leanprover-community/mathlib/pull/7407))
This adds the analogous definitions to those we have for `linear_map`, namely:
* `monoid_hom.comp_hom'` (c.f. `linear_map.lcomp`, `l` = `linear`)
* `monoid_hom.compl₂` (c.f. `linear_map.compl₂`, `l` = `left`)
* `monoid_hom.compr₂` (c.f. `linear_map.compr₂`, `r` = `right`)
We already have `monoid_hom.comp_hom` (c.f. `linear_map.llcomp`, `ll` = `linear linear`)
It also adds an `ext_iff₂` lemma, which is occasionally useful (but not present for any other time at the moment).
The order of definitions in the file has been shuffled slightly to permit addition of a subheading to group things in doc-gen
#### Estimated changes
Modified src/algebra/group/hom_instances.lean
- \+ *lemma* add_monoid_hom.map_mul_iff
- \+ *def* monoid_hom.comp_hom'
- \+ *def* monoid_hom.compl₂
- \+ *lemma* monoid_hom.compl₂_apply
- \+ *def* monoid_hom.compr₂
- \+ *lemma* monoid_hom.compr₂_apply
- \+ *lemma* monoid_hom.ext_iff₂



## [2021-04-30 00:14:20](https://github.com/leanprover-community/mathlib/commit/413b426)
feat(finset/basic): fill in holes in the finset API ([#7386](https://github.com/leanprover-community/mathlib/pull/7386))
add basic lemmas about finsets
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.attach_eq_empty_iff
- \+ *lemma* finset.attach_nonempty_iff
- \+ *lemma* finset.eq_empty_of_ssubset_singleton
- \+ *lemma* finset.exists_of_ssubset
- \+ *lemma* finset.ssubset_of_ssubset_of_subset
- \+ *lemma* finset.ssubset_of_subset_of_ssubset
- \+ *lemma* finset.ssubset_singleton_iff
- \+ *lemma* finset.subset_inter_iff
- \+ *lemma* finset.subset_singleton_iff
- \+ *lemma* finset.union_subset_iff
- \+/\- *lemma* finset.union_subset_union

Modified src/data/set/basic.lean
- \+ *lemma* set.diff_union_of_subset
- \+ *lemma* set.eq_empty_of_ssubset_singleton
- \+ *lemma* set.ssubset_of_ssubset_of_subset
- \+ *lemma* set.ssubset_of_subset_of_ssubset
- \+ *lemma* set.ssubset_singleton_iff
- \+ *lemma* set.subset_singleton_iff_eq



## [2021-04-29 23:00:13](https://github.com/leanprover-community/mathlib/commit/6a796d0)
refactor(algebraic_geometry/structure_sheaf): Remove redundant isomorphism ([#7410](https://github.com/leanprover-community/mathlib/pull/7410))
Removes `stalk_iso_Type`, which is redundant since we also have `structure_sheaf.stalk_iso`, which is the same isomorphism in `CommRing`
#### Estimated changes
Modified src/algebraic_geometry/structure_sheaf.lean
- \- *def* algebraic_geometry.stalk_iso_Type
- \- *lemma* algebraic_geometry.structure_sheaf_stalk_to_fiber_injective
- \- *lemma* algebraic_geometry.structure_sheaf_stalk_to_fiber_surjective



## [2021-04-29 14:43:39](https://github.com/leanprover-community/mathlib/commit/ca5176c)
feat(linear_algebra/tensor_product): add definition `tensor_product.map_incl` and `simp` lemmas related to powers of `tensor_product.map` ([#7406](https://github.com/leanprover-community/mathlib/pull/7406))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.id_pow

Modified src/linear_algebra/tensor_product.lean
- \+/\- *lemma* linear_map.ltensor_id
- \+ *lemma* linear_map.ltensor_pow
- \+/\- *lemma* linear_map.rtensor_id
- \+ *lemma* linear_map.rtensor_pow
- \+ *lemma* tensor_product.map_id
- \+ *def* tensor_product.map_incl
- \+ *lemma* tensor_product.map_mul
- \+ *lemma* tensor_product.map_one
- \+ *lemma* tensor_product.map_pow



## [2021-04-29 14:43:38](https://github.com/leanprover-community/mathlib/commit/966b3b1)
feat(set_theory/{surreal, pgame}): `mul_comm` for surreal numbers  ([#7376](https://github.com/leanprover-community/mathlib/pull/7376))
This PR adds a proof of commutativity of multiplication for surreal numbers. 
We also add `mul_zero` and `zero_mul` along with several useful lemmas.
Finally, this renames a handful of lemmas about `relabelling` in order to enable dot notation.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers)
#### Estimated changes
Modified src/set_theory/game/impartial.lean


Modified src/set_theory/pgame.lean
- \- *theorem* pgame.equiv_of_relabelling
- \- *theorem* pgame.le_of_relabelling
- \- *theorem* pgame.le_of_restricted
- \+ *def* pgame.relabelling.add_congr
- \+ *theorem* pgame.relabelling.equiv
- \+ *theorem* pgame.relabelling.le
- \+ *def* pgame.relabelling.neg_congr
- \+ *def* pgame.relabelling.restricted:
- \+ *def* pgame.relabelling.sub_congr
- \+ *theorem* pgame.restricted.le
- \- *def* pgame.restricted_of_relabelling

Modified src/set_theory/surreal.lean
- \+ *def* pgame.add_comm_sub_relabelling
- \+ *def* pgame.add_sub_relabelling
- \+ *def* pgame.left_moves_mul
- \+ *lemma* pgame.mk_mul_move_left_inl
- \+ *lemma* pgame.mk_mul_move_left_inr
- \+ *lemma* pgame.mk_mul_move_right_inl
- \+ *lemma* pgame.mk_mul_move_right_inr
- \+ *theorem* pgame.mul_comm_equiv
- \+ *def* pgame.mul_comm_relabelling
- \+ *lemma* pgame.mul_move_left_inl
- \+ *lemma* pgame.mul_move_left_inr
- \+ *lemma* pgame.mul_move_right_inl
- \+ *lemma* pgame.mul_move_right_inr
- \+ *theorem* pgame.mul_zero_equiv
- \+ *def* pgame.mul_zero_relabelling
- \+ *def* pgame.right_moves_mul
- \+ *theorem* pgame.zero_mul_equiv
- \+ *def* pgame.zero_mul_relabelling



## [2021-04-29 12:50:46](https://github.com/leanprover-community/mathlib/commit/c956353)
chore(.docker): remove alpine build, too fragile ([#7401](https://github.com/leanprover-community/mathlib/pull/7401))
If this is approved I'll remove the automatic builds of the `alpine` based images over on `hub.docker.com`.
#### Estimated changes
Modified .docker/README.md


Deleted .docker/alpine/lean/.profile


Deleted .docker/alpine/lean/Dockerfile


Deleted .docker/alpine/mathlib/Dockerfile


Modified scripts/docker_build.sh


Modified scripts/docker_push.sh




## [2021-04-29 12:50:45](https://github.com/leanprover-community/mathlib/commit/91604cb)
feat(data/finsupp/to_dfinsupp): add equivalences between finsupp and dfinsupp ([#7311](https://github.com/leanprover-community/mathlib/pull/7311))
A rework of [#7217](https://github.com/leanprover-community/mathlib/pull/7217), that adds a more elementary equivalence.
#### Estimated changes
Added src/data/finsupp/to_dfinsupp.lean
- \+ *def* dfinsupp.to_finsupp
- \+ *lemma* dfinsupp.to_finsupp_add
- \+ *lemma* dfinsupp.to_finsupp_coe
- \+ *lemma* dfinsupp.to_finsupp_neg
- \+ *lemma* dfinsupp.to_finsupp_single
- \+ *lemma* dfinsupp.to_finsupp_smul
- \+ *lemma* dfinsupp.to_finsupp_sub
- \+ *lemma* dfinsupp.to_finsupp_support
- \+ *lemma* dfinsupp.to_finsupp_to_dfinsupp
- \+ *lemma* dfinsupp.to_finsupp_zero
- \+ *def* finsupp.to_dfinsupp
- \+ *lemma* finsupp.to_dfinsupp_add
- \+ *lemma* finsupp.to_dfinsupp_coe
- \+ *lemma* finsupp.to_dfinsupp_neg
- \+ *lemma* finsupp.to_dfinsupp_single
- \+ *lemma* finsupp.to_dfinsupp_smul
- \+ *lemma* finsupp.to_dfinsupp_sub
- \+ *lemma* finsupp.to_dfinsupp_to_finsupp
- \+ *lemma* finsupp.to_dfinsupp_zero
- \+ *def* finsupp_equiv_dfinsupp
- \+ *lemma* to_dfinsupp_support

Modified src/linear_algebra/direct_sum/finsupp.lean




## [2021-04-29 08:23:27](https://github.com/leanprover-community/mathlib/commit/fda4d3d)
feat(data/rat): add `@[simp]` to `rat.num_div_denom` ([#7393](https://github.com/leanprover-community/mathlib/pull/7393))
I have an equation in rational numbers that I want to turn into an equation in integers, and everything `simp`s away nicely except the equation `x.num / x.denom = x`. Marking `rat.num_div_denom` as `simp` should fix that, and I don't expect it will break anything. (`rat.num_denom : rat.mk x.num x.denom = x` is already a `simp` lemma.)
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60x.2Enum.20.2F.20x.2Edenom.20.3D.20x.60
#### Estimated changes
Modified archive/imo/imo2013_q5.lean


Modified src/data/rat/basic.lean


Modified src/number_theory/pythagorean_triples.lean




## [2021-04-28 19:37:48](https://github.com/leanprover-community/mathlib/commit/c50cb7a)
feat(data/fintype/basic): add decidable_eq_(bundled-hom)_fintype ([#7394](https://github.com/leanprover-community/mathlib/pull/7394))
Using the proof of `decidable_eq_equiv_fintype` for guidance, this adds equivalent statements about:
* `function.embedding`
* `zero_hom`
* `one_hom`
* `add_hom`
* `mul_hom`
* `add_monoid_hom`
* `monoid_hom`
* `monoid_with_zero_hom`
* `ring_hom`
It also fixes a typo that swaps `left` and `right` between two definition names.
#### Estimated changes
Modified src/data/fintype/basic.lean




## [2021-04-28 19:37:47](https://github.com/leanprover-community/mathlib/commit/abf1c20)
feat(linear_algebra/free_module): free of finite torsion free ([#7381](https://github.com/leanprover-community/mathlib/pull/7381))
This is a reformulation of module.free_of_finite_type_torsion_free in terms of `ring_theory.finiteness` (combining my recent algebra PRs). Note this adds an import but it seems ok to me.
#### Estimated changes
Modified src/linear_algebra/free_module.lean
- \+ *lemma* module.free_of_finite_type_torsion_free'



## [2021-04-28 19:37:46](https://github.com/leanprover-community/mathlib/commit/b9c80c9)
chore(*): use `sq` as convention for "squared" ([#7368](https://github.com/leanprover-community/mathlib/pull/7368))
This PR establishes `sq x` as the notation for `x ^ 2`. See [this Zulip conversation](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/sqr.20vs.20sq.20vs.20pow_two/near/224972795).
A breakdown of the refactor:
- All instances of `square` and `sqr` are changed to `sq` (except where `square` means something other than "to the second power")
- All instances of `pow_two` are changed to `sq`, though many are kept are aliases
- All instances of `sum_of_two_squares` are changed to `sq_add_sq`
n.b. I did NOT alter any instances of:
- `squarefree`
- `sum_of_four_squares`
- `fpow_two` or `rpow_two`
<!-- The text above the `
#### Estimated changes
Modified archive/100-theorems-list/57_herons_formula.lean


Modified archive/100-theorems-list/70_perfect_numbers.lean
- \- *lemma* nat.eq_pow_two_mul_odd
- \+ *lemma* nat.eq_two_pow_mul_odd

Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified archive/100-theorems-list/9_area_of_a_circle.lean


Modified archive/imo/imo1962_q4.lean


Modified archive/imo/imo1981_q3.lean


Modified archive/imo/imo1988_q6.lean


Modified archive/imo/imo2001_q2.lean


Modified archive/imo/imo2005_q3.lean


Modified archive/imo/imo2008_q2.lean


Modified archive/imo/imo2008_q3.lean


Modified archive/imo/imo2008_q4.lean


Modified docs/100.yaml


Modified docs/overview.yaml


Modified src/algebra/group_power/basic.lean
- \+ *theorem* abs_le_abs_of_sq_le_sq
- \- *theorem* abs_le_abs_of_sqr_le_sqr
- \+ *theorem* abs_le_of_sq_le_sq'
- \+ *theorem* abs_le_of_sq_le_sq
- \- *theorem* abs_le_of_sqr_le_sqr'
- \- *theorem* abs_le_of_sqr_le_sqr
- \+ *theorem* abs_lt_abs_of_sq_lt_sq
- \- *theorem* abs_lt_abs_of_sqr_lt_sqr
- \+ *theorem* abs_lt_of_sq_lt_sq'
- \+ *theorem* abs_lt_of_sq_lt_sq
- \- *theorem* abs_lt_of_sqr_lt_sqr'
- \- *theorem* abs_lt_of_sqr_lt_sqr
- \+ *theorem* abs_sq
- \- *theorem* abs_sqr
- \- *lemma* add_pow_two
- \+ *lemma* add_sq
- \- *lemma* eq_of_pow_two_eq_pow_two
- \+ *lemma* eq_of_sq_eq_sq
- \- *lemma* eq_or_eq_neg_of_pow_two_eq_pow_two
- \+ *lemma* eq_or_eq_neg_of_sq_eq_sq
- \+ *lemma* neg_sq
- \- *lemma* neg_square
- \- *theorem* pow_two_nonneg
- \- *theorem* pow_two_pos_of_ne_zero
- \- *lemma* pow_two_sub_pow_two
- \+ *theorem* sq_abs
- \+ *theorem* sq_le_sq'
- \+ *theorem* sq_le_sq
- \+ *theorem* sq_lt_sq'
- \+ *theorem* sq_lt_sq
- \+ *theorem* sq_nonneg
- \+ *theorem* sq_pos_of_ne_zero
- \+ *lemma* sq_sub_sq
- \- *theorem* sq_sub_sq
- \- *theorem* sqr_abs
- \- *theorem* sqr_le_sqr'
- \- *theorem* sqr_le_sqr
- \- *theorem* sqr_lt_sqr'
- \- *theorem* sqr_lt_sqr
- \- *lemma* sub_pow_two
- \+ *lemma* sub_sq
- \- *lemma* two_mul_le_add_pow_two
- \+ *lemma* two_mul_le_add_sq

Modified src/algebra/group_power/identities.lean
- \- *theorem* pow_two_add_mul_pow_two_mul_pow_two_add_mul_pow_two
- \- *theorem* pow_two_add_pow_two_mul_pow_two_add_pow_two
- \+ *theorem* sq_add_mul_sq_mul_sq_add_mul_sq
- \+ *theorem* sq_add_sq_mul_sq_add_sq

Modified src/algebra/group_power/lemmas.lean
- \- *lemma* int.abs_le_self_pow_two
- \+ *lemma* int.abs_le_self_sq
- \- *lemma* int.le_self_pow_two
- \+ *lemma* int.le_self_sq
- \- *lemma* int.nat_abs_pow_two
- \+ *lemma* int.nat_abs_sq
- \- *lemma* int.units_pow_two
- \+ *lemma* int.units_sq
- \+/\- *theorem* one_add_mul_le_pow'

Modified src/algebra/group_with_zero/power.lean


Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/ordered_ring.lean
- \+ *lemma* abs_sub_sq
- \- *lemma* abs_sub_square
- \+ *lemma* nonneg_le_nonneg_of_sq_le_sq
- \- *lemma* nonneg_le_nonneg_of_squares_le

Modified src/algebra/quadratic_discriminant.lean
- \+ *lemma* quadratic_eq_zero_iff_discrim_eq_sq
- \- *lemma* quadratic_eq_zero_iff_discrim_eq_square
- \+ *lemma* quadratic_ne_zero_of_discrim_ne_sq
- \- *lemma* quadratic_ne_zero_of_discrim_ne_square

Modified src/algebra/squarefree.lean


Modified src/algebra/star/chsh.lean


Modified src/analysis/analytic/inverse.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* differentiable.norm_sq
- \- *lemma* differentiable.norm_square
- \+ *lemma* differentiable_at.norm_sq
- \- *lemma* differentiable_at.norm_square
- \+ *lemma* differentiable_on.norm_sq
- \- *lemma* differentiable_on.norm_square
- \+ *lemma* differentiable_within_at.norm_sq
- \- *lemma* differentiable_within_at.norm_square
- \+ *lemma* inner_product_space.of_core.inner_self_eq_norm_sq
- \- *lemma* inner_product_space.of_core.inner_self_eq_norm_square
- \+ *lemma* inner_self_eq_norm_sq
- \- *lemma* inner_self_eq_norm_square
- \- *lemma* norm_add_pow_two
- \- *lemma* norm_add_pow_two_real
- \+ *lemma* norm_add_sq
- \+ *lemma* norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
- \+ *lemma* norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
- \+ *lemma* norm_add_sq_eq_norm_sq_add_norm_sq_real
- \+ *lemma* norm_add_sq_real
- \- *lemma* norm_add_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero
- \- *lemma* norm_add_square_eq_norm_square_add_norm_square_of_inner_eq_zero
- \- *lemma* norm_add_square_eq_norm_square_add_norm_square_real
- \- *lemma* norm_sub_pow_two
- \- *lemma* norm_sub_pow_two_real
- \+ *lemma* norm_sub_sq
- \+ *lemma* norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
- \+ *lemma* norm_sub_sq_eq_norm_sq_add_norm_sq_real
- \+ *lemma* norm_sub_sq_real
- \- *lemma* norm_sub_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero
- \- *lemma* norm_sub_square_eq_norm_square_add_norm_square_real
- \+ *lemma* real_inner_self_eq_norm_sq
- \- *lemma* real_inner_self_eq_norm_square
- \+ *lemma* times_cont_diff.norm_sq
- \- *lemma* times_cont_diff.norm_square
- \+ *lemma* times_cont_diff_at.norm_sq
- \- *lemma* times_cont_diff_at.norm_square
- \+ *lemma* times_cont_diff_norm_sq
- \- *lemma* times_cont_diff_norm_square
- \+ *lemma* times_cont_diff_on.norm_sq
- \- *lemma* times_cont_diff_on.norm_square
- \+ *lemma* times_cont_diff_within_at.norm_sq
- \- *lemma* times_cont_diff_within_at.norm_square

Modified src/analysis/quaternion.lean
- \+ *lemma* quaternion.norm_sq_eq_norm_sq
- \- *lemma* quaternion.norm_sq_eq_norm_square

Modified src/analysis/special_functions/arsinh.lean


Modified src/analysis/special_functions/bernstein.lean


Modified src/analysis/special_functions/integrals.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/sqrt.lean


Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* real.sin_sq_pi_over_two_pow
- \+ *lemma* real.sin_sq_pi_over_two_pow_succ
- \- *lemma* real.sin_square_pi_over_two_pow
- \- *lemma* real.sin_square_pi_over_two_pow_succ
- \+ *lemma* real.sq_cos_pi_div_six
- \+ *lemma* real.sq_sin_pi_div_three
- \- *lemma* real.square_cos_pi_div_six
- \- *lemma* real.square_sin_pi_div_three

Modified src/analysis/specific_limits.lean


Modified src/combinatorics/colex.lean
- \- *lemma* colex.sum_pow_two_lt_iff_lt
- \+ *lemma* colex.sum_sq_lt_iff_lt
- \- *lemma* nat.sum_pow_two_lt
- \+ *lemma* nat.sum_sq_lt

Modified src/data/complex/basic.lean
- \+/\- *lemma* complex.I_sq

Modified src/data/complex/exponential.lean
- \+ *lemma* complex.cos_sq'
- \+ *lemma* complex.cos_sq
- \- *lemma* complex.cos_square'
- \- *lemma* complex.cos_square
- \+ *lemma* complex.cosh_sq
- \- *lemma* complex.cosh_square
- \+ *lemma* complex.sin_sq
- \- *lemma* complex.sin_square
- \+ *lemma* complex.sinh_sq
- \- *lemma* complex.sinh_square
- \+ *lemma* real.cos_sq'
- \+ *lemma* real.cos_sq
- \- *lemma* real.cos_square'
- \- *lemma* real.cos_square
- \+ *lemma* real.cosh_sq
- \- *lemma* real.cosh_square
- \+ *lemma* real.sin_sq
- \- *lemma* real.sin_square
- \+ *lemma* real.sinh_sq
- \- *lemma* real.sinh_square

Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* is_R_or_C.abs_sq_re_add_conj'
- \+ *lemma* is_R_or_C.abs_sq_re_add_conj
- \- *lemma* is_R_or_C.abs_sqr_re_add_conj'
- \- *lemma* is_R_or_C.abs_sqr_re_add_conj
- \+/\- *lemma* is_R_or_C.norm_sq_to_real

Modified src/data/int/basic.lean


Modified src/data/int/gcd.lean
- \- *lemma* int.prime.dvd_nat_abs_of_coe_dvd_pow_two
- \+ *lemma* int.prime.dvd_nat_abs_of_coe_dvd_sq

Modified src/data/nat/basic.lean
- \- *theorem* nat.pow_two_sub_pow_two
- \+ *theorem* nat.sq_sub_sq

Modified src/data/nat/parity.lean
- \- *theorem* nat.neg_one_pow_two
- \+ *theorem* nat.neg_one_sq

Modified src/data/nat/prime.lean
- \- *lemma* nat.prime.mul_eq_prime_pow_two_iff
- \+ *lemma* nat.prime.mul_eq_prime_sq_iff

Modified src/data/padics/hensel.lean


Modified src/data/quaternion.lean


Modified src/data/real/golden_ratio.lean


Modified src/data/real/irrational.lean


Modified src/data/real/pi.lean


Modified src/data/real/sqrt.lean
- \+ *lemma* nnreal.sqrt_eq_iff_sq_eq
- \- *lemma* nnreal.sqrt_eq_iff_sqr_eq
- \+/\- *lemma* nnreal.sqrt_one
- \+ *theorem* real.le_sqrt_of_sq_le
- \- *theorem* real.le_sqrt_of_sqr_le
- \+ *theorem* real.lt_sqrt_of_sq_lt
- \- *theorem* real.lt_sqrt_of_sqr_lt
- \+ *theorem* real.neg_sqrt_le_of_sq_le
- \- *theorem* real.neg_sqrt_le_of_sqr_le
- \+ *theorem* real.neg_sqrt_lt_of_sq_lt
- \- *theorem* real.neg_sqrt_lt_of_sqr_lt
- \+ *theorem* real.sq_le
- \+ *theorem* real.sq_lt
- \+ *theorem* real.sq_sqrt
- \- *theorem* real.sqr_le
- \- *theorem* real.sqr_lt
- \- *theorem* real.sqr_sqrt
- \+ *theorem* real.sqrt_eq_iff_sq_eq
- \- *theorem* real.sqrt_eq_iff_sqr_eq
- \+ *theorem* real.sqrt_sq
- \+ *theorem* real.sqrt_sq_eq_abs
- \- *theorem* real.sqrt_sqr
- \- *theorem* real.sqrt_sqr_eq_abs

Modified src/data/zsqrtd/basic.lean
- \+ *theorem* zsqrtd.not_divides_sq
- \- *theorem* zsqrtd.not_divides_square

Modified src/data/zsqrtd/gaussian_int.lean
- \+ *lemma* gaussian_int.sq_add_sq_of_nat_prime_of_not_irreducible
- \- *lemma* gaussian_int.sum_two_squares_of_nat_prime_of_not_irreducible

Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/field_theory/finite/basic.lean
- \+ *lemma* char_p.sq_add_sq
- \- *lemma* char_p.sum_two_squares
- \+ *lemma* zmod.sq_add_sq
- \- *lemma* zmod.sum_two_squares

Modified src/field_theory/separable.lean


Modified src/geometry/euclidean/basic.lean
- \+ *lemma* euclidean_geometry.dist_smul_vadd_sq
- \- *lemma* euclidean_geometry.dist_smul_vadd_square
- \+ *lemma* euclidean_geometry.dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq
- \+ *lemma* euclidean_geometry.dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd
- \- *lemma* euclidean_geometry.dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
- \- *lemma* euclidean_geometry.dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd

Modified src/geometry/euclidean/circumcenter.lean


Modified src/geometry/euclidean/sphere.lean


Modified src/geometry/euclidean/triangle.lean
- \+ *lemma* euclidean_geometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two
- \+ *lemma* euclidean_geometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
- \- *lemma* euclidean_geometry.dist_square_eq_dist_square_add_dist_square_iff_angle_eq_pi_div_two
- \- *lemma* euclidean_geometry.dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle
- \+ *lemma* inner_product_geometry.norm_add_sq_eq_norm_sq_add_norm_sq'
- \+ *lemma* inner_product_geometry.norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two
- \- *lemma* inner_product_geometry.norm_add_square_eq_norm_square_add_norm_square'
- \- *lemma* inner_product_geometry.norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \+ *lemma* inner_product_geometry.norm_sub_sq_eq_norm_sq_add_norm_sq'
- \+ *lemma* inner_product_geometry.norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two
- \+ *lemma* inner_product_geometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
- \- *lemma* inner_product_geometry.norm_sub_square_eq_norm_square_add_norm_square'
- \- *lemma* inner_product_geometry.norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \- *lemma* inner_product_geometry.norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle

Modified src/geometry/manifold/instances/sphere.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/specific_groups/dihedral.lean


Modified src/group_theory/specific_groups/quaternion.lean
- \- *lemma* quaternion_group.xa_pow_two
- \+ *lemma* quaternion_group.xa_sq

Modified src/linear_algebra/clifford_algebra/basic.lean
- \+ *theorem* clifford_algebra.comp_ι_sq_scalar
- \- *theorem* clifford_algebra.comp_ι_square_scalar
- \+ *theorem* clifford_algebra.ι_sq_scalar
- \- *theorem* clifford_algebra.ι_square_scalar

Modified src/linear_algebra/exterior_algebra.lean
- \+ *theorem* exterior_algebra.comp_ι_sq_zero
- \- *theorem* exterior_algebra.comp_ι_square_zero
- \+ *theorem* exterior_algebra.ι_sq_zero
- \- *theorem* exterior_algebra.ι_square_zero

Modified src/measure_theory/l2_space.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/fermat4.lean
- \+ *lemma* int.coprime_of_sq_sum'
- \+ *lemma* int.coprime_of_sq_sum
- \- *lemma* int.coprime_of_sqr_sum'
- \- *lemma* int.coprime_of_sqr_sum

Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/number_theory/quadratic_reciprocity.lean
- \- *lemma* zmod.exists_pow_two_eq_neg_one_iff_mod_four_ne_three
- \- *lemma* zmod.exists_pow_two_eq_prime_iff_of_mod_four_eq_one
- \- *lemma* zmod.exists_pow_two_eq_prime_iff_of_mod_four_eq_three
- \- *lemma* zmod.exists_pow_two_eq_two_iff
- \+ *lemma* zmod.exists_sq_eq_neg_one_iff_mod_four_ne_three
- \+ *lemma* zmod.exists_sq_eq_prime_iff_of_mod_four_eq_one
- \+ *lemma* zmod.exists_sq_eq_prime_iff_of_mod_four_eq_three
- \+ *lemma* zmod.exists_sq_eq_two_iff

Modified src/number_theory/sum_four_squares.lean
- \+ *lemma* int.exists_sq_add_sq_add_one_eq_k
- \- *lemma* int.exists_sum_two_squares_add_one_eq_k
- \+ *lemma* int.sq_add_sq_of_two_mul_sq_add_sq
- \- *lemma* int.sum_two_squares_of_two_mul_sum_two_squares

Modified src/number_theory/sum_two_squares.lean
- \+ *lemma* nat.prime.sq_add_sq
- \- *lemma* nat.prime.sum_two_squares

Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/int/basic.lean
- \+ *lemma* int.sq_of_coprime
- \+ *lemma* int.sq_of_gcd_eq_one
- \- *lemma* int.sqr_of_coprime
- \- *lemma* int.sqr_of_gcd_eq_one

Modified src/ring_theory/polynomial/chebyshev.lean
- \- *lemma* polynomial.chebyshev.one_sub_X_pow_two_mul_U_eq_pol_in_T
- \- *lemma* polynomial.chebyshev.one_sub_X_pow_two_mul_derivative_T_eq_poly_in_T
- \+ *lemma* polynomial.chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T
- \+ *lemma* polynomial.chebyshev.one_sub_X_sq_mul_derivative_T_eq_poly_in_T

Modified src/ring_theory/polynomial/cyclotomic.lean


Modified src/ring_theory/polynomial/dickson.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/tactic/linarith/preprocessing.lean


Modified test/linarith.lean




## [2021-04-28 19:37:44](https://github.com/leanprover-community/mathlib/commit/2401d99)
feat(group_theory/finiteness): add group.fg ([#7338](https://github.com/leanprover-community/mathlib/pull/7338))
Basic facts about finitely generated groups.
- [x] depends on: [#7279](https://github.com/leanprover-community/mathlib/pull/7279)
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *theorem* submodule.to_add_subgroup_eq

Modified src/algebra/pointwise.lean
- \+ *lemma* set.finite.inv

Modified src/group_theory/finiteness.lean
- \+ *lemma* add_group.fg_def
- \+ *lemma* add_group.fg_iff_mul_fg
- \+ *lemma* add_subgroup.fg_iff_mul_fg
- \+ *lemma* group.fg_def
- \+ *lemma* group.fg_iff
- \+ *lemma* group.fg_iff_monoid.fg
- \+ *lemma* group_fg.iff_add_fg
- \+ *def* subgroup.fg
- \+ *lemma* subgroup.fg_iff
- \+ *lemma* subgroup.fg_iff_add_fg
- \+ *lemma* subgroup.fg_iff_submonoid_fg

Modified src/group_theory/subgroup.lean
- \+ *theorem* subgroup.to_submonoid_eq
- \+ *theorem* subgroup.to_submonoid_injective
- \+ *lemma* subgroup.to_submonoid_le
- \+ *lemma* subgroup.to_submonoid_mono
- \+ *lemma* subgroup.to_submonoid_strict_mono

Modified src/ring_theory/finiteness.lean
- \+ *lemma* module.finite.iff_add_group_fg
- \+ *lemma* module.finite.iff_add_monoid_fg
- \+/\- *lemma* module.finite_def

Modified src/ring_theory/noetherian.lean
- \+ *lemma* submodule.fg_iff_add_subgroup_fg



## [2021-04-28 19:37:43](https://github.com/leanprover-community/mathlib/commit/4328cc3)
feat(topology/continuous_function): abstract statement of Weierstrass approximation ([#7303](https://github.com/leanprover-community/mathlib/pull/7303))
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \- *theorem* algebra.coe_top
- \+ *theorem* algebra.top_to_submodule
- \+ *theorem* algebra.top_to_subsemiring
- \+ *lemma* subalgebra.coe_comap
- \+ *lemma* subalgebra.mem_comap

Modified src/data/set_like.lean


Modified src/field_theory/normal.lean


Modified src/field_theory/splitting_field.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/ring_theory/adjoin/basic.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/topology/algebra/algebra.lean
- \+ *lemma* subalgebra.topological_closure_coe
- \+ *lemma* subalgebra.topological_closure_comap'_homeomorph

Modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* continuous_map.subsingleton_subalgebra

Modified src/topology/continuous_function/basic.lean
- \+ *lemma* continuous_map.ext_iff

Modified src/topology/continuous_function/polynomial.lean
- \+ *lemma* polynomial.aeval_continuous_map_apply
- \+ *def* polynomial.to_continuous_map_alg_hom
- \+ *def* polynomial.to_continuous_map_on_alg_hom
- \+ *lemma* polynomial_functions.comap'_comp_right_alg_hom_Icc_homeo_I
- \+ *def* polynomial_functions
- \+ *lemma* polynomial_functions_coe
- \+ *lemma* polynomial_functions_separates_points

Added src/topology/continuous_function/weierstrass.lean
- \+ *theorem* continuous_map_mem_polynomial_functions_closure
- \+ *theorem* exists_polynomial_near_continuous_map
- \+ *theorem* exists_polynomial_near_of_continuous_on
- \+ *theorem* polynomial_functions_closure_eq_top'
- \+ *theorem* polynomial_functions_closure_eq_top



## [2021-04-28 14:47:13](https://github.com/leanprover-community/mathlib/commit/e6a4c81)
chore(algebra/module/submodule): mem_to_add_subgroup ([#7392](https://github.com/leanprover-community/mathlib/pull/7392))
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *lemma* submodule.mem_to_add_subgroup



## [2021-04-28 14:47:12](https://github.com/leanprover-community/mathlib/commit/052447d)
feat(algebra/group/hom_instance): add add_monoid_hom.mul ([#7382](https://github.com/leanprover-community/mathlib/pull/7382))
#### Estimated changes
Modified src/algebra/group/hom_instances.lean
- \+ *lemma* add_monoid_hom.coe_flip_mul
- \+ *lemma* add_monoid_hom.coe_mul
- \+ *def* add_monoid_hom.mul
- \+ *lemma* add_monoid_hom.mul_apply



## [2021-04-28 13:06:40](https://github.com/leanprover-community/mathlib/commit/a1b695a)
feat(algbera/lie/submodule): add `simp` lemmas `lie_submodule.map_sup`, `lie_ideal.map_sup` ([#7384](https://github.com/leanprover-community/mathlib/pull/7384))
#### Estimated changes
Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_ideal.map_sup
- \+/\- *def* lie_submodule.comap
- \+/\- *lemma* lie_submodule.gc_map_comap
- \+/\- *def* lie_submodule.map
- \+/\- *lemma* lie_submodule.map_le_iff_le_comap
- \+ *lemma* lie_submodule.map_sup
- \+/\- *lemma* lie_submodule.mem_map



## [2021-04-28 09:40:47](https://github.com/leanprover-community/mathlib/commit/105935c)
feat(linear_algebra/finite_dimensional): characterizations of finrank = 1 and ≤ 1 ([#7354](https://github.com/leanprover-community/mathlib/pull/7354))
#### Estimated changes
Modified src/linear_algebra/affine_space/independent.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.span_singleton_eq_top_iff

Modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis_singleton_iff

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.exists_is_basis_singleton
- \+/\- *lemma* finite_dimensional.finrank_zero_of_subsingleton
- \+ *lemma* finrank_eq_one
- \+ *lemma* finrank_eq_one_iff'
- \+ *lemma* finrank_eq_one_iff
- \+ *lemma* finrank_eq_one_iff_of_nonzero
- \+ *lemma* finrank_le_one
- \+ *lemma* finrank_le_one_iff
- \+ *lemma* singleton_is_basis

Modified src/linear_algebra/linear_independent.lean
- \+/\- *lemma* linear_independent_unique_iff



## [2021-04-28 06:27:58](https://github.com/leanprover-community/mathlib/commit/f952dd1)
refactor(algebra/big_operators/finprod, ring_theory/hahn_series): summable families now use `finsum` ([#7388](https://github.com/leanprover-community/mathlib/pull/7388))
Adds a few `finprod/finsum` lemmas
Uses them to refactor `hahn_series.summable_family` to use `finsum`
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_prod_comm
- \+ *lemma* finsum_mul
- \+ *lemma* mul_finsum
- \+ *lemma* prod_finprod_comm

Modified src/ring_theory/hahn_series.lean
- \- *lemma* hahn_series.summable_family.co_support_add_subset
- \- *lemma* hahn_series.summable_family.co_support_of_finsupp
- \+ *lemma* hahn_series.summable_family.finite_co_support
- \- *lemma* hahn_series.summable_family.mem_co_support



## [2021-04-28 01:28:28](https://github.com/leanprover-community/mathlib/commit/db89082)
chore(.): remove stray file ([#7390](https://github.com/leanprover-community/mathlib/pull/7390))
I accidentally committed a stray pdf file generated by `leanproject import-graph` during [#7250](https://github.com/leanprover-community/mathlib/pull/7250), and it accidentally got merged into master!
#### Estimated changes
Deleted i.pdf




## [2021-04-28 01:28:27](https://github.com/leanprover-community/mathlib/commit/97118b4)
fix(algebra/group/commute): use the right typeclass ([#7389](https://github.com/leanprover-community/mathlib/pull/7389))
This section is called `mul_one_class`, but I forgot to actually make it use `mul_one_class` instead of `monoid` in a previous PR...
#### Estimated changes
Modified src/algebra/group/commute.lean




## [2021-04-28 01:28:26](https://github.com/leanprover-community/mathlib/commit/d40a60c)
feat(logic/embedding): add function.embedding.coe_injective ([#7383](https://github.com/leanprover-community/mathlib/pull/7383))
Prior art for this lemma name: `linear_map.coe_injective`
#### Estimated changes
Modified src/logic/embedding.lean
- \+ *lemma* function.embedding.coe_injective



## [2021-04-27 20:07:51](https://github.com/leanprover-community/mathlib/commit/c562caf)
fix(tactic/itauto): reset after or split ([#7387](https://github.com/leanprover-community/mathlib/pull/7387))
Fixes a bug [reported on zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.60ring.60.20tactic.20for.20types/near/236368947)
#### Estimated changes
Modified src/tactic/itauto.lean


Modified test/itauto.lean




## [2021-04-27 20:07:50](https://github.com/leanprover-community/mathlib/commit/a24d480)
chore(.docker): fix alpine docker build ([#7374](https://github.com/leanprover-community/mathlib/pull/7374))
A dependency for building mathlibtools had gained a requirement of having `make` available, so we install that.
This doesn't affect the produced image, and we only install `make` in an intermediate image.
#### Estimated changes
Modified .docker/alpine/lean/Dockerfile




## [2021-04-27 20:07:49](https://github.com/leanprover-community/mathlib/commit/1ff56a0)
feat(analysis/analytic): a few lemmas about summability and radius ([#7365](https://github.com/leanprover-community/mathlib/pull/7365))
This PR adds a few lemmas relating the radius of a formal multilinear series `p` to the summability of `Σ ∥pₙ∥ ∥y∥ⁿ` (in both ways). There isn't anything incredibly new as these are mostly special cases of existing lemmas, but I think they could be simpler to find and use. I also modified the docstring of `formal_multilinear_series.radius` to emphasize the difference between "`Σ pₙ yⁿ`converges" and "`Σ ∥pₙ∥ ∥y∥ⁿ` converges".
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+ *lemma* formal_multilinear_series.le_radius_of_summable_norm
- \+ *lemma* formal_multilinear_series.le_radius_of_tendsto
- \+ *lemma* formal_multilinear_series.not_summable_norm_of_radius_lt_nnnorm
- \+ *lemma* formal_multilinear_series.radius_eq_top_iff_summable_norm
- \+/\- *lemma* formal_multilinear_series.radius_eq_top_of_eventually_eq_zero
- \+/\- *lemma* formal_multilinear_series.radius_eq_top_of_forall_image_add_eq_zero
- \+ *lemma* formal_multilinear_series.radius_eq_top_of_summable_norm
- \+ *lemma* formal_multilinear_series.summable_norm_of_lt_radius
- \+ *lemma* formal_multilinear_series.summable_of_nnnorm_lt_radius



## [2021-04-27 15:04:08](https://github.com/leanprover-community/mathlib/commit/5247d00)
feat(algebra/group_with_zero): add semigroup_with_zero ([#7346](https://github.com/leanprover-community/mathlib/pull/7346))
Split from [#6786](https://github.com/leanprover-community/mathlib/pull/6786). By putting the new typeclass _before_ `mul_zero_one_class`, it doesn't need any annotations on `zero_ne_one` as the original PR did.
#### Estimated changes
Modified src/algebra/group/pi.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/group_with_zero/basic.lean


Modified src/algebra/group_with_zero/defs.lean


Modified src/algebra/monoid_algebra.lean


Modified src/algebra/ordered_monoid.lean


Modified src/algebra/pointwise.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/finsupp/pointwise.lean


Modified src/topology/locally_constant/algebra.lean




## [2021-04-27 15:04:06](https://github.com/leanprover-community/mathlib/commit/78a20ff)
feat(data/buffer/parser/basic): nat_eq_done ([#6340](https://github.com/leanprover-community/mathlib/pull/6340))
The `nat` parser gives the maximal possible numeral.
#### Estimated changes
Modified src/data/buffer/parser/basic.lean
- \+ *lemma* parser.nat_eq_done
- \+ *lemma* parser.nat_of_done
- \+ *lemma* parser.nat_of_done_as_digit
- \+ *lemma* parser.nat_of_done_bounded



## [2021-04-27 11:31:38](https://github.com/leanprover-community/mathlib/commit/5263ea3)
chore(algebra/lie/{abelian,tensor_product}): rename `maximal_trivial_submodule` → `max_triv_submodule` ([#7385](https://github.com/leanprover-community/mathlib/pull/7385))
cf https://github.com/leanprover-community/mathlib/pull/7313#discussion_r619995552
#### Estimated changes
Modified src/algebra/lie/abelian.lean
- \+/\- *abbreviation* lie_algebra.center
- \+ *lemma* lie_module.coe_linear_map_max_triv_linear_map_equiv_lie_module_hom
- \+ *lemma* lie_module.coe_linear_map_max_triv_linear_map_equiv_lie_module_hom_symm
- \- *lemma* lie_module.coe_linear_map_maximal_trivial_linear_map_equiv_lie_module_hom
- \- *lemma* lie_module.coe_linear_map_maximal_trivial_linear_map_equiv_lie_module_hom_symm
- \+ *lemma* lie_module.coe_max_triv_equiv_apply
- \+ *lemma* lie_module.coe_max_triv_hom_apply
- \+ *lemma* lie_module.coe_max_triv_linear_map_equiv_lie_module_hom
- \+ *lemma* lie_module.coe_max_triv_linear_map_equiv_lie_module_hom_symm
- \- *lemma* lie_module.coe_maximal_trivial_equiv_apply
- \- *lemma* lie_module.coe_maximal_trivial_hom_apply
- \- *lemma* lie_module.coe_maximal_trivial_linear_map_equiv_lie_module_hom
- \- *lemma* lie_module.coe_maximal_trivial_linear_map_equiv_lie_module_hom_symm
- \+ *lemma* lie_module.is_trivial_iff_max_triv_eq_top
- \- *lemma* lie_module.is_trivial_iff_maximal_trivial_eq_top
- \+ *def* lie_module.max_triv_equiv
- \+ *lemma* lie_module.max_triv_equiv_of_equiv_symm_eq_symm
- \+ *lemma* lie_module.max_triv_equiv_of_refl_eq_refl
- \+ *def* lie_module.max_triv_hom
- \+ *def* lie_module.max_triv_linear_map_equiv_lie_module_hom
- \+ *def* lie_module.max_triv_submodule
- \- *def* lie_module.maximal_trivial_equiv
- \- *lemma* lie_module.maximal_trivial_equiv_of_equiv_symm_eq_symm
- \- *lemma* lie_module.maximal_trivial_equiv_of_refl_eq_refl
- \- *def* lie_module.maximal_trivial_hom
- \- *def* lie_module.maximal_trivial_linear_map_equiv_lie_module_hom
- \- *def* lie_module.maximal_trivial_submodule
- \+ *lemma* lie_module.mem_max_triv_submodule
- \- *lemma* lie_module.mem_maximal_trivial_submodule

Modified src/algebra/lie/tensor_product.lean




## [2021-04-27 11:31:37](https://github.com/leanprover-community/mathlib/commit/e7bd3ca)
docs(overview): Add some recent work by Yury ([#7378](https://github.com/leanprover-community/mathlib/pull/7378))
Hausdorff measure and Urysohn's lemma
#### Estimated changes
Modified docs/overview.yaml




## [2021-04-27 11:31:36](https://github.com/leanprover-community/mathlib/commit/efeeaca)
feat(analysis/special_functions/integrals): integral of `sin x ^ n` ([#7372](https://github.com/leanprover-community/mathlib/pull/7372))
The reduction of `∫ x in a..b, sin x ^ n`, ∀ n ∈ ℕ, 2 ≤ n.
We had this for the integral over [0, π] but I don't see any reason not to generalize it to any [a, b].
This also allows for the derivation of the integral of `sin x ^ 2` as a special case.
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_sin_pow
- \+ *lemma* integral_sin_pow_antimono
- \+/\- *lemma* integral_sin_pow_aux
- \- *lemma* integral_sin_pow_succ_succ
- \+ *lemma* integral_sin_sq

Modified src/data/real/pi.lean
- \- *lemma* real.integral_sin_pow_antimono

Modified test/integration.lean




## [2021-04-27 11:31:35](https://github.com/leanprover-community/mathlib/commit/18403ac)
feat(topology/separation): change regular_space definition, added t1_characterisation and definition of Urysohn space ([#7367](https://github.com/leanprover-community/mathlib/pull/7367))
This PR changes the definition of regular_space becouse the previous definition requests t1_space and it's posible to only require t0_space as a condition. Due to that change, we had to reformulate the prove of the lemma separed_regular in src/topology/uniform_space/separation.lean adding the t0 condition.
We've also define the Uryson space , with his respectives lemmas about the relation with `T_2` and `T_3`, and prove the relation between the definition of t1_space from mathlib and the common definition with open sets.
#### Estimated changes
Modified src/topology/separation.lean
- \+ *lemma* t1_iff_exists_open

Modified src/topology/uniform_space/separation.lean




## [2021-04-27 07:21:32](https://github.com/leanprover-community/mathlib/commit/287492c)
refactor(ring_theory/hahn_series): non-linearly-ordered Hahn series ([#7377](https://github.com/leanprover-community/mathlib/pull/7377))
Refactors Hahn series to use `set.is_pwo` instead of `set.is_wf`, allowing them to be defined on non-linearly-ordered monomial types
#### Estimated changes
Modified src/order/well_founded_set.lean
- \+/\- *theorem* finset.is_pwo
- \+ *theorem* finset.is_pwo_sup
- \+ *theorem* finset.is_pwo_support_mul_antidiagonal
- \+/\- *theorem* finset.is_wf
- \- *theorem* finset.is_wf_support_mul_antidiagonal
- \+/\- *theorem* finset.mul_antidiagonal_min_mul_min
- \+/\- *theorem* finset.partially_well_ordered_on
- \+/\- *theorem* finset.well_founded_on
- \+ *theorem* set.finite.is_pwo
- \- *theorem* set.finite.is_wf
- \+ *theorem* set.fintype.is_pwo
- \- *theorem* set.fintype.is_wf
- \+ *theorem* set.is_pwo.insert
- \+/\- *theorem* set.is_pwo.mul
- \+ *theorem* set.is_pwo.union
- \+ *theorem* set.is_pwo_empty
- \+ *theorem* set.is_pwo_singleton
- \- *theorem* set.is_wf.insert
- \- *theorem* set.is_wf_empty
- \- *theorem* set.is_wf_singleton
- \+ *theorem* set.partially_well_ordered_on.mono

Modified src/ring_theory/hahn_series.lean
- \+ *lemma* hahn_series.is_pwo_support
- \+/\- *lemma* hahn_series.is_wf_support
- \+/\- *lemma* hahn_series.mul_coeff_left'
- \+/\- *lemma* hahn_series.mul_coeff_min_add_min
- \+/\- *lemma* hahn_series.mul_coeff_right'
- \+ *lemma* hahn_series.summable_family.is_pwo_Union_support
- \- *lemma* hahn_series.summable_family.is_wf_Union_support
- \+/\- *structure* hahn_series



## [2021-04-27 07:21:31](https://github.com/leanprover-community/mathlib/commit/57cc384)
chore(integration): missing lemmas ([#7364](https://github.com/leanprover-community/mathlib/pull/7364))
These are still preliminaries for derivation of parametric integrals.
From the sphere eversion project
#### Estimated changes
Modified src/analysis/calculus/fderiv_measurable.lean
- \- *lemma* continuous_linear_map.measurable_apply'
- \- *lemma* continuous_linear_map.measurable_apply
- \- *lemma* continuous_linear_map.measurable_coe

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.continuous_at_of_dominated
- \+ *lemma* measure_theory.continuous_of_dominated

Modified src/measure_theory/borel_space.lean
- \+ *lemma* ae_measurable.apply_continuous_linear_map
- \+ *lemma* continuous.ae_measurable
- \+ *lemma* continuous_linear_map.measurable_apply'
- \+ *lemma* continuous_linear_map.measurable_apply
- \+ *lemma* continuous_linear_map.measurable_coe
- \+ *lemma* measurable.apply_continuous_linear_map

Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.integrable.apply_continuous_linear_map
- \+ *lemma* measure_theory.integrable_of_norm_sub_le

Modified src/measure_theory/set_integral.lean
- \+ *lemma* continuous_linear_map.integral_apply



## [2021-04-27 07:21:30](https://github.com/leanprover-community/mathlib/commit/241400f)
feat(analysis/seminorm): lemmas on balanced sets ([#7358](https://github.com/leanprover-community/mathlib/pull/7358))
Adds lemmas about operations on balanced sets and golfs a proof.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* absorbent_iff_forall_absorbs_singleton
- \+ *lemma* balanced.add
- \+ *lemma* balanced.inter
- \+ *lemma* balanced.smul
- \+ *lemma* balanced.union
- \+ *lemma* balanced.univ



## [2021-04-27 07:21:29](https://github.com/leanprover-community/mathlib/commit/20c520a)
feat(algebra/opposite): inversion is a mul_equiv to the opposite group ([#7330](https://github.com/leanprover-community/mathlib/pull/7330))
This also splits out `monoid_hom.to_opposite` from `ring_hom.to_opposite`, and adds `add_equiv.neg` and `mul_equiv.inv` for the case when the `(add_)group` is commutative.
#### Estimated changes
Modified src/algebra/opposites.lean
- \+ *def* monoid_hom.to_opposite
- \+ *def* mul_equiv.inv'
- \- *lemma* ring_hom.coe_to_opposite

Modified src/data/equiv/mul_add.lean
- \+ *def* mul_equiv.inv



## [2021-04-27 07:21:28](https://github.com/leanprover-community/mathlib/commit/465cf5a)
feat(category_theory/abelian): biproducts of projective objects are projective ([#7319](https://github.com/leanprover-community/mathlib/pull/7319))
Also all objects of `Type` are projective.
#### Estimated changes
Modified src/category_theory/abelian/projective.lean
- \+ *def* category_theory.projective.factor_thru
- \+ *lemma* category_theory.projective.factor_thru_comp



## [2021-04-27 07:21:26](https://github.com/leanprover-community/mathlib/commit/874780f)
feat(data/quot): rec_on_subsingleton2' ([#7294](https://github.com/leanprover-community/mathlib/pull/7294))
#### Estimated changes
Modified src/data/quot.lean




## [2021-04-27 07:21:25](https://github.com/leanprover-community/mathlib/commit/a3f589c)
feat(analysis/calculus/deriv): `has_deriv_at.continuous_on` ([#7260](https://github.com/leanprover-community/mathlib/pull/7260))
See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/has_deriv_at.2Econtinuous_on/near/235034547).
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/measure_theory/interval_integral.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_at.continuous_on



## [2021-04-27 07:21:24](https://github.com/leanprover-community/mathlib/commit/4f9543b)
feat(data/polynomial): lemma about aeval on functions, and on subalgebras ([#7252](https://github.com/leanprover-community/mathlib/pull/7252))
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* polynomial.aeval_fn_apply
- \+/\- *lemma* polynomial.aeval_monomial
- \+ *lemma* polynomial.aeval_subalgebra_coe



## [2021-04-27 07:21:23](https://github.com/leanprover-community/mathlib/commit/89c27cc)
feat(category/subobjects): more API on limit subobjects ([#7203](https://github.com/leanprover-community/mathlib/pull/7203))
#### Estimated changes
Modified src/category_theory/subobject/limits.lean
- \+ *abbreviation* category_theory.limits.equalizer_subobject
- \- *def* category_theory.limits.equalizer_subobject
- \+/\- *lemma* category_theory.limits.equalizer_subobject_arrow'
- \+ *lemma* category_theory.limits.factor_thru_image_subobject_comp_self
- \+ *lemma* category_theory.limits.factor_thru_image_subobject_comp_self_assoc
- \+ *abbreviation* category_theory.limits.image_subobject
- \- *def* category_theory.limits.image_subobject
- \+/\- *lemma* category_theory.limits.image_subobject_arrow'
- \+ *def* category_theory.limits.image_subobject_comp_iso
- \+ *lemma* category_theory.limits.image_subobject_comp_iso_hom_arrow
- \+ *lemma* category_theory.limits.image_subobject_comp_iso_inv_arrow
- \+ *lemma* category_theory.limits.image_subobject_comp_le
- \+ *lemma* category_theory.limits.image_subobject_zero
- \+ *lemma* category_theory.limits.image_subobject_zero_arrow
- \+ *abbreviation* category_theory.limits.kernel_subobject
- \- *def* category_theory.limits.kernel_subobject
- \+/\- *lemma* category_theory.limits.kernel_subobject_arrow'
- \+ *lemma* category_theory.limits.kernel_subobject_comp_le
- \+ *def* category_theory.limits.kernel_subobject_iso_comp
- \+ *lemma* category_theory.limits.kernel_subobject_iso_comp_hom_arrow
- \+ *lemma* category_theory.limits.kernel_subobject_iso_comp_inv_arrow
- \+ *lemma* category_theory.limits.kernel_subobject_zero



## [2021-04-27 07:21:22](https://github.com/leanprover-community/mathlib/commit/40b15f2)
feat(algebra/direct_sum): state what it means for a direct sum to be internal ([#7190](https://github.com/leanprover-community/mathlib/pull/7190))
The goal here is primarily to tick off the item in undergrad.yml.
We'll want some theorems relating this statement to independence / spanning of the submodules, but I'll leave those for someone else to follow-up with.
We end up needing three variants of this - one for each of add_submonoids, add_subgroups, and submodules.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/algebra/direct_sum.lean
- \+ *lemma* direct_sum.add_subgroup_is_internal.to_add_submonoid
- \+ *def* direct_sum.add_subgroup_is_internal
- \+ *def* direct_sum.add_submonoid_is_internal

Modified src/linear_algebra/direct_sum_module.lean
- \+ *lemma* direct_sum.submodule_is_internal.to_add_subgroup
- \+ *lemma* direct_sum.submodule_is_internal.to_add_submonoid
- \+ *def* direct_sum.submodule_is_internal



## [2021-04-27 05:47:11](https://github.com/leanprover-community/mathlib/commit/2d8ed1f)
chore(group_theory/eckmann_hilton): use `mul_one_class` and `is_(left|right)_id` ([#7370](https://github.com/leanprover-community/mathlib/pull/7370))
This ties these theorems slightly more to the rest of mathlib.
The changes are:
* `eckmann_hilton.comm_monoid` now promotes a `mul_one_class` to a `comm_monoid` rather than taking two `is_unital` objects. This makes it consistent with `eckmann_hilton.comm_group`.
* `is_unital` is no longer a `class`, since it never had any instances and was never used as a typeclass argument.
* `is_unital` is now defined in terms of `is_left_id` and `is_right_id`.
* `add_group.is_unital` has been renamed to `eckmann_hilton.add_zero_class.is_unital` - the missing namespace was an accident, and the definition works much more generally than it was originally stated for.
#### Estimated changes
Modified src/group_theory/eckmann_hilton.lean
- \+/\- *def* eckmann_hilton.comm_monoid
- \- *lemma* eckmann_hilton.group.is_unital
- \+ *structure* eckmann_hilton.is_unital
- \+/\- *lemma* eckmann_hilton.mul
- \+ *lemma* eckmann_hilton.mul_one_class.is_unital



## [2021-04-27 04:33:28](https://github.com/leanprover-community/mathlib/commit/1742443)
refactor(archive/imo) shorten imo1013_q5 using pow_unbounded_of_one_lt ([#7373](https://github.com/leanprover-community/mathlib/pull/7373))
Replaces a usage of `one_add_mul_sub_le_pow` with the more direct `pow_unbounded_of_one_lt`.
#### Estimated changes
Modified archive/imo/imo2013_q5.lean




## [2021-04-26 22:18:45](https://github.com/leanprover-community/mathlib/commit/3093fd8)
chore(algebra/category/*): use by apply to speed up elaboration ([#7360](https://github.com/leanprover-community/mathlib/pull/7360))
A few more speed ups.
#### Estimated changes
Modified src/algebra/category/Algebra/limits.lean
- \- *def* Algebra.forget₂_Module_preserves_limits_aux
- \- *def* Algebra.forget₂_Ring_preserves_limits_aux

Modified src/algebra/category/Group/limits.lean


Modified src/algebra/category/Mon/limits.lean




## [2021-04-26 18:22:46](https://github.com/leanprover-community/mathlib/commit/a5cb13a)
feat(order/zorn): upward inclusion variant of Zorn's lemma ([#7362](https://github.com/leanprover-community/mathlib/pull/7362))
add zorn_superset
This also add various missing bits of whitespace throughout the file.
#### Estimated changes
Modified src/order/zorn.lean
- \+/\- *theorem* zorn.chain.directed_on
- \+/\- *theorem* zorn.chain.image
- \+/\- *theorem* zorn.chain.mono
- \+ *theorem* zorn.chain.symm
- \+/\- *theorem* zorn.chain.total
- \+/\- *def* zorn.chain
- \+/\- *theorem* zorn.chain_chain_closure
- \+/\- *theorem* zorn.chain_closure_closure
- \+/\- *theorem* zorn.chain_closure_empty
- \+/\- *theorem* zorn.chain_closure_total
- \+/\- *theorem* zorn.chain_insert
- \+/\- *theorem* zorn.chain_succ
- \+/\- *theorem* zorn.exists_maximal_of_chains_bounded
- \+/\- *def* zorn.is_max_chain
- \+/\- *theorem* zorn.max_chain_spec
- \+/\- *theorem* zorn.succ_increasing
- \+/\- *theorem* zorn.succ_spec
- \+ *theorem* zorn.zorn_superset
- \+ *theorem* zorn.zorn_superset_nonempty



## [2021-04-26 13:34:11](https://github.com/leanprover-community/mathlib/commit/5ac79a6)
feat(algebra/lie/tensor_product): prove `lie_submodule.lie_ideal_oper_eq_tensor_map_range` ([#7313](https://github.com/leanprover-community/mathlib/pull/7313))
The lemma `coe_lift_lie_eq_lift_coe` also introduced here is an unrelated change but is a stronger form of `lift_lie_apply` that is worth having.
See also this [Zulip remark](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60linear_map.2Erange_eq_map.60.20vs.20.60submodule.2Emap_top.60/near/235845192) concerning the proposed library note.
#### Estimated changes
Modified src/algebra/lie/abelian.lean
- \+ *lemma* lie_module.coe_linear_map_maximal_trivial_linear_map_equiv_lie_module_hom
- \+ *lemma* lie_module.coe_linear_map_maximal_trivial_linear_map_equiv_lie_module_hom_symm
- \- *lemma* lie_module.coe_maximal_trivial_linear_map_equiv_lie_module_hom_apply
- \+ *lemma* lie_module.coe_maximal_trivial_linear_map_equiv_lie_module_hom_symm
- \- *lemma* lie_module.coe_maximal_trivial_linear_map_equiv_lie_module_hom_symm_apply

Modified src/algebra/lie/basic.lean
- \+ *lemma* lie_hom.coe_comp
- \+ *lemma* lie_hom.coe_linear_map_comp
- \+/\- *lemma* lie_hom.comp_apply
- \- *lemma* lie_hom.comp_coe
- \+ *lemma* lie_module_hom.coe_comp
- \+ *lemma* lie_module_hom.coe_linear_map_comp
- \+/\- *lemma* lie_module_hom.comp_apply
- \- *lemma* lie_module_hom.comp_coe

Modified src/algebra/lie/ideal_operations.lean


Modified src/algebra/lie/of_associative.lean


Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_module_hom.coe_range
- \+ *lemma* lie_module_hom.coe_submodule_range
- \+ *lemma* lie_module_hom.map_top
- \+ *lemma* lie_module_hom.mem_range
- \+ *def* lie_module_hom.range
- \+ *lemma* lie_submodule.mem_map

Modified src/algebra/lie/tensor_product.lean
- \+ *def* lie_module.to_module_hom
- \+ *lemma* lie_module.to_module_hom_apply
- \+ *lemma* lie_submodule.lie_ideal_oper_eq_tensor_map_range
- \+ *lemma* tensor_product.lie_module.coe_lift_lie_eq_lift_coe
- \+ *lemma* tensor_product.lie_module.coe_linear_map_map
- \- *lemma* tensor_product.lie_module.lie_tensor_right
- \+ *lemma* tensor_product.lie_module.lie_tmul_right
- \+/\- *lemma* tensor_product.lie_module.lift_lie_apply
- \+ *def* tensor_product.lie_module.map
- \+ *def* tensor_product.lie_module.map_incl
- \+ *lemma* tensor_product.lie_module.map_incl_def
- \+ *lemma* tensor_product.lie_module.map_tmul

Modified src/field_theory/subfield.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/linear_algebra/basic.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/subsemiring.lean




## [2021-04-26 13:34:10](https://github.com/leanprover-community/mathlib/commit/35b9d9c)
feat(group_theory/finiteness): add submonoid.fg ([#7279](https://github.com/leanprover-community/mathlib/pull/7279))
I introduce here the notion of a finitely generated monoid (not necessarily commutative) and I prove that the notion is preserved by `additive`/`multiplicative`.
A natural continuation is of course to introduce the same notion for groups.
#### Estimated changes
Added src/group_theory/finiteness.lean
- \+ *lemma* add_monoid.fg_def
- \+ *lemma* add_monoid.fg_iff_mul_fg
- \+ *lemma* add_submonoid.fg_iff_mul_fg
- \+ *lemma* monoid.fg_def
- \+ *lemma* monoid.fg_iff
- \+ *lemma* monoid.fg_iff_add_fg
- \+ *def* submonoid.fg
- \+ *lemma* submonoid.fg_iff
- \+ *lemma* submonoid.fg_iff_add_fg

Modified src/ring_theory/noetherian.lean
- \+ *lemma* submodule.fg_iff_add_submonoid_fg



## [2021-04-26 09:22:21](https://github.com/leanprover-community/mathlib/commit/5258669)
feat(topology/unit_interval): affine homeomorphisms of intervals ([#7250](https://github.com/leanprover-community/mathlib/pull/7250))
#### Estimated changes
Added i.pdf


Modified src/data/set/intervals/image_preimage.lean
- \+ *lemma* set.image_affine_Icc'

Added src/topology/algebra/field.lean
- \+ *def* affine_homeomorph

Modified src/topology/unit_interval.lean
- \+ *def* Icc_homeo_I
- \+ *lemma* Icc_homeo_I_apply_coe
- \+ *lemma* Icc_homeo_I_symm_apply_coe
- \+ *lemma* affine_homeomorph_image_I



## [2021-04-26 06:03:18](https://github.com/leanprover-community/mathlib/commit/c22de3f)
chore(algebra/lie/nilpotent): make proof of `module.derived_series_le_lower_central_series` less refl-heavy ([#7359](https://github.com/leanprover-community/mathlib/pull/7359))
According to the list in [this Zulip remark](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20repo.20GitHub.20actions.20queue/near/235996204)
this lemma was the slowest task for Leanchecker.
The changes here should help. Using `set_option profiler true`, I see
about a ten-fold speedup in elaboration time for Lean, from approximately
2.4s to 0.24s
#### Estimated changes
Modified src/algebra/lie/nilpotent.lean




## [2021-04-25 19:05:15](https://github.com/leanprover-community/mathlib/commit/9526061)
feat(data/nat/fib): add a strict monotonicity lemma. ([#7317](https://github.com/leanprover-community/mathlib/pull/7317))
Prove strict monotonicity of `fib (n + 2)`.
With thanks to @b-mehta and @dwarn.
#### Estimated changes
Modified src/data/nat/fib.lean
- \+ *lemma* nat.fib_add_two_strict_mono



## [2021-04-25 15:13:07](https://github.com/leanprover-community/mathlib/commit/4e0c460)
chore(analysis/special_functions/integrals): reorganize file ([#7351](https://github.com/leanprover-community/mathlib/pull/7351))
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+/\- *lemma* integral_id
- \+/\- *lemma* integral_one
- \+/\- *lemma* integral_pow
- \+/\- *lemma* integral_sin_pow_aux
- \+/\- *theorem* integral_sin_pow_even
- \+/\- *theorem* integral_sin_pow_odd
- \+/\- *lemma* integral_sin_pow_pos
- \+/\- *lemma* integral_sin_pow_succ_succ
- \+/\- *lemma* interval_integral.interval_integrable.const_mul
- \+/\- *lemma* interval_integral.interval_integrable.div
- \+/\- *lemma* interval_integral.interval_integrable.mul_const
- \+/\- *lemma* interval_integral.interval_integrable_const
- \+/\- *lemma* interval_integral.interval_integrable_inv_one_add_sq
- \+/\- *lemma* interval_integral.interval_integrable_one_div_one_add_sq
- \+/\- *lemma* interval_integral.interval_integrable_pow



## [2021-04-25 15:13:06](https://github.com/leanprover-community/mathlib/commit/dbc9cf9)
feat(data/matrix/basic): transform vec_mul to mul_vec ([#7348](https://github.com/leanprover-community/mathlib/pull/7348))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.add_mul_vec
- \+ *lemma* matrix.add_vec_mul
- \+ *lemma* matrix.mul_vec_add
- \+ *lemma* matrix.mul_vec_transpose
- \+ *lemma* matrix.vec_mul_add
- \+ *lemma* matrix.vec_mul_transpose



## [2021-04-25 15:13:05](https://github.com/leanprover-community/mathlib/commit/d5cb403)
chore(ring_theory/ideal/operations): golf and remove @ ([#7347](https://github.com/leanprover-community/mathlib/pull/7347))
Instead of passing all these arguments explicitly, it's sufficient to just use `(... : _)` to get the elaborator to do the right thing.
This makes this proof less fragile to argument changes to `pi.ring_hom`, such as the planned generalization to non-associative rings
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean




## [2021-04-25 15:13:04](https://github.com/leanprover-community/mathlib/commit/3821d31)
feat(ring_theory): fg_iff_exists_fin_generating_fam ([#7343](https://github.com/leanprover-community/mathlib/pull/7343))
#### Estimated changes
Modified src/ring_theory/finiteness.lean
- \+ *lemma* module.finite.exists_fin

Modified src/ring_theory/noetherian.lean
- \+ *lemma* submodule.fg_iff_exists_fin_generating_family



## [2021-04-25 15:13:03](https://github.com/leanprover-community/mathlib/commit/9cc3d80)
feat(linear_algebra): free_of_finite_type_torsion_free ([#7341](https://github.com/leanprover-community/mathlib/pull/7341))
A finite type torsion free module over a PID is free.
There are also some tiny preliminaries, and I moved `submodule.map_span` to `linear_map.map_span` to allow using the dot notation more often.
#### Estimated changes
Modified src/algebra/lie/ideal_operations.lean


Modified src/algebra/module/basic.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.map_span_le

Modified src/linear_algebra/free_module.lean
- \+ *lemma* module.free_of_finite_type_torsion_free

Modified src/linear_algebra/tensor_product.lean
- \+ *lemma* linear_map.ker_lsmul

Modified src/ring_theory/noetherian.lean




## [2021-04-25 10:09:22](https://github.com/leanprover-community/mathlib/commit/8e4ef23)
refactor(*): kill int multiplication diamonds ([#7255](https://github.com/leanprover-community/mathlib/pull/7255))
Insert a data field `gsmul` in `add_comm_group` containing a Z-action, and use it to make sure that all diamonds related to `Z` -actions disappear.
Followup to [#7084](https://github.com/leanprover-community/mathlib/pull/7084)
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/archimedean.lean


Modified src/algebra/category/CommRing/adjunctions.lean


Modified src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/algebra/category/Module/basic.lean


Modified src/algebra/field_power.lean


Modified src/algebra/group/defs.lean
- \+ *def* gpow_rec
- \+ *def* gsmul_rec

Modified src/algebra/group/hom_instances.lean


Modified src/algebra/group/pi.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/type_tags.lean


Modified src/algebra/group/ulift.lean


Modified src/algebra/group_power/basic.lean
- \- *def* gpow
- \+/\- *theorem* gpow_coe_nat
- \+ *lemma* gpow_eq_pow
- \+/\- *theorem* gpow_neg_one
- \+/\- *theorem* gpow_neg_succ_of_nat
- \+/\- *theorem* gpow_of_nat
- \+/\- *theorem* gpow_one
- \+/\- *theorem* gpow_zero
- \- *lemma* group.gpow_eq_has_pow
- \- *def* gsmul
- \+/\- *theorem* gsmul_add
- \+/\- *theorem* gsmul_coe_nat
- \+ *lemma* gsmul_eq_smul
- \+/\- *theorem* gsmul_neg
- \+/\- *theorem* gsmul_neg_succ_of_nat
- \+/\- *theorem* gsmul_of_nat
- \+/\- *theorem* gsmul_sub
- \+/\- *theorem* gsmul_zero
- \+/\- *theorem* neg_gsmul
- \+/\- *theorem* neg_one_gsmul
- \+/\- *lemma* of_mul_gpow
- \+/\- *theorem* one_gsmul
- \+/\- *theorem* zero_gsmul

Modified src/algebra/group_power/lemmas.lean
- \+/\- *theorem* add_gsmul
- \+/\- *theorem* add_monoid_hom.map_gsmul
- \+/\- *theorem* add_one_gsmul
- \+/\- *theorem* bit0_gsmul
- \+/\- *lemma* bit0_mul
- \+/\- *theorem* bit1_gsmul
- \+/\- *lemma* bit1_mul
- \+/\- *theorem* gsmul_add_comm
- \+/\- *theorem* gsmul_eq_mul'
- \+/\- *theorem* gsmul_eq_mul
- \+/\- *lemma* gsmul_int_int
- \+/\- *lemma* gsmul_int_one
- \+/\- *theorem* gsmul_le_gsmul
- \+/\- *theorem* gsmul_le_gsmul_iff
- \+/\- *theorem* gsmul_lt_gsmul
- \+/\- *theorem* gsmul_lt_gsmul_iff
- \+/\- *theorem* gsmul_mul'
- \- *theorem* gsmul_mul
- \+/\- *theorem* gsmul_one
- \+/\- *lemma* gsmul_pos
- \+/\- *lemma* mul_bit0
- \+/\- *lemma* mul_bit1
- \+ *theorem* mul_gsmul
- \+/\- *theorem* mul_gsmul_assoc
- \+/\- *theorem* mul_gsmul_left
- \+/\- *theorem* one_add_gsmul
- \+/\- *lemma* sub_gsmul

Modified src/algebra/group_with_zero/power.lean
- \- *def* fpow
- \- *theorem* fpow_coe_nat
- \+/\- *theorem* fpow_neg_one
- \- *theorem* fpow_neg_succ_of_nat
- \- *theorem* fpow_of_nat
- \- *theorem* fpow_one
- \- *theorem* fpow_zero

Modified src/algebra/iterate_hom.lean


Modified src/algebra/module/basic.lean
- \+ *def* add_comm_group.int_module.unique
- \- *def* add_comm_group.int_module
- \- *lemma* add_monoid_hom.int_smul_apply
- \+/\- *lemma* add_monoid_hom.map_int_module_smul
- \- *lemma* gsmul_def
- \- *lemma* gsmul_eq_smul
- \+/\- *lemma* gsmul_eq_smul_cast
- \+/\- *lemma* int.smul_one_eq_coe
- \+ *lemma* int_smul_eq_gsmul

Modified src/algebra/module/linear_map.lean


Modified src/algebra/punit_instances.lean


Modified src/algebra/ring/ulift.lean


Modified src/algebra/star/chsh.lean
- \- *lemma* tsirelson_inequality.neg_two_gsmul_half_smul
- \- *lemma* tsirelson_inequality.smul_four
- \- *lemma* tsirelson_inequality.smul_two
- \- *lemma* tsirelson_inequality.two_gsmul_half_smul

Modified src/analysis/asymptotics/specific_asymptotics.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/category_theory/endomorphism.lean


Modified src/data/complex/basic.lean


Modified src/data/equiv/mul_add_aut.lean


Modified src/data/equiv/ring_aut.lean


Modified src/data/finsupp/basic.lean


Modified src/data/fintype/card.lean


Modified src/data/holor.lean


Modified src/data/int/basic.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/padics/ring_homs.lean


Modified src/data/quaternion.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/irrational.lean


Modified src/data/zsqrtd/basic.lean


Modified src/deprecated/subfield.lean


Modified src/deprecated/subgroup.lean


Modified src/field_theory/intermediate_field.lean
- \+/\- *lemma* intermediate_field.pow_mem

Modified src/field_theory/perfect_closure.lean


Modified src/field_theory/subfield.lean


Modified src/group_theory/archimedean.lean


Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* exists_gpow_eq_one
- \+/\- *lemma* exists_gsmul_eq_zero
- \+/\- *lemma* gmultiples_equiv_gmultiples_apply
- \+/\- *lemma* gsmul_eq_mod_add_order_of

Modified src/group_theory/specific_groups/cyclic.lean


Modified src/group_theory/subgroup.lean
- \+/\- *lemma* add_subgroup.coe_gsmul

Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/multilinear.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/measure_theory/arithmetic.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/number_theory/dioph.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/roots_of_unity.lean
- \+/\- *lemma* is_primitive_root.fpow_eq_one
- \+/\- *lemma* is_primitive_root.gpow_eq_one

Modified src/ring_theory/subring.lean


Modified src/tactic/abel.lean
- \+/\- *def* tactic.abel.smulg
- \+/\- *def* tactic.abel.termg

Modified src/topology/algebra/group_with_zero.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.continuous.gsmul
- \+ *lemma* continuous_linear_map.continuous_gsmul

Modified src/topology/algebra/ordered.lean


Modified test/abel.lean


Modified test/refine_struct.lean




## [2021-04-25 05:29:14](https://github.com/leanprover-community/mathlib/commit/d052c52)
feat(order/extension): extend partial order to linear order ([#7142](https://github.com/leanprover-community/mathlib/pull/7142))
Adds a construction to extend a partial order to a linear order. Also fills in a missing Zorn variant.
#### Estimated changes
Modified src/analysis/convex/cone.lean


Modified src/analysis/normed_space/inner_product.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/order/compactly_generated.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* binary_relation_Sup_iff
- \+ *lemma* unary_relation_Sup_iff

Added src/order/extension.lean
- \+ *theorem* extend_partial_order
- \+ *def* linear_extension
- \+ *def* to_linear_extension

Modified src/order/zorn.lean
- \+ *theorem* zorn.zorn_nonempty_partial_order₀
- \+ *theorem* zorn.zorn_subset_nonempty
- \- *theorem* zorn.zorn_subset₀

Modified src/ring_theory/ideal/operations.lean


Modified src/topology/subset_properties.lean




## [2021-04-25 03:55:19](https://github.com/leanprover-community/mathlib/commit/d5330fe)
chore(algebra/category): remove duplicated proofs ([#7349](https://github.com/leanprover-community/mathlib/pull/7349))
The results added in [#7100](https://github.com/leanprover-community/mathlib/pull/7100) already exist. I moved them to the place where Scott added the duplicates. Hopefully that will make them more discoverable.
#### Estimated changes
Modified src/algebra/category/Module/basic.lean
- \- *lemma* Module.epi_of_range_eq_top
- \- *lemma* Module.ker_eq_bot_of_mono
- \- *lemma* Module.mono_of_ker_eq_bot
- \- *lemma* Module.range_eq_top_of_epi

Modified src/algebra/category/Module/epi_mono.lean
- \+ *lemma* Module.epi_iff_range_eq_top
- \+/\- *lemma* Module.epi_iff_surjective
- \+ *lemma* Module.ker_eq_bot_of_mono
- \+/\- *lemma* Module.mono_iff_injective
- \+ *lemma* Module.mono_iff_ker_eq_bot
- \+ *lemma* Module.range_eq_top_of_epi

Modified src/algebra/category/Module/kernels.lean


Modified src/algebra/category/Module/subobject.lean




## [2021-04-24 22:17:12](https://github.com/leanprover-community/mathlib/commit/6b2bb8a)
feat(data/finsupp): to_multiset symm apply ([#7356](https://github.com/leanprover-community/mathlib/pull/7356))
Adds a lemma and golfs a proof.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.to_multiset_symm_apply



## [2021-04-24 22:17:11](https://github.com/leanprover-community/mathlib/commit/beb694b)
feat(data/list/basic): assorted list lemmas ([#7296](https://github.com/leanprover-community/mathlib/pull/7296))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.exists_mem_of_ne_nil
- \+ *lemma* list.nth_le_cons_length
- \+ *lemma* list.nth_le_reverse'
- \+ *lemma* list.reverse_eq_iff
- \+ *lemma* list.tail_append_of_ne_nil



## [2021-04-24 22:17:10](https://github.com/leanprover-community/mathlib/commit/7716870)
feat(data/list/forall2): defines sublist_forall2 relation ([#7165](https://github.com/leanprover-community/mathlib/pull/7165))
Defines the `sublist_forall₂` relation, indicating that one list is related by `forall₂` to a sublist of another.
Provides two lemmas, `head_mem_self` and `mem_of_mem_tail`, which will be useful when proving Higman's Lemma about the `sublist_forall₂` relation.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.head_mem_self
- \+ *lemma* list.tail_sublist
- \+/\- *theorem* list.tail_subset

Modified src/data/list/forall2.lean
- \+ *lemma* list.sublist.sublist_forall₂
- \+ *inductive* list.sublist_forall₂
- \+ *lemma* list.sublist_forall₂_iff
- \+ *lemma* list.tail_sublist_forall₂_self



## [2021-04-24 19:36:55](https://github.com/leanprover-community/mathlib/commit/2ecd65e)
feat(archive/imo): IMO 2001 Q2 ([#7238](https://github.com/leanprover-community/mathlib/pull/7238))
Formalization of IMO 2001/2
#### Estimated changes
Added archive/imo/imo2001_q2.lean
- \+ *lemma* bound
- \+ *lemma* denom_pos
- \+ *theorem* imo2001_q2'
- \+ *theorem* imo2001_q2



## [2021-04-24 19:36:54](https://github.com/leanprover-community/mathlib/commit/8f8b194)
feat(linear_algebra): Lagrange formulas for expanding `det` along a row or column ([#6897](https://github.com/leanprover-community/mathlib/pull/6897))
This PR proves the full Lagrange formulas for writing the determinant of a `n+1 × n+1` matrix as an alternating sum of minors. @pechersky and @eric-wieser already put together enough of the pieces so that `simp` could apply this formula to matrices of a known size. In the end I still had to apply a couple of permutations (`fin.cycle_range` defined in [#6815](https://github.com/leanprover-community/mathlib/pull/6815)) to the entries to get to the "official" formula.
#### Estimated changes
Modified src/group_theory/perm/fin.lean
- \+ *lemma* fin.cycle_range_succ_above
- \+ *lemma* fin.cycle_range_symm_succ
- \+ *lemma* fin.cycle_range_symm_zero
- \+ *lemma* fin.succ_above_cycle_range

Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/determinant.lean
- \+ *lemma* matrix.det_fin_zero
- \+ *lemma* matrix.det_succ_column
- \+ *lemma* matrix.det_succ_column_zero
- \+ *lemma* matrix.det_succ_row
- \+ *lemma* matrix.det_succ_row_zero

Modified test/matrix.lean




## [2021-04-24 19:36:54](https://github.com/leanprover-community/mathlib/commit/f83ae59)
feat(group_theory/nielsen_schreier): subgroup of free group is free ([#6840](https://github.com/leanprover-community/mathlib/pull/6840))
Prove that a subgroup of a free group is itself free
#### Estimated changes
Modified src/category_theory/endomorphism.lean
- \+/\- *def* category_theory.functor.map_End

Modified src/category_theory/is_connected.lean


Modified src/category_theory/single_obj.lean
- \+ *def* category_theory.single_obj.difference_functor

Modified src/combinatorics/quiver.lean
- \+/\- *def* quiver.labelling
- \+/\- *structure* quiver.total

Added src/group_theory/nielsen_schreier.lean
- \+ *lemma* is_free_groupoid.ext_functor
- \+ *def* is_free_groupoid.generators
- \+ *lemma* is_free_groupoid.path_nonempty_of_hom
- \+ *def* is_free_groupoid.spanning_tree.End_is_free
- \+ *def* is_free_groupoid.spanning_tree.functor_of_monoid_hom
- \+ *def* is_free_groupoid.spanning_tree.loop_of_hom
- \+ *lemma* is_free_groupoid.spanning_tree.loop_of_hom_eq_id
- \+ *def* is_free_groupoid.spanning_tree.tree_hom
- \+ *lemma* is_free_groupoid.spanning_tree.tree_hom_eq
- \+ *lemma* is_free_groupoid.spanning_tree.tree_hom_root



## [2021-04-24 15:20:39](https://github.com/leanprover-community/mathlib/commit/46ceb36)
refactor(*): rename `semimodule` to `module`, delete typeclasses `module` and `vector_space` ([#7322](https://github.com/leanprover-community/mathlib/pull/7322))
Splitting typeclasses between `semimodule`, `module` and `vector_space` was causing many (small) issues, so why don't we just get rid of this duplication?
This PR contains the following changes:
 * delete the old `module` and `vector_space` synonyms for `semimodule`
 * find and replace all instances of `semimodule` and `vector_space` to `module`
 * (thereby renaming the previous `semimodule` typeclass to `module`)
 * rename `vector_space.dim` to `module.rank` (in preparation for generalizing this definition to all modules)
 * delete a couple `module` instances that have now become redundant
This find-and-replace has been done extremely naïvely, but it seems there were almost no name clashes and no "clbuttic mistakes". I have gone through the full set of changes, finding nothing weird, and I'm fixing any build issues as they come up (I expect less than 10 declarations will cause conflicts).
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/module.20from.20semimodule.20over.20a.20ring
A good example of a workaround required by the `module` abbreviation is the [`triv_sq_zero_ext.module` instance](https://github.com/leanprover-community/mathlib/blob/3b8cfdc905c663f3d99acac325c7dff1a0ce744c/src/algebra/triv_sq_zero_ext.lean#L164).
#### Estimated changes
Modified archive/sensitivity.lean
- \+/\- *lemma* dim_V
- \- *lemma* findim_V
- \+ *lemma* finrank_V

Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/algebra/algebra/basic.lean
- \+ *def* algebra.of_module'
- \+ *def* algebra.of_module
- \- *def* algebra.of_semimodule'
- \- *def* algebra.of_semimodule

Modified src/algebra/algebra/operations.lean


Modified src/algebra/algebra/ordered.lean


Modified src/algebra/algebra/tower.lean


Modified src/algebra/category/Module/limits.lean


Modified src/algebra/category/Module/monoidal.lean


Modified src/algebra/direct_limit.lean


Modified src/algebra/direct_sum_graded.lean


Modified src/algebra/lie/basic.lean


Modified src/algebra/linear_recurrence.lean
- \+/\- *lemma* linear_recurrence.sol_space_dim

Modified src/algebra/module/basic.lean
- \+ *def* add_comm_monoid.nat_module.unique
- \- *def* add_comm_monoid.nat_semimodule.unique
- \+/\- *lemma* add_monoid_hom.map_rat_module_smul
- \+/\- *theorem* add_smul
- \+/\- *lemma* gsmul_eq_smul
- \+/\- *lemma* int.smul_one_eq_coe
- \+ *def* module.add_comm_monoid_to_add_comm_group
- \+ *def* module.comp_hom
- \+ *structure* module.core
- \+ *lemma* module.eq_zero_of_zero_eq_one
- \+ *def* module.of_core
- \+ *theorem* module.subsingleton
- \- *abbreviation* module
- \+ *lemma* module_ext
- \+/\- *lemma* nat_smul_eq_nsmul
- \+ *def* ring_hom.to_module
- \- *def* ring_hom.to_semimodule
- \- *def* semimodule.add_comm_monoid_to_add_comm_group
- \- *def* semimodule.comp_hom
- \- *structure* semimodule.core
- \- *lemma* semimodule.eq_zero_of_zero_eq_one
- \- *def* semimodule.of_core
- \- *theorem* semimodule.subsingleton
- \- *lemma* semimodule_ext
- \- *abbreviation* vector_space

Modified src/algebra/module/hom.lean


Modified src/algebra/module/linear_map.lean
- \+/\- *def* add_monoid_hom.to_rat_linear_map
- \+/\- *lemma* is_linear_map.is_linear_map_smul'
- \+/\- *lemma* is_linear_map.is_linear_map_smul
- \+/\- *lemma* linear_equiv.coe_of_involutive
- \+/\- *lemma* linear_equiv.comp_coe
- \+/\- *def* linear_equiv.of_involutive
- \+/\- *def* linear_equiv.refl
- \+/\- *lemma* linear_equiv.refl_apply
- \+/\- *lemma* linear_equiv.refl_to_linear_map
- \+/\- *def* linear_equiv.simps.symm_apply
- \+/\- *lemma* linear_equiv.symm_bijective
- \+/\- *lemma* linear_equiv.symm_trans
- \+/\- *lemma* linear_equiv.trans_symm
- \+/\- *def* linear_map.inverse
- \+/\- *def* linear_map.restrict_scalars

Modified src/algebra/module/opposites.lean


Modified src/algebra/module/ordered.lean
- \+ *lemma* ordered_module.mk''
- \+ *lemma* ordered_module.mk'
- \- *lemma* ordered_semimodule.mk''
- \- *lemma* ordered_semimodule.mk'
- \+/\- *lemma* smul_lt_smul_of_pos

Modified src/algebra/module/pi.lean


Modified src/algebra/module/prod.lean


Modified src/algebra/module/projective.lean


Modified src/algebra/module/submodule.lean


Modified src/algebra/module/submodule_lattice.lean


Modified src/algebra/module/ulift.lean
- \+ *def* ulift.module_equiv
- \- *def* ulift.semimodule_equiv

Modified src/algebra/monoid_algebra.lean


Modified src/algebra/pointwise.lean
- \+/\- *lemma* zero_smul_set

Modified src/algebra/punit_instances.lean


Modified src/algebra/smul_regular.lean


Modified src/algebra/star/chsh.lean


Modified src/algebra/triv_sq_zero_ext.lean
- \+/\- *def* triv_sq_zero_ext.fst_hom
- \+/\- *def* triv_sq_zero_ext.inl_hom
- \+/\- *lemma* triv_sq_zero_ext.inl_mul_inr
- \+/\- *def* triv_sq_zero_ext.inr_hom
- \+/\- *lemma* triv_sq_zero_ext.inr_mul_inl
- \+/\- *lemma* triv_sq_zero_ext.inr_mul_inr
- \+/\- *def* triv_sq_zero_ext.snd_hom

Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/convex/basic.lean
- \+/\- *lemma* concave_on.concave_le
- \+/\- *lemma* concave_on.smul
- \+/\- *lemma* convex_on.convex_le
- \+/\- *lemma* convex_on.smul
- \+/\- *lemma* neg_concave_on_iff
- \+/\- *lemma* neg_convex_on_iff

Modified src/analysis/convex/caratheodory.lean
- \+/\- *lemma* caratheodory.mem_convex_hull_erase
- \+/\- *lemma* caratheodory.shrink'
- \+/\- *lemma* caratheodory.step

Modified src/analysis/convex/cone.lean
- \+ *lemma* convex_cone.to_ordered_module
- \- *lemma* convex_cone.to_ordered_semimodule

Modified src/analysis/convex/extrema.lean


Modified src/analysis/convex/topology.lean


Modified src/analysis/normed_space/add_torsor.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/enorm.lean
- \+/\- *structure* enorm

Modified src/analysis/normed_space/euclidean_dist.lean
- \+/\- *def* to_euclidean

Modified src/analysis/normed_space/extend.lean
- \+/\- *lemma* linear_map.extend_to_𝕜'_apply

Modified src/analysis/normed_space/finite_dimension.lean
- \- *def* continuous_linear_equiv.of_findim_eq
- \+ *def* continuous_linear_equiv.of_finrank_eq
- \- *theorem* finite_dimensional.nonempty_continuous_linear_equiv_iff_findim_eq
- \+ *theorem* finite_dimensional.nonempty_continuous_linear_equiv_iff_finrank_eq
- \- *theorem* finite_dimensional.nonempty_continuous_linear_equiv_of_findim_eq
- \+ *theorem* finite_dimensional.nonempty_continuous_linear_equiv_of_finrank_eq

Modified src/analysis/normed_space/hahn_banach.lean


Modified src/analysis/normed_space/inner_product.lean
- \+/\- *lemma* exists_is_orthonormal_basis'
- \- *lemma* findim_euclidean_space
- \- *lemma* findim_euclidean_space_fin
- \- *lemma* findim_orthogonal_span_singleton
- \+ *lemma* finrank_euclidean_space
- \+ *lemma* finrank_euclidean_space_fin
- \+ *lemma* finrank_orthogonal_span_singleton
- \+/\- *def* inner_product_space.of_core
- \- *lemma* is_basis_of_orthonormal_of_card_eq_findim
- \+ *lemma* is_basis_of_orthonormal_of_card_eq_finrank
- \- *lemma* submodule.findim_add_findim_orthogonal'
- \- *lemma* submodule.findim_add_findim_orthogonal
- \- *lemma* submodule.findim_add_inf_findim_orthogonal'
- \- *lemma* submodule.findim_add_inf_findim_orthogonal
- \+ *lemma* submodule.finrank_add_finrank_orthogonal'
- \+ *lemma* submodule.finrank_add_finrank_orthogonal
- \+ *lemma* submodule.finrank_add_inf_finrank_orthogonal'
- \+ *lemma* submodule.finrank_add_inf_finrank_orthogonal

Modified src/analysis/normed_space/linear_isometry.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/seminorm.lean


Modified src/data/complex/module.lean
- \+ *lemma* complex.complex_ordered_module
- \- *lemma* complex.complex_ordered_semimodule
- \+/\- *lemma* complex.dim_real_complex
- \- *lemma* complex.findim_real_complex
- \- *lemma* complex.findim_real_complex_fact
- \+ *lemma* complex.finrank_real_complex
- \+ *lemma* complex.finrank_real_complex_fact
- \+/\- *lemma* complex.{u}
- \- *lemma* findim_real_of_complex
- \+ *lemma* finrank_real_of_complex

Modified src/data/dfinsupp.lean
- \+/\- *lemma* dfinsupp.support_smul

Modified src/data/equiv/transfer_instance.lean
- \+/\- *def* equiv.linear_equiv

Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.coe_smul
- \+/\- *lemma* finsupp.filter_smul
- \+/\- *lemma* finsupp.map_domain_smul
- \+/\- *lemma* finsupp.map_range_smul
- \+/\- *lemma* finsupp.smul_apply
- \+/\- *lemma* finsupp.smul_single
- \+/\- *lemma* finsupp.sum_smul_index'
- \+/\- *lemma* finsupp.support_smul

Modified src/data/holor.lean


Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.block_diagonal'_smul
- \+/\- *lemma* matrix.block_diagonal_smul
- \+/\- *lemma* matrix.minor_smul

Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.coeff_smul

Modified src/data/polynomial/basic.lean
- \+/\- *lemma* polynomial.lhom_ext'
- \+/\- *lemma* polynomial.smul_monomial

Modified src/data/support.lean
- \+/\- *lemma* function.support_smul
- \+/\- *lemma* function.support_smul_subset_left

Modified src/field_theory/adjoin.lean
- \- *lemma* intermediate_field.adjoin.findim
- \+ *lemma* intermediate_field.adjoin.finrank
- \+/\- *lemma* intermediate_field.bot_eq_top_of_dim_adjoin_eq_one
- \- *lemma* intermediate_field.bot_eq_top_of_findim_adjoin_eq_one
- \- *lemma* intermediate_field.bot_eq_top_of_findim_adjoin_le_one
- \+ *lemma* intermediate_field.bot_eq_top_of_finrank_adjoin_eq_one
- \+ *lemma* intermediate_field.bot_eq_top_of_finrank_adjoin_le_one
- \+/\- *lemma* intermediate_field.dim_adjoin_eq_one_iff
- \+/\- *lemma* intermediate_field.dim_adjoin_simple_eq_one_iff
- \+/\- *lemma* intermediate_field.dim_eq_one_iff
- \- *lemma* intermediate_field.findim_adjoin_eq_one_iff
- \- *lemma* intermediate_field.findim_adjoin_simple_eq_one_iff
- \- *lemma* intermediate_field.findim_eq_one_iff
- \+ *lemma* intermediate_field.finrank_adjoin_eq_one_iff
- \+ *lemma* intermediate_field.finrank_adjoin_simple_eq_one_iff
- \+ *lemma* intermediate_field.finrank_eq_one_iff
- \+/\- *lemma* intermediate_field.subsingleton_of_dim_adjoin_eq_one
- \- *lemma* intermediate_field.subsingleton_of_findim_adjoin_eq_one
- \- *lemma* intermediate_field.subsingleton_of_findim_adjoin_le_one
- \+ *lemma* intermediate_field.subsingleton_of_finrank_adjoin_eq_one
- \+ *lemma* intermediate_field.subsingleton_of_finrank_adjoin_le_one

Modified src/field_theory/finite/basic.lean


Modified src/field_theory/finite/polynomial.lean
- \+/\- *lemma* mv_polynomial.dim_R
- \- *lemma* mv_polynomial.findim_R
- \+ *lemma* mv_polynomial.finrank_R

Modified src/field_theory/fixed.lean
- \- *lemma* findim_alg_hom
- \+ *lemma* finrank_alg_hom
- \+/\- *lemma* fixed_points.dim_le_card
- \- *theorem* fixed_points.findim_eq_card
- \- *lemma* fixed_points.findim_le_card
- \+ *theorem* fixed_points.finrank_eq_card
- \+ *lemma* fixed_points.finrank_le_card

Modified src/field_theory/galois.lean
- \- *lemma* intermediate_field.findim_fixed_field_eq_card
- \+ *lemma* intermediate_field.finrank_fixed_field_eq_card
- \- *lemma* is_galois.card_aut_eq_findim
- \+ *lemma* is_galois.card_aut_eq_finrank
- \- *lemma* is_galois.card_fixing_subgroup_eq_findim
- \+ *lemma* is_galois.card_fixing_subgroup_eq_finrank
- \- *lemma* is_galois.intermediate_field.adjoin_simple.card_aut_eq_findim
- \+ *lemma* is_galois.intermediate_field.adjoin_simple.card_aut_eq_finrank
- \- *lemma* is_galois.of_card_aut_eq_findim
- \+ *lemma* is_galois.of_card_aut_eq_finrank

Modified src/field_theory/intermediate_field.lean
- \- *lemma* intermediate_field.eq_of_le_of_findim_eq'
- \- *lemma* intermediate_field.eq_of_le_of_findim_eq
- \- *lemma* intermediate_field.eq_of_le_of_findim_le'
- \- *lemma* intermediate_field.eq_of_le_of_findim_le
- \+ *lemma* intermediate_field.eq_of_le_of_finrank_eq'
- \+ *lemma* intermediate_field.eq_of_le_of_finrank_eq
- \+ *lemma* intermediate_field.eq_of_le_of_finrank_le'
- \+ *lemma* intermediate_field.eq_of_le_of_finrank_le
- \- *lemma* intermediate_field.findim_eq_findim_subalgebra
- \+ *lemma* intermediate_field.finrank_eq_finrank_subalgebra

Modified src/field_theory/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.dim_mv_polynomial

Modified src/field_theory/normal.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/tower.lean
- \- *lemma* finite_dimensional.findim_linear_map'
- \- *lemma* finite_dimensional.findim_linear_map
- \- *theorem* finite_dimensional.findim_mul_findim
- \+ *lemma* finite_dimensional.finrank_linear_map'
- \+ *lemma* finite_dimensional.finrank_linear_map
- \+ *theorem* finite_dimensional.finrank_mul_finrank

Modified src/geometry/euclidean/basic.lean
- \- *lemma* euclidean_geometry.eq_of_dist_eq_of_dist_eq_of_findim_eq_two
- \+ *lemma* euclidean_geometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
- \- *lemma* euclidean_geometry.eq_of_dist_eq_of_dist_eq_of_mem_of_findim_eq_two
- \+ *lemma* euclidean_geometry.eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two

Modified src/geometry/euclidean/circumcenter.lean


Modified src/geometry/euclidean/monge_point.lean
- \- *lemma* affine.simplex.findim_direction_altitude
- \+ *lemma* affine.simplex.finrank_direction_altitude

Modified src/geometry/manifold/algebra/smooth_functions.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/bump_function.lean
- \- *lemma* exists_embedding_findim_of_compact
- \+ *lemma* exists_embedding_finrank_of_compact
- \- *lemma* smooth_bump_covering.exists_immersion_findim
- \+ *lemma* smooth_bump_covering.exists_immersion_finrank

Modified src/geometry/manifold/instances/circle.lean


Modified src/geometry/manifold/instances/sphere.lean
- \+/\- *def* stereographic'
- \+/\- *lemma* stereographic'_source
- \+/\- *lemma* stereographic'_target
- \+/\- *lemma* times_cont_mdiff.cod_restrict_sphere
- \+/\- *lemma* times_cont_mdiff_coe_sphere
- \+/\- *lemma* times_cont_mdiff_neg_sphere

Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/group_theory/group_action/defs.lean


Modified src/group_theory/group_action/sub_mul_action.lean


Modified src/linear_algebra/affine_space/affine_equiv.lean


Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/linear_algebra/affine_space/finite_dimensional.lean
- \- *lemma* affine_independent_iff_findim_vector_span_eq
- \+ *lemma* affine_independent_iff_finrank_vector_span_eq
- \- *lemma* affine_independent_iff_le_findim_vector_span
- \+ *lemma* affine_independent_iff_le_finrank_vector_span
- \- *lemma* affine_independent_iff_not_findim_vector_span_le
- \+ *lemma* affine_independent_iff_not_finrank_vector_span_le
- \- *lemma* affine_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* affine_span_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one
- \- *lemma* affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* affine_span_eq_top_of_affine_independent_of_card_eq_finrank_add_one
- \- *lemma* affine_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* affine_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one
- \+/\- *def* collinear
- \+/\- *lemma* collinear_iff_dim_le_one
- \- *lemma* collinear_iff_findim_le_one
- \+ *lemma* collinear_iff_finrank_le_one
- \- *lemma* findim_vector_span_image_finset_le
- \- *lemma* findim_vector_span_image_finset_of_affine_independent
- \- *lemma* findim_vector_span_le_iff_not_affine_independent
- \- *lemma* findim_vector_span_of_affine_independent
- \- *lemma* findim_vector_span_range_le
- \+ *lemma* finrank_vector_span_image_finset_le
- \+ *lemma* finrank_vector_span_image_finset_of_affine_independent
- \+ *lemma* finrank_vector_span_le_iff_not_affine_independent
- \+ *lemma* finrank_vector_span_of_affine_independent
- \+ *lemma* finrank_vector_span_range_le
- \- *lemma* vector_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* vector_span_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one
- \- *lemma* vector_span_eq_top_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* vector_span_eq_top_of_affine_independent_of_card_eq_finrank_add_one
- \- *lemma* vector_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* vector_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one

Modified src/linear_algebra/affine_space/midpoint.lean
- \+/\- *lemma* midpoint_unique

Modified src/linear_algebra/affine_space/ordered.lean


Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* is_linear_map.is_linear_map_add
- \+/\- *lemma* is_linear_map.is_linear_map_sub
- \+/\- *lemma* linear_equiv.eq_bot_of_equiv
- \+/\- *def* linear_equiv.of_submodule'
- \+/\- *lemma* linear_equiv.of_submodule'_apply
- \+/\- *lemma* linear_equiv.of_submodule'_symm_apply
- \+/\- *lemma* linear_equiv.of_submodule'_to_linear_map
- \+/\- *def* linear_map.ring_lmap_equiv_self

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/bilinear_form.lean
- \+/\- *lemma* bilin_form.comp_comp
- \+/\- *lemma* bilin_form.comp_congr
- \+/\- *lemma* bilin_form.congr_comp
- \- *lemma* bilin_form.findim_add_findim_orthogonal
- \+ *lemma* bilin_form.finrank_add_finrank_orthogonal
- \+/\- *structure* bilin_form

Modified src/linear_algebra/clifford_algebra/basic.lean


Modified src/linear_algebra/dfinsupp.lean
- \+/\- *def* dfinsupp.lsum

Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_bot
- \+/\- *lemma* dim_eq_of_injective
- \+/\- *lemma* dim_eq_of_surjective
- \+/\- *lemma* dim_fin_fun
- \+/\- *lemma* dim_fun'
- \+/\- *lemma* dim_fun
- \+/\- *lemma* dim_le_of_submodule
- \+/\- *lemma* dim_le_of_surjective
- \+/\- *lemma* dim_le_one_iff
- \+/\- *lemma* dim_map_le
- \+/\- *lemma* dim_of_field
- \+/\- *lemma* dim_pi
- \+/\- *lemma* dim_pos
- \+/\- *lemma* dim_pos_iff_exists_ne_zero
- \+/\- *lemma* dim_pos_iff_nontrivial
- \+/\- *theorem* dim_prod
- \+/\- *theorem* dim_range_add_dim_ker
- \+/\- *lemma* dim_range_le
- \+/\- *lemma* dim_range_of_surjective
- \+/\- *lemma* dim_span_le
- \+/\- *lemma* dim_submodule_le
- \+/\- *lemma* dim_submodule_le_one_iff'
- \+/\- *lemma* dim_submodule_le_one_iff
- \+/\- *lemma* dim_top
- \+/\- *lemma* dim_zero_iff
- \+/\- *lemma* dim_zero_iff_forall_zero
- \+/\- *lemma* exists_is_basis_fintype
- \+/\- *lemma* exists_mem_ne_zero_of_dim_pos
- \+/\- *theorem* linear_equiv.nonempty_equiv_iff_dim_eq
- \+/\- *def* linear_equiv.of_dim_eq
- \+/\- *theorem* nonempty_linear_equiv_of_dim_eq
- \+/\- *def* rank
- \+/\- *lemma* rank_le_domain
- \+/\- *lemma* rank_le_range
- \- *def* vector_space.dim

Modified src/linear_algebra/direct_sum_module.lean


Modified src/linear_algebra/dual.lean
- \- *lemma* linear_map.findim_range_dual_map_eq_findim_range
- \+ *lemma* linear_map.finrank_range_dual_map_eq_finrank_range
- \+ *theorem* module.dual_dim_eq
- \+ *lemma* module.erange_coe
- \+ *def* module.eval_equiv
- \+ *lemma* module.eval_equiv_to_linear_map
- \+ *theorem* module.eval_ker
- \- *lemma* subspace.dual_findim_eq
- \+ *lemma* subspace.dual_finrank_eq
- \- *lemma* subspace.findim_add_findim_dual_annihilator_comap_eq
- \- *lemma* subspace.findim_dual_annihilator_comap_eq
- \+ *lemma* subspace.finrank_add_finrank_dual_annihilator_comap_eq
- \+ *lemma* subspace.finrank_dual_annihilator_comap_eq
- \- *theorem* vector_space.dual_dim_eq
- \- *lemma* vector_space.erange_coe
- \- *def* vector_space.eval_equiv
- \- *lemma* vector_space.eval_equiv_to_linear_map
- \- *theorem* vector_space.eval_ker

Modified src/linear_algebra/eigenspace.lean
- \- *lemma* module.End.generalized_eigenspace_eq_generalized_eigenspace_findim_of_le
- \+ *lemma* module.End.generalized_eigenspace_eq_generalized_eigenspace_finrank_of_le
- \- *lemma* module.End.generalized_eigenspace_le_generalized_eigenspace_findim
- \+ *lemma* module.End.generalized_eigenspace_le_generalized_eigenspace_finrank
- \- *lemma* module.End.pos_findim_generalized_eigenspace_of_has_eigenvalue
- \+ *lemma* module.End.pos_finrank_generalized_eigenspace_of_has_eigenvalue

Modified src/linear_algebra/exterior_algebra.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* bot_eq_top_of_dim_eq_zero
- \+/\- *theorem* dim_eq_zero
- \- *lemma* findim_bot
- \- *theorem* findim_eq_zero
- \- *lemma* findim_eq_zero_of_dim_eq_zero
- \- *lemma* findim_eq_zero_of_not_exists_basis
- \- *lemma* findim_span_eq_card
- \- *lemma* findim_span_le_card
- \- *lemma* findim_span_set_eq_card
- \- *lemma* findim_span_singleton
- \- *theorem* findim_top
- \- *lemma* findim_zero_iff_forall_zero
- \- *lemma* finite_dimensional.cardinal_mk_le_findim_of_linear_independent
- \+ *lemma* finite_dimensional.cardinal_mk_le_finrank_of_linear_independent
- \+/\- *lemma* finite_dimensional.dim_lt_omega
- \- *lemma* finite_dimensional.eq_of_le_of_findim_eq
- \- *lemma* finite_dimensional.eq_of_le_of_findim_le
- \+ *lemma* finite_dimensional.eq_of_le_of_finrank_eq
- \+ *lemma* finite_dimensional.eq_of_le_of_finrank_le
- \- *lemma* finite_dimensional.eq_top_of_findim_eq
- \+ *lemma* finite_dimensional.eq_top_of_finrank_eq
- \+/\- *lemma* finite_dimensional.equiv_fin_of_dim_eq
- \+/\- *lemma* finite_dimensional.fin_basis
- \- *lemma* finite_dimensional.findim_eq_card_basis'
- \- *lemma* finite_dimensional.findim_eq_card_basis
- \- *lemma* finite_dimensional.findim_eq_card_finset_basis
- \- *lemma* finite_dimensional.findim_eq_dim
- \- *lemma* finite_dimensional.findim_eq_of_dim_eq
- \- *lemma* finite_dimensional.findim_fin_fun
- \- *lemma* finite_dimensional.findim_fintype_fun_eq_card
- \- *lemma* finite_dimensional.findim_map_subtype_eq
- \- *lemma* finite_dimensional.findim_of_field
- \- *lemma* finite_dimensional.findim_of_infinite_dimensional
- \- *lemma* finite_dimensional.findim_pos
- \- *lemma* finite_dimensional.findim_pos_iff
- \- *lemma* finite_dimensional.findim_pos_iff_exists_ne_zero
- \- *lemma* finite_dimensional.findim_zero_iff
- \- *lemma* finite_dimensional.findim_zero_of_subsingleton
- \+/\- *lemma* finite_dimensional.finite_dimensional_iff_dim_lt_omega
- \- *lemma* finite_dimensional.finite_dimensional_of_findim
- \- *lemma* finite_dimensional.finite_dimensional_of_findim_eq_succ
- \+ *lemma* finite_dimensional.finite_dimensional_of_finrank
- \+ *lemma* finite_dimensional.finite_dimensional_of_finrank_eq_succ
- \+ *lemma* finite_dimensional.finrank_eq_card_basis'
- \+ *lemma* finite_dimensional.finrank_eq_card_basis
- \+ *lemma* finite_dimensional.finrank_eq_card_finset_basis
- \+ *lemma* finite_dimensional.finrank_eq_dim
- \+ *lemma* finite_dimensional.finrank_eq_of_dim_eq
- \+ *lemma* finite_dimensional.finrank_fin_fun
- \+ *lemma* finite_dimensional.finrank_fintype_fun_eq_card
- \+ *lemma* finite_dimensional.finrank_map_subtype_eq
- \+ *lemma* finite_dimensional.finrank_of_field
- \+ *lemma* finite_dimensional.finrank_of_infinite_dimensional
- \+ *lemma* finite_dimensional.finrank_pos
- \+ *lemma* finite_dimensional.finrank_pos_iff
- \+ *lemma* finite_dimensional.finrank_pos_iff_exists_ne_zero
- \+ *lemma* finite_dimensional.finrank_zero_iff
- \+ *lemma* finite_dimensional.finrank_zero_of_subsingleton
- \- *lemma* finite_dimensional.finset_card_le_findim_of_linear_independent
- \+ *lemma* finite_dimensional.finset_card_le_finrank_of_linear_independent
- \- *lemma* finite_dimensional.fintype_card_le_findim_of_linear_independent
- \+ *lemma* finite_dimensional.fintype_card_le_finrank_of_linear_independent
- \- *theorem* finite_dimensional.nonempty_linear_equiv_iff_findim_eq
- \+ *theorem* finite_dimensional.nonempty_linear_equiv_iff_finrank_eq
- \- *theorem* finite_dimensional.nonempty_linear_equiv_of_findim_eq
- \+ *theorem* finite_dimensional.nonempty_linear_equiv_of_finrank_eq
- \+/\- *lemma* finite_dimensional_of_dim_eq_one
- \+/\- *lemma* finite_dimensional_of_dim_eq_zero
- \+ *lemma* finrank_bot
- \+ *theorem* finrank_eq_zero
- \+ *lemma* finrank_eq_zero_of_dim_eq_zero
- \+ *lemma* finrank_eq_zero_of_not_exists_basis
- \+ *lemma* finrank_span_eq_card
- \+ *lemma* finrank_span_le_card
- \+ *lemma* finrank_span_set_eq_card
- \+ *lemma* finrank_span_singleton
- \+ *theorem* finrank_top
- \+ *lemma* finrank_zero_iff_forall_zero
- \- *lemma* finset_is_basis_of_linear_independent_of_card_eq_findim
- \+ *lemma* finset_is_basis_of_linear_independent_of_card_eq_finrank
- \- *lemma* finset_is_basis_of_span_eq_top_of_card_eq_findim
- \+ *lemma* finset_is_basis_of_span_eq_top_of_card_eq_finrank
- \- *lemma* is_basis_of_findim_zero'
- \- *lemma* is_basis_of_findim_zero
- \+ *lemma* is_basis_of_finrank_zero'
- \+ *lemma* is_basis_of_finrank_zero
- \- *lemma* is_basis_of_linear_independent_of_card_eq_findim
- \+ *lemma* is_basis_of_linear_independent_of_card_eq_finrank
- \- *lemma* is_basis_of_span_eq_top_of_card_eq_findim
- \+ *lemma* is_basis_of_span_eq_top_of_card_eq_finrank
- \- *theorem* linear_equiv.findim_eq
- \+ *theorem* linear_equiv.finrank_eq
- \- *lemma* linear_independent_iff_card_eq_findim_span
- \+ *lemma* linear_independent_iff_card_eq_finrank_span
- \- *lemma* linear_independent_of_span_eq_top_of_card_eq_findim
- \+ *lemma* linear_independent_of_span_eq_top_of_card_eq_finrank
- \- *theorem* linear_map.findim_le_findim_of_injective
- \- *theorem* linear_map.findim_range_add_findim_ker
- \+ *theorem* linear_map.finrank_le_finrank_of_injective
- \+ *theorem* linear_map.finrank_range_add_finrank_ker
- \- *theorem* linear_map.injective_iff_surjective_of_findim_eq_findim
- \+ *theorem* linear_map.injective_iff_surjective_of_finrank_eq_finrank
- \- *lemma* linear_map.ker_eq_bot_iff_range_eq_top_of_findim_eq_findim
- \+ *lemma* linear_map.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank
- \- *lemma* module.End.ker_pow_eq_ker_pow_findim_of_le
- \+ *lemma* module.End.ker_pow_eq_ker_pow_finrank_of_le
- \- *lemma* module.End.ker_pow_le_ker_pow_findim
- \+ *lemma* module.End.ker_pow_le_ker_pow_finrank
- \- *lemma* set_is_basis_of_linear_independent_of_card_eq_findim
- \+ *lemma* set_is_basis_of_linear_independent_of_card_eq_finrank
- \- *lemma* set_is_basis_of_span_eq_top_of_card_eq_findim
- \+ *lemma* set_is_basis_of_span_eq_top_of_card_eq_finrank
- \- *lemma* span_eq_top_of_linear_independent_of_card_eq_findim
- \+ *lemma* span_eq_top_of_linear_independent_of_card_eq_finrank
- \- *lemma* span_lt_of_subset_of_card_lt_findim
- \+ *lemma* span_lt_of_subset_of_card_lt_finrank
- \- *lemma* span_lt_top_of_card_lt_findim
- \+ *lemma* span_lt_top_of_card_lt_finrank
- \+/\- *lemma* subalgebra.bot_eq_top_of_dim_eq_one
- \- *lemma* subalgebra.bot_eq_top_of_findim_eq_one
- \+ *lemma* subalgebra.bot_eq_top_of_finrank_eq_one
- \+/\- *lemma* subalgebra.dim_bot
- \+/\- *theorem* subalgebra.dim_eq_one_iff
- \+/\- *lemma* subalgebra.dim_eq_one_of_eq_bot
- \+/\- *lemma* subalgebra.dim_top
- \+/\- *lemma* subalgebra.eq_bot_of_dim_one
- \- *lemma* subalgebra.eq_bot_of_findim_one
- \+ *lemma* subalgebra.eq_bot_of_finrank_one
- \- *lemma* subalgebra.findim_bot
- \- *theorem* subalgebra.findim_eq_one_iff
- \- *lemma* subalgebra.findim_eq_one_of_eq_bot
- \+ *lemma* subalgebra.finrank_bot
- \+ *theorem* subalgebra.finrank_eq_one_iff
- \+ *lemma* subalgebra.finrank_eq_one_of_eq_bot
- \- *lemma* subalgebra_top_findim_eq_submodule_top_findim
- \+ *lemma* subalgebra_top_finrank_eq_submodule_top_finrank
- \+/\- *theorem* submodule.dim_sup_add_dim_inf_eq
- \- *lemma* submodule.findim_add_eq_of_is_compl
- \- *lemma* submodule.findim_le
- \- *lemma* submodule.findim_lt
- \- *lemma* submodule.findim_lt_findim_of_lt
- \- *lemma* submodule.findim_mono
- \- *theorem* submodule.findim_quotient_add_findim
- \- *lemma* submodule.findim_quotient_le
- \+ *lemma* submodule.finrank_add_eq_of_is_compl
- \+ *lemma* submodule.finrank_le
- \+ *lemma* submodule.finrank_lt
- \+ *lemma* submodule.finrank_lt_finrank_of_lt
- \+ *lemma* submodule.finrank_mono
- \+ *theorem* submodule.finrank_quotient_add_finrank
- \+ *lemma* submodule.finrank_quotient_le
- \- *lemma* submodule.lt_of_le_of_findim_lt_findim
- \+ *lemma* submodule.lt_of_le_of_finrank_lt_finrank
- \- *lemma* submodule.lt_top_of_findim_lt_findim
- \+ *lemma* submodule.lt_top_of_finrank_lt_finrank

Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean
- \+/\- *def* equiv_of_dim_eq_dim
- \+/\- *lemma* finsupp.dim_eq

Modified src/linear_algebra/free_algebra.lean


Modified src/linear_algebra/free_module.lean


Modified src/linear_algebra/invariant_basis_number.lean


Modified src/linear_algebra/linear_independent.lean
- \+/\- *lemma* linear_independent.restrict_scalars

Modified src/linear_algebra/matrix.lean
- \- *lemma* linear_map.findim_linear_map
- \+ *lemma* linear_map.finrank_linear_map
- \- *lemma* matrix.findim_matrix
- \+ *lemma* matrix.finrank_matrix

Modified src/linear_algebra/multilinear.lean


Modified src/linear_algebra/pi.lean
- \+/\- *lemma* linear_map.apply_single
- \+/\- *def* linear_map.lsum

Modified src/linear_algebra/pi_tensor_product.lean


Modified src/linear_algebra/prod.lean
- \+/\- *def* linear_map.coprod_equiv
- \+/\- *lemma* linear_map.ker_coprod_of_disjoint_range
- \+/\- *lemma* linear_map.ker_prod_ker_le_ker_coprod

Modified src/linear_algebra/quadratic_form.lean


Modified src/linear_algebra/std_basis.lean


Modified src/linear_algebra/tensor_algebra.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/lp_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/order/filter/germ.lean


Modified src/representation_theory/maschke.lean


Modified src/ring_theory/derivation.lean


Modified src/ring_theory/hahn_series.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/power_basis.lean
- \- *lemma* power_basis.findim
- \+ *lemma* power_basis.finrank

Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/tensor_product.lean


Modified src/ring_theory/trace.lean
- \+/\- *lemma* algebra.trace_algebra_map

Modified src/topology/algebra/affine.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/multilinear.lean


Modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* continuous_map.smul_apply
- \+/\- *lemma* continuous_map.smul_coe

Modified src/topology/continuous_function/bounded.lean


Modified src/topology/instances/real_vector_space.lean


Modified src/topology/metric_space/pi_Lp.lean


Modified src/topology/vector_bundle.lean


Modified test/free_algebra.lean




## [2021-04-24 10:16:02](https://github.com/leanprover-community/mathlib/commit/f15887a)
chore(docs/100.yaml): mention "Erdős–Szekeres" by name ([#7353](https://github.com/leanprover-community/mathlib/pull/7353))
#### Estimated changes
Modified docs/100.yaml




## [2021-04-24 10:16:00](https://github.com/leanprover-community/mathlib/commit/767c8c5)
feat(data/int/basic): add nat_abs_ne_zero ([#7350](https://github.com/leanprover-community/mathlib/pull/7350))
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.nat_abs_ne_zero

Modified src/ring_theory/int/basic.lean




## [2021-04-24 02:33:48](https://github.com/leanprover-community/mathlib/commit/27cd5c1)
feat(group_theory/{perm/cycle_type, specific_groups/alternating_group}): the alternating group is generated by 3-cycles ([#6949](https://github.com/leanprover-community/mathlib/pull/6949))
Moves the alternating group to a new file, renames `alternating_subgroup` to `alternating_group`
Proves that any permutation whose support has cardinality 3 is a cycle
Defines `equiv.perm.is_three_cycle`
Shows that the alternating group is generated by 3-cycles
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/data/multiset/basic.lean


Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* card_support_eq_three_iff
- \+ *lemma* equiv.perm.is_swap.mul_mem_closure_three_cycles
- \+ *lemma* equiv.perm.is_three_cycle.card_support
- \+ *lemma* equiv.perm.is_three_cycle.cycle_type
- \+ *lemma* equiv.perm.is_three_cycle.inv
- \+ *lemma* equiv.perm.is_three_cycle.inv_iff
- \+ *lemma* equiv.perm.is_three_cycle.is_cycle
- \+ *lemma* equiv.perm.is_three_cycle.sign
- \+ *def* equiv.perm.is_three_cycle
- \+ *lemma* equiv.perm.is_three_cycle_swap_mul_swap_same
- \+ *lemma* equiv.perm.swap_mul_swap_same_mem_closure_three_cycles

Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean
- \- *def* alternating_subgroup
- \- *lemma* alternating_subgroup_eq_sign_ker
- \- *lemma* alternating_subgroup_normal
- \- *lemma* mem_alternating_subgroup
- \- *lemma* prod_list_swap_mem_alternating_subgroup_iff_even_length
- \- *lemma* two_mul_card_alternating_subgroup

Added src/group_theory/specific_groups/alternating.lean
- \+ *def* alternating_group
- \+ *lemma* alternating_group_eq_sign_ker
- \+ *theorem* equiv.perm.closure_three_cycles_eq_alternating
- \+ *lemma* equiv.perm.mem_alternating_group
- \+ *lemma* equiv.perm.prod_list_swap_mem_alternating_group_iff_even_length
- \+ *lemma* two_mul_card_alternating_group



## [2021-04-23 20:45:18](https://github.com/leanprover-community/mathlib/commit/bbd9362)
feat(topology/algebra): uniform continuity from 0 ([#7318](https://github.com/leanprover-community/mathlib/pull/7318))
From https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Linear.20map.20is.20continuous.20if.20it's.20continuous.20at.20zero/near/234714207, thanks to @PatrickMassot.
#### Estimated changes
Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* add_monoid_hom.uniform_continuous_of_continuous_at_zero



## [2021-04-23 15:54:59](https://github.com/leanprover-community/mathlib/commit/d89f93a)
refactor(field_theory/algebraic_closure): move complex.is_alg_closed ([#7344](https://github.com/leanprover-community/mathlib/pull/7344))
This avoids having to import half of analysis in order to talk about eigenspaces.
#### Estimated changes
Modified src/analysis/complex/polynomial.lean


Modified src/field_theory/algebraic_closure.lean




## [2021-04-23 15:54:58](https://github.com/leanprover-community/mathlib/commit/bb2e7f9)
feat(algebra/star/pi): star operates elementwise on pi types ([#7342](https://github.com/leanprover-community/mathlib/pull/7342))
#### Estimated changes
Modified src/algebra/star/algebra.lean
- \+/\- *lemma* star_smul

Added src/algebra/star/pi.lean
- \+ *lemma* pi.star_apply



## [2021-04-23 15:54:57](https://github.com/leanprover-community/mathlib/commit/a5b5f6c)
chore(algebra/opposite): add missing `monoid_with_zero` instance ([#7339](https://github.com/leanprover-community/mathlib/pull/7339))
Along with the `mul_zero_one_class` and `mul_zero_class` instances needed to build it
#### Estimated changes
Modified src/algebra/opposites.lean




## [2021-04-23 15:54:56](https://github.com/leanprover-community/mathlib/commit/6c09295)
feat(analysis/specific_limits): basic ratio test for summability of a nat-indexed family ([#7277](https://github.com/leanprover-community/mathlib/pull/7277))
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+ *lemma* le_geom
- \+ *lemma* lt_geom
- \+ *lemma* not_summable_of_ratio_norm_eventually_ge
- \+ *lemma* not_summable_of_ratio_test_tendsto_gt_one
- \+ *lemma* summable_of_ratio_norm_eventually_le
- \+ *lemma* summable_of_ratio_test_tendsto_lt_one



## [2021-04-23 11:02:02](https://github.com/leanprover-community/mathlib/commit/33ea698)
feat(linear_algebra/tensor_product): characterise range of tensor product of two linear maps ([#7340](https://github.com/leanprover-community/mathlib/pull/7340))
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+ *lemma* tensor_product.map_range_eq_span_tmul
- \+ *lemma* tensor_product.span_tmul_eq_top



## [2021-04-23 11:02:00](https://github.com/leanprover-community/mathlib/commit/227c42d)
doc(field_theory/minpoly): improve some doc-strings ([#7336](https://github.com/leanprover-community/mathlib/pull/7336))
#### Estimated changes
Modified src/field_theory/minpoly.lean
- \- *lemma* minpoly.degree_le_of_monic



## [2021-04-23 11:01:59](https://github.com/leanprover-community/mathlib/commit/3a8f9db)
feat(logic/function/basic): function.involutive.eq_iff ([#7332](https://github.com/leanprover-community/mathlib/pull/7332))
The lemma name matches the brevity of `function.injective.eq_iff`.
The fact the definitions differ isn't important, as both are accessible from `hf : involutive f` as `hf.eq_iff` and `hf.injective.eq_iff`.
#### Estimated changes
Modified src/logic/function/basic.lean




## [2021-04-23 11:01:58](https://github.com/leanprover-community/mathlib/commit/15b4fe6)
chore(algebra/iterate_hom): generalize `iterate_map_one` and `iterate_map_mul` to mul_one_class ([#7331](https://github.com/leanprover-community/mathlib/pull/7331))
#### Estimated changes
Modified src/algebra/iterate_hom.lean




## [2021-04-23 11:01:57](https://github.com/leanprover-community/mathlib/commit/4b065bf)
feat(data/matrix/basic): add lemma for assoc of mul_vec w.r.t. smul ([#7310](https://github.com/leanprover-community/mathlib/pull/7310))
Add a new lemma for the other direction of smul_mul_vec_assoc, which works on commutative rings.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.mul_vec_smul_assoc
- \+/\- *lemma* matrix.smul_mul_vec_assoc



## [2021-04-23 07:17:04](https://github.com/leanprover-community/mathlib/commit/6f3d905)
refactor(ring_theory/polynomial/content): Define is_primitive more generally ([#7316](https://github.com/leanprover-community/mathlib/pull/7316))
The lemma `is_primitive_iff_is_unit_of_C_dvd` shows that `polynomial.is_primitive` can be defined without the `gcd_monoid` assumption.
#### Estimated changes
Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/polynomial/content.lean
- \+/\- *lemma* polynomial.is_primitive.content_eq_one
- \+/\- *lemma* polynomial.is_primitive.ne_zero
- \+/\- *def* polynomial.is_primitive
- \+ *lemma* polynomial.is_primitive_iff_content_eq_one

Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/roots_of_unity.lean




## [2021-04-23 07:17:03](https://github.com/leanprover-community/mathlib/commit/5bd96ce)
feat(algebra/group/pi): pow_apply ([#7302](https://github.com/leanprover-community/mathlib/pull/7302))
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+ *lemma* pi.pow_apply



## [2021-04-23 07:17:02](https://github.com/leanprover-community/mathlib/commit/85df3a3)
refactor(group_theory/submonoid/basic): merge together similar lemmas and definitions ([#7280](https://github.com/leanprover-community/mathlib/pull/7280))
This uses `simps` to generate lots of uninteresting coe lemmas, and removes the less-bundled versions of definitions.
The main changes are:
* `add_submonoid.to_submonoid_equiv` is now just called `add_submonoid.to_submonoid`. This means we can remove the `add_submonoid.to_submonoid_mono` lemma, as that's available as `add_submonoid.to_submonoid.monotone`. Ditto for the multiplicative version.
* `simps` now knows how to handled `(add_)submonoid` objects. Unfortunately it uses `coe` as a suffix rather than a prefix, so we can't use it everywhere yet. For now we restrict its use to just these additive / multiplicative lemmas which already had `coe` as a suffix.
* `submonoid.of_add_submonoid` has been renamed to `add_submonoid.to_submonoid'` to enable dot notation.
* `add_submonoid.of_submonoid` has been renamed to `submonoid.to_add_submonoid'` to enable dot notation.
* The above points, but applied to `(add_)subgroup`
* Two new variants of the closure lemmas about `add_submonoid` (`add_submonoid.to_submonoid'_closure` and `submonoid.to_add_submonoid'_closure`), taken from [#7279](https://github.com/leanprover-community/mathlib/pull/7279)
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \- *def* add_subgroup.of_subgroup
- \+ *abbreviation* add_subgroup.to_subgroup'
- \+/\- *def* add_subgroup.to_subgroup
- \- *def* subgroup.add_subgroup_equiv
- \- *def* subgroup.of_add_subgroup
- \+ *def* subgroup.simps.coe
- \+ *abbreviation* subgroup.to_add_subgroup'
- \+/\- *def* subgroup.to_add_subgroup

Modified src/group_theory/submonoid/basic.lean
- \+ *def* submonoid.simps.coe

Modified src/group_theory/submonoid/operations.lean
- \- *def* add_submonoid.of_submonoid
- \- *lemma* add_submonoid.of_submonoid_coe
- \- *lemma* add_submonoid.of_submonoid_mono
- \- *def* add_submonoid.submonoid_equiv
- \- *lemma* add_submonoid.submonoid_equiv_coe
- \- *lemma* add_submonoid.submonoid_equiv_symm_coe
- \+ *abbreviation* add_submonoid.to_submonoid'
- \+ *lemma* add_submonoid.to_submonoid'_closure
- \+/\- *def* add_submonoid.to_submonoid
- \+/\- *lemma* add_submonoid.to_submonoid_closure
- \- *lemma* add_submonoid.to_submonoid_coe
- \- *lemma* add_submonoid.to_submonoid_mono
- \- *def* submonoid.add_submonoid_equiv
- \- *lemma* submonoid.add_submonoid_equiv_coe
- \- *lemma* submonoid.add_submonoid_equiv_symm_coe
- \- *def* submonoid.of_add_submonoid
- \- *lemma* submonoid.of_add_submonoid_coe
- \- *lemma* submonoid.of_add_submonoid_mono
- \+ *abbreviation* submonoid.to_add_submonoid'
- \+ *lemma* submonoid.to_add_submonoid'_closure
- \+/\- *def* submonoid.to_add_submonoid
- \+/\- *lemma* submonoid.to_add_submonoid_closure
- \- *lemma* submonoid.to_add_submonoid_coe
- \- *lemma* submonoid.to_add_submonoid_mono



## [2021-04-23 07:17:01](https://github.com/leanprover-community/mathlib/commit/0070d22)
feat(algebra/category/Module): mono_iff_injective ([#7100](https://github.com/leanprover-community/mathlib/pull/7100))
We should also prove `epi_iff_surjective` at some point. In the `Module` case this doesn't fall out of an adjunction, but it's still true.
#### Estimated changes
Added src/algebra/category/Module/epi_mono.lean
- \+ *lemma* Module.epi_iff_surjective
- \+ *lemma* Module.mono_iff_injective



## [2021-04-23 06:00:43](https://github.com/leanprover-community/mathlib/commit/b77916d)
feat(algebraic_geometry/Scheme): improve cosmetics of definition ([#7325](https://github.com/leanprover-community/mathlib/pull/7325))
Purely cosmetic, but the definition is going on a poster, so ...
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/topology/category/Top/open_nhds.lean
- \+ *lemma* topological_space.open_nhds.open_embedding

Modified src/topology/category/Top/opens.lean
- \- *lemma* topological_space.opens.inclusion_open_embedding
- \+ *lemma* topological_space.opens.open_embedding



## [2021-04-23 04:34:57](https://github.com/leanprover-community/mathlib/commit/40bb51e)
chore(scripts): update nolints.txt ([#7334](https://github.com/leanprover-community/mathlib/pull/7334))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-04-23 00:41:31](https://github.com/leanprover-community/mathlib/commit/2bd09f0)
chore(geometry/manifold/instances/circle): provide instance ([#7333](https://github.com/leanprover-community/mathlib/pull/7333))
Assist typeclass inference when proving the circle is a Lie group, by providing an instance.
(Mostly cosmetic, but as this proof is going on a poster I wanted to streamline.)
#### Estimated changes
Modified src/geometry/manifold/instances/circle.lean




## [2021-04-23 00:41:30](https://github.com/leanprover-community/mathlib/commit/1e1e93a)
feat(data/list/zip): distributive lemmas ([#7312](https://github.com/leanprover-community/mathlib/pull/7312))
#### Estimated changes
Modified src/data/list/zip.lean
- \+ *lemma* list.zip_with_append
- \+ *lemma* list.zip_with_comm
- \+ *lemma* list.zip_with_distrib_drop
- \+ *lemma* list.zip_with_distrib_reverse
- \+ *lemma* list.zip_with_distrib_tail
- \+ *lemma* list.zip_with_distrib_take



## [2021-04-22 20:22:25](https://github.com/leanprover-community/mathlib/commit/b401f07)
feat(src/group_theory/subgroup): add closure.submonoid.closure ([#7328](https://github.com/leanprover-community/mathlib/pull/7328))
`subgroup.closure S` equals `submonoid.closure (S ∪ S⁻¹)`.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.closure_induction''
- \+ *lemma* subgroup.closure_inv
- \+ *lemma* subgroup.closure_to_submonoid
- \+ *lemma* subgroup.inv_subset_closure
- \+ *lemma* subgroup.mem_to_submonoid

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* submonoid.mem_closure_inv



## [2021-04-22 20:22:24](https://github.com/leanprover-community/mathlib/commit/aff758e)
feat(data/nat/gcd, ring_theory/int/basic): add some basic lemmas ([#7314](https://github.com/leanprover-community/mathlib/pull/7314))
This also reduces the dependency on definitional equalities a but
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+ *theorem* nat.coprime_comm
- \+ *theorem* nat.coprime_iff_gcd_eq_one

Modified src/ring_theory/int/basic.lean
- \+ *lemma* int.coprime_iff_nat_coprime
- \+ *lemma* int.gcd_eq_nat_abs



## [2021-04-22 20:22:23](https://github.com/leanprover-community/mathlib/commit/f8464e3)
chore(computability/language): golf some proofs ([#7301](https://github.com/leanprover-community/mathlib/pull/7301))
#### Estimated changes
Modified src/computability/language.lean
- \+ *lemma* language.mem_pow
- \+ *lemma* language.mem_supr
- \+/\- *lemma* language.mul_def

Modified src/data/list/basic.lean
- \+/\- *theorem* list.join_eq_nil
- \+ *theorem* list.join_filter_empty_eq_ff
- \+ *theorem* list.join_filter_ne_nil

Modified src/data/set/lattice.lean
- \+ *lemma* set.image2_Union_left
- \+ *lemma* set.image2_Union_right

Modified src/order/complete_lattice.lean
- \+ *lemma* inf_infi_nat_succ
- \+ *lemma* sup_supr_nat_succ



## [2021-04-22 20:22:22](https://github.com/leanprover-community/mathlib/commit/0521e2b)
feat(data/list/nodup): nodup.ne_singleton_iff ([#7298](https://github.com/leanprover-community/mathlib/pull/7298))
#### Estimated changes
Modified src/data/list/nodup.lean
- \+ *lemma* list.nodup.ne_singleton_iff
- \+ *lemma* list.nth_le_eq_of_ne_imp_not_nodup



## [2021-04-22 20:22:21](https://github.com/leanprover-community/mathlib/commit/1c07dc0)
feat(algebra/big_operators): `prod_ite_of_{true, false}`. ([#7291](https://github.com/leanprover-community/mathlib/pull/7291))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_apply_ite_of_false
- \+ *lemma* finset.prod_apply_ite_of_true
- \+ *lemma* finset.prod_ite_of_false
- \+ *lemma* finset.prod_ite_of_true



## [2021-04-22 20:22:20](https://github.com/leanprover-community/mathlib/commit/a104211)
feat(data/list): suffix_cons_iff ([#7287](https://github.com/leanprover-community/mathlib/pull/7287))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.suffix_cons_iff



## [2021-04-22 20:22:19](https://github.com/leanprover-community/mathlib/commit/98ccc66)
feat(algebra/lie/tensor_product): define (binary) tensor product of Lie modules ([#7266](https://github.com/leanprover-community/mathlib/pull/7266))
#### Estimated changes
Modified src/algebra/lie/abelian.lean
- \+ *lemma* lie_module.coe_maximal_trivial_linear_map_equiv_lie_module_hom

Modified src/algebra/lie/basic.lean
- \- *lemma* bracket_apply
- \+ *lemma* lie_hom.lie_apply
- \+ *lemma* lie_module_equiv.coe_mk
- \+ *lemma* lie_module_hom.map_lie₂

Added src/algebra/lie/tensor_product.lean
- \+ *def* tensor_product.lie_module.has_bracket_aux
- \+ *lemma* tensor_product.lie_module.lie_tensor_right
- \+ *def* tensor_product.lie_module.lift
- \+ *lemma* tensor_product.lie_module.lift_apply
- \+ *def* tensor_product.lie_module.lift_lie
- \+ *lemma* tensor_product.lie_module.lift_lie_apply

Modified src/linear_algebra/tensor_product.lean
- \+ *lemma* tensor_product.lift.equiv_apply
- \+ *lemma* tensor_product.lift.equiv_symm_apply



## [2021-04-22 20:22:18](https://github.com/leanprover-community/mathlib/commit/fa49a63)
feat(set/lattice): nonempty_of_union_eq_top_of_nonempty ([#7254](https://github.com/leanprover-community/mathlib/pull/7254))
I have no idea where these lemmas belong. This is the earliest possible point. But perhaps they are too specific, and only belong at the point of use? I'm not certain here.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.exists_set_mem_of_union_eq_top
- \+ *lemma* set.nonempty_of_union_eq_top_of_nonempty



## [2021-04-22 20:22:16](https://github.com/leanprover-community/mathlib/commit/1585b14)
feat(group_theory/perm/*): Generating S_n ([#7211](https://github.com/leanprover-community/mathlib/pull/7211))
This PR proves several lemmas about generating S_n, culminating in the following result:
If H is a subgroup of S_p, and if H has cardinality divisible by p, and if H contains a transposition, then H is all of S_p.
#### Estimated changes
Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* equiv.perm.subgroup_eq_top_of_swap_mem

Modified src/group_theory/perm/cycles.lean
- \+ *lemma* equiv.perm.closure_cycle_adjacent_swap
- \+ *lemma* equiv.perm.closure_cycle_coprime_swap
- \+ *lemma* equiv.perm.closure_is_cycle
- \+ *lemma* equiv.perm.closure_prime_cycle_swap
- \- *lemma* equiv.perm.is_cycle.swap
- \+ *lemma* equiv.perm.is_cycle_swap
- \+ *lemma* equiv.perm.is_swap.is_cycle

Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.closure_is_swap
- \- *lemma* equiv.perm.closure_swaps_eq_top
- \+ *lemma* equiv.perm.support_pow_coprime



## [2021-04-22 20:22:15](https://github.com/leanprover-community/mathlib/commit/6929740)
refactor(algebra/big_operators/finprod) move finiteness assumptions to be final parameters ([#7196](https://github.com/leanprover-community/mathlib/pull/7196))
This PR takes all the finiteness hypotheses in `finprod.lean` and moves them back to be the last parameters of their lemmas. this only affects a handful of them because the API is small, and nothing else relies on it yet. This change is to allow for easier rewriting in cases where finiteness goals can be easily discharged, such as where a `fintype` instance is present. 
I also added `t` as an explicit parameter in `finprod_mem_inter_mul_diff` and the primed version, since it may be useful to invoke the lemma in cases where it can't be inferred, such as when rewriting in reverse.
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+/\- *lemma* finprod_mem_bUnion
- \+/\- *lemma* finprod_mem_inter_mul_diff'
- \+/\- *lemma* finprod_mem_inter_mul_diff
- \+/\- *lemma* finprod_mem_mul_diff'
- \+/\- *lemma* finprod_mem_mul_diff
- \+/\- *lemma* finprod_mem_sUnion
- \+/\- *lemma* finprod_mem_union''
- \+/\- *lemma* finprod_mem_union'
- \+/\- *lemma* finprod_mem_union



## [2021-04-22 20:22:14](https://github.com/leanprover-community/mathlib/commit/a1f3ff8)
feat(algebra/lie/nilpotent): basic lemmas about nilpotency ([#7181](https://github.com/leanprover-community/mathlib/pull/7181))
#### Estimated changes
Modified src/algebra/lie/ideal_operations.lean
- \+ *lemma* lie_submodule.lie_coe_mem_lie
- \+/\- *lemma* lie_submodule.lie_mem_lie

Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lie_algebra.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent
- \+ *lemma* lie_algebra.nilpotent_ad_of_nilpotent_algebra
- \+ *lemma* lie_module.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent
- \+ *lemma* lie_module.iterate_to_endomorphism_mem_lower_central_series
- \+ *lemma* lie_module.nilpotent_endo_of_nilpotent_module

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* submodule.coe_scott_continuous



## [2021-04-22 14:56:29](https://github.com/leanprover-community/mathlib/commit/a28012c)
feat(algebra/monoid_algebra): add mem.span_support ([#7323](https://github.com/leanprover-community/mathlib/pull/7323))
A (very) easy lemma about `monoid_algebra`.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.mem_span_support
- \+ *lemma* monoid_algebra.mem_span_support



## [2021-04-22 14:56:28](https://github.com/leanprover-community/mathlib/commit/3d2fec5)
feat(algebra/group_power/basic): `pow_ne_zero_iff` and `pow_pos_iff` ([#7307](https://github.com/leanprover-community/mathlib/pull/7307))
For natural `n > 0`, 
- `a ^ n ≠ 0 ↔ a ≠ 0`
- `0 < a ^ n ↔ 0 < a` where `a` is a member of a `linear_ordered_comm_monoid_with_zero`
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_ne_zero_iff

Modified src/algebra/linear_ordered_comm_group_with_zero.lean
- \+ *lemma* pow_pos_iff



## [2021-04-22 14:56:27](https://github.com/leanprover-community/mathlib/commit/1f65e42)
feat(category_theory/adjunction): reflective adjunction induces partial bijection ([#7286](https://github.com/leanprover-community/mathlib/pull/7286))
#### Estimated changes
Modified src/category_theory/adjunction/reflective.lean
- \+ *def* category_theory.unit_comp_partial_bijective
- \+ *def* category_theory.unit_comp_partial_bijective_aux
- \+ *lemma* category_theory.unit_comp_partial_bijective_aux_symm_apply
- \+ *lemma* category_theory.unit_comp_partial_bijective_natural
- \+ *lemma* category_theory.unit_comp_partial_bijective_symm_apply
- \+ *lemma* category_theory.unit_comp_partial_bijective_symm_natural



## [2021-04-22 14:56:26](https://github.com/leanprover-community/mathlib/commit/e5e0ae7)
chore(data/set/intervals/image_preimage): remove unnecessary add_comm in lemmas ([#7276](https://github.com/leanprover-community/mathlib/pull/7276))
These lemmas introduce an unexpected flip of the addition, whereas without these lemmas the simplification occurs as you might expect. Since these lemmas aren't otherwise used in mathlib, it seems simplest to just remove them.
Let me know if I'm missing something, or some reason to prefer flipping the addition.
#### Estimated changes
Modified src/data/set/intervals/image_preimage.lean
- \+/\- *lemma* set.image_add_const_Icc
- \+/\- *lemma* set.image_add_const_Ici
- \+/\- *lemma* set.image_add_const_Ico
- \+/\- *lemma* set.image_add_const_Iic
- \+/\- *lemma* set.image_add_const_Iio
- \+/\- *lemma* set.image_add_const_Ioc
- \+/\- *lemma* set.image_add_const_Ioi
- \+/\- *lemma* set.image_add_const_Ioo



## [2021-04-22 14:56:25](https://github.com/leanprover-community/mathlib/commit/56bedb4)
feat(analysis/special_functions/exp_log): `continuous_on_exp`/`pow` ([#7243](https://github.com/leanprover-community/mathlib/pull/7243))
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* complex.continuous_on_exp
- \+ *lemma* real.continuous_on_exp

Modified src/analysis/special_functions/integrals.lean


Modified src/topology/algebra/monoid.lean
- \+ *lemma* continuous_on_pow



## [2021-04-22 14:56:24](https://github.com/leanprover-community/mathlib/commit/918aea7)
refactor(algebra/ring_quot.lean): make ring_quot irreducible ([#7120](https://github.com/leanprover-community/mathlib/pull/7120))
The quotient of a ring by an equivalence relation which is compatible with the operations is still a ring. This is used to define several objects such as tensor algebras, exterior algebras, and so on, but the details of the construction are irrelevant. This PR makes `ring_quot` irreducible to keep the complexity down.
#### Estimated changes
Modified src/algebra/ring_quot.lean
- \+ *lemma* ring_quot.add_quot
- \+ *lemma* ring_quot.mul_quot
- \+ *lemma* ring_quot.neg_quot
- \+ *lemma* ring_quot.one_quot
- \+ *theorem* ring_quot.rel.star
- \+ *lemma* ring_quot.smul_quot
- \+ *lemma* ring_quot.star'_quot
- \+ *lemma* ring_quot.sub_quot
- \+ *lemma* ring_quot.zero_quot
- \+ *structure* ring_quot
- \- *def* ring_quot

Modified src/linear_algebra/clifford_algebra/conjugation.lean




## [2021-04-22 10:34:46](https://github.com/leanprover-community/mathlib/commit/5ac093c)
fix(.github/workflows): missing closing parentheses in add_label_from_*.yml ([#7320](https://github.com/leanprover-community/mathlib/pull/7320))
#### Estimated changes
Modified .github/workflows/add_label_from_comment.yml


Modified .github/workflows/add_label_from_review.yml




## [2021-04-22 10:34:45](https://github.com/leanprover-community/mathlib/commit/2deda90)
feat(data/fin): help `simp` reduce expressions containing `fin.succ_above` ([#7308](https://github.com/leanprover-community/mathlib/pull/7308))
With these `simp` lemmas, in combination with [#6897](https://github.com/leanprover-community/mathlib/pull/6897), `simp; ring` can almost automatically compute the determinant of matrices like `![![a, b], ![c, d]]`.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.one_succ_above_one
- \+ *lemma* fin.one_succ_above_succ
- \+ *lemma* fin.one_succ_above_zero
- \+ *lemma* fin.succ_succ_above_one
- \+ *lemma* fin.succ_succ_above_succ
- \+ *lemma* fin.succ_succ_above_zero



## [2021-04-22 10:34:43](https://github.com/leanprover-community/mathlib/commit/8b7014b)
fix(data/finset/lattice): sup'/inf' docstring ([#7281](https://github.com/leanprover-community/mathlib/pull/7281))
Made proper reference to `f` in the doc string.
#### Estimated changes
Modified src/data/finset/lattice.lean




## [2021-04-22 10:34:41](https://github.com/leanprover-community/mathlib/commit/8c05ff8)
feat(set_theory/surreal): add ordered_add_comm_group instance for surreal numbers ([#7270](https://github.com/leanprover-community/mathlib/pull/7270))
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers/near/235213851)
Add ordered_add_comm_group instance for surreal numbers.
#### Estimated changes
Modified src/set_theory/surreal.lean
- \- *theorem* surreal.add_assoc
- \- *theorem* surreal.add_zero
- \+ *def* surreal.neg
- \- *theorem* surreal.zero_add



## [2021-04-22 10:34:39](https://github.com/leanprover-community/mathlib/commit/96d5730)
feat(topology/continuous_function): lemmas about pointwise sup/inf ([#7249](https://github.com/leanprover-community/mathlib/pull/7249))
#### Estimated changes
Modified src/data/finset/lattice.lean
- \- *lemma* finset.inf'_apply
- \- *lemma* finset.sup'_apply

Modified src/topology/continuous_function/basic.lean
- \+ *lemma* continuous_map.inf'_apply
- \+ *lemma* continuous_map.inf'_coe
- \+ *lemma* continuous_map.inf_coe
- \+ *lemma* continuous_map.sup'_apply
- \+ *lemma* continuous_map.sup'_coe
- \+ *lemma* continuous_map.sup_coe



## [2021-04-22 10:34:37](https://github.com/leanprover-community/mathlib/commit/4591eb5)
chore(category_theory): replace has_hom with quiver ([#7151](https://github.com/leanprover-community/mathlib/pull/7151))
#### Estimated changes
Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/algebraic_geometry/presheafed_space/has_colimits.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/epi_mono.lean


Modified src/category_theory/limits/cofinal.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/has_limits.lean


Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/presheaf.lean


Modified src/category_theory/limits/shapes/terminal.lean


Modified src/category_theory/limits/yoneda.lean


Modified src/category_theory/opposites.lean
- \- *def* category_theory.has_hom.hom.op
- \- *lemma* category_theory.has_hom.hom.op_inj
- \- *lemma* category_theory.has_hom.hom.op_unop
- \- *def* category_theory.has_hom.hom.unop
- \- *lemma* category_theory.has_hom.hom.unop_inj
- \- *lemma* category_theory.has_hom.hom.unop_op
- \+ *lemma* quiver.hom.op_inj
- \+ *lemma* quiver.hom.op_unop
- \+ *lemma* quiver.hom.unop_inj
- \+ *lemma* quiver.hom.unop_op

Modified src/category_theory/yoneda.lean


Modified src/combinatorics/quiver.lean
- \+ *def* quiver.hom.op
- \+ *def* quiver.hom.unop

Modified src/tactic/elementwise.lean


Modified src/tactic/reassoc_axiom.lean


Modified src/topology/sheaves/presheaf.lean


Modified src/topology/sheaves/sheaf_condition/equalizer_products.lean


Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean




## [2021-04-22 10:34:36](https://github.com/leanprover-community/mathlib/commit/8830a20)
refactor(geometry/manifold): redefine some instances ([#7124](https://github.com/leanprover-community/mathlib/pull/7124))
* Turn `unique_diff_within_at` into a `structure`.
* Generalize `tangent_cone_at`, `unique_diff_within_at`, and `unique_diff_on` to a `semimodule` that is a `topological_space`.
* Redefine `model_with_corners_euclidean_half_space` and `model_with_corners_euclidean_quadrant` to reuse more generic lemmas, including `unique_diff_on.pi` and `unique_diff_on.univ_pi`.
* Make `model_with_corners.unique_diff'` use `target` instead of `range I`; usually it has better defeq.
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *lemma* maps_to_tangent_cone_pi
- \+/\- *lemma* unique_diff_on.pi
- \+/\- *lemma* unique_diff_on.univ_pi
- \+/\- *lemma* unique_diff_within_at.pi
- \+/\- *lemma* unique_diff_within_at.univ_pi
- \+ *structure* unique_diff_within_at
- \- *def* unique_diff_within_at

Modified src/geometry/manifold/instances/real.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean




## [2021-04-22 06:38:11](https://github.com/leanprover-community/mathlib/commit/767d248)
doc(data/finset/basic): fix confusing typo ([#7315](https://github.com/leanprover-community/mathlib/pull/7315))
#### Estimated changes
Modified src/data/finset/basic.lean




## [2021-04-22 06:38:10](https://github.com/leanprover-community/mathlib/commit/3fb9823)
feat(topology/subset_properties): variant of elim_nhds_subcover for compact_space ([#7304](https://github.com/leanprover-community/mathlib/pull/7304))
I put this in the `compact_space` namespace, although dot notation won't work so if preferred I can move it back to `_root_`.
#### Estimated changes
Modified src/topology/subset_properties.lean
- \+ *lemma* compact_space.elim_nhds_subcover



## [2021-04-22 06:38:09](https://github.com/leanprover-community/mathlib/commit/b3b74f8)
feat(data/finset/basic): list.to_finset on list ops ([#7297](https://github.com/leanprover-community/mathlib/pull/7297))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* list.card_to_finset
- \+ *lemma* list.to_finset_append
- \+ *lemma* list.to_finset_eq_iff_perm_erase_dup
- \+ *lemma* list.to_finset_eq_of_perm
- \+ *lemma* list.to_finset_reverse



## [2021-04-22 06:38:08](https://github.com/leanprover-community/mathlib/commit/55a1e65)
feat(category_theory/adjunction): construct an adjunction on the over category ([#7290](https://github.com/leanprover-community/mathlib/pull/7290))
Pretty small PR in preparation for later things.
#### Estimated changes
Added src/category_theory/adjunction/over.lean
- \+ *def* category_theory.forget_adj_star
- \+ *def* category_theory.star



## [2021-04-22 06:38:07](https://github.com/leanprover-community/mathlib/commit/d9df8fb)
chore(category_theory/subterminal): update docstring ([#7289](https://github.com/leanprover-community/mathlib/pull/7289))
#### Estimated changes
Modified src/category_theory/subterminal.lean




## [2021-04-22 06:38:05](https://github.com/leanprover-community/mathlib/commit/07e9dd4)
feat(data/nat/prime): nat.factors_eq_nil and other trivial simp lemmas ([#7284](https://github.com/leanprover-community/mathlib/pull/7284))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.factors_eq_nil
- \+ *lemma* nat.factors_one
- \+ *lemma* nat.factors_zero



## [2021-04-22 01:02:34](https://github.com/leanprover-community/mathlib/commit/6deafc2)
chore(.github/workflows): add delegated tag on comment ([#7251](https://github.com/leanprover-community/mathlib/pull/7251))
This automation should hopefully add the "delegated" tag if a maintainer types `bors d+` or `bors d=`. (In fact, it will apply the label if it sees any line starting with `bors d`, since `bors delegate+`, etc. are also allowed).
#### Estimated changes
Modified .github/workflows/add_label_from_comment.yml


Modified .github/workflows/add_label_from_review.yml




## [2021-04-22 01:02:33](https://github.com/leanprover-community/mathlib/commit/f68645f)
feat(topology/continuous_function): change formulation of separates points strongly ([#7248](https://github.com/leanprover-community/mathlib/pull/7248))
#### Estimated changes
Modified src/logic/function/basic.lean
- \- *def* separates_points
- \- *def* separates_points_strongly
- \+ *def* set.separates_points

Modified src/topology/continuous_function/algebra.lean
- \+ *def* set.separates_points_strongly



## [2021-04-22 01:02:32](https://github.com/leanprover-community/mathlib/commit/22f96fc)
chore(topology/algebra/affine): add @continuity to line_map_continuous ([#7246](https://github.com/leanprover-community/mathlib/pull/7246))
#### Estimated changes
Modified src/topology/algebra/affine.lean




## [2021-04-22 01:02:31](https://github.com/leanprover-community/mathlib/commit/afa6b72)
feat(geometry/euclidean): proof of Freek thm 55 - product of chords ([#7139](https://github.com/leanprover-community/mathlib/pull/7139))
proof of thm 55
#### Estimated changes
Modified docs/100.yaml


Added src/geometry/euclidean/sphere.lean
- \+ *lemma* euclidean_geometry.mul_dist_eq_abs_sub_sq_dist
- \+ *lemma* euclidean_geometry.mul_dist_eq_mul_dist_of_cospherical
- \+ *theorem* euclidean_geometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi
- \+ *theorem* euclidean_geometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero
- \+ *lemma* inner_product_geometry.mul_norm_eq_abs_sub_sq_norm



## [2021-04-22 01:02:29](https://github.com/leanprover-community/mathlib/commit/dac1da3)
feat(analysis/special_functions/bernstein): Weierstrass' theorem: polynomials are dense in C([0,1]) ([#6497](https://github.com/leanprover-community/mathlib/pull/6497))
# Bernstein approximations and Weierstrass' theorem
We prove that the Bernstein approximations
```
∑ k : fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.
Our proof follows Richard Beals' *Analysis, an introduction*, §7D.
The original proof, due to Bernstein in 1912, is probabilistic,
and relies on Bernoulli's theorem,
which gives bounds for how quickly the observed frequencies in a
Bernoulli trial approach the underlying probability.
The proof here does not directly rely on Bernoulli's theorem,
but can also be given a probabilistic account.
* Consider a weighted coin which with probability `x` produces heads,
  and with probability `1-x` produces tails.
* The value of `bernstein n k x` is the probability that
  such a coin gives exactly `k` heads in a sequence of `n` tosses.
* If such an appearance of `k` heads results in a payoff of `f(k / n)`,
  the `n`-th Bernstein approximation for `f` evaluated at `x` is the expected payoff.
* The main estimate in the proof bounds the probability that
  the observed frequency of heads differs from `x` by more than some `δ`,
  obtaining a bound of `(4 * n * δ^2)⁻¹`, irrespective of `x`.
* This ensures that for `n` large, the Bernstein approximation is (uniformly) close to the
  payoff function `f`.
(You don't need to think in these terms to follow the proof below: it's a giant `calc` block!)
This result proves Weierstrass' theorem that polynomials are dense in `C([0,1], ℝ)`,
although we defer an abstract statement of this until later.
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/big_operators/order.lean
- \+ *lemma* finset.prod_le_univ_prod_of_one_le'

Modified src/algebra/group_power/basic.lean
- \+/\- *theorem* sqr_le_sqr

Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* group_with_zero.mul_left_injective
- \+ *lemma* group_with_zero.mul_right_injective

Modified src/algebra/group_with_zero/power.lean
- \+ *lemma* pow_minus_two_nonneg

Modified src/algebra/ordered_monoid.lean
- \+ *lemma* pos_of_gt

Modified src/algebra/ordered_ring.lean
- \+ *lemma* mul_nonneg_le_one_le

Added src/analysis/special_functions/bernstein.lean
- \+ *lemma* bernstein.probability
- \+ *lemma* bernstein.variance
- \+ *def* bernstein.z
- \+ *def* bernstein
- \+ *lemma* bernstein_apply
- \+ *def* bernstein_approximation.S
- \+ *lemma* bernstein_approximation.apply
- \+ *lemma* bernstein_approximation.le_of_mem_S_compl
- \+ *lemma* bernstein_approximation.lt_of_mem_S
- \+ *def* bernstein_approximation.δ
- \+ *def* bernstein_approximation
- \+ *theorem* bernstein_approximation_uniform
- \+ *lemma* bernstein_nonneg

Modified src/data/fintype/card.lean
- \+ *theorem* finset.prod_range

Modified src/ring_theory/polynomial/bernstein.lean
- \+ *lemma* bernstein_polynomial.variance

Added src/topology/continuous_function/polynomial.lean
- \+ *def* polynomial.to_continuous_map
- \+ *def* polynomial.to_continuous_map_on



## [2021-04-21 19:58:09](https://github.com/leanprover-community/mathlib/commit/f2984d5)
fix(data/{finsupp,polynomial,mv_polynomial}/basic): add missing decidable arguments ([#7309](https://github.com/leanprover-community/mathlib/pull/7309))
Lemmas with an `ite` in their conclusion should not use `classical.dec` or similar, instead inferring an appropriate decidability instance from their context. This eliminates a handful of converts elsewhere.
The linter in [#6485](https://github.com/leanprover-community/mathlib/pull/6485) should eventually find these automatically.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.single_apply

Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.support_monomial

Modified src/data/polynomial/basic.lean


Modified src/linear_algebra/basis.lean
- \+/\- *lemma* is_basis.repr_self_apply

Modified src/linear_algebra/dual.lean




## [2021-04-21 19:58:08](https://github.com/leanprover-community/mathlib/commit/120be3d)
feat(data/list/zip): map_zip_with ([#7295](https://github.com/leanprover-community/mathlib/pull/7295))
#### Estimated changes
Modified src/data/list/zip.lean
- \+ *lemma* list.map_zip_with



## [2021-04-21 19:58:07](https://github.com/leanprover-community/mathlib/commit/253d4f5)
feat(analysis/normed_space/dual): generalize to seminormed space ([#7262](https://github.com/leanprover-community/mathlib/pull/7262))
We generalize here the Hahn-Banach theorem and the notion of dual space to `semi_normed_space`.
#### Estimated changes
Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/hahn_banach.lean
- \+/\- *lemma* norm'_def



## [2021-04-21 19:58:06](https://github.com/leanprover-community/mathlib/commit/700d477)
feat(analysis/special_functions/integrals): integral_comp for `f : ℝ → ℝ` ([#7216](https://github.com/leanprover-community/mathlib/pull/7216))
In [#7103](https://github.com/leanprover-community/mathlib/pull/7103) I added lemmas to deal with integrals of the form `c • ∫ x in a..b, f (c * x + d)`. However, it came to my attention that, with those lemmas, `simp` can only handle such integrals if they use `•`, not `*`. To solve this problem and enable computation of these integrals by `simp`, I add versions of the aforementioned `integral_comp` lemmas specialized with `f : ℝ → ℝ` and label them with `simp`.
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+/\- *lemma* interval_integral.integral_const_mul
- \+/\- *lemma* interval_integral.integral_div
- \+/\- *lemma* interval_integral.integral_mul_const
- \+ *lemma* interval_integral.inv_mul_integral_comp_add_div
- \+ *lemma* interval_integral.inv_mul_integral_comp_div
- \+ *lemma* interval_integral.inv_mul_integral_comp_div_add
- \+ *lemma* interval_integral.inv_mul_integral_comp_div_sub
- \+ *lemma* interval_integral.inv_mul_integral_comp_sub_div
- \+ *lemma* interval_integral.mul_integral_comp_add_mul
- \+ *lemma* interval_integral.mul_integral_comp_mul_add
- \+ *lemma* interval_integral.mul_integral_comp_mul_left
- \+ *lemma* interval_integral.mul_integral_comp_mul_right
- \+ *lemma* interval_integral.mul_integral_comp_mul_sub
- \+ *lemma* interval_integral.mul_integral_comp_sub_mul

Modified src/measure_theory/interval_integral.lean
- \- *lemma* interval_integral.integral_comp_add_div'
- \- *lemma* interval_integral.integral_comp_add_mul'
- \- *lemma* interval_integral.integral_comp_div'
- \- *lemma* interval_integral.integral_comp_div_add'
- \- *lemma* interval_integral.integral_comp_div_sub'
- \- *lemma* interval_integral.integral_comp_mul_add'
- \- *lemma* interval_integral.integral_comp_mul_left'
- \- *lemma* interval_integral.integral_comp_mul_right'
- \- *lemma* interval_integral.integral_comp_mul_sub'
- \- *lemma* interval_integral.integral_comp_sub_div'
- \- *lemma* interval_integral.integral_comp_sub_mul'
- \+/\- *lemma* interval_integral.integral_smul
- \+ *lemma* interval_integral.inv_smul_integral_comp_add_div
- \+ *lemma* interval_integral.inv_smul_integral_comp_div
- \+ *lemma* interval_integral.inv_smul_integral_comp_div_add
- \+ *lemma* interval_integral.inv_smul_integral_comp_div_sub
- \+ *lemma* interval_integral.inv_smul_integral_comp_sub_div
- \+ *lemma* interval_integral.smul_integral_comp_add_mul
- \+ *lemma* interval_integral.smul_integral_comp_mul_add
- \+ *lemma* interval_integral.smul_integral_comp_mul_left
- \+ *lemma* interval_integral.smul_integral_comp_mul_right
- \+ *lemma* interval_integral.smul_integral_comp_mul_sub
- \+ *lemma* interval_integral.smul_integral_comp_sub_mul

Modified test/integration.lean




## [2021-04-21 19:58:05](https://github.com/leanprover-community/mathlib/commit/721e0b9)
feat(order/complete_lattice): independence of an indexed family ([#7199](https://github.com/leanprover-community/mathlib/pull/7199))
This PR reclaims the concept of `independent` for elements of a complete lattice. 
Right now it's defined on subsets -- a subset of a complete lattice L is independent if every
element of it is disjoint from (i.e. bot is the meet of it with) the Sup of all the other elements. 
The problem with this is that if you have an indexed family f:I->L of elements of L then
duplications get lost if you ask for the image of f to be independent (rather like the issue
with a basis of a vector space being a subset rather than an indexed family). This is
an issue when defining gradings on rings, for example: if M is a monoid and R is
a ring, then I don't want the map which sends every m to (top : subgroup R) to
be independent. 
I have renamed the set-theoretic version of `independent` to `set_independent`
#### Estimated changes
Modified src/order/compactly_generated.lean
- \- *lemma* complete_lattice.independent_Union_of_directed
- \- *theorem* complete_lattice.independent_iff_finite
- \+ *lemma* complete_lattice.set_independent_Union_of_directed
- \+ *theorem* complete_lattice.set_independent_iff_finite

Modified src/order/complete_lattice.lean
- \+ *theorem* bsupr_le_bsupr'
- \+ *lemma* complete_lattice.independent.comp
- \+/\- *lemma* complete_lattice.independent.disjoint
- \- *lemma* complete_lattice.independent.disjoint_Sup
- \+ *lemma* complete_lattice.independent.disjoint_bsupr
- \+ *lemma* complete_lattice.independent.mono
- \- *theorem* complete_lattice.independent.mono
- \+/\- *def* complete_lattice.independent
- \+ *theorem* complete_lattice.independent_def''
- \+ *theorem* complete_lattice.independent_def'
- \+ *theorem* complete_lattice.independent_def
- \+/\- *lemma* complete_lattice.independent_empty
- \+ *lemma* complete_lattice.independent_pempty
- \+ *lemma* complete_lattice.set_independent.disjoint
- \+ *lemma* complete_lattice.set_independent.disjoint_Sup
- \+ *theorem* complete_lattice.set_independent.mono
- \+ *def* complete_lattice.set_independent
- \+ *lemma* complete_lattice.set_independent_empty
- \+ *lemma* complete_lattice.set_independent_iff



## [2021-04-21 19:58:03](https://github.com/leanprover-community/mathlib/commit/66220ac)
chore(tactic/elementwise): fixes ([#7188](https://github.com/leanprover-community/mathlib/pull/7188))
These fixes, while an improvement, still don't fix the problem @justus-springer observed in [#7092](https://github.com/leanprover-community/mathlib/pull/7092).
Really we should generate a second copy of the `_apply` lemma, with the category specialized to `Type u`, and in that one remove all the coercions. Maybe later.
#### Estimated changes
Modified src/category_theory/concrete_category/basic.lean
- \+ *lemma* category_theory.concrete_category.has_coe_to_fun_Type

Modified src/tactic/elementwise.lean


Modified test/elementwise.lean




## [2021-04-21 09:38:17](https://github.com/leanprover-community/mathlib/commit/f08fe5f)
doc(data/quot): promote a comment to a docstring ([#7306](https://github.com/leanprover-community/mathlib/pull/7306))
#### Estimated changes
Modified src/data/quot.lean




## [2021-04-21 09:38:16](https://github.com/leanprover-community/mathlib/commit/7db1181)
feat(data/dfinsupp): copy map_range defs from finsupp ([#7293](https://github.com/leanprover-community/mathlib/pull/7293))
This adds the bundled homs:
* `dfinsupp.map_range.add_monoid_hom`
* `dfinsupp.map_range.add_equiv`
* `dfinsupp.map_range.linear_map`
* `dfinsupp.map_range.linear_equiv`
and lemmas
* `dfinsupp.map_range_zero`
* `dfinsupp.map_range_add`
* `dfinsupp.map_range_smul`
For which we already have identical lemmas for `finsupp`.
Split from [#7217](https://github.com/leanprover-community/mathlib/pull/7217), since `map_range.add_equiv` can be used in conjunction with `submonoid.mrange_restrict`
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.coe_zero
- \+ *def* dfinsupp.map_range.add_equiv
- \+ *lemma* dfinsupp.map_range.add_equiv_refl
- \+ *lemma* dfinsupp.map_range.add_equiv_symm
- \+ *lemma* dfinsupp.map_range.add_equiv_trans
- \+ *def* dfinsupp.map_range.add_monoid_hom
- \+ *lemma* dfinsupp.map_range.add_monoid_hom_comp
- \+ *lemma* dfinsupp.map_range.add_monoid_hom_id
- \+ *lemma* dfinsupp.map_range_add
- \+ *lemma* dfinsupp.map_range_comp
- \+ *lemma* dfinsupp.map_range_id
- \+ *lemma* dfinsupp.map_range_zero
- \+/\- *lemma* dfinsupp.zero_apply

Modified src/linear_algebra/dfinsupp.lean
- \+ *def* dfinsupp.map_range.linear_equiv
- \+ *lemma* dfinsupp.map_range.linear_equiv_refl
- \+ *lemma* dfinsupp.map_range.linear_equiv_symm
- \+ *lemma* dfinsupp.map_range.linear_equiv_trans
- \+ *def* dfinsupp.map_range.linear_map
- \+ *lemma* dfinsupp.map_range.linear_map_comp
- \+ *lemma* dfinsupp.map_range.linear_map_id
- \+ *lemma* dfinsupp.map_range_smul



## [2021-04-21 09:38:15](https://github.com/leanprover-community/mathlib/commit/80028f3)
feat(data/finset/lattice): add `comp_sup'_eq_sup'_comp`, golf some proofs ([#7275](https://github.com/leanprover-community/mathlib/pull/7275))
The proof is just a very marginally generalized version of the previous proof for `sup'_apply`.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.comp_inf'_eq_inf'_comp
- \+ *lemma* finset.comp_sup'_eq_sup'_comp



## [2021-04-21 04:20:35](https://github.com/leanprover-community/mathlib/commit/9b8d6e4)
feat(category_theory/monoidal): Drinfeld center ([#7186](https://github.com/leanprover-community/mathlib/pull/7186))
# Half braidings and the Drinfeld center of a monoidal category
We define `center C` to be pairs `⟨X, b⟩`, where `X : C` and `b` is a half-braiding on `X`.
We show that `center C` is braided monoidal,
and provide the monoidal functor `center.forget` from `center C` back to `C`.
## Future work
Verifying the various axioms here is done by tedious rewriting.
Using the `slice` tactic may make the proofs marginally more readable.
More exciting, however, would be to make possible one of the following options:
1. Integration with homotopy.io / globular to give "picture proofs".
2. The monoidal coherence theorem, so we can ignore associators
   (after which most of these proofs are trivial;
   I'm unsure if the monoidal coherence theorem is even usable in dependent type theory).
3. Automating these proofs using `rewrite_search` or some relative.
#### Estimated changes
Modified src/category_theory/monoidal/category.lean
- \+ *lemma* category_theory.monoidal_category.hom_inv_id_tensor
- \+ *lemma* category_theory.monoidal_category.id_tensor_associator_inv_naturality
- \+ *lemma* category_theory.monoidal_category.id_tensor_associator_naturality
- \+ *lemma* category_theory.monoidal_category.inv_hom_id_tensor
- \+ *lemma* category_theory.monoidal_category.tensor_hom_inv_id
- \+ *lemma* category_theory.monoidal_category.tensor_inv_hom_id

Added src/category_theory/monoidal/center.lean
- \+ *def* category_theory.center.associator
- \+ *lemma* category_theory.center.associator_hom_f
- \+ *lemma* category_theory.center.associator_inv_f
- \+ *def* category_theory.center.braiding
- \+ *lemma* category_theory.center.comp_f
- \+ *def* category_theory.center.forget
- \+ *structure* category_theory.center.hom
- \+ *lemma* category_theory.center.id_f
- \+ *def* category_theory.center.iso_mk
- \+ *def* category_theory.center.left_unitor
- \+ *lemma* category_theory.center.left_unitor_hom_f
- \+ *lemma* category_theory.center.left_unitor_inv_f
- \+ *def* category_theory.center.right_unitor
- \+ *lemma* category_theory.center.right_unitor_hom_f
- \+ *lemma* category_theory.center.right_unitor_inv_f
- \+ *lemma* category_theory.center.tensor_f
- \+ *lemma* category_theory.center.tensor_fst
- \+ *def* category_theory.center.tensor_hom
- \+ *def* category_theory.center.tensor_obj
- \+ *def* category_theory.center.tensor_unit
- \+ *lemma* category_theory.center.tensor_β
- \+ *def* category_theory.center
- \+ *structure* category_theory.half_braiding



## [2021-04-21 04:20:34](https://github.com/leanprover-community/mathlib/commit/923314f)
refactor(order/well_founded_set): partially well ordered sets using relations other than `has_le.le` ([#7131](https://github.com/leanprover-community/mathlib/pull/7131))
Introduces `set.partially_well_ordered_on` to generalize `set.is_partially_well_ordered` to relations that do not necessarily come from a `has_le` instance
Renames `set.is_partially_well_ordered` to `set.is_pwo` in analogy with `set.is_wf`
Prepares to refactor Hahn series to use `set.is_pwo` and avoid the assumption of a linear order
#### Estimated changes
Modified src/order/rel_classes.lean


Modified src/order/well_founded_set.lean
- \+ *theorem* finset.is_pwo
- \+ *theorem* finset.partially_well_ordered_on
- \+ *theorem* finset.well_founded_on
- \- *theorem* not_well_founded_swap_of_infinite_of_well_order
- \- *theorem* set.is_partially_well_ordered.exists_monotone_subseq
- \- *theorem* set.is_partially_well_ordered.image_of_monotone
- \- *lemma* set.is_partially_well_ordered.is_wf
- \- *theorem* set.is_partially_well_ordered.mul
- \- *lemma* set.is_partially_well_ordered.prod
- \- *def* set.is_partially_well_ordered
- \- *theorem* set.is_partially_well_ordered_iff_exists_monotone_subseq
- \+ *theorem* set.is_pwo.exists_monotone_subseq
- \+ *theorem* set.is_pwo.image_of_monotone
- \+ *lemma* set.is_pwo.is_wf
- \+ *theorem* set.is_pwo.mul
- \+ *lemma* set.is_pwo.prod
- \+ *def* set.is_pwo
- \+ *theorem* set.is_pwo_iff_exists_monotone_subseq
- \- *theorem* set.is_wf.is_partially_well_ordered
- \+ *theorem* set.is_wf.is_pwo
- \+ *theorem* set.is_wf_iff_is_pwo
- \+ *lemma* set.mul_antidiagonal.eq_of_fst_le_fst_of_snd_le_snd
- \+ *theorem* set.mul_antidiagonal.finite_of_is_pwo
- \+/\- *theorem* set.mul_antidiagonal.finite_of_is_wf
- \- *def* set.mul_antidiagonal.fst_rel_embedding
- \- *def* set.mul_antidiagonal.lt_left
- \- *def* set.mul_antidiagonal.snd_rel_embedding
- \+ *theorem* set.partially_well_ordered_on.exists_monotone_subseq
- \+ *theorem* set.partially_well_ordered_on.image_of_monotone
- \+ *lemma* set.partially_well_ordered_on.well_founded_on
- \+ *def* set.partially_well_ordered_on
- \+ *theorem* set.partially_well_ordered_on_iff_exists_monotone_subseq
- \+ *theorem* set.well_founded_on_iff_no_descending_seq



## [2021-04-21 04:20:32](https://github.com/leanprover-community/mathlib/commit/02a3133)
feat(group_theory/{order_of_element, perm/cycles}): two cycles are conjugate iff their supports have the same size ([#7024](https://github.com/leanprover-community/mathlib/pull/7024))
Separates out the `equiv`s from several proofs in `group_theory/order_of_element`.
The equivs defined: `fin_equiv_powers`, `fin_equiv_gpowers`, `powers_equiv_powers`, `gpowers_equiv_gpowers`.
Shows that two cyclic permutations are conjugate if and only if their supports have the same `finset.card`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.subtype_congr

Modified src/data/equiv/fintype.lean
- \+ *lemma* equiv.extend_subtype_apply_of_mem
- \+ *lemma* equiv.extend_subtype_apply_of_not_mem
- \+ *lemma* equiv.extend_subtype_mem
- \+ *lemma* equiv.extend_subtype_not_mem

Modified src/data/set/finite.lean
- \+ *lemma* fintype.card_compl_eq_card_compl
- \+ *lemma* fintype.card_subtype_compl

Modified src/group_theory/order_of_element.lean
- \+ *lemma* fin_equiv_gmultiples_apply
- \+ *lemma* fin_equiv_gmultiples_symm_apply
- \+ *lemma* fin_equiv_gpowers_apply
- \+ *lemma* fin_equiv_gpowers_symm_apply
- \+ *lemma* fin_equiv_multiples_apply
- \+ *lemma* fin_equiv_multiples_symm_apply
- \+ *lemma* fin_equiv_powers_apply
- \+ *lemma* fin_equiv_powers_symm_apply
- \+ *lemma* gmultiples_equiv_gmultiples_apply
- \+ *lemma* gpowers_equiv_gpowers_apply
- \+ *lemma* multiples_equiv_multiples_apply
- \+ *lemma* powers_equiv_powers_apply

Modified src/group_theory/perm/cycles.lean
- \+ *lemma* equiv.perm.is_conj_of_support_equiv
- \+ *lemma* equiv.perm.is_cycle.gpowers_equiv_support_apply
- \+ *lemma* equiv.perm.is_cycle.gpowers_equiv_support_symm_apply
- \+ *theorem* equiv.perm.is_cycle.is_conj
- \+ *theorem* equiv.perm.is_cycle.is_conj_iff

Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.gpow_apply_mem_support
- \+ *lemma* equiv.perm.pow_apply_mem_support



## [2021-04-21 00:48:48](https://github.com/leanprover-community/mathlib/commit/8481bf4)
feat(algebra/algebra/basic): add alg_hom.apply ([#7278](https://github.com/leanprover-community/mathlib/pull/7278))
This also renames some variables from α to R for readability
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* pi.alg_hom.apply
- \+/\- *lemma* pi.algebra_map_apply



## [2021-04-21 00:48:47](https://github.com/leanprover-community/mathlib/commit/4abf961)
feat(algebra/big_operators): product over coerced fintype ([#7236](https://github.com/leanprover-community/mathlib/pull/7236))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_finset_coe
- \+ *lemma* finset.prod_subtype
- \+ *lemma* fintype.prod_finset_coe

Modified src/data/fintype/card.lean
- \- *lemma* finset.prod_subtype



## [2021-04-21 00:48:46](https://github.com/leanprover-community/mathlib/commit/ad58861)
refactor(group_theory/submonoid): adjust definitional unfolding of add_monoid_hom.mrange to match set.range ([#7227](https://github.com/leanprover-community/mathlib/pull/7227))
This changes the following to unfold to `set.range`:
* `monoid_hom.mrange`
* `add_monoid_hom.mrange`
* `linear_map.range`
* `lie_hom.range`
* `ring_hom.range`
* `ring_hom.srange`
* `ring_hom.field_range`
* `alg_hom.range`
For example:
```lean
import ring_theory.subring
variables (R : Type*) [ring R] (f : R →+* R)
-- before this PR, these required `f '' univ` on the RHS
example : (f.range : set R) = set.range f := rfl
example : (f.srange : set R) = set.range f := rfl
example : (f.to_monoid_hom.mrange : set R) = set.range f := rfl
-- this one is unchanged by this PR
example : (f.to_add_monoid_hom.range : set R) = set.range f := rfl
```
The motivations behind this change are that
* It eliminates a lot of `∈ set.univ` hypotheses and goals that are just annoying
* it means that an equivalence like `A ≃ set.range f` is defeq to `A ≃ f.range`, with no need to insert awkward `equiv.cast`-like terms to translate between different approaches
* `monoid_hom.range` (as opposed to `mrange`) already used this pattern.
The number of lines has gone up a bit, but most of those are comments explaining the design choice.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60set.2Erange.20f.60.20vs.20.60f.20''.20univ.60/near/234893679)
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/algebra/tower.lean


Modified src/algebra/lie/nilpotent.lean


Modified src/algebra/lie/solvable.lean


Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_hom.range_eq_map

Modified src/algebra/lie/submodule.lean
- \+/\- *def* lie_hom.ideal_range
- \+ *lemma* lie_hom.ideal_range_eq_map
- \+/\- *lemma* lie_hom.map_le_ideal_range
- \+/\- *lemma* lie_hom.mem_ideal_range

Modified src/field_theory/adjoin.lean


Modified src/field_theory/minpoly.lean


Modified src/field_theory/normal.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/subfield.lean
- \+/\- *lemma* ring_hom.coe_field_range
- \+/\- *def* ring_hom.field_range
- \+ *lemma* ring_hom.field_range_eq_map
- \+/\- *lemma* ring_hom.mem_field_range
- \+/\- *def* ring_hom.range_restrict_field

Modified src/group_theory/congruence.lean


Modified src/group_theory/submonoid/membership.lean


Modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* monoid_hom.coe_mrange
- \+/\- *def* monoid_hom.mrange
- \+/\- *lemma* monoid_hom.mrange_eq_map
- \+/\- *lemma* submonoid.mrange_inl
- \+/\- *lemma* submonoid.mrange_inr

Modified src/linear_algebra/basic.lean
- \+/\- *theorem* linear_map.mem_range
- \+/\- *theorem* linear_map.mem_range_self
- \+/\- *def* linear_map.range
- \+/\- *theorem* linear_map.range_coe
- \+ *lemma* linear_map.range_eq_map
- \+/\- *theorem* linear_map.range_id
- \+/\- *theorem* submodule.map_top

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/prod.lean


Modified src/ring_theory/adjoin/basic.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/subring.lean
- \+/\- *lemma* ring_hom.coe_range
- \+/\- *lemma* ring_hom.mem_range
- \+/\- *def* ring_hom.range
- \+ *lemma* ring_hom.range_eq_map

Modified src/ring_theory/subsemiring.lean
- \+/\- *lemma* ring_hom.coe_srange
- \+/\- *def* ring_hom.srange
- \+ *lemma* ring_hom.srange_eq_map



## [2021-04-20 11:17:03](https://github.com/leanprover-community/mathlib/commit/9bdc555)
feat(algebraic_geometry/prime_spectrum): More lemmas ([#7244](https://github.com/leanprover-community/mathlib/pull/7244))
Adding and refactoring some lemmas about zero loci and basic opens. Also adds three lemmas in `ideal/basic.lean`.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean
- \+/\- *lemma* prime_spectrum.basic_open_eq_zero_locus_compl
- \+ *lemma* prime_spectrum.basic_open_mul
- \+ *lemma* prime_spectrum.basic_open_one
- \+ *lemma* prime_spectrum.basic_open_pow
- \+ *lemma* prime_spectrum.basic_open_zero
- \+ *lemma* prime_spectrum.mem_basic_open
- \+ *lemma* prime_spectrum.vanishing_ideal_closure
- \+ *lemma* prime_spectrum.zero_locus_mul
- \+ *lemma* prime_spectrum.zero_locus_pow
- \+ *lemma* prime_spectrum.zero_locus_radical
- \+ *lemma* prime_spectrum.zero_locus_singleton_mul
- \+ *lemma* prime_spectrum.zero_locus_singleton_one
- \+ *lemma* prime_spectrum.zero_locus_singleton_pow

Modified src/ring_theory/ideal/basic.lean
- \+ *theorem* ideal.is_prime.mul_mem_iff_mem_or_mem
- \+ *theorem* ideal.is_prime.pow_mem_iff_mem
- \+ *lemma* ideal.pow_mem_of_mem



## [2021-04-20 11:17:02](https://github.com/leanprover-community/mathlib/commit/39d23b8)
feat(logic/basic): exists_or_eq_{left,right} ([#7224](https://github.com/leanprover-community/mathlib/pull/7224))
#### Estimated changes
Modified src/data/list/sigma.lean


Modified src/logic/basic.lean
- \+ *lemma* exists_or_eq_left'
- \+ *lemma* exists_or_eq_left
- \+ *lemma* exists_or_eq_right'
- \+ *lemma* exists_or_eq_right



## [2021-04-20 09:55:49](https://github.com/leanprover-community/mathlib/commit/bf22ab3)
feat(linear_algebra/bilinear_form): Unique adjoints with respect to a nondegenerate bilinear form ([#7071](https://github.com/leanprover-community/mathlib/pull/7071))
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* bilin_form.comp_left_injective
- \+ *lemma* bilin_form.comp_symm_comp_of_nondegenerate_apply
- \+ *theorem* bilin_form.is_adjoint_pair_iff_eq_of_nondegenerate
- \+ *lemma* bilin_form.is_adjoint_pair_left_adjoint_of_nondegenerate
- \+ *lemma* bilin_form.is_adjoint_pair_unique_of_nondegenerate
- \+ *lemma* bilin_form.symm_comp_of_nondegenerate_left_apply



## [2021-04-20 07:56:28](https://github.com/leanprover-community/mathlib/commit/a4f59bd)
feat(category_theory/subobject): easy facts about the top subobject ([#7267](https://github.com/leanprover-community/mathlib/pull/7267))
#### Estimated changes
Modified src/category_theory/subobject/lattice.lean
- \+ *lemma* category_theory.subobject.eq_top_of_is_iso_arrow
- \+ *lemma* category_theory.subobject.is_iso_arrow_iff_eq_top
- \+ *lemma* category_theory.subobject.is_iso_iff_mk_eq_top
- \+/\- *lemma* category_theory.subobject.map_top
- \+ *lemma* category_theory.subobject.mk_eq_top_of_is_iso
- \+/\- *lemma* category_theory.subobject.top_eq_id



## [2021-04-20 07:56:27](https://github.com/leanprover-community/mathlib/commit/0c721d5)
feat(algebra/lie/abelian): expand API for `lie_module.maximal_trivial_submodule` ([#7235](https://github.com/leanprover-community/mathlib/pull/7235))
#### Estimated changes
Modified src/algebra/lie/abelian.lean
- \+ *lemma* lie_module.coe_maximal_trivial_equiv_apply
- \+ *lemma* lie_module.coe_maximal_trivial_hom_apply
- \+ *lemma* lie_module.coe_maximal_trivial_linear_map_equiv_lie_module_hom_apply
- \+ *lemma* lie_module.coe_maximal_trivial_linear_map_equiv_lie_module_hom_symm_apply
- \+ *def* lie_module.maximal_trivial_equiv
- \+ *lemma* lie_module.maximal_trivial_equiv_of_equiv_symm_eq_symm
- \+ *lemma* lie_module.maximal_trivial_equiv_of_refl_eq_refl
- \+ *def* lie_module.maximal_trivial_hom
- \+ *def* lie_module.maximal_trivial_linear_map_equiv_lie_module_hom

Modified src/algebra/lie/basic.lean
- \+ *lemma* lie_module_equiv.ext
- \+ *lemma* lie_module_equiv.to_equiv_injective
- \+/\- *structure* lie_module_equiv



## [2021-04-20 07:56:26](https://github.com/leanprover-community/mathlib/commit/944ffff)
chore(combinatorics/quiver): make quiver a class ([#7150](https://github.com/leanprover-community/mathlib/pull/7150))
#### Estimated changes
Modified src/combinatorics/quiver.lean
- \- *def* quiver.arrow.reverse
- \- *def* quiver.arrow.to_path
- \+ *def* quiver.empty
- \+/\- *lemma* quiver.empty_arrow
- \+/\- *def* quiver.geodesic_subtree
- \+ *def* quiver.hom.to_path
- \+/\- *def* quiver.labelling
- \- *lemma* quiver.opposite_arrow
- \- *lemma* quiver.opposite_opposite
- \+/\- *def* quiver.path.comp
- \+/\- *lemma* quiver.path.comp_assoc
- \+/\- *lemma* quiver.path.comp_cons
- \+/\- *lemma* quiver.path.comp_nil
- \+/\- *def* quiver.path.length
- \+/\- *lemma* quiver.path.length_cons
- \+/\- *lemma* quiver.path.nil_comp
- \+/\- *def* quiver.path.reverse
- \+/\- *inductive* quiver.path
- \+ *def* quiver.reverse
- \+ *def* quiver.root
- \+/\- *lemma* quiver.shortest_path_spec
- \- *lemma* quiver.sum_arrow
- \+/\- *def* quiver.symmetrify
- \- *lemma* quiver.symmetrify_arrow
- \+ *structure* quiver.total
- \+/\- *def* quiver.weakly_connected_component
- \+/\- *def* quiver.wide_subquiver_equiv_set_total
- \+/\- *def* quiver.wide_subquiver_symmetrify
- \- *structure* quiver
- \- *def* wide_subquiver.quiver
- \+ *def* wide_subquiver.to_Type
- \+/\- *def* wide_subquiver



## [2021-04-20 07:56:25](https://github.com/leanprover-community/mathlib/commit/5e188d2)
feat(category_theory/abelian): definition of projective object ([#7108](https://github.com/leanprover-community/mathlib/pull/7108))
This is extracted from @TwoFX's `projective` branch, with some slight tweaks (make things `Prop` valued classes), and documentation.
This is just the definition of `projective` and `enough_projectives`, with no attempt to construct projective resolutions. I want this in place because constructing projective resolutions will hopefully be a good test of experiments with chain complexes.
#### Estimated changes
Added src/category_theory/abelian/projective.lean
- \+ *abbreviation* category_theory.projective.d
- \+ *lemma* category_theory.projective.exact_d_f
- \+ *lemma* category_theory.projective.iso_iff
- \+ *def* category_theory.projective.left
- \+ *lemma* category_theory.projective.of_iso
- \+ *def* category_theory.projective.over
- \+ *def* category_theory.projective.π
- \+ *structure* category_theory.projective_presentation



## [2021-04-20 03:28:21](https://github.com/leanprover-community/mathlib/commit/013a84e)
chore(scripts): update nolints.txt ([#7272](https://github.com/leanprover-community/mathlib/pull/7272))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-04-20 03:28:20](https://github.com/leanprover-community/mathlib/commit/8bf9fd5)
chore(data/list): drop `list.is_nil` ([#7269](https://github.com/leanprover-community/mathlib/pull/7269))
We have `list.empty` in Lean core.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.empty_iff_eq_nil
- \- *lemma* list.is_nil_iff_eq_nil

Modified src/data/list/defs.lean
- \- *def* list.is_nil



## [2021-04-20 00:10:36](https://github.com/leanprover-community/mathlib/commit/3ad4dab)
chore(algebra/*): add back nat_algebra_subsingleton and add_comm_monoid.nat_semimodule.subsingleton ([#7263](https://github.com/leanprover-community/mathlib/pull/7263))
As suggested in https://github.com/leanprover-community/mathlib/pull/7084#discussion_r613195167.
Even if we now have a design solution that makes this unnecessary, it still feels like a result worth stating.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/module/basic.lean
- \+ *def* add_comm_monoid.nat_semimodule.unique
- \+ *lemma* nat_smul_eq_nsmul



## [2021-04-19 14:03:21](https://github.com/leanprover-community/mathlib/commit/0dfac6e)
chore(*): speed up slow proofs ([#7253](https://github.com/leanprover-community/mathlib/pull/7253))
Proofs that are too slow for the forthcoming `gsmul` refactor. I learnt that `by convert ...` is extremely useful even to close a goal, when elaboration using the expected type is a bad idea.
#### Estimated changes
Modified src/algebra/category/Algebra/limits.lean


Modified src/algebra/category/CommRing/limits.lean
- \- *def* CommRing.is_limit_lifted_cone
- \- *def* CommRing.lifted_cone
- \- *def* CommSemiRing.is_limit_lifted_cone
- \- *def* CommSemiRing.lifted_cone

Modified src/algebra/category/Group/abelian.lean


Modified src/algebra/category/Group/limits.lean


Modified src/linear_algebra/sesquilinear_form.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/ring_theory/jacobson.lean




## [2021-04-19 14:03:20](https://github.com/leanprover-community/mathlib/commit/829d773)
feat(algebra/module/submodule_lattice): add lemmas for nat submodules ([#7221](https://github.com/leanprover-community/mathlib/pull/7221))
This has been suggested by @eric-wieser (who also wrote everything) in [#7200](https://github.com/leanprover-community/mathlib/pull/7200).
This also:
* Merges `span_nat_eq_add_group_closure` and `submodule.span_eq_add_submonoid.closure` which are the same statement into `submodule.span_nat_eq_add_submonoid_closure`, which generalizes the former from `semiring` to `add_comm_monoid`.
* Renames `span_int_eq_add_group_closure` to `submodule.span_nat_eq_add_subgroup_closure`, and generalizes it from `ring` to `add_comm_group`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* span_int_eq
- \- *lemma* span_int_eq_add_group_closure
- \- *lemma* span_nat_eq
- \- *lemma* span_nat_eq_add_group_closure

Modified src/algebra/module/submodule_lattice.lean
- \+ *lemma* add_submonoid.coe_to_nat_submodule
- \+ *def* add_submonoid.to_nat_submodule
- \+ *lemma* add_submonoid.to_nat_submodule_symm
- \+ *lemma* add_submonoid.to_nat_submodule_to_add_submonoid
- \+ *lemma* submodule.to_add_submonoid_to_nat_submodule

Modified src/linear_algebra/basic.lean
- \- *lemma* submodule.span_eq_add_submonoid.closure
- \+ *lemma* submodule.span_int_eq
- \+ *lemma* submodule.span_int_eq_add_subgroup_closure
- \+ *lemma* submodule.span_nat_eq
- \+ *lemma* submodule.span_nat_eq_add_submonoid_closure



## [2021-04-19 09:07:23](https://github.com/leanprover-community/mathlib/commit/6f0c4fb)
feat(data/{int, nat}/parity): rename `ne_of_odd_sum` ([#7261](https://github.com/leanprover-community/mathlib/pull/7261))
`ne_of_odd_sum` becomes `ne_of_odd_add`.
#### Estimated changes
Modified archive/imo/imo1998_q2.lean


Modified src/data/int/parity.lean
- \+ *lemma* int.ne_of_odd_add
- \- *lemma* int.ne_of_odd_sum

Modified src/data/nat/parity.lean
- \+ *lemma* nat.ne_of_odd_add
- \- *lemma* nat.ne_of_odd_sum



## [2021-04-19 09:07:22](https://github.com/leanprover-community/mathlib/commit/fc5e8cb)
chore(algebra/group): missed generalizations to mul_one_class ([#7259](https://github.com/leanprover-community/mathlib/pull/7259))
This adds a missing `ulift` instance, relaxes some lemmas about `semiconj` and `commute` to apply more generally, and broadens the scope of the definitions `monoid_hom.apply` and `ulift.mul_equiv`.
#### Estimated changes
Modified src/algebra/group/commute.lean


Modified src/algebra/group/pi.lean


Modified src/algebra/group/semiconj.lean


Modified src/algebra/group/ulift.lean
- \+/\- *def* ulift.mul_equiv



## [2021-04-19 09:07:20](https://github.com/leanprover-community/mathlib/commit/184e0fe)
fix(equiv/ring): fix bad typeclasses on ring_equiv.trans_apply ([#7258](https://github.com/leanprover-community/mathlib/pull/7258))
`ring_equiv.trans` had weaker typeclasses than the lemma which unfolds it.
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+/\- *lemma* ring_equiv.trans_apply



## [2021-04-19 09:07:19](https://github.com/leanprover-community/mathlib/commit/77f5fb3)
feat(linear_algebra/eigenspace): `mem_maximal_generalized_eigenspace` ([#7162](https://github.com/leanprover-community/mathlib/pull/7162))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.coe_scott_continuous
- \+ *lemma* submodule.coe_supr_of_chain
- \+ *lemma* submodule.mem_supr_of_chain

Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* module.End.generalized_eigenspace_le_maximal
- \+ *lemma* module.End.mem_generalized_eigenspace
- \+ *lemma* module.End.mem_maximal_generalized_eigenspace

Modified src/order/directed.lean
- \+ *lemma* monotone.directed_le



## [2021-04-19 09:07:16](https://github.com/leanprover-community/mathlib/commit/15a64f5)
feat(algebra/module/projective): add projective module ([#6813](https://github.com/leanprover-community/mathlib/pull/6813))
Definition and universal property of projective modules; free modules are projective.
#### Estimated changes
Added src/algebra/module/projective.lean
- \+ *theorem* is_projective.lifting_property
- \+ *theorem* is_projective.of_free
- \+ *theorem* is_projective.of_lifting_property
- \+ *def* is_projective



## [2021-04-19 09:07:14](https://github.com/leanprover-community/mathlib/commit/272e2d2)
feat(data/{int, nat, rat}/cast): extensionality lemmas ([#6788](https://github.com/leanprover-community/mathlib/pull/6788))
Extensionality lemmas
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \- *lemma* monoid_hom.ext_mint

Modified src/data/int/cast.lean
- \+/\- *theorem* monoid_hom.ext_int
- \+ *theorem* monoid_hom.ext_mint
- \+ *theorem* monoid_with_zero_hom.ext_int'
- \+ *theorem* monoid_with_zero_hom.ext_int

Modified src/data/nat/cast.lean
- \+ *theorem* monoid_with_zero_hom.ext_nat

Modified src/data/rat/cast.lean
- \+ *theorem* monoid_with_zero_hom.ext_rat
- \+ *theorem* monoid_with_zero_hom.ext_rat_on_pnat



## [2021-04-19 06:54:49](https://github.com/leanprover-community/mathlib/commit/43f63d9)
feat(topology/algebra/ordered): IVT for the unordered interval ([#7237](https://github.com/leanprover-community/mathlib/pull/7237))
A version of the Intermediate Value Theorem for `interval`.
Co-authored by @ADedecker
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+ *lemma* intermediate_value_interval



## [2021-04-19 02:29:20](https://github.com/leanprover-community/mathlib/commit/5993b90)
feat(tactic/simps): use new options in library ([#7095](https://github.com/leanprover-community/mathlib/pull/7095))
#### Estimated changes
Modified src/data/equiv/local_equiv.lean
- \+/\- *def* equiv.to_local_equiv
- \+ *def* mfld_cfg

Modified src/geometry/manifold/charted_space.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/order/order_iso_nat.lean


Modified src/order/rel_iso.lean
- \- *lemma* order_embedding.coe_subtype
- \+/\- *def* order_embedding.subtype
- \+/\- *theorem* rel_embedding.coe_trans
- \- *theorem* rel_embedding.refl_apply
- \+ *def* rel_embedding.simps.apply
- \- *theorem* rel_hom.comp_apply
- \- *theorem* rel_hom.id_apply
- \- *theorem* rel_iso.of_surjective_coe
- \- *theorem* rel_iso.refl_apply
- \+ *def* rel_iso.simps.apply
- \+ *def* rel_iso.simps.symm_apply
- \- *theorem* rel_iso.trans_apply

Modified src/topology/homeomorph.lean
- \- *lemma* homeomorph.coe_prod_punit
- \- *lemma* homeomorph.coe_refl
- \+ *def* homeomorph.simps.apply
- \+ *def* homeomorph.simps.symm_apply

Modified src/topology/local_homeomorph.lean
- \- *lemma* homeomorph.to_local_homeomorph_coe
- \- *lemma* homeomorph.to_local_homeomorph_source
- \- *lemma* homeomorph.to_local_homeomorph_target
- \- *lemma* local_homeomorph.of_set_coe
- \- *lemma* local_homeomorph.of_set_source
- \- *lemma* local_homeomorph.of_set_target
- \- *lemma* local_homeomorph.piecewise_coe
- \- *lemma* local_homeomorph.piecewise_to_local_equiv
- \- *lemma* local_homeomorph.prod_coe
- \- *lemma* local_homeomorph.prod_coe_symm
- \- *lemma* local_homeomorph.prod_source
- \- *lemma* local_homeomorph.prod_target
- \- *lemma* local_homeomorph.prod_to_local_equiv
- \- *lemma* local_homeomorph.refl_coe
- \- *lemma* local_homeomorph.refl_source
- \- *lemma* local_homeomorph.refl_target
- \- *lemma* local_homeomorph.restr_coe
- \- *lemma* local_homeomorph.restr_coe_symm
- \- *lemma* local_homeomorph.restr_source
- \- *lemma* local_homeomorph.restr_target
- \+ *def* local_homeomorph.simps.apply
- \+ *def* local_homeomorph.simps.symm_apply
- \- *lemma* local_homeomorph.to_homeomorph_coe
- \- *lemma* local_homeomorph.to_homeomorph_symm_coe
- \- *lemma* open_embedding.source
- \- *lemma* open_embedding.target
- \- *lemma* open_embedding.to_local_homeomorph_coe



## [2021-04-18 22:03:44](https://github.com/leanprover-community/mathlib/commit/dbc6574)
chore(data/set/basic): add `set.subsingleton.pairwise_on` ([#7257](https://github.com/leanprover-community/mathlib/pull/7257))
Also add `set.pairwise_on_singleton`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *lemma* set.pairwise_on_empty
- \+ *lemma* set.pairwise_on_singleton



## [2021-04-18 22:03:43](https://github.com/leanprover-community/mathlib/commit/f6132e4)
feat(data/nat/parity): update to match int/parity ([#7156](https://github.com/leanprover-community/mathlib/pull/7156))
A couple of lemmas existed for `int` but not for `nat`, so I add them. I also tidy some lemmas I added in prior PRs and add a file-level docstring.
#### Estimated changes
Modified src/data/nat/parity.lean
- \+/\- *theorem* nat.even_div
- \+ *lemma* nat.ne_of_odd_sum
- \+ *theorem* nat.two_dvd_ne_zero



## [2021-04-18 22:03:41](https://github.com/leanprover-community/mathlib/commit/969c6a3)
feat(data/int/parity): update to match nat/parity (where applicable) ([#7155](https://github.com/leanprover-community/mathlib/pull/7155))
We had a number of lemmas for `nat` but not for `int`, so I add them. I also globalize variables in the file and add a module docstring.
#### Estimated changes
Modified src/data/int/parity.lean
- \+ *theorem* int.even.add_even
- \+ *theorem* int.even.add_odd
- \+ *theorem* int.even.mul_left
- \+ *theorem* int.even.mul_right
- \+ *theorem* int.even.sub_even
- \+ *theorem* int.even.sub_odd
- \+ *theorem* int.even_add'
- \+/\- *theorem* int.even_add
- \+ *theorem* int.even_add_one
- \+/\- *theorem* int.even_coe_nat
- \+/\- *theorem* int.even_iff
- \+/\- *lemma* int.even_iff_not_odd
- \+/\- *theorem* int.even_mul
- \+/\- *theorem* int.even_neg
- \+/\- *theorem* int.even_pow
- \+ *theorem* int.even_sub'
- \+/\- *theorem* int.even_sub
- \+ *lemma* int.is_compl_even_odd
- \+/\- *theorem* int.mod_two_ne_one
- \+/\- *theorem* int.mod_two_ne_zero
- \+/\- *lemma* int.ne_of_odd_sum
- \+/\- *lemma* int.not_even_iff
- \+/\- *lemma* int.not_odd_iff
- \+ *theorem* int.odd.add_even
- \+ *theorem* int.odd.add_odd
- \+ *theorem* int.odd.mul
- \+ *theorem* int.odd.of_mul_left
- \+ *theorem* int.odd.of_mul_right
- \+ *theorem* int.odd.sub_even
- \+ *theorem* int.odd.sub_odd
- \+ *theorem* int.odd_add'
- \+ *theorem* int.odd_add
- \+/\- *theorem* int.odd_iff
- \+/\- *lemma* int.odd_iff_not_even
- \+ *theorem* int.odd_mul
- \+ *theorem* int.odd_sub'
- \+ *theorem* int.odd_sub
- \+/\- *theorem* int.two_dvd_ne_zero
- \+ *lemma* int.two_not_dvd_two_mul_add_one



## [2021-04-18 18:41:38](https://github.com/leanprover-community/mathlib/commit/30ee691)
feat(group_theory/submonoid/operations): add lemmas ([#7219](https://github.com/leanprover-community/mathlib/pull/7219))
Some lemmas about the interaction between additive and multiplicative submonoids.
I provided the two version (from additive to multiplicative and the other way), I am not sure if `@[to_additive]` can automatize this.
#### Estimated changes
Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* add_submonoid.of_submonoid_coe
- \+ *lemma* add_submonoid.of_submonoid_mono
- \+ *def* add_submonoid.submonoid_equiv
- \+ *lemma* add_submonoid.submonoid_equiv_coe
- \+ *lemma* add_submonoid.submonoid_equiv_symm_coe
- \+ *lemma* add_submonoid.to_submonoid_closure
- \+ *lemma* add_submonoid.to_submonoid_coe
- \+ *lemma* add_submonoid.to_submonoid_mono
- \+ *lemma* submonoid.add_submonoid_equiv_coe
- \+ *lemma* submonoid.add_submonoid_equiv_symm_coe
- \+ *lemma* submonoid.of_add_submonoid_coe
- \+ *lemma* submonoid.of_add_submonoid_mono
- \+ *lemma* submonoid.to_add_submonoid_closure
- \+ *lemma* submonoid.to_add_submonoid_coe
- \+ *lemma* submonoid.to_add_submonoid_mono



## [2021-04-18 18:41:37](https://github.com/leanprover-community/mathlib/commit/d107d82)
feat(data/complex): numerical bounds on log 2 ([#7146](https://github.com/leanprover-community/mathlib/pull/7146))
Upper and lower bounds on log 2. Presumably these could be made faster but I don't know the tricks - the proof of `log_two_near_10` (for me) doesn't take longer than `exp_one_near_20` to compile.
I also strengthened the existing bounds slightly.
#### Estimated changes
Modified src/data/complex/exponential_bounds.lean
- \- *lemma* real.exp_neg_one_gt_0367879441
- \+ *lemma* real.exp_neg_one_gt_d9
- \- *lemma* real.exp_neg_one_lt_0367879442
- \+ *lemma* real.exp_neg_one_lt_d9
- \- *lemma* real.exp_one_gt_271828182
- \+ *lemma* real.exp_one_gt_d9
- \- *lemma* real.exp_one_lt_271828183
- \+ *lemma* real.exp_one_lt_d9
- \+ *lemma* real.log_two_gt_d9
- \+ *lemma* real.log_two_lt_d9
- \+ *lemma* real.log_two_near_10



## [2021-04-18 14:42:50](https://github.com/leanprover-community/mathlib/commit/7f541b4)
feat(topology/continuous_function): on a subsingleton X, there is only one subalgebra R C(X,R) ([#7247](https://github.com/leanprover-community/mathlib/pull/7247))
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean
- \+ *lemma* continuous_map.subsingleton_subalgebra



## [2021-04-18 14:42:49](https://github.com/leanprover-community/mathlib/commit/cab0481)
feat(data/finset/lattice): mem_sup, mem_sup' ([#7245](https://github.com/leanprover-community/mathlib/pull/7245))
Sets with `bot` and closed under `sup` are closed under `finset.sup`, and variations for `inf`, `sup'`, and `inf'`.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.inf'_mem
- \+ *lemma* finset.inf_mem
- \+ *lemma* finset.sup'_mem
- \+ *lemma* finset.sup_mem



## [2021-04-18 14:42:48](https://github.com/leanprover-community/mathlib/commit/3953378)
feat(set_theory/surreal): add add_monoid instance ([#7228](https://github.com/leanprover-community/mathlib/pull/7228))
This PR is a part of a project for putting ordered abelian group structure on surreal numbers.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers/near/234694758)
We construct add_monoid instance for surreal numbers.
The "term_type" proofs suggested on the above Zulip thread are not working nicely as Lean is unable to infer the type of the setoid.
#### Estimated changes
Modified src/set_theory/surreal.lean
- \+ *theorem* surreal.add_zero
- \+ *theorem* surreal.zero_add



## [2021-04-18 10:59:52](https://github.com/leanprover-community/mathlib/commit/a6f62a7)
feat(topology/algebra/mul_action.lean): add smul_const ([#7242](https://github.com/leanprover-community/mathlib/pull/7242))
add filter.tendsto.smul_const
#### Estimated changes
Modified src/topology/algebra/mul_action.lean
- \+ *lemma* filter.tendsto.smul_const



## [2021-04-18 10:59:52](https://github.com/leanprover-community/mathlib/commit/4d4b501)
chore(data/set/finite): rename some lemmas ([#7241](https://github.com/leanprover-community/mathlib/pull/7241))
### Revert some name changes from [#5813](https://github.com/leanprover-community/mathlib/pull/5813)
* `set.fintype_set_bUnion` → `set.fintype_bUnion`;
* `set.fintype_set_bUnion'` → `set.fintype_bUnion'`;
* `set.fintype_bUnion` → `set.fintype_bind`;
* `set.fintype_bUnion'` → `set.fintype_bind'`;
* `set.finite_bUnion` → `set.finite.bind`;
### Add a few lemmas
* `set.finite_Union_Prop`;
* add `set.seq` versions of lemmas/defs about `<*>` (they work for `α`, `β` in different universes).
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *theorem* set.finite.bind
- \+ *theorem* set.finite.seq'
- \+/\- *theorem* set.finite.seq
- \+ *theorem* set.finite_Union_Prop
- \- *theorem* set.finite_bUnion
- \+/\- *def* set.fintype_bUnion
- \+ *def* set.fintype_bind
- \- *def* set.fintype_set_bUnion

Modified src/ring_theory/polynomial/dickson.lean




## [2021-04-17 23:26:52](https://github.com/leanprover-community/mathlib/commit/043d046)
feat(algebra/lie/basic): define the `module` and `lie_module` structures on morphisms of Lie modules ([#7225](https://github.com/leanprover-community/mathlib/pull/7225))
Also sundry `simp` lemmas
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* bracket_apply
- \+ *lemma* lie_hom.coe_linear_mk
- \+ *lemma* lie_hom.coe_zero
- \+ *lemma* lie_hom.map_neg
- \+ *lemma* lie_hom.map_sub
- \+ *lemma* lie_hom.mk_coe
- \+ *lemma* lie_hom.zero_apply
- \+ *lemma* lie_module_hom.add_apply
- \+ *lemma* lie_module_hom.coe_add
- \+ *lemma* lie_module_hom.coe_linear_mk
- \+ *lemma* lie_module_hom.coe_neg
- \+ *lemma* lie_module_hom.coe_smul
- \+ *lemma* lie_module_hom.coe_sub
- \+ *lemma* lie_module_hom.coe_zero
- \+ *lemma* lie_module_hom.map_add
- \+ *lemma* lie_module_hom.map_neg
- \+ *lemma* lie_module_hom.map_smul
- \+ *lemma* lie_module_hom.map_sub
- \+ *lemma* lie_module_hom.map_zero
- \+ *lemma* lie_module_hom.mk_coe
- \+ *lemma* lie_module_hom.neg_apply
- \+ *lemma* lie_module_hom.smul_apply
- \+ *lemma* lie_module_hom.sub_apply
- \+ *lemma* lie_module_hom.zero_apply
- \+ *lemma* lie_nsmul
- \+ *lemma* lie_sub
- \+ *lemma* nsmul_lie
- \+ *lemma* sub_lie



## [2021-04-17 23:26:51](https://github.com/leanprover-community/mathlib/commit/aa44de5)
feat(data/real): Inf is nonneg ([#7223](https://github.com/leanprover-community/mathlib/pull/7223))
#### Estimated changes
Modified src/data/real/basic.lean
- \+ *lemma* real.Inf_nonneg
- \+ *lemma* real.Inf_nonpos
- \+ *lemma* real.Sup_nonneg
- \+ *lemma* real.Sup_nonpos



## [2021-04-17 23:26:50](https://github.com/leanprover-community/mathlib/commit/c68e718)
feat(linear_algebra): maximal linear independent ([#7160](https://github.com/leanprover-community/mathlib/pull/7160))
Co-authored by Anne Baanen and Kevin Buzzard
#### Estimated changes
Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* exists_maximal_independent'
- \+ *lemma* exists_maximal_independent
- \+ *lemma* linear_dependent_comp_subtype'
- \+ *lemma* linear_dependent_comp_subtype



## [2021-04-17 20:12:47](https://github.com/leanprover-community/mathlib/commit/ce667c4)
chore(.github/workflows/build.yml): update elan script URL ([#7234](https://github.com/leanprover-community/mathlib/pull/7234))
`elan` moved to the `leanprover` organization: http://github.com/leanprover/elan
#### Estimated changes
Modified .github/workflows/build.yml




## [2021-04-17 20:12:46](https://github.com/leanprover-community/mathlib/commit/20db2fb)
refactor(topology/algebra/module): `map_smul` argument swap ([#7233](https://github.com/leanprover-community/mathlib/pull/7233))
swap the arguments of map_smul to make dot notation work
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean


Modified src/topology/algebra/module.lean




## [2021-04-17 20:12:45](https://github.com/leanprover-community/mathlib/commit/b2e7f40)
feat(analysis/convex/basic): convex hull and empty set ([#7232](https://github.com/leanprover-community/mathlib/pull/7232))
added convex_hull_empty
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex_hull_empty
- \+ *lemma* convex_hull_empty_iff



## [2021-04-17 20:12:44](https://github.com/leanprover-community/mathlib/commit/2292463)
doc(group_theory): fix `normalizer` docstring ([#7231](https://github.com/leanprover-community/mathlib/pull/7231))
The _smallest_ subgroup of `G` inside which `H` is normal is `H` itself.
The _largest_ subgroup of `G` inside which `H` is normal is the normalizer.
Also confirmed by Wikipedia (see the 5th bullet point under "Groups" at [the list of properties of the centralizer and normalizer](https://en.wikipedia.org/wiki/Centralizer_and_normalizer#Properties)), because it's good to have independent confirmation for something so easy to confuse.
#### Estimated changes
Modified src/group_theory/subgroup.lean




## [2021-04-17 14:18:38](https://github.com/leanprover-community/mathlib/commit/21d74c7)
feat(data/equiv/mul_add): use `@[simps]` ([#7213](https://github.com/leanprover-community/mathlib/pull/7213))
Add some `@[simps]` for some algebra maps. This came up in [#6795](https://github.com/leanprover-community/mathlib/pull/6795).
#### Estimated changes
Modified src/algebra/group/hom.lean
- \- *lemma* monoid_hom.coe_mk'
- \- *lemma* monoid_hom.id_apply
- \- *lemma* monoid_with_zero_hom.id_apply
- \- *lemma* mul_hom.id_apply
- \- *lemma* one_hom.id_apply

Modified src/algebra/group/hom_instances.lean
- \- *lemma* monoid_hom.eval_apply

Modified src/analysis/normed_space/normed_group_hom.lean


Modified src/data/equiv/mul_add.lean
- \- *lemma* equiv.coe_inv
- \- *lemma* equiv.coe_mul_left'
- \- *lemma* equiv.coe_mul_right'
- \- *lemma* equiv.mul_left'_symm_apply
- \- *lemma* equiv.mul_right'_symm_apply
- \- *lemma* monoid_hom.coe_to_mul_equiv
- \- *lemma* units.coe_mul_left
- \- *lemma* units.coe_mul_right

Modified src/group_theory/free_abelian_group.lean


Modified src/group_theory/subgroup.lean




## [2021-04-17 09:45:21](https://github.com/leanprover-community/mathlib/commit/9363a64)
feat(data/nat/choose/sum): Add lower bound lemma for central binomial coefficient ([#7214](https://github.com/leanprover-community/mathlib/pull/7214))
This lemma complements the one above it, and will be useful in proving Bertrand's postulate from the 100 theorems list.
#### Estimated changes
Modified src/data/nat/choose/sum.lean
- \+ *lemma* nat.four_pow_le_two_mul_add_one_mul_central_binom



## [2021-04-17 09:45:20](https://github.com/leanprover-community/mathlib/commit/e9a11f6)
feat(analysis/normed_space/operator_norm): generalize to seminormed space ([#7202](https://github.com/leanprover-community/mathlib/pull/7202))
This PR is part of a series of PRs to have seminormed stuff in mathlib.
We generalize here `operator_norm` to `semi_normed_space`. I didn't do anything complicated, essentially I only generalized what works out of the box, without trying to modify the proofs that don't work.
#### Estimated changes
Modified src/analysis/analytic/linear.lean


Modified src/analysis/normed_space/extend.lean
- \+/\- *lemma* continuous_linear_map.extend_to_𝕜'_apply
- \+/\- *lemma* norm_bound

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.norm_id_of_nontrivial_seminorm
- \+/\- *lemma* continuous_linear_map.op_norm_comp_linear_isometry_equiv
- \+/\- *lemma* continuous_linear_map.op_norm_smul_le
- \+ *theorem* continuous_linear_map.op_norm_zero
- \+/\- *lemma* linear_equiv.uniform_embedding
- \+/\- *lemma* linear_map.bound_of_shell
- \+ *lemma* linear_map.bound_of_shell_semi_normed
- \+ *lemma* norm_image_of_norm_zero

Modified src/data/complex/is_R_or_C.lean




## [2021-04-17 05:06:55](https://github.com/leanprover-community/mathlib/commit/206ecce)
chore(category_theory/subobject): different proof of le_of_comm ([#7229](https://github.com/leanprover-community/mathlib/pull/7229))
This is certainly a shorter proof of `le_of_comm`; whether it is "cleaner" like the comment asked for is perhaps a matter of taste.
#### Estimated changes
Modified src/category_theory/subobject/basic.lean




## [2021-04-17 05:06:54](https://github.com/leanprover-community/mathlib/commit/0f6c1f1)
feat(order/conditionally_complete_lattice): conditional Inf of intervals ([#7226](https://github.com/leanprover-community/mathlib/pull/7226))
Some new simp lemmas for cInf/cSup of intervals. I tried to use the minimal possible assumptions that I could - some lemmas are therefore in the linear order section and others are just for lattices.
#### Estimated changes
Modified src/order/bounds.lean
- \+/\- *lemma* is_glb_Ioo

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* cInf_Icc
- \+ *lemma* cInf_Ico
- \+ *lemma* cInf_Ioc
- \+ *lemma* cInf_Ioi
- \+ *lemma* cInf_Ioo
- \+ *lemma* cSup_Icc
- \+ *lemma* cSup_Ico
- \+ *lemma* cSup_Iio
- \+ *lemma* cSup_Ioc
- \+ *lemma* cSup_Ioo



## [2021-04-17 05:06:53](https://github.com/leanprover-community/mathlib/commit/560a009)
feat(category_theory): formally adjoined initial objects are strict ([#7222](https://github.com/leanprover-community/mathlib/pull/7222))
#### Estimated changes
Modified src/category_theory/with_terminal.lean




## [2021-04-17 02:40:11](https://github.com/leanprover-community/mathlib/commit/89c16a7)
chore(ring_theory/adjoin.basic): use submodule.closure in algebra.adjoin_eq_span ([#7194](https://github.com/leanprover-community/mathlib/pull/7194))
`algebra.adjoin_eq_span` uses `monoid.closure` that is deprecated. We modify it to use `submonoid.closure`.
#### Estimated changes
Modified src/ring_theory/adjoin/basic.lean
- \+/\- *theorem* algebra.adjoin_eq_span

Modified src/ring_theory/algebra_tower.lean




## [2021-04-17 02:40:10](https://github.com/leanprover-community/mathlib/commit/b7a3d4e)
feat(test/integration): improve an example ([#7169](https://github.com/leanprover-community/mathlib/pull/7169))
With [#7103](https://github.com/leanprover-community/mathlib/pull/7103), I am able to improve one of my examples.
#### Estimated changes
Modified test/integration.lean




## [2021-04-16 22:20:07](https://github.com/leanprover-community/mathlib/commit/6b182fc)
feat(category_theory/triangulated/pretriangulated): add definition of pretriangulated categories and triangulated functors between them  ([#7153](https://github.com/leanprover-community/mathlib/pull/7153))
Adds a definition of pretriangulated categories and triangulated functors between them.
#### Estimated changes
Modified src/category_theory/preadditive/additive_functor.lean


Modified src/category_theory/triangulated/basic.lean
- \+/\- *def* category_theory.triangulated.contractible_triangle
- \+ *def* category_theory.triangulated.triangle.mk
- \+/\- *structure* category_theory.triangulated.triangle

Added src/category_theory/triangulated/pretriangulated.lean
- \+ *lemma* category_theory.triangulated.pretriangulated.comp_dist_triangle_mor_zero₁₂
- \+ *lemma* category_theory.triangulated.pretriangulated.comp_dist_triangle_mor_zero₂₃
- \+ *lemma* category_theory.triangulated.pretriangulated.comp_dist_triangle_mor_zero₃₁
- \+ *lemma* category_theory.triangulated.pretriangulated.inv_rot_of_dist_triangle
- \+ *lemma* category_theory.triangulated.pretriangulated.rot_of_dist_triangle
- \+ *lemma* category_theory.triangulated.pretriangulated.triangulated_functor.map_distinguished
- \+ *def* category_theory.triangulated.pretriangulated.triangulated_functor.map_triangle
- \+ *structure* category_theory.triangulated.pretriangulated.triangulated_functor
- \+ *def* category_theory.triangulated.pretriangulated.triangulated_functor_struct.map_triangle
- \+ *structure* category_theory.triangulated.pretriangulated.triangulated_functor_struct

Modified src/category_theory/triangulated/rotate.lean
- \+/\- *def* category_theory.triangulated.inv_rot_comp_rot
- \+/\- *def* category_theory.triangulated.inv_rot_comp_rot_hom
- \+/\- *def* category_theory.triangulated.inv_rot_comp_rot_inv
- \+/\- *def* category_theory.triangulated.rot_comp_inv_rot
- \+/\- *def* category_theory.triangulated.rot_comp_inv_rot_hom
- \+/\- *def* category_theory.triangulated.rot_comp_inv_rot_inv
- \+/\- *def* category_theory.triangulated.triangle.rotate



## [2021-04-16 22:20:06](https://github.com/leanprover-community/mathlib/commit/110541d)
feat(data/list/basic): fold[rl] recursion principles ([#7079](https://github.com/leanprover-community/mathlib/pull/7079))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *def* list.foldl_rec_on
- \+ *lemma* list.foldl_rec_on_nil
- \+ *def* list.foldr_rec_on
- \+ *lemma* list.foldr_rec_on_cons
- \+ *lemma* list.foldr_rec_on_nil



## [2021-04-16 17:35:16](https://github.com/leanprover-community/mathlib/commit/49040e5)
feat(data/set): sep true/false simp lemmas ([#7215](https://github.com/leanprover-community/mathlib/pull/7215))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.sep_false
- \+ *lemma* set.sep_true



## [2021-04-16 17:35:15](https://github.com/leanprover-community/mathlib/commit/24013e2)
feat(data/finsupp/basic): add finsupp.single_left_injective and docstrings ([#7207](https://github.com/leanprover-community/mathlib/pull/7207))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.single_left_inj
- \+ *lemma* finsupp.single_left_injective



## [2021-04-16 17:35:14](https://github.com/leanprover-community/mathlib/commit/0688612)
feat(order/rel_iso): constructors for rel embeddings ([#7046](https://github.com/leanprover-community/mathlib/pull/7046))
Alternate constructors for relation and order embeddings which require slightly less to prove.
#### Estimated changes
Modified src/order/rel_iso.lean
- \+ *lemma* order_embedding.coe_of_map_rel_iff
- \+ *def* order_embedding.of_map_rel_iff
- \+ *def* rel_embedding.of_map_rel_iff
- \+ *lemma* rel_embedding.of_map_rel_iff_coe



## [2021-04-16 17:35:13](https://github.com/leanprover-community/mathlib/commit/ea4dce0)
feat(category_theory): the additive envelope, Mat_ C ([#6845](https://github.com/leanprover-community/mathlib/pull/6845))
# Matrices over a category.
When `C` is a preadditive category, `Mat_ C` is the preadditive categoriy
whose objects are finite tuples of objects in `C`, and
whose morphisms are matrices of morphisms from `C`.
There is a functor `Mat_.embedding : C ⥤ Mat_ C` sending morphisms to one-by-one matrices.
`Mat_ C` has finite biproducts.
## The additive envelope
We show that this construction is the "additive envelope" of `C`,
in the sense that any additive functor `F : C ⥤ D` to a category `D` with biproducts
lifts to a functor `Mat_.lift F : Mat_ C ⥤ D`,
Moreover, this functor is unique (up to natural isomorphisms) amongst functors `L : Mat_ C ⥤ D`
such that `embedding C ⋙ L ≅ F`.
(As we don't have 2-category theory, we can't explicitly state that `Mat_ C` is
the initial object in the 2-category of categories under `C` which have biproducts.)
As a consequence, when `C` already has finite biproducts we have `Mat_ C ≌ C`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_dite_irrel

Modified src/algebra/big_operators/pi.lean
- \+ *lemma* finset.prod_fn

Added src/category_theory/preadditive/Mat.lean
- \+ *lemma* category_theory.Mat_.add_apply
- \+ *def* category_theory.Mat_.additive_obj_iso_biproduct
- \+ *lemma* category_theory.Mat_.additive_obj_iso_biproduct_naturality'
- \+ *lemma* category_theory.Mat_.additive_obj_iso_biproduct_naturality
- \+ *lemma* category_theory.Mat_.comp_apply
- \+ *lemma* category_theory.Mat_.comp_def
- \+ *def* category_theory.Mat_.embedding
- \+ *def* category_theory.Mat_.embedding_lift_iso
- \+ *def* category_theory.Mat_.equivalence_self_of_has_finite_biproducts
- \+ *def* category_theory.Mat_.equivalence_self_of_has_finite_biproducts_aux
- \+ *lemma* category_theory.Mat_.equivalence_self_of_has_finite_biproducts_functor
- \+ *lemma* category_theory.Mat_.equivalence_self_of_has_finite_biproducts_inverse
- \+ *def* category_theory.Mat_.ext
- \+ *def* category_theory.Mat_.hom.comp
- \+ *def* category_theory.Mat_.hom.id
- \+ *def* category_theory.Mat_.hom
- \+ *lemma* category_theory.Mat_.id_apply
- \+ *lemma* category_theory.Mat_.id_apply_of_ne
- \+ *lemma* category_theory.Mat_.id_apply_self
- \+ *lemma* category_theory.Mat_.id_def
- \+ *def* category_theory.Mat_.iso_biproduct_embedding
- \+ *def* category_theory.Mat_.lift
- \+ *def* category_theory.Mat_.lift_unique
- \+ *structure* category_theory.Mat_
- \+ *def* category_theory.functor.map_Mat_
- \+ *def* category_theory.functor.map_Mat_comp
- \+ *def* category_theory.functor.map_Mat_id

Modified src/data/matrix/basic.lean
- \- *theorem* matrix.add_apply
- \- *theorem* matrix.neg_apply
- \- *theorem* matrix.sub_apply
- \- *theorem* matrix.zero_apply

Added src/data/matrix/dmatrix.lean
- \+ *def* add_monoid_hom.map_dmatrix
- \+ *lemma* add_monoid_hom.map_dmatrix_apply
- \+ *theorem* dmatrix.add_apply
- \+ *def* dmatrix.col
- \+ *theorem* dmatrix.ext
- \+ *theorem* dmatrix.ext_iff
- \+ *def* dmatrix.map
- \+ *lemma* dmatrix.map_add
- \+ *lemma* dmatrix.map_apply
- \+ *lemma* dmatrix.map_map
- \+ *lemma* dmatrix.map_sub
- \+ *lemma* dmatrix.map_zero
- \+ *theorem* dmatrix.neg_apply
- \+ *def* dmatrix.row
- \+ *theorem* dmatrix.sub_apply
- \+ *lemma* dmatrix.subsingleton_of_empty_left
- \+ *lemma* dmatrix.subsingleton_of_empty_right
- \+ *def* dmatrix.transpose
- \+ *theorem* dmatrix.zero_apply
- \+ *def* dmatrix

Modified src/linear_algebra/char_poly/basic.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/ring_theory/polynomial_algebra.lean




## [2021-04-16 14:09:23](https://github.com/leanprover-community/mathlib/commit/108b923)
chore(algebra): add `sub{_mul_action,module,semiring,ring,field,algebra}.copy` ([#7220](https://github.com/leanprover-community/mathlib/pull/7220))
We already have this for sub{monoid,group}. With this in place, we can make `coe subalgebra.range` defeq to `set.range` and similar (left for a follow-up).
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/module/submodule.lean


Modified src/data/set_like.lean


Modified src/field_theory/subfield.lean


Modified src/group_theory/group_action/sub_mul_action.lean


Modified src/group_theory/submonoid/basic.lean
- \- *def* submonoid.copy

Modified src/ring_theory/subring.lean


Modified src/ring_theory/subsemiring.lean




## [2021-04-16 14:09:22](https://github.com/leanprover-community/mathlib/commit/e00d688)
chore(group_theory/subgroup): rename `monoid_hom.to_range` to `monoid_hom.range_restrict` ([#7218](https://github.com/leanprover-community/mathlib/pull/7218))
This makes it match:
* `monoid_hom.mrange_restrict`
* `linear_map.range_restrict`
* `ring_hom.range_restrict`
* `ring_hom.srange_restrict`
* `alg_hom.range_restrict`
This also adds a missing simp lemma.
#### Estimated changes
Modified src/algebra/category/Group/images.lean
- \+/\- *def* AddCommGroup.factor_thru_image

Modified src/group_theory/quotient_group.lean


Modified src/group_theory/subgroup.lean
- \+ *lemma* monoid_hom.coe_range_restrict
- \+ *def* monoid_hom.range_restrict
- \+ *lemma* monoid_hom.range_restrict_ker
- \- *def* monoid_hom.to_range
- \- *lemma* monoid_hom.to_range_ker



## [2021-04-16 11:48:29](https://github.com/leanprover-community/mathlib/commit/b1acb58)
chore(data/mv_polynomial/basic): golf some proofs ([#7209](https://github.com/leanprover-community/mathlib/pull/7209))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean




## [2021-04-16 05:10:03](https://github.com/leanprover-community/mathlib/commit/bb9b850)
feat(data/multiset/basic): some multiset lemmas, featuring sum inequalities ([#7090](https://github.com/leanprover-community/mathlib/pull/7090))
Proves some lemmas about `rel` and about inequalities between sums of multisets.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.card_nsmul_le_sum
- \+/\- *theorem* multiset.map_nsmul
- \+ *lemma* multiset.rel_of_forall
- \+ *lemma* multiset.rel_refl_of_refl_on
- \+ *lemma* multiset.rel_repeat_left
- \+ *lemma* multiset.rel_repeat_right
- \+ *lemma* multiset.sum_le_card_nsmul
- \+ *lemma* multiset.sum_le_sum_map
- \+ *lemma* multiset.sum_le_sum_of_rel_le
- \+ *lemma* multiset.sum_map_le_sum



## [2021-04-16 03:40:55](https://github.com/leanprover-community/mathlib/commit/148760e)
feat(category_theory/kernels): missing instances ([#7204](https://github.com/leanprover-community/mathlib/pull/7204))
#### Estimated changes
Modified src/category_theory/limits/shapes/kernels.lean
- \+/\- *def* category_theory.limits.cokernel_comp_is_iso
- \+/\- *def* category_theory.limits.kernel_is_iso_comp



## [2021-04-16 03:40:54](https://github.com/leanprover-community/mathlib/commit/9d1ab69)
refactor(category_theory/images): improvements ([#7198](https://github.com/leanprover-community/mathlib/pull/7198))
Some improvements to the images API, from `homology2`.
#### Estimated changes
Modified src/algebra/homology/image_to_kernel_map.lean


Modified src/category_theory/limits/shapes/images.lean
- \+ *def* category_theory.limits.image.comp_iso
- \+ *lemma* category_theory.limits.image.comp_iso_hom_comp_image_ι
- \+ *lemma* category_theory.limits.image.comp_iso_inv_comp_image_ι
- \- *def* category_theory.limits.image.post_comp_is_iso
- \- *lemma* category_theory.limits.image.post_comp_is_iso_hom_comp_image_ι
- \- *lemma* category_theory.limits.image.post_comp_is_iso_inv_comp_image_ι
- \+ *def* category_theory.limits.mono_factorisation.comp_mono
- \+ *def* category_theory.limits.mono_factorisation.iso_comp
- \+ *def* category_theory.limits.mono_factorisation.of_comp_iso
- \+ *def* category_theory.limits.mono_factorisation.of_iso_comp



## [2021-04-16 01:12:09](https://github.com/leanprover-community/mathlib/commit/81b8873)
doc(topology/bases): add module + theorem docstrings ([#7193](https://github.com/leanprover-community/mathlib/pull/7193))
#### Estimated changes
Modified src/topology/bases.lean




## [2021-04-15 20:50:28](https://github.com/leanprover-community/mathlib/commit/8742be7)
fix(.github/PULL_REQUEST_TEMPLATE.md): revert gitpod button URL ([#7210](https://github.com/leanprover-community/mathlib/pull/7210))
Reverts [#7096](https://github.com/leanprover-community/mathlib/pull/7096) since the URL was changed back.
#### Estimated changes
Modified .github/PULL_REQUEST_TEMPLATE.md




## [2021-04-15 20:50:27](https://github.com/leanprover-community/mathlib/commit/37ab34e)
doc(tactic/congr): example where congr fails, but exact works ([#7208](https://github.com/leanprover-community/mathlib/pull/7208))
As requested on zulip:
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.237084/near/234652967
#### Estimated changes
Modified src/tactic/congr.lean




## [2021-04-15 20:50:26](https://github.com/leanprover-community/mathlib/commit/b4201e7)
chore(group/ring_hom): fix a nat nsmul diamond ([#7201](https://github.com/leanprover-community/mathlib/pull/7201))
The space of additive monoid should be given a proper `nat`-action, by the pointwise action, to avoid diamonds.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \- *def* monoid_hom.comp_hom
- \- *def* monoid_hom.eval
- \- *lemma* monoid_hom.eval_apply
- \- *def* monoid_hom.flip
- \- *lemma* monoid_hom.flip_apply
- \- *def* monoid_hom.flip_hom

Added src/algebra/group/hom_instances.lean
- \+ *def* monoid_hom.comp_hom
- \+ *def* monoid_hom.eval
- \+ *lemma* monoid_hom.eval_apply
- \+ *def* monoid_hom.flip
- \+ *lemma* monoid_hom.flip_apply
- \+ *def* monoid_hom.flip_hom
- \+ *lemma* nat.succ_eq_one_add

Modified src/algebra/group/pi.lean


Modified src/algebra/group_power/basic.lean


Modified src/algebra/module/basic.lean
- \- *lemma* add_monoid_hom.nat_smul_apply

Modified src/data/nat/basic.lean
- \- *lemma* nat.succ_eq_one_add



## [2021-04-15 15:46:19](https://github.com/leanprover-community/mathlib/commit/50a843e)
chore(algebra/module/submodule): add missing coe lemmas ([#7205](https://github.com/leanprover-community/mathlib/pull/7205))
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *theorem* submodule.coe_to_add_submonoid
- \+ *theorem* submodule.coe_to_sub_mul_action



## [2021-04-15 15:46:18](https://github.com/leanprover-community/mathlib/commit/14c625e)
feat(linear_algebra/basic): add span_eq_add_submonoid.closure ([#7200](https://github.com/leanprover-community/mathlib/pull/7200))
The `ℕ` span equals `add_submonoid.closure`.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.span_eq_add_submonoid.closure



## [2021-04-15 15:46:16](https://github.com/leanprover-community/mathlib/commit/0f3ca67)
feat(number_theory/bernoulli): golf ([#7197](https://github.com/leanprover-community/mathlib/pull/7197))
I golf the file to improve scannability and stylistic uniformity.
#### Estimated changes
Modified src/number_theory/bernoulli.lean
- \+/\- *def* bernoulli'_power_series
- \+/\- *def* bernoulli
- \+/\- *def* bernoulli_power_series
- \+/\- *lemma* bernoulli_spec'



## [2021-04-15 15:46:15](https://github.com/leanprover-community/mathlib/commit/6a4d298)
chore(topology/vector_bundle): generalize to topological semimodules ([#7183](https://github.com/leanprover-community/mathlib/pull/7183))
#### Estimated changes
Modified src/topology/vector_bundle.lean
- \+/\- *def* topological_vector_bundle.trivial_bundle_trivialization
- \+/\- *def* topological_vector_bundle.trivialization.continuous_linear_equiv_at
- \+/\- *lemma* topological_vector_bundle.trivialization.continuous_linear_equiv_at_apply'
- \+/\- *lemma* topological_vector_bundle.trivialization.continuous_linear_equiv_at_apply
- \+/\- *lemma* topological_vector_bundle.trivialization.mem_source
- \+/\- *def* topological_vector_bundle.trivialization_at



## [2021-04-15 15:46:13](https://github.com/leanprover-community/mathlib/commit/f92dc6c)
feat(algebra/group_with_zero): non-associative monoid_with_zero ([#7176](https://github.com/leanprover-community/mathlib/pull/7176))
This introduces a new `mul_zero_one_class` which is `monoid_with_zero` without associativity, just as `mul_one_class` is `monoid` without associativity.
This would help expand the scope of [#6786](https://github.com/leanprover-community/mathlib/pull/6786) to include ring_homs, something that was previously blocked by `monoid_with_zero` and the `non_assoc_semiring` having no common ancestor with `0`, `1`, and `*`.
Using [#6865](https://github.com/leanprover-community/mathlib/pull/6865) as a template for what to cover, this PR includes;
* Generalizing `monoid_with_zero_hom` to require the weaker `mul_zero_one_class`. This has a slight downside, in that `some_mwzh.to_monoid_hom` now holds as its typeclass argument `mul_zero_one_class.to_mul_one_class` instead of `monoid_with_zero.to_monoid`. This means that lemmas about `monoid_hom`s with associate multiplication no longer always elaborate correctly without type annotations, as the `monoid` instance has to be found by typeclass search instead of unification.
* `function.(in|sur)jective.mul_zero_one_class`
* `equiv.mul_zero_one_class`
* Adding instances for:
  * `prod`
  * `pi`
  * `set_semiring`
  * `with_zero`
  * `locally_constant`
  * `monoid_algebra`
  * `add_monoid_algebra`
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+/\- *lemma* monoid_with_zero_hom.coe_comp
- \+/\- *lemma* monoid_with_zero_hom.coe_eq_to_monoid_hom
- \+/\- *lemma* monoid_with_zero_hom.coe_eq_to_zero_hom
- \+/\- *lemma* monoid_with_zero_hom.coe_inj
- \+/\- *lemma* monoid_with_zero_hom.coe_mk
- \+/\- *def* monoid_with_zero_hom.comp
- \+/\- *lemma* monoid_with_zero_hom.comp_apply
- \+/\- *lemma* monoid_with_zero_hom.comp_id
- \+/\- *theorem* monoid_with_zero_hom.congr_arg
- \+/\- *theorem* monoid_with_zero_hom.congr_fun
- \+/\- *lemma* monoid_with_zero_hom.ext
- \+/\- *lemma* monoid_with_zero_hom.ext_iff
- \+/\- *def* monoid_with_zero_hom.id
- \+/\- *lemma* monoid_with_zero_hom.id_apply
- \+/\- *lemma* monoid_with_zero_hom.id_comp
- \+/\- *lemma* monoid_with_zero_hom.map_mul
- \+/\- *lemma* monoid_with_zero_hom.map_one
- \+/\- *lemma* monoid_with_zero_hom.map_zero
- \+/\- *lemma* monoid_with_zero_hom.mk_coe
- \+/\- *lemma* monoid_with_zero_hom.to_fun_eq_coe
- \+/\- *lemma* monoid_with_zero_hom.to_monoid_hom_coe
- \+/\- *lemma* monoid_with_zero_hom.to_zero_hom_coe
- \+/\- *structure* monoid_with_zero_hom

Modified src/algebra/group/pi.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/group_power/basic.lean


Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/group_with_zero/basic.lean


Modified src/algebra/group_with_zero/defs.lean


Modified src/algebra/monoid_algebra.lean


Modified src/algebra/pointwise.lean


Modified src/analysis/normed_space/basic.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/mv_polynomial/invertible.lean


Modified src/data/polynomial/degree/definitions.lean


Modified src/ring_theory/perfection.lean


Modified src/topology/locally_constant/algebra.lean




## [2021-04-15 15:46:12](https://github.com/leanprover-community/mathlib/commit/adfeb24)
refactor(algebra/big_operators/order): use `to_additive` ([#7173](https://github.com/leanprover-community/mathlib/pull/7173))
* Replace many lemmas about `finset.sum` with lemmas about `finset.prod` + `@[to_additive]`;
* Avoid `s \ t` in `finset.sum_lt_sum_of_subset`.
* Use `M`, `N` instead of `α`, `β` for types with algebraic structures.
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+/\- *lemma* finset.abs_prod
- \+/\- *lemma* finset.abs_sum_le_sum_abs
- \+/\- *theorem* finset.card_le_mul_card_image
- \+/\- *theorem* finset.card_le_mul_card_image_of_maps_to
- \+ *theorem* finset.exists_le_of_prod_le'
- \- *theorem* finset.exists_le_of_sum_le
- \+ *theorem* finset.exists_lt_of_prod_lt'
- \- *theorem* finset.exists_lt_of_sum_lt
- \+ *lemma* finset.exists_one_lt_of_prod_one_of_exists_ne_one'
- \- *lemma* finset.exists_pos_of_sum_zero_of_exists_nonzero
- \+/\- *lemma* finset.le_prod_nonempty_of_submultiplicative
- \+/\- *lemma* finset.le_prod_nonempty_of_submultiplicative_on_pred
- \+/\- *lemma* finset.le_prod_of_submultiplicative
- \+/\- *lemma* finset.le_prod_of_submultiplicative_on_pred
- \+/\- *theorem* finset.mul_card_image_le_card
- \+/\- *theorem* finset.mul_card_image_le_card_of_maps_to
- \+/\- *lemma* finset.prod_add_prod_le'
- \+/\- *lemma* finset.prod_add_prod_le
- \+ *lemma* finset.prod_eq_one_iff'
- \+ *lemma* finset.prod_eq_one_iff_of_le_one'
- \+ *lemma* finset.prod_eq_one_iff_of_one_le'
- \+ *lemma* finset.prod_fiberwise_le_prod_of_one_le_prod_fiber'
- \+ *lemma* finset.prod_le_one'
- \+/\- *lemma* finset.prod_le_one
- \+ *lemma* finset.prod_le_prod''
- \+/\- *lemma* finset.prod_le_prod'
- \+/\- *lemma* finset.prod_le_prod
- \+ *lemma* finset.prod_le_prod_fiberwise_of_prod_fiber_le_one'
- \+ *lemma* finset.prod_le_prod_of_ne_one'
- \+ *lemma* finset.prod_le_prod_of_subset'
- \+ *lemma* finset.prod_le_prod_of_subset_of_one_le'
- \+ *theorem* finset.prod_lt_prod'
- \+ *lemma* finset.prod_lt_prod_of_nonempty'
- \+ *lemma* finset.prod_lt_prod_of_subset'
- \+ *lemma* finset.prod_mono_set'
- \+ *lemma* finset.prod_mono_set_of_one_le'
- \+/\- *lemma* finset.prod_nonneg
- \+/\- *lemma* finset.prod_pos
- \+ *lemma* finset.single_le_prod'
- \- *lemma* finset.single_le_sum
- \+ *lemma* finset.single_lt_prod'
- \- *lemma* finset.sum_eq_zero_iff
- \- *lemma* finset.sum_eq_zero_iff_of_nonneg
- \- *lemma* finset.sum_eq_zero_iff_of_nonpos
- \- *lemma* finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg
- \- *lemma* finset.sum_le_sum
- \- *lemma* finset.sum_le_sum_fiberwise_of_sum_fiber_nonpos
- \- *lemma* finset.sum_le_sum_of_ne_zero
- \- *lemma* finset.sum_le_sum_of_subset
- \- *lemma* finset.sum_le_sum_of_subset_of_nonneg
- \- *theorem* finset.sum_lt_sum
- \- *lemma* finset.sum_lt_sum_of_nonempty
- \- *lemma* finset.sum_lt_sum_of_subset
- \- *lemma* finset.sum_mono_set
- \- *lemma* finset.sum_mono_set_of_nonneg
- \- *lemma* finset.sum_nonneg
- \- *lemma* finset.sum_nonpos
- \+ *lemma* fintype.prod_mono'
- \+ *lemma* fintype.prod_strict_mono'
- \- *lemma* fintype.sum_mono
- \- *lemma* fintype.sum_strict_mono
- \+/\- *lemma* with_top.prod_lt_top
- \+/\- *lemma* with_top.sum_eq_top_iff
- \+/\- *lemma* with_top.sum_lt_top
- \+/\- *lemma* with_top.sum_lt_top_iff

Modified src/combinatorics/composition.lean




## [2021-04-15 15:46:11](https://github.com/leanprover-community/mathlib/commit/5806a94)
feat(data/nat/basic, data/nat/prime): add various lemmas ([#7171](https://github.com/leanprover-community/mathlib/pull/7171))
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* lt_mul_of_one_lt_left
- \+/\- *lemma* lt_mul_of_one_lt_right

Modified src/data/nat/basic.lean
- \+ *lemma* nat.dvd_sub'
- \+ *theorem* nat.pow_two_sub_pow_two

Modified src/data/nat/prime.lean
- \+/\- *lemma* nat.mem_factors
- \+ *lemma* nat.prime_of_mem_factors

Modified src/data/padics/padic_norm.lean


Modified src/data/pnat/factors.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/ring_theory/int/basic.lean




## [2021-04-15 08:26:50](https://github.com/leanprover-community/mathlib/commit/4b835cc)
feat(category_theory/subobject): proof golf and some API ([#7170](https://github.com/leanprover-community/mathlib/pull/7170))
#### Estimated changes
Modified src/category_theory/subobject/basic.lean
- \+ *lemma* category_theory.subobject.mk_arrow

Modified src/category_theory/subobject/factor_thru.lean
- \+ *lemma* category_theory.mono_over.factors_congr
- \+ *lemma* category_theory.subobject.mk_factors_iff

Modified src/category_theory/subobject/mono_over.lean
- \+ *def* category_theory.mono_over.mk'_arrow_iso



## [2021-04-15 08:26:48](https://github.com/leanprover-community/mathlib/commit/dbd468d)
feat(analysis/special_functions/trigonometric): periodicity of sine, cosine ([#7107](https://github.com/leanprover-community/mathlib/pull/7107))
Previously we only had `sin (x + 2 * π) = sin x` and `cos (x + 2 * π) = cos x`. I extend those results to cover shifts by any integer multiple of `2 * π`, not just `2 * π`. I also provide corresponding `sub` lemmas.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* real.cos_add_int_mul_two_pi
- \+ *lemma* real.cos_add_nat_mul_two_pi
- \+ *lemma* real.cos_int_mul_two_pi_sub_pi
- \+ *lemma* real.cos_nat_mul_two_pi_add_pi
- \+ *lemma* real.cos_nat_mul_two_pi_sub_pi
- \+ *lemma* real.cos_sub_int_mul_two_pi
- \+ *lemma* real.cos_sub_nat_mul_two_pi
- \+ *lemma* real.cos_sub_two_pi
- \+ *lemma* real.sin_add_int_mul_two_pi
- \+ *lemma* real.sin_add_nat_mul_two_pi
- \+ *lemma* real.sin_sub_int_mul_two_pi
- \+ *lemma* real.sin_sub_nat_mul_two_pi
- \+ *lemma* real.sin_sub_two_pi



## [2021-04-15 04:42:22](https://github.com/leanprover-community/mathlib/commit/3a64d11)
chore(scripts): update nolints.txt ([#7195](https://github.com/leanprover-community/mathlib/pull/7195))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-04-15 04:42:20](https://github.com/leanprover-community/mathlib/commit/c73b165)
chore(data/fin,data/finset): a few lemmas ([#7168](https://github.com/leanprover-community/mathlib/pull/7168))
* `fin.heq_fun_iff`: use `Sort*` instead of `Type*`;
* `fin.cast_refl`: take `h : n = n := rfl` as an argument;
* `fin.cast_to_equiv`, `fin.cast_eq_cast`: relate `fin.cast` to `_root_.cast`;
* `finset.map_cast_heq`: new lemma;
* `finset.subset_univ`: add `@[simp]`;
* `card_finset_fin_le`, `fintype.card_finset_len`, `fin.prod_const` : new lemmas;
* `order_iso.refl`: new definition.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.cast_eq_cast
- \+/\- *lemma* fin.cast_refl
- \+ *lemma* fin.cast_to_equiv

Modified src/data/finset/basic.lean
- \+/\- *theorem* finset.coe_map
- \+/\- *theorem* finset.coe_map_subset_range
- \+ *theorem* finset.map_cast_heq

Modified src/data/fintype/basic.lean
- \+ *lemma* card_finset_fin_le
- \+/\- *theorem* finset.subset_univ
- \+ *lemma* finset.univ_filter_card_eq
- \+ *lemma* fintype.card_finset_len

Modified src/data/fintype/card.lean
- \+ *lemma* fin.prod_const
- \+ *lemma* fin.sum_const

Modified src/linear_algebra/multilinear.lean


Modified src/order/rel_iso.lean
- \+ *lemma* order_iso.coe_refl
- \+ *def* order_iso.refl
- \+ *lemma* order_iso.refl_apply
- \+ *lemma* order_iso.refl_to_equiv
- \+ *lemma* order_iso.refl_trans
- \+ *lemma* order_iso.symm_refl
- \+ *lemma* order_iso.trans_refl



## [2021-04-14 23:14:49](https://github.com/leanprover-community/mathlib/commit/f74213b)
feat(algebra/ordered_group): proof of le without density ([#7191](https://github.com/leanprover-community/mathlib/pull/7191))
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* le_of_forall_pos_lt_add



## [2021-04-14 23:14:48](https://github.com/leanprover-community/mathlib/commit/60060c3)
feat(field_theory/algebraic_closure): define `is_alg_closed.splits_codomain` ([#7187](https://github.com/leanprover-community/mathlib/pull/7187))
Let `p : polynomial K` and `k` be an algebraically closed extension of `K`. Showing that `p` splits in `k` used to be a bit awkward because `is_alg_closed.splits` only gives `splits (p.map (f : k →+* K)) id`, which you still have to `simp` to `splits p f`.
This PR defines `is_alg_closed.splits_codomain`, showing `splits p f` directly by doing the `simp`ing for you. It also renames `polynomial.splits'` to `is_alg_closed.splits_domain`, for symmetry.
Zulip discussion starts [here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Complex.20numbers.20sums/near/234481576)
#### Estimated changes
Modified src/field_theory/algebraic_closure.lean
- \+ *theorem* is_alg_closed.splits_codomain
- \+ *theorem* is_alg_closed.splits_domain
- \- *theorem* polynomial.splits'



## [2021-04-14 23:14:47](https://github.com/leanprover-community/mathlib/commit/3d67b69)
chore(algebra/group_power/basic): `pow_abs` does not need commutativity ([#7178](https://github.com/leanprover-community/mathlib/pull/7178))
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* abs_neg_one_pow
- \+/\- *lemma* pow_abs



## [2021-04-14 23:14:46](https://github.com/leanprover-community/mathlib/commit/e4843ea)
chore(category_theory/subobject): split off specific subobjects ([#7167](https://github.com/leanprover-community/mathlib/pull/7167))
#### Estimated changes
Modified src/category_theory/subobject/factor_thru.lean
- \- *def* category_theory.limits.equalizer_subobject
- \- *lemma* category_theory.limits.equalizer_subobject_arrow'
- \- *lemma* category_theory.limits.equalizer_subobject_arrow
- \- *lemma* category_theory.limits.equalizer_subobject_arrow_comp
- \- *lemma* category_theory.limits.equalizer_subobject_factors
- \- *lemma* category_theory.limits.equalizer_subobject_factors_iff
- \- *def* category_theory.limits.equalizer_subobject_iso
- \- *def* category_theory.limits.factor_thru_image_subobject
- \- *def* category_theory.limits.image_subobject
- \- *lemma* category_theory.limits.image_subobject_arrow'
- \- *lemma* category_theory.limits.image_subobject_arrow
- \- *lemma* category_theory.limits.image_subobject_arrow_comp
- \- *lemma* category_theory.limits.image_subobject_factors_comp_self
- \- *def* category_theory.limits.image_subobject_iso
- \- *lemma* category_theory.limits.image_subobject_iso_comp
- \- *lemma* category_theory.limits.image_subobject_le
- \- *lemma* category_theory.limits.image_subobject_le_mk
- \- *def* category_theory.limits.image_subobject_map
- \- *lemma* category_theory.limits.image_subobject_map_arrow
- \- *def* category_theory.limits.kernel_subobject
- \- *lemma* category_theory.limits.kernel_subobject_arrow'
- \- *lemma* category_theory.limits.kernel_subobject_arrow
- \- *lemma* category_theory.limits.kernel_subobject_arrow_comp
- \- *lemma* category_theory.limits.kernel_subobject_comp_mono
- \- *lemma* category_theory.limits.kernel_subobject_factors
- \- *lemma* category_theory.limits.kernel_subobject_factors_iff
- \- *def* category_theory.limits.kernel_subobject_iso
- \- *lemma* category_theory.limits.le_kernel_subobject

Added src/category_theory/subobject/limits.lean
- \+ *def* category_theory.limits.equalizer_subobject
- \+ *lemma* category_theory.limits.equalizer_subobject_arrow'
- \+ *lemma* category_theory.limits.equalizer_subobject_arrow
- \+ *lemma* category_theory.limits.equalizer_subobject_arrow_comp
- \+ *lemma* category_theory.limits.equalizer_subobject_factors
- \+ *lemma* category_theory.limits.equalizer_subobject_factors_iff
- \+ *def* category_theory.limits.equalizer_subobject_iso
- \+ *def* category_theory.limits.factor_thru_image_subobject
- \+ *def* category_theory.limits.image_subobject
- \+ *lemma* category_theory.limits.image_subobject_arrow'
- \+ *lemma* category_theory.limits.image_subobject_arrow
- \+ *lemma* category_theory.limits.image_subobject_arrow_comp
- \+ *lemma* category_theory.limits.image_subobject_factors_comp_self
- \+ *def* category_theory.limits.image_subobject_iso
- \+ *lemma* category_theory.limits.image_subobject_iso_comp
- \+ *lemma* category_theory.limits.image_subobject_le
- \+ *lemma* category_theory.limits.image_subobject_le_mk
- \+ *def* category_theory.limits.image_subobject_map
- \+ *lemma* category_theory.limits.image_subobject_map_arrow
- \+ *def* category_theory.limits.kernel_subobject
- \+ *lemma* category_theory.limits.kernel_subobject_arrow'
- \+ *lemma* category_theory.limits.kernel_subobject_arrow
- \+ *lemma* category_theory.limits.kernel_subobject_arrow_comp
- \+ *lemma* category_theory.limits.kernel_subobject_comp_mono
- \+ *lemma* category_theory.limits.kernel_subobject_factors
- \+ *lemma* category_theory.limits.kernel_subobject_factors_iff
- \+ *def* category_theory.limits.kernel_subobject_iso
- \+ *lemma* category_theory.limits.le_kernel_subobject



## [2021-04-14 23:14:44](https://github.com/leanprover-community/mathlib/commit/74e1e83)
feat(topological/homeomorph): the image of a set ([#7147](https://github.com/leanprover-community/mathlib/pull/7147))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.image

Modified src/topology/homeomorph.lean
- \+ *def* homeomorph.image



## [2021-04-14 23:14:43](https://github.com/leanprover-community/mathlib/commit/5052ad9)
feat(data/nat/basic): (∀ a : ℕ, m ∣ a ↔ n ∣ a) ↔ m = n ([#7132](https://github.com/leanprover-community/mathlib/pull/7132))
... and the dual statement
`(∀ a : ℕ, a ∣ m ↔ a ∣ n) ↔ m = n`
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/semilattice.2C.20dvd.2C.20associated
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.dvd_left_iff_eq
- \+ *lemma* nat.dvd_left_injective
- \+ *lemma* nat.dvd_right_iff_eq



## [2021-04-14 23:14:42](https://github.com/leanprover-community/mathlib/commit/4605b55)
feat(algebra/big_operators/finprod): add a few lemmas ([#7130](https://github.com/leanprover-community/mathlib/pull/7130))
* add `finprod_nonneg`, `finprod_cond_nonneg`, and `finprod_eq_zero`;
* use `α → Prop` instead of `set α` in
`finprod_mem_eq_prod_of_mem_iff`, rename to `finprod_cond_eq_prod_of_cond_iff`.
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_cond_eq_prod_of_cond_iff
- \+ *lemma* finprod_cond_nonneg
- \+ *lemma* finprod_eq_zero
- \- *lemma* finprod_mem_eq_prod_of_mem_iff
- \+ *lemma* finprod_nonneg



## [2021-04-14 23:14:41](https://github.com/leanprover-community/mathlib/commit/49fd719)
feat(topology/algebra,geometry/manifold): continuity and smoothness of locally finite products of functions ([#7128](https://github.com/leanprover-community/mathlib/pull/7128))
#### Estimated changes
Modified src/geometry/manifold/algebra/monoid.lean
- \+ *lemma* smooth_finprod
- \+ *lemma* smooth_finprod_cond
- \+ *lemma* smooth_finset_prod'
- \+ *lemma* smooth_finset_prod

Modified src/topology/algebra/monoid.lean
- \+/\- *lemma* continuous.mul
- \+/\- *lemma* continuous.pow
- \+/\- *lemma* continuous_at.mul
- \+ *lemma* continuous_finprod
- \+ *lemma* continuous_finprod_cond
- \+/\- *lemma* continuous_finset_prod
- \+/\- *lemma* continuous_list_prod
- \+/\- *lemma* continuous_multiset_prod
- \+/\- *lemma* continuous_on.mul
- \+/\- *lemma* continuous_within_at.mul
- \+/\- *lemma* filter.tendsto.mul
- \+/\- *lemma* tendsto_finset_prod
- \+/\- *lemma* tendsto_list_prod
- \+/\- *lemma* tendsto_multiset_prod

Modified src/topology/continuous_function/basic.lean
- \- *lemma* continuous_map.coe_continuous



## [2021-04-14 23:14:40](https://github.com/leanprover-community/mathlib/commit/d820a9d)
feat(algebra/big_operators): some lemmas on big operators and `fin` ([#7119](https://github.com/leanprover-community/mathlib/pull/7119))
A couple of lemmas that I needed for `det_vandermonde` ([#7116](https://github.com/leanprover-community/mathlib/pull/7116)).
I put them in a new file because I didn't see any obvious point that they fit in the import hierarchy. `big_operators/basic.lean` would be the alternative, but that file is big enough as it is.
#### Estimated changes
Added src/algebra/big_operators/fin.lean
- \+ *lemma* fin.prod_filter_succ_lt
- \+ *lemma* fin.prod_filter_zero_lt
- \+ *lemma* fin.sum_filter_succ_lt
- \+ *lemma* fin.sum_filter_zero_lt

Added src/data/fintype/fin.lean
- \+ *lemma* fin.univ_filter_succ_lt
- \+ *lemma* fin.univ_filter_zero_lt



## [2021-04-14 23:14:39](https://github.com/leanprover-community/mathlib/commit/8d3e8b5)
feat(archive/imo): IMO 1977 Q6 ([#7097](https://github.com/leanprover-community/mathlib/pull/7097))
Formalization of IMO 1977/6
#### Estimated changes
Added archive/imo/imo1977_q6.lean
- \+ *theorem* imo1977_q6
- \+ *theorem* imo1977_q6_nat



## [2021-04-14 23:14:38](https://github.com/leanprover-community/mathlib/commit/456e5af)
feat(order/filter/*, topology/subset_properties): Filter Coprod ([#7073](https://github.com/leanprover-community/mathlib/pull/7073))
Define the "coproduct" of many filters (not just two) as
`protected def Coprod (f : Π d, filter (κ d)) : filter (Π d, κ d) :=
⨆ d : δ, (f d).comap (λ k, k d)`
and prove the three lemmas which motivated this construction: (finite!) coproduct of cofinite filters is the cofinite filter, coproduct of cocompact filters is the cocompact filter, and monotonicity; see also [#6372](https://github.com/leanprover-community/mathlib/pull/6372)
Co-authored by: Heather Macbeth @hrmacbeth
#### Estimated changes
Modified src/data/set/basic.lean


Modified src/data/set/finite.lean
- \+ *lemma* set.finite.pi

Modified src/order/filter/basic.lean
- \+ *lemma* filter.Coprod_mono
- \+ *lemma* filter.map_pi_map_Coprod_le
- \+ *lemma* filter.mem_Coprod_iff
- \+ *lemma* filter.tendsto.pi_map_Coprod

Modified src/order/filter/cofinite.lean
- \+ *lemma* filter.Coprod_cofinite

Modified src/topology/subset_properties.lean
- \+ *lemma* filter.Coprod_cocompact



## [2021-04-14 23:14:37](https://github.com/leanprover-community/mathlib/commit/89196b2)
feat(group_theory/perm/cycle_type): Cycle type of a permutation ([#6999](https://github.com/leanprover-community/mathlib/pull/6999))
This PR defines the cycle type of a permutation.
At some point we should prove the bijection between partitions and conjugacy classes.
#### Estimated changes
Modified src/algebra/gcd_monoid.lean
- \+ *lemma* nat.gcd_eq_gcd
- \+ *lemma* nat.lcm_eq_lcm
- \+ *lemma* nat.normalize_eq

Added src/group_theory/perm/cycle_type.lean
- \+ *lemma* equiv.perm.card_cycle_type_eq_one
- \+ *lemma* equiv.perm.card_cycle_type_eq_zero
- \+ *def* equiv.perm.cycle_type
- \+ *lemma* equiv.perm.cycle_type_eq
- \+ *lemma* equiv.perm.cycle_type_eq_zero
- \+ *lemma* equiv.perm.cycle_type_inv
- \+ *lemma* equiv.perm.cycle_type_one
- \+ *lemma* equiv.perm.cycle_type_prime_order
- \+ *lemma* equiv.perm.disjoint.cycle_type
- \+ *lemma* equiv.perm.dvd_of_mem_cycle_type
- \+ *lemma* equiv.perm.is_cycle.cycle_type
- \+ *lemma* equiv.perm.is_cycle_of_prime_order''
- \+ *lemma* equiv.perm.is_cycle_of_prime_order'
- \+ *lemma* equiv.perm.is_cycle_of_prime_order
- \+ *lemma* equiv.perm.lcm_cycle_type
- \+ *lemma* equiv.perm.list_cycles_perm_list_cycles
- \+ *lemma* equiv.perm.mem_list_cycles_iff
- \+ *lemma* equiv.perm.one_lt_of_mem_cycle_type
- \+ *def* equiv.perm.partition
- \+ *lemma* equiv.perm.sign_of_cycle_type
- \+ *lemma* equiv.perm.sum_cycle_type
- \+ *lemma* equiv.perm.two_le_of_mem_cycle_type

Modified src/group_theory/perm/cycles.lean
- \+/\- *lemma* equiv.perm.cycle_induction_on

Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.nodup_of_pairwise_disjoint



## [2021-04-14 23:14:36](https://github.com/leanprover-community/mathlib/commit/5775ef7)
feat(order/ideal, order/pfilter, order/prime_ideal): added `ideal_inter_nonempty`, proved that a maximal ideal is prime ([#6924](https://github.com/leanprover-community/mathlib/pull/6924))
- `ideal_inter_nonempty`: the intersection of any two ideals is nonempty. A preorder with joins and this property satisfies that its ideal poset is a lattice.
- An ideal is prime iff `x \inf y \in I` implies `x \in I` or `y \in I`.
- A maximal ideal in a distributive lattice is prime.
#### Estimated changes
Modified src/order/ideal.lean
- \+ *lemma* order.ideal.coe_sup_eq
- \+ *lemma* order.ideal.eq_sup_of_le_sup
- \+ *lemma* order.ideal.lt_sup_principal_of_not_mem
- \+ *lemma* order.ideal.mem_coe
- \+ *lemma* order.ideal.mem_compl_of_ge
- \+/\- *lemma* order.ideal.mem_inf
- \+ *lemma* order.ideal.mem_principal
- \+/\- *lemma* order.ideal.mem_sup
- \+ *lemma* order.inter_nonempty

Modified src/order/pfilter.lean
- \+ *lemma* order.is_pfilter.of_def
- \+ *lemma* order.pfilter.mem_coe

Modified src/order/prime_ideal.lean
- \+ *lemma* order.ideal.is_prime.mem_or_mem
- \+ *lemma* order.ideal.is_prime.of_mem_or_mem
- \+ *lemma* order.ideal.is_prime_iff_mem_or_mem



## [2021-04-14 18:40:20](https://github.com/leanprover-community/mathlib/commit/3df0f77)
feat(topology/sheaves): Induced map on stalks ([#7092](https://github.com/leanprover-community/mathlib/pull/7092))
This PR defines stalk maps for morphisms of presheaves. We prove that a morphism of type-valued sheaves is an isomorphism if and only if all the stalk maps are isomorphisms.
A few more lemmas about unique gluing are also added, as well as docstrings.
#### Estimated changes
Modified src/topology/sheaves/sheaf_condition/equalizer_products.lean
- \+ *lemma* Top.presheaf.sheaf_condition_equalizer_products.res_π

Modified src/topology/sheaves/sheaf_condition/unique_gluing.lean
- \+ *lemma* Top.presheaf.res_π_apply
- \+ *lemma* Top.sheaf.eq_of_locally_eq'
- \+ *lemma* Top.sheaf.eq_of_locally_eq
- \+ *lemma* Top.sheaf.exists_unique_gluing'

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* Top.presheaf.app_bijective_of_stalk_functor_map_bijective
- \+ *lemma* Top.presheaf.app_injective_iff_stalk_functor_map_injective
- \+ *lemma* Top.presheaf.app_injective_of_stalk_functor_map_injective
- \+ *lemma* Top.presheaf.is_iso_iff_stalk_functor_map_iso
- \+ *lemma* Top.presheaf.is_iso_of_stalk_functor_map_iso
- \+ *lemma* Top.presheaf.section_ext
- \+ *lemma* Top.presheaf.stalk_functor_map_germ
- \+ *lemma* Top.presheaf.stalk_functor_map_germ_apply
- \+ *lemma* Top.presheaf.stalk_functor_map_injective_of_app_injective



## [2021-04-14 18:40:15](https://github.com/leanprover-community/mathlib/commit/98c483b)
feat(ring_theory/hahn_series): a `finsupp` of Hahn series is a `summable_family` ([#7091](https://github.com/leanprover-community/mathlib/pull/7091))
Defines `summable_family.of_finsupp`
#### Estimated changes
Modified src/order/well_founded_set.lean
- \+ *theorem* finset.is_wf_sup

Modified src/ring_theory/hahn_series.lean
- \+/\- *def* hahn_series.C
- \- *lemma* hahn_series.C_apply
- \+ *def* hahn_series.coeff.add_monoid_hom
- \+ *def* hahn_series.coeff.linear_map
- \+/\- *def* hahn_series.single.add_monoid_hom
- \- *lemma* hahn_series.single.add_monoid_hom_apply
- \+/\- *def* hahn_series.single.linear_map
- \- *lemma* hahn_series.single.linear_map_apply
- \+ *lemma* hahn_series.summable_family.co_support_of_finsupp
- \+ *lemma* hahn_series.summable_family.coe_of_finsupp
- \+ *lemma* hahn_series.summable_family.hsum_of_finsupp
- \+/\- *def* hahn_series.summable_family.lsum
- \- *lemma* hahn_series.summable_family.lsum_apply
- \+ *def* hahn_series.summable_family.of_finsupp
- \+/\- *def* hahn_series.to_power_series
- \+/\- *def* hahn_series.to_power_series_alg
- \- *lemma* hahn_series.to_power_series_alg_apply
- \- *lemma* hahn_series.to_power_series_alg_symm_apply



## [2021-04-14 18:40:13](https://github.com/leanprover-community/mathlib/commit/f444128)
chore(algebra/direct_sum_graded): golf proofs ([#7029](https://github.com/leanprover-community/mathlib/pull/7029))
Simplify the proofs of mul_assoc and mul_comm, and speed up all the
proofs that were slow.
Total elaboration time for this file is reduced from 12.9s to 1.7s
(on my machine), and total CPU time is reduced from 19.8s to 6.8s.
All the remaining elaboration times are under 200ms.
The main idea is to explicitly construct bundled homomorphisms
corresponding to `λ a b c, a * b * c` and `λ a b c, a * (b * c)`
respectively.  Then in proving the equality between those, we can
unpack all the arguments immediately, and the remaining rewrites
needed become simpler.
#### Estimated changes
Modified src/algebra/direct_sum.lean
- \+ *lemma* direct_sum.add_hom_ext'
- \+ *lemma* direct_sum.add_hom_ext

Modified src/algebra/direct_sum_graded.lean
- \+ *def* direct_sum.mul_hom
- \+ *lemma* direct_sum.mul_hom_of_of

Modified src/algebra/group/hom.lean
- \+ *def* monoid_hom.flip_hom



## [2021-04-14 18:40:11](https://github.com/leanprover-community/mathlib/commit/3379f3e)
feat(archive/100-theorems-list): add proof of Heron's formula ([#6989](https://github.com/leanprover-community/mathlib/pull/6989))
This proves Heron's Formula for triangles, which happens to be Theorem 57 on Freek's 100 Theorems.
#### Estimated changes
Added archive/100-theorems-list/57_herons_formula.lean
- \+ *theorem* heron

Modified docs/100.yaml


Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* real.cos_eq_sqrt_one_sub_sin_sq
- \+ *lemma* real.cos_nonneg_of_neg_pi_div_two_le_of_le
- \+ *lemma* real.sin_eq_sqrt_one_sub_cos_sq

Modified src/data/complex/exponential.lean
- \+ *lemma* real.abs_cos_eq_sqrt_one_sub_sin_sq
- \+ *lemma* real.abs_sin_eq_sqrt_one_sub_cos_sq



## [2021-04-14 18:40:10](https://github.com/leanprover-community/mathlib/commit/2715769)
feat(geometry/manifold/instances/units_of_normed_algebra): the units of a normed algebra are a topological group and a smooth manifold ([#6981](https://github.com/leanprover-community/mathlib/pull/6981))
I decided to make a small PR now with only a partial result because Heather suggested proving GL^n is a Lie group on Zulip, and I wanted to share the work I did so that whoever wants to take over the task does not have to start from scratch.
Most of the ideas in this PR are by @hrmacbeth, as I was planning on doing a different proof, but I agreed Heather's one was better.
What remains to do in a future PR to prove GLn is a Lie group is to add and prove the following instance to the file `geometry/manifold/instances/units_of_normed_algebra.lean`:
```
instance units_of_normed_algebra.lie_group
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] :
  lie_group (model_with_corners_self 𝕜 R) (units R) :=
{
  smooth_mul := begin
    sorry,
  end,
  smooth_inv := begin
    sorry,
  end,
  ..units_of_normed_algebra.smooth_manifold_with_corners, /- Why does it not find the instance alone? -/
}
```
#### Estimated changes
Modified src/algebra/group/prod.lean
- \+ *def* embed_product

Modified src/analysis/normed_space/units.lean
- \+ *lemma* units.is_open_map_coe
- \+ *lemma* units.open_embedding_coe

Modified src/geometry/manifold/charted_space.lean
- \+/\- *lemma* chart_at_self_eq
- \+ *def* local_homeomorph.singleton_charted_space
- \+ *lemma* local_homeomorph.singleton_charted_space_chart_at_eq
- \+ *lemma* local_homeomorph.singleton_charted_space_chart_at_source
- \+ *lemma* local_homeomorph.singleton_charted_space_mem_atlas_eq
- \+ *lemma* local_homeomorph.singleton_has_groupoid
- \+ *def* open_embedding.singleton_charted_space
- \+ *lemma* open_embedding.singleton_charted_space_chart_at_eq
- \+ *lemma* open_embedding.singleton_has_groupoid
- \- *def* singleton_charted_space
- \- *lemma* singleton_charted_space_one_chart
- \- *lemma* singleton_has_groupoid

Added src/geometry/manifold/instances/units_of_normed_algebra.lean
- \+ *lemma* units.chart_at_apply
- \+ *lemma* units.chart_at_source

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* local_homeomorph.singleton_smooth_manifold_with_corners
- \+ *lemma* open_embedding.singleton_smooth_manifold_with_corners
- \+ *lemma* smooth_manifold_with_corners.mk'

Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean
- \+ *lemma* continuous_op
- \+ *lemma* continuous_unop
- \+ *lemma* units.continuous_coe
- \+ *lemma* units.continuous_embed_product



## [2021-04-14 18:40:08](https://github.com/leanprover-community/mathlib/commit/e4edf46)
feat(algebra/direct_sum_graded): `A 0` is a ring, `A i` is an `A 0`-module, and `direct_sum.of A 0` is a ring_hom ([#6851](https://github.com/leanprover-community/mathlib/pull/6851))
In a graded ring, grade 0 is itself a ring, and grade `i` (and therefore, the overall direct_sum) is a module over elements of grade 0.
This stops just short of the structure necessary to make a graded ring a graded algebra over elements of grade 0; this requires some extra assumptions and probably a new typeclass, so is best left to its own PR.
The main results here are `direct_sum.grade_zero.comm_ring`, `direct_sum.grade_zero.semimodule`, and `direct_sum.of_zero_ring_hom`.
Note that we have no way to let the user provide their own ring structure on `A 0`, as `[Π i, add_comm_monoid (A i)] [semiring (A 0)]` provides `add_comm_monoid (A 0)` twice.
#### Estimated changes
Modified src/algebra/direct_sum_graded.lean
- \+ *lemma* direct_sum.grade_zero.smul_eq_mul
- \+ *lemma* direct_sum.of_zero_mul
- \+ *lemma* direct_sum.of_zero_one
- \+ *def* direct_sum.of_zero_ring_hom
- \+ *lemma* direct_sum.of_zero_smul



## [2021-04-14 18:40:07](https://github.com/leanprover-community/mathlib/commit/24dc410)
feat(field_theory/separable_degree): introduce the separable degree ([#6743](https://github.com/leanprover-community/mathlib/pull/6743))
We introduce the definition of the separable degree of a polynomial. We prove that every irreducible polynomial can be contracted to a separable polynomial. We show that the separable degree divides the degree of the polynomial.
This formalizes a lemma in the Stacks Project, cf. https://stacks.math.columbia.edu/tag/09H0 
We also show that the separable degree is unique.
#### Estimated changes
Modified src/field_theory/separable.lean
- \+ *lemma* polynomial.expand_injective

Added src/field_theory/separable_degree.lean
- \+ *lemma* polynomial.contraction_degree_eq_aux
- \+ *theorem* polynomial.contraction_degree_eq_or_insep
- \+ *def* polynomial.has_separable_contraction.contraction
- \+ *def* polynomial.has_separable_contraction.degree
- \+ *lemma* polynomial.has_separable_contraction.dvd_degree'
- \+ *lemma* polynomial.has_separable_contraction.dvd_degree
- \+ *lemma* polynomial.has_separable_contraction.eq_degree
- \+ *def* polynomial.has_separable_contraction
- \+ *lemma* polynomial.irreducible_has_separable_contraction
- \+ *theorem* polynomial.is_separable_contraction.degree_eq
- \+ *lemma* polynomial.is_separable_contraction.dvd_degree'
- \+ *def* polynomial.is_separable_contraction



## [2021-04-14 18:40:05](https://github.com/leanprover-community/mathlib/commit/f12575e)
feat(topology/topological_fiber_bundle): topological fiber bundle over `[a, b]` is trivial ([#6555](https://github.com/leanprover-community/mathlib/pull/6555))
#### Estimated changes
Modified src/topology/topological_fiber_bundle.lean
- \+ *lemma* bundle_trivialization.continuous_coord_change
- \+ *def* bundle_trivialization.coord_change
- \+ *lemma* bundle_trivialization.coord_change_apply_snd
- \+ *lemma* bundle_trivialization.coord_change_coord_change
- \+ *def* bundle_trivialization.coord_change_homeomorph
- \+ *lemma* bundle_trivialization.coord_change_homeomorph_coe
- \+ *lemma* bundle_trivialization.coord_change_same
- \+ *lemma* bundle_trivialization.coord_change_same_apply
- \+ *lemma* bundle_trivialization.frontier_preimage
- \+ *lemma* bundle_trivialization.is_image_preimage_prod
- \+ *lemma* bundle_trivialization.mk_coord_change
- \+ *lemma* bundle_trivialization.mk_proj_snd'
- \+ *lemma* bundle_trivialization.mk_proj_snd
- \+ *def* bundle_trivialization.restr_open
- \+ *def* bundle_trivialization.trans_fiber_homeomorph
- \+ *lemma* bundle_trivialization.trans_fiber_homeomorph_apply
- \+ *lemma* is_topological_fiber_bundle.exists_trivialization_Icc_subset



## [2021-04-14 16:58:05](https://github.com/leanprover-community/mathlib/commit/b3eabc1)
hack(ci): run lean make twice ([#7192](https://github.com/leanprover-community/mathlib/pull/7192))
At the moment running `lean --make src` after `leanproject up` will recompile some files.  Merging this PR should have the effect of uploading these newly compiled olean files.
This also makes github actions call `lean --make src` twice to prevent this problem from happening in the first place.
#### Estimated changes
Modified .github/workflows/build.yml


Modified README.md




## [2021-04-14 08:29:46](https://github.com/leanprover-community/mathlib/commit/6380155)
refactor(*): kill nat multiplication diamonds ([#7084](https://github.com/leanprover-community/mathlib/pull/7084))
An `add_monoid` has a natural `ℕ`-action, defined by `n • a = a + ... + a`, that we want to declare
as an instance as it makes it possible to use the language of linear algebra. However, there are
often other natural `ℕ`-actions. For instance, for any semiring `R`, the space of polynomials
`polynomial R` has a natural `R`-action defined by multiplication on the coefficients. This means
that `polynomial ℕ` has two natural `ℕ`-actions, which are equal but not defeq. The same
goes for linear maps, tensor products, and so on (and even for `ℕ` itself). This is the case on current
mathlib, with such non-defeq diamonds all over the place.
To solve this issue, we embed an `ℕ`-action in the definition of an `add_monoid` (which is by
default the naive action `a + ... + a`, but can be adjusted when needed -- it should always be equal 
to this one, but not necessarily definitionally), and declare
a `has_scalar ℕ α` instance using this action. This is yet another example of the forgetful inheritance
pattern that we use in metric spaces, embedding a topology and a uniform structure in it (except that
here the functor from additive monoids to nat-modules is faithful instead of forgetful, but it doesn't 
make a difference).
More precisely, we define
```lean
def nsmul_rec [has_add M] [has_zero M] : ℕ → M → M
| 0     a := 0
| (n+1) a := nsmul_rec n a + a
class add_monoid (M : Type u) extends add_semigroup M, add_zero_class M :=
(nsmul : ℕ → M → M := nsmul_rec)
(nsmul_zero' : ∀ x, nsmul 0 x = 0 . try_refl_tac)
(nsmul_succ' : ∀ (n : ℕ) x, nsmul n.succ x = nsmul n x + x . try_refl_tac)
```
For example, when we define `polynomial R`, then we declare the `ℕ`-action to be by multiplication
on each coefficient (using the `ℕ`-action on `R` that comes from the fact that `R` is
an `add_monoid`). In this way, the two natural `has_scalar ℕ (polynomial ℕ)` instances are defeq.
The tactic `to_additive` transfers definitions and results from multiplicative monoids to additive
monoids. To work, it has to map fields to fields. This means that we should also add corresponding
fields to the multiplicative structure `monoid`, which could solve defeq problems for powers if
needed. These problems do not come up in practice, so most of the time we will not need to adjust
the `npow` field when defining multiplicative objects.
With this refactor, all the diamonds are gone. Or rather, all the diamonds I noticed are gone, but if
there are still some diamonds then they can be fixed, contrary to before.
Also, the notation `•ℕ` is gone, just use `•`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *def* ring_hom.to_nat_alg_hom

Modified src/algebra/algebra/subalgebra.lean
- \+/\- *theorem* subalgebra.nsmul_mem

Modified src/algebra/archimedean.lean


Modified src/algebra/associated.lean


Modified src/algebra/big_operators/basic.lean


Modified src/algebra/char_p/basic.lean


Modified src/algebra/field_power.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/group/defs.lean
- \+ *lemma* npow_add
- \+ *lemma* npow_one
- \+ *def* npow_rec
- \+ *lemma* nsmul_one'
- \+ *def* nsmul_rec

Modified src/algebra/group/pi.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/type_tags.lean


Modified src/algebra/group/ulift.lean


Modified src/algebra/group_power/basic.lean
- \+/\- *theorem* add_monoid_hom.map_nsmul
- \+/\- *theorem* add_nsmul
- \+/\- *theorem* bit0_nsmul'
- \+/\- *theorem* bit0_nsmul
- \+/\- *theorem* bit1_nsmul'
- \+/\- *theorem* bit1_nsmul
- \+/\- *theorem* gpow_zero
- \+/\- *theorem* gsmul_coe_nat
- \+/\- *theorem* gsmul_neg_succ_of_nat
- \+/\- *theorem* gsmul_of_nat
- \- *def* monoid.pow
- \- *lemma* monoid.pow_eq_has_pow
- \+/\- *theorem* mul_nsmul'
- \+/\- *theorem* mul_nsmul
- \+/\- *theorem* neg_nsmul
- \+ *lemma* npow_eq_pow
- \- *def* nsmul
- \+/\- *theorem* nsmul_add
- \+/\- *theorem* nsmul_add_comm'
- \+/\- *theorem* nsmul_add_comm
- \+/\- *theorem* nsmul_add_sub_nsmul
- \+ *lemma* nsmul_eq_smul
- \+/\- *theorem* nsmul_le_nsmul
- \+/\- *lemma* nsmul_le_nsmul_of_le_right
- \+/\- *theorem* nsmul_neg_comm
- \+/\- *theorem* nsmul_nonneg
- \+/\- *lemma* nsmul_pos
- \+/\- *theorem* nsmul_sub
- \+/\- *theorem* nsmul_zero
- \+/\- *theorem* one_gsmul
- \+/\- *theorem* one_nsmul
- \+/\- *theorem* pow_one
- \+/\- *theorem* pow_succ
- \+/\- *theorem* pow_zero
- \+/\- *theorem* sub_nsmul_nsmul_add
- \+/\- *theorem* succ_nsmul'
- \+/\- *theorem* succ_nsmul
- \+/\- *theorem* two_nsmul
- \+/\- *theorem* zero_gsmul
- \+/\- *theorem* zero_nsmul

Modified src/algebra/group_power/lemmas.lean
- \+/\- *theorem* list.sum_repeat
- \+/\- *theorem* mul_nsmul_assoc
- \+/\- *theorem* mul_nsmul_left
- \+/\- *theorem* nat.nsmul_eq_mul
- \+/\- *theorem* nsmul_eq_mul'
- \+/\- *theorem* nsmul_eq_mul
- \+/\- *theorem* nsmul_le_nsmul_iff
- \+/\- *theorem* nsmul_lt_nsmul_iff
- \+/\- *theorem* nsmul_one

Modified src/algebra/group_ring_action.lean


Modified src/algebra/group_with_zero/power.lean
- \+/\- *theorem* fpow_one
- \+/\- *theorem* fpow_zero

Modified src/algebra/iterate_hom.lean
- \+/\- *lemma* add_left_iterate

Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/module/basic.lean
- \- *def* add_comm_monoid.nat_semimodule
- \+/\- *lemma* nat.smul_one_eq_coe
- \- *lemma* nsmul_def
- \- *lemma* nsmul_eq_smul

Modified src/algebra/module/linear_map.lean


Modified src/algebra/monoid_algebra.lean


Modified src/algebra/ordered_pi.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/punit_instances.lean


Modified src/algebra/ring/basic.lean


Modified src/algebra/ring/pi.lean


Modified src/algebra/ring/ulift.lean


Modified src/algebra/ring_quot.lean


Modified src/algebra/smul_regular.lean


Modified src/algebra/smul_with_zero.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/p_series.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/category_theory/endomorphism.lean


Modified src/category_theory/monoidal/internal/Module.lean


Modified src/combinatorics/pigeonhole.lean
- \+/\- *lemma* fintype.exists_le_sum_fiber_of_nsmul_le_sum
- \+/\- *lemma* fintype.exists_lt_sum_fiber_of_nsmul_lt_sum
- \+/\- *lemma* fintype.exists_sum_fiber_le_of_sum_le_nsmul
- \+/\- *lemma* fintype.exists_sum_fiber_lt_of_sum_lt_nsmul

Modified src/data/buffer/parser/basic.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/equiv/mul_add_aut.lean


Modified src/data/equiv/ring_aut.lean


Modified src/data/finset/basic.lean


Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.to_multiset_apply
- \+/\- *lemma* finsupp.to_multiset_single

Modified src/data/holor.lean


Modified src/data/int/gcd.lean
- \+/\- *lemma* gcd_nsmul_eq_zero

Modified src/data/multiset/basic.lean
- \+/\- *theorem* multiset.count_nsmul
- \+/\- *theorem* multiset.map_nsmul

Modified src/data/multiset/erase_dup.lean


Modified src/data/multiset/fold.lean


Modified src/data/mv_polynomial/basic.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/nat/basic.lean
- \+ *lemma* nat.succ_eq_one_add

Modified src/data/nat/choose/sum.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/prime.lean


Modified src/data/num/lemmas.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/pfun.lean
- \+ *lemma* roption.get_eq_get_of_eq

Modified src/data/pnat/factors.lean


Modified src/data/polynomial/basic.lean


Modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* polynomial.degree_pow'
- \+/\- *lemma* polynomial.degree_pow_le

Modified src/data/polynomial/degree/lemmas.lean


Modified src/data/polynomial/monic.lean


Modified src/data/quaternion.lean


Modified src/data/real/basic.lean


Modified src/data/real/cardinality.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/irrational.lean


Modified src/data/real/nnreal.lean
- \+/\- *lemma* nnreal.nsmul_coe

Modified src/data/zsqrtd/basic.lean


Modified src/deprecated/submonoid.lean
- \+/\- *def* multiples

Modified src/field_theory/adjoin.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/field_theory/galois.lean


Modified src/field_theory/intermediate_field.lean


Modified src/field_theory/separable.lean


Modified src/geometry/manifold/algebra/monoid.lean


Modified src/group_theory/archimedean.lean


Modified src/group_theory/monoid_localization.lean


Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* add_order_of_dvd_iff_nsmul_eq_zero
- \+/\- *lemma* add_order_of_dvd_of_nsmul_eq_zero
- \+/\- *lemma* add_order_of_eq_zero
- \+/\- *lemma* add_order_of_le_of_nsmul_eq_zero'
- \+/\- *lemma* add_order_of_le_of_nsmul_eq_zero
- \+/\- *lemma* add_order_of_nsmul''
- \+/\- *lemma* add_order_of_nsmul_eq_zero
- \+/\- *lemma* add_order_of_pos'
- \+/\- *lemma* card_nsmul_eq_zero
- \+/\- *lemma* exists_nsmul_eq_zero
- \+/\- *lemma* nsmul_eq_mod_add_order_of

Modified src/group_theory/subgroup.lean
- \+/\- *lemma* add_subgroup.coe_smul

Modified src/group_theory/submonoid/membership.lean


Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/basic.lean
- \+ *theorem* submodule.quotient.mk_nsmul

Modified src/linear_algebra/dual.lean
- \+/\- *lemma* vector_space.eval_equiv_to_linear_map

Modified src/linear_algebra/multilinear.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/logic/basic.lean


Modified src/measure_theory/arithmetic.lean


Modified src/number_theory/dioph.lean


Modified src/order/filter/archimedean.lean


Modified src/order/filter/at_top_bot.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/bernstein.lean


Modified src/ring_theory/subsemiring.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *theorem* associates.pow_factors

Modified src/set_theory/ordinal_notation.lean


Modified src/tactic/abel.lean
- \+/\- *def* tactic.abel.smul
- \+/\- *def* tactic.abel.term

Modified src/tactic/interactive.lean


Modified src/tactic/norm_num.lean


Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.continuous.nsmul
- \+ *lemma* continuous_linear_map.continuous_nsmul

Modified src/topology/algebra/monoid.lean


Modified src/topology/metric_space/lipschitz.lean


Modified src/topology/uniform_space/basic.lean


Modified test/equiv_rw.lean


Modified test/refine_struct.lean


Modified test/transport/basic.lean




## [2021-04-14 03:47:14](https://github.com/leanprover-community/mathlib/commit/3ec54df)
feat(data/finset/lattice): le_sup_iff and lt_sup_iff ([#7182](https://github.com/leanprover-community/mathlib/pull/7182))
A few changes and additions to finset/lattice in response to this Zulip thread https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/finset.2Esup'
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.exists_mem_eq_inf'
- \+/\- *lemma* finset.exists_mem_eq_inf
- \+ *lemma* finset.exists_mem_eq_sup'
- \+/\- *lemma* finset.exists_mem_eq_sup
- \+ *lemma* finset.inf'_induction
- \+ *lemma* finset.inf'_le_iff
- \+ *lemma* finset.inf'_lt_iff
- \+ *lemma* finset.inf_induction
- \+ *lemma* finset.inf_le_iff
- \+ *lemma* finset.inf_lt_iff
- \+ *lemma* finset.le_sup'_iff
- \+ *lemma* finset.le_sup_iff
- \+/\- *lemma* finset.lt_inf_iff
- \+ *lemma* finset.lt_sup'_iff
- \+ *lemma* finset.lt_sup_iff
- \- *lemma* finset.of_inf'_of_forall
- \- *lemma* finset.of_inf_of_forall
- \- *lemma* finset.of_sup'_of_forall
- \- *lemma* finset.of_sup_of_forall
- \+ *lemma* finset.sup'_induction
- \+ *lemma* finset.sup_induction



## [2021-04-14 03:47:13](https://github.com/leanprover-community/mathlib/commit/500301e)
feat(algebra/group/hom): `monoid_with_zero_hom.to_monoid_hom_injective` and co. ([#7174](https://github.com/leanprover-community/mathlib/pull/7174))
This came up in [#6788](https://github.com/leanprover-community/mathlib/pull/6788).
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.to_mul_hom_injective
- \+ *lemma* monoid_hom.to_one_hom_injective
- \+ *lemma* monoid_with_zero_hom.to_monoid_hom_injective
- \+ *lemma* monoid_with_zero_hom.to_zero_hom_injective



## [2021-04-14 03:47:12](https://github.com/leanprover-community/mathlib/commit/4d19f5f)
feat(algebraic_geometry): Basic opens form basis of zariski topology ([#7152](https://github.com/leanprover-community/mathlib/pull/7152))
Fills in a few lemmas in `prime_spectrum.lean`, in particular that basic opens form a basis
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean
- \+ *lemma* prime_spectrum.basic_open_eq_zero_locus_compl
- \+ *lemma* prime_spectrum.is_topological_basis_basic_opens
- \+ *lemma* prime_spectrum.vanishing_ideal_anti_mono
- \+ *lemma* prime_spectrum.zero_locus_anti_mono
- \+ *lemma* prime_spectrum.zero_locus_anti_mono_ideal



## [2021-04-13 23:14:15](https://github.com/leanprover-community/mathlib/commit/724f804)
refactor(src/analysis/normed_space/linear_isometry): generalize to semi_normed_group ([#7122](https://github.com/leanprover-community/mathlib/pull/7122))
This is part of a series of PR to include the theory of seminormed things in mathlib.
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+/\- *lemma* linear_isometry.map_eq_iff
- \+/\- *lemma* linear_isometry.map_ne
- \+/\- *structure* linear_isometry
- \+/\- *structure* linear_isometry_equiv

Modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* is_R_or_C.conj_clm_norm

Modified src/data/padics/padic_integers.lean


Modified src/measure_theory/set_integral.lean


Modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* antilipschitz_with.comap_uniformity_le
- \+ *lemma* antilipschitz_with.is_closed_range
- \+ *lemma* antilipschitz_with.is_complete_range
- \- *lemma* antilipschitz_with.uniform_embedding
- \- *lemma* antilipschitz_with.uniform_embedding_of_injective

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/isometry.lean
- \+/\- *lemma* isometry.comp_continuous_iff
- \+/\- *lemma* isometry.comp_continuous_on_iff
- \+ *theorem* isometry.uniform_inducing

Modified src/topology/metric_space/pi_Lp.lean


Modified src/topology/uniform_space/basic.lean
- \+ *lemma* to_nhds_mono

Modified src/topology/uniform_space/uniform_embedding.lean
- \+/\- *lemma* complete_space_iff_is_complete_range
- \+/\- *lemma* is_complete_image_iff
- \+ *lemma* uniform_inducing.is_complete_range



## [2021-04-13 19:58:08](https://github.com/leanprover-community/mathlib/commit/06f7d3f)
feat(src/set_theory/surreal): add numeric_add and numeric_omega lemmas ([#7179](https://github.com/leanprover-community/mathlib/pull/7179))
Adds a couple of lemmas about surreal numbers: proving that natural numbers and omega are numeric.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers/near/234243582)
#### Estimated changes
Modified src/set_theory/surreal.lean
- \+ *theorem* pgame.numeric_nat
- \+ *theorem* pgame.numeric_omega



## [2021-04-12 23:25:53](https://github.com/leanprover-community/mathlib/commit/46302c7)
refactor(algebra/group/defs): remove left-right_cancel_comm_monoids ([#7134](https://github.com/leanprover-community/mathlib/pull/7134))
There were 6 distinct classes
* `(add_)left_cancel_comm_monoid`,
* `(add_)right_cancel_comm_monoid`,
* `(add_)cancel_comm_monoid`.
I removed them all, except for the last 2:
* `(add_)cancel_comm_monoid`.
The new typeclass `cancel_comm_monoid` requires only `a * b = a * c → b = c`, and deduces the other version from commutativity.
#### Estimated changes
Modified src/algebra/group/defs.lean


Modified src/algebra/group/inj_surj.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/punit_instances.lean


Modified src/data/finsupp/basic.lean


Modified src/data/multiset/basic.lean


Modified src/data/nat/basic.lean


Modified src/data/num/lemmas.lean


Modified src/data/pnat/basic.lean
- \+ *lemma* pnat.coe_injective

Modified src/data/real/nnreal.lean


Modified src/order/filter/germ.lean




## [2021-04-12 19:13:54](https://github.com/leanprover-community/mathlib/commit/92d5cab)
feat(logic/function/iterate): `f^[n]^[m] = f^[m]^[n]` ([#7121](https://github.com/leanprover-community/mathlib/pull/7121))
Prove `f^[n]^[m]=f^[m]^[n]` and improve some docs.
#### Estimated changes
Modified src/logic/function/conjugate.lean


Modified src/logic/function/iterate.lean
- \+ *lemma* function.iterate_comm
- \+ *lemma* function.iterate_commute



## [2021-04-12 15:23:30](https://github.com/leanprover-community/mathlib/commit/2af0147)
chore(data/equiv/basic): add simps attribute to some defs ([#7137](https://github.com/leanprover-community/mathlib/pull/7137))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.empty_sum
- \+/\- *def* equiv.pempty_sum
- \+/\- *def* equiv.sum_empty
- \+/\- *def* equiv.sum_pempty



## [2021-04-12 12:44:29](https://github.com/leanprover-community/mathlib/commit/a1c2bb7)
feat(data/zsqrtd/basic): add coe_int_dvd_iff lemma ([#7161](https://github.com/leanprover-community/mathlib/pull/7161))
#### Estimated changes
Modified src/data/zsqrtd/basic.lean
- \+ *lemma* zsqrtd.coe_int_dvd_iff



## [2021-04-12 12:44:28](https://github.com/leanprover-community/mathlib/commit/16e2c6c)
chore(data/matrix/basic): lemmas for `minor` about `diagonal`, `one`, and `mul` ([#7133](https://github.com/leanprover-community/mathlib/pull/7133))
The `minor_mul` lemma here has weaker hypotheses than the previous `reindex_mul`, as it only requires one mapping to be bijective.
#### Estimated changes
Modified src/algebra/lie/matrix.lean


Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.minor_diagonal
- \+ *lemma* matrix.minor_diagonal_embedding
- \+ *lemma* matrix.minor_diagonal_equiv
- \+ *lemma* matrix.minor_mul
- \+ *lemma* matrix.minor_mul_equiv
- \+ *lemma* matrix.minor_one
- \+ *lemma* matrix.minor_one_embedding
- \+ *lemma* matrix.minor_one_equiv
- \+/\- *lemma* matrix.minor_smul

Modified src/linear_algebra/matrix.lean
- \- *lemma* matrix.reindex_mul



## [2021-04-12 08:44:54](https://github.com/leanprover-community/mathlib/commit/f9c787d)
refactor(algebra/big_operators, *): specialize `finset.prod_bij` to `fintype.prod_equiv` ([#7109](https://github.com/leanprover-community/mathlib/pull/7109))
Often we want to apply `finset.prod_bij` to the case where the product is taken over `finset.univ` and the bijection is already a bundled `equiv`. This PR adds `fintype.prod_equiv` as a specialization for exactly these cases, filling in most of the arguments already.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* fintype.prod_bijective
- \+ *lemma* fintype.prod_equiv

Modified src/algebra/polynomial/group_ring_action.lean


Modified src/data/equiv/basic.lean


Modified src/data/fintype/card.lean


Modified src/linear_algebra/determinant.lean




## [2021-04-12 08:44:53](https://github.com/leanprover-community/mathlib/commit/001628b)
feat(category_theory/subobject/factor_thru): lemmas in a preadditive category ([#7104](https://github.com/leanprover-community/mathlib/pull/7104))
More side effects of recent reworking of homology.
#### Estimated changes
Modified src/category_theory/subobject/factor_thru.lean
- \+ *lemma* category_theory.subobject.factor_thru_add
- \+ *lemma* category_theory.subobject.factor_thru_add_sub_factor_thru_left
- \+ *lemma* category_theory.subobject.factor_thru_add_sub_factor_thru_right
- \+ *lemma* category_theory.subobject.factors_add
- \+ *lemma* category_theory.subobject.factors_left_of_factors_add
- \+ *lemma* category_theory.subobject.factors_right_of_factors_add



## [2021-04-12 08:44:51](https://github.com/leanprover-community/mathlib/commit/68e894d)
feat(finset/lattice): sup' is to sup as max' is to max ([#7087](https://github.com/leanprover-community/mathlib/pull/7087))
Introducing `finset.sup'`, modelled on `finset.max'` but having no need for a `linear_order`. I wanted this for functions so also provide `sup_apply` and `sup'_apply`. By using `cons` instead of `insert` the axiom of choice is avoided throughout and I have replaced the proofs of three existing lemmas (`sup_lt_iff`, `comp_sup_eq_sup_comp`, `sup_closed_of_sup_closed`) that didn't need it. I have removed `sup_subset` entirely as it was surely introduced in ignorance of `sup_mono`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.cons_induction
- \+ *lemma* finset.cons_induction_on

Modified src/data/finset/fold.lean
- \+ *theorem* finset.fold_cons

Modified src/data/finset/lattice.lean
- \+ *lemma* finset.coe_inf'
- \+ *lemma* finset.coe_sup'
- \+ *def* finset.inf'
- \+ *lemma* finset.inf'_apply
- \+ *lemma* finset.inf'_cons
- \+ *lemma* finset.inf'_eq_inf
- \+ *lemma* finset.inf'_insert
- \+ *lemma* finset.inf'_le
- \+ *lemma* finset.inf'_singleton
- \+ *lemma* finset.inf_closed_of_inf_closed
- \+ *lemma* finset.inf_cons
- \+ *lemma* finset.inf_of_mem
- \+ *lemma* finset.le_inf'
- \+ *lemma* finset.le_inf'_iff
- \+/\- *lemma* finset.le_inf_iff
- \+ *lemma* finset.le_sup'
- \+ *lemma* finset.lt_inf'_iff
- \+ *lemma* finset.of_inf'_of_forall
- \+ *lemma* finset.of_inf_of_forall
- \+ *lemma* finset.of_sup'_of_forall
- \+ *lemma* finset.of_sup_of_forall
- \+ *def* finset.sup'
- \+ *lemma* finset.sup'_apply
- \+ *lemma* finset.sup'_cons
- \+ *lemma* finset.sup'_eq_sup
- \+ *lemma* finset.sup'_insert
- \+ *lemma* finset.sup'_le
- \+ *lemma* finset.sup'_le_iff
- \+ *lemma* finset.sup'_lt_iff
- \+ *lemma* finset.sup'_singleton
- \+ *lemma* finset.sup_cons
- \+/\- *lemma* finset.sup_lt_iff
- \+ *lemma* finset.sup_of_mem
- \- *lemma* finset.sup_subset

Modified src/data/mv_polynomial/variables.lean




## [2021-04-12 05:36:40](https://github.com/leanprover-community/mathlib/commit/193dd5b)
feat(algebra/{algebra, module}/basic): make 3 smultiplication by 1 `simp` lemmas ([#7166](https://github.com/leanprover-community/mathlib/pull/7166))
The three lemmas in the merged PR [#7094](https://github.com/leanprover-community/mathlib/pull/7094) could be simp lemmas.  This PR makes this suggestion.
While I was at it,
* I moved one of the lemmas outside of the `alg_hom` namespace,
* I fixed a typo in a doc string of a tutorial.
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/trying.20out.20a.20.60simp.60.20lemma
#### Estimated changes
Modified docs/tutorial/Zmod37.lean


Modified src/algebra/algebra/basic.lean
- \- *lemma* alg_hom.rat.smul_one_eq_coe
- \+ *lemma* rat.smul_one_eq_coe

Modified src/algebra/module/basic.lean
- \+/\- *lemma* int.smul_one_eq_coe
- \+/\- *lemma* nat.smul_one_eq_coe



## [2021-04-11 12:32:54](https://github.com/leanprover-community/mathlib/commit/5694309)
feat(algebra/algebra/basic algebra/module/basic): add 3 lemmas m • (1 : R) = ↑m ([#7094](https://github.com/leanprover-community/mathlib/pull/7094))
Three lemmas asserting `m • (1 : R) = ↑m`, where `m` is a natural number, an integer or a rational number.
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.60smul_one_eq_coe.60
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_hom.rat.smul_one_eq_coe

Modified src/algebra/module/basic.lean
- \+ *lemma* int.smul_one_eq_coe
- \+ *lemma* nat.smul_one_eq_coe



## [2021-04-11 11:08:53](https://github.com/leanprover-community/mathlib/commit/fbf6219)
feat(analysis/special_functions/exp_log): add `continuity` attribute to `continuous_exp` ([#7157](https://github.com/leanprover-community/mathlib/pull/7157))
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+/\- *lemma* complex.continuous_exp
- \+/\- *lemma* real.continuous_exp
- \+/\- *lemma* real.continuous_log'



## [2021-04-11 10:03:43](https://github.com/leanprover-community/mathlib/commit/1442f70)
feat(measure_theory/interval_integral): variants of integral_comp lemmas ([#7103](https://github.com/leanprover-community/mathlib/pull/7103))
Alternate versions of some of our `integral_comp` lemmas which work even when `c = 0`.
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integral.integral_comp_add_div'
- \+/\- *lemma* interval_integral.integral_comp_add_div
- \+ *lemma* interval_integral.integral_comp_add_mul'
- \+/\- *lemma* interval_integral.integral_comp_add_mul
- \+/\- *lemma* interval_integral.integral_comp_add_right
- \+ *lemma* interval_integral.integral_comp_div'
- \+ *lemma* interval_integral.integral_comp_div_add'
- \+/\- *lemma* interval_integral.integral_comp_div_add
- \+ *lemma* interval_integral.integral_comp_div_sub'
- \+/\- *lemma* interval_integral.integral_comp_div_sub
- \+ *lemma* interval_integral.integral_comp_mul_add'
- \+/\- *lemma* interval_integral.integral_comp_mul_add
- \+ *lemma* interval_integral.integral_comp_mul_left'
- \+ *lemma* interval_integral.integral_comp_mul_right'
- \+ *lemma* interval_integral.integral_comp_mul_sub'
- \+/\- *lemma* interval_integral.integral_comp_mul_sub
- \+ *lemma* interval_integral.integral_comp_sub_div'
- \+/\- *lemma* interval_integral.integral_comp_sub_div
- \+/\- *lemma* interval_integral.integral_comp_sub_left
- \+ *lemma* interval_integral.integral_comp_sub_mul'
- \+/\- *lemma* interval_integral.integral_comp_sub_mul
- \+/\- *lemma* interval_integral.integral_comp_sub_right



## [2021-04-11 05:39:27](https://github.com/leanprover-community/mathlib/commit/fc8e18c)
feat(topology/continuous_function): comp_right_* ([#7145](https://github.com/leanprover-community/mathlib/pull/7145))
We setup variations on `comp_right_* f`, where `f : C(X, Y)`
(that is, precomposition by a continuous map),
as a morphism `C(Y, T) → C(X, T)`, respecting various types of structure.
In particular:
* `comp_right_continuous_map`, the bundled continuous map (for this we need `X Y` compact).
* `comp_right_homeomorph`, when we precompose by a homeomorphism.
* `comp_right_alg_hom`, when `T = R` is a topological ring.
#### Estimated changes
Modified src/topology/continuous_function/basic.lean
- \+ *def* homeomorph.to_continuous_map

Modified src/topology/continuous_function/compact.lean
- \+ *def* continuous_map.comp_right_alg_hom
- \+ *lemma* continuous_map.comp_right_alg_hom_apply
- \+ *lemma* continuous_map.comp_right_alg_hom_continuous
- \+ *def* continuous_map.comp_right_continuous_map
- \+ *lemma* continuous_map.comp_right_continuous_map_apply
- \+ *def* continuous_map.comp_right_homeomorph
- \+ *lemma* continuous_map.dist_lt_of_dist_lt_modulus
- \+ *def* continuous_map.modulus
- \+ *lemma* continuous_map.modulus_pos
- \+ *lemma* continuous_map.norm_coe_le_norm
- \+ *lemma* continuous_map.uniform_continuity



## [2021-04-11 04:38:14](https://github.com/leanprover-community/mathlib/commit/383f591)
chore(scripts): update nolints.txt ([#7154](https://github.com/leanprover-community/mathlib/pull/7154))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-04-11 01:51:24](https://github.com/leanprover-community/mathlib/commit/c6e62cf)
feat(analysis/normed_space/finite_dimension): set of `f : E →L[𝕜] F` of rank `≥n` is open ([#7022](https://github.com/leanprover-community/mathlib/pull/7022))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* antilipschitz_with.add_sub_lipschitz_with

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* is_open_set_of_linear_independent
- \+ *lemma* is_open_set_of_nat_le_rank
- \+ *lemma* linear_map.exists_antilipschitz_with

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_equiv.nnnorm_symm_pos

Modified src/data/finsupp/basic.lean
- \+/\- *def* finsupp.equiv_fun_on_fintype

Modified src/linear_algebra/basic.lean
- \+ *theorem* linear_map.coe_smul_right
- \+/\- *theorem* linear_map.smul_right_apply

Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/linear_independent.lean
- \+ *theorem* fintype.linear_independent_iff'

Modified src/linear_algebra/pi.lean
- \+/\- *def* linear_map.lsum



## [2021-04-10 14:43:35](https://github.com/leanprover-community/mathlib/commit/a83230e)
feat(linear_algebra/eigenspace): define the maximal generalized eigenspace ([#7125](https://github.com/leanprover-community/mathlib/pull/7125))
And prove that it is of the form kernel of `(f - μ • id) ^ k` for some finite `k` for endomorphisms of Noetherian modules.
#### Estimated changes
Modified src/linear_algebra/eigenspace.lean
- \+/\- *lemma* module.End.eigenspace_le_generalized_eigenspace
- \+/\- *def* module.End.generalized_eigenspace
- \- *lemma* module.End.generalized_eigenspace_mono
- \+ *def* module.End.maximal_generalized_eigenspace
- \+ *lemma* module.End.maximal_generalized_eigenspace_eq

Modified src/order/order_iso_nat.lean
- \+ *lemma* well_founded.supr_eq_monotonic_sequence_limit



## [2021-04-10 14:43:34](https://github.com/leanprover-community/mathlib/commit/026150f)
feat(geometry/manifold): a manifold with σ-countable topology has second countable topology ([#6948](https://github.com/leanprover-community/mathlib/pull/6948))
#### Estimated changes
Modified src/geometry/manifold/charted_space.lean
- \+ *lemma* charted_space.second_countable_of_countable_cover
- \+ *lemma* charted_space.second_countable_of_sigma_compact

Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/topology/bases.lean
- \+ *lemma* topological_space.is_topological_basis_of_cover
- \+ *lemma* topological_space.second_countable_topology_of_countable_cover

Modified src/topology/homeomorph.lean


Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.second_countable_topology_source
- \+ *def* local_homeomorph.to_homeomorph_source_target

Modified src/topology/subset_properties.lean
- \+ *lemma* countable_cover_nhds_of_sigma_compact
- \+ *lemma* locally_finite.countable_of_sigma_compact
- \+ *lemma* locally_finite.finite_nonempty_inter_compact



## [2021-04-10 12:50:55](https://github.com/leanprover-community/mathlib/commit/6b3803d)
chore(analysis/normed_space/inner_product): simplify two proofs ([#7149](https://github.com/leanprover-community/mathlib/pull/7149))
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean




## [2021-04-10 12:50:54](https://github.com/leanprover-community/mathlib/commit/363a286)
chore(*): speedup slow proofs ([#7148](https://github.com/leanprover-community/mathlib/pull/7148))
Some proofs using heavy `rfl` or heavy `obviously` can be sped up considerably. Done in this PR for some outstanding examples.
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean


Modified src/algebra/category/Algebra/limits.lean


Modified src/algebra/category/CommRing/limits.lean
- \+ *def* CommRing.is_limit_lifted_cone
- \+ *def* CommRing.lifted_cone
- \+ *def* CommSemiRing.is_limit_lifted_cone
- \+ *def* CommSemiRing.lifted_cone

Modified src/algebra/category/Group/colimits.lean


Modified src/analysis/normed_space/hahn_banach.lean


Modified src/category_theory/monoidal/internal/Module.lean


Modified src/data/mv_polynomial/equiv.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/exterior_algebra.lean


Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/witt_vector/structure_polynomial.lean




## [2021-04-10 08:01:57](https://github.com/leanprover-community/mathlib/commit/7e93367)
feat(analysis/normed_space/banach): a range with closed complement is itself closed ([#6972](https://github.com/leanprover-community/mathlib/pull/6972))
If the range of a continuous linear map has a closed complement, then it is itself closed. For instance, the range can not be a dense hyperplane. We prove it when, additionally, the map has trivial kernel. The general case will follow from this particular case once we have quotients of normed spaces, which are currently only in Lean Liquid.
Along the way, we fill several small gaps in the API of continuous linear maps.
#### Estimated changes
Modified src/analysis/normed_space/banach.lean
- \+ *lemma* continuous_linear_map.closed_complemented_range_of_is_compl_of_ker_eq_bot

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* submodule.ker_subtypeL
- \+ *lemma* submodule.range_subtypeL

Modified src/linear_algebra/prod.lean
- \+ *lemma* linear_map.ker_coprod_of_disjoint_range
- \+ *lemma* linear_map.ker_prod_ker_le_ker_coprod

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.ker_coprod_of_disjoint_range
- \+ *lemma* continuous_linear_map.ker_prod_ker_le_ker_coprod
- \+ *lemma* continuous_linear_map.mem_range_self
- \+ *lemma* continuous_linear_map.range_coprod



## [2021-04-10 06:53:21](https://github.com/leanprover-community/mathlib/commit/d39c3a2)
feat(data/zsqrtd/basic): add some lemmas about norm ([#7114](https://github.com/leanprover-community/mathlib/pull/7114))
#### Estimated changes
Modified src/data/zsqrtd/basic.lean
- \+ *lemma* zsqrtd.is_unit_iff_norm_is_unit
- \+ *lemma* zsqrtd.norm_def
- \+ *lemma* zsqrtd.norm_eq_of_associated
- \+ *lemma* zsqrtd.norm_eq_one_iff'
- \+ *lemma* zsqrtd.norm_eq_zero_iff
- \+ *def* zsqrtd.norm_monoid_hom



## [2021-04-10 06:53:20](https://github.com/leanprover-community/mathlib/commit/7ae2af6)
feat(group_theory/is_free_group): promote `is_free_group.lift'` to an equiv ([#7110](https://github.com/leanprover-community/mathlib/pull/7110))
While non-computable, this makes the API of `is_free_group` align more closely with `free_group`.
Based on discussion in the original PR, this doesn't go as far as changing the definition of `is_free_group` to take the equiv directly.
This additionally:
* adds the definition `lift`, a universe polymorphic version of `lift'`
* adds the lemmas:
  * `lift'_eq_free_group_lift`
  * `lift_eq_free_group_lift`
  * `of_eq_free_group_of`
  * `ext_hom'`
  * `ext_hom`
* renames `is_free_group.iso_free_group_of_is_free_group` to the shorter `is_free_group.to_free_group`
* removes lemmas absent from the `free_group` API that are no longer needed for the proofs here:
  * `end_is_id`
  * `eq_lift`
#### Estimated changes
Modified src/group_theory/free_group.lean


Modified src/group_theory/is_free_group.lean
- \- *lemma* is_free_group.end_is_id
- \- *lemma* is_free_group.eq_lift'
- \+ *lemma* is_free_group.ext_hom'
- \+ *lemma* is_free_group.ext_hom
- \- *def* is_free_group.iso_free_group_of_is_free_group
- \+/\- *def* is_free_group.lift'
- \+ *lemma* is_free_group.lift'_eq_free_group_lift
- \+ *def* is_free_group.lift
- \+ *lemma* is_free_group.lift_eq_free_group_lift
- \+ *lemma* is_free_group.lift_of
- \+ *lemma* is_free_group.of_eq_free_group_of
- \+ *def* is_free_group.to_free_group
- \- *lemma* is_free_group.unique_lift'
- \+ *lemma* is_free_group.unique_lift



## [2021-04-10 03:46:26](https://github.com/leanprover-community/mathlib/commit/575b791)
chore(scripts): update nolints.txt ([#7144](https://github.com/leanprover-community/mathlib/pull/7144))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-04-10 03:46:25](https://github.com/leanprover-community/mathlib/commit/7138d35)
feat(category_theory/action): currying ([#7085](https://github.com/leanprover-community/mathlib/pull/7085))
A functor from an action category can be 'curried' to an ordinary group homomorphism. Also defines transitive group actions.
#### Estimated changes
Modified src/category_theory/action.lean
- \+ *def* category_theory.action_category.End_mul_equiv_subgroup
- \+ *lemma* category_theory.action_category.back_coe
- \+ *lemma* category_theory.action_category.coe_back
- \+ *def* category_theory.action_category.curry
- \+ *lemma* category_theory.action_category.hom_of_pair.val
- \+ *def* category_theory.action_category.hom_of_pair
- \+/\- *def* category_theory.action_category.stabilizer_iso_End
- \+ *def* category_theory.action_category.uncurry

Modified src/category_theory/single_obj.lean
- \+ *lemma* category_theory.single_obj.comp_as_mul
- \+ *lemma* category_theory.single_obj.id_as_one
- \+ *lemma* category_theory.single_obj.inv_as_inv

Modified src/group_theory/group_action/basic.lean
- \+ *lemma* exists_smul_eq
- \+ *lemma* mul_action.stabilizer_quotient

Modified src/group_theory/group_action/group.lean
- \+ *def* arrow_action
- \+ *def* mul_aut_arrow



## [2021-04-10 00:01:44](https://github.com/leanprover-community/mathlib/commit/e269dbc)
feat(tactic/itauto): Complete intuitionistic prover ([#7057](https://github.com/leanprover-community/mathlib/pull/7057))
[As requested on Zulip.](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/tauto.20is.20a.20decision.20procedure.3F/near/233222469)
#### Estimated changes
Modified docs/references.bib


Modified src/tactic/basic.lean


Added src/tactic/itauto.lean
- \+ *def* tactic.itauto.and_kind.cmp
- \+ *def* tactic.itauto.and_kind.sides
- \+ *inductive* tactic.itauto.and_kind
- \+ *inductive* tactic.itauto.proof
- \+ *def* tactic.itauto.prop.and
- \+ *def* tactic.itauto.prop.cmp
- \+ *def* tactic.itauto.prop.eq
- \+ *def* tactic.itauto.prop.iff
- \+ *def* tactic.itauto.prop.not
- \+ *def* tactic.itauto.prop.xor
- \+ *inductive* tactic.itauto.prop

Added test/itauto.lean




## [2021-04-10 00:01:43](https://github.com/leanprover-community/mathlib/commit/8efb93b)
feat(combinatorics/simple_graph/strongly_regular): add definition of strongly regular graph and proof that complete graph is SRG ([#7044](https://github.com/leanprover-community/mathlib/pull/7044))
Add definition of strongly regular graph and proof that complete graphs are strongly regular. Part of [#5698](https://github.com/leanprover-community/mathlib/pull/5698) to prove facts about strongly regular graphs.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean


Added src/combinatorics/simple_graph/strongly_regular.lean
- \+ *lemma* simple_graph.complete_strongly_regular
- \+ *structure* simple_graph.is_SRG_of



## [2021-04-09 22:57:37](https://github.com/leanprover-community/mathlib/commit/309e3b0)
feat(category_theory/subobjects): improvements to API ([#6932](https://github.com/leanprover-community/mathlib/pull/6932))
These additions have been useful while setting up homology.
#### Estimated changes
Modified src/algebra/category/Module/subobject.lean


Modified src/category_theory/subobject/basic.lean
- \+ *def* category_theory.subobject.iso_of_eq
- \+ *def* category_theory.subobject.iso_of_eq_mk
- \+ *def* category_theory.subobject.iso_of_mk_eq
- \+ *def* category_theory.subobject.iso_of_mk_eq_mk
- \+/\- *def* category_theory.subobject.of_le
- \+/\- *lemma* category_theory.subobject.of_le_arrow
- \+ *lemma* category_theory.subobject.of_le_comp_of_le
- \+ *lemma* category_theory.subobject.of_le_comp_of_le_mk
- \+/\- *def* category_theory.subobject.of_le_mk
- \+ *lemma* category_theory.subobject.of_le_mk_comp_of_mk_le
- \+ *lemma* category_theory.subobject.of_le_mk_comp_of_mk_le_mk
- \+ *lemma* category_theory.subobject.of_le_refl
- \+/\- *def* category_theory.subobject.of_mk_le
- \+ *lemma* category_theory.subobject.of_mk_le_comp_of_le
- \+ *lemma* category_theory.subobject.of_mk_le_comp_of_le_mk
- \+/\- *def* category_theory.subobject.of_mk_le_mk
- \+ *lemma* category_theory.subobject.of_mk_le_mk_comp_of_mk_le
- \+ *lemma* category_theory.subobject.of_mk_le_mk_comp_of_mk_le_mk
- \+ *lemma* category_theory.subobject.of_mk_le_mk_refl

Modified src/category_theory/subobject/factor_thru.lean
- \- *lemma* category_theory.limits.image_subobject_factors
- \+ *lemma* category_theory.limits.image_subobject_factors_comp_self
- \+ *lemma* category_theory.limits.image_subobject_iso_comp
- \+ *lemma* category_theory.limits.image_subobject_le_mk
- \+ *def* category_theory.limits.image_subobject_map
- \+ *lemma* category_theory.limits.image_subobject_map_arrow
- \+ *lemma* category_theory.limits.kernel_subobject_comp_mono
- \+ *lemma* category_theory.limits.le_kernel_subobject
- \+ *lemma* category_theory.subobject.factor_thru_comp_arrow
- \+ *lemma* category_theory.subobject.factor_thru_comp_of_le
- \+ *lemma* category_theory.subobject.factor_thru_self
- \+ *lemma* category_theory.subobject.factor_thru_zero
- \+ *lemma* category_theory.subobject.factors_self
- \+ *lemma* category_theory.subobject.factors_zero

Modified src/category_theory/subobject/lattice.lean




## [2021-04-09 18:56:37](https://github.com/leanprover-community/mathlib/commit/763c5c3)
chore(data/list/basic): avoid the axiom of choice ([#7135](https://github.com/leanprover-community/mathlib/pull/7135))
#### Estimated changes
Modified src/data/list/basic.lean




## [2021-04-09 12:24:51](https://github.com/leanprover-community/mathlib/commit/fe5d660)
feat(algebra/category/Module): arbitrary colimits ([#7099](https://github.com/leanprover-community/mathlib/pull/7099))
This is just the "semi-automated" construction of arbitrary colimits in the category or `R`-modules, following the same model as for `Mon`, `AddCommGroup`, etc.
We already have finite colimits from the `abelian` instance. One could also give definitionally nicer colimits as quotients of finitely supported functions. But this is better than nothing!
#### Estimated changes
Added src/algebra/category/Module/colimits.lean
- \+ *def* Module.colimits.cocone_fun
- \+ *def* Module.colimits.cocone_morphism
- \+ *lemma* Module.colimits.cocone_naturality
- \+ *lemma* Module.colimits.cocone_naturality_components
- \+ *def* Module.colimits.colimit
- \+ *def* Module.colimits.colimit_cocone
- \+ *def* Module.colimits.colimit_cocone_is_colimit
- \+ *def* Module.colimits.colimit_setoid
- \+ *def* Module.colimits.colimit_type
- \+ *def* Module.colimits.desc_fun
- \+ *def* Module.colimits.desc_fun_lift
- \+ *def* Module.colimits.desc_morphism
- \+ *inductive* Module.colimits.prequotient
- \+ *lemma* Module.colimits.quot_add
- \+ *lemma* Module.colimits.quot_neg
- \+ *lemma* Module.colimits.quot_smul
- \+ *lemma* Module.colimits.quot_zero
- \+ *inductive* Module.colimits.relation



## [2021-04-09 12:24:50](https://github.com/leanprover-community/mathlib/commit/0ec9cd8)
chore(data/fin): add simp lemmas about 1 and cast_{pred, succ} ([#7067](https://github.com/leanprover-community/mathlib/pull/7067))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.cast_pred_one
- \+ *lemma* fin.cast_succ_one



## [2021-04-09 12:24:49](https://github.com/leanprover-community/mathlib/commit/dd2466c)
chore(data/set_like): Add coe_strict_mono and coe_mono ([#7004](https://github.com/leanprover-community/mathlib/pull/7004))
This adds the following monotonicity lemmas:
* `set_like.coe_mono`, `set_like.coe_strict_mono`
* `submodule.to_add_submonoid_mono`, `submodule.to_add_submonoid_strict_mono`
* `submodule.to_add_subgroup_mono`, `submodule.to_add_subgroup_strict_mono`
* `subsemiring.to_submonoid_mono`, `submodule.to_submonoid_strict_mono`
* `subsemiring.to_add_submonoid_mono`, `submodule.to_add_submonoid_strict_mono`
* `subring.to_subsemiring_mono`, `subring.to_subsemiring_strict_mono`
* `subring.to_add_subgroup_mono`, `subring.to_add_subgroup_strict_mono`
* `subring.to_submonoid_mono`, `subring.to_submonoid_strict_mono`
This also makes `tactic.monotonicity.basic` a lighter-weight import, so that the `@[mono]` attribute is accessible in more places.
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *theorem* submodule.to_add_subgroup_injective
- \+ *lemma* submodule.to_add_subgroup_mono
- \+ *lemma* submodule.to_add_subgroup_strict_mono
- \+ *lemma* submodule.to_add_submonoid_mono
- \+ *lemma* submodule.to_add_submonoid_strict_mono
- \+ *lemma* submodule.to_sub_mul_action_mono
- \+ *lemma* submodule.to_sub_mul_action_strict_mono

Modified src/data/set_like.lean
- \+ *lemma* set_like.coe_mono
- \+ *lemma* set_like.coe_strict_mono

Modified src/ring_theory/subring.lean
- \+ *lemma* subring.to_add_subgroup_injective
- \+ *lemma* subring.to_add_subgroup_mono
- \+ *lemma* subring.to_add_subgroup_strict_mono
- \+ *lemma* subring.to_submonoid_injective
- \+ *lemma* subring.to_submonoid_mono
- \+ *lemma* subring.to_submonoid_strict_mono
- \+ *lemma* subring.to_subsemiring_injective
- \+ *lemma* subring.to_subsemiring_mono
- \+ *lemma* subring.to_subsemiring_strict_mono

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* subsemiring.to_add_submonoid_injective
- \+ *lemma* subsemiring.to_add_submonoid_mono
- \+ *lemma* subsemiring.to_add_submonoid_strict_mono
- \+ *lemma* subsemiring.to_submonoid_injective
- \+ *lemma* subsemiring.to_submonoid_mono
- \+ *lemma* subsemiring.to_submonoid_strict_mono

Modified src/tactic/monotonicity/basic.lean


Modified src/tactic/monotonicity/lemmas.lean




## [2021-04-09 12:24:48](https://github.com/leanprover-community/mathlib/commit/362844d)
feat(category_theory/preadditive): a category induced from a preadditive category is preadditive ([#6883](https://github.com/leanprover-community/mathlib/pull/6883))
#### Estimated changes
Modified src/category_theory/preadditive/additive_functor.lean


Modified src/category_theory/preadditive/default.lean




## [2021-04-09 08:28:56](https://github.com/leanprover-community/mathlib/commit/aa1fa0b)
feat(data/option/basic): option valued choice operator ([#7101](https://github.com/leanprover-community/mathlib/pull/7101))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* option.choice_eq
- \+ *lemma* option.choice_eq_none
- \+ *lemma* option.choice_is_some_iff_nonempty



## [2021-04-09 04:34:52](https://github.com/leanprover-community/mathlib/commit/6610e8f)
feat(data/fintype): golf, move and dualise proof ([#7126](https://github.com/leanprover-community/mathlib/pull/7126))
This PR moves `fintype.exists_max` higher up in the import tree, and golfs it, and adds the dual version, `fintype.exists_min`. The name and statement are unchanged.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.exists_max
- \+ *lemma* fintype.exists_min

Modified src/data/set/finite.lean
- \- *lemma* fintype.exists_max



## [2021-04-09 04:34:51](https://github.com/leanprover-community/mathlib/commit/991dc26)
chore(linear_algebra/multilinear): relax requirements on `multilinear_map.pi_ring_equiv` ([#7117](https://github.com/leanprover-community/mathlib/pull/7117))
#### Estimated changes
Modified src/linear_algebra/multilinear.lean




## [2021-04-09 04:34:50](https://github.com/leanprover-community/mathlib/commit/0b52522)
feat(test/integration): update with new examples ([#7105](https://github.com/leanprover-community/mathlib/pull/7105))
Add examples made possible by [#6787](https://github.com/leanprover-community/mathlib/pull/6787), [#6795](https://github.com/leanprover-community/mathlib/pull/6795), [#7010](https://github.com/leanprover-community/mathlib/pull/7010).
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* interval_integral.integral_comp_neg

Modified test/integration.lean




## [2021-04-09 04:34:49](https://github.com/leanprover-community/mathlib/commit/6dd9a54)
feat(tactic/simps): allow composite projections  ([#7074](https://github.com/leanprover-community/mathlib/pull/7074))
* Allows custom simps-projections that are compositions of multiple projections. This is useful when extending structures without the `old_structure_cmd`.
* Coercions that are compositions of multiple projections are *not* automatically recognized, and should be declared manually (coercions that are definitionally equal to a single projection are still automatically recognized).
* Custom simps projections should now be declared using the name used by `simps`. E.g. `equiv.simps.symm_apply` instead of `equiv.simps.inv_fun`.
* You can disable a projection `proj` being generated by default by `simps` using `initialize_simps_projections (-proj)`
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *def* alg_equiv.simps.inv_fun
- \+ *def* alg_equiv.simps.symm_apply

Modified src/algebra/module/linear_map.lean
- \- *def* linear_equiv.simps.inv_fun
- \+ *def* linear_equiv.simps.symm_apply

Modified src/category_theory/monad/basic.lean
- \+ *def* category_theory.comonad.simps.coe
- \- *def* category_theory.comonad.simps.to_functor
- \- *def* category_theory.comonad.simps.δ'
- \+ *def* category_theory.comonad.simps.δ
- \- *def* category_theory.comonad.simps.ε'
- \+ *def* category_theory.comonad.simps.ε
- \+ *def* category_theory.monad.simps.coe
- \- *def* category_theory.monad.simps.to_functor
- \- *def* category_theory.monad.simps.η'
- \+ *def* category_theory.monad.simps.η
- \- *def* category_theory.monad.simps.μ'
- \+ *def* category_theory.monad.simps.μ

Modified src/data/equiv/basic.lean
- \- *def* equiv.simps.inv_fun
- \+ *def* equiv.simps.symm_apply

Modified src/data/equiv/local_equiv.lean
- \- *def* local_equiv.simps.inv_fun
- \+ *def* local_equiv.simps.symm_apply

Modified src/data/equiv/mul_add.lean
- \- *def* mul_equiv.simps.inv_fun
- \+ *def* mul_equiv.simps.symm_apply

Modified src/data/equiv/ring.lean
- \- *def* ring_equiv.simps.inv_fun
- \+ *def* ring_equiv.simps.symm_apply

Modified src/data/subtype.lean
- \+ *def* subtype.simps.coe
- \- *def* subtype.simps.val

Modified src/order/closure.lean
- \+ *def* closure_operator.simps.apply

Modified src/tactic/simps.lean
- \+ *def* as_fn
- \+ *def* lemmas_only

Modified test/simps.lean
- \+ *def* decorated_equiv.simps.apply
- \+ *def* decorated_equiv.simps.symm_apply
- \+ *def* decorated_equiv.symm
- \+ *structure* decorated_equiv
- \+ *def* fffoo2
- \+ *def* fffoo
- \+ *def* ffoo3
- \+ *def* ffoo4
- \+ *def* ffoo
- \+ *def* foo2
- \+ *def* foo
- \+ *def* further_decorated_equiv.simps.apply
- \+ *def* further_decorated_equiv.simps.symm_apply
- \+ *def* further_decorated_equiv.symm
- \+ *structure* further_decorated_equiv
- \- *def* manual_projection_names.equiv.simps.inv_fun
- \+ *def* manual_projection_names.equiv.simps.symm_apply
- \+ *def* one_more.simps.apply
- \+ *def* one_more.simps.symm_apply
- \+ *def* one_more.symm
- \+ *structure* one_more
- \+/\- *def* very_partially_applied_term



## [2021-04-09 03:28:24](https://github.com/leanprover-community/mathlib/commit/29b834d)
feat(category_theory, algebra/category): AddCommGroup is well-powered ([#7006](https://github.com/leanprover-community/mathlib/pull/7006))
#### Estimated changes
Added src/algebra/category/Group/subobject.lean


Modified src/category_theory/subobject/mono_over.lean
- \+ *def* category_theory.mono_over.congr
- \+ *lemma* category_theory.mono_over.lift_obj_arrow
- \+/\- *def* category_theory.mono_over.map_iso

Modified src/category_theory/subobject/well_powered.lean
- \+ *theorem* category_theory.well_powered_congr
- \+ *theorem* category_theory.well_powered_of_equiv



## [2021-04-09 02:29:48](https://github.com/leanprover-community/mathlib/commit/4e607eb)
chore(scripts): update nolints.txt ([#7129](https://github.com/leanprover-community/mathlib/pull/7129))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-04-09 02:29:47](https://github.com/leanprover-community/mathlib/commit/505ffa9)
feat(analysis/special_functions/integrals): integral of `cos x ^ 2 - sin x ^ 2` ([#7012](https://github.com/leanprover-community/mathlib/pull/7012))
An example of a direct application of integration by parts.
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_cos_sq_sub_sin_sq

Modified test/integration.lean




## [2021-04-08 22:31:17](https://github.com/leanprover-community/mathlib/commit/92ec949)
feat(data/equiv/basic): swap_apply_eq_iff ([#7102](https://github.com/leanprover-community/mathlib/pull/7102))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.swap_apply_eq_iff
- \+ *lemma* equiv.symm_swap



## [2021-04-08 15:56:48](https://github.com/leanprover-community/mathlib/commit/379dd7d)
chore(algebra/ring_quot): Provide `sub` explicitly to `ring_quot` ([#7112](https://github.com/leanprover-community/mathlib/pull/7112))
This means that using `ring_quot.mk (A - B) = ring_quot.mk A - ring_quot.mk B` is true by definition, even if `A - B = A + -B` is not true by definition.
#### Estimated changes
Modified src/algebra/ring_quot.lean
- \+ *theorem* ring_quot.rel.sub_left
- \+ *theorem* ring_quot.rel.sub_right



## [2021-04-08 15:56:47](https://github.com/leanprover-community/mathlib/commit/54ac48a)
chore(data/matrix/basic): add simp lemmas about `minor`, move `reindex` to `matrix.basic` since it knows nothing about linear algebra ([#7083](https://github.com/leanprover-community/mathlib/pull/7083))
#### Estimated changes
Modified src/algebra/lie/classical.lean


Modified src/algebra/lie/matrix.lean
- \+ *lemma* matrix.reindex_lie_equiv_symm
- \- *lemma* matrix.reindex_lie_equiv_symm_apply

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.minor_add
- \+ *lemma* matrix.minor_apply
- \+ *lemma* matrix.minor_id_id
- \+ *lemma* matrix.minor_minor
- \+ *lemma* matrix.minor_neg
- \+ *lemma* matrix.minor_smul
- \+ *lemma* matrix.minor_sub
- \+ *lemma* matrix.minor_zero
- \+ *def* matrix.reindex
- \+ *lemma* matrix.reindex_apply
- \+ *lemma* matrix.reindex_refl_refl
- \+ *lemma* matrix.reindex_symm
- \+ *lemma* matrix.reindex_trans
- \+ *lemma* matrix.transpose_minor
- \+ *lemma* matrix.transpose_reindex

Modified src/linear_algebra/determinant.lean
- \+ *lemma* matrix.det_minor_equiv_self
- \+ *lemma* matrix.det_reindex_self

Modified src/linear_algebra/matrix.lean
- \- *lemma* matrix.coe_reindex_alg_equiv
- \- *lemma* matrix.coe_reindex_alg_equiv_symm
- \- *lemma* matrix.coe_reindex_linear_equiv
- \- *lemma* matrix.coe_reindex_linear_equiv_symm
- \- *lemma* matrix.det_reindex_self'
- \- *lemma* matrix.det_reindex_self
- \- *def* matrix.reindex
- \+/\- *lemma* matrix.reindex_alg_equiv_refl
- \+ *lemma* matrix.reindex_alg_equiv_symm
- \- *lemma* matrix.reindex_alg_equiv_symm_apply
- \- *lemma* matrix.reindex_apply
- \+/\- *lemma* matrix.reindex_linear_equiv_apply
- \+/\- *lemma* matrix.reindex_linear_equiv_refl_refl
- \+ *lemma* matrix.reindex_linear_equiv_symm
- \- *lemma* matrix.reindex_linear_equiv_symm_apply
- \- *lemma* matrix.reindex_refl_refl
- \- *lemma* matrix.reindex_symm_apply
- \- *lemma* matrix.reindex_transpose



## [2021-04-08 15:56:46](https://github.com/leanprover-community/mathlib/commit/fb74f98)
chore(data/set/finite): set.finite.sup ([#7080](https://github.com/leanprover-community/mathlib/pull/7080))
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *theorem* set.finite.inf_of_left
- \+ *theorem* set.finite.inf_of_right
- \+ *lemma* set.finite.sup



## [2021-04-08 15:56:45](https://github.com/leanprover-community/mathlib/commit/bcf5b1a)
feat(data/fintype/basic): to_finset lattice lemmas ([#7077](https://github.com/leanprover-community/mathlib/pull/7077))
While we do not have lattice homomorphisms, we can still provide some similar API.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *theorem* set.to_finset_disjoint_iff
- \+ *theorem* set.to_finset_mono
- \+ *theorem* set.to_finset_strict_mono

Modified src/data/set/finite.lean
- \+ *lemma* set.finite.diff
- \+ *lemma* set.finite.to_finset_inj
- \+ *lemma* set.finite.to_finset_mono
- \+ *lemma* set.finite.to_finset_strict_mono
- \+ *lemma* set.finite.union_iff
- \+ *lemma* set.finite_to_finset_eq_empty_iff
- \+ *lemma* set.insert_to_finset



## [2021-04-08 15:56:44](https://github.com/leanprover-community/mathlib/commit/56e5248)
feat(order/order_iso_nat): add another flavour of well-foundedness for partial orders ([#5434](https://github.com/leanprover-community/mathlib/pull/5434))
#### Estimated changes
Modified src/order/order_iso_nat.lean
- \+ *lemma* well_founded.monotone_chain_condition

Modified src/order/preorder_hom.lean
- \+ *lemma* rel_embedding.to_preorder_hom_injective
- \+ *def* rel_hom.to_preorder_hom
- \+ *lemma* rel_hom.to_preorder_hom_coe_fn



## [2021-04-08 14:49:49](https://github.com/leanprover-community/mathlib/commit/f474756)
chore(category_theory/abelian): enable instances ([#7106](https://github.com/leanprover-community/mathlib/pull/7106))
This PR is extracted from Markus' `projective` branch. It just turns on, as global instances, various instances provided by an `abelian` category. In the past these weren't instances, because `has_limit` carried data which could conflict.
#### Estimated changes
Modified src/category_theory/abelian/basic.lean
- \- *lemma* category_theory.abelian.has_finite_biproducts
- \- *lemma* category_theory.abelian.has_pullbacks
- \- *lemma* category_theory.abelian.has_pushouts

Modified src/category_theory/abelian/pseudoelements.lean




## [2021-04-08 06:49:07](https://github.com/leanprover-community/mathlib/commit/8e7028c)
feat(topology/unit_interval): abstract out material about [0,1] ([#7056](https://github.com/leanprover-community/mathlib/pull/7056))
Separates out some material about `[0,1]` from `topology/path_connected.lean`, and adds a very simple tactic.
#### Estimated changes
Modified src/topology/path_connected.lean
- \- *def* I_symm
- \- *lemma* I_symm_one
- \- *lemma* I_symm_zero
- \- *lemma* Icc_zero_one_symm
- \- *lemma* coe_I_one
- \- *lemma* coe_I_zero
- \- *lemma* continuous_I_symm

Added src/topology/unit_interval.lean
- \+ *lemma* unit_interval.coe_one
- \+ *lemma* unit_interval.coe_zero
- \+ *lemma* unit_interval.continuous_symm
- \+ *lemma* unit_interval.le_one
- \+ *lemma* unit_interval.mem_iff_one_sub_mem
- \+ *lemma* unit_interval.nonneg
- \+ *lemma* unit_interval.one_minus_le_one
- \+ *lemma* unit_interval.one_minus_nonneg
- \+ *def* unit_interval.symm
- \+ *lemma* unit_interval.symm_one
- \+ *lemma* unit_interval.symm_zero
- \+ *abbreviation* unit_interval



## [2021-04-08 06:49:06](https://github.com/leanprover-community/mathlib/commit/c6b0636)
feat(archive/imo): formalize IMO 2008 Q3 ([#7025](https://github.com/leanprover-community/mathlib/pull/7025))
#### Estimated changes
Added archive/imo/imo2008_q3.lean
- \+ *theorem* imo2008_q3
- \+ *lemma* p_lemma



## [2021-04-08 06:49:05](https://github.com/leanprover-community/mathlib/commit/9c2a3e7)
refactor(analysis/normed_space/add_torsor): generalize to semi_normed_space ([#7016](https://github.com/leanprover-community/mathlib/pull/7016))
This part of a series of PR to include the theory of `semi_normed_space` in mathlib.
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean
- \+/\- *lemma* affine_map.continuous_linear_iff
- \+/\- *def* affine_map.of_map_midpoint
- \+/\- *lemma* isometric.dist_point_reflection_self
- \+/\- *lemma* isometric.point_reflection_fixed_iff
- \+/\- *lemma* lipschitz_with.vadd
- \+/\- *lemma* lipschitz_with.vsub
- \+ *def* pseudo_metric_space_of_normed_group_of_add_torsor



## [2021-04-08 06:49:04](https://github.com/leanprover-community/mathlib/commit/c5ea4cd)
feat(group_theory/perm): define the permutation `(0 1 ... (i : fin n))` ([#6815](https://github.com/leanprover-community/mathlib/pull/6815))
I tried a number of definitions and it looks like this is the least awkward one to prove with. In any case, using the API should allow you to avoid unfolding the definition.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.of_left_inverse'_eq_of_injective
- \+/\- *lemma* equiv.of_left_inverse_eq_of_injective
- \+ *lemma* function.injective.map_swap

Modified src/data/equiv/fin.lean
- \+ *lemma* coe_fin_rotate
- \+ *lemma* coe_fin_rotate_of_ne_last
- \+/\- *def* fin_rotate
- \+ *lemma* fin_rotate_apply_zero
- \+/\- *lemma* fin_rotate_last'
- \+/\- *lemma* fin_rotate_last
- \+/\- *lemma* fin_rotate_of_lt
- \+ *lemma* fin_rotate_one
- \+ *lemma* fin_rotate_succ_apply
- \+ *lemma* fin_rotate_zero

Modified src/data/fin.lean
- \+ *lemma* fin.cast_le_zero
- \+ *lemma* fin.coe_add_one
- \+ *lemma* fin.coe_add_one_of_lt
- \+ *lemma* fin.coe_of_injective_cast_le_symm
- \+ *lemma* fin.coe_of_injective_cast_succ_symm
- \+ *lemma* fin.last_add_one
- \+ *lemma* fin.range_cast_le
- \+ *lemma* fin.range_cast_succ
- \+ *lemma* fin.succ_eq_last_succ

Modified src/group_theory/perm/fin.lean
- \+ *lemma* fin.coe_cycle_range_of_le
- \+ *lemma* fin.coe_cycle_range_of_lt
- \+ *def* fin.cycle_range
- \+ *lemma* fin.cycle_range_apply
- \+ *lemma* fin.cycle_range_last
- \+ *lemma* fin.cycle_range_of_eq
- \+ *lemma* fin.cycle_range_of_gt
- \+ *lemma* fin.cycle_range_of_le
- \+ *lemma* fin.cycle_range_of_lt
- \+ *lemma* fin.cycle_range_self
- \+ *lemma* fin.cycle_range_zero'
- \+ *lemma* fin.cycle_range_zero
- \+ *lemma* fin.sign_cycle_range
- \+ *lemma* fin_rotate_succ
- \+ *lemma* sign_fin_rotate



## [2021-04-08 05:45:01](https://github.com/leanprover-community/mathlib/commit/def9671)
feat(group_theory/is_free_group): the property of being a free group ([#7086](https://github.com/leanprover-community/mathlib/pull/7086))
#### Estimated changes
Added src/group_theory/is_free_group.lean
- \+ *lemma* is_free_group.end_is_id
- \+ *lemma* is_free_group.eq_lift'
- \+ *def* is_free_group.iso_free_group_of_is_free_group
- \+ *def* is_free_group.lift'
- \+ *lemma* is_free_group.lift'_of
- \+ *def* is_free_group.of_mul_equiv
- \+ *lemma* is_free_group.unique_lift'



## [2021-04-08 03:58:52](https://github.com/leanprover-community/mathlib/commit/e8b217b)
chore(scripts): update nolints.txt ([#7098](https://github.com/leanprover-community/mathlib/pull/7098))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-04-08 03:58:51](https://github.com/leanprover-community/mathlib/commit/b9d9bf0)
fix(.github/PULL_REQUEST_TEMPLATE.md): Fix the gitpod button link, looks like it moved with an update ([#7096](https://github.com/leanprover-community/mathlib/pull/7096))
I'll hold off for a couple of days on this as I'm not sure if the breakage was intentional or temporary on the gitpod side.
#### Estimated changes
Modified .github/PULL_REQUEST_TEMPLATE.md




## [2021-04-08 00:15:24](https://github.com/leanprover-community/mathlib/commit/99c7d22)
chore(*): fixup docs that don't parse/cause linting errors ([#7088](https://github.com/leanprover-community/mathlib/pull/7088))
A couple docs had errors in the way that they were written, leading to them not displaying properly, or causing linting errors. This aims to make the [style_exceptions.txt](https://github.com/leanprover-community/mathlib/blob/master/scripts/style-exceptions.txt) file smaller, and also make the webdocs display them properly, c.f. [here](https://leanprover-community.github.io/mathlib_docs/topology/metric_space/basic.html).
#### Estimated changes
Modified src/data/erased.lean


Modified src/data/list/palindrome.lean


Modified src/data/matrix/pequiv.lean


Modified src/data/nat/modeq.lean


Modified src/data/qpf/multivariate/basic.lean


Modified src/data/qpf/multivariate/constructions/fix.lean


Modified src/data/sym2.lean


Modified src/geometry/euclidean/basic.lean


Modified src/geometry/euclidean/circumcenter.lean


Modified src/geometry/euclidean/monge_point.lean


Modified src/geometry/euclidean/triangle.lean


Modified src/order/basic.lean


Modified src/set_theory/game/impartial.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean


Modified src/topology/metric_space/basic.lean




## [2021-04-07 22:32:23](https://github.com/leanprover-community/mathlib/commit/c356c1f)
chore(ring_theory/tensor_product): golf proofs ([#7089](https://github.com/leanprover-community/mathlib/pull/7089))
Cherry-picked from [#4773](https://github.com/leanprover-community/mathlib/pull/4773), entirely written by @jcommelin
#### Estimated changes
Modified src/ring_theory/tensor_product.lean




## [2021-04-07 22:32:22](https://github.com/leanprover-community/mathlib/commit/f4214de)
feat(measure_theory/group, measure_theory/bochner_integration): left translate of an integral ([#6936](https://github.com/leanprover-community/mathlib/pull/6936))
Translating a function on a topological group by left- (right-) multiplication by a constant does not change its integral with respect to a left- (right-) invariant measure.
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.integral_mul_left_eq_self
- \+ *lemma* measure_theory.integral_mul_right_eq_self
- \+ *lemma* measure_theory.integral_zero_of_mul_left_eq_neg
- \+ *lemma* measure_theory.integral_zero_of_mul_right_eq_neg

Modified src/measure_theory/group.lean
- \+ *lemma* measure_theory.lintegral_mul_left_eq_self
- \+ *lemma* measure_theory.lintegral_mul_right_eq_self

Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.lintegral_map_equiv
- \+ *lemma* measure_theory.simple_func.lintegral_map_equiv



## [2021-04-07 19:05:13](https://github.com/leanprover-community/mathlib/commit/68bd325)
feat(topology/category/Profinite): Profinite_to_Top creates limits. ([#7070](https://github.com/leanprover-community/mathlib/pull/7070))
This PR adds a proof that `Profinite` has limits by showing that the forgetful functor to `Top` creates limits.
#### Estimated changes
Modified src/topology/category/CompHaus.lean
- \+/\- *def* CompHaus_to_Top

Modified src/topology/category/Profinite.lean




## [2021-04-07 19:05:12](https://github.com/leanprover-community/mathlib/commit/08aff2c)
feat(algebra/big_operators/basic): edit `finset.sum/prod_range_succ` ([#6676](https://github.com/leanprover-community/mathlib/pull/6676))
- Change the RHS of the statement of `sum_range_succ` from `f n + ∑ x in range n, f x` to `∑ x in range n, f x + f n`
-  Change the RHS of the statement of `prod_range_succ` from `f n * ∑ x in range n, f x` to `∑ x in range n, f x * f n`
The old versions of those lemmas are now called `sum_range_succ_comm` and `prod_range_succ_comm`, respectively.
See [this conversation](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/break.20off.20last.20term.20of.20summation/near/229634503) on Zulip.
#### Estimated changes
Modified archive/imo/imo2013_q1.lean


Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.prod_range_add
- \+ *lemma* finset.prod_range_succ_comm
- \+ *lemma* finset.sum_range_succ_comm

Modified src/algebra/char_p/basic.lean


Modified src/algebra/geom_sum.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/p_series.lean


Modified src/analysis/special_functions/integrals.lean


Modified src/analysis/special_functions/polynomials.lean


Modified src/analysis/specific_limits.lean


Modified src/data/complex/exponential.lean


Modified src/data/nat/choose/sum.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/polynomial/iterated_deriv.lean


Modified src/data/polynomial/monic.lean


Modified src/linear_algebra/matrix.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/bernoulli_polynomials.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean




## [2021-04-07 15:23:49](https://github.com/leanprover-community/mathlib/commit/d76b649)
feat(dynamics/fixed_points/basic): fixed_points_id simp lemma ([#7078](https://github.com/leanprover-community/mathlib/pull/7078))
#### Estimated changes
Modified src/dynamics/fixed_points/basic.lean
- \+ *lemma* function.fixed_points_id



## [2021-04-07 15:23:48](https://github.com/leanprover-community/mathlib/commit/4a37c28)
feat(data/fintype/basic): set.to_finset_eq_empty_iff ([#7075](https://github.com/leanprover-community/mathlib/pull/7075))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* set.to_finset_eq_empty_iff



## [2021-04-07 15:23:46](https://github.com/leanprover-community/mathlib/commit/c3c7c34)
feat(data/matrix/basic): dependently-typed block diagonal ([#7068](https://github.com/leanprover-community/mathlib/pull/7068))
This allows constructing block diagonal matrices whose blocks are different sizes. A notable example of such a matrix is the one from the Jordan Normal Form.
This duplicates all of the API for `block_diagonal` from this file. Most of the proofs copy across cleanly, but the proof for `block_diagonal_mul'` required lots of hand-holding that `simp` could solve by itself for the non-dependent case.
#### Estimated changes
Modified src/data/matrix/basic.lean
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
- \+/\- *lemma* matrix.block_diagonal_mul



## [2021-04-07 15:23:45](https://github.com/leanprover-community/mathlib/commit/8459d0a)
feat(continuous_function/compact): lemmas characterising norm and dist ([#7054](https://github.com/leanprover-community/mathlib/pull/7054))
Transport lemmas charactering the norm and distance on bounded continuous functions, to continuous maps with compact domain.
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.dist_le_iff_of_nonempty
- \- *lemma* bounded_continuous_function.dist_le_of_nonempty

Modified src/topology/continuous_function/compact.lean
- \+ *lemma* continuous_map.dist_le
- \+ *lemma* continuous_map.dist_le_iff_of_nonempty
- \+ *lemma* continuous_map.dist_le_two_norm
- \+ *lemma* continuous_map.dist_lt_iff
- \+ *lemma* continuous_map.dist_lt_iff_of_nonempty
- \+ *lemma* continuous_map.dist_lt_of_nonempty
- \+ *lemma* continuous_map.norm_le
- \+ *lemma* continuous_map.norm_le_of_nonempty
- \+ *lemma* continuous_map.norm_lt_iff
- \+ *lemma* continuous_map.norm_lt_iff_of_nonempty



## [2021-04-07 15:23:44](https://github.com/leanprover-community/mathlib/commit/919b4e3)
feat(algebra/category/Module): free module functor is lax monoidal ([#6906](https://github.com/leanprover-community/mathlib/pull/6906))
#### Estimated changes
Modified src/algebra/category/Module/adjunctions.lean




## [2021-04-07 15:23:43](https://github.com/leanprover-community/mathlib/commit/893173d)
feat(category/subobject): complete_lattice instance ([#6809](https://github.com/leanprover-community/mathlib/pull/6809))
#### Estimated changes
Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \+ *def* category_theory.limits.wide_pullback_shape.mk_cone
- \+ *def* category_theory.limits.wide_pushout_shape.mk_cocone

Modified src/category_theory/subobject/basic.lean
- \+ *lemma* category_theory.subobject.arrow_congr

Modified src/category_theory/subobject/lattice.lean
- \+ *def* category_theory.subobject.Inf
- \+ *lemma* category_theory.subobject.Inf_le
- \+ *def* category_theory.subobject.Sup
- \+ *lemma* category_theory.subobject.Sup_le
- \+ *lemma* category_theory.subobject.le_Inf
- \+ *def* category_theory.subobject.le_Inf_cone
- \+ *lemma* category_theory.subobject.le_Inf_cone_π_app_none
- \+ *lemma* category_theory.subobject.le_Sup
- \+ *def* category_theory.subobject.small_coproduct_desc
- \+ *lemma* category_theory.subobject.symm_apply_mem_iff_mem_image
- \+ *def* category_theory.subobject.wide_cospan
- \+ *lemma* category_theory.subobject.wide_cospan_map_term
- \+ *def* category_theory.subobject.wide_pullback
- \+ *def* category_theory.subobject.wide_pullback_ι

Modified src/category_theory/subobject/mono_over.lean
- \+/\- *abbreviation* category_theory.mono_over.arrow
- \+ *lemma* category_theory.mono_over.mk'_coe'

Modified src/measure_theory/measure_space.lean




## [2021-04-07 10:30:59](https://github.com/leanprover-community/mathlib/commit/9157b57)
refactor(topology/algebra/normed_group): generalize to semi_normed_group ([#7066](https://github.com/leanprover-community/mathlib/pull/7066))
The completion of a `semi_normed_group` is a `normed_group` (and similarly for `pseudo_metric_space`).
#### Estimated changes
Modified src/topology/algebra/normed_group.lean
- \+/\- *lemma* uniform_space.completion.norm_coe

Modified src/topology/metric_space/completion.lean




## [2021-04-07 10:30:58](https://github.com/leanprover-community/mathlib/commit/d89bfc4)
feat(field_theory/minpoly): remove `is_integral` requirement from `unique'` ([#7064](https://github.com/leanprover-community/mathlib/pull/7064))
`unique'` had an extraneous requirement on `is_integral`, which could be inferred from the other arguments.
This is a small step towards [#5258](https://github.com/leanprover-community/mathlib/pull/5258), but is a breaking change; `unique'` now needs one less argument, which will break all current code using `unique'`.
#### Estimated changes
Modified src/field_theory/abel_ruffini.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/minpoly.lean
- \+/\- *theorem* minpoly.unique'



## [2021-04-07 10:30:56](https://github.com/leanprover-community/mathlib/commit/36649f8)
chore(linear_algebra/basic): add linear_map.one_eq_id ([#7063](https://github.com/leanprover-community/mathlib/pull/7063))
Cherry-picked from [#4773](https://github.com/leanprover-community/mathlib/pull/4773)
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.one_eq_id



## [2021-04-07 10:30:55](https://github.com/leanprover-community/mathlib/commit/104fb22)
chore(logic/basic): generalize eq_iff_true_of_subsingleton to Sort ([#7061](https://github.com/leanprover-community/mathlib/pull/7061))
#### Estimated changes
Modified src/logic/basic.lean
- \+/\- *lemma* eq_iff_true_of_subsingleton



## [2021-04-07 10:30:54](https://github.com/leanprover-community/mathlib/commit/b8414e7)
feat(logic/function/basic): add injectivity/surjectivity of functions from/to subsingletons ([#7060](https://github.com/leanprover-community/mathlib/pull/7060))
In the surjective lemma (`function.surjective.to_subsingleton`), ~~I had to assume `Type*`, instead of `Sort*`, since I was not able to make the proof work in the more general case.~~ [Edit: Eric fixed the proof so that now they work in full generality.] 🎉
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/lemmas.20on.20int.20and.20subsingleton
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *lemma* function.injective_of_subsingleton
- \+ *lemma* function.surjective_to_subsingleton



## [2021-04-07 10:30:53](https://github.com/leanprover-community/mathlib/commit/df8ef37)
feat(data/int/basic algebra/associated): is_unit (a : ℤ) iff a = ±1 ([#7058](https://github.com/leanprover-community/mathlib/pull/7058))
Besides the title lemma, this PR also moves lemma `is_unit_int` from `algebra/associated` to `data/int/basic`.
#### Estimated changes
Modified src/algebra/associated.lean
- \- *theorem* is_unit_int

Modified src/algebra/ring/basic.lean
- \+ *lemma* is_unit.neg

Modified src/data/int/basic.lean
- \+ *lemma* int.is_unit_eq_one_or
- \+ *lemma* int.is_unit_iff
- \+ *theorem* int.is_unit_iff_nat_abs_eq
- \+ *lemma* int.nat_abs_eq_iff

Modified src/ring_theory/int/basic.lean




## [2021-04-07 10:30:52](https://github.com/leanprover-community/mathlib/commit/a6024f1)
feat(archive/imo): formalize IMO 2008 Q4 ([#7039](https://github.com/leanprover-community/mathlib/pull/7039))
feat(archive/imo): formalize IMO 2008 Q4
#### Estimated changes
Added archive/imo/imo2008_q4.lean
- \+ *lemma* abs_eq_one_of_pow_eq_one
- \+ *theorem* imo2008_q4



## [2021-04-07 10:30:50](https://github.com/leanprover-community/mathlib/commit/7e71849)
feat(to_additive): copy _refl_lemma attribute ([#7011](https://github.com/leanprover-community/mathlib/pull/7011))
also warn user if if `simps` and `to_additive` are provided out of order.
#### Estimated changes
Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/category/Semigroup/basic.lean


Modified src/algebra/group/pi.lean


Modified src/algebra/group/to_additive.lean


Modified src/data/equiv/mul_add.lean


Modified src/topology/continuous_function/algebra.lean


Modified test/simps.lean
- \+ *def* monoid_hom.my_comp



## [2021-04-07 10:30:49](https://github.com/leanprover-community/mathlib/commit/c488997)
feat(analysis/special_functions/polynomial): polynomials are big O of polynomials of higher degree ([#6714](https://github.com/leanprover-community/mathlib/pull/6714))
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *theorem* asymptotics.div_is_bounded_under_of_is_O
- \+ *theorem* asymptotics.is_O_iff_div_is_bounded_under
- \+ *theorem* asymptotics.is_O_of_div_tendsto_nhds

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* is_bounded_under_of_tendsto
- \+ *lemma* norm_le_norm_add_const_of_dist_le
- \+ *lemma* norm_lt_norm_add_const_of_dist_lt

Modified src/analysis/special_functions/polynomials.lean
- \+ *lemma* polynomial.eventually_no_roots
- \+ *theorem* polynomial.is_O_of_degree_le

Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.ne_zero_of_degree_ge_degree

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.exists_max_root
- \+ *lemma* polynomial.exists_min_root

Modified src/data/set/finite.lean
- \+ *theorem* set.exists_lower_bound_image
- \+ *theorem* set.exists_upper_bound_image



## [2021-04-07 06:34:06](https://github.com/leanprover-community/mathlib/commit/05c491c)
feat(big_operators): single out one term from prod ([#7040](https://github.com/leanprover-community/mathlib/pull/7040))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \- *lemma* finset.mul_prod_diff_singleton
- \+ *lemma* finset.prod_eq_mul_prod_diff_singleton
- \+ *lemma* finset.prod_eq_prod_diff_singleton_mul
- \+/\- *lemma* finset.prod_insert
- \+ *lemma* fintype.prod_eq_mul_prod_compl
- \+ *lemma* fintype.prod_eq_prod_compl_mul

Modified src/algebra/big_operators/order.lean


Modified src/number_theory/bernoulli.lean




## [2021-04-07 06:34:05](https://github.com/leanprover-community/mathlib/commit/ec6f5d1)
feat(data/*set): some finite sets lemmas ([#7037](https://github.com/leanprover-community/mathlib/pull/7037))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.exists_mem_subset_of_subset_bUnion_of_directed_on

Modified src/data/set/finite.lean
- \+ *lemma* set.finite.fin_embedding
- \+ *lemma* set.finite.fin_param

Modified src/logic/embedding.lean
- \+ *def* equiv.as_embedding
- \+ *lemma* equiv.as_embedding_range



## [2021-04-07 06:34:04](https://github.com/leanprover-community/mathlib/commit/6048b6f)
feat(tactic/monotonicity): Allow `@[mono]` on `strict_mono` lemmas ([#7017](https://github.com/leanprover-community/mathlib/pull/7017))
A follow-up to [#3310](https://github.com/leanprover-community/mathlib/pull/3310)
#### Estimated changes
Modified src/tactic/monotonicity/basic.lean


Modified src/tactic/monotonicity/interactive.lean


Modified test/monotonicity/test_cases.lean
- \+ *def* my_id
- \- *lemma* test
- \+ *lemma* test_monotone
- \+ *lemma* test_strict_mono



## [2021-04-07 06:34:02](https://github.com/leanprover-community/mathlib/commit/21a96ef)
feat(ring_theory/hahn_series): summable families of Hahn series ([#6997](https://github.com/leanprover-community/mathlib/pull/6997))
Defines `hahn_series.summable_family`
Defines the formal sum `hahn_series.summable_family.hsum` and its linear map version, `hahn_series.summable_family.lsum`
#### Estimated changes
Modified src/ring_theory/hahn_series.lean
- \+ *lemma* hahn_series.summable_family.add_apply
- \+ *lemma* hahn_series.summable_family.co_support_add_subset
- \+ *lemma* hahn_series.summable_family.coe_add
- \+ *lemma* hahn_series.summable_family.coe_injective
- \+ *lemma* hahn_series.summable_family.coe_neg
- \+ *lemma* hahn_series.summable_family.coe_sub
- \+ *lemma* hahn_series.summable_family.coe_zero
- \+ *lemma* hahn_series.summable_family.ext
- \+ *def* hahn_series.summable_family.hsum
- \+ *lemma* hahn_series.summable_family.hsum_add
- \+ *lemma* hahn_series.summable_family.hsum_coeff
- \+ *lemma* hahn_series.summable_family.hsum_smul
- \+ *lemma* hahn_series.summable_family.is_wf_Union_support
- \+ *def* hahn_series.summable_family.lsum
- \+ *lemma* hahn_series.summable_family.lsum_apply
- \+ *lemma* hahn_series.summable_family.mem_co_support
- \+ *lemma* hahn_series.summable_family.neg_apply
- \+ *lemma* hahn_series.summable_family.smul_apply
- \+ *lemma* hahn_series.summable_family.sub_apply
- \+ *lemma* hahn_series.summable_family.support_hsum_subset
- \+ *lemma* hahn_series.summable_family.zero_apply
- \+ *structure* hahn_series.summable_family



## [2021-04-07 06:34:01](https://github.com/leanprover-community/mathlib/commit/6161a1f)
feat(category_theory/types): add explicit pullbacks in `Type u` ([#6973](https://github.com/leanprover-community/mathlib/pull/6973))
Add an explicit construction of binary pullbacks in the
category of types.
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/pullbacks.20in.20Type.20u
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *def* category_theory.limits.pullback_cone.is_limit_aux
- \+/\- *abbreviation* category_theory.limits.walking_cospan.hom.id
- \+/\- *abbreviation* category_theory.limits.walking_cospan.hom.inl
- \+/\- *abbreviation* category_theory.limits.walking_cospan.hom.inr
- \+/\- *abbreviation* category_theory.limits.walking_cospan.left
- \+/\- *abbreviation* category_theory.limits.walking_cospan.one
- \+/\- *abbreviation* category_theory.limits.walking_cospan.right
- \+/\- *abbreviation* category_theory.limits.walking_span.hom.fst
- \+/\- *abbreviation* category_theory.limits.walking_span.hom.id
- \+/\- *abbreviation* category_theory.limits.walking_span.hom.snd
- \+/\- *abbreviation* category_theory.limits.walking_span.left
- \+/\- *abbreviation* category_theory.limits.walking_span.right
- \+/\- *abbreviation* category_theory.limits.walking_span.zero

Modified src/category_theory/limits/shapes/types.lean
- \+ *abbreviation* category_theory.limits.types.pullback_cone
- \+ *lemma* category_theory.limits.types.pullback_iso_pullback_hom_fst
- \+ *lemma* category_theory.limits.types.pullback_iso_pullback_hom_snd
- \+ *lemma* category_theory.limits.types.pullback_iso_pullback_inv_fst
- \+ *lemma* category_theory.limits.types.pullback_iso_pullback_inv_snd
- \+ *def* category_theory.limits.types.pullback_limit_cone
- \+ *abbreviation* category_theory.limits.types.pullback_obj



## [2021-04-07 02:18:23](https://github.com/leanprover-community/mathlib/commit/77e90da)
chore(scripts): update nolints.txt ([#7072](https://github.com/leanprover-community/mathlib/pull/7072))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-04-07 02:18:22](https://github.com/leanprover-community/mathlib/commit/d904c8d)
chore(algebra/ring/prod): add missing `prod.distrib` instance ([#7069](https://github.com/leanprover-community/mathlib/pull/7069))
#### Estimated changes
Modified src/algebra/ring/prod.lean




## [2021-04-07 02:18:21](https://github.com/leanprover-community/mathlib/commit/8b33d74)
chore(group_theory/specific_groups/*): new folder specific_groups ([#7018](https://github.com/leanprover-community/mathlib/pull/7018))
This creates a new folder `specific_groups` analogous to `analysis.special_functions`. So far, I have put `cyclic` (split from `order_of_element`), `dihedral`, and `quaternion` there.
Related Zulip discussion: 
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/group_theory.2Especific_groups
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \- *lemma* card_order_of_eq_totient_aux₂
- \- *lemma* card_pow_eq_one_eq_order_of_aux
- \- *theorem* comm_group.is_simple_iff_is_cyclic_and_prime_card
- \- *lemma* is_cyclic.card_order_of_eq_totient
- \- *lemma* is_cyclic.card_pow_eq_one_le
- \- *def* is_cyclic.comm_group
- \- *lemma* is_cyclic.exists_monoid_generator
- \- *lemma* is_cyclic.image_range_card
- \- *lemma* is_cyclic.image_range_order_of
- \- *lemma* is_cyclic_of_card_pow_eq_one_le
- \- *lemma* is_cyclic_of_order_of_eq_card
- \- *lemma* is_cyclic_of_prime_card
- \- *theorem* is_simple_group.prime_card
- \- *lemma* is_simple_group_of_prime_card
- \- *lemma* monoid_hom.map_cyclic
- \- *lemma* order_of_eq_card_of_forall_mem_gpowers

Added src/group_theory/specific_groups/cyclic.lean
- \+ *lemma* card_order_of_eq_totient_aux₂
- \+ *lemma* card_pow_eq_one_eq_order_of_aux
- \+ *theorem* comm_group.is_simple_iff_is_cyclic_and_prime_card
- \+ *lemma* is_cyclic.card_order_of_eq_totient
- \+ *lemma* is_cyclic.card_pow_eq_one_le
- \+ *def* is_cyclic.comm_group
- \+ *lemma* is_cyclic.exists_monoid_generator
- \+ *lemma* is_cyclic.image_range_card
- \+ *lemma* is_cyclic.image_range_order_of
- \+ *lemma* is_cyclic_of_card_pow_eq_one_le
- \+ *lemma* is_cyclic_of_order_of_eq_card
- \+ *lemma* is_cyclic_of_prime_card
- \+ *theorem* is_simple_group.prime_card
- \+ *lemma* is_simple_group_of_prime_card
- \+ *lemma* monoid_hom.map_cyclic
- \+ *lemma* order_of_eq_card_of_forall_mem_gpowers

Renamed src/group_theory/dihedral_group.lean to src/group_theory/specific_groups/dihedral.lean


Renamed src/group_theory/quaternion_group.lean to src/group_theory/specific_groups/quaternion.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/roots_of_unity.lean




## [2021-04-07 02:18:20](https://github.com/leanprover-community/mathlib/commit/758d322)
feat(measure_theory/interval_integral): make integral_comp lemmas computable by simp ([#7010](https://github.com/leanprover-community/mathlib/pull/7010))
A follow-up to [#6795](https://github.com/leanprover-community/mathlib/pull/6795),  enabling the computation of integrals of the form `∫ x in a..b, f (c * x + d)` by `simp`, where `f` is a function whose integral is already in mathlib and `c` and `d` are any real constants such that `c ≠ 0`.
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* interval_integral.integral_comp_add_div
- \+/\- *lemma* interval_integral.integral_comp_add_mul
- \+/\- *lemma* interval_integral.integral_comp_add_right
- \+/\- *lemma* interval_integral.integral_comp_div
- \+/\- *lemma* interval_integral.integral_comp_div_add
- \+/\- *lemma* interval_integral.integral_comp_div_sub
- \+/\- *lemma* interval_integral.integral_comp_mul_add
- \+/\- *lemma* interval_integral.integral_comp_mul_left
- \+/\- *lemma* interval_integral.integral_comp_mul_right
- \+/\- *lemma* interval_integral.integral_comp_mul_sub
- \+/\- *lemma* interval_integral.integral_comp_sub_div
- \+/\- *lemma* interval_integral.integral_comp_sub_left
- \+/\- *lemma* interval_integral.integral_comp_sub_mul
- \+/\- *lemma* interval_integral.integral_comp_sub_right



## [2021-04-07 02:18:19](https://github.com/leanprover-community/mathlib/commit/97832da)
chore(logic/function/basic): remove classical decidable instance from a lemma statement ([#6488](https://github.com/leanprover-community/mathlib/pull/6488))
Found using [#6485](https://github.com/leanprover-community/mathlib/pull/6485)
This means that this lemma can be use in reverse against any `ite`, not just one that uses `classical.decidable`.
#### Estimated changes
Modified src/logic/function/basic.lean
- \+/\- *lemma* function.extend_def



## [2021-04-07 02:18:17](https://github.com/leanprover-community/mathlib/commit/a1057a3)
feat(data/finsum): sums over sets and types with no finiteness hypotheses ([#6355](https://github.com/leanprover-community/mathlib/pull/6355))
This rather large PR is mostly work of Jason KY. It is all an API for `finsum` and `finsum_in`, sums over sets with no finiteness assumption, and which return zero if the sum is infinite.
#### Estimated changes
Added src/algebra/big_operators/finprod.lean
- \+ *lemma* exists_ne_one_of_finprod_mem_ne_one
- \+ *lemma* finprod_cond_eq_left
- \+ *lemma* finprod_cond_eq_right
- \+ *lemma* finprod_congr
- \+ *lemma* finprod_congr_Prop
- \+ *lemma* finprod_def
- \+ *lemma* finprod_eq_dif
- \+ *lemma* finprod_eq_if
- \+ *lemma* finprod_eq_mul_indicator_apply
- \+ *lemma* finprod_eq_prod
- \+ *lemma* finprod_eq_prod_of_fintype
- \+ *lemma* finprod_eq_prod_of_mul_support_subset
- \+ *lemma* finprod_eq_prod_of_mul_support_to_finset_subset
- \+ *lemma* finprod_eq_prod_plift_of_mul_support_subset
- \+ *lemma* finprod_eq_prod_plift_of_mul_support_to_finset_subset
- \+ *lemma* finprod_false
- \+ *lemma* finprod_mem_Union
- \+ *lemma* finprod_mem_bUnion
- \+ *lemma* finprod_mem_coe_finset
- \+ *lemma* finprod_mem_comm
- \+ *lemma* finprod_mem_congr
- \+ *lemma* finprod_mem_def
- \+ *lemma* finprod_mem_empty
- \+ *lemma* finprod_mem_eq_finite_to_finset_prod
- \+ *lemma* finprod_mem_eq_of_bij_on
- \+ *lemma* finprod_mem_eq_one_of_infinite
- \+ *lemma* finprod_mem_eq_prod
- \+ *lemma* finprod_mem_eq_prod_filter
- \+ *lemma* finprod_mem_eq_prod_of_inter_mul_support_eq
- \+ *lemma* finprod_mem_eq_prod_of_mem_iff
- \+ *lemma* finprod_mem_eq_prod_of_subset
- \+ *lemma* finprod_mem_eq_to_finset_prod
- \+ *lemma* finprod_mem_finset_eq_prod
- \+ *lemma* finprod_mem_image'
- \+ *lemma* finprod_mem_image
- \+ *lemma* finprod_mem_induction
- \+ *lemma* finprod_mem_insert'
- \+ *lemma* finprod_mem_insert
- \+ *lemma* finprod_mem_insert_of_eq_one_if_not_mem
- \+ *lemma* finprod_mem_insert_one
- \+ *lemma* finprod_mem_inter_mul_diff'
- \+ *lemma* finprod_mem_inter_mul_diff
- \+ *lemma* finprod_mem_inter_mul_support
- \+ *lemma* finprod_mem_inter_mul_support_eq'
- \+ *lemma* finprod_mem_inter_mul_support_eq
- \+ *lemma* finprod_mem_mul_diff'
- \+ *lemma* finprod_mem_mul_diff
- \+ *lemma* finprod_mem_mul_distrib'
- \+ *lemma* finprod_mem_mul_distrib
- \+ *lemma* finprod_mem_of_eq_on_one
- \+ *lemma* finprod_mem_one
- \+ *lemma* finprod_mem_pair
- \+ *lemma* finprod_mem_range'
- \+ *lemma* finprod_mem_range
- \+ *lemma* finprod_mem_sUnion
- \+ *lemma* finprod_mem_singleton
- \+ *lemma* finprod_mem_union''
- \+ *lemma* finprod_mem_union'
- \+ *lemma* finprod_mem_union
- \+ *lemma* finprod_mem_union_inter'
- \+ *lemma* finprod_mem_union_inter
- \+ *lemma* finprod_mem_univ
- \+ *lemma* finprod_mul_distrib
- \+ *lemma* finprod_of_empty
- \+ *lemma* finprod_of_infinite_mul_support
- \+ *lemma* finprod_one
- \+ *lemma* finprod_set_coe_eq_finprod_mem
- \+ *lemma* finprod_subtype_eq_finprod_cond
- \+ *lemma* finprod_true
- \+ *lemma* finprod_unique
- \+ *lemma* monoid_hom.map_finprod
- \+ *lemma* monoid_hom.map_finprod_Prop
- \+ *lemma* monoid_hom.map_finprod_mem'
- \+ *lemma* monoid_hom.map_finprod_mem
- \+ *lemma* monoid_hom.map_finprod_plift
- \+ *lemma* nonempty_of_finprod_mem_ne_one

Modified src/data/dfinsupp.lean
- \- *lemma* dfinsupp.finite_supp
- \+ *lemma* dfinsupp.finite_support

Modified src/data/equiv/basic.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.insert_inter_of_mem
- \+ *lemma* set.insert_inter_of_not_mem

Modified src/data/set/finite.lean
- \+/\- *lemma* set.finite.coe_to_finset
- \+ *theorem* set.finite.inter_of_left
- \+ *theorem* set.finite.inter_of_right
- \+ *theorem* set.finite.of_preimage
- \+ *lemma* set.finite_empty_to_finset

Modified src/data/support.lean
- \+ *lemma* set.image_inter_mul_support_eq

Modified src/order/complete_lattice.lean




## [2021-04-06 18:32:51](https://github.com/leanprover-community/mathlib/commit/6ea4e9b)
feat(linear_algebra/eigenspace): generalized eigenvalues are just eigenvalues ([#7059](https://github.com/leanprover-community/mathlib/pull/7059))
#### Estimated changes
Modified src/linear_algebra/eigenspace.lean
- \+/\- *lemma* module.End.generalized_eigenspace_mono
- \+ *lemma* module.End.has_eigenvalue_of_has_generalized_eigenvalue
- \+ *lemma* module.End.has_generalized_eigenvalue_iff_has_eigenvalue



## [2021-04-06 18:32:50](https://github.com/leanprover-community/mathlib/commit/9b4f0cf)
feat(data/basic/lean): add lemmas finset.subset_iff_inter_eq_{left, right} ([#7053](https://github.com/leanprover-community/mathlib/pull/7053))
These lemmas are the analogues of `set.subset_iff_inter_eq_{left, right}`, except stated for `finset`s.
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/finset.2Esubset_iff_inter_eq_left.20.2F.20right
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* finset.inter_eq_left_iff_subset
- \+ *theorem* finset.inter_eq_right_iff_subset

Modified src/data/set/basic.lean
- \+ *theorem* set.inter_eq_left_iff_subset
- \+ *theorem* set.inter_eq_right_iff_subset
- \- *theorem* set.subset_iff_inter_eq_left
- \- *theorem* set.subset_iff_inter_eq_right

Modified src/measure_theory/measure_space.lean




## [2021-04-06 18:32:49](https://github.com/leanprover-community/mathlib/commit/6a9bf98)
doc(undergrad.yaml): add equiv.perm.trunc_swap_factors ([#7021](https://github.com/leanprover-community/mathlib/pull/7021))
This looks to me like the definition being asked for
```lean
def equiv.perm.trunc_swap_factors {α : Type u} [decidable_eq α] [fintype α] (f : equiv.perm α) :
trunc {l // l.prod = f ∧ ∀ (g : equiv.perm α), g ∈ l → g.is_swap}
```
I suppose the trunc could be considered a problem, but sorting the list is an easy way out, as is `trunc.out` for undergrads who don't care about computability.
#### Estimated changes
Modified docs/undergrad.yaml




## [2021-04-06 18:32:48](https://github.com/leanprover-community/mathlib/commit/aa5ec52)
feat(group_theory/perm/cycles): Applying cycle_of to an is_cycle ([#7000](https://github.com/leanprover-community/mathlib/pull/7000))
Applying cycle_of to an is_cycle gives you either the original cycle or 1.
#### Estimated changes
Modified src/group_theory/perm/cycles.lean
- \+ *lemma* equiv.perm.cycle_of_eq_one_iff
- \+ *lemma* equiv.perm.is_cycle.cycle_of



## [2021-04-06 18:32:47](https://github.com/leanprover-community/mathlib/commit/ae6d77b)
feat(linear_algebra/free_module): a set of linearly independent vectors over a ring S is also linearly independent over a subring R of S ([#6993](https://github.com/leanprover-community/mathlib/pull/6993))
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60algebra_map.2Einjective.2Elinear_independent.60
#### Estimated changes
Modified src/linear_algebra/free_module.lean
- \+ *lemma* linear_independent.restrict_scalars_algebras

Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.restrict_scalars



## [2021-04-06 18:32:46](https://github.com/leanprover-community/mathlib/commit/5f0dbf6)
feat(algebra/group/conj): `is_conj` for `monoid`s, `is_conj.setoid`, and `conj_classes` ([#6896](https://github.com/leanprover-community/mathlib/pull/6896))
Refactors `is_conj` to work in a `monoid`
Defines `is_conj.setoid` and its quotient type, `conj_classes`
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/algebra/char_p/invertible.lean
- \+ *lemma* not_ring_char_dvd_of_invertible
- \- *lemma* ring_char_not_dvd_of_invertible

Modified src/algebra/group/conj.lean
- \+ *def* conj_classes.carrier
- \+ *lemma* conj_classes.carrier_eq_preimage_mk
- \+ *lemma* conj_classes.exists_rep
- \+ *theorem* conj_classes.forall_is_conj
- \+ *def* conj_classes.map
- \+ *lemma* conj_classes.mem_carrier_iff_mk_eq
- \+ *lemma* conj_classes.mem_carrier_mk
- \+ *lemma* conj_classes.mk_bijective
- \+ *theorem* conj_classes.mk_eq_mk_iff_is_conj
- \+ *def* conj_classes.mk_equiv
- \+ *lemma* conj_classes.mk_injective
- \+ *theorem* conj_classes.mk_surjective
- \+ *theorem* conj_classes.one_eq_mk_one
- \+ *theorem* conj_classes.quot_mk_eq_mk
- \+ *theorem* conj_classes.quotient_mk_eq_mk
- \+ *def* conj_classes
- \+ *def* conjugates_of
- \+ *lemma* is_conj.conjugates_of_eq
- \+/\- *def* is_conj
- \+ *lemma* is_conj_iff'
- \+ *lemma* is_conj_iff
- \+ *lemma* is_conj_iff_conjugates_of_eq
- \+/\- *lemma* is_conj_iff_eq
- \+ *lemma* mem_conjugates_of_self

Modified src/algebra/group/semiconj.lean
- \+ *lemma* semiconj_by_iff_eq

Modified src/deprecated/subgroup.lean
- \+ *lemma* group.conjugates_of_subset
- \- *lemma* group.conjugates_subset

Modified src/group_theory/perm/sign.lean


Modified src/group_theory/solvable.lean


Modified src/group_theory/subgroup.lean
- \- *def* group.conjugates
- \+/\- *def* group.conjugates_of_set
- \- *lemma* group.mem_conjugates_self

Modified src/representation_theory/maschke.lean




## [2021-04-06 18:32:45](https://github.com/leanprover-community/mathlib/commit/41137fe)
feat(algebra/add_submonoid_closure): the additive closure of a multiplicative submonoid is a subsemiring ([#6860](https://github.com/leanprover-community/mathlib/pull/6860))
This file is extracted from PR [#6705](https://github.com/leanprover-community/mathlib/pull/6705)
#### Estimated changes
Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* submonoid.mul_left_mem_add_closure
- \+ *lemma* submonoid.mul_mem_add_closure
- \+ *lemma* submonoid.mul_right_mem_add_closure

Modified src/ring_theory/subsemiring.lean
- \+ *def* submonoid.subsemiring_closure
- \+ *lemma* submonoid.subsemiring_closure_coe
- \+ *lemma* submonoid.subsemiring_closure_eq_closure
- \+ *lemma* submonoid.subsemiring_closure_to_add_submonoid
- \+ *lemma* subsemiring.closure_add_submonoid_closure
- \+ *lemma* subsemiring.closure_submonoid_closure
- \+ *lemma* subsemiring.coe_closure_eq



## [2021-04-06 13:27:27](https://github.com/leanprover-community/mathlib/commit/5254ef1)
feat(topology/continuous_function): lemmas about coe ([#7055](https://github.com/leanprover-community/mathlib/pull/7055))
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean
- \+ *def* coe_fn_monoid_hom
- \+ *lemma* continuous_map.coe_prod
- \+ *lemma* continuous_map.prod_apply



## [2021-04-06 13:27:25](https://github.com/leanprover-community/mathlib/commit/43aee09)
feat(algebra/pointwise): improve instances on `set_semiring` ([#7050](https://github.com/leanprover-community/mathlib/pull/7050))
If `α` is weaker than a semiring, then `set_semiring α` inherits an appropriate weaker typeclass.
#### Estimated changes
Modified src/algebra/pointwise.lean




## [2021-04-06 13:27:23](https://github.com/leanprover-community/mathlib/commit/7928ca0)
feat(algebra/lie/subalgebra): define the restriction of a Lie module to a Lie subalgebra ([#7036](https://github.com/leanprover-community/mathlib/pull/7036))
#### Estimated changes
Modified src/algebra/lie/abelian.lean


Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_subalgebra.coe_bracket_of_module



## [2021-04-06 13:27:20](https://github.com/leanprover-community/mathlib/commit/2b7b1e7)
refactor(algebra/group/inj_surj): eliminate the versions of the definitions without `has_div` / `has_sub`. ([#7035](https://github.com/leanprover-community/mathlib/pull/7035))
The variables without the `_sub` / `_div` suffix were vestigial definitions that existed in order to prevent the already-large `div_inv_monoid` refactor becoming larger. This change removes all their remaining usages, allowing the `_sub` / `_div` versions to lose their suffix.
This changes the division operation on `α →ₘ[μ] γ` and the subtraction operator on `truncated_witt_vector p n R` to definitionally match the division operation on their components. In practice, this just shuffles some uses of `sub_eq_add_neg` around.
#### Estimated changes
Modified src/algebra/field.lean


Modified src/algebra/group/inj_surj.lean


Modified src/algebra/group_with_zero/basic.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/ring/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/normed_space/normed_group_hom.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/real/nnreal.lean


Modified src/group_theory/subgroup.lean


Modified src/measure_theory/ae_eq_fun.lean
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_div
- \- *lemma* measure_theory.ae_eq_fun.coe_fn_sub
- \+ *lemma* measure_theory.ae_eq_fun.div_to_germ
- \+ *lemma* measure_theory.ae_eq_fun.mk_div
- \- *lemma* measure_theory.ae_eq_fun.mk_sub

Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/lp_space.lean


Modified src/ring_theory/witt_vector/basic.lean


Modified src/ring_theory/witt_vector/truncated.lean
- \+ *lemma* witt_vector.truncate_fun_sub

Modified src/topology/algebra/multilinear.lean




## [2021-04-06 13:27:19](https://github.com/leanprover-community/mathlib/commit/0007c4a)
feat(topology/constructions): `function.update` is continuous in both arguments ([#7023](https://github.com/leanprover-community/mathlib/pull/7023))
#### Estimated changes
Modified src/topology/algebra/multilinear.lean


Modified src/topology/constructions.lean
- \+ *lemma* continuous.update
- \+ *lemma* continuous_at.update
- \+ *lemma* continuous_at_apply
- \+/\- *lemma* continuous_update
- \+ *lemma* filter.tendsto.apply
- \+ *lemma* filter.tendsto.update



## [2021-04-06 09:41:40](https://github.com/leanprover-community/mathlib/commit/d7f6bd6)
feat(data/finsupp,linear_algebra/finsupp): `finsupp`s and sum types ([#6992](https://github.com/leanprover-community/mathlib/pull/6992))
This PR contains a few definitions relating sum types and `finsupp`. The main result is `finsupp.sum_arrow_equiv_prod_arrow`, a `finsupp` version of `equiv.sum_arrow_equiv_prod_arrow`. This is turned into a `linear_equiv` by `finsupp.sum_arrow_lequiv_prod_arrow`.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.coe_sum_elim
- \+ *lemma* finsupp.fst_sum_finsupp_add_equiv_prod_finsupp
- \+ *lemma* finsupp.fst_sum_finsupp_equiv_prod_finsupp
- \+ *lemma* finsupp.snd_sum_finsupp_add_equiv_prod_finsupp
- \+ *lemma* finsupp.snd_sum_finsupp_equiv_prod_finsupp
- \+ *def* finsupp.sum_elim
- \+ *lemma* finsupp.sum_elim_apply
- \+ *lemma* finsupp.sum_elim_inl
- \+ *lemma* finsupp.sum_elim_inr
- \+ *def* finsupp.sum_finsupp_add_equiv_prod_finsupp
- \+ *lemma* finsupp.sum_finsupp_add_equiv_prod_finsupp_symm_inl
- \+ *lemma* finsupp.sum_finsupp_add_equiv_prod_finsupp_symm_inr
- \+ *def* finsupp.sum_finsupp_equiv_prod_finsupp
- \+ *lemma* finsupp.sum_finsupp_equiv_prod_finsupp_symm_inl
- \+ *lemma* finsupp.sum_finsupp_equiv_prod_finsupp_symm_inr

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.fst_sum_finsupp_lequiv_prod_finsupp
- \+ *lemma* finsupp.snd_sum_finsupp_lequiv_prod_finsupp
- \+ *def* finsupp.sum_finsupp_lequiv_prod_finsupp
- \+ *lemma* finsupp.sum_finsupp_lequiv_prod_finsupp_symm_inl
- \+ *lemma* finsupp.sum_finsupp_lequiv_prod_finsupp_symm_inr



## [2021-04-06 09:41:39](https://github.com/leanprover-community/mathlib/commit/82b0b30)
refactor(analysis/normed_space/normed_group_hom): generalize to semi_normed_group ([#6977](https://github.com/leanprover-community/mathlib/pull/6977))
This is part of a series of PR to have the theory of `semi_normed_group` (and related concepts) in mathlib.
We generalize here `normed_group_hom` to `semi_normed_group` (keeping the old name to avoid too long names).
- [x] depends on: [#6910](https://github.com/leanprover-community/mathlib/pull/6910)
#### Estimated changes
Modified src/analysis/normed_space/normed_group_hom.lean
- \+/\- *lemma* exists_pos_bound_of_bound
- \+/\- *lemma* normed_group_hom.norm_id
- \+ *lemma* normed_group_hom.norm_id_of_nontrivial_seminorm
- \+ *theorem* normed_group_hom.op_norm_zero
- \+/\- *theorem* normed_group_hom.op_norm_zero_iff
- \+/\- *structure* normed_group_hom



## [2021-04-06 09:41:37](https://github.com/leanprover-community/mathlib/commit/02058ed)
feat(group_theory/perm/*): facts about the cardinality of the support of a permutation ([#6951](https://github.com/leanprover-community/mathlib/pull/6951))
Proves lemmas about the cardinality of the support of a permutation
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/group_theory/perm/cycles.lean
- \+ *def* equiv.perm.cycle_factors
- \+ *def* equiv.perm.cycle_factors_aux
- \+ *lemma* equiv.perm.cycle_induction_on
- \+ *def* equiv.perm.cycle_of
- \+ *lemma* equiv.perm.is_cycle.ne_one
- \+ *lemma* equiv.perm.is_cycle.two_le_card_support
- \- *lemma* equiv.perm.one_lt_nonfixed_point_card_of_ne_one
- \+ *def* equiv.perm.trunc_cycle_factors

Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.apply_mem_support
- \+ *lemma* equiv.perm.card_support_eq_two
- \+ *lemma* equiv.perm.card_support_eq_zero
- \+ *lemma* equiv.perm.card_support_le_one
- \+ *lemma* equiv.perm.card_support_ne_one
- \+ *lemma* equiv.perm.card_support_prod_list_of_pairwise_disjoint
- \+/\- *lemma* equiv.perm.card_support_swap_mul
- \+ *lemma* equiv.perm.disjoint.card_support_mul
- \+ *lemma* equiv.perm.disjoint.disjoint_support
- \+ *lemma* equiv.perm.disjoint.support_mul
- \+ *lemma* equiv.perm.disjoint_iff_disjoint_support
- \+ *lemma* equiv.perm.disjoint_prod_list_of_disjoint
- \+ *lemma* equiv.perm.exists_mem_support_of_mem_support_prod
- \+/\- *lemma* equiv.perm.mem_support
- \+ *lemma* equiv.perm.one_lt_card_support_of_ne_one
- \+/\- *def* equiv.perm.support
- \+ *lemma* equiv.perm.support_eq_empty_iff
- \+ *lemma* equiv.perm.support_inv
- \+ *lemma* equiv.perm.support_mul_le
- \+ *lemma* equiv.perm.support_one
- \+/\- *lemma* equiv.perm.support_pow_le
- \+/\- *lemma* equiv.perm.support_swap_mul_eq
- \+ *lemma* equiv.perm.two_le_card_support_of_ne_one



## [2021-04-06 09:41:36](https://github.com/leanprover-community/mathlib/commit/07aa34e)
feat(algebra/category/Module): compare concrete and abstract kernels ([#6938](https://github.com/leanprover-community/mathlib/pull/6938))
#### Estimated changes
Modified src/algebra/category/Module/basic.lean


Modified src/algebra/category/Module/kernels.lean
- \+ *lemma* Module.cokernel_π_cokernel_iso_range_quotient_hom
- \+ *lemma* Module.kernel_iso_ker_hom_ker_subtype
- \+ *lemma* Module.kernel_iso_ker_inv_kernel_ι
- \+ *lemma* Module.range_mkq_cokernel_iso_range_quotient_inv

Modified src/algebra/category/Mon/basic.lean


Modified src/category_theory/concrete_category/basic.lean
- \+ *lemma* category_theory.concrete_category.congr_arg
- \+ *lemma* category_theory.concrete_category.congr_hom



## [2021-04-06 09:41:35](https://github.com/leanprover-community/mathlib/commit/3a99001)
feat(category_theory): Type u is well-powered ([#6812](https://github.com/leanprover-community/mathlib/pull/6812))
A minor test of the `well_powered` API: we can verify that `Type u` is well-powered, and show `subobject α ≃o set α`.
#### Estimated changes
Modified src/category_theory/concrete_category/basic.lean
- \+/\- *lemma* category_theory.concrete_category.hom_ext
- \+ *lemma* category_theory.congr_hom

Modified src/category_theory/equivalence.lean
- \+ *def* category_theory.equivalence.to_order_iso
- \+ *lemma* category_theory.equivalence.to_order_iso_apply
- \+ *lemma* category_theory.equivalence.to_order_iso_symm_apply

Modified src/category_theory/isomorphism.lean
- \+ *lemma* category_theory.iso.to_eq

Modified src/category_theory/skeletal.lean
- \+ *def* category_theory.equivalence.thin_skeleton_order_iso

Added src/category_theory/subobject/types.lean
- \+ *lemma* subtype_val_mono
- \+ *def* types.mono_over_equivalence_set



## [2021-04-06 05:50:28](https://github.com/leanprover-community/mathlib/commit/2daf2ff)
chore(scripts): update nolints.txt ([#7052](https://github.com/leanprover-community/mathlib/pull/7052))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-04-06 05:50:27](https://github.com/leanprover-community/mathlib/commit/6f38c14)
chore(data/finsupp/pointwise): add missing `finsupp.mul_zero_class` ([#7049](https://github.com/leanprover-community/mathlib/pull/7049))
#### Estimated changes
Modified src/data/finsupp/pointwise.lean




## [2021-04-06 05:50:26](https://github.com/leanprover-community/mathlib/commit/aa665b1)
feat(linear_algebra/finsupp): add refl/trans/symm lemmas for dom_lcongr ([#7048](https://github.com/leanprover-community/mathlib/pull/7048))
These are just copies of the lemmas for `dom_congr`
#### Estimated changes
Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.dom_lcongr_refl
- \+ *lemma* finsupp.dom_lcongr_symm
- \+ *lemma* finsupp.dom_lcongr_trans



## [2021-04-06 05:50:24](https://github.com/leanprover-community/mathlib/commit/8b34e00)
feat(order/complete_lattice): le_Sup and Inf_le iff lemmas ([#7047](https://github.com/leanprover-community/mathlib/pull/7047))
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *lemma* Inf_le_iff
- \+ *lemma* le_Sup_iff



## [2021-04-06 05:50:21](https://github.com/leanprover-community/mathlib/commit/ba264c4)
chore(group_theory/group_action):  cleanup ([#7045](https://github.com/leanprover-community/mathlib/pull/7045))
Clean up stabilizers and add a missing simp lemma.
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \+/\- *lemma* mul_action.mem_stabilizer_iff
- \+ *lemma* mul_action.mem_stabilizer_submonoid_iff
- \+/\- *lemma* mul_action.quotient.smul_coe
- \- *def* mul_action.stabilizer.subgroup
- \- *def* mul_action.stabilizer_carrier



## [2021-04-06 05:50:21](https://github.com/leanprover-community/mathlib/commit/5312895)
chore(group_theory/order_of_element): move some lemmas ([#7031](https://github.com/leanprover-community/mathlib/pull/7031))
I moved a few lemmas to `group_theory.subgroup` and to `group_theory.coset` and to `data.finset.basic`. Feel free to suggest different locations if they don't quite fit. This resolves [#1563](https://github.com/leanprover-community/mathlib/pull/1563).
Renamed `card_trivial` to `subgroup.card_bot`
#### Estimated changes
Modified docs/100.yaml


Modified src/data/finset/basic.lean
- \+ *lemma* finset.mem_range_iff_mem_finset_range_of_mod_eq'
- \+ *lemma* finset.mem_range_iff_mem_finset_range_of_mod_eq

Modified src/group_theory/coset.lean
- \+ *lemma* subgroup.card_eq_card_quotient_mul_card_subgroup
- \+ *lemma* subgroup.card_quotient_dvd_card
- \+ *lemma* subgroup.card_subgroup_dvd_card

Modified src/group_theory/order_of_element.lean
- \- *lemma* card_eq_card_quotient_mul_card_subgroup
- \- *lemma* card_quotient_dvd_card
- \- *lemma* card_subgroup_dvd_card
- \- *lemma* card_trivial
- \- *lemma* finset.mem_range_iff_mem_finset_range_of_mod_eq'
- \- *lemma* finset.mem_range_iff_mem_finset_range_of_mod_eq
- \- *lemma* mem_normalizer_fintype

Modified src/group_theory/perm/sign.lean


Modified src/group_theory/subgroup.lean
- \+ *lemma* add_subgroup.card_bot
- \+ *lemma* subgroup.card_bot
- \+ *lemma* subgroup.mem_normalizer_fintype

Modified src/group_theory/sylow.lean




## [2021-04-06 05:50:20](https://github.com/leanprover-community/mathlib/commit/dbb2b55)
feat(measure_theory/interval_integral): more on integral_comp ([#7030](https://github.com/leanprover-community/mathlib/pull/7030))
I replace `integral_comp_mul_right_of_pos`, `integral_comp_mul_right_of_neg`, and `integral_comp_mul_right` with a single lemma.
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \- *lemma* interval_integral.integral_comp_mul_right_of_neg
- \- *lemma* interval_integral.integral_comp_mul_right_of_pos



## [2021-04-06 05:50:19](https://github.com/leanprover-community/mathlib/commit/82fd6e1)
feat(logic/girard): Girard's paradox  ([#7026](https://github.com/leanprover-community/mathlib/pull/7026))
A proof of Girard's paradox in lean, based on the LF proof: http://www.cs.cmu.edu/~kw/research/hurkens95tlca.elf
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* cast_eq_iff_heq

Added src/logic/girard.lean
- \+ *theorem* {u}

Modified src/logic/small.lean
- \+ *theorem* not_small_type
- \+ *theorem* small_type



## [2021-04-06 05:50:18](https://github.com/leanprover-community/mathlib/commit/415b369)
feat(linear_algebra): `c ≤ dim K E` iff there exists a linear independent `s : set E`, `card s = c` ([#7014](https://github.com/leanprover-community/mathlib/pull/7014))
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* le_dim_iff_exists_linear_independent
- \+ *lemma* le_dim_iff_exists_linear_independent_finset
- \+ *lemma* le_rank_iff_exists_linear_independent
- \+ *lemma* le_rank_iff_exists_linear_independent_finset

Modified src/linear_algebra/linear_independent.lean
- \+ *theorem* linear_independent.image_of_comp

Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.mk_eq_nat_iff_finset



## [2021-04-06 05:50:17](https://github.com/leanprover-community/mathlib/commit/4192612)
chore(data/fintype/basic): add `card_unique` and a warning note to `card_of_subsingleton` ([#7008](https://github.com/leanprover-community/mathlib/pull/7008))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *theorem* fintype.card_unique



## [2021-04-06 05:50:16](https://github.com/leanprover-community/mathlib/commit/975f533)
chore(topology/continuous_function/algebra): add simp lemmas for smul coercion, move names out of global namespace ([#7007](https://github.com/leanprover-community/mathlib/pull/7007))
The two new lemmas proposed are:
- `continuous_map.smul_coe`
- `continuous_functions.smul_coe`
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean
- \+ *lemma* continuous_functions.smul_coe
- \+ *lemma* continuous_map.div_coe
- \+ *lemma* continuous_map.inv_coe
- \+ *lemma* continuous_map.pow_coe
- \+/\- *lemma* continuous_map.smul_apply
- \+ *lemma* continuous_map.smul_coe
- \- *lemma* div_coe
- \- *lemma* inv_coe
- \- *lemma* pow_coe



## [2021-04-06 05:50:15](https://github.com/leanprover-community/mathlib/commit/90e265e)
feat(algebra/category): the category of R-modules is well-powered ([#7002](https://github.com/leanprover-community/mathlib/pull/7002))
#### Estimated changes
Modified src/algebra/category/Module/subobject.lean




## [2021-04-06 05:50:13](https://github.com/leanprover-community/mathlib/commit/030a704)
feat(group_theory/perm/sign): Order of product of disjoint permutations ([#6998](https://github.com/leanprover-community/mathlib/pull/6998))
The order of the product of disjoint permutations is the lcm of the orders.
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* commute.order_of_mul_dvd_lcm

Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.disjoint.gpow_disjoint_gpow
- \+ *lemma* equiv.perm.disjoint.mul_apply_eq_iff
- \+ *lemma* equiv.perm.disjoint.mul_eq_one_iff
- \+ *lemma* equiv.perm.disjoint.order_of
- \+ *lemma* equiv.perm.disjoint.pow_disjoint_pow



## [2021-04-06 05:50:12](https://github.com/leanprover-community/mathlib/commit/fe16235)
feat(category_theory): equivalences preserve epis and monos ([#6994](https://github.com/leanprover-community/mathlib/pull/6994))
Note that these don't follow from the results in `limits/constructions/epi_mono.lean`, since the results in that file are less universe polymorphic.
#### Estimated changes
Modified src/category_theory/epi_mono.lean




## [2021-04-06 05:50:11](https://github.com/leanprover-community/mathlib/commit/89ea423)
feat(archive/imo): formalize IMO 2005 Q3 ([#6984](https://github.com/leanprover-community/mathlib/pull/6984))
feat(archive/imo): formalize IMO 2005 Q3
#### Estimated changes
Added archive/imo/imo2005_q3.lean
- \+ *theorem* imo2005_q3
- \+ *lemma* key_insight



## [2021-04-06 05:50:10](https://github.com/leanprover-community/mathlib/commit/b05affb)
chore(group_theory/subgroup): translate map comap lemmas from linear_map ([#6979](https://github.com/leanprover-community/mathlib/pull/6979))
Introduce the analogues of `linear_map.map_comap_eq` and `linear_map.comap_map_eq` to subgroups.
Also add `subgroup.map_eq_comap_of_inverse` which is a translation of `set.image_eq_preimage_of_inverse`.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.comap_injective
- \+ *lemma* subgroup.comap_map_eq
- \+ *lemma* subgroup.comap_map_eq_self
- \+ *lemma* subgroup.comap_map_eq_self_of_injective
- \+ *lemma* subgroup.comap_mono
- \+ *lemma* subgroup.ker_le_comap
- \+ *lemma* subgroup.le_comap_map
- \+ *lemma* subgroup.map_comap_eq
- \+ *lemma* subgroup.map_comap_eq_self
- \+ *lemma* subgroup.map_comap_eq_self_of_surjective
- \+ *lemma* subgroup.map_comap_le
- \+ *lemma* subgroup.map_eq_comap_of_inverse
- \+ *lemma* subgroup.map_injective
- \+ *lemma* subgroup.map_le_range
- \+ *lemma* subgroup.map_mono



## [2021-04-06 05:50:09](https://github.com/leanprover-community/mathlib/commit/6aa0e30)
feat(category_theory/preadditive): additive functors preserve biproducts ([#6882](https://github.com/leanprover-community/mathlib/pull/6882))
An additive functor between preadditive categories creates and preserves biproducts.
Also, renames `src/category_theory/abelian/additive_functor.lean` to `src/category_theory/preadditive/additive_functor.lean` as it so far doesn't actually rely on anything being abelian. 
Also, moves the `.map_X` lemmas about additive functors into the `functor` namespace, so we can use dot notation `F.map_add` etc, when `[functor.additive F]` is available.
#### Estimated changes
Modified src/algebra/homology/chain_complex.lean


Deleted src/category_theory/abelian/additive_functor.lean
- \- *lemma* category_theory.functor.additive.map_neg
- \- *lemma* category_theory.functor.additive.map_sub
- \- *lemma* category_theory.functor.coe_map_add_hom
- \- *def* category_theory.functor.map_add_hom

Modified src/category_theory/functor.lean
- \+ *lemma* category_theory.functor.map_dite

Added src/category_theory/preadditive/additive_functor.lean
- \+ *lemma* category_theory.functor.coe_map_add_hom
- \+ *lemma* category_theory.functor.map_add
- \+ *def* category_theory.functor.map_add_hom
- \+ *def* category_theory.functor.map_biproduct
- \+ *lemma* category_theory.functor.map_neg
- \+ *lemma* category_theory.functor.map_sub
- \+ *lemma* category_theory.functor.map_sum
- \+ *lemma* category_theory.functor.map_zero

Modified src/category_theory/triangulated/basic.lean


Modified src/category_theory/triangulated/rotate.lean




## [2021-04-06 01:49:51](https://github.com/leanprover-community/mathlib/commit/4ddbdc1)
refactor(topology/sheaves): Refactor sheaf condition proofs ([#6962](https://github.com/leanprover-community/mathlib/pull/6962))
This PR adds two convenience Lemmas for working with the sheaf condition in terms of unique gluing and then uses them to greatly simplify the proofs of the sheaf condition for sheaves of functions (with and without a local predicate). Basically, all the categorical jargon gets outsourced and the actual proofs of the sheaf condition can now work in a very concrete setting. This drastically reduced the size of the proofs and eliminated any uses of `simp`.
Note that I'm effectively translating the sheaf condition from `Type` into a `Prop`, i.e. using `∃!` instead of using an instance of `unique`. I guess this diverts slightly from the original design in which the sheaf condition was always a `Type`. I found this to work quite well but maybe there is a way to phrase it differently.
#### Estimated changes
Modified src/topology/sheaves/local_predicate.lean
- \- *def* Top.subpresheaf_to_Types.diagram_subtype
- \- *lemma* Top.subpresheaf_to_Types.sheaf_condition_fac
- \- *lemma* Top.subpresheaf_to_Types.sheaf_condition_uniq

Modified src/topology/sheaves/sheaf_condition/unique_gluing.lean
- \+ *def* Top.presheaf.sheaf_condition_of_exists_unique_gluing
- \+ *lemma* Top.sheaf.exists_unique_gluing

Modified src/topology/sheaves/sheaf_of_functions.lean




## [2021-04-06 01:49:50](https://github.com/leanprover-community/mathlib/commit/1e1eaae)
feat(archive/imo): formalize IMO 2008 Q2 ([#6958](https://github.com/leanprover-community/mathlib/pull/6958))
#### Estimated changes
Added archive/imo/imo2008_q2.lean
- \+ *theorem* imo2008_q2a
- \+ *theorem* imo2008_q2b
- \+ *def* rational_solutions
- \+ *lemma* subst_abc



## [2021-04-06 01:49:48](https://github.com/leanprover-community/mathlib/commit/0cc1fee)
feat(linear_algebra/finsupp): lemmas for finsupp_tensor_finsupp ([#6905](https://github.com/leanprover-community/mathlib/pull/6905))
#### Estimated changes
Modified src/linear_algebra/direct_sum/finsupp.lean
- \+ *def* finsupp_tensor_finsupp'
- \+ *lemma* finsupp_tensor_finsupp'_apply_apply
- \+ *lemma* finsupp_tensor_finsupp'_single_tmul_single
- \+ *theorem* finsupp_tensor_finsupp_apply

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.lcongr_apply_apply
- \+/\- *theorem* finsupp.lcongr_single
- \+ *lemma* finsupp.lcongr_symm
- \+ *theorem* finsupp.lcongr_symm_single



## [2021-04-06 01:49:47](https://github.com/leanprover-community/mathlib/commit/108fa6f)
feat(order/bounded_lattice): min/max commute with coe ([#6900](https://github.com/leanprover-community/mathlib/pull/6900))
to with_bot and with_top
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+ *lemma* with_bot.coe_max
- \+ *lemma* with_bot.coe_min
- \+ *lemma* with_top.coe_max
- \+ *lemma* with_top.coe_min



## [2021-04-06 01:49:46](https://github.com/leanprover-community/mathlib/commit/13f7910)
feat(category_theory/limits/kan_extension): Right and Left Kan extensions of a functor ([#6820](https://github.com/leanprover-community/mathlib/pull/6820))
This PR adds the left and right Kan extensions of a functor, and constructs the associated adjunction.
coauthored by @b-mehta 
A followup PR should prove that the adjunctions in this file are (co)reflective when \iota is fully faithful.
The current PR proves certain objects are initial/terminal, which will be useful for this.
#### Estimated changes
Added src/category_theory/limits/kan_extension.lean
- \+ *def* category_theory.Lan.adjunction
- \+ *def* category_theory.Lan.cocone
- \+ *abbreviation* category_theory.Lan.diagram
- \+ *def* category_theory.Lan.equiv
- \+ *def* category_theory.Lan.loc
- \+ *def* category_theory.Lan
- \+ *def* category_theory.Ran.adjunction
- \+ *def* category_theory.Ran.cone
- \+ *abbreviation* category_theory.Ran.diagram
- \+ *def* category_theory.Ran.equiv
- \+ *def* category_theory.Ran.loc
- \+ *def* category_theory.Ran

Modified src/category_theory/structured_arrow.lean
- \+ *def* category_theory.costructured_arrow.proj
- \+ *def* category_theory.structured_arrow.proj



## [2021-04-06 01:49:45](https://github.com/leanprover-community/mathlib/commit/8e2db7f)
refactor(order/boolean_algebra): generalized Boolean algebras ([#6775](https://github.com/leanprover-community/mathlib/pull/6775))
We add ["generalized Boolean algebras"](https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations), following a [suggestion](https://github.com/leanprover-community/mathlib/pull/6469#issuecomment-787521935) of @jsm28. Now `boolean_algebra` extends `generalized_boolean_algebra` and `boolean_algebra.core`:
```lean
class generalized_boolean_algebra (α : Type u) extends semilattice_sup_bot α, semilattice_inf_bot α,
  distrib_lattice α, has_sdiff α :=
(sup_inf_sdiff : ∀a b:α, (a ⊓ b) ⊔ (a \ b) = a)
(inf_inf_sdiff : ∀a b:α, (a ⊓ b) ⊓ (a \ b) = ⊥)
class boolean_algebra.core (α : Type u) extends bounded_distrib_lattice α, has_compl α :=
(inf_compl_le_bot : ∀x:α, x ⊓ xᶜ ≤ ⊥)
(top_le_sup_compl : ∀x:α, ⊤ ≤ x ⊔ xᶜ)
class boolean_algebra (α : Type u) extends generalized_boolean_algebra α, boolean_algebra.core α :=
(sdiff_eq : ∀x y:α, x \ y = x ⊓ yᶜ)
```
I also added a module doc for `order/boolean_algebra`.
Many lemmas about set difference both for `finset`s and `set`s now follow from their `generalized_boolean_algebra` counterparts and I've removed the (fin)set-specific proofs.
`finset.sdiff_subset_self` was removed in favor of the near-duplicate `finset.sdiff_subset` (the latter has more explicit arguments).
#### Estimated changes
Modified archive/imo/imo1998_q2.lean


Modified docs/references.bib


Modified src/algebra/big_operators/basic.lean


Modified src/algebra/punit_instances.lean


Modified src/algebra/ring/boolean_ring.lean
- \+ *def* boolean_ring.has_bot
- \+ *def* boolean_ring.has_sdiff
- \+ *lemma* boolean_ring.inf_inf_sdiff
- \+ *lemma* boolean_ring.sup_inf_sdiff
- \+/\- *lemma* mul_add_mul
- \+ *lemma* mul_one_add_self

Modified src/analysis/calculus/deriv.lean


Modified src/data/finset/basic.lean
- \+ *lemma* finset.bot_eq_empty
- \+/\- *theorem* finset.inf_eq_inter
- \- *lemma* finset.inter_eq_inter_of_sdiff_eq_sdiff
- \+ *theorem* finset.le_eq_subset
- \+/\- *theorem* finset.le_iff_subset
- \+ *theorem* finset.lt_eq_subset
- \+/\- *theorem* finset.lt_iff_ssubset
- \+ *lemma* finset.sdiff_eq_sdiff_iff_inter_eq_inter
- \- *theorem* finset.sdiff_subset_self
- \+/\- *theorem* finset.sup_eq_union
- \+ *lemma* finset.union_eq_sdiff_union_sdiff_union_inter

Modified src/data/finset/fold.lean


Modified src/data/finset/powerset.lean


Modified src/data/fintype/basic.lean


Modified src/data/set/basic.lean
- \+/\- *lemma* set.diff_compl
- \+/\- *lemma* set.diff_self
- \+/\- *theorem* set.diff_subset
- \+/\- *lemma* set.inf_eq_inter
- \+/\- *lemma* set.le_eq_subset
- \+/\- *lemma* set.lt_eq_ssubset
- \+/\- *lemma* set.sup_eq_union
- \+ *lemma* set.union_eq_sdiff_union_sdiff_union_inter

Modified src/data/sym2.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/set_integral.lean


Modified src/order/atoms.lean


Modified src/order/boolean_algebra.lean
- \+ *def* boolean_algebra.of_core
- \+ *lemma* bot_sdiff
- \+ *theorem* disjoint.sdiff_eq_left
- \+ *theorem* disjoint.sdiff_eq_of_sup_eq
- \+ *theorem* disjoint.sdiff_eq_right
- \+ *lemma* disjoint.sup_sdiff_cancel_left
- \+ *lemma* disjoint.sup_sdiff_cancel_right
- \+ *theorem* disjoint_inf_sdiff
- \+ *theorem* disjoint_sdiff
- \+ *lemma* disjoint_sdiff_iff_le
- \+ *lemma* disjoint_sdiff_sdiff
- \+ *theorem* inf_inf_sdiff
- \+ *lemma* inf_sdiff
- \+ *lemma* inf_sdiff_assoc
- \+ *lemma* inf_sdiff_eq_bot_iff
- \+ *theorem* inf_sdiff_inf
- \+ *lemma* inf_sdiff_left
- \+ *lemma* inf_sdiff_right
- \+ *theorem* inf_sdiff_self_left
- \+ *theorem* inf_sdiff_self_right
- \+ *lemma* inf_sdiff_sup_left
- \+ *lemma* inf_sdiff_sup_right
- \+ *lemma* le_iff_disjoint_sdiff
- \+ *lemma* le_iff_eq_sup_sdiff
- \+ *theorem* le_sdiff_sup
- \+ *theorem* le_sup_sdiff
- \+ *theorem* sdiff_bot
- \+ *theorem* sdiff_compl
- \+/\- *theorem* sdiff_eq
- \+ *lemma* sdiff_eq_bot_iff
- \- *theorem* sdiff_eq_left
- \+ *lemma* sdiff_eq_sdiff_iff_inf_eq_inf
- \+ *theorem* sdiff_eq_self_iff_disjoint'
- \+ *theorem* sdiff_eq_self_iff_disjoint
- \+ *lemma* sdiff_idem
- \- *lemma* sdiff_idem_right
- \+ *lemma* sdiff_inf
- \+ *lemma* sdiff_inf_sdiff
- \+ *lemma* sdiff_inf_self_left
- \+ *lemma* sdiff_inf_self_right
- \+ *lemma* sdiff_le
- \+ *lemma* sdiff_le_comm
- \+ *lemma* sdiff_le_iff
- \+ *lemma* sdiff_le_sdiff_self
- \+ *lemma* sdiff_le_self_sdiff
- \+ *lemma* sdiff_sdiff_comm
- \+ *lemma* sdiff_sdiff_eq_self
- \+ *lemma* sdiff_sdiff_left'
- \+ *lemma* sdiff_sdiff_left
- \+ *lemma* sdiff_sdiff_right'
- \+ *lemma* sdiff_sdiff_right
- \+ *lemma* sdiff_sdiff_right_self
- \+ *lemma* sdiff_sdiff_sup_sdiff'
- \+ *lemma* sdiff_sdiff_sup_sdiff
- \+ *lemma* sdiff_self
- \+ *lemma* sdiff_sup
- \+ *theorem* sdiff_symm
- \+ *theorem* sdiff_top
- \+ *theorem* sdiff_unique
- \+ *lemma* sup_eq_sdiff_sup_sdiff_sup_inf
- \+ *lemma* sup_inf_inf_sdiff
- \+ *theorem* sup_inf_sdiff
- \+ *lemma* sup_sdiff
- \+ *lemma* sup_sdiff_cancel'
- \+ *theorem* sup_sdiff_inf
- \+ *lemma* sup_sdiff_left
- \+ *lemma* sup_sdiff_left_self
- \+ *lemma* sup_sdiff_of_le
- \+ *lemma* sup_sdiff_right
- \+ *lemma* sup_sdiff_right_self
- \- *theorem* sup_sdiff_same
- \+ *theorem* sup_sdiff_self_left
- \+ *theorem* sup_sdiff_self_right
- \+ *lemma* sup_sdiff_symm
- \+ *theorem* top_sdiff

Modified src/order/bounded_lattice.lean


Modified src/order/lattice.lean
- \+ *lemma* inf_left_right_swap
- \+ *lemma* sup_left_right_swap

Modified src/ring_theory/polynomial/symmetric.lean




## [2021-04-06 01:49:44](https://github.com/leanprover-community/mathlib/commit/61d2ad0)
chore(algebra/char_p/basic): uniformise notation and weaken some assumptions ([#6765](https://github.com/leanprover-community/mathlib/pull/6765))
I had looked at this file in an earlier PR and decided to come back to uniformise the notation, using always `R` and never `α` for the generic type of the file.
While I was at it, I started also changing
* some `semiring` assumptions to `add_monoid + has_one`,
* some `ring` assumptions to `add_group + has_one`.
In the long run, I think that the characteristic of a ring should be defined as the order of `1` in the additive submonoid, but this is not what I am doing at the moment!
Here is a related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/char_zero
#### Estimated changes
Modified src/algebra/char_p/basic.lean
- \+/\- *theorem* add_pow_char
- \+/\- *theorem* add_pow_char_of_commute
- \+/\- *theorem* add_pow_char_pow
- \+/\- *theorem* add_pow_char_pow_of_commute
- \+/\- *lemma* char_p.cast_card_eq_zero
- \+/\- *lemma* char_p.cast_eq_mod
- \+/\- *theorem* char_p.cast_eq_zero
- \+/\- *theorem* char_p.char_ne_zero_of_fintype
- \+/\- *lemma* char_p.char_p_to_char_zero
- \+/\- *theorem* char_p.eq
- \+/\- *theorem* char_p.exists
- \+/\- *theorem* char_p.exists_unique
- \+/\- *lemma* char_p.false_of_nontrivial_of_char_one
- \+/\- *lemma* char_p.int_cast_eq_zero_iff
- \+/\- *lemma* char_p.int_coe_eq_int_coe_iff
- \+/\- *lemma* char_p.neg_one_ne_one
- \+/\- *lemma* char_p.nontrivial_of_char_ne_one
- \+/\- *lemma* char_p.ring_char_ne_one
- \+/\- *lemma* eq_iff_modeq_int
- \+/\- *theorem* frobenius_inj
- \+/\- *theorem* sub_pow_char
- \+/\- *theorem* sub_pow_char_of_commute
- \+/\- *theorem* sub_pow_char_pow
- \+/\- *theorem* sub_pow_char_pow_of_commute

Modified src/data/zmod/basic.lean


Modified src/linear_algebra/char_poly/coeff.lean
- \+ *lemma* mat_poly_equiv_eq_X_pow_sub_C

Modified src/ring_theory/perfection.lean
- \+/\- *lemma* perfection_map.map_eq_map

Modified src/ring_theory/witt_vector/init_tail.lean


Modified src/ring_theory/witt_vector/structure_polynomial.lean




## [2021-04-05 20:54:32](https://github.com/leanprover-community/mathlib/commit/1a45a56)
feat(logic/basic): subsingleton_of_not_nonempty ([#7043](https://github.com/leanprover-community/mathlib/pull/7043))
Also generalize `not_nonempty_iff_imp_false` to `Sort *`.
#### Estimated changes
Modified src/logic/basic.lean
- \+/\- *lemma* not_nonempty_iff_imp_false
- \+ *lemma* subsingleton_of_not_nonempty



## [2021-04-05 15:31:11](https://github.com/leanprover-community/mathlib/commit/04af8ba)
feat(logic/small): instances for Pi and sigma types ([#7042](https://github.com/leanprover-community/mathlib/pull/7042))
Add some instances to prove basic type formers preserve smallness.
#### Estimated changes
Modified src/logic/small.lean




## [2021-04-05 15:31:10](https://github.com/leanprover-community/mathlib/commit/e0e56ee)
feat(tactic/simps): trace with @[simps?] ([#6995](https://github.com/leanprover-community/mathlib/pull/6995))
also trace with initialize_simps_projections?
trace when to_additive is applied to generated lemmas
with @[simps?] projection information is not printed (since that is often not as useful)
#### Estimated changes
Modified src/tactic/simps.lean




## [2021-04-05 12:18:25](https://github.com/leanprover-community/mathlib/commit/5be4463)
fix(fintype/basic): typo in docstring ([#7041](https://github.com/leanprover-community/mathlib/pull/7041))
#### Estimated changes
Modified src/data/fintype/basic.lean




## [2021-04-05 05:18:28](https://github.com/leanprover-community/mathlib/commit/d36d766)
chore(scripts): update nolints.txt ([#7038](https://github.com/leanprover-community/mathlib/pull/7038))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-04-05 01:27:16](https://github.com/leanprover-community/mathlib/commit/530e7e3)
chore(data/quot): rename `nonempty_of_trunc` to enable dot notation ([#7034](https://github.com/leanprover-community/mathlib/pull/7034))
#### Estimated changes
Modified src/data/fintype/basic.lean


Modified src/data/quot.lean
- \- *theorem* nonempty_of_trunc

Modified src/data/set/countable.lean




## [2021-04-04 21:07:11](https://github.com/leanprover-community/mathlib/commit/c7d7d83)
chore(data/nat): use notation `n!`, minor golf ([#7032](https://github.com/leanprover-community/mathlib/pull/7032))
#### Estimated changes
Modified src/data/nat/choose/basic.lean
- \+/\- *lemma* nat.add_choose
- \+ *lemma* nat.add_choose_mul_factorial_mul_factorial

Modified src/data/nat/choose/sum.lean
- \+/\- *theorem* add_pow
- \+/\- *theorem* commute.add_pow

Modified src/data/nat/factorial.lean
- \+/\- *theorem* nat.factorial_le



## [2021-04-04 21:07:10](https://github.com/leanprover-community/mathlib/commit/92869e2)
chore(data/real/nnreal): use `function.injective.*` constructors ([#7028](https://github.com/leanprover-community/mathlib/pull/7028))
#### Estimated changes
Modified src/data/real/nnreal.lean




## [2021-04-04 14:00:36](https://github.com/leanprover-community/mathlib/commit/338331e)
feat(topology/urysohns_lemma): Urysohn's lemma ([#6967](https://github.com/leanprover-community/mathlib/pull/6967))
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* inv_of_le_one
- \+ *lemma* inv_of_lt_zero
- \+ *lemma* inv_of_nonneg
- \+ *lemma* inv_of_nonpos
- \+ *lemma* inv_of_pos

Modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* dist_midpoint_midpoint_le'
- \+ *lemma* dist_midpoint_midpoint_le
- \+ *lemma* filter.tendsto.line_map
- \+ *lemma* filter.tendsto.midpoint

Modified src/data/indicator_function.lean
- \+ *lemma* set.indicator_diff
- \+/\- *lemma* set.le_mul_indicator_apply
- \+/\- *lemma* set.mul_indicator_apply_le'
- \+/\- *lemma* set.mul_indicator_compl
- \+ *lemma* set.mul_indicator_diff

Modified src/linear_algebra/affine_space/midpoint.lean
- \+ *lemma* midpoint_eq_smul_add

Modified src/linear_algebra/affine_space/ordered.lean
- \+ *lemma* midpoint_le_midpoint

Modified src/topology/metric_space/basic.lean
- \+ *theorem* metric.nhds_basis_ball_pow
- \+ *theorem* metric.nhds_basis_closed_ball_pow
- \+ *theorem* metric.uniformity_basis_dist_le_pow
- \+ *theorem* metric.uniformity_basis_dist_pow
- \+ *theorem* real.dist_le_of_mem_Icc
- \+ *theorem* real.dist_le_of_mem_Icc_01
- \+ *theorem* real.dist_le_of_mem_interval
- \+ *theorem* real.dist_left_le_of_mem_interval
- \+ *theorem* real.dist_right_le_of_mem_interval

Added src/topology/urysohns_lemma.lean
- \+ *lemma* exists_continuous_zero_one_of_closed
- \+ *lemma* urysohns.CU.approx_le_approx_of_U_sub_C
- \+ *lemma* urysohns.CU.approx_le_lim
- \+ *lemma* urysohns.CU.approx_le_one
- \+ *lemma* urysohns.CU.approx_le_succ
- \+ *lemma* urysohns.CU.approx_mem_Icc_right_left
- \+ *lemma* urysohns.CU.approx_mono
- \+ *lemma* urysohns.CU.approx_nonneg
- \+ *lemma* urysohns.CU.approx_of_mem_C
- \+ *lemma* urysohns.CU.approx_of_nmem_U
- \+ *lemma* urysohns.CU.bdd_above_range_approx
- \+ *lemma* urysohns.CU.continuous_lim
- \+ *def* urysohns.CU.left
- \+ *lemma* urysohns.CU.left_U_subset
- \+ *lemma* urysohns.CU.left_U_subset_right_C
- \+ *lemma* urysohns.CU.lim_eq_midpoint
- \+ *lemma* urysohns.CU.lim_le_one
- \+ *lemma* urysohns.CU.lim_mem_Icc
- \+ *lemma* urysohns.CU.lim_nonneg
- \+ *lemma* urysohns.CU.lim_of_mem_C
- \+ *lemma* urysohns.CU.lim_of_nmem_U
- \+ *def* urysohns.CU.right
- \+ *lemma* urysohns.CU.subset_right_C
- \+ *lemma* urysohns.CU.tendsto_approx_at_top
- \+ *structure* urysohns.CU



## [2021-04-04 11:19:18](https://github.com/leanprover-community/mathlib/commit/ee58d66)
feat(topology): variations on the intermediate value theorem ([#6789](https://github.com/leanprover-community/mathlib/pull/6789))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.comap_coe_ne_bot_of_le_principal
- \+ *lemma* filter.eventually_comap'

Modified src/topology/algebra/ordered.lean
- \+ *lemma* eventually_ge_of_tendsto_gt
- \+ *lemma* eventually_le_of_tendsto_lt
- \+ *lemma* intermediate_value_Ico'
- \+ *lemma* intermediate_value_Ico
- \+ *lemma* intermediate_value_Ioc'
- \+ *lemma* intermediate_value_Ioc
- \+ *lemma* intermediate_value_Ioo'
- \+ *lemma* intermediate_value_Ioo
- \+ *lemma* intermediate_value_univ₂_eventually₁
- \+ *lemma* intermediate_value_univ₂_eventually₂
- \+ *lemma* is_preconnected.intermediate_value_Ici
- \+ *lemma* is_preconnected.intermediate_value_Ico
- \+ *lemma* is_preconnected.intermediate_value_Iic
- \+ *lemma* is_preconnected.intermediate_value_Iii
- \+ *lemma* is_preconnected.intermediate_value_Iio
- \+ *lemma* is_preconnected.intermediate_value_Ioc
- \+ *lemma* is_preconnected.intermediate_value_Ioi
- \+ *lemma* is_preconnected.intermediate_value_Ioo
- \+ *lemma* is_preconnected.intermediate_value₂_eventually₁
- \+ *lemma* is_preconnected.intermediate_value₂_eventually₂
- \+ *lemma* left_nhds_within_Ioc_ne_bot
- \+ *lemma* left_nhds_within_Ioo_ne_bot
- \+ *lemma* right_nhds_within_Ico_ne_bot
- \+ *lemma* right_nhds_within_Ioo_ne_bot



## [2021-04-04 06:41:15](https://github.com/leanprover-community/mathlib/commit/155b315)
chore(data/set/function): minor style fixes ([#7027](https://github.com/leanprover-community/mathlib/pull/7027))
#### Estimated changes
Modified src/data/set/function.lean
- \+/\- *lemma* set.inj_on_preimage
- \+/\- *theorem* set.left_inv_on.image_image'



## [2021-04-03 22:50:59](https://github.com/leanprover-community/mathlib/commit/44f34ee)
feat(group_theory/perm/sign): the alternating group ([#6913](https://github.com/leanprover-community/mathlib/pull/6913))
Defines `alternating_subgroup` to be `sign.ker`
Proves a few basic lemmas about its cardinality
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/group_theory/perm/sign.lean
- \+ *def* alternating_subgroup
- \+ *lemma* alternating_subgroup_eq_sign_ker
- \+ *lemma* alternating_subgroup_normal
- \+ *lemma* equiv.perm.closure_swaps_eq_top
- \+/\- *lemma* equiv.perm.sign_surjective
- \+ *lemma* mem_alternating_subgroup
- \+ *lemma* prod_list_swap_mem_alternating_subgroup_iff_even_length
- \+ *lemma* two_mul_card_alternating_subgroup

Modified src/group_theory/subgroup.lean




## [2021-04-03 16:38:16](https://github.com/leanprover-community/mathlib/commit/a5b7de0)
chore(linear_algebra): fix/add `coe_fn` simp lemmas ([#7015](https://github.com/leanprover-community/mathlib/pull/7015))
* move `@[simp]` from `linear_map.comp_apply` to new
  `linear_map.coe_comp`;
* rename `linear_map.comp_coe` to `linear_map.coe_comp`, swap LHS&RHS;
* add `linear_map.coe_proj`, move `@[simp]` from `linear_map.proj_apply`.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *lemma* linear_map.coe_comp
- \+/\- *lemma* linear_map.comp_apply
- \- *lemma* linear_map.comp_coe

Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/pi.lean
- \+ *lemma* linear_map.coe_proj
- \+/\- *lemma* linear_map.proj_apply



## [2021-04-03 14:32:04](https://github.com/leanprover-community/mathlib/commit/fc87598)
chore(data/polynomial/eval): add `map_ring_hom_{id,comp}` lemmas ([#7019](https://github.com/leanprover-community/mathlib/pull/7019))
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.map_ring_hom_comp
- \+ *lemma* polynomial.map_ring_hom_id



## [2021-04-03 11:15:54](https://github.com/leanprover-community/mathlib/commit/76a3b82)
feat(topology/sheaves/sheaf_condition): Sheaf condition in terms of unique gluing ([#6940](https://github.com/leanprover-community/mathlib/pull/6940))
As in
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Sheaf.20condition.20for.20type-valued.20sheaf
This PR adds an equivalent sheaf condition for type-valued presheaves, which is hopefully more "hands-on" and easier to work
with for concrete type-valued presheaves. I tried to roughly follow the design of the other sheaf conditions.
#### Estimated changes
Added src/topology/sheaves/sheaf_condition/unique_gluing.lean
- \+ *lemma* Top.presheaf.compatible_iff_left_res_eq_right_res
- \+ *def* Top.presheaf.gluing
- \+ *def* Top.presheaf.is_compatible
- \+ *def* Top.presheaf.is_gluing
- \+ *lemma* Top.presheaf.is_gluing_iff_eq_res
- \+ *def* Top.presheaf.pi_opens_iso_sections_family
- \+ *def* Top.presheaf.sheaf_condition_equiv_sheaf_condition_unique_gluing
- \+ *def* Top.presheaf.sheaf_condition_of_sheaf_condition_unique_gluing
- \+ *def* Top.presheaf.sheaf_condition_unique_gluing
- \+ *def* Top.presheaf.sheaf_condition_unique_gluing_of_sheaf_condition



## [2021-04-03 11:15:53](https://github.com/leanprover-community/mathlib/commit/0041898)
feat(category_theory/preadditive): single_obj α is preadditive when α is a ring ([#6884](https://github.com/leanprover-community/mathlib/pull/6884))
#### Estimated changes
Added src/category_theory/preadditive/single_obj.lean




## [2021-04-03 07:42:13](https://github.com/leanprover-community/mathlib/commit/51c9b60)
feat(category_theory/biproducts): additional lemmas ([#6881](https://github.com/leanprover-community/mathlib/pull/6881))
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.biproduct.components
- \+ *lemma* category_theory.limits.biproduct.components_matrix
- \+ *lemma* category_theory.limits.biproduct.lift_map
- \+ *lemma* category_theory.limits.biproduct.lift_matrix
- \+ *lemma* category_theory.limits.biproduct.map_desc
- \+ *def* category_theory.limits.biproduct.map_iso
- \+ *lemma* category_theory.limits.biproduct.map_matrix
- \+ *def* category_theory.limits.biproduct.matrix
- \+ *lemma* category_theory.limits.biproduct.matrix_components
- \+ *lemma* category_theory.limits.biproduct.matrix_desc
- \+ *def* category_theory.limits.biproduct.matrix_equiv
- \+ *lemma* category_theory.limits.biproduct.matrix_map
- \+ *lemma* category_theory.limits.biproduct.matrix_π
- \+ *lemma* category_theory.limits.biproduct.ι_matrix



## [2021-04-03 03:51:07](https://github.com/leanprover-community/mathlib/commit/6c59845)
doc(algebra/module/basic): update module doc ([#7009](https://github.com/leanprover-community/mathlib/pull/7009))
#### Estimated changes
Modified src/algebra/module/basic.lean




## [2021-04-03 03:51:06](https://github.com/leanprover-community/mathlib/commit/eedc9da)
chore(linear_algebra/basic, algebra/lie/basic): fix erroneous doc string, add notation comment ([#7005](https://github.com/leanprover-community/mathlib/pull/7005))
#### Estimated changes
Modified src/algebra/lie/basic.lean


Modified src/linear_algebra/basic.lean




## [2021-04-03 03:51:05](https://github.com/leanprover-community/mathlib/commit/b00d9be)
chore(data/finset/basic, ring_theory/hahn_series): mostly namespace changes ([#6996](https://github.com/leanprover-community/mathlib/pull/6996))
Added the line `open finset` and removed unneccesary `finset.`s from `ring_theory/hahn_series`
Added a small lemma to `data.finset.basic` that will be useful for an upcoming Hahn series PR
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.subset_bUnion_of_mem

Modified src/ring_theory/hahn_series.lean
- \+/\- *lemma* hahn_series.neg_coeff'
- \+/\- *lemma* hahn_series.neg_coeff
- \+/\- *lemma* hahn_series.sub_coeff'
- \+/\- *lemma* hahn_series.sub_coeff
- \+ *lemma* hahn_series.support_neg



## [2021-04-03 03:51:03](https://github.com/leanprover-community/mathlib/commit/b630c51)
feat(category_theory/kernels): mild generalization of lemma ([#6930](https://github.com/leanprover-community/mathlib/pull/6930))
Relaxes some `is_iso` assumptions to `mono` or `epi`.
I've also added some TODOs about related generalizations and instances which could be provided. I don't intend to get to them immediately.
#### Estimated changes
Modified src/algebra/homology/image_to_kernel_map.lean


Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.cokernel_epi_comp
- \- *def* category_theory.limits.cokernel_is_iso_comp
- \- *lemma* category_theory.limits.cokernel_π_comp_cokernel_comp_is_iso_hom
- \- *lemma* category_theory.limits.cokernel_π_comp_cokernel_comp_is_iso_inv
- \- *lemma* category_theory.limits.cokernel_π_comp_cokernel_is_iso_comp_hom
- \- *lemma* category_theory.limits.cokernel_π_comp_cokernel_is_iso_comp_inv
- \- *def* category_theory.limits.kernel_comp_is_iso
- \- *lemma* category_theory.limits.kernel_comp_is_iso_hom_comp_kernel_ι
- \- *lemma* category_theory.limits.kernel_comp_is_iso_inv_comp_kernel_ι
- \+ *def* category_theory.limits.kernel_comp_mono
- \- *lemma* category_theory.limits.kernel_is_iso_comp_hom_comp_kernel_ι
- \- *lemma* category_theory.limits.kernel_is_iso_comp_inv_comp_kernel_ι



## [2021-04-03 03:51:02](https://github.com/leanprover-community/mathlib/commit/9c6fe3c)
feat(linear_algebra/bilinear_form): Bilinear form restricted on a subspace is nondegenerate under some condition ([#6855](https://github.com/leanprover-community/mathlib/pull/6855))
The main result is `restrict_nondegenerate_iff_is_compl_orthogonal` which states that: a subspace is complement to its orthogonal complement with respect to some bilinear form if and only if that bilinear form restricted on to the subspace is nondegenerate.
To prove this, I also introduced `dual_annihilator_comap`. This is a definition that allows us to treat the dual annihilator of a dual annihilator as a subspace in the original space.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *def* linear_equiv.of_submodule'
- \+ *lemma* linear_equiv.of_submodule'_apply
- \+ *lemma* linear_equiv.of_submodule'_symm_apply
- \+ *lemma* linear_equiv.of_submodule'_to_linear_map
- \+ *def* submodule.equiv_subtype_map
- \+ *lemma* submodule.equiv_subtype_map_apply
- \+ *lemma* submodule.equiv_subtype_map_symm_apply

Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* bilin_form.findim_add_findim_orthogonal
- \+ *lemma* bilin_form.nondegenerate_restrict_of_disjoint_orthogonal
- \+ *theorem* bilin_form.restrict_nondegenerate_iff_is_compl_orthogonal
- \+ *lemma* bilin_form.restrict_nondegenerate_of_is_compl_orthogonal
- \+ *lemma* bilin_form.to_lin_restrict_ker_eq_inf_orthogonal
- \+ *lemma* bilin_form.to_lin_restrict_range_dual_annihilator_comap_eq_orthogonal

Modified src/linear_algebra/dual.lean
- \+ *def* submodule.dual_annihilator_comap
- \+ *lemma* submodule.mem_dual_annihilator_comap_iff
- \+ *lemma* subspace.findim_add_findim_dual_annihilator_comap_eq
- \+ *lemma* subspace.findim_dual_annihilator_comap_eq
- \+ *lemma* vector_space.eval_equiv_to_linear_map

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.findim_map_subtype_eq



## [2021-04-03 03:51:01](https://github.com/leanprover-community/mathlib/commit/2a9c21c)
feat(measure_theory/interval_integral): improve integral_comp lemmas ([#6795](https://github.com/leanprover-community/mathlib/pull/6795))
I expand our collection of `integral_comp` lemmas so that they can handle all interval integrals of the form
`∫ x in a..b, f (c * x + d)`, for any function `f : ℝ → E`  and any real constants `c` and `d` such that `c ≠ 0`.
This PR now also removes the `ae_measurable` assumptions from the preexisting `interval_comp` lemmas (thank you @sgouezel!).
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *lemma* equiv.coe_mul_left'
- \+ *lemma* equiv.coe_mul_right'
- \+ *lemma* equiv.mul_left'_symm_apply
- \+ *lemma* equiv.mul_right'_symm_apply

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.integral_map_of_closed_embedding

Modified src/measure_theory/borel_space.lean
- \+ *lemma* ae_measurable_comp_right_iff_of_closed_embedding
- \+ *lemma* closed_embedding.measurable
- \+ *lemma* homeomorph.measurable

Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integral.integral_comp_add_div
- \+ *lemma* interval_integral.integral_comp_add_mul
- \+/\- *lemma* interval_integral.integral_comp_add_right
- \+ *lemma* interval_integral.integral_comp_div
- \+ *lemma* interval_integral.integral_comp_div_add
- \+ *lemma* interval_integral.integral_comp_div_sub
- \+ *lemma* interval_integral.integral_comp_mul_add
- \+/\- *lemma* interval_integral.integral_comp_mul_left
- \+/\- *lemma* interval_integral.integral_comp_mul_right
- \+ *lemma* interval_integral.integral_comp_mul_right_of_neg
- \+ *lemma* interval_integral.integral_comp_mul_right_of_pos
- \+ *lemma* interval_integral.integral_comp_mul_sub
- \+/\- *lemma* interval_integral.integral_comp_neg
- \+ *lemma* interval_integral.integral_comp_sub_div
- \+ *lemma* interval_integral.integral_comp_sub_left
- \+ *lemma* interval_integral.integral_comp_sub_mul
- \+ *lemma* interval_integral.integral_comp_sub_right
- \+/\- *lemma* interval_integral.integral_congr

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.ae_map_mem_range
- \+ *lemma* measure_theory.ae_of_ae_map
- \+ *lemma* measure_theory.mem_ae_of_mem_ae_map

Modified src/measure_theory/set_integral.lean
- \+ *lemma* measure_theory.set_integral_map_of_closed_embedding

Modified src/topology/algebra/group_with_zero.lean
- \+ *lemma* homeomorph.coe_mul_left'
- \+ *lemma* homeomorph.coe_mul_right'
- \+ *lemma* homeomorph.mul_left'_symm_apply
- \+ *lemma* homeomorph.mul_right'_symm_apply



## [2021-04-02 21:56:53](https://github.com/leanprover-community/mathlib/commit/36e5ff4)
feat(category_theory/with_term): formally adjoin terminal / initial objects. ([#6966](https://github.com/leanprover-community/mathlib/pull/6966))
Adds the construction which formally adjoins a terminal resp. initial object to a category.
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* category_theory.limits.is_initial.of_iso
- \+ *def* category_theory.limits.is_terminal.of_iso

Added src/category_theory/with_terminal.lean
- \+ *def* category_theory.with_initial.comp
- \+ *def* category_theory.with_initial.hom
- \+ *def* category_theory.with_initial.hom_to
- \+ *def* category_theory.with_initial.id
- \+ *def* category_theory.with_initial.incl
- \+ *def* category_theory.with_initial.incl_lift
- \+ *def* category_theory.with_initial.incl_lift_to_initial
- \+ *def* category_theory.with_initial.lift
- \+ *def* category_theory.with_initial.lift_star
- \+ *lemma* category_theory.with_initial.lift_star_lift_map
- \+ *def* category_theory.with_initial.lift_to_initial
- \+ *def* category_theory.with_initial.lift_to_initial_unique
- \+ *def* category_theory.with_initial.lift_unique
- \+ *def* category_theory.with_initial.map
- \+ *def* category_theory.with_initial.star_initial
- \+ *inductive* category_theory.with_initial
- \+ *def* category_theory.with_terminal.comp
- \+ *def* category_theory.with_terminal.hom
- \+ *def* category_theory.with_terminal.hom_from
- \+ *def* category_theory.with_terminal.id
- \+ *def* category_theory.with_terminal.incl
- \+ *def* category_theory.with_terminal.incl_lift
- \+ *def* category_theory.with_terminal.incl_lift_to_terminal
- \+ *def* category_theory.with_terminal.lift
- \+ *lemma* category_theory.with_terminal.lift_map_lift_star
- \+ *def* category_theory.with_terminal.lift_star
- \+ *def* category_theory.with_terminal.lift_to_terminal
- \+ *def* category_theory.with_terminal.lift_to_terminal_unique
- \+ *def* category_theory.with_terminal.lift_unique
- \+ *def* category_theory.with_terminal.map
- \+ *def* category_theory.with_terminal.star_terminal
- \+ *inductive* category_theory.with_terminal



## [2021-04-02 21:56:51](https://github.com/leanprover-community/mathlib/commit/267e660)
refactor(algebra/add_torsor): use `to_additive` for `add_action` ([#6914](https://github.com/leanprover-community/mathlib/pull/6914))
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \- *lemma* vadd_assoc
- \- *lemma* vadd_comm
- \- *lemma* vadd_eq_add
- \- *lemma* vadd_left_cancel
- \- *lemma* vadd_left_cancel_iff
- \- *lemma* vadd_left_injective
- \- *lemma* zero_vadd

Modified src/algebra/group/to_additive.lean


Modified src/algebra/module/prod.lean
- \- *theorem* prod.smul_fst
- \- *theorem* prod.smul_mk
- \- *theorem* prod.smul_snd

Modified src/group_theory/group_action/defs.lean
- \+/\- *def* const_smul_hom
- \+/\- *lemma* const_smul_hom_apply
- \+/\- *def* distrib_mul_action.comp_hom
- \+/\- *lemma* ite_smul
- \+/\- *def* mul_action.comp_hom
- \+/\- *def* mul_action.to_fun
- \+/\- *lemma* mul_action.to_fun_apply
- \+/\- *theorem* one_smul
- \+/\- *theorem* smul_add
- \+/\- *lemma* smul_comm_class.symm
- \+/\- *lemma* smul_eq_mul
- \+/\- *lemma* smul_ite
- \+/\- *theorem* smul_neg
- \+/\- *lemma* smul_smul
- \+/\- *theorem* smul_sub
- \+/\- *theorem* smul_zero

Modified src/group_theory/group_action/group.lean
- \+ *def* add_units.vadd_perm_hom
- \+/\- *lemma* eq_inv_smul_iff
- \+/\- *lemma* inv_smul_eq_iff
- \+/\- *lemma* inv_smul_smul
- \+/\- *lemma* is_unit.smul_left_cancel
- \+/\- *lemma* smul_inv_smul
- \+ *lemma* smul_left_cancel
- \+ *lemma* smul_left_cancel_iff
- \+/\- *lemma* units.inv_smul_smul
- \+/\- *lemma* units.smul_eq_iff_eq_inv_smul
- \+/\- *lemma* units.smul_inv_smul
- \+/\- *lemma* units.smul_left_cancel
- \+ *def* units.smul_perm

Added src/group_theory/group_action/prod.lean
- \+ *theorem* prod.smul_fst
- \+ *theorem* prod.smul_mk
- \+ *theorem* prod.smul_snd

Modified src/linear_algebra/affine_space/affine_equiv.lean


Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/linear_algebra/affine_space/affine_subspace.lean


Modified src/linear_algebra/affine_space/combination.lean


Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/affine_space/midpoint.lean




## [2021-04-02 21:56:50](https://github.com/leanprover-community/mathlib/commit/278ad33)
refactor(topology/metric_space/isometry): generalize to pseudo_metric ([#6910](https://github.com/leanprover-community/mathlib/pull/6910))
This is part of a series of PR to have the theory of `semi_normed_group` (and related concepts) in mathlib.
We generalize here `isometry` to `pseudo_emetric_space` and `pseudo_metric_space`.
#### Estimated changes
Modified src/analysis/normed_space/dual.lean


Modified src/topology/metric_space/isometry.lean
- \+/\- *lemma* algebra_map_isometry
- \+/\- *def* isometric.mk'
- \+/\- *structure* isometric
- \+/\- *theorem* isometry.closed_embedding
- \+/\- *lemma* isometry.comp_continuous_iff
- \+/\- *lemma* isometry.comp_continuous_on_iff
- \+/\- *lemma* isometry.diam_image
- \+/\- *lemma* isometry.diam_range
- \+/\- *theorem* isometry.dist_eq
- \+/\- *theorem* isometry.edist_eq
- \+/\- *lemma* isometry.injective
- \+/\- *def* isometry.isometric_on_range
- \+/\- *lemma* isometry.isometric_on_range_apply
- \+/\- *theorem* isometry.uniform_embedding
- \+/\- *def* isometry
- \+/\- *lemma* isometry_emetric_iff_metric



## [2021-04-02 21:56:49](https://github.com/leanprover-community/mathlib/commit/cb1e888)
feat(category_theory/limits): is_iso_π_of_is_initial ([#6908](https://github.com/leanprover-community/mathlib/pull/6908))
From [zulip](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/Simplicial.20stuff/near/231346653)
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean
- \+ *lemma* category_theory.limits.initial.to_comp
- \+ *lemma* category_theory.limits.is_initial.to_comp
- \+ *lemma* category_theory.limits.is_initial.to_self
- \+ *lemma* category_theory.limits.is_iso_ι_of_is_terminal
- \+ *lemma* category_theory.limits.is_iso_π_of_is_initial
- \+ *lemma* category_theory.limits.is_terminal.comp_from
- \+ *lemma* category_theory.limits.is_terminal.from_self
- \+ *lemma* category_theory.limits.terminal.comp_from



## [2021-04-02 21:56:48](https://github.com/leanprover-community/mathlib/commit/fe4ea3d)
chore(docs/undergrad.yaml): a few updates to the undergrad list ([#6904](https://github.com/leanprover-community/mathlib/pull/6904))
Adds entries for Schur's Lemma and several infinite series concepts
#### Estimated changes
Modified docs/undergrad.yaml




## [2021-04-02 21:56:47](https://github.com/leanprover-community/mathlib/commit/7b52617)
feat(data/nat/multiplicity): weaken hypothesis on set bounds ([#6903](https://github.com/leanprover-community/mathlib/pull/6903))
#### Estimated changes
Modified src/data/nat/multiplicity.lean
- \+/\- *lemma* nat.multiplicity_eq_card_pow_dvd
- \+/\- *lemma* nat.prime.multiplicity_choose
- \+/\- *lemma* nat.prime.pow_dvd_factorial_iff



## [2021-04-02 16:17:31](https://github.com/leanprover-community/mathlib/commit/fead60f)
chore(data/finsupp/basic): add a lemma for `map_domain` applied to equivs ([#7001](https://github.com/leanprover-community/mathlib/pull/7001))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.map_domain_equiv_apply



## [2021-04-02 09:16:15](https://github.com/leanprover-community/mathlib/commit/394719f)
chore(data/finsupp): lemmas about map_range and map_domain ([#6976](https://github.com/leanprover-community/mathlib/pull/6976))
This proves some functorial properties:
* `finsupp.map_range_id`
* `finsupp.map_range_comp`
Adds the new definitions to match `finsupp.map_range.add_monoid_hom`, and uses them to golf some proofs:
* `finsupp.map_range.zero_hom`, which is `map_domain` as a `zero_hom`
* `finsupp.map_range.add_equiv`, which is `map_range` as an `add_equiv`
* `finsupp.map_range.linear_map`, which is `map_range` as a `linear_map`
* `finsupp.map_range.linear_equiv`, which is `map_range` as a `linear_equiv`
* `finsupp.map_domain.add_monoid_hom`, which is `map_domain` as an `add_monoid_hom`
Shows the functorial properties of these bundled definitions:
* `finsupp.map_range.zero_hom_id`, `finsupp.map_range.zero_hom_comp`
* `finsupp.map_range.add_monoid_hom_id`, `finsupp.map_range.add_monoid_hom_comp`
* `finsupp.map_range.add_equiv_refl`, `finsupp.map_range.add_equiv_trans`
* `finsupp.map_range.linear_map_id`, `finsupp.map_range.linear_map_comp`
* `finsupp.map_range.linear_equiv_refl`, `finsupp.map_range.linear_equiv_trans`
* `finsupp.map_domain.add_monoid_hom_id`, `finsupp.map_domain.add_monoid_hom_comp`
And shows that `map_range` and `map_domain` commute when the range-map preserves addition:
* `finsupp.map_domain_map_range`
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.dom_congr_symm
- \+ *def* finsupp.map_domain.add_monoid_hom
- \+ *lemma* finsupp.map_domain.add_monoid_hom_comp
- \+ *lemma* finsupp.map_domain.add_monoid_hom_comp_map_range
- \+ *lemma* finsupp.map_domain.add_monoid_hom_id
- \+ *lemma* finsupp.map_domain_map_range
- \+ *def* finsupp.map_range.add_equiv
- \+ *lemma* finsupp.map_range.add_equiv_refl
- \+ *lemma* finsupp.map_range.add_equiv_symm
- \+ *lemma* finsupp.map_range.add_equiv_trans
- \+/\- *def* finsupp.map_range.add_monoid_hom
- \+ *lemma* finsupp.map_range.add_monoid_hom_comp
- \+ *lemma* finsupp.map_range.add_monoid_hom_id
- \+ *def* finsupp.map_range.zero_hom
- \+ *lemma* finsupp.map_range.zero_hom_comp
- \+ *lemma* finsupp.map_range.zero_hom_id
- \+ *lemma* finsupp.map_range_comp
- \+/\- *lemma* finsupp.map_range_finset_sum
- \+ *lemma* finsupp.map_range_id
- \+/\- *lemma* finsupp.map_range_multiset_sum
- \+ *lemma* finsupp.map_range_smul

Modified src/linear_algebra/finsupp.lean
- \+ *def* finsupp.map_range.linear_equiv
- \+ *lemma* finsupp.map_range.linear_equiv_refl
- \+ *lemma* finsupp.map_range.linear_equiv_symm
- \+ *lemma* finsupp.map_range.linear_equiv_trans
- \+ *def* finsupp.map_range.linear_map
- \+ *lemma* finsupp.map_range.linear_map_comp
- \+ *lemma* finsupp.map_range.linear_map_id



## [2021-04-02 08:15:10](https://github.com/leanprover-community/mathlib/commit/6e5c07b)
feat(category_theory/subobject): well-powered categories ([#6802](https://github.com/leanprover-community/mathlib/pull/6802))
#### Estimated changes
Modified src/category_theory/subobject/default.lean


Added src/category_theory/subobject/well_powered.lean
- \+ *theorem* category_theory.essentially_small_mono_over_iff_small_subobject
- \+ *theorem* category_theory.well_powered_of_essentially_small_mono_over



## [2021-04-02 04:59:38](https://github.com/leanprover-community/mathlib/commit/19483ae)
feat(data/finset): inj on of image card eq ([#6785](https://github.com/leanprover-community/mathlib/pull/6785))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* finset.card_image_eq_iff_inj_on
- \+/\- *theorem* finset.image_val_of_inj_on
- \+ *theorem* finset.inj_on_of_card_image_eq

Modified src/data/list/nodup.lean
- \+ *theorem* list.inj_on_of_nodup_map
- \+ *theorem* list.nodup_map_iff_inj_on

Modified src/data/multiset/nodup.lean
- \+ *theorem* multiset.inj_on_of_nodup_map
- \+ *theorem* multiset.nodup_map_iff_inj_on



## [2021-04-02 01:20:16](https://github.com/leanprover-community/mathlib/commit/7337702)
feat(data/equiv/fintype): computable bijections and perms from/to fintype ([#6959](https://github.com/leanprover-community/mathlib/pull/6959))
Using exhaustive search, we can upgrade embeddings from fintypes into
equivs, and transport perms across embeddings. The computational
performance is poor, so the docstring suggests alternatives when an
explicit inverse is known.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *theorem* equiv.apply_of_injective_symm
- \+ *def* equiv.perm.extend_domain
- \+ *lemma* equiv.perm.extend_domain_apply_image
- \+ *lemma* equiv.perm.extend_domain_apply_not_subtype
- \+ *lemma* equiv.perm.extend_domain_apply_subtype
- \+ *lemma* equiv.perm.extend_domain_refl
- \+ *lemma* equiv.perm.extend_domain_symm
- \+ *lemma* equiv.perm.extend_domain_trans

Added src/data/equiv/fintype.lean
- \+ *def* equiv.perm.via_embedding
- \+ *lemma* equiv.perm.via_embedding_apply_image
- \+ *lemma* equiv.perm.via_embedding_apply_mem_range
- \+ *lemma* equiv.perm.via_embedding_apply_not_mem_range
- \+ *lemma* equiv.perm.via_embedding_sign
- \+ *def* function.embedding.to_equiv_range
- \+ *lemma* function.embedding.to_equiv_range_apply
- \+ *lemma* function.embedding.to_equiv_range_eq_of_injective
- \+ *lemma* function.embedding.to_equiv_range_symm_apply_self

Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.perm.extend_domain_inv
- \+ *lemma* equiv.perm.extend_domain_mul
- \+ *lemma* equiv.perm.extend_domain_one

Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.sign_extend_domain



## [2021-04-01 18:49:17](https://github.com/leanprover-community/mathlib/commit/d8de567)
feat(group_theory/order_of_element): generalised to add_order_of ([#6770](https://github.com/leanprover-community/mathlib/pull/6770))
This PR defines `add_order_of` for an additive monoid. If someone sees how to do this with more automation, let me know. 
This gets one step towards closing issue [#1563](https://github.com/leanprover-community/mathlib/pull/1563).
Coauthored by: Yakov Pechersky @pechersky
#### Estimated changes
Modified src/algebra/group/type_tags.lean
- \+ *lemma* of_add_eq_one
- \+ *lemma* of_mul_eq_zero

Modified src/algebra/group_power/basic.lean
- \+ *lemma* of_mul_gpow
- \+ *lemma* of_mul_pow

Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.eq_image_iff_symm_image_eq

Modified src/data/int/gcd.lean
- \+ *lemma* gcd_nsmul_eq_zero

Modified src/group_theory/order_of_element.lean
- \+ *lemma* add_order_eq_card_gmultiples
- \+ *lemma* add_order_of_dvd_card_univ
- \+ *lemma* add_order_of_dvd_iff_nsmul_eq_zero
- \+ *lemma* add_order_of_dvd_of_nsmul_eq_zero
- \+ *lemma* add_order_of_eq_add_order_of_iff
- \+ *lemma* add_order_of_eq_card_multiples
- \+ *lemma* add_order_of_eq_one_iff
- \+ *lemma* add_order_of_eq_prime
- \+ *lemma* add_order_of_eq_prime_pow
- \+ *lemma* add_order_of_eq_zero
- \+ *lemma* add_order_of_injective
- \+ *lemma* add_order_of_le_card_univ
- \+ *lemma* add_order_of_le_of_nsmul_eq_zero'
- \+ *lemma* add_order_of_le_of_nsmul_eq_zero
- \+ *lemma* add_order_of_nsmul''
- \+ *lemma* add_order_of_nsmul'
- \+ *lemma* add_order_of_nsmul
- \+ *lemma* add_order_of_nsmul_eq_zero
- \+ *lemma* add_order_of_of_mul_eq_order_of
- \+ *lemma* add_order_of_pos'
- \+ *lemma* add_order_of_pos
- \+ *lemma* add_order_of_zero
- \+ *lemma* card_nsmul_eq_zero
- \+ *lemma* exists_gsmul_eq_zero
- \+ *lemma* exists_nsmul_eq_self_of_coprime
- \+ *lemma* exists_nsmul_eq_zero
- \+ *lemma* gcd_nsmul_card_eq_zero_iff
- \+ *lemma* gsmul_eq_mod_add_order_of
- \+ *lemma* image_range_add_order_of
- \+ *lemma* mem_gmultiples_iff_mem_range_add_order_of
- \+ *lemma* mem_multiples_iff_mem_gmultiples
- \+ *lemma* mem_multiples_iff_mem_range_add_order_of
- \+ *lemma* multiples_eq_gmultiples
- \+ *lemma* nsmul_eq_mod_add_order_of
- \+ *lemma* nsmul_injective_aux
- \+ *lemma* nsmul_injective_of_lt_add_order_of
- \+/\- *lemma* order_of_eq_prime_pow
- \+/\- *lemma* order_of_le_card_univ
- \+ *lemma* order_of_of_add_eq_add_order_of
- \+/\- *lemma* order_of_pos
- \+/\- *lemma* order_of_subgroup
- \+/\- *lemma* order_of_submonoid
- \+ *lemma* pow_injective_aux
- \+ *lemma* sum_card_add_order_of_eq_card_nsmul_eq_zero

Modified src/group_theory/subgroup.lean
- \+ *lemma* of_add_image_gmultiples_eq_gpowers_of_add
- \+ *lemma* of_mul_image_gpowers_eq_gmultiples_of_mul

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* of_add_image_multiples_eq_powers_of_add
- \+ *lemma* of_mul_image_powers_eq_multiples_of_mul



## [2021-04-01 17:47:25](https://github.com/leanprover-community/mathlib/commit/1e27fba)
admin(README.md): add @adamtopaz to the maintainers list ([#6987](https://github.com/leanprover-community/mathlib/pull/6987))
#### Estimated changes
Modified README.md




## [2021-04-01 17:47:24](https://github.com/leanprover-community/mathlib/commit/c35e9f6)
admin(README.md): add @b-mehta to the maintainers list ([#6986](https://github.com/leanprover-community/mathlib/pull/6986))
#### Estimated changes
Modified README.md




## [2021-04-01 17:47:23](https://github.com/leanprover-community/mathlib/commit/cea8c65)
feat(algebra/char_p/exp_char): basics about the exponential characteristic ([#6671](https://github.com/leanprover-community/mathlib/pull/6671))
This file contains the definition and a few basic facts pertaining to the exponential characteristic of an integral domain.
#### Estimated changes
Added src/algebra/char_p/exp_char.lean
- \+ *theorem* char_eq_exp_char_iff
- \+ *lemma* char_prime_of_ne_zero
- \+ *lemma* char_zero_of_exp_char_one
- \+ *theorem* exp_char_is_prime_or_one
- \+ *theorem* exp_char_one_iff_char_zero
- \+ *lemma* exp_char_one_of_char_zero



## [2021-04-01 15:06:29](https://github.com/leanprover-community/mathlib/commit/396602b)
feat(algebra/module/hom): Add missing smul instances on add_monoid_hom ([#6891](https://github.com/leanprover-community/mathlib/pull/6891))
These are defeq to the smul instances on `linear_map`, in `linear_algebra/basic.lean`.
#### Estimated changes
Added src/algebra/module/hom.lean
- \+ *lemma* add_monoid_hom.coe_smul
- \+ *lemma* add_monoid_hom.smul_apply

Modified src/linear_algebra/basic.lean




## [2021-04-01 13:55:22](https://github.com/leanprover-community/mathlib/commit/a690ce7)
admin(README.md): add @TwoFX to the maintainers list ([#6985](https://github.com/leanprover-community/mathlib/pull/6985))
#### Estimated changes
Modified README.md




## [2021-04-01 12:44:31](https://github.com/leanprover-community/mathlib/commit/132ae2b)
fix(algebraic_topology): fix a typo ([#6991](https://github.com/leanprover-community/mathlib/pull/6991))
#### Estimated changes
Modified src/algebraic_topology/simplicial_set.lean




## [2021-04-01 09:03:10](https://github.com/leanprover-community/mathlib/commit/a9b6230)
feat(combinatorics/quiver): weakly connected components ([#6847](https://github.com/leanprover-community/mathlib/pull/6847))
Define composition of paths and the weakly connected components of a directed graph. Two vertices are in the same weakly connected component if there is a zigzag of arrows from one to the other.
#### Estimated changes
Modified src/combinatorics/quiver.lean
- \+ *def* quiver.arrow.reverse
- \+ *def* quiver.arrow.to_path
- \+ *def* quiver.path.comp
- \+ *lemma* quiver.path.comp_assoc
- \+ *lemma* quiver.path.comp_cons
- \+ *lemma* quiver.path.comp_nil
- \+/\- *def* quiver.path.length
- \+/\- *lemma* quiver.path.length_cons
- \+/\- *lemma* quiver.path.length_nil
- \+ *lemma* quiver.path.nil_comp
- \+ *def* quiver.path.reverse
- \+ *def* quiver.weakly_connected_component
- \+ *def* quiver.zigzag_setoid



## [2021-04-01 05:03:20](https://github.com/leanprover-community/mathlib/commit/21cc806)
feat(data/equiv/basic): `perm_congr` group lemmas ([#6982](https://github.com/leanprover-community/mathlib/pull/6982))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.perm_congr
- \+/\- *lemma* equiv.perm_congr_apply
- \+/\- *lemma* equiv.perm_congr_def
- \+ *lemma* equiv.perm_congr_refl
- \+/\- *lemma* equiv.perm_congr_symm
- \+/\- *lemma* equiv.perm_congr_symm_apply
- \+ *lemma* equiv.perm_congr_trans

Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.perm.perm_congr_eq_mul



## [2021-04-01 01:24:57](https://github.com/leanprover-community/mathlib/commit/3365c44)
feat(data/equiv/basic): `equiv.swap_eq_refl_iff` ([#6983](https://github.com/leanprover-community/mathlib/pull/6983))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.swap_eq_refl_iff

Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.swap_eq_one_iff



## [2021-04-01 01:24:56](https://github.com/leanprover-community/mathlib/commit/64abe48)
refactor(topology/metric_space/pi_Lp): generalize to pseudo_metric ([#6978](https://github.com/leanprover-community/mathlib/pull/6978))
We generalize here the Lp distance to `pseudo_emetric` and similar concepts.
#### Estimated changes
Modified src/topology/metric_space/pi_Lp.lean
- \+/\- *lemma* pi_Lp.lipschitz_with_equiv
- \+/\- *lemma* pi_Lp.norm_eq
- \+/\- *lemma* pi_Lp.norm_eq_of_nat
- \+ *def* pi_Lp.pseudo_emetric_aux



## [2021-04-01 01:24:55](https://github.com/leanprover-community/mathlib/commit/b7fbc17)
chore(data/equiv/add_equiv): missing simp lemmas ([#6975](https://github.com/leanprover-community/mathlib/pull/6975))
These lemmas already exist for `equiv`, this just copies them to `add_equiv`.
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *theorem* mul_equiv.coe_refl
- \+ *theorem* mul_equiv.coe_trans
- \+ *theorem* mul_equiv.self_comp_symm
- \+ *theorem* mul_equiv.symm_comp_self



## [2021-04-01 01:24:54](https://github.com/leanprover-community/mathlib/commit/e540c2f)
feat(data/set/basic): default_coe_singleton ([#6971](https://github.com/leanprover-community/mathlib/pull/6971))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.default_coe_singleton



## [2021-04-01 01:24:53](https://github.com/leanprover-community/mathlib/commit/ec9476f)
chore(data/fintype/basic): add card_le_of_surjective and card_quotient_le ([#6964](https://github.com/leanprover-community/mathlib/pull/6964))
Add two natural lemmas that were missing from `fintype.basic`.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_le_of_surjective
- \+ *lemma* fintype.card_lt_of_surjective_not_injective
- \+ *theorem* fintype.card_quotient_le
- \+ *theorem* fintype.card_quotient_lt



## [2021-04-01 01:24:52](https://github.com/leanprover-community/mathlib/commit/71c3e71)
refactor(topology/bases): use `structure` for `is_topological_basis ([#6947](https://github.com/leanprover-community/mathlib/pull/6947))
* turn `topological_space.is_topological_basis` into a `structure`;
* rename `mem_nhds_of_is_topological_basis` to `is_topological_basis.mem_nhds_iff`;
* rename `is_open_of_is_topological_basis` to `is_topological_basis.is_open`;
* rename `mem_basis_subset_of_mem_open` to `is_topological_basis.exists_subset_of_mem_open`;
* rename `sUnion_basis_of_is_open` to `is_topological_basis.open_eq_sUnion`, add prime version;
* add `is_topological_basis.prod`;
* add convenience lemma `is_topological_basis.second_countable_topology`;
* rename `is_open_generated_countable_inter` to `exists_countable_basis`;
* add `topological_space.countable_basis` and API around it;
* add `@[simp]` to `opens.mem_supr`, add `opens.mem_Sup`;
* golf
#### Estimated changes
Modified src/data/analysis/topology.lean


Modified src/data/set/basic.lean


Modified src/dynamics/ergodic/conservative.lean


Modified src/measure_theory/borel_space.lean
- \+ *lemma* topological_space.is_topological_basis.borel_eq_generate_from

Modified src/topology/bases.lean
- \- *lemma* topological_space.Union_basis_of_is_open
- \+ *def* topological_space.countable_basis
- \+ *lemma* topological_space.countable_countable_basis
- \+ *lemma* topological_space.empty_nmem_countable_basis
- \+ *lemma* topological_space.eq_generate_from_countable_basis
- \+ *lemma* topological_space.exists_countable_basis
- \+ *lemma* topological_space.is_basis_countable_basis
- \- *lemma* topological_space.is_open_generated_countable_inter
- \- *lemma* topological_space.is_open_of_is_topological_basis
- \+ *lemma* topological_space.is_open_of_mem_countable_basis
- \+ *lemma* topological_space.is_topological_basis.exists_subset_of_mem_open
- \+ *lemma* topological_space.is_topological_basis.mem_nhds_iff
- \+ *lemma* topological_space.is_topological_basis.open_eq_Union
- \+ *lemma* topological_space.is_topological_basis.open_eq_sUnion'
- \+ *lemma* topological_space.is_topological_basis.open_eq_sUnion
- \+ *structure* topological_space.is_topological_basis
- \- *def* topological_space.is_topological_basis
- \- *lemma* topological_space.mem_basis_subset_of_mem_open
- \- *lemma* topological_space.mem_nhds_of_is_topological_basis
- \+ *lemma* topological_space.nonempty_of_mem_countable_basis
- \- *lemma* topological_space.sUnion_basis_of_is_open

Modified src/topology/opens.lean
- \+ *lemma* topological_space.opens.mem_Sup
- \+/\- *theorem* topological_space.opens.mem_supr

Modified src/topology/stone_cech.lean


Modified src/topology/uniform_space/cauchy.lean


