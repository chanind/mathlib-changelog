### [2020-11-30 18:13:09](https://github.com/leanprover-community/mathlib/commit/c3f4d1b)
refactor(combinatorics/simple_graph): move simple graph files to their own folder ([#5154](https://github.com/leanprover-community/mathlib/pull/5154))
Move the files into one folder with the goal of integrating material from the branch [simple_graphs2](https://github.com/leanprover-community/mathlib/tree/simple_graphs2)

### [2020-11-30 12:04:56](https://github.com/leanprover-community/mathlib/commit/e3a699e)
feat(linear_algebra/determinant): Show that the determinant is a multilinear map ([#5142](https://github.com/leanprover-community/mathlib/pull/5142))

### [2020-11-30 10:52:36](https://github.com/leanprover-community/mathlib/commit/9f955fe)
feat(ring_theory/integral_closure): Cleanup interface for ring_hom.is_integral ([#5144](https://github.com/leanprover-community/mathlib/pull/5144))

### [2020-11-29 02:33:01](https://github.com/leanprover-community/mathlib/commit/1f1ba58)
feat(category_theory/limits): reflexive coequalizers ([#5123](https://github.com/leanprover-community/mathlib/pull/5123))
Adds reflexive coequalizers. These are useful for [#5118](https://github.com/leanprover-community/mathlib/pull/5118) as well as for some monadicity theorems and other results.

### [2020-11-29 01:19:16](https://github.com/leanprover-community/mathlib/commit/5866812)
chore(scripts): update nolints.txt ([#5143](https://github.com/leanprover-community/mathlib/pull/5143))
I am happy to remove some nolints for you!

### [2020-11-28 21:16:44](https://github.com/leanprover-community/mathlib/commit/fe7b407)
feat(tactic/explode): display exploded proofs as widgets ([#4718](https://github.com/leanprover-community/mathlib/pull/4718))
[#4094](https://github.com/leanprover-community/mathlib/pull/4094). This is a more advanced version of the expandable `#explode` diagram implemented in the [Mathematica-Lean Link](http://robertylewis.com/leanmm/lean_mm.pdf). The widget adds features such as jumping to definitions and exploding constants occurring in a proof term subsequently. Note that right now the [\<details\>](https://developer.mozilla.org/en-US/docs/Web/HTML/Element/details) tag simply hides the information. "Exploding on request" requires a bit more refactoring on `#explode` itself and is still on the way. 
Example usage:`#explode_widget iff_true_intro`. 
![explode_widget](https://user-images.githubusercontent.com/22624072/96630999-7cb62780-1361-11eb-977d-3eb34039ab41.png)

### [2020-11-28 19:38:23](https://github.com/leanprover-community/mathlib/commit/ec82227)
chore(group_theory/perm/sign): Add swap_mul_involutive ([#5141](https://github.com/leanprover-community/mathlib/pull/5141))
This is just a bundled version of swap_mul_self_mul

### [2020-11-28 17:42:18](https://github.com/leanprover-community/mathlib/commit/916bf74)
feat(category_theory/limits): images, equalizers and pullbacks imply functorial images ([#5140](https://github.com/leanprover-community/mathlib/pull/5140))

### [2020-11-28 17:42:16](https://github.com/leanprover-community/mathlib/commit/b1d8b89)
chore(algebra/char_p): refactor char_p ([#5132](https://github.com/leanprover-community/mathlib/pull/5132))

### [2020-11-28 16:26:44](https://github.com/leanprover-community/mathlib/commit/137163a)
feat(analysis/normed_space/dual): Fréchet-Riesz representation for the dual of a Hilbert space ([#4379](https://github.com/leanprover-community/mathlib/pull/4379))
This PR defines `to_dual` which maps an element `x` of an inner product space to `λ y, ⟪x, y⟫`. We also give the Fréchet-Riesz representation, which states that every element of the dual of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`.

### [2020-11-28 01:26:41](https://github.com/leanprover-community/mathlib/commit/801dea9)
chore(scripts): update nolints.txt ([#5139](https://github.com/leanprover-community/mathlib/pull/5139))
I am happy to remove some nolints for you!

### [2020-11-27 23:09:55](https://github.com/leanprover-community/mathlib/commit/ba43f6f)
doc(field_theory/finite/basic): update doc-strings ([#5134](https://github.com/leanprover-community/mathlib/pull/5134))
The documentation mentions `finite_field.is_cyclic` that does not exist (probably replaced by `subgroup_units_cyclic` in `ring_theory.integral_domain`).

### [2020-11-27 23:09:53](https://github.com/leanprover-community/mathlib/commit/b6f2309)
chore({ring,group}_theory/free_*): Add of_injective ([#5131](https://github.com/leanprover-community/mathlib/pull/5131))
This adds:
* `free_abelian_group.of_injective`
* `free_ring.of_injective`
* `free_comm_ring.of_injective`
* `free_algebra.of_injective`
following up from dcbec39a5bf9af5c6e065eea185f8776ac537d3b

### [2020-11-27 21:26:04](https://github.com/leanprover-community/mathlib/commit/4a153ed)
feat(ring_theory/polynomials/cyclotomic): add lemmas about cyclotomic polynomials ([#5122](https://github.com/leanprover-community/mathlib/pull/5122))
Two lemmas about cyclotomic polynomials:
`cyclotomic_of_prime` is the explicit formula for `cyclotomic p R` when `p` is prime;
`cyclotomic_coeff_zero` shows that the constant term of `cyclotomic n R` is `1` if `2 ≤ n`. I will use this to prove that there are infinitely many prime congruent to `1` modulo `n`, for all `n`.

### [2020-11-27 21:26:02](https://github.com/leanprover-community/mathlib/commit/14f2096)
feat(ring_theory/jacobson): generalized nullstellensatz - polynomials over a Jacobson ring are Jacobson ([#4962](https://github.com/leanprover-community/mathlib/pull/4962))
The main statements are `is_jacobson_polynomial_iff_is_jacobson ` and `is_jacobson_mv_polynomial`, saying that `polynomial` and `mv_polynomial` both preserve jacobson property of rings. 
This second statement is in some sense a general form of the classical nullstellensatz, since in a Jacobson ring the intersection of maximal ideals containing an ideal will be exactly the radical of that ideal (and so I(V(I)) = I.radical).

### [2020-11-27 18:30:26](https://github.com/leanprover-community/mathlib/commit/8d3e93f)
chore(category_theory/limits): golf a proof ([#5133](https://github.com/leanprover-community/mathlib/pull/5133))

### [2020-11-27 18:30:24](https://github.com/leanprover-community/mathlib/commit/fb70419)
feat(algebra/group/basic): simplify composed assoc ops ([#5031](https://github.com/leanprover-community/mathlib/pull/5031))
New lemmas:
`comp_assoc_left`
`comp_assoc_right`
`comp_mul_left`
`comp_add_left`
`comp_mul_right`
`comp_add_right`

### [2020-11-27 18:30:22](https://github.com/leanprover-community/mathlib/commit/73a2fd3)
feat(ring_theory/witt_vector/init_tail): adding disjoint witt vectors ([#4835](https://github.com/leanprover-community/mathlib/pull/4835))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-11-27 15:35:32](https://github.com/leanprover-community/mathlib/commit/396487f)
feat(topology/separation): Adds t2_space instances for disjoint unions (sums and sigma types). ([#5113](https://github.com/leanprover-community/mathlib/pull/5113))

### [2020-11-27 14:25:59](https://github.com/leanprover-community/mathlib/commit/876481e)
feat(field_theory/separable): add separable_of_X_pow_sub_C and squarefree_of_X_pow_sub_C ([#5052](https://github.com/leanprover-community/mathlib/pull/5052))
I've added that `X ^ n - a` is separable, and so `squarefree`.

### [2020-11-27 14:25:57](https://github.com/leanprover-community/mathlib/commit/c82b708)
feat(category_theory/sites): the canonical topology on a category ([#4928](https://github.com/leanprover-community/mathlib/pull/4928))
Explicitly construct the finest topology for which the given presheaves are sheaves, and specialise to construct the canonical topology. 
Also one or two tiny changes which should have been there before

### [2020-11-27 11:58:59](https://github.com/leanprover-community/mathlib/commit/0ac414a)
feat(data/fin): Add pred_{le,lt}_pred_iff ([#5121](https://github.com/leanprover-community/mathlib/pull/5121))

### [2020-11-27 11:58:57](https://github.com/leanprover-community/mathlib/commit/8acd296)
chore(topology/path_connected): move `proj_Icc` to a separate file ([#5120](https://github.com/leanprover-community/mathlib/pull/5120))
Also use `min` and `max` in the definition to make, e.g., the proof of the continuity trivial.

### [2020-11-27 09:16:37](https://github.com/leanprover-community/mathlib/commit/238c58c)
chore(category_theory/limits): golf a proof ([#5130](https://github.com/leanprover-community/mathlib/pull/5130))

### [2020-11-27 09:16:35](https://github.com/leanprover-community/mathlib/commit/ff2aeae)
feat(logic/relation): trans_gen closure ([#5129](https://github.com/leanprover-community/mathlib/pull/5129))
Mechanical conversion of `refl_trans_gen` lemmas for just `trans_gen`.

### [2020-11-27 09:16:33](https://github.com/leanprover-community/mathlib/commit/af7ba87)
feat(data/polynomial/eval): eval₂ f x (p * X) = eval₂ f x p * x ([#5110](https://github.com/leanprover-community/mathlib/pull/5110))
Also generalize `polynomial.eval₂_mul_noncomm` and
`polynomial.eval₂_list_prod_noncomm`.
This PR uses `add_monoid_algebra.lift_nc` to golf some proofs about
`eval₂`. I'm not ready to replace the definition of `eval₂` yet (e.g.,
because it breaks dot notation everywhere), so I added
a lemma `eval₂_eq_lift_nc` instead.

### [2020-11-27 09:16:31](https://github.com/leanprover-community/mathlib/commit/8e09111)
chore(order/basic): add `strict_mono_??cr_on.dual` and `dual_right` ([#5107](https://github.com/leanprover-community/mathlib/pull/5107))
We can use these to avoid `@strict_mono_??cr_on (order_dual α) (order_dual β)`.

### [2020-11-27 09:16:29](https://github.com/leanprover-community/mathlib/commit/a106102)
chore(category_theory/iso): golf and name consistency ([#5096](https://github.com/leanprover-community/mathlib/pull/5096))
Minor changes: makes the names consistent and simplifies proofs

### [2020-11-27 09:16:27](https://github.com/leanprover-community/mathlib/commit/d078950)
feat(linear_algebra/bilinear_form): equivalence with matrices, given a basis ([#5095](https://github.com/leanprover-community/mathlib/pull/5095))
This PR defines the equivalence between bilinear forms on an arbitrary module and matrices, given a basis of that module. It updates the existing equivalence between bilinear forms on `n → R` so that the overall structure of the file matches that of `linear_algebra.matrix`, i.e. there are two pairs of equivs, one for `n → R` and one for any `M` with a basis.
Changes:
 - `bilin_form_equiv_matrix`, `bilin_form.to_matrix` and `matrix.to_bilin_form` have been consolidated as linear equivs `bilin_form.to_matrix'` and `matrix.to_bilin'`. Other declarations have been renamed accordingly.
 - `quadratic_form.to_matrix` and `matrix.to_quadratic_form` are renamed by analogy to `quadratic_form.to_matrix'` and `matrix.to_quadratic_form'`
 - replaced some `classical.decidable_eq` in lemma statements with instance parameters, because otherwise we have to use `congr` to apply these lemmas when a `decidable_eq` instance is available
Additions:
 - `bilin_form.to_matrix` and `matrix.to_bilin`: given a basis, the equivalences between bilinear forms on any module and matrices
 - lemmas from `to_matrix'` and `to_bilin'` have been ported to `to_matrix` and `to_bilin`
 - `bilin_form.congr`, a dependency of `bilin_form.to_matrix`, states that `bilin_form R M` and `bilin_form R M'` are linearly equivalent if `M` and `M'` are
 - assorted lemmas involving `std_basis`
Deletions:
 - `bilin_form.to_matrix_smul`: use `linear_equiv.map_smul` instead

### [2020-11-27 09:16:24](https://github.com/leanprover-community/mathlib/commit/c06c616)
feat(number_theory/arithmetic_function): Moebius inversion ([#5047](https://github.com/leanprover-community/mathlib/pull/5047))
Changes the way that zeta works with coercion
Proves Möbius inversion for functions to a general `comm_ring`

### [2020-11-27 09:16:21](https://github.com/leanprover-community/mathlib/commit/2bda184)
feat(field_theory): Prove the Galois correspondence ([#4786](https://github.com/leanprover-community/mathlib/pull/4786))
The proof leverages existing results from field_theory/fixed.lean and field_theory/primitive_element.lean.
We define Galois as normal + separable. Proving the various equivalent characterizations of Galois extensions is yet to be done.

### [2020-11-27 06:39:09](https://github.com/leanprover-community/mathlib/commit/2f939e9)
chore(data/equiv/basic): redefine `set.bij_on.equiv` ([#5128](https://github.com/leanprover-community/mathlib/pull/5128))
Now `set.bij_on.equiv` works for any `h : set.bij_on f s t`. The old
behaviour can be achieved using `(equiv.set_univ _).symm.trans _`.

### [2020-11-27 06:39:07](https://github.com/leanprover-community/mathlib/commit/4715d99)
chore(data/set/function): add 3 trivial lemmas ([#5127](https://github.com/leanprover-community/mathlib/pull/5127))

### [2020-11-27 06:39:04](https://github.com/leanprover-community/mathlib/commit/c1edbdd)
chore(data/complex/exponential): golf 2 proofs ([#5126](https://github.com/leanprover-community/mathlib/pull/5126))

### [2020-11-27 06:39:02](https://github.com/leanprover-community/mathlib/commit/cb9e5cf)
doc(data/equiv/basic): improve docstring of `equiv.sum_equiv_sigma_bool` ([#5119](https://github.com/leanprover-community/mathlib/pull/5119))
Also slightly improve defeq of the `to_fun` field by using `sum.elim` instead of a custom `match`.

### [2020-11-27 06:39:00](https://github.com/leanprover-community/mathlib/commit/d3cc993)
chore(data/pprod): Add pprod.mk.eta ([#5114](https://github.com/leanprover-community/mathlib/pull/5114))
This is exactly the same as prod.mk.eta

### [2020-11-27 04:12:29](https://github.com/leanprover-community/mathlib/commit/2c5d4a3)
chore(order/rel_iso): add a few lemmas ([#5106](https://github.com/leanprover-community/mathlib/pull/5106))
* add lemmas `order_iso.apply_eq_iff_eq` etc;
* define `order_iso.symm`.

### [2020-11-27 01:21:04](https://github.com/leanprover-community/mathlib/commit/1a8089e)
chore(scripts): update nolints.txt ([#5125](https://github.com/leanprover-community/mathlib/pull/5125))
I am happy to remove some nolints for you!

### [2020-11-26 17:19:04](https://github.com/leanprover-community/mathlib/commit/59717d6)
chore(data/sum): Add trivial simp lemmas ([#5112](https://github.com/leanprover-community/mathlib/pull/5112))

### [2020-11-26 09:59:56](https://github.com/leanprover-community/mathlib/commit/2d476e0)
chore(data/equiv/basic): Add comp_swap_eq_update ([#5091](https://github.com/leanprover-community/mathlib/pull/5091))

### [2020-11-26 01:18:53](https://github.com/leanprover-community/mathlib/commit/98ebe5a)
chore(scripts): update nolints.txt ([#5117](https://github.com/leanprover-community/mathlib/pull/5117))
I am happy to remove some nolints for you!

### [2020-11-25 16:13:58](https://github.com/leanprover-community/mathlib/commit/6e301c7)
chore(logic/function/basic): Add function.update_apply ([#5093](https://github.com/leanprover-community/mathlib/pull/5093))
This makes it easier to eliminate `dite`s in simple situations when only `ite` is needed.

### [2020-11-25 15:09:50](https://github.com/leanprover-community/mathlib/commit/81207e0)
feat(algebra/triv_sq_zero_ext): trivial square-zero extension ([#5109](https://github.com/leanprover-community/mathlib/pull/5109))

### [2020-11-25 11:39:21](https://github.com/leanprover-community/mathlib/commit/4265f2c)
chore(data/int/basic): Add int.units_mul_self ([#5101](https://github.com/leanprover-community/mathlib/pull/5101))

### [2020-11-25 06:48:00](https://github.com/leanprover-community/mathlib/commit/0324935)
chore(data/equiv/basic): Add trivial simp lemma ([#5100](https://github.com/leanprover-community/mathlib/pull/5100))
With this in place, `⇑1 ∘ f` simplifies to `⇑f`

### [2020-11-25 03:17:58](https://github.com/leanprover-community/mathlib/commit/0020077)
fix(algebra/ordered_group): remove workaround ([#5103](https://github.com/leanprover-community/mathlib/pull/5103))
The problem mentioned in the TODO has been solved so the workaround is no longer needed.

### [2020-11-25 01:28:51](https://github.com/leanprover-community/mathlib/commit/83f293e)
chore(scripts): update nolints.txt ([#5105](https://github.com/leanprover-community/mathlib/pull/5105))
I am happy to remove some nolints for you!

### [2020-11-24 19:48:35](https://github.com/leanprover-community/mathlib/commit/7e66984)
fix(algebra/group_with_zero/power): remove duplicate lemmas ([#5083](https://github.com/leanprover-community/mathlib/pull/5083))
`pow_eq_zero` and `pow_eq_zero'` are syntactically equal, as are `pow_ne_zero` and `pow_ne_zero'`.

### [2020-11-24 13:18:42](https://github.com/leanprover-community/mathlib/commit/2ed4846)
chore(linear_algebra/multilinear_map): Add boring coercion lemmas copied from ring_hom ([#5099](https://github.com/leanprover-community/mathlib/pull/5099))

### [2020-11-24 11:42:00](https://github.com/leanprover-community/mathlib/commit/943b129)
feat(analysis/special_functions/trigonometric): sin, cos, sinh, and cosh are infinitely smooth ([#5090](https://github.com/leanprover-community/mathlib/pull/5090))

### [2020-11-24 09:15:42](https://github.com/leanprover-community/mathlib/commit/fe4abe0)
chore(algebra/lie/skew_adjoint): move logic for Lie algebras of skew-adjoint endomorphisms to own file ([#5098](https://github.com/leanprover-community/mathlib/pull/5098))

### [2020-11-24 02:14:31](https://github.com/leanprover-community/mathlib/commit/51e71e9)
chore(scripts): update nolints.txt ([#5097](https://github.com/leanprover-community/mathlib/pull/5097))
I am happy to remove some nolints for you!

### [2020-11-23 23:33:18](https://github.com/leanprover-community/mathlib/commit/64b3e52)
feat(data/finset/basic): Finset subset induction ([#5087](https://github.com/leanprover-community/mathlib/pull/5087))
Induction on subsets of a given finset.

### [2020-11-23 22:04:03](https://github.com/leanprover-community/mathlib/commit/434a34d)
feat(group_theory/perm/sign): Add swap_induction_on' ([#5092](https://github.com/leanprover-community/mathlib/pull/5092))
This also adds a docstring for swap_induction_on

### [2020-11-23 22:04:01](https://github.com/leanprover-community/mathlib/commit/2a49f4e)
feat(algebra/lie/direct_sum): direct sums of Lie modules ([#5063](https://github.com/leanprover-community/mathlib/pull/5063))
There are three things happening here:
  1. introduction of definitions of direct sums for Lie modules,
  2. introduction of definitions of morphisms, equivs for Lie modules,
  3. splitting out extant definition of direct sums for Lie algebras
     into a new file.

### [2020-11-23 19:56:57](https://github.com/leanprover-community/mathlib/commit/fee93e9)
feat(ring_theory/*): Various lemmas about ideals, quotients, and localizations ([#5046](https://github.com/leanprover-community/mathlib/pull/5046))
Lemmas needed for the proof that is_jacobson is preserved under taking polynomials.

### [2020-11-23 17:02:17](https://github.com/leanprover-community/mathlib/commit/96a2038)
chore(linear_algebra/bilinear_form): cleanup ([#5049](https://github.com/leanprover-community/mathlib/pull/5049))
- Generalize some defs and lemmas to semimodules over semirings
- Define the equiv between `bilin_form` and `linear_map` analogously to `linear_map.to_matrix / matrix.to_lin`
- Mark appropriate lemmas as `simp`
- Fix overlong lines, match style guide in other places too
- Make use of variables consistent throughout the file

### [2020-11-23 15:20:48](https://github.com/leanprover-community/mathlib/commit/270fc31)
fix(ring_theory/discrete_valuation_ring): docstring typos ([#5085](https://github.com/leanprover-community/mathlib/pull/5085))
Clarify one docstring and fix two others.

### [2020-11-23 13:47:52](https://github.com/leanprover-community/mathlib/commit/e8c8ce9)
chore(category_theory/limits): move product isomorphisms ([#5057](https://github.com/leanprover-community/mathlib/pull/5057))
This PR moves some constructions and lemmas from `monoidal/of_has_finite_products` (back) to `limits/shapes/binary_products`. 
This reverts some changes made in https://github.com/leanprover-community/mathlib/commit/18246ac427c62348e7ff854965998cd9878c7692#diff-95871ea16bec862dfc4359f812b624a7a98e87b8c31c034e8a6e792332edb646. In particular, the purpose of that PR was to minimise imports in particular relating to `finite_limits`, but moving these particular definitions back doesn't make the imports any worse in that sense - other than that `binary_products` now imports `terminal` which I think doesn't make the import graph much worse.  On the other hand, these definitions are useful outside of the context of monoidal categories so I think they do genuinely belong in `limits/`.
I also changed some proofs from `tidy` to `simp` or a term-mode proof, and removed a `simp` attribute from a lemma which was already provable by `simp`.

### [2020-11-23 13:47:50](https://github.com/leanprover-community/mathlib/commit/a71901f)
feat(category_theory/limits): explicit binary product functor in Type ([#5043](https://github.com/leanprover-community/mathlib/pull/5043))
Adds `binary_product_functor`, the explicit product functor in Type, and `binary_product_iso_prod` which shows it is isomorphic to the one picked by choice (this is helpful eg to show Type is cartesian closed).
I also edited the definitions a little to use existing machinery instead - this seems to make `simp` and `tidy` stronger when working with the explicit product cone; but they're definitionally the same as the old ones.

### [2020-11-23 13:47:48](https://github.com/leanprover-community/mathlib/commit/562be70)
feat(field_theory/separable): a separable polynomial is squarefree ([#5039](https://github.com/leanprover-community/mathlib/pull/5039))
I prove that a separable polynomial is squarefree.

### [2020-11-23 13:47:44](https://github.com/leanprover-community/mathlib/commit/3c1cf60)
feat(category_theory/sigma): disjoint union of categories ([#5020](https://github.com/leanprover-community/mathlib/pull/5020))

### [2020-11-23 13:47:42](https://github.com/leanprover-community/mathlib/commit/13b9478)
feat(combinatorics/colex): introduce colexicographical order ([#4858](https://github.com/leanprover-community/mathlib/pull/4858))
We define the colex ordering for finite sets, and give a couple of important lemmas and properties relating to it.
Part of [#2770](https://github.com/leanprover-community/mathlib/pull/2770), in order to prove the Kruskal-Katona theorem.

### [2020-11-23 12:40:48](https://github.com/leanprover-community/mathlib/commit/83ec6e0)
feat(analysis/normed_space/inner_product): inner product is infinitely smooth ([#5089](https://github.com/leanprover-community/mathlib/pull/5089))

### [2020-11-23 10:07:38](https://github.com/leanprover-community/mathlib/commit/fdabe9c)
feat(data/padics/padic_norm): add a little more API ([#5082](https://github.com/leanprover-community/mathlib/pull/5082))
A little more API for `padic_val_rat` and `padic_val_nat`.

### [2020-11-23 09:03:09](https://github.com/leanprover-community/mathlib/commit/2f51659)
feat(analysis/special_functions/exp_log): `exp` is infinitely smooth ([#5086](https://github.com/leanprover-community/mathlib/pull/5086))
* Prove that `complex.exp` and `real.exp` are infinitely smooth.
* Generalize lemmas about `exp ∘ f` to `f : E → ℂ` or `f : E → ℝ`
  instead of `f : ℂ → ℂ` or `f : ℝ → ℝ`.

### [2020-11-23 03:24:34](https://github.com/leanprover-community/mathlib/commit/b9bd4a5)
chore(scripts): update nolints.txt ([#5088](https://github.com/leanprover-community/mathlib/pull/5088))
I am happy to remove some nolints for you!

### [2020-11-23 01:00:25](https://github.com/leanprover-community/mathlib/commit/ce0498e)
feat(data/nat/basic): add injectivity and divisibility lemmas ([#5068](https://github.com/leanprover-community/mathlib/pull/5068))
Multiplication by a non-zero natural is injective. Also a simple criterion for non-divisibility which I couldn't find (0<b<a implies a doesn't divide b).

### [2020-11-22 22:06:40](https://github.com/leanprover-community/mathlib/commit/2252c3a)
chore(data/list/basic): Add pmap_map ([#5081](https://github.com/leanprover-community/mathlib/pull/5081))

### [2020-11-22 22:06:38](https://github.com/leanprover-community/mathlib/commit/7f4286c)
chore(order/basic): add `le_update_iff` and `update_le_iff`  ([#5080](https://github.com/leanprover-community/mathlib/pull/5080))
Other changes:
* add `update_eq_iff`, `eq_update_iff` and a more general lemma `rel_update_iff`;
* remove `@[simps]` attributes on `pi.*_lattice` instances.

### [2020-11-22 22:06:36](https://github.com/leanprover-community/mathlib/commit/c4132e9)
chore(logic/unique): add `fin.inhabited` ([#5077](https://github.com/leanprover-community/mathlib/pull/5077))

### [2020-11-22 22:06:34](https://github.com/leanprover-community/mathlib/commit/2044451)
chore(data/real/ennreal): add a few lemmas ([#5071](https://github.com/leanprover-community/mathlib/pull/5071))
Also swap LHS with RHS in `to_real_mul_to_real` and rename it to `to_real_mul`.

### [2020-11-22 22:06:32](https://github.com/leanprover-community/mathlib/commit/f627d76)
chore(data/set/basic): more simp lemmas ([#5070](https://github.com/leanprover-community/mathlib/pull/5070))
Motivated by [#4843](https://github.com/leanprover-community/mathlib/pull/4843)

### [2020-11-22 22:06:30](https://github.com/leanprover-community/mathlib/commit/f5b967a)
feat(finset/basic): Add forall_mem_union ([#5064](https://github.com/leanprover-community/mathlib/pull/5064))
Part of [[#4943](https://github.com/leanprover-community/mathlib/pull/4943)](https://github.com/leanprover-community/mathlib/pull/4943), in order to prove theorems about antichains.
Lemma and proof supplied by [eric-wieser](https://github.com/eric-wieser)

### [2020-11-22 22:06:27](https://github.com/leanprover-community/mathlib/commit/17a6f6d)
refactor(analysis/normed_space/hahn_banach): use is_R_or_C instead of specific typeclass ([#5009](https://github.com/leanprover-community/mathlib/pull/5009))
In the current version, the proof of Hahn-Banach theorem is given over the reals, then over the complexes, and then to state the consequences uniformly a custom typeclass is defined. The proof over the complexes in fact works directly over any `is_R_or_C` field (i.e., reals or complexes), so we reformulate the proof in these terms, avoiding the custom typeclass.
It doesn't bring any new theorem to mathlib, but it may be helpful in the future (to prove results uniformly over reals and complexes using `is_R_or_C`) if we have Hahn-Banach readily available for this typeclass.

### [2020-11-22 19:31:23](https://github.com/leanprover-community/mathlib/commit/2a876b6)
chore(algebra/ordered_group): move monoid stuff to ordered_monoid.lean ([#5066](https://github.com/leanprover-community/mathlib/pull/5066))
Replace one 2000 line file with two 1000 line files: ordered group stuff in one, and ordered monoid stuff in the other.

### [2020-11-22 14:51:30](https://github.com/leanprover-community/mathlib/commit/8d71ec9)
chore(data/fin): a few more lemmas about `fin.insert_nth` ([#5079](https://github.com/leanprover-community/mathlib/pull/5079))

### [2020-11-22 14:51:28](https://github.com/leanprover-community/mathlib/commit/c458724)
chore(topology/metric_space/isometry): add a missing simp lemma ([#5078](https://github.com/leanprover-community/mathlib/pull/5078))

### [2020-11-22 14:51:26](https://github.com/leanprover-community/mathlib/commit/a9b6b36)
chore(algebra/big_operators): add `finset.abs_prod` ([#5076](https://github.com/leanprover-community/mathlib/pull/5076))

### [2020-11-22 14:51:24](https://github.com/leanprover-community/mathlib/commit/2ba930e)
chore(measure_theory/borel_space): add some `simp` attrs ([#5075](https://github.com/leanprover-community/mathlib/pull/5075))

### [2020-11-22 14:51:21](https://github.com/leanprover-community/mathlib/commit/c59dbf3)
chore(topology/basic): add `cluster_pt.map`, rename `mem_closure` ([#5065](https://github.com/leanprover-community/mathlib/pull/5065))
* add `filter.prod_pure`, `filter.pure_prod`, `cluster_pt.map`, and `set.maps_to.closure`;
* rename `mem_closure` to `map_mem_closure`;
* rename `mem_closure2` to `map_mem_closure2`.

### [2020-11-22 12:03:14](https://github.com/leanprover-community/mathlib/commit/a649851)
chore(analysis/complex/basic): add `times_cont_diff.real_of_complex` ([#5073](https://github.com/leanprover-community/mathlib/pull/5073))
Also rename `has_deriv_at_real_of_complex` to `has_deriv_at.real_of_complex`.

### [2020-11-22 12:03:12](https://github.com/leanprover-community/mathlib/commit/87439b9)
chore(logic/basic): add `forall_apply_eq_imp_iff₂` ([#5072](https://github.com/leanprover-community/mathlib/pull/5072))
Other lemmas simplify `∀ y ∈ f '' s, p y` to the LHS of this lemma.

### [2020-11-22 10:15:37](https://github.com/leanprover-community/mathlib/commit/198f3e5)
chore(topology/homeomorph): add more simp lemmas ([#5069](https://github.com/leanprover-community/mathlib/pull/5069))
Also use implicit arguments in some `iff` lemmas.

### [2020-11-22 01:09:23](https://github.com/leanprover-community/mathlib/commit/8525aa9)
chore(scripts): update nolints.txt ([#5067](https://github.com/leanprover-community/mathlib/pull/5067))
I am happy to remove some nolints for you!

### [2020-11-21 21:24:19](https://github.com/leanprover-community/mathlib/commit/79cd720)
feat(data/complex/is_R_or_C): Create a proper coercion from ℝ ([#4824](https://github.com/leanprover-community/mathlib/pull/4824))
This PR creates a proper coercion `ℝ → 𝕜` for `[is_R_or_C 𝕜]`, modelled on the code in `data/nat/cast`, as per the discussion [here](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Hilbert.20space.20is.20isometric.20to.20its.20dual).

### [2020-11-21 20:09:32](https://github.com/leanprover-community/mathlib/commit/556a725)
feat(data/nat/parity): lemmas about (-1)^n ([#5056](https://github.com/leanprover-community/mathlib/pull/5056))
I needed these twice recently, for two independent reasons, so I thought they were worth a PR.

### [2020-11-21 17:37:55](https://github.com/leanprover-community/mathlib/commit/aff4669)
feat(group_theory/subgroup): add closure_eq_bot_iff ([#5055](https://github.com/leanprover-community/mathlib/pull/5055))
Add missing lemma

### [2020-11-21 01:13:36](https://github.com/leanprover-community/mathlib/commit/cff497f)
chore(scripts): update nolints.txt ([#5058](https://github.com/leanprover-community/mathlib/pull/5058))
I am happy to remove some nolints for you!

### [2020-11-20 19:18:02](https://github.com/leanprover-community/mathlib/commit/006f84e)
feat(algebra/group_power/basic): add add le_of_pow_le_pow ([#5054](https://github.com/leanprover-community/mathlib/pull/5054))
add a random missing lemma

### [2020-11-20 16:41:58](https://github.com/leanprover-community/mathlib/commit/1fbdf77)
fix(linear_algebra/quadratic_form): nondegenerate -> anisotropic ([#5050](https://github.com/leanprover-community/mathlib/pull/5050))
I made a mistake by merging a PR that defined `nondegenerate`
but should have used the terminology `anisotropic` instead.

### [2020-11-20 12:39:29](https://github.com/leanprover-community/mathlib/commit/498d497)
feat(measure_theory/lp_space): prove that neg and add are in Lp ([#5014](https://github.com/leanprover-community/mathlib/pull/5014))
For f and g in Lp, (-f) and (f+g) are also in Lp.

### [2020-11-20 09:40:27](https://github.com/leanprover-community/mathlib/commit/32d1dfc)
feat(linear_algebra/quadratic_form): nondegenerate quadratic forms ([#5045](https://github.com/leanprover-community/mathlib/pull/5045))
No real lemmas about these, but `nondegenerate Q` is easier to read than `∀ x, Q x = 0 → x = 0`

### [2020-11-20 07:52:25](https://github.com/leanprover-community/mathlib/commit/8d40e8d)
feat(analysis/special_functions/pow): add ennreal.to_nnreal_rpow ([#5042](https://github.com/leanprover-community/mathlib/pull/5042))
cut ennreal.to_real_rpow into two lemmas: to_nnreal_rpow and to_real_rpow

### [2020-11-20 06:44:00](https://github.com/leanprover-community/mathlib/commit/de76acd)
feat(number_theory/arithmetic_function): moebius is the inverse of zeta ([#5001](https://github.com/leanprover-community/mathlib/pull/5001))
Proves the most basic version of moebius inversion: that the moebius function is the inverse of the zeta function

### [2020-11-20 01:04:58](https://github.com/leanprover-community/mathlib/commit/0e976d9)
chore(scripts): update nolints.txt ([#5048](https://github.com/leanprover-community/mathlib/pull/5048))
I am happy to remove some nolints for you!

### [2020-11-19 15:34:57](https://github.com/leanprover-community/mathlib/commit/47542a0)
feat(ring_theory/witt_vector/verschiebung): verschiebung of witt vectors ([#4836](https://github.com/leanprover-community/mathlib/pull/4836))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-11-19 13:00:19](https://github.com/leanprover-community/mathlib/commit/3326510)
chore(field_theory/minimal_polynomial): generalize irreducible ([#5006](https://github.com/leanprover-community/mathlib/pull/5006))
I have removed the assumption that the base ring is a field for a minimal polynomial to be irreducible.
The proof is simple but long, it should be possible to use `wlog` to shorten it, but I do not understand how to do it...

### [2020-11-19 13:00:17](https://github.com/leanprover-community/mathlib/commit/b479d3b)
feat(algebra/*): star_ring instances on free_algebra, free_monoid, ring_quot, and quaternion ([#4902](https://github.com/leanprover-community/mathlib/pull/4902))

### [2020-11-19 10:10:26](https://github.com/leanprover-community/mathlib/commit/700d576)
chore(algebra/group/defs): Remove shortcut instance definitions ([#4955](https://github.com/leanprover-community/mathlib/pull/4955))
This means that `group.to_left_cancel_semigroup` is now spelt `group.to_cancel_monoid.to_left_cancel_monoid.to_left_cancel_semigroup`.
The longer spelling shouldn't actually matter because type inference will do it anyway.
I don't know whether this matters, but this should slightly reduce the number of connections that instance resolution must check.
This shortcut wasn't added deliberately, it seems it just got added accidentally when [#3688](https://github.com/leanprover-community/mathlib/pull/3688) was introduced.

### [2020-11-19 06:43:23](https://github.com/leanprover-community/mathlib/commit/123c522)
feat(category_theory/limits): terminal comparison morphism ([#5025](https://github.com/leanprover-community/mathlib/pull/5025))

### [2020-11-19 03:06:00](https://github.com/leanprover-community/mathlib/commit/b848b5b)
feat(algebra/squarefree): a squarefree element of a UFM divides a power iff it divides ([#5037](https://github.com/leanprover-community/mathlib/pull/5037))
Proves that if `x, y` are elements of a UFM such that `squarefree x`, then `x | y ^ n` iff `x | y`.

### [2020-11-19 01:49:38](https://github.com/leanprover-community/mathlib/commit/87a6d95)
chore(scripts): update nolints.txt ([#5041](https://github.com/leanprover-community/mathlib/pull/5041))
I am happy to remove some nolints for you!

### [2020-11-19 01:49:36](https://github.com/leanprover-community/mathlib/commit/68adaba)
chore(field_theory/separable): spell-check "seperable" to "separable" ([#5040](https://github.com/leanprover-community/mathlib/pull/5040))
Replacing instances of "seperable" with "separable"

### [2020-11-18 23:23:59](https://github.com/leanprover-community/mathlib/commit/dcbec39)
feat(algebra/*): Add of_injective lemmas ([#5034](https://github.com/leanprover-community/mathlib/pull/5034))
This adds `free_monoid.of_injective`, `monoid_algebra.of_injective`, `add_monoid_algebra.of_injective`, and renames and restates `free_group.of.inj` to match these lemmas.
`function.injective (free_abelian_group.of)` is probably also true, but I wasn't able to prove it.

### [2020-11-18 23:23:57](https://github.com/leanprover-community/mathlib/commit/2de8db4)
feat(analysis/special_functions/pow): prove measurability of rpow for ennreal ([#5026](https://github.com/leanprover-community/mathlib/pull/5026))
Prove measurability of rpow for an ennreal argument.
Also shorten the proof in the real case.

### [2020-11-18 21:10:00](https://github.com/leanprover-community/mathlib/commit/abb0b67)
refactor(*): make continuous a structure ([#5035](https://github.com/leanprover-community/mathlib/pull/5035))
Turn `continuous` into a structure, to make sure it is not unfolded too much by Lean.
After the change, inferring some types is harder to Lean (as it can not unfold further to find more information), so some help is needed at places. Especially, for `hf : continuous f` and `hg : continuous g`, I had to replace `hf.prod_mk hg` with `(hf.prod_mk hg : _)` a lot of times.
For `hf : continuous f` and `hs : is_open s`, the fact that `f^(-1) s` is open used to be `hf s hs`. Now, it is `hs.preimage hf`, just like it is for closed sets.

### [2020-11-18 16:28:13](https://github.com/leanprover-community/mathlib/commit/38d2b53)
feat(algebra/free_algebra): Add a nontrivial instance ([#5033](https://github.com/leanprover-community/mathlib/pull/5033))

### [2020-11-18 14:27:12](https://github.com/leanprover-community/mathlib/commit/0e09ada)
feat(category_theory/is_connected): zigzag lemmas ([#5024](https://github.com/leanprover-community/mathlib/pull/5024))
A few basic lemmas about connected categories and the zigzag relation

### [2020-11-18 12:44:52](https://github.com/leanprover-community/mathlib/commit/aff7727)
chore(data/complex/is_R_or_C): Remove two unnecessary axioms ([#5017](https://github.com/leanprover-community/mathlib/pull/5017))
`of_real` and `smul_coe_mul_ax` are already implied by the algebra structure.
The addition of `noncomputable` does not matter here, as both instances of `is_R_or_C` are marked non-computable anyway.

### [2020-11-18 09:32:12](https://github.com/leanprover-community/mathlib/commit/d22a878)
doc(algebra/module/linear_map): Explain where the ring instance is ([#5023](https://github.com/leanprover-community/mathlib/pull/5023))

### [2020-11-18 09:32:10](https://github.com/leanprover-community/mathlib/commit/dfdad99)
feat(category_theory): constant functor is faithful ([#5022](https://github.com/leanprover-community/mathlib/pull/5022))

### [2020-11-18 09:32:06](https://github.com/leanprover-community/mathlib/commit/dab2ae3)
feat(category_theory/is_connected): transfer across equivalence ([#5021](https://github.com/leanprover-community/mathlib/pull/5021))
Also renames some universes to match usual conventions

### [2020-11-18 09:31:55](https://github.com/leanprover-community/mathlib/commit/a44b46c)
chore(*/sub*): Use the simp normal form for has_coe_to_sort ([#5019](https://github.com/leanprover-community/mathlib/pull/5019))
This reduces the need to start proofs on subtypes by applying `mem_coe`.

### [2020-11-18 09:31:53](https://github.com/leanprover-community/mathlib/commit/0d3092b)
feat(number_theory/arithmetic_function): defining several more `arithmetic_function`s ([#4998](https://github.com/leanprover-community/mathlib/pull/4998))
Defines arithmetic functions `card_factors`, `card_distinct_factors`, and `moebius`

### [2020-11-18 09:31:50](https://github.com/leanprover-community/mathlib/commit/7cc6b53)
feat(category_theory/sites): sheaves on a grothendieck topology ([#4608](https://github.com/leanprover-community/mathlib/pull/4608))
Broken off from [#4577](https://github.com/leanprover-community/mathlib/pull/4577).

### [2020-11-18 07:06:12](https://github.com/leanprover-community/mathlib/commit/fec1a59)
feat(data/list): map lemmas paralleling functor ([#5028](https://github.com/leanprover-community/mathlib/pull/5028))
Adding `comp_map` and `map_comp_map`.
Docstrings done to match docstrings for equivalent `prod.map_comp_map`.

### [2020-11-18 01:08:16](https://github.com/leanprover-community/mathlib/commit/19e3302)
chore(scripts): update nolints.txt ([#5029](https://github.com/leanprover-community/mathlib/pull/5029))
I am happy to remove some nolints for you!

### [2020-11-17 17:53:52](https://github.com/leanprover-community/mathlib/commit/e92b5ac)
feat(algebra/opposites): Provide semimodule instances and op_linear_equiv ([#4954](https://github.com/leanprover-community/mathlib/pull/4954))
We already have a `has_scalar` definition via an `algebra` definition.
The definition used there satisfies a handful of other typeclasses too, and also allows for `op_add_equiv` to be stated more strongly as `op_linear_equiv`.
This also cuts back the imports a little on `algebra.module.basic`, which means formerly-transitive imports have to be added to downstream files.

### [2020-11-17 15:27:56](https://github.com/leanprover-community/mathlib/commit/97fc8ce)
refactor(algebra/lie/basic): unbundle the action in `lie_module` ([#4959](https://github.com/leanprover-community/mathlib/pull/4959))

### [2020-11-17 12:21:38](https://github.com/leanprover-community/mathlib/commit/47476ef)
docs(references.bib): adds Samuel's Théorie Algébrique des Nombres ([#5018](https://github.com/leanprover-community/mathlib/pull/5018))
Added Samuel's Théorie Algébrique des Nombres

### [2020-11-17 12:21:36](https://github.com/leanprover-community/mathlib/commit/a59e76b)
feat(ring_theory/noetherian): add two lemmas on products of prime ideals ([#5013](https://github.com/leanprover-community/mathlib/pull/5013))
Add two lemmas saying that in a noetherian ring (resp. _integral domain)_ every (_nonzero_) ideal contains a (_nonzero_) product of prime ideals.

### [2020-11-17 12:21:33](https://github.com/leanprover-community/mathlib/commit/86b0971)
feat(algebra/group_with_zero): Bundled `monoid_with_zero_hom` ([#4995](https://github.com/leanprover-community/mathlib/pull/4995))
This adds, without notation, `monoid_with_zero_hom` as a variant of `A →* B` that also satisfies `f 0 = 0`.
As part of this, this change:
* Splits up `group_with_zero` into multiple files, so that the definitions can be used in the bundled homs before any of the lemmas start pulling in dependencies
* Adds `monoid_with_zero_hom` as a base class of `ring_hom`
* Changes some `monoid_hom` objects into `monoid_with_zero_hom` objects.
* Moves some lemmas about `valuation` into `monoid_hom`, since they apply more generally
* Add automatic coercions between `monoid_with_zero_hom` and `monoid_hom`

### [2020-11-17 12:21:30](https://github.com/leanprover-community/mathlib/commit/7a70764)
feat(ring_theory/fractional_ideal): helper lemmas for Dedekind domains ([#4994](https://github.com/leanprover-community/mathlib/pull/4994))
An assortment of lemmas and refactoring related to `fractional_ideal`s, used in the Dedekind domain project.
    
The motivation for creating this PR is that we are planning to remove the general `has_inv` instance on `fractional_ideal` (reserving it only for Dedekind domains), and we don't want to do the resulting refactoring twice. So we make sure everything is in the master branch, do the refactoring there, then merge the changes back into the work in progress branch.
Overview of the changes in `localization.lean`:
 * more `is_integer` lemmas
 * a localization of a noetherian ring is noetherian
 * generalize a few lemmas from integral domains to nontrivial `comm_ring`s
 * `algebra A (fraction_ring A)` instance
Overview of the changes in `fractional_ideal.lean`:
 * generalize many lemmas from integral domains to (nontrivial) `comm_ring`s (now `R` is notation for a `comm_ring` and `R₁` for an integral domain) 
 * `is_fractional_of_le`, `is_fractional_span_iff` and `is_fractional_of_fg`
 * many `simp` and `norm_cast` results involving `coe : ideal -> fractional_ideal` and `coe : fractional_ideal -> submodule`: now should be complete for `0`, `1`, `+`, `*`, `/` and `≤`.
 * use `1 : submodule` as `simp` normal form instead of `coe_submodule (1 : ideal)`
 * make the multiplication operation irreducible
 * port `submodule.has_mul` lemmas to `fractional_ideal.has_mul`
 * `simp` lemmas for `canonical_equiv`, `span_singleton`
 * many ways to prove `is_noetherian`
Co-Authored-By: Ashvni <ashvni.n@gmail.com>
Co-Authored-By: faenuccio <filippo.nuccio@univ-st-etienne.fr>

### [2020-11-17 11:18:37](https://github.com/leanprover-community/mathlib/commit/ad286fb)
feat(tactic/fresh_names): add tactics for giving hyps fresh names ([#4987](https://github.com/leanprover-community/mathlib/pull/4987))
This commit adds a variant of `rename` which guarantees that the renamed
hypotheses receive fresh names. To implement this, we also add more flexible
variants of `get_unused_name`, `intro_fresh` and `intro_lst_fresh`.

### [2020-11-17 02:15:30](https://github.com/leanprover-community/mathlib/commit/a2f3399)
chore(scripts): update nolints.txt ([#5016](https://github.com/leanprover-community/mathlib/pull/5016))
I am happy to remove some nolints for you!

### [2020-11-16 23:47:31](https://github.com/leanprover-community/mathlib/commit/53f71f8)
feat(data/list): list last lemmas ([#5015](https://github.com/leanprover-community/mathlib/pull/5015))
list last lemmas letting lean learn little logical links

### [2020-11-16 14:15:33](https://github.com/leanprover-community/mathlib/commit/b588fc4)
chore(*) Unused have statements in term mode ([#5012](https://github.com/leanprover-community/mathlib/pull/5012))
Remove unneeded have statements.

### [2020-11-16 09:03:03](https://github.com/leanprover-community/mathlib/commit/90fa510)
feat(analysis/special_functions/pow): rpow is measurable ([#5008](https://github.com/leanprover-community/mathlib/pull/5008))
Prove the measurability of rpow in two cases: real and nnreal.

### [2020-11-16 01:22:58](https://github.com/leanprover-community/mathlib/commit/4cd2438)
chore(scripts): update nolints.txt ([#5011](https://github.com/leanprover-community/mathlib/pull/5011))
I am happy to remove some nolints for you!

### [2020-11-16 00:17:12](https://github.com/leanprover-community/mathlib/commit/470ac77)
feat(category_theory/monad): monadic functor really creates limits ([#4931](https://github.com/leanprover-community/mathlib/pull/4931))
Show that a monadic functor `creates_limits`, and a partial result for colimits.

### [2020-11-15 14:10:11](https://github.com/leanprover-community/mathlib/commit/9631594)
feat(algebra/star): star monoids, rings and algebras ([#4886](https://github.com/leanprover-community/mathlib/pull/4886))

### [2020-11-15 04:56:07](https://github.com/leanprover-community/mathlib/commit/9dd9b6b)
refactor(archive/imo/imo1969_q1): prove `infinite` statement, cleanup ([#4391](https://github.com/leanprover-community/mathlib/pull/4391))
The previous formalization didn't quite prove that there were infinitely many natural numbers with the desired property, but rather that for any natural number there's a larger one with the property. This PR changes the ending to prove that the set of integers described in the problem statement is `infinite`.

### [2020-11-15 01:46:16](https://github.com/leanprover-community/mathlib/commit/7e27d94)
chore(scripts): update nolints.txt ([#5007](https://github.com/leanprover-community/mathlib/pull/5007))
I am happy to remove some nolints for you!

### [2020-11-15 01:46:14](https://github.com/leanprover-community/mathlib/commit/447b18f)
chore(data/polynomial/degree): consolidate all `polynomial.degree` files in one folder ([#5005](https://github.com/leanprover-community/mathlib/pull/5005))
Moves `data/polynomial/degree.lean` to `data/polynomial/degree`, which already exists, renames it `lemmas.lean`
Renames `data/polynomial/degree/basic.lean` to `definitions.lean`
Adds `data/polynomial/degree/default.lean`, which just imports `lemmas.lean`

### [2020-11-15 01:46:12](https://github.com/leanprover-community/mathlib/commit/fca7eba)
chore(analysis/calculus/deriv): composition of `g : 𝕜 → 𝕜` with `f : E → 𝕜` ([#4871](https://github.com/leanprover-community/mathlib/pull/4871))

### [2020-11-15 00:37:55](https://github.com/leanprover-community/mathlib/commit/e6e8275)
chore(linear_algebra/char_poly): put everything `char_poly` in one folder ([#5004](https://github.com/leanprover-community/mathlib/pull/5004))
Moves `char_poly` to `char_poly.basic`, because the folder already exists

### [2020-11-14 23:13:25](https://github.com/leanprover-community/mathlib/commit/6544244)
feat(data/polynomial) small refactor and golf ([#5002](https://github.com/leanprover-community/mathlib/pull/5002))
Factor out the lemma that roots of the normalization equal the roots of a polynomial and golf a proof a tiny bit.

### [2020-11-14 22:08:14](https://github.com/leanprover-community/mathlib/commit/0582237)
feat(analysis): seminorms and local convexity ([#4827](https://github.com/leanprover-community/mathlib/pull/4827))

### [2020-11-14 19:46:53](https://github.com/leanprover-community/mathlib/commit/633c2a6)
feat(ring_theory/gauss_lemma): two primitive polynomials divide iff they do in a fraction field ([#5003](https://github.com/leanprover-community/mathlib/pull/5003))
Shows `polynomial.is_primitive.dvd_iff_fraction_map_dvd_fraction_map`, that two primitive polynomials divide iff they do over a fraction field.
Shows `polynomial.is_primitive.int.dvd_iff_map_cast_dvd_map_cast`, the version for integers and rationals.

### [2020-11-14 19:46:51](https://github.com/leanprover-community/mathlib/commit/0092414)
feat(data/nat/choose/sum): alternating binomial coefficient sums ([#4997](https://github.com/leanprover-community/mathlib/pull/4997))
Evaluates some sums related to binomial coefficients with alternating signs

### [2020-11-14 18:20:15](https://github.com/leanprover-community/mathlib/commit/9b887d5)
feat(measure_theory/lp_space): Define Lp spaces ([#4993](https://github.com/leanprover-community/mathlib/pull/4993))
Define the space Lp of functions for which the norm raised to the power p has finite integral.
Define the seminorm on that space (without proof that it is a seminorm, for now).
Add three lemmas to analysis/special_functions/pow.lean about ennreal.rpow
<!--
put comments you want to keep out of the PR commit here.
If this PR depends on other PRs, please list them below this comment,
using the following format:
- [ ] depends on: #abc [optional extra text]
- [ ] depends on: #xyz [optional extra text]
-->

### [2020-11-14 12:34:53](https://github.com/leanprover-community/mathlib/commit/70ca6fd)
feat(ring_theory/power_basis): `equiv`s between algebras with the same power basis ([#4986](https://github.com/leanprover-community/mathlib/pull/4986))
`power_basis.lift` and `power_basis.equiv` use the power basis structure to define `alg_hom`s and `alg_equiv`s.
    
The main application in this PR is `power_basis.equiv_adjoin_simple`, which states that adjoining an element of a power basis of `L : K` gives `L` itself.

### [2020-11-14 12:34:51](https://github.com/leanprover-community/mathlib/commit/6bac899)
feat(category_theory/limits/preserves): functor product preserves colims ([#4941](https://github.com/leanprover-community/mathlib/pull/4941))

### [2020-11-14 12:34:49](https://github.com/leanprover-community/mathlib/commit/154d73d)
feat(category_theory/equivalence): equivalence of functor categories ([#4940](https://github.com/leanprover-community/mathlib/pull/4940))

### [2020-11-14 12:34:46](https://github.com/leanprover-community/mathlib/commit/a0341a8)
feat(category_theory/limits/creates): transfer creating limits through nat iso ([#4938](https://github.com/leanprover-community/mathlib/pull/4938))
`creates` version of [#4934](https://github.com/leanprover-community/mathlib/pull/4934)

### [2020-11-14 12:34:45](https://github.com/leanprover-community/mathlib/commit/ccc1431)
feat(ring_theory/ideal_operations): prime avoidance ([#773](https://github.com/leanprover-community/mathlib/pull/773))
```lean
/-- Prime avoidance. Atiyah-Macdonald 1.11, Eisenbud 3.3, Stacks 10.14.2 (00DS), Matsumura Ex.1.6. -/
theorem subset_union_prime {s : finset ι} {f : ι → ideal R} (a b : ι)
  (hp : ∀ i ∈ s, i ≠ a → i ≠ b → is_prime (f i)) {I : ideal R} :
  (I : set R) ⊆ (⋃ i ∈ (↑s : set ι), f i) ↔ ∃ i ∈ s, I ≤ f i :=
```

### [2020-11-14 11:02:55](https://github.com/leanprover-community/mathlib/commit/5f15104)
feat(algebra/squarefree): Defines squarefreeness, proves several equivalences ([#4981](https://github.com/leanprover-community/mathlib/pull/4981))
Defines when a monoid element is `squarefree`
Proves basic lemmas to determine squarefreeness
Proves squarefreeness criteria in terms of `multiplicity`, `unique_factorization_monoid.factors`, and `nat.factors`

### [2020-11-14 01:13:48](https://github.com/leanprover-community/mathlib/commit/4db26af)
chore(scripts): update nolints.txt ([#4999](https://github.com/leanprover-community/mathlib/pull/4999))
I am happy to remove some nolints for you!

### [2020-11-13 22:06:40](https://github.com/leanprover-community/mathlib/commit/9ed9e0f)
feat(tactic/has_variable_names): add tactic for type-based naming ([#4988](https://github.com/leanprover-community/mathlib/pull/4988))
When we name hypotheses or variables, we often do so in a type-directed fashion:
a hypothesis of type `ℕ` is called `n` or `m`; a hypothesis of type `list ℕ` is
called `ns`; etc. This commits adds a tactic which looks up typical variable
names for a given type. Typical variable names are registered by giving an
instance of the new type class `has_variable_names`. We also give instances of
this type class for many core types.

### [2020-11-13 19:42:11](https://github.com/leanprover-community/mathlib/commit/050b837)
feat(field_theory/adjoin): Adjoin integral element ([#4831](https://github.com/leanprover-community/mathlib/pull/4831))

### [2020-11-13 17:59:05](https://github.com/leanprover-community/mathlib/commit/eeb2057)
feat(ring_theory/unique_factorization_domain): connecting `multiplicity` to `unique_factorization_domain.factors` ([#4980](https://github.com/leanprover-community/mathlib/pull/4980))
Connects multiplicity of an irreducible to the multiset of irreducible factors

### [2020-11-13 11:15:04](https://github.com/leanprover-community/mathlib/commit/1a233e0)
feat(analysis/calculus): derivative is measurable ([#4974](https://github.com/leanprover-community/mathlib/pull/4974))

### [2020-11-13 01:25:28](https://github.com/leanprover-community/mathlib/commit/140d8b4)
chore(scripts): update nolints.txt ([#4992](https://github.com/leanprover-community/mathlib/pull/4992))
I am happy to remove some nolints for you!

### [2020-11-12 23:23:14](https://github.com/leanprover-community/mathlib/commit/6b3a2d1)
feat(archive/imo): formalize IMO 1964 problem 1 ([#4935](https://github.com/leanprover-community/mathlib/pull/4935))
This is an alternative approach to [#4369](https://github.com/leanprover-community/mathlib/pull/4369), where progress seems to have stalled. I avoid integers completely by working with `nat.modeq`, and deal with the cases of n mod 3 by simply breaking into three cases.

### [2020-11-12 16:36:44](https://github.com/leanprover-community/mathlib/commit/6e64df5)
chore(deprecated/group): Do not import `deprecated` from `equiv/mul_add` ([#4989](https://github.com/leanprover-community/mathlib/pull/4989))
This swaps the direction of the import, which makes the deprecated instances for `mul_equiv` be in the same place as the instances for `monoid_hom`.

### [2020-11-12 16:36:42](https://github.com/leanprover-community/mathlib/commit/97a7f57)
chore(algebra/direct_limit): Use bundled morphisms ([#4964](https://github.com/leanprover-community/mathlib/pull/4964))
This introduced some ugliness in the form of `(λ i j h, f i j h)`, which is a little unfortunate

### [2020-11-12 14:19:46](https://github.com/leanprover-community/mathlib/commit/34215fc)
feat(group_theory/sub{monoid,group}): Add `closure_induction'` for subtypes ([#4984](https://github.com/leanprover-community/mathlib/pull/4984))

### [2020-11-12 12:14:35](https://github.com/leanprover-community/mathlib/commit/7404f0e)
feat(algebra/pointwise): lemmas relating to submonoids ([#4960](https://github.com/leanprover-community/mathlib/pull/4960))

### [2020-11-12 08:28:56](https://github.com/leanprover-community/mathlib/commit/593013d)
feat(algebra/quandle): Bundle `rack.to_envel_group.map` into an equiv ([#4978](https://github.com/leanprover-community/mathlib/pull/4978))
This also cleans up some non-terminal simp tactics

### [2020-11-12 04:06:42](https://github.com/leanprover-community/mathlib/commit/3f575d7)
feat(group_theory/subgroup) top is a normal subgroup ([#4982](https://github.com/leanprover-community/mathlib/pull/4982))

### [2020-11-12 02:51:51](https://github.com/leanprover-community/mathlib/commit/509a224)
chore(scripts): update nolints.txt ([#4983](https://github.com/leanprover-community/mathlib/pull/4983))
I am happy to remove some nolints for you!

### [2020-11-12 00:24:20](https://github.com/leanprover-community/mathlib/commit/f6c8d81)
feat(algebra/group/with_one): Use an equiv for `lift` ([#4975](https://github.com/leanprover-community/mathlib/pull/4975))

### [2020-11-12 00:24:16](https://github.com/leanprover-community/mathlib/commit/49cf28f)
feat(data/matrix): little lemmas on `map` ([#4874](https://github.com/leanprover-community/mathlib/pull/4874))
I had a couple of expressions involving mapping matrices, that the simplifier didn't `simp` away. It turns out the missing lemmas already existed, just not with the correct form / hypotheses. So here they are.

### [2020-11-11 22:13:41](https://github.com/leanprover-community/mathlib/commit/67309a4)
refactor(group_theory/group_action): Break the file into three pieces ([#4936](https://github.com/leanprover-community/mathlib/pull/4936))
I found myself fighting import cycles when trying to define `has_scalar` instances in files that are early in the import tree.
By creating a separate `defs` file with minimal dependencies, this ought to become easier.
This also adds documentation.
None of the proofs or lemma statements have been touched.

### [2020-11-11 19:36:52](https://github.com/leanprover-community/mathlib/commit/743a104)
chore(algebra): trivial lemmas on powers ([#4977](https://github.com/leanprover-community/mathlib/pull/4977))

### [2020-11-11 18:01:44](https://github.com/leanprover-community/mathlib/commit/5f098cf)
chore(topology): 2 trivial lemmas ([#4968](https://github.com/leanprover-community/mathlib/pull/4968))

### [2020-11-11 15:13:36](https://github.com/leanprover-community/mathlib/commit/d4aabf9)
doc(type_classes): Explain the use of {} instance arguments ([#4976](https://github.com/leanprover-community/mathlib/pull/4976))
Closes gh-4660

### [2020-11-11 13:39:21](https://github.com/leanprover-community/mathlib/commit/60234d1)
chore(algebra/archimedean): add `exists_pow_lt_of_lt_1` ([#4970](https://github.com/leanprover-community/mathlib/pull/4970))

### [2020-11-11 13:39:18](https://github.com/leanprover-community/mathlib/commit/4bf7ae4)
refactor(analysis/normed_space): use `lt` in rescale_to_shell, DRY ([#4969](https://github.com/leanprover-community/mathlib/pull/4969))
* Use strict inequality for the upper bound in `rescale_to_shell`.
* Deduplicate some proofs about operator norm.
* Add `linear_map.bound_of_shell`, `continuous_linear_map.op_norm_le_of_shell`, and `continuous_linear_map.op_norm_le_of_shell'`.

### [2020-11-11 13:39:16](https://github.com/leanprover-community/mathlib/commit/e1560a3)
feat(measure_theory/borel_space): continuity set of a function is measurable ([#4967](https://github.com/leanprover-community/mathlib/pull/4967))
* Move the definition of `is_Gδ` and basic lemmas to a separate file.
* Prove that `{x | continuous_at f x}` is a Gδ set provided that the
  codomain is a uniform space with countable basis of the uniformity
  filter (e.g., an `emetric_space`). In particular, this set is
  measurable.
* Rename `nhds_le_uniformity` to `supr_nhds_le_uniformity`.
* Add new `nhds_le_uniformity` without `⨆` in the statement.
* Add `uniform.continuous_at_iff_prod`.

### [2020-11-11 10:50:27](https://github.com/leanprover-community/mathlib/commit/02cdc33)
chore(algebra/group/hom): Add missing simp lemmas ([#4958](https://github.com/leanprover-community/mathlib/pull/4958))
These are named in the same pattern as `linear_map.to_add_monoid_hom_coe`

### [2020-11-11 10:50:25](https://github.com/leanprover-community/mathlib/commit/3d6291e)
chore(algebra/group/with_one): Use bundled morphisms ([#4957](https://github.com/leanprover-community/mathlib/pull/4957))
The comment "We have no bundled semigroup homomorphisms" has become false, these exist as `mul_hom`.
This also adds `with_one.coe_mul_hom` and `with_zero.coe_add_hom`

### [2020-11-11 08:22:46](https://github.com/leanprover-community/mathlib/commit/f30200e)
refactor(algebra/free_algebra): Make `lift` an equiv ([#4908](https://github.com/leanprover-community/mathlib/pull/4908))
This can probably lead to some API cleanup down the line

### [2020-11-11 01:33:41](https://github.com/leanprover-community/mathlib/commit/c20ecef)
chore(scripts): update nolints.txt ([#4965](https://github.com/leanprover-community/mathlib/pull/4965))
I am happy to remove some nolints for you!

### [2020-11-10 23:30:00](https://github.com/leanprover-community/mathlib/commit/5c9e3ef)
feat(ring_theory/adjoin_root): Dimension of adjoin_root ([#4830](https://github.com/leanprover-community/mathlib/pull/4830))
Adds `adjoin_root.degree_lt_linear_equiv`, the restriction of `adjoin_root.mk f`
to the polynomials of degree less than `f`, viewed as a isomorphism between
vector spaces over `K` and uses it to prove that `adjoin_root f` has dimension
`f.nat_degree`. Also renames `adjoin_root.alg_hom` to `adjoin_root.lift_hom`.

### [2020-11-10 20:04:41](https://github.com/leanprover-community/mathlib/commit/19bcf65)
chore(data/set/basic): Simp `(⊤ : set α)` to `set.univ` ([#4963](https://github.com/leanprover-community/mathlib/pull/4963))

### [2020-11-10 11:25:41](https://github.com/leanprover-community/mathlib/commit/d3fff8a)
feat(data/fin): define `fin.insert_nth` ([#4947](https://github.com/leanprover-community/mathlib/pull/4947))
Also rename `fin.succ_above_descend` to `fin.succ_above_pred_above`.

### [2020-11-10 11:25:39](https://github.com/leanprover-community/mathlib/commit/ecbcd38)
feat(category_theory/closed): cartesian closed category with zero object is trivial ([#4924](https://github.com/leanprover-community/mathlib/pull/4924))

### [2020-11-10 10:21:55](https://github.com/leanprover-community/mathlib/commit/55a28c1)
feat(ring_theory/witt_vector/mul_p): multiplication by p as operation on witt vectors ([#4837](https://github.com/leanprover-community/mathlib/pull/4837))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-11-10 08:10:37](https://github.com/leanprover-community/mathlib/commit/34b7361)
feat(algebra/*): Add ring instances to clifford_algebra and exterior_algebra ([#4916](https://github.com/leanprover-community/mathlib/pull/4916))
To do this, this removes the `irreducible` attributes.
These attributes were present to try and "insulate" the quotient / generator based definitions, and force downstream proofs to use the universal property.
Unfortunately, this irreducibility created massive headaches in typeclass resolution, and the tradeoff for neatness vs usability just isn't worth it.
If someone wants to add back the `irreducible` attributes in future, they now have test-cases that force them not to break the `ring` instances when doing so.

### [2020-11-10 01:07:17](https://github.com/leanprover-community/mathlib/commit/1ada09b)
chore(scripts): update nolints.txt ([#4961](https://github.com/leanprover-community/mathlib/pull/4961))
I am happy to remove some nolints for you!

### [2020-11-09 22:52:35](https://github.com/leanprover-community/mathlib/commit/e8758ae)
feat(measure_theory/*): a few lemmas about `(is_)measurable` in `Π i, π i` ([#4948](https://github.com/leanprover-community/mathlib/pull/4948))

### [2020-11-09 13:01:10](https://github.com/leanprover-community/mathlib/commit/09afb04)
feat(ring_theory/polynomial/content): Gauss's Lemma (irreducibility criterion) ([#4861](https://github.com/leanprover-community/mathlib/pull/4861))
Proves that a primitive polynomial is irreducible iff it is irreducible over the fraction field

### [2020-11-09 10:48:50](https://github.com/leanprover-community/mathlib/commit/fdbfe75)
chore(group_theory/group_action): Rename some group_action lemmas ([#4946](https://github.com/leanprover-community/mathlib/pull/4946))
This renames
* These lemmas about `group α`, for consistency with `smul_neg` etc, which are in the global scope:
  * `mul_action.inv_smul_smul` → `inv_smul_smul`
  * `mul_action.smul_inv_smul` → `smul_inv_smul`
  * `mul_action.inv_smul_eq_iff` → `inv_smul_eq_iff`
  * `mul_action.eq_inv_smul_iff` → `eq_inv_smul_iff`
* These lemmas about `group_with_zero α`, for consistency with `smul_inv_smul'` etc, which have trailing `'`s (and were added in [#2693](https://github.com/leanprover-community/mathlib/pull/2693), while the `'`-less ones were added later):
  * `inv_smul_eq_iff` → `inv_smul_eq_iff'`
  * `eq_inv_smul_iff` → `eq_inv_smul_iff'`

### [2020-11-09 05:45:56](https://github.com/leanprover-community/mathlib/commit/22b61b2)
feat(topology/subset_properties): separated of discrete ([#4952](https://github.com/leanprover-community/mathlib/pull/4952))
As [requested on Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/totally.20disconnected.20of.20discrete/near/216021581).

### [2020-11-09 03:25:54](https://github.com/leanprover-community/mathlib/commit/e1c333d)
chore(data/finset/basic): remove inter_eq_sdiff_sdiff ([#4953](https://github.com/leanprover-community/mathlib/pull/4953))
This is a duplicate of sdiff_sdiff_self_left

### [2020-11-09 00:48:26](https://github.com/leanprover-community/mathlib/commit/40f673e)
feat(data/set/intervals/pi): lemmas about intervals in `Π i, π i` ([#4951](https://github.com/leanprover-community/mathlib/pull/4951))
Also add missing lemmas `Ixx_mem_nhds` and lemmas `pi_Ixx_mem_nhds`.
For each `pi_Ixx_mem_nhds` I add a non-dependent version
`pi_Ixx_mem_nhds'` because sometimes Lean fails to unify different
instances while trying to apply the dependent version to `ι → ℝ`.

### [2020-11-08 18:51:05](https://github.com/leanprover-community/mathlib/commit/dcb8576)
chore(data/finset/basic): trivial simp lemmas ([#4950](https://github.com/leanprover-community/mathlib/pull/4950))

### [2020-11-08 18:51:03](https://github.com/leanprover-community/mathlib/commit/de2f1b2)
feat(data/set/intervals/basic): collection of lemmas of the form I??_of_I?? ([#4918](https://github.com/leanprover-community/mathlib/pull/4918))
Some propositions about intervals that I thought may be useful (despite their simplicity).

### [2020-11-08 16:26:23](https://github.com/leanprover-community/mathlib/commit/14a7c39)
chore(data/finset/basic): use `has_coe_t` for coercion of `finset` to `set` ([#4917](https://github.com/leanprover-community/mathlib/pull/4917))

### [2020-11-08 01:11:01](https://github.com/leanprover-community/mathlib/commit/26e4f15)
chore(scripts): update nolints.txt ([#4944](https://github.com/leanprover-community/mathlib/pull/4944))
I am happy to remove some nolints for you!

### [2020-11-07 21:27:41](https://github.com/leanprover-community/mathlib/commit/e7d40ef)
refactor(*): Move an instance to a more appropriate file ([#4939](https://github.com/leanprover-community/mathlib/pull/4939))
In its former location, this instance related neither to the section it was the sole resident of, nor even to the file.

### [2020-11-07 20:15:40](https://github.com/leanprover-community/mathlib/commit/5fed35b)
chore(docs/100): fix typo ([#4937](https://github.com/leanprover-community/mathlib/pull/4937))

### [2020-11-07 20:15:38](https://github.com/leanprover-community/mathlib/commit/c2ab384)
feat(category_theory/limits/preserves): convenience defs for things already there ([#4933](https://github.com/leanprover-community/mathlib/pull/4933))

### [2020-11-07 19:06:12](https://github.com/leanprover-community/mathlib/commit/9a0ba08)
feat(category_theory/limits/preserves): transfer preserving limits through nat iso ([#4932](https://github.com/leanprover-community/mathlib/pull/4932))
- Move two defs higher in the file
- Shorten some proofs using newer lemmas
- Show that we can transfer preservation of limits through natural isomorphism in the functor.

### [2020-11-07 19:06:10](https://github.com/leanprover-community/mathlib/commit/c494db5)
feat(category_theory/limits/shapes/equalizers): equalizer comparison map ([#4927](https://github.com/leanprover-community/mathlib/pull/4927))

### [2020-11-07 18:00:08](https://github.com/leanprover-community/mathlib/commit/11368e1)
feat(category_theory/limits/preserves): transfer reflecting limits through nat iso ([#4934](https://github.com/leanprover-community/mathlib/pull/4934))

### [2020-11-07 08:45:59](https://github.com/leanprover-community/mathlib/commit/655b617)
feat(category_theory/limits/preserves/shapes/products): preserve products ([#4857](https://github.com/leanprover-community/mathlib/pull/4857))
A smaller part of [#4716](https://github.com/leanprover-community/mathlib/pull/4716), for just products.
This also renames the file `preserves/shapes.lean` to `preserves/shapes/products.lean`, since I want a similar API for other special shapes and it'd get too big otherwise. 
Of the declarations which were already present: `preserves_products_iso`, `preserves_products_iso_hom_π`, `map_lift_comp_preserves_products_iso_hom`, the first is still there but with weaker assumptions, and the other two are now provable by simp (under weaker assumptions again).

### [2020-11-07 01:11:14](https://github.com/leanprover-community/mathlib/commit/c4e8d74)
chore(scripts): update nolints.txt ([#4926](https://github.com/leanprover-community/mathlib/pull/4926))
I am happy to remove some nolints for you!

### [2020-11-06 20:34:51](https://github.com/leanprover-community/mathlib/commit/8ba0dde)
chore(data/polynomial/monic): speedup next_coeff_mul ([#4920](https://github.com/leanprover-community/mathlib/pull/4920))

### [2020-11-06 20:34:49](https://github.com/leanprover-community/mathlib/commit/e0cf0d3)
fix(meta/expr): adjust is_likely_generated_binder_name to lean[#490](https://github.com/leanprover-community/mathlib/pull/490) ([#4915](https://github.com/leanprover-community/mathlib/pull/4915))
Lean PR 490 changed Lean's strategy for generating binder names. This PR adapts
`name.is_likely_generated_binder_name`, which checks whether a binder name was
likely generated by Lean (rather than given by the user).

### [2020-11-06 19:17:20](https://github.com/leanprover-community/mathlib/commit/b6b41c1)
feat(category_theory/limits/creates): composition creates limits ([#4922](https://github.com/leanprover-community/mathlib/pull/4922))

### [2020-11-06 19:17:18](https://github.com/leanprover-community/mathlib/commit/4f673bd)
feat(category_theory/limits/preserves): instances for composition preserving limits ([#4921](https://github.com/leanprover-community/mathlib/pull/4921))
A couple of quick instances. I'm pretty sure these instances don't cause clashes since they're for subsingleton classes, and they shouldn't cause loops since they're just other versions of instances already there.

### [2020-11-06 16:08:51](https://github.com/leanprover-community/mathlib/commit/bddc5c9)
feat(category_theory/limits): equivalence creates colimits ([#4923](https://github.com/leanprover-community/mathlib/pull/4923))
Dualises and tidy proofs already there

### [2020-11-06 14:57:51](https://github.com/leanprover-community/mathlib/commit/91f8e68)
feat(src/ring_theory/polynomial/cyclotomic): cyclotomic polynomials ([#4914](https://github.com/leanprover-community/mathlib/pull/4914))
I have added some basic results about cyclotomic polynomials. I defined them as the polynomial, with integer coefficients, that lifts the complex polynomial ∏ μ in primitive_roots n ℂ, (X - C μ). I proved that the degree of cyclotomic n is totient n and the product formula for X ^ n - 1. I plan to prove the irreducibility in the near future.
This was in [4869](https://github.com/leanprover-community/mathlib/pull/4869) before I splitted that PR. Compared to it, I added the definition of `cyclotomic n R` for any ring `R` (still using the polynomial with coefficients in `ℤ`) and some easy lemmas, especially `cyclotomic_of_ring_hom`, `cyclotomic'_eq_X_pow_sub_one_div` `cyclotomic_eq_X_pow_sub_one_div`, and `cycl_eq_cycl'`.

### [2020-11-06 10:17:40](https://github.com/leanprover-community/mathlib/commit/747aaae)
chore(algebra/lie/basic): Add some missing simp lemmas about A →ₗ⁅R⁆ B ([#4912](https://github.com/leanprover-community/mathlib/pull/4912))
These are mostly inspired by lemmas in linear_map. All the proofs are either `rfl` or copied from a proof for `linear_map`.

### [2020-11-06 01:10:55](https://github.com/leanprover-community/mathlib/commit/fd3212c)
chore(scripts): update nolints.txt ([#4919](https://github.com/leanprover-community/mathlib/pull/4919))
I am happy to remove some nolints for you!

### [2020-11-05 18:57:18](https://github.com/leanprover-community/mathlib/commit/a12d677)
feat(ring_theory): define a `power_basis` structure ([#4905](https://github.com/leanprover-community/mathlib/pull/4905))
This PR defines a structure `power_basis`. If `S` is an `R`-algebra, `pb : power_basis R S` states that `S` (as `R`-module) has basis `1`, `pb.gen`, ..., `pb.gen ^ (pb.dim - 1)`. Since there are multiple possible choices, I decided to not make it a typeclass.
Three constructors for `power_basis` are included: `algebra.adjoin`, `intermediate_field.adjoin` and `adjoin_root`. Each of these is of the form `power_basis K _` with `K` a field, at least until `minimal_polynomial` gets better support for rings.

### [2020-11-05 17:06:55](https://github.com/leanprover-community/mathlib/commit/246df99)
feat(category_theory/limits): Any small complete category is a preorder ([#4907](https://github.com/leanprover-community/mathlib/pull/4907))
Show that any small complete category has subsingleton homsets.
Not sure if this is useful for anything - maybe it shouldn't be an instance

### [2020-11-05 17:06:53](https://github.com/leanprover-community/mathlib/commit/4024597)
feat(category_theory/limits/presheaf): left adjoint if preserves colimits ([#4896](https://github.com/leanprover-community/mathlib/pull/4896))

### [2020-11-05 17:06:51](https://github.com/leanprover-community/mathlib/commit/6a1ce57)
chore(algebra/module/linear_map): Derive linear_map from mul_action_hom ([#4888](https://github.com/leanprover-community/mathlib/pull/4888))
Note that this required some stuff about polynomials to move to cut import cycles.

### [2020-11-05 15:43:26](https://github.com/leanprover-community/mathlib/commit/2f07ff2)
chore(topology/metric_space): more `norm_cast` lemmas, golf proofs ([#4911](https://github.com/leanprover-community/mathlib/pull/4911))

### [2020-11-05 01:07:58](https://github.com/leanprover-community/mathlib/commit/834d491)
chore(scripts): update nolints.txt ([#4910](https://github.com/leanprover-community/mathlib/pull/4910))
I am happy to remove some nolints for you!

### [2020-11-04 21:59:56](https://github.com/leanprover-community/mathlib/commit/189063b)
chore(data/W): rename `W` to `W_type` ([#4909](https://github.com/leanprover-community/mathlib/pull/4909))
Having a single character identifier in the root namespace is inconvenient.
closes leanprover-community/doc-gen[#83](https://github.com/leanprover-community/mathlib/pull/83)

### [2020-11-04 18:37:41](https://github.com/leanprover-community/mathlib/commit/5a61ef1)
feat(ring_theory/witt_vector/teichmuller): Teichmuller representatives ([#4690](https://github.com/leanprover-community/mathlib/pull/4690))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-11-04 16:04:42](https://github.com/leanprover-community/mathlib/commit/211b0c0)
feat(logic/basic): forall2_congr lemmas ([#4904](https://github.com/leanprover-community/mathlib/pull/4904))
Some helpful lemmas for working with quantifiers, just other versions of what's already there.

### [2020-11-04 16:04:40](https://github.com/leanprover-community/mathlib/commit/0081a5a)
feat(ring_theory/algebraic): if `L / K` is algebraic, then the subalgebras are fields ([#4903](https://github.com/leanprover-community/mathlib/pull/4903))

### [2020-11-04 14:06:15](https://github.com/leanprover-community/mathlib/commit/e303a7d)
feat(linear_algebra/tensor_product): tensoring linear maps with modules ([#4771](https://github.com/leanprover-community/mathlib/pull/4771))

### [2020-11-04 08:09:46](https://github.com/leanprover-community/mathlib/commit/6f72c22)
chore(data/finset): add a few lemmas ([#4901](https://github.com/leanprover-community/mathlib/pull/4901))

### [2020-11-04 08:09:42](https://github.com/leanprover-community/mathlib/commit/0877077)
chore(analysis/calculus/times_cont_diff): a few missing lemmas ([#4900](https://github.com/leanprover-community/mathlib/pull/4900))
* add `times_cont_diff_within_at_iff_forall_nat_le` and `times_cont_diff_on_iff_forall_nat_le`;
* add `times_cont_diff_on_all_iff_nat` and `times_cont_diff_all_iff_nat`;
* rename `times_cont_diff_at.differentiable` to `times_cont_diff_at.differentiable_at`;
* add `times_cont_diff.div_const`;
* add `times_cont_diff_succ_iff_deriv`
* move some `of_le` lemmas up to support minor golfing of proofs.

### [2020-11-04 08:09:40](https://github.com/leanprover-community/mathlib/commit/beb6831)
feat(analysis/calculus/times_cont_diff): add `restrict_scalars` ([#4899](https://github.com/leanprover-community/mathlib/pull/4899))
Add `restrict_scalars` lemmas to `has_ftaylor_series_up_to_on`,
`times_cont_diff_within_at`, `times_cont_diff_on`,
`times_cont_diff_at`, and `times_cont_diff`.

### [2020-11-04 08:09:38](https://github.com/leanprover-community/mathlib/commit/b7991c0)
feat(category_theory/limits/cones): map_cone and postcompose lemmas ([#4894](https://github.com/leanprover-community/mathlib/pull/4894))

### [2020-11-04 08:09:36](https://github.com/leanprover-community/mathlib/commit/7d6f37d)
feat(category_theory/closed/cartesian): product preserves colimits ([#4893](https://github.com/leanprover-community/mathlib/pull/4893))

### [2020-11-04 08:09:35](https://github.com/leanprover-community/mathlib/commit/e1d60fd)
feat(data/equiv): exists unique congr ([#4890](https://github.com/leanprover-community/mathlib/pull/4890))

### [2020-11-04 08:09:31](https://github.com/leanprover-community/mathlib/commit/d88042c)
feat(order/filter/at_top_bot): lemmas about `map/comap` of `at_top`/`at_bot` ([#4878](https://github.com/leanprover-community/mathlib/pull/4878))
* Redefine `at_top`/`at_bot` using `Ici`/`Iic`.
* Add lemmas about `map`/`comap` of `at_top`/`at_bot` under `coe : s → α`, where `s` is one of `Ici a`, `Iic a`, `Ioi a`, `Iio a`.

### [2020-11-04 05:43:18](https://github.com/leanprover-community/mathlib/commit/7ab3ca8)
feat(data/quaternion): define quaternions and prove some basic properties ([#2339](https://github.com/leanprover-community/mathlib/pull/2339))

### [2020-11-04 01:36:53](https://github.com/leanprover-community/mathlib/commit/16e3871)
chore(scripts): update nolints.txt ([#4898](https://github.com/leanprover-community/mathlib/pull/4898))
I am happy to remove some nolints for you!

### [2020-11-04 00:20:10](https://github.com/leanprover-community/mathlib/commit/23a2767)
feat(category_theory/yoneda): type level yoneda equivalence ([#4889](https://github.com/leanprover-community/mathlib/pull/4889))
Broken off from [#4608](https://github.com/leanprover-community/mathlib/pull/4608).

### [2020-11-03 21:30:18](https://github.com/leanprover-community/mathlib/commit/505097f)
feat(order): countable categoricity of dense linear orders ([#2860](https://github.com/leanprover-community/mathlib/pull/2860))
We construct an order isomorphism between any two countable, nonempty, dense linear orders without endpoints, using the back-and-forth method.

### [2020-11-03 20:37:43](https://github.com/leanprover-community/mathlib/commit/712a0b7)
chore(algebra/lie): adjoint rep of lie algebra uses lowercase `ad` ([#4891](https://github.com/leanprover-community/mathlib/pull/4891))
The uppercase is for Lie groups

### [2020-11-03 17:56:57](https://github.com/leanprover-community/mathlib/commit/e88a5bb)
feat(*): assorted prereqs for cyclotomic polynomials ([#4887](https://github.com/leanprover-community/mathlib/pull/4887))
This is hopefully my last preparatory PR for cyclotomic polynomials. It was in [4869](https://github.com/leanprover-community/mathlib/pull/4869) .

### [2020-11-03 17:56:54](https://github.com/leanprover-community/mathlib/commit/b37d4a3)
feat(category_theory/limits/types): ext iff lemma ([#4883](https://github.com/leanprover-community/mathlib/pull/4883))
A little lemma which sometimes makes it easier to work with limits in type.

### [2020-11-03 17:56:52](https://github.com/leanprover-community/mathlib/commit/6bed7d4)
fix(tactic/interactive): issue where long term tooltips break layout ([#4882](https://github.com/leanprover-community/mathlib/pull/4882))
For issue description see https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/widget.20v.20long.20term.20names
Basically the problem is that if the little 'argument pills' in the tooltip are too long, then there is a fight between the expression linebreaking algorithm and the pill linebreaking algorithm and something gets messed up.
A first attempt to fix this is to use flexbox for laying out the pills.
Still some issues with expressions linebreaking weirdly to sort out before this should be pulled.
Need to find a mwe that I can put in a file without a huge dependency tree.

### [2020-11-03 17:56:50](https://github.com/leanprover-community/mathlib/commit/4f8c490)
feat(tactic/mk_iff_of_inductive_prop): mk_iff attribute ([#4863](https://github.com/leanprover-community/mathlib/pull/4863))
This attribute should make `mk_iff_of_inductive_prop` easier to use.

### [2020-11-03 15:50:10](https://github.com/leanprover-community/mathlib/commit/918e28c)
feat(category_theory/limits/types): explicit description of equalizers in Type ([#4880](https://github.com/leanprover-community/mathlib/pull/4880))
Cf https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/concrete.20limits.20in.20Type.
Adds equivalent conditions for a fork in Type to be a equalizer, and a proof that the subtype is an equalizer.
(cc: @adamtopaz @kbuzzard)

### [2020-11-03 15:50:08](https://github.com/leanprover-community/mathlib/commit/34c3668)
chore(data/set/intervals/ord_connected): make it more useful as a typeclass ([#4879](https://github.com/leanprover-community/mathlib/pull/4879))
* Add `protected lemma set.Icc_subset` that looks for
  `ord_connected s` instance.
* Add `instance` versions to more lemmas.
* Add `ord_connected_pi`.

### [2020-11-03 15:50:06](https://github.com/leanprover-community/mathlib/commit/9851a88)
feat(*/multilinear): define `(continuous_)multilinear_map.restrict_scalars` ([#4872](https://github.com/leanprover-community/mathlib/pull/4872))
I'm going to use these definitions to prove
`times_cont_diff_at.restrict_scalars` etc.

### [2020-11-03 15:50:04](https://github.com/leanprover-community/mathlib/commit/63d109f)
chore(category_theory/limits): Use `lim_map` over `lim.map` ([#4856](https://github.com/leanprover-community/mathlib/pull/4856))
Modify the simp-normal form for `lim.map` to be `lim_map` instead, and express lemmas in terms of `lim_map` instead, as well as use it in special shapes so that the assumptions can be weakened.

### [2020-11-03 15:50:02](https://github.com/leanprover-community/mathlib/commit/b26fc59)
feat(category_theory/limits/shapes/products): pi comparison morphism ([#4855](https://github.com/leanprover-community/mathlib/pull/4855))

### [2020-11-03 14:17:25](https://github.com/leanprover-community/mathlib/commit/5275628)
feat(algebra/operations): add three lemmas ([#4864](https://github.com/leanprover-community/mathlib/pull/4864))
Add lemmas `one_le_inv`, `self_le_self_inv` and `self_inv_le_one`

### [2020-11-03 09:26:45](https://github.com/leanprover-community/mathlib/commit/c2b6220)
feat(linear_algebra/matrix): `det (reindex e e A) = det A` ([#4875](https://github.com/leanprover-community/mathlib/pull/4875))
This PR includes four flavours of this lemma: `det_reindex_self'` is the `simp` lemma that doesn't include the actual term `reindex` as a subexpression (because that would be already `simp`ed away by `reindex_apply`). `det_reindex_self`, `det_reindex_linear_equiv_self` and `det_reindex_alg_equiv` include their respective function in the lemma statement.

### [2020-11-03 01:06:41](https://github.com/leanprover-community/mathlib/commit/57ee216)
chore(scripts): update nolints.txt ([#4884](https://github.com/leanprover-community/mathlib/pull/4884))
I am happy to remove some nolints for you!

### [2020-11-02 22:24:06](https://github.com/leanprover-community/mathlib/commit/0e4f8f4)
chore(scripts): typo in yaml_check ([#4881](https://github.com/leanprover-community/mathlib/pull/4881))

### [2020-11-02 22:24:05](https://github.com/leanprover-community/mathlib/commit/dae87bc)
chore(data/finsupp/basic): Remove finsupp.leval which duplicates finsupp.lapply ([#4876](https://github.com/leanprover-community/mathlib/pull/4876))

### [2020-11-02 20:27:42](https://github.com/leanprover-community/mathlib/commit/5334f48)
chore(data/fintype/card): add a few lemmas ([#4877](https://github.com/leanprover-community/mathlib/pull/4877))
Prove a few versions of `(∏ i in s, f i) * (∏ i in sᶜ, f i) = ∏ i, f i`

### [2020-11-02 18:45:02](https://github.com/leanprover-community/mathlib/commit/13a104d)
chore({data,linear_algebra}/dfinsupp): Move linear_algebra stuff to its own file ([#4873](https://github.com/leanprover-community/mathlib/pull/4873))
This makes the layout of files about `dfinsupp` resemble those of `finsupp` a little better.
This also:
* Renames type arguments to match the names of those in finsupp
* Adjusts argument explicitness to match those in finsupp
* Adds `dfinsupp.lapply` to match `finsupp.lapply`

### [2020-11-02 17:17:23](https://github.com/leanprover-community/mathlib/commit/6587e84)
feat(algebra/algebra/subalgebra): subalgebras, when seen as submodules, are idempotent ([#4854](https://github.com/leanprover-community/mathlib/pull/4854))

### [2020-11-02 14:44:02](https://github.com/leanprover-community/mathlib/commit/0aa6aed)
chore(order/basic): move `strict_mono_coe`to `subtype` NS ([#4870](https://github.com/leanprover-community/mathlib/pull/4870))
Also add `subtype.mono_coe`

### [2020-11-02 04:55:03](https://github.com/leanprover-community/mathlib/commit/309df10)
refactor(data/list/basic,...): more explicit args ([#4866](https://github.com/leanprover-community/mathlib/pull/4866))
This makes the `p` in most lemmas involving the following functions explicit, following the usual explicitness conventions:
- `list.filter`,
- `list.countp`,
- `list.take_while`,
- `multiset.filter`,
- `multiset.countp`,
- `finset.filter`

### [2020-11-02 04:55:01](https://github.com/leanprover-community/mathlib/commit/556079b)
feat(ring_theory/polynomial/content): monic polynomials are primitive ([#4862](https://github.com/leanprover-community/mathlib/pull/4862))
Adds the lemma `monic.is_primitive`.

### [2020-11-02 02:10:46](https://github.com/leanprover-community/mathlib/commit/ecdc319)
fix(tactic/simpa): reflect more simp errors ([#4865](https://github.com/leanprover-community/mathlib/pull/4865))
fixes [#2061](https://github.com/leanprover-community/mathlib/pull/2061)

### [2020-11-02 01:12:55](https://github.com/leanprover-community/mathlib/commit/7c8868d)
chore(scripts): update nolints.txt ([#4868](https://github.com/leanprover-community/mathlib/pull/4868))
I am happy to remove some nolints for you!

### [2020-11-01 17:55:51](https://github.com/leanprover-community/mathlib/commit/4aa087a)
doc(*): work around markdown2 bug for now ([#4842](https://github.com/leanprover-community/mathlib/pull/4842))

### [2020-11-01 01:07:16](https://github.com/leanprover-community/mathlib/commit/7a624b8)
chore(scripts): update nolints.txt ([#4860](https://github.com/leanprover-community/mathlib/pull/4860))
I am happy to remove some nolints for you!