### [2020-05-31 20:01:07](https://github.com/leanprover-community/mathlib/commit/d3fc918)
chore(scripts): update nolints.txt ([#2892](https://github.com/leanprover-community/mathlib/pull/2892))
I am happy to remove some nolints for you!

### [2020-05-31 18:58:17](https://github.com/leanprover-community/mathlib/commit/1fd5195)
chore(data/equiv/mul_add): review ([#2874](https://github.com/leanprover-community/mathlib/pull/2874))
* make `mul_aut` and `add_aut` reducible to get `coe_fn`
* add some `coe_*` lemmas

### [2020-05-31 17:05:57](https://github.com/leanprover-community/mathlib/commit/7c7e866)
chore(*): update to lean 3.15.0 ([#2851](https://github.com/leanprover-community/mathlib/pull/2851))
The main effect for mathlib comes from https://github.com/leanprover-community/lean/pull/282, which changes the elaboration strategy for structure instance literals (`{ foo := 42 }`).  There are two points where we need to pay attention:
1. Avoid sourcing (`{ ..e }` where e.g. `e : euclidean_domain α`) for fields like `add`, `mul`, `zero`, etc.  Instead write `{ add := (+), mul := (*), zero := 0, ..e }`.  The reason is that `{ ..e }` is equivalent to `{ mul := euclidean_domain.mul, ..e }`.  And `euclidean_domain.mul` should never be mentioned.
I'm not completely sure if this issue remains visible once the structure literal has been elaborated, but this hasn't changed since 3.14.  For now, my advice is: if you get weird errors like "cannot unify `a * b` and `?m_1 * ?m_2` in a structure literal, add `mul := (*)`.
2. `refine { le := (≤), .. }; simp` is slower.  This is because references to `(≤)` are no longer reduced to `le` in the subgoals.  If a subgoal like `a ≤ b → b ≤ a → a = b` was stated for preorders (because `partial_order` extends `preorder`), then the `(≤)` will contain a `preorder` subterm.  This subterm also contains other subgoals (proofs of reflexivity and transitivity).  Therefore the goals are larger than you might expect:
```
∀ (a b : α),
    @has_le.le.{u} α
      (@preorder.to_has_le.{u} α
         (@preorder.mk.{u} α le (@lattice.lt._default.{u} α le)
            (@conditionally_complete_lattice.copy._aux_1.{u} α c le eq_le sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf)
            (@conditionally_complete_lattice.copy._aux_2.{u} α c le eq_le sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf)
            (λ (a b : α), iff.refl (@has_lt.lt.{u} α (@has_lt.mk.{u} α (@lattice.lt._default.{u} α le)) a b))))
      a
      b →
    @has_le.le.{u} α
      (@preorder.to_has_le.{u} α
         (@preorder.mk.{u} α le (@lattice.lt._default.{u} α le)
            (@conditionally_complete_lattice.copy._aux_1.{u} α c le eq_le sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf)
            (@conditionally_complete_lattice.copy._aux_2.{u} α c le eq_le sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf)
            (λ (a b : α), iff.refl (@has_lt.lt.{u} α (@has_lt.mk.{u} α (@lattice.lt._default.{u} α le)) a b))))
      b
      a →
    @eq.{u+1} α a b
```
Advice: in cases such as this, try `refine { le := (≤), .. }; abstract { simp }` to reduce the size of the (dependent) subgoals.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Lean.203.2E15.2E0).

### [2020-05-31 15:03:10](https://github.com/leanprover-community/mathlib/commit/25fc0a8)
feat(field_theory/splitting_field): lemmas ([#2887](https://github.com/leanprover-community/mathlib/pull/2887))

### [2020-05-31 06:22:54](https://github.com/leanprover-community/mathlib/commit/13b34b3)
chore(*): split long lines ([#2883](https://github.com/leanprover-community/mathlib/pull/2883))
Also move docs for `control/fold` from a comment to a module docstring.

### [2020-05-31 04:59:04](https://github.com/leanprover-community/mathlib/commit/a285049)
chore(algebra/group_hom): rename `add_monoid.smul` to `nsmul` ([#2861](https://github.com/leanprover-community/mathlib/pull/2861))
Also drop `•` as a notation for two `smul`s  declared in this file,
use `•ℕ` and `•ℤ` instead.
This way one can immediately see that a lemma uses `nsmul`/`gsmul`, not `has_scalar.smul`.

### [2020-05-31 01:56:14](https://github.com/leanprover-community/mathlib/commit/28e79d4)
chore(data/set/basic): add some lemmas to `function.surjective` ([#2876](https://github.com/leanprover-community/mathlib/pull/2876))
This way they can be used with dot notation. Also rename
`set.surjective_preimage` to
`function.surjective.injective_preimage`. I think that the old name
was misleading.

### [2020-05-31 01:56:12](https://github.com/leanprover-community/mathlib/commit/297806e)
feat(topology/homeomorph): sum_prod_distrib ([#2870](https://github.com/leanprover-community/mathlib/pull/2870))
Also modify the `inv_fun` of `equiv.sum_prod_distrib` to have
more useful definitional behavior. This also simplifies
`measurable_equiv.sum_prod_distrib`.

### [2020-05-30 22:43:58](https://github.com/leanprover-community/mathlib/commit/0827a30)
feat(tactic/noncomm_ring): add noncomm_ring tactic ([#2858](https://github.com/leanprover-community/mathlib/pull/2858))
Fixes https://github.com/leanprover-community/mathlib/issues/2727

### [2020-05-30 21:15:08](https://github.com/leanprover-community/mathlib/commit/6e581ef)
chore(scripts): update nolints.txt ([#2878](https://github.com/leanprover-community/mathlib/pull/2878))
I am happy to remove some nolints for you!

### [2020-05-30 19:55:19](https://github.com/leanprover-community/mathlib/commit/c034b4c)
chore(order/bounds): +2 lemmas, fix a name ([#2877](https://github.com/leanprover-community/mathlib/pull/2877))

### [2020-05-30 19:08:27](https://github.com/leanprover-community/mathlib/commit/9d76ac2)
chore(scripts): update nolints.txt ([#2873](https://github.com/leanprover-community/mathlib/pull/2873))
I am happy to remove some nolints for you!

### [2020-05-30 18:01:32](https://github.com/leanprover-community/mathlib/commit/f05acc8)
feat(group_theory/group_action): orbit_equiv_quotient_stabilizer_symm_apply and docs ([#2864](https://github.com/leanprover-community/mathlib/pull/2864))

### [2020-05-30 16:24:08](https://github.com/leanprover-community/mathlib/commit/67f1951)
refactor(algebra/module): change module into an abbreviation for semimodule ([#2848](https://github.com/leanprover-community/mathlib/pull/2848))
The file `algebra/module.lean` contains the lines
```
There were several attempts to make `module` an abbreviation of `semimodule` but this makes
  class instance search too hard for Lean 3.
```
It turns out that this was too hard for Lean 3 until recently, but this is not too hard for Lean 3.14. This PR removes these two lines, and changes the files accordingly.
This means that the basic objects of linear algebra are now semimodules over semiring, making it possible to talk about matrices with natural number coefficients or apply general results on multilinear maps to get the binomial or the multinomial formula.
A linear map is now defined over semirings, between semimodules which are `add_comm_monoid`s. For some statements, you need to have an `add_comm_group`, and a `ring` or a `comm_semiring` or a `comm_ring`. I have not tried to lower the possible typeclass assumptions like this in all files, but I have done it carefully in the following files:
* `algebra/module`
* `linear_algebra/basic`
* `linear_algebra/multilinear`
* `topology/algebra/module`
* `topology/algebra/multilinear`
Other files can be optimised later in the same way when needed, but this PR is already big enough.
I have also fixed the breakage in all the other files. It was sometimes completely mysterious (in tensor products, I had to replace several times `linear_map.id.flip` with `linear_map.flip linear_map.id`), but globally all right. I have tweaked a few instance priorities to make sure that things don't go too bad: there are often additional steps in typeclass inference, going from `ring` to `semiring` and from `add_comm_group` to `add_comm_monoid`, so I have increased their priority (putting it strictly between 100 and 1000), and adjusted some other priorities to get more canonical instance paths, fixing some preexisting weirdnesses (notably in multilinear maps). One place where I really had to help Lean is with normed spaces of continuous multilinear maps, where instance search is just too big.
I am aware that this will be a nightmare to refer, but as often with big refactor it's an "all or nothing" PR, impossible to split in tiny pieces.

### [2020-05-30 15:05:49](https://github.com/leanprover-community/mathlib/commit/cc06d53)
feat(algebra/big_operators): prod_ne_zero ([#2863](https://github.com/leanprover-community/mathlib/pull/2863))

### [2020-05-30 13:12:33](https://github.com/leanprover-community/mathlib/commit/b40ac2a)
chore(topology): make topological_space fields protected ([#2867](https://github.com/leanprover-community/mathlib/pull/2867))
This uses the recent `protect_proj` attribute ([#2855](https://github.com/leanprover-community/mathlib/pull/2855)).

### [2020-05-30 07:33:44](https://github.com/leanprover-community/mathlib/commit/62cb7f2)
feat(geometry/euclidean): Euclidean space ([#2852](https://github.com/leanprover-community/mathlib/pull/2852))
Define Euclidean affine spaces (not necessarily finite-dimensional),
and a corresponding instance for the standard Euclidean space `fin n → ℝ`.
This just defines the type class and the instance, with some other
basic geometric definitions and results to be added separately once
this is in.
I haven't attempted to do anything about the `euclidean_space`
definition in geometry/manifold/real_instances.lean that comes with a
comment that it uses the wrong norm.  That might better be refactored
by someone familiar with the manifold code.
By defining Euclidean spaces such that they are defined to be metric
spaces, and providing an instance, this probably implicitly gives item
91 "The Triangle Inequality" from the 100-theorems list, if that's
taken to have a geometric interpretation as in the Coq version, but
it's not very clear how something implicit like that from various
different pieces of the library, and where the item on the list could
be interpreted in several different ways anyway, should be entered in
100.yaml.

### [2020-05-30 06:12:38](https://github.com/leanprover-community/mathlib/commit/74d446d)
feat(order/iterate): some inequalities on `f^[n] x` and `g^[n] x` ([#2859](https://github.com/leanprover-community/mathlib/pull/2859))

### [2020-05-30 04:46:16](https://github.com/leanprover-community/mathlib/commit/aa47bba)
feat(data/equiv): equiv_of_subsingleton_of_subsingleton ([#2856](https://github.com/leanprover-community/mathlib/pull/2856))

### [2020-05-30 00:45:00](https://github.com/leanprover-community/mathlib/commit/5455fe1)
chore(scripts): update nolints.txt ([#2862](https://github.com/leanprover-community/mathlib/pull/2862))
I am happy to remove some nolints for you!

### [2020-05-29 22:20:28](https://github.com/leanprover-community/mathlib/commit/f95e809)
chore(algebra): displace zero_ne_one_class with nonzero and make no_zero_divisors a Prop ([#2847](https://github.com/leanprover-community/mathlib/pull/2847))
- `[nonzero_semiring α]` becomes `[semiring α] [nonzero α]`
- `[nonzero_comm_semiring α]` becomes `[comm_semiring α] [nonzero α]`
- `[nonzero_comm_ring α]` becomes `[comm_ring α] [nonzero α]`
- `no_zero_divisors` is now a `Prop`
- `units.ne_zero` (originally for `domain`) merges into `units.coe_ne_zero` (originally for `nonzero_comm_semiring`)

### [2020-05-29 20:46:37](https://github.com/leanprover-community/mathlib/commit/b2f643e)
feat(dynamics/fixed_points): define `is_fixed_pt` ([#2857](https://github.com/leanprover-community/mathlib/pull/2857))
Define `function.is_fixed_pt` and prove some basic properties.

### [2020-05-29 16:24:04](https://github.com/leanprover-community/mathlib/commit/836184a)
feat(tactic/protect_proj): protect_proj attribute for structures ([#2855](https://github.com/leanprover-community/mathlib/pull/2855))
This attribute protect the projections of a structure that is being defined. 
There were some errors in Euclidean domain caused by `rw` using `euclidean_domain.mul_assoc` instead of `mul_assoc` because the `euclidean_domain` namespace was open. This fixes this problem, and makes the `group` and `ring` etc. namespaces more usable.

### [2020-05-29 16:24:02](https://github.com/leanprover-community/mathlib/commit/77674a0)
chore(category_theory): T50000 challenge ([#2840](https://github.com/leanprover-community/mathlib/pull/2840))
A lame effort at making something compile with `-T50000`. No actual speed improvement, just split up a definition into pieces.

### [2020-05-29 16:24:00](https://github.com/leanprover-community/mathlib/commit/07cdafe)
feat(tactic/with_local_reducibility): alter reducibility attributes locally ([#2820](https://github.com/leanprover-community/mathlib/pull/2820))

### [2020-05-29 14:48:35](https://github.com/leanprover-community/mathlib/commit/4a5799e)
feat(data/equiv/basic): subtype_prod_equiv_prod ([#2717](https://github.com/leanprover-community/mathlib/pull/2717))

### [2020-05-29 06:50:56](https://github.com/leanprover-community/mathlib/commit/b013b2d)
feat(ring_theory): define subsemirings ([#2837](https://github.com/leanprover-community/mathlib/pull/2837))
~~Depends on [#2836](https://github.com/leanprover-community/mathlib/pull/2836),~~ needs a better module docstring.
Some lemmas are missing, most notably `(subsemiring.closure s : set R) = add_submonoid.closure (submonoid.closure s)`.

### [2020-05-29 05:57:08](https://github.com/leanprover-community/mathlib/commit/6c046c7)
chore(data/setoid): split into `basic` and `partition` ([#2853](https://github.com/leanprover-community/mathlib/pull/2853))
The `basic` part has slightly fewer dependencies and `partition` part
is never used in `mathlib`.

### [2020-05-28 23:10:08](https://github.com/leanprover-community/mathlib/commit/543ae52)
feat(analysis/normed_space/add_torsor): normed_add_torsor ([#2814](https://github.com/leanprover-community/mathlib/pull/2814))
Define the metric space structure on torsors of additive normed group
actions.  The motivating case is Euclidean affine spaces.
See
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Some.20olympiad.20formalisations
for the discussion leading to this particular handling of the
distance.
Note: I'm not sure what the right way is to address the
dangerous_instance linter error "The following arguments become
metavariables. argument 1: (V : Type u_1)".

### [2020-05-28 13:26:09](https://github.com/leanprover-community/mathlib/commit/e9ba32d)
chore(scripts): update nolints.txt ([#2849](https://github.com/leanprover-community/mathlib/pull/2849))
I am happy to remove some nolints for you!

### [2020-05-28 11:54:54](https://github.com/leanprover-community/mathlib/commit/ca95726)
feat(algebra/free) additive versions, docs. ([#2755](https://github.com/leanprover-community/mathlib/pull/2755))
https://github.com/leanprover-community/mathlib/issues/930

### [2020-05-28 08:37:23](https://github.com/leanprover-community/mathlib/commit/cbf4740)
refactor(data/equiv/local_equiv): use dot notation for `eq_on_source` ([#2830](https://github.com/leanprover-community/mathlib/pull/2830))
Also reuse more lemmas from `data/set/function`.

### [2020-05-28 08:37:21](https://github.com/leanprover-community/mathlib/commit/28dc2ed)
fix(tactic/suggest): normalize synonyms uniformly in goal and lemma ([#2829](https://github.com/leanprover-community/mathlib/pull/2829))
This change is intended to make `library_search` and `suggest` a bit more robust in unfolding the types of the goal and lemma in order to determine which lemmas it will try to apply.
Before, there were two ad-hoc systems to map a head symbol to the name(s) that it should match, now there is only one ad-hoc function that does so.  As a consequence, `library_search` should be able to use a lemma with return type `a > b` to close the goal `b < a`, and use `lemma foo : p → false` to close the goal `¬ p`.
(The `>` normalization shouldn't "really" be needed if we all strictly followed the `gt_or_ge` linter but we don't and the failure has already caused confusion.)
[Discussion on Zulip starts here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/How.20to.20get.20familiar.20enough.20with.20Mathlib.20to.20use.20it/near/198746479)

### [2020-05-28 07:50:25](https://github.com/leanprover-community/mathlib/commit/005763e)
feat(linear_algebra/lagrange): Lagrange interpolation ([#2764](https://github.com/leanprover-community/mathlib/pull/2764))
Fixes [#2600](https://github.com/leanprover-community/mathlib/pull/2600).

### [2020-05-28 07:50:22](https://github.com/leanprover-community/mathlib/commit/fa371f7)
feat(linear_algebra/bilinear_form): introduce adjoints of linear maps ([#2746](https://github.com/leanprover-community/mathlib/pull/2746))
We also use this to define the Lie algebra structure on skew-adjoint
endomorphisms / matrices. The motivation is to enable us to define the
classical Lie algebras.

### [2020-05-28 07:02:07](https://github.com/leanprover-community/mathlib/commit/315ba3e)
feat(category_theory): show an epi regular mono is an iso ([#2781](https://github.com/leanprover-community/mathlib/pull/2781))
a really minor proof to show that a regular mono which is epi is an iso

### [2020-05-27 21:30:17](https://github.com/leanprover-community/mathlib/commit/efb4e95)
refactor(*iterate*): move to `function`; renamings ([#2832](https://github.com/leanprover-community/mathlib/pull/2832))
* move lemmas about `iterate` from `data.nat.basic` to `logic.function.iterate`;
* move lemmas like `nat.iterate_succ` to `function` namespace;
* rename some lemmas:
  - `iterate₀` to `iterate_fixed`,
  - `iterate₁` to `semiconj.iterate_right`, see also `commute.iterate_left` and `commute.iterate_right`;
  - `iterate₂` to `semiconj₂.iterate`;
  - `iterate_cancel` to `left_inverse.iterate` and `right_inverse.iterate`;
* move lemmas `*_hom.iterate_map_*` to `algebra/iterate_hom`.

### [2020-05-27 18:57:00](https://github.com/leanprover-community/mathlib/commit/1988364)
feat(src/ring_theory): in a PID, all fractional ideals are invertible ([#2826](https://github.com/leanprover-community/mathlib/pull/2826))
This would show that all PIDs are Dedekind domains, once we have a definition of Dedekind domain (we could define it right now, but it would depend on the choice of field of fractions).
In `localization.lean`, I added a few small lemmas on localizations (`localization.exists_integer_multiple` and `fraction_map.to_map_eq_zero_iff`). @101damnations, are these additions compatible with your branches? I'm happy to change them if not.

### [2020-05-27 13:41:59](https://github.com/leanprover-community/mathlib/commit/c812ebe)
feat(category_theory/abelian): abelian categories ([#2817](https://github.com/leanprover-community/mathlib/pull/2817))
~~Depends on [#2779](https://github.com/leanprover-community/mathlib/pull/2779).~~ Closes [#2178](https://github.com/leanprover-community/mathlib/pull/2178). I will give instances for `AddCommGroup` and `Module`, but since this PR is large already, I'll wait until the next PR with that.

### [2020-05-27 12:11:16](https://github.com/leanprover-community/mathlib/commit/2deb6b4)
feat(algebra/continued_fractions): add computation definitions and basic translation lemmas ([#2797](https://github.com/leanprover-community/mathlib/pull/2797))
### What
- add definitions of the computation of a continued fraction for a given value (in a given floor field)
- add very basic, mostly technical lemmas to convert between the different structures used by the computation
### Why
- I want to be able to compute the continued fraction of a value. I next will add termination, approximation, and correctness lemmas for the definitions in this commit (I already have them lying around on my PC for ages :cold_sweat: )
- The technical lemmas are needed for the next bunch of commits.
### How
- Follow the straightforward approach as described, for example, on [Wikipedia](https://en.wikipedia.org/wiki/Continued_fraction#Calculating_continued_fraction_representations)

### [2020-05-27 12:11:14](https://github.com/leanprover-community/mathlib/commit/798c61b)
feat(data/nat/prime): eq_prime_pow_of_dvd_least_prime_pow ([#2791](https://github.com/leanprover-community/mathlib/pull/2791))
Proves
```lean
lemma eq_prime_pow_of_dvd_least_prime_pow
  (a p k : ℕ) (pp : prime p) (h₁ : ¬(a ∣ p^k)) (h₂ : a ∣ p^(k+1)) :
  a = p^(k+1)
```

### [2020-05-27 12:11:12](https://github.com/leanprover-community/mathlib/commit/85f08ec)
feat(CI): add -T100000 to the build step in CI ([#2276](https://github.com/leanprover-community/mathlib/pull/2276))
This PR adds `-T100000` to CI. This is the default timeout setting in the VS Code extension and emacs.
With some exceptions, noted with `FIXME` comments mentioning `-T50000`, the library now compiles with `-T50000`:
- [ ] `has_sum.has_sum_ne_zero` in `src/topology/algebra/infinite_sum.lean`, where I don't really understand why it is slow.
- [ ] `exists_norm_eq_infi_of_complete_convex` in `src/analysis/normed_space/real_inner_product.lean`, which has a giant proof which should be rewritten in several steps.
- [ ] `tangent_bundle_core.coord_change_comp` in `src/geometry/manifold/basic_smooth_bundle.lean`.
- [ ] `change_origin_radius` in `src/analysis/analytic/basic.lean`
There are 3 `def`s related to category theory which also don't compile:
- [ ] `adj₁` in `src/topology/category/Top/adjunctions.lean`
- [x] `cones_equiv_inverse` in `src/category_theory/limits/over.lean` (addressed in [#2840](https://github.com/leanprover-community/mathlib/pull/2840))
- [ ] `prod_functor` in `src/category_theory/limits/shapes/binary_products.lean`
This proof no longer causes problems with `-T50000`, but it should still be broken up at some point.
- [ ] `simple_func_sequence_tendsto` in `src/measure_theory/simple_func_dense.lean`, which has a giant proof which should be rewritten in several steps. ~~This one is really bad, and doesn't even compile with `-T100000`.~~ 
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/-T50000.20challenge).

### [2020-05-27 11:24:35](https://github.com/leanprover-community/mathlib/commit/7c5eab3)
chore(scripts): update nolints.txt ([#2841](https://github.com/leanprover-community/mathlib/pull/2841))
I am happy to remove some nolints for you!

### [2020-05-27 08:57:27](https://github.com/leanprover-community/mathlib/commit/a7063ec)
feat(ring_theory/prod): ring homs to/from `R × S` ([#2836](https://github.com/leanprover-community/mathlib/pull/2836))
* move some instances from `algebra/pi_instances`;
* add `prod.comm_semiring`;
* define `ring_hom.fst`, `ring_hom.snd`, `ring_hom.prod`, and
  `ring_hom.prod_map`.

### [2020-05-27 08:57:25](https://github.com/leanprover-community/mathlib/commit/6ee3a47)
chore(data/equiv/basic): simplify some defs, add `coe` lemmas ([#2835](https://github.com/leanprover-community/mathlib/pull/2835))
Use functions like `prod.map`, `curry`, `uncurry`, `sum.elim`, `sum.map` to define equivalences.

### [2020-05-27 08:57:23](https://github.com/leanprover-community/mathlib/commit/2a48225)
feat(computability/tm_to_partrec): partrec functions are TM-computable ([#2792](https://github.com/leanprover-community/mathlib/pull/2792))
A construction of a Turing machine that can evaluate any partial recursive function. This PR contains the bulk of the work but the end to end theorem (which asserts that any `computable` function can be evaluated by a Turing machine) has not yet been stated.

### [2020-05-27 07:09:31](https://github.com/leanprover-community/mathlib/commit/0d6d0b0)
chore(*): split long lines, unindent in namespaces ([#2834](https://github.com/leanprover-community/mathlib/pull/2834))
The diff is large but here is the word diff (search for `[-` or `[+`):
``` shellsession
$ git diff --word-diff=plain --ignore-all-space master | grep '(^---|\[-|\[\+)'
--- a/src/algebra/big_operators.lean
[-λ l, @is_group_anti_hom.map_prod _ _ _ _ _ inv_is_group_anti_hom l-]-- TODO there is probably a cleaner proof of this
        { have : [-(to_finset s).sum (λx,-]{+∑ x in s.to_finset,+} ite (x = a) 1 [-0)-]{+0+} = [-({a} : finset α).sum (λx,-]{+∑ x in {a},+} ite (x = a) 1 [-0),-]
[-          { apply (finset.sum_subset _ _).symm,-]{+0,+}
          { [-intros _ H, rwa mem_singleton.1 H },-]
[-            { exact λ _ _ H, if_neg (mt finset.mem_singleton.2 H) }-]{+rw [finset.sum_ite_eq', if_pos h, finset.sum_singleton, if_pos rfl],+} },
--- a/src/algebra/category/Group/basic.lean
[-a-]{+an+} `add_equiv` between `add_group`s."]
--- a/src/algebra/category/Group/colimits.lean
--- a/src/algebra/category/Mon/basic.lean
[-a-]{+an+} `add_equiv` between `add_monoid`s."]
[-a-]{+an+} `add_equiv` between `add_comm_monoid`s."]
--- a/src/algebra/free.lean
--- a/src/algebra/group/units.lean
--- a/src/algebra/group/units_hom.lean
--- a/src/category_theory/category/default.lean
[-universes v u-]-- The order in this declaration matters: v often needs to be explicitly specified while u often
--- a/src/control/monad/cont.lean
    simp [-[call_cc,except_t.call_cc,call_cc_bind_right,except_t.goto_mk_label,map_eq_bind_pure_comp,bind_assoc,@call_cc_bind_left-]{+[call_cc,except_t.call_cc,call_cc_bind_right,except_t.goto_mk_label,map_eq_bind_pure_comp,+}
  call_cc_bind_left  := by { intros, simp [-[call_cc,option_t.call_cc,call_cc_bind_right,option_t.goto_mk_label,map_eq_bind_pure_comp,bind_assoc,@call_cc_bind_left-]{+[call_cc,option_t.call_cc,call_cc_bind_right,+}
  call_cc_bind_left  := by { intros, simp [-[call_cc,state_t.call_cc,call_cc_bind_left,(>>=),state_t.bind,state_t.goto_mk_label],-]{+[call_cc,state_t.call_cc,call_cc_bind_left,(>>=),+}
  call_cc_dummy := by { intros, simp [-[call_cc,state_t.call_cc,call_cc_bind_right,(>>=),state_t.bind,@call_cc_dummy-]{+[call_cc,state_t.call_cc,call_cc_bind_right,(>>=),+}
  call_cc_bind_left  := by { intros, simp [-[call_cc,reader_t.call_cc,call_cc_bind_left,reader_t.goto_mk_label],-]{+[call_cc,reader_t.call_cc,call_cc_bind_left,+}
--- a/src/control/monad/writer.lean
--- a/src/control/traversable/basic.lean
   online at <http://arxiv.org/pdf/1202.2919>[-Synopsis-]
--- a/src/data/analysis/filter.lean
--- a/src/data/equiv/basic.lean
--- a/src/data/fin.lean
--- a/src/data/finset.lean
  [-by-]{+{+} rw [-[eq],-]{+[eq] },+}
--- a/src/data/hash_map.lean
--- a/src/data/int/basic.lean
--- a/src/data/list/basic.lean
--- a/src/data/list/tfae.lean
--- a/src/data/num/lemmas.lean
[-Properties of the binary representation of integers.-]
--- a/src/data/zsqrtd/basic.lean
--- a/src/group_theory/congruence.lean
with [-a-]{+an+} addition."]
@[to_additive Sup_eq_add_con_gen "The supremum of a set of additive congruence relations [-S-]{+`S`+} equals
--- a/src/group_theory/monoid_localization.lean
--- a/src/group_theory/submonoid.lean
--- a/src/number_theory/dioph.lean
--- a/src/set_theory/ordinal.lean
--- a/src/tactic/apply.lean
--- a/src/tactic/lean_core_docs.lean
--- a/src/tactic/lint/type_classes.lean
--- a/src/tactic/omega/main.lean
--- a/test/coinductive.lean
--- a/test/localized/import3.lean
--- a/test/norm_num.lean
--- a/test/tidy.lean
--- a/test/where.lean
```
P.S.: I don't know how to make `git diff` hide all non-interesting chunks.

### [2020-05-27 01:18:54](https://github.com/leanprover-community/mathlib/commit/2792c93)
feat(ring_theory/fintype): in a finite nonzero_semiring, fintype.card (units R) < fintype.card R ([#2793](https://github.com/leanprover-community/mathlib/pull/2793))

### [2020-05-26 17:35:27](https://github.com/leanprover-community/mathlib/commit/63b8c52)
chore(scripts): update nolints.txt ([#2833](https://github.com/leanprover-community/mathlib/pull/2833))
I am happy to remove some nolints for you!

### [2020-05-26 16:47:21](https://github.com/leanprover-community/mathlib/commit/4dfd706)
chore(scripts): update nolints.txt ([#2831](https://github.com/leanprover-community/mathlib/pull/2831))
I am happy to remove some nolints for you!

### [2020-05-26 16:47:19](https://github.com/leanprover-community/mathlib/commit/4ca776e)
feat(linear_algebra/quadratic_form): equivalence of quadratic forms ([#2769](https://github.com/leanprover-community/mathlib/pull/2769))

### [2020-05-26 15:15:29](https://github.com/leanprover-community/mathlib/commit/9630eca)
feat(data/nat/primes): lemmas about min_fac ([#2790](https://github.com/leanprover-community/mathlib/pull/2790))

### [2020-05-26 13:30:46](https://github.com/leanprover-community/mathlib/commit/895f568)
perf(tactic/lint): speed up nolint attribute ([#2828](https://github.com/leanprover-community/mathlib/pull/2828))
Looking up the nolint attribute only takes 15 seconds out of the 45 minutes, so speeding up this part has little effect.  More importantly, this PR removes one branch from the mathlib repository.

### [2020-05-26 13:30:44](https://github.com/leanprover-community/mathlib/commit/1cf59fc)
chore(src/algebra/ordered_ring.lean): fix linting errors ([#2827](https://github.com/leanprover-community/mathlib/pull/2827))
[Mentioned, but not really discussed, in this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/How.20to.20get.20familiar.20enough.20with.20Mathlib.20to.20use.20it/near/198747067).
This PR also removes `mul_pos'` and `mul_nonneg'` lemmas because they are now identical to the improved `mul_pos` and `mul_nonneg`.

### [2020-05-26 13:30:42](https://github.com/leanprover-community/mathlib/commit/7d86475)
feat(data/polynomial): eq_one_of_is_unit_of_monic ([#2823](https://github.com/leanprover-community/mathlib/pull/2823))
~~Depends on [#2822](https://github.com/leanprover-community/mathlib/pull/2822) ~~

### [2020-05-26 13:30:40](https://github.com/leanprover-community/mathlib/commit/099ffd3)
chore(algebra/free_monoid): use implicit args in `lift` ([#2821](https://github.com/leanprover-community/mathlib/pull/2821))

### [2020-05-26 13:30:38](https://github.com/leanprover-community/mathlib/commit/fc79089)
feat(number_theory/primorial): Bound on the primorial function ([#2701](https://github.com/leanprover-community/mathlib/pull/2701))
This lemma is needed for Erdös's proof of Bertrand's postulate, but it may be of independent interest.

### [2020-05-26 11:43:31](https://github.com/leanprover-community/mathlib/commit/2c40bd3)
feat(tactic/push_cast): take list of extra simp lemmas ([#2825](https://github.com/leanprover-community/mathlib/pull/2825))
closes [#2783](https://github.com/leanprover-community/mathlib/pull/2783)

### [2020-05-26 10:40:07](https://github.com/leanprover-community/mathlib/commit/ab2e52e)
feat(order/filter/basic): a local left inverse locally equals a local right inverse ([#2808](https://github.com/leanprover-community/mathlib/pull/2808))

### [2020-05-26 10:40:05](https://github.com/leanprover-community/mathlib/commit/8c36b32)
feat(order/filter/basic): add `eventually.curry` ([#2807](https://github.com/leanprover-community/mathlib/pull/2807))
I'm not sure that this is a good name. Suggestions of better names are welcome.

### [2020-05-26 10:40:03](https://github.com/leanprover-community/mathlib/commit/597946d)
feat(analysis/calculus/implicit): Implicit function theorem ([#2749](https://github.com/leanprover-community/mathlib/pull/2749))
Fixes [#1849](https://github.com/leanprover-community/mathlib/pull/1849)
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/2749.20Implicit.20function.20theorem).

### [2020-05-26 09:33:44](https://github.com/leanprover-community/mathlib/commit/b4d4d9a)
feat(ring_theory/algebra): more on restrict_scalars ([#2445](https://github.com/leanprover-community/mathlib/pull/2445))

### [2020-05-26 08:11:51](https://github.com/leanprover-community/mathlib/commit/ea403b3)
feat(algebra/group_with_zero): mul_self_mul_inv ([#2795](https://github.com/leanprover-community/mathlib/pull/2795))
I found this lemma was useful for simplifying some expressions without
needing to split into cases or provide a proof that the denominator is
nonzero, and it doesn't show up with library_search.

### [2020-05-26 06:41:18](https://github.com/leanprover-community/mathlib/commit/1c265e2)
feat(data/nat/basic): with_bot lemmas ([#2822](https://github.com/leanprover-community/mathlib/pull/2822))

### [2020-05-26 05:06:40](https://github.com/leanprover-community/mathlib/commit/9bb9956)
feat(data/nat/basic): inequalities ([#2801](https://github.com/leanprover-community/mathlib/pull/2801))
Adds some simple inequalities about `nat.pow`.

### [2020-05-26 00:59:03](https://github.com/leanprover-community/mathlib/commit/4b616e6)
feat(category_theory/limits): transport lemmas for kernels ([#2779](https://github.com/leanprover-community/mathlib/pull/2779))

### [2020-05-25 20:20:32](https://github.com/leanprover-community/mathlib/commit/aad2dfc)
fix(group_with_zero): fix definition of comm_monoid_with_zero ([#2818](https://github.com/leanprover-community/mathlib/pull/2818))
Also generate instance comm_group_with_zero -> comm_monoid_with_zero.

### [2020-05-25 15:03:03](https://github.com/leanprover-community/mathlib/commit/ae5b55b)
feat(algebra/ring): ring_hom.map_dvd ([#2813](https://github.com/leanprover-community/mathlib/pull/2813))

### [2020-05-25 12:50:28](https://github.com/leanprover-community/mathlib/commit/52b839f)
feat(data/polynomial): is_unit_C ([#2812](https://github.com/leanprover-community/mathlib/pull/2812))

### [2020-05-25 12:50:26](https://github.com/leanprover-community/mathlib/commit/3e0668e)
feat(linear_algebra/projection): add `equiv_prod_of_surjective_of_is_compl` ([#2787](https://github.com/leanprover-community/mathlib/pull/2787))
If kernels of two surjective linear maps `f`, `g` are complement subspaces,
then `x ↦ (f x, g x)` defines a  linear equivalence.
I also add a version of this equivalence for continuous maps.
Depends on [#2785](https://github.com/leanprover-community/mathlib/pull/2785)

### [2020-05-25 12:07:49](https://github.com/leanprover-community/mathlib/commit/60f0b01)
feat(logic/function): define `semiconj` and `commute` ([#2788](https://github.com/leanprover-community/mathlib/pull/2788))

### [2020-05-25 10:18:13](https://github.com/leanprover-community/mathlib/commit/96f318c)
feat(algebra/group_power): int.nat_abs_pow_two ([#2811](https://github.com/leanprover-community/mathlib/pull/2811))

### [2020-05-25 10:18:11](https://github.com/leanprover-community/mathlib/commit/9da47ad)
feat(data/zmod): lemmas about coercions to zmod ([#2802](https://github.com/leanprover-community/mathlib/pull/2802))
I'm not particularly happy with the location of these new lemmas within the file `data.zmod`. If anyone has a suggestion that they should be some particular place higher or lower in the file, that would be welcome.

### [2020-05-25 08:49:00](https://github.com/leanprover-community/mathlib/commit/dd062f0)
feat(data/nat/prime): pow_not_prime ([#2810](https://github.com/leanprover-community/mathlib/pull/2810))

### [2020-05-25 07:24:08](https://github.com/leanprover-community/mathlib/commit/a2d5007)
chore(topology/algebra/module): prove `fst.prod snd = id` ([#2806](https://github.com/leanprover-community/mathlib/pull/2806))

### [2020-05-25 07:24:07](https://github.com/leanprover-community/mathlib/commit/ccf646d)
chore(set_theory/ordinal): use a `protected lemma` to drop a `nolint` ([#2805](https://github.com/leanprover-community/mathlib/pull/2805))

### [2020-05-25 07:24:05](https://github.com/leanprover-community/mathlib/commit/a3b3aa6)
fix(tactic/norm_num): workaround int.sub unfolding bug ([#2804](https://github.com/leanprover-community/mathlib/pull/2804))
Fixes https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/certificates.20for.20calculations/near/198631936 . Or rather, it works around an issue in how the kernel unfolds applications. The real fix is probably to adjust the definitional height or other heuristics around `add_group_has_sub` and `int.sub` so that tries to prove that they are defeq that way rather than unfolding `bit0` and `bit1`. Here is a MWE for the issue:
```lean
example : int.has_sub = add_group_has_sub := rfl
example :
  (@has_sub.sub ℤ int.has_sub 5000 2 : ℤ) =
  (@has_sub.sub ℤ add_group_has_sub 5000 2) := rfl -- deep recursion
```

### [2020-05-25 06:35:44](https://github.com/leanprover-community/mathlib/commit/6552f21)
feat(algebra/add_torsor): torsors of additive group actions ([#2720](https://github.com/leanprover-community/mathlib/pull/2720))
Define torsors of additive group actions, to the extent needed for
(and with notation motivated by) affine spaces, to the extent needed
for Euclidean spaces.  See
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Some.20olympiad.20formalisations
for the discussion leading to this particular structure.

### [2020-05-25 05:05:19](https://github.com/leanprover-community/mathlib/commit/518d0fd)
feat(data/int/basic): eq_zero_of_dvd_of_nonneg_of_lt ([#2803](https://github.com/leanprover-community/mathlib/pull/2803))

### [2020-05-24 19:02:14](https://github.com/leanprover-community/mathlib/commit/8d352b2)
feat(char_p): generalize zmod.neg_one_ne_one ([#2796](https://github.com/leanprover-community/mathlib/pull/2796))

### [2020-05-24 17:52:18](https://github.com/leanprover-community/mathlib/commit/61b57cd)
chore(scripts): update nolints.txt ([#2799](https://github.com/leanprover-community/mathlib/pull/2799))
I am happy to remove some nolints for you!

### [2020-05-24 17:03:59](https://github.com/leanprover-community/mathlib/commit/1445e08)
chore(scripts): update nolints.txt ([#2798](https://github.com/leanprover-community/mathlib/pull/2798))
I am happy to remove some nolints for you!

### [2020-05-24 16:14:04](https://github.com/leanprover-community/mathlib/commit/8590081)
feat(category_theory): Product comparison ([#2753](https://github.com/leanprover-community/mathlib/pull/2753))
Construct the product comparison morphism, and show it's an iso iff F preserves binary products.

### [2020-05-24 15:07:07](https://github.com/leanprover-community/mathlib/commit/292fc04)
feat(category_theory): adjunction convenience defs ([#2754](https://github.com/leanprover-community/mathlib/pull/2754))
Transport adjunctions along natural isomorphisms, and `is_left_adjoint` or `is_right_adjoint` versions of existing adjunction properties.

### [2020-05-24 09:09:11](https://github.com/leanprover-community/mathlib/commit/2ef444a)
feat(linear_algebra/basic): range of `linear_map.prod` ([#2785](https://github.com/leanprover-community/mathlib/pull/2785))
Also make `ker_prod` a `simp` lemma.

### [2020-05-24 07:37:41](https://github.com/leanprover-community/mathlib/commit/5449203)
chore(order/basic): change "minimum" in descriptions to "minimal" ([#2789](https://github.com/leanprover-community/mathlib/pull/2789))

### [2020-05-23 13:13:15](https://github.com/leanprover-community/mathlib/commit/79e296b)
doc(archive/100-theorems-list): Update README.md ([#2750](https://github.com/leanprover-community/mathlib/pull/2750))
Making the 100.yaml file more discoverable.

### [2020-05-23 12:26:58](https://github.com/leanprover-community/mathlib/commit/2a3f59a)
chore(scripts): update nolints.txt ([#2782](https://github.com/leanprover-community/mathlib/pull/2782))
I am happy to remove some nolints for you!

### [2020-05-23 11:01:14](https://github.com/leanprover-community/mathlib/commit/2b79f1d)
feat(ring_theory/ideal_operations): lemmas about ideals and galois connections ([#2767](https://github.com/leanprover-community/mathlib/pull/2767))
depends on [#2766](https://github.com/leanprover-community/mathlib/pull/2766)

### [2020-05-23 09:33:06](https://github.com/leanprover-community/mathlib/commit/ceb13ba)
chore(order/basic): add `monotone.order_dual`, `strict_mono.order_dual` ([#2778](https://github.com/leanprover-community/mathlib/pull/2778))
Also split long lines and lint.

### [2020-05-23 09:33:05](https://github.com/leanprover-community/mathlib/commit/90abd3b)
feat(data/fintype): finset.univ_map_embedding ([#2765](https://github.com/leanprover-community/mathlib/pull/2765))
Adds the lemma
```
lemma finset.univ_map_embedding {α : Type*} [fintype α] (e : α ↪ α) :
  (finset.univ).map e = finset.univ :=
```

### [2020-05-23 09:33:02](https://github.com/leanprover-community/mathlib/commit/6948505)
feat(data/polynomial): prime_of_degree_eq_one_of_monic ([#2745](https://github.com/leanprover-community/mathlib/pull/2745))

### [2020-05-23 07:44:20](https://github.com/leanprover-community/mathlib/commit/8c1793f)
chore(data/equiv): make `equiv.ext` args use { } ([#2776](https://github.com/leanprover-community/mathlib/pull/2776))
Other changes:
* rename lemmas `eq_of_to_fun_eq` to `coe_fn_injective`;
* add `left_inverse.eq_right_inverse` and use it to prove `equiv.ext`.

### [2020-05-22 09:41:03](https://github.com/leanprover-community/mathlib/commit/f66caaa)
chore(scripts): update nolints.txt ([#2777](https://github.com/leanprover-community/mathlib/pull/2777))
I am happy to remove some nolints for you!

### [2020-05-22 08:09:58](https://github.com/leanprover-community/mathlib/commit/c6aab26)
feat(algebra/invertible): invertible_of_ring_char_not_dvd ([#2775](https://github.com/leanprover-community/mathlib/pull/2775))
```
def invertible_of_ring_char_not_dvd {R : Type*} [field R] {t : ℕ} (not_dvd : ¬(ring_char R ∣ t)) :
  invertible (t : R)
```

### [2020-05-22 08:09:56](https://github.com/leanprover-community/mathlib/commit/58789f7)
feat(analysis/normed_space/banach): add `continuous_linear_equiv.of_bijective` ([#2774](https://github.com/leanprover-community/mathlib/pull/2774))

### [2020-05-22 07:28:22](https://github.com/leanprover-community/mathlib/commit/80ad9ed)
refactor(ring_theory/localization): characterise ring localizations up to isomorphism ([#2714](https://github.com/leanprover-community/mathlib/pull/2714))
Beginnings of ```ring_theory/localization``` refactor from [#2675](https://github.com/leanprover-community/mathlib/pull/2675).
It's a bit sad that using the characteristic predicate means Lean can't infer the R-algebra structure of the localization. I've tried to get round this, but I'm not using •, and I've duplicated some fairly random lemmas about modules & algebras to take ```f``` as an explicit argument - mostly just what I needed to make ```fractional_ideal``` work. Should I duplicate more?
My comments in the ```fractional_ideal``` docs about 'preserving definitional equalities' wrt getting an R-module structure from an R-algebra structure: do they make sense? I had some errors about definitional equality of instances which I *think* I fixed after making sure the R-module structure always came from the R-algebra structure, as well as doing a few other things. I never chased up exactly what the errors were or how they went away, so I'm just guessing at my explanation.
Things I've got left to PR to ```ring_theory/localization``` after this: 
- ```away``` (localization at submonoid generated by one element)
- localization as a quotient type & proof it satisfies the char pred
- localization at the complement of a prime ideal and the fact this is a local ring
- more lemmas about fields of fractions
- the order embedding for ideals of the localization vs. ideals of the original ring

### [2020-05-22 06:26:36](https://github.com/leanprover-community/mathlib/commit/a012d76)
chore(linear_algebra/projection): use implicit args in lemmas ([#2773](https://github.com/leanprover-community/mathlib/pull/2773))

### [2020-05-22 06:26:34](https://github.com/leanprover-community/mathlib/commit/749e39f)
feat(category_theory): preadditive binary biproducts ([#2747](https://github.com/leanprover-community/mathlib/pull/2747))
This PR introduces "preadditive binary biproducts", which correspond to the second definition of biproducts given in [#2177](https://github.com/leanprover-community/mathlib/pull/2177).
* Preadditive binary biproducts are binary biproducts.
* In a preadditive category, a binary product is a preadditive binary biproduct.
* This directly implies that `AddCommGroup` has preadditive binary biproducts. The existence of binary coproducts in `AddCommGroup` is then a consequence of abstract nonsense.

### [2020-05-22 05:08:46](https://github.com/leanprover-community/mathlib/commit/5585e3c)
chore(linear_algebra/basic): redefine le on submodule ([#2766](https://github.com/leanprover-community/mathlib/pull/2766))
Previously, to prove an `S \le T`, there would be a coercion in the statement after `intro x`. This fixes that.

### [2020-05-21 22:53:42](https://github.com/leanprover-community/mathlib/commit/a9960ce)
chore(scripts): update nolints.txt ([#2771](https://github.com/leanprover-community/mathlib/pull/2771))
I am happy to remove some nolints for you!

### [2020-05-21 20:35:43](https://github.com/leanprover-community/mathlib/commit/6c71874)
feat(analysis/normed_space): complemented subspaces ([#2738](https://github.com/leanprover-community/mathlib/pull/2738))
Define complemented subspaces and prove some basic facts.

### [2020-05-21 20:35:41](https://github.com/leanprover-community/mathlib/commit/fd45e28)
fix(*): do not nolint simp_nf ([#2734](https://github.com/leanprover-community/mathlib/pull/2734))
The `nolint simp_nf` for `subgroup.coe_coe` was hiding an actual nontermination issue.  Please just ping me if you're unsure about the `simp_nf` linter.

### [2020-05-21 18:58:04](https://github.com/leanprover-community/mathlib/commit/ec01a0d)
perf(tactic/lint/simp): speed up `simp_comm` linter ([#2760](https://github.com/leanprover-community/mathlib/pull/2760))
This is a fairly unimportant linter, but takes 35% of the linting runtime in my unscientific small-case profiling run.

### [2020-05-21 15:42:46](https://github.com/leanprover-community/mathlib/commit/d532eb6)
feat(order/lattice): sup_left_idem and similar ([#2768](https://github.com/leanprover-community/mathlib/pull/2768))

### [2020-05-21 07:51:07](https://github.com/leanprover-community/mathlib/commit/951b967)
refactor(data/nat/basic): use function equality for `iterate` lemmas ([#2748](https://github.com/leanprover-community/mathlib/pull/2748))

### [2020-05-20 19:37:56](https://github.com/leanprover-community/mathlib/commit/a540d79)
chore(archive/sensitivity): Clean up function coercion in sensitivity proof (depends on [#2756](https://github.com/leanprover-community/mathlib/pull/2756)) ([#2758](https://github.com/leanprover-community/mathlib/pull/2758))
This formalizes the proof of an old conjecture: `is_awesome Gabriel`. I also took the opportunity to remove type class struggling, which I think is related to the proof of `is_awesome Floris`.
I think @jcommelin should also update this sensitivity file to use his sum notations if applicable.

### [2020-05-20 18:10:11](https://github.com/leanprover-community/mathlib/commit/3c9bf6b)
chore(scripts): update nolints.txt ([#2763](https://github.com/leanprover-community/mathlib/pull/2763))
I am happy to remove some nolints for you!

### [2020-05-20 15:35:04](https://github.com/leanprover-community/mathlib/commit/d6420bd)
feat(ring_theory/principal_ideal_domain): definition of principal submodule ([#2761](https://github.com/leanprover-community/mathlib/pull/2761))
This PR generalizes the definition of principal ideals to principal submodules. It turns out that it's essentially enough to replace `ideal R` with `submodule R M` in the relevant places. With this change, it's possible to talk about principal fractional ideals (although that development will have to wait [#2714](https://github.com/leanprover-community/mathlib/pull/2714) gets merged).
Since the PR already changes the variables used in this file, I took the opportunity to rename them so `[ring α]` becomes `[ring R]`.

### [2020-05-20 15:35:02](https://github.com/leanprover-community/mathlib/commit/4c3e1a9)
feat(algebra): the R-module structure on S-linear maps, for S an R-algebra ([#2759](https://github.com/leanprover-community/mathlib/pull/2759))
I couldn't find this already in mathlib, but perhaps I've missed it.

### [2020-05-20 15:34:59](https://github.com/leanprover-community/mathlib/commit/6df77a6)
chore(*): update to Lean 3.14.0 ([#2756](https://github.com/leanprover-community/mathlib/pull/2756))
This is an optimistic PR, betting *nothing* will break when moving to Lean 3.14.0.

### [2020-05-20 15:34:58](https://github.com/leanprover-community/mathlib/commit/164c2e3)
chore(category_theory): attributes and a transport proof ([#2751](https://github.com/leanprover-community/mathlib/pull/2751))
A couple of cleanups, modified a proof or two so that `@[simps]` can be used, which let me clean up some other proofs. Also a proof that we can transfer that `F` preserves the limit `K` along an isomorphism in `K`.
(Preparation for some PRs from my topos project)

### [2020-05-20 12:01:53](https://github.com/leanprover-community/mathlib/commit/ab5d0f1)
feat(category_theory/binary_products): some product lemmas and their dual ([#2752](https://github.com/leanprover-community/mathlib/pull/2752))
A bunch of lemmas about binary products.

### [2020-05-20 11:03:44](https://github.com/leanprover-community/mathlib/commit/1f00282)
docs(linear_algebra/sesquilinear_form): correct module docs ([#2757](https://github.com/leanprover-community/mathlib/pull/2757))
@PatrickMassot mentioned that the docs for `sesquilinear_form` mention bilinear forms instead in a few places. This PR corrects them to use "sesquilinear form" everywhere.

### [2020-05-20 06:18:22](https://github.com/leanprover-community/mathlib/commit/cbe80ed)
feat(linear_algebra/projection): projection to a subspace ([#2739](https://github.com/leanprover-community/mathlib/pull/2739))
Define equivalence between complement subspaces and projections.

### [2020-05-19 22:34:25](https://github.com/leanprover-community/mathlib/commit/3c1f9f9)
feat(data/nat/choose): sum_range_choose_halfway ([#2688](https://github.com/leanprover-community/mathlib/pull/2688))
This is a lemma on the way to proving that the product of primes less than `n` is less than `4 ^ n`, which is itself a lemma in Bertrand's postulate.
The lemma itself is of dubious significance, but it will eventually be necessary for Bertrand, and I want to commit early and often. Brief discussion of this decision at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Candidate.20for.20inclusion.20in.20mathlib/near/197619722 .
This is my second PR to mathlib; the code is definitely verbose and poorly structured, but I don't know how to fix it. I'm expecting almost no lines of the original to remain by the end of this!

### [2020-05-19 18:38:27](https://github.com/leanprover-community/mathlib/commit/e3aca90)
feat(logic/basic): spaces with a zero or a one are nonempty ([#2743](https://github.com/leanprover-community/mathlib/pull/2743))
Register instances that a space with a zero or a one is not empty, with low priority as we don't want to embark on a search for a zero or a one if this is not necessary.
Discussion on Zulip at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/inhabited.20and.20nonempty.20instances/near/198030072

### [2020-05-19 17:00:43](https://github.com/leanprover-community/mathlib/commit/607767e)
feat(algebra/big_operators): reversing an interval doesn't change the product ([#2740](https://github.com/leanprover-community/mathlib/pull/2740))
Also use Gauss summation in the Gauss summation formula.
Inspired by [#2688](https://github.com/leanprover-community/mathlib/pull/2688)

### [2020-05-19 15:54:58](https://github.com/leanprover-community/mathlib/commit/62c22da)
fix(ci): replace 2 old secret names ([#2744](https://github.com/leanprover-community/mathlib/pull/2744))
[`lean-3.13.2`](https://github.com/leanprover-community/mathlib/tree/lean-3.13.2) is out of date, since I missed two instances of `DEPLOY_NIGHTLY_GITHUB_TOKEN` in [#2737](https://github.com/leanprover-community/mathlib/pull/2737).

### [2020-05-19 11:50:10](https://github.com/leanprover-community/mathlib/commit/1e18512)
chore(*): remove non-canonical `option.decidable_eq_none` instance ([#2741](https://github.com/leanprover-community/mathlib/pull/2741))
I also removed the hack in `ulower.primcodable` where I had to use `none = o` instead of `o = none`.

### [2020-05-19 09:58:39](https://github.com/leanprover-community/mathlib/commit/93b41e5)
fix(*): put headings in multiline module docs on their own lines ([#2742](https://github.com/leanprover-community/mathlib/pull/2742))
found using regex: `/-! #([^-/])*$`.
These don't render correctly in the mathlib docs. Module doc strings that consist of a heading on its own line are OK so I haven't changed them.
I also moved some descriptive text from copyright headers to module docs, or removed such text if there was already a module doc string.

### [2020-05-19 09:58:37](https://github.com/leanprover-community/mathlib/commit/3d948bf)
feat(analysis/normed_space): interior of `closed_ball` etc ([#2723](https://github.com/leanprover-community/mathlib/pull/2723))
* define `sphere x r`
* prove formulas for `interior`, `closure`, and `frontier` of open and closed balls in real normed vector spaces.

### [2020-05-19 08:28:09](https://github.com/leanprover-community/mathlib/commit/f2cb546)
fix(ci): setup git before nolints, rename secret ([#2737](https://github.com/leanprover-community/mathlib/pull/2737))
Oops, I broke the update nolints step on master. This should fix it.

### [2020-05-19 08:28:08](https://github.com/leanprover-community/mathlib/commit/3968f7f)
feat(linear_algebra): equiv_of_is_basis' and module.fintype_of_fintype ([#2735](https://github.com/leanprover-community/mathlib/pull/2735))

### [2020-05-19 08:28:05](https://github.com/leanprover-community/mathlib/commit/80b7f97)
feat(tactic/localized): fail if unused locale is open ([#2718](https://github.com/leanprover-community/mathlib/pull/2718))
This is more in line with the behavior of `open`.
Closes [#2702](https://github.com/leanprover-community/mathlib/pull/2702)

### [2020-05-19 08:28:03](https://github.com/leanprover-community/mathlib/commit/3ba7d12)
feat(algebra): obtaining algebraic classes through in/surjective maps ([#2638](https://github.com/leanprover-community/mathlib/pull/2638))
This is needed for the definition of Witt vectors.

### [2020-05-19 07:10:15](https://github.com/leanprover-community/mathlib/commit/52aa128)
feat(data/equiv): add add_equiv.to_multiplicative ([#2732](https://github.com/leanprover-community/mathlib/pull/2732))
We already have `add_monoid_hom.to_multiplicative`. This adds `add_equiv.to_multiplicative`.
It is placed in `data/equiv/mul_add.lean` because `data/equiv/mul_add.lean` already imports `algebra/group/type_tags.lean`.

### [2020-05-19 06:13:04](https://github.com/leanprover-community/mathlib/commit/906220c)
feat(topology/bounded_continuous_function): Normed algebra of bounded continuous functions ([#2722](https://github.com/leanprover-community/mathlib/pull/2722))
The space `C(α, γ)` of bounded continuous functions into a normed algebra γ is a normed algebra.  The space of bounded continuous functions into a normed 𝕜-space is a `C(α, 𝕜)`-module.

### [2020-05-19 03:26:24](https://github.com/leanprover-community/mathlib/commit/01efaeb)
feat(ci): run lint and tests in parallel ([#2736](https://github.com/leanprover-community/mathlib/pull/2736))
Actions doesn't let us run *steps* in parallel, but we can run *jobs* in parallel. The lint and test jobs are part of the same *workflow*. Understanding Actions terminology is half the battle.

### [2020-05-18 18:12:30](https://github.com/leanprover-community/mathlib/commit/f01260a)
feat(algebra/char_p): eq_iff_modeq_int ([#2731](https://github.com/leanprover-community/mathlib/pull/2731))

### [2020-05-18 16:18:17](https://github.com/leanprover-community/mathlib/commit/9d762df)
chore(scripts): update nolints.txt ([#2733](https://github.com/leanprover-community/mathlib/pull/2733))
I am happy to remove some nolints for you!

### [2020-05-18 13:38:47](https://github.com/leanprover-community/mathlib/commit/ff3130d)
feat(topology/constructions): topology on ulift ([#2716](https://github.com/leanprover-community/mathlib/pull/2716))

### [2020-05-18 13:38:45](https://github.com/leanprover-community/mathlib/commit/4026bd8)
feat(category_theory/full_subcategory): induced category from a groupoid is a groupoid ([#2715](https://github.com/leanprover-community/mathlib/pull/2715))
Also some minor cleanup to the same file.

### [2020-05-18 13:38:43](https://github.com/leanprover-community/mathlib/commit/2fa1d7c)
Revert "fix(category_theory/eq_to_hom): remove bad simp lemmas ([#1346](https://github.com/leanprover-community/mathlib/pull/1346))" ([#2713](https://github.com/leanprover-community/mathlib/pull/2713))
These are good simp lemmas: they push things into a proof-irrelevant position.
This reverts commit 5a309a3aa30fcec122a26f379f05b466ee46fc7a.

### [2020-05-18 13:38:41](https://github.com/leanprover-community/mathlib/commit/8b42245)
refactor(algebra): merge init_.algebra into algebra ([#2707](https://github.com/leanprover-community/mathlib/pull/2707))
This is a big refactor PR. It depends on [#2697](https://github.com/leanprover-community/mathlib/pull/2697), which brings in the algebra hierarchy without any change to the file structure. This PR merges `init_.algebra.group` into `algebra.group` and so on for the rest of the algebraic hierarchy.

### [2020-05-18 13:38:39](https://github.com/leanprover-community/mathlib/commit/18217e9)
feat(nat/choose): Generalise nat.dvd_choose ([#2703](https://github.com/leanprover-community/mathlib/pull/2703))
Spin-off from [#2701](https://github.com/leanprover-community/mathlib/pull/2701).

### [2020-05-18 11:24:28](https://github.com/leanprover-community/mathlib/commit/434e6a6)
chore(*): update to lean 3.13.2 ([#2728](https://github.com/leanprover-community/mathlib/pull/2728))
This should fix the bug with the missing module doc strings in the documentation.

### [2020-05-17 23:39:12](https://github.com/leanprover-community/mathlib/commit/93119dd)
chore(scripts): update nolints.txt ([#2721](https://github.com/leanprover-community/mathlib/pull/2721))
I am happy to remove some nolints for you!

### [2020-05-17 22:37:56](https://github.com/leanprover-community/mathlib/commit/7325104)
feat(ci): store xz archives ([#2719](https://github.com/leanprover-community/mathlib/pull/2719))
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/olean.20cache

### [2020-05-17 20:01:37](https://github.com/leanprover-community/mathlib/commit/cdf97dc)
refactor(field_theory): preparations for Chevalley–Warning ([#2590](https://github.com/leanprover-community/mathlib/pull/2590))
This PR adds some preparations for the Chevalley–Warning theorem.
depends on: ~[#2606](https://github.com/leanprover-community/mathlib/pull/2606), [#2607](https://github.com/leanprover-community/mathlib/pull/2607), [#2623](https://github.com/leanprover-community/mathlib/pull/2623)~

### [2020-05-17 17:58:04](https://github.com/leanprover-community/mathlib/commit/f23c361)
chore(*): bump to lean-3.13.1 ([#2697](https://github.com/leanprover-community/mathlib/pull/2697))
## Move algebra to mathlib
The algebraic hierarchy has moved from the core library to `init_`. In later PRs this can be integrated into the existing directory structure of mathlib.

### [2020-05-17 15:08:29](https://github.com/leanprover-community/mathlib/commit/3449510)
feat(algebra/big_operators): Alternative phrasing of prod-bij ([#2709](https://github.com/leanprover-community/mathlib/pull/2709))
Requested by @ChrisHughes24 in https://github.com/leanprover-community/mathlib/pull/2688/files#r426184248
A repaired version of [#2708](https://github.com/leanprover-community/mathlib/pull/2708).

### [2020-05-17 12:00:04](https://github.com/leanprover-community/mathlib/commit/a206df1)
chore(scripts): update nolints.txt ([#2711](https://github.com/leanprover-community/mathlib/pull/2711))
I am happy to remove some nolints for you!

### [2020-05-17 07:42:04](https://github.com/leanprover-community/mathlib/commit/b530cdb)
refactor(normed_space): require `norm_smul_le` instead of `norm_smul` ([#2693](https://github.com/leanprover-community/mathlib/pull/2693))
While in many cases we can prove `norm_smul` directly, in some cases (e.g., for the operator norm) it's easier to prove `norm_smul_le`. Redefine `normed_space` to avoid repeating the same trick over and over.

### [2020-05-17 04:33:06](https://github.com/leanprover-community/mathlib/commit/39af0f6)
chore(algebra/ring): drop an unneeded instance ([#2705](https://github.com/leanprover-community/mathlib/pull/2705))
We're incompatible with Lean 3.4.2 for a long time.

### [2020-05-17 02:07:24](https://github.com/leanprover-community/mathlib/commit/1580cd8)
fix(algebra/big_operators): typo fix ([#2704](https://github.com/leanprover-community/mathlib/pull/2704))
Fix cut-and-paste typos in the doc string for `∑ x, f x`.

### [2020-05-17 02:07:22](https://github.com/leanprover-community/mathlib/commit/4f484a1)
feat(archive/100-theorems-list): Sum of the Reciprocals of the Triangular Numbers ([#2692](https://github.com/leanprover-community/mathlib/pull/2692))
Adds a folder `archive/100-theorems-list`, moves our proof of 82 into it, and provides a proof of 42. There's a readme, I haven't really thought about what should go in there.

### [2020-05-17 00:07:54](https://github.com/leanprover-community/mathlib/commit/21bdb78)
feat(ring_theory/ideal_operations): jacobson radical, is_local, and primary ideals ([#768](https://github.com/leanprover-community/mathlib/pull/768))

### [2020-05-16 21:18:08](https://github.com/leanprover-community/mathlib/commit/00024db)
refactor(group_theory/monoid_localization): use old_structure_cmd ([#2683](https://github.com/leanprover-community/mathlib/pull/2683))
Second bit of [#2675](https://github.com/leanprover-community/mathlib/pull/2675).
The change to ```old_structure_cmd``` is so ring localizations can use this file more easily.
I've not made sure the map ```f``` is implicit when it can be because ```f.foo``` notation means it doesn't make much difference, but I'll change this if needed.*
I have changed some of the bad names at the end; they are still not great.  Does anyone have any
alternative suggestions?
Things to come in future PRs: the group completion of a comm monoid and some examples, ```away``` (localization at a submonoid generated by one element), more stuff on the localization as a quotient type & the fact it satisfies the char pred.
I think I've learnt some stuff about the ```@[simp]``` linter today. Hopefully I'll be making fewer commits trying and failing to appease it.
*edit: I mean I haven't checked how many places I can make ```f``` implicit & remove the appropriate ```f.```'s.

### [2020-05-16 17:50:21](https://github.com/leanprover-community/mathlib/commit/a7b17cd)
feat(data/finset): remove uses of choice for infima ([#2699](https://github.com/leanprover-community/mathlib/pull/2699))
This PR removes the dependence of many lemmas about inf of finset sets on the axiom of choice. The motivation for this is to make `category_theory.limits.has_finite_limits_of_semilattice_inf_top` not depend on choice, which I would like so that I can prove independence results about topos models of set theory from the axiom of choice.
This does make the decidable_classical linter fail.

### [2020-05-16 14:49:11](https://github.com/leanprover-community/mathlib/commit/c81be77)
feat(data/finset) Another finset disjointness lemma ([#2698](https://github.com/leanprover-community/mathlib/pull/2698))
I couldn't find this anywhere, and I wanted it.
Naming question: this is "obviously" called `disjoint_filter`, except there's already a lemma with that name.
I know I've broken one of the rules of using `simp` here ("don't do it at the beginning"), but this proof is much longer than I'd have thought would be necessary so I'm rather expecting someone to hop in with a one-liner.

### [2020-05-16 07:36:54](https://github.com/leanprover-community/mathlib/commit/4b71428)
doc(tactic/solve_by_elim): improve docs ([#2696](https://github.com/leanprover-community/mathlib/pull/2696))

### [2020-05-16 02:47:42](https://github.com/leanprover-community/mathlib/commit/74286f5)
feat(category_theory/limits/shapes): avoid choice for binary products ([#2695](https://github.com/leanprover-community/mathlib/pull/2695))
A tiny change to liberate binary products from the axiom of choice

### [2020-05-15 21:05:48](https://github.com/leanprover-community/mathlib/commit/1b85e3c)
chore(*): bump to lean-3.12.0 ([#2681](https://github.com/leanprover-community/mathlib/pull/2681))
## Changes to bracket notation
* `{a}` now requires an instance `has_singleton`;
* `insert a ∅ = {a}` is called `insert_emptyc_eq`, provided by an `is_lawful_singleton` instance;
* `a ∈ ({b} : set α)` is now defeq `a = b`, not `a = b ∨ false`;
* `({a} : set α)` is no longer defeq `insert a ∅`;
* `({a} : finset α)` now means `⟨⟨[a]⟩, _⟩` (used to be called `finset.singleton a`), not `insert a ∅`;
* removed `finset.singleton`;
* `{a, b}` is now `insert a {b}`, not `insert b {a}`.
* `finset.univ : finset bool` is now `{tt, ff}`;
* `(({a} : finset α) : set α)` is no longer defeq `{a}`.
## Tactic `norm_num`
The interactive tactic `norm_num` was recently rewritten in Lean. The non-interactive `tactic.norm_num` has been removed in Lean 3.12 so that we can migrate the algebraic hierarchy to mathlib in 3.13.
## Tactic combinators
https://github.com/leanprover-community/lean/pull/212 renames a bunch of tactic combinators. We change to using the new names.
## Tactic `case`
https://github.com/leanprover-community/lean/pull/228 slightly changes the semantics of the `case` tactic. We fix the resulting breakage to be conform the new semantics.

### [2020-05-15 21:05:46](https://github.com/leanprover-community/mathlib/commit/f5f7a3c)
feat(analysis/special_functions/exp_log): power series for log around 1 ([#2646](https://github.com/leanprover-community/mathlib/pull/2646))
This PR adds the power series expansion for the real logarithm around `1`, in the form
```lean
has_sum (λ (n : ℕ), x ^ (n + 1) / (n + 1)) (-log (1 - x))
```

### [2020-05-15 18:16:25](https://github.com/leanprover-community/mathlib/commit/14a82b3)
fix(tactic/norm_num): div/mod with negative first arg ([#2689](https://github.com/leanprover-community/mathlib/pull/2689))
bugfix from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/norm_num.20doesn't.20prove/near/197674516

### [2020-05-15 16:34:16](https://github.com/leanprover-community/mathlib/commit/a4266a0)
chore(scripts): update nolints.txt ([#2690](https://github.com/leanprover-community/mathlib/pull/2690))
I am happy to remove some nolints for you!

### [2020-05-15 13:15:27](https://github.com/leanprover-community/mathlib/commit/471d29e)
perf(tactic/ring): use new norm_num, avoid mk_app ([#2685](https://github.com/leanprover-community/mathlib/pull/2685))
Remove `tactic.norm_num` from `ring`, and do some performance upgrades borrowed from the `norm_num` overhaul while I'm at it.

### [2020-05-15 07:57:55](https://github.com/leanprover-community/mathlib/commit/b44fa3c)
chore(data/int/basic): mark cast_sub with simp attribute ([#2687](https://github.com/leanprover-community/mathlib/pull/2687))
I think the reason this didn't have the `simp` attribute already was from the time when `sub_eq_add_neg` was a `simp` lemma, so it wasn't necessary. I'm adding the `simp` attribute back now that `sub_eq_add_neg` is not a `simp` lemma.

### [2020-05-15 04:51:31](https://github.com/leanprover-community/mathlib/commit/f07ac36)
feat(category_theory/limits/lattice): finite limits in a semilattice ([#2665](https://github.com/leanprover-community/mathlib/pull/2665))
Construct finite limits in a semilattice_inf_top category, and finite colimits in a semilattice_sup_bot category.

### [2020-05-15 03:11:30](https://github.com/leanprover-community/mathlib/commit/378aa0d)
feat(data/nat/choose): Sum a row of Pascal's triangle ([#2684](https://github.com/leanprover-community/mathlib/pull/2684))
Add the "sum of the nth row of Pascal's triangle" theorem.
Naming is hard, of course, and this is my first PR to mathlib, so naming suggestions are welcome.
Briefly discussed at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Candidate.20for.20inclusion.20in.20mathlib/near/197619403 .

### [2020-05-14 18:21:52](https://github.com/leanprover-community/mathlib/commit/be03a3d)
chore(scripts): update nolints.txt ([#2682](https://github.com/leanprover-community/mathlib/pull/2682))
I am happy to remove some nolints for you!

### [2020-05-14 18:21:50](https://github.com/leanprover-community/mathlib/commit/606be81)
perf(tactic/ext): NEVER USE `user_attribute.get_param` ([#2674](https://github.com/leanprover-community/mathlib/pull/2674))
Refactor the extensionality attribute a bit so that it avoids `get_param`, which is a performance nightmare because it uses `eval_expr`.
```lean
import all
set_option profiler true
example (f g : bool → bool → set bool) : f = g :=
by ext
-- before: tactic execution took 2.19s
-- after: tactic execution took 33ms
```

### [2020-05-14 18:21:48](https://github.com/leanprover-community/mathlib/commit/7427f8e)
feat(topology): a few properties of `tendsto _ _ (𝓤 α)` ([#2645](https://github.com/leanprover-community/mathlib/pull/2645))
- prove that `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is an equivalence realtion;
- in case of a metric space, restate this relation as `tendsto (λ x, dist (f x) (g x)) l (𝓝 0)`;
- prove that `tendsto f l (𝓝 a) ↔ tendsto g l (𝓝 b)` provided that
  `tendsto (λ x, (f x, g x)) l (𝓤 α)`.

### [2020-05-14 15:22:51](https://github.com/leanprover-community/mathlib/commit/d412cfd)
chore(algebra/ring): lemmas about units in a semiring ([#2680](https://github.com/leanprover-community/mathlib/pull/2680))
The lemmas in non-localization files from [#2675](https://github.com/leanprover-community/mathlib/pull/2675). (Apart from one, which wasn't relevant to [#2675](https://github.com/leanprover-community/mathlib/pull/2675)).
(Edit: I am bad at git. I was hoping there would only be 1 commit here. I hope whatever I'm doing wrong is inconsequential...)

### [2020-05-14 11:14:27](https://github.com/leanprover-community/mathlib/commit/03c272e)
chore(scripts): update nolints.txt ([#2679](https://github.com/leanprover-community/mathlib/pull/2679))
I am happy to remove some nolints for you!

### [2020-05-14 11:14:24](https://github.com/leanprover-community/mathlib/commit/2871bd1)
chore(logic/function): drop `function.uncurry'` ([#2678](https://github.com/leanprover-community/mathlib/pull/2678))
See [lean[#161](https://github.com/leanprover-community/mathlib/pull/161)](https://github.com/leanprover-community/lean/pull/161/files#diff-42c23da308a4d5900f9f3244953701daR132)
Also add `uniform_continuous.prod_map` and `uniform_continuous₂.bicompl`

### [2020-05-14 11:14:19](https://github.com/leanprover-community/mathlib/commit/3da777a)
chore(linear_algebra/basis): use dot notation, simplify some proofs ([#2671](https://github.com/leanprover-community/mathlib/pull/2671))

### [2020-05-14 07:53:24](https://github.com/leanprover-community/mathlib/commit/d0beb49)
doc(*): move most docs to website, update links ([#2676](https://github.com/leanprover-community/mathlib/pull/2676))
The relaunched https://leanprover-community.github.io now contains copies of most of the doc files. This PR replaces the corresponding markdown files on mathlib with pointers to their new locations so that they only need to be maintained in one place.
The two remaining markdown files are `docs/contribute/bors.md` and `docs/contribute/code-review.md`.
Fixes [#2168](https://github.com/leanprover-community/mathlib/pull/2168).

### [2020-05-14 04:40:05](https://github.com/leanprover-community/mathlib/commit/7077b58)
chore(logic/function): move to `logic/function/basic` ([#2677](https://github.com/leanprover-community/mathlib/pull/2677))
Also add some docstrings.
I'm going to add more `logic.function.*` files with theorems that can't go to `basic` because of imports.

### [2020-05-14 04:40:03](https://github.com/leanprover-community/mathlib/commit/6ffb613)
chore(algebra/free_monoid): add a custom `rec_on` ([#2670](https://github.com/leanprover-community/mathlib/pull/2670))

### [2020-05-14 00:19:02](https://github.com/leanprover-community/mathlib/commit/f7cb363)
refactor(order/lattice): adjust proofs to avoid choice ([#2666](https://github.com/leanprover-community/mathlib/pull/2666))
For foundational category theoretic reasons, I'd like these lattice properties to avoid choice.
In particular, I'd like the proof here: https://github.com/leanprover-community/mathlib/pull/2665 to be intuitionistic.
 For most of them it was very easy, eg changing `finish` to `simp`. For `sup_assoc` and `inf_assoc` it's a bit more complex though - for `inf_assoc` I wrote out a term mode proof, and for `sup_assoc` I used `ifinish`. I realise `ifinish` is deprecated because it isn't always intuitionistic, but in this case it did give an intuitionistic proof. I think both should be proved the same way, but I'm including one of each to see which is preferred.

### [2020-05-13 18:31:18](https://github.com/leanprover-community/mathlib/commit/fc0c025)
refactor(scripts/mk_all): generate a single deterministic all.lean file ([#2673](https://github.com/leanprover-community/mathlib/pull/2673))
The current `mk_all.sh` script is non-deterministic, and creates invalid Lean code for the `data.matrix.notation` import.  The generated `all.lean` files are also slow: they take two minutes to compile on my machine.
The new script fixes all of that.  The single generated `all.lean` file takes only 27 seconds to compile now.

### [2020-05-13 12:20:02](https://github.com/leanprover-community/mathlib/commit/9f16f86)
feat(topology/algebra/infinite_sum): sums on subtypes ([#2659](https://github.com/leanprover-community/mathlib/pull/2659))
For `f` a summable function defined on the integers, we prove the formula
```
(∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i)
```
This is deduced from a general version on subtypes of the form `univ - s` where `s` is a finset.

### [2020-05-13 10:27:15](https://github.com/leanprover-community/mathlib/commit/c9f2cbc)
chore(scripts): update nolints.txt ([#2669](https://github.com/leanprover-community/mathlib/pull/2669))
I am happy to remove some nolints for you!

### [2020-05-13 10:27:13](https://github.com/leanprover-community/mathlib/commit/506a71f)
feat(category_theory): preadditive categories ([#2663](https://github.com/leanprover-community/mathlib/pull/2663))
[As discussed](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Lean.20in.20the.20wild/near/197168926), here is the pedestrian definition of preadditive categories. Hopefully, it is not here to stay, but it will allow me to start PRing abelian categories.

### [2020-05-13 10:27:11](https://github.com/leanprover-community/mathlib/commit/ce86d33)
feat(analysis/calculus/(f)deriv): differentiability of a finite sum of functions ([#2657](https://github.com/leanprover-community/mathlib/pull/2657))
We show that, if each `f i` is differentiable, then `λ y, ∑ i in s, f i y` is also differentiable when `s` is a finset, and give the lemmas around this for `fderiv` and `deriv`.

### [2020-05-13 07:01:46](https://github.com/leanprover-community/mathlib/commit/ed183f9)
chore(group_theory/submonoid): use `complete_lattice_of_Inf` ([#2661](https://github.com/leanprover-community/mathlib/pull/2661))
* Use `complete_lattice_of_Inf` for `submonoid` and `subgroup` lattices.
* Add `sub*.copy`.
* Add a few `@[simp]` lemmas.

### [2020-05-13 03:44:20](https://github.com/leanprover-community/mathlib/commit/51e2b4c)
feat(topology/separation): add `subtype.t1_space` and `subtype.regular` ([#2667](https://github.com/leanprover-community/mathlib/pull/2667))
Also simplify the proof of `exists_open_singleton_of_fintype`

### [2020-05-13 03:44:18](https://github.com/leanprover-community/mathlib/commit/4857284)
feat(topology/bounded_continuous_function): the normed space C^0 ([#2660](https://github.com/leanprover-community/mathlib/pull/2660))
For β a normed (vector) space over a nondiscrete normed field 𝕜, we construct the normed 𝕜-space structure on the set of bounded continuous functions from a topological space into β.

### [2020-05-13 01:57:37](https://github.com/leanprover-community/mathlib/commit/cbffb34)
feat(analysis/specific_limits): more geometric series ([#2658](https://github.com/leanprover-community/mathlib/pull/2658))
Currently, the sum of a geometric series is only known for real numbers in `[0,1)`. We prove it for any element of a normed field with norm `< 1`, and specialize it to real numbers in `(-1, 1)`.
Some lemmas in `analysis/specific_limits` are also moved around (but their content is not changed) to get a better organization of this file.

### [2020-05-12 18:35:33](https://github.com/leanprover-community/mathlib/commit/437fdaf)
feat(category_theory/creates): creates limits => preserves limits ([#2639](https://github.com/leanprover-community/mathlib/pull/2639))
Show that `F` preserves limits if it creates them and the target category has them.

### [2020-05-12 15:37:33](https://github.com/leanprover-community/mathlib/commit/1141533)
feat(data/matrix): matrix and vector notation ([#2656](https://github.com/leanprover-community/mathlib/pull/2656))
This PR adds notation for matrices and vectors [as discussed on Zulip a couple of months ago](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Notation.20for.20matrices.20and.20vectors), so that `![![a, b], ![c, d]]` constructs a 2x2 matrix with rows `![a, b] : fin 2 -> α` and `![c, d]`. It also adds corresponding `simp` lemmas for all matrix operations defined in `data.matrix.basic`. These lemmas should apply only when the input already contains `![...]`.
To express the `simp` lemmas nicely, I defined a function `dot_product : (v w : n -> α) -> α` which returns the sum of the entrywise product of two vectors. IMO, this makes the definitions of `matrix.mul`, `matrix.mul_vec` and `matrix.vec_mul` clearer, and it allows us to share some proofs. I could also inline `dot_product` (restoring the old situation) if the reviewers prefer.

### [2020-05-12 15:37:31](https://github.com/leanprover-community/mathlib/commit/34a0c8c)
chore(*): unify use of left and right for injectivity lemmas ([#2655](https://github.com/leanprover-community/mathlib/pull/2655))
This is the evil twin of [#2652](https://github.com/leanprover-community/mathlib/pull/2652) using the opposite convention: the name of a lemma stating that a function in two arguments is injective in one of the arguments refers to the argument that changes. Example:
```lean
lemma sub_right_inj : a - b = a - c ↔ b = c
```
See also the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/pow_(left.7Cright)_inj(ective)).
This PR renames lemmas following the other convention. The following lemmas were renamed:
`algebra/group/basic.lean`:
* `mul_left_injective` ↔ `mul_right_injective`
* `mul_left_inj` ↔ `mul_right_inj`
* `sub_left_inj` ↔ `sub_right_inj`
`algebra/goup/units.lean`:
* `mul_left_inj` ↔ `mul_right_inj`
* `divp_right_inj` → `divp_left_inj`
`algebra/group_power.lean`:
* `pow_right_inj` → `pow_left_inj`
`algebra/group_with_zero.lean`:
* `div_right_inj'` → ` div_left_inj'`
* `mul_right_inj'` → `mul_left_inj'`
`algebra/ring.lean`:
* `domain.mul_right_inj` ↔ `domain.mul_left_inj`
`data/finsupp.lean`:
* `single_right_inj` → `single_left_inj`
`data/list/basic.lean`:
* `append_inj_left` ↔ `append_inj_right`
* `append_inj_left'` ↔ `append_inj_right'`
* `append_left_inj` ↔ `append_right_inj`
* `prefix_append_left_inj` → `prefix_append_right_inj`
`data/nat/basic.lean`:
* `mul_left_inj` ↔ `mul_right_inj`
`data/real/ennreal.lean`:
* `add_left_inj` ↔ `add_right_inj`
* `sub_left_inj` → `sub_right_inj`
`set_theory/ordinal.lean`:
* `mul_left_inj` → `mul_right_inj`

### [2020-05-12 15:37:29](https://github.com/leanprover-community/mathlib/commit/77b3d50)
chore(topology/instances/ennreal): add +1 version of `tsum_eq_supr_sum` ([#2633](https://github.com/leanprover-community/mathlib/pull/2633))
Also add a few lemmas about `supr` and monotone functions.

### [2020-05-12 15:37:27](https://github.com/leanprover-community/mathlib/commit/ff184e6)
feat(analysis/normed_space): add Mazur-Ulam theorem ([#2214](https://github.com/leanprover-community/mathlib/pull/2214))
Based on a proof by Jussi Väisälä, see [journal version](https://www.jstor.org/stable/3647749) or [preprint on web.archive](https://web.archive.org/web/20180516125105/http://www.helsinki.fi/~jvaisala/mazurulam.pdf).
Also rename `reflection` to `point_reflection` as was suggested by @rwbarton and @PatrickMassot

### [2020-05-12 13:39:55](https://github.com/leanprover-community/mathlib/commit/3f216bc)
feat(number_theory/basic): dvd_sub_pow_of_dvd_sub ([#2640](https://github.com/leanprover-community/mathlib/pull/2640))
Co-authored with: Kenny Lau <kc_kennylau@yahoo.com.hk>

### [2020-05-12 11:31:31](https://github.com/leanprover-community/mathlib/commit/61b59ec)
fix(order/filter/basic): markdown error in module doc ([#2664](https://github.com/leanprover-community/mathlib/pull/2664))

### [2020-05-12 06:37:08](https://github.com/leanprover-community/mathlib/commit/295b87e)
feat(ring_theory/integral_domain): sum in integral domain indexed by finite group ([#2623](https://github.com/leanprover-community/mathlib/pull/2623))
In other words: nontrivial sums are trivial
Moved from `field_theory.finite` to the new `ring_theory.integral_domain`:
- `card_nth_roots_subgroup_units`
- `subgroup_units_cyclic`

### [2020-05-12 05:22:17](https://github.com/leanprover-community/mathlib/commit/f0e7817)
chore(scripts): update nolints.txt ([#2662](https://github.com/leanprover-community/mathlib/pull/2662))
I am happy to remove some nolints for you!

### [2020-05-12 01:24:40](https://github.com/leanprover-community/mathlib/commit/8c88721)
feat(data/list): assorted lemmas ([#2651](https://github.com/leanprover-community/mathlib/pull/2651))
Some lemmas I found useful for [#2578](https://github.com/leanprover-community/mathlib/pull/2578)

### [2020-05-11 13:23:56](https://github.com/leanprover-community/mathlib/commit/eb9e382)
test(tactic/norm_num): import tests from lean core ([#2654](https://github.com/leanprover-community/mathlib/pull/2654))

### [2020-05-11 11:46:09](https://github.com/leanprover-community/mathlib/commit/a87f326)
chore(scripts): update nolints.txt ([#2653](https://github.com/leanprover-community/mathlib/pull/2653))
I am happy to remove some nolints for you!

### [2020-05-11 09:42:50](https://github.com/leanprover-community/mathlib/commit/e777d0b)
refactor(data/real/pi): add tactics for pi computation ([#2641](https://github.com/leanprover-community/mathlib/pull/2641))
Depends on [#2589](https://github.com/leanprover-community/mathlib/pull/2589). Moves pi bounds from @fpvandoorn's gist to mathlib, and also adds a small tactic to uniformize the proofs (and also skip some unsqueezed proofs), making the compilation even faster (just around 1 second for the longest proofs).

### [2020-05-11 06:32:55](https://github.com/leanprover-community/mathlib/commit/ff37fb8)
feat(algebra/ring): monoid structure on `R →+* R` ([#2649](https://github.com/leanprover-community/mathlib/pull/2649))
Also add `comp_id` and `id_comp`

### [2020-05-11 03:53:42](https://github.com/leanprover-community/mathlib/commit/7146082)
refactor(data/fintype/basic): weaken assumptions of set.fintype ([#2650](https://github.com/leanprover-community/mathlib/pull/2650))

### [2020-05-10 20:24:02](https://github.com/leanprover-community/mathlib/commit/b9bdc67)
feat(*): prove some `*.iterate` theorems ([#2647](https://github.com/leanprover-community/mathlib/pull/2647))

### [2020-05-10 17:09:22](https://github.com/leanprover-community/mathlib/commit/8c6b14e)
fix(library_search): use custom apply tactic for the main goal, as well as subgoals ([#2648](https://github.com/leanprover-community/mathlib/pull/2648))
cf https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/List.20lemmas

### [2020-05-10 07:14:07](https://github.com/leanprover-community/mathlib/commit/3710744)
feat(meta/uchange): universe lifting and lowering in meta ([#2627](https://github.com/leanprover-community/mathlib/pull/2627))
We define the meta type `uchange (α : Type v) : Type u`, which permits us to change the universe of a type analogously to `ulift`.  However since `uchange` is meta, it can both lift and lower the universe.
As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/widget/near/196808542

### [2020-05-10 04:05:15](https://github.com/leanprover-community/mathlib/commit/b248481)
chore(algebra/char_zero): add `∀ n : ℕ, (n + 1 : α) ≠ 0` ([#2644](https://github.com/leanprover-community/mathlib/pull/2644))

### [2020-05-10 04:05:14](https://github.com/leanprover-community/mathlib/commit/7590090)
chore(scripts): update nolints.txt ([#2643](https://github.com/leanprover-community/mathlib/pull/2643))
I am happy to remove some nolints for you!

### [2020-05-10 00:45:41](https://github.com/leanprover-community/mathlib/commit/81f97bd)
chore(*): move to lean-3.11.0 ([#2632](https://github.com/leanprover-community/mathlib/pull/2632))
Related Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/lean.23211.20don't.20unfold.20irred.20defs

### [2020-05-09 23:30:16](https://github.com/leanprover-community/mathlib/commit/a584d52)
chore(scripts): update nolints.txt ([#2642](https://github.com/leanprover-community/mathlib/pull/2642))
I am happy to remove some nolints for you!

### [2020-05-09 20:30:31](https://github.com/leanprover-community/mathlib/commit/9f33b7d)
feat(algebra/ordered_*): arithmetic operations on monotone functions ([#2634](https://github.com/leanprover-community/mathlib/pull/2634))
Also move `strict_mono` to `order/basic` and add a module docstring.

### [2020-05-09 20:30:29](https://github.com/leanprover-community/mathlib/commit/d04429f)
chore(logic/embedding,order/order_iso): review ([#2618](https://github.com/leanprover-community/mathlib/pull/2618))
* swap `inj` with `inj'` to match other bundled homomorphisms;
* make some arguments explicit to avoid `embedding.of_surjective _`
  in the pretty printer output;
* make `set_value` computable.

### [2020-05-09 20:30:27](https://github.com/leanprover-community/mathlib/commit/08d4316)
refactor(computability/turing_machine): add list_blank ([#2605](https://github.com/leanprover-community/mathlib/pull/2605))
This ended up being a major refactor of `computability.turing_machine`. It started as a change of the definition of turing machine so that the tape is a quotient of lists up to the relation "ends with blanks", but the file is quite old and I updated it to pass the linter as well. I'm not up to speed on the new documentation requirements, but now is a good time to request them for this file. This doesn't add many new theorems, it's mostly just fixes to make it compile again after the change. (Some of the turing machine constructions are also simplified.)

### [2020-05-09 20:30:25](https://github.com/leanprover-community/mathlib/commit/b769846)
feat(tactic/norm_num): new all-lean norm_num ([#2589](https://github.com/leanprover-community/mathlib/pull/2589))
This is a first draft of the lean replacement for `tactic.norm_num` in core. This isn't completely polished yet; the rest of `norm_num` can now be a little less "global-recursive" since the primitives for e.g. adding and multiplying natural numbers are exposed.
I'm also trying out a new approach using functions like `match_neg` and `match_numeral` instead of directly pattern matching on exprs, because this generates smaller (and hopefully more efficient) code. (Without this, some of the matches were hitting the equation compiler depth limit.)
I'm open to new feature suggestions as well here. `nat.succ` and coercions seem useful to support in the core part, and additional flexibility using `def_replacer` is also on the agenda.

### [2020-05-09 17:40:41](https://github.com/leanprover-community/mathlib/commit/20c7418)
chore(data/finset): drop `to_set`, use `has_lift` instead ([#2629](https://github.com/leanprover-community/mathlib/pull/2629))
Also cleanup `coe_to_finset` lemmas. Now we have `set.finite.coe_to_finset` and `set.coe_to_finset`.

### [2020-05-09 14:34:49](https://github.com/leanprover-community/mathlib/commit/e1192f3)
feat(data/nat/basic): add `mod_add_mod` and `add_mod_mod` ([#2635](https://github.com/leanprover-community/mathlib/pull/2635))
Added the `mod_add_mod` and `add_mod_mod` lemmas for `data.nat.basic`. I copied them from `data.int.basic`, and just changed the data type. Would there be issues with it being labelled `@[simp]`?
Also, would it make sense to refactor `add_mod` above it to use `mod_add_mod` and `add_mod_mod`? It'd make it considerably shorter.
(Tangential note, there's a disparity between the `mod` lemmas for `nat` and the `mod` lemmas for `int`, for example `int` doesn't have `add_mod`, should that be added in a separate PR?)

### [2020-05-09 08:33:21](https://github.com/leanprover-community/mathlib/commit/96efc22)
feat(data/nat/cast): nat.cast_with_bot ([#2636](https://github.com/leanprover-community/mathlib/pull/2636))
As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/with_bot/near/196979007

### [2020-05-08 21:01:31](https://github.com/leanprover-community/mathlib/commit/67e19cd)
feat(src/ring_theory/algebra): define equivalence of algebras ([#2625](https://github.com/leanprover-community/mathlib/pull/2625))

### [2020-05-08 16:39:26](https://github.com/leanprover-community/mathlib/commit/fc8c4b9)
chore(`analysis/normed_space/banach`): minor review ([#2631](https://github.com/leanprover-community/mathlib/pull/2631))
* move comment to module docstring;
* don't import `bounded_linear_maps`;
* reuse `open_mapping` in `linear_equiv.continuous_symm`;
* add a few `simp` lemmas.

### [2020-05-08 01:30:44](https://github.com/leanprover-community/mathlib/commit/ac3fb4e)
chore(scripts): update nolints.txt ([#2628](https://github.com/leanprover-community/mathlib/pull/2628))
I am happy to remove some nolints for you!

### [2020-05-07 22:43:02](https://github.com/leanprover-community/mathlib/commit/a7e8039)
feat(data/equiv/encodable): `ulower` lowers countable types to `Type 0` ([#2574](https://github.com/leanprover-community/mathlib/pull/2574))
Given a type `α : Type u`, we can lift it into a higher universe using `ulift α : Type (max u v)`.  This PR introduces an analogous construction going in the other direction.  Given an encodable (= countable) type `α : Type u`, we can lower it to the very bottom using `ulower α : Type 0`.  The equivalence is primitive recursive if the type is primcodable.
The definition of the equivalence was already present as `encodable.equiv_range_encode`.  However it is very inconvenient to use since it requires decidability instances (`encodable.decidable_range_encode`) that are not enabled by default because they would introduce overlapping instances that are not definitionally equal.

### [2020-05-07 21:02:37](https://github.com/leanprover-community/mathlib/commit/ed453c7)
chore(data/polynomial): remove unused argument ([#2626](https://github.com/leanprover-community/mathlib/pull/2626))

### [2020-05-07 18:46:03](https://github.com/leanprover-community/mathlib/commit/bdce195)
chore(linear_algebra/basic): review ([#2616](https://github.com/leanprover-community/mathlib/pull/2616))
* several new `simp` lemmas;
* use `linear_equiv.coe_coe` instead of `coe_apply`;
* rename `sup_quotient_to_quotient_inf` to `quotient_inf_to_sup_quotient` because it better reflects the definition; similarly for `equiv`.
* make `general_linear_group` reducible.

### [2020-05-07 15:51:38](https://github.com/leanprover-community/mathlib/commit/5d3b830)
refactor(order/lattice): add `sup/inf_eq_*`, rename `inf_le_inf_*` ([#2624](https://github.com/leanprover-community/mathlib/pull/2624))
## New lemmas:
* `sup_eq_right : a ⊔ b = b ↔a ≤ b`, and similarly for `sup_eq_left`, `left_eq_sup`, `right_eq_sup`,
  `inf_eq_right`, `inf_eq_left`, `left_eq_inf`, and `right_eq_inf`; all these lemmas are `@[simp]`;
* `sup_elim` and `inf_elim`: if `(≤)` is a total order, then `p a → p b → p (a ⊔ b)`, and similarly for `inf`.
## Renamed
* `inf_le_inf_right` is now `inf_le_inf_left` and vice versa. This agrees with `sup_le_sup_left`/`sup_le_sup_right`, and the rest of the library.
* `ord_continuous_sup` -> `ord_continuous.sup`;
* `ord_continuous_mono` -> `ord_continuous.mono`.

### [2020-05-07 13:09:37](https://github.com/leanprover-community/mathlib/commit/6c48444)
feat(algebra/lie_algebra): `lie_algebra.of_associative_algebra` is functorial ([#2620](https://github.com/leanprover-community/mathlib/pull/2620))
More precisely we:
  * define the Lie algebra homomorphism associated to a morphism of associative algebras
  * prove that the correspondence is functorial
  * prove that subalgebras and Lie subalgebras correspond

### [2020-05-07 10:25:22](https://github.com/leanprover-community/mathlib/commit/da10afc)
feat(*): define `equiv.reflection` and `isometry.reflection` ([#2609](https://github.com/leanprover-community/mathlib/pull/2609))
Define reflection in a point and prove basic properties.
It is defined both as an `equiv.perm` of an `add_comm_group` and
as an `isometric` of a `normed_group`.
Other changes:
* rename `two_smul` to `two_smul'`, add `two_smul` using `semimodule`
  instead of `add_monoid.smul`;
* minor review of `algebra.midpoint`;
* arguments of `isometry.dist_eq` and `isometry.edist_eq` are now explicit;
* rename `isometry.inv` to `isometry.right_inv`; now it takes `right_inverse`
  instead of `equiv`;
* drop `isometry_inv_fun`: use `h.symm.isometry` instead;
* pull a few more lemmas about `equiv` and `isometry` to the `isometric` namespace.

### [2020-05-07 07:12:04](https://github.com/leanprover-community/mathlib/commit/a6415d7)
chore(data/set/basic): use implicit args in `set.ext_iff` ([#2619](https://github.com/leanprover-community/mathlib/pull/2619))
Most other `ext_iff` lemmas use implicit arguments, let `set.ext_iff` use them too.

### [2020-05-07 02:39:51](https://github.com/leanprover-community/mathlib/commit/f6edeba)
chore(scripts): update nolints.txt ([#2622](https://github.com/leanprover-community/mathlib/pull/2622))
I am happy to remove some nolints for you!

### [2020-05-07 00:42:46](https://github.com/leanprover-community/mathlib/commit/a8eafb6)
chore(scripts): update nolints.txt ([#2621](https://github.com/leanprover-community/mathlib/pull/2621))
I am happy to remove some nolints for you!

### [2020-05-06 22:41:38](https://github.com/leanprover-community/mathlib/commit/0c8d2e2)
chore(data/set/countable): use dot syntax here and there ([#2617](https://github.com/leanprover-community/mathlib/pull/2617))
Renamed:
* `exists_surjective_of_countable` -> `countable.exists_surjective`;
* `countable_subset` -> `countable.mono`;
* `countable_image` -> `countable.image`;
* `countable_bUnion` -> `countable.bUnion`;
* `countable_sUnion` -> `countable.sUnion`;
* `countable_union` -> `countable.union`;
* `countable_insert` -> `countable.insert`;
* `countable_finite` -> `finite.countable`;
Add:
* `finset.countable_to_set`

### [2020-05-06 19:39:53](https://github.com/leanprover-community/mathlib/commit/c3d76d0)
chore(*): a few missing `simp` lemmas ([#2615](https://github.com/leanprover-community/mathlib/pull/2615))
Also replaces `monoid_hom.exists_inv_of_comp_exists_inv` with `monoid_hom.map_exists_right_inv` and adds `monoid_hom.map_exists_left_inv`.

### [2020-05-06 19:39:51](https://github.com/leanprover-community/mathlib/commit/460d9d4)
refactor(data/equiv/local_equiv, topology/local_homeomorph): use coercions ([#2603](https://github.com/leanprover-community/mathlib/pull/2603))
Local equivs and local homeomorphisms use `e.to_fun x` and `e.inv_fun x`, instead of coercions as in most of mathlib, as there were problems with coercions that made them unusable in manifolds. These problems have been fixed in Lean 3.10, so we switch to coercions for them also.
This is 95% a refactor PR, erasing `.to_fun` and replacing `.inv_fun` with `.symm` in several files, and fixing proofs. Plus a few simp lemmas on the coercions to let things go smoothly. I have also linted all the files I have touched.

### [2020-05-06 19:39:49](https://github.com/leanprover-community/mathlib/commit/b1c0398)
feat(analysis/analytic/composition): the composition of formal series is associative ([#2513](https://github.com/leanprover-community/mathlib/pull/2513))
The composition of formal multilinear series is associative. I will need this when doing the analytic local inverse theorem, and I was surprised by how nontrivial this is: one should show that two double sums coincide by reindexing, but the reindexing is combinatorially tricky (it involves joining and splitting lists carefully). 
Preliminary material on lists, sums and compositions is done in [#2501](https://github.com/leanprover-community/mathlib/pull/2501) and [#2554](https://github.com/leanprover-community/mathlib/pull/2554), and the proof is in this PR.

### [2020-05-06 16:31:27](https://github.com/leanprover-community/mathlib/commit/0a7ff10)
feat(algebra/units): some norm_cast attributes ([#2612](https://github.com/leanprover-community/mathlib/pull/2612))

### [2020-05-06 14:05:37](https://github.com/leanprover-community/mathlib/commit/93a64da)
chore(data/pnat/basic): add `mk_le_mk`, `mk_lt_mk`, `coe_le_coe`, `coe_lt_coe` ([#2613](https://github.com/leanprover-community/mathlib/pull/2613))

### [2020-05-06 09:03:06](https://github.com/leanprover-community/mathlib/commit/5593155)
feat(*): lemmas on sums and products over fintypes ([#2598](https://github.com/leanprover-community/mathlib/pull/2598))

### [2020-05-06 02:11:34](https://github.com/leanprover-community/mathlib/commit/4503f8f)
chore(scripts): update nolints.txt ([#2610](https://github.com/leanprover-community/mathlib/pull/2610))
I am happy to remove some nolints for you!

### [2020-05-05 22:33:19](https://github.com/leanprover-community/mathlib/commit/c7593cc)
refactor(field_theory): move finite_card.lean into finite.lean ([#2607](https://github.com/leanprover-community/mathlib/pull/2607))

### [2020-05-05 22:33:16](https://github.com/leanprover-community/mathlib/commit/0db59db)
feat(data/equiv/basic): some elementary equivs ([#2602](https://github.com/leanprover-community/mathlib/pull/2602))

### [2020-05-05 20:16:28](https://github.com/leanprover-community/mathlib/commit/359031f)
refactor(*): remove instance max depth ([#2608](https://github.com/leanprover-community/mathlib/pull/2608))
With current Lean, all the manual increases of the maximum instance depth have become unnecessary. This PR removes them all.

### [2020-05-05 19:08:14](https://github.com/leanprover-community/mathlib/commit/a66d0a8)
chore(field_theory/finite): meaningful variable names ([#2606](https://github.com/leanprover-community/mathlib/pull/2606))

### [2020-05-05 14:29:27](https://github.com/leanprover-community/mathlib/commit/0c1b60b)
feat(group_theory/order_of_element): order_of_eq_prime ([#2604](https://github.com/leanprover-community/mathlib/pull/2604))

### [2020-05-05 08:02:15](https://github.com/leanprover-community/mathlib/commit/7a367f3)
feat(algebra/char_p): add lemma ring_char_ne_one ([#2595](https://github.com/leanprover-community/mathlib/pull/2595))
This lemma is more useful than the extant `false_of_nonzero_of_char_one`
when we are working with the function `ring_char` rather than the `char_p`
Prop.

### [2020-05-05 06:09:07](https://github.com/leanprover-community/mathlib/commit/91b3906)
feat(data/polynomial): misc on derivatives of polynomials ([#2596](https://github.com/leanprover-community/mathlib/pull/2596))
Co-authored by: @alexjbest

### [2020-05-05 04:42:12](https://github.com/leanprover-community/mathlib/commit/d6ddfd2)
feat(algebra/midpoint): define `midpoint`, prove basic properties ([#2599](https://github.com/leanprover-community/mathlib/pull/2599))
Part of [#2214](https://github.com/leanprover-community/mathlib/pull/2214)

### [2020-05-04 22:27:29](https://github.com/leanprover-community/mathlib/commit/1c4b5ec)
feat(ring_theory/ideals): quotient map to residue field as ring hom ([#2597](https://github.com/leanprover-community/mathlib/pull/2597))

### [2020-05-04 10:57:29](https://github.com/leanprover-community/mathlib/commit/14aa1f7)
feat(combinatorics/composition): refactor compositions, split a list wrt a composition ([#2554](https://github.com/leanprover-community/mathlib/pull/2554))
Refactor `composition`, replacing in its definition a list of positive integers with a list of integers which are positive. This avoids going back and forth all the time between `nat` and `pnat`.
Also introduce the ability to split a list of length `n` with respect to a composition `c` of `n`, giving rise to a list of `c.length` sublists whose join is the original list.

### [2020-05-04 05:40:22](https://github.com/leanprover-community/mathlib/commit/70245f4)
feat(algebra/big_operators): prod_comp ([#2594](https://github.com/leanprover-community/mathlib/pull/2594))
This is a lemma that @jcommelin looks like he could have used in Chevalley Warning, and is probably useful elsewhere.

### [2020-05-03 12:27:43](https://github.com/leanprover-community/mathlib/commit/08a17d6)
chore(scripts): update nolints.txt ([#2593](https://github.com/leanprover-community/mathlib/pull/2593))
I am happy to remove some nolints for you!

### [2020-05-03 08:34:26](https://github.com/leanprover-community/mathlib/commit/a223bbb)
chore(*): switch to lean 3.10.0 ([#2587](https://github.com/leanprover-community/mathlib/pull/2587))
There have been two changes in Lean 3.10 that have a significant effect on mathlib:
 - `rename'` has been moved to core.  Therefore `rename'` has been removed.
 - Given a term `⇑f x`, the simplifier can now rewrite in both `f` and `x`.  In many cases we had both `⇑f = ⇑f'` and `⇑f x = ⇑f' x` as simp lemmas; the latter is redundant now and has been removed (or just not marked simp anymore).  The new and improved congruence lemmas are also used by `convert` and `congr`, these tactics have become more powerful as well.
I've also sneaked in two related changes that I noticed while fixing the proofs affected by the changes above:
 - `@[to_additive, simp]` has been replaced by `@[simp, to_additive]` in the monoid localization file.  The difference is that `@[to_additive, simp]` only marks the multiplicative lemma as simp.
 - `def prod_comm : α × β ≃ β × α` (etc.) is no longer marked `@[simp]`.  Marking this kind of lemmas as simp causes the simplifier to unfold the definition of `prod_comm` (instead of just rewriting `α × β` to `β × α` in the `≃` simp relation).  This has become a bigger issue now since the simplifier can rewrite the `f` in `⇑f x`.

### [2020-05-02 22:38:27](https://github.com/leanprover-community/mathlib/commit/d1eae21)
chore(build.yml): Don't build nolints branch ([#2591](https://github.com/leanprover-community/mathlib/pull/2591))

### [2020-05-02 15:22:25](https://github.com/leanprover-community/mathlib/commit/a99f9b5)
refactor(algebra/big_operators): introduce notation for finset.prod and finset.sum ([#2582](https://github.com/leanprover-community/mathlib/pull/2582))
I have not gone through all of mathlib to use this notation everywhere. I think we can maybe transition naturally.

### [2020-05-02 12:33:54](https://github.com/leanprover-community/mathlib/commit/1cc83e9)
chore(algebra/ordered_field): move inv_neg to field and prove for division ring ([#2588](https://github.com/leanprover-community/mathlib/pull/2588))
`neg_inv` this lemma with the equality swapped was already in the library, so maybe we should just get rid of this or `neg_inv`
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/inv_neg/near/196042954)

### [2020-05-02 09:41:43](https://github.com/leanprover-community/mathlib/commit/b902f6e)
feat(*): several `@[simp]` lemmas ([#2579](https://github.com/leanprover-community/mathlib/pull/2579))
Also add an explicit instance for `submodule.has_coe_to_sort`.
This way `rintro ⟨x, hx⟩` results in `(hx : x ∈ p)`.
Also fixes some timeouts introduced by [#2363](https://github.com/leanprover-community/mathlib/pull/2363). See Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/partrec_code

### [2020-05-02 09:41:41](https://github.com/leanprover-community/mathlib/commit/06bae3e)
fix(data/int/basic): use has_coe_t to prevent looping ([#2573](https://github.com/leanprover-community/mathlib/pull/2573))
The file `src/computability/partrec.lean` no longer opens in vscode because type-class search times out.  This happens because we have the instance `has_coe ℤ α` which causes non-termination because coercions are chained transitively (`has_coe ℤ ℤ`, `has_coe ℤ ℤ`, ...).  Even if the coercions would not apply to integers (and maybe avoid non-termination), it would still enumerate all `0,1,+,-` structures, of which there are unfortunately very many.
This PR therefore downgrades such instances to `has_coe_t` to prevent non-termination due to transitivity.  It also adds a linter to prevent this kind of error in the future.

### [2020-05-02 09:41:39](https://github.com/leanprover-community/mathlib/commit/9d57f68)
feat(order/bounded_lattice): introduce `is_compl` predicate ([#2569](https://github.com/leanprover-community/mathlib/pull/2569))
Also move `disjoint` from `data/set/lattice`

### [2020-05-02 08:31:10](https://github.com/leanprover-community/mathlib/commit/738bbae)
feat(algebra/group_ring_action): action on polynomials ([#2586](https://github.com/leanprover-community/mathlib/pull/2586))

### [2020-05-02 06:01:16](https://github.com/leanprover-community/mathlib/commit/d0a1d77)
doc(tactic/rcases): mention the "rfl" pattern ([#2585](https://github.com/leanprover-community/mathlib/pull/2585))
Edited from @jcommelin's answer on Zulip here: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/noob.20question%28s%29/near/184491982

### [2020-05-01 21:31:28](https://github.com/leanprover-community/mathlib/commit/eb383b1)
chore(group_theory/perm): delete duplicate lemmas ([#2584](https://github.com/leanprover-community/mathlib/pull/2584))
`sum_univ_perm` is a special case of `sum_equiv`, so it's not necessary. 
I also moved `sum_equiv` into the `finset` namespace.

### [2020-05-01 15:51:57](https://github.com/leanprover-community/mathlib/commit/4daa7e8)
feat(algebra/lie_algebra): define simple Lie algebras and define classical Lie algebra, slₙ ([#2567](https://github.com/leanprover-community/mathlib/pull/2567))
The changes here introduce a few important properties of Lie algebras and also begin providing definitions of the classical Lie algebras. The key changes are the following definitions:
 * `lie_algebra.is_abelian`
 * `lie_module.is_irreducible`
 * `lie_algebra.is_simple`
 * `lie_algebra.special_linear.sl`
Some simple related proofs are also included such as:
 * `commutative_ring_iff_abelian_lie_ring`
 * `lie_algebra.special_linear.sl_non_abelian`

### [2020-05-01 12:56:42](https://github.com/leanprover-community/mathlib/commit/6a2559a)
chore(algebra/group_with_zero): rename div_eq_inv_mul' to div_eq_inv_mul ([#2583](https://github.com/leanprover-community/mathlib/pull/2583))
There are no occurrences of the name without ' in either core or mathlib
so this change in name (from [#2242](https://github.com/leanprover-community/mathlib/pull/2242)) seems to have been unnecessary.

### [2020-05-01 10:09:30](https://github.com/leanprover-community/mathlib/commit/ee488b2)
fix(tactic/lint/basic): remove default argument for auto_decl and enable more linters ([#2580](https://github.com/leanprover-community/mathlib/pull/2580))
Run more linters on automatically-generated declarations.  Quite a few linters should have been run on them, but I forgot about it because the `auto_decls` flag is optional and off by default.  I've made it non-optional so that you don't forget about it when defining a linter.
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/simp.20linter.20and.20structure.20fields/near/195810856

### [2020-05-01 07:42:20](https://github.com/leanprover-community/mathlib/commit/67f3fde)
feat(algebra/group_ring_action) define group actions on rings ([#2566](https://github.com/leanprover-community/mathlib/pull/2566))
Define group action on rings.
Related Zulip discussions: 
- https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.232566.20group.20actions.20on.20ring 
- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mul_action

### [2020-05-01 05:59:47](https://github.com/leanprover-community/mathlib/commit/74d24ab)
feat(topology/instances/real_vector_space): `E →+ F` to `E →L[ℝ] F` ([#2577](https://github.com/leanprover-community/mathlib/pull/2577))
A continuous additive map between two vector spaces over `ℝ` is `ℝ`-linear.

### [2020-05-01 04:49:00](https://github.com/leanprover-community/mathlib/commit/d3140fb)
feat(data/mv_polynomial): lemmas on total_degree ([#2575](https://github.com/leanprover-community/mathlib/pull/2575))
This is a small preparation for the Chevalley–Warning theorem.