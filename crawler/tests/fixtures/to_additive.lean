/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn
-/
import tactic.transform_decl
import tactic.algebra
import tactic.lint.basic
import tactic.alias

/-!
# Transport multiplicative to additive

This file defines an attribute `to_additive` that can be used to
automatically transport theorems and definitions (but not inductive
types and structures) from a multiplicative theory to an additive theory.

Usage information is contained in the doc string of `to_additive.attr`.

### Missing features

* Automatically transport structures and other inductive types.

* For structures, automatically generate theorems like `group α ↔
  add_group (additive α)`.
-/

namespace to_additive
open tactic
setup_tactic_parser

section performance_hack -- see Note [user attribute parameters]

local attribute [semireducible] reflected

/-- Temporarily change the `has_reflect` instance for `name`. -/
local attribute [instance, priority 9000]
meta def hacky_name_reflect : has_reflect name :=
λ n, `(id %%(expr.const n []) : name)

/-- An auxiliary attribute used to store the names of the additive versions of declarations
that have been processed by `to_additive`. -/
@[user_attribute]
meta def aux_attr : user_attribute (name_map name) name :=
{ name      := `to_additive_aux,
  descr     := "Auxiliary attribute for `to_additive`. DON'T USE IT",
  parser    := failed,
  cache_cfg := ⟨λ ns,
                ns.mfoldl
                  (λ dict n', do
                   let n := match n' with
                            | name.mk_string s pre := if s = "_to_additive" then pre else n'
                            | _ := n'
                            end,
                    param ← aux_attr.get_param_untyped n',
                    pure $ dict.insert n param.app_arg.const_name)
                  mk_name_map, []⟩ }

end performance_hack

section extra_attributes

/--
An attribute that tells `@[to_additive]` that certain arguments of this definition are not
involved when using `@[to_additive]`.
This helps the heuristic of `@[to_additive]` by also transforming definitions if `ℕ` or another
fixed type occurs as one of these arguments.
-/
@[user_attribute]
meta def ignore_args_attr : user_attribute (name_map $ list ℕ) (list ℕ) :=
{ name      := `to_additive_ignore_args,
  descr     :=
    "Auxiliary attribute for `to_additive` stating that certain arguments are not additivized.",
  cache_cfg :=
    ⟨λ ns, ns.mfoldl
      (λ dict n, do
        param ← ignore_args_attr.get_param_untyped n, -- see Note [user attribute parameters]
        return $ dict.insert n (param.to_list expr.to_nat).iget)
      mk_name_map, []⟩,
  parser    := (lean.parser.small_nat)* }

/--
An attribute that is automatically added to declarations tagged with `@[to_additive]`, if needed.

This attribute tells which argument is the type where this declaration uses the multiplicative
structure. If there are multiple argument, we typically tag the first one.
If this argument contains a fixed type, this declaration will note be additivized.
See the Heuristics section of `to_additive.attr` for more details.

If a declaration is not tagged, it is presumed that the first argument is relevant.
`@[to_additive]` uses the function `to_additive.first_multiplicative_arg` to automatically tag
declarations. It is ok to update it manually if the automatic tagging made an error.

Implementation note: we only allow exactly 1 relevant argument, even though some declarations
(like `prod.group`) have multiple arguments with a multiplicative structure on it.
The reason is that whether we additivize a declaration is an all-or-nothing decision, and if
we will not be able to additivize declarations that (e.g.) talk about multiplication on `ℕ × α`
anyway.

Warning: adding `@[to_additive_reorder]` with an equal or smaller number than the number in this
attribute is currently not supported.
-/
@[user_attribute]
meta def relevant_arg_attr : user_attribute (name_map ℕ) ℕ :=
{ name      := `to_additive_relevant_arg,
  descr     :=
    "Auxiliary attribute for `to_additive` stating which arguments are the types with a " ++
    "multiplicative structure.",
  cache_cfg :=
    ⟨λ ns, ns.mfoldl
      (λ dict n, do
        param ← relevant_arg_attr.get_param_untyped n, -- see Note [user attribute parameters]
        -- we subtract 1 from the values provided by the user.
        return $ dict.insert n $ param.to_nat.iget.pred)
      mk_name_map, []⟩,
  parser    := lean.parser.small_nat }

/--
An attribute that stores all the declarations that needs their arguments reordered when
applying `@[to_additive]`. Currently, we only support swapping consecutive arguments.
The list of the natural numbers contains the positions of the first of the two arguments
to be swapped.
If the first two arguments are swapped, the first two universe variables are also swapped.
Example: `@[to_additive_reorder 1 4]` swaps the first two arguments and the arguments in
positions 4 and 5.
-/
@[user_attribute]
meta def reorder_attr : user_attribute (name_map $ list ℕ) (list ℕ) :=
{ name      := `to_additive_reorder,
  descr     :=
    "Auxiliary attribute for `to_additive` that stores arguments that need to be reordered.",
  cache_cfg :=
    ⟨λ ns, ns.mfoldl
      (λ dict n, do
        param ← reorder_attr.get_param_untyped n, -- see Note [user attribute parameters]
        return $ dict.insert n (param.to_list expr.to_nat).iget)
      mk_name_map, []⟩,
  parser    := do
    l ← (lean.parser.small_nat)*,
    guard (l.all (≠ 0)) <|> exceptional.fail "The reorder positions must be positive",
    return l }

end extra_attributes

/--
Find the first argument of `nm` that has a multiplicative type-class on it.
Returns 1 if there are no types with a multiplicative class as arguments.
E.g. `prod.group` returns 1, and `pi.has_one` returns 2.
-/
meta def first_multiplicative_arg (nm : name) : tactic ℕ := do
  d ← get_decl nm,
  let (es, _) := d.type.pi_binders,
  l ← es.mmap_with_index $ λ n bi, do
  { let tgt := bi.type.pi_codomain,
    let n_bi := bi.type.pi_binders.fst.length,
    tt ← has_attribute' `to_additive tgt.get_app_fn.const_name | return none,
    let n2 := tgt.get_app_args.head.get_app_fn.match_var.map $ λ m, n + n_bi - m,
    return $ n2 },
  let l := l.reduce_option,
  return $ if l = [] then 1 else l.foldr min l.head

/-- A command that can be used to have future uses of `to_additive` change the `src` namespace
to the `tgt` namespace.

For example:
```
run_cmd to_additive.map_namespace `quotient_group `quotient_add_group
```

Later uses of `to_additive` on declarations in the `quotient_group` namespace will be created
in the `quotient_add_group` namespaces.
-/
meta def map_namespace (src tgt : name) : command :=
do let n := src.mk_string "_to_additive",
   let decl := declaration.thm n [] `(unit) (pure (reflect ())),
   add_decl decl,
   aux_attr.set n tgt tt

/-- `value_type` is the type of the arguments that can be provided to `to_additive`.
`to_additive.parser` parses the provided arguments:
* `replace_all`: replace all multiplicative declarations, do not use the heuristic.
* `trace`: output the generated additive declaration.
* `tgt : name`: the name of the target (the additive declaration).
* `doc`: an optional doc string.
* if `allow_auto_name` is `ff` (default) then `@[to_additive]` will check whether the given name
  can be auto-generated.
-/
@[derive has_reflect, derive inhabited]
structure value_type : Type :=
(replace_all : bool)
(trace : bool)
(tgt : name)
(doc : option string)
(allow_auto_name : bool)

/-- `add_comm_prefix x s` returns `"comm_" ++ s` if `x = tt` and `s` otherwise. -/
meta def add_comm_prefix : bool → string → string
| tt s := "comm_" ++ s
| ff s := s

/-- Dictionary used by `to_additive.guess_name` to autogenerate names. -/
meta def tr : bool → list string → list string
| is_comm ("one" :: "le" :: s)        := add_comm_prefix is_comm "nonneg"    :: tr ff s
| is_comm ("one" :: "lt" :: s)        := add_comm_prefix is_comm "pos"       :: tr ff s
| is_comm ("le" :: "one" :: s)        := add_comm_prefix is_comm "nonpos"    :: tr ff s
| is_comm ("lt" :: "one" :: s)        := add_comm_prefix is_comm "neg"       :: tr ff s
| is_comm ("mul" :: "single" :: s)    := add_comm_prefix is_comm "single"    :: tr ff s
| is_comm ("mul" :: "support" :: s)   := add_comm_prefix is_comm "support"   :: tr ff s
| is_comm ("mul" :: "tsupport" :: s)  := add_comm_prefix is_comm "tsupport"  :: tr ff s
| is_comm ("mul" :: "indicator" :: s) := add_comm_prefix is_comm "indicator" :: tr ff s
| is_comm ("mul" :: s)                := add_comm_prefix is_comm "add"       :: tr ff s
| is_comm ("smul" :: s)               := add_comm_prefix is_comm "vadd"      :: tr ff s
| is_comm ("inv" :: s)                := add_comm_prefix is_comm "neg"       :: tr ff s
| is_comm ("div" :: s)                := add_comm_prefix is_comm "sub"       :: tr ff s
| is_comm ("one" :: s)                := add_comm_prefix is_comm "zero"      :: tr ff s
| is_comm ("prod" :: s)               := add_comm_prefix is_comm "sum"       :: tr ff s
| is_comm ("finprod" :: s)            := add_comm_prefix is_comm "finsum"    :: tr ff s
| is_comm ("pow" :: s)                := add_comm_prefix is_comm "nsmul"     :: tr ff s
| is_comm ("npow" :: s)               := add_comm_prefix is_comm "nsmul"     :: tr ff s
| is_comm ("zpow" :: s)               := add_comm_prefix is_comm "zsmul"     :: tr ff s
| is_comm ("is" :: "square" :: s)     := add_comm_prefix is_comm "even"      :: tr ff s
| is_comm ("is" :: "regular" :: s)    := add_comm_prefix is_comm "is_add_regular"   :: tr ff s
| is_comm ("is" :: "left" :: "regular" :: s)  :=
  add_comm_prefix is_comm "is_add_left_regular"  :: tr ff s
| is_comm ("is" :: "right" :: "regular" :: s) :=
  add_comm_prefix is_comm "is_add_right_regular" :: tr ff s
| is_comm ("monoid" :: s)      := ("add_" ++ add_comm_prefix is_comm "monoid")    :: tr ff s
| is_comm ("submonoid" :: s)   := ("add_" ++ add_comm_prefix is_comm "submonoid") :: tr ff s
| is_comm ("group" :: s)       := ("add_" ++ add_comm_prefix is_comm "group")     :: tr ff s
| is_comm ("subgroup" :: s)    := ("add_" ++ add_comm_prefix is_comm "subgroup")  :: tr ff s
| is_comm ("semigroup" :: s)   := ("add_" ++ add_comm_prefix is_comm "semigroup") :: tr ff s
| is_comm ("magma" :: s)       := ("add_" ++ add_comm_prefix is_comm "magma")     :: tr ff s
| is_comm ("haar" :: s)        := ("add_" ++ add_comm_prefix is_comm "haar")      :: tr ff s
| is_comm ("prehaar" :: s)     := ("add_" ++ add_comm_prefix is_comm "prehaar")   :: tr ff s
| is_comm ("unit" :: s)        := ("add_" ++ add_comm_prefix is_comm "unit")      :: tr ff s
| is_comm ("units" :: s)       := ("add_" ++ add_comm_prefix is_comm "units")     :: tr ff s
| is_comm ("comm" :: s)        := tr tt s
| is_comm (x :: s)             := (add_comm_prefix is_comm x :: tr ff s)
| tt []                        := ["comm"]
| ff []                        := []

/-- Autogenerate target name for `to_additive`. -/
meta def guess_name : string → string :=
string.map_tokens ''' $
λ s, string.intercalate (string.singleton '_') $
tr ff (s.split_on '_')

/-- Return the provided target name or autogenerate one if one was not provided. -/
meta def target_name (src tgt : name) (dict : name_map name) (allow_auto_name : bool) :
  tactic name :=
(if tgt.get_prefix ≠ name.anonymous ∨ allow_auto_name -- `tgt` is a full name
 then pure tgt
 else match src with
      | (name.mk_string s pre) :=
        do let tgt_auto := guess_name s,
           guard (tgt.to_string ≠ tgt_auto ∨ tgt = src)
             <|> trace ("`to_additive " ++ src.to_string ++ "`: correctly autogenerated target " ++
               "name, you may remove the explicit " ++ tgt_auto ++ " argument."),
           pure $ name.mk_string
                 (if tgt = name.anonymous then tgt_auto else tgt.to_string)
                 (pre.map_prefix dict.find)
      | _ := fail ("to_additive: can't transport " ++ src.to_string)
      end) >>=
(λ res,
  if res = src ∧ tgt ≠ src
  then fail ("to_additive: can't transport " ++ src.to_string ++ " to itself.
Give the desired additive name explicitly using `@[to_additive additive_name]`. ")
  else pure res)

/-- the parser for the arguments to `to_additive`. -/
meta def parser : lean.parser value_type :=
do
  bang ← option.is_some <$> (tk "!")?,
  ques ← option.is_some <$> (tk "?")?,
  tgt ← ident?,
  e ← texpr?,
  doc ← match e with
      | some pe := some <$> ((to_expr pe >>= eval_expr string) : tactic string)
      | none := pure none
      end,
  return ⟨bang, ques, tgt.get_or_else name.anonymous, doc, ff⟩

private meta def proceed_fields_aux (src tgt : name) (prio : ℕ) (f : name → tactic (list string)) :
  command :=
do
  src_fields ← f src,
  tgt_fields ← f tgt,
  guard (src_fields.length = tgt_fields.length) <|>
    fail ("Failed to map fields of " ++ src.to_string),
  (src_fields.zip tgt_fields).mmap' $
    λ names, guard (names.fst = names.snd) <|>
      aux_attr.set (src.append names.fst) (tgt.append names.snd) tt prio

/-- Add the `aux_attr` attribute to the structure fields of `src`
so that future uses of `to_additive` will map them to the corresponding `tgt` fields. -/
meta def proceed_fields (env : environment) (src tgt : name) (prio : ℕ) : command :=
let aux := proceed_fields_aux src tgt prio in
do
aux (λ n, pure $ list.map name.to_string $ (env.structure_fields n).get_or_else []) >>
aux (λ n, (list.map (λ (x : name), "to_" ++ x.to_string) <$> get_tagged_ancestors n)) >>
aux (λ n, (env.constructors_of n).mmap $
          λ cs, match cs with
                | (name.mk_string s pre) :=
                  (guard (pre = n) <|> fail "Bad constructor name") >>
                  pure s
                | _ := fail "Bad constructor name"
                end)

/--
The attribute `to_additive` can be used to automatically transport theorems
and definitions (but not inductive types and structures) from a multiplicative
theory to an additive theory.

To use this attribute, just write:

```
@[to_additive]
theorem mul_comm' {α} [comm_semigroup α] (x y : α) : x * y = y * x := comm_semigroup.mul_comm
```

This code will generate a theorem named `add_comm'`. It is also
possible to manually specify the name of the new declaration:

```
@[to_additive add_foo]
theorem foo := sorry
```

An existing documentation string will _not_ be automatically used, so if the theorem or definition
has a doc string, a doc string for the additive version should be passed explicitly to
`to_additive`.

```
/-- Multiplication is commutative -/
@[to_additive "Addition is commutative"]
theorem mul_comm' {α} [comm_semigroup α] (x y : α) : x * y = y * x := comm_semigroup.mul_comm
```

The transport tries to do the right thing in most cases using several
heuristics described below.  However, in some cases it fails, and
requires manual intervention.

If the declaration to be transported has attributes which need to be
copied to the additive version, then `to_additive` should come last:

```
@[simp, to_additive] lemma mul_one' {G : Type*} [group G] (x : G) : x * 1 = x := mul_one x
```

The following attributes are supported and should be applied correctly by `to_additive` to
the new additivized declaration, if they were present on the original one:
```
reducible, _refl_lemma, simp, norm_cast, instance, refl, symm, trans, elab_as_eliminator, no_rsimp,
continuity, ext, ematch, measurability, alias, _ext_core, _ext_lemma_core, nolint
```

The exception to this rule is the `simps` attribute, which should come after `to_additive`:

```
@[to_additive, simps]
instance {M N} [has_mul M] [has_mul N] : has_mul (M × N) := ⟨λ p q, ⟨p.1 * q.1, p.2 * q.2⟩⟩
```

Additionally the `mono` attribute is not handled by `to_additive` and should be applied afterwards
to both the original and additivized lemma.

## Implementation notes

The transport process generally works by taking all the names of
identifiers appearing in the name, type, and body of a declaration and
creating a new declaration by mapping those names to additive versions
using a simple string-based dictionary and also using all declarations
that have previously been labeled with `to_additive`.

In the `mul_comm'` example above, `to_additive` maps:
* `mul_comm'` to `add_comm'`,
* `comm_semigroup` to `add_comm_semigroup`,
* `x * y` to `x + y` and `y * x` to `y + x`, and
* `comm_semigroup.mul_comm'` to `add_comm_semigroup.add_comm'`.

### Heuristics

`to_additive` uses heuristics to determine whether a particular identifier has to be
mapped to its additive version. The basic heuristic is

* Only map an identifier to its additive version if its first argument doesn't
  contain any unapplied identifiers.

Examples:
* `@has_mul.mul ℕ n m` (i.e. `(n * m : ℕ)`) will not change to `+`, since its
  first argument is `ℕ`, an identifier not applied to any arguments.
* `@has_mul.mul (α × β) x y` will change to `+`. It's first argument contains only the identifier
  `prod`, but this is applied to arguments, `α` and `β`.
* `@has_mul.mul (α × ℤ) x y` will not change to `+`, since its first argument contains `ℤ`.

The reasoning behind the heuristic is that the first argument is the type which is "additivized",
and this usually doesn't make sense if this is on a fixed type.

There are some exceptions to this heuristic:

* Identifiers that have the `@[to_additive]` attribute are ignored.
  For example, multiplication in `↥Semigroup` is replaced by addition in `↥AddSemigroup`.
* If an identifier `d` has attribute `@[to_additive_relevant_arg n]` then the argument
  in position `n` is checked for a fixed type, instead of checking the first argument.
  `@[to_additive]` will automatically add the attribute `@[to_additive_relevant_arg n]` to a
  declaration when the first argument has no multiplicative type-class, but argument `n` does.
* If an identifier has attribute `@[to_additive_ignore_args n1 n2 ...]` then all the arguments in
  positions `n1`, `n2`, ... will not be checked for unapplied identifiers (start counting from 1).
  For example, `cont_mdiff_map` has attribute `@[to_additive_ignore_args 21]`, which means
  that its 21st argument `(n : with_top ℕ)` can contain `ℕ`
  (usually in the form `has_top.top ℕ ...`) and still be additivized.
  So `@has_mul.mul (C^∞⟮I, N; I', G⟯) _ f g` will be additivized.

### Troubleshooting

If `@[to_additive]` fails because the additive declaration raises a type mismatch, there are
various things you can try.
The first thing to do is to figure out what `@[to_additive]` did wrong by looking at the type
mismatch error.

* Option 1: It additivized a declaration `d` that should remain multiplicative. Solution:
  * Make sure the first argument of `d` is a type with a multiplicative structure. If not, can you
    reorder the (implicit) arguments of `d` so that the first argument becomes a type with a
    multiplicative structure (and not some indexing type)?
    The reason is that `@[to_additive]` doesn't additivize declarations if their first argument
    contains fixed types like `ℕ` or `ℝ`. See section Heuristics.
    If the first argument is not the argument with a multiplicative type-class, `@[to_additive]`
    should have automatically added the attribute `@[to_additive_relevant_arg]` to the declaration.
    You can test this by running the following (where `d` is the full name of the declaration):
    ```
      run_cmd to_additive.relevant_arg_attr.get_param `d >>= tactic.trace
    ```
    The expected output is `n` where the `n`-th argument of `d` is a type (family) with a
    multiplicative structure on it. If you get a different output (or a failure), you could add
    the attribute `@[to_additive_relevant_arg n]` manually, where `n` is an argument with a
    multiplicative structure.
* Option 2: It didn't additivize a declaration that should be additivized.
  This happened because the heuristic applied, and the first argument contains a fixed type,
  like `ℕ` or `ℝ`. Solutions:
  * If the fixed type has an additive counterpart (like `↥Semigroup`), give it the `@[to_additive]`
    attribute.
  * If the fixed type occurs inside the `k`-th argument of a declaration `d`, and the
    `k`-th argument is not connected to the multiplicative structure on `d`, consider adding
    attribute `[to_additive_ignore_args k]` to `d`.
  * If you want to disable the heuristic and replace all multiplicative
    identifiers with their additive counterpart, use `@[to_additive!]`.
* Option 3: Arguments / universe levels are incorrectly ordered in the additive version.
  This likely only happens when the multiplicative declaration involves `pow`/`^`. Solutions:
  * Ensure that the order of arguments of all relevant declarations are the same for the
    multiplicative and additive version. This might mean that arguments have an "unnatural" order
    (e.g. `monoid.npow n x` corresponds to `x ^ n`, but it is convenient that `monoid.npow` has this
    argument order, since it matches `add_monoid.nsmul n x`.
  * If this is not possible, add the `[to_additive_reorder k]` to the multiplicative declaration
    to indicate that the `k`-th and `(k+1)`-st arguments are reordered in the additive version.

If neither of these solutions work, and `to_additive` is unable to automatically generate the
additive version of a declaration, manually write and prove the additive version.
Often the proof of a lemma/theorem can just be the multiplicative version of the lemma applied to
`multiplicative G`.
Afterwards, apply the attribute manually:

```
attribute [to_additive foo_add_bar] foo_bar
```

This will allow future uses of `to_additive` to recognize that
`foo_bar` should be replaced with `foo_add_bar`.

### Handling of hidden definitions

Before transporting the “main” declaration `src`, `to_additive` first
scans its type and value for names starting with `src`, and transports
them. This includes auxiliary definitions like `src._match_1`,
`src._proof_1`.

In addition to transporting the “main” declaration, `to_additive` transports
its equational lemmas and tags them as equational lemmas for the new declaration,
attributes present on the original equational lemmas are also transferred first (notably
`_refl_lemma`).

### Structure fields and constructors

If `src` is a structure, then `to_additive` automatically adds
structure fields to its mapping, and similarly for constructors of
inductive types.

For new structures this means that `to_additive` automatically handles
coercions, and for old structures it does the same, if ancestry
information is present in `@[ancestor]` attributes. The `ancestor`
attribute must come before the `to_additive` attribute, and it is
essential that the order of the base structures passed to `ancestor` matches
between the multiplicative and additive versions of the structure.

### Name generation

* If `@[to_additive]` is called without a `name` argument, then the
  new name is autogenerated.  First, it takes the longest prefix of
  the source name that is already known to `to_additive`, and replaces
  this prefix with its additive counterpart. Second, it takes the last
  part of the name (i.e., after the last dot), and replaces common
  name parts (“mul”, “one”, “inv”, “prod”) with their additive versions.

* Namespaces can be transformed using `map_namespace`. For example:
  ```
  run_cmd to_additive.map_namespace `quotient_group `quotient_add_group
  ```

  Later uses of `to_additive` on declarations in the `quotient_group`
  namespace will be created in the `quotient_add_group` namespaces.

* If `@[to_additive]` is called with a `name` argument `new_name`
  /without a dot/, then `to_additive` updates the prefix as described
  above, then replaces the last part of the name with `new_name`.

* If `@[to_additive]` is called with a `name` argument
  `new_namespace.new_name` /with a dot/, then `to_additive` uses this
  new name as is.

As a safety check, in the first case `to_additive` double checks
that the new name differs from the original one.

-/
@[user_attribute]
protected meta def attr : user_attribute unit value_type :=
{ name      := `to_additive,
  descr     := "Transport multiplicative to additive",
  parser    := parser,
  after_set := some $ λ src prio persistent, do
    guard persistent <|> fail "`to_additive` can't be used as a local attribute",
    env ← get_env,
    val ← attr.get_param src,
    dict ← aux_attr.get_cache,
    ignore ← ignore_args_attr.get_cache,
    relevant ← relevant_arg_attr.get_cache,
    reorder ← reorder_attr.get_cache,
    tgt ← target_name src val.tgt dict val.allow_auto_name,
    aux_attr.set src tgt tt,
    let dict := dict.insert src tgt,
    first_mult_arg ← first_multiplicative_arg src,
    when (first_mult_arg ≠ 1) $ relevant_arg_attr.set src first_mult_arg tt,
    if env.contains tgt
    then proceed_fields env src tgt prio
    else do
      transform_decl_with_prefix_dict dict val.replace_all val.trace relevant ignore reorder src tgt
        [`reducible, `_refl_lemma, `simp, `norm_cast, `instance, `refl, `symm, `trans,
          `elab_as_eliminator, `no_rsimp, `continuity, `ext, `ematch, `measurability, `alias,
          `_ext_core, `_ext_lemma_core, `nolint, `protected],
      mwhen (has_attribute' `simps src)
        (trace "Apply the simps attribute after the to_additive attribute"),
      mwhen (has_attribute' `mono src)
        (trace $ "to_additive does not work with mono, apply the mono attribute to both" ++
          "versions after"),
      match val.doc with
      | some doc := add_doc_string tgt doc
      | none := do
        some alias_name ← tactic.alias.get_alias_target src | skip,
        some add_alias_name ← pure (dict.find alias_name) | skip,
        add_doc_string tgt ("**Alias** of `" ++ to_string add_alias_name ++ "`.")
      end }

add_tactic_doc
{ name                     := "to_additive",
  category                 := doc_category.attr,
  decl_names               := [`to_additive.attr],
  tags                     := ["transport", "environment", "lemma derivation"] }

end to_additive

/- map operations -/
attribute [to_additive] has_mul has_one has_inv has_div
/- the following types are supported by `@[to_additive]` and mapped to themselves. -/
attribute [to_additive empty] empty
attribute [to_additive pempty] pempty
attribute [to_additive punit] punit
attribute [to_additive unit] unit

section linter

open tactic expr

/-- A linter that checks that multiplicative and additive lemmas have both doc strings if one of
them has one -/
@[linter] meta def linter.to_additive_doc : linter :=
{ test := (λ d, do
    let mul_name := d.to_name,
    dict ← to_additive.aux_attr.get_cache,
    match dict.find mul_name with
    | some add_name := do
      mul_doc ← try_core $ doc_string mul_name,
      add_doc ← try_core $ doc_string add_name,
      match mul_doc.is_some, add_doc.is_some with
      | tt, ff := return $ some $ "declaration has a docstring, but its additive version `" ++
          add_name.to_string ++ "` does not. You might want to pass a string argument to " ++
          "`to_additive`."
      | ff, tt := return $ some $ "declaration has no docstring, but its additive version `" ++
          add_name.to_string ++ "` does. You might want to add a doc string to the declaration."
      | _, _ := return none
      end
    | none := return none
    end),
  auto_decls := ff,
  no_errors_found := "Multiplicative and additive lemmas are consistently documented",
  errors_found := "The following declarations have doc strings, but their additive versions do " ++
  "not (or vice versa).",
  is_fast := ff }

end linter
