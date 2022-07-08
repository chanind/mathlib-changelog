from crawler.extract_diff_info import extract_diff_changes


SAMPLE_ADD_LEMMAS_DIFF = """
@@ -1921,6 +1921,15 @@ lemma map_comm {β'} {f : β ↪ γ} {g : α ↪ β} {f' : α ↪ β'} {g' : β'
   (s.map g).map f = (s.map f').map g' :=
 by simp_rw [map_map, embedding.trans, function.comp, h_comm]
 
+lemma _root_.function.semiconj.finset_map {f : α ↪ β} {ga : α ↪ α} {gb : β ↪ β}
+  (h : function.semiconj f ga gb) :
+  function.semiconj (map f) (map ga) (map gb) :=
+λ s, map_comm h
+
+lemma _root_.function.commute.finset_map {f g : α ↪ α} (h : function.commute f g) :
+  function.commute (map f) (map g) :=
+h.finset_map
+
 @[simp] theorem map_subset_map {s₁ s₂ : finset α} : s₁.map f ⊆ s₂.map f ↔ s₁ ⊆ s₂ :=
 ⟨λ h x xs, (mem_map' _).1 $ h $ (mem_map' f).2 xs,
  λ h, by simp [subset_def, map_subset_map h]⟩
@@ -2095,6 +2104,16 @@ lemma image_comm {β'} [decidable_eq β'] [decidable_eq γ] {f : β → γ} {g :
   (s.image g).image f = (s.image f').image g' :=
 by simp_rw [image_image, comp, h_comm]
 
+lemma _root_.function.semiconj.finset_image [decidable_eq α] {f : α → β} {ga : α → α} {gb : β → β}
+  (h : function.semiconj f ga gb) :
+  function.semiconj (image f) (image ga) (image gb) :=
+λ s, image_comm h
+
+lemma _root_.function.commute.finset_image [decidable_eq α] {f g : α → α}
+  (h : function.commute f g) :
+  function.commute (image f) (image g) :=
+h.finset_image
+
 theorem image_subset_image {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f :=
 by simp only [subset_def, image_val, subset_dedup', dedup_subset',
   multiset.map_subset_map h]
"""

SAMPLE_MODIFY_LEMMAS_DIFF_COMPLEX = """
@@ -480,7 +480,7 @@ by simp only [is_unit_iff, group.is_unit, and_true]
 
 include β
 
-@[to_additive] lemma map_inv' : f⁻¹.map m = (f.map m)⁻¹ := map_comm (funext $ map_inv m) _
+@[to_additive] lemma map_inv' : f⁻¹.map m = (f.map m)⁻¹ := semiconj.filter_map (map_inv m) f
 
 @[to_additive] lemma tendsto.inv_inv : tendsto m f₁ f₂ → tendsto m f₁⁻¹ f₂⁻¹ :=
 λ hf, (filter.map_inv' m).trans_le $ filter.inv_le_inv hf
"""

SAMPLE_MIXED_DIFF = """
@@ -30,7 +30,7 @@ The space `lp E p` is the subtype of elements of `Π i : α, E i` which satisfy
 * `lp E p` : elements of `Π i : α, E i` such that `mem_ℓp f p`. Defined as an `add_subgroup` of
   a type synonym `pre_lp` for `Π i : α, E i`, and equipped with a `normed_group` structure.
   Under appropriate conditions, this is also equipped with the instances `lp.normed_space`,
-  `lp.complete_space`, and `lp.normed_ring`.
+  `lp.complete_space`. For `p=∞`, there is also `lp.infty_normed_ring`, `lp.infty_normed_algebra`.
 
 ## Main results
 
@@ -577,7 +577,7 @@ variables (E p 𝕜)
 
 /-- The `𝕜`-submodule of elements of `Π i : α, E i` whose `lp` norm is finite.  This is `lp E p`,
 with extra structure. -/
-def lp_submodule : submodule 𝕜 (pre_lp E) :=
+def _root_.lp_submodule : submodule 𝕜 (pre_lp E) :=
 { smul_mem' := λ c f hf, by simpa using mem_lp_const_smul c ⟨f, hf⟩,
   .. lp E p }
 
@@ -665,65 +665,65 @@ instance : non_unital_normed_ring (lp B ∞) :=
 
 -- we also want a `non_unital_normed_comm_ring` instance, but this has to wait for #13719
 
+instance infty_is_scalar_tower {𝕜} [normed_field 𝕜] [Π i, normed_space 𝕜 (B i)]
+  [Π i, is_scalar_tower 𝕜 (B i) (B i)] :
+  is_scalar_tower 𝕜 (lp B ∞) (lp B ∞) :=
+⟨λ r f g, lp.ext $ smul_assoc r ⇑f ⇑g⟩
+
+instance infty_smul_comm_class {𝕜} [normed_field 𝕜] [Π i, normed_space 𝕜 (B i)]
+  [Π i, smul_comm_class 𝕜 (B i) (B i)] :
+  smul_comm_class 𝕜 (lp B ∞) (lp B ∞) :=
+⟨λ r f g, lp.ext $ smul_comm r ⇑f ⇑g⟩
+
 end non_unital_normed_ring
 
 section normed_ring
 
-variables {I : Type*} {B : I → Type*} [Π i, normed_ring (B i)] [Π i, norm_one_class (B i)]
+variables {I : Type*} {B : I → Type*} [Π i, normed_ring (B i)]
+
+instance _root_.pre_lp.ring : ring (pre_lp B) := pi.ring
+
+variables [Π i, norm_one_class (B i)]
 
 lemma _root_.one_mem_ℓp_infty : mem_ℓp (1 : Π i, B i) ∞ :=
 ⟨1, by { rintros i ⟨i, rfl⟩, exact norm_one.le,}⟩
 
-instance : has_one (lp B ∞) :=
-{ one := ⟨(1 : Π i, B i), one_mem_ℓp_infty⟩ }
+variables (B)
 
-@[simp] lemma infty_coe_fn_one : ⇑(1 : lp B ∞) = 1 := rfl
+/-- The `𝕜`-subring of elements of `Π i : α, B i` whose `lp` norm is finite. This is `lp E ∞`,
+with extra structure. -/
+def _root_.lp_infty_subring : subring (pre_lp B) :=
+{ carrier := {f | mem_ℓp f ∞},
+  one_mem' := one_mem_ℓp_infty,
+  mul_mem' := λ f g hf hg, hf.infty_mul hg,
+  .. lp B ∞ }
 
-lemma _root_.mem_ℓp.infty_pow {f : Π i, B i} (hf : mem_ℓp f ∞) (n : ℕ) : mem_ℓp (f ^ n) ∞ :=
-begin
-  induction n with n hn,
-  { rw pow_zero,
-    exact one_mem_ℓp_infty },
-  { rw pow_succ,
-    exact hf.infty_mul hn }
-end
+variables {B}
 
-instance [nonempty I] : norm_one_class (lp B ∞) :=
-{ norm_one := by simp_rw [lp.norm_eq_csupr, infty_coe_fn_one, pi.one_apply, norm_one, csupr_const]}
-
-instance : has_pow (lp B ∞) ℕ := { pow := λ f n, ⟨_, f.prop.infty_pow n⟩ }
+instance infty_ring : ring (lp B ∞) := (lp_infty_subring B).to_ring
 
-@[simp] lemma infty_coe_fn_pow (f : lp B ∞) (n : ℕ) : ⇑(f ^ n) = f ^ n := rfl
+lemma _root_.mem_ℓp.infty_pow {f : Π i, B i} (hf : mem_ℓp f ∞) (n : ℕ) : mem_ℓp (f ^ n) ∞ :=
+(lp_infty_subring B).pow_mem hf n
 
-lemma _root_.nat_cast_mem_ℓp_infty : ∀ (n : ℕ), mem_ℓp (n : Π i, B i) ∞
-| 0 := by { rw nat.cast_zero, exact zero_mem_ℓp }
-| (n + 1) := by { rw nat.cast_succ, exact (_root_.nat_cast_mem_ℓp_infty n).add one_mem_ℓp_infty }
+lemma _root_.nat_cast_mem_ℓp_infty (n : ℕ) : mem_ℓp (n : Π i, B i) ∞ :=
+nat_cast_mem (lp_infty_subring B) n
 
-instance : has_nat_cast (lp B ∞) := { nat_cast := λ n, ⟨(↑n : Π i, B i), nat_cast_mem_ℓp_infty _⟩ }
+lemma _root_.int_cast_mem_ℓp_infty (z : ℤ) : mem_ℓp (z : Π i, B i) ∞ :=
+coe_int_mem (lp_infty_subring B) z
 
-@[simp] lemma infty_coe_fn_nat_cast (n : ℕ) : ⇑(n : lp B ∞) = n := rfl
+@[simp] lemma infty_coe_fn_one : ⇑(1 : lp B ∞) = 1 := rfl
 
-lemma _root_.int_cast_mem_ℓp_infty (z : ℤ) : mem_ℓp (z : Π i, B i) ∞ :=
-begin
-  obtain ⟨n, rfl | rfl⟩ := z.eq_coe_or_neg,
-  { rw int.cast_coe_nat,
-    exact nat_cast_mem_ℓp_infty n },
-  { rw [int.cast_neg, int.cast_coe_nat],
-    exact (nat_cast_mem_ℓp_infty n).neg }
-end
+@[simp] lemma infty_coe_fn_pow (f : lp B ∞) (n : ℕ) : ⇑(f ^ n) = f ^ n := rfl
 
-instance : has_int_cast (lp B ∞) := { int_cast := λ z, ⟨(↑z : Π i, B i), int_cast_mem_ℓp_infty _⟩ }
+@[simp] lemma infty_coe_fn_nat_cast (n : ℕ) : ⇑(n : lp B ∞) = n := rfl
 
 @[simp] lemma infty_coe_fn_int_cast (z : ℤ) : ⇑(z : lp B ∞) = z := rfl
 
-instance : ring (lp B ∞) :=
-function.injective.ring lp.has_coe_to_fun.coe subtype.coe_injective
-  (lp.coe_fn_zero B ∞) (infty_coe_fn_one) lp.coe_fn_add infty_coe_fn_mul
-  lp.coe_fn_neg lp.coe_fn_sub (λ _ _, rfl) (λ _ _, rfl) infty_coe_fn_pow
-  infty_coe_fn_nat_cast infty_coe_fn_int_cast
+instance [nonempty I] : norm_one_class (lp B ∞) :=
+{ norm_one := by simp_rw [lp.norm_eq_csupr, infty_coe_fn_one, pi.one_apply, norm_one, csupr_const]}
 
-instance : normed_ring (lp B ∞) :=
-{ .. lp.ring, .. lp.non_unital_normed_ring }
+instance infty_normed_ring : normed_ring (lp B ∞) :=
+{ .. lp.infty_ring, .. lp.non_unital_normed_ring }
 
 end normed_ring
 
@@ -731,15 +731,50 @@ section normed_comm_ring
 
 variables {I : Type*} {B : I → Type*} [Π i, normed_comm_ring (B i)] [∀ i, norm_one_class (B i)]
 
-instance : comm_ring (lp B ∞) :=
+instance infty_comm_ring : comm_ring (lp B ∞) :=
 { mul_comm := λ f g, by { ext, simp only [lp.infty_coe_fn_mul, pi.mul_apply, mul_comm] },
-  .. lp.ring }
+  .. lp.infty_ring }
 
-instance : normed_comm_ring (lp B ∞) :=
-{ .. lp.comm_ring, .. lp.normed_ring }
+instance infty_normed_comm_ring : normed_comm_ring (lp B ∞) :=
+{ .. lp.infty_comm_ring, .. lp.infty_normed_ring }
 
 end normed_comm_ring
 
+section algebra
+variables {I : Type*} {𝕜 : Type*} {B : I → Type*}
+variables [normed_field 𝕜] [Π i, normed_ring (B i)] [Π i, normed_algebra 𝕜 (B i)]
+
+/-- A variant of `pi.algebra` that lean can't find otherwise. -/
+instance _root_.pi.algebra_of_normed_algebra : algebra 𝕜 (Π i, B i) :=
+@pi.algebra I 𝕜 B _ _ $ λ i, normed_algebra.to_algebra
+
+instance _root_.pre_lp.algebra : algebra 𝕜 (pre_lp B) := _root_.pi.algebra_of_normed_algebra
+
+variables [∀ i, norm_one_class (B i)]
+
+lemma _root_.algebra_map_mem_ℓp_infty (k : 𝕜) : mem_ℓp (algebra_map 𝕜 (Π i, B i) k) ∞ :=
+begin
+  rw algebra.algebra_map_eq_smul_one,
+  exact (one_mem_ℓp_infty.const_smul k : mem_ℓp (k • 1 : Π i, B i) ∞)
+end
+
+variables (𝕜 B)
+
+/-- The `𝕜`-subalgebra of elements of `Π i : α, B i` whose `lp` norm is finite. This is `lp E ∞`,
+with extra structure. -/
+def _root_.lp_infty_subalgebra : subalgebra 𝕜 (pre_lp B) :=
+{ carrier := {f | mem_ℓp f ∞},
+  algebra_map_mem' := algebra_map_mem_ℓp_infty,
+  .. lp_infty_subring B }
+
+variables {𝕜 B}
+
+instance infty_normed_algebra : normed_algebra 𝕜 (lp B ∞) :=
+{ ..(lp_infty_subalgebra 𝕜 B).algebra,
+  ..(lp.normed_space : normed_space 𝕜 (lp B ∞)) }
+
+end algebra
+
 section single
 variables {𝕜 : Type*} [normed_field 𝕜] [Π i, normed_space 𝕜 (E i)]
 variables [decidable_eq α]
"""


def test_extract_diff_changes_finds_added_lemmas():
    changes = extract_diff_changes(SAMPLE_ADD_LEMMAS_DIFF)
    assert changes.added_lemmas == [
        "_root_.function.semiconj.finset_map",
        "_root_.function.commute.finset_map",
        "_root_.function.semiconj.finset_image",
        "_root_.function.commute.finset_image",
    ]
    assert changes.deleted_lemmas == []
    assert changes.added_theorems == []
    assert changes.deleted_theorems == []
    assert changes.added_defs == []
    assert changes.deleted_defs == []


def test_extract_diff_changes_finds_modified_lemmas_with_decorators():
    changes = extract_diff_changes(SAMPLE_MODIFY_LEMMAS_DIFF_COMPLEX)
    assert changes.added_lemmas == ["map_inv'"]
    assert changes.deleted_lemmas == ["map_inv'"]
    assert changes.added_theorems == []
    assert changes.deleted_theorems == []
    assert changes.added_defs == []
    assert changes.deleted_defs == []


def test_extract_diff_changes_finds_mixed_lemmas_and_defs():
    changes = extract_diff_changes(SAMPLE_MIXED_DIFF)
    assert changes.added_lemmas == [
        "_root_.mem_ℓp.infty_pow",
        "_root_.nat_cast_mem_ℓp_infty",
        "_root_.int_cast_mem_ℓp_infty",
        "infty_coe_fn_one",
        "infty_coe_fn_pow",
        "infty_coe_fn_nat_cast",
        "_root_.algebra_map_mem_ℓp_infty",
    ]
    assert changes.deleted_lemmas == [
        "infty_coe_fn_one",
        "_root_.mem_ℓp.infty_pow",
        "infty_coe_fn_pow",
        "_root_.nat_cast_mem_ℓp_infty",
        "infty_coe_fn_nat_cast",
        "_root_.int_cast_mem_ℓp_infty",
    ]
    assert changes.added_theorems == []
    assert changes.deleted_theorems == []
    assert changes.added_defs == [
        "_root_.lp_submodule",
        "_root_.lp_infty_subring",
        "_root_.lp_infty_subalgebra",
    ]
    assert changes.deleted_defs == ["lp_submodule"]
