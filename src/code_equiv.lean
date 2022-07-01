import A_map
import mathlib.nat

/-!
# Equivalence of codes


## Main declarations

* `con_nf.height`: Height of a code
* `con_nf.code.equiv`: Equivalence of codes
-/

open set with_bot

universe u

namespace con_nf
open params
variables [params.{u}] {α β γ δ : Λ} [phase_1a.{u} α] {hβ : β ≤ α}

/-! ### Height of a code -/

/-- The height of a code is the amount of iterated images under an inverse alternative extension map
that it admits. This is uniquely defined since any code has at most one inverse image under the
A-map, and we can just repeat this process until no inverse image exists. -/
noncomputable def height : nonempty_code α β hβ → ℕ
| c := @dite _ (∃ d, A_map_rel d c) (classical.dec _) (λ h, height h.some + 1) (λ _, 0)
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨A_map_rel, A_map_rel_well_founded hβ⟩],
  dec_tac := `[exact h.some_spec] }

lemma height_eq_zero {c : nonempty_code α β hβ} : height c = 0 ↔ ∀ d, ¬ A_map_rel d c :=
begin
  classical,
  rw height,
  refine (ne.dite_eq_right_iff $ λ h, _).trans not_exists,
  exact nat.succ_ne_zero _,
end

lemma height_ne_zero {c : nonempty_code α β hβ} : height c ≠ 0 ↔ ∃ d, A_map_rel d c :=
height_eq_zero.not.trans $ by { push_neg, refl }

@[simp] lemma height_A_map_code {hδ : δ < β} (c : nonempty_code α β hβ) (hcδ : c.1.extension ≠ δ) :
  height (A_map_code hδ c) = height c + 1 :=
begin
  classical,
  have h : ∃ d, A_map_rel d (A_map_code hδ c) := ⟨c, A_map_rel.intro _ _ hcδ⟩,
  rw [height, dif_pos h, A_map_rel_subsingleton _ h.some_spec (A_map_rel.intro _ _ hcδ)],
end

lemma height_even_of_A_map_code_not_even {γ : Λ} (hγ : γ < β) (c : nonempty_code α β hβ)
  (hcγ : c.1.extension ≠ γ) (hc : ¬ even (height c)) : even (height $ A_map_code hγ c) :=
by { rw [height_A_map_code c hcγ, nat.even_succ], exact hc }

lemma coe_A_map_code_ne_singleton {γ : type_index} {hγ : γ < β} {hδ : δ < β}
  {g : tangle α γ (hγ.trans_le $ coe_le_coe.2 hβ)} {c : nonempty_code α β hβ} :
  (A_map_code hδ c : code α β hβ) ≠ ⟨γ, hγ, {g}⟩ :=
begin
  simp only [A_map_code, coe_A_map, subtype.coe_mk, ne.def, eq_self_iff_true, heq_iff_eq, true_and],
  rintro ⟨rfl, h⟩,
  refine (cardinal.one_lt_aleph_0.trans_le $ κ_regular.aleph_0_le.trans κ_le_μ).not_le _,
  rw [←cardinal.mk_singleton g, ←h.eq],
  exact μ_le_mk_A_map _ ⟨(c : code α β hβ).elts, c.2⟩,
end

@[simp] lemma height_singleton {γ : type_index} {hγ : γ < β}
  (g : tangle α γ $ hγ.trans_le $ coe_le_coe.2 hβ) :
  height (⟨⟨γ, hγ, {g}⟩, singleton_nonempty _⟩ : nonempty_code α β hβ) = 0 :=
begin
  refine height_eq_zero.2 (λ c hc, _),
  obtain ⟨δ, hδ, hc, h⟩ := (A_map_rel_iff _ _).1 hc,
  exact coe_A_map_code_ne_singleton (congr_arg subtype.val h.symm),
end

@[simp] lemma height_base (c : nonempty_code α β hβ) (hc : c.val.extension = ⊥) : height c = 0 :=
by { rw height_eq_zero, rintro d ⟨γ, hγ, -⟩, exact coe_ne_bot hc }

/-! ### A⁻¹ and equivalence of codes -/

/-- The inverse map to `A_map_code`. -/
noncomputable def A_inverse (c : nonempty_code α β hβ) (hc : height c ≠ 0) : nonempty_code α β hβ :=
(height_ne_zero.1 hc).some

lemma A_inverse_spec (c : nonempty_code α β hβ) (hc) : A_map_rel (A_inverse c hc) c :=
(height_ne_zero.1 hc).some_spec

namespace code
variables {c d : code α β hβ}

/-- Equivalence of codes. -/
@[mk_iff] inductive equiv : code α β hβ → code α β hβ → Prop
| refl (c) : equiv c c
| empty_empty (γ hγ δ hδ) : equiv ⟨γ, hγ, ∅⟩ ⟨δ, hδ, ∅⟩
| A_map_left (c : nonempty_code α β hβ) (hc : even (height c)) (γ) (hγ : γ < β)
  (hcγ : c.1.extension ≠ γ) : equiv (A_map_code hγ c) c
| A_map_right (c : nonempty_code α β hβ) (hc : even (height c)) (γ) (hγ : γ < β)
  (hcγ : c.1.extension ≠ γ) : equiv c (A_map_code hγ c)
| A_map_A_map (c : nonempty_code α β hβ) (hc : even (height c)) (γ) (hγ : γ < β)
  (hcγ : c.1.extension ≠ γ) (δ) (hδ : δ < β) (hcδ : c.1.extension ≠ δ) :
    equiv (A_map_code hγ c) (A_map_code hδ c)

/-! We declare new notation for code equivalence. -/
infix ` ≡ `:50 := equiv

attribute [refl] equiv.refl

lemma equiv.rfl : c ≡ c := equiv.refl _

lemma equiv.symm : symmetric ((≡) : code α β hβ → code α β hβ → Prop)
| _ _ (equiv.refl _) := equiv.refl _
| _ _ (equiv.empty_empty γ hγ δ hδ) := equiv.empty_empty _ _ _ _
| _ _ (equiv.A_map_left c γ hγ hc hcγ) := equiv.A_map_right c γ hγ hc hcγ
| _ _ (equiv.A_map_right c γ hγ hc hcγ) := equiv.A_map_left c γ hγ hc hcγ
| _ _ (equiv.A_map_A_map c hc γ hγ hcγ δ hδ hcδ) := equiv.A_map_A_map c hc δ hδ hcδ γ hγ hcγ

lemma equiv_transitive : transitive ((≡) : code α β hβ → code α β hβ → Prop) := sorry
-- | _ _ _ (equiv.refl _) _ := ‹_›
-- | _ _ _ _ (equiv.refl _) := ‹_›
-- | _ _ _ (equiv.empty_empty hγ hδ) (equiv.empty_empty _ hε) := equiv.empty_empty _ _
-- | _ _ _ (equiv.A_map_left γ hγ _ hcγ _) (equiv.A_map_right δ hδ c hcδ h) := sorry
-- | _ _ _ (equiv.A_map_right c hc γ hγ h) (equiv.A_map_left _ _ _ _ _) := equiv.refl _
-- | _ _ _ (equiv.empty_empty hγ _) (equiv.A_map_right δ hδ c hcδ h) := _

lemma equiv_equivalence : equivalence ((≡) : code α β hβ → code α β hβ → Prop) :=
⟨equiv.refl, equiv.symm, equiv_transitive⟩

lemma equiv.nonempty_iff_nonempty :
  ∀ {c d : code α β hβ}, c ≡ d → (c.elts.nonempty ↔ d.elts.nonempty)
| _ _ (equiv.refl _) := iff.rfl
| _ _ (equiv.empty_empty γ hγ δ hδ) := iff_of_false not_nonempty_empty not_nonempty_empty
| _ _ (equiv.A_map_left c hc γ hγ h) := iff_of_true (A_map_code _ _).2 c.2
| _ _ (equiv.A_map_right c hc γ hγ h) := iff_of_true c.2 (A_map_code _ _).2
| _ _ (equiv.A_map_A_map c hc γ hγ hcγ δ hδ hcδ) :=
  iff_of_true (A_map_code _ _).2 (A_map_code _ _).2

lemma equiv.ext : ∀ {c d : code α β hβ}, c ≡ d → c.extension = d.extension → c = d
| _ _ (equiv.refl _) _ := rfl
| _ _ (equiv.empty_empty γ hγ δ hδ) rfl := rfl
| _ _ (equiv.A_map_left c hc γ hγ h) H := (h H.symm).elim
| _ _ (equiv.A_map_right c hc γ hγ h) H := (h H).elim
| _ _ (equiv.A_map_A_map c hc γ hγ hcγ δ hδ hcδ) H :=
  by { have : γ = δ := coe_injective H, subst this }

lemma singleton_equiv (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) (g : tangle α γ _) :
  (⟨γ, coe_lt_coe.2 hγ, {g}⟩ : code α β hβ) ≡
    ⟨δ, coe_lt_coe.2 hδ, to_tangle δ (hδ.trans_le hβ) ''
      local_cardinal (f_map γ δ (coe_lt_coe.2 (hγ.trans_le hβ)) (hδ.trans_le hβ) g)⟩ :=
begin
  convert code.equiv.A_map_right ⟨⟨γ, coe_lt_coe.2 hγ, {g}⟩, singleton_nonempty g⟩ _ _ hδ
    (coe_ne_coe.2 hγδ),
  { simp only [coe_A_map, subtype.coe_mk, mem_singleton_iff, Union_Union_eq_left] },
  { rw height_singleton,
    exact even_zero }
end

lemma singleton_equiv_iff {hγ : γ < β} {g : tangle _ _ _} {c : code α β hβ} :
  ⟨γ, coe_lt_coe.2 hγ, {g}⟩ ≡ c ↔
    c = ⟨γ, coe_lt_coe.2 hγ, {g}⟩ ∨
      ∃ δ (hc : c.extension = some δ) (hδ : δ < β) (hγδ : γ ≠ δ),
        c = A_map_code hδ ⟨⟨γ, coe_lt_coe.2 hγ, {g}⟩, singleton_nonempty g⟩ :=
begin
  classical,
  refine ⟨λ h, _, _⟩,
  {
    sorry
    -- cases h,
    -- dsimp at h,
    -- rw dif_pos (singleton_nonempty g) at h,
    -- have : even (height ⟨⟨γ, coe_lt_coe.2 hγ, {g}⟩, singleton_nonempty g⟩),
    -- { convert even_zero,
    --   simp },
    -- rw dif_neg (nat.even_iff_not_odd.mp this) at h,
    -- cases c with δ hδ D,
    -- split_ifs at h,
    -- { left,
    --   dsimp at h_1,
    --   subst h_1,
    --   simp at h,
    --   rw h },
    -- { right,
    --   cases δ; dsimp at h,
    --   { cases h },
    --   { rw ← h,
    --     exact ⟨δ, by { simp, refl }, coe_lt_coe.1 hδ, h_1 ∘ coe_eq_coe.2, rfl⟩ } }
        },
  { rintro (rfl | ⟨δ, hc, hδ, hγδ, rfl⟩),
    { refl },
    { convert singleton_equiv hγ hδ hγδ g,
      simp } }
end

lemma extension_eq_of_singleton_equiv_singleton (hγ : γ < β) (hδ : δ < β) {a b : tangle α _ _}
  (h : (⟨γ, coe_lt_coe.2 hγ, {a}⟩ : code α β hβ) ≡ ⟨δ, coe_lt_coe.2 hδ, {b}⟩) :
  γ = δ :=
begin
  cases singleton_equiv_iff.1 h,
  { simp at h_1,
    exact coe_eq_coe.1 h_1.left.symm },
  { exfalso,
    obtain ⟨ε, hc, hε, hγε, hA⟩ := h_1,
    have := congr_arg code.extension hA,
    simp at this,
    rw coe_eq_coe at this,
    subst this,
    simp at hA,
    sorry,
    -- exact hA
    }
end

/- Yaël: Do we really need this lemma? looks like `extension_eq_of_singleton_equiv_singleton` is
just as practical -/
lemma eq_of_singleton_equiv_singleton (hβ : β ≤ α) (hγ : γ < β) (hδ : δ < β) (a b : tangle _ _ _)
  (h : (⟨γ, coe_lt_coe.2 hγ, {a}⟩ : code α β hβ) ≡ ⟨δ, coe_lt_coe.2 hδ, {b}⟩) :
  a = cast (by simp_rw extension_eq_of_singleton_equiv_singleton _ _ h) b :=
begin
  sorry,
  -- cases singleton_equiv_iff.mp h,
  -- { simp at h_1,
  --   have := coe_eq_coe.1 h_1.left,
  --   subst this,
  --   simp at h_1 ⊢,
  --   exact h_1.symm },
  -- { exfalso,
  --   obtain ⟨ε, hc, hε, hγε, hA⟩ := h_1,
  --   have := congr_arg code.extension hA,
  --   simp at this,
  --   rw coe_eq_coe at this,
  --   subst this,
  --   simp at hA,
  --   exact hA }
end

/-!
Note for whoever is formalising this: feel free to reorder these definitions if it turns out
to be useful to use some lemmas in the proofs of others.
-/

/-- A code is representative if it is empty and has preferred extension `⊥`, or it is nonempty and
has even height. -/
@[mk_iff] inductive is_representative : code α β hβ → Prop
| empty : is_representative ⟨⊥, bot_lt_coe _, ∅⟩
| nonempty (c : nonempty_code α β hβ) : even (height c) → is_representative c

lemma is_representative.A_map (c d : nonempty_code α β hβ)
  (hc : c.val.is_representative) (hd : d.val.is_representative)
  {γ : Λ} (hγ : γ < β) (hγd : d.val.extension ≠ γ) : c ≠ A_map_code hγ d :=
begin
  intro h,
  have := height_A_map_code d hγd, rw ← h at this,
  rw is_representative_iff at hc hd,
  cases hc, { dsimp at hc, have := c.prop, rw hc at this, exact set.not_nonempty_empty this },
  cases hd, { dsimp at hd, have := d.prop, rw hd at this, exact set.not_nonempty_empty this },
  rcases hc with ⟨e, heeven, hce⟩, rcases hd with ⟨f, hfeven, hdf⟩,
  rw [← subtype.coe_injective hce, this, subtype.coe_injective hdf, nat.even_succ] at heeven,
  exact heeven hfeven,
end

lemma is_representative.unique (hc : c.is_representative) (hd : d.is_representative) (h : c ≡ d) :
  c = d :=
begin
  obtain hc | ⟨c, hc'⟩ := hc; obtain hd | ⟨d, hd'⟩ := hd,
  { refl },
  { cases set.not_nonempty_empty ((equiv.nonempty_iff_nonempty h).2 d.prop) },
  { cases set.not_nonempty_empty ((equiv.nonempty_iff_nonempty h).1 c.prop) },
  rw equiv_iff at h,
  obtain h | ⟨γ, hγ, δ, hδ, h1, h2⟩ |  ⟨e, he, γ, hγ, hcγ, h2, h3⟩ | ⟨e, he, γ, hγ, hcγ, h2, h3⟩ |
    ⟨e, he, γ, hγ, hcγ, δ, hδ, hdδ, h₁, h₂⟩ := h,
  { exact h.symm },
  { cases c.prop.ne_empty _,
    rw [←subtype.val_eq_coe, h1] },
  { rw [subtype.coe_injective h2, height_A_map_code _ hcγ, nat.even_succ] at hc',
    cases hc' he },
  { rw [subtype.coe_injective h3, height_A_map_code _ hcγ, nat.even_succ] at hd',
    cases hd' he },
  { rw [subtype.coe_injective h₁, height_A_map_code _ hcγ, nat.even_succ] at hc',
    cases hc' he }
end

lemma exists_representative_code (c : code α β hβ) : ∃ d ≡ c, d.is_representative :=
begin
   obtain hemp | hne := c.elts.eq_empty_or_nonempty,
  { obtain ⟨γ, hγ, G⟩ := c,
    refine ⟨⟨⊥, bot_lt_coe β, ∅⟩, ⟨_, is_representative.empty⟩⟩,
    convert equiv.empty_empty _ (bot_lt_coe β) _ hγ },
  obtain heven | hodd := (height ⟨c, hne⟩).even_or_odd,
  { exact ⟨c, equiv.rfl, is_representative.nonempty ⟨c, hne⟩ heven⟩ },
  obtain ⟨d, hd⟩ := height_ne_zero.1 hodd.pos.ne',
  rw A_map_rel_iff at hd,
  obtain ⟨γ, hγ, hdγ, hc⟩ := hd,
  rw [hc, height_A_map_code _ hdγ, nat.odd_succ, nat.not_odd] at hodd,
  have := equiv.A_map_right d hodd γ hγ hdγ,
  rw ←hc at this,
  exact ⟨d, this, is_representative.nonempty d hodd⟩,
end

lemma equiv_even_code_exists (γ : Λ) (hγ : γ < β) (c : code α β hβ) (hc : c.elts.nonempty) (heven : even (height ⟨c, hc⟩)) : ∃ d ≡ c, d.extension = γ :=
begin
  by_cases c.extension = γ,
  exact ⟨c, equiv.refl c, h⟩,
  exact ⟨A_map_code hγ ⟨c, hc⟩, equiv.A_map_left _ heven _ _ h, rfl⟩,
end

lemma equiv_code_exists (γ : Λ) (hγ : γ < β) (c : code α β hβ) : ∃ d ≡ c, d.extension = γ :=
begin
  by_cases c.elts = ∅,
  { cases c with δ hδ D, dsimp at h, rw h,
   refine ⟨⟨γ, coe_lt_coe.2 hγ, ∅⟩, equiv.empty_empty γ (coe_lt_coe.2 hγ) δ hδ, rfl⟩, },
  rw [← not_nonempty_iff_eq_empty, not_not] at h,
  obtain heven | hodd := (height ⟨c, h⟩).even_or_odd,
  exact equiv_even_code_exists _ hγ _ _ heven,
  obtain ⟨d, hd⟩ := height_ne_zero.1 hodd.pos.ne',
  rw A_map_rel_iff at hd,
  obtain ⟨δ, hδ, hdext, hd⟩ := hd,
  rw [hd, height_A_map_code _ hdext, nat.odd_succ, ← nat.even_iff_not_odd] at hodd,
  rcases equiv_even_code_exists γ hγ d.val d.prop _ with ⟨e, hequiv, he⟩,
  rw ((congr_arg subtype.val hd).congr_right.mp rfl : c = (A_map_code hδ d).val),
  exact ⟨e, equiv_transitive hequiv $ equiv.A_map_right d hodd δ hδ hdext, he⟩,
  rwa ← subtype.eta d at hodd,
end

lemma equiv_code_unique (c d : code α β hβ) (hequiv : c ≡ d) (h : c.extension = d.extension) : c = d := sorry

lemma equiv_code_exists_unique (γ : Λ) (hγ : γ < β) (c : code α β hβ) : ∃! d ≡ c, d.extension = γ :=
begin
  obtain ⟨d, hequiv, hd⟩ := equiv_code_exists γ hγ c, use d, split, refine ⟨hequiv, hd, λ x y, rfl⟩,
  rintros e ⟨hequiv', heext, he⟩,
  rw ← hd at heext,
  exact equiv_code_unique e d (equiv_transitive hequiv' hequiv.symm) heext,
end

lemma equiv_bot_code_subsingleton (c : code α β hβ) :
  ∀ d ≡ c, ∀ e ≡ c, d.extension = ⊥ → e.extension = ⊥ → d = e :=
begin
  intros d hd e he hdext heext, rw ← heext at hdext,
  exact equiv_code_unique d e (equiv_transitive hd he.symm) hdext,
end

end code
end con_nf
