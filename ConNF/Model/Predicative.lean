import ConNF.Model.Basic

/-!
# The predicative part of Hailperin's finite axiomatisation of NF
-/

open Quiver WithBot

open scoped Pointwise

universe u

noncomputable section

namespace ConNF

open TangleData TSet

variable [Params.{u}] {α β γ δ ε ζ : Λ}
  (hβ : β < α) (hγ : γ < β) (hδ : δ < γ) (hε : ε < δ) (hζ : ζ < ε)

theorem Symmetric.inter {s₁ s₂ : Set (TSet β)}
    (h₁ : Symmetric hβ s₁) (h₂ : Symmetric hβ s₂) :
    Symmetric hβ (s₁ ∩ s₂) := by
  obtain ⟨S₁, hS₁, hS₁'⟩ := h₁
  obtain ⟨S₂, hS₂, hS₂'⟩ := h₂
  refine ⟨S₁ ∪ S₂, hS₁.union hS₂, ?_⟩
  intro ρ hρ
  rw [Set.smul_set_inter, hS₁' ρ (fun c hc => hρ c (Or.inl hc)),
    hS₂' ρ (fun c hc => hρ c (Or.inr hc))]

theorem TangleData.TSet.inter_supported (t₁ t₂ : TSet α) :
    Symmetric hβ {s | s ∈[hβ] t₁ ∧ s ∈[hβ] t₂} := by
  obtain ⟨s₁, hs₁, rfl⟩ := t₁.induction hβ
  obtain ⟨s₂, hs₂, rfl⟩ := t₂.induction hβ
  simp only [mem_mk_iff]
  exact Symmetric.inter hβ hs₁ hs₂

def TangleData.TSet.inter (t₁ t₂ : TSet α) : TSet α :=
  mk hβ {s | s ∈[hβ] t₁ ∧ s ∈[hβ] t₂} (inter_supported hβ t₁ t₂)

theorem Symmetric.compl {s : Set (TSet β)} (h : Symmetric hβ s) :
    Symmetric hβ sᶜ := by
  obtain ⟨S, hS, hS'⟩ := h
  refine ⟨S, hS, ?_⟩
  intro ρ hρ
  rw [Set.smul_set_compl, hS' ρ hρ]

theorem TangleData.TSet.compl_supported (t : TSet α) :
    Symmetric hβ {s | ¬s ∈[hβ] t} := by
  obtain ⟨s, hs, rfl⟩ := t.induction hβ
  simp only [mem_mk_iff]
  exact hs.compl

def TangleData.TSet.compl (t : TSet α) : TSet α :=
  mk hβ {s | ¬s ∈[hβ] t} (compl_supported hβ t)

theorem TangleData.TSet.singleton_supported (t : TSet β) :
    Symmetric hβ {t} :=
  Small.symmetric (small_singleton _) hβ

def TangleData.TSet.singleton (t : TSet β) : TSet α :=
  mk hβ {t} (singleton_supported hβ t)

theorem TangleData.TSet.up_supported (t₁ t₂ : TSet β) :
    Symmetric hβ {t₁, t₂} := by
  refine Small.symmetric ?_ hβ
  exact Small.union (small_singleton _) (small_singleton _)

/-- The unordered pair. -/
def TangleData.TSet.up (t₁ t₂ : TSet β) : TSet α :=
  mk hβ {t₁, t₂} (up_supported hβ t₁ t₂)

/-- The Kuratowski ordered pair. -/
def TangleData.TSet.op (t₁ t₂ : TSet γ) : TSet α :=
  up hβ (singleton hγ t₁) (up hγ t₁ t₂)

@[simp]
theorem TangleData.TSet.mem_singleton_iff (t : TSet β) (s : TSet β) :
    s ∈[hβ] singleton hβ t ↔ s = t := by
  simp only [singleton, mem_mk_iff, Set.mem_singleton_iff]

@[simp]
theorem smul_singleton (t : TSet β) (ρ : Allowable α) :
    ρ • TSet.singleton hβ t = TSet.singleton hβ (cons hβ ρ • t) := by
  refine ext hβ _ _ ?_
  intro s
  simp only [mem_smul_iff, mem_singleton_iff, inv_smul_eq_iff]

theorem singleton_injective' (t₁ t₂ : TSet β) (h : TSet.singleton hβ t₁ = TSet.singleton hβ t₂) :
    t₁ = t₂ := by
  have : t₁ ∈[hβ] TSet.singleton hβ t₁
  · rw [mem_singleton_iff]
  rw [h, mem_singleton_iff] at this
  exact this

@[simp]
theorem TangleData.TSet.mem_up_iff (t₁ t₂ : TSet β) (s : TSet β) :
    s ∈[hβ] up hβ t₁ t₂ ↔ s = t₁ ∨ s = t₂ := by
  simp only [up, mem_mk_iff, Set.mem_insert_iff, Set.mem_singleton_iff]

@[simp]
theorem smul_up (t₁ t₂ : TSet β) (ρ : Allowable α) :
    ρ • up hβ t₁ t₂ = up hβ (cons hβ ρ • t₁) (cons hβ ρ • t₂) := by
  refine ext hβ _ _ ?_
  intro s
  simp only [mem_smul_iff, mem_up_iff, inv_smul_eq_iff]

@[simp]
theorem TangleData.TSet.mem_op_iff (t₁ t₂ : TSet γ) (s : TSet β) :
    s ∈[hβ] op hβ hγ t₁ t₂ ↔ s = singleton hγ t₁ ∨ s = up hγ t₁ t₂ :=
  mem_up_iff _ _ _ _

@[simp]
theorem smul_op (t₁ t₂ : TSet γ) (ρ : Allowable α) :
    ρ • op hβ hγ t₁ t₂ =
      op hβ hγ ((ρ |> cons hβ |> cons hγ) • t₁) ((ρ |> cons hβ |> cons hγ) • t₂) := by
  refine ext hβ _ _ ?_
  intro s
  simp only [mem_smul_iff, mem_op_iff, inv_smul_eq_iff, smul_singleton, smul_up]

theorem Symmetric.singletonImage {s : Set (TSet γ)} (h : Symmetric hγ s) :
    Symmetric hβ {p | ∃ a b : TSet ε, op hδ hε a b ∈ s ∧
      p = op hγ hδ (.singleton hε a) (.singleton hε b)} := by
  obtain ⟨S, hS, hS'⟩ := h
  refine Symmetric.ofSubset hβ _ ?_
  refine ⟨raise (coe_lt_coe.mpr hβ) '' S, hS.image, ?_⟩
  intro ρ hρ
  have := hS' (cons hβ ρ) ?_
  swap
  · simp only [Set.mem_image, Allowable.smul_address_eq_iff, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, raise_path, raise_value, cons_toStructPerm, Tree.comp_apply] at hρ ⊢
    exact hρ
  rintro _ ⟨_, ⟨a, b, hab, rfl⟩, rfl⟩
  refine ⟨(ρ |> cons hβ |> cons hγ |> cons hδ |> cons hε) • a,
      (ρ |> cons hβ |> cons hγ |> cons hδ |> cons hε) • b, ?_, ?_⟩
  · rw [← this, Set.mem_smul_set_iff_inv_smul_mem]
    simp only [smul_op, map_inv, inv_smul_smul]
    exact hab
  · simp only [smul_op, smul_singleton]

theorem TangleData.TSet.singletonImage_supported (t : TSet β) :
    Symmetric hβ {p | ∃ a b : TSet ε, op hδ hε a b ∈[hγ] t ∧
      p = op hγ hδ (singleton hε a) (singleton hε b)} := by
  obtain ⟨s, hs, rfl⟩ := t.induction hγ
  simp only [mem_mk_iff]
  exact hs.singletonImage _ _ _

def TangleData.TSet.singletonImage (t : TSet β) : TSet α :=
  mk hβ {p | ∃ a b : TSet ε, op hδ hε a b ∈[hγ] t ∧
    p = op hγ hδ (singleton hε a) (singleton hε b)} (singletonImage_supported hβ hγ hδ hε t)

theorem Symmetric.insertion2 {s : Set (TSet δ)} (h : Symmetric hδ s) :
    Symmetric hβ {p | ∃ a b c : TSet ζ, op hε hζ a c ∈ s ∧
      p = op hγ hδ (.singleton hε (.singleton hζ a)) (op hε hζ b c)} := by
  obtain ⟨S, hS, hS'⟩ := h
  refine Symmetric.ofSubset hβ _ ?_
  refine ⟨raise (coe_lt_coe.mpr hβ) ∘ raise (coe_lt_coe.mpr hγ) '' S, hS.image, ?_⟩
  intro ρ hρ
  have := hS' (ρ |> cons hβ |> cons hγ) ?_
  swap
  · simp only [Set.mem_image, Allowable.smul_address_eq_iff, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, raise_path, raise_value, cons_toStructPerm, Tree.comp_apply] at hρ ⊢
    exact hρ
  rintro _ ⟨_, ⟨a, b, c, habc, rfl⟩, rfl⟩
  refine ⟨(ρ |> cons hβ |> cons hγ |> cons hδ |> cons hε |> cons hζ) • a,
      (ρ |> cons hβ |> cons hγ |> cons hδ |> cons hε |> cons hζ) • b,
      (ρ |> cons hβ |> cons hγ |> cons hδ |> cons hε |> cons hζ) • c, ?_, ?_⟩
  · rw [← this, Set.mem_smul_set_iff_inv_smul_mem]
    simp only [smul_op, map_inv, inv_smul_smul]
    exact habc
  · simp only [smul_op, smul_singleton]

theorem TangleData.TSet.insertion2_supported (t : TSet γ) :
    Symmetric hβ {p | ∃ a b c : TSet ζ, op hε hζ a c ∈[hδ] t ∧
      p = op hγ hδ (.singleton hε (.singleton hζ a)) (op hε hζ b c)} := by
  obtain ⟨s, hs, rfl⟩ := t.induction hδ
  simp only [mem_mk_iff]
  exact hs.insertion2 _ _ _ _

def TangleData.TSet.insertion2 (t : TSet γ) : TSet α :=
  mk hβ {p | ∃ a b c : TSet ζ, op hε hζ a c ∈[hδ] t ∧
    p = op hγ hδ (.singleton hε (.singleton hζ a)) (op hε hζ b c)}
    (insertion2_supported hβ hγ hδ hε hζ t)

theorem Symmetric.insertion3 {s : Set (TSet δ)} (h : Symmetric hδ s) :
    Symmetric hβ {p | ∃ a b c : TSet ζ, op hε hζ a b ∈ s ∧
      p = op hγ hδ (.singleton hε (.singleton hζ a)) (op hε hζ b c)} := by
  obtain ⟨S, hS, hS'⟩ := h
  refine Symmetric.ofSubset hβ _ ?_
  refine ⟨raise (coe_lt_coe.mpr hβ) ∘ raise (coe_lt_coe.mpr hγ) '' S, hS.image, ?_⟩
  intro ρ hρ
  have := hS' (ρ |> cons hβ |> cons hγ) ?_
  swap
  · simp only [Set.mem_image, Allowable.smul_address_eq_iff, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, raise_path, raise_value, cons_toStructPerm, Tree.comp_apply] at hρ ⊢
    exact hρ
  rintro _ ⟨_, ⟨a, b, c, habc, rfl⟩, rfl⟩
  refine ⟨(ρ |> cons hβ |> cons hγ |> cons hδ |> cons hε |> cons hζ) • a,
      (ρ |> cons hβ |> cons hγ |> cons hδ |> cons hε |> cons hζ) • b,
      (ρ |> cons hβ |> cons hγ |> cons hδ |> cons hε |> cons hζ) • c, ?_, ?_⟩
  · rw [← this, Set.mem_smul_set_iff_inv_smul_mem]
    simp only [smul_op, map_inv, inv_smul_smul]
    exact habc
  · simp only [smul_op, smul_singleton]

theorem TangleData.TSet.insertion3_supported (t : TSet γ) :
    Symmetric hβ {p | ∃ a b c : TSet ζ, op hε hζ a b ∈[hδ] t ∧
      p = op hγ hδ (.singleton hε (.singleton hζ a)) (op hε hζ b c)} := by
  obtain ⟨s, hs, rfl⟩ := t.induction hδ
  simp only [mem_mk_iff]
  exact hs.insertion3 _ _ _ _

def TangleData.TSet.insertion3 (t : TSet γ) : TSet α :=
  mk hβ {p | ∃ a b c : TSet ζ, op hε hζ a b ∈[hδ] t ∧
    p = op hγ hδ (.singleton hε (.singleton hζ a)) (op hε hζ b c)}
    (insertion3_supported hβ hγ hδ hε hζ t)

theorem Symmetric.cross {s : Set (TSet δ)} (h : Symmetric hδ s) :
    Symmetric hβ {p | ∃ a b : TSet δ, b ∈ s ∧ p = op hγ hδ a b} := by
  obtain ⟨S, hS, hS'⟩ := h
  refine Symmetric.ofSubset hβ _ ?_
  refine ⟨raise (coe_lt_coe.mpr hβ) ∘ raise (coe_lt_coe.mpr hγ) '' S, hS.image, ?_⟩
  intro ρ hρ
  have := hS' (ρ |> cons hβ |> cons hγ) ?_
  swap
  · simp only [Set.mem_image, Allowable.smul_address_eq_iff, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, raise_path, raise_value, cons_toStructPerm, Tree.comp_apply] at hρ ⊢
    exact hρ
  rintro _ ⟨_, ⟨a, b, hb, rfl⟩, rfl⟩
  refine ⟨(ρ |> cons hβ |> cons hγ |> cons hδ) • a,
      (ρ |> cons hβ |> cons hγ |> cons hδ) • b, ?_, ?_⟩
  · rw [← this, Set.mem_smul_set_iff_inv_smul_mem, inv_smul_smul]
    exact hb
  · simp only [smul_op]

theorem TangleData.TSet.cross_supported (t : TSet γ) :
    Symmetric hβ {p | ∃ a b : TSet δ, b ∈[hδ] t ∧ p = op hγ hδ a b} := by
  obtain ⟨s, hs, rfl⟩ := t.induction hδ
  simp only [mem_mk_iff]
  exact hs.cross _ _ _

def TangleData.TSet.cross (t : TSet γ) : TSet α :=
  mk hβ {p | ∃ a b : TSet δ, b ∈[hδ] t ∧ p = op hγ hδ a b}
    (cross_supported hβ hγ hδ t)

theorem Symmetric.typeLower' {s : Set (TSet β)} (h : Symmetric hβ s) :
    Symmetric hβ {p | ∃ a : TSet ε, (∀ b : TSet δ, op hγ hδ b (.singleton hε a) ∈ s)
      ∧ p = .singleton hγ (.singleton hδ (.singleton hε a))} := by
  obtain ⟨S, hS, hS'⟩ := h
  refine Symmetric.ofSubset hβ _ ?_
  refine ⟨S, hS, ?_⟩
  intro ρ hρ
  have := hS' ρ hρ
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  refine ⟨(ρ |> cons hβ |> cons hγ |> cons hδ |> cons hε) • a, ?_, ?_⟩
  · intro b
    rw [← this, Set.mem_smul_set_iff_inv_smul_mem]
    simp only [smul_op, map_inv, smul_singleton, inv_smul_smul]
    exact ha _
  · simp only [smul_singleton]

theorem TangleData.TSet.typeLower'_supported (t : TSet α) :
    Symmetric hβ {p | ∃ a : TSet ε, (∀ b : TSet δ, op hγ hδ b (.singleton hε a) ∈[hβ] t)
      ∧ p = .singleton hγ (.singleton hδ (.singleton hε a))} := by
  obtain ⟨s, hs, rfl⟩ := t.induction hβ
  simp only [mem_mk_iff]
  exact hs.typeLower' _ _ _

/-- This isn't quite the right form of the type lowering axiom, but once we have the axiom
of union for singletons, we will be able to deduce the correct form of the result. -/
def TangleData.TSet.typeLower' (t : TSet α) : TSet α :=
  mk hβ {p | ∃ a : TSet ε, (∀ b : TSet δ, op hγ hδ b (.singleton hε a) ∈[hβ] t)
      ∧ p = .singleton hγ (.singleton hδ (.singleton hε a))}
    (typeLower'_supported hβ hγ hδ hε t)

theorem Symmetric.converse {s : Set (TSet β)} (h : Symmetric hβ s) :
    Symmetric hβ {p | ∃ a b : TSet δ, op hγ hδ a b ∈ s ∧ p = op hγ hδ b a} := by
  obtain ⟨S, hS, hS'⟩ := h
  refine Symmetric.ofSubset hβ _ ?_
  refine ⟨S, hS, ?_⟩
  intro ρ hρ
  have := hS' ρ hρ
  rintro _ ⟨_, ⟨a, b, hab, rfl⟩, rfl⟩
  refine ⟨(ρ |> cons hβ |> cons hγ |> cons hδ) • a,
      (ρ |> cons hβ |> cons hγ |> cons hδ) • b, ?_, ?_⟩
  · rw [← this, Set.mem_smul_set_iff_inv_smul_mem]
    simp only [smul_op, map_inv, smul_singleton, inv_smul_smul]
    exact hab
  · simp only [smul_op]

theorem TangleData.TSet.converse_supported (t : TSet α) :
    Symmetric hβ {p | ∃ a b : TSet δ, op hγ hδ a b ∈[hβ] t ∧ p = op hγ hδ b a} := by
  obtain ⟨s, hs, rfl⟩ := t.induction hβ
  simp only [mem_mk_iff]
  exact hs.converse _ _ _

def TangleData.TSet.converse (t : TSet α) : TSet α :=
  mk hβ {p | ∃ a b : TSet δ, op hγ hδ a b ∈[hβ] t ∧ p = op hγ hδ b a}
    (converse_supported hβ hγ hδ t)

theorem Symmetric.cardinalOne :
    Symmetric hβ {p | ∃ a : TSet γ, p = .singleton hγ a} := by
  refine Symmetric.ofSubset hβ _ ?_
  refine ⟨∅, small_empty, ?_⟩
  intro ρ _
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  simp only [smul_singleton, Set.mem_setOf_eq]
  exact ⟨_, rfl⟩

def TangleData.TSet.cardinalOne : TSet α :=
  mk hβ {p | ∃ a : TSet γ, p = .singleton hγ a} (Symmetric.cardinalOne hβ hγ)

theorem Symmetric.subset :
    Symmetric hβ {p | ∃ a b : TSet δ, (∀ c : TSet ε, c ∈[hε] a → c ∈[hε] b) ∧
      p = op hγ hδ a b} := by
  refine Symmetric.ofSubset hβ _ ?_
  refine ⟨∅, small_empty, ?_⟩
  intro ρ _
  rintro _ ⟨_, ⟨a, b, ha, rfl⟩, rfl⟩
  simp only [smul_op, Set.mem_setOf_eq]
  refine ⟨_, _, ?_, rfl⟩
  intro c hc
  have := ha ((ρ |> cons hβ |> cons hγ |> cons hδ |> cons hε)⁻¹ • c)
  rw [← mem_smul_iff, ← mem_smul_iff] at this
  exact this hc

def TangleData.TSet.subset : TSet α :=
  mk hβ {p | ∃ a b : TSet δ, (∀ c : TSet ε, c ∈[hε] a → c ∈[hε] b) ∧
      p = op hγ hδ a b} (Symmetric.subset hβ hγ hδ hε)

end ConNF
