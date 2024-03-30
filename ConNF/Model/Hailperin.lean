import ConNF.Model.Basic

/-!
# Hailperin's finite axiomatisation of NF
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

end ConNF
