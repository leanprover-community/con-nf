import ConNF.Mathlib.Support
import ConNF.FOA.Basic.Flexible
import ConNF.Counting.CodingFunction

/-!
# Specifications
-/

open Quiver Set Sum WithBot

open scoped Classical Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions]

section comp

variable {β γ : TypeIndex} {A : Quiver.Path β γ}

open scoped Classical in
noncomputable def SupportCondition.comp (A : Quiver.Path β γ) (c : SupportCondition β)
    (otherwise : SupportCondition γ) : SupportCondition γ :=
  if h : ∃ B : ExtendedIndex γ, c.path = A.comp B then
    ⟨h.choose, c.value⟩
  else
    otherwise

theorem SupportCondition.comp_eq_of_eq_comp {c : SupportCondition β}
    {otherwise : SupportCondition γ} (B : ExtendedIndex γ) (h : c.path = A.comp B) :
    c.comp A otherwise = ⟨B, c.value⟩ := by
  have : ∃ B : ExtendedIndex γ, c.path = A.comp B := ⟨B, h⟩
  have hB : this.choose = B := Path.comp_injective_right A (this.choose_spec.symm.trans h)
  rw [comp, dif_pos this, hB]

theorem SupportCondition.comp_eq_of_not_exists {c : SupportCondition β}
    {otherwise : SupportCondition γ} (h : ¬∃ B : ExtendedIndex γ, c.path = A.comp B) :
    c.comp A otherwise = otherwise :=
  by rw [comp, dif_neg h]

@[simp]
theorem SupportCondition.comp_smul_comp [LeLevel β] [LeLevel γ] (c : SupportCondition β)
    (otherwise : SupportCondition γ) (ρ : Allowable β) :
    Allowable.comp A ρ • (c.comp A otherwise) =
    (ρ • c).comp A (Allowable.comp A ρ • otherwise) := by
  by_cases h : ∃ B : ExtendedIndex γ, c.path = A.comp B
  · obtain ⟨B, h⟩ := h
    rw [comp_eq_of_eq_comp B h, comp_eq_of_eq_comp B (by exact h),
      Allowable.smul_supportCondition, Allowable.smul_supportCondition, h]
    simp only [Allowable.toStructPerm_comp, Tree.comp_apply]
  · rw [comp_eq_of_not_exists h, comp_eq_of_not_exists (by exact h)]

def Support.pathEnumeration (S : Support β) : Enumeration (ExtendedIndex β) :=
  S.enum.image SupportCondition.path

@[simp]
theorem Support.pathEnumeration_f (S : Support β) (i : κ) (hi : i < S.pathEnumeration.max) :
    S.pathEnumeration.f i hi = (S.f i hi).path :=
  rfl

@[simp]
theorem Support.pathEnumeration_smul [LeLevel β] (S : Support β) (ρ : Allowable β) :
    (ρ • S).pathEnumeration = S.pathEnumeration :=
  rfl

def Support.canComp (A : Quiver.Path β γ) (E : Enumeration (ExtendedIndex β)) : Prop :=
  ∃ i : κ, ∃ hi : i < E.max, ∃ C : ExtendedIndex γ, A.comp C = E.f i hi

noncomputable def Support.compIndex (E : Enumeration (ExtendedIndex β)) (h : canComp A E) : κ :=
  E.chooseIndex (fun B => ∃ C, A.comp C = B) h

theorem Support.compIndex_lt (E : Enumeration (ExtendedIndex β)) (h : canComp A E) :
    compIndex E h < E.max :=
  Enumeration.chooseIndex_lt (p := (fun B => ∃ C, A.comp C = B)) h

noncomputable def Support.compIndex_tail (E : Enumeration (ExtendedIndex β)) (h : canComp A E) :
    ExtendedIndex γ :=
  (Enumeration.chooseIndex_spec (p := (fun B => ∃ C, A.comp C = B)) h).choose

theorem Support.compIndex_spec (E : Enumeration (ExtendedIndex β)) (h : canComp A E) :
    A.comp (compIndex_tail E h) = E.f (compIndex E h) (compIndex_lt E h) :=
  (Enumeration.chooseIndex_spec (p := (fun B => ∃ C, A.comp C = B)) h).choose_spec

open scoped Classical in
noncomputable def Support.comp' (A : Quiver.Path β γ) (S : Support β) :
    Enumeration (SupportCondition γ) :=
  if h : canComp A S.pathEnumeration then
    ⟨S.max, fun i hi => (S.f i hi).comp A
      ⟨compIndex_tail S.pathEnumeration h,
        (S.f (compIndex S.pathEnumeration h) (compIndex_lt _ _)).value⟩⟩
  else
    ⟨0, fun _ hi => (κ_not_lt_zero _ hi).elim⟩

variable {S : Support β}

theorem Support.comp'_eq_pos (h : canComp A S.pathEnumeration) :
    S.comp' A = ⟨S.max, fun i hi => (S.f i hi).comp A
      ⟨compIndex_tail S.pathEnumeration h,
        (S.f (compIndex S.pathEnumeration h) (compIndex_lt _ _)).value⟩⟩ :=
  by rw [Support.comp', dif_pos h]

theorem Support.comp'_eq_neg (h : ¬canComp A S.pathEnumeration) :
    S.comp' A = ⟨0, fun _ hi => (κ_not_lt_zero _ hi).elim⟩ :=
  by rw [Support.comp', dif_neg h]

theorem Allowable.comp_smul_support_comp' {β γ : TypeIndex} [LeLevel β] [LeLevel γ]
    (S : Support β) (ρ : Allowable β) (A : Path β γ) :
    Allowable.comp A ρ • S.comp' A = (ρ • S).comp' A := by
  by_cases h : Support.canComp A S.pathEnumeration
  · rw [Support.comp'_eq_pos h, Support.comp'_eq_pos]
    swap
    · exact h
    refine Enumeration.ext _ _ rfl (heq_of_eq ?_)
    ext i hi : 2
    simp only [Enumeration.smul_f, SupportCondition.comp_smul_comp, smul_support_f,
      Support.pathEnumeration_smul]
    refine congr_arg _ ?_
    rw [Allowable.smul_supportCondition, Allowable.smul_supportCondition,
      toStructPerm_comp, Tree.comp_apply, SupportCondition.mk.injEq,
      Support.compIndex_spec S.pathEnumeration h, Support.pathEnumeration_f]
    exact ⟨rfl, rfl⟩
  · push_neg at h
    rw [Support.comp'_eq_neg h, Support.comp'_eq_neg (by rwa [Support.pathEnumeration_smul])]
    refine Enumeration.ext _ _ rfl (heq_of_eq ?_)
    ext i hi : 2
    cases κ_not_lt_zero _ hi

@[simp]
theorem Support.mem_comp'_iff (A : Quiver.Path β γ) (S : Support β) (c : SupportCondition γ) :
    c ∈ S.comp' A ↔ ⟨A.comp c.path, c.value⟩ ∈ S := by
  by_cases h : Support.canComp A S.pathEnumeration
  · simp only [comp'_eq_pos h, Enumeration.mem_iff, mem_iff]
    constructor
    · rintro ⟨i, hi, hc⟩
      by_cases h' : ∃ B : ExtendedIndex γ, (S.f i hi).path = A.comp B
      · obtain ⟨B, hB⟩ := h'
        rw [SupportCondition.comp_eq_of_eq_comp B hB] at hc
        subst hc
        refine ⟨i, hi, ?_⟩
        ext
        · exact hB.symm
        · rfl
      · rw [SupportCondition.comp_eq_of_not_exists h'] at hc
        subst hc
        refine ⟨compIndex _ h, compIndex_lt _ h, ?_⟩
        rw [compIndex_spec]
        rfl
    · rintro ⟨i, hi, hc⟩
      refine ⟨i, hi, ?_⟩
      rw [← hc, SupportCondition.comp_eq_of_eq_comp c.path]
      rfl
  · simp only [comp'_eq_neg h, Enumeration.mem_iff, mem_iff]
    constructor
    · rintro ⟨i, hi, _⟩
      cases κ_not_lt_zero i hi
    · rintro ⟨i, hi, hc⟩
      exfalso
      refine h ?_
      refine ⟨i, hi, c.path, ?_⟩
      rw [pathEnumeration_f, ← hc]

@[simp]
theorem Support.comp'_coe (A : Quiver.Path β γ) (S : Support β) :
    (S.comp' A : Set (SupportCondition γ)) =
    (fun c => ⟨A.comp c.path, c.value⟩) ⁻¹' (S : Set (SupportCondition β)) := by
  ext
  exact Support.mem_comp'_iff A S _

theorem Support.mem_of_mem_symmDiff_comp (A : Quiver.Path β γ) (S : Support β) (B : ExtendedIndex γ)
    (N₁ N₂ : NearLitter) (a : Atom) :
    N₁.1 = N₂.1 → a ∈ (N₁ : Set Atom) ∆ N₂ →
    ⟨B, inr N₁⟩ ∈ S.comp' A → ⟨B, inr N₂⟩ ∈ S.comp' A → ⟨B, inl a⟩ ∈ S.comp' A := by
  simp only [mem_comp'_iff]
  exact S.mem_of_mem_symmDiff (A.comp B) N₁ N₂ a

noncomputable def Support.comp (A : Quiver.Path β γ) (S : Support β) : Support γ :=
  ⟨S.comp' A, mem_of_mem_symmDiff_comp A S⟩

theorem Allowable.comp_smul_support_comp {β γ : TypeIndex} [LeLevel β] [LeLevel γ]
    (S : Support β) (ρ : Allowable β) (A : Path β γ) :
    Allowable.comp A ρ • S.comp A = (ρ • S).comp A := by
  ext : 1
  simp only [Support.comp, Allowable.smul_mk_support, Allowable.comp_smul_support_comp']

end comp

variable {β : Λ}

inductive SpecCondition' (β : Λ) (lower : ∀ (δ : Λ) [LeLevel δ], δ < β → Type u) : Type u
  | atom (A : ExtendedIndex β) (others : Set κ) (nearLitters : Set κ) :
      SpecCondition' β lower
  | flexible (A : ExtendedIndex β) :
      SpecCondition' β lower
  | inflexibleCoe (A : ExtendedIndex β) (h : InflexibleCoePath A)
      (χ : CodingFunction h.δ) (σ : Enumeration (lower h.δ (coe_lt_coe.mp h.δ_lt_β))) :
      SpecCondition' β lower
  | inflexibleBot (A : ExtendedIndex β) (h : InflexibleBotPath A) (atoms : Set κ) :
      SpecCondition' β lower

def SpecCondition : Λ → Type u
  | β => SpecCondition' β (fun δ _ _ => SpecCondition δ)
termination_by SpecCondition β => β

abbrev Spec (β : Λ) : Type u :=
  Enumeration (SpecCondition β)

/-- The "identity" equivalence between `SpecCondition` and `SpecCondition'`. -/
def SpecCondition.equiv : SpecCondition β ≃ SpecCondition' β (fun δ _ _ => SpecCondition δ) :=
  Equiv.cast <| by rw [SpecCondition]

def SpecCondition.atom (A : ExtendedIndex β) (others : Set κ) (nearLitters : Set κ) :
    SpecCondition β :=
  equiv.symm (SpecCondition'.atom A others nearLitters)

def SpecCondition.flexible (A : ExtendedIndex β) :
    SpecCondition β :=
  equiv.symm (SpecCondition'.flexible A)

def SpecCondition.inflexibleCoe (A : ExtendedIndex β) (h : InflexibleCoePath A)
    (χ : CodingFunction h.δ) (σ : Spec h.δ) :
    SpecCondition β :=
  equiv.symm (SpecCondition'.inflexibleCoe A h χ σ)

def SpecCondition.inflexibleBot (A : ExtendedIndex β) (h : InflexibleBotPath A) (atoms : Set κ) :
    SpecCondition β :=
  equiv.symm (SpecCondition'.inflexibleBot A h atoms)

@[simp]
theorem SpecCondition.equiv_atom (A : ExtendedIndex β) (others : Set κ) (nearLitters : Set κ) :
    equiv (atom A others nearLitters) = .atom A others nearLitters := by
  rw [atom, Equiv.apply_symm_apply]

@[simp]
theorem SpecCondition.equiv_flexible (A : ExtendedIndex β) :
    equiv (flexible A) = .flexible A := by
  rw [flexible, Equiv.apply_symm_apply]

@[simp]
theorem SpecCondition.equiv_inflexibleCoe (A : ExtendedIndex β) (h : InflexibleCoePath A)
    (χ : CodingFunction h.δ) (σ : Spec h.δ) :
    equiv (inflexibleCoe A h χ σ) = .inflexibleCoe A h χ σ := by
  rw [inflexibleCoe, Equiv.apply_symm_apply]

@[simp]
theorem SpecCondition.equiv_inflexibleBot (A : ExtendedIndex β) (h : InflexibleBotPath A)
    (atoms : Set κ) :
    equiv (inflexibleBot A h atoms) = .inflexibleBot A h atoms := by
  rw [inflexibleBot, Equiv.apply_symm_apply]

@[simp]
theorem SpecCondition.atom.injEq
    (A₁ A₂ : ExtendedIndex β) (o₁ o₂ : Set κ) (N₁ N₂ : Set κ) :
    SpecCondition.atom A₁ o₁ N₁ = SpecCondition.atom A₂ o₂ N₂ ↔ A₁ = A₂ ∧ o₁ = o₂ ∧ N₁= N₂ := by
  constructor
  · intro h
    have := congr_arg equiv h
    simp only [equiv_atom, SpecCondition'.atom.injEq] at this
    exact this
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

@[simp]
theorem SpecCondition.flexible.injEq (A₁ A₂ : ExtendedIndex β) :
    SpecCondition.flexible A₁ = SpecCondition.flexible A₂ ↔ A₁ = A₂ := by
  constructor
  · intro h
    have := congr_arg equiv h
    simp only [equiv_flexible, SpecCondition'.flexible.injEq] at this
    exact this
  · rintro rfl
    rfl

@[simp]
theorem SpecCondition.inflexibleCoe.injEq (A₁ A₂ : ExtendedIndex β)
    (h₁ : InflexibleCoePath A₁) (h₂ : InflexibleCoePath A₂)
    (χ₁ : CodingFunction h₁.δ) (χ₂ : CodingFunction h₂.δ) (σ₁ : Spec h₁.δ) (σ₂ : Spec h₂.δ) :
    SpecCondition.inflexibleCoe A₁ h₁ χ₁ σ₁ = SpecCondition.inflexibleCoe A₂ h₂ χ₂ σ₂ ↔
    A₁ = A₂ ∧ HEq h₁ h₂ ∧ HEq χ₁ χ₂ ∧ HEq σ₁ σ₂ := by
  constructor
  · intro h
    have := congr_arg equiv h
    simp only [equiv_inflexibleCoe, SpecCondition'.inflexibleCoe.injEq] at this
    exact this
  · rintro ⟨rfl, h⟩
    cases eq_of_heq h.1
    cases eq_of_heq h.2.1
    cases eq_of_heq h.2.2
    rfl

@[simp]
theorem SpecCondition.inflexibleBot.injEq (A₁ A₂ : ExtendedIndex β)
    (h₁ : InflexibleBotPath A₁) (h₂ : InflexibleBotPath A₂) (s₁ s₂ : Set κ) :
    SpecCondition.inflexibleBot A₁ h₁ s₁ = SpecCondition.inflexibleBot A₂ h₂ s₂ ↔
    A₁ = A₂ ∧ HEq h₁ h₂ ∧ s₁ = s₂ := by
  constructor
  · intro h
    have := congr_arg equiv h
    simp only [equiv_inflexibleBot, SpecCondition'.inflexibleBot.injEq] at this
    exact this
  · rintro ⟨rfl, h, rfl⟩
    cases eq_of_heq h
    rfl

@[simp]
theorem SpecCondition.atom_ne_flexible
    (A₁ : ExtendedIndex β) (o₁ : Set κ) (N₁ : Set κ)
    (A₂ : ExtendedIndex β) :
    SpecCondition.atom A₁ o₁ N₁ ≠ SpecCondition.flexible A₂ := by
  intro h
  have := congr_arg equiv h
  rw [equiv_atom, equiv_flexible] at this
  cases this

@[simp]
theorem SpecCondition.atom_ne_inflexibleCoe
    (A₁ : ExtendedIndex β) (o₁ : Set κ) (N₁ : Set κ)
    (A₂ : ExtendedIndex β) (h₂ : InflexibleCoePath A₂) (χ₂ : CodingFunction h₂.δ) (σ₂ : Spec h₂.δ) :
    SpecCondition.atom A₁ o₁ N₁ ≠ SpecCondition.inflexibleCoe A₂ h₂ χ₂ σ₂ := by
  intro h
  have := congr_arg equiv h
  rw [equiv_atom, equiv_inflexibleCoe] at this
  cases this

@[simp]
theorem SpecCondition.atom_ne_inflexibleBot
    (A₁ : ExtendedIndex β) (o₁ : Set κ) (N₁ : Set κ)
    (A₂ : ExtendedIndex β) (h₂ : InflexibleBotPath A₂) (s₂ : Set κ) :
    SpecCondition.atom A₁ o₁ N₁ ≠ SpecCondition.inflexibleBot A₂ h₂ s₂ := by
  intro h
  have := congr_arg equiv h
  rw [equiv_atom, equiv_inflexibleBot] at this
  cases this

@[simp]
theorem SpecCondition.flexible_ne_atom
    (A₁ : ExtendedIndex β)
    (A₂ : ExtendedIndex β) (o₂ : Set κ) (N₂ : Set κ) :
    SpecCondition.flexible A₁ ≠ SpecCondition.atom A₂ o₂ N₂ :=
  (atom_ne_flexible A₂ o₂ N₂ A₁).symm

@[simp]
theorem SpecCondition.flexible_ne_inflexibleCoe
    (A₁ : ExtendedIndex β)
    (A₂ : ExtendedIndex β) (h₂ : InflexibleCoePath A₂) (χ₂ : CodingFunction h₂.δ) (σ₂ : Spec h₂.δ) :
    SpecCondition.flexible A₁ ≠ SpecCondition.inflexibleCoe A₂ h₂ χ₂ σ₂ := by
  intro h
  have := congr_arg equiv h
  rw [equiv_flexible, equiv_inflexibleCoe] at this
  cases this

@[simp]
theorem SpecCondition.flexible_ne_inflexibleBot
    (A₁ : ExtendedIndex β)
    (A₂ : ExtendedIndex β) (h₂ : InflexibleBotPath A₂) (s₂ : Set κ) :
    SpecCondition.flexible A₁ ≠ SpecCondition.inflexibleBot A₂ h₂ s₂ := by
  intro h
  have := congr_arg equiv h
  rw [equiv_flexible, equiv_inflexibleBot] at this
  cases this

@[simp]
theorem SpecCondition.inflexibleCoe_ne_atom
    (A₁ : ExtendedIndex β) (h₁ : InflexibleCoePath A₁) (χ₁ : CodingFunction h₁.δ) (σ₁ : Spec h₁.δ)
    (A₂ : ExtendedIndex β) (o₂ : Set κ) (N₂ : Set κ) :
    SpecCondition.inflexibleCoe A₁ h₁ χ₁ σ₁ ≠ SpecCondition.atom A₂ o₂ N₂ :=
  (atom_ne_inflexibleCoe A₂ o₂ N₂ A₁ h₁ χ₁ σ₁).symm

@[simp]
theorem SpecCondition.inflexibleCoe_ne_flexible
    (A₁ : ExtendedIndex β) (h₁ : InflexibleCoePath A₁) (χ₁ : CodingFunction h₁.δ) (σ₁ : Spec h₁.δ)
    (A₂ : ExtendedIndex β) :
    SpecCondition.inflexibleCoe A₁ h₁ χ₁ σ₁ ≠ SpecCondition.flexible A₂ :=
  (flexible_ne_inflexibleCoe A₂ A₁ h₁ χ₁ σ₁).symm

@[simp]
theorem SpecCondition.inflexibleCoe_ne_inflexibleBot
    (A₁ : ExtendedIndex β) (h₁ : InflexibleCoePath A₁) (χ₁ : CodingFunction h₁.δ) (σ₁ : Spec h₁.δ)
    (A₂ : ExtendedIndex β) (h₂ : InflexibleBotPath A₂) (s₂ : Set κ) :
    SpecCondition.inflexibleCoe A₁ h₁ χ₁ σ₁ ≠ SpecCondition.inflexibleBot A₂ h₂ s₂ := by
  intro h
  have := congr_arg equiv h
  rw [equiv_inflexibleCoe, equiv_inflexibleBot] at this
  cases this

@[simp]
theorem SpecCondition.inflexibleBot_ne_atom
    (A₁ : ExtendedIndex β) (h₁ : InflexibleBotPath A₁) (s₁ : Set κ)
    (A₂ : ExtendedIndex β) (o₂ : Set κ) (N₂ : Set κ) :
    SpecCondition.inflexibleBot A₁ h₁ s₁ ≠ SpecCondition.atom A₂ o₂ N₂ :=
  (atom_ne_inflexibleBot A₂ o₂ N₂ A₁ h₁ s₁).symm

@[simp]
theorem SpecCondition.inflexibleBot_ne_flexible
    (A₁ : ExtendedIndex β) (h₁ : InflexibleBotPath A₁) (s₁ : Set κ)
    (A₂ : ExtendedIndex β) :
    SpecCondition.inflexibleBot A₁ h₁ s₁ ≠ SpecCondition.flexible A₂ :=
  (flexible_ne_inflexibleBot A₂ A₁ h₁ s₁).symm

@[simp]
theorem SpecCondition.inflexibleBot_ne_inflexibleCoe
    (A₁ : ExtendedIndex β) (h₁ : InflexibleBotPath A₁) (s₁ : Set κ)
    (A₂ : ExtendedIndex β) (h₂ : InflexibleCoePath A₂) (χ₂ : CodingFunction h₂.δ) (σ₂ : Spec h₂.δ) :
    SpecCondition.inflexibleBot A₁ h₁ s₁ ≠ SpecCondition.inflexibleCoe A₂ h₂ χ₂ σ₂ :=
  (inflexibleCoe_ne_inflexibleBot A₂ h₂ χ₂ σ₂ A₁ h₁ s₁).symm

section recursor

variable {motive : SpecCondition β → Sort _}
  (atom : ∀ (A : ExtendedIndex β) (others : Set κ) (nearLitters : Set κ),
    motive (.atom A others nearLitters))
  (flexible : ∀ (A : ExtendedIndex β), motive (.flexible A))
  (inflexibleCoe : ∀ (A : ExtendedIndex β) (h : InflexibleCoePath A)
    (χ : CodingFunction h.δ) (σ : Spec h.δ), motive (.inflexibleCoe A h χ σ))
  (inflexibleBot : ∀ (A : ExtendedIndex β) (h : InflexibleBotPath A)
    (atoms : Set κ), motive (.inflexibleBot A h atoms))

def SpecCondition.castMotive {c : SpecCondition β} :
    motive c ≃ motive (equiv.symm (equiv c)) :=
  Equiv.cast (by rw [Equiv.symm_apply_apply])

def SpecCondition.rec (c : SpecCondition β) : motive c :=
  castMotive.symm (match SpecCondition.equiv c with
    | .atom A others nearLitters => atom A others nearLitters
    | .flexible A => flexible A
    | .inflexibleCoe A h χ σ => inflexibleCoe A h χ σ
    | .inflexibleBot A h atoms => inflexibleBot A h atoms)

variable {atom flexible inflexibleCoe inflexibleBot}

theorem SpecCondition.castMotive_symm_apply_eq
    (C : (c : SpecCondition' β (fun δ _ _ => SpecCondition δ)) → motive (equiv.symm c))
    (c : SpecCondition' β (fun δ _ _ => SpecCondition δ)) :
    castMotive.symm (C (equiv (equiv.symm c))) = C c := by
  rw [castMotive, Equiv.cast_symm, Equiv.cast_eq_iff_heq]
  exact congr_arg_heq C (Equiv.apply_symm_apply equiv c)

/-- This is a theorem, but we use `def` to avoid writing out its type. -/
def SpecCondition.castMotive_symm_apply_eq' :=
  SpecCondition.castMotive_symm_apply_eq
    (fun c => match c with
      | .atom A others nearLitters => atom A others nearLitters
      | .flexible A => flexible A
      | .inflexibleCoe A h χ σ => inflexibleCoe A h χ σ
      | .inflexibleBot A h atoms => inflexibleBot A h atoms)

def SpecCondition.equiv_cast
    {C : (c : SpecCondition' β (fun δ _ _ => SpecCondition δ)) → Sort _}
    (c : SpecCondition' β (fun δ _ _ => SpecCondition δ)) :
    C (equiv (equiv.symm c)) ≃ C c :=
  Equiv.cast (by rw [Equiv.apply_symm_apply])

@[simp]
theorem SpecCondition.rec_atom (A : ExtendedIndex β) (others : Set κ) (nearLitters : Set κ) :
    SpecCondition.rec atom flexible inflexibleCoe inflexibleBot
      (SpecCondition.atom A others nearLitters) =
    atom A others nearLitters :=
  by simp only [SpecCondition.rec, SpecCondition.atom, SpecCondition.castMotive_symm_apply_eq']

@[simp]
theorem SpecCondition.rec_flexible (A : ExtendedIndex β) :
    SpecCondition.rec atom flexible inflexibleCoe inflexibleBot (SpecCondition.flexible A) =
    flexible A :=
  by simp only [SpecCondition.rec, SpecCondition.flexible, SpecCondition.castMotive_symm_apply_eq']

@[simp]
theorem SpecCondition.rec_inflexibleCoe (A : ExtendedIndex β) (h : InflexibleCoePath A)
    (χ : CodingFunction h.δ) (σ : Spec h.δ) :
    SpecCondition.rec atom flexible inflexibleCoe inflexibleBot
      (SpecCondition.inflexibleCoe A h χ σ) =
    inflexibleCoe A h χ σ :=
  by simp only [SpecCondition.rec, SpecCondition.inflexibleCoe,
    SpecCondition.castMotive_symm_apply_eq']

@[simp]
theorem SpecCondition.rec_inflexibleBot (A : ExtendedIndex β) (h : InflexibleBotPath A)
    (atoms : Set κ) :
    SpecCondition.rec atom flexible inflexibleCoe inflexibleBot
      (SpecCondition.inflexibleBot A h atoms) =
    inflexibleBot A h atoms :=
  by simp only [SpecCondition.rec, SpecCondition.inflexibleBot,
    SpecCondition.castMotive_symm_apply_eq']

end recursor

namespace Spec

inductive SpecifiesCondition' (S : Support β)
    (lower : ∀ (δ : Λ) [LeLevel δ], δ < β → Spec δ → Support δ → Prop) :
    SpecCondition β → SupportCondition β → Prop
  | atom (A : ExtendedIndex β) (a : Atom) :
    SpecifiesCondition' S lower
      (SpecCondition.atom A
        {i | ∃ hi : i < S.max, S.f i hi = ⟨A, inl a⟩}
        {i | ∃ N : NearLitter, a ∈ N ∧ ∃ hi : i < S.max, S.f i hi = ⟨A, inr N⟩})
      ⟨A, inl a⟩
  | flexible (A : ExtendedIndex β) (N : NearLitter) (h : Flexible A N.1) :
    SpecifiesCondition' S lower (SpecCondition.flexible A) ⟨A, inr N⟩
  | inflexibleCoe (A : ExtendedIndex β) (N : NearLitter) (h : InflexibleCoe A N.1)
    (S' : Support h.path.δ) (hS' : S'.IsSum (S.comp (h.path.B.cons h.path.hδ)) h.t.support)
    (σ : Spec h.path.δ) (hσ : lower h.path.δ (coe_lt_coe.mp (h.δ_lt_β)) σ S') :
    SpecifiesCondition' S lower
      (SpecCondition.inflexibleCoe A h.path
        (CodingFunction.code h.t.support h.t (support_supports _)) σ)
      ⟨A, inr N⟩
  | inflexibleBot (A : ExtendedIndex β) (N : NearLitter) (h : InflexibleBot A N.1) :
    SpecifiesCondition' S lower
      (SpecCondition.inflexibleBot A h.path
        {i | ∃ hi : i < S.max, S.f i hi = ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩})
      ⟨A, inr N⟩

@[mk_iff]
structure Specifies' (σ : Spec β) (S : Support β)
    (lower : ∀ (δ : Λ) [LeLevel δ], δ < β → Spec δ → Support δ → Prop) : Prop where
  max_eq_max : σ.max = S.max
  specifies (i : κ) (hσ : i < σ.max) (hS : i < S.max) :
    SpecifiesCondition' S lower (σ.f i hσ) (S.f i hS)

def Specifies {β : Λ} (σ : Spec β) (S : Support β) : Prop :=
  Specifies' σ S (fun δ _ _ σ S => Specifies σ S)
termination_by
  Specifies β _ _ => β

def SpecifiesCondition (S : Support β) : SpecCondition β → SupportCondition β → Prop :=
  SpecifiesCondition' S (fun _ _ _ => Specifies)

theorem specifies_iff (σ : Spec β) (S : Support β) :
    σ.Specifies S ↔
    σ.max = S.max ∧ ∀ (i : κ) (hσ : i < σ.max) (hS : i < S.max),
      SpecifiesCondition S (σ.f i hσ) (S.f i hS) := by
  rw [Specifies, Specifies'_iff]
  rfl

theorem Specifies.max_eq_max {σ : Spec β} {S : Support β} (h : σ.Specifies S) :
    σ.max = S.max := by
  rw [specifies_iff] at h
  exact h.1

theorem Specifies.lt_max {σ : Spec β} {S : Support β} (h : σ.Specifies S)
    {i : κ} (hi : i < σ.max) : i < S.max :=
  by rwa [← h.max_eq_max]

theorem Specifies.of_lt_max {σ : Spec β} {S : Support β} (h : σ.Specifies S)
    {i : κ} (hi : i < S.max) : i < σ.max :=
  by rwa [h.max_eq_max]

theorem Specifies.specifies {σ : Spec β} {S : Support β} (h : σ.Specifies S)
    (i : κ) (hσ : i < σ.max) (hS : i < S.max) : SpecifiesCondition S (σ.f i hσ) (S.f i hS) := by
  rw [specifies_iff] at h
  exact h.2 i hσ hS

theorem specifiesCondition_atom_right_iff (S : Support β)
    (A : ExtendedIndex β) (a : Atom) (σc : SpecCondition β) :
    SpecifiesCondition S σc ⟨A, inl a⟩ ↔
    σc = (SpecCondition.atom A
      {i | ∃ hi : i < S.max, S.f i hi = ⟨A, inl a⟩}
      {i | ∃ N : NearLitter, a ∈ N ∧ ∃ hi : i < S.max, S.f i hi = ⟨A, inr N⟩}) := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact SpecifiesCondition'.atom A a

theorem specifiesCondition_flexible_right_iff (S : Support β)
    (A : ExtendedIndex β) (N : NearLitter) (h : Flexible A N.1) (σc : SpecCondition β) :
    SpecifiesCondition S σc ⟨A, inr N⟩ ↔
    σc = SpecCondition.flexible A := by
  constructor
  · intro h
    cases h with
    | flexible => rfl
    | inflexibleCoe _ _ h' =>
        rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at h
        exact h.2.elim' h'
    | inflexibleBot _ _ h' =>
        rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at h
        exact h.1.elim' h'
  · rintro rfl
    exact SpecifiesCondition'.flexible A N h

theorem specifiesCondition_inflexibleCoe_right_iff (S : Support β)
    (A : ExtendedIndex β) (N : NearLitter) (h : InflexibleCoe A N.1) (σc : SpecCondition β) :
    SpecifiesCondition S σc ⟨A, inr N⟩ ↔
    ∃ (S' : Support h.path.δ) (_ : S'.IsSum (S.comp (h.path.B.cons h.path.hδ)) h.t.support)
      (σ : Spec h.path.δ) (_ : σ.Specifies S'),
      σc = (SpecCondition.inflexibleCoe A h.path
        (CodingFunction.code h.t.support h.t (support_supports _)) σ) := by
  constructor
  · intro h
    cases h with
    | flexible _ _ h' =>
        rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at h'
        exact h'.2.elim' h
    | inflexibleCoe _ _ h' S' hS' σ hσ =>
        cases Subsingleton.elim h h'
        exact ⟨S', hS', σ, hσ, rfl⟩
    | inflexibleBot _ _ h' => cases inflexibleBot_inflexibleCoe h' h
  · rintro ⟨S', hS', σ, hσ, rfl⟩
    exact SpecifiesCondition'.inflexibleCoe A N h S' hS' σ hσ

theorem specifiesCondition_inflexibleBot_right_iff (S : Support β)
    (A : ExtendedIndex β) (N : NearLitter) (h : InflexibleBot A N.1) (σc : SpecCondition β) :
    SpecifiesCondition S σc ⟨A, inr N⟩ ↔
    σc = (SpecCondition.inflexibleBot A h.path
      {i | ∃ hi : i < S.max, S.f i hi = ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩}) := by
  constructor
  · intro h
    cases h with
    | flexible _ _ h' =>
        rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at h'
        exact h'.1.elim' h
    | inflexibleCoe _ _ h' => cases inflexibleBot_inflexibleCoe h h'
    | inflexibleBot _ _ h' =>
        cases Subsingleton.elim h h'
        rfl
  · rintro rfl
    exact SpecifiesCondition'.inflexibleBot A N h

theorem specifiesCondition_atom_left_iff (S : Support β) (c : SupportCondition β)
    (A : ExtendedIndex β) (others : Set κ) (nearLitters : Set κ) :
    SpecifiesCondition S (SpecCondition.atom A others nearLitters) c ↔
    ∃ a : Atom,
      c = ⟨A, inl a⟩ ∧
      others = {i | ∃ hi : i < S.max, S.f i hi = ⟨A, inl a⟩} ∧
      nearLitters = {i | ∃ N : NearLitter, a ∈ N ∧ ∃ hi : i < S.max, S.f i hi = ⟨A, inr N⟩} := by
  obtain ⟨B, a | N⟩ := c
  · rw [specifiesCondition_atom_right_iff]
    aesop
  · obtain (h | ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩) := flexible_cases' B N.1
    · rw [specifiesCondition_flexible_right_iff _ _ _ h]
      aesop
    · rw [specifiesCondition_inflexibleBot_right_iff _ _ _ h]
      aesop
    · rw [specifiesCondition_inflexibleCoe_right_iff _ _ _ h]
      aesop

theorem specifiesCondition_flexible_left_iff (S : Support β) (c : SupportCondition β)
    (A : ExtendedIndex β) :
    SpecifiesCondition S (SpecCondition.flexible A) c ↔
    ∃ N : NearLitter,
      c = ⟨A, inr N⟩ ∧ Flexible A N.1 := by
  obtain ⟨B, a | N⟩ := c
  · rw [specifiesCondition_atom_right_iff]
    aesop
  · obtain (h | ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩) := flexible_cases' B N.1
    · rw [specifiesCondition_flexible_right_iff _ _ _ h]
      aesop
    · rw [specifiesCondition_inflexibleBot_right_iff _ _ _ h]
      aesop
    · rw [specifiesCondition_inflexibleCoe_right_iff _ _ _ h]
      aesop

theorem specifiesCondition_inflexibleCoe_left_iff (S : Support β) (c : SupportCondition β)
    (A : ExtendedIndex β) (h : InflexibleCoePath A) (χ : CodingFunction h.δ) (σ : Spec h.δ) :
    SpecifiesCondition S (SpecCondition.inflexibleCoe A h χ σ) c ↔
    ∃ (N : NearLitter) (t : Tangle h.δ) (S' : Support h.δ),
      c = ⟨A, inr N⟩ ∧
      N.1 = fuzz h.hδε t ∧
      S'.IsSum (S.comp (h.B.cons h.hδ)) t.support ∧
      σ.Specifies S' ∧
      χ = CodingFunction.code (TangleData.Tangle.support t) t (support_supports t) := by
  obtain ⟨B, a | N⟩ := c
  · rw [specifiesCondition_atom_right_iff]
    simp only [SpecCondition.inflexibleCoe_ne_atom, SupportCondition.mk.injEq, and_false, false_and,
      exists_false, exists_const]
  · obtain (h' | ⟨⟨h'⟩⟩ | ⟨⟨h'⟩⟩) := flexible_cases' B N.1
    · rw [specifiesCondition_flexible_right_iff _ _ _ h']
      simp only [SpecCondition.inflexibleCoe_ne_flexible, SupportCondition.mk.injEq, inr.injEq,
        exists_and_left, exists_prop, false_iff, not_exists, not_and, and_imp,
        forall_apply_eq_imp_iff]
      rintro rfl t hN
      cases h' (inflexible_of_inflexibleCoe ⟨h, _, hN⟩)
    · rw [specifiesCondition_inflexibleBot_right_iff _ _ _ h']
      simp only [SpecCondition.inflexibleCoe_ne_inflexibleBot, SupportCondition.mk.injEq, inr.injEq,
        exists_and_left, exists_prop, false_iff, not_exists, not_and, and_imp,
        forall_apply_eq_imp_iff]
      rintro rfl t hN
      cases inflexibleBot_inflexibleCoe h' ⟨h, _, hN⟩
    · rw [specifiesCondition_inflexibleCoe_right_iff _ _ _ h']
      constructor
      · rintro ⟨S', hS', σ, hσ, h⟩
        rw [SpecCondition.inflexibleCoe.injEq] at h
        cases h.1
        cases eq_of_heq h.2.1
        cases eq_of_heq h.2.2.1
        cases eq_of_heq h.2.2.2
        exact ⟨N, h'.t, S', rfl, h'.hL, hS', hσ, rfl⟩
      · rintro ⟨N, t, S', hc, hN, hS', hσ, rfl⟩
        rw [SupportCondition.mk.injEq, inr.injEq] at hc
        cases hc.1
        cases hc.2
        cases Subsingleton.elim h' ⟨h, _, hN⟩
        exact ⟨S', hS', σ, hσ, rfl⟩

theorem specifiesCondition_inflexibleBot_left_iff (S : Support β) (c : SupportCondition β)
    (A : ExtendedIndex β) (h : InflexibleBotPath A) (atoms : Set κ) :
    SpecifiesCondition S (SpecCondition.inflexibleBot A h atoms) c ↔
    ∃ (N : NearLitter) (a : Atom),
      c = ⟨A, inr N⟩ ∧
      N.1 = fuzz (bot_ne_coe (a := h.ε)) a ∧
      atoms = {i | ∃ hi : i < S.max, S.f i hi = ⟨h.B.cons (bot_lt_coe _), inl a⟩} := by
  obtain ⟨B, a | N⟩ := c
  · rw [specifiesCondition_atom_right_iff]
    simp only [SpecCondition.inflexibleBot_ne_atom, SupportCondition.mk.injEq, and_false, false_and,
      exists_const]
  · obtain (h' | ⟨⟨h'⟩⟩ | ⟨⟨h'⟩⟩) := flexible_cases' B N.1
    · rw [specifiesCondition_flexible_right_iff _ _ _ h']
      simp only [SpecCondition.inflexibleBot_ne_flexible, SupportCondition.mk.injEq, inr.injEq,
        exists_and_left, false_iff, not_exists, not_and, and_imp, forall_apply_eq_imp_iff]
      rintro rfl a hN
      cases h' (inflexible_of_inflexibleBot ⟨h, _, hN⟩)
    · rw [specifiesCondition_inflexibleBot_right_iff _ _ _ h', SpecCondition.inflexibleBot.injEq]
      constructor
      · rintro ⟨rfl, h, rfl⟩
        cases eq_of_heq h
        exact ⟨N, h'.a, rfl, h'.hL, rfl⟩
      · rintro ⟨N, a, h, hN, rfl⟩
        cases h
        cases Subsingleton.elim h' ⟨h, _, hN⟩
        exact ⟨rfl, HEq.rfl, rfl⟩
    · rw [specifiesCondition_inflexibleCoe_right_iff _ _ _ h']
      simp only [SpecCondition.inflexibleBot_ne_inflexibleCoe, exists_false,
        SupportCondition.mk.injEq, inr.injEq, exists_and_left, false_iff, not_exists, not_and,
        and_imp, forall_apply_eq_imp_iff]
      rintro rfl a hN
      cases inflexibleBot_inflexibleCoe ⟨h, _, hN⟩ h'

end Spec

theorem exists_spec' (S : Support β)
    (h : ∀ (c : SupportCondition β), ∃ σc, Spec.SpecifiesCondition S σc c) :
    ∃ σ : Spec β, σ.Specifies S := by
  choose f hf using h
  refine ⟨⟨S.max, fun i hi => f (S.f i hi)⟩, ?_⟩
  rw [Spec.specifies_iff]
  exact ⟨rfl, fun i _ _ => hf _⟩

theorem exists_specifiesCondition (S : Support β) (c : SupportCondition β) :
    ∃ σc : SpecCondition β, Spec.SpecifiesCondition S σc c := by
  have : WellFoundedLT Λ := inferInstance
  revert S c
  refine this.induction
    (C := fun β => ∀ S : Support β, ∀ c : SupportCondition β,
      ∃ σc, Spec.SpecifiesCondition S σc c) β ?_
  intro β ih S c
  obtain ⟨B, a | N⟩ := c
  · simp_rw [Spec.specifiesCondition_atom_right_iff]
    exact ⟨_, rfl⟩
  · obtain (h | ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩) := flexible_cases' B N.1
    · simp_rw [Spec.specifiesCondition_flexible_right_iff _ _ _ h]
      exact ⟨_, rfl⟩
    · simp_rw [Spec.specifiesCondition_inflexibleBot_right_iff _ _ _ h]
      exact ⟨_, rfl⟩
    · simp_rw [Spec.specifiesCondition_inflexibleCoe_right_iff _ _ _ h]
      obtain ⟨S', hS'⟩ := Support.exists_isSum (S.comp (h.path.B.cons h.path.hδ)) h.t.support
      obtain ⟨σ, hσ⟩ := exists_spec' S' (ih h.path.δ (coe_lt_coe.mp h.δ_lt_β) S')
      exact ⟨_, S', hS', σ, hσ, rfl⟩

theorem exists_spec (S : Support β) : ∃ σ : Spec β, σ.Specifies S :=
  exists_spec' S (exists_specifiesCondition S)

end ConNF
