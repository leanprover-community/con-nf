import ConNF.ModelData.CoherentData

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] {β : TypeIndex}

@[ext]
structure InflexiblePath (β : TypeIndex) where
  γ : Λ
  δ : TypeIndex
  ε : Λ
  hδ : δ < γ
  hε : (ε : TypeIndex) < γ
  hδε : δ ≠ ε
  A : β ↝ γ

instance {β β' : TypeIndex} : Coderivative (InflexiblePath β) (InflexiblePath β') β' β where
  coderiv P B := ⟨P.γ, P.δ, P.ε, P.hδ, P.hε, P.hδε, B ⇘ P.A⟩

@[simp]
theorem InflexiblePath.coderiv_A {β β' : TypeIndex} (P : InflexiblePath β) (B : β' ↝ β) :
    (P ⇗ B).A = B ⇘ P.A :=
  rfl

variable [Level] [CoherentData]

instance [LeLevel β] (P : InflexiblePath β) : LeLevel P.γ :=
  ⟨P.A.le.trans LeLevel.elim⟩

instance [LeLevel β] (P : InflexiblePath β) : LtLevel P.δ :=
  ⟨P.hδ.trans_le LeLevel.elim⟩

instance [LeLevel β] (P : InflexiblePath β) : LtLevel P.ε :=
  ⟨P.hε.trans_le LeLevel.elim⟩

def Inflexible [LeLevel β] (A : β ↝ ⊥) (L : Litter) : Prop :=
  ∃ P : InflexiblePath β, ∃ t, A = P.A ↘ P.hε ↘. ∧ L = fuzz P.hδε t

theorem inflexible_iff [LeLevel β] (A : β ↝ ⊥) (L : Litter) :
    Inflexible A L ↔ ∃ P : InflexiblePath β, ∃ t, A = P.A ↘ P.hε ↘. ∧ L = fuzz P.hδε t :=
  Iff.rfl

theorem not_inflexible_iff [LeLevel β] (A : β ↝ ⊥) (L : Litter) :
    ¬Inflexible A L ↔ ∀ P : InflexiblePath β, ∀ t, A = P.A ↘ P.hε ↘. → L ≠ fuzz P.hδε t := by
  rw [inflexible_iff]
  push_neg
  rfl

theorem inflexible_deriv [LeLevel β] {A : β ↝ ⊥} {L : Litter} (h : Inflexible A L)
    {β' : TypeIndex} [LeLevel β'] (B : β' ↝ β) :
    Inflexible (B ⇘ A) L := by
  obtain ⟨P, t, hA, ht⟩ := h
  refine ⟨P ⇗ B, t, ?_, ht⟩
  rw [hA]
  rfl

theorem inflexible_cases [LeLevel β] (A : β ↝ ⊥) (L : Litter) :
    (∃ P : InflexiblePath β, ∃ t, A = P.A ↘ P.hε ↘. ∧ L = fuzz P.hδε t) ∨ ¬Inflexible A L :=
  Classical.em _

theorem inflexiblePath_subsingleton [LeLevel β] {A : β ↝ ⊥} {L : Litter}
    {P₁ P₂ : InflexiblePath β} {t₁ : Tangle P₁.δ} {t₂ : Tangle P₂.δ}
    (hP₁ : A = P₁.A ↘ P₁.hε ↘.) (hP₂ : A = P₂.A ↘ P₂.hε ↘.)
    (ht₁ : L = fuzz P₁.hδε t₁) (ht₂ : L = fuzz P₂.hδε t₂) :
    P₁ = P₂ := by
  subst hP₁
  subst ht₁
  have := fuzz_β_eq ht₂ -- δ₁ = δ₂
  obtain ⟨γ₁, δ₁, ε₁, _, _, _, A₁⟩ := P₁
  obtain ⟨γ₂, δ₂, ε₂, _, _, _, A₂⟩ := P₂
  cases this
  cases Path.sderivBot_index_injective hP₂ -- ε₁ = ε₂
  cases Path.sderiv_index_injective (Path.sderivBot_path_injective hP₂) -- γ₁ = γ₂
  cases Path.sderiv_path_injective (Path.sderivBot_path_injective hP₂) -- A₁ = A₂
  rfl

def inflexiblePathEmbedding :
    InflexiblePath β ↪ Set.Iic β × Set.Iic β × (γ : TypeIndex) × β ↝ γ where
  toFun P := ⟨⟨P.δ, P.hδ.le.trans P.A.le⟩, ⟨P.ε, P.hε.le.trans P.A.le⟩, P.γ, P.A⟩
  inj' := by
    rintro ⟨⟩ ⟨⟩ h
    cases h
    rfl

omit [Level] [CoherentData] in
theorem card_inflexiblePath_lt (β : TypeIndex) : #(InflexiblePath β) < (#μ).ord.cof := by
  apply (mk_le_of_injective inflexiblePathEmbedding.injective).trans_lt
  simp only [mk_prod, Cardinal.lift_id]
  apply mul_lt_of_lt aleph0_lt_μ_ord_cof.le (TypeIndex.card_Iic_lt β)
  apply mul_lt_of_lt aleph0_lt_μ_ord_cof.le (TypeIndex.card_Iic_lt β)
  exact card_path_any_lt β

end ConNF
