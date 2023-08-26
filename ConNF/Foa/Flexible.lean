import ConNF.Foa.Constrains

open Set Sum

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] (α : Λ) [PositionData] [Phase2Assumptions α] {β : TypeIndex}

/-- A litter is *inflexible* if it is the image of some f-map. -/
@[mk_iff]
inductive Inflexible : Litter → ExtendedIndex β → Prop
  | mk_coe ⦃γ : Iic α⦄ ⦃δ : Iio α⦄ ⦃ε : Iio α⦄ (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
    (A : Quiver.Path (β : TypeIndex) γ) (t : Tangle δ) :
    Inflexible (fMap (WithBot.coe_ne_coe.mpr <| coe_ne' hδε) t)
      ((A.cons (coe_lt hε)).cons (WithBot.bot_lt_coe _))
  | mk_bot ⦃γ : Iic α⦄ ⦃ε : Iio α⦄ (hε : (ε : Λ) < γ)
    (A : Quiver.Path (β : TypeIndex) γ) (a : Atom) :
    Inflexible (fMap (show (⊥ : TypeIndex) ≠ (ε : Λ) from WithBot.bot_ne_coe) a)
      ((A.cons (coe_lt hε)).cons (WithBot.bot_lt_coe _))

/-- A litter is *flexible* if it is not the image of any f-map. -/
def Flexible (L : Litter) (A : ExtendedIndex β) : Prop :=
  ¬Inflexible α L A

theorem flexible_cases (L : Litter) (A : ExtendedIndex β) : Inflexible α L A ∨ Flexible α L A :=
  or_not

theorem mk_flexible (A : ExtendedIndex β) : #{L | Flexible α L A} = #μ := by
  refine le_antisymm ((Cardinal.mk_subtype_le _).trans mk_litter.le) ?_
  refine ⟨⟨fun ν => ⟨⟨ν, ⊥, α, WithBot.bot_ne_coe⟩, ?_⟩, ?_⟩⟩
  · intro h
    rw [Inflexible_iff] at h
    obtain ⟨γ, δ, ε, _, hε, hδε, A, t, h, rfl⟩ | ⟨γ, ε, hε, A, t, h, rfl⟩ := h
    all_goals
      apply_fun Litter.γ at h
      rw [fMap_γ _ _] at h
      exact ne_of_lt (Iio.lt ε) h.symm
  · intro ν₁ ν₂ h
    simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq, Litter.mk.injEq, and_self, and_true] at h
    exact h

variable {α}

theorem Inflexible.comp {γ : TypeIndex} {L : Litter} {A : ExtendedIndex γ} (h : Inflexible α L A)
    (B : Quiver.Path β γ) : Inflexible α L (B.comp A) := by
  induction h with
  | mk_coe => exact Inflexible.mk_coe ‹_› ‹_› ‹_› _ _
  | mk_bot => exact Inflexible.mk_bot ‹_› _ _

@[simp]
theorem not_flexible_iff {L : Litter} {A : ExtendedIndex β} : ¬Flexible α L A ↔ Inflexible α L A :=
  Classical.not_not

theorem flexible_of_comp_flexible {γ : TypeIndex} {L : Litter} {A : ExtendedIndex γ}
    {B : Quiver.Path β γ} (h : Flexible α L (B.comp A)) : Flexible α L A := fun h' => h (h'.comp B)

end ConNF
