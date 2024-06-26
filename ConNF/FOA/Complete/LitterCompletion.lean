import ConNF.FOA.Basic.Constrains
import ConNF.FOA.Complete.HypAction
import ConNF.FOA.LAction.ToApprox
import ConNF.FOA.Complete.FlexibleCompletion

open Quiver Set Sum WithBot

open scoped Classical

universe u

namespace ConNF

namespace StructApprox

variable [Params.{u}] [Level] [BasePositions] [FOAAssumptions]

/-- The inductive hypothesis used for proving freedom of action:
Every free approximation exactly approximates some allowable permutation. -/
def FOAIh (β : Λ) [LeLevel β] : Prop :=
  ∀ π₀ : StructApprox β, π₀.Free →
  ∃ π : Allowable β, π₀.ExactlyApproximates (Allowable.toStructPerm π)

class FreedomOfActionHypothesis (β : Λ) [LeLevel β] : Prop where
  freedomOfAction_of_lt : ∀ γ < β, [LeLevel γ] → FOAIh γ

export FreedomOfActionHypothesis (freedomOfAction_of_lt)

/-- The structural action associated to a given inductive hypothesis. -/
def ihAction {β : Λ} {c : Address β} (H : HypAction c) : StructLAction β := fun B =>
  { atomMap := fun a => ⟨_, fun h => H.atomImage B a h⟩
    litterMap := fun L => ⟨_, fun h => H.nearLitterImage B L.toNearLitter h⟩
    atomMap_dom_small := by
      simp only [PFun.dom_mk]
      have := transClosure_small (small_singleton c)
      simp only [transClosure, mem_singleton_iff, exists_prop, exists_eq_left] at this
      refine' Small.image_subset (fun a => ⟨B, inl a⟩) _ this _
      · intro a b h
        simpa [Address.mk.injEq, inl.injEq, true_and] using h
      · rintro _ ⟨a, h, rfl⟩
        exact h
    litterMap_dom_small := by
      simp only [PFun.dom_mk]
      have := transClosure_small (small_singleton c)
      simp only [transClosure, mem_singleton_iff, exists_prop, exists_eq_left] at this
      refine' Small.image_subset (fun L => ⟨B, inr L.toNearLitter⟩) _ this _
      · intro L₁ L₂ h
        simpa only [Address.mk.injEq, inr.injEq, Litter.toNearLitter_injective.eq_iff,
          true_and] using h
      · rintro _ ⟨a, h, rfl⟩
        exact h }

@[simp]
theorem ihAction_atomMap {β : Λ} {c : Address β} {H : HypAction c}
    {B : ExtendedIndex β} {a : Atom} : (ihAction H B).atomMap a = ⟨_, fun h => H.atomImage B a h⟩ :=
  rfl

@[simp]
theorem ihAction_litterMap {β : Λ} {c : Address β} {H : HypAction c}
    {B : ExtendedIndex β} {L : Litter} :
    (ihAction H B).litterMap L = ⟨_, fun h => H.nearLitterImage B L.toNearLitter h⟩ :=
  rfl

variable {β : Λ} [LeLevel β] [FreedomOfActionHypothesis β]

noncomputable def _root_.ConNF.StructLAction.allowable {γ : Λ} [LtLevel γ]
    (φ : StructLAction γ) (h : γ < β) (h₁ : φ.Lawful) (h₂ : φ.MapFlexible) : Allowable γ :=
  (freedomOfAction_of_lt _ h _ (StructLAction.toApprox_free _ h₁ h₂)).choose

theorem _root_.ConNF.StructLAction.allowable_exactlyApproximates {γ : Λ} [LtLevel γ]
    (φ : StructLAction γ) (h : γ < β) (h₁ : φ.Lawful) (h₂ : φ.MapFlexible) :
    (φ.toApprox h₁).ExactlyApproximates (Allowable.toStructPerm (φ.allowable h h₁ h₂)) :=
  (freedomOfAction_of_lt _ h _ (StructLAction.toApprox_free _ h₁ h₂)).choose_spec

noncomputable def _root_.ConNF.StructLAction.hypothesisedAllowable (φ : StructLAction β)
    {A : ExtendedIndex β} (h : InflexibleCoePath A)
    (h₁ : StructLAction.Lawful (φ.comp (h.B.cons h.hδ)))
    (h₂ : StructLAction.MapFlexible (φ.comp (h.B.cons h.hδ))) :
    Allowable h.δ :=
  StructLAction.allowable
    (φ.comp (h.B.cons h.hδ))
    (coe_lt_coe.mp (h.hδ.trans_le (le_of_path h.B)))
    h₁ h₂

theorem _root_.ConNF.StructLAction.hypothesisedAllowable_exactlyApproximates (φ : StructLAction β)
    {A : ExtendedIndex β} (h : InflexibleCoePath A)
    (h₁ : StructLAction.Lawful (φ.comp (h.B.cons h.hδ)))
    (h₂ : StructLAction.MapFlexible (φ.comp (h.B.cons h.hδ))) :
    StructApprox.ExactlyApproximates
      (StructLAction.toApprox (φ.comp (h.B.cons h.hδ)) h₁)
      (Allowable.toStructPerm (φ.hypothesisedAllowable h h₁ h₂)) :=
  StructLAction.allowable_exactlyApproximates (φ.comp (h.B.cons h.hδ)) _ _ _

noncomputable def litterCompletion (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : HypAction ⟨A, inr L.toNearLitter⟩) : Litter :=
  if h : Nonempty (InflexibleCoe A L) then
    if hs : _ ∧ _ then
      fuzz h.some.path.hδε ((ihAction H).hypothesisedAllowable h.some.path hs.1 hs.2 • h.some.t)
    else L
  else if h : Nonempty (InflexibleBot A L) then
    fuzz (show (⊥ : TypeIndex) ≠ (h.some.path.ε : Λ) from bot_ne_coe)
      (H.atomImage (h.some.path.B.cons (bot_lt_coe _)) h.some.a h.some.constrains)
  else BaseApprox.flexibleCompletion (π A) A • L

theorem litterCompletion_of_flexible (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : HypAction ⟨A, inr L.toNearLitter⟩) (hflex : Flexible A L) :
    litterCompletion π A L H = BaseApprox.flexibleCompletion (π A) A • L := by
  rw [litterCompletion, dif_neg, dif_neg]
  · rintro ⟨⟨⟨γ, ε, hε, C, rfl⟩, a, rfl⟩⟩
    exact hflex (Inflexible.mk_bot hε _ _)
  · rintro ⟨⟨⟨γ, δ, ε, hδ, hε, hδε, C, rfl⟩, t, rfl⟩⟩
    exact hflex (Inflexible.mk_coe hδ hε hδε _ _)

theorem litterCompletion_of_inflexibleCoe' (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : HypAction ⟨A, inr L.toNearLitter⟩) (h : InflexibleCoe A L) :
    litterCompletion π A L H =
      if h' : _ ∧ _ then
        fuzz h.path.hδε ((ihAction H).hypothesisedAllowable h.path h'.1 h'.2 • h.t)
      else L := by
  -- Push the subsingleton elimination into the kernel by
  -- making it a statement about proof-irrelevance.
  rw [litterCompletion, dif_pos ⟨h⟩]
  have h' : Nonempty (InflexibleCoe A L) := ⟨h⟩
  have : h = Nonempty.some h' := Subsingleton.elim _ _
  subst this
  rfl

theorem litterCompletion_of_inflexibleCoe (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : HypAction ⟨A, inr L.toNearLitter⟩) (h : InflexibleCoe A L)
    (h₁ : StructLAction.Lawful ((ihAction H).comp (h.path.B.cons h.path.hδ)))
    (h₂ : StructLAction.MapFlexible ((ihAction H).comp (h.path.B.cons h.path.hδ))) :
    litterCompletion π A L H =
      fuzz h.path.hδε ((ihAction H).hypothesisedAllowable h.path h₁ h₂ • h.t) := by
  rw [litterCompletion_of_inflexibleCoe', dif_pos]
  · refine' ⟨_, _⟩
    · rw [Subsingleton.elim h] at h₁
      exact h₁
    · rw [Subsingleton.elim h] at h₂
      exact h₂

theorem litterCompletion_of_inflexibleBot (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : HypAction ⟨A, inr L.toNearLitter⟩) (h : InflexibleBot A L) :
    litterCompletion π A L H =
      fuzz (show (⊥ : TypeIndex) ≠ (h.path.ε : Λ) from bot_ne_coe)
        (H.atomImage (h.path.B.cons (bot_lt_coe _)) h.a h.constrains) := by
  rw [litterCompletion, dif_neg, dif_pos, Subsingleton.elim h]
  · exact ⟨h⟩
  · rintro ⟨h'⟩
    exact inflexibleBot_inflexibleCoe h h'

end StructApprox

end ConNF
