import ConNF.Foa.Basic.Reduction
import ConNF.Foa.Action.Refine
import ConNF.Foa.Complete.FlexibleCompletion

open Quiver Set Sum WithBot

open scoped Classical

universe u

namespace ConNF

namespace StructApprox

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α]

/-- The inductive hypothesis used for proving freedom of action:
Every free approximation exactly approximates some allowable permutation. -/
def FoaIh (β : Iic α) : Prop :=
  ∀ π₀ : StructApprox β, π₀.Free →
  ∃ π : Allowable β, π₀.ExactlyApproximates (Allowable.toStructPerm π)

-- TODO: Split off the path bit of inflexible_*. Then rearrange args L and A.
-- TODO: Move Inflexible* objects into a new file.
/-- A proof-relevant statement that `L` is `A`-inflexible (excluding `ε = ⊥`). -/
structure InflexibleCoe {β : Iic α} (L : Litter) (A : ExtendedIndex β) where
  γ : Iic α
  (δ ε : Iio α)
  hδ : (δ : Λ) < γ
  hε : (ε : Λ) < γ
  hδε : δ ≠ ε
  B : Quiver.Path (β : TypeIndex) γ
  t : Tangle δ
  hL : L = fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t
  hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)

instance {β : Iic α} (L : Litter) (A : ExtendedIndex β) : Subsingleton (InflexibleCoe L A) := by
  constructor
  rintro ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, rfl, rfl⟩
    ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, hL₂, hA₂⟩
  cases Subtype.coe_injective (coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons hA₂))
  cases Subtype.coe_injective
    (coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hA₂).eq))
  cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hA₂).eq).eq
  have h₁ := fuzz_β (coe_ne_coe.mpr <| coe_ne' hδε₁) t₁
  have h₂ := fuzz_β (coe_ne_coe.mpr <| coe_ne' hδε₂) t₂
  rw [hL₂, h₂] at h₁
  cases Subtype.coe_injective (coe_eq_coe.mp h₁)
  cases fuzz_injective _ hL₂
  rfl

/-- A proof-relevant statement that `L` is `A`-inflexible, where `δ = ⊥`. -/
structure InflexibleBot {β : Iic α} (L : Litter) (A : ExtendedIndex β) where
  γ : Iic α
  ε : Iio α
  hε : (ε : Λ) < γ
  B : Quiver.Path (β : TypeIndex) γ
  a : Atom
  hL : L = fuzz (show (⊥ : TypeIndex) ≠ (ε : Λ) from bot_ne_coe) a
  hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)

instance {β : Iic α} (L : Litter) (A : ExtendedIndex β) : Subsingleton (InflexibleBot L A) := by
  constructor
  rintro ⟨γ₁, ε₁, hε₁, B₁, a₁, rfl, rfl⟩ ⟨γ₂, ε₂, hε₂, B₂, a₂, hL₂, hA₂⟩
  cases Subtype.coe_injective (coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons hA₂))
  cases Subtype.coe_injective
    (coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hA₂).eq))
  cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hA₂).eq).eq
  cases fuzz_injective _ hL₂
  rfl

theorem inflexibleBot_inflexibleCoe {β : Iic α} {L : Litter} {A : ExtendedIndex β} :
    InflexibleBot L A → InflexibleCoe L A → False := by
  rintro ⟨γ₁, ε₁, hε₁, B₁, a₁, rfl, rfl⟩ ⟨_, δ₂, ε₂, _, _, hδε₂, _, t₂, hL₂, _⟩
  have h₁ := fuzz_β (show (⊥ : TypeIndex) ≠ (ε₁ : Λ) from bot_ne_coe) a₁
  have h₂ := fuzz_β (coe_ne_coe.mpr <| coe_ne' hδε₂) t₂
  rw [hL₂, h₂] at h₁
  cases h₁

theorem InflexibleCoe.δ_lt_β {β : Iic α} {L : Litter} {A : ExtendedIndex β}
    (h : InflexibleCoe L A) : (h.δ : Λ) < β :=
  h.hδ.trans_le (show _ from coe_le_coe.mp (le_of_path h.B))

section Comp

variable {β : Iic α} {γ : Iio α} {L : Litter} {B : ExtendedIndex (γ : Iic α)}

def InflexibleCoe.comp (h : InflexibleCoe L B) (A : Path (β : TypeIndex) γ) :
    InflexibleCoe L (A.comp B) :=
  { h with
    B := A.comp h.B
    hA := by rw [← Path.comp_cons, ← Path.comp_cons]; exact congr_arg₂ _ rfl h.hA }

def InflexibleBot.comp (h : InflexibleBot L B) (A : Path (β : TypeIndex) γ) :
    InflexibleBot L (A.comp B) :=
  { h with
    B := A.comp h.B
    hA := by rw [← Path.comp_cons, ← Path.comp_cons]; exact congr_arg₂ _ rfl h.hA }

@[simp]
theorem InflexibleCoe.comp_γ (h : InflexibleCoe L B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).γ = h.γ :=
  rfl

@[simp]
theorem InflexibleCoe.comp_δ (h : InflexibleCoe L B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).δ = h.δ :=
  rfl

@[simp]
theorem InflexibleCoe.comp_ε (h : InflexibleCoe L B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).ε = h.ε :=
  rfl

@[simp]
theorem InflexibleCoe.comp_t (h : InflexibleCoe L B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).t = h.t :=
  rfl

@[simp]
theorem InflexibleCoe.comp_B (h : InflexibleCoe L B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).B = A.comp h.B :=
  rfl

@[simp]
theorem InflexibleBot.comp_γ (h : InflexibleBot L B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).γ = h.γ :=
  rfl

@[simp]
theorem InflexibleBot.comp_ε (h : InflexibleBot L B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).ε = h.ε :=
  rfl

@[simp]
theorem InflexibleBot.comp_a (h : InflexibleBot L B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).a = h.a :=
  rfl

@[simp]
theorem InflexibleBot.comp_B (h : InflexibleBot L B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).B = A.comp h.B :=
  rfl

end Comp

theorem InflexibleBot.constrains {β : Iic α} {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot L A) : ⟨h.B.cons (bot_lt_coe _), inl h.a⟩ <[α] ⟨A, inr L.toNearLitter⟩ := by
  have := Constrains.fuzz_bot h.hε h.B h.a
  rw [← h.hL, ← h.hA] at this
  exact Relation.TransGen.single this

theorem inflexible_of_inflexibleBot {β : Iic α} {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot L A) : Inflexible α L A := by
  have := Inflexible.mk_bot h.hε h.B h.a
  rw [← h.hL, ← h.hA] at this
  exact this

theorem inflexible_of_inflexibleCoe {β : Iic α} {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe L A) : Inflexible α L A := by
  have := Inflexible.mk_coe h.hδ h.hε h.hδε h.B h.t
  rw [← h.hL, ← h.hA] at this
  exact this

theorem inflexibleBot_or_inflexibleCoe_of_inflexible {β : Iic α} {A : ExtendedIndex β} {L : Litter}
    (h : Inflexible α L A) : Nonempty (InflexibleBot L A) ∨ Nonempty (InflexibleCoe L A) := by
  obtain ⟨hδ, hε, hδε, B, t⟩ | ⟨hε, B, a⟩ := h
  · refine' Or.inr ⟨⟨_, _, _, _, _, _, _, _, rfl, rfl⟩⟩ <;> assumption
  · refine' Or.inl ⟨⟨_, _, _, _, _, rfl, rfl⟩⟩; assumption

theorem inflexible_iff_inflexibleBot_or_inflexibleCoe {β : Iic α} {A : ExtendedIndex β}
    {L : Litter} :
    Inflexible α L A ↔ Nonempty (InflexibleBot L A) ∨ Nonempty (InflexibleCoe L A) := by
  constructor
  exact inflexibleBot_or_inflexibleCoe_of_inflexible
  rintro (⟨⟨h⟩⟩ | ⟨⟨h⟩⟩)
  exact inflexible_of_inflexibleBot h
  exact inflexible_of_inflexibleCoe h

theorem flexible_iff_not_inflexibleBot_inflexibleCoe {β : Iic α} {A : ExtendedIndex β}
    {L : Litter} :
    Flexible α L A ↔ IsEmpty (InflexibleBot L A) ∧ IsEmpty (InflexibleCoe L A) := by
  constructor
  · intro h
    exact ⟨⟨fun h' => h (inflexible_of_inflexibleBot h')⟩,
      ⟨fun h' => h (inflexible_of_inflexibleCoe h')⟩⟩
  · intro h₁ h₂
    obtain h | h := inflexibleBot_or_inflexibleCoe_of_inflexible h₂
    · exact h₁.1.false h.some
    · exact h₁.2.false h.some

theorem flexible_cases' (β : Iic α) (A : ExtendedIndex β) (L : Litter) :
    Flexible α L A ∨ Nonempty (InflexibleBot L A) ∨ Nonempty (InflexibleCoe L A) := by
  rw [← inflexible_iff_inflexibleBot_or_inflexibleCoe, or_comm]
  exact flexible_cases α L A

class FreedomOfActionHypothesis (β : Iic α) : Prop where
  freedomOfAction_of_lt : ∀ γ < β, FoaIh γ

export FreedomOfActionHypothesis (freedomOfAction_of_lt)

/-- The structural action associated to a given inductive hypothesis. -/
def ihAction {β : Iic α} {c : SupportCondition β} (H : Hypothesis c) : StructAction β := fun B =>
  { atomMap := fun a => ⟨_, fun h => H.atomImage B a h⟩
    litterMap := fun L => ⟨_, fun h => H.nearLitterImage B L.toNearLitter h⟩
    atomMap_dom_small := by
      simp only [PFun.dom_mk]
      have := transClosure_small α (small_singleton c)
      simp only [transClosure, mem_singleton_iff, exists_prop, exists_eq_left] at this
      refine' Small.image_subset (fun a => ⟨B, inl a⟩) _ this _
      · intro a b h
        simpa [SupportCondition.mk.injEq, inl.injEq, true_and] using h
      · rintro _ ⟨a, h, rfl⟩
        exact h
    litterMap_dom_small := by
      simp only [PFun.dom_mk]
      have := transClosure_small α (small_singleton c)
      simp only [transClosure, mem_singleton_iff, exists_prop, exists_eq_left] at this
      refine' Small.image_subset (fun L => ⟨B, inr L.toNearLitter⟩) _ this _
      · intro L₁ L₂ h
        simpa only [SupportCondition.mk.injEq, inr.injEq, Litter.toNearLitter_injective.eq_iff,
          true_and] using h
      · rintro _ ⟨a, h, rfl⟩
        exact h }

@[simp]
theorem ihAction_atomMap {β : Iic α} {c : SupportCondition β} {H : Hypothesis c}
    {B : ExtendedIndex β} {a : Atom} : (ihAction H B).atomMap a = ⟨_, fun h => H.atomImage B a h⟩ :=
  rfl

@[simp]
theorem ihAction_litterMap {β : Iic α} {c : SupportCondition β} {H : Hypothesis c}
    {B : ExtendedIndex β} {L : Litter} :
    (ihAction H B).litterMap L = ⟨_, fun h => H.nearLitterImage B L.toNearLitter h⟩ :=
  rfl

variable {β : Iic α} [FreedomOfActionHypothesis β]

noncomputable def _root_.ConNF.StructAction.allowable {γ : Iio α} (φ : StructAction γ)
    (h : (γ : Iic α) < β) (h₁ : φ.Lawful) (h₂ : φ.MapFlexible) : Allowable γ :=
  (freedomOfAction_of_lt _ h _ (StructAction.rc_free _ h₁ h₂)).choose

theorem _root_.ConNF.StructAction.allowable_exactlyApproximates {γ : Iio α} (φ : StructAction γ)
    (h : (γ : Iic α) < β) (h₁ : φ.Lawful) (h₂ : φ.MapFlexible) :
    (φ.rc h₁).ExactlyApproximates (Allowable.toStructPerm (φ.allowable h h₁ h₂)) :=
  (freedomOfAction_of_lt _ h _ (StructAction.rc_free _ h₁ h₂)).choose_spec

noncomputable def _root_.ConNF.StructAction.hypothesisedAllowable (φ : StructAction β) {L : Litter}
    {A : ExtendedIndex β} (h : InflexibleCoe L A)
    (h₁ : StructAction.Lawful (φ.comp (h.B.cons (coe_lt h.hδ))))
    (h₂ : StructAction.MapFlexible (φ.comp (h.B.cons (coe_lt h.hδ)))) : Allowable h.δ :=
  StructAction.allowable
    (φ.comp (h.B.cons (coe_lt h.hδ)))
    (h.hδ.trans_le (show _ from coe_le_coe.mp (le_of_path h.B)))
    h₁ h₂

/- TODO: Extract out the path bit from inflexible_coe so that the following lemma doesn't need
to be stated. -/
theorem _root_.ConNF.StructAction.hypothesisedAllowable_eq {φ : StructAction β} {L L' : Litter}
    {A : ExtendedIndex β} {γ : Iic α} {δ ε : Iio α} {hδ : (δ : Λ) < γ} {hε : (ε : Λ) < γ}
    {hδε : δ ≠ ε} {B : Quiver.Path (β : TypeIndex) γ} (t t' : Tangle δ)
    {hL : L = fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t}
    (hL' : L' = fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t')
    {hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)} {h₁ h₂} (h₁' h₂') :
    (φ.hypothesisedAllowable ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩ h₁ h₂ : Allowable δ) =
      (φ.hypothesisedAllowable ⟨γ, δ, ε, hδ, hε, hδε, B, t', hL', hA⟩ h₁' h₂' : Allowable δ) :=
  rfl

theorem _root_.ConNF.StructAction.hypothesisedAllowable_exactlyApproximates (φ : StructAction β)
    {L : Litter} {A : ExtendedIndex β} (h : InflexibleCoe L A)
    (h₁ : StructAction.Lawful (φ.comp (h.B.cons (coe_lt h.hδ))))
    (h₂ : StructAction.MapFlexible (φ.comp (h.B.cons (coe_lt h.hδ)))) :
    StructApprox.ExactlyApproximates
      (StructAction.rc (φ.comp (h.B.cons (coe_lt h.hδ))) h₁)
      (Allowable.toStructPerm (φ.hypothesisedAllowable h h₁ h₂)) :=
  StructAction.allowable_exactlyApproximates (φ.comp (h.B.cons (coe_lt h.hδ))) _ _ _

noncomputable def litterCompletion (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : Hypothesis ⟨A, inr L.toNearLitter⟩) : Litter :=
  if h : Nonempty (InflexibleCoe L A) then
    if hs : _ ∧ _ then
      fuzz (coe_ne_coe.mpr <| coe_ne' h.some.hδε)
        ((ihAction H).hypothesisedAllowable h.some hs.1 hs.2 • h.some.t)
    else L
  else
    if h : Nonempty (InflexibleBot L A) then
      fuzz (show (⊥ : TypeIndex) ≠ (h.some.ε : Λ) from bot_ne_coe)
        (H.atomImage (h.some.B.cons (bot_lt_coe _)) h.some.a h.some.constrains)
    else NearLitterApprox.flexibleCompletion α (π A) A • L

theorem litterCompletion_of_flexible (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : Hypothesis ⟨A, inr L.toNearLitter⟩) (hflex : Flexible α L A) :
    litterCompletion π A L H = NearLitterApprox.flexibleCompletion α (π A) A • L := by
  rw [litterCompletion, dif_neg, dif_neg]
  · rintro ⟨⟨γ, ε, hε, C, a, rfl, rfl⟩⟩
    exact hflex (Inflexible.mk_bot hε _ _)
  · rintro ⟨⟨γ, δ, ε, hδ, hε, hδε, C, t, rfl, rfl⟩⟩
    exact hflex (Inflexible.mk_coe hδ hε hδε _ _)

theorem litterCompletion_of_inflexibleCoe' (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : Hypothesis ⟨A, inr L.toNearLitter⟩) (h : InflexibleCoe L A) :
    litterCompletion π A L H =
      if h' : _ ∧ _ then
        fuzz (coe_ne_coe.mpr <| coe_ne' h.hδε)
          ((ihAction H).hypothesisedAllowable h h'.1 h'.2 • h.t)
      else L := by
  -- Push the subsingleton elimination into the kernel by
  -- making it a statement about proof-irrelevance.
  rw [litterCompletion, dif_pos ⟨h⟩]
  have h' : Nonempty (InflexibleCoe L A) := ⟨h⟩
  have : h = Nonempty.some h' := Subsingleton.elim _ _
  subst this
  rfl

theorem litterCompletion_of_inflexibleCoe (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : Hypothesis ⟨A, inr L.toNearLitter⟩) (h : InflexibleCoe L A)
    (h₁ : StructAction.Lawful ((ihAction H).comp (h.B.cons (coe_lt h.hδ))))
    (h₂ : StructAction.MapFlexible ((ihAction H).comp (h.B.cons (coe_lt h.hδ)))) :
    litterCompletion π A L H =
      fuzz (coe_ne_coe.mpr <| coe_ne' h.hδε)
        ((ihAction H).hypothesisedAllowable h h₁ h₂ • h.t) := by
  rw [litterCompletion_of_inflexibleCoe', dif_pos]
  · refine' ⟨_, _⟩
    · rw [Subsingleton.elim h] at h₁
      exact h₁
    · rw [Subsingleton.elim h] at h₂
      exact h₂

theorem litterCompletion_of_inflexibleBot (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : Hypothesis ⟨A, inr L.toNearLitter⟩) (h : InflexibleBot L A) :
    litterCompletion π A L H =
      fuzz (show (⊥ : TypeIndex) ≠ (h.ε : Λ) from bot_ne_coe)
        (H.atomImage (h.B.cons (bot_lt_coe _)) h.a h.constrains) := by
  rw [litterCompletion, dif_neg, dif_pos, Subsingleton.elim h]
  · exact ⟨h⟩
  · rintro ⟨h'⟩
    exact inflexibleBot_inflexibleCoe h h'

end StructApprox

end ConNF
