import ConNF.Phase2.FlexibleCompletion
import ConNF.Phase2.Reduction
import ConNF.Phase2.Refine

#align_import phase2.litter_completion

open Quiver Set Sum WithBot

open scoped Classical

universe u

namespace ConNF

namespace StructApprox

variable [Params.{u}] {α : Λ} [PositionData] [Phase2Assumptions α]

/-- The inductive hypothesis used for proving freedom of action:
Every free approximation exactly approximates some allowable permutation. -/
def FoaIh (β : Iic α) : Prop :=
  ∀ π₀ : StructApprox β, π₀.Free → ∃ π : Allowable β, π₀.ExactlyApproximates π.toStructPerm

-- TODO: Split off the path bit of inflexible_*. Then rearrange args L and A.
/-- A proof-relevant statement that `L` is `A`-inflexible (excluding `ε = ⊥`). -/
structure InflexibleCoe {β : Iic α} (L : Litter) (A : ExtendedIndex β) where
  γ : Iic α
  (δ ε : Iio α)
  hδ : (δ : Λ) < γ
  hε : (ε : Λ) < γ
  hδε : δ ≠ ε
  b : Quiver.Path (β : TypeIndex) γ
  t : Tangle δ
  hL : L = fMap (coe_ne_coe.mpr <| coe_ne' hδε) t
  hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)

instance {β : Iic α} (L : Litter) (A : ExtendedIndex β) : Subsingleton (InflexibleCoe L A) :=
  by
  constructor
  rintro ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, rfl, rfl⟩
    ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, hL₂, hA₂⟩
  cases Subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons hA₂))
  cases
    Subtype.coe_injective
      (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons (path.heq_of_cons_eq_cons hA₂).Eq))
  cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hA₂).Eq).Eq
  have h₁ := f_map_β (coe_ne_coe.mpr <| coe_ne' hδε₁) t₁
  have h₂ := f_map_β (coe_ne_coe.mpr <| coe_ne' hδε₂) t₂
  rw [hL₂, h₂] at h₁
  cases Subtype.coe_injective (coe_eq_coe.mp h₁)
  cases f_map_injective _ hL₂
  rfl

/-- A proof-relevant statement that `L` is `A`-inflexible, where `δ = ⊥`. -/
structure InflexibleBot {β : Iic α} (L : Litter) (A : ExtendedIndex β) where
  γ : Iic α
  ε : Iio α
  hε : (ε : Λ) < γ
  b : Quiver.Path (β : TypeIndex) γ
  a : Atom
  hL : L = fMap (show (⊥ : TypeIndex) ≠ (ε : Λ) from bot_ne_coe) a
  hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)

instance {β : Iic α} (L : Litter) (A : ExtendedIndex β) : Subsingleton (InflexibleBot L A) :=
  by
  constructor
  rintro ⟨γ₁, ε₁, hε₁, B₁, a₁, rfl, rfl⟩ ⟨γ₂, ε₂, hε₂, B₂, a₂, hL₂, hA₂⟩
  cases Subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons hA₂))
  cases
    Subtype.coe_injective
      (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons (path.heq_of_cons_eq_cons hA₂).Eq))
  cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hA₂).Eq).Eq
  cases f_map_injective _ hL₂
  rfl

theorem inflexibleBot_inflexibleCoe {β : Iic α} {L : Litter} {A : ExtendedIndex β} :
    InflexibleBot L A → InflexibleCoe L A → False :=
  by
  rintro ⟨γ₁, ε₁, hε₁, B₁, a₁, rfl, rfl⟩ ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, hL₂, hA₂⟩
  have h₁ := f_map_β (show (⊥ : type_index) ≠ (ε₁ : Λ) from bot_ne_coe) a₁
  have h₂ := f_map_β (coe_ne_coe.mpr <| coe_ne' hδε₂) t₂
  rw [hL₂, h₂] at h₁
  cases h₁

theorem InflexibleCoe.δ_lt_β {β : Iic α} {L : Litter} {A : ExtendedIndex β}
    (h : InflexibleCoe L A) : (h.δ : Λ) < β :=
  h.hδ.trans_le (show _ from coe_le_coe.mp (le_of_path h.b))

section Comp

variable {β : Iic α} {γ : Iio α} {L : Litter} {B : ExtendedIndex (γ : Iic α)}

def InflexibleCoe.comp (h : InflexibleCoe L B) (A : Path (β : TypeIndex) γ) :
    InflexibleCoe L (A.comp B) :=
  { h with
    b := A.comp h.b
    hA := by rw [← path.comp_cons, ← path.comp_cons] <;> exact congr_arg₂ _ rfl h.hA }

def InflexibleBot.comp (h : InflexibleBot L B) (A : Path (β : TypeIndex) γ) :
    InflexibleBot L (A.comp B) :=
  { h with
    b := A.comp h.b
    hA := by rw [← path.comp_cons, ← path.comp_cons] <;> exact congr_arg₂ _ rfl h.hA }

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
theorem InflexibleCoe.comp_b (h : InflexibleCoe L B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).b = A.comp h.b :=
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
theorem InflexibleBot.comp_b (h : InflexibleBot L B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).b = A.comp h.b :=
  rfl

end Comp

theorem InflexibleBot.constrains {β : Iic α} {L : Litter} {A : ExtendedIndex β}
    (h : InflexibleBot L A) : (inl h.a, h.b.cons (bot_lt_coe _)) <[α] (inr L.toNearLitter, A) :=
  by
  have := constrains.f_map_bot h.hε h.B h.a
  rw [← h.hL, ← h.hA] at this
  exact Relation.TransGen.single this

theorem inflexibleOfInflexibleBot {β : Iic α} {L : Litter} {A : ExtendedIndex β}
    (h : InflexibleBot L A) : Inflexible α L A :=
  by
  have := inflexible.mk_bot h.hε h.B h.a
  rw [← h.hL, ← h.hA] at this
  exact this

theorem inflexibleOfInflexibleCoe {β : Iic α} {L : Litter} {A : ExtendedIndex β}
    (h : InflexibleCoe L A) : Inflexible α L A :=
  by
  have := inflexible.mk_coe h.hδ h.hε h.hδε h.B h.t
  rw [← h.hL, ← h.hA] at this
  exact this

theorem inflexibleBot_or_inflexibleCoe_of_inflexible {β : Iic α} {L : Litter} {A : ExtendedIndex β}
    (h : Inflexible α L A) : Nonempty (InflexibleBot L A) ∨ Nonempty (InflexibleCoe L A) :=
  by
  obtain ⟨hδ, hε, hδε, B, t⟩ | ⟨hε, B, a⟩ := h
  · refine' Or.inr ⟨⟨_, _, _, _, _, _, _, _, rfl, rfl⟩⟩
    assumption
  · exact Or.inl ⟨⟨_, _, _, _, _, rfl, rfl⟩⟩

theorem inflexible_iff_inflexibleBot_or_inflexibleCoe {β : Iic α} {L : Litter}
    {A : ExtendedIndex β} :
    Inflexible α L A ↔ Nonempty (InflexibleBot L A) ∨ Nonempty (InflexibleCoe L A) :=
  by
  constructor
  exact inflexible_bot_or_inflexible_coe_of_inflexible
  rintro (⟨⟨h⟩⟩ | ⟨⟨h⟩⟩)
  exact inflexible_of_inflexible_bot h
  exact inflexible_of_inflexible_coe h

theorem flexible_iff_not_inflexibleBot_coe {β : Iic α} {L : Litter} {A : ExtendedIndex β} :
    Flexible α L A ↔ IsEmpty (InflexibleBot L A) ∧ IsEmpty (InflexibleCoe L A) :=
  by
  constructor
  · intro h
    exact
      ⟨⟨fun h' => h (inflexible_of_inflexible_bot h')⟩,
        ⟨fun h' => h (inflexible_of_inflexible_coe h')⟩⟩
  · intro h₁ h₂
    cases inflexible_bot_or_inflexible_coe_of_inflexible h₂
    exact h₁.1.False h.some
    exact h₁.2.False h.some

theorem flexible_cases' (β : Iic α) (L : Litter) (A : ExtendedIndex β) :
    Flexible α L A ∨ Nonempty (InflexibleBot L A) ∨ Nonempty (InflexibleCoe L A) :=
  by
  rw [← inflexible_iff_inflexible_bot_or_inflexible_coe, or_comm']
  exact flexible_cases α L A

class FreedomOfActionHypothesis (β : Iic α) : Prop where
  freedomOfActionOfLt : ∀ γ < β, FoaIh γ

export FreedomOfActionHypothesis (freedomOfActionOfLt)

/-- The structural action associated to a given inductive hypothesis. -/
def ihAction {β : Iic α} {c : SupportCondition β} (H : Hypothesis c) : StructAction β := fun B =>
  { atomMap := fun a => ⟨_, fun h => H.atomImage B a h⟩
    litterMap := fun L => ⟨_, fun h => H.nearLitterImage B L.toNearLitter h⟩
    atomMap_dom_small := by
      simp only [PFun.dom_mk]
      have := reduction_small'' α (small_singleton c)
      simp only [mem_singleton_iff, exists_prop, exists_eq_left] at this
      refine' small.image_subset (fun a => (inl a, B)) _ this _
      · intro a b h
        simpa only [Prod.mk.inj_iff, eq_self_iff_true, and_true_iff] using h
      · rintro _ ⟨a, h, rfl⟩
        exact h
    litterMap_dom_small := by
      simp only [PFun.dom_mk]
      have := reduction_small'' α (small_singleton c)
      simp only [mem_singleton_iff, exists_prop, exists_eq_left] at this
      refine' small.image_subset (fun L => (inr L.toNearLitter, B)) _ this _
      · intro L₁ L₂ h
        simpa only [Prod.mk.inj_iff, eq_self_iff_true, and_true_iff,
          litter.to_near_litter_injective.eq_iff] using h
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

noncomputable def ConNF.StructAction.allowable {γ : Iio α} (φ : StructAction γ)
    (h : (γ : Iic α) < β) (h₁ : φ.Lawful) (h₂ : φ.MapFlexible) : Allowable γ :=
  (freedomOfActionOfLt _ h _ (StructAction.rcFree _ h₁ h₂)).some

theorem ConNF.StructAction.allowable_exactlyApproximates {γ : Iio α} (φ : StructAction γ)
    (h : (γ : Iic α) < β) (h₁ : φ.Lawful) (h₂ : φ.MapFlexible) :
    (φ.rc h₁).ExactlyApproximates (φ.Allowable h h₁ h₂).toStructPerm :=
  (freedomOfActionOfLt _ h _ (StructAction.rcFree _ h₁ h₂)).choose_spec

noncomputable def ConNF.StructAction.hypothesisedAllowable (φ : StructAction β) {L : Litter}
    {A : ExtendedIndex β} (h : InflexibleCoe L A) (h₁ : (φ.comp (h.b.cons (coe_lt h.hδ))).Lawful)
    (h₂ : (φ.comp (h.b.cons (coe_lt h.hδ))).MapFlexible) : Allowable h.δ :=
  (φ.comp (h.b.cons (coe_lt h.hδ))).Allowable
    (h.hδ.trans_le (show _ from coe_le_coe.mp (le_of_path h.b))) h₁ h₂

/- TODO: Extract out the path bit from inflexible_coe so that the following lemma doesn't need
to be stated. -/
theorem ConNF.StructAction.hypothesisedAllowable_eq {φ : StructAction β} {L L' : Litter}
    {A : ExtendedIndex β} {γ : Iic α} {δ ε : Iio α} {hδ : (δ : Λ) < γ} {hε : (ε : Λ) < γ}
    {hδε : δ ≠ ε} {B : Quiver.Path (β : TypeIndex) γ} (t t' : Tangle δ)
    {hL : L = fMap (coe_ne_coe.mpr <| coe_ne' hδε) t}
    (hL' : L' = fMap (coe_ne_coe.mpr <| coe_ne' hδε) t')
    {hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)} {h₁ h₂} (h₁' h₂') :
    (φ.hypothesisedAllowable ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩ h₁ h₂ : Allowable δ) =
      (φ.hypothesisedAllowable ⟨γ, δ, ε, hδ, hε, hδε, B, t', hL', hA⟩ h₁' h₂' : Allowable δ) :=
  rfl

theorem ConNF.StructAction.hypothesisedAllowable_exactlyApproximates (φ : StructAction β)
    {L : Litter} {A : ExtendedIndex β} (h : InflexibleCoe L A)
    (h₁ : (φ.comp (h.b.cons (coe_lt h.hδ))).Lawful)
    (h₂ : (φ.comp (h.b.cons (coe_lt h.hδ))).MapFlexible) :
    ((φ.comp (h.b.cons (coe_lt h.hδ))).rc h₁).ExactlyApproximates
      (φ.hypothesisedAllowable h h₁ h₂).toStructPerm :=
  (φ.comp (h.b.cons (coe_lt h.hδ))).allowable_exactlyApproximates _ _ _

noncomputable def litterCompletion (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : Hypothesis ⟨inr L.toNearLitter, A⟩) : Litter :=
  if h : Nonempty (InflexibleCoe L A) then
    if hs : _ ∧ _ then
      fMap (coe_ne_coe.mpr <| coe_ne' h.some.hδε)
        ((ihAction H).hypothesisedAllowable h.some hs.1 hs.2 • h.some.t)
    else L
  else
    if h : Nonempty (InflexibleBot L A) then
      fMap (show (⊥ : TypeIndex) ≠ (h.some.ε : Λ) from bot_ne_coe)
        (H.atomImage (h.some.b.cons (bot_lt_coe _)) h.some.a h.some.Constrains)
    else NearLitterApprox.flexibleCompletion α (π A) A • L

theorem litterCompletion_of_flexible (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : Hypothesis ⟨inr L.toNearLitter, A⟩) (hflex : Flexible α L A) :
    litterCompletion π A L H = NearLitterApprox.flexibleCompletion α (π A) A • L :=
  by
  rw [litter_completion, dif_neg, dif_neg]
  · rintro ⟨⟨γ, ε, hε, C, a, rfl, rfl⟩⟩
    exact hflex (inflexible.mk_bot _ _ _)
  · rintro ⟨⟨γ, δ, ε, hδ, hε, hδε, C, t, rfl, rfl⟩⟩
    exact hflex (inflexible.mk_coe hδ _ _ _ _)

theorem litterCompletion_of_inflexible_coe' (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : Hypothesis ⟨inr L.toNearLitter, A⟩) (h : InflexibleCoe L A) :
    litterCompletion π A L H =
      if h' : _ ∧ _ then
        fMap (coe_ne_coe.mpr <| coe_ne' h.hδε)
          ((ihAction H).hypothesisedAllowable h h'.1 h'.2 • h.t)
      else L :=
  by
  rw [litter_completion, dif_pos]
  · repeat' congr 1 <;> try rw [Subsingleton.elim h]
  · exact ⟨h⟩

theorem litterCompletion_of_inflexibleCoe (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : Hypothesis ⟨inr L.toNearLitter, A⟩) (h : InflexibleCoe L A)
    (h₁ : ((ihAction H).comp (h.b.cons (coe_lt h.hδ))).Lawful)
    (h₂ : ((ihAction H).comp (h.b.cons (coe_lt h.hδ))).MapFlexible) :
    litterCompletion π A L H =
      fMap (coe_ne_coe.mpr <| coe_ne' h.hδε) ((ihAction H).hypothesisedAllowable h h₁ h₂ • h.t) :=
  by
  rw [litter_completion_of_inflexible_coe', dif_pos]
  · refine' ⟨_, _⟩
    · rw [Subsingleton.elim h] at h₁
      exact h₁
    · rw [Subsingleton.elim h] at h₂
      exact h₂

theorem litterCompletion_of_inflexibleBot (π : StructApprox β) (A : ExtendedIndex β) (L : Litter)
    (H : Hypothesis ⟨inr L.toNearLitter, A⟩) (h : InflexibleBot L A) :
    litterCompletion π A L H =
      fMap (show (⊥ : TypeIndex) ≠ (h.ε : Λ) from bot_ne_coe)
        (H.atomImage (h.b.cons (bot_lt_coe _)) h.a h.Constrains) :=
  by
  rw [litter_completion, dif_neg, dif_pos, Subsingleton.elim h]
  · exact ⟨h⟩
  · rintro ⟨h'⟩
    exact inflexible_bot_inflexible_coe h h'

end StructApprox

end ConNF
