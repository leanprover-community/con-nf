import ConNF.Foa.Basic.Constrains

open Quiver Set Sum WithBot

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] (α : Λ) [BasePositions] [FoaAssumptions α] {β : TypeIndex}

/-- A litter is *inflexible* if it is the image of some f-map. -/
@[mk_iff]
inductive Inflexible : ExtendedIndex β → Litter → Prop
  | mk_coe ⦃γ : Iic α⦄ ⦃δ : Iio α⦄ ⦃ε : Iio α⦄ (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
    (A : Quiver.Path (β : TypeIndex) γ) (t : Tangle δ) :
    Inflexible ((A.cons (coe_lt hε)).cons (bot_lt_coe _))
      (fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t)
  | mk_bot ⦃γ : Iic α⦄ ⦃ε : Iio α⦄ (hε : (ε : Λ) < γ)
    (A : Quiver.Path (β : TypeIndex) γ) (a : Atom) :
    Inflexible ((A.cons (coe_lt hε)).cons (bot_lt_coe _))
      (fuzz (show (⊥ : TypeIndex) ≠ (ε : Λ) from bot_ne_coe) a)

/-- A litter is *flexible* if it is not the image of any f-map. -/
def Flexible (A : ExtendedIndex β) (L : Litter) : Prop :=
  ¬Inflexible α A L

theorem flexible_cases (A : ExtendedIndex β) (L : Litter) : Inflexible α A L ∨ Flexible α A L :=
  or_not

theorem not_constrains_flexible {β : Λ} (c : SupportCondition β)
    {A : ExtendedIndex β} {L : Litter} (hL : Flexible α A L) :
    ¬c ≺ ⟨A, inr L.toNearLitter⟩ := by
  rintro (⟨A, a⟩ | ⟨A, N, hN⟩ | ⟨A, N, a, ha⟩ | ⟨hδ, hε, hδε, A, t, c, hc⟩ | ⟨hε, A, a⟩)
  · exact hN (NearLitter.IsLitter.mk _)
  · obtain (ha | ha) := ha
    · cases ha.2 ha.1
    · cases ha.2 ha.1
  · exact hL (Inflexible.mk_coe hδ hε hδε _ _)
  · exact hL (Inflexible.mk_bot hε _ _)

theorem not_transConstrains_flexible {β : Λ} (c : SupportCondition β)
    {A : ExtendedIndex β} {L : Litter} (hL : Flexible α A L) :
    ¬c <[α] ⟨A, inr L.toNearLitter⟩ := by
  intro h
  obtain ⟨d, _, hd⟩ := Relation.TransGen.tail'_iff.mp h
  exact not_constrains_flexible α d hL hd

theorem mk_flexible (A : ExtendedIndex β) : #{L | Flexible α A L} = #μ := by
  refine le_antisymm ((Cardinal.mk_subtype_le _).trans mk_litter.le) ?_
  refine ⟨⟨fun ν => ⟨⟨ν, ⊥, α, bot_ne_coe⟩, ?_⟩, ?_⟩⟩
  · intro h
    rw [Inflexible_iff] at h
    obtain ⟨γ, δ, ε, _, hε, hδε, A, t, rfl, h⟩ | ⟨γ, ε, hε, A, t, rfl, h⟩ := h
    all_goals
      apply_fun Litter.γ at h
      rw [fuzz_γ _ _] at h
      exact ne_of_lt (Iio.lt ε) h.symm
  · intro ν₁ ν₂ h
    simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq, Litter.mk.injEq, and_self, and_true] at h
    exact h

variable {α}

theorem Inflexible.comp {γ : TypeIndex} {L : Litter} {A : ExtendedIndex γ} (h : Inflexible α A L)
    (B : Quiver.Path β γ) : Inflexible α (B.comp A) L := by
  induction h with
  | mk_coe => exact Inflexible.mk_coe ‹_› ‹_› ‹_› _ _
  | mk_bot => exact Inflexible.mk_bot ‹_› _ _

@[simp]
theorem not_flexible_iff {L : Litter} {A : ExtendedIndex β} : ¬Flexible α A L ↔ Inflexible α A L :=
  Classical.not_not

theorem flexible_of_comp_flexible {γ : TypeIndex} {L : Litter} {A : ExtendedIndex γ}
    {B : Quiver.Path β γ} (h : Flexible α (B.comp A) L) : Flexible α A L := fun h' => h (h'.comp B)

structure InflexibleCoePath {β : Iic α} (A : ExtendedIndex β) where
  γ : Iic α
  (δ ε : Iio α)
  hδ : (δ : Λ) < γ
  hε : (ε : Λ) < γ
  hδε : δ ≠ ε
  B : Quiver.Path (β : TypeIndex) γ
  hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)

/-- A proof-relevant statement that `L` is `A`-inflexible (excluding `ε = ⊥`). -/
structure InflexibleCoe {β : Iic α} (A : ExtendedIndex β) (L : Litter) where
  path : InflexibleCoePath A
  t : Tangle path.δ
  hL : L = fuzz (coe_ne_coe.mpr <| coe_ne' path.hδε) t

structure InflexibleBotPath {β : Iic α} (A : ExtendedIndex β) where
  γ : Iic α
  ε : Iio α
  hε : (ε : Λ) < γ
  B : Quiver.Path (β : TypeIndex) γ
  hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)

/-- A proof-relevant statement that `L` is `A`-inflexible, where `δ = ⊥`. -/
structure InflexibleBot {β : Iic α} (A : ExtendedIndex β) (L : Litter) where
  path : InflexibleBotPath A
  a : Atom
  hL : L = fuzz (show (⊥ : TypeIndex) ≠ (path.ε : Λ) from bot_ne_coe) a

instance {β : Iic α} (A : ExtendedIndex β) (L : Litter) : Subsingleton (InflexibleCoe A L) := by
  constructor
  rintro ⟨⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, rfl⟩, t₁, rfl⟩
    ⟨⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, hA₂⟩, t₂, hL₂⟩
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

instance {β : Iic α} (A : ExtendedIndex β) (L : Litter) : Subsingleton (InflexibleBot A L) := by
  constructor
  rintro ⟨⟨γ₁, ε₁, hε₁, B₁, rfl⟩, a₁, rfl⟩ ⟨⟨γ₂, ε₂, hε₂, B₂, hA₂⟩, a₂, hL₂⟩
  cases Subtype.coe_injective (coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons hA₂))
  cases Subtype.coe_injective
    (coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hA₂).eq))
  cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hA₂).eq).eq
  cases fuzz_injective _ hL₂
  rfl

theorem inflexibleBot_inflexibleCoe {β : Iic α} {A : ExtendedIndex β} {L : Litter} :
    InflexibleBot A L → InflexibleCoe A L → False := by
  rintro ⟨⟨γ₁, ε₁, hε₁, B₁, rfl⟩, a₁, rfl⟩ ⟨⟨_, δ₂, ε₂, _, _, hδε₂, _, _⟩, t₂, hL₂⟩
  have h₁ := fuzz_β (show (⊥ : TypeIndex) ≠ (ε₁ : Λ) from bot_ne_coe) a₁
  have h₂ := fuzz_β (coe_ne_coe.mpr <| coe_ne' hδε₂) t₂
  rw [hL₂, h₂] at h₁
  cases h₁

theorem InflexibleCoe.δ_lt_β {β : Iic α} {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe A L) : (h.path.δ : Λ) < β :=
  h.path.hδ.trans_le (show _ from coe_le_coe.mp (le_of_path h.path.B))

section Comp

variable {β : Iic α} {γ : Iio α} {B : ExtendedIndex (γ : Iic α)} {L : Litter}

def InflexibleCoePath.comp (h : InflexibleCoePath B) (A : Path (β : TypeIndex) γ) :
    InflexibleCoePath (A.comp B) :=
  { h with
    B := A.comp h.B
    hA := by rw [← Path.comp_cons, ← Path.comp_cons]; exact congr_arg₂ _ rfl h.hA }

def InflexibleBotPath.comp (h : InflexibleBotPath B) (A : Path (β : TypeIndex) γ) :
    InflexibleBotPath (A.comp B) :=
  { h with
    B := A.comp h.B
    hA := by rw [← Path.comp_cons, ← Path.comp_cons]; exact congr_arg₂ _ rfl h.hA }

def InflexibleCoe.comp (h : InflexibleCoe B L) (A : Path (β : TypeIndex) γ) :
    InflexibleCoe (A.comp B) L where
  path := h.path.comp A
  t := h.t
  hL := h.hL

def InflexibleBot.comp (h : InflexibleBot B L) (A : Path (β : TypeIndex) γ) :
    InflexibleBot (A.comp B) L where
  path := h.path.comp A
  a := h.a
  hL := h.hL

@[simp]
theorem InflexibleCoe.comp_path (h : InflexibleCoe B L) (A : Path (β : TypeIndex) γ) :
    (h.comp A).path = h.path.comp A :=
  rfl

@[simp]
theorem InflexibleCoePath.comp_γ (h : InflexibleCoePath B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).γ = h.γ :=
  rfl

@[simp]
theorem InflexibleCoePath.comp_δ (h : InflexibleCoePath B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).δ = h.δ :=
  rfl

@[simp]
theorem InflexibleCoePath.comp_ε (h : InflexibleCoePath B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).ε = h.ε :=
  rfl

@[simp]
theorem InflexibleCoe.comp_t (h : InflexibleCoe B L) (A : Path (β : TypeIndex) γ) :
    (h.comp A).t = h.t :=
  rfl

@[simp]
theorem InflexibleCoePath.comp_B (h : InflexibleCoePath B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).B = A.comp h.B :=
  rfl

@[simp]
theorem InflexibleBot.comp_path (h : InflexibleBot B L) (A : Path (β : TypeIndex) γ) :
    (h.comp A).path = h.path.comp A :=
  rfl

@[simp]
theorem InflexibleBotPath.comp_γ (h : InflexibleBotPath B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).γ = h.γ :=
  rfl

@[simp]
theorem InflexibleBotPath.comp_ε (h : InflexibleBotPath B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).ε = h.ε :=
  rfl

@[simp]
theorem InflexibleBot.comp_a (h : InflexibleBot B L) (A : Path (β : TypeIndex) γ) :
    (h.comp A).a = h.a :=
  rfl

@[simp]
theorem InflexibleBotPath.comp_B (h : InflexibleBotPath B) (A : Path (β : TypeIndex) γ) :
    (h.comp A).B = A.comp h.B :=
  rfl

end Comp

theorem InflexibleBot.constrains {β : Iic α} {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot A L) :
    ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩ <[α] ⟨A, inr L.toNearLitter⟩ := by
  have := Constrains.fuzz_bot h.path.hε h.path.B h.a
  rw [← h.hL, ← h.path.hA] at this
  exact Relation.TransGen.single this

theorem inflexible_of_inflexibleBot {β : Iic α} {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot A L) : Inflexible α A L := by
  have := Inflexible.mk_bot h.path.hε h.path.B h.a
  rw [← h.hL, ← h.path.hA] at this
  exact this

theorem inflexible_of_inflexibleCoe {β : Iic α} {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe A L) : Inflexible α A L := by
  have := Inflexible.mk_coe h.path.hδ h.path.hε h.path.hδε h.path.B h.t
  rw [← h.hL, ← h.path.hA] at this
  exact this

theorem inflexibleBot_or_inflexibleCoe_of_inflexible {β : Iic α} {A : ExtendedIndex β} {L : Litter}
    (h : Inflexible α A L) : Nonempty (InflexibleBot A L) ∨ Nonempty (InflexibleCoe A L) := by
  obtain ⟨hδ, hε, hδε, B, t⟩ | ⟨hε, B, a⟩ := h
  · refine' Or.inr ⟨⟨⟨_, _, _, _, _, _, _, rfl⟩, _, rfl⟩⟩ <;> assumption
  · refine' Or.inl ⟨⟨⟨_, _, _, _, rfl⟩, _, rfl⟩⟩; assumption

theorem inflexible_iff_inflexibleBot_or_inflexibleCoe {β : Iic α} {A : ExtendedIndex β}
    {L : Litter} :
    Inflexible α A L ↔ Nonempty (InflexibleBot A L) ∨ Nonempty (InflexibleCoe A L) := by
  constructor
  exact inflexibleBot_or_inflexibleCoe_of_inflexible
  rintro (⟨⟨h⟩⟩ | ⟨⟨h⟩⟩)
  exact inflexible_of_inflexibleBot h
  exact inflexible_of_inflexibleCoe h

theorem flexible_iff_not_inflexibleBot_inflexibleCoe {β : Iic α} {A : ExtendedIndex β}
    {L : Litter} :
    Flexible α A L ↔ IsEmpty (InflexibleBot A L) ∧ IsEmpty (InflexibleCoe A L) := by
  constructor
  · intro h
    exact ⟨⟨fun h' => h (inflexible_of_inflexibleBot h')⟩,
      ⟨fun h' => h (inflexible_of_inflexibleCoe h')⟩⟩
  · intro h₁ h₂
    obtain h | h := inflexibleBot_or_inflexibleCoe_of_inflexible h₂
    · exact h₁.1.false h.some
    · exact h₁.2.false h.some

theorem flexible_cases' (β : Iic α) (A : ExtendedIndex β) (L : Litter) :
    Flexible α A L ∨ Nonempty (InflexibleBot A L) ∨ Nonempty (InflexibleCoe A L) := by
  rw [← inflexible_iff_inflexibleBot_or_inflexibleCoe, or_comm]
  exact flexible_cases α A L

end ConNF
