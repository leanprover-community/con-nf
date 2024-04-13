import ConNF.FOA.Basic.Hypotheses

open Quiver Set Sum WithBot

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [FOAAssumptions] {β : TypeIndex}

/-- A litter is *inflexible* if it is the image of some f-map. -/
@[mk_iff]
inductive Inflexible : ExtendedIndex β → Litter → Prop
  | mk_coe ⦃γ : Λ⦄ [LeLevel γ] ⦃δ : Λ⦄ [LtLevel δ] ⦃ε : Λ⦄ [LtLevel ε]
    (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : (δ : TypeIndex) ≠ ε)
    (A : Quiver.Path (β : TypeIndex) γ) (t : Tangle δ) :
    Inflexible ((A.cons hε).cons (bot_lt_coe _)) (fuzz hδε t)
  | mk_bot ⦃γ : Λ⦄ [LeLevel γ] ⦃ε : Λ⦄ [LtLevel ε] (hε : (ε : TypeIndex) < γ)
    (A : Quiver.Path (β : TypeIndex) γ) (a : Atom) :
    Inflexible ((A.cons hε).cons (bot_lt_coe _)) (fuzz (bot_ne_coe (a := ε)) a)

/-- A litter is *flexible* if it is not the image of any f-map. -/
def Flexible (A : ExtendedIndex β) (L : Litter) : Prop :=
  ¬Inflexible A L

theorem flexible_cases (A : ExtendedIndex β) (L : Litter) : Inflexible A L ∨ Flexible A L :=
  or_not

theorem mk_flexible (A : ExtendedIndex β) : #{L | Flexible A L} = #μ := by
  refine le_antisymm ((Cardinal.mk_subtype_le _).trans mk_litter.le) ?_
  refine ⟨⟨fun ν => ⟨⟨ν, ⊥, α, bot_ne_coe⟩, ?_⟩, ?_⟩⟩
  · intro h
    rw [inflexible_iff] at h
    obtain ⟨γ, _, δ, _, ε, _, _, hε, hδε, A, t, rfl, h⟩ | ⟨γ, _, ε, _, hε, A, t, rfl, h⟩ := h
    all_goals
      apply_fun Litter.γ at h
      rw [fuzz_γ _ _] at h
      exact ne_of_lt (coe_lt_coe.mp LtLevel.elim) h.symm
  · intro ν₁ ν₂ h
    simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq, Litter.mk.injEq, and_self, and_true] at h
    exact h

theorem Inflexible.comp {γ : TypeIndex} {L : Litter} {A : ExtendedIndex γ} (h : Inflexible A L)
    (B : Quiver.Path β γ) : Inflexible (B.comp A) L := by
  induction h with
  | mk_coe => exact Inflexible.mk_coe ‹_› ‹_› ‹_› _ _
  | mk_bot => exact Inflexible.mk_bot ‹_› _ _

@[simp]
theorem not_flexible_iff {L : Litter} {A : ExtendedIndex β} : ¬Flexible A L ↔ Inflexible A L :=
  Classical.not_not

theorem flexible_of_comp_flexible {γ : TypeIndex} {L : Litter} {A : ExtendedIndex γ}
    {B : Quiver.Path β γ} (h : Flexible (B.comp A) L) : Flexible A L := fun h' => h (h'.comp B)

structure InflexibleCoePath {β : Λ} (A : ExtendedIndex β) where
  (γ δ ε : Λ)
  [inst_γ : LeLevel γ]
  [inst_δ : LtLevel δ]
  [inst_ε : LtLevel ε]
  hδ : (δ : TypeIndex) < γ
  hε : (ε : TypeIndex) < γ
  hδε : (δ : TypeIndex) ≠ ε
  B : Quiver.Path (β : TypeIndex) γ
  hA : A = (B.cons hε).cons (bot_lt_coe _)

instance {β : Λ} (A : ExtendedIndex β) (path : InflexibleCoePath A) : LeLevel path.γ := path.inst_γ
instance {β : Λ} (A : ExtendedIndex β) (path : InflexibleCoePath A) : LtLevel path.δ := path.inst_δ
instance {β : Λ} (A : ExtendedIndex β) (path : InflexibleCoePath A) : LtLevel path.ε := path.inst_ε

/-- A proof-relevant statement that `L` is `A`-inflexible (excluding `ε = ⊥`). -/
structure InflexibleCoe {β : Λ} (A : ExtendedIndex β) (L : Litter) where
  path : InflexibleCoePath A
  t : Tangle path.δ
  hL : L = fuzz path.hδε t

structure InflexibleBotPath {β : Λ} (A : ExtendedIndex β) where
  (γ ε : Λ)
  [inst_γ : LeLevel γ]
  [inst_ε : LtLevel ε]
  hε : (ε : TypeIndex) < γ
  B : Quiver.Path (β : TypeIndex) γ
  hA : A = (B.cons hε).cons (bot_lt_coe _)

instance {β : Λ} (A : ExtendedIndex β) (path : InflexibleBotPath A) : LeLevel path.γ := path.inst_γ
instance {β : Λ} (A : ExtendedIndex β) (path : InflexibleBotPath A) : LtLevel path.ε := path.inst_ε

/-- A proof-relevant statement that `L` is `A`-inflexible, where `δ = ⊥`. -/
structure InflexibleBot {β : Λ} (A : ExtendedIndex β) (L : Litter) where
  path : InflexibleBotPath A
  a : Atom
  hL : L = fuzz (bot_ne_coe (a := path.ε)) a

instance {β : Λ} (A : ExtendedIndex β) (L : Litter) : Subsingleton (InflexibleCoe A L) := by
  constructor
  rintro ⟨⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, rfl⟩, t₁, rfl⟩
    ⟨⟨γ₂, δ₂, ε₂,hδ₂, hε₂, hδε₂, B₂, hA₂⟩, t₂, hL₂⟩
  cases coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons hA₂)
  cases coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hA₂).eq)
  cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hA₂).eq).eq
  cases fuzz_congr_β hL₂
  cases fuzz_injective _ hL₂
  rfl

instance {β : Λ} (A : ExtendedIndex β) (L : Litter) : Subsingleton (InflexibleBot A L) := by
  constructor
  rintro ⟨⟨γ₁, ε₁, hε₁, B₁, rfl⟩, a₁, rfl⟩ ⟨⟨γ₂, ε₂, hε₂, B₂, hA₂⟩, a₂, hL₂⟩
  cases coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons hA₂)
  cases coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hA₂).eq)
  cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hA₂).eq).eq
  cases fuzz_injective _ hL₂
  rfl

theorem inflexibleBot_inflexibleCoe {β : Λ} {A : ExtendedIndex β} {L : Litter} :
    InflexibleBot A L → InflexibleCoe A L → False := by
  rintro ⟨⟨γ₁, ε₁, hε₁, B₁, rfl⟩, a₁, rfl⟩ ⟨⟨_, δ₂, ε₂, _, _, hδε₂, _, _⟩, t₂, hL₂⟩
  cases fuzz_congr_β hL₂

theorem InflexibleCoePath.δ_lt_β {β : Λ} {A : ExtendedIndex β}
    (h : InflexibleCoePath A) : (h.δ : TypeIndex) < β :=
  h.hδ.trans_le (le_of_path h.B)

theorem InflexibleCoe.δ_lt_β {β : Λ} {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe A L) : (h.path.δ : TypeIndex) < β :=
  h.path.δ_lt_β

section Comp

variable {β : Λ} {γ : Λ} [LtLevel γ] {B : ExtendedIndex γ} {L : Litter}

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

@[aesop unsafe 50% apply]
theorem inflexible_of_inflexibleBot {β : Λ} {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot A L) : Inflexible A L := by
  have := Inflexible.mk_bot h.path.hε h.path.B h.a
  rw [← h.hL, ← h.path.hA] at this
  exact this

@[aesop unsafe 50% apply]
theorem inflexible_of_inflexibleCoe {β : Λ} {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe A L) : Inflexible A L := by
  have := Inflexible.mk_coe h.path.hδ h.path.hε h.path.hδε h.path.B h.t
  rw [← h.hL, ← h.path.hA] at this
  exact this

theorem inflexibleBot_or_inflexibleCoe_of_inflexible {β : Λ} {A : ExtendedIndex β} {L : Litter}
    (h : Inflexible A L) : Nonempty (InflexibleBot A L) ∨ Nonempty (InflexibleCoe A L) := by
  obtain ⟨hδ, hε, hδε, B, t⟩ | ⟨hε, B, a⟩ := h
  · exact Or.inr ⟨⟨⟨_, _, _, hδ, hε, hδε, _, rfl⟩, t, rfl⟩⟩
  · exact Or.inl ⟨⟨⟨_, _, hε, _, rfl⟩, a, rfl⟩⟩

theorem inflexible_iff_inflexibleBot_or_inflexibleCoe {β : Λ} {A : ExtendedIndex β}
    {L : Litter} :
    Inflexible A L ↔ Nonempty (InflexibleBot A L) ∨ Nonempty (InflexibleCoe A L) := by
  constructor
  exact inflexibleBot_or_inflexibleCoe_of_inflexible
  rintro (⟨⟨h⟩⟩ | ⟨⟨h⟩⟩)
  exact inflexible_of_inflexibleBot h
  exact inflexible_of_inflexibleCoe h

@[aesop unsafe 50% apply]
theorem flexible_iff_not_inflexibleBot_inflexibleCoe {β : Λ} {A : ExtendedIndex β}
    {L : Litter} :
    Flexible A L ↔ IsEmpty (InflexibleBot A L) ∧ IsEmpty (InflexibleCoe A L) := by
  constructor
  · intro h
    exact ⟨⟨fun h' => h (inflexible_of_inflexibleBot h')⟩,
      ⟨fun h' => h (inflexible_of_inflexibleCoe h')⟩⟩
  · intro h₁ h₂
    obtain h | h := inflexibleBot_or_inflexibleCoe_of_inflexible h₂
    · exact h₁.1.false h.some
    · exact h₁.2.false h.some

theorem flexible_cases' {β : Λ} (A : ExtendedIndex β) (L : Litter) :
    Flexible A L ∨ Nonempty (InflexibleBot A L) ∨ Nonempty (InflexibleCoe A L) := by
  rw [← inflexible_iff_inflexibleBot_or_inflexibleCoe, or_comm]
  exact flexible_cases A L

def InflexibleCoe.smul {β : Λ} [LeLevel β] {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe A L) (ρ : Allowable β) :
    InflexibleCoe A (Allowable.toStructPerm ρ A • L) :=
  ⟨h.path,
    Allowable.comp (h.path.B.cons h.path.hδ) ρ • h.t, by
      rw [← toStructPerm_smul_fuzz h.path.hδ h.path.hε]
      simp only [h.path.hA, h.hL]⟩

@[simp]
theorem inflexibleCoe_smul {β : Λ} [LeLevel β]
    {A : ExtendedIndex β} {L : Litter} {ρ : Allowable β} :
    Nonempty (InflexibleCoe A (Allowable.toStructPerm ρ A • L)) ↔ Nonempty (InflexibleCoe A L) := by
  constructor
  · rintro ⟨h⟩
    have := h.smul ρ⁻¹
    simp only [map_inv, Tree.inv_apply, inv_smul_smul] at this
    exact ⟨this⟩
  · rintro ⟨h⟩
    exact ⟨h.smul ρ⟩

def InflexibleBot.smul {β : Λ} [LeLevel β] {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot A L) (ρ : Allowable β) :
    InflexibleBot A (Allowable.toStructPerm ρ A • L) :=
  ⟨h.path,
    Allowable.comp (h.path.B.cons (bot_lt_coe _)) ρ • h.a, by
      rw [← toStructPerm_smul_fuzz (bot_lt_coe _) h.path.hε]
      simp only [h.path.hA, h.hL]⟩

@[simp]
theorem inflexibleBot_smul {β : Λ} [LeLevel β]
    {A : ExtendedIndex β} {L : Litter} {ρ : Allowable β} :
    Nonempty (InflexibleBot A (Allowable.toStructPerm ρ A • L)) ↔ Nonempty (InflexibleBot A L) := by
  constructor
  · rintro ⟨h⟩
    have := h.smul ρ⁻¹
    simp only [map_inv, Tree.inv_apply, inv_smul_smul] at this
    exact ⟨this⟩
  · rintro ⟨h⟩
    exact ⟨h.smul ρ⟩

theorem Flexible.smul {β : Λ} [LeLevel β] {A : ExtendedIndex β} {L : Litter}
    (h : Flexible A L) (ρ : Allowable β) :
    Flexible A (Allowable.toStructPerm ρ A • L) := by
  rw [flexible_iff_not_inflexibleBot_inflexibleCoe, ← not_nonempty_iff, ← not_nonempty_iff,
    inflexibleBot_smul, inflexibleCoe_smul, not_nonempty_iff, not_nonempty_iff,
    ← flexible_iff_not_inflexibleBot_inflexibleCoe]
  exact h

@[simp]
theorem flexible_smul {β : Λ} [LeLevel β]
    {A : ExtendedIndex β} {L : Litter} {ρ : Allowable β} :
    Flexible A (Allowable.toStructPerm ρ A • L) ↔ Flexible A L :=
  by simp only [flexible_iff_not_inflexibleBot_inflexibleCoe, ← not_nonempty_iff,
    inflexibleBot_smul, inflexibleCoe_smul]

@[simp]
theorem inflexibleCoe_smul_path {β : Λ} [LeLevel β]
    {A : ExtendedIndex β} {L : Litter} {ρ : Allowable β} (h : InflexibleCoe A L) :
    (h.smul ρ).path = h.path :=
  rfl

@[simp]
theorem inflexibleCoe_smul_t {β : Λ} [LeLevel β]
    {A : ExtendedIndex β} {L : Litter} {ρ : Allowable β} (h : InflexibleCoe A L) :
    (h.smul ρ).t = Allowable.comp (h.path.B.cons h.path.hδ) ρ • h.t :=
  rfl

@[simp]
theorem inflexibleBot_smul_path {β : Λ} [LeLevel β]
    {A : ExtendedIndex β} {L : Litter} {ρ : Allowable β} (h : InflexibleBot A L) :
    (h.smul ρ).path = h.path :=
  rfl

@[simp]
theorem inflexibleBot_smul_a {β : Λ} [LeLevel β]
    {A : ExtendedIndex β} {L : Litter} {ρ : Allowable β} (h : InflexibleBot A L) :
    (h.smul ρ).a = Allowable.comp (h.path.B.cons (bot_lt_coe _)) ρ • h.a :=
  rfl

end ConNF
