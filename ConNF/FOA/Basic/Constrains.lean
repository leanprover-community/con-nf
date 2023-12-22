import Mathlib.Data.Prod.Lex
import ConNF.Fuzz
import ConNF.FOA.Basic.Hypotheses

/-!
# Constraints
Support conditions can be said to *constrain* each other in a number of ways.
This is detailed below. The `constrains` relation is well-founded.

## Main declarations
* `ConNF.Constrains`: The constrains relation.
* `ConNF.constrains_wf`: The constrains relation is well-founded.
* `ConNF.small_constrains`: Only a small amount of things are constrained by a particular support
    condition.
-/

open Quiver Set Sum WithBot

open scoped Cardinal Classical

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ}

/-- Support conditions can be said to *constrain* each other in a number of ways.
1. `(L, A) ≺ (a, A)` when `a ∈ L` and `L` is a litter. We can say that an atom is constrained by the
    litter it belongs to.
2. `(N°, A) ≺ (N, A)` when `N` is a near-litter not equal to its corresponding litter `N°`.
3. `(a, A) ≺ (N, A)` for all `a ∈ N ∆ N°`.
4. `(x, A ≫ (γ ⟶ δ) ≫ B) ≺ (f_{γ,δ}(t), A ≫ (γ ⟶ ε) ≫ (ε ⟶ ⊥))` for all paths `A : β ⟶ γ` and
    `δ, ε < γ` with `δ ≠ ε`, `t ∈ τ_γ`, where `(x, B)` lies in the designated `δ`-support of `t`.
-/
@[mk_iff]
inductive Constrains : SupportCondition β → SupportCondition β → Prop
  | atom (A : ExtendedIndex β) (a : Atom) : Constrains ⟨A, inr a.1.toNearLitter⟩ ⟨A, inl a⟩
  | nearLitter (A : ExtendedIndex β) (N : NearLitter) (hN : ¬N.IsLitter) :
    Constrains ⟨A, inr N.fst.toNearLitter⟩ ⟨A, inr N⟩
  | symmDiff (A : ExtendedIndex β) (N : NearLitter) (a : Atom) :
    a ∈ litterSet N.fst ∆ N → Constrains ⟨A, inl a⟩ ⟨A, inr N⟩
  | fuzz ⦃γ : Λ⦄ [LeLevel γ] ⦃δ : Λ⦄ [LtLevel δ] ⦃ε : Λ⦄ [LtLevel ε]
    (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : (δ : TypeIndex) ≠ ε)
    (A : Path (β : TypeIndex) γ) (t : Tangle δ) (c : SupportCondition δ) :
    c ∈ t.support →
    Constrains ⟨(A.cons hδ).comp c.path, c.value⟩
      ⟨(A.cons hε).cons (bot_lt_coe _), inr (fuzz hδε t).toNearLitter⟩
  | fuzz_bot ⦃γ : Λ⦄ [LeLevel γ] ⦃ε : Λ⦄ [LtLevel ε]
    (hε : (ε : TypeIndex) < γ) (A : Path (β : TypeIndex) γ) (a : Atom) :
    Constrains ⟨A.cons (bot_lt_coe _), inl a⟩
      ⟨(A.cons hε).cons (bot_lt_coe _), inr (fuzz (bot_ne_coe (a := ε)) a).toNearLitter⟩

/-! We declare new notation for the "constrains" relation on support conditions. -/

@[inherit_doc] infix:50 " ≺ " => Constrains

inductive LitterConstrains : Litter → Litter → Prop
  | fuzz_atom ⦃δ : Λ⦄ [LtLevel δ] ⦃ε : Λ⦄ [LtLevel ε] (hδε : (δ : TypeIndex) ≠ ε)
    (t : Tangle δ) {B : ExtendedIndex δ} {a : Atom} : ⟨B, inl a⟩ ∈ t.support →
    LitterConstrains a.1 (fuzz hδε t)
  | fuzz_nearLitter ⦃δ : Λ⦄ [LtLevel δ] ⦃ε : Λ⦄ [LtLevel ε] (hδε : (δ : TypeIndex) ≠ ε)
    (t : Tangle δ) {B : ExtendedIndex δ} {N : NearLitter} (h : ⟨B, inr N⟩ ∈ t.support)
    {a : Atom} (ha : a ∈ N) :
    LitterConstrains a.1 (fuzz hδε t)
  | fuzz_bot ⦃ε : Λ⦄ [LtLevel ε] (a : Atom) :
    LitterConstrains a.1 (fuzz (bot_ne_coe (a := ε)) a)

@[mk_iff]
inductive HasPosition : Litter → μ → Prop
  | fuzz ⦃δ : Λ⦄ [LtLevel δ] ⦃ε : Λ⦄ [LtLevel ε] (hδε : (δ : TypeIndex) ≠ ε) (t : Tangle δ) :
    HasPosition (fuzz hδε t) (pos t)
  | fuzz_bot ⦃ε : Λ⦄ [LtLevel ε] (a : Atom) :
    HasPosition (fuzz (bot_ne_coe (a := ε)) a) (pos a)

theorem hasPosition_subsingleton {L : Litter} {ν₁ ν₂ : μ}
    (h₁ : HasPosition L ν₁) (h₂ : HasPosition L ν₂) : ν₁ = ν₂ := by
  rw [HasPosition_iff] at h₁ h₂
  cases h₁ with
  | inl h₁ =>
      obtain ⟨δ, _, ε, _, hδε, t, rfl, rfl⟩ := h₁
      cases h₂ with
      | inl h₂ =>
          obtain ⟨_, _, _, _, _, t, ht, rfl⟩ := h₂
          cases fuzz_congr_β ht
          cases fuzz_congr_γ ht
          cases fuzz_injective _ ht
          rfl
      | inr h₂ =>
          obtain ⟨_, _, a, ha, rfl⟩ := h₂
          cases fuzz_congr_β ha
  | inr h₁ =>
      obtain ⟨_, _, a, rfl, rfl⟩ := h₁
      cases h₂ with
      | inl h₂ =>
          obtain ⟨_, _, _, _, _, t, ht, rfl⟩ := h₂
          cases fuzz_congr_β ht
      | inr h₂ =>
          obtain ⟨_, _, a, ha, rfl⟩ := h₂
          cases fuzz_congr_γ ha
          cases fuzz_injective _ ha
          rfl

theorem hasPosition_of_litterConstrains {L₁ L₂ : Litter} (h : LitterConstrains L₁ L₂) :
    ∃ ν, HasPosition L₂ ν := by
  cases h
  · exact ⟨_, HasPosition.fuzz _ _⟩
  · exact ⟨_, HasPosition.fuzz _ _⟩
  · exact ⟨_, HasPosition.fuzz_bot _⟩

theorem hasPosition_lt_of_litterConstrains {L₁ L₂ : Litter} (h : LitterConstrains L₁ L₂)
    {ν₁ ν₂ : μ} (h₁ : HasPosition L₁ ν₁) (h₂ : HasPosition L₂ ν₂) :
    ν₁ < ν₂ := by
  rw [HasPosition_iff] at h₁ h₂
  cases h with
  | fuzz_atom hδε t ht =>
      cases h₂ with
      | inr h =>
          obtain ⟨_, _, _, h, rfl⟩ := h
          cases fuzz_congr_β h
      | inl h =>
          obtain ⟨δ, _, ε, _, _, t', ht', rfl⟩ := h
          cases fuzz_congr_β ht'
          cases fuzz_congr_γ ht'
          cases fuzz_injective _ ht'
          cases h₁ with
          | inl h =>
              obtain ⟨δ, _, ε, _, hδε, t', ht', rfl⟩ := h
              exact pos_lt_pos_atom t ht t' hδε ht'
          | inr h =>
              obtain ⟨ε, _, a, h, rfl⟩ := h
              exact pos_lt_pos_atom t ht (show Tangle ⊥ from a) bot_ne_coe h
  | fuzz_nearLitter hδε t ht ha =>
      cases h₂ with
      | inr h =>
          obtain ⟨_, _, _, h, rfl⟩ := h
          cases fuzz_congr_β h
      | inl h =>
          obtain ⟨δ, _, ε, _, _, t', ht', rfl⟩ := h
          cases fuzz_congr_β ht'
          cases fuzz_congr_γ ht'
          cases fuzz_injective _ ht'
          cases h₁ with
          | inl h =>
              obtain ⟨δ, _, ε, _, hδε, t', ht', rfl⟩ := h
              exact pos_lt_pos_nearLitter t ht t' hδε ⟨_, ha, ht'⟩
          | inr h =>
              obtain ⟨ε, _, a, h, rfl⟩ := h
              exact pos_lt_pos_nearLitter t ht (show Tangle ⊥ from a) bot_ne_coe ⟨_, ha, h⟩
  | fuzz_bot a =>
      cases h₂ with
      | inl h =>
          obtain ⟨_, _, _, _, _, _, h, rfl⟩ := h
          cases fuzz_congr_β h
      | inr h =>
          obtain ⟨ε, _, a, ha, rfl⟩ := h
          cases fuzz_congr_γ ha
          cases fuzz_injective _ ha
          cases h₁ with
          | inl h =>
              obtain ⟨δ, _, ε, _, hδε, t', ht', rfl⟩ := h
              exact pos_lt_pos_fuzz _ t' a ht'
          | inr h =>
              obtain ⟨ε, _, a', ha', rfl⟩ := h
              exact pos_lt_pos_fuzz _ (show Tangle ⊥ from a') a ha'

open scoped Classical in
noncomputable def positionOrBot (L : Litter) : WithBot μ :=
  if h : ∃ ν, HasPosition L ν then h.choose else ⊥

theorem litterConstrains_subrelation :
    Subrelation LitterConstrains (InvImage (· < ·) positionOrBot) := by
  intro L₁ L₂ h
  obtain ⟨ν₂, hν₂⟩ := hasPosition_of_litterConstrains h
  by_cases h₁ : ∃ ν₁, HasPosition L₁ ν₁
  · obtain ⟨ν₁, hν₁⟩ := h₁
    rw [InvImage, positionOrBot, positionOrBot, dif_pos ⟨ν₁, hν₁⟩, dif_pos ⟨ν₂, hν₂⟩,
      hasPosition_subsingleton (Exists.choose_spec ⟨ν₁, hν₁⟩) hν₁,
      hasPosition_subsingleton (Exists.choose_spec ⟨ν₂, hν₂⟩) hν₂]
    exact WithBot.coe_lt_coe.mpr (hasPosition_lt_of_litterConstrains h hν₁ hν₂)
  · rw [InvImage, positionOrBot, positionOrBot, dif_neg h₁, dif_pos ⟨ν₂, hν₂⟩]
    exact bot_lt_coe _

theorem litterConstrains_wf : WellFounded LitterConstrains :=
  Subrelation.wf litterConstrains_subrelation IsWellFounded.wf

@[simp]
theorem constrains_atom {c : SupportCondition β} {A : ExtendedIndex β} {a : Atom} :
    c ≺ ⟨A, inl a⟩ ↔ c = ⟨A, inr a.1.toNearLitter⟩ := by
  constructor
  · rintro ⟨⟩
    rfl
  · rintro rfl
    exact Constrains.atom A a

theorem constrains_nearLitter {c : SupportCondition β} {A : ExtendedIndex β}
    {N : NearLitter} (hN : ¬N.IsLitter) :
    c ≺ ⟨A, inr N⟩ ↔ c = ⟨A, inr N.1.toNearLitter⟩ ∨
      ∃ a ∈ litterSet N.fst ∆ N.snd, c = ⟨A, inl a⟩ := by
  constructor
  · intro h
    rw [Constrains_iff] at h
    obtain ⟨A, a, rfl, hc⟩ | ⟨A, N, hN, rfl, hc⟩ | ⟨A, N, a, ha, rfl, hc⟩ |
        ⟨γ, _, δ, _, ε, _, hδ, hε, hδε, A, t, c, _, rfl, hc'⟩ |
        ⟨γ, _, ε, _, hγ, A, a, rfl, hc⟩ := h
    · cases hc
    · cases hc
      exact Or.inl rfl
    · cases hc
      exact Or.inr ⟨a, ha, rfl⟩
    · cases hc'
      cases hN (NearLitter.IsLitter.mk _)
    · cases hc
      cases hN (NearLitter.IsLitter.mk _)
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact Constrains.nearLitter A N hN
    · exact Constrains.symmDiff A N a ha

theorem acc_atom {a : Atom} {A : ExtendedIndex β}
    (h : Acc ((· ≺ ·) : SupportCondition β → _ → Prop) ⟨A, inr a.1.toNearLitter⟩) :
    Acc ((· ≺ ·) : SupportCondition β → _ → Prop) ⟨A, inl a⟩ := by
  constructor
  intro c
  rw [constrains_atom]
  rintro rfl
  exact h

theorem acc_nearLitter {N : NearLitter} {A : ExtendedIndex β}
    (h : ∀ a ∈ N, Acc ((· ≺ ·) : SupportCondition β → _ → Prop) ⟨A, inr a.1.toNearLitter⟩) :
    Acc ((· ≺ ·) : SupportCondition β → _ → Prop) ⟨A, inr N⟩ := by
  by_cases hN : N.IsLitter
  · obtain ⟨L, rfl⟩ := hN.exists_litter_eq
    obtain ⟨⟨a, rfl⟩⟩ := litterSet_nonempty L
    exact h _ rfl
  constructor
  intro d hd
  rw [constrains_nearLitter hN] at hd
  obtain (rfl | ⟨a, ha, rfl⟩) := hd
  · obtain ⟨a, ha⟩ := NearLitter.inter_nonempty_of_fst_eq_fst (N₁ := N) (N₂ := N.1.toNearLitter) rfl
    have := h a ha.1
    rw [ha.2] at this
    exact this
  · refine acc_atom ?_
    obtain (ha | ha) := ha
    · obtain ⟨b, hb⟩ := NearLitter.inter_nonempty_of_fst_eq_fst (N₁ := N) (N₂ := N.1.toNearLitter) rfl
      have := h b hb.1
      rw [hb.2, ← ha.1] at this
      exact this
    · exact h a ha.1

/-- The `≺` relation is well-founded. -/
theorem constrains_wf (β : Λ) : WellFounded ((· ≺ ·) : SupportCondition β → _ → Prop) := by
  have : ∀ L : Litter, ∀ A : ExtendedIndex β,
      Acc ((· ≺ ·) : SupportCondition β → _ → Prop) ⟨A, inr L.toNearLitter⟩
  · intro L
    refine litterConstrains_wf.induction
      (C := fun L => ∀ A : ExtendedIndex β, Acc (· ≺ ·) ⟨A, inr L.toNearLitter⟩) L ?_
    clear L
    intro L ih A
    constructor
    intro c hc
    rw [Constrains_iff] at hc
    obtain ⟨A, a, rfl, hc⟩ | ⟨A, N, hN, rfl, hc⟩ | ⟨A, N, a, ha, rfl, hc⟩ |
        ⟨γ, _, δ, _, ε, _, hδ, hε, hδε, A, t, c, hc, rfl, hc'⟩ |
        ⟨γ, _, ε, _, hγ, A, a, rfl, hc⟩ := hc
    · cases hc
    · cases hc
      cases hN (NearLitter.IsLitter.mk _)
    · cases hc
      cases ha with
      | inl ha => cases ha.2 ha.1
      | inr ha => cases ha.2 ha.1
    · simp only [SupportCondition.mk.injEq, inr.injEq, Litter.toNearLitter_injective.eq_iff] at hc'
      cases hc'.1
      cases hc'.2
      obtain ⟨B, a | N⟩ := c
      · exact acc_atom (ih a.1 (LitterConstrains.fuzz_atom _ _ hc) _)
      · refine acc_nearLitter ?_
        intro a ha
        exact ih _ (LitterConstrains.fuzz_nearLitter hδε t hc ha) _
    · simp only [SupportCondition.mk.injEq, inr.injEq, Litter.toNearLitter_injective.eq_iff] at hc
      cases hc.1
      cases hc.2
      refine acc_atom (ih _ (LitterConstrains.fuzz_bot _) _)
  constructor
  intro c
  obtain ⟨B, a | N⟩ := c
  · exact acc_atom (this _ _)
  · exact acc_nearLitter (fun _ _ => this _ _)

/-- The constrains relation is stable under composition of paths. -/
theorem constrains_comp {β γ : Λ} {c d : SupportCondition γ} (h : c ≺ d)
    (B : Path (β : TypeIndex) γ) : ⟨B.comp c.path, c.value⟩ ≺ ⟨B.comp d.path, d.value⟩ := by
  obtain ⟨A, a⟩ | ⟨A, N, hN⟩ | ⟨A, N, a, ha⟩ | ⟨hδ, hε, hδε, A, t, c, hc⟩ | ⟨hδ, A, a⟩ := h
  · exact Constrains.atom _ _
  · exact Constrains.nearLitter _ _ hN
  · exact Constrains.symmDiff _ _ _ ha
  · rw [Path.comp_cons, ← Path.comp_assoc, Path.comp_cons]
    exact Constrains.fuzz hδ hε hδε (B.comp A) t c hc
  · rw [Path.comp_cons]
    exact Constrains.fuzz_bot hδ (B.comp A) a

instance : PartialOrder (SupportCondition β) where
  le := Relation.ReflTransGen (· ≺ ·)
  lt := Relation.TransGen (· ≺ ·)
  le_refl := fun _ => Relation.ReflTransGen.refl
  le_trans := fun _ _ _ => Relation.ReflTransGen.trans
  lt_iff_le_not_le := by
    intro c d
    constructor
    · intro h
      exact ⟨h.to_reflTransGen,
        fun h' => (constrains_wf β).transGen.isIrrefl.irrefl d (h.trans_right h')⟩
    · intro h
      obtain (rfl | h') := Relation.reflTransGen_iff_eq_or_transGen.mp h.1
      · cases h.2 Relation.ReflTransGen.refl
      · exact h'
  le_antisymm := by
    intro c d h₁ h₂
    obtain (h₁ | h₁) := Relation.reflTransGen_iff_eq_or_transGen.mp h₁
    · exact h₁.symm
    obtain (h₂ | h₂) := Relation.reflTransGen_iff_eq_or_transGen.mp h₂
    · exact h₂
    cases (constrains_wf β).transGen.isIrrefl.irrefl c (h₁.trans h₂)

instance : WellFoundedLT (SupportCondition β) where
  wf := (constrains_wf β).transGen

instance : WellFoundedRelation (SupportCondition β) :=
  ⟨(· < ·), (constrains_wf β).transGen⟩

theorem SupportCondition.le_iff {c d : SupportCondition β} :
    c ≤ d ↔ Relation.ReflTransGen (· ≺ ·) c d :=
  Iff.rfl

theorem SupportCondition.lt_iff {c d : SupportCondition β} :
    c < d ↔ Relation.TransGen (· ≺ ·) c d :=
  Iff.rfl

theorem le_comp {β γ : Λ} {c d : SupportCondition γ} (h : c ≤ d)
    (B : Path (β : TypeIndex) γ) :
    (⟨B.comp c.path, c.value⟩ : SupportCondition β) ≤ ⟨B.comp d.path, d.value⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact Relation.ReflTransGen.tail ih (constrains_comp h B)

theorem lt_comp {β γ : Λ} {c d : SupportCondition γ} (h : c < d)
    (B : Path (β : TypeIndex) γ) :
    (⟨B.comp c.path, c.value⟩ : SupportCondition β) < ⟨B.comp d.path, d.value⟩ := by
  induction h with
  | single h => exact Relation.TransGen.single (constrains_comp h B)
  | tail _ h ih => exact Relation.TransGen.tail ih (constrains_comp h B)

theorem le_nearLitter {β : Λ} {N : NearLitter} {B : ExtendedIndex β}
    {c : SupportCondition β} (h : ⟨B, inr N⟩ ≤ c) : ⟨B, inr N.1.toNearLitter⟩ ≤ c := by
  by_cases h' : N.IsLitter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.ReflTransGen.head (Constrains.nearLitter B N h') h

theorem lt_nearLitter {β : Λ} {N : NearLitter} {B : ExtendedIndex β}
    {c : SupportCondition β} (h : c < ⟨B, inr N.1.toNearLitter⟩) : c < ⟨B, inr N⟩ := by
  by_cases h' : N.IsLitter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.TransGen.tail h (Constrains.nearLitter B N h')

theorem lt_nearLitter' {β : Λ} {N : NearLitter} {B : ExtendedIndex β}
    {c : SupportCondition β} (h : ⟨B, inr N⟩ < c) : ⟨B, inr N.1.toNearLitter⟩ < c := by
  by_cases h' : N.IsLitter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.TransGen.head (Constrains.nearLitter B N h') h

theorem small_constrains {β : Λ} (c : SupportCondition β) : Small {d | d ≺ c} := by
  obtain ⟨A, a | N⟩ := c
  · simp only [constrains_atom, setOf_eq_eq_singleton, small_singleton]
  simp_rw [Constrains_iff]
  refine Small.union ?_ (Small.union ?_ (Small.union ?_ (Small.union ?_ ?_))) <;>
    rw [small_setOf]
  · change Small {c | ∃ b B, _ ∧ _ = _}
    simp only [SupportCondition.mk.injEq, false_and, and_false, exists_false,
      setOf_false, small_empty]
  · change Small {c | ∃ B N', _}
    refine Set.Subsingleton.small ?_
    rintro c ⟨_, _, _, ⟨rfl, rfl⟩, h₁⟩ d ⟨_, _, _, ⟨rfl, rfl⟩, h₂⟩
    cases h₁
    cases h₂
    rfl
  · change Small {c | ∃ B N' a, _}
    convert (show Small (litterSet N.fst ∆ N) from N.2.prop).image
      (f := fun a : Atom => (⟨A, inl a⟩ : SupportCondition β)) using 1
    ext c : 1
    simp only [mem_setOf_eq, mem_image]
    constructor
    · rintro ⟨B, N', a, h₁, h₂, h₃⟩
      cases h₃
      exact ⟨a, h₁, h₂.symm⟩
    · rintro ⟨a, h₁, h₂⟩
      exact ⟨A, N, a, h₁, h₂.symm, rfl⟩
  · by_cases h :
      ∃ (γ : Λ) (_ : LeLevel γ) (δ : Λ) (_ : LtLevel δ) (ε : Λ) (_ : LtLevel ε)
        (_ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : (δ : TypeIndex) ≠ ε)
        (B : Path (β : TypeIndex) γ) (t : Tangle δ),
        N = (fuzz hδε t).toNearLitter ∧ A = (B.cons hε).cons (bot_lt_coe _)
    · obtain ⟨γ, _, δ, _, ε, _, hδ, hε, hδε, B, t, rfl, rfl⟩ := h
      refine lt_of_le_of_lt ?_ t.support.small
      suffices
        #{a : SupportCondition β | ∃ c : (t.support : Set (SupportCondition δ)),
            a = ⟨(B.cons hδ).comp c.val.path, c.val.value⟩} ≤
          #(t.support : Set (SupportCondition δ)) by
        refine le_trans (Cardinal.mk_subtype_le_of_subset ?_) this
        rintro x ⟨_, _, _, _, _, _, _, _, _, _, _, c, hc, rfl, h⟩
        rw [SupportCondition.mk.injEq] at h
        simp only [inr.injEq, Litter.toNearLitter_injective.eq_iff] at h
        cases WithBot.coe_injective (fuzz_congr_β h.2)
        cases fuzz_congr_γ h.2
        cases fuzz_injective _ h.2
        cases coe_inj.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons h.1).eq)
        cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons h.1).eq).eq
        exact ⟨⟨c, hc⟩, rfl⟩
      refine ⟨⟨fun a => a.prop.choose, ?_⟩⟩
      intro a b h
      refine Subtype.coe_inj.mp ?_
      rw [a.prop.choose_spec, b.prop.choose_spec]
      simp only [h]
    · refine small_of_forall_not_mem ?_
      rintro x ⟨γ, _, δ, _, ε, _, hδ, hε, hδε, B, t, c, _, rfl, hA⟩
      rw [SupportCondition.mk.injEq] at hA
      simp only [inr.injEq] at hA
      exact h ⟨γ, inferInstance, δ, inferInstance, ε, inferInstance, hδ, hε, hδε, B, t, hA.2, hA.1⟩
  · refine Set.Subsingleton.small ?_
    rintro ⟨c, C⟩ ⟨γ, _, ε, _, hε, C', a, hc₁, hc₂⟩ ⟨d, D⟩ ⟨γ, _, ε, _, hε, D', b, hd₁, hd₂⟩
    rw [SupportCondition.mk.injEq] at hc₁ hc₂ hd₁ hd₂
    simp only [inr.injEq] at hc₂ hd₂
    rw [hc₁.1, hc₁.2, hd₁.1, hd₁.2]
    rw [hc₂.1, hc₂.2, Litter.toNearLitter_injective.eq_iff] at hd₂
    cases coe_inj.mp (Path.obj_eq_of_cons_eq_cons hd₂.1)
    cases coe_inj.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hd₂.1).eq)
    cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hd₂.1).eq).eq
    rw [(fuzz_injective bot_ne_coe).eq_iff] at hd₂
    cases hd₂.2
    rfl

end ConNF
