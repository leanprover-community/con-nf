import Mathlib.Order.Extension.Well
import ConNF.Mathlib.Support
import ConNF.FOA.Basic.Reduction
import ConNF.FOA.Basic.Flexible
import ConNF.Counting.CodingFunction

/-!
# Strong supports
-/

open Quiver Set Sum WithBot

open scoped Classical Cardinal symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ}

@[mk_iff]
inductive Interferes (a : Atom) (N₁ N₂ : NearLitter) : Prop
  | symmDiff : N₁.1 = N₂.1 → a ∈ (N₁ : Set Atom) ∆ N₂ → Interferes a N₁ N₂
  | inter : N₁.1 ≠ N₂.1 → a ∈ (N₁ : Set Atom) ∩ N₂ → Interferes a N₁ N₂

@[mk_iff]
inductive Precedes : Address β → Address β → Prop
  | fuzz (A : ExtendedIndex β) (N : NearLitter) (h : InflexibleCoe A N.1) (c : Address h.path.δ) :
    c ∈ h.t.support →
    Precedes ⟨(h.path.B.cons h.path.hδ).comp c.path, c.value⟩
      ⟨(h.path.B.cons h.path.hε).cons (bot_lt_coe _), inr N⟩
  | fuzzBot (A : ExtendedIndex β) (N : NearLitter) (h : InflexibleBot A N.1) :
    Precedes ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩
      ⟨(h.path.B.cons h.path.hε).cons (bot_lt_coe _), inr N⟩

@[mk_iff]
structure Strong (S : Support β) : Prop where
  interferes {i₁ i₂ : κ} (hi₁ : i₁ < S.max) (hi₂ : i₂ < S.max)
    {A : ExtendedIndex β} {N₁ N₂ : NearLitter}
    (h₁ : S.f i₁ hi₁ = ⟨A, inr N₁⟩) (h₂ : S.f i₂ hi₂ = ⟨A, inr N₂⟩)
    {a : Atom} (ha : Interferes a N₁ N₂) :
    ∃ (j : κ) (hj : j < S.max), j < i₁ ∧ j < i₂ ∧ S.f j hj = ⟨A, inl a⟩
  precedes {i : κ} (hi : i < S.max) (c : Address β) (hc : Precedes c (S.f i hi)) :
    ∃ (j : κ) (hj : j < S.max), j < i ∧ S.f j hj = c

theorem interferes_small (N₁ N₂ : NearLitter) :
    Small {a | Interferes a N₁ N₂} := by
  simp only [interferes_iff]
  by_cases h : N₁.1 = N₂.1
  · simp only [h, true_and, ne_eq, not_true_eq_false, mem_inter_iff, SetLike.mem_coe, false_and,
      or_false, setOf_mem_eq]
    have := N₁.2.2
    simp_rw [h] at this
    exact this.symm.trans N₂.2.2
  · simp only [h, false_and, ne_eq, not_false_eq_true, mem_inter_iff, SetLike.mem_coe, true_and,
      false_or]
    exact NearLitter.inter_small_of_fst_ne_fst h

theorem Precedes.lt {c d : Address β} :
    Precedes c d → c < d := by
  intro h
  cases h
  case fuzz A N h c hct =>
    refine lt_nearLitter (Relation.TransGen.single ?_)
    simp_rw [h.hL]
    exact Constrains.fuzz h.path.hδ h.path.hε h.path.hδε _ _ _ hct
  case fuzzBot A N h =>
    refine lt_nearLitter (Relation.TransGen.single ?_)
    simp_rw [h.hL]
    exact Constrains.fuzz_bot h.path.hε _ _

theorem Precedes.wellFounded : WellFounded (Precedes : Address β → Address β → Prop) := by
  have : Subrelation Precedes ((· < ·) : Address β → Address β → Prop) := Precedes.lt
  exact (this.isWellFounded).wf

def precClosure (s : Set (Address β)) : Set (Address β) :=
  {c | ∃ d ∈ s, Relation.ReflTransGen Precedes c d}

theorem precClosure_small {s : Set (Address β)} (h : Small s) :
    Small (precClosure s) := by
  refine (_root_.ConNF.reflTransClosure_small h).mono ?_
  rintro c ⟨d, hd, h⟩
  have := h.mono (fun _ _ => Precedes.lt)
  erw [Relation.reflTransGen_transGen] at this
  exact ⟨d, hd, this⟩

def strongClosure (s : Set (Address β)) : Set (Address β) :=
  {c | ∃ A a N₁ N₂, ⟨A, inr N₁⟩ ∈ precClosure s ∧ ⟨A, inr N₂⟩ ∈ precClosure s ∧
    Interferes a N₁ N₂ ∧ c = ⟨A, inl a⟩} ∪
  precClosure s

theorem interferesSet_eq (s : Set (Address β)) :
    {c : Address β | ∃ A a N₁ N₂, ⟨A, inr N₁⟩ ∈ precClosure s ∧ ⟨A, inr N₂⟩ ∈ precClosure s ∧
      Interferes a N₁ N₂ ∧ c = ⟨A, inl a⟩} =
    ⋃ (A : ExtendedIndex β),
    ⋃ (N₁ : NearLitter) (_ : ⟨A, inr N₁⟩ ∈ precClosure s),
    ⋃ (N₂ : NearLitter) (_ : ⟨A, inr N₂⟩ ∈ precClosure s),
    ⋃ (a : Atom) (_ : Interferes a N₁ N₂),
    {⟨A, inl a⟩} := by aesop

theorem strongClosure_small {s : Set (Address β)} (h : Small s) :
    Small (strongClosure s) := by
  refine Small.union ?_ (precClosure_small h)
  rw [interferesSet_eq]
  refine small_iUnion ((mk_extendedIndex β).trans_lt Params.Λ_lt_κ) ?_
  intro A
  refine Small.bUnion ?_ ?_
  · refine Small.image_subset (fun N => ⟨A, inr N⟩) ?_ (precClosure_small h) ?_
    · intro N N' h
      cases h
      rfl
    · rintro _ ⟨N, hN, rfl⟩
      exact hN
  intro N₁ _
  refine Small.bUnion ?_ ?_
  · refine Small.image_subset (fun N => ⟨A, inr N⟩) ?_ (precClosure_small h) ?_
    · intro N N' h
      cases h
      rfl
    · rintro _ ⟨N, hN, rfl⟩
      exact hN
  intro N₂ _
  refine Small.bUnion (interferes_small N₁ N₂) ?_
  intro a _
  exact small_singleton _

theorem subset_strongClosure (s : Set (Address β)) : s ⊆ strongClosure s :=
  fun c hc => Or.inr ⟨c, hc, Relation.ReflTransGen.refl⟩

theorem interferes_mem_strongClosure (s : Set (Address β)) (A : ExtendedIndex β) (a : Atom)
    (N₁ N₂ : NearLitter) (h : Interferes a N₁ N₂)
    (hN₁ : ⟨A, inr N₁⟩ ∈ strongClosure s) (hN₂ : ⟨A, inr N₂⟩ ∈ strongClosure s) :
    ⟨A, inl a⟩ ∈ strongClosure s := by
  obtain (⟨_, _, _, _, _, _, _, h⟩ | hN₁) := hN₁
  · cases h
  obtain (⟨_, _, _, _, _, _, _, h⟩ | hN₂) := hN₂
  · cases h
  exact Or.inl ⟨A, a, N₁, N₂, hN₁, hN₂, h, rfl⟩

theorem precedes_mem_strongClosure (s : Set (Address β)) {c d : Address β}
    (hcd : Precedes c d) (hd : d ∈ strongClosure s) : c ∈ strongClosure s := by
  obtain (⟨_, _, _, _, _, _, _, rfl⟩ | ⟨e, he, hd⟩) := hd
  · cases hcd
  · exact Or.inr ⟨e, he, Relation.ReflTransGen.head hcd hd⟩

inductive StrongSupportRel : Address β → Address β → Prop
  | atom (A B : ExtendedIndex β) (a : Atom) (N : NearLitter) :
      StrongSupportRel ⟨A, inl a⟩ ⟨B, inr N⟩
  | precedes (c d : Address β) : Precedes c d → StrongSupportRel c d

theorem StrongSupportRel.wellFounded :
    WellFounded (StrongSupportRel : Address β → Address β → Prop) := by
  constructor
  intro c
  refine Precedes.wellFounded.induction c ?_
  intro c ih
  constructor
  intro d hd
  cases hd
  case atom A B a N =>
    constructor
    intro d hd
    cases hd
    case precedes d h => cases h
  case precedes c d h => exact ih d h

/-- An arbitrary well-order on the type of β-addresses, formed in such a way that whenever
`c` must appear before `d` in a support, `c < d`. -/
noncomputable def StrongSupportOrder : Address β → Address β → Prop :=
  StrongSupportRel.wellFounded.wellOrderExtension.lt

noncomputable def StrongSupportOrderOn (s : Set (Address β)) : s → s → Prop :=
  fun c d => StrongSupportOrder c.val d.val

instance : IsWellOrder (Address β) StrongSupportOrder := by
  unfold StrongSupportOrder
  exact ⟨⟩

instance (s : Set (Address β)) : IsWellOrder s (StrongSupportOrderOn s) :=
  RelEmbedding.isWellOrder (Subtype.relEmbedding _ _)

noncomputable def indexMax {s : Set (Address β)} (hs : Small s) : κ :=
  Ordinal.enum (· < ·) (Ordinal.type (StrongSupportOrderOn s))
    (by
      refine lt_of_not_le (fun h => ?_)
      have := Ordinal.card_le_card h
      simp only [Ordinal.card_type] at this
      cases this.not_lt hs)

theorem of_lt_indexMax {s : Set (Address β)} (hs : Small s) {i : κ} (hi : i < indexMax hs) :
    Ordinal.typein (α := κ) (· < ·) i < Ordinal.type (StrongSupportOrderOn s) := by
  rw [indexMax, ← Ordinal.typein_lt_typein (· < ·), Ordinal.typein_enum] at hi
  exact hi

noncomputable def indexed {s : Set (Address β)} (hs : Small s) (i : κ) (hi : i < indexMax hs) :
    Address β :=
  (Ordinal.enum (StrongSupportOrderOn s)
    (Ordinal.typein (α := κ) (· < ·) i) (of_lt_indexMax hs hi)).val

/-- A strong support containing `s`. -/
noncomputable def strongSupport {s : Set (Address β)} (hs : Small s) : Support β :=
  ⟨indexMax (strongClosure_small hs), indexed (strongClosure_small hs)⟩

@[simp]
theorem strongSupport_f {s : Set (Address β)} (hs : Small s)
    {i : κ} (hi : i < indexMax (strongClosure_small hs)) :
    (strongSupport hs).f i hi = indexed (strongClosure_small hs) i hi := rfl

theorem strongSupport_index_lt_iff {s : Set (Address β)} (hs : Small s) {i j : κ}
    (hi : i < indexMax (strongClosure_small hs)) (hj : j < indexMax (strongClosure_small hs)) :
    StrongSupportOrder ((strongSupport hs).f i hi) ((strongSupport hs).f j hj) ↔ i < j := by
  rw [← Ordinal.typein_lt_typein (· < ·),
    ← Ordinal.enum_lt_enum (r := StrongSupportOrderOn (strongClosure s))]
  rfl

theorem lt_of_strongSupportRel {s : Set (Address β)} (hs : Small s) {i j : κ}
    (hi : i < indexMax (strongClosure_small hs)) (hj : j < indexMax (strongClosure_small hs))
    (h : StrongSupportRel ((strongSupport hs).f i hi) ((strongSupport hs).f j hj)) : i < j := by
  rw [← strongSupport_index_lt_iff hs hi hj]
  exact Prod.Lex.left _ _ (WellFounded.rank_lt_of_rel _ h)

theorem mem_of_strongSupport_f_eq {s : Set (Address β)} (hs : Small s)
    {i : κ} (hi : i < indexMax (strongClosure_small hs)) :
    (strongSupport hs).f i hi ∈ strongClosure s :=
  Subtype.coe_prop _

theorem exists_of_mem_strongClosure {s : Set (Address β)} (hs : Small s)
    (c : Address β) (hc : c ∈ strongClosure s) :
    ∃ (j : κ) (hj : j < indexMax (strongClosure_small hs)), (strongSupport hs).f j hj = c := by
  refine ⟨Ordinal.enum (α := κ) (· < ·)
    (Ordinal.typein (StrongSupportOrderOn (strongClosure s)) ⟨c, hc⟩) ?_,
      ?_, ?_⟩
  · refine lt_of_not_le (fun h => ?_)
    have := Ordinal.card_le_card h
    simp only [Ordinal.card_type] at this
    have := this.trans
      (Ordinal.card_le_card (Ordinal.typein_lt_type (StrongSupportOrderOn _) ⟨c, hc⟩).le)
    cases this.not_lt (strongClosure_small hs)
  · rw [indexMax, Ordinal.enum_lt_enum (r := (· < ·))]
    exact Ordinal.typein_lt_type _ _
  · simp only [strongSupport_f, indexed, Ordinal.typein_enum, Ordinal.enum_typein]

theorem subset_strongSupport {s : Set (Address β)} (hs : Small s) : s ⊆ strongSupport hs := by
  intro c hc
  obtain ⟨j, hj, hc⟩ := exists_of_mem_strongClosure hs c (subset_strongClosure s hc)
  exact ⟨j, hj, hc.symm⟩

theorem strongSupport_strong {s : Set (Address β)} (hs : Small s) : Strong (strongSupport hs) := by
  constructor
  · intro i₁ i₂ hi₁ hi₂ A N₁ N₂ hN₁ hN₂ a ha
    have hi₁' := mem_of_strongSupport_f_eq hs hi₁
    have hi₂' := mem_of_strongSupport_f_eq hs hi₂
    rw [hN₁] at hi₁'
    rw [hN₂] at hi₂'
    have := interferes_mem_strongClosure s A a N₁ N₂ ha hi₁' hi₂'
    obtain ⟨j, hj, hc⟩ := exists_of_mem_strongClosure _ _ this
    refine ⟨j, hj, ?_, ?_, hc⟩
    · refine lt_of_strongSupportRel hs hj hi₁ ?_
      rw [hc, hN₁]
      exact StrongSupportRel.atom _ _ _ _
    · refine lt_of_strongSupportRel hs hj hi₂ ?_
      rw [hc, hN₂]
      exact StrongSupportRel.atom _ _ _ _
  · intro i hi c hc
    have hi' := mem_of_strongSupport_f_eq hs hi
    have := precedes_mem_strongClosure s hc hi'
    obtain ⟨j, hj, hc'⟩ := exists_of_mem_strongClosure _ _ this
    refine ⟨j, hj, ?_, hc'⟩
    refine lt_of_strongSupportRel hs hj hi ?_
    rw [hc']
    exact StrongSupportRel.precedes _ _ hc

end ConNF
