import Mathlib.Order.Extension.Well
import ConNF.Mathlib.Support
import ConNF.FOA.Basic.Reduction
import ConNF.FOA.Basic.Flexible

/-!
# Strong supports
-/

open Quiver Set Sum WithBot

open scoped Classical Cardinal symmDiff

universe u

namespace ConNF

namespace Support

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

theorem strongSupport_strong {s : Set (Address β)} (hs : Small s) : (strongSupport hs).Strong := by
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

theorem Interferes.smul {a : Atom} {N₁ N₂ : NearLitter} (h : Interferes a N₁ N₂)
    (π : NearLitterPerm) : Interferes (π • a) (π • N₁) (π • N₂) := by
  cases h
  case symmDiff h₁ h₂ =>
    refine Interferes.symmDiff ?_ ?_
    · simp only [NearLitterPerm.smul_nearLitter_fst, smul_left_cancel_iff]
      exact h₁
    · obtain (h₂ | h₂) := h₂
      · refine Or.inl ?_
        rw [NearLitterPerm.smul_nearLitter_coe, NearLitterPerm.smul_nearLitter_coe,
          mem_diff, smul_mem_smul_set_iff, smul_mem_smul_set_iff]
        exact h₂
      · refine Or.inr ?_
        rw [NearLitterPerm.smul_nearLitter_coe, NearLitterPerm.smul_nearLitter_coe,
          mem_diff, smul_mem_smul_set_iff, smul_mem_smul_set_iff]
        exact h₂
  case inter h₁ h₂ =>
    refine Interferes.inter ?_ ?_
    · simp only [NearLitterPerm.smul_nearLitter_fst, ne_eq, smul_left_cancel_iff]
      exact h₁
    · rw [mem_inter_iff, NearLitterPerm.smul_nearLitter_coe, NearLitterPerm.smul_nearLitter_coe,
        smul_mem_smul_set_iff, smul_mem_smul_set_iff]
      exact h₂

theorem Precedes.smul [LeLevel β] {c d : Address β} (h : Precedes c d) (ρ : Allowable β) :
    Precedes (ρ • c) (ρ • d) := by
  cases h
  case fuzz A N h c hc =>
    have := Precedes.fuzz A (Allowable.toStructPerm ρ A • N) (h.smul ρ)
        (Allowable.comp (h.path.B.cons h.path.hδ) ρ • c) ?_
    · simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleCoe_smul_path,
        Allowable.smul_address, Allowable.toStructPerm_comp, Tree.comp_apply] at this
      simp only [Allowable.smul_address, smul_inr]
      rw [← h.path.hA] at this ⊢
      exact this
    · simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleCoe_smul_path, inflexibleCoe_smul_t,
        smul_support]
      change _ ∈ (_ : Set (Address h.path.δ))
      rw [Enumeration.smul_coe, smul_mem_smul_set_iff]
      exact hc
  case fuzzBot A N h =>
    have := Precedes.fuzzBot A (Allowable.toStructPerm ρ A • N) (h.smul ρ)
    simp only [Allowable.smul_address, smul_inl, smul_inr]
    simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleBot_smul_path, inflexibleBot_smul_a,
      ofBot_smul, Allowable.toStructPerm_apply] at this
    simp_rw [h.path.hA] at this ⊢
    exact this

theorem Strong.smul [LeLevel β] {S : Support β} (hS : S.Strong) (ρ : Allowable β) :
    (ρ • S).Strong := by
  constructor
  · intro i₁ i₂ hi₁ hi₂ A N₁ N₂ hN₁ hN₂ a ha
    have := ha.smul (Allowable.toStructPerm ρ A)⁻¹
    have := hS.interferes hi₁ hi₂
        (N₁ := (Allowable.toStructPerm ρ A)⁻¹ • N₁) (N₂ := (Allowable.toStructPerm ρ A)⁻¹ • N₂)
        ?_ ?_ (A := A) (a := (Allowable.toStructPerm ρ A)⁻¹ • a) this
    · obtain ⟨j, hj, hj₁, hj₂, h⟩ := this
      refine ⟨j, hj, hj₁, hj₂, ?_⟩
      rw [Enumeration.smul_f, h, Allowable.smul_address, smul_inl, smul_inv_smul]
    · rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at hN₁
      rw [hN₁, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr]
    · rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at hN₂
      rw [hN₂, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr]
  · intro i hi c hc
    have := hS.precedes hi (ρ⁻¹ • c) ?_
    · obtain ⟨j, hj, hj', hc⟩ := this
      refine ⟨j, hj, hj', ?_⟩
      rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul, hc]
    · have := hc.smul ρ⁻¹
      simp only [Enumeration.smul_f, inv_smul_smul] at this
      exact this

def before (S : Support β) (i : κ) (hi : i < S.max) : Support β :=
  ⟨i, fun j hj => S.f j (hj.trans hi)⟩

@[simp]
theorem before_carrier (S : Support β) (i : κ) (hi : i < S.max) :
    (S.before i hi).carrier = {c | ∃ j hj, j < i ∧ S.f j hj = c} := by
  ext c
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, _, hj, rfl⟩
  · rintro ⟨j, hj₁, hj₂, rfl⟩
    exact ⟨j, hj₂, rfl⟩

theorem before_strong (S : Support β) (i : κ) (hi : i < S.max) (hS : S.Strong) :
    (S.before i hi).Strong := by
  constructor
  · intro i₁ i₂ hi₁ hi₂ A N₁ N₂ hN₁ hN₂ a ha
    obtain ⟨j, hj, hj₁, hj₂, h⟩ := hS.interferes (hi₁.trans hi) (hi₂.trans hi) hN₁ hN₂ ha
    exact ⟨j, hj₁.trans hi₁, hj₁, hj₂, h⟩
  · intro j hj c hc
    obtain ⟨k, hk₁, hk₂, h⟩ := hS.precedes (hj.trans hi) c hc
    exact ⟨k, hk₂.trans hj, hk₂, h⟩

def CanComp {γ : Λ} (S : Support β) (A : Path (β : TypeIndex) γ) : Prop :=
  Set.Nonempty {i | ∃ hi, ∃ (c : Address γ), S.f i hi = ⟨A.comp c.1, c.2⟩}

noncomputable def leastCompIndex {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    (hS : S.CanComp A) : κ :=
  Params.κ_isWellOrder.wf.min {i | ∃ hi, ∃ (c : Address γ), S.f i hi = ⟨A.comp c.1, c.2⟩} hS

theorem leastCompIndex_mem {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    (hS : S.CanComp A) :
    leastCompIndex hS ∈ {i | ∃ hi, ∃ (c : Address γ), S.f i hi = ⟨A.comp c.1, c.2⟩} :=
  WellFounded.min_mem _ _ _

theorem not_lt_leastCompIndex {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    (hS : S.CanComp A) (i : κ) (hi : ∃ hi, ∃ (c : Address γ), S.f i hi = ⟨A.comp c.1, c.2⟩) :
    ¬i < leastCompIndex hS :=
  WellFounded.not_lt_min _ _ _ hi

noncomputable def compIndex {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    (hS : S.CanComp A) {i : κ} (hi : i < S.max) : κ :=
  if ∃ d : Address γ, S.f i hi = ⟨A.comp d.1, d.2⟩ then i else leastCompIndex hS

theorem compIndex_lt_max {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    (hS : S.CanComp A) {i : κ} (hi : i < S.max) :
    compIndex hS hi < S.max := by
  rw [compIndex]
  split_ifs
  · exact hi
  · exact (leastCompIndex_mem hS).choose

theorem compIndex_eq_comp {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    (hS : S.CanComp A) {i : κ} (hi : i < S.max) :
    ∃ d : Address γ, S.f (compIndex hS hi) (compIndex_lt_max hS hi) = ⟨A.comp d.1, d.2⟩ := by
  unfold compIndex
  split_ifs with h
  · exact h
  · exact (leastCompIndex_mem hS).choose_spec

theorem compIndex_eq_of_comp {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    (hS : S.CanComp A) {i : κ} (hi : i < S.max)
    {c : Address γ} (hc : S.f i hi = ⟨A.comp c.1, c.2⟩) :
    compIndex hS hi = i :=
  by rw [compIndex, if_pos ⟨c, hc⟩]

noncomputable def decomp {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    (hS : S.CanComp A) {i : κ} (hi : i < S.max) : Address γ :=
  (compIndex_eq_comp hS hi).choose

theorem decomp_spec {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    (hS : S.CanComp A) {i : κ} (hi : i < S.max) :
    S.f (compIndex hS hi) (compIndex_lt_max hS hi) =
      ⟨A.comp (decomp hS hi).1, (decomp hS hi).2⟩ :=
  (compIndex_eq_comp hS hi).choose_spec

open scoped Classical in
noncomputable def comp {γ : Λ} (S : Support β) (A : Path (β : TypeIndex) γ) : Support γ :=
  if hS : S.CanComp A then
    ⟨S.max, fun _ hi => decomp hS hi⟩
  else
    ⟨0, fun _ h => (κ_not_lt_zero _ h).elim⟩

theorem comp_eq_of_canComp {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ} (hS : S.CanComp A) :
    S.comp A = ⟨S.max, fun _ hi => decomp hS hi⟩ := by
  rw [comp, dif_pos]

theorem comp_max_eq_of_canComp {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    (hS : S.CanComp A) :
    (S.comp A).max = S.max := by
  rw [comp_eq_of_canComp hS]

theorem canComp_of_lt_comp_max {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    {i : κ} (hi : i < (S.comp A).max) : S.CanComp A := by
  rw [comp] at hi
  split_ifs at hi with hS
  · exact hS
  · cases κ_not_lt_zero _ hi

theorem lt_max_of_lt_comp_max {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    {i : κ} (hi : i < (S.comp A).max) : i < S.max := by
  rw [comp] at hi
  split_ifs at hi with hS
  · exact hi
  · cases κ_not_lt_zero _ hi

@[simp]
theorem comp_f_eq {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    {i : κ} (hi : i < (S.comp A).max) :
    (S.comp A).f i hi =
      decomp (canComp_of_lt_comp_max hi) (lt_max_of_lt_comp_max hi) := by
  unfold comp
  simp_rw [dif_pos (canComp_of_lt_comp_max hi)]

theorem comp_decomp_mem {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    (hS : S.CanComp A) {i : κ} (hi : i < S.max) :
    ⟨A.comp (decomp hS hi).1, (decomp hS hi).2⟩ ∈ S :=
  ⟨_, _, (decomp_spec hS hi).symm⟩

theorem comp_decomp_eq {γ : Λ} {S : Support β} {A : Path (β : TypeIndex) γ}
    (hS : S.CanComp A) {i : κ} (hi : i < S.max) {c : Address γ} (h : S.f i hi = ⟨A.comp c.1, c.2⟩) :
    decomp hS hi = c := by
  have hi' := compIndex_eq_of_comp hS hi h
  have := decomp_spec hS hi
  simp_rw [hi', h, Address.mk.injEq] at this
  refine Address.ext _ _ ?_ ?_
  · exact Path.comp_injective_right _ this.1.symm
  · exact this.2.symm

@[simp]
theorem comp_carrier {γ : Λ} (S : Support β) (A : Path (β : TypeIndex) γ) :
    (S.comp A).carrier = (fun c => ⟨A.comp c.1, c.2⟩) ⁻¹' S.carrier := by
  ext c
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [comp_f_eq]
    exact comp_decomp_mem _ _
  · rintro ⟨i, hi, hc⟩
    have hS : S.CanComp A := ⟨i, hi, c, hc.symm⟩
    rw [comp_eq_of_canComp hS]
    exact ⟨i, hi, (comp_decomp_eq hS hi hc.symm).symm⟩

theorem Precedes.comp {γ : Λ} {c d : Address γ} (h : Precedes c d) (A : Path (β : TypeIndex) γ) :
    Precedes ⟨A.comp c.1, c.2⟩ ⟨A.comp d.1, d.2⟩ := by
  cases h
  case fuzz B N h c hc =>
    have := Precedes.fuzz (A.comp B) N (h.comp A) c hc
    convert this using 2
    simp only [InflexibleCoe.comp_path, InflexibleCoePath.comp_δ, InflexibleCoePath.comp_γ,
      InflexibleCoePath.comp_B]
    rw [← Path.comp_assoc, Path.comp_cons]
  case fuzzBot B N h =>
    have := Precedes.fuzzBot (A.comp B) N (h.comp A)
    exact this

theorem comp_strong {γ : Λ} (S : Support β) (A : Path (β : TypeIndex) γ) (hS : S.Strong) :
    (S.comp A).Strong := by
  constructor
  · intro i₁ i₂ hi₁ hi₂ B N₁ N₂ hN₁ hN₂ a ha
    have hS' : S.CanComp A := canComp_of_lt_comp_max hi₁
    rw [comp_max_eq_of_canComp hS'] at hi₁ hi₂
    rw [comp_f_eq] at hN₁ hN₂
    have h₁ := decomp_spec hS' hi₁
    have h₂ := decomp_spec hS' hi₂
    rw [hN₁] at h₁
    rw [hN₂] at h₂
    obtain ⟨j, hj, hj₁, hj₂, h⟩ := hS.interferes _ _ h₁ h₂ ha
    refine ⟨j, ?_, ?_, ?_, ?_⟩
    · rw [comp_max_eq_of_canComp hS']
      exact hj
    · rw [compIndex] at hj₁
      split_ifs at hj₁ with hj'
      · exact hj₁
      · exact (not_lt_leastCompIndex hS' j ⟨hj, ⟨B, inl a⟩, h⟩ hj₁).elim
    · rw [compIndex] at hj₂
      split_ifs at hj₂ with hj'
      · exact hj₂
      · exact (not_lt_leastCompIndex hS' j ⟨hj, ⟨B, inl a⟩, h⟩ hj₂).elim
    · rw [comp_f_eq]
      exact comp_decomp_eq hS' hj h
  · intro i hi c hc
    have hS' : S.CanComp A := canComp_of_lt_comp_max hi
    rw [comp_max_eq_of_canComp hS'] at hi
    have h := decomp_spec hS' hi
    have := hS.precedes hi ⟨A.comp c.1, c.2⟩ ?_
    · obtain ⟨j, hj₁, hj₂, hj₃⟩ := this
      refine ⟨j, ?_, hj₂, ?_⟩
      · rw [comp_max_eq_of_canComp hS']
        exact hj₁
      · rw [comp_f_eq]
        exact comp_decomp_eq hS' hj₁ hj₃
    · have := hc.comp A
      rw [comp_f_eq, ← h] at this
      unfold compIndex at this
      split_ifs at this with h'
      · exact this
      · obtain ⟨j, hj₁, hj₂, hj₃⟩ := hS.precedes _ _ this
        exact (not_lt_leastCompIndex _ _ ⟨hj₁, c, hj₃⟩ hj₂).elim

end Support

end ConNF
