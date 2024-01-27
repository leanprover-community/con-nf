import ConNF.FOA.Result
import ConNF.FOA.Behaviour.StructBehaviour

open Equiv Function Quiver Set Sum WithBot

open scoped Classical Pointwise symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [LeLevel β]

-- TODO: Reverse equalities of NearLitterApprox.map_atom

-- TODO: Move this to a better place
@[mk_iff]
structure NearLitterAction.Approximates (ψ : NearLitterAction) (π : NearLitterPerm) : Prop where
  map_atom : ∀ a (h : (ψ.atomMap a).Dom), π • a = (ψ.atomMap a).get h
  map_litter : ∀ L (h : (ψ.litterMap L).Dom), π • L.toNearLitter = (ψ.litterMap L).get h

namespace StructAction

def Approximates (ψ : StructAction β) (π : StructPerm β) : Prop :=
  ∀ A, (ψ A).Approximates (π A)

structure Coherent (ψ : StructAction β) : Prop where
  mapFlexible : ψ.MapFlexible
  atom_bot_dom : ∀ {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ) {ε : Λ} [LtLevel ε]
    (hε : (ε : TypeIndex) < γ) {a : Atom},
    ((ψ ((A.cons hε).cons (bot_lt_coe _))).litterMap (fuzz (bot_ne_coe (a := ε)) a)).Dom →
    ((ψ (A.cons (bot_lt_coe _))).atomMap a).Dom
  atom_dom : ∀ {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ)
    {δ : Λ} [LtLevel δ] {ε : Λ} [LtLevel ε]
    (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : (δ : TypeIndex) ≠ ε) {t : Tangle δ}
    {B : ExtendedIndex δ} {a : Atom},
    ⟨B, inl a⟩ ∈ t.support →
    ((ψ ((A.cons hε).cons (bot_lt_coe _))).litterMap (fuzz hδε t)).Dom →
    ((ψ ((A.cons hδ).comp B)).atomMap a).Dom
  nearLitter_dom : ∀ {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ)
    {δ : Λ} [LtLevel δ] {ε : Λ} [LtLevel ε]
    (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : (δ : TypeIndex) ≠ ε) {t : Tangle δ}
    {B : ExtendedIndex δ} {N : NearLitter},
    ⟨B, inr N⟩ ∈ t.support →
    ((ψ ((A.cons hε).cons (bot_lt_coe _))).litterMap (fuzz hδε t)).Dom →
    ((ψ ((A.cons hδ).comp B)).litterMap N.fst).Dom
  symmDiff_dom : ∀ {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ)
    {δ : Λ} [LtLevel δ] {ε : Λ} [LtLevel ε]
    (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : (δ : TypeIndex) ≠ ε) {t : Tangle δ}
    {B : ExtendedIndex δ} {N : NearLitter} {a : Atom},
    ⟨B, inr N⟩ ∈ t.support → a ∈ litterSet N.1 ∆ N →
    ((ψ ((A.cons hε).cons (bot_lt_coe _))).litterMap (fuzz hδε t)).Dom →
    ((ψ ((A.cons hδ).comp B)).atomMap a).Dom
  coherent_coe : ∀ {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ)
    {δ : Λ} [LtLevel δ] {ε : Λ} [LtLevel ε]
    (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : (δ : TypeIndex) ≠ ε) {t : Tangle δ}
    (h : ((ψ ((A.cons hε).cons (bot_lt_coe _))).litterMap (fuzz hδε t)).Dom)
    (ρ : Allowable γ),
    (∀ (B : ExtendedIndex δ) (a : Atom) (ha : ⟨B, inl a⟩ ∈ t.support),
      ((ψ ((A.cons hδ).comp B)).atomMap a).get (atom_dom A hδ hε hδε ha h) =
      Allowable.toStructPerm ρ ((Hom.toPath hδ).comp B) • a) →
    (∀ (B : ExtendedIndex δ) (N : NearLitter) (ha : ⟨B, inr N⟩ ∈ t.support),
      ((ψ ((A.cons hδ).comp B)).litterMap N.1).get (nearLitter_dom A hδ hε hδε ha h) =
      Allowable.toStructPerm ρ ((Hom.toPath hδ).comp B) • N.1.toNearLitter) →
    (∀ (B : ExtendedIndex δ) (N : NearLitter) (a : Atom)
      (hN : ⟨B, inr N⟩ ∈ t.support) (ha : a ∈ litterSet N.1 ∆ N),
      ((ψ ((A.cons hδ).comp B)).atomMap a).get (symmDiff_dom A hδ hε hδε hN ha h) =
      Allowable.toStructPerm ρ ((Hom.toPath hδ).comp B) • a) →
    (((ψ ((A.cons hε).cons (bot_lt_coe _))).litterMap (fuzz hδε t)).get h).fst =
      fuzz hδε (Allowable.comp (Hom.toPath hδ) ρ • t)
  coherent_bot : ∀ {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ) {ε : Λ} [LtLevel ε]
    (hε : (ε : TypeIndex) < γ) {a : Atom}
    (h : ((ψ ((A.cons hε).cons (bot_lt_coe _))).litterMap (fuzz bot_ne_coe a)).Dom)
    (ρ : Allowable γ),
    ((ψ (A.cons (bot_lt_coe _))).atomMap a).get (atom_bot_dom A hε h) =
      Allowable.toStructPerm ρ (Hom.toPath (bot_lt_coe _)) • a →
    (((ψ ((A.cons hε).cons (bot_lt_coe _))).litterMap (fuzz bot_ne_coe a)).get h).fst =
      fuzz (bot_ne_coe (a := ε)) (Allowable.comp (Hom.toPath (bot_lt_coe _)) ρ • a)

def FOAMotive (ψ : StructAction β) (ρ : Allowable β) : SupportCondition β → Prop
  | ⟨A, inl a⟩ => (ha : ((ψ A).atomMap a).Dom) →
      Allowable.toStructPerm ρ A • a = ((ψ A).atomMap a).get ha
  | ⟨A, inr N⟩ => N.IsLitter → (hL : ((ψ A).litterMap N.1).Dom) →
      Allowable.toStructPerm ρ A • N = ((ψ A).litterMap N.1).get hL

theorem foaMotive_atom (ψ : StructAction β) (h₁ : ψ.Lawful)
    (ρ : Allowable β) (hρ : (ψ.rc h₁).ExactlyApproximates (Allowable.toStructPerm ρ))
    (A : ExtendedIndex β) (a : Atom)
    (ha : ((ψ A).atomMap a).Dom) :
    Allowable.toStructPerm ρ A • a = ((ψ A).atomMap a).get ha := by
  have := (hρ A).map_atom a ?_
  · rw [← this, rc_smul_atom_eq]
  · exact Or.inl (Or.inl (Or.inl (Or.inl ha)))

theorem foaMotive_litter (ψ : StructAction β) (h₁ : ψ.Lawful) (h₂ : ψ.Coherent)
    (ρ : Allowable β) (hρ : (ψ.rc h₁).ExactlyApproximates (Allowable.toStructPerm ρ))
    (A : ExtendedIndex β) (L : Litter)
    (ih : ∀ (c : SupportCondition β), c < ⟨A, inr L.toNearLitter⟩ → FOAMotive ψ ρ c)
    (hL : ((ψ A).litterMap L).Dom) :
    Allowable.toStructPerm ρ A • L = (((ψ A).litterMap L).get hL).fst := by
  obtain (hL' | ⟨⟨⟨γ, ε, hε, A, rfl⟩, a, rfl⟩⟩ |
      ⟨⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t, rfl⟩⟩) := flexible_cases' A L
  · rw [← (hρ A).map_litter L (Or.inl (Or.inl ⟨hL, hL'⟩)), rc_smul_litter_eq,
      NearLitterAction.flexibleLitterPartialPerm_apply_eq _ (by exact hL) hL',
      NearLitterAction.roughLitterMapOrElse,
      NearLitterAction.litterMapOrElse_of_dom]
    rfl
  · have := h₂.coherent_bot A hε hL (Allowable.comp A ρ) ?_
    · rw [this]
      simp only [Allowable.comp_comp_apply, Hom.comp_toPath, ofBot_smul,
        Allowable.toStructPerm_apply]
      rw [toStructPerm_smul_fuzz, comp_bot_smul_atom]
    · have := ih ⟨A.cons (bot_lt_coe _), inl a⟩
        (Relation.TransGen.single (Constrains.fuzz_bot hε A a))
        (h₂.atom_bot_dom A hε hL)
      simp only [Allowable.toStructPerm_comp, Tree.comp_apply, Hom.comp_toPath]
      exact this.symm
  · have := h₂.coherent_coe A hδ hε hδε hL (Allowable.comp A ρ) ?_ ?_ ?_
    · rw [this, Allowable.comp_comp_apply, Hom.comp_toPath, toStructPerm_smul_fuzz]
    · intro B a ha
      have := ih ⟨(A.cons hδ).comp B, inl a⟩
        (Relation.TransGen.single (Constrains.fuzz hδ hε hδε A t _ ha))
        (h₂.atom_dom A hδ hε hδε ha hL)
      simp only [Allowable.toStructPerm_comp, Tree.comp_apply, Hom.comp_toPath_comp]
      exact this.symm
    · intro B N hN
      have := ih ⟨(A.cons hδ).comp B, inr N.1.toNearLitter⟩
        (lt_nearLitter' (Relation.TransGen.single (Constrains.fuzz hδ hε hδε A t _ hN)))
        (NearLitter.IsLitter.mk _) (h₂.nearLitter_dom A hδ hε hδε (N := N) hN hL)
      simp only [Allowable.toStructPerm_comp, Tree.comp_apply, Hom.comp_toPath_comp]
      exact this.symm
    · intro B N a hN ha
      have := ih ⟨(A.cons hδ).comp B, inl a⟩
        ((Relation.TransGen.single (Constrains.symmDiff _ N a ha)).tail
          (Constrains.fuzz hδ hε hδε A t _ hN))
        (h₂.symmDiff_dom A hδ hε hδε hN ha hL)
      simp only [Allowable.toStructPerm_comp, Tree.comp_apply, Hom.comp_toPath_comp]
      exact this.symm

theorem foaMotive_nearLitter (ψ : StructAction β) (h₁ : ψ.Lawful) (h₂ : ψ.Coherent)
    (ρ : Allowable β) (hρ : (ψ.rc h₁).ExactlyApproximates (Allowable.toStructPerm ρ))
    (A : ExtendedIndex β) (L : Litter)
    (ih : ∀ (c : SupportCondition β), c < ⟨A, inr L.toNearLitter⟩ → FOAMotive ψ ρ c)
    (hL : ((ψ A).litterMap L).Dom) :
    Allowable.toStructPerm ρ A • L.toNearLitter = ((ψ A).litterMap L).get hL := by
  refine NearLitter.ext ?_
  rw [smul_nearLitter_eq_of_precise (ψ.refine h₁) refine_precise hρ
    (by exact hL) (foaMotive_litter ψ h₁ h₂ ρ hρ A L ih hL)]
  simp only [refine_apply, Litter.toNearLitter_fst, NearLitterAction.refine_litterMap,
    Tree.comp_bot, Litter.coe_toNearLitter, symmDiff_self, bot_eq_empty, smul_set_empty,
    symmDiff_empty]

-- TODO: This isn't the Lean naming convention!
theorem freedom_of_action (ψ : StructAction β) (h₁ : ψ.Lawful) (h₂ : ψ.Coherent) :
    ∃ ρ : Allowable β, ψ.Approximates (Allowable.toStructPerm ρ) := by
  obtain ⟨ρ, hρ⟩ := (ψ.rc h₁).freedom_of_action (rc_free _ _ h₂.mapFlexible)
  refine ⟨ρ, ?_⟩
  have := fun c => WellFounded.induction (constrains_wf _).transGen (C := FOAMotive ψ ρ) c ?_
  · intro A
    constructor
    · intro a ha
      exact this ⟨A, inl a⟩ ha
    · intro L hL
      exact this ⟨A, inr L.toNearLitter⟩ (NearLitter.IsLitter.mk L) hL
  · rintro ⟨A, a | N⟩ ih
    · exact foaMotive_atom ψ h₁ ρ hρ A a
    · intro hL h
      obtain ⟨L, rfl⟩ := hL.exists_litter_eq
      exact foaMotive_nearLitter ψ h₁ h₂ ρ hρ A L ih h

end StructAction

@[mk_iff]
structure NearLitterBehaviour.Approximates
    (ξ : NearLitterBehaviour) (π : NearLitterPerm) : Prop where
  map_atom : ∀ a (h : (ξ.atomMap a).Dom), π • a = (ξ.atomMap a).get h
  map_nearLitter : ∀ N (h : (ξ.nearLitterMap N).Dom), π • N = (ξ.nearLitterMap N).get h

namespace StructBehaviour

def Approximates (ξ : StructBehaviour β) (π : StructPerm β) : Prop :=
  ∀ A, (ξ A).Approximates (π A)

structure Coherent (ξ : StructBehaviour β) : Prop where
  mapFlexible : ∀ (A : ExtendedIndex β) (N : NearLitter) (hN : ((ξ A).nearLitterMap N).Dom),
    Flexible A N.1 → Flexible A (((ξ A).nearLitterMap N).get hN).1
  atom_bot_dom : ∀ {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ) {ε : Λ} [LtLevel ε]
    (hε : (ε : TypeIndex) < γ) {a : Atom} {Nt : NearLitter},
    Nt.1 = fuzz (bot_ne_coe (a := ε)) a →
    ((ξ ((A.cons hε).cons (bot_lt_coe _))).nearLitterMap Nt).Dom →
    ((ξ (A.cons (bot_lt_coe _))).atomMap a).Dom
  atom_dom : ∀ {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ)
    {δ : Λ} [LtLevel δ] {ε : Λ} [LtLevel ε]
    (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : (δ : TypeIndex) ≠ ε) {t : Tangle δ}
    {B : ExtendedIndex δ} {a : Atom} {Nt : NearLitter},
    Nt.1 = fuzz hδε t → ⟨B, inl a⟩ ∈ t.support →
    ((ξ ((A.cons hε).cons (bot_lt_coe _))).nearLitterMap Nt).Dom →
    ((ξ ((A.cons hδ).comp B)).atomMap a).Dom
  nearLitter_dom : ∀ {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ)
    {δ : Λ} [LtLevel δ] {ε : Λ} [LtLevel ε]
    (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : (δ : TypeIndex) ≠ ε) {t : Tangle δ}
    {B : ExtendedIndex δ} {N Nt : NearLitter},
    Nt.1 = fuzz hδε t → ⟨B, inr N⟩ ∈ t.support →
    ((ξ ((A.cons hε).cons (bot_lt_coe _))).nearLitterMap Nt).Dom →
    ((ξ ((A.cons hδ).comp B)).nearLitterMap N).Dom
  coherent_coe : ∀ {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ)
    {δ : Λ} [LtLevel δ] {ε : Λ} [LtLevel ε]
    (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : (δ : TypeIndex) ≠ ε) {t : Tangle δ}
    {Nt : NearLitter} (hNt : Nt.1 = fuzz hδε t)
    (h : ((ξ ((A.cons hε).cons (bot_lt_coe _))).nearLitterMap Nt).Dom)
    (ρ : Allowable γ),
    (∀ (B : ExtendedIndex δ) (a : Atom) (ha : ⟨B, inl a⟩ ∈ t.support),
      ((ξ ((A.cons hδ).comp B)).atomMap a).get (atom_dom A hδ hε hδε hNt ha h) =
      Allowable.toStructPerm ρ ((Hom.toPath hδ).comp B) • a) →
    (∀ (B : ExtendedIndex δ) (N : NearLitter) (ha : ⟨B, inr N⟩ ∈ t.support),
      ((ξ ((A.cons hδ).comp B)).nearLitterMap N).get (nearLitter_dom A hδ hε hδε hNt ha h) =
      Allowable.toStructPerm ρ ((Hom.toPath hδ).comp B) • N) →
    (((ξ ((A.cons hε).cons (bot_lt_coe _))).nearLitterMap Nt).get h).fst =
      fuzz hδε (Allowable.comp (Hom.toPath hδ) ρ • t)
  coherent_bot : ∀ {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ) {ε : Λ} [LtLevel ε]
    (hε : (ε : TypeIndex) < γ) {a : Atom} {Nt : NearLitter} (hNt : Nt.1 = fuzz bot_ne_coe a)
    (h : ((ξ ((A.cons hε).cons (bot_lt_coe _))).nearLitterMap Nt).Dom)
    (ρ : Allowable γ),
    ((ξ (A.cons (bot_lt_coe _))).atomMap a).get (atom_bot_dom A hε hNt h) =
      Allowable.toStructPerm ρ (Hom.toPath (bot_lt_coe _)) • a →
    (((ξ ((A.cons hε).cons (bot_lt_coe _))).nearLitterMap Nt).get h).fst =
      fuzz (bot_ne_coe (a := ε)) (Allowable.comp (Hom.toPath (bot_lt_coe _)) ρ • a)

noncomputable def _root_.ConNF.NearLitterBehaviour.action
    (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) : NearLitterAction where
  atomMap := (ξ.withLitters hξ).atomMap
  litterMap L := (ξ.withLitters hξ).nearLitterMap L.toNearLitter
  atomMap_dom_small := (ξ.withLitters hξ).atomMap_dom_small
  litterMap_dom_small :=
    (ξ.withLitters hξ).nearLitterMap_dom_small.image (f := fun N => N.1).mono
      (fun L hL => by exact ⟨L.toNearLitter, hL, rfl⟩)

noncomputable def action (ξ : StructBehaviour β) (hξ : ξ.Lawful) : StructAction β :=
  fun A => (ξ A).action (hξ A)

theorem _root_.ConNF.NearLitterBehaviour.action_lawful
    (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) : (ξ.action hξ).Lawful := by
  constructor
  case atomMap_injective => exact (ξ.withLitters_lawful hξ).atomMap_injective
  case litterMap_injective =>
    rintro L₁ L₂ hL₁ hL₂ ⟨a, ha⟩
    by_contra hL
    obtain ⟨a, ha', rfl⟩ := (ξ.withLitters_lawful hξ).ran_of_mem_inter a (by exact hL) hL₁ hL₂ ha
    simp only [NearLitterBehaviour.action, mem_inter_iff,
      SetLike.mem_coe, (ξ.withLitters_lawful hξ).atom_mem_iff] at ha
    exact hL (ha.1.symm.trans ha.2)
  case atom_mem =>
    intro a ha L hL
    exact ((ξ.withLitters_lawful hξ).atom_mem_iff ha hL).symm

theorem action_lawful (ξ : StructBehaviour β) (hξ : ξ.Lawful) : (ξ.action hξ).Lawful :=
  fun A => (ξ A).action_lawful (hξ A)

@[simp]
theorem _root_.ConNF.NearLitterBehaviour.action_atomMap
    (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) :
    (ξ.action hξ).atomMap = (ξ.withLitters hξ).atomMap :=
  rfl

@[simp]
theorem _root_.ConNF.NearLitterBehaviour.action_litterMap
    (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) :
    (ξ.action hξ).litterMap = fun L => (ξ.withLitters hξ).nearLitterMap L.toNearLitter :=
  rfl

@[simp]
theorem action_atomMap (ξ : StructBehaviour β) (hξ : ξ.Lawful) (A : ExtendedIndex β) :
    (ξ.action hξ A).atomMap = ((ξ A).withLitters (hξ A)).atomMap :=
  rfl

@[simp]
theorem action_litterMap (ξ : StructBehaviour β) (hξ : ξ.Lawful) (A : ExtendedIndex β) :
    (ξ.action hξ A).litterMap = fun L => ((ξ A).withLitters (hξ A)).nearLitterMap L.toNearLitter :=
  rfl

theorem _root_.ConNF.NearLitterBehaviour.action_approximates
    (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) (π : NearLitterPerm)
    (h : (ξ.action hξ).Approximates π) : ξ.Approximates π := by
  constructor
  · intro a ha
    simp only [h.map_atom a (Or.inl ha), NearLitterBehaviour.action_atomMap,
      NearLitterBehaviour.withLitters, NearLitterBehaviour.extraAtomMap_eq_of_dom a ha]
  · intro N hN
    refine NearLitter.ext ?_
    rw [NearLitterPerm.smul_nearLitter_eq_smul_symmDiff_smul,
      h.map_litter _ (Or.inr ⟨⟨_⟩, N, hN, rfl⟩)]
    rw [← symmDiff_right_inj, symmDiff_symmDiff_cancel_left]
    ext a
    simp only [NearLitterBehaviour.action_litterMap,
      NearLitterBehaviour.withLitters_nearLitterMap_fst hξ hN, NearLitterBehaviour.extraLitterMap,
      NearLitterBehaviour.extraLitterMap', NearLitter.coe_mk, symmDiff_symmDiff_self', mem_iUnion,
      mem_singleton_iff]
    constructor <;>
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a, ha, ?_⟩
      dsimp only
      rw [h.map_atom]
      rfl

theorem action_approximates (ξ : StructBehaviour β) (hξ : ξ.Lawful) (π : StructPerm β)
    (h : (ξ.action hξ).Approximates π) : ξ.Approximates π :=
  fun A => (ξ A).action_approximates (hξ A) (π A) (h A)

theorem action_coherent (ξ : StructBehaviour β) (h₁ : ξ.Lawful) (h₂ : ξ.Coherent) :
    (ξ.action h₁).Coherent := by
  constructor
  case mapFlexible => sorry
  case atom_bot_dom => sorry
  case atom_dom => sorry
  case nearLitter_dom => sorry
  case symmDiff_dom => sorry
  case coherent_coe => sorry
  case coherent_bot => sorry

theorem freedom_of_action (ξ : StructBehaviour β) (h₁ : ξ.Lawful) (h₂ : ξ.Coherent) :
    ∃ ρ : Allowable β, ξ.Approximates (Allowable.toStructPerm ρ) := by
  obtain ⟨ρ, hρ⟩ := (ξ.action h₁).freedom_of_action (ξ.action_lawful h₁) (ξ.action_coherent h₁ h₂)
  exact ⟨ρ, ξ.action_approximates h₁ _ hρ⟩

end StructBehaviour

end ConNF
