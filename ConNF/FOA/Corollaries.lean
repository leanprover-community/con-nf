import ConNF.FOA.Result
import ConNF.FOA.NLAction.StructNLAction

open Equiv Function Quiver Set Sum WithBot

open scoped Classical Pointwise symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [FOAAssumptions] {β : Λ} [LeLevel β]

-- TODO: Reverse equalities of BaseApprox.map_atom

namespace StructLAction

structure CoherentDom (ψ : StructLAction β) : Prop where
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

structure Coherent (ψ : StructLAction β) extends CoherentDom ψ : Prop where
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

def FOAMotive (ψ : StructLAction β) (ρ : Allowable β) : Address β → Prop
  | ⟨A, inl a⟩ => (ha : ((ψ A).atomMap a).Dom) →
      Allowable.toStructPerm ρ A • a = ((ψ A).atomMap a).get ha
  | ⟨A, inr N⟩ => N.IsLitter → (hL : ((ψ A).litterMap N.1).Dom) →
      Allowable.toStructPerm ρ A • N = ((ψ A).litterMap N.1).get hL

theorem foaMotive_atom (ψ : StructLAction β) (h₁ : ψ.Lawful)
    (ρ : Allowable β) (hρ : (ψ.toApprox h₁).ExactlyApproximates (Allowable.toStructPerm ρ))
    (A : ExtendedIndex β) (a : Atom)
    (ha : ((ψ A).atomMap a).Dom) :
    Allowable.toStructPerm ρ A • a = ((ψ A).atomMap a).get ha := by
  have := (hρ A).map_atom a ?_
  · rw [← this, toApprox_smul_atom_eq]
  · exact Or.inl (Or.inl (Or.inl (Or.inl ha)))

theorem foaMotive_litter (ψ : StructLAction β) (h₁ : ψ.Lawful) (h₂ : ψ.Coherent)
    (ρ : Allowable β) (hρ : (ψ.toApprox h₁).ExactlyApproximates (Allowable.toStructPerm ρ))
    (A : ExtendedIndex β) (L : Litter)
    (ih : ∀ (c : Address β), c < ⟨A, inr L.toNearLitter⟩ → FOAMotive ψ ρ c)
    (hL : ((ψ A).litterMap L).Dom) :
    Allowable.toStructPerm ρ A • L = (((ψ A).litterMap L).get hL).fst := by
  obtain (hL' | ⟨⟨⟨γ, ε, hε, A, rfl⟩, a, rfl⟩⟩ |
      ⟨⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t, rfl⟩⟩) := flexible_cases' A L
  · rw [← (hρ A).map_litter L (Or.inl (Or.inl ⟨hL, hL'⟩)), toApprox_smul_litter_eq,
      BaseLAction.flexibleLitterPartialPerm_apply_eq _ (by exact hL) hL',
      BaseLAction.roughLitterMapOrElse,
      BaseLAction.litterMapOrElse_of_dom]
    rfl
  · have := h₂.coherent_bot A hε hL (Allowable.comp A ρ) ?_
    · rw [this]
      simp only [Allowable.comp_comp_apply, Hom.comp_toPath, ofBot_smul,
        Allowable.toStructPerm_apply]
      rw [toStructPerm_smul_fuzz, comp_bot_smul_atom]
    · have := ih ⟨A.cons (bot_lt_coe _), inl a⟩
        (Relation.TransGen.single (Constrains.fuzzBot _ _ ⟨⟨γ, ε, hε, A, rfl⟩, a, rfl⟩))
        (h₂.atom_bot_dom A hε hL)
      simp only [Allowable.toStructPerm_comp, Tree.comp_apply, Hom.comp_toPath]
      exact this.symm
  · have := h₂.coherent_coe A hδ hε hδε hL (Allowable.comp A ρ) ?_ ?_ ?_
    · rw [this, Allowable.comp_comp_apply, Hom.comp_toPath, toStructPerm_smul_fuzz]
    · intro B a ha
      have := ih ⟨(A.cons hδ).comp B, inl a⟩
        (Relation.TransGen.single (Constrains.fuzz _ _
          ⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t, rfl⟩ _ ha))
        (h₂.atom_dom A hδ hε hδε ha hL)
      simp only [Allowable.toStructPerm_comp, Tree.comp_apply, Hom.comp_toPath_comp]
      exact this.symm
    · intro B N hN
      have := ih ⟨(A.cons hδ).comp B, inr N.1.toNearLitter⟩
        (lt_nearLitter' (Relation.TransGen.single (Constrains.fuzz _ _
          ⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t, rfl⟩ _ hN)))
        (NearLitter.IsLitter.mk _) (h₂.nearLitter_dom A hδ hε hδε (N := N) hN hL)
      simp only [Allowable.toStructPerm_comp, Tree.comp_apply, Hom.comp_toPath_comp]
      exact this.symm
    · intro B N a hN ha
      have := ih ⟨(A.cons hδ).comp B, inl a⟩
        ((Relation.TransGen.single (Constrains.symmDiff _ N a ha)).tail
          (Constrains.fuzz _ _
            ⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t, rfl⟩ _ hN))
        (h₂.symmDiff_dom A hδ hε hδε hN ha hL)
      simp only [Allowable.toStructPerm_comp, Tree.comp_apply, Hom.comp_toPath_comp]
      exact this.symm

theorem foaMotive_nearLitter (ψ : StructLAction β) (h₁ : ψ.Lawful) (h₂ : ψ.Coherent)
    (ρ : Allowable β) (hρ : (ψ.toApprox h₁).ExactlyApproximates (Allowable.toStructPerm ρ))
    (A : ExtendedIndex β) (L : Litter)
    (ih : ∀ (c : Address β), c < ⟨A, inr L.toNearLitter⟩ → FOAMotive ψ ρ c)
    (hL : ((ψ A).litterMap L).Dom) :
    Allowable.toStructPerm ρ A • L.toNearLitter = ((ψ A).litterMap L).get hL := by
  refine NearLitter.ext ?_
  rw [smul_nearLitter_eq_of_precise (ψ.refine h₁) refine_precise hρ
    (by exact hL) (foaMotive_litter ψ h₁ h₂ ρ hρ A L ih hL)]
  simp only [refine_apply, Litter.toNearLitter_fst, BaseLAction.refine_litterMap,
    Tree.comp_bot, Litter.coe_toNearLitter, symmDiff_self, bot_eq_empty, smul_set_empty,
    symmDiff_empty]

-- TODO: This isn't the Lean naming convention!
theorem freedom_of_action (ψ : StructLAction β) (h₁ : ψ.Lawful) (h₂ : ψ.Coherent) :
    ∃ ρ : Allowable β, ψ.Approximates (Allowable.toStructPerm ρ) := by
  obtain ⟨ρ, hρ⟩ := (ψ.toApprox h₁).freedom_of_action (toApprox_free _ _ h₂.mapFlexible)
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

end StructLAction

namespace StructNLAction

structure CoherentDom (ξ : StructNLAction β) : Prop where
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

structure Coherent (ξ : StructNLAction β) extends CoherentDom ξ : Prop where
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

noncomputable def _root_.ConNF.BaseNLAction.action
    (ξ : BaseNLAction) (hξ : ξ.Lawful) : BaseLAction where
  atomMap := (ξ.withLitters hξ).atomMap
  litterMap L := (ξ.withLitters hξ).nearLitterMap L.toNearLitter
  atomMap_dom_small := (ξ.withLitters hξ).atomMap_dom_small
  litterMap_dom_small :=
    (ξ.withLitters hξ).nearLitterMap_dom_small.image (f := fun N => N.1).mono
      (fun L hL => by exact ⟨L.toNearLitter, hL, rfl⟩)

noncomputable def action (ξ : StructNLAction β) (hξ : ξ.Lawful) : StructLAction β :=
  fun A => (ξ A).action (hξ A)

theorem _root_.ConNF.BaseNLAction.action_lawful
    (ξ : BaseNLAction) (hξ : ξ.Lawful) : (ξ.action hξ).Lawful := by
  constructor
  case atomMap_injective => exact (ξ.withLitters_lawful hξ).atomMap_injective
  case litterMap_injective =>
    rintro L₁ L₂ hL₁ hL₂ ⟨a, ha⟩
    by_contra hL
    obtain ⟨a, ha', rfl⟩ := (ξ.withLitters_lawful hξ).ran_of_mem_inter a (by exact hL) hL₁ hL₂ ha
    simp only [BaseNLAction.action, mem_inter_iff,
      SetLike.mem_coe, (ξ.withLitters_lawful hξ).atom_mem_iff] at ha
    exact hL (ha.1.symm.trans ha.2)
  case atom_mem =>
    intro a ha L hL
    exact ((ξ.withLitters_lawful hξ).atom_mem_iff ha hL).symm

theorem action_lawful (ξ : StructNLAction β) (hξ : ξ.Lawful) : (ξ.action hξ).Lawful :=
  fun A => (ξ A).action_lawful (hξ A)

@[simp]
theorem _root_.ConNF.BaseNLAction.action_atomMap
    (ξ : BaseNLAction) (hξ : ξ.Lawful) :
    (ξ.action hξ).atomMap = (ξ.withLitters hξ).atomMap :=
  rfl

@[simp]
theorem _root_.ConNF.BaseNLAction.action_litterMap
    (ξ : BaseNLAction) (hξ : ξ.Lawful) :
    (ξ.action hξ).litterMap = fun L => (ξ.withLitters hξ).nearLitterMap L.toNearLitter :=
  rfl

@[simp]
theorem action_atomMap (ξ : StructNLAction β) (hξ : ξ.Lawful) (A : ExtendedIndex β) :
    (ξ.action hξ A).atomMap = ((ξ A).withLitters (hξ A)).atomMap :=
  rfl

@[simp]
theorem action_litterMap (ξ : StructNLAction β) (hξ : ξ.Lawful) (A : ExtendedIndex β) :
    (ξ.action hξ A).litterMap = fun L => ((ξ A).withLitters (hξ A)).nearLitterMap L.toNearLitter :=
  rfl

theorem _root_.ConNF.BaseNLAction.action_approximates
    (ξ : BaseNLAction) (hξ : ξ.Lawful) (π : BasePerm)
    (h : (ξ.action hξ).Approximates π) : ξ.Approximates π := by
  constructor
  · intro a ha
    simp only [h.map_atom a (Or.inl ha), BaseNLAction.action_atomMap,
      BaseNLAction.withLitters, BaseNLAction.extraAtomMap_eq_of_dom a ha]
  · intro N hN
    refine NearLitter.ext ?_
    rw [BasePerm.smul_nearLitter_eq_smul_symmDiff_smul,
      h.map_litter _ (Or.inr ⟨⟨_⟩, N, hN, rfl⟩)]
    rw [← symmDiff_right_inj, symmDiff_symmDiff_cancel_left]
    ext a
    simp only [BaseNLAction.action_litterMap,
      BaseNLAction.withLitters_nearLitterMap_fst hξ hN, BaseNLAction.extraLitterMap,
      BaseNLAction.extraLitterMap', NearLitter.coe_mk, symmDiff_symmDiff_self', mem_iUnion,
      mem_singleton_iff]
    constructor <;>
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a, ha, ?_⟩
      dsimp only
      rw [h.map_atom]
      rfl

theorem action_approximates (ξ : StructNLAction β) (hξ : ξ.Lawful) (π : StructPerm β)
    (h : (ξ.action hξ).Approximates π) : ξ.Approximates π :=
  fun A => (ξ A).action_approximates (hξ A) (π A) (h A)

theorem _root_.ConNF.BaseNLAction.litterPresent_of_dom
    {ξ : BaseNLAction} (hξ : ξ.Lawful)
    {L : Litter} (h : ((ξ.withLitters hξ).nearLitterMap L.toNearLitter).Dom) :
    ξ.LitterPresent L := by
  obtain (hL | hL) := h
  · exact ⟨L.toNearLitter, hL, rfl⟩
  · exact hL.2

theorem _root_.ConNF.BaseNLAction.symmDiff {ξ : BaseNLAction} (hξ : ξ.Lawful)
    {N₁ N₂ : NearLitter} (h : N₁.1 = N₂.1)
    (hN₁ : (ξ.nearLitterMap N₁).Dom) (hN₂ : (ξ.nearLitterMap N₂).Dom) :
    ((ξ.nearLitterMap N₁).get hN₁ : Set Atom) ∆ (ξ.nearLitterMap N₂).get hN₂ =
    ⋃ (a : Atom) (ha : a ∈ (N₁ : Set Atom) ∆ N₂),
      {(ξ.atomMap a).get (hξ.dom_of_mem_symmDiff a h hN₁ hN₂ ha)} := by
  ext a
  simp only [mem_iUnion, mem_singleton_iff]
  constructor
  · intro ha
    obtain ⟨a, ha', rfl⟩ := hξ.ran_of_mem_symmDiff a h hN₁ hN₂ ha
    refine ⟨a, ?_, rfl⟩
    obtain (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩) := ha
    · rw [SetLike.mem_coe, hξ.atom_mem_iff] at ha₁ ha₂
      exact Or.inl ⟨ha₁, ha₂⟩
    · rw [SetLike.mem_coe, hξ.atom_mem_iff] at ha₁ ha₂
      exact Or.inr ⟨ha₁, ha₂⟩
  · rintro ⟨a, ha, rfl⟩
    obtain (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩) := ha
    · refine Or.inl ⟨?_, ?_⟩ <;> rw [SetLike.mem_coe, hξ.atom_mem_iff] <;> assumption
    · refine Or.inr ⟨?_, ?_⟩ <;> rw [SetLike.mem_coe, hξ.atom_mem_iff] <;> assumption

theorem action_coherentDom (ξ : StructNLAction β) (h₁ : ξ.Lawful) (h₂ : ξ.Coherent) :
    (ξ.action h₁).CoherentDom := by
  constructor
  case mapFlexible =>
    intro A L hL₁ hL₂
    obtain ⟨N, hN, rfl⟩ := (ξ A).litterPresent_of_dom (h₁ A) hL₁
    have := (BaseNLAction.map_nearLitter_fst (ξ.withLitters_lawful h₁ A)
      (Or.inl hN) (Or.inr ⟨⟨_⟩, N, hN, rfl⟩)).mp rfl
    erw [← this]
    simp only [withLitters, BaseNLAction.withLitters_nearLitterMap_of_dom _ hN]
    exact h₂.mapFlexible A N hN hL₂
  case atom_bot_dom =>
    intro γ _ A ε _ hε a ha
    obtain ⟨Nt, hNt₁, hNt₂⟩ := (ξ _).litterPresent_of_dom (h₁ _) ha
    exact Or.inl (h₂.atom_bot_dom A hε hNt₂ hNt₁)
  case atom_dom =>
    intro γ _ A δ _ ε _ hδ hε hδε t B a hc ht
    obtain ⟨Nt, hNt₁, hNt₂⟩ := (ξ _).litterPresent_of_dom (h₁ _) ht
    exact Or.inl (h₂.atom_dom A hδ hε hδε hNt₂ hc hNt₁)
  case nearLitter_dom =>
    intro γ _ A δ _ ε _ hδ hε hδε t B a hc ht
    obtain ⟨Nt, hNt₁, hNt₂⟩ := (ξ _).litterPresent_of_dom (h₁ _) ht
    exact Or.inr ⟨⟨_⟩, _, h₂.nearLitter_dom A hδ hε hδε hNt₂ hc hNt₁, rfl⟩
  case symmDiff_dom =>
    intro γ _ A δ _ ε _ hδ hε hδε t B N a hc ha ht
    obtain ⟨Nt, hNt₁, hNt₂⟩ := (ξ _).litterPresent_of_dom (h₁ _) ht
    simp only [action_atomMap, BaseNLAction.withLitters]
    have := h₂.nearLitter_dom A hδ hε hδε hNt₂ hc hNt₁
    exact BaseNLAction.extraAtomMap_dom_of_mem_symmDiff (h₁ _) this ha

theorem action_coherent (ξ : StructNLAction β) (h₁ : ξ.Lawful) (h₂ : ξ.Coherent) :
    (ξ.action h₁).Coherent := by
  constructor
  case toCoherentDom => exact action_coherentDom ξ h₁ h₂
  case coherent_coe =>
    intro γ _ A δ _ ε _ hδ hε hδε t ht ρ hta htN hts
    obtain ⟨Nt, hNt₁, hNt₂⟩ := (ξ _).litterPresent_of_dom (h₁ _) ht
    have := h₂.coherent_coe A hδ hε hδε hNt₂ hNt₁ ρ ?_ ?_
    · simp only [← this, action_litterMap, ← hNt₂,
        BaseNLAction.withLitters_nearLitterMap_fst _ hNt₁]
      rfl
    · intro B a ha
      simp only [← hta B a ha, action_atomMap, BaseNLAction.withLitters]
      rw [BaseNLAction.extraAtomMap_eq_of_dom]
    · intro B N hN
      refine NearLitter.ext ?_
      rw [BasePerm.smul_nearLitter_eq_smul_symmDiff_smul, ← htN B N hN,
        ← symmDiff_right_inj, symmDiff_symmDiff_cancel_left]
      have hN' := (action_coherentDom ξ h₁ h₂).nearLitter_dom A hδ hε hδε hN
        (Or.inr ⟨⟨_⟩, Nt, hNt₁, hNt₂⟩)
      have hN'' := h₂.nearLitter_dom A hδ hε hδε hNt₂ hN hNt₁
      refine Eq.trans ?_ ((BaseNLAction.symmDiff
          ((ξ _).withLitters_lawful (h₁ _)) (by exact rfl) hN' (Or.inl hN'')).trans ?_)
      · simp only [action_litterMap, symmDiff_right_inj, SetLike.coe_set_eq]
        rw [BaseNLAction.withLitters_nearLitterMap_of_dom]
      · ext a
        constructor
        · simp only [Litter.coe_toNearLitter, mem_iUnion, mem_singleton_iff, forall_exists_index]
          rintro a ha rfl
          refine ⟨a, ha, ?_⟩
          dsimp only
          rw [← hts _ N a hN ha]
          rfl
        · simp only [Litter.coe_toNearLitter, mem_iUnion, mem_singleton_iff]
          rintro ⟨a, ha, rfl⟩
          refine ⟨a, ha, ?_⟩
          dsimp only
          rw [← hts _ N a hN ha]
          rfl
  case coherent_bot =>
    intro γ _ A ε _ hδ a ha ρ hρa
    obtain ⟨Nt, hNt₁, hNt₂⟩ := (ξ _).litterPresent_of_dom (h₁ _) ha
    have := h₂.coherent_bot A hδ hNt₂ hNt₁ ρ ?_
    · simp only [← hNt₂, action_litterMap, ← this]
      rw [BaseNLAction.withLitters_nearLitterMap_fst]
      rfl
    · rw [← hρa]
      simp only [action_atomMap, BaseNLAction.withLitters]
      rw [BaseNLAction.extraAtomMap_eq_of_dom]

theorem freedom_of_action (ξ : StructNLAction β) (h₁ : ξ.Lawful) (h₂ : ξ.Coherent) :
    ∃ ρ : Allowable β, ξ.Approximates (Allowable.toStructPerm ρ) := by
  obtain ⟨ρ, hρ⟩ := (ξ.action h₁).freedom_of_action (ξ.action_lawful h₁) (ξ.action_coherent h₁ h₂)
  exact ⟨ρ, ξ.action_approximates h₁ _ hρ⟩

end StructNLAction

end ConNF
