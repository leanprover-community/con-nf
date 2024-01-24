import ConNF.FOA.Result

open Equiv Function Quiver Set Sum WithBot

open scoped Classical Pointwise symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [LeLevel β]

-- TODO: reverse equalities of NearLitterApprox.map_atom

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

end ConNF
