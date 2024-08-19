import ConNF.FOA.Properties.Injective

open Equiv Function Quiver Set Sum WithBot

open scoped Classical Pointwise symmDiff

universe u

namespace ConNF

namespace StructApprox

variable [Params.{u}] [Level] [BasePositions] [FOAAssumptions] {β : Λ} [LeLevel β]
  [FreedomOfActionHypothesis β] {π : StructApprox β}

theorem completeNearLitterMap_subset_range (A : ExtendedIndex β) (L : Litter) :
    (π.completeNearLitterMap A L.toNearLitter : Set Atom) ⊆ range (π.completeAtomMap A) := by
  rw [completeNearLitterMap_toNearLitter_eq]
  rintro a (⟨ha₁, ha₂⟩ | ⟨a, ⟨_, ha₂⟩, rfl⟩)
  · refine' ⟨(((π A).largestSublitter L).equiv ((π A).largestSublitter a.1)).symm
      ⟨a, (π A).mem_largestSublitter_of_not_mem_domain a ha₂⟩, _⟩
    rw [completeAtomMap_eq_of_not_mem_domain]
    swap
    · exact BaseApprox.not_mem_domain_of_mem_largestSublitter _
        (Sublitter.equiv_symm_apply_mem ⟨a, _⟩)
    · rw [mem_litterSet] at ha₁
      have : ((((π A).largestSublitter L).equiv
        ((π A).largestSublitter a.fst)).symm ⟨a, rfl, ha₂⟩ : Atom).fst =
          L :=
        Sublitter.equiv_symm_apply_fst_eq ⟨a, _⟩
      rw [Sublitter.equiv_congr_left (congr_arg _ this),
        Sublitter.equiv_congr_right (congr_arg _ (congr_arg _ this)),
        Sublitter.equiv_congr_right (congr_arg _ ha₁.symm)]
      simp only [SetLike.eta, Equiv.apply_symm_apply]
  · refine' ⟨a, _⟩
    rw [completeAtomMap_eq_of_mem_domain ha₂]

theorem completeAtomMap_surjective_extends (A : ExtendedIndex β) (a : Atom)
    (h : a.1 ∈ range (π.completeLitterMap A)) : a ∈ range (π.completeAtomMap A) := by
  obtain ⟨L, hL⟩ := h
  by_cases ha : a ∈ (π A).atomPerm.domain
  · refine' ⟨(π A).atomPerm.symm a, _⟩
    rw [completeAtomMap_eq_of_mem_domain ((π A).atomPerm.symm.map_domain ha)]
    exact (π A).atomPerm.right_inv ha
  · have := completeNearLitterMap_toNearLitter_eq (π := π) A L
    rw [hL] at this
    have := Eq.subset this.symm (Or.inl ⟨rfl, ha⟩)
    exact completeNearLitterMap_subset_range A L this

noncomputable def completeAddressMap (π : StructApprox β) :
    Address β → Address β
  | ⟨B, inl a⟩ => ⟨B, inl (π.completeAtomMap B a)⟩
  | ⟨B, inr N⟩ => ⟨B, inr (π.completeNearLitterMap B N)⟩

@[simp]
theorem completeAddressMap_atom_eq {π : StructApprox β} {a : Atom} {B : ExtendedIndex β} :
    π.completeAddressMap ⟨B, inl a⟩ = ⟨B, inl (π.completeAtomMap B a)⟩ :=
  rfl

@[simp]
theorem completeAddressMap_nearLitter_eq {π : StructApprox β} {N : NearLitter}
    {B : ExtendedIndex β} :
    π.completeAddressMap ⟨B, inr N⟩ = ⟨B, inr (π.completeNearLitterMap B N)⟩ :=
  rfl

theorem completeAddressMap_injective (hπf : π.Free) :
    Injective π.completeAddressMap := by
  rintro ⟨B₁, a₁ | N₁⟩ ⟨B₂, a₂ | N₂⟩ h <;>
    rw [Address.ext_iff] at h <;>
    simp only [completeAddressMap_atom_eq,
      completeAddressMap_nearLitter_eq,
      inl.injEq, inr.injEq, and_false] at h
  · cases h.1
    cases completeAtomMap_injective hπf B₁ h.2
    rfl
  · cases h.1
    cases completeNearLitterMap_injective hπf B₁ h.2
    rfl

def preimageConstrained (π : StructApprox β) (c : Address β) : Set (Address β) :=
  π.completeAddressMap ⁻¹' {d | d ≺ c}

theorem preimageConstrained_small (hπf : π.Free) (c : Address β) :
    Small (preimageConstrained π c) :=
  Small.preimage (completeAddressMap_injective hπf) (small_constrains c)

noncomputable def preimageAction (hπf : π.Free) (c : Address β) : StructLAction β :=
  constrainedAction π (preimageConstrained π c) (preimageConstrained_small hπf c)

theorem preimageAction_eq_constrainedAction (hπf : π.Free) (c : Address β) :
    preimageAction hπf c =
      constrainedAction π (preimageConstrained π c) (preimageConstrained_small hπf c) :=
  rfl

-- In fact, any `constrained_action` is lawful.
theorem preimageAction_lawful (hπf : π.Free) {c : Address β} :
    (preimageAction hπf c).Lawful := by
  intro A
  constructor
  · intro a b ha hb hab
    exact completeAtomMap_injective hπf A hab
  · intro L₁ L₂ hL₁ hL₂ hL
    exact completeLitterMap_injective hπf A (eq_of_completeLitterMap_inter_nonempty hL)
  · intro a _ L _
    exact (completeAtomMap_mem_completeNearLitterMap_toNearLitter hπf).symm

theorem preimageAction_comp_mapFlexible {hπf : π.Free} {γ : Λ} {c : Address β}
    (A : Path (β : TypeIndex) γ) :
    StructLAction.MapFlexible ((preimageAction hπf c).comp A) :=
  constrainedAction_comp_mapFlexible hπf A

theorem Relation.reflTransGen_of_eq {α : Type _} {r : α → α → Prop} {x y : α} (h : x = y) :
    Relation.ReflTransGen r x y := by
  cases h
  rfl

theorem preimageAction_coherent (hπf : π.Free) {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (N : NearLitter) (c : Address β)
    (hc : ⟨A.comp B, inr (π.completeNearLitterMap (A.comp B) N)⟩ ≺ c) (ρ : Allowable γ)
    (h : StructApprox.ExactlyApproximates
      (StructLAction.toApprox ((preimageAction hπf c).comp A) ((preimageAction_lawful hπf).comp _))
      (Allowable.toStructPerm ρ)) :
    completeNearLitterMap π (A.comp B) N =
    Tree.comp B (Allowable.toStructPerm ρ) • N := by
  refine' constrainedAction_coherent hπf A B N _ _ _
    ((preimageAction_lawful hπf).comp _) ρ h
  refine' ⟨_, _, Relation.ReflTransGen.refl⟩
  exact hc

theorem preimageAction_coherent_atom (hπf : π.Free) {γ : Λ} [LeLevel γ] (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (a : Atom) (c : Address β)
    (hc : ⟨A.comp B, inl (π.completeAtomMap (A.comp B) a)⟩ ≺ c) (ρ : Allowable γ)
    (h : StructApprox.ExactlyApproximates
      (StructLAction.toApprox ((preimageAction hπf c).comp A) ((preimageAction_lawful hπf).comp _))
      (Allowable.toStructPerm ρ)) :
    completeAtomMap π (A.comp B) a = Tree.comp B (Allowable.toStructPerm ρ) • a := by
  refine' constrainedAction_coherent_atom A B a _ _ _ _ ρ h
  refine' ⟨_, _, Relation.ReflTransGen.refl⟩
  exact hc

theorem completeLitterMap_surjective_extends (hπf : π.Free) (A : ExtendedIndex β) (L : Litter)
    (ha : ∀ (B : ExtendedIndex β) (a : Atom),
      ⟨B, inl a⟩ ≺ ⟨A, inr L.toNearLitter⟩ → a ∈ range (π.completeAtomMap B))
    (hN : ∀ (B : ExtendedIndex β) (N : NearLitter),
      ⟨B, inr N⟩ ≺ ⟨A, inr L.toNearLitter⟩ → N ∈ range (π.completeNearLitterMap B)) :
    L ∈ range (π.completeLitterMap A) := by
  obtain h | ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩ := flexible_cases' A L
  · refine' ⟨(BaseApprox.flexibleCompletion (π A) A).symm • L, _⟩
    rw [completeLitterMap_eq_of_flexible, BaseApprox.right_inv_litter]
    · rw [BaseApprox.flexibleCompletion_litterPerm_domain_free (π A) A (hπf A)]
      exact h
    · exact BaseApprox.flexibleCompletion_symm_smul_flexible (π A) A (hπf A) L h
  · obtain ⟨⟨γ, ε, hε, C, rfl⟩, a, rfl⟩ := h
    obtain ⟨b, h'⟩ := ha _ a (Constrains.fuzzBot _ _ ⟨⟨γ, ε, hε, C, rfl⟩, a, rfl⟩)
    rw [← h']
    refine' ⟨fuzz (show ⊥ ≠ (ε : TypeIndex) from bot_ne_coe) b, _⟩
    rw [completeLitterMap_eq_of_inflexibleBot ⟨⟨γ, ε, hε, C, rfl⟩, b, rfl⟩]
  · obtain ⟨⟨γ, δ, ε, hδ, hε, hδε, B, rfl⟩, t, rfl⟩ := h
    refine' ⟨fuzz hδε
      (((preimageAction hπf
            ⟨(B.cons hε).cons (bot_lt_coe _),
              inr (fuzz hδε t).toNearLitter⟩).hypothesisedAllowable
          ⟨γ, δ, ε, hδ, hε, hδε, B, rfl⟩
          ((preimageAction_lawful hπf).comp _) (preimageAction_comp_mapFlexible _))⁻¹ • t), _⟩
    rw [completeLitterMap_eq_of_inflexibleCoe ⟨⟨γ, δ, ε, hδ, hε, hδε, B, rfl⟩, _, rfl⟩
        ((ihAction_lawful hπf _).comp _) (ihAction_comp_mapFlexible hπf _ _)]
    refine' congr_arg _ _
    dsimp only
    rw [smul_eq_iff_eq_inv_smul]
    refine supports (t := t) ?_ ?_
    · intros A a hc
      have hac := Constrains.fuzz _ _ ⟨⟨γ, δ, ε, hδ, hε, hδε, B, rfl⟩, t, rfl⟩ _ hc
      specialize ha _ a hac
      obtain ⟨b, ha⟩ := ha
      have : (Tree.comp A
        (Allowable.toStructPerm ((preimageAction hπf
            ⟨(B.cons hε).cons (bot_lt_coe _),
              inr (fuzz hδε t).toNearLitter⟩).hypothesisedAllowable
              ⟨γ, δ, ε, hδ, hε, hδε, B, rfl⟩ ((preimageAction_lawful hπf).comp _)
              (preimageAction_comp_mapFlexible _))))⁻¹ • a = b
      · rw [inv_smul_eq_iff, ← ha]
        rw [StructLAction.hypothesisedAllowable]
        refine' preimageAction_coherent_atom hπf (B.cons hδ) A b _ _ _
          (StructLAction.allowable_exactlyApproximates _ _ _ _)
        rw [ha]
        exact hac
      trans b
      · rw [map_inv]
        exact this
      · rw [map_inv, Tree.inv_apply, ← smul_eq_iff_eq_inv_smul, ← ha]
        rw [StructLAction.hypothesisedAllowable]
        refine' (ihAction_coherent_atom (B.cons hδ) A b _ _
          ((ihAction_lawful hπf _).comp _) _
          (StructLAction.allowable_exactlyApproximates _ _ _ _)).symm
        refine' Relation.TransGen.tail' _
          (Constrains.fuzz _ _ ⟨⟨γ, δ, ε, hδ, hε, hδε, B, rfl⟩, _, rfl⟩ _ (smul_mem_support hc _))
        refine' Relation.reflTransGen_of_eq _
        refine' Address.ext _ _ rfl _
        change inl _ = inl _
        simp only [← this, ne_eq, Tree.comp_bot, Tree.toBot_inv_smul, map_inv,
          Tree.inv_apply]
    · intros A N hc
      have hNc := Constrains.fuzz _ _ ⟨⟨γ, δ, ε, hδ, hε, hδε, B, rfl⟩, t, rfl⟩ _ hc
      specialize hN _ N hNc
      obtain ⟨N', hN⟩ := hN
      have : (Tree.comp A
        (Allowable.toStructPerm ((preimageAction hπf
          ⟨(B.cons hε).cons (bot_lt_coe _),
            inr (fuzz hδε t).toNearLitter⟩).hypothesisedAllowable
              ⟨γ, δ, ε, hδ, hε, hδε, B, rfl⟩ ((preimageAction_lawful hπf).comp _)
              (preimageAction_comp_mapFlexible _))))⁻¹ • N = N'
      · rw [inv_smul_eq_iff, ← hN]
        rw [StructLAction.hypothesisedAllowable]
        refine' preimageAction_coherent hπf (B.cons hδ) A N' _ _ _
          (StructLAction.allowable_exactlyApproximates _ _ _ _)
        rw [hN]
        exact hNc
      trans N'
      · rw [map_inv]
        exact this
      · rw [map_inv, Tree.inv_apply, ← smul_eq_iff_eq_inv_smul, ← hN]
        rw [StructLAction.hypothesisedAllowable]
        refine' (ihAction_coherent hπf (B.cons hδ) A N' _ _
          ((ihAction_lawful hπf _).comp _) _
          (StructLAction.allowable_exactlyApproximates _ _ _ _)).symm
        refine' Relation.TransGen.tail' _
          (Constrains.fuzz _ _ ⟨⟨γ, δ, ε, hδ, hε, hδε, B, rfl⟩, _, rfl⟩ _ (smul_mem_support hc _))
        refine' Relation.reflTransGen_of_eq _
        refine' Address.ext _ _ rfl _
        change inr _ = inr _
        simp only [← this, ne_eq, Tree.comp_bot, Tree.toBot_inv_smul, map_inv,
          Tree.inv_apply]

theorem atom_mem_range_of_mem_completeNearLitterMap (A : ExtendedIndex β) (a : Atom)
    {N : NearLitter} (h : a ∈ π.completeNearLitterMap A N) : a ∈ range (π.completeAtomMap A) := by
  rw [← SetLike.mem_coe] at h
  rw [completeNearLitterMap_eq'] at h
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h
  · rw [completeNearLitterMap_toNearLitter_eq] at h₁
    obtain h₁ | h₁ := h₁
    · exact completeAtomMap_surjective_extends A a ⟨_, h₁.1.symm⟩
    · obtain ⟨b, h₁, rfl⟩ := h₁
      refine' ⟨b, _⟩
      exact completeAtomMap_eq_of_mem_domain h₁.2
  · obtain ⟨b, _, rfl⟩ := h₁
    exact ⟨b, rfl⟩

theorem completeNearLitterMap_coe (hπf : π.Free) (A : ExtendedIndex β) (N : NearLitter) :
    (π.completeNearLitterMap A N : Set Atom) = π.completeAtomMap A '' N := by
  ext a : 1
  constructor
  · intro h
    obtain ⟨b, rfl⟩ := atom_mem_range_of_mem_completeNearLitterMap A a h
    rw [SetLike.mem_coe, completeAtomMap_mem_completeNearLitterMap hπf] at h
    exact ⟨b, h, rfl⟩
  · rintro ⟨b, h, rfl⟩
    rw [SetLike.mem_coe, completeAtomMap_mem_completeNearLitterMap hπf]
    exact h

@[simp]
theorem preimage_symmDiff {α β : Type _} {s t : Set β} {f : α → β} :
    f ⁻¹' s ∆ t = (f ⁻¹' s) ∆ (f ⁻¹' t) :=
  rfl

theorem completeNearLitterMap_surjective_extends (hπf : π.Free) (A : ExtendedIndex β)
    (N : NearLitter) (hN : N.1 ∈ range (π.completeLitterMap A))
    (ha : litterSet N.1 ∆ N ⊆ range (π.completeAtomMap A)) :
    N ∈ range (π.completeNearLitterMap A) := by
  obtain ⟨L, hN⟩ := hN
  refine' ⟨⟨L, π.completeAtomMap A ⁻¹' N, _⟩, _⟩
  · suffices Small ((π.completeAtomMap A '' L.toNearLitter) ∆ N) by
      have := Small.preimage (completeAtomMap_injective hπf A) this
      rw [preimage_symmDiff, preimage_image_eq _ (completeAtomMap_injective hπf A)] at this
      exact this
    rw [← completeNearLitterMap_coe hπf]
    refine' IsNearLitter.near _ N.2.2
    simp only [NearLitter.isNearLitter, completeNearLitterMap_fst_eq]
    exact hN
  · refine' SetLike.coe_injective _
    rw [completeNearLitterMap_coe hπf]
    simp only [NearLitter.coe_mk, Subtype.coe_mk, Litter.coe_toNearLitter]
    rw [image_preimage_eq_of_subset _]
    intro a ha'
    by_cases h : a.1 = N.1
    · rw [← hN] at h
      exact completeAtomMap_surjective_extends A a ⟨_, h.symm⟩
    · exact ha (Or.inr ⟨ha', h⟩)

variable (π)

def CompleteMapSurjectiveAt : Address β → Prop
  | ⟨A, inl a⟩ => a ∈ range (π.completeAtomMap A)
  | ⟨A, inr N⟩ => N ∈ range (π.completeNearLitterMap A)

variable {π}

theorem completeMap_surjective_extends (hπf : π.Free) (c : Address β)
    (hc : ∀ d : Address β, d < c → π.CompleteMapSurjectiveAt d) :
    π.CompleteMapSurjectiveAt c := by
  obtain ⟨A, a | N⟩ := c
  · refine' completeAtomMap_surjective_extends A a _
    obtain ⟨N, hN⟩ := hc ⟨A, inr a.1.toNearLitter⟩ (Relation.TransGen.single <| Constrains.atom A a)
    refine' ⟨N.1, _⟩
    apply_fun Sigma.fst at hN
    simp only [Litter.toNearLitter_fst, completeNearLitterMap_fst_eq'] at hN
    exact hN
  · refine' completeNearLitterMap_surjective_extends hπf A N _ _
    · refine' completeLitterMap_surjective_extends hπf A N.1 _ _
      · intro B a h
        exact hc ⟨B, inl a⟩ (lt_nearLitter <| Relation.TransGen.single h)
      · intro B N h
        exact hc ⟨B, inr N⟩ (lt_nearLitter <| Relation.TransGen.single h)
    · intro a h
      exact hc ⟨A, inl a⟩ (Relation.TransGen.single <| Constrains.symmDiff A N a h)

theorem completeMapSurjectiveAtAll (hπf : π.Free) (c : Address β) :
    π.CompleteMapSurjectiveAt c :=
  WellFoundedRelation.wf.induction c (completeMap_surjective_extends hπf)

theorem completeAtomMap_surjective (hπf : π.Free) (A : ExtendedIndex β) :
    Surjective (π.completeAtomMap A) := fun a => completeMapSurjectiveAtAll hπf ⟨A, inl a⟩

theorem completeNearLitterMap_surjective (hπf : π.Free) (A : ExtendedIndex β) :
    Surjective (π.completeNearLitterMap A) := fun N => completeMapSurjectiveAtAll hπf ⟨A, inr N⟩

theorem completeLitterMap_surjective (hπf : π.Free) (A : ExtendedIndex β) :
    Surjective (π.completeLitterMap A) := by
  intro L
  obtain ⟨N, hN⟩ := completeNearLitterMap_surjective hπf A L.toNearLitter
  refine' ⟨N.1, _⟩
  apply_fun Sigma.fst at hN
  simp only [completeNearLitterMap_fst_eq', Litter.toNearLitter_fst] at hN
  exact hN

end StructApprox

end ConNF
