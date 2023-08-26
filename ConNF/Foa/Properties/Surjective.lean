import ConNF.Foa.Properties.Injective

open Equiv Function Quiver Set Sum WithBot

open scoped Classical Pointwise

universe u

namespace ConNF

namespace StructApprox

variable [Params.{u}] {α : Λ} [PositionData] [Phase2Assumptions α] {β : Iic α}
  [FreedomOfActionHypothesis β] {π : StructApprox β}

theorem completeNearLitterMap_subset_range (A : ExtendedIndex β) (L : Litter) :
    (π.completeNearLitterMap A L.toNearLitter : Set Atom) ⊆ range (π.completeAtomMap A) := by
  rw [completeNearLitterMap_toNearLitter_eq]
  rintro a (⟨ha₁, ha₂⟩ | ⟨a, ⟨_, ha₂⟩, rfl⟩)
  · refine' ⟨(((π A).largestSublitter L).equiv ((π A).largestSublitter a.1)).symm
      ⟨a, (π A).mem_largestSublitter_of_not_mem_domain a ha₂⟩, _⟩
    rw [completeAtomMap_eq_of_not_mem_domain]
    swap
    · exact NearLitterApprox.not_mem_domain_of_mem_largestSublitter _
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

noncomputable def completeSupportConditionMap (π : StructApprox β) :
    SupportCondition β → SupportCondition β
  | (inl a, B) => (inl (π.completeAtomMap B a), B)
  | (inr N, B) => (inr (π.completeNearLitterMap B N), B)

@[simp]
theorem completeSupportConditionMap_atom_eq {π : StructApprox β} {a : Atom} {B : ExtendedIndex β} :
    π.completeSupportConditionMap (inl a, B) = (inl (π.completeAtomMap B a), B) :=
  rfl

@[simp]
theorem completeSupportConditionMap_nearLitter_eq {π : StructApprox β} {N : NearLitter}
    {B : ExtendedIndex β} :
    π.completeSupportConditionMap (inr N, B) = (inr (π.completeNearLitterMap B N), B) :=
  rfl

theorem completeSupportConditionMap_injective (hπf : π.Free) :
    Injective π.completeSupportConditionMap := by
  rintro ⟨a₁ | N₁, B₁⟩ ⟨a₂ | N₂, B₂⟩ h <;>
    rw [Prod.ext_iff] at h <;>
    simp only [completeSupportConditionMap_atom_eq,
      completeSupportConditionMap_nearLitter_eq,
      inl.injEq, inr.injEq, false_and] at h
  · cases h.2
    cases completeAtomMap_injective hπf B₁ h.1
    rfl
  · cases h.2
    cases completeNearLitterMap_injective hπf B₁ h.1
    rfl

def preimageConstrained (π : StructApprox β) (c : SupportCondition β) : Set (SupportCondition β) :=
  π.completeSupportConditionMap ⁻¹' {d | d ≺[α] c}

theorem preimageConstrained_small (hπf : π.Free) (c : SupportCondition β) :
    Small (preimageConstrained π c) :=
  Small.preimage (completeSupportConditionMap_injective hπf) (small_constrains c)

noncomputable def preimageAction (hπf : π.Free) (c : SupportCondition β) : StructAction β :=
  constrainedAction π (preimageConstrained π c) (preimageConstrained_small hπf c)

theorem preimageAction_eq_constrainedAction (hπf : π.Free) (c : SupportCondition β) :
    preimageAction hπf c =
      constrainedAction π (preimageConstrained π c) (preimageConstrained_small hπf c) :=
  rfl

-- In fact, any `constrained_action` is lawful.
theorem preimageAction_lawful (hπf : π.Free) {c : SupportCondition β} :
    (preimageAction hπf c).Lawful := by
  intro A
  constructor
  · intro a b ha hb hab
    exact completeAtomMap_injective hπf A hab
  · intro L₁ L₂ hL₁ hL₂ hL
    exact completeLitterMap_injective hπf A (eq_of_completeLitterMap_inter_nonempty hL)
  · intro a _ L _
    exact (completeAtomMap_mem_completeNearLitterMap_toNearLitter hπf).symm

theorem preimageAction_comp_mapFlexible {hπf : π.Free} {γ : Iio α} {c : SupportCondition β}
    (A : Path (β : TypeIndex) γ) : ((preimageAction hπf c).comp A).MapFlexible :=
  constrainedAction_comp_mapFlexible hπf A

theorem Relation.reflTransGen_of_eq {α : Type _} {r : α → α → Prop} {x y : α} (h : x = y) :
    Relation.ReflTransGen r x y := by
  cases h
  rfl

theorem preimageAction_coherent (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (N : NearLitter) (c : SupportCondition β)
    (hc : (inr (π.completeNearLitterMap (A.comp B) N), A.comp B) ≺[α] c) (ρ : Allowable γ)
    (h : (((preimageAction hπf c).comp A).rc
      ((preimageAction_lawful hπf).comp _)).ExactlyApproximates (Allowable.toStructPerm ρ)) :
    completeNearLitterMap π (A.comp B) N =
    StructPerm.derivative B (Allowable.toStructPerm ρ) • N := by
  refine' constrainedAction_coherent hπf A B N _ _ _
    ((preimageAction_lawful hπf).comp _) ρ h
  refine' ⟨_, _, Relation.ReflTransGen.refl⟩
  exact hc

theorem preimageAction_coherent_atom (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (a : Atom) (c : SupportCondition β)
    (hc : (inl (π.completeAtomMap (A.comp B) a), A.comp B) ≺[α] c) (ρ : Allowable γ)
    (h : (((preimageAction hπf c).comp A).rc
      ((preimageAction_lawful hπf).comp _)).ExactlyApproximates (Allowable.toStructPerm ρ)) :
    completeAtomMap π (A.comp B) a = StructPerm.derivative B (Allowable.toStructPerm ρ) • a := by
  refine' constrainedAction_coherent_atom A B a _ _ _ _ ρ h
  refine' ⟨_, _, Relation.ReflTransGen.refl⟩
  exact hc

theorem completeLitterMap_surjective_extends (hπf : π.Free) (A : ExtendedIndex β) (L : Litter)
    (ha : ∀ (B : ExtendedIndex β) (a : Atom),
      (inl a, B) ≺[α] (inr L.toNearLitter, A) → a ∈ range (π.completeAtomMap B))
    (hN : ∀ (B : ExtendedIndex β) (N : NearLitter),
      (inr N, B) ≺[α] (inr L.toNearLitter, A) → N ∈ range (π.completeNearLitterMap B)) :
    L ∈ range (π.completeLitterMap A) := by
  obtain h | ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩ := flexible_cases' β L A
  · refine' ⟨(NearLitterApprox.flexibleCompletion α (π A) A).symm • L, _⟩
    rw [completeLitterMap_eq_of_flexible, NearLitterApprox.right_inv_litter]
    · rw [NearLitterApprox.flexibleCompletion_litterPerm_domain_free α (π A) A (hπf A)]
      exact h
    · exact NearLitterApprox.flexibleCompletion_symm_smul_flexible α (π A) A (hπf A) L h
  · obtain ⟨γ, ε, hε, C, a, rfl, rfl⟩ := h
    obtain ⟨b, rfl⟩ := ha _ a (Constrains.fuzz_bot hε _ a)
    refine' ⟨fuzz (show ⊥ ≠ (ε : TypeIndex) from bot_ne_coe) b, _⟩
    rw [completeLitterMap_eq_of_inflexibleBot ⟨γ, ε, hε, C, b, rfl, rfl⟩]
  · obtain ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ := h
    refine' ⟨fuzz (coe_ne_coe.mpr <| coe_ne' hδε)
      (((preimageAction hπf
            (inr (fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
              (B.cons (coe_lt hε)).cons (bot_lt_coe _))).hypothesisedAllowable
          ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩
          ((preimageAction_lawful hπf).comp _) (preimageAction_comp_mapFlexible _))⁻¹ • t), _⟩
    rw [completeLitterMap_eq_of_inflexibleCoe ⟨γ, δ, ε, hδ, hε, hδε, B, _, rfl, rfl⟩
        ((ihAction_lawful hπf _).comp _) (ihAction_comp_mapFlexible hπf _ _)]
    refine' congr_arg _ _
    rw [smul_smul]
    refine' (designatedSupport t).supports _ _
    intro c hc
    rw [mul_smul, smul_eq_iff_eq_inv_smul]
    change (_, c.2) = (_, c.2)
    refine' Prod.ext _ rfl
    obtain ⟨a | N, A⟩ := c
    · change inl _ = inl _
      simp only [inl.injEq]
      have hac := Constrains.fuzz hδ hε hδε B t _ hc
      specialize ha _ a hac
      obtain ⟨b, ha⟩ := ha
      have : (StructPerm.derivative A
        (Allowable.toStructPerm ((preimageAction hπf
            (inr (fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
              (B.cons (coe_lt hε)).cons (bot_lt_coe _))).hypothesisedAllowable
              ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ ((preimageAction_lawful hπf).comp _)
              (preimageAction_comp_mapFlexible _))))⁻¹ • a = b
      · rw [inv_smul_eq_iff, ← ha]
        rw [StructAction.hypothesisedAllowable]
        refine' preimageAction_coherent_atom hπf (B.cons <| coe_lt hδ) A b _ _ _
          (StructAction.allowable_exactlyApproximates _ _ _ _)
        rw [ha]
        exact hac
      trans b
      · rw [map_inv, map_inv, this]
      · rw [map_inv, map_inv, ← smul_eq_iff_eq_inv_smul, ← ha]
        rw [StructAction.hypothesisedAllowable]
        refine' (ihAction_coherent_atom (B.cons <| coe_lt hδ) A b _ _
          ((ihAction_lawful hπf _).comp _) _
          (StructAction.allowable_exactlyApproximates _ _ _ _)).symm
        refine' Relation.TransGen.tail' _
          (Constrains.fuzz hδ hε hδε B _ _ (smul_mem_designatedSupport hc _))
        refine' Relation.reflTransGen_of_eq _
        refine' Prod.ext _ rfl
        change inl _ = inl _
        simp only [map_inv, eq_inv_smul_iff, ← this, smul_inv_smul]
    · change inr _ = inr _
      simp only [inr.injEq]
      have hNc := Constrains.fuzz hδ hε hδε B t _ hc
      specialize hN _ N hNc
      obtain ⟨N', hN⟩ := hN
      have : (StructPerm.derivative A
        (Allowable.toStructPerm ((preimageAction hπf
          (inr (fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
            (B.cons (coe_lt hε)).cons (bot_lt_coe _))).hypothesisedAllowable
              ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ ((preimageAction_lawful hπf).comp _)
              (preimageAction_comp_mapFlexible _))))⁻¹ • N = N'
      · rw [inv_smul_eq_iff, ← hN]
        rw [StructAction.hypothesisedAllowable]
        refine' preimageAction_coherent hπf (B.cons <| coe_lt hδ) A N' _ _ _
          (StructAction.allowable_exactlyApproximates _ _ _ _)
        rw [hN]
        exact hNc
      trans N'
      · rw [map_inv, map_inv, this]
      · rw [map_inv, map_inv, ← smul_eq_iff_eq_inv_smul, ← hN]
        rw [StructAction.hypothesisedAllowable]
        refine' (ihAction_coherent hπf (B.cons <| coe_lt hδ) A N' _ _
          ((ihAction_lawful hπf _).comp _) _
          (StructAction.allowable_exactlyApproximates _ _ _ _)).symm
        refine' Relation.TransGen.tail' _
          (Constrains.fuzz hδ hε hδε B _ _ (smul_mem_designatedSupport hc _))
        refine' Relation.reflTransGen_of_eq _
        refine' Prod.ext _ rfl
        change inr _ = inr _
        simp only [map_inv, eq_inv_smul_iff, ← this, smul_inv_smul]

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
    by_cases a.1 = N.1
    · rw [← hN] at h
      exact completeAtomMap_surjective_extends A a ⟨_, h.symm⟩
    · exact ha (Or.inr ⟨ha', h⟩)

variable (π)

def CompleteMapSurjectiveAt : SupportCondition β → Prop
  | (inl a, A) => a ∈ range (π.completeAtomMap A)
  | (inr N, A) => N ∈ range (π.completeNearLitterMap A)

variable {π}

theorem completeMap_surjective_extends (hπf : π.Free) (c : SupportCondition β)
    (hc : ∀ d : SupportCondition β, d <[α] c → π.CompleteMapSurjectiveAt d) :
    π.CompleteMapSurjectiveAt c := by
  obtain ⟨a | N, A⟩ := c
  · refine' completeAtomMap_surjective_extends A a _
    obtain ⟨N, hN⟩ := hc (inr a.1.toNearLitter, A) (Relation.TransGen.single <| Constrains.atom a A)
    refine' ⟨N.1, _⟩
    apply_fun Sigma.fst at hN
    simp only [Litter.toNearLitter_fst, completeNearLitterMap_fst_eq'] at hN
    exact hN
  · refine' completeNearLitterMap_surjective_extends hπf A N _ _
    · refine' completeLitterMap_surjective_extends hπf A N.1 _ _
      · intro B a h
        exact hc (inl a, B) (transGen_nearLitter <| Relation.TransGen.single h)
      · intro B N h
        exact hc (inr N, B) (transGen_nearLitter <| Relation.TransGen.single h)
    · intro a h
      exact hc (inl a, A) (Relation.TransGen.single <| Constrains.symmDiff N a h A)

theorem completeMapSurjectiveAtAll (hπf : π.Free) (c : SupportCondition β) :
    π.CompleteMapSurjectiveAt c :=
  WellFounded.induction (trans_constrains_wf α β) c (completeMap_surjective_extends hπf)

theorem completeAtomMap_surjective (hπf : π.Free) (A : ExtendedIndex β) :
    Surjective (π.completeAtomMap A) := fun a => completeMapSurjectiveAtAll hπf (inl a, A)

theorem completeNearLitterMap_surjective (hπf : π.Free) (A : ExtendedIndex β) :
    Surjective (π.completeNearLitterMap A) := fun N => completeMapSurjectiveAtAll hπf (inr N, A)

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
