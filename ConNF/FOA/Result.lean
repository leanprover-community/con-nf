import ConNF.FOA.Properties.Bijective

open Equiv Function Quiver Set Sum WithBot

open scoped Classical Pointwise

universe u

namespace ConNF

namespace StructApprox

variable [Params.{u}] [Level] [BasePositions] [FOAAssumptions] {β : Λ} [LeLevel β]
  [FreedomOfActionHypothesis β] {π : StructApprox β}

noncomputable def completeAtomPerm (hπf : π.Free) (A : ExtendedIndex β) : Perm Atom :=
  Equiv.ofBijective _ (completeAtomMap_bijective hπf A)

noncomputable def completeLitterPerm (hπf : π.Free) (A : ExtendedIndex β) : Perm Litter :=
  Equiv.ofBijective _ (completeLitterMap_bijective hπf A)

theorem completeAtomPerm_apply (hπf : π.Free) (A : ExtendedIndex β) (a : Atom) :
    completeAtomPerm hπf A a = π.completeAtomMap A a :=
  rfl

theorem completeLitterPerm_apply (hπf : π.Free) (A : ExtendedIndex β) (L : Litter) :
    completeLitterPerm hπf A L = π.completeLitterMap A L :=
  rfl

noncomputable def completeNearLitterPerm (hπf : π.Free) (A : ExtendedIndex β) : NearLitterPerm
    where
  atomPerm := completeAtomPerm hπf A
  litterPerm := completeLitterPerm hπf A
  near := by
    intro L s hs
    have :
      ↑(completeAtomPerm hπf A)⁻¹ ⁻¹' s =
        (π.completeNearLitterMap A ⟨L, s, hs⟩ : Set Atom)
    · simp only [completeNearLitterMap_coe hπf, toFun_as_coe, Perm.preimage_inv, NearLitter.coe_mk]
      rfl
    rw [this]
    simp only [NearLitter.isNearLitter, completeNearLitterMap_fst_eq']
    rfl

theorem completeNearLitterPerm_smul_atom (hπf : π.Free) (A : ExtendedIndex β) (a : Atom) :
    completeNearLitterPerm hπf A • a = π.completeAtomMap A a :=
  rfl

theorem completeNearLitterPerm_smul_litter (hπf : π.Free) (A : ExtendedIndex β) (L : Litter) :
    completeNearLitterPerm hπf A • L = π.completeLitterMap A L :=
  rfl

theorem completeNearLitterPerm_smul_nearLitter (hπf : π.Free) (A : ExtendedIndex β)
    (N : NearLitter) : completeNearLitterPerm hπf A • N = π.completeNearLitterMap A N := by
  refine' SetLike.coe_injective _
  rw [completeNearLitterMap_coe hπf, NearLitterPerm.smul_nearLitter_coe]
  rfl

def AllowableBelow (hπf : π.Free) (γ : TypeIndex) [LeLevel γ] (A : Path (β : TypeIndex) γ) : Prop :=
  ∃ ρ : Allowable γ,
    ∀ B : ExtendedIndex γ,
      Tree.ofBot (Tree.comp B (Allowable.toStructPerm ρ)) =
        completeNearLitterPerm hπf (A.comp B)

@[simp]
theorem ofBot_toStructPerm (π : Allowable ⊥) : Tree.ofBot (Allowable.toStructPerm π) = π := by
  rfl

theorem allowableBelow_bot (hπf : π.Free) (A : ExtendedIndex β) : AllowableBelow hπf ⊥ A := by
  refine' ⟨completeNearLitterPerm hπf A, _⟩
  intro B
  obtain B | ⟨B, h⟩ := B
  · rfl
  · -- TODO: Make this a lemma.
    cases le_bot_iff.mp (le_of_path B)
    change (⊥ : TypeIndex) < ⊥ at h
    simp only [lt_self_iff_false] at h

theorem exists_nil_cons_of_path' {β γ : TypeIndex} (A : Path (β : TypeIndex) γ)
    (hA : A.length ≠ 0) :
    ∃ δ : TypeIndex,
      ∃ h : (δ : TypeIndex) < β,
        ∃ B : Path δ γ, A = ((Path.nil : Path (β : TypeIndex) β).cons h).comp B := by
  set n := A.length with hn
  clear_value n
  induction' n with n ih generalizing γ
  · cases hA rfl
  cases' A with δ _ A hδ
  · cases hn
  simp only [Path.length_cons, Nat.succ_eq_add_one, add_left_inj] at hn
  obtain _ | n := n
  · cases Path.eq_of_length_zero A hn.symm
    cases path_eq_nil A
    exact ⟨γ, hδ, Path.nil, rfl⟩
  · obtain ⟨ε, hε, B, rfl⟩ := ih A n.succ_ne_zero hn
    exact ⟨ε, hε, B.cons hδ, rfl⟩

theorem exists_nil_cons_of_path {β : Λ} [LeLevel β] (A : ExtendedIndex β) :
    ∃ γ : TypeIndex, ∃ _ : LtLevel γ,
      ∃ h : (γ : TypeIndex) < β,
        ∃ B : ExtendedIndex γ, A = ((Path.nil : Path (β : TypeIndex) β).cons h).comp B := by
  have := exists_nil_cons_of_path' A ?_
  obtain ⟨γ, h, B, rfl⟩ := this
  · refine' ⟨γ, _, h, B, rfl⟩
    exact ⟨lt_of_lt_of_le h LeLevel.elim⟩
  · intro h
    cases Path.eq_of_length_zero A h

theorem ConNF.StructApprox.extracted_1'
  (hπf : π.Free) (γ : Λ) [LeLevel γ] (A : Path (β : TypeIndex) γ)
  (ρs : (δ : TypeIndex) → [LtLevel δ] → δ < γ → Allowable δ)
  (hρ : ∀ (δ : TypeIndex) [LtLevel δ] (h : δ < γ) (B : ExtendedIndex δ),
    Tree.ofBot (Tree.comp B (Allowable.toStructPerm (ρs δ h))) =
      completeNearLitterPerm hπf ((A.cons h).comp B))
  (ε : Λ) [LtLevel ε] (hε : (ε : TypeIndex) < γ) (a : Atom) :
  Allowable.toStructPerm (ρs ε hε) (Hom.toPath (bot_lt_coe _)) • fuzz (bot_ne_coe (a := ε)) a =
    fuzz (bot_ne_coe (a := ε)) (NearLitterPerm.ofBot (ρs ⊥ (bot_lt_coe _)) • a) := by
  have := hρ ε hε (Path.nil.cons (bot_lt_coe _))
  simp only [Path.comp_cons, Path.comp_nil, Tree.comp_bot, Tree.ofBot_toBot, Hom.toPath] at this
  erw [this]
  rw [completeNearLitterPerm_smul_litter]
  refine' (completeLitterMap_eq_of_inflexibleBot ⟨⟨γ, ε, hε, A, rfl⟩, a, rfl⟩).trans _
  refine' congr_arg _ _
  specialize hρ ⊥ (bot_lt_coe _) Path.nil
  rw [Path.comp_nil, Tree.comp_nil
    (Allowable.toStructPerm (ρs ⊥ (bot_lt_coe _)))] at hρ
  rw [(ofBot_toStructPerm (ρs ⊥ (bot_lt_coe _))).symm.trans hρ]
  rfl

theorem ConNF.StructApprox.extracted_2'
  (hπf : π.Free) (γ : Λ) [LeLevel γ] (A : Path (β : TypeIndex) γ)
  (ρs : (δ : TypeIndex) → [LtLevel δ] → δ < γ → Allowable δ)
  (hρ : ∀ (δ : TypeIndex) [LtLevel δ] (h : δ < γ) (B : ExtendedIndex δ),
    Tree.ofBot (Tree.comp B (Allowable.toStructPerm (ρs δ h))) =
      completeNearLitterPerm hπf ((A.cons h).comp B))
  (δ : Λ) [LtLevel δ] (ε : Λ) [LtLevel ε] (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ)
  (hδε : (δ : TypeIndex) ≠ ε) (t : Tangle δ) :
  Allowable.toStructPerm (ρs ε hε) (Hom.toPath (bot_lt_coe _)) •
    fuzz hδε t =
  fuzz hδε (ρs δ hδ • t) := by
  have := hρ ε hε (Path.nil.cons (bot_lt_coe _))
  simp only [Tree.comp_bot, Tree.ofBot_toBot, Path.comp_cons,
    Path.comp_nil] at this
  erw [this]
  rw [completeNearLitterPerm_smul_litter]
  refine' (completeLitterMap_eq_of_inflexibleCoe
    ⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t, rfl⟩
    ((ihAction_lawful hπf _).comp _) (ihAction_comp_mapFlexible hπf _ _)).trans _
  refine' congr_arg _ _
  dsimp only
  refine supports (t := t) ?_ ?_
  · intros B a ha
    have := ihAction_coherent_atom (π := π) (A.cons _) B a
      ⟨_, inr (fuzz hδε t).toNearLitter⟩
      (Relation.TransGen.single <| Constrains.fuzz hδ hε hδε _ t _ ha)
      ((ihAction_lawful hπf _).comp _) ?_ ?_
    · exact this.symm.trans (congr_arg (fun π => π • a) (hρ δ hδ B)).symm
    · exact (ihAction π.foaHypothesis).hypothesisedAllowable_exactlyApproximates
        ⟨γ, δ, ε, _, _, _, _, rfl⟩ _ _
  · intros B N hN
    have := ihAction_coherent hπf (A.cons _) B N
      ⟨_, inr (fuzz hδε t).toNearLitter⟩
      (Relation.TransGen.single <| Constrains.fuzz hδ hε hδε _ t _ hN)
      ((ihAction_lawful hπf _).comp _) ?_ ?_
    rw [← completeNearLitterPerm_smul_nearLitter hπf] at this
    · exact this.symm.trans (congr_arg (fun π => π • N) (hρ δ hδ B)).symm
    · exact (ihAction π.foaHypothesis).hypothesisedAllowable_exactlyApproximates
        ⟨γ, δ, ε, _, _, _, _, rfl⟩ _ _

theorem allowableBelow_extends (hπf : π.Free) (γ : Λ) [LeLevel γ] (A : Path (β : TypeIndex) γ)
    (h : ∀ (δ : TypeIndex) [LtLevel δ] (h : δ < γ), AllowableBelow hπf δ (A.cons h)) :
    AllowableBelow hπf γ A := by
  choose ρs hρs using h
  have := allowable_of_smulFuzz γ ρs ?_
  · obtain ⟨ρ, hρ⟩ := this
    refine ⟨ρ, ?_⟩
    intro B
    obtain ⟨δ, _, hδ, B, rfl⟩ := exists_nil_cons_of_path B
    specialize hρs δ hδ B
    simp only [Tree.comp_bot, Tree.ofBot_toBot] at hρs ⊢
    have := hρ δ hδ
    apply_fun Allowable.toStructPerm at this
    rw [← allowableCons_eq] at this
    rw [← this] at hρs
    rw [← Path.comp_assoc, Path.comp_cons, Path.comp_nil]
    exact hρs
  · intro δ i ε _ hδ hε hδε t
    revert i
    induction δ using recBotCoe with
    | bot =>
        intro i t
        simp only [Allowable.comp_eq, NearLitterPerm.ofBot_smul, Allowable.toStructPerm_smul]
        refine Eq.trans ?_ (ConNF.StructApprox.extracted_1' hπf γ A ρs hρs ε hε t)
        simp only [Allowable.toStructPerm_comp, Tree.comp_bot, Tree.toBot_smul]
        rfl
    | coe δ =>
        intro i t
        simp only [Allowable.comp_eq, NearLitterPerm.ofBot_smul, Allowable.toStructPerm_smul]
        refine Eq.trans ?_ (ConNF.StructApprox.extracted_2' hπf γ A ρs hρs δ ε hδ hε hδε t)
        simp only [Allowable.toStructPerm_comp, Tree.comp_bot, Tree.toBot_smul]
        rfl

theorem allowableBelow_all (hπf : π.Free) (γ : Λ) [i : LeLevel γ] (A : Path (β : TypeIndex) γ) :
    AllowableBelow hπf γ A := by
  revert i
  have := WellFounded.induction
    (C := fun γ => ∀ (A : Path (β : TypeIndex) γ) (i : LeLevel γ), AllowableBelow hπf γ A)
    (inferInstanceAs (IsWellFounded Λ (· < ·))).wf γ
  refine this ?_ _
  intro γ ih A hγ
  refine' allowableBelow_extends hπf γ A _
  intro δ hδ
  induction δ using recBotCoe generalizing hδ with
  | bot => intro; exact allowableBelow_bot hπf _
  | coe δ => intro h; exact ih δ (coe_lt_coe.mp h) _ _

noncomputable def completeAllowable (hπf : π.Free) : Allowable β :=
  (allowableBelow_all hπf β Path.nil).choose

theorem completeAllowable_comp (hπf : π.Free) :
    Allowable.toStructPerm (completeAllowable hπf) = completeNearLitterPerm hπf := by
  funext A
  have := (allowableBelow_all hπf β Path.nil).choose_spec A
  rw [Path.nil_comp] at this
  exact this

theorem complete_exception_mem (hπf : π.Free) (A : ExtendedIndex β) (a : Atom)
    (ha : (completeNearLitterPerm hπf A).IsException a) : a ∈ (π A).atomPerm.domain := by
  unfold NearLitterPerm.IsException at ha
  simp only [mem_litterSet, completeNearLitterPerm_smul_atom,
    completeNearLitterPerm_smul_litter] at ha
  obtain ha | ha := ha
  · have := completeNearLitterMap_toNearLitter_eq (π := π) A a.1
    rw [completeNearLitterMap_coe hπf, Set.ext_iff] at this
    have := (this (π.completeAtomMap A a)).mp ⟨_, rfl, rfl⟩
    obtain ha' | ⟨b, ⟨hb₁, hb₂⟩, hb₃⟩ := this
    · cases ha ha'.1
    dsimp only at hb₃
    rw [← completeAtomMap_eq_of_mem_domain hb₂] at hb₃
    cases completeAtomMap_injective hπf A hb₃
    exact hb₂
  · obtain ⟨a, rfl⟩ := completeAtomMap_surjective hπf A a
    rw [eq_inv_smul_iff, ← completeNearLitterPerm_smul_atom hπf, inv_smul_smul] at ha
    have := completeNearLitterMap_toNearLitter_eq (π := π) A a.1
    rw [completeNearLitterMap_coe hπf, Set.ext_iff] at this
    have := (this (π.completeAtomMap A a)).mp ⟨_, rfl, rfl⟩
    obtain ha' | ⟨b, ⟨hb₁, hb₂⟩, hb₃⟩ := this
    · cases ha ha'.1.symm
    · dsimp only at hb₃
      rw [← completeAtomMap_eq_of_mem_domain hb₂] at hb₃
      cases completeAtomMap_injective hπf A hb₃
      rw [completeAtomMap_eq_of_mem_domain hb₂]
      exact (π A).atomPerm.map_domain hb₂

theorem completeAllowable_exactlyApproximates (hπf : π.Free) :
    π.ExactlyApproximates (Allowable.toStructPerm <| completeAllowable hπf) := by
  intro A
  refine' ⟨⟨_, _⟩, _⟩
  · intro a ha
    rw [completeAllowable_comp, completeNearLitterPerm_smul_atom,
      completeAtomMap_eq_of_mem_domain ha]
  · intro L hL
    rw [completeAllowable_comp, completeNearLitterPerm_smul_litter,
      completeLitterMap_eq_of_flexible (hπf A L hL),
      NearLitterApprox.flexibleCompletion_smul_of_mem_domain _ A L hL]
    rfl
  · intro a ha
    rw [completeAllowable_comp] at ha
    exact complete_exception_mem hπf A a ha

def foa_extends : FOAIh β := fun _ hπf =>
  ⟨completeAllowable hπf, completeAllowable_exactlyApproximates hπf⟩

theorem freedom_of_action {β : Λ} [i : LeLevel β] (π₀ : StructApprox β) (h : π₀.Free) :
    ∃ π : Allowable β, π₀.ExactlyApproximates (Allowable.toStructPerm π) := by
  revert i
  have := WellFounded.induction
    (C := fun β => ∀ (i : LeLevel β) (π₀ : StructApprox β),
      Free π₀ → ∃ π : Allowable β, ExactlyApproximates π₀ (Allowable.toStructPerm π))
    (inferInstanceAs (IsWellFounded Λ (· < ·))).wf β
  refine fun i => this ?_ i π₀ h
  intro β ih _ π₀ h
  have : FreedomOfActionHypothesis β
  · constructor
    intro γ hγ
    exact ih γ hγ inferInstance
  exact foa_extends π₀ h

end StructApprox

end ConNF
