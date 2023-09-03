import ConNF.Foa.Properties.Bijective

open Equiv Function Quiver Set Sum WithBot

open scoped Classical Pointwise

universe u

namespace ConNF

namespace StructApprox

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}
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

def AllowableBelow (hπf : π.Free) (γ : IicBot α) (A : Path (β : TypeIndex) γ) : Prop :=
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

theorem exists_nil_cons_of_path {β : Iic α} (A : ExtendedIndex β) :
    ∃ γ : IioBot α,
      ∃ h : (γ : TypeIndex) < β,
        ∃ B : ExtendedIndex γ, A = ((Path.nil : Path (β : TypeIndex) β).cons h).comp B := by
  have := exists_nil_cons_of_path' A ?_
  obtain ⟨γ, h, B, rfl⟩ := this
  · refine' ⟨⟨γ, _⟩, h, B, rfl⟩
    exact lt_of_lt_of_le h (coe_le_coe.mpr β.prop)
  · intro h
    cases Path.eq_of_length_zero A h

theorem iioBot_cases (δ : IioBot α) : δ = ⊥ ∨ ∃ ε : Iio α, δ = ε := by
  obtain ⟨_ | δ, hδ⟩ := δ
  · exact Or.inl rfl
  · exact Or.inr ⟨⟨δ, coe_lt_coe.mp hδ⟩, rfl⟩

theorem ConNF.StructApprox.extracted_1'
  (hπf : π.Free) (γ : Iic α) (A : Path (β : TypeIndex) γ)
  (ρs : (δ : IioBot α) → (δ : TypeIndex) < γ → Allowable δ)
  (hρ : ∀ (δ : IioBot α) (h : (δ : TypeIndex) < γ) (B : ExtendedIndex δ),
    Tree.ofBot (Tree.comp B (Allowable.toStructPerm (ρs δ h))) =
      completeNearLitterPerm hπf ((A.cons h).comp B))
  (ε : Iio α) (hε : (ε : TypeIndex) < γ) (a : Atom) :
  Allowable.toStructPerm (ρs ε hε) (Hom.toPath (bot_lt_coe _)) •
    fuzz (show ⊥ ≠ (ε : TypeIndex) from bot_ne_coe) a =
  fuzz (show ⊥ ≠ (ε : TypeIndex) from bot_ne_coe)
    (NearLitterPerm.ofBot (ρs ⊥ (bot_lt_coe _)) • a) := by
  have := hρ ε hε (Path.nil.cons (bot_lt_coe _))
  simp only [Path.comp_cons, Path.comp_nil, Tree.comp_bot, Tree.ofBot_toBot,
    Hom.toPath] at this
  erw [this]
  rw [completeNearLitterPerm_smul_litter]
  refine' (completeLitterMap_eq_of_inflexibleBot
    ⟨⟨γ, ε, coe_lt_coe.mp hε, A, rfl⟩, a, rfl⟩).trans _
  refine' congr_arg _ _
  specialize hρ ⊥ (bot_lt_coe _) Path.nil
  rw [Path.comp_nil, Tree.comp_nil
    (Allowable.toStructPerm (ρs ⊥ (bot_lt_coe _)))] at hρ
  rw [(ofBot_toStructPerm (ρs ⊥ (bot_lt_coe _))).symm.trans hρ]
  rfl

theorem ConNF.StructApprox.extracted_2'
  (hπf : π.Free) (γ : Iic α) (A : Path (β : TypeIndex) γ)
  (ρs : (δ : IioBot α) → (δ : TypeIndex) < γ → Allowable δ)
  (hρ : ∀ (δ : IioBot α) (h : (δ : TypeIndex) < γ) (B : ExtendedIndex δ),
    Tree.ofBot (Tree.comp B (Allowable.toStructPerm (ρs δ h))) =
      completeNearLitterPerm hπf ((A.cons h).comp B))
  (δ : Iio α) (ε : Iio α) (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ)
  (hδε : δ ≠ ε) (t : Tangle ↑δ) :
  Allowable.toStructPerm (ρs ε hε) (Hom.toPath (bot_lt_coe _)) •
    fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t =
  fuzz (coe_ne_coe.mpr <| coe_ne' hδε) (ρs δ hδ • t) := by
  have := hρ ε hε (Path.nil.cons (bot_lt_coe _))
  simp only [Tree.comp_bot, Tree.ofBot_toBot, Path.comp_cons,
    Path.comp_nil] at this
  erw [this]
  rw [completeNearLitterPerm_smul_litter]
  refine' (completeLitterMap_eq_of_inflexibleCoe
    ⟨⟨γ, δ, ε, coe_lt_coe.mp hδ, coe_lt_coe.mp hε, _, A, rfl⟩, t, rfl⟩
    ((ihAction_lawful hπf _).comp _) (ihAction_comp_mapFlexible hπf _ _)).trans _
  · rintro rfl
    cases hδε rfl
  refine' congr_arg _ _
  simp only
  refine supports (t := t) ?_ ?_
  · intros B a ha
    have := ihAction_coherent_atom (π := π) (A.cons _) B a
      ⟨_, inr (fuzz (show (δ : TypeIndex) ≠ ε from ?_) t).toNearLitter⟩
      (Relation.TransGen.single <| Constrains.fuzz ?_ ?_ ?_ _ t _ ha)
      ((ihAction_lawful hπf _).comp _) ?_ ?_
    exact this.symm.trans (congr_arg (fun π => π • a) (hρ δ hδ B)).symm
    · intro h
      simp only [coe_inj, Subtype.coe_inj] at h
      cases hδε h
    · exact coe_lt_coe.mp hδ
    · exact coe_lt_coe.mp hε
    · rintro rfl
      cases hδε rfl
    · exact (ihAction π.foaHypothesis).hypothesisedAllowable_exactlyApproximates
        ⟨γ, δ, ε, _, _, _, _, rfl⟩ _ _
  · intros B N hN
    have := ihAction_coherent hπf (A.cons _) B N
      ⟨_, inr (fuzz (show (δ : TypeIndex) ≠ ε from ?_) t).toNearLitter⟩
      (Relation.TransGen.single <| Constrains.fuzz ?_ ?_ ?_ _ t _ hN)
      ((ihAction_lawful hπf _).comp _) ?_ ?_
    rw [← completeNearLitterPerm_smul_nearLitter hπf] at this
    exact this.symm.trans (congr_arg (fun π => π • N) (hρ δ hδ B)).symm
    · exact coe_lt_coe.mp hδ
    · intro h
      simp only [coe_inj, Subtype.coe_inj] at h
      cases hδε h
    · exact coe_lt_coe.mp hε
    · rintro rfl
      cases hδε rfl
    · exact (ihAction π.foaHypothesis).hypothesisedAllowable_exactlyApproximates
        ⟨γ, δ, ε, _, _, _, _, rfl⟩ _ _

theorem allowableBelow_extends (hπf : π.Free) (γ : Iic α) (A : Path (β : TypeIndex) γ)
    (h : ∀ (δ : IioBot α) (h : (δ : TypeIndex) < γ), AllowableBelow hπf δ (A.cons h)) :
    AllowableBelow hπf γ A := by
  choose ρs hρ using h
  refine' ⟨allowableOfSmulFuzz γ ρs _, _⟩
  · intro δ ε hδ hε hδε t
    obtain rfl | ⟨δ, rfl⟩ := iioBot_cases δ
    · simp only [Allowable.comp_eq, NearLitterPerm.ofBot_smul, Allowable.toStructPerm_smul]
      refine Eq.trans ?_ (ConNF.StructApprox.extracted_1' hπf γ A ρs hρ ε hε t)
      exact congr_arg₂ _ (Allowable.comp_bot _ _) rfl
    · simp only [Allowable.comp_eq, NearLitterPerm.ofBot_smul, Allowable.toStructPerm_smul]
      refine Eq.trans ?_ (ConNF.StructApprox.extracted_2' hπf γ A ρs hρ δ ε hδ hε ?_ t)
      · exact congr_arg₂ _ (Allowable.comp_bot _ _) rfl
      · rintro rfl
        exact hδε rfl
  · intro B
    obtain ⟨δ, hδ, B, rfl⟩ := exists_nil_cons_of_path B
    specialize hρ δ hδ B
    rw [← Tree.comp_comp]
    have := allowableOfSmulFuzz_comp_eq (ρs := ρs) (h := ?_) δ hδ
    apply_fun Allowable.toStructPerm at this
    rw [← allowableCons_eq] at this
    rw [← this] at hρ
    rw [← Path.comp_assoc, Path.comp_cons, Path.comp_nil]
    exact hρ

theorem allowableBelow_all (hπf : π.Free) (γ : Iic α) (A : Path (β : TypeIndex) γ) :
    AllowableBelow hπf γ A := by
  obtain ⟨γ, hγ⟩ := γ
  revert hγ
  refine' WellFounded.induction
    (C := fun γ => ∀ (hγ : γ ∈ Iic α) (A : Path (β : TypeIndex) γ),
      AllowableBelow hπf ⟨γ, coe_le_coe.mpr hγ⟩ A) Λwo.wf γ _
  clear γ
  intro γ ih hγ A
  refine' allowableBelow_extends hπf ⟨γ, hγ⟩ A _
  intro δ hδ
  obtain rfl | ⟨δ, rfl⟩ := iioBot_cases δ
  · exact allowableBelow_bot hπf _
  · exact ih δ (coe_lt_coe.mp hδ) (le_of_lt (Iio.lt δ)) _

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
      NearLitterApprox.flexibleCompletion_smul_of_mem_domain _ _ A L hL]
    rfl
  · intro a ha
    rw [completeAllowable_comp] at ha
    exact complete_exception_mem hπf A a ha

def foa_extends : FoaIh β := fun _ hπf =>
  ⟨completeAllowable hπf, completeAllowable_exactlyApproximates hπf⟩

theorem freedom_of_action (β : Iic α) (π₀ : StructApprox β) (h : π₀.Free) :
    ∃ π : Allowable β, π₀.ExactlyApproximates (Allowable.toStructPerm π) := by
  obtain ⟨β, hβ⟩ := β
  revert hβ
  refine' WellFounded.induction
    (C := fun β => ∀ (hβ : β ∈ Iic α) (π₀ : StructApprox (⟨β, hβ⟩ : Iic α)),
      Free π₀ → ∃ π : @Allowable _ (⟨β, hβ⟩ : Iic α) FoaData.tangleData,
        ExactlyApproximates π₀ (@Allowable.toStructPerm _ _ FoaData.tangleData π)) Λwo.wf β _
  intro β ih hβ π₀ h
  have : FreedomOfActionHypothesis ⟨β, hβ⟩
  · constructor
    intro γ hγ
    exact ih γ hγ γ.prop
  exact foa_extends π₀ h

end StructApprox

end ConNF
