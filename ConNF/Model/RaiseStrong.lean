import ConNF.Model.FOA

open Quiver Sum WithBot

open scoped Pointwise symmDiff

universe u

noncomputable section

namespace ConNF.Support

variable [Params.{u}] [Level] {β γ : Λ} [iβ : LtLevel β] [iγ : LtLevel γ] (hγ : (γ : TypeIndex) < β)

local instance : FOAAssumptions := Construction.FOA.foaAssumptions

theorem toPath_comp_eq_cons {α β γ δ : TypeIndex} (hβ : β < α) (hγ : γ < α) (hδ : δ < γ)
    (A : Path β δ) (B : Path α γ)
    (h : (Hom.toPath hβ).comp A = B.cons hδ) :
    ∃ C : Path β γ, B = (Hom.toPath hβ).comp C := by
  induction' A with ε ζ A hε ih
  case nil =>
    cases h
    cases hγ.not_le le_rfl
  case cons =>
    simp only [Path.comp_cons, Path.cons.injEq] at h
    cases h.1
    simp only [heq_eq_eq, and_true, true_and] at h
    exact ⟨_, h.symm⟩

theorem raise_eq_cons_cons {α β γ δ : Λ} (hβ : (β : TypeIndex) < α) (hδ : (δ : TypeIndex) < γ)
    (c : Address β) (B : Path (α : TypeIndex) γ) (x : Atom ⊕ NearLitter)
    (h : raise hβ c = ⟨(B.cons hδ).cons (bot_lt_coe _), x⟩) :
    γ = α ∨ (∃ C : Path (β : TypeIndex) γ, B = (Hom.toPath hβ).comp C) := by
  by_cases hγ : (γ : TypeIndex) < α
  · simp only [raise, raiseIndex, Address.mk.injEq] at h
    obtain ⟨C, hC⟩ := toPath_comp_eq_cons hβ (hδ.trans hγ) (bot_lt_coe _) c.1 (B.cons hδ) h.1
    exact Or.inr (toPath_comp_eq_cons hβ hγ hδ C B hC.symm)
  · exact Or.inl (coe_injective (le_antisymm (le_of_path B) (le_of_not_lt hγ)))

theorem eq_raiseIndex_of_zero_lt_length {β : Λ} {δ : TypeIndex}
    {A : Path (β : TypeIndex) δ} (h : 0 < A.length) :
    ∃ (γ : TypeIndex) (hγ : γ < β) (B : Path (γ : TypeIndex) δ),
    A = (Hom.toPath hγ).comp B := by
  induction' A with ε ζ A hε ih
  · cases h
  · cases' A with η _ A hη
    · exact ⟨ζ, hε, Path.nil, rfl⟩
    · obtain ⟨γ, hγ, B, hB⟩ := ih (Nat.zero_lt_succ _)
      refine ⟨γ, hγ, B.cons hε, ?_⟩
      rw [hB]
      rfl

theorem eq_raiseIndex_of_one_lt_length {β : Λ} {A : ExtendedIndex β} (h : 1 < A.length) :
    ∃ (γ : Λ) (hγ : (γ : TypeIndex) < β) (B : ExtendedIndex γ),
    A = (Hom.toPath hγ).comp B := by
  obtain ⟨γ, hγ, B, hB⟩ := eq_raiseIndex_of_zero_lt_length (zero_lt_one.trans h)
  induction γ using recBotCoe
  · cases path_eq_nil B
    cases hB
    cases (lt_self_iff_false _).mp h
  · exact ⟨_, hγ, B, hB⟩

theorem eq_raise_of_one_lt_length {c : Address β} (h : 1 < c.path.length) :
    ∃ (γ : Λ) (hγ : (γ : TypeIndex) < β) (d : Address γ), c = raise hγ d := by
  obtain ⟨γ, hγ, B, hB⟩ := eq_raiseIndex_of_one_lt_length h
  exact ⟨γ, hγ, ⟨B, c.value⟩, Address.ext _ _ hB rfl⟩

theorem zero_lt_length (A : ExtendedIndex γ) : 0 < A.length := by
  by_contra h
  simp only [not_lt, nonpos_iff_eq_zero] at h
  cases Path.eq_of_length_zero _ h

theorem precedes_raise {c : Address β} {d : Address γ} (h : Precedes c (raise hγ d)) :
    1 < c.path.length ∨ ∃ a, c = ⟨Hom.toPath (bot_lt_coe _), inl a⟩ := by
  rw [precedes_iff] at h
  obtain (⟨A, N, h, e, -, hc, -⟩ | ⟨A, N, h, hc, hd⟩) := h
  · rw [hc]
    refine Or.inl ?_
    simp only [Path.length_comp, Path.length_cons]
    have := zero_lt_length e.path
    linarith
  · obtain (h' | ⟨C, hC⟩) := raise_eq_cons_cons _ _ _ _ _ hd
    · obtain ⟨⟨γ, ε, hε, B, hB⟩, a, hL⟩ := h
      dsimp only at h'
      cases h'
      cases path_eq_nil B
      rw [hc]
      exact Or.inr ⟨_, rfl⟩
    · rw [hc, hC]
      refine Or.inl ?_
      simp only [Path.length_cons, Path.length_comp, lt_add_iff_pos_left, add_pos_iff]
      exact Or.inl zero_lt_one

@[simp]
theorem raiseIndex_length (A : ExtendedIndex γ) :
    (raiseIndex hγ A).length = A.length + 1 := by
  rw [raiseIndex, Path.length_comp]
  exact add_comm _ _

theorem precClosure_raise_spec (T : Support γ) (c : Address β)
    (h : c ∈ precClosure (T.image (raise hγ))) :
    1 < c.path.length ∨ ∃ a, c = ⟨Hom.toPath (bot_lt_coe _), inl a⟩ := by
  obtain ⟨d, hd, hc⟩ := h
  induction' hc using Relation.ReflTransGen.head_induction_on with c' d' hcc' hcd' ih
  case refl =>
    simp only [Enumeration.image_carrier, Set.mem_image] at hd
    obtain ⟨d, _, rfl⟩ := hd
    refine Or.inl ?_
    simp only [raise_path, raiseIndex_length, lt_add_iff_pos_left]
    exact zero_lt_length d.path
  case head =>
    obtain (ih | ⟨a, rfl⟩) := ih
    · obtain ⟨δ, hδ, d, rfl⟩ := eq_raise_of_one_lt_length ih
      exact precedes_raise _ hcc'
    · simp only [not_precedes_atom] at hcc'

theorem strongSupport_raise_spec (T : Support γ) (c : Address β)
    (h : c ∈ strongSupport (T.image (raise hγ)).small) :
    1 < c.path.length ∨ ∃ a : Atom, c = ⟨Hom.toPath (bot_lt_coe _), inl a⟩ := by
  obtain ⟨i, hi, hc⟩ := h
  have := mem_of_strongSupport_f_eq (T.image (raise hγ)).small hi
  rw [← hc] at this
  obtain (⟨A, a, N₁, N₂, hN₁, _, _, rfl⟩ | h) := this
  · obtain (h | h) := precClosure_raise_spec hγ T _ hN₁
    · exact Or.inl h
    · simp only [Address.mk.injEq, and_false, exists_const] at h
  · exact precClosure_raise_spec hγ T c h

theorem path_eq_nil' {α β : TypeIndex} (h : α = β) (p : Quiver.Path α β) : Path.length p = 0 := by
  cases h
  cases path_eq_nil p
  rfl

theorem raise_raise_strong (T : Support γ) :
    Support.Strong ((strongSupport (T.image (raise hγ)).small).image (raise iβ.elim)) := by
  constructor
  · intro i₁ i₂ hi₁ hi₂ A N₁ N₂ hN₁ hN₂ a ha
    rw [Enumeration.image_f] at hN₁ hN₂
    have := (strongSupport_strong (T.image (raise hγ)).small).interferes hi₁ hi₂
        (A := ((strongSupport (T.image (raise hγ)).small).f i₁ hi₁).path) ?_ ?_ ha
    · obtain ⟨j, hj, hji₁, hji₂, hj'⟩ := this
      refine ⟨j, hj, hji₁, hji₂, ?_⟩
      rw [Enumeration.image_f, hj']
      refine Address.ext _ _ ?_ rfl
      have := congr_arg Address.path hN₁
      exact this
    · refine Address.ext _ _ rfl ?_
      have := congr_arg Address.value hN₁
      exact this
    · refine Address.ext _ _ ?_ ?_
      · have h₁ := congr_arg Address.path hN₁
        have h₂ := congr_arg Address.path hN₂
        exact raiseIndex_injective _ (h₂.trans h₁.symm)
      · have := congr_arg Address.value hN₂
        exact this
  · intro i hi c hc
    rw [precedes_iff] at hc
    obtain (⟨A, N, h, d, hd, rfl, hc⟩ | ⟨A, N, h, rfl, hc⟩) := hc
    · obtain (hc' | ⟨a, ha⟩) := strongSupport_raise_spec hγ T _ ⟨i, hi, rfl⟩
      · obtain (hc'' | ⟨C, hC⟩) := raise_eq_cons_cons _ _ _ _ _ hc
        · have := congr_arg Path.length (congr_arg Address.path hc)
          rw [Path.length_cons, Path.length_cons, Enumeration.image_f, raise_path,
            raiseIndex_length, path_eq_nil' (coe_inj.mpr hc''.symm) h.path.B, add_left_inj] at this
          rw [this, lt_self_iff_false] at hc'
          cases hc'
        · obtain ⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t, hL⟩ := h
          rw [hC, Enumeration.image_f, ← Path.comp_cons, ← Path.comp_cons] at hc
          change raise iβ.elim _ = raise iβ.elim ⟨(C.cons hε).cons (bot_lt_coe _), inr N⟩ at hc
          have := (strongSupport_strong (T.image (raise hγ)).small).precedes hi
            ⟨(C.cons hδ).comp d.path, d.value⟩ ?_
          · obtain ⟨j, hj₁, hj₂, hj₃⟩ := this
            refine ⟨j, hj₁, hj₂, ?_⟩
            rw [Enumeration.image_f, hj₃, hC, raise, Hom.toPath, raiseIndex,
              ← Path.comp_cons, Path.comp_assoc]
            rfl
          · rw [raise_injective _ hc]
            exact Precedes.fuzz ((C.cons hε).cons (bot_lt_coe _)) N
              ⟨⟨γ, δ, ε, hδ, hε, hδε, _, rfl⟩, t, hL⟩ d hd
      · have h₁ := congr_arg Address.value hc
        have h₂ := congr_arg Address.value ha
        cases h₁.symm.trans h₂
    · obtain (hc' | ⟨a, ha⟩) := strongSupport_raise_spec hγ T _ ⟨i, hi, rfl⟩
      · obtain (hc'' | ⟨C, hC⟩) := raise_eq_cons_cons _ _ _ _ _ hc
        · have := congr_arg Path.length (congr_arg Address.path hc)
          rw [Path.length_cons, Path.length_cons, Enumeration.image_f, raise_path,
            raiseIndex_length, path_eq_nil' (coe_inj.mpr hc''.symm) h.path.B, add_left_inj] at this
          rw [this, lt_self_iff_false] at hc'
          cases hc'
        · obtain ⟨⟨γ, ε, hε, A, rfl⟩, a, hL⟩ := h
          rw [hC, Enumeration.image_f, ← Path.comp_cons, ← Path.comp_cons] at hc
          change raise iβ.elim _ = raise iβ.elim ⟨(C.cons hε).cons (bot_lt_coe _), inr N⟩ at hc
          have := (strongSupport_strong (T.image (raise hγ)).small).precedes hi
            ⟨C.cons (bot_lt_coe _), inl a⟩ ?_
          · obtain ⟨j, hj₁, hj₂, hj₃⟩ := this
            refine ⟨j, hj₁, hj₂, ?_⟩
            rw [Enumeration.image_f, hj₃, hC]
            rfl
          · rw [raise_injective _ hc]
            exact Precedes.fuzzBot ((C.cons hε).cons (bot_lt_coe _)) N
              ⟨⟨γ, ε, hε, _, rfl⟩, a, hL⟩
      · have h₁ := congr_arg Address.value hc
        have h₂ := congr_arg Address.value ha
        cases h₁.symm.trans h₂

end ConNF.Support
