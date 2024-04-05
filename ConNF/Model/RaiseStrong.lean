import ConNF.Model.FOA

open Quiver Sum WithBot

open scoped Cardinal Pointwise symmDiff

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

theorem raise_smul_raise_strong (T : Support γ) (ρ : Allowable β) :
    Support.Strong ((ρ • strongSupport (T.image (raise hγ)).small).image (raise iβ.elim)) := by
  constructor
  · intro i₁ i₂ hi₁ hi₂ A N₁ N₂ hN₁ hN₂ a ha
    rw [Enumeration.image_f] at hN₁ hN₂
    have := (strongSupport_strong (T.image (raise hγ)).small).interferes hi₁ hi₂
        (A := ((strongSupport (T.image (raise hγ)).small).f i₁ hi₁).path) ?_ ?_
        (ha.smul (Allowable.toStructPerm ρ⁻¹
          ((strongSupport (T.image (raise hγ)).small).f i₁ hi₁).path))
    · obtain ⟨j, hj, hji₁, hji₂, hj'⟩ := this
      refine ⟨j, hj, hji₁, hji₂, ?_⟩
      rw [Enumeration.image_f, Enumeration.smul_f, hj']
      refine Address.ext _ _ ?_ ?_
      · have := congr_arg Address.path hN₁
        exact this
      · simp only [map_inv, Tree.inv_apply, Allowable.smul_address,
          smul_inl, smul_inv_smul, raise_value]
    · refine Address.ext _ _ rfl ?_
      have := congr_arg Address.value hN₁
      rw [Enumeration.smul_f, Allowable.smul_address, raise_value, smul_eq_iff_eq_inv_smul] at this
      simp only [this, smul_inr, map_inv, Tree.inv_apply]
    · refine Address.ext _ _ ?_ ?_
      · have h₁ := congr_arg Address.path hN₁
        have h₂ := congr_arg Address.path hN₂
        exact raiseIndex_injective _ (h₂.trans h₁.symm)
      · have := congr_arg Address.value hN₂
        rw [Enumeration.smul_f, Allowable.smul_address, raise_value,
          smul_eq_iff_eq_inv_smul] at this
        simp only [this, smul_inr, map_inv, Tree.inv_apply]
        have h₁ := congr_arg Address.path hN₁
        have h₂ := congr_arg Address.path hN₂
        have := raiseIndex_injective _ (h₂.trans h₁.symm)
        simp only [Enumeration.smul_f, Allowable.smul_address] at this
        rw [this]
  · intro i hi c hc
    rw [precedes_iff] at hc
    obtain (⟨A, N, h, d, hd, rfl, hc⟩ | ⟨A, N, h, rfl, hc⟩) := hc
    · obtain (hc' | ⟨a, ha⟩) := strongSupport_raise_spec hγ T _ ⟨i, hi, rfl⟩
      · obtain (hc'' | ⟨C, hC⟩) := raise_eq_cons_cons _ _ _ _ _ hc
        · have := congr_arg Path.length (congr_arg Address.path hc)
          rw [Path.length_cons, Path.length_cons, Enumeration.image_f, raise_path,
            raiseIndex_length, path_eq_nil' (coe_inj.mpr hc''.symm) h.path.B, add_left_inj,
            Enumeration.smul_f, Allowable.smul_address] at this
          rw [this, lt_self_iff_false] at hc'
          cases hc'
        · obtain ⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t, hL⟩ := h
          rw [hC, Enumeration.image_f, ← Path.comp_cons, ← Path.comp_cons] at hc
          change raise iβ.elim _ = raise iβ.elim ⟨(C.cons hε).cons (bot_lt_coe _), inr N⟩ at hc
          have := (strongSupport_strong (T.image (raise hγ)).small).precedes hi
            (ρ⁻¹ • ⟨(C.cons hδ).comp d.path, d.value⟩) ?_
          · obtain ⟨j, hj₁, hj₂, hj₃⟩ := this
            refine ⟨j, hj₁, hj₂, ?_⟩
            rw [Enumeration.image_f, Enumeration.smul_f, hj₃, hC, raise, Hom.toPath, raiseIndex,
              ← Path.comp_cons, Path.comp_assoc, smul_inv_smul]
            rfl
          · have := raise_injective _ hc
            rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at this
            rw [this]
            exact (Precedes.fuzz ((C.cons hε).cons (bot_lt_coe _)) N
              ⟨⟨γ, δ, ε, hδ, hε, hδε, _, rfl⟩, t, hL⟩ d hd).smul ρ⁻¹
      · have h₁ := congr_arg Address.value hc
        rw [Enumeration.image_f, Enumeration.smul_f, raise_value, Allowable.smul_address,
          smul_eq_iff_eq_inv_smul] at h₁
        have h₂ := congr_arg Address.value ha
        cases h₁.symm.trans h₂
    · obtain (hc' | ⟨a, ha⟩) := strongSupport_raise_spec hγ T _ ⟨i, hi, rfl⟩
      · obtain (hc'' | ⟨C, hC⟩) := raise_eq_cons_cons _ _ _ _ _ hc
        · have := congr_arg Path.length (congr_arg Address.path hc)
          rw [Path.length_cons, Path.length_cons, Enumeration.image_f, raise_path,
            raiseIndex_length, path_eq_nil' (coe_inj.mpr hc''.symm) h.path.B, add_left_inj,
            Enumeration.smul_f, Allowable.smul_address] at this
          rw [this, lt_self_iff_false] at hc'
          cases hc'
        · obtain ⟨⟨γ, ε, hε, A, rfl⟩, a, hL⟩ := h
          rw [hC, Enumeration.image_f, ← Path.comp_cons, ← Path.comp_cons] at hc
          change raise iβ.elim _ = raise iβ.elim ⟨(C.cons hε).cons (bot_lt_coe _), inr N⟩ at hc
          have := (strongSupport_strong (T.image (raise hγ)).small).precedes hi
            (ρ⁻¹ • ⟨C.cons (bot_lt_coe _), inl a⟩) ?_
          · obtain ⟨j, hj₁, hj₂, hj₃⟩ := this
            refine ⟨j, hj₁, hj₂, ?_⟩
            rw [Enumeration.image_f, Enumeration.smul_f, hj₃, hC, smul_inv_smul]
            rfl
          · have := raise_injective _ hc
            rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at this
            rw [this]
            exact (Precedes.fuzzBot ((C.cons hε).cons (bot_lt_coe _)) N
              ⟨⟨γ, ε, hε, _, rfl⟩, a, hL⟩).smul ρ⁻¹
      · have h₁ := congr_arg Address.value hc
        rw [Enumeration.image_f, Enumeration.smul_f, raise_value, Allowable.smul_address,
          smul_eq_iff_eq_inv_smul] at h₁
        have h₂ := congr_arg Address.value ha
        cases h₁.symm.trans h₂

def interference (S : Support α) (T : Support γ) : Set (Address β) :=
  {c | ∃ A : ExtendedIndex β, ∃ a : Atom, ∃ N₁ N₂ : NearLitter, c = ⟨A, inl a⟩ ∧
    raise iβ.elim ⟨A, inr N₁⟩ ∈ S ∧ ⟨A, inr N₂⟩ ∈ strongSupport (T.image (raise hγ)).small ∧
    Interferes a N₁ N₂}

def interference' (S : Support α) (T : Support γ) : Set (Address β) :=
  ⋃ (A : ExtendedIndex β) (N₁ ∈ {N | raise iβ.elim ⟨A, inr N⟩ ∈ S})
    (N₂ ∈ {N | ⟨A, inr N⟩ ∈ strongSupport (T.image (raise hγ)).small})
    (a ∈ {a | Interferes a N₁ N₂}),
    {⟨A, inl a⟩}

theorem interference_eq_interference' (S : Support α) (T : Support γ) :
    interference hγ S T = interference' hγ S T := by
  rw [interference, interference']
  aesop

theorem interference_small {S : Support α} {T : Support γ} : Small (interference hγ S T) := by
  rw [interference_eq_interference']
  refine small_iUnion ?_ (fun A => ?_)
  · exact (mk_extendedIndex β).trans_lt Params.Λ_lt_κ
  refine Small.bUnion ?_ (fun N₁ _ => ?_)
  · refine S.small.preimage ?_
    intro N₁ N₂ h
    cases h
    rfl
  refine Small.bUnion ?_ (fun N₂ _ => ?_)
  · refine (strongSupport (T.image (raise hγ)).small).small.preimage ?_
    intro N₁ N₂ h
    cases h
    rfl
  refine Small.bUnion (interferes_small _ _) (fun a _ => ?_)
  exact small_singleton _

def interferenceSupport (S : Support α) (T : Support γ) : Support β :=
  Enumeration.ofSet (interference hγ S T) (interference_small hγ)

theorem mem_interferenceSupport_iff (S : Support α) (T : Support γ) (c : Address β) :
    c ∈ interferenceSupport hγ S T ↔ c ∈ interference hγ S T :=
  Enumeration.mem_ofSet_iff _ _ _

theorem interferenceSupport_ne_nearLitter {S : Support α} {T : Support γ}
    {N : NearLitter} {i : κ} (hi : i < (interferenceSupport hγ S T).max) :
    ((interferenceSupport hγ S T).f i hi).value ≠ inr N := by
  intro h
  have := (mem_interferenceSupport_iff hγ S T ⟨_, inr N⟩).mp ⟨i, hi, Address.ext _ _ rfl h.symm⟩
  rw [interference] at this
  simp only [Enumeration.image_carrier, exists_and_left, Set.mem_setOf_eq, Address.mk.injEq,
    and_false, false_and, exists_const] at this

theorem interferenceSupport_eq_atom {S : Support α} {T : Support γ}
    {i : κ} (hi : i < (interferenceSupport hγ S T).max) :
    ∃ A a, (interferenceSupport hγ S T).f i hi = ⟨A, inl a⟩ := by
  set c := (interferenceSupport hγ S T).f i hi with hc
  obtain ⟨A, a | N⟩ := c
  · exact ⟨A, a, rfl⟩
  · have := interferenceSupport_ne_nearLitter hγ hi (N := N)
    rw [← hc] at this
    cases this rfl

def raiseRaise (S : Support α) (T : Support γ) (ρ : Allowable β) : Support α :=
    ((ρ • interferenceSupport hγ S T).image (raise iβ.elim)) +
      S + ((ρ • strongSupport (T.image (raise hγ)).small).image (raise iβ.elim))

variable {hγ} {S : Support α} {T : Support γ} {ρ : Allowable β}

theorem raiseRaise_max : (raiseRaise hγ S T ρ).max =
    (interferenceSupport hγ S T).max + S.max + (strongSupport (T.image (raise hγ)).small).max :=
  rfl

theorem raiseRaise_f_eq₁ {i : κ} (hi : i < (interferenceSupport hγ S T).max) :
    (raiseRaise hγ S T ρ).f i ((hi.trans_le (κ_le_self_add _ _)).trans_le (κ_le_self_add _ _)) =
    raise iβ.elim (ρ • (interferenceSupport hγ S T).f i hi) := by
  unfold raiseRaise
  rw [Enumeration.add_f_left (by exact hi.trans_le (κ_le_self_add _ _)),
    Enumeration.add_f_left (by exact hi)]
  rfl

theorem raiseRaise_f_eq₂ {i : κ} (hi₁ : (interferenceSupport hγ S T).max ≤ i)
    (hi₂ : i < (interferenceSupport hγ S T).max + S.max) :
    (raiseRaise hγ S T ρ).f i (hi₂.trans_le (κ_le_self_add _ _)) =
    S.f (i - (interferenceSupport hγ S T).max) (κ_sub_lt hi₂ hi₁) := by
  unfold raiseRaise
  rw [Enumeration.add_f_left (by exact hi₂), Enumeration.add_f_right (by exact hi₂) (by exact hi₁)]
  rfl

theorem raiseRaise_f_eq₃ {i : κ} (hi₁ : (interferenceSupport hγ S T).max + S.max ≤ i)
    (hi₂ : i < (raiseRaise hγ S T ρ).max) :
    (raiseRaise hγ S T ρ).f i hi₂ =
    raise iβ.elim (ρ • (strongSupport (T.image (raise hγ)).small).f
      (i - ((interferenceSupport hγ S T).max + S.max)) (κ_sub_lt hi₂ hi₁)) := by
  unfold raiseRaise
  rw [Enumeration.add_f_right (by exact hi₂) (by exact hi₁)]
  rfl

theorem raiseRaise_cases {i : κ} (hi : i < (raiseRaise hγ S T ρ).max) :
    (i < (interferenceSupport hγ S T).max) ∨
    ((interferenceSupport hγ S T).max ≤ i ∧ i < (interferenceSupport hγ S T).max + S.max) ∨
    ((interferenceSupport hγ S T).max + S.max ≤ i ∧ i < (raiseRaise hγ S T ρ).max) := by
  by_cases h₁ : i < (interferenceSupport hγ S T).max
  · exact Or.inl h₁
  by_cases h₂ : i < (interferenceSupport hγ S T).max + S.max
  · exact Or.inr (Or.inl ⟨le_of_not_lt h₁, h₂⟩)
  · exact Or.inr (Or.inr ⟨le_of_not_lt h₂, hi⟩)

variable (hS : S.Strong)

theorem raiseIndex_of_raise_eq {c : Address β} {d : Address α} (h : raise iβ.elim c = d) :
    ∃ A, raiseIndex iβ.elim A = d.path :=
  ⟨c.path, congr_arg Address.path h⟩

theorem raise_injective' {c : Address γ} {A : ExtendedIndex γ} {x : Atom ⊕ NearLitter}
    (h : raise hγ c = ⟨raiseIndex hγ A, x⟩) : c = ⟨A, x⟩ := by
  refine Address.ext _ _ ?_ ?_
  · exact raiseIndex_injective hγ (congr_arg Address.path h)
  · have := congr_arg Address.value h
    exact this

theorem raiseRaise_strong (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c) :
    (raiseRaise hγ S T ρ).Strong := by
  constructor
  · intro i₁ i₂ hi₁ hi₂ A N₁ N₂ hN₁ hN₂ a ha
    obtain (hi₁ | ⟨hi₁, hi₁'⟩ | ⟨hi₁, hi₁'⟩) := raiseRaise_cases hi₁
    · rw [raiseRaise_f_eq₁ hi₁] at hN₁
      simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul] at hN₁
      cases interferenceSupport_ne_nearLitter hγ hi₁ hN₁.2
    · rw [raiseRaise_f_eq₂ hi₁ hi₁'] at hN₁
      obtain (hi₂ | ⟨hi₂, hi₂'⟩ | ⟨hi₂, hi₂'⟩) := raiseRaise_cases hi₂
      · rw [raiseRaise_f_eq₁ hi₂] at hN₂
        simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul] at hN₂
        cases interferenceSupport_ne_nearLitter hγ hi₂ hN₂.2
      · rw [raiseRaise_f_eq₂ hi₂ hi₂'] at hN₂
        obtain ⟨j, hj, hj₁, hj₂, hj'⟩ := hS.interferes _ _ hN₁ hN₂ ha
        refine ⟨(interferenceSupport hγ S T).max + j, ?_, ?_, ?_, ?_⟩
        · rw [raiseRaise_max, add_assoc]
          refine add_lt_add_left ?_ _
          exact hj.trans_le (κ_le_self_add _ _)
        · rwa [← κ_lt_sub_iff]
        · rwa [← κ_lt_sub_iff]
        · rw [raiseRaise_f_eq₂]
          · simp_rw [κ_add_sub_cancel]
            exact hj'
          · rw [le_add_iff_nonneg_right]
            exact κ_pos _
          · rwa [add_lt_add_iff_left]
      · rw [raiseRaise_f_eq₃ hi₂ hi₂'] at hN₂
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hN₂
        have := raise_injective' hN₂
        rw [smul_eq_iff_eq_inv_smul] at this
        have := (mem_interferenceSupport_iff hγ S T ⟨A, inl (Allowable.toStructPerm ρ⁻¹ A • a)⟩).mpr
          ⟨A, _, N₁, _, rfl, ⟨_, _, hN₁.symm⟩, ⟨_, _, this.symm⟩, ?_⟩
        · obtain ⟨j, hj, hj'⟩ := this
          refine ⟨j, ?_, ?_, ?_, ?_⟩
          · rw [raiseRaise_max, add_assoc]
            exact hj.trans_le (κ_le_self_add _ _)
          · exact hj.trans_le hi₁
          · exact hj.trans_le ((κ_le_self_add _ _).trans hi₂)
          · rw [raiseRaise_f_eq₁ hj, ← hj', Allowable.smul_address]
            simp only [map_inv, Tree.inv_apply, smul_inl, smul_inv_smul]
            rfl
        · convert ha.smul (Allowable.toStructPerm ρ⁻¹ A) using 1
          have := hρS ⟨A, inr N₁⟩ ⟨_, _, hN₁.symm⟩
          simp only [Allowable.smul_address, smul_inr, Address.mk.injEq, inr.injEq, true_and]
            at this
          rw [map_inv, Tree.inv_apply, eq_inv_smul_iff, this]
    · rw [raiseRaise_f_eq₃ hi₁ hi₁'] at hN₁
      obtain (hi₂ | ⟨hi₂, hi₂'⟩ | ⟨hi₂, hi₂'⟩) := raiseRaise_cases hi₂
      · rw [raiseRaise_f_eq₁ hi₂] at hN₂
        simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul] at hN₂
        cases interferenceSupport_ne_nearLitter hγ hi₂ hN₂.2
      · rw [raiseRaise_f_eq₂ hi₂ hi₂'] at hN₂
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hN₁
        have := raise_injective' hN₁
        rw [smul_eq_iff_eq_inv_smul] at this
        have := (mem_interferenceSupport_iff hγ S T ⟨A, inl (Allowable.toStructPerm ρ⁻¹ A • a)⟩).mpr
          ⟨A, _, _, _, rfl, ⟨_, _, hN₂.symm⟩, ⟨_, _, this.symm⟩, ?_⟩
        · obtain ⟨j, hj, hj'⟩ := this
          refine ⟨j, ?_, ?_, ?_, ?_⟩
          · rw [raiseRaise_max, add_assoc]
            exact hj.trans_le (κ_le_self_add _ _)
          · exact hj.trans_le ((κ_le_self_add _ _).trans hi₁)
          · exact hj.trans_le hi₂
          · rw [raiseRaise_f_eq₁ hj, ← hj', Allowable.smul_address]
            simp only [map_inv, Tree.inv_apply, smul_inl, smul_inv_smul]
            rfl
        · convert ha.symm.smul (Allowable.toStructPerm ρ⁻¹ A) using 1
          have := hρS ⟨A, inr N₂⟩ ⟨_, _, hN₂.symm⟩
          simp only [Allowable.smul_address, smul_inr, Address.mk.injEq, inr.injEq, true_and]
            at this
          rw [map_inv, Tree.inv_apply, eq_inv_smul_iff, this]
      · rw [raiseRaise_f_eq₃ hi₂ hi₂'] at hN₂
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hN₂
        have hN₁' := raise_injective' hN₁
        have hN₂' := raise_injective' hN₂
        rw [smul_eq_iff_eq_inv_smul] at hN₁' hN₂'
        obtain ⟨j, hj, hj₁, hj₂, hj'⟩ :=
          (strongSupport_strong (T.image (raise hγ)).small).interferes _ _ hN₁' hN₂' (ha.smul _)
        refine ⟨(interferenceSupport hγ S T).max + S.max + j, ?_, ?_, ?_, ?_⟩
        · rw [raiseRaise_max]
          exact add_lt_add_left hj _
        · rw [κ_lt_sub_iff] at hj₁
          refine lt_of_le_of_lt ?_ hj₁
          rw [add_assoc, add_le_add_iff_left]
        · rw [κ_lt_sub_iff] at hj₂
          refine lt_of_le_of_lt ?_ hj₂
          rw [add_assoc, add_le_add_iff_left]
        · rw [raiseRaise_f_eq₃]
          · simp_rw [κ_add_sub_cancel]
            rw [hj']
            simp only [map_inv, Tree.inv_apply, Allowable.smul_address, smul_inl, smul_inv_smul]
            rfl
          · rw [le_add_iff_nonneg_right]
            exact κ_pos _
  · intro i hi c hc
    obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
    · rw [raiseRaise_f_eq₁ hi] at hc
      obtain ⟨A, a, ha⟩ := interferenceSupport_eq_atom hγ hi
      rw [ha] at hc
      cases not_precedes_atom hc
    · rw [raiseRaise_f_eq₂ hi hi'] at hc
      obtain ⟨j, hj₁, hj₂, hj₃⟩ := hS.precedes _ _ hc
      refine ⟨(interferenceSupport hγ S T).max + j, ?_, ?_, ?_⟩
      · rw [raiseRaise_max, add_assoc, add_lt_add_iff_left]
        exact hj₁.trans_le (κ_le_self_add _ _)
      · rwa [κ_lt_sub_iff] at hj₂
      · rw [raiseRaise_f_eq₂]
        · simp_rw [κ_add_sub_cancel]
          exact hj₃
        · exact κ_le_self_add _ _
        · rwa [add_lt_add_iff_left]
    · rw [raiseRaise_f_eq₃ hi hi'] at hc
      obtain ⟨j, hj₁, hj₂, hj₃⟩ := (raise_smul_raise_strong hγ T ρ).precedes _ _ hc
      refine ⟨(interferenceSupport hγ S T).max + S.max + j, ?_, ?_, ?_⟩
      · rwa [raiseRaise_max, add_lt_add_iff_left]
      · rwa [κ_lt_sub_iff] at hj₂
      · rw [raiseRaise_f_eq₃]
        · simp_rw [κ_add_sub_cancel]
          exact hj₃
        · exact κ_le_self_add _ _

theorem raiseRaise_max_eq_max : (raiseRaise hγ S T 1).max = (raiseRaise hγ S T ρ).max := rfl

theorem raiseRaise_f_eq_atom (i : κ) (hi : i < (raiseRaise hγ S T ρ).max)
    (A : ExtendedIndex α) (a : Atom) (ha : (raiseRaise hγ S T ρ).f i hi = ⟨A, inl a⟩) :
    ∃ b, (raiseRaise hγ S T 1).f i hi = ⟨A, inl b⟩ := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · rw [raiseRaise_f_eq₁ hi] at ha ⊢
    simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul, smul_inl,
      one_smul] at ha ⊢
    exact ⟨_, ha⟩
  · rw [raiseRaise_f_eq₂ hi hi'] at ha ⊢
    exact ⟨a, ha⟩
  · rw [raiseRaise_f_eq₃ hi hi'] at ha
    rw [raiseRaise_f_eq₃ hi (by exact hi')]
    simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul, smul_inl,
      one_smul] at ha ⊢
    exact ⟨_, ha⟩

theorem raiseRaise_f_eq_nearLitter (i : κ) (hi : i < (raiseRaise hγ S T ρ).max)
    (A : ExtendedIndex α) (N : NearLitter) (hN : (raiseRaise hγ S T ρ).f i hi = ⟨A, inr N⟩) :
    ∃ N', (raiseRaise hγ S T 1).f i hi = ⟨A, inr N'⟩ := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · rw [raiseRaise_f_eq₁ hi] at hN ⊢
    simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul, smul_inr,
      one_smul] at hN ⊢
    exact ⟨_, hN⟩
  · rw [raiseRaise_f_eq₂ hi hi'] at hN ⊢
    exact ⟨N, hN⟩
  · rw [raiseRaise_f_eq₃ hi hi'] at hN
    rw [raiseRaise_f_eq₃ hi (by exact hi')]
    simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul, smul_inr,
      one_smul] at hN ⊢
    exact ⟨_, hN⟩

theorem raiseRaise_f_eq_atom' (i : κ) (hi : i < (raiseRaise hγ S T ρ).max)
    (A : ExtendedIndex α) (a : Atom) (ha : (raiseRaise hγ S T 1).f i hi = ⟨A, inl a⟩) :
    ∃ b, (raiseRaise hγ S T ρ).f i hi = ⟨A, inl b⟩ := by
  set c := (raiseRaise hγ S T ρ).f i hi with hc
  obtain ⟨B, b | N⟩ := c
  · obtain ⟨b, hb⟩ := raiseRaise_f_eq_atom i hi B b hc.symm
    cases hb.symm.trans ha
    exact ⟨_, rfl⟩
  · obtain ⟨N, hN⟩ := raiseRaise_f_eq_nearLitter i hi B N hc.symm
    cases hN.symm.trans ha

theorem raiseRaise_f_eq_nearLitter' (i : κ) (hi : i < (raiseRaise hγ S T ρ).max)
    (A : ExtendedIndex α) (N : NearLitter) (hN : (raiseRaise hγ S T 1).f i hi = ⟨A, inr N⟩) :
    ∃ N', (raiseRaise hγ S T ρ).f i hi = ⟨A, inr N'⟩ := by
  set c := (raiseRaise hγ S T ρ).f i hi with hc
  obtain ⟨B, a | N'⟩ := c
  · obtain ⟨a, ha⟩ := raiseRaise_f_eq_atom i hi B a hc.symm
    cases ha.symm.trans hN
  · obtain ⟨N'', hN''⟩ := raiseRaise_f_eq_nearLitter i hi B N' hc.symm
    cases hN''.symm.trans hN
    exact ⟨_, rfl⟩

theorem raiseRaise_eq_cases {i : κ} {hi : i < (raiseRaise hγ S T ρ).max} {c : Address α}
    (h : (raiseRaise hγ S T ρ).f i hi = c) :
    (∃ d, c = raise iβ.elim (ρ • d) ∧ (raiseRaise hγ S T 1).f i hi = raise iβ.elim d) ∨
    (c ∈ S ∧ (raiseRaise hγ S T 1).f i hi = c) := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · rw [raiseRaise_f_eq₁ hi] at h ⊢
    refine Or.inl ⟨_, h.symm, ?_⟩
    rw [one_smul]
  · refine Or.inr ?_
    rw [raiseRaise_f_eq₂ hi hi'] at h ⊢
    exact ⟨⟨_, _, h.symm⟩, h⟩
  · rw [raiseRaise_f_eq₃ hi (by exact hi')] at h ⊢
    refine Or.inl ⟨_, h.symm, ?_⟩
    rw [one_smul]

theorem raiseRaise_atom_spec₁' (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c)
    {A : ExtendedIndex α} {a b : Atom} {c : Address β}
    (ha : raise iβ.elim (ρ • c) = ⟨A, inl a⟩)
    (hb : raise iβ.elim ((1 : Allowable β) • c) = ⟨A, inl b⟩) :
    {j | ∃ hj, (raiseRaise hγ S T 1).f j hj = ⟨A, inl b⟩} =
    {j | ∃ hj, (raiseRaise hγ S T ρ).f j hj = ⟨A, inl a⟩} := by
  obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq ha
  have ha := raise_injective' ha
  have hb := raise_injective' hb
  rw [one_smul] at hb
  ext j : 1
  constructor
  · rintro ⟨hj₁, hj₂⟩
    refine ⟨hj₁, ?_⟩
    refine Eq.trans ?_ (congr_arg (raise iβ.elim) ha)
    rw [hb]
    obtain (hj | ⟨hj, hj'⟩ | ⟨hj, hj'⟩) := raiseRaise_cases hj₁
    · rw [raiseRaise_f_eq₁ hj] at hj₂ ⊢
      have := raise_injective' hj₂
      rw [one_smul] at this
      rw [this]
    · rw [raiseRaise_f_eq₂ hj hj'] at hj₂ ⊢
      rw [hj₂, hρS ⟨A, inl b⟩ ⟨_, _, hj₂.symm⟩, raise]
    · rw [raiseRaise_f_eq₃ hj (by exact hj')] at hj₂ ⊢
      have := raise_injective' hj₂
      rw [one_smul] at this
      rw [this]
  · rintro ⟨hj₁, hj₂⟩
    refine ⟨hj₁, ?_⟩
    refine Eq.trans ?_ (congr_arg (raise iβ.elim) hb)
    rw [hb]
    obtain (hj | ⟨hj, hj'⟩ | ⟨hj, hj'⟩) := raiseRaise_cases hj₁
    · rw [raiseRaise_f_eq₁ hj] at hj₂ ⊢
      have := raise_injective' hj₂
      rw [smul_eq_iff_eq_inv_smul] at this
      rw [this, ← ha, hb, inv_smul_smul, one_smul]
    · rw [raiseRaise_f_eq₂ hj hj'] at hj₂ ⊢
      have := hρS ⟨A, inl a⟩ ⟨_, _, hj₂.symm⟩
      rw [smul_eq_iff_eq_inv_smul] at this
      rw [hj₂, ← hb]
      change raise _ ⟨A, inl a⟩ = _
      rw [this, ← ha, hb, inv_smul_smul]
    · rw [raiseRaise_f_eq₃ hj (by exact hj')] at hj₂ ⊢
      have := raise_injective' hj₂
      rw [smul_eq_iff_eq_inv_smul] at this
      rw [this, ← ha, hb, inv_smul_smul, one_smul]

theorem raiseRaise_atom_spec₁ (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c)
    {i : κ} (hi : i < (raiseRaise hγ S T ρ).max)
    {A : ExtendedIndex α} {a b : Atom}
    (ha : (raiseRaise hγ S T ρ).f i hi = ⟨A, inl a⟩)
    (hb : (raiseRaise hγ S T 1).f i hi = ⟨A, inl b⟩) :
    {j | ∃ hj, (raiseRaise hγ S T 1).f j hj = ⟨A, inl b⟩} =
    {j | ∃ hj, (raiseRaise hγ S T ρ).f j hj = ⟨A, inl a⟩} := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · rw [raiseRaise_f_eq₁ hi] at ha hb
    exact raiseRaise_atom_spec₁' hρS ha hb
  · rw [raiseRaise_f_eq₂ hi hi'] at ha hb
    rw [← ha, hb]
    ext j : 1
    constructor
    · rintro ⟨hj₁, hj₂⟩
      refine ⟨hj₁, Eq.trans ?_ hj₂⟩
      obtain (hj | ⟨hj, hj'⟩ | ⟨hj, hj'⟩) := raiseRaise_cases hj₁
      · rw [raiseRaise_f_eq₁ hj, raiseRaise_f_eq₁ hj]
        rw [raiseRaise_f_eq₁ hj] at hj₂
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hj₂
        have hj₂ := raise_injective' hj₂
        rw [one_smul] at hj₂
        rw [hj₂, hρS ⟨A, inl b⟩ ⟨_, _, hb.symm⟩, one_smul]
      · rw [raiseRaise_f_eq₂ hj hj', raiseRaise_f_eq₂ hj hj']
      · rw [raiseRaise_f_eq₃ hj hj', raiseRaise_f_eq₃ hj (by exact hj')]
        rw [raiseRaise_f_eq₃ hj hj'] at hj₂
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hj₂
        have hj₂ := raise_injective' hj₂
        rw [one_smul] at hj₂
        rw [hj₂, hρS ⟨A, inl b⟩ ⟨_, _, hb.symm⟩, one_smul]
    · rintro ⟨hj₁, hj₂⟩
      refine ⟨hj₁, Eq.trans ?_ hj₂⟩
      obtain (hj | ⟨hj, hj'⟩ | ⟨hj, hj'⟩) := raiseRaise_cases hj₁
      · rw [raiseRaise_f_eq₁ hj, raiseRaise_f_eq₁ hj]
        rw [raiseRaise_f_eq₁ hj] at hj₂
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hj₂
        have hj₂ := raise_injective' hj₂
        rw [smul_eq_iff_eq_inv_smul] at hj₂
        rw [hj₂, one_smul, smul_inv_smul]
        conv_lhs => rw [← hρS ⟨A, inl b⟩ ⟨_, _, hb.symm⟩, inv_smul_smul]
      · rw [raiseRaise_f_eq₂ hj hj', raiseRaise_f_eq₂ hj hj']
      · rw [raiseRaise_f_eq₃ hj hj', raiseRaise_f_eq₃ hj (by exact hj')]
        rw [raiseRaise_f_eq₃ hj hj'] at hj₂
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hj₂
        have hj₂ := raise_injective' hj₂
        rw [smul_eq_iff_eq_inv_smul] at hj₂
        rw [hj₂, one_smul, smul_inv_smul]
        conv_lhs => rw [← hρS ⟨A, inl b⟩ ⟨_, _, hb.symm⟩, inv_smul_smul]
  · rw [raiseRaise_f_eq₃ hi (by exact hi')] at ha hb
    exact raiseRaise_atom_spec₁' hρS ha hb

theorem raiseRaise_atom_spec₂' (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c)
    {A : ExtendedIndex α} {a b : Atom} {c : Address β}
    (ha : raise iβ.elim (ρ • c) = ⟨A, inl a⟩)
    (hb : raise iβ.elim ((1 : Allowable β) • c) = ⟨A, inl b⟩) :
    {j | ∃ hj, ∃ N, (raiseRaise hγ S T 1).f j hj = ⟨A, inr N⟩ ∧ b ∈ N} =
    {j | ∃ hj, ∃ N, (raiseRaise hγ S T ρ).f j hj = ⟨A, inr N⟩ ∧ a ∈ N} := by
  obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq ha
  have ha := raise_injective' ha
  have hb := raise_injective' hb
  rw [smul_eq_iff_eq_inv_smul] at ha
  rw [one_smul] at hb
  have := ha.symm.trans hb
  simp only [Allowable.smul_address, map_inv, Tree.inv_apply, smul_inl, Address.mk.injEq,
    inl.injEq, true_and] at this
  subst this
  ext j : 1
  constructor
  · rintro ⟨hj₁, N, hj₂, hN⟩
    obtain ⟨N', hN'⟩ := raiseRaise_f_eq_nearLitter' (ρ := ρ) j hj₁ _ _ hj₂
    refine ⟨hj₁, N', hN', ?_⟩
    obtain (hj | ⟨hj, hj'⟩ | ⟨hj, hj'⟩) := raiseRaise_cases hj₁
    · rw [raiseRaise_f_eq₁ hj] at hj₂ hN'
      have h₁ := raise_injective' hj₂
      have h₂ := raise_injective' hN'
      rw [one_smul] at h₁
      simp only [h₁, Allowable.smul_address, smul_inr, Address.mk.injEq, inr.injEq,
        true_and] at h₂
      rw [← h₂]
      exact hN
    · rw [raiseRaise_f_eq₂ hj hj'] at hj₂ hN'
      rw [hj₂] at hN'
      have := hρS ⟨A, inr N⟩ ⟨_, _, hj₂.symm⟩
      simp only [Allowable.smul_address, smul_inr, Address.mk.injEq, inr.injEq,
        true_and] at this hN'
      rw [← hN', ← this]
      exact hN
    · rw [raiseRaise_f_eq₃ hj (by exact hj')] at hj₂ hN'
      have h₁ := raise_injective' hj₂
      have h₂ := raise_injective' hN'
      rw [one_smul] at h₁
      simp only [h₁, Allowable.smul_address, smul_inr, Address.mk.injEq, inr.injEq,
        true_and] at h₂
      rw [← h₂]
      exact hN
  · rintro ⟨hj₁, N, hj₂, hN⟩
    obtain ⟨N', hN'⟩ := raiseRaise_f_eq_nearLitter j hj₁ _ _ hj₂
    refine ⟨hj₁, N', hN', ?_⟩
    obtain (hj | ⟨hj, hj'⟩ | ⟨hj, hj'⟩) := raiseRaise_cases hj₁
    · rw [raiseRaise_f_eq₁ hj] at hj₂ hN'
      have h₁ := raise_injective' hj₂
      have h₂ := raise_injective' hN'
      rw [one_smul] at h₂
      simp only [h₂, Allowable.smul_address, smul_inr, Address.mk.injEq, inr.injEq,
        true_and] at h₁
      rw [← h₁] at hN
      exact hN
    · rw [raiseRaise_f_eq₂ hj hj'] at hj₂ hN'
      rw [hj₂] at hN'
      have := hρS ⟨A, inr N⟩ ⟨_, _, hj₂.symm⟩
      simp only [Allowable.smul_address, smul_inr, Address.mk.injEq, inr.injEq,
        true_and] at this hN'
      rw [← this] at hN
      rw [← hN']
      exact hN
    · rw [raiseRaise_f_eq₃ hj (by exact hj')] at hj₂ hN'
      have h₁ := raise_injective' hj₂
      have h₂ := raise_injective' hN'
      rw [one_smul] at h₂
      simp only [h₂, Allowable.smul_address, smul_inr, Address.mk.injEq, inr.injEq,
        true_and] at h₁
      rw [← h₁] at hN
      exact hN

theorem raiseRaise_atom_spec₂ (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c)
    {i : κ} (hi : i < (raiseRaise hγ S T ρ).max)
    {A : ExtendedIndex α} {a b : Atom}
    (ha : (raiseRaise hγ S T ρ).f i hi = ⟨A, inl a⟩)
    (hb : (raiseRaise hγ S T 1).f i hi = ⟨A, inl b⟩) :
    {j | ∃ hj, ∃ N, (raiseRaise hγ S T 1).f j hj = ⟨A, inr N⟩ ∧ b ∈ N} =
    {j | ∃ hj, ∃ N, (raiseRaise hγ S T ρ).f j hj = ⟨A, inr N⟩ ∧ a ∈ N} := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · rw [raiseRaise_f_eq₁ hi] at ha hb
    exact raiseRaise_atom_spec₂' hρS ha hb
  · rw [raiseRaise_f_eq₂ hi hi'] at ha hb
    cases ha.symm.trans hb
    ext j : 1
    constructor
    · rintro ⟨hj₁, N, hN, hj₂⟩
      obtain (hj | ⟨hj, hj'⟩ | ⟨hj, hj'⟩) := raiseRaise_cases hj₁
      · rw [raiseRaise_f_eq₁ hj] at hN
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hN
        have hN := raise_injective' hN
        rw [one_smul] at hN
        refine ⟨hj₁, Allowable.toStructPerm ρ A • N, ?_, ?_⟩
        · rw [raiseRaise_f_eq₁ hj, hN]
          rfl
        · have := congr_arg Address.value (hρS ⟨A, inl a⟩ ⟨_, _, ha.symm⟩)
          simp only [Allowable.smul_address, smul_inl, inl.injEq] at this
          rw [← this, ← NearLitterPerm.NearLitter.mem_snd_iff, NearLitterPerm.smul_nearLitter_snd,
            Set.smul_mem_smul_set_iff, NearLitterPerm.NearLitter.mem_snd_iff]
          exact hj₂
      · refine ⟨hj₁, N, ?_, hj₂⟩
        rw [raiseRaise_f_eq₂ hj hj'] at hN ⊢
        exact hN
      · rw [raiseRaise_f_eq₃ hj hj'] at hN
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hN
        have hN := raise_injective' hN
        rw [one_smul] at hN
        refine ⟨hj₁, Allowable.toStructPerm ρ A • N, ?_, ?_⟩
        · rw [raiseRaise_f_eq₃ hj (by exact hj'), hN]
          rfl
        · have := congr_arg Address.value (hρS ⟨A, inl a⟩ ⟨_, _, ha.symm⟩)
          simp only [Allowable.smul_address, smul_inl, inl.injEq] at this
          rw [← this, ← NearLitterPerm.NearLitter.mem_snd_iff, NearLitterPerm.smul_nearLitter_snd,
            Set.smul_mem_smul_set_iff, NearLitterPerm.NearLitter.mem_snd_iff]
          exact hj₂
    · rintro ⟨hj₁, N, hN, hj₂⟩
      obtain (hj | ⟨hj, hj'⟩ | ⟨hj, hj'⟩) := raiseRaise_cases hj₁
      · rw [raiseRaise_f_eq₁ hj] at hN
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hN
        have hN := raise_injective' hN
        rw [smul_eq_iff_eq_inv_smul] at hN
        refine ⟨hj₁, Allowable.toStructPerm ρ⁻¹ A • N, ?_, ?_⟩
        · rw [raiseRaise_f_eq₁ hj, hN, one_smul]
          rfl
        · rw [map_inv, Tree.inv_apply]
          have := congr_arg Address.value (hρS ⟨A, inl a⟩ ⟨_, _, ha.symm⟩)
          simp only [Allowable.smul_address, smul_inl, inl.injEq] at this
          rw [← this] at hj₂
          exact hj₂
      · refine ⟨hj₁, N, ?_, hj₂⟩
        rw [raiseRaise_f_eq₂ hj hj'] at hN ⊢
        exact hN
      · rw [raiseRaise_f_eq₃ hj (by exact hj')] at hN
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hN
        have hN := raise_injective' hN
        rw [smul_eq_iff_eq_inv_smul] at hN
        refine ⟨hj₁, Allowable.toStructPerm ρ⁻¹ A • N, ?_, ?_⟩
        · rw [raiseRaise_f_eq₃ hj (by exact hj'), one_smul, hN]
          rfl
        · rw [map_inv, Tree.inv_apply]
          have := congr_arg Address.value (hρS ⟨A, inl a⟩ ⟨_, _, ha.symm⟩)
          simp only [Allowable.smul_address, smul_inl, inl.injEq] at this
          rw [← this] at hj₂
          exact hj₂
  · rw [raiseRaise_f_eq₃ hi (by exact hi')] at ha hb
    exact raiseRaise_atom_spec₂' hρS ha hb

theorem raiseRaise_specifies (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : Allowable β)
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c) {σ : Spec α}
    (hσ : σ.Specifies (raiseRaise hγ S T 1) (raiseRaise_strong hS (fun c _ => by rw [one_smul]))) :
    σ.Specifies (raiseRaise hγ S T ρ) (raiseRaise_strong hS hρS) where
  max_eq_max := raiseRaise_max_eq_max.symm.trans hσ.max_eq_max
  atom_spec := by
    intro i hi A a ha
    obtain ⟨b, hb⟩ := raiseRaise_f_eq_atom i hi A a ha
    rw [hσ.atom_spec i hi A b hb, SpecCondition.atom.injEq]
    exact ⟨rfl, raiseRaise_atom_spec₁ hρS hi ha hb, raiseRaise_atom_spec₂ hρS hi ha hb⟩
  flexible_spec := sorry
  inflexibleCoe_spec := sorry
  inflexibleBot_spec := sorry

end ConNF.Support
