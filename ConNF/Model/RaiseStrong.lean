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
    · obtain ⟨j, hj, hj'⟩ := this
      refine ⟨j, hj, ?_⟩
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
  S + ((ρ • (strongSupport (T.image (raise hγ)).small +
    interferenceSupport hγ S T)).image (raise iβ.elim))

variable {hγ} {S : Support α} {T : Support γ} {ρ ρ₁ ρ₂ : Allowable β}

theorem raiseRaise_max : (raiseRaise hγ S T ρ).max =
    S.max + ((strongSupport (T.image (raise hγ)).small).max + (interferenceSupport hγ S T).max) :=
  rfl

theorem raiseRaise_hi₁ {i : κ} (hi : i < S.max) : i < (raiseRaise hγ S T ρ).max :=
  hi.trans_le (κ_le_self_add _ _)

theorem raiseRaise_hi₂ {i : κ} (hi : i < S.max + (strongSupport (T.image (raise hγ)).small).max) :
    i < (raiseRaise hγ S T ρ).max := by
  rw [raiseRaise_max, ← add_assoc]
  exact hi.trans_le (κ_le_self_add _ _)

theorem raiseRaise_hi₂' {i : κ} (hi₁ : S.max ≤ i)
    (hi₂ : i < S.max + (strongSupport (T.image (raise hγ)).small).max) :
    i - S.max < (strongSupport (T.image (raise hγ)).small).max :=
  κ_sub_lt hi₂ hi₁

theorem raiseRaise_hi₃' {i : κ} (hi₁ : S.max + (strongSupport (T.image (raise hγ)).small).max ≤ i)
    (hi₂ : i < (raiseRaise hγ S T ρ).max) :
    i - S.max - (strongSupport (T.image (raise hγ)).small).max <
      (interferenceSupport hγ S T).max := by
  rw [κ_sub_lt_iff, κ_sub_lt_iff]
  · exact hi₂
  · exact (κ_le_self_add _ _).trans hi₁
  · by_contra! h
    rw [κ_sub_lt_iff ((κ_le_self_add _ _).trans hi₁)] at h
    cases not_lt_of_le hi₁ h

theorem raiseRaise_f_eq₁ {i : κ} (hi : i < S.max) :
    (raiseRaise hγ S T ρ).f i (raiseRaise_hi₁ hi) = S.f i hi := by
  unfold raiseRaise
  rw [Enumeration.add_f_left hi]

theorem raiseRaise_f_eq₂ {i : κ} (hi₁ : S.max ≤ i)
    (hi₂ : i < S.max + (strongSupport (T.image (raise hγ)).small).max) :
    (raiseRaise hγ S T ρ).f i (raiseRaise_hi₂ hi₂) =
    raise iβ.elim (ρ • (strongSupport (T.image (raise hγ)).small).f
      (i - S.max) (raiseRaise_hi₂' hi₁ hi₂)) := by
  unfold raiseRaise
  rw [Enumeration.add_f_right _ hi₁, Enumeration.image_f, Enumeration.smul_f,
    Enumeration.add_f_left (raiseRaise_hi₂' hi₁ hi₂)]

theorem raiseRaise_f_eq₃ {i : κ} (hi₁ : S.max + (strongSupport (T.image (raise hγ)).small).max ≤ i)
    (hi₂ : i < (raiseRaise hγ S T ρ).max) :
    (raiseRaise hγ S T ρ).f i hi₂ =
    raise iβ.elim (ρ • (interferenceSupport hγ S T).f
      (i - S.max - (strongSupport (T.image (raise hγ)).small).max)
      (raiseRaise_hi₃' hi₁ hi₂)) := by
  unfold raiseRaise
  rw [Enumeration.add_f_right hi₂ ((κ_le_self_add _ _).trans hi₁),
    Enumeration.image_f, Enumeration.smul_f, Enumeration.add_f_right]
  by_contra! h
  rw [κ_sub_lt_iff ((κ_le_self_add _ _).trans hi₁)] at h
  cases not_lt_of_le hi₁ h

theorem raiseRaise_cases {i : κ} (hi : i < (raiseRaise hγ S T ρ).max) :
    (i < S.max) ∨
    (S.max ≤ i ∧ i < S.max + (strongSupport (T.image (raise hγ)).small).max) ∨
    (S.max + (strongSupport (T.image (raise hγ)).small).max ≤ i ∧
      i < (raiseRaise hγ S T ρ).max) := by
  by_cases h₁ : i < S.max
  · exact Or.inl h₁
  by_cases h₂ : i < S.max + (strongSupport (T.image (raise hγ)).small).max
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
      obtain (hi₂ | ⟨hi₂, hi₂'⟩ | ⟨hi₂, hi₂'⟩) := raiseRaise_cases hi₂
      · rw [raiseRaise_f_eq₁ hi₂] at hN₂
        obtain ⟨j, hj, hj'⟩ := hS.interferes _ _ hN₁ hN₂ ha
        refine ⟨j, raiseRaise_hi₁ hj, ?_⟩
        rw [raiseRaise_f_eq₁ hj]
        exact hj'
      · rw [raiseRaise_f_eq₂ hi₂ hi₂'] at hN₂
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hN₂
        have := raise_injective' hN₂
        rw [smul_eq_iff_eq_inv_smul] at this
        have := (mem_interferenceSupport_iff hγ S T ⟨A, inl (Allowable.toStructPerm ρ⁻¹ A • a)⟩).mpr
          ⟨A, _, N₁, _, rfl, ⟨_, _, hN₁.symm⟩, ⟨_, _, this.symm⟩, ?_⟩
        · obtain ⟨j, hj, hj'⟩ := this
          refine ⟨S.max + (strongSupport (T.image (raise hγ)).small).max + j, ?_, ?_⟩
          · rwa [raiseRaise_max, add_assoc, add_lt_add_iff_left, add_lt_add_iff_left]
          · rw [raiseRaise_f_eq₃]
            swap
            · rw [le_add_iff_nonneg_right]
              exact κ_pos _
            simp_rw [add_assoc, κ_add_sub_cancel]
            rw [← hj', Allowable.smul_address]
            simp only [map_inv, Tree.inv_apply, smul_inl, smul_inv_smul]
            rfl
        · convert ha.smul (Allowable.toStructPerm ρ⁻¹ A) using 1
          have := hρS ⟨A, inr N₁⟩ ⟨_, _, hN₁.symm⟩
          simp only [Allowable.smul_address, smul_inr, Address.mk.injEq, inr.injEq, true_and]
            at this
          rw [map_inv, Tree.inv_apply, eq_inv_smul_iff, this]
      · rw [raiseRaise_f_eq₃ hi₂ hi₂'] at hN₂
        simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul] at hN₂
        cases interferenceSupport_ne_nearLitter hγ _ hN₂.2
    · rw [raiseRaise_f_eq₂ hi₁ hi₁'] at hN₁
      obtain (hi₂ | ⟨hi₂, hi₂'⟩ | ⟨hi₂, hi₂'⟩) := raiseRaise_cases hi₂
      · rw [raiseRaise_f_eq₁ hi₂] at hN₂
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hN₁
        have := raise_injective' hN₁
        rw [smul_eq_iff_eq_inv_smul] at this
        have := (mem_interferenceSupport_iff hγ S T ⟨A, inl (Allowable.toStructPerm ρ⁻¹ A • a)⟩).mpr
          ⟨A, _, _, _, rfl, ⟨_, _, hN₂.symm⟩, ⟨_, _, this.symm⟩, ?_⟩
        · obtain ⟨j, hj, hj'⟩ := this
          refine ⟨S.max + (strongSupport (T.image (raise hγ)).small).max + j, ?_, ?_⟩
          · rwa [raiseRaise_max, add_assoc, add_lt_add_iff_left, add_lt_add_iff_left]
          · rw [raiseRaise_f_eq₃]
            swap
            · rw [le_add_iff_nonneg_right]
              exact κ_pos _
            simp_rw [add_assoc, κ_add_sub_cancel]
            rw [← hj', Allowable.smul_address]
            simp only [map_inv, Tree.inv_apply, smul_inl, smul_inv_smul]
            rfl
        · convert ha.symm.smul (Allowable.toStructPerm ρ⁻¹ A) using 1
          have := hρS ⟨A, inr N₂⟩ ⟨_, _, hN₂.symm⟩
          simp only [Allowable.smul_address, smul_inr, Address.mk.injEq, inr.injEq, true_and]
            at this
          rw [map_inv, Tree.inv_apply, eq_inv_smul_iff, this]
      · rw [raiseRaise_f_eq₂ hi₂ hi₂'] at hN₂
        obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hN₂
        have hN₁' := raise_injective' hN₁
        have hN₂' := raise_injective' hN₂
        rw [smul_eq_iff_eq_inv_smul] at hN₁' hN₂'
        obtain ⟨j, hj, hj'⟩ :=
          (strongSupport_strong (T.image (raise hγ)).small).interferes _ _ hN₁' hN₂' (ha.smul _)
        refine ⟨S.max + j, ?_, ?_⟩
        · rw [raiseRaise_max, add_lt_add_iff_left]
          exact hj.trans_le (κ_le_self_add _ _)
        · rw [raiseRaise_f_eq₂]
          · simp_rw [κ_add_sub_cancel]
            rw [hj']
            simp only [map_inv, Tree.inv_apply, Allowable.smul_address, smul_inl, smul_inv_smul]
            rfl
          · rw [le_add_iff_nonneg_right]
            exact κ_pos _
          · rw [add_lt_add_iff_left]
            exact hj
      · rw [raiseRaise_f_eq₃ hi₂ hi₂'] at hN₂
        simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul] at hN₂
        cases interferenceSupport_ne_nearLitter hγ _ hN₂.2
    · rw [raiseRaise_f_eq₃ hi₁ hi₁'] at hN₁
      simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul] at hN₁
      cases interferenceSupport_ne_nearLitter hγ _ hN₁.2
  · intro i hi c hc
    obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
    · rw [raiseRaise_f_eq₁ hi] at hc
      obtain ⟨j, hj₁, hj₂, hj₃⟩ := hS.precedes _ _ hc
      refine ⟨j, raiseRaise_hi₁ hj₁, hj₂, ?_⟩
      rw [raiseRaise_f_eq₁ hj₁, hj₃]
    · rw [raiseRaise_f_eq₂ hi hi'] at hc
      obtain ⟨j, hj₁, hj₂, hj₃⟩ := (raise_smul_raise_strong hγ T ρ).precedes _ _ hc
      refine ⟨S.max + j, ?_, ?_, ?_⟩
      · rw [κ_lt_sub_iff] at hj₂
        exact hj₂.trans ‹_›
      · rw [κ_lt_sub_iff] at hj₂
        exact hj₂
      · rw [raiseRaise_f_eq₂, ← hj₃]
        · simp_rw [κ_add_sub_cancel]
          rfl
        · rw [le_add_iff_nonneg_right]
          exact κ_pos _
        · rw [add_lt_add_iff_left]
          exact hj₁
    · rw [raiseRaise_f_eq₃ hi hi'] at hc
      obtain ⟨A, a, ha⟩ := interferenceSupport_eq_atom hγ _
      rw [ha] at hc
      cases not_precedes_atom hc

theorem raiseRaise_max_eq_max : (raiseRaise hγ S T 1).max = (raiseRaise hγ S T ρ).max := rfl

theorem raiseRaise_ne_nearLitter
    {i : κ} (hi₁ : S.max + (strongSupport (T.image (raise hγ)).small).max ≤ i)
    (hi₂ : i < (raiseRaise hγ S T ρ).max) {A : ExtendedIndex α} {N : NearLitter} :
    (raiseRaise hγ S T ρ).f i hi₂ ≠ ⟨A, inr N⟩ := by
  intro h
  rw [raiseRaise_f_eq₃ hi₁ hi₂, raise, Allowable.smul_address, Address.mk.injEq,
    smul_eq_iff_eq_inv_smul, smul_inr] at h
  exact interferenceSupport_ne_nearLitter hγ _ h.2

theorem raiseRaise_f_eq_atom (i : κ) (hi : i < (raiseRaise hγ S T ρ₁).max)
    (A : ExtendedIndex α) (a : Atom) (ha : (raiseRaise hγ S T ρ₁).f i hi = ⟨A, inl a⟩) :
    ∃ b, (raiseRaise hγ S T ρ₂).f i hi = ⟨A, inl b⟩ := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · rw [raiseRaise_f_eq₁ hi] at ha ⊢
    exact ⟨a, ha⟩
  · rw [raiseRaise_f_eq₂ hi hi'] at ha
    rw [raiseRaise_f_eq₂ hi (by exact hi')]
    simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul, smul_inl,
      one_smul] at ha ⊢
    refine ⟨Allowable.toStructPerm (ρ₂ * ρ₁⁻¹) ((strongSupport (T.image (raise hγ)).small).f
        (i - S.max) ?_).path • a,
      ha.1, ?_⟩
    · rw [← κ_sub_lt_iff hi] at hi'
      exact hi'
    · simp only [ha.2, map_mul, map_inv, Tree.mul_apply, Tree.inv_apply, mul_smul, inv_smul_smul]
  · rw [raiseRaise_f_eq₃ hi (by exact hi')] at ha ⊢
    simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul, smul_inl,
      one_smul] at ha ⊢
    refine ⟨Allowable.toStructPerm (ρ₂ * ρ₁⁻¹) ((interferenceSupport hγ S T).f _
        (raiseRaise_hi₃' hi hi')).path • a, ha.1, ?_⟩
    simp only [ha.2, map_mul, map_inv, Tree.mul_apply, Tree.inv_apply, mul_smul, inv_smul_smul]

theorem raiseRaise_f_eq_nearLitter (i : κ) (hi : i < (raiseRaise hγ S T ρ₁).max)
    (A : ExtendedIndex α) (N : NearLitter) (hN : (raiseRaise hγ S T ρ₁).f i hi = ⟨A, inr N⟩) :
    ∃ N', (raiseRaise hγ S T ρ₂).f i hi = ⟨A, inr N'⟩ := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · rw [raiseRaise_f_eq₁ hi] at hN ⊢
    exact ⟨N, hN⟩
  · rw [raiseRaise_f_eq₂ hi hi'] at hN
    rw [raiseRaise_f_eq₂ hi (by exact hi')]
    simp only [Allowable.smul_address, raise, Address.mk.injEq, smul_eq_iff_eq_inv_smul, smul_inr,
      one_smul] at hN ⊢
    refine ⟨Allowable.toStructPerm (ρ₂ * ρ₁⁻¹) ((strongSupport (T.image (raise hγ)).small).f
        (i - S.max) ?_).path • N,
      hN.1, ?_⟩
    · rw [← κ_sub_lt_iff hi] at hi'
      exact hi'
    · simp only [hN.2, map_mul, map_inv, Tree.mul_apply, Tree.inv_apply, mul_smul, inv_smul_smul]
  · cases raiseRaise_ne_nearLitter hi hi' hN

theorem raiseRaise_cases_nearLitter {i : κ} {hi : i < (raiseRaise hγ S T ρ₁).max}
    {A : ExtendedIndex α} {N₁ N₂ : NearLitter}
    (h₁ : (raiseRaise hγ S T ρ₁).f i hi = ⟨A, inr N₁⟩)
    (h₂ : (raiseRaise hγ S T ρ₂).f i hi = ⟨A, inr N₂⟩) :
    (i < S.max) ∨
    (S.max ≤ i ∧ i < S.max + (strongSupport (T.image (raise hγ)).small).max ∧
      ∃ B : ExtendedIndex β, A = raiseIndex iβ.elim B) := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · exact Or.inl hi
  · rw [raiseRaise_f_eq₂ hi (by exact hi')] at h₁ h₂
    have : 0 < A.length
    · have := congr_arg (Path.length ∘ Address.path) h₁
      simp only [Allowable.smul_address, Function.comp_apply,
        raise_path, raiseIndex_length, Path.length_cons, add_left_inj] at this
      linarith
    obtain ⟨β', hβ', A, rfl⟩ := eq_raiseIndex_of_zero_lt_length this
    obtain ⟨B, hB⟩ := raiseIndex_of_raise_eq h₁
    exact Or.inr ⟨hi, hi', B, hB.symm⟩
  · cases raiseRaise_ne_nearLitter hi hi' h₁

/-- TODO: Use this lemma more! (All the lemmas tagged with this TODO should be put to use in the
atom_spec case.) -/
theorem raiseRaise_cases' (ρ₁ ρ₂ : Allowable β) {i : κ} {hi : i < (raiseRaise hγ S T ρ₁).max}
    {A : ExtendedIndex α} {x : Atom ⊕ NearLitter}
    (h : (raiseRaise hγ S T ρ₁).f i hi = ⟨A, x⟩) :
    (raiseRaise hγ S T ρ₂).f i hi = ⟨A, x⟩ ∨
    ∃ B : ExtendedIndex β, A = raiseIndex iβ.elim B ∧
      (raiseRaise hγ S T ρ₂).f i hi = ⟨A, Allowable.toStructPerm (ρ₂ * ρ₁⁻¹) B • x⟩ := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · left
    rw [raiseRaise_f_eq₁ hi] at h ⊢
    exact h
  · right
    rw [raiseRaise_f_eq₂ hi hi'] at h ⊢
    obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq h
    refine ⟨A, rfl, ?_⟩
    have := raise_injective' h
    rw [smul_eq_iff_eq_inv_smul] at this
    rw [this, smul_smul]
    rfl
  · right
    rw [raiseRaise_f_eq₃ hi (by exact hi')] at h ⊢
    obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq h
    refine ⟨A, rfl, ?_⟩
    have := raise_injective' h
    rw [smul_eq_iff_eq_inv_smul] at this
    rw [this, smul_smul]
    rfl

/-- TODO: Use this lemma more! -/
theorem raiseRaise_raiseIndex (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ₁⁻¹ • c = ρ₂⁻¹ • c)
    {i : κ} {hi : i < (raiseRaise hγ S T ρ₁).max}
    {A : ExtendedIndex β} {x : Atom ⊕ NearLitter}
    (h : (raiseRaise hγ S T ρ₁).f i hi = ⟨raiseIndex iβ.elim A, x⟩) :
    (raiseRaise hγ S T ρ₂).f i hi =
      ⟨raiseIndex iβ.elim A, Allowable.toStructPerm (ρ₂ * ρ₁⁻¹) A • x⟩ := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · rw [raiseRaise_f_eq₁ hi] at h ⊢
    simp only [h, map_mul, map_inv, Tree.mul_apply, Tree.inv_apply, mul_smul, Address.mk.injEq,
      true_and]
    have := congr_arg Address.value (hρS ⟨A, x⟩ ⟨i, hi, h.symm⟩)
    simp only [Allowable.smul_address, map_inv, Tree.inv_apply] at this
    rw [← smul_eq_iff_eq_inv_smul] at this
    exact this.symm
  · rw [raiseRaise_f_eq₂ hi hi'] at h ⊢
    have := raise_injective' h
    rw [smul_eq_iff_eq_inv_smul] at this
    rw [this, smul_smul]
    rfl
  · rw [raiseRaise_f_eq₃ hi (by exact hi')] at h ⊢
    have := raise_injective' h
    rw [smul_eq_iff_eq_inv_smul] at this
    rw [this, smul_smul]
    rfl

/-- TODO: Use this lemma more! -/
theorem raiseRaise_not_raiseIndex (ρ₂ : Allowable β)
    {i : κ} {hi : i < (raiseRaise hγ S T ρ₁).max}
    {A : ExtendedIndex α} (hA : ¬∃ B : ExtendedIndex β, A = raiseIndex iβ.elim B)
    {x : Atom ⊕ NearLitter} (h : (raiseRaise hγ S T ρ₁).f i hi = ⟨A, x⟩) :
    (raiseRaise hγ S T ρ₂).f i hi = ⟨A, x⟩ := by
  obtain (h' | ⟨B, hB, -⟩) := raiseRaise_cases' ρ₁ ρ₂ h
  · exact h'
  · cases hA ⟨B, hB⟩

theorem raiseRaise_inflexibleCoe₃ {i : κ}
    (hi : S.max ≤ i) (hi' : i < S.max + (strongSupport (T.image (raise hγ)).small).max)
    {A : ExtendedIndex β} {N₁ N₂ : NearLitter}
    (h₁ : (raiseRaise hγ S T ρ₁).f i (raiseRaise_hi₂ hi') = ⟨raiseIndex iβ.elim A, inr N₁⟩)
    (h₂ : (raiseRaise hγ S T ρ₂).f i (raiseRaise_hi₂ hi') = ⟨raiseIndex iβ.elim A, inr N₂⟩)
    (h : InflexibleCoe (raiseIndex iβ.elim A) N₁.1) :
    ∃ (P : InflexibleCoePath A) (t : Tangle P.δ),
    N₁.1 = fuzz P.hδε (Allowable.comp (P.B.cons P.hδ) ρ₁ • t) ∧
    N₂.1 = fuzz P.hδε (Allowable.comp (P.B.cons P.hδ) ρ₂ • t) := by
  rw [raiseRaise_f_eq₂ hi (by exact hi')] at h₁ h₂
  obtain ⟨⟨γ, δ, ε, hδ, hε, hδε, B, hB⟩, t, hL⟩ := h
  have : 0 < B.length
  · have := strongSupport_raise_spec hγ T _ ⟨i - S.max, ?_, rfl⟩
    swap
    · rw [κ_sub_lt_iff hi]
      exact hi'
    obtain (h | ⟨a, ha⟩) := this
    · have h₁ := congr_arg (Path.length ∘ Address.path) h₁
      have h₂ := congr_arg Path.length hB
      simp only [Allowable.smul_address, Function.comp_apply, raise_path,
        raiseIndex_length, Path.length_cons, add_left_inj] at h₁ h₂
      linarith
    · have h₁ := congr_arg Address.value h₁
      have h₂ := congr_arg Address.value ha
      rw [Allowable.smul_address, raise_value, smul_eq_iff_eq_inv_smul] at h₁
      cases h₁.symm.trans h₂
  obtain ⟨β', hβ', B, rfl⟩ := eq_raiseIndex_of_zero_lt_length this
  rw [← Path.comp_cons, ← Path.comp_cons] at hB
  cases Path.comp_injective' (by rfl) hB
  cases raiseIndex_injective _ hB
  refine ⟨⟨γ, δ, ε, hδ, hε, hδε, B, rfl⟩, Allowable.comp (B.cons hδ) ρ₁⁻¹ • t, ?_, ?_⟩
  · simp only [hL, map_inv, smul_inv_smul]
  · rw [← toStructPerm_smul_fuzz hδ hε hδε, ← toStructPerm_smul_fuzz hδ hε hδε,
      ← hL, ← inv_smul_eq_iff]
    simp only [map_inv, Tree.inv_apply]
    have h₁' := congr_arg Address.value h₁
    have h₂' := congr_arg Address.value h₂
    simp only [raise_value, Allowable.smul_address, smul_eq_iff_eq_inv_smul] at h₁' h₂'
    have := h₁'.symm.trans h₂'
    simp only [smul_inr, inr.injEq] at this
    have := congr_arg Sigma.fst this
    simp only [NearLitterPerm.smul_nearLitter_fst] at this
    rw [← raiseIndex_injective _ (congr_arg Address.path h₁)]
    exact this.symm

theorem raiseRaise_inflexibleBot₃ {i : κ}
    (hi : S.max ≤ i) (hi' : i < S.max + (strongSupport (T.image (raise hγ)).small).max)
    {A : ExtendedIndex β} {N₁ N₂ : NearLitter}
    (h₁ : (raiseRaise hγ S T ρ₁).f i (raiseRaise_hi₂ hi') = ⟨raiseIndex iβ.elim A, inr N₁⟩)
    (h₂ : (raiseRaise hγ S T ρ₂).f i (raiseRaise_hi₂ hi') = ⟨raiseIndex iβ.elim A, inr N₂⟩)
    (h : InflexibleBot (raiseIndex iβ.elim A) N₁.1) :
    ∃ (P : InflexibleBotPath A) (a : Atom),
    N₁.1 = fuzz (bot_ne_coe (a := P.ε))
      (Allowable.toStructPerm ρ₁ (P.B.cons (bot_lt_coe _)) • a) ∧
    N₂.1 = fuzz (bot_ne_coe (a := P.ε))
      (Allowable.toStructPerm ρ₂ (P.B.cons (bot_lt_coe _)) • a) := by
  rw [raiseRaise_f_eq₂ hi (by exact hi')] at h₁ h₂
  obtain ⟨⟨γ, ε, hε, B, hB⟩, a, hL⟩ := h
  have : 0 < B.length
  · have := strongSupport_raise_spec hγ T _ ⟨i - S.max, ?_, rfl⟩
    swap
    · rw [κ_sub_lt_iff hi]
      exact hi'
    obtain (h | ⟨a, ha⟩) := this
    · have h₁ := congr_arg (Path.length ∘ Address.path) h₁
      have h₂ := congr_arg Path.length hB
      simp only [Allowable.smul_address, Function.comp_apply, raise_path,
        raiseIndex_length, Path.length_cons, add_left_inj] at h₁ h₂
      linarith
    · have h₁ := congr_arg Address.value h₁
      have h₂ := congr_arg Address.value ha
      rw [Allowable.smul_address, raise_value, smul_eq_iff_eq_inv_smul] at h₁
      cases h₁.symm.trans h₂
  obtain ⟨β', hβ', B, rfl⟩ := eq_raiseIndex_of_zero_lt_length this
  rw [← Path.comp_cons, ← Path.comp_cons] at hB
  cases Path.comp_injective' (by rfl) hB
  cases raiseIndex_injective _ hB
  refine ⟨⟨γ, ε, hε, B, rfl⟩, Allowable.toStructPerm ρ₁⁻¹ (B.cons (bot_lt_coe _)) • a, ?_, ?_⟩
  · simp only [hL, gt_iff_lt, bot_lt_coe, map_inv, Tree.inv_apply, smul_inv_smul]
  · have := toStructPerm_smul_fuzz (bot_lt_coe _) hε (bot_ne_coe (a := ε)) B
    simp only [ofBot_smul, Allowable.toStructPerm_apply] at this
    rw [← this, ← this, ← hL, ← inv_smul_eq_iff]
    simp only [map_inv, Tree.inv_apply]
    have h₁' := congr_arg Address.value h₁
    have h₂' := congr_arg Address.value h₂
    simp only [raise_value, Allowable.smul_address, smul_eq_iff_eq_inv_smul] at h₁' h₂'
    have := h₁'.symm.trans h₂'
    simp only [smul_inr, inr.injEq] at this
    have := congr_arg Sigma.fst this
    simp only [NearLitterPerm.smul_nearLitter_fst] at this
    rw [← raiseIndex_injective _ (congr_arg Address.path h₁)]
    exact this.symm

theorem raiseRaise_flexible₃ {i : κ}
    (hi : S.max ≤ i) (hi' : i < S.max + (strongSupport (T.image (raise hγ)).small).max)
    {A : ExtendedIndex β} {N₁ N₂ : NearLitter}
    (h₁ : (raiseRaise hγ S T ρ₁).f i (raiseRaise_hi₂ hi') = ⟨raiseIndex iβ.elim A, inr N₁⟩)
    (h₂ : (raiseRaise hγ S T ρ₂).f i (raiseRaise_hi₂ hi') = ⟨raiseIndex iβ.elim A, inr N₂⟩)
    (h : Flexible (raiseIndex iβ.elim A) N₁.1) :
    Flexible (raiseIndex iβ.elim A) N₂.1 := by
  rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at h ⊢
  refine ⟨⟨fun h' => ?_⟩, ⟨fun h' => ?_⟩⟩
  · obtain ⟨P, a, -, h'⟩ := raiseRaise_inflexibleBot₃ hi hi' h₂ h₁ h'
    exact h.1.false ⟨P.comp _, _, h'⟩
  · obtain ⟨P, a, -, h'⟩ := raiseRaise_inflexibleCoe₃ hi hi' h₂ h₁ h'
    exact h.2.false ⟨P.comp _, _, h'⟩

theorem raiseRaise_eq_cases {i : κ} {hi : i < (raiseRaise hγ S T ρ).max} {c : Address α}
    (h : (raiseRaise hγ S T ρ).f i hi = c) :
    (∃ d, c = raise iβ.elim (ρ • d) ∧ (raiseRaise hγ S T 1).f i hi = raise iβ.elim d) ∨
    (c ∈ S ∧ (raiseRaise hγ S T 1).f i hi = c) := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · refine Or.inr ?_
    rw [raiseRaise_f_eq₁ hi] at h ⊢
    exact ⟨⟨_, _, h.symm⟩, h⟩
  · rw [raiseRaise_f_eq₂ hi hi'] at h ⊢
    refine Or.inl ⟨_, h.symm, ?_⟩
    rw [one_smul]
  · rw [raiseRaise_f_eq₃ hi (by exact hi')] at h ⊢
    refine Or.inl ⟨_, h.symm, ?_⟩
    rw [one_smul]

theorem raiseRaise_atom_spec₁_raise
    (hρ₁S : ∀ c : Address β, raise iβ.elim (ρ₁ • c) ∈ S → ρ₁ • c = ρ₂ • c)
    {A : ExtendedIndex α} {a₁ a₂ : Atom} {c : Address β}
    (ha₁ : raise iβ.elim (ρ₁ • c) = ⟨A, inl a₁⟩)
    (ha₂ : raise iβ.elim (ρ₂ • c) = ⟨A, inl a₂⟩) :
    {j | ∃ hj, (raiseRaise hγ S T ρ₁).f j hj = ⟨A, inl a₁⟩} ⊆
    {j | ∃ hj, (raiseRaise hγ S T ρ₂).f j hj = ⟨A, inl a₂⟩} := by
  obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq ha₁
  have ha₁ := raise_injective' ha₁
  have ha₂ := raise_injective' ha₂
  rintro j ⟨hj₁, hj₂⟩
  refine ⟨hj₁, ?_⟩
  change _ = raise iβ.elim ⟨A, inl _⟩ at hj₂ ⊢
  obtain (hj | ⟨hj, hj'⟩ | ⟨hj, hj'⟩) := raiseRaise_cases hj₁
  · rw [raiseRaise_f_eq₁ hj] at hj₂ ⊢
    rw [hj₂, ← ha₁, hρ₁S c ⟨_, _, ha₁.symm ▸ hj₂.symm⟩, ha₂]
  · rw [raiseRaise_f_eq₂ hj hj'] at hj₂ ⊢
    have := raise_injective _ hj₂
    rw [smul_eq_iff_eq_inv_smul] at ha₂
    rw [← ha₁, ha₂, smul_left_cancel_iff, ← smul_eq_iff_eq_inv_smul] at this
    rw [this]
  · rw [raiseRaise_f_eq₃ hj (by exact hj')] at hj₂ ⊢
    have := raise_injective _ hj₂
    rw [smul_eq_iff_eq_inv_smul] at ha₂
    rw [← ha₁, ha₂, smul_left_cancel_iff, ← smul_eq_iff_eq_inv_smul] at this
    rw [this]

theorem raiseRaise_atom_spec₁
    (hρ₁S : ∀ c : Address β, raise iβ.elim (ρ₁ • c) ∈ S → ρ₁ • c = ρ₂ • c)
    {i : κ} {hi : i < (raiseRaise hγ S T ρ₁).max}
    {A : ExtendedIndex α} {a₁ a₂ : Atom}
    (ha₁ : (raiseRaise hγ S T ρ₁).f i hi = ⟨A, inl a₁⟩)
    (ha₂ : (raiseRaise hγ S T ρ₂).f i hi = ⟨A, inl a₂⟩) :
    {j | ∃ hj, (raiseRaise hγ S T ρ₁).f j hj = ⟨A, inl a₁⟩} ⊆
    {j | ∃ hj, (raiseRaise hγ S T ρ₂).f j hj = ⟨A, inl a₂⟩} := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · rw [raiseRaise_f_eq₁ hi] at ha₁ ha₂
    have := ha₁.symm.trans ha₂
    simp only [Address.mk.injEq, inl.injEq, true_and] at this
    subst this
    rintro j ⟨hj₁, hj₂⟩
    refine ⟨hj₁, ?_⟩
    obtain (hj | ⟨hj, hj'⟩ | ⟨hj, hj'⟩) := raiseRaise_cases hj₁
    · rw [raiseRaise_f_eq₁ hj] at hj₂ ⊢
      exact hj₂
    · rw [raiseRaise_f_eq₂ hj hj'] at hj₂ ⊢
      obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hj₂
      have hj₂ := raise_injective' hj₂
      rw [smul_eq_iff_eq_inv_smul] at hj₂
      rw [hj₂, ← hρ₁S (ρ₁⁻¹ • ⟨A, inl a₁⟩), smul_inv_smul]
      rfl
      rw [smul_inv_smul]
      exact ⟨_, _, ha₁.symm⟩
    · rw [raiseRaise_f_eq₃ hj (by exact hj')] at hj₂ ⊢
      obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hj₂
      have hj₂ := raise_injective' hj₂
      rw [smul_eq_iff_eq_inv_smul] at hj₂
      rw [hj₂, ← hρ₁S (ρ₁⁻¹ • ⟨A, inl a₁⟩), smul_inv_smul]
      rfl
      rw [smul_inv_smul]
      exact ⟨_, _, ha₁.symm⟩
  · rw [raiseRaise_f_eq₂ hi hi'] at ha₁ ha₂
    exact raiseRaise_atom_spec₁_raise hρ₁S ha₁ ha₂
  · rw [raiseRaise_f_eq₃ hi (by exact hi')] at ha₁ ha₂
    exact raiseRaise_atom_spec₁_raise hρ₁S ha₁ ha₂

theorem raiseRaise_atom_spec₂_raise
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ₁⁻¹ • c = ρ₂⁻¹ • c)
    {A : ExtendedIndex α} {a₁ a₂ : Atom} {c : Address β}
    (ha₁ : raise iβ.elim (ρ₁ • c) = ⟨A, inl a₁⟩)
    (ha₂ : raise iβ.elim (ρ₂ • c) = ⟨A, inl a₂⟩) :
    {j | ∃ hj, ∃ N, (raiseRaise hγ S T ρ₁).f j hj = ⟨A, inr N⟩ ∧ a₁ ∈ N} ⊆
    {j | ∃ hj, ∃ N, (raiseRaise hγ S T ρ₂).f j hj = ⟨A, inr N⟩ ∧ a₂ ∈ N} := by
  obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq ha₁
  have ha₁ := raise_injective' ha₁
  have ha₂ := raise_injective' ha₂
  rw [smul_eq_iff_eq_inv_smul] at ha₁ ha₂
  have := ha₂.symm.trans ha₁
  simp only [Allowable.smul_address, map_inv, Tree.inv_apply, smul_inl, Address.mk.injEq,
    inl.injEq, true_and] at this
  rintro j ⟨hj₁, N, hj₂, hN⟩
  obtain ⟨N', hN'⟩ := raiseRaise_f_eq_nearLitter (ρ₂ := ρ₂) j hj₁ _ _ hj₂
  refine ⟨hj₁, N', hN', ?_⟩
  obtain (hj | ⟨hj, hj'⟩ | ⟨hj, hj'⟩) := raiseRaise_cases hj₁
  · rw [raiseRaise_f_eq₁ hj] at hj₂ hN'
    rw [inv_smul_eq_iff] at this
    rw [this]
    cases hN'.symm.trans hj₂
    rw [← NearLitterPerm.NearLitter.mem_snd_iff, ← Set.mem_inv_smul_set_iff,
      ← NearLitterPerm.smul_nearLitter_snd]
    have := hρS ⟨A, inr N⟩ ⟨_, _, hj₂.symm⟩
    simp only [Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr, Address.mk.injEq,
      inr.injEq, true_and] at this
    rw [← this]
    rw [NearLitterPerm.smul_nearLitter_snd, Set.smul_mem_smul_set_iff]
    exact hN
  · rw [raiseRaise_f_eq₂ hj hj'] at hj₂ hN'
    have h₁ := raise_injective' hj₂
    have h₂ := raise_injective' hN'
    rw [smul_eq_iff_eq_inv_smul] at h₁ h₂ this
    simp only [h₁, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr, Address.mk.injEq,
      inr.injEq, ← smul_eq_iff_eq_inv_smul, true_and] at h₂
    rw [← h₂, this, inv_inv]
    rw [smul_smul, smul_smul, ← NearLitterPerm.NearLitter.mem_snd_iff,
      NearLitterPerm.smul_nearLitter_snd, Set.smul_mem_smul_set_iff,
      NearLitterPerm.NearLitter.mem_snd_iff]
    exact hN
  · rw [raiseRaise_f_eq₃ hj (by exact hj')] at hj₂ hN'
    have h₁ := raise_injective' hj₂
    have h₂ := raise_injective' hN'
    rw [smul_eq_iff_eq_inv_smul] at h₁ h₂ this
    simp only [h₁, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr, Address.mk.injEq,
      inr.injEq, ← smul_eq_iff_eq_inv_smul, true_and] at h₂
    rw [← h₂, this, inv_inv]
    rw [smul_smul, smul_smul, ← NearLitterPerm.NearLitter.mem_snd_iff,
      NearLitterPerm.smul_nearLitter_snd, Set.smul_mem_smul_set_iff,
      NearLitterPerm.NearLitter.mem_snd_iff]
    exact hN

theorem raiseRaise_atom_spec₂
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ₁⁻¹ • c = ρ₂⁻¹ • c)
    {i : κ} {hi : i < (raiseRaise hγ S T ρ₁).max}
    {A : ExtendedIndex α} {a₁ a₂ : Atom}
    (ha₁ : (raiseRaise hγ S T ρ₁).f i hi = ⟨A, inl a₁⟩)
    (ha₂ : (raiseRaise hγ S T ρ₂).f i hi = ⟨A, inl a₂⟩) :
    {j | ∃ hj, ∃ N, (raiseRaise hγ S T ρ₁).f j hj = ⟨A, inr N⟩ ∧ a₁ ∈ N} ⊆
    {j | ∃ hj, ∃ N, (raiseRaise hγ S T ρ₂).f j hj = ⟨A, inr N⟩ ∧ a₂ ∈ N} := by
  obtain (hi | ⟨hi, hi'⟩ | ⟨hi, hi'⟩) := raiseRaise_cases hi
  · rw [raiseRaise_f_eq₁ hi] at ha₁ ha₂
    have := ha₁.symm.trans ha₂
    simp only [Address.mk.injEq, inl.injEq, true_and] at this
    subst this
    rintro j ⟨hj₁, N, hj₂, hN⟩
    refine ⟨hj₁, ?_⟩
    obtain (hj | ⟨hj, hj'⟩ | ⟨hj, hj'⟩) := raiseRaise_cases hj₁
    · rw [raiseRaise_f_eq₁ hj] at hj₂ ⊢
      exact ⟨N, hj₂, hN⟩
    · rw [raiseRaise_f_eq₂ hj hj'] at hj₂ ⊢
      obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hj₂
      have hj₂ := raise_injective' hj₂
      rw [smul_eq_iff_eq_inv_smul] at hj₂
      rw [hj₂]
      refine ⟨Allowable.toStructPerm (ρ₂ * ρ₁⁻¹) A • N, ?_, ?_⟩
      · simp only [Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr, raise, map_mul,
          Tree.mul_apply, mul_smul]
      · change _ = raise iβ.elim ⟨A, inl a₁⟩ at ha₁
        have := hρS _ ⟨_, _, ha₁.symm⟩
        simp only [Allowable.smul_address_eq_smul_iff, map_inv, Tree.inv_apply, smul_inl,
          inl.injEq] at this
        rw [map_mul, map_inv, Tree.mul_apply, Tree.inv_apply, mul_smul,
          ← NearLitterPerm.NearLitter.mem_snd_iff,
          NearLitterPerm.smul_nearLitter_snd, Set.mem_smul_set_iff_inv_smul_mem,
          ← this, NearLitterPerm.smul_nearLitter_snd, Set.smul_mem_smul_set_iff]
        exact hN
    · rw [raiseRaise_f_eq₃ hj (by exact hj')] at hj₂ ⊢
      obtain ⟨A, rfl⟩ := raiseIndex_of_raise_eq hj₂
      have hj₂ := raise_injective' hj₂
      rw [smul_eq_iff_eq_inv_smul] at hj₂
      rw [hj₂]
      refine ⟨Allowable.toStructPerm (ρ₂ * ρ₁⁻¹) A • N, ?_, ?_⟩
      · simp only [Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr, raise, map_mul,
          Tree.mul_apply, mul_smul]
      · change _ = raise iβ.elim ⟨A, inl a₁⟩ at ha₁
        have := hρS _ ⟨_, _, ha₁.symm⟩
        simp only [Allowable.smul_address_eq_smul_iff, map_inv, Tree.inv_apply, smul_inl,
          inl.injEq] at this
        rw [map_mul, map_inv, Tree.mul_apply, Tree.inv_apply, mul_smul,
          ← NearLitterPerm.NearLitter.mem_snd_iff,
          NearLitterPerm.smul_nearLitter_snd, Set.mem_smul_set_iff_inv_smul_mem,
          ← this, NearLitterPerm.smul_nearLitter_snd, Set.smul_mem_smul_set_iff]
        exact hN
  · rw [raiseRaise_f_eq₂ hi hi'] at ha₁ ha₂
    exact raiseRaise_atom_spec₂_raise hρS ha₁ ha₂
  · rw [raiseRaise_f_eq₃ hi (by exact hi')] at ha₁ ha₂
    exact raiseRaise_atom_spec₂_raise hρS ha₁ ha₂

theorem raiseRaise_flexibleCoe_spec_eq
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ₁⁻¹ • c = ρ₂⁻¹ • c)
    {i : κ} (hi : i < (raiseRaise hγ S T ρ₁).max) {A : ExtendedIndex α} {N₁ N₂ : NearLitter}
    (hN₁ : (raiseRaise hγ S T ρ₁).f i hi = ⟨A, inr N₁⟩)
    (hN₂ : (raiseRaise hγ S T ρ₂).f i hi = ⟨A, inr N₂⟩) :
    {j | ∃ (hj : j < (raiseRaise hγ S T ρ₁).max), ∃ N',
      (raiseRaise hγ S T ρ₁).f j hj = ⟨A, inr N'⟩ ∧ N'.1 = N₁.1} ⊆
    {j | ∃ (hj : j < (raiseRaise hγ S T ρ₂).max), ∃ N',
      (raiseRaise hγ S T ρ₂).f j hj = ⟨A, inr N'⟩ ∧ N'.1 = N₂.1} := by
  rintro j ⟨hj, N', hjN', hN'⟩
  obtain (h | ⟨A, rfl, h⟩) := raiseRaise_cases' ρ₁ ρ₂ hN₁
  · obtain (h' | ⟨A, rfl, h'⟩) := raiseRaise_cases' ρ₁ ρ₂ hjN'
    · cases h.symm.trans hN₂
      exact ⟨hj, N', h', hN'⟩
    · refine ⟨hj, Allowable.toStructPerm (ρ₂ * ρ₁⁻¹) A • N', ?_, ?_⟩
      · rw [h']
        simp only [map_mul, map_inv, Tree.mul_apply, Tree.inv_apply, smul_inr]
      · have := hN₂.symm.trans (raiseRaise_raiseIndex hρS hN₁)
        simp only [map_mul, map_inv, Tree.mul_apply, Tree.inv_apply, smul_inr, Address.mk.injEq,
          inr.injEq, true_and, NearLitterPerm.smul_nearLitter_fst] at this ⊢
        rw [this, NearLitterPerm.smul_nearLitter_fst, smul_left_cancel_iff, hN']
  · refine ⟨hj, Allowable.toStructPerm (ρ₂ * ρ₁⁻¹) A • N', raiseRaise_raiseIndex hρS hjN', ?_⟩
    have := hN₂.symm.trans (raiseRaise_raiseIndex hρS hN₁)
    simp only [map_mul, map_inv, Tree.mul_apply, Tree.inv_apply, smul_inr, Address.mk.injEq,
      inr.injEq, true_and, NearLitterPerm.smul_nearLitter_fst] at this ⊢
    rw [this, NearLitterPerm.smul_nearLitter_fst, smul_left_cancel_iff, hN']

theorem raiseRaise_inflexibleCoe_spec₁_comp_before_aux
    {i : κ} (hi : i < S.max) {j : κ} (hji : j < i) :
    ((raiseRaise hγ S T ρ₁).before i (raiseRaise_hi₁ hi)).f j hji =
    ((raiseRaise hγ S T ρ₂).before i (raiseRaise_hi₁ hi)).f j hji := by
  simp only [before_f, raiseRaise_f_eq₁ (hji.trans hi)]

theorem raiseRaise_inflexibleCoe_spec₁_comp_before
    {i : κ} (hi : i < S.max)
    {A : ExtendedIndex α} {N : NearLitter} (h : InflexibleCoe A N.1) :
    ∃ ρ : Allowable h.path.δ,
    ((raiseRaise hγ S T ρ₁).before i (raiseRaise_hi₁ hi)).comp (h.path.B.cons h.path.hδ) =
    ρ • ((raiseRaise hγ S T ρ₂).before i (raiseRaise_hi₁ hi)).comp (h.path.B.cons h.path.hδ) ∧
    h.t.set = ρ • h.t.set := by
  refine ⟨1, ?_, by rw [one_smul]⟩
  symm
  refine smul_comp_ext _ _ rfl ?_ ?_
  · intro j hji _ c h
    rw [raiseRaise_inflexibleCoe_spec₁_comp_before_aux hi hji (ρ₂ := ρ₁)] at h
    simp only [map_one, Tree.one_apply, one_smul]
    exact h
  · intro j hji _ c h
    rw [raiseRaise_inflexibleCoe_spec₁_comp_before_aux hi hji (ρ₂ := ρ₂)] at h
    simp only [inv_one, map_one, Tree.one_apply, one_smul]
    exact h

theorem raiseRaise_inflexibleCoe_spec₂_comp_before
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c)
    {i : κ}(hi' : i < S.max + (strongSupport (T.image (raise hγ)).small).max)
    {A : ExtendedIndex β} (P : InflexibleCoePath A) (t : Tangle P.δ) :
    ∃ ρ' : Allowable P.δ,
    ((raiseRaise hγ S T ρ).before i
      (raiseRaise_hi₂ hi')).comp (((Hom.toPath iβ.elim).comp P.B).cons P.hδ) =
    ρ' • ((raiseRaise hγ S T 1).before i
      (raiseRaise_hi₂ hi')).comp (((Hom.toPath iβ.elim).comp P.B).cons P.hδ) ∧
    Allowable.comp (P.B.cons P.hδ) ρ • t.set = ρ' • t.set := by
  refine ⟨Allowable.comp (P.B.cons P.hδ) ρ, ?_, rfl⟩
  symm
  refine smul_comp_ext _ _ rfl ?_ ?_
  · intro j hji _ c hc
    simp only [before_f, Allowable.toStructPerm_comp, Tree.comp_apply] at hc ⊢
    obtain (hj | ⟨hj, hj'⟩ | ⟨hj, -⟩) := raiseRaise_cases (ρ := ρ)
        (hji.trans (raiseRaise_hi₂ hi'))
    · rw [raiseRaise_f_eq₁ hj] at hc ⊢
      have := hρS ⟨(P.B.cons P.hδ).comp c.1, c.2⟩ ?_
      · rw [hc]
        simp only [Allowable.smul_address_eq_iff, Address.mk.injEq, true_and] at this ⊢
        exact this.symm
      · refine ⟨j, hj, ?_⟩
        rw [hc]
        simp only [raise, raiseIndex, Address.mk.injEq, and_true, ← Path.comp_assoc, Path.comp_cons]
    · rw [raiseRaise_f_eq₂ hj hj', ← Path.comp_cons, Path.comp_assoc] at hc ⊢
      have := raise_injective' hc
      rw [one_smul] at this
      rw [this]
      rfl
    · cases (hj.trans_lt hji).not_lt hi'
  · intro j hji _ c hc
    simp only [before_f, Allowable.toStructPerm_comp, Tree.comp_apply] at hc ⊢
    obtain (hj | ⟨hj, hj'⟩ | ⟨hj, -⟩) := raiseRaise_cases (ρ := ρ)
        (hji.trans (raiseRaise_hi₂ hi'))
    · rw [raiseRaise_f_eq₁ hj] at hc ⊢
      have := hρS ⟨(P.B.cons P.hδ).comp c.1, c.2⟩ ?_
      · rw [hc]
        simp only [Allowable.smul_address_eq_iff, Address.mk.injEq, true_and] at this ⊢
        rw [smul_eq_iff_eq_inv_smul] at this
        simp only [map_inv, Allowable.toStructPerm_comp, Tree.inv_apply, Tree.comp_apply]
        exact this
      · refine ⟨j, hj, ?_⟩
        rw [hc]
        simp only [raise, raiseIndex, Address.mk.injEq, and_true, ← Path.comp_assoc, Path.comp_cons]
    · rw [raiseRaise_f_eq₂ hj hj', ← Path.comp_cons, Path.comp_assoc] at hc ⊢
      have := raise_injective' hc
      rw [smul_eq_iff_eq_inv_smul] at this
      rw [this]
      simp only [Allowable.smul_address, map_inv, Tree.inv_apply, one_smul, raise, raiseIndex,
        ← Path.comp_assoc, Path.comp_cons, Allowable.toStructPerm_comp, Tree.comp_apply]
    · cases (hj.trans_lt hji).not_lt hi'

theorem raiseRaise_symmDiff
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ₁⁻¹ • c = ρ₂⁻¹ • c)
    {i : κ} {hi : i < (raiseRaise hγ S T ρ₁).max}
    {A : ExtendedIndex α} {N₁ N₂ : NearLitter}
    (hN₁ : (raiseRaise hγ S T ρ₁).f i hi = ⟨A, inr N₁⟩)
    (hN₂ : (raiseRaise hγ S T ρ₂).f i hi = ⟨A, inr N₂⟩)
    (j : κ) :
    {k | ∃ (hj : j < (raiseRaise hγ S T ρ₁).max) (hk : k < (raiseRaise hγ S T ρ₁).max),
      ∃ (a : Atom) (N' : NearLitter), N'.1 = N₁.1 ∧ a ∈ (N₁ : Set Atom) ∆ N' ∧
      (raiseRaise hγ S T ρ₁).f j hj = ⟨A, inr N'⟩ ∧
      (raiseRaise hγ S T ρ₁).f k hk = ⟨A, inl a⟩} ⊆
    {k | ∃ (hj : j < (raiseRaise hγ S T ρ₂).max) (hk : k < (raiseRaise hγ S T ρ₂).max),
      ∃ (a : Atom) (N' : NearLitter), N'.1 = N₂.1 ∧ a ∈ (N₂ : Set Atom) ∆ N' ∧
      (raiseRaise hγ S T ρ₂).f j hj = ⟨A, inr N'⟩ ∧
      (raiseRaise hγ S T ρ₂).f k hk = ⟨A, inl a⟩} := by
  by_cases h : ∃ B : ExtendedIndex β, A = raiseIndex iβ.elim B
  · obtain ⟨A, rfl⟩ := h
    rintro k ⟨hj, hk, a, N', hNN', ha, hN', ha'⟩
    refine ⟨hj, hk, ?_⟩
    cases hN₂.symm.trans (raiseRaise_raiseIndex hρS hN₁)
    refine ⟨_, _, ?_, ?_, raiseRaise_raiseIndex hρS hN', raiseRaise_raiseIndex hρS ha'⟩
    · simp only [map_mul, map_inv, Tree.mul_apply, Tree.inv_apply,
        NearLitterPerm.smul_nearLitter_fst, hNN']
    · rw [map_mul, map_inv, Tree.mul_apply, Tree.inv_apply,
        NearLitterPerm.smul_nearLitter_coe, NearLitterPerm.smul_nearLitter_coe,
        ← Set.smul_set_symmDiff, Set.smul_mem_smul_set_iff]
      exact ha
  · rintro k ⟨hj, hk, a, N', hNN', ha, hN', ha'⟩
    cases hN₂.symm.trans (raiseRaise_not_raiseIndex ρ₂ h hN₁)
    refine ⟨hj, hk, a, N', hNN', ha, ?_, ?_⟩
    · rw [raiseRaise_not_raiseIndex ρ₂ h hN']
    · rw [raiseRaise_not_raiseIndex ρ₂ h ha']

theorem raiseRaise_inflexibleCoe_spec₁_support
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ₁⁻¹ • c = ρ₂⁻¹ • c)
    {A : ExtendedIndex α} {N : NearLitter} (h : InflexibleCoe A N.1)
    {i : κ} {hi : i < S.max} (hN : S.f i hi = ⟨A, inr N⟩)
    (j : κ) :
    {k | ∃ (hj : j < h.t.support.max) (hk : k < (raiseRaise hγ S T ρ₁).max),
      ⟨(h.path.B.cons h.path.hδ).comp (h.t.support.f j hj).path, (h.t.support.f j hj).value⟩ =
      (raiseRaise hγ S T ρ₁).f k hk} ⊆
    {k | ∃ (hj : j < h.t.support.max) (hk : k < (raiseRaise hγ S T ρ₂).max),
      ⟨(h.path.B.cons h.path.hδ).comp (h.t.support.f j hj).path, (h.t.support.f j hj).value⟩ =
      (raiseRaise hγ S T ρ₂).f k hk} := by
  rintro k ⟨hj, hk, h₁⟩
  refine ⟨hj, hk, ?_⟩
  obtain (h₂ | ⟨B, hB, h₂⟩) := raiseRaise_cases' ρ₁ ρ₂ h₁.symm
  · rw [h₂]
  · simp only [Tangle.coe_support, h₂, map_mul, map_inv, Tree.mul_apply, Tree.inv_apply,
      Address.mk.injEq, true_and]
    have := hρS ⟨B, (h.t.support.f j hj).value⟩ ?_
    · rw [← smul_eq_iff_eq_inv_smul] at this
      simp only [Tangle.coe_support, Allowable.smul_address, map_inv, Tree.inv_apply,
        Address.mk.injEq, true_and, smul_smul] at this
      exact this.symm
    · rw [raise, ← hB]
      have := hS.precedes hi
          ⟨(h.path.B.cons h.path.hδ).comp (h.t.support.f j hj).path, (h.t.support.f j hj).value⟩ ?_
      · obtain ⟨l, hl, -, h⟩ := this
        exact ⟨l, hl, h.symm⟩
      · simp_rw [hN, h.path.hA]
        exact Precedes.fuzz A N h _ ⟨j, hj, rfl⟩

theorem raiseRaise_inflexibleCoe_spec₂_support
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ₁⁻¹ • c = ρ₂⁻¹ • c)
    {A : ExtendedIndex β} (P : InflexibleCoePath A)
    (t : Tangle P.δ) (j : κ) :
    {k | ∃ (hj : j < t.support.max) (hk : k < (raiseRaise hγ S T ρ₁).max),
      ⟨(((Hom.toPath iβ.elim).comp P.B).cons P.hδ).comp (t.support.f j hj).path,
        ((Allowable.comp (P.B.cons P.hδ) ρ₁ • t).support.f j hj).value⟩ =
        (raiseRaise hγ S T ρ₁).f k hk} ⊆
    {k | ∃ (hj : j < t.support.max) (hk : k < (raiseRaise hγ S T ρ₂).max),
      ⟨(((Hom.toPath iβ.elim).comp P.B).cons P.hδ).comp (t.support.f j hj).path,
        ((Allowable.comp (P.B.cons P.hδ) ρ₂ • t).support.f j hj).value⟩ =
        (raiseRaise hγ S T ρ₂).f k hk} := by
  rintro k ⟨hj, hk, h₁⟩
  refine ⟨hj, hk, ?_⟩
  rw [← Path.comp_cons, Path.comp_assoc] at h₁ ⊢
  rw [raiseRaise_raiseIndex hρS h₁.symm]
  simp only [Tangle.coe_support, raiseIndex, map_mul, map_inv, Tree.mul_apply, Tree.inv_apply,
    mul_smul, Address.mk.injEq, true_and]
  have : (Allowable.comp (P.B.cons P.hδ) ρ₁ • t).support.f j hj =
      Allowable.comp (P.B.cons P.hδ) ρ₁ • t.support.f j hj
  · simp only [Tangle.coe_support]
    rfl
  erw [this]
  have : (Allowable.comp (P.B.cons P.hδ) ρ₂ • t).support.f j hj =
      Allowable.comp (P.B.cons P.hδ) ρ₂ • t.support.f j hj
  · simp only [Tangle.coe_support]
    rfl
  erw [this]
  simp only [Tangle.coe_support, Allowable.smul_address, Allowable.toStructPerm_comp,
    Tree.comp_apply, inv_smul_smul]

theorem raiseRaise_inflexibleBot_spec₁_atom
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ₁⁻¹ • c = ρ₂⁻¹ • c)
    {i : κ} {hi : i < S.max}
    {A : ExtendedIndex α} {N : NearLitter} (h : InflexibleBot A N.1)
    (hN : S.f i hi = ⟨A, inr N⟩) :
    {j | ∃ (hj : j < (raiseRaise hγ S T ρ₁).max),
      (raiseRaise hγ S T ρ₁).f j hj = ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩} ⊆
    {j | ∃ (hj : j < (raiseRaise hγ S T ρ₂).max),
      (raiseRaise hγ S T ρ₂).f j hj = ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩} := by
  rintro j ⟨hj, hja⟩
  refine ⟨hj, ?_⟩
  by_cases hB : ∃ B : ExtendedIndex β, h.path.B.cons (bot_lt_coe _) = raiseIndex iβ.elim B
  · obtain ⟨B, hB⟩ := hB
    have := hρS ⟨B, inl h.a⟩ ?_
    · rw [hB] at hja ⊢
      rw [raiseRaise_raiseIndex hρS hja]
      simp only [Allowable.smul_address_eq_smul_iff, map_inv, Tree.inv_apply, smul_inl, inl.injEq,
        map_mul, Tree.mul_apply, mul_smul, Address.mk.injEq, true_and] at this ⊢
      rw [smul_eq_iff_eq_inv_smul, this]
    · rw [raise, ← hB]
      have := hS.precedes hi ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩ ?_
      · obtain ⟨j, hj, -, hj'⟩ := this
        exact ⟨j, hj, hj'.symm⟩
      · simp_rw [hN, h.path.hA]
        exact Precedes.fuzzBot A N h
  · exact raiseRaise_not_raiseIndex ρ₂ hB hja

theorem raiseRaise_inflexibleBot_spec₂_atom
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ₁⁻¹ • c = ρ₂⁻¹ • c)
    {A : ExtendedIndex β} (P : InflexibleBotPath A) (a : Atom) :
    {j | ∃ (hj : j < (raiseRaise hγ S T ρ₁).max), (raiseRaise hγ S T ρ₁).f j hj =
      ⟨((Hom.toPath iβ.elim).comp P.B).cons (bot_lt_coe _),
      inl (Allowable.toStructPerm ρ₁ (P.B.cons (bot_lt_coe _)) • a)⟩} ⊆
    {j | ∃ (hj : j < (raiseRaise hγ S T ρ₂).max), (raiseRaise hγ S T ρ₂).f j hj =
      ⟨((Hom.toPath iβ.elim).comp P.B).cons (bot_lt_coe _),
      inl (Allowable.toStructPerm ρ₂ (P.B.cons (bot_lt_coe _)) • a)⟩} := by
  rintro j ⟨hj, hja⟩
  refine ⟨hj, ?_⟩
  rw [← Path.comp_cons] at hja ⊢
  rw [raiseRaise_raiseIndex hρS hja]
  simp only [raiseIndex, Path.comp_cons, map_mul, map_inv, Tree.mul_apply, Tree.inv_apply, mul_smul,
    smul_inl, inv_smul_smul]

theorem raiseRaise_specifies_atom_spec
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c) {σ : Spec α}
    (hσ : σ.Specifies (raiseRaise hγ S T 1) (raiseRaise_strong hS (fun c _ => by rw [one_smul])))
    (i : κ) (hi : i < (raiseRaise hγ S T ρ).max) (A : ExtendedIndex α) (a : Atom) :
    (raiseRaise hγ S T ρ).f i hi = ⟨A, inl a⟩ →
    σ.f i (hi.trans_eq hσ.max_eq_max) = SpecCondition.atom A
      {j | ∃ hj, (raiseRaise hγ S T ρ).f j hj = ⟨A, inl a⟩}
      {j | ∃ hj N, (raiseRaise hγ S T ρ).f j hj = ⟨A, inr N⟩ ∧ a ∈ N} := by
  intro ha
  obtain ⟨b, hb⟩ := raiseRaise_f_eq_atom (ρ₂ := 1) i hi A a ha
  rw [hσ.atom_spec i hi A b hb, SpecCondition.atom.injEq]
  refine ⟨rfl, ?_, ?_⟩
  · refine subset_antisymm ?_ ?_
    · refine raiseRaise_atom_spec₁ ?_ hb ha
      intro c hc
      rw [one_smul, hρS]
      rwa [one_smul] at hc
    · refine raiseRaise_atom_spec₁ ?_ ha hb
      intro c hc
      have := hρS (ρ • c) hc
      rw [smul_left_cancel_iff] at this
      rwa [one_smul]
  · refine subset_antisymm ?_ ?_
    · refine raiseRaise_atom_spec₂ ?_ hb ha
      intro c hc
      rw [inv_one, one_smul, eq_inv_smul_iff]
      exact hρS c hc
    · refine raiseRaise_atom_spec₂ ?_ ha hb
      intro c hc
      rw [inv_one, one_smul, inv_smul_eq_iff]
      exact (hρS c hc).symm

theorem raiseRaise_specifies_flexible_spec
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c) {σ : Spec α}
    (hσ : σ.Specifies (raiseRaise hγ S T 1) (raiseRaise_strong hS (fun c _ => by rw [one_smul])))
    (i : κ) (hi : i < (raiseRaise hγ S T ρ).max) (A : ExtendedIndex α) (N₁ : NearLitter) :
    Flexible A N₁.1 → (raiseRaise hγ S T ρ).f i hi = ⟨A, inr N₁⟩ →
    σ.f i (hi.trans_eq hσ.max_eq_max) = SpecCondition.flexible A
      {j | ∃ hj, ∃ (N' : NearLitter), (raiseRaise hγ S T ρ).f j hj = ⟨A, inr N'⟩ ∧ N'.1 = N₁.1}
      (fun j => {k | ∃ hj hk, ∃ (a : Atom) (N' : NearLitter),
        N'.1 = N₁.1 ∧ a ∈ (N₁ : Set Atom) ∆ N' ∧
        (raiseRaise hγ S T ρ).f j hj = ⟨A, inr N'⟩ ∧
        (raiseRaise hγ S T ρ).f k hk = ⟨A, inl a⟩}) := by
  intro h hN₁
  obtain ⟨N₂, hN₂⟩ := raiseRaise_f_eq_nearLitter (ρ₂ := 1) i hi A N₁ hN₁
  obtain (hi' | ⟨hi, hi', A, rfl⟩) := raiseRaise_cases_nearLitter hN₁ hN₂
  · have : N₁ = N₂
    · rw [raiseRaise_f_eq₁ hi'] at hN₁ hN₂
      cases hN₁.symm.trans hN₂
      rfl
    cases this
    rw [hσ.flexible_spec i hi A N₁ h hN₂]
    simp only [SpecCondition.flexible.injEq, true_and]
    refine ⟨?_, ?_⟩
    · refine subset_antisymm ?_ ?_
      · refine raiseRaise_flexibleCoe_spec_eq ?_ (by exact hi) hN₂ hN₁
        intro c hc
        rw [inv_one, one_smul, ← smul_eq_iff_eq_inv_smul, hρS c hc]
      · refine raiseRaise_flexibleCoe_spec_eq ?_ hi hN₁ hN₂
        intro c hc
        rw [inv_one, one_smul, inv_smul_eq_iff, hρS c hc]
    · ext j : 1
      refine subset_antisymm ?_ ?_
      · refine raiseRaise_symmDiff ?_ hN₂ hN₁ j
        intro c hc
        rw [inv_one, one_smul, ← smul_eq_iff_eq_inv_smul, hρS c hc]
      · refine raiseRaise_symmDiff ?_ hN₁ hN₂ j
        intro c hc
        rw [inv_one, one_smul, inv_smul_eq_iff, hρS c hc]
  · have h' := raiseRaise_flexible₃ hi hi' hN₁ hN₂ h
    rw [hσ.flexible_spec i (raiseRaise_hi₂ hi') (raiseIndex iβ.elim A) N₂ h' hN₂]
    simp only [SpecCondition.flexible.injEq, true_and]
    refine ⟨?_, ?_⟩
    · refine subset_antisymm ?_ ?_
      · refine raiseRaise_flexibleCoe_spec_eq ?_ ‹_› hN₂ hN₁
        intro c hc
        rw [inv_one, one_smul, ← smul_eq_iff_eq_inv_smul, hρS c hc]
      · refine raiseRaise_flexibleCoe_spec_eq ?_ ‹_› hN₁ hN₂
        intro c hc
        rw [inv_one, one_smul, inv_smul_eq_iff, hρS c hc]
    · ext j : 1
      refine subset_antisymm ?_ ?_
      · refine raiseRaise_symmDiff ?_ hN₂ hN₁ j
        intro c hc
        rw [inv_one, one_smul, ← smul_eq_iff_eq_inv_smul, hρS c hc]
      · refine raiseRaise_symmDiff ?_ hN₁ hN₂ j
        intro c hc
        rw [inv_one, one_smul, inv_smul_eq_iff, hρS c hc]

theorem raiseRaise_specifies_inflexibleCoe_spec
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c) {σ : Spec α}
    (hσ : σ.Specifies (raiseRaise hγ S T 1) (raiseRaise_strong hS (fun c _ => by rw [one_smul])))
    (i : κ) (hi : i < (raiseRaise hγ S T ρ).max) (A : ExtendedIndex α) (N₁ : NearLitter)
    (h : InflexibleCoe A N₁.1) (hN₁ : (raiseRaise hγ S T ρ).f i hi = ⟨A, inr N₁⟩) :
    σ.f i (hi.trans_eq hσ.max_eq_max) = SpecCondition.inflexibleCoe A h.path
      (CodingFunction.code (((raiseRaise hγ S T ρ).before i hi).comp (h.path.B.cons h.path.hδ))
        h.t.set (Spec.before_comp_supports'
          (raiseRaise hγ S T ρ) (raiseRaise_strong hS hρS) hi h hN₁))
      (fun j => {k | ∃ hj hk, ∃ (a : Atom) (N' : NearLitter),
        N'.1 = N₁.1 ∧ a ∈ (N₁ : Set Atom) ∆ N' ∧
        (raiseRaise hγ S T ρ).f j hj = ⟨A, inr N'⟩ ∧ (raiseRaise hγ S T ρ).f k hk = ⟨A, inl a⟩})
      h.t.support.max
      (fun j => {k | ∃ (hj : j < h.t.support.max) (hk : k < (raiseRaise hγ S T ρ).max),
        ⟨(h.path.B.cons h.path.hδ).comp (h.t.support.f j hj).1, (h.t.support.f j hj).2⟩ =
          (raiseRaise hγ S T ρ).f k hk}) := by
  obtain ⟨N₂, hN₂⟩ := raiseRaise_f_eq_nearLitter (ρ₂ := 1) i hi A N₁ hN₁
  obtain (hi' | ⟨hi, hi', A, rfl⟩) := raiseRaise_cases_nearLitter hN₁ hN₂
  · have : N₁ = N₂
    · rw [raiseRaise_f_eq₁ hi'] at hN₁ hN₂
      cases hN₁.symm.trans hN₂
      rfl
    cases this
    rw [hσ.inflexibleCoe_spec i hi A N₁ h hN₂]
    simp only [Tangle.coe_set, Tangle.coe_support, SpecCondition.inflexibleCoe.injEq, heq_eq_eq,
      CodingFunction.code_eq_code_iff, true_and]
    refine ⟨?_, ?_, ?_⟩
    · rw [raiseRaise_f_eq₁ hi'] at hN₁ hN₂
      exact raiseRaise_inflexibleCoe_spec₁_comp_before (hγ := hγ) hi' h
    · ext j : 1
      refine subset_antisymm ?_ ?_
      · refine raiseRaise_symmDiff ?_ hN₂ hN₁ j
        intro c hc
        rw [inv_one, one_smul, ← smul_eq_iff_eq_inv_smul, hρS c hc]
      · refine raiseRaise_symmDiff ?_ hN₁ hN₂ j
        intro c hc
        rw [inv_one, one_smul, inv_smul_eq_iff, hρS c hc]
    · ext j : 1
      refine subset_antisymm ?_ ?_
      · refine raiseRaise_inflexibleCoe_spec₁_support hS ?_ h
          (raiseRaise_f_eq₁ (hγ := hγ) hi' ▸ hN₁) j
        intro c hc
        rw [inv_one, one_smul, ← smul_eq_iff_eq_inv_smul, hρS c hc]
      · refine raiseRaise_inflexibleCoe_spec₁_support hS ?_ h
          (raiseRaise_f_eq₁ (hγ := hγ) hi' ▸ hN₁) j
        intro c hc
        rw [inv_one, one_smul, inv_smul_eq_iff, hρS c hc]
  · obtain ⟨P, t, hN₁', hN₂'⟩ := raiseRaise_inflexibleCoe₃ hi hi' hN₁ hN₂ h
    cases Subsingleton.elim h ⟨P.comp _, _, hN₁'⟩
    rw [hσ.inflexibleCoe_spec i
      (raiseRaise_hi₂ hi') (raiseIndex iβ.elim A) N₂ ⟨P.comp _, _, hN₂'⟩ hN₂]
    simp only [InflexibleCoePath.comp_δ, InflexibleCoePath.comp_γ, InflexibleCoePath.comp_B,
      map_one, one_smul, Tangle.coe_set, Tangle.coe_support, SpecCondition.inflexibleCoe.injEq,
      heq_eq_eq, CodingFunction.code_eq_code_iff, true_and]
    refine ⟨?_, ?_, rfl, ?_⟩
    · rw [raiseRaise_f_eq₂ hi hi'] at hN₁ hN₂
      rw [one_smul] at hN₂
      have := raise_injective' hN₁
      rw [raise_injective' hN₂] at this
      simp only [map_one, one_smul] at hN₂'
      exact raiseRaise_inflexibleCoe_spec₂_comp_before hρS hi' P t
    · ext j : 1
      refine subset_antisymm ?_ ?_
      · refine raiseRaise_symmDiff ?_ hN₂ hN₁ j
        intro c hc
        rw [inv_one, one_smul, ← smul_eq_iff_eq_inv_smul, hρS c hc]
      · refine raiseRaise_symmDiff ?_ hN₁ hN₂ j
        intro c hc
        rw [inv_one, one_smul, inv_smul_eq_iff, hρS c hc]
    · ext j : 1
      refine subset_antisymm ?_ ?_
      · have := raiseRaise_inflexibleCoe_spec₂_support (ρ₁ := 1) (ρ₂ := ρ)
            (hγ := hγ) (S := S) (T := T) ?_ P t j
        · simp only [map_one, one_smul] at this ⊢
          exact this
        · intro c hc
          rw [inv_one, one_smul, ← smul_eq_iff_eq_inv_smul, hρS c hc]
      · have := raiseRaise_inflexibleCoe_spec₂_support (ρ₁ := ρ) (ρ₂ := 1)
            (hγ := hγ) (S := S) (T := T) ?_ P t j
        · simp only [map_one, one_smul] at this ⊢
          exact this
        · intro c hc
          rw [inv_one, one_smul, inv_smul_eq_iff, hρS c hc]

theorem raiseRaise_specifies_inflexibleBot_spec
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c) {σ : Spec α}
    (hσ : σ.Specifies (raiseRaise hγ S T 1) (raiseRaise_strong hS (fun c _ => by rw [one_smul])))
    (i : κ) (hi : i < (raiseRaise hγ S T ρ).max)
    (A : ExtendedIndex α) (N₁ : NearLitter) (h : InflexibleBot A N₁.1) :
    (raiseRaise hγ S T ρ).f i hi = ⟨A, inr N₁⟩ →
    σ.f i (hi.trans_eq hσ.max_eq_max) = SpecCondition.inflexibleBot A h.path
      {j | ∃ hj, (raiseRaise hγ S T ρ).f j hj = ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩}
      (fun j => {k | ∃ hj hk, ∃ (a : Atom) (N' : NearLitter),
        N'.1 = N₁.1 ∧ a ∈ (N₁ : Set Atom) ∆ N' ∧
        (raiseRaise hγ S T ρ).f j hj = ⟨A, inr N'⟩ ∧
        (raiseRaise hγ S T ρ).f k hk = ⟨A, inl a⟩}) := by
  intro hN₁
  obtain ⟨N₂, hN₂⟩ := raiseRaise_f_eq_nearLitter (ρ₂ := 1) i hi A N₁ hN₁
  obtain (hi' | ⟨hi, hi', A, rfl⟩) := raiseRaise_cases_nearLitter hN₁ hN₂
  · have : N₁ = N₂
    · rw [raiseRaise_f_eq₁ hi'] at hN₁ hN₂
      cases hN₁.symm.trans hN₂
      rfl
    cases this
    rw [hσ.inflexibleBot_spec i hi A N₁ h hN₂]
    simp only [SpecCondition.inflexibleBot.injEq, heq_eq_eq, true_and]
    refine ⟨?_, ?_⟩
    · rw [raiseRaise_f_eq₁ hi'] at hN₁ hN₂
      refine subset_antisymm ?_ ?_
      · refine raiseRaise_inflexibleBot_spec₁_atom hS ?_ h hN₂
        intro c hc
        rw [inv_one, one_smul, ← smul_eq_iff_eq_inv_smul, hρS c hc]
      · refine raiseRaise_inflexibleBot_spec₁_atom hS ?_ h hN₂
        intro c hc
        rw [inv_one, one_smul, inv_smul_eq_iff, hρS c hc]
    · ext j : 1
      refine subset_antisymm ?_ ?_
      · refine raiseRaise_symmDiff ?_ hN₂ hN₁ j
        intro c hc
        rw [inv_one, one_smul, ← smul_eq_iff_eq_inv_smul, hρS c hc]
      · refine raiseRaise_symmDiff ?_ hN₁ hN₂ j
        intro c hc
        rw [inv_one, one_smul, inv_smul_eq_iff, hρS c hc]
  · obtain ⟨P, a, hN₁', hN₂'⟩ := raiseRaise_inflexibleBot₃ hi hi' hN₁ hN₂ h
    cases Subsingleton.elim h ⟨P.comp _, _, hN₁'⟩
    rw [hσ.inflexibleBot_spec i
      (raiseRaise_hi₂ hi') (raiseIndex iβ.elim A) N₂ ⟨P.comp _, _, hN₂'⟩ hN₂]
    simp only [InflexibleBotPath.comp_γ, InflexibleBotPath.comp_B, map_one, Tree.one_apply,
      one_smul, SpecCondition.inflexibleBot.injEq, heq_eq_eq, true_and]
    refine ⟨?_, ?_⟩
    · rw [raiseRaise_f_eq₂ hi hi'] at hN₁ hN₂
      rw [one_smul] at hN₂
      have := raise_injective' hN₁
      rw [raise_injective' hN₂] at this
      simp only [map_one, one_smul] at hN₂'
      refine subset_antisymm ?_ ?_
      · have := raiseRaise_inflexibleBot_spec₂_atom
            (hγ := hγ) (S := S) (T := T) (ρ₁ := 1) (ρ₂ := ρ) ?_ P a
        · simp only [map_one, Tree.one_apply, one_smul] at this
          exact this
        · intro c hc
          rw [inv_one, one_smul, ← smul_eq_iff_eq_inv_smul, hρS c hc]
      · have := raiseRaise_inflexibleBot_spec₂_atom
            (hγ := hγ) (S := S) (T := T) (ρ₁ := ρ) (ρ₂ := 1) ?_ P a
        · simp only [map_one, Tree.one_apply, one_smul] at this
          exact this
        · intro c hc
          rw [inv_one, one_smul, inv_smul_eq_iff, hρS c hc]
    · ext j : 1
      refine subset_antisymm ?_ ?_
      · refine raiseRaise_symmDiff ?_ hN₂ hN₁ j
        intro c hc
        rw [inv_one, one_smul, ← smul_eq_iff_eq_inv_smul, hρS c hc]
      · refine raiseRaise_symmDiff ?_ hN₁ hN₂ j
        intro c hc
        rw [inv_one, one_smul, inv_smul_eq_iff, hρS c hc]

theorem raiseRaise_specifies (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : Allowable β)
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c) {σ : Spec α}
    (hσ : σ.Specifies (raiseRaise hγ S T 1) (raiseRaise_strong hS (fun c _ => by rw [one_smul]))) :
    σ.Specifies (raiseRaise hγ S T ρ) (raiseRaise_strong hS hρS) where
  max_eq_max := raiseRaise_max_eq_max.symm.trans hσ.max_eq_max
  atom_spec := raiseRaise_specifies_atom_spec hS hρS hσ
  flexible_spec := raiseRaise_specifies_flexible_spec hS hρS hσ
  inflexibleCoe_spec := raiseRaise_specifies_inflexibleCoe_spec hS hρS hσ
  inflexibleBot_spec := raiseRaise_specifies_inflexibleBot_spec hS hρS hσ

theorem raiseRaise_eq_smul (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : Allowable β)
    (hρS : ∀ c : Address β, raise iβ.elim c ∈ S → ρ • c = c) :
    ∃ ρ' : Allowable α, ρ' • S = S ∧ Allowable.comp ((Hom.toPath iβ.elim).cons hγ) ρ' • T =
      Allowable.comp (Hom.toPath hγ) ρ • T := by
  have hσ := raiseRaise_specifies (hγ := hγ) S hS T ρ hρS (spec_specifies _ _)
  have hρ := convertAllowable_smul (spec_specifies _ _) hσ
  refine ⟨convertAllowable (spec_specifies _ _) hσ, ?_, ?_⟩
  · refine Enumeration.ext' rfl ?_
    intro i hi hi'
    have := support_f_congr hρ i (raiseRaise_hi₁ hi)
    rw [Enumeration.smul_f, raiseRaise_f_eq₁ hi', raiseRaise_f_eq₁ hi'] at this
    exact this
  · refine Enumeration.ext' rfl ?_
    intro i hi hi'
    obtain ⟨j, hj, hc⟩ := subset_strongSupport (T.image (raise hγ)).small ⟨i, hi', rfl⟩
    have hj₁ : S.max ≤ S.max + j
    · rw [le_add_iff_nonneg_right]
      exact κ_pos _
    have hj₂ : S.max + j < S.max + (strongSupport (T.image (raise hγ)).small).max
    · rw [add_lt_add_iff_left]
      exact hj
    have := support_f_congr hρ (S.max + j) (raiseRaise_hi₂ hj₂)
    rw [Enumeration.smul_f, raiseRaise_f_eq₂ hj₁ hj₂, raiseRaise_f_eq₂ hj₁ hj₂] at this
    simp_rw [κ_add_sub_cancel, one_smul] at this
    rw [Enumeration.image_f] at hc
    rw [← hc] at this
    have := congr_arg Address.value this
    simp only [Allowable.smul_address, raise_path, raise_value, raiseIndex, Hom.toPath] at this
    simp only [Enumeration.smul_f, Allowable.smul_address_eq_smul_iff, Allowable.toStructPerm_comp,
      Tree.comp_apply, Hom.toPath]
    rw [← Path.comp_assoc, Path.comp_cons] at this
    exact this

end ConNF.Support
