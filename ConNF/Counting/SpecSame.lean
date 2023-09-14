import ConNF.Foa
import ConNF.Counting.OrdSupportEquiv
import ConNF.Counting.Spec

/-!
# Specifying two strong supports at once
-/

open Quiver Set Sum WithBot

open scoped Classical

universe u

namespace ConNF

/-!
The assumptions are as follows.

`S` and `T` are ordered supports, and we aim to produce an allowable permutation `ρ` such that
`ρ • S = T` under the hypothesis that `σ` specifies both `S` and `T`.
Note that this enforces that the set of indices in `μ` used in `S` and `T` agree.

We assume that `S` is a strong support, and that `T` is equivalent to a strong support `U`.
This condition will be relaxed later. The reordering `r` can be used to reinterpret the indices in
`T` in their "correct" positions in `U`.
-/

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}
  {σ : Spec β} {S T U : OrdSupport β}
  (hσS : Specifies σ S) (hσT : Specifies σ T)
  {r : Tree Reorder β} (hr : OrdSupport.IsEquiv r U T)
  (hS : S.Strong) (hU: U.Strong)

namespace Spec

set_option pp.proofs.withType false

/-- Because `σ` specifies a strong support `S` as well as `T`, `T` must assign its atoms
at "atom times": their positions must be indexed by an atom. -/
theorem cpos_atom (A : ExtendedIndex β) (a : Atom) (ha : ⟨A, inl a⟩ ∈ T) :
    ∃ b, (T.cpos ⟨A, inl a⟩).get ha = inl b := by
  obtain ⟨⟨B, x⟩, hc₁, hc₂⟩ := hσS.exists_mem_of_dom _ (hσT.cpos_dom _ ha)
  rw [Prod.ext_iff] at hc₂
  cases hc₂.2
  simp only [hS.cpos_get_eq, and_true] at hc₂
  rw [hc₂]
  obtain (b | N) := x
  · exact ⟨b, rfl⟩
  exfalso
  have := hS.reduced_of_mem _ hc₁
  simp only [Reduced_iff, exists_false, inr.injEq, false_or] at this
  obtain ⟨L, rfl⟩ := this
  have hcT := hσT.atom_spec A a a.1.toNearLitter ha (hU.fst_toNearLitter_mem_equiv hr.equiv ha) rfl
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A L
  · have hcS := hσS.flexible_spec A L.toNearLitter hc₁ hL
    simp_rw [hS.cpos_get_eq, ← hc₂, hcT] at hcS
  · obtain ⟨_, hcS⟩ := hσS.inflexibleBot_spec A L.toNearLitter hc₁ hL
    simp_rw [hS.cpos_get_eq, ← hc₂, hcT] at hcS
  · obtain ⟨_, _, _, hcS⟩ := hσS.inflexibleCoe_spec A L.toNearLitter hc₁ hL
    simp_rw [hS.cpos_get_eq, ← hc₂, hcT] at hcS

/-- Because `σ` specifies a strong support `S` as well as `T`, `T` must assign its near-litters
at "litter times": their positions must be indexed by a litter. -/
theorem cpos_nearLitter (A : ExtendedIndex β) (N : NearLitter) (hN : ⟨A, inr N⟩ ∈ T) :
    ∃ L : Litter, (T.cpos ⟨A, inr N⟩).get hN = inr L.toNearLitter := by
  obtain ⟨⟨B, x⟩, hc₁, hc₂⟩ := hσS.exists_mem_of_dom _ (hσT.cpos_dom _ hN)
  rw [Prod.ext_iff] at hc₂
  cases hc₂.2
  simp only [hS.cpos_get_eq, and_true] at hc₂
  rw [hc₂]
  obtain (b | N') := x
  swap
  · obtain ⟨L'⟩ := hS.isLitter_of_mem hc₁
    exact ⟨L', rfl⟩
  exfalso
  have hcS := hσS.atom_spec A b b.1.toNearLitter hc₁ (hS.fst_toNearLitter_mem hc₁) rfl
  have := hU.reduced_of_mem_equiv hr.equiv _ hN
  simp only [Reduced_iff, exists_false, inr.injEq, false_or] at this
  obtain ⟨L, rfl⟩ := this
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A L
  · have hcT := hσT.flexible_spec A L.toNearLitter hN hL
    simp_rw [hS.cpos_get_eq, ← hc₂, hcT] at hcS
  · obtain ⟨_, hcT⟩ := hσT.inflexibleBot_spec A L.toNearLitter hN hL
    simp_rw [hS.cpos_get_eq, ← hc₂, hcT] at hcS
  · obtain ⟨_, _, _, hcT⟩ := hσT.inflexibleCoe_spec A L.toNearLitter hN hL
    simp_rw [hS.cpos_get_eq, ← hc₂, hcT] at hcS

variable (T)

/-- Maps atoms in a strong support (in our case, `S`) to atoms in `T`
assigned the same position. -/
noncomputable def convertAtom (A : ExtendedIndex β) (a : Atom) : Part Atom :=
  ⟨∃ b : Atom, ∃ h : ⟨A, inl b⟩ ∈ T, (T.cpos ⟨A, inl b⟩).get h = inl a,
    Exists.choose⟩

/-- Maps litters in a strong support (in our case, `S`) to near-litters in `T`
assigned the same position. -/
noncomputable def convertLitter (A : ExtendedIndex β) (L : Litter) : Part NearLitter :=
  ⟨∃ N : NearLitter, ∃ h : ⟨A, inr N⟩ ∈ T, (T.cpos ⟨A, inr N⟩).get h = inr L.toNearLitter,
    Exists.choose⟩

/-- Maps atoms in a support `T` to the atom in a strong support in the same position. -/
noncomputable def deconvertAtom (A : ExtendedIndex β) (a : Atom) : Part Atom :=
  ⟨∃ b : Atom, ∃ h : ⟨A, inl a⟩ ∈ T, (T.cpos ⟨A, inl a⟩).get h = inl b,
    Exists.choose⟩

/-- Maps near-litters in a support `T` to the litter in a strong support in the same position. -/
noncomputable def deconvertLitter (A : ExtendedIndex β) (N : NearLitter) : Part Litter :=
  ⟨∃ L : Litter, ∃ h : ⟨A, inr N⟩ ∈ T, (T.cpos ⟨A, inr N⟩).get h = inr L.toNearLitter,
    Exists.choose⟩

variable {T}

theorem convertAtom_dom (A : ExtendedIndex β) (a : Atom) :
    (convertAtom T A a).Dom ↔ ⟨A, inl a⟩ ∈ S := by
  have := Specifies.dom_iff hσT ⟨inl a, A⟩
  rw [hσS.dom_iff ⟨inl a, A⟩] at this
  simp_rw [hS.cpos_get_eq] at this
  constructor
  · rintro ⟨b, hbT, h⟩
    obtain ⟨c, h₁, h₂⟩ := this.mpr ⟨_, hbT, Prod.ext h.symm rfl⟩
    suffices : c = ⟨A, inl a⟩
    · rwa [this] at h₁
    rw [Prod.ext_iff] at h₂
    exact SupportCondition.ext _ _ h₂.2.symm h₂.1.symm
  · intro h
    obtain ⟨c, h₁, h₂⟩ := this.mp ⟨_, h, rfl⟩
    rw [Prod.ext_iff] at h₂
    obtain ⟨A, b | N⟩ := c <;> cases h₂.2
    · exact ⟨b, h₁, h₂.1.symm⟩
    · obtain ⟨L, hL⟩ := cpos_nearLitter hσS hσT hr hS hU A N h₁
      rw [hL] at h₂
      simp only at h₂

theorem convertLitter_dom (A : ExtendedIndex β) (L : Litter) :
    (convertLitter T A L).Dom ↔ ⟨A, inr L.toNearLitter⟩ ∈ S := by
  have := Specifies.dom_iff hσT ⟨inr L.toNearLitter, A⟩
  rw [hσS.dom_iff ⟨inr L.toNearLitter, A⟩] at this
  simp_rw [hS.cpos_get_eq] at this
  constructor
  · rintro ⟨N, hNT, h⟩
    obtain ⟨c, h₁, h₂⟩ := this.mpr ⟨_, hNT, Prod.ext h.symm rfl⟩
    rw [Prod.ext_iff] at h₂
    obtain ⟨A, a | N'⟩ := c <;> cases h₂.2
    · cases h₂.1
    · cases h₂.1
      exact h₁
  · intro h
    obtain ⟨c, h₁, h₂⟩ := this.mp ⟨_, h, rfl⟩
    rw [Prod.ext_iff] at h₂
    obtain ⟨A, a | N'⟩ := c <;> cases h₂.2
    · obtain ⟨L, hL⟩ := cpos_atom hσS hσT hr hS hU A a h₁
      simp only [hL] at h₂
    · exact ⟨N', h₁, h₂.1.symm⟩

theorem deconvertAtom_dom (A : ExtendedIndex β) (a : Atom) :
    (deconvertAtom T A a).Dom ↔ ⟨A, inl a⟩ ∈ T := by
  have := Specifies.dom_iff hσT ⟨inl a, A⟩
  rw [hσS.dom_iff ⟨inl a, A⟩] at this
  simp_rw [hS.cpos_get_eq] at this
  constructor
  · rintro ⟨b, hbT, _⟩
    exact hbT
  · intro h
    obtain ⟨b, hb⟩ := cpos_atom hσS hσT hr hS hU A a h
    exact ⟨b, h, hb⟩

theorem deconvertLitter_dom (A : ExtendedIndex β) (N : NearLitter) :
    (deconvertLitter T A N).Dom ↔ ⟨A, inr N⟩ ∈ T := by
  have := Specifies.dom_iff hσT ⟨inr N, A⟩
  rw [hσS.dom_iff ⟨inr N, A⟩] at this
  simp_rw [hS.cpos_get_eq] at this
  constructor
  · rintro ⟨b, hbT, _⟩
    exact hbT
  · intro h
    obtain ⟨L, hL⟩ := cpos_nearLitter hσS hσT hr hS hU A N h
    exact ⟨L, h, hL⟩

theorem convertAtom_mem {A : ExtendedIndex β} {a : Atom} (h : (convertAtom T A a).Dom) :
    ⟨A, inl ((convertAtom T A a).get h)⟩ ∈ T :=
  h.choose_spec.1

theorem convertLitter_mem {A : ExtendedIndex β} {L : Litter} (h : (convertLitter T A L).Dom) :
    ⟨A, inr ((convertLitter T A L).get h)⟩ ∈ T :=
  h.choose_spec.1

theorem deconvertAtom_mem {A : ExtendedIndex β} {a : Atom} (h : (deconvertAtom T A a).Dom) :
    ⟨A, inl a⟩ ∈ T :=
  h.choose_spec.1

theorem deconvertLitter_mem {A : ExtendedIndex β} {N : NearLitter}
    (h : (deconvertLitter T A N).Dom) : ⟨A, inr N⟩ ∈ T :=
  h.choose_spec.1

theorem convertAtom_get {A : ExtendedIndex β} {a : Atom} (h : (convertAtom T A a).Dom) :
    (T.cpos ⟨A, inl ((convertAtom T A a).get h)⟩).get (convertAtom_mem h) = inl a :=
  h.choose_spec.2

theorem convertLitter_get {A : ExtendedIndex β} {L : Litter} (h : (convertLitter T A L).Dom) :
    (T.cpos ⟨A, inr ((convertLitter T A L).get h)⟩).get (convertLitter_mem h) = inr L.toNearLitter :=
  h.choose_spec.2

theorem get_deconvertAtom {A : ExtendedIndex β} {a : Atom} (h : (deconvertAtom T A a).Dom) :
    (T.cpos ⟨A, inl a⟩).get (deconvertAtom_mem h) = inl ((deconvertAtom T A a).get h) :=
  h.choose_spec.2

theorem get_deconvertLitter {A : ExtendedIndex β} {N : NearLitter}
    (h : (deconvertLitter T A N).Dom) :
    (T.cpos ⟨A, inr N⟩).get (deconvertLitter_mem h) =
      inr ((deconvertLitter T A N).get h).toNearLitter :=
  h.choose_spec.2

theorem convertLitter_isLitter {A : ExtendedIndex β} {L : Litter}
    (h : (convertLitter T A L).Dom) :
    ((convertLitter T A L).get h).IsLitter := by
  have := hU.reduced_of_mem_equiv hr.equiv _ (convertLitter_mem h)
  simp only [Reduced_iff, exists_false, inr.injEq, false_or] at this
  obtain ⟨L, h⟩ := this
  rw [h]
  exact NearLitter.IsLitter.mk _

theorem convertAtom_deconvertAtom_dom {A : ExtendedIndex β} {a : Atom}
    (h : (convertAtom T A a).Dom) :
    (deconvertAtom T A ((convertAtom T A a).get h)).Dom :=
  ⟨a, h.choose_spec⟩

theorem convertLitter_deconvertLitter_dom {A : ExtendedIndex β} {L : Litter}
    (h : (convertLitter T A L).Dom) :
    (deconvertLitter T A ((convertLitter T A L).get h)).Dom :=
  ⟨L, h.choose_spec⟩

theorem deconvertAtom_convertAtom_dom {A : ExtendedIndex β} {a : Atom}
    (h : (deconvertAtom T A a).Dom) :
    (convertAtom T A ((deconvertAtom T A a).get h)).Dom :=
  ⟨a, h.choose_spec⟩

theorem deconvertLitter_convertLitter_dom {A : ExtendedIndex β} {N : NearLitter}
    (h : (deconvertLitter T A N).Dom) :
    (convertLitter T A ((deconvertLitter T A N).get h)).Dom :=
  ⟨N, h.choose_spec⟩

theorem deconvertAtom_mem' {A : ExtendedIndex β} {a : Atom} (h : (deconvertAtom T A a).Dom) :
    ⟨A, inl ((deconvertAtom T A a).get h)⟩ ∈ S := by
  have := deconvertAtom_convertAtom_dom h
  rw [convertAtom_dom hσS hσT hr hS hU] at this
  exact this

theorem deconvertLitter_mem' {A : ExtendedIndex β} {N : NearLitter}
    (h : (deconvertLitter T A N).Dom) :
    ⟨A, inr ((deconvertLitter T A N).get h).toNearLitter⟩ ∈ S := by
  have := deconvertLitter_convertLitter_dom h
  rw [convertLitter_dom hσS hσT hr hS hU] at this
  exact this

theorem convertAtom_deconvertAtom {A : ExtendedIndex β} {a : Atom}
    (h : (convertAtom T A a).Dom) :
    (deconvertAtom T A ((convertAtom T A a).get h)).get (convertAtom_deconvertAtom_dom h) = a := by
  have := get_deconvertAtom (convertAtom_deconvertAtom_dom h)
  rw [convertAtom_get h, inl.injEq] at this
  exact this.symm

theorem convertLitter_deconvertLitter {A : ExtendedIndex β} {L : Litter}
    (h : (convertLitter T A L).Dom) :
    (deconvertLitter T A ((convertLitter T A L).get h)).get
      (convertLitter_deconvertLitter_dom h) = L := by
  have := get_deconvertLitter (convertLitter_deconvertLitter_dom h)
  rw [convertLitter_get h, inr.injEq, Litter.toNearLitter_injective.eq_iff] at this
  exact this.symm

theorem deconvertAtom_convertAtom {A : ExtendedIndex β} {a : Atom}
    (h : (deconvertAtom T A a).Dom) :
    (convertAtom T A ((deconvertAtom T A a).get h)).get (deconvertAtom_convertAtom_dom h) = a := by
  have := get_deconvertAtom h
  rw [← convertAtom_get (deconvertAtom_convertAtom_dom h)] at this
  have := T.injective _ _ _ _ (by rfl) this
  simp only [SupportCondition.mk.injEq, inl.injEq, true_and] at this
  exact this.symm

theorem deconvertLitter_convertLitter {A : ExtendedIndex β} {N : NearLitter}
    (h : (deconvertLitter T A N).Dom) :
    (convertLitter T A ((deconvertLitter T A N).get h)).get
      (deconvertLitter_convertLitter_dom h) = N := by
  have := get_deconvertLitter h
  rw [← convertLitter_get (deconvertLitter_convertLitter_dom h)] at this
  have := T.injective _ _ _ _ (by rfl) this
  simp only [SupportCondition.mk.injEq, inr.injEq, true_and] at this
  exact this.symm

theorem convertAtom_injective (A : ExtendedIndex β) (a b : Atom)
    (ha : (convertAtom T A a).Dom) (hb : (convertAtom T A b).Dom)
    (hab : (convertAtom T A a).get ha = (convertAtom T A b).get hb) :
    a = b := by
  rw [← convertAtom_deconvertAtom ha, ← convertAtom_deconvertAtom hb]
  simp_rw [hab]

theorem convertLitter_injective (A : ExtendedIndex β) (L₁ L₂ : Litter)
    (h₁ : (convertLitter T A L₁).Dom) (h₂ : (convertLitter T A L₂).Dom)
    (h : (convertLitter T A L₁).get h₁ = (convertLitter T A L₂).get h₂) :
    L₁ = L₂ := by
  rw [← convertLitter_deconvertLitter h₁, ← convertLitter_deconvertLitter h₂]
  simp_rw [h]

theorem convertLitter_injective' (A : ExtendedIndex β) (L₁ L₂ : Litter)
    (h₁ : (convertLitter T A L₁).Dom) (h₂ : (convertLitter T A L₂).Dom)
    (h : Set.Nonempty (((convertLitter T A L₁).get h₁ : Set Atom) ∩
      (convertLitter T A L₂).get h₂)) :
    L₁ = L₂ := by
  refine convertLitter_injective A L₁ L₂ h₁ h₂ ?_
  rw [(convertLitter_isLitter hr hU h₁).eq_fst_toNearLitter,
    (convertLitter_isLitter hr hU h₂).eq_fst_toNearLitter] at h ⊢
  obtain ⟨a, ha₁, ha₂⟩ := h
  refine congr_arg _ ?_
  exact ha₁.symm.trans ha₂

theorem convertAtom_ran (A : ExtendedIndex β) :
    PFun.ran (convertAtom T A) = PFun.Dom (deconvertAtom T A) := by
  ext a : 1
  constructor
  · intro ⟨b, hb₁, hb₂⟩
    subst hb₂
    refine ⟨(deconvertAtom T A ((convertAtom T A b).get hb₁)).get ?_, ?_, ?_⟩
    · exact convertAtom_deconvertAtom_dom hb₁
    · exact convertAtom_mem hb₁
    · rw [get_deconvertAtom]
  · intro ha
    refine ⟨(deconvertAtom T A a).get ha, ?_, ?_⟩
    · exact deconvertAtom_convertAtom_dom ha
    · rw [deconvertAtom_convertAtom]

theorem convertLitter_ran (A : ExtendedIndex β) :
    PFun.ran (convertLitter T A) = PFun.Dom (deconvertLitter T A) := by
  ext N : 1
  constructor
  · intro ⟨L, h₁, h₂⟩
    subst h₂
    refine ⟨(deconvertLitter T A ((convertLitter T A L).get h₁)).get ?_, ?_, ?_⟩
    · exact convertLitter_deconvertLitter_dom h₁
    · exact convertLitter_mem h₁
    · rw [get_deconvertLitter]
  · intro hN
    refine ⟨(deconvertLitter T A N).get hN, ?_, ?_⟩
    · exact deconvertLitter_convertLitter_dom hN
    · rw [deconvertLitter_convertLitter]

theorem deconvertAtom_ran (A : ExtendedIndex β) :
    PFun.ran (deconvertAtom T A) = PFun.Dom (convertAtom T A) := by
  ext a : 1
  constructor
  · intro ⟨b, hb₁, hb₂⟩
    subst hb₂
    refine ⟨(convertAtom T A ((deconvertAtom T A b).get hb₁)).get ?_, ?_, ?_⟩
    · exact deconvertAtom_convertAtom_dom hb₁
    · rw [deconvertAtom_dom hσS hσT hr hS hU] at hb₁
      rw [deconvertAtom_convertAtom]
      exact hb₁
    · rw [convertAtom_get]
  · intro ha
    refine ⟨(convertAtom T A a).get ha, ?_, ?_⟩
    · exact convertAtom_deconvertAtom_dom ha
    · rw [convertAtom_deconvertAtom]

theorem deconvertLitter_ran (A : ExtendedIndex β) :
    PFun.ran (deconvertLitter T A) = PFun.Dom (convertLitter T A) := by
  ext L : 1
  constructor
  · intro ⟨N, h₁, h₂⟩
    subst h₂
    refine ⟨(convertLitter T A ((deconvertLitter T A N).get h₁)).get ?_, ?_, ?_⟩
    · exact deconvertLitter_convertLitter_dom h₁
    · rw [deconvertLitter_dom hσS hσT hr hS hU] at h₁
      rw [deconvertLitter_convertLitter]
      exact h₁
    · rw [convertLitter_get]
  · intro hL
    refine ⟨(convertLitter T A L).get hL, ?_, ?_⟩
    · exact convertLitter_deconvertLitter_dom hL
    · rw [convertLitter_deconvertLitter]

theorem mem_convertAtom_ran (A : ExtendedIndex β) (a : Atom) (ha : ⟨A, inl a⟩ ∈ T) :
    a ∈ PFun.ran (convertAtom T A) := by
  rw [convertAtom_ran, PFun.Dom, mem_setOf, deconvertAtom_dom hσS hσT hr hS hU]
  exact ha

theorem mem_convertLitter_ran (A : ExtendedIndex β) (N : NearLitter) (hN : ⟨A, inr N⟩ ∈ T) :
    N ∈ PFun.ran (convertLitter T A) := by
  rw [convertLitter_ran, PFun.Dom, mem_setOf, deconvertLitter_dom hσS hσT hr hS hU]
  exact hN

theorem mem_deconvertAtom_ran (A : ExtendedIndex β) (a : Atom) (ha : ⟨A, inl a⟩ ∈ S) :
    a ∈ PFun.ran (deconvertAtom T A) := by
  rw [deconvertAtom_ran hσS hσT hr hS hU, PFun.Dom, mem_setOf, convertAtom_dom hσS hσT hr hS hU]
  exact ha

theorem mem_deconvertLitter_ran (A : ExtendedIndex β) (L : Litter)
    (hL : ⟨A, inr L.toNearLitter⟩ ∈ S) : L ∈ PFun.ran (deconvertLitter T A) := by
  rw [deconvertLitter_ran hσS hσT hr hS hU, PFun.Dom, mem_setOf, convertLitter_dom hσS hσT hr hS hU]
  exact hL

theorem convertAtom_eq_of_eq_cpos {A : ExtendedIndex β} {a b : Atom} {hbT : ⟨A, inl b⟩ ∈ T}
    (ha : (convertAtom T A a).Dom)
    (hb : inl a = (T.cpos ⟨A, inl b⟩).get hbT) :
    (convertAtom T A a).get ha = b := by
  rw [← convertAtom_get ha] at hb
  have := T.injective _ _ _ _ (by rfl) hb
  simp only [SupportCondition.mk.injEq, inl.injEq, true_and] at this
  exact this

theorem convertLitter_eq_of_eq_cpos {A : ExtendedIndex β} {L : Litter} {N : NearLitter}
    {hbT : ⟨A, inr N⟩ ∈ T}
    (hL : (convertLitter T A L).Dom)
    (hN : inr L.toNearLitter = (T.cpos ⟨A, inr N⟩).get hbT) :
    (convertLitter T A L).get hL = N := by
  rw [← convertLitter_get hL] at hN
  have := T.injective _ _ _ _ (by rfl) hN
  simp only [SupportCondition.mk.injEq, inr.injEq, true_and] at this
  exact this

theorem convertAtom_dom_small (A : ExtendedIndex β) :
    Small (PFun.Dom (convertAtom T A)) := by
  change Small {a | (convertAtom T A a).Dom}
  simp only [convertAtom_dom hσS hσT hr hS hU A]
  refine S.dom_small.image_subset (fun a => ⟨A, inl a⟩) ?_ ?_
  · intros a b h
    cases h
    rfl
  · rintro _ ⟨a, h, rfl⟩
    exact h

theorem convertLitter_dom_small (A : ExtendedIndex β) :
    Small (PFun.Dom (convertLitter T A)) := by
  change Small {L | (convertLitter T A L).Dom}
  simp only [convertLitter_dom hσS hσT hr hS hU A]
  refine S.dom_small.image_subset (fun L => ⟨A, inr L.toNearLitter⟩) ?_ ?_
  · intros L₁ L₂ h
    cases h
    rfl
  · rintro _ ⟨L, h, rfl⟩
    exact h

/-- Convert atoms or litters in `S` to the equivalent atoms or litters in `T`. -/
noncomputable def convert : StructAction β :=
  fun A => {
    atomMap := convertAtom T A
    litterMap := convertLitter T A
    atomMap_dom_small := convertAtom_dom_small hσS hσT hr hS hU A
    litterMap_dom_small := convertLitter_dom_small hσS hσT hr hS hU A
  }

theorem convert_atomMap {A : ExtendedIndex β} :
    (convert hσS hσT hr hS hU A).atomMap = convertAtom T A :=
  rfl

theorem convert_litterMap {A : ExtendedIndex β} :
    (convert hσS hσT hr hS hU A).litterMap = convertLitter T A :=
  rfl

theorem _root_.ConNF.mem_toNearLitter {a : Atom} {L : Litter} :
    a ∈ L.toNearLitter ↔ a.1 = L :=
  Iff.rfl

theorem convertLitter_dom_of_convertAtom_dom {A : ExtendedIndex β} {a : Atom}
    (ha : (convertAtom T A a).Dom) : (convertLitter T A a.fst).Dom := by
  rw [convertLitter_dom hσS hσT hr hS hU]
  exact hS.transConstrains_mem _ _
    (Reduced.mkLitter _)
    (Relation.TransGen.single (Constrains.atom _ _))
    ((convertAtom_dom hσS hσT hr hS hU A a).mp ha)

theorem get_fst_eq_fst_get {A : ExtendedIndex β} {a : Atom} (ha : (convertAtom T A a).Dom) :
    (Part.get (convertAtom T A a) ha).fst =
    (Part.get (convertLitter T A a.fst)
      (convertLitter_dom_of_convertAtom_dom hσS hσT hr hS hU ha)).fst := by
  have haS := hσS.atom_spec A a a.1.toNearLitter
    ((convertAtom_dom hσS hσT hr hS hU A a).mp ha)
    (hS.fst_toNearLitter_mem ((convertAtom_dom hσS hσT hr hS hU A a).mp ha)) rfl
  have haT := hσT.atom_spec A ((convertAtom T A a).get ha)
    ((convertAtom T A a).get ha).1.toNearLitter
    (convertAtom_mem ha) (hU.fst_toNearLitter_mem_equiv hr.equiv (convertAtom_mem ha)) rfl
  simp_rw [hS.cpos_get_eq] at haS
  simp_rw [convertAtom_get ha] at haT
  rw [haS] at haT
  have := congr_arg Prod.fst (SpecCondition.atom_injective haT)
  have ha' : (convertLitter T A a.1).Dom
  · rw [convertLitter_dom hσS hσT hr hS hU]
    exact hS.transConstrains_mem _ _
      (Reduced.mkLitter _)
      (Relation.TransGen.single (Constrains.atom _ _))
      ((convertAtom_dom hσS hσT hr hS hU A a).mp ha)
  rw [← convertLitter_get ha'] at this
  have := T.injective _ _ _ _ (by rfl) this
  simp only [SupportCondition.mk.injEq, inr.injEq, true_and] at this
  exact (congr_arg Sigma.fst this).symm

theorem get_mem_get (A : ExtendedIndex β) (a : Atom) (ha : (convertAtom T A a).Dom)
    (L : Litter) (hL : (convertLitter T A L).Dom) :
    a.1 = L ↔ (convertAtom T A a).get ha ∈ (convertLitter T A L).get hL := by
  obtain hL' := (convertLitter_isLitter hr hU hL).eq_fst_toNearLitter
  rw [hL', mem_toNearLitter, get_fst_eq_fst_get hσS hσT hr hS hU ha]
  constructor
  · rintro rfl
    rfl
  · intro h
    exact convertLitter_injective' hr hU A _ _
      (convertLitter_dom_of_convertAtom_dom hσS hσT hr hS hU ha) hL
      (NearLitter.inter_nonempty_of_fst_eq_fst h)

theorem convert_lawful : StructAction.Lawful (convert hσS hσT hr hS hU) :=
  fun A => {
    atomMap_injective := convertAtom_injective A
    litterMap_injective := convertLitter_injective' hr hU A
    atom_mem := get_mem_get hσS hσT hr hS hU A
  }

theorem convert_mapFlexible : StructAction.MapFlexible (convert hσS hσT hr hS hU) := by
  intro A L hL₁ hL₂
  have hL₃ := hL₁
  rw [convert_litterMap, convertLitter_dom hσS hσT hr hS hU] at hL₃
  have hLS := hσS.flexible_spec A L.toNearLitter hL₃ hL₂
  simp_rw [hS.cpos_get_eq] at hLS
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A ((convertLitter T A L).get hL₁).1
  · exact hL
  · exfalso
    obtain ⟨_, hLT⟩ := hσT.inflexibleBot_spec A _ (convertLitter_mem hL₁) hL
    simp_rw [convertLitter_get] at hLT
    rw [hLS] at hLT
    cases hLT
  · exfalso
    obtain ⟨χ, _, _, hLT⟩ := hσT.inflexibleCoe_spec A _ (convertLitter_mem hL₁) hL
    simp_rw [convertLitter_get] at hLT
    rw [hLS] at hLT
    cases hLT

theorem deconvert_mapFlexible (A : ExtendedIndex β) (N : NearLitter)
    (hL₁ : (deconvertLitter T A N).Dom) (hL₂ : Flexible α A N.1) :
    Flexible α A ((deconvertLitter T A N).get hL₁) := by
  have hL₃ := hL₁
  rw [deconvertLitter_dom hσS hσT hr hS hU] at hL₃
  have hLS := hσT.flexible_spec A N hL₃ hL₂
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A ((deconvertLitter T A N).get hL₁)
  · exact hL
  · exfalso
    obtain ⟨_, hLT⟩ := hσS.inflexibleBot_spec A _
      (deconvertLitter_mem' hσS hσT hr hS hU hL₁) hL
    simp_rw [get_deconvertLitter hL₁] at hLS
    simp_rw [hS.cpos_get_eq] at hLT
    rw [hLS] at hLT
    cases hLT
  · exfalso
    obtain ⟨χ, _, _, hLT⟩ := hσS.inflexibleCoe_spec A _
      (deconvertLitter_mem' hσS hσT hr hS hU hL₁) hL
    simp_rw [get_deconvertLitter hL₁] at hLS
    simp_rw [hS.cpos_get_eq] at hLT
    rw [hLS] at hLT
    cases hLT

noncomputable def convertAllowable : Allowable β :=
  (StructApprox.freedom_of_action β
    (StructAction.rc (convert hσS hσT hr hS hU) (convert_lawful hσS hσT hr hS hU))
    (StructAction.rc_free _ _ (convert_mapFlexible hσS hσT hr hS hU))).choose

theorem convertAllowable_spec :
    (StructAction.rc (convert hσS hσT hr hS hU)
      (convert_lawful hσS hσT hr hS hU)).ExactlyApproximates
    (Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU)) :=
  (StructApprox.freedom_of_action β
    (StructAction.rc (convert hσS hσT hr hS hU) (convert_lawful hσS hσT hr hS hU))
    (StructAction.rc_free _ _ (convert_mapFlexible hσS hσT hr hS hU))).choose_spec

theorem convertLitter_dom_of_cond_dom (A : ExtendedIndex β) (L : Litter)
    (h : (cond σ (inr L.toNearLitter, A)).Dom) :
    (convertLitter T A L).Dom := by
  rw [convertLitter_dom hσS hσT hr hS hU]
  obtain ⟨⟨B, x⟩, hc₁, hc₂⟩ := hσS.exists_mem_of_dom (inr L.toNearLitter, A) h
  rw [hS.cpos_get_eq] at hc₂
  cases hc₂
  exact hc₁

/-- If `LawfulIn s` holds, `convertAllowable` acts on support conditions assigned at a time in `s`
exactly as specified by (`de`)`convertAtom` and (`de`)`convertLitter`.
We do not use strongness to unfold invocations of `S.cpos` here for symmetry. -/
structure LawfulIn (s : Set (Atom ⊕ NearLitter)) : Prop where
  smul_atom_eq : ∀ A : ExtendedIndex β, ∀ a : Atom,
    ∀ hc : ⟨A, inl a⟩ ∈ S, (S.cpos _).get hc ∈ s →
    Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A • a =
    (convertAtom T A a).get ((convertAtom_dom hσS hσT hr hS hU A a).mpr hc)
  smul_litter_eq : ∀ A : ExtendedIndex β, ∀ L : Litter,
    ∀ hc : ⟨A, inr L.toNearLitter⟩ ∈ S, (S.cpos _).get hc ∈ s →
    Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A • L.toNearLitter =
    (convertLitter T A L).get ((convertLitter_dom hσS hσT hr hS hU A L).mpr hc)
  inv_smul_atom_eq : ∀ A : ExtendedIndex β, ∀ a : Atom,
    ∀ hc : ⟨A, inl a⟩ ∈ T, (T.cpos _).get hc ∈ s →
    (Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A)⁻¹ • a =
    (deconvertAtom T A a).get ((deconvertAtom_dom hσS hσT hr hS hU A a).mpr hc)
  inv_smul_litter_eq : ∀ A : ExtendedIndex β, ∀ N : NearLitter,
    ∀ hc : ⟨A, inr N⟩ ∈ T, (T.cpos _).get hc ∈ s →
    (Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A)⁻¹ • N =
    Litter.toNearLitter ((deconvertLitter T A N).get
      ((deconvertLitter_dom hσS hσT hr hS hU A N).mpr hc))

theorem LawfulIn.smul_mem {s : Set (Atom ⊕ NearLitter)} (h : LawfulIn hσS hσT hr hS hU s)
    {c : SupportCondition β} (hcS : c ∈ S) (hc : (S.cpos _).get hcS ∈ s) :
    convertAllowable hσS hσT hr hS hU • c ∈ T := by
  obtain ⟨A, a | N⟩ := c
  · rw [Allowable.smul_supportCondition, smul_inl, h.smul_atom_eq A a hcS hc]
    exact convertAtom_mem _
  · obtain ⟨L, rfl⟩ := (hS.isLitter_of_mem hcS).exists_litter_eq
    rw [Allowable.smul_supportCondition, smul_inr, h.smul_litter_eq A L hcS hc]
    exact convertLitter_mem _

theorem LawfulIn.inv_smul_mem {s : Set (Atom ⊕ NearLitter)} (h : LawfulIn hσS hσT hr hS hU s)
    {c : SupportCondition β} (hcT : c ∈ T) (hc : (T.cpos _).get hcT ∈ s) :
    (convertAllowable hσS hσT hr hS hU)⁻¹ • c ∈ S := by
  obtain ⟨A, a | N⟩ := c
  · rw [Allowable.smul_supportCondition, smul_inl, map_inv, Tree.inv_apply,
      h.inv_smul_atom_eq A a hcT hc]
    exact deconvertAtom_mem' hσS hσT hr hS hU _
  · obtain ⟨L, rfl⟩ := (hU.isLitter_of_mem_equiv hr.equiv hcT).exists_litter_eq
    rw [Allowable.smul_supportCondition, smul_inr, map_inv, Tree.inv_apply,
      h.inv_smul_litter_eq A _ hcT hc]
    exact deconvertLitter_mem' hσS hσT hr hS hU _

theorem LawfulIn.cpos_get_left {s : Set (Atom ⊕ NearLitter)} (ih : LawfulIn hσS hσT hr hS hU s)
    {c : SupportCondition β} (hcS : c ∈ S) (hc : (S.cpos _).get hcS ∈ s) :
    (T.cpos (convertAllowable hσS hσT hr hS hU • c)).get (ih.smul_mem hcS hc) = c.value := by
  obtain ⟨A, a | N⟩ := c
  · have := ih.smul_atom_eq A a hcS hc
    simp_rw [Allowable.smul_supportCondition, smul_inl, this]
    rw [convertAtom_get]
  · obtain ⟨L, rfl⟩ := (hS.isLitter_of_mem hcS).exists_litter_eq
    have := ih.smul_litter_eq A L hcS hc
    simp_rw [Allowable.smul_supportCondition, smul_inr, this]
    rw [convertLitter_get]

theorem LawfulIn.cpos_get_right {s : Set (Atom ⊕ NearLitter)} (ih : LawfulIn hσS hσT hr hS hU s)
    {c : SupportCondition β} (hcT : c ∈ T) (hc : (T.cpos _).get hcT ∈ s) :
    (T.cpos c).get hcT = ((convertAllowable hσS hσT hr hS hU)⁻¹ • c).value := by
  obtain ⟨A, a | N⟩ := c
  · have := ih.inv_smul_atom_eq A a hcT hc
    simp_rw [Allowable.smul_supportCondition, smul_inl, map_inv, Tree.inv_apply, this]
    rw [get_deconvertAtom]
  · have := ih.inv_smul_litter_eq A N hcT hc
    simp_rw [Allowable.smul_supportCondition, smul_inr, map_inv, Tree.inv_apply, this]
    rw [get_deconvertLitter]

abbrev LawfulBefore (i : Atom ⊕ NearLitter) : Prop :=
  LawfulIn hσS hσT hr hS hU {j | j < i}

theorem lawfulIn_iff (s : Set (Atom ⊕ NearLitter)) :
    LawfulIn hσS hσT hr hS hU s ↔ ∀ i ∈ s, LawfulIn hσS hσT hr hS hU {i} := by
  constructor
  · intro h i hi
    constructor
    case smul_atom_eq =>
      rintro A a hc rfl
      exact h.smul_atom_eq A a hc hi
    case smul_litter_eq =>
      rintro A L hc rfl
      exact h.smul_litter_eq A L hc hi
    case inv_smul_atom_eq =>
      rintro A a hc rfl
      exact h.inv_smul_atom_eq A a hc hi
    case inv_smul_litter_eq =>
      rintro A L hc rfl
      exact h.inv_smul_litter_eq A L hc hi
  · intro h
    constructor
    case smul_atom_eq =>
      intro A a hc hcd
      refine (h _ hcd).smul_atom_eq A a hc rfl
    case smul_litter_eq =>
      rintro A L hc hcd
      exact (h _ hcd).smul_litter_eq A L hc rfl
    case inv_smul_atom_eq =>
      intro A a hc hcd
      exact (h _ hcd).inv_smul_atom_eq A a hc rfl
    case inv_smul_litter_eq =>
      rintro A L hc hcd
      exact (h _ hcd).inv_smul_litter_eq A L hc rfl

theorem lawfulBefore_induction
    (h : ∀ i, LawfulBefore hσS hσT hr hS hU i → LawfulIn hσS hσT hr hS hU {i}) :
    LawfulIn hσS hσT hr hS hU univ := by
  rw [lawfulIn_iff]
  simp only [mem_univ, forall_true_left]
  intro i
  refine (inferInstanceAs (IsWellFounded (Atom ⊕ NearLitter) (· < ·))).wf.induction
    (C := fun i => LawfulIn hσS hσT hr hS hU {i}) i ?_
  intro i ih
  refine h i ?_
  rw [LawfulBefore, lawfulIn_iff]
  exact ih

theorem mem_before_smul_iff_mem_before (A : ExtendedIndex β) (i : Atom ⊕ NearLitter)
    (P : InflexibleCoePath A) (ih : LawfulBefore hσS hσT hr hS hU i)
    (c : SupportCondition P.δ) :
    c ∈ (S.before i).comp P.δ (P.B.cons (coe_lt P.hδ)) ↔
    Tree.comp (P.B.cons (coe_lt P.hδ))
        (Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU)) • c ∈
      ((T.before i).comp P.δ (P.B.cons (coe_lt P.hδ))) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨ih.smul_mem h₁ h₂, ?_⟩
    change (T.cpos (convertAllowable hσS hσT hr hS hU •
      ⟨(P.B.cons (coe_lt P.hδ)).comp c.path, c.value⟩)).get _ < _
    rw [ih.cpos_get_left h₁ h₂]
    rw [hS.cpos_get_eq] at h₂
    exact h₂
  · rintro ⟨h₁, h₂⟩
    change (convertAllowable hσS hσT hr hS hU •
      ⟨(P.B.cons (coe_lt P.hδ)).comp c.path, c.value⟩) ∈ T at h₁
    change (T.cpos (convertAllowable hσS hσT hr hS hU •
      ⟨(P.B.cons (coe_lt P.hδ)).comp c.path, c.value⟩)).get _ < _ at h₂
    refine ⟨?_, ?_⟩
    · have := ih.inv_smul_mem h₁ h₂
      rw [inv_smul_smul] at this
      exact this
    · rw [hS.cpos_get_eq]
      rw [ih.cpos_get_right h₁ h₂, inv_smul_smul] at h₂
      exact h₂

theorem before_smul_eq_before (A : ExtendedIndex β) (i : Atom ⊕ NearLitter)
    (P : InflexibleCoePath A) (ih : LawfulBefore hσS hσT hr hS hU i) :
    (S.before i).comp P.δ (P.B.cons (coe_lt P.hδ)) =
    (show Allowable (P.δ : Iic α) from
      (Allowable.comp (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from
          P.B.cons (coe_lt P.hδ)))
        (convertAllowable hσS hσT hr hS hU))⁻¹ •
    ((T.before i).comp P.δ (P.B.cons (coe_lt P.hδ))) := by
  dsimp only
  refine OrdSupport.ext ?_ ?_
  · intro c
    rw [mem_before_smul_iff_mem_before hσS hσT hr hS hU A i P ih c,
      OrdSupport.smul_mem, inv_inv, Allowable.smul_supportCondition,
      Allowable.toStructPerm_comp (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from
        P.B.cons (coe_lt P.hδ))]
    rfl
  · intro c hcS hcT
    simp only [OrdSupport.smul_cpos, inv_inv]
    obtain ⟨B, a | N⟩ := c
    · have ih := ih.smul_atom_eq ((P.B.cons (coe_lt P.hδ)).comp B) a hcS.1 hcS.2
      simp_rw [Allowable.smul_supportCondition]
      simp only [smul_inl]
      have := Allowable.toStructPerm_comp
        (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from P.B.cons (coe_lt P.hδ))
        (convertAllowable hσS hσT hr hS hU)
      dsimp only at this
      simp_rw [this, Tree.comp_apply, ih]
      simp only [OrdSupport.comp_get, OrdSupport.before_get]
      rw [hS.cpos_get_eq, convertAtom_get]
    · have hN : N.IsLitter := hS.isLitter_of_mem hcS.1
      have ih := ih.smul_litter_eq ((P.B.cons (coe_lt P.hδ)).comp B) N.1 ?_ ?_
      swap
      · rw [← hN.eq_fst_toNearLitter]
        exact hcS.1
      swap
      · have := hcS.2
        simp_rw [← hN.eq_fst_toNearLitter]
        exact this
      simp_rw [← hN.eq_fst_toNearLitter] at ih
      dsimp only at ih
      simp_rw [Allowable.smul_supportCondition]
      simp only [smul_inr]
      have := Allowable.toStructPerm_comp
        (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from P.B.cons (coe_lt P.hδ))
        (convertAllowable hσS hσT hr hS hU)
      dsimp only at this
      simp_rw [this, Tree.comp_apply, ih]
      simp only [OrdSupport.comp_get, OrdSupport.before_get]
      rw [hS.cpos_get_eq, convertLitter_get, ← hN.eq_fst_toNearLitter]

theorem spec_inflexibleBot (A : ExtendedIndex β) (L : Litter) (hL : InflexibleBot A L)
    (hLS₁ : (cond σ (inr L.toNearLitter, A)).Dom)
    (hLS₂ : (cond σ (inr L.toNearLitter, A)).get hLS₁ =
      SpecCondition.inflexibleBot A hL.path (inl hL.a, hL.path.B.cons (bot_lt_coe _))) :
    ∃ hL' : InflexibleBot A ((convertLitter T A L).get
      (convertLitter_dom_of_cond_dom hσS hσT hr hS hU A L hLS₁)).1,
    ∃ ha : (T.cpos ⟨hL'.path.B.cons (bot_lt_coe _), inl hL'.a⟩).Dom,
      hL.path = hL'.path ∧
      inl hL.a = (T.cpos ⟨hL'.path.B.cons (bot_lt_coe _), inl hL'.a⟩).get ha := by
  have hLd : (convertLitter T A L).Dom := convertLitter_dom_of_cond_dom hσS hσT hr hS hU A L hLS₁
  obtain (hL' | ⟨⟨hL'⟩⟩ | ⟨⟨hL'⟩⟩) := flexible_cases' β A ((convertLitter T A L).get hLd).1
  · have := hσT.flexible_spec A ((convertLitter T A L).get hLd) (convertLitter_mem hLd) hL'
    simp_rw [convertLitter_get] at this
    rw [hLS₂] at this
    cases this
  · obtain ⟨_, this⟩ := hσT.inflexibleBot_spec A
      ((convertLitter T A L).get hLd) (convertLitter_mem hLd) hL'
    simp_rw [convertLitter_get] at this
    rw [hLS₂] at this
    refine ⟨hL', ?_⟩
    have := SpecCondition.inflexibleBot_injective this
    rw [Prod.ext_iff] at this
    exact ⟨_, this.1, this.2.1⟩
  · obtain ⟨_, _, _, this⟩ := hσT.inflexibleCoe_spec A
      ((convertLitter T A L).get hLd) (convertLitter_mem hLd) hL'
    simp_rw [convertLitter_get] at this
    rw [hLS₂] at this
    cases this

theorem spec_inflexibleBot_inv (A : ExtendedIndex β) (L : Litter)
    (hL₁ : InflexibleBot A L) (hL₂ : ⟨A, inr L.toNearLitter⟩ ∈ T)
    (ha : ⟨hL₁.path.B.cons (bot_lt_coe _), inl hL₁.a⟩ ∈ T)
    (hLT₁ : (cond σ ((T.cpos ⟨A, inr L.toNearLitter⟩).get hL₂, A)).Dom)
    (hLT₂ : (cond σ ((T.cpos ⟨A, inr L.toNearLitter⟩).get hL₂, A)).get hLT₁ =
      SpecCondition.inflexibleBot A hL₁.path
        ((T.cpos _).get ha, hL₁.path.B.cons (bot_lt_coe _))) :
    ∃ hL' : InflexibleBot A ((deconvertLitter T A L.toNearLitter).get
      ((deconvertLitter_dom hσS hσT hr hS hU A _).mpr hL₂)),
    hL₁.path = hL'.path ∧
    (T.cpos ⟨hL₁.path.B.cons (bot_lt_coe _), inl hL₁.a⟩).get ha = inl hL'.a := by
  have hLd : (deconvertLitter T A L.toNearLitter).Dom :=
    (deconvertLitter_dom hσS hσT hr hS hU A _).mpr hL₂
  obtain (hL' | ⟨⟨hL'⟩⟩ | ⟨⟨hL'⟩⟩) := flexible_cases' β A ((deconvertLitter T A _).get hLd)
  · have := hσS.flexible_spec A ((deconvertLitter T A _).get hLd).toNearLitter
      (deconvertLitter_mem' hσS hσT hr hS hU hLd) hL'
    simp_rw [← get_deconvertLitter hLd, hS.cpos_get_eq] at this
    rw [hLT₂] at this
    cases this
  · obtain ⟨_, this⟩ := hσS.inflexibleBot_spec A ((deconvertLitter T A _).get hLd).toNearLitter
      (deconvertLitter_mem' hσS hσT hr hS hU hLd) hL'
    simp_rw [← get_deconvertLitter hLd, hS.cpos_get_eq] at this
    rw [hLT₂] at this
    refine ⟨hL', ?_⟩
    have := SpecCondition.inflexibleBot_injective this
    rw [Prod.ext_iff] at this
    exact ⟨this.1, this.2.1⟩
  · obtain ⟨_, _, _, this⟩ := hσS.inflexibleCoe_spec A ((deconvertLitter T A _).get hLd).toNearLitter
      (deconvertLitter_mem' hσS hσT hr hS hU hLd) hL'
    simp_rw [← get_deconvertLitter hLd, hS.cpos_get_eq] at this
    rw [hLT₂] at this
    cases this

theorem spec_inflexibleCoe (A : ExtendedIndex β) (L : Litter) (hL : InflexibleCoe A L)
    (χ : CodingFunction hL.path.δ)
    (hLS₁ : (cond σ (inr L.toNearLitter, A)).Dom)
    (hLS₂ : (cond σ (inr L.toNearLitter, A)).get hLS₁ =
      SpecCondition.inflexibleCoe A hL.path χ) :
    ∃ hL' : InflexibleCoe A ((convertLitter T A L).get
      (convertLitter_dom_of_cond_dom hσS hσT hr hS hU A L hLS₁)).1,
    ∃ hχT : (T.before (inr L.toNearLitter)).comp hL.path.δ (hL.path.B.cons hL.path.hδ) ∈ χ,
    hL.path = hL'.path ∧ HEq ((χ.decode _).get hχT) hL'.t := by
  have hLd : (convertLitter T A L).Dom := convertLitter_dom_of_cond_dom hσS hσT hr hS hU A L hLS₁
  obtain (hL' | ⟨⟨hL'⟩⟩ | ⟨⟨hL'⟩⟩) := flexible_cases' β A ((convertLitter T A L).get hLd).1
  · have := hσT.flexible_spec A ((convertLitter T A L).get hLd) (convertLitter_mem hLd) hL'
    simp_rw [convertLitter_get] at this
    rw [hLS₂] at this
    cases this
  · obtain ⟨_, this⟩ := hσT.inflexibleBot_spec A
      ((convertLitter T A L).get hLd) (convertLitter_mem hLd) hL'
    simp_rw [convertLitter_get] at this
    rw [hLS₂] at this
    cases this
  · obtain ⟨χ, hχ₁, hχ₂, this⟩ := hσT.inflexibleCoe_spec A
      ((convertLitter T A L).get hLd) (convertLitter_mem hLd) hL'
    simp_rw [convertLitter_get] at this
    rw [hLS₂] at this
    refine ⟨hL', ?_⟩
    obtain ⟨P, t, hL⟩ := hL
    obtain ⟨P', t', hL'⟩ := hL'
    cases SpecCondition.inflexibleCoe_injective₁ this
    cases SpecCondition.inflexibleCoe_injective₂ this
    refine ⟨?_, rfl, ?_⟩
    · rw [convertLitter_get] at hχ₁
      exact hχ₁
    · simp_rw [convertLitter_get] at hχ₂
      exact heq_of_eq hχ₂

theorem spec_inflexibleCoe_inv (A : ExtendedIndex β) (L : Litter)
    (hL₁ : InflexibleCoe A L) (hL₂ : ⟨A, inr L.toNearLitter⟩ ∈ T)
    (χ : CodingFunction hL₁.path.δ)
    (hLT₁ : (cond σ ((T.cpos ⟨A, inr L.toNearLitter⟩).get hL₂, A)).Dom)
    (hLT₂ : (cond σ ((T.cpos ⟨A, inr L.toNearLitter⟩).get hL₂, A)).get hLT₁ =
      SpecCondition.inflexibleCoe A hL₁.path χ) :
    ∃ hL' : InflexibleCoe A ((deconvertLitter T A L.toNearLitter).get
      ((deconvertLitter_dom hσS hσT hr hS hU A _).mpr hL₂)),
    ∃ hχT : (S.before ((T.cpos ⟨A, inr L.toNearLitter⟩).get hL₂)).comp
      hL₁.path.δ (hL₁.path.B.cons hL₁.path.hδ) ∈ χ,
    hL₁.path = hL'.path ∧ HEq ((χ.decode _).get hχT) hL'.t := by
  have hLd : (deconvertLitter T A L.toNearLitter).Dom :=
    (deconvertLitter_dom hσS hσT hr hS hU A _).mpr hL₂
  obtain (hL' | ⟨⟨hL'⟩⟩ | ⟨⟨hL'⟩⟩) := flexible_cases' β A ((deconvertLitter T A _).get hLd)
  · have := hσS.flexible_spec A ((deconvertLitter T A _).get hLd).toNearLitter
      (deconvertLitter_mem' hσS hσT hr hS hU hLd) hL'
    simp_rw [← get_deconvertLitter hLd, hS.cpos_get_eq] at this
    rw [hLT₂] at this
    cases this
  · obtain ⟨_, this⟩ := hσS.inflexibleBot_spec A
      ((deconvertLitter T A _).get hLd).toNearLitter (deconvertLitter_mem' hσS hσT hr hS hU hLd) hL'
    simp_rw [← get_deconvertLitter hLd, hS.cpos_get_eq] at this
    rw [hLT₂] at this
    cases this
  · obtain ⟨χ, hχ₁, hχ₂, this⟩ := hσS.inflexibleCoe_spec A
      ((deconvertLitter T A _).get hLd).toNearLitter (deconvertLitter_mem' hσS hσT hr hS hU hLd) hL'
    simp_rw [← get_deconvertLitter hLd, hS.cpos_get_eq] at this
    rw [hLT₂] at this
    refine ⟨hL', ?_⟩
    obtain ⟨P, t, hL⟩ := hL₁
    obtain ⟨P', t', hL'⟩ := hL'
    cases SpecCondition.inflexibleCoe_injective₁ this
    cases SpecCondition.inflexibleCoe_injective₂ this
    refine ⟨?_, rfl, ?_⟩
    · rw [get_deconvertLitter hLd]
      rw [hS.cpos_get_eq] at hχ₁
      exact hχ₁
    · simp_rw [get_deconvertLitter hLd]
      simp_rw [hS.cpos_get_eq] at hχ₂
      exact heq_of_eq hχ₂

theorem convert_inflexibleBot (A : ExtendedIndex β) (L : Litter) (hL : InflexibleBot A L)
    (hLd : (convertLitter T ((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _))
      (fuzz (show ((⊥ : IioBot α) : TypeIndex) ≠ (hL.path.ε : Λ) from bot_ne_coe) hL.a)).Dom)
    (had : (convertAtom T (hL.path.B.cons (bot_lt_coe _)) hL.a).Dom) :
    fuzz (show ((⊥ : IioBot α) : TypeIndex) ≠ (hL.path.ε : Λ) from bot_ne_coe)
      ((convertAtom T (hL.path.B.cons (bot_lt_coe _)) hL.a).get had) =
    ((convertLitter T ((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _))
        (fuzz (show ((⊥ : IioBot α) : TypeIndex) ≠ (hL.path.ε : Λ) from bot_ne_coe) hL.a)).get
      hLd).fst := by
  have := hσS.inflexibleBot_spec A L.toNearLitter ?_ hL
  swap
  · rw [convertLitter_dom hσS hσT hr hS hU] at hLd
    simp_rw [hL.hL, hL.path.hA]
    exact hLd
  obtain ⟨h₁, h₂⟩ := this
  simp_rw [hS.cpos_get_eq] at h₂
  obtain ⟨hL', ha', h₁', h₂'⟩ := spec_inflexibleBot hσS hσT hr hS hU A L hL _ h₂
  obtain ⟨P, a, hL⟩ := hL
  obtain ⟨P', a', hL'⟩ := hL'
  dsimp only at *
  subst h₁'
  have := hL'
  simp_rw [P.hA, hL] at this
  rw [this, convertAtom_eq_of_eq_cpos had h₂']

theorem deconvert_inflexibleBot (A : ExtendedIndex β) (L : Litter) (hL : InflexibleBot A L)
    (hLd : (deconvertLitter T ((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _))
      (fuzz (show ((⊥ : IioBot α) : TypeIndex) ≠ (hL.path.ε : Λ) from bot_ne_coe) hL.a).toNearLitter).Dom)
    (had : (deconvertAtom T (hL.path.B.cons (bot_lt_coe _)) hL.a).Dom) :
    fuzz (show ((⊥ : IioBot α) : TypeIndex) ≠ (hL.path.ε : Λ) from bot_ne_coe)
      ((deconvertAtom T (hL.path.B.cons (bot_lt_coe _)) hL.a).get had) =
    (deconvertLitter T _ _).get hLd := by
  have hLd' : ⟨A, inr L.toNearLitter⟩ ∈ T
  · rw [deconvertLitter_dom hσS hσT hr hS hU] at hLd
    simp_rw [hL.hL, hL.path.hA]
    exact hLd
  have := hσT.inflexibleBot_spec A L.toNearLitter hLd' hL
  obtain ⟨h₁, h₂⟩ := this
  have := spec_inflexibleBot_inv hσS hσT hr hS hU A L hL hLd' h₁ (hσT.cpos_dom _ _) h₂
  obtain ⟨hL', h₁', h₂'⟩ := this
  obtain ⟨P, a, hL⟩ := hL
  obtain ⟨P', a', hL'⟩ := hL'
  dsimp only at *
  subst h₁'
  have := hL'
  simp_rw [P.hA, hL] at this
  rw [get_deconvertAtom had, inl_injective.eq_iff] at h₂'
  rw [this, h₂']

theorem convert_inflexibleCoe (A : ExtendedIndex β) (L : Litter) (hL : InflexibleCoe A L)
    (hLd : ⟨((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _)),
      inr (fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε) hL.t).toNearLitter⟩ ∈ S)
    (ih : LawfulBefore hσS hσT hr hS hU (inr L.toNearLitter)) :
    fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε)
      (Allowable.comp
        (show Path ((β : IicBot α) : TypeIndex) (hL.path.δ : IicBot α) from
          hL.path.B.cons (coe_lt hL.path.hδ))
        (convertAllowable hσS hσT hr hS hU) • hL.t) =
    ((convertLitter T ((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _))
      (fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε) hL.t)).get
      ((convertLitter_dom hσS hσT hr hS hU _ _).mpr hLd)).fst := by
  have := hσS.inflexibleCoe_spec A L.toNearLitter ?_ hL
  swap
  · simp_rw [hL.hL, hL.path.hA]
    exact hLd
  obtain ⟨χ, hχ₁, hχ₂, h⟩ := this
  simp_rw [hS.cpos_get_eq] at h
  have := spec_inflexibleCoe hσS hσT hr hS hU A L hL χ ?_ h
  swap
  · simp_rw [hL.hL, hL.path.hA]
    have := hσS.cpos_dom _ hLd
    rw [hS.cpos_get_eq] at this
    exact this
  obtain ⟨hL', hχT, h₁, h₂⟩ := this
  obtain ⟨P, t, hL⟩ := hL
  obtain ⟨P', t', hL'⟩ := hL'
  subst h₁
  cases eq_of_heq h₂
  clear h₂
  dsimp only at *
  simp_rw [hL, P.hA] at hL'
  rw [hL']
  refine congr_arg _ ?_
  have := CodingFunction.decode_smul' _ _
    (Allowable.comp
      (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from
        P.B.cons (coe_lt P.hδ))
      (convertAllowable hσS hσT hr hS hU)⁻¹) hχT (CodingFunction.smul_mem _ hχT)
  rw [← inv_smul_eq_iff] at this
  refine Eq.trans ?_ this
  clear this
  simp only [map_inv, inv_inv, smul_left_cancel_iff]
  refine Eq.trans hχ₂.symm (CodingFunction.decode_congr ?_)
  simp_rw [hS.cpos_get_eq]
  exact before_smul_eq_before hσS hσT hr hS hU A _ P ih

theorem deconvert_inflexibleCoe (A : ExtendedIndex β) (L : Litter) (hL : InflexibleCoe A L)
    (hLd : ⟨((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _)),
      inr (fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε) hL.t).toNearLitter⟩ ∈ T)
    (ih : LawfulBefore hσS hσT hr hS hU ((T.cpos _).get hLd)) :
    fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε)
      (Allowable.comp
        (show Path ((β : IicBot α) : TypeIndex) (hL.path.δ : IicBot α) from
          hL.path.B.cons (coe_lt hL.path.hδ))
        (convertAllowable hσS hσT hr hS hU)⁻¹ • hL.t) =
    (deconvertLitter T ((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _))
      (fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε) hL.t).toNearLitter).get
      ((deconvertLitter_dom hσS hσT hr hS hU _ _).mpr hLd) := by
  have := hσT.inflexibleCoe_spec A L.toNearLitter ?_ hL
  swap
  · simp_rw [hL.hL, hL.path.hA]
    exact hLd
  obtain ⟨χ, hχ₁, hχ₂, h⟩ := this
  have := spec_inflexibleCoe_inv hσS hσT hr hS hU A L hL _ χ ?_ h
  swap
  · simp_rw [hL.hL, hL.path.hA]
    exact hσT.cpos_dom _ hLd
  obtain ⟨hL', hχT, h₁, h₂⟩ := this
  obtain ⟨P, t, hL⟩ := hL
  obtain ⟨P', t', hL'⟩ := hL'
  subst h₁
  cases eq_of_heq h₂
  clear h₂
  dsimp only at *
  simp_rw [hL, P.hA] at hL'
  rw [hL']
  refine congr_arg _ ?_
  have := CodingFunction.decode_smul' _ _
    (Allowable.comp
      (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from
        P.B.cons (coe_lt P.hδ))
      (convertAllowable hσS hσT hr hS hU)) hχT (CodingFunction.smul_mem _ hχT)
  rw [← inv_smul_eq_iff] at this
  refine Eq.trans ?_ this
  clear this
  simp only [map_inv, inv_inv, smul_left_cancel_iff]
  refine Eq.trans hχ₂.symm (CodingFunction.decode_congr ?_)
  have := before_smul_eq_before hσS hσT hr hS hU A _ P ih
  rw [eq_inv_smul_iff] at this
  simp_rw [hL, P.hA] at this ⊢
  exact this.symm

theorem smul_atom_eq (A : ExtendedIndex β) (a : Atom) (hc : ⟨A, inl a⟩ ∈ S) :
    Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A • a =
    (convertAtom T A a).get ((convertAtom_dom hσS hσT hr hS hU A a).mpr hc) := by
  rw [← (convertAllowable_spec hσS hσT hr hS hU A).map_atom a, StructAction.rc_smul_atom_eq]
  rfl
  exact Or.inl (Or.inl (Or.inl (Or.inl ((convertAtom_dom hσS hσT hr hS hU A a).mpr hc))))

theorem inv_smul_atom_eq (A : ExtendedIndex β) (a : Atom) (hc : ⟨A, inl a⟩ ∈ T) :
    (Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A)⁻¹ • a =
    (deconvertAtom T A a).get ((deconvertAtom_dom hσS hσT hr hS hU A a).mpr hc) := by
  rw [inv_smul_eq_iff, smul_atom_eq hσS hσT hr hS hU A, deconvertAtom_convertAtom]
  exact deconvertAtom_mem' hσS hσT hr hS hU _

theorem smul_litter_eq_of_lawfulBefore' (A : ExtendedIndex β) (L : Litter)
    (hc : ⟨A, inr L.toNearLitter⟩ ∈ S) (ih : LawfulBefore hσS hσT hr hS hU (inr L.toNearLitter)) :
    Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A • L =
    ((convertLitter T A L).get ((convertLitter_dom hσS hσT hr hS hU A L).mpr hc)).1 := by
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A L
  · rw [← (convertAllowable_spec hσS hσT hr hS hU A).map_litter L,
      StructAction.rc_smul_litter_eq,
      NearLitterAction.flexibleLitterLocalPerm_apply_eq,
      NearLitterAction.roughLitterMapOrElse_of_dom]
    rfl
    · exact (convertLitter_dom hσS hσT hr hS hU A L).mpr hc
    · exact hL
    · exact Or.inl (Or.inl ⟨(convertLitter_dom hσS hσT hr hS hU A L).mpr hc, hL⟩)
  · simp_rw [hL.hL, hL.path.hA]
    rw [toStructPerm_smul_fuzz β hL.path.γ ⊥ hL.path.ε]
    swap
    · exact bot_lt_coe _
    swap
    · intro h
      simp only [IioBot.bot_ne_mk_coe] at h
    rw [← convert_inflexibleBot hσS hσT hr hS hU A L hL ?_ ?_]
    swap
    · simp_rw [← hL.hL, ← hL.path.hA]
      exact (convertLitter_dom hσS hσT hr hS hU A L).mpr hc
    have := ih.smul_atom_eq (hL.path.B.cons (bot_lt_coe _)) hL.a ?_ ?_
    rw [← Allowable.toStructPerm_apply (β := (β : IicBot α)), NearLitterPerm.ofBot_smul] at this
    rw [this]
    · rw [convertAtom_dom hσS hσT hr hS hU]
      simp_rw [hL.hL, hL.path.hA] at hc
      exact hS.transConstrains_mem _ _ (Reduced.mkAtom _)
        (Relation.TransGen.single <| Constrains.fuzz_bot hL.path.hε hL.path.B hL.a) hc
    · simp_rw [hL.hL, hL.path.hA] at hc
      exact hS.transConstrains_mem _ _ (Reduced.mkAtom _)
        (Relation.TransGen.single <| Constrains.fuzz_bot hL.path.hε hL.path.B hL.a) hc
    · simp_rw [hL.hL]
      rw [hS.cpos_get_eq]
      exact constrains_subrelation _ _ (Constrains.fuzz_bot hL.path.hε hL.path.B hL.a)
  · simp_rw [hL.hL, hL.path.hA]
    rw [toStructPerm_smul_fuzz β hL.path.γ hL.path.δ hL.path.ε]
    swap
    · exact coe_lt_coe.mpr hL.path.hδ
    swap
    · intro h
      simp only [Subtype.mk.injEq, coe_inj] at h
      exact coe_ne' hL.path.hδε h
    simp_rw [hL.hL, hL.path.hA] at hc
    exact convert_inflexibleCoe hσS hσT hr hS hU A L hL hc ih

theorem smul_litter_eq_of_lawfulBefore (A : ExtendedIndex β) (L : Litter)
    (hc : ⟨A, inr L.toNearLitter⟩ ∈ S) (ih : LawfulBefore hσS hσT hr hS hU (inr L.toNearLitter)) :
    Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A • L.toNearLitter =
    (convertLitter T A L).get ((convertLitter_dom hσS hσT hr hS hU A L).mpr hc) :=
  StructAction.smul_toNearLitter_eq_of_precise _ StructAction.refine_precise
    (convertAllowable_spec hσS hσT hr hS hU) ((convertLitter_dom hσS hσT hr hS hU A L).mpr hc)
    (smul_litter_eq_of_lawfulBefore' hσS hσT hr hS hU A L hc ih)

theorem inv_smul_litter_eq_of_lawfulBefore' (A : ExtendedIndex β) (L : Litter)
    (hc : ⟨A, inr L.toNearLitter⟩ ∈ T)
    (ih : LawfulBefore hσS hσT hr hS hU ((T.cpos _).get hc)) :
    (Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A)⁻¹ • L =
    (deconvertLitter T A L.toNearLitter).get
      ((deconvertLitter_dom hσS hσT hr hS hU _ _).mpr hc) := by
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A L
  · rw [inv_smul_eq_iff,
      ← (convertAllowable_spec hσS hσT hr hS hU A).map_litter,
      StructAction.rc_smul_litter_eq,
      NearLitterAction.flexibleLitterLocalPerm_apply_eq,
      NearLitterAction.roughLitterMapOrElse_of_dom]
    simp only [StructAction.refine_apply, NearLitterAction.refine_litterMap, convert_litterMap]
    rw [deconvertLitter_convertLitter]
    · rfl
    · simp only [StructAction.refine_apply, NearLitterAction.refine_litterMap, convert_litterMap]
      exact deconvertLitter_convertLitter_dom _
    · simp only [StructAction.refine_apply, NearLitterAction.refine_litterMap, convert_litterMap]
      exact deconvertLitter_convertLitter_dom _
    · exact deconvert_mapFlexible hσS hσT hr hS hU A _ _ hL
    · refine Or.inl (Or.inl ⟨?_, ?_⟩)
      · simp only [StructAction.refine_apply, NearLitterAction.refine_litterMap, convert_litterMap]
        exact deconvertLitter_convertLitter_dom _
      · exact deconvert_mapFlexible hσS hσT hr hS hU A _ _ hL
  · simp_rw [hL.hL, hL.path.hA]
    rw [← Tree.inv_apply, ← map_inv]
    rw [toStructPerm_smul_fuzz β hL.path.γ ⊥ hL.path.ε]
    swap
    · exact bot_lt_coe _
    swap
    · intro h
      simp only [IioBot.bot_ne_mk_coe] at h
    rw [← deconvert_inflexibleBot hσS hσT hr hS hU A L hL ?_ ?_]
    swap
    · simp_rw [← hL.hL, ← hL.path.hA]
      exact (deconvertLitter_dom hσS hσT hr hS hU A L.toNearLitter).mpr hc
    have := ih.inv_smul_atom_eq (hL.path.B.cons (bot_lt_coe _)) hL.a ?_ ?_
    rw [← Allowable.toStructPerm_apply (β := (β : IicBot α)), inv_smul_eq_iff,
      NearLitterPerm.ofBot_smul, ← inv_smul_eq_iff, ← map_inv] at this
    rw [this]
    · rw [deconvertAtom_dom hσS hσT hr hS hU]
      simp_rw [hL.hL, hL.path.hA] at hc
      exact hU.transConstrains_mem_equiv hr.equiv _ _ (Reduced.mkAtom _)
        (Relation.TransGen.single <| Constrains.fuzz_bot hL.path.hε hL.path.B hL.a) hc
    · simp_rw [hL.hL, hL.path.hA] at hc
      exact hU.transConstrains_mem_equiv hr.equiv _ _ (Reduced.mkAtom _)
        (Relation.TransGen.single <| Constrains.fuzz_bot hL.path.hε hL.path.B hL.a) hc
    · rw [mem_setOf, ← hr.equiv.lt_iff_lt, hU.cpos_get_eq, hU.cpos_get_eq]
      · simp_rw [hL.hL]
        exact constrains_subrelation _ _ (Constrains.fuzz_bot hL.path.hε hL.path.B hL.a)
      · exact hr.equiv.mem_left hc
      · refine hU.transConstrains_mem _ _ (Reduced.mkAtom _) ?_ (hr.equiv.mem_left hc)
        simp_rw [hL.hL, hL.path.hA]
        exact Relation.TransGen.single (Constrains.fuzz_bot hL.path.hε hL.path.B hL.a)
  · simp_rw [hL.hL, hL.path.hA]
    rw [← Tree.inv_apply, ← map_inv]
    rw [toStructPerm_smul_fuzz β hL.path.γ hL.path.δ hL.path.ε]
    swap
    · exact coe_lt_coe.mpr hL.path.hδ
    swap
    · intro h
      simp only [Subtype.mk.injEq, coe_inj] at h
      exact coe_ne' hL.path.hδε h
    simp_rw [hL.hL, hL.path.hA] at hc ih
    exact deconvert_inflexibleCoe hσS hσT hr hS hU A L hL hc ih

theorem inv_smul_litter_eq_of_lawfulBefore (A : ExtendedIndex β) (L : Litter)
    (hc : ⟨A, inr L.toNearLitter⟩ ∈ T)
    (ih : LawfulBefore hσS hσT hr hS hU ((T.cpos _).get hc)) :
    (Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A)⁻¹ • L.toNearLitter =
    ((deconvertLitter T A L.toNearLitter).get
      ((deconvertLitter_dom hσS hσT hr hS hU _ _).mpr hc)).toNearLitter := by
  have := inv_smul_litter_eq_of_lawfulBefore' hσS hσT hr hS hU A L hc ih
  rw [inv_smul_eq_iff] at this ⊢
  rw [StructAction.smul_toNearLitter_eq_of_precise _ StructAction.refine_precise
    (convertAllowable_spec hσS hσT hr hS hU) ?_
    (this.symm.trans ?_)]
  · simp only [StructAction.refine_apply, NearLitterAction.refine_litterMap, convert_litterMap,
      deconvertLitter_convertLitter]
  · rw [StructAction.refine_apply, NearLitterAction.refine_litterMap, convert_litterMap]
    exact deconvertLitter_convertLitter_dom _
  · simp only [StructAction.refine_apply, NearLitterAction.refine_litterMap, convert_litterMap,
      deconvertLitter_convertLitter, Litter.toNearLitter_fst]

theorem lawfulIn_step (i : Atom ⊕ NearLitter) (ih : LawfulBefore hσS hσT hr hS hU i) :
    LawfulIn hσS hσT hr hS hU {i} := by
  constructor
  case smul_atom_eq =>
    rintro A a hc rfl
    exact smul_atom_eq hσS hσT hr hS hU A a hc
  case smul_litter_eq =>
    rintro A L hc rfl
    rw [hS.cpos_get_eq] at ih
    exact smul_litter_eq_of_lawfulBefore hσS hσT hr hS hU A L hc ih
  case inv_smul_atom_eq =>
    rintro A a hc rfl
    exact inv_smul_atom_eq hσS hσT hr hS hU A a hc
  case inv_smul_litter_eq =>
    rintro A N hc rfl
    obtain ⟨L, rfl⟩ := (hU.isLitter_of_mem_equiv hr.equiv hc).exists_litter_eq
    exact inv_smul_litter_eq_of_lawfulBefore hσS hσT hr hS hU A L hc ih

theorem lawfulIn_all : LawfulIn hσS hσT hr hS hU univ :=
  lawfulBefore_induction hσS hσT hr hS hU (lawfulIn_step hσS hσT hr hS hU)

theorem convertAllowable_smul : convertAllowable hσS hσT hr hS hU • S = T := by
  refine OrdSupport.ext ?_ ?_
  · intro c
    constructor
    · intro hc
      have := (lawfulIn_all hσS hσT hr hS hU).smul_mem hc (mem_univ _)
      rw [smul_inv_smul] at this
      exact this
    · intro hc
      exact (lawfulIn_all hσS hσT hr hS hU).inv_smul_mem hc (mem_univ _)
  · intro c hcS hcT
    obtain ⟨A, a | N⟩ := c
    · simp only [OrdSupport.smul_cpos, Allowable.smul_supportCondition,
        smul_inl]
      have := (lawfulIn_all hσS hσT hr hS hU).smul_atom_eq A _ hcS (mem_univ _)
      simp only [smul_inv_smul] at this
      rw [hS.cpos_get_eq]
      have goal := convertAtom_get ((convertAtom_dom hσS hσT hr hS hU A _).mpr hcS)
      simp_rw [← this] at goal
      simp only [map_inv, Tree.inv_apply, smul_inv_smul] at goal ⊢
      exact goal.symm
    · obtain ⟨L, rfl⟩ := (hU.isLitter_of_mem_equiv hr.equiv hcT).exists_litter_eq
      have hL := hS.isLitter_of_mem hcS
      simp only [map_inv, Tree.inv_apply] at hL
      simp only [OrdSupport.smul_cpos, Allowable.smul_supportCondition,
        smul_inr]
      have hd : ⟨A, inr (Allowable.toStructPerm
          (convertAllowable hσS hσT hr hS hU)⁻¹ A • L).toNearLitter⟩ ∈ S
      · change _ ∈ S at hcS
        simp only [Allowable.smul_supportCondition, smul_inr] at hcS
        rw [(hS.isLitter_of_mem hcS).eq_fst_toNearLitter] at hcS
        exact hcS
      have := (lawfulIn_all hσS hσT hr hS hU).smul_litter_eq A _ hd (mem_univ _)
      rw [hS.cpos_get_eq, map_inv, Tree.inv_apply, hL.eq_fst_toNearLitter,
        ← Tree.inv_apply, ← map_inv]
      simp only [NearLitterPerm.smul_nearLitter_fst, Litter.toNearLitter_fst]
      rw [← convertLitter_get ((convertLitter_dom hσS hσT hr hS hU A _).mpr hd)]
      simp_rw [← this]
      have hL' : (Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A •
        ((Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A)⁻¹ •
          L).toNearLitter).IsLitter
      · simp_rw [← Tree.inv_apply, ← map_inv, this, map_inv, Tree.inv_apply]
        rw [(convertLitter_isLitter hr hU _).eq_fst_toNearLitter]
        exact NearLitter.IsLitter.mk _
      congr
      rw [map_inv, Tree.inv_apply, hL'.eq_fst_toNearLitter]
      simp only [NearLitterPerm.smul_nearLitter_fst, Litter.toNearLitter_fst, smul_inv_smul]

end Spec

end ConNF
