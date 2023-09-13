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

theorem spec_inflexibleCoe (A : ExtendedIndex β) (L : Litter) (hL : InflexibleCoe A L)
    (χ : CodingFunction hL.path.δ)
    (hLS₁ : (cond σ (inr L.toNearLitter, A)).Dom)
    (hLS₂ : (cond σ (inr L.toNearLitter, A)).get hLS₁ =
      SpecCondition.inflexibleCoe A hL.path χ) :
    ∃ hL' : InflexibleCoe A ((convertLitter T A L).get
      (convertLitter_dom_of_cond_dom hσS hσT hr hS hU A L hLS₁)).1,
    ∃ hχT : (T.before (inr L.toNearLitter)).comp hL.path.δ (hL.path.B.cons hL.path.hδ) ∈ χ,
    hL.path = hL'.path ∧ HEq ((χ.decode _).get hχT) (hL'.t) := by
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

theorem convert_inflexibleBot (A : ExtendedIndex β) (L : Litter) (hL : InflexibleBot A L)
    (hLd : (convertLitter T ((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _))
      (fuzz (show ((⊥ : IioBot α) : TypeIndex) ≠ (hL.path.ε : Λ) from bot_ne_coe) hL.a)).Dom)
    (had : (convertAtom T (hL.path.B.cons (bot_lt_coe _)) hL.a).Dom) :
    fuzz (show ((⊥ : IioBot α) : TypeIndex) ≠ (hL.path.ε : Λ) from bot_ne_coe)
      ((convertAtom T (Path.cons hL.path.B (bot_lt_coe _)) hL.a).get had) =
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

/--
`convertAllowable` is lawful inside a set `s` if the set of support conditions assigned at times in
`s` lie in `S` if and only if they are mapped inside `T`, and such support conditions have images
given by `convertAtom` and `convertLitter`.
-/
structure LawfulIn (s : Set (Atom ⊕ NearLitter)) : Prop where
  /--
  All support conditions in `S` that are contained in `s` are mapped inside `T`.
  Note that `S` is strong so `c.value ∈ s` means `(S.cpos c).get _ ∈ s`.
  -/
  smul_mem : ∀ c : SupportCondition β, c ∈ S →
    c.value ∈ s → convertAllowable hσS hσT hr hS hU • c ∈ T
  /--
  All support conditions that were mapped inside `T`, and were defined at a time in `s`,
  came from `S`.
  -/
  of_smul_mem : ∀ c : SupportCondition β, ∀ hc : convertAllowable hσS hσT hr hS hU • c ∈ T,
    (T.cpos _).get hc ∈ s → c ∈ S
  /--
  The image of an atom in `s` under `convertAllowable` is given by `convertAtom`.
  -/
  smul_atom_eq : ∀ A : ExtendedIndex β, ∀ a : Atom,
    ∀ hc : (convertAtom T A a).Dom, inl a ∈ s →
    Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A • a =
    (convertAtom T A a).get hc
  /--
  The image of a litter in `s` under `convertAllowable` is given by `convertLitter`.
  -/
  smul_litter_eq : ∀ A : ExtendedIndex β, ∀ L : Litter,
    ∀ hc : (convertLitter T A L).Dom, inr L.toNearLitter ∈ s →
    Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A • L.toNearLitter =
    (convertLitter T A L).get hc

abbrev LawfulBefore (i : Atom ⊕ NearLitter) : Prop :=
  LawfulIn hσS hσT hr hS hU {j | j < i}

theorem lawfulIn_iff (s : Set (Atom ⊕ NearLitter)) :
    LawfulIn hσS hσT hr hS hU s ↔ ∀ i ∈ s, LawfulIn hσS hσT hr hS hU {i} := by
  constructor
  · intro h i hi
    constructor
    case smul_mem =>
      rintro c hcS rfl
      exact h.smul_mem c hcS hi
    case of_smul_mem =>
      rintro c hcT rfl
      exact h.of_smul_mem c hcT hi
    case smul_atom_eq =>
      rintro A a hc rfl
      exact h.smul_atom_eq A a hc hi
    case smul_litter_eq =>
      rintro A L hc rfl
      exact h.smul_litter_eq A L hc hi
  · intro h
    constructor
    case smul_mem =>
      rintro c hcS hcd
      exact (h c.value hcd).smul_mem c hcS rfl
    case of_smul_mem =>
      rintro c hcT hcd
      exact (h _ hcd).of_smul_mem c hcT rfl
    case smul_atom_eq =>
      intro A a hc hcd
      exact (h (inl a) hcd).smul_atom_eq A a hc rfl
    case smul_litter_eq =>
      rintro A L hc hcd
      exact (h (inr L.toNearLitter) hcd).smul_litter_eq A L hc rfl

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

theorem lawfulIn_step (i : Atom ⊕ NearLitter) (h : LawfulBefore hσS hσT hr hS hU i) :
    LawfulIn hσS hσT hr hS hU {i} :=
  sorry

theorem lawfulIn_all : LawfulIn hσS hσT hr hS hU univ :=
  lawfulBefore_induction hσS hσT hr hS hU (lawfulIn_step hσS hσT hr hS hU)

theorem convertAllowable_smul : convertAllowable hσS hσT hr hS hU • S = T := by
  refine OrdSupport.ext ?_ ?_
  · intro c
    constructor
    · intro hc
      have := (lawfulIn_all hσS hσT hr hS hU).smul_mem
        ((convertAllowable hσS hσT hr hS hU)⁻¹ • c) hc (mem_univ _)
      rw [smul_inv_smul] at this
      exact this
    · intro hc
      refine (lawfulIn_all hσS hσT hr hS hU).of_smul_mem
        ((convertAllowable hσS hσT hr hS hU)⁻¹ • c) ?_ (mem_univ _)
      rw [smul_inv_smul]
      exact hc
  · intro c hcS hcT
    obtain ⟨A, a | N⟩ := c
    · simp only [OrdSupport.smul_cpos, Allowable.smul_supportCondition, map_inv, Tree.inv_apply,
        smul_inl]
      have hd : (convertAtom T A ((Allowable.toStructPerm
        (convertAllowable hσS hσT hr hS hU) A)⁻¹ • a)).Dom
      · change _ ∈ S at hcS
        rw [convertAtom_dom hσS hσT hr hS hU]
        simp only [Allowable.smul_supportCondition, map_inv, Tree.inv_apply, smul_inl] at hcS
        exact hcS
      have := (lawfulIn_all hσS hσT hr hS hU).smul_atom_eq A _ hd (mem_univ _)
      rw [smul_inv_smul] at this
      rw [hS.cpos_get_eq]
      have goal := convertAtom_get hd
      simp_rw [← this] at goal
      exact goal.symm
    · obtain ⟨L, rfl⟩ := (hU.isLitter_of_mem_equiv hr.equiv hcT).exists_litter_eq
      have hL := hS.isLitter_of_mem hcS
      simp only [map_inv, Tree.inv_apply] at hL
      simp only [OrdSupport.smul_cpos, Allowable.smul_supportCondition, map_inv, Tree.inv_apply,
        smul_inr]
      have hd : (convertLitter T A ((Allowable.toStructPerm
        (convertAllowable hσS hσT hr hS hU) A)⁻¹ • L)).Dom
      · change _ ∈ S at hcS
        rw [convertLitter_dom hσS hσT hr hS hU]
        simp only [Allowable.smul_supportCondition, map_inv, Tree.inv_apply, smul_inr] at hcS
        rw [(hS.isLitter_of_mem hcS).eq_fst_toNearLitter] at hcS
        exact hcS
      have := (lawfulIn_all hσS hσT hr hS hU).smul_litter_eq A _ hd (mem_univ _)
      rw [hS.cpos_get_eq, hL.eq_fst_toNearLitter]
      simp only [NearLitterPerm.smul_nearLitter_fst, Litter.toNearLitter_fst]
      rw [← convertLitter_get hd]
      simp_rw [← this]
      have hL' : (Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A •
        ((Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A)⁻¹ •
          L).toNearLitter).IsLitter
      · rw [this]
        rw [(convertLitter_isLitter hr hU hd).eq_fst_toNearLitter]
        exact NearLitter.IsLitter.mk _
      congr
      rw [hL'.eq_fst_toNearLitter]
      simp only [NearLitterPerm.smul_nearLitter_fst, Litter.toNearLitter_fst, smul_inv_smul]

/-

theorem mem_before_smul_iff_mem_before (A : ExtendedIndex β) (L : Litter) (P : InflexibleCoePath A)
    (ih : LawfulBefore hσS hσT hr hS hU (inr L.toNearLitter))
    (c : SupportCondition P.δ) :
    c ∈ (S.before (inr L.toNearLitter)).comp P.δ (P.B.cons (coe_lt P.hδ)) ↔
    Tree.comp (P.B.cons (coe_lt P.hδ))
        (Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU)) • c ∈
      ((T.before (inr L.toNearLitter)).comp P.δ (P.B.cons (coe_lt P.hδ))) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [hS.cpos_get_eq] at h₂
    refine ⟨ih' _ h₁ h₂, ?_⟩
    change (T.cpos (convertAllowable hσS hσT hr hS hU •
      ⟨(P.B.cons (coe_lt P.hδ)).comp c.path, c.value⟩)).get _ < _
    rw [(ih _ h₂).cpos_get h₁]
    exact h₂
  · rintro ⟨h₁, h₂⟩
    change (convertAllowable hσS hσT hr hS hU •
      ⟨(P.B.cons (coe_lt P.hδ)).comp c.path, c.value⟩) ∈ T at h₁
    change (T.cpos (convertAllowable hσS hσT hr hS hU •
      ⟨(P.B.cons (coe_lt P.hδ)).comp c.path, c.value⟩)).get _ < _ at h₂
    refine ⟨ih'' _ h₁ h₂, ?_⟩
    rw [(ih''' _ h₁ h₂).cpos_get (ih'' _ h₁ h₂)] at h₂
    rw [hS.cpos_get_eq]
    exact h₂

#exit

theorem before_smul_eq_before (A : ExtendedIndex β) (L : Litter) (P : InflexibleCoePath A)
    (t : Tangle P.δ) (hL : L = fuzz (coe_ne_coe.mpr <| coe_ne' P.hδε) t)
    (hLd : (convertLitter T ((P.B.cons (coe_lt P.hε)).cons (bot_lt_coe _))
      (fuzz (coe_ne_coe.mpr <| coe_ne' P.hδε) t)).Dom)
    (ih : ∀ c : SupportCondition P.δ, c.value < inr L.toNearLitter →
      ConvertLawfulAt hσS hσT hr hS hU ⟨(P.B.cons (coe_lt P.hδ)).comp c.path, c.value⟩)
    (ih' : ∀ c : SupportCondition P.δ, c.value < inr L.toNearLitter →
      (⟨(P.B.cons (coe_lt P.hδ)).comp c.path, c.value⟩ ∈ S ↔
      convertAllowable hσS hσT hr hS hU • ⟨(P.B.cons (coe_lt P.hδ)).comp c.path, c.value⟩ ∈ T)) :
    (S.before (inr (Litter.toNearLitter L))).comp P.δ (P.B.cons (coe_lt P.hδ)) =
    (show Allowable (P.δ : Iic α) from
      (Allowable.comp (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from
          P.B.cons (coe_lt P.hδ)))
        (convertAllowable hσS hσT hr hS hU))⁻¹ •
    ((T.before (inr (Litter.toNearLitter L))).comp P.δ (P.B.cons (coe_lt P.hδ))) := by
  dsimp only
  refine OrdSupport.ext ?_ ?_
  · intro c
    rw [mem_before_smul_iff_mem_before hσS hσT hr hS hU A L P t hL hLd ih ih' c,
      OrdSupport.smul_mem, inv_inv, Allowable.smul_supportCondition,
      Allowable.toStructPerm_comp (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from
        P.B.cons (coe_lt P.hδ))]
    rfl
  · intro c hcS hcT
    simp only [OrdSupport.smul_cpos, inv_inv]
    have ih := ih c ?_
    swap
    · obtain ⟨_, hc⟩ := hcS
      rw [hS.cpos_get_eq] at hc
      exact hc
    obtain ⟨B, a | N⟩ := c
    · have ih := ih ?_
      swap
      · rw [convertAtom_dom hσS hσT hr hS hU]
        exact hcS.1
      dsimp only at ih
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
      have ih := ih hN ?_
      swap
      · rw [convertLitter_dom hσS hσT hr hS hU, ← hN.eq_fst_toNearLitter]
        exact hcS.1
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

theorem convert_inflexibleCoe (A : ExtendedIndex β) (L : Litter) (hL : InflexibleCoe A L)
    (hLd : (convertLitter T ((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _))
      (fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε) hL.t)).Dom)
    (ih : ∀ c : SupportCondition hL.path.δ, c.value < inr L.toNearLitter →
      ConvertLawfulAt hσS hσT hr hS hU ⟨(hL.path.B.cons (coe_lt hL.path.hδ)).comp c.path, c.value⟩)
    (ih' : ∀ c : SupportCondition hL.path.δ, c.value < inr L.toNearLitter →
      (⟨(hL.path.B.cons (coe_lt hL.path.hδ)).comp c.path, c.value⟩ ∈ S ↔
      convertAllowable hσS hσT hr hS hU •
        ⟨(hL.path.B.cons (coe_lt hL.path.hδ)).comp c.path, c.value⟩ ∈ T)) :
    fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε)
      (Allowable.comp
        (show Path ((β : IicBot α) : TypeIndex) (hL.path.δ : IicBot α) from
          hL.path.B.cons (coe_lt hL.path.hδ))
        (convertAllowable hσS hσT hr hS hU) • hL.t) =
    (Part.get (convertLitter T ((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _))
      (fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε) hL.t)) hLd).fst := by
  have := hσS.inflexibleCoe_spec A L.toNearLitter ?_ hL
  swap
  · rw [convertLitter_dom hσS hσT hr hS hU] at hLd
    simp_rw [hL.hL, hL.path.hA]
    exact hLd
  obtain ⟨χ, hχ₁, hχ₂, h⟩ := this
  simp_rw [hS.cpos_get_eq] at h
  have := spec_inflexibleCoe hσS hσT hr hS hU A L hL χ ?_ h
  swap
  · rw [convertLitter_dom hσS hσT hr hS hU] at hLd
    simp_rw [hL.hL, hL.path.hA]
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
  exact before_smul_eq_before hσS hσT hr hS hU A L P t hL hLd ih ih'

theorem convertLawfulAt_litter_extends' (A : ExtendedIndex β) (L : Litter)
    (ih : ∀ c : SupportCondition β, c.value < inr L.toNearLitter →
      ConvertLawfulAt hσS hσT hr hS hU c)
    (ih' : ∀ c : SupportCondition β, c.value < inr L.toNearLitter →
      (c ∈ S ↔ convertAllowable hσS hσT hr hS hU • c ∈ T))
    (hLd : (convertLitter T A L).Dom) :
    Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A • L =
    ((convertLitter T A L).get hLd).1 := by
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A L
  · sorry
  · simp_rw [hL.hL, hL.path.hA]
    rw [toStructPerm_smul_fuzz β hL.path.γ ⊥ hL.path.ε]
    swap
    · exact bot_lt_coe _
    swap
    · intro h
      simp only [IioBot.bot_ne_mk_coe] at h
    have hc := Constrains.fuzz_bot hL.path.hε hL.path.B hL.a
    rw [← hL.hL, ← hL.path.hA] at hc
    specialize ih _ (constrains_subrelation _ _ hc) ?_
    · rw [convertAtom_dom hσS hσT hr hS hU]
      rw [convertLitter_dom hσS hσT hr hS hU] at hLd
      exact hS.transConstrains_mem _ _ (Reduced.mkAtom _) (Relation.TransGen.single hc) hLd
    rw [← Allowable.toStructPerm_apply (β := (β : IicBot α)), NearLitterPerm.ofBot_smul] at ih
    rw [ih]
    exact convert_inflexibleBot hσS hσT hr hS hU A L hL _ _
  · simp_rw [hL.hL, hL.path.hA]
    rw [toStructPerm_smul_fuzz β hL.path.γ hL.path.δ hL.path.ε]
    swap
    · exact coe_lt_coe.mpr hL.path.hδ
    swap
    · intro h
      simp only [Subtype.mk.injEq, coe_inj] at h
      exact coe_ne' hL.path.hδε h
    simp_rw [hL.hL, hL.path.hA] at hLd
    refine convert_inflexibleCoe hσS hσT hr hS hU A L hL hLd ?_ ?_
    · intro c hc
      exact ih _ hc
    · intro c hc
      exact ih' _ hc

theorem convertLawfulAt_litter_extends (A : ExtendedIndex β) (L : Litter)
    (ih : ∀ c : SupportCondition β, c.value < inr L.toNearLitter →
      ConvertLawfulAt hσS hσT hr hS hU c)
    (ih' : ∀ c : SupportCondition β, c.value < inr L.toNearLitter →
      (c ∈ S ↔ convertAllowable hσS hσT hr hS hU • c ∈ T))
    (hLd : (convertLitter T A L).Dom) :
    Allowable.toStructPerm (convertAllowable hσS hσT hr hS hU) A • L.toNearLitter =
    (convertLitter T A L).get hLd :=
  StructAction.smul_toNearLitter_eq_of_precise _ StructAction.refine_precise
    (convertAllowable_spec hσS hσT hr hS hU) hLd
    (convertLawfulAt_litter_extends' hσS hσT hr hS hU A L ih ih' hLd)

theorem convertLawfulAt_all (c : SupportCondition β) :
    ConvertLawfulAt hσS hσT hr hS hU c ∧ (c ∈ S ↔ convertAllowable hσS hσT hr hS hU • c ∈ T) := by
  have : WellFounded (InvImage (· < ·) SupportCondition.value)
  · exact InvImage.wf _ IsWellFounded.wf
  refine this.induction
    (C := fun c => ConvertLawfulAt hσS hσT hr hS hU c ∧
      (c ∈ S ↔ convertAllowable hσS hσT hr hS hU • c ∈ T)) c ?_
  clear c
  intro c ih
  obtain ⟨A, a | N⟩ := c
  · constructor
    · refine convertLawfulAt_atom_extends hσS hσT hr hS hU A a ?_
      sorry
    · sorry
  · constructor
    · intro hL₁ hL₂
      obtain ⟨L, rfl⟩ := hL₁.exists_litter_eq
      refine convertLawfulAt_litter_extends hσS hσT hr hS hU A L ?_ ?_ hL₂
      · sorry
      · sorry
    · sorry

theorem convertAllowable_smul : convertAllowable hσS hσT hr hS hU • S = T := by
  refine OrdSupport.ext ?_ ?_
  · intro c
    have := convertLawfulAt_all hσS hσT hr hS hU ((convertAllowable hσS hσT hr hS hU)⁻¹ • c)
    obtain ⟨A, a | N⟩ := c
    · simp only [Allowable.smul_supportCondition, map_inv, Tree.inv_apply, smul_inl,
        convertLawfulAt_atom, smul_inv_smul] at this
      sorry
    · simp only [Allowable.smul_supportCondition, map_inv, Tree.inv_apply, smul_inr,
        convertLawfulAt_nearLitter, smul_inv_smul, NearLitterPerm.smul_nearLitter_fst] at this
      sorry
  · intro c hcS hcT
    have := convertLawfulAt_all hσS hσT hr hS hU ((convertAllowable hσS hσT hr hS hU)⁻¹ • c)
    obtain ⟨A, a | N⟩ := c
    · simp only [OrdSupport.smul_cpos, Allowable.smul_supportCondition, map_inv, Tree.inv_apply,
        smul_inl, convertLawfulAt_atom] at this ⊢
      have hd : (convertAtom T A ((Allowable.toStructPerm
        (convertAllowable hσS hσT hr hS hU) A)⁻¹ • a)).Dom
      · change _ ∈ S at hcS
        rw [convertAtom_dom hσS hσT hr hS hU]
        simp only [Allowable.smul_supportCondition, map_inv, Tree.inv_apply, smul_inl] at hcS
        exact hcS
      have := this.1 hd
      rw [smul_inv_smul] at this
      rw [hS.cpos_get_eq]
      have goal := convertAtom_get hd
      simp_rw [← this] at goal
      exact goal.symm
    · simp only [OrdSupport.smul_cpos, Allowable.smul_supportCondition, map_inv, Tree.inv_apply,
        smul_inr, convertLawfulAt_atom] at this ⊢
      have hd : (convertLitter T A ((Allowable.toStructPerm
        (convertAllowable hσS hσT hr hS hU) A)⁻¹ • N.1)).Dom
      · change _ ∈ S at hcS
        rw [convertLitter_dom hσS hσT hr hS hU]
        simp only [Allowable.smul_supportCondition, map_inv, Tree.inv_apply, smul_inr] at hcS
        rw [(hS.isLitter_of_mem hcS).eq_fst_toNearLitter] at hcS
        exact hcS
      have := this.1 ?_ hd
      · rw [smul_inv_smul] at this
        simp_rw [NearLitterPerm.smul_nearLitter_fst] at this
        have h' := (hS.isLitter_of_mem hcS).eq_fst_toNearLitter
        simp only [map_inv, Tree.inv_apply, NearLitterPerm.smul_nearLitter_fst] at h'
        rw [hS.cpos_get_eq, h', ← convertLitter_get hd]
        simp_rw [← this]
      · have := hS.isLitter_of_mem hcS
        simp only [map_inv, Tree.inv_apply] at this
        exact this

-/

end Spec

end ConNF
