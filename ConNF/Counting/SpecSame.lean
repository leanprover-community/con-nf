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
  · have hcS := hσS.inflexibleBot_spec A L.toNearLitter hc₁ hL ?_
    · simp_rw [hS.cpos_get_eq, ← hc₂, hcT] at hcS
    · refine hS.transConstrains_mem _ _ (Reduced.mkAtom hL.a) (Relation.TransGen.single ?_) hc₁
      simp_rw [hL.hL, hL.path.hA]
      exact Constrains.fuzz_bot hL.path.hε _ hL.a
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
  · have hcT := hσT.inflexibleBot_spec A L.toNearLitter hN hL ?_
    · simp_rw [hS.cpos_get_eq, ← hc₂, hcT] at hcS
    · refine hU.transConstrains_mem_equiv hr.equiv _ _
        (Reduced.mkAtom hL.a) (Relation.TransGen.single ?_) hN
      simp_rw [hL.hL, hL.path.hA]
      exact Constrains.fuzz_bot hL.path.hε _ hL.a
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
    dsimp only at h₂
    obtain ⟨A, b | N⟩ := c <;> cases h₂.2
    · exact ⟨b, h₁, h₂.1.symm⟩
    · obtain ⟨L, hL⟩ := cpos_nearLitter A N h₁
      rw [hL] at h₂
      simp only at h₂

theorem convertLitter_dom (A : ExtendedIndex β) (L : Litter) :
    (convertLitter T A L).Dom ↔ ⟨A, inr L.toNearLitter⟩ ∈ S :=
  sorry

theorem deconvertAtom_dom (A : ExtendedIndex β) (a : Atom) :
    (deconvertAtom T A a).Dom ↔ ⟨A, inl a⟩ ∈ T :=
  sorry

theorem deconvertLitter_dom (A : ExtendedIndex β) (N : NearLitter) :
    (deconvertLitter T A N).Dom ↔ ⟨A, inr N⟩ ∈ T :=
  sorry

theorem convertAtom_mem {A : ExtendedIndex β} {a : Atom} (h : (convertAtom T A a).Dom) :
    ⟨A, inl ((convertAtom T A a).get h)⟩ ∈ T :=
  h.choose_spec.1

theorem convertLitter_mem {A : ExtendedIndex β} {L : Litter} (h : (convertLitter T A L).Dom) :
    ⟨A, inr ((convertLitter T A L).get h)⟩ ∈ T :=
  h.choose_spec.1

theorem convertAtom_get {A : ExtendedIndex β} {a : Atom} (h : (convertAtom T A a).Dom) :
    (T.cpos ⟨A, inl ((convertAtom T A a).get h)⟩).get (convertAtom_mem h) = inl a :=
  h.choose_spec.2

theorem convertLitter_get {A : ExtendedIndex β} {L : Litter} (h : (convertLitter T A L).Dom) :
    (T.cpos ⟨A, inr ((convertLitter T A L).get h)⟩).get (convertLitter_mem h) = inr L.toNearLitter :=
  h.choose_spec.2

theorem convertAtom_dom_small (A : ExtendedIndex β) :
    Small (PFun.Dom (convertAtom T A)) := by
  sorry

theorem convertLitter_dom_small (A : ExtendedIndex β) :
    Small (PFun.Dom (convertLitter T A)) := by
  sorry

noncomputable def convert : StructAction β :=
  fun A => {
    atomMap := convertAtom T A
    litterMap := convertLitter T A
    atomMap_dom_small := convertAtom_dom_small A
    litterMap_dom_small := convertLitter_dom_small A
  }

end Spec

end ConNF
