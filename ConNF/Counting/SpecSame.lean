import ConNF.Foa
import ConNF.Counting.Spec

/-!
# Specifying two strong supports at once
-/

open Ordinal Quiver Set Sum WithBot

open scoped Classical

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}
  {σ : Spec β} {S T : OrdSupport β}
  (hσS : σ.Specifies S) (hσT : σ.Specifies T) (hS : S.Strong) (hT : T.Strong)

namespace Spec

theorem type_eq_type : type S.r = type T.r :=
  by rw [← orderType_eq_of_specifies hσS, ← orderType_eq_of_specifies hσT]

noncomputable def convertCondition (c : S) : T :=
  T.conditionAt (typein S.r c) (type_eq_type hσS hσT ▸ typein_lt_type S.r c)

@[simp]
theorem typein_convertCondition (c : S) :
    typein T.r (convertCondition hσS hσT c) = typein S.r c :=
  by rw [convertCondition, typein_conditionAt]

@[simp]
theorem convertCondition_convertCondition (c : S) :
    convertCondition hσT hσS (convertCondition hσS hσT c) = c := by
  refine typein_injective S.r ?_
  simp only [typein_convertCondition]

theorem convertCondition_atom (A : ExtendedIndex β) (a : Atom) (h : ⟨A, inl a⟩ ∈ S) :
    ∃ b : Atom, ∃ hb : ⟨A, inl b⟩ ∈ T,
      convertCondition hσS hσT ⟨⟨A, inl a⟩, h⟩ = ⟨⟨A, inl b⟩, hb⟩ := by
  have hc_spec := hσS.atom_spec A a a.1.toNearLitter h
    (hS.transConstrains_mem _ ⟨_, h⟩ (Reduced.mkLitter _)
      (Relation.TransGen.single <| Constrains.atom _ _)) rfl
  set d := convertCondition hσS hσT ⟨⟨A, inl a⟩, h⟩ with hd
  obtain ⟨⟨B, b | N⟩, hdT⟩ := d
  · have hd_spec := hσT.atom_spec B b b.1.toNearLitter hdT
      (hT.transConstrains_mem _ ⟨_, hdT⟩ (Reduced.mkLitter _)
        (Relation.TransGen.single <| Constrains.atom _ _)) rfl
    simp_rw [hd] at hd_spec
    simp only [OrdSupport.coe_sort_coe, typein_convertCondition,
      hc_spec, SpecCondition.atom.injEq] at hd_spec
    cases hd_spec.1
    exact ⟨b, hdT, rfl⟩
  exfalso
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β B N.1
  · have hd_spec := hσT.flexible_spec B N hdT hL
    simp_rw [hd] at hd_spec
    simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec] at hd_spec
  · obtain ⟨hdT', hd_spec⟩ := hσT.inflexibleBot_spec B N hdT hL
    simp_rw [hd] at hd_spec
    simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec] at hd_spec
  · obtain ⟨χ, hχ, hd_spec⟩ := hσT.inflexibleCoe_spec B N hdT hL
    simp_rw [hd] at hd_spec
    simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec, and_false] at hd_spec

noncomputable def convertAtom (A : ExtendedIndex β) (a : Atom) (h : ⟨A, inl a⟩ ∈ S) : Atom :=
  (convertCondition_atom hσS hσT hS hT A a h).choose

theorem convertAtom_mem (A : ExtendedIndex β) (a : Atom) (h : ⟨A, inl a⟩ ∈ S) :
    ⟨A, inl (convertAtom hσS hσT hS hT A a h)⟩ ∈ T :=
  (convertCondition_atom hσS hσT hS hT A a h).choose_spec.1

theorem convertCondition_eq_convertAtom (A : ExtendedIndex β) (a : Atom) (h : ⟨A, inl a⟩ ∈ S) :
    convertCondition hσS hσT ⟨⟨A, inl a⟩, h⟩ =
    ⟨⟨A, inl (convertAtom hσS hσT hS hT A a h)⟩, (convertAtom_mem hσS hσT hS hT A a h)⟩ :=
  (convertCondition_atom hσS hσT hS hT A a h).choose_spec.2

theorem convertCondition_litter (A : ExtendedIndex β) (L : Litter)
    (h : ⟨A, inr L.toNearLitter⟩ ∈ S) :
    ∃ L' : Litter, ∃ hL' : ⟨A, inr L'.toNearLitter⟩ ∈ T,
      convertCondition hσS hσT ⟨⟨A, inr L.toNearLitter⟩, h⟩ = ⟨⟨A, inr L'.toNearLitter⟩, hL'⟩ := by
  set d := convertCondition hσS hσT ⟨⟨A, inr L.toNearLitter⟩, h⟩ with hd
  obtain ⟨⟨B, b | N⟩, hdT⟩ := d
  · exfalso
    have hd_spec := hσT.atom_spec B b b.1.toNearLitter hdT
      (hT.transConstrains_mem _ ⟨_, hdT⟩ (Reduced.mkLitter _)
        (Relation.TransGen.single <| Constrains.atom _ _)) rfl
    simp_rw [hd] at hd_spec
    obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A L
    · have hc_spec := hσS.flexible_spec A L.toNearLitter h hL
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec] at hd_spec
    · obtain ⟨hL, hc_spec⟩ := hσS.inflexibleBot_spec A L.toNearLitter h hL
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec] at hd_spec
    · obtain ⟨χ, _, hc_spec⟩ := hσS.inflexibleCoe_spec A L.toNearLitter h hL
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec] at hd_spec
  obtain ⟨L', rfl⟩ := (isLitter_of_reduced (hT.reduced_of_mem ⟨_, hdT⟩)).exists_litter_eq
  obtain (hL₂ | ⟨⟨hL₂⟩⟩ | ⟨⟨hL₂⟩⟩) := flexible_cases' β B L'
  · have hd_spec := hσT.flexible_spec B L'.toNearLitter hdT hL₂
    simp_rw [hd] at hd_spec
    obtain (hL₁ | ⟨⟨hL₁⟩⟩ | ⟨⟨hL₁⟩⟩) := flexible_cases' β A L
    · have hc_spec := hσS.flexible_spec A L.toNearLitter h hL₁
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec,
        SpecCondition.flexible.injEq] at hd_spec
      cases hd_spec
      exact ⟨L', hdT, rfl⟩
    · obtain ⟨hL, hc_spec⟩ := hσS.inflexibleBot_spec A L.toNearLitter h hL₁
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec] at hd_spec
    · obtain ⟨χ, _, hc_spec⟩ := hσS.inflexibleCoe_spec A L.toNearLitter h hL₁
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec] at hd_spec
  · obtain ⟨hdT', hd_spec⟩ := hσT.inflexibleBot_spec B L'.toNearLitter hdT hL₂
    simp_rw [hd] at hd_spec
    obtain (hL₁ | ⟨⟨hL₁⟩⟩ | ⟨⟨hL₁⟩⟩) := flexible_cases' β A L
    · have hc_spec := hσS.flexible_spec A L.toNearLitter h hL₁
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec] at hd_spec
    · obtain ⟨hL, hc_spec⟩ := hσS.inflexibleBot_spec A L.toNearLitter h hL₁
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec, Litter.toNearLitter_fst,
        SpecCondition.inflexibleBot.injEq] at hd_spec
      cases hd_spec.1
      exact ⟨L', hdT, rfl⟩
    · obtain ⟨χ, _, hc_spec⟩ := hσS.inflexibleCoe_spec A L.toNearLitter h hL₁
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec] at hd_spec
  · obtain ⟨χ, hχ, hd_spec⟩ := hσT.inflexibleCoe_spec B L'.toNearLitter hdT hL₂
    simp_rw [hd] at hd_spec
    obtain (hL₁ | ⟨⟨hL₁⟩⟩ | ⟨⟨hL₁⟩⟩) := flexible_cases' β A L
    · have hc_spec := hσS.flexible_spec A L.toNearLitter h hL₁
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec, and_false] at hd_spec
    · obtain ⟨hL, hc_spec⟩ := hσS.inflexibleBot_spec A L.toNearLitter h hL₁
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec, and_false] at hd_spec
    · obtain ⟨χ, _, hc_spec⟩ := hσS.inflexibleCoe_spec A L.toNearLitter h hL₁
      simp only [Litter.toNearLitter_fst, OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec,
        SpecCondition.inflexibleCoe.injEq] at hd_spec
      cases hd_spec.2.1
      exact ⟨L', hdT, rfl⟩

noncomputable def convertLitter (A : ExtendedIndex β) (L : Litter)
    (h : ⟨A, inr L.toNearLitter⟩ ∈ S) : Litter :=
  (convertCondition_litter hσS hσT hT A L h).choose

theorem convertLitter_mem (A : ExtendedIndex β) (L : Litter)
    (h : ⟨A, inr L.toNearLitter⟩ ∈ S) :
    ⟨A, inr (convertLitter hσS hσT hT A L h).toNearLitter⟩ ∈ T :=
  (convertCondition_litter hσS hσT hT A L h).choose_spec.1

theorem convertCondition_eq_convertLitter (A : ExtendedIndex β) (L : Litter)
    (h : ⟨A, inr L.toNearLitter⟩ ∈ S) :
    convertCondition hσS hσT ⟨⟨A, inr L.toNearLitter⟩, h⟩ =
    ⟨⟨A, inr (convertLitter hσS hσT hT A L h).toNearLitter⟩, (convertLitter_mem hσS hσT hT A L h)⟩ :=
  (convertCondition_litter hσS hσT hT A L h).choose_spec.2

end Spec

end ConNF
