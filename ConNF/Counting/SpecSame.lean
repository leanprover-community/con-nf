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

theorem typein_lt {c : S} :
    typein S.r c < σ.orderType :=
  orderType_eq_of_specifies hσS ▸ typein_lt_type S.r _

noncomputable def convertCondition (c : S) : T :=
  T.conditionAt (typein S.r c) (type_eq_type hσS hσT ▸ typein_lt_type S.r c)

@[simp]
theorem typein_convertCondition (c : S) :
    typein T.r (convertCondition hσS hσT c) = typein S.r c :=
  by rw [convertCondition, typein_conditionAt]

theorem convertCondition_eq_of_typein_eq {c : S} {d : T}
    (hb : typein S.r c = typein T.r d) :
    convertCondition hσS hσT c = d := by
  refine typein_injective T.r ?_
  rw [← hb, typein_convertCondition]

@[simp]
theorem convertCondition_lt (c d : S) :
    convertCondition hσS hσT c < convertCondition hσS hσT d ↔ c < d := by
  refine (typein_lt_typein T.r).symm.trans ?_
  simp only [OrdSupport.coe_sort_coe, typein_convertCondition, typein_lt_typein]
  rfl

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
  · obtain ⟨χ, hχ₁, hχ₂, hd_spec⟩ := hσT.inflexibleCoe_spec B N hdT hL
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
    · obtain ⟨χ, _, _, hc_spec⟩ := hσS.inflexibleCoe_spec A L.toNearLitter h hL
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
    · obtain ⟨χ, _, _, hc_spec⟩ := hσS.inflexibleCoe_spec A L.toNearLitter h hL₁
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
    · obtain ⟨χ, _, _, hc_spec⟩ := hσS.inflexibleCoe_spec A L.toNearLitter h hL₁
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec] at hd_spec
  · obtain ⟨χ, _, _, hd_spec⟩ := hσT.inflexibleCoe_spec B L'.toNearLitter hdT hL₂
    simp_rw [hd] at hd_spec
    obtain (hL₁ | ⟨⟨hL₁⟩⟩ | ⟨⟨hL₁⟩⟩) := flexible_cases' β A L
    · have hc_spec := hσS.flexible_spec A L.toNearLitter h hL₁
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec, and_false] at hd_spec
    · obtain ⟨hL, hc_spec⟩ := hσS.inflexibleBot_spec A L.toNearLitter h hL₁
      simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hc_spec, and_false] at hd_spec
    · obtain ⟨χ, _, _, hc_spec⟩ := hσS.inflexibleCoe_spec A L.toNearLitter h hL₁
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

theorem convertAtom_eq_of_typein_eq {A₁ A₂ : ExtendedIndex β} {a₁ a₂ : Atom}
    {h₁ : ⟨A₁, inl a₁⟩ ∈ S} {h₂ : ⟨A₂, inl a₂⟩ ∈ T}
    (h : typein S.r ⟨_, h₁⟩ = typein T.r ⟨_, h₂⟩) :
    convertAtom hσS hσT hS hT A₁ a₁ h₁ = a₂ := by
  have := convertCondition_eq_of_typein_eq hσS hσT h
  simp only [convertCondition_eq_convertAtom hσS hσT hS hT, Subtype.mk.injEq,
    SupportCondition.mk.injEq, inl.injEq] at this
  exact this.2

theorem convertLitter_eq_of_typein_eq {A₁ A₂ : ExtendedIndex β} {L₁ L₂ : Litter}
    {h₁ : ⟨A₁, inr L₁.toNearLitter⟩ ∈ S} {h₂ : ⟨A₂, inr L₂.toNearLitter⟩ ∈ T}
    (h : typein S.r ⟨_, h₁⟩ = typein T.r ⟨_, h₂⟩) :
    convertLitter hσS hσT hT A₁ L₁ h₁ = L₂ := by
  have := convertCondition_eq_of_typein_eq hσS hσT h
  simp only [convertCondition_eq_convertLitter hσS hσT hT, Subtype.mk.injEq,
    SupportCondition.mk.injEq, inr.injEq, Litter.toNearLitter_injective.eq_iff] at this
  exact this.2

@[simp]
theorem convertCondition_path (c : S) :
    (convertCondition hσS hσT c).val.path = c.val.path := by
  obtain ⟨⟨A, a | N⟩, hc⟩ := c
  · rw [convertCondition_eq_convertAtom hσS hσT hS hT]
  · obtain ⟨L, rfl⟩ := (isLitter_of_reduced (hS.reduced_of_mem ⟨_, hc⟩)).exists_litter_eq
    rw [convertCondition_eq_convertLitter hσS hσT hT]

@[simp]
theorem convertCondition_mk (A : ExtendedIndex β) (x : Atom ⊕ NearLitter) (h : ⟨A, x⟩ ∈ S) :
    ⟨A, (convertCondition hσS hσT ⟨⟨A, x⟩, h⟩).val.value⟩ =
    (convertCondition hσS hσT ⟨⟨A, x⟩, h⟩).val := by
  have := convertCondition_path hσS hσT hS hT ⟨⟨A, x⟩, h⟩
  dsimp only at this
  conv in SupportCondition.mk _ =>
    rw [← this]

@[simp]
theorem convertAtom_convertAtom (A : ExtendedIndex β) (a : Atom) (h : ⟨A, inl a⟩ ∈ S) :
    convertAtom hσT hσS hT hS A (convertAtom hσS hσT hS hT A a h)
      (convertAtom_mem hσS hσT hS hT A a h) = a := by
  have := convertCondition_convertCondition hσS hσT ⟨⟨A, inl a⟩, h⟩
  rw [convertCondition_eq_convertAtom, convertCondition_eq_convertAtom] at this
  simp only [Subtype.mk.injEq, SupportCondition.mk.injEq, inl.injEq, true_and] at this
  exact this

@[simp]
theorem convertLitter_convertLitter (A : ExtendedIndex β) (L : Litter)
    (h : ⟨A, inr L.toNearLitter⟩ ∈ S) :
    convertLitter hσT hσS hS A (convertLitter hσS hσT hT A L h)
      (convertLitter_mem hσS hσT hT A L h) = L := by
  have := convertCondition_convertCondition hσS hσT ⟨⟨A, inr L.toNearLitter⟩, h⟩
  rw [convertCondition_eq_convertLitter, convertCondition_eq_convertLitter] at this
  simp only [Subtype.mk.injEq, SupportCondition.mk.injEq, inr.injEq, true_and,
    Litter.toNearLitter_injective.eq_iff] at this
  exact this

theorem convertAtom_injective {A : ExtendedIndex β} {a b : Atom}
    (ha : ⟨A, inl a⟩ ∈ S) (hb : ⟨A, inl b⟩ ∈ S)
    (h : convertAtom hσS hσT hS hT A a ha = convertAtom hσS hσT hS hT A b hb) :
    a = b := by
  have := convertAtom_convertAtom hσS hσT hS hT A a ha
  simp_rw [h, convertAtom_convertAtom] at this
  exact this.symm

theorem convertLitter_injective {A : ExtendedIndex β} {L₁ L₂ : Litter}
    (h₁ : ⟨A, inr L₁.toNearLitter⟩ ∈ S) (h₂ : ⟨A, inr L₂.toNearLitter⟩ ∈ S)
    (h : convertLitter hσS hσT hT A L₁ h₁ = convertLitter hσS hσT hT A L₂ h₂) :
    L₁ = L₂ := by
  have := convertLitter_convertLitter hσS hσT hS hT A L₁ h₁
  simp_rw [h, convertLitter_convertLitter] at this
  exact this.symm

@[simp]
theorem typein_convertAtom (A : ExtendedIndex β) (a : Atom) (h : ⟨A, inl a⟩ ∈ S) :
    typein T.r ⟨⟨A, inl (convertAtom hσS hσT hS hT A a h)⟩, convertAtom_mem hσS hσT hS hT A a h⟩ =
    typein S.r ⟨⟨A, inl a⟩, h⟩ :=
  by rw [← convertCondition_eq_convertAtom, typein_convertCondition]

@[simp]
theorem typein_convertLitter (A : ExtendedIndex β) (L : Litter) (h : ⟨A, inr L.toNearLitter⟩ ∈ S) :
    typein T.r ⟨⟨A, inr (convertLitter hσS hσT hT A L h).toNearLitter⟩,
      convertLitter_mem hσS hσT hT A L h⟩ =
    typein S.r ⟨⟨A, inr L.toNearLitter⟩, h⟩ :=
  by rw [← convertCondition_eq_convertLitter, typein_convertCondition]

noncomputable def convert : StructAction β :=
  fun A => {
    atomMap := fun a => ⟨_, fun h => convertAtom hσS hσT hS hT A a h⟩
    litterMap := fun L => ⟨_, fun h => (convertLitter hσS hσT hT A L h).toNearLitter⟩
    atomMap_dom_small := by
      refine S.small.preimage ?_
      intros _ _ h
      simp only [SupportCondition.mk.injEq, inl.injEq, true_and] at h
      exact h
    litterMap_dom_small := by
      refine S.small.preimage ?_
      intros _ _ h
      simp only [SupportCondition.mk.injEq, inr.injEq, true_and,
        Litter.toNearLitter_injective.eq_iff] at h
      exact h
  }

@[simp]
theorem convert_atomMap {A : ExtendedIndex β} {a : Atom}
    {h : (⟨A, inl a⟩ : SupportCondition β) ∈ S} :
    ((convert hσS hσT hS hT A).atomMap a).get h = convertAtom hσS hσT hS hT A a h :=
  rfl

@[simp]
theorem convert_litterMap {A : ExtendedIndex β} {L : Litter}
    {h : (⟨A, inr L.toNearLitter⟩ : SupportCondition β) ∈ S} :
    ((convert hσS hσT hS hT A).litterMap L).get h = (convertLitter hσS hσT hT A L h).toNearLitter :=
  rfl

@[simp]
theorem _root_.ConNF.mem_toNearLitter {a : Atom} {L : Litter} :
    a ∈ L.toNearLitter ↔ a.1 = L :=
  Iff.rfl

@[simp]
theorem convertAtom_fst {A : ExtendedIndex β} {a : Atom}
    (h : (⟨A, inl a⟩ : SupportCondition β) ∈ S) :
    (convertAtom hσS hσT hS hT A a h).1 =
    convertLitter hσS hσT hT A a.1 (hS.fst_toNearLitter_mem h) := by
  have hσ₁ := hσS.atom_spec A a a.1.toNearLitter h (hS.fst_toNearLitter_mem h) rfl
  have hσ₂ := hσT.atom_spec A (convertAtom hσS hσT hS hT A a h)
    (convertAtom hσS hσT hS hT A a h).1.toNearLitter (convertAtom_mem hσS hσT hS hT A a h)
    (hT.fst_toNearLitter_mem (convertAtom_mem hσS hσT hS hT A a h)) rfl
  rw [← convertCondition_eq_convertAtom] at hσ₂
  simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hσ₁, SpecCondition.atom.injEq,
    true_and] at hσ₂
  have := congr_arg (typein T.r)
    (convertCondition_eq_convertLitter hσS hσT hT A a.1 (hS.fst_toNearLitter_mem h))
  simp only [OrdSupport.coe_sort_coe, typein_convertCondition, hσ₂, typein_inj, Subtype.mk.injEq,
    SupportCondition.mk.injEq, inr.injEq, true_and, Litter.toNearLitter_injective.eq_iff] at this
  exact this

theorem convert_lawful : StructAction.Lawful (convert hσS hσT hS hT) :=
  fun A => {
    atomMap_injective := fun a b ha hb h => convertAtom_injective hσS hσT hS hT ha hb h
    litterMap_injective := by
      intro L₁ L₂ h₁ h₂ h
      refine convertLitter_injective hσS hσT hS hT h₁ h₂ ?_
      obtain ⟨a, ha₁, ha₂⟩ := h
      exact eq_of_mem_litterSet_of_mem_litterSet ha₁ ha₂
    atom_mem := by
      intro a ha L hL
      simp only [convert_atomMap, convert_litterMap, mem_toNearLitter, convertAtom_fst]
      constructor
      · rintro rfl
        rfl
      · exact convertLitter_injective hσS hσT hS hT (hS.fst_toNearLitter_mem ha) hL
  }

theorem convert_mapFlexible : StructAction.MapFlexible (convert hσS hσT hS hT) := by
  intro A L hL₁ hL₂
  have hLS := hσS.flexible_spec A L.toNearLitter hL₁ hL₂
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A (convertLitter hσS hσT hT A L hL₁)
  · exact hL
  · exfalso
    obtain ⟨_, hLT⟩ := hσT.inflexibleBot_spec A _ (convertLitter_mem hσS hσT hT A L hL₁) hL
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter, hLS, Litter.toNearLitter_fst] at hLT
  · exfalso
    obtain ⟨χ, _, _, _, hLT⟩ := hσT.inflexibleCoe_spec A _ (convertLitter_mem hσS hσT hT A L hL₁) hL
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter, hLS, Litter.toNearLitter_fst] at hLT

noncomputable def convertAllowable : Allowable β :=
  (StructApprox.freedom_of_action β
    (StructAction.rc (convert hσS hσT hS hT) (convert_lawful hσS hσT hS hT))
    (StructAction.rc_free _ _ (convert_mapFlexible hσS hσT hS hT))).choose

theorem convertAllowable_spec :
    (StructAction.rc (convert hσS hσT hS hT)
      (convert_lawful hσS hσT hS hT)).ExactlyApproximates
    (Allowable.toStructPerm (convertAllowable hσS hσT hS hT)) :=
  (StructApprox.freedom_of_action β
    (StructAction.rc (convert hσS hσT hS hT) (convert_lawful hσS hσT hS hT))
    (StructAction.rc_free _ _ (convert_mapFlexible hσS hσT hS hT))).choose_spec

/-- If `LawfulIn s` holds, `convertAllowable` acts on support conditions assigned at a time in `s`
exactly as specified by `convertCondition`. -/
structure LawfulIn (s : Set Ordinal) : Prop where
  smul_eq : ∀ c : S, typein S.r c ∈ s →
    convertAllowable hσS hσT hS hT • c.val = convertCondition hσS hσT c
  inv_smul_eq : ∀ c : T, typein T.r c ∈ s →
    (convertAllowable hσS hσT hS hT)⁻¹ • c.val = convertCondition hσT hσS c

theorem LawfulIn.smul_mem {s : Set Ordinal} (h : LawfulIn hσS hσT hS hT s)
    (c : S) (hc : typein S.r c ∈ s) :
    convertAllowable hσS hσT hS hT • c.val ∈ T := by
  rw [h.smul_eq c hc]
  exact (convertCondition hσS hσT c).prop

theorem LawfulIn.inv_smul_mem {s : Set Ordinal} (h : LawfulIn hσS hσT hS hT s)
    (c : T) (hc : typein T.r c ∈ s) :
    (convertAllowable hσS hσT hS hT)⁻¹ • c.val ∈ S := by
  rw [h.inv_smul_eq c hc]
  exact (convertCondition hσT hσS c).prop

theorem LawfulIn.typein_smul {s : Set Ordinal} (h : LawfulIn hσS hσT hS hT s)
    (c : S) (hc : typein S.r c ∈ s) :
    typein T.r ⟨convertAllowable hσS hσT hS hT • c.val, h.smul_mem c hc⟩ = typein S.r c :=
  by simp only [h.smul_eq c hc, OrdSupport.coe_sort_coe, Subtype.coe_eta, typein_convertCondition]

theorem LawfulIn.typein_inv_smul {s : Set Ordinal} (h : LawfulIn hσS hσT hS hT s)
    (c : T) (hc : typein T.r c ∈ s) :
    typein S.r ⟨(convertAllowable hσS hσT hS hT)⁻¹ • c.val, h.inv_smul_mem c hc⟩ = typein T.r c :=
  by simp only [h.inv_smul_eq c hc, OrdSupport.coe_sort_coe, Subtype.coe_eta,
    typein_convertCondition]

abbrev LawfulBefore (i : Ordinal) : Prop :=
  LawfulIn hσS hσT hS hT {j | j < i}

theorem lawfulIn_iff (s : Set Ordinal) :
    LawfulIn hσS hσT hS hT s ↔ ∀ i ∈ s, LawfulIn hσS hσT hS hT {i} := by
  constructor
  · intro h i hi
    constructor
    case smul_eq =>
      rintro c rfl
      exact h.smul_eq c hi
    case inv_smul_eq =>
      rintro c rfl
      exact h.inv_smul_eq c hi
  · intro h
    constructor
    case smul_eq =>
      intro c hcd
      refine (h _ hcd).smul_eq c rfl
    case inv_smul_eq =>
      intro c hcd
      refine (h _ hcd).inv_smul_eq c rfl

theorem lawfulBefore_induction
    (h : ∀ i, LawfulBefore hσS hσT hS hT i → LawfulIn hσS hσT hS hT {i}) :
    LawfulIn hσS hσT hS hT univ := by
  rw [lawfulIn_iff]
  simp only [mem_univ, forall_true_left]
  intro i
  induction i using Ordinal.induction with
  | h j ih =>
    refine h j ?_
    rw [LawfulBefore, lawfulIn_iff]
    exact ih

theorem mem_before_smul_iff_mem_before (A : ExtendedIndex β) (i : Ordinal)
    (P : InflexibleCoePath A) (ih : LawfulBefore hσS hσT hS hT i)
    (c : SupportCondition P.δ) :
    c ∈ (S.before i).comp P.δ (P.B.cons (coe_lt P.hδ)) ↔
    Tree.comp (P.B.cons (coe_lt P.hδ))
        (Allowable.toStructPerm (convertAllowable hσS hσT hS hT)) • c ∈
      ((T.before i).comp P.δ (P.B.cons (coe_lt P.hδ))) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨ih.smul_mem ⟨_, h₁⟩ h₂, ?_⟩
    change typein T.r ⟨convertAllowable hσS hσT hS hT •
      ⟨(P.B.cons (coe_lt P.hδ)).comp c.path, c.value⟩, _⟩ < _
    rw [ih.typein_smul ⟨_, h₁⟩ h₂]
    exact h₂
  · rintro ⟨h₁, h₂⟩
    change convertAllowable hσS hσT hS hT •
      ⟨(P.B.cons (coe_lt P.hδ)).comp c.path, c.value⟩ ∈ T at h₁
    change typein T.r ⟨(convertAllowable hσS hσT hS hT •
      ⟨(P.B.cons (coe_lt P.hδ)).comp c.path, c.value⟩), _⟩ < _ at h₂
    refine ⟨?_, ?_⟩
    · have := ih.inv_smul_mem ⟨_, h₁⟩ h₂
      rw [inv_smul_smul] at this
      exact this
    · simp only [← ih.typein_inv_smul ⟨_, h₁⟩ h₂, inv_smul_smul] at h₂
      exact h₂

theorem before_smul_eq_before (A : ExtendedIndex β) (i : Ordinal)
    (P : InflexibleCoePath A) (ih : LawfulBefore hσS hσT hS hT i) :
    (S.before i).comp P.δ (P.B.cons (coe_lt P.hδ)) =
    (show Allowable (P.δ : Iic α) from
      (Allowable.comp (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from
          P.B.cons (coe_lt P.hδ)))
        (convertAllowable hσS hσT hS hT))⁻¹ •
    (T.before i).comp P.δ (P.B.cons (coe_lt P.hδ)) := by
  dsimp only
  refine OrdSupport.ext ?_ ?_ ?_
  · intro c
    rw [mem_before_smul_iff_mem_before hσS hσT hS hT A i P ih c,
      OrdSupport.smul_mem, inv_inv, Allowable.smul_supportCondition,
      Allowable.toStructPerm_comp (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from
        P.B.cons (coe_lt P.hδ))]
    exact id
  · intro c
    rw [mem_before_smul_iff_mem_before hσS hσT hS hT A i P ih c,
      OrdSupport.smul_mem, inv_inv, Allowable.smul_supportCondition,
      Allowable.toStructPerm_comp (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from
        P.B.cons (coe_lt P.hδ))]
    exact id
  · intro c d
    have hc := ih.smul_eq ⟨_, c.prop.1⟩ c.prop.2
    have hd := ih.smul_eq ⟨_, d.prop.1⟩ d.prop.2
    simp only [Allowable.smul_supportCondition, SupportCondition.ext_iff] at hc hd
    have := Allowable.toStructPerm_comp
      (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from P.B.cons (coe_lt P.hδ))
      (convertAllowable hσS hσT hS hT)
    dsimp only at this
    simp only [OrdSupport.comp_lt, OrdSupport.before_lt, OrdSupport.lt_iff_smul, inv_inv,
      Allowable.smul_supportCondition, this, Tree.comp_apply, hc.2, hd.2,
      convertCondition_mk hσS hσT hS hT ((P.B.cons (coe_lt P.hδ)).comp c.val.path),
      convertCondition_mk hσS hσT hS hT ((P.B.cons (coe_lt P.hδ)).comp d.val.path),
      Subtype.coe_eta, convertCondition_lt]

theorem spec_inflexibleBot (A : ExtendedIndex β) (L : Litter) (hL : InflexibleBot A L)
    (haS : ⟨hL.path.B.cons (bot_lt_coe _), inl hL.a⟩ ∈ S) (hLS₁ : ⟨A, inr L.toNearLitter⟩ ∈ S)
    (hLS₂ : σ.cond (typein S.r ⟨_, hLS₁⟩) (typein_lt hσS) =
      SpecCondition.inflexibleBot A hL.path (typein S.r ⟨_, haS⟩)) :
    ∃ hL' : InflexibleBot A (convertLitter hσS hσT hT A L hLS₁),
    ∃ haT : ⟨hL'.path.B.cons (bot_lt_coe _), inl hL'.a⟩ ∈ T,
      hL.path = hL'.path ∧ typein S.r ⟨_, haS⟩ = typein T.r ⟨_, haT⟩ := by
  obtain (hL' | ⟨⟨hL'⟩⟩ | ⟨⟨hL'⟩⟩) := flexible_cases' β A (convertLitter hσS hσT hT A L hLS₁)
  · have := hσT.flexible_spec A
      (convertLitter hσS hσT hT A L hLS₁).toNearLitter
      (convertLitter_mem hσS hσT hT A L hLS₁) hL'
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter] at this
    rw [hLS₂] at this
    cases this
  · obtain ⟨_, this⟩ := hσT.inflexibleBot_spec A
      (convertLitter hσS hσT hT A L hLS₁).toNearLitter
      (convertLitter_mem hσS hσT hT A L hLS₁) hL'
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter] at this
    rw [hLS₂] at this
    exact ⟨hL', _, SpecCondition.inflexibleBot_injective this⟩
  · obtain ⟨_, _, _, _, this⟩ := hσT.inflexibleCoe_spec A
      (convertLitter hσS hσT hT A L hLS₁).toNearLitter
      (convertLitter_mem hσS hσT hT A L hLS₁) hL'
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter] at this
    rw [hLS₂] at this
    cases this

theorem spec_inflexibleBot_inv (A : ExtendedIndex β) (L : Litter) (hL : InflexibleBot A L)
    (haT : ⟨hL.path.B.cons (bot_lt_coe _), inl hL.a⟩ ∈ T) (hLT₁ : ⟨A, inr L.toNearLitter⟩ ∈ T)
    (hLT₂ : σ.cond (typein T.r ⟨_, hLT₁⟩) (typein_lt hσT) =
      SpecCondition.inflexibleBot A hL.path (typein T.r ⟨_, haT⟩)) :
    ∃ hL' : InflexibleBot A (convertLitter hσT hσS hS A L hLT₁),
    ∃ haS : ⟨hL'.path.B.cons (bot_lt_coe _), inl hL'.a⟩ ∈ S,
      hL.path = hL'.path ∧ typein T.r ⟨_, haT⟩ = typein S.r ⟨_, haS⟩ := by
  obtain (hL' | ⟨⟨hL'⟩⟩ | ⟨⟨hL'⟩⟩) := flexible_cases' β A (convertLitter hσT hσS hS A L hLT₁)
  · have := hσS.flexible_spec A
      (convertLitter hσT hσS hS A L hLT₁).toNearLitter
      (convertLitter_mem hσT hσS hS A L hLT₁) hL'
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter] at this
    rw [hLT₂] at this
    cases this
  · obtain ⟨_, this⟩ := hσS.inflexibleBot_spec A
      (convertLitter hσT hσS hS A L hLT₁).toNearLitter
      (convertLitter_mem hσT hσS hS A L hLT₁) hL'
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter] at this
    rw [hLT₂] at this
    exact ⟨hL', _, SpecCondition.inflexibleBot_injective this⟩
  · obtain ⟨_, _, _, _, this⟩ := hσS.inflexibleCoe_spec A
      (convertLitter hσT hσS hS A L hLT₁).toNearLitter
      (convertLitter_mem hσT hσS hS A L hLT₁) hL'
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter] at this
    rw [hLT₂] at this
    cases this

theorem spec_inflexibleCoe (A : ExtendedIndex β) (L : Litter) (hL : InflexibleCoe A L)
    (χ : CodingFunction hL.path.δ) (hχ : χ.Strong)
    (hLS₁ : ⟨A, inr L.toNearLitter⟩ ∈ S)
    (hLS₂ : σ.cond (typein S.r ⟨_, hLS₁⟩) (typein_lt hσS) =
      SpecCondition.inflexibleCoe A hL.path χ hχ) :
    ∃ hL' : InflexibleCoe A (convertLitter hσS hσT hT A L hLS₁),
    ∃ hχT : (T.before (typein S.r ⟨_, hLS₁⟩)).comp hL.path.δ (hL.path.B.cons hL.path.hδ) ∈ χ,
    hL.path = hL'.path ∧ HEq ((χ.decode _).get hχT) hL'.t := by
  obtain (hL' | ⟨⟨hL'⟩⟩ | ⟨⟨hL'⟩⟩) := flexible_cases' β A (convertLitter hσS hσT hT A L hLS₁)
  · have := hσT.flexible_spec A
      (convertLitter hσS hσT hT A L hLS₁).toNearLitter
      (convertLitter_mem hσS hσT hT A L hLS₁) hL'
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter] at this
    rw [hLS₂] at this
    cases this
  · obtain ⟨_, this⟩ := hσT.inflexibleBot_spec A
      (convertLitter hσS hσT hT A L hLS₁).toNearLitter
      (convertLitter_mem hσS hσT hT A L hLS₁) hL'
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter] at this
    rw [hLS₂] at this
    cases this
  · obtain ⟨χ, hχ₁, hχ₂, hχ₃, this⟩ := hσT.inflexibleCoe_spec A
      (convertLitter hσS hσT hT A L hLS₁).toNearLitter
      (convertLitter_mem hσS hσT hT A L hLS₁) hL'
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter] at this
    rw [hLS₂] at this
    refine ⟨hL', ?_⟩
    obtain ⟨P, t, hL⟩ := hL
    obtain ⟨P', t', hL'⟩ := hL'
    cases SpecCondition.inflexibleCoe_injective₁ this
    cases SpecCondition.inflexibleCoe_injective₂ this
    simp only [Litter.toNearLitter_fst, OrdSupport.coe_sort_coe, typein_convertLitter] at hχ₂ hχ₃
    exact ⟨hχ₂, rfl, heq_of_eq hχ₃⟩

theorem spec_inflexibleCoe_inv (A : ExtendedIndex β) (L : Litter) (hL : InflexibleCoe A L)
    (χ : CodingFunction hL.path.δ) (hχ : χ.Strong)
    (hLT₁ : ⟨A, inr L.toNearLitter⟩ ∈ T)
    (hLT₂ : σ.cond (typein T.r ⟨_, hLT₁⟩) (typein_lt hσT) =
      SpecCondition.inflexibleCoe A hL.path χ hχ) :
    ∃ hL' : InflexibleCoe A (convertLitter hσT hσS hS A L hLT₁),
    ∃ hχS : (S.before (typein T.r ⟨_, hLT₁⟩)).comp hL.path.δ (hL.path.B.cons hL.path.hδ) ∈ χ,
    hL.path = hL'.path ∧ HEq ((χ.decode _).get hχS) hL'.t := by
  obtain (hL' | ⟨⟨hL'⟩⟩ | ⟨⟨hL'⟩⟩) := flexible_cases' β A (convertLitter hσT hσS hS A L hLT₁)
  · have := hσS.flexible_spec A
      (convertLitter hσT hσS hS A L hLT₁).toNearLitter
      (convertLitter_mem hσT hσS hS A L hLT₁) hL'
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter] at this
    rw [hLT₂] at this
    cases this
  · obtain ⟨_, this⟩ := hσS.inflexibleBot_spec A
      (convertLitter hσT hσS hS A L hLT₁).toNearLitter
      (convertLitter_mem hσT hσS hS A L hLT₁) hL'
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter] at this
    rw [hLT₂] at this
    cases this
  · obtain ⟨χ, hχ₁, hχ₂, hχ₃, this⟩ := hσS.inflexibleCoe_spec A
      (convertLitter hσT hσS hS A L hLT₁).toNearLitter
      (convertLitter_mem hσT hσS hS A L hLT₁) hL'
    simp only [OrdSupport.coe_sort_coe, typein_convertLitter] at this
    rw [hLT₂] at this
    refine ⟨hL', ?_⟩
    obtain ⟨P, t, hL⟩ := hL
    obtain ⟨P', t', hL'⟩ := hL'
    cases SpecCondition.inflexibleCoe_injective₁ this
    cases SpecCondition.inflexibleCoe_injective₂ this
    simp only [Litter.toNearLitter_fst, OrdSupport.coe_sort_coe, typein_convertLitter] at hχ₂ hχ₃
    exact ⟨hχ₂, rfl, heq_of_eq hχ₃⟩

theorem convert_inflexibleBot (A : ExtendedIndex β) (L : Litter) (hL : InflexibleBot A L)
    (haS : ⟨(hL.path.B.cons (bot_lt_coe _)), inl hL.a⟩ ∈ S)
    (hLS : ⟨((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _)),
      inr (fuzz (show ((⊥ : IioBot α) : TypeIndex) ≠ (hL.path.ε : Λ) from bot_ne_coe)
        hL.a).toNearLitter⟩ ∈ S) :
    fuzz (show ((⊥ : IioBot α) : TypeIndex) ≠ (hL.path.ε : Λ) from bot_ne_coe)
      (convertAtom hσS hσT hS hT (hL.path.B.cons (bot_lt_coe _)) hL.a haS) =
    convertLitter hσS hσT hT ((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _))
        (fuzz (show ((⊥ : IioBot α) : TypeIndex) ≠ (hL.path.ε : Λ) from bot_ne_coe) hL.a) hLS := by
  simp_rw [← hL.hL, ← hL.path.hA] at hLS
  have := hσS.inflexibleBot_spec A L.toNearLitter hLS hL
  obtain ⟨h₁, h₂⟩ := this
  obtain ⟨hL', ha', h₁', h₂'⟩ := spec_inflexibleBot hσS hσT hT A L hL haS hLS h₂
  obtain ⟨P, a, hL⟩ := hL
  obtain ⟨P', a', hL'⟩ := hL'
  dsimp only at *
  subst h₁'
  cases convertAtom_eq_of_typein_eq hσS hσT hS hT h₂'
  have := hL'
  simp_rw [P.hA, hL] at this
  rw [this]

theorem convert_inflexibleCoe (A : ExtendedIndex β) (L : Litter) (hL : InflexibleCoe A L)
    (hLS : ⟨((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _)),
      inr (fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε) hL.t).toNearLitter⟩ ∈ S)
    (ih : LawfulBefore hσS hσT hS hT (typein S.r ⟨_, hLS⟩)) :
    fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε)
      (Allowable.comp
        (show Path ((β : IicBot α) : TypeIndex) (hL.path.δ : IicBot α) from
          hL.path.B.cons (coe_lt hL.path.hδ))
        (convertAllowable hσS hσT hS hT) • hL.t) =
    convertLitter hσS hσT hT ((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _))
      (fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε) hL.t) hLS := by
  simp_rw [← hL.hL, ← hL.path.hA] at hLS ih
  obtain ⟨χ, hχ₁, hχ₂, hχ₃, h⟩ := hσS.inflexibleCoe_spec A L.toNearLitter hLS hL
  obtain ⟨hL', hχT, h₁, h₂⟩ := spec_inflexibleCoe hσS hσT hT A L hL χ hχ₁ hLS h
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
      (convertAllowable hσS hσT hS hT)⁻¹) hχT (CodingFunction.smul_mem _ hχT)
  rw [← inv_smul_eq_iff] at this
  refine Eq.trans ?_ this
  clear this
  simp only [map_inv, inv_inv, smul_left_cancel_iff]
  refine Eq.trans hχ₃.symm (CodingFunction.decode_congr ?_)
  exact before_smul_eq_before hσS hσT hS hT A _ P ih

theorem convert_inflexibleCoe_inv (A : ExtendedIndex β) (L : Litter) (hL : InflexibleCoe A L)
    (hLT : ⟨((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _)),
      inr (fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε) hL.t).toNearLitter⟩ ∈ T)
    (ih : LawfulBefore hσS hσT hS hT (typein T.r ⟨_, hLT⟩)) :
    fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε)
      (Allowable.comp
        (show Path ((β : IicBot α) : TypeIndex) (hL.path.δ : IicBot α) from
          hL.path.B.cons (coe_lt hL.path.hδ))
        (convertAllowable hσS hσT hS hT)⁻¹ • hL.t) =
    convertLitter hσT hσS hS ((hL.path.B.cons (coe_lt hL.path.hε)).cons (bot_lt_coe _))
      (fuzz (coe_ne_coe.mpr <| coe_ne' hL.path.hδε) hL.t) hLT := by
  simp_rw [← hL.hL, ← hL.path.hA] at hLT ih
  obtain ⟨χ, hχ₁, hχ₂, hχ₃, h⟩ := hσT.inflexibleCoe_spec A L.toNearLitter hLT hL
  obtain ⟨hL', hχT, h₁, h₂⟩ := spec_inflexibleCoe hσT hσS hS A L hL χ hχ₁ hLT h
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
      (convertAllowable hσS hσT hS hT)) hχT (CodingFunction.smul_mem _ hχT)
  rw [← inv_smul_eq_iff] at this
  refine Eq.trans ?_ this
  clear this
  simp only [map_inv, inv_inv, smul_left_cancel_iff]
  refine Eq.trans hχ₃.symm (CodingFunction.decode_congr ?_)
  have := before_smul_eq_before hσS hσT hS hT A _ P ih
  rw [this]
  simp only [OrdSupport.coe_sort_coe]
  -- TODO: Tidy this up
  have := @smul_inv_smul _ _ _ ?_ (Allowable.comp
      (show Path ((β : IicBot α) : TypeIndex) (P.δ : IicBot α) from
        P.B.cons (coe_lt P.hδ))
      (convertAllowable hσS hσT hS hT))
    (((T.before (typein T.r ⟨_, hLT⟩)).comp P.δ (P.B.cons (coe_lt P.hδ))))
  swap
  · show MulAction (Allowable (P.δ : Iic α)) (OrdSupport _)
    infer_instance
  simp_rw [← hL, ← P.hA] at this
  convert this.symm

theorem smul_atom_eq (A : ExtendedIndex β) (a : Atom) (hc : ⟨A, inl a⟩ ∈ S) :
    Allowable.toStructPerm (convertAllowable hσS hσT hS hT) A • a =
    convertAtom hσS hσT hS hT A a hc := by
  rw [← (convertAllowable_spec hσS hσT hS hT A).map_atom a, StructAction.rc_smul_atom_eq]
  rfl
  exact Or.inl (Or.inl (Or.inl (Or.inl hc)))

theorem inv_smul_atom_eq (A : ExtendedIndex β) (a : Atom) (hc : ⟨A, inl a⟩ ∈ T) :
    (Allowable.toStructPerm (convertAllowable hσS hσT hS hT) A)⁻¹ • a =
    convertAtom hσT hσS hT hS A a hc :=
  by rw [inv_smul_eq_iff, smul_atom_eq hσS hσT hS hT A, convertAtom_convertAtom]

theorem smul_litter_eq_of_lawfulBefore' (A : ExtendedIndex β) (L : Litter)
    (hc : ⟨A, inr L.toNearLitter⟩ ∈ S) (ih : LawfulBefore hσS hσT hS hT (typein S.r ⟨_, hc⟩)) :
    Allowable.toStructPerm (convertAllowable hσS hσT hS hT) A • L =
    convertLitter hσS hσT hT A L hc := by
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A L
  · rw [← (convertAllowable_spec hσS hσT hS hT A).map_litter L (Or.inl (Or.inl ⟨hc, hL⟩)),
      StructAction.rc_smul_litter_eq,
      NearLitterAction.flexibleLitterLocalPerm_apply_eq _ hc hL,
      NearLitterAction.roughLitterMapOrElse_of_dom]
    rfl
  · simp_rw [hL.hL, hL.path.hA]
    have ha : ⟨hL.path.B.cons _, inl hL.a⟩ ∈ S
    · simp_rw [hL.hL, hL.path.hA] at hc
      exact hS.transConstrains_mem _ ⟨_, hc⟩ (Reduced.mkAtom _)
        (Relation.TransGen.single <| Constrains.fuzz_bot hL.path.hε hL.path.B hL.a)
    rw [toStructPerm_smul_fuzz β hL.path.γ ⊥ hL.path.ε]
    swap
    · exact bot_lt_coe _
    swap
    · intro h
      simp only [IioBot.bot_ne_mk_coe] at h
    rw [← convert_inflexibleBot hσS hσT hS hT A L hL ha]
    have := ih.smul_eq ⟨_, ha⟩ ?_
    · rw [convertCondition_eq_convertAtom hσS hσT hS hT, Allowable.smul_supportCondition] at this
      simp only [smul_inl, SupportCondition.mk.injEq, inl.injEq, true_and] at this
      rw [← this, Allowable.comp_bot (show Path ((β : IicBot α) : TypeIndex) (⊥ : IicBot α) from
          hL.path.B.cons (bot_lt_coe _))]
    · simp only [OrdSupport.coe_sort_coe, mem_setOf_eq, typein_lt_typein, hL.hL, hL.path.hA]
      exact hS.lt_of_transConstrains _ _
        (Relation.TransGen.single (Constrains.fuzz_bot hL.path.hε hL.path.B hL.a))
  · simp_rw [hL.hL, hL.path.hA]
    rw [toStructPerm_smul_fuzz β hL.path.γ hL.path.δ hL.path.ε]
    swap
    · exact coe_lt_coe.mpr hL.path.hδ
    swap
    · intro h
      simp only [Subtype.mk.injEq, coe_inj] at h
      exact coe_ne' hL.path.hδε h
    simp_rw [hL.hL, hL.path.hA] at hc ih
    exact convert_inflexibleCoe hσS hσT hS hT A L hL hc ih

theorem smul_litter_eq_of_lawfulBefore (A : ExtendedIndex β) (L : Litter)
    (hc : ⟨A, inr L.toNearLitter⟩ ∈ S) (ih : LawfulBefore hσS hσT hS hT (typein S.r ⟨_, hc⟩)) :
    Allowable.toStructPerm (convertAllowable hσS hσT hS hT) A • L.toNearLitter =
    (convertLitter hσS hσT hT A L hc).toNearLitter :=
  StructAction.smul_toNearLitter_eq_of_precise _ StructAction.refine_precise
    (convertAllowable_spec hσS hσT hS hT) hc
    (smul_litter_eq_of_lawfulBefore' hσS hσT hS hT A L hc ih)

theorem inv_smul_litter_eq_of_lawfulBefore' (A : ExtendedIndex β) (L : Litter)
    (hc : ⟨A, inr L.toNearLitter⟩ ∈ T) (ih : LawfulBefore hσS hσT hS hT (typein T.r ⟨_, hc⟩)) :
    (Allowable.toStructPerm (convertAllowable hσS hσT hS hT) A)⁻¹ • L =
    convertLitter hσT hσS hS A L hc := by
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A L
  · rw [inv_smul_eq_iff,
        ← (convertAllowable_spec hσS hσT hS hT A).map_litter _ (Or.inl (Or.inl ?_)),
        StructAction.rc_smul_litter_eq,
        NearLitterAction.flexibleLitterLocalPerm_apply_eq,
        NearLitterAction.roughLitterMapOrElse_of_dom]
    · simp only [StructAction.refine_apply, NearLitterAction.refine_litterMap, convert_litterMap,
        convertLitter_convertLitter, Litter.toNearLitter_fst]
    · exact convertLitter_mem hσT hσS hS A L _
    · exact convertLitter_mem hσT hσS hS A L _
    · exact convert_mapFlexible hσT hσS hT hS A L _ hL
    · exact ⟨convertLitter_mem hσT hσS hS A L _, convert_mapFlexible hσT hσS hT hS A L _ hL⟩
  · simp_rw [hL.hL, hL.path.hA]
    have ha : ⟨hL.path.B.cons _, inl hL.a⟩ ∈ T
    · simp_rw [hL.hL, hL.path.hA] at hc
      exact hT.transConstrains_mem _ ⟨_, hc⟩ (Reduced.mkAtom _)
        (Relation.TransGen.single <| Constrains.fuzz_bot hL.path.hε hL.path.B hL.a)
    rw [← Tree.inv_apply, ← map_inv]
    rw [toStructPerm_smul_fuzz β hL.path.γ ⊥ hL.path.ε]
    swap
    · exact bot_lt_coe _
    swap
    · intro h
      simp only [IioBot.bot_ne_mk_coe] at h
    rw [← convert_inflexibleBot hσT hσS hT hS A L hL ha]
    have := ih.inv_smul_eq ⟨_, ha⟩ ?_
    · rw [inv_smul_eq_iff,
        convertCondition_eq_convertAtom hσT hσS hT hS, Allowable.smul_supportCondition] at this
      simp only [smul_inl, SupportCondition.mk.injEq, inl.injEq, true_and] at this
      rw [← inv_smul_eq_iff] at this
      rw [← this, Allowable.comp_bot (show Path ((β : IicBot α) : TypeIndex) (⊥ : IicBot α) from
          hL.path.B.cons (bot_lt_coe _)), map_inv, Tree.inv_apply]
    · simp only [OrdSupport.coe_sort_coe, mem_setOf_eq, typein_lt_typein, hL.hL, hL.path.hA]
      exact hT.lt_of_transConstrains _ _
        (Relation.TransGen.single <| Constrains.fuzz_bot hL.path.hε hL.path.B hL.a)
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
    exact convert_inflexibleCoe_inv hσS hσT hS hT A L hL hc ih

theorem inv_smul_litter_eq_of_lawfulBefore (A : ExtendedIndex β) (L : Litter)
    (hc : ⟨A, inr L.toNearLitter⟩ ∈ T) (ih : LawfulBefore hσS hσT hS hT (typein T.r ⟨_, hc⟩)) :
    (Allowable.toStructPerm (convertAllowable hσS hσT hS hT) A)⁻¹ • L.toNearLitter =
    (convertLitter hσT hσS hS A L hc).toNearLitter := by
  have := inv_smul_litter_eq_of_lawfulBefore' hσS hσT hS hT A L hc ih
  rw [inv_smul_eq_iff] at this ⊢
  rw [StructAction.smul_toNearLitter_eq_of_precise _ StructAction.refine_precise
      (convertAllowable_spec hσS hσT hS hT) ?_
      (this.symm.trans ?_)]
  · simp only [StructAction.refine_apply, NearLitterAction.refine_litterMap, convert_litterMap,
    convertLitter_convertLitter]
  · exact convertLitter_mem hσT hσS hS _ _ _
  · simp only [StructAction.refine_apply, NearLitterAction.refine_litterMap, convert_litterMap,
    convertLitter_convertLitter, Litter.toNearLitter_fst]

theorem lawfulIn_step (i : Ordinal) (ih : LawfulBefore hσS hσT hS hT i) :
    LawfulIn hσS hσT hS hT {i} := by
  constructor
  case smul_eq =>
    rintro ⟨⟨A, a | N⟩, hc⟩ rfl
    · simp_rw [convertCondition_eq_convertAtom hσS hσT hS hT, ← smul_atom_eq hσS hσT hS hT A a hc]
      rfl
    · obtain ⟨L, rfl⟩ := (isLitter_of_reduced (hS.reduced_of_mem ⟨_, hc⟩)).exists_litter_eq
      simp_rw [convertCondition_eq_convertLitter hσS hσT hT,
        ← smul_litter_eq_of_lawfulBefore hσS hσT hS hT A L hc ih]
      rfl
  case inv_smul_eq =>
    rintro ⟨⟨A, a | N⟩, hc⟩ rfl
    · simp_rw [convertCondition_eq_convertAtom hσT hσS hT hS,
        ← inv_smul_atom_eq hσS hσT hS hT A a hc]
      simp only [Allowable.smul_supportCondition, smul_inl, map_inv, Tree.inv_apply]
    · obtain ⟨L, rfl⟩ := (isLitter_of_reduced (hT.reduced_of_mem ⟨_, hc⟩)).exists_litter_eq
      simp_rw [convertCondition_eq_convertLitter hσT hσS hS,
        ← inv_smul_litter_eq_of_lawfulBefore hσS hσT hS hT A L hc ih]
      simp only [Allowable.smul_supportCondition, smul_inr, map_inv, Tree.inv_apply]

theorem lawfulIn_all : LawfulIn hσS hσT hS hT univ :=
  lawfulBefore_induction hσS hσT hS hT (lawfulIn_step hσS hσT hS hT)

theorem convertAllowable_smul : convertAllowable hσS hσT hS hT • S = T := by
  refine OrdSupport.ext ?_ ?_ ?_
  · intro c hc
    have := (lawfulIn_all hσS hσT hS hT).smul_mem ⟨_, hc⟩ (mem_univ _)
    rw [smul_inv_smul] at this
    exact this
  · intro c hc
    exact (lawfulIn_all hσS hσT hS hT).inv_smul_mem ⟨_, hc⟩ (mem_univ _)
  · intro c d
    have hc := (lawfulIn_all hσS hσT hS hT).smul_eq ⟨_, c.prop⟩ (mem_univ _)
    have hd := (lawfulIn_all hσS hσT hS hT).smul_eq ⟨_, d.prop⟩ (mem_univ _)
    simp only [smul_inv_smul] at hc hd
    conv_rhs => simp (config := { singlePass := true }) only [hc, hd]
    simp only [OrdSupport.lt_iff_smul, Subtype.coe_eta, convertCondition_lt]

end Spec

end ConNF
