import ConNF.Foa.Basic.Flexible
import ConNF.Counting.CodingFunction

/-!
# Specifications
-/

open Ordinal Quiver Set Sum WithBot

open scoped Classical Cardinal

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

-- TODO: Make `Inflexible*Path` have better names.
inductive SpecCondition (β : Iic α)
  | atom (A : ExtendedIndex β) (i : Ordinal.{u})
  | flexible (A : ExtendedIndex β)
  | inflexibleCoe (A : ExtendedIndex β) (h : InflexibleCoePath A)
      (χ : CodingFunction (h.δ : Iic α)) (hχ : χ.Strong)
  | inflexibleBot (A : ExtendedIndex β) (h : InflexibleBotPath A) (i : Ordinal.{u})

theorem SpecCondition.atom_injective {A : ExtendedIndex β} {i j : Ordinal}
    (h : SpecCondition.atom A i = SpecCondition.atom A j) : i = j := by
  cases h
  rfl

theorem SpecCondition.inflexibleBot_injective {A : ExtendedIndex β} {h₁ h₂ : InflexibleBotPath A}
    {i j : Ordinal} (h : SpecCondition.inflexibleBot A h₁ i = SpecCondition.inflexibleBot A h₂ j) :
    h₁ = h₂ ∧ i = j := by
  cases h
  exact ⟨rfl, rfl⟩

theorem SpecCondition.inflexibleCoe_injective₁ {A : ExtendedIndex β} {h₁ h₂ : InflexibleCoePath A}
    {χ₁ : CodingFunction h₁.δ} {χ₂ : CodingFunction h₂.δ} {hχ₁ : χ₁.Strong} {hχ₂ : χ₂.Strong}
    (h : SpecCondition.inflexibleCoe A h₁ χ₁ hχ₁ = SpecCondition.inflexibleCoe A h₂ χ₂ hχ₂) :
    h₁ = h₂ := by
  cases h
  exact rfl

theorem SpecCondition.inflexibleCoe_injective₂ {A : ExtendedIndex β} {h : InflexibleCoePath A}
    {χ₁ χ₂ : CodingFunction h.δ} {hχ₁ : χ₁.Strong} {hχ₂ : χ₂.Strong}
    (h : SpecCondition.inflexibleCoe A h χ₁ hχ₁ = SpecCondition.inflexibleCoe A h χ₂ hχ₂) :
    χ₁ = χ₂ := by
  cases h
  exact rfl

@[ext]
structure Spec (β : Iic α) where
  orderType : Ordinal.{u}
  cond : (i : Ordinal) → i < orderType → SpecCondition β

namespace Spec

/-- A specification `σ` specifies an ordered support `S` if each support condition in `S` is
described in a sensible way by `σ`. -/
structure Specifies (σ : Spec β) (S : OrdSupport β) : Prop where
  lt_orderType (c : S) : typein S.r c < σ.orderType
  of_lt_orderType (i : Ordinal) : i < σ.orderType → ∃ c : S, i = typein S.r c
  atom_dom (A : ExtendedIndex β) (a : Atom) (ha : ⟨A, inl a⟩ ∈ S) :
    ∃ N : NearLitter, a ∈ N ∧ ⟨A, inr N⟩ ∈ S
  atom_spec (A : ExtendedIndex β) (a : Atom) (N : NearLitter)
    (ha : ⟨A, inl a⟩ ∈ S) (hN : ⟨A, inr N⟩ ∈ S) : a ∈ N →
    σ.cond (typein S.r ⟨_, ha⟩) (lt_orderType ⟨_, ha⟩) =
    SpecCondition.atom A (typein S.r ⟨_, hN⟩)
  flexible_spec (A : ExtendedIndex β) (N : NearLitter) (hN : ⟨A, inr N⟩ ∈ S) : Flexible α A N.fst →
    σ.cond (typein S.r ⟨_, hN⟩) (lt_orderType ⟨_, hN⟩) = SpecCondition.flexible A
  inflexibleCoe_spec (A : ExtendedIndex β) (N : NearLitter) (hN : ⟨A, inr N⟩ ∈ S)
    (h : InflexibleCoe A N.1) :
    ∃ χ : CodingFunction h.path.δ,
    ∃ hχ : χ.Strong,
    ∃ h' : (S.before (typein S.r ⟨_, hN⟩)).comp h.path.δ (h.path.B.cons h.path.hδ) ∈ χ,
    (χ.decode _).get h' = h.t ∧
    σ.cond (typein S.r ⟨_, hN⟩) (lt_orderType ⟨_, hN⟩) =
    SpecCondition.inflexibleCoe A h.path χ hχ
  inflexibleBot_spec (A : ExtendedIndex β) (N : NearLitter) (hN : ⟨A, inr N⟩ ∈ S)
    (h : InflexibleBot A N.1) :
    ∃ ha : ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩ ∈ S,
    σ.cond (typein S.r ⟨_, hN⟩) (lt_orderType ⟨_, hN⟩) =
    SpecCondition.inflexibleBot A h.path (typein S.r ⟨_, ha⟩)

theorem orderType_eq_of_specifies {σ : Spec β} {S : OrdSupport β} (hσS : σ.Specifies S) :
    σ.orderType = type S.r := by
  obtain (h | h | h) := lt_trichotomy σ.orderType (type S.r)
  · exfalso
    obtain ⟨c, hc⟩ := typein_surj S.r h
    exact (hσS.lt_orderType c).ne hc
  · exact h
  · exfalso
    obtain ⟨c, hc⟩ := hσS.of_lt_orderType _ h
    exact (typein_lt_type S.r c).ne hc.symm

theorem specifies_subsingleton (S : OrdSupport β) :
    {σ | Specifies σ S}.Subsingleton := by
  rintro ⟨o, c₁⟩ h₁ ⟨_, c₂⟩ h₂
  cases (orderType_eq_of_specifies h₂).trans (orderType_eq_of_specifies h₁).symm
  refine Spec.ext _ _ rfl (heq_of_eq ?_)
  dsimp only
  funext i hi
  obtain ⟨⟨c, hc⟩, rfl⟩ := h₁.of_lt_orderType i hi
  obtain ⟨A, a | N⟩ := c
  · obtain ⟨N, hN₁, hN₂⟩ := h₁.atom_dom A a hc
    exact (h₁.atom_spec A a N hc hN₂ hN₁).trans (h₂.atom_spec A a N hc hN₂ hN₁).symm
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A N.1
  · exact (h₁.flexible_spec A N hc hL).trans (h₂.flexible_spec A N hc hL).symm
  · obtain ⟨ha₁, ha₁'⟩ := h₁.inflexibleBot_spec A N hc hL
    obtain ⟨ha₂, ha₂'⟩ := h₂.inflexibleBot_spec A N hc hL
    exact ha₁'.trans ha₂'.symm
  · obtain ⟨χ₁, hχ₁, hχ₁', ht₁, h₁'⟩ := h₁.inflexibleCoe_spec A N hc hL
    obtain ⟨χ₂, hχ₂, hχ₂', ht₂, h₂'⟩ := h₂.inflexibleCoe_spec A N hc hL
    suffices : χ₁ = χ₂
    · subst this
      exact h₁'.trans h₂'.symm
    refine CodingFunction.ext _ hχ₁' hχ₂' ?_
    rw [ht₁, ht₂]

theorem before_comp_supports {S : OrdSupport β} (hS : S.Strong)
    {A : ExtendedIndex β} {N : NearLitter} (h : InflexibleCoe A N.1) (hN : ⟨A, inr N⟩ ∈ S) :
    MulAction.Supports (Allowable h.path.δ)
      {c | c ∈ (S.before (typein S.r ⟨_, hN⟩)).comp
        h.path.δ (h.path.B.cons h.path.hδ)} h.t := by
  intro ρ hρ
  refine (reducedSupport α h.t).supports ?_ ?_
  intros c hc
  refine hρ ?_
  rw [mem_setOf, OrdSupport.mem_comp (h.path.δ : Iic α), OrdSupport.mem_before]
  refine ⟨?_, ?_⟩
  · refine hS.transConstrains_mem _ ⟨⟨A, inr N⟩, hN⟩ ?_ ?_
    · exact hc.2
    · obtain ⟨d, hd₁, hd₂⟩ := hc.1
      refine Relation.TransGen.trans_right (reflTransConstrains_comp hd₂ _) ?_
      refine transConstrains_nearLitter ?_
      have := Constrains.fuzz h.path.hδ h.path.hε h.path.hδε h.path.B h.t d hd₁
      rw [← h.path.hA, ← h.hL] at this
      exact Relation.TransGen.single this
  · simp only [OrdSupport.coe_sort_coe, typein_lt_typein]
    refine hS.lt_of_transConstrains _ _ ?_
    have := transConstrains_of_mem_reducedSupport α h.path.hδ h.path.hε h.path.hδε h.path.B h.t c hc
    rw [← h.path.hA, ← h.hL] at this
    exact transConstrains_nearLitter this

noncomputable def codeBefore {S : OrdSupport β} (hS : S.Strong)
    {A : ExtendedIndex β} {N : NearLitter} (h : InflexibleCoe A N.1) (hN : ⟨A, inr N⟩ ∈ S) :
    CodingFunction (h.path.δ : Iic α) :=
  CodingFunction.code
    ((S.before (typein S.r ⟨_, hN⟩)).comp h.path.δ (h.path.B.cons h.path.hδ))
    h.t (before_comp_supports hS h hN)

theorem codeBefore_strong {S : OrdSupport β} (hS : S.Strong)
    {A : ExtendedIndex β} {N : NearLitter} (h : InflexibleCoe A N.1) (hN : ⟨A, inr N⟩ ∈ S) :
    (codeBefore hS h hN).Strong :=
  CodingFunction.code_strong ((hS.before _).comp _ _)

noncomputable def specCondition {S : OrdSupport β} (hS : S.Strong) :
    (c : S) → SpecCondition β
  | ⟨⟨A, Sum.inl a⟩, hc⟩ => SpecCondition.atom A
      (typein S.r ⟨⟨A, inr a.1.toNearLitter⟩, hS.transConstrains_mem _ ⟨_, hc⟩
        (Reduced.mkLitter _) (Relation.TransGen.single <| Constrains.atom _ _)⟩)
  | ⟨⟨A, Sum.inr N⟩, hc⟩ =>
      if h : Nonempty (InflexibleCoe A N.1) then
        SpecCondition.inflexibleCoe A h.some.path
          (codeBefore hS h.some hc) (codeBefore_strong hS h.some hc)
      else if h : Nonempty (InflexibleBot A N.1) then
        SpecCondition.inflexibleBot A h.some.path
          (typein S.r ⟨⟨h.some.path.B.cons (bot_lt_coe _), inl h.some.a⟩,
            hS.transConstrains_mem _ ⟨_, hc⟩ (Reduced.mkAtom _)
            (by
              have := Constrains.fuzz_bot h.some.path.hε h.some.path.B h.some.a
              rw [← h.some.path.hA, ← h.some.hL] at this
              exact transConstrains_nearLitter (Relation.TransGen.single this))⟩)
      else
        SpecCondition.flexible A

@[simp]
theorem specCondition_atom {S : OrdSupport β} {hS : S.Strong}
    (A : ExtendedIndex β) (a : Atom) (h : ⟨A, inl a⟩ ∈ S) :
    specCondition hS ⟨⟨A, inl a⟩, h⟩ = SpecCondition.atom A
      (typein S.r ⟨⟨A, inr a.1.toNearLitter⟩, hS.transConstrains_mem _ ⟨_, h⟩
        (Reduced.mkLitter _) (Relation.TransGen.single <| Constrains.atom _ _)⟩) :=
  rfl

theorem specCondition_inflexibleCoe {S : OrdSupport β} {hS : S.Strong}
    (A : ExtendedIndex β) (N : NearLitter) (hNS : ⟨A, inr N⟩ ∈ S) (hN : InflexibleCoe A N.1) :
    specCondition hS ⟨⟨A, inr N⟩, hNS⟩ =
    SpecCondition.inflexibleCoe A hN.path (codeBefore hS hN hNS) (codeBefore_strong hS hN hNS) := by
  rw [specCondition]
  dsimp only
  rw [dif_pos ⟨hN⟩]
  have : hN = Nonempty.some ⟨hN⟩ := Subsingleton.elim _ _
  rw [this]

theorem specCondition_inflexibleBot {S : OrdSupport β} {hS : S.Strong}
    (A : ExtendedIndex β) (N : NearLitter) (hNS : ⟨A, inr N⟩ ∈ S) (hN : InflexibleBot A N.1)
    (ha : ⟨hN.path.B.cons (bot_lt_coe _), inl hN.a⟩ ∈ S) :
    specCondition hS ⟨⟨A, inr N⟩, hNS⟩ =
    SpecCondition.inflexibleBot A hN.path
      (typein S.r ⟨⟨hN.path.B.cons (bot_lt_coe _), inl hN.a⟩, ha⟩) := by
  rw [specCondition]
  dsimp only
  rw [dif_neg, dif_pos ⟨hN⟩]
  · have : hN = Nonempty.some ⟨hN⟩ := Subsingleton.elim _ _
    congr 2
    · rw [this]
    · simp only [OrdSupport.coe_sort_coe, Subtype.mk.injEq, SupportCondition.mk.injEq, inl.injEq]
      rw [this]
      exact ⟨rfl, rfl⟩
  · rintro ⟨hN'⟩
    exact inflexibleBot_inflexibleCoe hN hN'

theorem specCondition_flexible {S : OrdSupport β} {hS : S.Strong}
    (A : ExtendedIndex β) (N : NearLitter) (hNS : ⟨A, inr N⟩ ∈ S) (hN : Flexible α A N.1) :
    specCondition hS ⟨⟨A, inr N⟩, hNS⟩ = SpecCondition.flexible A := by
  rw [specCondition]
  dsimp only
  rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at hN
  rw [dif_neg, dif_neg]
  · exact not_nonempty_iff.mpr hN.1
  · exact not_nonempty_iff.mpr hN.2

/-- The support condition at position `i` in `S`. -/
noncomputable def _root_.ConNF.OrdSupport.conditionAt (S : OrdSupport β)
    (i : Ordinal) (hi : i < type S.r) : S :=
  (typein_surj S.r hi).choose

@[simp]
theorem typein_conditionAt (S : OrdSupport β) (i : Ordinal) (hi : i < type S.r) :
    typein S.r (S.conditionAt i hi) = i :=
  (typein_surj S.r hi).choose_spec

@[simp]
theorem conditionAt_typein (S : OrdSupport β) (c : S) :
    S.conditionAt (typein S.r c) (typein_lt_type S.r c) = c := by
  refine typein_injective S.r ?_
  rw [typein_conditionAt]

noncomputable def spec (S : OrdSupport β) (hS : S.Strong) : Spec β where
  orderType := type S.r
  cond i hi := specCondition hS (S.conditionAt i hi)

@[simp]
theorem spec_orderType {S : OrdSupport β} {hS : S.Strong} :
    (spec S hS).orderType = type S.r :=
  rfl

@[simp]
theorem spec_cond_eq {S : OrdSupport β} {hS : S.Strong}
    (i : Ordinal) (hi : i < type S.r) :
    (spec S hS).cond i hi = specCondition hS (S.conditionAt i hi) :=
  rfl

/-- Every strong support has a specification, described by `spec`. -/
theorem spec_specifies {S : OrdSupport β} (hS : S.Strong) :
    (spec S hS).Specifies S := by
  constructor
  case lt_orderType =>
    intro c
    simp only [OrdSupport.coe_sort_coe, spec_orderType]
    exact typein_lt_type S.r c
  case of_lt_orderType =>
    intro i hi
    simp only [OrdSupport.coe_sort_coe, Subtype.exists]
    obtain ⟨c, hc⟩ := typein_surj S.r hi
    exact ⟨c, c.prop, hc.symm⟩
  case atom_dom =>
    intro A a ha
    refine ⟨a.1.toNearLitter, rfl, ?_⟩
    refine hS.transConstrains_mem _ ⟨_, ha⟩ (Reduced.mkLitter _) ?_
    exact Relation.TransGen.single (Constrains.atom _ _)
  case atom_spec =>
    intro A a N ha hN haN
    simp only [OrdSupport.coe_sort_coe, spec_cond_eq, conditionAt_typein, specCondition_atom,
      SpecCondition.atom.injEq, typein_inj, Subtype.mk.injEq, SupportCondition.mk.injEq,
      inr.injEq, true_and]
    have := hS.reduced_of_mem ⟨_, hN⟩
    cases this
    cases haN
    rfl
  case flexible_spec =>
    intro A N hN₁ hN₂
    simp only [OrdSupport.coe_sort_coe, spec_cond_eq, conditionAt_typein]
    rw [specCondition_flexible A N hN₁ hN₂]
  case inflexibleCoe_spec =>
    intro A N hN₁ hN₂
    refine ⟨codeBefore hS hN₂ hN₁, codeBefore_strong hS hN₂ hN₁, ?_, ?_, ?_⟩
    · rw [codeBefore]
      exact CodingFunction.mem_code_self
    · simp only [codeBefore, CodingFunction.code_decode, Part.get_some]
    · simp only [OrdSupport.coe_sort_coe, spec_cond_eq, conditionAt_typein]
      rw [specCondition_inflexibleCoe A N hN₁ hN₂]
  case inflexibleBot_spec =>
    intro A N hN₁ hN₂
    refine ⟨?_, ?_⟩
    · refine hS.transConstrains_mem _ ⟨_, hN₁⟩ (Reduced.mkAtom _) ?_
      have := Constrains.fuzz_bot hN₂.path.hε hN₂.path.B hN₂.a
      rw [← hN₂.hL, ← hN₂.path.hA] at this
      exact transConstrains_nearLitter (Relation.TransGen.single this)
    · simp only [OrdSupport.coe_sort_coe, spec_cond_eq, conditionAt_typein]
      rw [specCondition_inflexibleBot A N hN₁ hN₂]

/-- A specification is *strong* if it specifies a strong support. -/
def Strong (σ : Spec β) : Prop :=
  ∃ S : OrdSupport β, S.Strong ∧ σ.Specifies S

/-- A strong support specified by this strong specification. -/
noncomputable def Strong.out {σ : Spec β} (h : σ.Strong) : OrdSupport β :=
  h.choose

theorem Strong.out_strong {σ : Spec β} (h : σ.Strong) : h.out.Strong :=
  h.choose_spec.1

theorem Strong.specifies_out {σ : Spec β} (h : σ.Strong) : σ.Specifies h.out :=
  h.choose_spec.2

end Spec

end ConNF
