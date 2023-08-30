import ConNF.Fuzz
import ConNF.Foa.Basic.Hypotheses

/-!
# Constraints
Support conditions can be said to *constrain* each other in a number of ways.
This is detailed below. The `constrains` relation is well-founded.
-/

open Quiver Set Sum WithBot

open scoped Cardinal Classical

universe u

namespace ConNF

variable [Params.{u}]

section ExtendedIndex

variable {α : TypeIndex} [BasePositions]

/-!
We construct a well-order on the type of extended indices.
The details are unimportant, we probably don't actually need AC here.
-/

instance : LT (ExtendedIndex α) :=
  ⟨WellOrderingRel⟩

instance : IsWellOrder (ExtendedIndex α) (· < ·) :=
  WellOrderingRel.isWellOrder

instance : WellFoundedRelation (ExtendedIndex α) :=
  IsWellOrder.toHasWellFounded

noncomputable instance : LinearOrder (ExtendedIndex α) :=
  linearOrderOfSTO (· < ·)

def sumAtomNearLitterMap : Atom ⊕ NearLitter → μ
| inl a => typedAtomPosition a
| inr N => typedNearLitterPosition N

@[simp]
theorem sumAtomNearLitterMap_inl (a : Atom) :
    sumAtomNearLitterMap (inl a) = typedAtomPosition a :=
  rfl

@[simp]
theorem sumAtomNearLitterMap_inr (N : NearLitter) :
    sumAtomNearLitterMap (inr N) = typedNearLitterPosition N :=
  rfl

theorem sumAtomNearLitterMap_injective : Function.Injective sumAtomNearLitterMap := by
  rintro (a₁ | N₁) (a₂ | N₂) h
  · exact congr_arg _ (typedAtomPosition.injective h)
  · cases typedAtomPosition_ne_typedNearLitterPosition a₁ N₂ h
  · cases typedAtomPosition_ne_typedNearLitterPosition a₂ N₁ h.symm
  · exact congr_arg _ (typedNearLitterPosition.injective h)

-- TODO: Move and use
theorem isWellOrder_invImage {α β : Type _} {r : β → β → Prop} (h : IsWellOrder β r)
    (f : α → β) (hf : Function.Injective f) :
    IsWellOrder α (InvImage r f) where
  trichotomous := by
    intro x y
    have := h.trichotomous (f x) (f y)
    rw [hf.eq_iff] at this
    exact this
  trans x y z := h.trans (f x) (f y) (f z)
  wf := InvImage.wf _ h.wf

instance : LT (Atom ⊕ NearLitter) :=
  ⟨InvImage (· < ·) sumAtomNearLitterMap⟩

theorem sumAtomNearLitter_lt_def (x y : Atom ⊕ NearLitter) :
    x < y ↔ sumAtomNearLitterMap x < sumAtomNearLitterMap y :=
  Iff.rfl

instance : IsWellOrder (Atom ⊕ NearLitter) (· < ·) :=
  isWellOrder_invImage μwo _ sumAtomNearLitterMap_injective

instance : WellFoundedRelation (Atom ⊕ NearLitter) :=
  IsWellOrder.toHasWellFounded

def ConditionPosition (α : TypeIndex) : Type u :=
  (Atom ⊕ NearLitter) ×ₗ ExtendedIndex α

def SupportCondition.position : SupportCondition α → ConditionPosition α :=
  Prod.swap

theorem SupportCondition.position_injective :
    Function.Injective (SupportCondition.position (α := α)) :=
  Prod.swap_injective

instance : LT (ConditionPosition α) :=
  inferInstanceAs (LT ((Atom ⊕ NearLitter) ×ₗ ExtendedIndex α))

instance : IsWellOrder (ConditionPosition α) (· < ·) :=
  instIsWellOrderProdLex

instance : WellFoundedRelation (ConditionPosition α) :=
  IsWellOrder.toHasWellFounded

attribute [irreducible] ConditionPosition

instance : LT (SupportCondition α) :=
  ⟨InvImage (· < ·) SupportCondition.position⟩

theorem SupportCondition.lt_def (c d : SupportCondition α) :
    c < d ↔ SupportCondition.position c < SupportCondition.position d :=
  Iff.rfl

instance : IsWellOrder (SupportCondition α) (· < ·) :=
  isWellOrder_invImage inferInstance _ SupportCondition.position_injective

instance : WellFoundedRelation (SupportCondition α) :=
  IsWellOrder.toHasWellFounded

end ExtendedIndex

variable {α : Λ} [BasePositions] [Phase2Assumptions α] {β : Λ}

theorem coe_ne' {γ : Iio α} {β : Iio α} : γ ≠ β → (γ : Λ) ≠ (β : Λ) := by
  contrapose!
  simp only [Subtype.coe_inj, imp_self]

-- TODO: Remove?
theorem coe_lt {γ : Iio α} {β : Iic α} : (γ : Λ) < β → (γ : TypeIndex) < (β : TypeIndex) :=
  coe_lt_coe.mpr

variable (α) (β)

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ∈ » «expr ∆ »(litter_set[con_nf.litter_set] N.fst, N.snd)) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (c «expr ∈ » (designated_support[con_nf.designated_support] t).carrier) -/
-- TODO: Swap around argument order to put paths first.
/-- Support conditions can be said to *constrain* each other in a number of ways. This is discussed
in the "freedom of action discussion".
1. `(L, A) ≺ (a, A)` when `a ∈ L` and `L` is a litter. We can say that an atom is constrained by the
    litter it belongs to.
2. `(N°, A) ≺ (N, A)` when `N` is a near-litter not equal to its corresponding litter `N°`.
3. `(a, A) ≺ (N, A)` for all `a ∈ N ∆ N°`.
4. `(x, A ≫ (γ ⟶ δ) ≫ B) ≺ (f_{γ,δ}(t), A ≫ (γ ⟶ ε) ≫ (ε ⟶ ⊥))` for all paths `A : β ⟶ γ` and
    `δ, ε < γ` with `δ ≠ ε`, `t ∈ τ_γ`, where `(x, B)` lies in the designated `δ`-support of `t`.
TODO: Refactor `near_litter` to use `¬N.is_litter`.
-/
@[mk_iff]
inductive Constrains : SupportCondition β → SupportCondition β → Prop
  | atom (a : Atom) (A : ExtendedIndex β) : Constrains (A, inr a.1.toNearLitter) (A, inl a)
  | nearLitter (N : NearLitter) (hN : litterSet N.fst ≠ N.snd) (A : ExtendedIndex β) :
    Constrains (A, inr N.fst.toNearLitter) (A, inr N)
  | symmDiff (N : NearLitter) (a) (_ : a ∈ litterSet N.fst ∆ N.snd) (A : ExtendedIndex β) :
    Constrains (A, inl a) (A, inr N)
  | fuzz ⦃γ : Iic α⦄ ⦃δ : Iio α⦄ ⦃ε : Iio α⦄ (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
    (A : Path (β : TypeIndex) γ) (t : Tangle δ) (c) (_ : c ∈ (designatedSupport t).carrier) :
    Constrains ((A.cons (coe_lt hδ)).comp c.fst, c.snd)
      ((A.cons (coe_lt hε)).cons (bot_lt_coe _),
        inr (fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter)
  | fuzz_bot ⦃γ : Iic α⦄ ⦃ε : Iio α⦄ (hε : (ε : Λ) < γ) (A : Path (β : TypeIndex) γ) (a : Atom) :
    Constrains (A.cons (bot_lt_coe _), inl a)
      ((A.cons (coe_lt hε)).cons (bot_lt_coe _),
        inr (fuzz (show (⊥ : TypeIndex) ≠ (ε : Λ) from bot_ne_coe) a).toNearLitter)

/-! We declare new notation for the "constrains" relation on support conditions. -/

notation:50 c " ≺[" α "] " d:50 => Constrains α _ c d

theorem constrains_subrelation : Subrelation (Constrains α β) (· < ·) := by
  intro c d h
  obtain ⟨a, A⟩ | ⟨N, hN, A⟩ | ⟨N, a, ha, A⟩ | ⟨hδ, hε, hδε, A, t, c, hc⟩ | ⟨hδ, A, a⟩ := h <;> left
  · exact litter_lt a.1 a rfl
  · refine litter_lt_nearLitter N ?_
    contrapose! hN
    rw [← hN]
    rfl
  · exact symmDiff_lt_nearLitter N a ha
  · have := fuzz_position (coe_ne_coe.mpr <| coe_ne' hδε) t ?_ ?_
    rw [PositionedTypedObjects.typedNearLitterPosition_eq] at this
    refine' lt_of_le_of_lt _ this
    convert PositionedTypedObjects.support_le t _ hc
    · funext x
      cases x <;> rfl
    · rfl
  · simp only [InvImage, elim_inr]
    convert typedAtomPosition_lt_fuzz a
    simp only [sumAtomNearLitter_lt_def, sumAtomNearLitterMap_inl, sumAtomNearLitterMap_inr]
    rw [@PositionedTypedObjects.typedNearLitterPosition_eq _ _ _ ?_ ?_ ?_ ?_ _]
    infer_instance

/-- The `≺` relation is well-founded. By the conditions on orderings, if we have `(x, A) ≺ (y, B)`,
then `x < y` in `µ`, under the `typed_near_litter` or `typed_atom` maps. -/
theorem constrains_wf : WellFounded (Constrains α β) :=
  Subrelation.wf (constrains_subrelation α β) IsWellFounded.wf

variable {α}

@[simp]
theorem constrains_atom {c : SupportCondition β} {a : Atom} {A : ExtendedIndex β} :
    c ≺[α] (A, inl a) ↔ c = (A, inr a.1.toNearLitter) := by
  constructor
  · rintro ⟨⟩
    rfl
  · rintro rfl
    exact Constrains.atom a A

/-- The constrains relation is stable under composition of paths. -/
theorem constrains_comp {β γ : Λ} {c d : SupportCondition γ} (h : c ≺[α] d)
    (B : Path (β : TypeIndex) γ) : (B.comp c.fst, c.snd) ≺[α] (B.comp d.fst, d.snd) := by
  obtain ⟨a, A⟩ | ⟨N, hN, A⟩ | ⟨N, a, ha, A⟩ | ⟨hδ, hε, hδε, A, t, c, hc⟩ | ⟨hδ, A, a⟩ := h
  · exact Constrains.atom _ _
  · exact Constrains.nearLitter _ hN _
  · exact Constrains.symmDiff _ _ ha _
  · rw [Path.comp_cons, ← Path.comp_assoc, Path.comp_cons]
    exact Constrains.fuzz hδ hε hδε (B.comp A) t c hc
  · rw [Path.comp_cons]
    exact Constrains.fuzz_bot hδ (B.comp A) a

notation:50 c " <[" α "] " d:50 => Relation.TransGen (Constrains α _) c d

notation:50 c " ≤[" α "] " d:50 => Relation.ReflTransGen (Constrains α _) c d

theorem trans_constrains_wf (α : Λ) [Phase2Assumptions α] (β : Λ) :
    WellFounded fun c d : SupportCondition β => c <[α] d :=
  WellFounded.transGen (constrains_wf α β)

theorem reflTransGen_constrains_comp {β γ : Λ} {c d : SupportCondition γ} (h : c ≤[α] d)
    (B : Path (β : TypeIndex) γ) : (B.comp c.fst, c.snd) ≤[α] (B.comp d.fst, d.snd) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact Relation.ReflTransGen.tail ih (constrains_comp h B)

theorem transGen_constrains_comp {β γ : Λ} {c d : SupportCondition γ} (h : c <[α] d)
    (B : Path (β : TypeIndex) γ) : (B.comp c.fst, c.snd) <[α] (B.comp d.fst, d.snd) := by
  induction h with
  | single h => exact Relation.TransGen.single (constrains_comp h B)
  | tail _ h ih => exact Relation.TransGen.tail ih (constrains_comp h B)

theorem reflTransGen_nearLitter {β : Λ} {N : NearLitter} {B : ExtendedIndex β}
    {c : SupportCondition β} (h : (B, inr N) ≤[α] c) : (B, inr N.1.toNearLitter) ≤[α] c := by
  by_cases h' : N.IsLitter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.ReflTransGen.head (Constrains.nearLitter N (NearLitter.not_isLitter h') B) h

theorem transGen_nearLitter {β : Λ} {N : NearLitter} {B : ExtendedIndex β} {c : SupportCondition β}
    (h : c <[α] (B, inr N.1.toNearLitter)) : c <[α] (B, inr N) := by
  by_cases h' : N.IsLitter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.TransGen.tail h (Constrains.nearLitter N (NearLitter.not_isLitter h') B)

theorem transGen_nearLitter' {β : Λ} {N : NearLitter} {B : ExtendedIndex β}
    {c : SupportCondition β} (h : (B, inr N) <[α] c) : (B, inr N.1.toNearLitter) <[α] c := by
  by_cases h' : N.IsLitter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.TransGen.head (Constrains.nearLitter N (NearLitter.not_isLitter h') B) h

-- TODO: Move
-- TODO: Search for uses of fuzz_β and replace with this lemma.
lemma fuzz_congr_β {β γ β' γ' : Iio α} {hβγ : (β : TypeIndex) ≠ γ} {hβγ' : (β' : TypeIndex) ≠ γ'}
  {t : Tangle β} {t' : Tangle β'}
  (h : fuzz hβγ t = fuzz hβγ' t') :
  β = β' := by
  have h₁ := fuzz_β hβγ t
  have h₂ := fuzz_β hβγ' t'
  rw [← h, h₁] at h₂
  exact Subtype.coe_injective (WithBot.coe_injective h₂)

lemma fuzz_congr_γ {β γ β' γ' : Iio α} {hβγ : (β : TypeIndex) ≠ γ} {hβγ' : (β' : TypeIndex) ≠ γ'}
  {t : Tangle β} {t' : Tangle β'}
  (h : fuzz hβγ t = fuzz hβγ' t') :
  γ = γ' := by
  have h₁ := fuzz_γ hβγ t
  have h₂ := fuzz_γ hβγ' t'
  rw [← h, h₁] at h₂
  exact Subtype.coe_injective h₂

theorem small_constrains {β : Λ} (c : SupportCondition β) : Small {d | d ≺[α] c} := by
  obtain ⟨A, a | N⟩ := c
  · simp only [constrains_atom, setOf_eq_eq_singleton, small_singleton]
  simp_rw [Constrains_iff]
  refine Small.union ?_ (Small.union ?_ (Small.union ?_ (Small.union ?_ ?_))) <;>
    rw [small_setOf]
  · change Small {c | ∃ b B, _ ∧ _ = _}
    simp only [Prod.mk.injEq, false_and, and_false, exists_false, setOf_false, small_empty]
  · change Small {c | ∃ N', _ ∧ ∃ B, _ ∧ _ = _}
    simp only [ne_eq, Prod.mk.injEq, inr.injEq, exists_eq_right_right',
      ← and_assoc, exists_eq_right']
    by_cases litterSet N.fst = N.snd
    · refine small_of_forall_not_mem ?_
      rintro c ⟨N', h₁, A, ⟨rfl, rfl⟩, rfl⟩
      exact h₁ h
    · refine Set.Subsingleton.small ?_
      rintro c ⟨_, _, _, ⟨rfl, rfl⟩, rfl⟩ d ⟨_, _, _, ⟨rfl, rfl⟩, rfl⟩
      rfl
  · change Small {c | ∃ N' a, _ ∧ ∃ B, _ ∧ _ = _}
    simp only [Prod.mk.injEq, inr.injEq, and_assoc, exists_and_right, exists_eq_right']
    convert (show Small (litterSet N.fst ∆ N) from N.2.prop).image
      (f := fun a : Atom => ((A, inl a) : SupportCondition β)) using 1
    ext c : 1
    aesop
  · by_cases
      ∃ (γ : Iic α) (δ : Iio α) (ε : Iio α) (_hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
        (B : Path (β : TypeIndex) γ) (t : Tangle δ),
        N = (fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter ∧
          A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)
    · obtain ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ := h
      refine lt_of_le_of_lt ?_ (designatedSupport t).small
      suffices
        #{a : SupportCondition β |
            ∃ c : designatedSupport t, a = ((B.cons (coe_lt hδ)).comp c.val.fst, c.val.snd)} ≤
          #(designatedSupport t) by
        refine le_trans (Cardinal.mk_subtype_le_of_subset ?_) this
        rintro x ⟨_, _, _, _, _, _, _, _, c, hc, rfl, h⟩
        rw [Prod.mk.injEq] at h
        simp only [inr.injEq, Litter.toNearLitter_injective.eq_iff] at h
        cases fuzz_congr_β h.2
        cases fuzz_congr_γ h.2
        cases fuzz_injective _ h.2
        cases Subtype.coe_inj.mp
          (coe_inj.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons h.1).eq))
        cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons h.1).eq).eq
        exact ⟨⟨c, hc⟩, rfl⟩
      refine ⟨⟨fun a => a.prop.choose, ?_⟩⟩
      intro a b h
      refine Subtype.coe_inj.mp ?_
      rw [a.prop.choose_spec, b.prop.choose_spec]
      simp only [h]
    · refine small_of_forall_not_mem ?_
      rintro x ⟨γ, δ, ε, hδ, hε, hδε, B, t, c, _, rfl, hA⟩
      rw [Prod.mk.injEq] at hA
      simp only [inr.injEq] at hA
      exact h ⟨γ, δ, ε, hδ, hε, hδε, B, t, hA.2, hA.1⟩
  · refine Set.Subsingleton.small ?_
    rintro ⟨c, C⟩ ⟨γ, ε, hε, C', a, hc₁, hc₂⟩ ⟨d, D⟩ ⟨γ, ε, hε, D', b, hd₁, hd₂⟩
    rw [Prod.mk.injEq] at hc₁ hc₂ hd₁ hd₂
    simp only [inr.injEq] at hc₂ hd₂
    rw [hc₁.1, hc₁.2, hd₁.1, hd₁.2]
    rw [hc₂.1, hc₂.2, Litter.toNearLitter_injective.eq_iff] at hd₂
    cases Subtype.coe_inj.mp (coe_inj.mp (Path.obj_eq_of_cons_eq_cons hd₂.1))
    cases Subtype.coe_inj.mp
      (coe_inj.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hd₂.1).eq))
    cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hd₂.1).eq).eq
    rw [(fuzz_injective bot_ne_coe).eq_iff] at hd₂
    cases hd₂.2
    rfl

end ConNF
