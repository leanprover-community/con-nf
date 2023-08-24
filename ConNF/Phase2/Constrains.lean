import ConNF.Phase1.FMap
import ConNF.Phase2.Basic

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

variable {α : TypeIndex}

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

end ExtendedIndex

variable {α : Λ} [PositionData] [Phase2Assumptions α] {β : Λ}

theorem coe_ne' {γ : Iio α} {β : Iio α} : γ ≠ β → (γ : Λ) ≠ (β : Λ) := by
  contrapose!
  simp only [Subtype.coe_inj, imp_self]

-- TODO: Remove?
theorem coe_lt {γ : Iio α} {β : Iic α} : (γ : Λ) < β → (γ : TypeIndex) < (β : TypeIndex) :=
  coe_lt_coe.mpr

variable (α) (β)

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ∈ » «expr ∆ »(litter_set[con_nf.litter_set] N.fst, N.snd)) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (c «expr ∈ » (designated_support[con_nf.designated_support] t).carrier) -/
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
  | atom (a : Atom) (A : ExtendedIndex β) : Constrains (inr a.1.toNearLitter, A) (inl a, A)
  | nearLitter (N : NearLitter) (hN : litterSet N.fst ≠ N.snd) (A : ExtendedIndex β) :
    Constrains (inr N.fst.toNearLitter, A) (inr N, A)
  | symmDiff (N : NearLitter) (a) (_ : a ∈ litterSet N.fst ∆ N.snd) (A : ExtendedIndex β) :
    Constrains (inl a, A) (inr N, A)
  | fMap ⦃γ : Iic α⦄ ⦃δ : Iio α⦄ ⦃ε : Iio α⦄ (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
    (A : Path (β : TypeIndex) γ) (t : Tangle δ) (c) (_ : c ∈ (designatedSupport t).carrier) :
    Constrains (c.fst, (A.cons (coe_lt hδ)).comp c.snd)
      (inr (fMap (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
        (A.cons (coe_lt hε)).cons (bot_lt_coe _))
  | fMap_bot ⦃γ : Iic α⦄ ⦃ε : Iio α⦄ (hε : (ε : Λ) < γ) (A : Path (β : TypeIndex) γ) (a : Atom) :
    Constrains (inl a, A.cons (bot_lt_coe _))
      (inr (fMap (show (⊥ : TypeIndex) ≠ (ε : Λ) from bot_ne_coe) a).toNearLitter,
        (A.cons (coe_lt hε)).cons (bot_lt_coe _))

/-! We declare new notation for the "constrains" relation on support conditions. -/


notation:50 c " ≺[" α "] " d:50 => Constrains α _ c d

instance : LT (SupportCondition β) :=
  ⟨Prod.Lex (InvImage (· < ·) fun c => c.elim typedAtomPosition typedNearLitterPosition) (· < ·)⟩

instance : IsWellFounded (SupportCondition β) (· < ·) :=
  instIsWellFoundedProdLex

theorem constrains_subrelation : Subrelation (Constrains α β) (· < ·) := by
  intro c d h
  obtain ⟨a, A⟩ | ⟨N, hN, A⟩ | ⟨N, a, ha, A⟩ | ⟨hδ, hε, hδε, A, t, c, hc⟩ | ⟨hδ, A, a⟩ := h <;> left
  · exact litter_lt a.1 a rfl
  · refine litter_lt_nearLitter N ?_
    contrapose! hN
    rw [← hN]
    rfl
  · exact symmDiff_lt_nearLitter N a ha
  · have := fMap_position (coe_ne_coe.mpr <| coe_ne' hδε) t ?_ ?_
    rw [TangleData.typedNearLitterPosition_eq] at this
    refine' lt_of_le_of_lt _ this
    convert TangleData.support_le t _ hc
    rfl
  · simp only [InvImage, elim_inr]
    convert typedAtomPosition_lt_fMap a
    refine (@TangleData.typedNearLitterPosition_eq _ _ _ _ _ _ ?_ _).symm
    infer_instance

/-- The `≺` relation is well-founded. By the conditions on orderings, if we have `(x, A) ≺ (y, B)`,
then `x < y` in `µ`, under the `typed_near_litter` or `typed_atom` maps. -/
theorem constrains_wf : WellFounded (Constrains α β) :=
  Subrelation.wf (constrains_subrelation α β) IsWellFounded.wf

variable {α}

@[simp]
theorem constrains_atom {c : SupportCondition β} {a : Atom} {A : ExtendedIndex β} :
    c ≺[α] (inl a, A) ↔ c = (inr a.1.toNearLitter, A) := by
  constructor
  · rintro ⟨⟩
    rfl
  · rintro rfl
    exact Constrains.atom a A

/-- The constrains relation is stable under composition of paths. -/
theorem constrains_comp {β γ : Λ} {c d : SupportCondition γ} (h : c ≺[α] d)
    (B : Path (β : TypeIndex) γ) : (c.fst, B.comp c.snd) ≺[α] (d.fst, B.comp d.snd) := by
  obtain ⟨a, A⟩ | ⟨N, hN, A⟩ | ⟨N, a, ha, A⟩ | ⟨hδ, hε, hδε, A, t, c, hc⟩ | ⟨hδ, A, a⟩ := h
  · exact Constrains.atom _ _
  · exact Constrains.nearLitter _ hN _
  · exact Constrains.symmDiff _ _ ha _
  · rw [Path.comp_cons, ← Path.comp_assoc, Path.comp_cons]
    exact Constrains.fMap hδ hε hδε (B.comp A) t c hc
  · rw [Path.comp_cons]
    exact Constrains.fMap_bot hδ (B.comp A) a

notation:50 c " <[" α "] " d:50 => Relation.TransGen (Constrains α _) c d

notation:50 c " ≤[" α "] " d:50 => Relation.ReflTransGen (Constrains α _) c d

theorem trans_constrains_wf (α : Λ) [Phase2Assumptions α] (β : Λ) :
    WellFounded fun c d : SupportCondition β => c <[α] d :=
  WellFounded.transGen (constrains_wf α β)

theorem reflTransGen_constrains_comp {β γ : Λ} {c d : SupportCondition γ} (h : c ≤[α] d)
    (B : Path (β : TypeIndex) γ) : (c.fst, B.comp c.snd) ≤[α] (d.fst, B.comp d.snd) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact Relation.ReflTransGen.tail ih (constrains_comp h B)

theorem transGen_constrains_comp {β γ : Λ} {c d : SupportCondition γ} (h : c <[α] d)
    (B : Path (β : TypeIndex) γ) : (c.fst, B.comp c.snd) <[α] (d.fst, B.comp d.snd) := by
  induction h with
  | single h => exact Relation.TransGen.single (constrains_comp h B)
  | tail _ h ih => exact Relation.TransGen.tail ih (constrains_comp h B)

theorem reflTransGen_nearLitter {β : Λ} {N : NearLitter} {B : ExtendedIndex β}
    {c : SupportCondition β} (h : (inr N, B) ≤[α] c) : (inr N.1.toNearLitter, B) ≤[α] c := by
  by_cases h' : N.IsLitter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.ReflTransGen.head (Constrains.nearLitter N (NearLitter.not_isLitter h') B) h

theorem transGen_nearLitter {β : Λ} {N : NearLitter} {B : ExtendedIndex β} {c : SupportCondition β}
    (h : c <[α] (inr N.1.toNearLitter, B)) : c <[α] (inr N, B) := by
  by_cases h' : N.IsLitter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.TransGen.tail h (Constrains.nearLitter N (NearLitter.not_isLitter h') B)

theorem transGen_nearLitter' {β : Λ} {N : NearLitter} {B : ExtendedIndex β}
    {c : SupportCondition β} (h : (inr N, B) <[α] c) : (inr N.1.toNearLitter, B) <[α] c := by
  by_cases h' : N.IsLitter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.TransGen.head (Constrains.nearLitter N (NearLitter.not_isLitter h') B) h

-- TODO: Move
-- TODO: Search for uses of fMap_β and replace with this lemma.
lemma fMap_congr_β {β γ β' γ' : Iio α} {hβγ : (β : TypeIndex) ≠ γ} {hβγ' : (β' : TypeIndex) ≠ γ'}
  {t : Tangle β} {t' : Tangle β'}
  (h : fMap hβγ t = fMap hβγ' t') :
  β = β' := by
  have h₁ := fMap_β hβγ t
  have h₂ := fMap_β hβγ' t'
  rw [← h, h₁] at h₂
  exact Subtype.coe_injective (WithBot.coe_injective h₂)

lemma fMap_congr_γ {β γ β' γ' : Iio α} {hβγ : (β : TypeIndex) ≠ γ} {hβγ' : (β' : TypeIndex) ≠ γ'}
  {t : Tangle β} {t' : Tangle β'}
  (h : fMap hβγ t = fMap hβγ' t') :
  γ = γ' := by
  have h₁ := fMap_γ hβγ t
  have h₂ := fMap_γ hβγ' t'
  rw [← h, h₁] at h₂
  exact Subtype.coe_injective h₂

theorem small_constrains {β : Λ} (c : SupportCondition β) : Small {d | d ≺[α] c} := by
  obtain ⟨a | N, A⟩ := c
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
    · simp only [h, eq_self_iff_true, not_true, false_and_iff, setOf_false, small_empty]
    · simp only [h, not_false_iff, true_and_iff, setOf_eq_eq_singleton, small_singleton]
  · change Small {c | ∃ N' a, _ ∧ ∃ B, _ ∧ _ = _}
    simp only [Prod.mk.injEq, inr.injEq, exists_eq_right_right',
      ← and_assoc, exists_eq_right']
    simp only [exists_and_right, exists_eq_right']
    refine lt_of_le_of_lt ?_ N.2.prop
    refine ⟨⟨fun c => ⟨_, c.2.choose_spec.1⟩, ?_⟩⟩
    rintro ⟨c, hc⟩ ⟨d, hd⟩
    simp only [Subtype.mk_eq_mk]
    intro h
    rw [hc.choose_spec.2, hd.choose_spec.2, h]
  · by_cases
      ∃ (γ : Iic α) (δ : Iio α) (ε : Iio α) (_hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
        (B : Path (β : TypeIndex) γ) (t : Tangle δ),
        N = (fMap (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter ∧
          A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)
    · obtain ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ := h
      refine lt_of_le_of_lt ?_ (designatedSupport t).small
      suffices
        (#{a : SupportCondition β |
            ∃ c : designatedSupport t, a = (c.val.fst, (B.cons (coe_lt hδ)).comp c.val.snd)}) ≤
          #(designatedSupport t) by
        refine le_trans (Cardinal.mk_subtype_le_of_subset ?_) this
        rintro x ⟨_, _, _, _, _, _, _, _, c, hc, rfl, h⟩
        rw [Prod.mk.injEq] at h
        simp only [inr.injEq, Litter.toNearLitter_injective.eq_iff] at h
        cases fMap_congr_β h.1
        cases fMap_congr_γ h.1
        cases fMap_injective _ h.1
        cases Subtype.coe_inj.mp
          (coe_inj.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons h.2).eq))
        cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons h.2).eq).eq
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
      exact h ⟨γ, δ, ε, hδ, hε, hδε, B, t, hA⟩
  · refine Set.Subsingleton.small ?_
    rintro ⟨c, C⟩ ⟨γ, ε, hε, C', a, hc₁, hc₂⟩ ⟨d, D⟩ ⟨γ, ε, hε, D', b, hd₁, hd₂⟩
    rw [Prod.mk.injEq] at hc₁ hc₂ hd₁ hd₂
    simp only [inr.injEq] at hc₂ hd₂
    rw [hc₁.1, hc₁.2, hd₁.1, hd₁.2]
    rw [hc₂.1, hc₂.2, Litter.toNearLitter_injective.eq_iff] at hd₂
    cases Subtype.coe_inj.mp (coe_inj.mp (Path.obj_eq_of_cons_eq_cons hd₂.2))
    cases Subtype.coe_inj.mp
      (coe_inj.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hd₂.2).eq))
    cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hd₂.2).eq).eq
    rw [(fMap_injective bot_ne_coe).eq_iff] at hd₂
    cases hd₂.1
    rfl

end ConNF
