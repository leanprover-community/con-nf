import ConNF.Phase1.AMap
import ConNF.Phase2.Basic

#align_import phase2.constrains

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
  contrapose! <;> simp only [Subtype.coe_inj, imp_self]

theorem coe_lt {γ : Iio α} {β : Iic α} : (γ : Λ) < β → (γ : TypeIndex) < (β : TypeIndex) :=
  by
  intro h
  cases β
  cases γ
  exact coe_lt_coe.mpr h

variable (α) (β)

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ∈ » «expr ∆ »(litter_set[con_nf.litter_set] N.fst, N.snd)) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (c «expr ∈ » (designated_support[con_nf.designated_support] t).carrier) -/
/-- Support conditions can be said to *constrain* each other in a number of ways. This is discussed
in the "freedom of action discussion".
1. `⟨L, A⟩ ≺ ⟨a, A⟩` when `a ∈ L` and `L` is a litter. We can say that an atom is constrained by the
    litter it belongs to.
2. `⟨N°, A⟩ ≺ ⟨N, A⟩` when `N` is a near-litter not equal to its corresponding litter `N°`.
3. `⟨a, A⟩ ≺ ⟨N, A⟩` for all `a ∈ N ∆ N°`.
4. `⟨x, A ≫ (γ ⟶ δ) ≫ B⟩ ≺ ⟨f_{γ,δ}(t), A ≫ (γ ⟶ ε) ≫ (ε ⟶ ⊥)⟩` for all paths `A : β ⟶ γ` and
    `δ, ε < γ` with `δ ≠ ε`, `t ∈ τ_γ`, where `⟨x, B⟩` lies in the designated `δ`-support of `t`.
TODO: Refactor `near_litter` to use `¬N.is_litter`.
-/
@[mk_iff]
inductive Constrains : SupportCondition β → SupportCondition β → Prop
  | atom (a : Atom) (A : ExtendedIndex β) : constrains ⟨inr a.1.toNearLitter, A⟩ ⟨inl a, A⟩
  |
  near_litter (N : NearLitter) (hN : litterSet N.fst ≠ N.snd) (A : ExtendedIndex β) :
    constrains ⟨inr N.fst.toNearLitter, A⟩ ⟨inr N, A⟩
  |
  symmDiff (N : NearLitter) (a) (_ : a ∈ litterSet N.fst ∆ N.snd) (A : ExtendedIndex β) :
    constrains ⟨inl a, A⟩ ⟨inr N, A⟩
  |
  fMap ⦃γ : Iic α⦄ ⦃δ : Iio α⦄ ⦃ε : Iio α⦄ (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
    (A : Path (β : TypeIndex) γ) (t : Tangle δ) (c) (_ : c ∈ (designatedSupport t).carrier) :
    constrains ⟨c.fst, (A.cons (coe_lt hδ)).comp c.snd⟩
      ⟨inr (fMap (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
        (A.cons (coe_lt hε)).cons (bot_lt_coe _)⟩
  |
  fMap_bot ⦃γ : Iic α⦄ ⦃ε : Iio α⦄ (hε : (ε : Λ) < γ) (A : Path (β : TypeIndex) γ) (a : Atom) :
    constrains ⟨inl a, A.cons (bot_lt_coe _)⟩
      ⟨inr (fMap (show (⊥ : TypeIndex) ≠ (ε : Λ) from bot_ne_coe) a).toNearLitter,
        (A.cons (coe_lt hε)).cons (bot_lt_coe _)⟩

/-! We declare new notation for the "constrains" relation on support conditions. -/


notation:50 c " ≺[" α "] " d:50 => Constrains α _ c d

instance : LT (SupportCondition β) :=
  ⟨Prod.Lex (InvImage (· < ·) fun c => c.elim typedAtomPosition typedNearLitterPosition) (· < ·)⟩

instance : IsWellFounded (SupportCondition β) (· < ·) :=
  Prod.Lex.isWellFounded

theorem constrains_subrelation : Subrelation (Constrains α β) (· < ·) :=
  by
  rintro c d h
  obtain ⟨a, A⟩ | ⟨N, hN, A⟩ | ⟨N, a, ha, A⟩ | ⟨hδ, hε, hδε, A, t, c, hc⟩ | ⟨hδ, A, a⟩ := h <;> left
  · exact litter_lt a.1 a rfl
  · refine' litter_lt_near_litter N _
    contrapose! hN
    rw [← hN]
    rfl
  · exact symm_diff_lt_near_litter N a ha
  · have := fMap_position (coe_ne_coe.mpr <| coe_ne' hδε) t _ (is_near_litter_litter_set _)
    rw [TangleData.typed_near_litter_position_eq] at this
    refine' lt_of_le_of_lt _ this
    convert TangleData.support_le (show tangle (h_δ : Λ) from t) _ hc
  · simp only [InvImage, elim_inr]
    convert typed_atom_position_lt_fMap a
    rw [TangleData.typed_near_litter_position_eq (fMap bot_ne_coe a).toNearLitter]
    infer_instance

/-- The `≺` relation is well-founded. By the conditions on orderings, if we have `⟨x, A⟩ ≺ ⟨y, B⟩`,
then `x < y` in `µ`, under the `typed_near_litter` or `typed_atom` maps. -/
theorem constrains_wf : WellFounded (Constrains α β) :=
  Subrelation.wf (constrains_subrelation α β) (IsWellFounded.toHasWellFounded _).wf

instance : WellFoundedRelation (SupportCondition β) :=
  ⟨Constrains α β, constrains_wf α β⟩

variable {α}

@[simp]
theorem constrains_atom {c : SupportCondition β} {a : Atom} {A : ExtendedIndex β} :
    c ≺[α] ⟨inl a, A⟩ ↔ c = ⟨inr a.1.toNearLitter, A⟩ :=
  by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; exact constrains.atom a A

/-
-- Probably not the statement we actually want to prove.
lemma constrains_fMap {γ : Iio α} {δ : Iio α}
  (h : (γ : type_index) ≠ δ) (B : extended_index δ) (t : tangle γ) {c : support_condition δ}
  (hc : c ≺[α] (inr (fMap h t).to_near_litter, B)) :
  ∃ β : Iic α, ∃ hβ : (γ : Λ) < β, ∃ A : path (δ : type_index) β, ∃ d : support_condition γ,
    d ∈ designated_support t ∧ c = (d.fst, (A.cons (coe_lt hβ)).comp d.snd) :=
begin
  rw constrains_iff at hc,
  obtain (hc | hc | hc | hc | hc) := hc,
  { simp only [prod.mk.inj_iff, false_and, and_false, exists_false] at hc,
    cases hc, },
  { simp only [ne.def, prod.mk.inj_iff, exists_eq_right_right', litter.to_near_litter_fst] at hc,
    cases hc.1 rfl, },
  { simp only [prod.mk.inj_iff, exists_eq_right_right'] at hc,
    obtain ⟨_, a, ha, hc, rfl⟩ := hc,
    change a ∈ ((fMap h t).to_near_litter : set atom) ∆ (fMap h t).to_near_litter at ha,
    simp only [symm_diff_self, bot_eq_empty, mem_empty_iff_false] at ha,
    cases ha, },
  { obtain ⟨γ', δ', ε', hδ', hε', hδε', A, t', c, hc₁, rfl, hc₂⟩ := hc,
    simp only [prod.mk.inj_iff, litter.to_near_litter_injective.eq_iff] at hc₂,
    have : γ = δ',
    { have h₁ := fMap_β h t,
      rw hc₂.1 at h₁,
      have h₂ := fMap_β _ t',
      have := h₁.symm.trans h₂,
      have := with_bot.coe_inj.mp this,
      rw subtype.coe_inj at this,
      exact this, },
    subst this,
    have : δ = ε',
    { have h₁ := fMap_γ h t,
      rw hc₂.1 at h₁,
      have h₂ := fMap_γ _ t',
      have := h₁.symm.trans h₂,
      rw subtype.coe_inj at this,
      exact this, },
    subst this,
    cases fMap_injective _ hc₂.1,
    cases hc₂.2,
    exact ⟨γ', hδ', A, c, hc₁, rfl⟩, },
  { obtain ⟨γ', ε', hε', A, a, hc₁, hc₂⟩ := hc,
    simp only [prod.mk.inj_iff, litter.to_near_litter_injective.eq_iff] at hc₂,
    have := fMap_β h t,
    rw hc₂.1 at this,
    have := this.symm.trans (fMap_β bot_ne_coe a),
    cases this, },
end -/
/-- The constrains relation is stable under composition of paths. -/
theorem constrainsComp {β γ : Λ} {c d : SupportCondition γ} (h : c ≺[α] d)
    (B : Path (β : TypeIndex) γ) : ⟨c.fst, B.comp c.snd⟩ ≺[α] ⟨d.fst, B.comp d.snd⟩ :=
  by
  obtain ⟨a, A⟩ | ⟨N, hN, A⟩ | ⟨N, a, ha, A⟩ | ⟨hδ, hε, hδε, A, t, c, hc⟩ | ⟨hδ, A, a⟩ := h
  · exact constrains.atom _ _
  · exact constrains.near_litter _ hN _
  · exact constrains.symm_diff _ _ ha _
  · rw [path.comp_cons, ← path.comp_assoc, path.comp_cons]
    exact constrains.fMap hδ hε hδε (B.comp A) t c hc
  · rw [path.comp_cons]
    exact constrains.fMap_bot hδ (B.comp A) a

notation:50 c " <[" α "] " d:50 => Relation.TransGen (Constrains α _) c d

notation:50 c " ≤[" α "] " d:50 => Relation.ReflTransGen (Constrains α _) c d

theorem trans_constrains_wf (α : Λ) [Phase2Assumptions α] (β : Λ) :
    WellFounded fun c d : SupportCondition β => c <[α] d :=
  (@Relation.TransGen.isWellFounded _ _ _).wf

theorem reflTransGen_constrains_comp {β γ : Λ} {c d : SupportCondition γ} (h : c ≤[α] d)
    (B : Path (β : TypeIndex) γ) : ⟨c.fst, B.comp c.snd⟩ ≤[α] ⟨d.fst, B.comp d.snd⟩ :=
  by
  induction' h with e f hce hef ih
  exact Relation.ReflTransGen.refl
  exact Relation.ReflTransGen.tail ih (constrains_comp hef B)

theorem transGen_constrains_comp {β γ : Λ} {c d : SupportCondition γ} (h : c <[α] d)
    (B : Path (β : TypeIndex) γ) : ⟨c.fst, B.comp c.snd⟩ <[α] ⟨d.fst, B.comp d.snd⟩ :=
  by
  induction' h with e hce e f hce hef ih
  exact Relation.TransGen.single (constrains_comp hce B)
  exact Relation.TransGen.tail ih (constrains_comp hef B)

theorem reflTransGen_nearLitter {β : Λ} {N : NearLitter} {B : ExtendedIndex β}
    {c : SupportCondition β} (h : (inr N, B) ≤[α] c) : (inr N.1.toNearLitter, B) ≤[α] c :=
  by
  by_cases h' : N.is_litter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.ReflTransGen.head (constrains.near_litter N (near_litter.not_is_litter h') B) h

theorem transGen_nearLitter {β : Λ} {N : NearLitter} {B : ExtendedIndex β} {c : SupportCondition β}
    (h : c <[α] (inr N.1.toNearLitter, B)) : c <[α] (inr N, B) :=
  by
  by_cases h' : N.is_litter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.TransGen.tail h (constrains.near_litter N (near_litter.not_is_litter h') B)

theorem transGen_near_litter' {β : Λ} {N : NearLitter} {B : ExtendedIndex β}
    {c : SupportCondition β} (h : (inr N, B) <[α] c) : (inr N.1.toNearLitter, B) <[α] c :=
  by
  by_cases h' : N.is_litter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.TransGen.head (constrains.near_litter N (near_litter.not_is_litter h') B) h

theorem small_constrains {β : Λ} (c : SupportCondition β) : Small {d | d ≺[α] c} :=
  by
  obtain ⟨a | N, A⟩ := c
  · simp only [constrains_atom, set_of_eq_eq_singleton, small_singleton]
  simp_rw [constrains_iff]
  refine' small.union _ (small.union _ (small.union _ (small.union _ _))) <;> rw [small_set_of]
  ·
    simp only [Prod.mk.inj_iff, false_and_iff, and_false_iff, exists_false, set_of_false,
      small_empty]
  · simp only [Ne.def, Prod.mk.inj_iff, exists_eq_right_right']
    by_cases litter_set N.fst = N.snd
    simp only [h, eq_self_iff_true, not_true, false_and_iff, set_of_false, small_empty]
    simp only [h, not_false_iff, true_and_iff, set_of_eq_eq_singleton, small_singleton]
  · simp only [Prod.mk.inj_iff, exists_eq_right_right']
    have : Small {c : support_condition β | ∃ a, a ∈ litter_set N.fst ∆ N.snd ∧ c = (inl a, A)} :=
      by
      refine' lt_of_le_of_lt _ N.2.prop
      refine' ⟨⟨fun c => ⟨_, c.2.choose_spec.1⟩, _⟩⟩
      rintro ⟨c, hc⟩ ⟨d, hd⟩
      simp only [Subtype.val_eq_coe, Subtype.mk_eq_mk]
      intro h
      rw [hc.some_spec.2, hd.some_spec.2, h]
    convert this using 1
    ext ⟨a | N, A⟩ : 1
    · simp only [mem_set_of_eq, Prod.mk.inj_iff]
      constructor
      · rintro ⟨_, a', h₁, h₂, rfl⟩
        exact ⟨a', h₁, h₂⟩
      · rintro ⟨a', h₁, h₂⟩
        exact ⟨N, a', h₁, h₂, rfl⟩
    · simp only [mem_set_of_eq, Prod.mk.inj_iff, false_and_iff, and_false_iff, exists_false]
  · by_cases
      ∃ (γ : Iic α) (δ : Iio α) (ε : Iio α) (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε) (B :
        Path (β : type_index) γ) (t : tangle δ),
        N = (fMap (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter ∧
          A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)
    · obtain ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ := h
      refine' lt_of_le_of_lt _ (designated_support t).Small
      suffices
        (#{a : support_condition β |
              ∃ c : designated_support t, a = ⟨c.val.fst, (B.cons (coe_lt hδ)).comp c.val.snd⟩}) ≤
          (#designated_support t)
        by
        refine' le_trans (Cardinal.mk_subtype_le_of_subset _) this
        rintro x ⟨_, _, _, _, _, _, _, _, c, hc, rfl, h⟩
        simp only [Prod.mk.inj_iff, litter.to_near_litter_injective.eq_iff, fMap] at h
        cases subtype.coe_inj.mp (coe_inj.mp h.1.2.1)
        cases subtype.coe_inj.mp h.1.2.2
        cases choose_wf_injective h.1.1
        cases
          subtype.coe_inj.mp
            (coe_inj.mp (path.obj_eq_of_cons_eq_cons (path.heq_of_cons_eq_cons h.2).Eq))
        cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons h.2).Eq).Eq
        exact ⟨⟨c, hc⟩, rfl⟩
      refine' ⟨⟨fun a => a.prop.some, _⟩⟩
      intro a b h
      refine' subtype.coe_inj.mp _
      simp only [Subtype.val_eq_coe] at h
      rw [a.prop.some_spec, b.prop.some_spec]
      simp only [h, Subtype.val_eq_coe]
    · refine' small_of_forall_not_mem _
      rintro x ⟨γ, δ, ε, hδ, hε, hδε, B, t, c, hN, rfl, hA⟩
      simp only [Prod.mk.inj_iff] at hA
      refine' h ⟨γ, δ, ε, hδ, hε, hδε, B, t, hA⟩
  · refine' subsingleton.small _
    rintro ⟨c, C⟩ ⟨γ, ε, hε, C', a, hc₁, hc₂⟩ ⟨d, D⟩ ⟨γ, ε, hε, D', b, hd₁, hd₂⟩
    simp only [Prod.mk.inj_iff] at hc₁ hc₂ hd₁ hd₂
    rw [hc₁.1, hc₁.2, hd₁.1, hd₁.2]
    rw [hc₂.1, hc₂.2, litter.to_near_litter_injective.eq_iff] at hd₂
    cases subtype.coe_inj.mp (coe_inj.mp (path.obj_eq_of_cons_eq_cons hd₂.2))
    cases
      subtype.coe_inj.mp
        (coe_inj.mp (path.obj_eq_of_cons_eq_cons (path.heq_of_cons_eq_cons hd₂.2).Eq))
    cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hd₂.2).Eq).Eq
    rw [(fMap_injective bot_ne_coe).eq_iff] at hd₂
    cases hd₂.1
    rfl

end ConNF
