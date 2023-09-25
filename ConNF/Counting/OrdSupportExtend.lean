import ConNF.Counting.OrdSupportEquiv

/-!
# Extending ordered supports
-/

open Set Sum
open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

namespace OrdSupport

theorem _root_.PFun.image_dom {α β : Type _} (f : α →. β) :
    f.image f.Dom = f.ran := by
  ext x
  simp only [PFun.mem_image, PFun.ran, PFun.mem_dom, mem_setOf_eq]
  constructor
  · rintro ⟨y, _, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, ⟨x, hy⟩, hy⟩

theorem le_invImage_cof {α β : Type _} {c : Cardinal} (r : α → α → Prop) (f : β → α)
    [inst : IsWellOrder α r] [IsWellOrder β (InvImage r f)]
    (hf : Unbounded r (Set.range f)) (hc : c ≤ (Ordinal.type r).cof) :
    c ≤ (Ordinal.type (InvImage r f)).cof := by
  rw [Ordinal.le_cof_type] at hc ⊢
  intro s hs
  refine (hc (f '' s) ?_).trans Cardinal.mk_image_le
  intro a
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hf a
  obtain ⟨c, hc₁, hc₂⟩ := hs b
  refine ⟨f c, ⟨c, hc₁, rfl⟩, ?_⟩
  intro h
  rw [InvImage] at hc₂
  refine hc₂ ?_
  have := inst.trichotomous (f b) a
  simp only [hb, false_or] at this
  obtain (this | this) := this
  · subst this
    exact h
  · exact inst.trans _ _ _ h this

theorem unbounded_of_injective {α β : Type _} (r : α → α → Prop) (f : β → α)
    [IsWellOrder α r] (hα : Ordinal.type r = (#α).ord) (hαβ : #α = #β) (hf : Function.Injective f) :
    Unbounded r (Set.range f) := by
  rw [← not_bounded_iff]
  rintro ⟨x, hx⟩
  have : #{y | r y x} < #α := Cardinal.card_typein_lt r x hα.symm
  rw [lt_iff_not_le] at this
  refine this ?_
  rw [hαβ]
  refine ⟨⟨fun y => ⟨f y, hx _ ⟨_, rfl⟩⟩, ?_⟩⟩
  intro y z h
  simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq] at h
  exact hf h

theorem unbounded_sumAtomNearLitter_pos :
    Unbounded (· < ·) (Set.range (pos : Atom ⊕ NearLitter → μ)) := by
  refine unbounded_of_injective _ _ μ_ord ?_ ?_
  · simp only [Cardinal.mk_sum, mk_atom, Cardinal.lift_id, mk_nearLitter,
      Cardinal.add_mk_eq_max, max_self]
  · intro a b
    simp only [EmbeddingLike.apply_eq_iff_eq, imp_self]

theorem mk_setOf_eq (S : OrdSupport β) :
    #{x | ∀ d, ∀ hd : d ∈ S, (S.cpos d).get hd < x} = #μ := by
  letI hwo : IsWellOrder (Atom ⊕ NearLitter) (· < ·) := inferInstance
  letI hlo : LinearOrder (Atom ⊕ NearLitter) := inferInstance
  letI hpo : Preorder (Atom ⊕ NearLitter) := hlo.toPreorder
  refine le_antisymm ?_ ?_
  · refine (Cardinal.mk_subtype_le _).trans ?_
    simp only [Cardinal.mk_sum, mk_atom, Cardinal.lift_id, mk_nearLitter, Cardinal.add_mk_eq_max,
      max_self, le_refl]
  have : Small S.cpos.ran
  · have := Small.pFun_image S.dom_small' (f := S.cpos)
    rw [PFun.image_dom] at this
    exact this
  have := Ordinal.lt_cof_type (r := (· < ·)) (this.trans_le ?_)
  swap
  · have hμ := κ_le_μ_ord_cof
    rw [← μ_ord] at hμ
    exact le_invImage_cof _ _ unbounded_sumAtomNearLitter_pos hμ
  obtain ⟨x, hx⟩ := this
  have huniv : Iic x ∪ {y | ∀ d, ∀ hd : d ∈ S, (S.cpos d).get hd < y} = univ
  · simp only [eq_univ_iff_forall, mem_union, or_iff_not_imp_left, mem_Iic, not_le]
    rintro y hy d hd
    exact (hx _ ⟨d, hd, rfl⟩).trans hy
  by_contra' h
  have := Cardinal.mk_union_le (Iic x) {y | ∀ d, ∀ hd : d ∈ S, (S.cpos d).get hd < y}
  have := this.trans_lt (Cardinal.add_lt_of_lt μ_isStrongLimit.isLimit.aleph0_le ?_ h)
  swap
  · refine lt_of_le_of_lt ?_ (card_Iic_lt (pos x))
    refine ⟨⟨fun y => ⟨pos y.val, ?_⟩, ?_⟩⟩
    · rw [mem_Iic]
      show pos y.val ≤ pos x
      have : _ = _ ∨ _ < _ := y.prop
      rw [le_iff_eq_or_lt, EmbeddingLike.apply_eq_iff_eq]
      exact this
    · intro x y h
      simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Subtype.coe_inj.mp h
  simp only [huniv, Cardinal.mk_univ, Cardinal.mk_sum, mk_atom, Cardinal.lift_id, mk_nearLitter,
    Cardinal.add_mk_eq_max, max_self, lt_self_iff_false] at this

theorem exists_relHom_of_type_le
    (α : Type _) (r : α → α → Prop) [IsWellOrder α r]
    (β : Type _) (s : β → β → Prop) [IsWellOrder β s]
    (S : Set β) (h : Ordinal.type r ≤ @Ordinal.type _
      (InvImage s (Subtype.val : S → β))
      (isWellOrder_invImage inferInstance _ Subtype.val_injective)) :
    ∃ f : r ↪r s, ∀ x, f x ∈ S := by
  rw [@Ordinal.type_le_iff' _ _ _ _ _
    (isWellOrder_invImage inferInstance _ Subtype.val_injective)] at h
  obtain ⟨f⟩ := h
  refine ⟨⟨⟨Subtype.val ∘ f, ?_⟩, ?_⟩, ?_⟩
  · intro x y h
    simp only [Function.comp_apply, Subtype.coe_inj] at h
    exact f.injective h
  · intro x y
    simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
    exact f.map_rel_iff
  · intro x
    exact (f x).prop

theorem type_lt_type_of_lt {α β : Type _} (r : α → α → Prop) (s : β → β → Prop)
    [inst_α : IsWellOrder α r] [inst_β : IsWellOrder β s] (h : #α < #β) :
    Ordinal.type r < Ordinal.type s := by
  contrapose! h
  obtain ⟨f⟩ := h
  exact ⟨f, f.injective⟩

theorem exists_relHom (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s)
    (r : s → s → Prop) [IsWellOrder s r] :
    ∃ f : r ↪r ((· < ·) : Atom ⊕ NearLitter → _ → _),
      ∀ x, f x ∈ {x | ∀ d, ∀ hd : d ∈ S, (S.cpos d).get hd < x} := by
  refine exists_relHom_of_type_le s r (Atom ⊕ NearLitter) (· < ·)
      {x | ∀ d, ∀ hd : d ∈ S, (S.cpos d).get hd < x} ?_
  refine le_of_lt (type_lt_type_of_lt (inst_β := _) _ ?_)
  rw [mk_setOf_eq]
  exact hs.trans_le κ_le_μ

noncomputable def embedAfter (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s)
    (r : s → s → Prop) [IsWellOrder s r] (c : SupportCondition β) (hc : c ∈ s) :
    Atom ⊕ NearLitter :=
  (exists_relHom S s hs r).choose ⟨c, hc⟩

theorem embedAfter_injective (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s)
    (r : s → s → Prop) [IsWellOrder s r] (c d : SupportCondition β) (hc : c ∈ s) (hd : d ∈ s)
    (hcd : S.embedAfter s hs r c hc = S.embedAfter s hs r d hd) :
    c = d := by
  have := (exists_relHom S s hs r).choose.injective hcd
  rw [Subtype.mk.injEq] at this
  exact this

theorem lt_embedAfter (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s)
    (r : s → s → Prop) [IsWellOrder s r] (c d : SupportCondition β) (hc : c ∈ S) (hd : d ∈ s) :
    (S.cpos c).get hc < S.embedAfter s hs r d hd :=
  (exists_relHom S s hs r).choose_spec ⟨d, hd⟩ c hc

theorem embedAfter_lt_embedAfter_iff (S : OrdSupport β) (s : Set (SupportCondition β))
    (hs : Small s) (r : s → s → Prop) [IsWellOrder s r]
    (c d : SupportCondition β) (hc : c ∈ s) (hd : d ∈ s) :
    S.embedAfter s hs r c hc < S.embedAfter s hs r d hd ↔ r ⟨c, hc⟩ ⟨d, hd⟩ :=
  (exists_relHom S s hs r).choose.map_rel_iff

open scoped Classical in
/-- Add some extra support conditions to the end of an ordered support. -/
noncomputable def extend (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s) :
    OrdSupport β where
  cpos c := ⟨c ∈ S ∨ c ∈ s, fun h =>
    if hc : c ∈ S then
      (S.cpos c).get hc
    else
      S.embedAfter s hs WellOrderingRel c (or_iff_not_imp_left.mp h hc)⟩
  injective := by
    letI hlo : LinearOrder (Atom ⊕ NearLitter) := inferInstance
    letI hpo : Preorder (Atom ⊕ NearLitter) := hlo.toPreorder
    rintro ⟨A, x⟩ ⟨_, y⟩ hc hd rfl h
    simp only at hc hd h
    split_ifs at h with h₁ h₂ h₂
    · exact S.injective _ _ _ _ rfl h
    · have := lt_embedAfter S s hs WellOrderingRel _ _ h₁ (or_iff_not_imp_left.mp hd h₂)
      rw [h] at this
      cases this.false
    · have := lt_embedAfter S s hs WellOrderingRel _ _ h₂ (or_iff_not_imp_left.mp hc h₁)
      rw [h] at this
      cases this.false
    · exact S.embedAfter_injective s hs _ _ _
        (or_iff_not_imp_left.mp hc h₁) (or_iff_not_imp_left.mp hd h₂) h
  dom_small' := Small.union S.dom_small hs

/-- An extended support specialises the original. -/
theorem le_extend (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s) :
    S ≤ S.extend s hs where
  mem_of_mem c := Or.inl
  get_eq_get _ _ _ := by
    dsimp only [extend]
    rw [dif_pos]
  get_lt_get c d hc _ hdS hds := by
    dsimp only [extend]
    rw [dif_pos hc, dif_neg hdS]
    exact S.lt_embedAfter s hs WellOrderingRel c d hc (or_iff_not_imp_left.mp hds hdS)

theorem mem_extend_iff (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s)
    (c : SupportCondition β) :
    c ∈ S.extend s hs ↔ c ∈ S ∨ c ∈ s :=
  Iff.rfl

theorem extend_lt_extend₁ {S : OrdSupport β} {s : Set (SupportCondition β)} {hs : Small s}
    {c d : SupportCondition β} (hc : c ∈ S) (hd : d ∈ S) :
    ((S.extend s hs).cpos c).get (Or.inl hc) < ((S.extend s hs).cpos d).get (Or.inl hd) ↔
    (S.cpos c).get hc < (S.cpos d).get hd :=
  by simp only [extend, hc, hd, dite_true]

theorem extend_lt_extend₂ {S : OrdSupport β} {s : Set (SupportCondition β)} {hs : Small s}
    {c d : SupportCondition β} (hc : c ∈ S) (hd₁ : d ∉ S) (hd₂ : d ∈ s) :
    ((S.extend s hs).cpos c).get (Or.inl hc) < ((S.extend s hs).cpos d).get (Or.inr hd₂) := by
  dsimp only [extend]
  rw [dif_pos hc, dif_neg hd₁]
  exact lt_embedAfter _ _ _ _ _ _ _ _

theorem extend_lt_extend₃ {S : OrdSupport β} {s : Set (SupportCondition β)} {hs : Small s}
    {c d : SupportCondition β} (hc₁ : c ∉ S) (hc₂ : c ∈ s) (hd : d ∈ S) :
    ¬((S.extend s hs).cpos c).get (Or.inr hc₂) < ((S.extend s hs).cpos d).get (Or.inl hd) :=
  not_lt_of_lt (extend_lt_extend₂ hd hc₁ hc₂)

theorem extend_lt_extend₄ {S : OrdSupport β} {s : Set (SupportCondition β)} {hs : Small s}
    {c d : SupportCondition β} (hc₁ : c ∉ S) (hc₂ : c ∈ s) (hd₁ : d ∉ S) (hd₂ : d ∈ s) :
    ((S.extend s hs).cpos c).get (Or.inr hc₂) < ((S.extend s hs).cpos d).get (Or.inr hd₂) ↔
    (WellOrderingRel : s → s → Prop) ⟨c, hc₂⟩ ⟨d, hd₂⟩ :=
  by simp only [extend, hc₁, hd₁, dite_false, embedAfter_lt_embedAfter_iff]

theorem extend_equiv (S T : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s)
    (h : S ≈ T) : S.extend s hs ≈ T.extend s hs := by
  constructor
  · intro c hc
    rw [mem_extend_iff] at hc ⊢
    rw [OrdSupport.mem_iff_mem h]
    exact hc
  · intro c hc
    rw [mem_extend_iff] at hc ⊢
    rw [← OrdSupport.mem_iff_mem h]
    exact hc
  · intro c d hcS hcT hdS hdT
    by_cases hc₁ : c ∈ S <;> by_cases hd₁ : d ∈ S
    · rw [extend_lt_extend₁ hc₁ hd₁, extend_lt_extend₁ (h.mem_right hc₁) (h.mem_right hd₁),
        h.lt_iff_lt]
    · simp only [extend_lt_extend₂ hc₁ hd₁ (or_iff_not_imp_left.mp hdS hd₁),
        extend_lt_extend₂ (h.mem_right hc₁) (fun hd₂ => hd₁ (h.mem_left hd₂))
          (or_iff_not_imp_left.mp hdS hd₁)]
    · simp only [extend_lt_extend₃ hc₁ (or_iff_not_imp_left.mp hcS hc₁) hd₁,
        extend_lt_extend₃ (fun hc₂ => hc₁ (h.mem_left hc₂)) (or_iff_not_imp_left.mp hcS hc₁)
          (h.mem_right hd₁)]
    · rw [extend_lt_extend₄ hc₁ (or_iff_not_imp_left.mp hcS hc₁)
        hd₁ (or_iff_not_imp_left.mp hdS hd₁),
      extend_lt_extend₄ (fun hc₂ => hc₁ (h.mem_left hc₂))
        (or_iff_not_imp_left.mp hcT (fun hc₂ => hc₁ (h.mem_left hc₂)))
        (fun hd₂ => hd₁ (h.mem_left hd₂))
        (or_iff_not_imp_left.mp hdT (fun hd₂ => hd₁ (h.mem_left hd₂)))]

end OrdSupport

end ConNF
