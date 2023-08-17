import ConNF.Phase0.Litter

#align_import phase2.sublitter

open Cardinal

open scoped Cardinal

universe u

namespace ConNf

variable [Params.{u}]

/-- The type of sublitters. -/
structure Sublitter : Type u where
  Litter : Litter
  carrier : Set Atom
  Subset : carrier ⊆ litterSet litter
  diff_small : Small (litterSet litter \ carrier)

namespace Sublitter

variable {S S₁ S₂ : Sublitter}

/-- Use sublitter.mk_eq_κ instead if possible. -/
theorem mk_S_eq_κ (S : Sublitter) : (#S.carrier) = (#κ) :=
  by
  have := mk_le_mk_of_subset S.subset
  rw [mk_litter_set] at this
  cases lt_or_eq_of_le this
  · have := mk_diff_add_mk S.subset
    rw [mk_litter_set] at this
    cases (add_lt_of_lt κ_regular.aleph_0_le S.diff_small h).Ne this
  exact h

instance : SetLike Sublitter Atom where
  coe S := S.carrier
  coe_injective' := by
    rintro ⟨i, N₁, h₁, h₂⟩ ⟨j, N₂, h₃, h₄⟩ (rfl : N₁ = N₂)
    obtain ⟨e⟩ := cardinal.eq.mp (sublitter.mk_S_eq_κ ⟨i, N₁, h₁, h₂⟩)
    have h₅ := h₁ (e.symm (Inhabited.default κ)).Prop
    have h₆ := h₃ (e.symm (Inhabited.default κ)).Prop
    rw [mem_litter_set] at h₅ h₆
    rw [h₅] at h₆
    cases h₆
    rfl

@[simp]
theorem mk_eq_κ (S : Sublitter) : (#S) = (#κ) :=
  S.mk_S_eq_κ

@[simp]
theorem mk_eq_κ' (S : Sublitter) : (#(S : Set Atom)) = (#κ) :=
  S.mk_S_eq_κ

@[simp]
theorem carrier_eq_coe {S : Sublitter} : S.carrier = S :=
  rfl

@[simp]
theorem coe_mk (L S subset diff_small) :
    @coe Sublitter (Set Atom) _ ⟨L, S, subset, diff_small⟩ = S :=
  rfl

@[ext]
theorem ext (h : (S₁ : Set Atom) = S₂) : S₁ = S₂ :=
  SetLike.coe_injective h

theorem fst_eq_of_mem {a : Atom} (h : a ∈ S) : a.1 = S.Litter :=
  S.Subset h

theorem mem_litterSet_of_mem {a : Atom} (h : a ∈ S) : a ∈ litterSet S.Litter :=
  S.Subset h

@[simp]
theorem mem_mk {a : Atom} {L S subset diff_small} :
    a ∈ (⟨L, S, subset, diff_small⟩ : Sublitter) ↔ a ∈ S :=
  Iff.rfl

@[simp]
theorem litter_diff_eq (S : Sublitter) : (S : Set Atom) \ litterSet S.Litter = ∅ :=
  Set.eq_empty_of_forall_not_mem fun a ha => ha.2 (S.Subset ha.1)

theorem isNearLitter (S : Sublitter) : IsNearLitter S.Litter S :=
  by
  refine' small.union S.diff_small _
  rw [litter_diff_eq]
  exact small_empty

def toNearLitter (S : Sublitter) : NearLitter :=
  ⟨S.Litter, S, S.IsNearLitter⟩

@[simp]
theorem toNearLitter_litter (S : Sublitter) : S.toNearLitter.1 = S.Litter :=
  rfl

@[simp]
theorem coe_toNearLitter (S : Sublitter) : (S.toNearLitter : Set Atom) = S :=
  rfl

@[simp]
theorem mem_toNearLitter (a : Atom) : a ∈ S.toNearLitter ↔ a ∈ S :=
  Iff.rfl

theorem isNear_iff : IsNear (S₁ : Set Atom) S₂ ↔ S₁.Litter = S₂.Litter :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨f⟩ := is_near.mk_inter h S₁.mk_eq_κ.symm.le
    rw [← fst_eq_of_mem (f (Inhabited.default κ)).Prop.1, ←
      fst_eq_of_mem (f (Inhabited.default κ)).Prop.2]
  · refine' S₁.is_near_litter.symm.trans _
    rw [h]
    exact S₂.is_near_litter

theorem inter_nonempty_iff : (S₁ ∩ S₂ : Set Atom).Nonempty ↔ S₁.Litter = S₂.Litter :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨a, ha⟩ := h
    rw [← fst_eq_of_mem ha.1, fst_eq_of_mem ha.2]
  · obtain ⟨f⟩ := is_near.mk_inter _ _
    exact ⟨_, (f (Inhabited.default κ)).Prop⟩
    rw [is_near_iff]
    exact h
    rw [mk_eq_κ']

end Sublitter

def Litter.toSublitter (L : Litter) : Sublitter :=
  ⟨L, litterSet L, subset_rfl, by rw [sdiff_self] <;> exact small_empty⟩

@[simp]
theorem Litter.litter_toSublitter (L : Litter) : L.toSublitter.Litter = L :=
  rfl

@[simp]
theorem Litter.coe_toSublitter (L : Litter) : (L.toSublitter : Set Atom) = litterSet L :=
  rfl

namespace Sublitter

def relEmbedding (S : Sublitter) :
    ((· < ·) : S → S → Prop) ↪r ((· < ·) : litterSet S.Litter → litterSet S.Litter → Prop) :=
  ⟨⟨fun a => ⟨a, S.Subset a.Prop⟩, fun a b h => Subtype.coe_injective (Subtype.mk_eq_mk.mp h)⟩,
    fun a b => by simp only [Function.Embedding.coeFn_mk, Subtype.mk_lt_mk, Subtype.coe_lt_coe]⟩

/-- The order type of a sublitter is `κ`. -/
theorem ordinal_type (S : Sublitter) : Ordinal.type ((· < ·) : S → S → Prop) = (#κ).ord :=
  by
  refine' le_antisymm _ _
  · rw [← S.litter.ordinal_type]
    exact RelEmbedding.ordinal_type_le S.rel_embedding
  · rw [Cardinal.gc_ord_card, Ordinal.card_type, mk_eq_κ]

-- TODO: We can probably do this constructively, but this way is easier for now.
noncomputable def orderIsoκ (S : Sublitter) : S ≃o κ :=
  by
  refine' OrderIso.ofRelIsoLT (Nonempty.some _)
  rw [← Ordinal.type_eq, ordinal_type, ← κ_ord]
  rfl

/-- There is a (unique) order isomorphism between any two sublitters. -/
noncomputable def orderIso (S T : Sublitter) : S ≃o T :=
  S.orderIsoκ.trans T.orderIsoκ.symm

@[simp]
theorem orderIso_apply_mem {S T : Sublitter} (a : S) : (S.OrderIso T a : Atom) ∈ T :=
  (S.OrderIso T a).Prop

@[simp]
theorem orderIso_symm_apply_mem {S T : Sublitter} (a : T) : ((S.OrderIso T).symm a : Atom) ∈ S :=
  ((S.OrderIso T).symm a).Prop

@[simp]
theorem orderIso_apply_fst_eq {S T : Sublitter} (a : S) : (S.OrderIso T a : Atom).1 = T.Litter :=
  T.Subset (S.OrderIso T a).Prop

@[simp]
theorem orderIso_symm_apply_fst_eq {S T : Sublitter} (a : T) :
    ((S.OrderIso T).symm a : Atom).1 = S.Litter :=
  S.Subset ((S.OrderIso T).symm a).Prop

theorem orderIso_congr_left {S T U : Sublitter} (h : S = T) (a : S) :
    (S.OrderIso U a : Atom) = T.OrderIso U ⟨a, by rw [← h] <;> exact a.2⟩ := by
  cases h <;> rw [Subtype.coe_eta]

theorem orderIso_congr_right {S T U : Sublitter} (h : T = U) (a : S) :
    (S.OrderIso T a : Atom) = S.OrderIso U a := by cases h <;> rfl

def orderIso.subtypeIso {α β : Type _} [LE α] [LE β] (e : α ≃o β) {p : α → Prop} {q : β → Prop}
    (hpq : ∀ a, p a ↔ q (e a)) : { a // p a } ≃o { b // q b } :=
  ⟨e.subtypeEquiv hpq, by
    simp only [RelIso.coe_fn_toEquiv, Equiv.subtypeEquiv_apply, Subtype.mk_le_mk,
      OrderIso.le_iff_le, Subtype.coe_le_coe, iff_self_iff, Subtype.forall, imp_true_iff]⟩

/-- There is a unique order isomorphism between corresponding subtypes of a well-order.
TODO: Can prove this without specialising to subtypes. -/
theorem orderIso.unique {α β : Type _} [LinearOrder α] [αwf : WellFounded ((· < ·) : α → α → Prop)]
    [LinearOrder β] [βwf : WellFounded ((· < ·) : β → β → Prop)] (e : α ≃o β) {p : α → Prop}
    {q : β → Prop} (hpq : ∀ a, p a ↔ q (e a)) (e' : { a // p a } ≃o { b // q b }) :
    e' = e.subtypeIso hpq := by
  ext x
  obtain ⟨x, hx⟩ := x
  revert hx
  refine' αwf.induction x _
  intro x ih hx
  rw [Subtype.coe_inj]
  refine' Linarith.eq_of_not_lt_of_not_gt _ _ (fun h => _) fun h => _
  · have := ih ((e.subtype_iso hpq).symm (e' ⟨x, hx⟩)) _ _
    · simp only [Subtype.coe_eta, OrderIso.apply_symm_apply, Subtype.coe_inj,
        OrderIso.apply_eq_iff_eq, OrderIso.symm_apply_eq] at this
      exact h.ne this
    · refine' lt_of_lt_of_eq _ (Subtype.coe_mk x hx)
      have := (e.subtype_iso hpq).symm.StrictMono h
      rw [OrderIso.symm_apply_apply] at this
      exact this
    · exact Subtype.coe_prop _
  · have := ih (e'.symm (e.subtype_iso hpq ⟨x, hx⟩)) _ _
    · simp only [Subtype.coe_eta, OrderIso.apply_symm_apply, Subtype.coe_inj,
        OrderIso.apply_eq_iff_eq, OrderIso.symm_apply_eq] at this
      have := h.trans_eq (congr_arg e' this)
      rw [OrderIso.apply_symm_apply] at this
      exact this.ne rfl
    · refine' lt_of_lt_of_eq _ (Subtype.coe_mk x hx)
      have := e'.symm.strict_mono h
      rw [OrderIso.symm_apply_apply] at this
      exact this
    · exact Subtype.coe_prop _

/-- The intersection of two sublitters. -/
def meet (S T : Sublitter) (h : S.Litter = T.Litter) : Sublitter
    where
  Litter := S.Litter
  carrier := S ∩ T
  Subset := (Set.inter_subset_left _ _).trans S.Subset
  diff_small := by rw [Set.diff_inter] <;> exact small.union S.diff_small (h.symm ▸ T.diff_small)

/-- Transports the meet of sublitters `S` and `U` across the order isomorphism `S ≃o T`. -/
def orderIsoMeet (S T U : Sublitter) (h : S.Litter = U.Litter) : Sublitter
    where
  Litter := T.Litter
  carrier := {a | ∃ ha : a ∈ T, ((S.OrderIso T).symm ⟨a, ha⟩ : Atom) ∈ U}
  Subset a ha := T.Subset ha.some
  diff_small :=
    by
    suffices Small ((T : Set atom) \ {a | ∃ ha : a ∈ T, ((S.order_iso T).symm ⟨a, ha⟩ : atom) ∈ U})
      by
      refine' small.mono (fun a ha => _) (small.union T.diff_small this)
      by_cases a ∈ T
      exact Or.inr ⟨h, ha.2⟩
      exact Or.inl ⟨ha.1, h⟩
    refine' lt_of_le_of_lt _ U.diff_small
    refine' ⟨⟨fun a => ⟨(S.order_iso T).symm ⟨a, a.Prop.1⟩, _, _⟩, fun a b h => _⟩⟩
    · rw [← h]
      exact S.subset ((S.order_iso T).symm ⟨a, a.prop.1⟩).2
    · intro h
      exact a.prop.2 ⟨a.prop.1, h⟩
    · simpa only [Subtype.mk_eq_mk, RelIso.eq_iff_eq, Subtype.coe_inj] using h

end Sublitter

end ConNf
