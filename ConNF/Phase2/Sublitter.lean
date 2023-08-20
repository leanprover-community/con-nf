import ConNF.Phase0.NearLitter

open Cardinal

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}]

/-- The type of sublitters. -/
structure Sublitter : Type u where
  litter : Litter
  carrier : Set Atom
  subset : carrier ⊆ litterSet litter
  diff_small : Small (litterSet litter \ carrier)

namespace Sublitter

variable {S S₁ S₂ : Sublitter}

/-- Use sublitter.mk_eq_κ instead if possible. -/
theorem mk_S_eq_κ (S : Sublitter) : #S.carrier = #κ := by
  have := mk_le_mk_of_subset S.subset
  rw [mk_litterSet] at this
  obtain (h | h) := lt_or_eq_of_le this
  · have := mk_diff_add_mk S.subset
    rw [mk_litterSet] at this
    cases (add_lt_of_lt κ_regular.aleph0_le S.diff_small h).ne this
  · exact h

instance : SetLike Sublitter Atom where
  coe S := S.carrier
  coe_injective' := by
    rintro ⟨i, N₁, h₁, h₂⟩ ⟨j, N₂, h₃, h₄⟩ (rfl : N₁ = N₂)
    obtain ⟨e⟩ := Cardinal.eq.mp (Sublitter.mk_S_eq_κ ⟨i, N₁, h₁, h₂⟩)
    have h₅ := h₁ (e.symm default).prop
    have h₆ := h₃ (e.symm default).prop
    rw [mem_litterSet] at h₅ h₆
    rw [h₅] at h₆
    cases h₆
    rfl

@[simp]
theorem mk_eq_κ (S : Sublitter) : #S = #κ :=
  S.mk_S_eq_κ

@[simp]
theorem mk_eq_κ' (S : Sublitter) : #(S : Set Atom) = #κ :=
  S.mk_S_eq_κ

@[simp]
theorem carrier_eq_coe {S : Sublitter} : S.carrier = S :=
  rfl

@[simp]
theorem coe_mk (L S subset diff_small) :
    (⟨L, S, subset, diff_small⟩ : Sublitter) = S :=
  rfl

@[ext]
theorem ext (h : (S₁ : Set Atom) = S₂) : S₁ = S₂ :=
  SetLike.coe_injective h

theorem fst_eq_of_mem {a : Atom} (h : a ∈ S) : a.1 = S.litter :=
  S.subset h

theorem mem_litterSet_of_mem {a : Atom} (h : a ∈ S) : a ∈ litterSet S.litter :=
  S.subset h

@[simp]
theorem mem_mk {a : Atom} {L S subset diff_small} :
    a ∈ (⟨L, S, subset, diff_small⟩ : Sublitter) ↔ a ∈ S :=
  Iff.rfl

@[simp]
theorem litter_diff_eq (S : Sublitter) : (S : Set Atom) \ litterSet S.litter = ∅ :=
  Set.eq_empty_of_forall_not_mem fun _ ha => ha.2 (S.subset ha.1)

theorem isNearLitter (S : Sublitter) : IsNearLitter S.litter S := by
  refine Small.union S.diff_small ?_
  rw [litter_diff_eq]
  exact small_empty

def toNearLitter (S : Sublitter) : NearLitter :=
  ⟨S.litter, S, S.isNearLitter⟩

@[simp]
theorem toNearLitter_litter (S : Sublitter) : S.toNearLitter.1 = S.litter :=
  rfl

@[simp]
theorem coe_toNearLitter (S : Sublitter) : (S.toNearLitter : Set Atom) = S :=
  rfl

@[simp]
theorem mem_toNearLitter (a : Atom) : a ∈ S.toNearLitter ↔ a ∈ S :=
  Iff.rfl

theorem isNear_iff : IsNear (S₁ : Set Atom) S₂ ↔ S₁.litter = S₂.litter := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨f⟩ := IsNear.mk_inter h S₁.mk_eq_κ.symm.le
    rw [← fst_eq_of_mem (f default).prop.1, ← fst_eq_of_mem (f default).prop.2]
  · refine S₁.isNearLitter.symm.trans ?_
    rw [h]
    exact S₂.isNearLitter

theorem inter_nonempty_iff : (S₁ ∩ S₂ : Set Atom).Nonempty ↔ S₁.litter = S₂.litter := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, ha⟩ := h
    rw [← fst_eq_of_mem ha.1, fst_eq_of_mem ha.2]
  · exact NearLitter.inter_nonempty_of_fst_eq_fst (N₁ := S₁.toNearLitter) (N₂ := S₂.toNearLitter) h

end Sublitter

def Litter.toSublitter (L : Litter) : Sublitter :=
  ⟨L, litterSet L, subset_rfl, by
    rw [sdiff_self]
    exact small_empty⟩

@[simp]
theorem Litter.litter_toSublitter (L : Litter) : L.toSublitter.litter = L :=
  rfl

@[simp]
theorem Litter.coe_toSublitter (L : Litter) : (L.toSublitter : Set Atom) = litterSet L :=
  rfl

namespace Sublitter

def relEmbedding (S : Sublitter) :
    ((· < ·) : S → S → Prop) ↪r ((· < ·) : litterSet S.litter → litterSet S.litter → Prop) :=
  ⟨⟨fun a => ⟨a, S.subset a.prop⟩, fun a b h => Subtype.coe_injective (Subtype.mk_eq_mk.mp h)⟩,
    fun {a b} => by simp only [Function.Embedding.coeFn_mk, Subtype.mk_lt_mk, Subtype.coe_lt_coe]⟩

/-- The order type of a sublitter is `κ`. -/
theorem ordinal_type (S : Sublitter) : Ordinal.type ((· < ·) : S → S → Prop) = (#κ).ord := by
  refine le_antisymm ?_ ?_
  · rw [← S.litter.ordinal_type]
    exact RelEmbedding.ordinal_type_le S.relEmbedding
  · rw [Cardinal.gc_ord_card, Ordinal.card_type, mk_eq_κ]

-- TODO: We can probably do this constructively, but this way is easier for now.
noncomputable def orderIsoκ (S : Sublitter) : S ≃o κ := by
  refine OrderIso.ofRelIsoLT (Nonempty.some ?_)
  rw [← Ordinal.type_eq, ordinal_type, ← κ_ord]
  rfl

/-- There is a (unique) order isomorphism between any two sublitters. -/
noncomputable def orderIso (S T : Sublitter) : S ≃o T :=
  S.orderIsoκ.trans T.orderIsoκ.symm

@[simp]
theorem orderIso_apply_mem {S T : Sublitter} (a : S) : (S.orderIso T a : Atom) ∈ T :=
  (S.orderIso T a).prop

@[simp]
theorem orderIso_symm_apply_mem {S T : Sublitter} (a : T) : ((S.orderIso T).symm a : Atom) ∈ S :=
  ((S.orderIso T).symm a).prop

@[simp]
theorem orderIso_apply_fst_eq {S T : Sublitter} (a : S) : (S.orderIso T a : Atom).1 = T.litter :=
  T.subset (S.orderIso T a).prop

@[simp]
theorem orderIso_symm_apply_fst_eq {S T : Sublitter} (a : T) :
    ((S.orderIso T).symm a : Atom).1 = S.litter :=
  S.subset ((S.orderIso T).symm a).prop

theorem orderIso_congr_left {S T U : Sublitter} (h : S = T) (a : S) :
    (S.orderIso U a : Atom) = T.orderIso U ⟨a, by rw [← h]; exact a.2⟩ := by
  cases h
  rw [Subtype.coe_eta]

theorem orderIso_congr_right {S T U : Sublitter} (h : T = U) (a : S) :
    (S.orderIso T a : Atom) = S.orderIso U a := by cases h; rfl

def _root_.OrderIso.subtypeIso {α β : Type _} [LE α] [LE β] (e : α ≃o β)
    {p : α → Prop} {q : β → Prop} (hpq : ∀ a, p a ↔ q (e a)) :
    { a // p a } ≃o { b // q b } :=
  ⟨e.subtypeEquiv hpq, by
    simp only [RelIso.coe_fn_toEquiv, Equiv.subtypeEquiv_apply, Subtype.mk_le_mk,
      OrderIso.le_iff_le, Subtype.coe_le_coe, iff_self_iff, Subtype.forall, imp_true_iff]⟩

/-- The intersection of two sublitters. -/
def meet (S T : Sublitter) (h : S.litter = T.litter) : Sublitter
    where
  litter := S.litter
  carrier := S ∩ T
  subset := (Set.inter_subset_left _ _).trans S.subset
  diff_small := by rw [Set.diff_inter]; exact Small.union S.diff_small (h.symm ▸ T.diff_small)

/-- Transports the meet of sublitters `S` and `U` across the order isomorphism `S ≃o T`. -/
def orderIsoMeet (S T U : Sublitter) (h : S.litter = U.litter) : Sublitter
    where
  litter := T.litter
  carrier := {a | ∃ ha : a ∈ T, ((S.orderIso T).symm ⟨a, ha⟩ : Atom) ∈ U}
  subset a ha := T.subset ha.choose
  diff_small := by
    suffices Small ((T : Set Atom) \
      {a | ∃ ha : a ∈ T, ((S.orderIso T).symm ⟨a, ha⟩ : Atom) ∈ U}) by
      refine Small.mono (fun a ha => ?_) (Small.union T.diff_small this)
      by_cases a ∈ T
      exact Or.inr ⟨h, ha.2⟩
      exact Or.inl ⟨ha.1, h⟩
    refine lt_of_le_of_lt ?_ U.diff_small
    refine ⟨⟨fun a => ⟨(S.orderIso T).symm ⟨a, a.prop.1⟩, ?_, ?_⟩, fun a b h => ?_⟩⟩
    · rw [← h]
      exact S.subset ((S.orderIso T).symm ⟨a, a.prop.1⟩).2
    · intro h
      exact a.prop.2 ⟨a.prop.1, h⟩
    · simpa only [Subtype.mk_eq_mk, RelIso.eq_iff_eq, Subtype.coe_inj] using h

end Sublitter

end ConNF
