import phase0.litter

open cardinal
open_locale cardinal

universe u

namespace con_nf
variable [params.{u}]

/-- The type of sublitters. -/
structure sublitter : Type u :=
(litter : litter)
(carrier : set atom)
(subset : carrier ⊆ litter_set litter)
(diff_small : small (litter_set litter \ carrier))

namespace sublitter

variables {S S₁ S₂ : sublitter}

/-- Use sublitter.mk_eq_κ instead if possible. -/
lemma mk_S_eq_κ (S : sublitter) : #(S.carrier) = #κ :=
begin
  have := mk_le_mk_of_subset S.subset,
  rw mk_litter_set at this,
  cases lt_or_eq_of_le this,
  { have := mk_diff_add_mk S.subset,
    rw mk_litter_set at this,
    cases (add_lt_of_lt κ_regular.aleph_0_le S.diff_small h).ne this, },
  exact h,
end

instance : set_like sublitter atom :=
{ coe := λ S, S.carrier,
  coe_injective' := begin
    rintro ⟨i, N₁, h₁, h₂⟩ ⟨j, N₂, h₃, h₄⟩ (rfl : N₁ = N₂),
    obtain ⟨e⟩ := cardinal.eq.mp (sublitter.mk_S_eq_κ ⟨i, N₁, h₁, h₂⟩),
    have h₅ := h₁ (e.symm (arbitrary κ)).prop,
    have h₆ := h₃ (e.symm (arbitrary κ)).prop,
    rw mem_litter_set at h₅ h₆,
    rw h₅ at h₆,
    cases h₆,
    refl,
  end }

@[simp] lemma mk_eq_κ (S : sublitter) : #S = #κ := S.mk_S_eq_κ
@[simp] lemma mk_eq_κ' (S : sublitter) : #(S : set atom) = #κ := S.mk_S_eq_κ

@[simp] lemma carrier_eq_coe {S : sublitter} : S.carrier = S := rfl

@[simp] lemma coe_mk (L S subset diff_small) :
  @coe sublitter (set atom) _ ⟨L, S, subset, diff_small⟩ = S := rfl

@[ext] lemma ext (h : (S₁ : set atom) = S₂) : S₁ = S₂ :=
set_like.coe_injective h

lemma fst_eq_of_mem {a : atom} (h : a ∈ S) : a.1 = S.litter := S.subset h
lemma mem_litter_set_of_mem {a : atom} (h : a ∈ S) : a ∈ litter_set S.litter := S.subset h
@[simp] lemma mem_mk {a : atom} {L S subset diff_small} :
  a ∈ (⟨L, S, subset, diff_small⟩ : sublitter) ↔ a ∈ S := iff.rfl

@[simp] lemma litter_diff_eq (S : sublitter) : (S : set atom) \ litter_set S.litter = ∅ :=
set.eq_empty_of_forall_not_mem (λ a ha, ha.2 (S.subset ha.1))

lemma is_near_litter (S : sublitter) : is_near_litter S.litter S :=
begin
  refine small.union S.diff_small _,
  rw litter_diff_eq,
  exact small_empty,
end

def to_near_litter (S : sublitter) : near_litter := ⟨S.litter, S, S.is_near_litter⟩

@[simp] lemma to_near_litter_litter (S : sublitter) : S.to_near_litter.1 = S.litter := rfl
@[simp] lemma coe_to_near_litter (S : sublitter) : (S.to_near_litter : set atom) = S := rfl
@[simp] lemma mem_to_near_litter (a : atom) : a ∈ S.to_near_litter ↔ a ∈ S := iff.rfl

lemma is_near_iff : is_near (S₁ : set atom) S₂ ↔ S₁.litter = S₂.litter :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨f⟩ := is_near.mk_inter h S₁.mk_eq_κ.symm.le,
    rw [← fst_eq_of_mem (f (arbitrary κ)).prop.1, ← fst_eq_of_mem (f (arbitrary κ)).prop.2], },
  { refine S₁.is_near_litter.symm.trans _,
    rw h,
    exact S₂.is_near_litter, },
end

lemma inter_nonempty_iff : (S₁ ∩ S₂ : set atom).nonempty ↔ S₁.litter = S₂.litter :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨a, ha⟩ := h,
    rw [← fst_eq_of_mem ha.1, fst_eq_of_mem ha.2], },
  { obtain ⟨f⟩ := is_near.mk_inter _ _,
    exact ⟨_, (f (arbitrary κ)).prop⟩,
    rw is_near_iff,
    exact h,
    rw mk_eq_κ', },
end

end sublitter

def litter.to_sublitter (L : litter) : sublitter :=
⟨L, litter_set L, subset_rfl, by rw [sdiff_self]; exact small_empty⟩

@[simp] lemma litter.litter_to_sublitter (L : litter) : L.to_sublitter.litter = L := rfl
@[simp] lemma litter.coe_to_sublitter (L : litter) :
  (L.to_sublitter : set atom) = litter_set L := rfl

namespace sublitter

def rel_embedding (S : sublitter) :
  ((<) : S → S → Prop) ↪r ((<) : (litter_set S.litter) → (litter_set S.litter) → Prop) :=
⟨⟨λ a, ⟨a, S.subset a.prop⟩, λ a b h, subtype.coe_injective (subtype.mk_eq_mk.mp h)⟩,
  λ a b, by simp only [function.embedding.coe_fn_mk, subtype.mk_lt_mk, subtype.coe_lt_coe]⟩

/-- The order type of a sublitter is `κ`. -/
lemma ordinal_type (S : sublitter) : ordinal.type ((<) : S → S → Prop) = (#κ).ord :=
begin
  refine le_antisymm _ _,
  { rw ← S.litter.ordinal_type,
    exact rel_embedding.ordinal_type_le S.rel_embedding, },
  { rw [cardinal.gc_ord_card, ordinal.card_type, mk_eq_κ], },
end

-- TODO: We can probably do this constructively, but this way is easier for now.
noncomputable def order_iso_κ (S : sublitter) : S ≃o κ :=
begin
  refine order_iso.of_rel_iso_lt (nonempty.some _),
  rw [← ordinal.type_eq, ordinal_type, ← κ_ord],
  refl,
end

/-- There is a (unique) order isomorphism between any two sublitters. -/
noncomputable def order_iso (S T : sublitter) : S ≃o T :=
S.order_iso_κ.trans T.order_iso_κ.symm

@[simp] lemma order_iso_apply_mem {S T : sublitter} (a : S) : (S.order_iso T a : atom) ∈ T :=
(S.order_iso T a).prop

def order_iso.subtype_iso {α β : Type*} [has_le α] [has_le β] (e : α ≃o β)
  {p : α → Prop} {q : β → Prop} (hpq : ∀ a, p a ↔ q (e a)) :
  {a // p a} ≃o {b // q b} :=
⟨e.subtype_equiv hpq, by simp only [rel_iso.coe_fn_to_equiv, equiv.subtype_equiv_apply,
  subtype.mk_le_mk, order_iso.le_iff_le, subtype.coe_le_coe, iff_self, subtype.forall,
  implies_true_iff]⟩

/-- There is a unique order isomorphism between corresponding subtypes of a well-order. -/
lemma order_iso.unique {α β : Type*}
  [linear_order α] [αwf : well_founded ((<) : α → α → Prop)]
  [linear_order β] [βwf : well_founded ((<) : β → β → Prop)]
  (e : α ≃o β) {p : α → Prop} {q : β → Prop}
  (hpq : ∀ a, p a ↔ q (e a)) (e' : {a // p a} ≃o {b // q b}) :
  e' = e.subtype_iso hpq :=
begin
  ext x,
  obtain ⟨x, hx⟩ := x,
  revert hx,
  refine αwf.induction x _,
  intros x ih hx,
  rw subtype.coe_inj,
  refine linarith.eq_of_not_lt_of_not_gt _ _ (λ h, _) (λ h, _),
  { have := ih ((e.subtype_iso hpq).symm (e' ⟨x, hx⟩)) _ _,
    { simp only [subtype.coe_eta, order_iso.apply_symm_apply, subtype.coe_inj,
        order_iso.apply_eq_iff_eq, order_iso.symm_apply_eq] at this,
      exact h.ne this, },
    { refine lt_of_lt_of_eq _ (subtype.coe_mk x hx),
      have := (e.subtype_iso hpq).symm.strict_mono h,
      rw order_iso.symm_apply_apply at this,
      exact this, },
    { exact subtype.coe_prop _, }, },
  { have := ih (e'.symm (e.subtype_iso hpq ⟨x, hx⟩)) _ _,
    { simp only [subtype.coe_eta, order_iso.apply_symm_apply, subtype.coe_inj,
        order_iso.apply_eq_iff_eq, order_iso.symm_apply_eq] at this,
      have := h.trans_eq (congr_arg e' this),
      rw order_iso.apply_symm_apply at this,
      exact this.ne rfl, },
    { refine lt_of_lt_of_eq _ (subtype.coe_mk x hx),
      have := e'.symm.strict_mono h,
      rw order_iso.symm_apply_apply at this,
      exact this, },
    { exact subtype.coe_prop _, }, },
end

/-- The intersection of two sublitters. -/
def meet (S T : sublitter) (h : S.litter = T.litter) : sublitter := {
  litter := S.litter,
  carrier := S ∩ T,
  subset := (set.inter_subset_left _ _).trans S.subset,
  diff_small := by rw set.diff_inter; exact small.union S.diff_small (h.symm ▸ T.diff_small),
}

/-- Transports the meet of sublitters `S` and `U` across the order isomorphism `S ≃o T`. -/
def order_iso_meet (S T U : sublitter) (h : S.litter = U.litter) : sublitter := {
  litter := T.litter,
  carrier := {a | ∃ (ha : a ∈ T), ((S.order_iso T).symm ⟨a, ha⟩ : atom) ∈ U},
  subset := λ a ha, T.subset ha.some,
  diff_small := begin
    suffices : small ((T : set atom) \
      {a | ∃ (ha : a ∈ T), ((S.order_iso T).symm ⟨a, ha⟩ : atom) ∈ U}),
    { refine small.mono (λ a ha, _) (small.union T.diff_small this),
      by_cases a ∈ T,
      exact or.inr ⟨h, ha.2⟩,
      exact or.inl ⟨ha.1, h⟩, },
    refine lt_of_le_of_lt _ U.diff_small,
    refine ⟨⟨λ a, ⟨(S.order_iso T).symm ⟨a, a.prop.1⟩, _, _⟩, λ a b h, _⟩⟩,
    { rw ← h,
      exact S.subset ((S.order_iso T).symm ⟨a, a.prop.1⟩).2, },
    { intro h,
      exact a.prop.2 ⟨a.prop.1, h⟩, },
    { simpa only [subtype.mk_eq_mk, rel_iso.eq_iff_eq, subtype.coe_inj] using h, },
  end,
}

end sublitter

end con_nf
