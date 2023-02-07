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

lemma mk_eq_κ (S : sublitter) : #S = #κ := S.mk_S_eq_κ
lemma mk_eq_κ' (S : sublitter) : #(S : set atom) = #κ := S.mk_S_eq_κ

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

end con_nf
