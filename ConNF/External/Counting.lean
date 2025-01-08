import ConNF.External.Basic

/-!
# New file

In this file...

We are roughly following Scott Fenton's development of NF:
<https://us.metamath.org/nfeuni/mmnf.html>.

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal ConNF.TSet

namespace ConNF

variable [Params.{u}] {α β γ δ ε ζ η : Λ} (hβ : (β : TypeIndex) < α) (hγ : (γ : TypeIndex) < β)
  (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < δ) (hζ : (ζ : TypeIndex) < ε)
  (hη : (η : TypeIndex) < ζ)

-- ((( Ins3k disjoint) ∖
--   (( Ins2k Ins2k Sk ⊕ ( Ins2k Ins3k Sk ∪ Ins3k SIk SIk Sk )) “k ℘1℘1℘1℘11c)) “k ℘1℘1B) “k A)

-- ( Ins2k Ins2k Sk ⊕ ( Ins2k Ins3k Sk ∪ Ins3k SIk SIk Sk ))

/-- The set `{⟨x, y⟩ | x ∩ y = ∅}` (or rather, a set that contains only these Kuratowski pairs). -/
def disjoint : TSet α :=
  (image high high hβ
    (insertion3 high high hβ hγ hδ (subset hβ hγ hδ hε) ⊓[high]
      insertion2 high high hβ hγ hδ (subset hβ hγ hδ hε))
    (singletons hβ hγ (singletons hγ hδ (cardinalOne hδ hε))))ᶜ'

theorem mem_disjoint_iff' (x y : TSet δ) :
    ⟨x, y⟩' ∈' disjoint hβ hγ hδ hε ↔ ∀ z : TSet ε, ¬z ∈' x ⊓' y := by
  simp only [disjoint, mem_compl_iff, mem_image_iff, Rel.image, mem_singletons_iff,
    mem_cardinalOne_iff, Set.mem_setOf_eq, ExternalRel, mem_inter_iff, not_exists, not_and,
    forall_exists_index, and_imp, forall_eq_apply_imp_iff, insertion3_spec, subset_spec,
    singleton_subset_iff, insertion2_spec]

@[simp]
theorem mem_disjoint_iff (x y : TSet δ) :
    ⟨x, y⟩' ∈' disjoint hβ hγ hδ hε ↔ x ⊓' y = empty hε := by
  rw [mem_disjoint_iff']
  constructor
  · intro h
    apply ext hε
    simp only [h, mem_empty_iff, implies_true]
  · intro h
    rw [← ext_iff hε] at h
    simp only [h, mem_empty_iff, not_false_eq_true, implies_true]

/-- The set `{⟨{{z}}, ⟨y, x⟩ | y ∪ z = x}` (or rather, again,
a set that contains only these pairs). -/
def unionEq : TSet α :=
  (image high high hβ
    (insertion2 high high hβ hγ hδ (insertion2 hβ hγ hδ hε hζ (subset hδ hε hζ hη)) ∆[high]
      (insertion2 high high hβ hγ hδ (insertion3 hβ hγ hδ hε hζ (subset hδ hε hζ hη)) ⊔[high]
      insertion3 high high hβ hγ hδ (singletonImage hβ hγ hδ hε
        (singletonImage hγ hδ hε hζ (subset hδ hε hζ hη)))))
    (singletons hβ hγ (singletons hγ hδ (singletons hδ hε
      (singletons hε hζ (cardinalOne hζ hη))))))ᶜ'

theorem mem_unionEq_iff' (x y z : TSet ζ) :
    ⟨ { {z}' }', ⟨y, x⟩' ⟩[hγ, hδ] ∈' unionEq hβ hγ hδ hε hζ hη ↔
      ∀ a : TSet η, ¬(a ∈' x ↔ ¬a ∈' y ∧ ¬a ∈' z) := by
  simp only [unionEq, mem_compl_iff, mem_image_iff, Rel.image, mem_singletons_iff,
    mem_cardinalOne_iff, Set.mem_setOf_eq, ExternalRel, mem_symmDiff_iff, mem_union_iff, not_or,
    not_exists, not_and, forall_exists_index, and_imp, forall_eq_apply_imp_iff, insertion2_spec,
    subset_spec, singleton_subset_iff, insertion3_spec, singletonImage_spec]

@[simp]
theorem mem_unionEq_iff (x y z : TSet ζ) :
    ⟨ { {z}' }', ⟨y, x⟩' ⟩[hγ, hδ] ∈' unionEq hβ hγ hδ hε hζ hη ↔ y ⊔' z = x := by
  rw [mem_unionEq_iff']
  constructor
  · intro h
    apply ext hη
    intro t
    rw [mem_union_iff]
    have := h t
    rw [iff_comm, not_iff, not_and_or, not_not, not_not] at this
    exact this
  · rintro rfl a
    rw [iff_comm, not_iff, not_and_or, not_not, not_not, mem_union_iff]

/-- The sum of two cardinals: `x + y = {a ∪ b | a ∈ x ∧ b ∈ y ∧ a ∩ b = ∅}`. -/
def cardAdd (x y : TSet α) : TSet α :=
  image high high hβ
    (image high high high
      (insertion3 high high high high hβ (disjoint high high hβ hγ)
        ⊓[high] (unionEq high high high high hβ hγ))
      (singletons high high (singletons high hβ y))) x

@[simp]
theorem mem_cardAdd_iff (x y : TSet α) (z : TSet β) :
    z ∈' cardAdd hβ hγ x y ↔
    ∃ a b : TSet β, a ∈' x ∧ b ∈' y ∧ a ⊓' b = empty hγ ∧ a ⊔' b = z := by
  simp only [cardAdd, mem_image_iff, Rel.image, Set.mem_setOf_eq, ExternalRel, mem_singletons_iff,
    mem_inter_iff, exists_and_left]
  constructor
  · rintro ⟨a, ha, _, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, h₁, h₂⟩
    rw [insertion3_spec, mem_disjoint_iff] at h₁
    rw [mem_unionEq_iff] at h₂
    cases h₂
    rw [inter_comm] at h₁
    exact ⟨a, ha, b, hb, h₁, rfl⟩
  · rintro ⟨a, ha, b, hb, h, rfl⟩
    refine ⟨a, ha, _, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
    simp only [insertion3_spec, mem_disjoint_iff, mem_unionEq_iff, and_true]
    rwa [inter_comm]

/-- The successor of a cardinal: `x + 1 = {a ∪ {b} | a ∈ x, b ∉ a}`. -/
def succ (x : TSet α) : TSet α := sorry

def cardinalNat (n : ℕ) : TSet α :=
  (TSet.exists_cardinalOne hβ hγ).choose

@[simp]
theorem mem_cardinalNat_iff (n : ℕ) :
    ∀ a : TSet β, a ∈' cardinalNat hβ hγ n ↔
    ∃ s : Finset (TSet γ), s.card = n ∧ ∀ b : TSet γ, b ∈' a ↔ b ∈ s :=
  sorry

end ConNF
