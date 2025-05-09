import ConNF.Model.Result

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal ConNF.TSet

namespace ConNF

variable [Params.{u}] {α β γ δ ε ζ : Λ} (hβ : (β : TypeIndex) < α) (hγ : (γ : TypeIndex) < β)
  (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < δ) (hζ : (ζ : TypeIndex) < ε)

theorem inter_comm (x y : TSet α) :
    x ⊓' y = y ⊓' x := by
  apply ext hβ
  intro z
  rw [mem_inter_iff, mem_inter_iff]
  exact And.comm

def union (x y : TSet α) : TSet α :=
  (xᶜ' ⊓' yᶜ')ᶜ'

notation:68 x:68 " ⊔[" h "] " y:68 => _root_.ConNF.union h x y
notation:68 x:68 " ⊔' " y:68 => x ⊔[by assumption] y

@[simp]
theorem mem_union_iff (x y : TSet α) :
    ∀ z : TSet β, z ∈' x ⊔' y ↔ z ∈' x ∨ z ∈' y := by
  rw [union]
  intro z
  rw [mem_compl_iff, mem_inter_iff, mem_compl_iff, mem_compl_iff, or_iff_not_and_not]

theorem union_comm (x y : TSet α) :
    x ⊔' y = y ⊔' x := by
  apply ext hβ
  intro z
  rw [mem_union_iff, mem_union_iff]
  exact Or.comm

def symmDiff (x y : TSet α) : TSet α :=
  (x ⊓' yᶜ') ⊔' (xᶜ' ⊓' y)

notation:100 x:100 " ∆[" h "] " y:100 => _root_.ConNF.symmDiff h x y
notation:100 x:100 " ∆' " y:100 => x ∆[by assumption] y

@[simp]
theorem mem_symmDiff_iff (x y : TSet α) :
    ∀ z : TSet β, z ∈' x ∆' y ↔ (z ∈' x ↔ ¬(z ∈' y)) := by
  rw [symmDiff]
  intro z
  simp only [mem_union_iff, mem_inter_iff, mem_compl_iff]
  tauto

def diff (x y : TSet α) : TSet α :=
  x ⊓' yᶜ'

notation:70 x:70 " \\[" h "] " y:70 => _root_.ConNF.diff h x y
notation:70 x:70 " \\' " y:70 => x \[by assumption] y

@[simp]
theorem mem_diff_iff (x y : TSet α) :
    ∀ z : TSet β, z ∈' x \' y ↔ z ∈' x ∧ ¬(z ∈' y) := by
  rw [diff]
  intro z
  simp only [mem_union_iff, mem_inter_iff, mem_compl_iff]

def higherIndex (α : Λ) : Λ :=
  (exists_gt α).choose

/-- A short name is chosen because of its frequency of use. -/
theorem high {α : Λ} :
    (α : TypeIndex) < higherIndex α :=
  WithBot.coe_lt_coe.mpr (exists_gt α).choose_spec

theorem tSet_nonempty (h : ∃ β : Λ, (β : TypeIndex) < α) : Nonempty (TSet α) := by
  obtain ⟨α', hα⟩ := h
  constructor
  apply typeLower high high high hα
  apply cardinalOne high high

def empty : TSet α :=
  (tSet_nonempty ⟨β, hβ⟩).some ⊓' (tSet_nonempty ⟨β, hβ⟩).someᶜ'

@[simp]
theorem mem_empty_iff :
    ∀ x : TSet β, ¬x ∈' empty hβ := by
  intro x
  rw [empty, mem_inter_iff, mem_compl_iff]
  exact and_not_self

def univ : TSet α :=
  (empty hβ)ᶜ'

@[simp]
theorem mem_univ_iff :
    ∀ x : TSet β, x ∈' univ hβ := by
  intro x
  simp only [univ, mem_compl_iff, mem_empty_iff, not_false_eq_true]

/-- The set of all ordered pairs. -/
def orderedPairs : TSet α :=
  vCross hβ hγ hδ (univ hδ)

@[simp]
theorem mem_orderedPairs_iff (x : TSet β) :
    x ∈' orderedPairs hβ hγ hδ ↔ ∃ a b, x = ⟨a, b⟩' := by
  simp only [orderedPairs, mem_vCross_iff, mem_univ_iff, and_true]

def converse (x : TSet α) : TSet α :=
  converse' hβ hγ hδ x ⊓' orderedPairs hβ hγ hδ

@[simp]
theorem op_mem_converse_iff (x : TSet α) :
    ∀ a b, ⟨a, b⟩' ∈' converse hβ hγ hδ x ↔ ⟨b, a⟩' ∈' x := by
  intro a b
  simp only [converse, mem_inter_iff, converse'_spec, mem_orderedPairs_iff, op_inj, exists_and_left,
    exists_eq', and_true]

def cross (x y : TSet γ) : TSet α :=
  converse hβ hγ hδ (vCross hβ hγ hδ x) ⊓' vCross hβ hγ hδ y

@[simp]
theorem mem_cross_iff (x y : TSet γ) :
    ∀ a, a ∈' cross hβ hγ hδ x y ↔ ∃ b c, a = ⟨b, c⟩' ∧ b ∈' x ∧ c ∈' y := by
  intro a
  rw [cross, mem_inter_iff, mem_vCross_iff]
  constructor
  · rintro ⟨h₁, b, c, rfl, h₂⟩
    simp only [op_mem_converse_iff, mem_vCross_iff, op_inj] at h₁
    obtain ⟨b', c', ⟨rfl, rfl⟩, h₁⟩ := h₁
    exact ⟨b, c, rfl, h₁, h₂⟩
  · rintro ⟨b, c, rfl, h₁, h₂⟩
    simp only [op_mem_converse_iff, mem_vCross_iff, op_inj]
    exact ⟨⟨c, b, ⟨rfl, rfl⟩, h₁⟩, ⟨b, c, ⟨rfl, rfl⟩, h₂⟩⟩

def singletonImage (x : TSet β) : TSet α :=
  singletonImage' hβ hγ hδ hε x ⊓' (cross hβ hγ hδ (cardinalOne hδ hε) (cardinalOne hδ hε))

@[simp]
theorem singletonImage_spec (x : TSet β) :
    ∀ z w,
    ⟨ {z}', {w}' ⟩' ∈' singletonImage hβ hγ hδ hε x ↔ ⟨z, w⟩' ∈' x := by
  intro z w
  rw [singletonImage, mem_inter_iff, singletonImage'_spec, and_iff_left_iff_imp]
  intro hzw
  rw [mem_cross_iff]
  refine ⟨{z}', {w}', rfl, ?_⟩
  simp only [mem_cardinalOne_iff, singleton_inj, exists_eq', and_self]

theorem exists_of_mem_singletonImage {x : TSet β} {z w : TSet δ}
    (h : ⟨z, w⟩' ∈' singletonImage hβ hγ hδ hε x) :
    ∃ a b, z = {a}' ∧ w = {b}' := by
  simp only [singletonImage, mem_inter_iff, mem_cross_iff, op_inj, mem_cardinalOne_iff] at h
  obtain ⟨-, _, _, ⟨rfl, rfl⟩, ⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
  exact ⟨a, b, rfl, rfl⟩

/-- Turn a model element encoding a relation into an actual relation. -/
def ExternalRel (r : TSet α) : Rel (TSet δ) (TSet δ) :=
  λ x y ↦ ⟨x, y⟩' ∈' r

@[simp]
theorem externalRel_converse (r : TSet α) :
    ExternalRel hβ hγ hδ (converse hβ hγ hδ r) = (ExternalRel hβ hγ hδ r).inv := by
  ext
  simp only [ExternalRel, op_mem_converse_iff, Rel.inv_apply]

/-- The codomain of a relation. -/
def codom (r : TSet α) : TSet γ :=
  (typeLower high hβ hγ hδ (singletonImage high hβ hγ hδ r)ᶜ[high])ᶜ'

@[simp]
theorem mem_codom_iff (r : TSet α) (x : TSet δ) :
    x ∈' codom hβ hγ hδ r ↔ x ∈ (ExternalRel hβ hγ hδ r).codom := by
  simp only [codom, mem_compl_iff, mem_typeLower_iff, not_forall, not_not]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, b, rfl, hb⟩ := exists_of_mem_singletonImage high hβ hγ hδ hy
    rw [singleton_inj] at hb
    subst hb
    rw [singletonImage_spec] at hy
    exact ⟨a, hy⟩
  · rintro ⟨a, ha⟩
    use {a}'
    rw [singletonImage_spec]
    exact ha

/-- The domain of a relation. -/
def dom (r : TSet α) : TSet γ :=
  codom hβ hγ hδ (converse hβ hγ hδ r)

@[simp]
theorem mem_dom_iff (r : TSet α) (x : TSet δ) :
    x ∈' dom hβ hγ hδ r ↔ x ∈ (ExternalRel hβ hγ hδ r).dom := by
  rw [dom, mem_codom_iff, externalRel_converse, Rel.inv_codom]

/-- The field of a relation. -/
def field (r : TSet α) : TSet γ :=
  dom hβ hγ hδ r ⊔' codom hβ hγ hδ r

@[simp]
theorem mem_field_iff (r : TSet α) (x : TSet δ) :
    x ∈' field hβ hγ hδ r ↔ x ∈ (ExternalRel hβ hγ hδ r).field := by
  rw [field, mem_union_iff, mem_dom_iff, mem_codom_iff, Rel.field, Set.mem_union]

def subset : TSet α :=
  subset' hβ hγ hδ hε ⊓' orderedPairs hβ hγ hδ

@[simp]
theorem subset_spec :
    ∀ a b, ⟨a, b⟩' ∈' subset hβ hγ hδ hε ↔ a ⊆[TSet ε] b := by
  intro a b
  simp only [subset, mem_inter_iff, subset'_spec, mem_orderedPairs_iff, op_inj, exists_and_left,
    exists_eq', and_true]

@[simp]
theorem singleton_subset_iff (a : TSet β) (b : TSet α) :
    {a}' ⊆[TSet β] b ↔ a ∈' b := by
  constructor
  · intro h
    apply h a
    rw [typedMem_singleton_iff']
  · intro h x hx
    rw [typedMem_singleton_iff'] at hx
    cases hx
    exact h

def membership : TSet α :=
  subset hβ hγ hδ hε ⊓' cross hβ hγ hδ (cardinalOne hδ hε) (univ hδ)

@[simp]
theorem membership_spec :
    ∀ a b, ⟨{a}', b⟩' ∈' membership hβ hγ hδ hε ↔ a ∈' b := by
  intro a b
  rw [membership, mem_inter_iff, subset_spec]
  simp only [mem_cross_iff, op_inj, mem_cardinalOne_iff, mem_univ_iff, and_true, exists_and_right,
    exists_and_left, exists_eq', exists_eq_left', singleton_inj]
  constructor
  · intro h
    exact h a ((typedMem_singleton_iff' hε a a).mpr rfl)
  · intro h c hc
    simp only [typedMem_singleton_iff'] at hc
    cases hc
    exact h

def powerset (x : TSet β) : TSet α :=
  dom high high hβ
    (subset high high hβ hγ ⊓[high]
      vCross high high hβ {x}')

@[simp]
theorem mem_powerset_iff (x y : TSet β) :
    x ∈' powerset hβ hγ y ↔ x ⊆[TSet γ] y := by
  rw [powerset, mem_dom_iff]
  constructor
  · rintro ⟨z, h⟩
    simp only [ExternalRel, mem_inter_iff, subset_spec, mem_vCross_iff, op_inj,
      typedMem_singleton_iff', exists_eq_right, exists_and_right, exists_eq', true_and] at h
    cases h.2
    exact h.1
  · intro h
    refine ⟨y, ?_⟩
    simp only [ExternalRel, mem_inter_iff, subset_spec, h, mem_vCross_iff, op_inj,
      typedMem_singleton_iff', exists_eq_right, and_true, exists_eq', and_self]

/-- The set `ι²''x = {{{a}} | a ∈ x}`. -/
def doubleSingletons (x : TSet γ) : TSet α :=
  cross hβ hγ hδ x x ⊓' cardinalOne hβ hγ

@[simp]
theorem mem_doubleSingletons_iff (x : TSet γ) :
    ∀ y : TSet β, y ∈' doubleSingletons hβ hγ hδ x ↔
    ∃ z : TSet δ, z ∈' x ∧ y = { {z}' }' := by
  intro y
  rw [doubleSingletons, mem_inter_iff, mem_cross_iff, mem_cardinalOne_iff]
  constructor
  · rintro ⟨⟨b, c, h₁, h₂, h₃⟩, ⟨a, rfl⟩⟩
    obtain ⟨hbc, rfl⟩ := (op_eq_singleton_iff _ _ _ _ _).mp h₁.symm
    exact ⟨c, h₃, rfl⟩
  · rintro ⟨z, h, rfl⟩
    constructor
    · refine ⟨z, z, ?_⟩
      rw [eq_comm, op_eq_singleton_iff]
      tauto
    · exact ⟨_, rfl⟩

/-- The union of a set of *singletons*: `ι⁻¹''x = {a | {a} ∈ x}`.
Scott Fenton calls this the "unit union". -/
def singletonUnion (x : TSet α) : TSet β :=
  typeLower high high hβ hγ
    (vCross high high hβ x)

@[simp]
theorem mem_singletonUnion_iff (x : TSet α) :
    ∀ y : TSet γ, y ∈' singletonUnion hβ hγ x ↔ {y}' ∈' x := by
  intro y
  simp only [singletonUnion, mem_typeLower_iff, mem_vCross_iff, op_inj]
  constructor
  · intro h
    obtain ⟨a, b, ⟨rfl, rfl⟩, hy⟩ := h {y}'
    exact hy
  · intro h b
    exact ⟨b, _, ⟨rfl, rfl⟩, h⟩

/-- The set of singletons of a set: `ι''x = {{a} | a ∈ x}`.
Scott Fenton calls this the "unit powerset". -/
def singletons (x : TSet β) : TSet α :=
  singletonUnion high hβ (doubleSingletons high hβ hγ x)

@[simp]
theorem mem_singletons_iff (x : TSet β) :
    ∀ y : TSet β, y ∈' singletons hβ hγ x ↔ ∃ t : TSet γ, t ∈' x ∧ y = {t}' := by
  intro y
  simp only [singletons, mem_singletonUnion_iff, mem_doubleSingletons_iff, singleton_inj]

/--
The union of a set of sets.

```
⋃ x =
{a | a ∈ b ∧ b ∈ x} =
singletonUnion {{a} | a ∈ b ∧ b ∈ x} =
singletonUnion dom {⟨{a}, b⟩ | a ∈ b ∧ b ∈ x} =
singletonUnion dom ({⟨{a}, b⟩ | a ∈ b} ∩ (1 × x))
```
-/
def sUnion (x : TSet α) : TSet β :=
  singletonUnion hβ hγ <|
  dom high high hβ <|
  membership high high hβ hγ ⊓[high]
    cross high high hβ (cardinalOne hβ hγ) x

@[simp]
theorem mem_sUnion_iff (x : TSet α) :
    ∀ y : TSet γ, y ∈' sUnion hβ hγ x ↔ ∃ t : TSet β, t ∈' x ∧ y ∈' t := by
  intro y
  simp only [sUnion, mem_singletonUnion_iff, mem_dom_iff, Rel.dom, ExternalRel, mem_inter_iff,
    mem_cross_iff, op_inj, mem_cardinalOne_iff, Set.mem_setOf_eq, membership_spec]
  constructor
  · rintro ⟨z, h₁, a, b, ⟨rfl, rfl⟩, ⟨c, h₂⟩, h₃⟩
    rw [singleton_inj] at h₂
    cases h₂
    exact ⟨z, h₃, h₁⟩
  · rintro ⟨z, h₂, h₃⟩
    exact ⟨z, h₃, _, _, ⟨rfl, rfl⟩, ⟨y, rfl⟩, h₂⟩

/-- The set of all ordered triples. -/
def orderedTriples : TSet α :=
  cross hβ hγ hδ (doubleSingletons hδ hε hζ (univ hζ)) (vCross hδ hε hζ (univ hζ))

@[simp]
theorem mem_orderedTriples_iff (x : TSet β) :
    x ∈' orderedTriples hβ hγ hδ hε hζ ↔ ∃ a b c, x = ⟨ { {a}' }', ⟨b, c⟩' ⟩' := by
  simp only [orderedTriples, mem_cross_iff, mem_doubleSingletons_iff, mem_univ_iff, true_and,
    mem_vCross_iff, and_true]
  constructor
  · rintro ⟨_, _, rfl, ⟨a, rfl⟩, ⟨b, c, rfl⟩⟩
    exact ⟨_, _, _, rfl⟩
  · rintro ⟨a, b, c, rfl⟩
    exact ⟨_, _, rfl, ⟨_, rfl⟩, ⟨_, _, rfl⟩⟩

def insertion2 (x : TSet γ) : TSet α :=
  insertion2' hβ hγ hδ hε hζ x ⊓' orderedTriples hβ hγ hδ hε hζ

@[simp]
theorem insertion2_spec (x : TSet γ) :
    ∀ a b c, ⟨ { {a}' }', ⟨b, c⟩' ⟩' ∈' insertion2 hβ hγ hδ hε hζ x ↔
    ⟨a, c⟩' ∈' x := by
  simp only [insertion2, mem_inter_iff, insertion2'_spec, mem_orderedTriples_iff, op_inj,
    singleton_inj, exists_and_left, exists_eq', and_true, implies_true]

def insertion3 (x : TSet γ) : TSet α :=
  insertion3' hβ hγ hδ hε hζ x ⊓' orderedTriples hβ hγ hδ hε hζ

@[simp]
theorem insertion3_spec (x : TSet γ) :
    ∀ a b c, ⟨ { {a}' }', ⟨b, c⟩' ⟩' ∈' insertion3 hβ hγ hδ hε hζ x ↔
    ⟨a, b⟩' ∈' x := by
  simp only [insertion3, mem_inter_iff, insertion3'_spec, mem_orderedTriples_iff, op_inj,
    singleton_inj, exists_and_left, exists_eq', and_true, implies_true]

/-- The preimage of a set under a relation. -/
def preimage (r : TSet α) (x : TSet γ) : TSet γ :=
  dom hβ hγ hδ (r ⊓' vCross hβ hγ hδ x)

@[simp]
theorem mem_preimage_iff (r : TSet α) (x : TSet γ) (y : TSet δ) :
    y ∈' preimage hβ hγ hδ r x ↔ y ∈ (ExternalRel hβ hγ hδ r).preimage {a | a ∈' x} := by
  simp only [preimage, mem_dom_iff, Rel.dom, ExternalRel, mem_inter_iff, mem_vCross_iff, op_inj,
    Set.mem_setOf_eq, Rel.preimage, Rel.image, Rel.inv, flip]
  constructor
  · rintro ⟨a, h₁, _, _, ⟨rfl, rfl⟩, h₂⟩
    exact ⟨a, h₂, h₁⟩
  · rintro ⟨a, h₁, h₂⟩
    exact ⟨a, h₂, _, _, ⟨rfl, rfl⟩, h₁⟩

/-- The image of a set under a relation. -/
def image (r : TSet α) (x : TSet γ) : TSet γ :=
  preimage hβ hγ hδ (converse hβ hγ hδ r) x

@[simp]
theorem mem_image_iff (r : TSet α) (x : TSet γ) (y : TSet δ) :
    y ∈' image hβ hγ hδ r x ↔ y ∈ (ExternalRel hβ hγ hδ r).image {a | a ∈' x} := by
  simp only [image, mem_preimage_iff, externalRel_converse, Rel.preimage_inv]

theorem exists_smallUnion (s : Set (TSet α)) (hs : Small s) :
    ∃ x : TSet α, ∀ y : TSet β, y ∈' x ↔ ∃ t ∈ s, y ∈' t := by
  apply exists_of_symmetric
  have := exists_support (α := α)
  choose S hS using this
  refine ⟨⟨Enumeration.ofSet (⋃ t ∈ s, (S t)ᴬ) ?_, Enumeration.ofSet (⋃ t ∈ s, (S t)ᴺ) ?_⟩, ?_⟩
  · apply small_biUnion hs
    intros
    exact (S _)ᴬ.coe_small
  · apply small_biUnion hs
    intros
    exact (S _)ᴺ.coe_small
  intro ρ hρ
  suffices ∀ t ∈ s, ρ • t = t by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    constructor
    · rintro ⟨t, h₁, h₂⟩
      refine ⟨t, h₁, ?_⟩
      rw [← this t h₁]
      rwa [mem_smul_iff', allPerm_inv_sderiv']
    · rintro ⟨t, h₁, h₂⟩
      refine ⟨t, h₁, ?_⟩
      have := this t h₁
      rw [smul_eq_iff_eq_inv_smul] at this
      rwa [this, mem_smul_iff', inv_inv, smul_inv_smul]
  intro t ht
  apply (hS t).supports ρ
  refine smul_eq_of_le ?_ hρ
  intro A
  constructor
  · intro a ha
    rw [← Support.derivBot_atoms, Support.mk_atoms, ← Enumeration.mem_path_iff,
      Enumeration.mem_ofSet_iff, Set.mem_iUnion]
    use t
    rw [Set.mem_iUnion]
    use ht
    exact ha
  · intro a ha
    rw [← Support.derivBot_nearLitters, Support.mk_nearLitters, ← Enumeration.mem_path_iff,
      Enumeration.mem_ofSet_iff, Set.mem_iUnion]
    use t
    rw [Set.mem_iUnion]
    use ht
    exact ha

/-- Our model is `κ`-complete; small unions exist.
In particular, the model knows the correct natural numbers. -/
def smallUnion (s : Set (TSet α)) (hs : Small s) : TSet α :=
  (exists_smallUnion hβ s hs).choose

@[simp]
theorem mem_smallUnion_iff (s : Set (TSet α)) (hs : Small s) :
    ∀ x : TSet β, x ∈' smallUnion hβ s hs ↔ ∃ t ∈ s, x ∈' t :=
  (exists_smallUnion hβ s hs).choose_spec

end ConNF
