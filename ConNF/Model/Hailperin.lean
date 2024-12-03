import ConNF.Model.TTT

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] {α β γ δ ε ζ : Λ} (hβ : (β : TypeIndex) < α) (hγ : (γ : TypeIndex) < β)
  (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < δ) (hζ : (ζ : TypeIndex) < ε)

namespace TSet

theorem exists_inter (x y : TSet α) :
    ∃ w : TSet α, ∀ z : TSet β, z ∈[hβ] w ↔ z ∈[hβ] x ∧ z ∈[hβ] y := by
  refine exists_of_symmetric {z | z ∈[hβ] x ∧ z ∈[hβ] y} hβ ?_
  obtain ⟨S, hS⟩ := symmetric x hβ
  obtain ⟨T, hT⟩ := symmetric y hβ
  use S + T
  intro ρ hρ
  specialize hS ρ (smul_eq_of_le Support.le_add_right hρ)
  specialize hT ρ (smul_eq_of_le Support.le_add_left hρ)
  simp [Set.ext_iff, Set.mem_smul_set_iff_inv_smul_mem] at hS hT ⊢
  aesop

theorem exists_compl (x : TSet α) :
    ∃ y : TSet α, ∀ z : TSet β, z ∈[hβ] y ↔ ¬z ∈[hβ] x := by
  refine exists_of_symmetric {z | ¬z ∈[hβ] x} hβ ?_
  obtain ⟨S, hS⟩ := symmetric x hβ
  use S
  intro ρ hρ
  specialize hS ρ hρ
  simp [Set.ext_iff, Set.mem_smul_set_iff_inv_smul_mem] at hS ⊢
  aesop

theorem exists_up (x y : TSet β) :
    ∃ w : TSet α, ∀ z : TSet β, z ∈[hβ] w ↔ z = x ∨ z = y := by
  refine exists_of_symmetric {x, y} hβ ?_
  obtain ⟨S, hS⟩ := exists_support x
  obtain ⟨T, hT⟩ := exists_support y
  use (S + T) ↗ hβ
  intro ρ hρ
  rw [Support.smul_scoderiv, Support.scoderiv_inj, ← allPermSderiv_forget'] at hρ
  specialize hS (ρ ↘ hβ) (smul_eq_of_le Support.le_add_right hρ)
  specialize hT (ρ ↘ hβ) (smul_eq_of_le Support.le_add_left hρ)
  simp only [Set.smul_set_def, Set.image, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, hS, exists_eq_left, hT]
  ext z
  rw [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  aesop

/-- The unordered pair. -/
def up (x y : TSet β) : TSet α :=
  (exists_up hβ x y).choose

@[simp]
theorem mem_up_iff (x y z : TSet β) :
    z ∈[hβ] up hβ x y ↔ z = x ∨ z = y :=
  (exists_up hβ x y).choose_spec z

/-- The Kuratowski ordered pair. -/
def op (x y : TSet γ) : TSet α :=
  up hβ (singleton hγ x) (up hγ x y)

theorem up_injective {x y z w : TSet β} (h : up hβ x y = up hβ z w) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  have h₁ := mem_up_iff hβ x y z
  have h₂ := mem_up_iff hβ x y w
  have h₃ := mem_up_iff hβ z w x
  have h₄ := mem_up_iff hβ z w y
  rw [h, mem_up_iff] at h₁ h₂
  rw [← h, mem_up_iff] at h₃ h₄
  aesop

@[simp]
theorem up_inj (x y z w : TSet β) :
    up hβ x y = up hβ z w ↔ (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  constructor
  · exact up_injective hβ
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · apply tSet_ext' hβ
      aesop

@[simp]
theorem up_self {x : TSet β} :
    up hβ x x = singleton hβ x := by
  apply tSet_ext' hβ
  aesop

@[simp]
theorem up_eq_singleton_iff (x y z : TSet β) :
    up hβ x y = singleton hβ z ↔ x = z ∧ y = z := by
  constructor
  · intro h
    have h₁ := typedMem_singleton_iff' hβ z x
    have h₂ := typedMem_singleton_iff' hβ z y
    rw [← h, mem_up_iff] at h₁ h₂
    aesop
  · rintro ⟨rfl, rfl⟩
    rw [up_self]

@[simp]
theorem singleton_eq_up_iff (x y z : TSet β) :
    singleton hβ z = up hβ x y ↔ x = z ∧ y = z := by
  rw [← up_eq_singleton_iff hβ x y z, eq_comm]

theorem op_injective {x y z w : TSet γ} (h : op hβ hγ x y = op hβ hγ z w) :
    x = z ∧ y = w := by
  rw [op, op] at h
  simp only [up_inj, singleton_inj, singleton_eq_up_iff, up_eq_singleton_iff] at h
  obtain (⟨rfl, ⟨h, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨⟨rfl, rfl⟩, ⟨h, rfl⟩⟩) := h <;> simp only [and_self]

@[simp]
theorem op_inj (x y z w : TSet γ) :
    op hβ hγ x y = op hβ hγ z w ↔ x = z ∧ y = w := by
  constructor
  · exact op_injective hβ hγ
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem smul_up (x y : TSet β) (ρ : AllPerm α) :
    ρ • up hβ x y = up hβ (ρ ↘ hβ • x) (ρ ↘ hβ • y) := by
  apply tSet_ext' hβ
  aesop

@[simp]
theorem smul_op (x y : TSet γ) (ρ : AllPerm α) :
    ρ • op hβ hγ x y = op hβ hγ (ρ ↘ hβ ↘ hγ • x) (ρ ↘ hβ ↘ hγ • y) := by
  apply tSet_ext' hβ
  simp only [op, smul_up, smul_singleton, mem_up_iff, implies_true]

theorem exists_singletonImage (x : TSet β) :
    ∃ y : TSet α, ∀ z w,
    op hγ hδ (singleton hε z) (singleton hε w) ∈[hβ] y ↔ op hδ hε z w ∈[hγ] x := by
  have := exists_of_symmetric {u | ∃ z w : TSet ε, op hδ hε z w ∈[hγ] x ∧
      u = op hγ hδ (singleton hε z) (singleton hε w)} hβ ?_
  · obtain ⟨y, hy⟩ := this
    use y
    intro z w
    rw [hy]
    simp only [Set.mem_setOf_eq, op_inj, singleton_inj, exists_eq_right_right', exists_eq_right']
  · obtain ⟨S, hS⟩ := exists_support x
    use S ↗ hβ
    intro ρ hρ
    rw [Support.smul_scoderiv, Support.scoderiv_inj, ← allPermSderiv_forget'] at hρ
    specialize hS (ρ ↘ hβ) hρ
    ext z
    constructor
    · rintro ⟨_, ⟨z, w, hab, rfl⟩, rfl⟩
      refine ⟨ρ ↘ hβ ↘ hγ ↘ hδ ↘ hε • z, ρ ↘ hβ ↘ hγ ↘ hδ ↘ hε • w, ?_, ?_⟩
      · rwa [← hS, mem_smul_iff', smul_op, allPerm_inv_sderiv', allPerm_inv_sderiv',
          allPerm_inv_sderiv', inv_smul_smul, inv_smul_smul]
      · simp only [smul_op, smul_singleton]
    · rintro ⟨z, w, hab, rfl⟩
      refine ⟨ρ⁻¹ ↘ hβ • op hγ hδ (singleton hε z) (singleton hε w), ?_, ?_⟩
      · simp only [allPerm_inv_sderiv', smul_op, smul_singleton, Set.mem_setOf_eq, op_inj,
          singleton_inj, exists_eq_right_right', exists_eq_right']
        rw [smul_eq_iff_eq_inv_smul] at hS
        rw [hS]
        simp only [mem_smul_iff', inv_inv, smul_op, smul_inv_smul]
        exact hab
      · simp only [allPerm_inv_sderiv', smul_inv_smul]

theorem exists_insertion2 (x : TSet γ) :
    ∃ y : TSet α, ∀ a b c, op hγ hδ (singleton hε (singleton hζ a)) (op hε hζ b c) ∈[hβ] y ↔
    op hε hζ a c ∈[hδ] x := by
  have := exists_of_symmetric {u | ∃ a b c : TSet ζ, op hε hζ a c ∈[hδ] x ∧
      u = op hγ hδ (singleton hε (singleton hζ a)) (op hε hζ b c)} hβ ?_
  · obtain ⟨y, hy⟩ := this
    use y
    intro a b c
    rw [hy]
    constructor
    · rintro ⟨a', b', c', h₁, h₂⟩
      simp only [op_inj, singleton_inj] at h₂
      obtain ⟨rfl, rfl, rfl⟩ := h₂
      exact h₁
    · intro h
      exact ⟨a, b, c, h, rfl⟩
  · obtain ⟨S, hS⟩ := exists_support x
    use S ↗ hγ ↗ hβ
    intro ρ hρ
    simp only [Support.smul_scoderiv, Support.scoderiv_inj, ← allPermSderiv_forget'] at hρ
    specialize hS (ρ ↘ hβ ↘ hγ) hρ
    ext z
    constructor
    · rintro ⟨_, ⟨a, b, c, hx, rfl⟩, rfl⟩
      refine ⟨ρ ↘ hβ ↘ hγ ↘ hδ ↘ hε ↘ hζ • a, ρ ↘ hβ ↘ hγ ↘ hδ ↘ hε ↘ hζ • b,
        ρ ↘ hβ ↘ hγ ↘ hδ ↘ hε ↘ hζ • c, ?_, ?_⟩
      · rw [← hS]
        simp only [mem_smul_iff', allPerm_inv_sderiv', smul_op, inv_smul_smul]
        exact hx
      · simp only [smul_op, smul_singleton]
    · rintro ⟨a, b, c, hx, rfl⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      refine ⟨ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ ↘ hε ↘ hζ • a, ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ ↘ hε ↘ hζ • b,
        ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ ↘ hε ↘ hζ • c, ?_, ?_⟩
      · rw [smul_eq_iff_eq_inv_smul] at hS
        rw [hS, mem_smul_iff']
        simp only [inv_inv, allPerm_inv_sderiv', smul_op, smul_inv_smul]
        exact hx
      · simp only [smul_op, allPerm_inv_sderiv', smul_singleton]

theorem exists_insertion3 (x : TSet γ) :
    ∃ y : TSet α, ∀ a b c, op hγ hδ (singleton hε (singleton hζ a)) (op hε hζ b c) ∈[hβ] y ↔
    op hε hζ a b ∈[hδ] x := by
  have := exists_of_symmetric {u | ∃ a b c : TSet ζ, op hε hζ a b ∈[hδ] x ∧
      u = op hγ hδ (singleton hε (singleton hζ a)) (op hε hζ b c)} hβ ?_
  · obtain ⟨y, hy⟩ := this
    use y
    intro a b c
    rw [hy]
    constructor
    · rintro ⟨a', b', c', h₁, h₂⟩
      simp only [op_inj, singleton_inj] at h₂
      obtain ⟨rfl, rfl, rfl⟩ := h₂
      exact h₁
    · intro h
      exact ⟨a, b, c, h, rfl⟩
  · obtain ⟨S, hS⟩ := exists_support x
    use S ↗ hγ ↗ hβ
    intro ρ hρ
    simp only [Support.smul_scoderiv, Support.scoderiv_inj, ← allPermSderiv_forget'] at hρ
    specialize hS (ρ ↘ hβ ↘ hγ) hρ
    ext z
    constructor
    · rintro ⟨_, ⟨a, b, c, hx, rfl⟩, rfl⟩
      refine ⟨ρ ↘ hβ ↘ hγ ↘ hδ ↘ hε ↘ hζ • a, ρ ↘ hβ ↘ hγ ↘ hδ ↘ hε ↘ hζ • b,
        ρ ↘ hβ ↘ hγ ↘ hδ ↘ hε ↘ hζ • c, ?_, ?_⟩
      · rw [← hS]
        simp only [mem_smul_iff', allPerm_inv_sderiv', smul_op, inv_smul_smul]
        exact hx
      · simp only [smul_op, smul_singleton]
    · rintro ⟨a, b, c, hx, rfl⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      refine ⟨ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ ↘ hε ↘ hζ • a, ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ ↘ hε ↘ hζ • b,
        ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ ↘ hε ↘ hζ • c, ?_, ?_⟩
      · rw [smul_eq_iff_eq_inv_smul] at hS
        rw [hS, mem_smul_iff']
        simp only [inv_inv, allPerm_inv_sderiv', smul_op, smul_inv_smul]
        exact hx
      · simp only [smul_op, allPerm_inv_sderiv', smul_singleton]

theorem exists_cross (x : TSet γ) :
    ∃ y : TSet α, ∀ a, a ∈[hβ] y ↔ ∃ b c, a = op hγ hδ b c ∧ c ∈[hδ] x := by
  have := exists_of_symmetric {a | ∃ b c, a = op hγ hδ b c ∧ c ∈[hδ] x} hβ ?_
  · obtain ⟨y, hy⟩ := this
    use y
    intro a
    rw [hy]
    rfl
  · obtain ⟨S, hS⟩ := exists_support x
    use S ↗ hγ ↗ hβ
    intro ρ hρ
    simp only [Support.smul_scoderiv, Support.scoderiv_inj, ← allPermSderiv_forget'] at hρ
    specialize hS (ρ ↘ hβ ↘ hγ) hρ
    ext z
    constructor
    · rintro ⟨_, ⟨a, b, rfl, hab⟩, rfl⟩
      refine ⟨ρ ↘ hβ ↘ hγ ↘ hδ • a, ρ ↘ hβ ↘ hγ ↘ hδ • b, ?_, ?_⟩
      · simp only [smul_op]
      · rw [← hS]
        simp only [mem_smul_iff', allPerm_inv_sderiv', inv_smul_smul]
        exact hab
    · rintro ⟨a, b, rfl, hab⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      refine ⟨ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ • a, ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ • b, ?_, ?_⟩
      · simp only [smul_op, allPerm_inv_sderiv']
      · rw [smul_eq_iff_eq_inv_smul] at hS
        rw [hS]
        simp only [allPerm_inv_sderiv', mem_smul_iff', inv_inv, smul_inv_smul]
        exact hab

theorem exists_typeLower (x : TSet α) :
    ∃ y : TSet δ, ∀ a, a ∈[hε] y ↔ ∀ b, op hγ hδ b (singleton hε a) ∈[hβ] x := by
  have := exists_of_symmetric {a | ∀ b, op hγ hδ b (singleton hε a) ∈[hβ] x} hε ?_
  · obtain ⟨y, hy⟩ := this
    use y
    intro a
    rw [hy]
    rfl
  · apply sUnion_singleton_symmetric hε hδ
    apply sUnion_singleton_symmetric hδ hγ
    apply sUnion_singleton_symmetric hγ hβ
    obtain ⟨S, hS⟩ := exists_support x
    use S
    intro ρ hρ
    specialize hS ρ hρ
    ext z
    constructor
    · rintro ⟨_, ⟨_, ⟨a, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩, rfl⟩
      simp only [smul_singleton, Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and,
        singleton_inj, exists_eq_right]
      intro c
      have := hb (ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ • c)
      rw [smul_eq_iff_eq_inv_smul] at hS
      rw [hS] at this
      simp only [allPerm_inv_sderiv', mem_smul_iff', inv_inv, smul_op, smul_inv_smul,
        smul_singleton] at this
      exact this
    · rintro ⟨_, ⟨a, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp only [smul_singleton, allPerm_inv_sderiv', Set.mem_image, Set.mem_setOf_eq,
        exists_exists_and_eq_and, singleton_inj, exists_eq_right]
      intro c
      have := hb (ρ ↘ hβ ↘ hγ ↘ hδ • c)
      rw [← hS] at this
      simp only [mem_smul_iff', allPerm_inv_sderiv', smul_op, inv_smul_smul, smul_singleton] at this
      exact this

theorem exists_converse (x : TSet α) :
    ∃ y : TSet α, ∀ a b, op hγ hδ a b ∈[hβ] y ↔ op hγ hδ b a ∈[hβ] x := by
  have := exists_of_symmetric {a | ∃ b c, a = op hγ hδ b c ∧ op hγ hδ c b ∈[hβ] x} hβ ?_
  · obtain ⟨y, hy⟩ := this
    use y
    intro a b
    rw [hy]
    simp only [Set.mem_setOf_eq, op_inj]
    constructor
    · rintro ⟨a', b', ⟨rfl, rfl⟩, h⟩
      exact h
    · intro h
      exact ⟨a, b, ⟨rfl, rfl⟩, h⟩
  · obtain ⟨S, hS⟩ := exists_support x
    use S
    intro ρ hρ
    specialize hS ρ hρ
    ext z
    constructor
    · rintro ⟨_, ⟨a, b, rfl, hab⟩, rfl⟩
      refine ⟨ρ ↘ hβ ↘ hγ ↘ hδ • a, ρ ↘ hβ ↘ hγ ↘ hδ • b, ?_, ?_⟩
      · simp only [smul_op]
      · rw [← hS]
        simp only [mem_smul_iff', allPerm_inv_sderiv', smul_op, inv_smul_smul]
        exact hab
    · rintro ⟨a, b, rfl, hab⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      refine ⟨ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ • a, ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ • b, ?_, ?_⟩
      · simp only [smul_op, allPerm_inv_sderiv']
      · rw [smul_eq_iff_eq_inv_smul] at hS
        rw [hS]
        simp only [allPerm_inv_sderiv', mem_smul_iff', inv_inv, smul_op, smul_inv_smul]
        exact hab

theorem exists_cardinalOne :
    ∃ x : TSet α, ∀ a : TSet β, a ∈[hβ] x ↔ ∃ b, ∀ c : TSet γ, c ∈[hγ] a ↔ c = b := by
  have := exists_of_symmetric {a | ∃ b, ∀ c : TSet γ, c ∈[hγ] a ↔ c = b} hβ ?_
  · obtain ⟨y, hy⟩ := this
    use y
    intro a
    rw [hy]
    rfl
  · use ⟨.empty, .empty⟩
    intro ρ hρ
    ext z
    constructor
    · rintro ⟨z, ⟨a, ha⟩, rfl⟩
      refine ⟨ρ ↘ hβ ↘ hγ • a, ?_⟩
      intro b
      simp only [mem_smul_iff', allPerm_inv_sderiv', ha, inv_smul_eq_iff]
    · rintro ⟨a, ha⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      refine ⟨ρ⁻¹ ↘ hβ ↘ hγ • a, ?_⟩
      intro b
      simp only [mem_smul_iff', inv_inv, allPerm_inv_sderiv', ha, smul_eq_iff_eq_inv_smul]

theorem exists_subset :
    ∃ x : TSet α, ∀ a b, op hγ hδ a b ∈[hβ] x ↔ ∀ c : TSet ε, c ∈[hε] a → c ∈[hε] b := by
  have := exists_of_symmetric {a | ∃ b c, a = op hγ hδ b c ∧
      ∀ d : TSet ε, d ∈[hε] b → d ∈[hε] c} hβ ?_
  · obtain ⟨y, hy⟩ := this
    use y
    intro a b
    rw [hy]
    simp only [Set.mem_setOf_eq, op_inj]
    constructor
    · rintro ⟨a', b', ⟨rfl, rfl⟩, h⟩
      exact h
    · intro h
      exact ⟨a, b, ⟨rfl, rfl⟩, h⟩
  · use ⟨.empty, .empty⟩
    intro ρ hρ
    ext z
    constructor
    · rintro ⟨_, ⟨a, b, rfl, hab⟩, rfl⟩
      refine ⟨ρ ↘ hβ ↘ hγ ↘ hδ • a, ρ ↘ hβ ↘ hγ ↘ hδ • b, ?_⟩
      simp only [smul_op, mem_smul_iff', allPerm_inv_sderiv', true_and]
      intro d
      exact hab _
    · rintro ⟨a, b, rfl, hab⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      refine ⟨ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ • a, ρ⁻¹ ↘ hβ ↘ hγ ↘ hδ • b, ?_⟩
      simp only [smul_op, allPerm_inv_sderiv', mem_smul_iff', inv_inv, true_and]
      intro d
      exact hab _

end TSet

end ConNF
