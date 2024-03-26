import Mathlib.Data.Set.Pointwise.SMul
import ConNF.BaseType.Small
import ConNF.Structural.Index

open Cardinal Ordinal

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}] {α β : Type _}

/-- An *`α`-enumeration* is a function from an initial segment of κ to `α`. -/
@[ext]
structure Enumeration (α : Type _) where
  max : κ
  f : (i : κ) → i < max → α

theorem Enumeration.ext' {E F : Enumeration α} (h : E.max = F.max)
    (h' : ∀ (i : κ) (hE : i < E.max) (hF : i < F.max), E.f i hE = F.f i hF) :
    E = F := by
  ext
  · exact h
  obtain ⟨m, e⟩ := E
  obtain ⟨n, f⟩ := F
  cases h
  refine heq_of_eq (funext ?_)
  intro i
  ext h
  exact h' i h h

def Enumeration.carrier (E : Enumeration α) : Set α :=
  { c | ∃ i, ∃ (h : i < E.max), c = E.f i h }

instance : CoeTC (Enumeration α) (Set α) where
  coe E := E.carrier

instance : Membership α (Enumeration α) where
  mem x E := x ∈ E.carrier

theorem Enumeration.mem_carrier_iff (x : α) (E : Enumeration α) :
    x ∈ E.carrier ↔ ∃ i, ∃ (h : i < E.max), x = E.f i h :=
  Iff.rfl

theorem Enumeration.mem_iff (c : α) (E : Enumeration α) :
    c ∈ E ↔ ∃ i, ∃ (h : i < E.max), c = E.f i h :=
  Iff.rfl

theorem Enumeration.f_mem (E : Enumeration α) (i : κ) (hi : i < E.max) :
    E.f i hi ∈ E :=
  ⟨i, hi, rfl⟩

theorem Enumeration.carrier_small (E : Enumeration α) : Small E.carrier := by
  refine lt_of_le_of_lt (b := #(Set.Iio E.max)) ?_ (card_typein_lt (· < ·) E.max Params.κ_ord.symm)
  refine mk_le_of_surjective (f := fun x => ⟨E.f x x.prop, x, x.prop, rfl⟩) ?_
  rintro ⟨_, i, h, rfl⟩
  exact ⟨⟨i, h⟩, rfl⟩

theorem Enumeration.small (E : Enumeration α) : Small (E : Set α) :=
  E.carrier_small

def enumerationEquiv : Enumeration α ≃ Σ max : κ, Set.Iio max → α where
  toFun E := ⟨E.max, fun x => E.f x x.prop⟩
  invFun E := ⟨E.1, fun i h => E.2 ⟨i, h⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def funMap (α β : Type _) [LT β] (f : α → β) :
    { E : Set β // #E ≤ #α } × (α → α → Prop) :=
  ⟨⟨Set.range f, mk_range_le⟩, InvImage (· < ·) f⟩

theorem funMap_injective {α β : Type _} [LinearOrder β] [IsWellOrder β (· < ·)] :
    Function.Injective (funMap α β) := by
  intro f g h
  simp only [funMap, Prod.mk.injEq, Subtype.mk.injEq] at h
  suffices : ∀ y : β, ∀ x : α, f x = y → g x = y
  · ext x : 1
    rw [this]
    rfl
  intro y
  refine IsWellFounded.induction (· < ·) (C := fun y => ∀ x : α, f x = y → g x = y) y ?_
  clear y
  rintro y ih x rfl
  obtain ⟨y, h₁⟩ : f x ∈ Set.range g
  · rw [← h.1]
    exact ⟨x, rfl⟩
  rw [← h₁]
  obtain (h₂ | h₂ | h₂) := lt_trichotomy (g x) (g y)
  · obtain ⟨z, h₃⟩ : g x ∈ Set.range f
    · rw [h.1]
      exact ⟨x, rfl⟩
    rw [h₁, ← h₃] at h₂
    have h₄ := ih (f z) h₂ z rfl
    have := congr_fun₂ h.2 z x
    simp only [InvImage, h₂, eq_iff_iff, true_iff] at this
    rw [h₄, h₃] at this
    cases lt_irrefl _ this
  · exact h₂
  · have := congr_fun₂ h.2 y x
    simp only [InvImage, eq_iff_iff] at this
    rw [← this] at h₂
    have := ih (f y) h₂ y rfl
    have := h₂.trans_eq (h₁.symm.trans this)
    cases lt_irrefl _ this

theorem mk_fun_le {α β : Type u} :
    #(α → β) ≤ #({ E : Set β // #E ≤ #α } × (α → α → Prop)) := by
  classical
  obtain ⟨r, hr⟩ := IsWellOrder.subtype_nonempty (σ := β)
  let _ := linearOrderOfSTO r
  exact ⟨⟨funMap α β, funMap_injective⟩⟩

theorem pow_le_of_isStrongLimit' {α β : Type u} [Infinite α] [Infinite β]
    (h₁ : IsStrongLimit #β) (h₂ : #α < (#β).ord.cof) : #β ^ #α ≤ #β := by
  refine le_trans mk_fun_le ?_
  simp only [mk_prod, Cardinal.lift_id, mk_pi, mk_fintype, Fintype.card_prop, Nat.cast_ofNat,
    prod_const, Cardinal.lift_id', lift_two]
  have h₃ : #{ E : Set β // #E ≤ #α } ≤ #β
  · rw [← mk_subset_mk_lt_cof h₁.2]
    refine ⟨⟨fun E => ⟨E, E.prop.trans_lt h₂⟩, ?_⟩⟩
    intro E F h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.coe_injective h
  have h₄ : (2 ^ #α) ^ #α ≤ #β
  · rw [← power_mul, mul_eq_self (Cardinal.infinite_iff.mp inferInstance)]
    refine (h₁.2 _ ?_).le
    exact h₂.trans_le (cof_ord_le #β)
  refine le_trans (mul_le_max _ _) ?_
  simp only [ge_iff_le, le_max_iff, max_le_iff, le_aleph0_iff_subtype_countable, h₃, h₄, and_self,
    aleph0_le_mk]

theorem pow_lt_of_isStrongLimit' {α β γ : Type u} [Infinite β]
    (hα : #α < #γ) (hβ : #β < #γ) (hγ : IsStrongLimit #γ) : #α ^ #β < #γ := by
  refine lt_of_le_of_lt mk_fun_le ?_
  simp only [mk_prod, Cardinal.lift_id, mk_pi, mk_fintype, Fintype.card_prop, Nat.cast_ofNat,
    prod_const, Cardinal.lift_ofNat, Cardinal.lift_id']
  refine mul_lt_of_lt ?_ ?_ ?_
  · exact hγ.isLimit.aleph0_le
  · refine (Cardinal.mk_subtype_le _).trans_lt ?_
    rw [mk_set]
    exact hγ.2 _ hα
  · rw [← power_mul, mul_eq_self (Cardinal.infinite_iff.mp inferInstance)]
    exact hγ.2 _ hβ

theorem pow_le_of_isStrongLimit {κ μ : Cardinal.{u}} (h₁ : IsStrongLimit μ) (h₂ : κ < μ.ord.cof) :
    μ ^ κ ≤ μ := by
  by_cases h : κ < ℵ₀
  · exact pow_le h₁.isLimit.aleph0_le h
  · revert h₁ h₂ h
    refine inductionOn₂ κ μ ?_
    intro α β h₁ h₂ h
    have := Cardinal.infinite_iff.mpr (le_of_not_lt h)
    have := Cardinal.infinite_iff.mpr h₁.isLimit.aleph0_le
    exact pow_le_of_isStrongLimit' h₁ h₂

theorem pow_lt_of_isStrongLimit {ξ κ μ : Cardinal.{u}}
    (hξ : ξ < μ) (hκ : κ < μ) (hμ : IsStrongLimit μ) : ξ ^ κ < μ := by
  by_cases h : κ < ℵ₀
  · rw [lt_aleph0] at h
    obtain ⟨n, rfl⟩ := h
    by_cases h : ξ < ℵ₀
    · rw [lt_aleph0] at h
      obtain ⟨m, rfl⟩ := h
      rw [pow_cast_right, ← Nat.cast_pow]
      exact (nat_lt_aleph0 _).trans_le hμ.isLimit.aleph0_le
    · exact (power_nat_le (le_of_not_lt h)).trans_lt hξ
  · revert hξ hκ hμ h
    refine inductionOn₃ ξ κ μ ?_
    intro α β γ hα hβ hγ h
    have := infinite_iff.mpr (le_of_not_lt h)
    exact pow_lt_of_isStrongLimit' hα hβ hγ

/-- Given that `#α = #μ`, there are exactly `μ` Enumerations. -/
theorem mk_enumeration (mk_α : #α = #μ) : #(Enumeration α) = #μ := by
  refine le_antisymm ?_ ?_
  · rw [Cardinal.mk_congr enumerationEquiv]
    simp only [mk_sigma, mk_pi, mk_α, prod_const, Cardinal.lift_id]
    refine le_trans (sum_le_sum _ (fun _ => #μ) ?_) ?_
    · intro i
      refine pow_le_of_isStrongLimit Params.μ_isStrongLimit ?_
      refine lt_of_lt_of_le ?_ Params.κ_le_μ_ord_cof
      exact card_typein_lt (· < ·) i Params.κ_ord.symm
    · simp only [sum_const, Cardinal.lift_id, mul_mk_eq_max, ge_iff_le, max_le_iff, le_refl,
        and_true]
      exact Params.κ_lt_μ.le
  · rw [← mk_α]
    refine ⟨⟨fun x => ⟨1, fun _ _ => x⟩, ?_⟩⟩
    intro a₁ a₂ h
    simp only [Enumeration.mk.injEq, heq_eq_eq, true_and] at h
    exact congr_fun₂ h 0 κ_zero_lt_one

theorem _root_.Cardinal.pow_mono_left (a : Cardinal) (ha : a ≠ 0) :
    Monotone (fun (b : Cardinal) => a ^ b) := by
  intro b c
  revert ha
  refine Cardinal.inductionOn₃ a b c ?_
  intro α β γ hα h
  suffices : #(β → α) ≤ #(γ → α)
  · simp only [mk_pi, prod_const, Cardinal.lift_id] at this
    exact this
  obtain (hβ | hβ) := isEmpty_or_nonempty β
  · rw [mk_ne_zero_iff] at hα
    obtain ⟨a⟩ := hα
    refine ⟨fun _ _ => a, ?_⟩
    intro f g _
    ext x
    cases IsEmpty.false x
  · rw [Cardinal.le_def] at h
    obtain ⟨f, hf⟩ := h
    refine mk_le_of_surjective (f := (· ∘ f)) ?_
    intro g
    obtain ⟨k, hk⟩ := hf.hasLeftInverse
    rw [Function.leftInverse_iff_comp] at hk
    refine ⟨g ∘ k, ?_⟩
    dsimp only
    rw [Function.comp.assoc, hk, Function.comp_id]

theorem max_eq_zero [IsEmpty α] (E : Enumeration α) : E.max = 0 := by
  rw [← κ_le_zero_iff]
  by_contra! h
  have := E.f 0 h
  exact isEmptyElim this

instance [IsEmpty α] : Subsingleton (Enumeration α) := by
  constructor
  intro E F
  refine Enumeration.ext' ?_ ?_
  · rw [max_eq_zero, max_eq_zero]
  · intro i hE hF
    cases show False from isEmptyElim (E.f i hE)

theorem _root_.Cardinal.mul_le_of_le {a b c : Cardinal} (ha : a ≤ c) (hb : b ≤ c) (hc : ℵ₀ ≤ c) :
    a * b ≤ c := by
  by_cases ha' : ℵ₀ ≤ a
  · refine le_trans (mul_le_max_of_aleph0_le_left ha') ?_
    simp only [ge_iff_le, max_le_iff]
    exact ⟨ha, hb⟩
  by_cases hb' : ℵ₀ ≤ b
  · refine le_trans (mul_le_max_of_aleph0_le_right hb') ?_
    simp only [ge_iff_le, max_le_iff]
    exact ⟨ha, hb⟩
  · simp only [not_le] at ha' hb'
    exact (mul_lt_aleph0 ha' hb').le.trans hc

theorem _root_.Cardinal.lt_pow {a b : Cardinal} (h : 1 < a) : b < a ^ b := by
  refine Cardinal.inductionOn b ?_
  intro β
  have := sum_lt_prod (fun (_ : β) => 1) (fun _i_ => a) (fun _ => h)
  simp only [sum_const, Cardinal.lift_id, mul_one, prod_const] at this
  exact this

theorem mk_enumeration_ne_zero {α : Type u} : #(Enumeration α) ≠ 0 := by
  rw [Cardinal.mk_ne_zero_iff]
  exact ⟨⟨0, fun _ hi => (κ_not_lt_zero _ hi).elim⟩⟩

/-- A bound on the amount of enumerations. -/
theorem mk_enumeration_le {α : Type u} [Nontrivial α] : #(Enumeration α) ≤ #α ^ #κ := by
  rw [mk_congr enumerationEquiv]
  simp only [mk_sigma, mk_pi, prod_const, Cardinal.lift_id]
  have : ∀ i : κ, #α ^ #(Set.Iio i) ≤ #α ^ #κ
  · intro i
    refine pow_mono_left _ ?_ ?_
    · rw [mk_ne_zero_iff]
      infer_instance
    · exact (card_typein_lt (· < ·) i Params.κ_ord.symm).le
  refine (sum_le_sum _ _ this).trans ?_
  simp only [sum_const, Cardinal.lift_id]
  have : #κ ≤ #α ^ #κ := (lt_pow ?_).le
  · exact mul_le_of_le this le_rfl (Params.κ_isRegular.aleph0_le.trans this)
  · rw [one_lt_iff_nontrivial]
    infer_instance

theorem mk_enumeration_le_of_subsingleton {α : Type u} [Subsingleton α] :
    #(Enumeration α) ≤ #κ := by
  refine ⟨Enumeration.max, ?_⟩
  intro E F h
  refine Enumeration.ext' h ?_
  intro i hE hF
  exact Subsingleton.elim _ _

/-- A bound on the amount of enumerations. -/
theorem mk_enumeration_lt (h : #α < #μ) : #(Enumeration α) < #μ := by
  obtain (hα | hα) := subsingleton_or_nontrivial α
  · exact mk_enumeration_le_of_subsingleton.trans_lt Params.κ_lt_μ
  · refine mk_enumeration_le.trans_lt ?_
    exact pow_lt_of_isStrongLimit h Params.κ_lt_μ Params.μ_isStrongLimit

namespace Enumeration

def image (E : Enumeration α) (f : α → β) : Enumeration β where
  max := E.max
  f i hi := f (E.f i hi)

@[simp]
theorem image_max (E : Enumeration α) (f : α → β) :
    (E.image f).max = E.max :=
  rfl

@[simp]
theorem image_f (E : Enumeration α) (f : α → β) (i : κ) (hi : i < E.max) :
    (E.image f).f i hi = f (E.f i hi) :=
  rfl

@[simp]
theorem image_carrier (E : Enumeration α) (f : α → β) :
    (E.image f).carrier = f '' E.carrier := by
  ext x : 1
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h.symm⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, h⟩
    exact ⟨i, hi, h.symm⟩

@[simp]
theorem image_coe (E : Enumeration α) (f : α → β) :
    (E.image f : Enumeration β) = f '' (E : Set α) :=
  image_carrier E f

theorem apply_mem_image {E : Enumeration α} {x : α} (h : x ∈ E) (f : α → β) : f x ∈ E.image f := by
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hi, rfl⟩

theorem apply_eq_of_image_eq {E : Enumeration α} (f : α → α)
    (hE : E.image f = E) {x : α} (hx : x ∈ E) : f x = x := by
  obtain ⟨i, hi, rfl⟩ := hx
  have := image_f E f i hi
  conv at this => lhs; simp only [hE]
  exact this.symm

instance {G : Type _} [SMul G α] : SMul G (Enumeration α) where
  smul g E := E.image (g • ·)

@[simp]
theorem smul_max {G : Type _} [SMul G α] (g : G) (E : Enumeration α) :
    (g • E).max = E.max :=
  rfl

@[simp]
theorem smul_f {G : Type _} [SMul G α]
    (g : G) (E : Enumeration α) (i : κ) (hi : i < E.max) :
    (g • E).f i hi = g • E.f i hi :=
  rfl

@[simp]
theorem smul_carrier {G : Type _} [SMul G α] (g : G) (E : Enumeration α) :
    (g • E).carrier = g • E.carrier :=
  image_carrier _ _

@[simp]
theorem smul_coe {G : Type _} [SMul G α] (g : G) (E : Enumeration α) :
    (g • E : Enumeration α) = g • (E : Set α) :=
  image_coe _ _

theorem smul_mem_smul {G : Type _} [SMul G α]
    {E : Enumeration α} {x : α} (h : x ∈ E) (g : G) : g • x ∈ g • E :=
  apply_mem_image h _

theorem smul_eq_of_smul_eq {G : Type _} [SMul G α] {g : G} {E : Enumeration α}
    (hE : g • E = E) {x : α} (hx : x ∈ E) : g • x = x :=
  apply_eq_of_image_eq _ hE hx

instance {G : Type _} [Monoid G] [MulAction G α] : MulAction G (Enumeration α) where
  one_smul := by
    rintro ⟨i, f⟩
    ext
    · rfl
    · refine heq_of_eq (funext₂ ?_)
      intro j hj
      simp only [smul_f, one_smul]
  mul_smul g h := by
    rintro ⟨i, f⟩
    ext
    · rfl
    · refine heq_of_eq (funext₂ ?_)
      intro j hj
      simp only [smul_f, mul_smul]

theorem smul_mem_smul_iff {G : Type _} [Group G] [MulAction G α]
    {E : Enumeration α} {x : α} (g : G) : g • x ∈ g • E ↔ x ∈ E := by
  constructor
  · intro h
    have := smul_mem_smul h g⁻¹
    rwa [inv_smul_smul, inv_smul_smul] at this
  · exact (smul_mem_smul · g)

instance : Add (Enumeration α) where
  add E F := ⟨E.max + F.max, fun i hi =>
    if hi' : i < E.max then
      E.f i hi'
    else
      F.f (i - E.max) (κ_sub_lt hi (not_lt.mp hi'))⟩

theorem add_f_eq {E F : Enumeration α} {i : κ} (hi : i < (E + F).max) :
    (E + F).f i hi =
      if hi' : i < E.max then
        E.f i hi'
      else
        F.f (i - E.max) (κ_sub_lt hi (not_lt.mp hi')) :=
  rfl

@[simp]
theorem add_max {E F : Enumeration α} : (E + F).max = E.max + F.max :=
  rfl

theorem add_f_left {E F : Enumeration α} {i : κ} (h : i < E.max) :
    (E + F).f i (h.trans_le (κ_le_self_add _ _)) = E.f i h :=
  by rw [add_f_eq, dif_pos h]

theorem add_f_right {E F : Enumeration α} {i : κ} (h₁ : i < (E + F).max) (h₂ : E.max ≤ i) :
    (E + F).f i h₁ = F.f (i - E.max) (κ_sub_lt h₁ h₂) :=
  by rw [add_f_eq, dif_neg (not_lt.mpr h₂)]

theorem add_f_right_add {E F : Enumeration α} {i : κ} (h : i < F.max) :
    (E + F).f (E.max + i) (add_lt_add_left h E.max) = F.f i h := by
  rw [add_f_right]
  simp only [κ_add_sub_cancel]
  exact κ_le_self_add _ _

theorem add_coe (E F : Enumeration α) :
    (E + F : Set α) = (E : Set _) ∪ F := by
  ext c
  simp only [mem_carrier_iff, Set.mem_union]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases hi' : i < E.max
    · refine Or.inl ⟨i, hi', ?_⟩
      rw [add_f_left]
    · refine Or.inr ⟨i - E.max, κ_sub_lt hi (not_lt.mp hi'), ?_⟩
      rw [add_f_right]
      exact not_lt.mp hi'
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · refine ⟨i, hi.trans_le (κ_le_self_add _ _), ?_⟩
      rw [add_f_left]
    · refine ⟨E.max + i, add_lt_add_left hi E.max, ?_⟩
      rw [add_f_right_add]

@[simp]
theorem mem_add_iff (E F : Enumeration α) (x : α) :
    x ∈ E + F ↔ x ∈ E ∨ x ∈ F := by
  change x ∈ (E + F : Set α) ↔ _
  rw [add_coe]
  rfl

/-- TODO: Move this -/
instance : IsLeftCancelAdd κ := by
  constructor
  intro i j k h
  have := congr_arg (Ordinal.typein (· < ·)) h
  rw [Params.κ_add_typein, Params.κ_add_typein, Ordinal.add_left_cancel] at this
  exact Ordinal.typein_injective _ this

theorem add_congr {E F G H : Enumeration α} (hEF : E.max = F.max) (h : E + G = F + H) :
    E = F ∧ G = H := by
  have : E = F
  · refine ext' hEF ?_
    intro i hE hF
    have h₁ := add_f_left hE (F := G)
    have h₂ := add_f_left hF (F := H)
    simp_rw [h, h₂] at h₁
    exact h₁.symm
  subst this
  refine ⟨rfl, ?_⟩
  refine ext' ?_ ?_
  · have := congr_arg Enumeration.max h
    simp only [add_max, add_right_inj] at this
    exact this
  · intro i hG hH
    have h₁ := add_f_right_add hG (E := E)
    have h₂ := add_f_right_add hH (E := E)
    simp_rw [h, h₂] at h₁
    exact h₁.symm

@[simp]
theorem smul_add {G : Type _} [SMul G α] {g : G} (E F : Enumeration α) :
    g • (E + F) = g • E + g • F := by
  ext
  · rfl
  rw [heq_iff_eq]
  ext i hi : 2
  by_cases hi' : i < E.max
  · rw [smul_f, add_f_left (show i < (g • E).max from hi'), add_f_left hi', smul_f]
  · rw [smul_f, add_f_right hi (show (g • E).max ≤ i from le_of_not_lt hi'),
      add_f_right (show i < (g • E + g • F).max from hi)
        (show (g • E).max ≤ i from le_of_not_lt hi'), smul_f]
    rfl

instance : LE (Enumeration α) where
  le E F := E.max ≤ F.max ∧ ∀ (i : κ) (hE : i < E.max) (hF : i < F.max), E.f i hE = F.f i hF

instance : LT (Enumeration α) where
  lt E F := E.max < F.max ∧ ∀ (i : κ) (hE : i < E.max) (hF : i < F.max), E.f i hE = F.f i hF

theorem le_iff (E F : Enumeration α) :
    E ≤ F ↔ E.max ≤ F.max ∧ ∀ (i : κ) (hE : i < E.max) (hF : i < F.max), E.f i hE = F.f i hF :=
  Iff.rfl

theorem lt_iff (E F : Enumeration α) :
    E < F ↔ E.max < F.max ∧ ∀ (i : κ) (hE : i < E.max) (hF : i < F.max), E.f i hE = F.f i hF :=
  Iff.rfl

instance : PartialOrder (Enumeration α) where
  lt_iff_le_not_le E F := by
    rw [le_iff, le_iff, lt_iff]
    constructor
    · intro h
      exact ⟨⟨h.1.le, h.2⟩, fun h' => h'.1.not_lt h.1⟩
    · intro h
      rw [not_and'] at h
      exact ⟨lt_of_le_not_le h.1.1 (h.2 (fun i hE hF => (h.1.2 i hF hE).symm)), h.1.2⟩
  le_refl E := ⟨le_rfl, fun _ _ _ => rfl⟩
  le_trans E F G hEF hFG := ⟨hEF.1.trans hFG.1, fun i hE hG =>
    (hEF.2 i hE (hE.trans_le hEF.1)).trans (hFG.2 i (hE.trans_le hEF.1) hG)⟩
  le_antisymm := by
    rintro ⟨m₁, f₁⟩ ⟨m₂, f₂⟩ h₁₂ h₂₁
    cases le_antisymm h₁₂.1 h₂₁.1
    refine Enumeration.ext _ _ rfl (heq_of_eq ?_)
    ext i hi
    exact h₁₂.2 i hi hi

theorem image_le_image {E F : Enumeration α} (h : E ≤ F) (f : α → β) : E.image f ≤ F.image f := by
  constructor
  · exact h.1
  · intro i hE hF
    rw [image_f, image_f, h.2]

theorem smul_le_smul {G : Type _} [SMul G α] {E F : Enumeration α} (h : E ≤ F) (g : G) :
    g • E ≤ g • F :=
  image_le_image h (g • ·)

theorem le_inv_iff_smul_le {G : Type _} [Group G] [MulAction G α] {E F : Enumeration α} (g : G) :
    E ≤ g⁻¹ • F ↔ g • E ≤ F := by
  constructor
  · intro h
    have := smul_le_smul h g
    rwa [smul_inv_smul] at this
  · intro h
    have := smul_le_smul h g⁻¹
    rwa [inv_smul_smul] at this

theorem eq_of_le {G : Type _} [SMul G α] {E F : Enumeration α} {g : G}
    (h₁ : g • E ≤ F) (h₂ : E ≤ F) : g • E = E := by
  refine ext' rfl ?_
  intro i _ hE
  rw [h₁.2 i hE (hE.trans_le h₁.1), h₂.2 i hE (hE.trans_le h₁.1)]

theorem le_add (E F : Enumeration α) : E ≤ E + F := by
  constructor
  · simp only [add_max, le_add_iff_nonneg_right]
    exact κ_pos _
  · intro i hE hF
    rw [add_f_left]

noncomputable section
open scoped Classical

theorem ord_lt_of_small {s : Set α} (hs : Small s) [LinearOrder s] [IsWellOrder s (· < ·)] :
    type ((· < ·) : s → s → Prop) < type ((· < ·) : κ → κ → Prop) := by
  by_contra! h
  have := card_le_card h
  simp only [card_type] at this
  exact hs.not_le this

theorem typein_lt_type_of_small {s : Set α} (hs : Small s) [LinearOrder s] [IsWellOrder s (· < ·)]
    {i : κ} (hi : i < enum (· < ·) (type ((· < ·) : s → s → Prop)) (ord_lt_of_small hs)) :
    typein ((· < ·) : κ → κ → Prop) i < type ((· < ·) : s → s → Prop) := by
  rw [← typein_lt_typein (· < ·), typein_enum] at hi
  exact hi

def ofSet' (s : Set α) (hs : Small s) [LinearOrder s] [IsWellOrder s (· < ·)] : Enumeration α where
  max := enum (· < ·) (type ((· < ·) : s → s → Prop)) (ord_lt_of_small hs)
  f i hi := (enum ((· < ·) : s → s → Prop) (typein ((· < ·) : κ → κ → Prop) i)
    (typein_lt_type_of_small hs hi) : s)

@[simp]
theorem ofSet'_coe (s : Set α) (hs : Small s) [LinearOrder s] [IsWellOrder s (· < ·)] :
    (ofSet' s hs : Set α) = s := by
  ext x
  rw [ofSet', mem_carrier_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact Subtype.coe_prop _
  · rintro hx
    refine ⟨enum ((· < ·) : κ → κ → Prop) (typein ((· < ·) : s → s → Prop) ⟨x, hx⟩) ?_, ?_, ?_⟩
    · exact (typein_lt_type _ _).trans (ord_lt_of_small hs)
    · rw [enum_lt_enum (r := ((· < ·) : κ → κ → Prop))]
      exact typein_lt_type _ _
    · simp only [typein_enum, enum_typein]

def ofSet (s : Set α) (hs : Small s) : Enumeration α :=
  letI := (IsWellOrder.subtype_nonempty (σ := s)).some.prop
  letI := linearOrderOfSTO (IsWellOrder.subtype_nonempty (σ := s)).some.val
  ofSet' s hs

@[simp]
theorem ofSet_coe (s : Set α) (hs : Small s) :
    (ofSet s hs : Set α) = s :=
  letI := (IsWellOrder.subtype_nonempty (σ := s)).some.prop
  letI := linearOrderOfSTO (IsWellOrder.subtype_nonempty (σ := s)).some.val
  ofSet'_coe s hs

@[simp]
theorem mem_ofSet_iff (s : Set α) (hs : Small s) (x : α) :
    x ∈ ofSet s hs ↔ x ∈ s := by
  change x ∈ (ofSet s hs : Set α) ↔ x ∈ s
  rw [ofSet_coe]

def chooseIndex (E : Enumeration α) (p : α → Prop)
    (h : ∃ i : κ, ∃ h : i < E.max, p (E.f i h)) : κ :=
  h.choose

theorem chooseIndex_lt {E : Enumeration α} {p : α → Prop}
    (h : ∃ i : κ, ∃ h : i < E.max, p (E.f i h)) : E.chooseIndex p h < E.max :=
  h.choose_spec.choose

theorem chooseIndex_spec {E : Enumeration α} {p : α → Prop}
    (h : ∃ i : κ, ∃ h : i < E.max, p (E.f i h)) : p (E.f (E.chooseIndex p h) (chooseIndex_lt h)) :=
  h.choose_spec.choose_spec

end

end Enumeration

end ConNF
