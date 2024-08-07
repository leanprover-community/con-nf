import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.PartialEquiv

/-!
# Partial permutation

This files defines permutations on a set.

A partial permutation on `α` is a domain `Set α` and two functions `α → α` that map `domain` to
`domain` and are inverse to each other on `domain`.

## Main declarations

* `PartialPerm α`: The type of partial permutations on `α`.
-/

open Function Set

variable {α : Type _}

/-- A partial permutation of a subset `domain` of `α`. The (global) maps `toFun : α → α` and
`invFun : α → α` map `domain` to itself, and are inverse to each other there. The values of
`toFun` and `invFun` outside of `domain` are irrelevant. -/
structure PartialPerm (α : Type _) where
  (toFun invFun : α → α)
  domain : Set α
  toFun_domain' : ∀ ⦃x⦄, x ∈ domain → toFun x ∈ domain
  invFun_domain' : ∀ ⦃x⦄, x ∈ domain → invFun x ∈ domain
  left_inv' : ∀ ⦃x⦄, x ∈ domain → invFun (toFun x) = x
  right_inv' : ∀ ⦃x⦄, x ∈ domain → toFun (invFun x) = x

/-- A `Perm` gives rise to a `PartialPerm` defined on the entire type. -/
def Equiv.Perm.toPartialPerm (π : Equiv.Perm α) : PartialPerm α
    where
  toFun := π
  invFun := π.symm
  domain := univ
  toFun_domain' _ _ := mem_univ _
  invFun_domain' _ _ := mem_univ _
  left_inv' x _ := π.left_inv x
  right_inv' x _ := π.right_inv x

namespace PartialPerm

variable (π π' : PartialPerm α)

/-- The inverse of a partial permutation. -/
protected def symm : PartialPerm α where
  toFun := π.invFun
  invFun := π.toFun
  domain := π.domain
  toFun_domain' := π.invFun_domain'
  invFun_domain' := π.toFun_domain'
  left_inv' := π.right_inv'
  right_inv' := π.left_inv'

instance : CoeFun (PartialPerm α) fun _ => α → α :=
  ⟨PartialPerm.toFun⟩

@[simp]
theorem coe_mk (f : α → α) (g s ml mr il ir) : (PartialPerm.mk f g s ml mr il ir : α → α) = f :=
  rfl

@[simp]
theorem coe_symm_mk (f : α → α) (g s ml mr il ir) :
    ((PartialPerm.mk f g s ml mr il ir).symm : α → α) = g :=
  rfl

@[simp]
theorem toFun_as_coe : π.toFun = π :=
  rfl

@[simp]
theorem invFun_as_coe : π.invFun = π.symm :=
  rfl

@[simp]
theorem map_domain {x : α} (h : x ∈ π.domain) : π x ∈ π.domain :=
  π.toFun_domain' h

@[simp]
theorem iterate_domain {x : α} (h : x ∈ π.domain) {n : ℕ} : π^[n] x ∈ π.domain := by
  induction' n with n ih
  exact h
  rw [Function.iterate_succ']
  exact π.map_domain ih

@[simp]
theorem left_inv {x : α} (h : x ∈ π.domain) : π.symm (π x) = x :=
  π.left_inv' h

@[simp]
theorem right_inv {x : α} (h : x ∈ π.domain) : π (π.symm x) = x :=
  π.right_inv' h

@[simp]
theorem symm_domain : π.symm.domain = π.domain :=
  rfl

@[simp]
theorem symm_symm : π.symm.symm = π := by cases π; rfl

theorem eq_symm_apply {x : α} {y : α} (hx : x ∈ π.domain) (hy : y ∈ π.domain) :
    x = π.symm y ↔ π x = y :=
  ⟨fun h => by rw [← π.right_inv hy, h], fun h => by rw [← π.left_inv hx, h]⟩

protected theorem mapsTo : MapsTo π π.domain π.domain := fun _ => π.map_domain

protected theorem leftInvOn : LeftInvOn π.symm π π.domain := fun _ => π.left_inv

protected theorem rightInvOn : RightInvOn π.symm π π.domain := fun _ => π.right_inv

protected theorem invOn : InvOn π.symm π π.domain π.domain :=
  ⟨π.leftInvOn, π.rightInvOn⟩

protected theorem injOn : InjOn π π.domain :=
  π.leftInvOn.injOn

protected theorem bijOn : BijOn π π.domain π.domain :=
  π.invOn.bijOn π.mapsTo π.symm.mapsTo

protected theorem surjOn : SurjOn π π.domain π.domain :=
  π.bijOn.surjOn

/-- Create a copy of a `PartialPerm` providing better definitional equalities. -/
@[simps (config := { fullyApplied := false })]
def copy (π : PartialPerm α) (f : α → α) (hf : ⇑π = f) (g : α → α) (hg : ⇑π.symm = g) (s : Set α)
    (hs : π.domain = s) : PartialPerm α where
  toFun := f
  invFun := g
  domain := s
  toFun_domain' := hs ▸ hf ▸ π.toFun_domain'
  invFun_domain' := hs ▸ hg ▸ π.invFun_domain'
  left_inv' _ := hs ▸ hf ▸ hg ▸ π.left_inv
  right_inv' _ := hs ▸ hf ▸ hg ▸ π.right_inv

theorem copy_eq (π : PartialPerm α) (f : α → α) (hf : ⇑π = f) (g : α → α) (hg : ⇑π.symm = g)
    (s : Set α) (hs : π.domain = s) : π.copy f hf g hg s hs = π := by substs f g s; cases π; rfl

/-- Associating to a partial_perm a permutation of the domain. -/
protected def toPerm : Equiv.Perm π.domain
    where
  toFun x := ⟨π x, π.map_domain x.mem⟩
  invFun y := ⟨π.symm y, π.symm.map_domain y.mem⟩
  left_inv := fun ⟨_, hx⟩ => Subtype.eq <| π.left_inv hx
  right_inv := fun ⟨_, hy⟩ => Subtype.eq <| π.right_inv hy

@[simp]
theorem image_domain : π '' π.domain = π.domain :=
  π.bijOn.image_eq

theorem forall_mem_domain {p : α → Prop} : (∀ y ∈ π.domain, p y) ↔ ∀ x ∈ π.domain, p (π x) := by
  conv_lhs => rw [← image_domain, forall_mem_image]

theorem exists_mem_domain {p : α → Prop} : (∃ y ∈ π.domain, p y) ↔ ∃ x ∈ π.domain, p (π x) := by
  conv_lhs => rw [← image_domain, exists_mem_image]

/-- A set `s` is *stable* under a partial equivalence `π` if it preserved by it. -/
def IsStable (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ π.domain → (π x ∈ s ↔ x ∈ s)

namespace IsStable

variable {π π'} {s : Set α} {x y : α}

theorem apply_mem_iff (h : π.IsStable s) (hx : x ∈ π.domain) : π x ∈ s ↔ x ∈ s :=
  h hx

theorem symm_apply_mem_iff (h : π.IsStable s) : ∀ ⦃y⦄, y ∈ π.domain → (π.symm y ∈ s ↔ y ∈ s) :=
  π.forall_mem_domain.mpr fun x hx => by rw [π.left_inv hx, h hx]

protected theorem symm (h : π.IsStable s) : π.symm.IsStable s :=
  h.symm_apply_mem_iff

@[simp]
theorem symm_iff : π.symm.IsStable s ↔ π.IsStable s :=
  ⟨fun h => h.symm, fun h => h.symm⟩

protected theorem mapsTo (h : π.IsStable s) : MapsTo π (π.domain ∩ s) (π.domain ∩ s) :=
  fun _ hx => ⟨π.mapsTo hx.1, (h hx.1).2 hx.2⟩

theorem symm_mapsTo (h : π.IsStable s) : MapsTo π.symm (π.domain ∩ s) (π.domain ∩ s) :=
  h.symm.mapsTo

/-- Restrict a `PartialPerm` to a stable subset. -/
@[simps (config := { fullyApplied := false })]
def restr (h : π.IsStable s) : PartialPerm α
    where
  toFun := π
  invFun := π.symm
  domain := π.domain ∩ s
  toFun_domain' := h.mapsTo
  invFun_domain' := h.symm_mapsTo
  left_inv' := π.leftInvOn.mono inter_subset_left
  right_inv' := π.rightInvOn.mono inter_subset_left

theorem image_eq (h : π.IsStable s) : π '' (π.domain ∩ s) = π.domain ∩ s :=
  h.restr.image_domain

theorem symm_image_eq (h : π.IsStable s) : π.symm '' (π.domain ∩ s) = π.domain ∩ s :=
  h.symm.image_eq

theorem iff_preimage_eq : π.IsStable s ↔ π.domain ∩ π ⁻¹' s = π.domain ∩ s := by
  simp only [IsStable, Set.ext_iff, mem_inter_iff, and_congr_right_iff, mem_preimage]

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq

theorem iff_symm_preimage_eq : π.IsStable s ↔ π.domain ∩ π.symm ⁻¹' s = π.domain ∩ s :=
  symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq

protected theorem compl (h : π.IsStable s) : π.IsStable (sᶜ) :=
  fun _ hx => not_congr (h hx)

protected theorem inter {s'} (h : π.IsStable s) (h' : π.IsStable s') : π.IsStable (s ∩ s') :=
  fun _ hx => and_congr (h hx) (h' hx)

protected theorem union {s'} (h : π.IsStable s) (h' : π.IsStable s') : π.IsStable (s ∪ s') :=
  fun _ hx => or_congr (h hx) (h' hx)

protected theorem diff {s'} (h : π.IsStable s) (h' : π.IsStable s') : π.IsStable (s \ s') :=
  h.inter h'.compl

theorem leftInvOn_piecewise {π' : PartialPerm α} [∀ i, Decidable (i ∈ s)] (h : π.IsStable s)
    (h' : π'.IsStable s) :
    LeftInvOn (s.piecewise π.symm π'.symm) (s.piecewise π π') (s.ite π.domain π'.domain) := by
  rintro x (⟨he, hs⟩ | ⟨he, hs : x ∉ s⟩)
  · rw [piecewise_eq_of_mem _ _ _ hs, piecewise_eq_of_mem _ _ _ ((h he).2 hs), π.left_inv he]
  · rw [piecewise_eq_of_not_mem _ _ _ hs, piecewise_eq_of_not_mem _ _ _ ((h'.compl he).2 hs),
      π'.left_inv he]

theorem inter_eq_of_inter_eq_of_eqOn {π' : PartialPerm α} (h : π.IsStable s) (h' : π'.IsStable s)
    (hs : π.domain ∩ s = π'.domain ∩ s) (Heq : EqOn π π' (π.domain ∩ s)) :
    π.domain ∩ s = π'.domain ∩ s := by rw [← h.image_eq, ← h'.image_eq, ← hs, Heq.image_eq]

theorem symm_eqOn_of_inter_eq_of_eqOn {π' : PartialPerm α} (h : π.IsStable s)
    (hs : π.domain ∩ s = π'.domain ∩ s) (Heq : EqOn π π' (π.domain ∩ s)) :
    EqOn π.symm π'.symm (π.domain ∩ s) := by
  rw [← h.image_eq]
  rintro y ⟨x, hx, rfl⟩
  have hx' := hx; rw [hs] at hx'
  rw [π.left_inv hx.1, Heq hx, π'.left_inv hx'.1]

end IsStable

theorem image_domain_inter_eq' (s : Set α) : π '' (π.domain ∩ s) = π.domain ∩ π.symm ⁻¹' s := by
  rw [inter_comm, π.leftInvOn.image_inter', image_domain, inter_comm]

theorem image_domain_inter_eq (s : Set α) :
    π '' (π.domain ∩ s) = π.domain ∩ π.symm ⁻¹' (π.domain ∩ s) := by
  rw [inter_comm, π.leftInvOn.image_inter, image_domain, inter_comm]

theorem image_eq_domain_inter_inv_preimage {s : Set α} (h : s ⊆ π.domain) :
    π '' s = π.domain ∩ π.symm ⁻¹' s := by
  rw [← π.image_domain_inter_eq', inter_eq_self_of_subset_right h]

theorem symm_image_eq_domain_inter_preimage {s : Set α} (h : s ⊆ π.domain) :
    π.symm '' s = π.domain ∩ π ⁻¹' s :=
  π.symm.image_eq_domain_inter_inv_preimage h

theorem symm_image_domain_inter_eq (s : Set α) :
    π.symm '' (π.domain ∩ s) = π.domain ∩ π ⁻¹' (π.domain ∩ s) :=
  π.symm.image_domain_inter_eq _

theorem symm_image_domain_inter_eq' (s : Set α) : π.symm '' (π.domain ∩ s) = π.domain ∩ π ⁻¹' s :=
  π.symm.image_domain_inter_eq' _

theorem domain_inter_preimage_inv_preimage (s : Set α) :
    π.domain ∩ π ⁻¹' (π.symm ⁻¹' s) = π.domain ∩ s :=
  Set.ext fun x => and_congr_right_iff.2 fun hx => by simp only [mem_preimage, π.left_inv hx]

theorem domain_inter_preimage_domain_inter (s : Set α) :
    π.domain ∩ π ⁻¹' (π.domain ∩ s) = π.domain ∩ π ⁻¹' s :=
  ext fun _ => ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, π.map_domain hx.1, hx.2⟩⟩

theorem domain_inter_inv_preimage_preimage (s : Set α) :
    π.domain ∩ π.symm ⁻¹' (π ⁻¹' s) = π.domain ∩ s :=
  π.symm.domain_inter_preimage_inv_preimage _

theorem symm_image_image_of_subset_domain {s : Set α} (h : s ⊆ π.domain) : π.symm '' (π '' s) = s :=
  (π.leftInvOn.mono h).image_image

theorem image_symm_image_of_subset_domain {s : Set α} (h : s ⊆ π.domain) : π '' (π.symm '' s) = s :=
  π.symm.symm_image_image_of_subset_domain h

variable {π π'}

theorem domain_subset_preimage_domain : π.domain ⊆ π ⁻¹' π.domain :=
  π.mapsTo

theorem symm_image_domain : π.symm '' π.domain = π.domain :=
  π.symm.image_domain

/-- Two partial permutations that have the same `domain`, same `toFun` and same `invFun`, coincide. -/
@[ext]
protected theorem ext (h : ∀ x, π x = π' x) (hsymm : ∀ x, π.symm x = π'.symm x)
    (hs : π.domain = π'.domain) : π = π' := by
  have A : (π : α → α) = π' := by ext x; exact h x
  have B : (π.symm : α → α) = π'.symm := by ext x; exact hsymm x
  have I : π '' π.domain = π.domain := π.image_domain
  have I' : π' '' π'.domain = π'.domain := π'.image_domain
  rw [A, hs, I'] at I
  cases π; cases π'
  simp_all only [coe_symm_mk, coe_mk, eq_self_iff_true, and_self_iff]

/-- The identity partial permutation. -/
protected def refl (α : Type _) : PartialPerm α :=
  Equiv.Perm.toPartialPerm <| Equiv.refl _

@[simp]
theorem refl_domain : (PartialPerm.refl α).domain = univ :=
  rfl

@[simp]
theorem coe_refl : ⇑(PartialPerm.refl α) = id :=
  rfl

@[simp]
theorem symm_refl : (PartialPerm.refl α).symm = PartialPerm.refl α :=
  rfl

instance : Inhabited (PartialPerm α) :=
  ⟨PartialPerm.refl _⟩

variable (π π')

-- TODO: Clean up these proofs
/-- Composing two partial permutations if the domain of the first coincides with the domain of the
second. -/
@[simps]
protected def trans (π' : PartialPerm α) (h : π.domain = π'.domain) : PartialPerm α
    where
  toFun := π' ∘ π
  invFun := π.symm ∘ π'.symm
  domain := π.domain
  toFun_domain' x hx := by
    rw [h]
    refine map_domain _ ?_
    have := map_domain π hx
    rwa [h] at this
  invFun_domain' y hy := by
    refine map_domain _ ?_
    rw [h] at hy
    have := map_domain π'.symm hy
    rwa [symm_domain, ← h] at this
  left_inv' x hx := by
    simp [hx, h.symm]
    rw [left_inv π', left_inv π hx]
    have := map_domain π hx
    rwa [← h]
  right_inv' y hy := by
    simp
    rw [h] at hy
    rw [right_inv π, right_inv π' hy]
    have := map_domain π'.symm hy
    rwa [symm_domain, ← h] at this

/-- The identity partial PERMUTATION on a set `s` -/
def ofSet (s : Set α) : PartialPerm α where
  toFun := id
  invFun := id
  domain := s
  toFun_domain' _ hx := hx
  invFun_domain' _ hx := hx
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl

@[simp]
theorem ofSet_domain (s : Set α) : (ofSet s).domain = s :=
  rfl

@[simp]
theorem coe_ofSet (s : Set α) : (ofSet s : α → α) = id :=
  rfl

@[simp]
theorem ofSet_symm (s : Set α) : (ofSet s).symm = ofSet s :=
  rfl

@[simp]
theorem ofSet_trans_ofSet (s : Set α) : (ofSet s).trans (ofSet s) rfl = ofSet s :=
  rfl

@[simp]
theorem ofSet_univ : ofSet univ = PartialPerm.refl α :=
  rfl

/-- Reinterpret a partial permutation as a partial equivalence. -/
def toPartialEquiv : PartialEquiv α α where
  toFun := π
  invFun := π.symm
  source := π.domain
  target := π.domain
  map_source' := π.mapsTo
  map_target' := π.symm.mapsTo
  left_inv' := π.leftInvOn
  right_inv' := π.rightInvOn

@[simp]
theorem coe_toPartialEquiv : ⇑π.toPartialEquiv = π :=
  rfl

@[simp]
theorem coe_toPartialEquiv_symm : ⇑π.toPartialEquiv.symm = π.symm :=
  rfl

@[simp]
theorem toPartialEquiv_source : π.toPartialEquiv.source = π.domain :=
  rfl

@[simp]
theorem toPartialEquiv_target : π.toPartialEquiv.target = π.domain :=
  rfl

@[simp]
theorem toPartialEquiv_refl : (PartialPerm.refl α).toPartialEquiv = PartialEquiv.refl _ :=
  rfl

@[simp]
theorem toPartialEquiv_symm : π.symm.toPartialEquiv = π.toPartialEquiv.symm :=
  rfl

@[simp]
theorem toPartialEquiv_trans (h) :
    (π.trans π' h).toPartialEquiv = π.toPartialEquiv.trans π'.toPartialEquiv := by
  ext
  · rfl
  · rfl
  · simpa [← h] using fun hx => π.mapsTo hx

/-- `EqOnDomain π π'` means that `π` and `π'` have the same domain, and coincide there. Then `π`
and `π'` should really be considered the same partial permutation. -/
def EqOnDomain : Prop :=
  π.domain = π'.domain ∧ π.domain.EqOn π π'

/-- `eq_on_domain` is an equivalence relation -/
instance eqOnDomainSetoid : Setoid (PartialPerm α)
    where
  r := EqOnDomain
  iseqv := ⟨
    fun e => by
      simp [EqOnDomain]
      exact fun a _ => rfl,
    fun h => by
      simp [EqOnDomain]
      refine ⟨h.1.symm, ?_⟩
      exact fun a ha => (h.2 (h.1 ▸ ha)).symm,
    fun h h' => by
      simp [EqOnDomain]
      refine ⟨h.1.trans h'.1, ?_⟩
      intro a ha
      rw [← h'.2, h.2 ha]
      rwa [← h.1]
  ⟩

variable {π π'}

theorem eq_on_domain_refl : π ≈ π :=
  Setoid.refl _

/-- Two equivalent partial permutations have the same domain -/
theorem EqOnDomain.domain_eq (h : π ≈ π') : π.domain = π'.domain :=
  h.1

theorem EqOnDomain.symm_domain_eq (h : π ≈ π') : π.symm.domain = π'.symm.domain :=
  h.1

/-- Two equivalent partial permutations coincide on the domain -/
theorem EqOnDomain.eqOn (h : π ≈ π') : π.domain.EqOn π π' :=
  h.2

/-- If two partial permutations are equivalent, so are their inverses. -/
theorem EqOnDomain.symm' (h : π ≈ π') : π.symm ≈ π'.symm := by
  refine ⟨EqOnDomain.symm_domain_eq h, eqOn_of_leftInvOn_of_rightInvOn π.leftInvOn ?_ ?_⟩ <;>
    simp only [symm_domain, EqOnDomain.domain_eq h, π'.symm.mapsTo]
  exact π'.rightInvOn.congr_right π'.symm.mapsTo (EqOnDomain.domain_eq h ▸ h.eqOn.symm)
  exact π'.symm.mapsTo

/-- Two equivalent partial permutations have coinciding inverses on the domain -/
theorem EqOnDomain.symm_eqOn (h : π ≈ π') : EqOn π.symm π'.symm π.domain :=
  EqOnDomain.eqOn (EqOnDomain.symm' h)

/-- Preimages are respected by equivalence. -/
theorem EqOnDomain.domain_inter_preimage_eq (hπ : π ≈ π') (s : Set α) :
    π.domain ∩ π ⁻¹' s = π'.domain ∩ π' ⁻¹' s := by rw [hπ.eqOn.inter_preimage_eq, EqOnDomain.domain_eq hπ]

/-- Two equivalent partial permutations are equal when the domain and domain are univ. -/
protected theorem EqOnDomain.eq (h : π ≈ π') (hπ : π.domain = univ) : π = π' := by
  apply PartialPerm.ext (fun x => h.2 _) (fun x => h.symm'.2 _) h.1 <;> simp [hπ]

/-- We define a preorder on partial permutations by saying `π ≤ π'` if the domain of `π` is contained
in the domain of `π'`, and the permutations agree on the domain of `π`. -/
instance : Preorder (PartialPerm α)
    where
  le π π' := π.domain ⊆ π'.domain ∧ π.domain.EqOn π π'
  le_refl a := ⟨subset_rfl, eqOn_refl _ _⟩
  le_trans a b c hab hbc := ⟨hab.1.trans hbc.1, hab.2.trans <| hbc.2.mono hab.1⟩

theorem domain_mono (h : π ≤ π') : π.domain ⊆ π'.domain :=
  h.1

theorem eqOn_domain_of_le (h : π ≤ π') : π.domain.EqOn π π' :=
  h.2

theorem le_of_eq_on_domain (h : π ≈ π') : π ≤ π' :=
  ⟨subset_of_eq h.1, h.2⟩

theorem apply_eq_of_le (h : π ≤ π') {x : α} (hx : x ∈ π.domain) : π' x = π x :=
  (eqOn_domain_of_le h hx).symm

section Piecewise

variable (π π')
variable [∀ j : α, Decidable (j ∈ π.domain)] {h : Disjoint π.domain π'.domain}

/-- Construct a partial permutation from two partial permutations with disjoint domains. -/
def piecewise (h : Disjoint π.domain π'.domain) : PartialPerm α
    where
  toFun := π.domain.piecewise π π'
  invFun := π.domain.piecewise π.symm π'.symm
  domain := π.domain ∪ π'.domain
  toFun_domain' := by
    rintro x (hx | hx)
    · rw [piecewise_eqOn π.domain π π' hx]
      exact Or.inl (π.map_domain hx)
    · rw [piecewise_eqOn_compl π.domain π π' (disjoint_right.mp h hx)]
      exact Or.inr (π'.map_domain hx)
  invFun_domain' := by
    rintro x (hx | hx)
    · rw [piecewise_eqOn π.domain π.symm π'.symm hx]
      exact Or.inl (π.symm.map_domain hx)
    · rw [piecewise_eqOn_compl π.domain π.symm π'.symm (disjoint_right.mp h hx)]
      exact Or.inr (π'.symm.map_domain hx)
  left_inv' := by
    rintro x (hx | hx)
    · rw [piecewise_eqOn π.domain π π' hx,
        piecewise_eqOn π.domain π.symm π'.symm (π.map_domain hx), π.left_inv hx]
    · rw [piecewise_eqOn_compl π.domain π π' (disjoint_right.mp h hx),
        piecewise_eqOn_compl π.domain π.symm π'.symm (disjoint_right.mp h (π'.map_domain hx)),
        π'.left_inv hx]
  right_inv' := by
    rintro x (hx | hx)
    · rw [piecewise_eqOn π.domain π.symm π'.symm hx,
        piecewise_eqOn π.domain π π' (π.symm.map_domain hx), π.right_inv hx]
    · rw [piecewise_eqOn_compl π.domain π.symm π'.symm (disjoint_right.mp h hx),
        piecewise_eqOn_compl π.domain π π' (disjoint_right.mp h (π'.symm.map_domain hx)),
        π'.right_inv hx]

variable {π π'}

@[simp]
theorem piecewise_domain : (piecewise π π' h).domain = π.domain ∪ π'.domain :=
  rfl

theorem mem_piecewise_domain_left {x : α} (hx : x ∈ π.domain) : x ∈ (piecewise π π' h).domain :=
  mem_union_left _ hx

theorem mem_piecewise_domain_right {x : α} (hx : x ∈ π'.domain) : x ∈ (piecewise π π' h).domain :=
  mem_union_right _ hx

theorem piecewise_apply_eq_left {x : α} (hx : x ∈ π.domain) : piecewise π π' h x = π x :=
  piecewise_eqOn _ _ _ hx

theorem piecewise_apply_eq_right {x : α} (hx : x ∈ π'.domain) : piecewise π π' h x = π' x :=
  piecewise_eqOn_compl _ _ _ (disjoint_right.mp h hx)

theorem le_piecewise_left : π ≤ piecewise π π' h :=
  ⟨subset_union_left, fun _ hx => (piecewise_apply_eq_left hx).symm⟩

theorem le_piecewise_right : π' ≤ piecewise π π' h :=
  ⟨subset_union_right, fun _ hx => (piecewise_apply_eq_right hx).symm⟩

end Piecewise

end PartialPerm

namespace Set

-- All arguments are explicit to avoid missing information in the pretty printer output
/-- A bijection between two sets `s : Set α` and `t : Set α` provides a partial permutation on `α`. -/
@[simps (config := { fullyApplied := false })]
noncomputable def BijOn.toPartialPerm [Nonempty α] (f : α → α) (s : Set α) (hf : BijOn f s s) :
    PartialPerm α where
  toFun := f
  invFun := invFunOn f s
  domain := s
  toFun_domain' := hf.mapsTo
  invFun_domain' := hf.surjOn.mapsTo_invFunOn
  left_inv' := hf.invOn_invFunOn.1
  right_inv' := hf.invOn_invFunOn.2

end Set

/-!
# `Perm.toPartialPerm`

A `Perm` can be be interpreted as a `PartialPerm`. We set up simp lemmas to reduce most
properties of the `PartialPerm` to that of the `Perm`.
-/

open Equiv

namespace Equiv.Perm

variable (π π' : Perm α)

@[simp]
theorem toPartialPerm_one : toPartialPerm (Equiv.refl α) = PartialPerm.refl α :=
  rfl

@[simp]
theorem toPartialPerm_inv : π⁻¹.toPartialPerm = π.toPartialPerm.symm :=
  rfl

@[simp]
theorem toPartialPerm_mul : (π * π').toPartialPerm = π'.toPartialPerm.trans π.toPartialPerm rfl :=
  PartialPerm.ext (fun _ => rfl) (fun _ => rfl) rfl

@[simp]
theorem toPartialEquiv_toPartialPerm : π.toPartialPerm.toPartialEquiv = π.toPartialEquiv :=
  rfl

end Equiv.Perm
