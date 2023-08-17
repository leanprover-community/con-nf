/-
Copyright (c) 2023 Yaël Dillies, Sky Wilshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sky Wilshaw
-/
import Mathbin.GroupTheory.Perm.Basic
import Mathbin.Logic.Equiv.LocalEquiv

#align_import mathlib.logic.equiv.local_perm

/-!
# Local equivalences

This files defines permutations on a set.

A local permutation on `α` is a domain `set α` and two functions `α → α` that map `domain` to
`domain` and are inverse to each other on `domain`.

## Main declarations

* `local_perm α`: The type of local permutations on `α`.
* `equiv.to_local_perm`: Reinter
-/


open Function Set

variable {α : Type _}

/-- A local permutation of a subset `domain` of `α`. The (global) maps `to_fun : α → α` and
`inv_fun : α → α` map `domain` to itself, and are inverse to each other there. The values of
`to_fun` and `inv_fun` outside of `domain` are irrelevant. -/
structure LocalPerm (α : Type _) where
  (toFun invFun : α → α)
  domain : Set α
  toFun_domain' : ∀ ⦃x⦄, x ∈ domain → to_fun x ∈ domain
  invFun_domain' : ∀ ⦃x⦄, x ∈ domain → inv_fun x ∈ domain
  left_inv' : ∀ ⦃x⦄, x ∈ domain → inv_fun (to_fun x) = x
  right_inv' : ∀ ⦃x⦄, x ∈ domain → to_fun (inv_fun x) = x

/-- A `perm` gives rise to a `local_perm` Associating a local_perm to an equiv -/
def Equiv.Perm.toLocalPerm (π : Equiv.Perm α) : LocalPerm α
    where
  toFun := π
  invFun := π.symm
  domain := univ
  toFun_domain' x hx := mem_univ _
  invFun_domain' y hy := mem_univ _
  left_inv' x hx := π.left_inv x
  right_inv' x hx := π.right_inv x

namespace LocalPerm

variable (π π' : LocalPerm α)

/-- The inverse of a local permutation. -/
protected def symm : LocalPerm α where
  toFun := π.invFun
  invFun := π.toFun
  domain := π.domain
  toFun_domain' := π.invFun_domain'
  invFun_domain' := π.toFun_domain'
  left_inv' := π.right_inv'
  right_inv' := π.left_inv'

instance : CoeFun (LocalPerm α) fun _ => α → α :=
  ⟨LocalPerm.toFun⟩

/-- See Note [custom simps projection] -/
def Simps.symmApply (π : LocalPerm α) : α → α :=
  π.symm

initialize_simps_projections LocalPerm (toFun → apply, invFun → symm_apply)

@[simp]
theorem coe_mk (f : α → α) (g s ml mr il ir) : (LocalPerm.mk f g s ml mr il ir : α → α) = f :=
  rfl

@[simp]
theorem coe_symm_mk (f : α → α) (g s ml mr il ir) :
    ((LocalPerm.mk f g s ml mr il ir).symm : α → α) = g :=
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
theorem iterate_domain {x : α} (h : x ∈ π.domain) {n : ℕ} : (π^[n]) x ∈ π.domain :=
  by
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

protected theorem mapsTo : MapsTo π π.domain π.domain := fun x => π.map_domain

protected theorem leftInvOn : LeftInvOn π.symm π π.domain := fun x => π.left_inv

protected theorem rightInvOn : RightInvOn π.symm π π.domain := fun x => π.right_inv

protected theorem invOn : InvOn π.symm π π.domain π.domain :=
  ⟨π.LeftInvOn, π.RightInvOn⟩

protected theorem injOn : InjOn π π.domain :=
  π.LeftInvOn.InjOn

protected theorem bijOn : BijOn π π.domain π.domain :=
  π.InvOn.BijOn π.MapsTo π.symm.MapsTo

protected theorem surjOn : SurjOn π π.domain π.domain :=
  π.BijOn.SurjOn

/-- Create a copy of a `local_perm` providing better definitional equalities. -/
@[simps (config := { fullyApplied := false })]
def copy (π : LocalPerm α) (f : α → α) (hf : ⇑π = f) (g : α → α) (hg : ⇑π.symm = g) (s : Set α)
    (hs : π.domain = s) : LocalPerm α where
  toFun := f
  invFun := g
  domain := s
  toFun_domain' := hs ▸ hf ▸ π.toFun_domain'
  invFun_domain' := hs ▸ hg ▸ π.invFun_domain'
  left_inv' x := hs ▸ hf ▸ hg ▸ π.left_inv
  right_inv' x := hs ▸ hf ▸ hg ▸ π.right_inv

theorem copy_eq (π : LocalPerm α) (f : α → α) (hf : ⇑π = f) (g : α → α) (hg : ⇑π.symm = g)
    (s : Set α) (hs : π.domain = s) : π.copy f hf g hg s hs = π := by substs f g s; cases π; rfl

/-- Associating to a local_perm a permutation of the domain. -/
protected def toPerm : Equiv.Perm π.domain
    where
  toFun x := ⟨π x, π.map_domain x.Mem⟩
  invFun y := ⟨π.symm y, π.symm.map_domain y.Mem⟩
  left_inv := fun ⟨x, hx⟩ => Subtype.eq <| π.left_inv hx
  right_inv := fun ⟨y, hy⟩ => Subtype.eq <| π.right_inv hy

@[simp]
theorem image_domain : π '' π.domain = π.domain :=
  π.BijOn.image_eq

theorem forall_mem_domain {p : α → Prop} : (∀ y ∈ π.domain, p y) ↔ ∀ x ∈ π.domain, p (π x) := by
  conv_lhs => rw [← image_domain, ball_image_iff]

theorem exists_mem_domain {p : α → Prop} : (∃ y ∈ π.domain, p y) ↔ ∃ x ∈ π.domain, p (π x) := by
  conv_lhs => rw [← image_domain, bex_image_iff]

/-- A set `s` is *stable* under a local equivalence `π` if it preserved by it. -/
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

protected theorem mapsTo (h : π.IsStable s) : MapsTo π (π.domain ∩ s) (π.domain ∩ s) := fun x hx =>
  ⟨π.MapsTo hx.1, (h hx.1).2 hx.2⟩

theorem symm_mapsTo (h : π.IsStable s) : MapsTo π.symm (π.domain ∩ s) (π.domain ∩ s) :=
  h.symm.MapsTo

/-- Restrict a `local_perm` to a stable subset. -/
@[simps (config := { fullyApplied := false })]
def restr (h : π.IsStable s) : LocalPerm α
    where
  toFun := π
  invFun := π.symm
  domain := π.domain ∩ s
  toFun_domain' := h.MapsTo
  invFun_domain' := h.symm_mapsTo
  left_inv' := π.LeftInvOn.mono (inter_subset_left _ _)
  right_inv' := π.RightInvOn.mono (inter_subset_left _ _)

theorem image_eq (h : π.IsStable s) : π '' (π.domain ∩ s) = π.domain ∩ s :=
  h.restr.image_domain

theorem symm_image_eq (h : π.IsStable s) : π.symm '' (π.domain ∩ s) = π.domain ∩ s :=
  h.symm.image_eq

theorem iff_preimage_eq : π.IsStable s ↔ π.domain ∩ π ⁻¹' s = π.domain ∩ s := by
  simp only [is_stable, Set.ext_iff, mem_inter_iff, and_congr_right_iff, mem_preimage]

alias iff_preimage_eq ↔ preimage_eq of_preimage_eq

theorem iff_symm_preimage_eq : π.IsStable s ↔ π.domain ∩ π.symm ⁻¹' s = π.domain ∩ s :=
  symm_iff.symm.trans iff_preimage_eq

alias iff_symm_preimage_eq ↔ symm_preimage_eq of_symm_preimage_eq

-- lemma of_image_eq (h : π '' (π.domain ∩ s) = π.domain ∩ s) : π.is_stable s :=
-- of_symm_preimage_eq $ eq.trans (of_symm_preimage_eq rfl).image_eq.symm h
-- lemma of_symm_image_eq (h : π.symm '' (π.domain ∩ s) = π.domain ∩ s) : π.is_stable s :=
-- of_preimage_eq $ eq.trans (of_preimage_eq rfl).symm_image_eq.symm h
protected theorem compl (h : π.IsStable s) : π.IsStable (sᶜ) := fun x hx => not_congr (h hx)

protected theorem inter {s'} (h : π.IsStable s) (h' : π.IsStable s') : π.IsStable (s ∩ s') :=
  fun x hx => and_congr (h hx) (h' hx)

protected theorem union {s'} (h : π.IsStable s) (h' : π.IsStable s') : π.IsStable (s ∪ s') :=
  fun x hx => or_congr (h hx) (h' hx)

protected theorem diff {s'} (h : π.IsStable s) (h' : π.IsStable s') : π.IsStable (s \ s') :=
  h.inter h'.compl

theorem leftInvOn_piecewise {π' : LocalPerm α} [∀ i, Decidable (i ∈ s)] (h : π.IsStable s)
    (h' : π'.IsStable s) :
    LeftInvOn (s.piecewise π.symm π'.symm) (s.piecewise π π') (s.ite π.domain π'.domain) :=
  by
  rintro x (⟨he, hs⟩ | ⟨he, hs : x ∉ s⟩)
  · rw [piecewise_eq_of_mem _ _ _ hs, piecewise_eq_of_mem _ _ _ ((h he).2 hs), π.left_inv he]
  ·
    rw [piecewise_eq_of_not_mem _ _ _ hs, piecewise_eq_of_not_mem _ _ _ ((h'.compl he).2 hs),
      π'.left_inv he]

theorem inter_eq_of_inter_eq_of_eqOn {π' : LocalPerm α} (h : π.IsStable s) (h' : π'.IsStable s)
    (hs : π.domain ∩ s = π'.domain ∩ s) (Heq : EqOn π π' (π.domain ∩ s)) :
    π.domain ∩ s = π'.domain ∩ s := by rw [← h.image_eq, ← h'.image_eq, ← hs, Heq.image_eq]

theorem symm_eqOn_of_inter_eq_of_eqOn {π' : LocalPerm α} (h : π.IsStable s)
    (hs : π.domain ∩ s = π'.domain ∩ s) (Heq : EqOn π π' (π.domain ∩ s)) :
    EqOn π.symm π'.symm (π.domain ∩ s) :=
  by
  rw [← h.image_eq]
  rintro y ⟨x, hx, rfl⟩
  have hx' := hx; rw [hs] at hx' 
  rw [π.left_inv hx.1, Heq hx, π'.left_inv hx'.1]

end IsStable

theorem image_domain_inter_eq' (s : Set α) : π '' (π.domain ∩ s) = π.domain ∩ π.symm ⁻¹' s := by
  rw [inter_comm, π.left_inv_on.image_inter', image_domain, inter_comm]

theorem image_domain_inter_eq (s : Set α) :
    π '' (π.domain ∩ s) = π.domain ∩ π.symm ⁻¹' (π.domain ∩ s) := by
  rw [inter_comm, π.left_inv_on.image_inter, image_domain, inter_comm]

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
  ext fun x => ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, π.map_domain hx.1, hx.2⟩⟩

theorem domain_inter_inv_preimage_preimage (s : Set α) :
    π.domain ∩ π.symm ⁻¹' (π ⁻¹' s) = π.domain ∩ s :=
  π.symm.domain_inter_preimage_inv_preimage _

theorem symm_image_image_of_subset_domain {s : Set α} (h : s ⊆ π.domain) : π.symm '' (π '' s) = s :=
  (π.LeftInvOn.mono h).image_image

theorem image_symm_image_of_subset_domain {s : Set α} (h : s ⊆ π.domain) : π '' (π.symm '' s) = s :=
  π.symm.symm_image_image_of_subset_domain h

variable {π π'}

theorem domain_subset_preimage_domain : π.domain ⊆ π ⁻¹' π.domain :=
  π.MapsTo

theorem symm_image_domain : π.symm '' π.domain = π.domain :=
  π.symm.image_domain

/-- Two local equivs that have the same `domain`, same `to_fun` and same `inv_fun`, coincide. -/
@[ext]
protected theorem ext (h : ∀ x, π x = π' x) (hsymm : ∀ x, π.symm x = π'.symm x)
    (hs : π.domain = π'.domain) : π = π' :=
  by
  have A : (π : α → α) = π' := by ext x; exact h x
  have B : (π.symm : α → α) = π'.symm := by ext x; exact hsymm x
  have I : π '' π.domain = π.domain := π.image_domain
  have I' : π' '' π'.domain = π'.domain := π'.image_domain
  rw [A, hs, I'] at I 
  cases π <;> cases π'
  simp_all only [coe_symm_mk, coe_mk, eq_self_iff_true, and_self_iff]

/-- The identity local equivalence. -/
protected def refl (α : Type _) : LocalPerm α :=
  Equiv.Perm.toLocalPerm <| Equiv.refl _

@[simp]
theorem refl_domain : (LocalPerm.refl α).domain = univ :=
  rfl

@[simp, norm_cast]
theorem coe_refl : ⇑(LocalPerm.refl α) = id :=
  rfl

@[simp]
theorem symm_refl : (LocalPerm.refl α).symm = LocalPerm.refl α :=
  rfl

instance : Inhabited (LocalPerm α) :=
  ⟨LocalPerm.refl _⟩

variable (π π')

-- TODO: Clean up these proofs
/-- Composing two local equivs if the domain of the first coincides with the domain of the
second. -/
@[simps]
protected def trans (π' : LocalPerm α) (h : π.domain = π'.domain) : LocalPerm α
    where
  toFun := π' ∘ π
  invFun := π.symm ∘ π'.symm
  domain := π.domain
  toFun_domain' x hx := by
    rw [h]
    refine' map_domain _ _
    have := map_domain π hx
    rwa [h] at this 
  invFun_domain' y hy :=
    map_domain _
      (by
        rw [h] at hy 
        have := map_domain π'.symm hy
        rwa [symm_domain, ← h] at this )
  left_inv' x hx := by simp [hx, h.symm]
  right_inv' y hy := by
    simp
    rw [h] at hy 
    rw [right_inv π, right_inv π' hy]
    have := map_domain π'.symm hy
    rwa [symm_domain, ← h] at this 

/-- The identity local equiv on a set `s` -/
def ofSet (s : Set α) : LocalPerm α where
  toFun := id
  invFun := id
  domain := s
  toFun_domain' x hx := hx
  invFun_domain' x hx := hx
  left_inv' x hx := rfl
  right_inv' x hx := rfl

@[simp]
theorem ofSet_domain (s : Set α) : (ofSet s).domain = s :=
  rfl

@[simp, norm_cast]
theorem coe_ofSet (s : Set α) : (ofSet s : α → α) = id :=
  rfl

@[simp]
theorem ofSet_symm (s : Set α) : (ofSet s).symm = ofSet s :=
  rfl

@[simp]
theorem ofSet_trans_ofSet (s : Set α) : (ofSet s).trans (ofSet s) rfl = ofSet s :=
  rfl

@[simp]
theorem ofSet_univ : ofSet univ = LocalPerm.refl α :=
  rfl

/-- Reinterpret a local permutation as a local equivalence. -/
def toLocalEquiv : LocalEquiv α α where
  toFun := π
  invFun := π.symm
  source := π.domain
  target := π.domain
  map_source' := π.MapsTo
  map_target' := π.symm.MapsTo
  left_inv' := π.LeftInvOn
  right_inv' := π.RightInvOn

@[simp]
theorem coe_toLocalEquiv : ⇑π.toLocalEquiv = π :=
  rfl

@[simp]
theorem coe_toLocalEquiv_symm : ⇑π.toLocalEquiv.symm = π.symm :=
  rfl

@[simp]
theorem toLocalEquiv_source : π.toLocalEquiv.source = π.domain :=
  rfl

@[simp]
theorem toLocalEquiv_target : π.toLocalEquiv.target = π.domain :=
  rfl

@[simp]
theorem toLocalEquiv_refl : (LocalPerm.refl α).toLocalEquiv = LocalEquiv.refl _ :=
  rfl

@[simp]
theorem toLocalEquiv_symm : π.symm.toLocalEquiv = π.toLocalEquiv.symm :=
  rfl

@[simp]
theorem toLocalEquiv_trans (h) :
    (π.trans π' h).toLocalEquiv = π.toLocalEquiv.trans π'.toLocalEquiv :=
  by
  ext
  · simp
  · simp
  · simpa [← h] using fun hx => π.maps_to hx

/-- `eq_on_domain π π'` means that `π` and `π'` have the same domain, and coincide there. Then `π`
and `π'` should really be considered the same local permutation. -/
def EqOnDomain : Prop :=
  π.domain = π'.domain ∧ π.domain.EqOn π π'

/-- `eq_on_domain` is an equivalence relation -/
instance eqOnDomainSetoid : Setoid (LocalPerm α)
    where
  R := EqOnDomain
  iseqv :=
    ⟨fun e => by simp [eq_on_domain], fun e e' h => by simp [eq_on_domain, h.1.symm];
      exact fun x hx => (h.2 hx).symm, fun e e' e'' h h' =>
      ⟨by rwa [← h'.1, ← h.1], fun x hx => by rw [← h'.2, h.2 hx]; rwa [← h.1]⟩⟩

variable {π π'}

theorem eq_on_domain_refl : π ≈ π :=
  Setoid.refl _

/-- Two equivalent local equivs have the same domain -/
theorem EqOnDomain.domain_eq (h : π ≈ π') : π.domain = π'.domain :=
  h.1

/-- Two equivalent local equivs coincide on the domain -/
theorem EqOnDomain.eqOn (h : π ≈ π') : π.domain.EqOn π π' :=
  h.2

/-- If two local equivs are equivalent, so are their inverses. -/
theorem EqOnDomain.symm' (h : π ≈ π') : π.symm ≈ π'.symm :=
  by
  refine' ⟨h.domain_eq, eq_on_of_left_inv_on_of_right_inv_on π.left_inv_on _ _⟩ <;>
    simp only [symm_domain, h.domain_eq, h.domain_eq, π'.symm.maps_to]
  exact π'.right_inv_on.congr_right π'.symm.maps_to (h.domain_eq ▸ h.eq_on.symm)
  exact π'.symm.maps_to

/-- Two equivalent local equivs have coinciding inverses on the domain -/
theorem EqOnDomain.symm_eqOn (h : π ≈ π') : EqOn π.symm π'.symm π.domain :=
  h.symm'.EqOn

/-- Preimages are respected by equivalence -/
theorem EqOnDomain.domain_inter_preimage_eq (hπ : π ≈ π') (s : Set α) :
    π.domain ∩ π ⁻¹' s = π'.domain ∩ π' ⁻¹' s := by rw [hπ.eq_on.inter_preimage_eq, hπ.domain_eq]

/-- Two equivalent local equivs are equal when the domain and domain are univ -/
protected theorem EqOnDomain.eq (h : π ≈ π') (hπ : π.domain = univ) : π = π' := by
  apply LocalPerm.ext (fun x => h.2 _) (fun x => h.symm'.2 _) h.1 <;> simp [hπ]

/-- We define a preorder on local permutations by saying `π ≤ π'` if the domain of `π` is contained
in the domain of `π'`, and the permutations agree on the domain of `π`. -/
instance : Preorder (LocalPerm α)
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

variable (π π') [∀ j : α, Decidable (j ∈ π.domain)] {h : Disjoint π.domain π'.domain}

/-- Construct a local permutation from two local permutations with disjoint domains. -/
def piecewise (h : Disjoint π.domain π'.domain) : LocalPerm α
    where
  toFun := π.domain.piecewise π π'
  invFun := π.domain.piecewise π.symm π'.symm
  domain := π.domain ∪ π'.domain
  toFun_domain' := by
    rintro x (hx | hx)
    · rw [piecewise_eq_on π.domain π π' hx]
      exact Or.inl (π.map_domain hx)
    · rw [piecewise_eq_on_compl π.domain π π' (disjoint_right.mp h hx)]
      exact Or.inr (π'.map_domain hx)
  invFun_domain' := by
    rintro x (hx | hx)
    · rw [piecewise_eq_on π.domain π.symm π'.symm hx]
      exact Or.inl (π.symm.map_domain hx)
    · rw [piecewise_eq_on_compl π.domain π.symm π'.symm (disjoint_right.mp h hx)]
      exact Or.inr (π'.symm.map_domain hx)
  left_inv' := by
    rintro x (hx | hx)
    ·
      rw [piecewise_eq_on π.domain π π' hx,
        piecewise_eq_on π.domain π.symm π'.symm (π.map_domain hx), π.left_inv hx]
    ·
      rw [piecewise_eq_on_compl π.domain π π' (disjoint_right.mp h hx),
        piecewise_eq_on_compl π.domain π.symm π'.symm (disjoint_right.mp h (π'.map_domain hx)),
        π'.left_inv hx]
  right_inv' := by
    rintro x (hx | hx)
    ·
      rw [piecewise_eq_on π.domain π.symm π'.symm hx,
        piecewise_eq_on π.domain π π' (π.symm.map_domain hx), π.right_inv hx]
    ·
      rw [piecewise_eq_on_compl π.domain π.symm π'.symm (disjoint_right.mp h hx),
        piecewise_eq_on_compl π.domain π π' (disjoint_right.mp h (π'.symm.map_domain hx)),
        π'.right_inv hx]

variable {π π' h}

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
  ⟨subset_union_left _ _, fun x hx => (piecewise_apply_eq_left hx).symm⟩

theorem le_piecewise_right : π' ≤ piecewise π π' h :=
  ⟨subset_union_right _ _, fun x hx => (piecewise_apply_eq_right hx).symm⟩

end Piecewise

end LocalPerm

namespace Set

-- All arguments are explicit to avoid missing information in the pretty printer output
/-- A bijection between two sets `s : set α` and `t : set α` provides a local permutation on `α`. -/
@[simps (config := { fullyApplied := false })]
noncomputable def BijOn.toLocalPerm [Nonempty α] (f : α → α) (s : Set α) (hf : BijOn f s s) :
    LocalPerm α where
  toFun := f
  invFun := invFunOn f s
  domain := s
  toFun_domain' := hf.MapsTo
  invFun_domain' := hf.SurjOn.mapsTo_invFunOn
  left_inv' := hf.invOn_invFunOn.1
  right_inv' := hf.invOn_invFunOn.2

end Set

/-!
# `equiv.to_local_perm`

An `equiv` can be be interpreted give rise to local_perm. We set up simp lemmas to reduce most
properties of the local equiv to that of the equiv.
-/


open Equiv

namespace Equiv.Perm

variable (π π' : Perm α)

@[simp]
theorem toLocalPerm_one : toLocalPerm (Equiv.refl α) = LocalPerm.refl α :=
  rfl

@[simp]
theorem toLocalPerm_inv : π⁻¹.toLocalPerm = π.toLocalPerm.symm :=
  rfl

@[simp]
theorem toLocalPerm_hMul : (π * π').toLocalPerm = π'.toLocalPerm.trans π.toLocalPerm rfl :=
  LocalPerm.ext (fun x => rfl) (fun x => rfl) rfl

@[simp]
theorem toLocalEquiv_toLocalPerm : π.toLocalPerm.toLocalEquiv = π.toLocalEquiv :=
  rfl

end Equiv.Perm

