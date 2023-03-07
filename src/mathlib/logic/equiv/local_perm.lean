/-
Copyright (c) 2023 Yaël Dillies, Sky Wilshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sky Wilshaw
-/
import group_theory.perm.basic
import logic.equiv.local_equiv

/-!
# Local equivalences

This files defines permutations on a set.

A local permutation on `α` is a domain `set α` and two functions `α → α` that map `domain` to
`domain` and are inverse to each other on `domain`.

## Main declarations

* `local_perm α`: The type of local permutations on `α`.
* `equiv.to_local_perm`: Reinter
-/


open function set

variables {α : Type*}

/-- A local permutation of a subset `domain` of `α`. The (global) maps `to_fun : α → α` and
`inv_fun : α → α` map `domain` to itself, and are inverse to each other there. The values of
`to_fun` and `inv_fun` outside of `domain` are irrelevant. -/
structure local_perm (α : Type*) :=
(to_fun inv_fun : α → α)
(domain : set α)
(to_fun_domain' : ∀ ⦃x⦄, x ∈ domain → to_fun x ∈ domain)
(inv_fun_domain' : ∀ ⦃x⦄, x ∈ domain → inv_fun x ∈ domain)
(left_inv' : ∀ ⦃x⦄, x ∈ domain → inv_fun (to_fun x) = x)
(right_inv' : ∀ ⦃x⦄, x ∈ domain → to_fun (inv_fun x) = x)

/-- A `perm` gives rise to a `local_perm` Associating a local_perm to an equiv -/
def equiv.perm.to_local_perm (π : equiv.perm α) : local_perm α :=
{ to_fun := π,
  inv_fun := π.symm,
  domain := univ,
  to_fun_domain' := λ x hx, mem_univ _,
  inv_fun_domain' := λ y hy, mem_univ _,
  left_inv' := λ x hx, π.left_inv x,
  right_inv' := λ x hx, π.right_inv x }

namespace local_perm
variables (π π' : local_perm α)

/-- The inverse of a local permutation. -/
protected def symm : local_perm α :=
{ to_fun := π.inv_fun,
  inv_fun := π.to_fun,
  domain := π.domain,
  to_fun_domain' := π.inv_fun_domain',
  inv_fun_domain' := π.to_fun_domain',
  left_inv' := π.right_inv',
  right_inv' := π.left_inv' }

instance : has_coe_to_fun (local_perm α) (λ _, α → α) := ⟨local_perm.to_fun⟩

/-- See Note [custom simps projection] -/
def simps.symm_apply (π : local_perm α) : α → α := π.symm

initialize_simps_projections local_perm (to_fun → apply, inv_fun → symm_apply)

@[simp] theorem coe_mk (f : α → α) (g s ml mr il ir) :
  (local_perm.mk f g s ml mr il ir : α → α) = f := rfl

@[simp] theorem coe_symm_mk (f : α → α) (g s ml mr il ir) :
  ((local_perm.mk f g s ml mr il ir).symm : α → α) = g := rfl

@[simp] lemma to_fun_as_coe : π.to_fun = π := rfl
@[simp] lemma inv_fun_as_coe : π.inv_fun = π.symm := rfl

@[simp] lemma map_domain {x : α} (h : x ∈ π.domain) : π x ∈ π.domain := π.to_fun_domain' h
@[simp] lemma iterate_domain {x : α} (h : x ∈ π.domain) {n : ℕ} : π^[n] x ∈ π.domain :=
begin
  induction n with n ih,
  exact h,
  rw function.iterate_succ',
  exact π.map_domain ih,
end

@[simp] lemma left_inv {x : α} (h : x ∈ π.domain) : π.symm (π x) = x := π.left_inv' h
@[simp] lemma right_inv {x : α} (h : x ∈ π.domain) : π (π.symm x) = x := π.right_inv' h

@[simp] lemma symm_domain : π.symm.domain = π.domain := rfl
@[simp] lemma symm_symm : π.symm.symm = π := by { cases π, refl }

lemma eq_symm_apply {x : α} {y : α} (hx : x ∈ π.domain) (hy : y ∈ π.domain) :
  x = π.symm y ↔ π x = y :=
⟨λ h, by rw [← π.right_inv hy, h], λ h, by rw [← π.left_inv hx, h]⟩

protected lemma maps_to : maps_to π π.domain π.domain := λ x, π.map_domain
protected lemma left_inv_on : left_inv_on π.symm π π.domain := λ x, π.left_inv
protected lemma right_inv_on : right_inv_on π.symm π π.domain := λ x, π.right_inv
protected lemma inv_on : inv_on π.symm π π.domain π.domain := ⟨π.left_inv_on, π.right_inv_on⟩
protected lemma inj_on : inj_on π π.domain := π.left_inv_on.inj_on
protected lemma bij_on : bij_on π π.domain π.domain := π.inv_on.bij_on π.maps_to π.symm.maps_to
protected lemma surj_on : surj_on π π.domain π.domain := π.bij_on.surj_on

/-- Create a copy of a `local_perm` providing better definitional equalities. -/
@[simps {fully_applied := ff}]
def copy (π : local_perm α) (f : α → α) (hf : ⇑π = f) (g : α → α) (hg : ⇑π.symm = g)
  (s : set α) (hs : π.domain = s) :
  local_perm α :=
{ to_fun := f,
  inv_fun := g,
  domain := s,
  to_fun_domain' := hs ▸ hf ▸ π.to_fun_domain',
  inv_fun_domain' := hs ▸ hg ▸ π.inv_fun_domain',
  left_inv' := λ x, hs ▸ hf ▸ hg ▸ π.left_inv,
  right_inv' := λ x, hs ▸ hf ▸ hg ▸ π.right_inv }

lemma copy_eq (π : local_perm α) (f : α → α) (hf : ⇑π = f) (g : α → α) (hg : ⇑π.symm = g)
  (s : set α) (hs : π.domain = s) :
  π.copy f hf g hg s hs = π :=
by { substs f g s, cases π, refl }

/-- Associating to a local_perm a permutation of the domain. -/
protected def to_perm : equiv.perm π.domain :=
{ to_fun := λ x, ⟨π x, π.map_domain x.mem⟩,
  inv_fun := λ y, ⟨π.symm y, π.symm.map_domain y.mem⟩,
  left_inv := λ ⟨x, hx⟩, subtype.eq $ π.left_inv hx,
  right_inv := λ ⟨y, hy⟩, subtype.eq $ π.right_inv hy }

@[simp] lemma image_domain : π '' π.domain = π.domain := π.bij_on.image_eq

lemma forall_mem_domain {p : α → Prop} : (∀ y ∈ π.domain, p y) ↔ ∀ x ∈ π.domain, p (π x) :=
by conv_lhs { rw [←image_domain, ball_image_iff] }

lemma exists_mem_domain {p : α → Prop} : (∃ y ∈ π.domain, p y) ↔ ∃ x ∈ π.domain, p (π x) :=
by conv_lhs { rw [←image_domain, bex_image_iff] }

/-- A set `s` is *stable* under a local equivalence `π` if it preserved by it. -/
def is_stable (s : set α) : Prop := ∀ ⦃x⦄, x ∈ π.domain → (π x ∈ s ↔ x ∈ s)

namespace is_stable

variables {π π'} {s : set α} {x y : α}

lemma apply_mem_iff (h : π.is_stable s) (hx : x ∈ π.domain) : π x ∈ s ↔ x ∈ s := h hx

lemma symm_apply_mem_iff (h : π.is_stable s) : ∀ ⦃y⦄, y ∈ π.domain → (π.symm y ∈ s ↔ y ∈ s) :=
π.forall_mem_domain.mpr $ λ x hx, by rw [π.left_inv hx, h hx]

protected lemma symm (h : π.is_stable s) : π.symm.is_stable s := h.symm_apply_mem_iff

@[simp] lemma symm_iff : π.symm.is_stable s ↔ π.is_stable s := ⟨λ h, h.symm, λ h, h.symm⟩

protected lemma maps_to (h : π.is_stable s) : maps_to π (π.domain ∩ s) (π.domain ∩ s) :=
λ x hx, ⟨π.maps_to hx.1, (h hx.1).2 hx.2⟩

lemma symm_maps_to (h : π.is_stable s) : maps_to π.symm (π.domain ∩ s) (π.domain ∩ s) :=
h.symm.maps_to

/-- Restrict a `local_perm` to a stable subset. -/
@[simps {fully_applied := ff}] def restr (h : π.is_stable s) : local_perm α :=
{ to_fun := π,
  inv_fun := π.symm,
  domain := π.domain ∩ s,
  to_fun_domain' := h.maps_to,
  inv_fun_domain' := h.symm_maps_to,
  left_inv' := π.left_inv_on.mono (inter_subset_left _ _),
  right_inv' := π.right_inv_on.mono (inter_subset_left _ _) }

lemma image_eq (h : π.is_stable s) : π '' (π.domain ∩ s) = π.domain ∩ s :=
h.restr.image_domain

lemma symm_image_eq (h : π.is_stable s) : π.symm '' (π.domain ∩ s) = π.domain ∩ s :=
h.symm.image_eq

lemma iff_preimage_eq : π.is_stable s ↔ π.domain ∩ π ⁻¹' s = π.domain ∩ s :=
by simp only [is_stable, set.ext_iff, mem_inter_iff, and.congr_right_iff, mem_preimage]

alias iff_preimage_eq ↔ preimage_eq of_preimage_eq

lemma iff_symm_preimage_eq : π.is_stable s ↔ π.domain ∩ π.symm ⁻¹' s = π.domain ∩ s :=
symm_iff.symm.trans iff_preimage_eq

alias iff_symm_preimage_eq ↔ symm_preimage_eq of_symm_preimage_eq

-- lemma of_image_eq (h : π '' (π.domain ∩ s) = π.domain ∩ s) : π.is_stable s :=
-- of_symm_preimage_eq $ eq.trans (of_symm_preimage_eq rfl).image_eq.symm h

-- lemma of_symm_image_eq (h : π.symm '' (π.domain ∩ s) = π.domain ∩ s) : π.is_stable s :=
-- of_preimage_eq $ eq.trans (of_preimage_eq rfl).symm_image_eq.symm h

protected lemma compl (h : π.is_stable s) : π.is_stable sᶜ := λ x hx, not_congr (h hx)

protected lemma inter {s'} (h : π.is_stable s) (h' : π.is_stable s') : π.is_stable (s ∩ s') :=
λ x hx, and_congr (h hx) (h' hx)

protected lemma union {s'} (h : π.is_stable s) (h' : π.is_stable s') : π.is_stable (s ∪ s') :=
λ x hx, or_congr (h hx) (h' hx)

protected lemma diff {s'} (h : π.is_stable s) (h' : π.is_stable s') : π.is_stable (s \ s') :=
h.inter h'.compl

lemma left_inv_on_piecewise {π' : local_perm α} [Π i, decidable (i ∈ s)]
  (h : π.is_stable s) (h' : π'.is_stable s) :
  left_inv_on (s.piecewise π.symm π'.symm) (s.piecewise π π') (s.ite π.domain π'.domain) :=
begin
  rintro x (⟨he, hs⟩ | ⟨he, hs : x ∉ s⟩),
  { rw [piecewise_eq_of_mem _ _ _ hs, piecewise_eq_of_mem _ _ _ ((h he).2 hs), π.left_inv he] },
  { rw [piecewise_eq_of_not_mem _ _ _ hs, piecewise_eq_of_not_mem _ _ _ ((h'.compl he).2 hs),
      π'.left_inv he] }
end

lemma inter_eq_of_inter_eq_of_eq_on {π' : local_perm α} (h : π.is_stable s)
  (h' : π'.is_stable s) (hs : π.domain ∩ s = π'.domain ∩ s) (Heq : eq_on π π' (π.domain ∩ s)) :
  π.domain ∩ s = π'.domain ∩ s :=
by rw [← h.image_eq, ← h'.image_eq, ← hs, Heq.image_eq]

lemma symm_eq_on_of_inter_eq_of_eq_on {π' : local_perm α} (h : π.is_stable s)
  (hs : π.domain ∩ s = π'.domain ∩ s) (Heq : eq_on π π' (π.domain ∩ s)) :
  eq_on π.symm π'.symm (π.domain ∩ s) :=
begin
  rw ←h.image_eq,
  rintro y ⟨x, hx, rfl⟩,
  have hx' := hx, rw hs at hx',
  rw [π.left_inv hx.1, Heq hx, π'.left_inv hx'.1]
end

end is_stable

lemma image_domain_inter_eq' (s : set α) :
  π '' (π.domain ∩ s) = π.domain ∩ π.symm ⁻¹' s :=
by rw [inter_comm, π.left_inv_on.image_inter', image_domain, inter_comm]

lemma image_domain_inter_eq (s : set α) :
  π '' (π.domain ∩ s) = π.domain ∩ π.symm ⁻¹' (π.domain ∩ s) :=
by rw [inter_comm, π.left_inv_on.image_inter, image_domain, inter_comm]

lemma image_eq_domain_inter_inv_preimage {s : set α} (h : s ⊆ π.domain) :
  π '' s = π.domain ∩ π.symm ⁻¹' s :=
by rw [← π.image_domain_inter_eq', inter_eq_self_of_subset_right h]

lemma symm_image_eq_domain_inter_preimage {s : set α} (h : s ⊆ π.domain) :
  π.symm '' s = π.domain ∩ π ⁻¹' s :=
π.symm.image_eq_domain_inter_inv_preimage h

lemma symm_image_domain_inter_eq (s : set α) :
  π.symm '' (π.domain ∩ s) = π.domain ∩ π ⁻¹' (π.domain ∩ s) :=
π.symm.image_domain_inter_eq _

lemma symm_image_domain_inter_eq' (s : set α) : π.symm '' (π.domain ∩ s) = π.domain ∩ π ⁻¹' s :=
π.symm.image_domain_inter_eq' _

lemma domain_inter_preimage_inv_preimage (s : set α) :
  π.domain ∩ π ⁻¹' (π.symm ⁻¹' s) = π.domain ∩ s :=
set.ext $ λ x, and.congr_right_iff.2 $ λ hx, by simp only [mem_preimage, π.left_inv hx]

lemma domain_inter_preimage_domain_inter (s : set α) :
  π.domain ∩ (π ⁻¹' (π.domain ∩ s)) = π.domain ∩ (π ⁻¹' s) :=
ext $ λ x, ⟨λ hx, ⟨hx.1, hx.2.2⟩, λ hx, ⟨hx.1, π.map_domain hx.1, hx.2⟩⟩

lemma domain_inter_inv_preimage_preimage (s : set α) :
  π.domain ∩ π.symm ⁻¹' (π ⁻¹' s) = π.domain ∩ s :=
π.symm.domain_inter_preimage_inv_preimage _

lemma symm_image_image_of_subset_domain {s : set α} (h : s ⊆ π.domain) : π.symm '' (π '' s) = s :=
(π.left_inv_on.mono h).image_image

lemma image_symm_image_of_subset_domain {s : set α} (h : s ⊆ π.domain) : π '' (π.symm '' s) = s :=
π.symm.symm_image_image_of_subset_domain h

variables {π π'}

lemma domain_subset_preimage_domain : π.domain ⊆ π ⁻¹' π.domain := π.maps_to
lemma symm_image_domain : π.symm '' π.domain = π.domain := π.symm.image_domain

/-- Two local equivs that have the same `domain`, same `to_fun` and same `inv_fun`, coincide. -/
@[ext]
protected lemma ext (h : ∀ x, π x = π' x)
  (hsymm : ∀ x, π.symm x = π'.symm x) (hs : π.domain = π'.domain) : π = π' :=
begin
  have A : (π : α → α) = π', by { ext x, exact h x },
  have B : (π.symm : α → α) = π'.symm, by { ext x, exact hsymm x },
  have I : π '' π.domain = π.domain := π.image_domain,
  have I' : π' '' π'.domain = π'.domain := π'.image_domain,
  rw [A, hs, I'] at I,
  cases π; cases π',
  simp only [*, coe_symm_mk, coe_mk, eq_self_iff_true, and_self] at *
end

/-- The identity local equivalence. -/
protected def refl (α : Type*) : local_perm α := equiv.perm.to_local_perm $ equiv.refl _

@[simp] lemma refl_domain : (local_perm.refl α).domain = univ := rfl
@[simp, norm_cast] lemma coe_refl : ⇑(local_perm.refl α) = id := rfl
@[simp] lemma symm_refl : (local_perm.refl α).symm = local_perm.refl α := rfl

instance : inhabited (local_perm α) := ⟨local_perm.refl _⟩

variables (π π')

-- TODO: Clean up these proofs
/-- Composing two local equivs if the domain of the first coincides with the domain of the
second. -/
@[simps]
protected def trans (π' : local_perm α) (h : π.domain = π'.domain) : local_perm α :=
{ to_fun := π' ∘ π,
  inv_fun := π.symm ∘ π'.symm,
  domain := π.domain,
  to_fun_domain' := λ x hx, begin
    rw h,
    refine map_domain _ _,
    have := map_domain π hx,
    rwa h at this,
  end,
  inv_fun_domain' := λ y hy, map_domain _ begin
    rw h at hy,
    have := map_domain π'.symm hy,
    rwa [symm_domain, ← h] at this,
  end,
  left_inv' := λ x hx, by simp [hx, h.symm],
  right_inv' := λ y hy, begin
    simp,
    rw h at hy,
    rw [right_inv π, right_inv π' hy],
    have := map_domain π'.symm hy,
    rwa [symm_domain, ← h] at this,
  end }

/-- The identity local equiv on a set `s` -/
def of_set (s : set α) : local_perm α :=
{ to_fun := id,
  inv_fun := id,
  domain := s,
  to_fun_domain' := λ x hx, hx,
  inv_fun_domain' := λ x hx, hx,
  left_inv' := λ x hx, rfl,
  right_inv' := λ x hx, rfl }

@[simp] lemma of_set_domain (s : set α) : (of_set s).domain = s := rfl
@[simp, norm_cast] lemma coe_of_set (s : set α) : (of_set s : α → α) = id := rfl
@[simp] lemma of_set_symm (s : set α) : (of_set s).symm = of_set s := rfl
@[simp] lemma of_set_trans_of_set (s : set α) : (of_set s).trans (of_set s) rfl = of_set s := rfl
@[simp] lemma of_set_univ : of_set univ = local_perm.refl α := rfl

/-- Reinterpret a local permutation as a local equivalence. -/
def to_local_equiv : local_equiv α α :=
{ to_fun := π,
  inv_fun := π.symm,
  source := π.domain,
  target := π.domain,
  map_source' := π.maps_to,
  map_target' := π.symm.maps_to,
  left_inv' := π.left_inv_on,
  right_inv' := π.right_inv_on }

@[simp] lemma coe_to_local_equiv : ⇑π.to_local_equiv = π := rfl
@[simp] lemma coe_to_local_equiv_symm : ⇑π.to_local_equiv.symm = π.symm := rfl
@[simp] lemma to_local_equiv_source : π.to_local_equiv.source = π.domain := rfl
@[simp] lemma to_local_equiv_target : π.to_local_equiv.target = π.domain := rfl

@[simp] lemma to_local_equiv_refl : (local_perm.refl α).to_local_equiv = local_equiv.refl _ := rfl
@[simp] lemma to_local_equiv_symm : π.symm.to_local_equiv = π.to_local_equiv.symm := rfl
@[simp] lemma to_local_equiv_trans (h) :
  (π.trans π' h).to_local_equiv = π.to_local_equiv.trans π'.to_local_equiv :=
begin
  ext,
  { simp },
  { simp },
  { simpa [←h] using λ hx, π.maps_to hx }
end

/-- `eq_on_domain π π'` means that `π` and `π'` have the same domain, and coincide there. Then `π`
and `π'` should really be considered the same local permutation. -/
def eq_on_domain : Prop := π.domain = π'.domain ∧ π.domain.eq_on π π'

/-- `eq_on_domain` is an equivalence relation -/
instance eq_on_domain_setoid : setoid (local_perm α) :=
{ r := eq_on_domain,
  iseqv := ⟨
    λ e, by simp [eq_on_domain],
    λ e e' h, by { simp [eq_on_domain, h.1.symm], exact λ x hx, (h.2 hx).symm },
    λ e e' e'' h h', ⟨by rwa [← h'.1, ← h.1], λ x hx, by { rw [← h'.2, h.2 hx], rwa ← h.1 }⟩⟩ }

variables {π π'}

lemma eq_on_domain_refl : π ≈ π := setoid.refl _

/-- Two equivalent local equivs have the same domain -/
lemma eq_on_domain.domain_eq (h : π ≈ π') : π.domain = π'.domain := h.1

/-- Two equivalent local equivs coincide on the domain -/
lemma eq_on_domain.eq_on (h : π ≈ π') : π.domain.eq_on π π' := h.2

/-- If two local equivs are equivalent, so are their inverses. -/
lemma eq_on_domain.symm' (h : π ≈ π') : π.symm ≈ π'.symm :=
begin
  refine ⟨h.domain_eq, eq_on_of_left_inv_on_of_right_inv_on π.left_inv_on _ _⟩;
    simp only [symm_domain, h.domain_eq, h.domain_eq, π'.symm.maps_to],
  exact π'.right_inv_on.congr_right π'.symm.maps_to (h.domain_eq ▸ h.eq_on.symm),
  exact π'.symm.maps_to,
end

/-- Two equivalent local equivs have coinciding inverses on the domain -/
lemma eq_on_domain.symm_eq_on (h : π ≈ π') : eq_on π.symm π'.symm π.domain := h.symm'.eq_on

/-- Preimages are respected by equivalence -/
lemma eq_on_domain.domain_inter_preimage_eq (hπ : π ≈ π') (s : set α) :
  π.domain ∩ π ⁻¹' s = π'.domain ∩ π' ⁻¹' s :=
by rw [hπ.eq_on.inter_preimage_eq, hπ.domain_eq]

/-- Two equivalent local equivs are equal when the domain and domain are univ -/
protected lemma eq_on_domain.eq (h : π ≈ π') (hπ : π.domain = univ) : π = π' :=
by apply local_perm.ext (λ x, h.2 _) (λ x, h.symm'.2 _) h.1; simp [hπ]

/-- We define a preorder on local permutations by saying `π ≤ π'` if the domain of `π` is contained
in the domain of `π'`, and the permutations agree on the domain of `π`. -/
instance : preorder (local_perm α) :=
{  le := λ π π', π.domain ⊆ π'.domain ∧ π.domain.eq_on π π',
  le_refl := λ a, ⟨subset_rfl, eq_on_refl _ _⟩,
  le_trans := λ a b c hab hbc, ⟨hab.1.trans hbc.1, hab.2.trans $ hbc.2.mono hab.1⟩ }

lemma domain_mono (h : π ≤ π') : π.domain ⊆ π'.domain := h.1
lemma eq_on_domain_of_le (h : π ≤ π') : π.domain.eq_on π π' := h.2
lemma le_of_eq_on_domain (h : π ≈ π') : π ≤ π' := ⟨subset_of_eq h.1, h.2⟩
lemma apply_eq_of_le (h : π ≤ π') {x : α} (hx : x ∈ π.domain) : π' x = π x :=
(eq_on_domain_of_le h hx).symm

section piecewise
variables (π π') [Π (j : α), decidable (j ∈ π.domain)] {h : disjoint π.domain π'.domain}

/-- Construct a local permutation from two local permutations with disjoint domains. -/
def piecewise (h : disjoint π.domain π'.domain) : local_perm α :=
{ to_fun := π.domain.piecewise π π',
  inv_fun := π.domain.piecewise π.symm π'.symm,
  domain := π.domain ∪ π'.domain,
  to_fun_domain' := begin
    rintro x (hx | hx),
    { rw piecewise_eq_on π.domain π π' hx,
      exact or.inl (π.map_domain hx) },
    { rw piecewise_eq_on_compl π.domain π π' (disjoint_right.mp h hx),
      exact or.inr (π'.map_domain hx) },
  end,
  inv_fun_domain' := begin
    rintro x (hx | hx),
    { rw piecewise_eq_on π.domain π.symm π'.symm hx,
      exact or.inl (π.symm.map_domain hx) },
    { rw piecewise_eq_on_compl π.domain π.symm π'.symm (disjoint_right.mp h hx),
      exact or.inr (π'.symm.map_domain hx) },
  end,
  left_inv' := begin
    rintro x (hx | hx),
    { rw [piecewise_eq_on π.domain π π' hx,
        piecewise_eq_on π.domain π.symm π'.symm (π.map_domain hx),
        π.left_inv hx] },
    { rw [piecewise_eq_on_compl π.domain π π' (disjoint_right.mp h hx),
        piecewise_eq_on_compl π.domain π.symm π'.symm (disjoint_right.mp h (π'.map_domain hx)),
        π'.left_inv hx] },
  end,
  right_inv' := begin
    rintro x (hx | hx),
    { rw [piecewise_eq_on π.domain π.symm π'.symm hx,
        piecewise_eq_on π.domain π π' (π.symm.map_domain hx),
        π.right_inv hx] },
    { rw [piecewise_eq_on_compl π.domain π.symm π'.symm (disjoint_right.mp h hx),
        piecewise_eq_on_compl π.domain π π' (disjoint_right.mp h (π'.symm.map_domain hx)),
        π'.right_inv hx] },
  end }

variables {π π' h}

@[simp] lemma piecewise_domain : (piecewise π π' h).domain = π.domain ∪ π'.domain := rfl
lemma mem_piecewise_domain_left {x : α} (hx : x ∈ π.domain) : x ∈ (piecewise π π' h).domain :=
mem_union_left _ hx
lemma mem_piecewise_domain_right {x : α} (hx : x ∈ π'.domain) : x ∈ (piecewise π π' h).domain :=
mem_union_right _ hx

lemma piecewise_apply_eq_left {x : α} (hx : x ∈ π.domain) : piecewise π π' h x = π x :=
piecewise_eq_on _ _ _ hx

lemma piecewise_apply_eq_right {x : α} (hx : x ∈ π'.domain) : piecewise π π' h x = π' x :=
piecewise_eq_on_compl _ _ _ (disjoint_right.mp h hx)

lemma le_piecewise_left : π ≤ piecewise π π' h :=
⟨subset_union_left _ _, λ x hx, (piecewise_apply_eq_left hx).symm⟩

lemma le_piecewise_right : π' ≤ piecewise π π' h :=
⟨subset_union_right _ _, λ x hx, (piecewise_apply_eq_right hx).symm⟩

end piecewise

end local_perm

namespace set

-- All arguments are explicit to avoid missing information in the pretty printer output
/-- A bijection between two sets `s : set α` and `t : set α` provides a local permutation on `α`. -/
@[simps {fully_applied := ff}]
noncomputable def bij_on.to_local_perm [nonempty α] (f : α → α) (s : set α) (hf : bij_on f s s) :
  local_perm α :=
{ to_fun := f,
  inv_fun := inv_fun_on f s,
  domain := s,
  to_fun_domain' := hf.maps_to,
  inv_fun_domain' := hf.surj_on.maps_to_inv_fun_on,
  left_inv' := hf.inv_on_inv_fun_on.1,
  right_inv' := hf.inv_on_inv_fun_on.2 }

end set

/-!
# `equiv.to_local_perm`

An `equiv` can be be interpreted give rise to local_perm. We set up simp lemmas to reduce most
properties of the local equiv to that of the equiv.
-/

open equiv

namespace equiv.perm
variables (π π' : perm α)

@[simp] lemma to_local_perm_one : to_local_perm (equiv.refl α) = local_perm.refl α := rfl
@[simp] lemma to_local_perm_inv : π⁻¹.to_local_perm = π.to_local_perm.symm := rfl
@[simp] lemma to_local_perm_mul :
  (π * π').to_local_perm = π'.to_local_perm.trans π.to_local_perm rfl :=
local_perm.ext (λ x, rfl) (λ x, rfl) rfl

@[simp] lemma to_local_equiv_to_local_perm : π.to_local_perm.to_local_equiv = π.to_local_equiv :=
rfl

end equiv.perm
