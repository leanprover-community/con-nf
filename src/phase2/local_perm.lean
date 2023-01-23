import data.set.function
import logic.equiv.defs

open function set

variables {α : Type*}

/-- A local permutation of a subset `domain` of `α`. The (global) maps `to_fun : α → α` and
`inv_fun : α → α` map `domain` to itself, and are inverse to each other there. The values of
`to_fun` and `inv_fun` outside of `domain` are irrelevant. -/
structure local_perm (α : Type*) :=
(to_fun : α → α)
(inv_fun : α → α)
(domain : set α)
(to_fun_domain' : ∀ ⦃x⦄, x ∈ domain → to_fun x ∈ domain)
(inv_fun_domain' : ∀ ⦃x⦄, x ∈ domain → inv_fun x ∈ domain)
(left_inv' : ∀ ⦃x⦄, x ∈ domain → inv_fun (to_fun x) = x)
(right_inv' : ∀ ⦃x⦄, x ∈ domain → to_fun (inv_fun x) = x)

namespace local_perm

variables (π ρ : local_perm α)

instance [inhabited α] : inhabited (local_perm α) :=
⟨⟨const α default, const α default, ∅, maps_to_empty _ _, maps_to_empty _ _,
  eq_on_empty _ _, eq_on_empty _ _⟩⟩

/-- The inverse of a local permutation. -/
protected def symm : local_perm α := {
  to_fun := π.inv_fun,
  inv_fun := π.to_fun,
  domain := π.domain,
  to_fun_domain' := π.inv_fun_domain',
  inv_fun_domain' := π.to_fun_domain',
  left_inv' := π.right_inv',
  right_inv' := π.left_inv',
}

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

@[simp] lemma map_domain {x : α} (h : x ∈ π.domain) : π x ∈ π.domain :=
π.to_fun_domain' h

@[simp] lemma left_inv {x : α} (h : x ∈ π.domain) : π.symm (π x) = x :=
π.left_inv' h

@[simp] lemma right_inv {x : α} (h : x ∈ π.domain) : π (π.symm x) = x :=
π.right_inv' h

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

/-- Associating a local_perm to an equiv-/
@[simps] def _root_.equiv.to_local_perm (π : α ≃ α) : local_perm α :=
{ to_fun := π,
  inv_fun := π.symm,
  domain := univ,
  to_fun_domain' := λ x hx, mem_univ _,
  inv_fun_domain' := λ y hy, mem_univ _,
  left_inv' := λ x hx, π.left_inv x,
  right_inv' := λ x hx, π.right_inv x }

instance inhabited_of_empty [is_empty α] : inhabited (local_perm α) :=
⟨((equiv.equiv_empty α).trans (equiv.equiv_empty α).symm).to_local_perm⟩

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
protected def to_perm : equiv.perm (π.domain) :=
{ to_fun := λ x, ⟨π x, π.map_domain x.mem⟩,
  inv_fun := λ y, ⟨π.symm y, π.symm.map_domain y.mem⟩,
  left_inv := λ ⟨x, hx⟩, subtype.eq $ π.left_inv hx,
  right_inv := λ ⟨y, hy⟩, subtype.eq $ π.right_inv hy }

@[simp] lemma symm_domain : π.symm.domain = π.domain := rfl
@[simp] lemma symm_symm : π.symm.symm = π := by { cases π, refl }

lemma image_domain_eq_domain : π '' π.domain = π.domain := π.bij_on.image_eq

lemma forall_mem_domain {p : α → Prop} : (∀ y ∈ π.domain, p y) ↔ ∀ x ∈ π.domain, p (π x) :=
by conv_lhs { rw [← image_domain_eq_domain, ball_image_iff] }

lemma exists_mem_domain {p : α → Prop} : (∃ y ∈ π.domain, p y) ↔ ∃ x ∈ π.domain, p (π x) :=
by conv_lhs { rw [← image_domain_eq_domain, bex_image_iff] }

lemma image_domain_inter_eq' (s : set α) :
  π '' (π.domain ∩ s) = π.domain ∩ π.symm ⁻¹' s :=
by rw [inter_comm, π.left_inv_on.image_inter', image_domain_eq_domain, inter_comm]

lemma image_domain_inter_eq (s : set α) :
  π '' (π.domain ∩ s) = π.domain ∩ π.symm ⁻¹' (π.domain ∩ s) :=
by rw [inter_comm, π.left_inv_on.image_inter, image_domain_eq_domain, inter_comm]

lemma image_eq_domain_inter_inv_preimage {s : set α} (h : s ⊆ π.domain) :
  π '' s = π.domain ∩ π.symm ⁻¹' s :=
by rw [← π.image_domain_inter_eq', inter_eq_self_of_subset_right h]

lemma symm_image_eq_domain_inter_preimage {s : set α} (h : s ⊆ π.domain) :
  π.symm '' s = π.domain ∩ π ⁻¹' s :=
π.symm.image_eq_domain_inter_inv_preimage h

lemma symm_image_domain_inter_eq (s : set α) :
  π.symm '' (π.domain ∩ s) = π.domain ∩ π ⁻¹' (π.domain ∩ s) :=
π.symm.image_domain_inter_eq _

lemma symm_image_domain_inter_eq' (s : set α) :
  π.symm '' (π.domain ∩ s) = π.domain ∩ π ⁻¹' s :=
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

lemma symm_image_image_of_subset_domain {s : set α} (h : s ⊆ π.domain) :
  π.symm '' (π '' s) = s :=
(π.left_inv_on.mono h).image_image

lemma image_symm_image_of_subset_domain {s : set α} (h : s ⊆ π.domain) :
  π '' (π.symm '' s) = s :=
π.symm.symm_image_image_of_subset_domain h

lemma domain_subset_preimage_domain : π.domain ⊆ π ⁻¹' π.domain :=
π.maps_to

lemma symm_image_domain_eq_domain : π.symm '' π.domain = π.domain :=
π.symm.image_domain_eq_domain

/-- Two local equivs that have the same `domain`, same `to_fun` and same `inv_fun`, coincide. -/
@[ext]
protected lemma ext {π π' : local_perm α} (h : ∀ x, π x = π' x)
  (hsymm : ∀ x, π.symm x = π'.symm x) (hs : π.domain = π'.domain) : π = π' :=
begin
  have A : (π : α → α) = π', by { ext x, exact h x },
  have B : (π.symm : α → α) = π'.symm, by { ext x, exact hsymm x },
  have I : π '' π.domain = π.domain := π.image_domain_eq_domain,
  have I' : π' '' π'.domain = π'.domain := π'.image_domain_eq_domain,
  rw [A, hs, I'] at I,
  cases π; cases π',
  simp only [*, coe_symm_mk, coe_mk, eq_self_iff_true, and_self] at *
end

/-- The identity local equiv -/
protected def refl (α : Type*) : local_perm α := (equiv.refl α).to_local_perm

@[simp] lemma refl_domain : (local_perm.refl α).domain = univ := rfl
@[simp] lemma refl_coe : (local_perm.refl α : α → α) = id := rfl
@[simp] lemma refl_symm : (local_perm.refl α).symm = local_perm.refl α := rfl

/-- The identity local equiv on a set `s` -/
def of_set (s : set α) : local_perm α :=
{ to_fun := id,
  inv_fun := id,
  domain := s,
  to_fun_domain' := λ x hx, hx,
  inv_fun_domain' := λ x hx, hx,
  left_inv' := λ x hx, rfl,
  right_inv' := λ x hx, rfl }

@[simp] lemma of_set_domain (s : set α) : (local_perm.of_set s).domain = s := rfl
@[simp] lemma of_set_coe (s : set α) : (local_perm.of_set s : α → α) = id := rfl
@[simp] lemma of_set_symm (s : set α) :
  (local_perm.of_set s).symm = local_perm.of_set s := rfl

-- TODO: Clean up these proofs
/-- Composing two local equivs if the domain of the first coincides with the domain of the
second. -/
protected def trans (π' : local_perm α) (h : π.domain = π'.domain) : local_perm α :=
{ to_fun := π' ∘ π,
  inv_fun := π.symm ∘ π'.symm,
  domain := π.domain,
  to_fun_domain' := λ x hx, begin rw h, refine map_domain _ _, have := map_domain π hx,
    rw h at this, exact this, end,
  inv_fun_domain' := λ y hy, begin refine map_domain _ _, rw h at hy, have := map_domain π'.symm hy,
    rw [symm_domain, ← h] at this, exact this, end,
  left_inv' := λ x hx, by simp [hx, h.symm],
  right_inv' := λ y hy, begin simp only [comp_app], rw h at hy,
    rw [right_inv π, right_inv π'],
    exact hy,
    have := map_domain π'.symm hy, rw [symm_domain, ← h] at this, exact this, end }

/-- `eq_on_domain π π'` means that `π` and `π'` have the same domain, and coincide there. Then `π`
and `π'` should really be considered the same local permutation. -/
def eq_on_domain (π π' : local_perm α) : Prop :=
π.domain = π'.domain ∧ (π.domain.eq_on π π')

/-- `eq_on_domain` is an equivalence relation -/
instance eq_on_domain_setoid : setoid (local_perm α) :=
{ r := eq_on_domain,
  iseqv := ⟨
    λ e, by simp [eq_on_domain],
    λ e e' h, by { simp [eq_on_domain, h.1.symm], exact λx hx, (h.2 hx).symm },
    λ e e' e'' h h', ⟨by rwa [← h'.1, ← h.1], λx hx, by { rw [← h'.2, h.2 hx], rwa ← h.1 }⟩⟩ }

lemma eq_on_domain_refl : π ≈ π := setoid.refl _

/-- Two equivalent local equivs have the same domain -/
lemma eq_on_domain.domain_eq {π π' : local_perm α} (h : π ≈ π') : π.domain = π'.domain :=
h.1

/-- Two equivalent local equivs coincide on the domain -/
lemma eq_on_domain.eq_on {π π' : local_perm α} (h : π ≈ π') : π.domain.eq_on π π' :=
h.2

/-- If two local equivs are equivalent, so are their inverses. -/
lemma eq_on_domain.symm' {π π' : local_perm α} (h : π ≈ π') : π.symm ≈ π'.symm :=
begin
  refine ⟨h.domain_eq, eq_on_of_left_inv_on_of_right_inv_on π.left_inv_on _ _⟩;
    simp only [symm_domain, h.domain_eq, h.domain_eq, π'.symm.maps_to],
  exact π'.right_inv_on.congr_right π'.symm.maps_to (h.domain_eq ▸ h.eq_on.symm),
  exact π'.symm.maps_to,
end

/-- Two equivalent local equivs have coinciding inverses on the domain -/
lemma eq_on_domain.symm_eq_on {π π' : local_perm α} (h : π ≈ π') :
  eq_on π.symm π'.symm π.domain :=
h.symm'.eq_on

/-- Preimages are respected by equivalence -/
lemma eq_on_domain.domain_inter_preimage_eq {π π' : local_perm α} (hπ : π ≈ π') (s : set α) :
  π.domain ∩ π ⁻¹' s = π'.domain ∩ π' ⁻¹' s :=
by rw [hπ.eq_on.inter_preimage_eq, hπ.domain_eq]

/-- Two equivalent local equivs are equal when the domain and domain are univ -/
lemma eq_of_eq_on_domain_univ (π π' : local_perm α) (h : π ≈ π')
  (s : π.domain = univ) (t : π.domain = univ) : π = π' :=
begin
  apply local_perm.ext (λx, _) (λx, _) h.1,
  { apply h.2,
    rw s,
    exact mem_univ _ },
  { apply h.symm'.2,
    rw [symm_domain, t],
    exact mem_univ _ }
end

/-- We define a preorder on local permutations by saying `π ≤ π'` if the domain of `π` is contained
in the domain of `π'`, and the permutations agree on the domain of `π`. -/
instance : preorder (local_perm α) := {
  le := λ π π', π.domain ⊆ π'.domain ∧ π.domain.eq_on π π',
  le_refl := λ a, ⟨subset_rfl, eq_on_refl _ _⟩,
  le_trans := λ a b c hab hbc, ⟨hab.1.trans hbc.1, hab.2.trans (hbc.2.mono hab.1)⟩,
}

lemma domain_subset_domain_of_le {π π' : local_perm α} (h : π ≤ π') : π.domain ⊆ π'.domain := h.1
lemma eq_on_domain_of_le {π π' : local_perm α} (h : π ≤ π') : π.domain.eq_on π π' := h.2
lemma le_of_eq_on_source {π π' : local_perm α} (h : π ≈ π') : π ≤ π' := ⟨subset_of_eq h.1, h.2⟩
lemma apply_eq_of_le {π π' : local_perm α} (h : π ≤ π') {x : α} (hx : x ∈ π.domain) : π' x = π x :=
(eq_on_domain_of_le h hx).symm

end local_perm

namespace set

-- All arguments are explicit to avoid missing information in the pretty printer output
/-- A bijection between two sets `s : set α` and `t : set α` provides a local equivalence
between `α` and `α`. -/
@[simps {fully_applied := ff}] noncomputable def bij_on.to_local_perm [nonempty α] (f : α → α)
  (s : set α) (hf : bij_on f s s) : local_perm α :=
{ to_fun := f,
  inv_fun := inv_fun_on f s,
  domain := s,
  to_fun_domain' := hf.maps_to,
  inv_fun_domain' := hf.surj_on.maps_to_inv_fun_on,
  left_inv' := hf.inv_on_inv_fun_on.1,
  right_inv' := hf.inv_on_inv_fun_on.2 }

end set

namespace equiv

/- equivs give rise to local_perm. We set up simp lemmas to reduce most properties of the local
equiv to that of the equiv. -/
variables (π : α ≃ α) (π' : α ≃ α)

@[simp] lemma refl_to_local_perm :
  (equiv.refl α).to_local_perm = local_perm.refl α := rfl
@[simp] lemma symm_to_local_perm : π.symm.to_local_perm = π.to_local_perm.symm := rfl
@[simp] lemma trans_to_local_perm :
  (π.trans π').to_local_perm = π.to_local_perm.trans π'.to_local_perm rfl :=
local_perm.ext (λ x, rfl) (λ x, rfl) rfl

end equiv
