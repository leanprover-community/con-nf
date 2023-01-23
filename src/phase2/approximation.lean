import phase2.constrains
import phase2.local_perm
import phase2.sublitter

open set
open_locale cardinal pointwise

universe u

namespace con_nf
variable [params.{u}]

@[ext] structure near_litter_approx :=
(atom_perm : local_perm atom)
(litter_perm : local_perm litter)
(sublitter_perm : local_perm sublitter)
(sublitter_domain : ∀ ⦃S : sublitter⦄, S ∈ sublitter_perm.domain → S.litter ∈ litter_perm.domain)
(map_sublitter' : ∀ ⦃S : sublitter⦄, S ∈ sublitter_perm.domain →
  (sublitter_perm S).litter = litter_perm S.litter)
(atoms_cover_large : ∀ ⦃L : litter⦄, #(atom_perm.domain ∩ litter_set L : set atom) = #κ →
  litter_set L ⊆ atom_perm.domain)
(atoms_cover_diff : ∀ ⦃S : sublitter⦄, S ∈ sublitter_perm.domain →
  ∀ a ∈ litter_set S.litter, (a ∈ atom_perm.domain ↔ a ∉ S))

namespace near_litter_approx

instance : has_smul near_litter_approx atom := ⟨λ π, π.atom_perm⟩
instance : has_smul near_litter_approx litter := ⟨λ π, π.litter_perm⟩
instance : has_smul near_litter_approx sublitter := ⟨λ π, π.sublitter_perm⟩

variables (π : near_litter_approx)

@[simp] lemma map_sublitter (S : sublitter) (h : S ∈ π.sublitter_perm.domain) :
  (π • S).litter = π • S.litter := π.map_sublitter' h

lemma smul_eq_smul_atom {a₁ a₂ : atom}
  (h₁ : a₁ ∈ π.atom_perm.domain) (h₂ : a₂ ∈ π.atom_perm.domain) :
  π • a₁ = π • a₂ ↔ a₁ = a₂ :=
begin
  unfold has_smul.smul,
  rw [← π.atom_perm.eq_symm_apply h₁ (π.atom_perm.map_domain h₂), local_perm.left_inv _ h₂],
end

lemma smul_eq_smul_litter {L₁ L₂ : litter}
  (h₁ : L₁ ∈ π.litter_perm.domain) (h₂ : L₂ ∈ π.litter_perm.domain) :
  π • L₁ = π • L₂ ↔ L₁ = L₂ :=
begin
  unfold has_smul.smul,
  rw [← π.litter_perm.eq_symm_apply h₁ (π.litter_perm.map_domain h₂), local_perm.left_inv _ h₂],
end

lemma smul_eq_smul_sublitter {S₁ S₂ : sublitter}
  (h₁ : S₁ ∈ π.sublitter_perm.domain) (h₂ : S₂ ∈ π.sublitter_perm.domain) :
  π • S₁ = π • S₂ ↔ S₁ = S₂ :=
begin
  unfold has_smul.smul,
  rw [← π.sublitter_perm.eq_symm_apply h₁ (π.sublitter_perm.map_domain h₂),
    local_perm.left_inv _ h₂],
end

def symm : near_litter_approx := {
  atom_perm := π.atom_perm.symm,
  litter_perm := π.litter_perm.symm,
  sublitter_perm := π.sublitter_perm.symm,
  sublitter_domain := π.sublitter_domain,
  map_sublitter' := λ S h, begin
    rw ← π.smul_eq_smul_litter
      (π.sublitter_domain (π.sublitter_perm.symm.map_domain h))
      (π.litter_perm.symm.map_domain (π.sublitter_domain h)),
    have := π.map_sublitter (π.sublitter_perm.symm S) (π.sublitter_perm.symm.map_domain h),
    unfold has_smul.smul at this ⊢,
    rw [local_perm.right_inv] at this,
    rw [← this, local_perm.right_inv _ (π.sublitter_domain h)],
    exact h,
  end,
  atoms_cover_large := π.atoms_cover_large,
  atoms_cover_diff := π.atoms_cover_diff,
}

@[simp] lemma left_inv_atom {a} : a ∈ π.atom_perm.domain → π.symm • π • a = a :=
π.atom_perm.left_inv

@[simp] lemma left_inv_litter {L} : L ∈ π.litter_perm.domain → π.symm • π • L = L :=
π.litter_perm.left_inv

@[simp] lemma left_inv_sublitter {S} : S ∈ π.sublitter_perm.domain → π.symm • π • S = S :=
π.sublitter_perm.left_inv

@[simp] lemma right_inv_atom {a} : a ∈ π.atom_perm.domain → π • π.symm • a = a :=
π.atom_perm.right_inv

@[simp] lemma right_inv_litter {L} : L ∈ π.litter_perm.domain → π • π.symm • L = L :=
π.litter_perm.right_inv

@[simp] lemma right_inv_sublitter {S} : S ∈ π.sublitter_perm.domain → π • π.symm • S = S :=
π.sublitter_perm.right_inv

lemma eq_symm_apply_atom {a₁ a₂} : a₁ ∈ π.atom_perm.domain → a₂ ∈ π.atom_perm.domain →
  (a₁ = π.symm • a₂ ↔ π • a₁ = a₂) := π.atom_perm.eq_symm_apply

lemma eq_symm_apply_litter {L₁ L₂} : L₁ ∈ π.litter_perm.domain → L₂ ∈ π.litter_perm.domain →
  (L₁ = π.symm • L₂ ↔ π • L₁ = L₂) := π.litter_perm.eq_symm_apply

lemma eq_symm_apply_sublitter {S₁ S₂} : S₁ ∈ π.sublitter_perm.domain →
  S₂ ∈ π.sublitter_perm.domain → (S₁ = π.symm • S₂ ↔ π • S₁ = S₂) := π.sublitter_perm.eq_symm_apply

def generate_sublitter (atom_perm : local_perm atom) (litter_perm : local_perm litter)
  (h : small atom_perm.domain) (S : sublitter) : sublitter := {
  litter := litter_perm S.litter,
  carrier := litter_set (litter_perm S.litter) ∩
    (atom_perm.domainᶜ ∪ atom_perm '' (S ∩ atom_perm.domain)),
  subset := inter_subset_left _ _,
  diff_small := begin
    rw [diff_self_inter, ← diff_diff],
    refine small.mono (diff_subset _ _) _,
    rw diff_compl,
    exact small.mono (inter_subset_right _ _) h,
  end,
}

def generate_sublitter_domain (atom_domain : set atom) (litter_domain : set litter) :
  set sublitter :=
{S | S.litter ∈ litter_domain ∧ ∀ a ∈ litter_set S.litter, (a ∈ atom_domain ↔ a ∉ S)}

lemma generate_sublitter_mem_domain (atom_perm : local_perm atom) (litter_perm : local_perm litter)
  (h : small atom_perm.domain) ⦃S : sublitter⦄
  (hS : S ∈ generate_sublitter_domain atom_perm.domain litter_perm.domain) :
  generate_sublitter atom_perm litter_perm h S ∈
    generate_sublitter_domain atom_perm.domain litter_perm.domain :=
begin
  obtain ⟨h₁, h₂⟩ := hS,
  refine ⟨litter_perm.map_domain h₁, λ a ha, _⟩,
  simp only [generate_sublitter, sublitter.mem_mk, mem_inter_iff, mem_litter_set,
    mem_union, mem_compl_iff, mem_image, set_like.mem_coe, not_and, not_or_distrib],
  refine ⟨_, λ h, of_not_not (h ha).1⟩,
  intros ha₁ ha₂,
  simp only [ha₁, not_true, not_false_iff, not_exists, not_and, true_and, and_imp],
  intros b hb₁ hb₂ hb₃,
  have := h₂ b (sublitter.mem_litter_set_of_mem hb₁),
  simp only [hb₁, not_true, iff_false] at this,
  exact this hb₂,
end

lemma generate_sublitter_left_inv (atom_perm : local_perm atom) (litter_perm : local_perm litter)
  (h : small atom_perm.domain) ⦃S : sublitter⦄
  (hS : S ∈ generate_sublitter_domain atom_perm.domain litter_perm.domain) :
  generate_sublitter atom_perm.symm litter_perm.symm h
    (generate_sublitter atom_perm litter_perm h S) = S :=
begin
  obtain ⟨hS₁, hS₂⟩ := hS,
  ext a : 2,
  simp only [generate_sublitter, local_perm.symm_domain, sublitter.coe_mk, mem_inter_iff,
    mem_litter_set, mem_union, mem_compl_iff, mem_image, set_like.mem_coe],
  split,
  { rintro ⟨ha, hdom | ⟨b, ⟨⟨hb₁, hb₂ | ⟨c, ⟨hc₁, hc₂⟩, rfl⟩⟩, hb₃⟩, rfl⟩⟩,
    { rw [hS₂, not_not] at hdom,
      exact hdom,
      rw local_perm.left_inv at ha,
      exact ha,
      exact hS₁, },
    { cases hb₂ hb₃, },
    { rw local_perm.left_inv at ⊢,
      exact hc₁,
      exact hc₂, }, },
  { intro ha₁,
    split,
    { rw local_perm.left_inv,
      exact sublitter.fst_eq_of_mem ha₁,
      exact hS₁, },
    refine not_or_of_imp (λ ha₂, _),
    rw hS₂ a (sublitter.mem_litter_set_of_mem ha₁) at ha₂,
    cases ha₂ ha₁, },
end

def generate_sublitter_perm (atom_perm : local_perm atom) (litter_perm : local_perm litter)
  (h : small atom_perm.domain) : local_perm sublitter := {
  to_fun := generate_sublitter atom_perm litter_perm h,
  inv_fun := generate_sublitter atom_perm.symm litter_perm.symm h,
  domain := generate_sublitter_domain atom_perm.domain litter_perm.domain,
  to_fun_domain' := generate_sublitter_mem_domain atom_perm litter_perm h,
  inv_fun_domain' := generate_sublitter_mem_domain atom_perm.symm litter_perm.symm h,
  left_inv' := generate_sublitter_left_inv atom_perm litter_perm h,
  right_inv' := generate_sublitter_left_inv atom_perm.symm litter_perm.symm h,
}

/-- Generates the unique near-litter approximation given by an atom local permutation and a
near-litter local permutation. This uniqueness is only up to evaluating everything on the domain
of the permutation.. -/
def generate (atom_perm : local_perm atom) (litter_perm : local_perm litter)
  (h : small atom_perm.domain) : near_litter_approx := {
  atom_perm := atom_perm,
  litter_perm := litter_perm,
  sublitter_perm := generate_sublitter_perm atom_perm litter_perm h,
  sublitter_domain := λ S hS, hS.1,
  map_sublitter' := λ S hS, rfl,
  atoms_cover_large := λ L h₂, false.elim $ ne_of_lt (small.mono (inter_subset_left _ _) h) h₂,
  atoms_cover_diff := λ S hS, hS.2,
}

@[simp] lemma generate_symm (atom_perm : local_perm atom) (litter_perm : local_perm litter)
  (h : small atom_perm.domain) :
  (generate atom_perm litter_perm h).symm = generate atom_perm.symm litter_perm.symm h := rfl

lemma sublitter_coe_eq_of_mem_domain (S : sublitter) (h : S ∈ π.sublitter_perm.domain) :
  (S : set atom) = litter_set S.litter \ π.atom_perm.domain :=
begin
  ext a,
  have := π.atoms_cover_diff h a,
  exact ⟨λ h, ⟨sublitter.fst_eq_of_mem h, (this (sublitter.fst_eq_of_mem h)).not_left.mpr h⟩,
    λ h, (this h.1).not_left.mp h.2⟩,
end

def is_exception (π : near_litter_perm) (a : atom) : Prop :=
π • a ∉ litter_set (π • a.1) ∨ π⁻¹ • a ∉ litter_set (π⁻¹ • a.1)

@[mk_iff] structure approximates (π₀ : near_litter_approx) (π : near_litter_perm) : Prop :=
(map_atom : ∀ a, a ∈ π₀.atom_perm.domain → π₀ • a = π • a)
(map_litter : ∀ L, L ∈ π₀.litter_perm.domain → π₀ • L = π • L)
(map_sublitter : ∀ S, S ∈ π₀.sublitter_perm.domain → (↑(π₀ • S) : set _) = π • (S : set atom))

@[mk_iff] structure exactly_approximates (π₀ : near_litter_approx) (π : near_litter_perm)
  extends approximates π₀ π : Prop :=
(exception_mem : ∀ a, is_exception π a → a ∈ π₀.atom_perm.domain)

instance : preorder near_litter_approx := {
  le := λ π π', π.atom_perm ≤ π'.atom_perm ∧
    π.litter_perm ≤ π'.litter_perm ∧ π.sublitter_perm ≤ π'.sublitter_perm,
  le_refl := λ π, ⟨le_rfl, le_rfl, le_rfl⟩,
  le_trans := λ _ _ _ h₁ h₂, ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩,
}

section free

variables (α : Λ) [core_tangle_cumul α] [positioned_tangle_cumul α]
  [position_data.{}] [almost_tangle_cumul α] {β : type_index}

/-- A litter is *inflexible* if it is the image of some f-map. -/
@[mk_iff] inductive _root_.con_nf.inflexible : litter → extended_index β → Prop
| mk ⦃γ : Iio α⦄ ⦃ε : Iio α⦄ (hε : ε < γ)
    (A : quiver.path (β : type_index) γ) (a : atom) :
    _root_.con_nf.inflexible (f_map (show (⊥ : type_index) ≠ (ε : Λ), from with_bot.bot_ne_coe) a)
      ((A.cons (coe_lt hε)).cons (with_bot.bot_lt_coe _))

/-- A litter is *flexible* if it is not the image of any f-map. -/
def flexible (L : litter) (A : extended_index β) : Prop := ¬inflexible α L A

@[mk_iff] structure free (π : near_litter_approx) (A : extended_index β) : Prop :=
(mk_lt : ∀ L, small (π.atom_perm.domain ∩ litter_set L))
(flex : ∀ L ∈ π.litter_perm.domain, flexible α L A)

end free

end near_litter_approx

/-- A `β`-structural approximation is a product that assigns a near-litter approximation to each
`β`-extended index. -/
def struct_approx (β : type_index) := extended_index β → near_litter_approx

namespace struct_approx
variable {β : type_index}

def approximates (π₀ : struct_approx β) (π : struct_perm β) : Prop :=
∀ A, (π₀ A).approximates (struct_perm.of_bot $ struct_perm.derivative A π)

def exactly_approximates (π₀ : struct_approx β) (π : struct_perm β) : Prop :=
∀ A, (π₀ A).exactly_approximates (struct_perm.of_bot $ struct_perm.derivative A π)

variables (α : Λ) [core_tangle_cumul α] [positioned_tangle_cumul α]
  [position_data.{}] [almost_tangle_cumul α]

def free {β : Iio α} (π₀ : struct_approx β) : Prop := ∀ A, (π₀ A).free α A

end struct_approx

end con_nf
