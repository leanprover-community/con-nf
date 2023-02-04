import mathlib.logic.equiv.local_perm
import phase2.constrains
import phase2.sublitter

open set sum
open_locale cardinal pointwise

universe u

namespace con_nf
variable [params.{u}]

-- TODO: Factor this out into a file.
section flexible
variables (α : Λ) [position_data.{}] [phase_2_assumptions α] {β : type_index}

/-- A litter is *inflexible* if it is the image of some f-map. -/
@[mk_iff] inductive inflexible : litter → extended_index β → Prop
| mk_coe ⦃γ : Iic α⦄ ⦃δ : Iio α⦄ ⦃ε : Iio α⦄ (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
    (A : quiver.path (β : type_index) γ) (t : tangle δ) :
    inflexible
      (f_map (with_bot.coe_ne_coe.mpr $ coe_ne' hδε) t)
      ((A.cons (coe_lt hε)).cons (with_bot.bot_lt_coe _))
| mk_bot ⦃γ : Iic α⦄ ⦃ε : Iio α⦄ (hε : (ε : Λ) < γ)
    (A : quiver.path (β : type_index) γ) (a : atom) :
    inflexible
      (f_map (show (⊥ : type_index) ≠ (ε : Λ), from with_bot.bot_ne_coe) a)
      ((A.cons (coe_lt hε)).cons (with_bot.bot_lt_coe _))

/-- A litter is *flexible* if it is not the image of any f-map. -/
def flexible (L : litter) (A : extended_index β) : Prop := ¬inflexible α L A

variable {α}

lemma inflexible.comp {γ : type_index} {L : litter} {A : extended_index γ}
  (h : inflexible α L A) (B : quiver.path β γ) : inflexible α L (B.comp A) :=
begin
  induction h,
  refine inflexible.mk_coe _ _ _ _ _,
  assumption,
  exact inflexible.mk_bot _ _ _,
end

@[simp] lemma not_flexible_iff {L : litter} {A : extended_index β} :
  ¬flexible α L A ↔ inflexible α L A := not_not

lemma flexible_of_comp_flexible {γ : type_index} {L : litter} {A : extended_index γ}
  {B : quiver.path β γ} (h : flexible α L (B.comp A)) : flexible α L A :=
λ h', h (h'.comp B)

end flexible

@[ext] structure near_litter_approx :=
(atom_perm : local_perm atom)
(litter_perm : local_perm litter)
(domain_small : ∀ L, small (litter_set L ∩ atom_perm.domain))

namespace near_litter_approx

instance : has_smul near_litter_approx atom := ⟨λ π, π.atom_perm⟩
instance : has_smul near_litter_approx litter := ⟨λ π, π.litter_perm⟩

variables (π : near_litter_approx)

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

def symm : near_litter_approx := {
  atom_perm := π.atom_perm.symm,
  litter_perm := π.litter_perm.symm,
  domain_small := π.domain_small,
}

@[simp] lemma symm_atom_perm : π.symm.atom_perm = π.atom_perm.symm := rfl
@[simp] lemma symm_litter_perm : π.symm.litter_perm = π.litter_perm.symm := rfl

@[simp] lemma left_inv_atom {a} : a ∈ π.atom_perm.domain → π.symm • π • a = a :=
π.atom_perm.left_inv

@[simp] lemma left_inv_litter {L} : L ∈ π.litter_perm.domain → π.symm • π • L = L :=
π.litter_perm.left_inv

@[simp] lemma right_inv_atom {a} : a ∈ π.atom_perm.domain → π • π.symm • a = a :=
π.atom_perm.right_inv

@[simp] lemma right_inv_litter {L} : L ∈ π.litter_perm.domain → π • π.symm • L = L :=
π.litter_perm.right_inv

lemma eq_symm_apply_atom {a₁ a₂} : a₁ ∈ π.atom_perm.domain → a₂ ∈ π.atom_perm.domain →
  (a₁ = π.symm • a₂ ↔ π • a₁ = a₂) := π.atom_perm.eq_symm_apply

lemma eq_symm_apply_litter {L₁ L₂} : L₁ ∈ π.litter_perm.domain → L₂ ∈ π.litter_perm.domain →
  (L₁ = π.symm • L₂ ↔ π • L₁ = L₂) := π.litter_perm.eq_symm_apply

section generate

variables (π)

/-- Gives the largest sublitter of `π` on which `π.atom_perm` is not defined. -/
def largest_sublitter (L : litter) : sublitter := {
  litter := L,
  carrier := litter_set L \ π.atom_perm.domain,
  subset := diff_subset _ _,
  diff_small := by simpa only [sdiff_sdiff_right_self, inf_eq_inter] using π.domain_small L,
}

@[simp] lemma largest_sublitter_litter (L : litter) : (π.largest_sublitter L).litter = L := rfl
@[simp] lemma coe_largest_sublitter (L : litter) :
  (π.largest_sublitter L : set atom) = litter_set L \ π.atom_perm.domain := rfl

lemma mem_largest_sublitter_of_not_mem_domain (a : atom) (h : a ∉ π.atom_perm.domain) :
  a ∈ π.largest_sublitter a.1 := ⟨rfl, h⟩

lemma not_mem_domain_of_mem_largest_sublitter {a : atom} {L : litter}
  (h : a ∈ π.largest_sublitter L) : a ∉ π.atom_perm.domain := h.2

/-- Computes the action of `π` on this sublitter, assuming it is in `sublitter_domain`. -/
def generate_sublitter (S : sublitter) : sublitter := π.largest_sublitter (π • S.litter)

def sublitter_domain : set sublitter :=
{S | S.litter ∈ π.litter_perm.domain ∧ (S : set atom) = litter_set S.litter \ π.atom_perm.domain}

lemma mem_sublitter_domain (S : sublitter) (h : S ∈ π.sublitter_domain) :
  (S : set atom) = litter_set S.litter \ π.atom_perm.domain :=
h.2

lemma generate_sublitter_mem_domain ⦃S : sublitter⦄ (h : S ∈ sublitter_domain π) :
  generate_sublitter π S ∈ sublitter_domain π :=
⟨π.litter_perm.map_domain h.1, rfl⟩

lemma generate_sublitter_left_inv ⦃S : sublitter⦄ (h : S ∈ sublitter_domain π) :
  generate_sublitter π.symm (generate_sublitter π S) = S :=
begin
  ext : 1,
  simp only [h.2, largest_sublitter, generate_sublitter, symm_atom_perm, local_perm.symm_domain,
    sublitter.coe_mk, π.left_inv_litter h.1],
end

/-- Generates the unique near-litter approximation given by an atom local permutation and a
near-litter local permutation. This uniqueness is only up to evaluating everything on the domain
of the permutation. -/
def generate_sublitter_perm : local_perm sublitter := {
  to_fun := generate_sublitter π,
  inv_fun := generate_sublitter π.symm,
  domain := sublitter_domain π,
  to_fun_domain' := generate_sublitter_mem_domain π,
  inv_fun_domain' := generate_sublitter_mem_domain π.symm,
  left_inv' := generate_sublitter_left_inv π,
  right_inv' := generate_sublitter_left_inv π.symm,
}

@[simp] lemma generate_symm :
  (generate_sublitter_perm π).symm = generate_sublitter_perm π.symm := rfl

@[simp] lemma generate_sublitter_perm_domain :
  (generate_sublitter_perm π).domain = sublitter_domain π := rfl

@[simp] lemma generate_sublitter_apply (S : sublitter) :
  generate_sublitter_perm π S = generate_sublitter π S := rfl

instance : has_smul near_litter_approx sublitter := ⟨λ π, π.generate_sublitter_perm⟩

@[simp] lemma smul_sublitter (S : sublitter) :
  (π • S).litter = π • S.litter := rfl

lemma smul_eq_smul_sublitter {S₁ S₂ : sublitter}
  (h₁ : S₁ ∈ sublitter_domain π) (h₂ : S₂ ∈ sublitter_domain π) :
  π • S₁ = π • S₂ ↔ S₁ = S₂ :=
begin
  unfold has_smul.smul,
  rw [← π.generate_sublitter_perm.eq_symm_apply h₁ (π.generate_sublitter_perm.map_domain h₂),
    local_perm.left_inv _ _],
  exact h₂,
end

@[simp] lemma left_inv_sublitter {S} : S ∈ π.sublitter_domain → π.symm • π • S = S :=
π.generate_sublitter_perm.left_inv

@[simp] lemma right_inv_sublitter {S} : S ∈ π.sublitter_domain → π • π.symm • S = S :=
π.generate_sublitter_perm.right_inv

lemma eq_symm_apply_sublitter {S₁ S₂} : S₁ ∈ π.sublitter_domain →
  S₂ ∈ π.sublitter_domain → (S₁ = π.symm • S₂ ↔ π • S₁ = S₂) :=
π.generate_sublitter_perm.eq_symm_apply

end generate

def is_exception (π : near_litter_perm) (a : atom) : Prop :=
π • a ∉ litter_set (π • a.1) ∨ π⁻¹ • a ∉ litter_set (π⁻¹ • a.1)

@[mk_iff] structure approximates (π₀ : near_litter_approx) (π : near_litter_perm) : Prop :=
(map_atom : ∀ a, a ∈ π₀.atom_perm.domain → π₀ • a = π • a)
(map_litter : ∀ L, L ∈ π₀.litter_perm.domain → π₀ • L = π • L)

@[mk_iff] structure exactly_approximates (π₀ : near_litter_approx) (π : near_litter_perm)
  extends approximates π₀ π : Prop :=
(exception_mem : ∀ a, is_exception π a → a ∈ π₀.atom_perm.domain)

instance : preorder near_litter_approx := {
  le := λ π π', π.atom_perm ≤ π'.atom_perm ∧ π.litter_perm ≤ π'.litter_perm,
  le_refl := λ π, ⟨le_rfl, le_rfl⟩,
  le_trans := λ _ _ _ h₁ h₂, ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩,
}

def free (α : Λ) [position_data.{}] [phase_2_assumptions α] {β : type_index}
  (π : near_litter_approx) (A : extended_index β) : Prop :=
∀ L ∈ π.litter_perm.domain, flexible α L A

end near_litter_approx

/-- A `β`-structural approximation is a product that assigns a near-litter approximation to each
`β`-extended index. -/
def struct_approx (β : type_index) := extended_index β → near_litter_approx

namespace struct_approx

-- TODO: Could refactor struct_perm as a map `extended_index β → near_litter_perm`.

def approximates {β : type_index} (π₀ : struct_approx β) (π : struct_perm β) : Prop :=
∀ A, (π₀ A).approximates (struct_perm.of_bot $ struct_perm.derivative A π)

def exactly_approximates {β : type_index} (π₀ : struct_approx β) (π : struct_perm β) : Prop :=
∀ A, (π₀ A).exactly_approximates (struct_perm.of_bot $ struct_perm.derivative A π)

variables {α : Λ} [position_data.{}] [phase_2_assumptions α]

def free {β : Iic α} (π₀ : struct_approx β) : Prop := ∀ A, (π₀ A).free α A

/-- The inductive hypothesis used to construct the induced action of an approximation in the
freedom of action theorem. -/
structure hypothesis {β : Iic α} (c : support_condition β) :=
(atom_image : Π a A, (relation.trans_gen (constrains α β)) ⟨inl a, A⟩ c → atom)
(near_litter_image : Π N A, (relation.trans_gen (constrains α β)) ⟨inr N, A⟩ c → near_litter)

namespace hypothesis
variable {β : Iic α}

/-- Two hypotheses are compatible if they agree everywhere that they are both defined. -/
@[mk_iff] structure compatible {c d : support_condition β}
  (Hc : hypothesis c) (Hd : hypothesis d) : Prop :=
(atom_compatible : ∀ a A hc hd, Hc.atom_image a A hc = Hd.atom_image a A hd)
(near_litter_compatible : ∀ N A hc hd, Hc.near_litter_image N A hc = Hd.near_litter_image N A hd)

def fix_map :
  (psum (Σ' (_ : atom), extended_index β) (Σ' (_ : near_litter), extended_index β)) →
  support_condition β
| (psum.inl ⟨a, A⟩) := ⟨inl a, A⟩
| (psum.inr ⟨N, A⟩) := ⟨inr N, A⟩

def fix_wf : has_well_founded
  (psum (Σ' (_ : atom), extended_index β) (Σ' (_ : near_litter), extended_index β)) :=
⟨inv_image (relation.trans_gen (constrains α β)) fix_map,
  inv_image.wf _ (constrains_wf α β).trans_gen⟩

/-- Construct the fixed-point functions `fix_atom` and `fix_near_litter`.
This is used to compute the induced action of an approximation on all atoms and near-litters. -/
noncomputable! mutual def fix_atom, fix_near_litter
  (Fa : Π a (A : extended_index β), hypothesis ⟨inl a, A⟩ → atom)
  (FN : Π N (A : extended_index β), hypothesis ⟨inr N, A⟩ → near_litter)
with fix_atom : atom → extended_index β → atom
| a A := Fa a A ⟨λ b B hb, fix_atom b B, λ N B hb, fix_near_litter N B⟩
with fix_near_litter : near_litter → extended_index β → near_litter
| N A := FN N A ⟨λ b B hb, fix_atom b B, λ N B hb, fix_near_litter N B⟩
using_well_founded { rel_tac := λ _ _, `[exact fix_wf], dec_tac := `[exact hb] }

lemma fix_atom_eq (Fa FN) (a : atom) (A : extended_index β) :
  fix_atom Fa FN a A =
  Fa a A ⟨λ b B hb, fix_atom Fa FN b B, λ N B hb, fix_near_litter Fa FN N B⟩ :=
by rw fix_atom

lemma fix_near_litter_eq (Fa FN) (N : near_litter) (A : extended_index β) :
  fix_near_litter Fa FN N A =
  FN N A ⟨λ b B hb, fix_atom Fa FN b B, λ N B hb, fix_near_litter Fa FN N B⟩ :=
by rw fix_near_litter

end hypothesis

end struct_approx

end con_nf
