import code_equiv
import mathlib.group
import struct_perm

/-!
# Allowable permutations
-/

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

open function params set with_bot
open_locale pointwise

variables (α : Λ) [phase_1a.{u} α]

/-- Contains all the information needed for phase 1b of the recursion. -/
class phase_1b :=
(allowable : Π β < α, Type*)
[allowable_group : Π β hβ, group (allowable β hβ)]
(to_struct_perm : Π β hβ, allowable β hβ →* struct_perm α)
[allowable_action : Π β hβ, mul_action (allowable β hβ) (tangle α β $ coe_lt_coe.2 hβ)]

export phase_1b (allowable allowable_group to_struct_perm allowable_action)

attribute [instance] allowable_group allowable_action

variables [phase_1b.{u} α] {β γ δ : Λ} {hβ : β ≤ α}

/-- A semi-allowable permutation is a `-1`-allowable permutation of atoms (a near-litter
permutation) together with allowable permutations on all `γ < β`. This forms a group structure
automatically. -/
@[derive group] def semiallowable_perm (hβ : β ≤ α) :=
near_litter_perm × Π γ (h : γ < β), allowable γ (h.trans_le hβ)

instance near_litter_perm.mul_action_tangle (hβ : β < α) :
  mul_action near_litter_perm (tangle α β $ coe_lt_coe.2 hβ) :=
{ smul := λ f t, to_tangle _ _ $ f • sorry,
  one_smul := sorry,
  mul_smul := sorry }

namespace semiallowable_perm
variables {α} (π : semiallowable_perm α hβ) (X : code α β hβ)

def to_struct_perm : semiallowable_perm α hβ →* struct_perm β := sorry

instance mul_action_tangle {β : type_index} (hβ : β < α) :
  mul_action (semiallowable_perm α le_rfl) (tangle α β hβ) :=
{ smul := λ π, with_bot.rec_bot_coe
    (λ hβ t, π.fst.atom_perm t)
    (λ β hβ t, π.snd β (coe_lt_coe.mp hβ) • t) β hβ,
  one_smul := λ t, by { cases β, { refl }, { exact one_smul _ _ } },
  mul_smul := λ f g t, by { cases β, { refl }, { exact mul_smul _ _ _ } } }

instance mul_action_code (hβ : β ≤ α) : mul_action (semiallowable_perm α hβ) (code α β hβ) :=
{ smul := λ π X,
    ⟨X.extension, X.extension_lt,
      rec_bot_coe
      (λ none_lt, ((•) π.1 : set atom → set atom))
      (λ γ γ_lt, (•) (π.snd γ $ coe_lt_coe.mp γ_lt))
      X.extension X.extension_lt X.elts⟩,
  one_smul := λ ⟨β, hβ, elts⟩, code.ext _ _ rfl $ begin
    induction β using with_bot.rec_bot_coe,
    { simp only [one_smul, prod.fst_one, rec_bot_coe_bot] },
    { exact (one_smul _ _).heq }
  end,
  mul_smul := λ f g ⟨β, hβ, elts⟩, code.ext _ _ rfl $ begin
    induction β using with_bot.rec_bot_coe,
    { simp only [mul_smul, prod.fst_mul, rec_bot_coe_bot] },
    { exact (mul_smul _ _ _).heq }
  end }

lemma smul_code_def :
  π • X =
    ⟨X.extension, X.extension_lt,
    rec_bot_coe
      (λ none_lt elts, π.fst.atom_perm '' elts)
    (λ γ γ_lt elts, (•) (π.snd γ $ coe_lt_coe.mp γ_lt) '' elts)
      X.extension X.extension_lt X.elts⟩ := rfl

@[simp] lemma extension_smul : (π • X).extension = X.extension := rfl

instance has_smul_nonempty_code (hβ : β ≤ α) :
  has_smul (semiallowable_perm α hβ) (nonempty_code α β hβ) :=
⟨λ π X, ⟨π • X, let ⟨⟨γ, hγ, G⟩, hG⟩ := X in
  by induction γ using with_bot.rec_bot_coe; exact hG.image _⟩⟩

@[simp, norm_cast] lemma coe_smul (X : nonempty_code α β hβ) : (↑(π • X) : code α β hβ) = π • X :=
rfl

instance mul_action_nonempty_code (hβ : β ≤ α) :
  mul_action (semiallowable_perm α hβ) (nonempty_code α β hβ) :=
subtype.coe_injective.mul_action _ coe_smul

end semiallowable_perm

/-- An allowable permutation is a semi-allowable permutation whose action on code preserves
equivalence. -/
def allowable_perm (hβ : β ≤ α) :=
{π : semiallowable_perm α hβ // ∀ X Y : code α β hβ, π • X ≡ π • Y ↔ X ≡ Y}

namespace allowable_perm
variables {α}

instance : has_coe (allowable_perm α hβ) (semiallowable_perm α hβ) := coe_subtype

lemma coe_injective : injective (coe : allowable_perm α hβ → semiallowable_perm α hβ) :=
subtype.coe_injective

instance (hβ : β ≤ α) : has_one (allowable_perm α hβ) := ⟨⟨1, λ _ _, by simp_rw one_smul⟩⟩
instance (hβ : β ≤ α) : has_inv (allowable_perm α hβ) :=
⟨λ f, ⟨f⁻¹, λ c d, by rw [←f.prop, smul_inv_smul, smul_inv_smul]⟩⟩
instance (hβ : β ≤ α) : has_mul (allowable_perm α hβ) :=
⟨λ f g, ⟨f * g, λ c d, by simp_rw [mul_smul, f.prop, g.prop]⟩⟩
instance (hβ : β ≤ α) : has_div (allowable_perm α hβ) :=
⟨λ f g, ⟨f / g, by { simp_rw [div_eq_mul_inv], exact (f * g⁻¹).2 }⟩⟩
instance (hβ : β ≤ α) : has_pow (allowable_perm α hβ) ℕ :=
⟨λ f n, ⟨f ^ n, begin
  induction n with d hd,
  { simp_rw pow_zero,
    exact (1 : allowable_perm α hβ).2 },
  { simp_rw pow_succ,
    exact (f * ⟨f ^ d, hd⟩).2 }
end⟩⟩

instance (hβ : β ≤ α) : has_pow (allowable_perm α hβ) ℤ :=
⟨λ f n, ⟨f ^ n, begin
  cases n,
  { simp_rw zpow_of_nat,
    exact (f ^ n).2 },
  { simp_rw zpow_neg_succ_of_nat,
    exact (f ^ (n + 1))⁻¹.2 }
end⟩⟩

@[simp] lemma coe_one : ((1 : allowable_perm α hβ) : semiallowable_perm α hβ) = 1 := rfl
@[simp] lemma coe_inv (f : allowable_perm α hβ) : (↑(f⁻¹) : semiallowable_perm α hβ) = f⁻¹ := rfl
@[simp] lemma coe_mul (f g : allowable_perm α hβ) :
  (↑(f * g) : semiallowable_perm α hβ) = f * g := rfl
@[simp] lemma coe_div (f g : allowable_perm α hβ) :
  (↑(f / g) : semiallowable_perm α hβ) = f / g := rfl
@[simp] lemma coe_pow (f : allowable_perm α hβ) (n : ℕ) :
  (↑(f ^ n) : semiallowable_perm α hβ) = f ^ n := rfl
@[simp] lemma coe_zpow (f : allowable_perm α hβ) (n : ℤ) :
  (↑(f ^ n) : semiallowable_perm α hβ) = f ^ n := rfl

instance (hβ : β ≤ α) : group (allowable_perm α hβ) :=
coe_injective.group _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

/-- The coercion from allowable to semi-allowable permutation as a monoid homomorphism. -/
def coe_hom : allowable_perm α hβ →* semiallowable_perm α hβ := ⟨coe, coe_one, coe_mul⟩

/-- Turn an allowable permutation into a structural permutation. -/
def to_struct_perm (hβ : β ≤ α) : allowable_perm α hβ →* struct_perm β :=
semiallowable_perm.to_struct_perm.comp coe_hom

instance mul_action_tangle {β : type_index} (hβ : β < α) :
  mul_action (allowable_perm α le_rfl) (tangle α β hβ) :=
mul_action.comp_hom _ coe_hom

instance mul_action_code (hβ : β ≤ α) : mul_action (allowable_perm α hβ) (code α β hβ) :=
mul_action.comp_hom _ coe_hom

instance mul_action_nonempty_code (hβ : β ≤ α) :
  mul_action (allowable_perm α hβ) (nonempty_code α β hβ) :=
mul_action.comp_hom _ coe_hom

@[simp] lemma height_smul (f : allowable_perm α hβ) (c : nonempty_code α β hβ) :
  height (f • c) = height c := sorry

instance mul_action_support_condition : mul_action (allowable_perm α le_rfl) (support_condition α) :=
mul_action.comp_hom  _ (allowable_perm.to_struct_perm _)

instance has_smul_potential_support : has_smul (allowable_perm α le_rfl) (potential_support α) :=
⟨λ f s, ⟨f • s, s.2.image⟩⟩

@[simp] lemma coe_smul_potential_support (f : allowable_perm α le_rfl) (s : potential_support α) :
  (↑(f • s) : set (support_condition α)) = f • s := rfl

instance mul_action_potential_support :
  mul_action (allowable_perm α le_rfl) (potential_support α) :=
set_like.coe_injective.mul_action _ coe_smul_potential_support

/-- Contains coherence conditions on to_tangle. -/
class phase_1b_coherence (α : Λ) [phase_1a α] [phase_1b α] :=
(to_tangle_perm (β : Λ) (hβ : β < α) (π : allowable_perm α le_rfl) (N : near_litter) :
  @has_smul.smul _ _ (@mul_action.to_has_smul _ _ _ (allowable_action β hβ))
    (π.val.snd β hβ) (to_tangle β hβ N) = to_tangle β hβ (π.val.fst • N))

export phase_1b_coherence (to_tangle_perm)

variables [phase_1b_coherence.{u} α]

/-- The unpacked coherence condition for allowable permutations on proper type indices γ. -/
lemma coherence (π : allowable_perm α hβ) (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) (g) :
  f_map γ δ (coe_lt_coe.mpr (hγ.trans_le hβ)) (hδ.trans_le hβ) (π.val.snd γ hγ • g) =
    π.val.fst • (f_map γ δ (coe_lt_coe.mpr (hγ.trans_le hβ)) (hδ.trans_le hβ) g) :=
begin
  classical,
  unfold has_smul.smul,
  have equiv := code.singleton_equiv hγ hδ hγδ g,
  rw ← π.property at equiv,
  unfold has_smul.smul at equiv, simp at equiv,
  rw code.singleton_equiv_iff at equiv, cases equiv,
  { exfalso,
    have := congr_arg code.extension equiv, dsimp at this, rw coe_eq_coe at this,
    rw this at hγδ, exact hγδ rfl },
  obtain ⟨ε, hc, hε, hγε, hA⟩ := equiv,
  have hc' := coe_eq_coe.mp hc,
  subst hc',
  clear hc,
  dsimp at hA,
  have hA' := hA.symm,
  sorry,
  -- rw A_map_code_coe_eq_iff at hA',
  -- simp at hA', unfold A_map at hA',
  -- simp at hA',
  -- dsimp at hA',
  -- have : to_tangle δ (hε.trans_le hβ) ⟨f_map γ δ _ (hδ.trans_le hβ) (π.val.snd γ hγ • g),
  --   litter_set _, is_near_litter_litter_set _⟩
  --   ∈ to_tangle δ (hε.trans_le hβ) '' local_cardinal (f_map γ δ _ (hδ.trans_le hβ)
  --     (π.val.snd γ hγ • g)) := mem_image_of_mem (to_tangle δ $ hε.trans_le hβ) (by simp),
  -- rw subtype.val_eq_coe at this,
  -- rw hA' at this,
  -- rw mem_smul_set at this,
  -- obtain ⟨t, ⟨N, hN₁, hN₂⟩, ht⟩ := this, have := mem_set_of.mp hN₁, rw ← this, rw ← hN₂ at ht,
  -- sorry
end

lemma commute (π : allowable_perm α hβ) (hδ : δ < β) (X : nonempty_code α β hβ)
  (hX : X.val.extension ≠ δ) :
  π • (A_map_code hδ X) = A_map_code hδ (π • X) := sorry

end allowable_perm

namespace code

/-- Representative codes are mapped to representative codes under allowable permutations. -/
lemma is_representative.smul (π : allowable_perm α hβ) (hδ : δ < β) :
  ∀ c : code α β hβ, c.is_representative → (π • c).is_representative
| _ is_representative.empty :=
  by { convert is_representative.empty, exact code.ext _ _ rfl (image_empty _).heq }
| _ (is_representative.nonempty c hc) := is_representative.nonempty (π • c) $ by rwa π.height_smul

end code
end con_nf
