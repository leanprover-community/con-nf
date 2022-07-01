import A_map
import mathlib.group
import struct_perm

/-!
# Allowable permutations
-/

universe u

namespace con_nf
variable [params.{u}]

open params set with_bot
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
sorry

namespace semiallowable_perm
variables {α} (π : semiallowable_perm α hβ) (X : code α β hβ)

def to_struct_perm {hβ : β ≤ α} (π : semiallowable_perm α hβ) : struct_perm β := sorry

instance has_smul_tangle {β : type_index} (hβ : β < α) :
  has_smul (semiallowable_perm α le_rfl) (tangle α β hβ) :=
⟨λ π t, with_bot.rec_bot_coe
  (λ hβ t, π.fst.atom_perm t)
  (λ β hβ t, π.snd β (coe_lt_coe.mp hβ) • t) β hβ t⟩

instance mul_action_tangle {β : type_index} (hβ : β < α) :
  mul_action (semiallowable_perm α le_rfl) (tangle α β hβ) := sorry

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

@[reducible] def allowable_perm.to_struct_perm (hβ : β ≤ α) : allowable_perm α hβ → struct_perm β :=
semiallowable_perm.to_struct_perm ∘ subtype.val

instance allowable_perm_group (hβ : β ≤ α) : group (allowable_perm α hβ) := sorry

instance allowable_perm_scalar_tangle {β : type_index} (hβ : β < α) :
has_smul (allowable_perm α le_rfl) (tangle α β hβ) :=
⟨λ π t, π.val • t⟩

instance allowable_perm_mul_tangle {β : type_index} (hβ : β < α) :
mul_action (allowable_perm α le_rfl) (tangle α β hβ) := sorry

instance allowable_perm_scalar_code (hβ : β ≤ α) : has_smul (allowable_perm α hβ) (code α β hβ) :=
⟨λ π X, π.val • X⟩

instance allowable_perm_mul_code (hβ : β ≤ α) : mul_action (allowable_perm α hβ) (code α β hβ) :=
sorry

instance allowable_perm_scalar_nonempty (hβ : β ≤ α) :
  has_smul (allowable_perm α hβ) (nonempty_code α β hβ) := ⟨λ π X, π.val • X⟩

/-- The unpacked coherence condition for allowable permutations on proper type indices γ. -/
lemma allowable_perm_coherence (π : allowable_perm α hβ) (hγ : γ < β) (hδ : δ < β)
  (hγδ : γ ≠ δ) (g) :
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

lemma allowable_perm_commute (π : allowable_perm α hβ) (hδ : δ < β) (X : nonempty_code α β hβ)
  (hX : X.val.extension ≠ δ) :
  π • (A_map_code hδ X) = A_map_code hδ (π • X) := sorry

/-- Representative codes are mapped to representative codes under allowable permutations. -/
lemma code.is_representative.smul (π : allowable_perm α hβ) (hδ : δ < β)
  (X : code α β hβ) (hX : X.is_representative) :
  (π • X).is_representative := sorry

end con_nf
