import phase1.code_equiv

/-!
# Allowable permutations
-/

open function set with_bot
open_locale pointwise

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

variables (α : Λ) [phase_1a α] [phase_1b α] {β γ δ : Λ} {hβ : β ≤ α}

/-- A semi-allowable permutation is a `-1`-allowable permutation of atoms (a near-litter
permutation) together with allowable permutations on all `γ < β`. This forms a group structure
automatically. -/
@[derive group] def semiallowable_perm : Type u := near_litter_perm × Π γ (h : γ < α), allowable γ h

instance near_litter_perm.mul_action_tangle (hβ : β < α) :
  mul_action near_litter_perm (tangle α β $ coe_lt_coe.2 hβ) :=
{ smul := λ f t, to_tangle _ _ $ f • sorry,
  one_smul := sorry,
  mul_smul := sorry }

namespace semiallowable_perm
variables {α} (π : semiallowable_perm α) (c : code α α le_rfl)

def to_struct_perm : semiallowable_perm α →* struct_perm α := sorry

instance mul_action_tangle {γ : type_index} (hγ : γ < α) :
  mul_action (semiallowable_perm α) (tangle α γ hγ) :=
{ smul := λ π, rec_bot_coe
    (λ hγ t, π.fst.atom_perm t)
    (λ γ hγ, (•) (π.snd γ $ coe_lt_coe.mp hγ)) γ hγ,
  one_smul := λ t, by { cases γ, { refl }, { exact one_smul _ _ } },
  mul_smul := λ f g t, by { cases γ, { refl }, { exact mul_smul _ _ _ } } }

instance mul_action_code : mul_action (semiallowable_perm α) (code α α le_rfl) :=
{ smul := λ π c,
    ⟨c.extension, c.extension_lt,
      rec_bot_coe
      (λ none_lt, ((•) π.1 : set atom → set atom))
      (λ γ γ_lt, (•) (π.snd γ $ coe_lt_coe.mp γ_lt))
      c.extension c.extension_lt c.elts⟩,
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
  π • c =
    ⟨c.extension, c.extension_lt,
    rec_bot_coe
      (λ none_lt elts, π.fst.atom_perm '' elts)
    (λ γ γ_lt elts, (•) (π.snd γ $ coe_lt_coe.mp γ_lt) '' elts)
      c.extension c.extension_lt c.elts⟩ := rfl

@[simp] lemma extension_smul : (π • c).extension = c.extension := rfl
@[simp] lemma elts_smul :
  (π • c).elts = rec_bot_coe
      (λ none_lt elts, π.fst.atom_perm '' elts)
      (λ γ γ_lt elts, (•) (π.snd γ $ coe_lt_coe.mp γ_lt) '' elts)
        c.extension c.extension_lt c.elts := rfl

instance has_smul_nonempty_code : has_smul (semiallowable_perm α) (nonempty_code α α le_rfl) :=
⟨λ π c, ⟨π • c, let ⟨⟨γ, hγ, G⟩, hG⟩ := c in
  by induction γ using with_bot.rec_bot_coe; exact hG.image _⟩⟩

@[simp, norm_cast] lemma coe_smul (c : nonempty_code α α le_rfl) :
  (↑(π • c) : code α α le_rfl) = π • c := rfl

instance mul_action_nonempty_code : mul_action (semiallowable_perm α) (nonempty_code α α le_rfl) :=
subtype.coe_injective.mul_action _ coe_smul

end semiallowable_perm

/-- An allowable permutation is a semi-allowable permutation whose action on code preserves
equivalence. -/
def allowable_perm := {π : semiallowable_perm α // ∀ X Y : code α α le_rfl, π • X ≡ π • Y ↔ X ≡ Y}

namespace allowable_perm
variables {α} {f : allowable_perm α} {c d : code α α le_rfl}

instance : has_coe (allowable_perm α) (semiallowable_perm α) := coe_subtype

lemma coe_injective : injective (coe : allowable_perm α → semiallowable_perm α) :=
subtype.coe_injective

instance : has_one (allowable_perm α) := ⟨⟨1, λ _ _, by simp_rw one_smul⟩⟩
instance : has_inv (allowable_perm α) :=
⟨λ f, ⟨f⁻¹, λ c d, by rw [←f.prop, smul_inv_smul, smul_inv_smul]⟩⟩
instance : has_mul (allowable_perm α) :=
⟨λ f g, ⟨f * g, λ c d, by simp_rw [mul_smul, f.prop, g.prop]⟩⟩
instance : has_div (allowable_perm α) :=
⟨λ f g, ⟨f / g, by { simp_rw [div_eq_mul_inv], exact (f * g⁻¹).2 }⟩⟩
instance : has_pow (allowable_perm α) ℕ :=
⟨λ f n, ⟨f ^ n, begin
  induction n with d hd,
  { simp_rw pow_zero,
    exact (1 : allowable_perm α).2 },
  { simp_rw pow_succ,
    exact (f * ⟨f ^ d, hd⟩).2 }
end⟩⟩

instance : has_pow (allowable_perm α) ℤ :=
⟨λ f n, ⟨f ^ n, begin
  cases n,
  { simp_rw zpow_of_nat,
    exact (f ^ n).2 },
  { simp_rw zpow_neg_succ_of_nat,
    exact (f ^ (n + 1))⁻¹.2 }
end⟩⟩

@[simp] lemma coe_one : ((1 : allowable_perm α) : semiallowable_perm α) = 1 := rfl
@[simp] lemma coe_inv (f : allowable_perm α) : (↑(f⁻¹) : semiallowable_perm α) = f⁻¹ := rfl
@[simp] lemma coe_mul (f g : allowable_perm α) : (↑(f * g) : semiallowable_perm α) = f * g := rfl
@[simp] lemma coe_div (f g : allowable_perm α) : (↑(f / g) : semiallowable_perm α) = f / g := rfl
@[simp] lemma coe_pow (f : allowable_perm α) (n : ℕ) :
  (↑(f ^ n) : semiallowable_perm α) = f ^ n := rfl
@[simp] lemma coe_zpow (f : allowable_perm α) (n : ℤ) :
  (↑(f ^ n) : semiallowable_perm α) = f ^ n := rfl

instance : group (allowable_perm α) :=
coe_injective.group _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

/-- The coercion from allowable to semi-allowable permutation as a monoid homomorphism. -/
def coe_hom : allowable_perm α →* semiallowable_perm α := ⟨coe, coe_one, coe_mul⟩

/-- Turn an allowable permutation into a structural permutation. -/
def to_struct_perm : allowable_perm α →* struct_perm α :=
semiallowable_perm.to_struct_perm.comp coe_hom

instance mul_action_tangle {γ : type_index} (hγ : γ < α) :
  mul_action (allowable_perm α) (tangle α γ hγ) :=
mul_action.comp_hom _ coe_hom

instance mul_action_code : mul_action (allowable_perm α) (code α α le_rfl) :=
mul_action.comp_hom _ coe_hom

@[simp] lemma extension_smul (f : allowable_perm α) (c : code α α le_rfl) :
  (f • c).extension = c.extension := rfl

@[simp] lemma elts_smul (f : allowable_perm α) (c : code α α le_rfl) : (f • c).elts = f • c.elts :=
by obtain ⟨_ | γ, hγ, s⟩ := c; refl

@[simp] lemma smul_code_mk (f : allowable_perm α) (γ hγ s) :
  f • (⟨γ, hγ, s⟩ : code α α le_rfl) =
    ⟨γ, hγ, rec_bot_coe (λ hγ, (•) f) (λ γ hγ, (•) f) γ hγ s⟩ := rfl

instance mul_action_nonempty_code (hβ : β ≤ α) :
  mul_action (allowable_perm α) (nonempty_code α α le_rfl) :=
mul_action.comp_hom _ coe_hom

lemma _root_.con_nf.code.equiv.smul : c ≡ d → f • c ≡ f • d := (f.2 _ _).2

instance mul_action_support_condition : mul_action (allowable_perm α) (support_condition α) :=
mul_action.comp_hom _ allowable_perm.to_struct_perm

instance has_smul_potential_support : has_smul (allowable_perm α) (potential_support α) :=
⟨λ f s, ⟨f • s, s.2.image⟩⟩

@[simp] lemma coe_smul_potential_support (f : allowable_perm α) (s : potential_support α) :
  (↑(f • s) : set (support_condition α)) = f • s := rfl

instance mul_action_potential_support : mul_action (allowable_perm α) (potential_support α) :=
set_like.coe_injective.mul_action _ coe_smul_potential_support

end allowable_perm

/-- Contains coherence conditions on `to_tangle`. -/
class phase_1b_coherence (α : Λ) [phase_1a α] [phase_1b α] : Prop :=
(to_tangle_perm (β : Λ) (hβ : β < α) (π : allowable_perm α) (N : near_litter) :
  @has_smul.smul _ _ (@mul_action.to_has_smul _ _ _ (allowable_action β hβ))
    ((↑π : semiallowable_perm α).snd β hβ) (to_tangle β hβ N) =
      to_tangle β hβ ((↑π : semiallowable_perm α).fst • N))

export phase_1b_coherence (to_tangle_perm)

variables {α} [phase_1b_coherence α] {f : allowable_perm α} {c d : code α α le_rfl}

namespace allowable_perm

/-- The unpacked coherence condition for allowable permutations on proper type indices γ. -/
lemma coherence (π : allowable_perm α) (hγ : γ < α) (hδ : δ < α) (hγδ : γ ≠ δ) (g) :
  π.1.1 • f_map γ δ (coe_lt_coe.2 hγ) hδ g = f_map γ δ (coe_lt_coe.2 hγ) hδ (π.val.snd γ hγ • g) :=
begin
  classical,
  unfold has_smul.smul,
  have equiv := code.equiv.singleton (coe_lt_coe.2 hγ) hδ (coe_ne_coe.2 hγδ) g,
  rw ← π.property at equiv,
  unfold has_smul.smul at equiv,
  simp only [subtype.val_eq_coe, rec_bot_coe_coe, image_smul, smul_set_singleton] at equiv,
  rw [code.equiv.comm, code.equiv.singleton_iff] at equiv,
  cases equiv,
  { have := congr_arg code.extension equiv,
    cases hγδ.symm (with_bot.coe_injective this) },
  obtain ⟨ε, hc, hε, hγε, hA⟩ := equiv,
  have hc' := coe_eq_coe.mp hc,
  subst hc',
  clear hc,
  dsimp at hA,
  rw [code.mk_eq_mk, ← set.image_smul, set.image_image] at hA,
  simp_rw to_tangle_perm at hA,
  rw set.image_comp _ (λ a, (↑π : semiallowable_perm α).fst • a) at hA,
  unfold A_map at hA,
  simpa only [set.image_eq_image (embedding.injective $ to_tangle δ _), image_smul,
    near_litter_perm.smul_local_cardinal, mem_singleton_iff, Union_Union_eq_left,
    function.injective.eq_iff local_cardinal_injective] using hA
end

lemma smul_A_map {γ : type_index} {hγ : γ < α} (π : allowable_perm α) (hδ : δ < α)
  (s : set (tangle α γ hγ)) (hγδ : γ ≠ δ) :
  π • A_map hδ s = A_map hδ (π • s) :=
sorry

lemma smul_A_map_code (π : allowable_perm α) (hδ : δ < α) {c : code α α le_rfl}
  (hc : c.extension ≠ δ) :
  π • A_map_code hδ c = A_map_code hδ (π • c) :=
by simp only [code.ext_iff, smul_A_map _ hδ _ hc, extension_smul, extension_A_map_code,
  eq_self_iff_true, elts_smul, elts_A_map_code, heq_iff_eq, and_self]

end allowable_perm

@[simp] lemma A_map_rel.smul {c d : code α α le_rfl} : c ↝ d → f • c ↝ f • d :=
by { rintro ⟨δ, hδ, hcδ⟩, exact (A_map_rel_iff _ _).2 ⟨_, hδ, hcδ, f.smul_A_map_code _ hcδ⟩ }

@[simp] lemma smul_A_map_rel {c d : code α α le_rfl} : f • c ↝ f • d ↔ c ↝ d :=
by { refine ⟨λ h, _, A_map_rel.smul⟩, rw [←inv_smul_smul f c, ←inv_smul_smul f d], exact h.smul }

namespace code

lemma is_even_smul_nonempty : ∀ (c : nonempty_code α α le_rfl), (f • c.val).is_even ↔ c.val.is_even
| ⟨c, hc⟩ := begin
  simp_rw code.is_even_iff,
  split; intros h d hd,
  { have := hd.nonempty_iff.2 hc,
    let rec : A_map_rel' ⟨d, this⟩ ⟨c, hc⟩ := A_map_rel_coe_coe.1 hd,
    exact code.not_is_even.1 (λ H, (h _ hd.smul).not_is_even $
      (is_even_smul_nonempty ⟨d, this⟩).2 H) },
  { rw ←smul_inv_smul f d at hd ⊢,
    rw smul_A_map_rel at hd,
    have := hd.nonempty_iff.2 hc,
    let rec : A_map_rel' ⟨_, this⟩ ⟨c, hc⟩ := A_map_rel_coe_coe.1 hd,
    exact code.not_is_even.1 (λ H, (h _ hd).not_is_even $ (is_even_smul_nonempty ⟨_, this⟩).1 H) }
end
using_well_founded { dec_tac := `[assumption] }

@[simp] lemma is_even_smul : (f • c).is_even ↔ c.is_even :=
begin
  cases c.elts.eq_empty_or_nonempty,
  { obtain ⟨γ, hγ, G⟩ := c,
    dsimp at h,
    subst h,
    have : f • (⟨γ, hγ, ∅⟩ : code α α le_rfl) = ⟨γ, hγ, ∅⟩,
    { induction γ using with_bot.rec_bot_coe; simp },
    rw [this, code.is_even_empty_iff] },
  { exact is_even_smul_nonempty ⟨c, h⟩ }
end

@[simp] lemma is_odd_smul : (f • c).is_odd ↔ c.is_odd :=
by simp_rw [←code.not_is_even, is_even_smul]

alias is_even_smul ↔ _ is_even.smul
alias is_odd_smul ↔ _ is_odd.smul

end code
end con_nf
