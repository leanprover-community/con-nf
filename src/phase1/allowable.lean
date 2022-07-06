import mathlib.prod
import phase1.code_equiv

/-!
# Allowable permutations
-/

open function set with_bot
open_locale pointwise

noncomputable theory

universe u

namespace con_nf
variables [params.{u}] {α β γ δ : Λ} [phase_1 α] {hβ : β < α}

namespace allowable

/-- Reinterpret an allowable permutation as a structural permutation. -/
def to_struct_perm (hβ : β < α) : allowable β hβ →* struct_perm β :=
phase_1.allowable_to_struct_perm _ _

instance mul_action_tangle : mul_action (allowable β hβ) (tangle α β $ coe_lt_coe.2 hβ) :=
phase_1.allowable_action _ _

end allowable

variables (α)

/-- A semi-allowable permutation is a `-1`-allowable permutation of atoms (a near-litter
permutation) together with allowable permutations on all `γ < β`. This forms a group structure
automatically. -/
@[derive group] def semiallowable_perm : Type u := near_litter_perm × Π β (h : β < α), allowable β h

instance near_litter_perm.mul_action_tangle (hβ : β < α) :
  mul_action near_litter_perm (tangle α β $ coe_lt_coe.2 hβ) :=
{ smul := λ f t, to_tangle _ _ $ f • sorry,
  one_smul := sorry,
  mul_smul := sorry }

namespace semiallowable_perm
variables {α} (π : semiallowable_perm α) (c : code α)

/-- The allowable permutation at a lower level corresponding to a semi-allowable permutation. -/
def to_allowable (hβ : β < α) : semiallowable_perm α →* allowable β hβ :=
⟨λ f, f.2 β hβ, rfl, λ _ _, rfl⟩

/-- Reinterpret a semi-allowable permutation as a structural permutation. -/
def to_struct_perm : semiallowable_perm α →* struct_perm α :=
{ to_fun := λ f, struct_perm.to_coe $ λ β hβ, match β, hβ with
    | ⊥, _ := struct_perm.to_bot f.1
    | (β : Λ), (hβ : ↑β < ↑α) := allowable.to_struct_perm (coe_lt_coe.1 hβ) $ to_allowable _ f
  end,
  map_one' := struct_perm.of_coe.injective $ funext $ λ β, funext $ λ hβ, match β, hβ with
    | ⊥, _ := by { simp only [struct_perm.of_coe_to_coe, struct_perm.of_coe_one, pi.one_apply],
      exact struct_perm.to_bot_one }
    | (β : Λ), (hβ : ↑β < ↑α) := by { simp only [struct_perm.of_coe_to_coe, struct_perm.of_coe_one,
      pi.one_apply], exact (allowable.to_struct_perm _).map_one }
  end,
  map_mul' := λ f g, struct_perm.of_coe.injective $ funext $ λ β, funext $ λ hβ, match β, hβ with
    | ⊥, _ := by { simp only [struct_perm.of_coe_to_coe, struct_perm.of_coe_mul, pi.mul_apply],
      exact struct_perm.to_bot_mul _ _ }
    | (β : Λ), (hβ : ↑β < ↑α) := by { simp only [struct_perm.of_coe_to_coe, struct_perm.of_coe_mul,
      pi.mul_apply], exact (allowable.to_struct_perm _).map_mul _ _ }
  end }

section
variables {X : Type*} [mul_action (struct_perm α) X]

instance mul_action_of_struct_perm : mul_action (semiallowable_perm α) X :=
mul_action.comp_hom _ to_struct_perm

@[simp] lemma to_struct_perm_smul (f : semiallowable_perm α) (x : X) :
  f.to_struct_perm • x = f • x := rfl

end

instance mul_action_tangle' (hβ : β < α) :
  mul_action (semiallowable_perm α) (phase_1.tangle β hβ) :=
mul_action.comp_hom _ $ to_allowable hβ

instance mul_action_tangle {β : type_index} (hβ : β < α) :
  mul_action (semiallowable_perm α) (tangle α β hβ) :=
{ smul := λ π, match β, hβ with
    | ⊥, hβ := π.fst.atom_perm
    | (β : Λ), hβ := (•) (π.snd β $ coe_lt_coe.1 hβ)
  end,
  one_smul := λ t, by { cases β, { refl }, { exact one_smul _ _ } },
  mul_smul := λ f g t, by { cases β, { refl }, { exact mul_smul _ _ _ } } }

@[simp] lemma smul_to_tangle (f : semiallowable_perm α) (N : near_litter) {β} (hβ : β < α) :
  f • to_tangle β hβ N = to_tangle β hβ (f • N) :=
begin
  refine (smul_to_tangle _ _ (to_allowable hβ f) N).trans _,
  simp only [embedding_like.apply_eq_iff_eq],
  sorry -- ought to be refl
end

instance mul_action_code : mul_action (semiallowable_perm α) (code α) :=
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

instance has_smul_nonempty_code : has_smul (semiallowable_perm α) (nonempty_code α) :=
⟨λ π c, ⟨π • c, let ⟨⟨γ, hγ, G⟩, hG⟩ := c in
  by induction γ using with_bot.rec_bot_coe; exact hG.image _⟩⟩

@[simp, norm_cast] lemma coe_smul (c : nonempty_code α) :
  (↑(π • c) : code α) = π • c := rfl

instance mul_action_nonempty_code : mul_action (semiallowable_perm α) (nonempty_code α) :=
subtype.coe_injective.mul_action _ coe_smul

end semiallowable_perm

/-- An allowable permutation is a semi-allowable permutation whose action on code preserves
equivalence. -/
def allowable_perm := {π : semiallowable_perm α // ∀ X Y : code α, π • X ≡ π • Y ↔ X ≡ Y}

namespace allowable_perm
variables {α} {f : allowable_perm α} {c d : code α}

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

section
variables {X : Type*} [mul_action (semiallowable_perm α) X]

instance mul_action_of_semiallowable_perm : mul_action (allowable_perm α) X :=
mul_action.comp_hom _ coe_hom

@[simp] lemma coe_smul (f : allowable_perm α) (x : X) : (f : semiallowable_perm α) • x = f • x :=
rfl

end

@[simp] lemma smul_to_tangle (f : allowable_perm α) (N : near_litter) (β) (hβ : β < α) :
  f • to_tangle β hβ N = to_tangle β hβ (f • N) :=
sorry -- smul_to_tangle β hβ (semiallowable_perm.to_allowable hβ f.1) N

@[simp] lemma extension_smul (f : allowable_perm α) (c : code α) :
  (f • c).extension = c.extension := rfl

@[simp] lemma elts_smul (f : allowable_perm α) (c : code α) : (f • c).elts = f • c.elts :=
by obtain ⟨_ | γ, hγ, s⟩ := c; refl

@[simp] lemma smul_code_mk (f : allowable_perm α) (γ hγ s) :
  f • (⟨γ, hγ, s⟩ : code α) = ⟨γ, hγ, rec_bot_coe (λ hγ, (•) f) (λ γ hγ, (•) f) γ hγ s⟩ := rfl

lemma _root_.con_nf.code.equiv.smul : c ≡ d → f • c ≡ f • d := (f.2 _ _).2

instance has_smul_potential_support : has_smul (allowable_perm α) (potential_support α) :=
⟨λ f s, ⟨f • s, s.2.image⟩⟩

@[simp] lemma coe_smul_potential_support (f : allowable_perm α) (s : potential_support α) :
  (↑(f • s) : set (support_condition α)) = f • s := rfl

instance mul_action_potential_support : mul_action (allowable_perm α) (potential_support α) :=
set_like.coe_injective.mul_action _ coe_smul_potential_support

end allowable_perm

variables {α} {f : allowable_perm α} {c d : code α}

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
  rw [code.mk_inj, ← set.image_smul, set.image_image] at hA,
  sorry
  -- simp_rw ←smul_to_tangle at hA,
  -- rw set.image_comp _ (λ a, (↑π : semiallowable_perm α).fst • a) at hA,
  -- unfold A_map at hA,
  -- simpa only [set.image_eq_image (embedding.injective $ to_tangle δ _), image_smul,
  --   near_litter_perm.smul_local_cardinal, mem_singleton_iff, Union_Union_eq_left,
  --   local_cardinal_injective.eq_iff] using hA,
end

lemma coherence_bot (hγ : ⊥ < ↑α) (π : allowable_perm α) (hδ : δ < α) (i : tangle α ⊥ hγ) :
  π.val.fst.litter_perm (f_map ⊥ δ hγ hδ i) = f_map ⊥ δ hγ hδ (π.val.fst.atom_perm i) :=
begin
  sorry,
end

lemma a_perm_commutes_with_local_cardinal (π : allowable_perm α) (a : near_litter) (b : litter) :
  π.val.fst • a ∈ local_cardinal (π.val.fst.litter_perm b) ↔ a ∈ local_cardinal b :=
(π : semiallowable_perm α).fst.litter_perm.injective.eq_iff

lemma smul_A_map {γ : type_index} {hγ : γ < α} (π : allowable_perm α) (hδ : δ < α)
  (s : set (tangle α γ hγ)) (hγδ : γ ≠ δ) :
  π • A_map hδ s = A_map hδ (π • s) :=
begin
  unfold A_map,
  dsimp only [(•)],
  simp only [has_smul.comp.smul, image_smul, mem_image, Union_exists, bUnion_and',
    Union_Union_eq_right],
  dsimp only [(coe_hom)],
  simp only [monoid_hom.coe_mk],
  dsimp only [(•)],
  unfold image,
  simp only [mem_Union, exists_prop, mem_set_of_eq, subtype.val_eq_coe, exists_exists_and_eq_and],
  ext,
  simp only [mem_set_of_eq],
  sorry
  -- rw rec_bot_coe_coe,
  -- induction γ using with_bot.rec_bot_coe,
  -- { rw rec_bot_coe_bot,
  --   split,
  --   intro lhs,
  --   use (π.1.1 • lhs.some),
  --   use lhs.some_spec.left.some,
  --   split,
  --   exact lhs.some_spec.left.some_spec.left,
  --   let a := f_map ⊥ δ hγ hδ ((π.val.fst.atom_perm)  lhs.some_spec.left.some),
  --   have hm1 : a = f_map ⊥ δ hγ hδ ((π.val.fst.atom_perm)  lhs.some_spec.left.some), by refl,
  --   suffices hm2 : (π.val.fst • lhs.some) ∈ local_cardinal (a),
  --   { rw hm1 at hm2,
  --     exact hm2 },
  --   rw ← coherence_bot hγ π hδ lhs.some_spec.left.some at hm1,
  --   rw hm1,
  --   exact (a_perm_commutes_with_local_cardinal π lhs.some _).mpr lhs.some_spec.left.some_spec.right,
  --   rw ← smul_to_tangle,
  --   exact lhs.some_spec.right,
  --   intro rhs,
  --   use ((π⁻¹).1.1 • rhs.some),
  --   use rhs.some_spec.left.some,
  --   split,
  --   exact rhs.some_spec.left.some_spec.left,
  --   suffices h5 : π.val.fst • π⁻¹.val.fst • rhs.some ∈ local_cardinal ( π.val.fst.litter_perm (f_map ⊥ δ hγ hδ rhs.some_spec.left.some)),
  --   { rw a_perm_commutes_with_local_cardinal at h5,
  --     exact h5 },
  --   rw (coherence_bot hγ π hδ),
  --   suffices h6 :  π.val.fst • π⁻¹.val.fst • rhs.some = rhs.some,
  --   { rw h6,
  --     exact rhs.some_spec.left.some_spec.right },
  --   apply smul_inv_smul,
  --   rw ← smul_to_tangle,
  --   let f : tangle α ↑δ (coe_lt_coe.mpr hδ) := (to_tangle δ hδ) rhs.some,
  --   suffices h7 : π.val.snd δ _ • π⁻¹.val.snd δ hδ • (f)= x,
  --   { exact h7 },
  --   have h8 : f = (to_tangle δ hδ) rhs.some, by refl,
  --   rw rhs.some_spec.right at h8,
  --   rw h8,
  --   apply smul_inv_smul },
  -- rw rec_bot_coe_coe,
  -- have h1 : (↑π : semiallowable_perm α).snd = π.val.snd, by refl,
  -- rw h1,
  -- have h3 : γ ≠ δ, {by_contra, exact (hγδ (coe_eq_coe.mpr h))},
  -- simp_rw ← coherence π _ hδ h3,
  -- split,
  -- intro lhs,
  -- use (π.1.1 • lhs.some),
  -- use lhs.some_spec.left.some,
  -- split,
  -- exact lhs.some_spec.left.some_spec.left,
  -- exact (a_perm_commutes_with_local_cardinal π lhs.some _).mpr lhs.some_spec.left.some_spec.right,
  -- rw ← smul_to_tangle,
  -- exact lhs.some_spec.right,
  -- intro rhs,
  -- use ((π⁻¹).1.1 • rhs.some),
  -- use rhs.some_spec.left.some,
  -- split,
  -- exact rhs.some_spec.left.some_spec.left,
  -- have h4 : ∀ b : litter, b = π⁻¹.1.fst.litter_perm • π.1.fst.litter_perm • b,
  -- { intro b,
  --   simp only [subtype.val_eq_coe, coe_inv, prod.fst_inv, near_litter_perm.litter_perm_inv,
  --     equiv.perm.smul_def, equiv.perm.inv_apply_self] },
  -- specialize h4 (f_map ↑γ δ hγ hδ rhs.some_spec.left.some),
  -- rw h4,
  -- exact (a_perm_commutes_with_local_cardinal π⁻¹ rhs.some _).mpr rhs.some_spec.left.some_spec.right,
  -- rw ← smul_to_tangle,
  -- rw rhs.some_spec.right,
  -- apply smul_inv_smul,
end

lemma smul_A_map_code (π : allowable_perm α) (hδ : δ < α) {c : code α} (hc : c.extension ≠ δ) :
  π • A_map_code hδ c = A_map_code hδ (π • c) :=
by simp only [code.ext_iff, smul_A_map _ hδ _ hc, extension_smul, extension_A_map_code,
  eq_self_iff_true, elts_smul, elts_A_map_code, heq_iff_eq, and_self]

end allowable_perm

@[simp] lemma A_map_rel.smul {c d : code α} : c ↝ d → f • c ↝ f • d :=
by { rintro ⟨δ, hδ, hcδ⟩, exact (A_map_rel_iff _ _).2 ⟨_, hδ, hcδ, f.smul_A_map_code _ hcδ⟩ }

@[simp] lemma smul_A_map_rel {c d : code α} : f • c ↝ f • d ↔ c ↝ d :=
by { refine ⟨λ h, _, A_map_rel.smul⟩, rw [←inv_smul_smul f c, ←inv_smul_smul f d], exact h.smul }

namespace code

lemma is_even_smul_nonempty : ∀ (c : nonempty_code α), (f • c.val).is_even ↔ c.val.is_even
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
    have : f • (⟨γ, hγ, ∅⟩ : code α) = ⟨γ, hγ, ∅⟩,
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
