import mathlib.prod
import group_theory.group_action.sigma
import phase1.code_equiv

/-!
# Allowable permutations
-/

-- Note to whoever fixes this file: We may want to use `type_index` instead of `Λ` in some places
-- now that supports are defined in these cases.

open function set with_bot
open_locale pointwise

noncomputable theory

universe u

namespace con_nf
variables [params.{u}] (α : Λ) [core_tangle_cumul α] (β : Iio_index α) (γ : Iio α)

open code

/-- A semi-allowable permutation is a `-1`-allowable permutation of atoms (a near-litter
permutation) together with allowable permutations on all `γ < β`. This forms a group structure
automatically. -/
@[derive group] def semiallowable_perm : Type u := Π β : Iio_index α, allowable β

namespace semiallowable_perm
variables {α} (π : semiallowable_perm α) (c : code α)

/-- The allowable permutation at a lower level corresponding to a semi-allowable permutation. -/
noncomputable! def to_allowable : semiallowable_perm α →* allowable β :=
⟨λ f, f β, rfl, λ _ _, rfl⟩

/-- Reinterpret a semi-allowable permutation as a structural permutation. -/
noncomputable! def to_struct_perm : semiallowable_perm α →* struct_perm α :=
{ to_fun := λ f, struct_perm.to_coe $ λ β hβ, (f ⟨β, hβ⟩).to_struct_perm,
  map_one' := struct_perm.of_coe.injective $ funext $ λ β, funext $ λ hβ, match β, hβ with
    | ⊥, _ := by { simp only [struct_perm.of_coe_to_coe, struct_perm.of_coe_one, pi.one_apply],
      exact struct_perm.to_bot_one }
    | (β : Λ), (hβ : ↑β < ↑α) := by { simp only [struct_perm.of_coe_to_coe, struct_perm.of_coe_one,
      pi.one_apply], exact allowable.to_struct_perm.map_one }
  end,
  map_mul' := λ f g, struct_perm.of_coe.injective $ funext $ λ β, funext $ λ hβ, match β, hβ with
    | ⊥, _ := by { simp only [struct_perm.of_coe_to_coe, struct_perm.of_coe_mul, pi.mul_apply],
      exact struct_perm.to_bot_mul _ _ }
    | (β : Λ), (hβ : ↑β < ↑α) := by { simp only [struct_perm.of_coe_to_coe, struct_perm.of_coe_mul,
      pi.mul_apply], exact allowable.to_struct_perm.map_mul _ _ }
  end }

section
variables {X : Type*} [mul_action (struct_perm α) X]

instance mul_action_of_struct_perm : mul_action (semiallowable_perm α) X :=
mul_action.comp_hom _ to_struct_perm

@[simp] lemma to_struct_perm_smul (f : semiallowable_perm α) (x : X) :
  f.to_struct_perm • x = f • x := rfl

end

instance mul_action_tangle : mul_action (semiallowable_perm α) (tangle β) :=
mul_action.comp_hom _ $ to_allowable β

instance mul_action_tangle' {β : Iio α} : mul_action (semiallowable_perm α) (tangle β) :=
show mul_action (semiallowable_perm α) (tangle $ Iio_coe β), from infer_instance

instance mul_action_tangle'' : mul_action (semiallowable_perm α) (tangle (γ : Λ)) :=
show mul_action (semiallowable_perm α) (tangle $ Iio_coe γ), from infer_instance

@[simp] lemma to_allowable_smul (f : semiallowable_perm α) (t : tangle β) :
  to_allowable β f • t = f • t := rfl

attribute [derive mul_action (semiallowable_perm α)] code

@[simp] lemma fst_smul : (π • c).1 = c.1 := rfl
@[simp] lemma snd_smul : (π • c).2 = π • c.2 := rfl
@[simp] lemma smul_mk (f : semiallowable_perm α) (γ s) : f • (mk γ s : code α) = mk γ (f • s) := rfl

instance has_smul_nonempty_code : has_smul (semiallowable_perm α) (nonempty_code α) :=
⟨λ π c, ⟨π • c, c.2.image _⟩⟩

@[simp, norm_cast] lemma coe_smul (c : nonempty_code α) : (↑(π • c) : code α) = π • c := rfl

instance mul_action_nonempty_code : mul_action (semiallowable_perm α) (nonempty_code α) :=
subtype.coe_injective.mul_action _ coe_smul

end semiallowable_perm

variables [position_data.{}] [positioned_tangle_cumul α] [almost_tangle_cumul α]
  [core_tangle_data α]

/-- An allowable permutation is a semi-allowable permutation whose action on codes preserves
equivalence. -/
def allowable_perm := {π : semiallowable_perm α // ∀ X Y : code α, π • X ≡ π • Y ↔ X ≡ Y}

variables {α} {f : allowable_perm α} {c d : code α}

namespace allowable_perm

instance : has_coe_t (allowable_perm α) (semiallowable_perm α) := @coe_base _ _ coe_subtype

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
@[simps] noncomputable! def coe_hom : allowable_perm α →* semiallowable_perm α :=
⟨coe, coe_one, coe_mul⟩

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

@[simp] lemma fst_smul_near_litter (f : allowable_perm α) (N : near_litter) : (f • N).1 = f • N.1 :=
rfl
@[simp] lemma snd_smul_near_litter (f : allowable_perm α) (N : near_litter) :
  ((f • N).2 : set atom) = f • ↑N.2 := rfl

@[simp] lemma smul_typed_near_litter (f : allowable_perm α) (N : near_litter) :
  f • (typed_near_litter N : tangle (γ : Λ)) =
    typed_near_litter ((f : semiallowable_perm α) γ • N) :=
allowable.smul_typed_near_litter _ _

@[simp] lemma fst_smul (f : allowable_perm α) (c : code α) : (f • c).1 = c.1 := rfl
@[simp] lemma snd_smul (f : allowable_perm α) (c : code α) : (f • c).2 = f • c.2 := rfl
@[simp] lemma smul_mk (f : allowable_perm α) (γ s) : f • (mk γ s : code α) = mk γ (f • s) := rfl

lemma _root_.con_nf.code.equiv.smul : c ≡ d → f • c ≡ f • d := (f.2 _ _).2

end allowable_perm

namespace allowable_perm
variables {β γ}

lemma smul_f_map (hβγ : β ≠ γ) (π : allowable_perm α) (t : tangle β) :
  ((π : semiallowable_perm α) γ) • f_map (coe_ne hβγ) t = f_map (coe_ne hβγ) (π • t) :=
begin
  classical,
  have equiv := code.equiv.singleton hβγ t,
  rw ← π.prop at equiv,
  simp only [subtype.val_eq_coe, rec_bot_coe_coe, image_smul, smul_set_singleton] at equiv,
  simp only [code.equiv_iff] at equiv,
  obtain a | ⟨heven, ε, hε, hA⟩ | ⟨heven, ε, hε, hA⟩ | ⟨c, heven, ε, hε, ζ, hζ, h₁, h₂⟩ := equiv,
  { cases hβγ.symm (congr_arg sigma.fst a) },
  { simp_rw [semiallowable_perm.smul_mk, smul_set_singleton] at hA,
    cases A_map_code_ne_singleton _ hA.symm,
    exact hβγ.symm },
  { have := congr_arg sigma.fst hA,
    simp only [semiallowable_perm.smul_mk, fst_A_map_code, fst_mk, Iio.coe_inj] at this,
    subst this,
    simp only [semiallowable_perm.smul_mk, A_map_code_ne _ (mk β _) hβγ, mk_inj] at hA,
    simp only [coe_smul, snd_mk, smul_set_singleton, A_map_singleton] at hA,
    simp only [← image_smul, image_image, smul_typed_near_litter] at hA,
    rw ← image_image at hA,
    rw image_eq_image typed_near_litter.injective at hA,
    have := litter.to_near_litter_mem_local_cardinal (f_map (coe_ne hβγ) (π • t)),
    rw ← hA at this,
    obtain ⟨N, hN₁, hN₂⟩ := this,
    have := congr_arg sigma.fst hN₂,
    simp only [litter.to_near_litter_fst] at this,
    rw [← allowable.to_struct_perm_smul, struct_perm.smul_near_litter_fst,
      allowable.to_struct_perm_smul] at this,
    rw mem_local_cardinal at hN₁,
    rw hN₁ at this,
    exact this },
  { have := congr_arg sigma.fst h₁,
    simp only [coe_smul, smul_mk, fst_mk, fst_A_map_code] at this,
    subst this,
    simp only [coe_smul, smul_mk, smul_set_singleton] at h₁,
    cases A_map_code_ne_singleton hε h₁.symm }
end

lemma smul_A_map (π : allowable_perm α) (s : set (tangle β)) (hβγ : β ≠ γ) :
  π • A_map hβγ s = A_map hβγ (π • s) :=
begin
  ext,
  simp only [A_map, mem_image, mem_Union, mem_local_cardinal, exists_prop, ← image_smul],
  simp only [exists_exists_and_eq_and, smul_typed_near_litter, ← smul_f_map hβγ],
  split,
  { rintro ⟨N, ⟨y, y_mem, y_fmap⟩, rfl⟩,
    refine ⟨(π : semiallowable_perm α) γ • N, ⟨y, y_mem, _⟩, rfl⟩,
    rw ← y_fmap,
    refl },
  { rintro ⟨N, ⟨y, y_mem, y_fmap⟩, rfl⟩,
    refine ⟨((π : semiallowable_perm α) γ)⁻¹ • N, ⟨y, y_mem, _⟩, _⟩,
    { change _ • N.fst = _,
      simp only [y_fmap, map_inv, inv_smul_eq_iff],
      refl },
    { simp only [smul_inv_smul] } },
end

lemma smul_A_map_code (π : allowable_perm α) (hc : c.1 ≠ γ) :
  π • A_map_code γ c = A_map_code γ (π • c) :=
by simp only [A_map_code_ne γ c hc, A_map_code_ne γ (π • c) hc, smul_A_map, snd_smul, smul_mk]

end allowable_perm

lemma A_map_rel.smul : c ↝ d → f • c ↝ f • d :=
by { rintro ⟨γ, hγ⟩, exact (A_map_rel_iff _ _).2 ⟨_, hγ, f.smul_A_map_code hγ⟩ }

@[simp] lemma smul_A_map_rel : f • c ↝ f • d ↔ c ↝ d :=
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
  cases c.2.eq_empty_or_nonempty,
  { rw [is_empty.is_even_iff h, is_empty.is_even_iff],
    { refl },
    simpa [code.is_empty] },
  { exact is_even_smul_nonempty ⟨c, h⟩ }
end

@[simp] lemma is_odd_smul : (f • c).is_odd ↔ c.is_odd :=
by simp_rw [←code.not_is_even, is_even_smul]

alias is_even_smul ↔ _ is_even.smul
alias is_odd_smul ↔ _ is_odd.smul

end code
end con_nf
