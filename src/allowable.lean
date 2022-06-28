import code
import struct_perm
import A_map

/-!
# Allowable permutations
-/

universe u

namespace con_nf
variable [params.{u}]

open params with_bot

variables (α : Λ) [phase_1a.{u} α]

/-- Contains all the information needed for phase 1b of the recursion.
We use an explicit `→*` here instead of a `monoid_hom_class` so that we don't need to worry
about typeclass instances not firing under a `β < α` condition. -/
class phase_1b :=
(allowable : Π β < α, Type*) [allowable_group : Π β (h : β < α), group (allowable β h)]
(to_structural : Π β (h : β < α), allowable β h →* struct_perm α)
[allowable_action : Π β (h : β < α), mul_action (allowable β h) (tangle α β (coe_lt_coe.mpr h))]

export phase_1b (allowable allowable_group to_structural allowable_action)

variables [phase_1b.{u} α]

def allowable_scalar : Π β (h : β < α), has_scalar (allowable β h) (tangle α β (coe_lt_coe.mpr h)) :=
λ β h, @mul_action.to_has_scalar _ _
  (@group.to_monoid _ (allowable_group β h)) (allowable_action β h)

-- TODO(zeramorphic): When `pi.group` works with `Prop`, change this to just an invocation of `pi.group`.
instance allowable_group_pi' {β : Λ} (hβ : β ≤ α) (γ : Λ) :
group (∀ (h : γ < β), allowable γ (h.trans_le hβ)) := {
  one := (λ h, (allowable_group γ (h.trans_le hβ)).one),
  mul := (λ x y h, @group.mul _ (allowable_group γ (h.trans_le hβ)) (x h) (y h)),
  one_mul := (λ x, funext (λ h, @group.one_mul _ (allowable_group γ (h.trans_le hβ)) (x h))),
  mul_one := (λ x, funext (λ h, @group.mul_one _ (allowable_group γ (h.trans_le hβ)) (x h))),
  mul_assoc := (λ x y z, funext (λ h, @group.mul_assoc _ (allowable_group γ (h.trans_le hβ)) (x h) (y h) (z h))),
  inv := (λ x h, @group.inv _ (allowable_group γ (h.trans_le hβ)) (x h)),
  mul_left_inv := (λ x, funext (λ h, @group.mul_left_inv _ (allowable_group γ (h.trans_le hβ)) (x h))),
  div := (λ x y h, @group.div _ (allowable_group γ (h.trans_le hβ)) (x h) (y h)),
  div_eq_mul_inv := (λ x y, funext (λ h, @group.div_eq_mul_inv _ (allowable_group γ _) (x h) (y h))),
  npow := (λ n x h, @group.npow _ (allowable_group γ (h.trans_le hβ)) n (x h)),
  npow_zero' := (λ x, funext (λ h, @group.npow_zero' _ (allowable_group γ _) (x h))),
  npow_succ' := (λ n x, funext (λ h, @group.npow_succ' _ (allowable_group γ _) n (x h))),
  zpow := (λ n x h, @group.zpow _ (allowable_group γ (h.trans_le hβ)) n (x h)),
  zpow_zero' := (λ x, funext (λ h, @group.zpow_zero' _ (allowable_group γ _) (x h))),
  zpow_succ' := (λ n x, funext (λ h, @group.zpow_succ' _ (allowable_group γ _) n (x h))),
  zpow_neg' := (λ n x, funext (λ h, @group.zpow_neg' _ (allowable_group γ _) n (x h))),
}

instance allowable_group_pi {β : Λ} (hβ : β ≤ α) :
group (Π γ (h : γ < β), allowable γ (h.trans_le hβ)) :=
@pi.group _ _ (con_nf.allowable_group_pi' α hβ)

/-- A semiallowable permutation is a `-1`-allowable permutation of atoms (a near-litter permutation)
together with allowable permutations on all `γ < β`. This forms a group structure automatically. -/
def semiallowable_perm {β : Λ} (hβ : β ≤ α) :=
near_litter_perm × Π γ (h : γ < β), allowable γ (h.trans_le hβ)

instance semiallowable_perm_group {β : Λ} (hβ : β ≤ α) : group (semiallowable_perm α hβ) :=
prod.group

instance semiallowable_perm_scalar {β : Λ} (hβ : β ≤ α) :
has_scalar (semiallowable_perm α hβ) (code α β hβ) :=
⟨λ π X,
  ⟨X.extension, X.extension_lt,
    option.rec
    (λ none_lt elts, π.fst.atom_perm '' elts)
    (λ γ γ_lt elts,
      (λ g, @has_scalar.smul _ _ (allowable_scalar α γ _)(π.snd γ (coe_lt_coe.mp γ_lt)) g) '' elts)
    X.extension X.extension_lt X.elts⟩⟩

lemma semiallowable_perm_scalar_def {β : Λ} (hβ : β ≤ α)
(π : semiallowable_perm α hβ) (X : code α β hβ) :
π • X = ⟨X.extension, X.extension_lt,
  option.rec
  (λ none_lt elts, π.fst.atom_perm '' elts)
  (λ γ γ_lt elts,
    (λ g, @has_scalar.smul _ _ (allowable_scalar α γ _)(π.snd γ (coe_lt_coe.mp γ_lt)) g) '' elts)
  X.extension X.extension_lt X.elts⟩ := rfl

instance semiallowable_perm_scalar_nonempty {β : Λ} (hβ : β ≤ α) :
has_scalar (semiallowable_perm α hβ) {c : code α β hβ // c.elts.nonempty} :=
⟨λ π X, ⟨π • X.val, begin
  obtain ⟨⟨γ, hγ, G⟩, hG⟩ := X,
  rw semiallowable_perm_scalar_def, dsimp,
  cases γ; simp; exact hG
end⟩⟩

-- TODO(zeramorphic)
instance semiallowable_perm_action {β : Λ} (hβ : β ≤ α) :
mul_action (semiallowable_perm α hβ) (code α β hβ) := sorry

def allowable_perm {β : Λ} (hβ : β ≤ α) :=
{π : semiallowable_perm α hβ // ∀ (X Y : code α β hβ), X ≡ Y ↔ π • X ≡ π • Y}

instance allowable_perm_scalar {β : Λ} (hβ : β ≤ α) :
has_scalar (allowable_perm α hβ) (code α β hβ) := ⟨λ π X, π.val • X⟩

instance allowable_perm_scalar_nonempty {β : Λ} (hβ : β ≤ α) :
has_scalar (allowable_perm α hβ) {c : code α β hβ // c.elts.nonempty} := ⟨λ π X, π.val • X⟩

/-- The unpacked coherence condition for allowable permutations on proper type indices γ. -/
lemma allowable_perm_coherence {β : Λ} {hβ : β ≤ α} (π : allowable_perm α hβ) :
∀ γ (hγ : γ < β) δ (hδ : δ < β) g,
f_map γ δ (coe_lt_coe.mpr (hγ.trans_le hβ)) (hδ.trans_le hβ)
  (@has_scalar.smul _ _ (allowable_scalar α γ (hγ.trans_le hβ)) (π.val.snd γ hγ) g) =
π.val.fst • (f_map γ δ (coe_lt_coe.mpr (hγ.trans_le hβ)) (hδ.trans_le hβ) g) :=
begin
  classical,
  rintros γ hγ δ hδ g,
  unfold has_scalar.smul,
  have : ⟨γ, coe_lt_coe.mpr hγ, {g}⟩ ≡
    ⟨δ, coe_lt_coe.mpr hδ, to_tangle δ (hδ.trans_le hβ) ''
      local_cardinal (f_map γ δ (coe_lt_coe.mpr (hγ.trans_le hβ)) (hδ.trans_le hβ) g)⟩,
  { unfold code_equiv, dsimp, rw dif_pos (set.singleton_nonempty g), },
end

lemma allowable_perm_commute {β : Λ} {hβ : β ≤ α} (π : allowable_perm α hβ)
{δ : Λ} (hδ : δ < β) (X : {c : code α β hβ // c.elts.nonempty}) (hX : X.val.extension ≠ δ) :
π • (A_map_code hβ hδ X hX) = A_map_code hβ hδ (π • X) hX := sorry

/-- Representative codes are mapped to representative codes under allowable permutations. -/
lemma representative_code_map {β : Λ} {hβ : β ≤ α} (π : allowable_perm α hβ)
{δ : Λ} (hδ : δ < β) (X : code α β hβ) (hX : X.is_representative) :
(π • X).is_representative := sorry

end con_nf
