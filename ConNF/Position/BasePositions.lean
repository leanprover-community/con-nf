import ConNF.Position.Deny
import ConNF.Base.NearLitter

/-!
# Base positions

In this file, we define position functions for atoms, litters, and near-litters.

## Main declarations

* `ConNF.instPositionLitter`: The position function for litters.
* `ConNF.instPositionAtom`: The position function for atoms.
* `ConNF.instPositionNearLitter`: The position function for near-litters.
-/

noncomputable section
universe u

open Cardinal
open scoped symmDiff

namespace ConNF

variable [Params.{u}]

/-!
TODO: These position functions are very simple to define but might not have all the required
properties (e.g. joint injectivity, positions of litters compared to their near-litters).
We should investigate this later, once we know precisely what is needed.
The properties of the position function on litters allows for a concise description of the
fuzz map condition.
-/

instance : Position Litter where
  pos := ⟨funOfDeny card_litter.le (λ L ↦ {L.ν})
      (λ _ ↦ (mk_singleton _).trans_lt (one_lt_aleph0.trans aleph0_lt_μ_ord_cof)),
    funOfDeny_injective _ _ _⟩

theorem Litter.lt_pos (L : Litter) :
    L.ν < pos L :=
  funOfDeny_gt_deny _ _ _ _ _ rfl

instance : Position Atom where
  pos := ⟨funOfDeny card_atom.le (λ a ↦ {pos aᴸ})
      (λ _ ↦ (mk_singleton _).trans_lt (one_lt_aleph0.trans aleph0_lt_μ_ord_cof)),
    funOfDeny_injective _ _ _⟩

theorem Atom.pos_litter_lt_pos (a : Atom) :
    pos aᴸ < pos a :=
  funOfDeny_gt_deny _ _ _ _ _ rfl

instance : Position NearLitter where
  pos := ⟨funOfDeny card_nearLitter.le (λ N ↦ {pos Nᴸ} ∪ ⋃ (a ∈ Nᴬ ∆ Nᴸᴬ), {pos a})
      (λ N ↦ (small_union (small_singleton _)
        (small_biUnion N.symmDiff_small (λ _ _ ↦ small_singleton _))).trans_le κ_le_μ_ord_cof),
    funOfDeny_injective _ _ _⟩

theorem NearLitter.pos_litter_lt_pos (N : NearLitter) :
    pos Nᴸ < pos N :=
  funOfDeny_gt_deny _ _ _ _ _ (Or.inl rfl)

theorem NearLitter.pos_atom_lt_pos (N : NearLitter) (a : Atom) (h : a ∈ Nᴬ ∆ Nᴸᴬ) :
    pos a < pos N :=
  funOfDeny_gt_deny _ _ _ _ _ (Or.inr ⟨_, ⟨a, rfl⟩, _, ⟨h, rfl⟩, rfl⟩)

end ConNF
