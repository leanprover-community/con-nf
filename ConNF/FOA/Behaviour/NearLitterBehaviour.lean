import ConNF.FOA.Action.NearLitterAction

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise symmDiff

universe u

namespace ConNF

variable [Params.{u}]

@[ext]
structure NearLitterBehaviour where
  atomMap : Atom →. Atom
  nearLitterMap : NearLitter →. NearLitter
  atomMap_dom_small : Small atomMap.Dom
  nearLitterMap_dom_small : Small nearLitterMap.Dom

namespace NearLitterBehaviour

structure Lawful (ξ : NearLitterBehaviour) : Prop where
  atomMap_injective : ∀ ⦃a b : Atom⦄ (ha : (ξ.atomMap a).Dom) (hb : (ξ.atomMap b).Dom),
    (ξ.atomMap a).get ha = (ξ.atomMap b).get hb → a = b
  atom_mem_iff : ∀ ⦃a : Atom⦄ (ha : (ξ.atomMap a).Dom)
    ⦃N : NearLitter⦄ (hN : (ξ.nearLitterMap N).Dom),
    a ∈ N ↔ (ξ.atomMap a).get ha ∈ (ξ.nearLitterMap N).get hN
  map_nearLitter_fst : ∀ ⦃N₁ N₂ : NearLitter⦄
    (hN₁ : (ξ.nearLitterMap N₁).Dom) (hN₂ : (ξ.nearLitterMap N₂).Dom),
    N₁.fst = N₂.fst ↔ ((ξ.nearLitterMap N₁).get hN₁).fst = ((ξ.nearLitterMap N₂).get hN₂).fst
  mem_of_mem_symmDiff : ∀ ⦃a : Atom⦄ ⦃N₁ N₂ : NearLitter⦄,
    N₁.fst = N₂.fst → (ξ.nearLitterMap N₁).Dom → (ξ.nearLitterMap N₂).Dom →
    a ∈ (N₁ : Set Atom) ∆ N₂ → (ξ.atomMap a).Dom

instance : PartialOrder NearLitterBehaviour
    where
  le ξ ξ' := ξ.atomMap ≤ ξ'.atomMap ∧ ξ.nearLitterMap ≤ ξ'.nearLitterMap
  le_refl ξ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm := by
    intro ξ ξ' h₁ h₂
    ext : 1
    exact le_antisymm h₁.1 h₂.1
    exact le_antisymm h₁.2 h₂.2

def HasLitters (ξ : NearLitterBehaviour) : Prop :=
  ∀ ⦃N : NearLitter⦄, (ξ.nearLitterMap N).Dom → (ξ.nearLitterMap N.1.toNearLitter).Dom

def action (ξ : NearLitterBehaviour) : NearLitterAction where
  atomMap := ξ.atomMap
  litterMap L := ξ.nearLitterMap L.toNearLitter
  atomMap_dom_small := ξ.atomMap_dom_small
  litterMap_dom_small := Small.preimage (fun _ _ => congr_arg Sigma.fst) (ξ.nearLitterMap_dom_small)

theorem exists_hasLitters (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) :
    ∃ ξ' ≥ ξ, ξ'.Lawful ∧ ξ'.HasLitters := sorry

end NearLitterBehaviour

end ConNF
