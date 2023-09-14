import ConNF.Counting.OrdSupport

/-!
# Equivalence of ordered supports
-/

open Set Sum

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

namespace OrdSupport

/-- Ordered supports are *equivalent* if they are defined on the same set and put support conditions
in the same order. -/
structure Equiv (S T : OrdSupport β) : Prop where
  mem_left ⦃c : SupportCondition β⦄ : c ∈ T → c ∈ S
  mem_right ⦃c : SupportCondition β⦄ : c ∈ S → c ∈ T
  lt_iff_lt ⦃c d : SupportCondition β⦄ (hcS : c ∈ S) (hcT : c ∈ T) (hdS : d ∈ S) (hdT : d ∈ T) :
    (S.cpos c).get hcS < (S.cpos d).get hdS ↔ (T.cpos c).get hcT < (T.cpos d).get hdT

namespace Equiv

def refl (S : OrdSupport β) : Equiv S S where
  mem_left _ hc := hc
  mem_right _ hc := hc
  lt_iff_lt _ _ _ _ _ _ := Iff.rfl

def symm {S T : OrdSupport β} (e : Equiv S T) : Equiv T S where
  mem_left _ hc := e.mem_right hc
  mem_right _ hc := e.mem_left hc
  lt_iff_lt _ _ hcT hcS hdT hdS := (e.lt_iff_lt hcS hcT hdS hdT).symm

def trans {S T U : OrdSupport β} (e : Equiv S T) (f : Equiv T U) : Equiv S U where
  mem_left _ hc := e.mem_left (f.mem_left hc)
  mem_right _ hc := f.mem_right (e.mem_right hc)
  lt_iff_lt _ _ hcS hcU hdS hdU :=
    (e.lt_iff_lt hcS (e.mem_right hcS) hdS (e.mem_right hdS)).trans
    (f.lt_iff_lt (f.mem_left hcU) hcU (f.mem_left hdU) hdU)

end Equiv

instance setoid (β : Iic α) : Setoid (OrdSupport β) where
  r S T := Equiv S T
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

theorem mem_iff_mem {S T : OrdSupport β} (h : S ≈ T) (c : SupportCondition β) :
    c ∈ S ↔ c ∈ T :=
  ⟨fun h' => h.mem_right h', fun h' => h.mem_left h'⟩

theorem smul_equiv_smul {S T : OrdSupport β} (h : S ≈ T) (ρ : Allowable β) :
    ρ • S ≈ ρ • T := by
  constructor
  case mem_left =>
    intro c hc
    exact h.mem_left hc
  case mem_right =>
    intro c hc
    exact h.mem_right hc
  case lt_iff_lt =>
    intro c d hcS hcT hdS hdT
    exact h.lt_iff_lt _ _ _ _

theorem Strong.reduced_of_mem_equiv {S T : OrdSupport β} (hS : S.Strong) (hST : S ≈ T)
    (c : SupportCondition β) (h : c ∈ T) : Reduced c.value :=
  hS.reduced_of_mem c (hST.mem_left h)

theorem Strong.transConstrains_mem_equiv {S T : OrdSupport β} (hS : S.Strong) (hST : S ≈ T)
    (c d : SupportCondition β) (hc : Reduced c.value) (hcd : c <[α] d) (hd : d ∈ T) : c ∈ T :=
  hST.mem_right (hS.transConstrains_mem c d hc hcd (hST.mem_left hd))

theorem Strong.fst_toNearLitter_mem_equiv {S T : OrdSupport β} (hS : S.Strong) (hST : S ≈ T)
    {A : ExtendedIndex β} {a : Atom} (h : ⟨A, inl a⟩ ∈ T) :
    ⟨A, inr a.1.toNearLitter⟩ ∈ T :=
  hST.mem_right (hS.fst_toNearLitter_mem (hST.mem_left h))

theorem Strong.isLitter_of_mem_equiv {S T : OrdSupport β} (hS : S.Strong) (hST : S ≈ T)
    {A : ExtendedIndex β} {N : NearLitter} (h : ⟨A, inr N⟩ ∈ T) :
    N.IsLitter :=
  hS.isLitter_of_mem (hST.mem_left h)

end OrdSupport

def OrdSupportClass (β : Iic α) : Type u :=
  Quotient (OrdSupport.setoid β)

end ConNF
