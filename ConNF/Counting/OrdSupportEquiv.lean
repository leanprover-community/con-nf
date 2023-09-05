import ConNF.Counting.OrdSupport
import ConNF.Counting.Reorder

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
  mem_left (c : SupportCondition β) : c ∈ T → c ∈ S
  mem_right (c : SupportCondition β) : c ∈ S → c ∈ T
  lt_iff_lt (c d : SupportCondition β) (hcS : c ∈ S) (hcT : c ∈ T) (hdS : d ∈ S) (hdT : d ∈ T) :
    (S.cpos c).get hcS < (S.cpos d).get hdS ↔ (T.cpos c).get hcT < (T.cpos d).get hdT

namespace Equiv

def refl (S : OrdSupport β) : Equiv S S where
  mem_left _ hc := hc
  mem_right _ hc := hc
  lt_iff_lt _ _ _ _ _ _ := Iff.rfl

def symm {S T : OrdSupport β} (e : Equiv S T) : Equiv T S where
  mem_left c hc := e.mem_right c hc
  mem_right c hc := e.mem_left c hc
  lt_iff_lt c d hcT hcS hdT hdS := (e.lt_iff_lt c d hcS hcT hdS hdT).symm

def trans {S T U : OrdSupport β} (e : Equiv S T) (f : Equiv T U) : Equiv S U where
  mem_left c hc := e.mem_left c (f.mem_left c hc)
  mem_right c hc := f.mem_right c (e.mem_right c hc)
  lt_iff_lt c d hcS hcU hdS hdU :=
    (e.lt_iff_lt c d hcS (e.mem_right c hcS) hdS (e.mem_right d hdS)).trans
    (f.lt_iff_lt c d (f.mem_left c hcU) hcU (f.mem_left d hdU) hdU)

end Equiv

instance setoid (β : Iic α) : Setoid (OrdSupport β) where
  r S T := Equiv S T
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

theorem mem_iff_mem {S T : OrdSupport β} (h : S ≈ T) (c : SupportCondition β) :
    c ∈ S ↔ c ∈ T :=
  ⟨h.mem_right c, h.mem_left c⟩

theorem smul_equiv_smul {S T : OrdSupport β} (h : S ≈ T) (ρ : Allowable β) :
    ρ • S ≈ ρ • T := by
  constructor
  case mem_left =>
    intro c hc
    exact h.mem_left (ρ⁻¹ • c) hc
  case mem_right =>
    intro c hc
    exact h.mem_right (ρ⁻¹ • c) hc
  case lt_iff_lt =>
    intro c d hcS hcT hdS hdT
    exact h.lt_iff_lt (ρ⁻¹ • c) (ρ⁻¹ • d) _ _ _ _

end OrdSupport

def OrdSupportClass (β : Iic α) : Type u :=
  Quotient (OrdSupport.setoid β)

-- TODO: API for `OrdSupportClass` once we know what's needed.

namespace OrdSupport

/--
`r` is an equivalence of ordered supports `S` and `T`.

Paths in the following diagram starting with `S` or `T` commute, where
* the morphisms `S ↔ T` are the identity,
* the maps `μ ↔ μ` are `toFun` and `invFun`,
* the maps `S → μ` and `T → μ` are `cpos`.
```
μ ↔ μ
↑   ↑
S ↔ T
```
-/
structure IsEquiv (r : Tree Reorder β) (S T : OrdSupport β) : Prop where
  equiv : Equiv S T
  toFun_apply (c : SupportCondition β) (hS : c ∈ S) (hT : c ∈ T) :
    r c.path ((S.cpos c).get hS) = (T.cpos c).get hT
  invFun_apply (c : SupportCondition β) (hT : c ∈ T) (hS : c ∈ S) :
    (r c.path).symm ((T.cpos c).get hT) = (S.cpos c).get hS

theorem isEquiv_smul {r : Tree Reorder β} {S T : OrdSupport β}
    (h : IsEquiv r S T) (ρ : Allowable β) :
    IsEquiv r (ρ • S) (ρ • T) := by
  constructor
  case equiv => exact smul_equiv_smul h.equiv ρ
  case toFun_apply =>
    intros c hS hT
    exact h.toFun_apply (ρ⁻¹ • c) hS hT
  case invFun_apply =>
    intros c hT hS
    exact h.invFun_apply (ρ⁻¹ • c) hT hS

end OrdSupport

end ConNF
