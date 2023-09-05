import ConNF.Counting.OrdSupport

/-!
# Equivalence of ordered supports
-/

open Set Sum

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

namespace OrdSupport

/-- An equivalence of ordered supports.

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
@[ext]
structure Equiv (S T : OrdSupport β) where
  toFun : μ → μ
  invFun : μ → μ
  mem_left (c : SupportCondition β) : c ∈ T → c ∈ S
  mem_right (c : SupportCondition β) : c ∈ S → c ∈ T
  toFun_apply (c : SupportCondition β) (hS : c ∈ S) (hT : c ∈ T) :
    toFun ((S.cpos c).get hS) = (T.cpos c).get hT
  invFun_apply (c : SupportCondition β) (hT : c ∈ T) (hS : c ∈ S) :
    invFun ((T.cpos c).get hT) = (S.cpos c).get hS
  lt_iff_lt (c d : SupportCondition β) (hcS : c ∈ S) (hcT : c ∈ T) (hdS : d ∈ S) (hdT : d ∈ T) :
    (S.cpos c).get hcS < (S.cpos d).get hdS ↔ (T.cpos c).get hcT < (T.cpos d).get hdT

namespace Equiv

theorem mem_iff_mem {S T : OrdSupport β} (e : Equiv S T) (c : SupportCondition β) :
    c ∈ S ↔ c ∈ T :=
  ⟨e.mem_right c, e.mem_left c⟩

def refl (S : OrdSupport β) : Equiv S S where
  toFun := id
  invFun := id
  mem_left _ hc := hc
  mem_right _ hc := hc
  toFun_apply _ _ _ := rfl
  invFun_apply _ _ _ := rfl
  lt_iff_lt _ _ _ _ _ _ := Iff.rfl

def symm {S T : OrdSupport β} (e : Equiv S T) : Equiv T S where
  toFun := e.invFun
  invFun := e.toFun
  mem_left c hc := e.mem_right c hc
  mem_right c hc := e.mem_left c hc
  toFun_apply c hT hS := e.invFun_apply c hT hS
  invFun_apply c hS hT := e.toFun_apply c hS hT
  lt_iff_lt c d hcT hcS hdT hdS := (e.lt_iff_lt c d hcS hcT hdS hdT).symm

def trans {S T U : OrdSupport β} (e : Equiv S T) (f : Equiv T U) : Equiv S U where
  toFun := f.toFun ∘ e.toFun
  invFun := e.invFun ∘ f.invFun
  mem_left c hc := e.mem_left c (f.mem_left c hc)
  mem_right c hc := f.mem_right c (e.mem_right c hc)
  toFun_apply c hS hU := by
    rw [Function.comp_apply, e.toFun_apply c hS (e.mem_right c hS)]
    exact f.toFun_apply c (e.mem_right c hS) hU
  invFun_apply c hU hS := by
    rw [Function.comp_apply, f.invFun_apply c hU (f.mem_left c hU)]
    exact e.invFun_apply c (f.mem_left c hU) hS
  lt_iff_lt c d hcS hcU hdS hdU :=
    (e.lt_iff_lt c d hcS (e.mem_right c hcS) hdS (e.mem_right d hdS)).trans
    (f.lt_iff_lt c d (f.mem_left c hcU) hcU (f.mem_left d hdU) hdU)

end Equiv

instance setoid (β : Iic α) : Setoid (OrdSupport β) where
  r S T := Nonempty (Equiv S T)
  iseqv := by
    constructor
    case refl =>
      intro S
      exact ⟨Equiv.refl S⟩
    case symm =>
      rintro S T ⟨e⟩
      exact ⟨e.symm⟩
    case trans =>
      rintro S T U ⟨e⟩ ⟨f⟩
      exact ⟨e.trans f⟩

theorem mem_iff_mem_of_equiv {S T : OrdSupport β} (h : S ≈ T) (c : SupportCondition β) :
    c ∈ S ↔ c ∈ T :=
  h.some.mem_iff_mem c

end OrdSupport

def OrdSupportClass (β : Iic α) : Type u :=
  Quotient (OrdSupport.setoid β)

-- TODO: API for `OrdSupportClass` once we know what's needed.

end ConNF
