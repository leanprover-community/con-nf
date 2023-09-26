import ConNF.Foa.Basic.Reduction

/-!
# Ordered supports
-/

open Set Sum

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

structure OrdSupport (β : Iic α) where
  /-- The set of support conditions in this ordered support. -/
  carrier : Set (SupportCondition β)
  /-- An order on `carrier`. -/
  r : carrier → carrier → Prop
  /-- `r` is a well order. -/
  r_isWellOrder : IsWellOrder carrier r

namespace OrdSupport

variable {S : OrdSupport β}

instance : CoeTC (OrdSupport β) (Set (SupportCondition β)) where
  coe := OrdSupport.carrier

instance : Membership (SupportCondition β) (OrdSupport β) where
  mem c S := c ∈ S.carrier

instance : CoeSort (OrdSupport β) (Type _) :=
  ⟨fun S => { x : SupportCondition β // x ∈ S }⟩

@[simp, norm_cast]
theorem coe_sort_coe (S : OrdSupport β) : ((S : Set (SupportCondition β)) : Type _) = S :=
  rfl

instance : IsWellOrder S S.r := S.r_isWellOrder

instance : PartialOrder S := partialOrderOfSO S.r

open scoped Classical in
noncomputable instance : LinearOrder S := linearOrderOfSTO S.r

end OrdSupport

end ConNF
