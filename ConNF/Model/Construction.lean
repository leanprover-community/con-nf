import ConNF.NewTangle
import ConNF.Counting

open Cardinal Function MulAction Set Quiver

open scoped Cardinal

universe u

namespace ConNF.Construction

variable [Params.{u}] [Level]
  {data : TangleDataLt} {positioned : PositionedTanglesLt} {typed : TypedObjectsLt}

def levelTangleData
    (data : TangleDataLt) (positioned : PositionedTanglesLt) (typed : TypedObjectsLt) :
    TangleData α where
  Tangle := NewTangle
  Allowable := NewAllowable
  allowableToStructPerm := NewAllowable.toStructPerm
  support := NewTangle.S
  support_supports := by
    intro t ρ h
    refine NewTangle.ext _ _ (t.h ρ h) ?_
    refine Enumeration.ext' rfl ?_
    intro i hi _
    exact h ⟨i, hi, rfl⟩

def levelTypedObjects
    (data : TangleDataLt) (positioned : PositionedTanglesLt) (typed : TypedObjectsLt) :
    letI := levelTangleData data positioned typed
    TypedObjects α :=
  letI := levelTangleData data positioned typed
  {
    typedAtom := ⟨newTypedAtom, newTypedAtom_injective⟩
    typedNearLitter := ⟨newTypedNearLitter, newTypedNearLitter_injective⟩
    smul_typedNearLitter := fun N ρ => NewAllowable.smul_newTypedNearLitter ρ N
  }

theorem eq_of_not_ltLevel {β : Λ} [LeLevel β] (h : ¬(β : TypeIndex) < α) : β = α :=
  WithBot.coe_injective (le_antisymm (inferInstanceAs (LeLevel β)).elim (le_of_not_lt h))

def lowerTangleData
    (data : TangleDataLt) (positioned : PositionedTanglesLt) (typed : TypedObjectsLt)
    (β : Λ) [LeLevel β] : TangleData β :=
  if h : (β : TypeIndex) < α then
    have : LtLevel β := ⟨h⟩
    data.data β
  else
    eq_of_not_ltLevel h ▸ levelTangleData data positioned typed

def lowerTangleData_lt_eq (β : Λ) [i : LtLevel β] :
    lowerTangleData data positioned typed β = data.data β :=
  by rw [lowerTangleData, dif_pos i.elim]

instance : LeLevel α := ⟨le_rfl⟩

def lowerTangleData_level_eq :
    lowerTangleData data positioned typed α = levelTangleData data positioned typed :=
  by rw [lowerTangleData, dif_neg (gt_irrefl _)]

def foaData
    (data : TangleDataLt) (positioned : PositionedTanglesLt) (typed : TypedObjectsLt) :
    FOAData where
  lowerTangleData := lowerTangleData data positioned typed
  lowerPositionedTangles β := lowerTangleData_lt_eq β ▸ positioned.data β
  lowerTypedObjects β :=
    if h : (β : TypeIndex) < α then
      have : LtLevel β := ⟨h⟩
      lowerTangleData_lt_eq β ▸ typed β
    else
      eq_of_not_ltLevel h ▸ lowerTangleData_level_eq ▸ levelTypedObjects data positioned typed

def foaAssumptions
    (data : TangleDataLt) (positioned : PositionedTanglesLt) (typed : TypedObjectsLt) :
    FOAAssumptions where
  __ := foaData data positioned typed
  allowableCons := sorry
  allowableCons_eq := sorry
  smul_support := sorry
  pos_lt_pos_atom := sorry
  pos_lt_pos_nearLitter := sorry
  smul_fuzz := sorry
  allowableOfSmulFuzz := sorry
  allowableOfSmulFuzz_comp_eq := sorry

end ConNF.Construction
