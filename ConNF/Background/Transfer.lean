module

public import Mathlib.Algebra.Group.TransferInstance
public import ConNF.Background.Ordinal

@[expose] public section

universe u v

namespace Equiv

variable {α : Type u} {β : Type v} (e : α ≃ β)

@[implicit_reducible]
protected def decidableLE [LE β] [DecidableRel ((· ≤ ·) : β → β → Prop)] :
    letI := e.le
    DecidableRel ((· ≤ ·) : α → α → Prop) :=
  λ x y ↦ inferInstanceAs (Decidable (e x ≤ e y))

@[implicit_reducible]
protected def decidableLT [LT β] [DecidableRel ((· < ·) : β → β → Prop)] :
    letI := e.lt
    DecidableRel ((· < ·) : α → α → Prop) :=
  λ x y ↦ inferInstanceAs (Decidable (e x < e y))

protected def leIso [LE β] :
    letI := e.le
    ((· ≤ ·) : α → α → Prop) ≃r ((· ≤ ·) : β → β → Prop) where
  map_rel_iff' := Iff.rfl
  __ := e

protected def orderIso [LE β] :
    letI := e.le
    α ≃o β :=
  e.leIso

protected def ltIso [LT β] :
    letI := e.lt
    ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop) where
  map_rel_iff' := Iff.rfl
  __ := e

protected theorem wellFoundedLT [DecidableEq α] [LinearOrder β] [WellFoundedLT β] :
    letI := e.linearOrder
    WellFoundedLT α :=
  letI := e.linearOrder
  ⟨InvImage.wf e wellFounded_lt⟩

theorem type_lt [DecidableEq α] [LinearOrder β] [WellFoundedLT β] :
    letI := e.linearOrder
    letI := e.wellFoundedLT
    Ordinal.lift.{max u v, u} (Ordinal.type ((· < ·) : α → α → Prop)) =
    Ordinal.lift.{max u v, v} (Ordinal.type ((· < ·) : β → β → Prop)) := by
  let := e.linearOrder
  let := e.wellFoundedLT
  rw [Ordinal.lift_type_eq.{u, v, max u v}]
  exact ⟨e.ltIso⟩

theorem typein_lt [DecidableEq α] [LinearOrder β] [WellFoundedLT β] (x : α) :
    letI := e.linearOrder
    letI := e.wellFoundedLT
    Ordinal.lift.{max u v, v} (Ordinal.typein ((· < ·) : β → β → Prop) (e x)) =
    Ordinal.lift.{max u v, u} (Ordinal.typein ((· < ·) : α → α → Prop) x) := by
  let := e.linearOrder
  have := e.wellFoundedLT
  exact Ordinal.lift_typein_apply (r := (· < ·)) (s := (· < ·)) (f := ⟨⟨e.toEmbedding, .rfl⟩,
    fun a b _ ↦ ⟨e.symm b, by simp⟩⟩) x

protected theorem noMaxOrder [LT β] [NoMaxOrder β] :
    letI := e.lt
    NoMaxOrder α := by
  let := e.lt
  constructor
  intro x
  obtain ⟨y, hy⟩ := exists_gt (e x)
  use e.symm y
  rw [← lt_def, apply_symm_apply]
  exact hy

@[implicit_reducible]
protected def ofNat (n : ℕ) [OfNat β n] : OfNat α n where
  ofNat := e.symm (OfNat.ofNat n)

theorem apply_add [Add β] (x y : α) :
    letI := e.add
    e (x + y) = e x + e y := by
  rw [add_def, apply_symm_apply]

theorem apply_sub [Sub β] (x y : α) :
    letI := e.sub
    e (x - y) = e x - e y := by
  rw [sub_def, apply_symm_apply]

theorem apply_zero [Zero β] :
    letI := e.zero
    e 0 = 0 := by
  rw [zero_def, apply_symm_apply]

end Equiv
