import phase1.basic

open set with_bot

universe u

namespace con_nf
variables [params.{u}] (α : Λ) [core_tangle_cumul α] {β : Iio (α : type_index)}
  {s t : set (tangle β)}

/-- An `α` code is a type index `β < α` together with a set of tangles of type `β`. -/
@[derive inhabited] def code : Type u := Σ β : Iio (α : type_index), set (tangle β)

/-- Nonempty codes. -/
abbreviation nonempty_code : Type u := {c : code α // c.2.nonempty}

namespace code
variables {α} {c : code α}

/-- Constructor for `code`. -/
def mk : Π β : Iio (α : type_index), set (tangle β) → code α := sigma.mk

@[simp] lemma fst_mk (β : Iio (α : type_index)) (s : set (tangle β)) : (mk β s).1 = β := rfl
@[simp] lemma snd_mk (β : Iio (α : type_index)) (s : set (tangle β)) : (mk β s).2 = s := rfl

/-- A code is empty if it has no element. -/
protected def is_empty (c : code α) : Prop := c.2 = ∅

protected lemma is_empty.eq : c.is_empty → c.2 = ∅ := id

@[simp] lemma is_empty_mk : (mk β s).is_empty ↔ s = ∅ := iff.rfl

@[simp] lemma mk_inj : mk β s = mk β t ↔ s = t := by simp [mk]

end code
end con_nf
