import mathlib.equiv
import mathlib.order
import params

open cardinal cardinal.is_regular equiv equiv.perm function set
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

open params

/-- Either the base type or a proper type index (an element of `Λ`).
The base type is written `⊥`. -/
@[reducible]
def type_index := with_bot Λ

/-- A *pretangle* is an object that may become a *tangle*,
an element of the model.
The type of pretangles forms a model of TTT without extensionality. -/
def pretangle : Λ → Type u
| α :=
    (Π β < α, set (pretangle β)) ×
    (option (set base_type)) ×
    ({β : type_index | β < α})
using_well_founded { dec_tac := `[assumption] }

namespace pretangle

def members {α : Λ} (a : pretangle α) : Π (β < α), set (pretangle β) :=
by { unfold pretangle at a, exact a.1 }

-- TODO: Why is there an `option` in the set of base members?
def base_members {α : Λ} (a : pretangle α) : option (set base_type) :=
by { unfold pretangle at a, exact a.2.1 }

def preferred_extension {α : Λ} (a : pretangle α) : {β : type_index | β < α} :=
by { unfold pretangle at a, exact a.2.2 }

instance has_mem {α β : Λ} (h : β < α) :
has_mem (pretangle β) (pretangle α) :=
⟨λ b a, b ∈ a.members β h⟩

instance has_mem_base_type {α : Λ} :
has_mem base_type (pretangle α) :=
⟨λ b a, a.base_members.elim false (λ s, b ∈ s)⟩

end pretangle

end con_nf
