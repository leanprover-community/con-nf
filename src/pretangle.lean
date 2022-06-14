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

end con_nf
