import mathlib.equiv
import mathlib.order
import params

open cardinal cardinal.is_regular equiv equiv.perm function set
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

open params

/-- A *pretangle* is an object that may become a *tangle*,
an element of the model. -/
def pretangle : Λ → Type u
| α :=
    (Π (β : Λ), β < α → set (pretangle β)) ×
    (option (set base_type)) ×
    ({β : with_bot Λ | β < α})
using_well_founded { dec_tac := `[assumption] }

end con_nf
