import combinatorics.quiver.basic
import combinatorics.quiver.path
import params
import pretangle

universe u

namespace con_nf
variables [params.{u}]

open params

/-- We define the type of paths from certain types to higher types
as elements of this quiver. -/
instance has_paths : quiver type_index := ⟨(<)⟩

/-- A (finite) path from the base type to type α. -/
def type_index_path (α : Λ) := quiver.path ⊥ (α : type_index)

/-- A proper type index, together with a path from the base type. -/
def type_index_with_path := Σ' (α : Λ), type_index_path α

end con_nf
