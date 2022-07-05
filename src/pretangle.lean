import params

noncomputable theory

universe u

namespace con_nf
variables [params.{u}]

open params

/-- A *pretangle* is an object that may become a *tangle*,
an element of the model.
The type of pretangles forms a model of TTT without extensionality. -/
def pretangle : Λ → Type u
| α := set atom × Π β < α, set (pretangle β)
using_well_founded { dec_tac := `[assumption] }

namespace pretangle

variable {α : Λ}

def mk (atoms : set atom) (extensions : Π β < α, set (pretangle β)) : pretangle α :=
by { unfold pretangle, exact ⟨atoms, extensions⟩ }

/-- Obtains the members of a pretangle of type `α`, seen as a set of atoms.
This is called the `-1`-extension of the pretangle. -/
def atom_extension (a : pretangle α) : set atom :=
by { unfold pretangle at a, exact a.fst }

/-- Obtains the members of a pretangle of type `α`, seen as a set of elements of type `β < α`.
This is called the `β`-extension of the pretangle. -/
def extension (a : pretangle α) : Π (β < α), set (pretangle β) :=
by { unfold pretangle at a, exact a.snd }

@[simp] lemma atom_extension_mk (atoms : set atom) (extensions : Π β < α, set (pretangle β)) :
  (mk atoms extensions).atom_extension = atoms :=
by { simp [atom_extension, mk] }

@[simp] lemma extension_mk (atoms : set atom) (extensions : Π β < α, set (pretangle β)) :
  (mk atoms extensions).extension = extensions :=
by { simp [extension, mk] }

lemma eta (t : pretangle α) : mk (t.atom_extension) (t.extension) = t :=
by { simp [atom_extension, extension, mk] }

/-- The membership relation defined on pretangles for atoms. -/
instance has_mem_atom : has_mem atom (pretangle α) :=
⟨λ b a, b ∈ a.atom_extension⟩

-- Yaël: Note, this instance is useless as it won't fire because `β < α` is not a class
/-- The membership relation defined on pretangles.
This is exactly the membership relation on tangles, without the extensionality condition that
allows this membership relation to be used in a model of TTT. -/
instance has_mem {α β : Λ} (h : β < α) : has_mem (pretangle β) (pretangle α) :=
⟨λ b a, b ∈ a.extension β h⟩

end pretangle

end con_nf
