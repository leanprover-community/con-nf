import mathlib.order
import set_theory.cardinal.basic

open set
open_locale cardinal

universe u
variables {ι α : Type u} {s : set α}

namespace cardinal

lemma mk_bUnion_le' (s : set ι) (f : Π i ∈ s, set α) :
  #(⋃ i (hi : i ∈ s), f i hi) ≤ #s * ⨆ i : s, #(f i.1 i.2) :=
by { rw bUnion_eq_Union, apply mk_Union_le }

lemma nonempty_compl_of_mk_lt_mk (h : #s < #α) : sᶜ.nonempty :=
begin
  simp_rw [set.nonempty_iff_ne_empty, ne.def, compl_eq_empty],
  rintro rfl,
  simpa using h,
end

end cardinal
