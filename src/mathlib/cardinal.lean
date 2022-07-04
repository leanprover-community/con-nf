import set_theory.cardinal.basic

open set
open_locale cardinal

namespace cardinal
variables {α : Type*}

lemma le_mk_diff_add_mk (S T : set α) : #S ≤ #(S \ T : set α) + #T :=
(mk_le_mk_of_subset $ subset_diff_union _ _).trans $ mk_union_le _ _

end cardinal
