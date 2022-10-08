import set_theory.cardinal.continuum

open set
open_locale cardinal

universes u

namespace Well_order

@[simp] lemma eta (o : Well_order) : mk o.α o.r o.wo = o := by { cases o, refl }

end Well_order

namespace ordinal

@[simp] lemma type_out (o : ordinal) : ordinal.type o.out.r = o :=
by rw [ordinal.type, Well_order.eta, quotient.out_eq]

end ordinal

variables {α : Type*}

namespace cardinal

lemma le_mk_diff_add_mk (S T : set α) : #S ≤ #(S \ T : set α) + #T :=
(mk_le_mk_of_subset $ subset_diff_union _ _).trans $ mk_union_le _ _

end cardinal

open cardinal

lemma set.subsingleton.coe_sort {s : set α} : s.subsingleton → subsingleton s :=
s.subsingleton_coe.2

lemma set.subsingleton.cardinal_mk_le_one {s : set α} (hs : s.subsingleton) : #s ≤ 1 :=
le_one_iff_subsingleton.2 hs.coe_sort
