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

lemma beth_mono : monotone beth := beth_strict_mono.monotone

lemma beth_normal : ordinal.is_normal.{u} (λ o, (beth o).ord) :=
(ordinal.is_normal_iff_strict_mono_limit _).2 ⟨ord_strict_mono.comp beth_strict_mono, λ o ho a ha,
  begin
    have : bdd_above (range $ λ b : Iio o, beth.{u} b) :=
      ⟨beth o, forall_range_iff.2 $ λ b, beth_mono $ le_of_lt b.2⟩,
    rw [beth_limit ho, ordinal.supr_ord this],
    exact csupr_le' (λ b, ha _ b.2),
  end⟩

lemma aleph_one_lt_beth_aleph_one : aleph 1 < beth (aleph 1).ord :=
begin
  refine aleph_one_le_continuum.trans_lt _,
  rw [←two_power_aleph_0, ←beth_zero, ←beth_succ, ordinal.succ_zero],
  exact beth_lt.2 (ord_aleph_is_limit _).one_lt,
end

end cardinal

open cardinal

lemma set.subsingleton.coe_sort {s : set α} : s.subsingleton → subsingleton s :=
s.subsingleton_coe.2

lemma set.subsingleton.cardinal_mk_le_one {s : set α} (hs : s.subsingleton) : #s ≤ 1 :=
le_one_iff_subsingleton.2 hs.coe_sort
