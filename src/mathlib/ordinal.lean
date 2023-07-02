import set_theory.ordinal.arithmetic

open set

universe u
variables {ι α : Type u} {s : set α}

namespace ordinal

@[protected]
lemma is_limit.is_succ_limit {o : ordinal} (h : o.is_limit) : order.is_succ_limit o :=
by { rw [order.is_succ_limit_iff_succ_lt], exact h.2, }

end ordinal
