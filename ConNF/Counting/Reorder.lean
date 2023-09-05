import ConNF.BaseType.Params

universe u

namespace ConNF

variable [Params.{u}]

/-- A reordering of some subset of `μ`.
Reorders typically have hypotheses attached to them to make them into local order isomorphisms. -/
structure Reorder where
  toFun : μ → μ
  invFun : μ → μ

namespace Reorder

instance : CoeFun Reorder (fun _ => μ → μ) where
  coe := Reorder.toFun

@[simp]
theorem toFun_apply (r : Reorder) (ν : μ) :
    r.toFun ν = r ν :=
  rfl

def symm (r : Reorder) : Reorder where
  toFun := r.invFun
  invFun := r.toFun

@[simp]
theorem invFun_apply (r : Reorder) (ν : μ) :
    r.invFun ν = r.symm ν :=
  rfl

@[simp]
theorem symm_symm (r : Reorder) :
    r.symm.symm = r :=
  rfl

end Reorder

end ConNF
