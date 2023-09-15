import ConNF.BaseType.NearLitter

universe u

namespace ConNF

variable [Params.{u}]

/-- A reordering of some subset of `Atom ⊕ NearLitter`.
Reorders typically have hypotheses attached to them to make them into local order isomorphisms. -/
structure Reorder where
  toFun : Atom ⊕ NearLitter → Atom ⊕ NearLitter
  invFun : Atom ⊕ NearLitter → Atom ⊕ NearLitter

namespace Reorder

instance : CoeFun Reorder (fun _ => Atom ⊕ NearLitter → Atom ⊕ NearLitter) where
  coe := Reorder.toFun

@[simp]
theorem toFun_apply (r : Reorder) (i : Atom ⊕ NearLitter) :
    r.toFun i = r i :=
  rfl

def symm (r : Reorder) : Reorder where
  toFun := r.invFun
  invFun := r.toFun

@[simp]
theorem invFun_apply (r : Reorder) (i : Atom ⊕ NearLitter) :
    r.invFun i = r.symm i :=
  rfl

@[simp]
theorem symm_symm (r : Reorder) :
    r.symm.symm = r :=
  rfl

end Reorder

end ConNF
