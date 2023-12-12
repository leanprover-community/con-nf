import ConNF.FOA.Properties.Injective
import ConNF.FOA.Properties.Surjective

open Equiv Function Quiver Set Sum WithBot

open scoped Classical Pointwise

universe u

namespace ConNF

namespace StructApprox

variable [Params.{u}] [BasePositions] [Level] [FOAAssumptions] {β : Λ} [LeLevel β]
  [FreedomOfActionHypothesis β] {π : StructApprox β}

theorem completeAtomMap_bijective (hπf : π.Free) (A : ExtendedIndex β) :
    Bijective (π.completeAtomMap A) :=
  ⟨completeAtomMap_injective hπf A, completeAtomMap_surjective hπf A⟩

theorem completeLitterMap_bijective (hπf : π.Free) (A : ExtendedIndex β) :
    Bijective (π.completeLitterMap A) :=
  ⟨completeLitterMap_injective hπf A, completeLitterMap_surjective hπf A⟩

theorem completeNearLitterMap_bijective (hπf : π.Free) (A : ExtendedIndex β) :
    Bijective (π.completeNearLitterMap A) :=
  ⟨completeNearLitterMap_injective hπf A, completeNearLitterMap_surjective hπf A⟩

end StructApprox

end ConNF
