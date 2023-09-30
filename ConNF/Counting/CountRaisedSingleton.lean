import ConNF.Counting.Recode
import ConNF.Counting.Spec

/-!
# Counting raised singletons
-/

open Cardinal Function MulAction Set
open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [CountingAssumptions α] {β γ : Iic α} (hγ : γ < β)

noncomputable def raisedSingleton_map
    (σ : Spec β) (hσ : σ.Strong) (χ : CodingFunction γ) (hχ : χ.Strong) :
    RaisedSingleton hγ :=
  sorry

theorem raisedSingleton_surjective :
    Surjective (fun x : { σ : Spec β // σ.Strong } × { χ : CodingFunction γ // χ.Strong } =>
      ULift.up.{u + 1} <| raisedSingleton_map hγ x.1.1 x.1.2 x.2.1 x.2.2) := sorry

/-- The main lemma about counting raised singletons. -/
theorem mk_raisedSingleton :
    lift.{u + 1} #(RaisedSingleton hγ) ≤
    #{ σ : Spec β // σ.Strong } * lift.{u + 1} #{ χ : CodingFunction γ // χ.Strong } := by
  have := mk_le_of_surjective (raisedSingleton_surjective hγ)
  simp only [mk_uLift, mk_prod] at this
  rw [lift_id'.{u, u + 1} _] at this
  exact this

end ConNF
