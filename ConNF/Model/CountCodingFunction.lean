import ConNF.NewTangle
import ConNF.Counting.CodingFunction

open Cardinal Function MulAction Set Sum Quiver WithBot

open scoped Cardinal

universe u

namespace ConNF.Construction

variable [Params.{u}] [BasePositions]

local instance : Level := ⟨0⟩

theorem zeroTangleData_subsingleton
    (i₁ j₁ : TangleDataLt)
    (i₂ : letI := i₁; PositionedTanglesLt) (j₂ : letI := j₁; PositionedTanglesLt)
    (i₃ : letI := i₁; TypedObjectsLt) (j₃ : letI := j₁; TypedObjectsLt)
    (i₄ : letI := i₁; PositionedObjectsLt) (j₄ : letI := j₁; PositionedObjectsLt) :
    (letI := i₁; letI := i₂; letI := i₃; letI := i₄
    {
      TSet := NewTSet
      Allowable := NewAllowable
      allowableToStructPerm := NewAllowable.toStructPerm
      allowableToStructPerm_injective := NewAllowable.toStructPerm_injective
      has_support := by
        intro t
        obtain ⟨S, hS⟩ := t.prop
        exact ⟨S, fun ρ hρ => Subtype.ext (hS ρ hρ)⟩
      toPretangle := ⟨NewTSet.toPretangle, NewTSet.toPretangle_injective⟩
      toPretangle_smul := NewTSet.toPretangle_smul
    } : TangleData (0 : Λ)) =
    (letI := j₁; letI := j₂; letI := j₃; letI := j₄
    {
      TSet := NewTSet
      Allowable := NewAllowable
      allowableToStructPerm := NewAllowable.toStructPerm
      allowableToStructPerm_injective := NewAllowable.toStructPerm_injective
      has_support := by
        intro t
        obtain ⟨S, hS⟩ := t.prop
        exact ⟨S, fun ρ hρ => Subtype.ext (hS ρ hρ)⟩
      toPretangle := ⟨NewTSet.toPretangle, NewTSet.toPretangle_injective⟩
      toPretangle_smul := NewTSet.toPretangle_smul
    }) := by
  have : i₁ = j₁
  · refine TangleDataLt.ext _ _ ?_
    funext β iβ
    cases (Params.Λ_zero_le β).not_lt (coe_lt_coe.mp iβ.elim)
  cases this
  have : i₂ = j₂
  · refine PositionedTanglesLt.ext _ _ ?_
    funext β iβ
    cases (Params.Λ_zero_le β).not_lt (coe_lt_coe.mp iβ.elim)
  cases this
  have : i₃ = j₃
  · funext β iβ
    cases (Params.Λ_zero_le β).not_lt (coe_lt_coe.mp iβ.elim)
  cases this
  have : i₄ = j₄
  · funext β iβ
    cases (Params.Λ_zero_le β).not_lt (coe_lt_coe.mp iβ.elim)
  cases this
  rfl

local instance : TangleDataLt :=
  ⟨fun β i => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp i.elim)).elim⟩
local instance : PositionedTanglesLt :=
  ⟨fun β i => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp i.elim)).elim⟩
local instance : TypedObjectsLt :=
  fun β i => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp i.elim)).elim
local instance : PositionedObjectsLt :=
  fun β i => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp i.elim)).elim

local instance zeroTangleData : TangleData (0 : Λ) :=
  {
    TSet := NewTSet
    Allowable := NewAllowable
    allowableToStructPerm := NewAllowable.toStructPerm
    allowableToStructPerm_injective := NewAllowable.toStructPerm_injective
    has_support := by
      intro t
      obtain ⟨S, hS⟩ := t.prop
      exact ⟨S, fun ρ hρ => Subtype.ext (hS ρ hρ)⟩
    toPretangle := ⟨NewTSet.toPretangle, NewTSet.toPretangle_injective⟩
    toPretangle_smul := NewTSet.toPretangle_smul
  }

theorem mk_codingFunction_zero_le : #(CodingFunction 0) < #μ := sorry

end ConNF.Construction
