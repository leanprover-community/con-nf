import ConNF.Foa.Basic.Flexible
import ConNF.Counting.CodingFunction

/-!
# Specifications
-/

open Quiver Set Sum WithBot

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

def Time (β : Iic α) : Type u :=
  μ ×ₗ ExtendedIndex β

inductive SpecCondition (β : Iic α)
  | atom (A : ExtendedIndex β) (i : Time β)
  | flexible (A : ExtendedIndex β)
  | inflexible_coe ⦃γ : Iic α⦄ ⦃δ : Iio α⦄ ⦃ε : Iio α⦄
    (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
    (A : Path (β : TypeIndex) γ) (χ : CodingFunction (δ : Iic α))
  | inflexible_bot ⦃γ : Iic α⦄ ⦃ε : Iio α⦄ (hε : (ε : Λ) < γ) (A : Path (β : TypeIndex) γ)
    (i : Time β)

structure Spec (β : Iic α) where
  /-- `cond i` describes the condition inserted at time `i` in the construction of an ordered
  support. -/
  cond : Time β →. SpecCondition β
  dom_small : Small cond.Dom

/-- A specification `σ` specifies an ordered support `S` if `dom σ = ran S`, and each support
condition in `S` is described in a sensible way by `σ`. -/
structure Specifies (σ : Spec β) (S : OrdSupport β) : Prop where
  cpos_dom (c : SupportCondition β) (hc : c ∈ S) : (σ.cond ⟨(S.cpos c).get hc, c.path⟩).Dom
  exists_mem_of_dom (i : Time β) : (σ.cond i).Dom →
    ∃ c, ∃ (hc : c ∈ S), c.path = i.snd ∧ (S.cpos c).get hc = i.fst
  atom_spec (A : ExtendedIndex β) (a : Atom) (N : NearLitter)
    (ha : ⟨A, inl a⟩ ∈ S) (hN : ⟨A, inr N⟩ ∈ S) : a ∈ N →
    (σ.cond ⟨(S.cpos _).get ha, A⟩).get (cpos_dom ⟨A, inl a⟩ ha) =
    SpecCondition.atom A ⟨(S.cpos _).get hN, A⟩
  flexible_spec (A : ExtendedIndex β) (N : NearLitter) (hN : ⟨A, inr N⟩ ∈ S) : Flexible α A N.fst →
    (σ.cond ⟨(S.cpos _).get hN, A⟩).get (cpos_dom ⟨A, inr N⟩ hN) = SpecCondition.flexible A
  inflexible_coe_spec (A : ExtendedIndex β) (N : NearLitter) (hN : ⟨A, inr N⟩ ∈ S)
    (h : InflexibleCoe A N.1) :
    ∃ χ : CodingFunction h.path.δ,
    ∃ h' : (S.before ((S.cpos _).get hN)).comp h.path.δ (h.path.B.cons h.path.hδ) ∈ χ,
    (χ.decode _).get h' = h.t ∧
    (σ.cond ⟨(S.cpos _).get hN, A⟩).get (cpos_dom ⟨A, inr N⟩ hN) =
    SpecCondition.inflexible_coe h.path.hδ h.path.hε h.path.hδε h.path.B χ
  inflexible_bot_spec (A : ExtendedIndex β) (N : NearLitter) (hN : ⟨A, inr N⟩ ∈ S)
    (h : InflexibleBot A N.1) (ha : ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩ ∈ S) :
    (σ.cond ⟨(S.cpos _).get hN, A⟩).get (cpos_dom ⟨A, inr N⟩ hN) =
    SpecCondition.inflexible_bot h.path.hε h.path.B
      ⟨(S.cpos _).get ha, h.path.B.cons (bot_lt_coe _)⟩

end ConNF
