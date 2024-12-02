import ConNF.Construction.Hailperin

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal ConNF.TSet

namespace ConNF

variable [Params.{u}] {α β γ δ ε ζ : Λ} (hβ : (β : TypeIndex) < α) (hγ : (γ : TypeIndex) < β)
  (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < δ) (hζ : (ζ : TypeIndex) < ε)

theorem ext (x y : TSet α) :
    (∀ z : TSet β, z ∈[hβ] x ↔ z ∈[hβ] y) → x = y :=
  tSet_ext' hβ x y

theorem exists_inter (x y : TSet α) :
    ∃ w : TSet α, ∀ z : TSet β, z ∈[hβ] w ↔ z ∈[hβ] x ∧ z ∈[hβ] y :=
  TSet.exists_inter hβ x y

theorem exists_compl (x : TSet α) :
    ∃ y : TSet α, ∀ z : TSet β, z ∈[hβ] y ↔ ¬z ∈[hβ] x :=
  TSet.exists_compl hβ x

theorem mem_singleton_iff (x y : TSet β) :
    y ∈[hβ] singleton hβ x ↔ y = x :=
  typedMem_singleton_iff' hβ x y

theorem mem_up_iff (x y z : TSet β) :
    z ∈[hβ] up hβ x y ↔ z = x ∨ z = y :=
  TSet.mem_up_iff hβ x y z

theorem op_def (x y : TSet γ) :
    op hβ hγ x y = up hβ (singleton hγ x) (up hγ x y) :=
  rfl

theorem exists_singletonImage (x : TSet β) :
    ∃ y : TSet α, ∀ z w,
    op hγ hδ (singleton hε z) (singleton hε w) ∈[hβ] y ↔ op hδ hε z w ∈[hγ] x :=
  TSet.exists_singletonImage hβ hγ hδ hε x

theorem exists_insertion2 (x : TSet γ) :
    ∃ y : TSet α, ∀ a b c, op hγ hδ (singleton hε (singleton hζ a)) (op hε hζ b c) ∈[hβ] y ↔
    op hε hζ a c ∈[hδ] x :=
  TSet.exists_insertion2 hβ hγ hδ hε hζ x

theorem exists_insertion3 (x : TSet γ) :
    ∃ y : TSet α, ∀ a b c, op hγ hδ (singleton hε (singleton hζ a)) (op hε hζ b c) ∈[hβ] y ↔
    op hε hζ a b ∈[hδ] x :=
  TSet.exists_insertion3 hβ hγ hδ hε hζ x

theorem exists_cross (x : TSet γ) :
    ∃ y : TSet α, ∀ a, a ∈[hβ] y ↔ ∃ b c, a = op hγ hδ b c ∧ c ∈[hδ] x :=
  TSet.exists_cross hβ hγ hδ x

theorem exists_typeLower (x : TSet α) :
    ∃ y : TSet δ, ∀ a, a ∈[hε] y ↔ ∀ b, op hγ hδ b (singleton hε a) ∈[hβ] x :=
  TSet.exists_typeLower hβ hγ hδ hε x

theorem exists_converse (x : TSet α) :
    ∃ y : TSet α, ∀ a b, op hγ hδ a b ∈[hβ] y ↔ op hγ hδ b a ∈[hβ] x :=
  TSet.exists_converse hβ hγ hδ x

theorem exists_cardinalOne :
    ∃ x : TSet α, ∀ a : TSet β, a ∈[hβ] x ↔ ∃ b, ∀ c : TSet γ, c ∈[hγ] a ↔ c = b :=
  TSet.exists_cardinalOne hβ hγ

theorem exists_subset :
    ∃ x : TSet α, ∀ a b, op hγ hδ a b ∈[hβ] x ↔ ∀ c : TSet ε, c ∈[hε] a → c ∈[hε] b :=
  TSet.exists_subset hβ hγ hδ hε

end ConNF
