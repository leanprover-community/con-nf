module

public import ConNF.Model.Hailperin

@[expose] public noncomputable section

universe u

open Cardinal Ordinal ConNF.TSet

namespace ConNF

variable [Params.{u}] {α β γ δ ε ζ : Λ} (hβ : (β : TypeIndex) < α) (hγ : (γ : TypeIndex) < β)
  (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < δ) (hζ : (ζ : TypeIndex) < ε)

theorem ext (x y : TSet α) :
    (∀ z : TSet β, z ∈' x ↔ z ∈' y) → x = y :=
  tSet_ext' hβ x y

theorem ext_iff (x y : TSet α) :
    (∀ z : TSet β, z ∈' x ↔ z ∈' y) ↔ x = y :=
  ⟨ext hβ x y, λ h _ ↦ iff_of_eq (congr_arg _ h)⟩

def inter (x y : TSet α) : TSet α :=
  (TSet.exists_inter hβ x y).choose

notation:69 x:69 " ⊓[" h "] " y:69 => ConNF.inter h x y
notation:69 x:69 " ⊓[" l "] " y:69 => ConNF.inter (β := l) (by assumption) x y

@[simp]
theorem mem_inter_iff (x y : TSet α) :
    ∀ z : TSet β, z ∈' x ⊓[β] y ↔ z ∈' x ∧ z ∈' y :=
  (TSet.exists_inter hβ x y).choose_spec

def compl (x : TSet α) : TSet α :=
  (TSet.exists_compl hβ x).choose

notation:1024 x:1024 " ᶜ[" h "]" => _root_.ConNF.compl h x
notation:1024 x:1024 " ᶜ[" l "]" => ConNF.compl (β := l) (by assumption) x

@[simp]
theorem mem_compl_iff (x : TSet α) :
    ∀ z : TSet β, z ∈' xᶜ[β] ↔ ¬z ∈' x :=
  (TSet.exists_compl hβ x).choose_spec

notation:1024 "{" x "}[" h "]" => _root_.ConNF.singleton h x
notation:1024 "{" x "}[" u "]" => ConNF.singleton (α := u) (by assumption) x

@[simp]
theorem mem_singleton_iff (x y : TSet β) :
    y ∈' {x}[α] ↔ y = x :=
  typedMem_singleton_iff' hβ x y

notation:1024 "{" x ", " y "}[" h "]" => _root_.ConNF.TSet.up h x y
notation:1024 "{" x ", " y "}[" u "]" => ConNF.TSet.up (α := u) (by assumption) x y

@[simp]
theorem mem_up_iff (x y z : TSet β) :
    z ∈' {x, y}[α] ↔ z = x ∨ z = y :=
  TSet.mem_up_iff hβ x y z

notation:1024 "⟨" x ", " y "⟩[" h ", " h' "]" => _root_.ConNF.TSet.op h h' x y
notation:1024 "⟨" x ", " y "⟩[" u ", " m "]" =>
  ConNF.TSet.op (α := u) (β := m) (by assumption) (by assumption) x y

theorem op_def (x y : TSet γ) :
    (⟨x, y⟩[α, β] : TSet α) = {{x}[β], {x, y}[β]}[α] :=
  rfl

def singletonImage' (x : TSet β) : TSet α :=
  (TSet.exists_singletonImage hβ hγ hδ hε x).choose

@[simp]
theorem singletonImage'_spec (x : TSet β) :
    ∀ z w : TSet ε,
    ⟨{z}[δ], {w}[δ]⟩[β, γ] ∈' singletonImage' hβ hγ hδ hε x ↔ ⟨z, w⟩[γ, δ] ∈' x :=
  (TSet.exists_singletonImage hβ hγ hδ hε x).choose_spec

def insertion2' (x : TSet γ) : TSet α :=
  (TSet.exists_insertion2 hβ hγ hδ hε hζ x).choose

@[simp]
theorem insertion2'_spec (x : TSet γ) :
    ∀ a b c : TSet ζ, ⟨{{a}[ε]}[δ], ⟨b, c⟩[δ, ε]⟩[β, γ] ∈' insertion2' hβ hγ hδ hε hζ x ↔
    ⟨a, c⟩[δ, ε] ∈' x :=
  (TSet.exists_insertion2 hβ hγ hδ hε hζ x).choose_spec

def insertion3' (x : TSet γ) : TSet α :=
  (TSet.exists_insertion3 hβ hγ hδ hε hζ x).choose

theorem insertion3'_spec (x : TSet γ) :
    ∀ a b c : TSet ζ, ⟨{{a}[ε]}[δ], ⟨b, c⟩[δ, ε]⟩[β, γ] ∈' insertion3' hβ hγ hδ hε hζ x ↔
    ⟨a, b⟩[δ, ε] ∈' x :=
  (TSet.exists_insertion3 hβ hγ hδ hε hζ x).choose_spec

def vCross (x : TSet γ) : TSet α :=
  (TSet.exists_cross hβ hγ hδ x).choose

@[simp]
theorem mem_vCross_iff (x : TSet γ) :
    ∀ a : TSet β, a ∈' vCross hβ hγ hδ x ↔ ∃ b c : TSet δ, a = ⟨b, c⟩[β, γ] ∧ c ∈' x :=
  (TSet.exists_cross hβ hγ hδ x).choose_spec

def typeLower (x : TSet α) : TSet δ :=
  (TSet.exists_typeLower hβ hγ hδ hε x).choose

@[simp]
theorem mem_typeLower_iff (x : TSet α) :
    ∀ a : TSet ε, a ∈' typeLower hβ hγ hδ hε x ↔ ∀ b : TSet δ, ⟨b, {a}[δ]⟩[β, γ] ∈' x :=
  (TSet.exists_typeLower hβ hγ hδ hε x).choose_spec

def converse' (x : TSet α) : TSet α :=
  (TSet.exists_converse hβ hγ hδ x).choose

@[simp]
theorem converse'_spec (x : TSet α) :
    ∀ a b : TSet δ, ⟨a, b⟩[β, γ] ∈' converse' hβ hγ hδ x ↔ ⟨b, a⟩[β, γ] ∈' x :=
  (TSet.exists_converse hβ hγ hδ x).choose_spec

def cardinalOne : TSet α :=
  (TSet.exists_cardinalOne hβ hγ).choose

@[simp]
theorem mem_cardinalOne_iff :
    ∀ a : TSet β, a ∈' cardinalOne hβ hγ ↔ ∃ b : TSet γ, a = {b}[β] :=
  (TSet.exists_cardinalOne hβ hγ).choose_spec

def subset' : TSet α :=
  (TSet.exists_subset hβ hγ hδ hε).choose

theorem subset'_spec :
    ∀ a b : TSet δ, ⟨a, b⟩[β, γ] ∈' subset' hβ hγ hδ hε ↔ a ⊆[TSet ε] b :=
  (TSet.exists_subset hβ hγ hδ hε).choose_spec

end ConNF
