import Mathlib.Combinatorics.Quiver.Path
import ConNF.Atom.Params

open Cardinal Function Quiver Quiver.Path Set WithBot

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}]

section IioIic

variable {α β : Λ}

abbrev IioBot (α : Λ) :=
  Iio (α : TypeIndex)

abbrev IicBot (α : Λ) :=
  Iic (α : TypeIndex)

@[simp]
lemma _root_.Set.Iio.lt (β : Iio α) : (β : Λ) < α := β.prop

@[simp]
lemma _root_.Set.Iic.le (β : Iic α) : (β : Λ) ≤ α := β.prop

@[simp]
lemma IioBot.lt (β : IioBot α) : (β : TypeIndex) < α := β.prop

@[simp]
lemma IicBot.le (β : IicBot α) : (β : TypeIndex) ≤ α := β.prop

instance coeIioIic : CoeTC (Iio α) (Iic α) :=
  ⟨fun β => ⟨β.1, le_of_lt (show β < α from β.2)⟩⟩

instance coeIio : CoeTC (Iio α) (IioBot α) :=
  ⟨fun β => ⟨β.1, coe_lt_coe.2 β.2⟩⟩

instance coeIic : CoeTC (Iic α) (IicBot α) :=
  ⟨fun β => ⟨β.1, coe_le_coe.2 β.2⟩⟩

abbrev iioCoe : Iio α → IioBot α :=
  coeIio.coe

abbrev iicCoe : Iic α → IicBot α :=
  coeIic.coe

@[simp]
theorem Iio.coe_mk (β : Λ) (hβ : β < α) : ((⟨β, hβ⟩ : Iio α) : IioBot α) = ⟨β, coe_lt_coe.2 hβ⟩ :=
  rfl

@[simp]
theorem Iic.coe_mk (β : Λ) (hβ : β ≤ α) : ((⟨β, hβ⟩ : Iic α) : IicBot α) = ⟨β, coe_le_coe.2 hβ⟩ :=
  rfl

theorem Iio.coe_injective : Injective (show Iio α → IioBot α from CoeTC.coe) := by
  rintro ⟨β, hβ⟩ ⟨γ, hγ⟩ h
  cases h
  rfl

theorem Iic.coe_injective : Injective (show Iic α → IicBot α from CoeTC.coe) := by
  rintro ⟨β, hβ⟩ ⟨γ, hγ⟩ h
  cases h
  rfl

@[simp]
theorem Iio.coe_inj {β γ : Iio α} : iioCoe β = γ ↔ β = γ :=
  Iio.coe_injective.eq_iff

@[simp]
theorem Iic.coe_inj {β γ : Iic α} : iicCoe β = γ ↔ β = γ :=
  Iic.coe_injective.eq_iff

section IioIndex

variable {hβ : (β : TypeIndex) ∈ IioBot α}

instance : Bot (IioBot α) :=
  ⟨⟨⊥, bot_lt_coe _⟩⟩

instance : Inhabited (IioBot α) :=
  ⟨⊥⟩

@[simp]
theorem IioBot.bot_ne_mk_coe : (⊥ : IioBot α) ≠ ⟨β, hβ⟩ :=
  ne_of_apply_ne Subtype.val WithBot.bot_ne_coe

@[simp]
theorem IioBot.mk_coe_ne_bot : (⟨β, hβ⟩ : IioBot α) ≠ ⊥ :=
  ne_of_apply_ne Subtype.val WithBot.coe_ne_bot

@[simp]
theorem IioBot.bot_ne_coe {β : Iio α} : ⊥ ≠ (β : IioBot α) :=
  ne_of_apply_ne Subtype.val WithBot.bot_ne_coe

@[simp]
theorem IioBot.coe_ne_bot {β : Iio α} : (β : IioBot α) ≠ ⊥ :=
  ne_of_apply_ne Subtype.val WithBot.coe_ne_bot

end IioIndex

section IicIndex

variable {hβ : (β : TypeIndex) ∈ IicBot α}

instance : Bot (IicBot α) :=
  ⟨⟨⊥, bot_le (a := (α : TypeIndex))⟩⟩

instance : Inhabited (IicBot α) :=
  ⟨⊥⟩

@[simp]
theorem IicBot.bot_ne_mk_coe : (⊥ : IicBot α) ≠ ⟨β, hβ⟩ :=
  ne_of_apply_ne Subtype.val bot_ne_coe

@[simp]
theorem IicBot.mk_coe_ne_bot : (⟨β, hβ⟩ : IicBot α) ≠ ⊥ :=
  ne_of_apply_ne Subtype.val coe_ne_bot

end IicIndex

end IioIic

variable {α : TypeIndex}

/-- We define the type of paths from certain types to lower types as elements of this quiver. -/
instance quiver : Quiver TypeIndex :=
  ⟨(· > ·)⟩

/-- A (finite) path from the type α to the base type.
This can be seen as a way that we can perceive extensionality, iteratively descending to lower
types in the hierarchy until we reach the base type.
This plays the role of an extended type index in the paper. -/
def ExtendedIndex (α : TypeIndex) :=
  Quiver.Path α ⊥

/-- If there is a path between `α` and `β`, we must have `β ≤ α`.
The case `β = α` can occur with the nil path. -/
theorem le_of_path : ∀ {β : TypeIndex}, Path α β → β ≤ α
  | _, nil => le_rfl
  | _, cons p f => (le_of_lt f).trans <| le_of_path p

theorem path_eq_nil : ∀ p : Path α α, p = nil
  | nil => rfl
  | cons p f => ((le_of_path p).not_lt f).elim

theorem ExtendedIndex.length_ne_zero {α : Λ} (A : ExtendedIndex α) : A.length ≠ 0 := by
  intro h
  cases Quiver.Path.eq_of_length_zero A h

/-- An induction principle for paths that allows us to use `Iic_index α` instead of needing to
define the motive for all `type_index`. -/
@[elab_as_elim]
def Path.iicRec {α : Λ} {β : IicBot α}
    {motive : ∀ γ : IicBot α, Path (β : TypeIndex) γ → Sort _} :
    motive β nil →
      (∀ (γ δ : IicBot α) (A : Path (β : TypeIndex) γ) (h : δ < γ),
          motive γ A → motive δ (A.cons h)) →
        ∀ (γ : IicBot α) (A : Path (β : TypeIndex) γ), motive γ A :=
  fun hn hc _ => Path.rec (motive := fun δ B => motive ⟨δ, (le_of_path B).trans β.prop⟩ B)
    hn (fun {δ ε} B h c => hc ⟨δ, _⟩ ⟨ε, _⟩ B h c)

@[simp]
theorem Path.iicRec_nil {α : Λ} {β : IicBot α}
    {motive : ∀ γ : IicBot α, Path (β : TypeIndex) γ → Sort _} {hn : motive β nil} {hc} :
    @Path.iicRec _ _ _ motive hn hc β nil = hn :=
  rfl

@[simp]
theorem Path.iicRec_cons {α : Λ} {β : IicBot α}
    {motive : ∀ γ : IicBot α, Path (β : TypeIndex) γ → Sort _} {hn : motive β nil} {hc}
    (γ δ : IicBot α) (A : Path (β : TypeIndex) γ) (h : δ < γ) :
    @Path.iicRec _ _ _ motive hn hc δ (A.cons h) = hc γ δ A h (Path.iicRec hn hc γ A) :=
  rfl

/-- There are at most `Λ` `α`-extended type indices. -/
@[simp]
theorem mk_extendedIndex (α : TypeIndex) : #(ExtendedIndex α) ≤ (#Λ) := by
  refine le_trans ((Cardinal.le_def _ _).2 ⟨⟨toList, toList_injective (α : TypeIndex) ⊥⟩⟩) ?_
  convert mk_list_le_max _ using 1
  simp only [mk_typeIndex, max_eq_right, aleph0_le_mk]

/-- If `β < γ`, we have a path directly between the two types in the opposite order.
Note that the `⟶` symbol (long right arrow) is not the normal `→` (right arrow),
even though monospace fonts often display them similarly. -/
instance ltToHom (β γ : Λ) : Coe (β < γ) ((γ : TypeIndex) ⟶ β) :=
  ⟨coe_lt_coe.2⟩

instance : (α : TypeIndex) → Inhabited (ExtendedIndex α)
  | ⊥ => ⟨nil⟩
  | (α : Λ) => ⟨Hom.toPath <| WithBot.bot_lt_coe α⟩

/-- There exists an `α`-extended type index. --/
theorem mk_extendedIndex_ne_zero (α : TypeIndex) : #(ExtendedIndex α) ≠ 0 :=
  Cardinal.mk_ne_zero _

end ConNF
