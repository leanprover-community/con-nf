import phase0.support
import mathlib.with_bot

/-!
# Phase 1 of the recursion

This file contains the induction hypothesis for the first phase of the recursion. In this phase at
level `α`, we assume phase 1 at all levels `β < α`, but we do not assume any interaction between the
levels. Interaction will be introduced in phase 2.

## Main declarations

* `con_nf.core_tangle_data`:
* `con_nf.positioned_tangle_data`:
* `con_nf.almost_tangle_data`:
* `con_nf.tangle_data`: The data for the first phase of the recursion.
-/

open function set with_bot

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

section define_tangle_data

/-- The motor of the initial recursion. This contains the data of tangles and allowable permutations
for phase 1 of the recursion. -/
class core_tangle_data (α : type_index) :=
(tangle allowable : Type u)
[allowable_group : group allowable]
(allowable_to_struct_perm : allowable →* struct_perm α)
[allowable_action : mul_action allowable tangle]
(designated_support : by { haveI : mul_action allowable (support_condition α) :=
  mul_action.comp_hom _ allowable_to_struct_perm, exact Π t : tangle, small_support α allowable t })

export core_tangle_data (tangle allowable allowable_to_struct_perm designated_support)
attribute [instance] core_tangle_data.allowable_group core_tangle_data.allowable_action

section
variables (α : type_index) [core_tangle_data α]

/-- Nonempty sets of tangles. -/
abbreviation tangles : Type u := {s : set (tangle α) // s.nonempty}

variables {α} {X : Type*} [mul_action (struct_perm α) X]

instance : mul_action (allowable α) X := mul_action.comp_hom _ allowable_to_struct_perm

@[simp] lemma allowable_to_struct_perm_smul (f : allowable α) (x : X) :
  allowable_to_struct_perm f • x = f • x := rfl

end

/-- The motor of the initial recursion. This contains the data of the position function. -/
class positioned_tangle_data (α : type_index) [core : core_tangle_data α] :=
(position : tangle α ↪ μ)

export positioned_tangle_data (position)

variables (α : Λ) [core_tangle_data α]

/-- The motor of the initial recursion. This contains the data of the injection to  all the information needed for phase 1 of the
recursion. Note that this is slightly different to the blueprint's formulation; here, we keep phase
1 data *cumulatively*, for all previous iterations of the recursion at once. -/
class almost_tangle_data :=
(to_tangle : near_litter ↪ tangle α)
(smul_to_tangle : Π (π : allowable α) N, π • to_tangle N = to_tangle (π • N))
(pretangle_inj : tangle α ↪ pretangle α)
(smul_pretangle_inj : Π (π : allowable α) (t : tangle α),
  π • pretangle_inj t = pretangle_inj (π • t))
(typed_singleton : atom ↪ tangle α)

export almost_tangle_data (to_tangle typed_singleton)

variables [almost_tangle_data α] [positioned_tangle_data α]

/-- The motor of the initial recursion. This contains all the information needed for phase 1 of the
recursion. -/
class tangle_data :=
(litter_lt : Π (L : litter) (a ∈ litter_set L),
  position (to_tangle L.to_near_litter : tangle α) < position (typed_singleton a : tangle α))
(litter_lt_near_litter : Π (N : near_litter),
  position (to_tangle N.fst.to_near_litter : tangle α) ≤ position (to_tangle N : tangle α))
(symm_diff_lt_near_litter : Π (N : near_litter) (a ∈ litter_set N.fst ∆ N.snd),
  position (typed_singleton a : tangle α) < position (to_tangle N : tangle α))
(support_le : Π (t : tangle α) (c : support_condition α) (hc : c ∈ designated_support t)
  (not_singleton : ∀ a, t ≠ typed_singleton a)
  (not_near_litter : ∀ (L : litter), t ≠ to_tangle L.to_near_litter),
  position (c.fst.elim (typed_singleton) (to_tangle) : tangle α) ≤ position t)

/-- The type of tangles that we assume were constructed at stage `α`.
Later in the recursion, we will construct this type explicitly, but for now, we will just assume
that it exists.
Fields in `tangle_data` give more information about this type. -/
add_decl_doc core_tangle_data.tangle

/-- The type of allowable permutations that we assume exists on `α`-tangles.
This is given as a plain type, its action on `α`-tangles is given by `allowable_action`. -/
add_decl_doc core_tangle_data.allowable

/-- The type of allowable permutations at level `α` forms a group with respect to function
composition. Note that at this stage in the recursion, we have not established that the allowable
permutations on `α`-tangles are actually (coercible to) functions, so we cannot compose them with
the `∘` symbol; we must instead use group multiplication `*`. -/
add_decl_doc core_tangle_data.allowable_group

/-- Allowable permutations can be considered a subtype of structural permutations. However, we
cannot write this explicitly in type theory, so instead we assume this monoid homomorphism from
allowable permutations to structural permutations. This can be thought of as an inclusion map that
preserves the group structure. This allows allowable permutations to act on pretangles. -/
add_decl_doc core_tangle_data.allowable_to_struct_perm

/-- Allowable permutations act on tangles. This action commutes with certain other operations; the
exact conditions are given in `smul_to_tangle` and `smul_pretangle_inj`. -/
add_decl_doc core_tangle_data.allowable_action

/-- For each tangle, we provide a small support for it. This is known as the designated support of
the tangle. -/
add_decl_doc core_tangle_data.designated_support

/-- An injection from near-litters into level `α` tangles.
These will be explicitly constructed as "typed near-litters", which are codes of the form
`(α, -1, N)` for `N` a near-litter.

Since we haven't assumed anything about the structure of tangles at this level, we can't construct
these typed near-litters explicitly, so we rely on this function instead. In the blueprint, this is
function `j`. -/
add_decl_doc almost_tangle_data.to_tangle

/-- The action of allowable permutations on tangles commutes with the `to_tangle` function mapping
near-litters to typed near-litters. This is quite clear to see when representing tangles as codes,
but since at this stage tangles are just a type, we have to state this condition explicitly. -/
add_decl_doc almost_tangle_data.smul_to_tangle

/-- Tangles can be considered a subtype of pretangles, which are tangles without extensionality and
which are guaranteed to have a `-1`-extension. This injection can be seen as an inclusion map.
Since pretangles have a membership relation, we can use this map to see the members of a tangle at
any given level, by first converting it to a pretangle. -/
add_decl_doc almost_tangle_data.pretangle_inj

/-- The action of allowable permutations on tangles commutes with the `pretangle_inj` injection
converting tangles into pretangles. -/
add_decl_doc almost_tangle_data.smul_pretangle_inj

/-- For any atom `a`, we can construct an `α`-tangle that has a `-1`-extension that contains exactly
this atom. This is called a typed singleton. In the blueprint, this is the function `k`. -/
add_decl_doc almost_tangle_data.typed_singleton

/-- An injection from level `α` tangles into the type `μ`.
Since `μ` has a well-ordering, this induces a well-ordering on `α`-tangles: to compare two tangles,
simply compare their images under this map.

Conditions satisfied by this injection are given in `litter_lt`, `litter_lt_near_litter`,
`symm_diff_lt_near_litter`, and `support_le`. In the blueprint, this is function `ι`. -/
add_decl_doc positioned_tangle_data.position

/-- Each typed litter `L` precedes the typed singletons of all of its elements `a ∈ L`. -/
add_decl_doc tangle_data.litter_lt

/-- Each near litter `N` which is not a litter comes later than its associated liter `L = N°`. -/
add_decl_doc tangle_data.litter_lt_near_litter

/-- Each near litter `N` comes after all elements in the symmetric difference `N ∆ N°` (which is
a small set by construction). Note that if `N` is a litter, this condition is vacuously true. -/
add_decl_doc tangle_data.symm_diff_lt_near_litter

/-- For all tangles `t` that are not typed singletons and not typed litters, `t` comes later than
all of the support conditions in its designated support. That is, if an atom `a` is in the
designated support for `t`, then `t` lies after `a`, and if a near-litter `N` is in the designated
support for `t`, then `t` lies after `N` (under suitable maps to `μ`). -/
add_decl_doc tangle_data.support_le

end define_tangle_data

section instances
variables {α : Λ}

instance coe_Iio : has_coe_t (Iio α) (Iio (α : type_index)) := ⟨λ β, ⟨β.1, coe_lt_coe.2 β.2⟩⟩

@[simp] lemma Iio.coe_mk (β : Λ) (hβ : β < α) :
  ((⟨β, hβ⟩ : Iio α) : Iio (α : type_index)) = ⟨β, coe_lt_coe.2 hβ⟩ := rfl

lemma Iio.coe_injective : injective (coe : Iio α → Iio (α : type_index)) :=
begin
  rintro ⟨β, hβ⟩ ⟨γ, hγ⟩ h,
  simp only [Iio.coe_mk, subtype.mk_eq_mk] at h,
  have := with_bot.coe_injective h,
  subst this,
end

@[simp] lemma Iio.coe_inj {β γ : Iio α} : (β : Iio (α : type_index)) = γ ↔ β = γ :=
Iio.coe_injective.eq_iff

section bot
variables {α} {β : Λ} {hβ : (β : type_index) ∈ Iio (α : type_index)}

instance : has_bot (Iio (α : type_index)) := ⟨⟨⊥, bot_lt_coe _⟩⟩

@[simp] lemma bot_ne_mk_coe : (⊥ : Iio (α : type_index)) ≠ ⟨β, hβ⟩ :=
ne_of_apply_ne subtype.val bot_ne_coe

@[simp] lemma mk_coe_ne_bot : (⟨β, hβ⟩ : Iio (α : type_index)) ≠ ⊥ :=
ne_of_apply_ne subtype.val coe_ne_bot

end bot

variables (β : Iio α) [core_tangle_data (β : Iio (α : type_index))]

instance core_val : core_tangle_data β.val := ‹core_tangle_data β›
instance core_coe_coe : core_tangle_data (β : Λ) := ‹core_tangle_data β›

section positioned_tangle_data
variables [positioned_tangle_data (β : Iio (α : type_index))]

instance positioned_val : positioned_tangle_data β.val := ‹positioned_tangle_data _›
instance positioned_coe_coe : positioned_tangle_data (β : Λ) := ‹positioned_tangle_data _›

end positioned_tangle_data

variables [almost_tangle_data β]

instance almost_val : almost_tangle_data β.val := ‹almost_tangle_data β›

end instances

/-- The tangle data at level `⊥` is constructed by taking the tangles to be the atoms, the allowable
permutations to be near-litter-permutations, and the designated supports to be singletons. -/
instance bot.core_tangle_data : core_tangle_data ⊥ :=
{ tangle := atom,
  allowable := near_litter_perm,
  allowable_to_struct_perm := struct_perm.to_bot_iso.to_monoid_hom,
  allowable_action := infer_instance,
  designated_support := λ a,
    { carrier := {to_condition (sum.inl a, quiver.path.nil)},
      supports := λ π, by simp only [mem_singleton_iff, has_smul.comp.smul,
        mul_equiv.coe_to_monoid_hom, struct_perm.coe_to_bot_iso, equiv.to_fun_as_coe,
        forall_eq, struct_perm.smul_to_condition, struct_perm.derivative_nil,
        struct_perm.to_bot_smul, sum.smul_inl, embedding_like.apply_eq_iff_eq, prod.mk.inj_iff,
        eq_self_iff_true, and_true, imp_self],
      small := small_singleton _ } }

/-- The tangle data at the bottom level. -/
def bot.positioned_tangle_data : positioned_tangle_data ⊥ := ⟨nonempty.some mk_atom.le⟩

variables (α : Λ)

/-- The core tangle data below phase `α`. -/
class core_tangle_cumul (α : Λ) := (data : Π β : Iio α, core_tangle_data β)

section core_tangle_cumul
variables [core_tangle_cumul α]

instance core_tangle_cumul.to_core_tangle_data : Π β : Iio (α : type_index), core_tangle_data β
| ⟨⊥, h⟩ := bot.core_tangle_data
| ⟨(β : Λ), hβ⟩ := core_tangle_cumul.data ⟨β, coe_lt_coe.1 hβ⟩

instance core_tangle_cumul.to_core_tangle_data' (β : Iio α) : core_tangle_data β :=
show core_tangle_data (β : Iio (α : type_index)), by apply_instance

end core_tangle_cumul

/-- The positioned tangle data below phase `α`. -/
class positioned_tangle_cumul (α : Λ) [core_tangle_cumul α] :=
(data : Π β : Iio α, positioned_tangle_data β)

section positioned_tangle_cumul
variables [core_tangle_cumul α] [positioned_tangle_cumul α]

instance positioned_tangle_cumul.to_positioned_tangle_data :
  Π β : Iio (α : type_index), positioned_tangle_data β
| ⟨⊥, h⟩ := bot.positioned_tangle_data
| ⟨(β : Λ), hβ⟩ := positioned_tangle_cumul.data ⟨β, coe_lt_coe.1 hβ⟩

instance positioned_tangle_cumul.to_positioned_tangle_data' (β : Iio α) :
  positioned_tangle_data β :=
show positioned_tangle_data (β : Iio (α : type_index)), by apply_instance

end positioned_tangle_cumul

/-- The almost tangle data below phase `α`. -/
abbreviation almost_tangle_cumul (α : Λ) [core_tangle_cumul α] := Π β : Iio α, almost_tangle_data β

/-- The tangle data below phase `α`. -/
abbreviation tangle_cumul (α : Λ) [core_tangle_cumul α] [positioned_tangle_cumul α]
  [almost_tangle_cumul α] :=
Π β : Iio α, tangle_data β

end con_nf
