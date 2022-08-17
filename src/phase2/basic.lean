import phase1.f_map

open function set with_bot quiver
open_locale pointwise

/-!
# Typeclasses for phase 2

We now proceed to make some assumptions that will be held throughout phase 2.
We assume:

* core tangle data at all `le_index α`;
* positioned tangle data at all `lt_index α`;
* full tangle data at all `proper_lt_index α`.

Note that:

* There is a trivial `le_index` path `α ⟶ α`, which means that we have core tangle data at `α`.
    This is precisely what we have constructed in phase 1 of the recursion.
* Positioned tangle data exists at all type indices `β < α` (which may be different depending on the
    path taken from `α` down to `β` a priori), which notably includes the base type `-1`/`⊥`.
    This allows us to talk about f-maps and other things that require the position function without
    having to construct full tangle data for the base type `-1`/`⊥`.

In order to have positioned (or full) tangle data at a given `lt_index` (or `proper_lt_index`) we
must first have constructed the previous tangle data components. By parametrising all of the
`*_tangle_data` classes with their predecessors, we can get definitional equality and avoid diamonds
almost for free. We simply provide some instances which give

* core tangle data at all `lt_index α`;
* core tangle data at all `proper_lt_index α`;
* positioned tangle data at all `proper_lt_index α`.

These instances can obviously be satisfied using the natural coercions between the index types
above, and they can be accessed easily through typeclass resolution.

The only downside (that I can see!) to this approach is that we need to define our assumptions class
in several steps so that we can write the relevant instances between writing all of our assumptions.
-/

noncomputable theory

universe u

namespace con_nf
variables [params.{u}] (α : Λ)

section

/-- We assume core tangle data for all type indices less than (or equal to) `α`, along all paths. -/
class phase_2_core_assumptions :=
[lower_core_tangle_data : Π (A : le_index α), core_tangle_data A.index]

/-! Make the core tangle data accessible as an instance for all `le_index α`. -/
attribute [instance] phase_2_core_assumptions.lower_core_tangle_data

variable [phase_2_core_assumptions α]

/-! We now take the core tangle data that we just assumed exists, and make it accessible under
all possible different names. This allows lean's typeclass inference to easily find all the required
instances in many cases. -/

/-! Make the core tangle data accessible as an instance for all `lt_index α`. -/
instance lt_index_core_tangle_data (A : lt_index α) : core_tangle_data A.index :=
phase_2_core_assumptions.lower_core_tangle_data (A : le_index α)

/-! Make the core tangle data accessible as an instance for all `lt_index α`,
where the index is accessed through the coercion to `le_index`. -/
instance lt_index_coe_core_tangle_data (A : lt_index α) : core_tangle_data (A : le_index α).index :=
phase_2_core_assumptions.lower_core_tangle_data (A : le_index α)

/-! Make the core tangle data accessible as an instance for all `proper_lt_index α`. -/
instance proper_lt_index_core_tangle_data (A : proper_lt_index α) : core_tangle_data A.index :=
phase_2_core_assumptions.lower_core_tangle_data (A : le_index α)

/-! Make the core tangle data accessible as an instance for all `proper_lt_index α`,
where the index is accessed through the coercion to `lt_index`. -/
instance proper_lt_index_coe_core_tangle_data (A : proper_lt_index α) :
  core_tangle_data (A : lt_index α).index :=
phase_2_core_assumptions.lower_core_tangle_data (A : le_index α)

/-! Make the core tangle data accessible as an instance for all `proper_lt_index α`,
where the index is accessed through the coercion to `le_index`. -/
instance proper_lt_index_coe_coe_core_tangle_data (A : proper_lt_index α) :
  core_tangle_data (A : le_index α).index :=
phase_2_core_assumptions.lower_core_tangle_data (A : le_index α)

instance allowable_action_lt (A : le_index α) {β : type_index} (hβ : β < A) :
mul_action (allowable (A.cons hβ).index) (tangle (lt_index.mk' hβ A.path).index) :=
core_tangle_data.allowable_action

/-- We assume positioned tangle data for all type indices strictly less than `α`,
along all paths. -/
class phase_2_positioned_assumptions :=
[lower_positioned_tangle_data : Π (A : lt_index α), positioned_tangle_data A.index]

/-! Make the positioned tangle data accessible as an instance for all `lt_index α`. -/
attribute [instance] phase_2_positioned_assumptions.lower_positioned_tangle_data

variable [phase_2_positioned_assumptions α]

/-! We now take the positioned tangle data that we just assumed exists, and make it accessible under
all possible different names. This allows lean's typeclass inference to easily find all the required
instances in many cases. -/

/-! Make the positioned tangle data accessible as an instance for all `lt_index α`. -/
instance lt_index_positioned_tangle_data (A : lt_index α) : positioned_tangle_data A.index :=
phase_2_positioned_assumptions.lower_positioned_tangle_data A

/-! Make the positioned tangle data accessible as an instance for all `lt_index α`,
where the index is accessed through the coercion to `le_index`. -/
instance lt_index_coe_positioned_tangle_data (A : lt_index α) :
  positioned_tangle_data (A : le_index α).index :=
phase_2_positioned_assumptions.lower_positioned_tangle_data A

/-! Make the positioned tangle data accessible as an instance for all `proper_lt_index α`. -/
instance proper_lt_index_positioned_tangle_data (A : proper_lt_index α) :
  positioned_tangle_data A.index :=
phase_2_positioned_assumptions.lower_positioned_tangle_data (A : lt_index α)

/-! Make the positioned tangle data accessible as an instance for all `proper_lt_index α`,
where the index is accessed through the coercion to `lt_index`. -/
instance proper_lt_index_coe_positioned_tangle_data (A : proper_lt_index α) :
  positioned_tangle_data (A : lt_index α).index :=
phase_2_positioned_assumptions.lower_positioned_tangle_data (A : lt_index α)

/-! Make the positioned tangle data accessible as an instance for all `proper_lt_index α`,
where the index is accessed through the coercion to `le_index`. -/
instance proper_lt_index_coe_coe_positioned_tangle_data (A : proper_lt_index α) :
  positioned_tangle_data (A : le_index α).index :=
phase_2_positioned_assumptions.lower_positioned_tangle_data (A : lt_index α)

/-- Along with `phase_2_core_assumptions` and `phase_2_positioned_assumptions`, this is the class
containing the assumptions we take for phase 2 of the recursion. In this class, we assume full
tangle data for all proper type indices `β < α` along all paths. -/
class phase_2_assumptions [typed_positions] :=
[lower_almost_tangle_data : Π (A : proper_lt_index α), almost_tangle_data A.index]
[lower_tangle_data : Π (A : proper_lt_index α), tangle_data A.index]
(allowable_derivative : Π (A : le_index α) {γ : type_index} (hγ : γ < A.index),
  allowable A.index → allowable (A.cons hγ).index)
(allowable_derivative_comm : Π (A : le_index α) {γ : type_index} (hγ : γ < A.index)
  (π : allowable A.index),
  (allowable_derivative A hγ π).to_struct_perm =
    struct_perm.derivative (path.cons path.nil hγ) π.to_struct_perm)
(smul_f_map {β : Λ} (A : path (α : type_index) β) {γ : type_index} {δ : Λ}
  (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  (π : allowable (le_index.mk β A).index) (t : tangle (lt_index.mk' hγ A).index) :
  (allowable_derivative (le_index.mk β A) (coe_lt_coe.mpr hδ) π) •
    f_map (proper_lt_index.mk' hδ A).index t =
    f_map (proper_lt_index.mk' hδ A).index (allowable_derivative ⟨β, A⟩ hγ π • t))

/-- The derivative of a permutation along a particular path.
Note that `allowable (A.cons hγ).index` is defeq to `allowable γ`, but by writing it in this form,
lean's typeclass resolution can find the particular instance of `core_tangle_data` that we want. -/
add_decl_doc phase_2_assumptions.allowable_derivative

/-- The derivative map commutes with the map from allowable to structural permutations.
The term `path.cons path.nil hγ` is the singleton path `A.index ⟶ γ`.
TODO: Should we refactor `struct_perm.derivative` to use singleton paths as well? -/
add_decl_doc phase_2_assumptions.allowable_derivative_comm

/-- The unpacked coherence condition. -/
add_decl_doc phase_2_assumptions.smul_f_map

attribute [instance]
  phase_2_assumptions.lower_almost_tangle_data
  phase_2_assumptions.lower_tangle_data

end

variables {α}

/-! There are no additional names that could be used to refer to the instances
`lower_almost_tangle_data` and `lower_tangle_data`, so no new instances need to be defined here. -/

/-!
We can now proceed to define API for the phase 1 constructs in terms of our new types.
Typeclass inference should behave a lot nicer with the utility instances constructed above.
Because of how the instances are all parametrised, all suitable instances of defeq things should
also be defeq to each other.
-/

instance (A : le_index α) : mul_action (struct_perm A.index) (support_condition A) :=
struct_perm.mul_action_support_condition

variables [phase_2_core_assumptions α]

/-- The type of tangles indexed by a path. This is a type synonym of `tangle`. -/
@[nolint has_nonempty_instance] def tangle_path (A : le_index α) : Type u := tangle A.index

/-- The equivalence between tangles accessed via different, equal, paths. Many functions, such as
`f_map_path`, are invariant under this map. -/
def tangle_path.lt_index_assoc {β γ δ ε : type_index} {A : path (α : type_index) β}
  {B : path β γ} {C : path γ δ} {h : ε < δ} :
  tangle_path (lt_index.mk' h ((A.comp B).comp C) : le_index α) ≃
  tangle_path (lt_index.mk' h (A.comp (B.comp C)) : le_index α) :=
equiv.cast (by rw path.comp_assoc)

lemma tangle_path.lt_index_assoc.heq {β γ δ ε : type_index} {A : path (α : type_index) β}
  {B : path β γ} {C : path γ δ} {h : ε < δ}
  (t : tangle_path (lt_index.mk' h ((A.comp B).comp C) : le_index α)) :
  t.lt_index_assoc == t :=
by simp only [tangle_path.lt_index_assoc, equiv.cast_apply, cast_heq]

/-- The type of allowable permutations indexed by a path. This is a type synonym of `allowable`. -/
def allowable_path (A : le_index α) : Type u := allowable A.index

/-- The equivalence between allowable permutations accessed via different, equal, paths.
Many operations, such as scalar multiplication on tangles and support conditions, are invariant
under this map. -/
def allowable_path.lt_index_assoc {β γ δ ε : type_index} {A : path (α : type_index) β}
  {B : path β γ} {C : path γ δ} {h : ε < δ} :
  allowable_path (lt_index.mk' h ((A.comp B).comp C) : le_index α) ≃
  allowable_path (lt_index.mk' h (A.comp (B.comp C)) : le_index α) :=
equiv.cast (by rw path.comp_assoc)

lemma allowable_path.lt_index_assoc.heq {β γ δ ε : type_index} {A : path (α : type_index) β}
  {B : path β γ} {C : path γ δ} {h : ε < δ}
  (π : allowable_path (lt_index.mk' h ((A.comp B).comp C) : le_index α)) :
  π.lt_index_assoc == π :=
by simp only [allowable_path.lt_index_assoc, equiv.cast_apply, cast_heq]

instance (A : le_index α) : group (allowable_path A) := allowable.group _

instance (A : le_index α) : inhabited (allowable_path A) := ⟨1⟩

/-! Utility instances to let us write things in a nicer way. -/
instance allowable_smul_le (A : le_index α) :
  mul_action (allowable_path A) (tangle_path A) := core_tangle_data.allowable_action

instance allowable_smul_lt (A : lt_index α) :
  mul_action (allowable_path (A : le_index α)) (tangle_path (A : le_index α)) :=
core_tangle_data.allowable_action

instance allowable_smul_proper_lt (A : proper_lt_index α) :
  mul_action (allowable_path (A : le_index α)) (tangle_path (A : le_index α)) :=
core_tangle_data.allowable_action

instance allowable_smul_cons {β γ : type_index} (A : path (α : type_index) β) (hγ : γ < β) :
  mul_action (allowable_path ⟨γ, A.cons hγ⟩) (tangle_path (lt_index.mk' hγ A : le_index α)) :=
core_tangle_data.allowable_action

lemma allowable_path.lt_index_assoc_smul {β γ δ ε : type_index} {A : path (α : type_index) β}
  {B : path β γ} {C : path γ δ} {h : ε < δ}
  (π : allowable_path (lt_index.mk' h ((A.comp B).comp C) : le_index α))
  (t₁ t₂ : tangle_path (lt_index.mk' h ((A.comp B).comp C) : le_index α)) :
  π.lt_index_assoc • t₁.lt_index_assoc = t₂.lt_index_assoc ↔ π • t₁ = t₂ :=
begin
  congr' 2,
  rw path.comp_assoc,
  { congr' 1,
    rw path.comp_assoc,
    rw path.comp_assoc,
    { congr' 1; rw path.comp_assoc, },
    exact allowable_path.lt_index_assoc.heq π,
    exact tangle_path.lt_index_assoc.heq t₁, },
  exact tangle_path.lt_index_assoc.heq t₂,
end

/-- The designated support of a path-indexed tangle. -/
def designated_support_path {A : le_index α} (t : tangle_path A) :
  small_support A.index (allowable_path A) t := designated_support t

namespace allowable_path
variables {A : le_index α}

/-- Reinterpret an allowable permutation as a structural permutation. -/
def to_struct_perm : allowable_path A →* struct_perm A.index := allowable.to_struct_perm

lemma to_struct_perm.lt_index_assoc {β γ δ ε : type_index} {A : path (α : type_index) β}
  {B : path β γ} {C : path γ δ} {h : ε < δ}
  (π : allowable_path (lt_index.mk' h ((A.comp B).comp C) : le_index α)) :
  π.lt_index_assoc.to_struct_perm = π.to_struct_perm :=
begin
  unfold_coes,
  congr' 1,
  rw path.comp_assoc,
  rw path.comp_assoc,
  { congr' 1, rw path.comp_assoc, },
  exact allowable_path.lt_index_assoc.heq π,
end

section
variables {X : Type*} [mul_action (struct_perm A.index) X]

instance : mul_action (allowable_path A) X := mul_action.comp_hom _ to_struct_perm

@[simp] lemma smul_to_struct_perm (π : allowable_path A) (x : X) : π.to_struct_perm • x = π • x :=
rfl

end

lemma smul_near_litter_fst (π : allowable_path A) (N : near_litter) :
  (π • N).fst = π • N.fst := rfl

lemma lt_index_assoc_smul_support_condition {β γ δ ε : type_index} {A : path (α : type_index) β}
  {B : path β γ} {C : path γ δ} {h : ε < δ}
  (π : allowable_path (lt_index.mk' h ((A.comp B).comp C) : le_index α))
  (c : support_condition ε) :
  π.lt_index_assoc • c = π • c :=
begin
  unfold has_smul.smul has_smul.comp.smul,
  obtain ⟨a | N, D⟩ := c;
  simp only [has_smul.comp.smul, struct_perm.coe_to_near_litter_perm, sum.map_inl, sum.map_inr,
    struct_perm.of_bot_smul, prod.mk.inj_iff, eq_self_iff_true,
    and_true, to_struct_perm.lt_index_assoc],
end

end allowable_path

variables [phase_2_positioned_assumptions α] [typed_positions.{}] [phase_2_assumptions α]

namespace allowable_path

/-- The derivative of a path-indexed allowable permutation. -/
def derivative : Π {A : le_index α} {γ : type_index} (hγ : γ < A.index),
  allowable_path A → allowable_path (A.cons hγ) := phase_2_assumptions.allowable_derivative

@[simp] lemma to_struct_perm_derivative : Π (A : le_index α) {γ : type_index} (hγ : γ < A.index)
  (π : allowable_path A),
  (π.derivative hγ).to_struct_perm = struct_perm.derivative (path.nil.cons hγ) π.to_struct_perm :=
phase_2_assumptions.allowable_derivative_comm

/-- Computes the derivative of an allowable permutation along a path `B`. -/
def derivative_comp (A : le_index α) :
  Π {γ : type_index} (B : path A.index γ) (π : allowable_path A),
    allowable_path ⟨γ, A.path.comp B⟩
| _ path.nil π := by { convert π, rw path.comp_nil, ext, simp }
| γ (path.cons B hγ) π := (derivative_comp B π).derivative hγ

def derivative_nil_comp {β : type_index} (B : path (α : type_index) β)
  (π : allowable_path ⟨α, path.nil⟩) : allowable_path ⟨β, B⟩ :=
by { convert derivative_comp ⟨α, path.nil⟩ B π, rw path.nil_comp }

@[simp] lemma to_struct_perm_derivative_comp : Π (A : le_index α)
  {γ : type_index} (B : path A.index γ) (π : allowable_path A),
  (π.derivative_comp _ B).to_struct_perm = struct_perm.derivative B π.to_struct_perm :=
sorry

@[simp] lemma smul_derivative_bot {A : le_index α} (π : allowable_path A) (h : (⊥ : type_index) < A)
  {X : Type*} [mul_action near_litter_perm X] (x : X) :
  (π.derivative h) • x = π • x :=
begin
  unfold has_smul.smul has_smul.comp.smul struct_perm.to_near_litter_perm,
  simp only [monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, struct_perm.coe_to_bot_iso_symm,
    struct_perm.of_bot_smul, to_struct_perm_derivative],
  refl,
end

end allowable_path

/-- Path-indexed of the f-map. -/
def f_map_path {A : Λ} {A_path : path (α : type_index) A} ⦃γ : type_index⦄ ⦃δ : Λ⦄ (hγ : γ < A)
  (hδ : δ < A) : tangle_path (lt_index.mk' hγ A_path : le_index α) → litter :=
f_map (proper_lt_index.mk' hδ A_path).index

lemma f_map_path_assoc {δ ζ : Λ} {β γ ε : type_index} (A : path (α : type_index) β)
  (B : path β γ) (C : path γ δ) (hε : ε < δ) (hζ : ζ < δ)
  (t : tangle_path (lt_index.mk' hε ((A.comp B).comp C) : le_index α)) :
  f_map_path hε hζ (t.lt_index_assoc) = f_map_path hε hζ t :=
begin
  unfold f_map_path,
  congr' 1; try { rw path.comp_assoc },
  exact tangle_path.lt_index_assoc.heq t,
end

lemma f_map_path_injective {A : Λ} {A_path : path (α : type_index) A} ⦃γ₁ γ₂ : type_index⦄ ⦃δ : Λ⦄
  {hγ₁ : γ₁ < A} {hγ₂ : γ₂ < A} {hδ : δ < A}
  {t₁ : tangle_path (lt_index.mk' hγ₁ A_path : le_index α)}
  {t₂ : tangle_path (lt_index.mk' hγ₂ A_path : le_index α)} :
  f_map_path hγ₁ hδ t₁ = f_map_path hγ₂ hδ t₂ → γ₁ = γ₂ ∧ t₁ == t₂ :=
begin
  intro h,
  cases f_map_range_eq _ h,
  exact ⟨rfl, heq_of_eq (f_map_injective (proper_lt_index.mk' hδ A_path).index h)⟩,
end

/-- The injection from near-litters to path-indexed tangles. -/
def typed_near_litter_path (A : proper_lt_index α) : near_litter ↪ tangle_path (A : le_index α) :=
typed_near_litter

/-- The typed singleton as a path-indexed tangle. -/
def typed_singleton_path (A : proper_lt_index α) : atom ↪ tangle_path (A : le_index α) :=
typed_singleton

lemma f_map_path_position_raising {A : Λ} {A_path : path (α : type_index) A}
  ⦃γ : type_index⦄ ⦃δ : Λ⦄ (hγ : γ < A) (hδ : δ < A)
  (t : tangle_path (lt_index.mk' hγ A_path : le_index α))
  (N : set atom) (hN : is_near_litter (f_map_path hγ hδ t) N) :
  position t <
    position (typed_near_litter_path (proper_lt_index.mk' hδ A_path) ⟨f_map_path hγ hδ t, N, hN⟩) :=
f_map_position_raising (proper_lt_index.mk' hδ A_path).index t N hN

instance allowable_path_action_lt (A : le_index α) {β : type_index} (hβ : β < A) :
mul_action (allowable_path (A.cons hβ)) (tangle_path (lt_index.mk' hβ A.path : le_index α)) :=
core_tangle_data.allowable_action

/-- The unpacked coherence condition, given in terms of the phase 2 constructions. -/
def smul_f_map_path {β : Λ} (A : path (α : type_index) β) {γ : type_index} {δ : Λ}
  (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  (π : allowable_path (le_index.mk β A)) (t : tangle_path (lt_index.mk' hγ A : le_index α)) :
  (π.derivative $ coe_lt_coe.mpr hδ) • f_map_path hγ hδ t =
  f_map_path hγ hδ (π.derivative hγ • t) :=
phase_2_assumptions.smul_f_map A hγ hδ hγδ π t

lemma smul_tangle_eq_iff_smul_f_map_eq {β : Λ} (A : path (α : type_index) β)
  {γ : type_index} {δ : Λ} (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  (π : allowable_path (le_index.mk β A))
  (t : tangle_path (lt_index.mk' hγ A : le_index α)) :
  (π.derivative hγ) • t = t ↔
  (π.derivative $ with_bot.coe_lt_coe.mpr hδ) • f_map_path hγ hδ t = f_map_path hγ hδ t :=
begin
  rw smul_f_map_path _ _ _ hγδ,
  split,
  { intro h, rw h, },
  { intro h, have := f_map_path_injective h, exact eq_of_heq this.2, },
end

lemma support_le_path (A : proper_lt_index α) (t : tangle_path (A : le_index α))
  (c : support_condition A) (hc : c ∈ designated_support_path t)
  (not_singleton : ∀ a, t ≠ typed_singleton a)
  (not_near_litter : ∀ (L : litter), t ≠ typed_near_litter L.to_near_litter) :
  position (c.fst.elim (typed_singleton_path A) (typed_near_litter_path A)) ≤ position t :=
tangle_data.support_le t c hc not_singleton not_near_litter

end con_nf
