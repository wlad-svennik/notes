import Foundation.FirstOrder.LK.Interpretation
import Foundation.FirstOrder.SetTheory.Basic

set_option autoImplicit false

/-!
# NF and NFU as first-order theories

The theories `𝗡𝗙` (in the language `ℒₛₑₜ` of set theory) and `𝗡𝗙𝗨ₛ` (in the language `ℒₛₑₜᵤ`,
which has a further predicate "is a set"), stated in the idiom of the library: a schema is a
function from formulas to sentences, built with `univCl`, and a theory is an inductive set of
sentences.

Stratification is a predicate on the formulas of the library. It is defined once, for every
language without function symbols whose relation symbols say how the types of their arguments
are related (`Language.Stratification`).
-/

namespace FFL.FirstOrder

/-! ### The language of set theory with urelements -/

namespace Language

namespace SetU

inductive Rel : ℕ → Type
  | eq : Rel 2
  | mem : Rel 2
  | set : Rel 1

end SetU

/-- Language of set theory with urelements: equality, membership, and "is a set". -/
@[reducible]
def setU : Language where
  Func := fun _ ↦ Empty
  Rel := SetU.Rel

notation "ℒₛₑₜᵤ" => setU

namespace SetU

instance (k) : DecidableEq (SetU.Rel k) := fun a b => by
  rcases a <;> rcases b <;>
  simp only [reduceCtorEq] <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : Encodable (SetU.Rel k) where
  encode := fun x =>
    match x with
    | Rel.eq => 0
    | Rel.mem => 1
    | Rel.set => 0
  decode := fun e =>
    match k, e with
    | 2, 0 => some Rel.eq
    | 2, 1 => some Rel.mem
    | 1, 0 => some Rel.set
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance : (ℒₛₑₜᵤ).DecidableEq := ⟨fun _ ↦ inferInstanceAs (DecidableEq Empty), fun _ ↦ inferInstance⟩

instance : (ℒₛₑₜᵤ).Encodable := ⟨fun _ ↦ inferInstanceAs (Encodable Empty), fun _ ↦ inferInstance⟩

instance : (ℒₛₑₜᵤ).Eq := ⟨Rel.eq⟩

instance : (ℒₛₑₜᵤ).Mem := ⟨Rel.mem⟩

instance : (ℒₛₑₜᵤ).Relational := ⟨fun _ ↦ inferInstanceAs (IsEmpty Empty)⟩

end SetU

instance : (ℒₛₑₜ).Relational := ⟨fun _ ↦ inferInstanceAs (IsEmpty Empty)⟩

/-- The relation symbols of the language say how the types of their arguments are related: an
atomic formula `r(v₀, …, vₖ₋₁)` is well typed when, for some `t`, each `vᵢ` has type
`t + lv r i`. -/
class Stratification (L : Language) where
  lv {k : ℕ} : L.Rel k → Fin k → ℕ

/-- In `x = y` the two sides have the same type; in `x ∈ y` the type of `y` is one more than
the type of `x`. -/
instance : (ℒₛₑₜ).Stratification where
  lv := fun r =>
    match r with
    | Set.Rel.eq => ![0, 0]
    | Set.Rel.mem => ![0, 1]

instance : (ℒₛₑₜᵤ).Stratification where
  lv := fun r =>
    match r with
    | SetU.Rel.eq => ![0, 0]
    | SetU.Rel.mem => ![0, 1]
    | SetU.Rel.set => ![0]

end Language

/-! ### Stratified formulas -/

section stratified

variable {L : Language} [L.Relational] {ξ : Type*}

/-- The type of a variable, where `σ` gives the types of the free variables and `τ` those of
the bound variables. -/
def Semiterm.lv (σ : ξ → ℕ) {n : ℕ} (τ : Fin n → ℕ) : Semiterm L ξ n → ℕ
  | #x => τ x
  | &x => σ x
  | .func f _ => isEmptyElim f

@[simp] lemma Semiterm.lv_bvar (σ : ξ → ℕ) {n : ℕ} (τ : Fin n → ℕ) (x : Fin n) :
    (#x : Semiterm L ξ n).lv σ τ = τ x := rfl

@[simp] lemma Semiterm.lv_fvar (σ : ξ → ℕ) {n : ℕ} (τ : Fin n → ℕ) (x : ξ) :
    (&x : Semiterm L ξ n).lv σ τ = σ x := rfl

@[simp] lemma Semiterm.lv_bShift (σ : ξ → ℕ) {n : ℕ} (τ : Fin n → ℕ) (t₀ : ℕ)
    (t : Semiterm L ξ n) : (Rew.bShift t).lv σ (t₀ :> τ) = t.lv σ τ := by
  match t with
  | #x => simp
  | &x => simp
  | .func f _ => exact isEmptyElim f

variable [L.Stratification]

/-- `φ.Stratified σ τ`: the formula is stratified, where `σ` gives the types of the free
variables, `τ` those of the bound variables that are free in `φ`, and each quantifier chooses
a type for the variable it binds. -/
def Semiformula.Stratified (σ : ξ → ℕ) {n : ℕ} (τ : Fin n → ℕ) : Semiformula L ξ n → Prop
  | .rel r v => ∃ t, ∀ i, (v i).lv σ τ = t + Language.Stratification.lv r i
  | .nrel r v => ∃ t, ∀ i, (v i).lv σ τ = t + Language.Stratification.lv r i
  | ⊤ => True
  | ⊥ => True
  | φ ⋏ ψ => φ.Stratified σ τ ∧ ψ.Stratified σ τ
  | φ ⋎ ψ => φ.Stratified σ τ ∧ ψ.Stratified σ τ
  | ∀¹ φ => ∃ t, φ.Stratified σ (t :> τ)
  | ∃¹ φ => ∃ t, φ.Stratified σ (t :> τ)

namespace Semiformula

variable {σ : ξ → ℕ} {n : ℕ} {τ : Fin n → ℕ}

@[simp] lemma stratified_rel {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ n} :
    (rel r v).Stratified σ τ ↔ ∃ t, ∀ i, (v i).lv σ τ = t + Language.Stratification.lv r i := by
  rfl

@[simp] lemma stratified_nrel {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ n} :
    (nrel r v).Stratified σ τ ↔ ∃ t, ∀ i, (v i).lv σ τ = t + Language.Stratification.lv r i := by
  rfl

@[simp] lemma stratified_verum : (⊤ : Semiformula L ξ n).Stratified σ τ := trivial

@[simp] lemma stratified_falsum : (⊥ : Semiformula L ξ n).Stratified σ τ := trivial

@[simp] lemma stratified_and {φ ψ : Semiformula L ξ n} :
    (φ ⋏ ψ).Stratified σ τ ↔ φ.Stratified σ τ ∧ ψ.Stratified σ τ := by rfl

@[simp] lemma stratified_or {φ ψ : Semiformula L ξ n} :
    (φ ⋎ ψ).Stratified σ τ ↔ φ.Stratified σ τ ∧ ψ.Stratified σ τ := by rfl

@[simp] lemma stratified_all {φ : Semiformula L ξ (n + 1)} :
    (∀¹ φ).Stratified σ τ ↔ ∃ t, φ.Stratified σ (t :> τ) := by rfl

@[simp] lemma stratified_exs {φ : Semiformula L ξ (n + 1)} :
    (∃¹ φ).Stratified σ τ ↔ ∃ t, φ.Stratified σ (t :> τ) := by rfl

@[simp] lemma stratified_neg {φ : Semiformula L ξ n} :
    (∼φ).Stratified σ τ ↔ φ.Stratified σ τ := by
  induction φ using Semiformula.rec' <;> simp [*]

@[simp] lemma stratified_imp {φ ψ : Semiformula L ξ n} :
    (φ 🡒 ψ).Stratified σ τ ↔ φ.Stratified σ τ ∧ ψ.Stratified σ τ := by
  simp [Semiformula.imp_eq]

/-- A formula is stratified when some assignment of types to its variables stratifies it. -/
def IsStratified (φ : Semiformula L ξ n) : Prop := ∃ σ τ, φ.Stratified σ τ

end Semiformula

end stratified

/-! ### NF -/

namespace SetTheory

namespace Axiom

/-- Axiom schema of comprehension. Its instances for stratified formulas are axioms of NF. -/
def comprehensionSchema (φ : SetTheorySemiproposition 1) : SetTheorySentence :=
  .univCl “∃ y, ∀ x, x ∈ y ↔ !φ x”

end Axiom

/-- Quine's New Foundations: extensionality and stratified comprehension. -/
inductive NewFoundations : SetTheory
  /-- Axiom of equality. -/
  | equality : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ, NewFoundations φ
  /-- Axiom of extensionality. -/
  | extensionality : NewFoundations “∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y”
  /-- Axiom schema of stratified comprehension. -/
  | comprehension (φ : SetTheorySemiproposition 1) :
      φ.IsStratified → NewFoundations (Axiom.comprehensionSchema φ)

notation "𝗡𝗙" => NewFoundations

instance : 𝗘𝗤 _ ⪯ 𝗡𝗙 := Entailment.WeakerThan.ofSubset NewFoundations.equality

/-! ### NFU, in the language of membership and equality -/

namespace Axiom

/-- The universe is not finite: some family contains every object without members and is closed
under adjoining one element, but contains no universal set. -/
def universeInfinite : SetTheorySentence :=
  “∃ F, (∀ e, (∀ z, z ∉ e) → e ∈ F) ∧
    (∀ s ∈ F, ∀ b s', (∀ z, z ∈ s' ↔ z ∈ s ∨ z = b) → s' ∈ F) ∧
    (∀ u, (∀ z, z ∈ u) → u ∉ F)”

end Axiom

/-- Jensen's NFU: extensionality for the objects that have members, and stratified
comprehension. Objects without members are the urelements; none of them is singled out as the
empty set. -/
inductive NewFoundationsWithUrelements : SetTheory
  /-- Axiom of equality. -/
  | equality : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ, NewFoundationsWithUrelements φ
  /-- Axiom of extensionality for objects with members. -/
  | extensionality :
      NewFoundationsWithUrelements “∀ x y, (∃ z, z ∈ x) → (∀ z, z ∈ x ↔ z ∈ y) → x = y”
  /-- Axiom schema of stratified comprehension. -/
  | comprehension (φ : SetTheorySemiproposition 1) :
      φ.IsStratified → NewFoundationsWithUrelements (Axiom.comprehensionSchema φ)

notation "𝗡𝗙𝗨" => NewFoundationsWithUrelements

instance : 𝗘𝗤 _ ⪯ 𝗡𝗙𝗨 := Entailment.WeakerThan.ofSubset NewFoundationsWithUrelements.equality

/-- The theory containing only the axiom that the universe is not finite. -/
def UniverseInfinite : SetTheory := {Axiom.universeInfinite}

notation "𝗜𝗡𝗙" => UniverseInfinite

/-- NFU with the axiom of infinity. -/
abbrev NFUInfinity : SetTheory := 𝗡𝗙𝗨 ∪ 𝗜𝗡𝗙

notation "𝗡𝗙𝗨𝗜" => NFUInfinity

instance : 𝗡𝗙𝗨 ⪯ 𝗡𝗙𝗨𝗜 := inferInstance

instance : 𝗘𝗤 _ ⪯ 𝗡𝗙𝗨𝗜 :=
  let : 𝗘𝗤 _ ⪯ 𝗡𝗙𝗨 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

end SetTheory

/-! ### NFU with a predicate for sethood -/

namespace SetTheoryU

/-- "is a set" -/
def isSet : Semisentence ℒₛₑₜᵤ 1 := Semiformula.rel Language.SetU.Rel.set ![#0]

namespace Axiom

/-- Axiom schema of comprehension, with a set as the result. -/
def comprehensionSchema (φ : Semiproposition ℒₛₑₜᵤ 1) : Sentence ℒₛₑₜᵤ :=
  .univCl “∃ y, !isSet y ∧ ∀ x, x ∈ y ↔ !φ x”

/-- Axiom of infinity: the universe is not finite. Some family contains every empty set and is
closed under adjoining one element, but contains no universal set. -/
def infinity : Sentence ℒₛₑₜᵤ :=
  “∃ F, (∀ e, !isSet e → (∀ z, z ∉ e) → e ∈ F) ∧
    (∀ s ∈ F, ∀ b s', !isSet s' → (∀ z, z ∈ s' ↔ z ∈ s ∨ z = b) → s' ∈ F) ∧
    (∀ u, (∀ z, z ∈ u) → u ∉ F)”

end Axiom

/-- NFU: only sets have members, sets with the same members are equal, and stratified
comprehension. -/
inductive NewFoundationsU : Theory ℒₛₑₜᵤ
  /-- Axiom of equality. -/
  | equality : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜᵤ, NewFoundationsU φ
  /-- Only sets have members. -/
  | set_of_mem : NewFoundationsU “∀ x y, x ∈ y → !isSet y”
  /-- Axiom of extensionality for sets. -/
  | extensionality :
      NewFoundationsU “∀ x y, !isSet x → !isSet y → (∀ z, z ∈ x ↔ z ∈ y) → x = y”
  /-- Axiom schema of stratified comprehension. -/
  | comprehension (φ : Semiproposition ℒₛₑₜᵤ 1) :
      φ.IsStratified → NewFoundationsU (Axiom.comprehensionSchema φ)

notation "𝗡𝗙𝗨ₛ" => NewFoundationsU

instance : 𝗘𝗤 _ ⪯ 𝗡𝗙𝗨ₛ := Entailment.WeakerThan.ofSubset NewFoundationsU.equality

/-- The theory containing only the axiom of infinity. -/
def AxiomOfInfinity : Theory ℒₛₑₜᵤ := {Axiom.infinity}

notation "𝗜𝗡𝗙ₛ" => AxiomOfInfinity

/-- NFU with the axiom of infinity. -/
abbrev NewFoundationsUInfinity : Theory ℒₛₑₜᵤ := 𝗡𝗙𝗨ₛ ∪ 𝗜𝗡𝗙ₛ

notation "𝗡𝗙𝗨𝗜ₛ" => NewFoundationsUInfinity

instance : 𝗡𝗙𝗨ₛ ⪯ 𝗡𝗙𝗨𝗜ₛ := inferInstance

instance : 𝗘𝗤 _ ⪯ 𝗡𝗙𝗨𝗜ₛ :=
  let : 𝗘𝗤 _ ⪯ 𝗡𝗙𝗨ₛ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

end SetTheoryU

end FFL.FirstOrder
