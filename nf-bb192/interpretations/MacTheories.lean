import Foundation.FirstOrder.SetTheory.Z.Basic
import Foundation.FirstOrder.SetTheory.Basic

set_option autoImplicit false

/-!
# Mac Lane set theory

The theories `𝗠` and `𝗠𝗔𝗖` of A. R. D. Mathias, *The strength of Mac Lane set theory* (2001), in
the idiom of the library.

* `𝗦𝗘𝗣₀` is the schema of separation for bounded formulas: the formulas in which every
  quantifier has the form `∀ x ∈ t` or `∃ x ∈ t` (`Bounding.Closure` for the bounding `∈`).
* `𝗧𝗖𝗼` is transitive containment: every set is included in a transitive set.
* `𝗠` is `𝗕𝗦𝗧 + 𝗦𝗘𝗣₀ + 𝗧𝗖𝗼`. Here `𝗕𝗦𝗧` is the library's theory of extensionality, empty set,
  pairing, union, power set, infinity and foundation. (Mathias also lists set difference, which
  is an instance of `𝗦𝗘𝗣₀`.)
* `𝗠𝗔𝗖` is `𝗠` with the axiom of choice `𝗔𝗖` of the library (a choice set for every family of
  pairwise disjoint sets with members).

Mac Lane's own system `ZBQC` is `𝗠𝗔𝗖` without `𝗧𝗖𝗼`, so it is a subtheory of `𝗠𝗔𝗖`.

This file imports only the library.
-/

namespace FFL.FirstOrder.SetTheory

namespace Axiom

/-- Transitive containment: every set is included in a transitive set. -/
def transitiveContainment : SetTheorySentence :=
  “∀ x, ∃ t, x ⊆ t ∧ ∀ y ∈ t, y ⊆ t”

end Axiom

/-! ### Separation for bounded formulas -/

/-- The schema of separation for bounded formulas. -/
inductive BoundedSeparation : SetTheory
  /-- Separation for a formula all of whose quantifiers are bounded. -/
  | separation (φ : SetTheorySemiproposition 1) :
      (Bounding.mem ℒₛₑₜ).Closure φ → BoundedSeparation (Axiom.separationSchema φ)

/-- The schema of separation for bounded formulas. -/
notation "𝗦𝗘𝗣₀" => BoundedSeparation

/-- Every instance of bounded separation is an instance of separation. -/
lemma boundedSeparation_subset : 𝗦𝗘𝗣₀ ⊆ 𝗦𝗘𝗣 := by
  rintro φ ⟨ψ, -⟩
  exact Separation.separation ψ

/-! ### Transitive containment -/

/-- The theory containing only the axiom of transitive containment. -/
def TransitiveContainment : SetTheory := {Axiom.transitiveContainment}

/-- The theory containing only the axiom of transitive containment. -/
notation "𝗧𝗖𝗼" => TransitiveContainment

/-! ### Mathias's `M` -/

/-- Mathias's theory `M`: extensionality, empty set, pairing, union, power set, infinity,
foundation, separation for bounded formulas, and transitive containment. No choice. -/
abbrev MathiasM : SetTheory := 𝗕𝗦𝗧 ∪ 𝗦𝗘𝗣₀ ∪ 𝗧𝗖𝗼

/-- Mathias's theory `M`. -/
notation "𝗠" => MathiasM

instance : 𝗘𝗤 _ ⪯ 𝗠 :=
  let : 𝗘𝗤 _ ⪯ 𝗕𝗦𝗧 := inferInstance
  Entailment.WeakerThan.trans this
    (Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl (Or.inl h))

instance : 𝗕𝗦𝗧 ⪯ 𝗠 := Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl (Or.inl h)

instance : 𝗦𝗘𝗣₀ ⪯ 𝗠 := Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl (Or.inr h)

instance : 𝗧𝗖𝗼 ⪯ 𝗠 := Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inr h

/-! ### Mac Lane set theory -/

/-- Mac Lane set theory in Mathias's sense: `𝗠` with the axiom of choice. -/
abbrev MacLane : SetTheory := 𝗠 ∪ 𝗔𝗖

/-- Mac Lane set theory in Mathias's sense: `𝗠` with the axiom of choice. -/
notation "𝗠𝗔𝗖" => MacLane

instance : 𝗠 ⪯ 𝗠𝗔𝗖 := Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl h

instance : 𝗔𝗖 ⪯ 𝗠𝗔𝗖 := Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inr h

instance : 𝗘𝗤 _ ⪯ 𝗠𝗔𝗖 :=
  let : 𝗘𝗤 _ ⪯ 𝗠 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

end FFL.FirstOrder.SetTheory
