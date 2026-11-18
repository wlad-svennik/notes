import MHInterpretsMAC
import NFConsistentViaNFU

set_option autoImplicit false

/-!
# Mac Lane set theory with Choice: the statements together

* `SetTheory.nfInterpretsMH : 𝗡𝗙 ⊳ 𝗠𝗛` (`NFInterpretsMH`): the theory `𝗠𝗛` is Mathias's `𝗠` with the
  collapse axiom.
* `SetTheory.mhInterpretsMAC : 𝗠𝗛 ⊳ 𝗠𝗔𝗖` (`MHInterpretsMAC`): the constructible sets.
* `SetTheory.nfInterpretsMAC : 𝗡𝗙 ⊳ 𝗠𝗔𝗖` and `SetTheory.nfuInterpretsMAC : 𝗡𝗙𝗨𝗜 ⊳ 𝗠𝗔𝗖`, by
  composition.

The two statements below are theorems of Lean for a reason outside the interpretations: NFU +
Infinity has a model in Lean's own logic (`consistent_nf_of_jensen`). They show that the
interpretations are not vacuous. They do not say that `𝗠𝗔𝗖` or `𝗡𝗙` is consistent relative to a
weaker system.
-/

namespace FFL.FirstOrder.SetTheory

/-- If `𝗡𝗙` is consistent then so is `𝗠𝗛`. -/
theorem consistent_mh_of_consistent_nf (h : Entailment.Consistent 𝗡𝗙) :
    Entailment.Consistent 𝗠𝗛 := by
  by_contra hM
  have hbot : 𝗠𝗛 ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hM ⊥
  have := DirectInterpretation.sound nfInterpretsMH hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

/-- **`𝗠𝗛` is consistent**, in Lean's logic. -/
theorem consistent_mh : Entailment.Consistent 𝗠𝗛 :=
  consistent_mh_of_consistent_nf consistent_nf_of_jensen

/-- **`𝗠𝗔𝗖` is consistent**, in Lean's logic. -/
theorem consistent_mac : Entailment.Consistent 𝗠𝗔𝗖 :=
  consistent_mac_of_consistent_nf consistent_nf_of_jensen

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.consistent_mh
#print axioms FFL.FirstOrder.SetTheory.consistent_mac
