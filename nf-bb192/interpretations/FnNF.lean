import NFInterpretsFn
import FnInterpretsNFU

set_option autoImplicit false

/-!
# NF, FunctionNF and NFU + Infinity interpret each other

The interpretations proved in the other files, and their compositions:

* `SetTheory.NFFn.nfInterpretsFn : 𝗡𝗙 ⊳ 𝗙𝗡𝗙` (`NFInterpretsFn.lean`)
* `FNF.fnInterpretsNFUI : 𝗙𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜` (`FnInterpretsNFU.lean`)
* `FNF.fnInterpretsNF : 𝗙𝗡𝗙 ⊳ 𝗡𝗙`, through `SetTheory.nfuInterpretsNF : 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`
* `nfuiInterpretsFn : 𝗡𝗙𝗨𝗜 ⊳ 𝗙𝗡𝗙`, through `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`
* `nfInterpretsNFUIviaFn : 𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜`, through FunctionNF

and the statements about consistency that follow from them.
-/

namespace FFL.FirstOrder

open SetTheory

/-- **NFU + Infinity interprets FunctionNF**, by composition with `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`. -/
instance nfuiInterpretsFn : 𝗡𝗙𝗨𝗜 ⊳ 𝗙𝗡𝗙 :=
  DirectInterpretation.comp NFFn.nfInterpretsFn nfuInterpretsNF

/-- **NF interprets NFU + Infinity through FunctionNF.** -/
def nfInterpretsNFUIviaFn : 𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜 :=
  DirectInterpretation.comp FNF.fnInterpretsNFUI NFFn.nfInterpretsFn

/-- If `𝗡𝗙` is consistent then so is FunctionNF. -/
theorem consistent_fn_of_consistent_nf (h : Entailment.Consistent 𝗡𝗙) :
    Entailment.Consistent 𝗙𝗡𝗙 := by
  by_contra hU
  have hbot : 𝗙𝗡𝗙 ⊢ (⊥ : Sentence ℒλ) := Entailment.not_consistent_iff_inconsistent.mp hU ⊥
  have := DirectInterpretation.sound NFFn.nfInterpretsFn hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

/-- If FunctionNF is consistent then so is `𝗡𝗙`. -/
theorem consistent_nf_of_consistent_fn (h : Entailment.Consistent 𝗙𝗡𝗙) :
    Entailment.Consistent 𝗡𝗙 := by
  by_contra hU
  have hbot : 𝗡𝗙 ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hU ⊥
  have := DirectInterpretation.sound FNF.fnInterpretsNF hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

/-- If FunctionNF is consistent then so is NFU + Infinity. -/
theorem consistent_nfui_of_consistent_fn (h : Entailment.Consistent 𝗙𝗡𝗙) :
    Entailment.Consistent 𝗡𝗙𝗨𝗜 := by
  by_contra hU
  have hbot : 𝗡𝗙𝗨𝗜 ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hU ⊥
  have := DirectInterpretation.sound FNF.fnInterpretsNFUI hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

/-- If NFU + Infinity is consistent then so is FunctionNF. -/
theorem consistent_fn_of_consistent_nfui (h : Entailment.Consistent 𝗡𝗙𝗨𝗜) :
    Entailment.Consistent 𝗙𝗡𝗙 := by
  by_contra hU
  have hbot : 𝗙𝗡𝗙 ⊢ (⊥ : Sentence ℒλ) := Entailment.not_consistent_iff_inconsistent.mp hU ⊥
  have := DirectInterpretation.sound nfuiInterpretsFn hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

/-- **FunctionNF is consistent if and only if NF is.** -/
theorem consistent_fn_iff_consistent_nf :
    Entailment.Consistent 𝗙𝗡𝗙 ↔ Entailment.Consistent 𝗡𝗙 :=
  ⟨consistent_nf_of_consistent_fn, consistent_fn_of_consistent_nf⟩

/-- **FunctionNF is consistent if and only if NFU + Infinity is.** -/
theorem consistent_fn_iff_consistent_nfui :
    Entailment.Consistent 𝗙𝗡𝗙 ↔ Entailment.Consistent 𝗡𝗙𝗨𝗜 :=
  ⟨consistent_nfui_of_consistent_fn, consistent_fn_of_consistent_nfui⟩

/-- **FunctionNF is consistent.** This is a theorem of Lean because NFU + Infinity has a model
(`Jensen.consistent_nfuInfinity`, Jensen's construction). It shows that the interpretations
above are not vacuous; it also makes the two equivalences above true for a trivial reason, so
the content is in the interpretations, not in the equivalences. -/
theorem consistent_fn : Entailment.Consistent 𝗙𝗡𝗙 :=
  consistent_fn_of_consistent_nfui SetTheory.Jensen.consistent_nfuInfinity

end FFL.FirstOrder

#print axioms FFL.FirstOrder.consistent_fn
#print axioms FFL.FirstOrder.SetTheory.NFFn.nfInterpretsFn
#print axioms FFL.FirstOrder.FNF.fnInterpretsNFUI
#print axioms FFL.FirstOrder.FNF.fnInterpretsNF
#print axioms FFL.FirstOrder.nfuiInterpretsFn
#print axioms FFL.FirstOrder.nfInterpretsNFUIviaFn
#print axioms FFL.FirstOrder.consistent_fn_iff_consistent_nf
#print axioms FFL.FirstOrder.consistent_fn_iff_consistent_nfui
