import NFInterpretsComb
import CombFn
import FnNF

set_option autoImplicit false

/-!
# NF, CombNF, FunctionNF and NFU + Infinity interpret each other

The interpretations proved in the other files, and their compositions:

* `SetTheory.NFFn.nfInterpretsComb : 𝗡𝗙 ⊳ 𝗖𝗡𝗙` (`NFInterpretsComb.lean`)
* `CNF.combInterpretsFn : 𝗖𝗡𝗙 ⊳ 𝗙𝗡𝗙` (`CombFn.lean`)
* `CNF.combInterpretsNFUI : 𝗖𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜`, through FunctionNF
* `CNF.combInterpretsNF : 𝗖𝗡𝗙 ⊳ 𝗡𝗙`, through FunctionNF and NFU + Infinity
* `nfuiInterpretsComb : 𝗡𝗙𝗨𝗜 ⊳ 𝗖𝗡𝗙`, through NF
* `fnInterpretsComb : 𝗙𝗡𝗙 ⊳ 𝗖𝗡𝗙`, through NFU + Infinity and NF

and the statements about consistency that follow from them.
-/

namespace FFL.FirstOrder

open SetTheory

/-- **NFU + Infinity interprets CombNF**, by composition with `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`. -/
instance nfuiInterpretsComb : 𝗡𝗙𝗨𝗜 ⊳ 𝗖𝗡𝗙 :=
  DirectInterpretation.comp NFFn.nfInterpretsComb nfuInterpretsNF

/-- **FunctionNF interprets CombNF**, through NFU + Infinity and NF. -/
instance fnInterpretsComb : 𝗙𝗡𝗙 ⊳ 𝗖𝗡𝗙 :=
  DirectInterpretation.comp NFFn.nfInterpretsComb FNF.fnInterpretsNF

/-- If `𝗡𝗙` is consistent then so is CombNF. -/
theorem consistent_comb_of_consistent_nf (h : Entailment.Consistent 𝗡𝗙) :
    Entailment.Consistent 𝗖𝗡𝗙 := by
  by_contra hU
  have hbot : 𝗖𝗡𝗙 ⊢ (⊥ : Sentence ℒᴄ) := Entailment.not_consistent_iff_inconsistent.mp hU ⊥
  have := DirectInterpretation.sound NFFn.nfInterpretsComb hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

/-- If CombNF is consistent then so is `𝗡𝗙`. -/
theorem consistent_nf_of_consistent_comb (h : Entailment.Consistent 𝗖𝗡𝗙) :
    Entailment.Consistent 𝗡𝗙 := by
  by_contra hU
  have hbot : 𝗡𝗙 ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hU ⊥
  have := DirectInterpretation.sound CNF.combInterpretsNF hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

/-- If CombNF is consistent then so is FunctionNF. -/
theorem consistent_fn_of_consistent_comb (h : Entailment.Consistent 𝗖𝗡𝗙) :
    Entailment.Consistent 𝗙𝗡𝗙 := by
  by_contra hU
  have hbot : 𝗙𝗡𝗙 ⊢ (⊥ : Sentence ℒλ) := Entailment.not_consistent_iff_inconsistent.mp hU ⊥
  have := DirectInterpretation.sound CNF.combInterpretsFn hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

/-- **CombNF is consistent if and only if NF is.** -/
theorem consistent_comb_iff_consistent_nf :
    Entailment.Consistent 𝗖𝗡𝗙 ↔ Entailment.Consistent 𝗡𝗙 :=
  ⟨consistent_nf_of_consistent_comb, consistent_comb_of_consistent_nf⟩

/-- **CombNF is consistent.** A theorem of Lean because NFU + Infinity has a model
(`Jensen.consistent_nfuInfinity`) and `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙 ⊳ 𝗖𝗡𝗙`. It shows that the interpretations are
not vacuous, and it makes the equivalence above true for a trivial reason. -/
theorem consistent_comb : Entailment.Consistent 𝗖𝗡𝗙 :=
  consistent_comb_of_consistent_nf (consistent_nf_of_consistent_fn consistent_fn)

end FFL.FirstOrder

#print axioms FFL.FirstOrder.SetTheory.NFFn.nfInterpretsComb
#print axioms FFL.FirstOrder.CNF.combInterpretsFn
#print axioms FFL.FirstOrder.CNF.combInterpretsNFUI
#print axioms FFL.FirstOrder.CNF.combInterpretsNF
#print axioms FFL.FirstOrder.nfuiInterpretsComb
#print axioms FFL.FirstOrder.fnInterpretsComb
#print axioms FFL.FirstOrder.consistent_comb_iff_consistent_nf
#print axioms FFL.FirstOrder.consistent_comb
