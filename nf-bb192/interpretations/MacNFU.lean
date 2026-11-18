import MInterpretsTST
import TSTJensen
import NFInterpretsMac

set_option autoImplicit false

/-!
# Mac Lane set theory without choice, type theory, NFU + Infinity and NF

This file puts together

* `mInterpretsTSTI : 𝗠 ⊳ 𝗧𝗦𝗧𝗜` (`MInterpretsTST.lean`);
* `TST.exists_nfui_model`: every model of `𝗧𝗦𝗧𝗜` gives a model of `𝗡𝗙𝗨𝗜` (`TSTJensen.lean`);
* `nfuInterpretsM : 𝗡𝗙𝗨𝗜 ⊳ 𝗠` and `consistent_m_of_consistent_nf` (`NFInterpretsMac.lean`);
* `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙` (`NFUJensen.lean`).

**What the statements say.** `exists_nfui_model_of_m` is the theorem with content: from any
model of `𝗠` it gives a model of `𝗡𝗙𝗨𝗜`, and it ties the truth of typed sentences in the new
model to the levels `Pⁿ(ω)` of the given one. The implications between consistency statements
below follow from it and from the interpretations. As *statements* they say little in Lean,
because Lean proves `Entailment.Consistent 𝗡𝗙𝗨𝗜` outright (`Jensen.consistent_nfuInfinity`, from
the iterated power sets of `ℕ`). Their *proofs* here do not use that theorem: they go through
an arbitrary model of `𝗠`.
-/

namespace FFL.FirstOrder.SetTheory

open JensenNFU (TFm)

/-- If `𝗠` is consistent then so is `𝗧𝗦𝗧𝗜`: the translation of a proof of `⊥` in `𝗧𝗦𝗧𝗜` is a
proof of `⊥` in `𝗠`. -/
theorem consistent_tsti_of_consistent_m (h : Entailment.Consistent 𝗠) :
    Entailment.Consistent 𝗧𝗦𝗧𝗜 := by
  by_contra hT
  have hbot : 𝗧𝗦𝗧𝗜 ⊢ (⊥ : Sentence ℒₜₛₜ) := Entailment.not_consistent_iff_inconsistent.mp hT ⊥
  have := m_provable_translate_of_tsti hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

/-- If `𝗧𝗦𝗧𝗜` is consistent then so is `𝗡𝗙𝗨𝗜`: a consistent theory has a model, and
`TST.exists_nfui_model` turns a model of `𝗧𝗦𝗧𝗜` into a model of `𝗡𝗙𝗨𝗜`. -/
theorem consistent_nfui_of_consistent_tsti (h : Entailment.Consistent 𝗧𝗦𝗧𝗜) :
    Entailment.Consistent 𝗡𝗙𝗨𝗜 := by
  have hsat : Semantics.Satisfiable (Tarski.Struc.{0, 0} ℒₜₛₜ) 𝗧𝗦𝗧𝗜 :=
    (Theory.satisfiable_iff_consistent.{0, 0}).mpr h
  obtain ⟨M, hne, s, heq, hM⟩ := satisfiable_iff_eq.mp hsat
  obtain ⟨N, _, _, hN, -⟩ := TST.exists_nfui_model (M := M)
  exact consistent_of_model 𝗡𝗙𝗨𝗜 N

/-- **Every model of `𝗠` gives a model of `𝗡𝗙𝗨𝗜`.** Every well typed sentence `φ` that is true
in the new model is true of the levels `Pⁿ(ω)` of the given model when it is read along some
strictly increasing sequence of levels `ℓ` (`TST.skip ℓ [] φ`): a variable of type `t` ranges
over `lvl (ℓ t)`, and membership between the levels `ℓ t` and `ℓ (t + 1)` is `TST.SMem`. -/
theorem exists_nfui_model_of_m {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠] :
    ∃ (N : Type) (_ : SetStructure N) (_ : Nonempty N), N↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 ∧
      ∀ φ : TFm, TFm.Strat [] φ → TFm.Sat (fun a b : N => a ∈ b) φ [] →
        ∃ ℓ : ℕ → ℕ, StrictMono ℓ ∧ ∀ v : ℕ → V,
          TFm.SatT (fun k (a : V) => a ∈ (lvl k : V)) (fun a b => a ∈ b)
            (TST.skip ℓ [] φ) v := by
  haveI := tstModel_models (V := V)
  obtain ⟨N, i1, i2, hN, htie⟩ := TST.exists_nfui_model (M := tstTranslation.Model V)
  refine ⟨N, i1, i2, hN, fun φ hφ hsat => ?_⟩
  obtain ⟨ℓ, hℓ, h⟩ := htie φ hφ hsat
  exact ⟨ℓ, hℓ, fun v => (tm_holds _ (fun i => toModel (v i))).mp (h _)⟩

/-- If `𝗠` is consistent then so is `𝗡𝗙𝗨𝗜`. -/
theorem consistent_nfui_of_consistent_m (h : Entailment.Consistent 𝗠) :
    Entailment.Consistent 𝗡𝗙𝗨𝗜 :=
  consistent_nfui_of_consistent_tsti (consistent_tsti_of_consistent_m h)

/-- If `𝗡𝗙𝗨𝗜` is consistent then so is `𝗠`, by the interpretation `nfuInterpretsM`. -/
theorem consistent_m_of_consistent_nfui (h : Entailment.Consistent 𝗡𝗙𝗨𝗜) :
    Entailment.Consistent 𝗠 := by
  by_contra hM
  have hbot : 𝗠 ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hM ⊥
  have := DirectInterpretation.sound nfuInterpretsM hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

/-- `𝗠` is consistent iff `𝗡𝗙𝗨𝗜` is. -/
theorem consistent_m_iff_consistent_nfui :
    Entailment.Consistent 𝗠 ↔ Entailment.Consistent 𝗡𝗙𝗨𝗜 :=
  ⟨consistent_nfui_of_consistent_m, consistent_m_of_consistent_nfui⟩

/-- `𝗠` is consistent iff `𝗡𝗙` is. -/
theorem consistent_m_iff_consistent_nf :
    Entailment.Consistent 𝗠 ↔ Entailment.Consistent 𝗡𝗙 :=
  consistent_m_iff_consistent_nfui.trans consistent_nfuInfinity_iff_consistent_nf

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.exists_nfui_model_of_m
#print axioms FFL.FirstOrder.SetTheory.consistent_m_iff_consistent_nfui
#print axioms FFL.FirstOrder.TST.exists_nfui_model
