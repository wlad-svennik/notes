import NFUJensen
import ConNF.NF.ExistsNF

set_option autoImplicit false

/-!
# NF is consistent, by way of con-nf's model

`ConNF.NF.exists_nf` is a model of NF obtained from the con-nf project's model of tangled type
theory. This is the only one of our files outside the con-nf tree that uses that model. The proof
of the same statement that does not use it is `consistent_nf_of_jensen`, in
`NFConsistentViaNFU.lean`.
-/

namespace FFL.FirstOrder.SetTheory

/-- **`𝗡𝗙` is consistent**: it does not derive a contradiction. The model is the one given by
`ConNF.NF.exists_nf`. -/
theorem consistent_nf : Entailment.Consistent 𝗡𝗙 := by
  obtain ⟨V, mem, h⟩ := ConNF.NF.exists_nf
  have : Nonempty V := h.nonempty
  let _ : SetStructure V := ⟨fun y x ↦ mem x y⟩
  have hV : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙 := models_nf_of_isNF h
  exact consistent_of_model 𝗡𝗙 V

/-- **`𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ` is consistent.** -/
theorem consistent_nfui : Entailment.Consistent 𝗡𝗙𝗨𝗜ₛ :=
  SetTheoryU.consistent_nfui_iff_consistent_nf.mpr consistent_nf

/-- **NFU + Infinity is consistent.** -/
theorem consistent_nfuInfinity : Entailment.Consistent 𝗡𝗙𝗨𝗜 :=
  consistent_nfuInfinity_iff_consistent_nf.mpr consistent_nf

end FFL.FirstOrder.SetTheory
