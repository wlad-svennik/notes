import NFUJensen
import NFUConsistent

set_option autoImplicit false

/-!
# NF is consistent, by way of NFU + Infinity

Jensen's model gives the consistency of `𝗡𝗙𝗨𝗜`, and `𝗡𝗙𝗨𝗜` interprets `𝗡𝗙`. So `𝗡𝗙` is consistent.
This proof does not use the model of tangled type theory of the con-nf project.
-/

namespace FFL.FirstOrder.SetTheory

/-- **NF is consistent**, from the consistency of NFU + Infinity and the interpretation of NF
in NFU + Infinity. -/
theorem consistent_nf_of_jensen : Entailment.Consistent 𝗡𝗙 :=
  consistent_nfuInfinity_iff_consistent_nf.mp Jensen.consistent_nfuInfinity

end FFL.FirstOrder.SetTheory
