import NF210.ProofBB210Final
import NF210.ProofBusyBeaverExactValue

/-! Exact-value versions of the completed 210-state Busy Beaver theorem. -/

namespace NF210.Proof.BusyBeaver

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- Under consistency, NF cannot prove any proposed numeral value of BB(210). -/
theorem no_numeral_exact_value (consistent : ConNF) :
    ∀ k : Nat, NF ⊬ nfExactValue k := by
  intro k proof
  exact no_numeral_upper_bound consistent k
    (Entailment.mdp (nf_exactValue_implies_upperBound k) proof)

/-- Under arithmetic Sigma-one soundness, the sentence asserting the actual
value of BB(210) is neither provable nor refutable in NF. Its numeral is
selected externally by the least-bound definition; it is not computed. -/
theorem busyBeaver210_exactValue_independent
    (sound : NFSecond.ArithmeticSigmaOneSound) :
    Entailment.Independent NF (nfExactValue (TM.busyBeaver 210)) := by
  let : ArithmeticTheory.SoundOnHierarchy ArithmeticPullback.theory 𝚺 1 := sound
  have consistent : ConNF := ArithmeticPullback.conNF_of_consistent inferInstance
  exact ⟨no_numeral_exact_value consistent (TM.busyBeaver 210),
    busyBeaver210_exactValue_unrefutable sound⟩

end NF210.Proof.BusyBeaver

#print NF210.Proof.BusyBeaver.no_numeral_exact_value
#print NF210.Proof.BusyBeaver.busyBeaver210_exactValue_independent
#print axioms NF210.Proof.BusyBeaver.no_numeral_exact_value
#print axioms NF210.Proof.BusyBeaver.busyBeaver210_exactValue_independent
