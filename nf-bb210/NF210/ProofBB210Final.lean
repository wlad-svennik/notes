import NF210.ProofBinarySourceBridge
import NF210.ProofFinalGroundHBL
import NF210.ProofBusyBeaverSoundness
import NF210.BusyBeaverValue

/-!
# The completed 210-state Busy Beaver incompleteness theorem

The binary source bridge and the ground provability predicate's derivability
conditions are theorems. The unprovability conclusion below assumes only
consistency of the original NF proof system. No calibration, reflection,
compiler-correctness, simulation, or machine-behavior premise remains.

Two-sided independence of a true upper bound is stated separately under
arithmetic Sigma-one soundness. The least upper bound is the actual runtime
Busy Beaver value for binary, two-way, blank-tape machines with 210 nonhalting
states. No value of that number is calculated or supplied as an assumption.
-/

namespace NF210.Proof.BusyBeaver

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- Every standard numeral upper bound for runtime BB(210) is unprovable
in NF, assuming only the consistency of the displayed NF proof system. -/
theorem no_numeral_upper_bound (consistent : ConNF) :
    ∀ k : Nat, NF ⊬ nfUpperBound k :=
  GroundReduction.no_numeral_upper_bound_of_binary
    BinarySimulation.source_implies_binary_halting consistent

/-- A true numerical upper bound is independent under arithmetic Sigma-one
soundness. This stronger assumption is explicit and is not replaced by
bare consistency. -/
theorem true_upperBound_independent
    (sound : NFSecond.ArithmeticSigmaOneSound)
    (k : Nat) (trueBound : TM.UpperBound 210 k) :
    Entailment.Independent NF (nfUpperBound k) := by
  letI : ArithmeticTheory.SoundOnHierarchy ArithmeticPullback.theory 𝚺 1 := sound
  have consistent : ConNF := ArithmeticPullback.conNF_of_consistent inferInstance
  exact ⟨no_numeral_upper_bound consistent k, upperBound_unrefutable sound k trueBound⟩

/-- In particular, the upper-bound sentence at the actual, uncomputed
value of runtime BB(210) is independent of NF under the displayed soundness
assumption. -/
theorem busyBeaver210_bound_independent
    (sound : NFSecond.ArithmeticSigmaOneSound) :
    Entailment.Independent NF (nfUpperBound (TM.busyBeaver 210)) :=
  true_upperBound_independent sound (TM.busyBeaver 210) (TM.upperBound_busyBeaver 210)

end NF210.Proof.BusyBeaver

#print NF210.Proof.BusyBeaver.no_numeral_upper_bound
#print NF210.Proof.BusyBeaver.busyBeaver210_bound_independent
#print axioms NF210.Proof.BusyBeaver.no_numeral_upper_bound
#print axioms NF210.Proof.BusyBeaver.true_upperBound_independent
#print axioms NF210.Proof.BusyBeaver.busyBeaver210_bound_independent
