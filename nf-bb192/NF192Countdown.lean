import DirectNFToNormalized
import NormalizedToComb
import NumericalModel
import SourceComplete
import CountdownSearch
import CombAll

set_option autoImplicit false

/-! The public results for the selected table. A single external import
loads the user's archived NF, FunctionNF and CombNF definitions. -/

namespace NF192

open FFL FFL.FirstOrder NF210

/-- The two model constructions relate the normalized basis to ordinary NF. -/
theorem exists_basis_iff_consistent_nf :
    (∃ A : Type, Nonempty (NormalizedBasis A)) ↔ Entailment.Consistent 𝗡𝗙 := by
  constructor
  · rintro ⟨A, ⟨S⟩⟩
    exact consistent_nf_of_consistent_comb S.comb_consistent
  · intro h
    classical
    by_contra noBasis
    apply (Entailment.consistent_iff_unprovable_bot.mp h)
    apply SetTheory.complete.{0}
    intro V _ _ _
    exact False.elim (noBasis ⟨_, ⟨SetTheory.NFFn.Normalized.ofNF (V := V)⟩⟩)

/-- The numeral at the halt check is a theorem exactly if NF is inconsistent.
The proof uses the interpretability chain through CombNF and FunctionNF. -/
theorem derives_goal_iff_nf_inconsistent :
    Numerical.Deriv Numerical.goal ↔ ¬ Entailment.Consistent 𝗡𝗙 := by
  classical
  have h := Numerical.not_deriv_goal_iff_basis.trans exists_basis_iff_consistent_nf
  exact ⟨fun d hc => h.mpr hc d, fun hi => Classical.byContradiction (fun hn => hi (h.mp hn))⟩

open ProofSearch

/-- Equivalence for the unbounded command enumerator at an arbitrary
sound refill boundary. Binary and literal register-machine simulations
can use this theorem without reproving the arithmetized proof calculus. -/
theorem command_stream_halts_iff_nf_inconsistent (start : Nat) (s : State) (hs : s.Sound) :
    (∃ ticks, streamRun ticks ⟨start,0,s⟩ = none) ↔ ¬ Entailment.Consistent 𝗡𝗙 :=
  (stream_halting_iff_goal start s hs).trans derives_goal_iff_nf_inconsistent

open Emitter

/-- The selected 3,089-instruction register machine halts from any sound
command boundary exactly when the original first-order NF is inconsistent. -/
theorem literal_source_halts_iff_nf_inconsistent (counter cursor : Nat)
    (s : ProofSearch.State) (hs : s.Sound) :
    (∃ ticks, Source.advance ticks
      (atFrame 0 (SourceSimulation.registers counter cursor s)) = Source.Config.halted) ↔
    ¬ Entailment.Consistent 𝗡𝗙 :=
  (SourceSimulation.literal_source_iff_goal counter cursor s hs).trans derives_goal_iff_nf_inconsistent

/-- The frozen two-symbol, 192-state countdown table on the all-zero tape
halts precisely if first-order New Foundations is inconsistent. -/
theorem countdown_halts_iff_nf_inconsistent :
    TM.Halts Selected.machine Selected.start ↔ ¬ Entailment.Consistent 𝗡𝗙 :=
  countdown_halts_iff_goal.trans derives_goal_iff_nf_inconsistent

/-- In Lean's metatheory the uploaded NF development also gives consistency
outright. The calibration above is independent of that extra result. -/
theorem countdown_never_halts : ¬ TM.Halts Selected.machine Selected.start := by
  intro halt
  exact countdown_halts_iff_nf_inconsistent.mp halt
    (consistent_nf_of_consistent_comb consistent_comb)

theorem countdown_halts_iff_nf_proves_bot :
    NF210.TM.Halts Selected.machine Selected.start ↔ 𝗡𝗙 ⊢ (⊥ : Sentence ℒₛₑₜ) :=
  countdown_halts_iff_nf_inconsistent.trans
    (Entailment.not_consistent_iff_inconsistent.trans Entailment.inconsistent_iff_provable_bot)

theorem basis_iff_consistent_combnf :
    (∃ A : Type, Nonempty (NormalizedBasis A)) ↔ Entailment.Consistent 𝗖𝗡𝗙 :=
  exists_basis_iff_consistent_nf.trans consistent_comb_iff_consistent_nf.symm

theorem basis_iff_consistent_functionnf :
    (∃ A : Type, Nonempty (NormalizedBasis A)) ↔ Entailment.Consistent 𝗙𝗡𝗙 :=
  exists_basis_iff_consistent_nf.trans consistent_fn_iff_consistent_nf.symm

theorem countdown_halts_iff_combnf_inconsistent :
    TM.Halts Selected.machine Selected.start ↔ ¬ Entailment.Consistent 𝗖𝗡𝗙 :=
  countdown_halts_iff_nf_inconsistent.trans consistent_comb_iff_consistent_nf.symm.not

theorem countdown_halts_iff_functionnf_inconsistent :
    TM.Halts Selected.machine Selected.start ↔ ¬ Entailment.Consistent 𝗙𝗡𝗙 :=
  countdown_halts_iff_nf_inconsistent.trans consistent_fn_iff_consistent_nf.symm.not

end NF192

#print axioms NF192.derives_goal_iff_nf_inconsistent
#print axioms NF192.command_stream_halts_iff_nf_inconsistent
#print axioms NF192.literal_source_halts_iff_nf_inconsistent
#print axioms NF192.countdown_halts_iff_nf_inconsistent
#print axioms NF192.countdown_never_halts
#print axioms NF192.countdown_halts_iff_nf_proves_bot
#print axioms NF192.basis_iff_consistent_combnf
#print axioms NF192.basis_iff_consistent_functionnf
#print axioms NF192.countdown_halts_iff_combnf_inconsistent
#print axioms NF192.countdown_halts_iff_functionnf_inconsistent
