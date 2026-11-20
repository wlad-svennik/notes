module
public import P192End
public import C193Cold
public import C193Model
public import C193Distinguishes
public import C193OldExample
@[expose] public section
namespace Counting192J
open NF210 NF192.Numerical

/-- The literal binary machine recognizes derivability of goal code 3 in
    the J-point presentation. -/
theorem halts_iff_jpoint_goal :
    TM.Halts CS192.Table.machine CS192.Table.start ↔ C193.Deriv goal :=
  P192.Physical.signed_halts_iff.trans C193.Register.signed_source_halts_iff_goal

theorem nonhalting_iff_jpoint_chart :
    (¬ TM.Halts CS192.Table.machine CS192.Table.start) ↔
      ∃ M : Type, Nonempty (NF193.Chart M) :=
  (not_congr halts_iff_jpoint_goal).trans
    (C193.not_deriv_iff_ground_model.trans C193.ground_model_iff_chart)

private theorem run_sound (w : List NF192.ProofSearch.Command) (s : C193.State)
    (hs : s.Sound) : (C193.run w s).Sound := by
  induction w generalizing s with
  | nil => exact hs
  | cons c cs ih => exact ih _ (C193.step_sound c s hs)

/-- Every proof word builds a derivable formula, and every finite derivation
    in the J-point presentation has a proof word. -/
theorem buildable_iff_jpoint_derivable (x : Nat) :
    (∃ w, C193.Builds x w) ↔ C193.Deriv x := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨c,hc⟩ := hw 0 [] 0
    have hs : (C193.State.mk 0 [] 0 0).Sound :=
      ⟨C193.deriv_zero, by simp, C193.deriv_zero⟩
    have h := run_sound w _ hs
    rw [hc] at h
    exact h.1
  · exact C193.deriv_buildable

end Counting192J
#print axioms Counting192J.halts_iff_jpoint_goal
#print axioms Counting192J.buildable_iff_jpoint_derivable

#print axioms Counting192J.nonhalting_iff_jpoint_chart
