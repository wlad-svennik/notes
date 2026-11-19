module
public import C201Counting

@[expose] public section

namespace Counting201Certificate

open NF192.Numerical
open C201 (rowList)

/-- Projections of the Cantor code used throughout the ten-row numeral calculus. -/
def left (code : Nat) : Nat := (Cantor.unpair code).1
def right (code : Nat) : Nat := (Cantor.unpair code).2

@[simp] theorem left_pair (a b : Nat) : left (pair a b) = a := by
  simp [left, Cantor.unpair_pair]
@[simp] theorem right_pair (a b : Nat) : right (pair a b) = b := by
  simp [right, Cantor.unpair_pair]

def axiomData (a b c u : Nat) : Nat := pair a (pair b (pair c u))

def leafOK (data conclusion : Nat) : Bool :=
  let a := left data
  let b := left (right data)
  let c := left (right (right data))
  let u := right (right (right data))
  decide (u ≤ a ∧ conclusion ∈ rowList a b c u)

theorem leafOK_sound {data x : Nat} (h : leafOK data x = true) : C201.Deriv x := by
  unfold leafOK at h
  exact C201.Deriv.row (of_decide_eq_true h).1 (of_decide_eq_true h).2

theorem leafOK_complete {a b c u x : Nat} (hu : u ≤ a) (hx : x ∈ rowList a b c u) :
    leafOK (axiomData a b c u) x = true := by
  simp [leafOK, axiomData, hu, hx]

/-- The test is structurally recursive on fuel. A zero tag is a ten-row leaf.
Any other tag carries the minor formula and the two child certificate codes. -/
def checkTree : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, code, x =>
    if left code = 0 then leafOK (right code) x
    else
      let data := right code
      let a := left data
      let children := right data
      checkTree fuel (left children) (imp a x) && checkTree fuel (right children) a

theorem checkTree_sound (fuel : Nat) {code x : Nat} (h : checkTree fuel code x = true) :
    C201.Deriv x := by
  induction fuel generalizing code x with
  | zero => simp [checkTree] at h
  | succ n ih =>
    by_cases hz : left code = 0
    · exact leafOK_sound (by simpa [checkTree, hz] using h)
    · simp only [checkTree, hz, ite_false, Bool.and_eq_true] at h
      exact C201.Deriv.mp (ih h.1) (ih h.2)

theorem checkTree_complete {x : Nat} (d : C201.Deriv x) :
    ∃ depth code, ∀ fuel, depth ≤ fuel → checkTree fuel code x = true := by
  induction d with
  | @row a b c u x hu hx =>
    refine ⟨1, pair 0 (axiomData a b c u), ?_⟩
    intro fuel h
    cases fuel with
    | zero => omega
    | succ n => simpa [checkTree] using leafOK_complete hu hx
  | @mp a b _ _ hmajor hminor =>
    obtain ⟨dm, cm, hm⟩ := hmajor
    obtain ⟨dn, cn, hn⟩ := hminor
    refine ⟨max dm dn + 1, pair 1 (pair a (pair cm cn)), ?_⟩
    intro fuel h
    cases fuel with
    | zero => omega
    | succ n =>
      have em : dm ≤ n := by omega
      have en : dn ≤ n := by omega
      simp [checkTree, hm n em, hn n en]

/-- A single natural number stores both the depth bound and proof tree. -/
def check (certificate conclusion : Nat) : Bool :=
  checkTree (left certificate) (right certificate) conclusion

example : check 0 0 = false := by decide

theorem derives_iff_certificate (x : Nat) : C201.Deriv x ↔ ∃ p, check p x = true := by
  constructor
  · intro d
    obtain ⟨depth, code, h⟩ := checkTree_complete d
    exact ⟨pair depth code, by simpa [check] using h depth (Nat.le_refl _)⟩
  · rintro ⟨p,h⟩
    exact checkTree_sound _ h

/-- A numeric proof code checked against the ten emitted rows is a necessary
and sufficient witness for this literal blank-tape halting event. -/
theorem halts_iff_numerical_certificate :
    NF210.TM.Halts CS201.Table.machine CS201.Table.start ↔ ∃ p, check p goal = true := by
  have h := C201.Physical.blank_iff_signed_of_realizes P201.Physical.realizes
  have s := (C201.Register.bootstrap_halts_at C201.Register.advance_steps201).symm.trans
    C201.Register.signed_source_halts_iff_goal
  exact (h.trans s).trans (derives_iff_certificate goal)

end Counting201Certificate

#print axioms Counting201Certificate.derives_iff_certificate
#print axioms Counting201Certificate.halts_iff_numerical_certificate
