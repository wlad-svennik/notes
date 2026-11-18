module

public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic

/-!
# Generic levels (new file)

This file is pure Mathlib; it does not depend on the construction.

We fix a nonprincipal ultrafilter on `ℕ` and consider *generic points* `(v, D)`, where
`v : ℤ → ℕ` is a `ℤ`-indexed sequence of natural numbers (to be used as levels) and `D : ℕ`
(to be used as a height). A predicate on generic points is *finitely supported* if it depends on
only finitely many coordinates of `v`. For such predicates we define generic truth by iterating the
ultrafilter quantifier over the coordinates in increasing order, and then over `D`.

Generic truth is a two-valued measure on finitely supported predicates. It is invariant under
shifting the sequence, and generically `v i < v j` for `i < j` and `v i + c ≤ D`.
We extend it to an ultrafilter `genW` on all generic points, so that Mathlib's filter API applies.

## Main statements

* `ConNF.NF.ev_sh`: shift invariance of `genW` on finitely supported predicates.
* `ConNF.NF.ev_lt`, `ConNF.NF.ev_le_D`: the generic order facts.
-/

@[expose] public section

open Filter

namespace ConNF.NF

/-- The fixed nonprincipal ultrafilter on `ℕ`. -/
noncomputable def genU : Ultrafilter ℕ := hyperfilter ℕ

theorem eventually_gt_genU (a : ℕ) : ∀ᶠ b in (genU : Filter ℕ), a < b := by
  have h : (genU : Filter ℕ) ≤ atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact hyperfilter_le_cofinite
  exact (eventually_gt_atTop a).filter_mono h

/-! ## Sequences indexed by `ℕ` -/

/-- Prepend a value to a sequence. -/
def cons (a : ℕ) (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => a
  | k + 1 => u k

/-- Drop the first value of a sequence. -/
def tail (u : ℕ → ℕ) : ℕ → ℕ := fun k => u (k + 1)

@[simp] theorem cons_zero (a : ℕ) (u : ℕ → ℕ) : cons a u 0 = a := rfl

@[simp] theorem cons_succ (a : ℕ) (u : ℕ → ℕ) (k : ℕ) : cons a u (k + 1) = u k := rfl

@[simp] theorem tail_cons (a : ℕ) (u : ℕ → ℕ) : tail (cons a u) = u := rfl

/-- Generic truth of a predicate that depends on the first `n` coordinates of a sequence and on a
height `D`: quantify the coordinates in order, then `D`. -/
def Gen : ℕ → ((ℕ → ℕ) → ℕ → Prop) → Prop
  | 0, P => ∀ᶠ D in (genU : Filter ℕ), P (fun _ => 0) D
  | n + 1, P => ∀ᶠ a in (genU : Filter ℕ), Gen n (fun u D => P (cons a u) D)

theorem gen_succ (n : ℕ) (P : (ℕ → ℕ) → ℕ → Prop) :
    Gen (n + 1) P ↔ ∀ᶠ a in (genU : Filter ℕ), Gen n (fun u D => P (cons a u) D) :=
  Iff.rfl

theorem gen_congr {n : ℕ} {P Q : (ℕ → ℕ) → ℕ → Prop} (h : ∀ u D, P u D ↔ Q u D) :
    Gen n P ↔ Gen n Q := by
  have : P = Q := by
    funext u D
    exact propext (h u D)
  rw [this]

theorem gen_of_forall {n : ℕ} {P : (ℕ → ℕ) → ℕ → Prop} (h : ∀ u D, P u D) : Gen n P := by
  induction n generalizing P with
  | zero => exact Eventually.of_forall fun D => h _ D
  | succ n ih => exact Eventually.of_forall fun a => ih fun u D => h _ D

theorem gen_not {n : ℕ} {P : (ℕ → ℕ) → ℕ → Prop} :
    Gen n (fun u D => ¬P u D) ↔ ¬Gen n P := by
  induction n generalizing P with
  | zero => exact Ultrafilter.eventually_not
  | succ n ih =>
    rw [gen_succ, gen_succ, ← Ultrafilter.eventually_not]
    exact eventually_congr (Eventually.of_forall fun a => ih)

theorem gen_and {n : ℕ} {P Q : (ℕ → ℕ) → ℕ → Prop} :
    Gen n (fun u D => P u D ∧ Q u D) ↔ Gen n P ∧ Gen n Q := by
  induction n generalizing P Q with
  | zero => exact eventually_and
  | succ n ih =>
    rw [gen_succ, gen_succ, gen_succ, ← eventually_and]
    exact eventually_congr (Eventually.of_forall fun a => ih)

/-- `P` depends only on the first `n` coordinates. -/
def Supp (n : ℕ) (P : (ℕ → ℕ) → ℕ → Prop) : Prop :=
  ∀ u u' D, (∀ k < n, u k = u' k) → (P u D ↔ P u' D)

theorem gen_succ_of_supp {n : ℕ} {P : (ℕ → ℕ) → ℕ → Prop} (h : Supp n P) :
    Gen (n + 1) P ↔ Gen n P := by
  induction n generalizing P with
  | zero =>
    have key : ∀ a, (∀ᶠ D in (genU : Filter ℕ), P (cons a fun _ => 0) D) ↔
        ∀ᶠ D in (genU : Filter ℕ), P (fun _ => 0) D := fun a =>
      eventually_congr (Eventually.of_forall fun D =>
        h _ _ D fun k hk => absurd hk (Nat.not_lt_zero k))
    show (∀ᶠ a in (genU : Filter ℕ), ∀ᶠ D in (genU : Filter ℕ), P (cons a fun _ => 0) D) ↔
      ∀ᶠ D in (genU : Filter ℕ), P (fun _ => 0) D
    simp only [key, eventually_const]
  | succ n ih =>
    rw [gen_succ, gen_succ (n := n)]
    refine eventually_congr (Eventually.of_forall fun a => ih ?_)
    intro u u' D huu
    refine h _ _ D ?_
    intro k hk
    cases k with
    | zero => rfl
    | succ k => exact huu k (Nat.lt_of_succ_lt_succ hk)

theorem gen_tail {n : ℕ} {P : (ℕ → ℕ) → ℕ → Prop} :
    Gen (n + 1) (fun u D => P (tail u) D) ↔ Gen n P := by
  rw [gen_succ]
  simp only [tail_cons, eventually_const]

theorem gen_gt_coord {n : ℕ} (a : ℕ) {k : ℕ} (hk : k < n) : Gen n (fun u _ => a < u k) := by
  induction k generalizing n with
  | zero =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [gen_succ]
    exact (eventually_gt_genU a).mono fun b hb => gen_of_forall fun _ _ => hb
  | succ k ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [gen_succ]
    exact Eventually.of_forall fun b => ih (by omega)

theorem gen_lt_coord {n i j : ℕ} (hij : i < j) (hj : j < n) :
    Gen n (fun u _ => u i < u j) := by
  induction i generalizing n j with
  | zero =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [gen_succ]
    exact Eventually.of_forall fun a => gen_gt_coord a (by omega)
  | succ i ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [gen_succ]
    exact Eventually.of_forall fun a => ih (by omega) (by omega)

theorem gen_le_D {n : ℕ} (f : (ℕ → ℕ) → ℕ) : Gen n (fun u D => f u ≤ D) := by
  induction n generalizing f with
  | zero => exact (eventually_gt_genU (f fun _ => 0)).mono fun D hD => hD.le
  | succ n ih =>
    rw [gen_succ]
    exact Eventually.of_forall fun a => ih fun u => f (cons a u)

/-! ## Sequences indexed by `ℤ` -/

/-- Read a window `[-N, N)` of a `ℤ`-indexed sequence off an `ℕ`-indexed one. -/
def unwin (N : ℕ) (u : ℕ → ℕ) : ℤ → ℕ := fun k => u (k + N).toNat

/-- `P` depends only on the coordinates in `[-N, N)`. -/
def SuppZ (N : ℕ) (P : (ℤ → ℕ) → ℕ → Prop) : Prop :=
  ∀ v v' D, (∀ k : ℤ, -(N : ℤ) ≤ k → k < N → v k = v' k) → (P v D ↔ P v' D)

/-- Generic truth computed in the window `[-N, N)`. -/
def GenZ (N : ℕ) (P : (ℤ → ℕ) → ℕ → Prop) : Prop :=
  Gen (2 * N) (fun u D => P (unwin N u) D)

theorem suppZ_mono {N N' : ℕ} (h : N ≤ N') {P : (ℤ → ℕ) → ℕ → Prop} (hP : SuppZ N P) :
    SuppZ N' P :=
  fun v v' D hv => hP v v' D fun k hk1 hk2 => hv k (by omega) (by omega)

theorem supp_unwin {N : ℕ} {P : (ℤ → ℕ) → ℕ → Prop} (hP : SuppZ N P) :
    Supp (2 * N) (fun u D => P (unwin N u) D) := by
  intro u u' D h
  refine hP _ _ D fun k hk1 hk2 => ?_
  exact h _ (by omega)

theorem genZ_succ {N : ℕ} {P : (ℤ → ℕ) → ℕ → Prop} (hP : SuppZ N P) :
    GenZ (N + 1) P ↔ GenZ N P := by
  have h1 : GenZ (N + 1) P ↔
      Gen (2 * N + 1 + 1) (fun u D => P (unwin N (tail u)) D) := by
    refine gen_congr fun u D => hP _ _ D fun k hk1 hk2 => ?_
    show u ((k + ((N + 1 : ℕ) : ℤ)).toNat) = u ((k + (N : ℤ)).toNat + 1)
    congr 1
    omega
  rw [h1, gen_tail (P := fun u D => P (unwin N u) D), gen_succ_of_supp (supp_unwin hP)]
  rfl

theorem genZ_of_le {N N' : ℕ} (h : N ≤ N') {P : (ℤ → ℕ) → ℕ → Prop} (hP : SuppZ N P) :
    GenZ N' P ↔ GenZ N P := by
  induction N', h using Nat.le_induction with
  | base => rfl
  | succ M hM ih => rw [genZ_succ (suppZ_mono hM hP), ih]

/-- Shift a `ℤ`-indexed sequence by `m`. -/
def sh (m : ℤ) (v : ℤ → ℕ) : ℤ → ℕ := fun k => v (k + m)

@[simp] theorem sh_apply (m : ℤ) (v : ℤ → ℕ) (k : ℤ) : sh m v k = v (k + m) := rfl

@[simp] theorem sh_zero (v : ℤ → ℕ) : sh 0 v = v := by
  funext k
  simp [sh]

theorem sh_sh (a b : ℤ) (v : ℤ → ℕ) : sh a (sh b v) = sh (a + b) v := by
  funext k
  simp [sh, add_assoc]

theorem suppZ_sh {N : ℕ} {P : (ℤ → ℕ) → ℕ → Prop} (hP : SuppZ N P) (m : ℤ) :
    SuppZ (N + m.natAbs) (fun v D => P (sh m v) D) := by
  intro v v' D hv
  refine hP _ _ D fun k hk1 hk2 => ?_
  exact hv (k + m) (by omega) (by omega)

theorem genZ_sh1 {N : ℕ} {P : (ℤ → ℕ) → ℕ → Prop} (hP : SuppZ N P) :
    GenZ (N + 1) (fun v D => P (sh 1 v) D) ↔ GenZ N P := by
  have h1 : GenZ (N + 1) (fun v D => P (sh 1 v) D) ↔
      Gen (2 * N + 1 + 1) (fun u D => P (unwin N (tail (tail u))) D) := by
    refine gen_congr fun u D => hP _ _ D fun k hk1 hk2 => ?_
    show u ((k + 1 + ((N + 1 : ℕ) : ℤ)).toNat) = u ((k + (N : ℤ)).toNat + 1 + 1)
    congr 1
    omega
  rw [h1, gen_tail (P := fun u D => P (unwin N (tail u)) D),
    gen_tail (P := fun u D => P (unwin N u) D)]
  rfl

/-! ## Generic truth of finitely supported predicates -/

/-- `P` depends on only finitely many coordinates of the sequence. -/
def FinSupp (P : (ℤ → ℕ) → ℕ → Prop) : Prop := ∃ N, SuppZ N P

/-- Generic truth of a finitely supported predicate. -/
def Forces (P : (ℤ → ℕ) → ℕ → Prop) : Prop := ∃ N, SuppZ N P ∧ GenZ N P

theorem forces_iff {N : ℕ} {P : (ℤ → ℕ) → ℕ → Prop} (hP : SuppZ N P) : Forces P ↔ GenZ N P := by
  constructor
  · rintro ⟨N', hP', hG⟩
    have h1 := genZ_of_le (le_max_left N N') hP
    have h2 := genZ_of_le (le_max_right N N') hP'
    exact h1.mp (h2.mpr hG)
  · exact fun h => ⟨N, hP, h⟩

theorem FinSupp.not {P : (ℤ → ℕ) → ℕ → Prop} (h : FinSupp P) : FinSupp (fun v D => ¬P v D) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun v v' D hv => not_congr (hN v v' D hv)⟩

theorem FinSupp.and {P Q : (ℤ → ℕ) → ℕ → Prop} (hP : FinSupp P) (hQ : FinSupp Q) :
    FinSupp (fun v D => P v D ∧ Q v D) := by
  obtain ⟨N, hN⟩ := hP
  obtain ⟨M, hM⟩ := hQ
  exact ⟨max N M, fun v v' D hv => and_congr
    (suppZ_mono (le_max_left N M) hN v v' D hv) (suppZ_mono (le_max_right N M) hM v v' D hv)⟩

theorem FinSupp.sh {P : (ℤ → ℕ) → ℕ → Prop} (hP : FinSupp P) (m : ℤ) :
    FinSupp (fun v D => P (sh m v) D) := by
  obtain ⟨N, hN⟩ := hP
  exact ⟨_, suppZ_sh hN m⟩

theorem forces_not {P : (ℤ → ℕ) → ℕ → Prop} (h : FinSupp P) :
    Forces (fun v D => ¬P v D) ↔ ¬Forces P := by
  obtain ⟨N, hN⟩ := h
  have hN' : SuppZ N (fun v D => ¬P v D) := fun v v' D hv => not_congr (hN v v' D hv)
  rw [forces_iff hN, forces_iff hN']
  exact gen_not

theorem forces_and {P Q : (ℤ → ℕ) → ℕ → Prop} (hP : FinSupp P) (hQ : FinSupp Q) :
    Forces (fun v D => P v D ∧ Q v D) ↔ Forces P ∧ Forces Q := by
  obtain ⟨N, hN⟩ := hP
  obtain ⟨M, hM⟩ := hQ
  have hN' := suppZ_mono (le_max_left N M) hN
  have hM' := suppZ_mono (le_max_right N M) hM
  have hPQ : SuppZ (max N M) (fun v D => P v D ∧ Q v D) :=
    fun v v' D hv => and_congr (hN' v v' D hv) (hM' v v' D hv)
  rw [forces_iff hPQ, forces_iff hN', forces_iff hM']
  exact gen_and

theorem forces_of_forall {P : (ℤ → ℕ) → ℕ → Prop} (h : ∀ v D, P v D) : Forces P :=
  ⟨0, fun _ _ _ _ => ⟨fun _ => h _ _, fun _ => h _ _⟩, gen_of_forall fun _ _ => h _ _⟩

theorem forces_sh1 {P : (ℤ → ℕ) → ℕ → Prop} (hP : FinSupp P) :
    Forces (fun v D => P (sh 1 v) D) ↔ Forces P := by
  obtain ⟨N, hN⟩ := hP
  have hS : SuppZ (N + 1) (fun v D => P (sh 1 v) D) := suppZ_sh hN 1
  rw [forces_iff hS, forces_iff hN]
  exact genZ_sh1 hN

/-! ## The ultrafilter of generic points -/

/-- Generic points: a `ℤ`-indexed sequence of levels and a height. -/
abbrev Pt : Type := (ℤ → ℕ) × ℕ

/-- The filter generated by the generically true finitely supported predicates. -/
def genFilter : Filter Pt where
  sets := {s | ∃ P, FinSupp P ∧ Forces P ∧ ∀ p : Pt, P p.1 p.2 → p ∈ s}
  univ_sets := ⟨fun _ _ => True, ⟨0, fun _ _ _ _ => Iff.rfl⟩,
    forces_of_forall fun _ _ => trivial, fun _ _ => Set.mem_univ _⟩
  sets_of_superset := by
    rintro s t ⟨P, hP, hF, hs⟩ hst
    exact ⟨P, hP, hF, fun p hp => hst (hs p hp)⟩
  inter_sets := by
    rintro s t ⟨P, hP, hF, hs⟩ ⟨Q, hQ, hG, ht⟩
    exact ⟨fun v D => P v D ∧ Q v D, hP.and hQ, (forces_and hP hQ).mpr ⟨hF, hG⟩,
      fun p hp => ⟨hs p hp.1, ht p hp.2⟩⟩

instance genFilter_neBot : NeBot genFilter := by
  rw [neBot_iff, Ne, ← empty_mem_iff_bot]
  rintro ⟨P, hP, hF, hs⟩
  have hfalse : Forces (fun v D => ¬P v D) := forces_of_forall fun v D h => hs (v, D) h
  exact (forces_not hP).mp hfalse hF

/-- The ultrafilter of generic points. On finitely supported predicates it agrees with generic
truth (`ev_iff_forces`). -/
noncomputable def genW : Ultrafilter Pt := Ultrafilter.of genFilter

theorem ev_of_forces {P : (ℤ → ℕ) → ℕ → Prop} (hP : FinSupp P) (h : Forces P) :
    ∀ᶠ p in (genW : Filter Pt), P p.1 p.2 :=
  Ultrafilter.of_le genFilter (show {p : Pt | P p.1 p.2} ∈ genFilter from ⟨P, hP, h, fun _ hp => hp⟩)

theorem ev_iff_forces {P : (ℤ → ℕ) → ℕ → Prop} (hP : FinSupp P) :
    (∀ᶠ p in (genW : Filter Pt), P p.1 p.2) ↔ Forces P := by
  constructor
  · intro h
    by_contra hF
    have h' := ev_of_forces hP.not ((forces_not hP).mpr hF)
    obtain ⟨p, hp1, hp2⟩ := (h.and h').exists
    exact hp2 hp1
  · exact ev_of_forces hP

theorem ev_sh1 {P : (ℤ → ℕ) → ℕ → Prop} (hP : FinSupp P) :
    (∀ᶠ p in (genW : Filter Pt), P (sh 1 p.1) p.2) ↔ ∀ᶠ p in (genW : Filter Pt), P p.1 p.2 := by
  rw [ev_iff_forces hP, ev_iff_forces (P := fun v D => P (sh 1 v) D) (hP.sh 1), forces_sh1 hP]

theorem ev_sh_nat {P : (ℤ → ℕ) → ℕ → Prop} (hP : FinSupp P) (m : ℕ) :
    (∀ᶠ p in (genW : Filter Pt), P (sh (m : ℤ) p.1) p.2) ↔
      ∀ᶠ p in (genW : Filter Pt), P p.1 p.2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have key : ∀ v : ℤ → ℕ, sh ((m + 1 : ℕ) : ℤ) v = sh (m : ℤ) (sh 1 v) := by
      intro v
      rw [sh_sh]
      push_cast
      rfl
    simp only [key]
    rw [ev_sh1 (P := fun v D => P (sh (m : ℤ) v) D) (hP.sh m)]
    exact ih

/-- **Shift invariance.** A finitely supported predicate is generically true iff its shift is. -/
theorem ev_sh {P : (ℤ → ℕ) → ℕ → Prop} (hP : FinSupp P) (m : ℤ) :
    (∀ᶠ p in (genW : Filter Pt), P (sh m p.1) p.2) ↔ ∀ᶠ p in (genW : Filter Pt), P p.1 p.2 := by
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · exact ev_sh_nat hP n
  · have := ev_sh_nat (P := fun v D => P (sh (-(n : ℤ)) v) D) (hP.sh _) n
    simp only [sh_sh, neg_add_cancel, sh_zero] at this
    exact this.symm

/-- Generically, the sequence of levels is increasing. -/
theorem ev_lt {i j : ℤ} (h : i < j) : ∀ᶠ p in (genW : Filter Pt), p.1 i < p.1 j := by
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, -(N : ℤ) ≤ i ∧ j < N :=
    ⟨i.natAbs + j.natAbs + 1, by omega, by omega⟩
  have hS : SuppZ N (fun v _ => v i < v j) := by
    intro v v' D hv
    show v i < v j ↔ v' i < v' j
    rw [hv i (by omega) (by omega), hv j (by omega) (by omega)]
  refine ev_of_forces ⟨N, hS⟩ ((forces_iff hS).mpr ?_)
  show Gen (2 * N) (fun u _ => u (i + N).toNat < u (j + N).toNat)
  exact gen_lt_coord (by omega) (by omega)

/-- Generically, the height exceeds any fixed level by any fixed amount. -/
theorem ev_le_D (i : ℤ) (c : ℕ) : ∀ᶠ p in (genW : Filter Pt), p.1 i + c ≤ p.2 := by
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, -(N : ℤ) ≤ i ∧ i < N := ⟨i.natAbs + 1, by omega, by omega⟩
  have hS : SuppZ N (fun v D => v i + c ≤ D) := by
    intro v v' D hv
    show v i + c ≤ D ↔ v' i + c ≤ D
    rw [hv i (by omega) (by omega)]
  refine ev_of_forces ⟨N, hS⟩ ((forces_iff hS).mpr ?_)
  show Gen (2 * N) (fun u D => u (i + N).toNat + c ≤ D)
  exact gen_le_D fun u => u (i + N).toNat + c

end ConNF.NF
