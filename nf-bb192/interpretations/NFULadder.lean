module

public import ConNF.NF.NFUArith

/-!
# Ladders, recursion into a set, and coding of finite sets (§2.1 and §3.2 of the note)

This file continues `NFUArith`. It works in an arbitrary model `M` of NFU + Infinity.

* **Recursion into an arbitrary set** (`exists_rec_set`, `rec_set_unique`): for a set `D`,
  `a ∈ D` and a set function `G : D → D` there is a unique set function `f : ℕ → D` with
  `f 0 = a` and `f (n + 1) = G (f n)`.
* **Ladders** (`IsLadder`): a sequence of sets `T₀, …, T_m` with relations `Eᵢ` such that every
  subset of `Tᵢ` is the `Eᵢ`-extension of exactly one member of `Tᵢ₊₁`, with a zero and an
  injective successor on `T₀` satisfying induction for all sets.
* **Lemma 3.1** (`lemma_3_1`, `exists_ladder`, `ladder_base_iso`): for every calm `n` there is
  a ladder of height `n`, and the base of a ladder is isomorphic to `ℕ` by a set bijection.
* **Coding of finite sets** (`exists_code`, `exists_code_rel`): every finite set of natural
  numbers, and every finite relation between natural numbers, is coded by a natural number
  through its binary digits (`Bit`), with the pairing `(x + y)² + x` for relations.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

@[expose] public section

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

/-! ## Recursion into an arbitrary set -/

/-- `G` is the graph of a function from `D` to `D`. -/
def FunOn (G D : V) : Prop :=
  ∀ u, M.mem u D → ∃ v, M.mem v D ∧ M.mem (M.op u v) G ∧ ∀ v', M.mem (M.op u v') G → v' = v

/-- `r` contains `⟨0, a⟩` and is closed under `⟨n, u⟩ ↦ ⟨n + 1, G u⟩`. -/
def ClosedS (G D a r : V) : Prop :=
  M.mem (M.op M.zero a) r ∧
  ∀ n u v s, (M.mem n M.nat ∧ M.mem (M.op n u) r ∧ M.mem u D ∧ M.mem (M.op u v) G ∧
    s = M.succ n) → M.mem (M.op s v) r

def recSFml : Fml :=
  .all 5 (Fml.imp
    (.and (fApp 5 3 6)
      (.all 7 (.all 8 (.all 9 (.all 10 (Fml.imp
        (.and (.mem 7 4) (.and (fApp 5 7 8) (.and (.mem 8 2) (.and (fApp 1 8 9)
          (fSuccEq 10 7)))))
        (fApp 5 10 9)))))))
    (.mem 0 5))

def totSFml : Fml := Fml.ex 8 (.and (.mem 8 2) (fApp 5 0 8))

theorem sat_totSFml (D A n : V) :
    Sat M.mem M.isSet totSFml (Function.update (Function.update (Function.update (fun _ => dflt)
      2 D) 5 A) 0 n) ↔ ∃ u, M.mem u D ∧ M.mem (M.op n u) A := by
  simp [totSFml, Sat, M.sat_ex, M.sat_fApp, Function.update_apply]

/-- Every pair of the recursion set arises from one of the two clauses. -/
def InvS (G D a A p : V) : Prop :=
  M.mem p A ∧ ∃ n u, p = M.op n u ∧ M.mem n M.nat ∧ M.mem u D ∧ (n = M.zero → u = a) ∧
    ∀ n', (M.mem n' M.nat ∧ n = M.succ n') →
      ∃ w, M.mem (M.op n' w) A ∧ M.mem w D ∧ M.mem (M.op w u) G

def invSFml : Fml :=
  .and (.mem 0 5) (Fml.ex 7 (Fml.ex 8 (.and (fPr 0 7 8) (.and (.mem 7 4) (.and (.mem 8 2)
    (.and (Fml.imp (.eq 7 3) (.eq 8 6))
      (.all 12 (Fml.imp (.and (.mem 12 4) (fSuccEq 7 12))
        (Fml.ex 11 (.and (fApp 5 12 11) (.and (.mem 11 2) (fApp 1 11 8))))))))))))

def uniqSFml : Fml :=
  .all 8 (.all 9 (Fml.imp (fApp 5 0 8) (Fml.imp (fApp 5 0 9) (.eq 8 9))))

theorem sat_uniqSFml (A n : V) :
    Sat M.mem M.isSet uniqSFml (Function.update (Function.update (fun _ => dflt) 5 A) 0 n) ↔
    ∀ u u', M.mem (M.op n u) A → M.mem (M.op n u') A → u = u' := by
  simp [uniqSFml, Sat, M.sat_imp, M.sat_fApp, Function.update_apply]

/-- **Recursion into a set.** For a set `D`, `a ∈ D` and a function `G : D → D` that is a
set, there is a set `f` of pairs that is a function from the natural numbers to `D` with
`f 0 = a` and `f (n + 1) = G (f n)`. -/
theorem exists_rec_set {D a G : V} (ha : M.mem a D) (hG : M.FunOn G D) :
    ∃ f, (∀ n : M.Num, ∃ u, M.mem u D ∧ M.mem (M.op n.1 u) f ∧
        ∀ u', M.mem (M.op n.1 u') f → u' = u) ∧
      M.mem (M.op M.zero a) f ∧
      ∀ (n : M.Num) (u v : V), M.mem (M.op n.1 u) f → M.mem (M.op u v) G →
        M.mem (M.op (M.succ n.1) v) f := by
  obtain ⟨A, -, hA0⟩ := M.comp (σW [(0, 4), (1, 5), (2, 3), (4, 3), (5, 5)]) recSFml 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 G) 2 D) 3 M.zero) 4 M.nat) 6 a)
  have hA : ∀ p, M.mem p A ↔ ∀ r, M.ClosedS G D a r → M.mem p r := by
    intro p
    rw [hA0 p]
    simp [recSFml, ClosedS, Sat, M.sat_imp, M.sat_fApp, M.sat_fSuccEq, Function.update_apply]
  have hcl : M.ClosedS G D a A :=
    ⟨(hA _).mpr fun r hr => hr.1, fun n u v s ⟨hn, h1, hu, h2, hs⟩ =>
      (hA _).mpr fun r hr => hr.2 n u v s ⟨hn, (hA _).mp h1 r hr, hu, h2, hs⟩⟩
  -- totality
  have tot : ∀ n : M.Num, ∃ u, M.mem u D ∧ M.mem (M.op n.1 u) A := by
    intro n
    have h0 : Sat M.mem M.isSet totSFml (Function.update (Function.update (Function.update
        (fun _ => dflt) 2 D) 5 A) 0 M.zero) := (M.sat_totSFml D A _).mpr ⟨a, ha, hcl.1⟩
    have hs : ∀ k : M.Num, Sat M.mem M.isSet totSFml (Function.update (Function.update
        (Function.update (fun _ => dflt) 2 D) 5 A) 0 k.1) →
        Sat M.mem M.isSet totSFml (Function.update (Function.update (Function.update
        (fun _ => dflt) 2 D) 5 A) 0 (M.succ k.1)) := by
      intro k ih
      rw [M.sat_totSFml] at ih ⊢
      obtain ⟨u, hu, hu'⟩ := ih
      obtain ⟨v, hv, hv', -⟩ := hG u hu
      exact ⟨v, hv, hcl.2 k.1 u v _ ⟨k.2, hu', hu, hv', rfl⟩⟩
    have key := M.num_ind_fml (σW [(2, 3), (5, 5)]) totSFml 0 rfl _ h0 hs n
    exact (M.sat_totSFml D A _).mp key
  -- inversion
  obtain ⟨B, -, hB0⟩ := M.comp (σW [(0, 4), (1, 5), (2, 3), (4, 3), (5, 5)]) invSFml 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (fun _ => dflt) 1 G) 2 D) 3 M.zero) 4 M.nat) 5 A) 6 a)
  have hB : ∀ p, M.mem p B ↔ M.InvS G D a A p := by
    intro p
    rw [hB0 p]
    simp [invSFml, InvS, Sat, M.sat_imp, M.sat_ex, M.sat_fPr, M.sat_fApp, M.sat_fSuccEq,
      Function.update_apply]
  have hBcl : M.ClosedS G D a B := by
    constructor
    · exact (hB _).mpr ⟨hcl.1, M.zero, a, rfl, M.zero_mem_nat, ha, fun _ => rfl,
        fun n' h => absurd h.2 (M.zero_ne_succ n')⟩
    · rintro n u v s ⟨hn, h1, hu, h2, hs⟩
      have h1A := ((hB _).mp h1).1
      obtain ⟨v0, hv0, -, hv0u⟩ := hG u hu
      have hvD : M.mem v D := by
        rw [hv0u v h2]
        exact hv0
      refine (hB _).mpr ⟨hcl.2 n u v s ⟨hn, h1A, hu, h2, hs⟩, s, v, rfl, ?_, hvD, ?_, ?_⟩
      · rw [hs]
        exact M.succ_mem_nat hn
      · intro hs0
        rw [hs] at hs0
        exact absurd hs0.symm (M.zero_ne_succ n)
      · rintro n' ⟨hn', hsn'⟩
        rw [hs] at hsn'
        have e : n = n' := M.succ_inj hn hn' hsn'
        rw [← e]
        exact ⟨u, h1A, hu, h2⟩
  have inv : ∀ p, M.mem p A → M.InvS G D a A p := fun p hp =>
    (hB p).mp ((hA p).mp hp B hBcl)
  -- uniqueness
  have uniq : ∀ (n : M.Num) (u u' : V), M.mem (M.op n.1 u) A → M.mem (M.op n.1 u') A →
      u = u' := by
    intro n
    have h0 : Sat M.mem M.isSet uniqSFml
        (Function.update (Function.update (fun _ => dflt) 5 A) 0 M.zero) := by
      rw [M.sat_uniqSFml]
      intro u u' h1 h2
      obtain ⟨-, n1, u1, e, -, -, hz, -⟩ := inv _ h1
      obtain ⟨-, n2, u2, e', -, -, hz', -⟩ := inv _ h2
      obtain ⟨en, eu⟩ := M.op_inj e
      obtain ⟨en', eu'⟩ := M.op_inj e'
      rw [eu, eu', hz en.symm, hz' en'.symm]
    have hs : ∀ k : M.Num, Sat M.mem M.isSet uniqSFml
        (Function.update (Function.update (fun _ => dflt) 5 A) 0 k.1) →
        Sat M.mem M.isSet uniqSFml
        (Function.update (Function.update (fun _ => dflt) 5 A) 0 (M.succ k.1)) := by
      intro k ih
      rw [M.sat_uniqSFml] at ih ⊢
      intro u u' h1 h2
      obtain ⟨-, n1, u1, e, -, -, -, hst⟩ := inv _ h1
      obtain ⟨-, n2, u2, e', -, -, -, hst'⟩ := inv _ h2
      obtain ⟨en, eu⟩ := M.op_inj e
      obtain ⟨en', eu'⟩ := M.op_inj e'
      obtain ⟨w, hw1, hwD, hw2⟩ := hst k.1 ⟨k.2, en.symm⟩
      obtain ⟨w', hw1', hwD', hw2'⟩ := hst' k.1 ⟨k.2, en'.symm⟩
      have eww : w = w' := ih w w' hw1 hw1'
      rw [← eww] at hw2'
      obtain ⟨v, -, -, hv⟩ := hG w hwD
      rw [eu, eu', hv u1 hw2, hv u2 hw2']
    have key := M.num_ind_fml (σW [(5, 5)]) uniqSFml 0 rfl _ h0 hs n
    rw [M.sat_uniqSFml] at key
    exact key
  refine ⟨A, fun n => ?_, hcl.1, fun n u v h1 h2 => ?_⟩
  · obtain ⟨u, hu, hu'⟩ := tot n
    exact ⟨u, hu, hu', fun u' h => uniq n u' u h hu'⟩
  · obtain ⟨u0, hu0, hu0'⟩ := tot n
    have e : u = u0 := uniq n u u0 h1 hu0'
    rw [e] at h2
    exact hcl.2 n.1 u0 v _ ⟨n.2, hu0', hu0, h2, rfl⟩

def agreeFml : Fml := .all 8 (Fml.imp (fApp 5 0 8) (fApp 1 0 8))

theorem sat_agreeFml (f f' n : V) :
    Sat M.mem M.isSet agreeFml (Function.update (Function.update (Function.update (fun _ => dflt)
      5 f) 1 f') 0 n) ↔ ∀ u, M.mem (M.op n u) f → M.mem (M.op n u) f' := by
  simp [agreeFml, Sat, M.sat_imp, M.sat_fApp, Function.update_apply]

/-- The function defined by recursion into a set is unique. -/
theorem rec_set_unique {D a G f f' : V} (hG : M.FunOn G D)
    (hf : ∀ n : M.Num, ∃ u, M.mem u D ∧ M.mem (M.op n.1 u) f ∧
      ∀ u', M.mem (M.op n.1 u') f → u' = u)
    (hf0 : M.mem (M.op M.zero a) f)
    (hfs : ∀ (n : M.Num) (u v : V), M.mem (M.op n.1 u) f → M.mem (M.op u v) G →
      M.mem (M.op (M.succ n.1) v) f)
    (hf0' : M.mem (M.op M.zero a) f')
    (hfs' : ∀ (n : M.Num) (u v : V), M.mem (M.op n.1 u) f' → M.mem (M.op u v) G →
      M.mem (M.op (M.succ n.1) v) f')
    (n : M.Num) (u : V) (h : M.mem (M.op n.1 u) f) : M.mem (M.op n.1 u) f' := by
  have h0 : Sat M.mem M.isSet agreeFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 5 f) 1 f') 0 M.zero) := by
    rw [M.sat_agreeFml]
    intro u hu
    obtain ⟨u0, -, -, huniq⟩ := hf M.nzero
    rw [huniq u hu, ← huniq a hf0]
    exact hf0'
  have hs : ∀ k : M.Num, Sat M.mem M.isSet agreeFml (Function.update (Function.update
      (Function.update (fun _ => dflt) 5 f) 1 f') 0 k.1) →
      Sat M.mem M.isSet agreeFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 5 f) 1 f') 0 (M.succ k.1)) := by
    intro k ih
    rw [M.sat_agreeFml] at ih ⊢
    intro u hu
    obtain ⟨w, hwD, hw, -⟩ := hf k
    obtain ⟨v, -, hwv, -⟩ := hG w hwD
    obtain ⟨u0, -, -, huniq⟩ := hf (M.nsucc k)
    rw [huniq u hu, ← huniq v (hfs k w v hw hwv)]
    exact hfs' k w v (ih w hw) hwv
  have key := M.num_ind_fml (σW [(1, 5), (5, 5)]) agreeFml 0 rfl _ h0 hs n
  rw [M.sat_agreeFml] at key
  exact key u h

/-! ## Ladders (§3.2 of the note) -/

/-! ### Order facts -/

theorem le_add_one (k : M.Num) : k ≤ k + 1 := M.le_def.mpr ⟨1, rfl⟩

theorem not_succ_le (k : M.Num) : ¬ k + 1 ≤ k := by
  intro h
  obtain ⟨c, hc⟩ := M.le_def.mp h
  have h1 : M.addN k (c + 1) = M.addN k 0 := by
    show k + (c + 1) = k + 0
    rw [add_zero]
    exact (by ring : k + (c + 1) = k + 1 + c).trans hc
  exact M.peano.1 c (M.addN_left_cancel h1)

theorem le_of_succ_le_succ {j m : M.Num} (h : j + 1 ≤ m + 1) : j ≤ m := by
  obtain ⟨c, hc⟩ := M.le_def.mp h
  exact M.le_def.mpr ⟨c, M.peano.2.1 _ _ ((by ring : j + c + 1 = j + 1 + c).trans hc)⟩

theorem eq_or_succ_le {j m : M.Num} (h : j ≤ m) : j = m ∨ j + 1 ≤ m := by
  obtain ⟨c, hc⟩ := M.le_def.mp h
  rcases M.num_cases c with h0 | ⟨c', hc'⟩
  · left
    rw [h0] at hc
    exact (M.addN_zero j).symm.trans hc
  · right
    rw [hc', M.nsucc_eq_add_one] at hc
    exact M.le_def.mpr ⟨c', (by ring : j + 1 + c' = j + (c' + 1)).trans hc⟩

theorem val_add_one (m : M.Num) : (m + 1).1 = M.succ m.1 := by
  rw [← M.nsucc_eq_add_one]
  rfl

/-! ### The relation `T i = j` between numbers given as objects -/

/-- Some member of `i` has its singleton image in `j`. -/
def TRel (i j : V) : Prop := ∃ y, M.mem y i ∧ M.mem (M.simg y) j

/-- For a calm number `i`, the only natural number `j` with `T i = j` is `i`. -/
theorem TRel_iff_of_inS {i : M.Num} (hi : M.InS i.1) {j : V} (hj : M.mem j M.nat) :
    M.TRel i.1 j ↔ j = i.1 := by
  constructor
  · rintro ⟨y, hy, hyj⟩
    have h1 : M.mem (M.simg y) (M.T i).1 := M.simg_mem_T hy
    rw [M.T_eq_self_of_inS hi] at h1
    exact M.nat_disjoint hj i.2 hyj h1
  · intro e
    obtain ⟨y, hy⟩ := M.nat_nonempty i.2
    have h1 : M.mem (M.simg y) (M.T i).1 := M.simg_mem_T hy
    rw [M.T_eq_self_of_inS hi] at h1
    rw [e]
    exact ⟨y, hy, h1⟩

/-- `T i = j`, with bound names `8`, `9`, `12`–`14`. -/
def fT (i j : ℕ) : Fml :=
  Fml.ex 8 (.and (.mem 8 i) (Fml.ex 9 (.and
    (.and (.set 9) (.all 12 (Fml.iff (.mem 12 9) (Fml.ex 13 (.and (.mem 13 8) (fSing 12 13 14))))))
    (.mem 9 j))))

theorem sat_fT {i j : ℕ} (ρ : ℕ → V) (hi : i < 8) (hj : j < 8) :
    Sat M.mem M.isSet (fT i j) ρ ↔ M.TRel (ρ i) (ρ j) := by
  have h1 : i ≠ 8 := by omega
  have h2 : j ≠ 8 := by omega
  have h3 : j ≠ 9 := by omega
  have h : Sat M.mem M.isSet (fT i j) ρ ↔ ∃ y, M.mem y (ρ i) ∧ ∃ S, (M.isSet S ∧
      ∀ s, M.mem s S ↔ ∃ a, M.mem a y ∧ s = M.sing a) ∧ M.mem S (ρ j) := by
    simp only [fT, Sat, M.sat_iff, M.sat_ex,
      M.sat_fSing (u := 12) (a := 13) (c := 14) (by decide) (by decide)]
    simp [Function.update_apply, h1, h2, h3]
  rw [h]
  constructor
  · rintro ⟨y, hy, S, hS, hSj⟩
    rw [M.eq_simg_iff.mp hS] at hSj
    exact ⟨y, hy, hSj⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, _, ⟨M.simg_isSet y, fun s => M.mem_simg⟩, h⟩

/-- `q = ⟨a, b, c⟩` for components one type higher, with bound names `52`–`57`. -/
def fTripH (q a b c : ℕ) : Fml :=
  Fml.ex 52 (Fml.ex 53 (.and (fOp q 52 53 54 55) (.and (fOp 52 a b 56 57) (fOp 53 c c 56 57))))

theorem sat_fTripH {q a b c : ℕ} (ρ : ℕ → V) (hq : q < 30) (ha : a < 30) (hb : b < 30)
    (hc : c < 30) :
    Sat M.mem M.isSet (fTripH q a b c) ρ ↔ ρ q = M.trip (ρ a) (ρ b) (ρ c) := by
  have q52 : q ≠ 52 := by omega
  have q53 : q ≠ 53 := by omega
  have a52 : a ≠ 52 := by omega
  have a53 : a ≠ 53 := by omega
  have b52 : b ≠ 52 := by omega
  have b53 : b ≠ 53 := by omega
  have c52 : c ≠ 52 := by omega
  have c53 : c ≠ 53 := by omega
  simp only [fTripH, M.sat_ex, Sat,
    M.sat_fOp (p := q) (a := 52) (b := 53) (u := 54) (c := 55) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    M.sat_fOp (p := 52) (a := a) (b := b) (u := 56) (c := 57) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    M.sat_fOp (p := 53) (a := c) (b := c) (u := 56) (c := 57) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    Function.update_self, Function.update_of_ne q52, Function.update_of_ne q53,
    Function.update_of_ne a52, Function.update_of_ne a53, Function.update_of_ne b52,
    Function.update_of_ne b53, Function.update_of_ne c52, Function.update_of_ne c53,
    Function.update_of_ne (show (52 : ℕ) ≠ 53 by decide)]
  unfold trip
  constructor
  · rintro ⟨p1, p2, h1, rfl, rfl⟩
    exact h1
  · intro h
    exact ⟨_, _, h, rfl, rfl⟩

theorem exists_unsing (X : V) : ∃ x, M.isSet x ∧ ∀ a, M.mem a x ↔ M.mem (M.sing a) X := by
  obtain ⟨x, hx, h⟩ := M.comp (fun i => if i = 1 then 2 else if i = 2 then 1 else 0)
    (Fml.ex 2 (.and (fSing 2 0 3) (.mem 2 1))) 0 rfl (Function.update (fun _ => dflt) 1 X)
  refine ⟨x, hx, fun a => ?_⟩
  rw [h a]
  simp [M.sat_ex, Sat, M.sat_fSing, Function.update_apply]

/-- `{a : {a} ∈ X}`. -/
noncomputable def unsing (X : V) : V := Classical.choose (M.exists_unsing X)

theorem unsing_isSet (X : V) : M.isSet (M.unsing X) :=
  (Classical.choose_spec (M.exists_unsing X)).1

theorem mem_unsing {X a : V} : M.mem a (M.unsing X) ↔ M.mem (M.sing a) X :=
  (Classical.choose_spec (M.exists_unsing X)).2 a

/-! ### The definition -/

/-- **A ladder of height `m`.** `R` is the set of pairs `⟨i, a⟩` with `a` in rung `i`, for
`i ≤ m`; `E` is the set of triples `⟨i, a, b⟩` with `a` in rung `i`, `b` in rung `i + 1` and
`a E b`; `z` and `S` are a zero and a successor on rung `0`. Rung `0` satisfies the Peano
axioms with induction for every set, and every set of members of rung `i`, for `i < m`, is
the extension of exactly one member of rung `i + 1`. -/
structure IsLadder (R E z S : V) (m : M.Num) : Prop where
  idx : ∀ i a, M.mem (M.op i a) R → ∃ j : M.Num, j.1 = i ∧ j ≤ m
  eidx : ∀ i a b, M.mem (M.trip i a b) E → ∃ j : M.Num, j.1 = i ∧ j + 1 ≤ m
  zero_mem : M.mem (M.op M.zero z) R
  succ_fun : ∀ a, M.mem (M.op M.zero a) R → ∃ b, M.mem (M.op M.zero b) R ∧
    M.mem (M.op a b) S ∧ ∀ b', M.mem (M.op a b') S → b' = b
  succ_inj : ∀ a a' b, M.mem (M.op a b) S → M.mem (M.op a' b) S → a = a'
  zero_ne : ∀ a, ¬ M.mem (M.op a z) S
  ind : ∀ x, M.mem z x → (∀ a b, M.mem a x → M.mem (M.op a b) S → M.mem b x) →
    ∀ a, M.mem (M.op M.zero a) R → M.mem a x
  full : ∀ i : M.Num, i + 1 ≤ m → ∀ x, M.isSet x → (∀ a, M.mem a x → M.mem (M.op i.1 a) R) →
    ∃ b, M.mem (M.op (i + 1).1 b) R ∧
      (∀ a, M.mem a x ↔ M.mem (M.op i.1 a) R ∧ M.mem (M.trip i.1 a b) E) ∧
      ∀ b', M.mem (M.op (i + 1).1 b') R →
        (∀ a, M.mem a x ↔ M.mem (M.op i.1 a) R ∧ M.mem (M.trip i.1 a b') E) → b' = b

/-! ### The same as a stratified formula -/

/-- `a ≤ b` for numbers given as objects, through the graph `ad` of addition. -/
def LeRaw (ad a b : V) : Prop := ∃ c, M.mem c M.nat ∧ M.mem (M.trip a c b) ad

theorem leRaw_iff {ad : V} (had : M.IsGraphOf₂ ad M.addN) (j k : M.Num) :
    M.LeRaw ad j.1 k.1 ↔ j ≤ k := by
  constructor
  · rintro ⟨c, hc, h⟩
    have e := M.graph₂_val had (m := j) (n := ⟨c, hc⟩) h
    exact M.le_def.mpr ⟨⟨c, hc⟩, Subtype.ext e.symm⟩
  · intro h
    obtain ⟨c, hc⟩ := M.le_def.mp h
    refine ⟨c.1, c.2, ?_⟩
    rw [← hc]
    exact M.graph₂_app had j c

/-- The definition of a ladder with the numbers as objects. -/
def LadderRaw (ad R E z S m : V) : Prop :=
  (∀ i a, M.mem (M.op i a) R → M.mem i M.nat ∧ M.LeRaw ad i m) ∧
  (∀ i a b, M.mem (M.trip i a b) E → M.mem i M.nat ∧ ∃ s, s = M.succ i ∧ M.LeRaw ad s m) ∧
  M.mem (M.op M.zero z) R ∧
  (∀ a, M.mem (M.op M.zero a) R → ∃ b, M.mem (M.op M.zero b) R ∧ M.mem (M.op a b) S ∧
    ∀ b', M.mem (M.op a b') S → b' = b) ∧
  (∀ a a' b, M.mem (M.op a b) S → M.mem (M.op a' b) S → a = a') ∧
  (∀ a, ¬ M.mem (M.op a z) S) ∧
  (∀ x, M.mem z x → (∀ a b, M.mem a x → M.mem (M.op a b) S → M.mem b x) →
    ∀ a, M.mem (M.op M.zero a) R → M.mem a x) ∧
  (∀ i, M.mem i M.nat → ∀ s, s = M.succ i → M.LeRaw ad s m → ∀ x, M.isSet x →
    (∀ a, M.mem a x → M.mem (M.op i a) R) →
    ∃ b, M.mem (M.op s b) R ∧
      (∀ a, M.mem a x ↔ M.mem (M.op i a) R ∧ M.mem (M.trip i a b) E) ∧
      ∀ b', M.mem (M.op s b') R →
        (∀ a, M.mem a x ↔ M.mem (M.op i a) R ∧ M.mem (M.trip i a b') E) → b' = b)

/-- `a ≤ b`, with `ℕ` and the graph of addition the names `6`, `7`. -/
def fLe (a b : ℕ) : Fml := Fml.ex 14 (.and (.mem 14 6) (fApp3 7 a 14 b))

/-- "`R`, `E`, `z`, `S` (names `1`–`4`) is a ladder of height `m` (name `0`)"; the names
`5`, `6`, `7` stand for `0`, `ℕ` and the graph of addition. -/
def ladderFml : Fml :=
  .and (.all 8 (.all 9 (Fml.imp (fApp 1 8 9) (.and (.mem 8 6) (fLe 8 0)))))
  (.and (.all 8 (.all 9 (.all 10 (Fml.imp (fApp3 2 8 9 10)
    (.and (.mem 8 6) (Fml.ex 13 (.and (fSuccEq 13 8) (fLe 13 0))))))))
  (.and (fApp 1 5 3)
  (.and (.all 9 (Fml.imp (fApp 1 5 9) (Fml.ex 10 (.and (fApp 1 5 10) (.and (fApp 4 9 10)
    (.all 12 (Fml.imp (fApp 4 9 12) (.eq 12 10))))))))
  (.and (.all 9 (.all 15 (.all 10 (Fml.imp (fApp 4 9 10) (Fml.imp (fApp 4 15 10) (.eq 9 15))))))
  (.and (.all 9 (.neg (fApp 4 9 3)))
  (.and (.all 11 (Fml.imp (.mem 3 11) (Fml.imp
    (.all 9 (.all 10 (Fml.imp (.mem 9 11) (Fml.imp (fApp 4 9 10) (.mem 10 11)))))
    (.all 9 (Fml.imp (fApp 1 5 9) (.mem 9 11))))))
  (.all 8 (Fml.imp (.mem 8 6) (.all 13 (Fml.imp (fSuccEq 13 8) (Fml.imp (fLe 13 0)
    (.all 11 (Fml.imp (.set 11) (Fml.imp (.all 9 (Fml.imp (.mem 9 11) (fApp 1 8 9)))
      (Fml.ex 10 (.and (fApp 1 13 10) (.and
        (.all 9 (Fml.iff (.mem 9 11) (.and (fApp 1 8 9) (fApp3 2 8 9 10))))
        (.all 12 (Fml.imp (fApp 1 13 12) (Fml.imp
          (.all 9 (Fml.iff (.mem 9 11) (.and (fApp 1 8 9) (fApp3 2 8 9 12))))
          (.eq 12 10)))))))))))))))))))))

/-- The stratification of `ladderFml`: numbers and members of rungs have type `2`. -/
def σL : ℕ → ℕ := σW [(1, 5), (2, 7), (4, 5), (6, 3), (7, 7), (11, 3)]

theorem ladderRaw_iff {ad : V} (had : M.IsGraphOf₂ ad M.addN) (R E z S : V) (m : M.Num) :
    M.LadderRaw ad R E z S m.1 ↔ M.IsLadder R E z S m := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨fun i a h => ?_, fun i a b h => ?_, h3, h4, h5, h6, h7, fun i hi x hx hxi => ?_⟩
    · obtain ⟨hi, hle⟩ := h1 i a h
      exact ⟨⟨i, hi⟩, rfl, (M.leRaw_iff had ⟨i, hi⟩ m).mp hle⟩
    · obtain ⟨hi, s, hs, hle⟩ := h2 i a b h
      refine ⟨⟨i, hi⟩, rfl, ?_⟩
      rw [← M.nsucc_eq_add_one]
      rw [hs] at hle
      exact (M.leRaw_iff had (M.nsucc ⟨i, hi⟩) m).mp hle
    · have hle : M.LeRaw ad (M.succ i.1) m.1 := by
        refine (M.leRaw_iff had (M.nsucc i) m).mpr ?_
        rw [M.nsucc_eq_add_one]
        exact hi
      have h9 := h8 i.1 i.2 _ rfl hle x hx hxi
      rw [M.val_add_one]
      exact h9
  · intro h
    refine ⟨fun i a hia => ?_, fun i a b hiab => ?_, h.zero_mem, h.succ_fun, h.succ_inj,
      h.zero_ne, h.ind, fun i hi s hs hle x hx hxi => ?_⟩
    · obtain ⟨j, hj, hjm⟩ := h.idx i a hia
      rw [← hj]
      exact ⟨j.2, (M.leRaw_iff had j m).mpr hjm⟩
    · obtain ⟨j, hj, hjm⟩ := h.eidx i a b hiab
      rw [← hj]
      refine ⟨j.2, _, rfl, ?_⟩
      rw [← M.nsucc_eq_add_one] at hjm
      exact (M.leRaw_iff had (M.nsucc j) m).mpr hjm
    · rw [hs] at hle ⊢
      have hi' : (⟨i, hi⟩ : M.Num) + 1 ≤ m := by
        rw [← M.nsucc_eq_add_one]
        exact (M.leRaw_iff had (M.nsucc ⟨i, hi⟩) m).mp hle
      have h9 := h.full ⟨i, hi⟩ hi' x hx hxi
      rw [M.val_add_one] at h9
      exact h9

/-! ### The ladder of height `0` -/

theorem ladder_zero : ∃ R E z S, M.IsLadder R E z S 0 := by
  obtain ⟨R, -, hR0⟩ := M.comp (σW [(0, 4), (1, 3)]) (Fml.ex 3 (.and (.mem 3 1) (fPr 0 2 3))) 0
    rfl (Function.update (Function.update (fun _ => dflt) 1 M.nat) 2 M.zero)
  have hR : ∀ p, M.mem p R ↔ ∃ a, M.mem a M.nat ∧ p = M.op M.zero a := by
    intro p
    rw [hR0 p]
    simp [M.sat_ex, Sat, M.sat_fPr, Function.update_apply]
  have hR' : ∀ i a, M.mem (M.op i a) R ↔ i = M.zero ∧ M.mem a M.nat := by
    intro i a
    rw [hR]
    constructor
    · rintro ⟨a', ha', e⟩
      obtain ⟨e1, e2⟩ := M.op_inj e
      rw [e1, e2]
      exact ⟨rfl, ha'⟩
    · rintro ⟨hi, ha⟩
      rw [hi]
      exact ⟨a, ha, rfl⟩
  obtain ⟨S, hS⟩ := M.natFn_succ
  refine ⟨R, M.emp, M.zero, S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i a h
    exact ⟨0, ((hR' i a).mp h).1.symm, le_refl _⟩
  · intro i a b h
    exact absurd h (M.not_mem_emp _)
  · exact (hR' _ _).mpr ⟨rfl, M.zero_mem_nat⟩
  · intro a ha
    have han := ((hR' _ _).mp ha).2
    refine ⟨M.succ a, (hR' _ _).mpr ⟨rfl, M.succ_mem_nat han⟩,
      (hS _ _).mpr ⟨⟨a, han⟩, rfl, rfl⟩, fun b' hb' => ?_⟩
    obtain ⟨n, hn, hb⟩ := (hS _ _).mp hb'
    rw [← hb, ← hn]
    rfl
  · intro a a' b h1 h2
    obtain ⟨n, hn, hb⟩ := (hS _ _).mp h1
    obtain ⟨n', hn', hb'⟩ := (hS _ _).mp h2
    have e : M.nsucc n = M.nsucc n' := Subtype.ext (hb.trans hb'.symm)
    rw [← hn, ← hn', M.nsucc_inj e]
  · intro a h
    obtain ⟨n, hn, hb⟩ := (hS _ _).mp h
    exact M.zero_ne_succ n.1 hb.symm
  · intro x hz hcl a ha
    have han := ((hR' _ _).mp ha).2
    obtain ⟨J, -, hJ⟩ := M.exists_inter x M.nat
    have key := M.nat_ind (I := J) ((hJ _).mpr ⟨hz, M.zero_mem_nat⟩) (fun k hk => by
      obtain ⟨hkx, hkn⟩ := (hJ k).mp hk
      exact (hJ _).mpr ⟨hcl k (M.succ k) hkx ((hS _ _).mpr ⟨⟨k, hkn⟩, rfl, rfl⟩),
        M.succ_mem_nat hkn⟩) han
    exact ((hJ a).mp key).1
  · intro i hi
    exfalso
    obtain ⟨c, hc⟩ := M.le_def.mp hi
    exact M.peano.1 (i + c) ((by ring : i + c + 1 = i + 1 + c).trans hc)

/-! ### From height `m` to height `m + 1`, for calm `m`

Each rung is replaced by its singleton image, and the set of all subsets of the old top rung
is put on top. The singleton image raises the type, so in the defining formulas the index
`i` of an old rung becomes `T i`; for calm `m` and `i ≤ m` this is `i` again. -/

def rungFml : Fml :=
  Fml.or
    (Fml.ex 5 (Fml.ex 6 (Fml.ex 7 (Fml.ex 10 (.and (fApp 1 5 6) (.and (.mem 7 2) (.and (fT 5 7)
      (.and (fSing 10 6 15) (fOp 0 7 10 46 47)))))))))
    (Fml.ex 11 (.and (.set 11) (.and (.all 6 (Fml.imp (.mem 6 11) (fApp 1 3 6)))
      (fOp 0 4 11 46 47))))

def edgeFml : Fml :=
  Fml.or
    (Fml.ex 5 (Fml.ex 6 (Fml.ex 16 (Fml.ex 7 (Fml.ex 10 (Fml.ex 17 (.and (fApp3 1 5 6 16)
      (.and (.mem 7 2) (.and (fT 5 7) (.and (fSing 10 6 15) (.and (fSing 17 16 15)
        (fTripH 0 7 10 17))))))))))))
    (Fml.ex 6 (Fml.ex 11 (Fml.ex 10 (.and (.mem 6 11) (.and (fSing 10 6 15)
      (fTripH 0 3 10 11))))))

def succImgFml : Fml :=
  Fml.ex 6 (Fml.ex 16 (Fml.ex 10 (Fml.ex 17 (.and (fApp 1 6 16) (.and (fSing 10 6 15)
    (.and (fSing 17 16 15) (fOp 0 10 17 46 47)))))))

/-- **The step of Lemma 3.1 (b).** A ladder of calm height `m` gives a ladder of height
`m + 1`. -/
theorem ladder_succ {R E z S : V} {m : M.Num} (hm : M.InS m.1) (h : M.IsLadder R E z S m) :
    ∃ R' E' z' S', M.IsLadder R' E' z' S' (m + 1) := by
  have calm : ∀ k : M.Num, k ≤ m → ∀ j, M.mem j M.nat → (M.TRel k.1 j ↔ j = k.1) :=
    fun k hk j hj => M.TRel_iff_of_inS (M.inS_of_le hk hm) hj
  -- the rungs
  obtain ⟨R', -, hR0⟩ := M.comp (σW [(0, 5), (1, 5), (2, 4), (4, 3), (7, 3), (8, 1), (10, 3),
      (11, 3), (12, 1), (13, 0), (14, 0), (46, 4), (47, 3)]) rungFml 0 rfl
    (Function.update (Function.update (Function.update (Function.update (fun _ => dflt)
      1 R) 2 M.nat) 3 m.1) 4 (m + 1).1)
  have hR1 : ∀ p, M.mem p R' ↔
      (∃ i a i' t, M.mem (M.op i a) R ∧ M.mem i' M.nat ∧ M.TRel i i' ∧ t = M.sing a ∧
        p = M.op i' t) ∨
      (∃ x, M.isSet x ∧ (∀ a, M.mem a x → M.mem (M.op m.1 a) R) ∧ p = M.op (m + 1).1 x) := by
    intro p
    rw [hR0 p]
    simp [rungFml, M.sat_or, M.sat_ex, Sat, M.sat_imp, M.sat_fApp, M.sat_fT, M.sat_fSing,
      M.sat_fOp, Function.update_apply]
  have hR : ∀ j t, M.mem (M.op j t) R' ↔
      (∃ i : M.Num, i.1 = j ∧ i ≤ m ∧ ∃ a, M.mem (M.op j a) R ∧ t = M.sing a) ∨
      (j = (m + 1).1 ∧ M.isSet t ∧ ∀ a, M.mem a t → M.mem (M.op m.1 a) R) := by
    intro j t
    rw [hR1]
    constructor
    · rintro (⟨i, a, i', t0, hia, hi', hT, ht0, e⟩ | ⟨x, hx, hxm, e⟩)
      · obtain ⟨e1, e2⟩ := M.op_inj e
        obtain ⟨k, hk, hkm⟩ := h.idx i a hia
        rw [← hk] at hT hia
        have e3 : i' = k.1 := (calm k hkm i' hi').mp hT
        left
        refine ⟨k, ?_, hkm, a, ?_, ?_⟩
        · rw [e1, e3]
        · rw [e1, e3]
          exact hia
        · rw [e2, ht0]
      · obtain ⟨e1, e2⟩ := M.op_inj e
        right
        rw [e1, e2]
        exact ⟨rfl, hx, hxm⟩
    · rintro (⟨i, hi, him, a, hja, ht⟩ | ⟨hj, hts, htm⟩)
      · left
        refine ⟨j, a, j, t, hja, ?_, ?_, ht, rfl⟩
        · rw [← hi]
          exact i.2
        · rw [← hi]
          exact (calm i him i.1 i.2).mpr rfl
      · right
        exact ⟨t, hts, htm, by rw [hj]⟩
  -- the relations between consecutive rungs
  obtain ⟨E', -, hE0⟩ := M.comp (σW [(0, 7), (1, 7), (2, 4), (3, 3), (7, 3), (8, 1), (10, 3),
      (11, 3), (12, 1), (13, 0), (14, 0), (17, 3), (52, 5), (53, 5), (54, 6), (55, 5), (56, 4),
      (57, 3)]) edgeFml 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 1 E) 2 M.nat) 3 m.1)
  have hE1 : ∀ q, M.mem q E' ↔
      (∃ i a b i' t u, M.mem (M.trip i a b) E ∧ M.mem i' M.nat ∧ M.TRel i i' ∧ t = M.sing a ∧
        u = M.sing b ∧ q = M.trip i' t u) ∨
      (∃ a x t, M.mem a x ∧ t = M.sing a ∧ q = M.trip m.1 t x) := by
    intro q
    rw [hE0 q]
    simp [edgeFml, M.sat_or, M.sat_ex, Sat, M.sat_fApp3, M.sat_fT, M.sat_fSing, M.sat_fTripH,
      Function.update_apply]
  have hE : ∀ j t u, M.mem (M.trip j t u) E' ↔
      (∃ i : M.Num, i.1 = j ∧ i + 1 ≤ m ∧ ∃ a b, M.mem (M.trip j a b) E ∧ t = M.sing a ∧
        u = M.sing b) ∨
      (j = m.1 ∧ ∃ a, M.mem a u ∧ t = M.sing a) := by
    intro j t u
    rw [hE1]
    constructor
    · rintro (⟨i, a, b, i', t0, u0, hiab, hi', hT, ht0, hu0, e⟩ | ⟨a, x, t0, hax, ht0, e⟩)
      · obtain ⟨e1, e2, e3⟩ := M.trip_inj e
        obtain ⟨k, hk, hkm⟩ := h.eidx i a b hiab
        rw [← hk] at hT hiab
        have hkm' : k ≤ m := le_trans (M.le_add_one k) hkm
        have e4 : i' = k.1 := (calm k hkm' i' hi').mp hT
        left
        refine ⟨k, ?_, hkm, a, b, ?_, ?_, ?_⟩
        · rw [e1, e4]
        · rw [e1, e4]
          exact hiab
        · rw [e2, ht0]
        · rw [e3, hu0]
      · obtain ⟨e1, e2, e3⟩ := M.trip_inj e
        right
        refine ⟨e1, a, ?_, ?_⟩
        · rw [e3]
          exact hax
        · rw [e2, ht0]
    · rintro (⟨i, hi, him, a, b, hjab, ht, hu⟩ | ⟨hj, a, hau, ht⟩)
      · left
        refine ⟨j, a, b, j, t, u, hjab, ?_, ?_, ht, hu, rfl⟩
        · rw [← hi]
          exact i.2
        · rw [← hi]
          exact (calm i (le_trans (M.le_add_one i) him) i.1 i.2).mpr rfl
      · right
        exact ⟨a, u, t, hau, ht, by rw [hj]⟩
  -- the successor on the base
  obtain ⟨S', -, hS0⟩ := M.comp (σW [(0, 5), (1, 5), (10, 3), (17, 3), (46, 4), (47, 3)])
    succImgFml 0 rfl (Function.update (fun _ => dflt) 1 S)
  have hS1 : ∀ q, M.mem q S' ↔
      ∃ a b t u, M.mem (M.op a b) S ∧ t = M.sing a ∧ u = M.sing b ∧ q = M.op t u := by
    intro q
    rw [hS0 q]
    simp [succImgFml, M.sat_ex, Sat, M.sat_fApp, M.sat_fSing, M.sat_fOp, Function.update_apply]
  have hS : ∀ t u, M.mem (M.op t u) S' ↔
      ∃ a b, M.mem (M.op a b) S ∧ t = M.sing a ∧ u = M.sing b := by
    intro t u
    rw [hS1]
    constructor
    · rintro ⟨a, b, t0, u0, hab, ht0, hu0, e⟩
      obtain ⟨e1, e2⟩ := M.op_inj e
      exact ⟨a, b, hab, by rw [e1, ht0], by rw [e2, hu0]⟩
    · rintro ⟨a, b, hab, ht, hu⟩
      exact ⟨a, b, t, u, hab, ht, hu, rfl⟩
  have hm1 : (m + 1).1 = M.succ m.1 := M.val_add_one m
  have rung0 : ∀ t, M.mem (M.op M.zero t) R' ↔ ∃ a, M.mem (M.op M.zero a) R ∧ t = M.sing a := by
    intro t
    rw [hR]
    constructor
    · rintro (⟨i, hi, him, a, ha, ht⟩ | ⟨hj, -, -⟩)
      · exact ⟨a, ha, ht⟩
      · rw [hm1] at hj
        exact absurd hj (M.zero_ne_succ _)
    · rintro ⟨a, ha, ht⟩
      exact Or.inl ⟨0, rfl, zero_le, a, ha, ht⟩
  refine ⟨R', E', M.sing z, S', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j t hjt
    rcases (hR j t).mp hjt with ⟨i, hi, him, -⟩ | ⟨hj, -, -⟩
    · exact ⟨i, hi, le_trans him (M.le_add_one m)⟩
    · exact ⟨m + 1, hj.symm, le_refl _⟩
  · intro j t u hjtu
    rcases (hE j t u).mp hjtu with ⟨i, hi, him, -⟩ | ⟨hj, -⟩
    · exact ⟨i, hi, le_trans him (M.le_add_one m)⟩
    · exact ⟨m, hj.symm, le_refl _⟩
  · exact (rung0 _).mpr ⟨z, h.zero_mem, rfl⟩
  · intro t ht
    obtain ⟨a, ha, hta⟩ := (rung0 t).mp ht
    obtain ⟨b, hb, hab, huniq⟩ := h.succ_fun a ha
    refine ⟨M.sing b, (rung0 _).mpr ⟨b, hb, rfl⟩, (hS _ _).mpr ⟨a, b, hab, hta, rfl⟩,
      fun u hu => ?_⟩
    obtain ⟨a0, b0, hab0, hta0, hub0⟩ := (hS _ _).mp hu
    have e : a0 = a := M.sing_inj (hta0.symm.trans hta)
    rw [e] at hab0
    rw [hub0, huniq b0 hab0]
  · intro t t' u h1 h2
    obtain ⟨a, b, hab, hta, hub⟩ := (hS _ _).mp h1
    obtain ⟨a', b', hab', hta', hub'⟩ := (hS _ _).mp h2
    have e : b' = b := M.sing_inj (hub'.symm.trans hub)
    rw [e] at hab'
    rw [hta, hta', h.succ_inj a a' b hab hab']
  · intro t ht
    obtain ⟨a, b, hab, -, hub⟩ := (hS _ _).mp ht
    have e : z = b := M.sing_inj hub
    rw [← e] at hab
    exact h.zero_ne a hab
  · intro X hz hcl t ht
    obtain ⟨a, ha, hta⟩ := (rung0 t).mp ht
    have key := h.ind (M.unsing X) (M.mem_unsing.mpr hz) (fun a b hax hab =>
      M.mem_unsing.mpr (hcl _ _ (M.mem_unsing.mp hax) ((hS _ _).mpr ⟨a, b, hab, rfl, rfl⟩))) a ha
    rw [hta]
    exact M.mem_unsing.mp key
  · intro j hj X hXs hX
    have hjm : j ≤ m := M.le_of_succ_le_succ hj
    have hjne : j.1 ≠ (m + 1).1 := by
      intro e
      have e' : j = m + 1 := Subtype.ext e
      rw [e'] at hjm
      exact M.not_succ_le m hjm
    have rung : ∀ t, M.mem (M.op j.1 t) R' ↔ ∃ a, M.mem (M.op j.1 a) R ∧ t = M.sing a := by
      intro t
      rw [hR]
      constructor
      · rintro (⟨i, hi, him, a, ha, ht⟩ | ⟨hjj, -, -⟩)
        · exact ⟨a, ha, ht⟩
        · exact absurd hjj hjne
      · rintro ⟨a, ha, ht⟩
        exact Or.inl ⟨j, rfl, hjm, a, ha, ht⟩
    have hxj : ∀ a, M.mem a (M.unsing X) → M.mem (M.op j.1 a) R := by
      intro a ha
      obtain ⟨a0, ha0, e⟩ := (rung _).mp (hX _ (M.mem_unsing.mp ha))
      rw [M.sing_inj e]
      exact ha0
    have hXx : ∀ t, M.mem t X ↔ ∃ a, M.mem a (M.unsing X) ∧ t = M.sing a := by
      intro t
      constructor
      · intro ht
        obtain ⟨a, -, e⟩ := (rung t).mp (hX t ht)
        rw [e] at ht
        exact ⟨a, M.mem_unsing.mpr ht, e⟩
      · rintro ⟨a, ha, e⟩
        rw [e]
        exact M.mem_unsing.mp ha
    have noE : ∀ i : M.Num, i.1 = m.1 → ¬ i + 1 ≤ m := by
      intro i hi hle
      have e : i = m := Subtype.ext hi
      rw [e] at hle
      exact M.not_succ_le m hle
    rcases M.eq_or_succ_le hjm with hjeq | hjlt
    · -- the top rung: the subsets of the old top rung
      have ejm : j.1 = m.1 := congrArg Subtype.val hjeq
      have ejm1 : (j + 1).1 = (m + 1).1 := by rw [hjeq]
      have hxm : ∀ a, M.mem a (M.unsing X) → M.mem (M.op m.1 a) R := by
        intro a ha
        rw [← ejm]
        exact hxj a ha
      refine ⟨M.unsing X, ?_, fun t => ?_, fun b' hb' hext' => ?_⟩
      · exact (hR _ _).mpr (Or.inr ⟨ejm1, M.unsing_isSet X, hxm⟩)
      · constructor
        · intro ht
          obtain ⟨a, ha, e⟩ := (hXx t).mp ht
          exact ⟨hX t ht, (hE _ _ _).mpr (Or.inr ⟨ejm, a, ha, e⟩)⟩
        · rintro ⟨ht1, ht2⟩
          rcases (hE _ _ _).mp ht2 with ⟨i, hi, him, -⟩ | ⟨-, a, ha, e⟩
          · exact absurd him (noE i (hi.trans ejm))
          · exact (hXx t).mpr ⟨a, ha, e⟩
      · rcases (hR _ _).mp hb' with ⟨i, hi, him, -⟩ | ⟨-, hb's, hb'm⟩
        · exfalso
          have e : i = m + 1 := Subtype.ext (hi.trans ejm1)
          rw [e] at him
          exact M.not_succ_le m him
        · refine M.ext hb's (M.unsing_isSet X) fun a => ?_
          constructor
          · intro ha
            have h1 : M.mem (M.op j.1 (M.sing a)) R' := by
              refine (rung _).mpr ⟨a, ?_, rfl⟩
              rw [ejm]
              exact hb'm a ha
            exact M.mem_unsing.mpr ((hext' (M.sing a)).mpr
              ⟨h1, (hE _ _ _).mpr (Or.inr ⟨ejm, a, ha, rfl⟩)⟩)
          · intro ha
            have h1 := ((hext' (M.sing a)).mp (M.mem_unsing.mp ha)).2
            rcases (hE _ _ _).mp h1 with ⟨i, hi, him, -⟩ | ⟨-, a1, ha1, e⟩
            · exact absurd him (noE i (hi.trans ejm))
            · rw [M.sing_inj e]
              exact ha1
    · -- a rung below the top: singleton images
      have hjnm : j.1 ≠ m.1 := fun e => noE j e hjlt
      obtain ⟨b, hb, hext, huniq⟩ := h.full j hjlt (M.unsing X) (M.unsing_isSet X) hxj
      refine ⟨M.sing b, ?_, fun t => ?_, fun b' hb' hext' => ?_⟩
      · exact (hR _ _).mpr (Or.inl ⟨j + 1, rfl, hjlt, b, hb, rfl⟩)
      · constructor
        · intro ht
          obtain ⟨a, ha, e⟩ := (hXx t).mp ht
          exact ⟨hX t ht, (hE _ _ _).mpr
            (Or.inl ⟨j, rfl, hjlt, a, b, ((hext a).mp ha).2, e, rfl⟩)⟩
        · rintro ⟨ht1, ht2⟩
          obtain ⟨a, ha, e⟩ := (rung t).mp ht1
          rcases (hE _ _ _).mp ht2 with ⟨i, hi, him, a0, b0, hE0, hta, hub⟩ | ⟨hjj, -⟩
          · have ea : a0 = a := M.sing_inj (hta.symm.trans e)
            have eb : b0 = b := (M.sing_inj hub).symm
            rw [ea, eb] at hE0
            exact (hXx t).mpr ⟨a, (hext a).mpr ⟨ha, hE0⟩, e⟩
          · exact absurd hjj hjnm
      · rcases (hR _ _).mp hb' with ⟨i, hi, him, b0, hb0, eb'⟩ | ⟨hjj, -, -⟩
        · have e0 : b0 = b := by
            refine huniq b0 hb0 fun a => ?_
            constructor
            · intro ha
              have h1 := ((hext' (M.sing a)).mp (M.mem_unsing.mp ha)).2
              rw [eb'] at h1
              rcases (hE _ _ _).mp h1 with ⟨i', hi', him', a1, b1, hE1', hta, hub⟩ | ⟨hjj, -⟩
              · have ea : a1 = a := (M.sing_inj hta).symm
                have eb : b1 = b0 := (M.sing_inj hub).symm
                rw [ea, eb] at hE1'
                exact ⟨hxj a ha, hE1'⟩
              · exact absurd hjj hjnm
            · rintro ⟨ha1, ha2⟩
              refine M.mem_unsing.mpr ((hext' (M.sing a)).mpr ⟨(rung _).mpr ⟨a, ha1, rfl⟩, ?_⟩)
              rw [eb']
              exact (hE _ _ _).mpr (Or.inl ⟨j, rfl, hjlt, a, b0, ha2, rfl, rfl⟩)
          rw [eb', e0]
        · exfalso
          have e : j + 1 = m + 1 := Subtype.ext hjj
          have e' : j = m := M.peano.2.1 j m e
          rw [e'] at hjlt
          exact M.not_succ_le m hjlt

/-! ### Lemma 3.1 -/

/-- "If `k ≤ n` then there is a ladder of height `k`", with `k` the name `0` and `n` the
name `16`. -/
def hasLadderFml : Fml :=
  Fml.imp (fLe 0 16) (Fml.ex 1 (Fml.ex 2 (Fml.ex 3 (Fml.ex 4 ladderFml))))

/-- **Lemma 3.1 (b).** For every calm `n` there is a ladder of height `n`. The proof is an
induction on `k ≤ n`; the condition is stratified. -/
theorem exists_ladder {n : M.Num} (hn : M.InS n.1) : ∃ R E z S, M.IsLadder R E z S n := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  have hsat : ∀ k : V, Sat M.mem M.isSet hasLadderFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 5 M.zero) 6 M.nat)
        7 ad) 16 n.1) 0 k) ↔
      (M.LeRaw ad k n.1 → ∃ R E z S, M.LadderRaw ad R E z S k) := by
    intro k
    simp [hasLadderFml, ladderFml, fLe, LadderRaw, LeRaw, Sat, M.sat_imp, M.sat_iff, M.sat_ex,
      M.sat_fApp, M.sat_fApp3, M.sat_fSuccEq, Function.update_apply]
  have h0 : Sat M.mem M.isSet hasLadderFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 5 M.zero) 6 M.nat)
        7 ad) 16 n.1) 0 M.zero) := by
    rw [hsat]
    intro _
    obtain ⟨R, E, z, S, h⟩ := M.ladder_zero
    exact ⟨R, E, z, S, (M.ladderRaw_iff had R E z S 0).mpr h⟩
  have hs : ∀ k : M.Num, Sat M.mem M.isSet hasLadderFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 5 M.zero) 6 M.nat)
        7 ad) 16 n.1) 0 k.1) →
      Sat M.mem M.isSet hasLadderFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 5 M.zero) 6 M.nat)
        7 ad) 16 n.1) 0 (M.succ k.1)) := by
    intro k ih
    rw [hsat] at ih ⊢
    intro hle
    have hle' : k + 1 ≤ n := by
      rw [← M.nsucc_eq_add_one]
      exact (M.leRaw_iff had (M.nsucc k) n).mp hle
    have hk : k ≤ n := le_trans (M.le_add_one k) hle'
    obtain ⟨R, E, z, S, h⟩ := ih ((M.leRaw_iff had k n).mpr hk)
    obtain ⟨R', E', z', S', h'⟩ :=
      M.ladder_succ (M.inS_of_le hk hn) ((M.ladderRaw_iff had R E z S k).mp h)
    refine ⟨R', E', z', S', ?_⟩
    have h9 := (M.ladderRaw_iff had R' E' z' S' (k + 1)).mpr h'
    rw [M.val_add_one] at h9
    exact h9
  have key := M.num_ind_fml σL hasLadderFml 0 rfl _ h0 hs n
  rw [hsat] at key
  obtain ⟨R, E, z, S, h⟩ := key ((M.leRaw_iff had n n).mpr (le_refl n))
  exact ⟨R, E, z, S, (M.ladderRaw_iff had R E z S n).mp h⟩

def baseInjFml : Fml :=
  .all 3 (.all 4 (Fml.imp (.mem 3 2) (Fml.imp (fApp 1 0 4) (Fml.imp (fApp 1 3 4) (.eq 0 3)))))

theorem sat_baseInjFml (f k : V) :
    Sat M.mem M.isSet baseInjFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 f) 2 M.nat) 0 k) ↔
    ∀ n' a, M.mem n' M.nat → M.mem (M.op k a) f → M.mem (M.op n' a) f → k = n' := by
  simp [baseInjFml, Sat, M.sat_imp, M.sat_fApp, Function.update_apply]

/-- **Lemma 3.1 (a).** The base of a ladder is isomorphic to the natural numbers: there is a
set `f` of pairs that is a bijection from the natural numbers onto rung `0`, taking `0` to the
zero of the ladder and successor to its successor. -/
theorem ladder_base_iso {R E z S : V} {m : M.Num} (h : M.IsLadder R E z S m) :
    ∃ f, (∀ n : M.Num, ∃ a, M.mem (M.op M.zero a) R ∧ M.mem (M.op n.1 a) f ∧
        ∀ a', M.mem (M.op n.1 a') f → a' = a) ∧
      (∀ (n n' : M.Num) (a : V), M.mem (M.op n.1 a) f → M.mem (M.op n'.1 a) f → n = n') ∧
      (∀ a, M.mem (M.op M.zero a) R → ∃ n : M.Num, M.mem (M.op n.1 a) f) ∧
      M.mem (M.op M.zero z) f ∧
      ∀ (n : M.Num) (a b : V), M.mem (M.op n.1 a) f → M.mem (M.op a b) S →
        M.mem (M.op (M.succ n.1) b) f := by
  -- rung 0 as a set
  obtain ⟨D, -, hD0⟩ := M.comp (σW [(1, 5)]) (fApp 1 2 0) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 R) 2 M.zero)
  have hD : ∀ a, M.mem a D ↔ M.mem (M.op M.zero a) R := by
    intro a
    rw [hD0 a]
    simp [M.sat_fApp, Function.update_apply]
  have hG : M.FunOn S D := by
    intro u hu
    obtain ⟨b, hb, hab, huniq⟩ := h.succ_fun u ((hD u).mp hu)
    exact ⟨b, (hD b).mpr hb, hab, huniq⟩
  obtain ⟨f, hf, hf0, hfs⟩ := M.exists_rec_set ((hD z).mpr h.zero_mem) hG
  have val0 : ∀ a, M.mem (M.op M.zero a) f → a = z := by
    intro a ha
    obtain ⟨u, -, -, huniq⟩ := hf M.nzero
    rw [huniq a ha, ← huniq z hf0]
  have valS : ∀ (k : M.Num) (b : V), M.mem (M.op (M.succ k.1) b) f →
      ∃ a, M.mem (M.op k.1 a) f ∧ M.mem (M.op a b) S := by
    intro k b hb
    obtain ⟨a, haD, ha, -⟩ := hf k
    obtain ⟨b0, -, hab0, -⟩ := hG a haD
    obtain ⟨u, -, -, huniq⟩ := hf (M.nsucc k)
    have e : b = b0 := (huniq b hb).trans (huniq b0 (hfs k a b0 ha hab0)).symm
    rw [e]
    exact ⟨a, ha, hab0⟩
  refine ⟨f, fun n => ?_, ?_, ?_, hf0, hfs⟩
  · obtain ⟨u, huD, hu, huniq⟩ := hf n
    exact ⟨u, (hD u).mp huD, hu, huniq⟩
  · -- injective
    have key : ∀ n : M.Num, ∀ n' a, M.mem n' M.nat → M.mem (M.op n.1 a) f →
        M.mem (M.op n' a) f → n.1 = n' := by
      intro n
      have h0 : Sat M.mem M.isSet baseInjFml (Function.update (Function.update (Function.update
          (fun _ => dflt) 1 f) 2 M.nat) 0 M.zero) := by
        rw [M.sat_baseInjFml]
        intro n' a hn' h1 h2
        rw [val0 a h1] at h2
        rcases M.nat_cases hn' with e | ⟨k', hk', e⟩
        · exact e.symm
        · rw [e] at h2
          obtain ⟨a0, -, ha0⟩ := valS ⟨k', hk'⟩ z h2
          exact absurd ha0 (h.zero_ne a0)
      have hs : ∀ k : M.Num, Sat M.mem M.isSet baseInjFml (Function.update (Function.update
          (Function.update (fun _ => dflt) 1 f) 2 M.nat) 0 k.1) →
          Sat M.mem M.isSet baseInjFml (Function.update (Function.update (Function.update
          (fun _ => dflt) 1 f) 2 M.nat) 0 (M.succ k.1)) := by
        intro k ih
        rw [M.sat_baseInjFml] at ih ⊢
        intro n' a hn' h1 h2
        obtain ⟨a0, ha0, ha0a⟩ := valS k a h1
        rcases M.nat_cases hn' with e | ⟨k', hk', e⟩
        · rw [e] at h2
          rw [val0 a h2] at ha0a
          exact absurd ha0a (h.zero_ne a0)
        · rw [e] at h2 ⊢
          obtain ⟨a1, ha1, ha1a⟩ := valS ⟨k', hk'⟩ a h2
          have ea : a0 = a1 := h.succ_inj a0 a1 a ha0a ha1a
          rw [← ea] at ha1
          rw [ih k' a0 hk' ha0 ha1]
      have key := M.num_ind_fml (σW [(1, 5), (2, 3)]) baseInjFml 0 rfl _ h0 hs n
      rw [M.sat_baseInjFml] at key
      exact key
    intro n n' a h1 h2
    exact Subtype.ext (key n n'.1 a n'.2 h1 h2)
  · -- surjective
    obtain ⟨X, -, hX0⟩ := M.comp (σW [(1, 5), (2, 3)]) (Fml.ex 3 (.and (.mem 3 2) (fApp 1 3 0)))
      0 rfl (Function.update (Function.update (fun _ => dflt) 1 f) 2 M.nat)
    have hX : ∀ a, M.mem a X ↔ ∃ n, M.mem n M.nat ∧ M.mem (M.op n a) f := by
      intro a
      rw [hX0 a]
      simp [M.sat_ex, Sat, M.sat_fApp, Function.update_apply]
    intro a ha
    have key := h.ind X ((hX z).mpr ⟨M.zero, M.zero_mem_nat, hf0⟩) (fun a b hax hab => by
      obtain ⟨n, hn, hna⟩ := (hX a).mp hax
      exact (hX b).mpr ⟨M.succ n, M.succ_mem_nat hn, hfs ⟨n, hn⟩ a b hna hab⟩) a ha
    obtain ⟨n, hn, hna⟩ := (hX a).mp key
    exact ⟨⟨n, hn⟩, hna⟩

/-- **Lemma 3.1**, both parts. -/
theorem lemma_3_1 {n : M.Num} (hn : M.InS n.1) :
    ∃ R E z S, M.IsLadder R E z S n ∧
      ∃ f, (∀ k : M.Num, ∃ a, M.mem (M.op M.zero a) R ∧ M.mem (M.op k.1 a) f ∧
          ∀ a', M.mem (M.op k.1 a') f → a' = a) ∧
        (∀ (k k' : M.Num) (a : V), M.mem (M.op k.1 a) f → M.mem (M.op k'.1 a) f → k = k') ∧
        (∀ a, M.mem (M.op M.zero a) R → ∃ k : M.Num, M.mem (M.op k.1 a) f) ∧
        M.mem (M.op M.zero z) f ∧
        ∀ (k : M.Num) (a b : V), M.mem (M.op k.1 a) f → M.mem (M.op a b) S →
          M.mem (M.op (M.succ k.1) b) f := by
  obtain ⟨R, E, z, S, h⟩ := M.exists_ladder hn
  exact ⟨R, E, z, S, h, M.ladder_base_iso h⟩

/-! ## Coding finite sets of numbers by numbers (remark of §2.1)

A number `c` codes the set of `i` whose binary digit in `c` is `1`. Every finite set of
natural numbers of the model is coded by a natural number of the model. -/

theorem succ_not_le_zero {x : M.Num} (h : x + 1 ≤ 0) : False := by
  obtain ⟨c, hc⟩ := M.le_def.mp h
  exact M.peano.1 (x + c) ((by ring : x + c + 1 = x + 1 + c).trans hc)

theorem lt_trichotomy' (i n : M.Num) : i = n ∨ i + 1 ≤ n ∨ n + 1 ≤ i := by
  rcases M.le_total' i n with h | h
  · rcases M.eq_or_succ_le h with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  · rcases M.eq_or_succ_le h with e | e
    · exact Or.inl e.symm
    · exact Or.inr (Or.inr e)

theorem expN_mono_add (n d : M.Num) : M.expN n ≤ M.expN (n + d) := by
  rw [M.expN_add]
  calc M.expN n = M.expN n * 1 := (mul_one _).symm
    _ ≤ M.expN n * M.expN d := mul_le_mul_of_nonneg_left (M.one_le_expN d) zero_le

/-- The binary digit `i` of `c` is `1`: `c = a · 2^(i+1) + 2^i + b` with `b < 2^i`. -/
def Bit (c i : M.Num) : Prop :=
  ∃ a b : M.Num, b + 1 ≤ M.expN i ∧ c = a * M.expN (i + 1) + M.expN i + b

theorem expN_le_of_bit {c i : M.Num} (h : M.Bit c i) : M.expN i ≤ c := by
  obtain ⟨a, b, -, hc⟩ := h
  exact M.le_def.mpr ⟨a * M.expN (i + 1) + b, by rw [hc]; ring⟩

theorem not_bit_of_lt {c n i : M.Num} (hc : c + 1 ≤ M.expN n) (hi : n ≤ i) : ¬ M.Bit c i := by
  intro h
  obtain ⟨d, hd⟩ := M.le_def.mp hi
  have h1 : M.expN n ≤ M.expN i := by
    rw [← hd]
    exact M.expN_mono_add n d
  exact M.not_succ_le c (le_trans hc (le_trans h1 (M.expN_le_of_bit h)))

theorem bit_top {c n : M.Num} (hc : c + 1 ≤ M.expN n) : M.Bit (c + M.expN n) n :=
  ⟨0, c, hc, by ring⟩

/-- Adding `2ⁿ` to a number below `2ⁿ` does not change the digits below `n`. -/
theorem bit_add_exp_iff {c n i : M.Num} (hc : c + 1 ≤ M.expN n) (hi : i + 1 ≤ n) :
    M.Bit (c + M.expN n) i ↔ M.Bit c i := by
  obtain ⟨d, hd⟩ := M.le_def.mp hi
  have hn : M.expN n = M.expN d * M.expN (i + 1) := by
    rw [← hd, M.expN_add, mul_comm]
  constructor
  · rintro ⟨a', b, hb, hcb⟩
    have ha' : M.expN d ≤ a' := by
      rcases M.le_total' (M.expN d) a' with h | h
      · exact h
      · rcases M.eq_or_succ_le h with e | e
        · exact le_of_eq e.symm
        · exfalso
          have h1 : c + M.expN n + 1 ≤ M.expN n := by
            calc c + M.expN n + 1 = a' * M.expN (i + 1) + (M.expN i + (b + 1)) := by
                  rw [hcb]
                  ring
              _ ≤ a' * M.expN (i + 1) + (M.expN i + M.expN i) :=
                  add_le_add (le_refl _) (add_le_add (le_refl _) hb)
              _ = (a' + 1) * M.expN (i + 1) := by
                  rw [M.expN_add_one]
                  ring
              _ ≤ M.expN d * M.expN (i + 1) := mul_le_mul_of_nonneg_right e zero_le
              _ = M.expN n := hn.symm
          have h2 : M.expN n + (c + 1) ≤ M.expN n :=
            le_of_eq_of_le (by ring : M.expN n + (c + 1) = c + M.expN n + 1) h1
          obtain ⟨f, hf⟩ := M.le_def.mp h2
          have h3 : M.addN (M.expN n) (c + f + 1) = M.addN (M.expN n) 0 := by
            show M.expN n + (c + f + 1) = M.expN n + 0
            rw [add_zero]
            exact (by ring : M.expN n + (c + f + 1) = M.expN n + (c + 1) + f).trans hf
          exact M.peano.1 (c + f) (M.addN_left_cancel h3)
    obtain ⟨a, ha⟩ := M.le_def.mp ha'
    refine ⟨a, b, hb, ?_⟩
    have h2 : M.addN (M.expN n) c =
        M.addN (M.expN n) (a * M.expN (i + 1) + M.expN i + b) := by
      show M.expN n + c = M.expN n + (a * M.expN (i + 1) + M.expN i + b)
      calc M.expN n + c = c + M.expN n := add_comm _ _
        _ = a' * M.expN (i + 1) + M.expN i + b := hcb
        _ = (M.expN d + a) * M.expN (i + 1) + M.expN i + b := by rw [ha]
        _ = M.expN n + (a * M.expN (i + 1) + M.expN i + b) := by
            rw [hn]
            ring
    exact M.addN_left_cancel h2
  · rintro ⟨a, b, hb, hcb⟩
    exact ⟨a + M.expN d, b, hb, by rw [hcb, hn]; ring⟩

/-- A number below `2ⁿ` codes every set of numbers below `n`. -/
def Codes (n : M.Num) : Prop :=
  ∀ s, M.isSet s → (∀ y, M.mem y s → ∃ j : M.Num, j.1 = y ∧ j + 1 ≤ n) →
    ∃ c : M.Num, c + 1 ≤ M.expN n ∧ ∀ i : M.Num, M.mem i.1 s ↔ M.Bit c i

theorem codes_zero : M.Codes 0 := by
  intro s hs hb
  refine ⟨0, le_of_eq ?_, fun i => ⟨fun hi => ?_, fun hbit => ?_⟩⟩
  · rw [zero_add]
    exact M.expN_zero.symm
  · obtain ⟨j, -, hj⟩ := hb _ hi
    exact (M.succ_not_le_zero hj).elim
  · exfalso
    have h1 := M.expN_le_of_bit hbit
    have h2 : (0 : M.Num) + 1 ≤ 0 := by
      rw [zero_add]
      exact le_trans (M.one_le_expN i) h1
    exact M.succ_not_le_zero h2

theorem codes_step {n : M.Num} (ih : M.Codes n) : M.Codes (n + 1) := by
  intro s hs hb
  have hb' : ∀ y, M.mem y (M.rem s n.1) → ∃ j : M.Num, j.1 = y ∧ j + 1 ≤ n := by
    intro y hy
    obtain ⟨hys, hyn⟩ := M.mem_rem.mp hy
    obtain ⟨j, hj, hjn⟩ := hb y hys
    refine ⟨j, hj, ?_⟩
    rcases M.eq_or_succ_le (M.le_of_succ_le_succ hjn) with e | e
    · exfalso
      apply hyn
      rw [← hj, e]
    · exact e
  obtain ⟨c', hc', hbit'⟩ := ih (M.rem s n.1) (M.rem_isSet _ _) hb'
  have hexp : M.expN (n + 1) = M.expN n + M.expN n := M.expN_add_one n
  have hc2 : c' + M.expN n + 1 ≤ M.expN (n + 1) := by
    rw [hexp]
    calc c' + M.expN n + 1 = (c' + 1) + M.expN n := by ring
      _ ≤ M.expN n + M.expN n := add_le_add hc' (le_refl _)
  by_cases hn : M.mem n.1 s
  · refine ⟨c' + M.expN n, hc2, fun i => ?_⟩
    rcases M.lt_trichotomy' i n with e | e | e
    · rw [e]
      exact ⟨fun _ => M.bit_top hc', fun _ => hn⟩
    · rw [M.bit_add_exp_iff hc' e, ← hbit' i, M.mem_rem]
      constructor
      · intro hi
        refine ⟨hi, fun hin => ?_⟩
        have ein : i = n := Subtype.ext hin
        rw [ein] at e
        exact M.not_succ_le n e
      · exact fun h => h.1
    · constructor
      · intro hi
        obtain ⟨j, hj, hjn⟩ := hb _ hi
        have eji : j = i := Subtype.ext hj
        rw [eji] at hjn
        exact absurd (le_trans e (M.le_of_succ_le_succ hjn)) (M.not_succ_le n)
      · intro hbit
        exact absurd hbit (M.not_bit_of_lt hc2 e)
  · refine ⟨c', ?_, fun i => ?_⟩
    · rw [hexp]
      exact le_trans hc' (M.le_def.mpr ⟨M.expN n, rfl⟩)
    · rw [← hbit' i, M.mem_rem]
      constructor
      · intro hi
        refine ⟨hi, fun hin => hn ?_⟩
        rw [← hin]
        exact hi
      · exact fun h => h.1

/-! ### The induction, as a stratified formula -/

/-- `Bit c i` with the numbers as objects, through the graphs of `+`, `·` and `2ˣ`. -/
def BitRaw (ad mu ex c i : V) : Prop :=
  ∃ a b p p1 s1 u v sb, M.mem (M.op i p) ex ∧ s1 = M.succ i ∧ M.mem (M.op s1 p1) ex ∧
    sb = M.succ b ∧ M.LeRaw ad sb p ∧ M.mem (M.trip a p1 u) mu ∧ M.mem (M.trip u p v) ad ∧
    M.mem (M.trip v b c) ad

/-- `Bit c i`; the names `6`, `7`, `18`, `19` stand for `ℕ` and the graphs of `+`, `·`, `2ˣ`. -/
def fBit (c i : ℕ) : Fml :=
  Fml.ex 20 (Fml.ex 21 (Fml.ex 22 (Fml.ex 23 (Fml.ex 24 (Fml.ex 25 (Fml.ex 26 (Fml.ex 27
    (.and (fApp 19 i 22) (.and (fSuccEq 24 i) (.and (fApp 19 24 23) (.and (fSuccEq 27 21)
      (.and (fLe 27 22) (.and (fApp3 18 20 23 25) (.and (fApp3 7 25 22 26)
        (fApp3 7 26 21 c)))))))))))))))

theorem bitRaw_iff {ad mu ex : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN)
    (hex : M.IsGraphOf ex M.expN) (c i : M.Num) : M.BitRaw ad mu ex c.1 i.1 ↔ M.Bit c i := by
  constructor
  · rintro ⟨a, b, p, p1, s1, u, v, sb, h1, h2, h3, h4, h5, h6, h7, h8⟩
    have e1 : p = (M.expN i).1 := M.graph_val hex h1
    rw [h2] at h3
    have e2 : p1 = (M.expN (M.nsucc i)).1 := M.graph_val hex (n := M.nsucc i) h3
    obtain ⟨A, P1, hA, hP1, hu⟩ := (hmu _ _ _).mp h6
    obtain ⟨U, P, hU, hP, hv⟩ := (had _ _ _).mp h7
    obtain ⟨W, B, hW, hB, hc⟩ := (had _ _ _).mp h8
    have eP1 : P1 = M.expN (i + 1) := Subtype.ext (by rw [hP1, e2, M.nsucc_eq_add_one])
    have eP : P = M.expN i := Subtype.ext (hP.trans e1)
    have eU : U = M.mulN A (M.expN (i + 1)) := Subtype.ext (by rw [hU, ← hu, eP1])
    have eW : W = M.addN (M.mulN A (M.expN (i + 1))) (M.expN i) :=
      Subtype.ext (by rw [hW, ← hv, eU, eP])
    refine ⟨A, B, ?_, ?_⟩
    · rw [h4, e1, ← hB] at h5
      have h9 := (M.leRaw_iff had (M.nsucc B) (M.expN i)).mp h5
      rw [M.nsucc_eq_add_one] at h9
      exact h9
    · show c = M.addN (M.addN (M.mulN A (M.expN (i + 1))) (M.expN i)) B
      exact Subtype.ext (by rw [← hc, eW])
  · rintro ⟨A, B, hB, hc⟩
    refine ⟨A.1, B.1, (M.expN i).1, (M.expN (i + 1)).1, (i + 1).1, (A * M.expN (i + 1)).1,
      (A * M.expN (i + 1) + M.expN i).1, (B + 1).1, M.graph_app hex i, M.val_add_one i,
      M.graph_app hex (i + 1), M.val_add_one B, (M.leRaw_iff had (B + 1) (M.expN i)).mpr hB,
      M.graph₂_app hmu A (M.expN (i + 1)), M.graph₂_app had _ _, ?_⟩
    rw [hc]
    exact M.graph₂_app had _ B

def CodeRaw (ad mu ex n : V) : Prop :=
  ∀ s, M.isSet s →
    (∀ y, M.mem y s → M.mem y M.nat ∧ ∃ sy, sy = M.succ y ∧ M.LeRaw ad sy n) →
    ∃ c, M.mem c M.nat ∧ (∃ sc pn, sc = M.succ c ∧ M.mem (M.op n pn) ex ∧ M.LeRaw ad sc pn) ∧
      ∀ i, M.mem i M.nat → (M.mem i s ↔ M.BitRaw ad mu ex c i)

def codeFml : Fml :=
  .all 10 (Fml.imp (.set 10) (Fml.imp
    (.all 11 (Fml.imp (.mem 11 10)
      (.and (.mem 11 6) (Fml.ex 12 (.and (fSuccEq 12 11) (fLe 12 0))))))
    (Fml.ex 9 (.and (.mem 9 6) (.and
      (Fml.ex 13 (Fml.ex 15 (.and (fSuccEq 13 9) (.and (fApp 19 0 15) (fLe 13 15)))))
      (.all 8 (Fml.imp (.mem 8 6) (Fml.iff (.mem 8 10) (fBit 9 8)))))))))

theorem codeRaw_iff {ad mu ex : V} (had : M.IsGraphOf₂ ad M.addN)
    (hmu : M.IsGraphOf₂ mu M.mulN) (hex : M.IsGraphOf ex M.expN) (n : M.Num) :
    M.CodeRaw ad mu ex n.1 ↔ M.Codes n := by
  constructor
  · intro h s hs hb
    obtain ⟨c, hc, ⟨sc, pn, hsc, hpn, hle⟩, hbit⟩ := h s hs (fun y hy => by
      obtain ⟨j, hj, hjn⟩ := hb y hy
      rw [← hj]
      refine ⟨j.2, _, rfl, (M.leRaw_iff had (M.nsucc j) n).mpr ?_⟩
      rw [M.nsucc_eq_add_one]
      exact hjn)
    refine ⟨⟨c, hc⟩, ?_, fun i => (hbit i.1 i.2).trans (M.bitRaw_iff had hmu hex ⟨c, hc⟩ i)⟩
    rw [hsc, M.graph_val hex hpn] at hle
    have h9 := (M.leRaw_iff had (M.nsucc ⟨c, hc⟩) (M.expN n)).mp hle
    rw [M.nsucc_eq_add_one] at h9
    exact h9
  · intro h s hs hraw
    obtain ⟨c, hc, hbit⟩ := h s hs (fun y hy => by
      obtain ⟨hyn, sy, hsy, hle⟩ := hraw y hy
      refine ⟨⟨y, hyn⟩, rfl, ?_⟩
      rw [hsy] at hle
      have h9 := (M.leRaw_iff had (M.nsucc ⟨y, hyn⟩) n).mp hle
      rw [M.nsucc_eq_add_one] at h9
      exact h9)
    refine ⟨c.1, c.2, ⟨_, _, rfl, M.graph_app hex n, (M.leRaw_iff had (M.nsucc c) (M.expN n)).mpr ?_⟩,
      fun i hi => (hbit ⟨i, hi⟩).trans (M.bitRaw_iff had hmu hex c ⟨i, hi⟩).symm⟩
    rw [M.nsucc_eq_add_one]
    exact hc

/-- **Every set of numbers below `n` is coded by a number below `2ⁿ`.** -/
theorem codes_all (n : M.Num) : M.Codes n := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  obtain ⟨mu, hmu⟩ := M.mulN_natOp
  obtain ⟨ex, hex⟩ := M.natFn_expN
  have hsat : ∀ k : V, Sat M.mem M.isSet codeFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 18 mu)
        19 ex) 0 k) ↔ M.CodeRaw ad mu ex k := by
    intro k
    simp [codeFml, fBit, fLe, CodeRaw, BitRaw, LeRaw, Sat, M.sat_imp, M.sat_iff, M.sat_ex,
      M.sat_fApp, M.sat_fApp3, M.sat_fSuccEq, Function.update_apply]
  have h0 : Sat M.mem M.isSet codeFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 18 mu)
        19 ex) 0 M.zero) := by
    rw [hsat]
    exact (M.codeRaw_iff had hmu hex 0).mpr M.codes_zero
  have hs : ∀ k : M.Num, Sat M.mem M.isSet codeFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 18 mu)
        19 ex) 0 k.1) →
      Sat M.mem M.isSet codeFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 18 mu)
        19 ex) 0 (M.succ k.1)) := by
    intro k ih
    rw [hsat] at ih ⊢
    have ih' := M.codes_step ((M.codeRaw_iff had hmu hex k).mp ih)
    have h9 := (M.codeRaw_iff had hmu hex (k + 1)).mpr ih'
    rw [M.val_add_one] at h9
    exact h9
  have key := M.num_ind_fml (σW [(6, 3), (7, 7), (10, 3), (18, 7), (19, 5)]) codeFml 0 rfl _
    h0 hs n
  rw [hsat] at key
  exact (M.codeRaw_iff had hmu hex n).mp key

/-! ### A finite set of numbers is bounded -/

def bddFml : Fml :=
  .all 10 (Fml.imp (.mem 10 0) (Fml.imp (.all 11 (Fml.imp (.mem 11 10) (.mem 11 6)))
    (Fml.ex 9 (.and (.mem 9 6) (.all 11 (Fml.imp (.mem 11 10)
      (Fml.ex 12 (.and (fSuccEq 12 11) (fLe 12 9)))))))))

theorem exists_bound {k s : V} (hk : M.mem k M.nat) (hs : M.mem s k)
    (hN : ∀ y, M.mem y s → M.mem y M.nat) :
    ∃ n : M.Num, ∀ y, M.mem y s → ∃ j : M.Num, j.1 = y ∧ j + 1 ≤ n := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  have hsat : ∀ k : V, Sat M.mem M.isSet bddFml (Function.update (Function.update
      (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 0 k) ↔
      ∀ s, M.mem s k → (∀ y, M.mem y s → M.mem y M.nat) →
        ∃ n, M.mem n M.nat ∧ ∀ y, M.mem y s → ∃ sy, sy = M.succ y ∧ M.LeRaw ad sy n := by
    intro k
    simp [bddFml, fLe, LeRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fApp3, M.sat_fSuccEq,
      Function.update_apply]
  have h0 : Sat M.mem M.isSet bddFml (Function.update (Function.update
      (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 0 M.zero) := by
    rw [hsat]
    intro s hs _
    refine ⟨M.zero, M.zero_mem_nat, fun y hy => ?_⟩
    rw [M.mem_zero.mp hs] at hy
    exact absurd hy (M.not_mem_emp y)
  have hs' : ∀ k, M.mem k M.nat → Sat M.mem M.isSet bddFml (Function.update (Function.update
      (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 0 k) →
      Sat M.mem M.isSet bddFml (Function.update (Function.update
      (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 0 (M.succ k)) := by
    intro k _ ih
    rw [hsat] at ih ⊢
    intro s hs hN
    obtain ⟨s', b, hs', -, hse⟩ := M.mem_succ.mp hs
    rw [hse] at hN ⊢
    obtain ⟨n', hn', hbd⟩ := ih s' hs' (fun y hy => hN y (M.mem_adj.mpr (Or.inl hy)))
    have hb : M.mem b M.nat := hN b (M.mem_adj.mpr (Or.inr rfl))
    refine ⟨((⟨n', hn'⟩ : M.Num) + ⟨b, hb⟩ + 1).1, ((⟨n', hn'⟩ : M.Num) + ⟨b, hb⟩ + 1).2,
      fun y hy => ⟨_, rfl, ?_⟩⟩
    have hyn : M.mem y M.nat := hN y hy
    refine (M.leRaw_iff had (M.nsucc ⟨y, hyn⟩) _).mpr ?_
    rw [M.nsucc_eq_add_one]
    rcases M.mem_adj.mp hy with hy' | hy'
    · obtain ⟨sy, hsy, hle⟩ := hbd y hy'
      rw [hsy] at hle
      have h9 := (M.leRaw_iff had (M.nsucc ⟨y, hyn⟩) ⟨n', hn'⟩).mp hle
      rw [M.nsucc_eq_add_one] at h9
      exact le_trans h9 (M.le_def.mpr ⟨⟨b, hb⟩ + 1, by ring⟩)
    · have e : (⟨y, hyn⟩ : M.Num) = ⟨b, hb⟩ := Subtype.ext hy'
      rw [e]
      exact M.le_def.mpr ⟨⟨n', hn'⟩, by ring⟩
  have key := M.nat_ind_fml' (σW [(0, 4), (6, 3), (7, 7), (10, 3)]) bddFml 0 rfl _ h0 hs' hk
  rw [hsat] at key
  obtain ⟨n, hn, hbd⟩ := key s hs hN
  refine ⟨⟨n, hn⟩, fun y hy => ?_⟩
  obtain ⟨sy, hsy, hle⟩ := hbd y hy
  refine ⟨⟨y, hN y hy⟩, rfl, ?_⟩
  rw [hsy] at hle
  have h9 := (M.leRaw_iff had (M.nsucc ⟨y, hN y hy⟩) ⟨n, hn⟩).mp hle
  rw [M.nsucc_eq_add_one] at h9
  exact h9

/-- **Every finite set of natural numbers is coded by a natural number**: there is `c` such
that `i` belongs to the set if and only if the binary digit `i` of `c` is `1`. -/
theorem exists_code {s : V} (hs : M.Fin s) (hN : ∀ y, M.mem y s → M.mem y M.nat) :
    ∃ c : M.Num, ∀ i : M.Num, M.mem i.1 s ↔ M.Bit c i := by
  obtain ⟨hset, k, hk, hsk⟩ := hs
  obtain ⟨n, hn⟩ := M.exists_bound hk hsk hN
  obtain ⟨c, -, hc⟩ := M.codes_all n s hset hn
  exact ⟨c, hc⟩

/-! ### Coding finite relations between numbers -/

/-- A pairing function on the natural numbers of the model. -/
noncomputable def pairN (x y : M.Num) : M.Num := (x + y) * (x + y) + x

theorem pairN_inj {x y x' y' : M.Num} (h : M.pairN x y = M.pairN x' y') : x = x' ∧ y = y' := by
  have key : ∀ x y x' y' : M.Num, (x + y) + 1 ≤ x' + y' →
      M.pairN x y + 1 ≤ M.pairN x' y' := by
    intro x y x' y' hs
    calc M.pairN x y + 1 = (x + y) * (x + y) + (x + 1) := by
          unfold pairN
          ring
      _ ≤ (x + y) * (x + y) + ((x + y) + (x + y) + 1) :=
          add_le_add (le_refl _) (M.le_def.mpr ⟨y + (x + y), by ring⟩)
      _ = (x + y + 1) * (x + y + 1) := by ring
      _ ≤ (x' + y') * (x' + y') := mul_le_mul hs hs zero_le zero_le
      _ ≤ M.pairN x' y' := M.le_def.mpr ⟨x', rfl⟩
  have hs : x + y = x' + y' := by
    rcases M.lt_trichotomy' (x + y) (x' + y') with e | e | e
    · exact e
    · have h1 := key x y x' y' e
      rw [h] at h1
      exact absurd h1 (M.not_succ_le _)
    · have h1 := key x' y' x y e
      rw [← h] at h1
      exact absurd h1 (M.not_succ_le _)
  have hx : x = x' := by
    have h2 : M.pairN x' y' = (x + y) * (x + y) + x' := by
      unfold pairN
      rw [← hs]
    have h1 : M.addN ((x + y) * (x + y)) x = M.addN ((x + y) * (x + y)) x' := h.trans h2
    exact M.addN_left_cancel h1
  have hy : y = y' := by
    rw [hx] at hs
    exact M.addN_left_cancel hs
  exact ⟨hx, hy⟩

theorem pairN_eq (x y : M.Num) :
    M.pairN x y = M.addN (M.mulN (M.addN x y) (M.addN x y)) x := rfl

theorem leRaw_of_add {ad : V} (had : M.IsGraphOf₂ ad M.addN) (a d : M.Num) :
    M.LeRaw ad a.1 (a + d).1 := ⟨d.1, d.2, M.graph₂_app had a d⟩

theorem leRaw_mono {ad : V} (had : M.IsGraphOf₂ ad M.addN) {a : V} {b c : M.Num}
    (h : M.LeRaw ad a b.1) (hbc : b ≤ c) : M.LeRaw ad a c.1 := by
  obtain ⟨d, hd, hmem⟩ := h
  obtain ⟨m, k, hm, hk, hmk⟩ := (had _ _ _).mp hmem
  obtain ⟨e, he⟩ := M.le_def.mp hbc
  refine ⟨(k + e).1, (k + e).2, ?_⟩
  have h1 := M.graph₂_app had m (k + e)
  have h3 : M.addN m k = b := Subtype.ext hmk
  have h2 : M.addN m (k + e) = c := by
    rw [← he, ← h3]
    exact (M.addN_assoc m k e).symm
  rw [h2, hm] at h1
  exact h1

def bddRelFml : Fml :=
  .all 10 (Fml.imp (.mem 10 0) (Fml.imp
    (.all 11 (Fml.imp (.mem 11 10)
      (Fml.ex 3 (Fml.ex 4 (.and (.mem 3 6) (.and (.mem 4 6) (fPr 11 3 4)))))))
    (Fml.ex 9 (.and (.mem 9 6) (.all 3 (.all 4 (Fml.imp (fApp 10 3 4)
      (Fml.ex 5 (Fml.ex 8 (Fml.ex 12 (Fml.ex 13 (.and (fApp3 7 3 4 5) (.and (fApp3 18 5 5 8)
        (.and (fApp3 7 8 3 12) (.and (fSuccEq 13 12) (fLe 13 9))))))))))))))))

theorem sat_bddRelFml (ad mu k : V) :
    Sat M.mem M.isSet bddRelFml (Function.update (Function.update
      (Function.update (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 18 mu) 0 k) ↔
      ∀ f, M.mem f k →
        (∀ p, M.mem p f → ∃ x y, M.mem x M.nat ∧ M.mem y M.nat ∧ p = M.op x y) →
        ∃ n, M.mem n M.nat ∧ ∀ x y, M.mem (M.op x y) f → ∃ s q w sw,
          M.mem (M.trip x y s) ad ∧ M.mem (M.trip s s q) mu ∧ M.mem (M.trip q x w) ad ∧
          sw = M.succ w ∧ M.LeRaw ad sw n := by
  simp [bddRelFml, fLe, LeRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fPr, M.sat_fApp, M.sat_fApp3,
    M.sat_fSuccEq, Function.update_apply]

/-- The step of the induction for `exists_bound_rel`. -/
theorem bound_rel_step {ad mu f' p0 : V} (had : M.IsGraphOf₂ ad M.addN)
    (hmu : M.IsGraphOf₂ mu M.mulN) (N' X0 Y0 : M.Num) (hp0 : p0 = M.op X0.1 Y0.1)
    (hbd : ∀ x y, M.mem (M.op x y) f' → ∃ s q w sw,
      M.mem (M.trip x y s) ad ∧ M.mem (M.trip s s q) mu ∧ M.mem (M.trip q x w) ad ∧
      sw = M.succ w ∧ M.LeRaw ad sw N'.1) :
    ∃ n, M.mem n M.nat ∧ ∀ x y, M.mem (M.op x y) (M.adj f' p0) → ∃ s q w sw,
      M.mem (M.trip x y s) ad ∧ M.mem (M.trip s s q) mu ∧ M.mem (M.trip q x w) ad ∧
      sw = M.succ w ∧ M.LeRaw ad sw n := by
  obtain ⟨B, hB⟩ : ∃ B : M.Num, B = N' + (M.pairN X0 Y0 + 1) := ⟨_, rfl⟩
  refine ⟨B.1, B.2, fun x y hxy => ?_⟩
  rcases M.mem_adj.mp hxy with h1 | h1
  · obtain ⟨s, q, w, sw, a1, a2, a3, a4, a5⟩ := hbd x y h1
    exact ⟨s, q, w, sw, a1, a2, a3, a4,
      M.leRaw_mono had a5 (M.le_def.mpr ⟨M.pairN X0 Y0 + 1, hB.symm⟩)⟩
  · obtain ⟨e1, e2⟩ := M.op_inj (h1.trans hp0)
    rw [e1, e2]
    have b1 := M.graph₂_app had X0 Y0
    have b2 := M.graph₂_app hmu (M.addN X0 Y0) (M.addN X0 Y0)
    have b3 := M.graph₂_app had (M.mulN (M.addN X0 Y0) (M.addN X0 Y0)) X0
    refine ⟨_, _, _, _, b1, b2, b3, rfl, ?_⟩
    have h5 := M.leRaw_of_add had (M.nsucc (M.pairN X0 Y0)) N'
    have e5 : M.nsucc (M.pairN X0 Y0) + N' = B := by
      rw [hB, M.nsucc_eq_add_one]
      exact add_comm _ _
    rw [e5, M.pairN_eq] at h5
    exact h5

/-- The codes of the pairs in a finite relation between numbers are bounded. -/
theorem exists_bound_rel {k f : V} (hk : M.mem k M.nat) (hf : M.mem f k)
    (hN : ∀ p, M.mem p f → ∃ x y : M.Num, p = M.op x.1 y.1) :
    ∃ n : M.Num, ∀ x y : M.Num, M.mem (M.op x.1 y.1) f → M.pairN x y + 1 ≤ n := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  obtain ⟨mu, hmu⟩ := M.mulN_natOp
  have h0 : Sat M.mem M.isSet bddRelFml (Function.update (Function.update
      (Function.update (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 18 mu) 0 M.zero) := by
    rw [M.sat_bddRelFml]
    intro f hf _
    refine ⟨M.zero, M.zero_mem_nat, fun x y hxy => ?_⟩
    rw [M.mem_zero.mp hf] at hxy
    exact absurd hxy (M.not_mem_emp _)
  have hs' : ∀ k, M.mem k M.nat → Sat M.mem M.isSet bddRelFml (Function.update (Function.update
      (Function.update (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 18 mu) 0 k) →
      Sat M.mem M.isSet bddRelFml (Function.update (Function.update
      (Function.update (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 18 mu) 0 (M.succ k)) := by
    intro k _ ih
    rw [M.sat_bddRelFml] at ih ⊢
    intro f hf hN
    obtain ⟨f', p0, hf', -, hfe⟩ := M.mem_succ.mp hf
    rw [hfe] at hN ⊢
    obtain ⟨n', hn', hbd⟩ := ih f' hf' (fun p hp => hN p (M.mem_adj.mpr (Or.inl hp)))
    obtain ⟨x0, y0, hx0, hy0, hp0⟩ := hN p0 (M.mem_adj.mpr (Or.inr rfl))
    exact M.bound_rel_step had hmu ⟨n', hn'⟩ ⟨x0, hx0⟩ ⟨y0, hy0⟩ hp0 hbd
  have key := M.nat_ind_fml' (σW [(0, 6), (6, 3), (7, 7), (10, 5), (11, 4), (18, 7)]) bddRelFml 0
    rfl _ h0 hs' hk
  rw [M.sat_bddRelFml] at key
  obtain ⟨n, hn, hbd⟩ := key f hf (fun p hp => by
    obtain ⟨x, y, e⟩ := hN p hp
    exact ⟨x.1, y.1, x.2, y.2, e⟩)
  refine ⟨⟨n, hn⟩, fun x y hxy => ?_⟩
  obtain ⟨s, q, w, sw, a1, a2, a3, a4, a5⟩ := hbd x.1 y.1 hxy
  have e1 : s = (M.addN x y).1 := M.graph₂_val had a1
  rw [e1] at a2
  have e2 : q = (M.mulN (M.addN x y) (M.addN x y)).1 := M.graph₂_val hmu a2
  rw [e2] at a3
  have e3 : w = (M.addN (M.mulN (M.addN x y) (M.addN x y)) x).1 := M.graph₂_val had a3
  rw [a4, e3] at a5
  have h9 := (M.leRaw_iff had (M.nsucc (M.addN (M.mulN (M.addN x y) (M.addN x y)) x))
    ⟨n, hn⟩).mp a5
  rw [← M.pairN_eq, M.nsucc_eq_add_one] at h9
  exact h9

/-- **Every finite relation between natural numbers is coded by a natural number**, through
the pairing function and binary digits. In particular every set function from one finite set
of numbers to another is coded. -/
theorem exists_code_rel {f : V} (hf : M.Fin f)
    (hN : ∀ p, M.mem p f → ∃ x y : M.Num, p = M.op x.1 y.1) :
    ∃ c : M.Num, ∀ x y : M.Num, M.mem (M.op x.1 y.1) f ↔ M.Bit c (M.pairN x y) := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  obtain ⟨mu, hmu⟩ := M.mulN_natOp
  obtain ⟨-, k, hk, hfk⟩ := hf
  obtain ⟨n, hn⟩ := M.exists_bound_rel hk hfk hN
  -- the set of codes of the pairs
  obtain ⟨S, hSs, hS0⟩ := M.comp (σW [(1, 5), (7, 7), (18, 7)])
    (Fml.ex 3 (Fml.ex 4 (Fml.ex 5 (Fml.ex 8 (.and (fApp 1 3 4) (.and (fApp3 7 3 4 5)
      (.and (fApp3 18 5 5 8) (fApp3 7 8 3 0)))))))) 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 1 f) 7 ad) 18 mu)
  have hS1 : ∀ w, M.mem w S ↔ ∃ x y s q, M.mem (M.op x y) f ∧ M.mem (M.trip x y s) ad ∧
      M.mem (M.trip s s q) mu ∧ M.mem (M.trip q x w) ad := by
    intro w
    rw [hS0 w]
    simp [M.sat_ex, Sat, M.sat_fApp, M.sat_fApp3, Function.update_apply]
  have hS : ∀ w, M.mem w S ↔ ∃ x y : M.Num, M.mem (M.op x.1 y.1) f ∧ w = (M.pairN x y).1 := by
    intro w
    rw [hS1]
    constructor
    · rintro ⟨x, y, s, q, hxy, a1, a2, a3⟩
      obtain ⟨X, Y, e⟩ := hN _ hxy
      obtain ⟨e1, e2⟩ := M.op_inj e
      rw [e1, e2] at hxy a1
      rw [e1] at a3
      have h1 : s = (M.addN X Y).1 := M.graph₂_val had a1
      rw [h1] at a2
      have h2 : q = (M.mulN (M.addN X Y) (M.addN X Y)).1 := M.graph₂_val hmu a2
      rw [h2] at a3
      exact ⟨X, Y, hxy, M.graph₂_val had a3⟩
    · rintro ⟨X, Y, hxy, e⟩
      refine ⟨X.1, Y.1, (X + Y).1, ((X + Y) * (X + Y)).1, hxy, M.graph₂_app had X Y,
        M.graph₂_app hmu _ _, ?_⟩
      rw [e]
      exact M.graph₂_app had _ X
  obtain ⟨c, -, hc⟩ := M.codes_all n S hSs (fun w hw => by
    obtain ⟨x, y, hxy, e⟩ := (hS w).mp hw
    exact ⟨M.pairN x y, e.symm, hn x y hxy⟩)
  refine ⟨c, fun x y => ?_⟩
  rw [← hc (M.pairN x y), hS]
  constructor
  · intro hxy
    exact ⟨x, y, hxy, rfl⟩
  · rintro ⟨x', y', hxy, e⟩
    obtain ⟨e1, e2⟩ := M.pairN_inj (Subtype.ext e)
    rw [e1, e2]
    exact hxy

end Model

end NFUCut
