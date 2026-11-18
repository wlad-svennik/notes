module

public import ConNF.NF.NFUCut

/-!
# Arithmetic in NFU + Infinity (§2 of the note)

This file continues `NFUCut`. It works in an arbitrary model `M` of NFU with the axiom of
Infinity, given as `[Fact M.Infinity]`.

* The natural numbers of the model are pairwise disjoint (`nat_disjoint`), successor is
  injective (`succ_inj`) and zero is not a successor. `M.Num` is the type of natural numbers
  of the model.
* A function `M.Num → M.Num` is a *set function* (`NatFn`) if its graph is a set of the model.
  Set functions are closed under composition, and the numbers satisfying an equation or an
  inequality between set functions, or a Boolean combination of these, form a set, so
  induction holds for such conditions (`num_ind`).
* **Recursion** (`exists_prec`, `prec_unique`): for set functions `h` and `g` there is a unique
  set function `F` with `F a 0 = h a` and `F a (b + 1) = g a (F a b)`.
* Addition, multiplication, `2ˣ` and the tower are defined by recursion. With them `M.Num` is
  a commutative semiring with a compatible order (`instCommSemiringNum`,
  `instIsOrderedRingNum`, `instCanonicallyOrderedAddNum`).
* **Peano arithmetic** (`peano`, `pa_induction`): the natural numbers of the model satisfy
  the axioms of Robinson arithmetic and the induction schema for every formula of arithmetic.
* The operation `T` (`T`, `T_zero`, `T_succ`).
* **Lemma 2.2** (`lemma_2_2`): the cut of natural numbers with a strongly cantorian member is
  closed downwards and under successor, `+`, `·` and `2ˣ`, and is fixed pointwise by `T`.
  The link with the recursive exponential is `pow_mem_expN`: if `y ∈ m` and the singleton
  image of `y` is in `n`, then `P(y) ∈ 2ⁿ`.
* **Lemma 2.3** (`lemma_2_3`): tower absorption, for the tower and exponential of the model.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

@[expose] public section

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V)

/-! ## Small additions to the set operations -/

theorem exists_inter (A B : V) : ∃ U, M.isSet U ∧ ∀ c, M.mem c U ↔ M.mem c A ∧ M.mem c B := by
  obtain ⟨U, hU, h⟩ := M.comp (fun i => if i = 0 then 0 else 1) (.and (.mem 0 1) (.mem 0 2)) 0
    rfl (Function.update (Function.update (fun _ => dflt) 1 A) 2 B)
  refine ⟨U, hU, fun c => ?_⟩
  simpa [Sat, Function.update_apply] using h c

/-- Induction for a stratified formula, with `k ∈ ℕ` available in the step. -/
theorem nat_ind_fml' (σ : ℕ → ℕ) (φ : Fml) (x : ℕ) (hφ : φ.strat σ = true) (ρ : ℕ → V)
    (h0 : Sat M.mem M.isSet φ (Function.update ρ x M.zero))
    (hs : ∀ k, M.mem k M.nat → Sat M.mem M.isSet φ (Function.update ρ x k) →
      Sat M.mem M.isSet φ (Function.update ρ x (M.succ k)))
    {n : V} (hn : M.mem n M.nat) : Sat M.mem M.isSet φ (Function.update ρ x n) := by
  obtain ⟨I, -, hI⟩ := M.comp σ φ x hφ ρ
  obtain ⟨J, -, hJ⟩ := M.exists_inter I M.nat
  have key := M.nat_ind (I := J) ((hJ _).mpr ⟨(hI _).mpr h0, M.zero_mem_nat⟩)
    (fun k hk => (hJ _).mpr ⟨(hI _).mpr (hs k ((hJ k).mp hk).2 ((hI k).mp ((hJ k).mp hk).1)),
      M.succ_mem_nat ((hJ k).mp hk).2⟩) hn
  exact (hI n).mp ((hJ n).mp key).1

/-- `z ∖ {b}`. -/
noncomputable def rem (z b : V) : V := Classical.choose (M.exists_rem z b)

theorem rem_isSet (z b : V) : M.isSet (M.rem z b) := (Classical.choose_spec (M.exists_rem z b)).1

theorem mem_rem {z b e : V} : M.mem e (M.rem z b) ↔ M.mem e z ∧ e ≠ b :=
  (Classical.choose_spec (M.exists_rem z b)).2 e

theorem eq_rem_iff {r z b : V} :
    (M.isSet r ∧ ∀ e, M.mem e r ↔ M.mem e z ∧ ¬ e = b) ↔ r = M.rem z b := by
  constructor
  · rintro ⟨hr, h⟩
    exact M.ext hr (M.rem_isSet z b) fun e => (h e).trans M.mem_rem.symm
  · rintro rfl
    exact ⟨M.rem_isSet z b, fun e => M.mem_rem⟩

theorem rem_adj_self {x b : V} (hx : M.isSet x) (hb : ¬ M.mem b x) : M.rem (M.adj x b) b = x := by
  refine M.ext (M.rem_isSet _ _) hx fun e => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2⟩ := M.mem_rem.mp h
    exact (M.mem_adj.mp h1).resolve_right h2
  · refine M.mem_rem.mpr ⟨M.mem_adj.mpr (Or.inl h), fun he => hb ?_⟩
    rw [← he]
    exact h

theorem eq_simg_iff {S y : V} :
    (M.isSet S ∧ ∀ s, M.mem s S ↔ ∃ a, M.mem a y ∧ s = M.sing a) ↔ S = M.simg y := by
  constructor
  · rintro ⟨hS, h⟩
    exact M.ext hS (M.simg_isSet y) fun s => (h s).trans M.mem_simg.symm
  · rintro rfl
    exact ⟨M.simg_isSet y, fun s => M.mem_simg⟩

/-! ## Zero and successor -/

theorem emp_not_mem_succ (k : V) : ¬ M.mem M.emp (M.succ k) := by
  intro h
  obtain ⟨x, b, -, -, e⟩ := M.mem_succ.mp h
  have hb : M.mem b (M.adj x b) := M.mem_adj.mpr (Or.inr rfl)
  rw [← e] at hb
  exact M.not_mem_emp b hb

theorem zero_ne_succ (k : V) : M.zero ≠ M.succ k := by
  intro h
  have h1 : M.mem M.emp M.zero := M.mem_zero.mpr rfl
  rw [h] at h1
  exact M.emp_not_mem_succ k h1

/-- `s` is the successor of `k`, with bound names `40`–`43`. -/
def fSuccEq (s k : ℕ) : Fml := fSucc s k 40 41 42 43

theorem sat_fSuccEq {s k : ℕ} (ρ : ℕ → V) (hs : s < 30) (hk : k < 30) :
    Sat M.mem M.isSet (fSuccEq s k) ρ ↔ ρ s = M.succ (ρ k) :=
  M.sat_fSucc (by omega) (by omega) (by decide) (by decide) (by decide) (by omega) (by omega)
    (by decide) (by decide) (by decide) ρ

/-- The types of the bound names used by the formulas for pairs, triples and successor, when
numbers have type `2`. -/
def σN : ℕ → ℕ := fun i =>
  match i with
  | 32 => 4 | 33 => 4 | 34 => 5 | 35 => 4 | 36 => 3 | 37 => 2 | 38 => 4 | 39 => 6
  | 40 => 1 | 41 => 1 | 42 => 0 | 43 => 0 | _ => 2

/-- `σN` with the types of some names overridden. -/
def σW (l : List (ℕ × ℕ)) : ℕ → ℕ := fun i => (l.lookup i).getD (σN i)

def casesFml : Fml := Fml.or (.eq 0 1) (Fml.ex 3 (.and (.mem 3 2) (fSuccEq 0 3)))

/-- A natural number is zero or a successor. -/
theorem nat_cases {n : V} (hn : M.mem n M.nat) :
    n = M.zero ∨ ∃ k, M.mem k M.nat ∧ n = M.succ k := by
  have hsat : ∀ m, Sat M.mem M.isSet casesFml
      (Function.update (Function.update (Function.update (fun _ => dflt) 1 M.zero) 2 M.nat) 0 m) ↔
      (m = M.zero ∨ ∃ k, M.mem k M.nat ∧ m = M.succ k) := by
    intro m
    simp [casesFml, M.sat_or, M.sat_ex, Sat, M.sat_fSuccEq, Function.update_apply]
  have key := M.nat_ind_fml' (σW [(2, 3)]) casesFml 0 rfl _ ((hsat _).mpr (Or.inl rfl))
    (fun k hk _ => (hsat _).mpr (Or.inr ⟨k, hk, rfl⟩)) hn
  exact (hsat n).mp key

def remFml : Fml :=
  .all 1 (Fml.imp (fSuccEq 1 0) (.all 2 (Fml.imp (.mem 2 1) (.all 3 (Fml.imp (.mem 3 2)
    (.all 4 (Fml.imp
      (.and (.set 4) (.all 5 (Fml.iff (.mem 5 4) (.and (.mem 5 2) (.neg (.eq 5 3))))))
      (.mem 4 0))))))))

theorem sat_remFml (n : V) :
    Sat M.mem M.isSet remFml (Function.update (fun _ => dflt) 0 n) ↔
    ∀ y, M.mem y (M.succ n) → ∀ c, M.mem c y → M.mem (M.rem y c) n := by
  have h1 : Sat M.mem M.isSet remFml (Function.update (fun _ => dflt) 0 n) ↔
      ∀ s, s = M.succ n → ∀ y, M.mem y s → ∀ c, M.mem c y → ∀ r,
        (M.isSet r ∧ ∀ e, M.mem e r ↔ M.mem e y ∧ ¬ e = c) → M.mem r n := by
    simp [remFml, Sat, M.sat_imp, M.sat_iff, M.sat_fSuccEq, Function.update_apply]
  rw [h1]
  constructor
  · intro h y hy c hc
    exact h _ rfl y hy c hc _ ⟨M.rem_isSet y c, fun e => M.mem_rem⟩
  · rintro h s rfl y hy c hc r hr
    rw [M.eq_rem_iff.mp hr]
    exact h y hy c hc

/-- Removing an element from a member of `n + 1` gives a member of `n`. -/
theorem rem_mem_of_succ {n y c : V} (hn : M.mem n M.nat) (hy : M.mem y (M.succ n))
    (hc : M.mem c y) : M.mem (M.rem y c) n := by
  have h0 : Sat M.mem M.isSet remFml (Function.update (fun _ => dflt) 0 M.zero) := by
    rw [M.sat_remFml]
    intro y hy c hc
    obtain ⟨x, b, hx, hb, rfl⟩ := M.mem_succ.mp hy
    obtain rfl := M.mem_zero.mp hx
    have hcb : c = b := (M.mem_adj.mp hc).resolve_left (M.not_mem_emp c)
    rw [hcb, M.rem_adj_self M.emp_isSet hb]
    exact M.mem_zero.mpr rfl
  have hs : ∀ k, M.mem k M.nat → Sat M.mem M.isSet remFml (Function.update (fun _ => dflt) 0 k) →
      Sat M.mem M.isSet remFml (Function.update (fun _ => dflt) 0 (M.succ k)) := by
    intro k hk ih
    rw [M.sat_remFml] at ih ⊢
    intro y hy c hc
    obtain ⟨x, b, hx, hb, rfl⟩ := M.mem_succ.mp hy
    have hxs : M.isSet x := by
      obtain ⟨x', b', -, -, e⟩ := M.mem_succ.mp hx
      rw [e]
      exact M.adj_isSet _ _
    by_cases hcb : c = b
    · rw [hcb, M.rem_adj_self hxs hb]
      exact hx
    · have hcx : M.mem c x := (M.mem_adj.mp hc).resolve_right hcb
      have e : M.rem (M.adj x b) c = M.adj (M.rem x c) b := by
        refine M.ext (M.rem_isSet _ _) (M.adj_isSet _ _) fun z => ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨h1, h2⟩ := M.mem_rem.mp h
          rcases M.mem_adj.mp h1 with h1 | h1
          · exact M.mem_adj.mpr (Or.inl (M.mem_rem.mpr ⟨h1, h2⟩))
          · exact M.mem_adj.mpr (Or.inr h1)
        · rcases M.mem_adj.mp h with h | h
          · obtain ⟨h1, h2⟩ := M.mem_rem.mp h
            exact M.mem_rem.mpr ⟨M.mem_adj.mpr (Or.inl h1), h2⟩
          · exact M.mem_rem.mpr ⟨M.mem_adj.mpr (Or.inr h), fun hzc => hcb (hzc.symm.trans h)⟩
      rw [e]
      exact M.mem_succ.mpr ⟨_, b, ih x hx c hcx, fun h => hb (M.mem_rem.mp h).1, rfl⟩
  have key := M.nat_ind_fml' (σW [(2, 1), (3, 0), (4, 1), (5, 0)]) remFml 0 rfl _ h0 hs hn
  rw [M.sat_remFml] at key
  exact key y hy c hc

def disjFml : Fml :=
  .all 2 (Fml.imp (.mem 2 1) (.all 3 (Fml.imp (.mem 3 0) (Fml.imp (.mem 3 2) (.eq 0 2)))))

theorem sat_disjFml (m : V) :
    Sat M.mem M.isSet disjFml (Function.update (Function.update (fun _ => dflt) 1 M.nat) 0 m) ↔
    ∀ n, M.mem n M.nat → ∀ x, M.mem x m → M.mem x n → m = n := by
  simp [disjFml, Sat, M.sat_imp, Function.update_apply]

/-- **Two natural numbers with a common member are equal.** -/
theorem nat_disjoint {m n x : V} (hm : M.mem m M.nat) (hn : M.mem n M.nat) (hxm : M.mem x m)
    (hxn : M.mem x n) : m = n := by
  have h0 : Sat M.mem M.isSet disjFml
      (Function.update (Function.update (fun _ => dflt) 1 M.nat) 0 M.zero) := by
    rw [M.sat_disjFml]
    intro n hn x hx0 hxn
    obtain rfl := M.mem_zero.mp hx0
    rcases M.nat_cases hn with h | ⟨k, hk, h⟩
    · exact h.symm
    · rw [h] at hxn
      exact absurd hxn (M.emp_not_mem_succ k)
  have hs : ∀ k, M.mem k M.nat → Sat M.mem M.isSet disjFml
      (Function.update (Function.update (fun _ => dflt) 1 M.nat) 0 k) →
      Sat M.mem M.isSet disjFml
      (Function.update (Function.update (fun _ => dflt) 1 M.nat) 0 (M.succ k)) := by
    intro k hk ih
    rw [M.sat_disjFml] at ih ⊢
    intro n hn x hxk hxn
    rcases M.nat_cases hn with h | ⟨k', hk', h⟩
    · rw [h] at hxn
      have hx := M.mem_zero.mp hxn
      rw [hx] at hxk
      exact absurd hxk (M.emp_not_mem_succ k)
    · rw [h] at hxn ⊢
      obtain ⟨x', b, hx', hb, rfl⟩ := M.mem_succ.mp hxk
      have h1 := M.rem_mem_of_succ hk' hxn (M.mem_adj.mpr (Or.inr rfl))
      rw [M.rem_adj_self (M.isSet_of_mem_nat hk hx') hb] at h1
      rw [ih k' hk' x' hx' h1]
  have key := M.nat_ind_fml' (σW [(1, 3), (3, 1)]) disjFml 0 rfl _ h0 hs hm
  rw [M.sat_disjFml] at key
  exact key n hn x hxm hxn

/-! ## Pairs and triples in formulas -/

/-- `p = ⟨a, b⟩`, with bound names `36`, `37`. -/
def fPr (p a b : ℕ) : Fml := fOp p a b 36 37

theorem sat_fPr {p a b : ℕ} (ρ : ℕ → V) (hp : p < 30) (ha : a < 30) (hb : b < 30) :
    Sat M.mem M.isSet (fPr p a b) ρ ↔ ρ p = M.op (ρ a) (ρ b) :=
  M.sat_fOp (by omega) (by omega) (by omega) (by omega) (by omega) (by decide) ρ

/-- `⟨a, b⟩ ∈ g`, with bound names `36`–`38`. -/
def fApp (g a b : ℕ) : Fml := Fml.ex 38 (.and (.mem 38 g) (fOp 38 a b 36 37))

theorem sat_fApp {g a b : ℕ} (ρ : ℕ → V) (hg : g < 30) (ha : a < 30) (hb : b < 30) :
    Sat M.mem M.isSet (fApp g a b) ρ ↔ M.mem (M.op (ρ a) (ρ b)) (ρ g) := by
  have h1 : g ≠ 38 := by omega
  have h2 : a ≠ 38 := by omega
  have h3 : b ≠ 38 := by omega
  simp only [fApp, M.sat_ex, Sat,
    M.sat_fOp (p := 38) (a := a) (b := b) (u := 36) (c := 37) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro h
    exact ⟨_, h, rfl⟩

/-- The triple `⟨⟨a, b⟩, ⟨c, c⟩⟩`. Its three components have the same type. -/
noncomputable def trip (a b c : V) : V := M.op (M.op a b) (M.op c c)

theorem trip_inj {a b c a' b' c' : V} (h : M.trip a b c = M.trip a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨h1, h2⟩ := M.op_inj h
  obtain ⟨ha, hb⟩ := M.op_inj h1
  exact ⟨ha, hb, (M.op_inj h2).1⟩

/-- `q = ⟨a, b, c⟩`, with bound names `32`–`37`. -/
def fTrip (q a b c : ℕ) : Fml :=
  Fml.ex 32 (Fml.ex 33 (.and (fOp q 32 33 34 35) (.and (fOp 32 a b 36 37) (fOp 33 c c 36 37))))

theorem sat_fTrip {q a b c : ℕ} (ρ : ℕ → V) (hq : q < 30 ∨ q = 39) (ha : a < 30 ∨ 99 < a)
    (hb : b < 30 ∨ 99 < b) (hc : c < 30 ∨ 99 < c) :
    Sat M.mem M.isSet (fTrip q a b c) ρ ↔ ρ q = M.trip (ρ a) (ρ b) (ρ c) := by
  have q32 : q ≠ 32 := by omega
  have q33 : q ≠ 33 := by omega
  have a32 : a ≠ 32 := by omega
  have a33 : a ≠ 33 := by omega
  have b32 : b ≠ 32 := by omega
  have b33 : b ≠ 33 := by omega
  have c32 : c ≠ 32 := by omega
  have c33 : c ≠ 33 := by omega
  simp only [fTrip, M.sat_ex, Sat,
    M.sat_fOp (p := q) (a := 32) (b := 33) (u := 34) (c := 35) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    M.sat_fOp (p := 32) (a := a) (b := b) (u := 36) (c := 37) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    M.sat_fOp (p := 33) (a := c) (b := c) (u := 36) (c := 37) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    Function.update_self, Function.update_of_ne q32, Function.update_of_ne q33,
    Function.update_of_ne a32, Function.update_of_ne a33, Function.update_of_ne b32,
    Function.update_of_ne b33, Function.update_of_ne c32, Function.update_of_ne c33,
    Function.update_of_ne (show (32 : ℕ) ≠ 33 by decide)]
  unfold trip
  constructor
  · rintro ⟨p1, p2, h1, rfl, rfl⟩
    exact h1
  · intro h
    exact ⟨_, _, h, rfl, rfl⟩

/-- `⟨a, b, c⟩ ∈ G`, with bound names `32`–`37` and `39`. -/
def fApp3 (G a b c : ℕ) : Fml := Fml.ex 39 (.and (.mem 39 G) (fTrip 39 a b c))

theorem sat_fApp3 {G a b c : ℕ} (ρ : ℕ → V) (hG : G < 30) (ha : a < 30 ∨ 99 < a)
    (hb : b < 30 ∨ 99 < b) (hc : c < 30 ∨ 99 < c) :
    Sat M.mem M.isSet (fApp3 G a b c) ρ ↔ M.mem (M.trip (ρ a) (ρ b) (ρ c)) (ρ G) := by
  have h1 : G ≠ 39 := by omega
  have h2 : a ≠ 39 := by omega
  have h3 : b ≠ 39 := by omega
  have h4 : c ≠ 39 := by omega
  simp only [fApp3, M.sat_ex, Sat,
    fun ρ' : ℕ → V => M.sat_fTrip (q := 39) (a := a) (b := b) (c := c) ρ' (Or.inr rfl) ha hb hc,
    Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

/-! ## Infinity as a standing assumption -/

variable [hinf : Fact M.Infinity]

/-- With Infinity, every natural number has a member. -/
theorem nat_nonempty {n : V} (hn : M.mem n M.nat) : ∃ x, M.mem x n := by
  have hsat : ∀ m, Sat M.mem M.isSet (Fml.ex 1 (.mem 1 0)) (Function.update (fun _ => dflt) 0 m) ↔
      ∃ x, M.mem x m := by
    intro m
    simp [M.sat_ex, Sat, Function.update_apply]
  have key := M.nat_ind_fml' (fun i => if i = 0 then 1 else 0) (Fml.ex 1 (.mem 1 0)) 0 rfl _
    ((hsat _).mpr ⟨M.emp, M.mem_zero.mpr rfl⟩)
    (fun k hk ih => (hsat _).mpr (by
      obtain ⟨x, hx⟩ := (hsat _).mp ih
      obtain ⟨b, hb⟩ := M.infinity_iff.mp hinf.out k hk x hx
      exact ⟨M.adj x b, M.mem_succ.mpr ⟨x, b, hx, hb, rfl⟩⟩)) hn
  exact (hsat n).mp key

/-- With Infinity, successor is injective on the natural numbers. -/
theorem succ_inj {m n : V} (hm : M.mem m M.nat) (hn : M.mem n M.nat)
    (h : M.succ m = M.succ n) : m = n := by
  obtain ⟨x, hx⟩ := M.nat_nonempty hm
  obtain ⟨b, hb⟩ := M.infinity_iff.mp hinf.out m hm x hx
  have h1 : M.mem (M.adj x b) (M.succ n) := by
    rw [← h]
    exact M.mem_succ.mpr ⟨x, b, hx, hb, rfl⟩
  have h2 := M.rem_mem_of_succ hn h1 (M.mem_adj.mpr (Or.inr rfl))
  rw [M.rem_adj_self (M.isSet_of_mem_nat hm hx) hb] at h2
  exact M.nat_disjoint hm hn hx h2

/-! ## The natural numbers of the model as a type -/

/-- The natural numbers of the model. -/
abbrev Num (M : Model V) : Type := {n : V // M.mem n M.nat}

/-- Zero. -/
noncomputable def nzero : M.Num := ⟨M.zero, M.zero_mem_nat⟩

/-- Successor. -/
noncomputable def nsucc (n : M.Num) : M.Num := ⟨M.succ n.1, M.succ_mem_nat n.2⟩

theorem nsucc_inj {m n : M.Num} (h : M.nsucc m = M.nsucc n) : m = n :=
  Subtype.ext (M.succ_inj m.2 n.2 (congrArg Subtype.val h))

theorem nzero_ne_nsucc (n : M.Num) : M.nzero ≠ M.nsucc n := fun h =>
  M.zero_ne_succ n.1 (congrArg Subtype.val h)

theorem num_cases (n : M.Num) : n = M.nzero ∨ ∃ k, n = M.nsucc k := by
  rcases M.nat_cases n.2 with h | ⟨k, hk, h⟩
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr ⟨⟨k, hk⟩, Subtype.ext h⟩

/-- Induction on the numbers of the model for a stratified formula. -/
theorem num_ind_fml (σ : ℕ → ℕ) (φ : Fml) (x : ℕ) (hφ : φ.strat σ = true) (ρ : ℕ → V)
    (h0 : Sat M.mem M.isSet φ (Function.update ρ x M.zero))
    (hs : ∀ k : M.Num, Sat M.mem M.isSet φ (Function.update ρ x k.1) →
      Sat M.mem M.isSet φ (Function.update ρ x (M.succ k.1)))
    (n : M.Num) : Sat M.mem M.isSet φ (Function.update ρ x n.1) :=
  M.nat_ind_fml' σ φ x hφ ρ h0 (fun k hk ih => hs ⟨k, hk⟩ ih) n.2

/-! ## Set functions and set conditions on the natural numbers -/

/-- The pairs in `f` are exactly the pairs `⟨n, F n⟩`. -/
def IsGraphOf (f : V) (F : M.Num → M.Num) : Prop :=
  ∀ a u : V, M.mem (M.op a u) f ↔ ∃ n : M.Num, n.1 = a ∧ (F n).1 = u

/-- `F` is a set function: its graph is a set of the model. -/
def NatFn (F : M.Num → M.Num) : Prop := ∃ f, M.IsGraphOf f F

/-- The triples in `G` are exactly the triples `⟨m, n, H m n⟩`. -/
def IsGraphOf₂ (G : V) (H : M.Num → M.Num → M.Num) : Prop :=
  ∀ a b c : V, M.mem (M.trip a b c) G ↔ ∃ m n : M.Num, m.1 = a ∧ n.1 = b ∧ (H m n).1 = c

/-- `H` is a set function of two arguments. -/
def NatOp (H : M.Num → M.Num → M.Num) : Prop := ∃ G, M.IsGraphOf₂ G H

/-- The numbers satisfying `P` form a set of the model. -/
def IsPred (P : M.Num → Prop) : Prop := ∃ s, ∀ v : V, M.mem v s ↔ ∃ n : M.Num, n.1 = v ∧ P n

theorem graph_app {f : V} {F : M.Num → M.Num} (h : M.IsGraphOf f F) (n : M.Num) :
    M.mem (M.op n.1 (F n).1) f := (h _ _).mpr ⟨n, rfl, rfl⟩

theorem graph_val {f : V} {F : M.Num → M.Num} (h : M.IsGraphOf f F) {n : M.Num} {u : V}
    (hu : M.mem (M.op n.1 u) f) : u = (F n).1 := by
  obtain ⟨n', h1, h2⟩ := (h _ _).mp hu
  have e : n' = n := Subtype.ext h1
  rw [← h2, e]

theorem graph₂_app {G : V} {H : M.Num → M.Num → M.Num} (h : M.IsGraphOf₂ G H) (m n : M.Num) :
    M.mem (M.trip m.1 n.1 (H m n).1) G := (h _ _ _).mpr ⟨m, n, rfl, rfl, rfl⟩

theorem graph₂_val {G : V} {H : M.Num → M.Num → M.Num} (h : M.IsGraphOf₂ G H) {m n : M.Num}
    {u : V} (hu : M.mem (M.trip m.1 n.1 u) G) : u = (H m n).1 := by
  obtain ⟨m', n', h1, h2, h3⟩ := (h _ _ _).mp hu
  have e1 : m' = m := Subtype.ext h1
  have e2 : n' = n := Subtype.ext h2
  rw [← h3, e1, e2]

/-- **Induction for set conditions.** -/
theorem num_ind {P : M.Num → Prop} (hP : M.IsPred P) (h0 : P M.nzero)
    (hs : ∀ k, P k → P (M.nsucc k)) (n : M.Num) : P n := by
  obtain ⟨s, hs'⟩ := hP
  have key := M.nat_ind (I := s) ((hs' _).mpr ⟨M.nzero, rfl, h0⟩) (fun k hk => by
    obtain ⟨m, hmk, hm⟩ := (hs' k).mp hk
    rw [← hmk]
    exact (hs' _).mpr ⟨M.nsucc m, rfl, hs m hm⟩) n.2
  obtain ⟨m, hm, hPm⟩ := (hs' _).mp key
  have e : m = n := Subtype.ext hm
  rw [← e]
  exact hPm

theorem isPred_congr {P Q : M.Num → Prop} (h : ∀ n, P n ↔ Q n) (hP : M.IsPred P) :
    M.IsPred Q := by
  obtain ⟨s, hs⟩ := hP
  exact ⟨s, fun v => (hs v).trans
    ⟨fun ⟨n, hn, hp⟩ => ⟨n, hn, (h n).mp hp⟩, fun ⟨n, hn, hq⟩ => ⟨n, hn, (h n).mpr hq⟩⟩⟩

theorem isPred_const (p : Prop) : M.IsPred (fun _ => p) := by
  by_cases hp : p
  · refine ⟨M.nat, fun v => ⟨fun h => ⟨⟨v, h⟩, rfl, hp⟩, ?_⟩⟩
    rintro ⟨n, hn, -⟩
    rw [← hn]
    exact n.2
  · exact ⟨M.emp, fun v => ⟨fun h => absurd h (M.not_mem_emp v), fun ⟨_, _, h⟩ => absurd h hp⟩⟩

theorem isPred_not {P : M.Num → Prop} (hP : M.IsPred P) : M.IsPred (fun n => ¬ P n) := by
  obtain ⟨s, hs⟩ := hP
  obtain ⟨t, -, ht⟩ := M.comp (fun i => if i = 0 then 0 else 1)
    (.and (.mem 0 1) (.neg (.mem 0 2))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 M.nat) 2 s)
  have ht' : ∀ v, M.mem v t ↔ M.mem v M.nat ∧ ¬ M.mem v s := by
    intro v
    simpa [Sat, Function.update_apply] using ht v
  refine ⟨t, fun v => ?_⟩
  rw [ht']
  constructor
  · rintro ⟨hv, hns⟩
    exact ⟨⟨v, hv⟩, rfl, fun hp => hns ((hs v).mpr ⟨⟨v, hv⟩, rfl, hp⟩)⟩
  · rintro ⟨n, hn, hnp⟩
    rw [← hn]
    refine ⟨n.2, fun hin => ?_⟩
    obtain ⟨m, hm, hpm⟩ := (hs _).mp hin
    have e : m = n := Subtype.ext hm
    rw [e] at hpm
    exact hnp hpm

theorem isPred_and {P Q : M.Num → Prop} (hP : M.IsPred P) (hQ : M.IsPred Q) :
    M.IsPred (fun n => P n ∧ Q n) := by
  obtain ⟨s, hs⟩ := hP
  obtain ⟨t, ht⟩ := hQ
  obtain ⟨u, -, hu⟩ := M.exists_inter s t
  refine ⟨u, fun v => ?_⟩
  rw [hu]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨n, hn, hp⟩ := (hs v).mp h1
    obtain ⟨m, hm, hq⟩ := (ht v).mp h2
    have e : m = n := Subtype.ext (hm.trans hn.symm)
    rw [e] at hq
    exact ⟨n, hn, hp, hq⟩
  · rintro ⟨n, hn, hp, hq⟩
    exact ⟨(hs v).mpr ⟨n, hn, hp⟩, (ht v).mpr ⟨n, hn, hq⟩⟩

theorem isPred_imp {P Q : M.Num → Prop} (hP : M.IsPred P) (hQ : M.IsPred Q) :
    M.IsPred (fun n => P n → Q n) :=
  M.isPred_congr (P := fun n => ¬ (P n ∧ ¬ Q n))
    (fun n => ⟨fun h hp => by_contra fun hq => h ⟨hp, hq⟩, fun h hpq => hpq.2 (h hpq.1)⟩)
    (M.isPred_not (M.isPred_and hP (M.isPred_not hQ)))

theorem isPred_eq {F G : M.Num → M.Num} (hF : M.NatFn F) (hG : M.NatFn G) :
    M.IsPred (fun n => F n = G n) := by
  obtain ⟨f, hf⟩ := hF
  obtain ⟨g, hg⟩ := hG
  obtain ⟨s, -, hs⟩ := M.comp (σW [(1, 5), (2, 5)])
    (Fml.ex 3 (.and (fApp 1 0 3) (fApp 2 0 3))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 f) 2 g)
  have hs' : ∀ v, M.mem v s ↔ ∃ u, M.mem (M.op v u) f ∧ M.mem (M.op v u) g := by
    intro v
    rw [hs v]
    simp [M.sat_ex, Sat, M.sat_fApp, Function.update_apply]
  refine ⟨s, fun v => ?_⟩
  rw [hs']
  constructor
  · rintro ⟨u, h1, h2⟩
    obtain ⟨n, hn, hu⟩ := (hf _ _).mp h1
    rw [← hn] at h2
    exact ⟨n, hn, Subtype.ext (hu.trans (M.graph_val hg h2))⟩
  · rintro ⟨n, hn, h⟩
    rw [← hn]
    refine ⟨(F n).1, M.graph_app hf n, ?_⟩
    rw [h]
    exact M.graph_app hg n

theorem natFn_id : M.NatFn (fun n => n) := by
  obtain ⟨s, -, hs⟩ := M.comp (σW [(0, 4), (1, 3)])
    (Fml.ex 3 (.and (.mem 3 1) (fPr 0 3 3))) 0 rfl (Function.update (fun _ => dflt) 1 M.nat)
  have hs' : ∀ p, M.mem p s ↔ ∃ a, M.mem a M.nat ∧ p = M.op a a := by
    intro p
    rw [hs p]
    simp [M.sat_ex, Sat, M.sat_fPr, Function.update_apply]
  refine ⟨s, fun a u => ?_⟩
  rw [hs']
  constructor
  · rintro ⟨a', ha', e⟩
    obtain ⟨h1, h2⟩ := M.op_inj e
    exact ⟨⟨a', ha'⟩, h1.symm, h2.symm⟩
  · rintro ⟨n, hn, hu⟩
    exact ⟨n.1, n.2, by rw [← hn, ← hu]⟩

theorem natFn_const (c : M.Num) : M.NatFn (fun _ => c) := by
  obtain ⟨s, -, hs⟩ := M.comp (σW [(0, 4), (1, 3)])
    (Fml.ex 3 (.and (.mem 3 1) (fPr 0 3 2))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 M.nat) 2 c.1)
  have hs' : ∀ p, M.mem p s ↔ ∃ a, M.mem a M.nat ∧ p = M.op a c.1 := by
    intro p
    rw [hs p]
    simp [M.sat_ex, Sat, M.sat_fPr, Function.update_apply]
  refine ⟨s, fun a u => ?_⟩
  rw [hs']
  constructor
  · rintro ⟨a', ha', e⟩
    obtain ⟨h1, h2⟩ := M.op_inj e
    exact ⟨⟨a', ha'⟩, h1.symm, h2.symm⟩
  · rintro ⟨n, hn, hu⟩
    exact ⟨n.1, n.2, by rw [← hn, ← hu]⟩

theorem natFn_succ : M.NatFn M.nsucc := by
  obtain ⟨s, -, hs⟩ := M.comp (σW [(0, 4), (1, 3)])
    (Fml.ex 3 (.and (.mem 3 1) (Fml.ex 4 (.and (fSuccEq 4 3) (fPr 0 3 4))))) 0 rfl
    (Function.update (fun _ => dflt) 1 M.nat)
  have hs' : ∀ p, M.mem p s ↔ ∃ a, M.mem a M.nat ∧ ∃ b, b = M.succ a ∧ p = M.op a b := by
    intro p
    rw [hs p]
    simp [M.sat_ex, Sat, M.sat_fPr, M.sat_fSuccEq, Function.update_apply]
  refine ⟨s, fun a u => ?_⟩
  rw [hs']
  constructor
  · rintro ⟨a', ha', b, hb, e⟩
    obtain ⟨h1, h2⟩ := M.op_inj e
    exact ⟨⟨a', ha'⟩, h1.symm, by rw [h2, hb]; rfl⟩
  · rintro ⟨n, hn, hu⟩
    exact ⟨n.1, n.2, M.succ n.1, rfl, by rw [← hn, ← hu]; rfl⟩

theorem natFn_comp {K F : M.Num → M.Num} (hK : M.NatFn K) (hF : M.NatFn F) :
    M.NatFn (fun n => K (F n)) := by
  obtain ⟨k, hk⟩ := hK
  obtain ⟨f, hf⟩ := hF
  obtain ⟨s, -, hs⟩ := M.comp (σW [(0, 4), (1, 5), (2, 5)])
    (Fml.ex 3 (Fml.ex 4 (Fml.ex 5 (.and (fApp 1 3 4) (.and (fApp 2 4 5) (fPr 0 3 5)))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 f) 2 k)
  have hs' : ∀ p, M.mem p s ↔
      ∃ a u w, M.mem (M.op a u) f ∧ M.mem (M.op u w) k ∧ p = M.op a w := by
    intro p
    rw [hs p]
    simp [M.sat_ex, Sat, M.sat_fPr, M.sat_fApp, Function.update_apply]
  refine ⟨s, fun a w => ?_⟩
  rw [hs']
  constructor
  · rintro ⟨a', u, w', h1, h2, e⟩
    obtain ⟨e1, e2⟩ := M.op_inj e
    obtain ⟨n, hn, hu⟩ := (hf _ _).mp h1
    rw [← hu] at h2
    exact ⟨n, hn.trans e1.symm, (M.graph_val hk h2).symm.trans e2.symm⟩
  · rintro ⟨n, hn, hw⟩
    exact ⟨n.1, (F n).1, (K (F n)).1, M.graph_app hf n, M.graph_app hk (F n), by rw [← hn, ← hw]⟩

theorem natFn_op₂ {H : M.Num → M.Num → M.Num} {F G : M.Num → M.Num} (hH : M.NatOp H)
    (hF : M.NatFn F) (hG : M.NatFn G) : M.NatFn (fun n => H (F n) (G n)) := by
  obtain ⟨hh, hhh⟩ := hH
  obtain ⟨f, hf⟩ := hF
  obtain ⟨g, hg⟩ := hG
  obtain ⟨s, -, hs⟩ := M.comp (σW [(0, 4), (1, 5), (2, 5), (7, 7)])
    (Fml.ex 3 (Fml.ex 4 (Fml.ex 5 (Fml.ex 6 (.and (fApp 1 3 4) (.and (fApp 2 3 5)
      (.and (fApp3 7 4 5 6) (fPr 0 3 6)))))))) 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 1 f) 2 g) 7 hh)
  have hs' : ∀ p, M.mem p s ↔ ∃ a u v w, M.mem (M.op a u) f ∧ M.mem (M.op a v) g ∧
      M.mem (M.trip u v w) hh ∧ p = M.op a w := by
    intro p
    rw [hs p]
    simp [M.sat_ex, Sat, M.sat_fPr, M.sat_fApp, M.sat_fApp3, Function.update_apply]
  refine ⟨s, fun a w => ?_⟩
  rw [hs']
  constructor
  · rintro ⟨a', u, v, w', h1, h2, h3, e⟩
    obtain ⟨e1, e2⟩ := M.op_inj e
    obtain ⟨n, hn, hu⟩ := (hf _ _).mp h1
    rw [← hn] at h2
    have hv := M.graph_val hg h2
    rw [← hu, hv] at h3
    exact ⟨n, hn.trans e1.symm, (M.graph₂_val hhh h3).symm.trans e2.symm⟩
  · rintro ⟨n, hn, hw⟩
    exact ⟨n.1, (F n).1, (G n).1, (H (F n) (G n)).1, M.graph_app hf n, M.graph_app hg n,
      M.graph₂_app hhh (F n) (G n), by rw [← hn, ← hw]⟩

theorem natOp_of_fn {K : M.Num → M.Num} (hK : M.NatFn K) : M.NatOp (fun _ u => K u) := by
  obtain ⟨k, hk⟩ := hK
  obtain ⟨s, -, hs⟩ := M.comp (σW [(0, 6), (1, 3), (2, 5)])
    (Fml.ex 3 (Fml.ex 4 (Fml.ex 5 (.and (.mem 3 1) (.and (fApp 2 4 5) (fTrip 0 3 4 5)))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 M.nat) 2 k)
  have hs' : ∀ q, M.mem q s ↔
      ∃ a u w, M.mem a M.nat ∧ M.mem (M.op u w) k ∧ q = M.trip a u w := by
    intro q
    rw [hs q]
    simp [M.sat_ex, Sat, M.sat_fTrip, M.sat_fApp, Function.update_apply]
  refine ⟨s, fun a b c => ?_⟩
  rw [hs']
  constructor
  · rintro ⟨a', u, w, ha', h2, e⟩
    obtain ⟨e1, e2, e3⟩ := M.trip_inj e
    obtain ⟨n, hn, hw⟩ := (hk _ _).mp h2
    exact ⟨⟨a', ha'⟩, n, e1.symm, hn.trans e2.symm, hw.trans e3.symm⟩
  · rintro ⟨m, n, hm, hn, hc⟩
    exact ⟨m.1, n.1, (K n).1, m.2, M.graph_app hk n, by rw [← hm, ← hn, ← hc]⟩

theorem natOp_swap {H : M.Num → M.Num → M.Num} (hH : M.NatOp H) :
    M.NatOp (fun a u => H u a) := by
  obtain ⟨hh, hhh⟩ := hH
  obtain ⟨s, -, hs⟩ := M.comp (σW [(0, 6), (1, 7)])
    (Fml.ex 3 (Fml.ex 4 (Fml.ex 5 (.and (fApp3 1 4 3 5) (fTrip 0 3 4 5))))) 0 rfl
    (Function.update (fun _ => dflt) 1 hh)
  have hs' : ∀ q, M.mem q s ↔ ∃ a u w, M.mem (M.trip u a w) hh ∧ q = M.trip a u w := by
    intro q
    rw [hs q]
    simp [M.sat_ex, Sat, M.sat_fTrip, M.sat_fApp3, Function.update_apply]
  refine ⟨s, fun a b c => ?_⟩
  rw [hs']
  constructor
  · rintro ⟨a', u, w, h1, e⟩
    obtain ⟨e1, e2, e3⟩ := M.trip_inj e
    obtain ⟨m, n, hm, hn, hw⟩ := (hhh _ _ _).mp h1
    exact ⟨n, m, hn.trans e1.symm, hm.trans e2.symm, hw.trans e3.symm⟩
  · rintro ⟨m, n, hm, hn, hc⟩
    exact ⟨m.1, n.1, (H n m).1, M.graph₂_app hhh n m, by rw [← hm, ← hn, ← hc]⟩

/-! ## Recursion on the natural numbers

Given set functions `h : ℕ → ℕ` and `g : ℕ × ℕ → ℕ`, there is a set function `F : ℕ × ℕ → ℕ`
with `F a 0 = h a` and `F a (b + 1) = g a (F a b)`. The graph of `F` is the intersection of
all sets of triples closed under the two clauses. -/

/-- `r` is closed under the two clauses of the recursion with base graph `hG` and step
graph `gG`. -/
def Closed (hG gG r : V) : Prop :=
  (∀ a u, M.mem (M.op a u) hG → M.mem (M.trip a M.zero u) r) ∧
  (∀ a b c v s, (M.mem b M.nat ∧ M.mem (M.trip a b c) r ∧ M.mem (M.trip a c v) gG ∧
    s = M.succ b) → M.mem (M.trip a s v) r)

def recFml : Fml :=
  .all 5 (Fml.imp
    (.and
      (.all 6 (.all 11 (Fml.imp (fApp 1 6 11) (fApp3 5 6 3 11))))
      (.all 6 (.all 7 (.all 8 (.all 9 (.all 10 (Fml.imp
        (.and (.mem 7 4) (.and (fApp3 5 6 7 8) (.and (fApp3 2 6 8 9) (fSuccEq 10 7))))
        (fApp3 5 6 10 9))))))))
    (.mem 0 5))

theorem exists_recSet (hG gG : V) :
    ∃ A, ∀ q, M.mem q A ↔ ∀ r, M.Closed hG gG r → M.mem q r := by
  obtain ⟨A, -, hA⟩ := M.comp (σW [(0, 6), (1, 5), (2, 7), (4, 3), (5, 7)]) recFml 0 rfl
    (Function.update (Function.update (Function.update (Function.update (fun _ => dflt)
      1 hG) 2 gG) 3 M.zero) 4 M.nat)
  refine ⟨A, fun q => ?_⟩
  rw [hA q]
  simp [recFml, Closed, Sat, M.sat_imp, M.sat_fApp, M.sat_fApp3, M.sat_fSuccEq,
    Function.update_apply]

theorem closed_recSet {hG gG A : V}
    (hA : ∀ q, M.mem q A ↔ ∀ r, M.Closed hG gG r → M.mem q r) : M.Closed hG gG A := by
  constructor
  · intro a u h
    exact (hA _).mpr fun r hr => hr.1 a u h
  · rintro a b c v s ⟨hb, h1, h2, hs⟩
    exact (hA _).mpr fun r hr => hr.2 a b c v s ⟨hb, (hA _).mp h1 r hr, h2, hs⟩

def totFml : Fml := .all 6 (Fml.imp (.mem 6 4) (Fml.ex 8 (.and (.mem 8 4) (fApp3 5 6 0 8))))

theorem sat_totFml (A b : V) :
    Sat M.mem M.isSet totFml (Function.update (Function.update (Function.update (fun _ => dflt)
      4 M.nat) 5 A) 0 b) ↔
    ∀ a, M.mem a M.nat → ∃ c, M.mem c M.nat ∧ M.mem (M.trip a b c) A := by
  simp [totFml, Sat, M.sat_imp, M.sat_ex, M.sat_fApp3, Function.update_apply]

/-- Every triple of the recursion set arises from one of the two clauses. -/
def Inv (hG gG A q : V) : Prop :=
  M.mem q A ∧ ∃ a b c, q = M.trip a b c ∧ M.mem a M.nat ∧ M.mem b M.nat ∧ M.mem c M.nat ∧
    (b = M.zero → M.mem (M.op a c) hG) ∧
    ∀ b', (M.mem b' M.nat ∧ b = M.succ b') →
      ∃ u, M.mem (M.trip a b' u) A ∧ M.mem (M.trip a u c) gG

def invFml : Fml :=
  .and (.mem 0 5) (Fml.ex 6 (Fml.ex 7 (Fml.ex 8 (.and (fTrip 0 6 7 8) (.and (.mem 6 4)
    (.and (.mem 7 4) (.and (.mem 8 4) (.and (Fml.imp (.eq 7 3) (fApp 1 6 8))
      (.all 12 (Fml.imp (.and (.mem 12 4) (fSuccEq 7 12))
        (Fml.ex 11 (.and (fApp3 5 6 12 11) (fApp3 2 6 11 8)))))))))))))

def uniqFml : Fml :=
  .all 6 (.all 8 (.all 9 (Fml.imp (fApp3 5 6 0 8) (Fml.imp (fApp3 5 6 0 9) (.eq 8 9)))))

theorem sat_uniqFml (A b : V) :
    Sat M.mem M.isSet uniqFml (Function.update (Function.update (fun _ => dflt) 5 A) 0 b) ↔
    ∀ a c c', M.mem (M.trip a b c) A → M.mem (M.trip a b c') A → c = c' := by
  simp [uniqFml, Sat, M.sat_imp, M.sat_fApp3, Function.update_apply]

/-- **The recursion theorem**, with a parameter. -/
theorem exists_prec {h : M.Num → M.Num} {g : M.Num → M.Num → M.Num} (hh : M.NatFn h)
    (hg : M.NatOp g) :
    ∃ F : M.Num → M.Num → M.Num, M.NatOp F ∧ (∀ a, F a M.nzero = h a) ∧
      ∀ a b, F a (M.nsucc b) = g a (F a b) := by
  obtain ⟨hG, hhG⟩ := hh
  obtain ⟨gG, hgG⟩ := hg
  obtain ⟨A, hA⟩ := M.exists_recSet hG gG
  have hcl := M.closed_recSet hA
  have cl1 : ∀ a : M.Num, M.mem (M.trip a.1 M.zero (h a).1) A := fun a =>
    hcl.1 _ _ (M.graph_app hhG a)
  have cl2 : ∀ a b c : M.Num, M.mem (M.trip a.1 b.1 c.1) A →
      M.mem (M.trip a.1 (M.succ b.1) (g a c).1) A := fun a b c hc =>
    hcl.2 _ _ _ _ _ ⟨b.2, hc, M.graph₂_app hgG a c, rfl⟩
  -- totality
  have tot : ∀ b a : M.Num, ∃ c : M.Num, M.mem (M.trip a.1 b.1 c.1) A := by
    intro b
    have h0 : Sat M.mem M.isSet totFml (Function.update (Function.update (Function.update
        (fun _ => dflt) 4 M.nat) 5 A) 0 M.zero) := by
      rw [M.sat_totFml]
      intro a ha
      exact ⟨(h ⟨a, ha⟩).1, (h ⟨a, ha⟩).2, cl1 ⟨a, ha⟩⟩
    have hs : ∀ k : M.Num, Sat M.mem M.isSet totFml (Function.update (Function.update
        (Function.update (fun _ => dflt) 4 M.nat) 5 A) 0 k.1) →
        Sat M.mem M.isSet totFml (Function.update (Function.update (Function.update
        (fun _ => dflt) 4 M.nat) 5 A) 0 (M.succ k.1)) := by
      intro k ih
      rw [M.sat_totFml] at ih ⊢
      intro a ha
      obtain ⟨c, hc, hc'⟩ := ih a ha
      exact ⟨(g ⟨a, ha⟩ ⟨c, hc⟩).1, (g ⟨a, ha⟩ ⟨c, hc⟩).2, cl2 ⟨a, ha⟩ k ⟨c, hc⟩ hc'⟩
    have key := M.num_ind_fml (σW [(4, 3), (5, 7)]) totFml 0 rfl _ h0 hs b
    rw [M.sat_totFml] at key
    intro a
    obtain ⟨c, hc, hc'⟩ := key a.1 a.2
    exact ⟨⟨c, hc⟩, hc'⟩
  -- inversion
  obtain ⟨B, -, hB⟩ := M.comp (σW [(0, 6), (1, 5), (2, 7), (4, 3), (5, 7)]) invFml 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 hG) 2 gG) 3 M.zero) 4 M.nat) 5 A)
  have hB' : ∀ q, M.mem q B ↔ M.Inv hG gG A q := by
    intro q
    rw [hB q]
    simp [invFml, Inv, Sat, M.sat_imp, M.sat_ex, M.sat_fTrip, M.sat_fApp, M.sat_fApp3,
      M.sat_fSuccEq, Function.update_apply]
  have hBcl : M.Closed hG gG B := by
    constructor
    · intro a u hau
      obtain ⟨n, hn, hu⟩ := (hhG _ _).mp hau
      refine (hB' _).mpr ⟨hcl.1 a u hau, a, M.zero, u, rfl, ?_, M.zero_mem_nat, ?_,
        fun _ => hau, ?_⟩
      · rw [← hn]
        exact n.2
      · rw [← hu]
        exact (h n).2
      · rintro b' ⟨-, hb'⟩
        exact absurd hb' (M.zero_ne_succ b')
    · rintro a b c v s ⟨hb, h1, h2, hs⟩
      obtain ⟨h1A, a0, b0, c0, e, ha0, hb0, hc0, -, -⟩ := (hB' _).mp h1
      obtain ⟨e1, e2, e3⟩ := M.trip_inj e
      obtain ⟨m, n, hm, hn, hv⟩ := (hgG _ _ _).mp h2
      refine (hB' _).mpr ⟨hcl.2 a b c v s ⟨hb, h1A, h2, hs⟩, a, s, v, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e1]
        exact ha0
      · rw [hs]
        exact M.succ_mem_nat hb
      · rw [← hv]
        exact (g m n).2
      · intro hs0
        rw [hs] at hs0
        exact absurd hs0.symm (M.zero_ne_succ b)
      · rintro b' ⟨hb', hsb'⟩
        rw [hs] at hsb'
        have ebb : b = b' := M.succ_inj hb hb' hsb'
        rw [← ebb]
        exact ⟨c, h1A, h2⟩
  have inv : ∀ q, M.mem q A → M.Inv hG gG A q := fun q hq =>
    (hB' q).mp ((hA q).mp hq B hBcl)
  -- uniqueness
  have uniq : ∀ (b : M.Num) (a c c' : V), M.mem (M.trip a b.1 c) A →
      M.mem (M.trip a b.1 c') A → c = c' := by
    intro b
    have h0 : Sat M.mem M.isSet uniqFml
        (Function.update (Function.update (fun _ => dflt) 5 A) 0 M.zero) := by
      rw [M.sat_uniqFml]
      intro a c c' h1 h2
      obtain ⟨-, x1, y1, z1, e, -, -, -, hz, -⟩ := inv _ h1
      obtain ⟨-, x2, y2, z2, e', -, -, -, hz', -⟩ := inv _ h2
      obtain ⟨ea, eb, ec⟩ := M.trip_inj e
      obtain ⟨ea', eb', ec'⟩ := M.trip_inj e'
      have g1 := hz eb.symm
      have g2 := hz' eb'.symm
      rw [← ea, ← ec] at g1
      rw [← ea', ← ec'] at g2
      obtain ⟨n, hn, hu⟩ := (hhG _ _).mp g1
      obtain ⟨n', hn', hu'⟩ := (hhG _ _).mp g2
      have enn : n = n' := Subtype.ext (hn.trans hn'.symm)
      rw [← hu, ← hu', enn]
    have hs : ∀ k : M.Num, Sat M.mem M.isSet uniqFml
        (Function.update (Function.update (fun _ => dflt) 5 A) 0 k.1) →
        Sat M.mem M.isSet uniqFml
        (Function.update (Function.update (fun _ => dflt) 5 A) 0 (M.succ k.1)) := by
      intro k ih
      rw [M.sat_uniqFml] at ih ⊢
      intro a c c' h1 h2
      obtain ⟨-, x1, y1, z1, e, -, -, -, -, hstep⟩ := inv _ h1
      obtain ⟨-, x2, y2, z2, e', -, -, -, -, hstep'⟩ := inv _ h2
      obtain ⟨ea, eb, ec⟩ := M.trip_inj e
      obtain ⟨ea', eb', ec'⟩ := M.trip_inj e'
      obtain ⟨u, hu1, hu2⟩ := hstep k.1 ⟨k.2, eb.symm⟩
      obtain ⟨u', hu1', hu2'⟩ := hstep' k.1 ⟨k.2, eb'.symm⟩
      rw [← ea] at hu1 hu2
      rw [← ea'] at hu1' hu2'
      rw [← ec] at hu2
      rw [← ec'] at hu2'
      have euu : u = u' := ih a u u' hu1 hu1'
      rw [← euu] at hu2'
      obtain ⟨m, n, hm, hn, hv⟩ := (hgG _ _ _).mp hu2
      obtain ⟨m', n', hm', hn', hv'⟩ := (hgG _ _ _).mp hu2'
      have em : m = m' := Subtype.ext (hm.trans hm'.symm)
      have en : n = n' := Subtype.ext (hn.trans hn'.symm)
      rw [← hv, ← hv', em, en]
    have key := M.num_ind_fml (σW [(5, 7)]) uniqFml 0 rfl _ h0 hs b
    rw [M.sat_uniqFml] at key
    exact key
  choose F hF using fun (a b : M.Num) => tot b a
  have hgraph : M.IsGraphOf₂ A F := by
    intro a b c
    constructor
    · intro hq
      obtain ⟨-, x1, y1, z1, e, hx, hy, hz, -, -⟩ := inv _ hq
      obtain ⟨ea, eb, ec⟩ := M.trip_inj e
      rw [← ea] at hx
      rw [← eb] at hy
      exact ⟨⟨a, hx⟩, ⟨b, hy⟩, rfl, rfl, uniq ⟨b, hy⟩ a _ _ (hF ⟨a, hx⟩ ⟨b, hy⟩) hq⟩
    · rintro ⟨m, n, hm, hn, hc⟩
      rw [← hm, ← hn, ← hc]
      exact hF m n
  refine ⟨F, ⟨A, hgraph⟩, fun a => ?_, fun a b => ?_⟩
  · exact Subtype.ext (uniq M.nzero a.1 _ _ (hF a M.nzero) (cl1 a))
  · exact Subtype.ext (uniq (M.nsucc b) a.1 _ _ (hF a (M.nsucc b)) (cl2 a b (F a b) (hF a b)))

/-! ## Addition, multiplication, exponentiation and the tower -/

theorem exists_addN : ∃ F : M.Num → M.Num → M.Num, M.NatOp F ∧ (∀ a, F a M.nzero = a) ∧
    ∀ a b, F a (M.nsucc b) = M.nsucc (F a b) :=
  M.exists_prec M.natFn_id (M.natOp_of_fn M.natFn_succ)

/-- Addition: `a + 0 = a`, `a + (b + 1) = (a + b) + 1`. -/
noncomputable def addN : M.Num → M.Num → M.Num := Classical.choose M.exists_addN

theorem addN_natOp : M.NatOp M.addN := (Classical.choose_spec M.exists_addN).1

theorem addN_zero (a : M.Num) : M.addN a M.nzero = a :=
  (Classical.choose_spec M.exists_addN).2.1 a

theorem addN_succ (a b : M.Num) : M.addN a (M.nsucc b) = M.nsucc (M.addN a b) :=
  (Classical.choose_spec M.exists_addN).2.2 a b

theorem exists_mulN : ∃ F : M.Num → M.Num → M.Num, M.NatOp F ∧ (∀ a, F a M.nzero = M.nzero) ∧
    ∀ a b, F a (M.nsucc b) = M.addN (F a b) a :=
  M.exists_prec (M.natFn_const M.nzero) (M.natOp_swap M.addN_natOp)

/-- Multiplication: `a · 0 = 0`, `a · (b + 1) = a · b + a`. -/
noncomputable def mulN : M.Num → M.Num → M.Num := Classical.choose M.exists_mulN

theorem mulN_natOp : M.NatOp M.mulN := (Classical.choose_spec M.exists_mulN).1

theorem mulN_zero (a : M.Num) : M.mulN a M.nzero = M.nzero :=
  (Classical.choose_spec M.exists_mulN).2.1 a

theorem mulN_succ (a b : M.Num) : M.mulN a (M.nsucc b) = M.addN (M.mulN a b) a :=
  (Classical.choose_spec M.exists_mulN).2.2 a b

/-- One. -/
noncomputable def none : M.Num := M.nsucc M.nzero

/-- Two. -/
noncomputable def ntwo : M.Num := M.nsucc (M.nsucc M.nzero)

theorem fnAdd {F G : M.Num → M.Num} (hF : M.NatFn F) (hG : M.NatFn G) :
    M.NatFn (fun n => M.addN (F n) (G n)) := M.natFn_op₂ M.addN_natOp hF hG

theorem fnMul {F G : M.Num → M.Num} (hF : M.NatFn F) (hG : M.NatFn G) :
    M.NatFn (fun n => M.mulN (F n) (G n)) := M.natFn_op₂ M.mulN_natOp hF hG

theorem fnSucc {F : M.Num → M.Num} (hF : M.NatFn F) : M.NatFn (fun n => M.nsucc (F n)) :=
  M.natFn_comp M.natFn_succ hF

theorem exists_expN : ∃ F : M.Num → M.Num → M.Num, M.NatOp F ∧ (∀ a, F a M.nzero = M.none) ∧
    ∀ a b, F a (M.nsucc b) = M.addN (F a b) (F a b) :=
  M.exists_prec (M.natFn_const M.none) (M.natOp_of_fn (M.fnAdd M.natFn_id M.natFn_id))

/-- Exponentiation with base two: `2⁰ = 1`, `2^(b+1) = 2^b + 2^b`. -/
noncomputable def expN (b : M.Num) : M.Num := Classical.choose M.exists_expN M.nzero b

theorem expN_zero : M.expN M.nzero = M.none :=
  (Classical.choose_spec M.exists_expN).2.1 M.nzero

theorem expN_succ (b : M.Num) : M.expN (M.nsucc b) = M.addN (M.expN b) (M.expN b) :=
  (Classical.choose_spec M.exists_expN).2.2 M.nzero b

theorem natFn_expN : M.NatFn M.expN :=
  M.natFn_op₂ (Classical.choose_spec M.exists_expN).1 (M.natFn_const M.nzero) M.natFn_id

theorem exists_towN : ∃ F : M.Num → M.Num → M.Num, M.NatOp F ∧ (∀ a, F a M.nzero = M.ntwo) ∧
    ∀ a b, F a (M.nsucc b) = M.expN (F a b) :=
  M.exists_prec (M.natFn_const M.ntwo) (M.natOp_of_fn M.natFn_expN)

/-- The tower: `t(0) = 2`, `t(b+1) = 2^{t(b)}`. -/
noncomputable def towN (b : M.Num) : M.Num := Classical.choose M.exists_towN M.nzero b

theorem towN_zero : M.towN M.nzero = M.ntwo :=
  (Classical.choose_spec M.exists_towN).2.1 M.nzero

theorem towN_succ (b : M.Num) : M.towN (M.nsucc b) = M.expN (M.towN b) :=
  (Classical.choose_spec M.exists_towN).2.2 M.nzero b

theorem natFn_towN : M.NatFn M.towN :=
  M.natFn_op₂ (Classical.choose_spec M.exists_towN).1 (M.natFn_const M.nzero) M.natFn_id

/-! ### The semiring laws -/

theorem zero_addN (b : M.Num) : M.addN M.nzero b = b := by
  refine M.num_ind (P := fun b => M.addN M.nzero b = b)
    (M.isPred_eq (M.fnAdd (M.natFn_const _) M.natFn_id) M.natFn_id) ?_ ?_ b
  · exact M.addN_zero _
  · intro k (ih : M.addN M.nzero k = k)
    show M.addN M.nzero (M.nsucc k) = M.nsucc k
    rw [M.addN_succ, ih]

theorem succ_addN (a b : M.Num) : M.addN (M.nsucc a) b = M.nsucc (M.addN a b) := by
  refine M.num_ind (P := fun b => M.addN (M.nsucc a) b = M.nsucc (M.addN a b))
    (M.isPred_eq (M.fnAdd (M.natFn_const _) M.natFn_id)
      (M.fnSucc (M.fnAdd (M.natFn_const _) M.natFn_id))) ?_ ?_ b
  · show M.addN (M.nsucc a) M.nzero = M.nsucc (M.addN a M.nzero)
    rw [M.addN_zero, M.addN_zero]
  · intro k (ih : M.addN (M.nsucc a) k = M.nsucc (M.addN a k))
    show M.addN (M.nsucc a) (M.nsucc k) = M.nsucc (M.addN a (M.nsucc k))
    rw [M.addN_succ, M.addN_succ, ih]

theorem addN_comm (a b : M.Num) : M.addN a b = M.addN b a := by
  refine M.num_ind (P := fun b => M.addN a b = M.addN b a)
    (M.isPred_eq (M.fnAdd (M.natFn_const _) M.natFn_id)
      (M.fnAdd M.natFn_id (M.natFn_const _))) ?_ ?_ b
  · show M.addN a M.nzero = M.addN M.nzero a
    rw [M.addN_zero, M.zero_addN]
  · intro k (ih : M.addN a k = M.addN k a)
    show M.addN a (M.nsucc k) = M.addN (M.nsucc k) a
    rw [M.addN_succ, M.succ_addN, ih]

theorem addN_assoc (a b c : M.Num) : M.addN (M.addN a b) c = M.addN a (M.addN b c) := by
  refine M.num_ind (P := fun c => M.addN (M.addN a b) c = M.addN a (M.addN b c))
    (M.isPred_eq (M.fnAdd (M.natFn_const _) M.natFn_id)
      (M.fnAdd (M.natFn_const _) (M.fnAdd (M.natFn_const _) M.natFn_id))) ?_ ?_ c
  · show M.addN (M.addN a b) M.nzero = M.addN a (M.addN b M.nzero)
    rw [M.addN_zero, M.addN_zero]
  · intro k (ih : M.addN (M.addN a b) k = M.addN a (M.addN b k))
    show M.addN (M.addN a b) (M.nsucc k) = M.addN a (M.addN b (M.nsucc k))
    rw [M.addN_succ, M.addN_succ, M.addN_succ, ih]

theorem zero_mulN (b : M.Num) : M.mulN M.nzero b = M.nzero := by
  refine M.num_ind (P := fun b => M.mulN M.nzero b = M.nzero)
    (M.isPred_eq (M.fnMul (M.natFn_const _) M.natFn_id) (M.natFn_const _)) ?_ ?_ b
  · exact M.mulN_zero _
  · intro k (ih : M.mulN M.nzero k = M.nzero)
    show M.mulN M.nzero (M.nsucc k) = M.nzero
    rw [M.mulN_succ, M.addN_zero, ih]

theorem succ_mulN (a b : M.Num) : M.mulN (M.nsucc a) b = M.addN (M.mulN a b) b := by
  refine M.num_ind (P := fun b => M.mulN (M.nsucc a) b = M.addN (M.mulN a b) b)
    (M.isPred_eq (M.fnMul (M.natFn_const _) M.natFn_id)
      (M.fnAdd (M.fnMul (M.natFn_const _) M.natFn_id) M.natFn_id)) ?_ ?_ b
  · show M.mulN (M.nsucc a) M.nzero = M.addN (M.mulN a M.nzero) M.nzero
    rw [M.mulN_zero, M.mulN_zero, M.addN_zero]
  · intro k (ih : M.mulN (M.nsucc a) k = M.addN (M.mulN a k) k)
    show M.mulN (M.nsucc a) (M.nsucc k) = M.addN (M.mulN a (M.nsucc k)) (M.nsucc k)
    calc M.mulN (M.nsucc a) (M.nsucc k)
        = M.addN (M.mulN (M.nsucc a) k) (M.nsucc a) := M.mulN_succ _ _
      _ = M.addN (M.addN (M.mulN a k) k) (M.nsucc a) := by rw [ih]
      _ = M.nsucc (M.addN (M.addN (M.mulN a k) k) a) := M.addN_succ _ _
      _ = M.nsucc (M.addN (M.addN (M.mulN a k) a) k) := by
          rw [M.addN_assoc (M.mulN a k) k a, M.addN_comm k a, ← M.addN_assoc]
      _ = M.addN (M.addN (M.mulN a k) a) (M.nsucc k) := (M.addN_succ _ _).symm
      _ = M.addN (M.mulN a (M.nsucc k)) (M.nsucc k) := by rw [M.mulN_succ a k]

theorem mulN_comm (a b : M.Num) : M.mulN a b = M.mulN b a := by
  refine M.num_ind (P := fun b => M.mulN a b = M.mulN b a)
    (M.isPred_eq (M.fnMul (M.natFn_const _) M.natFn_id)
      (M.fnMul M.natFn_id (M.natFn_const _))) ?_ ?_ b
  · show M.mulN a M.nzero = M.mulN M.nzero a
    rw [M.mulN_zero, M.zero_mulN]
  · intro k (ih : M.mulN a k = M.mulN k a)
    show M.mulN a (M.nsucc k) = M.mulN (M.nsucc k) a
    rw [M.mulN_succ, M.succ_mulN, ih]

theorem mulN_addN (a b c : M.Num) :
    M.mulN a (M.addN b c) = M.addN (M.mulN a b) (M.mulN a c) := by
  refine M.num_ind (P := fun c => M.mulN a (M.addN b c) = M.addN (M.mulN a b) (M.mulN a c))
    (M.isPred_eq (M.fnMul (M.natFn_const _) (M.fnAdd (M.natFn_const _) M.natFn_id))
      (M.fnAdd (M.natFn_const _) (M.fnMul (M.natFn_const _) M.natFn_id))) ?_ ?_ c
  · show M.mulN a (M.addN b M.nzero) = M.addN (M.mulN a b) (M.mulN a M.nzero)
    rw [M.addN_zero, M.mulN_zero, M.addN_zero]
  · intro k (ih : M.mulN a (M.addN b k) = M.addN (M.mulN a b) (M.mulN a k))
    show M.mulN a (M.addN b (M.nsucc k)) = M.addN (M.mulN a b) (M.mulN a (M.nsucc k))
    rw [M.addN_succ, M.mulN_succ a (M.addN b k), ih, M.mulN_succ a k, M.addN_assoc]

theorem mulN_assoc (a b c : M.Num) : M.mulN (M.mulN a b) c = M.mulN a (M.mulN b c) := by
  refine M.num_ind (P := fun c => M.mulN (M.mulN a b) c = M.mulN a (M.mulN b c))
    (M.isPred_eq (M.fnMul (M.natFn_const _) M.natFn_id)
      (M.fnMul (M.natFn_const _) (M.fnMul (M.natFn_const _) M.natFn_id))) ?_ ?_ c
  · show M.mulN (M.mulN a b) M.nzero = M.mulN a (M.mulN b M.nzero)
    rw [M.mulN_zero (M.mulN a b), M.mulN_zero b, M.mulN_zero a]
  · intro k (ih : M.mulN (M.mulN a b) k = M.mulN a (M.mulN b k))
    show M.mulN (M.mulN a b) (M.nsucc k) = M.mulN a (M.mulN b (M.nsucc k))
    rw [M.mulN_succ (M.mulN a b) k, ih, M.mulN_succ b k, M.mulN_addN]

theorem mulN_one (a : M.Num) : M.mulN a M.none = a := by
  show M.mulN a (M.nsucc M.nzero) = a
  rw [M.mulN_succ, M.mulN_zero, M.zero_addN]

theorem nsucc_eq (a : M.Num) : M.nsucc a = M.addN a M.none := by
  show M.nsucc a = M.addN a (M.nsucc M.nzero)
  rw [M.addN_succ, M.addN_zero]

/-! ### The order -/

/-- `a ≤ b` if `a + c = b` for some `c`. -/
def leN (a b : M.Num) : Prop := ∃ c, M.addN a c = b

theorem isPred_le {F G : M.Num → M.Num} (hF : M.NatFn F) (hG : M.NatFn G) :
    M.IsPred (fun n => M.leN (F n) (G n)) := by
  obtain ⟨f, hf⟩ := hF
  obtain ⟨g, hg⟩ := hG
  obtain ⟨ad, had⟩ := M.addN_natOp
  obtain ⟨s, -, hs⟩ := M.comp (σW [(1, 5), (2, 5), (7, 7)])
    (Fml.ex 3 (Fml.ex 4 (Fml.ex 5 (.and (fApp 1 0 3) (.and (fApp 2 0 4) (fApp3 7 3 5 4)))))) 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 1 f) 2 g) 7 ad)
  have hs' : ∀ a, M.mem a s ↔ ∃ u v c, M.mem (M.op a u) f ∧ M.mem (M.op a v) g ∧
      M.mem (M.trip u c v) ad := by
    intro a
    rw [hs a]
    simp [M.sat_ex, Sat, M.sat_fApp, M.sat_fApp3, Function.update_apply]
  refine ⟨s, fun a => ?_⟩
  rw [hs']
  constructor
  · rintro ⟨u, v, c, h1, h2, h3⟩
    obtain ⟨n, hn, hu⟩ := (hf _ _).mp h1
    rw [← hn] at h2
    have hv := M.graph_val hg h2
    obtain ⟨m, k, hm, hk, hmk⟩ := (had _ _ _).mp h3
    have em : m = F n := Subtype.ext (hm.trans hu.symm)
    rw [em] at hmk
    exact ⟨n, hn, k, Subtype.ext (hmk.trans hv)⟩
  · rintro ⟨n, hn, c, hc⟩
    rw [← hn]
    refine ⟨(F n).1, (G n).1, c.1, M.graph_app hf n, M.graph_app hg n, ?_⟩
    rw [← hc]
    exact M.graph₂_app had (F n) c

theorem addN_left_cancel {a x y : M.Num} (h : M.addN a x = M.addN a y) : x = y := by
  refine M.num_ind (P := fun a => M.addN a x = M.addN a y → x = y)
    (M.isPred_imp (M.isPred_eq (M.fnAdd M.natFn_id (M.natFn_const _))
      (M.fnAdd M.natFn_id (M.natFn_const _))) (M.isPred_const _)) ?_ ?_ a h
  · intro (h0 : M.addN M.nzero x = M.addN M.nzero y)
    rwa [M.zero_addN, M.zero_addN] at h0
  · intro k (ih : M.addN k x = M.addN k y → x = y) (hk : M.addN (M.nsucc k) x = M.addN (M.nsucc k) y)
    rw [M.succ_addN, M.succ_addN] at hk
    exact ih (M.nsucc_inj hk)

theorem addN_eq_zero {c d : M.Num} (h : M.addN c d = M.nzero) : d = M.nzero := by
  rcases M.num_cases d with hd | ⟨k, hd⟩
  · exact hd
  · rw [hd, M.addN_succ] at h
    exact absurd h.symm (M.nzero_ne_nsucc _)

theorem leN_refl (a : M.Num) : M.leN a a := ⟨M.nzero, M.addN_zero a⟩

theorem leN_trans {a b c : M.Num} (h1 : M.leN a b) (h2 : M.leN b c) : M.leN a c := by
  obtain ⟨d, hd⟩ := h1
  obtain ⟨e, he⟩ := h2
  exact ⟨M.addN d e, by rw [← M.addN_assoc, hd, he]⟩

theorem leN_antisymm {a b : M.Num} (h1 : M.leN a b) (h2 : M.leN b a) : a = b := by
  obtain ⟨d, hd⟩ := h1
  obtain ⟨e, he⟩ := h2
  have h3 : M.addN a (M.addN d e) = M.addN a M.nzero := by
    rw [← M.addN_assoc, hd, he, M.addN_zero]
  have h4 : e = M.nzero := M.addN_eq_zero (M.addN_left_cancel h3)
  rw [h4, M.addN_zero] at he
  exact he.symm

/-! ### The natural numbers of the model as an ordered commutative semiring -/

noncomputable instance instZeroNum : Zero M.Num := ⟨M.nzero⟩

noncomputable instance instOneNum : One M.Num := ⟨M.none⟩

noncomputable instance instAddNum : Add M.Num := ⟨M.addN⟩

noncomputable instance instMulNum : Mul M.Num := ⟨M.mulN⟩

noncomputable instance instCommSemiringNum : CommSemiring M.Num where
  add := (· + ·)
  add_assoc := M.addN_assoc
  zero := 0
  zero_add := M.zero_addN
  add_zero := M.addN_zero
  add_comm := M.addN_comm
  mul := (· * ·)
  left_distrib := M.mulN_addN
  right_distrib := fun a b c => by
    show M.mulN (M.addN a b) c = M.addN (M.mulN a c) (M.mulN b c)
    rw [M.mulN_comm, M.mulN_addN, M.mulN_comm c a, M.mulN_comm c b]
  zero_mul := M.zero_mulN
  mul_zero := M.mulN_zero
  mul_assoc := M.mulN_assoc
  one := 1
  one_mul := fun a => by
    show M.mulN M.none a = a
    rw [M.mulN_comm, M.mulN_one]
  mul_one := M.mulN_one
  mul_comm := M.mulN_comm
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl

noncomputable instance instPartialOrderNum : PartialOrder M.Num where
  le := M.leN
  le_refl := M.leN_refl
  le_trans := fun _ _ _ => M.leN_trans
  le_antisymm := fun _ _ => M.leN_antisymm

theorem le_def {a b : M.Num} : a ≤ b ↔ ∃ c, a + c = b := Iff.rfl

theorem zero_def : (0 : M.Num) = M.nzero := rfl

theorem one_def : (1 : M.Num) = M.none := rfl

theorem add_def (a b : M.Num) : a + b = M.addN a b := rfl

theorem mul_def (a b : M.Num) : a * b = M.mulN a b := rfl

theorem nsucc_eq_add_one (a : M.Num) : M.nsucc a = a + 1 := M.nsucc_eq a

instance instIsOrderedRingNum : IsOrderedRing M.Num where
  add_le_add_left := fun a b h c => by
    obtain ⟨d, hd⟩ := M.le_def.mp h
    exact M.le_def.mpr ⟨d, by rw [← hd]; ring⟩
  zero_le_one := M.le_def.mpr ⟨1, zero_add 1⟩
  mul_le_mul_of_nonneg_left := fun a _ b c h => by
    obtain ⟨d, hd⟩ := M.le_def.mp h
    exact M.le_def.mpr ⟨a * d, by rw [← hd]; ring⟩
  mul_le_mul_of_nonneg_right := fun a _ b c h => by
    obtain ⟨d, hd⟩ := M.le_def.mp h
    exact M.le_def.mpr ⟨d * a, by rw [← hd]; ring⟩

instance instCanonicallyOrderedAddNum : CanonicallyOrderedAdd M.Num where
  exists_add_of_le := fun h => by
    obtain ⟨d, hd⟩ := M.le_def.mp h
    exact ⟨d, hd.symm⟩
  le_add_self := fun a b => M.le_def.mpr ⟨b, add_comm a b⟩
  le_self_add := fun a b => M.le_def.mpr ⟨b, rfl⟩

/-! ## The cut and the arithmetic of the model

From here on `+`, `·`, `≤`, `0`, `1` on `M.Num` are the operations just defined. -/

theorem expN_add_one (n : M.Num) : M.expN (n + 1) = M.expN n + M.expN n := by
  rw [← M.nsucc_eq_add_one]
  exact M.expN_succ n

theorem towN_add_one (n : M.Num) : M.towN (n + 1) = M.expN (M.towN n) := by
  rw [← M.nsucc_eq_add_one]
  exact M.towN_succ n

theorem one_le_expN (n : M.Num) : 1 ≤ M.expN n := by
  refine M.num_ind (P := fun n => (1 : M.Num) ≤ M.expN n)
    (M.isPred_le (M.natFn_const 1) M.natFn_expN) ?_ ?_ n
  · show (1 : M.Num) ≤ M.expN M.nzero
    exact le_of_eq M.expN_zero.symm
  · intro k (ih : (1 : M.Num) ≤ M.expN k)
    show (1 : M.Num) ≤ M.expN (M.nsucc k)
    have h2 : M.expN k ≤ M.expN (M.nsucc k) := M.le_def.mpr ⟨M.expN k, (M.expN_succ k).symm⟩
    exact le_trans ih h2

theorem le_expN (n : M.Num) : n ≤ M.expN n := by
  refine M.num_ind (P := fun n => n ≤ M.expN n) (M.isPred_le M.natFn_id M.natFn_expN) ?_ ?_ n
  · show M.nzero ≤ M.expN M.nzero
    exact M.le_def.mpr ⟨_, M.zero_addN _⟩
  · intro k (ih : k ≤ M.expN k)
    show M.nsucc k ≤ M.expN (M.nsucc k)
    have h2 : k + 1 ≤ M.expN k + M.expN k := add_le_add ih (M.one_le_expN k)
    have e1 : M.nsucc k = k + 1 := M.nsucc_eq_add_one k
    have e2 : M.expN (M.nsucc k) = M.expN k + M.expN k := M.expN_succ k
    rw [e2, e1]
    exact h2

theorem towN_le_towN_add (a c : M.Num) : M.towN a ≤ M.towN (a + c) := by
  refine M.num_ind (P := fun c => M.towN a ≤ M.towN (a + c))
    (M.isPred_le (M.natFn_const _) (M.natFn_comp M.natFn_towN
      (M.fnAdd (M.natFn_const a) M.natFn_id))) ?_ ?_ c
  · show M.towN a ≤ M.towN (M.addN a M.nzero)
    exact le_of_eq (by rw [M.addN_zero])
  · intro k (ih : M.towN a ≤ M.towN (M.addN a k))
    show M.towN a ≤ M.towN (M.addN a (M.nsucc k))
    have e : M.towN (M.addN a (M.nsucc k)) = M.expN (M.towN (M.addN a k)) := by
      rw [M.addN_succ, M.towN_succ]
    rw [e]
    exact le_trans ih (M.le_expN _)

/-- The tower is monotone. -/
theorem towN_mono {a b : M.Num} (h : a ≤ b) : M.towN a ≤ M.towN b := by
  obtain ⟨c, hc⟩ := M.le_def.mp h
  rw [← hc]
  exact M.towN_le_towN_add a c

/-! ### The cut is closed downwards -/

def subFml : Fml :=
  .all 3 (.all 4 (Fml.imp (.and (fApp3 1 2 0 3) (.mem 4 3))
    (Fml.ex 5 (.and (.mem 5 2) (.all 6 (Fml.imp (.mem 6 5) (.mem 6 4)))))))

theorem sat_subFml (ad a c : V) :
    Sat M.mem M.isSet subFml (Function.update (Function.update (Function.update (fun _ => dflt)
      1 ad) 2 a) 0 c) ↔
    ∀ s x, (M.mem (M.trip a c s) ad ∧ M.mem x s) →
      ∃ y, M.mem y a ∧ ∀ e, M.mem e y → M.mem e x := by
  simp [subFml, Sat, M.sat_imp, M.sat_ex, M.sat_fApp3, Function.update_apply]

/-- Every member of `a + c` includes a member of `a`. -/
theorem exists_subset_of_add (a c : M.Num) {x : V} (hx : M.mem x (a + c).1) :
    ∃ y, M.mem y a.1 ∧ ∀ e, M.mem e y → M.mem e x := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  have h0 : Sat M.mem M.isSet subFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 ad) 2 a.1) 0 M.zero) := by
    rw [M.sat_subFml]
    rintro s x ⟨hs, hx⟩
    have e : s = (M.addN a M.nzero).1 := M.graph₂_val had (m := a) (n := M.nzero) hs
    rw [e, M.addN_zero] at hx
    exact ⟨x, hx, fun e he => he⟩
  have hs : ∀ k : M.Num, Sat M.mem M.isSet subFml (Function.update (Function.update
      (Function.update (fun _ => dflt) 1 ad) 2 a.1) 0 k.1) →
      Sat M.mem M.isSet subFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 ad) 2 a.1) 0 (M.succ k.1)) := by
    intro k ih
    rw [M.sat_subFml] at ih ⊢
    rintro s x ⟨hs, hx⟩
    have e : s = (M.addN a (M.nsucc k)).1 := M.graph₂_val had (m := a) (n := M.nsucc k) hs
    rw [e, M.addN_succ] at hx
    obtain ⟨x', b, hx', -, hxe⟩ := M.mem_succ.mp hx
    obtain ⟨y, hy, hyx⟩ := ih _ x' ⟨M.graph₂_app had a k, hx'⟩
    refine ⟨y, hy, fun e he => ?_⟩
    rw [hxe]
    exact M.mem_adj.mpr (Or.inl (hyx e he))
  have key := M.num_ind_fml (σW [(1, 7), (4, 1), (5, 1), (6, 0)]) subFml 0 rfl _ h0 hs c
  rw [M.sat_subFml] at key
  exact key _ x ⟨M.graph₂_app had a c, hx⟩

/-- **The cut is closed downwards.** -/
theorem inS_of_le {a b : M.Num} (hab : a ≤ b) (hb : M.InS b.1) : M.InS a.1 := by
  obtain ⟨c, hc⟩ := M.le_def.mp hab
  obtain ⟨-, x, hx, hsc⟩ := hb
  rw [← hc] at hx
  obtain ⟨y, hy, hyx⟩ := M.exists_subset_of_add a c hx
  exact M.inS_of_subset a.2 hy hsc hyx

/-! ### Cardinality of a disjoint union -/

def cardUnFml : Fml :=
  .all 3 (Fml.imp (.mem 3 0) (.all 4 (Fml.imp (.mem 4 2)
    (Fml.imp (.all 6 (Fml.imp (.mem 6 4) (.neg (.mem 6 3))))
      (.all 5 (Fml.imp
        (.and (.set 5) (.all 6 (Fml.iff (.mem 6 5) (Fml.or (.mem 6 4) (.mem 6 3)))))
        (.all 7 (Fml.imp (fApp3 1 2 0 7) (.mem 5 7)))))))))

theorem sat_cardUnFml (ad a c : V) :
    Sat M.mem M.isSet cardUnFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 ad) 2 a) 0 c) ↔
    ∀ B, M.mem B c → ∀ A, M.mem A a → (∀ e, M.mem e A → ¬ M.mem e B) →
      ∀ s, M.mem (M.trip a c s) ad → M.mem (M.un A B) s := by
  have h1 : Sat M.mem M.isSet cardUnFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 ad) 2 a) 0 c) ↔
      ∀ B, M.mem B c → ∀ A, M.mem A a → (∀ e, M.mem e A → ¬ M.mem e B) →
        ∀ U, (M.isSet U ∧ ∀ e, M.mem e U ↔ M.mem e A ∨ M.mem e B) →
          ∀ s, M.mem (M.trip a c s) ad → M.mem U s := by
    simp [cardUnFml, Sat, M.sat_imp, M.sat_iff, M.sat_or, M.sat_fApp3, Function.update_apply]
  rw [h1]
  constructor
  · intro h B hB A hA hd s hs
    exact h B hB A hA hd _ ⟨M.un_isSet A B, fun e => M.mem_un⟩ s hs
  · rintro h B hB A hA hd U hU s hs
    rw [M.eq_un_iff.mp hU]
    exact h B hB A hA hd s hs

/-- **If `A ∈ a` and `B ∈ c` are disjoint, then `A ∪ B ∈ a + c`.** -/
theorem un_mem_add (a c : M.Num) {A B : V} (hA : M.mem A a.1) (hB : M.mem B c.1)
    (hd : ∀ e, M.mem e A → ¬ M.mem e B) : M.mem (M.un A B) (a + c).1 := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  have h0 : Sat M.mem M.isSet cardUnFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 ad) 2 a.1) 0 M.zero) := by
    rw [M.sat_cardUnFml]
    intro B hB A hA hd s hs
    have e : s = (M.addN a M.nzero).1 := M.graph₂_val had (m := a) (n := M.nzero) hs
    have e2 : M.un A B = A := by
      refine M.ext (M.un_isSet A B) (M.isSet_of_mem_nat a.2 hA) fun z => ?_
      rw [M.mem_un, M.mem_zero.mp hB]
      exact ⟨fun h => h.elim id (fun h => absurd h (M.not_mem_emp z)), Or.inl⟩
    rw [e, M.addN_zero, e2]
    exact hA
  have hs : ∀ k : M.Num, Sat M.mem M.isSet cardUnFml (Function.update (Function.update
      (Function.update (fun _ => dflt) 1 ad) 2 a.1) 0 k.1) →
      Sat M.mem M.isSet cardUnFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 ad) 2 a.1) 0 (M.succ k.1)) := by
    intro k ih
    rw [M.sat_cardUnFml] at ih ⊢
    intro B hB A hA hd s hs
    have e : s = (M.addN a (M.nsucc k)).1 := M.graph₂_val had (m := a) (n := M.nsucc k) hs
    obtain ⟨B', b, hB', hb, hBe⟩ := M.mem_succ.mp hB
    rw [hBe] at hd ⊢
    have hd' : ∀ e, M.mem e A → ¬ M.mem e B' := fun e he he' =>
      hd e he (M.mem_adj.mpr (Or.inl he'))
    have hbA : ¬ M.mem b A := fun h => hd b h (M.mem_adj.mpr (Or.inr rfl))
    have ih' := ih B' hB' A hA hd' _ (M.graph₂_app had a k)
    have e2 : M.un A (M.adj B' b) = M.adj (M.un A B') b :=
      M.ext (M.un_isSet _ _) (M.adj_isSet _ _) fun z => by
        simp only [M.mem_un, M.mem_adj]
        tauto
    rw [e, M.addN_succ, e2]
    refine M.mem_succ.mpr ⟨_, b, ih', fun h => ?_, rfl⟩
    rcases M.mem_un.mp h with h | h
    · exact hbA h
    · exact hb h
  have key := M.num_ind_fml (σW [(1, 7), (3, 1), (4, 1), (5, 1), (6, 0)]) cardUnFml 0 rfl _
    h0 hs c
  rw [M.sat_cardUnFml] at key
  exact key B hB A hA hd _ (M.graph₂_app had a c)

/-! ### An injective image of a member of `k` is in `k` -/

def injFml : Fml :=
  .all 1 (Fml.imp (.mem 1 0) (Fml.imp
    (.all 5 (Fml.imp (.mem 5 1) (.and (.set 5) (.neg (.mem 6 5)))))
    (.all 2 (Fml.imp
      (.and (.set 2) (.all 3 (Fml.iff (.mem 3 2) (Fml.ex 5 (.and (.mem 5 1) (fAdj 3 5 6 7))))))
      (.mem 2 0)))))

theorem sat_injFml (b k : V) :
    Sat M.mem M.isSet injFml (Function.update (Function.update (fun _ => dflt) 6 b) 0 k) ↔
    ∀ W, M.mem W k → (∀ z, M.mem z W → M.isSet z ∧ ¬ M.mem b z) → M.mem (M.adjImg W b) k := by
  have h1 : Sat M.mem M.isSet injFml (Function.update (Function.update (fun _ => dflt) 6 b) 0 k) ↔
      ∀ W, M.mem W k → (∀ z, M.mem z W → M.isSet z ∧ ¬ M.mem b z) → ∀ U, (M.isSet U ∧
        ∀ c, M.mem c U ↔ ∃ z, M.mem z W ∧ c = M.adj z b) → M.mem U k := by
    simp only [injFml, Sat, M.sat_imp, M.sat_iff, M.sat_ex,
      M.sat_fAdj (y := 3) (x := 5) (b := 6) (c := 7) (by decide) (by decide) (by decide)]
    simp [Function.update_apply]
  rw [h1]
  constructor
  · intro h W hW hWb
    exact h W hW hWb _ ⟨M.adjImg_isSet W b, fun c => M.mem_adjImg⟩
  · rintro h W hW hWb U hU
    rw [M.eq_adjImg_iff.mp hU]
    exact h W hW hWb

/-- If `W ∈ k` consists of sets not containing `b`, then `{z ∪ {b} : z ∈ W} ∈ k`. -/
theorem adjImg_mem {k W b : V} (hk : M.mem k M.nat) (hW : M.mem W k)
    (hWb : ∀ z, M.mem z W → M.isSet z ∧ ¬ M.mem b z) : M.mem (M.adjImg W b) k := by
  have h0 : Sat M.mem M.isSet injFml
      (Function.update (Function.update (fun _ => dflt) 6 b) 0 M.zero) := by
    rw [M.sat_injFml]
    intro W hW _
    rw [M.mem_zero.mp hW, M.adjImg_emp]
    exact M.mem_zero.mpr rfl
  have hs : ∀ k, M.mem k M.nat → Sat M.mem M.isSet injFml
      (Function.update (Function.update (fun _ => dflt) 6 b) 0 k) →
      Sat M.mem M.isSet injFml
      (Function.update (Function.update (fun _ => dflt) 6 b) 0 (M.succ k)) := by
    intro k _ ih
    rw [M.sat_injFml] at ih ⊢
    intro W hW hWb
    obtain ⟨W', z0, hW', hz0, hWe⟩ := M.mem_succ.mp hW
    rw [hWe] at hWb ⊢
    have hW'b : ∀ z, M.mem z W' → M.isSet z ∧ ¬ M.mem b z := fun z hz =>
      hWb z (M.mem_adj.mpr (Or.inl hz))
    have hz0b := hWb z0 (M.mem_adj.mpr (Or.inr rfl))
    rw [M.adjImg_adj]
    refine M.mem_succ.mpr ⟨_, _, ih W' hW' hW'b, fun h => ?_, rfl⟩
    obtain ⟨z, hz, e⟩ := M.mem_adjImg.mp h
    have hzb := hW'b z hz
    have e1 : z0 = z := by
      rw [← M.rem_adj_self hz0b.1 hz0b.2, e, M.rem_adj_self hzb.1 hzb.2]
    rw [e1] at hz0
    exact hz0 hz
  have key := M.nat_ind_fml' (fun i => match i with
      | 0 => 3 | 1 => 2 | 2 => 2 | 3 => 1 | 5 => 1 | _ => 0) injFml 0 rfl _ h0 hs hk
  rw [M.sat_injFml] at key
  exact key W hW hWb

/-! ### The power set of a member of `n` is in `2ⁿ`, up to the singleton image -/

def powExpFml : Fml :=
  .all 3 (Fml.imp (.mem 3 0) (.all 4 (Fml.imp (.mem 4 2) (.all 5 (Fml.imp
    (.and (.set 5) (.all 8 (Fml.iff (.mem 8 5) (Fml.ex 9 (.and (.mem 9 3) (fSing 8 9 10))))))
    (Fml.imp (.mem 5 4) (.all 6 (Fml.imp
      (.and (.set 6) (.all 11 (Fml.iff (.mem 11 6)
        (.and (.set 11) (.all 12 (Fml.imp (.mem 12 11) (.mem 12 3)))))))
      (.all 7 (Fml.imp (fApp 1 4 7) (.mem 6 7)))))))))))

def powExpStrat : ℕ → ℕ := fun i =>
  match i with
  | 0 => 2 | 1 => 6 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 2 | 6 => 2 | 7 => 3 | 8 => 1 | 11 => 1
  | 36 => 4 | 37 => 3 | 38 => 5 | _ => 0

theorem sat_powExpFml (eG m : V) :
    Sat M.mem M.isSet powExpFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 eG) 2 M.nat) 0 m) ↔
    ∀ y, M.mem y m → ∀ m', M.mem m' M.nat → M.mem (M.simg y) m' →
      ∀ e', M.mem (M.op m' e') eG → M.mem (M.pow y) e' := by
  have h1 : Sat M.mem M.isSet powExpFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 eG) 2 M.nat) 0 m) ↔
      ∀ y, M.mem y m → ∀ m', M.mem m' M.nat → ∀ S, (M.isSet S ∧
        ∀ s, M.mem s S ↔ ∃ a, M.mem a y ∧ s = M.sing a) → M.mem S m' → ∀ P, (M.isSet P ∧
        ∀ z, M.mem z P ↔ M.isSet z ∧ ∀ e, M.mem e z → M.mem e y) →
        ∀ e', M.mem (M.op m' e') eG → M.mem P e' := by
    simp only [powExpFml, Sat, M.sat_imp, M.sat_iff, M.sat_ex,
      M.sat_fSing (u := 8) (a := 9) (c := 10) (by decide) (by decide),
      fun ρ' : ℕ → V => M.sat_fApp (g := 1) (a := 4) (b := 7) ρ' (by decide) (by decide)
        (by decide)]
    simp [Function.update_apply]
  rw [h1]
  constructor
  · intro h y hy m' hm' hS e' he'
    exact h y hy m' hm' _ ⟨M.simg_isSet y, fun s => M.mem_simg⟩ hS _
      ⟨M.pow_isSet y, fun z => M.mem_pow⟩ e' he'
  · rintro h y hy m' hm' S hS hSm P hP e' he'
    rw [M.eq_simg_iff.mp hS] at hSm
    rw [M.eq_pow_iff.mp hP]
    exact h y hy m' hm' hSm e' he'

theorem sing_emp_mem_one : M.mem (M.sing M.emp) (M.succ M.zero) := by
  have e : M.sing M.emp = M.adj M.emp M.emp :=
    M.ext (M.sing_isSet _) (M.adj_isSet _ _) fun z =>
      M.mem_sing.trans (M.mem_adj.trans
        ⟨fun h => h.elim (fun h => absurd h (M.not_mem_emp z)) id, Or.inr⟩).symm
  rw [e]
  exact M.mem_succ.mpr ⟨M.emp, M.emp, M.mem_zero.mpr rfl, M.not_mem_emp _, rfl⟩

/-- **If `y ∈ m` and `{{a} : a ∈ y} ∈ n`, then `P(y) ∈ 2ⁿ`.** This is the equation
`2^{T m} = |P(y)|` for the exponential defined by recursion. -/
theorem pow_mem_expN {m y : V} (hm : M.mem m M.nat) (hy : M.mem y m) (n : M.Num)
    (hs : M.mem (M.simg y) n.1) : M.mem (M.pow y) (M.expN n).1 := by
  obtain ⟨eG, heG⟩ := M.natFn_expN
  have h0 : Sat M.mem M.isSet powExpFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 eG) 2 M.nat) 0 M.zero) := by
    rw [M.sat_powExpFml]
    intro y hy m' hm' hS e' he'
    rw [M.mem_zero.mp hy, M.simg_emp] at hS
    have em : m' = M.zero := M.nat_disjoint hm' M.zero_mem_nat hS (M.mem_zero.mpr rfl)
    rw [em] at he'
    have ee : e' = (M.expN M.nzero).1 := M.graph_val heG (n := M.nzero) he'
    rw [ee, M.expN_zero, M.mem_zero.mp hy, M.pow_emp]
    exact M.sing_emp_mem_one
  have hs' : ∀ k, M.mem k M.nat → Sat M.mem M.isSet powExpFml (Function.update
      (Function.update (Function.update (fun _ => dflt) 1 eG) 2 M.nat) 0 k) →
      Sat M.mem M.isSet powExpFml (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 eG) 2 M.nat) 0 (M.succ k)) := by
    intro k hk ih
    rw [M.sat_powExpFml] at ih ⊢
    intro y hy m' hm' hS e' he'
    obtain ⟨x, b, hx, hb, hye⟩ := M.mem_succ.mp hy
    rw [hye, M.simg_adj] at hS
    rw [hye]
    have hnb : ¬ M.mem (M.sing b) (M.simg x) := by
      intro h
      obtain ⟨a, ha, e⟩ := M.mem_simg.mp h
      have hba : b = a := M.sing_inj e
      rw [hba] at hb
      exact hb ha
    rcases M.nat_cases hm' with em | ⟨k', hk', em⟩
    · rw [em] at hS
      have h1 := M.mem_zero.mp hS
      have h2 : M.mem (M.sing b) (M.adj (M.simg x) (M.sing b)) := M.mem_adj.mpr (Or.inr rfl)
      rw [h1] at h2
      exact absurd h2 (M.not_mem_emp _)
    · rw [em] at hS he'
      have h1 := M.rem_mem_of_succ hk' hS (M.mem_adj.mpr (Or.inr rfl))
      rw [M.rem_adj_self (M.simg_isSet x) hnb] at h1
      have hpow : M.mem (M.pow x) (M.expN ⟨k', hk'⟩).1 :=
        ih x hx k' hk' h1 _ (M.graph_app heG ⟨k', hk'⟩)
      have ee : e' = (M.expN (M.nsucc ⟨k', hk'⟩)).1 :=
        M.graph_val heG (n := M.nsucc ⟨k', hk'⟩) he'
      have himg : M.mem (M.adjImg (M.pow x) b) (M.expN ⟨k', hk'⟩).1 :=
        M.adjImg_mem (M.expN ⟨k', hk'⟩).2 hpow fun z hz =>
          ⟨(M.mem_pow.mp hz).1, fun hbz => hb ((M.mem_pow.mp hz).2 b hbz)⟩
      have hd : ∀ e, M.mem e (M.pow x) → ¬ M.mem e (M.adjImg (M.pow x) b) := by
        intro e he he'
        obtain ⟨z, -, ez⟩ := M.mem_adjImg.mp he'
        have hbe : M.mem b e := by
          rw [ez]
          exact M.mem_adj.mpr (Or.inr rfl)
        exact hb ((M.mem_pow.mp he).2 b hbe)
      rw [ee, M.expN_succ, M.pow_adj]
      exact M.un_mem_add _ _ hpow himg hd
  have key := M.nat_ind_fml' powExpStrat powExpFml 0 rfl _ h0 hs' hm
  rw [M.sat_powExpFml] at key
  exact key y hy n.1 n.2 hs _ (M.graph_app heG n)

/-- **The cut is closed under the exponential.** -/
theorem inS_expN {n : M.Num} (h : M.InS n.1) : M.InS (M.expN n).1 := by
  obtain ⟨hn, x, hx, hsc⟩ := h
  have h1 := M.simg_mem_of_sc hn hx hsc
  have h2 := M.pow_mem_expN hn hx n h1
  exact ⟨(M.expN n).2, M.pow x, h2, M.sc_pow hsc⟩

/-! ### The cut is closed under addition and multiplication -/

theorem isPred_or {P Q : M.Num → Prop} (hP : M.IsPred P) (hQ : M.IsPred Q) :
    M.IsPred (fun n => P n ∨ Q n) :=
  M.isPred_congr (P := fun n => ¬ (¬ P n ∧ ¬ Q n))
    (fun n => ⟨fun h => by_contra fun hn => h ⟨fun hp => hn (Or.inl hp), fun hq => hn (Or.inr hq)⟩,
      fun h hpq => h.elim hpq.1 hpq.2⟩)
    (M.isPred_not (M.isPred_and (M.isPred_not hP) (M.isPred_not hQ)))

/-- The order on the natural numbers of the model is total. -/
theorem le_total' (a b : M.Num) : a ≤ b ∨ b ≤ a := by
  refine M.num_ind (P := fun b => a ≤ b ∨ b ≤ a)
    (M.isPred_or (M.isPred_le (M.natFn_const a) M.natFn_id)
      (M.isPred_le M.natFn_id (M.natFn_const a))) ?_ ?_ b
  · exact Or.inr (M.le_def.mpr ⟨a, M.zero_addN a⟩)
  · intro k (ih : a ≤ k ∨ k ≤ a)
    show a ≤ M.nsucc k ∨ M.nsucc k ≤ a
    rw [M.nsucc_eq_add_one]
    rcases ih with h | h
    · exact Or.inl (le_trans h (M.le_def.mpr ⟨1, rfl⟩))
    · obtain ⟨c, hc⟩ := M.le_def.mp h
      rcases M.num_cases c with hc0 | ⟨c', hc'⟩
      · left
        rw [hc0] at hc
        have e : a = k := by
          rw [← hc]
          exact M.addN_zero k
        rw [e]
        exact M.le_def.mpr ⟨1, rfl⟩
      · right
        rw [hc', M.nsucc_eq_add_one] at hc
        exact M.le_def.mpr ⟨c', by rw [← hc]; ring⟩

theorem expN_add (a b : M.Num) : M.expN (a + b) = M.expN a * M.expN b := by
  refine M.num_ind (P := fun b => M.expN (a + b) = M.expN a * M.expN b)
    (M.isPred_eq (M.natFn_comp M.natFn_expN (M.fnAdd (M.natFn_const a) M.natFn_id))
      (M.fnMul (M.natFn_const _) M.natFn_expN)) ?_ ?_ b
  · show M.expN (M.addN a M.nzero) = M.mulN (M.expN a) (M.expN M.nzero)
    rw [M.addN_zero, M.expN_zero, M.mulN_one]
  · intro k (ih : M.expN (M.addN a k) = M.mulN (M.expN a) (M.expN k))
    show M.expN (M.addN a (M.nsucc k)) = M.mulN (M.expN a) (M.expN (M.nsucc k))
    rw [M.addN_succ, M.expN_succ (M.addN a k), M.expN_succ k, ih, M.mulN_addN]

theorem inS_add {a b : M.Num} (ha : M.InS a.1) (hb : M.InS b.1) : M.InS (a + b).1 := by
  have key : ∀ a b : M.Num, a ≤ b → M.InS b.1 → M.InS (a + b).1 := by
    intro a b hab hb
    have h1 : a + b ≤ M.expN (b + 1) := by
      rw [M.expN_add_one]
      exact add_le_add (le_trans hab (M.le_expN b)) (M.le_expN b)
    have h2 : M.InS (M.expN (b + 1)).1 := by
      refine M.inS_expN ?_
      rw [← M.nsucc_eq_add_one]
      exact M.inS_succ hinf.out hb
    exact M.inS_of_le h1 h2
  rcases M.le_total' a b with h | h
  · exact key a b h hb
  · rw [add_comm]
    exact key b a h ha

theorem inS_mul {a b : M.Num} (ha : M.InS a.1) (hb : M.InS b.1) : M.InS (a * b).1 := by
  have key : ∀ a b : M.Num, a ≤ b → M.InS b.1 → M.InS (a * b).1 := by
    intro a b hab hb
    have h1 : a * b ≤ M.expN (b + b) := by
      rw [M.expN_add]
      exact mul_le_mul (le_trans hab (M.le_expN b)) (M.le_expN b) zero_le zero_le
    exact M.inS_of_le h1 (M.inS_expN (M.inS_add hb hb))
  rcases M.le_total' a b with h | h
  · exact key a b h hb
  · rw [mul_comm]
    exact key b a h ha

/-- The natural numbers of the model satisfy the axioms of Robinson arithmetic for `0`, `1`,
`+`, `·`; together with `pa_induction` below they form a model of Peano arithmetic. -/
theorem peano :
    (∀ n : M.Num, n + 1 ≠ 0) ∧ (∀ m n : M.Num, m + 1 = n + 1 → m = n) ∧
    (∀ a : M.Num, a + 0 = a) ∧ (∀ a b : M.Num, a + (b + 1) = (a + b) + 1) ∧
    (∀ a : M.Num, a * 0 = 0) ∧ (∀ a b : M.Num, a * (b + 1) = a * b + a) := by
  refine ⟨fun n h => ?_, fun m n h => ?_, fun a => add_zero a, fun a b => (add_assoc a b 1).symm,
    fun a => mul_zero a, fun a b => by ring⟩
  · rw [← M.nsucc_eq_add_one] at h
    exact M.nzero_ne_nsucc n h.symm
  · rw [← M.nsucc_eq_add_one, ← M.nsucc_eq_add_one] at h
    exact M.nsucc_inj h

/-- The defining equations of `2ˣ` and of the tower. -/
theorem exp_tower_equations :
    M.expN 0 = 1 ∧ (∀ n : M.Num, M.expN (n + 1) = M.expN n + M.expN n) ∧
    M.towN 0 = 1 + 1 ∧ ∀ n : M.Num, M.towN (n + 1) = M.expN (M.towN n) := by
  refine ⟨M.expN_zero, M.expN_add_one, ?_, M.towN_add_one⟩
  rw [← M.nsucc_eq_add_one]
  exact M.towN_zero

/-- The function defined by recursion is unique. -/
theorem prec_unique {h : M.Num → M.Num} {g : M.Num → M.Num → M.Num}
    {F F' : M.Num → M.Num → M.Num} (hF : M.NatOp F) (hF' : M.NatOp F')
    (h0 : ∀ a, F a M.nzero = h a) (hs : ∀ a b, F a (M.nsucc b) = g a (F a b))
    (h0' : ∀ a, F' a M.nzero = h a) (hs' : ∀ a b, F' a (M.nsucc b) = g a (F' a b))
    (a b : M.Num) : F a b = F' a b := by
  refine M.num_ind (P := fun b => F a b = F' a b)
    (M.isPred_eq (M.natFn_op₂ hF (M.natFn_const a) M.natFn_id)
      (M.natFn_op₂ hF' (M.natFn_const a) M.natFn_id)) ?_ ?_ b
  · show F a M.nzero = F' a M.nzero
    rw [h0, h0']
  · intro k (ih : F a k = F' a k)
    show F a (M.nsucc k) = F' a (M.nsucc k)
    rw [hs, hs', ih]

/-! ## The operation `T` -/

def tFml : Fml :=
  Fml.ex 2 (.and (.mem 2 1) (.all 3 (Fml.imp (.mem 3 0) (.all 4 (Fml.imp
    (.and (.set 4) (.all 5 (Fml.iff (.mem 5 4) (Fml.ex 6 (.and (.mem 6 3) (fSing 5 6 7))))))
    (.mem 4 2))))))

def tStrat : ℕ → ℕ := fun i =>
  match i with
  | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 1 | _ => 0

theorem sat_tFml (m : V) :
    Sat M.mem M.isSet tFml (Function.update (Function.update (fun _ => dflt) 1 M.nat) 0 m) ↔
    ∃ k, M.mem k M.nat ∧ ∀ x, M.mem x m → M.mem (M.simg x) k := by
  have h1 : Sat M.mem M.isSet tFml
      (Function.update (Function.update (fun _ => dflt) 1 M.nat) 0 m) ↔
      ∃ k, M.mem k M.nat ∧ ∀ x, M.mem x m → ∀ S, (M.isSet S ∧
        ∀ s, M.mem s S ↔ ∃ a, M.mem a x ∧ s = M.sing a) → M.mem S k := by
    simp only [tFml, Sat, M.sat_imp, M.sat_iff, M.sat_ex,
      M.sat_fSing (u := 5) (a := 6) (c := 7) (by decide) (by decide)]
    simp [Function.update_apply]
  rw [h1]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, fun x hx => h x hx _ ⟨M.simg_isSet x, fun s => M.mem_simg⟩⟩
  · rintro ⟨k, hk, h⟩
    refine ⟨k, hk, fun x hx S hS => ?_⟩
    rw [M.eq_simg_iff.mp hS]
    exact h x hx

/-- For every natural number `m` there is a natural number containing the singleton images
of all members of `m`. -/
theorem exists_T (m : M.Num) : ∃ k : M.Num, ∀ x, M.mem x m.1 → M.mem (M.simg x) k.1 := by
  have h0 : Sat M.mem M.isSet tFml
      (Function.update (Function.update (fun _ => dflt) 1 M.nat) 0 M.zero) := by
    rw [M.sat_tFml]
    refine ⟨M.zero, M.zero_mem_nat, fun x hx => ?_⟩
    rw [M.mem_zero.mp hx, M.simg_emp]
    exact M.mem_zero.mpr rfl
  have hs : ∀ k : M.Num, Sat M.mem M.isSet tFml
      (Function.update (Function.update (fun _ => dflt) 1 M.nat) 0 k.1) →
      Sat M.mem M.isSet tFml
      (Function.update (Function.update (fun _ => dflt) 1 M.nat) 0 (M.succ k.1)) := by
    intro k ih
    rw [M.sat_tFml] at ih ⊢
    obtain ⟨j, hj, h⟩ := ih
    refine ⟨M.succ j, M.succ_mem_nat hj, fun x hx => ?_⟩
    obtain ⟨x', b, hx', hb, hxe⟩ := M.mem_succ.mp hx
    rw [hxe, M.simg_adj]
    refine M.mem_succ.mpr ⟨_, _, h x' hx', fun hc => ?_, rfl⟩
    obtain ⟨a, ha, e⟩ := M.mem_simg.mp hc
    have hba : b = a := M.sing_inj e
    rw [hba] at hb
    exact hb ha
  have key := M.num_ind_fml tStrat tFml 0 rfl _ h0 hs m
  rw [M.sat_tFml] at key
  obtain ⟨k, hk, h⟩ := key
  exact ⟨⟨k, hk⟩, h⟩

/-- `T m` is the natural number containing `{{a} : a ∈ x}` for `x ∈ m`. -/
noncomputable def T (m : M.Num) : M.Num := Classical.choose (M.exists_T m)

theorem simg_mem_T {m : M.Num} {x : V} (hx : M.mem x m.1) : M.mem (M.simg x) (M.T m).1 :=
  Classical.choose_spec (M.exists_T m) x hx

/-- `T m` is determined by one member of `m`. -/
theorem T_eq_of_mem {m n : M.Num} {x : V} (hx : M.mem x m.1) (hs : M.mem (M.simg x) n.1) :
    M.T m = n :=
  Subtype.ext (M.nat_disjoint (M.T m).2 n.2 (M.simg_mem_T hx) hs)

/-- **Lemma 2.1 (a).** `T 0 = 0`. -/
theorem T_zero : M.T 0 = 0 := by
  refine M.T_eq_of_mem (m := 0) (x := M.emp) (M.mem_zero.mpr rfl) ?_
  rw [M.simg_emp]
  exact M.mem_zero.mpr rfl

/-- **Lemma 2.1 (a).** `T (n + 1) = T n + 1`. -/
theorem T_succ (n : M.Num) : M.T (n + 1) = M.T n + 1 := by
  obtain ⟨x, hx⟩ := M.nat_nonempty n.2
  obtain ⟨b, hb⟩ := M.infinity_iff.mp hinf.out n.1 n.2 x hx
  rw [← M.nsucc_eq_add_one, ← M.nsucc_eq_add_one]
  refine M.T_eq_of_mem (m := M.nsucc n) (x := M.adj x b)
    (M.mem_succ.mpr ⟨x, b, hx, hb, rfl⟩) ?_
  show M.mem (M.simg (M.adj x b)) (M.succ (M.T n).1)
  rw [M.simg_adj]
  refine M.mem_succ.mpr ⟨_, _, M.simg_mem_T hx, fun hc => ?_, rfl⟩
  obtain ⟨a, ha, e⟩ := M.mem_simg.mp hc
  have hba : b = a := M.sing_inj e
  rw [hba] at hb
  exact hb ha

/-- **Lemma 2.1 (b).** `T` is the identity on the cut. -/
theorem T_eq_self_of_inS {n : M.Num} (h : M.InS n.1) : M.T n = n := by
  obtain ⟨hn, x, hx, hsc⟩ := h
  exact M.T_eq_of_mem hx (M.simg_mem_of_sc hn hx hsc)

/-! ## The induction schema of Peano arithmetic

Formulas of arithmetic are taken in relational form, with atomic formulas `x = y`, `x = 0`,
`x = 1`, `x + y = z` and `x · y = z`. Every such formula, with its quantifiers restricted to
the natural numbers, is stratified: give every variable the type of a number and the graphs
of `+` and `·` the type of a set of triples of numbers. So induction holds for it. -/

/-- Formulas of arithmetic in relational form. -/
inductive AFml : Type
  | eq (x y : ℕ) : AFml
  | zero (x : ℕ) : AFml
  | one (x : ℕ) : AFml
  | add (x y z : ℕ) : AFml
  | mul (x y z : ℕ) : AFml
  | neg (φ : AFml) : AFml
  | and (φ ψ : AFml) : AFml
  | all (x : ℕ) (φ : AFml) : AFml

/-- Truth of a formula of arithmetic in the natural numbers of the model. -/
def holds : AFml → (ℕ → M.Num) → Prop
  | .eq x y, e => e x = e y
  | .zero x, e => e x = 0
  | .one x, e => e x = 1
  | .add x y z, e => e x + e y = e z
  | .mul x y z, e => e x * e y = e z
  | .neg φ, e => ¬ holds φ e
  | .and φ ψ, e => holds φ e ∧ holds ψ e
  | .all x φ, e => ∀ a : M.Num, holds φ (Function.update e x a)

/-- The translation into the language of set theory. The variable `i` becomes the name
`i + 100`; the names `1`–`5` stand for `0`, `ℕ`, the graph of `+`, the graph of `·`, and `1`. -/
def trA : AFml → Fml
  | .eq x y => .eq (x + 100) (y + 100)
  | .zero x => .eq (x + 100) 1
  | .one x => .eq (x + 100) 5
  | .add x y z => fApp3 3 (x + 100) (y + 100) (z + 100)
  | .mul x y z => fApp3 4 (x + 100) (y + 100) (z + 100)
  | .neg φ => .neg (trA φ)
  | .and φ ψ => .and (trA φ) (trA ψ)
  | .all x φ => .all (x + 100) (Fml.imp (.mem (x + 100) 2) (trA φ))

/-- The stratification of translated formulas: every variable of arithmetic has type `2`. -/
def σP : ℕ → ℕ := fun i => if 100 ≤ i then 2 else σW [(2, 3), (3, 7), (4, 7)] i

/-- **Every formula of arithmetic is stratified.** -/
theorem strat_trA (φ : AFml) : (trA φ).strat σP = true := by
  have hv : ∀ x, σP (x + 100) = 2 := fun x => by simp [σP]
  induction φ with
  | eq x y => simp [trA, Fml.strat, hv]
  | zero x => simp [trA, Fml.strat, hv, show σP 1 = 2 from rfl]
  | one x => simp [trA, Fml.strat, hv, show σP 5 = 2 from rfl]
  | add x y z =>
    simp [trA, fApp3, fTrip, fOp, fSing, fUp, Fml.ex, Fml.iff, Fml.imp, Fml.or, Fml.strat, hv,
      show σP 3 = 7 from rfl, show σP 39 = 6 from rfl, show σP 32 = 4 from rfl,
      show σP 33 = 4 from rfl, show σP 34 = 5 from rfl, show σP 35 = 4 from rfl,
      show σP 36 = 3 from rfl, show σP 37 = 2 from rfl]
  | mul x y z =>
    simp [trA, fApp3, fTrip, fOp, fSing, fUp, Fml.ex, Fml.iff, Fml.imp, Fml.or, Fml.strat, hv,
      show σP 4 = 7 from rfl, show σP 39 = 6 from rfl, show σP 32 = 4 from rfl,
      show σP 33 = 4 from rfl, show σP 34 = 5 from rfl, show σP 35 = 4 from rfl,
      show σP 36 = 3 from rfl, show σP 37 = 2 from rfl]
  | neg φ ih => simpa [trA, Fml.strat] using ih
  | and φ ψ ih1 ih2 => simp [trA, Fml.strat, ih1, ih2]
  | all x φ ih => simp [trA, Fml.imp, Fml.strat, ih, hv, show σP 2 = 3 from rfl]

/-- The assignment `ρ` of the model represents the assignment `e` of numbers, with the
parameters in place. -/
def Rep (ad mu : V) (ρ : ℕ → V) (e : ℕ → M.Num) : Prop :=
  ρ 1 = M.zero ∧ ρ 2 = M.nat ∧ ρ 3 = ad ∧ ρ 4 = mu ∧ ρ 5 = (1 : M.Num).1 ∧
    ∀ i, ρ (i + 100) = (e i).1

theorem rep_update {ad mu : V} {ρ : ℕ → V} {e : ℕ → M.Num} (h : M.Rep ad mu ρ e) (x : ℕ)
    (a : M.Num) : M.Rep ad mu (Function.update ρ (x + 100) a.1) (Function.update e x a) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, fun i => ?_⟩
  · rw [Function.update_of_ne (by omega)]
    exact h1
  · rw [Function.update_of_ne (by omega)]
    exact h2
  · rw [Function.update_of_ne (by omega)]
    exact h3
  · rw [Function.update_of_ne (by omega)]
    exact h4
  · rw [Function.update_of_ne (by omega)]
    exact h5
  · by_cases hi : i = x
    · rw [hi, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne hi]
      exact h6 i

theorem sat_trA {ad mu : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN) :
    ∀ (φ : AFml) (ρ : ℕ → V) (e : ℕ → M.Num), M.Rep ad mu ρ e →
      (Sat M.mem M.isSet (trA φ) ρ ↔ M.holds φ e) := by
  intro φ
  induction φ with
  | eq x y =>
    intro ρ e h
    simp only [trA, Sat, holds, h.2.2.2.2.2 x, h.2.2.2.2.2 y]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  | zero x =>
    intro ρ e h
    simp only [trA, Sat, holds, h.2.2.2.2.2 x, h.1]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  | one x =>
    intro ρ e h
    simp only [trA, Sat, holds, h.2.2.2.2.2 x, h.2.2.2.2.1]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  | add x y z =>
    intro ρ e h
    rw [trA, M.sat_fApp3 ρ (by decide) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)), h.2.2.2.2.2 x, h.2.2.2.2.2 y, h.2.2.2.2.2 z, h.2.2.1]
    simp only [holds]
    constructor
    · intro hm
      exact Subtype.ext (M.graph₂_val had hm).symm
    · intro he
      have h3 := M.graph₂_app had (e x) (e y)
      rw [show M.addN (e x) (e y) = e z from he] at h3
      exact h3
  | mul x y z =>
    intro ρ e h
    rw [trA, M.sat_fApp3 ρ (by decide) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)), h.2.2.2.2.2 x, h.2.2.2.2.2 y, h.2.2.2.2.2 z, h.2.2.2.1]
    simp only [holds]
    constructor
    · intro hm
      exact Subtype.ext (M.graph₂_val hmu hm).symm
    · intro he
      have h3 := M.graph₂_app hmu (e x) (e y)
      rw [show M.mulN (e x) (e y) = e z from he] at h3
      exact h3
  | neg φ ih =>
    intro ρ e h
    simp only [trA, Sat, holds, ih ρ e h]
  | and φ ψ ih1 ih2 =>
    intro ρ e h
    simp only [trA, Sat, holds, ih1 ρ e h, ih2 ρ e h]
  | all x φ ih =>
    intro ρ e h
    have hx2 : (2 : ℕ) ≠ x + 100 := by omega
    simp only [trA, Sat, M.sat_imp, holds, Function.update_self, Function.update_of_ne hx2,
      h.2.1]
    constructor
    · intro hall a
      exact (ih _ _ (M.rep_update h x a)).mp (hall a.1 a.2)
    · intro hall a ha
      exact (ih _ _ (M.rep_update h x ⟨a, ha⟩)).mpr (hall ⟨a, ha⟩)

/-- **The induction schema of Peano arithmetic holds in the natural numbers of every model of
NFU + Infinity**, for every formula of arithmetic and every choice of parameters. -/
theorem pa_induction (φ : AFml) (x : ℕ) (e : ℕ → M.Num)
    (h0 : M.holds φ (Function.update e x 0))
    (hs : ∀ k : M.Num, M.holds φ (Function.update e x k) →
      M.holds φ (Function.update e x (k + 1)))
    (n : M.Num) : M.holds φ (Function.update e x n) := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  obtain ⟨mu, hmu⟩ := M.mulN_natOp
  let ρ : ℕ → V := fun i => if 100 ≤ i then (e (i - 100)).1 else if i = 1 then M.zero
    else if i = 2 then M.nat else if i = 3 then ad else if i = 4 then mu else (1 : M.Num).1
  have hρ : M.Rep ad mu ρ e :=
    ⟨by simp [ρ], by simp [ρ], by simp [ρ], by simp [ρ], by simp [ρ], fun i => by simp [ρ]⟩
  have hrep : ∀ a : M.Num, M.Rep ad mu (Function.update ρ (x + 100) a.1)
      (Function.update e x a) := fun a => M.rep_update hρ x a
  have key := M.num_ind_fml σP (trA φ) (x + 100) (strat_trA φ) ρ
    ((M.sat_trA had hmu φ _ _ (hrep 0)).mpr h0)
    (fun k ih => (M.sat_trA had hmu φ _ _ (hrep (M.nsucc k))).mpr (by
      rw [M.nsucc_eq_add_one]
      exact hs k ((M.sat_trA had hmu φ _ _ (hrep k)).mp ih))) n
  exact (M.sat_trA had hmu φ _ _ (hrep n)).mp key

/-! ## Lemmas 2.2 and 2.3 -/

/-- **Lemma 2.2.** The cut `𝖲` of natural numbers with a strongly cantorian member contains
`0`, is closed under successor and under `n ↦ 2ⁿ`, is closed downwards and under `+` and `·`,
and is fixed pointwise by `T`; and for a strongly cantorian `x ∈ n`, the singleton image of `x`
is in `n` and `P(x) ∈ 2ⁿ`. -/
theorem lemma_2_2 :
    M.InS (0 : M.Num).1 ∧ (∀ n : M.Num, M.InS n.1 → M.InS (n + 1).1) ∧
    (∀ n : M.Num, M.InS n.1 → M.InS (M.expN n).1) ∧
    (∀ a b : M.Num, a ≤ b → M.InS b.1 → M.InS a.1) ∧
    (∀ a b : M.Num, M.InS a.1 → M.InS b.1 → M.InS (a + b).1 ∧ M.InS (a * b).1) ∧
    (∀ n : M.Num, M.InS n.1 → M.T n = n) ∧
    ∀ (n : M.Num) (x : V), M.mem x n.1 → M.SC x →
      M.mem (M.simg x) n.1 ∧ M.mem (M.pow x) (M.expN n).1 := by
  refine ⟨M.inS_zero, fun n h => ?_, fun n h => M.inS_expN h, fun a b hab hb => M.inS_of_le hab hb,
    fun a b ha hb => ⟨M.inS_add ha hb, M.inS_mul ha hb⟩, fun n h => M.T_eq_self_of_inS h,
    fun n x hx hsc => ?_⟩
  · rw [← M.nsucc_eq_add_one]
    exact M.inS_succ hinf.out h
  · have h1 := M.simg_mem_of_sc n.2 hx hsc
    exact ⟨h1, M.pow_mem_expN n.2 hx n h1⟩

/-- The hypotheses of the shortening argument hold for the cut, the tower and the
exponential of the model. -/
theorem shortening_hyp : Shortening.Hyp (fun n : M.Num => M.InS n.1) M.towN M.expN where
  down := fun hab hb => M.inS_of_le hab hb
  mono := fun h => M.towN_mono h
  step := fun n => M.towN_add_one n
  exp := fun h => M.inS_expN h
  base := by
    show M.InS (M.towN M.nzero).1
    rw [M.towN_zero]
    exact M.inS_succ hinf.out (M.inS_succ hinf.out M.inS_zero)

/-- `𝖢₂`: the numbers `n` with `t(n)` in the cut. -/
def InC₂ (n : M.Num) : Prop := Shortening.C₂ (fun n : M.Num => M.InS n.1) M.towN n

/-- `𝖪`: the cut obtained from `𝖢₂` by shortening twice. -/
def InK (n : M.Num) : Prop := Shortening.K (fun n : M.Num => M.InS n.1) M.towN n

/-- **Lemma 2.3 (tower absorption).** `𝖪` is closed downwards and under `+` and `·`, contains
`0` and `1`, is included in `𝖢₂`, and for `n ∈ 𝖪` and standard `c`, `d`, `j`, applying `2ˣ`
to `t(c · n + d)` `j` times gives a number of the cut `𝖲`. -/
theorem lemma_2_3 :
    (∀ a b : M.Num, a ≤ b → M.InK b → M.InK a) ∧ M.InK 0 ∧ M.InK 1 ∧
    (∀ a b : M.Num, M.InK a → M.InK b → M.InK (a + b)) ∧
    (∀ a b : M.Num, M.InK a → M.InK b → M.InK (a * b)) ∧
    (∀ n : M.Num, M.InK n → M.InS (M.towN n).1) ∧
    ∀ n : M.Num, M.InK n → ∀ c d j : ℕ,
      M.InS (M.expN^[j] (M.towN ((c : M.Num) * n + (d : M.Num)))).1 :=
  ⟨fun _ _ hab hb => Shortening.K_down M.shortening_hyp hab hb, Shortening.K_zero,
    Shortening.K_one, fun _ _ ha hb => Shortening.K_add ha hb,
    fun _ _ ha hb => Shortening.K_mul ha hb,
    fun _ hn => Shortening.K_sub M.shortening_hyp hn,
    fun _ hn c d j => Shortening.absorb M.shortening_hyp hn c d j⟩

end Model

end NFUCut
