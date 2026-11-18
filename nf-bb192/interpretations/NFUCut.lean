module

public import Mathlib.Tactic

/-!
# The strongly cantorian cut in NFU + Infinity (core of §2 of the note)

We work in an arbitrary model of NFU: a membership relation, a predicate "is a set",
extensionality for sets, and comprehension for stratified formulas. The numerals are Frege's:
`0 = {∅}` and `n + 1 = {x ∪ {b} : x ∈ n, b ∉ x}`, and `ℕ` is the least set containing `0` and
closed under successor.

A set `x` is *strongly cantorian* if the map `a ↦ {a}` restricted to `x` is a set. The main
results are: strongly cantorian sets are closed under adjoining an element, under subsets and
under power set; and if `x` is a strongly cantorian member of a numeral `n`, then the set of
singletons of members of `x` is again in `n` (that is, `T n = n`). So the numerals with a
strongly cantorian member contain `0`, are closed under successor (by Infinity) and under
`n ↦ 2ⁿ`, and are fixed by `T`.

Formulas have named variables, and a stratification is an assignment of types to names.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

@[expose] public section

namespace NFUCut

/-! ## Formulas and satisfaction -/

/-- Formulas in the language `∈`, `=`, "is a set", with named variables. -/
inductive Fml : Type
  | mem (x y : ℕ) : Fml
  | eq (x y : ℕ) : Fml
  | set (x : ℕ) : Fml
  | neg (φ : Fml) : Fml
  | and (φ ψ : Fml) : Fml
  | all (x : ℕ) (φ : Fml) : Fml

namespace Fml

def or (φ ψ : Fml) : Fml := neg (and (neg φ) (neg ψ))
def imp (φ ψ : Fml) : Fml := neg (and φ (neg ψ))
def iff (φ ψ : Fml) : Fml := and (imp φ ψ) (imp ψ φ)
def ex (x : ℕ) (φ : Fml) : Fml := neg (all x (neg φ))

/-- `σ` is a stratification of the formula: `x ∈ y` needs `σ y = σ x + 1`, and `x = y` needs
`σ x = σ y`. -/
def strat (σ : ℕ → ℕ) : Fml → Bool
  | mem x y => σ y == σ x + 1
  | eq x y => σ x == σ y
  | set _ => true
  | neg φ => strat σ φ
  | and φ ψ => strat σ φ && strat σ ψ
  | all _ φ => strat σ φ

end Fml

variable {V : Type}

/-- Satisfaction. -/
def Sat (mem : V → V → Prop) (isSet : V → Prop) : Fml → (ℕ → V) → Prop
  | .mem x y, ρ => mem (ρ x) (ρ y)
  | .eq x y, ρ => ρ x = ρ y
  | .set x, ρ => isSet (ρ x)
  | .neg φ, ρ => ¬ Sat mem isSet φ ρ
  | .and φ ψ, ρ => Sat mem isSet φ ρ ∧ Sat mem isSet ψ ρ
  | .all x φ, ρ => ∀ a, Sat mem isSet φ (Function.update ρ x a)

/-- A model of NFU: sets are determined by their members, only sets have members, and every
stratified formula defines a set. -/
structure Model (V : Type) where
  mem : V → V → Prop
  isSet : V → Prop
  isSet_of_mem : ∀ {x y : V}, mem x y → isSet y
  ext : ∀ {x y : V}, isSet x → isSet y → (∀ z, mem z x ↔ mem z y) → x = y
  comp : ∀ (σ : ℕ → ℕ) (φ : Fml) (x : ℕ), φ.strat σ = true → ∀ ρ : ℕ → V,
    ∃ y, isSet y ∧ ∀ a, mem a y ↔ Sat mem isSet φ (Function.update ρ x a)

namespace Model

variable [Nonempty V] (M : Model V)

theorem sat_or {φ ψ : Fml} {ρ : ℕ → V} :
    Sat M.mem M.isSet (φ.or ψ) ρ ↔ Sat M.mem M.isSet φ ρ ∨ Sat M.mem M.isSet ψ ρ := by
  simp only [Fml.or, Sat]
  tauto

theorem sat_imp {φ ψ : Fml} {ρ : ℕ → V} :
    Sat M.mem M.isSet (φ.imp ψ) ρ ↔ (Sat M.mem M.isSet φ ρ → Sat M.mem M.isSet ψ ρ) := by
  simp only [Fml.imp, Sat]
  tauto

theorem sat_iff {φ ψ : Fml} {ρ : ℕ → V} :
    Sat M.mem M.isSet (φ.iff ψ) ρ ↔ (Sat M.mem M.isSet φ ρ ↔ Sat M.mem M.isSet ψ ρ) := by
  simp only [Fml.iff, Fml.imp, Sat]
  tauto

theorem sat_ex {x : ℕ} {φ : Fml} {ρ : ℕ → V} :
    Sat M.mem M.isSet (φ.ex x) ρ ↔ ∃ a, Sat M.mem M.isSet φ (Function.update ρ x a) := by
  simp only [Fml.ex, Sat]
  exact not_forall_not

/-- An arbitrary element, used for the variables that do not matter. -/
noncomputable def dflt : V := Classical.arbitrary V

/-! ## Basic sets -/

theorem exists_emp : ∃ e, M.isSet e ∧ ∀ a, ¬ M.mem a e := by
  obtain ⟨e, he, h⟩ := M.comp (fun _ => 0) (.neg (.eq 0 0)) 0 rfl (fun _ => dflt)
  refine ⟨e, he, fun a ha => ?_⟩
  have := (h a).mp ha
  simp [Sat] at this

/-- The empty set. -/
noncomputable def emp : V := Classical.choose M.exists_emp

theorem emp_isSet : M.isSet M.emp := (Classical.choose_spec M.exists_emp).1

theorem not_mem_emp (a : V) : ¬ M.mem a M.emp := (Classical.choose_spec M.exists_emp).2 a

theorem eq_emp {x : V} (hx : M.isSet x) (h : ∀ a, ¬ M.mem a x) : x = M.emp :=
  M.ext hx M.emp_isSet fun z => ⟨fun hz => absurd hz (h z), fun hz => absurd hz (M.not_mem_emp z)⟩

theorem exists_sing (a : V) : ∃ u, M.isSet u ∧ ∀ c, M.mem c u ↔ c = a := by
  obtain ⟨u, hu, h⟩ := M.comp (fun _ => 0) (.eq 0 1) 0 rfl (Function.update (fun _ => dflt) 1 a)
  refine ⟨u, hu, fun c => ?_⟩
  simpa [Sat, Function.update_apply] using h c

/-- The singleton `{a}`. -/
noncomputable def sing (a : V) : V := Classical.choose (M.exists_sing a)

theorem sing_isSet (a : V) : M.isSet (M.sing a) := (Classical.choose_spec (M.exists_sing a)).1

theorem mem_sing {a c : V} : M.mem c (M.sing a) ↔ c = a :=
  (Classical.choose_spec (M.exists_sing a)).2 c

theorem sing_inj {a b : V} (h : M.sing a = M.sing b) : a = b :=
  M.mem_sing.mp (h ▸ M.mem_sing.mpr rfl)

theorem eq_sing_iff {u a : V} : (∀ c, M.mem c u ↔ c = a) ↔ u = M.sing a := by
  constructor
  · intro h
    exact M.ext (M.isSet_of_mem ((h a).mpr rfl)) (M.sing_isSet a) fun z =>
      (h z).trans M.mem_sing.symm
  · rintro rfl c
    exact M.mem_sing

theorem exists_up (a b : V) : ∃ u, M.isSet u ∧ ∀ c, M.mem c u ↔ c = a ∨ c = b := by
  obtain ⟨u, hu, h⟩ := M.comp (fun _ => 0) (Fml.or (.eq 0 1) (.eq 0 2)) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 a) 2 b)
  refine ⟨u, hu, fun c => ?_⟩
  simpa [M.sat_or, Sat, Function.update_apply] using h c

/-- The unordered pair `{a, b}`. -/
noncomputable def up (a b : V) : V := Classical.choose (M.exists_up a b)

theorem up_isSet (a b : V) : M.isSet (M.up a b) := (Classical.choose_spec (M.exists_up a b)).1

theorem mem_up {a b c : V} : M.mem c (M.up a b) ↔ c = a ∨ c = b :=
  (Classical.choose_spec (M.exists_up a b)).2 c

theorem eq_up_iff {u a b : V} : (∀ c, M.mem c u ↔ c = a ∨ c = b) ↔ u = M.up a b := by
  constructor
  · intro h
    exact M.ext (M.isSet_of_mem ((h a).mpr (Or.inl rfl))) (M.up_isSet a b) fun z =>
      (h z).trans M.mem_up.symm
  · rintro rfl c
    exact M.mem_up

theorem exists_adj (x b : V) : ∃ y, M.isSet y ∧ ∀ c, M.mem c y ↔ M.mem c x ∨ c = b := by
  obtain ⟨y, hy, h⟩ := M.comp (fun i => if i = 1 then 1 else 0) (Fml.or (.mem 0 1) (.eq 0 2)) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 x) 2 b)
  refine ⟨y, hy, fun c => ?_⟩
  simpa [M.sat_or, Sat, Function.update_apply] using h c

/-- `x ∪ {b}`. -/
noncomputable def adj (x b : V) : V := Classical.choose (M.exists_adj x b)

theorem adj_isSet (x b : V) : M.isSet (M.adj x b) := (Classical.choose_spec (M.exists_adj x b)).1

theorem mem_adj {x b c : V} : M.mem c (M.adj x b) ↔ M.mem c x ∨ c = b :=
  (Classical.choose_spec (M.exists_adj x b)).2 c

theorem eq_adj_iff {y x b : V} : (∀ c, M.mem c y ↔ M.mem c x ∨ c = b) ↔ y = M.adj x b := by
  constructor
  · intro h
    exact M.ext (M.isSet_of_mem ((h b).mpr (Or.inr rfl))) (M.adj_isSet x b) fun z =>
      (h z).trans M.mem_adj.symm
  · rintro rfl c
    exact M.mem_adj

/-- The Kuratowski pair `{{a}, {a, b}}`. -/
noncomputable def op (a b : V) : V := M.up (M.sing a) (M.up a b)

theorem up_eq_sing {a b c : V} (h : M.up a b = M.sing c) : a = c ∧ b = c :=
  ⟨M.mem_sing.mp (h ▸ M.mem_up.mpr (Or.inl rfl)), M.mem_sing.mp (h ▸ M.mem_up.mpr (Or.inr rfl))⟩

theorem op_inj {a b a' b' : V} (h : M.op a b = M.op a' b') : a = a' ∧ b = b' := by
  have h1 : M.mem (M.sing a) (M.op a' b') := h ▸ M.mem_up.mpr (Or.inl rfl)
  have ha : a = a' := by
    rcases M.mem_up.mp h1 with e | e
    · exact M.sing_inj e
    · exact (M.up_eq_sing e.symm).1.symm
  subst ha
  refine ⟨rfl, ?_⟩
  have h2 : M.mem (M.up a b) (M.op a b') := h ▸ M.mem_up.mpr (Or.inr rfl)
  have h3 : M.mem (M.up a b') (M.op a b) := h.symm ▸ M.mem_up.mpr (Or.inr rfl)
  rcases M.mem_up.mp h2 with e | e
  · have hb : b = a := (M.up_eq_sing e).2
    rcases M.mem_up.mp h3 with e' | e'
    · exact hb.trans (M.up_eq_sing e').2.symm
    · have : M.mem b' (M.up a b) := e' ▸ M.mem_up.mpr (Or.inr rfl)
      rcases M.mem_up.mp this with e'' | e''
      · exact hb.trans e''.symm
      · exact e''.symm
  · have : M.mem b (M.up a b') := e ▸ M.mem_up.mpr (Or.inr rfl)
    rcases M.mem_up.mp this with e' | e'
    · rcases M.mem_up.mp h3 with e'' | e''
      · exact e'.trans (M.up_eq_sing e'').2.symm
      · have : M.mem b' (M.up a b) := e'' ▸ M.mem_up.mpr (Or.inr rfl)
        rcases M.mem_up.mp this with e3 | e3
        · exact e'.trans e3.symm
        · exact e3.symm
    · exact e'

theorem eq_op_iff {p a b : V} :
    (∀ u, M.mem u p ↔ u = M.sing a ∨ u = M.up a b) ↔ p = M.op a b :=
  M.eq_up_iff

theorem eq_emp_iff {y : V} : (M.isSet y ∧ ∀ c, ¬ M.mem c y) ↔ y = M.emp :=
  ⟨fun h => M.eq_emp h.1 h.2, fun h => h ▸ ⟨M.emp_isSet, M.not_mem_emp⟩⟩

/-! ## Formulas for the basic notions -/

/-- `u = {a}`. -/
def fSing (u a c : ℕ) : Fml := .all c (Fml.iff (.mem c u) (.eq c a))

/-- `u = {a, b}`. -/
def fUp (u a b c : ℕ) : Fml := .all c (Fml.iff (.mem c u) (Fml.or (.eq c a) (.eq c b)))

/-- `y = x ∪ {b}`. -/
def fAdj (y x b c : ℕ) : Fml := .all c (Fml.iff (.mem c y) (Fml.or (.mem c x) (.eq c b)))

/-- `p = ⟨a, b⟩`. -/
def fOp (p a b u c : ℕ) : Fml :=
  .all u (Fml.iff (.mem u p) (Fml.or (fSing u a c) (fUp u a b c)))

/-- `y = ∅`. -/
def fEmp (y c : ℕ) : Fml := .and (.set y) (.all c (.neg (.mem c y)))

theorem sat_fSing {u a c : ℕ} (hu : u ≠ c) (ha : a ≠ c) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fSing u a c) ρ ↔ ρ u = M.sing (ρ a) := by
  rw [← M.eq_sing_iff]
  simp only [fSing, Sat, M.sat_iff, Function.update_self, Function.update_of_ne hu,
    Function.update_of_ne ha]

theorem sat_fUp {u a b c : ℕ} (hu : u ≠ c) (ha : a ≠ c) (hb : b ≠ c) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fUp u a b c) ρ ↔ ρ u = M.up (ρ a) (ρ b) := by
  rw [← M.eq_up_iff]
  simp only [fUp, Sat, M.sat_iff, M.sat_or, Function.update_self, Function.update_of_ne hu,
    Function.update_of_ne ha, Function.update_of_ne hb]

theorem sat_fAdj {y x b c : ℕ} (hy : y ≠ c) (hx : x ≠ c) (hb : b ≠ c) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fAdj y x b c) ρ ↔ ρ y = M.adj (ρ x) (ρ b) := by
  rw [← M.eq_adj_iff]
  simp only [fAdj, Sat, M.sat_iff, M.sat_or, Function.update_self, Function.update_of_ne hy,
    Function.update_of_ne hx, Function.update_of_ne hb]

theorem sat_fOp {p a b u c : ℕ} (hpu : p ≠ u) (hau : a ≠ u) (hbu : b ≠ u) (hac : a ≠ c)
    (hbc : b ≠ c) (huc : u ≠ c) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fOp p a b u c) ρ ↔ ρ p = M.op (ρ a) (ρ b) := by
  rw [← M.eq_op_iff]
  simp only [fOp, Sat, M.sat_iff, M.sat_or, M.sat_fSing huc hac, M.sat_fUp huc hac hbc,
    Function.update_self, Function.update_of_ne hpu, Function.update_of_ne hau,
    Function.update_of_ne hbu]

theorem sat_fEmp {y c : ℕ} (hy : y ≠ c) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fEmp y c) ρ ↔ ρ y = M.emp := by
  rw [← M.eq_emp_iff]
  simp only [fEmp, Sat, Function.update_self, Function.update_of_ne hy]

/-! ## Numerals -/

/-- The numeral `0 = {∅}`. -/
noncomputable def zero : V := M.sing M.emp

theorem mem_zero {y : V} : M.mem y M.zero ↔ y = M.emp := M.mem_sing

/-- `y` is a member of the successor of `k`: `∃x b (x ∈ k ∧ b ∉ x ∧ y = x ∪ {b})`. -/
def fSuccMem (y k x b z : ℕ) : Fml :=
  Fml.ex x (Fml.ex b (.and (.mem x k) (.and (.neg (.mem b x)) (fAdj y x b z))))

theorem sat_fSuccMem {y k x b z : ℕ} (hyx : y ≠ x) (hyb : y ≠ b) (hyz : y ≠ z) (hkx : k ≠ x)
    (hkb : k ≠ b) (hxb : x ≠ b) (hxz : x ≠ z) (hbz : b ≠ z) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fSuccMem y k x b z) ρ ↔
      ∃ x' b', M.mem x' (ρ k) ∧ ¬ M.mem b' x' ∧ ρ y = M.adj x' b' := by
  simp only [fSuccMem, M.sat_ex, Sat, M.sat_fAdj hyz hxz hbz, Function.update_self,
    Function.update_of_ne hyx, Function.update_of_ne hyb, Function.update_of_ne hkx,
    Function.update_of_ne hkb, Function.update_of_ne hxb]

theorem exists_succ (k : V) : ∃ s, M.isSet s ∧ ∀ y, M.mem y s ↔
    ∃ x b, M.mem x k ∧ ¬ M.mem b x ∧ y = M.adj x b := by
  obtain ⟨s, hs, h⟩ := M.comp (fun i => if i = 1 then 2 else if i = 0 ∨ i = 2 then 1 else 0)
    (fSuccMem 0 1 2 3 4) 0 rfl (Function.update (fun _ => dflt) 1 k)
  refine ⟨s, hs, fun y => ?_⟩
  rw [h y, M.sat_fSuccMem (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  simp [Function.update_apply]

/-- The successor of a numeral: `{x ∪ {b} : x ∈ k, b ∉ x}`. -/
noncomputable def succ (k : V) : V := Classical.choose (M.exists_succ k)

theorem succ_isSet (k : V) : M.isSet (M.succ k) := (Classical.choose_spec (M.exists_succ k)).1

theorem mem_succ {k y : V} :
    M.mem y (M.succ k) ↔ ∃ x b, M.mem x k ∧ ¬ M.mem b x ∧ y = M.adj x b :=
  (Classical.choose_spec (M.exists_succ k)).2 y

theorem eq_succ_iff {s k : V} : (M.isSet s ∧ ∀ y, M.mem y s ↔
    ∃ x b, M.mem x k ∧ ¬ M.mem b x ∧ y = M.adj x b) ↔ s = M.succ k := by
  constructor
  · rintro ⟨hs, h⟩
    exact M.ext hs (M.succ_isSet k) fun z => (h z).trans M.mem_succ.symm
  · rintro rfl
    exact ⟨M.succ_isSet k, fun y => M.mem_succ⟩

/-- `s` is the successor of `k`. -/
def fSucc (s k y x b z : ℕ) : Fml :=
  .and (.set s) (.all y (Fml.iff (.mem y s) (fSuccMem y k x b z)))

theorem sat_fSucc {s k y x b z : ℕ} (hsy : s ≠ y) (hky : k ≠ y) (hyx : y ≠ x) (hyb : y ≠ b)
    (hyz : y ≠ z) (hkx : k ≠ x) (hkb : k ≠ b) (hxb : x ≠ b) (hxz : x ≠ z) (hbz : b ≠ z)
    (ρ : ℕ → V) : Sat M.mem M.isSet (fSucc s k y x b z) ρ ↔ ρ s = M.succ (ρ k) := by
  rw [← M.eq_succ_iff]
  simp only [fSucc, Sat, M.sat_iff, M.sat_fSuccMem hyx hyb hyz hkx hkb hxb hxz hbz,
    Function.update_self, Function.update_of_ne hsy, Function.update_of_ne hky]

/-- `n` belongs to every set that contains `o` and is closed under successor. -/
def fNat : Fml :=
  .all 2 (Fml.imp
    (.and (.mem 1 2) (.all 3 (Fml.imp (.mem 3 2) (Fml.ex 4 (.and (.mem 4 2) (fSucc 4 3 5 6 7 8))))))
    (.mem 0 2))

theorem exists_nat : ∃ N, M.isSet N ∧ ∀ n, M.mem n N ↔
    ∀ I, (M.mem M.zero I ∧ ∀ k, M.mem k I → M.mem (M.succ k) I) → M.mem n I := by
  obtain ⟨N, hN, h⟩ := M.comp
    (fun i => if i = 2 then 3 else if i = 5 ∨ i = 6 then 1 else if i = 7 ∨ i = 8 then 0 else 2)
    fNat 0 rfl (Function.update (fun _ => dflt) 1 M.zero)
  refine ⟨N, hN, fun n => ?_⟩
  rw [h n]
  simp only [fNat, Sat, M.sat_imp, M.sat_ex, M.sat_fSucc (s := 4) (k := 3) (y := 5) (x := 6)
    (b := 7) (z := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)]
  simp [Function.update_apply]

/-- The set of natural numbers. -/
noncomputable def nat : V := Classical.choose M.exists_nat

theorem mem_nat {n : V} : M.mem n M.nat ↔
    ∀ I, (M.mem M.zero I ∧ ∀ k, M.mem k I → M.mem (M.succ k) I) → M.mem n I :=
  (Classical.choose_spec M.exists_nat).2 n

theorem zero_mem_nat : M.mem M.zero M.nat := M.mem_nat.mpr fun _ h => h.1

theorem succ_mem_nat {n : V} (h : M.mem n M.nat) : M.mem (M.succ n) M.nat :=
  M.mem_nat.mpr fun I hI => hI.2 n (M.mem_nat.mp h I hI)

/-- Induction for sets. -/
theorem nat_ind {I n : V} (h0 : M.mem M.zero I) (hs : ∀ k, M.mem k I → M.mem (M.succ k) I)
    (hn : M.mem n M.nat) : M.mem n I :=
  M.mem_nat.mp hn I ⟨h0, hs⟩

/-! ## Images, singleton images, unions, power sets -/

/-- `∃a ∈ y, ⟨a, s⟩ ∈ f`. The bound variables are the names `20`, `21`, `22`, `23`. -/
def fImgMem (s f y : ℕ) : Fml :=
  Fml.ex 20 (.and (.mem 20 y) (Fml.ex 21 (.and (.mem 21 f) (fOp 21 20 s 22 23))))

theorem sat_fImgMem {s f y : ℕ} (hs : s < 20 ∨ 23 < s) (hf : f < 20 ∨ 23 < f)
    (hy : y < 20 ∨ 23 < y) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fImgMem s f y) ρ ↔ ∃ a, M.mem a (ρ y) ∧ M.mem (M.op a (ρ s)) (ρ f) := by
  have h1 : y ≠ 20 := by omega
  have h2 : f ≠ 20 := by omega
  have h3 : f ≠ 21 := by omega
  have h4 : s ≠ 20 := by omega
  have h5 : s ≠ 21 := by omega
  have h6 : s ≠ 22 := by omega
  have h7 : s ≠ 23 := by omega
  simp only [fImgMem, M.sat_ex, Sat, M.sat_fOp (p := 21) (a := 20) (b := s) (u := 22) (c := 23)
    (by decide) (by decide) h6 (by decide) h7 (by decide), Function.update_self,
    Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4, Function.update_of_ne h5,
    Function.update_of_ne (show (20 : ℕ) ≠ 21 by decide)]
  constructor
  · rintro ⟨a, ha, p, hp, rfl⟩
    exact ⟨a, ha, hp⟩
  · rintro ⟨a, ha, hp⟩
    exact ⟨a, ha, _, hp, rfl⟩

theorem exists_img (f y : V) : ∃ w, M.isSet w ∧ ∀ s, M.mem s w ↔
    ∃ a, M.mem a y ∧ M.mem (M.op a s) f := by
  obtain ⟨w, hw, h⟩ := M.comp
    (fun i => if i = 1 then 3 else if i = 2 ∨ i = 22 then 1 else if i = 21 then 2 else 0)
    (fImgMem 0 1 2) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 f) 2 y)
  refine ⟨w, hw, fun s => ?_⟩
  rw [h s, M.sat_fImgMem (by decide) (by decide) (by decide)]
  simp [Function.update_apply]

/-- The image of `y` under the set of pairs `f`. -/
noncomputable def img (f y : V) : V := Classical.choose (M.exists_img f y)

theorem img_isSet (f y : V) : M.isSet (M.img f y) := (Classical.choose_spec (M.exists_img f y)).1

theorem mem_img {f y s : V} : M.mem s (M.img f y) ↔ ∃ a, M.mem a y ∧ M.mem (M.op a s) f :=
  (Classical.choose_spec (M.exists_img f y)).2 s

theorem eq_img_iff {w f y : V} : (M.isSet w ∧ ∀ s, M.mem s w ↔
    ∃ a, M.mem a y ∧ M.mem (M.op a s) f) ↔ w = M.img f y := by
  constructor
  · rintro ⟨hw, h⟩
    exact M.ext hw (M.img_isSet f y) fun z => (h z).trans M.mem_img.symm
  · rintro rfl
    exact ⟨M.img_isSet f y, fun s => M.mem_img⟩

/-- `w` is the image of `y` under `f`. The extra bound variable is the name `24`. -/
def fImg (w f y : ℕ) : Fml := .and (.set w) (.all 24 (Fml.iff (.mem 24 w) (fImgMem 24 f y)))

theorem sat_fImg {w f y : ℕ} (hw : w < 20) (hf : f < 20) (hy : y < 20) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fImg w f y) ρ ↔ ρ w = M.img (ρ f) (ρ y) := by
  have h1 : w ≠ 24 := by omega
  have h2 : f ≠ 24 := by omega
  have h3 : y ≠ 24 := by omega
  rw [← M.eq_img_iff]
  simp only [fImg, Sat, M.sat_iff, M.sat_fImgMem (s := 24) (Or.inr (by decide)) (Or.inl hf)
    (Or.inl hy), Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3]

theorem exists_simg (x : V) : ∃ w, M.isSet w ∧ ∀ s, M.mem s w ↔
    ∃ a, M.mem a x ∧ s = M.sing a := by
  obtain ⟨w, hw, h⟩ := M.comp (fun i => if i = 0 ∨ i = 1 then 1 else 0)
    (Fml.ex 20 (.and (.mem 20 1) (fSing 0 20 23))) 0 rfl
    (Function.update (fun _ => dflt) 1 x)
  refine ⟨w, hw, fun s => ?_⟩
  rw [h s]
  simp only [M.sat_ex, Sat, M.sat_fSing (u := 0) (a := 20) (c := 23) (by decide) (by decide)]
  simp [Function.update_apply]

/-- The set of singletons of the members of `x`. -/
noncomputable def simg (x : V) : V := Classical.choose (M.exists_simg x)

theorem simg_isSet (x : V) : M.isSet (M.simg x) := (Classical.choose_spec (M.exists_simg x)).1

theorem mem_simg {x s : V} : M.mem s (M.simg x) ↔ ∃ a, M.mem a x ∧ s = M.sing a :=
  (Classical.choose_spec (M.exists_simg x)).2 s

theorem exists_sUnion (w : V) : ∃ y, M.isSet y ∧ ∀ e, M.mem e y ↔
    ∃ s, M.mem s w ∧ M.mem e s := by
  obtain ⟨y, hy, h⟩ := M.comp (fun i => if i = 1 then 2 else if i = 2 then 1 else 0)
    (Fml.ex 2 (.and (.mem 2 1) (.mem 0 2))) 0 rfl (Function.update (fun _ => dflt) 1 w)
  refine ⟨y, hy, fun e => ?_⟩
  rw [h e]
  simp [M.sat_ex, Sat, Function.update_apply]

/-- The union of the members of `w`. -/
noncomputable def sUnion (w : V) : V := Classical.choose (M.exists_sUnion w)

theorem sUnion_isSet (w : V) : M.isSet (M.sUnion w) :=
  (Classical.choose_spec (M.exists_sUnion w)).1

theorem mem_sUnion {w e : V} : M.mem e (M.sUnion w) ↔ ∃ s, M.mem s w ∧ M.mem e s :=
  (Classical.choose_spec (M.exists_sUnion w)).2 e

theorem exists_pow (x : V) : ∃ P, M.isSet P ∧ ∀ y, M.mem y P ↔
    M.isSet y ∧ ∀ z, M.mem z y → M.mem z x := by
  obtain ⟨P, hP, h⟩ := M.comp (fun i => if i = 2 then 0 else 1)
    (.and (.set 0) (.all 2 (Fml.imp (.mem 2 0) (.mem 2 1)))) 0 rfl
    (Function.update (fun _ => dflt) 1 x)
  refine ⟨P, hP, fun y => ?_⟩
  rw [h y]
  simp [M.sat_imp, Sat, Function.update_apply]

/-- The power set: the sets included in `x`. -/
noncomputable def pow (x : V) : V := Classical.choose (M.exists_pow x)

theorem pow_isSet (x : V) : M.isSet (M.pow x) := (Classical.choose_spec (M.exists_pow x)).1

theorem mem_pow {x y : V} : M.mem y (M.pow x) ↔ M.isSet y ∧ ∀ z, M.mem z y → M.mem z x :=
  (Classical.choose_spec (M.exists_pow x)).2 y

/-! ## Strongly cantorian sets -/

/-- `f` is the graph of `a ↦ {a}` on `x`. -/
def IsGraph (f x : V) : Prop := ∀ p, M.mem p f ↔ ∃ a, M.mem a x ∧ p = M.op a (M.sing a)

/-- `x` is strongly cantorian: the map `a ↦ {a}` restricted to `x` is a set. -/
def SC (x : V) : Prop := ∃ f, M.IsGraph f x

theorem IsGraph.mem_op {f x a s : V} (hf : M.IsGraph f x) :
    M.mem (M.op a s) f ↔ M.mem a x ∧ s = M.sing a := by
  rw [hf]
  constructor
  · rintro ⟨a', ha', e⟩
    obtain ⟨rfl, rfl⟩ := M.op_inj e
    exact ⟨ha', rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ha, rfl⟩

/-- On a subset of `x`, the image under the graph is the set of singletons. -/
theorem IsGraph.img_eq {f x y : V} (hf : M.IsGraph f x) (hyx : ∀ a, M.mem a y → M.mem a x) :
    M.img f y = M.simg y := by
  refine M.ext (M.img_isSet f y) (M.simg_isSet y) fun s => ?_
  rw [M.mem_img, M.mem_simg]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, ((IsGraph.mem_op M hf).mp h).2⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (IsGraph.mem_op M hf).mpr ⟨hyx a ha, rfl⟩⟩

theorem sc_emp : M.SC M.emp :=
  ⟨M.emp, fun p => ⟨fun h => absurd h (M.not_mem_emp p),
    fun ⟨a, ha, _⟩ => absurd ha (M.not_mem_emp a)⟩⟩

/-- Adjoining an element to a strongly cantorian set. -/
theorem sc_adj {x b : V} (h : M.SC x) : M.SC (M.adj x b) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨M.adj f (M.op b (M.sing b)), fun p => ?_⟩
  rw [M.mem_adj, hf]
  constructor
  · rintro (⟨a, ha, rfl⟩ | rfl)
    · exact ⟨a, M.mem_adj.mpr (Or.inl ha), rfl⟩
    · exact ⟨b, M.mem_adj.mpr (Or.inr rfl), rfl⟩
  · rintro ⟨a, ha, rfl⟩
    rcases M.mem_adj.mp ha with ha | rfl
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr rfl

/-- A subset of a strongly cantorian set is strongly cantorian. -/
theorem sc_subset {x y : V} (h : M.SC x) (hyx : ∀ a, M.mem a y → M.mem a x) : M.SC y := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, -, hg⟩ := M.comp
    (fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 ∨ i = 22 then 1 else 0)
    (.and (.mem 0 1) (Fml.ex 20 (.and (.mem 20 2) (Fml.ex 24 (fOp 0 20 24 22 23))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 f) 2 y)
  have hg' : ∀ p, M.mem p g ↔ M.mem p f ∧ ∃ a, M.mem a y ∧ ∃ s, p = M.op a s := by
    intro p
    rw [hg p]
    simp only [M.sat_ex, Sat, M.sat_fOp (p := 0) (a := 20) (b := 24) (u := 22) (c := 23)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [Function.update_apply]
  refine ⟨g, fun p => ?_⟩
  rw [hg']
  constructor
  · rintro ⟨hp, a, ha, s, rfl⟩
    exact ⟨a, ha, by rw [((IsGraph.mem_op M hf).mp hp).2]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(IsGraph.mem_op M hf).mpr ⟨hyx a ha, rfl⟩, a, ha, _, rfl⟩

theorem sUnion_simg {y : V} (hy : M.isSet y) : M.sUnion (M.simg y) = y := by
  refine M.ext (M.sUnion_isSet _) hy fun e => ?_
  rw [M.mem_sUnion]
  constructor
  · rintro ⟨s, hs, he⟩
    obtain ⟨a, ha, rfl⟩ := M.mem_simg.mp hs
    rwa [M.mem_sing.mp he]
  · intro he
    exact ⟨M.sing e, M.mem_simg.mpr ⟨e, he, rfl⟩, M.mem_sing.mpr rfl⟩

theorem eq_sUnion_iff {v w : V} : (M.isSet v ∧ ∀ e, M.mem e v ↔ ∃ s, M.mem s w ∧ M.mem e s) ↔
    v = M.sUnion w := by
  constructor
  · rintro ⟨hv, h⟩
    exact M.ext hv (M.sUnion_isSet w) fun z => (h z).trans M.mem_sUnion.symm
  · rintro rfl
    exact ⟨M.sUnion_isSet w, fun e => M.mem_sUnion⟩

/-- `u = {⋃w}`. The bound variables are the names `25`, `26`, `27`. -/
def fSingUn (u w : ℕ) : Fml :=
  .all 25 (Fml.iff (.mem 25 u)
    (.and (.set 25) (.all 26 (Fml.iff (.mem 26 25) (Fml.ex 27 (.and (.mem 27 w) (.mem 26 27)))))))

theorem sat_fSingUn {u w : ℕ} (hu : u < 20) (hw : w < 20) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fSingUn u w) ρ ↔ ρ u = M.sing (M.sUnion (ρ w)) := by
  have h1 : u ≠ 25 := by omega
  have h2 : w ≠ 25 := by omega
  have h3 : w ≠ 26 := by omega
  have h4 : w ≠ 27 := by omega
  rw [← M.eq_sing_iff]
  simp only [fSingUn, Sat, M.sat_iff, M.sat_ex, Function.update_self, Function.update_of_ne h1,
    Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4,
    Function.update_of_ne (show (25 : ℕ) ≠ 26 by decide),
    Function.update_of_ne (show (25 : ℕ) ≠ 27 by decide),
    Function.update_of_ne (show (26 : ℕ) ≠ 27 by decide), M.eq_sUnion_iff]

/-- **The power set of a strongly cantorian set is strongly cantorian.** The graph of
`y ↦ {y}` on the power set is `{⟨y, {⋃ f"y}⟩ : y ⊆ x}`, which is given by a stratified
formula with `f` as a parameter. -/
theorem sc_pow {x : V} (h : M.SC x) : M.SC (M.pow x) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, -, hg⟩ := M.comp
    (fun i => match i with
      | 0 => 4 | 1 => 2 | 2 => 4 | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 1
      | 20 => 1 | 21 => 3 | 22 => 2 | 23 => 1 | 24 => 1 | 25 => 1 | 26 => 0 | 27 => 1
      | 30 => 3 | 31 => 2 | _ => 0)
    (Fml.ex 3 (Fml.ex 4 (.and (fOp 0 3 4 30 31) (.and (.set 3)
      (.and (.all 6 (Fml.imp (.mem 6 3) (.mem 6 1)))
        (Fml.ex 5 (.and (fImg 5 2 3) (fSingUn 4 5)))))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 x) 2 f)
  have hg' : ∀ q, M.mem q g ↔ ∃ y u, q = M.op y u ∧ M.isSet y ∧
      (∀ z, M.mem z y → M.mem z x) ∧ u = M.sing (M.sUnion (M.img f y)) := by
    intro q
    rw [hg q]
    simp only [M.sat_ex, Sat, M.sat_imp, M.sat_fOp (p := 0) (a := 3) (b := 4) (u := 30) (c := 31)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      M.sat_fImg (w := 5) (f := 2) (y := 3) (by decide) (by decide) (by decide),
      M.sat_fSingUn (u := 4) (w := 5) (by decide) (by decide)]
    simp [Function.update_apply]
  refine ⟨g, fun q => ?_⟩
  rw [hg']
  constructor
  · rintro ⟨y, u, rfl, hys, hyx, rfl⟩
    refine ⟨y, M.mem_pow.mpr ⟨hys, hyx⟩, ?_⟩
    rw [IsGraph.img_eq M hf hyx, M.sUnion_simg hys]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hys, hyx⟩ := M.mem_pow.mp hy
    refine ⟨y, M.sing y, rfl, hys, hyx, ?_⟩
    rw [IsGraph.img_eq M hf hyx, M.sUnion_simg hys]

/-! ## Induction for stratified formulas -/

/-- Induction on the natural numbers for a property given by a stratified formula. -/
theorem nat_ind_fml (σ : ℕ → ℕ) (φ : Fml) (x : ℕ) (hφ : φ.strat σ = true) (ρ : ℕ → V)
    (h0 : Sat M.mem M.isSet φ (Function.update ρ x M.zero))
    (hs : ∀ k, Sat M.mem M.isSet φ (Function.update ρ x k) →
      Sat M.mem M.isSet φ (Function.update ρ x (M.succ k)))
    {n : V} (hn : M.mem n M.nat) : Sat M.mem M.isSet φ (Function.update ρ x n) := by
  obtain ⟨I, -, hI⟩ := M.comp σ φ x hφ ρ
  exact (hI n).mp (M.nat_ind ((hI _).mpr h0) (fun k hk => (hI _).mpr (hs k ((hI k).mp hk))) hn)

/-- The members of a natural number are sets. -/
theorem isSet_of_mem_nat {n x : V} (hn : M.mem n M.nat) (hx : M.mem x n) : M.isSet x := by
  have hsat : ∀ m, Sat M.mem M.isSet (.all 1 (Fml.imp (.mem 1 0) (.set 1)))
      (Function.update (fun _ => dflt) 0 m) ↔ ∀ y, M.mem y m → M.isSet y := by
    intro m
    simp [Sat, M.sat_imp, Function.update_apply]
  have h0 : Sat M.mem M.isSet (.all 1 (Fml.imp (.mem 1 0) (.set 1)))
      (Function.update (fun _ => dflt) 0 M.zero) := by
    rw [hsat]
    intro y hy
    rw [M.mem_zero.mp hy]
    exact M.emp_isSet
  have hs : ∀ k, Sat M.mem M.isSet (.all 1 (Fml.imp (.mem 1 0) (.set 1)))
      (Function.update (fun _ => dflt) 0 k) →
      Sat M.mem M.isSet (.all 1 (Fml.imp (.mem 1 0) (.set 1)))
      (Function.update (fun _ => dflt) 0 (M.succ k)) := by
    intro k _
    rw [hsat]
    intro y hy
    obtain ⟨x', b, -, -, rfl⟩ := M.mem_succ.mp hy
    exact M.adj_isSet _ _
  have key := M.nat_ind_fml (fun i => if i = 0 then 1 else 0) _ 0 rfl _ h0 hs hn
  rw [hsat] at key
  exact key x hx

/-! ## A strongly cantorian member of `n` has its singleton image in `n` -/

theorem simg_emp : M.simg M.emp = M.emp :=
  M.eq_emp (M.simg_isSet _) fun s hs => by
    obtain ⟨a, ha, -⟩ := M.mem_simg.mp hs
    exact M.not_mem_emp a ha

theorem simg_adj (x b : V) : M.simg (M.adj x b) = M.adj (M.simg x) (M.sing b) := by
  refine M.ext (M.simg_isSet _) (M.adj_isSet _ _) fun s => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := M.mem_simg.mp h
    rcases M.mem_adj.mp ha with ha | rfl
    · exact M.mem_adj.mpr (Or.inl (M.mem_simg.mpr ⟨a, ha, rfl⟩))
    · exact M.mem_adj.mpr (Or.inr rfl)
  · rcases M.mem_adj.mp h with h | rfl
    · obtain ⟨a, ha, rfl⟩ := M.mem_simg.mp h
      exact M.mem_simg.mpr ⟨a, M.mem_adj.mpr (Or.inl ha), rfl⟩
    · exact M.mem_simg.mpr ⟨b, M.mem_adj.mpr (Or.inr rfl), rfl⟩

/-- `∀y (y ⊆ x → y ∈ m → f"y ∈ m)`, with `m`, `x`, `f` the names `0`, `1`, `2`. -/
def cantorFml : Fml :=
  .all 3 (Fml.imp (.all 4 (Fml.imp (.mem 4 3) (.mem 4 1)))
    (Fml.imp (.mem 3 0) (Fml.ex 5 (.and (fImg 5 2 3) (.mem 5 0)))))

def cantorStrat : ℕ → ℕ := fun i =>
  match i with
  | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 1 | 5 => 1 | 21 => 2 | 22 => 1 | _ => 0

theorem sat_cantorFml (x f m : V) :
    Sat M.mem M.isSet cantorFml
      (Function.update (Function.update (Function.update (fun _ => dflt) 1 x) 2 f) 0 m) ↔
    ∀ y, (∀ e, M.mem e y → M.mem e x) → M.mem y m → M.mem (M.img f y) m := by
  simp only [cantorFml, Sat, M.sat_imp, M.sat_ex,
    M.sat_fImg (w := 5) (f := 2) (y := 3) (by decide) (by decide) (by decide)]
  simp [Function.update_apply]

/-- **If `x` is a strongly cantorian member of the natural number `n`, then the set of
singletons of members of `x` is also in `n`.** In the usual notation: `T n = n`. The proof is
by induction on `m` for the property `∀y ⊆ x (y ∈ m → f"y ∈ m)`, which is stratified because
the graph `f` of the singleton map on `x` is a parameter. -/
theorem simg_mem_of_sc {n x : V} (hn : M.mem n M.nat) (hx : M.mem x n) (h : M.SC x) :
    M.mem (M.simg x) n := by
  obtain ⟨f, hf⟩ := h
  have h0 : Sat M.mem M.isSet cantorFml
      (Function.update (Function.update (Function.update (fun _ => dflt) 1 x) 2 f) 0 M.zero) := by
    rw [M.sat_cantorFml]
    intro y hyx hy
    rw [IsGraph.img_eq M hf hyx, M.mem_zero.mp hy, M.simg_emp]
    exact M.mem_zero.mpr rfl
  have hs : ∀ k, Sat M.mem M.isSet cantorFml
      (Function.update (Function.update (Function.update (fun _ => dflt) 1 x) 2 f) 0 k) →
      Sat M.mem M.isSet cantorFml
      (Function.update (Function.update (Function.update (fun _ => dflt) 1 x) 2 f) 0
        (M.succ k)) := by
    intro k ih
    rw [M.sat_cantorFml] at ih ⊢
    intro y hyx hy
    obtain ⟨x', b, hx', hb, rfl⟩ := M.mem_succ.mp hy
    have hsub : ∀ e, M.mem e x' → M.mem e x := fun e he => hyx e (M.mem_adj.mpr (Or.inl he))
    have h1 := ih x' hsub hx'
    rw [IsGraph.img_eq M hf hsub] at h1
    rw [IsGraph.img_eq M hf hyx, M.simg_adj]
    refine M.mem_succ.mpr ⟨_, _, h1, ?_, rfl⟩
    intro hc
    obtain ⟨a, ha, e⟩ := M.mem_simg.mp hc
    have hba : b = a := M.sing_inj e
    exact hb (hba ▸ ha)
  have key := M.nat_ind_fml cantorStrat cantorFml 0 rfl _ h0 hs hn
  rw [M.sat_cantorFml] at key
  have := key x (fun _ h => h) hx
  rwa [IsGraph.img_eq M hf (fun _ h => h)] at this

/-! ## The universe and Infinity -/

theorem exists_univ : ∃ u, M.isSet u ∧ ∀ a, M.mem a u := by
  obtain ⟨u, hu, h⟩ := M.comp (fun _ => 0) (.eq 0 0) 0 rfl (fun _ => dflt)
  exact ⟨u, hu, fun a => (h a).mpr (by simp [Sat])⟩

/-- The universe. -/
noncomputable def univ : V := Classical.choose M.exists_univ

theorem univ_isSet : M.isSet M.univ := (Classical.choose_spec M.exists_univ).1

theorem mem_univ (a : V) : M.mem a M.univ := (Classical.choose_spec M.exists_univ).2 a

/-- The axiom of Infinity: the universe belongs to no natural number. -/
def Infinity : Prop := ∀ n, M.mem n M.nat → ¬ M.mem M.univ n

/-- Infinity says that every member of a natural number omits some object. -/
theorem infinity_iff :
    M.Infinity ↔ ∀ n, M.mem n M.nat → ∀ x, M.mem x n → ∃ b, ¬ M.mem b x := by
  constructor
  · intro h n hn x hx
    by_contra hc
    have hall : ∀ b, M.mem b x := fun b => by_contra fun hb => hc ⟨b, hb⟩
    have hxu : x = M.univ := M.ext (M.isSet_of_mem (hall x)) M.univ_isSet fun z =>
      ⟨fun _ => M.mem_univ z, fun _ => hall z⟩
    rw [hxu] at hx
    exact h n hn hx
  · intro h n hn hu
    obtain ⟨b, hb⟩ := h n hn _ hu
    exact hb (M.mem_univ b)

/-! ## Finite sets -/

/-- A finite set: a set that belongs to a natural number. -/
def Fin (x : V) : Prop := M.isSet x ∧ ∃ k, M.mem k M.nat ∧ M.mem x k

/-- `x` is a set in a member of `N`. The bound variable is the name `28`. -/
def fFin (x N : ℕ) : Fml := .and (.set x) (Fml.ex 28 (.and (.mem 28 N) (.mem x 28)))

theorem sat_fFin {x N : ℕ} (hx : x ≠ 28) (hN : N ≠ 28) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fFin x N) ρ ↔ M.isSet (ρ x) ∧ ∃ k, M.mem k (ρ N) ∧ M.mem (ρ x) k := by
  simp only [fFin, Sat, M.sat_ex, Function.update_self, Function.update_of_ne hx,
    Function.update_of_ne hN]

theorem fin_emp : M.Fin M.emp := ⟨M.emp_isSet, M.zero, M.zero_mem_nat, M.mem_zero.mpr rfl⟩

theorem fin_adj {x : V} (b : V) (h : M.Fin x) : M.Fin (M.adj x b) := by
  obtain ⟨hx, k, hk, hxk⟩ := h
  refine ⟨M.adj_isSet x b, ?_⟩
  by_cases hb : M.mem b x
  · have e : M.adj x b = x := M.ext (M.adj_isSet x b) hx fun z =>
      M.mem_adj.trans ⟨fun h => h.elim id (fun e => e ▸ hb), Or.inl⟩
    rw [e]
    exact ⟨k, hk, hxk⟩
  · exact ⟨M.succ k, M.succ_mem_nat hk, M.mem_succ.mpr ⟨x, b, hxk, hb, rfl⟩⟩

theorem fin_sing (a : V) : M.Fin (M.sing a) := by
  have e : M.sing a = M.adj M.emp a := M.ext (M.sing_isSet a) (M.adj_isSet _ _) fun z =>
    M.mem_sing.trans (M.mem_adj.trans
      ⟨fun h => h.elim (fun h => absurd h (M.not_mem_emp z)) id, Or.inr⟩).symm
  rw [e]
  exact M.fin_adj a M.fin_emp

theorem fin_of_mem_nat {n x : V} (hn : M.mem n M.nat) (hx : M.mem x n) : M.Fin x :=
  ⟨M.isSet_of_mem_nat hn hx, n, hn, hx⟩

/-! ### Unions of finite sets -/

theorem exists_un (A B : V) : ∃ U, M.isSet U ∧ ∀ c, M.mem c U ↔ M.mem c A ∨ M.mem c B := by
  obtain ⟨U, hU, h⟩ := M.comp (fun i => if i = 0 then 0 else 1) (Fml.or (.mem 0 1) (.mem 0 2)) 0
    rfl (Function.update (Function.update (fun _ => dflt) 1 A) 2 B)
  refine ⟨U, hU, fun c => ?_⟩
  simpa [M.sat_or, Sat, Function.update_apply] using h c

/-- The union of two sets. -/
noncomputable def un (A B : V) : V := Classical.choose (M.exists_un A B)

theorem un_isSet (A B : V) : M.isSet (M.un A B) := (Classical.choose_spec (M.exists_un A B)).1

theorem mem_un {A B c : V} : M.mem c (M.un A B) ↔ M.mem c A ∨ M.mem c B :=
  (Classical.choose_spec (M.exists_un A B)).2 c

theorem eq_un_iff {U A B : V} :
    (M.isSet U ∧ ∀ c, M.mem c U ↔ M.mem c A ∨ M.mem c B) ↔ U = M.un A B := by
  constructor
  · rintro ⟨hU, h⟩
    exact M.ext hU (M.un_isSet A B) fun z => (h z).trans M.mem_un.symm
  · rintro rfl
    exact ⟨M.un_isSet A B, fun c => M.mem_un⟩

/-- `∀B ∈ l ∀A U (A finite ∧ U = A ∪ B → U finite)`, with `l` the name `0` and `ℕ` the
name `9`. -/
def unFml : Fml :=
  .all 1 (Fml.imp (.mem 1 0) (.all 2 (.all 3 (Fml.imp
    (.and (fFin 2 9) (.and (.set 3) (.all 4 (Fml.iff (.mem 4 3) (Fml.or (.mem 4 2) (.mem 4 1))))))
    (fFin 3 9)))))

def unStrat : ℕ → ℕ := fun i =>
  match i with
  | 0 => 2 | 4 => 0 | 9 => 3 | 28 => 2 | _ => 1

theorem sat_unFml (l : V) :
    Sat M.mem M.isSet unFml (Function.update (Function.update (fun _ => dflt) 9 M.nat) 0 l) ↔
    ∀ B, M.mem B l → ∀ A, M.Fin A → M.Fin (M.un A B) := by
  have h1 : Sat M.mem M.isSet unFml
      (Function.update (Function.update (fun _ => dflt) 9 M.nat) 0 l) ↔
      ∀ B, M.mem B l → ∀ A U, (M.Fin A ∧ M.isSet U ∧
        ∀ c, M.mem c U ↔ M.mem c A ∨ M.mem c B) → M.Fin U := by
    simp only [unFml, Sat, M.sat_imp, M.sat_iff, M.sat_or,
      M.sat_fFin (x := 2) (N := 9) (by decide) (by decide),
      M.sat_fFin (x := 3) (N := 9) (by decide) (by decide), Fin]
    simp [Function.update_apply]
  rw [h1]
  constructor
  · intro h B hB A hA
    exact h B hB A _ ⟨hA, M.un_isSet A B, fun c => M.mem_un⟩
  · rintro h B hB A U ⟨hA, hU, hc⟩
    rw [M.eq_un_iff.mp ⟨hU, hc⟩]
    exact h B hB A hA

/-- The union of two finite sets is finite. -/
theorem fin_un {A B : V} (hA : M.Fin A) (hB : M.Fin B) : M.Fin (M.un A B) := by
  obtain ⟨-, l, hl, hBl⟩ := hB
  have h0 : Sat M.mem M.isSet unFml
      (Function.update (Function.update (fun _ => dflt) 9 M.nat) 0 M.zero) := by
    rw [M.sat_unFml]
    intro B hB A hA
    have e : M.un A B = A := M.ext (M.un_isSet A B) hA.1 fun z => by
      rw [M.mem_un, M.mem_zero.mp hB]
      exact ⟨fun h => h.elim id (fun h => absurd h (M.not_mem_emp z)), Or.inl⟩
    rw [e]
    exact hA
  have hs : ∀ k, Sat M.mem M.isSet unFml
      (Function.update (Function.update (fun _ => dflt) 9 M.nat) 0 k) →
      Sat M.mem M.isSet unFml
      (Function.update (Function.update (fun _ => dflt) 9 M.nat) 0 (M.succ k)) := by
    intro k ih
    rw [M.sat_unFml] at ih ⊢
    intro B hB A hA
    obtain ⟨B', b, hB', -, rfl⟩ := M.mem_succ.mp hB
    have e : M.un A (M.adj B' b) = M.adj (M.un A B') b :=
      M.ext (M.un_isSet _ _) (M.adj_isSet _ _) fun z => by
        simp only [M.mem_un, M.mem_adj]
        tauto
    rw [e]
    exact M.fin_adj b (ih B' hB' A hA)
  have key := M.nat_ind_fml unStrat unFml 0 rfl _ h0 hs hl
  rw [M.sat_unFml] at key
  exact key B hBl A hA

/-! ### The image of a finite set under `z ↦ z ∪ {b}` -/

theorem exists_adjImg (W b : V) : ∃ U, M.isSet U ∧ ∀ c, M.mem c U ↔
    ∃ z, M.mem z W ∧ c = M.adj z b := by
  obtain ⟨U, hU, h⟩ := M.comp (fun i => if i = 1 then 2 else if i = 0 ∨ i = 3 then 1 else 0)
    (Fml.ex 3 (.and (.mem 3 1) (fAdj 0 3 2 4))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 W) 2 b)
  refine ⟨U, hU, fun c => ?_⟩
  rw [h c]
  simp only [M.sat_ex, Sat, M.sat_fAdj (y := 0) (x := 3) (b := 2) (c := 4) (by decide)
    (by decide) (by decide)]
  simp [Function.update_apply]

/-- `{z ∪ {b} : z ∈ W}`. -/
noncomputable def adjImg (W b : V) : V := Classical.choose (M.exists_adjImg W b)

theorem adjImg_isSet (W b : V) : M.isSet (M.adjImg W b) :=
  (Classical.choose_spec (M.exists_adjImg W b)).1

theorem mem_adjImg {W b c : V} : M.mem c (M.adjImg W b) ↔ ∃ z, M.mem z W ∧ c = M.adj z b :=
  (Classical.choose_spec (M.exists_adjImg W b)).2 c

theorem eq_adjImg_iff {U W b : V} :
    (M.isSet U ∧ ∀ c, M.mem c U ↔ ∃ z, M.mem z W ∧ c = M.adj z b) ↔ U = M.adjImg W b := by
  constructor
  · rintro ⟨hU, h⟩
    exact M.ext hU (M.adjImg_isSet W b) fun z => (h z).trans M.mem_adjImg.symm
  · rintro rfl
    exact ⟨M.adjImg_isSet W b, fun c => M.mem_adjImg⟩

theorem adjImg_emp (b : V) : M.adjImg M.emp b = M.emp :=
  M.eq_emp (M.adjImg_isSet _ _) fun c hc => by
    obtain ⟨z, hz, -⟩ := M.mem_adjImg.mp hc
    exact M.not_mem_emp z hz

theorem adjImg_adj (W z b : V) :
    M.adjImg (M.adj W z) b = M.adj (M.adjImg W b) (M.adj z b) := by
  refine M.ext (M.adjImg_isSet _ _) (M.adj_isSet _ _) fun c => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨z', hz', rfl⟩ := M.mem_adjImg.mp h
    rcases M.mem_adj.mp hz' with h | rfl
    · exact M.mem_adj.mpr (Or.inl (M.mem_adjImg.mpr ⟨z', h, rfl⟩))
    · exact M.mem_adj.mpr (Or.inr rfl)
  · rcases M.mem_adj.mp h with h | rfl
    · obtain ⟨z', hz', rfl⟩ := M.mem_adjImg.mp h
      exact M.mem_adjImg.mpr ⟨z', M.mem_adj.mpr (Or.inl hz'), rfl⟩
    · exact M.mem_adjImg.mpr ⟨z, M.mem_adj.mpr (Or.inr rfl), rfl⟩

/-- `∀W ∈ k ∀U (U = {z ∪ {b} : z ∈ W} → U finite)`, with `k`, `b` the names `0`, `6` and `ℕ`
the name `9`. -/
def adjImgFml : Fml :=
  .all 1 (Fml.imp (.mem 1 0) (.all 2 (Fml.imp
    (.and (.set 2) (.all 3 (Fml.iff (.mem 3 2) (Fml.ex 5 (.and (.mem 5 1) (fAdj 3 5 6 7))))))
    (fFin 2 9))))

def adjImgStrat : ℕ → ℕ := fun i =>
  match i with
  | 0 => 3 | 1 => 2 | 2 => 2 | 3 => 1 | 5 => 1 | 9 => 4 | 28 => 3 | _ => 0

theorem sat_adjImgFml (b k : V) :
    Sat M.mem M.isSet adjImgFml (Function.update (Function.update
      (Function.update (fun _ => dflt) 9 M.nat) 6 b) 0 k) ↔
    ∀ W, M.mem W k → M.Fin (M.adjImg W b) := by
  have h1 : Sat M.mem M.isSet adjImgFml (Function.update (Function.update
      (Function.update (fun _ => dflt) 9 M.nat) 6 b) 0 k) ↔
      ∀ W, M.mem W k → ∀ U, (M.isSet U ∧
        ∀ c, M.mem c U ↔ ∃ z, M.mem z W ∧ c = M.adj z b) → M.Fin U := by
    simp only [adjImgFml, Sat, M.sat_imp, M.sat_iff, M.sat_ex,
      M.sat_fAdj (y := 3) (x := 5) (b := 6) (c := 7) (by decide) (by decide) (by decide),
      M.sat_fFin (x := 2) (N := 9) (by decide) (by decide), Fin]
    simp [Function.update_apply]
  rw [h1]
  constructor
  · intro h W hW
    exact h W hW _ ⟨M.adjImg_isSet W b, fun c => M.mem_adjImg⟩
  · rintro h W hW U hU
    rw [M.eq_adjImg_iff.mp hU]
    exact h W hW

theorem fin_adjImg {W : V} (b : V) (hW : M.Fin W) : M.Fin (M.adjImg W b) := by
  obtain ⟨-, k, hk, hWk⟩ := hW
  have h0 : Sat M.mem M.isSet adjImgFml (Function.update (Function.update
      (Function.update (fun _ => dflt) 9 M.nat) 6 b) 0 M.zero) := by
    rw [M.sat_adjImgFml]
    intro W' hW'
    rw [M.mem_zero.mp hW', M.adjImg_emp]
    exact M.fin_emp
  have hs : ∀ k, Sat M.mem M.isSet adjImgFml (Function.update (Function.update
      (Function.update (fun _ => dflt) 9 M.nat) 6 b) 0 k) →
      Sat M.mem M.isSet adjImgFml (Function.update (Function.update
      (Function.update (fun _ => dflt) 9 M.nat) 6 b) 0 (M.succ k)) := by
    intro k ih
    rw [M.sat_adjImgFml] at ih ⊢
    intro W' hW'
    obtain ⟨W'', z, hW'', -, rfl⟩ := M.mem_succ.mp hW'
    rw [M.adjImg_adj]
    exact M.fin_adj _ (ih W'' hW'')
  have key := M.nat_ind_fml adjImgStrat adjImgFml 0 rfl _ h0 hs hk
  rw [M.sat_adjImgFml] at key
  exact key W hWk

/-! ### The power set of a finite set is finite -/

theorem eq_pow_iff {P y : V} :
    (M.isSet P ∧ ∀ z, M.mem z P ↔ M.isSet z ∧ ∀ e, M.mem e z → M.mem e y) ↔ P = M.pow y := by
  constructor
  · rintro ⟨hP, h⟩
    exact M.ext hP (M.pow_isSet y) fun z => (h z).trans M.mem_pow.symm
  · rintro rfl
    exact ⟨M.pow_isSet y, fun z => M.mem_pow⟩

theorem exists_rem (z b : V) : ∃ r, M.isSet r ∧ ∀ e, M.mem e r ↔ M.mem e z ∧ e ≠ b := by
  obtain ⟨r, hr, h⟩ := M.comp (fun i => if i = 1 then 1 else 0)
    (.and (.mem 0 1) (.neg (.eq 0 2))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 z) 2 b)
  refine ⟨r, hr, fun e => ?_⟩
  simpa [Sat, Function.update_apply] using h e

theorem pow_emp : M.pow M.emp = M.sing M.emp := by
  refine M.ext (M.pow_isSet _) (M.sing_isSet _) fun z => ?_
  rw [M.mem_pow, M.mem_sing]
  constructor
  · rintro ⟨hz, h⟩
    exact M.eq_emp hz fun a ha => M.not_mem_emp a (h a ha)
  · intro h
    rw [h]
    exact ⟨M.emp_isSet, fun e he => he⟩

/-- `P(y ∪ {b}) = P(y) ∪ {z ∪ {b} : z ∈ P(y)}`. -/
theorem pow_adj (y b : V) :
    M.pow (M.adj y b) = M.un (M.pow y) (M.adjImg (M.pow y) b) := by
  refine M.ext (M.pow_isSet _) (M.un_isSet _ _) fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨hzs, hz⟩ := M.mem_pow.mp hz
    by_cases hb : M.mem b z
    · refine M.mem_un.mpr (Or.inr (M.mem_adjImg.mpr ?_))
      obtain ⟨r, hr, hre⟩ := M.exists_rem z b
      refine ⟨r, M.mem_pow.mpr ⟨hr, fun e he => ?_⟩, ?_⟩
      · obtain ⟨he1, he2⟩ := (hre e).mp he
        exact (M.mem_adj.mp (hz e he1)).resolve_right he2
      · refine M.ext hzs (M.adj_isSet _ _) fun e => ⟨fun he => ?_, fun he => ?_⟩
        · by_cases heb : e = b
          · exact M.mem_adj.mpr (Or.inr heb)
          · exact M.mem_adj.mpr (Or.inl ((hre e).mpr ⟨he, heb⟩))
        · rcases M.mem_adj.mp he with he | he
          · exact ((hre e).mp he).1
          · rw [he]
            exact hb
    · refine M.mem_un.mpr (Or.inl (M.mem_pow.mpr ⟨hzs, fun e he => ?_⟩))
      refine (M.mem_adj.mp (hz e he)).resolve_right fun heb => hb ?_
      rw [← heb]
      exact he
  · rcases M.mem_un.mp hz with hz | hz
    · obtain ⟨hzs, hz⟩ := M.mem_pow.mp hz
      exact M.mem_pow.mpr ⟨hzs, fun e he => M.mem_adj.mpr (Or.inl (hz e he))⟩
    · obtain ⟨z', hz', rfl⟩ := M.mem_adjImg.mp hz
      obtain ⟨-, hz⟩ := M.mem_pow.mp hz'
      refine M.mem_pow.mpr ⟨M.adj_isSet _ _, fun e he => ?_⟩
      rcases M.mem_adj.mp he with he | he
      · exact M.mem_adj.mpr (Or.inl (hz e he))
      · exact M.mem_adj.mpr (Or.inr he)

/-- `∀y ∈ m ∀P (P = P(y) → P finite)`, with `m` the name `0` and `ℕ` the name `9`. -/
def powFml : Fml :=
  .all 1 (Fml.imp (.mem 1 0) (.all 2 (Fml.imp
    (.and (.set 2) (.all 3 (Fml.iff (.mem 3 2)
      (.and (.set 3) (.all 4 (Fml.imp (.mem 4 3) (.mem 4 1)))))))
    (fFin 2 9))))

def powStrat : ℕ → ℕ := fun i =>
  match i with
  | 0 => 2 | 1 => 1 | 2 => 2 | 3 => 1 | 9 => 4 | 28 => 3 | _ => 0

theorem sat_powFml (m : V) :
    Sat M.mem M.isSet powFml (Function.update (Function.update (fun _ => dflt) 9 M.nat) 0 m) ↔
    ∀ y, M.mem y m → M.Fin (M.pow y) := by
  have h1 : Sat M.mem M.isSet powFml
      (Function.update (Function.update (fun _ => dflt) 9 M.nat) 0 m) ↔
      ∀ y, M.mem y m → ∀ P, (M.isSet P ∧
        ∀ z, M.mem z P ↔ M.isSet z ∧ ∀ e, M.mem e z → M.mem e y) → M.Fin P := by
    simp only [powFml, Sat, M.sat_imp, M.sat_iff,
      M.sat_fFin (x := 2) (N := 9) (by decide) (by decide), Fin]
    simp [Function.update_apply]
  rw [h1]
  constructor
  · intro h y hy
    exact h y hy _ ⟨M.pow_isSet y, fun z => M.mem_pow⟩
  · rintro h y hy P hP
    rw [M.eq_pow_iff.mp hP]
    exact h y hy

/-- **The power set of a finite set is finite.** -/
theorem fin_pow {x : V} (hx : M.Fin x) : M.Fin (M.pow x) := by
  obtain ⟨-, m, hm, hxm⟩ := hx
  have h0 : Sat M.mem M.isSet powFml
      (Function.update (Function.update (fun _ => dflt) 9 M.nat) 0 M.zero) := by
    rw [M.sat_powFml]
    intro y hy
    rw [M.mem_zero.mp hy, M.pow_emp]
    exact M.fin_sing _
  have hs : ∀ k, Sat M.mem M.isSet powFml
      (Function.update (Function.update (fun _ => dflt) 9 M.nat) 0 k) →
      Sat M.mem M.isSet powFml
      (Function.update (Function.update (fun _ => dflt) 9 M.nat) 0 (M.succ k)) := by
    intro k ih
    rw [M.sat_powFml] at ih ⊢
    intro y hy
    obtain ⟨y', b, hy', -, rfl⟩ := M.mem_succ.mp hy
    rw [M.pow_adj]
    exact M.fin_un (ih y' hy') (M.fin_adjImg b (ih y' hy'))
  have key := M.nat_ind_fml powStrat powFml 0 rfl _ h0 hs hm
  rw [M.sat_powFml] at key
  exact key x hxm

/-! ## The cut -/

/-- The cut `𝖲`: the natural numbers with a strongly cantorian member. -/
def InS (n : V) : Prop := M.mem n M.nat ∧ ∃ x, M.mem x n ∧ M.SC x

theorem inS_zero : M.InS M.zero := ⟨M.zero_mem_nat, M.emp, M.mem_zero.mpr rfl, M.sc_emp⟩

/-- With Infinity, the cut is closed under successor. -/
theorem inS_succ (hinf : M.Infinity) {n : V} (h : M.InS n) : M.InS (M.succ n) := by
  obtain ⟨hn, x, hx, hsc⟩ := h
  obtain ⟨b, hb⟩ := M.infinity_iff.mp hinf n hn x hx
  exact ⟨M.succ_mem_nat hn, M.adj x b, M.mem_succ.mpr ⟨x, b, hx, hb, rfl⟩, M.sc_adj hsc⟩

/-- A natural number with a member included in a strongly cantorian set is in the cut. -/
theorem inS_of_subset {m x y : V} (hm : M.mem m M.nat) (hy : M.mem y m) (hx : M.SC x)
    (hyx : ∀ a, M.mem a y → M.mem a x) : M.InS m :=
  ⟨hm, y, hy, M.sc_subset hx hyx⟩

/-- If `x` is a strongly cantorian member of the natural number `n`, the power set of `x`
belongs to a natural number of the cut. -/
theorem inS_pow {n x : V} (hn : M.mem n M.nat) (hx : M.mem x n) (hsc : M.SC x) :
    ∃ m, M.InS m ∧ M.mem (M.pow x) m := by
  obtain ⟨-, m, hm, hpm⟩ := M.fin_pow (M.fin_of_mem_nat hn hx)
  exact ⟨m, ⟨hm, M.pow x, hpm, M.sc_pow hsc⟩, hpm⟩

/-- **The strongly cantorian cut in NFU + Infinity.** The natural numbers with a strongly
cantorian member contain `0` and are closed under successor; and if `x` is a strongly
cantorian member of `n`, then the set of singletons of members of `x` is in `n` (so `T n = n`)
and the power set of `x` is in a natural number `m` of the cut (so `m = 2ⁿ`, by the definition
`2^{|ι"x|} = |P(x)|`). -/
theorem cut (hinf : M.Infinity) :
    M.InS M.zero ∧ (∀ n, M.InS n → M.InS (M.succ n)) ∧
    ∀ n x, M.mem n M.nat → M.mem x n → M.SC x →
      M.mem (M.simg x) n ∧ ∃ m, M.InS m ∧ M.mem (M.pow x) m :=
  ⟨M.inS_zero, fun _ h => M.inS_succ hinf h, fun _ _ hn hx hsc =>
    ⟨M.simg_mem_of_sc hn hx hsc, M.inS_pow hn hx hsc⟩⟩

end Model

/-! ## Shortening a cut (Lemma 2.3 of the note, in abstract form)

This part is about an arbitrary ordered commutative semiring in which every element is
nonnegative, with a monotone function `t` and a function `e` such that `t (n + 1) = e (t n)`.
It is not connected here to the natural numbers of a model of NFU, because addition,
multiplication, `2ˣ` and the tower on those numbers are not constructed in this file. -/

namespace Shortening

variable {N : Type} [CommSemiring N] [PartialOrder N] [IsOrderedRing N] [CanonicallyOrderedAdd N]

/-- `C` is closed downwards and under `e`, and `t` is monotone with `t 0 ∈ C` and
`t (n + 1) = e (t n)`. -/
structure Hyp (C : N → Prop) (t e : N → N) : Prop where
  down : ∀ {a b : N}, a ≤ b → C b → C a
  mono : ∀ {a b : N}, a ≤ b → t a ≤ t b
  step : ∀ n : N, t (n + 1) = e (t n)
  exp : ∀ {a : N}, C a → C (e a)
  base : C (t 0)

/-- `𝖢₂ = {n : t n ∈ 𝖢}`. -/
def C₂ (C : N → Prop) (t : N → N) (n : N) : Prop := C (t n)

/-- `{n : ∀m ∈ 𝖢₂, m + n ∈ 𝖢₂}`, closed under addition. -/
def K₁ (C : N → Prop) (t : N → N) (n : N) : Prop := ∀ m, C₂ C t m → C₂ C t (m + n)

/-- `𝖪 = {n : ∀m ∈ K₁, m · n ∈ K₁}`, closed under addition and multiplication. -/
def K (C : N → Prop) (t : N → N) (n : N) : Prop := ∀ m, K₁ C t m → K₁ C t (m * n)

variable {C : N → Prop} {t e : N → N}

theorem C₂_down (h : Hyp C t e) {a b : N} (hab : a ≤ b) (hb : C₂ C t b) : C₂ C t a :=
  h.down (h.mono hab) hb

theorem C₂_zero (h : Hyp C t e) : C₂ C t 0 := h.base

theorem C₂_succ (h : Hyp C t e) {n : N} (hn : C₂ C t n) : C₂ C t (n + 1) := by
  unfold C₂
  rw [h.step]
  exact h.exp hn

theorem K₁_zero : K₁ C t 0 := fun m hm => by rwa [add_zero]

theorem K₁_one (h : Hyp C t e) : K₁ C t 1 := fun _ hm => C₂_succ h hm

theorem K₁_add {a b : N} (ha : K₁ C t a) (hb : K₁ C t b) : K₁ C t (a + b) := fun m hm => by
  rw [← add_assoc]
  exact hb _ (ha m hm)

theorem K₁_down (h : Hyp C t e) {a b : N} (hab : a ≤ b) (hb : K₁ C t b) : K₁ C t a :=
  fun m hm => C₂_down h (add_le_add le_rfl hab) (hb m hm)

theorem K₁_sub (h : Hyp C t e) {n : N} (hn : K₁ C t n) : C₂ C t n := by
  have := hn 0 (C₂_zero h)
  rwa [zero_add] at this

theorem K_zero : K C t 0 := fun m _ => by
  rw [mul_zero]
  exact K₁_zero

theorem K_one : K C t 1 := fun m hm => by rwa [mul_one]

theorem K_add {a b : N} (ha : K C t a) (hb : K C t b) : K C t (a + b) := fun m hm => by
  rw [mul_add]
  exact K₁_add (ha m hm) (hb m hm)

theorem K_mul {a b : N} (ha : K C t a) (hb : K C t b) : K C t (a * b) := fun m hm => by
  rw [← mul_assoc]
  exact hb _ (ha m hm)

theorem K_down (h : Hyp C t e) {a b : N} (hab : a ≤ b) (hb : K C t b) : K C t a :=
  fun m hm => K₁_down h (mul_le_mul_of_nonneg_left hab zero_le) (hb m hm)

theorem K_sub (h : Hyp C t e) {n : N} (hn : K C t n) : C₂ C t n := by
  have := hn 1 (K₁_one h)
  rw [one_mul] at this
  exact K₁_sub h this

/-- **Tower absorption.** For `n ∈ 𝖪` and standard `c`, `d`, `j`, applying `e` to
`t (c · n + d)` `j` times gives an element of `𝖢`. -/
theorem absorb (h : Hyp C t e) {n : N} (hn : K C t n) (c d j : ℕ) :
    C (e^[j] (t ((c : N) * n + (d : N)))) := by
  have hnat : ∀ k : ℕ, K C t (k : N) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero]
      exact K_zero
    | succ k ih =>
      rw [Nat.cast_succ]
      exact K_add ih K_one
  have h1 : K C t ((c : N) * n + (d : N)) := K_add (K_mul (hnat c) hn) (hnat d)
  have h2 : C (t ((c : N) * n + (d : N))) := K_sub h h1
  induction j with
  | zero => exact h2
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact h.exp ih

end Shortening

end NFUCut
