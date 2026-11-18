module

public import ConNF.NF.NFUSat

/-!
# Soundness for coded derivations (§3.1 of the note, second half)

This file continues `NFUSat`. It works in an arbitrary model `M` of NFU + Infinity.

Formulas are the codes of `NFUSat` (numbers of the model, standard or not), and a sequent is a
pair `G`, `D` of sets of the model whose members are codes.

* `arith_comp`, `arith_lfp`: comprehension and least fixed points for sets of numbers defined
  by arithmetical formulas (`AF`) with one set parameter.
* `Sub x y φ ψ`: `ψ` is the result of replacing the free occurrences of the variable `x` in
  `φ` by `y`, with no capture; an arithmetical least fixed point (`subSet`).
* `substitution`: truth and falsity of `ψ` at `s` agree with those of `φ` at `s` with `x`
  sent to the value of `y`.
* `coincide`: changing an assignment at a variable greater than the code `m` changes neither
  the truth nor the falsity of `m`.
* `Der n G D`: the sequent `G ⊢ D` has a cut-free derivation of size `n`; the set of these
  facts (`derSet`) is the least set closed under the rules `der_ax`, `der_negL`, `der_negR`,
  `der_andL`, `der_andR`, `der_allL`, `der_allR`. The eigenvariable of `der_allR` has to be
  greater than every code in the sequent.
* `soundness`: if `G ⊢ D` is derivable then in every set structure, at every assignment at
  which all members of `G` are true, some member of `D` is not false.
  `no_model_of_refutation` is the case `D = ∅`.

The calculus has no cut rule; that it derives the same sequents as a calculus with cut is not
proved here.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

@[expose] public section

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

/-! ## More on assignments -/

theorem updS_updS_same (s i a b : V) : M.updS (M.updS s i a) i b = M.updS s i b := by
  refine M.ext (M.updS_isSet _ _ _) (M.updS_isSet _ _ _) fun p => ?_
  simp only [M.mem_updS]
  constructor
  · rintro (⟨h | h, hn⟩ | h)
    · exact Or.inl ⟨h.1, hn⟩
    · exact absurd ⟨a, h⟩ hn
    · exact Or.inr h
  · rintro (⟨h, hn⟩ | h)
    · exact Or.inl ⟨Or.inl ⟨h, hn⟩, hn⟩
    · exact Or.inr h

theorem updS_comm {i j : V} (hij : i ≠ j) (s a b : V) :
    M.updS (M.updS s i a) j b = M.updS (M.updS s j b) i a := by
  refine M.ext (M.updS_isSet _ _ _) (M.updS_isSet _ _ _) fun p => ?_
  simp only [M.mem_updS]
  constructor
  · rintro (⟨⟨h, hni⟩ | h, hnj⟩ | h)
    · exact Or.inl ⟨Or.inl ⟨h, hnj⟩, hni⟩
    · exact Or.inr h
    · exact Or.inl ⟨Or.inr h, fun ⟨c, hc⟩ => hij ((M.op_inj (h.symm.trans hc)).1.symm)⟩
  · rintro (⟨⟨h, hnj⟩ | h, hni⟩ | h)
    · exact Or.inl ⟨Or.inl ⟨h, hni⟩, hnj⟩
    · exact Or.inr h
    · exact Or.inl ⟨Or.inr h, fun ⟨c, hc⟩ => hij ((M.op_inj (h.symm.trans hc)).1)⟩

theorem updS_self {U s i b : V} (hs : M.IsAsg U s) (hi : M.mem i M.nat)
    (h : M.mem (M.op i b) s) : M.updS s i b = s := by
  refine M.ext (M.updS_isSet _ _ _) hs.1 fun p => ?_
  rw [M.mem_updS]
  constructor
  · rintro (⟨h1, -⟩ | h1)
    · exact h1
    · rw [h1]
      exact h
  · intro hp
    by_cases hc : ∃ c, p = M.op i c
    · obtain ⟨c, hc⟩ := hc
      rw [hc] at hp
      obtain ⟨a, ha, hu⟩ := hs.2.2.1 i hi
      have e1 := hu c hp
      have e2 := hu b h
      right
      rw [hc, e1, e2]
    · exact Or.inl ⟨hp, hc⟩

/-! ## Arithmetical formulas with a set parameter

Formulas of arithmetic in relational form with one more atomic formula, `x ∈ Y`, for a set
`Y` of the model. They are stratified, so they define sets of numbers, and a condition that
is monotone in `Y` has a least fixed point. This is used for relations between coded
formulas, such as substitution. -/

/-- Formulas of arithmetic with a set parameter. -/
inductive AF : Type
  | eq (x y : ℕ) : AF
  | add (x y z : ℕ) : AF
  | mul (x y z : ℕ) : AF
  | inY (x : ℕ) : AF
  | neg (φ : AF) : AF
  | and (φ ψ : AF) : AF
  | all (x : ℕ) (φ : AF) : AF

namespace AF

def or (φ ψ : AF) : AF := neg (and (neg φ) (neg ψ))

def ex (x : ℕ) (φ : AF) : AF := neg (all x (neg φ))

end AF

/-- Truth of a formula of arithmetic with the set parameter `Y`. -/
def holdsA (Y : V) : AF → (ℕ → M.Num) → Prop
  | .eq x y, e => e x = e y
  | .add x y z, e => e x + e y = e z
  | .mul x y z, e => e x * e y = e z
  | .inY x, e => M.mem (e x).1 Y
  | .neg φ, e => ¬ holdsA Y φ e
  | .and φ ψ, e => holdsA Y φ e ∧ holdsA Y ψ e
  | .all x φ, e => ∀ a : M.Num, holdsA Y φ (Function.update e x a)

theorem holdsA_or {Y : V} {φ ψ : AF} {e : ℕ → M.Num} :
    M.holdsA Y (φ.or ψ) e ↔ M.holdsA Y φ e ∨ M.holdsA Y ψ e := by
  simp only [AF.or, holdsA]
  tauto

theorem holdsA_ex {Y : V} {x : ℕ} {φ : AF} {e : ℕ → M.Num} :
    M.holdsA Y (φ.ex x) e ↔ ∃ a : M.Num, M.holdsA Y φ (Function.update e x a) := by
  simp only [AF.ex, holdsA]
  exact not_forall_not

/-- The translation: the variable `i` becomes the name `i + 100`; the names `2`, `3`, `4`,
`8` stand for `ℕ`, the graphs of `+` and `·`, and the set parameter. -/
def trF : AF → Fml
  | .eq x y => .eq (x + 100) (y + 100)
  | .add x y z => fApp3 3 (x + 100) (y + 100) (z + 100)
  | .mul x y z => fApp3 4 (x + 100) (y + 100) (z + 100)
  | .inY x => .mem (x + 100) 8
  | .neg φ => .neg (trF φ)
  | .and φ ψ => .and (trF φ) (trF ψ)
  | .all x φ => .all (x + 100) (Fml.imp (.mem (x + 100) 2) (trF φ))

def σF : ℕ → ℕ := fun i => if 100 ≤ i then 2 else σW [(2, 3), (3, 7), (4, 7), (8, 3)] i

theorem strat_trF (φ : AF) : (trF φ).strat σF = true := by
  have hv : ∀ x, σF (x + 100) = 2 := fun x => by simp [σF]
  induction φ with
  | eq x y => simp [trF, Fml.strat, hv]
  | add x y z =>
    simp [trF, fApp3, fTrip, fOp, fSing, fUp, Fml.ex, Fml.iff, Fml.imp, Fml.or, Fml.strat, hv,
      show σF 3 = 7 from rfl, show σF 39 = 6 from rfl, show σF 32 = 4 from rfl,
      show σF 33 = 4 from rfl, show σF 34 = 5 from rfl, show σF 35 = 4 from rfl,
      show σF 36 = 3 from rfl, show σF 37 = 2 from rfl]
  | mul x y z =>
    simp [trF, fApp3, fTrip, fOp, fSing, fUp, Fml.ex, Fml.iff, Fml.imp, Fml.or, Fml.strat, hv,
      show σF 4 = 7 from rfl, show σF 39 = 6 from rfl, show σF 32 = 4 from rfl,
      show σF 33 = 4 from rfl, show σF 34 = 5 from rfl, show σF 35 = 4 from rfl,
      show σF 36 = 3 from rfl, show σF 37 = 2 from rfl]
  | inY x => simp [trF, Fml.strat, hv, show σF 8 = 3 from rfl]
  | neg φ ih => simpa [trF, Fml.strat] using ih
  | and φ ψ ih1 ih2 => simp [trF, Fml.strat, ih1, ih2]
  | all x φ ih => simp [trF, Fml.imp, Fml.strat, ih, hv, show σF 2 = 3 from rfl]

/-- The assignment `ρ` of the model represents the assignment `e` of numbers. -/
def RepF (ad mu : V) (ρ : ℕ → V) (e : ℕ → M.Num) : Prop :=
  ρ 2 = M.nat ∧ ρ 3 = ad ∧ ρ 4 = mu ∧ ∀ i, ρ (i + 100) = (e i).1

theorem repF_update {ad mu : V} {ρ : ℕ → V} {e : ℕ → M.Num} (h : M.RepF ad mu ρ e) (x : ℕ)
    (a : M.Num) : M.RepF ad mu (Function.update ρ (x + 100) a.1) (Function.update e x a) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, fun i => ?_⟩
  · rw [Function.update_of_ne (by omega)]
    exact h1
  · rw [Function.update_of_ne (by omega)]
    exact h2
  · rw [Function.update_of_ne (by omega)]
    exact h3
  · by_cases hi : i = x
    · rw [hi, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne hi]
      exact h4 i

theorem repF_update_low {ad mu : V} {ρ : ℕ → V} {e : ℕ → M.Num} (h : M.RepF ad mu ρ e) {i : ℕ}
    (h2 : i ≠ 2) (h3 : i ≠ 3) (h4 : i ≠ 4) (hi : i < 100) (v : V) :
    M.RepF ad mu (Function.update ρ i v) e := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  refine ⟨?_, ?_, ?_, fun j => ?_⟩
  · rw [Function.update_of_ne (Ne.symm h2)]
    exact a1
  · rw [Function.update_of_ne (Ne.symm h3)]
    exact a2
  · rw [Function.update_of_ne (Ne.symm h4)]
    exact a3
  · rw [Function.update_of_ne (by omega)]
    exact a4 j

theorem sat_trF {ad mu : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN) :
    ∀ (φ : AF) (ρ : ℕ → V) (e : ℕ → M.Num), M.RepF ad mu ρ e →
      (Sat M.mem M.isSet (trF φ) ρ ↔ M.holdsA (ρ 8) φ e) := by
  intro φ
  induction φ with
  | eq x y =>
    intro ρ e h
    simp only [trF, Sat, holdsA, h.2.2.2 x, h.2.2.2 y]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  | add x y z =>
    intro ρ e h
    rw [trF, M.sat_fApp3 ρ (by decide) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)), h.2.2.2 x, h.2.2.2 y, h.2.2.2 z, h.2.1]
    simp only [holdsA]
    constructor
    · intro hm
      exact Subtype.ext (M.graph₂_val had hm).symm
    · intro he
      have h3 := M.graph₂_app had (e x) (e y)
      rw [show M.addN (e x) (e y) = e z from he] at h3
      exact h3
  | mul x y z =>
    intro ρ e h
    rw [trF, M.sat_fApp3 ρ (by decide) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)), h.2.2.2 x, h.2.2.2 y, h.2.2.2 z, h.2.2.1]
    simp only [holdsA]
    constructor
    · intro hm
      exact Subtype.ext (M.graph₂_val hmu hm).symm
    · intro he
      have h3 := M.graph₂_app hmu (e x) (e y)
      rw [show M.mulN (e x) (e y) = e z from he] at h3
      exact h3
  | inY x =>
    intro ρ e h
    simp only [trF, Sat, holdsA, h.2.2.2 x]
  | neg φ ih =>
    intro ρ e h
    simp only [trF, Sat, holdsA, ih ρ e h]
  | and φ ψ ih1 ih2 =>
    intro ρ e h
    simp only [trF, Sat, holdsA, ih1 ρ e h, ih2 ρ e h]
  | all x φ ih =>
    intro ρ e h
    have hx2 : (2 : ℕ) ≠ x + 100 := by omega
    have hx8 : (8 : ℕ) ≠ x + 100 := by omega
    simp only [trF, Sat, M.sat_imp, holdsA, Function.update_self, Function.update_of_ne hx2, h.1]
    constructor
    · intro hall a
      have h1 := (ih _ _ (M.repF_update h x a)).mp (hall a.1 a.2)
      rwa [Function.update_of_ne hx8] at h1
    · intro hall a ha
      refine (ih _ _ (M.repF_update h x ⟨a, ha⟩)).mpr ?_
      rw [Function.update_of_ne hx8]
      exact hall ⟨a, ha⟩

theorem exists_repF (ad mu : V) (e : ℕ → M.Num) : ∃ ρ : ℕ → V, M.RepF ad mu ρ e :=
  ⟨fun i => if 100 ≤ i then (e (i - 100)).1 else if i = 2 then M.nat else if i = 3 then ad
    else mu, by simp [RepF]⟩

/-- **Arithmetical comprehension with a set parameter.** -/
theorem arith_comp (φ : AF) (Y : V) (e : ℕ → M.Num) :
    ∃ S, ∀ v, M.mem v S ↔ ∃ q : M.Num, q.1 = v ∧ M.holdsA Y φ (Function.update e 0 q) := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  obtain ⟨mu, hmu⟩ := M.mulN_natOp
  obtain ⟨ρ0, hρ0⟩ := M.exists_repF ad mu e
  have hρ : M.RepF ad mu (Function.update ρ0 8 Y) e :=
    M.repF_update_low hρ0 (by decide) (by decide) (by decide) (by decide) Y
  obtain ⟨S, -, hS⟩ := M.comp σF (.and (.mem 100 2) (trF φ)) 100
    (by simp [Fml.strat, strat_trF, show σF 2 = 3 from rfl, show σF 100 = 2 from rfl])
    (Function.update ρ0 8 Y)
  refine ⟨S, fun v => ?_⟩
  rw [hS v]
  simp only [Sat, Function.update_self, Function.update_of_ne (show (2 : ℕ) ≠ 100 by decide),
    hρ.1]
  constructor
  · rintro ⟨hv, h⟩
    refine ⟨⟨v, hv⟩, rfl, ?_⟩
    have h1 := (M.sat_trF had hmu φ _ _ (M.repF_update hρ 0 ⟨v, hv⟩)).mp h
    rwa [Function.update_of_ne (show (8 : ℕ) ≠ 0 + 100 by decide), Function.update_self] at h1
  · rintro ⟨q, hq, h⟩
    rw [← hq]
    refine ⟨q.2, (M.sat_trF had hmu φ _ _ (M.repF_update hρ 0 q)).mpr ?_⟩
    rwa [Function.update_of_ne (show (8 : ℕ) ≠ 0 + 100 by decide), Function.update_self]

/-- **Least fixed points of monotone arithmetical conditions.** -/
theorem arith_lfp (φ : AF) (e : ℕ → M.Num)
    (hmono : ∀ Y Y' : V, (∀ p, M.mem p Y → M.mem p Y') → ∀ q : M.Num,
      M.holdsA Y φ (Function.update e 0 q) → M.holdsA Y' φ (Function.update e 0 q)) :
    ∃ L, (∀ q : M.Num, M.holdsA L φ (Function.update e 0 q) → M.mem q.1 L) ∧
      (∀ Y, (∀ q : M.Num, M.holdsA Y φ (Function.update e 0 q) → M.mem q.1 Y) →
        ∀ p, M.mem p L → M.mem p Y) ∧
      ∀ p, M.mem p L → M.mem p M.nat := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  obtain ⟨mu, hmu⟩ := M.mulN_natOp
  obtain ⟨ρ, hρ⟩ := M.exists_repF ad mu e
  obtain ⟨L, -, hL0⟩ := M.comp σF
    (.all 8 (Fml.imp (.all 100 (Fml.imp (.mem 100 2) (Fml.imp (trF φ) (.mem 100 8))))
      (.mem 0 8))) 0
    (by simp [Fml.strat, Fml.imp, strat_trF, show σF 2 = 3 from rfl, show σF 100 = 2 from rfl,
      show σF 8 = 3 from rfl, show σF 0 = 2 from rfl]) ρ
  have hL : ∀ p, M.mem p L ↔ ∀ Y, (∀ q : M.Num, M.holdsA Y φ (Function.update e 0 q) →
      M.mem q.1 Y) → M.mem p Y := by
    intro p
    rw [hL0 p]
    simp only [Sat, M.sat_imp, Function.update_self,
      Function.update_of_ne (show (2 : ℕ) ≠ 100 by decide),
      Function.update_of_ne (show (2 : ℕ) ≠ 8 by decide),
      Function.update_of_ne (show (2 : ℕ) ≠ 0 by decide),
      Function.update_of_ne (show (8 : ℕ) ≠ 100 by decide),
      Function.update_of_ne (show (0 : ℕ) ≠ 8 by decide), hρ.1]
    have hrep : ∀ (Y : V) (q : M.Num), M.RepF ad mu (Function.update (Function.update
        (Function.update ρ 0 p) 8 Y) (0 + 100) q.1) (Function.update e 0 q) := fun Y q =>
      M.repF_update (M.repF_update_low (M.repF_update_low hρ (by decide) (by decide) (by decide)
        (by decide) p) (by decide) (by decide) (by decide) (by decide) Y) 0 q
    constructor
    · intro h Y hY
      refine h Y fun a ha hsat => ?_
      have h1 := (M.sat_trF had hmu φ _ _ (hrep Y ⟨a, ha⟩)).mp hsat
      rw [Function.update_of_ne (show (8 : ℕ) ≠ 0 + 100 by decide), Function.update_self] at h1
      exact hY ⟨a, ha⟩ h1
    · intro h Y hY
      refine h Y fun q hq => ?_
      refine hY q.1 q.2 ((M.sat_trF had hmu φ _ _ (hrep Y q)).mpr ?_)
      rw [Function.update_of_ne (show (8 : ℕ) ≠ 0 + 100 by decide), Function.update_self]
      exact hq
  refine ⟨L, fun q hq => ?_, fun Y hY p hp => (hL p).mp hp Y hY, fun p hp => ?_⟩
  · exact (hL q.1).mpr fun Y hY => hY q (hmono L Y (fun p hp => (hL p).mp hp Y hY) q hq)
  · exact (hL p).mp hp M.nat fun q _ => q.2

/-- `c = pairN x y`. Bound variables `200`, `201`. -/
def aPair (c x y : ℕ) : AF :=
  AF.ex 200 (AF.ex 201 (.and (.add x y 200) (.and (.mul 200 200 201) (.add 201 x c))))

theorem holdsA_aPair {Y : V} {c x y : ℕ} (e : ℕ → M.Num) (hc : c < 200) (hx : x < 200)
    (hy : y < 200) : M.holdsA Y (aPair c x y) e ↔ e c = M.pairN (e x) (e y) := by
  have c0 : c ≠ 200 := by omega
  have c1 : c ≠ 201 := by omega
  have x0 : x ≠ 200 := by omega
  have x1 : x ≠ 201 := by omega
  have y0 : y ≠ 200 := by omega
  have y1 : y ≠ 201 := by omega
  simp only [aPair, M.holdsA_ex, holdsA, Function.update_self, Function.update_of_ne c0,
    Function.update_of_ne c1, Function.update_of_ne x0, Function.update_of_ne x1,
    Function.update_of_ne y0, Function.update_of_ne y1,
    Function.update_of_ne (show (200 : ℕ) ≠ 201 by decide)]
  constructor
  · rintro ⟨u, v, h1, h2, h3⟩
    rw [← h3, ← h2, ← h1]
    rfl
  · intro h
    exact ⟨_, _, rfl, rfl, h.symm⟩

/-! ## Substitution of a variable for a variable in a coded formula

`Sub x y φ ψ` says that `ψ` is `φ` with the free occurrences of the variable `x` replaced by
`y`, no bound variable of `φ` being `x` or `y` below a quantifier that is crossed. It is the
least relation closed under five clauses, and it is a set of the model because the clauses
are arithmetical. -/

/-- The number coding the fact `Sub x y φ ψ`. -/
noncomputable def sq (x y φ ψ : M.Num) : M.Num := M.pairN (M.pairN x y) (M.pairN φ ψ)

def subC1 : AF :=
  AF.ex 14 (AF.ex 15 (AF.ex 16 (AF.ex 17 (AF.ex 18 (AF.ex 19 (AF.ex 20 (AF.ex 21 (AF.ex 22
    (.and (aPair 19 15 16) (.and (aPair 20 14 19) (.and (aPair 3 10 20) (.and (aPair 21 17 18)
    (.and (aPair 22 14 21) (.and (aPair 4 10 22)
    (.and (AF.or (.and (.eq 15 1) (.eq 17 2)) (.and (.neg (.eq 15 1)) (.eq 17 15)))
      (AF.or (.and (.eq 16 1) (.eq 18 2)) (.and (.neg (.eq 16 1)) (.eq 18 16))))))))))))))))))

def SubC1 (z0 x y φ ψ : M.Num) : Prop :=
  ∃ r v w v' w' a1 a2 b1 b2 : M.Num, a1 = M.pairN v w ∧ a2 = M.pairN r a1 ∧ φ = M.pairN z0 a2 ∧
    b1 = M.pairN v' w' ∧ b2 = M.pairN r b1 ∧ ψ = M.pairN z0 b2 ∧
    ((v = x ∧ v' = y) ∨ (¬ v = x ∧ v' = v)) ∧ ((w = x ∧ w' = y) ∨ (¬ w = x ∧ w' = w))

theorem holdsA_subC1 {Y : V} (e : ℕ → M.Num) :
    M.holdsA Y subC1 e ↔ M.SubC1 (e 10) (e 1) (e 2) (e 3) (e 4) := by
  simp [subC1, SubC1, M.holdsA_ex, M.holdsA_or, holdsA, M.holdsA_aPair, Function.update_apply]

def subC2 : AF :=
  AF.ex 14 (AF.ex 15 (AF.ex 19 (AF.ex 20 (.and (aPair 3 11 14) (.and (aPair 4 11 15)
    (.and (aPair 19 14 15) (.and (aPair 20 5 19) (.inY 20))))))))

def SubC2 (Y : V) (z1 p1 φ ψ : M.Num) : Prop :=
  ∃ φ1 ψ1 a1 a2 : M.Num, φ = M.pairN z1 φ1 ∧ ψ = M.pairN z1 ψ1 ∧ a1 = M.pairN φ1 ψ1 ∧
    a2 = M.pairN p1 a1 ∧ M.mem a2.1 Y

theorem holdsA_subC2 {Y : V} (e : ℕ → M.Num) :
    M.holdsA Y subC2 e ↔ M.SubC2 Y (e 11) (e 5) (e 3) (e 4) := by
  simp [subC2, SubC2, M.holdsA_ex, holdsA, M.holdsA_aPair, Function.update_apply]

def subC3 : AF :=
  AF.ex 14 (AF.ex 15 (AF.ex 16 (AF.ex 17 (AF.ex 19 (AF.ex 20 (AF.ex 21 (AF.ex 22 (AF.ex 23
    (AF.ex 24 (.and (aPair 19 14 15) (.and (aPair 3 12 19) (.and (aPair 20 16 17)
    (.and (aPair 4 12 20) (.and (aPair 21 14 16) (.and (aPair 22 5 21) (.and (.inY 22)
    (.and (aPair 23 15 17) (.and (aPair 24 5 23) (.inY 24)))))))))))))))))))

def SubC3 (Y : V) (z2 p1 φ ψ : M.Num) : Prop :=
  ∃ φ1 φ2 ψ1 ψ2 a b c1 c2 d1 d2 : M.Num, a = M.pairN φ1 φ2 ∧ φ = M.pairN z2 a ∧
    b = M.pairN ψ1 ψ2 ∧ ψ = M.pairN z2 b ∧ c1 = M.pairN φ1 ψ1 ∧ c2 = M.pairN p1 c1 ∧
    M.mem c2.1 Y ∧ d1 = M.pairN φ2 ψ2 ∧ d2 = M.pairN p1 d1 ∧ M.mem d2.1 Y

theorem holdsA_subC3 {Y : V} (e : ℕ → M.Num) :
    M.holdsA Y subC3 e ↔ M.SubC3 Y (e 12) (e 5) (e 3) (e 4) := by
  simp [subC3, SubC3, M.holdsA_ex, holdsA, M.holdsA_aPair, Function.update_apply]

def subC4 : AF :=
  AF.ex 14 (AF.ex 15 (AF.ex 16 (AF.ex 19 (.and (aPair 1 14 15) (.and (aPair 19 1 16)
    (.and (aPair 3 13 19) (.eq 4 3)))))))

def SubC4 (z3 x φ ψ : M.Num) : Prop :=
  ∃ t n φ1 a : M.Num, x = M.pairN t n ∧ a = M.pairN x φ1 ∧ φ = M.pairN z3 a ∧ ψ = φ

theorem holdsA_subC4 {Y : V} (e : ℕ → M.Num) :
    M.holdsA Y subC4 e ↔ M.SubC4 (e 13) (e 1) (e 3) (e 4) := by
  simp [subC4, SubC4, M.holdsA_ex, holdsA, M.holdsA_aPair, Function.update_apply]

def subC5 : AF :=
  AF.ex 14 (AF.ex 15 (AF.ex 16 (AF.ex 17 (AF.ex 18 (AF.ex 19 (AF.ex 20 (AF.ex 21 (AF.ex 22
    (.and (aPair 16 14 15) (.and (aPair 19 16 17) (.and (aPair 3 13 19) (.and (aPair 20 16 18)
    (.and (aPair 4 13 20) (.and (.neg (.eq 16 1)) (.and (.neg (.eq 16 2))
    (.and (aPair 21 17 18) (.and (aPair 22 5 21) (.inY 22))))))))))))))))))

def SubC5 (Y : V) (z3 x y p1 φ ψ : M.Num) : Prop :=
  ∃ t n z φ1 ψ1 a b c1 c2 : M.Num, z = M.pairN t n ∧ a = M.pairN z φ1 ∧ φ = M.pairN z3 a ∧
    b = M.pairN z ψ1 ∧ ψ = M.pairN z3 b ∧ ¬ z = x ∧ ¬ z = y ∧ c1 = M.pairN φ1 ψ1 ∧
    c2 = M.pairN p1 c1 ∧ M.mem c2.1 Y

theorem holdsA_subC5 {Y : V} (e : ℕ → M.Num) :
    M.holdsA Y subC5 e ↔ M.SubC5 Y (e 13) (e 1) (e 2) (e 5) (e 3) (e 4) := by
  simp [subC5, SubC5, M.holdsA_ex, holdsA, M.holdsA_aPair, Function.update_apply]

def subAF : AF :=
  AF.ex 1 (AF.ex 2 (AF.ex 3 (AF.ex 4 (AF.ex 5 (AF.ex 6 (.and (aPair 5 1 2) (.and (aPair 6 3 4)
    (.and (aPair 0 5 6) (AF.or subC1 (AF.or subC2 (AF.or subC3 (AF.or subC4 subC5))))))))))))

/-- One step of the definition of substitution, for the set `Y` of facts. -/
def SubStepM (Y : V) (z0 z1 z2 z3 q : M.Num) : Prop :=
  ∃ x y φ ψ p1 p2 : M.Num, p1 = M.pairN x y ∧ p2 = M.pairN φ ψ ∧ q = M.pairN p1 p2 ∧
    (M.SubC1 z0 x y φ ψ ∨ M.SubC2 Y z1 p1 φ ψ ∨ M.SubC3 Y z2 p1 φ ψ ∨ M.SubC4 z3 x φ ψ ∨
      M.SubC5 Y z3 x y p1 φ ψ)

theorem holdsA_subAF {Y : V} (e : ℕ → M.Num) :
    M.holdsA Y subAF e ↔ M.SubStepM Y (e 10) (e 11) (e 12) (e 13) (e 0) := by
  simp [subAF, SubStepM, M.holdsA_ex, M.holdsA_or, holdsA, M.holdsA_aPair, M.holdsA_subC1,
    M.holdsA_subC2, M.holdsA_subC3, M.holdsA_subC4, M.holdsA_subC5, Function.update_apply]

theorem subStepM_mono {Y Y' : V} (hY : ∀ p, M.mem p Y → M.mem p Y') {z0 z1 z2 z3 q : M.Num}
    (h : M.SubStepM Y z0 z1 z2 z3 q) : M.SubStepM Y' z0 z1 z2 z3 q := by
  obtain ⟨x, y, φ, ψ, p1, p2, h1, h2, h3, hC⟩ := h
  refine ⟨x, y, φ, ψ, p1, p2, h1, h2, h3, ?_⟩
  rcases hC with h | h | h | h | h
  · exact Or.inl h
  · obtain ⟨φ1, ψ1, a1, a2, e1, e2, e3, e4, hm⟩ := h
    exact Or.inr (Or.inl ⟨φ1, ψ1, a1, a2, e1, e2, e3, e4, hY _ hm⟩)
  · obtain ⟨φ1, φ2, ψ1, ψ2, a, b, c1, c2, d1, d2, e1, e2, e3, e4, e5, e6, hm1, e7, e8, hm2⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨φ1, φ2, ψ1, ψ2, a, b, c1, c2, d1, d2, e1, e2, e3, e4, e5, e6,
      hY _ hm1, e7, e8, hY _ hm2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · obtain ⟨t, n, z, φ1, ψ1, a, b, c1, c2, e1, e2, e3, e4, e5, e6, e7, e8, e9, hm⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, n, z, φ1, ψ1, a, b, c1, c2, e1, e2, e3, e4, e5, e6,
      e7, e8, e9, hY _ hm⟩)))

/-- The numbers `0`, `1`, `2`, `3` at the variables `10`–`13`. -/
noncomputable def tagEnv : ℕ → M.Num := fun i =>
  if i = 11 then 1 else if i = 12 then 2 else if i = 13 then 3 else 0

theorem holdsA_subAF_tag {Y : V} (q : M.Num) :
    M.holdsA Y subAF (Function.update M.tagEnv 0 q) ↔ M.SubStepM Y 0 1 2 3 q := by
  rw [M.holdsA_subAF]
  simp [tagEnv, Function.update_apply]

theorem exists_subSet : ∃ L, (∀ q : M.Num, M.SubStepM L 0 1 2 3 q → M.mem q.1 L) ∧
    (∀ Y, (∀ q : M.Num, M.SubStepM Y 0 1 2 3 q → M.mem q.1 Y) → ∀ p, M.mem p L → M.mem p Y) := by
  obtain ⟨L, h1, h2, -⟩ := M.arith_lfp subAF M.tagEnv (fun Y Y' hY q hq =>
    (M.holdsA_subAF_tag q).mpr (M.subStepM_mono hY ((M.holdsA_subAF_tag q).mp hq)))
  exact ⟨L, fun q hq => h1 q ((M.holdsA_subAF_tag q).mpr hq),
    fun Y hY => h2 Y fun q hq => hY q ((M.holdsA_subAF_tag q).mp hq)⟩

/-- The substitution relation, a set of the model. -/
noncomputable def subSet : V := Classical.choose M.exists_subSet

/-- `ψ` is `φ` with `y` substituted for `x`. -/
def Sub (x y φ ψ : M.Num) : Prop := M.mem (M.sq x y φ ψ).1 M.subSet

theorem subSet_closed {q : M.Num} (h : M.SubStepM M.subSet 0 1 2 3 q) : M.mem q.1 M.subSet :=
  (Classical.choose_spec M.exists_subSet).1 q h

theorem subSet_least {Y : V} (hY : ∀ q : M.Num, M.SubStepM Y 0 1 2 3 q → M.mem q.1 Y) {p : V}
    (hp : M.mem p M.subSet) : M.mem p Y := (Classical.choose_spec M.exists_subSet).2 Y hY p hp

/-- The clauses of substitution. -/
theorem sub_rel (x y r v w v' w' : M.Num) (hv : (v = x ∧ v' = y) ∨ (¬ v = x ∧ v' = v))
    (hw : (w = x ∧ w' = y) ∨ (¬ w = x ∧ w' = w)) :
    M.Sub x y (M.cRel r v w) (M.cRel r v' w') :=
  M.subSet_closed ⟨x, y, _, _, _, _, rfl, rfl, rfl,
    Or.inl ⟨r, v, w, v', w', _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, hv, hw⟩⟩

theorem sub_neg {x y φ ψ : M.Num} (h : M.Sub x y φ ψ) : M.Sub x y (M.cNeg φ) (M.cNeg ψ) :=
  M.subSet_closed ⟨x, y, _, _, _, _, rfl, rfl, rfl,
    Or.inr (Or.inl ⟨φ, ψ, _, _, rfl, rfl, rfl, rfl, h⟩)⟩

theorem sub_and {x y φ1 φ2 ψ1 ψ2 : M.Num} (h1 : M.Sub x y φ1 ψ1) (h2 : M.Sub x y φ2 ψ2) :
    M.Sub x y (M.cAnd φ1 φ2) (M.cAnd ψ1 ψ2) :=
  M.subSet_closed ⟨x, y, _, _, _, _, rfl, rfl, rfl,
    Or.inr (Or.inr (Or.inl ⟨φ1, φ2, ψ1, ψ2, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, h1,
      rfl, rfl, h2⟩))⟩

theorem sub_all_same (t n y φ : M.Num) :
    M.Sub (M.vr t n) y (M.cAll (M.vr t n) φ) (M.cAll (M.vr t n) φ) :=
  M.subSet_closed ⟨M.vr t n, y, _, _, _, _, rfl, rfl, rfl,
    Or.inr (Or.inr (Or.inr (Or.inl ⟨t, n, φ, _, rfl, rfl, rfl, rfl⟩)))⟩

theorem sub_all {x y φ ψ : M.Num} (t n : M.Num) (hx : ¬ M.vr t n = x) (hy : ¬ M.vr t n = y)
    (h : M.Sub x y φ ψ) : M.Sub x y (M.cAll (M.vr t n) φ) (M.cAll (M.vr t n) ψ) :=
  M.subSet_closed ⟨x, y, _, _, _, _, rfl, rfl, rfl,
    Or.inr (Or.inr (Or.inr (Or.inr ⟨t, n, _, φ, ψ, _, _, _, _, rfl, rfl, rfl, rfl, rfl, hx, hy,
      rfl, rfl, h⟩)))⟩

/-! ### The substitution lemma -/

/-- The fact coded by `q` satisfies the substitution lemma in the structure `(U, E)`. -/
def GoodSub (U E : V) (q : M.Num) : Prop :=
  ∀ x y φ ψ : M.Num, q = M.sq x y φ ψ → ∀ s b, M.IsAsg U s → M.IsAsg U (M.updS s x.1 b) →
    M.mem (M.op y.1 b) s →
    (M.Holds U E ψ s ↔ M.Holds U E φ (M.updS s x.1 b)) ∧
    (M.Fails U E ψ s ↔ M.Fails U E φ (M.updS s x.1 b))

def subGoodFml : Fml :=
  .all 21 (.all 22 (.all 23 (.all 24 (.all 25 (.all 26 (Fml.imp
    (.and (fPairN 25 21 22) (.and (fPairN 26 23 24) (fPairN 0 25 26)))
    (.all 20 (.all 17 (.all 27 (Fml.imp
      (.and (.mem 20 5) (.and (fUpd 27 20 21 17) (.and (.mem 27 5) (fApp 20 22 17))))
      (.and (Fml.iff (fLit 8 24 11 20) (fLit 8 23 11 27))
        (Fml.iff (fLit 8 24 10 20) (fLit 8 23 10 27)))))))))))))

def σG : ℕ → ℕ :=
  σW [(5, 6), (7, 7), (18, 7), (8, 8), (20, 5), (27, 5), (110, 7), (111, 3), (112, 4), (113, 5),
    (115, 3), (116, 4), (117, 6), (118, 5), (119, 4)]

theorem exists_goodSub (U E : V) : ∃ G, ∀ q : M.Num, M.mem q.1 G ↔ M.GoodSub U E q := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  obtain ⟨mu, hmu⟩ := M.mulN_natOp
  obtain ⟨G, -, hG⟩ := M.comp σG subGoodFml 0 rfl (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (fun _ => dflt)
    5 (M.asg U)) 7 ad) 18 mu) 8 (M.satSet U E)) 10 (0 : M.Num).1) 11 (1 : M.Num).1)
  have hG' : ∀ q, M.mem q G ↔ ∀ x y φ ψ p1 p2,
      (M.PairRaw ad mu x y p1 ∧ M.PairRaw ad mu φ ψ p2 ∧ M.PairRaw ad mu p1 p2 q) →
      ∀ s b s', (M.mem s (M.asg U) ∧ s' = M.updS s x b ∧ M.mem s' (M.asg U) ∧
        M.mem (M.op y b) s) →
      (M.LitRaw ad mu (M.satSet U E) ψ (1 : M.Num).1 s ↔
        M.LitRaw ad mu (M.satSet U E) φ (1 : M.Num).1 s') ∧
      (M.LitRaw ad mu (M.satSet U E) ψ (0 : M.Num).1 s ↔
        M.LitRaw ad mu (M.satSet U E) φ (0 : M.Num).1 s') := by
    intro q
    rw [hG q]
    simp [subGoodFml, Sat, M.sat_imp, M.sat_iff, M.sat_fPairN, M.sat_fUpd, M.sat_fApp,
      M.sat_fLit, Function.update_apply]
  refine ⟨G, fun q => ?_⟩
  rw [hG']
  constructor
  · intro h x y φ ψ hq s b hs hs' hyb
    have h1 := h x.1 y.1 φ.1 ψ.1 (M.pairN x y).1 (M.pairN φ ψ).1
      ⟨(M.pairRaw_iff had hmu _ _ _).mpr ⟨x, y, rfl, rfl, rfl⟩,
        (M.pairRaw_iff had hmu _ _ _).mpr ⟨φ, ψ, rfl, rfl, rfl⟩,
        (M.pairRaw_iff had hmu _ _ _).mpr ⟨M.pairN x y, M.pairN φ ψ, rfl, rfl, by rw [hq]; rfl⟩⟩
      s b _ ⟨M.mem_asg.mpr hs, rfl, M.mem_asg.mpr hs', hyb⟩
    simp only [M.litRaw_iff had hmu] at h1
    exact h1
  · rintro h x y φ ψ p1 p2 ⟨h1, h2, h3⟩ s b s' ⟨hs, hs'e, hs', hyb⟩
    obtain ⟨X, Y, hX, hY, hp1⟩ := (M.pairRaw_iff had hmu _ _ _).mp h1
    obtain ⟨P, Q, hP, hQ, hp2⟩ := (M.pairRaw_iff had hmu _ _ _).mp h2
    obtain ⟨P1, P2, hP1, hP2, hq⟩ := (M.pairRaw_iff had hmu _ _ _).mp h3
    have e1 : P1 = M.pairN X Y := Subtype.ext (hP1.trans hp1)
    have e2 : P2 = M.pairN P Q := Subtype.ext (hP2.trans hp2)
    have eq : q = M.sq X Y P Q := Subtype.ext (by rw [hq, e1, e2]; rfl)
    rw [hs'e] at hs' ⊢
    rw [← hX] at hs' ⊢
    rw [← hY] at hyb
    rw [← hP, ← hQ]
    simp only [M.litRaw_iff had hmu]
    exact h X Y P Q eq s b (M.mem_asg.mp hs) (M.mem_asg.mp hs') hyb

/-- The value of a variable after substitution. -/
theorem val_sub {U s b : V} (hs : M.IsAsg U s) {x y u u' : M.Num} (hyb : M.mem (M.op y.1 b) s)
    (h : (u = x ∧ u' = y) ∨ (¬ u = x ∧ u' = u)) (a : V) :
    M.mem (M.op u'.1 a) s ↔ M.mem (M.op u.1 a) (M.updS s x.1 b) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, M.mem_updS_same]
    constructor
    · intro ha
      obtain ⟨a0, -, hu⟩ := hs.2.2.1 y.1 y.2
      rw [hu a ha, hu b hyb]
    · intro ha
      rw [ha]
      exact hyb
  · rw [h2]
    exact (M.mem_updS_of_ne (fun e => h1 (Subtype.ext e))).symm

theorem goodSub_closed (U E : V) {G : V} (hG : ∀ q : M.Num, M.mem q.1 G ↔ M.GoodSub U E q)
    (q : M.Num) (h : M.SubStepM G 0 1 2 3 q) : M.mem q.1 G := by
  rw [hG]
  obtain ⟨x, y, φ, ψ, p1, p2, hp1, hp2, hq, hC⟩ := h
  intro x' y' φ' ψ' hq' s b hs hs' hyb
  rw [hq, hp1, hp2] at hq'
  obtain ⟨e1, e2⟩ := M.pairN_inj hq'
  obtain ⟨e3, e4⟩ := M.pairN_inj e1
  obtain ⟨e5, e6⟩ := M.pairN_inj e2
  rw [← e3] at hs' ⊢
  rw [← e4] at hyb
  rw [← e5, ← e6]
  rcases hC with h | h | h | h | h
  · obtain ⟨r, v, w, v', w', a1, a2, b1, b2, ha1, ha2, hφ, hb1, hb2, hψ, hv, hw⟩ := h
    have eφ : φ = M.cRel r v w := by rw [hφ, ha2, ha1]; rfl
    have eψ : ψ = M.cRel r v' w' := by rw [hψ, hb2, hb1]; rfl
    rw [eφ, eψ, M.holds_rel, M.holds_rel, M.fails_rel, M.fails_rel]
    have hR : M.RelH E r v' w' s ↔ M.RelH E r v w (M.updS s x.1 b) := by
      simp only [RelH, M.val_sub hs hyb hv, M.val_sub hs hyb hw]
    rw [hR]
    exact ⟨⟨fun h => ⟨hs', h.2⟩, fun h => ⟨hs, h.2⟩⟩, ⟨fun h => ⟨hs', h.2⟩, fun h => ⟨hs, h.2⟩⟩⟩
  · obtain ⟨φ1, ψ1, a1, a2, hφ, hψ, ha1, ha2, hm⟩ := h
    have ih := (hG a2).mp hm x y φ1 ψ1 (by rw [ha2, ha1, hp1]; rfl) s b hs hs' hyb
    have eφ : φ = M.cNeg φ1 := hφ
    have eψ : ψ = M.cNeg ψ1 := hψ
    rw [eφ, eψ, M.holds_neg, M.holds_neg, M.fails_neg, M.fails_neg, ih.1, ih.2]
    exact ⟨⟨fun h => ⟨hs', h.2⟩, fun h => ⟨hs, h.2⟩⟩, ⟨fun h => ⟨hs', h.2⟩, fun h => ⟨hs, h.2⟩⟩⟩
  · obtain ⟨φ1, φ2, ψ1, ψ2, a, b', c1, c2, d1, d2, ha, hφ, hb, hψ, hc1, hc2, hm1, hd1, hd2, hm2⟩ := h
    have ih1 := (hG c2).mp hm1 x y φ1 ψ1 (by rw [hc2, hc1, hp1]; rfl) s b hs hs' hyb
    have ih2 := (hG d2).mp hm2 x y φ2 ψ2 (by rw [hd2, hd1, hp1]; rfl) s b hs hs' hyb
    have eφ : φ = M.cAnd φ1 φ2 := by rw [hφ, ha]; rfl
    have eψ : ψ = M.cAnd ψ1 ψ2 := by rw [hψ, hb]; rfl
    rw [eφ, eψ, M.holds_and, M.holds_and, M.fails_and, M.fails_and, ih1.1, ih1.2, ih2.1, ih2.2]
    exact ⟨⟨fun h => ⟨hs', h.2⟩, fun h => ⟨hs, h.2⟩⟩, ⟨fun h => ⟨hs', h.2⟩, fun h => ⟨hs, h.2⟩⟩⟩
  · obtain ⟨t, n, φ1, a, hx, ha, hφ, hψ⟩ := h
    have eφ : φ = M.cAll (M.vr t n) φ1 := by rw [hφ, ha, hx]; rfl
    have ex : x = M.vr t n := hx
    rw [hψ, eφ, ex, M.holds_all, M.holds_all, M.fails_all, M.fails_all]
    rw [ex] at hs'
    simp only [M.updS_updS_same]
    exact ⟨⟨fun h => ⟨hs', h.2⟩, fun h => ⟨hs, h.2⟩⟩, ⟨fun h => ⟨hs', h.2⟩, fun h => ⟨hs, h.2⟩⟩⟩
  · obtain ⟨t, n, z, φ1, ψ1, a, b', c1, c2, hz, ha, hφ, hb, hψ, hzx, hzy, hc1, hc2, hm⟩ := h
    have eφ : φ = M.cAll (M.vr t n) φ1 := by rw [hφ, ha, hz]; rfl
    have eψ : ψ = M.cAll (M.vr t n) ψ1 := by rw [hψ, hb, hz]; rfl
    have hzx' : (M.vr t n).1 ≠ x.1 := fun e => hzx (hz.trans (Subtype.ext e))
    have hzy' : y.1 ≠ (M.vr t n).1 := fun e => hzy (hz.trans (Subtype.ext e.symm))
    have key : ∀ a', M.mem (M.op t.1 a') U →
        (M.Holds U E ψ1 (M.updS s (M.vr t n).1 a') ↔
          M.Holds U E φ1 (M.updS (M.updS s x.1 b) (M.vr t n).1 a')) ∧
        (M.Fails U E ψ1 (M.updS s (M.vr t n).1 a') ↔
          M.Fails U E φ1 (M.updS (M.updS s x.1 b) (M.vr t n).1 a')) := by
      intro a' ha'
      have hsa : M.IsAsg U (M.updS s (M.vr t n).1 a') := M.isAsg_updS hs t n ha'
      have hsa' : M.IsAsg U (M.updS (M.updS s x.1 b) (M.vr t n).1 a') :=
        M.isAsg_updS hs' t n ha'
      rw [M.updS_comm hzx'.symm s b a'] at hsa' ⊢
      exact (hG c2).mp hm x y φ1 ψ1 (by rw [hc2, hc1, hp1]; rfl) _ b hsa hsa'
        ((M.mem_updS_of_ne hzy').mpr hyb)
    rw [eφ, eψ, M.holds_all, M.holds_all, M.fails_all, M.fails_all]
    refine ⟨⟨fun h => ⟨hs', fun a' ha' => (key a' ha').1.mp (h.2 a' ha')⟩,
      fun h => ⟨hs, fun a' ha' => (key a' ha').1.mpr (h.2 a' ha')⟩⟩, ⟨?_, ?_⟩⟩
    · rintro ⟨-, h1, a', ha', h2⟩
      exact ⟨hs', fun a'' ha'' => (h1 a'' ha'').imp (key a'' ha'').1.mp (key a'' ha'').2.mp,
        a', ha', (key a' ha').2.mp h2⟩
    · rintro ⟨-, h1, a', ha', h2⟩
      exact ⟨hs, fun a'' ha'' => (h1 a'' ha'').imp (key a'' ha'').1.mpr (key a'' ha'').2.mpr,
        a', ha', (key a' ha').2.mpr h2⟩

/-- **The substitution lemma.** If `ψ` is `φ` with `y` for `x`, then `ψ` is true (false) at
`s` if and only if `φ` is true (false) at `s` with `x` given the value of `y`. -/
theorem substitution {U E : V} {x y φ ψ : M.Num} (h : M.Sub x y φ ψ) {s b : V}
    (hs : M.IsAsg U s) (hs' : M.IsAsg U (M.updS s x.1 b)) (hyb : M.mem (M.op y.1 b) s) :
    (M.Holds U E ψ s ↔ M.Holds U E φ (M.updS s x.1 b)) ∧
    (M.Fails U E ψ s ↔ M.Fails U E φ (M.updS s x.1 b)) := by
  obtain ⟨G, hG⟩ := M.exists_goodSub U E
  have h1 : M.mem (M.sq x y φ ψ).1 G := M.subSet_least (M.goodSub_closed U E hG) h
  exact (hG _).mp h1 x y φ ψ rfl s b hs hs' hyb

/-! ## Coincidence: a variable greater than a code does not matter to it

The parts of a code are smaller numbers, so a variable which, as a number, is greater than a
code does not occur in it. This is the form in which the eigenvariable condition is used. -/

theorem val_ne_of_lt {a b : M.Num} (h : a + 1 ≤ b) : a.1 ≠ b.1 := fun e => by
  have e' : a = b := Subtype.ext e
  rw [e'] at h
  exact M.not_succ_le b h

theorem coin_core {U E : V} (t n m : M.Num) (hm : m + 1 ≤ M.vr t n)
    (ih : ∀ m' : M.Num, m' + 1 ≤ m → ∀ s a, M.IsAsg U s → M.mem (M.op t.1 a) U →
      (M.Holds U E m' s → M.Holds U E m' (M.updS s (M.vr t n).1 a)) ∧
      (M.Fails U E m' s → M.Fails U E m' (M.updS s (M.vr t n).1 a)))
    (s a : V) (hs : M.IsAsg U s) (ha : M.mem (M.op t.1 a) U) :
    (M.Holds U E m s → M.Holds U E m (M.updS s (M.vr t n).1 a)) ∧
    (M.Fails U E m s → M.Fails U E m (M.updS s (M.vr t n).1 a)) := by
  have hs' : M.IsAsg U (M.updS s (M.vr t n).1 a) := M.isAsg_updS hs t n ha
  -- the common part: the shape of `m` and the transfer for its parts
  have part : ∀ k x : M.Num, m = M.pairN k x → ∀ b : M.Num,
      M.Body U E (M.satSet U E) b k x s → M.Body U E (M.satSet U E) b k x (M.updS s (M.vr t n).1 a) := by
    intro k x hmk b hB
    have hxm : x ≤ m := by
      rw [hmk]
      exact M.le_pairN_right k x
    have hlt : ∀ {u : M.Num}, u ≤ x → 1 ≤ k → u + 1 ≤ m := by
      intro u hu hk
      rw [hmk]
      exact le_trans (add_le_add hu (le_refl 1)) (M.lt_pairN_right x hk)
    have hne : ∀ {u : M.Num}, u ≤ x → u.1 ≠ (M.vr t n).1 := fun hu =>
      M.val_ne_of_lt (le_trans (add_le_add (le_trans hu hxm) (le_refl 1)) hm)
    rcases hB with ⟨hk, hB⟩ | ⟨hk, hB⟩ | ⟨hk, hB⟩ | ⟨hk, hB⟩
    · refine Or.inl ⟨hk, ?_⟩
      obtain ⟨r, v, w, e, h⟩ := hB
      have hv : v.1 ≠ (M.vr t n).1 := hne (by
        rw [e]
        exact le_trans (M.le_pairN_left v w) (M.le_pairN_right r _))
      have hw : w.1 ≠ (M.vr t n).1 := hne (by
        rw [e]
        exact le_trans (M.le_pairN_right v w) (M.le_pairN_right r _))
      have hR : M.RelH E r v w s ↔ M.RelH E r v w (M.updS s (M.vr t n).1 a) := by
        simp only [RelH, M.mem_updS_of_ne hv, M.mem_updS_of_ne hw]
      refine ⟨r, v, w, e, ?_⟩
      rw [← hR]
      exact h
    · refine Or.inr (Or.inl ⟨hk, ?_⟩)
      have h1 : (1 : M.Num) ≤ k := by rw [hk]
      have ihx := ih x (hlt (le_refl x) h1) s a hs ha
      exact hB.imp (fun h => ⟨h.1, ihx.2 h.2⟩) (fun h => ⟨h.1, ihx.1 h.2⟩)
    · refine Or.inr (Or.inr (Or.inl ⟨hk, ?_⟩))
      have h1 : (1 : M.Num) ≤ k := by
        rw [hk]
        exact one_le_two
      obtain ⟨φ, ψ, e, h⟩ := hB
      have ihφ := ih φ (hlt (by rw [e]; exact M.le_pairN_left φ ψ) h1) s a hs ha
      have ihψ := ih ψ (hlt (by rw [e]; exact M.le_pairN_right φ ψ) h1) s a hs ha
      refine ⟨φ, ψ, e, ?_⟩
      rcases h with ⟨hb, h1, h2⟩ | ⟨hb, h⟩
      · exact Or.inl ⟨hb, ihφ.1 h1, ihψ.1 h2⟩
      · refine Or.inr ⟨hb, ?_⟩
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨ihφ.2 h1, h2.imp ihψ.1 ihψ.2⟩
        · exact Or.inr ⟨h1.imp ihφ.1 ihφ.2, ihψ.2 h2⟩
    · refine Or.inr (Or.inr (Or.inr ⟨hk, ?_⟩))
      have h1 : (1 : M.Num) ≤ k := by
        rw [hk]
        exact M.le_def.mpr ⟨2, by norm_num⟩
      obtain ⟨t', n', φ, e, h⟩ := hB
      have hvne : (M.pairN t' n').1 ≠ (M.vr t n).1 := hne (by
        rw [e]
        exact M.le_pairN_left _ φ)
      have tr3 : ∀ a', M.mem (M.op t'.1 a') U →
          (M.Holds U E φ (M.updS s (M.pairN t' n').1 a') →
            M.Holds U E φ (M.updS (M.updS s (M.vr t n).1 a) (M.pairN t' n').1 a')) ∧
          (M.Fails U E φ (M.updS s (M.pairN t' n').1 a') →
            M.Fails U E φ (M.updS (M.updS s (M.vr t n).1 a) (M.pairN t' n').1 a')) := by
        intro a' ha'
        have h3 := ih φ (hlt (by rw [e]; exact M.le_pairN_right _ φ) h1) _ a
          (M.isAsg_updS hs t' n' ha') ha
        rwa [M.updS_comm hvne] at h3
      refine ⟨t', n', φ, e, ?_⟩
      rcases h with ⟨hb, h⟩ | ⟨hb, h, a', ha', h2⟩
      · exact Or.inl ⟨hb, fun a' ha' => (tr3 a' ha').1 (h a' ha')⟩
      · exact Or.inr ⟨hb, fun a'' ha'' => (h a'' ha'').imp (tr3 a'' ha'').1 (tr3 a'' ha'').2,
          a', ha', (tr3 a' ha').2 h2⟩
  constructor
  · intro hT
    obtain ⟨k, x, hmk⟩ := M.code_of_holds hT
    rw [hmk] at hT ⊢
    exact (M.holds_iff U E k x _).mpr ⟨hs', part k x hmk 1 ((M.holds_iff U E k x s).mp hT).2⟩
  · intro hF
    obtain ⟨b, k, x, s', e, -, -⟩ := M.satSet_inv hF
    have hmk : m = M.pairN k x := (M.pairN_inj (Subtype.ext (M.fact_inj e).1)).1
    rw [hmk] at hF ⊢
    exact (M.fails_iff U E k x _).mpr ⟨hs', part k x hmk 0 ((M.fails_iff U E k x s).mp hF).2⟩

def coinFml : Fml :=
  .all 21 (Fml.imp (fLe 21 0) (Fml.imp (Fml.ex 22 (.and (fSuccEq 22 21) (fLe 22 3)))
    (.all 20 (Fml.imp (.mem 20 5) (.all 25 (Fml.imp (fApp 1 4 25) (.all 27 (Fml.imp
      (fUpd 27 20 3 25) (.and (Fml.imp (fLit 8 21 11 20) (fLit 8 21 11 27))
        (Fml.imp (fLit 8 21 10 20) (fLit 8 21 10 27)))))))))))

def σK : ℕ → ℕ :=
  σW [(1, 5), (5, 6), (6, 3), (7, 7), (18, 7), (8, 8), (20, 5), (27, 5), (110, 7), (111, 3),
    (112, 4), (113, 5), (115, 3), (116, 4), (117, 6), (118, 5), (119, 4)]

/-- The parameters for `coinFml`. -/
noncomputable def coinEnv (ad mu U E : V) (y t : M.Num) : ℕ → V :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (fun _ => dflt) 1 U) 3 y.1) 4 t.1) 5 (M.asg U)) 6 M.nat) 7 ad) 18 mu) 8 (M.satSet U E))
    10 (0 : M.Num).1) 11 (1 : M.Num).1

theorem sat_coinFml {ad mu : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN)
    (U E : V) (y t c : M.Num) :
    Sat M.mem M.isSet coinFml (Function.update (M.coinEnv ad mu U E y t) 0 c.1) ↔
    ∀ m : M.Num, m ≤ c → m + 1 ≤ y → ∀ s a, M.IsAsg U s → M.mem (M.op t.1 a) U →
      (M.Holds U E m s → M.Holds U E m (M.updS s y.1 a)) ∧
      (M.Fails U E m s → M.Fails U E m (M.updS s y.1 a)) := by
  have h1 : Sat M.mem M.isSet coinFml (Function.update (M.coinEnv ad mu U E y t) 0 c.1) ↔
      ∀ m, M.LeRaw ad m c.1 → (∃ sm, sm = M.succ m ∧ M.LeRaw ad sm y.1) →
      ∀ s, M.mem s (M.asg U) → ∀ a, M.mem (M.op t.1 a) U → ∀ s', s' = M.updS s y.1 a →
        (M.LitRaw ad mu (M.satSet U E) m (1 : M.Num).1 s →
          M.LitRaw ad mu (M.satSet U E) m (1 : M.Num).1 s') ∧
        (M.LitRaw ad mu (M.satSet U E) m (0 : M.Num).1 s →
          M.LitRaw ad mu (M.satSet U E) m (0 : M.Num).1 s') := by
    simp [coinFml, coinEnv, fLe, LeRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fApp, M.sat_fApp3,
      M.sat_fSuccEq, M.sat_fUpd, M.sat_fLit, Function.update_apply]
  rw [h1]
  constructor
  · intro h m hmc hmy s a hs ha
    have h2 := h m.1 ((M.leRaw_iff had m c).mpr hmc)
      ⟨(M.nsucc m).1, rfl, (M.leRaw_iff had (M.nsucc m) y).mpr (by
        rw [M.nsucc_eq_add_one]
        exact hmy)⟩ s (M.mem_asg.mpr hs) a ha _ rfl
    simp only [M.litRaw_iff had hmu] at h2
    exact h2
  · rintro h m ⟨d, hd, hmd⟩ ⟨sm, hsm, hsmy⟩ s hs a ha s' hs'
    obtain ⟨M', D', hM', hD', hc⟩ := (had _ _ _).mp hmd
    have hle : M' ≤ c := M.le_def.mpr ⟨D', Subtype.ext hc⟩
    rw [hsm, ← hM'] at hsmy
    have hlt : M' + 1 ≤ y := by
      rw [← M.nsucc_eq_add_one]
      exact (M.leRaw_iff had (M.nsucc M') y).mp hsmy
    rw [hs', ← hM']
    simp only [M.litRaw_iff had hmu]
    exact h M' hle hlt s a (M.mem_asg.mp hs) ha

theorem coincide_imp {U E : V} (t n m : M.Num) (hm : m + 1 ≤ M.vr t n) (s a : V)
    (hs : M.IsAsg U s) (ha : M.mem (M.op t.1 a) U) :
    (M.Holds U E m s → M.Holds U E m (M.updS s (M.vr t n).1 a)) ∧
    (M.Fails U E m s → M.Fails U E m (M.updS s (M.vr t n).1 a)) := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  obtain ⟨mu, hmu⟩ := M.mulN_natOp
  have key := M.num_ind_fml σK coinFml 0 rfl (M.coinEnv ad mu U E (M.vr t n) t)
    ((M.sat_coinFml had hmu U E (M.vr t n) t 0).mpr (fun m' hm' hm'y s' a' hs' ha' =>
      M.coin_core t n m' hm'y (fun m'' hm'' =>
        absurd (le_trans hm'' hm') (fun h => M.succ_not_le_zero h)) s' a' hs' ha'))
    (fun k ih => (M.sat_coinFml had hmu U E (M.vr t n) t (M.nsucc k)).mpr
      (fun m' hm' hm'y s' a' hs' ha' =>
        M.coin_core t n m' hm'y (fun m'' hm'' => by
          rw [M.nsucc_eq_add_one] at hm'
          exact (M.sat_coinFml had hmu U E (M.vr t n) t k).mp ih m''
            (M.le_of_succ_le_succ (le_trans hm'' hm'))
            (le_trans hm'' (le_trans (M.le_add_one m') hm'y))) s' a' hs' ha')) m
  exact (M.sat_coinFml had hmu U E (M.vr t n) t m).mp key m (le_refl m) hm s a hs ha

/-- **Coincidence.** If the code `m` is smaller than the variable `vr t n`, then changing the
value of that variable does not change the truth or the falsity of `m`. -/
theorem coincide {U E : V} {t n m : M.Num} (hm : m + 1 ≤ M.vr t n) {s a : V}
    (hs : M.IsAsg U s) (ha : M.mem (M.op t.1 a) U) :
    (M.Holds U E m s ↔ M.Holds U E m (M.updS s (M.vr t n).1 a)) ∧
    (M.Fails U E m s ↔ M.Fails U E m (M.updS s (M.vr t n).1 a)) := by
  have hfw := M.coincide_imp (U := U) (E := E) t n m hm s a hs ha
  obtain ⟨b, hb, -⟩ := hs.2.2.1 (M.vr t n).1 (M.vr t n).2
  have hbU : M.mem (M.op t.1 b) U := hs.2.2.2 t n b hb
  have hbw := M.coincide_imp (U := U) (E := E) t n m hm (M.updS s (M.vr t n).1 a) b
    (M.isAsg_updS hs t n ha) hbU
  have e : M.updS (M.updS s (M.vr t n).1 a) (M.vr t n).1 b = s := by
    rw [M.updS_updS_same]
    exact M.updS_self hs (M.vr t n).2 hb
  rw [e] at hbw
  exact ⟨⟨hfw.1, hbw.1⟩, ⟨hfw.2, hbw.2⟩⟩

/-! ## Coded derivations

A sequent is a pair of sets of the model whose members are codes of formulas. The fact
"`G ⊢ D` has a cut-free derivation of size `n`" is the triple of `{n}`, `G`, `D`, and the set
of these facts is the least set closed under the rules. -/

/-- The graph of `+` chosen once and for all. -/
noncomputable def adG : V := Classical.choose M.addN_natOp

theorem adG_spec : M.IsGraphOf₂ M.adG M.addN := Classical.choose_spec M.addN_natOp

/-- The graph of `·` chosen once and for all. -/
noncomputable def muG : V := Classical.choose M.mulN_natOp

theorem muG_spec : M.IsGraphOf₂ M.muG M.mulN := Classical.choose_spec M.mulN_natOp

theorem natFn_pairN {F G : M.Num → M.Num} (hF : M.NatFn F) (hG : M.NatFn G) :
    M.NatFn (fun n => M.pairN (F n) (G n)) := by
  simp only [M.pairN_eq]
  exact M.fnAdd (M.fnMul (M.fnAdd hF hG) (M.fnAdd hF hG)) hF

/-- The graph of negation on codes. -/
noncomputable def negG : V := Classical.choose (M.natFn_pairN (M.natFn_const 1) M.natFn_id)

theorem negG_spec : M.IsGraphOf M.negG M.cNeg :=
  Classical.choose_spec (M.natFn_pairN (M.natFn_const 1) M.natFn_id)

/-- The graph of `p ↦ pairN 2 p`, the second step of forming a conjunction. -/
noncomputable def andG : V := Classical.choose (M.natFn_pairN (M.natFn_const 2) M.natFn_id)

theorem andG_spec : M.IsGraphOf M.andG (fun p => M.pairN 2 p) :=
  Classical.choose_spec (M.natFn_pairN (M.natFn_const 2) M.natFn_id)

/-! ### Instances of a universal formula -/

def alliAF : AF :=
  AF.ex 1 (AF.ex 2 (AF.ex 3 (AF.ex 4 (AF.ex 5 (AF.ex 6 (AF.ex 7 (AF.ex 8 (AF.ex 9 (AF.ex 14
    (AF.ex 15 (AF.ex 16 (AF.ex 17 (.and (aPair 14 2 3) (.and (aPair 0 1 14) (.and (aPair 8 4 5)
    (.and (aPair 9 8 7) (.and (aPair 1 13 9) (.and (aPair 2 4 6) (.and (aPair 15 8 2)
    (.and (aPair 16 7 3) (.and (aPair 17 15 16) (.inY 17))))))))))))))))))))))

def AlliM (Y : V) (z3 q : M.Num) : Prop :=
  ∃ c y ψ t n1 n2 φ x a p s1 s2 s : M.Num, p = M.pairN y ψ ∧ q = M.pairN c p ∧
    x = M.pairN t n1 ∧ a = M.pairN x φ ∧ c = M.pairN z3 a ∧ y = M.pairN t n2 ∧
    s1 = M.pairN x y ∧ s2 = M.pairN φ ψ ∧ s = M.pairN s1 s2 ∧ M.mem s.1 Y

theorem holdsA_alliAF {Y : V} (e : ℕ → M.Num) :
    M.holdsA Y alliAF e ↔ M.AlliM Y (e 13) (e 0) := by
  simp (config := { decide := true }) only [alliAF, AlliM, M.holdsA_ex, holdsA, M.holdsA_aPair,
    Function.update_apply, ↓reduceIte]

theorem exists_alliSet : ∃ S, ∀ v, M.mem v S ↔ ∃ q : M.Num, q.1 = v ∧ M.AlliM M.subSet 3 q := by
  obtain ⟨S, hS⟩ := M.arith_comp alliAF M.subSet M.tagEnv
  refine ⟨S, fun v => ?_⟩
  rw [hS v]
  refine exists_congr fun q => and_congr Iff.rfl ?_
  rw [M.holdsA_alliAF]
  simp [tagEnv, Function.update_apply]

/-- The set of codes of triples `(∀x φ, y, φ[y/x])` with `x`, `y` variables of one sort. -/
noncomputable def alliSet : V := Classical.choose M.exists_alliSet

theorem mem_alliSet (c y ψ : M.Num) : M.mem (M.pairN c (M.pairN y ψ)).1 M.alliSet ↔
    ∃ t n1 n2 φ : M.Num, c = M.cAll (M.vr t n1) φ ∧ y = M.vr t n2 ∧
      M.Sub (M.vr t n1) y φ ψ := by
  refine (Classical.choose_spec M.exists_alliSet _).trans ?_
  constructor
  · rintro ⟨q, hq, c', y', ψ', t, n1, n2, φ, x, a, p, s1, s2, s, hp, hq', hx, ha, hc, hy, hs1,
      hs2, hs, hm⟩
    have e0 : M.pairN c' p = M.pairN c (M.pairN y ψ) := hq'.symm.trans (Subtype.ext hq)
    obtain ⟨e1, e2⟩ := M.pairN_inj e0
    rw [hp] at e2
    obtain ⟨e3, e4⟩ := M.pairN_inj e2
    refine ⟨t, n1, n2, φ, ?_, ?_, ?_⟩
    · rw [← e1, hc, ha, hx]
      rfl
    · rw [← e3, hy]
      rfl
    · rw [← e3, ← e4]
      rw [hs, hs1, hs2, hx] at hm
      exact hm
  · rintro ⟨t, n1, n2, φ, hc, hy, hsub⟩
    exact ⟨_, rfl, c, y, ψ, t, n1, n2, φ, _, _, _, _, _, _, rfl, rfl, rfl, rfl, hc, hy, rfl, rfl,
      rfl, hsub⟩

/-! ### Facts about derivations and the rules -/

/-- The fact "`G ⊢ D` has a derivation of size `n`". -/
noncomputable def dfact (n G D : V) : V := M.trip (M.sing n) G D

theorem dfact_inj {n G D n' G' D' : V} (h : M.dfact n G D = M.dfact n' G' D') :
    n = n' ∧ G = G' ∧ D = D' := by
  obtain ⟨h1, h2, h3⟩ := M.trip_inj h
  exact ⟨M.sing_inj h1, h2, h3⟩

/-- `q = dfact m G D`. Bound names `52`–`59`. -/
def fDFact (q m G D : ℕ) : Fml :=
  Fml.ex 58 (Fml.ex 52 (Fml.ex 53 (.and (fSing 58 m 59) (.and (fOp q 52 53 54 55)
    (.and (fOp 52 58 G 56 57) (fOp 53 D D 56 57))))))

theorem sat_fDFact {q m G D : ℕ} (ρ : ℕ → V) (hq : q < 50 ∨ q = 60) (hm : m < 50) (hG : G < 50)
    (hD : D < 50) :
    Sat M.mem M.isSet (fDFact q m G D) ρ ↔ ρ q = M.dfact (ρ m) (ρ G) (ρ D) := by
  have q1 : q ≠ 58 := by omega
  have q2 : q ≠ 52 := by omega
  have q3 : q ≠ 53 := by omega
  have m1 : m ≠ 58 := by omega
  have m2 : m ≠ 52 := by omega
  have m3 : m ≠ 53 := by omega
  have g1 : G ≠ 58 := by omega
  have g2 : G ≠ 52 := by omega
  have g3 : G ≠ 53 := by omega
  have d1 : D ≠ 58 := by omega
  have d2 : D ≠ 52 := by omega
  have d3 : D ≠ 53 := by omega
  simp only [fDFact, M.sat_ex, Sat,
    M.sat_fSing (u := 58) (a := m) (c := 59) (by decide) (by omega),
    M.sat_fOp (p := q) (a := 52) (b := 53) (u := 54) (c := 55) (by omega) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    M.sat_fOp (p := 52) (a := 58) (b := G) (u := 56) (c := 57) (by decide) (by decide)
      (by omega) (by decide) (by omega) (by decide),
    M.sat_fOp (p := 53) (a := D) (b := D) (u := 56) (c := 57) (by decide) (by omega)
      (by omega) (by omega) (by omega) (by decide),
    Function.update_self, Function.update_of_ne q1, Function.update_of_ne q2,
    Function.update_of_ne q3, Function.update_of_ne m1, Function.update_of_ne m2,
    Function.update_of_ne m3, Function.update_of_ne g1, Function.update_of_ne g2,
    Function.update_of_ne g3, Function.update_of_ne d1, Function.update_of_ne d2,
    Function.update_of_ne d3, Function.update_of_ne (show (58 : ℕ) ≠ 52 by decide),
    Function.update_of_ne (show (58 : ℕ) ≠ 53 by decide),
    Function.update_of_ne (show (52 : ℕ) ≠ 53 by decide)]
  unfold dfact trip
  constructor
  · rintro ⟨u, p1, p2, rfl, h, rfl, rfl⟩
    exact h
  · intro h
    exact ⟨_, _, _, rfl, h, rfl, rfl⟩

/-- `dfact m G D ∈ Y`. Bound names `52`–`60`. -/
def fDIn (Y m G D : ℕ) : Fml := Fml.ex 60 (.and (.mem 60 Y) (fDFact 60 m G D))

theorem sat_fDIn {Y m G D : ℕ} (ρ : ℕ → V) (hY : Y < 50) (hm : m < 50) (hG : G < 50)
    (hD : D < 50) :
    Sat M.mem M.isSet (fDIn Y m G D) ρ ↔ M.mem (M.dfact (ρ m) (ρ G) (ρ D)) (ρ Y) := by
  have h1 : Y ≠ 60 := by omega
  have h2 : m ≠ 60 := by omega
  have h3 : G ≠ 60 := by omega
  have h4 : D ≠ 60 := by omega
  simp only [fDIn, M.sat_ex, Sat,
    fun ρ' : ℕ → V => M.sat_fDFact (q := 60) (m := m) (G := G) (D := D) ρ' (Or.inr rfl) hm hG hD,
    Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

/-- Axiom: a formula on both sides. -/
def RAx (N n G D : V) : Prop := M.mem n N ∧ ∃ φ, M.mem φ N ∧ M.mem φ G ∧ M.mem φ D

def rAx : Fml := .and (.mem 11 6) (Fml.ex 19 (.and (.mem 19 6) (.and (.mem 19 15) (.mem 19 16))))

theorem sat_rAx (ρ : ℕ → V) : Sat M.mem M.isSet rAx ρ ↔ M.RAx (ρ 6) (ρ 11) (ρ 15) (ρ 16) := by
  simp [rAx, RAx, Sat, M.sat_ex, Function.update_apply]

/-- `¬φ` on the left. -/
def RNegL (ng Y n G D : V) : Prop :=
  ∃ φ c D' m, M.mem (M.op φ c) ng ∧ M.mem c G ∧ D' = M.adj D φ ∧ n = M.succ m ∧
    M.mem (M.dfact m G D') Y

def rNegL : Fml :=
  Fml.ex 19 (Fml.ex 21 (Fml.ex 27 (Fml.ex 17 (.and (fApp 2 19 21) (.and (.mem 21 15)
    (.and (fAdj 27 16 19 61) (.and (fSuccEq 11 17) (fDIn 8 17 15 27))))))))

theorem sat_rNegL (ρ : ℕ → V) :
    Sat M.mem M.isSet rNegL ρ ↔ M.RNegL (ρ 2) (ρ 8) (ρ 11) (ρ 15) (ρ 16) := by
  simp [rNegL, RNegL, Sat, M.sat_ex, M.sat_fApp, M.sat_fAdj, M.sat_fSuccEq, M.sat_fDIn,
    Function.update_apply]

/-- `¬φ` on the right. -/
def RNegR (ng Y n G D : V) : Prop :=
  ∃ φ c G' m, M.mem (M.op φ c) ng ∧ M.mem c D ∧ G' = M.adj G φ ∧ n = M.succ m ∧
    M.mem (M.dfact m G' D) Y

def rNegR : Fml :=
  Fml.ex 19 (Fml.ex 21 (Fml.ex 27 (Fml.ex 17 (.and (fApp 2 19 21) (.and (.mem 21 16)
    (.and (fAdj 27 15 19 61) (.and (fSuccEq 11 17) (fDIn 8 17 27 16))))))))

theorem sat_rNegR (ρ : ℕ → V) :
    Sat M.mem M.isSet rNegR ρ ↔ M.RNegR (ρ 2) (ρ 8) (ρ 11) (ρ 15) (ρ 16) := by
  simp [rNegR, RNegR, Sat, M.sat_ex, M.sat_fApp, M.sat_fAdj, M.sat_fSuccEq, M.sat_fDIn,
    Function.update_apply]

/-- `φ ∧ ψ` on the left. -/
def RAndL (ag ad mu Y n G D : V) : Prop :=
  ∃ φ ψ p c G1 G2 m, M.PairRaw ad mu φ ψ p ∧ M.mem (M.op p c) ag ∧ M.mem c G ∧
    G1 = M.adj G φ ∧ G2 = M.adj G1 ψ ∧ n = M.succ m ∧ M.mem (M.dfact m G2 D) Y

def rAndL : Fml :=
  Fml.ex 19 (Fml.ex 20 (Fml.ex 22 (Fml.ex 21 (Fml.ex 27 (Fml.ex 28 (Fml.ex 17
    (.and (fPairN 22 19 20) (.and (fApp 3 22 21) (.and (.mem 21 15) (.and (fAdj 27 15 19 61)
    (.and (fAdj 28 27 20 61) (.and (fSuccEq 11 17) (fDIn 8 17 28 16)))))))))))))

theorem sat_rAndL (ρ : ℕ → V) :
    Sat M.mem M.isSet rAndL ρ ↔ M.RAndL (ρ 3) (ρ 7) (ρ 18) (ρ 8) (ρ 11) (ρ 15) (ρ 16) := by
  simp [rAndL, RAndL, Sat, M.sat_ex, M.sat_fApp, M.sat_fPairN, M.sat_fAdj, M.sat_fSuccEq,
    M.sat_fDIn, Function.update_apply]

/-- `φ ∧ ψ` on the right. -/
def RAndR (ag ad mu Y n G D : V) : Prop :=
  ∃ φ ψ p c D1 D2 m1 m2 mm, M.PairRaw ad mu φ ψ p ∧ M.mem (M.op p c) ag ∧ M.mem c D ∧
    D1 = M.adj D φ ∧ D2 = M.adj D ψ ∧ M.mem (M.trip m1 m2 mm) ad ∧ n = M.succ mm ∧
    M.mem (M.dfact m1 G D1) Y ∧ M.mem (M.dfact m2 G D2) Y

def rAndR : Fml :=
  Fml.ex 19 (Fml.ex 20 (Fml.ex 22 (Fml.ex 21 (Fml.ex 27 (Fml.ex 28 (Fml.ex 17 (Fml.ex 25
    (Fml.ex 26 (.and (fPairN 22 19 20) (.and (fApp 3 22 21) (.and (.mem 21 16)
    (.and (fAdj 27 16 19 61) (.and (fAdj 28 16 20 61) (.and (fApp3 7 17 25 26)
    (.and (fSuccEq 11 26) (.and (fDIn 8 17 15 27) (fDIn 8 25 15 28)))))))))))))))))

theorem sat_rAndR (ρ : ℕ → V) :
    Sat M.mem M.isSet rAndR ρ ↔ M.RAndR (ρ 3) (ρ 7) (ρ 18) (ρ 8) (ρ 11) (ρ 15) (ρ 16) := by
  simp [rAndR, RAndR, Sat, M.sat_ex, M.sat_fApp, M.sat_fApp3, M.sat_fPairN, M.sat_fAdj,
    M.sat_fSuccEq, M.sat_fDIn, Function.update_apply]

/-- `∀x φ` on the left, with the instance `ψ = φ[y/x]`. -/
def RAllL (al ad mu Y n G D : V) : Prop :=
  ∃ c y ψ p p' G' m, M.PairRaw ad mu y ψ p ∧ M.PairRaw ad mu c p p' ∧ M.mem p' al ∧
    M.mem c G ∧ G' = M.adj G ψ ∧ n = M.succ m ∧ M.mem (M.dfact m G' D) Y

def rAllL : Fml :=
  Fml.ex 21 (Fml.ex 24 (Fml.ex 20 (Fml.ex 22 (Fml.ex 23 (Fml.ex 27 (Fml.ex 17
    (.and (fPairN 22 24 20) (.and (fPairN 23 21 22) (.and (.mem 23 4) (.and (.mem 21 15)
    (.and (fAdj 27 15 20 61) (.and (fSuccEq 11 17) (fDIn 8 17 27 16)))))))))))))

theorem sat_rAllL (ρ : ℕ → V) :
    Sat M.mem M.isSet rAllL ρ ↔ M.RAllL (ρ 4) (ρ 7) (ρ 18) (ρ 8) (ρ 11) (ρ 15) (ρ 16) := by
  simp [rAllL, RAllL, Sat, M.sat_ex, M.sat_fPairN, M.sat_fAdj, M.sat_fSuccEq, M.sat_fDIn,
    Function.update_apply]

/-- `∀x φ` on the right, with the instance `ψ = φ[y/x]` for a variable `y` greater than
every code in the sequent. -/
def RAllR (al N ad mu Y n G D : V) : Prop :=
  ∃ c y ψ p p' D' m, M.PairRaw ad mu y ψ p ∧ M.PairRaw ad mu c p p' ∧ M.mem p' al ∧
    M.mem c D ∧
    (∀ χ, (M.mem χ G ∨ M.mem χ D) → M.mem χ N ∧
      ∃ sχ, sχ = M.succ χ ∧ ∃ d, M.mem d N ∧ M.mem (M.trip sχ d y) ad) ∧
    D' = M.adj D ψ ∧ n = M.succ m ∧ M.mem (M.dfact m G D') Y

def rAllR : Fml :=
  Fml.ex 21 (Fml.ex 24 (Fml.ex 20 (Fml.ex 22 (Fml.ex 23 (Fml.ex 27 (Fml.ex 17
    (.and (fPairN 22 24 20) (.and (fPairN 23 21 22) (.and (.mem 23 4) (.and (.mem 21 16)
    (.and (.all 29 (Fml.imp (Fml.or (.mem 29 15) (.mem 29 16)) (.and (.mem 29 6)
      (Fml.ex 10 (.and (fSuccEq 10 29) (fLe 10 24))))))
    (.and (fAdj 27 16 20 61) (.and (fSuccEq 11 17) (fDIn 8 17 15 27))))))))))))))

theorem sat_rAllR (ρ : ℕ → V) :
    Sat M.mem M.isSet rAllR ρ ↔
      M.RAllR (ρ 4) (ρ 6) (ρ 7) (ρ 18) (ρ 8) (ρ 11) (ρ 15) (ρ 16) := by
  simp [rAllR, RAllR, fLe, Sat, M.sat_ex, M.sat_imp, M.sat_or, M.sat_fPairN, M.sat_fApp3,
    M.sat_fAdj, M.sat_fSuccEq, M.sat_fDIn, Function.update_apply]

/-- One step of derivability. -/
def DerStepRaw (ng ag al N ad mu Y q : V) : Prop :=
  ∃ n G D, q = M.dfact n G D ∧
    (M.RAx N n G D ∨ M.RNegL ng Y n G D ∨ M.RNegR ng Y n G D ∨ M.RAndL ag ad mu Y n G D ∨
      M.RAndR ag ad mu Y n G D ∨ M.RAllL al ad mu Y n G D ∨ M.RAllR al N ad mu Y n G D)

def derStepFml : Fml :=
  Fml.ex 11 (Fml.ex 15 (Fml.ex 16 (.and (fDFact 9 11 15 16)
    (Fml.or rAx (Fml.or rNegL (Fml.or rNegR (Fml.or rAndL (Fml.or rAndR
      (Fml.or rAllL rAllR)))))))))

theorem sat_derStepFml (ρ : ℕ → V) : Sat M.mem M.isSet derStepFml ρ ↔
    M.DerStepRaw (ρ 2) (ρ 3) (ρ 4) (ρ 6) (ρ 7) (ρ 18) (ρ 8) (ρ 9) := by
  simp [derStepFml, DerStepRaw, Sat, M.sat_ex, M.sat_or, M.sat_fDFact, M.sat_rAx, M.sat_rNegL,
    M.sat_rNegR, M.sat_rAndL, M.sat_rAndR, M.sat_rAllL, M.sat_rAllR, Function.update_apply]

/-- One step of derivability, with the parameters in place. -/
def DerStep (Y q : V) : Prop :=
  M.DerStepRaw M.negG M.andG M.alliSet M.nat M.adG M.muG Y q

theorem derStep_mono {Y Y' q : V} (hY : ∀ p, M.mem p Y → M.mem p Y') (h : M.DerStep Y q) :
    M.DerStep Y' q := by
  obtain ⟨n, G, D, hq, hR⟩ := h
  refine ⟨n, G, D, hq, ?_⟩
  rcases hR with h | h | h | h | h | h | h
  · exact Or.inl h
  · obtain ⟨φ, c, D', m, h1, h2, h3, h4, h5⟩ := h
    exact Or.inr (Or.inl ⟨φ, c, D', m, h1, h2, h3, h4, hY _ h5⟩)
  · obtain ⟨φ, c, G', m, h1, h2, h3, h4, h5⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨φ, c, G', m, h1, h2, h3, h4, hY _ h5⟩))
  · obtain ⟨φ, ψ, p, c, G1, G2, m, h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, p, c, G1, G2, m, h1, h2, h3, h4, h5, h6,
      hY _ h7⟩)))
  · obtain ⟨φ, ψ, p, c, D1, D2, m1, m2, mm, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, p, c, D1, D2, m1, m2, mm, h1, h2, h3,
      h4, h5, h6, h7, hY _ h8, hY _ h9⟩))))
  · obtain ⟨c, y, ψ, p, p', G', m, h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, y, ψ, p, p', G', m, h1, h2, h3,
      h4, h5, h6, hY _ h7⟩)))))
  · obtain ⟨c, y, ψ, p, p', D', m, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, y, ψ, p, p', D', m, h1, h2, h3,
      h4, h5, h6, h7, hY _ h8⟩)))))

def derFml : Fml := .all 8 (Fml.imp (.all 9 (Fml.imp derStepFml (.mem 9 8))) (.mem 0 8))

def σD : ℕ → ℕ :=
  σW [(0, 7), (2, 5), (3, 5), (4, 3), (6, 3), (7, 7), (18, 7), (8, 8), (9, 7), (15, 3), (16, 3),
    (27, 3), (28, 3), (52, 5), (53, 5), (54, 6), (55, 5), (56, 4), (57, 3), (58, 3), (60, 7)]

/-- **The set of derivable sequents exists**: the least set closed under the rules. -/
theorem exists_derSet : ∃ Dr, (∀ q, M.DerStep Dr q → M.mem q Dr) ∧
    (∀ Y, (∀ q, M.DerStep Y q → M.mem q Y) → ∀ p, M.mem p Dr → M.mem p Y) := by
  obtain ⟨ρ0, e2, e3, e4, e6, e7, e18⟩ : ∃ ρ0 : ℕ → V, ρ0 2 = M.negG ∧ ρ0 3 = M.andG ∧
      ρ0 4 = M.alliSet ∧ ρ0 6 = M.nat ∧ ρ0 7 = M.adG ∧ ρ0 18 = M.muG :=
    ⟨Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (fun _ => dflt) 2 M.negG) 3 M.andG) 4 M.alliSet) 6 M.nat) 7 M.adG)
      18 M.muG, by simp [Function.update_apply]⟩
  obtain ⟨Dr, -, hDr⟩ := M.comp σD derFml 0 rfl ρ0
  have hDr' : ∀ p, M.mem p Dr ↔ ∀ Y, (∀ q, M.DerStep Y q → M.mem q Y) → M.mem p Y := by
    intro p
    rw [hDr p]
    simp [derFml, DerStep, Sat, M.sat_imp, M.sat_derStepFml, Function.update_apply, e2, e3, e4,
      e6, e7, e18]
  refine ⟨Dr, fun q hq => ?_, fun Y hY p hp => (hDr' p).mp hp Y hY⟩
  exact (hDr' q).mpr fun Y hY => hY q (M.derStep_mono (fun p hp => (hDr' p).mp hp Y hY) hq)

/-- The set of derivable sequents with their sizes. -/
noncomputable def derSet : V := Classical.choose M.exists_derSet

/-- `G ⊢ D` has a cut-free derivation of size `n`. -/
def Der (n G D : V) : Prop := M.mem (M.dfact n G D) M.derSet

theorem derSet_closed {q : V} (h : M.DerStep M.derSet q) : M.mem q M.derSet :=
  (Classical.choose_spec M.exists_derSet).1 q h

theorem derSet_least {Y : V} (hY : ∀ q, M.DerStep Y q → M.mem q Y) {p : V}
    (hp : M.mem p M.derSet) : M.mem p Y := (Classical.choose_spec M.exists_derSet).2 Y hY p hp

/-! ## Soundness -/

/-- The sequent `G ⊢ D` is sound in the structure `(U, E)`: at every assignment at which all
members of `G` are true, some member of `D` is not false. For decided formulas "not false"
is "true"; for `D` empty it says that `G` has no model. -/
def SeqOK (U E G D : V) : Prop :=
  ∀ s, M.IsAsg U s → (∀ c : M.Num, M.mem c.1 G → M.Holds U E c s) →
    ∃ c : M.Num, M.mem c.1 D ∧ ¬ M.Fails U E c s

def validFml : Fml :=
  .all 11 (.all 15 (.all 16 (Fml.imp (fDFact 0 11 15 16) (.all 20 (Fml.imp (.mem 20 5)
    (Fml.imp (.all 21 (Fml.imp (.and (.mem 21 15) (.mem 21 6)) (fLit 8 21 13 20)))
      (Fml.ex 21 (.and (.mem 21 16) (.and (.mem 21 6) (.neg (fLit 8 21 12 20)))))))))))

def σV : ℕ → ℕ :=
  σW [(0, 7), (5, 6), (6, 3), (7, 7), (18, 7), (8, 8), (15, 3), (16, 3), (20, 5), (52, 5),
    (53, 5), (54, 6), (55, 5), (56, 4), (57, 3), (58, 3), (110, 7), (111, 3), (112, 4), (113, 5),
    (115, 3), (116, 4), (117, 6), (118, 5)]

theorem exists_validSet (U E : V) :
    ∃ W, ∀ q, M.mem q W ↔ ∀ n G D, q = M.dfact n G D → M.SeqOK U E G D := by
  have had := M.adG_spec
  have hmu := M.muG_spec
  obtain ⟨W, -, hW⟩ := M.comp σV validFml 0 rfl (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (fun _ => dflt) 5 (M.asg U)) 6 M.nat) 7 M.adG) 18 M.muG) 8 (M.satSet U E))
    12 (0 : M.Num).1) 13 (1 : M.Num).1)
  have hW' : ∀ q, M.mem q W ↔ ∀ n G D, q = M.dfact n G D → ∀ s, M.mem s (M.asg U) →
      (∀ c, (M.mem c G ∧ M.mem c M.nat) → M.LitRaw M.adG M.muG (M.satSet U E) c (1 : M.Num).1 s) →
      ∃ c, M.mem c D ∧ M.mem c M.nat ∧
        ¬ M.LitRaw M.adG M.muG (M.satSet U E) c (0 : M.Num).1 s := by
    intro q
    rw [hW q]
    simp [validFml, Sat, M.sat_imp, M.sat_ex, M.sat_fDFact, M.sat_fLit, Function.update_apply]
  refine ⟨W, fun q => ?_⟩
  rw [hW']
  refine forall_congr' fun n => forall_congr' fun G => forall_congr' fun D =>
    imp_congr Iff.rfl ?_
  constructor
  · intro h s hs hΓ
    obtain ⟨c, hc, hn, hf⟩ := h s (M.mem_asg.mpr hs) (fun c hc =>
      (M.litRaw_iff had hmu _ ⟨c, hc.2⟩ 1 s).mpr (hΓ ⟨c, hc.2⟩ hc.1))
    exact ⟨⟨c, hn⟩, hc, fun hF => hf ((M.litRaw_iff had hmu _ ⟨c, hn⟩ 0 s).mpr hF)⟩
  · intro h s hs hΓ
    obtain ⟨c, hc, hf⟩ := h s (M.mem_asg.mp hs) (fun c hc =>
      (M.litRaw_iff had hmu _ c 1 s).mp (hΓ c.1 ⟨hc, c.2⟩))
    exact ⟨c.1, hc, c.2, fun hF => hf ((M.litRaw_iff had hmu _ c 0 s).mp hF)⟩

theorem and_dec {φ ψ p c : V} (hp : M.PairRaw M.adG M.muG φ ψ p)
    (hc : M.mem (M.op p c) M.andG) :
    ∃ P Q : M.Num, P.1 = φ ∧ Q.1 = ψ ∧ c = (M.cAnd P Q).1 := by
  obtain ⟨P, Q, hP, hQ, hp'⟩ := (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mp hp
  obtain ⟨R, hR, hc'⟩ := (M.andG_spec _ _).mp hc
  have e : R = M.pairN P Q := Subtype.ext (hR.trans hp')
  refine ⟨P, Q, hP, hQ, ?_⟩
  rw [← hc', e]
  rfl

theorem alli_dec {c y ψ p p' : V} (hp : M.PairRaw M.adG M.muG y ψ p)
    (hp' : M.PairRaw M.adG M.muG c p p') (h : M.mem p' M.alliSet) :
    ∃ C Yv Ps t n1 n2 φ : M.Num, C.1 = c ∧ Yv.1 = y ∧ Ps.1 = ψ ∧
      C = M.cAll (M.vr t n1) φ ∧ Yv = M.vr t n2 ∧ M.Sub (M.vr t n1) Yv φ Ps := by
  obtain ⟨Yv, Ps, hY, hPs, hp1⟩ := (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mp hp
  obtain ⟨C, P2, hC, hP2, hp2⟩ := (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mp hp'
  have e : P2 = M.pairN Yv Ps := Subtype.ext (hP2.trans hp1)
  rw [hp2, e] at h
  obtain ⟨t, n1, n2, φ, h1, h2, h3⟩ := (M.mem_alliSet C Yv Ps).mp h
  exact ⟨C, Yv, Ps, t, n1, n2, φ, hC, hY, hPs, h1, h2, h3⟩

/-- The set of sound sequents is closed under the rules. -/
theorem valid_closed (U E : V) {W : V}
    (hW : ∀ q, M.mem q W ↔ ∀ n G D, q = M.dfact n G D → M.SeqOK U E G D) (q : V)
    (h : M.DerStep W q) : M.mem q W := by
  obtain ⟨n, G, D, hq, hR⟩ := h
  rw [hW]
  intro n' G' D' e
  obtain ⟨-, eG, eD⟩ := M.dfact_inj (hq.symm.trans e)
  rw [← eG, ← eD]
  have prem : ∀ {m G1 D1 : V}, M.mem (M.dfact m G1 D1) W → M.SeqOK U E G1 D1 := fun h =>
    (hW _).mp h _ _ _ rfl
  intro s hs hΓ
  rcases hR with h | h | h | h | h | h | h
  · obtain ⟨-, φ, hφN, hφG, hφD⟩ := h
    exact ⟨⟨φ, hφN⟩, hφD, fun hf => M.consistent U E ⟨φ, hφN⟩ s ⟨hΓ ⟨φ, hφN⟩ hφG, hf⟩⟩
  · obtain ⟨φ, c, D', m, hng, hcG, hD', -, hpr⟩ := h
    obtain ⟨P, hP, hc⟩ := (M.negG_spec _ _).mp hng
    have hcG' : M.mem (M.cNeg P).1 G := by
      rw [hc]
      exact hcG
    have hF : M.Fails U E P s := ((M.holds_neg P s).mp (hΓ _ hcG')).2
    obtain ⟨c1, hc1, hnf⟩ := prem hpr s hs hΓ
    rw [hD'] at hc1
    rcases M.mem_adj.mp hc1 with h1 | h1
    · exact ⟨c1, h1, hnf⟩
    · have e1 : c1 = P := Subtype.ext (h1.trans hP.symm)
      rw [e1] at hnf
      exact absurd hF hnf
  · obtain ⟨φ, c, G', m, hng, hcD, hG', -, hpr⟩ := h
    obtain ⟨P, hP, hc⟩ := (M.negG_spec _ _).mp hng
    by_cases hT : M.Holds U E P s
    · refine prem hpr s hs fun c1 hc1 => ?_
      rw [hG'] at hc1
      rcases M.mem_adj.mp hc1 with h1 | h1
      · exact hΓ c1 h1
      · have e1 : c1 = P := Subtype.ext (h1.trans hP.symm)
        rw [e1]
        exact hT
    · refine ⟨M.cNeg P, ?_, fun hf => hT ((M.fails_neg P s).mp hf).2⟩
      rw [hc]
      exact hcD
  · obtain ⟨φ, ψ, p, c, G1, G2, m, hp, hag, hcG, hG1, hG2, -, hpr⟩ := h
    obtain ⟨P, Q, hP, hQ, hc⟩ := M.and_dec hp hag
    have hcG' : M.mem (M.cAnd P Q).1 G := by
      rw [← hc]
      exact hcG
    have hPQ := ((M.holds_and P Q s).mp (hΓ _ hcG')).2
    refine prem hpr s hs fun c1 hc1 => ?_
    rw [hG2, hG1] at hc1
    rcases M.mem_adj.mp hc1 with h1 | h1
    · rcases M.mem_adj.mp h1 with h2 | h2
      · exact hΓ c1 h2
      · have e1 : c1 = P := Subtype.ext (h2.trans hP.symm)
        rw [e1]
        exact hPQ.1
    · have e1 : c1 = Q := Subtype.ext (h1.trans hQ.symm)
      rw [e1]
      exact hPQ.2
  · obtain ⟨φ, ψ, p, c, D1, D2, m1, m2, mm, hp, hag, hcD, hD1, hD2, -, -, hpr1, hpr2⟩ := h
    obtain ⟨P, Q, hP, hQ, hc⟩ := M.and_dec hp hag
    obtain ⟨c1, hc1, hnf1⟩ := prem hpr1 s hs hΓ
    obtain ⟨c2, hc2, hnf2⟩ := prem hpr2 s hs hΓ
    rw [hD1] at hc1
    rw [hD2] at hc2
    rcases M.mem_adj.mp hc1 with h1 | h1
    · exact ⟨c1, h1, hnf1⟩
    · rcases M.mem_adj.mp hc2 with h2 | h2
      · exact ⟨c2, h2, hnf2⟩
      · have e1 : c1 = P := Subtype.ext (h1.trans hP.symm)
        have e2 : c2 = Q := Subtype.ext (h2.trans hQ.symm)
        rw [e1] at hnf1
        rw [e2] at hnf2
        refine ⟨M.cAnd P Q, ?_, fun hf => ?_⟩
        · rw [← hc]
          exact hcD
        · rcases ((M.fails_and P Q s).mp hf).2 with ⟨h3, -⟩ | ⟨-, h3⟩
          · exact hnf1 h3
          · exact hnf2 h3
  · obtain ⟨c, y, ψ, p, p', G', m, hp, hp', hal, hcG, hG', -, hpr⟩ := h
    obtain ⟨C, Yv, Ps, t, n1, n2, φ, hC, hY, hPs, eC, eY, hsub⟩ := M.alli_dec hp hp' hal
    have hCG : M.mem (M.cAll (M.vr t n1) φ).1 G := by
      rw [← eC, hC]
      exact hcG
    have hall := ((M.holds_all t n1 φ s).mp (hΓ _ hCG)).2
    obtain ⟨b, hb, -⟩ := hs.2.2.1 Yv.1 Yv.2
    have hbU : M.mem (M.op t.1 b) U := by
      have hb' := hb
      rw [eY] at hb'
      exact hs.2.2.2 t n2 b hb'
    have hsb : M.IsAsg U (M.updS s (M.vr t n1).1 b) := M.isAsg_updS hs t n1 hbU
    have hT : M.Holds U E Ps s := (M.substitution hsub hs hsb hb).1.mpr (hall b hbU)
    refine prem hpr s hs fun c1 hc1 => ?_
    rw [hG'] at hc1
    rcases M.mem_adj.mp hc1 with h1 | h1
    · exact hΓ c1 h1
    · have e1 : c1 = Ps := Subtype.ext (h1.trans hPs.symm)
      rw [e1]
      exact hT
  · obtain ⟨c, y, ψ, p, p', D', m, hp, hp', hal, hcD, hfresh, hD', -, hpr⟩ := h
    obtain ⟨C, Yv, Ps, t, n1, n2, φ, hC, hY, hPs, eC, eY, hsub⟩ := M.alli_dec hp hp' hal
    by_contra hcon
    have hallF : ∀ c1 : M.Num, M.mem c1.1 D → M.Fails U E c1 s := fun c1 hc1 =>
      by_contra fun hnf => hcon ⟨c1, hc1, hnf⟩
    have hlt : ∀ c1 : M.Num, (M.mem c1.1 G ∨ M.mem c1.1 D) → c1 + 1 ≤ M.vr t n2 := by
      intro c1 hc1
      obtain ⟨-, sχ, hsχ, d, hd, hmem⟩ := hfresh c1.1 hc1
      rw [hsχ, ← hY] at hmem
      have h1 : M.LeRaw M.adG (M.nsucc c1).1 Yv.1 := ⟨d, hd, hmem⟩
      have h2 := (M.leRaw_iff M.adG_spec (M.nsucc c1) Yv).mp h1
      rw [M.nsucc_eq_add_one, eY] at h2
      exact h2
    have hCD : M.mem (M.cAll (M.vr t n1) φ).1 D := by
      rw [← eC, hC]
      exact hcD
    obtain ⟨-, -, a, haU, hFa⟩ := (M.fails_all t n1 φ s).mp (hallF _ hCD)
    have hs1 : M.IsAsg U (M.updS s (M.vr t n2).1 a) := M.isAsg_updS hs t n2 haU
    have hΓ1 : ∀ c1 : M.Num, M.mem c1.1 G → M.Holds U E c1 (M.updS s (M.vr t n2).1 a) :=
      fun c1 hc1 => (M.coincide (hlt c1 (Or.inl hc1)) hs haU).1.mp (hΓ c1 hc1)
    obtain ⟨c1, hc1, hnf⟩ := prem hpr _ hs1 hΓ1
    rw [hD'] at hc1
    rcases M.mem_adj.mp hc1 with h1 | h1
    · exact hnf ((M.coincide (hlt c1 (Or.inr h1)) hs haU).2.mp (hallF c1 h1))
    · have e1 : c1 = Ps := Subtype.ext (h1.trans hPs.symm)
      rw [e1] at hnf
      have hya : M.mem (M.op Yv.1 a) (M.updS s (M.vr t n2).1 a) := by
        rw [eY]
        exact M.mem_updS_same.mpr rfl
      have hCy := hlt _ (Or.inr hCD)
      have hxC : M.vr t n1 ≤ M.cAll (M.vr t n1) φ :=
        le_trans (M.le_pairN_left _ φ) (M.le_pairN_right 3 _)
      have hφC : φ ≤ M.cAll (M.vr t n1) φ :=
        le_trans (M.le_pairN_right _ φ) (M.le_pairN_right 3 _)
      have hxy : (M.vr t n1).1 ≠ (M.vr t n2).1 :=
        M.val_ne_of_lt (le_trans (add_le_add hxC (le_refl 1)) hCy)
      have hφlt : φ + 1 ≤ M.vr t n2 := le_trans (add_le_add hφC (le_refl 1)) hCy
      have hs2 : M.IsAsg U (M.updS (M.updS s (M.vr t n2).1 a) (M.vr t n1).1 a) :=
        M.isAsg_updS hs1 t n1 haU
      have hsubst := (M.substitution (U := U) (E := E) hsub hs1 hs2 hya).2
      have hsx : M.IsAsg U (M.updS s (M.vr t n1).1 a) := M.isAsg_updS hs t n1 haU
      have h2 := (M.coincide hφlt hsx haU).2.mp hFa
      rw [M.updS_comm hxy] at h2
      exact hnf (hsubst.mpr h2)

/-- **Soundness for coded cut-free derivations.** If `G ⊢ D` has a derivation, of any size
`n` (a number of the model, standard or not), then in every set structure, at every
assignment at which all members of `G` are true, some member of `D` is not false. -/
theorem soundness {n G D : V} (h : M.Der n G D) (U E : V) : M.SeqOK U E G D := by
  obtain ⟨W, hW⟩ := M.exists_validSet U E
  exact (hW _).mp (M.derSet_least (M.valid_closed U E hW) h) n G D rfl

/-- A set of coded formulas with a refutation has no model. -/
theorem no_model_of_refutation {n G : V} (h : M.Der n G M.emp) (U E s : V)
    (hs : M.IsAsg U s) : ¬ ∀ c : M.Num, M.mem c.1 G → M.Holds U E c s := fun hΓ => by
  obtain ⟨c, hc, -⟩ := M.soundness h U E s hs hΓ
  exact M.not_mem_emp _ hc

/-- For decided formulas on the right, soundness gives a true formula. -/
theorem soundness_form {n G D : V} (h : M.Der n G D) (U E s : V) (hs : M.IsAsg U s)
    (hD : ∀ c : M.Num, M.mem c.1 D → M.Form U E c)
    (hΓ : ∀ c : M.Num, M.mem c.1 G → M.Holds U E c s) :
    ∃ c : M.Num, M.mem c.1 D ∧ M.Holds U E c s := by
  obtain ⟨c, hc, hnf⟩ := M.soundness h U E s hs hΓ
  exact ⟨c, hc, (hD c hc s hs).resolve_right hnf⟩

/-! ### The rules, in clean form -/

theorem der_ax (n : M.Num) {G D : V} (c : M.Num) (hG : M.mem c.1 G) (hD : M.mem c.1 D) :
    M.Der n.1 G D :=
  M.derSet_closed ⟨n.1, G, D, rfl, Or.inl ⟨n.2, c.1, c.2, hG, hD⟩⟩

theorem der_negL {m G D : V} (φ : M.Num) (hc : M.mem (M.cNeg φ).1 G)
    (h : M.Der m G (M.adj D φ.1)) : M.Der (M.succ m) G D :=
  M.derSet_closed ⟨_, G, D, rfl, Or.inr (Or.inl ⟨φ.1, (M.cNeg φ).1, _, m,
    M.graph_app M.negG_spec φ, hc, rfl, rfl, h⟩)⟩

theorem der_negR {m G D : V} (φ : M.Num) (hc : M.mem (M.cNeg φ).1 D)
    (h : M.Der m (M.adj G φ.1) D) : M.Der (M.succ m) G D :=
  M.derSet_closed ⟨_, G, D, rfl, Or.inr (Or.inr (Or.inl ⟨φ.1, (M.cNeg φ).1, _, m,
    M.graph_app M.negG_spec φ, hc, rfl, rfl, h⟩))⟩

theorem der_andL {m G D : V} (φ ψ : M.Num) (hc : M.mem (M.cAnd φ ψ).1 G)
    (h : M.Der m (M.adj (M.adj G φ.1) ψ.1) D) : M.Der (M.succ m) G D :=
  M.derSet_closed ⟨_, G, D, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨φ.1, ψ.1, (M.pairN φ ψ).1,
    (M.cAnd φ ψ).1, _, _, m,
    (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mpr ⟨φ, ψ, rfl, rfl, rfl⟩,
    M.graph_app M.andG_spec (M.pairN φ ψ), hc, rfl, rfl, rfl, h⟩)))⟩

theorem der_andR {G D : V} (m1 m2 φ ψ : M.Num) (hc : M.mem (M.cAnd φ ψ).1 D)
    (h1 : M.Der m1.1 G (M.adj D φ.1)) (h2 : M.Der m2.1 G (M.adj D ψ.1)) :
    M.Der (M.succ (m1 + m2).1) G D :=
  M.derSet_closed ⟨_, G, D, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ.1, ψ.1,
    (M.pairN φ ψ).1, (M.cAnd φ ψ).1, _, _, m1.1, m2.1, (m1 + m2).1,
    (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mpr ⟨φ, ψ, rfl, rfl, rfl⟩,
    M.graph_app M.andG_spec (M.pairN φ ψ), hc, rfl, rfl, M.graph₂_app M.adG_spec m1 m2, rfl,
    h1, h2⟩))))⟩

theorem der_allL {m G D : V} (t n1 n2 φ ψ : M.Num) (hc : M.mem (M.cAll (M.vr t n1) φ).1 G)
    (hsub : M.Sub (M.vr t n1) (M.vr t n2) φ ψ) (h : M.Der m (M.adj G ψ.1) D) :
    M.Der (M.succ m) G D :=
  M.derSet_closed ⟨_, G, D, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨(M.cAll (M.vr t n1) φ).1, (M.vr t n2).1, ψ.1, (M.pairN (M.vr t n2) ψ).1,
    (M.pairN (M.cAll (M.vr t n1) φ) (M.pairN (M.vr t n2) ψ)).1, _, m,
    (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mpr ⟨M.vr t n2, ψ, rfl, rfl, rfl⟩,
    (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mpr
      ⟨M.cAll (M.vr t n1) φ, M.pairN (M.vr t n2) ψ, rfl, rfl, rfl⟩,
    (M.mem_alliSet _ _ _).mpr ⟨t, n1, n2, φ, rfl, rfl, hsub⟩, hc, rfl, rfl, h⟩)))))⟩

theorem der_allR {m G D : V} (t n1 n2 φ ψ : M.Num) (hc : M.mem (M.cAll (M.vr t n1) φ).1 D)
    (hsub : M.Sub (M.vr t n1) (M.vr t n2) φ ψ)
    (hfresh : ∀ χ, (M.mem χ G ∨ M.mem χ D) → ∃ X : M.Num, X.1 = χ ∧ X + 1 ≤ M.vr t n2)
    (h : M.Der m G (M.adj D ψ.1)) : M.Der (M.succ m) G D := by
  refine M.derSet_closed ⟨_, G, D, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨(M.cAll (M.vr t n1) φ).1, (M.vr t n2).1, ψ.1, (M.pairN (M.vr t n2) ψ).1,
    (M.pairN (M.cAll (M.vr t n1) φ) (M.pairN (M.vr t n2) ψ)).1, _, m,
    (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mpr ⟨M.vr t n2, ψ, rfl, rfl, rfl⟩,
    (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mpr
      ⟨M.cAll (M.vr t n1) φ, M.pairN (M.vr t n2) ψ, rfl, rfl, rfl⟩,
    (M.mem_alliSet _ _ _).mpr ⟨t, n1, n2, φ, rfl, rfl, hsub⟩, hc, fun χ hχ => ?_, rfl, rfl,
    h⟩)))))⟩
  obtain ⟨X, hX, hlt⟩ := hfresh χ hχ
  obtain ⟨d, hd⟩ := M.le_def.mp hlt
  refine ⟨by rw [← hX]; exact X.2, M.succ χ, rfl, d.1, d.2, ?_⟩
  have h1 := M.graph₂_app M.adG_spec (X + 1) d
  rw [show M.addN (X + 1) d = M.vr t n2 from hd, M.val_add_one, hX] at h1
  exact h1

end Model

end NFUCut
