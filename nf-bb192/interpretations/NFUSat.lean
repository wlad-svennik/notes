module

public import ConNF.NF.NFULadder

/-!
# Satisfaction for coded formulas (§3.1 of the note, first half)

This file continues `NFULadder`. It works in an arbitrary model `M` of NFU + Infinity.

A many-sorted set structure is given by two sets of the model: `U`, the set of pairs `⟨t, a⟩`
with `a` an element of sort `t`, and `E`, the set of triples `⟨r, a, b⟩` with `a` related to `b`
by the relation number `r`. Formulas are coded by natural numbers of the model, standard or
not: `cRel r v w`, `cNeg φ`, `cAnd φ ψ`, `cAll v φ`, with variables `vr t n` (the `n`-th variable
of sort `t`). An assignment (`IsAsg`) is a set function on the natural numbers that gives each
variable a value of its sort.

* `satSet U E` is the satisfaction relation, a set of the model: the least set of signed facts
  closed under one step of the truth definition (`exists_satSet`, `sat_char`).
* `consistent`: no code is both true and false at an assignment (induction on the code).
* `satisfaction`: the codes built by the four constructors are decided by every assignment,
  and truth obeys Tarski's clauses.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

@[expose] public section

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

/-! ## Numerals of the model -/

theorem natCast_inj' : ∀ a b : ℕ, ((a : M.Num) = (b : M.Num)) → a = b := by
  intro a
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ b =>
      rw [Nat.cast_zero, Nat.cast_succ] at h
      exact absurd h.symm (M.peano.1 _)
  | succ a ih =>
    intro b h
    cases b with
    | zero =>
      rw [Nat.cast_zero, Nat.cast_succ] at h
      exact absurd h (M.peano.1 _)
    | succ b =>
      rw [Nat.cast_succ, Nat.cast_succ] at h
      rw [ih b (M.peano.2.1 _ _ h)]

instance instCharZeroNum : CharZero M.Num := ⟨fun a b h => M.natCast_inj' a b h⟩

instance instNontrivialNum : Nontrivial M.Num :=
  ⟨⟨0, 1, fun h => M.peano.1 0 (by rw [zero_add]; exact h.symm)⟩⟩

/-! ## The pairing function on numbers -/

theorem pairN_inj_iff {x y x' y' : M.Num} : M.pairN x y = M.pairN x' y' ↔ x = x' ∧ y = y' :=
  ⟨M.pairN_inj, fun h => by rw [h.1, h.2]⟩

theorem le_mul_self' (z : M.Num) : z ≤ z * z := by
  rcases M.num_cases z with h | ⟨k, h⟩
  · rw [h]
    exact M.le_def.mpr ⟨M.nzero * M.nzero, M.zero_addN _⟩
  · rw [h, M.nsucc_eq_add_one]
    exact M.le_def.mpr ⟨k * (k + 1), by ring⟩

theorem le_pairN_left (x y : M.Num) : x ≤ M.pairN x y :=
  M.le_def.mpr ⟨(x + y) * (x + y), add_comm _ _⟩

theorem le_pairN_right (x y : M.Num) : y ≤ M.pairN x y := by
  have h1 : y ≤ x + y := M.le_def.mpr ⟨x, add_comm y x⟩
  have h2 : x + y ≤ (x + y) * (x + y) := M.le_mul_self' _
  have h3 : (x + y) * (x + y) ≤ M.pairN x y := M.le_def.mpr ⟨x, rfl⟩
  exact le_trans h1 (le_trans h2 h3)

theorem lt_pairN_right {x : M.Num} (y : M.Num) (hx : 1 ≤ x) : y + 1 ≤ M.pairN x y := by
  have h1 : y ≤ (x + y) * (x + y) :=
    le_trans (M.le_def.mpr ⟨x, add_comm y x⟩) (M.le_mul_self' _)
  exact add_le_add h1 hx

/-- `c = pairN x y`, stated with the graphs of `+` and `·`. -/
def PairRaw (ad mu x y c : V) : Prop :=
  ∃ u v, M.mem (M.trip x y u) ad ∧ M.mem (M.trip u u v) mu ∧ M.mem (M.trip v x c) ad

theorem pairRaw_iff {ad mu : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN)
    (x y c : V) :
    M.PairRaw ad mu x y c ↔ ∃ X Y : M.Num, X.1 = x ∧ Y.1 = y ∧ c = (M.pairN X Y).1 := by
  constructor
  · rintro ⟨u, v, h1, h2, h3⟩
    obtain ⟨X, Y, hX, hY, hu⟩ := (had _ _ _).mp h1
    rw [← hu] at h2
    have hv := M.graph₂_val hmu h2
    rw [hv, ← hX] at h3
    refine ⟨X, Y, hX, hY, ?_⟩
    rw [M.pairN_eq]
    exact M.graph₂_val had h3
  · rintro ⟨X, Y, hX, hY, hc⟩
    refine ⟨(M.addN X Y).1, (M.mulN (M.addN X Y) (M.addN X Y)).1, ?_, ?_, ?_⟩
    · rw [← hX, ← hY]
      exact M.graph₂_app had X Y
    · exact M.graph₂_app hmu (M.addN X Y) (M.addN X Y)
    · rw [hc, M.pairN_eq, ← hX]
      exact M.graph₂_app had (M.mulN (M.addN X Y) (M.addN X Y)) X

/-- `c = pairN x y`. Bound names `100`, `101`; the graphs of `+` and `·` are the names `7`
and `18`. -/
def fPairN (c x y : ℕ) : Fml :=
  Fml.ex 100 (Fml.ex 101 (.and (fApp3 7 x y 100) (.and (fApp3 18 100 100 101)
    (fApp3 7 101 x c))))

theorem sat_fPairN {c x y : ℕ} (ρ : ℕ → V) (hc : c < 30 ∨ 101 < c) (hx : x < 30 ∨ 101 < x)
    (hy : y < 30 ∨ 101 < y) :
    Sat M.mem M.isSet (fPairN c x y) ρ ↔ M.PairRaw (ρ 7) (ρ 18) (ρ x) (ρ y) (ρ c) := by
  have c0 : c ≠ 100 := by omega
  have c1 : c ≠ 101 := by omega
  have x0 : x ≠ 100 := by omega
  have x1 : x ≠ 101 := by omega
  have y0 : y ≠ 100 := by omega
  have y1 : y ≠ 101 := by omega
  simp only [fPairN, M.sat_ex, Sat, PairRaw,
    fun ρ' : ℕ → V => M.sat_fApp3 (G := 7) (a := x) (b := y) (c := 100) ρ' (by decide)
      (by omega) (by omega) (by decide),
    fun ρ' : ℕ → V => M.sat_fApp3 (G := 18) (a := 100) (b := 100) (c := 101) ρ' (by decide)
      (by decide) (by decide) (by decide),
    fun ρ' : ℕ → V => M.sat_fApp3 (G := 7) (a := 101) (b := x) (c := c) ρ' (by decide)
      (by decide) (by omega) (by omega),
    Function.update_self, Function.update_of_ne c0, Function.update_of_ne c1,
    Function.update_of_ne x0, Function.update_of_ne x1, Function.update_of_ne y0,
    Function.update_of_ne y1, Function.update_of_ne (show (7 : ℕ) ≠ 100 by decide),
    Function.update_of_ne (show (7 : ℕ) ≠ 101 by decide),
    Function.update_of_ne (show (18 : ℕ) ≠ 100 by decide),
    Function.update_of_ne (show (18 : ℕ) ≠ 101 by decide),
    Function.update_of_ne (show (100 : ℕ) ≠ 101 by decide)]

/-! ## Facts: pairs of a number and an assignment -/

/-- The pair of a number `c` (three times a singleton, to match types) and an object `s`. -/
noncomputable def fact (c s : V) : V := M.op (M.sing (M.sing (M.sing c))) s

theorem fact_inj {c s c' s' : V} (h : M.fact c s = M.fact c' s') : c = c' ∧ s = s' := by
  obtain ⟨h1, h2⟩ := M.op_inj h
  exact ⟨M.sing_inj (M.sing_inj (M.sing_inj h1)), h2⟩

/-- `q = fact c s`. Bound names `111`–`118`. -/
def fFact (q c s : ℕ) : Fml :=
  Fml.ex 111 (Fml.ex 112 (Fml.ex 113 (.and (fSing 111 c 114) (.and (fSing 112 111 115)
    (.and (fSing 113 112 116) (fOp q 113 s 117 118))))))

theorem sat_fFact {q c s : ℕ} (ρ : ℕ → V) (hq : q < 111) (hc : c < 111) (hs : s < 111) :
    Sat M.mem M.isSet (fFact q c s) ρ ↔ ρ q = M.fact (ρ c) (ρ s) := by
  have q1 : q ≠ 111 := by omega
  have q2 : q ≠ 112 := by omega
  have q3 : q ≠ 113 := by omega
  have c1 : c ≠ 111 := by omega
  have c2 : c ≠ 112 := by omega
  have c3 : c ≠ 113 := by omega
  have s1 : s ≠ 111 := by omega
  have s2 : s ≠ 112 := by omega
  have s3 : s ≠ 113 := by omega
  simp only [fFact, M.sat_ex, Sat,
    M.sat_fSing (u := 111) (a := c) (c := 114) (by decide) (by omega),
    M.sat_fSing (u := 112) (a := 111) (c := 115) (by decide) (by decide),
    M.sat_fSing (u := 113) (a := 112) (c := 116) (by decide) (by decide),
    M.sat_fOp (p := q) (a := 113) (b := s) (u := 117) (c := 118) (by omega) (by decide)
      (by omega) (by decide) (by omega) (by decide),
    Function.update_self, Function.update_of_ne q1, Function.update_of_ne q2,
    Function.update_of_ne q3, Function.update_of_ne c1, Function.update_of_ne c2,
    Function.update_of_ne c3, Function.update_of_ne s1, Function.update_of_ne s2,
    Function.update_of_ne s3, Function.update_of_ne (show (111 : ℕ) ≠ 112 by decide),
    Function.update_of_ne (show (111 : ℕ) ≠ 113 by decide),
    Function.update_of_ne (show (112 : ℕ) ≠ 113 by decide)]
  unfold fact
  constructor
  · rintro ⟨u1, u2, u3, rfl, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, _, rfl, rfl, rfl, h⟩

/-- `fact c s ∈ Y`. Bound names `110`–`118`. -/
def fIn (Y c s : ℕ) : Fml := Fml.ex 110 (.and (.mem 110 Y) (fFact 110 c s))

theorem sat_fIn {Y c s : ℕ} (ρ : ℕ → V) (hY : Y < 110) (hc : c < 110) (hs : s < 110) :
    Sat M.mem M.isSet (fIn Y c s) ρ ↔ M.mem (M.fact (ρ c) (ρ s)) (ρ Y) := by
  have h1 : Y ≠ 110 := by omega
  have h2 : c ≠ 110 := by omega
  have h3 : s ≠ 110 := by omega
  simp only [fIn, M.sat_ex, Sat,
    fun ρ' : ℕ → V => M.sat_fFact (q := 110) (c := c) (s := s) ρ' (by decide) (by omega)
      (by omega),
    Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

/-- The signed fact `fact (pairN x sg) s` is in `Y`. -/
def LitRaw (ad mu Y x sg s : V) : Prop := ∃ w, M.PairRaw ad mu x sg w ∧ M.mem (M.fact w s) Y

/-- Bound name `104`. -/
def fLit (Y x sg s : ℕ) : Fml := Fml.ex 104 (.and (fPairN 104 x sg) (fIn Y 104 s))

theorem sat_fLit {Y x sg s : ℕ} (ρ : ℕ → V) (hY : Y < 30) (hx : x < 30) (hsg : sg < 30)
    (hs : s < 30) :
    Sat M.mem M.isSet (fLit Y x sg s) ρ ↔
      M.LitRaw (ρ 7) (ρ 18) (ρ Y) (ρ x) (ρ sg) (ρ s) := by
  have h1 : Y ≠ 104 := by omega
  have h2 : x ≠ 104 := by omega
  have h3 : sg ≠ 104 := by omega
  have h4 : s ≠ 104 := by omega
  simp only [fLit, LitRaw, M.sat_ex, Sat,
    fun ρ' : ℕ → V => M.sat_fPairN (c := 104) (x := x) (y := sg) ρ' (by decide) (by omega)
      (by omega),
    fun ρ' : ℕ → V => M.sat_fIn (Y := Y) (c := 104) (s := s) ρ' (by omega) (by decide)
      (by omega),
    Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4,
    Function.update_of_ne (show (7 : ℕ) ≠ 104 by decide),
    Function.update_of_ne (show (18 : ℕ) ≠ 104 by decide)]

/-! ## Assignments -/

theorem exists_updS (s i a : V) : ∃ t, M.isSet t ∧
    ∀ p, M.mem p t ↔ (M.mem p s ∧ ¬ ∃ b, p = M.op i b) ∨ p = M.op i a := by
  obtain ⟨t, ht, h⟩ := M.comp (σW [(0, 4), (1, 5)])
    (Fml.or (.and (.mem 0 1) (.neg (Fml.ex 4 (fPr 0 2 4)))) (fPr 0 2 3)) 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 1 s) 2 i) 3 a)
  refine ⟨t, ht, fun p => ?_⟩
  rw [h p]
  simp [M.sat_or, M.sat_ex, Sat, M.sat_fPr, Function.update_apply]

/-- The assignment `s` with its value at `i` changed to `a`. -/
noncomputable def updS (s i a : V) : V := Classical.choose (M.exists_updS s i a)

theorem updS_isSet (s i a : V) : M.isSet (M.updS s i a) :=
  (Classical.choose_spec (M.exists_updS s i a)).1

theorem mem_updS {s i a p : V} :
    M.mem p (M.updS s i a) ↔ (M.mem p s ∧ ¬ ∃ b, p = M.op i b) ∨ p = M.op i a :=
  (Classical.choose_spec (M.exists_updS s i a)).2 p

theorem eq_updS_iff {t s i a : V} :
    (M.isSet t ∧ ∀ p, M.mem p t ↔ (M.mem p s ∧ ¬ ∃ b, p = M.op i b) ∨ p = M.op i a) ↔
      t = M.updS s i a := by
  constructor
  · rintro ⟨ht, h⟩
    exact M.ext ht (M.updS_isSet s i a) fun z => (h z).trans M.mem_updS.symm
  · rintro rfl
    exact ⟨M.updS_isSet s i a, fun p => M.mem_updS⟩

theorem mem_updS_same {s i a b : V} : M.mem (M.op i b) (M.updS s i a) ↔ b = a := by
  rw [M.mem_updS]
  constructor
  · rintro (⟨-, h⟩ | h)
    · exact absurd ⟨b, rfl⟩ h
    · exact (M.op_inj h).2
  · intro h
    rw [h]
    exact Or.inr rfl

theorem mem_updS_of_ne {s i a j b : V} (h : j ≠ i) :
    M.mem (M.op j b) (M.updS s i a) ↔ M.mem (M.op j b) s := by
  rw [M.mem_updS]
  constructor
  · rintro (⟨h1, -⟩ | h1)
    · exact h1
    · exact absurd (M.op_inj h1).1 h
  · intro h1
    exact Or.inl ⟨h1, fun ⟨c, hc⟩ => h (M.op_inj hc).1⟩

/-- `t = updS s i a`. Bound names `103`, `119`. -/
def fUpd (t s i a : ℕ) : Fml :=
  .and (.set t) (.all 119 (Fml.iff (.mem 119 t)
    (Fml.or (.and (.mem 119 s) (.neg (Fml.ex 103 (fOp 119 i 103 36 37)))) (fOp 119 i a 36 37))))

theorem sat_fUpd {t s i a : ℕ} (ρ : ℕ → V) (ht : t < 30) (hs : s < 30) (hi : i < 30)
    (ha : a < 30) :
    Sat M.mem M.isSet (fUpd t s i a) ρ ↔ ρ t = M.updS (ρ s) (ρ i) (ρ a) := by
  have t1 : t ≠ 119 := by omega
  have s1 : s ≠ 119 := by omega
  have i1 : i ≠ 119 := by omega
  have a1 : a ≠ 119 := by omega
  have i2 : i ≠ 103 := by omega
  rw [← M.eq_updS_iff]
  simp only [fUpd, M.sat_ex, M.sat_iff, M.sat_or, Sat,
    M.sat_fOp (p := 119) (a := i) (b := 103) (u := 36) (c := 37) (by decide) (by omega)
      (by decide) (by omega) (by decide) (by decide),
    M.sat_fOp (p := 119) (a := i) (b := a) (u := 36) (c := 37) (by decide) (by omega)
      (by omega) (by omega) (by omega) (by decide),
    Function.update_self, Function.update_of_ne t1, Function.update_of_ne s1,
    Function.update_of_ne i1, Function.update_of_ne a1, Function.update_of_ne i2,
    Function.update_of_ne (show (119 : ℕ) ≠ 103 by decide)]

/-- `s` is an assignment for the structure with sorts `U`: a set function defined on all
natural numbers which gives the variable `pairN t n` a value of sort `t`. -/
def IsAsg (U s : V) : Prop :=
  M.isSet s ∧ (∀ p, M.mem p s → ∃ i a, M.mem i M.nat ∧ p = M.op i a) ∧
  (∀ i, M.mem i M.nat → ∃ a, M.mem (M.op i a) s ∧ ∀ b, M.mem (M.op i b) s → b = a) ∧
  ∀ (t n : M.Num) (a : V), M.mem (M.op (M.pairN t n).1 a) s → M.mem (M.op t.1 a) U

def asgFml : Fml :=
  .and (.set 0) (.and
    (.all 15 (Fml.imp (.mem 15 0) (Fml.ex 16 (Fml.ex 17 (.and (.mem 16 6) (fPr 15 16 17))))))
    (.and
      (.all 16 (Fml.imp (.mem 16 6) (Fml.ex 17 (.and (fApp 0 16 17)
        (.all 19 (Fml.imp (fApp 0 16 19) (.eq 19 17)))))))
      (.all 20 (.all 21 (.all 22 (.all 17 (Fml.imp (.and (fPairN 22 20 21) (fApp 0 22 17))
        (fApp 1 20 17))))))))

theorem exists_asg (U : V) : ∃ A, ∀ s, M.mem s A ↔ M.IsAsg U s := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  obtain ⟨mu, hmu⟩ := M.mulN_natOp
  obtain ⟨A, -, hA⟩ := M.comp (σW [(0, 5), (1, 5), (6, 3), (7, 7), (18, 7), (15, 4)]) asgFml 0
    rfl (Function.update (Function.update (Function.update (Function.update (fun _ => dflt)
      1 U) 6 M.nat) 7 ad) 18 mu)
  have hA' : ∀ s, M.mem s A ↔ (M.isSet s ∧ (∀ p, M.mem p s → ∃ i a, M.mem i M.nat ∧ p = M.op i a) ∧
      (∀ i, M.mem i M.nat → ∃ a, M.mem (M.op i a) s ∧ ∀ b, M.mem (M.op i b) s → b = a) ∧
      ∀ t n v a, (M.PairRaw ad mu t n v ∧ M.mem (M.op v a) s) → M.mem (M.op t a) U) := by
    intro s
    rw [hA s]
    simp [asgFml, Sat, M.sat_imp, M.sat_ex, M.sat_fPr, M.sat_fApp, M.sat_fPairN,
      Function.update_apply]
  refine ⟨A, fun s => ?_⟩
  rw [hA']
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  constructor
  · intro h t n a ha
    exact h t.1 n.1 _ a ⟨(M.pairRaw_iff had hmu _ _ _).mpr ⟨t, n, rfl, rfl, rfl⟩, ha⟩
  · rintro h t n v a ⟨hp, ha⟩
    obtain ⟨T, N, hT, hN, hv⟩ := (M.pairRaw_iff had hmu _ _ _).mp hp
    rw [hv] at ha
    rw [← hT]
    exact h T N a ha

/-- The set of assignments. -/
noncomputable def asg (U : V) : V := Classical.choose (M.exists_asg U)

theorem mem_asg {U s : V} : M.mem s (M.asg U) ↔ M.IsAsg U s :=
  Classical.choose_spec (M.exists_asg U) s

/-- Changing the value of a variable of sort `t` to an element of sort `t` gives an
assignment. -/
theorem isAsg_updS {U s : V} (hs : M.IsAsg U s) (t n : M.Num) {a : V}
    (ha : M.mem (M.op t.1 a) U) : M.IsAsg U (M.updS s (M.pairN t n).1 a) := by
  obtain ⟨-, h2, h3, h4⟩ := hs
  refine ⟨M.updS_isSet _ _ _, fun p hp => ?_, fun i hi => ?_, fun t' n' a' h => ?_⟩
  · rcases M.mem_updS.mp hp with ⟨hp, -⟩ | hp
    · exact h2 p hp
    · exact ⟨_, a, (M.pairN t n).2, hp⟩
  · by_cases hiv : i = (M.pairN t n).1
    · rw [hiv]
      exact ⟨a, M.mem_updS_same.mpr rfl, fun b hb => M.mem_updS_same.mp hb⟩
    · obtain ⟨b, hb, hbu⟩ := h3 i hi
      exact ⟨b, (M.mem_updS_of_ne hiv).mpr hb, fun c hc => hbu c ((M.mem_updS_of_ne hiv).mp hc)⟩
  · by_cases hv : (M.pairN t' n').1 = (M.pairN t n).1
    · rw [hv] at h
      have e1 := M.mem_updS_same.mp h
      have e2 := (M.pairN_inj (Subtype.ext hv)).1
      rw [e1, e2]
      exact ha
    · exact h4 t' n' a' ((M.mem_updS_of_ne hv).mp h)

/-! ## One step of the truth definition

A formula is a number. The fact `fact (pairN c 1) s` says that `c` is true at the assignment
`s`, and `fact (pairN c 0) s` that it is false. A code is `pairN k x` with tag `k`:
`0` atomic, `1` negation, `2` conjunction, `3` universal quantifier. -/

/-- `x` is true at `s` according to `Y`. -/
def Tr (Y : V) (x : M.Num) (s : V) : Prop := M.mem (M.fact (M.pairN x 1).1 s) Y

/-- `x` is false at `s` according to `Y`. -/
def Fa (Y : V) (x : M.Num) (s : V) : Prop := M.mem (M.fact (M.pairN x 0).1 s) Y

/-- The values of the variables `v`, `w` under `s` stand in the relation number `r`. -/
def RelH (E : V) (r v w : M.Num) (s : V) : Prop :=
  ∃ a c, M.mem (M.op v.1 a) s ∧ M.mem (M.op w.1 c) s ∧ M.mem (M.trip r.1 a c) E

def B0 (E : V) (b x : M.Num) (s : V) : Prop :=
  ∃ r v w : M.Num, x = M.pairN r (M.pairN v w) ∧
    ((b = 1 ∧ M.RelH E r v w s) ∨ (b = 0 ∧ ¬ M.RelH E r v w s))

def B1 (Y : V) (b x : M.Num) (s : V) : Prop :=
  (b = 1 ∧ M.Fa Y x s) ∨ (b = 0 ∧ M.Tr Y x s)

def B2 (Y : V) (b x : M.Num) (s : V) : Prop :=
  ∃ φ ψ : M.Num, x = M.pairN φ ψ ∧
    ((b = 1 ∧ M.Tr Y φ s ∧ M.Tr Y ψ s) ∨
     (b = 0 ∧ ((M.Fa Y φ s ∧ (M.Tr Y ψ s ∨ M.Fa Y ψ s)) ∨
       ((M.Tr Y φ s ∨ M.Fa Y φ s) ∧ M.Fa Y ψ s))))

def B3 (U Y : V) (b x : M.Num) (s : V) : Prop :=
  ∃ t n φ : M.Num, x = M.pairN (M.pairN t n) φ ∧
    ((b = 1 ∧ ∀ a, M.mem (M.op t.1 a) U → M.Tr Y φ (M.updS s (M.pairN t n).1 a)) ∨
     (b = 0 ∧ (∀ a, M.mem (M.op t.1 a) U → M.Tr Y φ (M.updS s (M.pairN t n).1 a) ∨
         M.Fa Y φ (M.updS s (M.pairN t n).1 a)) ∧
       ∃ a, M.mem (M.op t.1 a) U ∧ M.Fa Y φ (M.updS s (M.pairN t n).1 a)))

/-- The truth conditions of the code `pairN k x` with sign `b` at `s`, given the facts `Y`
about smaller codes. -/
def Body (U E Y : V) (b k x : M.Num) (s : V) : Prop :=
  (k = 0 ∧ M.B0 E b x s) ∨ (k = 1 ∧ M.B1 Y b x s) ∨ (k = 2 ∧ M.B2 Y b x s) ∨
    (k = 3 ∧ M.B3 U Y b x s)

theorem body_mono {U E Y Y' : V} (hY : ∀ p, M.mem p Y → M.mem p Y') {b k x : M.Num} {s : V}
    (h : M.Body U E Y b k x s) : M.Body U E Y' b k x s := by
  rcases h with h | ⟨hk, h⟩ | ⟨hk, h⟩ | ⟨hk, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hk, h.imp (fun h => ⟨h.1, hY _ h.2⟩) (fun h => ⟨h.1, hY _ h.2⟩)⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨hk, ?_⟩))
    obtain ⟨φ, ψ, hx, h⟩ := h
    refine ⟨φ, ψ, hx, ?_⟩
    rcases h with ⟨hb, h1, h2⟩ | ⟨hb, h⟩
    · exact Or.inl ⟨hb, hY _ h1, hY _ h2⟩
    · refine Or.inr ⟨hb, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hY _ h1, h2.imp (hY _) (hY _)⟩
      · exact Or.inr ⟨h1.imp (hY _) (hY _), hY _ h2⟩
  · refine Or.inr (Or.inr (Or.inr ⟨hk, ?_⟩))
    obtain ⟨t, n, φ, hx, h⟩ := h
    refine ⟨t, n, φ, hx, ?_⟩
    rcases h with ⟨hb, h1⟩ | ⟨hb, h1, a, ha, h2⟩
    · exact Or.inl ⟨hb, fun a ha => hY _ (h1 a ha)⟩
    · exact Or.inr ⟨hb, fun a ha => (h1 a ha).imp (hY _) (hY _), a, ha, hY _ h2⟩

/-- One step: the facts that follow from `Y`. -/
def Step (U E A Y q : V) : Prop :=
  ∃ (b k x : M.Num) (s : V), q = M.fact (M.pairN (M.pairN k x) b).1 s ∧ M.mem s A ∧
    M.Body U E Y b k x s

theorem step_mono {U E A Y Y' q : V} (hY : ∀ p, M.mem p Y → M.mem p Y')
    (h : M.Step U E A Y q) : M.Step U E A Y' q := by
  obtain ⟨b, k, x, s, hq, hs, hB⟩ := h
  exact ⟨b, k, x, s, hq, hs, M.body_mono hY hB⟩

/-! ### The same as stratified formulas

Names: `1` sorts, `2` relations, `5` the set of assignments, `7` and `18` the graphs of `+`
and `·`, `8` the set of facts, `10`–`13` the numbers `0`–`3`; `14` sign, `15` tag, `16`
payload, `20` assignment. -/

def B0Raw (ad mu E z0 z1 b x s : V) : Prop :=
  ∃ r v w y, M.PairRaw ad mu v w y ∧ M.PairRaw ad mu r y x ∧
    ((b = z1 ∧ ∃ a c, M.mem (M.op v a) s ∧ M.mem (M.op w c) s ∧ M.mem (M.trip r a c) E) ∨
     (b = z0 ∧ ¬ ∃ a c, M.mem (M.op v a) s ∧ M.mem (M.op w c) s ∧ M.mem (M.trip r a c) E))

def relFml : Fml :=
  Fml.ex 25 (Fml.ex 26 (.and (fApp 20 22 25) (.and (fApp 20 23 26) (fApp3 2 21 25 26))))

def b0Fml : Fml :=
  Fml.ex 21 (Fml.ex 22 (Fml.ex 23 (Fml.ex 24 (.and (fPairN 24 22 23) (.and (fPairN 16 21 24)
    (Fml.or (.and (.eq 14 11) relFml) (.and (.eq 14 10) (.neg relFml))))))))

theorem sat_b0Fml (ρ : ℕ → V) : Sat M.mem M.isSet b0Fml ρ ↔
    M.B0Raw (ρ 7) (ρ 18) (ρ 2) (ρ 10) (ρ 11) (ρ 14) (ρ 16) (ρ 20) := by
  simp [b0Fml, relFml, B0Raw, Sat, M.sat_or, M.sat_ex, M.sat_fPairN, M.sat_fApp, M.sat_fApp3,
    Function.update_apply]

def B1Raw (ad mu Y z0 z1 b x s : V) : Prop :=
  (b = z1 ∧ M.LitRaw ad mu Y x z0 s) ∨ (b = z0 ∧ M.LitRaw ad mu Y x z1 s)

def b1Fml : Fml :=
  Fml.or (.and (.eq 14 11) (fLit 8 16 10 20)) (.and (.eq 14 10) (fLit 8 16 11 20))

theorem sat_b1Fml (ρ : ℕ → V) : Sat M.mem M.isSet b1Fml ρ ↔
    M.B1Raw (ρ 7) (ρ 18) (ρ 8) (ρ 10) (ρ 11) (ρ 14) (ρ 16) (ρ 20) := by
  simp [b1Fml, B1Raw, Sat, M.sat_or, M.sat_fLit]

def B2Raw (ad mu Y z0 z1 b x s : V) : Prop :=
  ∃ φ ψ, M.PairRaw ad mu φ ψ x ∧
    ((b = z1 ∧ M.LitRaw ad mu Y φ z1 s ∧ M.LitRaw ad mu Y ψ z1 s) ∨
     (b = z0 ∧ ((M.LitRaw ad mu Y φ z0 s ∧ (M.LitRaw ad mu Y ψ z1 s ∨ M.LitRaw ad mu Y ψ z0 s)) ∨
       ((M.LitRaw ad mu Y φ z1 s ∨ M.LitRaw ad mu Y φ z0 s) ∧ M.LitRaw ad mu Y ψ z0 s))))

def b2Fml : Fml :=
  Fml.ex 21 (Fml.ex 22 (.and (fPairN 16 21 22)
    (Fml.or (.and (.eq 14 11) (.and (fLit 8 21 11 20) (fLit 8 22 11 20)))
      (.and (.eq 14 10) (Fml.or
        (.and (fLit 8 21 10 20) (Fml.or (fLit 8 22 11 20) (fLit 8 22 10 20)))
        (.and (Fml.or (fLit 8 21 11 20) (fLit 8 21 10 20)) (fLit 8 22 10 20)))))))

theorem sat_b2Fml (ρ : ℕ → V) : Sat M.mem M.isSet b2Fml ρ ↔
    M.B2Raw (ρ 7) (ρ 18) (ρ 8) (ρ 10) (ρ 11) (ρ 14) (ρ 16) (ρ 20) := by
  simp [b2Fml, B2Raw, Sat, M.sat_or, M.sat_ex, M.sat_fPairN, M.sat_fLit, Function.update_apply]

def B3Raw (ad mu U Y z0 z1 b x s : V) : Prop :=
  ∃ t n vv φ, M.PairRaw ad mu t n vv ∧ M.PairRaw ad mu vv φ x ∧
    ((b = z1 ∧ ∀ a, M.mem (M.op t a) U → ∀ s', s' = M.updS s vv a → M.LitRaw ad mu Y φ z1 s') ∨
     (b = z0 ∧ (∀ a, M.mem (M.op t a) U → ∀ s', s' = M.updS s vv a →
         (M.LitRaw ad mu Y φ z1 s' ∨ M.LitRaw ad mu Y φ z0 s')) ∧
       ∃ a, M.mem (M.op t a) U ∧ ∃ s', s' = M.updS s vv a ∧ M.LitRaw ad mu Y φ z0 s'))

def b3Fml : Fml :=
  Fml.ex 21 (Fml.ex 22 (Fml.ex 23 (Fml.ex 24 (.and (fPairN 23 21 22) (.and (fPairN 16 23 24)
    (Fml.or
      (.and (.eq 14 11) (.all 25 (Fml.imp (fApp 1 21 25)
        (.all 27 (Fml.imp (fUpd 27 20 23 25) (fLit 8 24 11 27))))))
      (.and (.eq 14 10) (.and
        (.all 25 (Fml.imp (fApp 1 21 25) (.all 27 (Fml.imp (fUpd 27 20 23 25)
          (Fml.or (fLit 8 24 11 27) (fLit 8 24 10 27))))))
        (Fml.ex 25 (.and (fApp 1 21 25)
          (Fml.ex 27 (.and (fUpd 27 20 23 25) (fLit 8 24 10 27)))))))))))))

theorem sat_b3Fml (ρ : ℕ → V) : Sat M.mem M.isSet b3Fml ρ ↔
    M.B3Raw (ρ 7) (ρ 18) (ρ 1) (ρ 8) (ρ 10) (ρ 11) (ρ 14) (ρ 16) (ρ 20) := by
  simp [b3Fml, B3Raw, Sat, M.sat_or, M.sat_imp, M.sat_ex, M.sat_fPairN, M.sat_fApp,
    M.sat_fUpd, M.sat_fLit, Function.update_apply]

def BodyRaw (ad mu U E Y z0 z1 z2 z3 b k x s : V) : Prop :=
  (k = z0 ∧ M.B0Raw ad mu E z0 z1 b x s) ∨ (k = z1 ∧ M.B1Raw ad mu Y z0 z1 b x s) ∨
    (k = z2 ∧ M.B2Raw ad mu Y z0 z1 b x s) ∨ (k = z3 ∧ M.B3Raw ad mu U Y z0 z1 b x s)

def bodyFml : Fml :=
  Fml.or (.and (.eq 15 10) b0Fml) (Fml.or (.and (.eq 15 11) b1Fml)
    (Fml.or (.and (.eq 15 12) b2Fml) (.and (.eq 15 13) b3Fml)))

theorem sat_bodyFml (ρ : ℕ → V) : Sat M.mem M.isSet bodyFml ρ ↔
    M.BodyRaw (ρ 7) (ρ 18) (ρ 1) (ρ 2) (ρ 8) (ρ 10) (ρ 11) (ρ 12) (ρ 13) (ρ 14) (ρ 15) (ρ 16)
      (ρ 20) := by
  simp only [bodyFml, BodyRaw, Sat, M.sat_or, M.sat_b0Fml, M.sat_b1Fml, M.sat_b2Fml,
    M.sat_b3Fml]

def StepRaw (ad mu U E A Y z0 z1 z2 z3 q : V) : Prop :=
  ∃ b k x w c s, M.PairRaw ad mu k x w ∧ M.PairRaw ad mu w b c ∧ q = M.fact c s ∧ M.mem s A ∧
    M.BodyRaw ad mu U E Y z0 z1 z2 z3 b k x s

def stepFml : Fml :=
  Fml.ex 14 (Fml.ex 15 (Fml.ex 16 (Fml.ex 17 (Fml.ex 19 (Fml.ex 20 (.and (fPairN 17 15 16)
    (.and (fPairN 19 17 14) (.and (fFact 9 19 20) (.and (.mem 20 5) bodyFml)))))))))

theorem sat_stepFml (ρ : ℕ → V) : Sat M.mem M.isSet stepFml ρ ↔
    M.StepRaw (ρ 7) (ρ 18) (ρ 1) (ρ 2) (ρ 5) (ρ 8) (ρ 10) (ρ 11) (ρ 12) (ρ 13) (ρ 9) := by
  simp [stepFml, StepRaw, Sat, M.sat_ex, M.sat_fPairN, M.sat_fFact, M.sat_bodyFml,
    Function.update_apply]

/-! ### Raw and clean forms agree -/

theorem litRaw_iff {ad mu : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN)
    (Y : V) (x sg : M.Num) (s : V) :
    M.LitRaw ad mu Y x.1 sg.1 s ↔ M.mem (M.fact (M.pairN x sg).1 s) Y := by
  constructor
  · rintro ⟨w, hw, h⟩
    obtain ⟨X, S, hX, hS, hw'⟩ := (M.pairRaw_iff had hmu _ _ _).mp hw
    have e1 : X = x := Subtype.ext hX
    have e2 : S = sg := Subtype.ext hS
    rw [hw', e1, e2] at h
    exact h
  · intro h
    exact ⟨_, (M.pairRaw_iff had hmu _ _ _).mpr ⟨x, sg, rfl, rfl, rfl⟩, h⟩

theorem b0Raw_iff {ad mu : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN)
    (E : V) (b x : M.Num) (s : V) :
    M.B0Raw ad mu E (0 : M.Num).1 (1 : M.Num).1 b.1 x.1 s ↔ M.B0 E b x s := by
  constructor
  · rintro ⟨r, v, w, y, h1, h2, h⟩
    obtain ⟨V', W', hV, hW, hy⟩ := (M.pairRaw_iff had hmu _ _ _).mp h1
    obtain ⟨R', Y', hR, hY, hx⟩ := (M.pairRaw_iff had hmu _ _ _).mp h2
    have eY : Y' = M.pairN V' W' := Subtype.ext (hY.trans hy)
    refine ⟨R', V', W', Subtype.ext (by rw [hx, eY]), ?_⟩
    rw [← hR, ← hV, ← hW] at h
    exact h.imp (fun h => ⟨Subtype.ext h.1, h.2⟩) (fun h => ⟨Subtype.ext h.1, h.2⟩)
  · rintro ⟨r, v, w, hx, h⟩
    refine ⟨r.1, v.1, w.1, (M.pairN v w).1, (M.pairRaw_iff had hmu _ _ _).mpr ⟨v, w, rfl, rfl, rfl⟩,
      (M.pairRaw_iff had hmu _ _ _).mpr ⟨r, M.pairN v w, rfl, rfl, by rw [hx]⟩, ?_⟩
    exact h.imp (fun h => ⟨congrArg Subtype.val h.1, h.2⟩)
      (fun h => ⟨congrArg Subtype.val h.1, h.2⟩)

theorem b1Raw_iff {ad mu : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN)
    (Y : V) (b x : M.Num) (s : V) :
    M.B1Raw ad mu Y (0 : M.Num).1 (1 : M.Num).1 b.1 x.1 s ↔ M.B1 Y b x s := by
  unfold B1Raw B1 Tr Fa
  rw [M.litRaw_iff had hmu Y x 0 s, M.litRaw_iff had hmu Y x 1 s]
  exact or_congr (and_congr Subtype.ext_iff.symm Iff.rfl) (and_congr Subtype.ext_iff.symm Iff.rfl)

theorem b2Raw_iff {ad mu : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN)
    (Y : V) (b x : M.Num) (s : V) :
    M.B2Raw ad mu Y (0 : M.Num).1 (1 : M.Num).1 b.1 x.1 s ↔ M.B2 Y b x s := by
  constructor
  · rintro ⟨φ, ψ, h1, h⟩
    obtain ⟨P, Q, hP, hQ, hx⟩ := (M.pairRaw_iff had hmu _ _ _).mp h1
    refine ⟨P, Q, Subtype.ext hx, ?_⟩
    rw [← hP, ← hQ] at h
    simp only [M.litRaw_iff had hmu] at h
    exact h.imp (fun h => ⟨Subtype.ext h.1, h.2⟩) (fun h => ⟨Subtype.ext h.1, h.2⟩)
  · rintro ⟨φ, ψ, hx, h⟩
    refine ⟨φ.1, ψ.1, (M.pairRaw_iff had hmu _ _ _).mpr ⟨φ, ψ, rfl, rfl, by rw [hx]⟩, ?_⟩
    simp only [M.litRaw_iff had hmu]
    exact h.imp (fun h => ⟨congrArg Subtype.val h.1, h.2⟩)
      (fun h => ⟨congrArg Subtype.val h.1, h.2⟩)

theorem b3Raw_iff {ad mu : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN)
    (U Y : V) (b x : M.Num) (s : V) :
    M.B3Raw ad mu U Y (0 : M.Num).1 (1 : M.Num).1 b.1 x.1 s ↔ M.B3 U Y b x s := by
  constructor
  · rintro ⟨t, n, vv, φ, h1, h2, h⟩
    obtain ⟨T, N, hT, hN, hv⟩ := (M.pairRaw_iff had hmu _ _ _).mp h1
    obtain ⟨V', P, hV, hP, hx⟩ := (M.pairRaw_iff had hmu _ _ _).mp h2
    have eV : V' = M.pairN T N := Subtype.ext (hV.trans hv)
    refine ⟨T, N, P, Subtype.ext (by rw [hx, eV]), ?_⟩
    rw [← hT, ← hP, hv] at h
    simp only [forall_eq, exists_eq_left, M.litRaw_iff had hmu] at h
    exact h.imp (fun h => ⟨Subtype.ext h.1, h.2⟩) (fun h => ⟨Subtype.ext h.1, h.2⟩)
  · rintro ⟨t, n, φ, hx, h⟩
    refine ⟨t.1, n.1, (M.pairN t n).1, φ.1, (M.pairRaw_iff had hmu _ _ _).mpr ⟨t, n, rfl, rfl, rfl⟩,
      (M.pairRaw_iff had hmu _ _ _).mpr ⟨M.pairN t n, φ, rfl, rfl, by rw [hx]⟩, ?_⟩
    simp only [forall_eq, exists_eq_left, M.litRaw_iff had hmu]
    exact h.imp (fun h => ⟨congrArg Subtype.val h.1, h.2⟩)
      (fun h => ⟨congrArg Subtype.val h.1, h.2⟩)

theorem bodyRaw_iff {ad mu : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN)
    (U E Y : V) (b k x : M.Num) (s : V) :
    M.BodyRaw ad mu U E Y (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 b.1 k.1 x.1 s ↔
      M.Body U E Y b k x s := by
  unfold BodyRaw Body
  rw [M.b0Raw_iff had hmu, M.b1Raw_iff had hmu, M.b2Raw_iff had hmu, M.b3Raw_iff had hmu]
  exact or_congr (and_congr Subtype.ext_iff.symm Iff.rfl)
    (or_congr (and_congr Subtype.ext_iff.symm Iff.rfl)
      (or_congr (and_congr Subtype.ext_iff.symm Iff.rfl)
        (and_congr Subtype.ext_iff.symm Iff.rfl)))

theorem stepRaw_iff {ad mu : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN)
    (U E A Y q : V) :
    M.StepRaw ad mu U E A Y (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 q ↔
      M.Step U E A Y q := by
  constructor
  · rintro ⟨b, k, x, w, c, s, h1, h2, hq, hs, hB⟩
    obtain ⟨K, X, hK, hX, hw⟩ := (M.pairRaw_iff had hmu _ _ _).mp h1
    obtain ⟨W, B, hW, hB', hc⟩ := (M.pairRaw_iff had hmu _ _ _).mp h2
    have eW : W = M.pairN K X := Subtype.ext (hW.trans hw)
    rw [← hB', ← hK, ← hX] at hB
    refine ⟨B, K, X, s, ?_, hs, (M.bodyRaw_iff had hmu U E Y B K X s).mp hB⟩
    rw [hq, hc, eW]
  · rintro ⟨b, k, x, s, hq, hs, hB⟩
    exact ⟨b.1, k.1, x.1, (M.pairN k x).1, (M.pairN (M.pairN k x) b).1, s,
      (M.pairRaw_iff had hmu _ _ _).mpr ⟨k, x, rfl, rfl, rfl⟩,
      (M.pairRaw_iff had hmu _ _ _).mpr ⟨M.pairN k x, b, rfl, rfl, rfl⟩, hq, hs,
      (M.bodyRaw_iff had hmu U E Y b k x s).mpr hB⟩

/-! ## The satisfaction relation as a least fixed point -/

def lfpFml : Fml := .all 8 (Fml.imp (.all 9 (Fml.imp stepFml (.mem 9 8))) (.mem 0 8))

def σS : ℕ → ℕ :=
  σW [(0, 7), (1, 5), (2, 7), (5, 6), (6, 3), (7, 7), (18, 7), (8, 8), (9, 7), (20, 5), (27, 5),
    (110, 7), (111, 3), (112, 4), (113, 5), (115, 3), (116, 4), (117, 6), (118, 5), (119, 4)]

/-- **The satisfaction relation exists.** There is a set `Ys` of facts which is closed under
one step of the truth definition and all of whose members arise by one step from `Ys`. -/
theorem exists_satSet (U E : V) : ∃ Ys,
    (∀ q, M.Step U E (M.asg U) Ys q → M.mem q Ys) ∧
    (∀ q, M.mem q Ys → M.Step U E (M.asg U) Ys q) := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  obtain ⟨mu, hmu⟩ := M.mulN_natOp
  obtain ⟨ρ0, e1, e2, e5, e7, e18, e10, e11, e12, e13⟩ : ∃ ρ0 : ℕ → V, ρ0 1 = U ∧ ρ0 2 = E ∧
      ρ0 5 = M.asg U ∧ ρ0 7 = ad ∧ ρ0 18 = mu ∧ ρ0 10 = (0 : M.Num).1 ∧ ρ0 11 = (1 : M.Num).1 ∧
      ρ0 12 = (2 : M.Num).1 ∧ ρ0 13 = (3 : M.Num).1 :=
    ⟨Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (fun _ => dflt)
      1 U) 2 E) 5 (M.asg U)) 7 ad) 18 mu) 10 (0 : M.Num).1) 11 (1 : M.Num).1) 12 (2 : M.Num).1)
      13 (3 : M.Num).1, by simp [Function.update_apply]⟩
  -- the set of facts obtained in one step from `Y`
  have hgam : ∀ Y, ∃ G, ∀ q, M.mem q G ↔ M.Step U E (M.asg U) Y q := by
    intro Y
    obtain ⟨G, -, hG⟩ := M.comp σS stepFml 9 rfl (Function.update ρ0 8 Y)
    refine ⟨G, fun q => ?_⟩
    rw [hG q, M.sat_stepFml]
    simp [Function.update_apply, e1, e2, e5, e7, e18, e10, e11, e12, e13,
      M.stepRaw_iff had hmu]
  obtain ⟨Ys, -, hYs⟩ := M.comp σS lfpFml 0 rfl ρ0
  have hYs' : ∀ p, M.mem p Ys ↔
      ∀ Y, (∀ q, M.Step U E (M.asg U) Y q → M.mem q Y) → M.mem p Y := by
    intro p
    rw [hYs p]
    simp [lfpFml, Sat, M.sat_imp, M.sat_stepFml, Function.update_apply, e1, e2, e5, e7, e18,
      e10, e11, e12, e13, M.stepRaw_iff had hmu]
  have hclosed : ∀ q, M.Step U E (M.asg U) Ys q → M.mem q Ys := by
    intro q hq
    refine (hYs' q).mpr fun Y hY => hY q (M.step_mono (fun p hp => (hYs' p).mp hp Y hY) hq)
  refine ⟨Ys, hclosed, fun q hq => ?_⟩
  obtain ⟨G, hG⟩ := hgam Ys
  have hGsub : ∀ p, M.mem p G → M.mem p Ys := fun p hp => hclosed p ((hG p).mp hp)
  have hGclosed : ∀ p, M.Step U E (M.asg U) G p → M.mem p G := fun p hp =>
    (hG p).mpr (M.step_mono hGsub hp)
  exact (hG q).mp ((hYs' q).mp hq G hGclosed)

/-- The satisfaction relation of the structure `(U, E)`: a set of the model. -/
noncomputable def satSet (U E : V) : V := Classical.choose (M.exists_satSet U E)

theorem satSet_closed {U E q : V} (h : M.Step U E (M.asg U) (M.satSet U E) q) :
    M.mem q (M.satSet U E) := (Classical.choose_spec (M.exists_satSet U E)).1 q h

theorem satSet_inv {U E q : V} (h : M.mem q (M.satSet U E)) :
    M.Step U E (M.asg U) (M.satSet U E) q := (Classical.choose_spec (M.exists_satSet U E)).2 q h

/-- The facts in the satisfaction relation are exactly those given by one step from it. -/
theorem sat_char (U E : V) (b k x : M.Num) (s : V) :
    M.mem (M.fact (M.pairN (M.pairN k x) b).1 s) (M.satSet U E) ↔
      M.IsAsg U s ∧ M.Body U E (M.satSet U E) b k x s := by
  constructor
  · intro h
    obtain ⟨b', k', x', s', e, hs', hB⟩ := M.satSet_inv h
    obtain ⟨e1, e2⟩ := M.fact_inj e
    obtain ⟨e3, e4⟩ := M.pairN_inj (Subtype.ext e1)
    obtain ⟨e5, e6⟩ := M.pairN_inj e3
    rw [e2, e4, e5, e6]
    exact ⟨M.mem_asg.mp hs', hB⟩
  · rintro ⟨hs, hB⟩
    exact M.satSet_closed ⟨b, k, x, s, rfl, M.mem_asg.mpr hs, hB⟩

/-! ### Numerals used as tags -/

theorem tag_ne {a b : ℕ} (h : a ≠ b) : ((a : ℕ) : M.Num) ≠ ((b : ℕ) : M.Num) := fun e =>
  h (M.natCast_inj' a b e)

@[simp] theorem n01 : (0 : M.Num) ≠ 1 := by simp
@[simp] theorem n02 : (0 : M.Num) ≠ 2 := by simp
@[simp] theorem n03 : (0 : M.Num) ≠ 3 := by simp
@[simp] theorem n12 : (1 : M.Num) ≠ 2 := by simp
@[simp] theorem n13 : (1 : M.Num) ≠ 3 := by simp
@[simp] theorem n23 : (2 : M.Num) ≠ 3 := by simp
@[simp] theorem n10 : (1 : M.Num) ≠ 0 := M.n01.symm
@[simp] theorem n20 : (2 : M.Num) ≠ 0 := M.n02.symm
@[simp] theorem n30 : (3 : M.Num) ≠ 0 := M.n03.symm
@[simp] theorem n21 : (2 : M.Num) ≠ 1 := M.n12.symm
@[simp] theorem n31 : (3 : M.Num) ≠ 1 := M.n13.symm
@[simp] theorem n32 : (3 : M.Num) ≠ 2 := M.n23.symm

/-! ### The truth conditions, clause by clause -/

theorem body_tag {U E Y : V} {b k x : M.Num} {s : V} (h : M.Body U E Y b k x s) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 :=
  h.imp (fun h => h.1) (fun h => h.imp (fun h => h.1) (fun h => h.imp (fun h => h.1) (fun h => h.1)))

theorem body_1_0 {U E Y : V} {x : M.Num} {s : V} : M.Body U E Y 1 0 x s ↔
    ∃ r v w : M.Num, x = M.pairN r (M.pairN v w) ∧ M.RelH E r v w s := by
  simp [Body, B0]

theorem body_0_0 {U E Y : V} {x : M.Num} {s : V} : M.Body U E Y 0 0 x s ↔
    ∃ r v w : M.Num, x = M.pairN r (M.pairN v w) ∧ ¬ M.RelH E r v w s := by
  simp [Body, B0]

theorem body_1_1 {U E Y : V} {x : M.Num} {s : V} : M.Body U E Y 1 1 x s ↔ M.Fa Y x s := by
  simp [Body, B1]

theorem body_0_1 {U E Y : V} {x : M.Num} {s : V} : M.Body U E Y 0 1 x s ↔ M.Tr Y x s := by
  simp [Body, B1]

theorem body_1_2 {U E Y : V} {x : M.Num} {s : V} : M.Body U E Y 1 2 x s ↔
    ∃ φ ψ : M.Num, x = M.pairN φ ψ ∧ M.Tr Y φ s ∧ M.Tr Y ψ s := by
  simp [Body, B2]

theorem body_0_2 {U E Y : V} {x : M.Num} {s : V} : M.Body U E Y 0 2 x s ↔
    ∃ φ ψ : M.Num, x = M.pairN φ ψ ∧ ((M.Fa Y φ s ∧ (M.Tr Y ψ s ∨ M.Fa Y ψ s)) ∨
      ((M.Tr Y φ s ∨ M.Fa Y φ s) ∧ M.Fa Y ψ s)) := by
  simp [Body, B2]

theorem body_1_3 {U E Y : V} {x : M.Num} {s : V} : M.Body U E Y 1 3 x s ↔
    ∃ t n φ : M.Num, x = M.pairN (M.pairN t n) φ ∧
      ∀ a, M.mem (M.op t.1 a) U → M.Tr Y φ (M.updS s (M.pairN t n).1 a) := by
  simp [Body, B3]

theorem body_0_3 {U E Y : V} {x : M.Num} {s : V} : M.Body U E Y 0 3 x s ↔
    ∃ t n φ : M.Num, x = M.pairN (M.pairN t n) φ ∧
      (∀ a, M.mem (M.op t.1 a) U → M.Tr Y φ (M.updS s (M.pairN t n).1 a) ∨
        M.Fa Y φ (M.updS s (M.pairN t n).1 a)) ∧
      ∃ a, M.mem (M.op t.1 a) U ∧ M.Fa Y φ (M.updS s (M.pairN t n).1 a) := by
  simp [Body, B3]

/-! ## Coded formulas, truth and falsity -/

/-- The atomic formula "`v` is related to `w` by the relation number `r`". -/
noncomputable def cRel (r v w : M.Num) : M.Num := M.pairN 0 (M.pairN r (M.pairN v w))

/-- Negation. -/
noncomputable def cNeg (φ : M.Num) : M.Num := M.pairN 1 φ

/-- Conjunction. -/
noncomputable def cAnd (φ ψ : M.Num) : M.Num := M.pairN 2 (M.pairN φ ψ)

/-- Universal quantification over the variable `v`. -/
noncomputable def cAll (v φ : M.Num) : M.Num := M.pairN 3 (M.pairN v φ)

/-- The `n`-th variable of sort `t`. -/
noncomputable def vr (t n : M.Num) : M.Num := M.pairN t n

/-- The coded formula `c` is true in `(U, E)` at the assignment `s`. -/
def Holds (U E : V) (c : M.Num) (s : V) : Prop := M.Tr (M.satSet U E) c s

/-- The coded formula `c` is false in `(U, E)` at the assignment `s`. -/
def Fails (U E : V) (c : M.Num) (s : V) : Prop := M.Fa (M.satSet U E) c s

theorem holds_iff (U E : V) (k x : M.Num) (s : V) : M.Holds U E (M.pairN k x) s ↔
    M.IsAsg U s ∧ M.Body U E (M.satSet U E) 1 k x s := M.sat_char U E 1 k x s

theorem fails_iff (U E : V) (k x : M.Num) (s : V) : M.Fails U E (M.pairN k x) s ↔
    M.IsAsg U s ∧ M.Body U E (M.satSet U E) 0 k x s := M.sat_char U E 0 k x s

theorem code_of_holds {U E : V} {c : M.Num} {s : V} (h : M.Holds U E c s) :
    ∃ k x : M.Num, c = M.pairN k x := by
  obtain ⟨b, k, x, s', e, -, -⟩ := M.satSet_inv h
  exact ⟨k, x, (M.pairN_inj (Subtype.ext (M.fact_inj e).1)).1⟩

theorem holds_rel {U E : V} (r v w : M.Num) (s : V) :
    M.Holds U E (M.cRel r v w) s ↔ M.IsAsg U s ∧ M.RelH E r v w s := by
  unfold cRel
  rw [M.holds_iff, M.body_1_0]
  constructor
  · rintro ⟨hs, r', v', w', e, h⟩
    obtain ⟨e1, e2⟩ := M.pairN_inj e
    obtain ⟨e3, e4⟩ := M.pairN_inj e2
    rw [e1, e3, e4]
    exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩
    exact ⟨hs, r, v, w, rfl, h⟩

theorem fails_rel {U E : V} (r v w : M.Num) (s : V) :
    M.Fails U E (M.cRel r v w) s ↔ M.IsAsg U s ∧ ¬ M.RelH E r v w s := by
  unfold cRel
  rw [M.fails_iff, M.body_0_0]
  constructor
  · rintro ⟨hs, r', v', w', e, h⟩
    obtain ⟨e1, e2⟩ := M.pairN_inj e
    obtain ⟨e3, e4⟩ := M.pairN_inj e2
    rw [e1, e3, e4]
    exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩
    exact ⟨hs, r, v, w, rfl, h⟩

theorem holds_neg {U E : V} (φ : M.Num) (s : V) :
    M.Holds U E (M.cNeg φ) s ↔ M.IsAsg U s ∧ M.Fails U E φ s := by
  unfold cNeg
  rw [M.holds_iff, M.body_1_1]
  rfl

theorem fails_neg {U E : V} (φ : M.Num) (s : V) :
    M.Fails U E (M.cNeg φ) s ↔ M.IsAsg U s ∧ M.Holds U E φ s := by
  unfold cNeg
  rw [M.fails_iff, M.body_0_1]
  rfl

theorem holds_and {U E : V} (φ ψ : M.Num) (s : V) :
    M.Holds U E (M.cAnd φ ψ) s ↔ M.IsAsg U s ∧ M.Holds U E φ s ∧ M.Holds U E ψ s := by
  unfold cAnd
  rw [M.holds_iff, M.body_1_2]
  constructor
  · rintro ⟨hs, φ', ψ', e, h⟩
    obtain ⟨e1, e2⟩ := M.pairN_inj e
    rw [e1, e2]
    exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩
    exact ⟨hs, φ, ψ, rfl, h⟩

theorem fails_and {U E : V} (φ ψ : M.Num) (s : V) :
    M.Fails U E (M.cAnd φ ψ) s ↔ M.IsAsg U s ∧
      ((M.Fails U E φ s ∧ (M.Holds U E ψ s ∨ M.Fails U E ψ s)) ∨
       ((M.Holds U E φ s ∨ M.Fails U E φ s) ∧ M.Fails U E ψ s)) := by
  unfold cAnd
  rw [M.fails_iff, M.body_0_2]
  constructor
  · rintro ⟨hs, φ', ψ', e, h⟩
    obtain ⟨e1, e2⟩ := M.pairN_inj e
    rw [e1, e2]
    exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩
    exact ⟨hs, φ, ψ, rfl, h⟩

theorem holds_all {U E : V} (t n φ : M.Num) (s : V) :
    M.Holds U E (M.cAll (M.vr t n) φ) s ↔ M.IsAsg U s ∧
      ∀ a, M.mem (M.op t.1 a) U → M.Holds U E φ (M.updS s (M.vr t n).1 a) := by
  unfold cAll vr
  rw [M.holds_iff, M.body_1_3]
  constructor
  · rintro ⟨hs, t', n', φ', e, h⟩
    obtain ⟨e1, e2⟩ := M.pairN_inj e
    obtain ⟨e3, e4⟩ := M.pairN_inj e1
    rw [e3, e4, e2]
    exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩
    exact ⟨hs, t, n, φ, rfl, h⟩

theorem fails_all {U E : V} (t n φ : M.Num) (s : V) :
    M.Fails U E (M.cAll (M.vr t n) φ) s ↔ M.IsAsg U s ∧
      (∀ a, M.mem (M.op t.1 a) U → M.Holds U E φ (M.updS s (M.vr t n).1 a) ∨
        M.Fails U E φ (M.updS s (M.vr t n).1 a)) ∧
      ∃ a, M.mem (M.op t.1 a) U ∧ M.Fails U E φ (M.updS s (M.vr t n).1 a) := by
  unfold cAll vr
  rw [M.fails_iff, M.body_0_3]
  constructor
  · rintro ⟨hs, t', n', φ', e, h⟩
    obtain ⟨e1, e2⟩ := M.pairN_inj e
    obtain ⟨e3, e4⟩ := M.pairN_inj e1
    rw [e3, e4, e2]
    exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩
    exact ⟨hs, t, n, φ, rfl, h⟩

/-! ## No formula is both true and false -/

theorem cons_core {U E : V} (c : M.Num)
    (ih : ∀ m : M.Num, m + 1 ≤ c → ∀ s, ¬ (M.Holds U E m s ∧ M.Fails U E m s)) (s : V) :
    ¬ (M.Holds U E c s ∧ M.Fails U E c s) := by
  rintro ⟨hT, hF⟩
  obtain ⟨k, x, rfl⟩ := M.code_of_holds hT
  have hB := ((M.holds_iff U E k x s).mp hT).2
  have hB' := ((M.fails_iff U E k x s).mp hF).2
  rcases M.body_tag hB with rfl | rfl | rfl | rfl
  · rw [M.body_1_0] at hB
    rw [M.body_0_0] at hB'
    obtain ⟨r, v, w, e, h⟩ := hB
    obtain ⟨r', v', w', e', h'⟩ := hB'
    obtain ⟨e1, e2⟩ := M.pairN_inj (e.symm.trans e')
    obtain ⟨e3, e4⟩ := M.pairN_inj e2
    rw [← e1, ← e3, ← e4] at h'
    exact h' h
  · rw [M.body_1_1] at hB
    rw [M.body_0_1] at hB'
    exact ih x (M.lt_pairN_right x (le_refl 1)) s ⟨hB', hB⟩
  · rw [M.body_1_2] at hB
    rw [M.body_0_2] at hB'
    obtain ⟨φ, ψ, e, h1, h2⟩ := hB
    obtain ⟨φ', ψ', e', h'⟩ := hB'
    obtain ⟨e1, e2⟩ := M.pairN_inj (e.symm.trans e')
    rw [← e1, ← e2] at h'
    have hlt : x + 1 ≤ M.pairN 2 x := M.lt_pairN_right x one_le_two
    have hφ : φ ≤ x := by
      rw [e]
      exact M.le_pairN_left φ ψ
    have hψ : ψ ≤ x := by
      rw [e]
      exact M.le_pairN_right φ ψ
    rcases h' with ⟨hf, -⟩ | ⟨-, hf⟩
    · exact ih φ (le_trans (add_le_add hφ (le_refl 1)) hlt) s ⟨h1, hf⟩
    · exact ih ψ (le_trans (add_le_add hψ (le_refl 1)) hlt) s ⟨h2, hf⟩
  · rw [M.body_1_3] at hB
    rw [M.body_0_3] at hB'
    obtain ⟨t, n, φ, e, h⟩ := hB
    obtain ⟨t', n', φ', e', -, a, ha, hf⟩ := hB'
    obtain ⟨e1, e2⟩ := M.pairN_inj (e.symm.trans e')
    obtain ⟨e3, e4⟩ := M.pairN_inj e1
    rw [← e2, ← e3, ← e4] at hf
    rw [← e3] at ha
    have hlt : x + 1 ≤ M.pairN 3 x := M.lt_pairN_right x (M.le_def.mpr ⟨2, by norm_num⟩)
    have hφ : φ ≤ x := by
      rw [e]
      exact M.le_pairN_right _ φ
    exact ih φ (le_trans (add_le_add hφ (le_refl 1)) hlt) _ ⟨h a ha, hf⟩

def consFml : Fml :=
  .all 21 (Fml.imp (fLe 21 0) (.all 20 (.all 15 (.all 16 (Fml.imp
    (.and (fPairN 15 21 11) (fPairN 16 21 10)) (.neg (.and (fIn 8 15 20) (fIn 8 16 20))))))))

def σC : ℕ → ℕ :=
  σW [(6, 3), (7, 7), (18, 7), (8, 8), (20, 5), (110, 7), (111, 3), (112, 4), (113, 5), (115, 3),
    (116, 4), (117, 6), (118, 5)]

theorem sat_consFml {ad mu : V} (had : M.IsGraphOf₂ ad M.addN) (hmu : M.IsGraphOf₂ mu M.mulN)
    (Ys : V) (c : M.Num) :
    Sat M.mem M.isSet consFml (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 18 mu)
      8 Ys) 10 (0 : M.Num).1) 11 (1 : M.Num).1 |> fun ρ => Function.update ρ 0 c.1) ↔
    ∀ m : M.Num, m ≤ c → ∀ s, ¬ (M.Tr Ys m s ∧ M.Fa Ys m s) := by
  have h1 : Sat M.mem M.isSet consFml (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 18 mu)
      8 Ys) 10 (0 : M.Num).1) 11 (1 : M.Num).1 |> fun ρ => Function.update ρ 0 c.1) ↔
      ∀ m, M.LeRaw ad m c.1 → ∀ s w1 w0,
        (M.PairRaw ad mu m (1 : M.Num).1 w1 ∧ M.PairRaw ad mu m (0 : M.Num).1 w0) →
        ¬ (M.mem (M.fact w1 s) Ys ∧ M.mem (M.fact w0 s) Ys) := by
    simp [consFml, fLe, LeRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fPairN, M.sat_fApp3, M.sat_fIn,
      Function.update_apply]
  rw [h1]
  constructor
  · intro h m hm s
    exact h m.1 ((M.leRaw_iff had m c).mpr hm) s _ _
      ⟨(M.pairRaw_iff had hmu _ _ _).mpr ⟨m, 1, rfl, rfl, rfl⟩,
        (M.pairRaw_iff had hmu _ _ _).mpr ⟨m, 0, rfl, rfl, rfl⟩⟩
  · rintro h m ⟨d, hd, hmd⟩ s w1 w0 ⟨p1, p0⟩
    obtain ⟨M', D', hM', hD', hc⟩ := (had _ _ _).mp hmd
    have hle : M' ≤ c := M.le_def.mpr ⟨D', Subtype.ext hc⟩
    obtain ⟨X1, S1, hX1, hS1, hw1⟩ := (M.pairRaw_iff had hmu _ _ _).mp p1
    obtain ⟨X0, S0, hX0, hS0, hw0⟩ := (M.pairRaw_iff had hmu _ _ _).mp p0
    have e1 : X1 = M' := Subtype.ext (hX1.trans hM'.symm)
    have e0 : X0 = M' := Subtype.ext (hX0.trans hM'.symm)
    have f1 : S1 = 1 := Subtype.ext hS1
    have f0 : S0 = 0 := Subtype.ext hS0
    rw [hw1, hw0, e1, e0, f1, f0]
    exact h M' hle s

/-- **No coded formula is both true and false at an assignment.** -/
theorem consistent (U E : V) (c : M.Num) (s : V) :
    ¬ (M.Holds U E c s ∧ M.Fails U E c s) := by
  obtain ⟨ad, had⟩ := M.addN_natOp
  obtain ⟨mu, hmu⟩ := M.mulN_natOp
  have key := M.num_ind_fml σC consFml 0 rfl (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 6 M.nat) 7 ad) 18 mu)
      8 (M.satSet U E)) 10 (0 : M.Num).1) 11 (1 : M.Num).1)
    ((M.sat_consFml had hmu (M.satSet U E) 0).mpr (fun m hm s =>
      M.cons_core m (fun m' hm' => absurd (le_trans hm' hm) (fun h => M.succ_not_le_zero h)) s))
    (fun k ih => (M.sat_consFml had hmu (M.satSet U E) (M.nsucc k)).mpr (fun m hm s =>
      M.cons_core m (fun m' hm' s' => by
        rw [M.nsucc_eq_add_one] at hm
        exact (M.sat_consFml had hmu (M.satSet U E) k).mp ih m'
          (M.le_of_succ_le_succ (le_trans hm' hm)) s') s)) c
  exact (M.sat_consFml had hmu (M.satSet U E) c).mp key c (le_refl c) s

/-! ## Tarski's clauses -/

/-- `c` is a formula for the structure `(U, E)`: every assignment makes it true or false. -/
def Form (U E : V) (c : M.Num) : Prop :=
  ∀ s, M.IsAsg U s → M.Holds U E c s ∨ M.Fails U E c s

theorem form_rel {U E : V} (r v w : M.Num) : M.Form U E (M.cRel r v w) := fun s hs => by
  by_cases h : M.RelH E r v w s
  · exact Or.inl ((M.holds_rel r v w s).mpr ⟨hs, h⟩)
  · exact Or.inr ((M.fails_rel r v w s).mpr ⟨hs, h⟩)

theorem form_neg {U E : V} {φ : M.Num} (hφ : M.Form U E φ) : M.Form U E (M.cNeg φ) :=
  fun s hs => (hφ s hs).elim (fun h => Or.inr ((M.fails_neg φ s).mpr ⟨hs, h⟩))
    (fun h => Or.inl ((M.holds_neg φ s).mpr ⟨hs, h⟩))

theorem form_and {U E : V} {φ ψ : M.Num} (hφ : M.Form U E φ) (hψ : M.Form U E ψ) :
    M.Form U E (M.cAnd φ ψ) := fun s hs => by
  rcases hφ s hs with h1 | h1
  · rcases hψ s hs with h2 | h2
    · exact Or.inl ((M.holds_and φ ψ s).mpr ⟨hs, h1, h2⟩)
    · exact Or.inr ((M.fails_and φ ψ s).mpr ⟨hs, Or.inr ⟨Or.inl h1, h2⟩⟩)
  · exact Or.inr ((M.fails_and φ ψ s).mpr ⟨hs, Or.inl ⟨h1, hψ s hs⟩⟩)

theorem form_all {U E : V} {φ : M.Num} (hφ : M.Form U E φ) (t n : M.Num) :
    M.Form U E (M.cAll (M.vr t n) φ) := fun s hs => by
  have hs' : ∀ a, M.mem (M.op t.1 a) U → M.IsAsg U (M.updS s (M.vr t n).1 a) := fun a ha =>
    M.isAsg_updS hs t n ha
  by_cases h : ∀ a, M.mem (M.op t.1 a) U → M.Holds U E φ (M.updS s (M.vr t n).1 a)
  · exact Or.inl ((M.holds_all t n φ s).mpr ⟨hs, h⟩)
  · obtain ⟨a, hn⟩ := not_forall.mp h
    obtain ⟨ha, hnh⟩ := Classical.not_imp.mp hn
    exact Or.inr ((M.fails_all t n φ s).mpr ⟨hs, fun a ha => hφ _ (hs' a ha), a, ha,
      (hφ _ (hs' a ha)).resolve_left hnh⟩)

/-- **§3.1, satisfaction.** For every many-sorted set structure `(U, E)` of the model, with
`U` the set of pairs `⟨t, a⟩` (`a` in sort `t`) and `E` the set of triples `⟨r, a, b⟩` (`a`
related to `b` by the relation number `r`), the satisfaction relation `satSet U E` is a set of
the model. The codes built from atomic formulas by negation, conjunction and quantification
are formulas (decided by every assignment), whatever numbers of the model the indices are,
and truth obeys Tarski's clauses. -/
theorem satisfaction (U E : V) :
    (∀ r v w : M.Num, M.Form U E (M.cRel r v w)) ∧
    (∀ φ : M.Num, M.Form U E φ → M.Form U E (M.cNeg φ)) ∧
    (∀ φ ψ : M.Num, M.Form U E φ → M.Form U E ψ → M.Form U E (M.cAnd φ ψ)) ∧
    (∀ t n φ : M.Num, M.Form U E φ → M.Form U E (M.cAll (M.vr t n) φ)) ∧
    ∀ s, M.IsAsg U s →
      (∀ r v w : M.Num, M.Holds U E (M.cRel r v w) s ↔ M.RelH E r v w s) ∧
      (∀ φ : M.Num, M.Form U E φ → (M.Holds U E (M.cNeg φ) s ↔ ¬ M.Holds U E φ s)) ∧
      (∀ φ ψ : M.Num, M.Holds U E (M.cAnd φ ψ) s ↔ M.Holds U E φ s ∧ M.Holds U E ψ s) ∧
      (∀ t n φ : M.Num, M.Holds U E (M.cAll (M.vr t n) φ) s ↔
        ∀ a, M.mem (M.op t.1 a) U → M.Holds U E φ (M.updS s (M.vr t n).1 a)) := by
  refine ⟨M.form_rel, fun φ h => M.form_neg h, fun φ ψ h1 h2 => M.form_and h1 h2,
    fun t n φ h => M.form_all h t n, fun s hs => ⟨fun r v w => ?_, fun φ hφ => ?_,
      fun φ ψ => ?_, fun t n φ => ?_⟩⟩
  · rw [M.holds_rel]
    exact and_iff_right hs
  · rw [M.holds_neg]
    constructor
    · rintro ⟨-, hf⟩ ht
      exact M.consistent U E φ s ⟨ht, hf⟩
    · intro hn
      exact ⟨hs, (hφ s hs).resolve_left hn⟩
  · rw [M.holds_and]
    exact and_iff_right hs
  · rw [M.holds_all]
    exact and_iff_right hs

end Model

end NFUCut
