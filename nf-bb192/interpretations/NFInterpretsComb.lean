import NFInterpretsFn
import CombTheory

set_option autoImplicit false

/-!
# NF interprets CombNF

In a model of `𝗡𝗙`, with the application `AppR` of `NFFn.lean`:

* `KR a k`: `k` is the constant function with value `a`.
* `IsB b`: `b` is the value of the λ-term `λa.λb.λc. a (λy.c) (b c)` (`termB`), so
  `b · x · y · z = x · K(z) · (y · z)` (`b_spec`).
* `IsR r`: `r` is the empty set if `B` is not the empty set, and the universal set otherwise.
  Any object other than `B` would do.
* `IsQ q`: `q · f · x` is `B` if `f · x = x`, and `R` otherwise.

Each exists, by comprehension applied to its graph and the bijection between the universe and
the set of functions (`app_of_graph`), and is unique by extensionality.

**Result**: `nfInterpretsComb : 𝗡𝗙 ⊳ 𝗖𝗡𝗙`.
-/

namespace FFL.FirstOrder.SetTheory

namespace NFFn

open JensenNFU.TFm (scons scons_zero scons_succ)
open FNF (LTm HasLev)
open DirectTranslation

/-! ### More connectives for definitions with variables indexed by `ℕ` -/

namespace NDef

variable {γ : ℕ → ℕ} {R S : NRel}

/-- Negation. -/
def not (d : NDef γ R) : NDef γ (fun V _ env => ¬R V env) where
  φ := ∼d.φ
  strat := Semiformula.stratified_neg.mpr d.strat
  eval V _ env := by simp [d.eval]

/-- Disjunction. -/
def or (d : NDef γ R) (e : NDef γ S) : NDef γ (fun V _ env => R V env ∨ S V env) where
  φ := d.φ ⋎ e.φ
  strat := Semiformula.stratified_or.mpr ⟨d.strat, e.strat⟩
  eval V _ env := by simp [d.eval, e.eval]

/-- Implication. -/
def imp (d : NDef γ R) (e : NDef γ S) : NDef γ (fun V _ env => R V env → S V env) where
  φ := d.φ 🡒 e.φ
  strat := Semiformula.stratified_imp.mpr ⟨d.strat, e.strat⟩
  eval V _ env := by simp [d.eval, e.eval]

/-- Equivalence. -/
def iff (d : NDef γ R) (e : NDef γ S) : NDef γ (fun V _ env => (R V env ↔ S V env)) :=
  ((d.imp e).and (e.imp d)).congr fun _ _ _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- The formula with every variable replaced by one variable, as a formula in one variable. -/
def toOp (d : NDef γ R) : Semiformula.Operator ℒₛₑₜ 1 :=
  ⟨Rew.bind (![] : Fin 0 → Semiterm ℒₛₑₜ Empty 1) (fun _ : ℕ => (#0 : Semiterm ℒₛₑₜ Empty 1)) ▹
    d.φ⟩

lemma toOp_val {V : Type} [SetStructure V] (d : NDef γ R) (y : V) :
    d.toOp.val ![y] ↔ R V (fun _ => y) := by
  have e1 : (Semiterm.val ![y] (Empty.elim : Empty → V) ∘
      Rew.bind (![] : Fin 0 → Semiterm ℒₛₑₜ Empty 1)
        (fun _ : ℕ => (#0 : Semiterm ℒₛₑₜ Empty 1)) ∘ Semiterm.bvar) = (![] : Fin 0 → V) :=
    funext fun x => x.elim0
  have e2 : (Semiterm.val ![y] (Empty.elim : Empty → V) ∘
      Rew.bind (![] : Fin 0 → Semiterm ℒₛₑₜ Empty 1)
        (fun _ : ℕ => (#0 : Semiterm ℒₛₑₜ Empty 1)) ∘ Semiterm.fvar) = fun _ : ℕ => y := by
    funext i
    simp
  have h : Semiformula.Eval ![y] (Empty.elim : Empty → V)
      (Rew.bind (![] : Fin 0 → Semiterm ℒₛₑₜ Empty 1)
        (fun _ : ℕ => (#0 : Semiterm ℒₛₑₜ Empty 1)) ▹ d.φ) ↔ R V (fun _ => y) := by
    rw [Semiformula.eval_rew, e1, e2]
    exact d.eval V _
  exact h

end NDef

/-! ### The combinators as relations -/

section defs

variable {V : Type} [SetStructure V]

/-- `k` is the constant function with value `a`. -/
def KR (a k : V) : Prop := ∀ y w, AppR k y w ↔ w = a

/-- The λ-term `λa.λb.λc. a (λy.c) (b c)`. -/
def termB : LTm :=
  .lam (.lam (.lam (.app (.app (.var 2) (.lam (.var 1))) (.app (.var 1) (.var 0)))))

/-- `b` is the value of `termB`. -/
def IsB (b : V) : Prop := DenV termB (fun _ => b) b

/-- `r` is the empty set, or the universal set if `B` is the empty set. -/
def IsR (r : V) : Prop := ∃ b : V, IsB b ∧ ((IsFF b ∧ IsTT r) ∨ (¬IsFF b ∧ IsFF r))

/-- `y` is `B` if `f · x = x`, and `R` otherwise. -/
def QG (f x y : V) : Prop := (AppR f x x ∧ IsB y) ∨ (¬AppR f x x ∧ IsR y)

/-- `g = q · f`. -/
def QF (f g : V) : Prop := ∀ x y, AppR g x y ↔ QG f x y

/-- `q` is the fixed-point tester. -/
def IsQ (q : V) : Prop := ∀ f g, AppR q f g ↔ QF f g

end defs

theorem hasLev_termB (γ : ℕ → ℕ) : HasLev γ termB 3 :=
  ⟨2, rfl, 1, rfl, 0, rfl, ⟨rfl, 0, rfl, rfl⟩, rfl, rfl⟩

def kD : SDef ![8, 9] (fun _ _ v ↦ KR (v 0) (v 1)) :=
  (SDef.all 8 (SDef.all 8 ((appD.comp ![3, 1, 0] 0).iff (SDef.eq 0 2)))).congr
    fun _ _ _ => Iff.rfl

def isBN {γ : ℕ → ℕ} (j : ℕ) (hj : γ j = 11) : NDef γ (fun V _ env => IsB (env j)) :=
  ((denN termB (fun _ => 3) 3 (hasLev_termB _)).ren (fun _ => j) 0
    (fun i => by cases i <;> simp [hj])).congr fun _ _ _ => Iff.rfl

def isRN {γ : ℕ → ℕ} (j : ℕ) (hj : γ j = 11) : NDef γ (fun V _ env => IsR (env j)) :=
  ((NDef.ex (γ := fun _ => 11) 11 ((isBN 0 rfl).and
    (((NDef.ofS ffD ![0] 10 (fun i => by fin_cases i; rfl)).and
        (NDef.ofS ttD ![1] 10 (fun i => by fin_cases i; rfl))).or
      (((NDef.ofS ffD ![0] 10 (fun i => by fin_cases i; rfl)).not).and
        (NDef.ofS ffD ![1] 10 (fun i => by fin_cases i; rfl)))))).ren (fun _ => j) 0
    (fun i => by simp [hj])).congr fun _ _ _ => Iff.rfl

def qgN {γ : ℕ → ℕ} (jf jx jy : ℕ) (hf : γ jf = 12) (hx : γ jx = 11) (hy : γ jy = 11) :
    NDef γ (fun V _ env => QG (env jf) (env jx) (env jy)) :=
  (((NDef.ofS appD ![jf, jx, jx] 3 (fun i => by fin_cases i <;> simp [hf, hx])).and
      (isBN jy hy)).or
    (((NDef.ofS appD ![jf, jx, jx] 3 (fun i => by fin_cases i <;> simp [hf, hx])).not).and
      (isRN jy hy))).congr fun _ _ _ => Iff.rfl

def qfN {γ : ℕ → ℕ} (jf jg : ℕ) (hf : γ jf = 12) (hg : γ jg = 12) :
    NDef γ (fun V _ env => QF (env jf) (env jg)) :=
  (NDef.all 11 (NDef.all 11 ((NDef.ofS appD ![jg + 2, 1, 0] 3
    (fun i => by fin_cases i <;> simp [hg])).iff (qgN (jf + 2) 1 0 hf rfl rfl)))).congr
    fun _ _ _ => Iff.rfl

def isQN {γ : ℕ → ℕ} (j : ℕ) (hj : γ j = 13) : NDef γ (fun V _ env => IsQ (env j)) :=
  (NDef.all 12 (NDef.all 12 ((NDef.ofS appD ![j + 2, 1, 0] 4
    (fun i => by fin_cases i <;> simp [hj])).iff (qfN 1 0 rfl rfl)))).congr
    fun _ _ _ => Iff.rfl

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

/-! ### `K` -/

theorem exists_k (a : V) : ∃ k, KR a k := by
  obtain ⟨F, hF⟩ := (SDef.ex (τ := ![8, 8]) 8 (SDef.ex 8
    ((prD.comp ![2, 1, 0] 0).and (SDef.eq 0 3)))).comprehension ![a]
  exact app_of_graph (G := fun _ w => w = a) hF (fun _ => ⟨a, rfl⟩)
    (fun _ _ _ h h' => h.trans h'.symm)

theorem k_unique {a k k' : V} (h : KR a k) (h' : KR a k') : k = k' :=
  app_ext fun x y hxy => (h' x y).mpr ((h x y).mp hxy)

/-! ### `B` -/

theorem exists_b : ∃ b : V, IsB b := by
  obtain ⟨b, hb⟩ := denV_exists termB (fun _ => 3) 3 (hasLev_termB _)
    (fun _ => Classical.arbitrary V)
  exact ⟨b, hb⟩

theorem b_unique {b b' : V} (h : IsB b) (h' : IsB b') : b = b' :=
  denV_fun termB (fun _ => b) b b' h h'

/-- `B · x · y · z = x · K(z) · (y · z)`. -/
theorem b_spec {b x y z kz b1 b2 w u v : V} (hb : IsB b) (hk : KR z kz) (h1 : AppR b x b1)
    (h2 : AppR b1 y b2) (h3 : AppR b2 z w) (h4 : AppR x kz u) (h5 : AppR y z v) :
    AppR u v w := by
  obtain ⟨w1, d1, a1⟩ := hb x
  obtain ⟨w2, d2, a2⟩ := d1 y
  obtain ⟨w3, d3, a3⟩ := d2 z
  obtain ⟨u', v', ⟨xa, kc, hxa, hkc, hu⟩, ⟨ya, za, hya, hza, hv⟩, hw⟩ := d3
  have e1 : b1 = w1 := app_fun h1 a1
  subst e1
  have e2 : b2 = w2 := app_fun h2 a2
  subst e2
  have e3 : w = w3 := app_fun h3 a3
  subst e3
  have hxa' : xa = x := hxa
  have hya' : ya = y := hya
  have hza' : za = z := hza
  subst hxa' hya' hza'
  have hkc' : KR za kc := fun y' w' => by
    obtain ⟨w0, (hw0 : w0 = za), hk0⟩ := hkc y'
    subst hw0
    exact ⟨fun h => app_fun h hk0, fun h => by rw [h]; exact hk0⟩
  have e4 : kz = kc := k_unique hk hkc'
  subst e4
  have e5 : u = u' := app_fun h4 hu
  have e6 : v = v' := app_fun h5 hv
  rw [e5, e6]
  exact hw

/-! ### `R` -/

theorem exists_r : ∃ r : V, IsR r := by
  obtain ⟨b, hb⟩ := exists_b (V := V)
  by_cases h : IsFF b
  · obtain ⟨t, ht⟩ := exists_tt (V := V)
    exact ⟨t, b, hb, Or.inl ⟨h, ht⟩⟩
  · obtain ⟨t, ht⟩ := exists_ff (V := V)
    exact ⟨t, b, hb, Or.inr ⟨h, ht⟩⟩

theorem r_unique {r r' : V} (h : IsR r) (h' : IsR r') : r = r' := by
  obtain ⟨b, hb, h⟩ := h
  obtain ⟨b', hb', h'⟩ := h'
  have e := b_unique hb hb'
  subst e
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · exact tt_unique h2 h2'
  · exact absurd h1 h1'
  · exact absurd h1' h1
  · exact ff_unique h2 h2'

theorem b_ne_r {b r : V} (hb : IsB b) (hr : IsR r) : b ≠ r := by
  intro e
  obtain ⟨b', hb', h⟩ := hr
  have e' := b_unique hb hb'
  subst e' e
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact tt_ne_ff h2 h1 rfl
  · exact h1 h2

/-! ### `q` -/

theorem qg_total (f x : V) : ∃ y, QG f x y := by
  by_cases h : AppR f x x
  · obtain ⟨b, hb⟩ := exists_b (V := V)
    exact ⟨b, Or.inl ⟨h, hb⟩⟩
  · obtain ⟨r, hr⟩ := exists_r (V := V)
    exact ⟨r, Or.inr ⟨h, hr⟩⟩

theorem qg_fun {f x y y' : V} (h : QG f x y) (h' : QG f x y') : y = y' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · exact b_unique h2 h2'
  · exact absurd h1 h1'
  · exact absurd h1' h1
  · exact r_unique h2 h2'

theorem exists_qf (f : V) : ∃ g, QF f g := by
  obtain ⟨F, hF⟩ := (NDef.ex (γ := scons 11 (scons 12 (fun _ => 0))) 11 (NDef.ex 11
    ((NDef.ofS prD ![2, 1, 0] 3 (fun i => by fin_cases i <;> rfl)).and
      (qgN 3 1 0 rfl rfl rfl)))).comprehension (fun _ => f)
  exact app_of_graph (G := QG f) hF (qg_total f) (fun _ _ _ h h' => qg_fun h h')

theorem qf_unique {f g g' : V} (h : QF f g) (h' : QF f g') : g = g' :=
  app_ext fun x y hxy => (h' x y).mpr ((h x y).mp hxy)

theorem exists_q : ∃ q : V, IsQ q := by
  obtain ⟨F, hF⟩ := (NDef.ex (γ := scons 12 (fun _ => 0)) 12 (NDef.ex 12
    ((NDef.ofS prD ![2, 1, 0] 4 (fun i => by fin_cases i <;> rfl)).and
      (qfN 1 0 rfl rfl)))).comprehension (fun _ => Classical.arbitrary V)
  exact app_of_graph (G := QF) hF exists_qf (fun _ _ _ h h' => qf_unique h h')

theorem q_unique {q q' : V} (h : IsQ q) (h' : IsQ q') : q = q' :=
  app_ext fun x y hxy => (h' x y).mpr ((h x y).mp hxy)

theorem q_spec {q f g x y : V} (hq : IsQ q) (h1 : AppR q f g) (h2 : AppR g x y) : QG f x y :=
  ((hq f g).mp h1 x y).mp h2

end model

/-! ### The translation -/

namespace Comb

/-- The graphs of the function symbols of CombNF: the first variable is the value. -/
def combFunc : {k : ℕ} → (ℒᴄ).Func k → Semiformula.Operator ℒₛₑₜ (k + 1)
  | _, Language.Comb.Func.cB => (isBN (γ := fun _ => 11) 0 rfl).toOp
  | _, Language.Comb.Func.cR => (isRN (γ := fun _ => 11) 0 rfl).toOp
  | _, Language.Comb.Func.cQ => (isQN (γ := fun _ => 13) 0 rfl).toOp
  | _, Language.Comb.Func.K => ⟨(kD.comp (τ' := ![9, 8]) ![1, 0] 0).φ⟩
  | _, Language.Comb.Func.app => ⟨(appD.comp (τ' := ![8, 9, 8]) ![1, 2, 0] 0).φ⟩

/-- Equality is itself. -/
def combRel : {k : ℕ} → (ℒᴄ).Rel k → Semiformula.Operator ℒₛₑₜ k
  | _, Language.Comb.Rel.eq => Semiformula.Operator.Eq.eq

/-- What the graph of a function symbol says. -/
def Graph {V : Type} [SetStructure V] : {k : ℕ} → (ℒᴄ).Func k → V → (Fin k → V) → Prop
  | _, Language.Comb.Func.cB, y, _ => IsB y
  | _, Language.Comb.Func.cR, y, _ => IsR y
  | _, Language.Comb.Func.cQ, y, _ => IsQ y
  | _, Language.Comb.Func.K, y, v => KR (v 0) y
  | _, Language.Comb.Func.app, y, v => AppR (v 0) (v 1) y

lemma combFunc_val {V : Type} [SetStructure V] {k : ℕ} (f : (ℒᴄ).Func k) (y : V)
    (v : Fin k → V) : (combFunc f).val (y :> v) ↔ Graph f y v := by
  cases f with
  | cB =>
    have e : (y :> v) = ![y] := by funext i; fin_cases i; rfl
    rw [e]
    exact (isBN (γ := fun _ => 11) 0 rfl).toOp_val y
  | cR =>
    have e : (y :> v) = ![y] := by funext i; fin_cases i; rfl
    rw [e]
    exact (isRN (γ := fun _ => 11) 0 rfl).toOp_val y
  | cQ =>
    have e : (y :> v) = ![y] := by funext i; fin_cases i; rfl
    rw [e]
    exact (isQN (γ := fun _ => 13) 0 rfl).toOp_val y
  | K => exact (kD.comp (τ' := ![9, 8]) ![1, 0] 0).eval V (y :> v)
  | app => exact (appD.comp (τ' := ![8, 9, 8]) ![1, 2, 0] 0).eval V (y :> v)

theorem graph_existsUnique {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙]
    {k : ℕ} (f : (ℒᴄ).Func k) (v : Fin k → V) : ∃! y, Graph f y v := by
  cases f with
  | cB => exact let ⟨b, hb⟩ := exists_b (V := V); ⟨b, hb, fun _ h => b_unique h hb⟩
  | cR => exact let ⟨r, hr⟩ := exists_r (V := V); ⟨r, hr, fun _ h => r_unique h hr⟩
  | cQ => exact let ⟨q, hq⟩ := exists_q (V := V); ⟨q, hq, fun _ h => q_unique h hq⟩
  | K => exact let ⟨k', hk⟩ := exists_k (v 0); ⟨k', hk, fun _ h => k_unique h hk⟩
  | app => exact let ⟨y, hy⟩ := app_total (v 0) (v 1); ⟨y, hy, fun _ h => app_fun h hy⟩

/-- **The translation of the language of CombNF into `𝗡𝗙`.** -/
def combTranslation : DirectTranslation 𝗡𝗙 ℒᴄ where
  domain := ⟨⊤⟩
  rel := combRel
  func := combFunc
  domain_nonempty := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    simp [models_iff, Semiformula.Operator.val]
  func_defined {k} f := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    have h : ∀ v : Fin k → M, (∀ i, (⟨⊤⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![v i]) →
        ∃! y, (⟨⊤⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![y] ∧ (combFunc f).val (y :> v) := by
      intro v _
      obtain ⟨y, hy, huniq⟩ := graph_existsUnique f v
      exact ⟨y, ⟨by simp [Semiformula.Operator.val], (combFunc_val f y v).mpr hy⟩,
        fun y' hy' => huniq y' ((combFunc_val f y' v).mp hy'.2)⟩
    simpa [models_iff, Function.comp_def, Matrix.constant_eq_singleton] using h
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : combRel (Language.Eq.eq : (ℒᴄ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section combModel

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

local notation "N" => combTranslation.Model M

/-- An object of the model, as an object of the interpreted structure. -/
def toModel (a : M) : N :=
  ⟨a, by simp [DirectTranslation.Dom, combTranslation, Semiformula.Operator.val]⟩

omit [Nonempty M] hT in
theorem coe_inj {a b : N} (h : (a : M) = (b : M)) : a = b := by
  cases a; cases b; cases h; rfl

theorem app_iff (a b y : N) : y = CNF.App a b ↔ AppR (a : M) (b : M) (y : M) :=
  (Model.func_iff (f := Language.Comb.Func.app) (y := y) (v := ![a, b])).trans
    (combFunc_val Language.Comb.Func.app _ _)

theorem k_iff (a y : N) : y = CNF.Kf a ↔ KR (a : M) (y : M) :=
  (Model.func_iff (f := Language.Comb.Func.K) (y := y) (v := ![a])).trans
    (combFunc_val Language.Comb.Func.K _ _)

theorem b_iff (y : N) : y = CNF.Bc ↔ IsB (y : M) :=
  (Model.func_iff (f := Language.Comb.Func.cB) (y := y) (v := ![])).trans
    (combFunc_val Language.Comb.Func.cB _ _)

theorem r_iff (y : N) : y = CNF.Rc ↔ IsR (y : M) :=
  (Model.func_iff (f := Language.Comb.Func.cR) (y := y) (v := ![])).trans
    (combFunc_val Language.Comb.Func.cR _ _)

theorem q_iff (y : N) : y = CNF.Qc ↔ IsQ (y : M) :=
  (Model.func_iff (f := Language.Comb.Func.cQ) (y := y) (v := ![])).trans
    (combFunc_val Language.Comb.Func.cQ _ _)

/-- **In a model of `𝗡𝗙`, the interpreted structure is a model of `𝗖𝗡𝗙`.** -/
theorem combModel_models : (combTranslation.Model M)↓[ℒᴄ] ⊧* 𝗖𝗡𝗙 := by
  have hB : IsB ((CNF.Bc : N) : M) := (b_iff _).mp rfl
  have hR : IsR ((CNF.Rc : N) : M) := (r_iff _).mp rfl
  have hQ : IsQ ((CNF.Qc : N) : M) := (q_iff _).mp rfl
  have happ : ∀ a b : N, AppR (a : M) (b : M) ((CNF.App a b : N) : M) :=
    fun a b => (app_iff a b _).mp rfl
  have hK : ∀ a : N, KR (a : M) ((CNF.Kf a : N) : M) := fun a => (k_iff a _).mp rfl
  refine CNF.models_of ?_ ?_ ?_ ?_ ?_ ?_
  · intro x y
    exact ((app_iff (CNF.Kf x) y x).mpr ((hK x (y : M) (x : M)).mpr rfl)).symm
  · intro x y z
    exact (app_iff (CNF.App x (CNF.Kf z)) (CNF.App y z) _).mpr (b_spec hB (hK z)
      (happ CNF.Bc x) (happ _ y) (happ _ z) (happ x (CNF.Kf z)) (happ y z))
  · intro x y h
    have hxy : AppR (x : M) (y : M) (y : M) := (app_iff x y y).mp h.symm
    rcases q_spec hQ (happ CNF.Qc x) (happ _ y) with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact ((b_iff _).mpr h2)
    · exact absurd hxy h1
  · intro x y h
    have hxy : ¬AppR (x : M) (y : M) (y : M) := fun h' => h ((app_iff x y y).mpr h').symm
    rcases q_spec hQ (happ CNF.Qc x) (happ _ y) with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd h1 hxy
    · exact ((r_iff _).mpr h2)
  · intro f g h
    refine coe_inj (app_ext fun x y hxy => ?_)
    have h1 : toModel y = CNF.App f (toModel x) := (app_iff f (toModel x) (toModel y)).mpr hxy
    rw [h (toModel x)] at h1
    exact (app_iff g (toModel x) (toModel y)).mp h1
  · intro e
    exact b_ne_r hB hR (congrArg _ e)

end combModel

end Comb

/-- **`𝗡𝗙` interprets CombNF.** -/
instance nfInterpretsComb : 𝗡𝗙 ⊳ 𝗖𝗡𝗙 where
  trln := Comb.combTranslation
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp Comb.combModel_models φ hφ)

end NFFn

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.NFFn.nfInterpretsComb
