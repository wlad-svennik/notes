import NFTheories
import TFmExtra

set_option autoImplicit false

/-!
# FunctionNF: the stratified λ-calculus with full extensionality and without pairing

Everything is a function. The language `ℒλ` has application `f · x`, the equality test
`s ≐ t`, and two constants `⊤`, `⊥`, all as function symbols, and equality.

* **λ-terms** (`FNF.LTm`): variables (de Bruijn indices), application, abstraction, the equality
  test, `⊤`, `⊥`. They are not terms of the language: abstraction binds a variable.
* **Stratification** (`FNF.HasLev γ t ℓ`): the term `t` has level `ℓ` when its free variables have
  the levels `γ`.
  * in `t u`, `t` is one level above `u` and above `t u`;
  * `λx.t` is one level above `t`, and `x` has the level of `t`;
  * in `s ≐ t` the three levels are equal;
  * `⊤` and `⊥` have every level.
* **The value of a λ-term** (`FNF.Den t env v`): `v` is the value of `t` in the environment
  `env`. The value of `λx.t` is a `v` with `v · x = t` for all `x`. `FNF.denF` is the formula of
  `ℒλ` that says this.
* **Axioms of `𝗙𝗡𝗙`.**
  * the axioms of equality;
  * `extensionality`: if `f · x = g · x` for all `x`, then `f = g`;
  * `eqtTrue`, `eqtFalse`: `(a ≐ a) = ⊤`, and `(a ≐ b) = ⊥` when `a ≠ b`;
  * `nontrivial`: `⊤ ≠ ⊥`;
  * `abstraction t`, for every stratified λ-term `t`: `t` has a value, for all values of its free
    variables.

This is Holmes's stratified λ-calculus with full extensionality kept and with pairing,
projections and case expressions removed.
-/

namespace FFL.FirstOrder

open JensenNFU.TFm (scons scons_zero scons_succ)

/-! ### The language -/

namespace Language

namespace Fn

inductive Func : ℕ → Type
  | tt : Func 0
  | ff : Func 0
  | app : Func 2
  | eqt : Func 2

inductive Rel : ℕ → Type
  | eq : Rel 2

end Fn

/-- Language of FunctionNF: application, the equality test, `⊤`, `⊥`, and equality. -/
@[reducible]
def fn : Language where
  Func := Fn.Func
  Rel := Fn.Rel

notation "ℒλ" => fn

namespace Fn

instance (k) : DecidableEq (Fn.Func k) := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

instance (k) : DecidableEq (Fn.Rel k) := fun a b => by
  cases a; cases b; exact isTrue rfl

instance (k) : Encodable (Fn.Func k) where
  encode := fun x =>
    match x with
    | Func.tt => 0
    | Func.ff => 1
    | Func.app => 0
    | Func.eqt => 1
  decode := fun e =>
    match k, e with
    | 0, 0 => some Func.tt
    | 0, 1 => some Func.ff
    | 2, 0 => some Func.app
    | 2, 1 => some Func.eqt
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance (k) : Encodable (Fn.Rel k) where
  encode := fun _ => 0
  decode := fun e =>
    match k, e with
    | 2, 0 => some Rel.eq
    | _, _ => none
  encodek := fun x => by rcases x; simp

instance : (ℒλ).DecidableEq := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : (ℒλ).Encodable := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : (ℒλ).Eq := ⟨Rel.eq⟩

end Fn

end Language

/-! ### λ-terms and their stratification -/

namespace FNF

/-- λ-terms, with de Bruijn indices. -/
inductive LTm : Type
  | var (i : ℕ) : LTm
  | app (s t : LTm) : LTm
  | lam (t : LTm) : LTm
  | eqt (s t : LTm) : LTm
  | tt : LTm
  | ff : LTm

/-- `HasLev γ t ℓ`: the term `t` is stratified and has level `ℓ`, where `γ` gives the levels of
its free variables. -/
def HasLev : (ℕ → ℕ) → LTm → ℕ → Prop
  | γ, .var i, ℓ => γ i = ℓ
  | γ, .app s t, ℓ => HasLev γ s (ℓ + 1) ∧ HasLev γ t ℓ
  | γ, .lam t, ℓ => ∃ k, ℓ = k + 1 ∧ HasLev (scons k γ) t k
  | γ, .eqt s t, ℓ => HasLev γ s ℓ ∧ HasLev γ t ℓ
  | _, .tt, _ => True
  | _, .ff, _ => True

open Language.Fn

variable {ξ : Type*} {n : ℕ}

/-- `t = u`. -/
def eqF (t u : Semiterm ℒλ ξ n) : Semiformula ℒλ ξ n := Semiformula.rel Rel.eq ![t, u]

/-- `t · u`. -/
def appT (t u : Semiterm ℒλ ξ n) : Semiterm ℒλ ξ n := Semiterm.func Func.app ![t, u]

/-- `t ≐ u`. -/
def eqtT (t u : Semiterm ℒλ ξ n) : Semiterm ℒλ ξ n := Semiterm.func Func.eqt ![t, u]

/-- `⊤`. -/
def ttT : Semiterm ℒλ ξ n := Semiterm.func Func.tt ![]

/-- `⊥`. -/
def ffT : Semiterm ℒλ ξ n := Semiterm.func Func.ff ![]

/-- `denF t ρ v`: the formula "`v` is the value of the λ-term `t`", where the variable with
index `i` is the term `ρ i`. -/
def denF : LTm → {n : ℕ} → (ℕ → Semiterm ℒλ ξ n) → Semiterm ℒλ ξ n → Semiformula ℒλ ξ n
  | .var i, _, ρ, v => eqF v (ρ i)
  | .app s t, _, ρ, v => ∃¹ ∃¹ (denF s (fun i => Rew.bShift (Rew.bShift (ρ i))) #1 ⋏
      (denF t (fun i => Rew.bShift (Rew.bShift (ρ i))) #0 ⋏
        eqF (Rew.bShift (Rew.bShift v)) (appT #1 #0)))
  | .lam t, _, ρ, v => ∀¹ ∃¹ (denF t (scons #1 (fun i => Rew.bShift (Rew.bShift (ρ i)))) #0 ⋏
      eqF (appT (Rew.bShift (Rew.bShift v)) #1) #0)
  | .eqt s t, _, ρ, v => ∃¹ ∃¹ (denF s (fun i => Rew.bShift (Rew.bShift (ρ i))) #1 ⋏
      (denF t (fun i => Rew.bShift (Rew.bShift (ρ i))) #0 ⋏
        eqF (Rew.bShift (Rew.bShift v)) (eqtT #1 #0)))
  | .tt, _, _, v => eqF v ttT
  | .ff, _, _, v => eqF v ffT

namespace Axiom

/-- If `f · x = g · x` for all `x`, then `f = g`. -/
def extensionality : Sentence ℒλ :=
  ∀¹ ∀¹ ((∀¹ eqF (appT #2 #0) (appT #1 #0)) 🡒 eqF #1 #0)

/-- `(a ≐ a) = ⊤`. -/
def eqtTrue : Sentence ℒλ := ∀¹ eqF (eqtT #0 #0) ttT

/-- If `a ≠ b` then `(a ≐ b) = ⊥`. -/
def eqtFalse : Sentence ℒλ := ∀¹ ∀¹ (eqF #1 #0 ⋎ eqF (eqtT #1 #0) ffT)

/-- `⊤ ≠ ⊥`. -/
def nontrivial : Sentence ℒλ := ∼(eqF ttT ffT)

/-- The λ-term `t` has a value, for all values of its free variables. -/
def abstraction (t : LTm) : Sentence ℒλ :=
  Semiformula.univCl (∃¹ denF t (fun i => (&i : Semiterm ℒλ ℕ 1)) #0)

end Axiom

end FNF

/-- **FunctionNF**: the stratified λ-calculus with full extensionality and without pairing. -/
inductive FunctionNF : Theory ℒλ
  | equality : ∀ φ ∈ 𝗘𝗤 ℒλ, FunctionNF φ
  | extensionality : FunctionNF FNF.Axiom.extensionality
  | eqtTrue : FunctionNF FNF.Axiom.eqtTrue
  | eqtFalse : FunctionNF FNF.Axiom.eqtFalse
  | nontrivial : FunctionNF FNF.Axiom.nontrivial
  | abstraction (t : FNF.LTm) (γ : ℕ → ℕ) (ℓ : ℕ) :
      FNF.HasLev γ t ℓ → FunctionNF (FNF.Axiom.abstraction t)

notation "𝗙𝗡𝗙" => FunctionNF

instance : 𝗘𝗤 _ ⪯ 𝗙𝗡𝗙 := Entailment.WeakerThan.ofSubset FunctionNF.equality

/-! ### What the axioms say in a structure -/

namespace FNF

open Language.Fn

variable {M : Type*} [s : Tarski.Structure ℒλ M]

/-- Application in the structure. -/
def App (a b : M) : M := s.func Func.app ![a, b]

/-- The equality test in the structure. -/
def EqT (a b : M) : M := s.func Func.eqt ![a, b]

/-- `⊤` in the structure. -/
def TT : M := s.func Func.tt ![]

/-- `⊥` in the structure. -/
def FF : M := s.func Func.ff ![]

/-- `Den t env v`: `v` is the value of the λ-term `t` in the environment `env`. -/
def Den : LTm → (ℕ → M) → M → Prop
  | .var i, env, v => v = env i
  | .app s t, env, v => ∃ a b, Den s env a ∧ Den t env b ∧ v = App a b
  | .lam t, env, v => ∀ x, ∃ w, Den t (scons x env) w ∧ App v x = w
  | .eqt s t, env, v => ∃ a b, Den s env a ∧ Den t env b ∧ v = EqT a b
  | .tt, _, v => v = TT
  | .ff, _, v => v = FF

variable {ξ : Type*}

lemma val_appT {n : ℕ} (t u : Semiterm ℒλ ξ n) (e : Fin n → M) (ε : ξ → M) :
    (appT t u).val e ε = App (t.val e ε) (u.val e ε) := by
  show s.func Func.app _ = s.func Func.app _
  congr 1
  funext i
  fin_cases i <;> rfl

lemma val_eqtT {n : ℕ} (t u : Semiterm ℒλ ξ n) (e : Fin n → M) (ε : ξ → M) :
    (eqtT t u).val e ε = EqT (t.val e ε) (u.val e ε) := by
  show s.func Func.eqt _ = s.func Func.eqt _
  congr 1
  funext i
  fin_cases i <;> rfl

lemma val_ttT {n : ℕ} (e : Fin n → M) (ε : ξ → M) : (ttT : Semiterm ℒλ ξ n).val e ε = TT := by
  show s.func Func.tt _ = s.func Func.tt _
  congr 1
  funext i
  exact i.elim0

lemma val_ffT {n : ℕ} (e : Fin n → M) (ε : ξ → M) : (ffT : Semiterm ℒλ ξ n).val e ε = FF := by
  show s.func Func.ff _ = s.func Func.ff _
  congr 1
  funext i
  exact i.elim0

variable [Tarski.Structure.Eq ℒλ M]

lemma eval_eqF {n : ℕ} (t u : Semiterm ℒλ ξ n) (e : Fin n → M) (ε : ξ → M) :
    Semiformula.Eval e ε (eqF t u) ↔ t.val e ε = u.val e ε := by
  simp only [eqF, Semiformula.eval_rel]
  have : (Semiterm.val e ε ∘ ![t, u]) = ![t.val e ε, u.val e ε] := by
    funext i; fin_cases i <;> rfl
  rw [this]
  exact (‹Tarski.Structure.Eq ℒλ M›).1 _ _

/-- The formula `denF t ρ v` says that `v` is the value of `t`. -/
lemma eval_denF (t : LTm) :
    ∀ {n : ℕ} (ρ : ℕ → Semiterm ℒλ ξ n) (v : Semiterm ℒλ ξ n) (e : Fin n → M) (ε : ξ → M),
      Semiformula.Eval e ε (denF t ρ v) ↔ Den t (fun i => (ρ i).val e ε) (v.val e ε) := by
  induction t with
  | var i => intro n ρ v e ε; simp only [denF, eval_eqF, Den]
  | app s t ihs iht =>
    intro n ρ v e ε
    simp only [denF, Semiformula.eval_ex, LogicalConnective.HomClass.map_and, ihs, iht, eval_eqF,
      val_appT, Semiterm.val_bvar, Semiterm.val_bShift, Den]
    rfl
  | lam t ih =>
    intro n ρ v e ε
    simp only [denF, Semiformula.eval_all, Semiformula.eval_ex,
      LogicalConnective.HomClass.map_and, ih, eval_eqF, val_appT, Semiterm.val_bvar,
      Semiterm.val_bShift, Den]
    refine forall_congr' fun x => exists_congr fun w => and_congr ?_ Iff.rfl
    have : (fun i => Semiterm.val (w :> x :> e) ε
        (scons (#1 : Semiterm ℒλ ξ (n + 1 + 1)) (fun i => Rew.bShift (Rew.bShift (ρ i))) i)) =
        scons x (fun i => (ρ i).val e ε) := by
      funext i
      cases i with
      | zero => rfl
      | succ i => simp [Semiterm.val_bShift]
    rw [this]
    rfl
  | eqt s t ihs iht =>
    intro n ρ v e ε
    simp only [denF, Semiformula.eval_ex, LogicalConnective.HomClass.map_and, ihs, iht, eval_eqF,
      val_eqtT, Semiterm.val_bvar, Semiterm.val_bShift, Den]
    rfl
  | tt => intro n ρ v e ε; simp only [denF, eval_eqF, val_ttT, Den]
  | ff => intro n ρ v e ε; simp only [denF, eval_eqF, val_ffT, Den]

section model

variable [Nonempty M] (hM : M↓[ℒλ] ⊧* 𝗙𝗡𝗙)

include hM

/-- Extensionality in a model of `𝗙𝗡𝗙`. -/
theorem fn_ext {f g : M} (h : ∀ x, App f x = App g x) : f = g := by
  have := models_iff.mp (Theory.models M 𝗙𝗡𝗙 FunctionNF.extensionality)
  simp only [Axiom.extensionality, Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
    eval_eqF, val_appT, Semiterm.val_bvar] at this
  exact this f g h

theorem eqT_self (a : M) : EqT a a = TT := by
  have := models_iff.mp (Theory.models M 𝗙𝗡𝗙 FunctionNF.eqtTrue)
  simp only [Axiom.eqtTrue, Semiformula.eval_all, eval_eqF, val_eqtT, val_ttT,
    Semiterm.val_bvar] at this
  exact this a

theorem eqT_ne {a b : M} (h : a ≠ b) : EqT a b = FF := by
  have := models_iff.mp (Theory.models M 𝗙𝗡𝗙 FunctionNF.eqtFalse)
  simp only [Axiom.eqtFalse, Semiformula.eval_all, LogicalConnective.HomClass.map_or, eval_eqF,
    val_eqtT, val_ffT, Semiterm.val_bvar] at this
  exact (this a b).resolve_left h

theorem tt_ne_ff : (TT : M) ≠ FF := by
  have := models_iff.mp (Theory.models M 𝗙𝗡𝗙 FunctionNF.nontrivial)
  simpa [Axiom.nontrivial, eval_eqF, val_ttT, val_ffT] using this

/-- A stratified λ-term has a value. -/
theorem fn_abs {γ : ℕ → ℕ} {t : LTm} {ℓ : ℕ} (h : HasLev γ t ℓ) (env : ℕ → M) :
    ∃ v, Den t env v := by
  have := models_iff.mp (Theory.models M 𝗙𝗡𝗙 (FunctionNF.abstraction t γ ℓ h))
  simp only [Axiom.abstraction, Semiformula.eval_univCl, Semiformula.eval_ex, eval_denF,
    Semiterm.val_fvar, Semiterm.val_bvar] at this
  obtain ⟨v, hv⟩ := this env
  exact ⟨v, by simpa using hv⟩

end model

/-- **A structure with these five properties is a model of `𝗙𝗡𝗙`.** -/
theorem models_of [Nonempty M]
    (hext : ∀ f g : M, (∀ x, App f x = App g x) → f = g)
    (h1 : ∀ a : M, EqT a a = TT)
    (h2 : ∀ a b : M, a ≠ b → EqT a b = FF)
    (h3 : (TT : M) ≠ FF)
    (habs : ∀ (t : LTm) (γ : ℕ → ℕ) (ℓ : ℕ), HasLev γ t ℓ → ∀ env : ℕ → M, ∃ v, Den t env v) :
    M↓[ℒλ] ⊧* 𝗙𝗡𝗙 := by
  refine models_theory_iff.mpr fun φ hφ => ?_
  cases hφ with
  | equality φ hφ =>
    have : M↓[ℒλ] ⊧* 𝗘𝗤 ℒλ := Tarski.Structure.Eq.models_eqAxiom' ℒλ M
    exact models_theory_iff.mp this φ hφ
  | extensionality =>
    simp only [models_iff, Axiom.extensionality, Semiformula.eval_all,
      LogicalConnective.HomClass.map_imply, eval_eqF, val_appT, Semiterm.val_bvar]
    exact fun f g h => hext f g h
  | eqtTrue =>
    simp only [models_iff, Axiom.eqtTrue, Semiformula.eval_all, eval_eqF, val_eqtT, val_ttT,
      Semiterm.val_bvar]
    exact fun a => h1 a
  | eqtFalse =>
    simp only [models_iff, Axiom.eqtFalse, Semiformula.eval_all,
      LogicalConnective.HomClass.map_or, eval_eqF, val_eqtT, val_ffT, Semiterm.val_bvar]
    exact fun a b => (em (a = b)).imp id (h2 a b)
  | nontrivial =>
    simpa [models_iff, Axiom.nontrivial, eval_eqF, val_ttT, val_ffT] using h3
  | abstraction t γ ℓ h =>
    simp only [models_iff, Axiom.abstraction, Semiformula.eval_univCl, Semiformula.eval_ex,
      eval_denF, Semiterm.val_fvar, Semiterm.val_bvar]
    intro env
    obtain ⟨v, hv⟩ := habs t γ ℓ h env
    exact ⟨v, by simpa using hv⟩

end FNF

end FFL.FirstOrder
