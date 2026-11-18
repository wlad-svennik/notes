import FnTheory

set_option autoImplicit false

/-!
# CombNF: the combinatory form of FunctionNF

The language `ℒᴄ` has application `f · x`, a unary function symbol `K`, three constants `B`,
`R`, `q`, and equality. `K` is a function symbol and not an object: `K(x)` is the constant
function with value `x`, one level above `x`.

**Axioms of `𝗖𝗡𝗙`.**

| Name | Statement |
|---|---|
| equality | the axioms of equality for `ℒᴄ` |
| `kAx` | `K(x) · y = x` |
| `bAx` | `B · x · y · z = x · K(z) · (y · z)` |
| `qTrue` | if `x · y = y` then `q · x · y = B` |
| `qFalse` | `x · y = y` or `q · x · y = R` |
| `extensionality` | if `f · x = g · x` for all `x`, then `f = g` |
| `nontrivial` | `B ≠ R` |

So `B` is the stratified form of the combinator `S`, `q` tests for a fixed point, and the two
truth values are `B` and `R`. There is no pairing.
-/

namespace FFL.FirstOrder

/-! ### The language -/

namespace Language

namespace Comb

inductive Func : ℕ → Type
  | cB : Func 0
  | cR : Func 0
  | cQ : Func 0
  | K : Func 1
  | app : Func 2

inductive Rel : ℕ → Type
  | eq : Rel 2

end Comb

/-- Language of CombNF: application, `K`, the constants `B`, `R`, `q`, and equality. -/
@[reducible]
def comb : Language where
  Func := Comb.Func
  Rel := Comb.Rel

notation "ℒᴄ" => comb

namespace Comb

instance (k) : DecidableEq (Comb.Func k) := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

instance (k) : DecidableEq (Comb.Rel k) := fun a b => by
  cases a; cases b; exact isTrue rfl

instance (k) : Encodable (Comb.Func k) where
  encode := fun x =>
    match x with
    | Func.cB => 0
    | Func.cR => 1
    | Func.cQ => 2
    | Func.K => 0
    | Func.app => 0
  decode := fun e =>
    match k, e with
    | 0, 0 => some Func.cB
    | 0, 1 => some Func.cR
    | 0, 2 => some Func.cQ
    | 1, 0 => some Func.K
    | 2, 0 => some Func.app
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance (k) : Encodable (Comb.Rel k) where
  encode := fun _ => 0
  decode := fun e =>
    match k, e with
    | 2, 0 => some Rel.eq
    | _, _ => none
  encodek := fun x => by rcases x; simp

instance : (ℒᴄ).DecidableEq := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : (ℒᴄ).Encodable := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : (ℒᴄ).Eq := ⟨Rel.eq⟩

end Comb

end Language

/-! ### Terms and axioms -/

namespace CNF

open Language.Comb

variable {ξ : Type*} {n : ℕ}

/-- `t = u`. -/
def eqF (t u : Semiterm ℒᴄ ξ n) : Semiformula ℒᴄ ξ n := Semiformula.rel Rel.eq ![t, u]

/-- `t · u`. -/
def appT (t u : Semiterm ℒᴄ ξ n) : Semiterm ℒᴄ ξ n := Semiterm.func Func.app ![t, u]

/-- `K(t)`. -/
def kT (t : Semiterm ℒᴄ ξ n) : Semiterm ℒᴄ ξ n := Semiterm.func Func.K ![t]

/-- `B`. -/
def bT : Semiterm ℒᴄ ξ n := Semiterm.func Func.cB ![]

/-- `R`. -/
def rT : Semiterm ℒᴄ ξ n := Semiterm.func Func.cR ![]

/-- `q`. -/
def qT : Semiterm ℒᴄ ξ n := Semiterm.func Func.cQ ![]

namespace Axiom

/-- `K(x) · y = x`. -/
def kAx : Sentence ℒᴄ := ∀¹ ∀¹ eqF (appT (kT #1) #0) #1

/-- `B · x · y · z = x · K(z) · (y · z)`. -/
def bAx : Sentence ℒᴄ :=
  ∀¹ ∀¹ ∀¹ eqF (appT (appT (appT bT #2) #1) #0) (appT (appT #2 (kT #0)) (appT #1 #0))

/-- If `x · y = y` then `q · x · y = B`. -/
def qTrue : Sentence ℒᴄ :=
  ∀¹ ∀¹ (eqF (appT #1 #0) #0 🡒 eqF (appT (appT qT #1) #0) bT)

/-- `x · y = y` or `q · x · y = R`. -/
def qFalse : Sentence ℒᴄ :=
  ∀¹ ∀¹ (eqF (appT #1 #0) #0 ⋎ eqF (appT (appT qT #1) #0) rT)

/-- If `f · x = g · x` for all `x`, then `f = g`. -/
def extensionality : Sentence ℒᴄ :=
  ∀¹ ∀¹ ((∀¹ eqF (appT #2 #0) (appT #1 #0)) 🡒 eqF #1 #0)

/-- `B ≠ R`. -/
def nontrivial : Sentence ℒᴄ := ∼(eqF bT rT)

end Axiom

end CNF

/-- **CombNF**: the combinatory form of FunctionNF. -/
inductive CombNF : Theory ℒᴄ
  | equality : ∀ φ ∈ 𝗘𝗤 ℒᴄ, CombNF φ
  | kAx : CombNF CNF.Axiom.kAx
  | bAx : CombNF CNF.Axiom.bAx
  | qTrue : CombNF CNF.Axiom.qTrue
  | qFalse : CombNF CNF.Axiom.qFalse
  | extensionality : CombNF CNF.Axiom.extensionality
  | nontrivial : CombNF CNF.Axiom.nontrivial

notation "𝗖𝗡𝗙" => CombNF

instance : 𝗘𝗤 _ ⪯ 𝗖𝗡𝗙 := Entailment.WeakerThan.ofSubset CombNF.equality

/-! ### What the axioms say in a structure -/

namespace CNF

open Language.Comb

variable {M : Type*} [s : Tarski.Structure ℒᴄ M]

/-- Application in the structure. -/
def App (a b : M) : M := s.func Func.app ![a, b]

/-- The constant function with value `a`. -/
def Kf (a : M) : M := s.func Func.K ![a]

/-- `B` in the structure. -/
def Bc : M := s.func Func.cB ![]

/-- `R` in the structure. -/
def Rc : M := s.func Func.cR ![]

/-- `q` in the structure. -/
def Qc : M := s.func Func.cQ ![]

variable {ξ : Type*}

lemma val_appT {n : ℕ} (t u : Semiterm ℒᴄ ξ n) (e : Fin n → M) (ε : ξ → M) :
    (appT t u).val e ε = App (t.val e ε) (u.val e ε) := by
  show s.func Func.app _ = s.func Func.app _
  congr 1
  funext i
  fin_cases i <;> rfl

lemma val_kT {n : ℕ} (t : Semiterm ℒᴄ ξ n) (e : Fin n → M) (ε : ξ → M) :
    (kT t).val e ε = Kf (t.val e ε) := by
  show s.func Func.K _ = s.func Func.K _
  congr 1
  funext i
  fin_cases i
  rfl

lemma val_bT {n : ℕ} (e : Fin n → M) (ε : ξ → M) : (bT : Semiterm ℒᴄ ξ n).val e ε = Bc := by
  show s.func Func.cB _ = s.func Func.cB _
  congr 1
  funext i
  exact i.elim0

lemma val_rT {n : ℕ} (e : Fin n → M) (ε : ξ → M) : (rT : Semiterm ℒᴄ ξ n).val e ε = Rc := by
  show s.func Func.cR _ = s.func Func.cR _
  congr 1
  funext i
  exact i.elim0

lemma val_qT {n : ℕ} (e : Fin n → M) (ε : ξ → M) : (qT : Semiterm ℒᴄ ξ n).val e ε = Qc := by
  show s.func Func.cQ _ = s.func Func.cQ _
  congr 1
  funext i
  exact i.elim0

variable [Tarski.Structure.Eq ℒᴄ M]

lemma eval_eqF {n : ℕ} (t u : Semiterm ℒᴄ ξ n) (e : Fin n → M) (ε : ξ → M) :
    Semiformula.Eval e ε (eqF t u) ↔ t.val e ε = u.val e ε := by
  simp only [eqF, Semiformula.eval_rel]
  have : (Semiterm.val e ε ∘ ![t, u]) = ![t.val e ε, u.val e ε] := by
    funext i; fin_cases i <;> rfl
  rw [this]
  exact (‹Tarski.Structure.Eq ℒᴄ M›).1 _ _

section model

variable [Nonempty M] (hM : M↓[ℒᴄ] ⊧* 𝗖𝗡𝗙)

include hM

local infixl:70 " ⬝ " => App

theorem k_app (x y : M) : Kf x ⬝ y = x := by
  have := models_iff.mp (Theory.models M 𝗖𝗡𝗙 CombNF.kAx)
  simp only [Axiom.kAx, Semiformula.eval_all, eval_eqF, val_appT, val_kT,
    Semiterm.val_bvar] at this
  exact this x y

theorem b_app (x y z : M) : Bc ⬝ x ⬝ y ⬝ z = x ⬝ Kf z ⬝ (y ⬝ z) := by
  have := models_iff.mp (Theory.models M 𝗖𝗡𝗙 CombNF.bAx)
  simp only [Axiom.bAx, Semiformula.eval_all, eval_eqF, val_appT, val_kT, val_bT,
    Semiterm.val_bvar] at this
  exact this x y z

theorem q_true {x y : M} (h : x ⬝ y = y) : Qc ⬝ x ⬝ y = Bc := by
  have := models_iff.mp (Theory.models M 𝗖𝗡𝗙 CombNF.qTrue)
  simp only [Axiom.qTrue, Semiformula.eval_all, LogicalConnective.HomClass.map_imply, eval_eqF,
    val_appT, val_qT, val_bT, Semiterm.val_bvar] at this
  exact this x y h

theorem q_false {x y : M} (h : x ⬝ y ≠ y) : Qc ⬝ x ⬝ y = Rc := by
  have := models_iff.mp (Theory.models M 𝗖𝗡𝗙 CombNF.qFalse)
  simp only [Axiom.qFalse, Semiformula.eval_all, LogicalConnective.HomClass.map_or, eval_eqF,
    val_appT, val_qT, val_rT, Semiterm.val_bvar] at this
  exact (this x y).resolve_left h

theorem c_ext {f g : M} (h : ∀ x, f ⬝ x = g ⬝ x) : f = g := by
  have := models_iff.mp (Theory.models M 𝗖𝗡𝗙 CombNF.extensionality)
  simp only [Axiom.extensionality, Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
    eval_eqF, val_appT, Semiterm.val_bvar] at this
  exact this f g h

theorem b_ne_r : (Bc : M) ≠ Rc := by
  have := models_iff.mp (Theory.models M 𝗖𝗡𝗙 CombNF.nontrivial)
  simpa [Axiom.nontrivial, eval_eqF, val_bT, val_rT] using this

end model

/-- **A structure with these six properties is a model of `𝗖𝗡𝗙`.** -/
theorem models_of [Nonempty M]
    (hk : ∀ x y : M, App (Kf x) y = x)
    (hb : ∀ x y z : M, App (App (App Bc x) y) z = App (App x (Kf z)) (App y z))
    (hq1 : ∀ x y : M, App x y = y → App (App Qc x) y = Bc)
    (hq2 : ∀ x y : M, App x y ≠ y → App (App Qc x) y = Rc)
    (hext : ∀ f g : M, (∀ x, App f x = App g x) → f = g)
    (hne : (Bc : M) ≠ Rc) : M↓[ℒᴄ] ⊧* 𝗖𝗡𝗙 := by
  refine models_theory_iff.mpr fun φ hφ => ?_
  cases hφ with
  | equality φ hφ =>
    have : M↓[ℒᴄ] ⊧* 𝗘𝗤 ℒᴄ := Tarski.Structure.Eq.models_eqAxiom' ℒᴄ M
    exact models_theory_iff.mp this φ hφ
  | kAx =>
    simp only [models_iff, Axiom.kAx, Semiformula.eval_all, eval_eqF, val_appT, val_kT,
      Semiterm.val_bvar]
    exact fun x y => hk x y
  | bAx =>
    simp only [models_iff, Axiom.bAx, Semiformula.eval_all, eval_eqF, val_appT, val_kT, val_bT,
      Semiterm.val_bvar]
    exact fun x y z => hb x y z
  | qTrue =>
    simp only [models_iff, Axiom.qTrue, Semiformula.eval_all,
      LogicalConnective.HomClass.map_imply, eval_eqF, val_appT, val_qT, val_bT,
      Semiterm.val_bvar]
    exact fun x y h => hq1 x y h
  | qFalse =>
    simp only [models_iff, Axiom.qFalse, Semiformula.eval_all,
      LogicalConnective.HomClass.map_or, eval_eqF, val_appT, val_qT, val_rT, Semiterm.val_bvar]
    exact fun x y => (em (App x y = y)).imp id (hq2 x y)
  | extensionality =>
    simp only [models_iff, Axiom.extensionality, Semiformula.eval_all,
      LogicalConnective.HomClass.map_imply, eval_eqF, val_appT, Semiterm.val_bvar]
    exact fun f g h => hext f g h
  | nontrivial =>
    simpa [models_iff, Axiom.nontrivial, eval_eqF, val_bT, val_rT] using hne

end CNF

end FFL.FirstOrder
