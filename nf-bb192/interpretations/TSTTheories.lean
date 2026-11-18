import NFTheories
import TFmExtra

set_option autoImplicit false

/-!
# The simple theory of types with infinity, `𝗧𝗦𝗧𝗜`

The theory is stated in a language with one sort: equality, membership, and a predicate
"has type `n`" for each natural number `n`. This is the usual way to write a theory with
infinitely many sorts in one-sorted logic: every quantifier is restricted to a type.

* **Typed formulas.** The formulas that may be used in comprehension are the well typed ones:
  `JensenNFU.TFm` with `TFm.Strat Γ φ`. In an atomic formula `x ∈ y` the type of `y` is one more
  than the type of `x`, in `x = y` the two types are equal, and each quantifier carries its type.
  `TFm.toFm` translates a typed formula into a formula of the language, with each quantifier
  restricted to its type.
* **Axioms of `𝗧𝗦𝗧𝗜`.**
  * the axioms of equality;
  * `extensionality n`: two objects of type `n + 1` with the same members of type `n` are equal;
  * `comprehension t Γ φ`, for `φ` well typed with a variable of type `t` and parameters of the
    types `Γ`: for all parameters of these types there is `y` of type `t + 1` such that, for all
    `x` of type `t`, `x ∈ y ↔ φ(x)`;
  * `infinity`: the universe of type `0` is not finite (`TFm.infFm 0`, which is
    `Axiom.universeInfinite` with the types `0`, `1`, `2`).

Nothing says that the types are disjoint, or that the members of an object of type `n + 1` have
type `n`: every axiom only speaks of objects through quantifiers restricted to a type.
-/

namespace FFL.FirstOrder

open JensenNFU (TFm)

/-! ### The language -/

namespace Language

namespace TST

inductive Rel : ℕ → Type
  | eq : Rel 2
  | mem : Rel 2
  | ty (n : ℕ) : Rel 1

end TST

/-- Language of type theory: equality, membership, and "has type `n`" for each `n`. -/
@[reducible]
def tst : Language where
  Func := fun _ ↦ Empty
  Rel := TST.Rel

notation "ℒₜₛₜ" => tst

namespace TST

instance (k) : DecidableEq (TST.Rel k) := fun a b =>
  match k, a, b with
  | _, .eq, .eq => isTrue rfl
  | _, .eq, .mem => isFalse (by simp)
  | _, .mem, .eq => isFalse (by simp)
  | _, .mem, .mem => isTrue rfl
  | _, .ty n, .ty m => decidable_of_iff (n = m) (by simp)

instance (k) : Encodable (TST.Rel k) where
  encode := fun x =>
    match x with
    | Rel.eq => 0
    | Rel.mem => 1
    | Rel.ty n => n
  decode := fun e =>
    match k, e with
    | 2, 0 => some Rel.eq
    | 2, 1 => some Rel.mem
    | 1, n => some (Rel.ty n)
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance : (ℒₜₛₜ).DecidableEq := ⟨fun _ ↦ inferInstanceAs (DecidableEq Empty), fun _ ↦ inferInstance⟩

instance : (ℒₜₛₜ).Encodable := ⟨fun _ ↦ inferInstanceAs (Encodable Empty), fun _ ↦ inferInstance⟩

instance : (ℒₜₛₜ).Eq := ⟨Rel.eq⟩

instance : (ℒₜₛₜ).Mem := ⟨Rel.mem⟩

instance : (ℒₜₛₜ).Relational := ⟨fun _ ↦ inferInstanceAs (IsEmpty Empty)⟩

end TST

end Language

/-! ### Typed formulas as formulas of the language -/

namespace TST

open Language.TST (Rel)

variable {ξ : Type*} {n : ℕ}

/-- `t` has type `k`. -/
def tyF (k : ℕ) (t : Semiterm ℒₜₛₜ ξ n) : Semiformula ℒₜₛₜ ξ n := Semiformula.rel (Rel.ty k) ![t]

/-- `t ∈ u`. -/
def memF (t u : Semiterm ℒₜₛₜ ξ n) : Semiformula ℒₜₛₜ ξ n := Semiformula.rel Rel.mem ![t, u]

/-- `t = u`. -/
def eqF (t u : Semiterm ℒₜₛₜ ξ n) : Semiformula ℒₜₛₜ ξ n := Semiformula.rel Rel.eq ![t, u]

/-- Translation of a typed formula. The variable with index `i` becomes the term `ρ i`, and a
quantifier of type `t` becomes a quantifier restricted to the objects of type `t`. -/
def toFm : TFm → {n : ℕ} → (ℕ → Semiterm ℒₜₛₜ ξ n) → Semiformula ℒₜₛₜ ξ n
  | .mem i j, _, ρ => memF (ρ i) (ρ j)
  | .eq i j, _, ρ => eqF (ρ i) (ρ j)
  | .neg φ, _, ρ => ∼(toFm φ ρ)
  | .and φ ψ, _, ρ => toFm φ ρ ⋏ toFm ψ ρ
  | .all t φ, _, ρ => ∀¹ (tyF t #0 🡒 toFm φ (TFm.scons #0 (fun i => Rew.bShift (ρ i))))

/-- The sentence that says a typed formula without free variables holds. -/
def sentence (φ : TFm) : Sentence ℒₜₛₜ :=
  Semiformula.univCl (toFm φ (fun i => (&i : Semiterm ℒₜₛₜ ℕ 0)))

/-- The parameters `&k, &(k+1), …` have the types listed in `Γ`. -/
def guard : List ℕ → ℕ → Semiformula ℒₜₛₜ ℕ 0
  | [], _ => ⊤
  | t :: Γ, k => tyF t &k ⋏ guard Γ (k + 1)

namespace Axiom

/-- Two objects of type `n + 1` with the same members of type `n` are equal. -/
def extensionality (n : ℕ) : Sentence ℒₜₛₜ :=
  sentence (.all (n + 1) (.all (n + 1)
    (TFm.imp (.all n (TFm.iff (.mem 0 1) (.mem 0 2))) (.eq 0 1))))

/-- For all parameters of the types `Γ` there is `y` of type `t + 1` such that for all `x` of
type `t`, `x ∈ y ↔ φ(x, parameters)`. In `φ` the variable `0` is `x` and the variables
`1, 2, …` are the parameters. -/
def comprehension (t : ℕ) (Γ : List ℕ) (φ : TFm) : Sentence ℒₜₛₜ :=
  Semiformula.univCl (guard Γ 0 🡒
    ∃¹ (tyF (t + 1) #0 ⋏ (∀¹ (tyF t #0 🡒
      ((memF #0 #1 🡒 toFm φ (TFm.scons #0 (fun i => &i))) ⋏
        (toFm φ (TFm.scons #0 (fun i => &i)) 🡒 memF #0 #1))))))

/-- The universe of type `0` is not finite. -/
def infinity : Sentence ℒₜₛₜ := sentence (TFm.infFm 0)

end Axiom

end TST

/-- **The simple theory of types with infinity.** -/
inductive TSTI : Theory ℒₜₛₜ
  | equality : ∀ φ ∈ 𝗘𝗤 ℒₜₛₜ, TSTI φ
  | extensionality (n : ℕ) : TSTI (TST.Axiom.extensionality n)
  | comprehension (t : ℕ) (Γ : List ℕ) (φ : TFm) :
      TFm.Strat (t :: Γ) φ → TSTI (TST.Axiom.comprehension t Γ φ)
  | infinity : TSTI TST.Axiom.infinity

notation "𝗧𝗦𝗧𝗜" => TSTI

instance : 𝗘𝗤 _ ⪯ 𝗧𝗦𝗧𝗜 := Entailment.WeakerThan.ofSubset TSTI.equality

/-! ### What the axioms say in a model -/

namespace TST

variable {M : Type*} [s : Tarski.Structure ℒₜₛₜ M]

/-- `a` has type `k` in the structure. -/
def Ty (k : ℕ) (a : M) : Prop := s.rel (Language.TST.Rel.ty k) ![a]

/-- `a ∈ b` in the structure. -/
def Mem (a b : M) : Prop := s.rel Language.TST.Rel.mem ![a, b]

/-- Satisfaction of a typed formula in the structure. -/
abbrev Holds (φ : TFm) (v : ℕ → M) : Prop := TFm.SatT (Ty (M := M)) Mem φ v

variable [Tarski.Structure.Eq ℒₜₛₜ M]

lemma eval_tyF {ξ : Type*} {n : ℕ} (k : ℕ) (t : Semiterm ℒₜₛₜ ξ n) (e : Fin n → M) (ε : ξ → M) :
    Semiformula.Eval e ε (tyF k t) ↔ Ty k (t.val e ε) := by
  simp only [tyF, Semiformula.eval_rel, Ty]
  have : (Semiterm.val e ε ∘ ![t]) = ![t.val e ε] := by
    funext i; fin_cases i; rfl
  rw [this]

lemma eval_memF {ξ : Type*} {n : ℕ} (t u : Semiterm ℒₜₛₜ ξ n) (e : Fin n → M) (ε : ξ → M) :
    Semiformula.Eval e ε (memF t u) ↔ Mem (t.val e ε) (u.val e ε) := by
  simp only [memF, Semiformula.eval_rel, Mem]
  have : (Semiterm.val e ε ∘ ![t, u]) = ![t.val e ε, u.val e ε] := by
    funext i; fin_cases i <;> rfl
  rw [this]

lemma eval_eqF {ξ : Type*} {n : ℕ} (t u : Semiterm ℒₜₛₜ ξ n) (e : Fin n → M) (ε : ξ → M) :
    Semiformula.Eval e ε (eqF t u) ↔ t.val e ε = u.val e ε := by
  simp only [eqF, Semiformula.eval_rel]
  have : (Semiterm.val e ε ∘ ![t, u]) = ![t.val e ε, u.val e ε] := by
    funext i; fin_cases i <;> rfl
  rw [this]
  exact (‹Tarski.Structure.Eq ℒₜₛₜ M›).1 _ _

/-- The translation of a typed formula means what the typed formula means. -/
lemma eval_toFm {ξ : Type*} (φ : TFm) :
    ∀ {n : ℕ} (ρ : ℕ → Semiterm ℒₜₛₜ ξ n) (e : Fin n → M) (ε : ξ → M),
      Semiformula.Eval e ε (toFm φ ρ) ↔ Holds φ (fun i => (ρ i).val e ε) := by
  induction φ with
  | mem i j => intro n ρ e ε; simp only [toFm, eval_memF, TFm.satT_mem]
  | eq i j => intro n ρ e ε; simp only [toFm, eval_eqF, TFm.satT_eq]
  | neg φ ih => intro n ρ e ε; simp [toFm, ih]
  | and φ ψ ih1 ih2 => intro n ρ e ε; simp [toFm, ih1, ih2]
  | all t φ ih =>
    intro n ρ e ε
    simp only [toFm, Semiformula.eval_all, LogicalConnective.HomClass.map_imply, eval_tyF, ih,
      TFm.satT_all, Semiterm.val_bvar]
    refine forall_congr' fun a => imp_congr (by simp) ?_
    have : (fun i => Semiterm.val (a :> e) ε
        (TFm.scons (#0 : Semiterm ℒₜₛₜ ξ (n + 1)) (fun i => Rew.bShift (ρ i)) i)) =
        TFm.scons a (fun i => (ρ i).val e ε) := by
      funext i
      cases i with
      | zero => simp
      | succ i => simp [Semiterm.val_bShift]
    rw [this]

lemma eval_guard (Γ : List ℕ) : ∀ (k : ℕ) (ε : ℕ → M),
    Semiformula.Eval ![] ε (guard Γ k) ↔ ∀ i (h : i < Γ.length), Ty Γ[i] (ε (k + i)) := by
  induction Γ with
  | nil => intro k ε; simp [guard]
  | cons t Γ ih =>
    intro k ε
    simp only [guard, LogicalConnective.HomClass.map_and, eval_tyF, ih, Semiterm.val_fvar]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => exact h0
      | succ i =>
        have := h1 i (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    · intro h
      refine ⟨h 0 (by simp), fun i hi => ?_⟩
      have := h (i + 1) (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

variable [Nonempty M] (hM : M↓[ℒₜₛₜ] ⊧* 𝗧𝗦𝗧𝗜)

include hM

/-- Extensionality in a model of `𝗧𝗦𝗧𝗜`. -/
theorem ext {n : ℕ} {x y : M} (hx : Ty (n + 1) x) (hy : Ty (n + 1) y)
    (h : ∀ z, Ty n z → (Mem z x ↔ Mem z y)) : x = y := by
  have := models_iff.mp (Theory.models M 𝗧𝗦𝗧𝗜 (TSTI.extensionality n))
  simp only [Axiom.extensionality, sentence, Semiformula.eval_univCl, eval_toFm] at this
  have h2 := this (fun _ => x)
  simp only [TFm.satT_all, TFm.satT_imp, TFm.satT_iff, TFm.satT_mem, TFm.satT_eq,
    TFm.scons_zero, TFm.scons_succ] at h2
  exact h2 y hy x hx fun z hz => h z hz

/-- Comprehension in a model of `𝗧𝗦𝗧𝗜`, for a well typed formula and parameters of the right
types. -/
theorem comp {t : ℕ} {Γ : List ℕ} {φ : TFm} (hφ : TFm.Strat (t :: Γ) φ) (v : ℕ → M)
    (hv : ∀ i (h : i < Γ.length), Ty Γ[i] (v i)) :
    ∃ y, Ty (t + 1) y ∧ ∀ x, Ty t x → (Mem x y ↔ Holds φ (TFm.scons x v)) := by
  have := models_iff.mp (Theory.models M 𝗧𝗦𝗧𝗜 (TSTI.comprehension t Γ φ hφ))
  simp only [Axiom.comprehension, Semiformula.eval_univCl, LogicalConnective.HomClass.map_imply,
    eval_guard, Semiformula.eval_ex, LogicalConnective.HomClass.map_and, eval_tyF,
    Semiformula.eval_all, eval_memF, eval_toFm, Semiterm.val_bvar] at this
  obtain ⟨y, hy, h⟩ := this v (fun i hi => by simpa using hv i hi)
  refine ⟨y, by simpa using hy, fun x hx => ?_⟩
  have e : (fun i => Semiterm.val (x :> ![y]) v
      (TFm.scons (#0 : Semiterm ℒₜₛₜ ℕ 2) (fun i => &i) i)) = TFm.scons x v := by
    funext i
    cases i with
    | zero => simp
    | succ i => simp
  have h' := h x (by simpa using hx)
  rw [e] at h'
  simpa using ⟨h'.1, h'.2⟩

/-- The universe of type `0` is not finite, in a model of `𝗧𝗦𝗧𝗜`. -/
theorem inf (v : ℕ → M) : Holds (TFm.infFm 0) v := by
  have := models_iff.mp (Theory.models M 𝗧𝗦𝗧𝗜 TSTI.infinity)
  simp only [Axiom.infinity, sentence, Semiformula.eval_univCl, eval_toFm] at this
  exact this v

end TST

namespace TST

variable {M : Type*} [s : Tarski.Structure ℒₜₛₜ M] [Tarski.Structure.Eq ℒₜₛₜ M] [Nonempty M]

/-- **A structure with extensionality, typed comprehension and a universe of type 0 that is not
finite is a model of `𝗧𝗦𝗧𝗜`.** -/
theorem models_of
    (hext : ∀ (n : ℕ) (x y : M), Ty (n + 1) x → Ty (n + 1) y →
      (∀ z, Ty n z → (Mem z x ↔ Mem z y)) → x = y)
    (hcomp : ∀ (t : ℕ) (Γ : List ℕ) (φ : TFm), TFm.Strat (t :: Γ) φ → ∀ v : ℕ → M,
      (∀ i (h : i < Γ.length), Ty Γ[i] (v i)) →
        ∃ y, Ty (t + 1) y ∧ ∀ x, Ty t x → (Mem x y ↔ Holds φ (TFm.scons x v)))
    (hinf : ∀ v : ℕ → M, Holds (TFm.infFm 0) v) : M↓[ℒₜₛₜ] ⊧* 𝗧𝗦𝗧𝗜 := by
  refine models_theory_iff.mpr fun φ hφ => ?_
  cases hφ with
  | equality φ hφ =>
    have : M↓[ℒₜₛₜ] ⊧* 𝗘𝗤 ℒₜₛₜ := Tarski.Structure.Eq.models_eqAxiom' ℒₜₛₜ M
    exact models_theory_iff.mp this φ hφ
  | extensionality n =>
    simp only [models_iff, Axiom.extensionality, sentence, Semiformula.eval_univCl, eval_toFm,
      TFm.satT_all, TFm.satT_imp, TFm.satT_iff, TFm.satT_mem, TFm.satT_eq, TFm.scons_zero,
      TFm.scons_succ]
    intro f a ha b hb h
    exact hext n b a hb ha h
  | comprehension t Γ φ hs =>
    simp only [models_iff, Axiom.comprehension, Semiformula.eval_univCl,
      LogicalConnective.HomClass.map_imply, eval_guard, Semiformula.eval_ex,
      LogicalConnective.HomClass.map_and, eval_tyF, Semiformula.eval_all, eval_memF, eval_toFm,
      Semiterm.val_bvar]
    intro v hv
    obtain ⟨y, hy, h⟩ := hcomp t Γ φ hs v (fun i hi => by simpa using hv i hi)
    refine ⟨y, by simpa using hy, fun x hx => ?_⟩
    have e : (fun i => Semiterm.val (x :> ![y]) v
        (TFm.scons (#0 : Semiterm ℒₜₛₜ ℕ 2) (fun i => &i) i)) = TFm.scons x v := by
      funext i
      cases i with
      | zero => simp
      | succ i => simp
    rw [e]
    have hh := h x (by simpa using hx)
    simpa using ⟨hh.mp, hh.mpr⟩
  | infinity =>
    simp only [models_iff, Axiom.infinity, sentence, Semiformula.eval_univCl, eval_toFm]
    exact hinf

end TST

end FFL.FirstOrder
