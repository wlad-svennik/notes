import CombTheory
import FnInterpretsNFU

set_option autoImplicit false

/-!
# CombNF interprets FunctionNF

In a model of `𝗖𝗡𝗙` every stratified λ-term of FunctionNF has a value, when `⊤` is read as `B`,
`⊥` as `R`, and `s ≐ t` as `q · K(s) · t`. This is bracket abstraction for stratified terms.

* `Ic = B (B B B) B` is the identity (`i_app`).
* A *normal term* (`NT`) is built by application from leaves `K^m(a)`, where `a` is a variable
  or a constant. `kpush` is `K` applied to a normal term, pushed down to the leaves by
  `K(u v) = B K(u) K(v)` (`nval_kpush`, which uses extensionality).
* `abs j T` abstracts variable `0` from the normal term `T`, where the variable occurs as
  `K^j(x)` at the root and as `K^(j+1)(x)` one step into a function position:
  `abs j (U V) = B (abs (j+1) U) (abs j V)`. `abs_spec`: `abs j T · K^j(x) = T`. The condition
  on the occurrences of the variable (`Good`) follows from stratification (`nlev_good`).
* `tr` translates λ-terms into normal terms; `den_tr`: the value of `tr t` is a value of `t`.
* **Results**: `combInterpretsFn : 𝗖𝗡𝗙 ⊳ 𝗙𝗡𝗙`, and by composition `combInterpretsNFUI` and
  `combInterpretsNF`.
-/

namespace FFL.FirstOrder.CNF

open JensenNFU.TFm (scons scons_zero scons_succ)
open FNF (LTm HasLev)
open DirectTranslation

/-! ### Normal terms -/

/-- A variable or one of the three constants. -/
inductive Atom : Type
  | var (i : ℕ) : Atom
  | cB : Atom
  | cR : Atom
  | cQ : Atom

/-- Normal terms: applications of leaves `K^m(a)`. -/
inductive NT : Type
  | leaf (m : ℕ) (a : Atom) : NT
  | app (s t : NT) : NT

/-- The identity `B (B B B) B`, as a normal term. -/
def iT : NT :=
  .app (.app (.leaf 0 .cB) (.app (.app (.leaf 0 .cB) (.leaf 0 .cB)) (.leaf 0 .cB))) (.leaf 0 .cB)

/-- `K` applied to a normal term, pushed down to the leaves. -/
def kpush : NT → NT
  | .leaf m a => .leaf (m + 1) a
  | .app s t => .app (.app (.leaf 0 .cB) (kpush s)) (kpush t)

/-- Abstraction of variable `0`, occurring as `K^j` of itself at the root. The other variables
move down by one. -/
def abs : ℕ → NT → NT
  | _, .leaf _ (.var 0) => iT
  | _, .leaf m (.var (i + 1)) => .leaf (m + 1) (.var i)
  | _, .leaf m .cB => .leaf (m + 1) .cB
  | _, .leaf m .cR => .leaf (m + 1) .cR
  | _, .leaf m .cQ => .leaf (m + 1) .cQ
  | j, .app s t => .app (.app (.leaf 0 .cB) (abs (j + 1) s)) (abs j t)

/-- Every occurrence of variable `0` is under the right number of `K`s. -/
def Good : ℕ → NT → Prop
  | j, .leaf m (.var 0) => m = j
  | _, .leaf _ (.var (_ + 1)) => True
  | _, .leaf _ .cB => True
  | _, .leaf _ .cR => True
  | _, .leaf _ .cQ => True
  | j, .app s t => Good (j + 1) s ∧ Good j t

/-- Levels of normal terms: `K` raises the level by one. -/
def NLev : (ℕ → ℕ) → NT → ℕ → Prop
  | γ, .leaf m (.var i), ℓ => γ i + m = ℓ
  | _, .leaf _ .cB, _ => True
  | _, .leaf _ .cR, _ => True
  | _, .leaf _ .cQ, _ => True
  | γ, .app s t, ℓ => NLev γ s (ℓ + 1) ∧ NLev γ t ℓ

/-- The translation of λ-terms. -/
def tr : LTm → NT
  | .var i => .leaf 0 (.var i)
  | .app s t => .app (tr s) (tr t)
  | .lam t => abs 0 (tr t)
  | .eqt s t => .app (.app (.leaf 0 .cQ) (kpush (tr s))) (tr t)
  | .tt => .leaf 0 .cB
  | .ff => .leaf 0 .cR

theorem nlev_iT (γ : ℕ → ℕ) (L : ℕ) : NLev γ iT L := by simp [iT, NLev]

theorem nlev_good (T : NT) : ∀ (j ℓ k : ℕ) (γ : ℕ → ℕ), NLev (scons k γ) T ℓ → k + j = ℓ →
    Good j T := by
  induction T with
  | leaf m a =>
    intro j ℓ k γ h e
    cases a with
    | var i =>
      cases i with
      | zero =>
        have h' : k + m = ℓ := h
        show m = j
        omega
      | succ i => trivial
    | cB => trivial
    | cR => trivial
    | cQ => trivial
  | app s t ihs iht =>
    intro j ℓ k γ h e
    exact ⟨ihs (j + 1) (ℓ + 1) k γ h.1 (by omega), iht j ℓ k γ h.2 e⟩

theorem nlev_abs (T : NT) : ∀ (j ℓ k : ℕ) (γ : ℕ → ℕ), NLev (scons k γ) T ℓ → k + j = ℓ →
    NLev γ (abs j T) (ℓ + 1) := by
  induction T with
  | leaf m a =>
    intro j ℓ k γ h e
    cases a with
    | var i =>
      cases i with
      | zero => exact nlev_iT γ (ℓ + 1)
      | succ i =>
        have h' : γ i + m = ℓ := h
        show γ i + (m + 1) = ℓ + 1
        omega
    | cB => trivial
    | cR => trivial
    | cQ => trivial
  | app s t ihs iht =>
    intro j ℓ k γ h e
    exact ⟨⟨trivial, ihs (j + 1) (ℓ + 1) k γ h.1 (by omega)⟩, iht j ℓ k γ h.2 e⟩

theorem nlev_kpush (T : NT) : ∀ (ℓ : ℕ) (γ : ℕ → ℕ), NLev γ T ℓ → NLev γ (kpush T) (ℓ + 1) := by
  induction T with
  | leaf m a =>
    intro ℓ γ h
    cases a with
    | var i =>
      have h' : γ i + m = ℓ := h
      show γ i + (m + 1) = ℓ + 1
      omega
    | cB => trivial
    | cR => trivial
    | cQ => trivial
  | app s t ihs iht =>
    intro ℓ γ h
    exact ⟨⟨trivial, ihs (ℓ + 1) γ h.1⟩, iht ℓ γ h.2⟩

/-- The translation of a stratified λ-term has the same level. -/
theorem nlev_tr (t : LTm) : ∀ (γ : ℕ → ℕ) (ℓ : ℕ), HasLev γ t ℓ → NLev γ (tr t) ℓ := by
  induction t with
  | var i => intro γ ℓ h; exact (show γ i + 0 = ℓ from h)
  | app s t ihs iht => intro γ ℓ h; exact ⟨ihs γ (ℓ + 1) h.1, iht γ ℓ h.2⟩
  | lam t ih =>
    intro γ ℓ h
    obtain ⟨k, rfl, hk⟩ := h
    exact nlev_abs (tr t) 0 k k γ (ih (scons k γ) k hk) rfl
  | eqt s t ihs iht =>
    intro γ ℓ h
    exact ⟨⟨trivial, nlev_kpush (tr s) ℓ γ (ihs γ ℓ h.1)⟩, iht γ ℓ h.2⟩
  | tt => intro γ ℓ _; trivial
  | ff => intro γ ℓ _; trivial

/-! ### In a model of `𝗖𝗡𝗙` -/

section model

variable {M : Type} [s : Tarski.Structure ℒᴄ M] [Tarski.Structure.Eq ℒᴄ M] [Nonempty M]
  [hM : M↓[ℒᴄ] ⊧* 𝗖𝗡𝗙]

local infixl:70 " ⬝ " => App

/-- The identity `B (B B B) B`. -/
def Ic : M := Bc ⬝ (Bc ⬝ Bc ⬝ Bc) ⬝ Bc

theorem i_app (z : M) : (Ic : M) ⬝ z = z := by
  simp only [Ic, b_app hM, k_app hM]

/-- `K` applied `m` times. -/
def kpow : ℕ → M → M
  | 0, x => x
  | m + 1, x => Kf (kpow m x)

/-- The value of an atom. -/
def aval (env : ℕ → M) : Atom → M
  | .var i => env i
  | .cB => Bc
  | .cR => Rc
  | .cQ => Qc

/-- The value of a normal term. -/
def nval (env : ℕ → M) : NT → M
  | .leaf m a => kpow m (aval env a)
  | .app s t => nval env s ⬝ nval env t

omit [Tarski.Structure.Eq ℒᴄ M] [Nonempty M] hM in
theorem nval_iT (env : ℕ → M) : nval env iT = Ic := rfl

theorem nval_kpush (env : ℕ → M) (T : NT) : nval env (kpush T) = Kf (nval env T) := by
  induction T with
  | leaf m a => rfl
  | app s t ihs iht =>
    show Bc ⬝ nval env (kpush s) ⬝ nval env (kpush t) = Kf (nval env s ⬝ nval env t)
    rw [ihs, iht]
    exact c_ext hM fun z => by simp only [b_app hM, k_app hM]

/-- **Abstraction.** -/
theorem abs_spec (T : NT) : ∀ j, Good j T → ∀ (env : ℕ → M) (x : M),
    nval env (abs j T) ⬝ kpow j x = nval (scons x env) T := by
  induction T with
  | leaf m a =>
    intro j h env x
    cases a with
    | var i =>
      cases i with
      | zero =>
        have e : m = j := h
        subst e
        show nval env iT ⬝ kpow m x = kpow m x
        rw [nval_iT, i_app]
      | succ i =>
        show Kf (kpow m (env i)) ⬝ kpow j x = kpow m (env i)
        rw [k_app hM]
    | cB => show Kf (kpow m Bc) ⬝ kpow j x = kpow m Bc; rw [k_app hM]
    | cR => show Kf (kpow m Rc) ⬝ kpow j x = kpow m Rc; rw [k_app hM]
    | cQ => show Kf (kpow m Qc) ⬝ kpow j x = kpow m Qc; rw [k_app hM]
  | app s t ihs iht =>
    intro j h env x
    show Bc ⬝ nval env (abs (j + 1) s) ⬝ nval env (abs j t) ⬝ kpow j x =
      nval (scons x env) s ⬝ nval (scons x env) t
    rw [b_app hM, iht j h.2 env x]
    have := ihs (j + 1) h.1 env x
    rw [show kpow (j + 1) x = Kf (kpow j x) from rfl] at this
    rw [this]

/-- The equality test `q · K(a) · b`. -/
def EqC (a b : M) : M := Qc ⬝ Kf a ⬝ b

theorem eqC_self (a : M) : EqC a a = Bc := q_true hM (k_app hM a a)

theorem eqC_ne {a b : M} (h : a ≠ b) : EqC a b = Rc :=
  q_false hM (by rw [k_app hM]; exact h)

/-- `DenC t env v`: `v` is the value of the λ-term `t`, with `⊤` read as `B`, `⊥` as `R` and
`s ≐ t` as `q · K(s) · t`. -/
def DenC : LTm → (ℕ → M) → M → Prop
  | .var i, env, v => v = env i
  | .app s t, env, v => ∃ a b, DenC s env a ∧ DenC t env b ∧ v = a ⬝ b
  | .lam t, env, v => ∀ x, ∃ w, DenC t (scons x env) w ∧ v ⬝ x = w
  | .eqt s t, env, v => ∃ a b, DenC s env a ∧ DenC t env b ∧ v = EqC a b
  | .tt, _, v => v = Bc
  | .ff, _, v => v = Rc

/-- **Every stratified λ-term has a value**, namely the value of its translation. -/
theorem den_tr (t : LTm) : ∀ (γ : ℕ → ℕ) (ℓ : ℕ), HasLev γ t ℓ → ∀ env : ℕ → M,
    DenC t env (nval env (tr t)) := by
  induction t with
  | var i => intro γ ℓ _ env; rfl
  | app s t ihs iht =>
    intro γ ℓ h env
    exact ⟨_, _, ihs γ (ℓ + 1) h.1 env, iht γ ℓ h.2 env, rfl⟩
  | lam t ih =>
    intro γ ℓ h env x
    obtain ⟨k, -, hk⟩ := h
    refine ⟨_, ih (scons k γ) k hk (scons x env), ?_⟩
    exact abs_spec (tr t) 0 (nlev_good (tr t) 0 k k γ (nlev_tr t (scons k γ) k hk) rfl) env x
  | eqt s t ihs iht =>
    intro γ ℓ h env
    refine ⟨_, _, ihs γ ℓ h.1 env, iht γ ℓ h.2 env, ?_⟩
    show Qc ⬝ nval env (kpush (tr s)) ⬝ nval env (tr t) = EqC _ _
    rw [nval_kpush]
    rfl
  | tt => intro γ ℓ _ env; rfl
  | ff => intro γ ℓ _ env; rfl

end model

/-! ### The translation -/

/-- The graphs of the function symbols of FunctionNF: the first variable is the value. -/
def fnFuncC : {k : ℕ} → (ℒλ).Func k → Semiformula.Operator ℒᴄ (k + 1)
  | _, Language.Fn.Func.tt => ⟨eqF #0 bT⟩
  | _, Language.Fn.Func.ff => ⟨eqF #0 rT⟩
  | _, Language.Fn.Func.app => ⟨eqF #0 (appT #1 #2)⟩
  | _, Language.Fn.Func.eqt => ⟨eqF #0 (appT (appT qT (kT #1)) #2)⟩

/-- Equality is itself. -/
def fnRelC : {k : ℕ} → (ℒλ).Rel k → Semiformula.Operator ℒᴄ k
  | _, Language.Fn.Rel.eq => Semiformula.Operator.Eq.eq

/-- The value of a function symbol of FunctionNF in a structure for `ℒᴄ`. -/
def FnVal {M : Type} [Tarski.Structure ℒᴄ M] : {k : ℕ} → (ℒλ).Func k → (Fin k → M) → M
  | _, Language.Fn.Func.tt, _ => Bc
  | _, Language.Fn.Func.ff, _ => Rc
  | _, Language.Fn.Func.app, v => App (v 0) (v 1)
  | _, Language.Fn.Func.eqt, v => EqC (v 0) (v 1)

lemma fnFuncC_val {M : Type} [Tarski.Structure ℒᴄ M] [Tarski.Structure.Eq ℒᴄ M] {k : ℕ}
    (f : (ℒλ).Func k) (y : M) (v : Fin k → M) :
    (fnFuncC f).val (y :> v) ↔ y = FnVal f v := by
  cases f with
  | tt =>
    simp only [fnFuncC, Semiformula.Operator.val, eval_eqF, val_bT, Semiterm.val_bvar]
    exact Iff.rfl
  | ff =>
    simp only [fnFuncC, Semiformula.Operator.val, eval_eqF, val_rT, Semiterm.val_bvar]
    exact Iff.rfl
  | app =>
    simp only [fnFuncC, Semiformula.Operator.val, eval_eqF, val_appT, Semiterm.val_bvar]
    exact Iff.rfl
  | eqt =>
    simp only [fnFuncC, Semiformula.Operator.val, eval_eqF, val_appT, val_kT, val_qT,
      Semiterm.val_bvar]
    exact Iff.rfl

/-- **The translation of the language of FunctionNF into CombNF.** -/
def fnOfComb : DirectTranslation 𝗖𝗡𝗙 ℒλ where
  domain := ⟨⊤⟩
  rel := fnRelC
  func := fnFuncC
  domain_nonempty := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    simp [models_iff, Semiformula.Operator.val]
  func_defined {k} f := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have h : ∀ v : Fin k → M, (∀ i, (⟨⊤⟩ : Semiformula.Operator ℒᴄ 1).val ![v i]) →
        ∃! y, (⟨⊤⟩ : Semiformula.Operator ℒᴄ 1).val ![y] ∧ (fnFuncC f).val (y :> v) := by
      intro v _
      exact ⟨FnVal f v, ⟨by simp [Semiformula.Operator.val], (fnFuncC_val f _ v).mpr rfl⟩,
        fun y' hy' => (fnFuncC_val f y' v).mp hy'.2⟩
    simpa [models_iff, Function.comp_def, Matrix.constant_eq_singleton] using h
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : fnRelC (Language.Eq.eq : (ℒλ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section fnModel

variable {M : Type} [Tarski.Structure ℒᴄ M] [Tarski.Structure.Eq ℒᴄ M] [Nonempty M]
  [hM : M↓[ℒᴄ] ⊧* 𝗖𝗡𝗙]

local notation "N" => fnOfComb.Model M

/-- An object of the model, as an object of the interpreted structure. -/
def toModel (a : M) : N :=
  ⟨a, by simp [DirectTranslation.Dom, fnOfComb, Semiformula.Operator.val]⟩

omit [Nonempty M] hM in
theorem coe_inj {a b : N} (h : (a : M) = (b : M)) : a = b := by
  cases a; cases b; cases h; rfl

theorem app_iff (a b y : N) : y = FNF.App a b ↔ (y : M) = App (a : M) (b : M) :=
  (Model.func_iff (f := Language.Fn.Func.app) (y := y) (v := ![a, b])).trans
    (fnFuncC_val Language.Fn.Func.app _ _)

theorem eqt_iff (a b y : N) : y = FNF.EqT a b ↔ (y : M) = EqC (a : M) (b : M) :=
  (Model.func_iff (f := Language.Fn.Func.eqt) (y := y) (v := ![a, b])).trans
    (fnFuncC_val Language.Fn.Func.eqt _ _)

theorem tt_iff (y : N) : y = FNF.TT ↔ (y : M) = Bc :=
  (Model.func_iff (f := Language.Fn.Func.tt) (y := y) (v := ![])).trans
    (fnFuncC_val Language.Fn.Func.tt _ _)

theorem ff_iff (y : N) : y = FNF.FF ↔ (y : M) = Rc :=
  (Model.func_iff (f := Language.Fn.Func.ff) (y := y) (v := ![])).trans
    (fnFuncC_val Language.Fn.Func.ff _ _)

/-- The value of a λ-term in the interpreted structure is its value computed in `M`. -/
theorem den_iff (t : LTm) : ∀ (env : ℕ → N) (v : N),
    FNF.Den t env v ↔ DenC t (fun i => (env i : M)) (v : M) := by
  induction t with
  | var i => intro env v; exact ⟨fun h => congrArg _ h, fun h => coe_inj h⟩
  | app s t ihs iht =>
    intro env v
    constructor
    · rintro ⟨a, b, ha, hb, h⟩
      exact ⟨a, b, (ihs env a).mp ha, (iht env b).mp hb, (app_iff a b v).mp h⟩
    · rintro ⟨a, b, ha, hb, h⟩
      exact ⟨toModel a, toModel b, (ihs env _).mpr ha, (iht env _).mpr hb,
        (app_iff (toModel a) (toModel b) v).mpr h⟩
  | lam t ih =>
    intro env v
    have e : ∀ x : N, (fun i => ((scons x env i : N) : M)) =
        scons (x : M) (fun i => (env i : M)) := by
      intro x
      funext i
      cases i <;> rfl
    constructor
    · intro h x
      obtain ⟨w, hw, hvw⟩ := h (toModel x)
      have := (ih _ w).mp hw
      rw [e] at this
      exact ⟨w, this, ((app_iff v (toModel x) w).mp hvw.symm).symm⟩
    · intro h x
      obtain ⟨w, hw, hvw⟩ := h (x : M)
      refine ⟨toModel w, (ih _ _).mpr ?_, ((app_iff v x (toModel w)).mpr hvw.symm).symm⟩
      rw [e]
      exact hw
  | eqt s t ihs iht =>
    intro env v
    constructor
    · rintro ⟨a, b, ha, hb, h⟩
      exact ⟨a, b, (ihs env a).mp ha, (iht env b).mp hb, (eqt_iff a b v).mp h⟩
    · rintro ⟨a, b, ha, hb, h⟩
      exact ⟨toModel a, toModel b, (ihs env _).mpr ha, (iht env _).mpr hb,
        (eqt_iff (toModel a) (toModel b) v).mpr h⟩
  | tt => intro env v; exact tt_iff v
  | ff => intro env v; exact ff_iff v

/-- **In a model of `𝗖𝗡𝗙`, the interpreted structure is a model of `𝗙𝗡𝗙`.** -/
theorem fnModel_models : (fnOfComb.Model M)↓[ℒλ] ⊧* 𝗙𝗡𝗙 := by
  have htt : ((FNF.TT : N) : M) = Bc := (tt_iff _).mp rfl
  have hff : ((FNF.FF : N) : M) = Rc := (ff_iff _).mp rfl
  refine FNF.models_of ?_ ?_ ?_ ?_ ?_
  · intro f g h
    refine coe_inj (c_ext hM fun x => ?_)
    have h1 : ((FNF.App f (toModel x) : N) : M) = App (f : M) x :=
      (app_iff f (toModel x) _).mp rfl
    have h2 : ((FNF.App f (toModel x) : N) : M) = App (g : M) x :=
      (app_iff g (toModel x) _).mp (h (toModel x))
    exact h1.symm.trans h2
  · intro a
    exact ((eqt_iff a a FNF.TT).mpr (htt.trans (eqC_self (a : M)).symm)).symm
  · intro a b hab
    exact ((eqt_iff a b FNF.FF).mpr
      (hff.trans (eqC_ne (fun e => hab (coe_inj e))).symm)).symm
  · intro e
    exact b_ne_r hM (htt.symm.trans ((congrArg _ e).trans hff))
  · intro t γ ℓ h env
    exact ⟨toModel (nval (fun i => (env i : M)) (tr t)),
      (den_iff t env _).mpr (den_tr t γ ℓ h _)⟩

end fnModel

/-- **CombNF interprets FunctionNF.** -/
instance combInterpretsFn : 𝗖𝗡𝗙 ⊳ 𝗙𝗡𝗙 where
  trln := fnOfComb
  interpret_theory φ hφ := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp fnModel_models φ hφ)

/-- **CombNF interprets NFU + Infinity**, through FunctionNF. -/
instance combInterpretsNFUI : 𝗖𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜 :=
  DirectInterpretation.comp FNF.fnInterpretsNFUI combInterpretsFn

/-- **CombNF interprets NF**, through FunctionNF and NFU + Infinity. -/
instance combInterpretsNF : 𝗖𝗡𝗙 ⊳ 𝗡𝗙 :=
  DirectInterpretation.comp FNF.fnInterpretsNF combInterpretsFn

end FFL.FirstOrder.CNF

#print axioms FFL.FirstOrder.CNF.combInterpretsFn
#print axioms FFL.FirstOrder.CNF.combInterpretsNFUI
