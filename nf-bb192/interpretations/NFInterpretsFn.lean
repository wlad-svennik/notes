import NFFn
import FnTheory

set_option autoImplicit false

/-!
# NF interprets FunctionNF

* `NDef γ R`: a stratified definition with variables indexed by `ℕ`, as the free variables of a
  λ-term are. `NDef.comprehension` is stratified comprehension in a model of `𝗡𝗙` for them.
* `DenV t env v`: `v` is the value of the λ-term `t`, computed with the application `AppR` of
  `NFFn.lean`. `denN`: it has a stratified definition when `t` is stratified, with all types
  raised by 8. `denV_exists`, `denV_fun`: a stratified λ-term has exactly one value. For an
  abstraction this is comprehension applied to the graph, followed by the bijection between the
  universe and the set of functions.
* `fnTranslation`: the translation of the language of FunctionNF into `𝗡𝗙`. The domain is
  everything; application is `AppR`; `⊤` is the universal set and `⊥` the empty set.
* **Result**: `nfInterpretsFn : 𝗡𝗙 ⊳ 𝗙𝗡𝗙`.
-/

namespace FFL.FirstOrder.SetTheory

namespace NFFn

open JensenNFU.TFm (scons scons_zero scons_succ)
open FNF (LTm HasLev)
open DirectTranslation

/-! ### Stratified definitions with variables indexed by `ℕ` -/

/-- A relation on environments, uniformly in every structure. -/
abbrev NRel := ∀ (V : Type) [SetStructure V], (ℕ → V) → Prop

/-- `NDef γ R`: a formula with free variables indexed by `ℕ` that defines `R` in every structure
and is stratified when the variables have the types `γ`. -/
structure NDef (γ : ℕ → ℕ) (R : NRel) where
  /-- The formula. -/
  φ : Semiformula ℒₛₑₜ ℕ 0
  /-- It is stratified by `γ`. -/
  strat : φ.Stratified γ ![]
  /-- It defines `R`. -/
  eval : ∀ (V : Type) [SetStructure V] (env : ℕ → V), Semiformula.Eval ![] env φ ↔ R V env

/-- Free variable `0` becomes the bound variable; the others move down. -/
def fixTm : ℕ → Semiterm ℒₛₑₜ ℕ 1
  | 0 => #0
  | i + 1 => &i

/-- The substitution that prepares a quantifier over free variable `0`. -/
def fixRew : Rew ℒₛₑₜ ℕ 0 ℕ 1 := Rew.bind (![] : Fin 0 → Semiterm ℒₛₑₜ ℕ 1) fixTm

lemma fix_strat {γ : ℕ → ℕ} {t : ℕ} {φ : Semiformula ℒₛₑₜ ℕ 0}
    (h : φ.Stratified (scons t γ) ![]) : (fixRew ▹ φ).Stratified γ (t :> ![]) :=
  Semiformula.stratified_rew 0 φ fixRew ![] (t :> ![]) (fun x => x.elim0)
    (fun x => by cases x <;> simp [fixRew, fixTm]) h

lemma fix_eval {V : Type} [SetStructure V] (φ : Semiformula ℒₛₑₜ ℕ 0) (a : V) (env : ℕ → V) :
    Semiformula.Eval (a :> ![]) env (fixRew ▹ φ) ↔ Semiformula.Eval ![] (scons a env) φ := by
  have e1 : (Semiterm.val (a :> ![]) env ∘ fixRew ∘ Semiterm.bvar) = (![] : Fin 0 → V) :=
    funext fun x => x.elim0
  have e2 : (Semiterm.val (a :> ![]) env ∘ fixRew ∘ Semiterm.fvar) = scons a env := by
    funext i
    cases i <;> simp [fixRew, fixTm]
  rw [Semiformula.eval_rew, e1, e2]

namespace NDef

variable {γ : ℕ → ℕ} {R S : NRel}

/-- The same formula defines every relation equivalent to `R`. -/
def congr {R' : NRel} (d : NDef γ R)
    (h : ∀ (V : Type) [SetStructure V] (env : ℕ → V), R V env ↔ R' V env) : NDef γ R' where
  φ := d.φ
  strat := d.strat
  eval V _ env := (d.eval V env).trans (h V env)

/-- From a stratified definition with finitely many variables. -/
def ofS {k : ℕ} {τ : Fin k → ℕ} {R : URel k} (d : SDef τ R) (f : Fin k → ℕ) (c : ℕ)
    (hf : ∀ i, γ (f i) = τ i + c) : NDef γ (fun V _ env => R V (fun i => env (f i))) where
  φ := Rew.bind (fun i => (&(f i) : Semiterm ℒₛₑₜ ℕ 0)) Empty.elim ▹ d.φ
  strat := Semiformula.stratified_rew c d.φ _ τ ![] (by intro x; simp [hf])
    (fun x => x.elim) d.strat
  eval V _ env := by
    have e1 : (Semiterm.val (![] : Fin 0 → V) env ∘
        Rew.bind (fun i => (&(f i) : Semiterm ℒₛₑₜ ℕ 0)) Empty.elim ∘ Semiterm.bvar) =
        fun i => env (f i) := by funext i; simp
    have e2 : (Semiterm.val (![] : Fin 0 → V) env ∘
        Rew.bind (fun i => (&(f i) : Semiterm ℒₛₑₜ ℕ 0)) Empty.elim ∘ Semiterm.fvar) =
        (Empty.elim : Empty → V) := funext fun z => z.elim
    rw [Semiformula.eval_rew, e1, e2]
    exact d.eval V _

/-- Renaming of variables, when the types match up to a shift by `c`. -/
def ren {γ₀ : ℕ → ℕ} (d : NDef γ₀ R) (g : ℕ → ℕ) (c : ℕ) (hg : ∀ i, γ (g i) = γ₀ i + c) :
    NDef γ (fun V _ env => R V (fun i => env (g i))) where
  φ := Rew.rewriteMap g ▹ d.φ
  strat := Semiformula.stratified_rew c d.φ _ ![] ![] (fun x => x.elim0)
    (by intro x; simp [hg]) d.strat
  eval V _ env := by
    rw [Semiformula.eval_rewriteMap]
    exact d.eval V _

/-- Conjunction. -/
def and (d : NDef γ R) (e : NDef γ S) : NDef γ (fun V _ env => R V env ∧ S V env) where
  φ := d.φ ⋏ e.φ
  strat := Semiformula.stratified_and.mpr ⟨d.strat, e.strat⟩
  eval V _ env := by simp [d.eval, e.eval]

/-- Universal quantification over variable `0`, of type `t`. -/
def all (t : ℕ) {R : NRel} (d : NDef (scons t γ) R) :
    NDef γ (fun V _ env => ∀ a : V, R V (scons a env)) where
  φ := ∀¹ (fixRew ▹ d.φ)
  strat := Semiformula.stratified_all.mpr ⟨t, fix_strat d.strat⟩
  eval V _ env := by
    simp only [Semiformula.eval_all]
    exact forall_congr' fun a => (fix_eval d.φ a env).trans (d.eval V _)

/-- Existential quantification over variable `0`, of type `t`. -/
def ex (t : ℕ) {R : NRel} (d : NDef (scons t γ) R) :
    NDef γ (fun V _ env => ∃ a : V, R V (scons a env)) where
  φ := ∃¹ (fixRew ▹ d.φ)
  strat := Semiformula.stratified_exs.mpr ⟨t, fix_strat d.strat⟩
  eval V _ env := by
    simp only [Semiformula.eval_ex]
    exact exists_congr fun a => (fix_eval d.φ a env).trans (d.eval V _)

end NDef

/-- **Stratified comprehension in a model of `𝗡𝗙`**, for definitions with variables indexed by
`ℕ`. -/
theorem NDef.comprehension {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙]
    {γ : ℕ → ℕ} {t : ℕ} {R : NRel} (d : NDef (scons t γ) R) (env : ℕ → V) :
    ∃ y : V, ∀ x, x ∈ y ↔ R V (scons x env) := by
  have hψ : (fixRew ▹ d.φ : SetTheorySemiproposition 1).IsStratified :=
    ⟨γ, ![t], fix_strat d.strat⟩
  have := by
    simpa [models_iff, Axiom.comprehensionSchema] using
      Theory.models V 𝗡𝗙 (NewFoundations.comprehension (fixRew ▹ d.φ) hψ)
  obtain ⟨y, hy⟩ := this env
  exact ⟨y, fun x => (hy x).trans ((fix_eval d.φ x env).trans (d.eval V _))⟩

/-! ### The value of a λ-term -/

/-- `DenV t env v`: `v` is the value of the λ-term `t` in the environment `env`. -/
def DenV {V : Type} [SetStructure V] : LTm → (ℕ → V) → V → Prop
  | .var i, env, v => v = env i
  | .app s t, env, v => ∃ a b, DenV s env a ∧ DenV t env b ∧ AppR a b v
  | .lam t, env, v => ∀ x, ∃ w, DenV t (scons x env) w ∧ AppR v x w
  | .eqt s t, env, v => ∃ a b, DenV s env a ∧ DenV t env b ∧ EqtR a b v
  | .tt, _, v => IsTT v
  | .ff, _, v => IsFF v

lemma lam_lev {γ : ℕ → ℕ} {t : LTm} {ℓ : ℕ} (h : HasLev γ (.lam t) ℓ) :
    0 < ℓ ∧ HasLev (scons (ℓ - 1) γ) t (ℓ - 1) := by
  obtain ⟨k, rfl, hk⟩ := h
  exact ⟨Nat.succ_pos k, by simpa using hk⟩

/-- Renamings used below. -/
def g1 : ℕ → ℕ
  | 0 => 1
  | i + 1 => i + 3

def g2 : ℕ → ℕ
  | 0 => 0
  | i + 1 => i + 3

def g3 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | i + 2 => i + 3

/-- **The value of a stratified λ-term has a stratified definition**: variable `0` is the value
and variable `i + 1` is the `i`-th variable of the term; all types are raised by 8. -/
def denN : (t : LTm) → (γ : ℕ → ℕ) → (ℓ : ℕ) → HasLev γ t ℓ →
    NDef (scons (ℓ + 8) (fun i => γ i + 8))
      (fun V _ env => DenV t (fun i => env (i + 1)) (env 0))
  | .var i, γ, ℓ, h =>
    (NDef.ofS (SDef.eq (τ := ![0, 0]) 0 1) ![0, i + 1] (ℓ + 8) (fun j => by
      fin_cases j
      · show ℓ + 8 = 0 + (ℓ + 8)
        omega
      · show γ i + 8 = 0 + (ℓ + 8)
        have : γ i = ℓ := h
        omega)).congr fun _ _ _ => Iff.rfl
  | .app s t, γ, ℓ, h =>
    (NDef.ex (ℓ + 1 + 8) (NDef.ex (ℓ + 8)
      (((denN s γ (ℓ + 1) h.1).ren g1 0 (fun i => by cases i <;> rfl)).and
        (((denN t γ ℓ h.2).ren g2 0 (fun i => by cases i <;> rfl)).and
          (NDef.ofS appD ![1, 0, 2] ℓ (fun j => by
            fin_cases j
            · show ℓ + 1 + 8 = 9 + ℓ
              omega
            · show ℓ + 8 = 8 + ℓ
              omega
            · show ℓ + 8 = 8 + ℓ
              omega)))))).congr fun _ _ _ => Iff.rfl
  | .lam t, γ, ℓ, h =>
    (NDef.all (ℓ - 1 + 8) (NDef.ex (ℓ - 1 + 8)
      (((denN t (scons (ℓ - 1) γ) (ℓ - 1) (lam_lev h).2).ren g3 0 (fun i => by
          match i with
          | 0 => rfl
          | 1 => rfl
          | i + 2 => rfl)).and
        (NDef.ofS appD ![2, 1, 0] (ℓ - 1) (fun j => by
          have := (lam_lev h).1
          fin_cases j
          · show ℓ + 8 = 9 + (ℓ - 1)
            omega
          · show ℓ - 1 + 8 = 8 + (ℓ - 1)
            omega
          · show ℓ - 1 + 8 = 8 + (ℓ - 1)
            omega))))).congr fun V _ env =>
      forall_congr' fun x => exists_congr fun w => and_congr
        (iff_of_eq (congrArg (fun e => DenV t e w) (funext fun i => by cases i <;> rfl)))
        Iff.rfl
  | .eqt s t, γ, ℓ, h =>
    (NDef.ex (ℓ + 8) (NDef.ex (ℓ + 8)
      (((denN s γ ℓ h.1).ren g1 0 (fun i => by cases i <;> rfl)).and
        (((denN t γ ℓ h.2).ren g2 0 (fun i => by cases i <;> rfl)).and
          (NDef.ofS eqtD ![1, 0, 2] (ℓ + 7) (fun j => by
            fin_cases j
            · show ℓ + 8 = 1 + (ℓ + 7)
              omega
            · show ℓ + 8 = 1 + (ℓ + 7)
              omega
            · show ℓ + 8 = 1 + (ℓ + 7)
              omega)))))).congr fun _ _ _ => Iff.rfl
  | .tt, γ, ℓ, _ =>
    (NDef.ofS ttD ![0] (ℓ + 7) (fun j => by
      fin_cases j
      show ℓ + 8 = 1 + (ℓ + 7)
      omega)).congr fun _ _ _ => Iff.rfl
  | .ff, γ, ℓ, _ =>
    (NDef.ofS ffD ![0] (ℓ + 7) (fun j => by
      fin_cases j
      show ℓ + 8 = 1 + (ℓ + 7)
      omega)).congr fun _ _ _ => Iff.rfl

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

/-- A λ-term has at most one value. -/
theorem denV_fun (t : LTm) :
    ∀ (env : ℕ → V) (v v' : V), DenV t env v → DenV t env v' → v = v' := by
  induction t with
  | var i => intro env v v' h h'; exact h.trans h'.symm
  | app s t ihs iht =>
    rintro env v v' ⟨a, b, ha, hb, h⟩ ⟨a', b', ha', hb', h'⟩
    rw [ihs env a a' ha ha', iht env b b' hb hb'] at h
    exact app_fun h h'
  | lam t ih =>
    intro env v v' h h'
    refine app_ext fun x y hxy => ?_
    obtain ⟨w, hw, hvw⟩ := h x
    obtain ⟨w', hw', hvw'⟩ := h' x
    rw [app_fun hxy hvw, ih _ w w' hw hw']
    exact hvw'
  | eqt s t ihs iht =>
    rintro env v v' ⟨a, b, ha, hb, h⟩ ⟨a', b', ha', hb', h'⟩
    rw [ihs env a a' ha ha', iht env b b' hb hb'] at h
    exact eqt_fun h h'
  | tt => intro env v v' h h'; exact tt_unique h h'
  | ff => intro env v v' h h'; exact ff_unique h h'

/-- **A stratified λ-term has a value.** -/
theorem denV_exists (t : LTm) :
    ∀ (γ : ℕ → ℕ) (ℓ : ℕ), HasLev γ t ℓ → ∀ env : ℕ → V, ∃ v, DenV t env v := by
  induction t with
  | var i => intro γ ℓ _ env; exact ⟨env i, rfl⟩
  | app s t ihs iht =>
    intro γ ℓ h env
    obtain ⟨a, ha⟩ := ihs γ (ℓ + 1) h.1 env
    obtain ⟨b, hb⟩ := iht γ ℓ h.2 env
    obtain ⟨v, hv⟩ := app_total a b
    exact ⟨v, a, b, ha, hb, hv⟩
  | lam t ih =>
    intro γ ℓ h env
    obtain ⟨k, -, hk⟩ := h
    obtain ⟨F, hF⟩ := (NDef.ex (γ := scons (k + 8) (fun i => γ i + 8)) (k + 8) (NDef.ex (k + 8)
      ((NDef.ofS prD ![2, 1, 0] k (fun j => by
          fin_cases j
          · show k + 8 = 8 + k
            omega
          · show k + 8 = 8 + k
            omega
          · show k + 8 = 8 + k
            omega)).and
        ((denN t (scons k γ) k hk).ren g3 0 (fun i => by
          match i with
          | 0 => rfl
          | 1 => rfl
          | i + 2 => rfl))))).comprehension env
    have hF' : ∀ p, p ∈ F ↔ ∃ x y, Pr p x y ∧ DenV t (scons x env) y := by
      intro p
      refine (hF p).trans (exists_congr fun x => exists_congr fun w => and_congr Iff.rfl ?_)
      exact iff_of_eq (congrArg (fun e => DenV t e w) (funext fun i => by cases i <;> rfl))
    obtain ⟨f, hf⟩ := app_of_graph hF' (fun x => ih (scons k γ) k hk (scons x env))
      (fun x y y' hy hy' => denV_fun t _ y y' hy hy')
    refine ⟨f, fun x => ?_⟩
    obtain ⟨w, hw⟩ := ih (scons k γ) k hk (scons x env)
    exact ⟨w, hw, (hf x w).mpr hw⟩
  | eqt s t ihs iht =>
    intro γ ℓ h env
    obtain ⟨a, ha⟩ := ihs γ ℓ h.1 env
    obtain ⟨b, hb⟩ := iht γ ℓ h.2 env
    obtain ⟨v, hv⟩ := eqt_total a b
    exact ⟨v, a, b, ha, hb, hv⟩
  | tt => intro γ ℓ _ env; exact exists_tt
  | ff => intro γ ℓ _ env; exact exists_ff

end model

/-! ### The translation -/

/-- The graphs of the function symbols: the first variable is the value. -/
def fnFunc : {k : ℕ} → (ℒλ).Func k → Semiformula.Operator ℒₛₑₜ (k + 1)
  | _, Language.Fn.Func.tt => ⟨ttD.φ⟩
  | _, Language.Fn.Func.ff => ⟨ffD.φ⟩
  | _, Language.Fn.Func.app => ⟨(appD.comp (τ' := ![8, 9, 8]) ![1, 2, 0] 0).φ⟩
  | _, Language.Fn.Func.eqt => ⟨(eqtD.comp (τ' := ![1, 1, 1]) ![1, 2, 0] 0).φ⟩

/-- The interpretation of the relation symbols: equality is itself. -/
def fnRel : {k : ℕ} → (ℒλ).Rel k → Semiformula.Operator ℒₛₑₜ k
  | _, Language.Fn.Rel.eq => Semiformula.Operator.Eq.eq

/-- What the graph of a function symbol says. -/
def Graph {V : Type} [SetStructure V] : {k : ℕ} → (ℒλ).Func k → V → (Fin k → V) → Prop
  | _, Language.Fn.Func.tt, y, _ => IsTT y
  | _, Language.Fn.Func.ff, y, _ => IsFF y
  | _, Language.Fn.Func.app, y, v => AppR (v 0) (v 1) y
  | _, Language.Fn.Func.eqt, y, v => EqtR (v 0) (v 1) y

lemma fnFunc_val {V : Type} [SetStructure V] {k : ℕ} (f : (ℒλ).Func k) (y : V) (v : Fin k → V) :
    (fnFunc f).val (y :> v) ↔ Graph f y v := by
  cases f with
  | tt => exact ttD.eval V (y :> v)
  | ff => exact ffD.eval V (y :> v)
  | app => exact (appD.comp (τ' := ![8, 9, 8]) ![1, 2, 0] 0).eval V (y :> v)
  | eqt => exact (eqtD.comp (τ' := ![1, 1, 1]) ![1, 2, 0] 0).eval V (y :> v)

theorem graph_existsUnique {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙]
    {k : ℕ} (f : (ℒλ).Func k) (v : Fin k → V) : ∃! y, Graph f y v := by
  cases f with
  | tt => exact let ⟨t, ht⟩ := exists_tt (V := V); ⟨t, ht, fun _ h => tt_unique h ht⟩
  | ff => exact let ⟨t, ht⟩ := exists_ff (V := V); ⟨t, ht, fun _ h => ff_unique h ht⟩
  | app => exact let ⟨y, hy⟩ := app_total (v 0) (v 1); ⟨y, hy, fun _ h => app_fun h hy⟩
  | eqt => exact let ⟨y, hy⟩ := eqt_total (v 0) (v 1); ⟨y, hy, fun _ h => eqt_fun h hy⟩

/-- **The translation of the language of FunctionNF into `𝗡𝗙`.** -/
def fnTranslation : DirectTranslation 𝗡𝗙 ℒλ where
  domain := ⟨⊤⟩
  rel := fnRel
  func := fnFunc
  domain_nonempty := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    simp [models_iff, Semiformula.Operator.val]
  func_defined {k} f := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    have h : ∀ v : Fin k → M, (∀ i, (⟨⊤⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![v i]) →
        ∃! y, (⟨⊤⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![y] ∧ (fnFunc f).val (y :> v) := by
      intro v _
      obtain ⟨y, hy, huniq⟩ := graph_existsUnique f v
      exact ⟨y, ⟨by simp [Semiformula.Operator.val], (fnFunc_val f y v).mpr hy⟩,
        fun y' hy' => huniq y' ((fnFunc_val f y' v).mp hy'.2)⟩
    simpa [models_iff, Function.comp_def, Matrix.constant_eq_singleton] using h
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : fnRel (Language.Eq.eq : (ℒλ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section fnModel

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

local notation "N" => fnTranslation.Model M

/-- An object of the model, as an object of the interpreted structure. -/
def toModel (a : M) : N :=
  ⟨a, by simp [DirectTranslation.Dom, fnTranslation, Semiformula.Operator.val]⟩

omit [Nonempty M] hT in
theorem coe_inj {a b : N} (h : (a : M) = (b : M)) : a = b := by
  cases a; cases b; cases h; rfl

theorem app_iff (a b y : N) : y = FNF.App a b ↔ AppR (a : M) (b : M) (y : M) :=
  (Model.func_iff (f := Language.Fn.Func.app) (y := y) (v := ![a, b])).trans
    (fnFunc_val Language.Fn.Func.app _ _)

theorem eqt_iff (a b y : N) : y = FNF.EqT a b ↔ EqtR (a : M) (b : M) (y : M) :=
  (Model.func_iff (f := Language.Fn.Func.eqt) (y := y) (v := ![a, b])).trans
    (fnFunc_val Language.Fn.Func.eqt _ _)

theorem tt_iff (y : N) : y = FNF.TT ↔ IsTT (y : M) :=
  (Model.func_iff (f := Language.Fn.Func.tt) (y := y) (v := ![])).trans
    (fnFunc_val Language.Fn.Func.tt _ _)

theorem ff_iff (y : N) : y = FNF.FF ↔ IsFF (y : M) :=
  (Model.func_iff (f := Language.Fn.Func.ff) (y := y) (v := ![])).trans
    (fnFunc_val Language.Fn.Func.ff _ _)

/-- The value of a λ-term in the interpreted structure is its value computed in `M`. -/
theorem den_iff (t : LTm) : ∀ (env : ℕ → N) (v : N),
    FNF.Den t env v ↔ DenV t (fun i => (env i : M)) (v : M) := by
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
      exact ⟨w, this, (app_iff v (toModel x) w).mp hvw.symm⟩
    · intro h x
      obtain ⟨w, hw, hvw⟩ := h (x : M)
      refine ⟨toModel w, (ih _ _).mpr ?_, ((app_iff v x (toModel w)).mpr hvw).symm⟩
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

/-- **In a model of `𝗡𝗙`, the interpreted structure is a model of `𝗙𝗡𝗙`.** -/
theorem fnModel_models : (fnTranslation.Model M)↓[ℒλ] ⊧* 𝗙𝗡𝗙 := by
  have htt : IsTT ((FNF.TT : N) : M) := (tt_iff _).mp rfl
  have hff : IsFF ((FNF.FF : N) : M) := (ff_iff _).mp rfl
  refine FNF.models_of ?_ ?_ ?_ ?_ ?_
  · intro f g h
    refine coe_inj (app_ext fun x y hxy => ?_)
    have h1 : toModel y = FNF.App f (toModel x) := (app_iff f (toModel x) (toModel y)).mpr hxy
    rw [h (toModel x)] at h1
    exact (app_iff g (toModel x) (toModel y)).mp h1
  · intro a
    exact ((eqt_iff a a FNF.TT).mpr (Or.inl ⟨rfl, htt⟩)).symm
  · intro a b hab
    exact ((eqt_iff a b FNF.FF).mpr (Or.inr ⟨fun e => hab (coe_inj e), hff⟩)).symm
  · intro e
    exact tt_ne_ff htt hff (congrArg _ e)
  · intro t γ ℓ h env
    obtain ⟨v, hv⟩ := denV_exists t γ ℓ h (fun i => (env i : M))
    exact ⟨toModel v, (den_iff t env _).mpr hv⟩

end fnModel

/-- **`𝗡𝗙` interprets FunctionNF.** -/
instance nfInterpretsFn : 𝗡𝗙 ⊳ 𝗙𝗡𝗙 where
  trln := fnTranslation
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp fnModel_models φ hφ)

/-- **The syntactic transformation.** The translation of a theorem of `𝗙𝗡𝗙` is a theorem of
`𝗡𝗙`. -/
theorem nf_provable_translate_of_fn {σ : Sentence ℒλ} (h : 𝗙𝗡𝗙 ⊢ σ) : 𝗡𝗙 ⊢ nfInterpretsFn σ :=
  DirectInterpretation.sound nfInterpretsFn h

end NFFn

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.NFFn.nfInterpretsFn
