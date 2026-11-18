import NFTheories
import MacModel
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Stratified definitions and comprehension in models of `𝗡𝗙`

To use the comprehension schema of `𝗡𝗙` one needs a formula, a stratification of it, and its
meaning. `SDef τ R` packages the three: a formula of `ℒₛₑₜ` with `k` variables that defines the
relation `R` in every structure and is stratified when the variables are given the types `τ`.
The constructors (`SDef.mem`, `SDef.eq`, `SDef.and`, `SDef.all`, `SDef.comp`, …) build the three
together, so that no formula has to be written out and no stratification checked by hand:
the types of the bound variables are arguments of `SDef.all` and `SDef.ex`.

* `Semiformula.stratified_rew`: stratification is preserved by a substitution of variables
  that shifts all types by the same amount.
* `SDef.comprehension`: in a model of `𝗡𝗙`, `{x | R (x, p)}` is a set for every relation with
  an `SDef` and all parameters `p`.
-/

namespace FFL.FirstOrder

open Semiformula

/-! ### Stratification and substitution -/

section rew

variable {ξ₁ ξ₂ : Type*}

lemma Semiterm.lv_rew {σ₁ : ξ₁ → ℕ} {σ₂ : ξ₂ → ℕ} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    {τ₁ : Fin n₁ → ℕ} {τ₂ : Fin n₂ → ℕ} {c : ℕ}
    (hb : ∀ x, (ω #x).lv σ₂ τ₂ = τ₁ x + c) (hf : ∀ x, (ω &x).lv σ₂ τ₂ = σ₁ x + c)
    (t : Semiterm ℒₛₑₜ ξ₁ n₁) : (ω t).lv σ₂ τ₂ = t.lv σ₁ τ₁ + c := by
  match t with
  | #x => simpa using hb x
  | &x => simpa using hf x
  | .func f _ => exact isEmptyElim f

/-- **Stratification is preserved by a substitution of variables for variables** that shifts
all types by the same amount `c`. -/
theorem Semiformula.stratified_rew {σ₁ : ξ₁ → ℕ} {σ₂ : ξ₂ → ℕ} (c : ℕ) :
    ∀ {n₁ : ℕ} (φ : Semiformula ℒₛₑₜ ξ₁ n₁) {n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
      (τ₁ : Fin n₁ → ℕ) (τ₂ : Fin n₂ → ℕ),
      (∀ x, (ω #x).lv σ₂ τ₂ = τ₁ x + c) → (∀ x, (ω &x).lv σ₂ τ₂ = σ₁ x + c) →
      φ.Stratified σ₁ τ₁ → (ω ▹ φ).Stratified σ₂ τ₂ := by
  intro n₁ φ
  induction φ using Semiformula.rec' with
  | hverum => intros; simp
  | hfalsum => intros; simp
  | hrel r v =>
    intro n₂ ω τ₁ τ₂ hb hf h
    obtain ⟨t, ht⟩ := stratified_rel.mp h
    rw [Semiformula.rew_rel]
    exact stratified_rel.mpr ⟨t + c, fun i => by rw [Semiterm.lv_rew ω hb hf, ht i]; omega⟩
  | hnrel r v =>
    intro n₂ ω τ₁ τ₂ hb hf h
    obtain ⟨t, ht⟩ := stratified_nrel.mp h
    rw [Semiformula.rew_nrel]
    exact stratified_nrel.mpr ⟨t + c, fun i => by rw [Semiterm.lv_rew ω hb hf, ht i]; omega⟩
  | hand φ ψ ih1 ih2 =>
    intro n₂ ω τ₁ τ₂ hb hf h
    simpa using And.intro (ih1 ω τ₁ τ₂ hb hf (stratified_and.mp h).1)
      (ih2 ω τ₁ τ₂ hb hf (stratified_and.mp h).2)
  | hor φ ψ ih1 ih2 =>
    intro n₂ ω τ₁ τ₂ hb hf h
    simpa using And.intro (ih1 ω τ₁ τ₂ hb hf (stratified_or.mp h).1)
      (ih2 ω τ₁ τ₂ hb hf (stratified_or.mp h).2)
  | hall φ ih =>
    intro n₂ ω τ₁ τ₂ hb hf h
    obtain ⟨t, ht⟩ := stratified_all.mp h
    have := ih ω.q (t :> τ₁) ((t + c) :> τ₂)
      (by intro x; cases x using Fin.cases <;> simp [hb])
      (by intro x; simp [hf]) ht
    simpa using Exists.intro (t + c) this
  | hexs φ ih =>
    intro n₂ ω τ₁ τ₂ hb hf h
    obtain ⟨t, ht⟩ := stratified_exs.mp h
    have := ih ω.q (t :> τ₁) ((t + c) :> τ₂)
      (by intro x; cases x using Fin.cases <;> simp [hb])
      (by intro x; simp [hf]) ht
    simpa using Exists.intro (t + c) this

end rew

namespace SetTheory

/-! ### Stratified definitions -/

/-- A relation of `k` arguments on every structure with a membership relation. -/
abbrev URel (k : ℕ) := ∀ (V : Type) [SetStructure V], (Fin k → V) → Prop

/-- `SDef τ R`: a formula that defines `R` in every structure and is stratified when its
variables have the types `τ`. -/
structure SDef {k : ℕ} (τ : Fin k → ℕ) (R : URel k) where
  /-- The formula. -/
  φ : Semisentence ℒₛₑₜ k
  /-- It is stratified by `τ`. -/
  strat : φ.Stratified Empty.elim τ
  /-- It defines `R`. -/
  eval : ∀ (V : Type) [SetStructure V] (v : Fin k → V), V ⊧/v φ ↔ R V v

/-- Proves the side condition of `SDef.comp`: the types match after a shift. -/
macro "sd_ty" : tactic => `(tactic| (intro i; fin_cases i <;> rfl))

namespace SDef

variable {k : ℕ} {τ : Fin k → ℕ}

/-- The same formula defines every relation equivalent to `R`. -/
def congr {R R' : URel k} (d : SDef τ R)
    (h : ∀ (V : Type) [SetStructure V] (v : Fin k → V), R V v ↔ R' V v) : SDef τ R' where
  φ := d.φ
  strat := d.strat
  eval V _ v := (d.eval V v).trans (h V v)

/-- `vᵢ ∈ vⱼ`, when the type of `vⱼ` is one more than that of `vᵢ`. -/
def mem (i j : Fin k) (h : τ j = τ i + 1 := by rfl) : SDef τ (fun _ _ v ↦ v i ∈ v j) where
  φ := Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![#i, #j]
  strat := stratified_rel.mpr ⟨τ i, fun x => by
    cases x using Fin.cases with
    | zero => rfl
    | succ x => cases x using Fin.cases with
      | zero => exact h
      | succ x => exact x.elim0⟩
  eval V _ v := Iff.rfl

/-- `vᵢ = vⱼ`, when the two have the same type. -/
def eq (i j : Fin k) (h : τ i = τ j := by rfl) : SDef τ (fun _ _ v ↦ v i = v j) where
  φ := Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![#i, #j]
  strat := stratified_rel.mpr ⟨τ i, fun x => by
    cases x using Fin.cases with
    | zero => rfl
    | succ x => cases x using Fin.cases with
      | zero => exact h.symm
      | succ x => exact x.elim0⟩
  eval V _ v := Iff.rfl

variable {R S : URel k}

/-- Conjunction. -/
def and (d : SDef τ R) (e : SDef τ S) : SDef τ (fun V _ v ↦ R V v ∧ S V v) where
  φ := d.φ ⋏ e.φ
  strat := stratified_and.mpr ⟨d.strat, e.strat⟩
  eval V _ v := by simp [d.eval, e.eval]

/-- Disjunction. -/
def or (d : SDef τ R) (e : SDef τ S) : SDef τ (fun V _ v ↦ R V v ∨ S V v) where
  φ := d.φ ⋎ e.φ
  strat := stratified_or.mpr ⟨d.strat, e.strat⟩
  eval V _ v := by simp [d.eval, e.eval]

/-- Negation. -/
def not (d : SDef τ R) : SDef τ (fun V _ v ↦ ¬ R V v) where
  φ := ∼d.φ
  strat := stratified_neg.mpr d.strat
  eval V _ v := by simp [d.eval]

/-- Implication. -/
def imp (d : SDef τ R) (e : SDef τ S) : SDef τ (fun V _ v ↦ R V v → S V v) where
  φ := d.φ 🡒 e.φ
  strat := stratified_imp.mpr ⟨d.strat, e.strat⟩
  eval V _ v := by simp [d.eval, e.eval]

/-- Equivalence. -/
def iff (d : SDef τ R) (e : SDef τ S) : SDef τ (fun V _ v ↦ (R V v ↔ S V v)) :=
  ((d.imp e).and (e.imp d)).congr fun _ _ _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Universal quantification over a new first variable of type `t`. -/
def all (t : ℕ) {R : URel (k + 1)} (d : SDef (t :> τ) R) :
    SDef τ (fun V _ v ↦ ∀ a : V, R V (a :> v)) where
  φ := ∀¹ d.φ
  strat := stratified_all.mpr ⟨t, d.strat⟩
  eval V _ v := by simp [d.eval]

/-- Existential quantification over a new first variable of type `t`. -/
def ex (t : ℕ) {R : URel (k + 1)} (d : SDef (t :> τ) R) :
    SDef τ (fun V _ v ↦ ∃ a : V, R V (a :> v)) where
  φ := ∃¹ d.φ
  strat := stratified_exs.mpr ⟨t, d.strat⟩
  eval V _ v := by simp [d.eval]

/-- Substitution of variables: `R (v ∘ f)`, when the types match up to a shift by `c`. -/
def comp {m : ℕ} {τ' : Fin m → ℕ} (d : SDef τ R) (f : Fin k → Fin m) (c : ℕ)
    (hf : ∀ i, τ' (f i) = τ i + c := by sd_ty) :
    SDef τ' (fun V _ v ↦ R V (fun i ↦ v (f i))) where
  φ := Rew.subst (fun i ↦ (#(f i) : Semiterm ℒₛₑₜ Empty m)) ▹ d.φ
  strat := Semiformula.stratified_rew c d.φ _ τ τ' (by intro x; simp [hf])
    (fun x => x.elim) d.strat
  eval V _ v := by
    have : (Semiterm.val v Empty.elim ∘ fun i ↦ (#(f i) : Semiterm ℒₛₑₜ Empty m)) =
        fun i ↦ v (f i) := by funext i; simp
    simp only [eval_substs, this]
    exact d.eval V _

end SDef

/-! ### Comprehension in a model of `𝗡𝗙` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

/-- Extensionality in a model of `𝗡𝗙`. -/
theorem nf_ext {x y : V} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  have := by
    simpa [models_iff] using Theory.models V 𝗡𝗙 NewFoundations.extensionality
  exact this x y h

/-- **Stratified comprehension in a model of `𝗡𝗙`**: if `R` has a stratified definition, then
`{x | R (x, p)}` is a set, for all parameters `p`. -/
theorem SDef.comprehension {k : ℕ} {τ : Fin (k + 1) → ℕ} {R : URel (k + 1)} (d : SDef τ R)
    (p : Fin k → V) : ∃ y : V, ∀ x, x ∈ y ↔ R V (x :> p) := by
  classical
  let ω : Rew ℒₛₑₜ Empty (k + 1) ℕ 1 :=
    Rew.bind ((#0 : Semiterm ℒₛₑₜ ℕ 1) :> fun i : Fin k ↦ &(i : ℕ)) Empty.elim
  let ψ : SetTheorySemiproposition 1 := ω ▹ d.φ
  let σ : ℕ → ℕ := fun n ↦ if h : n < k then τ (Fin.succ ⟨n, h⟩) else 0
  have hψ : ψ.IsStratified :=
    ⟨σ, ![τ 0], Semiformula.stratified_rew 0 d.φ ω τ ![τ 0]
      (by
        intro x
        cases x using Fin.cases with
        | zero => simp [ω]
        | succ x => simp [ω, σ]; rfl)
      (fun x => x.elim) d.strat⟩
  have := by
    simpa [models_iff, Axiom.comprehensionSchema] using
      Theory.models V 𝗡𝗙 (NewFoundations.comprehension ψ hψ)
  let x₀ : V := Classical.arbitrary V
  obtain ⟨y, hy⟩ := this (fun n ↦ if h : n < k then p ⟨n, h⟩ else x₀)
  refine ⟨y, fun x => (hy x).trans ?_⟩
  have e : (Semiterm.val ![x] (fun n ↦ if h : n < k then p ⟨n, h⟩ else x₀) ∘ ω ∘ Semiterm.bvar) =
      (x :> p) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [ω]
    | succ i => simp [ω]
  have e2 : (Semiterm.val ![x] (fun n ↦ if h : n < k then p ⟨n, h⟩ else x₀) ∘ ω ∘
      Semiterm.fvar) = (Empty.elim : Empty → V) := funext fun z => z.elim
  rw [eval_rew, e, e2]
  exact d.eval V _

end model

end SetTheory

end FFL.FirstOrder
