import MacModel

set_option autoImplicit false

/-!
# Working inside a model of `𝗠`

To use bounded separation one needs a bounded formula and its meaning. `BDef R` packages the
two: a formula of `ℒₛₑₜ` with `k` variables that is bounded and defines the relation `R` in every
structure. `FDef R` is the same without the bound. Both are built with combinators, so no
formula is written out by hand.

In a model of `𝗠`:

* `BDef.sep`: `{z ∈ a | R (z, p)}` is a set, when `R` has a bounded definition;
* `sep_raw`: the same for a bounded formula with parameters;
* the axioms of the base theory as statements about the model (`m_ext`, `m_empty`, `m_pair`,
  `m_union`, `m_power`, `m_inf`, `m_found`).
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

/-- A relation of `k` arguments on every structure. -/
abbrev MRel (k : ℕ) := ∀ (V : Type) [SetStructure V], (Fin k → V) → Prop

/-- A formula that defines the relation `R` in every structure. -/
structure FDef {k : ℕ} (R : MRel k) where
  /-- The formula. -/
  φ : Semisentence ℒₛₑₜ k
  /-- It defines `R`. -/
  eval : ∀ (V : Type) [SetStructure V] (v : Fin k → V), V ⊧/v φ ↔ R V v

/-- A bounded formula that defines the relation `R` in every structure. -/
structure BDef {k : ℕ} (R : MRel k) extends FDef R where
  /-- The formula is bounded. -/
  bdd : (Bounding.mem ℒₛₑₜ).Closure φ

/-- The membership operator, as it appears in bounded quantifiers. -/
abbrev memOp : Semiformula.Operator ℒₛₑₜ 2 := Semiformula.Operator.Mem.mem

namespace BDef

variable {k : ℕ}

/-- The same formula defines every relation equivalent to `R`. -/
def congr {R R' : MRel k} (d : BDef R)
    (h : ∀ (V : Type) [SetStructure V] (v : Fin k → V), R V v ↔ R' V v) : BDef R' where
  φ := d.φ
  bdd := d.bdd
  eval V _ v := (d.eval V v).trans (h V v)

/-- Falsity. -/
def fls : BDef (k := k) (fun _ _ _ ↦ False) where
  φ := ⊥
  bdd := by simp
  eval V _ v := by simp

/-- `vᵢ ∈ vⱼ`. -/
def mem (i j : Fin k) : BDef (fun _ _ v ↦ v i ∈ v j) where
  φ := Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![#i, #j]
  bdd := by simp
  eval V _ v := Iff.rfl

/-- `vᵢ = vⱼ`. -/
def eq (i j : Fin k) : BDef (fun _ _ v ↦ v i = v j) where
  φ := Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![#i, #j]
  bdd := by simp
  eval V _ v := Iff.rfl

variable {R S : MRel k}

/-- Conjunction. -/
def and (d : BDef R) (e : BDef S) : BDef (fun V _ v ↦ R V v ∧ S V v) where
  φ := d.φ ⋏ e.φ
  bdd := by simp [d.bdd, e.bdd]
  eval V _ v := by simp [d.eval, e.eval]

/-- Disjunction. -/
def or (d : BDef R) (e : BDef S) : BDef (fun V _ v ↦ R V v ∨ S V v) where
  φ := d.φ ⋎ e.φ
  bdd := by simp [d.bdd, e.bdd]
  eval V _ v := by simp [d.eval, e.eval]

/-- Negation. -/
def not (d : BDef R) : BDef (fun V _ v ↦ ¬R V v) where
  φ := ∼d.φ
  bdd := by simp [d.bdd]
  eval V _ v := by simp [d.eval]

/-- Implication. -/
def imp (d : BDef R) (e : BDef S) : BDef (fun V _ v ↦ R V v → S V v) :=
  (d.not.or e).congr fun _ _ _ => by tauto

/-- Equivalence. -/
def iff (d : BDef R) (e : BDef S) : BDef (fun V _ v ↦ (R V v ↔ S V v)) :=
  ((d.imp e).and (e.imp d)).congr fun _ _ _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Bounded universal quantification: for all `a ∈ vⱼ`. The new variable comes first. -/
def ball (j : Fin k) {R : MRel (k + 1)} (d : BDef R) :
    BDef (fun V _ v ↦ ∀ a : V, a ∈ v j → R V (a :> v)) where
  φ := ∀¹[memOp.operator ![#0, #j.succ]] d.φ
  bdd := Bounding.Closure.ball (Set.mem_singleton_iff.mpr rfl) (by simp [Semiterm.Positive])
    d.bdd
  eval V _ v := by simp [eval_memOp, d.eval]

/-- Bounded existential quantification: for some `a ∈ vⱼ`. The new variable comes first. -/
def bex (j : Fin k) {R : MRel (k + 1)} (d : BDef R) :
    BDef (fun V _ v ↦ ∃ a : V, a ∈ v j ∧ R V (a :> v)) where
  φ := ∃¹[memOp.operator ![#0, #j.succ]] d.φ
  bdd := Bounding.Closure.bexs (Set.mem_singleton_iff.mpr rfl) (by simp [Semiterm.Positive])
    d.bdd
  eval V _ v := by simp [eval_memOp, d.eval]

/-- Substitution of variables: `R (v ∘ f)`. -/
def comp {m : ℕ} (d : BDef R) (f : Fin k → Fin m) : BDef (fun V _ v ↦ R V (fun i ↦ v (f i))) where
  φ := Rew.subst (fun i ↦ (#(f i) : Semiterm ℒₛₑₜ Empty m)) ▹ d.φ
  bdd := d.bdd.rew _
  eval V _ v := by
    have : (Semiterm.val v Empty.elim ∘ fun i ↦ (#(f i) : Semiterm ℒₛₑₜ Empty m)) =
        fun i ↦ v (f i) := by funext i; simp
    simp only [eval_substs, this]
    exact d.eval V _

end BDef

namespace FDef

variable {k : ℕ} {R S : MRel k}

/-- The same formula defines every relation equivalent to `R`. -/
def congr {R R' : MRel k} (d : FDef R)
    (h : ∀ (V : Type) [SetStructure V] (v : Fin k → V), R V v ↔ R' V v) : FDef R' where
  φ := d.φ
  eval V _ v := (d.eval V v).trans (h V v)

/-- Truth. -/
def tru : FDef (k := k) (fun _ _ _ ↦ True) where
  φ := ⊤
  eval V _ v := by simp

/-- Conjunction. -/
def and (d : FDef R) (e : FDef S) : FDef (fun V _ v ↦ R V v ∧ S V v) where
  φ := d.φ ⋏ e.φ
  eval V _ v := by simp [d.eval, e.eval]

/-- Implication. -/
def imp (d : FDef R) (e : FDef S) : FDef (fun V _ v ↦ R V v → S V v) where
  φ := d.φ 🡒 e.φ
  eval V _ v := by simp [d.eval, e.eval]

/-- Equivalence. -/
def iff (d : FDef R) (e : FDef S) : FDef (fun V _ v ↦ (R V v ↔ S V v)) :=
  ((d.imp e).and (e.imp d)).congr fun _ _ _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Universal quantification over a new first variable. -/
def all {R : MRel (k + 1)} (d : FDef R) : FDef (fun V _ v ↦ ∀ a : V, R V (a :> v)) where
  φ := ∀¹ d.φ
  eval V _ v := by simp [d.eval]

/-- Existential quantification over a new first variable. -/
def ex {R : MRel (k + 1)} (d : FDef R) : FDef (fun V _ v ↦ ∃ a : V, R V (a :> v)) where
  φ := ∃¹ d.φ
  eval V _ v := by simp [d.eval]

/-- Substitution of variables: `R (v ∘ f)`. -/
def comp {m : ℕ} (d : FDef R) (f : Fin k → Fin m) : FDef (fun V _ v ↦ R V (fun i ↦ v (f i))) where
  φ := Rew.subst (fun i ↦ (#(f i) : Semiterm ℒₛₑₜ Empty m)) ▹ d.φ
  eval V _ v := by
    have : (Semiterm.val v Empty.elim ∘ fun i ↦ (#(f i) : Semiterm ℒₛₑₜ Empty m)) =
        fun i ↦ v (f i) := by funext i; simp
    simp only [eval_substs, this]
    exact d.eval V _

end FDef

/-! ### In a model of `𝗠` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-- **Bounded separation**, for a bounded formula with parameters. -/
theorem sep_raw (ψ : SetTheorySemiproposition 1) (hψ : (Bounding.mem ℒₛₑₜ).Closure ψ)
    (ε : ℕ → V) (a : V) : ∃ y : V, ∀ z, z ∈ y ↔ z ∈ a ∧ Eval (M := V) ![z] ε ψ := by
  have := by
    simpa [models_iff, Semiformula.eval_univCl, Axiom.separationSchema,
      Matrix.constant_eq_singleton] using
      Theory.models V 𝗠 (Or.inl (Or.inr (BoundedSeparation.separation ψ hψ)))
  exact this ε a

/-- **Bounded separation**: if `R` has a bounded definition, then `{z ∈ a | R (z, p)}` is a set,
for all parameters `p`. -/
theorem BDef.sep {k : ℕ} {R : MRel (k + 1)} (d : BDef R) (a : V) (p : Fin k → V) :
    ∃ y : V, ∀ z, z ∈ y ↔ z ∈ a ∧ R V (z :> p) := by
  classical
  let ω : Rew ℒₛₑₜ Empty (k + 1) ℕ 1 :=
    Rew.bind ((#0 : Semiterm ℒₛₑₜ ℕ 1) :> fun i : Fin k ↦ &(i : ℕ)) Empty.elim
  let x₀ : V := Classical.arbitrary V
  obtain ⟨y, hy⟩ := sep_raw (ω ▹ d.φ) (d.bdd.rew ω)
    (fun n ↦ if h : n < k then p ⟨n, h⟩ else x₀) a
  refine ⟨y, fun z => (hy z).trans (and_congr Iff.rfl ?_)⟩
  have e : (Semiterm.val ![z] (fun n ↦ if h : n < k then p ⟨n, h⟩ else x₀) ∘ ω ∘ Semiterm.bvar) =
      (z :> p) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [ω]
    | succ i => simp [ω]
  have e2 : (Semiterm.val ![z] (fun n ↦ if h : n < k then p ⟨n, h⟩ else x₀) ∘ ω ∘
      Semiterm.fvar) = (Empty.elim : Empty → V) := funext fun z => z.elim
  rw [eval_rew, e, e2]
  exact d.eval V _

theorem m_ext {x y : V} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  have := by
    simpa [models_iff] using Theory.models V 𝗠 (Or.inl (Or.inl BasicSetTheory.extensionality))
  exact (this x y).mpr h

theorem m_empty : ∃ e : V, ∀ z, z ∉ e := by
  simpa [models_iff, IsEmpty] using Theory.models V 𝗠 (Or.inl (Or.inl BasicSetTheory.empty_set))

theorem m_pair (x y : V) : ∃ p : V, ∀ w, w ∈ p ↔ w = x ∨ w = y := by
  have := by
    simpa [models_iff] using Theory.models V 𝗠 (Or.inl (Or.inl BasicSetTheory.pairing))
  exact this x y

theorem m_union (x : V) : ∃ u : V, ∀ z, z ∈ u ↔ ∃ w ∈ x, z ∈ w := by
  have := by
    simpa [models_iff] using Theory.models V 𝗠 (Or.inl (Or.inl BasicSetTheory.union))
  exact this x

theorem m_power (x : V) : ∃ p : V, ∀ z, z ∈ p ↔ ∀ w ∈ z, w ∈ x := by
  have := by
    simpa [models_iff, subset_def] using
      Theory.models V 𝗠 (Or.inl (Or.inl BasicSetTheory.power_set))
  exact this x

theorem m_inf : ∃ I : V, (∀ e : V, (∀ z, z ∉ e) → e ∈ I) ∧
    ∀ x ∈ I, ∀ x' : V, (∀ z, z ∈ x' ↔ z = x ∨ z ∈ x) → x' ∈ I := by
  simpa [models_iff, IsEmpty, val_isSucc_iff] using
    Theory.models V 𝗠 (Or.inl (Or.inl BasicSetTheory.infinity))

theorem m_found (x : V) (h : ∃ y, y ∈ x) : ∃ y ∈ x, ∀ z ∈ x, z ∉ y := by
  have := by
    simpa [models_iff, isNonempty_def] using
      Theory.models V 𝗠 (Or.inl (Or.inl BasicSetTheory.foundation))
  obtain ⟨y, hy⟩ := h
  exact this x y hy

end model

end FFL.FirstOrder.SetTheory
