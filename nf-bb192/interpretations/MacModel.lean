import MacTheories
import Foundation.FirstOrder.SetTheory.Z.Model

set_option autoImplicit false

/-!
# A sufficient condition for a structure to be a model of `𝗠`

`IsMacBase V` lists properties of a structure `V` with a membership relation, all but one of
them plain statements about `V`:

* extensionality, foundation and infinity;
* weak forms of pairing and power set, which give a set that includes the pair or the power
  set, and transitive containment;
* `sep`: for every `t`, every subset of the members of `t` that is definable, with parameters,
  in the structure formed by the members of `t`, is the extension of an element of `V`.

`IsMacBase.models` shows that such a structure is a model of `𝗠`. The exact forms of pairing,
union and power set come from the weak forms and separation for bounded formulas, and that
comes from `sep` and the absoluteness of bounded formulas for transitive sets
(`eval_submodel_iff`).

Nothing here mentions NF.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

variable {V : Type*} [SetStructure V]

/-- The members of `t`, as a set of the metatheory. -/
def extSet (t : V) : Set V := {z | z ∈ t}

@[simp] lemma mem_extSet {t z : V} : z ∈ extSet t ↔ z ∈ t := Iff.rfl

/-! ### Bounded formulas are absolute for transitive sets -/

section absoluteness

variable {U : Set V}

lemma val_submodel {ξ : Type*} {n : ℕ} (t : Semiterm ℒₛₑₜ ξ n) (e : Fin n → U) (ε : ξ → U) :
    ((t.val (M := U) e ε : U) : V) =
      t.val (M := V) (fun i ↦ (e i : V)) (fun x ↦ (ε x : V)) := by
  match t with
  | #x => simp
  | &x => simp
  | .func f _ => exact Empty.elim f

lemma val_positive {ξ : Type*} {n : ℕ} (t : Semiterm ℒₛₑₜ ξ (n + 1)) (ht : t.Positive)
    (e : Fin n → U) (ε : ξ → U) :
    ∃ u : U, (∀ x : U, t.val (M := U) (x :> e) ε = u) ∧
      ∀ x : V, t.val (M := V) (x :> fun i ↦ (e i : V)) (fun k ↦ (ε k : V)) = u := by
  match t with
  | #i =>
    cases i using Fin.cases with
    | zero => simp [Semiterm.Positive] at ht
    | succ j => exact ⟨e j, by simp, by simp⟩
  | &k => exact ⟨ε k, by simp, by simp⟩
  | .func f _ => exact Empty.elim f

lemma eval_memOp {W : Type*} [SetStructure W] {ξ : Type*} {n : ℕ} (b : Fin (n + 1) → W)
    (f : ξ → W) (t : Semiterm ℒₛₑₜ ξ (n + 1)) :
    Eval (M := W) b f
        ((Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).operator ![#0, t]) ↔
      b 0 ∈ t.val b f := by
  rw [Semiformula.Operator.mem_def]; rfl

/-- **Bounded formulas are absolute for transitive sets.** -/
theorem eval_submodel_iff (hU : ∀ y ∈ U, ∀ z ∈ y, z ∈ U) {ξ : Type*} {n : ℕ}
    {φ : Semiformula ℒₛₑₜ ξ n} (h : (Bounding.mem ℒₛₑₜ).Closure φ) :
    ∀ (e : Fin n → U) (ε : ξ → U),
      Eval (M := U) e ε φ ↔ Eval (M := V) (fun i ↦ (e i : V)) (fun x ↦ (ε x : V)) φ := by
  induction h with
  | verum n => intro e ε; simp
  | falsum n => intro e ε; simp
  | rel r v =>
    intro e ε
    cases r with
    | eq =>
      show (Semiterm.val (M := U) e ε (v 0) = Semiterm.val (M := U) e ε (v 1)) ↔
        (Semiterm.val (M := V) _ _ (v 0) = Semiterm.val (M := V) _ _ (v 1))
      rw [← val_submodel, ← val_submodel]
      exact Subtype.ext_iff
    | mem =>
      show (Semiterm.val (M := U) e ε (v 0) ∈ Semiterm.val (M := U) e ε (v 1)) ↔
        (Semiterm.val (M := V) _ _ (v 0) ∈ Semiterm.val (M := V) _ _ (v 1))
      rw [← val_submodel, ← val_submodel]
      exact Iff.rfl
  | nrel r v =>
    intro e ε
    cases r with
    | eq =>
      show ¬ (Semiterm.val (M := U) e ε (v 0) = Semiterm.val (M := U) e ε (v 1)) ↔
        ¬ (Semiterm.val (M := V) _ _ (v 0) = Semiterm.val (M := V) _ _ (v 1))
      rw [← val_submodel, ← val_submodel]
      exact not_congr Subtype.ext_iff
    | mem =>
      show ¬ (Semiterm.val (M := U) e ε (v 0) ∈ Semiterm.val (M := U) e ε (v 1)) ↔
        ¬ (Semiterm.val (M := V) _ _ (v 0) ∈ Semiterm.val (M := V) _ _ (v 1))
      rw [← val_submodel, ← val_submodel]
      exact Iff.rfl
  | and _ _ ih₁ ih₂ => intro e ε; simp [ih₁ e ε, ih₂ e ε]
  | or _ _ ih₁ ih₂ => intro e ε; simp [ih₁ e ε, ih₂ e ε]
  | @ball n R φ t hR ht _ ih =>
    intro e ε
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨u, hu₁, hu₂⟩ := val_positive t ht e ε
    have key : ∀ (x : V) (hx : x ∈ U),
        (fun i ↦ (((⟨x, hx⟩ : U) :> e) i : V)) = (x :> fun i ↦ (e i : V)) := by
      intro x hx; funext i; cases i using Fin.cases <;> simp
    simp only [eval_ball, eval_memOp, Matrix.cons_val_zero]
    constructor
    · intro H x hx
      rw [hu₂ x] at hx
      have hxU : x ∈ U := hU u u.2 x hx
      have := (ih (⟨x, hxU⟩ :> e) ε).mp (H ⟨x, hxU⟩ (by rw [hu₁]; exact hx))
      rwa [key] at this
    · intro H x hx
      rw [hu₁ x] at hx
      have := H x (by rw [hu₂]; exact hx)
      rw [← key x x.2] at this
      exact (ih (x :> e) ε).mpr this
  | @bexs n R φ t hR ht _ ih =>
    intro e ε
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨u, hu₁, hu₂⟩ := val_positive t ht e ε
    have key : ∀ (x : V) (hx : x ∈ U),
        (fun i ↦ (((⟨x, hx⟩ : U) :> e) i : V)) = (x :> fun i ↦ (e i : V)) := by
      intro x hx; funext i; cases i using Fin.cases <;> simp
    simp only [eval_bexs, eval_memOp, Matrix.cons_val_zero]
    constructor
    · rintro ⟨x, hx, H⟩
      rw [hu₁ x] at hx
      refine ⟨x, by rw [hu₂]; exact hx, ?_⟩
      have := (ih (x :> e) ε).mp H
      rwa [key x x.2] at this
    · rintro ⟨x, hx, H⟩
      rw [hu₂ x] at hx
      have hxU : x ∈ U := hU u u.2 x hx
      refine ⟨⟨x, hxU⟩, by rw [hu₁]; exact hx, ?_⟩
      rw [← key x hxU] at H
      exact (ih (⟨x, hxU⟩ :> e) ε).mpr H

end absoluteness

/-! ### The condition -/

/-- A structure with these properties is a model of `𝗠` (`IsMacBase.models`). -/
structure IsMacBase (V : Type*) [SetStructure V] : Prop where
  /-- Extensionality. -/
  ext : ∀ x y : V, (∀ z, z ∈ x ↔ z ∈ y) → x = y
  /-- Foundation. -/
  found : ∀ x : V, (∃ y, y ∈ x) → ∃ y ∈ x, ∀ z ∈ x, z ∉ y
  /-- Any two elements are members of one element. -/
  pair : ∀ x y : V, ∃ p : V, x ∈ p ∧ y ∈ p
  /-- The subsets of an element are members of one element. -/
  power : ∀ x : V, ∃ p : V, ∀ z : V, (∀ w ∈ z, w ∈ x) → z ∈ p
  /-- Transitive containment. -/
  tco : ∀ x : V, ∃ t : V, (∀ z ∈ x, z ∈ t) ∧ ∀ y ∈ t, ∀ z ∈ y, z ∈ t
  /-- Infinity: an element with an empty member that has, with each member `x`, a member whose
  members are `x` and the members of `x`. -/
  inf : ∃ I : V, (∃ e ∈ I, ∀ z, z ∉ e) ∧
    ∀ x ∈ I, ∃ x' ∈ I, ∀ z, z ∈ x' ↔ z = x ∨ z ∈ x
  /-- Every subset of the members of `t` that is definable in the structure of the members of
  `t` is the extension of an element. -/
  sep : ∀ (t : V) (ψ : SetTheorySemiproposition 1) (ε : ℕ → extSet t),
    ∃ y : V, ∀ z, z ∈ y ↔ ∃ hz : z ∈ extSet t, Eval (M := extSet t) ![⟨z, hz⟩] ε ψ

namespace IsMacBase

variable (h : IsMacBase V)
include h

lemma nonempty : Nonempty V := let ⟨I, _⟩ := h.inf; ⟨I⟩

/-- Finitely many elements are members of one transitive element. -/
lemma exists_trans_of_list (l : List V) :
    ∃ t : V, (∀ y ∈ t, ∀ z ∈ y, z ∈ t) ∧ ∀ a ∈ l, a ∈ t := by
  induction l with
  | nil =>
    obtain ⟨I, -⟩ := h.inf
    obtain ⟨t, -, ht⟩ := h.tco I
    exact ⟨t, ht, by simp⟩
  | cons a l ih =>
    obtain ⟨t₀, ht₀, hl⟩ := ih
    obtain ⟨p, hap, htp⟩ := h.pair a t₀
    obtain ⟨t, hpt, ht⟩ := h.tco p
    refine ⟨t, ht, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hpt _ hap
    · exact ht t₀ (hpt _ htp) b (hl b hb)

/-- **Separation for bounded formulas.** -/
theorem bounded_separation (φ : SetTheorySemiproposition 1)
    (hφ : (Bounding.mem ℒₛₑₜ).Closure φ) (ε : ℕ → V) (x : V) :
    ∃ y : V, ∀ z, z ∈ y ↔ z ∈ x ∧ Eval (M := V) ![z] ε φ := by
  classical
  obtain ⟨t, htr, hl⟩ := h.exists_trans_of_list (x :: (List.range φ.fvSup).map ε)
  have hx : x ∈ extSet t := hl x (by simp)
  have hε : ∀ k, φ.FVar? k → ε k ∈ extSet t := fun k hk =>
    hl _ (List.mem_cons_of_mem _ (List.mem_map.mpr
      ⟨k, List.mem_range.mpr (lt_fvSup_of_fvar? hk), rfl⟩))
  let ε' : ℕ → extSet t := fun k =>
    match k with
    | 0 => ⟨x, hx⟩
    | k + 1 => if hk : ε k ∈ extSet t then ⟨ε k, hk⟩ else ⟨x, hx⟩
  let ψ : SetTheorySemiproposition 1 :=
    (Rew.rewriteMap (L := ℒₛₑₜ) (n := 1) Nat.succ ▹ φ) ⋏ Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![#0, &0]
  obtain ⟨y, hy⟩ := h.sep t ψ ε'
  have htr' : ∀ y ∈ extSet t, ∀ z ∈ y, z ∈ extSet t := htr
  refine ⟨y, fun z => (hy z).trans ?_⟩
  constructor
  · rintro ⟨hz, H⟩
    have H1 : Eval (M := extSet t) ![⟨z, hz⟩] (fun k ↦ ε' (k + 1)) φ :=
      (eval_rewriteMap (L := ℒₛₑₜ) Nat.succ φ).mp H.1
    have H2 : z ∈ x := H.2
    refine ⟨H2, ?_⟩
    have := (eval_submodel_iff htr' hφ _ _).mp H1
    have e1 : (fun i ↦ ((![(⟨z, hz⟩ : extSet t)] i : extSet t) : V)) = ![z] := by
      funext i; simp
    rw [e1] at this
    refine (eval_iff_of_funEqOn φ ?_).mp this
    intro k hk
    have hk' : ε k ∈ extSet t := hε k hk
    show ((ε' (k + 1) : extSet t) : V) = ε k
    simp only [ε']
    split
    · rfl
    · exact absurd hk' ‹_›
  · rintro ⟨hzx, H⟩
    have hz : z ∈ extSet t := htr x hx z hzx
    refine ⟨hz, (eval_rewriteMap (L := ℒₛₑₜ) Nat.succ φ).mpr ?_, hzx⟩
    refine (eval_submodel_iff htr' hφ _ _).mpr ?_
    have e1 : (fun i ↦ ((![(⟨z, hz⟩ : extSet t)] i : extSet t) : V)) = ![z] := by
      funext i; simp
    rw [e1]
    refine (eval_iff_of_funEqOn φ ?_).mp H
    intro k hk
    have hk' : ε k ∈ extSet t := hε k hk
    show ε k = ((ε' (k + 1) : extSet t) : V)
    simp only [ε']
    split
    · rfl
    · exact absurd hk' ‹_›

/-- The empty set. -/
lemma exists_empty : ∃ e : V, ∀ z, z ∉ e := let ⟨_, ⟨e, _, he⟩, _⟩ := h.inf; ⟨e, he⟩

/-- Pairing. -/
lemma pairing (x y : V) : ∃ p : V, ∀ w, w ∈ p ↔ w = x ∨ w = y := by
  obtain ⟨p₀, hx, hy⟩ := h.pair x y
  obtain ⟨p, hp⟩ := h.bounded_separation
    (Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![#0, &0] ⋎
      Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![#0, &1])
    (by simp) (fun k ↦ if k = 0 then x else y) p₀
  refine ⟨p, fun w => (hp w).trans ?_⟩
  have : Eval (M := V) ![w] (fun k ↦ if k = 0 then x else y)
      (Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![#0, &0] ⋎
      Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![#0, &1]) ↔
      w = x ∨ w = y := by
    simp [eval_rel]
  rw [this]
  constructor
  · exact fun H => H.2
  · rintro (rfl | rfl)
    · exact ⟨hx, Or.inl rfl⟩
    · exact ⟨hy, Or.inr rfl⟩

/-- Union. -/
lemma union (x : V) : ∃ u : V, ∀ z, z ∈ u ↔ ∃ w ∈ x, z ∈ w := by
  obtain ⟨t, hxt, ht⟩ := h.tco x
  obtain ⟨u, hu⟩ := h.bounded_separation
    (∃¹[(Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).operator ![#0, &0]]
      Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![#1, #0])
    (.bexs (Set.mem_singleton_iff.mpr rfl) (by simp [Semiterm.Positive]) (by simp))
    (fun _ ↦ x) t
  refine ⟨u, fun z => (hu z).trans ?_⟩
  have : Eval (M := V) ![z] (fun _ ↦ x)
      (∃¹[(Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).operator ![#0, &0]]
        Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![#1, #0]) ↔ ∃ w ∈ x, z ∈ w := by
    simp [eval_rel]
  rw [this]
  constructor
  · exact fun H => H.2
  · rintro ⟨w, hw, hz⟩
    exact ⟨ht w (hxt w hw) z hz, w, hw, hz⟩

/-- Power set. -/
lemma powerset (x : V) : ∃ p : V, ∀ z, z ∈ p ↔ ∀ w ∈ z, w ∈ x := by
  obtain ⟨p₀, hp₀⟩ := h.power x
  obtain ⟨p, hp⟩ := h.bounded_separation
    (∀¹[(Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).operator ![#0, #1]]
      Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![#0, &0])
    (.ball (Set.mem_singleton_iff.mpr rfl) (by simp [Semiterm.Positive]) (by simp))
    (fun _ ↦ x) p₀
  refine ⟨p, fun z => (hp z).trans ?_⟩
  have : Eval (M := V) ![z] (fun _ ↦ x)
      (∀¹[(Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).operator ![#0, #1]]
        Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![#0, &0]) ↔ ∀ w ∈ z, w ∈ x := by
    simp [eval_rel]
  rw [this]
  exact ⟨fun H => H.2, fun H => ⟨hp₀ z H, H⟩⟩

/-- **A structure with the properties `IsMacBase` is a model of `𝗠`.** -/
theorem models [Nonempty V] : V↓[ℒₛₑₜ] ⊧* 𝗠 := by
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with (hφ | hφ) | hφ
  · cases hφ with
    | equality φ hφ =>
      have : V↓[ℒₛₑₜ] ⊧* (𝗘𝗤 _ : SetTheory) := inferInstance
      exact models_theory_iff.mp this φ hφ
    | empty_set =>
      obtain ⟨e, he⟩ := h.exists_empty
      simpa [models_iff, isEmpty] using ⟨e, he⟩
    | extensionality =>
      suffices ∀ x y : V, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y by simpa [models_iff]
      exact fun x y => ⟨fun e z => by rw [e], h.ext x y⟩
    | pairing =>
      simpa [models_iff] using h.pairing
    | union =>
      simpa [models_iff] using h.union
    | power_set =>
      simpa [models_iff, isSubsetOf] using h.powerset
    | infinity =>
      obtain ⟨I, ⟨e, heI, he⟩, hs⟩ := h.inf
      suffices ∃ I : V, (∀ e : V, (∀ y, y ∉ e) → e ∈ I) ∧
          ∀ x ∈ I, ∀ x' : V, (∀ z, z ∈ x' ↔ z = x ∨ z ∈ x) → x' ∈ I by
        simpa [models_iff, isEmpty, isSucc]
      refine ⟨I, fun e' he' => ?_, fun x hx x' hx' => ?_⟩
      · have : e' = e := h.ext _ _ fun z => ⟨fun hz => absurd hz (he' z), fun hz => absurd hz (he z)⟩
        rw [this]; exact heI
      · obtain ⟨x'', hx''I, hx''⟩ := hs x hx
        have : x' = x'' := h.ext _ _ fun z => (hx' z).trans (hx'' z).symm
        rw [this]; exact hx''I
    | foundation =>
      suffices ∀ x : V, (∃ y, y ∈ x) → ∃ y ∈ x, ∀ z ∈ x, z ∉ y by
        simpa [models_iff, isNonempty]
      exact h.found
  · cases hφ with
    | separation φ hφ =>
      suffices ∀ (ε : ℕ → V) (x : V), ∃ y : V, ∀ z, z ∈ y ↔ z ∈ x ∧ Eval (M := V) ![z] ε φ by
        simpa [models_iff, Semiformula.eval_univCl, Axiom.separationSchema,
          Matrix.constant_eq_singleton]
      exact fun ε x => h.bounded_separation φ hφ ε x
  · have e : φ = Axiom.transitiveContainment := hφ
    rw [e]
    suffices ∀ x : V, ∃ t : V, (∀ z ∈ x, z ∈ t) ∧ ∀ y ∈ t, ∀ z ∈ y, z ∈ t by
      simpa [models_iff, Axiom.transitiveContainment, isSubsetOf]
    exact h.tco

end IsMacBase

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.eval_submodel_iff
#print axioms FFL.FirstOrder.SetTheory.IsMacBase.models
