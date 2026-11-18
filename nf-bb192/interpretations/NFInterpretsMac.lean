import NFMac
import NFUJensen

set_option autoImplicit false

/-!
# `𝗡𝗙` interprets `𝗠`

`𝗠` is Mathias's theory `M`: Mac Lane set theory with transitive containment and without choice
(`MacTheories.lean`).

The interpretation: the domain is `Hin.Dom`, the types of well-founded pointed graphs that
belong to a set of types which the type-raising map `θ` maps onto itself and which is closed
under members; membership is `Hin.EE`; equality is equality.

* `exists_definable_subset`: in a model of `𝗡𝗙`, every subset of a set structure that is
  definable in the structure, with parameters, is a set. The formula is rewritten with all its
  quantifiers restricted to the universe of the structure and membership read through the
  graph of the structure; the result is stratified whatever the formula was.
* `isMacBase_of_embed`: the types in `Hin.Dom` satisfy the conditions of `IsMacBase`, so they
  form a model of `𝗠` (`MacModel.lean`).
* `interpretsM : 𝗡𝗙 ⊳ 𝗠`, and `nfuInterpretsM : 𝗡𝗙𝗨𝗜 ⊳ 𝗠` by composition with `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`.

Every derivation here is obtained from the completeness theorem of the library and a theorem
about models, as in `NFInterpretations.lean`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

/-! ### Formulas without a stratification -/

/-- A formula that defines `R` in every structure. -/
structure UDef {k : ℕ} (R : URel k) where
  /-- The formula. -/
  φ : Semisentence ℒₛₑₜ k
  /-- It defines `R`. -/
  eval : ∀ (V : Type) [SetStructure V] (v : Fin k → V), V ⊧/v φ ↔ R V v

namespace UDef

variable {k : ℕ} {R S : URel k}

def ofS {τ : Fin k → ℕ} (d : SDef τ R) : UDef R := ⟨d.φ, d.eval⟩

def congr {R' : URel k} (d : UDef R)
    (h : ∀ (V : Type) [SetStructure V] (v : Fin k → V), R V v ↔ R' V v) : UDef R' :=
  ⟨d.φ, fun V _ v => (d.eval V v).trans (h V v)⟩

def mem (i j : Fin k) : UDef (k := k) (fun _ _ v ↦ v i ∈ v j) :=
  ⟨Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![#i, #j], fun _ _ _ => Iff.rfl⟩

def and (d : UDef R) (e : UDef S) : UDef (fun V _ v ↦ R V v ∧ S V v) :=
  ⟨d.φ ⋏ e.φ, fun V _ v => by simp [d.eval, e.eval]⟩

def ex {R : URel (k + 1)} (d : UDef R) : UDef (fun V _ v ↦ ∃ a : V, R V (a :> v)) :=
  ⟨∃¹ d.φ, fun V _ v => by simp [d.eval]⟩

def comp {m : ℕ} (d : UDef R) (f : Fin k → Fin m) :
    UDef (fun V _ v ↦ R V (fun i ↦ v (f i))) where
  φ := Rew.subst (fun i ↦ (#(f i) : Semiterm ℒₛₑₜ Empty m)) ▹ d.φ
  eval V _ v := by
    have : (Semiterm.val v Empty.elim ∘ fun i ↦ (#(f i) : Semiterm ℒₛₑₜ Empty m)) =
        fun i ↦ v (f i) := by funext i; simp
    simp only [eval_substs, this]
    exact d.eval V _

end UDef

namespace Hin

/-! ### The formulas of the interpretation -/

section fmls

variable {V : Type} [SetStructure V]

/-- `Stable g X`, with the two types at which `X` is used kept apart. -/
def StableS (g X X' : V) : Prop :=
  (∀ x, x ∈ X → InZ x) ∧ (∀ x, x ∈ X → ∀ y, IsType y g x → y ∈ X') ∧
    ∀ y, y ∈ X' → ∃ x, x ∈ X ∧ IsType y g x

end fmls

def stableSD : SDef ![9, 7, 13] (fun _ _ v ↦ StableS (v 0) (v 1) (v 2)) :=
  ((SDef.all 6 ((SDef.mem 0 2).imp (inZD.comp ![0] 0))).and
    ((SDef.all 6 ((SDef.mem 0 2).imp (SDef.all 12
        ((isTypeD.comp ![0, 2, 1] 6).imp (SDef.mem 0 4))))).and
      (SDef.all 12 ((SDef.mem 0 3).imp (SDef.ex 6
        ((SDef.mem 0 3).and (isTypeD.comp ![1, 2, 0] 6))))))).congr fun _ _ _ => Iff.rfl

def transD : SDef ![7] (fun _ _ v ↦ Trans (v 0)) :=
  (SDef.all 6 ((SDef.mem 0 1).imp (SDef.all 6
    ((eeD.comp ![0, 1] 0).imp (SDef.mem 0 2))))).congr fun _ _ _ => Iff.rfl

/-- The formula for the domain. It is not stratified: `Stable g X` uses `X` at two types. -/
def domU : UDef (k := 1) (fun _ _ v ↦ Dom (v 0)) :=
  (UDef.ex (UDef.ex (((UDef.ofS isEgD).comp ![1]).and
    (((UDef.ofS stableSD).comp ![1, 0, 0]).and
      (((UDef.ofS transD).comp ![0]).and (UDef.mem 2 0)))))).congr fun _ _ _ => Iff.rfl

/-! ### Definable subsets of a set structure -/

/-- A term with its parameters moved up by two, to make room for the universe and the graph of
the structure. -/
def sh {n : ℕ} : Semiterm ℒₛₑₜ ℕ n → Semiterm ℒₛₑₜ ℕ n
  | #x => #x
  | &x => &(x + 2)
  | .func f _ => Empty.elim f

/-- An atomic formula read in the structure with universe `&0` and graph `&1`. -/
def trRel {n : ℕ} :
    {k : ℕ} → (ℒₛₑₜ).Rel k → (Fin k → Semiterm ℒₛₑₜ ℕ n) → Semiformula ℒₛₑₜ ℕ n
  | _, Language.Set.Rel.eq, v => Semiformula.rel Language.Set.Rel.eq v
  | _, Language.Set.Rel.mem, v =>
    ∃¹ (Semiformula.rel Language.Set.Rel.mem ![#0, &1] ⋏
      (Rew.embSubsts ![#0, Rew.bShift (v 0), Rew.bShift (v 1)] ▹ isOpD.φ))

/-- A formula read in the structure with universe `&0` and graph `&1`. -/
def tr {n : ℕ} : Semiformula ℒₛₑₜ ℕ n → Semiformula ℒₛₑₜ ℕ n
  | .rel r v => trRel r (fun i ↦ sh (v i))
  | .nrel r v => ∼trRel r (fun i ↦ sh (v i))
  | ⊤ => ⊤
  | ⊥ => ⊥
  | φ ⋏ ψ => tr φ ⋏ tr ψ
  | φ ⋎ ψ => tr φ ⋎ tr ψ
  | ∀¹ φ => ∀¹ (Semiformula.rel Language.Set.Rel.mem ![#0, &0] 🡒 tr φ)
  | ∃¹ φ => ∃¹ (Semiformula.rel Language.Set.Rel.mem ![#0, &0] ⋏ tr φ)

/-- The types of the parameters: the universe has type `1`, the graph type `3`, the rest `0`. -/
def σr : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | _ + 2 => 0

lemma sh_lv {n : ℕ} (t : Semiterm ℒₛₑₜ ℕ n) (τ : Fin n → ℕ) (hτ : ∀ i, τ i = 0) :
    (sh t).lv σr τ = 0 := by
  match t with
  | #x => exact hτ x
  | &x => rfl
  | .func f _ => exact Empty.elim f

lemma trRel_strat {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ℕ n) (τ : Fin n → ℕ)
    (hv : ∀ i, (v i).lv σr τ = 0) : (trRel r v).Stratified σr τ := by
  cases r with
  | eq => exact stratified_rel.mpr ⟨0, fun i => by rw [hv i]; fin_cases i <;> rfl⟩
  | mem =>
    refine stratified_exs.mpr ⟨2, stratified_and.mpr
      ⟨stratified_rel.mpr ⟨2, fun i => by fin_cases i <;> rfl⟩, ?_⟩⟩
    refine Semiformula.stratified_rew 0 isOpD.φ _ ![2, 0, 0] (2 :> τ) ?_ (fun x => x.elim)
      isOpD.strat
    intro x
    fin_cases x
    · rfl
    · show (Rew.bShift (v 0)).lv σr (2 :> τ) = 0
      rw [Semiterm.lv_bShift]; exact hv 0
    · show (Rew.bShift (v 1)).lv σr (2 :> τ) = 0
      rw [Semiterm.lv_bShift]; exact hv 1

/-- **The rewritten formula is stratified**, whatever the formula was: every variable of the
formula gets type `0`. -/
theorem tr_strat : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) (τ : Fin n → ℕ), (∀ i, τ i = 0) →
    (tr φ).Stratified σr τ := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intros; trivial
  | hfalsum => intros; trivial
  | hrel r v => intro τ hτ; exact trRel_strat r _ τ fun i => sh_lv (v i) τ hτ
  | hnrel r v =>
    intro τ hτ
    exact stratified_neg.mpr (trRel_strat r _ τ fun i => sh_lv (v i) τ hτ)
  | hand φ ψ ih1 ih2 => intro τ hτ; exact stratified_and.mpr ⟨ih1 τ hτ, ih2 τ hτ⟩
  | hor φ ψ ih1 ih2 => intro τ hτ; exact stratified_or.mpr ⟨ih1 τ hτ, ih2 τ hτ⟩
  | hall φ ih =>
    intro τ hτ
    refine stratified_all.mpr ⟨0, stratified_imp.mpr
      ⟨stratified_rel.mpr ⟨0, fun i => by fin_cases i <;> rfl⟩, ih (0 :> τ) ?_⟩⟩
    intro i; cases i using Fin.cases with
    | zero => rfl
    | succ i => exact hτ i
  | hexs φ ih =>
    intro τ hτ
    refine stratified_exs.mpr ⟨0, stratified_and.mpr
      ⟨stratified_rel.mpr ⟨0, fun i => by fin_cases i <;> rfl⟩, ih (0 :> τ) ?_⟩⟩
    intro i; cases i using Fin.cases with
    | zero => rfl
    | succ i => exact hτ i

section relativise

variable {M : Type} [SetStructure M] {U : Type} [SetStructure U]

/-- The parameters: the universe, the graph, and the images of the parameters of the formula. -/
def rho (A R : M) (j : U → M) (ε : ℕ → U) : ℕ → M
  | 0 => A
  | 1 => R
  | k + 2 => j (ε k)

lemma sh_val (A R : M) (j : U → M) (ε : ℕ → U) {n : ℕ} (t : Semiterm ℒₛₑₜ ℕ n)
    (e : Fin n → U) :
    (sh t).val (M := M) (fun i ↦ j (e i)) (rho A R j ε) = j (t.val (M := U) e ε) := by
  match t with
  | #x => rfl
  | &x => rfl
  | .func f _ => exact Empty.elim f

lemma eval_and' {n : ℕ} (b : Fin n → M) (f : ℕ → M) (φ ψ : Semiformula ℒₛₑₜ ℕ n) :
    Eval (M := M) b f (φ ⋏ ψ) ↔ Eval (M := M) b f φ ∧ Eval (M := M) b f ψ := by simp

lemma eval_imp' {n : ℕ} (b : Fin n → M) (f : ℕ → M) (φ ψ : Semiformula ℒₛₑₜ ℕ n) :
    Eval (M := M) b f (φ 🡒 ψ) ↔ (Eval (M := M) b f φ → Eval (M := M) b f ψ) := by simp

lemma trRel_mem_eval {n : ℕ} (b : Fin n → M) (f : ℕ → M) (t u : Semiterm ℒₛₑₜ ℕ n) :
    Eval (M := M) b f (trRel Language.Set.Rel.mem ![t, u]) ↔
      Rl (f 1) (t.val b f) (u.val b f) := by
  show (Eval (M := M) b f (∃¹ (Semiformula.rel Language.Set.Rel.mem ![#0, &1] ⋏
      (Rew.embSubsts ![#0, Rew.bShift t, Rew.bShift u] ▹ isOpD.φ)))) ↔ _
  rw [eval_ex]
  refine exists_congr fun p => ?_
  rw [eval_and', eval_embSubsts]
  refine and_congr Iff.rfl ((isOpD.eval M _).trans ?_)
  show IsOp p (Semiterm.val (p :> b) f (Rew.bShift t)) (Semiterm.val (p :> b) f (Rew.bShift u)) ↔ _
  rw [Semiterm.val_bShift, Semiterm.val_bShift]

/-- **The meaning of the rewritten formula** is that of the formula in the structure. -/
theorem tr_eval (A R : M) (j : U → M) (hA : ∀ v, v ∈ A ↔ ∃ u, j u = v)
    (hj : Function.Injective j) (hR : ∀ u u' : U, u ∈ u' ↔ Rl R (j u) (j u')) (ε : ℕ → U) :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) (e : Fin n → U),
      Eval (M := M) (fun i ↦ j (e i)) (rho A R j ε) (tr φ) ↔ Eval (M := U) e ε φ := by
  have hcons : ∀ {n : ℕ} (u : U) (e : Fin n → U),
      (j u :> fun i ↦ j (e i)) = fun i ↦ j ((u :> e) i) := by
    intro n u e; funext i; cases i using Fin.cases <;> rfl
  have hrel : ∀ {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ℕ n) (e : Fin n → U),
      Eval (M := M) (fun i ↦ j (e i)) (rho A R j ε) (trRel r (fun i ↦ sh (v i))) ↔
        Eval (M := U) e ε (Semiformula.rel r v) := by
    intro n k r v e
    cases r with
    | eq =>
      show ((sh (v 0)).val (M := M) (fun i ↦ j (e i)) (rho A R j ε) =
        (sh (v 1)).val (M := M) (fun i ↦ j (e i)) (rho A R j ε)) ↔
        ((v 0).val (M := U) e ε = (v 1).val (M := U) e ε)
      rw [sh_val, sh_val]
      exact hj.eq_iff
    | mem =>
      have h1 : (fun i ↦ sh (v i)) = ![sh (v 0), sh (v 1)] := Matrix.fun_eq_vec_two _
      rw [h1, trRel_mem_eval, sh_val, sh_val]
      exact (hR _ _).symm
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro e; exact Iff.rfl
  | hfalsum => intro e; exact Iff.rfl
  | hrel r v => intro e; exact hrel r v e
  | hnrel r v =>
    intro e
    show Eval (M := M) (fun i ↦ j (e i)) (rho A R j ε) (∼trRel r (fun i ↦ sh (v i))) ↔
      Eval (M := U) e ε (∼Semiformula.rel r v)
    simp only [LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
    exact not_congr (hrel r v e)
  | hand φ ψ ih1 ih2 =>
    intro e
    show Eval (M := M) _ _ (tr φ ⋏ tr ψ) ↔ Eval (M := U) e ε (φ ⋏ ψ)
    rw [eval_and', eval_and', ih1 e, ih2 e]
  | hor φ ψ ih1 ih2 =>
    intro e
    show Eval (M := M) _ _ (tr φ ⋎ tr ψ) ↔ Eval (M := U) e ε (φ ⋎ ψ)
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
    rw [ih1 e, ih2 e]
  | hall φ ih =>
    intro e
    show Eval (M := M) _ _ (∀¹ (Semiformula.rel Language.Set.Rel.mem ![#0, &0] 🡒 tr φ)) ↔
      Eval (M := U) e ε (∀¹ φ)
    rw [eval_all, eval_all]
    constructor
    · intro H u
      have h1 := (eval_imp' _ _ _ _).mp (H (j u)) ((hA (j u)).mpr ⟨u, rfl⟩)
      rw [hcons] at h1
      exact (ih _).mp h1
    · intro H x
      refine (eval_imp' _ _ _ _).mpr fun hx => ?_
      obtain ⟨u, rfl⟩ := (hA x).mp hx
      rw [hcons]
      exact (ih _).mpr (H u)
  | hexs φ ih =>
    intro e
    show Eval (M := M) _ _ (∃¹ (Semiformula.rel Language.Set.Rel.mem ![#0, &0] ⋏ tr φ)) ↔
      Eval (M := U) e ε (∃¹ φ)
    rw [eval_ex, eval_ex]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨hxA, h1⟩ := (eval_and' _ _ _ _).mp hx
      obtain ⟨u, rfl⟩ := (hA x).mp hxA
      rw [hcons] at h1
      exact ⟨u, (ih _).mp h1⟩
    · rintro ⟨u, hu⟩
      refine ⟨j u, (eval_and' _ _ _ _).mpr ⟨(hA (j u)).mpr ⟨u, rfl⟩, ?_⟩⟩
      rw [hcons]
      exact (ih _).mpr hu

variable [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

/-- **Definable subsets of a set structure are sets.** `U` is a structure whose universe is,
through the one-to-one map `j`, the set `A` of the model, and whose membership relation is the
graph `R`. -/
theorem exists_definable_subset (j : U → M) (A R : M) (hA : ∀ v, v ∈ A ↔ ∃ u, j u = v)
    (hj : Function.Injective j) (hR : ∀ u u' : U, u ∈ u' ↔ Rl R (j u) (j u'))
    (ψ : SetTheorySemiproposition 1) (ε : ℕ → U) :
    ∃ S : M, ∀ v, v ∈ S ↔ ∃ u : U, j u = v ∧ Eval (M := U) ![u] ε ψ := by
  let χ : SetTheorySemiproposition 1 := Semiformula.rel Language.Set.Rel.mem ![#0, &0] ⋏ tr ψ
  have hχ : χ.IsStratified := ⟨σr, ![0], stratified_and.mpr
    ⟨stratified_rel.mpr ⟨0, fun i => by fin_cases i <;> rfl⟩,
      tr_strat ψ ![0] (fun i => by fin_cases i; rfl)⟩⟩
  have := by
    simpa [models_iff, Axiom.comprehensionSchema] using
      Theory.models M 𝗡𝗙 (NewFoundations.comprehension χ hχ)
  obtain ⟨S, hS⟩ := this (rho A R j ε)
  refine ⟨S, fun v => (hS v).trans ?_⟩
  rw [eval_and']
  have e1 : ∀ u : U, (![j u] : Fin 1 → M) = fun i ↦ j (![u] i) := by
    intro u; funext i; fin_cases i; rfl
  constructor
  · rintro ⟨hv, H⟩
    obtain ⟨u, rfl⟩ := (hA v).mp hv
    rw [e1] at H
    exact ⟨u, rfl, (tr_eval A R j hA hj hR ε ψ _).mp H⟩
  · rintro ⟨u, rfl, H⟩
    refine ⟨(hA (j u)).mpr ⟨u, rfl⟩, ?_⟩
    rw [e1]
    exact (tr_eval A R j hA hj hR ε ψ _).mpr H

end relativise

/-! ### The types in the domain form a model of `𝗠` -/

section base

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

/-- **The conditions of `IsMacBase` hold for the types in `Dom`**, with membership `EE`. -/
theorem isMacBase_of_embed {W : Type} [SetStructure W] (i : W → M) (hi : Function.Injective i)
    (hdom : ∀ x : M, Dom x ↔ ∃ w, i w = x) (hmem : ∀ a b : W, a ∈ b ↔ EE (i a) (i b)) :
    IsMacBase W := by
  obtain ⟨g, hg⟩ := exists_eg (V := M)
  have dom_iff : ∀ x : M, Dom x ↔ ∃ X, Stable g X ∧ Trans X ∧ x ∈ X := fun x =>
    ⟨fun ⟨g', X, hg', h⟩ => ⟨X, by rw [eg_unique hg hg']; exact h⟩, fun ⟨X, h⟩ => ⟨g, X, hg, h⟩⟩
  have hdomi : ∀ w, Dom (i w) := fun w => (hdom _).mpr ⟨w, rfl⟩
  have hZ : ∀ w, InZ (i w) := fun w =>
    let ⟨X, hX, _, hx⟩ := (dom_iff _).mp (hdomi w); hX.1 _ hx
  have hdown : ∀ w v, EE v (i w) → ∃ w', i w' = v := fun w v hv => by
    obtain ⟨X, hX, hXt, hx⟩ := (dom_iff _).mp (hdomi w)
    exact (hdom v).mp ((dom_iff v).mpr ⟨X, hX, hXt, hXt _ hx v hv⟩)
  have key : ∀ X S : M, Stable g X → Trans X → (∀ s, s ∈ S → s ∈ X) →
      ∃ w : W, ∀ v, EE v (i w) ↔ v ∈ S := by
    intro X S hX hXt hS
    obtain ⟨y, hyZ, hy⟩ := stable_full hg hX S hS
    obtain ⟨P, hP⟩ := exists_pow X
    have hyP : y ∈ P := (hP y).mpr ⟨hyZ, fun u hu => hS u ((hy u).mp hu)⟩
    obtain ⟨w, rfl⟩ := (hdom y).mp
      ((dom_iff y).mpr ⟨P, pow_stable hg hX hP, (pow_trans hX hXt hP).2, hyP⟩)
    exact ⟨w, hy⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- extensionality
    intro x y h
    refine hi (ee_ext (hZ x) (hZ y) fun v => ⟨fun hv => ?_, fun hv => ?_⟩)
    · obtain ⟨z, rfl⟩ := hdown x v hv
      exact (hmem z y).mp ((h z).mp ((hmem z x).mpr hv))
    · obtain ⟨z, rfl⟩ := hdown y v hv
      exact (hmem z x).mp ((h z).mpr ((hmem z y).mpr hv))
  · -- foundation
    rintro x ⟨y, hy⟩
    obtain ⟨S, hS⟩ := (eeD.comp (τ' := ![6, 6]) ![0, 1] 0).comprehension ![i x]
    have hS' : ∀ v, v ∈ S ↔ EE v (i x) := hS
    obtain ⟨v, hvS, -, hmin⟩ := ee_wf S ⟨i y, (hS' _).mpr ((hmem y x).mp hy), hZ y⟩
    obtain ⟨z, rfl⟩ := hdown x v ((hS' v).mp hvS)
    exact ⟨z, (hmem z x).mpr ((hS' _).mp hvS), fun z' hz' hz'z =>
      hmin (i z') ((hS' _).mpr ((hmem z' x).mp hz')) ((hmem z' z).mp hz'z)⟩
  · -- pairing
    intro x y
    obtain ⟨X, hX, hXt, hx⟩ := (dom_iff _).mp (hdomi x)
    obtain ⟨Y, hY, hYt, hy⟩ := (dom_iff _).mp (hdomi y)
    obtain ⟨Un, hU⟩ := exists_union X Y
    obtain ⟨S, hS⟩ := exists_up (i x) (i y)
    obtain ⟨p, hp⟩ := key Un S (union_stable hX hY hU) (union_trans hXt hYt hU) fun s hs => by
      rcases (hS s).mp hs with rfl | rfl
      · exact (hU _).mpr (Or.inl hx)
      · exact (hU _).mpr (Or.inr hy)
    exact ⟨p, (hmem x p).mpr ((hp _).mpr ((hS _).mpr (Or.inl rfl))),
      (hmem y p).mpr ((hp _).mpr ((hS _).mpr (Or.inr rfl)))⟩
  · -- power set
    intro x
    obtain ⟨X, hX, hXt, hx⟩ := (dom_iff _).mp (hdomi x)
    obtain ⟨P, hP⟩ := exists_pow X
    obtain ⟨p, hp⟩ := key P P (pow_stable hg hX hP) (pow_trans hX hXt hP).2 fun s hs => hs
    refine ⟨p, fun z hz => (hmem z p).mpr ((hp _).mpr ((hP _).mpr ⟨hZ z, fun u hu => ?_⟩))⟩
    obtain ⟨w', rfl⟩ := hdown z u hu
    exact hXt _ hx _ ((hmem w' x).mp (hz w' ((hmem w' z).mpr hu)))
  · -- transitive containment
    intro x
    obtain ⟨X, hX, hXt, hx⟩ := (dom_iff _).mp (hdomi x)
    obtain ⟨t, ht⟩ := key X X hX hXt fun s hs => hs
    refine ⟨t, fun z hz => (hmem z t).mpr ((ht _).mpr (hXt _ hx _ ((hmem z x).mp hz))),
      fun y hy z hz => ?_⟩
    exact (hmem z t).mpr ((ht _).mpr (hXt _ ((ht _).mp ((hmem y t).mp hy)) _ ((hmem z y).mp hz)))
  · -- infinity
    obtain ⟨Ω, hΩ, hΩs, hΩt⟩ := om_stable hg
    obtain ⟨I, hI⟩ := key Ω Ω hΩs hΩt fun s hs => hs
    have hΩdom : ∀ v, v ∈ Ω → ∃ w, i w = v := fun v hv =>
      (hdom v).mp ((dom_iff v).mpr ⟨Ω, hΩs, hΩt, hv⟩)
    refine ⟨I, ?_, fun x hx => ?_⟩
    · obtain ⟨z₀, hz₀⟩ := exists_zero (V := M)
      obtain ⟨e, rfl⟩ := hΩdom z₀ ((hΩ _).mpr (om_zero hz₀))
      exact ⟨e, (hmem e I).mpr ((hI _).mpr ((hΩ _).mpr (om_zero hz₀))),
        fun z hz => hz₀.2 _ ((hmem z e).mp hz)⟩
    · have hxΩ : InOm (i x) := (hΩ _).mp ((hI _).mp ((hmem x I).mp hx))
      obtain ⟨w', hw', hw'om⟩ := om_succ_exists hxΩ
      obtain ⟨x', rfl⟩ := hΩdom w' ((hΩ _).mpr hw'om)
      refine ⟨x', (hmem x' I).mpr ((hI _).mpr ((hΩ _).mpr hw'om)), fun z => ?_⟩
      rw [hmem z x', hw'.2.2 (i z), hmem z x]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (hi h)
      · rintro (rfl | h)
        · exact Or.inr rfl
        · exact Or.inl h
  · -- definable subsets
    intro t ψ ε
    obtain ⟨X, hX, hXt, ht⟩ := (dom_iff _).mp (hdomi t)
    obtain ⟨A, hA⟩ := (eeD.comp (τ' := ![6, 6]) ![0, 1] 0).comprehension ![i t]
    have hA' : ∀ v, v ∈ A ↔ EE v (i t) := hA
    let j : extSet t → M := fun u ↦ i u.1
    have hjA : ∀ v, v ∈ A ↔ ∃ u : extSet t, j u = v := fun v =>
      ⟨fun hv => by
        obtain ⟨z, rfl⟩ := hdown t v ((hA' v).mp hv)
        exact ⟨⟨z, (hmem z t).mpr ((hA' _).mp hv)⟩, rfl⟩,
      fun ⟨u, hu⟩ => hu ▸ (hA' _).mpr ((hmem u.1 t).mp u.2)⟩
    obtain ⟨S, hS⟩ := exists_definable_subset j A g hjA
      (fun u u' h => Subtype.ext (hi h))
      (fun u u' => (hmem u.1 u'.1).trans (rl_eg hg _ _).symm) ψ ε
    obtain ⟨y, hy⟩ := key X S hX hXt fun s hs => by
      obtain ⟨u, rfl, -⟩ := (hS s).mp hs
      exact hXt _ ht _ ((hmem u.1 t).mp u.2)
    refine ⟨y, fun z => (hmem z y).trans ((hy _).trans ((hS _).trans ⟨?_, ?_⟩))⟩
    · rintro ⟨u, hu, H⟩
      have e : u.1 = z := hi hu
      subst e
      exact ⟨u.2, H⟩
    · rintro ⟨hz, H⟩
      exact ⟨⟨z, hz⟩, rfl, H⟩

end base

end Hin

/-! ### The interpretation -/

/-- `IsMacBase.models` for a structure given with its relation symbols, not through its
membership relation. -/
theorem IsMacBase.models' {W : Type} [SetStructure W] [Nonempty W] [s : Tarski.Structure ℒₛₑₜ W]
    [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W] (h : IsMacBase W) :
    W↓[ℒₛₑₜ] ⊧* 𝗠 := by
  rcases standardStructure_unique W s
  exact h.models

open DirectTranslation

/-- The interpretation of the relation symbols: equality is itself, and membership is the
membership relation between types. -/
def macRel : {k : ℕ} → (ℒₛₑₜ).Rel k → Semiformula.Operator ℒₛₑₜ k
  | _, Language.Set.Rel.eq => Semiformula.Operator.Eq.eq
  | _, Language.Set.Rel.mem => ⟨Hin.eeD.φ⟩

section

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

omit [Nonempty M] hT in
lemma macDomain_val_iff (x : M) :
    (⟨Hin.domU.φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] ↔ Hin.Dom x :=
  Hin.domU.eval M ![x]

omit [Nonempty M] hT in
lemma macMem_val_iff (x y : M) :
    (⟨Hin.eeD.φ⟩ : Semiformula.Operator ℒₛₑₜ 2).val ![x, y] ↔ Hin.EE x y :=
  Hin.eeD.eval M ![x, y]

theorem exists_dom : ∃ x : M, Hin.Dom x := by
  obtain ⟨g, hg⟩ := Hin.exists_eg (V := M)
  obtain ⟨Ω, hΩ, hΩs, hΩt⟩ := Hin.om_stable hg
  obtain ⟨z, hz⟩ := Hin.exists_zero (V := M)
  exact ⟨z, g, Ω, hg, hΩs, hΩt, (hΩ z).mpr (Hin.om_zero hz)⟩

end

/-- **The translation of `ℒₛₑₜ` into `𝗡𝗙`**: the domain is `Hin.Dom`, membership is `Hin.EE`, and
equality is equality. -/
def macTranslation : DirectTranslation 𝗡𝗙 ℒₛₑₜ where
  domain := ⟨Hin.domU.φ⟩
  rel := macRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    obtain ⟨x, hx⟩ := exists_dom (M := M)
    suffices ∃ x : M, (⟨Hin.domU.φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] by
      simpa [models_iff] using this
    exact ⟨x, (macDomain_val_iff x).mpr hx⟩
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : macRel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

/-- The membership relation of the interpreted structure. -/
instance macModel_setStructure : SetStructure (macTranslation.Model M) :=
  ⟨fun y x ↦ Hin.EE (x : M) (y : M)⟩

omit [Nonempty M] hT in
lemma macModel_mem_iff (a b : macTranslation.Model M) : a ∈ b ↔ Hin.EE (a : M) (b : M) := Iff.rfl

instance macModel_mem : Tarski.Structure.Mem ℒₛₑₜ (macTranslation.Model M) where
  mem a b := by
    have h1 : (Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).val ![a, b] ↔
        Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b] := by
      simp [Semiformula.Operator.val, Semiformula.Operator.Mem.sentence_eq, eval_rel,
        Matrix.fun_eq_vec_two]
    rw [h1, Model.rel_iff]
    have h2 : (fun i ↦ ((![a, b] i : macTranslation.Model M) : M)) = ![(a : M), (b : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2]
    exact macMem_val_iff _ _

/-- **In a model of `𝗡𝗙`, the interpreted structure is a model of `𝗠`.** -/
theorem macModel_models : (macTranslation.Model M)↓[ℒₛₑₜ] ⊧* 𝗠 :=
  IsMacBase.models' (Hin.isMacBase_of_embed (fun a : macTranslation.Model M ↦ (a : M))
    (fun a b h => by cases a; cases b; cases h; rfl)
    (fun x => ⟨fun hx => ⟨⟨x, (macDomain_val_iff x).mpr hx⟩, rfl⟩,
      fun ⟨w, hw⟩ => hw ▸ (macDomain_val_iff _).mp w.dom⟩)
    macModel_mem_iff)

end model

/-- **`𝗡𝗙` interprets `𝗠`**, Mac Lane set theory with transitive containment and without choice. -/
instance interpretsM : 𝗡𝗙 ⊳ 𝗠 where
  trln := macTranslation
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp macModel_models φ hφ)

/-- **NFU + Infinity interprets `𝗠`**, by composition with `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`. -/
instance nfuInterpretsM : 𝗡𝗙𝗨𝗜 ⊳ 𝗠 := DirectInterpretation.comp interpretsM nfuInterpretsNF

/-- **The syntactic transformation.** The translation of a theorem of `𝗠` is a theorem of
`𝗡𝗙`. -/
theorem nf_provable_translate_of_m {σ : Sentence ℒₛₑₜ} (h : 𝗠 ⊢ σ) : 𝗡𝗙 ⊢ interpretsM σ :=
  DirectInterpretation.sound interpretsM h

/-- If `𝗡𝗙` is consistent then so is `𝗠`. -/
theorem consistent_m_of_consistent_nf (h : Entailment.Consistent 𝗡𝗙) : Entailment.Consistent 𝗠 := by
  by_contra hM
  have hbot : 𝗠 ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hM ⊥
  have := nf_provable_translate_of_m hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.interpretsM
#print axioms FFL.FirstOrder.SetTheory.nfuInterpretsM
