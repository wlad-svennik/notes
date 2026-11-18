import NFTheories
import NFUJensenModel

set_option autoImplicit false

/-!
# NFU + Infinity is consistent: Jensen's proof

`JensenNFU.exists_model` gives a structure with extensionality for objects with members,
comprehension for stratified formulas with typed quantifiers, and a universe that is not finite.
Here every stratified formula of `ℒₛₑₜ` is shown to have the meaning of such a formula, so the
structure is a model of the theory `𝗡𝗙𝗨𝗜`, and `𝗡𝗙𝗨𝗜` is consistent.

This file and the files it imports use Mathlib, the library Foundation, `NFTheories.lean` and
`ConNF.NF.Generic` (pure Mathlib). They use neither NF nor the model of tangled type theory.
-/

namespace FFL.FirstOrder

open JensenNFU (TFm IsNFU UnivInfinite)

section lists

variable {α : Type*}

lemma List.ofFn_vecCons_j {n : ℕ} (a : α) (e : Fin n → α) :
    List.ofFn (a :> e) = a :: List.ofFn e := by
  simp [List.ofFn_succ]

lemma List.getElem?_ofFn_append_left_j {n : ℕ} (e : Fin n → α) (l : List α) (x : Fin n) :
    getElem? (List.ofFn e ++ l) (x : ℕ) = some (e x) := by
  rw [List.getElem?_append_left (by simp)]
  simp

lemma List.getElem?_ofFn_append_right_j {n : ℕ} (e : Fin n → α) (g : ℕ → α) {K x : ℕ}
    (hx : x < K) : getElem? (List.ofFn e ++ (List.range K).map g) (n + x) = some (g x) := by
  rw [List.getElem?_append_right (by simp)]
  simp [hx]

end lists

section idx

variable {L : Language} [L.Relational]

/-- The position of a variable in the list of the bound variables followed by the free
variables. -/
def Semiterm.jidx {n : ℕ} : Semiterm L ℕ n → ℕ
  | #x => x
  | &x => n + x
  | .func f _ => isEmptyElim f

lemma Semiterm.getElem?_jidx_val {N : Type*} [Tarski.Structure L N] {n : ℕ} (t : Semiterm L ℕ n)
    (e : Fin n → N) (f : ℕ → N) {K : ℕ} (h : ∀ x ∈ t.freeVariables, x < K) :
    getElem? (List.ofFn e ++ (List.range K).map f) t.jidx = some (t.val e f) := by
  match t with
  | #x => exact List.getElem?_ofFn_append_left_j e _ x
  | &x => exact List.getElem?_ofFn_append_right_j e f (h x (by simp))
  | .func f _ => exact isEmptyElim f

lemma Semiterm.getElem?_jidx_lv {n : ℕ} (t : Semiterm L ℕ n)
    (σ : ℕ → ℕ) (τ : Fin n → ℕ) {K : ℕ} (h : ∀ x ∈ t.freeVariables, x < K) :
    getElem? (List.ofFn τ ++ (List.range K).map σ) t.jidx = some (t.lv σ τ) := by
  match t with
  | #x => exact List.getElem?_ofFn_append_left_j τ _ x
  | &x => exact List.getElem?_ofFn_append_right_j τ σ (h x (by simp))
  | .func f _ => exact isEmptyElim f

end idx

namespace SetTheory

namespace Jensen

variable {N : Type} [s : Tarski.Structure ℒₛₑₜ N] [Tarski.Structure.Eq ℒₛₑₜ N]

/-- Every stratified formula of `ℒₛₑₜ` has the same meaning as a stratified formula with typed
quantifiers. -/
theorem exists_tfm (σ : ℕ → ℕ) (K : ℕ) (f : ℕ → N) {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) :
    ∀ τ : Fin n → ℕ, (∀ x ∈ φ.freeVariables, x < K) → φ.Stratified σ τ →
      ∃ ψ : TFm, TFm.Strat (List.ofFn τ ++ (List.range K).map σ) ψ ∧
        ∀ e : Fin n → N,
          TFm.Sat (fun a b ↦ s.rel Language.Mem.mem ![a, b]) ψ
            (List.ofFn e ++ (List.range K).map f) ↔ Semiformula.Eval e f φ := by
  have hatom : ∀ {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ℕ n) (τ : Fin n → ℕ),
      (∀ x ∈ (Semiformula.rel r v).freeVariables, x < K) →
      (∃ t, ∀ i, (v i).lv σ τ = t + Language.Stratification.lv r i) →
      ∃ ψ : TFm, TFm.Strat (List.ofFn τ ++ (List.range K).map σ) ψ ∧
        ∀ e : Fin n → N,
          TFm.Sat (fun a b ↦ s.rel Language.Mem.mem ![a, b]) ψ
            (List.ofFn e ++ (List.range K).map f) ↔ s.rel r (fun i ↦ (v i).val e f) := by
    intro n k r v τ hfv hst
    have hv : ∀ i, ∀ x ∈ (v i).freeVariables, x < K := fun i x hx =>
      hfv x (by rw [Semiformula.freeVariables_rel]; exact Finset.mem_biUnion.mpr ⟨i, by simp, hx⟩)
    obtain ⟨t, ht⟩ := hst
    cases r with
    | eq =>
      refine ⟨TFm.eq (v 0).jidx (v 1).jidx, ⟨t, ?_, ?_⟩, fun e => ?_⟩
      · rw [(v 0).getElem?_jidx_lv σ τ (hv 0), ht 0]; rfl
      · rw [(v 1).getElem?_jidx_lv σ τ (hv 1), ht 1]; rfl
      · simp only [TFm.Sat, (v 0).getElem?_jidx_val e f (hv 0),
          (v 1).getElem?_jidx_val e f (hv 1)]
        have : s.rel (Language.Set.Rel.eq) (fun i ↦ (v i).val e f) ↔
            (v 0).val e f = (v 1).val e f :=
          Tarski.Structure.eq_lang (L := ℒₛₑₜ) (v := fun i ↦ (v i).val e f)
        rw [this]
        constructor
        · rintro ⟨a, b, ha, hb, hab⟩
          rw [Option.some.inj ha, Option.some.inj hb]; exact hab
        · intro h; exact ⟨_, _, rfl, rfl, h⟩
    | mem =>
      refine ⟨TFm.mem (v 0).jidx (v 1).jidx, ⟨t, ?_, ?_⟩, fun e => ?_⟩
      · rw [(v 0).getElem?_jidx_lv σ τ (hv 0), ht 0]; rfl
      · rw [(v 1).getElem?_jidx_lv σ τ (hv 1), ht 1]; rfl
      · simp only [TFm.Sat, (v 0).getElem?_jidx_val e f (hv 0),
          (v 1).getElem?_jidx_val e f (hv 1)]
        have : (fun i ↦ (v i).val e f) = ![(v 0).val e f, (v 1).val e f] :=
          Matrix.fun_eq_vec_two _
        rw [this]
        constructor
        · rintro ⟨a, b, ha, hb, hab⟩
          rw [Option.some.inj ha, Option.some.inj hb]; exact hab
        · intro h; exact ⟨_, _, rfl, rfl, h⟩
  induction φ using Semiformula.rec' with
  | hverum =>
    intro τ _ _
    refine ⟨TFm.all 0 (TFm.eq 0 0), ⟨0, rfl, rfl⟩, fun e => ?_⟩
    simp [TFm.Sat]
  | hfalsum =>
    intro τ _ _
    refine ⟨TFm.neg (TFm.all 0 (TFm.eq 0 0)), ⟨0, rfl, rfl⟩, fun e => ?_⟩
    simp [TFm.Sat]
  | hrel r v =>
    intro τ hfv hst
    obtain ⟨ψ, h1, h2⟩ := hatom r v τ hfv (Semiformula.stratified_rel.mp hst)
    exact ⟨ψ, h1, fun e => (h2 e).trans Semiformula.eval_rel'.symm⟩
  | hnrel r v =>
    intro τ hfv hst
    obtain ⟨ψ, h1, h2⟩ := hatom r v τ (by simpa [Semiformula.freeVariables_rel,
      Semiformula.freeVariables_nrel] using hfv) (Semiformula.stratified_nrel.mp hst)
    refine ⟨TFm.neg ψ, h1, fun e => ?_⟩
    simp only [TFm.Sat, h2 e]
    exact Semiformula.eval_nrel'.symm
  | hand φ ψ ihφ ihψ =>
    intro τ hfv hst
    obtain ⟨hs1, hs2⟩ := Semiformula.stratified_and.mp hst
    obtain ⟨φ', h1, h2⟩ := ihφ τ (fun x hx => hfv x (by simp [hx])) hs1
    obtain ⟨ψ', h3, h4⟩ := ihψ τ (fun x hx => hfv x (by simp [hx])) hs2
    refine ⟨TFm.and φ' ψ', ⟨h1, h3⟩, fun e => ?_⟩
    simp [TFm.Sat, h2 e, h4 e]
  | hor φ ψ ihφ ihψ =>
    intro τ hfv hst
    obtain ⟨hs1, hs2⟩ := Semiformula.stratified_or.mp hst
    obtain ⟨φ', h1, h2⟩ := ihφ τ (fun x hx => hfv x (by simp [hx])) hs1
    obtain ⟨ψ', h3, h4⟩ := ihψ τ (fun x hx => hfv x (by simp [hx])) hs2
    refine ⟨TFm.neg (TFm.and (TFm.neg φ') (TFm.neg ψ')), ⟨h1, h3⟩, fun e => ?_⟩
    simp only [TFm.Sat, h2 e, h4 e]
    simp
    tauto
  | hall φ ih =>
    intro τ hfv hst
    obtain ⟨t, ht⟩ := Semiformula.stratified_all.mp hst
    obtain ⟨φ', h1, h2⟩ := ih (t :> τ) (fun x hx => hfv x (by simpa using hx)) ht
    rw [List.ofFn_vecCons_j, List.cons_append] at h1
    refine ⟨TFm.all t φ', h1, fun e => ?_⟩
    simp only [TFm.Sat, Semiformula.eval_all]
    refine forall_congr' fun a => ?_
    rw [← h2 (a :> e), List.ofFn_vecCons_j, List.cons_append]
  | hexs φ ih =>
    intro τ hfv hst
    obtain ⟨t, ht⟩ := Semiformula.stratified_exs.mp hst
    obtain ⟨φ', h1, h2⟩ := ih (t :> τ) (fun x hx => hfv x (by simpa using hx)) ht
    rw [List.ofFn_vecCons_j, List.cons_append] at h1
    refine ⟨TFm.neg (TFm.all t (TFm.neg φ')), h1, fun e => ?_⟩
    simp only [TFm.Sat, Semiformula.eval_ex]
    rw [not_forall]
    refine exists_congr fun a => ?_
    rw [not_not, ← h2 (a :> e), List.ofFn_vecCons_j, List.cons_append]


/-- **A structure with NFU and a universe that is not finite is a model of `𝗡𝗙𝗨𝗜`.** -/
theorem models_nfui_of_isNFU {N : Type} [Nonempty N] [SetStructure N]
    (h : IsNFU N (fun a b : N ↦ a ∈ b)) (hinf : UnivInfinite (fun a b : N ↦ a ∈ b)) :
    N↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 := by
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | hφ
  · cases hφ with
    | equality φ hφ =>
      have : N↓[ℒₛₑₜ] ⊧* 𝗘𝗤 ℒₛₑₜ := inferInstance
      exact models_theory_iff.mp this φ hφ
    | extensionality =>
      have := h.ext
      simpa [models_iff] using fun x y => this x y
    | comprehension φ hφ =>
      obtain ⟨σ, τ, hst⟩ := hφ
      simp only [models_iff, Axiom.comprehensionSchema, Semiformula.eval_univCl]
      intro f
      obtain ⟨ψ, h1, h2⟩ := exists_tfm (N := N) σ φ.fvSup f φ τ
        (fun x hx => Semiformula.lt_fvSup_of_fvar? hx) hst
      have hτ : List.ofFn τ = [τ 0] := by simp [List.ofFn_succ]
      rw [hτ] at h1
      obtain ⟨y, hy⟩ := h.comprehension (τ 0) ((List.range φ.fvSup).map σ) ψ h1
        ((List.range φ.fvSup).map f) (by simp)
      have key : ∀ x : N, x ∈ y ↔ Semiformula.Eval ![x] f φ := by
        intro x
        have := h2 ![x]
        have he : List.ofFn ![x] = [x] := by simp [List.ofFn_succ]
        rw [he] at this
        exact (hy x).trans this
      simpa [Matrix.constant_eq_singleton] using ⟨y, key⟩
  · have e : φ = Axiom.universeInfinite := hφ
    rw [e]
    simpa [models_iff, Axiom.universeInfinite, UnivInfinite] using hinf

/-- **NFU + Infinity is consistent.** The model is `JensenNFU.exists_model`. -/
theorem consistent_nfuInfinity : Entailment.Consistent 𝗡𝗙𝗨𝗜 := by
  obtain ⟨V, mem, h, hinf⟩ := JensenNFU.exists_model
  have hne : Nonempty V := by
    obtain ⟨y, -⟩ := h.comprehension 0 [] (TFm.eq 0 0) ⟨0, rfl, rfl⟩ [] rfl
    exact ⟨y⟩
  let _ : SetStructure V := ⟨fun y x ↦ mem x y⟩
  have hV : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 := models_nfui_of_isNFU h hinf
  exact consistent_of_model 𝗡𝗙𝗨𝗜 V

end Jensen

end SetTheory

end FFL.FirstOrder
