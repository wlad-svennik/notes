import NFTheories
import NFUInterpretsNFEq
import NFChoiceForms
import Foundation.FirstOrder.SetTheory.Z.Basic

set_option autoImplicit false

/-!
# `𝗡𝗙` and `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ` interpret each other: the statement about derivations

The theories are those of `NFTheories.lean`; `𝗡𝗙𝗨ₛ`, `𝗜𝗡𝗙ₛ`, `𝗡𝗙𝗨𝗜ₛ` are NFU, Infinity and their
union in the language `ℒₛₑₜᵤ` with a predicate for sethood. (The same for Jensen's NFU, in the
language of membership and equality, is in `NFUJensen.lean`.) The interpretations are instances
of the class `DirectInterpretation` of the library (`T ⊳ U`), so `DirectInterpretation.sound`
gives the transformation of derivations. Every derivation in this file is obtained from the
completeness theorem of the library (`Theory.Proof.complete_on_eq_models`, `SetTheory.complete`)
and a theorem about models.

## Main results

* `SetTheoryU.interpretsNF : 𝗡𝗙𝗨𝗜ₛ ⊳ 𝗡𝗙`
* `SetTheory.interpretsNFUI : 𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜ₛ`
* `SetTheoryU.mutualInterpretation : 𝗡𝗙𝗨𝗜ₛ ⋈ 𝗡𝗙`
* `SetTheoryU.provable_translate_of_nf : 𝗡𝗙 ⊢ σ → 𝗡𝗙𝗨𝗜ₛ ⊢ interpretsNF σ`
* `SetTheoryU.provable_translate_of_nfui : 𝗡𝗙𝗨𝗜ₛ ⊢ σ → 𝗡𝗙 ⊢ interpretsNFUI σ`
* `SetTheory.provable_unset_of_nfui : 𝗡𝗙𝗨𝗜ₛ ⊢ σ → 𝗡𝗙 ⊢ σ.unset`
* `SetTheoryU.consistent_nfui_iff_consistent_nf`
* `SetTheory.nf_provable_universeInfinite : 𝗡𝗙 ⊢ Axiom.universeInfinite`
* `SetTheory.nf_provable_not_choice : 𝗡𝗙 ⊢ ∼Axiom.choice`
* `SetTheory.nf_provable_not_zorn : 𝗡𝗙 ⊢ ∼Axiom.zorn`

No model of NF is used here. Consistency is in `NFConsistentViaNFU.lean` and
`NFConsistentViaConNF.lean`.
-/

/-!
## From the formulas of the library to de Bruijn formulas with typed quantifiers

A structure for `ℒₛₑₜ` that satisfies stratified comprehension for the formulas `ConNF.NF.Fm`
(that is, `ConNF.NF.IsNF`) is a model of the theory `𝗡𝗙`.
-/

namespace FFL.FirstOrder

/-- The membership relation of a structure for a language with a membership symbol. -/
@[reducible] def Tarski.Structure.membership (L : Language) [L.Mem] (N : Type*)
    [s : Tarski.Structure L N] : Membership N N :=
  ⟨fun y x ↦ s.rel Language.Mem.mem ![x, y]⟩

lemma Tarski.Structure.membership_mem (L : Language) [L.Mem] (N : Type*)
    [s : Tarski.Structure L N] :
    letI := Tarski.Structure.membership L N
    Tarski.Structure.Mem L N :=
  letI := Tarski.Structure.membership L N
  ⟨fun a b ↦ by
    simp only [Semiformula.Operator.val, Semiformula.Operator.Mem.sentence_eq,
      Semiformula.eval_rel]
    have : (Semiterm.val (L := L) ![a, b] Empty.elim ∘ Semiterm.bvar : Fin 2 → N) = ![a, b] := by
      funext i; simp
    rw [this]; rfl⟩

section lists

variable {α : Type*}

lemma List.ofFn_vecCons {n : ℕ} (a : α) (e : Fin n → α) :
    List.ofFn (a :> e) = a :: List.ofFn e := by
  simp [List.ofFn_succ]

lemma List.getElem?_ofFn_append_left {n : ℕ} (e : Fin n → α) (l : List α) (x : Fin n) :
    getElem? (List.ofFn e ++ l) (x : ℕ) = some (e x) := by
  rw [List.getElem?_append_left (by simp)]
  simp

lemma List.getElem?_ofFn_append_right {n : ℕ} (e : Fin n → α) (g : ℕ → α) {K x : ℕ}
    (hx : x < K) : getElem? (List.ofFn e ++ (List.range K).map g) (n + x) = some (g x) := by
  rw [List.getElem?_append_right (by simp)]
  simp [hx]

end lists

section idx

variable {L : Language} [L.Relational]

/-- The position of a variable in the list of the bound variables followed by the free
variables. -/
def Semiterm.idx {n : ℕ} : Semiterm L ℕ n → ℕ
  | #x => x
  | &x => n + x
  | .func f _ => isEmptyElim f

lemma Semiterm.getElem?_idx_val {N : Type*} [Tarski.Structure L N] {n : ℕ} (t : Semiterm L ℕ n)
    (e : Fin n → N) (f : ℕ → N) {K : ℕ} (h : ∀ x ∈ t.freeVariables, x < K) :
    getElem? (List.ofFn e ++ (List.range K).map f) t.idx = some (t.val e f) := by
  match t with
  | #x => exact List.getElem?_ofFn_append_left e _ x
  | &x => exact List.getElem?_ofFn_append_right e f (h x (by simp))
  | .func f _ => exact isEmptyElim f

lemma Semiterm.getElem?_idx_lv {n : ℕ} (t : Semiterm L ℕ n)
    (σ : ℕ → ℕ) (τ : Fin n → ℕ) {K : ℕ} (h : ∀ x ∈ t.freeVariables, x < K) :
    getElem? (List.ofFn τ ++ (List.range K).map σ) t.idx = some (t.lv σ τ) := by
  match t with
  | #x => exact List.getElem?_ofFn_append_left τ _ x
  | &x => exact List.getElem?_ofFn_append_right τ σ (h x (by simp))
  | .func f _ => exact isEmptyElim f

end idx

namespace SetTheory

open ConNF.NF (Fm Strat IsNF)

variable {N : Type} [s : Tarski.Structure ℒₛₑₜ N] [Tarski.Structure.Eq ℒₛₑₜ N]

/-- Every stratified formula of `ℒₛₑₜ` has the same meaning as a stratified formula in the
sense of `ConNF.NF`. -/
theorem exists_fm (σ : ℕ → ℕ) (K : ℕ) (f : ℕ → N) {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) :
    ∀ τ : Fin n → ℕ, (∀ x ∈ φ.freeVariables, x < K) → φ.Stratified σ τ →
      ∃ ψ : Fm, Strat (List.ofFn τ ++ (List.range K).map σ) ψ ∧
        ∀ e : Fin n → N,
          ConNF.NF.Sat (fun a b ↦ s.rel Language.Mem.mem ![a, b]) ψ
            (List.ofFn e ++ (List.range K).map f) ↔ Semiformula.Eval e f φ := by
  have hatom : ∀ {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ℕ n) (τ : Fin n → ℕ),
      (∀ x ∈ (Semiformula.rel r v).freeVariables, x < K) →
      (∃ t, ∀ i, (v i).lv σ τ = t + Language.Stratification.lv r i) →
      ∃ ψ : Fm, Strat (List.ofFn τ ++ (List.range K).map σ) ψ ∧
        ∀ e : Fin n → N,
          ConNF.NF.Sat (fun a b ↦ s.rel Language.Mem.mem ![a, b]) ψ
            (List.ofFn e ++ (List.range K).map f) ↔ s.rel r (fun i ↦ (v i).val e f) := by
    intro n k r v τ hfv hst
    have hv : ∀ i, ∀ x ∈ (v i).freeVariables, x < K := fun i x hx =>
      hfv x (by rw [Semiformula.freeVariables_rel]; exact Finset.mem_biUnion.mpr ⟨i, by simp, hx⟩)
    obtain ⟨t, ht⟩ := hst
    cases r with
    | eq =>
      refine ⟨Fm.eq (v 0).idx (v 1).idx, ⟨t, ?_, ?_⟩, fun e => ?_⟩
      · rw [(v 0).getElem?_idx_lv σ τ (hv 0), ht 0]; rfl
      · rw [(v 1).getElem?_idx_lv σ τ (hv 1), ht 1]; rfl
      · simp only [ConNF.NF.Sat, (v 0).getElem?_idx_val e f (hv 0),
          (v 1).getElem?_idx_val e f (hv 1)]
        have : s.rel (Language.Set.Rel.eq) (fun i ↦ (v i).val e f) ↔
            (v 0).val e f = (v 1).val e f :=
          Tarski.Structure.eq_lang (L := ℒₛₑₜ) (v := fun i ↦ (v i).val e f)
        rw [this]
        constructor
        · rintro ⟨a, b, ha, hb, hab⟩
          rw [Option.some.inj ha, Option.some.inj hb]; exact hab
        · intro h; exact ⟨_, _, rfl, rfl, h⟩
    | mem =>
      refine ⟨Fm.mem (v 0).idx (v 1).idx, ⟨t, ?_, ?_⟩, fun e => ?_⟩
      · rw [(v 0).getElem?_idx_lv σ τ (hv 0), ht 0]; rfl
      · rw [(v 1).getElem?_idx_lv σ τ (hv 1), ht 1]; rfl
      · simp only [ConNF.NF.Sat, (v 0).getElem?_idx_val e f (hv 0),
          (v 1).getElem?_idx_val e f (hv 1)]
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
    refine ⟨Fm.all 0 (Fm.eq 0 0), ⟨0, rfl, rfl⟩, fun e => ?_⟩
    simp [ConNF.NF.Sat]
  | hfalsum =>
    intro τ _ _
    refine ⟨Fm.neg (Fm.all 0 (Fm.eq 0 0)), ⟨0, rfl, rfl⟩, fun e => ?_⟩
    simp [ConNF.NF.Sat]
  | hrel r v =>
    intro τ hfv hst
    obtain ⟨ψ, h1, h2⟩ := hatom r v τ hfv (Semiformula.stratified_rel.mp hst)
    exact ⟨ψ, h1, fun e => (h2 e).trans Semiformula.eval_rel'.symm⟩
  | hnrel r v =>
    intro τ hfv hst
    obtain ⟨ψ, h1, h2⟩ := hatom r v τ (by simpa [Semiformula.freeVariables_rel,
      Semiformula.freeVariables_nrel] using hfv) (Semiformula.stratified_nrel.mp hst)
    refine ⟨Fm.neg ψ, h1, fun e => ?_⟩
    simp only [ConNF.NF.Sat, h2 e]
    exact Semiformula.eval_nrel'.symm
  | hand φ ψ ihφ ihψ =>
    intro τ hfv hst
    obtain ⟨hs1, hs2⟩ := Semiformula.stratified_and.mp hst
    obtain ⟨φ', h1, h2⟩ := ihφ τ (fun x hx => hfv x (by simp [hx])) hs1
    obtain ⟨ψ', h3, h4⟩ := ihψ τ (fun x hx => hfv x (by simp [hx])) hs2
    refine ⟨Fm.and φ' ψ', ⟨h1, h3⟩, fun e => ?_⟩
    simp [ConNF.NF.Sat, h2 e, h4 e]
  | hor φ ψ ihφ ihψ =>
    intro τ hfv hst
    obtain ⟨hs1, hs2⟩ := Semiformula.stratified_or.mp hst
    obtain ⟨φ', h1, h2⟩ := ihφ τ (fun x hx => hfv x (by simp [hx])) hs1
    obtain ⟨ψ', h3, h4⟩ := ihψ τ (fun x hx => hfv x (by simp [hx])) hs2
    refine ⟨Fm.neg (Fm.and (Fm.neg φ') (Fm.neg ψ')), ⟨h1, h3⟩, fun e => ?_⟩
    simp only [ConNF.NF.Sat, h2 e, h4 e]
    simp
    tauto
  | hall φ ih =>
    intro τ hfv hst
    obtain ⟨t, ht⟩ := Semiformula.stratified_all.mp hst
    obtain ⟨φ', h1, h2⟩ := ih (t :> τ) (fun x hx => hfv x (by simpa using hx)) ht
    rw [List.ofFn_vecCons, List.cons_append] at h1
    refine ⟨Fm.all t φ', h1, fun e => ?_⟩
    simp only [ConNF.NF.Sat, Semiformula.eval_all]
    refine forall_congr' fun a => ?_
    rw [← h2 (a :> e), List.ofFn_vecCons, List.cons_append]
  | hexs φ ih =>
    intro τ hfv hst
    obtain ⟨t, ht⟩ := Semiformula.stratified_exs.mp hst
    obtain ⟨φ', h1, h2⟩ := ih (t :> τ) (fun x hx => hfv x (by simpa using hx)) ht
    rw [List.ofFn_vecCons, List.cons_append] at h1
    refine ⟨Fm.neg (Fm.all t (Fm.neg φ')), h1, fun e => ?_⟩
    simp only [ConNF.NF.Sat, Semiformula.eval_ex]
    rw [not_forall]
    refine exists_congr fun a => ?_
    rw [not_not, ← h2 (a :> e), List.ofFn_vecCons, List.cons_append]

/-- **A structure that satisfies extensionality and stratified comprehension for the formulas
`ConNF.NF.Fm` is a model of `𝗡𝗙`.** -/
theorem models_nf_of_isNF [Nonempty N]
    (h : IsNF N (fun a b ↦ s.rel Language.Mem.mem ![a, b])) : N↓[ℒₛₑₜ] ⊧* 𝗡𝗙 := by
  let _ := Tarski.Structure.membership ℒₛₑₜ N
  have := Tarski.Structure.membership_mem ℒₛₑₜ N
  refine models_theory_iff.mpr fun φ hφ => ?_
  cases hφ with
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
    obtain ⟨ψ, h1, h2⟩ := exists_fm (N := N) σ φ.fvSup f φ τ
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

end SetTheory

end FFL.FirstOrder

/-!
## Models of `𝗡𝗙𝗨ₛ` are models of NFU in the sense of `NFUCut.Model`

The formulas with named variables (`NFUCut.Fml`) are translated to formulas of `ℒₛₑₜᵤ`. The
translation preserves stratification and meaning, so a structure that satisfies `𝗡𝗙𝗨ₛ` gives a
`NFUCut.Model`, and the axiom of infinity `𝗜𝗡𝗙ₛ` holds in the structure exactly when the
`NFUCut.Model` satisfies `Infinity`.
-/

namespace FFL.FirstOrder.SetTheoryU

open NFUCut (Fml)

section translation

variable {ξ : Type*}

/-- Translation of a formula with named variables, where `c` says which term each name stands
for. -/
def ofFml : {n : ℕ} → (ℕ → Semiterm ℒₛₑₜᵤ ξ n) → Fml → Semiformula ℒₛₑₜᵤ ξ n
  | _, c, .mem x y => Semiformula.rel Language.SetU.Rel.mem ![c x, c y]
  | _, c, .eq x y => Semiformula.rel Language.SetU.Rel.eq ![c x, c y]
  | _, c, .set x => Semiformula.rel Language.SetU.Rel.set ![c x]
  | _, c, .neg φ => ∼ofFml c φ
  | _, c, .and φ ψ => ofFml c φ ⋏ ofFml c ψ
  | _, c, .all x φ => ∀¹ ofFml (Function.update (fun i ↦ Rew.bShift (c i)) x #0) φ

/-- The translation of a stratified formula is stratified. -/
lemma stratified_ofFml {σ : ℕ → ℕ} (φ : Fml) (h : φ.strat σ = true) :
    ∀ {n : ℕ} (c : ℕ → Semiterm ℒₛₑₜᵤ ξ n) (σ' : ξ → ℕ) (τ : Fin n → ℕ),
      (∀ i, (c i).lv σ' τ = σ i) → (ofFml c φ).Stratified σ' τ := by
  induction φ with
  | mem x y =>
    intro n c σ' τ hc
    have h' : σ y = σ x + 1 := by simpa [Fml.strat] using h
    refine Semiformula.stratified_rel.mpr ⟨σ x, fun i => ?_⟩
    fin_cases i
    · show (c x).lv σ' τ = σ x + 0
      rw [hc]; rfl
    · show (c y).lv σ' τ = σ x + 1
      rw [hc, h']
  | eq x y =>
    intro n c σ' τ hc
    have h' : σ x = σ y := by simpa [Fml.strat] using h
    refine Semiformula.stratified_rel.mpr ⟨σ x, fun i => ?_⟩
    fin_cases i
    · show (c x).lv σ' τ = σ x + 0
      rw [hc]; rfl
    · show (c y).lv σ' τ = σ x + 0
      rw [hc, h']; rfl
  | set x =>
    intro n c σ' τ hc
    refine Semiformula.stratified_rel.mpr ⟨σ x, fun i => ?_⟩
    fin_cases i
    show (c x).lv σ' τ = σ x + 0
    rw [hc]; rfl
  | neg φ ih =>
    intro n c σ' τ hc
    exact Semiformula.stratified_neg.mpr (ih (by simpa [Fml.strat] using h) c σ' τ hc)
  | and φ ψ ih1 ih2 =>
    intro n c σ' τ hc
    have h' : φ.strat σ = true ∧ ψ.strat σ = true := by simpa [Fml.strat] using h
    exact Semiformula.stratified_and.mpr ⟨ih1 h'.1 c σ' τ hc, ih2 h'.2 c σ' τ hc⟩
  | all x φ ih =>
    intro n c σ' τ hc
    refine Semiformula.stratified_all.mpr ⟨σ x, ih (by simpa [Fml.strat] using h) _ σ' _ ?_⟩
    intro i
    by_cases hi : i = x
    · subst hi; simp
    · simp [Function.update_of_ne hi, hc]

variable {M : Type} [s : Tarski.Structure ℒₛₑₜᵤ M] [Tarski.Structure.Eq ℒₛₑₜᵤ M]

/-- The translation has the same meaning. -/
lemma eval_ofFml (φ : Fml) :
    ∀ {n : ℕ} (c : ℕ → Semiterm ℒₛₑₜᵤ ξ n) (e : Fin n → M) (f : ξ → M),
      Semiformula.Eval e f (ofFml c φ) ↔
        NFUCut.Sat (fun a b ↦ s.rel Language.SetU.Rel.mem ![a, b])
          (fun a ↦ s.rel Language.SetU.Rel.set ![a]) φ (fun i ↦ (c i).val e f) := by
  induction φ with
  | mem x y =>
    intro n c e f
    simp only [ofFml, Semiformula.eval_rel, NFUCut.Sat]
    have : (Semiterm.val e f ∘ ![c x, c y]) = ![(c x).val e f, (c y).val e f] := by
      funext i; fin_cases i <;> rfl
    rw [this]
  | eq x y =>
    intro n c e f
    simp only [ofFml, Semiformula.eval_rel, NFUCut.Sat]
    exact Tarski.Structure.eq_lang (L := ℒₛₑₜᵤ) (v := Semiterm.val e f ∘ ![c x, c y])
  | set x =>
    intro n c e f
    simp only [ofFml, Semiformula.eval_rel, NFUCut.Sat]
    have : (Semiterm.val e f ∘ ![c x]) = ![(c x).val e f] := by
      funext i; fin_cases i; rfl
    rw [this]
  | neg φ ih =>
    intro n c e f
    simp only [ofFml, NFUCut.Sat]
    rw [← ih c e f]
    simp
  | and φ ψ ih1 ih2 =>
    intro n c e f
    simp only [ofFml, NFUCut.Sat]
    rw [← ih1 c e f, ← ih2 c e f]
    simp
  | all x φ ih =>
    intro n c e f
    simp only [ofFml, NFUCut.Sat, Semiformula.eval_all]
    refine forall_congr' fun a => ?_
    rw [ih]
    have : (fun i ↦ (Function.update (fun i ↦ Rew.bShift (c i)) x #0 i).val (a :> e) f) =
        Function.update (fun i ↦ (c i).val e f) x a := by
      funext i
      by_cases hi : i = x
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    rw [this]

end translation

section model

variable {M : Type} [Nonempty M] [s : Tarski.Structure ℒₛₑₜᵤ M] [Tarski.Structure.Eq ℒₛₑₜᵤ M]

omit [Tarski.Structure.Eq ℒₛₑₜᵤ M] in
/-- The meaning of the axiom "only sets have members". -/
lemma models_set_of_mem_iff :
    M↓[ℒₛₑₜᵤ] ⊧ (“∀ x y, x ∈ y → !isSet y” : Sentence ℒₛₑₜᵤ) ↔
      ∀ x y : M, s.rel Language.SetU.Rel.mem ![x, y] → s.rel Language.SetU.Rel.set ![y] := by
  let _ := Tarski.Structure.membership ℒₛₑₜᵤ M
  have := Tarski.Structure.membership_mem ℒₛₑₜᵤ M
  simp [models_iff, isSet]
  rfl

/-- The meaning of the axiom of extensionality for sets. -/
lemma models_extensionality_iff :
    M↓[ℒₛₑₜᵤ] ⊧ (“∀ x y, !isSet x → !isSet y → (∀ z, z ∈ x ↔ z ∈ y) → x = y” :
      Sentence ℒₛₑₜᵤ) ↔
      ∀ x y : M, s.rel Language.SetU.Rel.set ![x] → s.rel Language.SetU.Rel.set ![y] →
        (∀ z, s.rel Language.SetU.Rel.mem ![z, x] ↔ s.rel Language.SetU.Rel.mem ![z, y]) →
        x = y := by
  let _ := Tarski.Structure.membership ℒₛₑₜᵤ M
  have := Tarski.Structure.membership_mem ℒₛₑₜᵤ M
  simp [models_iff, isSet]
  rfl

omit [Tarski.Structure.Eq ℒₛₑₜᵤ M] in
/-- The meaning of an instance of the comprehension schema. -/
lemma models_comprehension_iff (φ : Semiproposition ℒₛₑₜᵤ 1) :
    M↓[ℒₛₑₜᵤ] ⊧ Axiom.comprehensionSchema φ ↔
      ∀ f : ℕ → M, ∃ y, s.rel Language.SetU.Rel.set ![y] ∧
        ∀ x, s.rel Language.SetU.Rel.mem ![x, y] ↔ Semiformula.Eval ![x] f φ := by
  let _ := Tarski.Structure.membership ℒₛₑₜᵤ M
  have := Tarski.Structure.membership_mem ℒₛₑₜᵤ M
  simp [models_iff, Axiom.comprehensionSchema, isSet]
  rfl

/-- The meaning of the axiom of infinity. -/
lemma models_infinity_iff :
    M↓[ℒₛₑₜᵤ] ⊧ Axiom.infinity ↔
      ∃ F : M,
        (∀ e, s.rel Language.SetU.Rel.set ![e] →
          (∀ z, ¬ s.rel Language.SetU.Rel.mem ![z, e]) → s.rel Language.SetU.Rel.mem ![e, F]) ∧
        (∀ a, s.rel Language.SetU.Rel.mem ![a, F] → ∀ b a', s.rel Language.SetU.Rel.set ![a'] →
          (∀ z, s.rel Language.SetU.Rel.mem ![z, a'] ↔
            s.rel Language.SetU.Rel.mem ![z, a] ∨ z = b) → s.rel Language.SetU.Rel.mem ![a', F]) ∧
        ∀ u, (∀ z, s.rel Language.SetU.Rel.mem ![z, u]) →
          ¬ s.rel Language.SetU.Rel.mem ![u, F] := by
  let _ := Tarski.Structure.membership ℒₛₑₜᵤ M
  have := Tarski.Structure.membership_mem ℒₛₑₜᵤ M
  simp [models_iff, Axiom.infinity, isSet]
  rfl

/-- **A model of `𝗡𝗙𝗨ₛ` is a model of NFU in the sense of `NFUCut.Model`.** -/
def modelOfNFU (h : M↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨ₛ) : NFUCut.Model M where
  mem a b := s.rel Language.SetU.Rel.mem ![a, b]
  isSet a := s.rel Language.SetU.Rel.set ![a]
  isSet_of_mem := fun {x y} hxy =>
    models_set_of_mem_iff.mp (models_theory_iff.mp h _ NewFoundationsU.set_of_mem) x y hxy
  ext := fun {x y} hx hy hxy =>
    models_extensionality_iff.mp (models_theory_iff.mp h _ NewFoundationsU.extensionality)
      x y hx hy hxy
  comp := fun σ φ x hstrat ρ => by
    let c : ℕ → Semiterm ℒₛₑₜᵤ ℕ 1 := Function.update (fun i ↦ &i) x #0
    have hst : (ofFml c φ).IsStratified :=
      ⟨σ, ![σ x], stratified_ofFml φ hstrat c σ ![σ x] (fun i => by
        by_cases hi : i = x
        · subst hi; simp [c]
        · simp [c, Function.update_of_ne hi])⟩
    obtain ⟨y, hy1, hy2⟩ := (models_comprehension_iff _).mp
      (models_theory_iff.mp h _ (NewFoundationsU.comprehension _ hst)) ρ
    refine ⟨y, hy1, fun a => (hy2 a).trans ?_⟩
    rw [eval_ofFml]
    have : (fun i ↦ (c i).val ![a] ρ) = Function.update ρ x a := by
      funext i
      by_cases hi : i = x
      · subst hi; simp [c]
      · simp [c, Function.update_of_ne hi]
    rw [this]

/-- **The axiom of infinity `𝗜𝗡𝗙ₛ` says the same as `NFUCut.Model.Infinity`**: the universe is
not finite if and only if it belongs to no natural number. -/
theorem modelOfNFU_infinity_iff (h : M↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨ₛ) :
    (modelOfNFU h).Infinity ↔ M↓[ℒₛₑₜᵤ] ⊧ Axiom.infinity := by
  rw [models_infinity_iff]
  let Mo := modelOfNFU h
  constructor
  · intro hinf
    obtain ⟨F, -, hF⟩ := Mo.comp (fun i => if i = 0 then 0 else if i = 28 then 1 else 2)
      (NFUCut.Model.fFin 0 3) 0 rfl (fun _ => Mo.nat)
    have hF' : ∀ a, Mo.mem a F ↔ Mo.Fin a := by
      intro a
      rw [hF a, Mo.sat_fFin (x := 0) (N := 3) (by decide) (by decide)]
      rfl
    refine ⟨F, fun e he hz => ?_, fun a ha b a' ha' hz => ?_, fun u hu huF => ?_⟩
    · have e1 : e = Mo.emp := Mo.eq_emp he hz
      rw [e1]
      exact (hF' _).mpr Mo.fin_emp
    · have e1 : a' = Mo.adj a b := Mo.eq_adj_iff.mp hz
      rw [e1]
      exact (hF' _).mpr (Mo.fin_adj b ((hF' a).mp ha))
    · obtain ⟨hset, k, hk, huk⟩ := (hF' u).mp huF
      have e1 : u = Mo.univ :=
        Mo.ext hset Mo.univ_isSet fun z => ⟨fun _ => Mo.mem_univ z, fun _ => hu z⟩
      rw [e1] at huk
      exact hinf k hk huk
  · rintro ⟨F, h0, hs, hu⟩ n hn hun
    have hfin : Mo.Fin Mo.univ := ⟨Mo.univ_isSet, n, hn, hun⟩
    have key : Mo.mem Mo.univ F :=
      Mo.fin_ind (F := F) (h0 _ Mo.emp_isSet Mo.not_mem_emp)
        (fun a b haF => hs a haF b _ (Mo.adj_isSet a b) (fun z => Mo.mem_adj)) hfin
    exact hu _ Mo.mem_univ key

end model

end FFL.FirstOrder.SetTheoryU

/-!
## `𝗡𝗙` interprets `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ`

The interpretation is the identity on the universe, with "is a set" interpreted as truth.
-/

namespace FFL.FirstOrder

/-! ### Operators and relation symbols -/

namespace Semiformula.Operator

variable {L : Language} {M : Type*} [s : Tarski.Structure L M]

lemma Mem.val_iff [L.Mem] (v : Fin 2 → M) :
    (Operator.Mem.mem : Operator L 2).val v ↔ s.rel Language.Mem.mem v := by
  simp only [Operator.val, Operator.Mem.sentence_eq, Semiformula.eval_rel]
  have : (Semiterm.val (L := L) v Empty.elim ∘ Semiterm.bvar : Fin 2 → M) = v := by
    funext i; simp
  rw [this]

lemma Eq.val_iff [L.Eq] (v : Fin 2 → M) :
    (Operator.Eq.eq : Operator L 2).val v ↔ s.rel Language.Eq.eq v := by
  simp only [Operator.val, Operator.Eq.sentence_eq, Semiformula.eval_rel]
  have : (Semiterm.val (L := L) v Empty.elim ∘ Semiterm.bvar : Fin 2 → M) = v := by
    funext i; simp
  rw [this]

end Semiformula.Operator

/-! ### Forgetting "is a set" -/

section unset

variable {ξ : Type*}

/-- A term of `ℒₛₑₜᵤ` as a term of `ℒₛₑₜ`. -/
def Semiterm.unset {n : ℕ} : Semiterm ℒₛₑₜᵤ ξ n → Semiterm ℒₛₑₜ ξ n
  | #x => #x
  | &x => &x
  | .func f _ => Empty.elim f

/-- An atomic formula of `ℒₛₑₜᵤ` as a formula of `ℒₛₑₜ`, with "is a set" replaced by truth. -/
def Semiformula.unsetRel {n : ℕ} :
    {k : ℕ} → (ℒₛₑₜᵤ).Rel k → (Fin k → Semiterm ℒₛₑₜ ξ n) → Semiformula ℒₛₑₜ ξ n
  | _, Language.SetU.Rel.eq, v => Semiformula.rel Language.Set.Rel.eq v
  | _, Language.SetU.Rel.mem, v => Semiformula.rel Language.Set.Rel.mem v
  | _, Language.SetU.Rel.set, _ => ⊤

/-- A formula of `ℒₛₑₜᵤ` as a formula of `ℒₛₑₜ`, with "is a set" replaced by truth. -/
def Semiformula.unset {n : ℕ} : Semiformula ℒₛₑₜᵤ ξ n → Semiformula ℒₛₑₜ ξ n
  | .rel r v => unsetRel r (fun i ↦ (v i).unset)
  | .nrel r v => ∼unsetRel r (fun i ↦ (v i).unset)
  | ⊤ => ⊤
  | ⊥ => ⊥
  | φ ⋏ ψ => φ.unset ⋏ ψ.unset
  | φ ⋎ ψ => φ.unset ⋎ ψ.unset
  | ∀¹ φ => ∀¹ φ.unset
  | ∃¹ φ => ∃¹ φ.unset

@[simp] lemma Semiterm.lv_unset (σ : ξ → ℕ) {n : ℕ} (τ : Fin n → ℕ) (t : Semiterm ℒₛₑₜᵤ ξ n) :
    t.unset.lv σ τ = t.lv σ τ := by
  match t with
  | #x => rfl
  | &x => rfl
  | .func f _ => exact Empty.elim f

lemma Semiformula.stratified_unsetRel {σ : ξ → ℕ} {n : ℕ} {τ : Fin n → ℕ} {k : ℕ}
    (r : (ℒₛₑₜᵤ).Rel k) (v : Fin k → Semiterm ℒₛₑₜᵤ ξ n)
    (h : ∃ t, ∀ i, (v i).lv σ τ = t + Language.Stratification.lv r i) :
    (unsetRel r (fun i ↦ (v i).unset)).Stratified σ τ := by
  obtain ⟨t, ht⟩ := h
  cases r with
  | eq =>
    refine Semiformula.stratified_rel.mpr ⟨t, fun i => ?_⟩
    rw [Semiterm.lv_unset, ht i]
    fin_cases i <;> rfl
  | mem =>
    refine Semiformula.stratified_rel.mpr ⟨t, fun i => ?_⟩
    rw [Semiterm.lv_unset, ht i]
    fin_cases i <;> rfl
  | set => trivial

/-- Forgetting "is a set" preserves stratification. -/
lemma Semiformula.stratified_unset {σ : ξ → ℕ} {n : ℕ} (φ : Semiformula ℒₛₑₜᵤ ξ n) :
    ∀ τ : Fin n → ℕ, φ.Stratified σ τ → φ.unset.Stratified σ τ := by
  induction φ using Semiformula.rec' with
  | hverum => intro τ _; trivial
  | hfalsum => intro τ _; trivial
  | hrel r v => intro τ h; exact stratified_unsetRel r v (stratified_rel.mp h)
  | hnrel r v =>
    intro τ h
    exact stratified_neg.mpr (stratified_unsetRel r v (stratified_nrel.mp h))
  | hand φ ψ ih1 ih2 =>
    intro τ h
    exact stratified_and.mpr ⟨ih1 τ (stratified_and.mp h).1, ih2 τ (stratified_and.mp h).2⟩
  | hor φ ψ ih1 ih2 =>
    intro τ h
    exact stratified_or.mpr ⟨ih1 τ (stratified_or.mp h).1, ih2 τ (stratified_or.mp h).2⟩
  | hall φ ih =>
    intro τ h
    obtain ⟨t, ht⟩ := stratified_all.mp h
    exact stratified_all.mpr ⟨t, ih _ ht⟩
  | hexs φ ih =>
    intro τ h
    obtain ⟨t, ht⟩ := stratified_exs.mp h
    exact stratified_exs.mpr ⟨t, ih _ ht⟩

section semantics

variable {N M : Type*} [sN : Tarski.Structure ℒₛₑₜᵤ N] [sM : Tarski.Structure ℒₛₑₜ M]

lemma Semiterm.val_unset (p : N → M) {n : ℕ} (e : Fin n → N) (f : ξ → N)
    (t : Semiterm ℒₛₑₜᵤ ξ n) : t.unset.val (p ∘ e) (p ∘ f) = p (t.val e f) := by
  match t with
  | #x => rfl
  | &x => rfl
  | .func f _ => exact Empty.elim f

/-- Forgetting "is a set" preserves meaning, along a surjection from a structure in which
everything is a set. -/
lemma Semiformula.eval_unset (p : N → M) (hp : Function.Surjective p)
    (heq : ∀ a b : N, sN.rel Language.SetU.Rel.eq ![a, b] ↔
      sM.rel Language.Set.Rel.eq ![p a, p b])
    (hmem : ∀ a b : N, sN.rel Language.SetU.Rel.mem ![a, b] ↔
      sM.rel Language.Set.Rel.mem ![p a, p b])
    (hset : ∀ a : N, sN.rel Language.SetU.Rel.set ![a]) (f : ξ → N) {n : ℕ}
    (φ : Semiformula ℒₛₑₜᵤ ξ n) :
    ∀ e : Fin n → N, Semiformula.Eval e f φ ↔ Semiformula.Eval (p ∘ e) (p ∘ f) φ.unset := by
  have hatom : ∀ {n k : ℕ} (r : (ℒₛₑₜᵤ).Rel k) (v : Fin k → Semiterm ℒₛₑₜᵤ ξ n)
      (e : Fin n → N), sN.rel r (fun i ↦ (v i).val e f) ↔
        Semiformula.Eval (p ∘ e) (p ∘ f) (unsetRel r (fun i ↦ (v i).unset)) := by
    intro n k r v e
    cases r with
    | eq =>
      have h1 : (fun i ↦ (v i).val e f) = ![(v 0).val e f, (v 1).val e f] :=
        Matrix.fun_eq_vec_two _
      have h2 : (fun i ↦ (v i).unset.val (p ∘ e) (p ∘ f)) =
          ![p ((v 0).val e f), p ((v 1).val e f)] := by
        funext i; fin_cases i <;> exact Semiterm.val_unset p e f _
      rw [h1, heq]
      simp only [unsetRel, Semiformula.eval_rel']
      rw [h2]
    | mem =>
      have h1 : (fun i ↦ (v i).val e f) = ![(v 0).val e f, (v 1).val e f] :=
        Matrix.fun_eq_vec_two _
      have h2 : (fun i ↦ (v i).unset.val (p ∘ e) (p ∘ f)) =
          ![p ((v 0).val e f), p ((v 1).val e f)] := by
        funext i; fin_cases i <;> exact Semiterm.val_unset p e f _
      rw [h1, hmem]
      simp only [unsetRel, Semiformula.eval_rel']
      rw [h2]
    | set =>
      have h1 : (fun i ↦ (v i).val e f) = ![(v 0).val e f] := by
        funext i; fin_cases i; rfl
      rw [h1]
      simp [unsetRel, hset]
  have hcons : ∀ {n : ℕ} (a : N) (e : Fin n → N), p ∘ (a :> e) = p a :> p ∘ e :=
    fun a e => Matrix.comp_vecCons'' p a e
  induction φ using Semiformula.rec' with
  | hverum => intro e; simp [unset]
  | hfalsum => intro e; simp [unset]
  | hrel r v =>
    intro e
    rw [Semiformula.eval_rel']
    exact hatom r v e
  | hnrel r v =>
    intro e
    rw [Semiformula.eval_nrel', hatom r v e]
    simp [unset]
  | hand φ ψ ih1 ih2 => intro e; simp [unset, ih1 e, ih2 e]
  | hor φ ψ ih1 ih2 => intro e; simp [unset, ih1 e, ih2 e]
  | hall φ ih =>
    intro e
    simp only [unset, Semiformula.eval_all]
    constructor
    · intro h b
      obtain ⟨a, rfl⟩ := hp b
      rw [← hcons]
      exact (ih _).mp (h a)
    · intro h a
      refine (ih _).mpr ?_
      rw [hcons]
      exact h (p a)
  | hexs φ ih =>
    intro e
    simp only [unset, Semiformula.eval_ex]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨p a, ?_⟩
      rw [← hcons]
      exact (ih _).mp ha
    · rintro ⟨b, hb⟩
      obtain ⟨a, rfl⟩ := hp b
      refine ⟨a, (ih _).mpr ?_⟩
      rw [hcons]
      exact hb

end semantics

end unset

end FFL.FirstOrder

namespace FFL.FirstOrder

namespace SetTheory

section meaning

variable {M : Type} [Nonempty M] [s : Tarski.Structure ℒₛₑₜ M] [Tarski.Structure.Eq ℒₛₑₜ M]

/-- The meaning of the axiom of extensionality. -/
lemma models_extensionality_iff :
    M↓[ℒₛₑₜ] ⊧ (“∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y” : SetTheorySentence) ↔
      ∀ x y : M, (∀ z, s.rel Language.Set.Rel.mem ![z, x] ↔ s.rel Language.Set.Rel.mem ![z, y]) →
        x = y := by
  let _ := Tarski.Structure.membership ℒₛₑₜ M
  have := Tarski.Structure.membership_mem ℒₛₑₜ M
  simp [models_iff]
  rfl

omit [Tarski.Structure.Eq ℒₛₑₜ M] in
/-- The meaning of an instance of the comprehension schema. -/
lemma models_comprehension_iff (φ : SetTheorySemiproposition 1) :
    M↓[ℒₛₑₜ] ⊧ Axiom.comprehensionSchema φ ↔
      ∀ f : ℕ → M, ∃ y, ∀ x, s.rel Language.Set.Rel.mem ![x, y] ↔ Semiformula.Eval ![x] f φ := by
  let _ := Tarski.Structure.membership ℒₛₑₜ M
  have := Tarski.Structure.membership_mem ℒₛₑₜ M
  simp [models_iff, Axiom.comprehensionSchema]
  rfl

end meaning

/-! ### The translation -/

/-- The interpretation of the relation symbols of `ℒₛₑₜᵤ`: equality and membership are
themselves, and everything is a set. -/
def nfuRel : {k : ℕ} → (ℒₛₑₜᵤ).Rel k → Semiformula.Operator ℒₛₑₜ k
  | _, Language.SetU.Rel.eq => Semiformula.Operator.Eq.eq
  | _, Language.SetU.Rel.mem => Semiformula.Operator.Mem.mem
  | _, Language.SetU.Rel.set => ⟨⊤⟩

/-- The translation of `ℒₛₑₜᵤ` into `𝗡𝗙`: the domain is everything and "is a set" is true. -/
def nfuTranslation : DirectTranslation 𝗡𝗙 ℒₛₑₜᵤ where
  domain := ⟨⊤⟩
  rel := nfuRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    simp [models_iff, Semiformula.Operator.val]
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : nfuRel (Language.Eq.eq : (ℒₛₑₜᵤ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

open DirectTranslation

variable {M : Type} [Nonempty M] [s : Tarski.Structure ℒₛₑₜ M] [Tarski.Structure.Eq ℒₛₑₜ M]
  [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

omit [Nonempty M] [Tarski.Structure.Eq ℒₛₑₜ M] hT in
lemma nfuTranslation_dom (x : M) : nfuTranslation.Dom x := by
  simp [DirectTranslation.Dom, nfuTranslation, Semiformula.Operator.val]

omit [Nonempty M] [Tarski.Structure.Eq ℒₛₑₜ M] hT in
lemma nfuModel_val_surjective :
    Function.Surjective (fun a : nfuTranslation.Model M ↦ (a : M)) :=
  fun x => ⟨⟨x, nfuTranslation_dom x⟩, rfl⟩

omit [Nonempty M] [Tarski.Structure.Eq ℒₛₑₜ M] hT in
lemma nfuModel_ext {a b : nfuTranslation.Model M} (h : (a : M) = (b : M)) : a = b := by
  cases a; cases b; cases h; rfl

lemma nfuModel_set (a : nfuTranslation.Model M) :
    Tarski.Structure.rel (L := ℒₛₑₜᵤ) Language.SetU.Rel.set ![a] := by
  rw [Model.rel_iff]
  simp [nfuTranslation, nfuRel, Semiformula.Operator.val]

lemma nfuModel_mem (a b : nfuTranslation.Model M) :
    Tarski.Structure.rel (L := ℒₛₑₜᵤ) Language.SetU.Rel.mem ![a, b] ↔
      s.rel Language.Set.Rel.mem ![(a : M), (b : M)] := by
  rw [Model.rel_iff]
  have h1 : (fun i ↦ ((![a, b] i : nfuTranslation.Model M) : M)) = ![(a : M), (b : M)] := by
    funext i; fin_cases i <;> rfl
  rw [h1]
  exact Semiformula.Operator.Mem.val_iff (L := ℒₛₑₜ) _

lemma nfuModel_eq (a b : nfuTranslation.Model M) :
    Tarski.Structure.rel (L := ℒₛₑₜᵤ) Language.SetU.Rel.eq ![a, b] ↔
      s.rel Language.Set.Rel.eq ![(a : M), (b : M)] := by
  rw [Model.rel_iff]
  have h1 : (fun i ↦ ((![a, b] i : nfuTranslation.Model M) : M)) = ![(a : M), (b : M)] := by
    funext i; fin_cases i <;> rfl
  rw [h1]
  exact Semiformula.Operator.Eq.val_iff (L := ℒₛₑₜ) _

/-- In a model of `𝗡𝗙`, the interpreted structure is a model of `𝗡𝗙𝗨ₛ`. -/
theorem nfuModel_models_nfu : (nfuTranslation.Model M)↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨ₛ := by
  refine models_theory_iff.mpr fun φ hφ => ?_
  cases hφ with
  | equality φ hφ =>
    have : (nfuTranslation.Model M)↓[ℒₛₑₜᵤ] ⊧* 𝗘𝗤 ℒₛₑₜᵤ := inferInstance
    exact models_theory_iff.mp this φ hφ
  | set_of_mem => exact SetTheoryU.models_set_of_mem_iff.mpr fun x y _ => nfuModel_set y
  | extensionality =>
    refine SetTheoryU.models_extensionality_iff.mpr fun x y _ _ hxy => ?_
    refine nfuModel_ext (models_extensionality_iff.mp
      (models_theory_iff.mp hT _ NewFoundations.extensionality) x.val y.val fun z => ?_)
    have := hxy ⟨z, nfuTranslation_dom z⟩
    rw [nfuModel_mem, nfuModel_mem] at this
    exact this
  | comprehension φ hφ =>
    obtain ⟨σ, τ, hst⟩ := hφ
    refine (SetTheoryU.models_comprehension_iff φ).mpr fun f => ?_
    obtain ⟨y, hy⟩ := (models_comprehension_iff φ.unset).mp
      (models_theory_iff.mp hT _
        (NewFoundations.comprehension _ ⟨σ, τ, Semiformula.stratified_unset φ τ hst⟩))
      (fun i ↦ ((f i : nfuTranslation.Model M) : M))
    refine ⟨⟨y, nfuTranslation_dom y⟩, nfuModel_set _, fun x => ?_⟩
    rw [nfuModel_mem]
    refine (hy x).trans ?_
    have key := Semiformula.eval_unset (fun a : nfuTranslation.Model M ↦ (a : M))
      nfuModel_val_surjective nfuModel_eq nfuModel_mem nfuModel_set f φ ![x]
    rw [key]
    have h1 : ((fun a : nfuTranslation.Model M ↦ (a : M)) ∘ ![x]) = ![(x : M)] := by
      funext i; fin_cases i; rfl
    rw [h1]
    rfl

/-- **In a model of `𝗡𝗙`, the interpreted structure is a model of `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ`.** The axiom of
infinity holds by `NFUCut.Model.nf_infinity`. -/
theorem nfuModel_models_nfui : (nfuTranslation.Model M)↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨𝗜ₛ := by
  have h : (nfuTranslation.Model M)↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨ₛ := nfuModel_models_nfu
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | hφ
  · exact models_theory_iff.mp h φ hφ
  · have e : φ = SetTheoryU.Axiom.infinity := hφ
    rw [e]
    have : Fact (∀ x, (SetTheoryU.modelOfNFU h).isSet x) := ⟨fun x => nfuModel_set x⟩
    exact (SetTheoryU.modelOfNFU_infinity_iff h).mp (SetTheoryU.modelOfNFU h).nf_infinity

end model

/-- **`𝗡𝗙` interprets `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ`.** -/
instance interpretsNFUI : 𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜ₛ where
  trln := nfuTranslation
  interpret_theory φ hφ := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp nfuModel_models_nfui φ hφ)

end SetTheory

end FFL.FirstOrder

/-!
## `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ` interprets `𝗡𝗙`, and the two theories are mutually interpretable

The domain of the interpretation is the formula `nfDom` (the least codes of the terms) and
membership is interpreted by the formula `nfEps`, both translated to `ℒₛₑₜᵤ`. Equality is
interpreted by equality.
-/

namespace FFL.FirstOrder

namespace SetTheoryU

open DirectTranslation

/-- The domain of the interpretation of `𝗡𝗙`. -/
def nfDomain : Semiformula.Operator ℒₛₑₜᵤ 1 := ⟨ofFml (fun _ ↦ #0) NFUCut.nfDom⟩

/-- The interpretation of membership. -/
def nfMem : Semiformula.Operator ℒₛₑₜᵤ 2 :=
  ⟨ofFml (Function.update (fun _ ↦ #0) 103 #1) NFUCut.nfEps⟩

/-- The interpretation of the relation symbols of `ℒₛₑₜ`. -/
def nfRel : {k : ℕ} → (ℒₛₑₜ).Rel k → Semiformula.Operator ℒₛₑₜᵤ k
  | _, Language.Set.Rel.eq => Semiformula.Operator.Eq.eq
  | _, Language.Set.Rel.mem => nfMem

section model

variable {M : Type} [Nonempty M] [s : Tarski.Structure ℒₛₑₜᵤ M] [Tarski.Structure.Eq ℒₛₑₜᵤ M]

lemma nfDomain_val_iff (h : M↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨ₛ) (x : M) :
    nfDomain.val ![x] ↔
      NFUCut.Sat (modelOfNFU h).mem (modelOfNFU h).isSet NFUCut.nfDom (fun _ ↦ x) :=
  eval_ofFml NFUCut.nfDom (fun _ ↦ #0) ![x] Empty.elim

lemma nfMem_val_iff (h : M↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨ₛ) (x y : M) :
    nfMem.val ![x, y] ↔
      NFUCut.Sat (modelOfNFU h).mem (modelOfNFU h).isSet NFUCut.nfEps
        (Function.update (fun _ ↦ x) 103 y) := by
  have key := eval_ofFml (s := s) NFUCut.nfEps
    (Function.update (fun _ ↦ (#0 : Semiterm ℒₛₑₜᵤ Empty 2)) 103 #1) ![x, y] Empty.elim
  have e : (fun i ↦ (Function.update (fun _ ↦ (#0 : Semiterm ℒₛₑₜᵤ Empty 2)) 103 #1 i).val
      ![x, y] Empty.elim) = Function.update (fun _ ↦ x) 103 y := by
    funext i
    by_cases hi : i = 103
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [e] at key
  exact key

omit [Tarski.Structure.Eq ℒₛₑₜᵤ M] in
lemma models_nfu_of_nfui (hT : M↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨𝗜ₛ) : M↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨ₛ :=
  models_of_ss hT Set.subset_union_left

lemma infinity_of_nfui (hT : M↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨𝗜ₛ) :
    (modelOfNFU (models_nfu_of_nfui hT)).Infinity :=
  (modelOfNFU_infinity_iff _).mpr (models_theory_iff.mp hT _ (Or.inr rfl))

end model

/-- The translation of `ℒₛₑₜ` into `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ`. -/
def nfTranslation : DirectTranslation 𝗡𝗙𝗨𝗜ₛ ℒₛₑₜ where
  domain := nfDomain
  rel := nfRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    have hU := models_nfu_of_nfui hT
    have : Fact (modelOfNFU hU).Infinity := ⟨infinity_of_nfui hT⟩
    obtain ⟨x⟩ := (modelOfNFU hU).dom_isNF.nonempty
    suffices ∃ x : M, nfDomain.val ![x] by simpa [models_iff] using this
    exact ⟨x.1, (nfDomain_val_iff hU x.1).mpr x.2⟩
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : nfRel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {M : Type} [Nonempty M] [s : Tarski.Structure ℒₛₑₜᵤ M] [Tarski.Structure.Eq ℒₛₑₜᵤ M]
  [hT : M↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨𝗜ₛ]

/-- **In a model of `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ`, the interpreted structure is a model of NF** in the sense of
`ConNF.NF.IsNF`. This is `NFUCut.Model.dom_isNF`. -/
theorem nfModel_isNF :
    ConNF.NF.IsNF (nfTranslation.Model M)
      (fun a b ↦ Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b]) := by
  have hU := models_nfu_of_nfui hT
  have : Fact (modelOfNFU hU).Infinity := ⟨infinity_of_nfui hT⟩
  have hdom : ∀ a : nfTranslation.Model M,
      NFUCut.Sat (modelOfNFU hU).mem (modelOfNFU hU).isSet NFUCut.nfDom (fun _ ↦ (a : M)) :=
    fun a => (nfDomain_val_iff hU _).mp a.dom
  refine ConNF.NF.IsNF.of_bijective
    (fun a ↦ (Subtype.mk (a : M) (hdom a) : (modelOfNFU hU).Dom))
    ⟨fun a b hab => ?_, fun w => ?_⟩ (fun a b => ?_) (modelOfNFU hU).dom_isNF
  · have e : (a : M) = (b : M) := congrArg Subtype.val hab
    cases a; cases b; cases e; rfl
  · exact ⟨⟨w.1, (nfDomain_val_iff hU w.1).mpr w.2⟩, rfl⟩
  · rw [Model.rel_iff]
    have h1 : (fun i ↦ ((![a, b] i : nfTranslation.Model M) : M)) = ![(a : M), (b : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h1]
    exact nfMem_val_iff hU _ _

/-- In a model of `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ`, the interpreted structure is a model of `𝗡𝗙`. -/
theorem nfModel_models_nf : (nfTranslation.Model M)↓[ℒₛₑₜ] ⊧* 𝗡𝗙 :=
  SetTheory.models_nf_of_isNF nfModel_isNF

end model

/-- **`𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ` interprets `𝗡𝗙`.** -/
instance interpretsNF : 𝗡𝗙𝗨𝗜ₛ ⊳ 𝗡𝗙 where
  trln := nfTranslation
  interpret_theory φ hφ := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp nfModel_models_nf φ hφ)

/-- **`𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ` and `𝗡𝗙` are mutually interpretable.** -/
instance mutualInterpretation : 𝗡𝗙𝗨𝗜ₛ ⋈ 𝗡𝗙 where
  r := interpretsNF
  l := SetTheory.interpretsNFUI

/-- **The syntactic transformation from `𝗡𝗙` to `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ`.** The translation of a theorem
of `𝗡𝗙` is a theorem of `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ`. -/
theorem provable_translate_of_nf {σ : Sentence ℒₛₑₜ} (h : 𝗡𝗙 ⊢ σ) : 𝗡𝗙𝗨𝗜ₛ ⊢ interpretsNF σ :=
  DirectInterpretation.sound interpretsNF h

/-- **The syntactic transformation from `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ` to `𝗡𝗙`.** The translation of a theorem
of `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ` is a theorem of `𝗡𝗙`. -/
theorem provable_translate_of_nfui {σ : Sentence ℒₛₑₜᵤ} (h : 𝗡𝗙𝗨𝗜ₛ ⊢ σ) :
    𝗡𝗙 ⊢ SetTheory.interpretsNFUI σ :=
  DirectInterpretation.sound SetTheory.interpretsNFUI h

/-- **`𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ` and `𝗡𝗙` are equiconsistent**, as a statement about derivations. -/
theorem consistent_nfui_iff_consistent_nf :
    Entailment.Consistent 𝗡𝗙𝗨𝗜ₛ ↔ Entailment.Consistent 𝗡𝗙 := by
  rw [Entailment.consistent_iff_unprovable_bot, Entailment.consistent_iff_unprovable_bot]
  constructor
  · intro h hb
    exact h (by simpa using provable_translate_of_nf hb)
  · intro h hb
    exact h (by simpa using provable_translate_of_nfui hb)

end SetTheoryU

end FFL.FirstOrder

/-!
## Theorems of `𝗡𝗙`, as statements about derivations

* `provable_unset_of_nfui`: if `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ` proves `σ`, then `𝗡𝗙` proves `σ` with "is a set"
  replaced by truth.
* `nf_provable_universeInfinite`: `𝗡𝗙` proves that the universe is not finite.
* `nf_provable_not_choice`: `𝗡𝗙` proves the negation of the axiom of choice of the library.

This file does not use a model of NF. That `𝗡𝗙` is consistent is proved in
`NFConsistentViaNFU.lean` (from a model of NFU + Infinity) and in `NFConsistentViaConNF.lean`
(from con-nf's model of tangled type theory).
-/

namespace FFL.FirstOrder

namespace SetTheory

open DirectTranslation

/-- **Forgetting "is a set" turns theorems of `𝗡𝗙𝗨ₛ + 𝗜𝗡𝗙ₛ` into theorems of `𝗡𝗙`.** -/
theorem provable_unset_of_nfui {σ : Sentence ℒₛₑₜᵤ} (h : 𝗡𝗙𝗨𝗜ₛ ⊢ σ) : 𝗡𝗙 ⊢ σ.unset := by
  apply Theory.Proof.complete_on_eq_models.{_, 0}
  intro M _ s _ hT
  have hN : (nfuTranslation.Model M)↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨𝗜ₛ := nfuModel_models_nfui
  have h1 : (nfuTranslation.Model M)↓[ℒₛₑₜᵤ] ⊧ σ := models_of_provable hN h
  have key := (Semiformula.eval_unset (fun a : nfuTranslation.Model M ↦ (a : M))
    nfuModel_val_surjective nfuModel_eq nfuModel_mem nfuModel_set Empty.elim σ ![]).mp
    (models_iff.mp h1)
  have e1 : ((fun a : nfuTranslation.Model M ↦ (a : M)) ∘ ![]) = ![] := by
    funext i; exact i.elim0
  have e2 : ((fun a : nfuTranslation.Model M ↦ (a : M)) ∘ Empty.elim) = Empty.elim := by
    funext i; exact i.elim
  rw [e1, e2] at key
  exact models_iff.mpr key

/-- **`𝗡𝗙` proves that the universe is not finite.** -/
theorem nf_provable_universeInfinite : 𝗡𝗙 ⊢ Axiom.universeInfinite := by
  apply Theory.Proof.complete_on_eq_models.{_, 0}
  intro M _ s _ hT
  have hN : (nfuTranslation.Model M)↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨𝗜ₛ := nfuModel_models_nfui
  obtain ⟨F, h0, hs, hu⟩ := (SetTheoryU.models_infinity_iff (M := nfuTranslation.Model M)).mp
    (models_theory_iff.mp hN _ (Or.inr rfl))
  let _ := Tarski.Structure.membership ℒₛₑₜ M
  have := Tarski.Structure.membership_mem ℒₛₑₜ M
  suffices ∃ F : M, (∀ e, (∀ z, ¬ z ∈ e) → e ∈ F) ∧
      (∀ a ∈ F, ∀ b a', (∀ z, z ∈ a' ↔ z ∈ a ∨ z = b) → a' ∈ F) ∧
      ∀ u, (∀ z, z ∈ u) → ¬ u ∈ F by
    simpa [models_iff, Axiom.universeInfinite] using this
  let mk : M → nfuTranslation.Model M := fun x => ⟨x, nfuTranslation_dom x⟩
  have hm : ∀ a b : nfuTranslation.Model M,
      Tarski.Structure.rel (L := ℒₛₑₜᵤ) Language.SetU.Rel.mem ![a, b] ↔ (a : M) ∈ (b : M) :=
    nfuModel_mem
  refine ⟨F.val, fun e he => ?_, fun a ha b a' ha' => ?_, fun u hu' huF => ?_⟩
  · exact (hm (mk e) F).mp
      (h0 (mk e) (nfuModel_set _) fun z hz => he z.val ((hm z (mk e)).mp hz))
  · refine (hm (mk a') F).mp
      (hs (mk a) ((hm (mk a) F).mpr ha) (mk b) (mk a') (nfuModel_set _) fun z => ?_)
    rw [hm, hm]
    constructor
    · intro h
      rcases (ha' z.val).mp h with h | h
      · exact Or.inl h
      · exact Or.inr (nfuModel_ext h)
    · rintro (h | h)
      · exact (ha' z.val).mpr (Or.inl h)
      · exact (ha' z.val).mpr (Or.inr (congrArg Model.val h))
  · exact hu (mk u) (fun z => (hm z (mk u)).mpr (hu' z.val)) ((hm (mk u) F).mpr huF)

/-- **`𝗡𝗙` proves the negation of the axiom of choice.** -/
theorem nf_provable_not_choice : 𝗡𝗙 ⊢ ∼Axiom.choice := by
  apply SetTheory.complete.{0}
  intro M _ _ hT
  have hN : (nfuTranslation.Model M)↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨ₛ := nfuModel_models_nfu
  have : Fact (∀ x, (SetTheoryU.modelOfNFU hN).isSet x) := ⟨fun x => nfuModel_set x⟩
  have hnc : ¬ (SetTheoryU.modelOfNFU hN).AC := (SetTheoryU.modelOfNFU hN).nf_not_choice
  suffices ¬ (∀ 𝓧 : M, (∀ X ∈ 𝓧, IsNonempty X) ∧
      (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ z, z ∈ X ∧ z ∈ Y) → X = Y) →
      ∃ C, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X) by
    simpa [models_iff, Axiom.choice] using this
  intro hAC
  apply hnc
  let mk : M → nfuTranslation.Model M := fun x => ⟨x, nfuTranslation_dom x⟩
  have hm : ∀ a b : nfuTranslation.Model M,
      (SetTheoryU.modelOfNFU hN).mem a b ↔ (a : M) ∈ (b : M) := nfuModel_mem
  intro X hne hdis
  have h1 : ∀ A ∈ X.val, IsNonempty A := by
    intro A hA
    obtain ⟨u, hu⟩ := hne (mk A) ((hm (mk A) X).mpr hA)
    exact ⟨u.val, (hm u (mk A)).mp hu⟩
  have h2 : ∀ A ∈ X.val, ∀ B ∈ X.val, (∃ z, z ∈ A ∧ z ∈ B) → A = B := by
    rintro A hA B hB ⟨z, hzA, hzB⟩
    exact congrArg Model.val (hdis (mk A) (mk B) (mk z) ((hm (mk A) X).mpr hA)
      ((hm (mk B) X).mpr hB) ((hm (mk z) (mk A)).mpr hzA) ((hm (mk z) (mk B)).mpr hzB))
  obtain ⟨C, hC⟩ := hAC X.val ⟨h1, h2⟩
  refine ⟨mk C, fun a ha => ?_⟩
  obtain ⟨x, ⟨hxC, hxa⟩, hx⟩ := hC a.val ((hm a X).mp ha)
  refine ⟨mk x, (hm (mk x) a).mpr hxa, (hm (mk x) (mk C)).mpr hxC, fun u' hu'a hu'C => ?_⟩
  exact nfuModel_ext (hx u'.val ⟨(hm u' (mk C)).mp hu'C, (hm u' a).mp hu'a⟩)

/-! ### Checks on the statements -/

/-- The formula `x ∉ x` is not stratified. -/
theorem not_isStratified_not_mem_self :
    ¬ (“x. x ∉ x” : SetTheorySemiproposition 1).IsStratified := by
  rintro ⟨σ, τ, h⟩
  simp only [Semiformula.Operator.mem_def, Semiformula.stratified_neg,
    Semiformula.stratified_rel] at h
  obtain ⟨t, ht⟩ := h
  have h0 : τ 0 = t + 0 := ht 0
  have h1 : τ 0 = t + 1 := ht 1
  omega

/-- `𝗡𝗙` proves that there is a universal set. -/
theorem nf_provable_exists_universal : 𝗡𝗙 ⊢ “∃ u, ∀ x, x ∈ u” := by
  apply SetTheory.complete.{0}
  intro M _ _ hT
  obtain ⟨y, hy⟩ := (models_comprehension_iff ⊤).mp
    (models_theory_iff.mp hT _ (NewFoundations.comprehension ⊤ ⟨fun _ ↦ 0, ![0], trivial⟩))
    (fun _ ↦ Classical.arbitrary M)
  have : ∃ u : M, ∀ x, x ∈ u := ⟨y, fun x => (hy x).mpr (by simp)⟩
  simpa [models_iff] using this

end SetTheory

end FFL.FirstOrder

/-!
## `𝗡𝗙` refutes Zorn's lemma

The statement about derivations that corresponds to `NFUCut.Model.nf_not_zorn`.
-/

namespace FFL.FirstOrder

namespace SetTheory

open DirectTranslation

namespace Axiom

/-- Zorn's lemma for inclusion: a family in which every chain has an upper bound has a maximal
member. -/
def zorn : SetTheorySentence :=
  “∀ P, (∀ C, (∀ c ∈ C, c ∈ P) →
      (∀ c ∈ C, ∀ c' ∈ C, (∀ z ∈ c, z ∈ c') ∨ (∀ z ∈ c', z ∈ c)) →
      ∃ b ∈ P, ∀ c ∈ C, ∀ z ∈ c, z ∈ b) →
    ∃ m ∈ P, ∀ c ∈ P, (∀ z ∈ m, z ∈ c) → c = m”

end Axiom

/-- **`𝗡𝗙` proves the negation of Zorn's lemma.** -/
theorem nf_provable_not_zorn : 𝗡𝗙 ⊢ ∼Axiom.zorn := by
  apply SetTheory.complete.{0}
  intro M _ _ hT
  have hN : (nfuTranslation.Model M)↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨ₛ := nfuModel_models_nfu
  have : Fact (∀ x, (SetTheoryU.modelOfNFU hN).isSet x) := ⟨fun x => nfuModel_set x⟩
  have hnz : ¬ (SetTheoryU.modelOfNFU hN).ZornLemma := (SetTheoryU.modelOfNFU hN).nf_not_zorn
  suffices ¬ (∀ P : M, (∀ C : M, (∀ c ∈ C, c ∈ P) →
      (∀ c ∈ C, ∀ c' ∈ C, (∀ z ∈ c, z ∈ c') ∨ (∀ z ∈ c', z ∈ c)) →
      ∃ b ∈ P, ∀ c ∈ C, ∀ z ∈ c, z ∈ b) →
      ∃ m ∈ P, ∀ c ∈ P, (∀ z ∈ m, z ∈ c) → c = m) by
    simpa [models_iff, Axiom.zorn] using this
  intro hZ
  apply hnz
  let mk : M → nfuTranslation.Model M := fun x => ⟨x, nfuTranslation_dom x⟩
  have hm : ∀ a b : nfuTranslation.Model M,
      (SetTheoryU.modelOfNFU hN).mem a b ↔ (a : M) ∈ (b : M) := nfuModel_mem
  intro P hub
  have hubM : ∀ C : M, (∀ c ∈ C, c ∈ P.val) →
      (∀ c ∈ C, ∀ c' ∈ C, (∀ z ∈ c, z ∈ c') ∨ (∀ z ∈ c', z ∈ c)) →
      ∃ b ∈ P.val, ∀ c ∈ C, ∀ z ∈ c, z ∈ b := by
    intro C hCP hch
    obtain ⟨b, hb, hbub⟩ := hub (mk C)
      (fun c hc => (hm c P).mpr (hCP c.val ((hm c (mk C)).mp hc)))
      (fun c c' hc hc' =>
        (hch c.val ((hm c (mk C)).mp hc) c'.val ((hm c' (mk C)).mp hc')).imp
          (fun h z hz => (hm z c').mpr (h z.val ((hm z c).mp hz)))
          (fun h z hz => (hm z c).mpr (h z.val ((hm z c').mp hz))))
    exact ⟨b.val, (hm b P).mp hb, fun c hc z hz =>
      (hm (mk z) b).mp (hbub (mk c) ((hm (mk c) (mk C)).mpr hc) (mk z)
        ((hm (mk z) (mk c)).mpr hz))⟩
  obtain ⟨m, hmP, hmax⟩ := hZ P.val hubM
  exact ⟨mk m, (hm (mk m) P).mpr hmP, fun c hc hsub =>
    nfuModel_ext (hmax c.val ((hm c P).mp hc) fun z hz =>
      (hm (mk z) c).mp (hsub (mk z) ((hm (mk z) (mk m)).mpr hz)))⟩

end SetTheory

end FFL.FirstOrder
