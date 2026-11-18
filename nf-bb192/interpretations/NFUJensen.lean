import NFInterpretations
import NFUShift

set_option autoImplicit false

/-!
# Jensen's NFU + Infinity and NF interpret each other

`𝗡𝗙𝗨` is Jensen's NFU, in the language of membership and equality: extensionality for the
objects that have members, and stratified comprehension. `𝗡𝗙𝗨𝗜` adds the axiom that the
universe is not finite. Both are defined in `NFTheories.lean`.

## Main results

* `SetTheory.interpretsNFUs : 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙𝗨𝗜ₛ`, without parameters
* `SetTheory.nfuInterpretsNF : 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`
* `SetTheory.nfui_weakerThan_nf : 𝗡𝗙𝗨𝗜 ⪯ 𝗡𝗙` and `SetTheory.nfInterpretsNFU : 𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜`
* `SetTheory.nfuMutualNF : 𝗡𝗙𝗨𝗜 ⋈ 𝗡𝗙`
* `SetTheory.nfu_provable_translate_of_nf : 𝗡𝗙 ⊢ σ → 𝗡𝗙𝗨𝗜 ⊢ nfuInterpretsNF σ`
* `SetTheory.consistent_nfuInfinity_iff_consistent_nf`
-/

/-!
## From Jensen's NFU to NFU with a predicate for sethood

`𝗡𝗙𝗨` is NFU in the language of membership and equality. A model of it, with any object
without members chosen as the empty set, is a model of NFU in the sense of `NFUCut.Model`
(`modelOfJensenNFU`); the choice is a parameter of the proofs and does not occur in any
formula. The formula `memStarF` is the membership relation of `SZ1`, and `Semiformula.star`
translates the formulas of `ℒₛₑₜᵤ` to formulas of `ℒₛₑₜ`, preserving stratification and
meaning.
-/

namespace FFL.FirstOrder

namespace SetTheory

open NFUCut (Fml)

section translation

variable {ξ : Type*}

/-- Translation of a formula with named variables into `ℒₛₑₜ`, where `c` says which term each
name stands for and `st` translates "is a set". -/
def ofFmlS (st : {n : ℕ} → ℕ → Semiterm ℒₛₑₜ ξ n → Semiformula ℒₛₑₜ ξ n) :
    {n : ℕ} → (ℕ → Semiterm ℒₛₑₜ ξ n) → Fml → Semiformula ℒₛₑₜ ξ n
  | _, c, .mem x y => Semiformula.rel Language.Set.Rel.mem ![c x, c y]
  | _, c, .eq x y => Semiformula.rel Language.Set.Rel.eq ![c x, c y]
  | _, c, .set x => st x (c x)
  | _, c, .neg φ => ∼ofFmlS st c φ
  | _, c, .and φ ψ => ofFmlS st c φ ⋏ ofFmlS st c ψ
  | _, c, .all x φ => ∀¹ ofFmlS st (Function.update (fun i ↦ Rew.bShift (c i)) x #0) φ

/-- The translation of a stratified formula is stratified. Only the names that are free in the
formula need terms of the right types. -/
lemma stratified_ofFmlS {σ : ℕ → ℕ} {σ' : ξ → ℕ}
    {st : {n : ℕ} → ℕ → Semiterm ℒₛₑₜ ξ n → Semiformula ℒₛₑₜ ξ n}
    (hst : ∀ (x : ℕ) {n : ℕ} (t : Semiterm ℒₛₑₜ ξ n) (τ : Fin n → ℕ),
      t.lv σ' τ = σ x → (st x t).Stratified σ' τ)
    (φ : Fml) (h : φ.strat σ = true) :
    ∀ {n : ℕ} (c : ℕ → Semiterm ℒₛₑₜ ξ n) (τ : Fin n → ℕ),
      (∀ i, φ.Free i → (c i).lv σ' τ = σ i) → (ofFmlS st c φ).Stratified σ' τ := by
  induction φ with
  | mem x y =>
    intro n c τ hc
    have h' : σ y = σ x + 1 := by simpa [Fml.strat] using h
    refine Semiformula.stratified_rel.mpr ⟨σ x, fun i => ?_⟩
    fin_cases i
    · show (c x).lv σ' τ = σ x + 0
      rw [hc x (Or.inl rfl)]; rfl
    · show (c y).lv σ' τ = σ x + 1
      rw [hc y (Or.inr rfl), h']
  | eq x y =>
    intro n c τ hc
    have h' : σ x = σ y := by simpa [Fml.strat] using h
    refine Semiformula.stratified_rel.mpr ⟨σ x, fun i => ?_⟩
    fin_cases i
    · show (c x).lv σ' τ = σ x + 0
      rw [hc x (Or.inl rfl)]; rfl
    · show (c y).lv σ' τ = σ x + 0
      rw [hc y (Or.inr rfl), h']; rfl
  | set x =>
    intro n c τ hc
    exact hst x (c x) τ (hc x rfl)
  | neg φ ih =>
    intro n c τ hc
    exact Semiformula.stratified_neg.mpr (ih (by simpa [Fml.strat] using h) c τ hc)
  | and φ ψ ih1 ih2 =>
    intro n c τ hc
    have h' : φ.strat σ = true ∧ ψ.strat σ = true := by simpa [Fml.strat] using h
    exact Semiformula.stratified_and.mpr
      ⟨ih1 h'.1 c τ fun i hi => hc i (Or.inl hi), ih2 h'.2 c τ fun i hi => hc i (Or.inr hi)⟩
  | all x φ ih =>
    intro n c τ hc
    refine Semiformula.stratified_all.mpr ⟨σ x, ih (by simpa [Fml.strat] using h) _ _ ?_⟩
    intro i hi
    by_cases hix : i = x
    · subst hix; simp
    · simp [Function.update_of_ne hix, hc i ⟨hix, hi⟩]

variable {M : Type} [s : Tarski.Structure ℒₛₑₜ M] [Tarski.Structure.Eq ℒₛₑₜ M]

/-- The translation has the same meaning. -/
lemma eval_ofFmlS {st : {n : ℕ} → ℕ → Semiterm ℒₛₑₜ ξ n → Semiformula ℒₛₑₜ ξ n}
    (isSet : M → Prop) (f : ξ → M)
    (hst : ∀ (x : ℕ) {n : ℕ} (t : Semiterm ℒₛₑₜ ξ n) (e : Fin n → M),
      Semiformula.Eval e f (st x t) ↔ isSet (t.val e f))
    (φ : Fml) :
    ∀ {n : ℕ} (c : ℕ → Semiterm ℒₛₑₜ ξ n) (e : Fin n → M),
      Semiformula.Eval e f (ofFmlS st c φ) ↔
        NFUCut.Sat (fun a b ↦ s.rel Language.Set.Rel.mem ![a, b]) isSet φ
          (fun i ↦ (c i).val e f) := by
  induction φ with
  | mem x y =>
    intro n c e
    simp only [ofFmlS, Semiformula.eval_rel, NFUCut.Sat]
    have : (Semiterm.val e f ∘ ![c x, c y]) = ![(c x).val e f, (c y).val e f] := by
      funext i; fin_cases i <;> rfl
    rw [this]
  | eq x y =>
    intro n c e
    simp only [ofFmlS, Semiformula.eval_rel, NFUCut.Sat]
    exact Tarski.Structure.eq_lang (L := ℒₛₑₜ) (v := Semiterm.val e f ∘ ![c x, c y])
  | set x =>
    intro n c e
    simp only [ofFmlS, NFUCut.Sat]
    exact hst x (c x) e
  | neg φ ih =>
    intro n c e
    simp only [ofFmlS, NFUCut.Sat]
    rw [← ih c e]
    simp
  | and φ ψ ih1 ih2 =>
    intro n c e
    simp only [ofFmlS, NFUCut.Sat]
    rw [← ih1 c e, ← ih2 c e]
    simp
  | all x φ ih =>
    intro n c e
    simp only [ofFmlS, NFUCut.Sat, Semiformula.eval_all]
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

/-! ### A model of `𝗡𝗙𝗨` as a `NFUCut.Model` -/

section model

variable {M : Type} [Nonempty M] [s : Tarski.Structure ℒₛₑₜ M] [Tarski.Structure.Eq ℒₛₑₜ M]

/-- The meaning of the axiom of extensionality for objects with members. -/
lemma models_weak_extensionality_iff :
    M↓[ℒₛₑₜ] ⊧ (“∀ x y, (∃ z, z ∈ x) → (∀ z, z ∈ x ↔ z ∈ y) → x = y” : SetTheorySentence) ↔
      ∀ x y : M, (∃ z, s.rel Language.Set.Rel.mem ![z, x]) →
        (∀ z, s.rel Language.Set.Rel.mem ![z, x] ↔ s.rel Language.Set.Rel.mem ![z, y]) →
        x = y := by
  let _ := Tarski.Structure.membership ℒₛₑₜ M
  have := Tarski.Structure.membership_mem ℒₛₑₜ M
  simp [models_iff]
  rfl

/-- The meaning of the axiom that the universe is not finite. -/
lemma models_universeInfinite_iff :
    M↓[ℒₛₑₜ] ⊧ Axiom.universeInfinite ↔
      ∃ F : M,
        (∀ e, (∀ z, ¬ s.rel Language.Set.Rel.mem ![z, e]) → s.rel Language.Set.Rel.mem ![e, F]) ∧
        (∀ a, s.rel Language.Set.Rel.mem ![a, F] → ∀ b a',
          (∀ z, s.rel Language.Set.Rel.mem ![z, a'] ↔
            s.rel Language.Set.Rel.mem ![z, a] ∨ z = b) → s.rel Language.Set.Rel.mem ![a', F]) ∧
        ∀ u, (∀ z, s.rel Language.Set.Rel.mem ![z, u]) →
          ¬ s.rel Language.Set.Rel.mem ![u, F] := by
  let _ := Tarski.Structure.membership ℒₛₑₜ M
  have := Tarski.Structure.membership_mem ℒₛₑₜ M
  simp [models_iff, Axiom.universeInfinite]
  rfl

omit [Tarski.Structure.Eq ℒₛₑₜ M] in
/-- `𝗡𝗙𝗨` proves that some object has no members. -/
lemma exists_empty (h : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨) :
    ∃ e : M, ∀ z, ¬ s.rel Language.Set.Rel.mem ![z, e] := by
  obtain ⟨y, hy⟩ := (models_comprehension_iff ⊥).mp
    (models_theory_iff.mp h _
      (NewFoundationsWithUrelements.comprehension ⊥ ⟨fun _ ↦ 0, ![0], trivial⟩))
    (fun _ ↦ Classical.arbitrary M)
  exact ⟨y, fun z hz => by simpa using (hy z).mp hz⟩

/-- The types of the free variables used for comprehension in `modelOfJensenNFU`: the variable
`2 * i` stands for the name `i`, with its type raised by one, and the variable `2 * t + 1`
stands for the empty set, at the type `t`. -/
def σJ (σ : ℕ → ℕ) : ℕ → ℕ := fun j ↦ if j % 2 = 0 then σ (j / 2) + 1 else j / 2

/-- "is a set": has a member, or is the empty set. -/
def stJ (σ : ℕ → ℕ) {n : ℕ} (x : ℕ) (t : Semiterm ℒₛₑₜ ℕ n) : Semiformula ℒₛₑₜ ℕ n :=
  (∃¹ Semiformula.rel Language.Set.Rel.mem ![#0, Rew.bShift t]) ⋎
    Semiformula.rel Language.Set.Rel.eq ![t, &(2 * (σ x + 1) + 1)]

omit [Nonempty M] in
lemma eval_stJ (σ : ℕ → ℕ) (e₀ : M) (f : ℕ → M) (hf : ∀ k, f (2 * k + 1) = e₀) (x : ℕ) {n : ℕ}
    (t : Semiterm ℒₛₑₜ ℕ n) (e : Fin n → M) :
    Semiformula.Eval e f (stJ σ x t) ↔
      (∃ z, s.rel Language.Set.Rel.mem ![z, t.val e f]) ∨ t.val e f = e₀ := by
  simp [stJ, Semiformula.eval_rel, hf]
  exact or_congr Iff.rfl (Tarski.Structure.eq_lang (L := ℒₛₑₜ) (v := ![_, _]))

/-- **A model of `𝗡𝗙𝗨`, with an object without members chosen as the empty set, is a model of
NFU in the sense of `NFUCut.Model`.** The sets are the objects with members and the chosen
object. -/
def modelOfJensenNFU (h : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨) (e₀ : M)
    (he₀ : ∀ z, ¬ s.rel Language.Set.Rel.mem ![z, e₀]) : NFUCut.Model M where
  mem a b := s.rel Language.Set.Rel.mem ![a, b]
  isSet a := (∃ z, s.rel Language.Set.Rel.mem ![z, a]) ∨ a = e₀
  isSet_of_mem := fun {x y} hxy => Or.inl ⟨x, hxy⟩
  ext := fun {x y} hx hy hxy => by
    rcases hx with hx | rfl
    · exact models_weak_extensionality_iff.mp
        (models_theory_iff.mp h _ NewFoundationsWithUrelements.extensionality) x y hx hxy
    · rcases hy with ⟨z, hz⟩ | rfl
      · exact absurd ((hxy z).mpr hz) (he₀ z)
      · rfl
  comp := fun σ φ x hstrat ρ => by
    let c : ℕ → Semiterm ℒₛₑₜ ℕ 1 := Function.update (fun i ↦ &(2 * i)) x #0
    let f : ℕ → M := fun j ↦ if j % 2 = 0 then ρ (j / 2) else e₀
    have hf : ∀ k, f (2 * k + 1) = e₀ := fun k => by
      simp [f]
    have hst : (ofFmlS (stJ σ) c φ).IsStratified := by
      refine ⟨σJ σ, ![σ x + 1], stratified_ofFmlS (σ := fun i ↦ σ i + 1)
        (fun x' {n} t τ ht => ?_) φ (Fml.strat_add 1 φ hstrat) c ![σ x + 1] (fun i _ => ?_)⟩
      · refine Semiformula.stratified_or.mpr ⟨Semiformula.stratified_exs.mpr ⟨σ x', ?_⟩, ?_⟩
        · refine Semiformula.stratified_rel.mpr ⟨σ x', fun i => ?_⟩
          fin_cases i
          · rfl
          · show (Rew.bShift t).lv (σJ σ) (σ x' :> τ) = σ x' + 1
            rw [Semiterm.lv_bShift, ht]
        · refine Semiformula.stratified_rel.mpr ⟨σ x' + 1, fun i => ?_⟩
          fin_cases i
          · show t.lv (σJ σ) τ = σ x' + 1 + 0
            rw [ht]
          · show σJ σ (2 * (σ x' + 1) + 1) = σ x' + 1 + 0
            have e1 : ¬ (2 * (σ x' + 1) + 1) % 2 = 0 := by omega
            simp only [σJ, e1, ite_false]
            omega
      · by_cases hi : i = x
        · subst hi; simp [c]
        · have e1 : (2 * i) % 2 = 0 := by omega
          have e2 : (2 * i) / 2 = i := by omega
          simp [c, Function.update_of_ne hi, σJ, e1, e2]
    obtain ⟨y, hy⟩ := (models_comprehension_iff _).mp
      (models_theory_iff.mp h _ (NewFoundationsWithUrelements.comprehension _ hst)) f
    have hev : ∀ a, Semiformula.Eval ![a] f (ofFmlS (stJ σ) c φ) ↔
        NFUCut.Sat (fun a b ↦ s.rel Language.Set.Rel.mem ![a, b])
          (fun a ↦ (∃ z, s.rel Language.Set.Rel.mem ![z, a]) ∨ a = e₀) φ
          (Function.update ρ x a) := by
      intro a
      rw [eval_ofFmlS (fun a ↦ (∃ z, s.rel Language.Set.Rel.mem ![z, a]) ∨ a = e₀) f
        (fun x' {n} t e => eval_stJ σ e₀ f hf x' t e) φ c ![a]]
      have : (fun i ↦ (c i).val ![a] f) = Function.update ρ x a := by
        funext i
        by_cases hi : i = x
        · subst hi; simp [c]
        · have e1 : (2 * i) % 2 = 0 := by omega
          have e2 : (2 * i) / 2 = i := by omega
          simp [c, f, Function.update_of_ne hi, e1, e2]
      rw [this]
    by_cases hne : ∃ z, s.rel Language.Set.Rel.mem ![z, y]
    · exact ⟨y, Or.inl hne, fun a => (hy a).trans (hev a)⟩
    · refine ⟨e₀, Or.inr rfl, fun a => ?_⟩
      rw [← hev a, ← hy a]
      exact ⟨fun h => absurd h (he₀ a), fun h => absurd ⟨a, h⟩ hne⟩

/-- **The axiom that the universe is not finite gives `NFUCut.Model.Infinity`.** -/
theorem modelOfJensenNFU_infinity (h : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨) (e₀ : M)
    (he₀ : ∀ z, ¬ s.rel Language.Set.Rel.mem ![z, e₀])
    (hI : M↓[ℒₛₑₜ] ⊧ Axiom.universeInfinite) : (modelOfJensenNFU h e₀ he₀).Infinity := by
  obtain ⟨F, h0, hs, hu⟩ := models_universeInfinite_iff.mp hI
  let Mo := modelOfJensenNFU h e₀ he₀
  intro n hn hun
  have hfin : Mo.Fin Mo.univ := ⟨Mo.univ_isSet, n, hn, hun⟩
  have key : Mo.mem Mo.univ F :=
    Mo.fin_ind (F := F) (h0 _ Mo.not_mem_emp)
      (fun a b haF => hs a haF b _ (fun z => Mo.mem_adj)) hfin
  exact hu _ Mo.mem_univ key

end model

/-! ### The new membership relation as a formula of `ℒₛₑₜ` -/

section memStar

variable {ξ : Type*}

/-- The membership relation `NFUCut.Model.MemS`, between two terms. -/
def memStarF {n : ℕ} (t u : Semiterm ℒₛₑₜ ξ n) : Semiformula ℒₛₑₜ ξ n :=
  ofFmlS (fun {_} _ _ ↦ ⊤) (fun i ↦ if i = 1 then u else t) NFUCut.Model.fMemS

/-- `memStarF t u` is stratified when the type of `u` is one more than the type of `t`, and
the type of `t` is at least one. -/
lemma stratified_memStarF {σ' : ξ → ℕ} {n : ℕ} {τ : Fin n → ℕ} {t u : Semiterm ℒₛₑₜ ξ n} (a : ℕ)
    (ht : t.lv σ' τ = a + 1) (hu : u.lv σ' τ = a + 2) : (memStarF t u).Stratified σ' τ := by
  refine stratified_ofFmlS (σ := fun i ↦ NFUCut.Model.σMemS i + a) (σ' := σ')
    (st := fun {_} _ _ ↦ ⊤) (fun _ {_} _ _ _ => Semiformula.stratified_verum) _
    (Fml.strat_add a _ NFUCut.Model.fMemS_strat) _ τ (fun i hi => ?_)
  rcases NFUCut.Model.fMemS_free hi with rfl | rfl
  · show t.lv σ' τ = 1 + a
    rw [ht]; omega
  · show u.lv σ' τ = 2 + a
    rw [hu]; omega

variable {M : Type} [Nonempty M] [s : Tarski.Structure ℒₛₑₜ M] [Tarski.Structure.Eq ℒₛₑₜ M]

/-- The meaning of `memStarF`. -/
lemma eval_memStarF (h : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨) (e₀ : M)
    (he₀ : ∀ z, ¬ s.rel Language.Set.Rel.mem ![z, e₀]) {n : ℕ} (t u : Semiterm ℒₛₑₜ ξ n)
    (e : Fin n → M) (f : ξ → M) :
    Semiformula.Eval e f (memStarF t u) ↔
      (modelOfJensenNFU h e₀ he₀).MemS (t.val e f) (u.val e f) := by
  unfold memStarF
  rw [eval_ofFmlS (fun _ ↦ True) f (fun _ _ _ => by simp) NFUCut.Model.fMemS _ e]
  rw [NFUCut.sat_congr_isSet _ (fun _ ↦ True) (modelOfJensenNFU h e₀ he₀).isSet _
    NFUCut.Model.fMemS_noSet]
  exact (modelOfJensenNFU h e₀ he₀).sat_fMemS _

end memStar

end SetTheory

/-! ### The translation of the formulas of `ℒₛₑₜᵤ` -/

section star

variable {ξ : Type*}

/-- An atomic formula of `ℒₛₑₜᵤ` as a formula of `ℒₛₑₜ`: membership becomes `memStarF`, and
"is a set" becomes "has a member". -/
def Semiformula.starRel {n : ℕ} :
    {k : ℕ} → (ℒₛₑₜᵤ).Rel k → (Fin k → Semiterm ℒₛₑₜ ξ n) → Semiformula ℒₛₑₜ ξ n
  | _, Language.SetU.Rel.eq, v => Semiformula.rel Language.Set.Rel.eq v
  | _, Language.SetU.Rel.mem, v => SetTheory.memStarF (v 0) (v 1)
  | _, Language.SetU.Rel.set, v =>
    ∃¹ Semiformula.rel Language.Set.Rel.mem ![#0, Rew.bShift (v 0)]

/-- A formula of `ℒₛₑₜᵤ` as a formula of `ℒₛₑₜ`. -/
def Semiformula.star {n : ℕ} : Semiformula ℒₛₑₜᵤ ξ n → Semiformula ℒₛₑₜ ξ n
  | .rel r v => starRel r (fun i ↦ (v i).unset)
  | .nrel r v => ∼starRel r (fun i ↦ (v i).unset)
  | ⊤ => ⊤
  | ⊥ => ⊥
  | φ ⋏ ψ => φ.star ⋏ ψ.star
  | φ ⋎ ψ => φ.star ⋎ ψ.star
  | ∀¹ φ => ∀¹ φ.star
  | ∃¹ φ => ∃¹ φ.star

lemma Semiterm.lv_unset_succ (σ : ξ → ℕ) {n : ℕ} (τ : Fin n → ℕ) (t : Semiterm ℒₛₑₜᵤ ξ n) :
    t.unset.lv (fun i ↦ σ i + 1) (fun i ↦ τ i + 1) = t.lv σ τ + 1 := by
  match t with
  | #x => rfl
  | &x => rfl
  | .func f _ => exact Empty.elim f

lemma Semiformula.stratified_starRel {σ : ξ → ℕ} {n : ℕ} {τ : Fin n → ℕ} {k : ℕ}
    (r : (ℒₛₑₜᵤ).Rel k) (v : Fin k → Semiterm ℒₛₑₜᵤ ξ n)
    (h : ∃ t, ∀ i, (v i).lv σ τ = t + Language.Stratification.lv r i) :
    (starRel r (fun i ↦ (v i).unset)).Stratified (fun i ↦ σ i + 1) (fun i ↦ τ i + 1) := by
  obtain ⟨t, ht⟩ := h
  cases r with
  | eq =>
    refine Semiformula.stratified_rel.mpr ⟨t + 1, fun i => ?_⟩
    rw [Semiterm.lv_unset_succ, ht i]
    fin_cases i <;> rfl
  | mem =>
    refine SetTheory.stratified_memStarF t ?_ ?_
    · rw [Semiterm.lv_unset_succ, ht 0]; rfl
    · rw [Semiterm.lv_unset_succ, ht 1]; rfl
  | set =>
    refine Semiformula.stratified_exs.mpr ⟨t, Semiformula.stratified_rel.mpr ⟨t, fun i => ?_⟩⟩
    fin_cases i
    · rfl
    · show (Rew.bShift (v 0).unset).lv (fun i ↦ σ i + 1) (t :> fun i ↦ τ i + 1) = t + 1
      rw [Semiterm.lv_bShift, Semiterm.lv_unset_succ, ht 0]
      rfl

/-- The translation preserves stratification, with every type raised by one. -/
lemma Semiformula.stratified_star {σ : ξ → ℕ} {n : ℕ} (φ : Semiformula ℒₛₑₜᵤ ξ n) :
    ∀ τ : Fin n → ℕ, φ.Stratified σ τ →
      φ.star.Stratified (fun i ↦ σ i + 1) (fun i ↦ τ i + 1) := by
  have hcons : ∀ {n : ℕ} (t : ℕ) (τ : Fin n → ℕ),
      (fun i ↦ (t :> τ) i + 1) = ((t + 1) :> fun i ↦ τ i + 1) := by
    intro n t τ
    funext i
    cases i using Fin.cases <;> simp
  induction φ using Semiformula.rec' with
  | hverum => intro τ _; trivial
  | hfalsum => intro τ _; trivial
  | hrel r v => intro τ h; exact stratified_starRel r v (stratified_rel.mp h)
  | hnrel r v =>
    intro τ h
    exact stratified_neg.mpr (stratified_starRel r v (stratified_nrel.mp h))
  | hand φ ψ ih1 ih2 =>
    intro τ h
    exact stratified_and.mpr ⟨ih1 τ (stratified_and.mp h).1, ih2 τ (stratified_and.mp h).2⟩
  | hor φ ψ ih1 ih2 =>
    intro τ h
    exact stratified_or.mpr ⟨ih1 τ (stratified_or.mp h).1, ih2 τ (stratified_or.mp h).2⟩
  | hall φ ih =>
    intro τ h
    obtain ⟨t, ht⟩ := stratified_all.mp h
    have := ih _ ht
    rw [hcons] at this
    exact stratified_all.mpr ⟨t + 1, this⟩
  | hexs φ ih =>
    intro τ h
    obtain ⟨t, ht⟩ := stratified_exs.mp h
    have := ih _ ht
    rw [hcons] at this
    exact stratified_exs.mpr ⟨t + 1, this⟩

section semantics

variable {N M : Type*} [sN : Tarski.Structure ℒₛₑₜᵤ N] [sM : Tarski.Structure ℒₛₑₜ M]

/-- The translation preserves meaning, along a surjection onto a structure for `ℒₛₑₜ` in which
`MemS` is the relation defined by `memStarF`. -/
lemma Semiformula.eval_star (p : N → M) (hp : Function.Surjective p) (MemS : M → M → Prop)
    (hF : ∀ {n : ℕ} (t u : Semiterm ℒₛₑₜ ξ n) (e : Fin n → M) (f : ξ → M),
      Semiformula.Eval e f (SetTheory.memStarF t u) ↔ MemS (t.val e f) (u.val e f))
    (heq : ∀ a b : N, sN.rel Language.SetU.Rel.eq ![a, b] ↔
      sM.rel Language.Set.Rel.eq ![p a, p b])
    (hmem : ∀ a b : N, sN.rel Language.SetU.Rel.mem ![a, b] ↔ MemS (p a) (p b))
    (hset : ∀ a : N, sN.rel Language.SetU.Rel.set ![a] ↔
      ∃ z, sM.rel Language.Set.Rel.mem ![z, p a]) (f : ξ → N) {n : ℕ}
    (φ : Semiformula ℒₛₑₜᵤ ξ n) :
    ∀ e : Fin n → N, Semiformula.Eval e f φ ↔ Semiformula.Eval (p ∘ e) (p ∘ f) φ.star := by
  have hatom : ∀ {n k : ℕ} (r : (ℒₛₑₜᵤ).Rel k) (v : Fin k → Semiterm ℒₛₑₜᵤ ξ n)
      (e : Fin n → N), sN.rel r (fun i ↦ (v i).val e f) ↔
        Semiformula.Eval (p ∘ e) (p ∘ f) (starRel r (fun i ↦ (v i).unset)) := by
    intro n k r v e
    cases r with
    | eq =>
      have h1 : (fun i ↦ (v i).val e f) = ![(v 0).val e f, (v 1).val e f] :=
        Matrix.fun_eq_vec_two _
      have h2 : (fun i ↦ (v i).unset.val (p ∘ e) (p ∘ f)) =
          ![p ((v 0).val e f), p ((v 1).val e f)] := by
        funext i; fin_cases i <;> exact Semiterm.val_unset p e f _
      rw [h1, heq]
      simp only [starRel, Semiformula.eval_rel']
      rw [h2]
    | mem =>
      have h1 : (fun i ↦ (v i).val e f) = ![(v 0).val e f, (v 1).val e f] :=
        Matrix.fun_eq_vec_two _
      rw [h1, hmem]
      simp only [starRel]
      rw [hF, Semiterm.val_unset, Semiterm.val_unset]
    | set =>
      have h1 : (fun i ↦ (v i).val e f) = ![(v 0).val e f] := by
        funext i; fin_cases i; rfl
      rw [h1, hset]
      simp [starRel, Semiformula.eval_rel, Semiterm.val_unset]
  have hcons : ∀ {n : ℕ} (a : N) (e : Fin n → N), p ∘ (a :> e) = p a :> p ∘ e :=
    fun a e => Matrix.comp_vecCons'' p a e
  induction φ using Semiformula.rec' with
  | hverum => intro e; simp [star]
  | hfalsum => intro e; simp [star]
  | hrel r v =>
    intro e
    rw [Semiformula.eval_rel']
    exact hatom r v e
  | hnrel r v =>
    intro e
    rw [Semiformula.eval_nrel', hatom r v e]
    simp [star]
  | hand φ ψ ih1 ih2 => intro e; simp [star, ih1 e, ih2 e]
  | hor φ ψ ih1 ih2 => intro e; simp [star, ih1 e, ih2 e]
  | hall φ ih =>
    intro e
    simp only [star, Semiformula.eval_all]
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
    simp only [star, Semiformula.eval_ex]
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

end star

end FFL.FirstOrder

/-!
## Jensen's NFU + Infinity and NF interpret each other

`𝗡𝗙𝗨𝗜` is NFU + Infinity in the language of membership and equality. It interprets the theory
`𝗡𝗙𝗨𝗜ₛ` with a predicate for sethood: the domain is everything, membership is `memStarF`, and
"is a set" is "has a member". No parameter is used. Composing with `𝗡𝗙𝗨𝗜ₛ ⊳ 𝗡𝗙` gives
`𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`. In the other direction every axiom of `𝗡𝗙𝗨𝗜` is a theorem of `𝗡𝗙`.
-/

namespace FFL.FirstOrder

namespace SetTheory

open DirectTranslation

/-- The interpretation of the relation symbols of `ℒₛₑₜᵤ` in `𝗡𝗙𝗨𝗜`. -/
def setRel : {k : ℕ} → (ℒₛₑₜᵤ).Rel k → Semiformula.Operator ℒₛₑₜ k
  | _, Language.SetU.Rel.eq => Semiformula.Operator.Eq.eq
  | _, Language.SetU.Rel.mem => ⟨memStarF #0 #1⟩
  | _, Language.SetU.Rel.set => ⟨∃¹ Semiformula.rel Language.Set.Rel.mem ![#0, #1]⟩

/-- The translation of `ℒₛₑₜᵤ` into `𝗡𝗙𝗨𝗜`. -/
def setTranslation : DirectTranslation 𝗡𝗙𝗨𝗜 ℒₛₑₜᵤ where
  domain := ⟨⊤⟩
  rel := setRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    simp [models_iff, Semiformula.Operator.val]
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : setRel (Language.Eq.eq : (ℒₛₑₜᵤ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {M : Type} [Nonempty M] [s : Tarski.Structure ℒₛₑₜ M] [Tarski.Structure.Eq ℒₛₑₜ M]
  [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

omit [Nonempty M] [Tarski.Structure.Eq ℒₛₑₜ M] hT in
lemma setTranslation_dom (x : M) : setTranslation.Dom x := by
  simp [DirectTranslation.Dom, setTranslation, Semiformula.Operator.val]

omit [Nonempty M] [Tarski.Structure.Eq ℒₛₑₜ M] hT in
lemma setModel_val_surjective :
    Function.Surjective (fun a : setTranslation.Model M ↦ (a : M)) :=
  fun x => ⟨⟨x, setTranslation_dom x⟩, rfl⟩

omit [Nonempty M] [Tarski.Structure.Eq ℒₛₑₜ M] hT in
lemma setModel_ext {a b : setTranslation.Model M} (h : (a : M) = (b : M)) : a = b := by
  cases a; cases b; cases h; rfl

lemma setModel_eq (a b : setTranslation.Model M) :
    Tarski.Structure.rel (L := ℒₛₑₜᵤ) Language.SetU.Rel.eq ![a, b] ↔
      s.rel Language.Set.Rel.eq ![(a : M), (b : M)] := by
  rw [Model.rel_iff]
  have h1 : (fun i ↦ ((![a, b] i : setTranslation.Model M) : M)) = ![(a : M), (b : M)] := by
    funext i; fin_cases i <;> rfl
  rw [h1]
  exact Semiformula.Operator.Eq.val_iff (L := ℒₛₑₜ) _

lemma setModel_set (a : setTranslation.Model M) :
    Tarski.Structure.rel (L := ℒₛₑₜᵤ) Language.SetU.Rel.set ![a] ↔
      ∃ z, s.rel Language.Set.Rel.mem ![z, (a : M)] := by
  rw [Model.rel_iff]
  have h1 : (fun i ↦ ((![a] i : setTranslation.Model M) : M)) = ![(a : M)] := by
    funext i; fin_cases i; rfl
  rw [h1]
  simp [setTranslation, setRel, Semiformula.Operator.val, Semiformula.eval_rel]

lemma setModel_mem (hU : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨) (e₀ : M)
    (he₀ : ∀ z, ¬ s.rel Language.Set.Rel.mem ![z, e₀]) (a b : setTranslation.Model M) :
    Tarski.Structure.rel (L := ℒₛₑₜᵤ) Language.SetU.Rel.mem ![a, b] ↔
      (modelOfJensenNFU hU e₀ he₀).MemS (a : M) (b : M) := by
  rw [Model.rel_iff]
  have h1 : (fun i ↦ ((![a, b] i : setTranslation.Model M) : M)) = ![(a : M), (b : M)] := by
    funext i; fin_cases i <;> rfl
  rw [h1]
  exact eval_memStarF hU e₀ he₀ #0 #1 ![(a : M), (b : M)] Empty.elim

/-- **In a model of `𝗡𝗙𝗨𝗜`, the interpreted structure is a model of `𝗡𝗙𝗨𝗜ₛ`.** -/
theorem setModel_models_nfus : (setTranslation.Model M)↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨𝗜ₛ := by
  have hU : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨 := models_of_ss hT Set.subset_union_left
  obtain ⟨e₀, he₀⟩ := exists_empty hU
  have hInf : Fact (modelOfJensenNFU hU e₀ he₀).Infinity :=
    ⟨modelOfJensenNFU_infinity hU e₀ he₀ (models_theory_iff.mp hT _ (Or.inr rfl))⟩
  have hm : ∀ a b : setTranslation.Model M,
      Tarski.Structure.rel (L := ℒₛₑₜᵤ) Language.SetU.Rel.mem ![a, b] ↔
        (modelOfJensenNFU hU e₀ he₀).MemS (a : M) (b : M) := setModel_mem hU e₀ he₀
  let mk : M → setTranslation.Model M := fun x => ⟨x, setTranslation_dom x⟩
  have h1 : (setTranslation.Model M)↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨ₛ := by
    refine models_theory_iff.mpr fun φ hφ => ?_
    cases hφ with
    | equality φ hφ =>
      have : (setTranslation.Model M)↓[ℒₛₑₜᵤ] ⊧* 𝗘𝗤 ℒₛₑₜᵤ := inferInstance
      exact models_theory_iff.mp this φ hφ
    | set_of_mem =>
      exact SetTheoryU.models_set_of_mem_iff.mpr fun x y hxy =>
        (setModel_set y).mpr ((modelOfJensenNFU hU e₀ he₀).memS_nonempty ((hm x y).mp hxy))
    | extensionality =>
      refine SetTheoryU.models_extensionality_iff.mpr fun x y hx hy hxy => ?_
      refine setModel_ext ((modelOfJensenNFU hU e₀ he₀).memS_ext ((setModel_set x).mp hx)
        ((setModel_set y).mp hy) fun z => ?_)
      have := hxy (mk z)
      rw [hm, hm] at this
      exact this
    | comprehension φ hφ =>
      obtain ⟨σ, τ, hst⟩ := hφ
      refine (SetTheoryU.models_comprehension_iff φ).mpr fun f => ?_
      obtain ⟨z, hz⟩ := (models_comprehension_iff φ.star).mp
        (models_theory_iff.mp hU _ (NewFoundationsWithUrelements.comprehension _
          ⟨_, _, Semiformula.stratified_star φ τ hst⟩))
        (fun i ↦ ((f i : setTranslation.Model M) : M))
      obtain ⟨y, hy1, hy2⟩ := (modelOfJensenNFU hU e₀ he₀).exists_codeS z
      refine ⟨mk y, (setModel_set _).mpr hy1, fun x => ?_⟩
      rw [hm]
      refine (hy2 x.val).trans ((hz x.val).trans ?_)
      have key := Semiformula.eval_star (fun a : setTranslation.Model M ↦ (a : M))
        setModel_val_surjective (modelOfJensenNFU hU e₀ he₀).MemS
        (fun t u e f => eval_memStarF hU e₀ he₀ t u e f) setModel_eq hm setModel_set f φ ![x]
      rw [key]
      have h1 : ((fun a : setTranslation.Model M ↦ (a : M)) ∘ ![x]) = ![(x : M)] := by
        funext i; fin_cases i; rfl
      rw [h1]
      rfl
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | hφ
  · exact models_theory_iff.mp h1 φ hφ
  · have e : φ = SetTheoryU.Axiom.infinity := hφ
    rw [e]
    obtain ⟨F, h0, hs, hu⟩ := (modelOfJensenNFU hU e₀ he₀).shift_infinity
    refine SetTheoryU.models_infinity_iff.mpr
      ⟨mk F, fun e he hz => ?_, fun a ha b a' ha' hz => ?_, fun u hu' huF => ?_⟩
    · exact (hm e (mk F)).mpr (h0 e.val ((setModel_set e).mp he)
        fun z hzz => hz (mk z) ((hm (mk z) e).mpr hzz))
    · refine (hm a' (mk F)).mpr (hs a.val ((hm a (mk F)).mp ha) b.val a'.val
        ((setModel_set a').mp ha') fun z => ?_)
      have := hz (mk z)
      rw [hm, hm] at this
      exact this.trans (or_congr Iff.rfl ⟨fun h => congrArg Model.val h, fun h => setModel_ext h⟩)
    · exact hu u.val (fun z => (hm (mk z) u).mp (hu' (mk z))) ((hm u (mk F)).mp huF)

end model

/-- **`𝗡𝗙𝗨𝗜` interprets `𝗡𝗙𝗨𝗜ₛ`**: NFU + Infinity in the language of membership and equality
interprets NFU + Infinity with a predicate for sethood. -/
instance interpretsNFUs : 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙𝗨𝗜ₛ where
  trln := setTranslation
  interpret_theory φ hφ := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp setModel_models_nfus φ hφ)

/-- **`𝗡𝗙𝗨𝗜` interprets `𝗡𝗙`.** -/
instance nfuInterpretsNF : 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙 :=
  DirectInterpretation.comp SetTheoryU.interpretsNF interpretsNFUs

section

variable {M : Type} [Nonempty M] [s : Tarski.Structure ℒₛₑₜ M] [Tarski.Structure.Eq ℒₛₑₜ M]

/-- A model of `𝗡𝗙` is a model of `𝗡𝗙𝗨𝗜`. -/
theorem models_nfui_of_models_nf (hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙) : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 := by
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | hφ
  · cases hφ with
    | equality φ hφ => exact models_theory_iff.mp hT φ (NewFoundations.equality φ hφ)
    | extensionality =>
      exact models_weak_extensionality_iff.mpr fun x y _ hxy =>
        models_extensionality_iff.mp
          (models_theory_iff.mp hT _ NewFoundations.extensionality) x y hxy
    | comprehension φ hφ =>
      exact models_theory_iff.mp hT _ (NewFoundations.comprehension φ hφ)
  · have e : φ = Axiom.universeInfinite := hφ
    rw [e]
    exact models_of_provable hT nf_provable_universeInfinite

end

/-- **Every theorem of `𝗡𝗙𝗨𝗜` is a theorem of `𝗡𝗙`.** -/
instance nfui_weakerThan_nf : 𝗡𝗙𝗨𝗜 ⪯ 𝗡𝗙 :=
  Entailment.weakerThan_iff.mpr fun {φ} h => by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    exact models_of_provable (models_nfui_of_models_nf hT) h

/-- **`𝗡𝗙` interprets `𝗡𝗙𝗨𝗜`**, by the identity. -/
instance nfInterpretsNFU : 𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜 := DirectInterpretation.ofWeakerThan 𝗡𝗙 𝗡𝗙𝗨𝗜

/-- **NFU + Infinity and NF are mutually interpretable**, both in the language of membership
and equality. -/
instance nfuMutualNF : 𝗡𝗙𝗨𝗜 ⋈ 𝗡𝗙 where
  r := nfuInterpretsNF
  l := nfInterpretsNFU

/-- The two formulations of NFU + Infinity are mutually interpretable. -/
instance nfuMutualNFUs : 𝗡𝗙𝗨𝗜 ⋈ 𝗡𝗙𝗨𝗜ₛ where
  r := interpretsNFUs
  l := DirectInterpretation.comp nfInterpretsNFU SetTheoryU.interpretsNF

/-- **The syntactic transformation from `𝗡𝗙` to `𝗡𝗙𝗨𝗜`.** -/
theorem nfu_provable_translate_of_nf {σ : Sentence ℒₛₑₜ} (h : 𝗡𝗙 ⊢ σ) :
    𝗡𝗙𝗨𝗜 ⊢ nfuInterpretsNF σ :=
  DirectInterpretation.sound nfuInterpretsNF h

/-- **NFU + Infinity and NF are equiconsistent**, as a statement about derivations. -/
theorem consistent_nfuInfinity_iff_consistent_nf :
    Entailment.Consistent 𝗡𝗙𝗨𝗜 ↔ Entailment.Consistent 𝗡𝗙 := by
  rw [Entailment.consistent_iff_unprovable_bot, Entailment.consistent_iff_unprovable_bot]
  constructor
  · intro h hb
    exact h (by simpa using nfu_provable_translate_of_nf hb)
  · intro h hb
    exact h (Entailment.weakerThan_iff.mp nfui_weakerThan_nf hb)

end SetTheory

end FFL.FirstOrder
