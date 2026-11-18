import ConNF.NF.NFUConstr
import ConNF.NF.Hailperin
import HostTerm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false


/-!
# Phase 0, part 1: formulas of a host as codes of the hierarchy

`CF` is a type of formulas in the two relation symbols `ε` and `<*` with the connectives that
the codes of §3 have. `code` gives the code of a formula, `TrC` its truth at a stage under an
assignment of names, and `bridge` says that the truth of the code, in the sense of the
hierarchy, is `TrC`.
-/

namespace NFUCut

/-- Formulas in `ε` and `<*` with negation, conjunction and the universal quantifier. -/
inductive CF : Type
  | mem (v w : ℕ)
  | lt (v w : ℕ)
  | neg (φ : CF)
  | and (φ ψ : CF)
  | all (v : ℕ) (φ : CF)

namespace CF

/-- The pairing function of §3.1 on standard numbers. -/
def npair (x y : ℕ) : ℕ := (x + y) * (x + y) + x

theorem le_npair_left (x y : ℕ) : x ≤ npair x y := Nat.le_add_left _ _

theorem le_npair_right (x y : ℕ) : y ≤ npair x y := by
  unfold npair
  nlinarith [Nat.zero_le x, Nat.zero_le y]

/-- The code of a formula as a standard number. -/
def ncode : CF → ℕ
  | mem v w => npair 0 (npair 0 (npair v w))
  | lt v w => npair 0 (npair 2 (npair v w))
  | neg φ => npair 1 φ.ncode
  | and φ ψ => npair 2 (npair φ.ncode ψ.ncode)
  | all v φ => npair 3 (npair v φ.ncode)

def imp (A B : CF) : CF := neg (and A (neg B))
def or (X Y : CF) : CF := neg (and (neg X) (neg Y))
def iff (A B : CF) : CF := and (neg (and A (neg B))) (neg (and B (neg A)))
def ex (v : ℕ) (c : CF) : CF := neg (all v (neg c))
/-- "`v` and `w` have the same members", with the auxiliary variable `z`. -/
def eq (z v w : ℕ) : CF := all z (iff (mem z v) (mem z w))

theorem mem_left (v w : ℕ) : v ≤ (mem v w).ncode :=
  le_trans (le_npair_left v w) (le_trans (le_npair_right 0 _) (le_npair_right 0 _))

theorem mem_right (v w : ℕ) : w ≤ (mem v w).ncode :=
  le_trans (le_npair_right v w) (le_trans (le_npair_right 0 _) (le_npair_right 0 _))

theorem lt_left (v w : ℕ) : v ≤ (lt v w).ncode :=
  le_trans (le_npair_left v w) (le_trans (le_npair_right 2 _) (le_npair_right 0 _))

theorem lt_right (v w : ℕ) : w ≤ (lt v w).ncode :=
  le_trans (le_npair_right v w) (le_trans (le_npair_right 2 _) (le_npair_right 0 _))

theorem neg_le (φ : CF) : φ.ncode ≤ (neg φ).ncode := le_npair_right 1 _

theorem and_left (φ ψ : CF) : φ.ncode ≤ (and φ ψ).ncode :=
  le_trans (le_npair_left _ _) (le_npair_right 2 _)

theorem and_right (φ ψ : CF) : ψ.ncode ≤ (and φ ψ).ncode :=
  le_trans (le_npair_right _ _) (le_npair_right 2 _)

theorem all_var (v : ℕ) (φ : CF) : v ≤ (all v φ).ncode :=
  le_trans (le_npair_left _ _) (le_npair_right 3 _)

theorem all_le (v : ℕ) (φ : CF) : φ.ncode ≤ (all v φ).ncode :=
  le_trans (le_npair_right _ _) (le_npair_right 3 _)

end CF

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

/-- The code of a formula in the model. -/
noncomputable def code : CF → M.Num
  | .mem v w => M.cRel 0 (v : M.Num) (w : M.Num)
  | .lt v w => M.cRel 2 (v : M.Num) (w : M.Num)
  | .neg φ => M.cNeg (code φ)
  | .and φ ψ => M.cAnd (code φ) (code ψ)
  | .all v φ => M.cAll (v : M.Num) (code φ)

theorem pairN_cast (x y : ℕ) : M.pairN (x : M.Num) (y : M.Num) = ((CF.npair x y : ℕ) : M.Num) := by
  simp [pairN, CF.npair]

theorem code_eq : ∀ φ : CF, M.code φ = ((φ.ncode : ℕ) : M.Num)
  | .mem v w => by
    have h0 : (0 : M.Num) = ((0 : ℕ) : M.Num) := by simp
    simp only [code, cRel, CF.ncode]
    rw [h0, pairN_cast, pairN_cast, pairN_cast]
  | .lt v w => by
    have h0 : (0 : M.Num) = ((0 : ℕ) : M.Num) := by simp
    have h2 : (2 : M.Num) = ((2 : ℕ) : M.Num) := by simp
    simp only [code, cRel, CF.ncode]
    rw [h0, h2, pairN_cast, pairN_cast, pairN_cast]
  | .neg φ => by
    have h1 : (1 : M.Num) = ((1 : ℕ) : M.Num) := by simp
    simp only [code, cNeg, CF.ncode]
    rw [code_eq φ, h1, pairN_cast]
  | .and φ ψ => by
    have h2 : (2 : M.Num) = ((2 : ℕ) : M.Num) := by simp
    simp only [code, cAnd, CF.ncode]
    rw [code_eq φ, code_eq ψ, h2, pairN_cast, pairN_cast]
  | .all v φ => by
    have h3 : (3 : M.Num) = ((3 : ℕ) : M.Num) := by simp
    simp only [code, cAll, CF.ncode]
    rw [code_eq φ, h3, pairN_cast, pairN_cast]

theorem cast_le_cast {a b : ℕ} (h : a ≤ b) : (a : M.Num) ≤ (b : M.Num) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  exact M.le_def.mpr ⟨(c : M.Num), by push_cast; rfl⟩

theorem cast_le_code {i : ℕ} {φ : CF} (h : i ≤ φ.ncode) : (i : M.Num) ≤ M.code φ := by
  rw [M.code_eq]
  exact M.cast_le_cast h

/-- Truth of a formula at the stage `α` under an assignment of names to the variables. -/
def TrC (P th io tp F Pr : V) (j : M.Num) (α : V) : CF → (ℕ → V) → Prop
  | .mem v w, ρ => M.EpsStarRaw P th io M.nat j.1 tp F (ρ v) (ρ w)
  | .lt v w, ρ => M.Lt P j.1 tp F Pr (ρ v) (ρ w)
  | .neg φ, ρ => ¬ TrC P th io tp F Pr j α φ ρ
  | .and φ ψ, ρ => TrC P th io tp F Pr j α φ ρ ∧ TrC P th io tp F Pr j α ψ ρ
  | .all v φ, ρ => ∀ a, M.InNRaw P th io M.nat j.1 α a →
      TrC P th io tp F Pr j α φ (Function.update ρ v a)

section bridge

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- Truth depends only on the values of the variables up to the code. -/
theorem tr_congr {α : V} : ∀ (φ : CF) (ρ ρ' : ℕ → V), (∀ i, i ≤ φ.ncode → ρ i = ρ' i) →
    (M.TrC P th io tp F Pr j α φ ρ ↔ M.TrC P th io tp F Pr j α φ ρ')
  | .mem v w, ρ, ρ', h => by
    simp only [TrC]
    rw [h v (CF.mem_left v w), h w (CF.mem_right v w)]
  | .lt v w, ρ, ρ', h => by
    simp only [TrC]
    rw [h v (CF.lt_left v w), h w (CF.lt_right v w)]
  | .neg φ, ρ, ρ', h => by
    simp only [TrC]
    exact not_congr (tr_congr φ ρ ρ' (fun i hi => h i (le_trans hi (CF.neg_le φ))))
  | .and φ ψ, ρ, ρ', h => by
    simp only [TrC]
    exact and_congr (tr_congr φ ρ ρ' (fun i hi => h i (le_trans hi (CF.and_left φ ψ))))
      (tr_congr ψ ρ ρ' (fun i hi => h i (le_trans hi (CF.and_right φ ψ))))
  | .all v φ, ρ, ρ', h => by
    simp only [TrC]
    refine forall_congr' fun a => imp_congr_right fun _ => ?_
    refine tr_congr φ _ _ (fun i hi => ?_)
    by_cases e : i = v
    · subst e
      simp
    · simp [Function.update_of_ne e, h i (le_trans hi (CF.all_le v φ))]

/-- **The bridge.** If the sequence `t` has the values `ρ i` at the variables up to the code of
`φ`, then the code of `φ` is true at the stage `α` under `t` if and only if `φ` is true under
`ρ`. -/
theorem bridge (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {α : V} (hα : M.mem (M.op α α) th) :
    ∀ (φ : CF) (ρ : ℕ → V) (t : V), (∀ i, M.InNRaw P th io M.nat j.1 α (ρ i)) →
      (∀ i : ℕ, i ≤ φ.ncode → M.ValRaw P th io M.nat Nt j.1 d α t (i : M.Num).1 (ρ i)) →
      (M.TrueAt P io F j.1 α (M.code φ) t ↔ M.TrC P th io tp F Pr j α φ ρ)
  | .mem v w, ρ, t, hρ, hv => by
    simp only [code, TrC]
    exact M.rel_val hd (v : M.Num) (w : M.Num) hα (hv v (CF.mem_left v w)) (hv w (CF.mem_right v w))
  | .lt v w, ρ, t, hρ, hv => by
    simp only [code, TrC]
    rw [M.hier_lt hd hPr]
    constructor
    · rintro ⟨-, a, b, va, vb, -, -, h⟩
      rw [M.val_unique hd va (hv v (CF.lt_left v w)), M.val_unique hd vb (hv w (CF.lt_right v w))] at h
      exact h
    · intro h
      exact ⟨hα, ρ v, ρ w, hv v (CF.lt_left v w), hv w (CF.lt_right v w), hρ v, hρ w, h⟩
  | .neg φ, ρ, t, hρ, hv => by
    simp only [code, TrC]
    rw [M.hier_neg hd, bridge hd hPr hα φ ρ t hρ (fun i hi => hv i (le_trans hi (CF.neg_le φ)))]
    exact ⟨fun h => h.2, fun h => ⟨hα, h⟩⟩
  | .and φ ψ, ρ, t, hρ, hv => by
    simp only [code, TrC]
    rw [M.hier_and hd, bridge hd hPr hα φ ρ t hρ (fun i hi => hv i (le_trans hi (CF.and_left φ ψ))),
      bridge hd hPr hα ψ ρ t hρ (fun i hi => hv i (le_trans hi (CF.and_right φ ψ)))]
    exact ⟨fun h => h.2, fun h => ⟨hα, h⟩⟩
  | .all v φ, ρ, t, hρ, hv => by
    simp only [code, TrC]
    rw [M.hier_all_ex hd]
    have hC : M.cAll (v : M.Num) (M.code φ) = M.code (.all v φ) := rfl
    have key : ∀ a t', M.InNRaw P th io M.nat j.1 α a →
        M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' (v : M.Num).1 a (M.cAll (v : M.Num) (M.code φ)).1 →
        (M.TrueAt P io F j.1 α (M.code φ) t' ↔
          M.TrC P th io tp F Pr j α φ (Function.update ρ v a)) := by
      intro a t' ha hag
      refine bridge hd hPr hα φ (Function.update ρ v a) t' (fun i => ?_) (fun i hi => ?_)
      · by_cases e : i = v
        · subst e
          simpa using ha
        · simpa [Function.update_of_ne e] using hρ i
      · have hiC : (i : M.Num) ≤ M.cAll (v : M.Num) (M.code φ) := by
          rw [hC]
          exact M.cast_le_code (le_trans hi (CF.all_le v φ))
        by_cases e : i = v
        · subst e
          simp only [Function.update_self]
          exact M.agree_same hag (by rw [hC]; exact M.cast_le_code (CF.all_var i φ))
        · rw [Function.update_of_ne e]
          exact M.agree_other hag hiC (fun e' => e (M.natCast_inj' _ _ e'))
            (hv i (le_trans hi (CF.all_le v φ)))
    constructor
    · rintro ⟨-, h⟩ a ha
      obtain ⟨t', hag, htr⟩ := h a ha
      exact (key a t' ha hag).mp htr
    · intro h
      refine ⟨hα, fun a ha => ?_⟩
      obtain ⟨t', hag⟩ := M.exists_upd hd ha t (v : M.Num).1 (M.cAll (v : M.Num) (M.code φ))
      exact ⟨t', hag, (key a t' ha hag).mpr (h a ha)⟩

/-- A sequence with prescribed values at the variables up to a standard number. -/
theorem exists_cfseq (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    {ρ : ℕ → V} (hρ : ∀ i, M.InNRaw P th io M.nat j.1 α (ρ i)) (n : ℕ) :
    ∃ t, ∀ i : ℕ, i ≤ n → M.ValRaw P th io M.nat Nt j.1 d α t (i : M.Num).1 (ρ i) := by
  have key : ∀ k : ℕ, ∃ t, ∀ i : ℕ, i < k → i ≤ n →
      M.ValRaw P th io M.nat Nt j.1 d α t (i : M.Num).1 (ρ i) := by
    intro k
    induction k with
    | zero => exact ⟨d, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    | succ k ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨t', hag⟩ := M.exists_upd hd (hρ k) t (k : M.Num).1 (n : M.Num)
      refine ⟨t', fun i hi hin => ?_⟩
      by_cases e : i = k
      · subst e
        exact M.agree_same hag (M.cast_le_cast hin)
      · exact M.agree_other hag (M.cast_le_cast hin) (fun e' => e (M.natCast_inj' _ _ e'))
          (ht i (by omega) hin)
  obtain ⟨t, ht⟩ := key (n + 1)
  exact ⟨t, fun i hi => ht i (by omega) hi⟩

/-- A code that is true under every sequence is true under every assignment of names. -/
theorem tr_of_true (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {α : V} (hα : M.mem (M.op α α) th) (φ : CF)
    (h : ∀ t, M.TrueAt P io F j.1 α (M.code φ) t) {ρ : ℕ → V}
    (hρ : ∀ i, M.InNRaw P th io M.nat j.1 α (ρ i)) : M.TrC P th io tp F Pr j α φ ρ := by
  obtain ⟨t, ht⟩ := M.exists_cfseq hd hρ φ.ncode
  exact (M.bridge hd hPr hα φ ρ t hρ ht).mp (h t)

end bridge

end Model

end NFUCut



/-!
# Phase 0, part 2: the axioms of a host for the level at a limit stage, in semantic form
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

section sforms

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem tr_imp {α : V} (A B : CF) (ρ : ℕ → V) :
    M.TrC P th io tp F Pr j α (A.imp B) ρ ↔
      (M.TrC P th io tp F Pr j α A ρ → M.TrC P th io tp F Pr j α B ρ) := by
  simp only [CF.imp, TrC]
  tauto

theorem tr_or {α : V} (A B : CF) (ρ : ℕ → V) :
    M.TrC P th io tp F Pr j α (A.or B) ρ ↔
      (M.TrC P th io tp F Pr j α A ρ ∨ M.TrC P th io tp F Pr j α B ρ) := by
  simp only [CF.or, TrC]
  tauto

theorem tr_iff {α : V} (A B : CF) (ρ : ℕ → V) :
    M.TrC P th io tp F Pr j α (A.iff B) ρ ↔
      (M.TrC P th io tp F Pr j α A ρ ↔ M.TrC P th io tp F Pr j α B ρ) := by
  simp only [CF.iff, TrC]
  tauto

theorem tr_ex {α : V} (v : ℕ) (c : CF) (ρ : ℕ → V) :
    M.TrC P th io tp F Pr j α (CF.ex v c) ρ ↔
      ∃ a, M.InNRaw P th io M.nat j.1 α a ∧ M.TrC P th io tp F Pr j α c (Function.update ρ v a) := by
  simp only [CF.ex, TrC]
  constructor
  · intro h
    by_contra hc
    exact h (fun a ha htr => hc ⟨a, ha, htr⟩)
  · rintro ⟨a, ha, htr⟩ h
    exact h a ha htr

/-- **Separation, in semantic form.** -/
theorem s_sep (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {κ : V} (hκ : M.mem (M.op κ κ) th)
    (hsep : ∀ a b φ : M.Num, a ≠ 0 → M.cAnd (M.cRel 0 0 a) φ + 1 ≤ b →
      ∀ t, M.TrueAt P io F j.1 κ (M.cSep a b φ) t)
    (ψ : CF) {ρ : ℕ → V} (hρ : ∀ i, M.InNRaw P th io M.nat j.1 κ (ρ i)) {a : V}
    (ha : M.InNRaw P th io M.nat j.1 κ a) :
    ∃ b, M.InNRaw P th io M.nat j.1 κ b ∧ ∀ y, M.InNRaw P th io M.nat j.1 κ y →
      (M.EpsStarRaw P th io M.nat j.1 tp F y b ↔
        (M.EpsStarRaw P th io M.nat j.1 tp F y a ∧
          M.TrC P th io tp F Pr j κ ψ (Function.update ρ 0 y))) := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ, A = ψ.ncode + 1 := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ, B = (CF.and (.mem 0 A) ψ).ncode + 1 := ⟨_, rfl⟩
  have hA0 : A ≠ 0 := by omega
  have hAB : A < B := by
    have := CF.mem_right 0 A
    have := CF.and_left (.mem 0 A) ψ
    omega
  have hψA : ψ.ncode < A := by omega
  have hcode : M.cSep (A : M.Num) (B : M.Num) (M.code ψ) =
      M.code (.all A (.ex B (.all 0 (.iff (.mem 0 B) (.and (.mem 0 A) ψ))))) := by
    simp [code, cSep, cEx, cIff, CF.ex, CF.iff]
  have hA : (A : M.Num) ≠ 0 := by exact_mod_cast hA0
  have hB : M.cAnd (M.cRel 0 0 (A : M.Num)) (M.code ψ) + 1 ≤ (B : M.Num) := by
    have e : M.cAnd (M.cRel 0 0 (A : M.Num)) (M.code ψ) = M.code (.and (.mem 0 A) ψ) := by
      simp [code]
    rw [e, M.code_eq, hBdef]
    exact le_of_eq (by push_cast; rfl)
  have htr := M.tr_of_true hd hPr hκ _ (fun t => by rw [← hcode]; exact hsep _ _ _ hA hB t)
    (ρ := ρ) hρ
  simp only [TrC] at htr
  have h1 := htr a ha
  rw [M.tr_ex] at h1
  obtain ⟨b, hb, h2⟩ := h1
  refine ⟨b, hb, fun y hy => ?_⟩
  have h3 := h2 y hy
  rw [M.tr_iff] at h3
  simp only [TrC] at h3
  have hB0 : B ≠ 0 := by omega
  have e1 : Function.update (Function.update (Function.update ρ A a) B b) 0 y 0 = y := by simp
  have e2 : Function.update (Function.update (Function.update ρ A a) B b) 0 y B = b := by
    simp [Function.update_apply, hB0]
  have e3 : Function.update (Function.update (Function.update ρ A a) B b) 0 y A = a := by
    simp [Function.update_apply, hA0, (Nat.ne_of_lt hAB)]
  rw [e1, e2, e3] at h3
  rw [h3]
  refine and_congr_right fun _ => M.tr_congr ψ _ _ (fun i hi => ?_)
  have hiA : i ≠ A := by omega
  have hiB : i ≠ B := by omega
  by_cases e : i = 0
  · subst e
    simp
  · simp [Function.update_apply, e, hiA, hiB]

/-- **Collection, in semantic form.** -/
theorem s_coll (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {κ : V} (hκ : M.mem (M.op κ κ) th)
    (hcoll : ∀ a b y z φ : M.Num, a ≠ y → a ≠ b → b ≠ y → b ≠ z → φ + 1 ≤ b →
      ∀ t, M.TrueAt P io F j.1 κ (M.cColl a b y z φ) t)
    (ψ : CF) (y z : ℕ) {ρ : ℕ → V} (hρ : ∀ i, M.InNRaw P th io M.nat j.1 κ (ρ i)) {a : V}
    (ha : M.InNRaw P th io M.nat j.1 κ a)
    (h : ∀ u, M.InNRaw P th io M.nat j.1 κ u → M.EpsStarRaw P th io M.nat j.1 tp F u a →
      ∃ v, M.InNRaw P th io M.nat j.1 κ v ∧
        M.TrC P th io tp F Pr j κ ψ (Function.update (Function.update ρ y u) z v)) :
    ∃ b, M.InNRaw P th io M.nat j.1 κ b ∧
      ∀ u, M.InNRaw P th io M.nat j.1 κ u → M.EpsStarRaw P th io M.nat j.1 tp F u a →
        ∃ v, M.InNRaw P th io M.nat j.1 κ v ∧ M.EpsStarRaw P th io M.nat j.1 tp F v b ∧
          M.TrC P th io tp F Pr j κ ψ (Function.update (Function.update ρ y u) z v) := by
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ, B = ψ.ncode + y + z + 1 := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ, A = B + 1 := ⟨_, rfl⟩
  have hAy : A ≠ y := by omega
  have hAB : A ≠ B := by omega
  have hBy : B ≠ y := by omega
  have hBz : B ≠ z := by omega
  have hAz : A ≠ z := by omega
  have hcode : M.cColl (A : M.Num) (B : M.Num) (y : M.Num) (z : M.Num) (M.code ψ) =
      M.code (.all A (CF.imp (.all y (CF.imp (.mem y A) (CF.ex z ψ)))
        (CF.ex B (.all y (CF.imp (.mem y A) (CF.ex z (.and (.mem z B) ψ))))))) := by
    simp [code, cColl, cEx, cImp, CF.ex, CF.imp]
  have c1 : (A : M.Num) ≠ (y : M.Num) := by exact_mod_cast hAy
  have c2 : (A : M.Num) ≠ (B : M.Num) := by exact_mod_cast hAB
  have c3 : (B : M.Num) ≠ (y : M.Num) := by exact_mod_cast hBy
  have c4 : (B : M.Num) ≠ (z : M.Num) := by exact_mod_cast hBz
  have c5 : M.code ψ + 1 ≤ (B : M.Num) := by
    rw [M.code_eq]
    have : ψ.ncode + 1 ≤ B := by omega
    have h' := M.cast_le_cast this
    simpa using h'
  have htr := M.tr_of_true hd hPr hκ _
    (fun t => by rw [← hcode]; exact hcoll _ _ _ _ _ c1 c2 c3 c4 c5 t) (ρ := ρ) hρ
  simp only [TrC] at htr
  have h1 := htr a ha
  rw [M.tr_imp] at h1
  have key : ∀ (ρ' : ℕ → V) (u v : V), (∀ i, i ≤ ψ.ncode → ρ' i = ρ i) →
      (M.TrC P th io tp F Pr j κ ψ (Function.update (Function.update ρ' y u) z v) ↔
        M.TrC P th io tp F Pr j κ ψ (Function.update (Function.update ρ y u) z v)) := by
    intro ρ' u v hρ'
    refine M.tr_congr ψ _ _ (fun i hi => ?_)
    simp only [Function.update_apply]
    split_ifs
    · rfl
    · rfl
    · exact hρ' i hi
  have h2 : M.TrC P th io tp F Pr j κ (.all y (CF.imp (.mem y A) (CF.ex z ψ)))
      (Function.update ρ A a) := by
    simp only [TrC]
    intro u hu
    rw [M.tr_imp, M.tr_ex]
    simp only [TrC]
    have e1 : Function.update (Function.update ρ A a) y u y = u := by simp
    have e2 : Function.update (Function.update ρ A a) y u A = a := by
      simp [Function.update_apply, hAy]
    rw [e1, e2]
    intro hua
    obtain ⟨v, hv, hψ⟩ := h u hu hua
    refine ⟨v, hv, (key (Function.update ρ A a) u v (fun i hi => ?_)).mpr hψ⟩
    have : i ≠ A := by omega
    simp [Function.update_apply, this]
  have h3 := h1 h2
  rw [M.tr_ex] at h3
  obtain ⟨b, hb, h4⟩ := h3
  refine ⟨b, hb, fun u hu hua => ?_⟩
  simp only [TrC] at h4
  have h5 := h4 u hu
  rw [M.tr_imp, M.tr_ex] at h5
  simp only [TrC] at h5
  have e1 : Function.update (Function.update (Function.update ρ A a) B b) y u y = u := by simp
  have e2 : Function.update (Function.update (Function.update ρ A a) B b) y u A = a := by
    simp [Function.update_apply, hAy, hAB]
  rw [e1, e2] at h5
  obtain ⟨v, hv, h6, h7⟩ := h5 hua
  have e3 : Function.update (Function.update (Function.update (Function.update ρ A a) B b) y u) z v z
      = v := by simp
  have e4 : Function.update (Function.update (Function.update (Function.update ρ A a) B b) y u) z v B
      = b := by simp [Function.update_apply, hBz, hBy]
  rw [e3, e4] at h6
  refine ⟨v, hv, h6, (key (Function.update (Function.update ρ A a) B b) u v (fun i hi => ?_)).mp h7⟩
  have hiA : i ≠ A := by omega
  have hiB : i ≠ B := by omega
  simp [Function.update_apply, hiA, hiB]

/-- **Every set that has a member has a least member**, in semantic form. -/
theorem s_least (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {κ : V} (hκ : M.mem (M.op κ κ) th)
    (hwl : ∀ a x y : M.Num, a ≠ x → x ≠ y → a ≠ y →
      ∀ t, M.TrueAt P io F j.1 κ (M.cWLeast a x y) t)
    {a : V} (ha : M.InNRaw P th io M.nat j.1 κ a)
    (hne : ∃ x, M.InNRaw P th io M.nat j.1 κ x ∧ M.EpsStarRaw P th io M.nat j.1 tp F x a) :
    ∃ x, M.InNRaw P th io M.nat j.1 κ x ∧ M.EpsStarRaw P th io M.nat j.1 tp F x a ∧
      ∀ y, M.InNRaw P th io M.nat j.1 κ y → M.EpsStarRaw P th io M.nat j.1 tp F y a →
        ¬ M.Lt P j.1 tp F Pr y x := by
  have hcode : M.cWLeast 0 1 2 =
      M.code (.all 0 (CF.imp (CF.ex 1 (.mem 1 0))
        (CF.ex 1 (.and (.mem 1 0) (.all 2 (CF.imp (.mem 2 0) (.neg (.lt 2 1)))))))) := by
    simp [code, cWLeast, cEx, cImp, CF.ex, CF.imp]
  have n01 : (0 : M.Num) ≠ 1 := by
    have : ((0 : ℕ) : M.Num) ≠ ((1 : ℕ) : M.Num) := by exact_mod_cast (by decide : (0 : ℕ) ≠ 1)
    simpa using this
  have n12 : (1 : M.Num) ≠ 2 := by
    have : ((1 : ℕ) : M.Num) ≠ ((2 : ℕ) : M.Num) := by exact_mod_cast (by decide : (1 : ℕ) ≠ 2)
    simpa using this
  have n02 : (0 : M.Num) ≠ 2 := by
    have : ((0 : ℕ) : M.Num) ≠ ((2 : ℕ) : M.Num) := by exact_mod_cast (by decide : (0 : ℕ) ≠ 2)
    simpa using this
  have htr := M.tr_of_true hd hPr hκ _
    (fun t => by rw [← hcode]; exact hwl 0 1 2 n01 n12 n02 t) (ρ := fun _ => a) (fun _ => ha)
  simp only [TrC] at htr
  have h1 := htr a ha
  rw [M.tr_imp, M.tr_ex, M.tr_ex] at h1
  simp only [TrC] at h1
  obtain ⟨x, hx, h2, h3⟩ := h1 (by
    obtain ⟨x, hx, hxa⟩ := hne
    exact ⟨x, hx, by simpa [Function.update_apply] using hxa⟩)
  refine ⟨x, hx, by simpa [Function.update_apply] using h2, fun y hy hya => ?_⟩
  have h4 := h3 y hy
  rw [M.tr_imp] at h4
  simp only [TrC] at h4
  have h5 := h4 (by simpa [Function.update_apply] using hya)
  simpa [Function.update_apply] using h5

/-- Membership implies the canonical order. -/
theorem eps_lt (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {x y : V}
    (hy : M.SimRaw P j.1 tp F y y) (h : M.EpsStarRaw P th io M.nat j.1 tp F x y) :
    M.Lt P j.1 tp F Pr x y := by
  have hth := hd.hth
  have hx := M.epsStar_left hd h
  obtain ⟨y0, cy, sy⟩ := M.exists_can hd hPr hy
  obtain ⟨x0, cx, sx⟩ := M.exists_can hd hPr hx
  obtain ⟨x', hs, he⟩ := M.epsStar_congr hd hx sy h
  obtain ⟨ρy, -, ry0, -, hρy, -⟩ := M.sim_names hd cy.1
  have hx'in := M.eps_inN_rank hd ry0 he
  obtain ⟨ρx', rx', lt', ne'⟩ := M.inN_rank hx'in
  obtain ⟨ρx, -, rx0, -, hρx, -⟩ := M.sim_names hd cx.1
  have hpr : M.mem (M.op x0 x') Pr := cx.2 x' (M.sim_trans hd (M.sim_symm hd sx) hs)
  have hle := M.pr_rank_le hd hPr rx0 rx' hpr
  have hlt : M.mem (M.op ρx ρy) th := hth.trans _ _ _ hle lt'
  have hne : ρx ≠ ρy := fun e => by
    rw [e] at hle
    exact ne' (hth.antisymm _ _ lt' hle)
  refine ⟨x0, y0, cx, cy, sx, sy, M.pr_of_lt hPr rx0 ry0 hlt hne, fun hc => ?_⟩
  have hge := M.pr_rank_le hd hPr ry0 rx0 hc
  exact hne (hth.antisymm _ _ hlt hge)

/-- What is before a set with a name of rank below `γ` has a name of rank below `γ`. -/
theorem lt_inN (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {γ a b : V}
    (ha : M.InNRaw P th io M.nat j.1 γ a) (h : M.Lt P j.1 tp F Pr b a) :
    ∃ b0, M.InNRaw P th io M.nat j.1 γ b0 ∧ M.SimRaw P j.1 tp F b b0 := by
  have hth := hd.hth
  obtain ⟨b0, a0, cb, ca, sb, sa, pp, -⟩ := h
  have ha0 := M.can_inN hd hPr ha ca sa
  obtain ⟨ρa, ra0, lta, nea⟩ := M.inN_rank ha0
  obtain ⟨ρb, -, rb0, -, hρb, -⟩ := M.sim_names hd cb.1
  have hle := M.pr_rank_le hd hPr rb0 ra0 pp
  refine ⟨b0, M.rank_inN rb0 (hth.trans _ _ _ hle lta) (fun e => ?_), sb⟩
  rw [e] at hle
  exact nea (hth.antisymm _ _ lta hle)

end sforms

end Model

end NFUCut



/-!
# Phase 0, part 3: the levels at the least stages that are not small are closed

Collection into such a level for formulas of a later stage (`next_coll_at`, `s_kcoll`), names
for the levels (`IsLevQ`, `lev_epsStar`), and the semantic forms of transitivity, of closure
under subsets (`k_sub`, from `next_absorb`) and of the covering of initial segments of the
canonical order (`cover_lim`).
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

section collat

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {ν Sg : V}
variable {q1 : V}

/-- **Collection into the least stage that is not small, for formulas of a later stage.** Let
`κ` be the least stage that is not `ν`-small and `lam ≥ κ` a stage with two stages above it. If
for every member `y₀` of the set denoted by a name `a` of rank below `κ` the formula `c`,
evaluated at the stage `lam`, has a witness of rank below `κ` for the variable `z`, then there
is a stage `γ` below `κ` such that the witnesses can be taken of rank below `γ`. -/
theorem next_coll_at (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {κ lam : V}
    (hκ : M.IsNext P th Sg j ν κ) {σ' δ a t : V} (hκlam : M.mem (M.op κ lam) th)
    (hlamσ' : M.mem (M.op lam σ') th) (nelam : lam ≠ σ') (hσ'δ : M.mem (M.op σ' δ) th) (neσ' : σ' ≠ δ)
    (c y z : M.Num) (ha : M.InNRaw P th io M.nat j.1 κ a)
    (hyp : ∀ y0, M.InNRaw P th io M.nat j.1 κ y0 → M.EpsStarRaw P th io M.nat j.1 tp F y0 a → ∀ t1, M.AgreeRaw P th io M.nat Nt j.1 d M.adG lam t t1 y.1 y0 c.1 →
      ∃ z0, M.InNRaw P th io M.nat j.1 κ z0 ∧ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F lam c.1 z.1 t1 z0) :
    ∃ γ, M.mem (M.op γ κ) th ∧ γ ≠ κ ∧
      ∀ y0, M.InNRaw P th io M.nat j.1 κ y0 → M.EpsStarRaw P th io M.nat j.1 tp F y0 a → ∀ t1, M.AgreeRaw P th io M.nat Nt j.1 d M.adG lam t t1 y.1 y0 c.1 →
        ∃ z0, M.InNRaw P th io M.nat j.1 γ z0 ∧ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F lam c.1 z.1 t1 z0 := by
  have hth := hd.hth
  obtain ⟨hκκ, hns, hsm⟩ := hκ
  have hlam := (hth.fld _ _ hκlam).2
  have hκσ' : M.mem (M.op κ σ') th := hth.trans _ _ _ hκlam hlamσ'
  have neκ : κ ≠ σ' := M.wo_ne_of_le_lt hth hκlam hlamσ' nelam
  have hσ' := (hth.fld _ _ hκσ').2
  obtain ⟨hνκ, hνκne⟩ : M.mem (M.op ν κ) th ∧ ν ≠ κ := by
    obtain ⟨βa, ra, lta, nea⟩ := M.inN_rank ha
    obtain ⟨ρ2, b2, h1, h2⟩ := hsm βa lta nea
    obtain ⟨g1, g2, -⟩ := M.gen_lt hd hSg h2
    have hρ2 := (hth.fld _ _ h1).2
    rcases M.wo_total hth hρ2 hκκ with h | h
    · exact ⟨hth.trans _ _ _ g1 h, M.wo_ne_of_lt_le hth g1 g2 h⟩
    · exact (hns ⟨ρ2, b2, h, h2⟩).elim
  have hνδ : M.mem (M.op ν δ) th := hth.trans _ _ _ (hth.trans _ _ _ hνκ hκσ') hσ'δ
  obtain ⟨oκ, hoκ⟩ := M.exists_mark hd hq hlam
  have hdσ' : M.InNRaw P th io M.nat j.1 σ' d := M.d_inN hd hκσ' neκ
  -- the carrier name
  obtain ⟨c1, hc1⟩ : ∃ c1 : M.Num, c1 = c + 1 := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c2 : M.Num, c2 = c1 + 1 := ⟨_, rfl⟩
  obtain ⟨g, -, hg0⟩ := M.comp (σW [(0, 4), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7)])
    (Fml.ex 326 (Fml.ex 327 (.and (fPr 0 326 327) (.and (.mem 326 27) (Fml.or (.and (fLeN 326 301) (fVal 250 340 326 327)) (Fml.or (.and (.eq 326 345) (.eq 327 346)) (.and (.eq 326 347) (.eq 327 348)))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 250 lam) 301 c.1) 340 t) 345 c1.1) 346 a) 347 c2.1) 348 oκ)
  have hg1 : ∀ q, M.mem q g ↔ ∃ i e, q = M.op i e ∧ M.mem i M.nat ∧
      (((∃ x, M.mem x M.nat ∧ M.mem (M.trip i x c.1) M.adG) ∧ M.ValRaw P th io M.nat Nt j.1 d lam t i e) ∨
        (i = c1.1 ∧ e = a) ∨ (i = c2.1 ∧ e = oκ)) := by
    intro q
    rw [hg0 q]
    simp [Sat, M.sat_or, M.sat_ex, M.sat_fPr', M.sat_fVal, M.sat_fLeN, Function.update_apply]
  have hgs : ∀ (i : M.Num) (e : V), M.mem (M.op i.1 e) g ↔
      ((i ≤ c ∧ M.ValRaw P th io M.nat Nt j.1 d lam t i.1 e) ∨ (i = c1 ∧ e = a) ∨ (i = c2 ∧ e = oκ)) := by
    intro i e
    constructor
    · intro h
      obtain ⟨i', e'', eq, -, h'⟩ := (hg1 _).mp h
      obtain ⟨e1, e2⟩ := M.op_inj eq
      rw [← e1, ← e2] at h'
      rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨(M.leRaw_iff M.adG_spec i c).mp h1, h2⟩
      · exact Or.inr (Or.inl ⟨Subtype.ext h1, h2⟩)
      · exact Or.inr (Or.inr ⟨Subtype.ext h1, h2⟩)
    · intro h
      refine (hg1 _).mpr ⟨i.1, e, rfl, i.2, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨(M.leRaw_iff M.adG_spec i c).mpr h1, h2⟩
      · exact Or.inr (Or.inl ⟨congrArg Subtype.val h1, h2⟩)
      · exact Or.inr (Or.inr ⟨congrArg Subtype.val h1, h2⟩)
  have haσ' : M.InNRaw P th io M.nat j.1 σ' a := M.inN_mono hd ha hκσ'
  have hoκσ' : M.InNRaw P th io M.nat j.1 σ' oκ := M.rank_inN (M.mark_rank hq hoκ) hlamσ' nelam
  have hvalσ' : ∀ {i e : V}, M.ValRaw P th io M.nat Nt j.1 d lam t i e → M.InNRaw P th io M.nat j.1 σ' e := by
    intro i e hv
    rcases M.val_cases hv with h | h
    · exact M.inN_mono hd h hlamσ'
    · rw [h]
      exact hdσ'
  have nc1 : ¬ c1 ≤ c := by
    rw [hc1]
    exact M.not_succ_le c
  have nc2 : ¬ c2 ≤ c := by
    rw [hc2, hc1]
    exact fun h => M.not_succ_le c (le_trans (M.le_add_one _) h)
  have nc12 : c1 ≠ c2 := by
    rw [hc2]
    exact fun e => M.not_succ_le c1 (le_of_eq e.symm)
  obtain ⟨s, hsR, hs⟩ := M.exists_seq_vals hd (σ := σ') (g := g) (c2 + 1)
    (fun k hk => by
      have hk2 : k ≤ c2 := M.le_of_succ_le_succ hk
      rcases M.eq_or_succ_le hk2 with e | e
      · exact ⟨oκ, hoκσ', (hgs k oκ).mpr (Or.inr (Or.inr ⟨e, rfl⟩))⟩
      · rw [hc2] at e
        have hk1 : k ≤ c1 := M.le_of_succ_le_succ e
        rcases M.eq_or_succ_le hk1 with e' | e'
        · exact ⟨a, haσ', (hgs k a).mpr (Or.inr (Or.inl ⟨e', rfl⟩))⟩
        · rw [hc1] at e'
          have hk0 : k ≤ c := M.le_of_succ_le_succ e'
          obtain ⟨e0, ve0⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) lam t k.1
          exact ⟨e0, hvalσ' ve0, (hgs k e0).mpr (Or.inl ⟨hk0, ve0⟩)⟩)
    (fun k e hk hge => by
      rcases (hgs k e).mp hge with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
      · exact hvalσ' h2
      · rw [h2]
        exact haσ'
      · rw [h2]
        exact hoκσ')
  obtain ⟨b, hb⟩ := M.nameOf_exists hd hσ' hsR c2
  have hbδ : M.InNRaw P th io M.nat j.1 δ b := M.rank_inN (M.nameOf_rank hb) hσ'δ neσ'
  have hbν : ¬ M.InNRaw P th io M.nat j.1 ν b := by
    intro h
    obtain ⟨β0, r0, lt0, ne0⟩ := M.inN_rank h
    have e0 := M.rank_unique hd r0 (M.nameOf_rank hb)
    rw [e0] at lt0 ne0
    exact ne0 (hth.antisymm _ _ lt0 (hth.trans _ _ _ hνκ hκσ'))
  obtain ⟨N, Oc, H, PiS, γ, hN, cd, hH⟩ := M.exists_hull_cond hd hPr hq hNu hSg hνδ hbδ
  have hbN := M.hull_gen hN hbδ
  have hvalN : ∀ (i : M.Num) (e : V), i ≤ c2 → M.ValRaw P th io M.nat Nt j.1 d σ' s i.1 e → M.mem e N := fun i e hi hv =>
    cd.hcl.2.1 b σ' c2.1 s i.1 e hbN ((M.nameR_iff c2).mpr hb) i.2
      ((M.leRaw_iff M.adG_spec i c2).mpr hi) hv
  have hc1c2 : c1 ≤ c2 := by
    rw [hc2]
    exact M.le_add_one c1
  have hcc1 : c ≤ c1 := by
    rw [hc1]
    exact M.le_add_one c
  have haN : M.mem a N := by
    obtain ⟨e, hge, hv⟩ := hs c1 (add_le_add hc1c2 (le_refl 1))
    rcases (hgs c1 e).mp hge with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h1, -⟩
    · exact (nc1 h1).elim
    · rw [← h2]
      exact hvalN c1 e hc1c2 hv
    · exact (nc12 h1).elim
  have hoκN : M.mem oκ N := by
    obtain ⟨e, hge, hv⟩ := hs c2 (le_refl _)
    rcases (hgs c2 e).mp hge with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
    · exact (nc2 h1).elim
    · exact (nc12 h1.symm).elim
    · rw [← h2]
      exact hvalN c2 e (le_refl _) hv
  have htN : ∀ (i : M.Num) (e : V), i ≤ c → M.ValRaw P th io M.nat Nt j.1 d lam t i.1 e → M.mem e N := by
    intro i e hi hv
    obtain ⟨e', hge, hv'⟩ := hs i (add_le_add (le_trans hi (le_trans hcc1 hc1c2)) (le_refl 1))
    rcases (hgs i e').mp hge with ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [M.val_unique hd hv h2]
      exact hvalN i e' (le_trans hi (le_trans hcc1 hc1c2)) hv'
    · rw [h1] at hi
      exact (nc1 hi).elim
    · rw [h1] at hi
      exact (nc2 hi).elim
  -- the collapse is below `κ`
  obtain ⟨bt, pb⟩ := M.pi_tot cd hbN
  have hgenγ := M.hull_collapse cd hSg hN hνδ hbδ hbν hH pb
  have hγ := (M.coll_dom cd.hH hH).2.2
  have hγκ : M.mem (M.op γ κ) th ∧ γ ≠ κ := by
    rcases M.wo_total hth hγ hκκ with h | h
    · refine ⟨h, fun e => hns ⟨γ, bt, ?_, hgenγ⟩⟩
      rw [← e]
      exact hγ
    · exact (hns ⟨γ, bt, h, hgenγ⟩).elim
  have hκδ : M.mem (M.op κ δ) th := hth.trans _ _ _ hκσ' hσ'δ
  have neκδ : κ ≠ δ := M.wo_ne_of_le_lt hth hκσ' hσ'δ neσ'
  -- the names of rank at most a stage below `κ` whose marker is in `N` are in `N`
  have hlow : ∀ {ζ oζ x β' : V}, M.mem (M.quad j.1 ζ q1 oζ) P → M.mem oζ N →
      M.mem (M.op ζ κ) th → ζ ≠ κ → M.RankIs P io M.nat j.1 β' x → M.mem (M.op β' ζ) th → M.mem x N := by
    intro ζ oζ x β' hoζ hoζN ltζ neζ rx hβ'
    obtain ⟨ρ2, b2, h1, h2⟩ := hsm ζ ltζ neζ
    have hρ2 := (hth.fld _ _ h1).2
    have hρ2κ : M.mem (M.op ρ2 κ) th := by
      rcases M.wo_total hth hρ2 hκκ with h | h
      · exact h
      · exact (hns ⟨ρ2, b2, h, h2⟩).elim
    exact M.closed_small hd hPr hq hSg cd.hcl (fun x hx => M.hull_base hd hN hνδ hx) cd.hdN hoζ
      hoζN ⟨ρ2, b2, h1, hth.trans _ _ _ hρ2κ hκδ, M.wo_ne_of_le_lt hth hρ2κ hκδ neκδ, h2⟩ rx hβ'
  have hbelow : ∀ {w ζ : V}, M.mem w N → M.RankIs P io M.nat j.1 ζ w → M.mem (M.op ζ κ) th → ζ ≠ κ →
      M.InNRaw P th io M.nat j.1 γ w := by
    intro w ζ hwN rw' ltζ neζ
    obtain ⟨ltδ, neδ, hζO, oζ, hoζ, hoζN⟩ := M.cond_rank cd hwN rw'
    have hζ := (hth.fld _ _ ltζ).1
    have hid : M.mem (M.op ζ ζ) H := M.coll_id hth cd.hH hζ (fun β' h' => by
      obtain ⟨o, ho⟩ := M.exists_mark hd hq (hth.fld _ _ h').1
      exact (cd.hO β').mpr (Or.inr ⟨o, ho, hlow hoζ hoζN ltζ neζ (M.mark_rank hq ho) h'⟩))
    obtain ⟨l1, l2⟩ := M.coll_mono hth cd.hH hid hH ltδ neδ
    exact M.rank_inN rw' l1 l2
  refine ⟨γ, hγκ.1, hγκ.2, fun y0 hy0 hy0a t1 hag1 => ?_⟩
  obtain ⟨y1, hsy, ey1⟩ := hy0a
  obtain ⟨βa, ra, lta, nea⟩ := M.inN_rank ha
  have hy1a := M.eps_inN_rank hd ra ey1
  have hy1κ := M.inN_mono hd hy1a lta
  have hy1lam := M.inN_mono hd hy1κ hκlam
  obtain ⟨-, -, -, oa, hoa, hoaN⟩ := M.cond_rank cd haN ra
  obtain ⟨β1, ry1, lt1, -⟩ := M.inN_rank hy1a
  have hy1N : M.mem y1 N := hlow hoa hoaN lta nea ry1 lt1
  obtain ⟨τ, hagτ⟩ := M.exists_upd hd hy1lam t y.1 c
  have hτN : ∀ i : M.Num, i ≤ c → ∀ e, M.ValRaw P th io M.nat Nt j.1 d lam τ i.1 e → M.mem e N := by
    intro i hi e hv
    by_cases e1 : i = y
    · rw [e1] at hv hi
      rw [M.val_unique hd hv (M.agree_same hagτ hi)]
      exact hy1N
    · obtain ⟨e0, ve0⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) lam t i.1
      rw [M.val_unique hd hv (M.agree_other hagτ hi e1 ve0)]
      exact htN i e0 hi ve0
  obtain ⟨z0, hz0, htu0⟩ := hyp y1 hy1κ ⟨y1, M.inN_refl hd hy1κ, ey1⟩ τ hagτ
  have hz0lam := M.inN_mono hd hz0 hκlam
  obtain ⟨w, hlw, htuw⟩ := M.exists_lw_pos hd hPr c z ⟨z0, hz0lam, htu0⟩
  have hwN : M.mem w N := cd.hcl.2.2.2.2.1 lam c.1 z.1 τ w
    (M.cond_stage cd ((cd.hO lam).mpr (Or.inr ⟨oκ, hoκ, hoκN⟩))) c.2 z.2
    (fun i e hi hle hv => hτN ⟨i, hi⟩ ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ c).mp hle) e hv) hlw
  have hwlam := hlw.1
  have hpr : M.mem (M.op w z0) Pr := by
    rcases hlw.2 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h z0 hz0lam htu0
    · exact (h htuw).elim
  obtain ⟨ζ, rw', -, -⟩ := M.inN_rank hwlam
  obtain ⟨ζ0, rz0, ltζ0, neζ0⟩ := M.inN_rank hz0
  have hle := M.pr_rank_le hd hPr rw' rz0 hpr
  have ltζ : M.mem (M.op ζ κ) th := hth.trans _ _ _ hle ltζ0
  have neζ : ζ ≠ κ := fun e => by
    rw [e] at hle
    exact neζ0 (hth.antisymm _ _ ltζ0 hle)


  refine ⟨w, hbelow hwN rw' ltζ neζ, (M.tu_seq_sim hd c z hlam hwlam (fun i hi => ?_)).mp htuw⟩
  by_cases e1 : i = y
  · rw [e1] at hi ⊢
    exact ⟨y1, y0, M.agree_same hagτ hi, M.agree_same hag1 hi, M.sim_symm hd hsy⟩
  · obtain ⟨e0, ve0⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) lam t i.1
    exact ⟨e0, e0, M.agree_other hagτ hi e1 ve0, M.agree_other hag1 hi e1 ve0,
      M.val_sim_refl hd hlam ve0⟩



/-- **Collection into the least stage that is not small**, for a formula of a later stage, in
semantic form. -/
theorem s_kcoll (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {κ lam σ' δ : V}
    (hκ : M.IsNext P th Sg j ν κ) (hκlam : M.mem (M.op κ lam) th)
    (hlamσ' : M.mem (M.op lam σ') th) (nelam : lam ≠ σ') (hσ'δ : M.mem (M.op σ' δ) th) (neσ' : σ' ≠ δ)
    (ψ : CF) (y z : ℕ) {ρ : ℕ → V} (hρ : ∀ i, M.InNRaw P th io M.nat j.1 lam (ρ i)) {a : V}
    (ha : M.InNRaw P th io M.nat j.1 κ a)
    (h : ∀ u, M.InNRaw P th io M.nat j.1 κ u → M.EpsStarRaw P th io M.nat j.1 tp F u a →
      ∃ v, M.InNRaw P th io M.nat j.1 κ v ∧
        M.TrC P th io tp F Pr j lam ψ (Function.update (Function.update ρ y u) z v)) :
    ∃ γ, M.mem (M.op γ κ) th ∧ γ ≠ κ ∧
      ∀ u, M.InNRaw P th io M.nat j.1 κ u → M.EpsStarRaw P th io M.nat j.1 tp F u a →
        ∃ v, M.InNRaw P th io M.nat j.1 γ v ∧
          M.TrC P th io tp F Pr j lam ψ (Function.update (Function.update ρ y u) z v) := by
  have hlam := (hd.hth.fld _ _ hκlam).2
  obtain ⟨t, ht⟩ := M.exists_cfseq hd hρ ψ.ncode
  have val1 : ∀ {u t1 : V}, M.InNRaw P th io M.nat j.1 lam u →
      M.AgreeRaw P th io M.nat Nt j.1 d M.adG lam t t1 (y : M.Num).1 u (M.code ψ).1 →
      ∀ i : ℕ, i ≤ ψ.ncode →
        M.ValRaw P th io M.nat Nt j.1 d lam t1 (i : M.Num).1 (Function.update ρ y u i) := by
    intro u t1 hu hag i hi
    by_cases e : i = y
    · subst e
      simp only [Function.update_self]
      exact M.agree_same hag (M.cast_le_code hi)
    · rw [Function.update_of_ne e]
      exact M.agree_other hag (M.cast_le_code hi) (fun e' => e (M.natCast_inj' _ _ e')) (ht i hi)
  have key : ∀ {u t1 v : V}, M.InNRaw P th io M.nat j.1 lam u → M.InNRaw P th io M.nat j.1 lam v →
      M.AgreeRaw P th io M.nat Nt j.1 d M.adG lam t t1 (y : M.Num).1 u (M.code ψ).1 →
      (M.TrueUpdR P th io M.nat Nt j.1 d M.adG F lam (M.code ψ).1 (z : M.Num).1 t1 v ↔
        M.TrC P th io tp F Pr j lam ψ (Function.update (Function.update ρ y u) z v)) := by
    intro u t1 v hu hv hag
    obtain ⟨t2, hag2⟩ := M.exists_upd hd hv t1 (z : M.Num).1 (M.code ψ)
    rw [M.trueUpd_iff hd (M.code ψ) (z : M.Num) hag2]
    refine M.bridge hd hPr hlam ψ _ t2 (fun i => ?_) (fun i hi => ?_)
    · simp only [Function.update_apply]
      split_ifs
      · exact hv
      · exact hu
      · exact hρ i
    · by_cases e : i = z
      · subst e
        simp only [Function.update_self]
        exact M.agree_same hag2 (M.cast_le_code hi)
      · rw [Function.update_of_ne e]
        exact M.agree_other hag2 (M.cast_le_code hi) (fun e' => e (M.natCast_inj' _ _ e'))
          (val1 hu hag i hi)
  obtain ⟨γ, g1, g2, hγ⟩ := M.next_coll_at hd hPr hq hNu hSg hκ hκlam hlamσ' nelam hσ'δ neσ'
    (M.code ψ) (y : M.Num) (z : M.Num) ha
    (fun y0 hy0 hy0a t1 hag => by
      have hy0lam := M.inN_mono hd hy0 hκlam
      obtain ⟨v, hv, hψ⟩ := h y0 hy0 hy0a
      exact ⟨v, hv, (key hy0lam (M.inN_mono hd hv hκlam) hag).mpr hψ⟩)
  refine ⟨γ, g1, g2, fun u hu hua => ?_⟩
  have hulam := M.inN_mono hd hu hκlam
  obtain ⟨t1, hag⟩ := M.exists_upd hd hulam t (y : M.Num).1 (M.code ψ)
  obtain ⟨z0, hz0, htu⟩ := hγ u hu hua t1 hag
  have hz0lam := M.inN_mono hd (M.inN_mono hd hz0 g1) hκlam
  exact ⟨z0, hz0, (key hulam hz0lam hag).mp htu⟩

/-- **Closure under subsets.** A set all of whose members are members of a set with a name of
rank below the least stage `κ` that is not `ν`-small has a name of rank below `κ`. -/
theorem k_sub (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {κ lam δ x y : V}
    (hκ : M.IsNext P th Sg j ν κ)
    (hlamδ : M.mem (M.op lam δ) th) (nelam : lam ≠ δ)
    (hx : M.InNRaw P th io M.nat j.1 lam x) (hy : M.InNRaw P th io M.nat j.1 κ y)
    (hsub : ∀ z, M.EpsStarRaw P th io M.nat j.1 tp F z x → M.EpsStarRaw P th io M.nat j.1 tp F z y) :
    ∃ x', M.InNRaw P th io M.nat j.1 κ x' ∧ M.SimRaw P j.1 tp F x x' := by
  obtain ⟨σ, rx, ltσ, neσ⟩ := M.inN_rank hx
  obtain ⟨β, ry, ltβ, neβ⟩ := M.inN_rank hy
  refine M.next_absorb hd hPr hq hNu hSg hκ rx ltσ neσ hlamδ nelam ltβ neβ (fun z hz => ?_)
  have hzz : M.SimRaw P j.1 tp F z z := M.inN_refl hd (M.eps_inN_rank hd rx hz)
  obtain ⟨z', hs, he⟩ := hsub z ⟨z, hzz, hz⟩
  exact ⟨z', M.eps_inN_rank hd ry he, hs⟩

end collat

section levels

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- A code that is true under every sequence. -/
noncomputable def cTop : M.Num := M.cNeg (M.cAnd (M.cRel 0 0 0) (M.cNeg (M.cRel 0 0 0)))

theorem true_cTop (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) (s : V) : M.TrueAt P io F j.1 α M.cTop s := by
  unfold cTop
  rw [M.hier_neg hd, M.hier_and hd, M.hier_neg hd]
  exact ⟨hα, fun h => h.2.2.2 h.2.1⟩

/-- `q0` is the pair of the true formula and a parameter. The names `(α, q0)` denote the
levels. -/
def IsLevQ (P io : V) (j : M.Num) (q0 : V) : Prop :=
  ∃ f u, M.mem (M.op M.cTop.1 f) io ∧ M.mem (M.quad j.1 f u q0) P

theorem exists_levQ (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) :
    ∃ q0, M.IsLevQ P io j q0 := by
  obtain ⟨f, hf⟩ := hd.io_tot M.cTop
  obtain ⟨α0, f0, u0, q0', h1, h2, -⟩ := hd.d_spec
  have hu : M.mem (M.op j.1 u0) R := (hd.hP.dom _ _ _ _ h2).2.2.1
  obtain ⟨q, hq⟩ := hd.hP.tot j hd.hj f u0 (hd.io_dom _ _ hf).2 hu
  exact ⟨q, f, u0, hf, hq⟩

theorem lev_name (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q0 α : V}
    (hq0 : M.IsLevQ P io j q0) (hα : M.mem (M.op α α) th) : ∃ b, M.mem (M.quad j.1 α q0 b) P := by
  obtain ⟨f, u, hf, hq⟩ := hq0
  exact hd.hP.tot j hd.hj α q0 (hd.th_rung α α hα).1 (hd.hP.dom _ _ _ _ hq).2.2.2

theorem lev_rank (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q0 α b : V}
    (hq0 : M.IsLevQ P io j q0) (hb : M.mem (M.quad j.1 α q0 b) P) :
    M.RankIs P io M.nat j.1 α b := by
  obtain ⟨f, u, hf, hq⟩ := hq0
  exact ⟨f, u, q0, hb, hq, _, (hd.io_dom _ _ hf).1, hf⟩

theorem lev_eps (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q0 α b : V}
    (hq0 : M.IsLevQ P io j q0) (hα : M.mem (M.op α α) th) (hb : M.mem (M.quad j.1 α q0 b) P)
    (a : V) : M.EpsRaw P th io M.nat j.1 F a b ↔ M.InNRaw P th io M.nat j.1 α a := by
  obtain ⟨f, u, hf, hq⟩ := hq0
  rw [M.eps_iff hd hb hq hf a]
  constructor
  · exact fun h => h.1
  · intro h
    have ha : M.mem (M.op j.1 a) R := by
      obtain ⟨β, f1, u1, q1, h1, -⟩ := h
      exact (hd.hP.dom _ _ _ _ h1).2.2.2
    obtain ⟨s, hs⟩ := hd.hP.tot j hd.hj a u ha (hd.hP.dom _ _ _ _ hq).2.2.1
    exact ⟨h, s, hs, M.true_cTop hd hα s⟩

/-- The members of the set denoted by the name of a level are the sets with a name in the
level. -/
theorem lev_epsStar (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q0 α b : V}
    (hq0 : M.IsLevQ P io j q0) (hα : M.mem (M.op α α) th) (hb : M.mem (M.quad j.1 α q0 b) P)
    (y : V) : M.EpsStarRaw P th io M.nat j.1 tp F y b ↔
      ∃ y', M.InNRaw P th io M.nat j.1 α y' ∧ M.SimRaw P j.1 tp F y y' := by
  constructor
  · rintro ⟨y', hs, he⟩
    exact ⟨y', (M.lev_eps hd hq0 hα hb y').mp he, hs⟩
  · rintro ⟨y', hy', hs⟩
    exact ⟨y', hs, (M.lev_eps hd hq0 hα hb y').mpr hy'⟩

/-- Transitivity of the levels. -/
theorem k_trans (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {κ x y : V}
    (hy : M.InNRaw P th io M.nat j.1 κ y) (h : M.EpsStarRaw P th io M.nat j.1 tp F x y) :
    ∃ x', M.InNRaw P th io M.nat j.1 κ x' ∧ M.SimRaw P j.1 tp F x x' := by
  obtain ⟨x', hs, he⟩ := h
  obtain ⟨β, ry, lt, ne⟩ := M.inN_rank hy
  exact ⟨x', M.inN_mono hd (M.eps_inN_rank hd ry he) lt, hs⟩

/-- **Initial segments of the canonical order are covered by sets of the level**, at a limit
stage. -/
theorem cover_lim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {q0 l a : V} (hq0 : M.IsLevQ P io j q0)
    (hl : M.IsLim th l) (ha : M.InNRaw P th io M.nat j.1 l a) :
    ∃ T, M.InNRaw P th io M.nat j.1 l T ∧
      ∀ b, M.Lt P j.1 tp F Pr b a → M.EpsStarRaw P th io M.nat j.1 tp F b T := by
  obtain ⟨γ, g1, g2, ha', -⟩ := M.inN_lim hd hl ha ha
  have hγ := (hd.hth.fld _ _ g1).1
  obtain ⟨T, hT⟩ := M.lev_name hd hq0 hγ
  refine ⟨T, M.rank_inN (M.lev_rank hd hq0 hT) g1 g2, fun b hb => ?_⟩
  obtain ⟨b0, hb0, hs⟩ := M.lt_inN hd hPr ha' hb
  exact (M.lev_epsStar hd hq0 hγ hT b).mpr ⟨b0, hb0, hs⟩

end levels

end Model

end NFUCut



/-!
# Phase 0, part 4: Lemma 3.2 with the sequence of stages exposed

`L32X` is the form of Lemma 3.2 that the host construction uses: the hierarchy, the stages
`ν₀ < … < ν_(m+1) = κ`, each the least stage that is not small over the one before, the
numbers of the hierarchy with their order, names for the levels at these stages, and the
finite sequence of these names as a member of the level at `κ`.
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

section seq3x

variable {R E z S P th io Nt nle p F d tp qo Nu Pr Sg : V} {m j m1 : M.Num}
variable {q1 W l κ : V}

/-- The numbers of the hierarchy, with their order. -/
theorem exists_numNames' (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hqo : M.OrdQ P io j d qo) {l N : V} (hl : M.IsLim th l)
    (hβ : ∃ β, M.mem (M.op β l) th ∧ β ≠ l)
    (Ntot : ∀ n : M.Num, ∃ ξ, M.mem (M.op n.1 ξ) N)
    (Ndom : ∀ k ξ, M.mem (M.op k ξ) N → M.mem k M.nat ∧ M.mem (M.op ξ l) th ∧ ξ ≠ l)
    (Nfun : ∀ k ξ ξ', M.mem (M.op k ξ) N → M.mem (M.op k ξ') N → ξ = ξ')
    (Nonto : ∀ ξ, M.mem (M.op ξ l) th → ξ ≠ l → ∃ n : M.Num, M.mem (M.op n.1 ξ) N)
    (Nord : ∀ (n n' : M.Num) (ξ ξ' : V), M.mem (M.op n.1 ξ) N → M.mem (M.op n'.1 ξ') N →
      (n ≤ n' ↔ M.mem (M.op ξ ξ') th)) :
    ∃ Nm ol, M.NumNames P th io F tp qo Nm ol j l ∧
      ∀ (i i' : M.Num) (o o' : V), M.mem (M.op i.1 o) Nm → M.mem (M.op i'.1 o') Nm →
        (M.EpsStarRaw P th io M.nat j.1 tp F o o' ↔ i + 1 ≤ i') := by
  have hth := hd.hth
  obtain ⟨ol, hol⟩ := M.exists_ordName hd hqo hl.1
  obtain ⟨Nm, -, hN0⟩ := M.comp (σW [(0, 4), (20, 7), (463, 5)]) (Fml.ex 401 (Fml.ex 402 (Fml.ex 403 (.and (fPr 0 401 402) (.and (fApp 463 401 403) (fApp4 20 25 403 161 402)))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 25 j.1) 161 qo) 463 N)
  have hN1 : ∀ q0, M.mem q0 Nm ↔ ∃ i o ξ, q0 = M.op i o ∧ M.mem (M.op i ξ) N ∧
      M.mem (M.quad j.1 ξ qo o) P := by
    intro q0
    rw [hN0 q0]
    simp [Sat, M.sat_ex, M.sat_fPr', M.sat_fApp', M.sat_fApp4', Function.update_apply]
  have hNm : ∀ i o, M.mem (M.op i o) Nm ↔ ∃ ξ, M.mem (M.op i ξ) N ∧ M.mem (M.quad j.1 ξ qo o) P := by
    intro i o
    rw [hN1]
    constructor
    · rintro ⟨i1, o1, ξ, hq0, h1, h2⟩
      obtain ⟨e1, e2⟩ := M.op_inj hq0
      rw [e1, e2]
      exact ⟨ξ, h1, h2⟩
    · rintro ⟨ξ, h1, h2⟩
      exact ⟨i, o, ξ, rfl, h1, h2⟩
  have ninj : ∀ (i i' : M.Num) (ξ : V), M.mem (M.op i.1 ξ) N → M.mem (M.op i'.1 ξ) N → i = i' :=
    fun i i' ξ h1 h2 => le_antisymm ((Nord i i' ξ ξ h1 h2).mpr (hth.fld _ _ (Ndom _ _ h1).2.1).1)
      ((Nord i' i ξ ξ h2 h1).mpr (hth.fld _ _ (Ndom _ _ h1).2.1).1)
  refine ⟨Nm, ol, ⟨hol, fun i => ?_, fun i o o' h1 h2 => ?_, fun i o h1 => ?_, fun i o h1 => ?_,
    fun x hx => ?_, fun o u h1 => ?_, fun i o o' u h1 h2 => ?_, fun i i' o o' h1 h2 hs => ?_⟩,
    fun i i' o o' h1 h2 => ?_⟩
  · obtain ⟨ξ, hξ⟩ := Ntot i
    obtain ⟨o, ho⟩ := M.exists_ordName hd hqo (hth.fld _ _ (Ndom _ _ hξ).2.1).1
    exact ⟨o, (hNm _ _).mpr ⟨ξ, hξ, ho⟩⟩
  · obtain ⟨ξ, a1, a2⟩ := (hNm _ _).mp h1
    obtain ⟨ξ', b1, b2⟩ := (hNm _ _).mp h2
    rw [Nfun _ _ _ b1 a1] at b2
    exact hd.hP.fn _ _ _ _ _ a2 b2
  · obtain ⟨ξ, a1, a2⟩ := (hNm _ _).mp h1
    exact ⟨ξ, M.ordName_rank hd hqo a2, (Ndom _ _ a1).2⟩
  · obtain ⟨ξ, a1, a2⟩ := (hNm _ _).mp h1
    obtain ⟨-, lt, ne⟩ := Ndom _ _ a1
    exact (M.ordName_lt hd hqo (hth.fld _ _ lt).1 hl.1 a2 hol).mpr ⟨lt, ne⟩
  · obtain ⟨n0, ξ, o, a1, a2, a3⟩ := M.omega_members hd hqo hl.1 hol Nonto hx
    exact ⟨n0, o, (hNm _ _).mpr ⟨ξ, a1, a2⟩, a3⟩
  · obtain ⟨ξ0, a1, a2⟩ := (hNm _ _).mp h1
    obtain ⟨α0, hα0, hleast⟩ := M.exists_least_stage hd hl.1
    obtain ⟨β, hβl, hβne⟩ := hβ
    have h0l : M.mem (M.op α0 l) th := hth.trans _ _ _ (hleast β (hth.fld _ _ hβl).1) hβl
    have h0ne : α0 ≠ l := M.wo_ne_of_le_lt hth (hleast β (hth.fld _ _ hβl).1) hβl hβne
    obtain ⟨n0, hn0⟩ := Nonto α0 h0l h0ne
    have e0 : ξ0 = α0 := hth.antisymm _ _ ((Nord 0 n0 ξ0 α0 a1 hn0).mp zero_le)
      (hleast ξ0 (hth.fld _ _ (Ndom _ _ a1).2.1).1)
    rw [e0] at a2
    exact M.ordName_zero hd hqo hα0 hleast a2 u
  · obtain ⟨ζ, a1, a2⟩ := (hNm _ _).mp h1
    obtain ⟨ζ', b1, b2⟩ := (hNm _ _).mp h2
    have k1 : M.mem (M.op ζ ζ') th := (Nord i (i + 1) ζ ζ' a1 b1).mp (M.le_add_one i)
    have k2 : ζ ≠ ζ' := fun e => by
      rw [← e] at b1
      exact M.not_succ_le i (le_of_eq (ninj i (i + 1) ζ a1 b1).symm)
    refine M.ordName_succ hd hqo k1 k2 (fun γ hγ hne => ?_) a2 b2 u
    have hγγ := (hth.fld _ _ hγ).2
    obtain ⟨-, ltζ', neζ'⟩ := Ndom _ _ b1
    rcases M.wo_total hth hγγ hl.1 with hγl | hlγ
    · by_cases eγ : γ = l
      · rw [eγ]
        exact ltζ'
      · obtain ⟨n0, hn0⟩ := Nonto γ hγl eγ
        have h1' : i ≤ n0 := (Nord i n0 ζ γ a1 hn0).mpr hγ
        rcases M.eq_or_succ_le h1' with e | e
        · rw [← e] at hn0
          exact (hne (Nfun _ _ _ a1 hn0)).elim
        · exact (Nord (i + 1) n0 ζ' γ b1 hn0).mp e
    · exact hth.trans _ _ _ ltζ' hlγ
  · obtain ⟨ζ, a1, a2⟩ := (hNm _ _).mp h1
    obtain ⟨ζ', b1, b2⟩ := (hNm _ _).mp h2
    have e := M.ordName_inj hd hqo (hth.fld _ _ (Ndom _ _ a1).2.1).1
      (hth.fld _ _ (Ndom _ _ b1).2.1).1 a2 b2 hs
    rw [← e] at b1
    exact ninj i i' ζ a1 b1
  · obtain ⟨ζ, a1, a2⟩ := (hNm _ _).mp h1
    obtain ⟨ζ', b1, b2⟩ := (hNm _ _).mp h2
    rw [M.ordName_lt hd hqo (hth.fld _ _ (Ndom _ _ a1).2.1).1 (hth.fld _ _ (Ndom _ _ b1).2.1).1 a2 b2]
    constructor
    · rintro ⟨lt, ne⟩
      have hle : i ≤ i' := (Nord i i' ζ ζ' a1 b1).mpr lt
      rcases M.eq_or_succ_le hle with e | e
      · rw [← e] at b1
        exact (ne (Nfun _ _ _ a1 b1)).elim
      · exact e
    · intro h
      have hle : i ≤ i' := le_trans (M.le_add_one i) h
      refine ⟨(Nord i i' ζ ζ' a1 b1).mp hle, fun e => ?_⟩
      rw [← e] at b1
      have e2 := ninj i i' ζ a1 b1
      rw [← e2] at h
      exact M.not_succ_le i h

/-- The names of the levels at the stages of the sequence, as a set function. -/
theorem exists_levSeq (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (ss : M.StageSeq P th io Sg qo W l j m1 κ) (q0 : V) :
    ∃ Kn, ∀ (i b : V), M.mem (M.op i b) Kn ↔ ∃ y1 ξ p0, M.mem (M.op i y1) W ∧
      M.mem (M.quad j.1 ξ p0 y1) P ∧ M.mem (M.quad j.1 ξ q0 b) P := by
  obtain ⟨Kn, -, hK0⟩ := M.comp (σW [(0, 4), (20, 7), (464, 5)])
    (Fml.ex 401 (Fml.ex 402 (Fml.ex 403 (Fml.ex 404 (Fml.ex 405 (.and (fPr 0 401 402)
      (.and (fApp 464 401 403) (.and (fApp4 20 25 404 405 403) (fApp4 20 25 404 161 402))))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 25 j.1) 161 q0) 464 W)
  have hK1 : ∀ q, M.mem q Kn ↔ ∃ i b y1 ξ p0, q = M.op i b ∧ M.mem (M.op i y1) W ∧
      M.mem (M.quad j.1 ξ p0 y1) P ∧ M.mem (M.quad j.1 ξ q0 b) P := by
    intro q
    rw [hK0 q]
    simp [Sat, M.sat_ex, M.sat_fPr', M.sat_fApp', M.sat_fApp4', Function.update_apply]
  refine ⟨Kn, fun i b => ?_⟩
  rw [hK1]
  constructor
  · rintro ⟨i1, b1, y1, ξ, p0, hq0, h1, h2, h3⟩
    obtain ⟨e1, e2⟩ := M.op_inj hq0
    rw [e1, e2]
    exact ⟨y1, ξ, p0, h1, h2, h3⟩
  · rintro ⟨y1, ξ, p0, h1, h2, h3⟩
    exact ⟨i, b, y1, ξ, p0, rfl, h1, h2, h3⟩

end seq3x

section inner1x

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j m1 : M.Num}
variable {l κ Nm ol Pw : V}

/-- The internal sequence, for an arbitrary set function `Pw` from the numbers below `m₁` to
names of rank below `κ`. -/
theorem exists_inner_seq' (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hlim : M.IsLim th κ)
    (nn : M.NumNames P th io F tp qo Nm ol j l)
    (ptot : ∀ i : M.Num, i + 1 ≤ m1 → ∃ p0, M.mem (M.op i.1 p0) Pw)
    (pfn : ∀ i p0 p', M.mem (M.op i p0) Pw → M.mem (M.op i p') Pw → p0 = p')
    (pinN : ∀ (i : M.Num) (p0 : V), i + 1 ≤ m1 → M.mem (M.op i.1 p0) Pw → M.InNRaw P th io M.nat j.1 κ p0)
    (hlκ : M.mem (M.op l κ) th) (k : M.Num) (hk : k + 1 ≤ m1) :
    ∃ f, M.InnerSeqR P th io M.nat M.adG F tp Nm Pw κ j k.1 f := by
  have hth := hd.hth
  have numκ : ∀ i o, M.mem (M.op i o) Nm → M.InNRaw P th io M.nat j.1 κ o := by
    intro i o h1
    obtain ⟨ξ, r, lt, ne⟩ := nn.rank i o h1
    exact M.rank_inN r (hth.trans _ _ _ lt hlκ) (M.wo_ne_of_lt_le hth lt ne hlκ)
  have hsat : ∀ k : M.Num, Sat M.mem M.isSet innerFml (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 10 (0 : M.Num).1) 20 P) 21 tp) 22 th) 24 io) 25 j.1) 27 M.nat) 28 M.adG) 396 m1.1) 460 Nm) 461 Pw) 462 κ) 400 k.1) ↔
      ((∃ x, M.mem x M.nat ∧ ¬ x = (0 : M.Num).1 ∧ M.mem (M.trip k.1 x m1.1) M.adG) →
        ∃ f, M.InnerSeqR P th io M.nat M.adG F tp Nm Pw κ j k.1 f) := by
    intro k
    simp [innerFml, InnerSeqR, IsOPairN, IsPairN, Sat, M.sat_imp, M.sat_iff, M.sat_or, M.sat_ex,
      M.sat_fInN, M.sat_fEpsS, M.sat_fSim, M.sat_fLeN, M.sat_fLtN, M.sat_fApp', Function.update_apply]
  have key := M.num_ind_fml (σW [(6, 5), (20, 7), (22, 5), (24, 5), (27, 3), (28, 7), (460, 5), (461, 5)])
    innerFml 400 rfl (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 10 (0 : M.Num).1) 20 P) 21 tp) 22 th) 24 io) 25 j.1) 27 M.nat) 28 M.adG) 396 m1.1) 460 Nm) 461 Pw) 462 κ) ?_ ?_ k
  · exact (hsat k).mp key ((M.ltRaw_num k m1).mpr hk)
  · rw [show M.zero = (0 : M.Num).1 from rfl, hsat 0]
    intro hlt
    have h01 : (0 : M.Num) + 1 ≤ m1 := (M.ltRaw_num 0 m1).mp hlt
    obtain ⟨o0, ho0⟩ := nn.tot 0
    obtain ⟨p00, hp00⟩ := ptot 0 h01
    have hoκ := numκ _ _ ho0
    have hpκ := pinN 0 _ h01 hp00
    obtain ⟨c0, hc0, hc0p⟩ := M.opair_lim hd hlim hoκ hpκ
    obtain ⟨f, hf, hfm⟩ := M.pair_lim hd hlim hc0 hc0
    refine ⟨f, hf, fun x => ?_⟩
    rw [hfm x]
    constructor
    · intro h1
      have hs : M.SimRaw P j.1 tp F x c0 := h1.elim id id
      exact ⟨(0 : M.Num).1, o0, p00, c0, (0 : M.Num).2, (M.leRaw_iff M.adG_spec 0 0).mpr (le_refl _),
        ho0, hp00, hc0p, hs⟩
    · rintro ⟨i, o, p1, c, hi, hle, r1, r2, r3, r4⟩
      have e0 : (⟨i, hi⟩ : M.Num) = 0 :=
        le_antisymm ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ 0).mp hle) zero_le
      have ei : i = (0 : M.Num).1 := congrArg Subtype.val e0
      rw [ei] at r1 r2
      rw [nn.fn _ _ _ r1 ho0, pfn _ _ _ r2 hp00] at r3
      exact Or.inl (M.sim_trans hd r4 (M.opairN_congr hd r3 hc0p (M.inN_refl hd hoκ)
        (M.inN_refl hd hpκ) (M.sim_trans hd (M.sim_symm hd r4) r4) (M.inN_refl hd hc0)))
  · intro k ih
    rw [show M.succ k.1 = (k + 1).1 from (M.val_add_one k).symm, hsat (k + 1)]
    intro hlt
    have hk2 : k + 1 + 1 ≤ m1 := (M.ltRaw_num (k + 1) m1).mp hlt
    obtain ⟨f, hf, hfm⟩ := (hsat k).mp ih
      ((M.ltRaw_num k m1).mpr (le_trans (M.le_add_one _) hk2))
    obtain ⟨o', ho'⟩ := nn.tot (k + 1)
    obtain ⟨p', hp'⟩ := ptot (k + 1) hk2
    have hoκ := numκ _ _ ho'
    have hpκ := pinN (k + 1) _ hk2 hp'
    obtain ⟨c', hc', hc'p⟩ := M.opair_lim hd hlim hoκ hpκ
    obtain ⟨s1, hs1, hs1m⟩ := M.pair_lim hd hlim hc' hc'
    obtain ⟨s2, hs2, hs2m⟩ := M.pair_lim hd hlim hf hs1
    obtain ⟨f', hf', hf'm⟩ := M.union_lim hd hlim hs2
    refine ⟨f', hf', fun x => ?_⟩
    rw [hf'm x]
    constructor
    · rintro ⟨y, hxy, hy2⟩
      rcases (hs2m y).mp hy2 with h1 | h1
      · have hxf : M.EpsStarRaw P th io M.nat j.1 tp F x f := M.epsStar_congr hd (M.epsStar_left hd hxy) h1 hxy
        obtain ⟨i, o, p1, c, hi, hle, r1, r2, r3, r4⟩ := (hfm x).mp hxf
        exact ⟨i, o, p1, c, hi, (M.leRaw_iff M.adG_spec ⟨i, hi⟩ (k + 1)).mpr
          (le_trans ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ k).mp hle) (M.le_add_one k)), r1, r2, r3, r4⟩
      · have hxs1 : M.EpsStarRaw P th io M.nat j.1 tp F x s1 := M.epsStar_congr hd (M.epsStar_left hd hxy) h1 hxy
        have hs : M.SimRaw P j.1 tp F x c' := ((hs1m x).mp hxs1).elim id id
        exact ⟨(k + 1).1, o', p', c', (k + 1).2,
          (M.leRaw_iff M.adG_spec (k + 1) (k + 1)).mpr (le_refl _), ho', hp', hc'p, hs⟩
    · rintro ⟨i, o, p1, c, hi, hle, r1, r2, r3, r4⟩
      rcases M.eq_or_succ_le ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ (k + 1)).mp hle) with e | e
      · have ei : i = (k + 1).1 := congrArg Subtype.val e
        rw [ei] at r1 r2
        rw [nn.fn _ _ _ r1 ho', pfn _ _ _ r2 hp'] at r3
        have hs : M.SimRaw P j.1 tp F x c' := M.sim_trans hd r4 (M.opairN_congr hd r3 hc'p (M.inN_refl hd hoκ)
          (M.inN_refl hd hpκ) (M.sim_trans hd (M.sim_symm hd r4) r4) (M.inN_refl hd hc'))
        exact ⟨s1, (hs1m x).mpr (Or.inl hs), (hs2m s1).mpr (Or.inr (M.inN_refl hd hs1))⟩
      · have hxf : M.EpsStarRaw P th io M.nat j.1 tp F x f := (hfm x).mpr ⟨i, o, p1, c, hi,
          (M.leRaw_iff M.adG_spec ⟨i, hi⟩ k).mpr (M.le_of_succ_le_succ e), r1, r2, r3, r4⟩
        exact ⟨f, hxf, (hs2m f).mpr (Or.inl (M.inN_refl hd hf))⟩


end inner1x

/-- **Lemma 3.2 with the stages exposed.** -/
structure L32X (R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ : V)
    (n j m : M.Num) : Prop where
  hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr n j
  hPr : M.IsPrec P th io Nt d Pr j
  hq : M.IsMark P th io Nt d j q1
  hNu : ∀ k o, ¬ M.mem (M.op k o) Nu
  hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j
  hqo : M.OrdQ P io j d qo
  ss : M.StageSeq P th io Sg qo W l j (m + 1) κ
  hunb : ∀ e, M.mem (M.op e e) th → ∃ e', M.mem (M.op e e') th ∧ e ≠ e'
  hκ : M.IsLim th κ
  hlκ : M.mem (M.op l κ) th ∧ l ≠ κ
  nums : M.NumNames P th io F tp qo Nm ol j l
  ord : ∀ (i i' : M.Num) (o o' : V), M.mem (M.op i.1 o) Nm → M.mem (M.op i'.1 o') Nm →
    (M.EpsStarRaw P th io M.nat j.1 tp F o o' ↔ i + 1 ≤ i')
  sep : ∀ a b φ : M.Num, a ≠ 0 → M.cAnd (M.cRel 0 0 a) φ + 1 ≤ b →
    ∀ t, M.TrueAt P io F j.1 κ (M.cSep a b φ) t
  coll : ∀ a b y z φ : M.Num, a ≠ y → a ≠ b → b ≠ y → b ≠ z → φ + 1 ≤ b →
    ∀ t, M.TrueAt P io F j.1 κ (M.cColl a b y z φ) t
  wleast : ∀ a x y : M.Num, a ≠ x → x ≠ y → a ≠ y → ∀ t, M.TrueAt P io F j.1 κ (M.cWLeast a x y) t
  hσ' : M.mem (M.op κ σ') th ∧ κ ≠ σ'
  hδ : M.mem (M.op σ' δ) th ∧ σ' ≠ δ
  hq0 : M.IsLevQ P io j q0
  kn : ∀ (i b : V), M.mem (M.op i b) Kn ↔ ∃ y1 ξ p0, M.mem (M.op i y1) W ∧
    M.mem (M.quad j.1 ξ p0 y1) P ∧ M.mem (M.quad j.1 ξ q0 b) P
  lam : M.InnerSeqR P th io M.nat M.adG F tp Nm Kn κ j m.1 Lam

theorem l32x {R E z S : V} {n m : M.Num} (h : M.IsLadder R E z S n)
    (hn : 3 * (m + 1) + 1 + 1 ≤ n) :
    ∃ P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ,
      M.L32X R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ n
        (3 * (m + 1) + 1 + 1) m := by
  obtain ⟨P, hP⟩ := M.exists_pairing h
  have hL : 3 * (m + 1) ≤ n := le_trans (le_trans (M.le_add_one _) (M.le_add_one _)) hn
  obtain ⟨th, hth, fldH, hlong, hseg⟩ := M.hartogs h hP (i := 3 * (m + 1)) hn
  obtain ⟨l, N, hl, hβ, Ntot, Ndom, Nfun, Nonto, Nord⟩ := M.exists_omega_stage h hP hL hth hlong
  obtain ⟨io, Nt, nle, p, F, d, tp, qo, Nu, Pr, hd, -, -, -, hqo', hNu', hPr⟩ :=
    M.exists_hierData h hP hn hth
      (fun a b hab => ⟨fldH a (hth.fld a b hab).1, fldH b (hth.fld a b hab).2⟩) ⟨l, hl.1⟩
      (M.cOrd 0 1 2 3) M.emp
  have hqo : M.OrdQ P io (3 * (m + 1) + 1 + 1) d qo := hqo'
  have hNu : ∀ k o, ¬ M.mem (M.op k o) Nu := fun k o hko => by
    obtain ⟨ξ, hξ, -⟩ := (hNu' k o).mp hko
    exact M.not_mem_emp _ hξ
  obtain ⟨q1, hq⟩ := M.exists_isMark hd
  obtain ⟨Sg, hSg⟩ := M.exists_sig hth P io Nt d tp q1 F Pr (3 * (m + 1) + 1 + 1)
  have hunb : ∀ e, M.mem (M.op e e) th → ∃ e', M.mem (M.op e e') th ∧ e ≠ e' := fun e he => by
    obtain ⟨l', -, h1, h2⟩ := M.limit_above h hP hL hth hlong hseg he
    exact ⟨l', h1, h2⟩
  obtain ⟨u0, v0, hu0, hv0, huv0⟩ := M.rung_two h (j := 0) zero_le
  obtain ⟨io0, io0_dom, io0_tot, io0_fun, io0_inj, -⟩ :=
    M.exists_numerals hP (j := 0) zero_le hu0 hv0 huv0
  have g0_tot : ∀ β, M.mem (M.op β l) th → β ≠ l →
      ∃ a, M.mem (M.op β a) (M.rcomp (M.conv N) io0) := fun β lt ne => by
    obtain ⟨k, hk⟩ := Nonto β lt ne
    obtain ⟨a, ha⟩ := io0_tot k
    exact ⟨a, M.mem_rcomp.mpr ⟨k.1, M.mem_conv.mpr hk, ha⟩⟩
  have g0_dom : ∀ β a, M.mem (M.op β a) (M.rcomp (M.conv N) io0) →
      M.mem (M.op β l) th ∧ β ≠ l ∧ M.mem (M.op (0 : M.Num).1 a) R := fun β a hβa => by
    obtain ⟨k, h1, h2⟩ := M.mem_rcomp.mp hβa
    obtain ⟨-, lt, ne⟩ := Ndom _ _ (M.mem_conv.mp h1)
    exact ⟨lt, ne, (io0_dom _ _ h2).2⟩
  have g0_inj : ∀ β β' a, M.mem (M.op β a) (M.rcomp (M.conv N) io0) →
      M.mem (M.op β' a) (M.rcomp (M.conv N) io0) → β = β' := fun β β' a h1 h2 => by
    obtain ⟨k, a1, a2⟩ := M.mem_rcomp.mp h1
    obtain ⟨k', b1, b2⟩ := M.mem_rcomp.mp h2
    have ek : k = k' := io0_inj _ _ _ a2 b2
    rw [← ek] at b1
    exact Nfun _ _ _ (M.mem_conv.mp a1) (M.mem_conv.mp b1)
  obtain ⟨Nm, ol, nn, nord⟩ := M.exists_numNames' hd hqo hl hβ Ntot Ndom Nfun Nonto Nord
  obtain ⟨W, κ, ss⟩ := M.exists_stageSeq h hd hPr hq hSg (L := 3 * (m + 1)) (m1 := m + 1) hL
    (le_refl _) hlong hunb hl.1 nn.hol g0_tot g0_dom g0_inj
  have hm1 : (1 : M.Num) ≤ m + 1 := M.le_def.mpr ⟨m, by ring⟩
  have hlim := M.top_lim hd hPr hq hSg ss hm1
  have hlκ : M.mem (M.op l κ) th ∧ l ≠ κ := by
    have h0 := M.sat_zero hd ss nn.hol
    obtain ⟨ξ1, p1, h1⟩ := M.sat_tot ss (i := 0 + 1) (by rw [zero_add]; exact hm1)
    obtain ⟨lt, ne⟩ := M.sat_lt hd hq hSg ss hunb h0 h1
    have le2 := M.sat_le_top ss h1
    exact ⟨hth.trans _ _ _ lt le2, M.wo_ne_of_lt_le hth lt ne le2⟩
  have holκ := M.rank_inN (M.ordName_rank hd hqo nn.hol) hlκ.1 hlκ.2
  have hdκ := M.d_inN hd hlκ.1 hlκ.2
  obtain ⟨pκ, yk, a1, a2⟩ := ss.top
  have htop : M.SAt P W (3 * (m + 1) + 1 + 1) (m + 1) κ pκ := ⟨yk, a1, a2⟩
  obtain ⟨ξm, pm, hm0⟩ := M.sat_tot ss (i := m) (M.le_add_one m)
  have hnext := (M.sat_step ss hm0 htop).1
  obtain ⟨σ', hσ', neσ'⟩ := hunb κ hlim.1
  obtain ⟨δ, hδ, neδ⟩ := hunb σ' (hth.fld _ _ hσ').2
  obtain ⟨β0, hβ0, hβ0ne⟩ := hβ
  obtain ⟨q0, hq0⟩ := M.exists_levQ hd
  obtain ⟨Kn, hKn⟩ := M.exists_levSeq hd ss q0
  have kfn : ∀ i b b', M.mem (M.op i b) Kn → M.mem (M.op i b') Kn → b = b' := by
    intro i b b' h1 h2
    obtain ⟨y1, ξ, p0, a1, a2, a3⟩ := (hKn i b).mp h1
    obtain ⟨y1', ξ', p0', b1, b2, b3⟩ := (hKn i b').mp h2
    rw [ss.fn _ _ _ b1 a1] at b2
    obtain ⟨e, -⟩ := hd.hP.inj _ _ _ _ _ _ b2 a2
    rw [e] at b3
    exact hd.hP.fn _ _ _ _ _ a3 b3
  have ktot : ∀ i : M.Num, i + 1 ≤ m + 1 → ∃ b, M.mem (M.op i.1 b) Kn := by
    intro i hi
    obtain ⟨ξ, p0, y1, a1, a2⟩ := M.sat_tot ss (le_trans (M.le_add_one i) hi)
    obtain ⟨b, hb⟩ := M.lev_name hd hq0 (hth.fld _ _ (ss.le_top _ _ _ _ a1 a2)).1
    exact ⟨b, (hKn _ _).mpr ⟨y1, ξ, p0, a1, a2, hb⟩⟩
  have kinN : ∀ (i : M.Num) (b : V), i + 1 ≤ m + 1 → M.mem (M.op i.1 b) Kn →
      M.InNRaw P th io M.nat (3 * (m + 1) + 1 + 1 : M.Num).1 κ b := by
    intro i b hi hb
    obtain ⟨y1, ξ, p0, a1, a2, a3⟩ := (hKn _ _).mp hb
    have hs : M.SAt P W (3 * (m + 1) + 1 + 1) i ξ p0 := ⟨y1, a1, a2⟩
    obtain ⟨ξ', p', h2⟩ := M.sat_tot ss hi
    obtain ⟨lt, ne⟩ := M.sat_lt hd hq hSg ss hunb hs h2
    have le2 := M.sat_le_top ss h2
    exact M.rank_inN (M.lev_rank hd hq0 a3) (hth.trans _ _ _ lt le2) (M.wo_ne_of_lt_le hth lt ne le2)
  obtain ⟨Lam, hLam⟩ := M.exists_inner_seq' hd hlim nn ktot kfn kinN hlκ.1 m (le_refl _)
  exact ⟨P, th, io, Nt, nle, p, F, d, tp, qo, Nu, Pr, κ, ol, Nm, l, Sg, q1, W, q0, Kn, Lam, σ', δ,
    { hd := hd
      hPr := hPr
      hq := hq
      hNu := hNu
      hSg := hSg
      hqo := hqo
      ss := ss
      hunb := hunb
      hκ := hlim
      hlκ := hlκ
      nums := nn
      ord := nord
      sep := fun a b φ ha hb t =>
        M.hier_sep hd hPr hq hNu hSg hnext hσ' neσ' hδ neδ a b φ ha hb t
      coll := fun a b y z φ h1 h2 h3 h4 h5 t =>
        M.hier_coll hd hPr hq hNu hSg hnext hσ' neσ' hδ neδ a b y z φ h1 h2 h3 h4 h5 t
      wleast := fun a x y h1 h2 h3 t => M.hier_wleast hd hPr hlim.1 a x y h1 h2 h3 t
      hσ' := ⟨hσ', neσ'⟩
      hδ := ⟨hδ, neδ⟩
      hq0 := hq0
      kn := hKn
      lam := hLam }⟩

/-- At calm heights the structure exists. -/
theorem l32x_calm {m : M.Num} (hn : M.InS (3 * (m + 1) + 1 + 1 : M.Num).1) :
    ∃ R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ,
      M.L32X R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ
        (3 * (m + 1) + 1 + 1) (3 * (m + 1) + 1 + 1) m := by
  obtain ⟨R, E, z, S, h, -⟩ := M.lemma_3_1 hn
  obtain ⟨P, th, io, Nt, nle, p, F, d, tp, qo, Nu, Pr, κ, ol, Nm, l, Sg, q1, W, q0, Kn, Lam, σ', δ, L⟩ :=
    M.l32x h (le_refl _)
  exact ⟨R, P, th, io, Nt, nle, p, F, d, tp, qo, Nu, Pr, κ, ol, Nm, l, Sg, q1, W, q0, Kn, Lam, σ', δ, L⟩

end Model

end NFUCut



/-!
# Phase 0, part 5: the level at the top stage of Lemma 3.2 is a host

The carrier is the type of the names of rank below `κ` modulo "denote the same set".
`hholds_iff` relates satisfaction in this structure to truth at the stage `κ`; the axioms of a
host follow from the semantic forms of part 2.
-/

namespace NFUCut

/-- The translation of the formulas of a host. Equality becomes "have the same members", with
an auxiliary variable. -/
def toCF : Form → CF
  | .mem x y => .mem x y
  | .lt x y => .lt x y
  | .eq x y => CF.eq (x + y + 1) x y
  | .rel _ _ _ _ => CF.and (.mem 0 0) (.neg (.mem 0 0))
  | .tru => .neg (CF.and (.mem 0 0) (.neg (.mem 0 0)))
  | .fls => CF.and (.mem 0 0) (.neg (.mem 0 0))
  | .neg φ => .neg (toCF φ)
  | .and φ ψ => .and (toCF φ) (toCF ψ)
  | .or φ ψ => CF.or (toCF φ) (toCF ψ)
  | .imp φ ψ => CF.imp (toCF φ) (toCF ψ)
  | .iff φ ψ => CF.iff (toCF φ) (toCF ψ)
  | .all x φ => .all x (toCF φ)
  | .ex x φ => CF.ex x (toCF φ)

theorem upd_eq_update {W : Type} (ρ : ℕ → W) (x : ℕ) (a : W) : upd ρ x a = Function.update ρ x a := by
  funext n
  by_cases h : n = x
  · subst h
    simp [upd_same]
  · simp [upd_ne _ _ h, Function.update_of_ne h]

theorem update_map {A B : Type} (f : A → B) (ρ : ℕ → A) (x : ℕ) (a : A) :
    (fun i => f (Function.update ρ x a i)) = Function.update (fun i => f (ρ i)) x (f a) := by
  funext n
  by_cases h : n = x
  · subst h
    simp
  · simp [Function.update_of_ne h]

/-- The renaming used for Separation: the comprehension variable becomes `0`. -/
def renS (x : ℕ) : ℕ → ℕ := fun n => if n = x then 0 else n + 1

theorem renS_inj (x : ℕ) : Function.Injective (renS x) := by
  intro a b h
  unfold renS at h
  split_ifs at h with h1 h2 h2 <;> omega

/-- The renaming used for Collection: the two variables become `0` and `1`. -/
def renC (x y : ℕ) : ℕ → ℕ := fun n => if n = x then 0 else if n = y then 1 else n + 2

theorem renC_inj {x y : ℕ} (hxy : x ≠ y) : Function.Injective (renC x y) := by
  intro a b h
  unfold renC at h
  split_ifs at h <;> omega

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

section quot

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem tr_eq {α : V} {z x y : ℕ} (hzx : z ≠ x) (hzy : z ≠ y) (ρ : ℕ → V) :
    M.TrC P th io tp F Pr j α (CF.eq z x y) ρ ↔
      ∀ a, M.InNRaw P th io M.nat j.1 α a →
        (M.EpsStarRaw P th io M.nat j.1 tp F a (ρ x) ↔
          M.EpsStarRaw P th io M.nat j.1 tp F a (ρ y)) := by
  unfold CF.eq
  simp only [TrC]
  refine forall_congr' fun a => imp_congr_right fun _ => ?_
  rw [M.tr_iff]
  simp only [TrC, Function.update_self, Function.update_of_ne hzx.symm,
    Function.update_of_ne hzy.symm]

/-- Extensionality among the names of rank below a stage. -/
theorem sim_iff_inN (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {κ a b : V}
    (ha : M.InNRaw P th io M.nat j.1 κ a) (hb : M.InNRaw P th io M.nat j.1 κ b) :
    M.SimRaw P j.1 tp F a b ↔ ∀ x, M.InNRaw P th io M.nat j.1 κ x →
      (M.EpsStarRaw P th io M.nat j.1 tp F x a ↔ M.EpsStarRaw P th io M.nat j.1 tp F x b) := by
  obtain ⟨βa, ra, lta, -⟩ := M.inN_rank ha
  obtain ⟨βb, rb, ltb, -⟩ := M.inN_rank hb
  have hβa := (hd.hth.fld _ _ lta).1
  have hβb := (hd.hth.fld _ _ ltb).1
  rw [M.sim_iff_ext hd ra rb hβa hβb]
  constructor
  · exact fun h x _ => h x
  · intro h x
    have saa := M.inN_refl hd ha
    have sbb := M.inN_refl hd hb
    constructor
    · intro hx
      obtain ⟨x', hx', hs⟩ := M.k_trans hd ha hx
      have h1 := M.epsStar_congr hd hs saa hx
      exact M.epsStar_congr hd (M.sim_symm hd hs) sbb ((h x' hx').mp h1)
    · intro hx
      obtain ⟨x', hx', hs⟩ := M.k_trans hd hb hx
      have h1 := M.epsStar_congr hd hs sbb hx
      exact M.epsStar_congr hd (M.sim_symm hd hs) saa ((h x' hx').mpr h1)

/-- The names of rank below `κ`. -/
abbrev NameT (P th io κ : V) (j : M.Num) : Type := {a : V // M.InNRaw P th io M.nat j.1 κ a}

/-- "Denote the same set" on the names of rank below `κ`. -/
def nameSetoid (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (κ : V) :
    Setoid (M.NameT P th io κ j) where
  r a b := M.SimRaw P j.1 tp F a.1 b.1
  iseqv := ⟨fun a => M.inN_refl hd a.2, fun h => M.sim_symm hd h,
    fun h1 h2 => M.sim_trans hd h1 h2⟩

/-- The sets of the level at `κ`. -/
abbrev HW (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (κ : V) : Type :=
  Quotient (M.nameSetoid hd κ)

/-- The set denoted by a name. -/
def hmk (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {κ : V}
    (a : M.NameT P th io κ j) : M.HW hd κ := Quotient.mk (M.nameSetoid hd κ) a

theorem hmk_eq (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {κ : V}
    {a b : M.NameT P th io κ j} :
    M.hmk hd a = M.hmk hd b ↔ M.SimRaw P j.1 tp F a.1 b.1 :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem hmk_surj (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {κ : V}
    (x : M.HW hd κ) : ∃ a, x = M.hmk hd a := Quotient.inductionOn x (fun a => ⟨a, rfl⟩)

/-- Membership between the sets denoted. -/
def hmem (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {κ : V} :
    M.HW hd κ → M.HW hd κ → Prop :=
  Quotient.lift₂ (s₁ := M.nameSetoid hd κ) (s₂ := M.nameSetoid hd κ)
    (fun a b => M.EpsStarRaw P th io M.nat j.1 tp F a.1 b.1)
    (fun a b a' b' ha hb => propext ⟨fun h => M.epsStar_congr hd ha hb h,
      fun h => M.epsStar_congr hd (M.sim_symm hd ha) (M.sim_symm hd hb) h⟩)

/-- The canonical order of the sets denoted. -/
def hlt (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {κ : V} :
    M.HW hd κ → M.HW hd κ → Prop :=
  Quotient.lift₂ (s₁ := M.nameSetoid hd κ) (s₂ := M.nameSetoid hd κ)
    (fun a b => M.Lt P j.1 tp F Pr a.1 b.1)
    (fun a b a' b' ha hb => propext ⟨fun h => M.lt_congr hd ha hb h,
      fun h => M.lt_congr hd (M.sim_symm hd ha) (M.sim_symm hd hb) h⟩)

/-- **Satisfaction in the level is truth at the stage.** -/
theorem hholds_iff (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {κ : V} :
    ∀ (φ : _root_.Form), φ.Pure → ∀ ρ : ℕ → M.NameT P th io κ j,
      (_root_.Holds (M.hmem hd) (M.hlt hd) noRel φ (fun i => M.hmk hd (ρ i)) ↔
        M.TrC P th io tp F Pr j κ (toCF φ) (fun i => (ρ i).1))
  | .mem x y, _, ρ => Iff.rfl
  | .lt x y, _, ρ => Iff.rfl
  | .eq x y, _, ρ => by
    simp only [_root_.Holds, toCF]
    rw [M.hmk_eq hd, M.tr_eq (by omega) (by omega),
      M.sim_iff_inN hd (ρ x).2 (ρ y).2]
  | .rel _ _ _ _, h, ρ => h.elim
  | .tru, _, ρ => by
    simp only [_root_.Holds, toCF, TrC]
    tauto
  | .fls, _, ρ => by
    simp only [_root_.Holds, toCF, TrC]
    tauto
  | .neg φ, h, ρ => by
    simp only [_root_.Holds, toCF, TrC]
    exact not_congr (hholds_iff hd hPr φ h ρ)
  | .and φ ψ, h, ρ => by
    simp only [_root_.Holds, toCF, TrC]
    exact and_congr (hholds_iff hd hPr φ h.1 ρ) (hholds_iff hd hPr ψ h.2 ρ)
  | .or φ ψ, h, ρ => by
    simp only [_root_.Holds, toCF]
    rw [M.tr_or]
    exact or_congr (hholds_iff hd hPr φ h.1 ρ) (hholds_iff hd hPr ψ h.2 ρ)
  | .imp φ ψ, h, ρ => by
    simp only [_root_.Holds, toCF]
    rw [M.tr_imp]
    exact imp_congr (hholds_iff hd hPr φ h.1 ρ) (hholds_iff hd hPr ψ h.2 ρ)
  | .iff φ ψ, h, ρ => by
    simp only [_root_.Holds, toCF]
    rw [M.tr_iff]
    exact iff_congr (hholds_iff hd hPr φ h.1 ρ) (hholds_iff hd hPr ψ h.2 ρ)
  | .all x φ, h, ρ => by
    simp only [_root_.Holds, toCF, TrC]
    constructor
    · intro hall a ha
      have h1 := hall (M.hmk hd ⟨a, ha⟩)
      rw [upd_eq_update, ← update_map (M.hmk hd) ρ x ⟨a, ha⟩,
        hholds_iff hd hPr φ h (Function.update ρ x ⟨a, ha⟩),
        update_map Subtype.val ρ x ⟨a, ha⟩] at h1
      exact h1
    · intro hall w
      obtain ⟨a, rfl⟩ := M.hmk_surj hd w
      rw [upd_eq_update, ← update_map (M.hmk hd) ρ x a,
        hholds_iff hd hPr φ h (Function.update ρ x a), update_map Subtype.val ρ x a]
      exact hall a.1 a.2
  | .ex x φ, h, ρ => by
    simp only [_root_.Holds, toCF]
    rw [M.tr_ex]
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨a, rfl⟩ := M.hmk_surj hd w
      rw [upd_eq_update, ← update_map (M.hmk hd) ρ x a,
        hholds_iff hd hPr φ h (Function.update ρ x a), update_map Subtype.val ρ x a] at hw
      exact ⟨a.1, a.2, hw⟩
    · rintro ⟨a, ha, hw⟩
      refine ⟨M.hmk hd ⟨a, ha⟩, ?_⟩
      rw [upd_eq_update, ← update_map (M.hmk hd) ρ x ⟨a, ha⟩,
        hholds_iff hd hPr φ h (Function.update ρ x ⟨a, ha⟩),
        update_map Subtype.val ρ x ⟨a, ha⟩]
      exact hw

end quot

end Model

end NFUCut



/-!
# Phase 0, part 6: the host of Lemma 3.2
-/

namespace NFUCut

theorem renS_spec {A : Type} (ρ : ℕ → A) (x : ℕ) (y : A) (n : ℕ) :
    Function.update (fun k => ρ (k - 1)) 0 y (renS x n) = Function.update ρ x y n := by
  unfold renS
  by_cases h : n = x
  · subst h
    simp
  · simp [h, Function.update_of_ne]

theorem renC_spec {A : Type} (ρ : ℕ → A) {x y : ℕ} (hxy : x ≠ y) (u v : A) (n : ℕ) :
    Function.update (Function.update (fun k => ρ (k - 2)) 0 u) 1 v (renC x y n) =
      Function.update (Function.update ρ x u) y v n := by
  unfold renC
  by_cases h : n = x
  · subst h
    simp [Function.update_apply, hxy]
  · by_cases h' : n = y
    · subst h'
      simp [Function.update_apply, h]
    · simp [Function.update_apply, h, h']

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

section host

variable {R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ : V} {n j m : M.Num}

theorem numκ (L : M.L32X R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ n j m)
    {i o : V} (h : M.mem (M.op i o) Nm) : M.InNRaw P th io M.nat j.1 κ o := by
  obtain ⟨ξ, r, lt, ne⟩ := L.nums.rank i o h
  exact M.rank_inN r (L.hd.hth.trans _ _ _ lt L.hlκ.1) (M.wo_ne_of_lt_le L.hd.hth lt ne L.hlκ.1)

theorem olκ (L : M.L32X R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ n j m) :
    M.InNRaw P th io M.nat j.1 κ ol :=
  M.rank_inN (M.ordName_rank L.hd L.hqo L.nums.hol) L.hlκ.1 L.hlκ.2

/-- Truth of the renamed formula under representatives is satisfaction in the level. -/
theorem coll_key (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr n j)
    (hPr : M.IsPrec P th io Nt d Pr j) (φ : _root_.Form) (hφ : φ.Pure) {x y : ℕ} (hxy : x ≠ y)
    (ρb : ℕ → M.HW hd κ) (u v : M.NameT P th io κ j) :
    (M.TrC P th io tp F Pr j κ (toCF (φ.map (renC x y)))
        (Function.update (Function.update (fun i => (Quotient.out (ρb (i - 2))).1) 0 u.1) 1 v.1) ↔
      _root_.Holds (M.hmem hd) (M.hlt hd) noRel φ
        (upd (upd ρb x (M.hmk hd u)) y (M.hmk hd v))) := by
  have hρ : ∀ i, M.hmk hd (Quotient.out (ρb i)) = ρb i := fun i => Quotient.out_eq (ρb i)
  have e1 : Function.update (Function.update (fun i => (Quotient.out (ρb (i - 2))).1) 0 u.1) 1 v.1 =
      fun i => (Function.update (Function.update (fun k => Quotient.out (ρb (k - 2))) 0 u) 1 v i).1 := by
    rw [update_map Subtype.val, update_map Subtype.val]
  rw [e1, ← M.hholds_iff hd hPr (φ.map (renC x y)) (Form.pure_map _ φ hφ),
    holds_map _ _ _ (renC_inj hxy)]
  have e2 : (fun i => M.hmk hd
      (Function.update (Function.update (fun k => Quotient.out (ρb (k - 2))) 0 u) 1 v i)) ∘
      renC x y = upd (upd ρb x (M.hmk hd u)) y (M.hmk hd v) := by
    funext k
    simp only [Function.comp]
    rw [renC_spec (fun k => Quotient.out (ρb k)) hxy u v k, upd_eq_update, upd_eq_update]
    simp only [Function.update_apply]
    split_ifs
    · rfl
    · rfl
    · exact hρ k
  rw [e2]

/-- The data of a host for the level at the top stage. -/
def preHost (L : M.L32X R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ n j m) :
    PreHost where
  W := M.HW L.hd κ
  mem := M.hmem L.hd
  lt := M.hlt L.hd
  ext := by
    intro x y h
    obtain ⟨a, rfl⟩ := M.hmk_surj L.hd x
    obtain ⟨b, rfl⟩ := M.hmk_surj L.hd y
    refine (M.hmk_eq L.hd).mpr ((M.sim_iff_inN L.hd a.2 b.2).mpr (fun z hz => ?_))
    exact h (M.hmk L.hd ⟨z, hz⟩)
  pair := by
    intro x y
    obtain ⟨a, rfl⟩ := M.hmk_surj L.hd x
    obtain ⟨b, rfl⟩ := M.hmk_surj L.hd y
    obtain ⟨c, hc, hcm⟩ := M.pair_lim L.hd L.hκ a.2 b.2
    refine ⟨M.hmk L.hd ⟨c, hc⟩, fun z => ?_⟩
    obtain ⟨z, rfl⟩ := M.hmk_surj L.hd z
    rw [M.hmk_eq L.hd, M.hmk_eq L.hd]
    exact hcm z.1
  union := by
    intro x
    obtain ⟨b, rfl⟩ := M.hmk_surj L.hd x
    obtain ⟨c, hc, hcm⟩ := M.union_lim L.hd L.hκ b.2
    refine ⟨M.hmk L.hd ⟨c, hc⟩, fun z => ?_⟩
    obtain ⟨z, rfl⟩ := M.hmk_surj L.hd z
    constructor
    · intro h
      obtain ⟨y, hzy, hyb⟩ := (hcm z.1).mp h
      obtain ⟨y', hy', hs⟩ := M.k_trans L.hd b.2 hyb
      exact ⟨M.hmk L.hd ⟨y', hy'⟩, M.epsStar_congr L.hd hs (M.inN_refl L.hd b.2) hyb,
        M.epsStar_congr L.hd (M.inN_refl L.hd z.2) hs hzy⟩
    · rintro ⟨y, hyb, hzy⟩
      obtain ⟨y, rfl⟩ := M.hmk_surj L.hd y
      exact (hcm z.1).mpr ⟨y.1, hzy, hyb⟩
  inf := by
    have nn := L.nums
    obtain ⟨o0, ho0⟩ := nn.tot 0
    refine ⟨M.hmk L.hd ⟨ol, M.olκ L⟩, ⟨M.hmk L.hd ⟨o0, M.numκ L ho0⟩, nn.mem _ _ ho0, fun z => ?_⟩,
      fun x hx => ?_⟩
    · obtain ⟨z, rfl⟩ := M.hmk_surj L.hd z
      exact nn.zero o0 z.1 ho0
    · obtain ⟨a, rfl⟩ := M.hmk_surj L.hd x
      obtain ⟨i, o, hio, hs⟩ := nn.onto a.1 hx
      obtain ⟨o', ho'⟩ := nn.tot (i + 1)
      refine ⟨M.hmk L.hd ⟨o', M.numκ L ho'⟩, nn.mem _ _ ho', fun z => ?_⟩
      obtain ⟨z, rfl⟩ := M.hmk_surj L.hd z
      have e : M.hmk L.hd a = M.hmk L.hd ⟨o, M.numκ L hio⟩ := (M.hmk_eq L.hd).mpr hs
      rw [e, M.hmk_eq L.hd]
      exact nn.succ i o o' z.1 hio ho'
  sep := by
    intro φ hφ ρb x ab
    obtain ⟨a, rfl⟩ := M.hmk_surj L.hd ab
    have hρ : ∀ i, M.hmk L.hd (Quotient.out (ρb i)) = ρb i := fun i => Quotient.out_eq (ρb i)
    obtain ⟨b, hb, hbm⟩ := M.s_sep L.hd L.hPr L.hκ.1 L.sep (toCF (φ.map (renS x)))
      (ρ := fun i => (Quotient.out (ρb (i - 1))).1) (fun i => (Quotient.out (ρb (i - 1))).2) a.2
    refine ⟨M.hmk L.hd ⟨b, hb⟩, fun y => ?_⟩
    obtain ⟨y, rfl⟩ := M.hmk_surj L.hd y
    refine (hbm y.1 y.2).trans (and_congr_right fun _ => ?_)
    have e1 : Function.update (fun i => (Quotient.out (ρb (i - 1))).1) 0 y.1 =
        fun i => (Function.update (fun k => Quotient.out (ρb (k - 1))) 0 y i).1 :=
      (update_map Subtype.val (fun k => Quotient.out (ρb (k - 1))) 0 y).symm
    rw [e1, ← M.hholds_iff L.hd L.hPr (φ.map (renS x)) (Form.pure_map _ φ hφ), holds_map _ _ _ (renS_inj x)]
    have e2 : (fun i => M.hmk L.hd (Function.update (fun k => Quotient.out (ρb (k - 1))) 0 y i)) ∘
        renS x = upd ρb x (M.hmk L.hd y) := by
      funext k
      simp only [Function.comp]
      rw [renS_spec (fun k => Quotient.out (ρb k)) x y k, upd_eq_update]
      by_cases h : k = x
      · subst h
        simp
      · simp [Function.update_of_ne h, hρ]
    rw [e2]
  coll := by
    intro φ hφ ρb x y ab hxy h
    obtain ⟨a, rfl⟩ := M.hmk_surj L.hd ab
    have key := fun u v => M.coll_key L.hd L.hPr φ hφ hxy ρb u v
    obtain ⟨b, hb, hbm⟩ := M.s_coll L.hd L.hPr L.hκ.1 L.coll (toCF (φ.map (renC x y))) 0 1
      (ρ := fun i => (Quotient.out (ρb (i - 2))).1) (fun i => (Quotient.out (ρb (i - 2))).2) a.2
      (fun u hu hua => by
        obtain ⟨v, hv⟩ := h (M.hmk L.hd ⟨u, hu⟩) hua
        obtain ⟨v, rfl⟩ := M.hmk_surj L.hd v
        exact ⟨v.1, v.2, (key ⟨u, hu⟩ v).mpr hv⟩)
    refine ⟨M.hmk L.hd ⟨b, hb⟩, fun u hu => ?_⟩
    obtain ⟨u, rfl⟩ := M.hmk_surj L.hd u
    obtain ⟨v, hv, hvb, hψ⟩ := hbm u.1 u.2 hu
    exact ⟨M.hmk L.hd ⟨v, hv⟩, hvb, (key u ⟨v, hv⟩).mp hψ⟩
  lt_irrefl := by
    intro x
    obtain ⟨a, rfl⟩ := M.hmk_surj L.hd x
    exact M.lt_irrefl L.hd (M.inN_refl L.hd a.2)
  lt_trans := by
    intro x y z
    obtain ⟨a, rfl⟩ := M.hmk_surj L.hd x
    obtain ⟨b, rfl⟩ := M.hmk_surj L.hd y
    obtain ⟨c, rfl⟩ := M.hmk_surj L.hd z
    exact fun h1 h2 => M.lt_trans' L.hd L.hPr h1 h2
  lt_tri := by
    intro x y
    obtain ⟨a, rfl⟩ := M.hmk_surj L.hd x
    obtain ⟨b, rfl⟩ := M.hmk_surj L.hd y
    rcases M.lt_tri L.hd L.hPr (M.inN_refl L.hd a.2) (M.inN_refl L.hd b.2) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ((M.hmk_eq L.hd).mpr h))
    · exact Or.inr (Or.inr h)
  least := by
    rintro x ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := M.hmk_surj L.hd x
    obtain ⟨y, rfl⟩ := M.hmk_surj L.hd y
    obtain ⟨c, hc, hca, hmin⟩ := M.s_least L.hd L.hPr L.hκ.1 L.wleast a.2 ⟨y.1, y.2, hy⟩
    refine ⟨M.hmk L.hd ⟨c, hc⟩, hca, fun b hb => ?_⟩
    obtain ⟨b, rfl⟩ := M.hmk_surj L.hd b
    exact hmin b.1 b.2 hb
  mem_lt := by
    intro x y h
    obtain ⟨a, rfl⟩ := M.hmk_surj L.hd x
    obtain ⟨b, rfl⟩ := M.hmk_surj L.hd y
    exact M.eps_lt L.hd L.hPr (M.inN_refl L.hd b.2) h
  cover := by
    intro x
    obtain ⟨a, rfl⟩ := M.hmk_surj L.hd x
    obtain ⟨T, hT, hc⟩ := M.cover_lim L.hd L.hPr L.hq0 L.hκ a.2
    refine ⟨M.hmk L.hd ⟨T, hT⟩, fun b hb => ?_⟩
    obtain ⟨b, rfl⟩ := M.hmk_surj L.hd b
    exact hc b.1 hb

/-- **The host of Lemma 3.2**: the level at the top stage, with membership and the canonical
order. -/
def host (L : M.L32X R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ n j m) :
    Host := (M.preHost L).toHost

end host

end Model

end NFUCut



/-!
# Phase 0, part 7: numbers and levels of the host of Lemma 3.2
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

section tower

variable {R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ : V} {n j m : M.Num}
/-- `b` is the name of the level at the `i`-th stage `ξ`. -/
def LevAt (P W q0 : V) (j i : M.Num) (ξ b : V) : Prop :=
  ∃ p0, M.SAt P W j i ξ p0 ∧ M.mem (M.quad j.1 ξ q0 b) P

variable (L : M.L32X R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ n j m)
include L

/-- The set denoted by a name of rank below `κ`, as an element of the host. -/
def st (a : V) (ha : M.InNRaw P th io M.nat j.1 κ a) : (M.host L).W := M.hmk L.hd ⟨a, ha⟩

theorem mem_st {a b : V} {ha : M.InNRaw P th io M.nat j.1 κ a} {hb : M.InNRaw P th io M.nat j.1 κ b} :
    M.st L a ha ∈ M.st L b hb ↔ M.EpsStarRaw P th io M.nat j.1 tp F a b := Iff.rfl

theorem lt_st {a b : V} {ha : M.InNRaw P th io M.nat j.1 κ a} {hb : M.InNRaw P th io M.nat j.1 κ b} :
    (M.host L).lt (M.st L a ha) (M.st L b hb) ↔ M.Lt P j.1 tp F Pr a b := Iff.rfl

theorem st_eq {a b : V} {ha : M.InNRaw P th io M.nat j.1 κ a} {hb : M.InNRaw P th io M.nat j.1 κ b} :
    M.st L a ha = M.st L b hb ↔ M.SimRaw P j.1 tp F a b := M.hmk_eq L.hd

theorem st_surj (x : (M.host L).W) : ∃ a ha, x = M.st L a ha := by
  obtain ⟨a, rfl⟩ := M.hmk_surj L.hd x
  exact ⟨a.1, a.2, rfl⟩

/-! ### The numbers -/

/-- The number of the host that corresponds to a number of the model. -/
noncomputable def num (i : M.Num) : (M.host L).W :=
  M.st L (Classical.choose (L.nums.tot i)) (M.numκ L (Classical.choose_spec (L.nums.tot i)))

theorem num_eq {i : M.Num} {o : V} (h : M.mem (M.op i.1 o) Nm) :
    M.num L i = M.st L o (M.numκ L h) := by
  have e := L.nums.fn _ _ _ (Classical.choose_spec (L.nums.tot i)) h
  refine (M.st_eq L).mpr ?_
  rw [e]
  exact M.inN_refl L.hd (M.numκ L h)

theorem num_zero : M.num L 0 = (M.host L).emp := by
  obtain ⟨o, ho⟩ := L.nums.tot 0
  rw [M.num_eq L ho]
  refine (M.host L).ext' fun z => ⟨fun h => ?_, fun h => ((M.host L).not_mem_emp z h).elim⟩
  obtain ⟨z', hz', rfl⟩ := M.st_surj L z
  exact (L.nums.zero o z' ho h).elim

theorem num_succ (i : M.Num) : M.num L (i + 1) = (M.host L).suc (M.num L i) := by
  obtain ⟨o, ho⟩ := L.nums.tot i
  obtain ⟨o', ho'⟩ := L.nums.tot (i + 1)
  rw [M.num_eq L ho, M.num_eq L ho']
  refine (M.host L).ext' fun z => ?_
  obtain ⟨z', hz', rfl⟩ := M.st_surj L z
  rw [(M.host L).mem_suc, M.st_eq L]
  exact L.nums.succ i o o' z' ho ho'

theorem num_inj {i i' : M.Num} (h : M.num L i = M.num L i') : i = i' := by
  obtain ⟨o, ho⟩ := L.nums.tot i
  obtain ⟨o', ho'⟩ := L.nums.tot i'
  rw [M.num_eq L ho, M.num_eq L ho'] at h
  exact L.nums.inj i i' o o' ho ho' ((M.st_eq L).mp h)

theorem num_mem {i i' : M.Num} : M.num L i ∈ M.num L i' ↔ i + 1 ≤ i' := by
  obtain ⟨o, ho⟩ := L.nums.tot i
  obtain ⟨o', ho'⟩ := L.nums.tot i'
  rw [M.num_eq L ho, M.num_eq L ho']
  exact L.ord i i' o o' ho ho'

theorem mem_ol {z : (M.host L).W} : z ∈ M.st L ol (M.olκ L) ↔ ∃ i, z = M.num L i := by
  constructor
  · intro h
    obtain ⟨z', hz', rfl⟩ := M.st_surj L z
    obtain ⟨i, o, hio, hs⟩ := L.nums.onto z' h
    exact ⟨i, by rw [M.num_eq L hio]; exact (M.st_eq L).mpr hs⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨o, ho⟩ := L.nums.tot i
    rw [M.num_eq L ho]
    exact L.nums.mem _ _ ho

/-- The set denoted by `ol` is the `ω` of the host. -/
theorem om_eq : M.st L ol (M.olκ L) = (M.host L).om := by
  refine (M.host L).om_eq_of_ind ((M.host L).ind_iff.mpr ⟨?_, fun x hx => ?_⟩) (fun x hx => ?_)
  · rw [← M.num_zero L]
    exact (M.mem_ol L).mpr ⟨0, rfl⟩
  · obtain ⟨i, rfl⟩ := (M.mem_ol L).mp hx
    rw [← M.num_succ L]
    exact (M.mem_ol L).mpr ⟨i + 1, rfl⟩
  · obtain ⟨i, rfl⟩ := (M.mem_ol L).mp hx
    rcases M.num_cases i with e0 | ⟨k, ek⟩
    · have ei : i = 0 := e0
      rw [ei]
      exact Or.inl (M.num_zero L)
    · have ei : i = k + 1 := by rw [ek, M.nsucc_eq_add_one]
      rw [ei]
      exact Or.inr ⟨M.num L k, (M.mem_ol L).mpr ⟨k, rfl⟩, M.num_succ L k⟩

theorem num_mem_om (i : M.Num) : M.num L i ∈ (M.host L).om := by
  rw [← M.om_eq L]
  exact (M.mem_ol L).mpr ⟨i, rfl⟩

theorem mem_om_iff {z : (M.host L).W} : z ∈ (M.host L).om ↔ ∃ i, z = M.num L i := by
  rw [← M.om_eq L]
  exact M.mem_ol L

/-- The members of the number that corresponds to `k` correspond to the numbers below `k`. -/
theorem mem_num {z : (M.host L).W} {k : M.Num} :
    z ∈ M.num L k ↔ ∃ i, i + 1 ≤ k ∧ z = M.num L i := by
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := (M.mem_om_iff L).mp ((M.host L).mem_om_of_mem (M.num_mem_om L k) h)
    exact ⟨i, (M.num_mem L).mp h, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact (M.num_mem L).mpr hi

/-! ### The levels -/

theorem lev_ex {i : M.Num} (hi : i ≤ m) : ∃ ξ b, M.LevAt P W q0 j i ξ b := by
  obtain ⟨ξ, p0, hs⟩ := M.sat_tot L.ss (le_trans hi (M.le_add_one m))
  obtain ⟨b, hb⟩ := M.lev_name L.hd L.hq0 (L.hd.hth.fld _ _ (M.sat_le_top L.ss hs)).1
  exact ⟨ξ, b, p0, hs, hb⟩

theorem lev_stage {i : M.Num} {ξ b : V} (h : M.LevAt P W q0 j i ξ b) : M.mem (M.op ξ ξ) th := by
  obtain ⟨p0, hs, hb⟩ := h
  exact (L.hd.hth.fld _ _ (M.sat_le_top L.ss hs)).1

theorem lev_lt {i : M.Num} {ξ b : V} (h : M.LevAt P W q0 j i ξ b) (hi : i ≤ m) :
    M.mem (M.op ξ κ) th ∧ ξ ≠ κ := by
  obtain ⟨p0, hs, hb⟩ := h
  obtain ⟨ξ', p', h2⟩ := M.sat_tot L.ss (i := i + 1) (add_le_add hi (le_refl 1))
  obtain ⟨lt, ne⟩ := M.sat_lt L.hd L.hq L.hSg L.ss L.hunb hs h2
  have le2 := M.sat_le_top L.ss h2
  exact ⟨L.hd.hth.trans _ _ _ lt le2, M.wo_ne_of_lt_le L.hd.hth lt ne le2⟩

theorem lev_inN {i : M.Num} {ξ b : V} (h : M.LevAt P W q0 j i ξ b) (hi : i ≤ m) :
    M.InNRaw P th io M.nat j.1 κ b := by
  obtain ⟨lt, ne⟩ := M.lev_lt L h hi
  obtain ⟨p0, hs, hb⟩ := h
  exact M.rank_inN (M.lev_rank L.hd L.hq0 hb) lt ne

theorem lev_fun {i : M.Num} {ξ b ξ' b' : V} (h : M.LevAt P W q0 j i ξ b)
    (h' : M.LevAt P W q0 j i ξ' b') : ξ = ξ' ∧ b = b' := by
  obtain ⟨p0, hs, hb⟩ := h
  obtain ⟨p0', hs', hb'⟩ := h'
  obtain ⟨e, -⟩ := M.sat_fun L.hd L.ss hs hs'
  rw [← e] at hb'
  exact ⟨e, L.hd.hP.fn _ _ _ _ _ hb hb'⟩

theorem lev_next {i : M.Num} {ν b0 ξ b : V} (h0 : M.LevAt P W q0 j i ν b0)
    (h1 : M.LevAt P W q0 j (i + 1) ξ b) :
    M.IsNext P th Sg j ν ξ ∧ M.mem (M.op ν ξ) th ∧ ν ≠ ξ := by
  obtain ⟨p0, hs, hb⟩ := h0
  obtain ⟨p1, hs1, hb1⟩ := h1
  exact ⟨(M.sat_step L.ss hs hs1).1, M.sat_lt L.hd L.hq L.hSg L.ss L.hunb hs hs1⟩

/-- The members of a level are the sets with a name of rank below its stage. -/
theorem mem_lev {i : M.Num} {ξ b : V} (h : M.LevAt P W q0 j i ξ b) (hi : i ≤ m)
    (z : (M.host L).W) : z ∈ M.st L b (M.lev_inN L h hi) ↔
      ∃ y hy, M.InNRaw P th io M.nat j.1 ξ y ∧ z = M.st L y hy := by
  have hξ := M.lev_stage L h
  obtain ⟨lt, ne⟩ := M.lev_lt L h hi
  have hb := h.choose_spec.2
  obtain ⟨z', hz', rfl⟩ := M.st_surj L z
  rw [M.mem_st L, M.lev_epsStar L.hd L.hq0 hξ hb z']
  constructor
  · rintro ⟨y', hy', hs⟩
    exact ⟨y', M.inN_mono L.hd hy' lt, hy', (M.st_eq L).mpr hs⟩
  · rintro ⟨y, hy, hyξ, e⟩
    exact ⟨y, hyξ, (M.st_eq L).mp e⟩

theorem lev_trans {i : M.Num} {ξ b : V} (h : M.LevAt P W q0 j i ξ b) (hi : i ≤ m)
    (x y : (M.host L).W) (hxy : x ∈ y) (hy : y ∈ M.st L b (M.lev_inN L h hi)) :
    x ∈ M.st L b (M.lev_inN L h hi) := by
  obtain ⟨lt, ne⟩ := M.lev_lt L h hi
  obtain ⟨y1, hy1, hy1ξ, rfl⟩ := (M.mem_lev L h hi y).mp hy
  obtain ⟨x', hx', rfl⟩ := M.st_surj L x
  obtain ⟨x'', hx''ξ, hs⟩ := M.k_trans L.hd hy1ξ ((M.mem_st L).mp hxy)
  exact (M.mem_lev L h hi _).mpr ⟨x'', M.inN_mono L.hd hx''ξ lt, hx''ξ, (M.st_eq L).mpr hs⟩

theorem lev_cons {i : M.Num} {ν b0 ξ b : V} (h0 : M.LevAt P W q0 j i ν b0)
    (h1 : M.LevAt P W q0 j (i + 1) ξ b) (hi : i + 1 ≤ m) :
    M.st L b0 (M.lev_inN L h0 (le_trans (M.le_add_one i) hi)) ∈ M.st L b (M.lev_inN L h1 hi) := by
  obtain ⟨-, lt, ne⟩ := M.lev_next L h0 h1
  have hb0 := h0.choose_spec.2
  exact (M.mem_lev L h1 hi _).mpr ⟨b0, _, M.rank_inN (M.lev_rank L.hd L.hq0 hb0) lt ne, rfl⟩

theorem lev_om {ν b0 ξ b : V} (h0 : M.LevAt P W q0 j 0 ν b0)
    (h1 : M.LevAt P W q0 j (0 + 1) ξ b) (hi : (0 : M.Num) + 1 ≤ m) :
    (M.host L).om ∈ M.st L b (M.lev_inN L h1 hi) := by
  obtain ⟨-, lt, ne⟩ := M.lev_next L h0 h1
  obtain ⟨p0, hs, hb⟩ := h0
  obtain ⟨e, -⟩ := M.sat_fun L.hd L.ss hs (M.sat_zero L.hd L.ss L.nums.hol)
  rw [e] at lt ne
  rw [← M.om_eq L]
  exact (M.mem_lev L h1 hi _).mpr ⟨ol, _, M.rank_inN (M.ordName_rank L.hd L.hqo L.nums.hol) lt ne, rfl⟩

theorem lev_sub {i : M.Num} {ν b0 ξ b : V} (h0 : M.LevAt P W q0 j i ν b0)
    (h1 : M.LevAt P W q0 j (i + 1) ξ b) (hi : i + 1 ≤ m)
    (x y : (M.host L).W) (hsub : (M.host L).Sub x y) (hy : y ∈ M.st L b (M.lev_inN L h1 hi)) :
    x ∈ M.st L b (M.lev_inN L h1 hi) := by
  obtain ⟨hnext, -, -⟩ := M.lev_next L h0 h1
  obtain ⟨lt, ne⟩ := M.lev_lt L h1 hi
  obtain ⟨y1, hy1, hy1ξ, rfl⟩ := (M.mem_lev L h1 hi y).mp hy
  obtain ⟨x', hx', rfl⟩ := M.st_surj L x
  obtain ⟨x'', hx''ξ, hs⟩ := M.k_sub L.hd L.hPr L.hq L.hNu L.hSg hnext L.hσ'.1 L.hσ'.2 hx' hy1ξ
    (fun z hz => by
      obtain ⟨z', hz', hsz⟩ := M.k_trans L.hd hx' hz
      have h1' : M.st L z' hz' ∈ M.st L x' hx' :=
        (M.mem_st L).mpr (M.epsStar_congr L.hd hsz (M.inN_refl L.hd hx') hz)
      have h2 := (M.mem_st L).mp (hsub _ h1')
      exact M.epsStar_congr L.hd (M.sim_symm L.hd hsz) (M.inN_refl L.hd hy1) h2)
  exact (M.mem_lev L h1 hi _).mpr ⟨x'', M.inN_mono L.hd hx''ξ lt, hx''ξ, (M.st_eq L).mpr hs⟩

theorem lev_cover {i : M.Num} {ν b0 ξ b : V} (h0 : M.LevAt P W q0 j i ν b0)
    (h1 : M.LevAt P W q0 j (i + 1) ξ b) (hi : i + 1 ≤ m)
    (a : (M.host L).W) (ha : a ∈ M.st L b (M.lev_inN L h1 hi)) :
    ∃ T, T ∈ M.st L b (M.lev_inN L h1 hi) ∧ ∀ c, (M.host L).lt c a → c ∈ T := by
  obtain ⟨hnext, -, -⟩ := M.lev_next L h0 h1
  obtain ⟨lt, ne⟩ := M.lev_lt L h1 hi
  obtain ⟨a1, ha1, ha1ξ, rfl⟩ := (M.mem_lev L h1 hi a).mp ha
  obtain ⟨T, hT, hc⟩ := M.cover_lim L.hd L.hPr L.hq0 (M.next_lim L.hd L.hPr L.hq L.hSg hnext) ha1ξ
  refine ⟨M.st L T (M.inN_mono L.hd hT lt), (M.mem_lev L h1 hi _).mpr ⟨T, _, hT, rfl⟩, fun c hc' => ?_⟩
  obtain ⟨c', hc'', rfl⟩ := M.st_surj L c
  exact (M.mem_st L).mpr (hc c' ((M.lt_st L).mp hc'))

theorem lev_kcoll {i : M.Num} {ν b0 ξ b : V} (h0 : M.LevAt P W q0 j i ν b0)
    (h1 : M.LevAt P W q0 j (i + 1) ξ b) (hi : i + 1 ≤ m)
    (Rl : (M.host L).W → (M.host L).W → Prop) (hR : Def2 (M.host L) Rl)
    (a : (M.host L).W) (ha : a ∈ M.st L b (M.lev_inN L h1 hi))
    (h : ∀ u, u ∈ a → ∃ v, v ∈ M.st L b (M.lev_inN L h1 hi) ∧ Rl u v) :
    ∃ c, c ∈ M.st L b (M.lev_inN L h1 hi) ∧ ∀ u, u ∈ a → ∃ v, v ∈ c ∧ Rl u v := by
  obtain ⟨hnext, -, -⟩ := M.lev_next L h0 h1
  obtain ⟨lt, ne⟩ := M.lev_lt L h1 hi
  obtain ⟨φ, ρb, x, y, hφ, hxy, hRφ⟩ := hR
  obtain ⟨a1, ha1, ha1ξ, rfl⟩ := (M.mem_lev L h1 hi a).mp ha
  have key := fun u v => M.coll_key L.hd L.hPr φ hφ hxy ρb u v
  obtain ⟨γ, g1, g2, hγ⟩ := M.s_kcoll L.hd L.hPr L.hq L.hNu L.hSg hnext lt L.hσ'.1 L.hσ'.2 L.hδ.1 L.hδ.2
    (toCF (φ.map (renC x y))) 0 1 (ρ := fun i => (Quotient.out (ρb (i - 2))).1)
    (fun i => (Quotient.out (ρb (i - 2))).2) ha1ξ
    (fun u hu hua => by
      have huκ := M.inN_mono L.hd hu lt
      obtain ⟨v, hv, hRv⟩ := h (M.st L u huκ) ((M.mem_st L).mpr hua)
      obtain ⟨v1, hv1, hv1ξ, rfl⟩ := (M.mem_lev L h1 hi v).mp hv
      exact ⟨v1, hv1ξ, (key ⟨u, huκ⟩ ⟨v1, hv1⟩).mpr ((hRφ _ _).mp hRv)⟩)
  have hγγ := (L.hd.hth.fld _ _ g1).1
  obtain ⟨T, hT⟩ := M.lev_name L.hd L.hq0 hγγ
  have hTξ : M.InNRaw P th io M.nat j.1 ξ T := M.rank_inN (M.lev_rank L.hd L.hq0 hT) g1 g2
  refine ⟨M.st L T (M.inN_mono L.hd hTξ lt), (M.mem_lev L h1 hi _).mpr ⟨T, _, hTξ, rfl⟩,
    fun u hu => ?_⟩
  obtain ⟨u', hu', rfl⟩ := M.st_surj L u
  obtain ⟨u'', hu''ξ, hs⟩ := M.k_trans L.hd ha1ξ ((M.mem_st L).mp hu)
  have hu''κ := M.inN_mono L.hd hu''ξ lt
  have e : M.st L u' hu' = M.st L u'' hu''κ := (M.st_eq L).mpr hs
  obtain ⟨v, hv, hψ⟩ := hγ u'' hu''ξ
    (M.epsStar_congr L.hd hs (M.inN_refl L.hd ha1) ((M.mem_st L).mp hu))
  have hvκ := M.inN_mono L.hd (M.inN_mono L.hd hv g1) lt
  refine ⟨M.st L v hvκ, (M.mem_st L).mpr ((M.lev_epsStar L.hd L.hq0 hγγ hT v).mpr
    ⟨v, hv, M.inN_refl L.hd hvκ⟩), ?_⟩
  rw [e]
  exact (hRφ _ _).mpr ((key ⟨u'', hu''κ⟩ ⟨v, hvκ⟩).mp hψ)

end tower

end Model

end NFUCut



/-!
# Phase 0, part 8: the ladder of closed levels and the tower

`exists_host_tower`: in a model of NFU + Infinity, for every number `d₀` such that
`3(d₀ + 3) + 2` is calm there are a host, a tower in it of height `d₀ + 1`, and a one-to-one
correspondence between the numbers of the model and the numbers of the host.
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

section tower

variable {R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ : V} {n j m : M.Num}
variable (L : M.L32X R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ n j m)
include L

/-- A name of an ordered pair denotes the ordered pair of the host. -/
theorem st_opair {o p0 x c : V} (ho : M.InNRaw P th io M.nat j.1 κ o)
    (hp : M.InNRaw P th io M.nat j.1 κ p0) (hx : M.InNRaw P th io M.nat j.1 κ x)
    (hs : M.SimRaw P j.1 tp F x c) (hop : M.IsOPairN P th io F tp j o p0 c) :
    M.st L x hx = (M.host L).op (M.st L o ho) (M.st L p0 hp) := by
  obtain ⟨s, q, hss, hqq, hs1, hq1, hc1⟩ := hop
  obtain ⟨βx, βc, rx, rc, hβx, hβc⟩ := M.sim_names L.hd hs
  have hxc := (M.sim_iff_ext L.hd rx rc hβx hβc).mp hs
  have hsx := (hxc s).mpr ((hc1 s).mpr (Or.inl hss))
  have hqx := (hxc q).mpr ((hc1 q).mpr (Or.inr hqq))
  obtain ⟨s', hs', hss'⟩ := M.k_trans L.hd hx hsx
  obtain ⟨q', hq', hqq'⟩ := M.k_trans L.hd hx hqx
  have e1 : M.st L s' hs' = (M.host L).sg (M.st L o ho) := by
    refine (M.host L).ext' fun z => ?_
    obtain ⟨z', hz', rfl⟩ := M.st_surj L z
    rw [(M.host L).mem_sg, M.st_eq L]
    constructor
    · intro h
      have h1 := (hs1 z').mp (M.epsStar_congr L.hd (M.inN_refl L.hd hz') (M.sim_symm L.hd hss')
        ((M.mem_st L).mp h))
      exact h1.elim id id
    · intro h
      exact (M.mem_st L).mpr (M.epsStar_congr L.hd (M.inN_refl L.hd hz') hss' ((hs1 z').mpr (Or.inl h)))
  have e2 : M.st L q' hq' = (M.host L).up (M.st L o ho) (M.st L p0 hp) := by
    refine (M.host L).ext' fun z => ?_
    obtain ⟨z', hz', rfl⟩ := M.st_surj L z
    rw [(M.host L).mem_up, M.st_eq L, M.st_eq L]
    constructor
    · intro h
      exact (hq1 z').mp (M.epsStar_congr L.hd (M.inN_refl L.hd hz') (M.sim_symm L.hd hqq')
        ((M.mem_st L).mp h))
    · intro h
      exact (M.mem_st L).mpr (M.epsStar_congr L.hd (M.inN_refl L.hd hz') hqq' ((hq1 z').mpr h))
  have e3 : M.st L x hx = (M.host L).up (M.st L s' hs') (M.st L q' hq') := by
    refine (M.host L).ext' fun z => ?_
    obtain ⟨z', hz', rfl⟩ := M.st_surj L z
    rw [(M.host L).mem_up, M.st_eq L, M.st_eq L]
    constructor
    · intro h
      rcases (hc1 z').mp ((hxc z').mp ((M.mem_st L).mp h)) with h1 | h1
      · exact Or.inl (M.sim_trans L.hd h1 hss')
      · exact Or.inr (M.sim_trans L.hd h1 hqq')
    · rintro (h | h)
      · exact (M.mem_st L).mpr ((hxc z').mpr ((hc1 z').mpr
          (Or.inl (M.sim_trans L.hd h (M.sim_symm L.hd hss')))))
      · exact (M.mem_st L).mpr ((hxc z').mpr ((hc1 z').mpr
          (Or.inr (M.sim_trans L.hd h (M.sim_symm L.hd hqq')))))
  rw [e3, e1, e2]
  rfl

/-- The members of the internal sequence are the ordered pairs of a number and the level with
that index. -/
theorem mem_lam (x : (M.host L).W) : x ∈ M.st L Lam L.lam.1 ↔
    ∃ (i : M.Num) (ξ b : V) (hi : i ≤ m) (h : M.LevAt P W q0 j i ξ b),
      x = (M.host L).op (M.num L i) (M.st L b (M.lev_inN L h hi)) := by
  obtain ⟨x, hx, rfl⟩ := M.st_surj L x
  constructor
  · intro hmem
    obtain ⟨i, o, p0, c, hi, hle, hio, hip, hop, hs⟩ := (L.lam.2 x).mp ((M.mem_st L).mp hmem)
    have hi' : (⟨i, hi⟩ : M.Num) ≤ m := (M.leRaw_iff M.adG_spec ⟨i, hi⟩ m).mp hle
    obtain ⟨y1, ξ, pp, a1, a2, a3⟩ := (L.kn i p0).mp hip
    have hlev : M.LevAt P W q0 j ⟨i, hi⟩ ξ p0 := ⟨pp, ⟨y1, a1, a2⟩, a3⟩
    refine ⟨⟨i, hi⟩, ξ, p0, hi', hlev, ?_⟩
    rw [M.num_eq L (i := ⟨i, hi⟩) hio]
    exact M.st_opair L (M.numκ L hio) (M.lev_inN L hlev hi') hx hs hop
  · rintro ⟨i, ξ, b, hi, hlev, e⟩
    obtain ⟨o, ho⟩ := L.nums.tot i
    have hb := M.lev_inN L hlev hi
    obtain ⟨c, hc, hop⟩ := M.opair_lim L.hd L.hκ (M.numκ L ho) hb
    have hkn : M.mem (M.op i.1 b) Kn := by
      obtain ⟨pp, ⟨y1, a1, a2⟩, a3⟩ := hlev
      exact (L.kn _ _).mpr ⟨y1, ξ, pp, a1, a2, a3⟩
    have hcl : M.EpsStarRaw P th io M.nat j.1 tp F c Lam :=
      (L.lam.2 c).mpr ⟨i.1, o, b, c, i.2, (M.leRaw_iff M.adG_spec i m).mpr hi, ho, hkn, hop,
        M.inN_refl L.hd hc⟩
    have e2 : M.st L c hc = (M.host L).op (M.num L i) (M.st L b hb) := by
      rw [M.num_eq L ho]
      exact M.st_opair L (M.numκ L ho) hb hc (M.inN_refl L.hd hc) hop
    rw [e, ← e2]
    exact (M.mem_st L).mpr hcl

theorem app_lam {α La : (M.host L).W} : (M.host L).App (M.st L Lam L.lam.1) α La ↔
    ∃ (i : M.Num) (ξ b : V) (hi : i ≤ m) (h : M.LevAt P W q0 j i ξ b),
      α = M.num L i ∧ La = M.st L b (M.lev_inN L h hi) := by
  rw [(M.host L).app_iff, M.mem_lam L]
  constructor
  · rintro ⟨i, ξ, b, hi, h, e⟩
    obtain ⟨e1, e2⟩ := (M.host L).op_inj e
    exact ⟨i, ξ, b, hi, h, e1, e2⟩
  · rintro ⟨i, ξ, b, hi, h, rfl, rfl⟩
    exact ⟨i, ξ, b, hi, h, rfl⟩

theorem num_ne_emp {i : M.Num} (h : M.num L i ≠ (M.host L).emp) : ∃ k, i = k + 1 := by
  rcases M.num_cases i with e0 | ⟨k, ek⟩
  · have ei : i = 0 := e0
    rw [ei] at h
    exact (h (M.num_zero L)).elim
  · exact ⟨k, by rw [ek, M.nsucc_eq_add_one]⟩

/-- **The tower of Lemma 3.2.** If `m = d₀ + 2`, the host has a tower of height `d₀ + 1`
whose ladder is the internal sequence of the levels. -/
theorem exists_tower_of (d0 : M.Num) (hm : m = d0 + 1 + 1) :
    ∃ T : Host.Tower (M.host L), T.d = M.num L (d0 + 1) ∧ T.Λ = M.st L Lam L.lam.1 := by
  subst hm
  have hsd : (M.host L).suc ((M.host L).suc (M.num L (d0 + 1))) = M.num L (d0 + 1 + 1 + 1) := by
    rw [← M.num_succ L, ← M.num_succ L]
  refine (M.host L).tower_of_ladder _ _ (M.num_mem_om L _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [M.num_succ L]
    exact (M.host L).suc_ne_emp _
  · refine ⟨fun x hx => ?_, fun a b b' h1 h2 => ?_⟩
    · obtain ⟨i, ξ, b, hi, h, e⟩ := (M.mem_lam L x).mp hx
      exact ⟨_, _, by rw [e]; exact (M.host L).isOp_op _ _⟩
    · obtain ⟨i, ξ, c, hi, h, e1, e2⟩ := (M.app_lam L).mp h1
      obtain ⟨i', ξ', c', hi', h', e1', e2'⟩ := (M.app_lam L).mp h2
      have ei : i = i' := M.num_inj L (e1.symm.trans e1')
      subst ei
      obtain ⟨-, ec⟩ := M.lev_fun L h h'
      subst ec
      rw [e2, e2']
  · intro α hα
    rw [hsd] at hα
    obtain ⟨i, hi, rfl⟩ := (M.mem_num L).mp hα
    have hi' := M.le_of_succ_le_succ hi
    obtain ⟨ξ, b, h⟩ := M.lev_ex L hi'
    exact ⟨_, (M.app_lam L).mpr ⟨i, ξ, b, hi', h, rfl, rfl⟩⟩
  · intro α La h
    obtain ⟨i, ξ, b, hi, hl, rfl, -⟩ := (M.app_lam L).mp h
    rw [hsd]
    exact (M.num_mem L).mpr (add_le_add hi (le_refl 1))
  · intro k La Lb h1 h2
    obtain ⟨i, ν, b0, hi, h0, rfl, rfl⟩ := (M.app_lam L).mp h1
    obtain ⟨i', ξ, b, hi', h1', e1, rfl⟩ := (M.app_lam L).mp h2
    rw [← M.num_succ L] at e1
    have ei := M.num_inj L e1
    subst ei
    exact M.lev_cons L h0 h1' hi'
  · intro α La h x y hxy hy
    obtain ⟨i, ξ, b, hi, hl, -, rfl⟩ := (M.app_lam L).mp h
    exact M.lev_trans L hl hi x y hxy hy
  · intro L1 h
    obtain ⟨i, ξ, b, hi, hl, e1, rfl⟩ := (M.app_lam L).mp h
    rw [← M.num_zero L, ← M.num_succ L] at e1
    have ei := M.num_inj L e1
    subst ei
    obtain ⟨ν, b0, h0⟩ := M.lev_ex L (i := 0) zero_le
    exact M.lev_om L h0 hl hi
  · intro α La h hα0 x y hsub hy
    obtain ⟨i, ξ, b, hi, hl, rfl, rfl⟩ := (M.app_lam L).mp h
    obtain ⟨k, rfl⟩ := M.num_ne_emp L hα0
    obtain ⟨ν, b0, h0⟩ := M.lev_ex L (le_trans (M.le_add_one k) hi)
    exact M.lev_sub L h0 hl hi x y hsub hy
  · intro α La h hα0 Rl hR a ha hall
    obtain ⟨i, ξ, b, hi, hl, rfl, rfl⟩ := (M.app_lam L).mp h
    obtain ⟨k, rfl⟩ := M.num_ne_emp L hα0
    obtain ⟨ν, b0, h0⟩ := M.lev_ex L (le_trans (M.le_add_one k) hi)
    exact M.lev_kcoll L h0 hl hi Rl hR a ha hall
  · intro α La h hα0 a ha
    obtain ⟨i, ξ, b, hi, hl, rfl, rfl⟩ := (M.app_lam L).mp h
    obtain ⟨k, rfl⟩ := M.num_ne_emp L hα0
    obtain ⟨ν, b0, h0⟩ := M.lev_ex L (le_trans (M.le_add_one k) hi)
    exact M.lev_cover L h0 hl hi a ha

theorem numIso : NumIso (M.host L) (M.num L) where
  zero := M.num_zero L
  succ := M.num_succ L
  inj := fun _ _ h => M.num_inj L h
  onto := fun _ => M.mem_om_iff L
  mem := fun _ _ => M.num_mem L

end tower

/-- **Phase 0.** In a model of NFU + Infinity, if `3(d₀ + 3) + 2` is calm, there are a host,
a tower in it of height `d₀ + 1`, and a correspondence between the numbers of the model and
the numbers of the host under which the height of the tower corresponds to `d₀ + 1`. -/
theorem exists_host_tower {d0 : M.Num}
    (hcalm : M.InS (3 * (d0 + 1 + 1 + 1) + 1 + 1 : M.Num).1) :
    ∃ (H : Host) (T : Host.Tower H) (num : M.Num → H.W), NumIso H num ∧ T.d = num (d0 + 1) := by
  obtain ⟨R, P, th, io, Nt, nle, p, F, d, tp, qo, Nu, Pr, κ, ol, Nm, l, Sg, q1, W, q0, Kn, Lam, σ', δ, L⟩ :=
    M.l32x_calm (m := d0 + 1 + 1) hcalm
  obtain ⟨T, hT, -⟩ := M.exists_tower_of L d0 rfl
  exact ⟨M.host L, T, M.num L, M.numIso L, hT⟩

end Model

end NFUCut



/-!
# Phase 2, NFU side, part 1: the host of Lemma 3.2 computes with the numbers of the model

The graph of a set function on the numbers of the model is a function of the host
(`exists_inner_graph`). Hence induction over the numbers of the model is available for
definable relations of the host along set functions (`mixed_ind`), recursions carried out in
the host agree with the recursions of the model (`rec_transfer`), and the host has the
arithmetic of the model (`arith`).
-/

namespace Host

/-- `f` is a computation, of length `b`, of the recursion with the initial value `c` and the
step relation `S`. -/
def Cert (H : Host) (S : H.W → H.W → Prop) (f c b : H.W) : Prop :=
  H.FunOn f (H.suc b) ∧ H.App f H.emp c ∧
    ∀ i u v, i ∈ b → H.App f i u → H.App f (H.suc i) v → S u v

/-- The value at `b` of the recursion with the initial value `c` and the step relation `S`. -/
def RecG (H : Host) (S : H.W → H.W → Prop) (c b z : H.W) : Prop :=
  ∃ f, H.Cert S f c b ∧ H.App f b z

end Host

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

/-- The facts about the numbers of the model that the host side uses. -/
theorem nfacts : NFacts M.Num M.expN where
  le_iff := fun a b => Iff.rfl
  total := M.le_total'
  cancel := fun a b c h => M.addN_left_cancel (a := c) (by
    show M.addN c a = M.addN c b
    rw [M.addN_comm c a, M.addN_comm c b]
    exact h)
  not_succ_le := M.not_succ_le
  eq_or_succ_le := fun a b h => M.eq_or_succ_le h
  zero_or_succ := fun a => by
    rcases M.num_cases a with h | ⟨b, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨b, by rw [h, M.nsucc_eq_add_one]⟩
  E_zero := M.expN_zero
  E_add := M.expN_add
  E_one := by
    have h := M.expN_add_one 0
    rw [zero_add] at h
    rw [h, show M.expN (0 : M.Num) = 1 from M.expN_zero]
    exact one_add_one_eq_two
  E_pos := M.one_le_expN
  le_mul_self := M.le_mul_self'
  cast_inj := M.natCast_inj'
  pair_inj := fun x y x' y' h => M.pairN_inj h

/-- The composition of a set function with the assignment of names to the numbers. -/
theorem exists_nmComp {g : M.Num → M.Num} (hg : M.NatFn g) (Nm : V) :
    ∃ Pw, ∀ i o, M.mem (M.op i o) Pw ↔ ∃ k : M.Num, k.1 = i ∧ M.mem (M.op (g k).1 o) Nm := by
  obtain ⟨gs, hgs⟩ := hg
  obtain ⟨Pw, -, hPw⟩ := M.comp (σW [(0, 4), (1, 5), (2, 5)])
    (Fml.ex 3 (Fml.ex 4 (Fml.ex 5 (.and (fPr 0 3 4) (.and (fApp 1 3 5) (fApp 2 5 4)))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 gs) 2 Nm)
  have hPw' : ∀ q, M.mem q Pw ↔ ∃ i o y, q = M.op i o ∧ M.mem (M.op i y) gs ∧
      M.mem (M.op y o) Nm := by
    intro q
    rw [hPw q]
    simp [M.sat_ex, Sat, M.sat_fApp, M.sat_fPr, Function.update_apply]
  refine ⟨Pw, fun i o => ?_⟩
  rw [hPw']
  constructor
  · rintro ⟨i', o', y, e, h1, h2⟩
    obtain ⟨e1, e2⟩ := M.op_inj e
    obtain ⟨k, hk, hy⟩ := (hgs _ _).mp h1
    rw [← hy] at h2
    exact ⟨k, hk.trans e1.symm, e2 ▸ h2⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨i, o, (g k).1, rfl, (hgs _ _).mpr ⟨k, hk, rfl⟩, h⟩

section tower

variable {R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ : V} {n j m : M.Num}
variable (L : M.L32X R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ n j m)
include L

/-- **The graph of a set function, restricted to the numbers up to `k`, is a set of the
host.** -/
theorem exists_inner_graph {g : M.Num → M.Num} (hg : M.NatFn g) (k : M.Num) :
    ∃ f : (M.host L).W, ∀ x, x ∈ f ↔
      ∃ i : M.Num, i ≤ k ∧ x = (M.host L).op (M.num L i) (M.num L (g i)) := by
  obtain ⟨Pw, hPw⟩ := M.exists_nmComp hg Nm
  have ptot : ∀ i : M.Num, i + 1 ≤ k + 1 → ∃ p0, M.mem (M.op i.1 p0) Pw := fun i _ => by
    obtain ⟨o, ho⟩ := L.nums.tot (g i)
    exact ⟨o, (hPw _ _).mpr ⟨i, rfl, ho⟩⟩
  have pfn : ∀ i p0 p', M.mem (M.op i p0) Pw → M.mem (M.op i p') Pw → p0 = p' := by
    intro i p0 p' h h'
    obtain ⟨a, ha, h1⟩ := (hPw _ _).mp h
    obtain ⟨a', ha', h1'⟩ := (hPw _ _).mp h'
    have e : a = a' := Subtype.ext (ha.trans ha'.symm)
    subst e
    exact L.nums.fn _ _ _ h1 h1'
  have pinN : ∀ (i : M.Num) (p0 : V), i + 1 ≤ k + 1 → M.mem (M.op i.1 p0) Pw →
      M.InNRaw P th io M.nat j.1 κ p0 := by
    intro i p0 _ h
    obtain ⟨a, ha, h1⟩ := (hPw _ _).mp h
    exact M.numκ L h1
  obtain ⟨f, hf, hfm⟩ := M.exists_inner_seq' L.hd L.hκ L.nums ptot pfn pinN L.hlκ.1 k (le_refl _)
  refine ⟨M.st L f hf, fun x => ?_⟩
  obtain ⟨x, hx, rfl⟩ := M.st_surj L x
  constructor
  · intro hmem
    obtain ⟨i, o, p0, c, hi, hle, hio, hip, hop, hs⟩ := (hfm x).mp ((M.mem_st L).mp hmem)
    have hi' : (⟨i, hi⟩ : M.Num) ≤ k := (M.leRaw_iff M.adG_spec ⟨i, hi⟩ k).mp hle
    obtain ⟨a, ha, h1⟩ := (hPw _ _).mp hip
    have ea : a = ⟨i, hi⟩ := Subtype.ext ha
    subst ea
    refine ⟨⟨i, hi⟩, hi', ?_⟩
    rw [M.num_eq L (i := ⟨i, hi⟩) hio, M.num_eq L h1]
    exact M.st_opair L (M.numκ L hio) (M.numκ L h1) hx hs hop
  · rintro ⟨i, hi, e⟩
    obtain ⟨o, ho⟩ := L.nums.tot i
    obtain ⟨o', ho'⟩ := L.nums.tot (g i)
    obtain ⟨c, hc, hop⟩ := M.opair_lim L.hd L.hκ (M.numκ L ho) (M.numκ L ho')
    have hcl : M.EpsStarRaw P th io M.nat j.1 tp F c f :=
      (hfm c).mpr ⟨i.1, o, o', c, i.2, (M.leRaw_iff M.adG_spec i k).mpr hi, ho,
        (hPw _ _).mpr ⟨i, rfl, ho'⟩, hop, M.inN_refl L.hd hc⟩
    have e2 : M.st L c hc = (M.host L).op (M.num L i) (M.num L (g i)) := by
      rw [M.num_eq L ho, M.num_eq L ho']
      exact M.st_opair L (M.numκ L ho) (M.numκ L ho') hc (M.inN_refl L.hd hc) hop
    rw [e, ← e2]
    exact (M.mem_st L).mpr hcl

/-- The graph of a set function up to `k`, as a function of the host. -/
theorem inner_app {g : M.Num → M.Num} (hg : M.NatFn g) (k : M.Num) :
    ∃ f : (M.host L).W, (M.host L).IsFun f ∧ ∀ x y, (M.host L).App f x y ↔
      ∃ i : M.Num, i ≤ k ∧ x = M.num L i ∧ y = M.num L (g i) := by
  obtain ⟨f, hf⟩ := M.exists_inner_graph L hg k
  have happ : ∀ x y, (M.host L).App f x y ↔
      ∃ i : M.Num, i ≤ k ∧ x = M.num L i ∧ y = M.num L (g i) := by
    intro x y
    rw [(M.host L).app_iff, hf]
    constructor
    · rintro ⟨i, hi, e⟩
      obtain ⟨e1, e2⟩ := (M.host L).op_inj e
      exact ⟨i, hi, e1, e2⟩
    · rintro ⟨i, hi, rfl, rfl⟩
      exact ⟨i, hi, rfl⟩
  refine ⟨f, ⟨fun q hq => ?_, fun a b b' h h' => ?_⟩, happ⟩
  · obtain ⟨i, -, rfl⟩ := (hf q).mp hq
    exact ⟨_, _, (M.host L).isOp_op _ _⟩
  · obtain ⟨i, -, rfl, rfl⟩ := (happ _ _).mp h
    obtain ⟨i', -, e, rfl⟩ := (happ _ _).mp h'
    rw [M.num_inj L e]

theorem mem_suc_num {x : (M.host L).W} {b : M.Num} :
    x ∈ (M.host L).suc (M.num L b) ↔ ∃ i : M.Num, i ≤ b ∧ x = M.num L i := by
  rw [← M.num_succ L, M.mem_num L]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, M.nfacts.le_of_succ_le_succ hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, M.nfacts.add_le_add_r hi 1, rfl⟩

/-- **Induction over the numbers of the model** for a definable relation of the host along a
set function. -/
theorem mixed_ind (Q : (M.host L).W → (M.host L).W → Prop) (hQ : Def2 (M.host L) Q)
    (g : M.Num → M.Num) (hg : M.NatFn g) (h0 : Q (M.num L 0) (M.num L (g 0)))
    (hs : ∀ b, Q (M.num L b) (M.num L (g b)) → Q (M.num L (b + 1)) (M.num L (g (b + 1)))) :
    ∀ b, Q (M.num L b) (M.num L (g b)) := by
  intro B
  obtain ⟨f, hff, happ⟩ := M.inner_app L hg B
  have key := (M.host L).om_ind
    (fun x => x ∈ (M.host L).suc (M.num L B) → ∃ y, (M.host L).App f x y ∧ Q x y) (by hdef)
    (fun _ => ⟨M.num L (g 0), (happ _ _).mpr ⟨0, M.nfacts.zero_le B, (M.num_zero L).symm, rfl⟩, by
      rw [← M.num_zero L]
      exact h0⟩)
    (fun x hx ih hsx => by
      obtain ⟨i, rfl⟩ := (M.mem_om_iff L).mp hx
      rw [← M.num_succ L i] at hsx ⊢
      obtain ⟨i', hi', e⟩ := (M.mem_suc_num L).mp hsx
      have ei := M.num_inj L e
      subst ei
      have hiB : i ≤ B := le_trans (M.nfacts.le_add i 1) hi'
      obtain ⟨y, hy, hQy⟩ := ih ((M.mem_suc_num L).mpr ⟨i, hiB, rfl⟩)
      obtain ⟨i2, -, e2, rfl⟩ := (happ _ _).mp hy
      have ei2 := M.num_inj L e2
      subst ei2
      exact ⟨M.num L (g (i + 1)), (happ _ _).mpr ⟨i + 1, hi', rfl, rfl⟩, hs i hQy⟩)
  obtain ⟨y, hy, hQy⟩ := key (M.num L B) (M.num_mem_om L B)
    ((M.mem_suc_num L).mpr ⟨B, le_refl B, rfl⟩)
  obtain ⟨i, -, e, rfl⟩ := (happ _ _).mp hy
  have ei := M.num_inj L e
  subst ei
  exact hQy

/-- **Recursion in the host agrees with recursion in the model.** -/
theorem rec_transfer (S : (M.host L).W → (M.host L).W → Prop) {g : M.Num → M.Num}
    (hg : M.NatFn g)
    (hS : ∀ (i : M.Num) (v : (M.host L).W), S (M.num L (g i)) v ↔ v = M.num L (g (i + 1)))
    (b : M.Num) (z : (M.host L).W) :
    (M.host L).RecG S (M.num L (g 0)) (M.num L b) z ↔ z = M.num L (g b) := by
  obtain ⟨f, hff, happ⟩ := M.inner_app L hg b
  have hcert : (M.host L).Cert S f (M.num L (g 0)) (M.num L b) := by
    refine ⟨⟨hff, fun a => ⟨fun ha => ?_, fun ⟨y, hy⟩ => ?_⟩⟩,
      (happ _ _).mpr ⟨0, M.nfacts.zero_le b, (M.num_zero L).symm, rfl⟩, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := (M.mem_suc_num L).mp ha
      exact ⟨_, (happ _ _).mpr ⟨i, hi, rfl, rfl⟩⟩
    · obtain ⟨i, hi, rfl, -⟩ := (happ _ _).mp hy
      exact (M.mem_suc_num L).mpr ⟨i, hi, rfl⟩
    · intro i u v hi hu hv
      obtain ⟨i', hi', rfl⟩ := (M.mem_num L).mp hi
      obtain ⟨i2, -, e2, rfl⟩ := (happ _ _).mp hu
      have ei2 := M.num_inj L e2
      subst ei2
      rw [← M.num_succ L] at hv
      obtain ⟨i3, -, e3, rfl⟩ := (happ _ _).mp hv
      rw [← M.num_inj L e3]
      exact (hS i' _).mpr rfl
  constructor
  · rintro ⟨f', hc', hz⟩
    have key := (M.host L).om_ind
      (fun x => x ∈ (M.host L).suc (M.num L b) → ∀ u, (M.host L).App f' x u →
        (M.host L).App f x u) (by hdef)
      (fun _ u hu => by
        rw [hc'.1.1.2 _ _ _ hu hc'.2.1]
        exact hcert.2.1)
      (fun x hx ih hsx u hu => by
        obtain ⟨i, rfl⟩ := (M.mem_om_iff L).mp hx
        have hsx' := hsx
        rw [← M.num_succ L i] at hsx'
        obtain ⟨i', hi', e⟩ := (M.mem_suc_num L).mp hsx'
        have ei := M.num_inj L e
        subst ei
        have hiB : i ≤ b := le_trans (M.nfacts.le_add i 1) hi'
        have hxs := (M.mem_suc_num L).mpr ⟨i, hiB, rfl⟩
        obtain ⟨u0, hu0⟩ := (hc'.1.2 _).mp hxs
        obtain ⟨i2, -, e2, rfl⟩ := (happ _ _).mp (ih hxs u0 hu0)
        have ei2 := M.num_inj L e2
        subst ei2
        have hSu := hc'.2.2 _ _ _ ((M.num_mem L).mpr hi') hu0 hu
        rw [(hS i u).mp hSu, ← M.num_succ L]
        exact (happ _ _).mpr ⟨i + 1, hi', rfl, rfl⟩)
    obtain ⟨i, -, e, rfl⟩ := (happ _ _).mp (key (M.num L b) (M.num_mem_om L b)
      ((M.mem_suc_num L).mpr ⟨b, le_refl b, rfl⟩) z hz)
    rw [← M.num_inj L e]
  · rintro rfl
    exact ⟨f, hcert, (happ _ _).mpr ⟨b, le_refl b, rfl, rfl⟩⟩

theorem add_transfer (a b : M.Num) (z : (M.host L).W) :
    (M.host L).RecG (fun u v => v = (M.host L).suc u) (M.num L a) (M.num L b) z ↔
      z = M.num L (a + b) := by
  have h := M.rec_transfer L (fun u v => v = (M.host L).suc u) (g := fun i => M.addN a i)
    (M.fnAdd (M.natFn_const a) M.natFn_id)
    (fun i v => by
      show v = (M.host L).suc (M.num L (a + i)) ↔ v = M.num L (a + (i + 1))
      rw [← M.num_succ L, add_assoc]) b z
  rw [show M.addN a 0 = a from add_zero a] at h
  exact h

theorem mul_transfer (a b : M.Num) (z : (M.host L).W) :
    (M.host L).RecG (fun u v => (M.host L).RecG (fun u v => v = (M.host L).suc u) u (M.num L a) v)
      (M.host L).emp (M.num L b) z ↔ z = M.num L (a * b) := by
  have h := M.rec_transfer L
    (fun u v => (M.host L).RecG (fun u v => v = (M.host L).suc u) u (M.num L a) v)
    (g := fun i => M.mulN a i) (M.fnMul (M.natFn_const a) M.natFn_id)
    (fun i v => by
      show (M.host L).RecG (fun u v => v = (M.host L).suc u) (M.num L (a * i)) (M.num L a) v ↔
        v = M.num L (a * (i + 1))
      rw [M.add_transfer L, mul_add, mul_one]) b z
  rw [show M.mulN a 0 = 0 from mul_zero a, M.num_zero L] at h
  exact h

theorem exp_transfer (b : M.Num) (z : (M.host L).W) :
    (M.host L).RecG (fun u v => (M.host L).RecG (fun u v => v = (M.host L).suc u) u u v)
      ((M.host L).suc (M.host L).emp) (M.num L b) z ↔ z = M.num L (M.expN b) := by
  have h := M.rec_transfer L
    (fun u v => (M.host L).RecG (fun u v => v = (M.host L).suc u) u u v)
    (g := M.expN) M.natFn_expN
    (fun i v => by
      rw [M.add_transfer L, M.expN_add_one]) b z
  rw [show M.expN 0 = 1 from M.expN_zero, show (1 : M.Num) = 0 + 1 from (zero_add 1).symm,
    M.num_succ L, M.num_zero L] at h
  exact h

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **The host of Lemma 3.2 has the arithmetic of the model.** -/
theorem arith : (M.host L).Arith M.expN (M.num L) where
  iso := M.numIso L
  nf := M.nfacts
  add := ⟨fun a b z => (M.host L).RecG (fun u v => v = (M.host L).suc u) a b z, by hdef,
    fun a b z => M.add_transfer L a b z⟩
  mul := ⟨fun a b z => (M.host L).RecG
      (fun u v => (M.host L).RecG (fun u v => v = (M.host L).suc u) u a v) (M.host L).emp b z,
    by hdef, fun a b z => M.mul_transfer L a b z⟩
  exp := ⟨fun b z => (M.host L).RecG
      (fun u v => (M.host L).RecG (fun u v => v = (M.host L).suc u) u u v)
      ((M.host L).suc (M.host L).emp) b z, by hdef, fun b z => M.exp_transfer L b z⟩

end tower

end Model

end NFUCut



/-!
# Phase 2, NFU side, part 2: the cut `𝖪ₜ` and the existence of truth assignments

`tw` iterates the step `rstep` of the Ramsey bound. `𝖪ₜ` is the cut obtained from
`{n : tw n ∈ 𝖲}` by shortening twice. For `q ∈ 𝖪ₜ` there is a set `τ` of numbers which, as a
truth assignment on the codes of atoms, satisfies every instance of the axioms N whose atoms
have codes below `q` (`sound`).
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

theorem natFn_rstep : M.NatFn (Host.rstep M.expN) := by
  have hs1 : M.NatFn (fun n => M.addN n 1) := M.fnAdd M.natFn_id (M.natFn_const 1)
  have hE1 := M.natFn_comp M.natFn_expN hs1
  have hmul := M.fnMul hE1 hs1
  have hEE := M.natFn_comp M.natFn_expN hmul
  exact M.fnAdd hEE hEE

theorem lt_rstep (x : M.Num) : x + 1 ≤ Host.rstep M.expN x := by
  have h1 : x + 1 ≤ M.expN (x + 1) * (x + 1) := by
    have h := M.nfacts.mul_le_mul_l (M.one_le_expN (x + 1)) (x + 1)
    rw [mul_one, mul_comm] at h
    exact h
  have h2 : M.expN (x + 1) * (x + 1) ≤ M.expN (M.expN (x + 1) * (x + 1)) := M.le_expN _
  exact le_trans h1 (le_trans h2 (M.nfacts.le_add _ _))

theorem inS_succ' {a : M.Num} (h : M.InS a.1) : M.InS (a + 1).1 := M.lemma_2_2.2.1 a h

theorem inS_rstep {a : M.Num} (h : M.InS a.1) : M.InS (Host.rstep M.expN a).1 := by
  have h1 := M.inS_succ' h
  have h2 := M.inS_expN (M.inS_mul (M.inS_expN h1) h1)
  exact M.inS_add h2 h2

theorem inS_cast (k : ℕ) : M.InS ((k : M.Num)).1 := by
  induction k with
  | zero =>
    rw [Nat.cast_zero]
    exact M.lemma_2_2.1
  | succ k ih =>
    rw [Nat.cast_succ]
    exact M.inS_succ' ih

theorem exists_tw : ∃ F : M.Num → M.Num → M.Num, M.NatOp F ∧ (∀ a, F a M.nzero = a) ∧
    ∀ a b, F a (M.nsucc b) = Host.rstep M.expN (F a b) :=
  M.exists_prec M.natFn_id (M.natOp_of_fn M.natFn_rstep)

/-- The iteration of the Ramsey step: `tw 0 = 0`, `tw (b + 1) = rstep (tw b)`. -/
noncomputable def tw (b : M.Num) : M.Num := Classical.choose M.exists_tw 0 b

theorem tw_zero : M.tw 0 = 0 := (Classical.choose_spec M.exists_tw).2.1 0

theorem tw_succ (b : M.Num) : M.tw (b + 1) = Host.rstep M.expN (M.tw b) := by
  rw [← M.nsucc_eq_add_one]
  exact (Classical.choose_spec M.exists_tw).2.2 0 b

theorem natFn_tw : M.NatFn M.tw :=
  M.natFn_op₂ (Classical.choose_spec M.exists_tw).1 (M.natFn_const 0) M.natFn_id

theorem le_tw (n : M.Num) : n ≤ M.tw n := by
  refine M.num_ind (P := fun n => n ≤ M.tw n) (M.isPred_le M.natFn_id M.natFn_tw) ?_ ?_ n
  · exact M.nfacts.zero_le _
  · intro k (ih : k ≤ M.tw k)
    show M.nsucc k ≤ M.tw (M.nsucc k)
    rw [M.nsucc_eq_add_one, M.tw_succ]
    exact le_trans (M.nfacts.add_le_add_r ih 1) (M.lt_rstep _)

theorem tw_le_add (a c : M.Num) : M.tw a ≤ M.tw (a + c) := by
  refine M.num_ind (P := fun c => M.tw a ≤ M.tw (a + c))
    (M.isPred_le (M.natFn_const (M.tw a))
      (M.natFn_comp M.natFn_tw (M.fnAdd (M.natFn_const a) M.natFn_id))) ?_ ?_ c
  · show M.tw a ≤ M.tw (a + 0)
    rw [add_zero]
  · intro k (ih : M.tw a ≤ M.tw (a + k))
    show M.tw a ≤ M.tw (a + M.nsucc k)
    rw [M.nsucc_eq_add_one, ← add_assoc, M.tw_succ]
    exact le_trans ih (le_trans (M.nfacts.le_add _ 1) (M.lt_rstep _))

theorem tw_mono {a b : M.Num} (h : a ≤ b) : M.tw a ≤ M.tw b := by
  obtain ⟨c, rfl⟩ := M.le_def.mp h
  exact M.tw_le_add a c

theorem tw_hyp : Shortening.Hyp (fun n : M.Num => M.InS n.1) M.tw (Host.rstep M.expN) where
  down := fun hab hb => M.inS_of_le hab hb
  mono := fun h => M.tw_mono h
  step := fun n => M.tw_succ n
  exp := fun h => M.inS_rstep h
  base := by
    show M.InS (M.tw 0).1
    rw [M.tw_zero]
    exact M.lemma_2_2.1

/-- `𝖪ₜ`: the cut obtained from `{n : tw n ∈ 𝖲}` by shortening twice. -/
def InKt (n : M.Num) : Prop := Shortening.K (fun n : M.Num => M.InS n.1) M.tw n

theorem kt_down {a b : M.Num} (hab : a ≤ b) (hb : M.InKt b) : M.InKt a :=
  Shortening.K_down M.tw_hyp hab hb

theorem kt_zero : M.InKt 0 := Shortening.K_zero

theorem kt_one : M.InKt 1 := Shortening.K_one

theorem kt_add {a b : M.Num} (ha : M.InKt a) (hb : M.InKt b) : M.InKt (a + b) :=
  Shortening.K_add ha hb

theorem kt_mul {a b : M.Num} (ha : M.InKt a) (hb : M.InKt b) : M.InKt (a * b) :=
  Shortening.K_mul ha hb

theorem kt_tw {a : M.Num} (ha : M.InKt a) : M.InS (M.tw a).1 := Shortening.K_sub M.tw_hyp ha

theorem kt_cast (k : ℕ) : M.InKt (k : M.Num) := by
  induction k with
  | zero =>
    rw [Nat.cast_zero]
    exact M.kt_zero
  | succ k ih =>
    rw [Nat.cast_succ]
    exact M.kt_add ih M.kt_one

section tower

variable {R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ : V} {n j m : M.Num}
variable (L : M.L32X R P th io Nt nle p F d tp qo Nu Pr κ ol Nm l Sg q1 W q0 Kn Lam σ' δ n j m)
include L

/-- The numbers of the model that correspond to the members of a set of the host form a set
of the model. -/
theorem isPred_mem (X : (M.host L).W) : M.IsPred (fun i : M.Num => M.num L i ∈ X) := by
  obtain ⟨a, ha, rfl⟩ := M.st_surj L X
  obtain ⟨s, -, hs⟩ := M.comp (σW [(6, 5), (20, 7), (22, 5), (24, 5), (27, 3), (460, 5)])
    (.and (.mem 400 27) (Fml.ex 473 (.and (fApp 460 400 473) (fEpsS 473 470)))) 400 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 F)
      20 P) 21 tp) 22 th) 24 io) 25 j.1) 27 M.nat) 460 Nm) 470 a)
  have hs' : ∀ v, M.mem v s ↔ M.mem v M.nat ∧ ∃ o, M.mem (M.op v o) Nm ∧
      M.EpsStarRaw P th io M.nat j.1 tp F o a := by
    intro v
    rw [hs v]
    simp [Sat, M.sat_ex, M.sat_fEpsS, M.sat_fApp', Function.update_apply]
  refine ⟨s, fun v => ?_⟩
  rw [hs']
  constructor
  · rintro ⟨hv, o, ho, he⟩
    refine ⟨⟨v, hv⟩, rfl, ?_⟩
    show M.num L ⟨v, hv⟩ ∈ M.st L a ha
    rw [M.num_eq L (i := ⟨v, hv⟩) ho]
    exact (M.mem_st L).mpr he
  · rintro ⟨i, rfl, h⟩
    obtain ⟨o, ho⟩ := L.nums.tot i
    have h' : M.num L i ∈ M.st L a ha := h
    rw [M.num_eq L ho] at h'
    exact ⟨i.2, o, ho, (M.mem_st L).mp h'⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The existence of a truth assignment, in the host of Lemma 3.2 with a tower of the height
`d₀ + 1`. -/
theorem sound_L {q : M.Num} (d0 : M.Num) (hm' : m = d0 + 1 + 1)
    (hd0 : M.tw (5 * q + 6 + 5 + (5 * q + 6) + 1 + (5 * q + 6 + (5 * q + 6) + 1) * q) ≤ d0 + 1) :
    ∃ τ : V, NSat (fun i : M.Num => M.mem i.1 τ) q := by
  obtain ⟨T, hT, -⟩ := M.exists_tower_of L d0 hm'
  have ar := M.arith L
  obtain ⟨e, he, hlv, hns⟩ := Host.sound_core ar T.flat T.flat_ax M.tw
    (fun n => le_of_eq (M.tw_succ n).symm) M.NatFn
    (fun Q hQ g hg h0 hs => M.mixed_ind L Q hQ g hg h0 hs)
    (fun a => M.natFn_comp M.natFn_tw (M.fnAdd (M.natFn_const a) M.natFn_id))
    (fun m r => M.natFn_comp M.natFn_tw
      (M.fnAdd (M.natFn_const m) (M.fnMul (M.natFn_const r) M.natFn_id)))
    (D := d0 + 1) (q := q) (R := 5 * q + 6) (m := 5 * q + 6 + 5 + (5 * q + 6) + 1) hT (le_refl _)
    hd0 (M.le_tw _)
  have hdt := T.flat.def_tr ar
  have hdi := (M.host L).def_incSeq
  have hdA := ar.def_Ad
  obtain ⟨X, hX⟩ := (M.host L).sep' (M.num L q)
    (fun x => T.flat.AllT ar e x (M.num L (5 * q + 6))) (by hdef)
  obtain ⟨τ, hτ⟩ := M.isPred_mem L X
  refine ⟨τ, NSat.congr (fun i hi => ?_) hns⟩
  rw [hτ]
  constructor
  · exact fun h => ⟨i, rfl, (hX _).mpr ⟨(M.num_mem L).mpr hi, h⟩⟩
  · rintro ⟨k, hk, hx⟩
    have e : k = i := Subtype.ext hk
    subst e
    exact ((hX _).mp hx).2

end tower

/-- **Existence of truth assignments.** For `q` in the cut `𝖪ₜ` there is a set of numbers
which, as a truth assignment on the codes of atoms, satisfies every instance of the axioms N
whose atoms have codes below `q`. -/
theorem sound {q : M.Num} (hq : M.InKt q) : ∃ τ : V, NSat (fun i : M.Num => M.mem i.1 τ) q := by
  have h5 : M.InKt (5 : M.Num) := by
    rw [show (5 : M.Num) = ((5 : ℕ) : M.Num) from by norm_num]
    exact M.kt_cast 5
  have h6 : M.InKt (6 : M.Num) := by
    rw [show (6 : M.Num) = ((6 : ℕ) : M.Num) from by norm_num]
    exact M.kt_cast 6
  have hR : M.InKt (5 * q + 6) := M.kt_add (M.kt_mul h5 hq) h6
  have hn0 : M.InKt (5 * q + 6 + 5 + (5 * q + 6) + 1 + (5 * q + 6 + (5 * q + 6) + 1) * q) :=
    M.kt_add (M.kt_add (M.kt_add (M.kt_add hR h5) hR) M.kt_one)
      (M.kt_mul (M.kt_add (M.kt_add hR hR) M.kt_one) hq)
  have hS := M.kt_tw hn0
  have h3 : M.InS ((3 : M.Num)).1 := by
    rw [show (3 : M.Num) = ((3 : ℕ) : M.Num) from by norm_num]
    exact M.inS_cast 3
  have hcalm : M.InS (3 * (M.tw (5 * q + 6 + 5 + (5 * q + 6) + 1 +
      (5 * q + 6 + (5 * q + 6) + 1) * q) + 1 + 1 + 1) + 1 + 1 : M.Num).1 :=
    M.inS_succ' (M.inS_succ' (M.inS_mul h3 (M.inS_succ' (M.inS_succ' (M.inS_succ' hS)))))
  obtain ⟨R, P, th, io, Nt, nle, p, F, d, tp, qo, Nu, Pr, κ, ol, Nm, l, Sg, q1, W, q0, Kn, Lam,
    σ', δ, L⟩ := M.l32x_calm (m := M.tw (5 * q + 6 + 5 + (5 * q + 6) + 1 +
      (5 * q + 6 + (5 * q + 6) + 1) * q) + 1 + 1) hcalm
  exact M.sound_L L _ rfl (M.nfacts.le_add _ 1)

end Model

end NFUCut



/-!
# Phase 2, NFU side, part 3: correct states and the cut of the terms

A state is a number `k` (its length) and a set `S` of numbers; only the members of `S` below
`k` matter. It is *good* if for every `q` in `𝖪ₜ` it extends to a truth assignment that
satisfies the axioms N below `q`. A state is *correct* if all its initial segments are good
and each of its values is `1` exactly when the extension by `1` is good.
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

/-- `S` and `S'` have the same members below `k`. -/
def Agree (k : M.Num) (S S' : V) : Prop := ∀ i : M.Num, i + 1 ≤ k → (M.mem i.1 S ↔ M.mem i.1 S')

theorem agree_refl (k : M.Num) (S : V) : M.Agree k S S := fun _ _ => Iff.rfl

theorem agree_symm {k : M.Num} {S S' : V} (h : M.Agree k S S') : M.Agree k S' S :=
  fun i hi => (h i hi).symm

theorem agree_trans {k : M.Num} {S S' S'' : V} (h : M.Agree k S S') (h' : M.Agree k S' S'') :
    M.Agree k S S'' := fun i hi => (h i hi).trans (h' i hi)

theorem agr_mono {i k : M.Num} {S S' : V} (hik : i ≤ k) (h : M.Agree k S S') : M.Agree i S S' :=
  fun x hx => h x (le_trans hx hik)

theorem le_succ_iff {i k : M.Num} : i ≤ k + 1 ↔ i ≤ k ∨ i = k + 1 := by
  constructor
  · intro h
    rcases M.eq_or_succ_le h with h1 | h1
    · exact Or.inr h1
    · exact Or.inl (M.nfacts.le_of_succ_le_succ h1)
  · rintro (h | h)
    · exact le_trans h (M.nfacts.le_add k 1)
    · rw [h]

theorem agree_succ {k : M.Num} {S S' : V} :
    M.Agree (k + 1) S S' ↔ M.Agree k S S' ∧ (M.mem k.1 S ↔ M.mem k.1 S') := by
  constructor
  · intro h
    exact ⟨M.agr_mono (M.nfacts.le_add k 1) h, h k (le_refl _)⟩
  · rintro ⟨h1, h2⟩ i hi
    have hik : i ≤ k := M.nfacts.le_of_succ_le_succ hi
    rcases M.eq_or_succ_le hik with h | h
    · rw [h]
      exact h2
    · exact h1 i h

/-- The state extends to a truth assignment that satisfies the axioms N below `q`. -/
def Sat1 (k : M.Num) (S : V) (q : M.Num) : Prop :=
  ∃ τ : V, M.Agree k τ S ∧ NSat (fun i : M.Num => M.mem i.1 τ) q

/-- The state is good. -/
def Good (k : M.Num) (S : V) : Prop := ∀ q, M.InKt q → M.Sat1 k S q

theorem good_congr {k : M.Num} {S S' : V} (h : M.Agree k S S') (hg : M.Good k S) : M.Good k S' :=
  fun q hq => by
    obtain ⟨τ, h1, h2⟩ := hg q hq
    exact ⟨τ, M.agree_trans h1 h, h2⟩

theorem good_mono {i k : M.Num} {S : V} (hik : i ≤ k) (hg : M.Good k S) : M.Good i S :=
  fun q hq => by
    obtain ⟨τ, h1, h2⟩ := hg q hq
    exact ⟨τ, M.agr_mono hik h1, h2⟩

/-- The extension of the state by the value `1` is good. -/
def T1 (k : M.Num) (S : V) : Prop :=
  ∃ S', M.Agree k S' S ∧ M.mem k.1 S' ∧ M.Good (k + 1) S'

theorem t1_congr {k : M.Num} {S S' : V} (h : M.Agree k S S') : M.T1 k S ↔ M.T1 k S' :=
  ⟨fun ⟨S1, h1, h2, h3⟩ => ⟨S1, M.agree_trans h1 h, h2, h3⟩,
    fun ⟨S1, h1, h2, h3⟩ => ⟨S1, M.agree_trans h1 (M.agree_symm h), h2, h3⟩⟩

/-- **The dichotomy.** A good state has a good extension by `1` or a good extension by `0`. -/
theorem dichotomy {k : M.Num} {S : V} (h : M.Good k S) :
    M.T1 k S ∨ ∃ S', M.Agree k S' S ∧ ¬ M.mem k.1 S' ∧ M.Good (k + 1) S' := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hn1, hn0⟩ := hne
  have hk : ∀ i : M.Num, i + 1 ≤ k → i.1 ≠ k.1 := fun i hi e => by
    have e' : i = k := Subtype.ext e
    rw [e'] at hi
    exact M.not_succ_le k hi
  have ag1 : M.Agree k (M.adj S k.1) S := fun i hi => by
    rw [M.mem_adj]
    exact ⟨fun h' => h'.elim id (fun e => absurd e (hk i hi)), Or.inl⟩
  have ag0 : M.Agree k (M.rem S k.1) S := fun i hi => by
    rw [M.mem_rem]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', hk i hi⟩⟩
  have m1 : M.mem k.1 (M.adj S k.1) := M.mem_adj.mpr (Or.inr rfl)
  have m0 : ¬ M.mem k.1 (M.rem S k.1) := fun h' => (M.mem_rem.mp h').2 rfl
  have b1 : ¬ M.Good (k + 1) (M.adj S k.1) := fun hg => hn1 ⟨_, ag1, m1, hg⟩
  have b0 : ¬ M.Good (k + 1) (M.rem S k.1) := fun hg => hn0 ⟨_, ag0, m0, hg⟩
  unfold Good at b1 b0
  push_neg at b1 b0
  obtain ⟨q1, hq1, hs1⟩ := b1
  obtain ⟨q0, hq0, hs0⟩ := b0
  obtain ⟨τ, hτ, hns⟩ := h (q0 + q1) (M.kt_add hq0 hq1)
  by_cases hkτ : M.mem k.1 τ
  · exact hs1 ⟨τ, M.agree_succ.mpr ⟨M.agree_trans hτ (M.agree_symm ag1), ⟨fun _ => m1, fun _ => hkτ⟩⟩,
      hns.mono (by rw [add_comm]; exact M.nfacts.le_add q1 q0)⟩
  · exact hs0 ⟨τ, M.agree_succ.mpr ⟨M.agree_trans hτ (M.agree_symm ag0),
      ⟨fun h' => absurd h' hkτ, fun h' => absurd h' m0⟩⟩, hns.mono (M.nfacts.le_add q0 q1)⟩

/-- The state is correct. -/
def Correct (k : M.Num) (S : V) : Prop :=
  (∀ i, i ≤ k → M.Good i S) ∧ ∀ i : M.Num, i + 1 ≤ k → (M.mem i.1 S ↔ M.T1 i S)

theorem correct_down {i k : M.Num} {S : V} (h : M.Correct k S) (hik : i ≤ k) : M.Correct i S :=
  ⟨fun x hx => h.1 x (le_trans hx hik), fun x hx => h.2 x (le_trans hx hik)⟩

theorem correct_congr {k : M.Num} {S S' : V} (hag : M.Agree k S S') (h : M.Correct k S) :
    M.Correct k S' :=
  ⟨fun i hi => M.good_congr (M.agr_mono hi hag) (h.1 i hi),
    fun i hi => ((hag i hi).symm.trans (h.2 i hi)).trans
      (M.t1_congr (M.agr_mono (le_trans (M.nfacts.le_add i 1) hi) hag))⟩

theorem correct_zero : M.Correct 0 M.emp := by
  have hno : ∀ i : M.Num, ¬ i + 1 ≤ 0 := fun i hi =>
    M.not_succ_le i (le_trans hi (M.nfacts.zero_le i))
  refine ⟨fun i hi q hq => ?_, fun i hi => absurd hi (hno i)⟩
  obtain ⟨τ, hτ⟩ := M.sound hq
  have e : i = 0 := le_antisymm hi (M.nfacts.zero_le i)
  rw [e]
  exact ⟨τ, fun x hx => absurd hx (hno x), hτ⟩

/-- A correct state has a correct extension by one more value. -/
theorem correct_succ {k : M.Num} {S : V} (h : M.Correct k S) :
    ∃ S', M.Correct (k + 1) S' := by
  have key : ∀ S', M.Agree k S' S → M.Good (k + 1) S' → (M.mem k.1 S' ↔ M.T1 k S) →
      M.Correct (k + 1) S' := by
    intro S' hag hgood hval
    have hc := M.correct_congr (M.agree_symm hag) h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases M.le_succ_iff.mp hi with h1 | h1
      · exact hc.1 i h1
      · rw [h1]
        exact hgood
    · have hik : i ≤ k := M.nfacts.le_of_succ_le_succ hi
      rcases M.eq_or_succ_le hik with h1 | h1
      · rw [h1]
        exact hval.trans (M.t1_congr (M.agree_symm hag))
      · exact hc.2 i h1
  by_cases hT : M.T1 k S
  · obtain ⟨S1, hag, hk1, hgood⟩ := hT
    exact ⟨S1, key S1 hag hgood ⟨fun _ => ⟨S1, hag, hk1, hgood⟩, fun _ => hk1⟩⟩
  · rcases M.dichotomy (h.1 k (le_refl k)) with h1 | ⟨S0, hag, hk0, hgood⟩
    · exact absurd h1 hT
    · exact ⟨S0, key S0 hag hgood ⟨fun h' => absurd h' hk0, fun h' => absurd h' hT⟩⟩

/-- Agreement below a number is a set condition on the number. -/
theorem isPred_agree (S S' : V) : M.IsPred (fun i : M.Num => M.Agree i S S') := by
  obtain ⟨s, -, hs⟩ := M.comp (σW [(27, 3), (28, 7), (460, 3), (461, 3)])
    (.and (.mem 400 27) (.all 401 (Fml.imp (.and (.mem 401 27) (fLtN 401 400))
      (Fml.iff (.mem 401 460) (.mem 401 461))))) 400 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (fun _ => dflt) 10 (0 : M.Num).1) 27 M.nat) 28 M.adG) 460 S) 461 S')
  have hs' : ∀ v, M.mem v s ↔ M.mem v M.nat ∧ ∀ x, M.mem x M.nat →
      (∃ y, M.mem y M.nat ∧ ¬ y = (0 : M.Num).1 ∧ M.mem (M.trip x y v) M.adG) →
      (M.mem x S ↔ M.mem x S') := by
    intro v
    rw [hs v]
    simp [Sat, M.sat_imp, M.sat_iff, M.sat_fLtN, Function.update_apply]
  refine ⟨s, fun v => ?_⟩
  rw [hs']
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, rfl, fun i hi => h i.1 i.2 ((M.ltRaw_num i ⟨v, hv⟩).mpr hi)⟩
  · rintro ⟨n, rfl, h⟩
    exact ⟨n.2, fun x hx hlt => h ⟨x, hx⟩ ((M.ltRaw_num ⟨x, hx⟩ n).mp hlt)⟩

/-- Correct states agree. -/
theorem correct_unique {k k' : M.Num} {S S' : V} (h : M.Correct k S) (h' : M.Correct k' S')
    (hkk : k ≤ k') : M.Agree k S S' := by
  have key : ∀ i : M.Num, i ≤ k → M.Agree i S S' := by
    intro i
    refine M.num_ind (P := fun i => i ≤ k → M.Agree i S S')
      (M.isPred_imp (M.isPred_le M.natFn_id (M.natFn_const k)) (M.isPred_agree S S')) ?_ ?_ i
    · intro _ x hx
      exact absurd (le_trans hx (M.nfacts.zero_le x)) (M.not_succ_le x)
    · intro x ih hx
      rw [M.nsucc_eq_add_one] at hx ⊢
      have hag := ih (le_trans (M.nfacts.le_add x 1) hx)
      exact M.agree_succ.mpr ⟨hag,
        ((h.2 x hx).trans (M.t1_congr hag)).trans (h'.2 x (le_trans hx hkk)).symm⟩
  exact key k (le_refl k)

/-- The numbers of `𝖪ₜ` that are the length of a correct state. -/
def InJ (k : M.Num) : Prop := M.InKt k ∧ ∃ S, M.Correct k S

theorem inJ_hyp : Shortening.Hyp M.InJ (fun n : M.Num => n) (fun n : M.Num => n + 1) where
  down := fun hab ⟨h1, S, h2⟩ => ⟨M.kt_down hab h1, S, M.correct_down h2 hab⟩
  mono := fun h => h
  step := fun _ => rfl
  exp := fun ⟨h1, S, h2⟩ => ⟨M.kt_add h1 M.kt_one, M.correct_succ h2⟩
  base := ⟨M.kt_zero, M.emp, M.correct_zero⟩

/-- **The cut of the terms**: obtained from `InJ` by shortening twice, so that it is closed
under addition and multiplication. -/
def InI (n : M.Num) : Prop := Shortening.K M.InJ (fun n : M.Num => n) n

theorem i_down {a b : M.Num} (hab : a ≤ b) (hb : M.InI b) : M.InI a :=
  Shortening.K_down M.inJ_hyp hab hb

theorem i_zero : M.InI 0 := Shortening.K_zero

theorem i_one : M.InI 1 := Shortening.K_one

theorem i_add {a b : M.Num} (ha : M.InI a) (hb : M.InI b) : M.InI (a + b) :=
  Shortening.K_add ha hb

theorem i_mul {a b : M.Num} (ha : M.InI a) (hb : M.InI b) : M.InI (a * b) :=
  Shortening.K_mul ha hb

theorem i_sub {a : M.Num} (ha : M.InI a) : M.InJ a := Shortening.K_sub M.inJ_hyp ha

theorem i_cast (k : ℕ) : M.InI (k : M.Num) := by
  induction k with
  | zero =>
    rw [Nat.cast_zero]
    exact M.i_zero
  | succ k ih =>
    rw [Nat.cast_succ]
    exact M.i_add ih M.i_one

theorem i_npair {x y : M.Num} (hx : M.InI x) (hy : M.InI y) : M.InI (npair x y) :=
  M.i_add (M.i_mul (M.i_add hx hy) (M.i_add hx hy)) hx

theorem i_tm (f : ℕ) {x y : M.Num} (hx : M.InI x) (hy : M.InI y) : M.InI (tm f x y) :=
  M.i_add (M.i_npair (M.i_cast f) (M.i_npair hx hy)) M.i_one

theorem i_aIn {x y : M.Num} (hx : M.InI x) (hy : M.InI y) : M.InI (aIn x y) :=
  M.i_add (M.i_npair hx hy) (M.i_npair hx hy)

theorem i_aEq {x y : M.Num} (hx : M.InI x) (hy : M.InI y) : M.InI (aEq x y) :=
  M.i_add (M.i_aIn hx hy) M.i_one

/-- The interpretation of membership: the correct states give the atom `t ∈ t'` the value 1. -/
def Eps (t t' : M.Num) : Prop :=
  ∃ S, M.Correct (aIn t t' + 1) S ∧ M.mem (aIn t t').1 S

/-- The interpretation of equality: the correct states give the atom `t = t'` the value 1. -/
def Eta (t t' : M.Num) : Prop :=
  ∃ S, M.Correct (aEq t t' + 1) S ∧ M.mem (aEq t t').1 S

theorem val_iff {k : M.Num} {S : V} (h : M.Correct k S) {i : M.Num} (hi : i + 1 ≤ k) :
    (∃ S', M.Correct (i + 1) S' ∧ M.mem i.1 S') ↔ M.mem i.1 S := by
  constructor
  · rintro ⟨S', hc, hm⟩
    exact (M.correct_unique hc h hi i (le_refl _)).mp hm
  · exact fun hm => ⟨S, M.correct_down h hi, hm⟩

theorem exists_ibound (l : List M.Num) (hl : ∀ a ∈ l, M.InI a) :
    ∃ k, M.InI k ∧ ∀ a ∈ l, a + 1 ≤ k := by
  induction l with
  | nil => exact ⟨0, M.i_zero, fun a ha => absurd ha (List.not_mem_nil)⟩
  | cons b l ih =>
    obtain ⟨k, hk, hb⟩ := ih (fun a ha => hl a (List.mem_cons_of_mem b ha))
    refine ⟨k + (b + 1), M.i_add hk (M.i_add (hl b List.mem_cons_self) M.i_one), fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with h | h
    · rw [h]
      exact (M.nfacts.le_iff _ _).mpr ⟨k, add_comm _ _⟩
    · exact le_trans (hb a h) (M.nfacts.le_add k (b + 1))

/-- **A correct state long enough for a list of atoms in the cut**: it satisfies the axioms N
below its length, and its values at the atoms of the list are the values of `Eps` and `Eta`. -/
theorem exists_model_state (l : List M.Num) (hl : ∀ a ∈ l, M.InI a) :
    ∃ (S : V) (k : M.Num), NSat (fun i : M.Num => M.mem i.1 S) k ∧ (∀ a ∈ l, a + 1 ≤ k) ∧
      (∀ t t' : M.Num, aIn t t' ∈ l → (M.mem (aIn t t').1 S ↔ M.Eps t t')) ∧
      (∀ t t' : M.Num, aEq t t' ∈ l → (M.mem (aEq t t').1 S ↔ M.Eta t t')) := by
  obtain ⟨k, hk, hb⟩ := M.exists_ibound l hl
  obtain ⟨hkt, S, hS⟩ := M.i_sub hk
  obtain ⟨τ, hτ, hns⟩ := hS.1 k (le_refl k) k hkt
  exact ⟨S, k, hns.congr hτ, hb, fun t t' h => (M.val_iff hS (hb _ h)).symm,
    fun t t' h => (M.val_iff hS (hb _ h)).symm⟩

end Model

end NFUCut



/-!
# Phase 2, NFU side, part 4: the axioms N hold for `Eps` and `Eta` on the cut of the terms

Generated by `gen/genS4.py` from the list of the axioms in `gen/gen53.py`.
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

theorem i_sgT {x : M.Num} (hx : M.InI x) : M.InI (sgT x) := M.i_tm 0 hx M.i_zero
theorem i_upT {x y : M.Num} (hx : M.InI x) (hy : M.InI y) : M.InI (upT x y) := M.i_tm 1 hx hy
theorem i_opT {x y : M.Num} (hx : M.InI x) (hy : M.InI y) : M.InI (opT x y) :=
  M.i_upT (M.i_sgT hx) (M.i_upT hx hy)
theorem i_inT {x y : M.Num} (hx : M.InI x) (hy : M.InI y) : M.InI (inT x y) := M.i_tm 2 hx hy
theorem i_coT {x : M.Num} (hx : M.InI x) : M.InI (coT x) := M.i_tm 3 hx M.i_zero
theorem i_siT {x : M.Num} (hx : M.InI x) : M.InI (siT x) := M.i_tm 4 hx M.i_zero
theorem i_i2T {x : M.Num} (hx : M.InI x) : M.InI (i2T x) := M.i_tm 5 hx M.i_zero
theorem i_i3T {x : M.Num} (hx : M.InI x) : M.InI (i3T x) := M.i_tm 6 hx M.i_zero
theorem i_vcT {x : M.Num} (hx : M.InI x) : M.InI (vcT x) := M.i_tm 7 hx M.i_zero
theorem i_tlT {x : M.Num} (hx : M.InI x) : M.InI (tlT x) := M.i_tm 8 hx M.i_zero
theorem i_cvT {x : M.Num} (hx : M.InI x) : M.InI (cvT x) := M.i_tm 9 hx M.i_zero
theorem i_c1T : M.InI (c1T : M.Num) := M.i_tm 10 M.i_zero M.i_zero
theorem i_sbT : M.InI (sbT : M.Num) := M.i_tm 11 M.i_zero M.i_zero
theorem i_dT {x y : M.Num} (hx : M.InI x) (hy : M.InI y) : M.InI (dT x y) := M.i_tm 12 hx hy
theorem i_p1T {x : M.Num} (hx : M.InI x) : M.InI (p1T x) := M.i_tm 13 hx M.i_zero
theorem i_p2T {x : M.Num} (hx : M.InI x) : M.InI (p2T x) := M.i_tm 14 hx M.i_zero
theorem i_elT {x : M.Num} (hx : M.InI x) : M.InI (elT x) := M.i_tm 15 hx M.i_zero
theorem i_wtT {x y : M.Num} (hx : M.InI x) (hy : M.InI y) : M.InI (wtT x y) := M.i_tm 16 hx hy
theorem i_wsT {x y : M.Num} (hx : M.InI x) (hy : M.InI y) : M.InI (wsT x y) := M.i_tm 17 hx hy

theorem ax_e1 {x : M.Num} (hx : M.InI x) :
    M.Eta (x) (x) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aEq (x) (x)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact M.i_aEq hx hx)
  have h := hns.e1 x (hb (aEq (x) (x)) (by simp))
  beta_reduce at h
  rw [heq x x (by simp)] at h
  exact h

theorem ax_e2 {x y z : M.Num} (hx : M.InI x) (hy : M.InI y) (hz : M.InI z) :
    M.Eta (x) (y) → M.Eta (x) (z) → M.Eta (y) (z) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aEq (x) (y), aEq (x) (z), aEq (y) (z)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact M.i_aEq hx hy
    · exact M.i_aEq hx hz
    · exact M.i_aEq hy hz)
  have h := hns.e2 x y z (hb (aEq (x) (y)) (by simp)) (hb (aEq (x) (z)) (by simp)) (hb (aEq (y) (z)) (by simp))
  beta_reduce at h
  rw [heq x y (by simp), heq x z (by simp), heq y z (by simp)] at h
  exact h

theorem ax_e3 {x x' y y' : M.Num} (hx : M.InI x) (hx' : M.InI x') (hy : M.InI y) (hy' : M.InI y') :
    M.Eta (x) (x') → M.Eta (y) (y') → M.Eps (x) (y) → M.Eps (x') (y') := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aEq (x) (x'), aEq (y) (y'), aIn (x) (y), aIn (x') (y')] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact M.i_aEq hx hx'
    · exact M.i_aEq hy hy'
    · exact M.i_aIn hx hy
    · exact M.i_aIn hx' hy')
  have h := hns.e3 x x' y y' (hb (aEq (x) (x')) (by simp)) (hb (aEq (y) (y')) (by simp)) (hb (aIn (x) (y)) (by simp)) (hb (aIn (x') (y')) (by simp))
  beta_reduce at h
  rw [heq x x' (by simp), heq y y' (by simp), hin x y (by simp), hin x' y' (by simp)] at h
  exact h

theorem ax_e4a {x x' : M.Num} (hx : M.InI x) (hx' : M.InI x') :
    M.Eta (x) (x') → M.Eta (sgT x) (sgT x') := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aEq (x) (x'), aEq (sgT x) (sgT x')] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact M.i_aEq hx hx'
    · exact M.i_aEq (M.i_sgT hx) (M.i_sgT hx'))
  have h := hns.e4a x x' (hb (aEq (x) (x')) (by simp)) (hb (aEq (sgT x) (sgT x')) (by simp))
  beta_reduce at h
  rw [heq x x' (by simp), heq (sgT x) (sgT x') (by simp)] at h
  exact h

theorem ax_e4b {x x' y y' : M.Num} (hx : M.InI x) (hx' : M.InI x') (hy : M.InI y) (hy' : M.InI y') :
    M.Eta (x) (x') → M.Eta (y) (y') → M.Eta (upT x y) (upT x' y') := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aEq (x) (x'), aEq (y) (y'), aEq (upT x y) (upT x' y')] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact M.i_aEq hx hx'
    · exact M.i_aEq hy hy'
    · exact M.i_aEq (M.i_upT hx hy) (M.i_upT hx' hy'))
  have h := hns.e4b x x' y y' (hb (aEq (x) (x')) (by simp)) (hb (aEq (y) (y')) (by simp)) (hb (aEq (upT x y) (upT x' y')) (by simp))
  beta_reduce at h
  rw [heq x x' (by simp), heq y y' (by simp), heq (upT x y) (upT x' y') (by simp)] at h
  exact h

theorem ax_m1 {x y : M.Num} (hx : M.InI x) (hy : M.InI y) :
    (M.Eps (dT x y) (x) ↔ M.Eps (dT x y) (y)) → M.Eta (x) (y) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (dT x y) (x), aIn (dT x y) (y), aEq (x) (y)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact M.i_aIn (M.i_dT hx hy) hx
    · exact M.i_aIn (M.i_dT hx hy) hy
    · exact M.i_aEq hx hy)
  have h := hns.m1 x y (hb (aIn (dT x y) (x)) (by simp)) (hb (aIn (dT x y) (y)) (by simp)) (hb (aEq (x) (y)) (by simp))
  beta_reduce at h
  rw [hin (dT x y) x (by simp), hin (dT x y) y (by simp), heq x y (by simp)] at h
  exact h

theorem ax_m2 {x y : M.Num} (hx : M.InI x) (hy : M.InI y) :
    (M.Eps (y) (sgT x) ↔ M.Eta (y) (x)) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (y) (sgT x), aEq (y) (x)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact M.i_aIn hy (M.i_sgT hx)
    · exact M.i_aEq hy hx)
  have h := hns.m2 x y (hb (aIn (y) (sgT x)) (by simp)) (hb (aEq (y) (x)) (by simp))
  beta_reduce at h
  rw [hin y (sgT x) (by simp), heq y x (by simp)] at h
  exact h

theorem ax_m3 {x y z : M.Num} (hx : M.InI x) (hy : M.InI y) (hz : M.InI z) :
    (M.Eps (z) (upT x y) ↔ M.Eta (z) (x) ∨ M.Eta (z) (y)) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (z) (upT x y), aEq (z) (x), aEq (z) (y)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact M.i_aIn hz (M.i_upT hx hy)
    · exact M.i_aEq hz hx
    · exact M.i_aEq hz hy)
  have h := hns.m3 x y z (hb (aIn (z) (upT x y)) (by simp)) (hb (aEq (z) (x)) (by simp)) (hb (aEq (z) (y)) (by simp))
  beta_reduce at h
  rw [hin z (upT x y) (by simp), heq z x (by simp), heq z y (by simp)] at h
  exact h

theorem ax_m4 {x y z : M.Num} (hx : M.InI x) (hy : M.InI y) (hz : M.InI z) :
    (M.Eps (z) (inT x y) ↔ M.Eps (z) (x) ∧ M.Eps (z) (y)) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (z) (inT x y), aIn (z) (x), aIn (z) (y)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact M.i_aIn hz (M.i_inT hx hy)
    · exact M.i_aIn hz hx
    · exact M.i_aIn hz hy)
  have h := hns.m4 x y z (hb (aIn (z) (inT x y)) (by simp)) (hb (aIn (z) (x)) (by simp)) (hb (aIn (z) (y)) (by simp))
  beta_reduce at h
  rw [hin z (inT x y) (by simp), hin z x (by simp), hin z y (by simp)] at h
  exact h

theorem ax_m5 {x z : M.Num} (hx : M.InI x) (hz : M.InI z) :
    (M.Eps (z) (coT x) ↔ ¬ M.Eps (z) (x)) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (z) (coT x), aIn (z) (x)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact M.i_aIn hz (M.i_coT hx)
    · exact M.i_aIn hz hx)
  have h := hns.m5 x z (hb (aIn (z) (coT x)) (by simp)) (hb (aIn (z) (x)) (by simp))
  beta_reduce at h
  rw [hin z (coT x) (by simp), hin z x (by simp)] at h
  exact h

theorem ax_m6 {x z w : M.Num} (hx : M.InI x) (hz : M.InI z) (hw : M.InI w) :
    (M.Eps (opT (sgT z) (sgT w)) (siT x) ↔ M.Eps (opT z w) (x)) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (opT (sgT z) (sgT w)) (siT x), aIn (opT z w) (x)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact M.i_aIn (M.i_opT (M.i_sgT hz) (M.i_sgT hw)) (M.i_siT hx)
    · exact M.i_aIn (M.i_opT hz hw) hx)
  have h := hns.m6 x z w (hb (aIn (opT (sgT z) (sgT w)) (siT x)) (by simp)) (hb (aIn (opT z w) (x)) (by simp))
  beta_reduce at h
  rw [hin (opT (sgT z) (sgT w)) (siT x) (by simp), hin (opT z w) x (by simp)] at h
  exact h

theorem ax_m7 {x p s r : M.Num} (hx : M.InI x) (hp : M.InI p) (hs : M.InI s) (hr : M.InI r) :
    (M.Eps (opT (sgT (sgT p)) (opT s r)) (i2T x) ↔ M.Eps (opT p r) (x)) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (opT (sgT (sgT p)) (opT s r)) (i2T x), aIn (opT p r) (x)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact M.i_aIn (M.i_opT (M.i_sgT (M.i_sgT hp)) (M.i_opT hs hr)) (M.i_i2T hx)
    · exact M.i_aIn (M.i_opT hp hr) hx)
  have h := hns.m7 x p s r (hb (aIn (opT (sgT (sgT p)) (opT s r)) (i2T x)) (by simp)) (hb (aIn (opT p r) (x)) (by simp))
  beta_reduce at h
  rw [hin (opT (sgT (sgT p)) (opT s r)) (i2T x) (by simp), hin (opT p r) x (by simp)] at h
  exact h

theorem ax_m8 {x p s r : M.Num} (hx : M.InI x) (hp : M.InI p) (hs : M.InI s) (hr : M.InI r) :
    (M.Eps (opT (sgT (sgT p)) (opT s r)) (i3T x) ↔ M.Eps (opT p s) (x)) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (opT (sgT (sgT p)) (opT s r)) (i3T x), aIn (opT p s) (x)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact M.i_aIn (M.i_opT (M.i_sgT (M.i_sgT hp)) (M.i_opT hs hr)) (M.i_i3T hx)
    · exact M.i_aIn (M.i_opT hp hs) hx)
  have h := hns.m8 x p s r (hb (aIn (opT (sgT (sgT p)) (opT s r)) (i3T x)) (by simp)) (hb (aIn (opT p s) (x)) (by simp))
  beta_reduce at h
  rw [hin (opT (sgT (sgT p)) (opT s r)) (i3T x) (by simp), hin (opT p s) x (by simp)] at h
  exact h

theorem ax_m9a {x p : M.Num} (hx : M.InI x) (hp : M.InI p) :
    M.Eps (p) (vcT x) → M.Eta (p) (opT (p1T p) (p2T p)) ∧ M.Eps (p2T p) (x) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (p) (vcT x), aEq (p) (opT (p1T p) (p2T p)), aIn (p2T p) (x)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact M.i_aIn hp (M.i_vcT hx)
    · exact M.i_aEq hp (M.i_opT (M.i_p1T hp) (M.i_p2T hp))
    · exact M.i_aIn (M.i_p2T hp) hx)
  have h := hns.m9a x p (hb (aIn (p) (vcT x)) (by simp)) (hb (aEq (p) (opT (p1T p) (p2T p))) (by simp)) (hb (aIn (p2T p) (x)) (by simp))
  beta_reduce at h
  rw [hin p (vcT x) (by simp), heq p (opT (p1T p) (p2T p)) (by simp), hin (p2T p) x (by simp)] at h
  exact h

theorem ax_m9b {x p s r : M.Num} (hx : M.InI x) (hp : M.InI p) (hs : M.InI s) (hr : M.InI r) :
    M.Eta (p) (opT s r) → M.Eps (r) (x) → M.Eps (p) (vcT x) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aEq (p) (opT s r), aIn (r) (x), aIn (p) (vcT x)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact M.i_aEq hp (M.i_opT hs hr)
    · exact M.i_aIn hr hx
    · exact M.i_aIn hp (M.i_vcT hx))
  have h := hns.m9b x p s r (hb (aEq (p) (opT s r)) (by simp)) (hb (aIn (r) (x)) (by simp)) (hb (aIn (p) (vcT x)) (by simp))
  beta_reduce at h
  rw [heq p (opT s r) (by simp), hin r x (by simp), hin p (vcT x) (by simp)] at h
  exact h

theorem ax_m10a {x p s : M.Num} (hx : M.InI x) (hp : M.InI p) (hs : M.InI s) :
    M.Eps (p) (tlT x) → M.Eps (opT s (sgT p)) (x) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (p) (tlT x), aIn (opT s (sgT p)) (x)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact M.i_aIn hp (M.i_tlT hx)
    · exact M.i_aIn (M.i_opT hs (M.i_sgT hp)) hx)
  have h := hns.m10a x p s (hb (aIn (p) (tlT x)) (by simp)) (hb (aIn (opT s (sgT p)) (x)) (by simp))
  beta_reduce at h
  rw [hin p (tlT x) (by simp), hin (opT s (sgT p)) x (by simp)] at h
  exact h

theorem ax_m10b {x p : M.Num} (hx : M.InI x) (hp : M.InI p) :
    M.Eps (opT (wtT p x) (sgT p)) (x) → M.Eps (p) (tlT x) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (opT (wtT p x) (sgT p)) (x), aIn (p) (tlT x)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact M.i_aIn (M.i_opT (M.i_wtT hp hx) (M.i_sgT hp)) hx
    · exact M.i_aIn hp (M.i_tlT hx))
  have h := hns.m10b x p (hb (aIn (opT (wtT p x) (sgT p)) (x)) (by simp)) (hb (aIn (p) (tlT x)) (by simp))
  beta_reduce at h
  rw [hin (opT (wtT p x) (sgT p)) x (by simp), hin p (tlT x) (by simp)] at h
  exact h

theorem ax_m11 {x p s : M.Num} (hx : M.InI x) (hp : M.InI p) (hs : M.InI s) :
    (M.Eps (opT p s) (cvT x) ↔ M.Eps (opT s p) (x)) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (opT p s) (cvT x), aIn (opT s p) (x)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact M.i_aIn (M.i_opT hp hs) (M.i_cvT hx)
    · exact M.i_aIn (M.i_opT hs hp) hx)
  have h := hns.m11 x p s (hb (aIn (opT p s) (cvT x)) (by simp)) (hb (aIn (opT s p) (x)) (by simp))
  beta_reduce at h
  rw [hin (opT p s) (cvT x) (by simp), hin (opT s p) x (by simp)] at h
  exact h

theorem ax_m12a {p : M.Num} (hp : M.InI p) :
    M.Eps (p) (c1T) → M.Eta (p) (sgT (elT p)) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (p) (c1T), aEq (p) (sgT (elT p))] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact M.i_aIn hp M.i_c1T
    · exact M.i_aEq hp (M.i_sgT (M.i_elT hp)))
  have h := hns.m12a p (hb (aIn (p) (c1T)) (by simp)) (hb (aEq (p) (sgT (elT p))) (by simp))
  beta_reduce at h
  rw [hin p c1T (by simp), heq p (sgT (elT p)) (by simp)] at h
  exact h

theorem ax_m12b {p s : M.Num} (hp : M.InI p) (hs : M.InI s) :
    M.Eta (p) (sgT s) → M.Eps (p) (c1T) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aEq (p) (sgT s), aIn (p) (c1T)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact M.i_aEq hp (M.i_sgT hs)
    · exact M.i_aIn hp M.i_c1T)
  have h := hns.m12b p s (hb (aEq (p) (sgT s)) (by simp)) (hb (aIn (p) (c1T)) (by simp))
  beta_reduce at h
  rw [heq p (sgT s) (by simp), hin p c1T (by simp)] at h
  exact h

theorem ax_m13a {p s r : M.Num} (hp : M.InI p) (hs : M.InI s) (hr : M.InI r) :
    M.Eps (opT p s) (sbT) → M.Eps (r) (p) → M.Eps (r) (s) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (opT p s) (sbT), aIn (r) (p), aIn (r) (s)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact M.i_aIn (M.i_opT hp hs) M.i_sbT
    · exact M.i_aIn hr hp
    · exact M.i_aIn hr hs)
  have h := hns.m13a p s r (hb (aIn (opT p s) (sbT)) (by simp)) (hb (aIn (r) (p)) (by simp)) (hb (aIn (r) (s)) (by simp))
  beta_reduce at h
  rw [hin (opT p s) sbT (by simp), hin r p (by simp), hin r s (by simp)] at h
  exact h

theorem ax_m13b {p s : M.Num} (hp : M.InI p) (hs : M.InI s) :
    (M.Eps (wsT p s) (p) → M.Eps (wsT p s) (s)) → M.Eps (opT p s) (sbT) := by
  obtain ⟨S, k, hns, hb, hin, heq⟩ := M.exists_model_state [aIn (wsT p s) (p), aIn (wsT p s) (s), aIn (opT p s) (sbT)] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact M.i_aIn (M.i_wsT hp hs) hp
    · exact M.i_aIn (M.i_wsT hp hs) hs
    · exact M.i_aIn (M.i_opT hp hs) M.i_sbT)
  have h := hns.m13b p s (hb (aIn (wsT p s) (p)) (by simp)) (hb (aIn (wsT p s) (s)) (by simp)) (hb (aIn (opT p s) (sbT)) (by simp))
  beta_reduce at h
  rw [hin (wsT p s) p (by simp), hin (wsT p s) s (by simp), hin (opT p s) sbT (by simp)] at h
  exact h

end Model

end NFUCut



/-!
# Phase 2, NFU side, part 5: the term model is a model of NF

In a model of NFU + Infinity, the numbers of the cut `InI` (codes of closed terms), with
`Eps` as membership and modulo `Eta`, form an `NFModel`, hence a model of NF.
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

/-- The terms of the cut. -/
abbrev Tm : Type := {t : M.Num // M.InI t}

theorem eta_refl {x : M.Num} (hx : M.InI x) : M.Eta x x := M.ax_e1 hx

theorem eta_symm {x y : M.Num} (hx : M.InI x) (hy : M.InI y) (h : M.Eta x y) : M.Eta y x :=
  M.ax_e2 (x := x) (y := y) (z := x) hx hy hx h (M.eta_refl hx)

theorem eta_trans {x y z : M.Num} (hx : M.InI x) (hy : M.InI y) (hz : M.InI z) (h : M.Eta x y)
    (h' : M.Eta y z) : M.Eta x z :=
  M.ax_e2 (x := y) (y := x) (z := z) hy hx hz (M.eta_symm hx hy h) h'

/-- The interpreted equality, on the terms of the cut. -/
instance tmSetoid : Setoid M.Tm where
  r a b := M.Eta a.1 b.1
  iseqv := ⟨fun a => M.eta_refl a.2, fun {a b} h => M.eta_symm a.2 b.2 h,
    fun {a b c} h h' => M.eta_trans a.2 b.2 c.2 h h'⟩

/-- The carrier of the model of NF: the terms of the cut modulo the interpreted equality. -/
def NV : Type := Quotient M.tmSetoid

/-- The class of a term. -/
def nmk (a : M.Tm) : M.NV := Quotient.mk M.tmSetoid a

theorem nmk_eq {a b : M.Tm} : M.nmk a = M.nmk b ↔ M.Eta a.1 b.1 :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The interpreted membership, on the classes. -/
def nmem : M.NV → M.NV → Prop :=
  Quotient.lift₂ (s₁ := M.tmSetoid) (s₂ := M.tmSetoid) (fun a b => M.Eps a.1 b.1)
    (fun a b a' b' ha hb => propext ⟨fun h => M.ax_e3 a.2 a'.2 b.2 b'.2 ha hb h,
      fun h => M.ax_e3 a'.2 a.2 b'.2 b.2 (M.eta_symm a.2 a'.2 ha) (M.eta_symm b.2 b'.2 hb) h⟩)

/-- The singleton, on the classes. -/
noncomputable def nsing : M.NV → M.NV :=
  Quotient.map (sa := M.tmSetoid) (sb := M.tmSetoid)
    (fun a => (⟨sgT a.1, M.i_sgT a.2⟩ : M.Tm)) (fun a b h => M.ax_e4a a.2 b.2 h)

/-- The unordered pair, on the classes. -/
noncomputable def nup : M.NV → M.NV → M.NV :=
  Quotient.map₂ (sa := M.tmSetoid) (sb := M.tmSetoid) (sc := M.tmSetoid)
    (fun a b => (⟨upT a.1 b.1, M.i_upT a.2 b.2⟩ : M.Tm))
    (fun a a' ha b b' hb => M.ax_e4b a.2 a'.2 b.2 b'.2 ha hb)

theorem nmem_mk (a b : M.Tm) : M.nmem (M.nmk a) (M.nmk b) ↔ M.Eps a.1 b.1 := Iff.rfl

theorem nsing_mk (a : M.Tm) : M.nsing (M.nmk a) = M.nmk ⟨sgT a.1, M.i_sgT a.2⟩ := rfl

theorem nup_mk (a b : M.Tm) : M.nup (M.nmk a) (M.nmk b) = M.nmk ⟨upT a.1 b.1, M.i_upT a.2 b.2⟩ :=
  rfl

theorem nop_mk (a b : M.Tm) :
    M.nup (M.nsing (M.nmk a)) (M.nup (M.nmk a) (M.nmk b)) = M.nmk ⟨opT a.1 b.1, M.i_opT a.2 b.2⟩ :=
  rfl

theorem nmk_surj (x : M.NV) : ∃ a : M.Tm, x = M.nmk a :=
  Quotient.inductionOn x (fun a => ⟨a, rfl⟩)

set_option maxHeartbeats 400000 in
/-- **The term model.** -/
noncomputable def termModel : ConNF.NF.NFModel M.NV where
  mem := M.nmem
  sing := M.nsing
  up := M.nup
  ext := by
    intro x y
    obtain ⟨a, rfl⟩ := M.nmk_surj x
    obtain ⟨b, rfl⟩ := M.nmk_surj y
    intro h
    exact M.nmk_eq.mpr (M.ax_m1 a.2 b.2 (h (M.nmk ⟨dT a.1 b.1, M.i_dT a.2 b.2⟩)))
  mem_sing := by
    intro x y
    obtain ⟨a, rfl⟩ := M.nmk_surj x
    obtain ⟨b, rfl⟩ := M.nmk_surj y
    exact (M.ax_m2 a.2 b.2).trans M.nmk_eq.symm
  mem_up := by
    intro x y z
    obtain ⟨a, rfl⟩ := M.nmk_surj x
    obtain ⟨b, rfl⟩ := M.nmk_surj y
    obtain ⟨c, rfl⟩ := M.nmk_surj z
    exact (M.ax_m3 a.2 b.2 c.2).trans (or_congr M.nmk_eq.symm M.nmk_eq.symm)
  inter := by
    intro x y
    obtain ⟨a, rfl⟩ := M.nmk_surj x
    obtain ⟨b, rfl⟩ := M.nmk_surj y
    refine ⟨M.nmk ⟨inT a.1 b.1, M.i_inT a.2 b.2⟩, fun z => ?_⟩
    obtain ⟨c, rfl⟩ := M.nmk_surj z
    exact M.ax_m4 a.2 b.2 c.2
  compl := by
    intro x
    obtain ⟨a, rfl⟩ := M.nmk_surj x
    refine ⟨M.nmk ⟨coT a.1, M.i_coT a.2⟩, fun z => ?_⟩
    obtain ⟨c, rfl⟩ := M.nmk_surj z
    exact M.ax_m5 a.2 c.2
  singletonImage := by
    intro x
    obtain ⟨a, rfl⟩ := M.nmk_surj x
    refine ⟨M.nmk ⟨siT a.1, M.i_siT a.2⟩, fun z w => ?_⟩
    obtain ⟨c, rfl⟩ := M.nmk_surj z
    obtain ⟨e, rfl⟩ := M.nmk_surj w
    exact M.ax_m6 a.2 c.2 e.2
  insertion2 := by
    intro x
    obtain ⟨a, rfl⟩ := M.nmk_surj x
    refine ⟨M.nmk ⟨i2T a.1, M.i_i2T a.2⟩, fun p q r => ?_⟩
    obtain ⟨c, rfl⟩ := M.nmk_surj p
    obtain ⟨e, rfl⟩ := M.nmk_surj q
    obtain ⟨f, rfl⟩ := M.nmk_surj r
    exact M.ax_m7 a.2 c.2 e.2 f.2
  insertion3 := by
    intro x
    obtain ⟨a, rfl⟩ := M.nmk_surj x
    refine ⟨M.nmk ⟨i3T a.1, M.i_i3T a.2⟩, fun p q r => ?_⟩
    obtain ⟨c, rfl⟩ := M.nmk_surj p
    obtain ⟨e, rfl⟩ := M.nmk_surj q
    obtain ⟨f, rfl⟩ := M.nmk_surj r
    exact M.ax_m8 a.2 c.2 e.2 f.2
  vCross := by
    intro x
    obtain ⟨a, rfl⟩ := M.nmk_surj x
    refine ⟨M.nmk ⟨vcT a.1, M.i_vcT a.2⟩, fun p => ?_⟩
    obtain ⟨c, rfl⟩ := M.nmk_surj p
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := M.ax_m9a a.2 c.2 h
      refine ⟨M.nmk ⟨p1T c.1, M.i_p1T c.2⟩, M.nmk ⟨p2T c.1, M.i_p2T c.2⟩, ?_, h2⟩
      show M.nmk c = M.nup (M.nsing (M.nmk ⟨p1T c.1, M.i_p1T c.2⟩))
        (M.nup (M.nmk ⟨p1T c.1, M.i_p1T c.2⟩) (M.nmk ⟨p2T c.1, M.i_p2T c.2⟩))
      rw [M.nop_mk]
      exact M.nmk_eq.mpr h1
    · rintro ⟨q, r, e, hm⟩
      obtain ⟨e', rfl⟩ := M.nmk_surj q
      obtain ⟨f, rfl⟩ := M.nmk_surj r
      change M.nmk c = M.nup (M.nsing (M.nmk e')) (M.nup (M.nmk e') (M.nmk f)) at e
      rw [M.nop_mk] at e
      exact M.ax_m9b a.2 c.2 e'.2 f.2
        ((M.nmk_eq (a := c) (b := ⟨opT e'.1 f.1, M.i_opT e'.2 f.2⟩)).mp e) hm
  typeLower := by
    intro x
    obtain ⟨a, rfl⟩ := M.nmk_surj x
    refine ⟨M.nmk ⟨tlT a.1, M.i_tlT a.2⟩, fun p => ?_⟩
    obtain ⟨c, rfl⟩ := M.nmk_surj p
    constructor
    · intro h q
      obtain ⟨e, rfl⟩ := M.nmk_surj q
      exact M.ax_m10a a.2 c.2 e.2 h
    · intro h
      exact M.ax_m10b a.2 c.2 (h (M.nmk ⟨wtT c.1 a.1, M.i_wtT c.2 a.2⟩))
  converse := by
    intro x
    obtain ⟨a, rfl⟩ := M.nmk_surj x
    refine ⟨M.nmk ⟨cvT a.1, M.i_cvT a.2⟩, fun p q => ?_⟩
    obtain ⟨c, rfl⟩ := M.nmk_surj p
    obtain ⟨e, rfl⟩ := M.nmk_surj q
    exact M.ax_m11 a.2 c.2 e.2
  cardinalOne := by
    refine ⟨M.nmk ⟨c1T, M.i_c1T⟩, fun p => ?_⟩
    obtain ⟨c, rfl⟩ := M.nmk_surj p
    constructor
    · intro h
      refine ⟨M.nmk ⟨elT c.1, M.i_elT c.2⟩, ?_⟩
      show M.nmk c = M.nsing (M.nmk ⟨elT c.1, M.i_elT c.2⟩)
      rw [M.nsing_mk]
      exact M.nmk_eq.mpr (M.ax_m12a c.2 h)
    · rintro ⟨q, e⟩
      obtain ⟨e', rfl⟩ := M.nmk_surj q
      change M.nmk c = M.nsing (M.nmk e') at e
      rw [M.nsing_mk] at e
      exact M.ax_m12b c.2 e'.2 ((M.nmk_eq (a := c) (b := ⟨sgT e'.1, M.i_sgT e'.2⟩)).mp e)
  subset := by
    refine ⟨M.nmk ⟨sbT, M.i_sbT⟩, fun p q => ?_⟩
    obtain ⟨c, rfl⟩ := M.nmk_surj p
    obtain ⟨e, rfl⟩ := M.nmk_surj q
    constructor
    · intro h r
      obtain ⟨f, rfl⟩ := M.nmk_surj r
      exact M.ax_m13a c.2 e.2 f.2 h
    · intro h
      exact M.ax_m13b c.2 e.2 (h (M.nmk ⟨wsT c.1 e.1, M.i_wsT c.2 e.2⟩))

/-- **In every model of NFU + Infinity, the term model is a model of NF**: the codes of closed
terms in the cut `InI`, with `Eps` as membership and modulo `Eta`, satisfy extensionality and
every instance of stratified comprehension. -/
theorem termModel_isNF : ConNF.NF.IsNF M.NV M.nmem := M.termModel.isNF

end Model

end NFUCut

