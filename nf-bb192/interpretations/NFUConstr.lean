module

public import ConNF.NF.NFUHartogs

/-!
# The constructible ladder, continued: Lemma 3.2 (§3.3 of the note)

This file continues `NFUHartogs`. It works with a solution of the recursion that defines the
hierarchy of names (`HierData`) and with the order of the names (`IsPrec`), and proves
Lemma 3.2 (`lemma_3_2`, `Lemma32`).

The order of the names.
* `pr_iff`: a name `(ρ, k, u)` is at most `(ρ', k', u')` if and only if `ρ` is below `ρ'`, or
  `ρ = ρ'` and `k < k'`, or `ρ = ρ'`, `k = k'` and `u'` is not lexicographically below `u`.
* `pr_total`, `pr_trans`, `pr_refl`; `lex_min`, `pr_least`: the order is a total preorder in
  which every set that contains a name has a least member.
* `tie_sim`: two names each at most the other denote the same set. `IsCan`, `exists_can`,
  `can_vals`: canonical names.
* `Lt`, `hier_lt`, `lt_tri`, `lt_least`: the relation symbol `2` of the hierarchy is a
  well-ordering of the denoted sets. `hier_T_false`: the symbol `1` is never true when the
  hierarchy is built with an empty oracle.

Hulls and condensation.
* `ClosedR`: a set of names is closed under six rules (markers of ranks, values of parameters,
  names formed from members, canonical names, least witnesses, recorded generators).
  `IsHull`, `exists_hull`, `hull_closed`.
* `IsColl`, `exists_coll`: the order collapse of a set of stages. `IsPi`, `PiRel`: the
  collapsing map on names. `CondData`, `cond_all`: condensation at every stage.
* `IsSig`, `Gen`, `Small`, `IsNext`: a stage is generated from `ν` and a name; `ν`-small
  stages; the least stage that is not `ν`-small. `next_lim`, `next_gt`.
* `hull_collapse`: the collapse of a hull is generated. `next_absorb`: absorption.
  `next_sep`, `next_coll`: Separation and Collection at the least stage that is not small, in
  semantic form.

The count.
* `rung_lift`: a rung maps one-to-one into every higher rung.
* `RuleR`, `StepR`, `EvData`: terms for the members of a hull, and the least relation closed
  under the steps of their evaluation. `rule_fun`, `ev_fun`: evaluation is a function up to
  the order of names. `evX_closed`, `evX_all`: every name of rank below a generated stage is
  the value of a term.
* `gen_small`, `gen_count`: if the stages below `ν` map one-to-one into the rung `i`, the
  stages below a stage generated from `ν` map one-to-one into the rung `i + 1`.
* `next_exists`: the least stage that is not `ν`-small exists, and the stages below it map
  one-to-one into the rung `i + 3`.

The axioms as coded sentences.
* `cSep`, `hier_sep`; `cColl`, `hier_coll`: every instance of Separation and of Collection is
  true at the least stage that is not small, under every sequence.
* `hier_wlin`, `hier_wirr`, `hier_wtrans`, `hier_wcong`, `hier_wleast`: the canonical order is
  a linear order that respects "have the same members" and in which every set that has a
  member has a least member.

The sequence of stages and Lemma 3.2.
* `stage_seq_raw`, `StageSeq`, `exists_stageSeq`: the stages `ν₀ < ν₁ < … < ν_{m₁}`, each the
  least stage that is not small over the one before, with the names `Pⁱ`.
* `pow_of_next`, `PowNames`, `exists_powNames`: `Pⁱ⁺¹` denotes the power set of the set denoted
  by `Pⁱ` in every later level.
* `NumNames`, `exists_numNames`: the numbers of the hierarchy are the numbers of the model.
* `exists_inner_seq`: the finite sequence of the iterated power sets is a member of the level.
* `Lemma32`, `lemma_3_2`, `lemma_3_2_calm` (at calm heights, with `lemma_3_1`); `l32_holds`,
  `l32_sep_holds`, `l32_coll_holds`: the passage to
  truth in the level as a set structure in the sense of §3.1.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

@[expose] public section

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

/-! ## The order of the names -/

/-- **Induction along a set well-ordering**, for a stratified condition. -/
theorem wo_ind_fml {r : V} (hr : M.IsWO r) (σ : ℕ → ℕ) (φ : Fml) (x : ℕ) (hφ : φ.strat σ = true)
    (ρ : ℕ → V)
    (step : ∀ α, M.mem (M.op α α) r →
      (∀ β, M.mem (M.op β α) r → β ≠ α → Sat M.mem M.isSet φ (Function.update ρ x β)) →
      Sat M.mem M.isSet φ (Function.update ρ x α))
    (α : V) (hα : M.mem (M.op α α) r) : Sat M.mem M.isSet φ (Function.update ρ x α) := by
  by_contra hcon
  obtain ⟨B, -, hB⟩ := M.comp σ (.neg φ) x (by simpa [Fml.strat] using hφ) ρ
  have hB' : ∀ a, M.mem a B ↔ ¬ Sat M.mem M.isSet φ (Function.update ρ x a) := by
    intro a
    rw [hB a]
    simp [Sat]
  obtain ⟨α0, hα0B, hα0, hmin⟩ := hr.least B ⟨α, (hB' α).mpr hcon, hα⟩
  refine (hB' α0).mp hα0B (step α0 hα0 (fun β hβ hne => ?_))
  by_contra hb
  exact hne (hr.antisymm β α0 hβ (hmin β ((hB' β).mpr hb) (hr.fld β α0 hβ).1))

theorem ltRaw_num (i' i : M.Num) :
    (∃ x, M.mem x M.nat ∧ ¬ x = (0 : M.Num).1 ∧ M.mem (M.trip i'.1 x i.1) M.adG) ↔
      i' + 1 ≤ i := by
  constructor
  · rintro ⟨x, hx, hne, h⟩
    have e := M.graph₂_val M.adG_spec (m := i') (n := ⟨x, hx⟩) h
    have e' : i' + ⟨x, hx⟩ = i := Subtype.ext e.symm
    rcases M.num_cases ⟨x, hx⟩ with h0 | ⟨k, hk⟩
    · exact (hne (congrArg Subtype.val h0)).elim
    · refine M.le_def.mpr ⟨k, ?_⟩
      rw [← e', hk, M.nsucc_eq_add_one]
      ring
  · intro h
    obtain ⟨c, hc⟩ := M.le_def.mp h
    refine ⟨(c + 1).1, (c + 1).2, fun e => M.succ_not_le_zero (x := c) (le_of_eq (Subtype.ext e)),
      ?_⟩
    have h1 := M.graph₂_app M.adG_spec i' (c + 1)
    have e : M.addN i' (c + 1) = i := by
      rw [← hc]
      show i' + (c + 1) = i' + 1 + c
      ring
    rw [e] at h1
    exact h1

/-- `x` is at most `y` in the order `Pr` of the names, or `x = y`. -/
def LeV (Pr x y : V) : Prop := x = y ∨ M.mem (M.op x y) Pr

/-- `u'` is strictly below `u` lexicographically at the indices up to `k`, at stage `β`, the
values being compared by `Pr`. -/
def LexLt (P th io Nt d Pr : V) (j : M.Num) (β : V) (k : M.Num) (u' u : V) : Prop :=
  ∃ i : M.Num, i ≤ k ∧ ∃ e' e, M.ValRaw P th io M.nat Nt j.1 d β u' i.1 e' ∧
    M.ValRaw P th io M.nat Nt j.1 d β u i.1 e ∧ M.LeV Pr e' e ∧ ¬ M.LeV Pr e e' ∧
    ∀ i' : M.Num, i' + 1 ≤ i → ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d β u' i'.1 g' ∧
      M.ValRaw P th io M.nat Nt j.1 d β u i'.1 g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g'

/-- `n` is the name of rank `ρ` with the formula number `k` and the parameters `u`. -/
def NameOf (P io : V) (j : M.Num) (n ρ : V) (k : M.Num) (u : V) : Prop :=
  ∃ f q, M.mem (M.quad j.1 ρ q n) P ∧ M.mem (M.quad j.1 f u q) P ∧ M.mem (M.op k.1 f) io

section prec

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem nameOf_rank {n ρ u : V} {k : M.Num} (h : M.NameOf P io j n ρ k u) :
    M.RankIs P io M.nat j.1 ρ n := by
  obtain ⟨f, q, h1, h2, h3⟩ := h
  exact ⟨f, u, q, h1, h2, k.1, k.2, h3⟩

theorem rank_nameOf {n ρ : V} (h : M.RankIs P io M.nat j.1 ρ n) :
    ∃ (k : M.Num) (u : V), M.NameOf P io j n ρ k u := by
  obtain ⟨f, u, q, h1, h2, k, hk, h3⟩ := h
  exact ⟨⟨k, hk⟩, u, f, q, h1, h2, h3⟩

theorem nameOf_unique (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {n ρ ρ' u u' : V}
    {k k' : M.Num} (h : M.NameOf P io j n ρ k u) (h' : M.NameOf P io j n ρ' k' u') :
    ρ = ρ' ∧ k = k' ∧ u = u' := by
  obtain ⟨f, q, h1, h2, h3⟩ := h
  obtain ⟨f', q', h1', h2', h3'⟩ := h'
  obtain ⟨e1, e2⟩ := hd.hP.inj _ _ _ _ _ _ h1 h1'
  rw [e2] at h2
  obtain ⟨e3, e4⟩ := hd.hP.inj _ _ _ _ _ _ h2 h2'
  rw [e3] at h3
  exact ⟨e1, Subtype.ext (hd.io_inj _ _ _ h3 h3'), e4⟩

theorem nameOf_exists (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ρ u : V}
    (hρ : M.mem (M.op ρ ρ) th) (hu : M.mem (M.op j.1 u) R) (k : M.Num) :
    ∃ n, M.NameOf P io j n ρ k u := by
  obtain ⟨f, hf⟩ := hd.io_tot k
  obtain ⟨q, hq⟩ := hd.hP.tot j hd.hj f u (hd.io_dom _ _ hf).2 hu
  obtain ⟨n, hn⟩ := hd.hP.tot j hd.hj ρ q (hd.th_rung ρ ρ hρ).1 (hd.hP.dom _ _ _ _ hq).2.2.2
  exact ⟨n, f, q, hn, hq, hf⟩

theorem leE_restr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {Pr0 β x y : V}
    (hPr : ∀ n n', M.mem (M.op n n') Pr ↔ ∃ ρx ρy, M.RankIs P io M.nat j.1 ρx n ∧
      M.RankIs P io M.nat j.1 ρy n' ∧ ((M.mem (M.op ρx ρy) th ∧ ¬ ρx = ρy) ∨
        (ρx = ρy ∧ ∃ yy, M.mem (M.quad j.1 n n' yy) P ∧ M.mem (M.op ρx yy) Pr0)))
    (hx : M.InNRaw P th io M.nat j.1 β x ∨ x = d) (hy : M.InNRaw P th io M.nat j.1 β y ∨ y = d) :
    M.LeERaw P th io M.nat j.1 (M.restr th Pr0 β) x y ↔ M.LeV Pr x y := by
  by_cases e : x = y
  · exact ⟨fun _ => Or.inl e, fun _ => Or.inl e⟩
  have both : M.InNRaw P th io M.nat j.1 β x ∧ M.InNRaw P th io M.nat j.1 β y := by
    rcases hx with hx | hx
    · rcases hy with hy | hy
      · exact ⟨hx, hy⟩
      · obtain ⟨βx, -, lt, ne⟩ := M.inN_rank hx
        rw [hy]
        exact ⟨hx, M.d_inN hd lt ne⟩
    · rcases hy with hy | hy
      · obtain ⟨βy, -, lt, ne⟩ := M.inN_rank hy
        rw [hx]
        exact ⟨M.d_inN hd lt ne, hy⟩
      · exact (e (hx.trans hy.symm)).elim
  obtain ⟨βx, rx, ltx, nex⟩ := M.inN_rank both.1
  constructor
  · rintro (h | ⟨ρx, ρy, r1, r2, h⟩)
    · exact Or.inl h
    · refine Or.inr ((hPr x y).mpr ⟨ρx, ρy, r1, r2, ?_⟩)
      rcases h with h | ⟨h1, yy, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, yy, h2, (M.mem_restr.mp h3).1⟩
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨ρx, ρy, r1, r2, h⟩ := (hPr x y).mp h
      refine Or.inr ⟨ρx, ρy, r1, r2, ?_⟩
      rcases h with h | ⟨h1, yy, h2, h3⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, yy, h2, M.mem_restr.mpr ⟨h3, ?_⟩⟩
        rw [M.rank_unique hd r1 rx]
        exact ⟨ltx, nex⟩

theorem lexLtRaw_iff (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {Pr0 β u u' : V}
    (hPr : ∀ n n', M.mem (M.op n n') Pr ↔ ∃ ρx ρy, M.RankIs P io M.nat j.1 ρx n ∧
      M.RankIs P io M.nat j.1 ρy n' ∧ ((M.mem (M.op ρx ρy) th ∧ ¬ ρx = ρy) ∨
        (ρx = ρy ∧ ∃ yy, M.mem (M.quad j.1 n n' yy) P ∧ M.mem (M.op ρx yy) Pr0)))
    (k : M.Num) :
    M.LexLtRaw P th io M.nat Nt j.1 d M.adG (0 : M.Num).1 (M.restr th Pr0 β) β k.1 u' u ↔
      M.LexLt P th io Nt d Pr j β k u' u := by
  have cv : ∀ {t t' i i' e e' : V}, M.ValRaw P th io M.nat Nt j.1 d β t i e →
      M.ValRaw P th io M.nat Nt j.1 d β t' i' e' →
      (M.LeERaw P th io M.nat j.1 (M.restr th Pr0 β) e e' ↔ M.LeV Pr e e') :=
    fun v1 v2 => M.leE_restr hd hPr (M.val_cases v1) (M.val_cases v2)
  constructor
  · rintro ⟨i, hi, hle, e', e, v1, v2, l1, l2, hall⟩
    refine ⟨⟨i, hi⟩, (M.leRaw_iff M.adG_spec ⟨i, hi⟩ k).mp hle, e', e, v1, v2, (cv v1 v2).mp l1,
      fun h => l2 ((cv v2 v1).mpr h), fun i' hi' => ?_⟩
    obtain ⟨g', g, w1, w2, m1, m2⟩ := hall i'.1 i'.2 ((M.ltRaw_num i' ⟨i, hi⟩).mpr hi')
    exact ⟨g', g, w1, w2, (cv w1 w2).mp m1, (cv w2 w1).mp m2⟩
  · rintro ⟨i, hle, e', e, v1, v2, l1, l2, hall⟩
    refine ⟨i.1, i.2, (M.leRaw_iff M.adG_spec i k).mpr hle, e', e, v1, v2, (cv v1 v2).mpr l1,
      fun h => l2 ((cv v2 v1).mp h), fun i' hi' hlt => ?_⟩
    obtain ⟨g', g, w1, w2, m1, m2⟩ := hall ⟨i', hi'⟩ ((M.ltRaw_num ⟨i', hi'⟩ i).mp hlt)
    exact ⟨g', g, w1, w2, (cv w1 w2).mpr m1, (cv w2 w1).mpr m2⟩

/-- **The order of the names, characterised.** For names `n = (ρ, k, u)` and `n' = (ρ', k',
u')`: `n` is at most `n'` if and only if `ρ` is below `ρ'`, or `ρ = ρ'` and `k < k'`, or
`ρ = ρ'`, `k = k'` and `u'` is not lexicographically below `u`. -/
theorem pr_iff (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n n' ρ ρ' u u' : V} {k k' : M.Num}
    (hn : M.NameOf P io j n ρ k u) (hn' : M.NameOf P io j n' ρ' k' u')
    (hρ : M.mem (M.op ρ ρ) th) :
    M.mem (M.op n n') Pr ↔ ((M.mem (M.op ρ ρ') th ∧ ρ ≠ ρ') ∨
      (ρ = ρ' ∧ ((k ≤ k' ∧ k ≠ k') ∨ (k = k' ∧ ¬ M.LexLt P th io Nt d Pr j ρ k u' u)))) := by
  obtain ⟨Pr0, hPr0, hPrf⟩ := hPr
  have rn := M.nameOf_rank hn
  have rn' := M.nameOf_rank hn'
  rw [hPrf n n']
  constructor
  · rintro ⟨ρx, ρy, r1, r2, h⟩
    rw [M.rank_unique hd r1 rn, M.rank_unique hd r2 rn'] at h
    rcases h with h | ⟨e, yy, hy, hy0⟩
    · exact Or.inl h
    · refine Or.inr ⟨e, ?_⟩
      obtain ⟨-, n1, n1', f1, u1, q1, f1', u1', q1', k1, k1', g1, g2, g3, g4, g5, g6, g7, g8, g9,
        g10⟩ := (hPr0 ρ yy).mp hy0
      obtain ⟨e1, e2⟩ := hd.hP.inj _ _ _ _ _ _ g1 hy
      rw [e1] at g2
      rw [e2] at g6
      have hk1 := M.nameOf_unique hd (⟨f1, q1, g2, g3, g5⟩ : M.NameOf P io j n ρ ⟨k1, g4⟩ u1) hn
      rw [← e] at hn'
      have hk1' := M.nameOf_unique hd
        (⟨f1', q1', g6, g7, g9⟩ : M.NameOf P io j n' ρ ⟨k1', g8⟩ u1') hn'
      obtain ⟨-, ek, eu⟩ := hk1
      obtain ⟨-, ek', eu'⟩ := hk1'
      have ekv : k1 = k.1 := congrArg Subtype.val ek
      have ekv' : k1' = k'.1 := congrArg Subtype.val ek'
      rw [ekv, ekv', eu, eu'] at g10
      rcases g10 with ⟨hle, hne⟩ | ⟨heq, hlex⟩
      · exact Or.inl ⟨(M.leRaw_iff M.adG_spec k k').mp hle, fun e3 => hne (congrArg Subtype.val e3)⟩
      · have ekk : k = k' := Subtype.ext heq
        exact Or.inr ⟨ekk, fun hl => hlex ((M.lexLtRaw_iff hd hPrf k).mpr hl)⟩
  · rintro (h | ⟨e, h⟩)
    · exact ⟨ρ, ρ', rn, rn', Or.inl h⟩
    · refine ⟨ρ, ρ', rn, rn', Or.inr ⟨e, ?_⟩⟩
      obtain ⟨f, q, h1, h2, h3⟩ := hn
      obtain ⟨f', q', h1', h2', h3'⟩ := hn'
      rw [← e] at h1'
      obtain ⟨yy, hyy⟩ := hd.hP.tot j hd.hj n n' (hd.hP.dom _ _ _ _ h1).2.2.2
        (hd.hP.dom _ _ _ _ h1').2.2.2
      refine ⟨yy, hyy, (hPr0 ρ yy).mpr ⟨hρ, n, n', f, u, q, f', u', q', k.1, k'.1, hyy, h1, h2,
        k.2, h3, h1', h2', k'.2, h3', ?_⟩⟩
      rcases h with ⟨hle, hne⟩ | ⟨heq, hlex⟩
      · exact Or.inl ⟨(M.leRaw_iff M.adG_spec k k').mpr hle, fun e3 => hne (Subtype.ext e3)⟩
      · exact Or.inr ⟨congrArg Subtype.val heq,
          fun hl => hlex ((M.lexLtRaw_iff hd hPrf k).mp hl)⟩

end prec

/-! ## The order of the names is a total preorder -/

/-- `LeV` with `Pr` the name `162`, for the names `x`, `y`. -/
def fLeV (x y : ℕ) : Fml := Fml.or (.eq x y) (fApp 162 x y)

theorem sat_fLeV {x y : ℕ} (ρ : ℕ → V) (hx : 199 < x) (hy : 199 < y) :
    Sat M.mem M.isSet (fLeV x y) ρ ↔ M.LeV (ρ 162) (ρ x) (ρ y) := by
  have b1 : x < 30 ∨ 59 < x := by omega
  have b2 : y < 30 ∨ 59 < y := by omega
  simp [fLeV, LeV, Sat, M.sat_or, M.sat_fApp', b1, b2]

/-- On the names of rank `ρ` the order `Pr` is total and transitive. -/
def PrOrdAt (P io nat j Pr ρ : V) : Prop :=
  (∀ n n', M.RankIs P io nat j ρ n → M.RankIs P io nat j ρ n' →
    M.mem (M.op n n') Pr ∨ M.mem (M.op n' n) Pr) ∧
  ∀ n n' n'', M.RankIs P io nat j ρ n → M.RankIs P io nat j ρ n' → M.RankIs P io nat j ρ n'' →
    M.mem (M.op n n') Pr → M.mem (M.op n' n'') Pr → M.mem (M.op n n'') Pr

/-- `PrOrdAt`, with `ρ` the name `250`. -/
def prOrdFml : Fml :=
  .and (.all 251 (.all 252 (Fml.imp (fRank 250 251) (Fml.imp (fRank 250 252) (Fml.or (fApp 162
    251 252) (fApp 162 252 251)))))) (.all 251 (.all 252 (.all 253 (Fml.imp (fRank 250 251)
    (Fml.imp (fRank 250 252) (Fml.imp (fRank 250 253) (Fml.imp (fApp 162 251 252) (Fml.imp (fApp
    162 252 253) (fApp 162 251 253)))))))))

theorem sat_prOrdFml (ρ : ℕ → V) : Sat M.mem M.isSet prOrdFml ρ ↔
    M.PrOrdAt (ρ 20) (ρ 24) (ρ 27) (ρ 25) (ρ 162) (ρ 250) := by
  simp [prOrdFml, PrOrdAt, Sat, M.sat_imp, M.sat_or, M.sat_fRank, M.sat_fApp',
    Function.update_apply]

section prec2

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem pr_names (hPr : M.IsPrec P th io Nt d Pr j) {n n' : V} (h : M.mem (M.op n n') Pr) :
    ∃ ρ ρ', M.RankIs P io M.nat j.1 ρ n ∧ M.RankIs P io M.nat j.1 ρ' n' ∧
      M.mem (M.op ρ ρ') th := by
  obtain ⟨Pr0, hPr0, hPrf⟩ := hPr
  obtain ⟨ρx, ρy, r1, r2, h1 | ⟨e, yy, -, h2⟩⟩ := (hPrf n n').mp h
  · exact ⟨ρx, ρy, r1, r2, h1.1⟩
  · refine ⟨ρx, ρy, r1, r2, ?_⟩
    rw [← e]
    exact ((hPr0 ρx yy).mp h2).1

theorem pr_of_lt (hPr : M.IsPrec P th io Nt d Pr j) {n n' ρ ρ' : V}
    (rn : M.RankIs P io M.nat j.1 ρ n) (rn' : M.RankIs P io M.nat j.1 ρ' n')
    (h : M.mem (M.op ρ ρ') th) (hne : ρ ≠ ρ') : M.mem (M.op n n') Pr := by
  obtain ⟨Pr0, -, hPrf⟩ := hPr
  exact (hPrf n n').mpr ⟨ρ, ρ', rn, rn', Or.inl ⟨h, hne⟩⟩

theorem pr_rank_le (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n n' ρ ρ' : V}
    (rn : M.RankIs P io M.nat j.1 ρ n) (rn' : M.RankIs P io M.nat j.1 ρ' n')
    (h : M.mem (M.op n n') Pr) : M.mem (M.op ρ ρ') th := by
  obtain ⟨ρ1, ρ1', r1, r1', h1⟩ := M.pr_names hPr h
  rw [M.rank_unique hd rn r1, M.rank_unique hd rn' r1']
  exact h1

/-- Two sequences are not each lexicographically below the other. -/
theorem lex_asymm (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ρ u u' : V}
    {k : M.Num} (h1 : M.LexLt P th io Nt d Pr j ρ k u' u)
    (h2 : M.LexLt P th io Nt d Pr j ρ k u u') : False := by
  obtain ⟨i, hi, e', e, v1, v2, l1, l2, hall⟩ := h1
  obtain ⟨i1, hi1, f, f', w1, w2, m1, m2, hall1⟩ := h2
  rcases M.le_total' i i1 with h | h
  · rcases M.eq_or_succ_le h with e0 | e0
    · rw [← e0] at w1 w2
      rw [M.val_unique hd w1 v2, M.val_unique hd w2 v1] at m1
      exact l2 m1
    · obtain ⟨g', g, a1, a2, a3, a4⟩ := hall1 i e0
      rw [M.val_unique hd a1 v2, M.val_unique hd a2 v1] at a3
      exact l2 a3
  · rcases M.eq_or_succ_le h with e0 | e0
    · rw [e0] at w1 w2
      rw [M.val_unique hd w1 v2, M.val_unique hd w2 v1] at m1
      exact l2 m1
    · obtain ⟨g', g, a1, a2, a3, a4⟩ := hall i1 e0
      rw [M.val_unique hd a1 w2, M.val_unique hd a2 w1] at a3
      exact m2 a3

/-- If `u''` is lexicographically below `u` then `u'` is below `u` or `u''` is below `u'`,
provided the values at the stage are totally and transitively ordered. -/
theorem lex_negtrans (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ρ u u' u'' : V}
    {k : M.Num}
    (vtot : ∀ x y, (M.InNRaw P th io M.nat j.1 ρ x ∨ x = d) →
      (M.InNRaw P th io M.nat j.1 ρ y ∨ y = d) → M.LeV Pr x y ∨ M.LeV Pr y x)
    (vtrans : ∀ x y z, (M.InNRaw P th io M.nat j.1 ρ x ∨ x = d) →
      (M.InNRaw P th io M.nat j.1 ρ y ∨ y = d) → (M.InNRaw P th io M.nat j.1 ρ z ∨ z = d) →
      M.LeV Pr x y → M.LeV Pr y z → M.LeV Pr x z)
    (h : M.LexLt P th io Nt d Pr j ρ k u'' u) :
    M.LexLt P th io Nt d Pr j ρ k u' u ∨ M.LexLt P th io Nt d Pr j ρ k u'' u' := by
  obtain ⟨i, hi, a'', a, v1, v2, l1, l2, hall⟩ := h
  have vex : ∀ (t i : V), ∃ e, M.ValRaw P th io M.nat Nt j.1 d ρ t i e := fun t i =>
    M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) ρ t i
  -- the conclusion at an index `i0` up to which `u'` ties with `u` and `u''` ties with `u`
  have key : ∀ i0 : M.Num, i0 ≤ k →
      (∀ i' : M.Num, i' + 1 ≤ i0 → ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d ρ u' i'.1 g' ∧
        M.ValRaw P th io M.nat Nt j.1 d ρ u i'.1 g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g') →
      (∀ i' : M.Num, i' + 1 ≤ i0 → ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d ρ u'' i'.1 g' ∧
        M.ValRaw P th io M.nat Nt j.1 d ρ u i'.1 g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g') →
      ∀ c0 a0 b0, M.ValRaw P th io M.nat Nt j.1 d ρ u'' i0.1 c0 →
        M.ValRaw P th io M.nat Nt j.1 d ρ u i0.1 a0 → M.ValRaw P th io M.nat Nt j.1 d ρ u' i0.1 b0 →
        M.LeV Pr c0 a0 → (M.LeV Pr a0 c0 → ¬ (M.LeV Pr b0 a0 ∧ M.LeV Pr a0 b0)) →
        (¬ M.LeV Pr a0 c0 ∨ ¬ (M.LeV Pr b0 a0 ∧ M.LeV Pr a0 b0)) →
        M.LexLt P th io Nt d Pr j ρ k u' u ∨ M.LexLt P th io Nt d Pr j ρ k u'' u' := by
    intro i0 hi0 tie1 tie2 c0 a0 b0 vc va vb hca hcase hne
    have ties : ∀ i' : M.Num, i' + 1 ≤ i0 → ∃ g' g,
        M.ValRaw P th io M.nat Nt j.1 d ρ u'' i'.1 g' ∧ M.ValRaw P th io M.nat Nt j.1 d ρ u' i'.1 g ∧
        M.LeV Pr g' g ∧ M.LeV Pr g g' := by
      intro i' hi'
      obtain ⟨x1, y1, p1, p2, p3, p4⟩ := tie1 i' hi'
      obtain ⟨x2, y2, q1, q2, q3, q4⟩ := tie2 i' hi'
      rw [M.val_unique hd q2 p2] at q3 q4
      exact ⟨x2, x1, q1, p1,
        vtrans _ _ _ (M.val_cases q1) (M.val_cases p2) (M.val_cases p1) q3 p4,
        vtrans _ _ _ (M.val_cases p1) (M.val_cases p2) (M.val_cases q1) p3 q4⟩
    by_cases hstrict : M.LeV Pr b0 a0 ∧ ¬ M.LeV Pr a0 b0
    · exact Or.inl ⟨i0, hi0, b0, a0, vb, va, hstrict.1, hstrict.2, tie1⟩
    · have hab : M.LeV Pr a0 b0 := by
        rcases vtot a0 b0 (M.val_cases va) (M.val_cases vb) with h1 | h1
        · exact h1
        · by_contra h2
          exact hstrict ⟨h1, h2⟩
      refine Or.inr ⟨i0, hi0, c0, b0, vc, vb,
        vtrans _ _ _ (M.val_cases vc) (M.val_cases va) (M.val_cases vb) hca hab, fun hbc => ?_,
        ties⟩
      have hba : M.LeV Pr b0 a0 :=
        vtrans _ _ _ (M.val_cases vb) (M.val_cases vc) (M.val_cases va) hbc hca
      rcases hne with h3 | h3
      · exact h3 (vtrans _ _ _ (M.val_cases va) (M.val_cases vb) (M.val_cases vc) hab hbc)
      · exact h3 ⟨hba, hab⟩
  by_cases hT : ∀ i' : M.Num, i' + 1 ≤ i → ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d ρ u' i'.1 g' ∧
      M.ValRaw P th io M.nat Nt j.1 d ρ u i'.1 g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g'
  · obtain ⟨b, vb⟩ := vex u' i.1
    exact key i hi hT hall a'' a b v1 v2 vb l1 (fun h => (l2 h).elim) (Or.inl l2)
  · -- the least index at which `u'` does not tie with `u`
    obtain ⟨S, -, hS0⟩ := M.comp (σW [(20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (162, 5)])
      (.and (.mem 229 27) (.neg (Fml.ex 230 (Fml.ex 231 (.and (fVal 250 224 229 230) (.and (fVal 250 225 229 231) (.and (fLeV 230 231) (fLeV 231 230)))))))) 229 rfl
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 162 Pr) 250 ρ)
        224 u' |> fun r => Function.update r 225 u)
    have hS : ∀ x, M.mem x S ↔ M.mem x M.nat ∧ ¬ ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d ρ u' x g' ∧
        M.ValRaw P th io M.nat Nt j.1 d ρ u x g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g' := by
      intro x
      rw [hS0 x]
      simp [Sat, M.sat_ex, M.sat_fVal, M.sat_fLeV, Function.update_apply]
    have hne : ∃ n : M.Num, M.mem n.1 S := by
      by_contra hcon
      refine hT (fun i' hi' => ?_)
      by_contra h1
      exact hcon ⟨i', (hS _).mpr ⟨i'.2, h1⟩⟩
    obtain ⟨i0, hi0S, hmin⟩ := M.nat_least hne
    have hnt := ((hS _).mp hi0S).2
    have hlt : i0 + 1 ≤ i := by
      by_contra hcon
      refine hT (fun i' hi' => ?_)
      by_contra h1
      have h2 := hmin i' ((hS _).mpr ⟨i'.2, h1⟩)
      exact hcon (le_trans (add_le_add h2 (le_refl 1)) hi')
    have tie1 : ∀ i' : M.Num, i' + 1 ≤ i0 → ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d ρ u' i'.1 g' ∧
        M.ValRaw P th io M.nat Nt j.1 d ρ u i'.1 g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g' := by
      intro i' hi'
      by_contra h1
      exact M.not_succ_le i' (le_trans hi' (hmin i' ((hS _).mpr ⟨i'.2, h1⟩)))
    have tie2 : ∀ i' : M.Num, i' + 1 ≤ i0 → ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d ρ u'' i'.1 g' ∧
        M.ValRaw P th io M.nat Nt j.1 d ρ u i'.1 g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g' :=
      fun i' hi' => hall i' (le_trans hi' (le_trans (M.le_add_one i0) hlt))
    obtain ⟨c0, a0, vc, va, hca, hac⟩ := hall i0 hlt
    obtain ⟨b0, vb⟩ := vex u' i0.1
    exact key i0 (le_trans (le_trans (M.le_add_one i0) hlt) hi) tie1 tie2 c0 a0 b0 vc va vb hca
      (fun _ hboth => hnt ⟨b0, a0, vb, va, hboth.1, hboth.2⟩)
      (Or.inr (fun hboth => hnt ⟨b0, a0, vb, va, hboth.1, hboth.2⟩))

end prec2

section prec3

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem pr_total_of (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n n' ρ ρ' : V}
    (rn : M.RankIs P io M.nat j.1 ρ n) (rn' : M.RankIs P io M.nat j.1 ρ' n')
    (hρ : M.mem (M.op ρ ρ) th) (hρ' : M.mem (M.op ρ' ρ') th)
    (H : ρ = ρ' → M.PrOrdAt P io M.nat j.1 Pr ρ) :
    M.mem (M.op n n') Pr ∨ M.mem (M.op n' n) Pr := by
  by_cases e : ρ = ρ'
  · subst e
    exact (H rfl).1 n n' rn rn'
  · rcases M.wo_total hd.hth hρ hρ' with h | h
    · exact Or.inl (M.pr_of_lt hPr rn rn' h e)
    · exact Or.inr (M.pr_of_lt hPr rn' rn h (fun e' => e e'.symm))

theorem pr_trans_of (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n n' n'' ρ ρ' ρ'' : V}
    (rn : M.RankIs P io M.nat j.1 ρ n) (rn' : M.RankIs P io M.nat j.1 ρ' n')
    (rn'' : M.RankIs P io M.nat j.1 ρ'' n'')
    (H : ρ = ρ' → ρ' = ρ'' → M.PrOrdAt P io M.nat j.1 Pr ρ)
    (h1 : M.mem (M.op n n') Pr) (h2 : M.mem (M.op n' n'') Pr) : M.mem (M.op n n'') Pr := by
  have l1 := M.pr_rank_le hd hPr rn rn' h1
  have l2 := M.pr_rank_le hd hPr rn' rn'' h2
  by_cases e1 : ρ = ρ'
  · by_cases e2 : ρ' = ρ''
    · subst e1
      subst e2
      exact (H rfl rfl).2 n n' n'' rn rn' rn'' h1 h2
    · refine M.pr_of_lt hPr rn rn'' (hd.hth.trans _ _ _ l1 l2) (fun e => e2 ?_)
      rw [← e, ← e1] at l2
      exact (e1.symm.trans e)
  · refine M.pr_of_lt hPr rn rn'' (hd.hth.trans _ _ _ l1 l2) (fun e => e1 ?_)
    rw [← e] at l2
    exact hd.hth.antisymm _ _ l1 l2

theorem val_inN_of_ne (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ρ x : V}
    (hx : M.InNRaw P th io M.nat j.1 ρ x ∨ x = d) (hne : ∃ z, M.InNRaw P th io M.nat j.1 ρ z) :
    M.InNRaw P th io M.nat j.1 ρ x := by
  rcases hx with hx | hx
  · exact hx
  · obtain ⟨z, hz⟩ := hne
    obtain ⟨β, -, lt, ne⟩ := M.inN_rank hz
    rw [hx]
    exact M.d_inN hd lt ne

theorem val_eq_d_of_empty {ρ x : V} (hx : M.InNRaw P th io M.nat j.1 ρ x ∨ x = d)
    (hne : ¬ ∃ z, M.InNRaw P th io M.nat j.1 ρ z) : x = d := by
  rcases hx with hx | hx
  · exact (hne ⟨x, hx⟩).elim
  · exact hx

theorem leV_total_of (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {ρ : V}
    (hlow : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.PrOrdAt P io M.nat j.1 Pr β) (x y : V)
    (hx : M.InNRaw P th io M.nat j.1 ρ x ∨ x = d) (hy : M.InNRaw P th io M.nat j.1 ρ y ∨ y = d) :
    M.LeV Pr x y ∨ M.LeV Pr y x := by
  by_cases hne : ∃ z, M.InNRaw P th io M.nat j.1 ρ z
  · obtain ⟨βx, rx, ltx, nex⟩ := M.inN_rank (M.val_inN_of_ne hd hx hne)
    obtain ⟨βy, ry, lty, ney⟩ := M.inN_rank (M.val_inN_of_ne hd hy hne)
    rcases M.pr_total_of hd hPr rx ry (hd.hth.fld _ _ ltx).1 (hd.hth.fld _ _ lty).1
      (fun _ => hlow βx ltx nex) with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (Or.inl ((M.val_eq_d_of_empty hx hne).trans (M.val_eq_d_of_empty hy hne).symm))

theorem leV_trans_of (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {ρ : V}
    (hlow : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.PrOrdAt P io M.nat j.1 Pr β) (x y z : V)
    (hx : M.InNRaw P th io M.nat j.1 ρ x ∨ x = d) (hy : M.InNRaw P th io M.nat j.1 ρ y ∨ y = d)
    (hz : M.InNRaw P th io M.nat j.1 ρ z ∨ z = d)
    (h1 : M.LeV Pr x y) (h2 : M.LeV Pr y z) : M.LeV Pr x z := by
  by_cases hne : ∃ z, M.InNRaw P th io M.nat j.1 ρ z
  · rcases h1 with h1 | h1
    · rw [h1]
      exact h2
    rcases h2 with h2 | h2
    · rw [← h2]
      exact Or.inr h1
    obtain ⟨βx, rx, ltx, nex⟩ := M.inN_rank (M.val_inN_of_ne hd hx hne)
    obtain ⟨βy, ry, lty, ney⟩ := M.inN_rank (M.val_inN_of_ne hd hy hne)
    obtain ⟨βz, rz, ltz, nez⟩ := M.inN_rank (M.val_inN_of_ne hd hz hne)
    exact Or.inr (M.pr_trans_of hd hPr rx ry rz (fun _ _ => hlow βx ltx nex) h1 h2)
  · exact Or.inl ((M.val_eq_d_of_empty hx hne).trans (M.val_eq_d_of_empty hz hne).symm)

/-- **The order of the names is total and transitive** on the names of each rank. -/
theorem prOrd_all (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {ρ : V} (hρ : M.mem (M.op ρ ρ) th) :
    M.PrOrdAt P io M.nat j.1 Pr ρ := by
  have key := M.wo_ind_fml hd.hth (σW [(20, 7), (24, 5), (27, 3), (162, 5)]) prOrdFml 250 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (fun _ => dflt) 20 P) 24 io) 25 j.1) 27 M.nat) 162 Pr) (fun α hα ih => ?_) ρ hρ
  · rw [M.sat_prOrdFml] at key
    simpa [Function.update_apply] using key
  · rw [M.sat_prOrdFml]
    simp only [Function.update_apply]
    simp only [show ((250 : ℕ) = 20) = False from by simp, show ((250 : ℕ) = 24) = False from by simp,
      show ((250 : ℕ) = 25) = False from by simp, show ((250 : ℕ) = 27) = False from by simp,
      show ((250 : ℕ) = 162) = False from by simp, ite_true, ite_false]
    norm_num
    have hlow : ∀ β, M.mem (M.op β α) th → β ≠ α → M.PrOrdAt P io M.nat j.1 Pr β := by
      intro β hβ hne
      have h1 := ih β hβ hne
      rw [M.sat_prOrdFml] at h1
      simpa [Function.update_apply] using h1
    refine ⟨fun n n' rn rn' => ?_, fun n n' n'' rn rn' rn'' h1 h2 => ?_⟩
    · obtain ⟨k, u, hn⟩ := M.rank_nameOf rn
      obtain ⟨k', u', hn'⟩ := M.rank_nameOf rn'
      rw [M.pr_iff hd hPr hn hn' hα, M.pr_iff hd hPr hn' hn hα]
      rcases M.le_total' k k' with h | h
      · rcases M.eq_or_succ_le h with e | e
        · subst e
          by_cases hl : M.LexLt P th io Nt d Pr j α k u' u
          · exact Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, fun hl' => M.lex_asymm hd hl hl'⟩⟩)
          · exact Or.inl (Or.inr ⟨rfl, Or.inr ⟨rfl, hl⟩⟩)
        · exact Or.inl (Or.inr ⟨rfl, Or.inl ⟨h, fun e' => M.not_succ_le k (by rw [← e'] at e; exact e)⟩⟩)
      · rcases M.eq_or_succ_le h with e | e
        · subst e
          by_cases hl : M.LexLt P th io Nt d Pr j α k' u' u
          · exact Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, fun hl' => M.lex_asymm hd hl hl'⟩⟩)
          · exact Or.inl (Or.inr ⟨rfl, Or.inr ⟨rfl, hl⟩⟩)
        · exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨h, fun e' => M.not_succ_le k' (by rw [← e'] at e; exact e)⟩⟩)
    · obtain ⟨k, u, hn⟩ := M.rank_nameOf rn
      obtain ⟨k', u', hn'⟩ := M.rank_nameOf rn'
      obtain ⟨k'', u'', hn''⟩ := M.rank_nameOf rn''
      rw [M.pr_iff hd hPr hn hn' hα] at h1
      rw [M.pr_iff hd hPr hn' hn'' hα] at h2
      rw [M.pr_iff hd hPr hn hn'' hα]
      refine Or.inr ⟨rfl, ?_⟩
      rcases h1 with ⟨-, h1⟩ | ⟨-, h1⟩
      · exact (h1 rfl).elim
      rcases h2 with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact (h2 rfl).elim
      rcases h1 with ⟨l1, n1⟩ | ⟨e1, x1⟩
      · rcases h2 with ⟨l2, n2⟩ | ⟨e2, x2⟩
        · refine Or.inl ⟨le_trans l1 l2, fun e => n1 (le_antisymm l1 ?_)⟩
          rw [e]
          exact l2
        · subst e2
          exact Or.inl ⟨l1, n1⟩
      · subst e1
        rcases h2 with ⟨l2, n2⟩ | ⟨e2, x2⟩
        · exact Or.inl ⟨l2, n2⟩
        · subst e2
          refine Or.inr ⟨rfl, fun hl => ?_⟩
          rcases M.lex_negtrans hd (u' := u') (M.leV_total_of hd hPr hlow)
            (M.leV_trans_of hd hPr hlow) hl with h | h
          · exact x1 h
          · exact x2 h

theorem pr_total (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n n' ρ ρ' : V}
    (rn : M.RankIs P io M.nat j.1 ρ n) (rn' : M.RankIs P io M.nat j.1 ρ' n')
    (hρ : M.mem (M.op ρ ρ) th) (hρ' : M.mem (M.op ρ' ρ') th) :
    M.mem (M.op n n') Pr ∨ M.mem (M.op n' n) Pr :=
  M.pr_total_of hd hPr rn rn' hρ hρ' (fun _ => M.prOrd_all hd hPr hρ)

theorem pr_refl (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n ρ : V} (rn : M.RankIs P io M.nat j.1 ρ n)
    (hρ : M.mem (M.op ρ ρ) th) : M.mem (M.op n n) Pr := by
  rcases M.pr_total hd hPr rn rn hρ hρ with h | h <;> exact h

theorem pr_trans (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n n' n'' : V}
    (h1 : M.mem (M.op n n') Pr) (h2 : M.mem (M.op n' n'') Pr) : M.mem (M.op n n'') Pr := by
  obtain ⟨ρx, ρy, rx, ry, hxy⟩ := M.pr_names hPr h1
  obtain ⟨ρy', ρz, ry', rz, -⟩ := M.pr_names hPr h2
  exact M.pr_trans_of hd hPr rx ry' rz
    (fun _ _ => M.prOrd_all hd hPr (hd.hth.fld _ _ hxy).1) h1 h2

/-- The name of a value at a stage has a rank in the well-ordering. -/
theorem val_rank (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ρ x : V}
    (hρ : M.mem (M.op ρ ρ) th) (hx : M.InNRaw P th io M.nat j.1 ρ x ∨ x = d) :
    ∃ β, M.RankIs P io M.nat j.1 β x ∧ M.mem (M.op β β) th := by
  rcases hx with hx | hx
  · obtain ⟨β, rx, lt, -⟩ := M.inN_rank hx
    exact ⟨β, rx, (hd.hth.fld _ _ lt).1⟩
  · obtain ⟨α0, f0, u0, q0, k1, k2, ⟨k, hk⟩, hleast⟩ := hd.d_spec
    rw [hx]
    exact ⟨α0, ⟨f0, u0, q0, k1, k2, k, (hd.io_dom _ _ hk).1, hk⟩,
      (hd.hth.fld _ _ (hleast ρ hρ)).1⟩

theorem leV_iff (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {ρ x y : V} (hρ : M.mem (M.op ρ ρ) th)
    (hx : M.InNRaw P th io M.nat j.1 ρ x ∨ x = d) :
    M.LeV Pr x y ↔ M.mem (M.op x y) Pr := by
  constructor
  · rintro (h | h)
    · obtain ⟨β, rx, hβ⟩ := M.val_rank hd hρ hx
      rw [← h]
      exact M.pr_refl hd hPr rx hβ
    · exact h
  · exact fun h => Or.inr h

end prec3

/-! ## The order of the names is well-founded -/

/-- `LexLt` in raw form, with the order `Pr` as a set. -/
def LexLtR (P th io nat Nt j d ad z0 Pr β k u' u : V) : Prop :=
  ∃ i, M.mem i nat ∧ (∃ x, M.mem x nat ∧ M.mem (M.trip i x k) ad) ∧ ∃ e' e,
    M.ValRaw P th io nat Nt j d β u' i e' ∧ M.ValRaw P th io nat Nt j d β u i e ∧
    M.LeV Pr e' e ∧ ¬ M.LeV Pr e e' ∧
    ∀ i', M.mem i' nat → (∃ x, M.mem x nat ∧ ¬ x = z0 ∧ M.mem (M.trip i' x i) ad) →
      ∃ g' g, M.ValRaw P th io nat Nt j d β u' i' g' ∧ M.ValRaw P th io nat Nt j d β u i' g ∧
        M.LeV Pr g' g ∧ M.LeV Pr g g'

/-- `LexLtR`, with `β`, `k`, `u'`, `u` the names `250`, `223`, `224`, `225`. -/
def lexFml : Fml :=
  Fml.ex 226 (.and (.mem 226 27) (.and (fLeN 226 223) (Fml.ex 227 (Fml.ex 228 (.and (fVal 250
    224 226 227) (.and (fVal 250 225 226 228) (.and (fLeV 227 228) (.and (.neg (fLeV 228 227))
    (.all 229 (Fml.imp (.mem 229 27) (Fml.imp (fLtN 229 226) (Fml.ex 230 (Fml.ex 231 (.and (fVal
    250 224 229 230) (.and (fVal 250 225 229 231) (.and (fLeV 230 231) (fLeV 231
    230)))))))))))))))))

theorem sat_lexFml (ρ : ℕ → V) : Sat M.mem M.isSet lexFml ρ ↔
    M.LexLtR (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 10) (ρ 162) (ρ 250)
      (ρ 223) (ρ 224) (ρ 225) := by
  simp [lexFml, LexLtR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fLeN, M.sat_fLtN,
    M.sat_fLeV, Function.update_apply]

/-- Every set that contains a name of rank `ρ` has a least name of rank `ρ`. -/
def PrWFAt (P io nat j Pr ρ : V) : Prop :=
  ∀ S, (∃ n, M.mem n S ∧ M.RankIs P io nat j ρ n) →
    ∃ n0, M.mem n0 S ∧ M.RankIs P io nat j ρ n0 ∧
      ∀ n, M.mem n S → M.RankIs P io nat j ρ n → M.mem (M.op n0 n) Pr

/-- `PrWFAt`, with `ρ` the name `250`. -/
def prWFFml : Fml :=
  .all 251 (Fml.imp (Fml.ex 252 (.and (.mem 252 251) (fRank 250 252))) (Fml.ex 253 (.and (.mem
    253 251) (.and (fRank 250 253) (.all 252 (Fml.imp (.mem 252 251) (Fml.imp (fRank 250 252)
    (fApp 162 253 252))))))))

theorem sat_prWFFml (ρ : ℕ → V) : Sat M.mem M.isSet prWFFml ρ ↔
    M.PrWFAt (ρ 20) (ρ 24) (ρ 27) (ρ 25) (ρ 162) (ρ 250) := by
  simp [prWFFml, PrWFAt, Sat, M.sat_imp, M.sat_ex, M.sat_fRank, M.sat_fApp',
    Function.update_apply]

/-- Every nonempty set of sequences has a lexicographically minimal member; `k` is the name
`223`, the stage the name `250`. -/
def lexMinFml : Fml :=
  .all 251 (Fml.imp (Fml.ex 224 (.mem 224 251)) (Fml.ex 225 (.and (.mem 225 251) (.all 224
    (Fml.imp (.mem 224 251) (.neg lexFml))))))

theorem sat_lexMinFml (ρ : ℕ → V) : Sat M.mem M.isSet lexMinFml ρ ↔
    ∀ U, (∃ u, M.mem u U) → ∃ u0, M.mem u0 U ∧ ∀ u, M.mem u U →
      ¬ M.LexLtR (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 10) (ρ 162) (ρ 250)
        (ρ 223) u u0 := by
  simp [lexMinFml, Sat, M.sat_imp, M.sat_ex, M.sat_lexFml, Function.update_apply]

section prec4

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem lexLtR_iff {β u u' : V} (k : M.Num) :
    M.LexLtR P th io M.nat Nt j.1 d M.adG (0 : M.Num).1 Pr β k.1 u' u ↔
      M.LexLt P th io Nt d Pr j β k u' u := by
  constructor
  · rintro ⟨i, hi, hle, e', e, v1, v2, l1, l2, hall⟩
    exact ⟨⟨i, hi⟩, (M.leRaw_iff M.adG_spec ⟨i, hi⟩ k).mp hle, e', e, v1, v2, l1, l2,
      fun i' hi' => hall i'.1 i'.2 ((M.ltRaw_num i' ⟨i, hi⟩).mpr hi')⟩
  · rintro ⟨i, hle, e', e, v1, v2, l1, l2, hall⟩
    exact ⟨i.1, i.2, (M.leRaw_iff M.adG_spec i k).mpr hle, e', e, v1, v2, l1, l2,
      fun i' hi' hlt => hall ⟨i', hi'⟩ ((M.ltRaw_num ⟨i', hi'⟩ i).mp hlt)⟩

theorem leV_total (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {ρ : V} (x y : V)
    (hx : M.InNRaw P th io M.nat j.1 ρ x ∨ x = d) (hy : M.InNRaw P th io M.nat j.1 ρ y ∨ y = d) :
    M.LeV Pr x y ∨ M.LeV Pr y x :=
  M.leV_total_of hd hPr (fun β hβ _ => M.prOrd_all hd hPr (hd.hth.fld _ _ hβ).1) x y hx hy

theorem leV_trans (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {ρ : V} (x y z : V)
    (hx : M.InNRaw P th io M.nat j.1 ρ x ∨ x = d) (hy : M.InNRaw P th io M.nat j.1 ρ y ∨ y = d)
    (hz : M.InNRaw P th io M.nat j.1 ρ z ∨ z = d)
    (h1 : M.LeV Pr x y) (h2 : M.LeV Pr y z) : M.LeV Pr x z :=
  M.leV_trans_of hd hPr (fun β hβ _ => M.prOrd_all hd hPr (hd.hth.fld _ _ hβ).1) x y z hx hy hz
    h1 h2

/-- Among the values at a stage that belong to a set there is a least one. -/
theorem val_least (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {ρ : V}
    (hlow : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.PrWFAt P io M.nat j.1 Pr β) (S : V)
    (hS : ∃ x, M.mem x S ∧ (M.InNRaw P th io M.nat j.1 ρ x ∨ x = d)) :
    ∃ x0, M.mem x0 S ∧ (M.InNRaw P th io M.nat j.1 ρ x0 ∨ x0 = d) ∧
      ∀ x, M.mem x S → (M.InNRaw P th io M.nat j.1 ρ x ∨ x = d) → M.LeV Pr x0 x := by
  obtain ⟨x1, hx1S, hx1⟩ := hS
  by_cases hne : ∃ z, M.InNRaw P th io M.nat j.1 ρ z
  · have hx1' := M.val_inN_of_ne hd hx1 hne
    obtain ⟨B, -, hB0⟩ := M.comp (σW [(20, 7), (22, 5), (24, 5), (27, 3), (251, 3)])
      (Fml.ex 252 (.and (.mem 252 251) (.and (fInN 252) (fRank 250 252)))) 250 rfl
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 65 ρ) 251 S)
    have hB : ∀ β, M.mem β B ↔ ∃ x, M.mem x S ∧ M.InNRaw P th io M.nat j.1 ρ x ∧
        M.RankIs P io M.nat j.1 β x := by
      intro β
      rw [hB0 β]
      simp [Sat, M.sat_ex, M.sat_fInN, M.sat_fRank, Function.update_apply]
    obtain ⟨β1, r1, lt1, ne1⟩ := M.inN_rank hx1'
    obtain ⟨β0, hβ0B, hβ0, hmin⟩ := hd.hth.least B
      ⟨β1, (hB β1).mpr ⟨x1, hx1S, hx1', r1⟩, (hd.hth.fld _ _ lt1).1⟩
    obtain ⟨x2, hx2S, hx2, r2⟩ := (hB β0).mp hβ0B
    obtain ⟨β2, r2', lt2, ne2⟩ := M.inN_rank hx2
    have e2 := M.rank_unique hd r2 r2'
    rw [← e2] at lt2 ne2
    obtain ⟨n0, hn0S, rn0, hn0⟩ := hlow β0 lt2 ne2 S ⟨x2, hx2S, r2⟩
    refine ⟨n0, hn0S, Or.inl (M.rank_inN rn0 lt2 ne2), fun x hxS hx => ?_⟩
    have hx' := M.val_inN_of_ne hd hx hne
    obtain ⟨βx, rx, ltx, nex⟩ := M.inN_rank hx'
    have hle := hmin βx ((hB βx).mpr ⟨x, hxS, hx', rx⟩) (hd.hth.fld _ _ ltx).1
    by_cases e : β0 = βx
    · rw [← e] at rx
      exact Or.inr (hn0 x hxS rx)
    · exact Or.inr (M.pr_of_lt hPr rn0 rx hle e)
  · exact ⟨x1, hx1S, hx1, fun x _ hx =>
      Or.inl ((M.val_eq_d_of_empty hx1 hne).trans (M.val_eq_d_of_empty hx hne).symm)⟩

/-- In a nonempty set of sequences some member has the least value at the index `i`. -/
theorem exists_minAt (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {ρ : V}
    (hlow : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.PrWFAt P io M.nat j.1 Pr β) (U i : V)
    (hU : ∃ u, M.mem u U) :
    ∃ u0 e0, M.mem u0 U ∧ M.ValRaw P th io M.nat Nt j.1 d ρ u0 i e0 ∧
      ∀ u e, M.mem u U → M.ValRaw P th io M.nat Nt j.1 d ρ u i e → M.LeV Pr e0 e := by
  obtain ⟨W, -, hW0⟩ := M.comp (σW [(20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (251, 3)])
    (Fml.ex 224 (.and (.mem 224 251) (fVal 250 224 232 233))) 233 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 232 i) 250 ρ) 251 U)
  have hW : ∀ e, M.mem e W ↔ ∃ u, M.mem u U ∧ M.ValRaw P th io M.nat Nt j.1 d ρ u i e := by
    intro e
    rw [hW0 e]
    simp [Sat, M.sat_ex, M.sat_fVal, Function.update_apply]
  obtain ⟨u1, hu1⟩ := hU
  obtain ⟨e1, v1⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) ρ u1 i
  obtain ⟨e0, he0W, -, hmin⟩ := M.val_least hd hPr hlow W
    ⟨e1, (hW e1).mpr ⟨u1, hu1, v1⟩, M.val_cases v1⟩
  obtain ⟨u0, hu0, v0⟩ := (hW e0).mp he0W
  exact ⟨u0, e0, hu0, v0, fun u e hu hv => hmin e ((hW e).mpr ⟨u, hu, hv⟩) (M.val_cases hv)⟩

/-- **Lexicographic minimum.** Every nonempty set of sequences has a member below which,
lexicographically at the indices up to `k`, there is no member of the set. -/
theorem lex_min (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {ρ : V}
    (hlow : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.PrWFAt P io M.nat j.1 Pr β) (k : M.Num) (U : V)
    (hU : ∃ u, M.mem u U) :
    ∃ u0, M.mem u0 U ∧ ∀ u, M.mem u U → ¬ M.LexLt P th io Nt d Pr j ρ k u u0 := by
  have hsat : ∀ n : M.Num, Sat M.mem M.isSet lexMinFml (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 10 (0 : M.Num).1) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 162 Pr) 250 ρ) 223 n.1) ↔
      ∀ U, (∃ u, M.mem u U) → ∃ u0, M.mem u0 U ∧ ∀ u, M.mem u U →
        ¬ M.LexLt P th io Nt d Pr j ρ n u u0 := by
    intro n
    rw [M.sat_lexMinFml]
    simp [Function.update_apply, M.lexLtR_iff]
  have vtot := M.leV_total hd hPr (ρ := ρ)
  have vtrans := M.leV_trans hd hPr (ρ := ρ)
  have key := M.num_ind_fml
    (σW [(20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7), (162, 5), (251, 3)]) lexMinFml 223
    rfl (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 10 (0 : M.Num).1) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 162 Pr) 250 ρ) ?_ ?_ k
  · exact (hsat k).mp key U hU
  · rw [show M.zero = (0 : M.Num).1 from rfl, hsat 0]
    intro U hU
    obtain ⟨u0, e0, hu0, v0, hmin⟩ := M.exists_minAt hd hPr hlow U (0 : M.Num).1 hU
    refine ⟨u0, hu0, fun u hu hl => ?_⟩
    obtain ⟨i, hi, e', e, w1, w2, l1, l2, -⟩ := hl
    have i0 : i = 0 := le_antisymm hi zero_le
    subst i0
    rw [M.val_unique hd w2 v0] at l2
    exact l2 (hmin u e' hu w1)
  · intro k ih
    rw [show M.succ k.1 = (k + 1).1 from (M.val_add_one k).symm, hsat (k + 1)]
    rw [hsat k] at ih
    intro U hU
    obtain ⟨u1, hu1, hmin1⟩ := ih U hU
    obtain ⟨U', -, hU'0⟩ := M.comp
      (σW [(20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7), (162, 5), (251, 3)])
      (.and (.mem 225 251) (.neg lexFml)) 225 rfl
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 10 (0 : M.Num).1) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 162 Pr) 223 k.1) 224 u1) 250 ρ) 251 U)
    have hU' : ∀ u, M.mem u U' ↔ M.mem u U ∧ ¬ M.LexLt P th io Nt d Pr j ρ k u1 u := by
      intro u
      rw [hU'0 u]
      simp [Sat, M.sat_lexFml, Function.update_apply, M.lexLtR_iff]
    have hu1' : M.mem u1 U' := (hU' u1).mpr ⟨hu1, fun h => M.lex_asymm hd h h⟩
    obtain ⟨u0, e0, hu0', v0, hmin0⟩ := M.exists_minAt hd hPr hlow U' (k + 1).1 ⟨u1, hu1'⟩
    obtain ⟨hu0, hu0t⟩ := (hU' u0).mp hu0'
    refine ⟨u0, hu0, fun u hu hl => ?_⟩
    obtain ⟨i, hi, e', e, w1, w2, l1, l2, hall⟩ := hl
    rcases M.eq_or_succ_le hi with ei | hlt
    · subst ei
      have hmem : M.mem u U' := by
        refine (hU' u).mpr ⟨hu, fun h1 => ?_⟩
        rcases M.lex_negtrans hd (u' := u0) vtot vtrans h1 with h2 | h2
        · obtain ⟨i2, hi2, a', a, x1, x2, m1, m2, -⟩ := h2
          obtain ⟨g', g, y1, y2, t1, t2⟩ := hall i2 (add_le_add hi2 (le_refl 1))
          rw [M.val_unique hd y1 x2, M.val_unique hd y2 x1] at t1
          exact m2 t1
        · exact hu0t h2
      rw [M.val_unique hd w2 v0] at l2
      exact l2 (hmin0 u e' hmem w1)
    · have hik := M.le_of_succ_le_succ hlt
      have h1 : M.LexLt P th io Nt d Pr j ρ k u u0 := ⟨i, hik, e', e, w1, w2, l1, l2, hall⟩
      rcases M.lex_negtrans hd (u' := u1) vtot vtrans h1 with h2 | h2
      · exact hu0t h2
      · exact hmin1 u hu h2

/-- **The order of the names is well-founded** on the names of each rank. -/
theorem prWF_all (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {ρ : V} (hρ : M.mem (M.op ρ ρ) th) :
    M.PrWFAt P io M.nat j.1 Pr ρ := by
  have key := M.wo_ind_fml hd.hth (σW [(20, 7), (24, 5), (27, 3), (162, 5), (251, 3)]) prWFFml 250
    rfl (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 24 io) 25 j.1) 27 M.nat) 162 Pr) (fun α hα ih => ?_) ρ hρ
  · rw [M.sat_prWFFml] at key
    simpa [Function.update_apply] using key
  · have hlow : ∀ β, M.mem (M.op β α) th → β ≠ α → M.PrWFAt P io M.nat j.1 Pr β := by
      intro β hβ hne
      have h1 := ih β hβ hne
      rw [M.sat_prWFFml] at h1
      simpa [Function.update_apply] using h1
    rw [M.sat_prWFFml]
    have goal : M.PrWFAt P io M.nat j.1 Pr α := by
      rintro S ⟨n1, hn1S, rn1⟩
      obtain ⟨k1, u1, hn1⟩ := M.rank_nameOf rn1
      obtain ⟨K, -, hK0⟩ := M.comp (σW [(20, 7), (24, 5), (27, 3), (251, 3)])
        (.and (.mem 254 27) (Fml.ex 252 (Fml.ex 255 (.and (.mem 252 251) (Fml.ex 256 (Fml.ex 257 (.and (fApp4 20 25 250 257 252) (.and (fApp4 20 25 256 255 257) (fApp 24 254 256))))))))) 254 rfl
        (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 24 io) 25 j.1) 27 M.nat) 250 α) 251 S)
      have hK : ∀ k : M.Num, M.mem k.1 K ↔ ∃ n u, M.mem n S ∧ M.NameOf P io j n α k u := by
        intro k
        rw [hK0 k.1]
        simp [Sat, M.sat_ex, M.sat_fApp4', M.sat_fApp', Function.update_apply, NameOf, k.2]
      obtain ⟨k0, hk0K, hk0min⟩ := M.nat_least ⟨k1, (hK k1).mpr ⟨n1, u1, hn1S, hn1⟩⟩
      obtain ⟨n2, u2, hn2S, hn2⟩ := (hK k0).mp hk0K
      obtain ⟨U, -, hU0⟩ := M.comp (σW [(20, 7), (24, 5), (27, 3), (251, 3)])
        (Fml.ex 252 (.and (.mem 252 251) (Fml.ex 256 (Fml.ex 257 (.and (fApp4 20 25 250 257 252) (.and (fApp4 20 25 256 255 257) (fApp 24 254 256))))))) 255 rfl
        (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 24 io) 25 j.1) 27 M.nat) 250 α) 251 S) 254 k0.1)
      have hU : ∀ u, M.mem u U ↔ ∃ n, M.mem n S ∧ M.NameOf P io j n α k0 u := by
        intro u
        rw [hU0 u]
        simp [Sat, M.sat_ex, M.sat_fApp4', M.sat_fApp', Function.update_apply, NameOf]
      obtain ⟨u0, hu0U, hmin⟩ := M.lex_min hd hPr hlow k0 U ⟨u2, (hU u2).mpr ⟨n2, hn2S, hn2⟩⟩
      obtain ⟨n0, hn0S, hn0⟩ := (hU u0).mp hu0U
      refine ⟨n0, hn0S, M.nameOf_rank hn0, fun n hnS rn => ?_⟩
      obtain ⟨k, u, hn⟩ := M.rank_nameOf rn
      rw [M.pr_iff hd hPr hn0 hn hα]
      refine Or.inr ⟨rfl, ?_⟩
      have hk := hk0min k ((hK k).mpr ⟨n, u, hnS, hn⟩)
      rcases M.eq_or_succ_le hk with e | e
      · subst e
        exact Or.inr ⟨rfl, hmin u ((hU u).mpr ⟨n, hnS, hn⟩)⟩
      · exact Or.inl ⟨hk, fun e' => M.not_succ_le k0 (by rw [← e'] at e; exact e)⟩
    simpa [Function.update_apply] using goal

/-- **Every set that contains a name has a least name**, in the order of the names. -/
theorem pr_least (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) (S : V)
    (hS : ∃ n ρ, M.mem n S ∧ M.RankIs P io M.nat j.1 ρ n ∧ M.mem (M.op ρ ρ) th) :
    ∃ n0 ρ0, M.mem n0 S ∧ M.RankIs P io M.nat j.1 ρ0 n0 ∧ M.mem (M.op ρ0 ρ0) th ∧
      ∀ n ρ, M.mem n S → M.RankIs P io M.nat j.1 ρ n → M.mem (M.op ρ ρ) th →
        M.mem (M.op n0 n) Pr := by
  obtain ⟨n1, ρ1, hn1S, rn1, hρ1⟩ := hS
  obtain ⟨B, -, hB0⟩ := M.comp (σW [(20, 7), (24, 5), (27, 3), (251, 3)])
    (Fml.ex 252 (.and (.mem 252 251) (fRank 250 252))) 250 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 24 io) 25 j.1) 27 M.nat) 251 S)
  have hB : ∀ β, M.mem β B ↔ ∃ x, M.mem x S ∧ M.RankIs P io M.nat j.1 β x := by
    intro β
    rw [hB0 β]
    simp [Sat, M.sat_ex, M.sat_fRank, Function.update_apply]
  obtain ⟨ρ0, hρ0B, hρ0, hmin⟩ := hd.hth.least B ⟨ρ1, (hB ρ1).mpr ⟨n1, hn1S, rn1⟩, hρ1⟩
  obtain ⟨n0, hn0S, rn0, hn0⟩ := M.prWF_all hd hPr hρ0 S ((hB ρ0).mp hρ0B)
  refine ⟨n0, ρ0, hn0S, rn0, hρ0, fun n ρ hnS rn hρ => ?_⟩
  have hle := hmin ρ ((hB ρ).mpr ⟨n, hnS, rn⟩) hρ
  by_cases e : ρ0 = ρ
  · rw [← e] at rn
    exact hn0 n hnS rn
  · exact M.pr_of_lt hPr rn0 rn hle e

end prec4

/-! ## Ties and canonical names -/

/-- For names of rank `ρ`: two names that are each at most the other denote the same set. -/
def tieSimFml : Fml :=
  .all 252 (.all 253 (Fml.imp (fRank 250 252) (Fml.imp (fApp 162 252 253) (Fml.imp (fApp 162 253
    252) (fSim 252 253)))))

theorem sat_tieSimFml (ρ : ℕ → V) : Sat M.mem M.isSet tieSimFml ρ ↔
    ∀ n n', M.RankIs (ρ 20) (ρ 24) (ρ 27) (ρ 25) (ρ 250) n → M.mem (M.op n n') (ρ 162) →
      M.mem (M.op n' n) (ρ 162) → M.SimRaw (ρ 20) (ρ 25) (ρ 21) (ρ 6) n n' := by
  simp [tieSimFml, Sat, M.sat_imp, M.sat_fRank, M.sat_fApp', M.sat_fSim, Function.update_apply]

/-- A **canonical name**: a name that is least, in the order of the names, among the names
that denote the same set. -/
def IsCan (P j tp F Pr n : V) : Prop :=
  M.SimRaw P j tp F n n ∧ ∀ n', M.SimRaw P j tp F n n' → M.mem (M.op n n') Pr

section prec5

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem val_cons_succ (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ρ x u s e : V}
    (hs : M.mem (M.quad j.1 x u s) P) (n : M.Num) :
    M.ValRaw P th io M.nat Nt j.1 d ρ s (n + 1).1 e ↔ M.ValRaw P th io M.nat Nt j.1 d ρ u n.1 e := by
  unfold ValRaw
  simp only [M.nth_cons_succ hd hs n]

theorem val_cons_zero (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ρ x u s : V}
    (hs : M.mem (M.quad j.1 x u s) P) (hx : M.InNRaw P th io M.nat j.1 ρ x) :
    M.ValRaw P th io M.nat Nt j.1 d ρ s (0 : M.Num).1 x :=
  Or.inl ⟨(hd.nt_zero s x).mpr ⟨u, hs⟩, hx⟩

/-- A value at a stage denotes the same set as itself. -/
theorem val_sim_refl (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ρ t i e : V}
    (hρ : M.mem (M.op ρ ρ) th) (hv : M.ValRaw P th io M.nat Nt j.1 d ρ t i e) :
    M.SimRaw P j.1 tp F e e := by
  obtain ⟨β, re, hβ⟩ := M.val_rank hd hρ (M.val_cases hv)
  exact M.sim_refl hd re hβ

/-- Members pass from a name to a name of the same rank and formula whose parameters denote
the same sets. -/
theorem eps_transfer (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    {ρ f u u' q q' n n' : V} {k : M.Num} (hf : M.mem (M.op k.1 f) io)
    (h1 : M.mem (M.quad j.1 ρ q n) P) (h2 : M.mem (M.quad j.1 f u q) P)
    (h1' : M.mem (M.quad j.1 ρ q' n') P) (h2' : M.mem (M.quad j.1 f u' q') P)
    (hv : ∀ i : M.Num, i + 1 ≤ k → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ u i.1 e ∧
      M.ValRaw P th io M.nat Nt j.1 d ρ u' i.1 e' ∧ M.SimRaw P j.1 tp F e e') (x : V)
    (hx : M.EpsRaw P th io M.nat j.1 F x n) : M.EpsRaw P th io M.nat j.1 F x n' := by
  rw [M.eps_iff hd h1 h2 hf x] at hx
  rw [M.eps_iff hd h1' h2' hf x]
  obtain ⟨hxN, s, hs, htr⟩ := hx
  have hxR := M.inN_rung hd hxN
  obtain ⟨s', hs'⟩ := hd.hP.tot j hd.hj x u' hxR (hd.hP.dom _ _ _ _ h2').2.2.1
  refine ⟨hxN, s', hs', (M.inv_hier hd k s s' (fun i hi => ?_)).mp htr⟩
  rcases M.num_cases i with h0 | ⟨i', hi'⟩
  · rw [h0]
    exact ⟨x, x, M.val_cons_zero hd hs hxN, M.val_cons_zero hd hs' hxN, M.inN_refl hd hxN⟩
  · rw [hi', M.nsucc_eq_add_one]
    obtain ⟨e, e', v, v', hsim⟩ := hv i' (by rw [← M.nsucc_eq_add_one, ← hi']; exact hi)
    exact ⟨e, e', (M.val_cons_succ hd hs i').mpr v, (M.val_cons_succ hd hs' i').mpr v', hsim⟩

/-- Two names of the same rank and formula whose parameters denote the same sets denote the
same set. -/
theorem name_sim_of_vals (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {n n' ρ u u' : V}
    {k : M.Num} (hn : M.NameOf P io j n ρ k u) (hn' : M.NameOf P io j n' ρ k u')
    (hρ : M.mem (M.op ρ ρ) th)
    (hv : ∀ i : M.Num, i + 1 ≤ k → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ u i.1 e ∧
      M.ValRaw P th io M.nat Nt j.1 d ρ u' i.1 e' ∧ M.SimRaw P j.1 tp F e e') :
    M.SimRaw P j.1 tp F n n' := by
  have rn := M.nameOf_rank hn
  have rn' := M.nameOf_rank hn'
  obtain ⟨f, q, h1, h2, h3⟩ := hn
  obtain ⟨f', q', h1', h2', h3'⟩ := hn'
  have ef := hd.io_fun _ _ _ h3 h3'
  rw [← ef] at h2'
  have hv' : ∀ i : M.Num, i + 1 ≤ k → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ u' i.1 e ∧
      M.ValRaw P th io M.nat Nt j.1 d ρ u i.1 e' ∧ M.SimRaw P j.1 tp F e e' := by
    intro i hi
    obtain ⟨e, e', v, v', hs⟩ := hv i hi
    exact ⟨e', e, v', v, M.sim_symm hd hs⟩
  refine (M.hier_sim hd rn rn' hρ hρ).mpr ⟨fun x hx => ?_, fun x' hx' => ?_⟩
  · exact ⟨x, M.eps_transfer hd h3 h1 h2 h1' h2' hv x hx,
      M.inN_refl hd (M.eps_inN_rank hd rn hx)⟩
  · exact ⟨x', M.eps_transfer hd h3 h1' h2' h1 h2 hv' x' hx',
      M.inN_refl hd (M.eps_inN_rank hd rn' hx')⟩

/-- The least index at which two sequences do not have equivalent values. -/
theorem notTie_least (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ρ u u' : V}
    (i1 : M.Num)
    (h : ¬ ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d ρ u' i1.1 g' ∧
      M.ValRaw P th io M.nat Nt j.1 d ρ u i1.1 g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g') :
    ∃ i0 : M.Num, i0 ≤ i1 ∧
      (¬ ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d ρ u' i0.1 g' ∧
        M.ValRaw P th io M.nat Nt j.1 d ρ u i0.1 g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g') ∧
      ∀ i' : M.Num, i' + 1 ≤ i0 → ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d ρ u' i'.1 g' ∧
        M.ValRaw P th io M.nat Nt j.1 d ρ u i'.1 g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g' := by
  obtain ⟨S, -, hS0⟩ := M.comp (σW [(20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (162, 5)])
    (.and (.mem 229 27) (.neg (Fml.ex 230 (Fml.ex 231 (.and (fVal 250 224 229 230) (.and (fVal 250 225 229 231) (.and (fLeV 230 231) (fLeV 231 230)))))))) 229 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 162 Pr) 224 u') 225 u) 250 ρ)
  have hS : ∀ x : M.Num, M.mem x.1 S ↔ ¬ ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d ρ u' x.1 g' ∧
      M.ValRaw P th io M.nat Nt j.1 d ρ u x.1 g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g' := by
    intro x
    rw [hS0 x.1]
    simp [Sat, M.sat_ex, M.sat_fVal, M.sat_fLeV, Function.update_apply, x.2]
  obtain ⟨i0, hi0S, hmin⟩ := M.nat_least ⟨i1, (hS i1).mpr h⟩
  refine ⟨i0, hmin i1 ((hS i1).mpr h), (hS i0).mp hi0S, fun i' hi' => ?_⟩
  by_contra h1
  exact M.not_succ_le i' (le_trans hi' (hmin i' ((hS i').mpr h1)))

/-- Two sequences neither of which is lexicographically below the other have equivalent
values at all indices up to the bound. -/
theorem lex_tie (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {ρ u u' : V} {k : M.Num}
    (h1 : ¬ M.LexLt P th io Nt d Pr j ρ k u' u) (h2 : ¬ M.LexLt P th io Nt d Pr j ρ k u u')
    (i : M.Num) (hi : i ≤ k) :
    ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d ρ u' i.1 g' ∧
      M.ValRaw P th io M.nat Nt j.1 d ρ u i.1 g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g' := by
  by_contra hne
  obtain ⟨i0, hi0, hnt, hties⟩ := M.notTie_least hd i hne
  obtain ⟨e', v'⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) ρ u' i0.1
  obtain ⟨e, v⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) ρ u i0.1
  rcases M.leV_total hd hPr e' e (M.val_cases v') (M.val_cases v) with l | l
  · exact h1 ⟨i0, le_trans hi0 hi, e', e, v', v, l, fun l' => hnt ⟨e', e, v', v, l, l'⟩, hties⟩
  · exact h2 ⟨i0, le_trans hi0 hi, e, e', v, v', l, fun l' => hnt ⟨e', e, v', v, l', l⟩,
      fun i' hi' => by
        obtain ⟨g', g, a, b, c, dd⟩ := hties i' hi'
        exact ⟨g, g', b, a, dd, c⟩⟩

theorem tie_rank (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n n' ρ ρ' : V}
    (rn : M.RankIs P io M.nat j.1 ρ n) (rn' : M.RankIs P io M.nat j.1 ρ' n')
    (h1 : M.mem (M.op n n') Pr) (h2 : M.mem (M.op n' n) Pr) : ρ = ρ' :=
  hd.hth.antisymm _ _ (M.pr_rank_le hd hPr rn rn' h1) (M.pr_rank_le hd hPr rn' rn h2)

/-- Two names each at most the other have the same formula, and equivalent values of the
parameters. -/
theorem tie_shape (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n n' ρ u u' : V} {k k' : M.Num}
    (hn : M.NameOf P io j n ρ k u) (hn' : M.NameOf P io j n' ρ k' u')
    (hρ : M.mem (M.op ρ ρ) th)
    (h1 : M.mem (M.op n n') Pr) (h2 : M.mem (M.op n' n) Pr) :
    k = k' ∧ ∀ i : M.Num, i ≤ k → ∃ g' g, M.ValRaw P th io M.nat Nt j.1 d ρ u' i.1 g' ∧
      M.ValRaw P th io M.nat Nt j.1 d ρ u i.1 g ∧ M.LeV Pr g' g ∧ M.LeV Pr g g' := by
  rw [M.pr_iff hd hPr hn hn' hρ] at h1
  rw [M.pr_iff hd hPr hn' hn hρ] at h2
  rcases h1 with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact (h1 rfl).elim
  rcases h2 with ⟨-, h2⟩ | ⟨-, h2⟩
  · exact (h2 rfl).elim
  rcases h1 with ⟨l1, n1⟩ | ⟨e1, x1⟩
  · rcases h2 with ⟨l2, n2⟩ | ⟨e2, x2⟩
    · exact (n1 (le_antisymm l1 l2)).elim
    · exact (n1 e2.symm).elim
  · subst e1
    rcases h2 with ⟨l2, n2⟩ | ⟨e2, x2⟩
    · exact (n2 rfl).elim
    · exact ⟨rfl, fun i hi => M.lex_tie hd hPr x1 x2 i hi⟩

/-- **Names each at most the other denote the same set.** -/
theorem tie_sim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n n' : V}
    (h1 : M.mem (M.op n n') Pr) (h2 : M.mem (M.op n' n) Pr) : M.SimRaw P j.1 tp F n n' := by
  obtain ⟨ρ, ρ', rn, rn', hle⟩ := M.pr_names hPr h1
  have hρ := (hd.hth.fld _ _ hle).1
  have key := M.wo_ind_fml hd.hth (σW [(6, 5), (20, 7), (24, 5), (27, 3), (162, 5)]) tieSimFml 250
    rfl (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 24 io) 25 j.1) 27 M.nat) 162 Pr) (fun α hα ih => ?_) ρ hρ
  · rw [M.sat_tieSimFml] at key
    simp only [Function.update_apply] at key
    norm_num at key
    exact key n n' rn h1 h2
  · have hlow : ∀ β, M.mem (M.op β α) th → β ≠ α → ∀ a a', M.RankIs P io M.nat j.1 β a →
        M.mem (M.op a a') Pr → M.mem (M.op a' a) Pr → M.SimRaw P j.1 tp F a a' := by
      intro β hβ hne
      have h1 := ih β hβ hne
      rw [M.sat_tieSimFml] at h1
      simp only [Function.update_apply] at h1
      norm_num at h1
      exact h1
    rw [M.sat_tieSimFml]
    simp only [Function.update_apply]
    norm_num
    intro a a' ra t1 t2
    obtain ⟨ρa, ρa', ra1, ra', -⟩ := M.pr_names hPr t1
    have e2 := M.tie_rank hd hPr ra ra' t1 t2
    rw [← e2] at ra'
    obtain ⟨k, u, hn⟩ := M.rank_nameOf ra
    obtain ⟨k', u', hn'⟩ := M.rank_nameOf ra'
    obtain ⟨ek, hties⟩ := M.tie_shape hd hPr hn hn' hα t1 t2
    subst ek
    refine M.name_sim_of_vals hd hn hn' hα (fun i hi => ?_)
    obtain ⟨g', g, v', v, l1, l2⟩ := hties i (le_trans (M.le_add_one i) hi)
    refine ⟨g, g', v, v', ?_⟩
    by_cases e : g = g'
    · rw [← e]
      exact M.val_sim_refl hd hα v
    · have p1 : M.mem (M.op g g') Pr := by
        rcases l2 with l | l
        · exact (e l).elim
        · exact l
      have p2 : M.mem (M.op g' g) Pr := by
        rcases l1 with l | l
        · exact (e l.symm).elim
        · exact l
      have hne : ∃ z, M.InNRaw P th io M.nat j.1 α z := by
        rcases M.val_cases v with h | h
        · exact ⟨g, h⟩
        · rcases M.val_cases v' with h' | h'
          · exact ⟨g', h'⟩
          · exact (e (h.trans h'.symm)).elim
      obtain ⟨β, rg, lt, ne⟩ := M.inN_rank (M.val_inN_of_ne hd (M.val_cases v) hne)
      exact hlow β lt ne g g' rg p1 p2

theorem can_refl {n : V} (h : M.IsCan P j.1 tp F Pr n) : M.SimRaw P j.1 tp F n n := h.1

/-- Every name has a canonical name that denotes the same set. -/
theorem exists_can (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n : V} (h : M.SimRaw P j.1 tp F n n) :
    ∃ n0, M.IsCan P j.1 tp F Pr n0 ∧ M.SimRaw P j.1 tp F n n0 := by
  obtain ⟨C, -, hC0⟩ := M.comp (σW [(6, 5), (20, 7)]) (fSim 252 253) 253 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 25 j.1) 252 n)
  have hC : ∀ x, M.mem x C ↔ M.SimRaw P j.1 tp F n x := by
    intro x
    rw [hC0 x]
    simp [M.sat_fSim, Function.update_apply]
  obtain ⟨ρ, -, rn, -, hρ, -⟩ := M.sim_names hd h
  obtain ⟨n0, ρ0, hn0C, rn0, hρ0, hmin⟩ := M.pr_least hd hPr C ⟨n, ρ, (hC n).mpr h, rn, hρ⟩
  have hs0 := (hC n0).mp hn0C
  refine ⟨n0, ⟨M.sim_trans hd (M.sim_symm hd hs0) hs0, fun n' hn' => ?_⟩, hs0⟩
  have hs' := M.sim_trans hd hs0 hn'
  obtain ⟨-, ρ', -, rn', -, hρ'⟩ := M.sim_names hd hs'
  exact hmin n' ρ' ((hC n').mpr hs') rn' hρ'

/-- A name equivalent to a canonical name in the order of the names is canonical. -/
theorem can_of_tie (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n0 n1 : V} (hc : M.IsCan P j.1 tp F Pr n0)
    (h1 : M.mem (M.op n0 n1) Pr) (h2 : M.mem (M.op n1 n0) Pr) : M.IsCan P j.1 tp F Pr n1 := by
  have hs := M.tie_sim hd hPr h1 h2
  exact ⟨M.sim_trans hd (M.sim_symm hd hs) hs,
    fun n' hn' => M.pr_trans hd hPr h2 (hc.2 n' (M.sim_trans hd hs hn'))⟩

/-- **The parameters of a canonical name are canonical**, at a stage that is not the least. -/
theorem can_vals (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {n0 ρ u e : V} {k i : M.Num}
    (hc : M.IsCan P j.1 tp F Pr n0) (hn : M.NameOf P io j n0 ρ k u)
    (hρ : M.mem (M.op ρ ρ) th) (hne : ∃ z, M.InNRaw P th io M.nat j.1 ρ z) (hi : i ≤ k)
    (hv : M.ValRaw P th io M.nat Nt j.1 d ρ u i.1 e) : M.IsCan P j.1 tp F Pr e := by
  have heN := M.val_inN_of_ne hd (M.val_cases hv) hne
  obtain ⟨βe, re, lte, nee⟩ := M.inN_rank heN
  have hβe := (hd.hth.fld _ _ lte).1
  have hee := M.sim_refl hd re hβe
  obtain ⟨e0, hc0, hs0⟩ := M.exists_can hd hPr hee
  obtain ⟨-, β0, -, re0, -, hβ0⟩ := M.sim_names hd hs0
  have p0 : M.mem (M.op e0 e) Pr := hc0.2 e (M.sim_symm hd hs0)
  by_cases p1 : M.mem (M.op e e0) Pr
  · exact M.can_of_tie hd hPr hc0 p0 p1
  exfalso
  -- replace the value at `i` by the canonical name
  have hle0 := M.pr_rank_le hd hPr re0 re p0
  have lt0 := hd.hth.trans _ _ _ hle0 lte
  have ne0 : β0 ≠ ρ := by
    intro e1
    rw [e1] at hle0
    exact nee (hd.hth.antisymm _ _ lte hle0)
  have he0N := M.rank_inN re0 lt0 ne0
  obtain ⟨u', hu'R, hag⟩ := M.exists_updR hd he0N u i.1 k
  obtain ⟨n', hn'⟩ := M.nameOf_exists hd hρ hu'R k
  have hik : i ≤ k := hi
  have hsim : M.SimRaw P j.1 tp F n0 n' := by
    refine M.name_sim_of_vals hd hn hn' hρ (fun i' hi' => ?_)
    have hi'k : i' ≤ k := le_trans (M.le_add_one i') hi'
    by_cases ei : i' = i
    · rw [ei]
      exact ⟨e, e0, hv, M.agree_same hag hik, hs0⟩
    · obtain ⟨g, vg⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j)
        ρ u i'.1
      exact ⟨g, g, vg, M.agree_other hag hi'k ei vg, M.val_sim_refl hd hρ vg⟩
  have hpr := hc.2 n' hsim
  rw [M.pr_iff hd hPr hn hn' hρ] at hpr
  rcases hpr with ⟨-, h⟩ | ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩
  · exact h rfl
  · exact h rfl
  · refine h ⟨i, hik, e0, e, M.agree_same hag hik, hv, Or.inr p0, ?_, fun i' hi' => ?_⟩
    · rintro (l | l)
      · rw [l] at p1
        exact p1 (M.pr_refl hd hPr re0 hβ0)
      · exact p1 l
    · obtain ⟨g, vg⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j)
        ρ u i'.1
      have ne : i' ≠ i := fun e1 => M.not_succ_le i (by rw [e1] at hi'; exact hi')
      exact ⟨g, g, M.agree_other hag (le_trans (le_trans (M.le_add_one i') hi') hik) ne vg, vg,
        Or.inl rfl, Or.inl rfl⟩

end prec5

/-! ## The canonical well-ordering of the denoted sets -/

/-- `IsCan` for the name `x`; bound name `258`. -/
def fCan (x : ℕ) : Fml := .and (fSim x x) (.all 258 (Fml.imp (fSim x 258) (fApp 162 x 258)))

theorem sat_fCan {x : ℕ} (ρ : ℕ → V) (hx : 199 < x) (hx' : x ≠ 258) :
    Sat M.mem M.isSet (fCan x) ρ ↔ M.IsCan (ρ 20) (ρ 25) (ρ 21) (ρ 6) (ρ 162) (ρ x) := by
  have b : x < 30 ∨ 59 < x := by omega
  simp [fCan, IsCan, Sat, M.sat_imp, M.sat_fSim, M.sat_fApp', Function.update_apply, hx, hx', b]

/-- The set denoted by `a` is before the set denoted by `b` in the **canonical well-ordering**:
the canonical names are strictly ordered. -/
def Lt (P j tp F Pr a b : V) : Prop :=
  ∃ a0 b0, M.IsCan P j tp F Pr a0 ∧ M.IsCan P j tp F Pr b0 ∧ M.SimRaw P j tp F a a0 ∧
    M.SimRaw P j tp F b b0 ∧ M.mem (M.op a0 b0) Pr ∧ ¬ M.mem (M.op b0 a0) Pr

section prec6

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- A canonical name of a set that has a name of rank below `α` has rank below `α`. -/
theorem can_inN (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {α a a0 : V} (ha : M.InNRaw P th io M.nat j.1 α a)
    (hc : M.IsCan P j.1 tp F Pr a0) (hs : M.SimRaw P j.1 tp F a a0) :
    M.InNRaw P th io M.nat j.1 α a0 := by
  obtain ⟨β, ra, lt, ne⟩ := M.inN_rank ha
  obtain ⟨-, β0, -, r0, -, hβ0⟩ := M.sim_names hd hs
  have hle := M.pr_rank_le hd hPr r0 ra (hc.2 a (M.sim_symm hd hs))
  refine M.rank_inN r0 (hd.hth.trans _ _ _ hle lt) (fun e => ?_)
  rw [e] at hle
  exact ne (hd.hth.antisymm _ _ lt hle)

theorem can_tie (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a0 b0 : V}
    (ca : M.IsCan P j.1 tp F Pr a0) (cb : M.IsCan P j.1 tp F Pr b0)
    (hs : M.SimRaw P j.1 tp F a0 b0) : M.mem (M.op a0 b0) Pr ∧ M.mem (M.op b0 a0) Pr :=
  ⟨ca.2 b0 hs, cb.2 a0 (M.sim_symm hd hs)⟩

theorem ltRaw_iff (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {α a b : V} :
    M.LtRaw P th io M.nat j.1 tp Pr F α a b ↔ M.InNRaw P th io M.nat j.1 α a ∧
      M.InNRaw P th io M.nat j.1 α b ∧ M.Lt P j.1 tp F Pr a b := by
  constructor
  · rintro ⟨ha, hb, a0, b0, ha0, hb0, sa, sb, la, lb, pp, np⟩
    have can : ∀ {x0 : V}, M.InNRaw P th io M.nat j.1 α x0 →
        (∀ x', M.InNRaw P th io M.nat j.1 α x' → M.SimRaw P j.1 tp F x' x0 →
          M.mem (M.op x0 x') Pr) → M.IsCan P j.1 tp F Pr x0 := by
      intro x0 hx0 hl
      refine ⟨M.inN_refl hd hx0, fun n' hn' => ?_⟩
      obtain ⟨β0, r0, lt0, ne0⟩ := M.inN_rank hx0
      obtain ⟨-, β', -, r', -, hβ'⟩ := M.sim_names hd hn'
      by_cases hN : M.InNRaw P th io M.nat j.1 α n'
      · exact hl n' hN (M.sim_symm hd hn')
      · have hα := (hd.hth.fld _ _ lt0).2
        rcases M.wo_total hd.hth hα hβ' with h | h
        · refine M.pr_of_lt hPr r0 r' (hd.hth.trans _ _ _ lt0 h) (fun e => ?_)
          rw [← e] at h
          exact ne0 (hd.hth.antisymm _ _ lt0 h)
        · by_cases e : β' = α
          · rw [e] at r'
            exact M.pr_of_lt hPr r0 r' lt0 ne0
          · exact (hN (M.rank_inN r' h e)).elim
    exact ⟨ha, hb, a0, b0, can ha0 la, can hb0 lb, sa, sb, pp, np⟩
  · rintro ⟨ha, hb, a0, b0, ca, cb, sa, sb, pp, np⟩
    exact ⟨ha, hb, a0, b0, M.can_inN hd hPr ha ca sa, M.can_inN hd hPr hb cb sb, sa, sb,
      fun a' _ h => ca.2 a' (M.sim_symm hd h), fun b' _ h => cb.2 b' (M.sim_symm hd h), pp, np⟩

/-- **The clause for the canonical well-ordering**: the atomic formula with the relation
symbol `2` is true if and only if the value of the first variable is before the value of the
second. -/
theorem hier_lt (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {α : V} (v w : M.Num) (t : V) :
    M.TrueAt P io F j.1 α (M.cRel 2 v w) t ↔ M.mem (M.op α α) th ∧
      ∃ a b, M.ValRaw P th io M.nat Nt j.1 d α t v.1 a ∧ M.ValRaw P th io M.nat Nt j.1 d α t w.1 b ∧
        M.InNRaw P th io M.nat j.1 α a ∧ M.InNRaw P th io M.nat j.1 α b ∧
        M.Lt P j.1 tp F Pr a b := by
  rw [M.hier_rel hd]
  constructor
  · rintro ⟨hα, a, b, va, vb, h⟩
    rcases h with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exact (h rfl).elim
    · exact (M.n21 (Subtype.ext h)).elim
    · exact ⟨hα, a, b, va, vb, (M.ltRaw_iff hd hPr).mp h⟩
  · rintro ⟨hα, a, b, va, vb, h⟩
    exact ⟨hα, a, b, va, vb, Or.inr (Or.inr ⟨rfl, (M.ltRaw_iff hd hPr).mpr h⟩)⟩

/-- If the set of numerals of the hierarchy is empty, the atomic formulas with the relation
symbol `1` are never true. -/
theorem hier_T_false (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu) {α : V} (v w : M.Num) (t : V) :
    ¬ M.TrueAt P io F j.1 α (M.cRel 1 v w) t := by
  rw [M.hier_rel hd]
  rintro ⟨-, a, b, -, -, h⟩
  rcases h with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact h rfl
  · obtain ⟨-, -, β, c, ob, oc, t', -, -, -, -, hn, -⟩ := h
    exact hNu c oc hn
  · exact M.n12 (Subtype.ext h)

theorem lt_congr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a a' b b' : V}
    (sa : M.SimRaw P j.1 tp F a a') (sb : M.SimRaw P j.1 tp F b b')
    (h : M.Lt P j.1 tp F Pr a b) : M.Lt P j.1 tp F Pr a' b' := by
  obtain ⟨a0, b0, ca, cb, s1, s2, pp, np⟩ := h
  exact ⟨a0, b0, ca, cb, M.sim_trans hd (M.sim_symm hd sa) s1,
    M.sim_trans hd (M.sim_symm hd sb) s2, pp, np⟩

theorem lt_irrefl (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a b : V}
    (hs : M.SimRaw P j.1 tp F a b) : ¬ M.Lt P j.1 tp F Pr a b := by
  rintro ⟨a0, b0, ca, cb, sa, sb, pp, np⟩
  exact np (cb.2 a0 (M.sim_trans hd (M.sim_symm hd sb) (M.sim_trans hd (M.sim_symm hd hs) sa)))

theorem lt_trans' (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {a b c : V}
    (h1 : M.Lt P j.1 tp F Pr a b) (h2 : M.Lt P j.1 tp F Pr b c) : M.Lt P j.1 tp F Pr a c := by
  obtain ⟨a0, b0, ca, cb, sa, sb, pp, np⟩ := h1
  obtain ⟨b1, c0, cb1, cc, sb1, sc, q, nq⟩ := h2
  have t := M.can_tie hd cb cb1 (M.sim_trans hd (M.sim_symm hd sb) sb1)
  exact ⟨a0, c0, ca, cc, sa, sc, M.pr_trans hd hPr pp (M.pr_trans hd hPr t.1 q),
    fun h => nq (M.pr_trans hd hPr h (M.pr_trans hd hPr pp t.1))⟩

/-- **Trichotomy** for the canonical well-ordering. -/
theorem lt_tri (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {a b : V}
    (ha : M.SimRaw P j.1 tp F a a) (hb : M.SimRaw P j.1 tp F b b) :
    M.Lt P j.1 tp F Pr a b ∨ M.SimRaw P j.1 tp F a b ∨ M.Lt P j.1 tp F Pr b a := by
  obtain ⟨a0, ca, sa⟩ := M.exists_can hd hPr ha
  obtain ⟨b0, cb, sb⟩ := M.exists_can hd hPr hb
  obtain ⟨ρa, -, ra, -, hρa, -⟩ := M.sim_names hd ca.1
  obtain ⟨ρb, -, rb, -, hρb, -⟩ := M.sim_names hd cb.1
  by_cases pp : M.mem (M.op a0 b0) Pr
  · by_cases q : M.mem (M.op b0 a0) Pr
    · exact Or.inr (Or.inl (M.sim_trans hd sa (M.sim_trans hd (M.tie_sim hd hPr pp q)
        (M.sim_symm hd sb))))
    · exact Or.inl ⟨a0, b0, ca, cb, sa, sb, pp, q⟩
  · have q : M.mem (M.op b0 a0) Pr := (M.pr_total hd hPr ra rb hρa hρb).resolve_left pp
    exact Or.inr (Or.inr ⟨b0, a0, cb, ca, sb, sa, q, pp⟩)

/-- **The canonical ordering is well-founded**: every set that contains a name has a member
before which no member of the set comes. -/
theorem lt_least (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) (S : V)
    (hS : ∃ a, M.mem a S ∧ M.SimRaw P j.1 tp F a a) :
    ∃ a1, M.mem a1 S ∧ M.SimRaw P j.1 tp F a1 a1 ∧ ∀ b, M.mem b S → ¬ M.Lt P j.1 tp F Pr b a1 := by
  obtain ⟨a, haS, ha⟩ := hS
  obtain ⟨S0, -, hS00⟩ := M.comp (σW [(6, 5), (20, 7), (162, 5), (251, 3)])
    (.and (fCan 253) (Fml.ex 252 (.and (.mem 252 251) (fSim 252 253)))) 253 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 25 j.1) 162 Pr) 251 S)
  have hS0 : ∀ x, M.mem x S0 ↔ M.IsCan P j.1 tp F Pr x ∧ ∃ b, M.mem b S ∧ M.SimRaw P j.1 tp F b x := by
    intro x
    rw [hS00 x]
    simp [Sat, M.sat_ex, M.sat_fCan, M.sat_fSim, Function.update_apply]
  obtain ⟨a0, ca, sa⟩ := M.exists_can hd hPr ha
  obtain ⟨ρa, -, ra, -, hρa, -⟩ := M.sim_names hd ca.1
  obtain ⟨n1, ρ1, hn1S0, rn1, hρ1, hmin⟩ := M.pr_least hd hPr S0
    ⟨a0, ρa, (hS0 a0).mpr ⟨ca, a, haS, sa⟩, ra, hρa⟩
  obtain ⟨cn1, a1, ha1S, s1⟩ := (hS0 n1).mp hn1S0
  refine ⟨a1, ha1S, M.sim_trans hd s1 (M.sim_symm hd s1), fun b hbS hlt => ?_⟩
  obtain ⟨b0, a10, cb, c10, sb, s10, pp, np⟩ := hlt
  obtain ⟨ρb, -, rb, -, hρb, -⟩ := M.sim_names hd cb.1
  have h1 := hmin b0 ρb ((hS0 b0).mpr ⟨cb, b, hbS, sb⟩) rb hρb
  have t := M.can_tie hd c10 cn1 (M.sim_trans hd (M.sim_symm hd s10) s1)
  exact np (M.pr_trans hd hPr t.1 h1)

end prec6

/-! ## Least witnesses and the closure rules of the hulls -/

/-- `TrueAt` with the code as an object. -/
def TrueAtR (P io F j α c t : V) : Prop :=
  ∃ ch pt, M.mem (M.op c ch) io ∧ M.mem (M.quad j α ch pt) P ∧ M.mem (M.op pt t) F

/-- `TrueAtR`, with `α`, `c`, `t` the names `300`, `301`, `302`; the solution `F` of the
recursion is the name `163`. -/
def trueAtGFml : Fml :=
  Fml.ex 259 (Fml.ex 260 (.and (fApp 24 301 259) (.and (fApp4 20 25 300 259 260) (fApp 163 260
    302))))

theorem sat_trueAtGFml (ρ : ℕ → V) : Sat M.mem M.isSet trueAtGFml ρ ↔
    M.TrueAtR (ρ 20) (ρ 24) (ρ 163) (ρ 25) (ρ 300) (ρ 301) (ρ 302) := by
  simp [trueAtGFml, TrueAtR, Sat, M.sat_ex, M.sat_fApp', M.sat_fApp4', Function.update_apply]

/-- The formula `c` is true at stage `α` under the sequence `t` with the value at `v`
changed to `w`. -/
def TrueUpdR (P th io nat Nt j d ad F α c v t w : V) : Prop :=
  ∃ t', M.AgreeRaw P th io nat Nt j d ad α t t' v w c ∧ M.TrueAtR P io F j α c t'

/-- `TrueUpdR`, with `α`, `c`, `v`, `t`, `w` the names `300`, `301`, `303`, `304`, `305`. -/
def trueUpdFml : Fml :=
  Fml.ex 302 (.and (Fml.ex 65 (.and (.eq 65 300) (Fml.ex 5 (.and (.eq 5 304) (Fml.ex 80 (.and
    (.eq 80 302) (Fml.ex 81 (.and (.eq 81 303) (Fml.ex 82 (.and (.eq 82 305) (Fml.ex 83 (.and
    (.eq 83 301) agreeHFml)))))))))))) trueAtGFml)

theorem sat_trueUpdFml (ρ : ℕ → V) : Sat M.mem M.isSet trueUpdFml ρ ↔
    M.TrueUpdR (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 163) (ρ 300) (ρ 301)
      (ρ 303) (ρ 304) (ρ 305) := by
  simp [trueUpdFml, TrueUpdR, Sat, M.sat_ex, M.sat_agreeHFml, M.sat_trueAtGFml,
    Function.update_apply]

/-- `w` is the **least witness**: the least name of rank below `α`, in the order of the
names, among those `w` for which `c` is true at stage `α` under `t` with the value at `v`
changed to `w`, or among those for which it is not true. -/
def LWR (P th io nat Nt j d ad F Pr α c v t w : V) : Prop :=
  M.InNRaw P th io nat j α w ∧
  ((M.TrueUpdR P th io nat Nt j d ad F α c v t w ∧ ∀ w', M.InNRaw P th io nat j α w' →
      M.TrueUpdR P th io nat Nt j d ad F α c v t w' → M.mem (M.op w w') Pr) ∨
   (¬ M.TrueUpdR P th io nat Nt j d ad F α c v t w ∧ ∀ w', M.InNRaw P th io nat j α w' →
      ¬ M.TrueUpdR P th io nat Nt j d ad F α c v t w' → M.mem (M.op w w') Pr))

/-- `LWR`, with `α`, `c`, `v`, `t`, `w` the names `300`, `301`, `303`, `304`, `306`. -/
def lwFml : Fml :=
  .and (Fml.ex 65 (.and (.eq 65 300) (fInN 306))) (Fml.or (.and (Fml.ex 305 (.and (.eq 305 306)
    trueUpdFml)) (.all 307 (Fml.imp (Fml.ex 65 (.and (.eq 65 300) (fInN 307))) (Fml.imp (Fml.ex
    305 (.and (.eq 305 307) trueUpdFml)) (fApp 162 306 307))))) (.and (.neg (Fml.ex 305 (.and
    (.eq 305 306) trueUpdFml))) (.all 307 (Fml.imp (Fml.ex 65 (.and (.eq 65 300) (fInN 307)))
    (Fml.imp (.neg (Fml.ex 305 (.and (.eq 305 307) trueUpdFml))) (fApp 162 306 307))))))

theorem sat_lwFml (ρ : ℕ → V) : Sat M.mem M.isSet lwFml ρ ↔
    M.LWR (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 163) (ρ 162) (ρ 300) (ρ 301)
      (ρ 303) (ρ 304) (ρ 306) := by
  simp [lwFml, LWR, Sat, M.sat_imp, M.sat_or, M.sat_ex, M.sat_fInN, M.sat_fApp',
    M.sat_trueUpdFml, Function.update_apply]

/-- `n` is the name of rank `β` with the formula `c` (an object) and the parameters `u`. -/
def NameR (P io nat j n β c u : V) : Prop :=
  ∃ f q, M.mem (M.quad j β q n) P ∧ M.mem (M.quad j f u q) P ∧ M.mem c nat ∧ M.mem (M.op c f) io

/-- Rule 1: with a name, the ordinal name of its rank. -/
def R1 (P io nat j qo X : V) : Prop :=
  ∀ n β o, M.mem n X → M.RankIs P io nat j β n → M.mem (M.quad j β qo o) P → M.mem o X

/-- Rule 2: with a name, the values of its parameters. -/
def R2 (P th io nat Nt j d ad X : V) : Prop :=
  ∀ n β c u i e, M.mem n X → M.NameR P io nat j n β c u → M.mem i nat → (∃ x, M.mem x nat ∧ M.mem (M.trip i x c) ad) →
    M.ValRaw P th io nat Nt j d β u i e → M.mem e X

/-- Rule 3: every name whose rank is below `ρ` and has its ordinal name in the set, and
whose parameters have their values in the set. -/
def R3 (P th io nat Nt j d ad qo X ρ : V) : Prop :=
  ∀ n β c u o, M.mem (M.quad j β qo o) P → M.mem o X → M.mem (M.op β ρ) th → ¬ β = ρ →
    M.NameR P io nat j n β c u →
    (∀ i e, M.mem i nat → (∃ x, M.mem x nat ∧ M.mem (M.trip i x c) ad) →
      M.ValRaw P th io nat Nt j d β u i e → M.mem e X) → M.mem n X

/-- Rule 4: with a name, the canonical names of the set it denotes. -/
def R4 (P j tp F Pr X : V) : Prop :=
  ∀ n n0, M.mem n X → M.IsCan P j tp F Pr n0 → M.SimRaw P j tp F n n0 → M.mem n0 X

/-- Rule 5: the least witnesses, at the stage `ρ` and at the stages below it whose ordinal
names are in the set, for all formulas and all sequences with values in the set. -/
def R5 (P th io nat Nt j d ad F Pr qo X ρ : V) : Prop :=
  ∀ β c v t w, (β = ρ ∨ (M.mem (M.op β ρ) th ∧ ¬ β = ρ ∧ ∃ o, M.mem (M.quad j β qo o) P ∧
      M.mem o X)) → M.mem c nat → M.mem v nat →
    (∀ i e, M.mem i nat → (∃ x, M.mem x nat ∧ M.mem (M.trip i x c) ad) →
      M.ValRaw P th io nat Nt j d β t i e → M.mem e X) →
    M.LWR P th io nat Nt j d ad F Pr β c v t w → M.mem w X

/-- Rule 6: with the ordinal name of `β₁`, the ordinal name of the least stage `β₂ ≥ β₁`
recorded in `G` for `ν`, and the least generators recorded there. -/
def R6 (P th j qo Pr G X ν : V) : Prop :=
  ∀ β1 o1 β2 w y, M.mem (M.quad j β1 qo o1) P → M.mem o1 X → M.mem (M.op β1 β2) th →
    M.mem (M.quad j ν w y) P → M.mem (M.op β2 y) G →
    (∀ β' b' y', M.mem (M.quad j ν b' y') P → M.mem (M.op β' y') G → M.mem (M.op β1 β') th →
      M.mem (M.op β2 β') th) →
    (∀ b' y', M.mem (M.quad j ν b' y') P → M.mem (M.op β2 y') G → M.mem (M.op w b') Pr) →
    (∀ o2, M.mem (M.quad j β2 qo o2) P → M.mem o2 X) ∧ M.mem w X

/-- Rules 1–6 as formulas; the set `X` is the name `270`, the stage `ρ` the name `271`, `ν`
the name `272`, `G` the name `6`, `F` the name `163`. -/
def r1Fml : Fml :=
  .all 280 (.all 281 (.all 282 (Fml.imp (.mem 280 270) (Fml.imp (fRank 281 280) (Fml.imp (fApp4
    20 25 281 160 282) (.mem 282 270))))))

theorem sat_r1Fml (ρ : ℕ → V) : Sat M.mem M.isSet r1Fml ρ ↔
    M.R1 (ρ 20) (ρ 24) (ρ 27) (ρ 25) (ρ 160) (ρ 270) := by
  simp [r1Fml, R1, Sat, M.sat_imp, M.sat_fRank, M.sat_fApp4', Function.update_apply]

def r2Fml : Fml :=
  .all 280 (.all 281 (.all 283 (.all 284 (.all 285 (.all 286 (Fml.imp (.mem 280 270) (Fml.imp
    (Fml.ex 262 (Fml.ex 263 (.and (fApp4 20 25 281 263 280) (.and (fApp4 20 25 262 284 263)
    (.and (.mem 283 27) (fApp 24 283 262)))))) (Fml.imp (.mem 285 27) (Fml.imp (fLeN 285 283)
    (Fml.imp (fVal 281 284 285 286) (.mem 286 270)))))))))))

theorem sat_r2Fml (ρ : ℕ → V) : Sat M.mem M.isSet r2Fml ρ ↔
    M.R2 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 270) := by
  simp [r2Fml, R2, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fLeN, M.sat_fApp',
    M.sat_fApp4', Function.update_apply]

def r3Fml : Fml :=
  .all 280 (.all 281 (.all 283 (.all 284 (.all 282 (Fml.imp (fApp4 20 25 281 160 282) (Fml.imp
    (.mem 282 270) (Fml.imp (fApp 22 281 271) (Fml.imp (.neg (.eq 281 271)) (Fml.imp (Fml.ex 262
    (Fml.ex 263 (.and (fApp4 20 25 281 263 280) (.and (fApp4 20 25 262 284 263) (.and (.mem 283
    27) (fApp 24 283 262)))))) (Fml.imp (.all 285 (.all 286 (Fml.imp (.mem 285 27) (Fml.imp
    (fLeN 285 283) (Fml.imp (fVal 281 284 285 286) (.mem 286 270)))))) (.mem 280 270)))))))))))

theorem sat_r3Fml (ρ : ℕ → V) : Sat M.mem M.isSet r3Fml ρ ↔
    M.R3 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 160) (ρ 270) (ρ 271) := by
  simp [r3Fml, R3, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fLeN, M.sat_fApp',
    M.sat_fApp4', Function.update_apply]

def r4Fml : Fml :=
  .all 280 (.all 287 (Fml.imp (.mem 280 270) (Fml.imp (.and (Fml.ex 6 (.and (.eq 6 163) (fSim
    287 287))) (.all 258 (Fml.imp (Fml.ex 6 (.and (.eq 6 163) (fSim 287 258))) (fApp 162 287
    258)))) (Fml.imp (Fml.ex 6 (.and (.eq 6 163) (fSim 280 287))) (.mem 287 270)))))

theorem sat_r4Fml (ρ : ℕ → V) : Sat M.mem M.isSet r4Fml ρ ↔
    M.R4 (ρ 20) (ρ 25) (ρ 21) (ρ 163) (ρ 162) (ρ 270) := by
  simp [r4Fml, R4, IsCan, Sat, M.sat_imp, M.sat_ex, M.sat_fSim, M.sat_fApp',
    Function.update_apply]

def r5Fml : Fml :=
  .all 300 (.all 301 (.all 303 (.all 304 (.all 306 (Fml.imp (Fml.or (.eq 300 271) (.and (fApp 22
    300 271) (.and (.neg (.eq 300 271)) (Fml.ex 282 (.and (fApp4 20 25 300 160 282) (.mem 282
    270)))))) (Fml.imp (.mem 301 27) (Fml.imp (.mem 303 27) (Fml.imp (.all 285 (.all 286
    (Fml.imp (.mem 285 27) (Fml.imp (fLeN 285 301) (Fml.imp (fVal 300 304 285 286) (.mem 286
    270)))))) (Fml.imp lwFml (.mem 306 270))))))))))

theorem sat_r5Fml (ρ : ℕ → V) : Sat M.mem M.isSet r5Fml ρ ↔
    M.R5 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 163) (ρ 162) (ρ 160) (ρ 270)
      (ρ 271) := by
  simp [r5Fml, R5, Sat, M.sat_imp, M.sat_or, M.sat_ex, M.sat_fVal, M.sat_fLeN, M.sat_fApp',
    M.sat_fApp4', M.sat_lwFml, Function.update_apply]

def r6Fml : Fml :=
  .all 288 (.all 289 (.all 290 (.all 291 (.all 292 (Fml.imp (fApp4 20 25 288 160 289) (Fml.imp
    (.mem 289 270) (Fml.imp (fApp 22 288 290) (Fml.imp (fApp4 20 25 272 291 292) (Fml.imp (fApp
    6 290 292) (Fml.imp (.all 293 (.all 294 (.all 295 (Fml.imp (fApp4 20 25 272 294 295)
    (Fml.imp (fApp 6 293 295) (Fml.imp (fApp 22 288 293) (fApp 22 290 293))))))) (Fml.imp (.all
    294 (.all 295 (Fml.imp (fApp4 20 25 272 294 295) (Fml.imp (fApp 6 290 295) (fApp 162 291
    294))))) (.and (.all 296 (Fml.imp (fApp4 20 25 290 160 296) (.mem 296 270))) (.mem 291
    270)))))))))))))

theorem sat_r6Fml (ρ : ℕ → V) : Sat M.mem M.isSet r6Fml ρ ↔
    M.R6 (ρ 20) (ρ 22) (ρ 25) (ρ 160) (ρ 162) (ρ 6) (ρ 270) (ρ 272) := by
  simp [r6Fml, R6, Sat, M.sat_imp, M.sat_fApp', M.sat_fApp4', Function.update_apply]

/-- The set `X` is closed under the six rules. -/
def ClosedR (P th io nat Nt j d ad tp qo F Pr G X ρ ν : V) : Prop :=
  M.R1 P io nat j qo X ∧ M.R2 P th io nat Nt j d ad X ∧ M.R3 P th io nat Nt j d ad qo X ρ ∧
  M.R4 P j tp F Pr X ∧ M.R5 P th io nat Nt j d ad F Pr qo X ρ ∧ M.R6 P th j qo Pr G X ν

def closedFml : Fml :=
  .and r1Fml (.and r2Fml (.and r3Fml (.and r4Fml (.and r5Fml r6Fml))))

theorem sat_closedFml (ρ : ℕ → V) : Sat M.mem M.isSet closedFml ρ ↔
    M.ClosedR (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 21) (ρ 160) (ρ 163)
      (ρ 162) (ρ 6) (ρ 270) (ρ 271) (ρ 272) := by
  simp [closedFml, ClosedR, Sat, M.sat_r1Fml, M.sat_r2Fml, M.sat_r3Fml, M.sat_r4Fml,
    M.sat_r5Fml, M.sat_r6Fml]

/-- The names of rank below `ρ` are generated from the names of rank below `ν`, the name `b`
and the default name: every set that contains these and is closed under the rules contains
all names of rank below `ρ`. -/
def GenR (P th io nat Nt j d ad tp qo F Pr G ν ρ b : V) : Prop :=
  M.mem (M.op ν ρ) th ∧ ¬ ν = ρ ∧ M.InNRaw P th io nat j ρ b ∧
  ∀ X, (∀ x, M.InNRaw P th io nat j ν x → M.mem x X) → M.mem b X → M.mem d X →
    M.ClosedR P th io nat Nt j d ad tp qo F Pr G X ρ ν →
    ∀ x, M.InNRaw P th io nat j ρ x → M.mem x X

/-- One step of the recursion for the record of generators: `y` is the pair of `ν` and `b`
with `GenR ν ρ b`; the names `4`, `5`, `6` are `ρ`, `y`, `G`. -/
def genFml : Fml :=
  Fml.ex 272 (Fml.ex 273 (.and (fApp4 20 25 272 273 5) (.and (fApp 22 272 4) (.and (.neg (.eq
    272 4)) (.and (Fml.ex 65 (.and (.eq 65 4) (fInN 273))) (.all 270 (Fml.imp (.all 274 (Fml.imp
    (Fml.ex 65 (.and (.eq 65 272) (fInN 274))) (.mem 274 270))) (Fml.imp (.mem 273 270) (Fml.imp
    (.mem 26 270) (Fml.imp (Fml.ex 271 (.and (.eq 271 4) closedFml)) (.all 274 (Fml.imp (Fml.ex
    65 (.and (.eq 65 4) (fInN 274))) (.mem 274 270)))))))))))))

theorem sat_genFml (ρ : ℕ → V) : Sat M.mem M.isSet genFml ρ ↔
    ∃ ν b, M.mem (M.quad (ρ 25) ν b (ρ 5)) (ρ 20) ∧
      M.GenR (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 21) (ρ 160) (ρ 163)
        (ρ 162) (ρ 6) ν (ρ 4) b := by
  simp [genFml, GenR, Sat, M.sat_imp, M.sat_ex, M.sat_fInN, M.sat_fApp', M.sat_fApp4',
    M.sat_closedFml, Function.update_apply]

/-- The hull as a formula: `x` (the name `275`) has rank below `δ` (the name `271`) and
belongs to every closed set that contains the names of rank below `ν` (`272`), the name `b`
(`273`) and the default name. -/
def hullFml : Fml :=
  .and (Fml.ex 65 (.and (.eq 65 271) (fInN 275))) (.all 270 (Fml.imp (.all 274 (Fml.imp (Fml.ex
    65 (.and (.eq 65 272) (fInN 274))) (.mem 274 270))) (Fml.imp (.mem 273 270) (Fml.imp (.mem
    26 270) (Fml.imp closedFml (.mem 275 270))))))

theorem sat_hullFml (ρ : ℕ → V) : Sat M.mem M.isSet hullFml ρ ↔
    M.InNRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 25) (ρ 271) (ρ 275) ∧
    ∀ X, (∀ x, M.InNRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 25) (ρ 272) x → M.mem x X) →
      M.mem (ρ 273) X → M.mem (ρ 26) X →
      M.ClosedR (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 21) (ρ 160) (ρ 163)
        (ρ 162) (ρ 6) X (ρ 271) (ρ 272) → M.mem (ρ 275) X := by
  simp [hullFml, Sat, M.sat_imp, M.sat_ex, M.sat_fInN, M.sat_closedFml, Function.update_apply]

/-! ## Markers of stages -/

/-- `q` is a **marker parameter**: a formula number together with a sequence all of whose
values, at every stage, are the default name. The name of rank `β` with this parameter is the
*marker* of the stage `β`. -/
def IsMark (P th io Nt d : V) (j : M.Num) (q : V) : Prop :=
  ∃ (f t0 : V) (c0 : M.Num), M.mem (M.op c0.1 f) io ∧ M.mem (M.quad j.1 f t0 q) P ∧
    ∀ (α : V) (i : M.Num), i ≤ c0 → M.ValRaw P th io M.nat Nt j.1 d α t0 i.1 d

section mark

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {q1 : V}

/-- A sequence all of whose values at the indices below `n` are the default name. -/
theorem const_seq (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (n : M.Num) :
    ∃ t0, M.mem (M.op j.1 t0) R ∧ ∀ (α : V) (k : M.Num), k + 1 ≤ n →
      M.ValRaw P th io M.nat Nt j.1 d α t0 k.1 d := by
  obtain ⟨g, -, hg0⟩ := M.comp (σW [(0, 4), (27, 3)])
    (Fml.ex 326 (.and (fPr 0 326 26) (.mem 326 27))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 26 d) 27 M.nat)
  have hg1 : ∀ q, M.mem q g ↔ ∃ i, q = M.op i d ∧ M.mem i M.nat := by
    intro q
    rw [hg0 q]
    simp [Sat, M.sat_ex, M.sat_fPr', Function.update_apply]
  obtain ⟨t0, ht0R, hcode⟩ := M.seq_code hd.hP hd.hj ⟨d, M.d_rung hd⟩ hd.nt_zero hd.nt_succ n g
    (fun k _ => ⟨d, M.d_rung hd, (hg1 _).mpr ⟨k.1, rfl, k.2⟩⟩)
  refine ⟨t0, ht0R, fun α k hk => ?_⟩
  obtain ⟨a, hga, hnt⟩ := hcode k hk
  obtain ⟨i, eq, -⟩ := (hg1 _).mp hga
  rw [(M.op_inj eq).2] at hnt
  rcases M.val_of_nth hd (α := α) hnt with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h

theorem exists_isMark (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) :
    ∃ q, M.IsMark P th io Nt d j q := by
  obtain ⟨t0, ht0R, hconst⟩ := M.const_seq hd (0 + 1)
  obtain ⟨f, hf⟩ := hd.io_tot 0
  obtain ⟨q, hq⟩ := hd.hP.tot j hd.hj f t0 (hd.io_dom _ _ hf).2 ht0R
  exact ⟨q, f, t0, 0, hf, hq, fun α i hi => hconst α i (add_le_add hi (le_refl 1))⟩

theorem mark_rank (hq : M.IsMark P th io Nt d j q1) {ξ o : V}
    (ho : M.mem (M.quad j.1 ξ q1 o) P) : M.RankIs P io M.nat j.1 ξ o := by
  obtain ⟨f, t0, c0, hf, hfq, -⟩ := hq
  exact ⟨f, t0, q1, ho, hfq, c0.1, c0.2, hf⟩

theorem exists_mark (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hq : M.IsMark P th io Nt d j q1) {ξ : V} (hξ : M.mem (M.op ξ ξ) th) :
    ∃ o, M.mem (M.quad j.1 ξ q1 o) P := by
  obtain ⟨f, t0, c0, hf, hfq, -⟩ := hq
  exact hd.hP.tot j hd.hj ξ q1 (hd.th_rung ξ ξ hξ).1 (hd.hP.dom _ _ _ _ hfq).2.2.2

/-- The marker of a stage is the name with a fixed formula and a sequence whose values are
the default name. -/
theorem mark_name (hq : M.IsMark P th io Nt d j q1) {ξ o : V}
    (ho : M.mem (M.quad j.1 ξ q1 o) P) :
    ∃ (c0 : M.Num) (t0 : V), M.NameOf P io j o ξ c0 t0 ∧
      ∀ (α : V) (i : M.Num), i ≤ c0 → M.ValRaw P th io M.nat Nt j.1 d α t0 i.1 d := by
  obtain ⟨f, t0, c0, hf, hfq, hv⟩ := hq
  exact ⟨c0, t0, ⟨f, q1, ho, hfq, hf⟩, hv⟩

end mark

/-! ## The record of generators and the hulls -/

/-- `Sg` is the **record of generators**: the pair of a stage `ρ` and the code `y` of a pair
`(ν, b)` belongs to it if and only if the names of rank below `ρ` are generated from the names
of rank below `ν` and `b`, by the six rules, where rule 6 uses the record below `ρ`. -/
def IsSig (P th io Nt d tp qo F Pr Sg : V) (j : M.Num) : Prop :=
  ∀ ρ y, M.mem (M.op ρ y) Sg ↔ M.mem (M.op ρ ρ) th ∧ ∃ ν b, M.mem (M.quad j.1 ν b y) P ∧
    M.GenR P th io M.nat Nt j.1 d M.adG tp qo F Pr (M.restr th Sg ρ) ν ρ b

theorem exists_sig {th : V} (hth : M.IsWO th) (P io Nt d tp qo F Pr : V) (j : M.Num) :
    ∃ Sg, M.IsSig P th io Nt d tp qo F Pr Sg j := by
  obtain ⟨ρ, e20, e21, e22, e23, e24, e25, e26, e27, e28, e160, e162, e163⟩ :
      ∃ ρ : ℕ → V, ρ 20 = P ∧ ρ 21 = tp ∧ ρ 22 = th ∧ ρ 23 = Nt ∧ ρ 24 = io ∧ ρ 25 = j.1 ∧
        ρ 26 = d ∧ ρ 27 = M.nat ∧ ρ 28 = M.adG ∧ ρ 160 = qo ∧ ρ 162 = Pr ∧ ρ 163 = F :=
    ⟨(Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 21 tp) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 160 qo) 162 Pr) 163 F),
      by simp [Function.update_apply]⟩
  exact M.wo_rec hth (fun α y G => ∃ ν b, M.mem (M.quad j.1 ν b y) P ∧
      M.GenR P th io M.nat Nt j.1 d M.adG tp qo F Pr G ν α b) genFml
    [(20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7), (162, 5), (163, 5), (270, 3)] rfl ρ
    (fun ρ' h => by
      rw [M.sat_genFml, h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide),
        h 24 (by decide), h 25 (by decide), h 26 (by decide), h 27 (by decide), h 28 (by decide),
        h 160 (by decide), h 162 (by decide), h 163 (by decide),
        e20, e21, e22, e23, e24, e25, e26, e27, e28, e160, e162, e163])

/-- The names of rank below `ρ` are generated from the names of rank below `ν` and `b`. -/
def Gen (P Sg : V) (j : M.Num) (ν ρ b : V) : Prop :=
  ∃ y, M.mem (M.quad j.1 ν b y) P ∧ M.mem (M.op ρ y) Sg

/-- `N` is the **hull** at the stage `δ` of the names of rank below `ν` and the name `b`:
the names of rank below `δ` that belong to every closed set containing these and the default
name. -/
def IsHull (P th io Nt d tp qo F Pr Sg : V) (j : M.Num) (N δ ν b : V) : Prop :=
  ∀ x, M.mem x N ↔ M.InNRaw P th io M.nat j.1 δ x ∧
    ∀ X, (∀ x, M.InNRaw P th io M.nat j.1 ν x → M.mem x X) → M.mem b X → M.mem d X →
      M.ClosedR P th io M.nat Nt j.1 d M.adG tp qo F Pr (M.restr th Sg δ) X δ ν → M.mem x X

section hull1

variable {R P th io Nt nle p F d tp qo Nu Pr Sg : V} {m j : M.Num}
variable {q1 : V}

theorem nameR_rank {n β c u : V} (h : M.NameR P io M.nat j.1 n β c u) :
    M.RankIs P io M.nat j.1 β n := by
  obtain ⟨f, q, h1, h2, h3, h4⟩ := h
  exact ⟨f, u, q, h1, h2, c, h3, h4⟩

theorem nameR_iff {n β u : V} (c : M.Num) :
    M.NameR P io M.nat j.1 n β c.1 u ↔ M.NameOf P io j n β c u := by
  constructor
  · rintro ⟨f, q, h1, h2, -, h4⟩
    exact ⟨f, q, h1, h2, h4⟩
  · rintro ⟨f, q, h1, h2, h4⟩
    exact ⟨f, q, h1, h2, c.2, h4⟩

theorem gen_iff (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {ν ρ b : V} :
    M.Gen P Sg j ν ρ b ↔ M.mem (M.op ρ ρ) th ∧
      M.GenR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) ν ρ b := by
  constructor
  · rintro ⟨y, hy, hSgm⟩
    obtain ⟨hρ, ν', b', hy', hgen⟩ := (hSg ρ y).mp hSgm
    obtain ⟨e1, e2⟩ := hd.hP.inj _ _ _ _ _ _ hy' hy
    rw [e1, e2] at hgen
    exact ⟨hρ, hgen⟩
  · rintro ⟨hρ, hgen⟩
    obtain ⟨y, hy⟩ := hd.hP.tot j hd.hj ν b (hd.th_rung _ _ hgen.1).1 (M.inN_rung hd hgen.2.2.1)
    exact ⟨y, hy, (hSg ρ y).mpr ⟨hρ, ν, b, hy, hgen⟩⟩

theorem gen_lt (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {ν ρ b : V} (h : M.Gen P Sg j ν ρ b) :
    M.mem (M.op ν ρ) th ∧ ν ≠ ρ ∧ M.InNRaw P th io M.nat j.1 ρ b := by
  obtain ⟨-, h1, h2, h3, -⟩ := (M.gen_iff hd hSg).mp h
  exact ⟨h1, h2, h3⟩

theorem exists_hull (Sg δ ν b : V) : ∃ N, M.IsHull P th io Nt d tp q1 F Pr Sg j N δ ν b := by
  obtain ⟨N, -, hN0⟩ := M.comp
    (σW [(6, 5), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7), (162, 5), (163, 5),
      (270, 3)]) hullFml 275 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 (M.restr th Sg δ)) 20 P) 21 tp) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 160 q1) 162 Pr) 163 F) 271 δ) 272 ν) 273 b)
  refine ⟨N, fun x => ?_⟩
  rw [hN0 x, M.sat_hullFml]
  simp [Function.update_apply]

theorem hull_sub {N δ ν b x : V} (hN : M.IsHull P th io Nt d tp q1 F Pr Sg j N δ ν b)
    (h : M.mem x N) : M.InNRaw P th io M.nat j.1 δ x := ((hN x).mp h).1

/-- The hull is contained in every closed set that contains the generators. -/
theorem hull_min {N δ ν b X x : V} (hN : M.IsHull P th io Nt d tp q1 F Pr Sg j N δ ν b)
    (b1 : ∀ x, M.InNRaw P th io M.nat j.1 ν x → M.mem x X) (b2 : M.mem b X) (b3 : M.mem d X)
    (hX : M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg δ) X δ ν)
    (h : M.mem x N) : M.mem x X := ((hN x).mp h).2 X b1 b2 b3 hX

theorem hull_base (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {N δ ν b x : V}
    (hN : M.IsHull P th io Nt d tp q1 F Pr Sg j N δ ν b) (hνδ : M.mem (M.op ν δ) th)
    (hx : M.InNRaw P th io M.nat j.1 ν x) : M.mem x N :=
  (hN x).mpr ⟨M.inN_mono hd hx hνδ, fun X b1 _ _ _ => b1 x hx⟩

theorem hull_gen {N δ ν b : V} (hN : M.IsHull P th io Nt d tp q1 F Pr Sg j N δ ν b)
    (hb : M.InNRaw P th io M.nat j.1 δ b) : M.mem b N :=
  (hN b).mpr ⟨hb, fun X _ b2 _ _ => b2⟩

theorem hull_d {N δ ν b : V} (hN : M.IsHull P th io Nt d tp q1 F Pr Sg j N δ ν b)
    (hb : M.InNRaw P th io M.nat j.1 δ d) : M.mem d N :=
  (hN d).mpr ⟨hb, fun X _ _ b3 _ => b3⟩

/-- **The hull is closed** under the six rules. -/
theorem hull_closed (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) (hq : M.IsMark P th io Nt d j q1)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {N δ ν b : V}
    (hN : M.IsHull P th io Nt d tp q1 F Pr Sg j N δ ν b) :
    M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg δ) N δ ν := by
  have sub : ∀ {x : V}, M.mem x N → M.InNRaw P th io M.nat j.1 δ x := fun h => ((hN _).mp h).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n β o hn rn ho
    obtain ⟨β', rn', lt, ne⟩ := M.inN_rank (sub hn)
    have e := M.rank_unique hd rn rn'
    rw [← e] at lt ne
    exact (hN o).mpr ⟨M.rank_inN (M.mark_rank hq ho) lt ne, fun X b1 b2 b3 hX =>
      hX.1 n β o (((hN n).mp hn).2 X b1 b2 b3 hX) rn ho⟩
  · intro n β c u i e hn hname hi hle hv
    obtain ⟨β', rn', lt, ne⟩ := M.inN_rank (sub hn)
    have e' := M.rank_unique hd (M.nameR_rank hname) rn'
    rw [← e'] at lt ne
    have heN : M.InNRaw P th io M.nat j.1 δ e := by
      rcases M.val_cases hv with h | h
      · exact M.inN_mono hd h lt
      · rw [h]
        exact M.d_inN hd lt ne
    exact (hN e).mpr ⟨heN, fun X b1 b2 b3 hX =>
      hX.2.1 n β c u i e (((hN n).mp hn).2 X b1 b2 b3 hX) hname hi hle hv⟩
  · intro n β c u o ho hoN lt ne hname hvals
    exact (hN n).mpr ⟨M.rank_inN (M.nameR_rank hname) lt ne, fun X b1 b2 b3 hX =>
      hX.2.2.1 n β c u o ho (((hN o).mp hoN).2 X b1 b2 b3 hX) lt ne hname
        (fun i e hi hle hv => ((hN e).mp (hvals i e hi hle hv)).2 X b1 b2 b3 hX)⟩
  · intro n n0 hn hc hs
    exact (hN n0).mpr ⟨M.can_inN hd hPr (sub hn) hc hs, fun X b1 b2 b3 hX =>
      hX.2.2.2.1 n n0 (((hN n).mp hn).2 X b1 b2 b3 hX) hc hs⟩
  · intro β c v t w hβ hc hv hvals hlw
    have hwN : M.InNRaw P th io M.nat j.1 δ w := by
      rcases hβ with e | ⟨lt, ne, -⟩
      · rw [← e]
        exact hlw.1
      · exact M.inN_mono hd hlw.1 lt
    refine (hN w).mpr ⟨hwN, fun X b1 b2 b3 hX => hX.2.2.2.2.1 β c v t w ?_ hc hv
      (fun i e hi hle hv' => ((hN e).mp (hvals i e hi hle hv')).2 X b1 b2 b3 hX) hlw⟩
    rcases hβ with e | ⟨lt, ne, o, ho, hoN⟩
    · exact Or.inl e
    · exact Or.inr ⟨lt, ne, o, ho, ((hN o).mp hoN).2 X b1 b2 b3 hX⟩
  · intro β1 o1 β2 w y ho1 ho1N h12 hwy hG hmin hleast
    obtain ⟨hSgm, lt2, ne2⟩ := M.mem_restr.mp hG
    obtain ⟨hβ2, ν', b', hy', hgen⟩ := (hSg β2 y).mp hSgm
    obtain ⟨e1, e2⟩ := hd.hP.inj _ _ _ _ _ _ hy' hwy
    have hwN : M.InNRaw P th io M.nat j.1 δ w := by
      rw [← e2]
      exact M.inN_mono hd hgen.2.2.1 lt2
    constructor
    · intro o2 ho2
      exact (hN o2).mpr ⟨M.rank_inN (M.mark_rank hq ho2) lt2 ne2, fun X b1 b2 b3 hX =>
        (hX.2.2.2.2.2 β1 o1 β2 w y ho1 (((hN o1).mp ho1N).2 X b1 b2 b3 hX) h12 hwy hG hmin
          hleast).1 o2 ho2⟩
    · exact (hN w).mpr ⟨hwN, fun X b1 b2 b3 hX =>
        (hX.2.2.2.2.2 β1 o1 β2 w y ho1 (((hN o1).mp ho1N).2 X b1 b2 b3 hX) h12 hwy hG hmin
          hleast).2⟩

end hull1

/-! ## Generated levels: the hull contains the levels below a generated stage -/

/-- `β'` is the successor of the stage `β`. -/
def IsSucc (th β β' : V) : Prop :=
  M.mem (M.op β β') th ∧ β ≠ β' ∧ ∀ γ, M.mem (M.op β γ) th → β ≠ γ → M.mem (M.op β' γ) th

/-- The stage `ρ` is **`ν`-small**: the names of rank below some stage `ρ₂ ≥ ρ` are generated
from the names of rank below `ν` and one more name. -/
def Small (P th Sg : V) (j : M.Num) (ν ρ : V) : Prop :=
  ∃ ρ2 b, M.mem (M.op ρ ρ2) th ∧ M.Gen P Sg j ν ρ2 b

/-- `κ` is the least stage that is not `ν`-small. -/
def IsNext (P th Sg : V) (j : M.Num) (ν κ : V) : Prop :=
  M.mem (M.op κ κ) th ∧ ¬ M.Small P th Sg j ν κ ∧
    ∀ ρ, M.mem (M.op ρ κ) th → ρ ≠ κ → M.Small P th Sg j ν ρ

section hull2

variable {R P th io Nt nle p F d tp qo Nu Pr Sg : V} {m j : M.Num}
variable {q1 : V}

/-- A set closed at the stage `δ` that contains the ordinal name of a stage `ρ` below `δ` is
closed at the stage `ρ`. -/
theorem closed_lower (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {X δ ρ ν o : V}
    (hX : M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg δ) X δ ν)
    (hρδ : M.mem (M.op ρ δ) th) (hne : ρ ≠ δ) (ho : M.mem (M.quad j.1 ρ q1 o) P)
    (hoX : M.mem o X) :
    M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) X ρ ν := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hX
  have below : ∀ {β : V}, M.mem (M.op β ρ) th → β ≠ δ := by
    intro β hβ e
    rw [e] at hβ
    exact hne (hd.hth.antisymm _ _ hρδ hβ)
  refine ⟨h1, h2, ?_, h4, ?_, ?_⟩
  · intro n β c u o' ho' ho'X lt ne hname hvals
    exact h3 n β c u o' ho' ho'X (hd.hth.trans _ _ _ lt hρδ) (below lt) hname hvals
  · intro β c v t w hβ hc hv hvals hlw
    refine h5 β c v t w ?_ hc hv hvals hlw
    rcases hβ with e | ⟨lt, ne, o', ho', ho'X⟩
    · rw [e]
      exact Or.inr ⟨hρδ, hne, o, ho, hoX⟩
    · exact Or.inr ⟨hd.hth.trans _ _ _ lt hρδ, below lt, o', ho', ho'X⟩
  · intro β1 o1 β2 w y ho1 ho1X h12 hwy hG hmin hleast
    obtain ⟨hSgm, lt2, ne2⟩ := M.mem_restr.mp hG
    refine h6 β1 o1 β2 w y ho1 ho1X h12 hwy
      (M.mem_restr.mpr ⟨hSgm, hd.hth.trans _ _ _ lt2 hρδ, below lt2⟩)
      (fun β' b' y' hq' hG' h1' => ?_)
      (fun b' y' hq' hG' => hleast b' y' hq' (M.mem_restr.mpr ⟨(M.mem_restr.mp hG').1, lt2, ne2⟩))
    obtain ⟨hS', lt', ne'⟩ := M.mem_restr.mp hG'
    by_cases hlt : M.mem (M.op β' ρ) th ∧ β' ≠ ρ
    · exact hmin β' b' y' hq' (M.mem_restr.mpr ⟨hS', hlt.1, hlt.2⟩) h1'
    · rcases M.wo_total hd.hth (hd.hth.fld _ _ hρδ).1 (hd.hth.fld _ _ lt').1 with h | h
      · exact hd.hth.trans _ _ _ lt2 h
      · by_cases e : β' = ρ
        · rw [e]
          exact lt2
        · exact (hlt ⟨h, e⟩).elim

/-- **Generated levels are inside the hull.** If the names of rank below `ρ` are generated
from the names of rank below `ν` and `b`, then every set that is closed at a later stage `δ`
and contains these names and the ordinal name of `ρ` contains all names of rank below `ρ`. -/
theorem gen_sub (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {X δ ρ ν b o : V}
    (hgen : M.Gen P Sg j ν ρ b)
    (hX : M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg δ) X δ ν)
    (hρδ : M.mem (M.op ρ δ) th) (hne : ρ ≠ δ) (ho : M.mem (M.quad j.1 ρ q1 o) P)
    (hoX : M.mem o X) (b1 : ∀ x, M.InNRaw P th io M.nat j.1 ν x → M.mem x X) (b2 : M.mem b X)
    (b3 : M.mem d X) : ∀ x, M.InNRaw P th io M.nat j.1 ρ x → M.mem x X :=
  ((M.gen_iff hd hSg).mp hgen).2.2.2.2 X b1 b2 b3 (M.closed_lower hd hX hρδ hne ho hoX)

/-- A closed set that contains the ordinal name of a stage `β` below `δ` and all names of
rank below `β` contains all names of rank `β`. -/
theorem closed_rank (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {X δ β ν o G : V}
    (hX : M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr G X δ ν)
    (hβδ : M.mem (M.op β δ) th) (hne : β ≠ δ) (ho : M.mem (M.quad j.1 β q1 o) P)
    (hoX : M.mem o X) (hlow : ∀ x, M.InNRaw P th io M.nat j.1 β x → M.mem x X)
    (b3 : M.mem d X) {x : V} (rx : M.RankIs P io M.nat j.1 β x) : M.mem x X := by
  obtain ⟨k, u, hn⟩ := M.rank_nameOf rx
  refine hX.2.2.1 x β k.1 u o ho hoX hβδ hne ((M.nameR_iff k).mpr hn) (fun i e _ _ hv => ?_)
  rcases M.val_cases hv with h | h
  · exact hlow e h
  · rw [h]
    exact b3

theorem inN_succ (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {β β' x : V}
    (hs : M.IsSucc th β β') (hx : M.InNRaw P th io M.nat j.1 β' x) :
    M.InNRaw P th io M.nat j.1 β x ∨ M.RankIs P io M.nat j.1 β x := by
  obtain ⟨β0, rx, lt, ne⟩ := M.inN_rank hx
  by_cases e : β0 = β
  · rw [e] at rx
    exact Or.inr rx
  · rcases M.wo_total hd.hth (hd.hth.fld _ _ lt).1 (hd.hth.fld _ _ hs.1).1 with h | h
    · exact Or.inl (M.rank_inN rx h e)
    · exact (ne (hd.hth.antisymm _ _ lt (hs.2.2 β0 h (fun e' => e e'.symm)))).elim

/-- The names of rank at most `ν` are generated from the names of rank below `ν` and the
ordinal name of `ν`. -/
theorem gen_self_succ (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {ν ν' o : V}
    (hs : M.IsSucc th ν ν') (ho : M.mem (M.quad j.1 ν q1 o) P) : M.Gen P Sg j ν ν' o := by
  refine (M.gen_iff hd hSg).mpr ⟨(hd.hth.fld _ _ hs.1).2, hs.1, hs.2.1,
    M.rank_inN (M.mark_rank hq ho) hs.1 hs.2.1, fun X b1 b2 b3 hX x hx => ?_⟩
  rcases M.inN_succ hd hs hx with h | h
  · exact b1 x h
  · exact M.closed_rank hd hX hs.1 hs.2.1 ho b2 b1 b3 h

/-- Among the generators of a stage there is a least one. -/
theorem exists_least_gen (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {ν ρ b : V}
    (h : M.Gen P Sg j ν ρ b) :
    ∃ w, M.Gen P Sg j ν ρ w ∧ ∀ b', M.Gen P Sg j ν ρ b' → M.mem (M.op w b') Pr := by
  obtain ⟨S, -, hS0⟩ := M.comp (σW [(20, 7), (164, 5)])
    (Fml.ex 292 (.and (fApp4 20 25 272 291 292) (fApp 164 271 292))) 291 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 25 j.1) 164 Sg) 271 ρ) 272 ν)
  have hS : ∀ x, M.mem x S ↔ M.Gen P Sg j ν ρ x := by
    intro x
    rw [hS0 x]
    simp [Sat, M.sat_ex, M.sat_fApp4', M.sat_fApp', Function.update_apply, Gen]
  obtain ⟨ρb, rb, ltb, -⟩ := M.inN_rank (M.gen_lt hd hSg h).2.2
  obtain ⟨w, ρw, hwS, rw', hρw, hmin⟩ := M.pr_least hd hPr S
    ⟨b, ρb, (hS b).mpr h, rb, (hd.hth.fld _ _ ltb).1⟩
  refine ⟨w, (hS w).mp hwS, fun b' hb' => ?_⟩
  obtain ⟨ρ', r', lt', -⟩ := M.inN_rank (M.gen_lt hd hSg hb').2.2
  exact hmin b' ρ' ((hS b').mpr hb') r' (hd.hth.fld _ _ lt').1

/-- If the names of rank below `β` are generated from the names of rank below `ν` and some
name, then the names of rank at most `β` are generated from the names of rank below `ν` and
the ordinal name of `β`. -/
theorem gen_succ (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) (hq : M.IsMark P th io Nt d j q1)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {ν β β' b o : V}
    (hgen : M.Gen P Sg j ν β b) (hs : M.IsSucc th β β') (ho : M.mem (M.quad j.1 β q1 o) P) :
    M.Gen P Sg j ν β' o := by
  obtain ⟨hνβ, hνne, -⟩ := M.gen_lt hd hSg hgen
  obtain ⟨w, hw, hwmin⟩ := M.exists_least_gen hd hPr hSg hgen
  obtain ⟨y, hy, hySg⟩ := hw
  have hββ := (hd.hth.fld _ _ hs.1).1
  refine (M.gen_iff hd hSg).mpr ⟨(hd.hth.fld _ _ hs.1).2, hd.hth.trans _ _ _ hνβ hs.1, ?_,
    M.rank_inN (M.mark_rank hq ho) hs.1 hs.2.1, fun X b1 b2 b3 hX x hx => ?_⟩
  · intro e
    rw [e] at hνβ
    exact hs.2.1 (hd.hth.antisymm _ _ hs.1 hνβ)
  · have hwX : M.mem w X :=
      (hX.2.2.2.2.2 β o β w y ho b2 hββ hy (M.mem_restr.mpr ⟨hySg, hs.1, hs.2.1⟩)
        (fun β'' b' y' _ _ h1 => h1)
        (fun b' y' hq' hG' => hwmin b' ⟨y', hq', (M.mem_restr.mp hG').1⟩)).2
    have hlow := M.gen_sub hd hSg ⟨y, hy, hySg⟩ hX hs.1 hs.2.1 ho b2 b1 hwX b3
    rcases M.inN_succ hd hs hx with h | h
    · exact hlow x h
    · exact M.closed_rank hd hX hs.1 hs.2.1 ho b2 hlow b3 h

theorem small_mono (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ν ρ ρ' : V}
    (h : M.Small P th Sg j ν ρ) (hle : M.mem (M.op ρ' ρ) th) : M.Small P th Sg j ν ρ' := by
  obtain ⟨ρ2, b, h1, h2⟩ := h
  exact ⟨ρ2, b, hd.hth.trans _ _ _ hle h1, h2⟩

/-- **The least stage that is not `ν`-small is a limit stage above `ν`.** -/
theorem next_lim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) (hq : M.IsMark P th io Nt d j q1)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {ν κ : V} (hκ : M.IsNext P th Sg j ν κ) :
    M.IsLim th κ := by
  obtain ⟨hκκ, hns, hsm⟩ := hκ
  refine ⟨hκκ, fun β hβ hne => ?_⟩
  obtain ⟨ρ2, b, h1, h2⟩ := hsm β hβ hne
  have hρ2 := (hd.hth.fld _ _ h1).2
  -- `ρ₂` is below `κ`
  have lt2 : M.mem (M.op ρ2 κ) th ∧ ρ2 ≠ κ := by
    rcases M.wo_total hd.hth hρ2 hκκ with h | h
    · refine ⟨h, fun e => hns ⟨ρ2, b, ?_, h2⟩⟩
      rw [e]
      exact hκκ
    · exact (hns ⟨ρ2, b, h, h2⟩).elim
  obtain ⟨ρ3, s1, s2, s3, s4⟩ := M.exists_succ_stage hd lt2.1 lt2.2
  obtain ⟨o, ho⟩ := M.exists_mark hd hq hρ2
  have hgen3 := M.gen_succ hd hPr hq hSg h2 ⟨s1, s2, s4⟩ ho
  have hρ3 := (hd.hth.fld _ _ s1).2
  refine ⟨ρ3, hd.hth.trans _ _ _ h1 s1, fun e => ?_, s3, fun e => hns ⟨ρ3, o, ?_, hgen3⟩⟩
  · rw [← e] at s1
    exact s2 ((hd.hth.antisymm _ _ s1 h1).trans e)
  · rw [e]
    exact hκκ

/-- The stage `ν` is below the least stage that is not `ν`-small, if `ν` is not the last
stage. -/
theorem next_gt (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {ν κ ν' : V}
    (hκ : M.IsNext P th Sg j ν κ) (hs : M.IsSucc th ν ν') :
    M.mem (M.op ν κ) th ∧ ν ≠ κ := by
  obtain ⟨hκκ, hns, hsm⟩ := hκ
  obtain ⟨o, ho⟩ := M.exists_mark hd hq (hd.hth.fld _ _ hs.1).1
  have hgen := M.gen_self_succ hd hq hSg hs ho
  rcases M.wo_total hd.hth (hd.hth.fld _ _ hs.1).1 hκκ with h | h
  · refine ⟨h, fun e => hns ⟨ν', o, ?_, hgen⟩⟩
    rw [← e]
    exact hs.1
  · exact (hns ⟨ν', o, hd.hth.trans _ _ _ h hs.1, hgen⟩).elim

end hull2

/-! ## The order collapse of a set of stages -/

/-- One step of the collapse: `y` is the least stage that is not a value of `G`. -/
def CollStep (th O G α y : V) : Prop :=
  M.mem α O ∧ M.mem (M.op y y) th ∧ (∀ β' y', M.mem (M.op β' y') G → ¬ y' = y) ∧
    ∀ y2, M.mem (M.op y2 y2) th → (∀ β' y', M.mem (M.op β' y') G → ¬ y' = y2) →
      M.mem (M.op y y2) th

def collFml : Fml :=
  .and (.mem 4 170) (.and (fApp 22 5 5) (.and (.all 310 (.all 311 (Fml.imp (fApp 6 310 311)
    (.neg (.eq 311 5))))) (.all 312 (Fml.imp (fApp 22 312 312) (Fml.imp (.all 310 (.all 311
    (Fml.imp (fApp 6 310 311) (.neg (.eq 311 312))))) (fApp 22 5 312))))))

theorem sat_collFml (ρ : ℕ → V) : Sat M.mem M.isSet collFml ρ ↔
    M.CollStep (ρ 22) (ρ 170) (ρ 6) (ρ 4) (ρ 5) := by
  simp [collFml, CollStep, Sat, M.sat_imp, M.sat_fApp', Function.update_apply]

/-- `H` is the **order collapse** of the set `O` of stages: it maps each stage in `O` to the
least stage that is not the image of an earlier stage in `O`. -/
def IsColl (th O H : V) : Prop :=
  ∀ β y, M.mem (M.op β y) H ↔ M.mem (M.op β β) th ∧ M.CollStep th O (M.restr th H β) β y

theorem exists_coll {th : V} (hth : M.IsWO th) (O : V) : ∃ H, M.IsColl th O H := by
  obtain ⟨ρ, e22, e170⟩ : ∃ ρ : ℕ → V, ρ 22 = th ∧ ρ 170 = O :=
    ⟨(Function.update (Function.update (fun _ => dflt) 22 th) 170 O), by simp [Function.update_apply]⟩
  exact M.wo_rec hth (fun α y G => M.CollStep th O G α y) collFml [(22, 5), (170, 3)] rfl ρ
    (fun ρ' h => by rw [M.sat_collFml, h 22 (by decide), h 170 (by decide), e22, e170])

section coll

variable {th O H : V}

theorem coll_dom (hH : M.IsColl th O H) {β y : V} (h : M.mem (M.op β y) H) :
    M.mem (M.op β β) th ∧ M.mem β O ∧ M.mem (M.op y y) th := by
  obtain ⟨h1, h2, h3, -⟩ := (hH β y).mp h
  exact ⟨h1, h2, h3⟩

/-- The collapse moves no stage up. -/
theorem coll_le (hth : M.IsWO th) (hH : M.IsColl th O H) {β y : V} (h : M.mem (M.op β y) H) :
    M.mem (M.op y β) th := by
  have hβ := (M.coll_dom hH h).1
  have key := M.wo_ind_fml hth (σW [(22, 5), (171, 5)]) (.all 313 (Fml.imp (fApp 171 250 313) (fApp 22 313 250))) 250 rfl
    (Function.update (Function.update (fun _ => dflt) 22 th) 171 H) (fun α hα ih => ?_) β hβ
  · have key' : ∀ y, M.mem (M.op β y) H → M.mem (M.op y β) th := by
      simpa [Sat, M.sat_imp, M.sat_fApp', Function.update_apply] using key
    exact key' y h
  · have ih' : ∀ β', M.mem (M.op β' α) th → β' ≠ α → ∀ y, M.mem (M.op β' y) H →
        M.mem (M.op y β') th := by
      intro β' h1 h2
      have := ih β' h1 h2
      simpa [Sat, M.sat_imp, M.sat_fApp', Function.update_apply] using this
    have goal : ∀ y, M.mem (M.op α y) H → M.mem (M.op y α) th := by
      intro y hy
      obtain ⟨-, -, -, -, hleast⟩ := (hH α y).mp hy
      refine hleast α hα (fun β' y' hr e => ?_)
      obtain ⟨hm, lt, ne⟩ := M.mem_restr.mp hr
      have := ih' β' lt ne y' hm
      rw [e] at this
      exact ne (hth.antisymm _ _ lt this)
    simpa [Sat, M.sat_imp, M.sat_fApp', Function.update_apply] using goal

theorem coll_fun (hth : M.IsWO th) (hH : M.IsColl th O H) {β y y' : V}
    (h : M.mem (M.op β y) H) (h' : M.mem (M.op β y') H) : y = y' := by
  obtain ⟨-, -, hy, hnot, hleast⟩ := (hH β y).mp h
  obtain ⟨-, -, hy', hnot', hleast'⟩ := (hH β y').mp h'
  exact hth.antisymm _ _ (hleast y' hy' hnot') (hleast' y hy hnot)

theorem coll_tot (hth : M.IsWO th) (hH : M.IsColl th O H) {β : V} (hβ : M.mem (M.op β β) th)
    (hO : M.mem β O) : ∃ y, M.mem (M.op β y) H := by
  obtain ⟨Z, -, hZ0⟩ := M.comp (σW [(6, 5), (22, 5)]) (.and (fApp 22 312 312) (.all 310 (.all 311 (Fml.imp (fApp 6 310 311) (.neg (.eq 311 312)))))) 312 rfl
    (Function.update (Function.update (fun _ => dflt) 6 (M.restr th H β)) 22 th)
  have hZ : ∀ y2, M.mem y2 Z ↔ M.mem (M.op y2 y2) th ∧
      ∀ β' y', M.mem (M.op β' y') (M.restr th H β) → ¬ y' = y2 := by
    intro y2
    rw [hZ0 y2]
    simp [Sat, M.sat_imp, M.sat_fApp', Function.update_apply]
  have hβZ : M.mem β Z := by
    refine (hZ β).mpr ⟨hβ, fun β' y' hr e => ?_⟩
    obtain ⟨hm, lt, ne⟩ := M.mem_restr.mp hr
    have := M.coll_le hth hH hm
    rw [e] at this
    exact ne (hth.antisymm _ _ lt this)
  obtain ⟨y0, hy0Z, hy0, hmin⟩ := hth.least Z ⟨β, hβZ, hβ⟩
  obtain ⟨-, hnot⟩ := (hZ y0).mp hy0Z
  exact ⟨y0, (hH β y0).mpr ⟨hβ, hO, hy0, hnot,
    fun y2 hy2 h2 => hmin y2 ((hZ y2).mpr ⟨hy2, h2⟩) hy2⟩⟩

/-- The collapse is strictly increasing. -/
theorem coll_mono (hth : M.IsWO th) (hH : M.IsColl th O H) {β1 β2 y1 y2 : V}
    (h1 : M.mem (M.op β1 y1) H) (h2 : M.mem (M.op β2 y2) H) (hlt : M.mem (M.op β1 β2) th)
    (hne : β1 ≠ β2) : M.mem (M.op y1 y2) th ∧ y1 ≠ y2 := by
  obtain ⟨-, -, hy1, hnot1, hleast1⟩ := (hH β1 y1).mp h1
  obtain ⟨-, -, hy2, hnot2, hleast2⟩ := (hH β2 y2).mp h2
  refine ⟨hleast1 y2 hy2 (fun β' y' hr => ?_), hnot2 β1 y1 (M.mem_restr.mpr ⟨h1, hlt, hne⟩)⟩
  obtain ⟨hm, lt, ne⟩ := M.mem_restr.mp hr
  refine hnot2 β' y' (M.mem_restr.mpr ⟨hm, hth.trans _ _ _ lt hlt, fun e => ?_⟩)
  rw [e] at lt
  exact ne (e.trans (hth.antisymm _ _ lt hlt))

theorem coll_le_iff (hth : M.IsWO th) (hH : M.IsColl th O H) {β1 β2 y1 y2 : V}
    (h1 : M.mem (M.op β1 y1) H) (h2 : M.mem (M.op β2 y2) H) :
    M.mem (M.op β1 β2) th ↔ M.mem (M.op y1 y2) th := by
  have f1 := (M.coll_dom hH h1).1
  have f2 := (M.coll_dom hH h2).1
  constructor
  · intro h
    by_cases e : β1 = β2
    · rw [e] at h1
      rw [M.coll_fun hth hH h1 h2]
      exact (M.coll_dom hH h2).2.2
    · exact (M.coll_mono hth hH h1 h2 h e).1
  · intro h
    rcases M.wo_total hth f1 f2 with h' | h'
    · exact h'
    · by_cases e : β2 = β1
      · rw [e]
        exact f1
      · obtain ⟨l, ne⟩ := M.coll_mono hth hH h2 h1 h' e
        exact (ne (hth.antisymm _ _ l h)).elim

theorem coll_inj (hth : M.IsWO th) (hH : M.IsColl th O H) {β1 β2 y : V}
    (h1 : M.mem (M.op β1 y) H) (h2 : M.mem (M.op β2 y) H) : β1 = β2 :=
  hth.antisymm _ _ ((M.coll_le_iff hth hH h1 h2).mpr (M.coll_dom hH h1).2.2)
    ((M.coll_le_iff hth hH h2 h1).mpr (M.coll_dom hH h1).2.2)

/-- The values of the collapse form an initial segment. -/
theorem coll_range (hth : M.IsWO th) (hH : M.IsColl th O H) {β y γ : V}
    (h : M.mem (M.op β y) H) (hγ : M.mem (M.op γ y) th) (hne : γ ≠ y) :
    ∃ β', M.mem (M.op β' β) th ∧ β' ≠ β ∧ M.mem (M.op β' γ) H := by
  obtain ⟨-, -, hy, hnot, hleast⟩ := (hH β y).mp h
  by_contra hcon
  refine hne (hth.antisymm _ _ hγ (hleast γ (hth.fld _ _ hγ).1 (fun β' y' hr e => hcon ?_)))
  obtain ⟨hm, lt, ne⟩ := M.mem_restr.mp hr
  rw [e] at hm
  exact ⟨β', lt, ne, hm⟩

/-- The collapse is the identity on an initial segment contained in the set. -/
theorem coll_id (hth : M.IsWO th) (hH : M.IsColl th O H) {β : V} (hβ : M.mem (M.op β β) th)
    (hall : ∀ β', M.mem (M.op β' β) th → M.mem β' O) : M.mem (M.op β β) H := by
  have key := M.wo_ind_fml hth (σW [(22, 5), (170, 3), (171, 5)]) (Fml.imp (.all 313 (Fml.imp (fApp 22 313 250) (.mem 313 170))) (fApp 171 250 250)) 250 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 22 th) 170 O) 171 H) (fun α hα ih => ?_) β hβ
  · have key' : (∀ β', M.mem (M.op β' β) th → M.mem β' O) → M.mem (M.op β β) H := by
      simpa [Sat, M.sat_imp, M.sat_fApp', Function.update_apply] using key
    exact key' hall
  · have ih' : ∀ β', M.mem (M.op β' α) th → β' ≠ α →
        (∀ β'', M.mem (M.op β'' β') th → M.mem β'' O) → M.mem (M.op β' β') H := by
      intro β' h1 h2
      have := ih β' h1 h2
      simpa [Sat, M.sat_imp, M.sat_fApp', Function.update_apply] using this
    have goal : (∀ β', M.mem (M.op β' α) th → M.mem β' O) → M.mem (M.op α α) H := by
      intro hallα
      obtain ⟨y, hy⟩ := M.coll_tot hth hH hα (hallα α hα)
      have hle := M.coll_le hth hH hy
      by_cases e : y = α
      · rw [e] at hy
        exact hy
      · exfalso
        have hyy := ih' y hle e (fun β'' h'' => hallα β'' (hth.trans _ _ _ h'' hle))
        obtain ⟨-, -, -, hnot, -⟩ := (hH α y).mp hy
        exact hnot y y (M.mem_restr.mpr ⟨hyy, hle, e⟩) rfl
    simpa [Sat, M.sat_imp, M.sat_fApp', Function.update_apply] using goal

end coll

/-! ## The collapsing map on names -/

/-- One step of the recursion for the collapsing map: `y` is the pair of a name `n` of rank
`β` and a name `n'` of rank the collapse of `β`, with the same formula, such that the values
of the parameters correspond: both are the default name, or they are related by `G`. -/
def PiStep (P th io nat Nt j d ad H G δ β y : V) : Prop :=
  ∃ n n' c u u' βb, M.mem (M.quad j n n' y) P ∧ M.mem (M.op β δ) th ∧ ¬ β = δ ∧
    M.mem (M.op β βb) H ∧ M.NameR P io nat j n β c u ∧ M.NameR P io nat j n' βb c u' ∧
    ∀ i, M.mem i nat → (∃ x, M.mem x nat ∧ M.mem (M.trip i x c) ad) → ∃ e e',
      M.ValRaw P th io nat Nt j d β u i e ∧ M.ValRaw P th io nat Nt j d βb u' i e' ∧
      ((e = d ∧ e' = d) ∨ ∃ β1 y1, M.mem (M.quad j e e' y1) P ∧ M.mem (M.op β1 y1) G)

def piFml : Fml :=
  Fml.ex 320 (Fml.ex 321 (Fml.ex 322 (Fml.ex 323 (Fml.ex 324 (Fml.ex 325 (.and (fApp4 20 25 320
    321 5) (.and (fApp 22 4 271) (.and (.neg (.eq 4 271)) (.and (fApp 171 4 325) (.and (Fml.ex
    262 (Fml.ex 263 (.and (fApp4 20 25 4 263 320) (.and (fApp4 20 25 262 323 263) (.and (.mem
    322 27) (fApp 24 322 262)))))) (.and (Fml.ex 262 (Fml.ex 263 (.and (fApp4 20 25 325 263 321)
    (.and (fApp4 20 25 262 324 263) (.and (.mem 322 27) (fApp 24 322 262)))))) (.all 326
    (Fml.imp (.mem 326 27) (Fml.imp (fLeN 326 322) (Fml.ex 327 (Fml.ex 328 (.and (fVal 4 323 326
    327) (.and (fVal 325 324 326 328) (Fml.or (.and (.eq 327 26) (.eq 328 26)) (Fml.ex 329
    (Fml.ex 330 (.and (fApp4 20 25 327 328 330) (fApp 6 329 330)))))))))))))))))))))))

theorem sat_piFml (ρ : ℕ → V) : Sat M.mem M.isSet piFml ρ ↔
    M.PiStep (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 171) (ρ 6) (ρ 271) (ρ 4)
      (ρ 5) := by
  simp [piFml, PiStep, NameR, Sat, M.sat_imp, M.sat_or, M.sat_ex, M.sat_fVal, M.sat_fLeN,
    M.sat_fApp', M.sat_fApp4', Function.update_apply]

/-- `PiS` is the record of the **collapsing map on names** for the collapse `H` of stages. -/
def IsPi (P th io Nt d H PiS δ : V) (j : M.Num) : Prop :=
  ∀ β y, M.mem (M.op β y) PiS ↔ M.mem (M.op β β) th ∧
    M.PiStep P th io M.nat Nt j.1 d M.adG H (M.restr th PiS β) δ β y

theorem exists_pi {th : V} (hth : M.IsWO th) (P io Nt d H δ : V) (j : M.Num) :
    ∃ PiS, M.IsPi P th io Nt d H PiS δ j := by
  obtain ⟨ρ, e20, e22, e23, e24, e25, e26, e27, e28, e171, e271⟩ :
      ∃ ρ : ℕ → V, ρ 20 = P ∧ ρ 22 = th ∧ ρ 23 = Nt ∧ ρ 24 = io ∧ ρ 25 = j.1 ∧ ρ 26 = d ∧
        ρ 27 = M.nat ∧ ρ 28 = M.adG ∧ ρ 171 = H ∧ ρ 271 = δ :=
    ⟨(Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 171 H) 271 δ),
      by simp [Function.update_apply]⟩
  exact M.wo_rec hth (fun α y G => M.PiStep P th io M.nat Nt j.1 d M.adG H G δ α y) piFml
    [(20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7), (171, 5)] rfl ρ
    (fun ρ' h => by
      rw [M.sat_piFml, h 20 (by decide), h 22 (by decide), h 23 (by decide), h 24 (by decide),
        h 25 (by decide), h 26 (by decide), h 27 (by decide), h 28 (by decide),
        h 171 (by decide), h 271 (by decide), e20, e22, e23, e24, e25, e26, e27, e28, e171, e271])

/-- The name `n'` is an image of the name `n` under the collapsing map. -/
def PiRel (P PiS : V) (j : M.Num) (n n' : V) : Prop :=
  ∃ β y, M.mem (M.quad j.1 n n' y) P ∧ M.mem (M.op β y) PiS

/-- **The data of a condensation**: a set `N` of names of rank below `δ` that contains the
default name and is closed under the rules, the set `Oc` of the stages whose ordinal names
are in `N` together with `δ`, its collapse `H`, and the collapsing map `PiS` on names. The set
of numerals of the hierarchy is empty, so the relation symbol `1` is never true. -/
structure CondData (R P th io Nt nle p F d tp qo Nu Pr : V) (m j : M.Num)
    (N δ Oc H PiS G ν q1 : V) : Prop where
  hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j
  hPr : M.IsPrec P th io Nt d Pr j
  hq : M.IsMark P th io Nt d j q1
  hNu : ∀ k o, ¬ M.mem (M.op k o) Nu
  hδ : M.mem (M.op δ δ) th
  hcl : M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr G N δ ν
  hsub : ∀ x, M.mem x N → M.InNRaw P th io M.nat j.1 δ x
  hdN : M.mem d N
  hO : ∀ β, M.mem β Oc ↔ (β = δ ∨ ∃ o, M.mem (M.quad j.1 β q1 o) P ∧ M.mem o N)
  hH : M.IsColl th Oc H
  hPi : M.IsPi P th io Nt d H PiS δ j

section cond1

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {N δ Oc H PiS G ν : V}
variable {q1 : V}

theorem exists_condData (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) (hq : M.IsMark P th io Nt d j q1)
    (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu) (hδ : M.mem (M.op δ δ) th)
    (hcl : M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr G N δ ν)
    (hsub : ∀ x, M.mem x N → M.InNRaw P th io M.nat j.1 δ x) (hdN : M.mem d N) :
    ∃ Oc H PiS, M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1 := by
  obtain ⟨Oc, -, hO0⟩ := M.comp (σW [(20, 7), (169, 3)]) (Fml.or (.eq 332 271) (Fml.ex 282 (.and (fApp4 20 25 332 160 282) (.mem 282 169)))) 332 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 25 j.1) 160 q1) 169 N) 271 δ)
  have hO : ∀ β, M.mem β Oc ↔ (β = δ ∨ ∃ o, M.mem (M.quad j.1 β q1 o) P ∧ M.mem o N) := by
    intro β
    rw [hO0 β]
    simp [Sat, M.sat_or, M.sat_ex, M.sat_fApp4', Function.update_apply]
  obtain ⟨H, hH⟩ := M.exists_coll hd.hth Oc
  obtain ⟨PiS, hPi⟩ := M.exists_pi hd.hth P io Nt d H δ j
  exact ⟨Oc, H, PiS, ⟨hd, hPr, hq, hNu, hδ, hcl, hsub, hdN, hO, hH, hPi⟩⟩

/-- The rank of a member of `N` is a stage below `δ` whose ordinal name is in `N`. -/
theorem cond_rank (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1)
    {n β : V} (hn : M.mem n N) (rn : M.RankIs P io M.nat j.1 β n) :
    M.mem (M.op β δ) th ∧ β ≠ δ ∧ M.mem β Oc ∧ ∃ o, M.mem (M.quad j.1 β q1 o) P ∧ M.mem o N := by
  obtain ⟨β', rn', lt, ne⟩ := M.inN_rank (cd.hsub n hn)
  have e := M.rank_unique cd.hd rn rn'
  rw [← e] at lt ne
  obtain ⟨o, ho⟩ := M.exists_mark cd.hd cd.hq (cd.hd.hth.fld _ _ lt).1
  have hoN := cd.hcl.1 n β o hn rn ho
  exact ⟨lt, ne, (cd.hO β).mpr (Or.inr ⟨o, ho, hoN⟩), o, ho, hoN⟩

theorem piStep_name (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {G' β y n n' : V}
    (h : M.PiStep P th io M.nat Nt j.1 d M.adG H G' δ β y) (hy : M.mem (M.quad j.1 n n' y) P) :
    M.RankIs P io M.nat j.1 β n := by
  obtain ⟨n1, n1', c, u, u', βb, hq1, -, -, -, hn1, -⟩ := h
  obtain ⟨e1, -⟩ := hd.hP.inj _ _ _ _ _ _ hq1 hy
  rw [e1] at hn1
  exact M.nameR_rank hn1

/-- The collapsing map, unfolded. -/
theorem pi_unpack (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1)
    {n n' : V} (h : M.PiRel P PiS j n n') :
    ∃ (β βb : V) (c : M.Num) (u u' : V), M.mem (M.op β δ) th ∧ β ≠ δ ∧ M.mem (M.op β βb) H ∧
      M.NameOf P io j n β c u ∧ M.NameOf P io j n' βb c u' ∧
      ∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β u i.1 e ∧
        M.ValRaw P th io M.nat Nt j.1 d βb u' i.1 e' ∧
        ((e = d ∧ e' = d) ∨ (M.InNRaw P th io M.nat j.1 β e ∧ M.PiRel P PiS j e e')) := by
  obtain ⟨β, y, hy, hm⟩ := h
  obtain ⟨hβ, n1, n1', c, u, u', βb, hq1, lt, ne, hH, hn1, hn1', hv⟩ := (cd.hPi β y).mp hm
  obtain ⟨e1, e2⟩ := cd.hd.hP.inj _ _ _ _ _ _ hq1 hy
  rw [e1] at hn1
  rw [e2] at hn1'
  have hc : M.mem c M.nat := by
    obtain ⟨f, q, -, -, h3, -⟩ := hn1
    exact h3
  refine ⟨β, βb, ⟨c, hc⟩, u, u', lt, ne, hH, (M.nameR_iff ⟨c, hc⟩).mp hn1,
    (M.nameR_iff ⟨c, hc⟩).mp hn1', fun i hi => ?_⟩
  obtain ⟨e, e', v, v', hrel⟩ := hv i.1 i.2 ((M.leRaw_iff M.adG_spec i ⟨c, hc⟩).mpr hi)
  refine ⟨e, e', v, v', ?_⟩
  rcases hrel with h1 | ⟨β1, y1, hq2, hG⟩
  · exact Or.inl h1
  · obtain ⟨hm1, lt1, ne1⟩ := M.mem_restr.mp hG
    have r1 := M.piStep_name cd.hd ((cd.hPi β1 y1).mp hm1).2 hq2
    exact Or.inr ⟨M.rank_inN r1 lt1 ne1, β1, y1, hq2, hm1⟩

/-- The rank of a name in the domain of the collapsing map, and of its image. -/
theorem pi_rank (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1)
    {n n' : V} (h : M.PiRel P PiS j n n') :
    ∃ β βb, M.RankIs P io M.nat j.1 β n ∧ M.RankIs P io M.nat j.1 βb n' ∧ M.mem (M.op β βb) H ∧
      M.mem (M.op β δ) th ∧ β ≠ δ := by
  obtain ⟨β, βb, c, u, u', lt, ne, hH, hn, hn', -⟩ := M.pi_unpack cd h
  exact ⟨β, βb, M.nameOf_rank hn, M.nameOf_rank hn', hH, lt, ne⟩

/-- The collapsing map, introduced. -/
theorem pi_intro (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1)
    {n n' β βb u u' : V} {c : M.Num} (lt : M.mem (M.op β δ) th) (ne : β ≠ δ)
    (hH : M.mem (M.op β βb) H) (hn : M.NameOf P io j n β c u) (hn' : M.NameOf P io j n' βb c u')
    (hv : ∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β u i.1 e ∧
        M.ValRaw P th io M.nat Nt j.1 d βb u' i.1 e' ∧
        ((e = d ∧ e' = d) ∨ (M.InNRaw P th io M.nat j.1 β e ∧ M.PiRel P PiS j e e'))) :
    M.PiRel P PiS j n n' := by
  have hnR : M.mem (M.op j.1 n) R := by
    obtain ⟨f, q, h1, -⟩ := hn
    exact (cd.hd.hP.dom _ _ _ _ h1).2.2.2
  have hn'R : M.mem (M.op j.1 n') R := by
    obtain ⟨f, q, h1, -⟩ := hn'
    exact (cd.hd.hP.dom _ _ _ _ h1).2.2.2
  obtain ⟨y, hy⟩ := cd.hd.hP.tot j cd.hd.hj n n' hnR hn'R
  refine ⟨β, y, hy, (cd.hPi β y).mpr ⟨(cd.hd.hth.fld _ _ lt).1, n, n', c.1, u, u', βb, hy, lt, ne,
    hH, (M.nameR_iff c).mpr hn, (M.nameR_iff c).mpr hn', fun i hi hle => ?_⟩⟩
  obtain ⟨e, e', v, v', hrel⟩ := hv ⟨i, hi⟩ ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ c).mp hle)
  refine ⟨e, e', v, v', ?_⟩
  rcases hrel with h1 | ⟨heN, β1, y1, hq2, hm1⟩
  · exact Or.inl h1
  · obtain ⟨β2, r2, lt2, ne2⟩ := M.inN_rank heN
    have r1 := M.piStep_name cd.hd ((cd.hPi β1 y1).mp hm1).2 hq2
    have e12 := M.rank_unique cd.hd r1 r2
    rw [← e12] at lt2 ne2
    exact Or.inr ⟨β1, y1, hq2, M.mem_restr.mpr ⟨hm1, lt2, ne2⟩⟩

end cond1

/-! ## The collapsing map: domain, totality, monotonicity -/

/-- `PiRel` as a formula, for the names `x`, `y`; the record `PiS` is the name `167`. -/
def fPi (x y : ℕ) : Fml :=
  Fml.ex 334 (Fml.ex 333 (.and (fApp4 20 25 x y 333) (fApp 167 334 333)))

theorem sat_fPi {x y : ℕ} (ρ : ℕ → V) (hx : 199 < x) (hy : 199 < y) (hx1 : x ≠ 333)
    (hx2 : x ≠ 334) (hy1 : y ≠ 333) (hy2 : y ≠ 334) :
    Sat M.mem M.isSet (fPi x y) ρ ↔
      ∃ β z, M.mem (M.quad (ρ 25) (ρ x) (ρ y) z) (ρ 20) ∧ M.mem (M.op β z) (ρ 167) := by
  have b1 : x < 30 ∨ 59 < x := by omega
  have b2 : y < 30 ∨ 59 < y := by omega
  simp [fPi, Sat, M.sat_ex, M.sat_fApp4', M.sat_fApp', Function.update_apply, hx1, hx2, hy1, hy2,
    b1, b2]

section cond2

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {N δ Oc H PiS G ν : V}
variable {q1 : V}

theorem rank_rung (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {β a : V}
    (h : M.RankIs P io M.nat j.1 β a) : M.mem (M.op j.1 a) R := by
  obtain ⟨f, u, q, h1, -⟩ := h
  exact (hd.hP.dom _ _ _ _ h1).2.2.2

theorem leV_iff' (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {β x y : V} (rx : M.RankIs P io M.nat j.1 β x)
    (hβ : M.mem (M.op β β) th) : M.LeV Pr x y ↔ M.mem (M.op x y) Pr := by
  constructor
  · rintro (h | h)
    · rw [← h]
      exact M.pr_refl hd hPr rx hβ
    · exact h
  · exact fun h => Or.inr h

/-- **The domain of the collapsing map is contained in `N`.** -/
theorem pi_mem (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {n n' : V}
    (h : M.PiRel P PiS j n n') : M.mem n N := by
  obtain ⟨β, βb, rn, -, -, lt, -⟩ := M.pi_rank cd h
  have hβ := (cd.hd.hth.fld _ _ lt).1
  have hsat : ∀ α, Sat M.mem M.isSet (.all 320 (.all 321 (Fml.imp (fRank 250 320) (Fml.imp (fPi 320 321) (.mem 320 169)))))
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 167 PiS) 169 N) 250 α) ↔
      ∀ n n', M.RankIs P io M.nat j.1 α n → M.PiRel P PiS j n n' → M.mem n N := by
    intro α
    simp [Sat, M.sat_imp, M.sat_fRank, M.sat_fPi, Function.update_apply, PiRel]
  have key := M.wo_ind_fml cd.hd.hth (σW [(20, 7), (24, 5), (27, 3), (167, 5), (169, 3)])
    (.all 320 (.all 321 (Fml.imp (fRank 250 320) (Fml.imp (fPi 320 321) (.mem 320 169))))) 250 rfl (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 167 PiS) 169 N) (fun α hα ih => ?_) β hβ
  · exact (hsat β).mp key n n' rn h
  · rw [hsat α]
    have ih' : ∀ β', M.mem (M.op β' α) th → β' ≠ α → ∀ n n', M.RankIs P io M.nat j.1 β' n →
        M.PiRel P PiS j n n' → M.mem n N := fun β' h1 h2 => (hsat β').mp (ih β' h1 h2)
    intro n n' rn h
    obtain ⟨β1, βb, c, u, u', lt, ne, hH, hn, hn', hv⟩ := M.pi_unpack cd h
    have e := M.rank_unique cd.hd (M.nameOf_rank hn) rn
    subst e
    rcases (cd.hO β1).mp (M.coll_dom cd.hH hH).2.1 with e | ⟨o, ho, hoN⟩
    · exact (ne e).elim
    refine cd.hcl.2.2.1 n β1 c.1 u o ho hoN lt ne ((M.nameR_iff c).mpr hn)
      (fun i e hi hle hv' => ?_)
    obtain ⟨e1, e1', v1, -, hrel⟩ := hv ⟨i, hi⟩ ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ c).mp hle)
    rw [M.val_unique cd.hd hv' v1]
    rcases hrel with ⟨h1, -⟩ | ⟨heN, hpi⟩
    · rw [h1]
      exact cd.hdN
    · obtain ⟨β2, r2, lt2, ne2⟩ := M.inN_rank heN
      exact ih' β2 lt2 ne2 e1 e1' r2 hpi

/-- **The collapsing map is defined on all of `N`.** -/
theorem pi_tot (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {n : V}
    (hnN : M.mem n N) : ∃ n', M.PiRel P PiS j n n' := by
  obtain ⟨β, rn, lt, -⟩ := M.inN_rank (cd.hsub n hnN)
  have hβ := (cd.hd.hth.fld _ _ lt).1
  have hsat : ∀ α, Sat M.mem M.isSet (.all 320 (Fml.imp (fRank 250 320) (Fml.imp (.mem 320 169) (Fml.ex 321 (fPi 320 321)))))
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 167 PiS) 169 N) 250 α) ↔
      ∀ n, M.RankIs P io M.nat j.1 α n → M.mem n N → ∃ n', M.PiRel P PiS j n n' := by
    intro α
    simp [Sat, M.sat_imp, M.sat_ex, M.sat_fRank, M.sat_fPi, Function.update_apply, PiRel]
  have key := M.wo_ind_fml cd.hd.hth (σW [(20, 7), (24, 5), (27, 3), (167, 5), (169, 3)])
    (.all 320 (Fml.imp (fRank 250 320) (Fml.imp (.mem 320 169) (Fml.ex 321 (fPi 320 321))))) 250 rfl (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 167 PiS) 169 N) (fun α hα ih => ?_) β hβ
  · exact (hsat β).mp key n rn hnN
  · rw [hsat α]
    have ih' : ∀ β', M.mem (M.op β' α) th → β' ≠ α → ∀ n, M.RankIs P io M.nat j.1 β' n →
        M.mem n N → ∃ n', M.PiRel P PiS j n n' := fun β' h1 h2 => (hsat β').mp (ih β' h1 h2)
    intro n rn hnN
    obtain ⟨c, u, hname⟩ := M.rank_nameOf rn
    obtain ⟨lt, ne, hαO, o, ho, hoN⟩ := M.cond_rank cd hnN rn
    obtain ⟨αb, hH⟩ := M.coll_tot cd.hd.hth cd.hH hα hαO
    obtain ⟨g, -, hg0⟩ := M.comp
      (σW [(0, 4), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (167, 5)])
      (Fml.ex 326 (Fml.ex 328 (.and (fPr 0 326 328) (.and (.mem 326 27) (Fml.ex 327 (.and (fVal 250 323 326 327) (Fml.or (.and (.eq 327 26) (.eq 328 26)) (.and (Fml.ex 65 (.and (.eq 65 250) (fInN 327))) (fPi 327 328))))))))) 0 rfl
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 167 PiS) 250 α) 323 u)
    have hg1 : ∀ q, M.mem q g ↔ ∃ i e', q = M.op i e' ∧ M.mem i M.nat ∧
        ∃ e, M.ValRaw P th io M.nat Nt j.1 d α u i e ∧
          ((e = d ∧ e' = d) ∨ (M.InNRaw P th io M.nat j.1 α e ∧ M.PiRel P PiS j e e')) := by
      intro q
      rw [hg0 q]
      simp [Sat, M.sat_or, M.sat_ex, M.sat_fPr', M.sat_fVal, M.sat_fInN, M.sat_fPi,
        Function.update_apply, PiRel]
    have hg : ∀ i e', M.mem (M.op i e') g ↔ M.mem i M.nat ∧
        ∃ e, M.ValRaw P th io M.nat Nt j.1 d α u i e ∧
          ((e = d ∧ e' = d) ∨ (M.InNRaw P th io M.nat j.1 α e ∧ M.PiRel P PiS j e e')) := by
      intro i e'
      constructor
      · intro h
        obtain ⟨i', e'', eq, h'⟩ := (hg1 _).mp h
        obtain ⟨e1, e2⟩ := M.op_inj eq
        rw [e1, e2]
        exact h'
      · intro h
        exact (hg1 _).mpr ⟨i, e', rfl, h⟩
    obtain ⟨u', hu'R, hcode⟩ := M.seq_code cd.hd.hP cd.hd.hj ⟨d, M.d_rung cd.hd⟩ cd.hd.nt_zero
      cd.hd.nt_succ (c + 1) g (fun k hk => by
        obtain ⟨e, ve⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d)
          (j := j) α u k.1
        by_cases hN : M.InNRaw P th io M.nat j.1 α e
        · have heN : M.mem e N := cd.hcl.2.1 n α c.1 u k.1 e hnN ((M.nameR_iff c).mpr hname) k.2
            ((M.leRaw_iff M.adG_spec k c).mpr (M.le_of_succ_le_succ hk)) ve
          obtain ⟨β1, r1, lt1, ne1⟩ := M.inN_rank hN
          obtain ⟨e', hpi⟩ := ih' β1 lt1 ne1 e r1 heN
          obtain ⟨-, β1b, -, r1', -⟩ := M.pi_rank cd hpi
          exact ⟨e', M.rank_rung cd.hd r1', (hg k.1 e').mpr ⟨k.2, e, ve, Or.inr ⟨hN, hpi⟩⟩⟩
        · have hed : e = d := (M.val_cases ve).resolve_left hN
          exact ⟨d, M.d_rung cd.hd, (hg k.1 d).mpr ⟨k.2, e, ve, Or.inl ⟨hed, rfl⟩⟩⟩)
    obtain ⟨n', hn'⟩ := M.nameOf_exists cd.hd (M.coll_dom cd.hH hH).2.2 hu'R c
    refine ⟨n', M.pi_intro cd lt ne hH hname hn' (fun i hi => ?_)⟩
    obtain ⟨a, hga, hnt⟩ := hcode i (add_le_add hi (le_refl 1))
    obtain ⟨-, e, ve, hrel⟩ := (hg i.1 a).mp hga
    rcases hrel with ⟨hed, had⟩ | ⟨heN, hpi⟩
    · rw [had] at hnt
      refine ⟨e, d, ve, ?_, Or.inl ⟨hed, rfl⟩⟩
      rcases M.val_of_nth cd.hd (α := αb) hnt with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h
    · obtain ⟨β1, β1b, r1, r1', hH1, -, -⟩ := M.pi_rank cd hpi
      obtain ⟨β2, r2, lt2, ne2⟩ := M.inN_rank heN
      have e12 := M.rank_unique cd.hd r1 r2
      rw [← e12] at lt2 ne2
      have hm := M.coll_mono cd.hd.hth cd.hH hH1 hH lt2 ne2
      exact ⟨e, a, ve, Or.inl ⟨hnt, M.rank_inN r1' hm.1 hm.2⟩, Or.inr ⟨heN, hpi⟩⟩

/-- The default name is its own image. -/
theorem pi_dd (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) :
    M.PiRel P PiS j d d := by
  obtain ⟨α0, f0, u0, q0, k1, k2, ⟨k, hk⟩, hleast⟩ := cd.hd.d_spec
  have hkN := (cd.hd.io_dom _ _ hk).1
  have hnd : M.NameOf P io j d α0 ⟨k, hkN⟩ u0 := ⟨f0, q0, k1, k2, hk⟩
  obtain ⟨lt, ne, hαO, -⟩ := M.cond_rank cd cd.hdN (M.nameOf_rank hnd)
  have hα0 := (cd.hd.hth.fld _ _ lt).1
  have hH : M.mem (M.op α0 α0) H := by
    refine M.coll_id cd.hd.hth cd.hH hα0 (fun β' h => ?_)
    rw [cd.hd.hth.antisymm _ _ h (hleast β' (cd.hd.hth.fld _ _ h).1)]
    exact hαO
  refine M.pi_intro cd lt ne hH hnd hnd (fun i _ => ?_)
  obtain ⟨e, ve⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j)
    α0 u0 i.1
  have hed : e = d := (M.val_cases ve).resolve_left (fun h => M.no_inN_least cd.hd hleast h)
  rw [hed] at ve
  exact ⟨d, d, ve, ve, Or.inl ⟨rfl, rfl⟩⟩

/-- A lexicographic comparison passes along a relation between the values that respects
the order. -/
theorem lex_transfer (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    {β βb u1 u2 u1' u2' : V} {c : M.Num} (Rel : V → V → Prop)
    (h1 : ∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β u1 i.1 e ∧
      M.ValRaw P th io M.nat Nt j.1 d βb u1' i.1 e' ∧ Rel e e')
    (h2 : ∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β u2 i.1 e ∧
      M.ValRaw P th io M.nat Nt j.1 d βb u2' i.1 e' ∧ Rel e e')
    (hrel : ∀ x x' y y', Rel x x' → Rel y y' → (M.LeV Pr x y ↔ M.LeV Pr x' y'))
    (h : M.LexLt P th io Nt d Pr j β c u2 u1) : M.LexLt P th io Nt d Pr j βb c u2' u1' := by
  obtain ⟨i, hi, e', e, v', v, l1, l2, hall⟩ := h
  obtain ⟨a, a', w, w', ra⟩ := h2 i hi
  obtain ⟨b, b', x, x', rb⟩ := h1 i hi
  rw [M.val_unique hd v' w] at l1 l2
  rw [M.val_unique hd v x] at l1 l2
  refine ⟨i, hi, a', b', w', x', (hrel _ _ _ _ ra rb).mp l1,
    fun hl => l2 ((hrel _ _ _ _ rb ra).mpr hl), fun i' hi' => ?_⟩
  obtain ⟨g', g, y', y, m1, m2⟩ := hall i' hi'
  have hi'c : i' ≤ c := le_trans (le_trans (M.le_add_one i') hi') hi
  obtain ⟨p1, p1', z, z', rp⟩ := h2 i' hi'c
  obtain ⟨q1, q1', s, s', rq⟩ := h1 i' hi'c
  rw [M.val_unique hd y' z, M.val_unique hd y s] at m1 m2
  exact ⟨p1', q1', z', s', (hrel _ _ _ _ rp rq).mp m1, (hrel _ _ _ _ rq rp).mp m2⟩

/-- The image of a name of rank below `ρ` has rank below the collapse of `ρ`. -/
theorem pi_inN (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {n n' ρ ρb : V}
    (h : M.PiRel P PiS j n n') (hn : M.InNRaw P th io M.nat j.1 ρ n)
    (hH : M.mem (M.op ρ ρb) H) : M.InNRaw P th io M.nat j.1 ρb n' := by
  obtain ⟨β1, β1b, r1, r1', hH1, -, -⟩ := M.pi_rank cd h
  obtain ⟨β2, r2, lt2, ne2⟩ := M.inN_rank hn
  have e12 := M.rank_unique cd.hd r1 r2
  rw [← e12] at lt2 ne2
  have hm := M.coll_mono cd.hd.hth cd.hH hH1 hH lt2 ne2
  exact M.rank_inN r1' hm.1 hm.2

/-- **The collapsing map preserves the order of the names**, in both directions. -/
theorem pi_pr (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {n1 n2 n1' n2' : V}
    (p1 : M.PiRel P PiS j n1 n1') (p2 : M.PiRel P PiS j n2 n2') :
    M.mem (M.op n1 n2) Pr ↔ M.mem (M.op n1' n2') Pr := by
  have hsat : ∀ α, Sat M.mem M.isSet (.all 320 (.all 335 (.all 321 (.all 336 (Fml.imp (Fml.ex 65 (.and (.eq 65 250) (fInN 320))) (Fml.imp (Fml.ex 65 (.and (.eq 65 250) (fInN 335))) (Fml.imp (fPi 320 321) (Fml.imp (fPi 335 336) (Fml.iff (fApp 162 320 335) (fApp 162 321 336))))))))))
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 167 PiS) 169 N) 162 Pr) 250 α) ↔
      ∀ n1 n2 n1' n2', M.InNRaw P th io M.nat j.1 α n1 → M.InNRaw P th io M.nat j.1 α n2 →
        M.PiRel P PiS j n1 n1' → M.PiRel P PiS j n2 n2' →
        (M.mem (M.op n1 n2) Pr ↔ M.mem (M.op n1' n2') Pr) := by
    intro α
    simp [Sat, M.sat_imp, M.sat_iff, M.sat_ex, M.sat_fInN, M.sat_fApp', M.sat_fPi,
      Function.update_apply, PiRel]
  have key := M.wo_ind_fml cd.hd.hth
    (σW [(20, 7), (22, 5), (24, 5), (27, 3), (162, 5), (167, 5), (169, 3)])
    (.all 320 (.all 335 (.all 321 (.all 336 (Fml.imp (Fml.ex 65 (.and (.eq 65 250) (fInN 320))) (Fml.imp (Fml.ex 65 (.and (.eq 65 250) (fInN 335))) (Fml.imp (fPi 320 321) (Fml.imp (fPi 335 336) (Fml.iff (fApp 162 320 335) (fApp 162 321 336)))))))))) 250 rfl (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 167 PiS) 169 N) 162 Pr) (fun α hα ih => ?_) δ cd.hδ
  · exact (hsat δ).mp key n1 n2 n1' n2' (cd.hsub _ (M.pi_mem cd p1)) (cd.hsub _ (M.pi_mem cd p2))
      p1 p2
  · rw [hsat α]
    have ih' : ∀ β', M.mem (M.op β' α) th → β' ≠ α → ∀ n1 n2 n1' n2',
        M.InNRaw P th io M.nat j.1 β' n1 → M.InNRaw P th io M.nat j.1 β' n2 →
        M.PiRel P PiS j n1 n1' → M.PiRel P PiS j n2 n2' →
        (M.mem (M.op n1 n2) Pr ↔ M.mem (M.op n1' n2') Pr) :=
      fun β' h1 h2 => (hsat β').mp (ih β' h1 h2)
    intro n1 n2 n1' n2' hN1 hN2 p1 p2
    obtain ⟨β1, β1b, c1, u1, u1', lt1, ne1, hH1, hn1, hn1', hv1⟩ := M.pi_unpack cd p1
    obtain ⟨β2, β2b, c2, u2, u2', lt2, ne2, hH2, hn2, hn2', hv2⟩ := M.pi_unpack cd p2
    have hβ1 := (cd.hd.hth.fld _ _ lt1).1
    have hβ1b := (M.coll_dom cd.hH hH1).2.2
    obtain ⟨γ1, rγ1, ltγ1, neγ1⟩ := M.inN_rank hN1
    have eγ := M.rank_unique cd.hd (M.nameOf_rank hn1) rγ1
    rw [← eγ] at ltγ1 neγ1
    rw [M.pr_iff cd.hd cd.hPr hn1 hn2 hβ1, M.pr_iff cd.hd cd.hPr hn1' hn2' hβ1b]
    have hle : M.mem (M.op β1 β2) th ↔ M.mem (M.op β1b β2b) th :=
      M.coll_le_iff cd.hd.hth cd.hH hH1 hH2
    have heq : β1 = β2 ↔ β1b = β2b := by
      constructor
      · intro e
        rw [e] at hH1
        exact M.coll_fun cd.hd.hth cd.hH hH1 hH2
      · intro e
        rw [e] at hH1
        exact M.coll_inj cd.hd.hth cd.hH hH1 hH2
    have hL : β1 = β2 → c1 = c2 → (M.LexLt P th io Nt d Pr j β1 c1 u2 u1 ↔
        M.LexLt P th io Nt d Pr j β1b c1 u2' u1') := by
      intro eβ ec
      have eβb := heq.mp eβ
      subst eβ
      subst ec
      rw [← eβb] at hv2
      by_cases hne : ∃ z, M.InNRaw P th io M.nat j.1 β1 z
      · have conv : ∀ {u u' : V}, (∀ i : M.Num, i ≤ c1 → ∃ e e',
            M.ValRaw P th io M.nat Nt j.1 d β1 u i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d β1b u' i.1 e' ∧
            ((e = d ∧ e' = d) ∨ (M.InNRaw P th io M.nat j.1 β1 e ∧ M.PiRel P PiS j e e'))) →
            ∀ i : M.Num, i ≤ c1 → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β1 u i.1 e ∧
              M.ValRaw P th io M.nat Nt j.1 d β1b u' i.1 e' ∧
              (M.InNRaw P th io M.nat j.1 β1 e ∧ M.PiRel P PiS j e e') := by
          intro u u' hv i hi
          obtain ⟨e, e', v, v', hrel⟩ := hv i hi
          refine ⟨e, e', v, v', ?_⟩
          rcases hrel with ⟨h1, h2⟩ | h
          · rw [h1, h2]
            exact ⟨M.val_inN_of_ne cd.hd (Or.inr rfl) hne, M.pi_dd cd⟩
          · exact h
        have hrel : ∀ x x' y y', (M.InNRaw P th io M.nat j.1 β1 x ∧ M.PiRel P PiS j x x') →
            (M.InNRaw P th io M.nat j.1 β1 y ∧ M.PiRel P PiS j y y') →
            (M.LeV Pr x y ↔ M.LeV Pr x' y') := by
          rintro x x' y y' ⟨hx, px⟩ ⟨hy, py⟩
          obtain ⟨βx, βxb, rx, rx', hHx, -, -⟩ := M.pi_rank cd px
          rw [M.leV_iff' cd.hd cd.hPr rx (M.coll_dom cd.hH hHx).1,
            M.leV_iff' cd.hd cd.hPr rx' (M.coll_dom cd.hH hHx).2.2]
          exact ih' β1 ltγ1 neγ1 x y x' y' hx hy px py
        constructor
        · exact M.lex_transfer cd.hd _ (conv hv1) (conv hv2) hrel
        · refine M.lex_transfer cd.hd (fun x' x => M.InNRaw P th io M.nat j.1 β1 x ∧
            M.PiRel P PiS j x x') (fun i hi => ?_) (fun i hi => ?_)
            (fun x' x y' y hx hy => (hrel x x' y y' hx hy).symm)
          · obtain ⟨e, e', v, v', h⟩ := conv hv1 i hi
            exact ⟨e', e, v', v, h⟩
          · obtain ⟨e, e', v, v', h⟩ := conv hv2 i hi
            exact ⟨e', e, v', v, h⟩
      · have alld : ∀ {u u' : V}, (∀ i : M.Num, i ≤ c1 → ∃ e e',
            M.ValRaw P th io M.nat Nt j.1 d β1 u i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d β1b u' i.1 e' ∧
            ((e = d ∧ e' = d) ∨ (M.InNRaw P th io M.nat j.1 β1 e ∧ M.PiRel P PiS j e e'))) →
            ∀ i : M.Num, i ≤ c1 → M.ValRaw P th io M.nat Nt j.1 d β1 u i.1 d ∧
              M.ValRaw P th io M.nat Nt j.1 d β1b u' i.1 d := by
          intro u u' hv i hi
          obtain ⟨e, e', v, v', hrel⟩ := hv i hi
          rcases hrel with ⟨h1, h2⟩ | ⟨h, -⟩
          · rw [h1] at v
            rw [h2] at v'
            exact ⟨v, v'⟩
          · exact (hne ⟨e, h⟩).elim
        constructor
        · rintro ⟨i, hi, e', e, v', v, l1, l2, -⟩
          rw [M.val_unique cd.hd v' (alld hv2 i hi).1, M.val_unique cd.hd v (alld hv1 i hi).1] at l2
          exact (l2 (Or.inl rfl)).elim
        · rintro ⟨i, hi, e', e, v', v, l1, l2, -⟩
          rw [M.val_unique cd.hd v' (alld hv2 i hi).2, M.val_unique cd.hd v (alld hv1 i hi).2] at l2
          exact (l2 (Or.inl rfl)).elim
    constructor
    · rintro (⟨a, b⟩ | ⟨e, x | ⟨ec, nl⟩⟩)
      · exact Or.inl ⟨hle.mp a, fun e => b (heq.mpr e)⟩
      · exact Or.inr ⟨heq.mp e, Or.inl x⟩
      · exact Or.inr ⟨heq.mp e, Or.inr ⟨ec, fun l => nl ((hL e ec).mpr l)⟩⟩
    · rintro (⟨a, b⟩ | ⟨e, x | ⟨ec, nl⟩⟩)
      · exact Or.inl ⟨hle.mpr a, fun e => b (heq.mp e)⟩
      · exact Or.inr ⟨heq.mpr e, Or.inl x⟩
      · exact Or.inr ⟨heq.mpr e, Or.inr ⟨ec, fun l => nl ((hL (heq.mpr e) ec).mp l)⟩⟩

/-- Two images of a name are equivalent in the order of the names. -/
theorem pi_tie (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {n n' n'' : V}
    (p1 : M.PiRel P PiS j n n') (p2 : M.PiRel P PiS j n n'') :
    M.mem (M.op n' n'') Pr ∧ M.mem (M.op n'' n') Pr := by
  obtain ⟨β, -, rn, -, -, lt, -⟩ := M.pi_rank cd p1
  have hrefl := M.pr_refl cd.hd cd.hPr rn (cd.hd.hth.fld _ _ lt).1
  exact ⟨(M.pi_pr cd p1 p2).mp hrefl, (M.pi_pr cd p2 p1).mp hrefl⟩

/-- **The collapsing map is the identity on an initial part of `N`**: if the ordinal names of
all stages up to `B0` are in `N`, then every name of rank at most `B0` is in `N` and is its
own image. -/
theorem pi_self (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {B0 : V}
    (hall : ∀ β', M.mem (M.op β' B0) th → ∃ o, M.mem (M.quad j.1 β' q1 o) P ∧ M.mem o N)
    {n β : V} (rn : M.RankIs P io M.nat j.1 β n) (hβB : M.mem (M.op β B0) th) :
    M.mem n N ∧ M.PiRel P PiS j n n := by
  have hβ := (cd.hd.hth.fld _ _ hβB).1
  have hsat : ∀ α, Sat M.mem M.isSet (Fml.imp (fApp 22 250 337) (.all 320 (Fml.imp (fRank 250 320) (.and (.mem 320 169) (fPi 320 320)))))
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 167 PiS) 169 N) 337 B0) 250 α) ↔
      (M.mem (M.op α B0) th → ∀ n, M.RankIs P io M.nat j.1 α n →
        M.mem n N ∧ M.PiRel P PiS j n n) := by
    intro α
    simp [Sat, M.sat_imp, M.sat_fRank, M.sat_fApp', M.sat_fPi, Function.update_apply, PiRel]
  have key := M.wo_ind_fml cd.hd.hth (σW [(20, 7), (22, 5), (24, 5), (27, 3), (167, 5), (169, 3)])
    (Fml.imp (fApp 22 250 337) (.all 320 (Fml.imp (fRank 250 320) (.and (.mem 320 169) (fPi 320 320))))) 250 rfl (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 167 PiS) 169 N) 337 B0) (fun α hα ih => ?_) β hβ
  · exact (hsat β).mp key hβB n rn
  · rw [hsat α]
    have ih' : ∀ β', M.mem (M.op β' α) th → β' ≠ α → M.mem (M.op β' B0) th → ∀ n,
        M.RankIs P io M.nat j.1 β' n → M.mem n N ∧ M.PiRel P PiS j n n :=
      fun β' h1 h2 => (hsat β').mp (ih β' h1 h2)
    intro hαB n rn
    obtain ⟨c, u, hname⟩ := M.rank_nameOf rn
    obtain ⟨o, ho, hoN⟩ := hall α hαB
    obtain ⟨lt, ne, -⟩ := M.cond_rank cd hoN (M.mark_rank cd.hq ho)
    have hvals : ∀ i e, M.ValRaw P th io M.nat Nt j.1 d α u i e → M.mem e N ∧
        ((e = d ∧ e = d) ∨ (M.InNRaw P th io M.nat j.1 α e ∧ M.PiRel P PiS j e e)) := by
      intro i e hv
      rcases M.val_cases hv with h | h
      · obtain ⟨β1, r1, lt1, ne1⟩ := M.inN_rank h
        obtain ⟨h1, h2⟩ := ih' β1 lt1 ne1 (cd.hd.hth.trans _ _ _ lt1 hαB) e r1
        exact ⟨h1, Or.inr ⟨h, h2⟩⟩
      · rw [h]
        exact ⟨cd.hdN, Or.inl ⟨rfl, rfl⟩⟩
    have hH : M.mem (M.op α α) H := M.coll_id cd.hd.hth cd.hH hα
      (fun β' h => (cd.hO β').mpr (Or.inr (hall β' (cd.hd.hth.trans _ _ _ h hαB))))
    refine ⟨cd.hcl.2.2.1 n α c.1 u o ho hoN lt ne ((M.nameR_iff c).mpr hname)
      (fun i e _ _ hv => (hvals i e hv).1), M.pi_intro cd lt ne hH hname hname (fun i _ => ?_)⟩
    obtain ⟨e, ve⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j)
      α u i.1
    exact ⟨e, e, ve, ve, (hvals i.1 e ve).2⟩

end cond2

/-! ## Least witnesses in closed sets, and the statement of condensation at a stage -/

section tv

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}
variable {q1 : V}

/-- Truth with one value changed is truth under any sequence that has the changed values. -/
theorem trueUpd_iff (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t t' w : V}
    (c v : M.Num) (hag : M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v.1 w c.1) :
    M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 t w ↔ M.TrueAt P io F j.1 α c t' := by
  constructor
  · rintro ⟨t'', hag', h⟩
    refine (M.coin_hier hd c t'' t' (fun i hi e => ?_)).mp h
    rw [hag' i.1 i.2 ((M.leRaw_iff M.adG_spec i c).mpr hi) e,
      hag i.1 i.2 ((M.leRaw_iff M.adG_spec i c).mpr hi) e]
  · exact fun h => ⟨t', hag, h⟩

theorem agree_mono {α t t' v w : V} {c C : M.Num}
    (h : M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v w C.1) (hc : c ≤ C) :
    M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v w c.1 :=
  fun i hi hle e => h i hi ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ C).mpr
    (le_trans ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ c).mp hle) hc)) e

/-- Among the names of rank below `α` in a set there is a least one. -/
theorem least_inN (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {α : V} (S : V)
    (hS : ∃ w, M.mem w S ∧ M.InNRaw P th io M.nat j.1 α w) :
    ∃ w0, M.mem w0 S ∧ M.InNRaw P th io M.nat j.1 α w0 ∧
      ∀ w', M.mem w' S → M.InNRaw P th io M.nat j.1 α w' → M.mem (M.op w0 w') Pr := by
  obtain ⟨S', -, hS'0⟩ := M.comp (σW [(20, 7), (22, 5), (24, 5), (27, 3), (251, 3)])
    (.and (.mem 305 251) (Fml.ex 65 (.and (.eq 65 300) (fInN 305)))) 305 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 251 S) 300 α)
  have hS' : ∀ w, M.mem w S' ↔ M.mem w S ∧ M.InNRaw P th io M.nat j.1 α w := by
    intro w
    rw [hS'0 w]
    simp [Sat, M.sat_ex, M.sat_fInN, Function.update_apply]
  obtain ⟨w, hwS, hw⟩ := hS
  obtain ⟨β, rw', lt, -⟩ := M.inN_rank hw
  obtain ⟨w0, ρ0, hw0S', -, -, hmin⟩ := M.pr_least hd hPr S'
    ⟨w, β, (hS' w).mpr ⟨hwS, hw⟩, rw', (hd.hth.fld _ _ lt).1⟩
  obtain ⟨h1, h2⟩ := (hS' w0).mp hw0S'
  refine ⟨w0, h1, h2, fun w' hw'S hw' => ?_⟩
  obtain ⟨β', r', lt', -⟩ := M.inN_rank hw'
  exact hmin w' β' ((hS' w').mpr ⟨hw'S, hw'⟩) r' (hd.hth.fld _ _ lt').1

/-- A least witness exists whenever a witness exists. -/
theorem exists_lw_pos (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {α t : V} (c v : M.Num)
    (h : ∃ w, M.InNRaw P th io M.nat j.1 α w ∧ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 t w) :
    ∃ w0, M.LWR P th io M.nat Nt j.1 d M.adG F Pr α c.1 v.1 t w0 ∧
      M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 t w0 := by
  obtain ⟨S, -, hS0⟩ := M.comp
    (σW [(20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7), (163, 5)]) trueUpdFml 305 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 163 F) 300 α) 301 c.1) 303 v.1) 304 t)
  have hS : ∀ w, M.mem w S ↔ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 t w := by
    intro w
    rw [hS0 w, M.sat_trueUpdFml]
    simp [Function.update_apply]
  obtain ⟨w, hw, htu⟩ := h
  obtain ⟨w0, hw0S, hw0, hmin⟩ := M.least_inN hd hPr S ⟨w, (hS w).mpr htu, hw⟩
  exact ⟨w0, ⟨hw0, Or.inl ⟨(hS w0).mp hw0S, fun w' hw' htu' => hmin w' ((hS w').mpr htu') hw'⟩⟩,
    (hS w0).mp hw0S⟩

theorem exists_lw_neg (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j) {α t : V} (c v : M.Num)
    (h : ∃ w, M.InNRaw P th io M.nat j.1 α w ∧ ¬ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 t w) :
    ∃ w0, M.LWR P th io M.nat Nt j.1 d M.adG F Pr α c.1 v.1 t w0 ∧
      ¬ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 t w0 := by
  obtain ⟨S, -, hS0⟩ := M.comp
    (σW [(20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7), (163, 5)]) (.neg trueUpdFml) 305 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 163 F) 300 α) 301 c.1) 303 v.1) 304 t)
  have hS : ∀ w, M.mem w S ↔ ¬ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 t w := by
    intro w
    rw [hS0 w]
    simp [Sat, M.sat_trueUpdFml, Function.update_apply]
  obtain ⟨w, hw, htu⟩ := h
  obtain ⟨w0, hw0S, hw0, hmin⟩ := M.least_inN hd hPr S ⟨w, (hS w).mpr htu, hw⟩
  exact ⟨w0, ⟨hw0, Or.inr ⟨(hS w0).mp hw0S, fun w' hw' htu' => hmin w' ((hS w').mpr htu') hw'⟩⟩,
    (hS w0).mp hw0S⟩

variable {N δ Oc H PiS G ν : V}

theorem cond_stage (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ : V} (hρ : M.mem ρ Oc) :
    ρ = δ ∨ (M.mem (M.op ρ δ) th ∧ ¬ ρ = δ ∧ ∃ o, M.mem (M.quad j.1 ρ q1 o) P ∧ M.mem o N) := by
  rcases (cd.hO ρ).mp hρ with e | ⟨o, ho, hoN⟩
  · exact Or.inl e
  · obtain ⟨lt, ne, -⟩ := M.cond_rank cd hoN (M.mark_rank cd.hq ho)
    exact Or.inr ⟨lt, ne, o, ho, hoN⟩

/-- **Witnesses in `N`** (the Tarski–Vaught test): at a stage whose ordinal name is in `N`, or
at `δ`, if a formula with values in `N` has a witness then it has a witness in `N`. -/
theorem cond_lw_pos (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ t : V} (hρ : M.mem ρ Oc) (c v : M.Num)
    (hvals : ∀ i : M.Num, i ≤ c → ∀ e, M.ValRaw P th io M.nat Nt j.1 d ρ t i.1 e → M.mem e N)
    (h : ∃ w, M.InNRaw P th io M.nat j.1 ρ w ∧ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F ρ c.1 v.1 t w) :
    ∃ w, M.mem w N ∧ M.InNRaw P th io M.nat j.1 ρ w ∧ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F ρ c.1 v.1 t w := by
  obtain ⟨w0, hlw, htu⟩ := M.exists_lw_pos cd.hd cd.hPr c v h
  exact ⟨w0, cd.hcl.2.2.2.2.1 ρ c.1 v.1 t w0 (M.cond_stage cd hρ) c.2 v.2
    (fun i e hi hle hv => hvals ⟨i, hi⟩ ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ c).mp hle) e hv) hlw,
    hlw.1, htu⟩

theorem cond_lw_neg (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ t : V} (hρ : M.mem ρ Oc) (c v : M.Num)
    (hvals : ∀ i : M.Num, i ≤ c → ∀ e, M.ValRaw P th io M.nat Nt j.1 d ρ t i.1 e → M.mem e N)
    (h : ∃ w, M.InNRaw P th io M.nat j.1 ρ w ∧ ¬ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F ρ c.1 v.1 t w) :
    ∃ w, M.mem w N ∧ M.InNRaw P th io M.nat j.1 ρ w ∧ ¬ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F ρ c.1 v.1 t w := by
  obtain ⟨w0, hlw, htu⟩ := M.exists_lw_neg cd.hd cd.hPr c v h
  exact ⟨w0, cd.hcl.2.2.2.2.1 ρ c.1 v.1 t w0 (M.cond_stage cd hρ) c.2 v.2
    (fun i e hi hle hv => hvals ⟨i, hi⟩ ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ c).mp hle) e hv) hlw,
    hlw.1, htu⟩

/-- If some name of rank below `δ` denotes a member of the set denoted by `a` and not of the
set denoted by `b`, with `a`, `b` in `N`, then some member of `N` does. -/
theorem tv_diff (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {a b : V} (ha : M.mem a N) (hb : M.mem b N)
    (h : ∃ y, M.InNRaw P th io M.nat j.1 δ y ∧ M.EpsStarRaw P th io M.nat j.1 tp F y a ∧
      ¬ M.EpsStarRaw P th io M.nat j.1 tp F y b) :
    ∃ y, M.mem y N ∧ M.EpsStarRaw P th io M.nat j.1 tp F y a ∧
      ¬ M.EpsStarRaw P th io M.nat j.1 tp F y b := by
  obtain ⟨C, hC⟩ : ∃ C : M.Num, C = M.cAnd (M.cRel 0 0 1) (M.cNeg (M.cRel 0 0 2)) := ⟨_, rfl⟩
  have h0C : (0 : M.Num) ≤ C := by
    rw [hC]
    exact le_trans (M.le_cRel_left 0 0 1) (M.le_cAnd_left _ _)
  have h1C : (1 : M.Num) ≤ C := by
    rw [hC]
    exact le_trans (M.le_cRel_right 0 0 1) (M.le_cAnd_left _ _)
  have h2C : (2 : M.Num) ≤ C := by
    rw [hC]
    exact le_trans (M.le_cRel_right 0 0 2) (le_trans (M.le_cNeg _) (M.le_cAnd_right _ _))
  obtain ⟨t0, ht0R, hconst⟩ := M.const_seq cd.hd (C + 1)
  obtain ⟨t1, -, hag1⟩ := M.exists_updR cd.hd (cd.hsub a ha) t0 (1 : M.Num).1 C
  obtain ⟨t2, -, hag2⟩ := M.exists_updR cd.hd (cd.hsub b hb) t1 (2 : M.Num).1 C
  have w1 : M.ValRaw P th io M.nat Nt j.1 d δ t2 (1 : M.Num).1 a :=
    M.agree_other hag2 h1C M.n12 (M.agree_same hag1 h1C)
  have w2 : M.ValRaw P th io M.nat Nt j.1 d δ t2 (2 : M.Num).1 b := M.agree_same hag2 h2C
  have key : ∀ y, M.InNRaw P th io M.nat j.1 δ y → (M.TrueUpdR P th io M.nat Nt j.1 d M.adG F δ C.1 (0 : M.Num).1 t2 y ↔
      (M.EpsStarRaw P th io M.nat j.1 tp F y a ∧ ¬ M.EpsStarRaw P th io M.nat j.1 tp F y b)) := by
    intro y hy
    obtain ⟨t3, -, hag3⟩ := M.exists_updR cd.hd hy t2 (0 : M.Num).1 C
    rw [M.trueUpd_iff cd.hd C 0 hag3]
    have v0 : M.ValRaw P th io M.nat Nt j.1 d δ t3 (0 : M.Num).1 y := M.agree_same hag3 h0C
    have v1 : M.ValRaw P th io M.nat Nt j.1 d δ t3 (1 : M.Num).1 a := M.agree_other hag3 h1C M.n10 w1
    have v2 : M.ValRaw P th io M.nat Nt j.1 d δ t3 (2 : M.Num).1 b := M.agree_other hag3 h2C M.n20 w2
    rw [hC, M.hier_and cd.hd, M.hier_neg cd.hd, M.rel_val cd.hd 0 1 cd.hδ v0 v1,
      M.rel_val cd.hd 0 2 cd.hδ v0 v2]
    constructor
    · rintro ⟨-, h1, -, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨cd.hδ, h1, cd.hδ, h2⟩
  have hvals : ∀ i : M.Num, i ≤ C → ∀ e, M.ValRaw P th io M.nat Nt j.1 d δ t2 i.1 e → M.mem e N := by
    intro i hi e hv
    by_cases e2 : i = 2
    · rw [e2] at hv
      rw [M.val_unique cd.hd hv w2]
      exact hb
    · by_cases e1 : i = 1
      · rw [e1] at hv
        rw [M.val_unique cd.hd hv w1]
        exact ha
      · rw [M.val_unique cd.hd hv (M.agree_other hag2 hi e2 (M.agree_other hag1 hi e1
          (hconst δ i (add_le_add hi (le_refl 1)))))]
        exact cd.hdN
  obtain ⟨y, hy, hprop⟩ := h
  obtain ⟨w, hwN, hwδ, htu⟩ := M.cond_lw_pos cd ((cd.hO δ).mpr (Or.inl rfl)) C 0 hvals
    ⟨y, hy, (key y hy).mpr hprop⟩
  exact ⟨w, hwN, (key w hwδ).mp htu⟩

end tv

/-- **The statement of condensation at the stage `ρ`**, for the collapse `H` and the
collapsing map `PiS`. (1) For names of rank below `ρ`, "denote the same set" is preserved in
both directions. For the collapse `ρb` of `ρ`: (2) every name of rank below `ρb` denotes the
same set as an image; (3) every canonical name of rank below `ρb` is equivalent, in the order
of the names, to the image of a canonical name; (4) a formula is true at `ρ` under a sequence
if and only if it is true at `ρb` under a sequence whose values are images of the values. -/
def CondAtR (P th io nat Nt j d ad tp F Pr H PiS ρ : V) : Prop :=
  (∀ n1 n2 n1' n2', M.InNRaw P th io nat j ρ n1 → M.InNRaw P th io nat j ρ n2 →
    (∃ β z, M.mem (M.quad j n1 n1' z) P ∧ M.mem (M.op β z) PiS) →
    (∃ β z, M.mem (M.quad j n2 n2' z) P ∧ M.mem (M.op β z) PiS) →
    (M.SimRaw P j tp F n1 n2 ↔ M.SimRaw P j tp F n1' n2')) ∧
  ∀ ρb, M.mem (M.op ρ ρb) H →
    (∀ m', M.InNRaw P th io nat j ρb m' → ∃ n n', M.InNRaw P th io nat j ρ n ∧
      (∃ β z, M.mem (M.quad j n n' z) P ∧ M.mem (M.op β z) PiS) ∧ M.SimRaw P j tp F n' m') ∧
    (∀ m', M.InNRaw P th io nat j ρb m' → M.IsCan P j tp F Pr m' →
      ∃ n n', M.InNRaw P th io nat j ρ n ∧
        (∃ β z, M.mem (M.quad j n n' z) P ∧ M.mem (M.op β z) PiS) ∧ M.IsCan P j tp F Pr n ∧
        M.mem (M.op n' m') Pr ∧ M.mem (M.op m' n') Pr) ∧
    (∀ c t t', M.mem c nat →
      (∀ i, M.mem i nat → (∃ x, M.mem x nat ∧ M.mem (M.trip i x c) ad) → ∃ e e',
        M.ValRaw P th io nat Nt j d ρ t i e ∧ M.ValRaw P th io nat Nt j d ρb t' i e' ∧
        ∃ β z, M.mem (M.quad j e e' z) P ∧ M.mem (M.op β z) PiS) →
      (M.TrueAtR P io F j ρ c t ↔ M.TrueAtR P io F j ρb c t'))

/-- `CondAtR`, with `ρ` the name `250`; `H` is the name `171`, `PiS` the name `167`, `F` the
name `6`. -/
def condAtFml : Fml :=
  .and (.all 320 (.all 335 (.all 321 (.all 336 (Fml.imp (Fml.ex 65 (.and (.eq 65 250) (fInN
    320))) (Fml.imp (Fml.ex 65 (.and (.eq 65 250) (fInN 335))) (Fml.imp (fPi 320 321) (Fml.imp
    (fPi 335 336) (Fml.iff (fSim 320 335) (fSim 321 336)))))))))) (.all 338 (Fml.imp (fApp 171
    250 338) (.and (.all 339 (Fml.imp (Fml.ex 65 (.and (.eq 65 338) (fInN 339))) (Fml.ex 320
    (Fml.ex 321 (.and (Fml.ex 65 (.and (.eq 65 250) (fInN 320))) (.and (fPi 320 321) (fSim 321
    339))))))) (.and (.all 339 (Fml.imp (Fml.ex 65 (.and (.eq 65 338) (fInN 339))) (Fml.imp
    (fCan 339) (Fml.ex 320 (Fml.ex 321 (.and (Fml.ex 65 (.and (.eq 65 250) (fInN 320))) (.and
    (fPi 320 321) (.and (fCan 320) (.and (fApp 162 321 339) (fApp 162 339 321)))))))))) (.all
    301 (.all 340 (.all 341 (Fml.imp (.mem 301 27) (Fml.imp (.all 326 (Fml.imp (.mem 326 27)
    (Fml.imp (fLeN 326 301) (Fml.ex 327 (Fml.ex 328 (.and (fVal 250 340 326 327) (.and (fVal 338
    341 326 328) (fPi 327 328)))))))) (Fml.iff (Fml.ex 259 (Fml.ex 260 (.and (fApp 24 301 259)
    (.and (fApp4 20 25 250 259 260) (fApp 6 260 340))))) (Fml.ex 259 (Fml.ex 260 (.and (fApp 24
    301 259) (.and (fApp4 20 25 338 259 260) (fApp 6 260 341)))))))))))))))

theorem sat_condAtFml (ρ : ℕ → V) : Sat M.mem M.isSet condAtFml ρ ↔
    M.CondAtR (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 21) (ρ 6) (ρ 162) (ρ 171)
      (ρ 167) (ρ 250) := by
  simp [condAtFml, CondAtR, TrueAtR, Sat, M.sat_imp, M.sat_iff, M.sat_ex, M.sat_fInN, M.sat_fSim,
    M.sat_fCan, M.sat_fPi, M.sat_fVal, M.sat_fLeN, M.sat_fApp', M.sat_fApp4',
    Function.update_apply]

/-! ## Condensation: the step for "denote the same set" and membership -/

section cond3

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {N δ Oc H PiS G ν : V}
variable {q1 : V}

theorem ca_sim {ρ n1 n2 n1' n2' : V} (h : M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS ρ)
    (hn1 : M.InNRaw P th io M.nat j.1 ρ n1) (hn2 : M.InNRaw P th io M.nat j.1 ρ n2) (p1 : M.PiRel P PiS j n1 n1') (p2 : M.PiRel P PiS j n2 n2') :
    M.SimRaw P j.1 tp F n1 n2 ↔ M.SimRaw P j.1 tp F n1' n2' := h.1 n1 n2 n1' n2' hn1 hn2 p1 p2

theorem ca_surj {ρ ρb m' : V} (h : M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS ρ) (hH : M.mem (M.op ρ ρb) H)
    (hm : M.InNRaw P th io M.nat j.1 ρb m') : ∃ n n', M.InNRaw P th io M.nat j.1 ρ n ∧ M.PiRel P PiS j n n' ∧ M.SimRaw P j.1 tp F n' m' :=
  (h.2 ρb hH).1 m' hm

theorem ca_can {ρ ρb m' : V} (h : M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS ρ) (hH : M.mem (M.op ρ ρb) H)
    (hm : M.InNRaw P th io M.nat j.1 ρb m') (hc : M.IsCan P j.1 tp F Pr m') :
    ∃ n n', M.InNRaw P th io M.nat j.1 ρ n ∧ M.PiRel P PiS j n n' ∧ M.IsCan P j.1 tp F Pr n ∧ M.mem (M.op n' m') Pr ∧ M.mem (M.op m' n') Pr :=
  (h.2 ρb hH).2.1 m' hm hc

theorem ca_elem {ρ ρb : V} (h : M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS ρ) (hH : M.mem (M.op ρ ρb) H) (c : M.Num) (t t' : V)
    (hv : ∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d ρb t' i.1 e' ∧ M.PiRel P PiS j e e') :
    M.TrueAt P io F j.1 ρ c t ↔ M.TrueAt P io F j.1 ρb c t' :=
  (h.2 ρb hH).2.2 c.1 t t' c.2
    (fun i hi hle => hv ⟨i, hi⟩ ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ c).mp hle))

theorem eps_name (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {n β u : V} {c : M.Num}
    (hn : M.NameOf P io j n β c u) (x : V) :
    M.EpsRaw P th io M.nat j.1 F x n ↔ M.InNRaw P th io M.nat j.1 β x ∧ ∃ s, M.mem (M.quad j.1 x u s) P ∧ M.TrueAt P io F j.1 β c s := by
  obtain ⟨f, q, h1, h2, h3⟩ := hn
  exact M.eps_iff hd h1 h2 h3 x

theorem nameOf_u_rung (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {n β u : V}
    {c : M.Num} (hn : M.NameOf P io j n β c u) : M.mem (M.op j.1 u) R := by
  obtain ⟨f, q, h1, h2, h3⟩ := hn
  exact (hd.hP.dom _ _ _ _ h2).2.2.1

/-- Membership in a name passes to a name of rank below the same stage that denotes the same
set. -/
theorem eps_sim_left (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {n β u x x2 : V}
    {c : M.Num} (hn : M.NameOf P io j n β c u) (hβ : M.mem (M.op β β) th) (he : M.EpsRaw P th io M.nat j.1 F x n)
    (hs : M.SimRaw P j.1 tp F x x2) (hx2 : M.InNRaw P th io M.nat j.1 β x2) : M.EpsRaw P th io M.nat j.1 F x2 n := by
  rw [M.eps_name hd hn] at he ⊢
  obtain ⟨hx, s, hs', htr⟩ := he
  obtain ⟨s2, hs2⟩ := hd.hP.tot j hd.hj x2 u (M.inN_rung hd hx2) (M.nameOf_u_rung hd hn)
  refine ⟨hx2, s2, hs2, (M.inv_hier hd c s s2 (fun i hi => ?_)).mp htr⟩
  rcases M.num_cases i with h0 | ⟨i', hi'⟩
  · rw [h0]
    exact ⟨x, x2, M.val_cons_zero hd hs' hx, M.val_cons_zero hd hs2 hx2, hs⟩
  · rw [hi', M.nsucc_eq_add_one]
    obtain ⟨g, vg⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j)
      β u i'.1
    exact ⟨g, g, (M.val_cons_succ hd hs' i').mpr vg, (M.val_cons_succ hd hs2 i').mpr vg,
      M.val_sim_refl hd hβ vg⟩

/-- **Members correspond**: for a name and its image, a member of `N` denotes a member of the
one if and only if its image denotes a member of the other. -/
theorem cond_eps (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1)
    {β βb n n' u u' x x' : V} {c : M.Num} (hca : M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β) (hH : M.mem (M.op β βb) H)
    (hn : M.NameOf P io j n β c u) (hn' : M.NameOf P io j n' βb c u')
    (hv : ∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β u i.1 e ∧
      M.ValRaw P th io M.nat Nt j.1 d βb u' i.1 e' ∧
      ((e = d ∧ e' = d) ∨ (M.InNRaw P th io M.nat j.1 β e ∧ M.PiRel P PiS j e e')))
    (hx : M.InNRaw P th io M.nat j.1 β x) (px : M.PiRel P PiS j x x') : M.EpsRaw P th io M.nat j.1 F x n ↔ M.EpsRaw P th io M.nat j.1 F x' n' := by
  rw [M.eps_name cd.hd hn, M.eps_name cd.hd hn']
  have hx' := M.pi_inN cd px hx hH
  obtain ⟨s, hs⟩ := cd.hd.hP.tot j cd.hd.hj x u (M.inN_rung cd.hd hx) (M.nameOf_u_rung cd.hd hn)
  obtain ⟨s', hs'⟩ := cd.hd.hP.tot j cd.hd.hj x' u' (M.inN_rung cd.hd hx')
    (M.nameOf_u_rung cd.hd hn')
  have key : M.TrueAt P io F j.1 β c s ↔ M.TrueAt P io F j.1 βb c s' := by
    refine M.ca_elem hca hH c s s' (fun i hi => ?_)
    rcases M.num_cases i with h0 | ⟨i', hi'⟩
    · rw [h0]
      exact ⟨x, x', M.val_cons_zero cd.hd hs hx, M.val_cons_zero cd.hd hs' hx', px⟩
    · rw [hi', M.nsucc_eq_add_one]
      rw [hi', M.nsucc_eq_add_one] at hi
      obtain ⟨e, e', v, v', hrel⟩ := hv i' (le_trans (M.le_add_one i') hi)
      refine ⟨e, e', (M.val_cons_succ cd.hd hs i').mpr v, (M.val_cons_succ cd.hd hs' i').mpr v', ?_⟩
      rcases hrel with ⟨h1, h2⟩ | ⟨-, h⟩
      · rw [h1, h2]
        exact M.pi_dd cd
      · exact h
  constructor
  · rintro ⟨-, s1, hs1, htr⟩
    rw [cd.hd.hP.fn _ _ _ _ _ hs1 hs] at htr
    exact ⟨hx', s', hs', key.mp htr⟩
  · rintro ⟨-, s1, hs1, htr⟩
    rw [cd.hd.hP.fn _ _ _ _ _ hs1 hs'] at htr
    exact ⟨hx, s, hs, key.mpr htr⟩

/-- A member of `N` has a canonical name in `N`. -/
theorem cond_can (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {x : V} (hx : M.mem x N) :
    ∃ x0, M.mem x0 N ∧ M.IsCan P j.1 tp F Pr x0 ∧ M.SimRaw P j.1 tp F x x0 := by
  obtain ⟨x0, hc, hs⟩ := M.exists_can cd.hd cd.hPr (M.inN_refl cd.hd (cd.hsub x hx))
  exact ⟨x0, cd.hcl.2.2.2.1 x x0 hx hc hs, hc, hs⟩

/-- One half of the step for "denote the same set", forwards. -/
theorem step_sim_half (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ : V}
    (lower : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β)
    {n1 n2 n1' n2' β1 β1b β2 β2b u1 u1' u2 u2' : V} {c1 c2 : M.Num}
    (lt1 : M.mem (M.op β1 ρ) th) (ne1 : β1 ≠ ρ) (hH1 : M.mem (M.op β1 β1b) H)
    (hn1 : M.NameOf P io j n1 β1 c1 u1) (hn1' : M.NameOf P io j n1' β1b c1 u1')
    (hv1 : ∀ i : M.Num, i ≤ c1 → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β1 u1 i.1 e ∧
      M.ValRaw P th io M.nat Nt j.1 d β1b u1' i.1 e' ∧
      ((e = d ∧ e' = d) ∨ (M.InNRaw P th io M.nat j.1 β1 e ∧ M.PiRel P PiS j e e')))
    (lt2 : M.mem (M.op β2 ρ) th) (ne2 : β2 ≠ ρ) (hH2 : M.mem (M.op β2 β2b) H)
    (hn2 : M.NameOf P io j n2 β2 c2 u2) (hn2' : M.NameOf P io j n2' β2b c2 u2')
    (hv2 : ∀ i : M.Num, i ≤ c2 → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β2 u2 i.1 e ∧
      M.ValRaw P th io M.nat Nt j.1 d β2b u2' i.1 e' ∧
      ((e = d ∧ e' = d) ∨ (M.InNRaw P th io M.nat j.1 β2 e ∧ M.PiRel P PiS j e e')))
    (hs : M.SimRaw P j.1 tp F n1 n2) (x' : V) (hx' : M.EpsRaw P th io M.nat j.1 F x' n1') :
    ∃ y', M.EpsRaw P th io M.nat j.1 F y' n2' ∧ M.SimRaw P j.1 tp F x' y' := by
  have hβ1 := (cd.hd.hth.fld _ _ lt1).1
  have hβ2 := (cd.hd.hth.fld _ _ lt2).1
  have hβ1b := (M.coll_dom cd.hH hH1).2.2
  have hx'N := M.eps_inN_rank cd.hd (M.nameOf_rank hn1') hx'
  obtain ⟨x, xt, hxN, px, hsx⟩ := M.ca_surj (lower β1 lt1 ne1) hH1 hx'N
  have hxt := M.pi_inN cd px hxN hH1
  have ext : M.EpsRaw P th io M.nat j.1 F xt n1' := M.eps_sim_left cd.hd hn1' hβ1b hx' (M.sim_symm cd.hd hsx) hxt
  have ex : M.EpsRaw P th io M.nat j.1 F x n1 := (M.cond_eps cd (lower β1 lt1 ne1) hH1 hn1 hn1' hv1 hxN px).mpr ext
  obtain ⟨y, ey, hsy⟩ := ((M.hier_sim cd.hd (M.nameOf_rank hn1) (M.nameOf_rank hn2) hβ1 hβ2).mp
    hs).1 x ex
  have hyN := M.eps_inN_rank cd.hd (M.nameOf_rank hn2) ey
  obtain ⟨y0, hy0N, hc0, hs0⟩ := M.cond_can cd (M.pi_mem cd px)
  have hsyy0 : M.SimRaw P j.1 tp F y y0 := M.sim_trans cd.hd (M.sim_symm cd.hd hsy) hs0
  have hy0 := M.can_inN cd.hd cd.hPr hyN hc0 hsyy0
  have ey0 : M.EpsRaw P th io M.nat j.1 F y0 n2 := M.eps_sim_left cd.hd hn2 hβ2 ey hsyy0 hy0
  obtain ⟨y0t, py0⟩ := M.pi_tot cd hy0N
  have ey0t : M.EpsRaw P th io M.nat j.1 F y0t n2' := (M.cond_eps cd (lower β2 lt2 ne2) hH2 hn2 hn2' hv2 hy0 py0).mp ey0
  -- the larger of the two ranks
  have hsim : M.SimRaw P j.1 tp F xt y0t := by
    rcases M.wo_total cd.hd.hth hβ1 hβ2 with h | h
    · exact (M.ca_sim (lower β2 lt2 ne2) (M.inN_mono cd.hd hxN h) hy0 px py0).mp hs0
    · exact (M.ca_sim (lower β1 lt1 ne1) hxN (M.inN_mono cd.hd hy0 h) px py0).mp hs0
  exact ⟨y0t, ey0t, M.sim_trans cd.hd (M.sim_symm cd.hd hsx) hsim⟩

/-- One half of the step for "denote the same set", backwards: no member of `N`... no name of
rank below `δ` denotes a member of the set denoted by `n1` and not of that denoted by `n2`. -/
theorem step_sim_back (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ : V}
    (lower : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β)
    {n1 n2 n1' n2' β1 β1b β2 β2b u1 u1' u2 u2' : V} {c1 c2 : M.Num}
    (lt1 : M.mem (M.op β1 ρ) th) (ne1 : β1 ≠ ρ) (hH1 : M.mem (M.op β1 β1b) H)
    (hn1 : M.NameOf P io j n1 β1 c1 u1) (hn1' : M.NameOf P io j n1' β1b c1 u1')
    (hv1 : ∀ i : M.Num, i ≤ c1 → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β1 u1 i.1 e ∧
      M.ValRaw P th io M.nat Nt j.1 d β1b u1' i.1 e' ∧
      ((e = d ∧ e' = d) ∨ (M.InNRaw P th io M.nat j.1 β1 e ∧ M.PiRel P PiS j e e')))
    (lt2 : M.mem (M.op β2 ρ) th) (ne2 : β2 ≠ ρ) (hH2 : M.mem (M.op β2 β2b) H)
    (hn2 : M.NameOf P io j n2 β2 c2 u2) (hn2' : M.NameOf P io j n2' β2b c2 u2')
    (hv2 : ∀ i : M.Num, i ≤ c2 → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β2 u2 i.1 e ∧
      M.ValRaw P th io M.nat Nt j.1 d β2b u2' i.1 e' ∧
      ((e = d ∧ e' = d) ∨ (M.InNRaw P th io M.nat j.1 β2 e ∧ M.PiRel P PiS j e e')))
    (hn1N : M.mem n1 N) (hn2N : M.mem n2 N) (hs' : M.SimRaw P j.1 tp F n1' n2') :
    ¬ ∃ y, M.InNRaw P th io M.nat j.1 δ y ∧ M.EpsStarRaw P th io M.nat j.1 tp F y n1 ∧ ¬ M.EpsStarRaw P th io M.nat j.1 tp F y n2 := by
  intro hex
  have hβ1 := (cd.hd.hth.fld _ _ lt1).1
  have hβ2 := (cd.hd.hth.fld _ _ lt2).1
  have hβ1b := (M.coll_dom cd.hH hH1).2.2
  have hβ2b := (M.coll_dom cd.hH hH2).2.2
  obtain ⟨y, hyN, ⟨y1, hsy1, ey1⟩, hnot⟩ := M.tv_diff cd hn1N hn2N hex
  have hy1 := M.eps_inN_rank cd.hd (M.nameOf_rank hn1) ey1
  obtain ⟨y0, hy0N, hc0, hs0⟩ := M.cond_can cd hyN
  have hsy1y0 : M.SimRaw P j.1 tp F y1 y0 := M.sim_trans cd.hd (M.sim_symm cd.hd hsy1) hs0
  have hy0 := M.can_inN cd.hd cd.hPr hy1 hc0 hsy1y0
  have ey0 : M.EpsRaw P th io M.nat j.1 F y0 n1 := M.eps_sim_left cd.hd hn1 hβ1 ey1 hsy1y0 hy0
  obtain ⟨y0t, py0⟩ := M.pi_tot cd hy0N
  have ey0t : M.EpsRaw P th io M.nat j.1 F y0t n1' := (M.cond_eps cd (lower β1 lt1 ne1) hH1 hn1 hn1' hv1 hy0 py0).mp ey0
  obtain ⟨z', ez', hsz'⟩ := ((M.hier_sim cd.hd (M.nameOf_rank hn1') (M.nameOf_rank hn2') hβ1b
    hβ2b).mp hs').1 y0t ey0t
  have hz'N := M.eps_inN_rank cd.hd (M.nameOf_rank hn2') ez'
  obtain ⟨z, zt, hzN, pz, hsz⟩ := M.ca_surj (lower β2 lt2 ne2) hH2 hz'N
  have hzt := M.pi_inN cd pz hzN hH2
  have ezt : M.EpsRaw P th io M.nat j.1 F zt n2' := M.eps_sim_left cd.hd hn2' hβ2b ez' (M.sim_symm cd.hd hsz) hzt
  have ez : M.EpsRaw P th io M.nat j.1 F z n2 := (M.cond_eps cd (lower β2 lt2 ne2) hH2 hn2 hn2' hv2 hzN pz).mpr ezt
  have hsim' : M.SimRaw P j.1 tp F y0t zt := M.sim_trans cd.hd hsz' (M.sim_symm cd.hd hsz)
  have hsim : M.SimRaw P j.1 tp F y0 z := by
    rcases M.wo_total cd.hd.hth hβ1 hβ2 with h | h
    · exact (M.ca_sim (lower β2 lt2 ne2) (M.inN_mono cd.hd hy0 h) hzN py0 pz).mpr hsim'
    · exact (M.ca_sim (lower β1 lt1 ne1) hy0 (M.inN_mono cd.hd hzN h) py0 pz).mpr hsim'
  exact hnot ⟨z, M.sim_trans cd.hd hs0 hsim, ez⟩

/-- **The step for "denote the same set"**: it is preserved by the collapsing map, in both
directions, for names of rank below `ρ`, if condensation holds at the stages below `ρ`. -/
theorem step_sim (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ : V}
    (lower : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β)
    {n1 n2 n1' n2' : V} (hN1 : M.InNRaw P th io M.nat j.1 ρ n1) (hN2 : M.InNRaw P th io M.nat j.1 ρ n2)
    (p1 : M.PiRel P PiS j n1 n1') (p2 : M.PiRel P PiS j n2 n2') : M.SimRaw P j.1 tp F n1 n2 ↔ M.SimRaw P j.1 tp F n1' n2' := by
  obtain ⟨β1, β1b, c1, u1, u1', ltd1, -, hH1, hn1, hn1', hv1⟩ := M.pi_unpack cd p1
  obtain ⟨β2, β2b, c2, u2, u2', ltd2, -, hH2, hn2, hn2', hv2⟩ := M.pi_unpack cd p2
  obtain ⟨γ1, r1, lt1, ne1⟩ := M.inN_rank hN1
  obtain ⟨γ2, r2, lt2, ne2⟩ := M.inN_rank hN2
  have e1 := M.rank_unique cd.hd (M.nameOf_rank hn1) r1
  have e2 := M.rank_unique cd.hd (M.nameOf_rank hn2) r2
  rw [← e1] at lt1 ne1
  rw [← e2] at lt2 ne2
  have hβ1 := (cd.hd.hth.fld _ _ lt1).1
  have hβ2 := (cd.hd.hth.fld _ _ lt2).1
  have hβ1b := (M.coll_dom cd.hH hH1).2.2
  have hβ2b := (M.coll_dom cd.hH hH2).2.2
  constructor
  · intro hs
    refine (M.hier_sim cd.hd (M.nameOf_rank hn1') (M.nameOf_rank hn2') hβ1b hβ2b).mpr
      ⟨fun x' hx' => M.step_sim_half cd lower lt1 ne1 hH1 hn1 hn1' hv1 lt2 ne2 hH2 hn2 hn2' hv2
        hs x' hx', fun y' hy' => ?_⟩
    obtain ⟨x', h1, h2⟩ := M.step_sim_half cd lower lt2 ne2 hH2 hn2 hn2' hv2 lt1 ne1 hH1 hn1 hn1'
      hv1 (M.sim_symm cd.hd hs) y' hy'
    exact ⟨x', h1, M.sim_symm cd.hd h2⟩
  · intro hs'
    have hn1N := M.pi_mem cd p1
    have hn2N := M.pi_mem cd p2
    have s11 := M.sim_refl cd.hd (M.nameOf_rank hn1) hβ1
    have s22 := M.sim_refl cd.hd (M.nameOf_rank hn2) hβ2
    refine (M.sim_iff_ext cd.hd (M.nameOf_rank hn1) (M.nameOf_rank hn2) hβ1 hβ2).mpr (fun x => ?_)
    constructor
    · intro h1
      by_contra h2
      obtain ⟨x0, hsx, ex0⟩ := h1
      have hx0 := M.eps_inN_rank cd.hd (M.nameOf_rank hn1) ex0
      exact M.step_sim_back cd lower lt1 ne1 hH1 hn1 hn1' hv1 lt2 ne2 hH2 hn2 hn2' hv2 hn1N hn2N
        hs' ⟨x0, M.inN_mono cd.hd hx0 ltd1, ⟨x0, M.inN_refl cd.hd hx0, ex0⟩,
          fun h => h2 (M.epsStar_congr cd.hd (M.sim_symm cd.hd hsx) s22 h)⟩
    · intro h1
      by_contra h2
      obtain ⟨x0, hsx, ex0⟩ := h1
      have hx0 := M.eps_inN_rank cd.hd (M.nameOf_rank hn2) ex0
      exact M.step_sim_back cd lower lt2 ne2 hH2 hn2 hn2' hv2 lt1 ne1 hH1 hn1 hn1' hv1 hn2N hn1N
        (M.sim_symm cd.hd hs') ⟨x0, M.inN_mono cd.hd hx0 ltd2, ⟨x0, M.inN_refl cd.hd hx0, ex0⟩,
          fun h => h2 (M.epsStar_congr cd.hd (M.sim_symm cd.hd hsx) s11 h)⟩

/-- **The step for membership**: membership between the denoted sets is preserved by the
collapsing map, in both directions, for names of rank below `ρ`. -/
theorem step_eps (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ : V}
    (lower : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β)
    {n1 n2 n1' n2' : V} (hN1 : M.InNRaw P th io M.nat j.1 ρ n1) (hN2 : M.InNRaw P th io M.nat j.1 ρ n2)
    (p1 : M.PiRel P PiS j n1 n1') (p2 : M.PiRel P PiS j n2 n2') : M.EpsStarRaw P th io M.nat j.1 tp F n1 n2 ↔ M.EpsStarRaw P th io M.nat j.1 tp F n1' n2' := by
  obtain ⟨β2, β2b, c2, u2, u2', ltd2, -, hH2, hn2, hn2', hv2⟩ := M.pi_unpack cd p2
  obtain ⟨γ2, r2, lt2, ne2⟩ := M.inN_rank hN2
  have e2 := M.rank_unique cd.hd (M.nameOf_rank hn2) r2
  rw [← e2] at lt2 ne2
  have hβ2 := (cd.hd.hth.fld _ _ lt2).1
  have hβ2b := (M.coll_dom cd.hH hH2).2.2
  constructor
  · rintro ⟨a, hs, he⟩
    have haN := M.eps_inN_rank cd.hd (M.nameOf_rank hn2) he
    obtain ⟨a0, ha0N, hc0, hs0⟩ := M.cond_can cd (M.pi_mem cd p1)
    have hsa : M.SimRaw P j.1 tp F a a0 := M.sim_trans cd.hd (M.sim_symm cd.hd hs) hs0
    have ha0 := M.can_inN cd.hd cd.hPr haN hc0 hsa
    have ea0 : M.EpsRaw P th io M.nat j.1 F a0 n2 := M.eps_sim_left cd.hd hn2 hβ2 he hsa ha0
    obtain ⟨a0t, pa0⟩ := M.pi_tot cd ha0N
    exact ⟨a0t, (M.step_sim cd lower hN1 (M.inN_mono cd.hd ha0 lt2) p1 pa0).mp hs0,
      (M.cond_eps cd (lower β2 lt2 ne2) hH2 hn2 hn2' hv2 ha0 pa0).mp ea0⟩
  · rintro ⟨a', hs', he'⟩
    have ha'N := M.eps_inN_rank cd.hd (M.nameOf_rank hn2') he'
    obtain ⟨a, at', haN, pa, hsa⟩ := M.ca_surj (lower β2 lt2 ne2) hH2 ha'N
    have hat := M.pi_inN cd pa haN hH2
    have eat : M.EpsRaw P th io M.nat j.1 F at' n2' := M.eps_sim_left cd.hd hn2' hβ2b he' (M.sim_symm cd.hd hsa) hat
    exact ⟨a, (M.step_sim cd lower hN1 (M.inN_mono cd.hd haN lt2) p1 pa).mpr
        (M.sim_trans cd.hd hs' (M.sim_symm cd.hd hsa)),
      (M.cond_eps cd (lower β2 lt2 ne2) hH2 hn2 hn2' hv2 haN pa).mpr eat⟩

end cond3

/-! ## Condensation: surjectivity, canonical names, the canonical well-ordering -/

section cond4

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {N δ Oc H PiS G ν : V}
variable {q1 : V}

/-- A stage below a stage of `Oc` is below `δ`. -/
theorem cond_below (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ β : V} (hρO : M.mem ρ Oc) (lt : M.mem (M.op β ρ) th)
    (ne : β ≠ ρ) : M.mem (M.op β δ) th ∧ β ≠ δ := by
  rcases M.cond_stage cd hρO with e | ⟨l, n, -⟩
  · rw [← e]
    exact ⟨lt, ne⟩
  · refine ⟨cd.hd.hth.trans _ _ _ lt l, fun e => n ?_⟩
    rw [e] at lt
    exact cd.hd.hth.antisymm _ _ l lt

/-- The ordinal name of a stage of `Oc` below `δ` is in `N`. -/
theorem cond_ord (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {β : V} (hβO : M.mem β Oc) (ne : β ≠ δ) :
    ∃ o, M.mem (M.quad j.1 β q1 o) P ∧ M.mem o N := by
  rcases (cd.hO β).mp hβO with e | h
  · exact (ne e).elim
  · exact h

/-- Two names of the same rank and formula whose parameters have equivalent values are
equivalent in the order of the names. -/
theorem tie_of_vals (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j) {n n' ρ u u' : V} {k : M.Num}
    (hn : M.NameOf P io j n ρ k u) (hn' : M.NameOf P io j n' ρ k u') (hρ : M.mem (M.op ρ ρ) th)
    (hv : ∀ i : M.Num, i ≤ k → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ u i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d ρ u' i.1 e' ∧
      M.LeV Pr e e' ∧ M.LeV Pr e' e) :
    M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr := by
  rw [M.pr_iff hd hPr hn hn' hρ, M.pr_iff hd hPr hn' hn hρ]
  refine ⟨Or.inr ⟨rfl, Or.inr ⟨rfl, fun hl => ?_⟩⟩, Or.inr ⟨rfl, Or.inr ⟨rfl, fun hl => ?_⟩⟩⟩
  · obtain ⟨i, hi, e', e, v', v, l1, l2, -⟩ := hl
    obtain ⟨a, a', w, w', m1, m2⟩ := hv i hi
    rw [M.val_unique hd v w, M.val_unique hd v' w'] at l2
    exact l2 m1
  · obtain ⟨i, hi, e', e, v', v, l1, l2, -⟩ := hl
    obtain ⟨a, a', w, w', m1, m2⟩ := hv i hi
    rw [M.val_unique hd v w', M.val_unique hd v' w] at l2
    exact l2 m2

/-- **The step for surjectivity**: every name of rank below the collapse of `ρ` denotes the
same set as the image of a name of rank below `ρ` in `N`. -/
theorem step_surj (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ ρb : V}
    (lower : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β) (hρO : M.mem ρ Oc) (hH : M.mem (M.op ρ ρb) H) {m' : V}
    (hm : M.InNRaw P th io M.nat j.1 ρb m') : ∃ n n', M.InNRaw P th io M.nat j.1 ρ n ∧ M.PiRel P PiS j n n' ∧ M.SimRaw P j.1 tp F n' m' := by
  obtain ⟨γ, rm, ltγ, neγ⟩ := M.inN_rank hm
  obtain ⟨β, ltβ, neβ, hHβ⟩ := M.coll_range cd.hd.hth cd.hH hH ltγ neγ
  have hβ := (cd.hd.hth.fld _ _ ltβ).1
  have hγ := (M.coll_dom cd.hH hHβ).2.2
  obtain ⟨ltδ, neδ⟩ := M.cond_below cd hρO ltβ neβ
  obtain ⟨o, ho, hoN⟩ := M.cond_ord cd (M.coll_dom cd.hH hHβ).2.1 neδ
  obtain ⟨c, u', hm'⟩ := M.rank_nameOf rm
  have CAβ := lower β ltβ neβ
  obtain ⟨g, -, hg0⟩ := M.comp
    (σW [(0, 4), (6, 5), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (167, 5), (169, 3)])
    (Fml.ex 326 (Fml.ex 327 (.and (fPr 0 326 327) (.and (.mem 326 27) (.and (Fml.or (Fml.ex 65 (.and (.eq 65 250) (fInN 327))) (.eq 327 26)) (.and (.mem 327 169) (Fml.ex 328 (Fml.ex 329 (.and (fVal 338 341 326 329) (.and (fPi 327 328) (fSim 328 329))))))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 167 PiS) 169 N) 250 β) 338 γ) 341 u')
  have hg1 : ∀ q, M.mem q g ↔ ∃ i e, q = M.op i e ∧ M.mem i M.nat ∧ (M.InNRaw P th io M.nat j.1 β e ∨ e = d) ∧
      M.mem e N ∧ ∃ et e', M.ValRaw P th io M.nat Nt j.1 d γ u' i e' ∧ M.PiRel P PiS j e et ∧ M.SimRaw P j.1 tp F et e' := by
    intro q
    rw [hg0 q]
    simp [Sat, M.sat_or, M.sat_ex, M.sat_fPr', M.sat_fVal, M.sat_fInN, M.sat_fPi, M.sat_fSim,
      Function.update_apply, PiRel]
  have hg : ∀ i e, M.mem (M.op i e) g ↔ M.mem i M.nat ∧ (M.InNRaw P th io M.nat j.1 β e ∨ e = d) ∧
      M.mem e N ∧ ∃ et e', M.ValRaw P th io M.nat Nt j.1 d γ u' i e' ∧ M.PiRel P PiS j e et ∧ M.SimRaw P j.1 tp F et e' := by
    intro i e
    constructor
    · intro h
      obtain ⟨i', e'', eq, h'⟩ := (hg1 _).mp h
      obtain ⟨e1, e2⟩ := M.op_inj eq
      rw [e1, e2]
      exact h'
    · intro h
      exact (hg1 _).mpr ⟨i, e, rfl, h⟩
  obtain ⟨u, huR, hcode⟩ := M.seq_code cd.hd.hP cd.hd.hj ⟨d, M.d_rung cd.hd⟩ cd.hd.nt_zero
    cd.hd.nt_succ (c + 1) g (fun k hk => by
      obtain ⟨e', ve'⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) γ u' k.1
      by_cases hN : M.InNRaw P th io M.nat j.1 γ e'
      · obtain ⟨e, et, heN, pe, hs⟩ := M.ca_surj CAβ hHβ hN
        exact ⟨e, M.inN_rung cd.hd heN, (hg k.1 e).mpr ⟨k.2, Or.inl heN, M.pi_mem cd pe, et, e',
          ve', pe, hs⟩⟩
      · have hed : e' = d := (M.val_cases ve').resolve_left hN
        exact ⟨d, M.d_rung cd.hd, (hg k.1 d).mpr ⟨k.2, Or.inr rfl, cd.hdN, d, e', ve',
          M.pi_dd cd, by rw [hed]; exact M.inN_refl cd.hd (cd.hsub d cd.hdN)⟩⟩)
  have hval : ∀ i : M.Num, i ≤ c → ∃ a, M.ValRaw P th io M.nat Nt j.1 d β u i.1 a ∧ M.mem a N ∧
      ∃ et e', M.ValRaw P th io M.nat Nt j.1 d γ u' i.1 e' ∧ M.PiRel P PiS j a et ∧ M.SimRaw P j.1 tp F et e' := by
    intro i hi
    obtain ⟨a, hga, hnt⟩ := hcode i (add_le_add hi (le_refl 1))
    obtain ⟨-, hcase, haN, rest⟩ := (hg i.1 a).mp hga
    refine ⟨a, ?_, haN, rest⟩
    rcases M.val_of_nth cd.hd (α := β) hnt with ⟨-, h⟩ | ⟨hN, h⟩
    · exact h
    · rw [hcase.resolve_left hN]
      exact h
  obtain ⟨n, hn⟩ := M.nameOf_exists cd.hd hβ huR c
  have hnN : M.mem n N := cd.hcl.2.2.1 n β c.1 u o ho hoN ltδ neδ ((M.nameR_iff c).mpr hn)
    (fun i e hi hle hv => by
      obtain ⟨a, va, haN, -⟩ := hval ⟨i, hi⟩ ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ c).mp hle)
      rw [M.val_unique cd.hd hv va]
      exact haN)
  obtain ⟨nt, pn⟩ := M.pi_tot cd hnN
  obtain ⟨β', βb', c', ut, ut', -, -, hH', hn0, hnt, hvn⟩ := M.pi_unpack cd pn
  obtain ⟨eβ, ec, eu⟩ := M.nameOf_unique cd.hd hn0 hn
  subst eβ
  subst ec
  subst eu
  have eγ := M.coll_fun cd.hd.hth cd.hH hH' hHβ
  subst eγ
  refine ⟨n, nt, M.rank_inN (M.nameOf_rank hn) ltβ neβ, pn,
    M.name_sim_of_vals cd.hd hnt hm' hγ (fun i hi => ?_)⟩
  have hic : i ≤ c' := le_trans (M.le_add_one i) hi
  obtain ⟨e, e2, v, v2, hrel⟩ := hvn i hic
  obtain ⟨a, va, haN, et, e', ve', pa, hs⟩ := hval i hic
  have ea := M.val_unique cd.hd v va
  have pa2 : M.PiRel P PiS j a e2 := by
    rcases hrel with ⟨h1, h2⟩ | ⟨-, h⟩
    · rw [← ea, h1, h2]
      exact M.pi_dd cd
    · rw [← ea]
      exact h
  obtain ⟨t1, t2⟩ := M.pi_tie cd pa2 pa
  exact ⟨e2, e', v2, ve', M.sim_trans cd.hd (M.tie_sim cd.hd cd.hPr t1 t2) hs⟩

/-- **The step for canonical names**: every canonical name of rank below the collapse of `ρ`
is equivalent, in the order of the names, to the image of a canonical name of rank below `ρ`
in `N`. -/
theorem step_can (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ ρb : V}
    (lower : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β) (hρO : M.mem ρ Oc) (hH : M.mem (M.op ρ ρb) H) {m' : V}
    (hm : M.InNRaw P th io M.nat j.1 ρb m') (hc : M.IsCan P j.1 tp F Pr m') :
    ∃ n n', M.InNRaw P th io M.nat j.1 ρ n ∧ M.PiRel P PiS j n n' ∧ M.IsCan P j.1 tp F Pr n ∧ M.mem (M.op n' m') Pr ∧ M.mem (M.op m' n') Pr := by
  obtain ⟨γ, rm, ltγ, neγ⟩ := M.inN_rank hm
  obtain ⟨β, ltβ, neβ, hHβ⟩ := M.coll_range cd.hd.hth cd.hH hH ltγ neγ
  have hβ := (cd.hd.hth.fld _ _ ltβ).1
  have hγ := (M.coll_dom cd.hH hHβ).2.2
  obtain ⟨ltδ, neδ⟩ := M.cond_below cd hρO ltβ neβ
  obtain ⟨o, ho, hoN⟩ := M.cond_ord cd (M.coll_dom cd.hH hHβ).2.1 neδ
  obtain ⟨c, u', hm'⟩ := M.rank_nameOf rm
  have CAβ := lower β ltβ neβ
  by_cases hne : ∃ z, M.InNRaw P th io M.nat j.1 γ z
  · obtain ⟨g, -, hg0⟩ := M.comp
      (σW [(0, 4), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (162, 5), (167, 5)])
      (Fml.ex 326 (Fml.ex 327 (.and (fPr 0 326 327) (.and (.mem 326 27) (.and (Fml.ex 65 (.and (.eq 65 250) (fInN 327))) (Fml.ex 328 (Fml.ex 329 (.and (fVal 338 341 326 329) (.and (fPi 327 328) (.and (fApp 162 328 329) (fApp 162 329 328))))))))))) 0 rfl
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 162 Pr) 167 PiS) 250 β) 338 γ) 341 u')
    have hg1 : ∀ q, M.mem q g ↔ ∃ i e, q = M.op i e ∧ M.mem i M.nat ∧ M.InNRaw P th io M.nat j.1 β e ∧
        ∃ et e', M.ValRaw P th io M.nat Nt j.1 d γ u' i e' ∧ M.PiRel P PiS j e et ∧ M.mem (M.op et e') Pr ∧ M.mem (M.op e' et) Pr := by
      intro q
      rw [hg0 q]
      simp [Sat, M.sat_ex, M.sat_fPr', M.sat_fVal, M.sat_fInN, M.sat_fPi, M.sat_fApp',
        Function.update_apply, PiRel]
    have hg : ∀ i e, M.mem (M.op i e) g ↔ M.mem i M.nat ∧ M.InNRaw P th io M.nat j.1 β e ∧
        ∃ et e', M.ValRaw P th io M.nat Nt j.1 d γ u' i e' ∧ M.PiRel P PiS j e et ∧ M.mem (M.op et e') Pr ∧ M.mem (M.op e' et) Pr := by
      intro i e
      constructor
      · intro h
        obtain ⟨i', e'', eq, h'⟩ := (hg1 _).mp h
        obtain ⟨e1, e2⟩ := M.op_inj eq
        rw [e1, e2]
        exact h'
      · intro h
        exact (hg1 _).mpr ⟨i, e, rfl, h⟩
    obtain ⟨u, huR, hcode⟩ := M.seq_code cd.hd.hP cd.hd.hj ⟨d, M.d_rung cd.hd⟩ cd.hd.nt_zero
      cd.hd.nt_succ (c + 1) g (fun k hk => by
        obtain ⟨e', ve'⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) γ u' k.1
        have hce := M.can_vals cd.hd cd.hPr hc hm' hγ hne (M.le_of_succ_le_succ hk) ve'
        obtain ⟨e, et, heN, pe, -, t1, t2⟩ := M.ca_can CAβ hHβ
          (M.val_inN_of_ne cd.hd (M.val_cases ve') hne) hce
        exact ⟨e, M.inN_rung cd.hd heN, (hg k.1 e).mpr ⟨k.2, heN, et, e', ve', pe, t1, t2⟩⟩)
    have hval : ∀ i : M.Num, i ≤ c → ∃ a, M.ValRaw P th io M.nat Nt j.1 d β u i.1 a ∧ M.InNRaw P th io M.nat j.1 β a ∧
        ∃ et e', M.ValRaw P th io M.nat Nt j.1 d γ u' i.1 e' ∧ M.PiRel P PiS j a et ∧ M.mem (M.op et e') Pr ∧ M.mem (M.op e' et) Pr := by
      intro i hi
      obtain ⟨a, hga, hnt⟩ := hcode i (add_le_add hi (le_refl 1))
      obtain ⟨-, haN, rest⟩ := (hg i.1 a).mp hga
      exact ⟨a, Or.inl ⟨hnt, haN⟩, haN, rest⟩
    obtain ⟨n, hn⟩ := M.nameOf_exists cd.hd hβ huR c
    have hnN : M.mem n N := cd.hcl.2.2.1 n β c.1 u o ho hoN ltδ neδ ((M.nameR_iff c).mpr hn)
      (fun i e hi hle hv => by
        obtain ⟨a, va, -, et, e', -, pa, -⟩ := hval ⟨i, hi⟩
          ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ c).mp hle)
        rw [M.val_unique cd.hd hv va]
        exact M.pi_mem cd pa)
    have hnρ : M.InNRaw P th io M.nat j.1 ρ n := M.rank_inN (M.nameOf_rank hn) ltβ neβ
    obtain ⟨nt, pn⟩ := M.pi_tot cd hnN
    obtain ⟨β', βb', c', ut, ut', -, -, hH', hn0, hnt, hvn⟩ := M.pi_unpack cd pn
    obtain ⟨eβ, ec, eu⟩ := M.nameOf_unique cd.hd hn0 hn
    subst eβ
    subst ec
    subst eu
    have eγ := M.coll_fun cd.hd.hth cd.hH hH' hHβ
    subst eγ
    have htie : M.mem (M.op nt m') Pr ∧ M.mem (M.op m' nt) Pr := by
      refine M.tie_of_vals cd.hd cd.hPr hnt hm' hγ (fun i hi => ?_)
      obtain ⟨e, e2, v, v2, hrel⟩ := hvn i hi
      obtain ⟨a, va, haN, et, e', ve', pa, t1, t2⟩ := hval i hi
      have ea := M.val_unique cd.hd v va
      have pa2 : M.PiRel P PiS j a e2 := by
        rcases hrel with ⟨h1, h2⟩ | ⟨-, h⟩
        · rw [← ea, h1, h2]
          exact M.pi_dd cd
        · rw [← ea]
          exact h
      obtain ⟨s1, s2⟩ := M.pi_tie cd pa2 pa
      exact ⟨e2, e', v2, ve', Or.inr (M.pr_trans cd.hd cd.hPr s1 t1),
        Or.inr (M.pr_trans cd.hd cd.hPr t2 s2)⟩
    refine ⟨n, nt, hnρ, pn, ?_, htie.1, htie.2⟩
    by_contra hnc
    obtain ⟨n0, hn0N, hc0, hs0⟩ := M.cond_can cd hnN
    have p0 : M.mem (M.op n0 n) Pr := hc0.2 n (M.sim_symm cd.hd hs0)
    have np : ¬ M.mem (M.op n n0) Pr := fun h => hnc (M.can_of_tie cd.hd cd.hPr hc0 p0 h)
    have hn0ρ := M.can_inN cd.hd cd.hPr hnρ hc0 hs0
    obtain ⟨n0t, pn0⟩ := M.pi_tot cd hn0N
    have s1 : M.SimRaw P j.1 tp F nt n0t := (M.step_sim cd lower hnρ hn0ρ pn pn0).mp hs0
    have s2 : M.SimRaw P j.1 tp F m' n0t :=
      M.sim_trans cd.hd (M.sim_symm cd.hd (M.tie_sim cd.hd cd.hPr htie.1 htie.2)) s1
    exact np ((M.pi_pr cd pn pn0).mpr (M.pr_trans cd.hd cd.hPr htie.1 (hc.2 n0t s2)))
  · -- `γ` is the least stage
    obtain ⟨α0, f0, u0, q0, k1, k2, ⟨k, hk⟩, hleast⟩ := cd.hd.d_spec
    have rd : M.RankIs P io M.nat j.1 α0 d := ⟨f0, u0, q0, k1, k2, k, (cd.hd.io_dom _ _ hk).1, hk⟩
    have eα : α0 = γ := by
      by_contra e
      exact hne ⟨d, M.d_inN cd.hd (hleast γ hγ) e⟩
    obtain ⟨-, -, -, od, hod, hodN⟩ := M.cond_rank cd cd.hdN rd
    rw [eα] at hod
    have hall : ∀ β', M.mem (M.op β' γ) th → ∃ o, M.mem (M.quad j.1 β' q1 o) P ∧ M.mem o N := by
      intro β' h
      have e : β' = γ := by
        by_contra e
        exact hne ⟨d, M.d_inN cd.hd h e⟩
      rw [e]
      exact ⟨od, hod, hodN⟩
    obtain ⟨hmN, pm⟩ := M.pi_self cd hall rm hγ
    have hγβ : M.mem (M.op γ β) th := by
      rw [← eα]
      exact hleast β hβ
    have hmρ : M.InNRaw P th io M.nat j.1 ρ m' := M.rank_inN rm (cd.hd.hth.trans _ _ _ hγβ ltβ) (fun e => by
      rw [e] at hγβ
      exact neβ (cd.hd.hth.antisymm _ _ ltβ hγβ))
    have hrefl := M.pr_refl cd.hd cd.hPr rm hγ
    exact ⟨m', m', hmρ, pm, hc, hrefl, hrefl⟩

/-- The image of a canonical name is canonical. -/
theorem step_can_img (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ ρb : V}
    (lower : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β) (hρO : M.mem ρ Oc) (hH : M.mem (M.op ρ ρb) H) {n n' : V}
    (hn : M.InNRaw P th io M.nat j.1 ρ n) (pn : M.PiRel P PiS j n n') (hc : M.IsCan P j.1 tp F Pr n) : M.IsCan P j.1 tp F Pr n' := by
  have hn' := M.pi_inN cd pn hn hH
  obtain ⟨m', hcm, hsm⟩ := M.exists_can cd.hd cd.hPr (M.inN_refl cd.hd hn')
  have hm' := M.can_inN cd.hd cd.hPr hn' hcm hsm
  obtain ⟨n1, n1t, hn1, pn1, hc1, t1, t2⟩ := M.step_can cd lower hρO hH hm' hcm
  have s1 : M.SimRaw P j.1 tp F n1t n' :=
    M.sim_trans cd.hd (M.tie_sim cd.hd cd.hPr t1 t2) (M.sim_symm cd.hd hsm)
  have s2 : M.SimRaw P j.1 tp F n1 n := (M.step_sim cd lower hn1 hn pn1 pn).mpr s1
  obtain ⟨q1, q2⟩ := M.can_tie cd.hd hc1 hc s2
  have r1 := (M.pi_pr cd pn1 pn).mp q1
  have r2 := (M.pi_pr cd pn pn1).mp q2
  exact M.can_of_tie cd.hd cd.hPr hcm (M.pr_trans cd.hd cd.hPr t2 r1)
    (M.pr_trans cd.hd cd.hPr r2 t1)

/-- **The step for the canonical well-ordering**: it is preserved by the collapsing map, in
both directions. -/
theorem step_lt (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ ρb : V}
    (lower : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β) (hρO : M.mem ρ Oc) (hH : M.mem (M.op ρ ρb) H) {n1 n2 n1' n2' : V}
    (hN1 : M.InNRaw P th io M.nat j.1 ρ n1) (hN2 : M.InNRaw P th io M.nat j.1 ρ n2) (p1 : M.PiRel P PiS j n1 n1') (p2 : M.PiRel P PiS j n2 n2') :
    M.Lt P j.1 tp F Pr n1 n2 ↔ M.Lt P j.1 tp F Pr n1' n2' := by
  constructor
  · rintro ⟨a0, b0, ca, cb, sa, sb, pp, np⟩
    have ha0N : M.mem a0 N := cd.hcl.2.2.2.1 n1 a0 (M.pi_mem cd p1) ca sa
    have hb0N : M.mem b0 N := cd.hcl.2.2.2.1 n2 b0 (M.pi_mem cd p2) cb sb
    have ha0 := M.can_inN cd.hd cd.hPr hN1 ca sa
    have hb0 := M.can_inN cd.hd cd.hPr hN2 cb sb
    obtain ⟨a0t, pa⟩ := M.pi_tot cd ha0N
    obtain ⟨b0t, pb⟩ := M.pi_tot cd hb0N
    exact ⟨a0t, b0t, M.step_can_img cd lower hρO hH ha0 pa ca,
      M.step_can_img cd lower hρO hH hb0 pb cb, (M.step_sim cd lower hN1 ha0 p1 pa).mp sa,
      (M.step_sim cd lower hN2 hb0 p2 pb).mp sb, (M.pi_pr cd pa pb).mp pp,
      fun h => np ((M.pi_pr cd pb pa).mpr h)⟩
  · rintro ⟨a0', b0', ca', cb', sa', sb', pp', np'⟩
    have ha0' := M.can_inN cd.hd cd.hPr (M.pi_inN cd p1 hN1 hH) ca' sa'
    have hb0' := M.can_inN cd.hd cd.hPr (M.pi_inN cd p2 hN2 hH) cb' sb'
    obtain ⟨a, at', ha, pa, hca, ta1, ta2⟩ := M.step_can cd lower hρO hH ha0' ca'
    obtain ⟨b, bt, hb, pb, hcb, tb1, tb2⟩ := M.step_can cd lower hρO hH hb0' cb'
    have sa : M.SimRaw P j.1 tp F n1 a := (M.step_sim cd lower hN1 ha p1 pa).mpr
      (M.sim_trans cd.hd sa' (M.sim_symm cd.hd (M.tie_sim cd.hd cd.hPr ta1 ta2)))
    have sb : M.SimRaw P j.1 tp F n2 b := (M.step_sim cd lower hN2 hb p2 pb).mpr
      (M.sim_trans cd.hd sb' (M.sim_symm cd.hd (M.tie_sim cd.hd cd.hPr tb1 tb2)))
    refine ⟨a, b, hca, hcb, sa, sb, (M.pi_pr cd pa pb).mpr
      (M.pr_trans cd.hd cd.hPr ta1 (M.pr_trans cd.hd cd.hPr pp' tb2)), fun h => np' ?_⟩
    have h' := (M.pi_pr cd pb pa).mp h
    exact M.pr_trans cd.hd cd.hPr tb2 (M.pr_trans cd.hd cd.hPr h' ta1)

end cond4

/-! ## Condensation: elementarity, and the induction along the stages -/

/-- The statement of elementarity for the formulas up to `n`, in raw form. -/
def ElemR (P th io nat Nt j d ad F PiS ρ ρb n : V) : Prop :=
  ∀ c, M.mem c nat → (∃ x, M.mem x nat ∧ M.mem (M.trip c x n) ad) → ∀ t t',
    (∀ i, M.mem i nat → (∃ x, M.mem x nat ∧ M.mem (M.trip i x c) ad) → ∃ e e',
      M.ValRaw P th io nat Nt j d ρ t i e ∧ M.ValRaw P th io nat Nt j d ρb t' i e' ∧
      ∃ β z, M.mem (M.quad j e e' z) P ∧ M.mem (M.op β z) PiS) →
    (M.TrueAtR P io F j ρ c t ↔ M.TrueAtR P io F j ρb c t')

/-- `ElemR`, with `ρ`, `ρb`, `n` the names `250`, `338`, `342`. -/
def elemFml : Fml :=
  .all 301 (Fml.imp (.mem 301 27) (Fml.imp (fLeN 301 342) (.all 340 (.all 341 (Fml.imp (.all 326
    (Fml.imp (.mem 326 27) (Fml.imp (fLeN 326 301) (Fml.ex 327 (Fml.ex 328 (.and (fVal 250 340
    326 327) (.and (fVal 338 341 326 328) (fPi 327 328)))))))) (Fml.iff (Fml.ex 259 (Fml.ex 260
    (.and (fApp 24 301 259) (.and (fApp4 20 25 250 259 260) (fApp 6 260 340))))) (Fml.ex 259
    (Fml.ex 260 (.and (fApp 24 301 259) (.and (fApp4 20 25 338 259 260) (fApp 6 260
    341)))))))))))

theorem sat_elemFml (ρ : ℕ → V) : Sat M.mem M.isSet elemFml ρ ↔
    M.ElemR (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 6) (ρ 167) (ρ 250) (ρ 338)
      (ρ 342) := by
  simp [elemFml, ElemR, TrueAtR, Sat, M.sat_imp, M.sat_iff, M.sat_ex, M.sat_fPi, M.sat_fVal,
    M.sat_fLeN, M.sat_fApp', M.sat_fApp4', Function.update_apply]

section cond5

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {N δ Oc H PiS G ν : V}
variable {q1 : V}

/-- Elementarity for atomic formulas. -/
theorem elem_rel (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ ρb : V}
    (lower : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β) (hρO : M.mem ρ Oc) (hH : M.mem (M.op ρ ρb) H)
    (hne : ∃ z, M.InNRaw P th io M.nat j.1 ρ z) (r v w : M.Num) (t t' : V)
    (hv : (∀ i : M.Num, i ≤ M.cRel r v w → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d ρb t' i.1 e' ∧ M.PiRel P PiS j e e')) :
    M.TrueAt P io F j.1 ρ (M.cRel r v w) t ↔ M.TrueAt P io F j.1 ρb (M.cRel r v w) t' := by
  obtain ⟨a, a', va, va', pa⟩ := hv v (M.le_cRel_left r v w)
  obtain ⟨b, b', vb, vb', pb⟩ := hv w (M.le_cRel_right r v w)
  have haN := M.val_inN_of_ne cd.hd (M.val_cases va) hne
  have hbN := M.val_inN_of_ne cd.hd (M.val_cases vb) hne
  have ha'N := M.pi_inN cd pa haN hH
  have hb'N := M.pi_inN cd pb hbN hH
  have hρ := (M.coll_dom cd.hH hH).1
  have hρb := (M.coll_dom cd.hH hH).2.2
  by_cases h1 : r = 1
  · rw [h1]
    exact ⟨fun h => (M.hier_T_false cd.hd cd.hNu v w t h).elim,
      fun h => (M.hier_T_false cd.hd cd.hNu v w t' h).elim⟩
  by_cases h2 : r = 2
  · rw [h2, M.hier_lt cd.hd cd.hPr, M.hier_lt cd.hd cd.hPr]
    constructor
    · rintro ⟨-, a1, b1, w1, w2, -, -, hlt⟩
      rw [M.val_unique cd.hd w1 va, M.val_unique cd.hd w2 vb] at hlt
      exact ⟨hρb, a', b', va', vb', ha'N, hb'N,
        (M.step_lt cd lower hρO hH haN hbN pa pb).mp hlt⟩
    · rintro ⟨-, a1, b1, w1, w2, -, -, hlt⟩
      rw [M.val_unique cd.hd w1 va', M.val_unique cd.hd w2 vb'] at hlt
      exact ⟨hρ, a, b, va, vb, haN, hbN, (M.step_lt cd lower hρO hH haN hbN pa pb).mpr hlt⟩
  · rw [M.hier_relE cd.hd r v w h1 h2, M.hier_relE cd.hd r v w h1 h2]
    constructor
    · rintro ⟨-, a1, b1, w1, w2, he⟩
      rw [M.val_unique cd.hd w1 va, M.val_unique cd.hd w2 vb] at he
      exact ⟨hρb, a', b', va', vb', (M.step_eps cd lower haN hbN pa pb).mp he⟩
    · rintro ⟨-, a1, b1, w1, w2, he⟩
      rw [M.val_unique cd.hd w1 va', M.val_unique cd.hd w2 vb'] at he
      exact ⟨hρ, a, b, va, vb, (M.step_eps cd lower haN hbN pa pb).mpr he⟩

/-- Elementarity for a quantified formula, from elementarity for its body. -/
theorem elem_all (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ ρb : V}
    (lower : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β) (hρO : M.mem ρ Oc) (hH : M.mem (M.op ρ ρb) H)
    (v c' : M.Num)
    (ih : ∀ t t', (∀ i : M.Num, i ≤ c' → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d ρb t' i.1 e' ∧ M.PiRel P PiS j e e') → (M.TrueAt P io F j.1 ρ c' t ↔ M.TrueAt P io F j.1 ρb c' t'))
    (t t' : V) (hv : (∀ i : M.Num, i ≤ M.cAll v c' → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d ρb t' i.1 e' ∧ M.PiRel P PiS j e e')) :
    M.TrueAt P io F j.1 ρ (M.cAll v c') t ↔ M.TrueAt P io F j.1 ρb (M.cAll v c') t' := by
  have hρ := (M.coll_dom cd.hH hH).1
  have hρb := (M.coll_dom cd.hH hH).2.2
  have hvC : v ≤ M.cAll v c' := M.le_cAll_var v c'
  have hcC : c' ≤ M.cAll v c' := M.le_cAll_body v c'
  rw [M.hier_all_ex cd.hd, M.hier_all_ex cd.hd]
  constructor
  · rintro ⟨-, hall⟩
    refine ⟨hρb, fun a' ha' => ?_⟩
    obtain ⟨a, at', haN, pa, hsa⟩ := M.step_surj cd lower hρO hH ha'
    obtain ⟨t1, hag1, htr1⟩ := hall a haN
    have hat := M.pi_inN cd pa haN hH
    obtain ⟨t1t, hag1t⟩ := M.exists_upd cd.hd hat t' v.1 (M.cAll v c')
    have htr1t : M.TrueAt P io F j.1 ρb c' t1t := by
      refine (ih t1 t1t (fun i hi => ?_)).mp htr1
      by_cases e : i = v
      · rw [e]
        exact ⟨a, at', M.agree_same hag1 hvC, M.agree_same hag1t hvC, pa⟩
      · obtain ⟨e1, e1', w1, w1', p1⟩ := hv i (le_trans hi hcC)
        exact ⟨e1, e1', M.agree_other hag1 (le_trans hi hcC) e w1,
          M.agree_other hag1t (le_trans hi hcC) e w1', p1⟩
    obtain ⟨t2, hag2⟩ := M.exists_upd cd.hd ha' t' v.1 (M.cAll v c')
    refine ⟨t2, hag2, (M.inv_hier cd.hd c' t1t t2 (fun i hi => ?_)).mp htr1t⟩
    by_cases e : i = v
    · rw [e]
      exact ⟨at', a', M.agree_same hag1t hvC, M.agree_same hag2 hvC, hsa⟩
    · obtain ⟨g, vg⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) ρb t' i.1
      exact ⟨g, g, M.agree_other hag1t (le_trans hi hcC) e vg,
        M.agree_other hag2 (le_trans hi hcC) e vg, M.val_sim_refl cd.hd hρb vg⟩
  · rintro ⟨-, hall'⟩
    refine ⟨hρ, fun a ha => ?_⟩
    by_contra hcon
    have hex : ∃ w, M.InNRaw P th io M.nat j.1 ρ w ∧ ¬ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F ρ c'.1 v.1 t w := by
      refine ⟨a, ha, fun htu => hcon ?_⟩
      obtain ⟨t1, hag1⟩ := M.exists_upd cd.hd ha t v.1 (M.cAll v c')
      exact ⟨t1, hag1, (M.trueUpd_iff cd.hd c' v (M.agree_mono hag1 hcC)).mp htu⟩
    have hvals : ∀ i : M.Num, i ≤ c' → ∀ e, M.ValRaw P th io M.nat Nt j.1 d ρ t i.1 e → M.mem e N := by
      intro i hi e hve
      obtain ⟨e1, e1', w1, -, p1⟩ := hv i (le_trans hi hcC)
      rw [M.val_unique cd.hd hve w1]
      exact M.pi_mem cd p1
    obtain ⟨a0, ha0N, ha0, hntu⟩ := M.cond_lw_neg cd hρO c' v hvals hex
    obtain ⟨a0t, pa0⟩ := M.pi_tot cd ha0N
    have ha0t := M.pi_inN cd pa0 ha0 hH
    obtain ⟨t1', hag1', htr1'⟩ := hall' a0t ha0t
    obtain ⟨t1, hag1⟩ := M.exists_upd cd.hd ha0 t v.1 (M.cAll v c')
    have htr1 : M.TrueAt P io F j.1 ρ c' t1 := by
      refine (ih t1 t1' (fun i hi => ?_)).mpr htr1'
      by_cases e : i = v
      · rw [e]
        exact ⟨a0, a0t, M.agree_same hag1 hvC, M.agree_same hag1' hvC, pa0⟩
      · obtain ⟨e1, e1', w1, w1', p1⟩ := hv i (le_trans hi hcC)
        exact ⟨e1, e1', M.agree_other hag1 (le_trans hi hcC) e w1,
          M.agree_other hag1' (le_trans hi hcC) e w1', p1⟩
    exact hntu ((M.trueUpd_iff cd.hd c' v (M.agree_mono hag1 hcC)).mpr htr1)

/-- Elementarity for a formula, from elementarity for the smaller formulas. -/
theorem elem_core (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ ρb : V}
    (lower : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β) (hρO : M.mem ρ Oc) (hH : M.mem (M.op ρ ρb) H)
    (hne : ∃ z, M.InNRaw P th io M.nat j.1 ρ z) (c : M.Num)
    (ih : ∀ c' : M.Num, c' + 1 ≤ c → ∀ t t', (∀ i : M.Num, i ≤ c' → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d ρb t' i.1 e' ∧ M.PiRel P PiS j e e') →
      (M.TrueAt P io F j.1 ρ c' t ↔ M.TrueAt P io F j.1 ρb c' t'))
    (t t' : V) (hv : (∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d ρb t' i.1 e' ∧ M.PiRel P PiS j e e')) : M.TrueAt P io F j.1 ρ c t ↔ M.TrueAt P io F j.1 ρb c t' := by
  have hρ := (M.coll_dom cd.hH hH).1
  have hρb := (M.coll_dom cd.hH hH).2.2
  have cases : ((∃ r v w, c = M.cRel r v w) ∨ (∃ c', c = M.cNeg c') ∨
      (∃ c' c'', c = M.cAnd c' c'') ∨ ∃ v c', c = M.cAll v c') →
      (M.TrueAt P io F j.1 ρ c t ↔ M.TrueAt P io F j.1 ρb c t') := by
    rintro (⟨r, v, w, e⟩ | ⟨c', e⟩ | ⟨c', c'', e⟩ | ⟨v, c', e⟩)
    · subst e
      exact M.elem_rel cd lower hρO hH hne r v w t t' hv
    · subst e
      have h1 := ih c' (M.lt_pairN_right c' (le_refl 1)) t t'
        (fun i hi => hv i (le_trans hi (M.le_cNeg c')))
      rw [M.hier_neg cd.hd, M.hier_neg cd.hd, h1]
      exact ⟨fun h => ⟨hρb, h.2⟩, fun h => ⟨hρ, h.2⟩⟩
    · subst e
      have h1 := ih c' (le_trans (add_le_add (M.le_pairN_left c' c'') (le_refl 1))
        (M.lt_pairN_right _ M.one_le_two')) t t'
        (fun i hi => hv i (le_trans hi (M.le_cAnd_left c' c'')))
      have h2 := ih c'' (le_trans (add_le_add (M.le_pairN_right c' c'') (le_refl 1))
        (M.lt_pairN_right _ M.one_le_two')) t t'
        (fun i hi => hv i (le_trans hi (M.le_cAnd_right c' c'')))
      rw [M.hier_and cd.hd, M.hier_and cd.hd, h1, h2]
      exact ⟨fun h => ⟨hρb, h.2⟩, fun h => ⟨hρ, h.2⟩⟩
    · subst e
      exact M.elem_all cd lower hρO hH v c'
        (fun t1 t1' h => ih c' (le_trans (add_le_add (M.le_pairN_right v c') (le_refl 1))
          (M.lt_pairN_right _ M.one_le_three')) t1 t1' h) t t' hv
  exact ⟨fun h => (cases (M.trueAt_shape cd.hd h)).mp h,
    fun h => (cases (M.trueAt_shape cd.hd h)).mpr h⟩

/-- **The step for elementarity.** -/
theorem step_elem (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ ρb : V}
    (lower : ∀ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β) (hρO : M.mem ρ Oc) (hH : M.mem (M.op ρ ρb) H)
    (c : M.Num) (t t' : V) (hv : (∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d ρb t' i.1 e' ∧ M.PiRel P PiS j e e')) : M.TrueAt P io F j.1 ρ c t ↔ M.TrueAt P io F j.1 ρb c t' := by
  have hρ := (M.coll_dom cd.hH hH).1
  by_cases hne : ∃ z, M.InNRaw P th io M.nat j.1 ρ z
  · have conv : ∀ n : M.Num, M.ElemR P th io M.nat Nt j.1 d M.adG F PiS ρ ρb n.1 ↔
        ∀ c : M.Num, c ≤ n → ∀ t t', (∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d ρb t' i.1 e' ∧ M.PiRel P PiS j e e') → (M.TrueAt P io F j.1 ρ c t ↔ M.TrueAt P io F j.1 ρb c t') := by
      intro n
      constructor
      · intro h c hc t t' hv
        exact h c.1 c.2 ((M.leRaw_iff M.adG_spec c n).mpr hc) t t'
          (fun i hi hle => hv ⟨i, hi⟩ ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ c).mp hle))
      · intro h c hcN hle t t' hv
        exact h ⟨c, hcN⟩ ((M.leRaw_iff M.adG_spec ⟨c, hcN⟩ n).mp hle) t t'
          (fun i hi => hv i.1 i.2 ((M.leRaw_iff M.adG_spec i ⟨c, hcN⟩).mpr hi))
    have hsat : ∀ n : M.Num, Sat M.mem M.isSet elemFml (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 162 Pr) 167 PiS) 171 H) 250 ρ) 338 ρb) 342 n.1) ↔
        ∀ c : M.Num, c ≤ n → ∀ t t', (∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d ρ t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d ρb t' i.1 e' ∧ M.PiRel P PiS j e e') → (M.TrueAt P io F j.1 ρ c t ↔ M.TrueAt P io F j.1 ρb c t') := by
      intro n
      rw [M.sat_elemFml, ← conv n]
      simp [Function.update_apply]
    have key := M.num_ind_fml
      (σW [(6, 5), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7), (167, 5)]) elemFml 342 rfl
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 162 Pr) 167 PiS) 171 H) 250 ρ) 338 ρb) ?_ ?_ c
    · exact (hsat c).mp key c (le_refl c) t t' hv
    · rw [show M.zero = (0 : M.Num).1 from rfl, hsat 0]
      intro c hc t t' hv
      have e0 : c = 0 := le_antisymm hc zero_le
      subst e0
      exact M.elem_core cd lower hρO hH hne 0 (fun c' hc' => (M.succ_not_le_zero hc').elim) t t' hv
    · intro k ih
      rw [show M.succ k.1 = (k + 1).1 from (M.val_add_one k).symm, hsat (k + 1)]
      rw [hsat k] at ih
      intro c hc t t' hv
      rcases M.eq_or_succ_le hc with e | e
      · subst e
        exact M.elem_core cd lower hρO hH hne (k + 1)
          (fun c' hc' => ih c' (M.le_of_succ_le_succ hc')) t t' hv
      · exact ih c (M.le_of_succ_le_succ e) t t' hv
  · -- `ρ` is the least stage: then so is its collapse, and all values are the default name
    have eρ : ρb = ρ := by
      by_contra e
      exact hne ⟨d, M.d_inN cd.hd (M.coll_le cd.hd.hth cd.hH hH) e⟩
    rw [eρ] at hv ⊢
    refine M.coin_hier cd.hd c t t' (fun i hi e => ?_)
    obtain ⟨e1, e1', w1, w1', -⟩ := hv i hi
    rw [M.val_eq_d_of_empty (M.val_cases w1) hne] at w1
    rw [M.val_eq_d_of_empty (M.val_cases w1') hne] at w1'
    constructor
    · intro h
      rw [M.val_unique cd.hd h w1]
      exact w1'
    · intro h
      rw [M.val_unique cd.hd h w1']
      exact w1

/-- **Condensation holds at every stage.** -/
theorem cond_all (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {ρ : V}
    (hρ : M.mem (M.op ρ ρ) th) : M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS ρ := by
  have hsat : ∀ α, Sat M.mem M.isSet condAtFml (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 162 Pr) 167 PiS) 171 H) 250 α) ↔ M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS α := by
    intro α
    rw [M.sat_condAtFml]
    simp [Function.update_apply]
  have key := M.wo_ind_fml cd.hd.hth
    (σW [(6, 5), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7), (162, 5), (167, 5),
      (171, 5)]) condAtFml 250 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 162 Pr) 167 PiS) 171 H) (fun α hα ih => ?_) ρ hρ
  · exact (hsat ρ).mp key
  · rw [hsat α]
    have lower : ∀ β, M.mem (M.op β α) th → β ≠ α → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β :=
      fun β h1 h2 => (hsat β).mp (ih β h1 h2)
    refine ⟨fun n1 n2 n1' n2' h1 h2 p1 p2 => M.step_sim cd lower h1 h2 p1 p2, fun ρb hH => ?_⟩
    have hρO := (M.coll_dom cd.hH hH).2.1
    exact ⟨fun m' hm => M.step_surj cd lower hρO hH hm,
      fun m' hm hc => M.step_can cd lower hρO hH hm hc,
      fun c t t' hc hv => M.step_elem cd lower hρO hH ⟨c, hc⟩ t t'
        (fun i hi => hv i.1 i.2 ((M.leRaw_iff M.adG_spec i ⟨c, hc⟩).mpr hi))⟩

end cond5

/-! ## Closed sets: equivalent names, all names; transfer of least witnesses -/

section cond6

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {N δ Oc H PiS G ν : V}
variable {q1 : V}

/-- The marker of the collapse of a stage is an image of the marker of the stage. -/
theorem pi_mark (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {β βb o o' : V}
    (hH : M.mem (M.op β βb) H) (lt : M.mem (M.op β δ) th) (ne : β ≠ δ)
    (ho : M.mem (M.quad j.1 β q1 o) P) (ho' : M.mem (M.quad j.1 βb q1 o') P) : M.PiRel P PiS j o o' := by
  obtain ⟨f, t0, c0, hf, hfq, hv⟩ := cd.hq
  exact M.pi_intro cd lt ne hH ⟨f, q1, ho, hfq, hf⟩ ⟨f, q1, ho', hfq, hf⟩
    (fun i hi => ⟨d, d, hv β i hi, hv βb i hi, Or.inl ⟨rfl, rfl⟩⟩)

/-- A closed set that contains the default name contains, with a name of rank below `ρ`, the
names equivalent to it in the order of the names. -/
theorem closed_tie (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) {X ρ ν' G' : V} (hX : M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr G' X ρ ν') (hdX : M.mem d X)
    {n n' : V} (hn : M.mem n X) (hnρ : M.InNRaw P th io M.nat j.1 ρ n) (t1 : M.mem (M.op n n') Pr)
    (t2 : M.mem (M.op n' n) Pr) : M.mem n' X := by
  obtain ⟨β, rn, ltβ, -⟩ := M.inN_rank hnρ
  have hβ := (hd.hth.fld _ _ ltβ).1
  have hsat : ∀ α, Sat M.mem M.isSet (.all 320 (.all 321 (Fml.imp (fRank 250 320) (Fml.imp (.mem 320 270) (Fml.imp (Fml.ex 65 (.and (.eq 65 271) (fInN 320))) (Fml.imp (fApp 162 320 321) (Fml.imp (fApp 162 321 320) (.mem 321 270))))))))
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 162 Pr) 270 X) 271 ρ) 250 α) ↔
      ∀ n n', M.RankIs P io M.nat j.1 α n → M.mem n X → M.InNRaw P th io M.nat j.1 ρ n → M.mem (M.op n n') Pr →
        M.mem (M.op n' n) Pr → M.mem n' X := by
    intro α
    simp [Sat, M.sat_imp, M.sat_ex, M.sat_fRank, M.sat_fInN, M.sat_fApp', Function.update_apply]
  have key := M.wo_ind_fml hd.hth (σW [(20, 7), (22, 5), (24, 5), (27, 3), (162, 5), (270, 3)])
    (.all 320 (.all 321 (Fml.imp (fRank 250 320) (Fml.imp (.mem 320 270) (Fml.imp (Fml.ex 65 (.and (.eq 65 271) (fInN 320))) (Fml.imp (fApp 162 320 321) (Fml.imp (fApp 162 321 320) (.mem 321 270)))))))) 250 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 162 Pr) 270 X) 271 ρ)
    (fun α hα ih => ?_) β hβ
  · exact (hsat β).mp key n n' rn hn hnρ t1 t2
  · rw [hsat α]
    have ih' : ∀ β', M.mem (M.op β' α) th → β' ≠ α → ∀ n n', M.RankIs P io M.nat j.1 β' n → M.mem n X →
        M.InNRaw P th io M.nat j.1 ρ n → M.mem (M.op n n') Pr → M.mem (M.op n' n) Pr → M.mem n' X :=
      fun β' h1 h2 => (hsat β').mp (ih β' h1 h2)
    intro n n' rn hn hnρ t1 t2
    obtain ⟨α', rn2, ltα, neα⟩ := M.inN_rank hnρ
    have eα := M.rank_unique hd rn rn2
    rw [← eα] at ltα neα
    obtain ⟨ρ1, ρ1', r1, r1', -⟩ := M.pr_names hPr t1
    have e1 := M.rank_unique hd r1 rn
    have e2 := M.tie_rank hd hPr r1 r1' t1 t2
    rw [← e2, e1] at r1'
    obtain ⟨k, u, hname⟩ := M.rank_nameOf rn
    obtain ⟨k', u', hname'⟩ := M.rank_nameOf r1'
    obtain ⟨ek, hties⟩ := M.tie_shape hd hPr hname hname' hα t1 t2
    subst ek
    obtain ⟨o, ho⟩ := M.exists_mark hd hq hα
    have hoX := hX.1 n α o hn rn ho
    refine hX.2.2.1 n' α k.1 u' o ho hoX ltα neα ((M.nameR_iff k).mpr hname')
      (fun i e' hi hle hv' => ?_)
    obtain ⟨g', g, v', v, l1, l2⟩ := hties ⟨i, hi⟩ ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ k).mp hle)
    rw [M.val_unique hd hv' v']
    have hgX : M.mem g X := hX.2.1 n α k.1 u i g hn ((M.nameR_iff k).mpr hname) hi hle v
    by_cases e : g = g'
    · rw [← e]
      exact hgX
    · have p1 : M.mem (M.op g g') Pr := by
        rcases l2 with l | l
        · exact (e l).elim
        · exact l
      have p2 : M.mem (M.op g' g) Pr := by
        rcases l1 with l | l
        · exact (e l.symm).elim
        · exact l
      have hne : ∃ z, M.InNRaw P th io M.nat j.1 α z := by
        rcases M.val_cases v with h | h
        · exact ⟨g, h⟩
        · rcases M.val_cases v' with h' | h'
          · exact ⟨g', h'⟩
          · exact (e (h.trans h'.symm)).elim
      have hgα := M.val_inN_of_ne hd (M.val_cases v) hne
      obtain ⟨β1, rg, lt1, ne1⟩ := M.inN_rank hgα
      exact ih' β1 lt1 ne1 g g' rg hgX (M.inN_mono hd hgα ltα) p1 p2

/-- A closed set that contains the default name and a name of every rank below `ρ` contains
all names of rank below `ρ`. -/
theorem closed_all (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    {X ρ ν' G' : V} (hX : M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr G' X ρ ν') (hdX : M.mem d X)
    (hords : ∀ β', M.mem (M.op β' ρ) th → β' ≠ ρ → ∃ n o, M.mem n X ∧ M.RankIs P io M.nat j.1 β' n ∧
      M.mem (M.quad j.1 β' q1 o) P)
    {x : V} (hx : M.InNRaw P th io M.nat j.1 ρ x) : M.mem x X := by
  obtain ⟨β, rx, ltβ, neβ⟩ := M.inN_rank hx
  have hβ := (hd.hth.fld _ _ ltβ).1
  have hsat : ∀ α, Sat M.mem M.isSet (.all 320 (Fml.imp (fRank 250 320) (Fml.imp (fApp 22 250 271) (Fml.imp (.neg (.eq 250 271)) (.mem 320 270)))))
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 270 X) 271 ρ) 250 α) ↔
      ∀ n, M.RankIs P io M.nat j.1 α n → M.mem (M.op α ρ) th → ¬ α = ρ → M.mem n X := by
    intro α
    simp [Sat, M.sat_imp, M.sat_fRank, M.sat_fApp', Function.update_apply]
  have key := M.wo_ind_fml hd.hth (σW [(20, 7), (22, 5), (24, 5), (27, 3), (270, 3)])
    (.all 320 (Fml.imp (fRank 250 320) (Fml.imp (fApp 22 250 271) (Fml.imp (.neg (.eq 250 271)) (.mem 320 270))))) 250 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 270 X) 271 ρ)
    (fun α hα ih => ?_) β hβ
  · exact (hsat β).mp key x rx ltβ neβ
  · rw [hsat α]
    have ih' : ∀ β', M.mem (M.op β' α) th → β' ≠ α → ∀ n, M.RankIs P io M.nat j.1 β' n →
        M.mem (M.op β' ρ) th → ¬ β' = ρ → M.mem n X :=
      fun β' h1 h2 => (hsat β').mp (ih β' h1 h2)
    intro n rn ltα neα
    obtain ⟨n0, o, hn0X, rn0, ho⟩ := hords α ltα neα
    have hoX := hX.1 n0 α o hn0X rn0 ho
    refine M.closed_rank hd hX ltα neα ho hoX (fun y hy => ?_) hdX rn
    obtain ⟨β1, ry, lt1, ne1⟩ := M.inN_rank hy
    refine ih' β1 lt1 ne1 y ry (hd.hth.trans _ _ _ lt1 ltα) (fun e => ?_)
    rw [e] at lt1
    exact neα (hd.hth.antisymm _ _ ltα lt1)

/-- Truth with one value changed does not depend on the name chosen for the changed value. -/
theorem tu_sim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t w w2 : V} (c v : M.Num) (hα : M.mem (M.op α α) th)
    (hw : M.InNRaw P th io M.nat j.1 α w) (hw2 : M.InNRaw P th io M.nat j.1 α w2) (hs : M.SimRaw P j.1 tp F w w2) :
    M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 t w ↔ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 t w2 := by
  obtain ⟨t1, hag1⟩ := M.exists_upd hd hw t v.1 c
  obtain ⟨t2, hag2⟩ := M.exists_upd hd hw2 t v.1 c
  rw [M.trueUpd_iff hd c v hag1, M.trueUpd_iff hd c v hag2]
  refine M.inv_hier hd c t1 t2 (fun i hi => ?_)
  by_cases e : i = v
  · rw [e] at hi ⊢
    exact ⟨w, w2, M.agree_same hag1 hi, M.agree_same hag2 hi, hs⟩
  · obtain ⟨g, vg⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) α t i.1
    exact ⟨g, g, M.agree_other hag1 hi e vg, M.agree_other hag2 hi e vg,
      M.val_sim_refl hd hα vg⟩

/-- Truth with one value changed passes to the collapse. -/
theorem tu_transfer (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {β βb t t' w w' : V} (c v : M.Num) (hca : M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β)
    (hH : M.mem (M.op β βb) H)
    (hpairs : ∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d βb t' i.1 e' ∧ M.PiRel P PiS j e e')
    (hw : M.InNRaw P th io M.nat j.1 β w) (pw : M.PiRel P PiS j w w') :
    M.TrueUpdR P th io M.nat Nt j.1 d M.adG F β c.1 v.1 t w ↔ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F βb c.1 v.1 t' w' := by
  have hw' := M.pi_inN cd pw hw hH
  obtain ⟨t1, hag1⟩ := M.exists_upd cd.hd hw t v.1 c
  obtain ⟨t1', hag1'⟩ := M.exists_upd cd.hd hw' t' v.1 c
  rw [M.trueUpd_iff cd.hd c v hag1, M.trueUpd_iff cd.hd c v hag1']
  refine M.ca_elem hca hH c t1 t1' (fun i hi => ?_)
  by_cases e : i = v
  · rw [e] at hi ⊢
    exact ⟨w, w', M.agree_same hag1 hi, M.agree_same hag1' hi, pw⟩
  · obtain ⟨e1, e1', w1, w1', p1⟩ := hpairs i hi
    exact ⟨e1, e1', M.agree_other hag1 hi e w1, M.agree_other hag1' hi e w1', p1⟩

/-- A sequence at the collapse whose values are images, in a given set, of the values of a
sequence. -/
theorem exists_img_seq (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS G ν q1) {β βb t X : V} (c : M.Num) (hH : M.mem (M.op β βb) H)
    (hvals : ∀ i : M.Num, i ≤ c → ∀ e, M.ValRaw P th io M.nat Nt j.1 d β t i.1 e → ∃ e', M.PiRel P PiS j e e' ∧ M.mem e' X)
    (hdX : M.mem d X) :
    ∃ t', ∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d βb t' i.1 e' ∧ M.PiRel P PiS j e e' ∧
      M.mem e' X := by
  obtain ⟨g, -, hg0⟩ := M.comp
    (σW [(0, 4), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (167, 5), (270, 3)])
    (Fml.ex 326 (Fml.ex 328 (.and (fPr 0 326 328) (.and (.mem 326 27) (Fml.ex 327 (.and (fVal 250 340 326 327) (.and (fPi 327 328) (.mem 328 270)))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 167 PiS) 250 β) 270 X) 340 t)
  have hg1 : ∀ q, M.mem q g ↔ ∃ i e', q = M.op i e' ∧ M.mem i M.nat ∧
      ∃ e, M.ValRaw P th io M.nat Nt j.1 d β t i e ∧ M.PiRel P PiS j e e' ∧ M.mem e' X := by
    intro q
    rw [hg0 q]
    simp [Sat, M.sat_ex, M.sat_fPr', M.sat_fVal, M.sat_fPi, Function.update_apply, PiRel]
  have hg : ∀ i e', M.mem (M.op i e') g ↔ M.mem i M.nat ∧
      ∃ e, M.ValRaw P th io M.nat Nt j.1 d β t i e ∧ M.PiRel P PiS j e e' ∧ M.mem e' X := by
    intro i e'
    constructor
    · intro h
      obtain ⟨i', e'', eq, h'⟩ := (hg1 _).mp h
      obtain ⟨e1, e2⟩ := M.op_inj eq
      rw [e1, e2]
      exact h'
    · intro h
      exact (hg1 _).mpr ⟨i, e', rfl, h⟩
  obtain ⟨t', -, hcode⟩ := M.seq_code cd.hd.hP cd.hd.hj ⟨d, M.d_rung cd.hd⟩ cd.hd.nt_zero
    cd.hd.nt_succ (c + 1) g (fun k hk => by
      obtain ⟨e, ve⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) β t k.1
      obtain ⟨e', pe, he'X⟩ := hvals k (M.le_of_succ_le_succ hk) e ve
      obtain ⟨-, βe, -, re', -⟩ := M.pi_rank cd pe
      exact ⟨e', M.rank_rung cd.hd re', (hg k.1 e').mpr ⟨k.2, e, ve, pe, he'X⟩⟩)
  refine ⟨t', fun i hi => ?_⟩
  obtain ⟨a, hga, hnt⟩ := hcode i (add_le_add hi (le_refl 1))
  obtain ⟨-, e, ve, pe, haX⟩ := (hg i.1 a).mp hga
  rcases M.val_of_nth cd.hd (α := βb) hnt with ⟨-, h⟩ | ⟨hN, h⟩
  · exact ⟨e, a, ve, h, pe, haX⟩
  · have hed : e = d := by
      rcases M.val_cases ve with h1 | h1
      · exact (hN (M.pi_inN cd pe h1 hH)).elim
      · exact h1
    refine ⟨e, d, ve, h, ?_, hdX⟩
    rw [hed]
    exact M.pi_dd cd

end cond6

/-! ## The collapse of a hull is generated -/

section cond7

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {N δ Oc H PiS ν Sg : V}
variable {q1 : V}

/-- **The collapse of a hull is generated.** Let `N` be the hull at the stage `δ` of the names
of rank below `ν` and a name `b` of rank at least `ν`, and let `γ` be the collapse of `δ`.
Then the names of rank below `γ` are generated from the names of rank below `ν` and any
image of `b`. -/
theorem hull_collapse (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS (M.restr th Sg δ) ν q1)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    {b : V} (hN : M.IsHull P th io Nt d tp q1 F Pr Sg j N δ ν b)
    (hνδ : M.mem (M.op ν δ) th) (hbδ : M.InNRaw P th io M.nat j.1 δ b) (hbν : ¬ M.InNRaw P th io M.nat j.1 ν b) {γ b' : V}
    (hH : M.mem (M.op δ γ) H) (pb : M.PiRel P PiS j b b') : M.Gen P Sg j ν γ b' := by
  have hd := cd.hd
  have hth := cd.hd.hth
  have hδO : M.mem δ Oc := (cd.hO δ).mpr (Or.inl rfl)
  have lowerAny : ∀ ρ β, M.mem (M.op β ρ) th → β ≠ ρ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β :=
    fun ρ β h _ => M.cond_all cd (hth.fld _ _ h).1
  have hγ := (M.coll_dom cd.hH hH).2.2
  have hγδ := M.coll_le hth cd.hH hH
  have hmarkν : ∀ β', M.mem (M.op β' ν) th → β' ≠ ν →
      ∃ o, M.mem (M.quad j.1 β' q1 o) P ∧ M.mem o N := by
    intro β' h ne
    obtain ⟨o, ho⟩ := M.exists_mark hd cd.hq (hth.fld _ _ h).1
    exact ⟨o, ho, M.hull_base hd hN hνδ (M.rank_inN (M.mark_rank cd.hq ho) h ne)⟩
  have hself : ∀ x, M.InNRaw P th io M.nat j.1 ν x → M.mem x N ∧ M.PiRel P PiS j x x := by
    intro x hx
    obtain ⟨β, rx, lt, ne⟩ := M.inN_rank hx
    refine M.pi_self cd (fun β' h' => hmarkν β' (hth.trans _ _ _ h' lt) (fun e => ?_)) rx
      (hth.fld _ _ lt).1
    rw [e] at h'
    exact ne (hth.antisymm _ _ lt h')
  have hbN : M.mem b N := M.hull_gen hN hbδ
  obtain ⟨βb, rb, ltb, neb⟩ := M.inN_rank hbδ
  have hβb := (hth.fld _ _ ltb).1
  have hν := (hth.fld _ _ hνδ).1
  obtain ⟨-, -, hβbO, -⟩ := M.cond_rank cd hbN rb
  obtain ⟨βbb, hHb⟩ := M.coll_tot hth cd.hH hβb hβbO
  have hβbb := (M.coll_dom cd.hH hHb).2.2
  have hνβbb : M.mem (M.op ν βbb) th := by
    rcases M.wo_total hth hν hβbb with h | h
    · exact h
    · by_cases e : βbb = ν
      · rw [e]
        exact hν
      · exfalso
        have hid : M.mem (M.op βbb βbb) H := M.coll_id hth cd.hH hβbb (fun β' h' => by
          obtain ⟨o, ho, hoN⟩ := hmarkν β' (hth.trans _ _ _ h' h) (fun e' => by
            rw [e'] at h'
            exact e (hth.antisymm _ _ h h'))
          exact (cd.hO β').mpr (Or.inr ⟨o, ho, hoN⟩))
        have e2 := M.coll_inj hth cd.hH hid hHb
        rw [e2] at h e
        exact hbν (M.rank_inN rb h e)
  obtain ⟨m1, m2⟩ := M.coll_mono hth cd.hH hHb hH ltb neb
  have hνγ : M.mem (M.op ν γ) th := hth.trans _ _ _ hνβbb m1
  have hνγne : ¬ ν = γ := by
    intro e
    rw [← e] at m1 m2
    exact m2 (hth.antisymm _ _ m1 hνβbb)
  have hb'γ := M.pi_inN cd pb hbδ hH
  refine (M.gen_iff hd hSg).mpr ⟨hγ, hνγ, hνγne, hb'γ, fun X b1 b2 b3 hX => ?_⟩
  obtain ⟨Y, -, hY0⟩ := M.comp (σW [(20, 7), (167, 5), (169, 3), (270, 3)]) (.and (.mem 320 169) (Fml.ex 321 (.and (fPi 320 321) (.mem 321 270)))) 320 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 25 j.1) 167 PiS) 169 N) 270 X)
  have hY : ∀ n, M.mem n Y ↔ M.mem n N ∧ ∃ n', M.PiRel P PiS j n n' ∧ M.mem n' X := by
    intro n
    rw [hY0 n]
    simp [Sat, M.sat_ex, M.sat_fPi, Function.update_apply, PiRel]
  have imgX : ∀ {n n' n'' : V}, M.PiRel P PiS j n n' → M.mem n' X → M.PiRel P PiS j n n'' → M.mem n'' X := by
    intro n n' n'' p h p'
    obtain ⟨t1, t2⟩ := M.pi_tie cd p p'
    exact M.closed_tie hd cd.hPr cd.hq hX b3 h (M.pi_inN cd p (cd.hsub n (M.pi_mem cd p)) hH)
      t1 t2
  have hY1 : ∀ x, M.InNRaw P th io M.nat j.1 ν x → M.mem x Y := fun x hx =>
    (hY x).mpr ⟨(hself x hx).1, x, (hself x hx).2, b1 x hx⟩
  have hY2 : M.mem b Y := (hY b).mpr ⟨hbN, b', pb, b2⟩
  have hY3 : M.mem d Y := (hY d).mpr ⟨cd.hdN, d, M.pi_dd cd, b3⟩
  have hYcl : M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg δ) Y δ ν := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- rule 1
      intro n β o hnY rn ho
      obtain ⟨hnN, n', pn, hn'X⟩ := (hY n).mp hnY
      obtain ⟨lt, ne, hβO, -⟩ := M.cond_rank cd hnN rn
      have hoN := cd.hcl.1 n β o hnN rn ho
      obtain ⟨β1, β1b, r1, r1', hH1, -, -⟩ := M.pi_rank cd pn
      have e1 := M.rank_unique hd r1 rn
      rw [e1] at hH1
      obtain ⟨o', ho'⟩ := M.exists_mark hd cd.hq (M.coll_dom cd.hH hH1).2.2
      exact (hY o).mpr ⟨hoN, o', M.pi_mark cd hH1 lt ne ho ho', hX.1 n' β1b o' hn'X r1' ho'⟩
    · -- rule 2
      intro n β c u i e hnY hname hi hle hv
      obtain ⟨hnN, n', pn, hn'X⟩ := (hY n).mp hnY
      have heN := cd.hcl.2.1 n β c u i e hnN hname hi hle hv
      obtain ⟨β0, β0b, c0, u0, u0', -, -, hH0, hn0, hn0', hvn⟩ := M.pi_unpack cd pn
      have hc : M.mem c M.nat := by
        obtain ⟨f, q, -, -, h3, -⟩ := hname
        exact h3
      obtain ⟨eβ, ec, eu⟩ := M.nameOf_unique hd hn0 ((M.nameR_iff ⟨c, hc⟩).mp hname)
      subst ec
      subst eu
      obtain ⟨e1, e1', v1, v1', hrel⟩ := hvn ⟨i, hi⟩
        ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ ⟨c, hc⟩).mp hle)
      rw [eβ] at v1
      have ee := M.val_unique hd hv v1
      have he1'X : M.mem e1' X :=
        hX.2.1 n' β0b c u0' i e1' hn'X ((M.nameR_iff ⟨c, hc⟩).mpr hn0') hi hle v1'
      refine (hY e).mpr ⟨heN, e1', ?_, he1'X⟩
      rcases hrel with ⟨h1, h2⟩ | ⟨-, h⟩
      · rw [ee, h1, h2]
        exact M.pi_dd cd
      · rw [ee]
        exact h
    · -- rule 3
      intro n β c u o ho hoY lt ne hname hvals
      obtain ⟨hoN, o', po, ho'X⟩ := (hY o).mp hoY
      have hc : M.mem c M.nat := by
        obtain ⟨f, q, -, -, h3, -⟩ := hname
        exact h3
      have hnN := cd.hcl.2.2.1 n β c u o ho hoN lt ne hname
        (fun i e hi hle hv => ((hY e).mp (hvals i e hi hle hv)).1)
      obtain ⟨n', pn⟩ := M.pi_tot cd hnN
      refine (hY n).mpr ⟨hnN, n', pn, ?_⟩
      obtain ⟨β0, β0b, c0, u0, u0', -, -, hH0, hn0, hn0', hvn⟩ := M.pi_unpack cd pn
      obtain ⟨eβ, ec, eu⟩ := M.nameOf_unique hd hn0 ((M.nameR_iff ⟨c, hc⟩).mp hname)
      subst ec
      subst eu
      rw [eβ] at hH0 hvn
      obtain ⟨γ1, γ1b, ro, ro', hHo, -, -⟩ := M.pi_rank cd po
      have e1 := M.rank_unique hd ro (M.mark_rank cd.hq ho)
      rw [e1] at hHo
      have e2 := M.coll_fun hth cd.hH hHo hH0
      rw [e2] at ro'
      obtain ⟨o2, ho2⟩ := M.exists_mark hd cd.hq (M.coll_dom cd.hH hH0).2.2
      have ho2X := hX.1 o' β0b o2 ho'X ro' ho2
      obtain ⟨l1, l2⟩ := M.coll_mono hth cd.hH hH0 hH lt ne
      refine hX.2.2.1 n' β0b c u0' o2 ho2 ho2X l1 l2 ((M.nameR_iff ⟨c, hc⟩).mpr hn0')
        (fun i e' hi hle hv' => ?_)
      obtain ⟨e1, e1', v1, v1', hrel⟩ := hvn ⟨i, hi⟩
        ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ ⟨c, hc⟩).mp hle)
      rw [M.val_unique hd hv' v1']
      obtain ⟨-, e2', pe, he2'X⟩ := (hY e1).mp (hvals i e1 hi hle v1)
      refine imgX pe he2'X ?_
      rcases hrel with ⟨h1, h2⟩ | ⟨-, h⟩
      · rw [h1, h2]
        exact M.pi_dd cd
      · exact h
    · -- rule 4
      intro n n0 hnY hc hs
      obtain ⟨hnN, n', pn, hn'X⟩ := (hY n).mp hnY
      have hn0N := cd.hcl.2.2.2.1 n n0 hnN hc hs
      obtain ⟨n0', pn0⟩ := M.pi_tot cd hn0N
      exact (hY n0).mpr ⟨hn0N, n0', pn0, hX.2.2.2.1 n' n0' hn'X
        (M.step_can_img cd (lowerAny δ) hδO hH (cd.hsub n0 hn0N) pn0 hc)
        ((M.step_sim cd (lowerAny δ) (cd.hsub n hnN) (cd.hsub n0 hn0N) pn pn0).mp hs)⟩
    · -- rule 5
      intro β c v t w hβ hc hv hvals hlw
      have hβO : M.mem β Oc := by
        rcases hβ with e | ⟨lt, ne, o, ho, hoY⟩
        · rw [e]
          exact hδO
        · exact (cd.hO β).mpr (Or.inr ⟨o, ho, ((hY o).mp hoY).1⟩)
      have hβN : (β = δ ∨ (M.mem (M.op β δ) th ∧ ¬ β = δ ∧
          ∃ o, M.mem (M.quad j.1 β q1 o) P ∧ M.mem o N)) := by
        rcases hβ with e | ⟨lt, ne, o, ho, hoY⟩
        · exact Or.inl e
        · exact Or.inr ⟨lt, ne, o, ho, ((hY o).mp hoY).1⟩
      have hwN := cd.hcl.2.2.2.2.1 β c v t w hβN hc hv
        (fun i e hi hle hv' => ((hY e).mp (hvals i e hi hle hv')).1) hlw
      have hβfld : M.mem (M.op β β) th := by
        rcases hβN with e | ⟨lt, -⟩
        · rw [e]
          exact cd.hδ
        · exact (hth.fld _ _ lt).1
      obtain ⟨βc, hHβ⟩ := M.coll_tot hth cd.hH hβfld hβO
      have hβc := (M.coll_dom cd.hH hHβ).2.2
      have CAβ := M.cond_all cd hβfld
      obtain ⟨t', hpairs⟩ := M.exists_img_seq cd ⟨c, hc⟩ hHβ (fun i hi e hv' => by
        obtain ⟨-, e', pe, he'X⟩ := (hY e).mp
          (hvals i.1 e i.2 ((M.leRaw_iff M.adG_spec i ⟨c, hc⟩).mpr hi) hv')
        exact ⟨e', pe, he'X⟩) b3
      have hpairs' : ∀ i : M.Num, i ≤ (⟨c, hc⟩ : M.Num) → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d β t i.1 e ∧
          M.ValRaw P th io M.nat Nt j.1 d βc t' i.1 e' ∧ M.PiRel P PiS j e e' := fun i hi => by
        obtain ⟨e, e', a1, a2, a3, -⟩ := hpairs i hi
        exact ⟨e, e', a1, a2, a3⟩
      obtain ⟨w', pw⟩ := M.pi_tot cd hwN
      refine (hY w).mpr ⟨hwN, w', pw, ?_⟩
      have hwβ := hlw.1
      have hw'βc := M.pi_inN cd pw hwβ hHβ
      have hβcX : (βc = γ ∨ (M.mem (M.op βc γ) th ∧ ¬ βc = γ ∧
          ∃ o', M.mem (M.quad j.1 βc q1 o') P ∧ M.mem o' X)) := by
        rcases hβ with e | ⟨lt, ne, o, ho, hoY⟩
        · rw [e] at hHβ
          exact Or.inl (M.coll_fun hth cd.hH hHβ hH)
        · obtain ⟨-, o1, po, ho1X⟩ := (hY o).mp hoY
          obtain ⟨γ1, γ1b, ro, ro', hHo, -, -⟩ := M.pi_rank cd po
          have e1 := M.rank_unique hd ro (M.mark_rank cd.hq ho)
          rw [e1] at hHo
          have e2 := M.coll_fun hth cd.hH hHo hHβ
          rw [e2] at ro'
          obtain ⟨o2, ho2⟩ := M.exists_mark hd cd.hq hβc
          obtain ⟨l1, l2⟩ := M.coll_mono hth cd.hH hHβ hH lt ne
          exact Or.inr ⟨l1, l2, o2, ho2, hX.1 o1 βc o2 ho1X ro' ho2⟩
      refine hX.2.2.2.2.1 βc c v t' w' hβcX hc hv (fun i e' hi hle hv' => ?_) ?_
      · obtain ⟨e, e1', a1, a2, a3, a4⟩ := hpairs ⟨i, hi⟩
          ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ ⟨c, hc⟩).mp hle)
        rw [M.val_unique hd hv' a2]
        exact a4
      · have tr : ∀ {x x' : V}, M.InNRaw P th io M.nat j.1 β x → M.PiRel P PiS j x x' →
            (M.TrueUpdR P th io M.nat Nt j.1 d M.adG F β c v t x ↔ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F βc c v t' x') :=
          fun hx px => M.tu_transfer cd ⟨c, hc⟩ ⟨v, hv⟩ CAβ hHβ hpairs' hx px
        have minimal : ∀ (pol : Prop), (∀ w2, M.InNRaw P th io M.nat j.1 β w2 → (M.TrueUpdR P th io M.nat Nt j.1 d M.adG F β c v t w2 ↔ pol) →
            M.mem (M.op w w2) Pr) → ∀ w2', M.InNRaw P th io M.nat j.1 βc w2' → (M.TrueUpdR P th io M.nat Nt j.1 d M.adG F βc c v t' w2' ↔ pol) →
            M.mem (M.op w' w2') Pr := by
          intro pol hmin w2' hw2' hpol'
          obtain ⟨m', hcm, hsm⟩ := M.exists_can hd cd.hPr (M.inN_refl hd hw2')
          have hm' := M.can_inN hd cd.hPr hw2' hcm hsm
          obtain ⟨n1, n1t, hn1, pn1, -, t1, t2⟩ := M.step_can cd (lowerAny β) hβO hHβ hm' hcm
          have hn1t := M.pi_inN cd pn1 hn1 hHβ
          have s1 : M.TrueUpdR P th io M.nat Nt j.1 d M.adG F βc c v t' n1t ↔ pol :=
            (M.tu_sim hd ⟨c, hc⟩ ⟨v, hv⟩ hβc hn1t hw2' (M.sim_trans hd
              (M.tie_sim hd cd.hPr t1 t2) (M.sim_symm hd hsm))).trans hpol'
          have p1 := hmin n1 hn1 ((tr hn1 pn1).trans s1)
          have p2 := (M.pi_pr cd pw pn1).mp p1
          exact M.pr_trans hd cd.hPr (M.pr_trans hd cd.hPr p2 t1) (hcm.2 w2' (M.sim_symm hd hsm))
        refine ⟨hw'βc, ?_⟩
        rcases hlw.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨(tr hwβ pw).mp h1, fun w2' hw2' h' =>
            minimal True (fun w2 hw2 hp => h2 w2 hw2 (hp.mpr trivial)) w2' hw2'
              ⟨fun _ => trivial, fun _ => h'⟩⟩
        · exact Or.inr ⟨fun h => h1 ((tr hwβ pw).mpr h), fun w2' hw2' h' =>
            minimal False (fun w2 hw2 hp => h2 w2 hw2 (fun h => hp.mp h)) w2' hw2'
              ⟨fun h => h' h, fun h => h.elim⟩⟩
    · -- rule 6
      intro β1 o1 β2 w y ho1 ho1Y h12 hwy hG hmin hleast
      obtain ⟨ho1N, o1', po1, ho1'X⟩ := (hY o1).mp ho1Y
      obtain ⟨hSgm, lt2, ne2⟩ := M.mem_restr.mp hG
      obtain ⟨hall2, hwN⟩ := cd.hcl.2.2.2.2.2 β1 o1 β2 w y ho1 ho1N h12 hwy hG hmin hleast
      have hgen : M.Gen P Sg j ν β2 w := ⟨y, hwy, hSgm⟩
      have hβ2 := (hth.fld _ _ lt2).1
      obtain ⟨o2, ho2⟩ := M.exists_mark hd cd.hq hβ2
      have ho2N := hall2 o2 ho2
      have hlow2 := M.gen_sub hd hSg hgen cd.hcl lt2 ne2 ho2 ho2N
        (fun x hx => M.hull_base hd hN hνδ hx) hwN cd.hdN
      have hmark2 : ∀ β', M.mem (M.op β' β2) th →
          ∃ o, M.mem (M.quad j.1 β' q1 o) P ∧ M.mem o N := by
        intro β' h'
        by_cases e : β' = β2
        · rw [e]
          exact ⟨o2, ho2, ho2N⟩
        · obtain ⟨o, ho⟩ := M.exists_mark hd cd.hq (hth.fld _ _ h').1
          exact ⟨o, ho, hlow2 o (M.rank_inN (M.mark_rank cd.hq ho) h' e)⟩
      have hself2 : ∀ {x β' : V}, M.RankIs P io M.nat j.1 β' x → M.mem (M.op β' β2) th → M.PiRel P PiS j x x :=
        fun rx h' => (M.pi_self cd hmark2 rx h').2
      have ho1X : M.mem o1 X := imgX po1 ho1'X (hself2 (M.mark_rank cd.hq ho1) h12)
      have hH2 : M.mem (M.op β2 β2) H := M.coll_id hth cd.hH hβ2 (fun β' h' => by
        obtain ⟨o, ho, hoN⟩ := hmark2 β' h'
        exact (cd.hO β').mpr (Or.inr ⟨o, ho, hoN⟩))
      obtain ⟨l1, l2⟩ := M.coll_mono hth cd.hH hH2 hH lt2 ne2
      obtain ⟨hallX, hwX⟩ := hX.2.2.2.2.2 β1 o1 β2 w y ho1 ho1X h12 hwy
        (M.mem_restr.mpr ⟨hSgm, l1, l2⟩)
        (fun β' b0 y' hq' hG' h1' => by
          obtain ⟨hS', lt', ne'⟩ := M.mem_restr.mp hG'
          refine hmin β' b0 y' hq' (M.mem_restr.mpr ⟨hS', hth.trans _ _ _ lt' hγδ, fun e => ?_⟩) h1'
          rw [e] at lt'
          exact ne' (e.trans (hth.antisymm _ _ lt' hγδ)))
        (fun b0 y' hq' hG' => hleast b0 y' hq'
          (M.mem_restr.mpr ⟨(M.mem_restr.mp hG').1, lt2, ne2⟩))
      constructor
      · intro o2' ho2'
        exact (hY o2').mpr ⟨hall2 o2' ho2', o2', hself2 (M.mark_rank cd.hq ho2') hβ2,
          hallX o2' ho2'⟩
      · obtain ⟨-, -, hwβ2⟩ := M.gen_lt hd hSg hgen
        obtain ⟨βw, rw', ltw, -⟩ := M.inN_rank hwβ2
        exact (hY w).mpr ⟨hwN, w, hself2 rw' ltw, hwX⟩
  have hNY : ∀ n, M.mem n N → M.mem n Y := fun n hn => M.hull_min hN hY1 hY2 hY3 hYcl hn
  intro x hx
  refine M.closed_all hd hX b3 (fun β' lt' ne' => ?_) hx
  obtain ⟨β, ltβ, neβ, hHβ⟩ := M.coll_range hth cd.hH hH lt' ne'
  obtain ⟨o, ho, hoN⟩ := M.cond_ord cd (M.coll_dom cd.hH hHβ).2.1 neβ
  obtain ⟨-, o', po, ho'X⟩ := (hY o).mp (hNY o hoN)
  obtain ⟨β1, β1b, r1, r1', hH1, -, -⟩ := M.pi_rank cd po
  have e1 := M.rank_unique hd r1 (M.mark_rank cd.hq ho)
  rw [e1] at hH1
  have e2 := M.coll_fun hth cd.hH hH1 hHβ
  rw [e2] at r1'
  obtain ⟨o2, ho2⟩ := M.exists_mark hd cd.hq (hth.fld _ _ lt').1
  exact ⟨o', o2, ho'X, r1', ho2⟩

end cond7

/-! ## Sets of small members are absorbed below the next stage that is not small -/

section absorb

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {N δ Oc H PiS ν Sg : V}
variable {q1 : V}

/-- **A closed set contains the levels up to its small stages.** If a closed set contains
the marker of a `ν`-small stage `β₁`, generated below `δ`, then it contains every name of rank
at most `β₁`. -/
theorem closed_small (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j) (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    {X β1 o1 : V} (hX : M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg δ) X δ ν)
    (b1 : ∀ x, M.InNRaw P th io M.nat j.1 ν x → M.mem x X) (b3 : M.mem d X)
    (ho1 : M.mem (M.quad j.1 β1 q1 o1) P) (ho1X : M.mem o1 X)
    (hsm : ∃ ρ2 b, M.mem (M.op β1 ρ2) th ∧ M.mem (M.op ρ2 δ) th ∧ ρ2 ≠ δ ∧ M.Gen P Sg j ν ρ2 b)
    {x β' : V} (rx : M.RankIs P io M.nat j.1 β' x) (hβ' : M.mem (M.op β' β1) th) : M.mem x X := by
  obtain ⟨ρ2, b, h12, h2δ, ne2δ, hgen⟩ := hsm
  obtain ⟨Z, -, hZ0⟩ := M.comp (σW [(20, 7), (22, 5), (164, 5)]) (.and (fApp 22 343 344) (Fml.ex 291 (Fml.ex 292 (.and (fApp4 20 25 272 291 292) (fApp 164 344 292))))) 344 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 25 j.1) 164 Sg) 272 ν) 343 β1)
  have hZ : ∀ β, M.mem β Z ↔ M.mem (M.op β1 β) th ∧ ∃ b, M.Gen P Sg j ν β b := by
    intro β
    rw [hZ0 β]
    simp [Sat, M.sat_ex, M.sat_fApp', M.sat_fApp4', Function.update_apply, Gen]
  obtain ⟨β2, hβ2Z, hβ2, hmin⟩ := hd.hth.least Z ⟨ρ2, (hZ ρ2).mpr ⟨h12, b, hgen⟩,
    (hd.hth.fld _ _ h12).2⟩
  obtain ⟨h1β2, b2, hgen2⟩ := (hZ β2).mp hβ2Z
  have hβ2ρ2 := hmin ρ2 ((hZ ρ2).mpr ⟨h12, b, hgen⟩) (hd.hth.fld _ _ h12).2
  have lt2 : M.mem (M.op β2 δ) th := hd.hth.trans _ _ _ hβ2ρ2 h2δ
  have ne2 : β2 ≠ δ := by
    intro e
    rw [e] at hβ2ρ2
    exact ne2δ (hd.hth.antisymm _ _ h2δ hβ2ρ2)
  obtain ⟨w, ⟨y, hwy, hSgm⟩, hwmin⟩ := M.exists_least_gen hd hPr hSg hgen2
  obtain ⟨hall, hwX⟩ := hX.2.2.2.2.2 β1 o1 β2 w y ho1 ho1X h1β2 hwy
    (M.mem_restr.mpr ⟨hSgm, lt2, ne2⟩)
    (fun β'' b' y' hq' hG' h1' => hmin β'' ((hZ β'').mpr ⟨h1', b', y', hq', (M.mem_restr.mp hG').1⟩)
      (hd.hth.fld _ _ h1').2)
    (fun b' y' hq' hG' => hwmin b' ⟨y', hq', (M.mem_restr.mp hG').1⟩)
  obtain ⟨o2, ho2⟩ := M.exists_mark hd hq hβ2
  have ho2X := hall o2 ho2
  have hlow := M.gen_sub hd hSg ⟨y, hwy, hSgm⟩ hX lt2 ne2 ho2 ho2X b1 hwX b3
  by_cases e : β' = β2
  · rw [e] at rx
    exact M.closed_rank hd hX lt2 ne2 ho2 ho2X hlow b3 rx
  · exact hlow x (M.rank_inN rx (hd.hth.trans _ _ _ hβ' h1β2) e)

/-- A name with two prescribed values of its parameters. -/
theorem exists_name_vals2 (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {σ x o : V} (hσ : M.mem (M.op σ σ) th)
    (hx : M.InNRaw P th io M.nat j.1 σ x) (ho : M.InNRaw P th io M.nat j.1 σ o) :
    ∃ b u, M.NameOf P io j b σ 1 u ∧ M.ValRaw P th io M.nat Nt j.1 d σ u (0 : M.Num).1 x ∧ M.ValRaw P th io M.nat Nt j.1 d σ u (1 : M.Num).1 o := by
  obtain ⟨t0, -, -⟩ := M.const_seq hd (1 + 1)
  obtain ⟨t1, -, hag1⟩ := M.exists_updR hd hx t0 (0 : M.Num).1 1
  obtain ⟨u, huR, hag2⟩ := M.exists_updR hd ho t1 (1 : M.Num).1 1
  obtain ⟨b, hb⟩ := M.nameOf_exists hd hσ huR 1
  have h01 : (0 : M.Num) ≤ 1 := zero_le
  exact ⟨b, u, hb, M.agree_other hag2 h01 M.n01 (M.agree_same hag1 h01),
    M.agree_same hag2 (le_refl 1)⟩

/-- **A member of `N` whose members all lie in a part of `N` that the collapse fixes is
fixed**: it denotes the same set as its image. -/
theorem cond_fix_set (cd : M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS (M.restr th Sg δ) ν q1)
    {x x' β γ : V} (hxN : M.mem x N) (px : M.PiRel P PiS j x x') (hH : M.mem (M.op δ γ) H)
    (hmarks : ∀ β', M.mem (M.op β' β) th → β' ≠ β →
      ∃ o, M.mem (M.quad j.1 β' q1 o) P ∧ M.mem o N)
    (hmem : ∀ y, M.EpsRaw P th io M.nat j.1 F y x → ∃ y', M.InNRaw P th io M.nat j.1 β y' ∧ M.SimRaw P j.1 tp F y y') : M.SimRaw P j.1 tp F x x' := by
  have hd := cd.hd
  have hth := cd.hd.hth
  have hδO : M.mem δ Oc := (cd.hO δ).mpr (Or.inl rfl)
  have lower : ∀ β0, M.mem (M.op β0 δ) th → β0 ≠ δ → M.CondAtR P th io M.nat Nt j.1 d M.adG tp F Pr H PiS β0 :=
    fun β0 h _ => M.cond_all cd (hth.fld _ _ h).1
  have hself : ∀ y', M.InNRaw P th io M.nat j.1 β y' → M.mem y' N ∧ M.PiRel P PiS j y' y' := by
    intro y' hy'
    obtain ⟨β0, ry, lt, ne⟩ := M.inN_rank hy'
    refine M.pi_self cd (fun β' h' => hmarks β' (hth.trans _ _ _ h' lt) (fun e => ?_)) ry
      (hth.fld _ _ lt).1
    rw [e] at h'
    exact ne (hth.antisymm _ _ lt h')
  obtain ⟨σ, σb, rx, rx', hHσ, ltσ, neσ⟩ := M.pi_rank cd px
  have hσ := (hth.fld _ _ ltσ).1
  have hσb := (M.coll_dom cd.hH hHσ).2.2
  have hxδ := cd.hsub x hxN
  have hsxx := M.sim_refl hd rx hσ
  have hsx'x' := M.sim_refl hd rx' hσb
  refine (M.hier_sim hd rx rx' hσ hσb).mpr ⟨fun y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨y', hy'β, hsy⟩ := hmem y hy
    obtain ⟨hy'N, py'⟩ := hself y' hy'β
    have h1 : M.EpsStarRaw P th io M.nat j.1 tp F y' x := ⟨y, M.sim_symm hd hsy, hy⟩
    obtain ⟨z, hsz, hz⟩ := (M.step_eps cd lower (cd.hsub y' hy'N) hxδ py' px).mp h1
    exact ⟨z, hz, M.sim_trans hd hsy hsz⟩
  · have hzN := M.inN_mono hd (M.eps_inN_rank hd rx' hz)
      ((M.coll_le_iff hth cd.hH hHσ hH).mp ltσ)
    obtain ⟨n, nt, hnδ, pn, hsn⟩ := M.step_surj cd lower hδO hH hzN
    have h1 : M.EpsStarRaw P th io M.nat j.1 tp F nt x' := ⟨z, hsn, hz⟩
    obtain ⟨y, hsy, hy⟩ := (M.step_eps cd lower hnδ hxδ pn px).mpr h1
    obtain ⟨y', hy'β, hsy'⟩ := hmem y hy
    obtain ⟨hy'N, py'⟩ := hself y' hy'β
    have h2 : M.SimRaw P j.1 tp F nt y' := (M.step_sim cd lower hnδ (cd.hsub y' hy'N) pn py').mp
      (M.sim_trans hd hsy hsy')
    exact ⟨y, hy, M.sim_trans hd hsy' (M.sim_trans hd (M.sim_symm hd h2) hsn)⟩

end absorb

/-! ## The absorption theorem and separation -/

section absorb2

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {ν Sg : V}
variable {q1 : V}

theorem wo_ne_of_le_lt {r a b c : V} (hr : M.IsWO r) (h1 : M.mem (M.op a b) r)
    (h2 : M.mem (M.op b c) r) (ne : b ≠ c) : a ≠ c := by
  intro e
  rw [e] at h1
  exact ne (hr.antisymm _ _ h2 h1)

theorem wo_ne_of_lt_le {r a b c : V} (hr : M.IsWO r) (h1 : M.mem (M.op a b) r) (ne : a ≠ b)
    (h2 : M.mem (M.op b c) r) : a ≠ c := by
  intro e
  rw [← e] at h2
  exact ne (hr.antisymm _ _ h1 h2)

/-- The hull at a stage, with its collapse. -/
theorem exists_hull_cond (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {δ b : V}
    (hνδ : M.mem (M.op ν δ) th) (hbδ : M.InNRaw P th io M.nat j.1 δ b) :
    ∃ N Oc H PiS γ, M.IsHull P th io Nt d tp q1 F Pr Sg j N δ ν b ∧
      M.CondData R P th io Nt nle p F d tp qo Nu Pr m j N δ Oc H PiS (M.restr th Sg δ) ν q1 ∧
      M.mem (M.op δ γ) H := by
  obtain ⟨N, hN⟩ := M.exists_hull (P := P) (th := th) (io := io) (Nt := Nt) (F := F) (d := d)
    (tp := tp) (Pr := Pr) (j := j) (q1 := q1) Sg δ ν b
  have hδ := (hd.hth.fld _ _ hνδ).2
  obtain ⟨β0, -, lt0, ne0⟩ := M.inN_rank hbδ
  have hdN : M.mem d N := M.hull_d hN (M.d_inN hd lt0 ne0)
  obtain ⟨Oc, H, PiS, cd⟩ := M.exists_condData hd hPr hq hNu hδ
    (M.hull_closed hd hPr hq hSg hN) (fun x hx => M.hull_sub hN hx) hdN
  obtain ⟨γ, hH⟩ := M.coll_tot hd.hth cd.hH hδ ((cd.hO δ).mpr (Or.inl rfl))
  exact ⟨N, Oc, H, PiS, γ, hN, cd, hH⟩

/-- **Absorption.** Let `κ` be the least stage that is not `ν`-small. If all members of the
set denoted by a name `x`, of any rank that has two stages above it, are denoted by names of
rank below a stage `β` below `κ`, then `x` denotes the same set as a name of rank below `κ`. -/
theorem next_absorb (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {κ : V}
    (hκ : M.IsNext P th Sg j ν κ) {x σ σ' δ β : V} (rx : M.RankIs P io M.nat j.1 σ x)
    (hσσ' : M.mem (M.op σ σ') th) (neσ : σ ≠ σ') (hσ'δ : M.mem (M.op σ' δ) th) (neσ' : σ' ≠ δ)
    (hβκ : M.mem (M.op β κ) th) (neβ : β ≠ κ)
    (hmem : ∀ y, M.EpsRaw P th io M.nat j.1 F y x → ∃ y', M.InNRaw P th io M.nat j.1 β y' ∧ M.SimRaw P j.1 tp F y y') :
    ∃ x', M.InNRaw P th io M.nat j.1 κ x' ∧ M.SimRaw P j.1 tp F x x' := by
  have hth := hd.hth
  obtain ⟨hκκ, hns, hsm⟩ := hκ
  have hσ := (hth.fld _ _ hσσ').1
  have hσ' := (hth.fld _ _ hσσ').2
  by_cases hlt : M.mem (M.op σ κ) th ∧ σ ≠ κ
  · exact ⟨x, M.rank_inN rx hlt.1 hlt.2, M.sim_refl hd rx hσ⟩
  have hκσ : M.mem (M.op κ σ) th := by
    rcases M.wo_total hth hκκ hσ with h | h
    · exact h
    · by_cases e : σ = κ
      · rw [e]
        exact hκκ
      · exact (hlt ⟨h, e⟩).elim
  obtain ⟨ρ2, b2, hβρ2, hgen2⟩ := hsm β hβκ neβ
  have hρ2 := (hth.fld _ _ hβρ2).2
  have lt2κ : M.mem (M.op ρ2 κ) th ∧ ρ2 ≠ κ := by
    rcases M.wo_total hth hρ2 hκκ with h | h
    · refine ⟨h, fun e => hns ⟨ρ2, b2, ?_, hgen2⟩⟩
      rw [e]
      exact hκκ
    · exact (hns ⟨ρ2, b2, h, hgen2⟩).elim
  obtain ⟨hνρ2, neνρ2, -⟩ := M.gen_lt hd hSg hgen2
  have hρ2σ : M.mem (M.op ρ2 σ) th := hth.trans _ _ _ lt2κ.1 hκσ
  have hρ2σ' : M.mem (M.op ρ2 σ') th := hth.trans _ _ _ hρ2σ hσσ'
  have neρ2σ' : ρ2 ≠ σ' := M.wo_ne_of_le_lt hth hρ2σ hσσ' neσ
  have hρ2δ : M.mem (M.op ρ2 δ) th := hth.trans _ _ _ hρ2σ' hσ'δ
  have neρ2δ : ρ2 ≠ δ := M.wo_ne_of_le_lt hth hρ2σ' hσ'δ neσ'
  have hνσ' : M.mem (M.op ν σ') th := hth.trans _ _ _ hνρ2 hρ2σ'
  have hνδ : M.mem (M.op ν δ) th := hth.trans _ _ _ hνσ' hσ'δ
  obtain ⟨o2, ho2⟩ := M.exists_mark hd hq hρ2
  have hxσ' : M.InNRaw P th io M.nat j.1 σ' x := M.rank_inN rx hσσ' neσ
  have ho2σ' : M.InNRaw P th io M.nat j.1 σ' o2 := M.rank_inN (M.mark_rank hq ho2) hρ2σ' neρ2σ'
  obtain ⟨b, u, hb, v0, v1⟩ := M.exists_name_vals2 hd hσ' hxσ' ho2σ'
  have hbδ : M.InNRaw P th io M.nat j.1 δ b := M.rank_inN (M.nameOf_rank hb) hσ'δ neσ'
  have hbν : ¬ M.InNRaw P th io M.nat j.1 ν b := by
    intro h
    obtain ⟨β0, r0, lt0, ne0⟩ := M.inN_rank h
    have e0 := M.rank_unique hd r0 (M.nameOf_rank hb)
    rw [e0] at lt0 ne0
    exact ne0 (hth.antisymm _ _ lt0 hνσ')
  obtain ⟨N, Oc, H, PiS, γ, hN, cd, hH⟩ := M.exists_hull_cond hd hPr hq hNu hSg hνδ hbδ
  have hbN := M.hull_gen hN hbδ
  have hxN : M.mem x N := cd.hcl.2.1 b σ' (1 : M.Num).1 u (0 : M.Num).1 x hbN
    ((M.nameR_iff 1).mpr hb) (0 : M.Num).2 ((M.leRaw_iff M.adG_spec 0 1).mpr zero_le) v0
  have ho2N : M.mem o2 N := cd.hcl.2.1 b σ' (1 : M.Num).1 u (1 : M.Num).1 o2 hbN
    ((M.nameR_iff 1).mpr hb) (1 : M.Num).2 ((M.leRaw_iff M.adG_spec 1 1).mpr (le_refl 1)) v1
  have hlow : ∀ {y β' : V}, M.RankIs P io M.nat j.1 β' y → M.mem (M.op β' ρ2) th → M.mem y N := fun ry h =>
    M.closed_small hd hPr hq hSg cd.hcl (fun x hx => M.hull_base hd hN hνδ hx) cd.hdN ho2 ho2N
      ⟨ρ2, b2, hρ2, hρ2δ, neρ2δ, hgen2⟩ ry h
  have hmarks : ∀ β', M.mem (M.op β' β) th → β' ≠ β →
      ∃ o, M.mem (M.quad j.1 β' q1 o) P ∧ M.mem o N := by
    intro β' h ne
    obtain ⟨o, ho⟩ := M.exists_mark hd hq (hth.fld _ _ h).1
    exact ⟨o, ho, hlow (M.mark_rank hq ho) (hth.trans _ _ _ h hβρ2)⟩
  obtain ⟨xt, px⟩ := M.pi_tot cd hxN
  have hs := M.cond_fix_set cd hxN px hH hmarks hmem
  obtain ⟨bt, pb⟩ := M.pi_tot cd hbN
  have hgenγ := M.hull_collapse cd hSg hN hνδ hbδ hbν hH pb
  have hγ := (M.coll_dom cd.hH hH).2.2
  have hγκ : M.mem (M.op γ κ) th := by
    rcases M.wo_total hth hγ hκκ with h | h
    · exact h
    · exact (hns ⟨γ, bt, h, hgenγ⟩).elim
  exact ⟨xt, M.inN_mono hd (M.pi_inN cd px (cd.hsub x hxN) hH) hγκ, hs⟩

/-- **Separation at the least stage that is not small**, in semantic form: if the names `y` of
rank below `κ` that satisfy a formula with parameters `u` all denote sets denoted by names of
rank below a stage `β` below `κ`, then some name of rank below `κ` denotes the set of the sets
denoted by them. -/
theorem next_sep (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {κ : V}
    (hκ : M.IsNext P th Sg j ν κ) {σ' δ β u : V}
    (hκσ' : M.mem (M.op κ σ') th) (neκ : κ ≠ σ') (hσ'δ : M.mem (M.op σ' δ) th) (neσ' : σ' ≠ δ)
    (hβκ : M.mem (M.op β κ) th) (neβ : β ≠ κ) (hu : M.mem (M.op j.1 u) R) (φ : M.Num)
    (hbound : ∀ y, M.InNRaw P th io M.nat j.1 κ y → (∃ s, M.mem (M.quad j.1 y u s) P ∧ M.TrueAt P io F j.1 κ φ s) →
      ∃ y', M.InNRaw P th io M.nat j.1 β y' ∧ M.SimRaw P j.1 tp F y y') :
    ∃ x', M.InNRaw P th io M.nat j.1 κ x' ∧ ∀ y, (M.EpsStarRaw P th io M.nat j.1 tp F y x' ↔
      ∃ y0, M.SimRaw P j.1 tp F y y0 ∧ M.InNRaw P th io M.nat j.1 κ y0 ∧ ∃ s, M.mem (M.quad j.1 y0 u s) P ∧ M.TrueAt P io F j.1 κ φ s) := by
  have hκκ := hκ.1
  obtain ⟨x, rx, hx⟩ := M.def_name hd hκκ hu φ
  obtain ⟨x', hx'κ, hs⟩ := M.next_absorb hd hPr hq hNu hSg hκ rx hκσ' neκ hσ'δ neσ' hβκ neβ
    (fun y hy => hbound y ((hx y).mp hy).1 ((hx y).mp hy).2)
  obtain ⟨βx', rx', ltx', -⟩ := M.inN_rank hx'κ
  have sxx := M.sim_refl hd rx hκκ
  refine ⟨x', hx'κ, fun y => ?_⟩
  constructor
  · intro h
    have hyy : M.SimRaw P j.1 tp F y y := M.epsStar_left hd h
    obtain ⟨y0, hsy, hy0⟩ := M.epsStar_congr hd hyy (M.sim_symm hd hs) h
    exact ⟨y0, hsy, ((hx y0).mp hy0).1, ((hx y0).mp hy0).2⟩
  · rintro ⟨y0, hsy, hy0κ, hy0⟩
    have h1 : M.EpsStarRaw P th io M.nat j.1 tp F y x := ⟨y0, hsy, (hx y0).mpr ⟨hy0κ, hy0⟩⟩
    exact M.epsStar_congr hd (M.sim_trans hd hsy (M.sim_symm hd hsy)) hs h1

end absorb2

/-! ## Collection at the least stage that is not small -/

section coll2

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {ν Sg : V}
variable {q1 : V}

/-- A sequence with prescribed values, chosen from a set relation all of whose values are
names of rank below the stage. -/
theorem exists_seq_vals (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {σ g : V} (n : M.Num)
    (hg : ∀ k : M.Num, k + 1 ≤ n → ∃ a, M.InNRaw P th io M.nat j.1 σ a ∧ M.mem (M.op k.1 a) g)
    (hgN : ∀ (k : M.Num) (a : V), k + 1 ≤ n → M.mem (M.op k.1 a) g → M.InNRaw P th io M.nat j.1 σ a) :
    ∃ s, M.mem (M.op j.1 s) R ∧ ∀ k : M.Num, k + 1 ≤ n →
      ∃ a, M.mem (M.op k.1 a) g ∧ M.ValRaw P th io M.nat Nt j.1 d σ s k.1 a := by
  obtain ⟨s, hsR, hcode⟩ := M.seq_code hd.hP hd.hj ⟨d, M.d_rung hd⟩ hd.nt_zero hd.nt_succ n g
    (fun k hk => by
      obtain ⟨a, ha, hga⟩ := hg k hk
      exact ⟨a, M.inN_rung hd ha, hga⟩)
  refine ⟨s, hsR, fun k hk => ?_⟩
  obtain ⟨a, hga, hnt⟩ := hcode k hk
  exact ⟨a, hga, Or.inl ⟨hnt, hgN k a hk hga⟩⟩

/-- Truth with one value changed depends only on the sets denoted by the other values. -/
theorem tu_seq_sim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t t' w : V} (c v : M.Num) (hα : M.mem (M.op α α) th)
    (hw : M.InNRaw P th io M.nat j.1 α w)
    (hv : ∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d α t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e' ∧ M.SimRaw P j.1 tp F e e') :
    M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 t w ↔ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 t' w := by
  obtain ⟨t1, hag1⟩ := M.exists_upd hd hw t v.1 c
  obtain ⟨t2, hag2⟩ := M.exists_upd hd hw t' v.1 c
  rw [M.trueUpd_iff hd c v hag1, M.trueUpd_iff hd c v hag2]
  refine M.inv_hier hd c t1 t2 (fun i hi => ?_)
  by_cases e : i = v
  · rw [e] at hi ⊢
    exact ⟨w, w, M.agree_same hag1 hi, M.agree_same hag2 hi, M.inN_refl hd hw⟩
  · obtain ⟨e1, e1', w1, w1', hs⟩ := hv i hi
    exact ⟨e1, e1', M.agree_other hag1 hi e w1, M.agree_other hag2 hi e w1', hs⟩

/-- **Collection at the least stage that is not small**, in semantic form. Let `κ` be the
least stage that is not `ν`-small, with two stages above it. If for every member `y₀` of the
set denoted by a name `a` of rank below `κ` the formula `c` has a witness of rank below `κ`
for the variable `z`, when the variable `y` has the value `y₀`, then there is a stage `γ`
below `κ` such that the witnesses can be taken of rank below `γ`. -/
theorem next_coll (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) {κ : V}
    (hκ : M.IsNext P th Sg j ν κ) {σ' δ a t : V}
    (hκσ' : M.mem (M.op κ σ') th) (neκ : κ ≠ σ') (hσ'δ : M.mem (M.op σ' δ) th) (neσ' : σ' ≠ δ)
    (c y z : M.Num) (ha : M.InNRaw P th io M.nat j.1 κ a)
    (hyp : ∀ y0, M.InNRaw P th io M.nat j.1 κ y0 → M.EpsStarRaw P th io M.nat j.1 tp F y0 a → ∀ t1, M.AgreeRaw P th io M.nat Nt j.1 d M.adG κ t t1 y.1 y0 c.1 →
      ∃ z0, M.InNRaw P th io M.nat j.1 κ z0 ∧ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F κ c.1 z.1 t1 z0) :
    ∃ γ, M.mem (M.op γ κ) th ∧ γ ≠ κ ∧
      ∀ y0, M.InNRaw P th io M.nat j.1 κ y0 → M.EpsStarRaw P th io M.nat j.1 tp F y0 a → ∀ t1, M.AgreeRaw P th io M.nat Nt j.1 d M.adG κ t t1 y.1 y0 c.1 →
        ∃ z0, M.InNRaw P th io M.nat j.1 γ z0 ∧ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F κ c.1 z.1 t1 z0 := by
  have hth := hd.hth
  obtain ⟨hκκ, hns, hsm⟩ := hκ
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
  obtain ⟨oκ, hoκ⟩ := M.exists_mark hd hq hκκ
  have hdσ' : M.InNRaw P th io M.nat j.1 σ' d := M.d_inN hd hκσ' neκ
  -- the carrier name
  obtain ⟨c1, hc1⟩ : ∃ c1 : M.Num, c1 = c + 1 := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c2 : M.Num, c2 = c1 + 1 := ⟨_, rfl⟩
  obtain ⟨g, -, hg0⟩ := M.comp (σW [(0, 4), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7)])
    (Fml.ex 326 (Fml.ex 327 (.and (fPr 0 326 327) (.and (.mem 326 27) (Fml.or (.and (fLeN 326 301) (fVal 250 340 326 327)) (Fml.or (.and (.eq 326 345) (.eq 327 346)) (.and (.eq 326 347) (.eq 327 348)))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 250 κ) 301 c.1) 340 t) 345 c1.1) 346 a) 347 c2.1) 348 oκ)
  have hg1 : ∀ q, M.mem q g ↔ ∃ i e, q = M.op i e ∧ M.mem i M.nat ∧
      (((∃ x, M.mem x M.nat ∧ M.mem (M.trip i x c.1) M.adG) ∧ M.ValRaw P th io M.nat Nt j.1 d κ t i e) ∨
        (i = c1.1 ∧ e = a) ∨ (i = c2.1 ∧ e = oκ)) := by
    intro q
    rw [hg0 q]
    simp [Sat, M.sat_or, M.sat_ex, M.sat_fPr', M.sat_fVal, M.sat_fLeN, Function.update_apply]
  have hgs : ∀ (i : M.Num) (e : V), M.mem (M.op i.1 e) g ↔
      ((i ≤ c ∧ M.ValRaw P th io M.nat Nt j.1 d κ t i.1 e) ∨ (i = c1 ∧ e = a) ∨ (i = c2 ∧ e = oκ)) := by
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
  have hoκσ' : M.InNRaw P th io M.nat j.1 σ' oκ := M.rank_inN (M.mark_rank hq hoκ) hκσ' neκ
  have hvalσ' : ∀ {i e : V}, M.ValRaw P th io M.nat Nt j.1 d κ t i e → M.InNRaw P th io M.nat j.1 σ' e := by
    intro i e hv
    rcases M.val_cases hv with h | h
    · exact M.inN_mono hd h hκσ'
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
          obtain ⟨e0, ve0⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) κ t k.1
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
  have htN : ∀ (i : M.Num) (e : V), i ≤ c → M.ValRaw P th io M.nat Nt j.1 d κ t i.1 e → M.mem e N := by
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
  obtain ⟨-, -, -, oa, hoa, hoaN⟩ := M.cond_rank cd haN ra
  obtain ⟨β1, ry1, lt1, -⟩ := M.inN_rank hy1a
  have hy1N : M.mem y1 N := hlow hoa hoaN lta nea ry1 lt1
  obtain ⟨τ, hagτ⟩ := M.exists_upd hd hy1κ t y.1 c
  have hτN : ∀ i : M.Num, i ≤ c → ∀ e, M.ValRaw P th io M.nat Nt j.1 d κ τ i.1 e → M.mem e N := by
    intro i hi e hv
    by_cases e1 : i = y
    · rw [e1] at hv hi
      rw [M.val_unique hd hv (M.agree_same hagτ hi)]
      exact hy1N
    · obtain ⟨e0, ve0⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) κ t i.1
      rw [M.val_unique hd hv (M.agree_other hagτ hi e1 ve0)]
      exact htN i e0 hi ve0
  obtain ⟨z0, hz0, htu0⟩ := hyp y1 hy1κ ⟨y1, M.inN_refl hd hy1κ, ey1⟩ τ hagτ
  obtain ⟨w, hwN, hwκ, htuw⟩ := M.cond_lw_pos cd ((cd.hO κ).mpr (Or.inr ⟨oκ, hoκ, hoκN⟩)) c z
    hτN ⟨z0, hz0, htu0⟩
  obtain ⟨ζ, rw', ltζ, neζ⟩ := M.inN_rank hwκ
  refine ⟨w, hbelow hwN rw' ltζ neζ, (M.tu_seq_sim hd c z hκκ hwκ (fun i hi => ?_)).mp htuw⟩
  by_cases e1 : i = y
  · rw [e1] at hi ⊢
    exact ⟨y1, y0, M.agree_same hagτ hi, M.agree_same hag1 hi, M.sim_symm hd hsy⟩
  · obtain ⟨e0, ve0⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) κ t i.1
    exact ⟨e0, e0, M.agree_other hagτ hi e1 ve0, M.agree_other hag1 hi e1 ve0,
      M.val_sim_refl hd hκκ ve0⟩

end coll2

/-! ## Sizes: lifting between rungs, and tools for the count of a hull -/

theorem adG_iff (a b c : M.Num) : M.mem (M.trip a.1 b.1 c.1) M.adG ↔ a + b = c := by
  constructor
  · intro h
    exact Subtype.ext (M.graph₂_val M.adG_spec h).symm
  · intro h
    exact (M.adG_spec _ _ _).mpr ⟨a, b, rfl, rfl, by rw [← h]; rfl⟩

theorem adG_num {a b : M.Num} {c : V} (h : M.mem (M.trip a.1 b.1 c) M.adG) : c = (a + b).1 :=
  M.graph₂_val M.adG_spec h

/-- There is a one-to-one map of the rung `i` (name `395`) into the rung `n` (name `400`), if `i ≤ n ≤ m` (name `396`); the ladder is the name `393`. -/
def liftFml : Fml :=
  Fml.imp (fLeN 395 400) (Fml.imp (fLeN 400 396) (Fml.ex 397 (.and (.all 401 (Fml.imp (fApp 393
    395 401) (Fml.ex 402 (fApp 397 401 402)))) (.and (.all 401 (.all 402 (Fml.imp (fApp 397 401
    402) (.and (fApp 393 395 401) (fApp 393 400 402))))) (.and (.all 401 (.all 402 (.all 403
    (Fml.imp (fApp 397 401 402) (Fml.imp (fApp 397 401 403) (.eq 402 403)))))) (.all 401 (.all
    402 (.all 403 (Fml.imp (fApp 397 401 403) (Fml.imp (fApp 397 402 403) (.eq 401
    402)))))))))))

section lift

variable {R E z S : V} {m : M.Num}

theorem lift_id (R : V) (i : M.Num) : ∃ e, (∀ a, M.mem (M.op i.1 a) R → ∃ a', M.mem (M.op a a') e) ∧
      (∀ a a', M.mem (M.op a a') e → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 a') R) ∧
      (∀ a a' a'', M.mem (M.op a a') e → M.mem (M.op a a'') e → a' = a'') ∧
      (∀ a a' c, M.mem (M.op a c) e → M.mem (M.op a' c) e → a = a') := by
  obtain ⟨e, -, he0⟩ := M.comp (σW [(0, 4), (393, 5)]) (Fml.ex 401 (.and (fPr 0 401 401) (fApp 393 395 401))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 393 R) 395 i.1)
  have he1 : ∀ q, M.mem q e ↔ ∃ x, q = M.op x x ∧ M.mem (M.op i.1 x) R := by
    intro q
    rw [he0 q]
    simp [Sat, M.sat_ex, M.sat_fPr', M.sat_fApp', Function.update_apply]
  have he : ∀ a a', M.mem (M.op a a') e ↔ a = a' ∧ M.mem (M.op i.1 a) R := by
    intro a a'
    rw [he1]
    constructor
    · rintro ⟨x, hx, hR⟩
      obtain ⟨e1, e2⟩ := M.op_inj hx
      rw [e1, e2]
      exact ⟨rfl, hR⟩
    · rintro ⟨e1, hR⟩
      exact ⟨a, by rw [e1], hR⟩
  refine ⟨e, fun a ha => ⟨a, (he a a).mpr ⟨rfl, ha⟩⟩, fun a a' h => ?_, fun a a' a'' h1 h2 => ?_,
    fun a a' c h1 h2 => ?_⟩
  · obtain ⟨e1, hR⟩ := (he a a').mp h
    exact ⟨hR, by rw [← e1]; exact hR⟩
  · exact ((he a a').mp h1).1.symm.trans ((he a a'').mp h2).1
  · exact ((he a c).mp h1).1.trans ((he a' c).mp h2).1.symm

theorem lift_step (h : M.IsLadder R E z S m) {i n : M.Num} (hn : n + 1 ≤ m) {e : V}
    (he : (∀ a, M.mem (M.op i.1 a) R → ∃ a', M.mem (M.op a a') e) ∧
      (∀ a a', M.mem (M.op a a') e → M.mem (M.op i.1 a) R ∧ M.mem (M.op n.1 a') R) ∧
      (∀ a a' a'', M.mem (M.op a a') e → M.mem (M.op a a'') e → a' = a'') ∧
      (∀ a a' c, M.mem (M.op a c) e → M.mem (M.op a' c) e → a = a')) :
    ∃ e', (∀ a, M.mem (M.op i.1 a) R → ∃ a', M.mem (M.op a a') e') ∧
      (∀ a a', M.mem (M.op a a') e' → M.mem (M.op i.1 a) R ∧ M.mem (M.op (n + 1).1 a') R) ∧
      (∀ a a' a'', M.mem (M.op a a') e' → M.mem (M.op a a'') e' → a' = a'') ∧
      (∀ a a' c, M.mem (M.op a c) e' → M.mem (M.op a' c) e' → a = a') := by
  obtain ⟨e1, e2, e3, e4⟩ := he
  obtain ⟨e', -, he0⟩ := M.comp (σW [(0, 4), (393, 5), (394, 7), (397, 5)]) (Fml.ex 401 (Fml.ex 402 (Fml.ex 403 (.and (fPr 0 401 402) (.and (fApp 397 401 403) (.and (fApp 393 398 402) (.all 404 (Fml.iff (.and (fApp 393 400 404) (fApp3 394 400 404 402)) (.eq 404 403))))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 393 R) 394 E) 397 e) 398 (n + 1).1) 400 n.1)
  have he1 : ∀ q, M.mem q e' ↔ ∃ x y a', q = M.op x y ∧ M.mem (M.op x a') e ∧
      M.mem (M.op (n + 1).1 y) R ∧
      ∀ x', (M.mem (M.op n.1 x') R ∧ M.mem (M.trip n.1 x' y) E) ↔ x' = a' := by
    intro q
    rw [he0 q]
    simp [Sat, M.sat_ex, M.sat_iff, M.sat_fPr', M.sat_fApp', M.sat_fApp3', Function.update_apply]
  have he' : ∀ a c, M.mem (M.op a c) e' ↔ ∃ a', M.mem (M.op a a') e ∧ M.mem (M.op (n + 1).1 c) R ∧
      ∀ x, (M.mem (M.op n.1 x) R ∧ M.mem (M.trip n.1 x c) E) ↔ x = a' := by
    intro a c
    rw [he1]
    constructor
    · rintro ⟨x, y, a', hxy, h1, h2, h3⟩
      obtain ⟨q1, q2⟩ := M.op_inj hxy
      rw [q1, q2]
      exact ⟨a', h1, h2, h3⟩
    · rintro ⟨a', h1, h2, h3⟩
      exact ⟨a, c, a', rfl, h1, h2, h3⟩
  refine ⟨e', fun a ha => ?_, fun a c hc => ?_, fun a c c' h1 h2 => ?_, fun a a2 c h1 h2 => ?_⟩
  · obtain ⟨a', ha'⟩ := e1 a ha
    obtain ⟨b, hb, hmem, -⟩ := h.full n hn (M.sing a') (M.sing_isSet a') (fun x hx => by
      rw [M.mem_sing.mp hx]
      exact (e2 a a' ha').2)
    exact ⟨b, (he' a b).mpr ⟨a', ha', hb, fun x => ((hmem x).symm.trans M.mem_sing)⟩⟩
  · obtain ⟨a', h1, h2, -⟩ := (he' a c).mp hc
    exact ⟨(e2 a a' h1).1, h2⟩
  · obtain ⟨a', k1, k2, k3⟩ := (he' a c).mp h1
    obtain ⟨a'', l1, l2, l3⟩ := (he' a c').mp h2
    have ea : a' = a'' := e3 a a' a'' k1 l1
    obtain ⟨b, hb, hmem, huniq⟩ := h.full n hn (M.sing a') (M.sing_isSet a') (fun x hx => by
      rw [M.mem_sing.mp hx]
      exact (e2 a a' k1).2)
    have c1 : c = b := huniq c k2 (fun x => M.mem_sing.trans (k3 x).symm)
    have c2 : c' = b := huniq c' l2 (fun x => M.mem_sing.trans (by rw [ea]; exact (l3 x).symm))
    rw [c1, c2]
  · obtain ⟨a', k1, k2, k3⟩ := (he' a c).mp h1
    obtain ⟨a'', l1, l2, l3⟩ := (he' a2 c).mp h2
    have ea : a' = a'' := (l3 a').mp ((k3 a').mpr rfl)
    rw [← ea] at l1
    exact e4 a a2 a' k1 l1

/-- **Lifting.** A lower rung of a ladder maps one-to-one into every higher rung. -/
theorem rung_lift (h : M.IsLadder R E z S m) (i n : M.Num) (hin : i ≤ n) (hn : n ≤ m) :
    ∃ e, (∀ a, M.mem (M.op i.1 a) R → ∃ a', M.mem (M.op a a') e) ∧
      (∀ a a', M.mem (M.op a a') e → M.mem (M.op i.1 a) R ∧ M.mem (M.op n.1 a') R) ∧
      (∀ a a' a'', M.mem (M.op a a') e → M.mem (M.op a a'') e → a' = a'') ∧
      (∀ a a' c, M.mem (M.op a c) e → M.mem (M.op a' c) e → a = a') := by
  have hsat : ∀ n : M.Num, Sat M.mem M.isSet liftFml (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 27 M.nat) 28 M.adG) 393 R) 395 i.1) 396 m.1) 400 n.1) ↔
      (i ≤ n → n ≤ m → ∃ e, (∀ a, M.mem (M.op i.1 a) R → ∃ a', M.mem (M.op a a') e) ∧
      (∀ a a', M.mem (M.op a a') e → M.mem (M.op i.1 a) R ∧ M.mem (M.op n.1 a') R) ∧
      (∀ a a' a'', M.mem (M.op a a') e → M.mem (M.op a a'') e → a' = a'') ∧
      (∀ a a' c, M.mem (M.op a c) e → M.mem (M.op a' c) e → a = a')) := by
    intro n
    rw [← M.leRaw_iff M.adG_spec i n, ← M.leRaw_iff M.adG_spec n m]
    simp [liftFml, LeRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fLeN, M.sat_fApp', Function.update_apply]
  have key := M.num_ind_fml (σW [(27, 3), (28, 7), (393, 5), (397, 5)]) liftFml 400 rfl (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 27 M.nat) 28 M.adG) 393 R) 395 i.1) 396 m.1)
    ?_ ?_ n
  · exact (hsat n).mp key hin hn
  · rw [show M.zero = (0 : M.Num).1 from rfl, hsat 0]
    intro h0 _
    have e0 : i = 0 := le_antisymm h0 zero_le
    rw [e0]
    exact M.lift_id R 0
  · intro k ih
    rw [show M.succ k.1 = (k + 1).1 from (M.val_add_one k).symm, hsat (k + 1)]
    intro h1 h2
    rcases M.eq_or_succ_le h1 with e1 | e1
    · rw [e1]
      exact M.lift_id R (k + 1)
    · obtain ⟨e, he⟩ := (hsat k).mp ih (M.le_of_succ_le_succ e1) (le_trans (M.le_add_one k) h2)
      exact M.lift_step h h2 he

end lift

/-- `LWp`, with `α`, `c`, `v`, `t`, `w` the names `300`, `301`, `303`, `304`, `306`. -/
def lwpFml : Fml :=
  .and (Fml.ex 65 (.and (.eq 65 300) (fInN 306))) (.and (Fml.ex 305 (.and (.eq 305 306)
    trueUpdFml)) (.all 307 (Fml.imp (Fml.ex 65 (.and (.eq 65 300) (fInN 307))) (Fml.imp (Fml.ex
    305 (.and (.eq 305 307) trueUpdFml)) (fApp 162 306 307)))))

/-- `LWn`, with the same names. -/
def lwnFml : Fml :=
  .and (Fml.ex 65 (.and (.eq 65 300) (fInN 306))) (.and (.neg (Fml.ex 305 (.and (.eq 305 306)
    trueUpdFml))) (.all 307 (Fml.imp (Fml.ex 65 (.and (.eq 65 300) (fInN 307))) (Fml.imp (.neg
    (Fml.ex 305 (.and (.eq 305 307) trueUpdFml))) (fApp 162 306 307)))))

/-- `w` is a least name of rank below `α` at which the formula `c` is true, the variable `v`
having the value `w`. -/
def LWp (P th io nat Nt j d ad F Pr α c v t w : V) : Prop :=
  M.InNRaw P th io nat j α w ∧ M.TrueUpdR P th io nat Nt j d ad F α c v t w ∧
    ∀ w', M.InNRaw P th io nat j α w' → M.TrueUpdR P th io nat Nt j d ad F α c v t w' →
      M.mem (M.op w w') Pr

/-- `w` is a least name of rank below `α` at which the formula `c` is false. -/
def LWn (P th io nat Nt j d ad F Pr α c v t w : V) : Prop :=
  M.InNRaw P th io nat j α w ∧ ¬ M.TrueUpdR P th io nat Nt j d ad F α c v t w ∧
    ∀ w', M.InNRaw P th io nat j α w' → ¬ M.TrueUpdR P th io nat Nt j d ad F α c v t w' →
      M.mem (M.op w w') Pr

theorem sat_lwpFml (ρ : ℕ → V) : Sat M.mem M.isSet lwpFml ρ ↔
    M.LWp (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 163) (ρ 162) (ρ 300) (ρ 301)
      (ρ 303) (ρ 304) (ρ 306) := by
  simp [lwpFml, LWp, Sat, M.sat_imp, M.sat_ex, M.sat_fInN, M.sat_fApp',
    M.sat_trueUpdFml, Function.update_apply]

theorem sat_lwnFml (ρ : ℕ → V) : Sat M.mem M.isSet lwnFml ρ ↔
    M.LWn (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 163) (ρ 162) (ρ 300) (ρ 301)
      (ρ 303) (ρ 304) (ρ 306) := by
  simp [lwnFml, LWn, Sat, M.sat_imp, M.sat_ex, M.sat_fInN, M.sat_fApp',
    M.sat_trueUpdFml, Function.update_apply]

theorem lwR_iff {P th io nat Nt j d ad F Pr α c v t w : V} :
    M.LWR P th io nat Nt j d ad F Pr α c v t w ↔
      M.LWp P th io nat Nt j d ad F Pr α c v t w ∨ M.LWn P th io nat Nt j d ad F Pr α c v t w := by
  unfold LWR LWp LWn
  constructor
  · rintro ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2, h3⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨h1, Or.inl ⟨h2, h3⟩⟩
    · exact ⟨h1, Or.inr ⟨h2, h3⟩⟩

section sizes1

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {ν Sg : V}
variable {q1 : V}

/-- A closed set that contains the default name and a name of every rank below `ν` contains
every name of rank below `ν`. -/
theorem closed_below (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    {X ρ ν ν' G' : V} (hX : M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr G' X ρ ν') (hdX : M.mem d X)
    (hνρ : M.mem (M.op ν ρ) th)
    (hords : ∀ β', M.mem (M.op β' ν) th → β' ≠ ν → ∃ n o, M.mem n X ∧ M.RankIs P io M.nat j.1 β' n ∧
      M.mem (M.quad j.1 β' q1 o) P)
    {x : V} (hx : M.InNRaw P th io M.nat j.1 ν x) : M.mem x X := by
  obtain ⟨β, rx, ltβ, neβ⟩ := M.inN_rank hx
  have hβ := (hd.hth.fld _ _ ltβ).1
  have hsat : ∀ α, Sat M.mem M.isSet (.all 320 (Fml.imp (fRank 250 320) (Fml.imp (fApp 22 250 272) (Fml.imp (.neg (.eq 250 272)) (.mem 320 270)))))
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 270 X) 272 ν) 250 α) ↔
      ∀ n, M.RankIs P io M.nat j.1 α n → M.mem (M.op α ν) th → ¬ α = ν → M.mem n X := by
    intro α
    simp [Sat, M.sat_imp, M.sat_fRank, M.sat_fApp', Function.update_apply]
  have key := M.wo_ind_fml hd.hth (σW [(20, 7), (22, 5), (24, 5), (27, 3), (270, 3)])
    (.all 320 (Fml.imp (fRank 250 320) (Fml.imp (fApp 22 250 272) (Fml.imp (.neg (.eq 250 272)) (.mem 320 270))))) 250 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 270 X) 272 ν)
    (fun α hα ih => ?_) β hβ
  · exact (hsat β).mp key x rx ltβ neβ
  · rw [hsat α]
    have ih' : ∀ β', M.mem (M.op β' α) th → β' ≠ α → ∀ n, M.RankIs P io M.nat j.1 β' n →
        M.mem (M.op β' ν) th → ¬ β' = ν → M.mem n X :=
      fun β' h1 h2 => (hsat β').mp (ih β' h1 h2)
    intro n rn ltα neα
    obtain ⟨n0, o, hn0X, rn0, ho⟩ := hords α ltα neα
    have hoX := hX.1 n0 α o hn0X rn0 ho
    have ltρ : M.mem (M.op α ρ) th := hd.hth.trans _ _ _ ltα hνρ
    have neρ : α ≠ ρ := M.wo_ne_of_lt_le hd.hth ltα neα hνρ
    refine M.closed_rank hd hX ltρ neρ ho hoX (fun y hy => ?_) hdX rn
    obtain ⟨β1, ry, lt1, ne1⟩ := M.inN_rank hy
    refine ih' β1 lt1 ne1 y ry (hd.hth.trans _ _ _ lt1 ltα) (fun e => ?_)
    rw [e] at lt1
    exact neα (hd.hth.antisymm _ _ ltα lt1)

/-- A sequence whose values at the stage `ρ` are the values of `u` at an earlier stage `β`
up to the index `c`, followed by the name `o`. -/
theorem exists_shift_seq (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {β ρ u o : V} (c : M.Num)
    (hβρ : M.mem (M.op β ρ) th) (hne : β ≠ ρ) (ho : M.InNRaw P th io M.nat j.1 ρ o) :
    ∃ w, M.mem (M.op j.1 w) R ∧ (∀ i : M.Num, i ≤ c → ∀ e, M.ValRaw P th io M.nat Nt j.1 d β u i.1 e → M.ValRaw P th io M.nat Nt j.1 d ρ w i.1 e) ∧
      M.ValRaw P th io M.nat Nt j.1 d ρ w (c + 1).1 o := by
  obtain ⟨g, -, hg0⟩ := M.comp (σW [(0, 4), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7)])
    (Fml.ex 326 (Fml.ex 327 (.and (fPr 0 326 327) (.and (.mem 326 27) (Fml.or (.and (fLeN 326 301) (fVal 250 340 326 327)) (.and (.eq 326 345) (.eq 327 346))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 250 β) 301 c.1) 340 u) 345 (c + 1).1) 346 o)
  have hg1 : ∀ q, M.mem q g ↔ ∃ i e, q = M.op i e ∧ M.mem i M.nat ∧
      (((∃ x, M.mem x M.nat ∧ M.mem (M.trip i x c.1) M.adG) ∧ M.ValRaw P th io M.nat Nt j.1 d β u i e) ∨
        (i = (c + 1).1 ∧ e = o)) := by
    intro q
    rw [hg0 q]
    simp [Sat, M.sat_or, M.sat_ex, M.sat_fPr', M.sat_fVal, M.sat_fLeN, Function.update_apply]
  have hgs : ∀ (i : M.Num) (e : V), M.mem (M.op i.1 e) g ↔
      ((i ≤ c ∧ M.ValRaw P th io M.nat Nt j.1 d β u i.1 e) ∨ (i = c + 1 ∧ e = o)) := by
    intro i e
    rw [hg1]
    constructor
    · rintro ⟨i', e', hq, -, h | ⟨h1, h2⟩⟩
      · obtain ⟨q1', q2'⟩ := M.op_inj hq
        rw [← q1', ← q2'] at h
        exact Or.inl ⟨(M.leRaw_iff M.adG_spec i c).mp h.1, h.2⟩
      · obtain ⟨q1', q2'⟩ := M.op_inj hq
        rw [← q1'] at h1
        rw [← q2'] at h2
        exact Or.inr ⟨Subtype.ext h1, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨i.1, e, rfl, i.2, Or.inl ⟨(M.leRaw_iff M.adG_spec i c).mpr h1, h2⟩⟩
      · exact ⟨i.1, e, rfl, i.2, Or.inr ⟨by rw [h1], h2⟩⟩
  have hvalN : ∀ (i : M.Num) (e : V), M.ValRaw P th io M.nat Nt j.1 d β u i.1 e → M.InNRaw P th io M.nat j.1 ρ e := by
    intro i e hv
    rcases M.val_cases hv with h | h
    · exact M.inN_mono hd h hβρ
    · rw [h]
      exact M.d_inN hd hβρ hne
  obtain ⟨w, hwR, hw⟩ := M.exists_seq_vals hd (σ := ρ) (g := g) (c + 1 + 1)
    (fun k hk => by
      have hk' : k ≤ c + 1 := M.le_of_succ_le_succ hk
      rcases M.eq_or_succ_le hk' with e1 | e1
      · exact ⟨o, ho, (hgs k o).mpr (Or.inr ⟨e1, rfl⟩)⟩
      · obtain ⟨e, he⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) β u k.1
        exact ⟨e, hvalN k e he, (hgs k e).mpr (Or.inl ⟨M.le_of_succ_le_succ e1, he⟩)⟩)
    (fun k a hk hka => by
      rcases (hgs k a).mp hka with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact hvalN k a h2
      · rw [h2]
        exact ho)
  refine ⟨w, hwR, fun i hi e he => ?_, ?_⟩
  · obtain ⟨a, hga, hva⟩ := hw i (by
      have : i + 1 ≤ c + 1 := add_le_add_left hi 1
      exact le_trans this (M.le_add_one _))
    rcases (hgs i a).mp hga with ⟨-, h2⟩ | ⟨h1, -⟩
    · rw [M.val_unique hd he h2]
      exact hva
    · rw [h1] at hi
      exact (M.not_succ_le c hi).elim
  · obtain ⟨a, hga, hva⟩ := hw (c + 1) (le_refl _)
    rcases (hgs (c + 1) a).mp hga with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact (M.not_succ_le c h1).elim
    · rw [← h2]
      exact hva

end sizes1
/-! ## Terms for the members of a hull -/

/-- Clause `0` of the rules for terms; the arity `c`, the number `v`, the atom `a`, the inputs `w` and the output `n` are the names `381`–`385`. -/
def rc0Fml : Fml :=
  .and (.eq 381 180) (Fml.ex 421 (.and (fApp 177 421 383) (fApp4 20 25 421 160 385)))

def RC0 (P j q1 g t0 c a n : V) : Prop :=
  c = t0 ∧ ∃ β, M.mem (M.op β a) g ∧ M.mem (M.quad j β q1 n) P

theorem sat_rc0Fml (ρ : ℕ → V) : Sat M.mem M.isSet rc0Fml ρ ↔
    M.RC0 (ρ 20) (ρ 25) (ρ 160) (ρ 177) (ρ 180) (ρ 381) (ρ 383) (ρ 385) := by
  simp [rc0Fml, RC0, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fRank, M.sat_fLeN, M.sat_fCan, M.sat_fSim, M.sat_fApp', M.sat_fApp3', M.sat_fApp4', M.sat_lwpFml, M.sat_lwnFml, Function.update_apply]

/-- Clause `3` of the rules for terms; the arity `c`, the number `v`, the atom `a`, the inputs `w` and the output `n` are the names `381`–`385`. -/
def rc3Fml : Fml :=
  .and (.eq 381 181) (Fml.ex 420 (Fml.ex 421 (.and (Fml.ex 388 (.and (.eq 388 180) (fVal 271 384
    388 420))) (.and (fRank 421 420) (fApp4 20 25 421 160 385)))))

def RC3 (P th io nat Nt j d q1 ρ t0 t1 c w n : V) : Prop :=
  c = t1 ∧ ∃ n0 β, M.ValRaw P th io nat Nt j d ρ w t0 n0 ∧ M.RankIs P io nat j β n0 ∧ M.mem (M.quad j β q1 n) P

theorem sat_rc3Fml (ρ : ℕ → V) : Sat M.mem M.isSet rc3Fml ρ ↔
    M.RC3 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 160) (ρ 271) (ρ 180) (ρ 181) (ρ 381) (ρ 384) (ρ 385) := by
  simp [rc3Fml, RC3, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fRank, M.sat_fLeN, M.sat_fCan, M.sat_fSim, M.sat_fApp', M.sat_fApp3', M.sat_fApp4', M.sat_lwpFml, M.sat_lwnFml, Function.update_apply]

/-- Clause `4` of the rules for terms; the arity `c`, the number `v`, the atom `a`, the inputs `w` and the output `n` are the names `381`–`385`. -/
def rc4Fml : Fml :=
  .and (.eq 381 181) (Fml.ex 420 (Fml.ex 421 (Fml.ex 422 (Fml.ex 423 (.and (Fml.ex 388 (.and
    (.eq 388 180) (fVal 271 384 388 420))) (.and (Fml.ex 262 (Fml.ex 263 (.and (fApp4 20 25 421
    263 420) (.and (fApp4 20 25 262 423 263) (.and (.mem 422 27) (fApp 24 422 262)))))) (.and
    (fLeN 382 422) (fVal 421 423 382 385))))))))

def RC4 (P th io nat Nt j d ad ρ t0 t1 c v w n : V) : Prop :=
  c = t1 ∧ ∃ n0 β c' u, M.ValRaw P th io nat Nt j d ρ w t0 n0 ∧ M.NameR P io nat j n0 β c' u ∧ (∃ y, M.mem y nat ∧ M.mem (M.trip v y c') ad) ∧ M.ValRaw P th io nat Nt j d β u v n

theorem sat_rc4Fml (ρ : ℕ → V) : Sat M.mem M.isSet rc4Fml ρ ↔
    M.RC4 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 271) (ρ 180) (ρ 181) (ρ 381) (ρ 382) (ρ 384) (ρ 385) := by
  simp [rc4Fml, RC4, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fRank, M.sat_fLeN, M.sat_fCan, M.sat_fSim, M.sat_fApp', M.sat_fApp3', M.sat_fApp4', M.sat_lwpFml, M.sat_lwnFml, Function.update_apply]

/-- Clause `5` of the rules for terms; the arity `c`, the number `v`, the atom `a`, the inputs `w` and the output `n` are the names `381`–`385`. -/
def rc5Fml : Fml :=
  Fml.ex 422 (Fml.ex 424 (Fml.ex 425 (Fml.ex 421 (Fml.ex 423 (.and (fApp3 28 422 181 424) (.and
    (fApp3 28 424 181 381) (.and (fVal 271 384 424 425) (.and (fApp4 20 25 421 160 425) (.and
    (fApp 22 421 271) (.and (.neg (.eq 421 271)) (.and (Fml.ex 262 (Fml.ex 263 (.and (fApp4 20
    25 421 263 385) (.and (fApp4 20 25 262 423 263) (.and (.mem 422 27) (fApp 24 422 262))))))
    (.all 428 (.all 429 (Fml.imp (.mem 428 27) (Fml.imp (fLeN 428 422) (Fml.imp (fVal 421 423
    428 429) (fVal 271 384 428 429)))))))))))))))))

def RC5 (P th io nat Nt j d ad q1 ρ t1 c w n : V) : Prop :=
  ∃ c' k1 o β u, M.mem (M.trip c' t1 k1) ad ∧ M.mem (M.trip k1 t1 c) ad ∧ M.ValRaw P th io nat Nt j d ρ w k1 o ∧ M.mem (M.quad j β q1 o) P ∧ M.mem (M.op β ρ) th ∧ ¬ β = ρ ∧ M.NameR P io nat j n β c' u ∧ ∀ i e, M.mem i nat → (∃ y, M.mem y nat ∧ M.mem (M.trip i y c') ad) → M.ValRaw P th io nat Nt j d β u i e → M.ValRaw P th io nat Nt j d ρ w i e

theorem sat_rc5Fml (ρ : ℕ → V) : Sat M.mem M.isSet rc5Fml ρ ↔
    M.RC5 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 160) (ρ 271) (ρ 181) (ρ 381) (ρ 384) (ρ 385) := by
  simp [rc5Fml, RC5, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fRank, M.sat_fLeN, M.sat_fCan, M.sat_fSim, M.sat_fApp', M.sat_fApp3', M.sat_fApp4', M.sat_lwpFml, M.sat_lwnFml, Function.update_apply]

/-- Clause `6` of the rules for terms; the arity `c`, the number `v`, the atom `a`, the inputs `w` and the output `n` are the names `381`–`385`. -/
def rc6Fml : Fml :=
  .and (.eq 381 181) (Fml.ex 420 (.and (Fml.ex 388 (.and (.eq 388 180) (fVal 271 384 388 420)))
    (.and (Fml.ex 6 (.and (.eq 6 163) (fCan 385))) (Fml.ex 6 (.and (.eq 6 163) (fSim 420
    385))))))

def RC6 (P th io nat Nt j d tp F Pr ρ t0 t1 c w n : V) : Prop :=
  c = t1 ∧ ∃ n0, M.ValRaw P th io nat Nt j d ρ w t0 n0 ∧ M.IsCan P j tp F Pr n ∧ M.SimRaw P j tp F n0 n

theorem sat_rc6Fml (ρ : ℕ → V) : Sat M.mem M.isSet rc6Fml ρ ↔
    M.RC6 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 21) (ρ 163) (ρ 162) (ρ 271) (ρ 180) (ρ 181) (ρ 381) (ρ 384) (ρ 385) := by
  simp [rc6Fml, RC6, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fRank, M.sat_fLeN, M.sat_fCan, M.sat_fSim, M.sat_fApp', M.sat_fApp3', M.sat_fApp4', M.sat_lwpFml, M.sat_lwnFml, Function.update_apply]

/-- Clause `7` of the rules for terms; the arity `c`, the number `v`, the atom `a`, the inputs `w` and the output `n` are the names `381`–`385`. -/
def rc7Fml : Fml :=
  Fml.ex 426 (.and (.mem 426 27) (.and (fApp3 28 426 181 381) (Fml.ex 300 (.and (.eq 300 271)
    (Fml.ex 301 (.and (.eq 301 426) (Fml.ex 303 (.and (.eq 303 382) (Fml.ex 304 (.and (.eq 304
    384) (Fml.ex 306 (.and (.eq 306 385) lwpFml))))))))))))

def RC7 (P th io nat Nt j d ad F Pr ρ t1 c v w n : V) : Prop :=
  ∃ cf, M.mem cf nat ∧ M.mem (M.trip cf t1 c) ad ∧ M.LWp P th io nat Nt j d ad F Pr ρ cf v w n

theorem sat_rc7Fml (ρ : ℕ → V) : Sat M.mem M.isSet rc7Fml ρ ↔
    M.RC7 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 163) (ρ 162) (ρ 271) (ρ 181) (ρ 381) (ρ 382) (ρ 384) (ρ 385) := by
  simp [rc7Fml, RC7, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fRank, M.sat_fLeN, M.sat_fCan, M.sat_fSim, M.sat_fApp', M.sat_fApp3', M.sat_fApp4', M.sat_lwpFml, M.sat_lwnFml, Function.update_apply]

/-- Clause `8` of the rules for terms; the arity `c`, the number `v`, the atom `a`, the inputs `w` and the output `n` are the names `381`–`385`. -/
def rc8Fml : Fml :=
  Fml.ex 426 (.and (.mem 426 27) (.and (fApp3 28 426 181 381) (Fml.ex 300 (.and (.eq 300 271)
    (Fml.ex 301 (.and (.eq 301 426) (Fml.ex 303 (.and (.eq 303 382) (Fml.ex 304 (.and (.eq 304
    384) (Fml.ex 306 (.and (.eq 306 385) lwnFml))))))))))))

def RC8 (P th io nat Nt j d ad F Pr ρ t1 c v w n : V) : Prop :=
  ∃ cf, M.mem cf nat ∧ M.mem (M.trip cf t1 c) ad ∧ M.LWn P th io nat Nt j d ad F Pr ρ cf v w n

theorem sat_rc8Fml (ρ : ℕ → V) : Sat M.mem M.isSet rc8Fml ρ ↔
    M.RC8 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 163) (ρ 162) (ρ 271) (ρ 181) (ρ 381) (ρ 382) (ρ 384) (ρ 385) := by
  simp [rc8Fml, RC8, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fRank, M.sat_fLeN, M.sat_fCan, M.sat_fSim, M.sat_fApp', M.sat_fApp3', M.sat_fApp4', M.sat_lwpFml, M.sat_lwnFml, Function.update_apply]

/-- Clause `9` of the rules for terms; the arity `c`, the number `v`, the atom `a`, the inputs `w` and the output `n` are the names `381`–`385`. -/
def rc9Fml : Fml :=
  Fml.ex 426 (Fml.ex 424 (Fml.ex 425 (Fml.ex 421 (Fml.ex 427 (.and (.mem 426 27) (.and (fApp3 28
    426 181 424) (.and (fApp3 28 424 181 381) (.and (fVal 271 384 424 425) (.and (fApp4 20 25
    421 160 425) (.and (fApp 22 421 271) (.and (.neg (.eq 421 271)) (.and (.all 428 (.all 429
    (Fml.imp (.mem 428 27) (Fml.imp (fLeN 428 426) (Fml.imp (fVal 421 427 428 429) (fVal 271 384
    428 429)))))) (Fml.ex 300 (.and (.eq 300 421) (Fml.ex 301 (.and (.eq 301 426) (Fml.ex 303
    (.and (.eq 303 382) (Fml.ex 304 (.and (.eq 304 427) (Fml.ex 306 (.and (.eq 306 385)
    lwpFml))))))))))))))))))))))

def RC9 (P th io nat Nt j d ad q1 F Pr ρ t1 c v w n : V) : Prop :=
  ∃ cf k1 o β t, M.mem cf nat ∧ M.mem (M.trip cf t1 k1) ad ∧ M.mem (M.trip k1 t1 c) ad ∧ M.ValRaw P th io nat Nt j d ρ w k1 o ∧ M.mem (M.quad j β q1 o) P ∧ M.mem (M.op β ρ) th ∧ ¬ β = ρ ∧ (∀ i e, M.mem i nat → (∃ y, M.mem y nat ∧ M.mem (M.trip i y cf) ad) → M.ValRaw P th io nat Nt j d β t i e → M.ValRaw P th io nat Nt j d ρ w i e) ∧ M.LWp P th io nat Nt j d ad F Pr β cf v t n

theorem sat_rc9Fml (ρ : ℕ → V) : Sat M.mem M.isSet rc9Fml ρ ↔
    M.RC9 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 160) (ρ 163) (ρ 162) (ρ 271) (ρ 181) (ρ 381) (ρ 382) (ρ 384) (ρ 385) := by
  simp [rc9Fml, RC9, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fRank, M.sat_fLeN, M.sat_fCan, M.sat_fSim, M.sat_fApp', M.sat_fApp3', M.sat_fApp4', M.sat_lwpFml, M.sat_lwnFml, Function.update_apply]

/-- Clause `10` of the rules for terms; the arity `c`, the number `v`, the atom `a`, the inputs `w` and the output `n` are the names `381`–`385`. -/
def rc10Fml : Fml :=
  Fml.ex 426 (Fml.ex 424 (Fml.ex 425 (Fml.ex 421 (Fml.ex 427 (.and (.mem 426 27) (.and (fApp3 28
    426 181 424) (.and (fApp3 28 424 181 381) (.and (fVal 271 384 424 425) (.and (fApp4 20 25
    421 160 425) (.and (fApp 22 421 271) (.and (.neg (.eq 421 271)) (.and (.all 428 (.all 429
    (Fml.imp (.mem 428 27) (Fml.imp (fLeN 428 426) (Fml.imp (fVal 421 427 428 429) (fVal 271 384
    428 429)))))) (Fml.ex 300 (.and (.eq 300 421) (Fml.ex 301 (.and (.eq 301 426) (Fml.ex 303
    (.and (.eq 303 382) (Fml.ex 304 (.and (.eq 304 427) (Fml.ex 306 (.and (.eq 306 385)
    lwnFml))))))))))))))))))))))

def RC10 (P th io nat Nt j d ad q1 F Pr ρ t1 c v w n : V) : Prop :=
  ∃ cf k1 o β t, M.mem cf nat ∧ M.mem (M.trip cf t1 k1) ad ∧ M.mem (M.trip k1 t1 c) ad ∧ M.ValRaw P th io nat Nt j d ρ w k1 o ∧ M.mem (M.quad j β q1 o) P ∧ M.mem (M.op β ρ) th ∧ ¬ β = ρ ∧ (∀ i e, M.mem i nat → (∃ y, M.mem y nat ∧ M.mem (M.trip i y cf) ad) → M.ValRaw P th io nat Nt j d β t i e → M.ValRaw P th io nat Nt j d ρ w i e) ∧ M.LWn P th io nat Nt j d ad F Pr β cf v t n

theorem sat_rc10Fml (ρ : ℕ → V) : Sat M.mem M.isSet rc10Fml ρ ↔
    M.RC10 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 160) (ρ 163) (ρ 162) (ρ 271) (ρ 181) (ρ 381) (ρ 382) (ρ 384) (ρ 385) := by
  simp [rc10Fml, RC10, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fRank, M.sat_fLeN, M.sat_fCan, M.sat_fSim, M.sat_fApp', M.sat_fApp3', M.sat_fApp4', M.sat_lwpFml, M.sat_lwnFml, Function.update_apply]

/-- Clause `11` of the rules for terms; the arity `c`, the number `v`, the atom `a`, the inputs `w` and the output `n` are the names `381`–`385`. -/
def rc11Fml : Fml :=
  .and (.eq 381 181) (Fml.ex 430 (Fml.ex 431 (Fml.ex 432 (Fml.ex 433 (Fml.ex 434 (.and (Fml.ex
    388 (.and (.eq 388 180) (fVal 271 384 388 430))) (.and (fApp4 20 25 431 160 430) (.and (fApp
    22 431 432) (.and (fApp4 20 25 272 433 434) (.and (fApp 179 432 434) (.and (.all 435 (.all
    436 (.all 437 (Fml.imp (fApp4 20 25 272 436 437) (Fml.imp (fApp 179 435 437) (Fml.imp (fApp
    22 431 435) (fApp 22 432 435))))))) (.and (.all 436 (.all 437 (Fml.imp (fApp4 20 25 272 436
    437) (Fml.imp (fApp 179 432 437) (fApp 162 433 436))))) (fApp4 20 25 432 160
    385)))))))))))))

def RC11 (P th io nat Nt j d q1 Pr G ρ ν t0 t1 c w n : V) : Prop :=
  c = t1 ∧ ∃ o1 β1 β2 w0 y, M.ValRaw P th io nat Nt j d ρ w t0 o1 ∧ M.mem (M.quad j β1 q1 o1) P ∧ M.mem (M.op β1 β2) th ∧ M.mem (M.quad j ν w0 y) P ∧ M.mem (M.op β2 y) G ∧ (∀ β' b' y', M.mem (M.quad j ν b' y') P → M.mem (M.op β' y') G → M.mem (M.op β1 β') th → M.mem (M.op β2 β') th) ∧ (∀ b' y', M.mem (M.quad j ν b' y') P → M.mem (M.op β2 y') G → M.mem (M.op w0 b') Pr) ∧ M.mem (M.quad j β2 q1 n) P

theorem sat_rc11Fml (ρ : ℕ → V) : Sat M.mem M.isSet rc11Fml ρ ↔
    M.RC11 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 160) (ρ 162) (ρ 179) (ρ 271) (ρ 272) (ρ 180) (ρ 181) (ρ 381) (ρ 384) (ρ 385) := by
  simp [rc11Fml, RC11, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fRank, M.sat_fLeN, M.sat_fCan, M.sat_fSim, M.sat_fApp', M.sat_fApp3', M.sat_fApp4', M.sat_lwpFml, M.sat_lwnFml, Function.update_apply]

/-- Clause `12` of the rules for terms; the arity `c`, the number `v`, the atom `a`, the inputs `w` and the output `n` are the names `381`–`385`. -/
def rc12Fml : Fml :=
  .and (.eq 381 181) (Fml.ex 430 (Fml.ex 431 (Fml.ex 432 (Fml.ex 433 (Fml.ex 434 (.and (Fml.ex
    388 (.and (.eq 388 180) (fVal 271 384 388 430))) (.and (fApp4 20 25 431 160 430) (.and (fApp
    22 431 432) (.and (fApp4 20 25 272 433 434) (.and (fApp 179 432 434) (.and (.all 435 (.all
    436 (.all 437 (Fml.imp (fApp4 20 25 272 436 437) (Fml.imp (fApp 179 435 437) (Fml.imp (fApp
    22 431 435) (fApp 22 432 435))))))) (.and (.all 436 (.all 437 (Fml.imp (fApp4 20 25 272 436
    437) (Fml.imp (fApp 179 432 437) (fApp 162 433 436))))) (.eq 385 433)))))))))))))

def RC12 (P th io nat Nt j d q1 Pr G ρ ν t0 t1 c w n : V) : Prop :=
  c = t1 ∧ ∃ o1 β1 β2 w0 y, M.ValRaw P th io nat Nt j d ρ w t0 o1 ∧ M.mem (M.quad j β1 q1 o1) P ∧ M.mem (M.op β1 β2) th ∧ M.mem (M.quad j ν w0 y) P ∧ M.mem (M.op β2 y) G ∧ (∀ β' b' y', M.mem (M.quad j ν b' y') P → M.mem (M.op β' y') G → M.mem (M.op β1 β') th → M.mem (M.op β2 β') th) ∧ (∀ b' y', M.mem (M.quad j ν b' y') P → M.mem (M.op β2 y') G → M.mem (M.op w0 b') Pr) ∧ n = w0

theorem sat_rc12Fml (ρ : ℕ → V) : Sat M.mem M.isSet rc12Fml ρ ↔
    M.RC12 (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 160) (ρ 162) (ρ 179) (ρ 271) (ρ 272) (ρ 180) (ρ 181) (ρ 381) (ρ 384) (ρ 385) := by
  simp [rc12Fml, RC12, NameR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fRank, M.sat_fLeN, M.sat_fCan, M.sat_fSim, M.sat_fApp', M.sat_fApp3', M.sat_fApp4', M.sat_lwpFml, M.sat_lwnFml, Function.update_apply]

/-- The rules for terms: the tag `x` (name `380`) selects one of thirteen clauses; the tags are the names `180`–`192`. -/
def ruleFml : Fml :=
  .and (Fml.or (.eq 380 180) (Fml.or (.eq 380 181) (Fml.or (.eq 380 182) (Fml.or (.eq 380 183)
    (Fml.or (.eq 380 184) (Fml.or (.eq 380 185) (Fml.or (.eq 380 186) (Fml.or (.eq 380 187)
    (Fml.or (.eq 380 188) (Fml.or (.eq 380 189) (Fml.or (.eq 380 190) (Fml.or (.eq 380 191) (.eq
    380 192))))))))))))) (.and (Fml.imp (.eq 380 180) rc0Fml) (.and (Fml.imp (.eq 380 181) (.and
    (.eq 381 180) (.eq 385 273))) (.and (Fml.imp (.eq 380 182) (.and (.eq 381 180) (.eq 385
    26))) (.and (Fml.imp (.eq 380 183) rc3Fml) (.and (Fml.imp (.eq 380 184) rc4Fml) (.and
    (Fml.imp (.eq 380 185) rc5Fml) (.and (Fml.imp (.eq 380 186) rc6Fml) (.and (Fml.imp (.eq 380
    187) rc7Fml) (.and (Fml.imp (.eq 380 188) rc8Fml) (.and (Fml.imp (.eq 380 189) rc9Fml) (.and
    (Fml.imp (.eq 380 190) rc10Fml) (.and (Fml.imp (.eq 380 191) rc11Fml) (Fml.imp (.eq 380 192)
    rc12Fml)))))))))))))

/-- **The rules for terms.** The tag `x` selects the clause: an atom (a stage below `ν`,
through the map `g`), the generator `b`, the default name, and the six rules for hulls (rule 5
in four forms, rule 6 in two). The inputs are the values of the sequence `w` at the stage `ρ`
below the arity `c`; the output is `n`. -/
def RuleR (P th io nat Nt j d ad tp q1 F Pr G g b ρ ν t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 x c v a w n : V) : Prop :=
  (x = t0 ∨ x = t1 ∨ x = t2 ∨ x = t3 ∨ x = t4 ∨ x = t5 ∨ x = t6 ∨ x = t7 ∨ x = t8 ∨ x = t9 ∨ x = t10 ∨ x = t11 ∨ x = t12) ∧
  (x = t0 → M.RC0 P j q1 g t0 c a n) ∧
  (x = t1 → c = t0 ∧ n = b) ∧
  (x = t2 → c = t0 ∧ n = d) ∧
  (x = t3 → M.RC3 P th io nat Nt j d q1 ρ t0 t1 c w n) ∧
  (x = t4 → M.RC4 P th io nat Nt j d ad ρ t0 t1 c v w n) ∧
  (x = t5 → M.RC5 P th io nat Nt j d ad q1 ρ t1 c w n) ∧
  (x = t6 → M.RC6 P th io nat Nt j d tp F Pr ρ t0 t1 c w n) ∧
  (x = t7 → M.RC7 P th io nat Nt j d ad F Pr ρ t1 c v w n) ∧
  (x = t8 → M.RC8 P th io nat Nt j d ad F Pr ρ t1 c v w n) ∧
  (x = t9 → M.RC9 P th io nat Nt j d ad q1 F Pr ρ t1 c v w n) ∧
  (x = t10 → M.RC10 P th io nat Nt j d ad q1 F Pr ρ t1 c v w n) ∧
  (x = t11 → M.RC11 P th io nat Nt j d q1 Pr G ρ ν t0 t1 c w n) ∧
  (x = t12 → M.RC12 P th io nat Nt j d q1 Pr G ρ ν t0 t1 c w n)

theorem sat_ruleFml (ρ : ℕ → V) : Sat M.mem M.isSet ruleFml ρ ↔
    M.RuleR (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 21) (ρ 160) (ρ 163) (ρ 162) (ρ 179)
      (ρ 177) (ρ 273) (ρ 271) (ρ 272) (ρ 180) (ρ 181) (ρ 182) (ρ 183) (ρ 184) (ρ 185) (ρ 186) (ρ 187) (ρ 188) (ρ 189) (ρ 190) (ρ 191) (ρ 192)
      (ρ 380) (ρ 381) (ρ 382) (ρ 383) (ρ 384) (ρ 385) := by
  simp [ruleFml, RuleR, Sat, M.sat_imp, M.sat_or, M.sat_rc0Fml, M.sat_rc3Fml, M.sat_rc4Fml, M.sat_rc5Fml, M.sat_rc6Fml, M.sat_rc7Fml, M.sat_rc8Fml, M.sat_rc9Fml, M.sat_rc10Fml, M.sat_rc11Fml, M.sat_rc12Fml]

/-- One step of the evaluation of terms: the relation `E` is the name `178`, the term `t` the name `386`, the name `n` it evaluates to the name `387`. -/
def tstepFml : Fml :=
  Fml.ex 380 (Fml.ex 381 (Fml.ex 382 (Fml.ex 383 (Fml.ex 389 (Fml.ex 410 (Fml.ex 411 (Fml.ex 412
    (Fml.ex 413 (Fml.ex 414 (Fml.ex 415 (Fml.ex 384 (Fml.ex 385 (.and (fApp 174 380 410) (.and
    (fApp 174 381 411) (.and (fApp 174 382 412) (.and (fApp4 20 176 383 389 413) (.and (fApp4 20
    176 412 413 414) (.and (fApp4 20 176 411 414 415) (.and (fApp4 20 176 410 415 386) (.and
    (.all 416 (Fml.imp (.mem 416 27) (Fml.imp (Fml.ex 84 (.and (.mem 84 27) (.and (.neg (.eq 84
    180)) (fApp3 28 416 84 381)))) (Fml.ex 417 (Fml.ex 418 (.and (fApp3 175 389 416 417) (.and
    (fVal 271 384 416 418) (fApp 178 417 418)))))))) (.and ruleFml (.and (fApp 162 385 387)
    (.and (fApp 162 387 385) (Fml.ex 65 (.and (.eq 65 271) (fInN 387))))))))))))))))))))))))))

/-- **One step of the evaluation of terms.** The term `t` is the tuple of a tag `x`, an arity
`c`, a number `v`, an atom `a` and a sequence `s` of terms, in the rung `i`; the terms of `s`
below the arity evaluate, by `E`, to the values of a sequence `w`; and `n` is, up to the order
of names, the output of the rule for these inputs. -/
def StepR (P th io nat Nt j d ad tp q1 F Pr G g b ρ ν t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 io2 Nt2 i E t n : V) : Prop :=
  ∃ x c v a s f1 f2 f3 r1 r2 r3 w n1,
    M.mem (M.op x f1) io2 ∧ M.mem (M.op c f2) io2 ∧ M.mem (M.op v f3) io2 ∧
    M.mem (M.quad i a s r1) P ∧ M.mem (M.quad i f3 r1 r2) P ∧ M.mem (M.quad i f2 r2 r3) P ∧
    M.mem (M.quad i f1 r3 t) P ∧
    (∀ k, M.mem k nat → (∃ y, M.mem y nat ∧ ¬ y = t0 ∧ M.mem (M.trip k y c) ad) →
      ∃ a' e, M.mem (M.trip s k a') Nt2 ∧ M.ValRaw P th io nat Nt j d ρ w k e ∧ M.mem (M.op a' e) E) ∧
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 x c v a w n1 ∧
    M.mem (M.op n1 n) Pr ∧ M.mem (M.op n n1) Pr ∧ M.InNRaw P th io nat j ρ n

theorem sat_tstepFml (ρ : ℕ → V) : Sat M.mem M.isSet tstepFml ρ ↔
    M.StepR (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 21) (ρ 160) (ρ 163) (ρ 162) (ρ 179)
      (ρ 177) (ρ 273) (ρ 271) (ρ 272) (ρ 180) (ρ 181) (ρ 182) (ρ 183) (ρ 184) (ρ 185) (ρ 186) (ρ 187) (ρ 188) (ρ 189) (ρ 190) (ρ 191) (ρ 192)
      (ρ 174) (ρ 175) (ρ 176) (ρ 178) (ρ 386) (ρ 387) := by
  simp [tstepFml, StepR, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fInN, M.sat_fApp', M.sat_fApp3',
    M.sat_fApp4', M.sat_ruleFml, Function.update_apply]

theorem tstep_mono {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 io2 Nt2 i E E' t n : V}
    (hE : ∀ t n, M.mem (M.op t n) E → M.mem (M.op t n) E')
    (h : M.StepR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 io2 Nt2 i E t n) :
    M.StepR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 io2 Nt2 i E' t n := by
  obtain ⟨x, c, v, a, s, f1, f2, f3, r1, r2, r3, w, n1, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨x, c, v, a, s, f1, f2, f3, r1, r2, r3, w, n1, h1, h2, h3, h4, h5, h6, h7, fun k hk hlt => ?_, h9⟩
  obtain ⟨a', e, k1, k2, k3⟩ := h8 k hk hlt
  exact ⟨a', e, k1, k2, hE _ _ k3⟩

/-- **The data for the count of a hull.** Numerals `io2` and sequences `Nt2` in the rung `i`,
a one-to-one map `g` of the stages below `ν` into that rung, a stage `ρ` generated from `ν` and
`b`, and the least relation `Ev` closed under the steps of evaluation. -/
structure EvData (R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev : V) (m j i : M.Num) : Prop where
  hi : i ≤ m
  io2_dom : ∀ k a, M.mem (M.op k a) io2 → M.mem k M.nat ∧ M.mem (M.op i.1 a) R
  io2_tot : ∀ n : M.Num, ∃ a, M.mem (M.op n.1 a) io2
  io2_fun : ∀ k a a', M.mem (M.op k a) io2 → M.mem (M.op k a') io2 → a = a'
  io2_inj : ∀ k k' a, M.mem (M.op k a) io2 → M.mem (M.op k' a) io2 → k = k'
  nt2_zero : ∀ t a, M.mem (M.trip t M.zero a) Nt2 ↔ ∃ t', M.mem (M.quad i.1 a t' t) P
  nt2_succ : ∀ (n : M.Num) (t b : V), M.mem (M.trip t (n + 1).1 b) Nt2 ↔
    ∃ a t', M.mem (M.quad i.1 a t' t) P ∧ M.mem (M.trip t' n.1 b) Nt2
  g_tot : ∀ β, M.mem (M.op β ν) th → β ≠ ν → ∃ a, M.mem (M.op β a) g
  g_dom : ∀ β a, M.mem (M.op β a) g → M.mem (M.op β ν) th ∧ β ≠ ν ∧ M.mem (M.op i.1 a) R
  g_inj : ∀ β β' a, M.mem (M.op β a) g → M.mem (M.op β' a) g → β = β'
  hgen : M.Gen P Sg j ν ρ b
  hEv : ∀ q, M.mem q Ev ↔ ∃ t n, q = M.op t n ∧
    ∀ E, (∀ t' n', M.StepR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 io2 Nt2 i.1 E t' n' → M.mem (M.op t' n') E) → M.mem (M.op t n) E

section ev1

variable {R P th io Nt nle p F d tp qo Nu Pr Sg : V} {m j i : M.Num}
variable {q1 g b ρ ν io2 Nt2 Ev : V}

theorem exists_evSet (P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 : V) (j i : M.Num) :
    ∃ Ev, ∀ q, M.mem q Ev ↔ ∃ t n, q = M.op t n ∧
      ∀ E, (∀ t' n', M.StepR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 io2 Nt2 i.1 E t' n' → M.mem (M.op t' n') E) → M.mem (M.op t n) E := by
  obtain ⟨Ev, -, h0⟩ := M.comp (σW [(0, 4), (6, 5), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7), (162, 5),
      (163, 5), (174, 5), (175, 7), (177, 5), (178, 5), (179, 5)])
    (Fml.ex 386 (Fml.ex 387 (.and (fPr 0 386 387) (.all 178 (Fml.imp (.all 440 (.all 441 (Fml.imp (Fml.ex 386 (.and (.eq 386 440) (Fml.ex 387 (.and (.eq 387 441) tstepFml)))) (fApp 178 440 441)))) (fApp 178 386 387)))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 21 tp) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 160 q1) 162 Pr) 163 F) 174 io2) 175 Nt2) 176 i.1) 177 g) 179 (M.restr th Sg ρ)) 271 ρ) 272 ν) 273 b) 180 (0 : M.Num).1) 181 (1 : M.Num).1) 182 (2 : M.Num).1) 183 (3 : M.Num).1) 184 (4 : M.Num).1) 185 (5 : M.Num).1) 186 (6 : M.Num).1) 187 (7 : M.Num).1) 188 (8 : M.Num).1) 189 (9 : M.Num).1) 190 (10 : M.Num).1) 191 (11 : M.Num).1) 192 (12 : M.Num).1)
  refine ⟨Ev, fun q => ?_⟩
  rw [h0 q]
  simp [Sat, M.sat_imp, M.sat_ex, M.sat_fPr', M.sat_fApp', M.sat_tstepFml, Function.update_apply]

theorem ev_mem (ed : M.EvData R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev m j i) {t n : V} :
    M.mem (M.op t n) Ev ↔
      ∀ E, (∀ t' n', M.StepR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 io2 Nt2 i.1 E t' n' → M.mem (M.op t' n') E) → M.mem (M.op t n) E := by
  rw [ed.hEv]
  constructor
  · rintro ⟨t1, n1, hq, h⟩
    obtain ⟨e1, e2⟩ := M.op_inj hq
    rw [e1, e2]
    exact h
  · intro h
    exact ⟨t, n, rfl, h⟩

/-- The evaluation relation is closed under the steps. -/
theorem ev_step (ed : M.EvData R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev m j i) {t n : V} (h : M.StepR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 io2 Nt2 i.1 Ev t n) : M.mem (M.op t n) Ev := by
  rw [M.ev_mem ed]
  intro E hE
  exact hE t n (M.tstep_mono (fun t' n' h' => (M.ev_mem ed).mp h' E hE) h)

/-- Every evaluation arises by a step. -/
theorem ev_inv (ed : M.EvData R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev m j i) {t n : V} (h : M.mem (M.op t n) Ev) : M.StepR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 io2 Nt2 i.1 Ev t n := by
  obtain ⟨S, -, hS0⟩ := M.comp (σW [(0, 4), (6, 5), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7), (162, 5),
      (163, 5), (174, 5), (175, 7), (177, 5), (178, 5), (179, 5)])
    (Fml.ex 386 (Fml.ex 387 (.and (fPr 0 386 387) (.and (fApp 178 386 387) tstepFml)))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 21 tp) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 160 q1) 162 Pr) 163 F) 174 io2) 175 Nt2) 176 i.1) 177 g) 178 Ev) 179 (M.restr th Sg ρ)) 271 ρ) 272 ν) 273 b) 180 (0 : M.Num).1) 181 (1 : M.Num).1) 182 (2 : M.Num).1) 183 (3 : M.Num).1) 184 (4 : M.Num).1) 185 (5 : M.Num).1) 186 (6 : M.Num).1) 187 (7 : M.Num).1) 188 (8 : M.Num).1) 189 (9 : M.Num).1) 190 (10 : M.Num).1) 191 (11 : M.Num).1) 192 (12 : M.Num).1)
  have hS1 : ∀ q, M.mem q S ↔ ∃ t n, q = M.op t n ∧ M.mem (M.op t n) Ev ∧ M.StepR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 io2 Nt2 i.1 Ev t n := by
    intro q
    rw [hS0 q]
    simp [Sat, M.sat_ex, M.sat_fPr', M.sat_fApp', M.sat_tstepFml, Function.update_apply]
  have hS : ∀ t n, M.mem (M.op t n) S ↔ M.mem (M.op t n) Ev ∧ M.StepR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 io2 Nt2 i.1 Ev t n := by
    intro t n
    rw [hS1]
    constructor
    · rintro ⟨t1, n1, hq, h⟩
      obtain ⟨e1, e2⟩ := M.op_inj hq
      rw [e1, e2]
      exact h
    · intro h
      exact ⟨t, n, rfl, h⟩
  have hcl : ∀ t' n', M.StepR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 io2 Nt2 i.1 S t' n' → M.mem (M.op t' n') S := by
    intro t' n' hst
    have hst' : M.StepR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 io2 Nt2 i.1 Ev t' n' := M.tstep_mono (fun t n h => ((hS t n).mp h).1) hst
    exact (hS t' n').mpr ⟨M.ev_step ed hst', hst'⟩
  exact ((hS t n).mp ((M.ev_mem ed).mp h S hcl)).2

end ev1
/-! ## The rules for terms are functions, up to the order of names -/

section rulefun

variable {R P th io Nt nle p F d tp qo Nu Pr Sg : V} {m j i : M.Num}
variable {q1 g b ρ ν io2 Nt2 Ev : V}

theorem adG_succ {a : V} {c : M.Num} (h : M.mem (M.trip a (1 : M.Num).1 c.1) M.adG) :
    ∃ a' : M.Num, a'.1 = a ∧ c = a' + 1 := by
  obtain ⟨m, n, h1, h2, h3⟩ := (M.adG_spec _ _ _).mp h
  have hn : n = 1 := Subtype.ext h2
  have h4 : m + n = c := Subtype.ext h3
  exact ⟨m, h1, by rw [← h4, hn]⟩

theorem add_one_inj {a b : M.Num} (h : a + 1 = b + 1) : a = b :=
  le_antisymm (M.le_of_succ_le_succ (le_of_eq h)) (M.le_of_succ_le_succ (le_of_eq h.symm))

theorem tie_refl_inN (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j) {α x : V} (hx : M.InNRaw P th io M.nat j.1 α x) : M.mem (M.op x x) Pr := by
  obtain ⟨β, rx, lt, -⟩ := M.inN_rank hx
  exact M.pr_refl hd hPr rx (hd.hth.fld _ _ lt).1

theorem lwp_tie (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    {α t t' n n' : V} (c v : M.Num) (hα : M.mem (M.op α α) th)
    (h : M.LWp P th io M.nat Nt j.1 d M.adG F Pr α c.1 v.1 t n)
    (h' : M.LWp P th io M.nat Nt j.1 d M.adG F Pr α c.1 v.1 t' n')
    (hv : ∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d α t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e' ∧ M.SimRaw P j.1 tp F e e') :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨b1, b2, b3⟩ := h'
  exact ⟨a3 n' b1 ((M.tu_seq_sim hd c v hα b1 hv).mpr b2), b3 n a1 ((M.tu_seq_sim hd c v hα a1 hv).mp a2)⟩

theorem lwn_tie (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    {α t t' n n' : V} (c v : M.Num) (hα : M.mem (M.op α α) th)
    (h : M.LWn P th io M.nat Nt j.1 d M.adG F Pr α c.1 v.1 t n)
    (h' : M.LWn P th io M.nat Nt j.1 d M.adG F Pr α c.1 v.1 t' n')
    (hv : ∀ i : M.Num, i ≤ c → ∃ e e', M.ValRaw P th io M.nat Nt j.1 d α t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e' ∧ M.SimRaw P j.1 tp F e e') :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨b1, b2, b3⟩ := h'
  exact ⟨a3 n' b1 (fun h => b2 ((M.tu_seq_sim hd c v hα b1 hv).mp h)), b3 n a1 (fun h => a2 ((M.tu_seq_sim hd c v hα a1 hv).mpr h))⟩

theorem rc0_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hginj : ∀ β β' a, M.mem (M.op β a) g → M.mem (M.op β' a) g → β = β')
    (hgdom : ∀ β a, M.mem (M.op β a) g → M.mem (M.op β β) th) {c : M.Num} {a n n' : V}
    (h : M.RC0 P j.1 q1 g (0 : M.Num).1 c.1 a n) (h' : M.RC0 P j.1 q1 g (0 : M.Num).1 c.1 a n') :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨-, β, hg, ho⟩ := h
  obtain ⟨-, β', hg', ho'⟩ := h'
  have e := hginj β β' a hg hg'
  rw [← e] at ho'
  have en : n = n' := hd.hP.fn _ _ _ _ _ ho ho'
  rw [← en]
  have := M.pr_refl hd hPr (M.mark_rank hq ho) (hgdom β a hg)
  exact ⟨this, this⟩

theorem rc3_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hρ : M.mem (M.op ρ ρ) th) {c v : M.Num} {w w' n n' : V}
    (h : M.RC3 P th io M.nat Nt j.1 d q1 ρ (0 : M.Num).1 (1 : M.Num).1 c.1 w n)
    (h' : M.RC3 P th io M.nat Nt j.1 d q1 ρ (0 : M.Num).1 (1 : M.Num).1 c.1 w' n')
    (htie : ∀ k : M.Num, k + 1 ≤ c → ∀ e e', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e → M.ValRaw P th io M.nat Nt j.1 d ρ w' k.1 e' → (M.mem (M.op e e') Pr ∧ M.mem (M.op e' e) Pr)) :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨hc, n0, β, v0, r0, ho⟩ := h
  obtain ⟨-, n0', β', v0', r0', ho'⟩ := h'
  have hc1 : c = 1 := Subtype.ext hc
  obtain ⟨t1, t2⟩ := htie 0 (by rw [hc1, zero_add]) n0 n0' v0 v0'
  have eβ : β = β' := M.tie_rank hd hPr r0 r0' t1 t2
  rw [← eβ] at ho'
  have en : n = n' := hd.hP.fn _ _ _ _ _ ho ho'
  rw [← en]
  obtain ⟨β0, rb, hβ0⟩ := M.val_rank hd hρ (M.val_cases v0)
  have e0 : β0 = β := M.rank_unique hd rb r0
  rw [e0] at hβ0
  have := M.pr_refl hd hPr (M.mark_rank hq ho) hβ0
  exact ⟨this, this⟩

theorem rc4_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hρ : M.mem (M.op ρ ρ) th) {c v : M.Num} {w w' n n' : V}
    (h : M.RC4 P th io M.nat Nt j.1 d M.adG ρ (0 : M.Num).1 (1 : M.Num).1 c.1 v.1 w n)
    (h' : M.RC4 P th io M.nat Nt j.1 d M.adG ρ (0 : M.Num).1 (1 : M.Num).1 c.1 v.1 w' n')
    (htie : ∀ k : M.Num, k + 1 ≤ c → ∀ e e', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e → M.ValRaw P th io M.nat Nt j.1 d ρ w' k.1 e' → (M.mem (M.op e e') Pr ∧ M.mem (M.op e' e) Pr)) :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨hc, n0, β, c', u, v0, nm, hle, hv⟩ := h
  obtain ⟨-, n0', β', c'', u', v0', nm', hle', hv'⟩ := h'
  have hc1 : c = 1 := Subtype.ext hc
  obtain ⟨t1, t2⟩ := htie 0 (by rw [hc1, zero_add]) n0 n0' v0 v0'
  have eβ : β = β' := M.tie_rank hd hPr (M.nameR_rank nm) (M.nameR_rank nm') t1 t2
  rw [← eβ] at nm' hv'
  obtain ⟨β0, rb, hβ0⟩ := M.val_rank hd hρ (M.val_cases v0)
  have e0 : β0 = β := M.rank_unique hd rb (M.nameR_rank nm)
  rw [e0] at hβ0
  have hc'N : M.mem c' M.nat := by
    obtain ⟨f, q, -, -, k, -⟩ := nm
    exact k
  have hc''N : M.mem c'' M.nat := by
    obtain ⟨f, q, -, -, k, -⟩ := nm'
    exact k
  have nmO : M.NameOf P io j n0 β ⟨c', hc'N⟩ u := (M.nameR_iff ⟨c', hc'N⟩).mp nm
  have nmO' : M.NameOf P io j n0' β ⟨c'', hc''N⟩ u' := (M.nameR_iff ⟨c'', hc''N⟩).mp nm'
  obtain ⟨ek, hvals⟩ := M.tie_shape hd hPr nmO nmO' hβ0 t1 t2
  have hvle : v ≤ ⟨c', hc'N⟩ := (M.leRaw_iff M.adG_spec v ⟨c', hc'N⟩).mp hle
  obtain ⟨g', g0, w1, w2, l1, l2⟩ := hvals v hvle
  have e1 : g' = n' := M.val_unique hd w1 hv'
  have e2 : g0 = n := M.val_unique hd w2 hv
  rw [e1, e2] at l1 l2
  exact ⟨(M.leV_iff hd hPr hβ0 (M.val_cases hv)).mp l2, (M.leV_iff hd hPr hβ0 (M.val_cases hv')).mp l1⟩

theorem rc5_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hρ : M.mem (M.op ρ ρ) th) {c v : M.Num} {w w' n n' : V}
    (h : M.RC5 P th io M.nat Nt j.1 d M.adG q1 ρ (1 : M.Num).1 c.1 w n)
    (h' : M.RC5 P th io M.nat Nt j.1 d M.adG q1 ρ (1 : M.Num).1 c.1 w' n')
    (htie : ∀ k : M.Num, k + 1 ≤ c → ∀ e e', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e → M.ValRaw P th io M.nat Nt j.1 d ρ w' k.1 e' → (M.mem (M.op e e') Pr ∧ M.mem (M.op e' e) Pr)) :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨c', k1, o, β, u, a1, a2, vo, ho, lt, ne, nm, hvals⟩ := h
  obtain ⟨c'', k1', o', β', u', b1, b2, vo', ho', lt', ne', nm', hvals'⟩ := h'
  obtain ⟨K, hK, hcK⟩ := M.adG_succ a2
  obtain ⟨K', hK', hcK'⟩ := M.adG_succ b2
  have eK : K = K' := M.add_one_inj (hcK.symm.trans hcK')
  rw [← hK] at a1 vo
  rw [← hK', ← eK] at b1 vo'
  obtain ⟨C, hC, hKC⟩ := M.adG_succ a1
  obtain ⟨C', hC', hKC'⟩ := M.adG_succ b1
  have eC : C = C' := M.add_one_inj (hKC.symm.trans hKC')
  rw [← hC] at nm hvals
  rw [← hC', ← eC] at nm' hvals'
  obtain ⟨t1, t2⟩ := htie K (by rw [hcK]) o o' vo vo'
  have eβ : β = β' := M.tie_rank hd hPr (M.mark_rank hq ho) (M.mark_rank hq ho') t1 t2
  rw [← eβ] at nm' hvals'
  have hβ := (hd.hth.fld _ _ lt).1
  refine M.tie_of_vals hd hPr ((M.nameR_iff C).mp nm) ((M.nameR_iff C).mp nm') hβ (fun i hi => ?_)
  obtain ⟨e, he⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) β u i.1
  obtain ⟨e', he'⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) β u' i.1
  have hiC := (M.leRaw_iff M.adG_spec i C).mpr hi
  obtain ⟨s1, s2⟩ := htie i (by
    rw [hcK, hKC]
    exact le_trans (add_le_add_left hi 1) (M.le_add_one _)) e e'
    (hvals i.1 e i.2 hiC he) (hvals' i.1 e' i.2 hiC he')
  exact ⟨e, e', he, he', Or.inr s1, Or.inr s2⟩

theorem rc6_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hρ : M.mem (M.op ρ ρ) th) {c v : M.Num} {w w' n n' : V}
    (h : M.RC6 P th io M.nat Nt j.1 d tp F Pr ρ (0 : M.Num).1 (1 : M.Num).1 c.1 w n)
    (h' : M.RC6 P th io M.nat Nt j.1 d tp F Pr ρ (0 : M.Num).1 (1 : M.Num).1 c.1 w' n')
    (htie : ∀ k : M.Num, k + 1 ≤ c → ∀ e e', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e → M.ValRaw P th io M.nat Nt j.1 d ρ w' k.1 e' → (M.mem (M.op e e') Pr ∧ M.mem (M.op e' e) Pr)) :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨hc, n0, v0, ca, hs⟩ := h
  obtain ⟨-, n0', v0', ca', hs'⟩ := h'
  have hc1 : c = 1 := Subtype.ext hc
  obtain ⟨t1, t2⟩ := htie 0 (by rw [hc1, zero_add]) n0 n0' v0 v0'
  have s0 := M.tie_sim hd hPr t1 t2
  exact M.can_tie hd ca ca' (M.sim_trans hd (M.sim_symm hd hs) (M.sim_trans hd s0 hs'))

theorem rc7_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hρ : M.mem (M.op ρ ρ) th) {c v : M.Num} {w w' n n' : V}
    (h : M.RC7 P th io M.nat Nt j.1 d M.adG F Pr ρ (1 : M.Num).1 c.1 v.1 w n)
    (h' : M.RC7 P th io M.nat Nt j.1 d M.adG F Pr ρ (1 : M.Num).1 c.1 v.1 w' n')
    (htie : ∀ k : M.Num, k + 1 ≤ c → ∀ e e', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e → M.ValRaw P th io M.nat Nt j.1 d ρ w' k.1 e' → (M.mem (M.op e e') Pr ∧ M.mem (M.op e' e) Pr)) :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨cf, hcf, a1, lw⟩ := h
  obtain ⟨cf', hcf', b1, lw'⟩ := h'
  obtain ⟨C, hC, hcC⟩ := M.adG_succ a1
  obtain ⟨C', hC', hcC'⟩ := M.adG_succ b1
  have eC : C = C' := M.add_one_inj (hcC.symm.trans hcC')
  rw [← hC] at lw
  rw [← hC', ← eC] at lw'
  refine M.lwp_tie hd hPr C v hρ lw lw' (fun i hi => ?_)
  obtain ⟨e, he⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) ρ w i.1
  obtain ⟨e', he'⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) ρ w' i.1
  obtain ⟨s1, s2⟩ := htie i (by rw [hcC]; exact add_le_add_left hi 1) e e' he he'
  exact ⟨e, e', he, he', M.tie_sim hd hPr s1 s2⟩

theorem rc8_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hρ : M.mem (M.op ρ ρ) th) {c v : M.Num} {w w' n n' : V}
    (h : M.RC8 P th io M.nat Nt j.1 d M.adG F Pr ρ (1 : M.Num).1 c.1 v.1 w n)
    (h' : M.RC8 P th io M.nat Nt j.1 d M.adG F Pr ρ (1 : M.Num).1 c.1 v.1 w' n')
    (htie : ∀ k : M.Num, k + 1 ≤ c → ∀ e e', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e → M.ValRaw P th io M.nat Nt j.1 d ρ w' k.1 e' → (M.mem (M.op e e') Pr ∧ M.mem (M.op e' e) Pr)) :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨cf, hcf, a1, lw⟩ := h
  obtain ⟨cf', hcf', b1, lw'⟩ := h'
  obtain ⟨C, hC, hcC⟩ := M.adG_succ a1
  obtain ⟨C', hC', hcC'⟩ := M.adG_succ b1
  have eC : C = C' := M.add_one_inj (hcC.symm.trans hcC')
  rw [← hC] at lw
  rw [← hC', ← eC] at lw'
  refine M.lwn_tie hd hPr C v hρ lw lw' (fun i hi => ?_)
  obtain ⟨e, he⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) ρ w i.1
  obtain ⟨e', he'⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) ρ w' i.1
  obtain ⟨s1, s2⟩ := htie i (by rw [hcC]; exact add_le_add_left hi 1) e e' he he'
  exact ⟨e, e', he, he', M.tie_sim hd hPr s1 s2⟩

theorem rc9_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hρ : M.mem (M.op ρ ρ) th) {c v : M.Num} {w w' n n' : V}
    (h : M.RC9 P th io M.nat Nt j.1 d M.adG q1 F Pr ρ (1 : M.Num).1 c.1 v.1 w n)
    (h' : M.RC9 P th io M.nat Nt j.1 d M.adG q1 F Pr ρ (1 : M.Num).1 c.1 v.1 w' n')
    (htie : ∀ k : M.Num, k + 1 ≤ c → ∀ e e', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e → M.ValRaw P th io M.nat Nt j.1 d ρ w' k.1 e' → (M.mem (M.op e e') Pr ∧ M.mem (M.op e' e) Pr)) :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨cf, k1, o, β, t, hcf, a1, a2, vo, ho, lt, ne, hvals, lw⟩ := h
  obtain ⟨cf', k1', o', β', t', hcf', b1, b2, vo', ho', lt', ne', hvals', lw'⟩ := h'
  obtain ⟨K, hK, hcK⟩ := M.adG_succ a2
  obtain ⟨K', hK', hcK'⟩ := M.adG_succ b2
  have eK : K = K' := M.add_one_inj (hcK.symm.trans hcK')
  rw [← hK] at a1 vo
  rw [← hK', ← eK] at b1 vo'
  obtain ⟨C, hC, hKC⟩ := M.adG_succ a1
  obtain ⟨C', hC', hKC'⟩ := M.adG_succ b1
  have eC : C = C' := M.add_one_inj (hKC.symm.trans hKC')
  rw [← hC] at hvals lw
  rw [← hC', ← eC] at hvals' lw'
  obtain ⟨t1, t2⟩ := htie K (by rw [hcK]) o o' vo vo'
  have eβ : β = β' := M.tie_rank hd hPr (M.mark_rank hq ho) (M.mark_rank hq ho') t1 t2
  rw [← eβ] at hvals' lw'
  have hβ := (hd.hth.fld _ _ lt).1
  refine M.lwp_tie hd hPr C v hβ lw lw' (fun i hi => ?_)
  obtain ⟨e, he⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) β t i.1
  obtain ⟨e', he'⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) β t' i.1
  have hiC := (M.leRaw_iff M.adG_spec i C).mpr hi
  obtain ⟨s1, s2⟩ := htie i (by
    rw [hcK, hKC]
    exact le_trans (add_le_add_left hi 1) (M.le_add_one _)) e e'
    (hvals i.1 e i.2 hiC he) (hvals' i.1 e' i.2 hiC he')
  exact ⟨e, e', he, he', M.tie_sim hd hPr s1 s2⟩

theorem rc10_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hρ : M.mem (M.op ρ ρ) th) {c v : M.Num} {w w' n n' : V}
    (h : M.RC10 P th io M.nat Nt j.1 d M.adG q1 F Pr ρ (1 : M.Num).1 c.1 v.1 w n)
    (h' : M.RC10 P th io M.nat Nt j.1 d M.adG q1 F Pr ρ (1 : M.Num).1 c.1 v.1 w' n')
    (htie : ∀ k : M.Num, k + 1 ≤ c → ∀ e e', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e → M.ValRaw P th io M.nat Nt j.1 d ρ w' k.1 e' → (M.mem (M.op e e') Pr ∧ M.mem (M.op e' e) Pr)) :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨cf, k1, o, β, t, hcf, a1, a2, vo, ho, lt, ne, hvals, lw⟩ := h
  obtain ⟨cf', k1', o', β', t', hcf', b1, b2, vo', ho', lt', ne', hvals', lw'⟩ := h'
  obtain ⟨K, hK, hcK⟩ := M.adG_succ a2
  obtain ⟨K', hK', hcK'⟩ := M.adG_succ b2
  have eK : K = K' := M.add_one_inj (hcK.symm.trans hcK')
  rw [← hK] at a1 vo
  rw [← hK', ← eK] at b1 vo'
  obtain ⟨C, hC, hKC⟩ := M.adG_succ a1
  obtain ⟨C', hC', hKC'⟩ := M.adG_succ b1
  have eC : C = C' := M.add_one_inj (hKC.symm.trans hKC')
  rw [← hC] at hvals lw
  rw [← hC', ← eC] at hvals' lw'
  obtain ⟨t1, t2⟩ := htie K (by rw [hcK]) o o' vo vo'
  have eβ : β = β' := M.tie_rank hd hPr (M.mark_rank hq ho) (M.mark_rank hq ho') t1 t2
  rw [← eβ] at hvals' lw'
  have hβ := (hd.hth.fld _ _ lt).1
  refine M.lwn_tie hd hPr C v hβ lw lw' (fun i hi => ?_)
  obtain ⟨e, he⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) β t i.1
  obtain ⟨e', he'⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) β t' i.1
  have hiC := (M.leRaw_iff M.adG_spec i C).mpr hi
  obtain ⟨s1, s2⟩ := htie i (by
    rw [hcK, hKC]
    exact le_trans (add_le_add_left hi 1) (M.le_add_one _)) e e'
    (hvals i.1 e i.2 hiC he) (hvals' i.1 e' i.2 hiC he')
  exact ⟨e, e', he, he', M.tie_sim hd hPr s1 s2⟩

theorem rc11_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hρ : M.mem (M.op ρ ρ) th) {c v : M.Num} {w w' n n' : V}
    (h : M.RC11 P th io M.nat Nt j.1 d q1 Pr (M.restr th Sg ρ) ρ ν (0 : M.Num).1 (1 : M.Num).1 c.1 w n)
    (h' : M.RC11 P th io M.nat Nt j.1 d q1 Pr (M.restr th Sg ρ) ρ ν (0 : M.Num).1 (1 : M.Num).1 c.1 w' n')
    (htie : ∀ k : M.Num, k + 1 ≤ c → ∀ e e', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e → M.ValRaw P th io M.nat Nt j.1 d ρ w' k.1 e' → (M.mem (M.op e e') Pr ∧ M.mem (M.op e' e) Pr)) :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨hc, o1, β1, β2, w0, y, v0, ho1, l12, hy, hG, hleast, hprl, hn⟩ := h
  obtain ⟨-, o1', β1', β2', w0', y', v0', ho1', l12', hy', hG', hleast', hprl', hn'⟩ := h'
  have hc1 : c = 1 := Subtype.ext hc
  obtain ⟨t1, t2⟩ := htie 0 (by rw [hc1, zero_add]) o1 o1' v0 v0'
  have e1 : β1 = β1' := M.tie_rank hd hPr (M.mark_rank hq ho1) (M.mark_rank hq ho1') t1 t2
  rw [← e1] at l12' hleast'
  have e2 : β2 = β2' := hd.hth.antisymm _ _ (hleast β2' w0' y' hy' hG' l12') (hleast' β2 w0 y hy hG l12)
  rw [← e2] at hn'
  have en : n = n' := hd.hP.fn _ _ _ _ _ hn hn'
  rw [← en]
  have := M.pr_refl hd hPr (M.mark_rank hq hn) (hd.hth.fld _ _ l12).2
  exact ⟨this, this⟩

theorem rc12_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hρ : M.mem (M.op ρ ρ) th) {c v : M.Num} {w w' n n' : V}
    (h : M.RC12 P th io M.nat Nt j.1 d q1 Pr (M.restr th Sg ρ) ρ ν (0 : M.Num).1 (1 : M.Num).1 c.1 w n)
    (h' : M.RC12 P th io M.nat Nt j.1 d q1 Pr (M.restr th Sg ρ) ρ ν (0 : M.Num).1 (1 : M.Num).1 c.1 w' n')
    (htie : ∀ k : M.Num, k + 1 ≤ c → ∀ e e', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e → M.ValRaw P th io M.nat Nt j.1 d ρ w' k.1 e' → (M.mem (M.op e e') Pr ∧ M.mem (M.op e' e) Pr)) :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨hc, o1, β1, β2, w0, y, v0, ho1, l12, hy, hG, hleast, hprl, hn⟩ := h
  obtain ⟨-, o1', β1', β2', w0', y', v0', ho1', l12', hy', hG', hleast', hprl', hn'⟩ := h'
  have hc1 : c = 1 := Subtype.ext hc
  obtain ⟨t1, t2⟩ := htie 0 (by rw [hc1, zero_add]) o1 o1' v0 v0'
  have e1 : β1 = β1' := M.tie_rank hd hPr (M.mark_rank hq ho1) (M.mark_rank hq ho1') t1 t2
  rw [← e1] at l12' hleast'
  have e2 : β2 = β2' := hd.hth.antisymm _ _ (hleast β2' w0' y' hy' hG' l12') (hleast' β2 w0 y hy hG l12)
  rw [← e2] at hG' hprl'
  rw [hn, hn']
  exact ⟨hprl w0' y' hy' hG', hprl' w0 y hy hG⟩

/-- **The rules are functions up to the order of names.** If the inputs of two applications of
a rule, with the same tag, arity, number and atom, are pairwise each at most the other in the
order of names, then so are the outputs. -/
theorem rule_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    (ed : M.EvData R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev m j i) {x c v : M.Num} {a w w' n n' : V}
    (h : M.RuleR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 x.1 c.1 v.1 a w n)
    (h' : M.RuleR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 x.1 c.1 v.1 a w' n')
    (htie : ∀ k : M.Num, k + 1 ≤ c → ∀ e e', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e → M.ValRaw P th io M.nat Nt j.1 d ρ w' k.1 e' → (M.mem (M.op e e') Pr ∧ M.mem (M.op e' e) Pr)) :
    (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨hx, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  obtain ⟨-, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩ := h'
  obtain ⟨hνρ, hνne, hbρ⟩ := M.gen_lt hd hSg ed.hgen
  have hρ := (hd.hth.fld _ _ hνρ).2
  rcases hx with e | e | e | e | e | e | e | e | e | e | e | e | e
  · exact M.rc0_fun hd hPr hq ed.g_inj (fun β a hg => (hd.hth.fld _ _ (ed.g_dom β a hg).1).1) (h0 e) (k0 e)
  · rw [(h1 e).2, (k1 e).2]
    have := M.tie_refl_inN hd hPr hbρ
    exact ⟨this, this⟩
  · rw [(h2 e).2, (k2 e).2]
    have := M.tie_refl_inN hd hPr (M.d_inN hd hνρ hνne)
    exact ⟨this, this⟩
  · exact M.rc3_fun hd hPr hq hρ (v := v) (h3 e) (k3 e) htie
  · exact M.rc4_fun hd hPr hq hρ (v := v) (h4 e) (k4 e) htie
  · exact M.rc5_fun hd hPr hq hρ (v := v) (h5 e) (k5 e) htie
  · exact M.rc6_fun hd hPr hq hρ (v := v) (h6 e) (k6 e) htie
  · exact M.rc7_fun hd hPr hq hρ (v := v) (h7 e) (k7 e) htie
  · exact M.rc8_fun hd hPr hq hρ (v := v) (h8 e) (k8 e) htie
  · exact M.rc9_fun hd hPr hq hρ (v := v) (h9 e) (k9 e) htie
  · exact M.rc10_fun hd hPr hq hρ (v := v) (h10 e) (k10 e) htie
  · exact M.rc11_fun hd hPr hq hρ (v := v) (h11 e) (k11 e) htie
  · exact M.rc12_fun hd hPr hq hρ (v := v) (h12 e) (k12 e) htie

end rulefun
/-! ## Evaluation of terms is a function up to the order of names -/

section ev2

variable {R P th io Nt nle p F d tp qo Nu Pr Sg : V} {m j i : M.Num}
variable {q1 g b ρ ν io2 Nt2 Ev : V}

/-- Terms are members of the rung `i`. -/
theorem ev_rung (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (ed : M.EvData R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev m j i) {t n : V}
    (h : M.mem (M.op t n) Ev) : M.mem (M.op i.1 t) R := by
  obtain ⟨x, c, v, a, s, f1, f2, f3, r1, r2, r3, w, n1, i1, i2, i3, p1, p2, p3, p4, -⟩ := M.ev_inv ed h
  exact (hd.hP.dom _ _ _ _ p4).2.2.2

/-- Terms evaluate to names of rank below `ρ`. -/
theorem ev_inN (ed : M.EvData R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev m j i) {t n : V}
    (h : M.mem (M.op t n) Ev) : M.InNRaw P th io M.nat j.1 ρ n := by
  obtain ⟨x, c, v, a, s, f1, f2, f3, r1, r2, r3, w, n1, i1, i2, i3, p1, p2, p3, p4, hin, hrule, pr1, pr2, hn⟩ := M.ev_inv ed h
  exact hn

/-- **Evaluation is a function up to the order of names.** -/
theorem ev_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    (ed : M.EvData R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev m j i) {t n n' : V}
    (h : M.mem (M.op t n) Ev) (h' : M.mem (M.op t n') Ev) : (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
  obtain ⟨Q, -, hQ0⟩ := M.comp (σW [(0, 4), (162, 5), (178, 5)]) (Fml.ex 386 (Fml.ex 387 (.and (fPr 0 386 387) (.and (fApp 178 386 387) (.all 441 (Fml.imp (fApp 178 386 441) (.and (fApp 162 387 441) (fApp 162 441 387)))))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 162 Pr) 178 Ev)
  have hQ1 : ∀ q, M.mem q Q ↔ ∃ t n, q = M.op t n ∧ M.mem (M.op t n) Ev ∧
      ∀ n', M.mem (M.op t n') Ev → (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
    intro q
    rw [hQ0 q]
    simp [Sat, M.sat_imp, M.sat_ex, M.sat_fPr', M.sat_fApp', Function.update_apply]
  have hQ : ∀ t n, M.mem (M.op t n) Q ↔ M.mem (M.op t n) Ev ∧
      ∀ n', M.mem (M.op t n') Ev → (M.mem (M.op n n') Pr ∧ M.mem (M.op n' n) Pr) := by
    intro t n
    rw [hQ1]
    constructor
    · rintro ⟨t1, n1, hq, h⟩
      obtain ⟨e1, e2⟩ := M.op_inj hq
      rw [e1, e2]
      exact h
    · intro h
      exact ⟨t, n, rfl, h⟩
  have hcl : ∀ t n, M.StepR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 io2 Nt2 i.1 Q t n → M.mem (M.op t n) Q := by
    intro t n hst
    have hstEv : M.StepR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 io2 Nt2 i.1 Ev t n := M.tstep_mono (fun t n h => ((hQ t n).mp h).1) hst
    refine (hQ t n).mpr ⟨M.ev_step ed hstEv, fun n' hn' => ?_⟩
    have hst' := M.ev_inv ed hn'
    obtain ⟨x, c, v, a, s, f1, f2, f3, r1, r2, r3, w, n1, i1, i2, i3, p1, p2, p3, p4, hin, hrule, pr1, pr2, hnρ⟩ := hst
    obtain ⟨x', c', v', a', s', f1', f2', f3', r1', r2', r3', w', n1', i1', i2', i3', p1', p2', p3', p4', hin', hrule', pr1', pr2', hnρ'⟩ := hst'
    obtain ⟨ef1, er3⟩ := hd.hP.inj _ _ _ _ _ _ p4 p4'
    rw [← er3] at p3'
    obtain ⟨ef2, er2⟩ := hd.hP.inj _ _ _ _ _ _ p3 p3'
    rw [← er2] at p2'
    obtain ⟨ef3, er1⟩ := hd.hP.inj _ _ _ _ _ _ p2 p2'
    rw [← er1] at p1'
    obtain ⟨ea, es⟩ := hd.hP.inj _ _ _ _ _ _ p1 p1'
    rw [← ef1] at i1'
    rw [← ef2] at i2'
    rw [← ef3] at i3'
    have ex : x = x' := ed.io2_inj _ _ _ i1 i1'
    have ec : c = c' := ed.io2_inj _ _ _ i2 i2'
    have ev : v = v' := ed.io2_inj _ _ _ i3 i3'
    have hxN := (ed.io2_dom _ _ i1).1
    have hcN := (ed.io2_dom _ _ i2).1
    have hvN := (ed.io2_dom _ _ i3).1
    rw [← ex, ← ec, ← ev, ← ea] at hrule'
    rw [← ec, ← es] at hin'
    have htie : ∀ k : M.Num, k + 1 ≤ (⟨c, hcN⟩ : M.Num) → ∀ e e', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e →
        M.ValRaw P th io M.nat Nt j.1 d ρ w' k.1 e' → (M.mem (M.op e e') Pr ∧ M.mem (M.op e' e) Pr) := by
      intro k hk e e' he he'
      have hlt := (M.ltRaw_num k ⟨c, hcN⟩).mpr hk
      obtain ⟨a1, e1, n1a, v1, q1m⟩ := hin k.1 k.2 hlt
      obtain ⟨a2, e2, n2a, v2, q2m⟩ := hin' k.1 k.2 hlt
      have ea12 : a1 = a2 := M.nth_fun hd.hP ed.nt2_zero ed.nt2_succ k s a1 a2 n1a n2a
      rw [← ea12] at q2m
      rw [M.val_unique hd he v1, M.val_unique hd he' v2]
      exact ((hQ a1 e1).mp q1m).2 e2 q2m
    have key := M.rule_fun hd hPr hq hSg ed (x := ⟨x, hxN⟩) (c := ⟨c, hcN⟩) (v := ⟨v, hvN⟩) hrule hrule' htie
    exact ⟨M.pr_trans hd hPr (M.pr_trans hd hPr pr2 key.1) pr1',
      M.pr_trans hd hPr (M.pr_trans hd hPr pr2' key.2) pr1⟩
  exact ((hQ t n).mp ((M.ev_mem ed).mp h Q hcl)).2 n' h'

theorem rule_mk0 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : M.RC0 P j q1 g (0 : M.Num).1 c a n) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (0 : M.Num).1 c v a w n :=
  ⟨Or.inl rfl, fun _ => h, fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num)⟩

theorem rule_mk1 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : c = (0 : M.Num).1 ∧ n = b) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (1 : M.Num).1 c v a w n :=
  ⟨Or.inr (Or.inl rfl), fun e => absurd (Subtype.ext e) (by norm_num), fun _ => h, fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num)⟩

theorem rule_mk2 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : c = (0 : M.Num).1 ∧ n = d) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (2 : M.Num).1 c v a w n :=
  ⟨Or.inr (Or.inr (Or.inl rfl)), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun _ => h, fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num)⟩

theorem rule_mk3 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : M.RC3 P th io nat Nt j d q1 ρ (0 : M.Num).1 (1 : M.Num).1 c w n) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (3 : M.Num).1 c v a w n :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun _ => h, fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num)⟩

theorem rule_mk4 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : M.RC4 P th io nat Nt j d ad ρ (0 : M.Num).1 (1 : M.Num).1 c v w n) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (4 : M.Num).1 c v a w n :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun _ => h, fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num)⟩

theorem rule_mk5 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : M.RC5 P th io nat Nt j d ad q1 ρ (1 : M.Num).1 c w n) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (5 : M.Num).1 c v a w n :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun _ => h, fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num)⟩

theorem rule_mk6 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : M.RC6 P th io nat Nt j d tp F Pr ρ (0 : M.Num).1 (1 : M.Num).1 c w n) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (6 : M.Num).1 c v a w n :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun _ => h, fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num)⟩

theorem rule_mk7 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : M.RC7 P th io nat Nt j d ad F Pr ρ (1 : M.Num).1 c v w n) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (7 : M.Num).1 c v a w n :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun _ => h, fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num)⟩

theorem rule_mk8 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : M.RC8 P th io nat Nt j d ad F Pr ρ (1 : M.Num).1 c v w n) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (8 : M.Num).1 c v a w n :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun _ => h, fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num)⟩

theorem rule_mk9 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : M.RC9 P th io nat Nt j d ad q1 F Pr ρ (1 : M.Num).1 c v w n) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (9 : M.Num).1 c v a w n :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun _ => h, fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num)⟩

theorem rule_mk10 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : M.RC10 P th io nat Nt j d ad q1 F Pr ρ (1 : M.Num).1 c v w n) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (10 : M.Num).1 c v a w n :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun _ => h, fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num)⟩

theorem rule_mk11 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : M.RC11 P th io nat Nt j d q1 Pr G ρ ν (0 : M.Num).1 (1 : M.Num).1 c w n) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (11 : M.Num).1 c v a w n :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun _ => h, fun e => absurd (Subtype.ext e) (by norm_num)⟩

theorem rule_mk12 {P th io nat Nt j d ad tp q1 F Pr G g b ρ ν c v a w n : V}
    (h : M.RC12 P th io nat Nt j d q1 Pr G ρ ν (0 : M.Num).1 (1 : M.Num).1 c w n) :
    M.RuleR P th io nat Nt j d ad tp q1 F Pr G g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 (12 : M.Num).1 c v a w n :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))))))), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun e => absurd (Subtype.ext e) (by norm_num), fun _ => h⟩

/-- **Forming a term.** If the inputs of a rule are values of terms, so is its output. -/
theorem ev_intro (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (ed : M.EvData R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev m j i)
    (x c v : M.Num) {a w n1 n : V} (ha : M.mem (M.op i.1 a) R)
    (hin : ∀ k : M.Num, k + 1 ≤ c → ∃ e a', M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e ∧ M.mem (M.op a' e) Ev)
    (hrule : M.RuleR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 x.1 c.1 v.1 a w n1)
    (p1 : M.mem (M.op n1 n) Pr) (p2 : M.mem (M.op n n1) Pr) (hn : M.InNRaw P th io M.nat j.1 ρ n) :
    ∃ t, M.mem (M.op t n) Ev := by
  obtain ⟨g2, -, hg0⟩ := M.comp (σW [(0, 4), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (178, 5)])
    (Fml.ex 326 (Fml.ex 327 (Fml.ex 328 (.and (fPr 0 326 327) (.and (fVal 271 384 326 328) (fApp 178 327 328)))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 178 Ev) 271 ρ) 384 w)
  have hg1 : ∀ q, M.mem q g2 ↔ ∃ k a' e, q = M.op k a' ∧ M.ValRaw P th io M.nat Nt j.1 d ρ w k e ∧ M.mem (M.op a' e) Ev := by
    intro q
    rw [hg0 q]
    simp [Sat, M.sat_ex, M.sat_fPr', M.sat_fVal, M.sat_fApp', Function.update_apply]
  have hg : ∀ k a', M.mem (M.op k a') g2 ↔ ∃ e, M.ValRaw P th io M.nat Nt j.1 d ρ w k e ∧ M.mem (M.op a' e) Ev := by
    intro k a'
    rw [hg1]
    constructor
    · rintro ⟨k1, a1, e, hq, h1, h2⟩
      obtain ⟨e1, e2⟩ := M.op_inj hq
      rw [e1, e2]
      exact ⟨e, h1, h2⟩
    · rintro ⟨e, h1, h2⟩
      exact ⟨k, a', e, rfl, h1, h2⟩
  obtain ⟨s, hsR, hs⟩ := M.seq_code hd.hP ed.hi ⟨a, ha⟩ ed.nt2_zero ed.nt2_succ c g2 (fun k hk => by
    obtain ⟨e, a', h1, h2⟩ := hin k hk
    exact ⟨a', M.ev_rung hd ed h2, (hg k.1 a').mpr ⟨e, h1, h2⟩⟩)
  obtain ⟨f1, i1⟩ := ed.io2_tot x
  obtain ⟨f2, i2⟩ := ed.io2_tot c
  obtain ⟨f3, i3⟩ := ed.io2_tot v
  obtain ⟨r1, p1'⟩ := hd.hP.tot i ed.hi a s ha hsR
  obtain ⟨r2, p2'⟩ := hd.hP.tot i ed.hi f3 r1 (ed.io2_dom _ _ i3).2 (hd.hP.dom _ _ _ _ p1').2.2.2
  obtain ⟨r3, p3'⟩ := hd.hP.tot i ed.hi f2 r2 (ed.io2_dom _ _ i2).2 (hd.hP.dom _ _ _ _ p2').2.2.2
  obtain ⟨t, p4'⟩ := hd.hP.tot i ed.hi f1 r3 (ed.io2_dom _ _ i1).2 (hd.hP.dom _ _ _ _ p3').2.2.2
  refine ⟨t, M.ev_step ed ⟨x.1, c.1, v.1, a, s, f1, f2, f3, r1, r2, r3, w, n1, i1, i2, i3, p1', p2', p3',
    p4', fun k hk hlt => ?_, hrule, p1, p2, hn⟩⟩
  have hk' : (⟨k, hk⟩ : M.Num) + 1 ≤ c := (M.ltRaw_num ⟨k, hk⟩ c).mp hlt
  obtain ⟨a', hga, hnt⟩ := hs ⟨k, hk⟩ hk'
  obtain ⟨e, h1, h2⟩ := (hg k a').mp hga
  exact ⟨a', e, hnt, h1, h2⟩

/-- The set of the values of terms. -/
theorem exists_evX (Ev : V) : ∃ X, ∀ n, M.mem n X ↔ ∃ t, M.mem (M.op t n) Ev := by
  obtain ⟨X, -, hX0⟩ := M.comp (σW [(178, 5)]) (Fml.ex 386 (fApp 178 386 0)) 0 rfl
    (Function.update (fun _ => dflt) 178 Ev)
  refine ⟨X, fun n => ?_⟩
  rw [hX0 n]
  simp [Sat, M.sat_ex, M.sat_fApp', Function.update_apply]

/-- If the inputs of a rule are values of terms, so is its output. -/
theorem evX_intro (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j) (ed : M.EvData R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev m j i)
    {X : V} (hX : ∀ n, M.mem n X ↔ ∃ t, M.mem (M.op t n) Ev)
    (x c v : M.Num) {w n : V}
    (hin : ∀ k : M.Num, k + 1 ≤ c → ∃ e, M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e ∧ M.mem e X)
    (hrule : ∀ a, M.RuleR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) g b ρ ν (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 (4 : M.Num).1 (5 : M.Num).1 (6 : M.Num).1 (7 : M.Num).1 (8 : M.Num).1 (9 : M.Num).1 (10 : M.Num).1 (11 : M.Num).1 (12 : M.Num).1 x.1 c.1 v.1 a w n) (hn : M.InNRaw P th io M.nat j.1 ρ n) : M.mem n X := by
  obtain ⟨a, ia⟩ := ed.io2_tot 0
  have ha := (ed.io2_dom _ _ ia).2
  have hnn := M.tie_refl_inN hd hPr hn
  exact (hX n).mpr (M.ev_intro hd ed x c v ha (fun k hk => by
    obtain ⟨e, h1, h2⟩ := hin k hk
    obtain ⟨a', h3⟩ := (hX e).mp h2
    exact ⟨e, a', h1, h3⟩) (hrule a) hnn hnn hn)

end ev2
/-! ## The values of terms form a closed set; the count of a generated stage -/

section ev3

variable {R E z S P th io Nt nle p F d tp qo Nu Pr Sg : V} {m j i : M.Num}
variable {q1 g b ρ ν io2 Nt2 Ev : V}

theorem exists_seq0 (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ρ n : V} (hn : M.InNRaw P th io M.nat j.1 ρ n) :
    ∃ w, M.ValRaw P th io M.nat Nt j.1 d ρ w (0 : M.Num).1 n := by
  have hR := M.inN_rung hd hn
  obtain ⟨w, hw⟩ := hd.hP.tot j hd.hj n n hR hR
  exact ⟨w, M.val_cons_zero hd hw hn⟩

/-- **The values of terms are closed under the six rules.** -/
theorem evX_closed (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    (ed : M.EvData R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev m j i) {X : V} (hX : ∀ n, M.mem n X ↔ ∃ t, M.mem (M.op t n) Ev) :
    M.ClosedR P th io M.nat Nt j.1 d M.adG tp q1 F Pr (M.restr th Sg ρ) X ρ ν := by
  obtain ⟨hνρ, hνne, hbρ⟩ := M.gen_lt hd hSg ed.hgen
  have hρ := (hd.hth.fld _ _ hνρ).2
  have hdρ := M.d_inN hd hνρ hνne
  have xin : ∀ n, M.mem n X → M.InNRaw P th io M.nat j.1 ρ n := fun n hn => by
    obtain ⟨t, ht⟩ := (hX n).mp hn
    exact M.ev_inN ed ht
  have one_in : ∀ {w n0 : V}, M.ValRaw P th io M.nat Nt j.1 d ρ w (0 : M.Num).1 n0 → M.mem n0 X → ∀ k : M.Num, k + 1 ≤ 1 →
      ∃ e, M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e ∧ M.mem e X := by
    intro w n0 hv hn0 k hk
    have hk0 : k = 0 := le_antisymm (M.le_of_succ_le_succ (by rw [zero_add]; exact hk)) zero_le
    rw [hk0]
    exact ⟨n0, hv, hn0⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n β o hn rn ho
    have hnρ := xin n hn
    obtain ⟨w, hw⟩ := M.exists_seq0 hd hnρ
    obtain ⟨β', rn', lt, ne⟩ := M.inN_rank hnρ
    have eβ : β' = β := M.rank_unique hd rn' rn
    rw [eβ] at lt ne
    exact M.evX_intro hd hPr ed hX 3 1 0 (one_in hw hn) (fun a => M.rule_mk3 ⟨rfl, n, β, hw, rn, ho⟩)
      (M.rank_inN (M.mark_rank hq ho) lt ne)
  · intro n β c u i' e hn nm hi hle hv
    have hnρ := xin n hn
    obtain ⟨w, hw⟩ := M.exists_seq0 hd hnρ
    obtain ⟨β', rn', lt, ne⟩ := M.inN_rank hnρ
    have eβ : β' = β := M.rank_unique hd rn' (M.nameR_rank nm)
    rw [eβ] at lt ne
    have heρ : M.InNRaw P th io M.nat j.1 ρ e := by
      rcases M.val_cases hv with h | h
      · exact M.inN_mono hd h lt
      · rw [h]
        exact hdρ
    exact M.evX_intro hd hPr ed hX 4 1 ⟨i', hi⟩ (one_in hw hn)
      (fun a => M.rule_mk4 ⟨rfl, n, β, c, u, hw, nm, hle, hv⟩) heρ
  · intro n β c u o ho hoX lt ne nm hvals
    have hcN : M.mem c M.nat := by
      obtain ⟨f, q, -, -, k, -⟩ := nm
      exact k
    obtain ⟨w, -, hw1, hw2⟩ := M.exists_shift_seq hd (u := u) ⟨c, hcN⟩ lt ne (xin o hoX)
    refine M.evX_intro hd hPr ed hX 5 (⟨c, hcN⟩ + 1 + 1) 0 (w := w) (fun k hk => ?_)
      (fun a => M.rule_mk5 ⟨c, ((⟨c, hcN⟩ : M.Num) + 1).1, o, β, u, (M.adG_iff ⟨c, hcN⟩ 1 _).mpr rfl,
        (M.adG_iff _ 1 _).mpr rfl, hw2, ho, lt, ne, nm,
        fun i e hi hle hv => hw1 ⟨i, hi⟩ ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ ⟨c, hcN⟩).mp hle) e hv⟩)
      (M.rank_inN (M.nameR_rank nm) lt ne)
    rcases M.eq_or_succ_le (M.le_of_succ_le_succ hk) with e1 | e1
    · rw [e1]
      exact ⟨o, hw2, hoX⟩
    · have hkc := M.le_of_succ_le_succ e1
      obtain ⟨e, he⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) β u k.1
      exact ⟨e, hw1 k hkc e he, hvals k.1 e k.2 ((M.leRaw_iff M.adG_spec k ⟨c, hcN⟩).mpr hkc) he⟩
  · intro n n0 hn hc hs
    have hnρ := xin n hn
    obtain ⟨w, hw⟩ := M.exists_seq0 hd hnρ
    exact M.evX_intro hd hPr ed hX 6 1 0 (one_in hw hn) (fun a => M.rule_mk6 ⟨rfl, n, hw, hc, hs⟩)
      (M.can_inN hd hPr hnρ hc hs)
  · intro β c v t w hβ hc hv hvals hlw
    rcases M.lwR_iff.mp hlw with hp | hn'
    ·
      rcases hβ with e | ⟨lt, ne, o, ho, hoX⟩
      · rw [e] at hvals hp
        refine M.evX_intro hd hPr ed hX 7 (⟨c, hc⟩ + 1) ⟨v, hv⟩ (w := t) (fun k hk => ?_)
          (fun a => M.rule_mk7 ⟨c, hc, (M.adG_iff ⟨c, hc⟩ 1 _).mpr rfl, hp⟩) hp.1
        obtain ⟨e', he'⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) ρ t k.1
        exact ⟨e', he', hvals k.1 e' k.2
          ((M.leRaw_iff M.adG_spec k ⟨c, hc⟩).mpr (M.le_of_succ_le_succ hk)) he'⟩
      · obtain ⟨w', -, hw1, hw2⟩ := M.exists_shift_seq hd (u := t) ⟨c, hc⟩ lt ne (xin o hoX)
        refine M.evX_intro hd hPr ed hX 9 (⟨c, hc⟩ + 1 + 1) ⟨v, hv⟩ (w := w') (fun k hk => ?_)
          (fun a => M.rule_mk9 ⟨c, ((⟨c, hc⟩ : M.Num) + 1).1, o, β, t, hc,
            (M.adG_iff ⟨c, hc⟩ 1 _).mpr rfl, (M.adG_iff _ 1 _).mpr rfl, hw2, ho, lt, ne,
            fun i e hi hle hv' => hw1 ⟨i, hi⟩ ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ ⟨c, hc⟩).mp hle) e hv',
            hp⟩) (M.inN_mono hd hp.1 lt)
        rcases M.eq_or_succ_le (M.le_of_succ_le_succ hk) with e1 | e1
        · rw [e1]
          exact ⟨o, hw2, hoX⟩
        · have hkc := M.le_of_succ_le_succ e1
          obtain ⟨e', he'⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) β t k.1
          exact ⟨e', hw1 k hkc e' he', hvals k.1 e' k.2
            ((M.leRaw_iff M.adG_spec k ⟨c, hc⟩).mpr hkc) he'⟩
    ·
      rcases hβ with e | ⟨lt, ne, o, ho, hoX⟩
      · rw [e] at hvals hn'
        refine M.evX_intro hd hPr ed hX 8 (⟨c, hc⟩ + 1) ⟨v, hv⟩ (w := t) (fun k hk => ?_)
          (fun a => M.rule_mk8 ⟨c, hc, (M.adG_iff ⟨c, hc⟩ 1 _).mpr rfl, hn'⟩) hn'.1
        obtain ⟨e', he'⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) ρ t k.1
        exact ⟨e', he', hvals k.1 e' k.2
          ((M.leRaw_iff M.adG_spec k ⟨c, hc⟩).mpr (M.le_of_succ_le_succ hk)) he'⟩
      · obtain ⟨w', -, hw1, hw2⟩ := M.exists_shift_seq hd (u := t) ⟨c, hc⟩ lt ne (xin o hoX)
        refine M.evX_intro hd hPr ed hX 10 (⟨c, hc⟩ + 1 + 1) ⟨v, hv⟩ (w := w') (fun k hk => ?_)
          (fun a => M.rule_mk10 ⟨c, ((⟨c, hc⟩ : M.Num) + 1).1, o, β, t, hc,
            (M.adG_iff ⟨c, hc⟩ 1 _).mpr rfl, (M.adG_iff _ 1 _).mpr rfl, hw2, ho, lt, ne,
            fun i e hi hle hv' => hw1 ⟨i, hi⟩ ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ ⟨c, hc⟩).mp hle) e hv',
            hn'⟩) (M.inN_mono hd hn'.1 lt)
        rcases M.eq_or_succ_le (M.le_of_succ_le_succ hk) with e1 | e1
        · rw [e1]
          exact ⟨o, hw2, hoX⟩
        · have hkc := M.le_of_succ_le_succ e1
          obtain ⟨e', he'⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) β t k.1
          exact ⟨e', hw1 k hkc e' he', hvals k.1 e' k.2
            ((M.leRaw_iff M.adG_spec k ⟨c, hc⟩).mpr hkc) he'⟩
  · intro β1 o1 β2 w y ho1 ho1X l12 hy hG hleast hprl
    have ho1ρ := xin o1 ho1X
    obtain ⟨w', hw'⟩ := M.exists_seq0 hd ho1ρ
    obtain ⟨hSgy, lt2, ne2⟩ := M.mem_restr.mp hG
    refine ⟨fun o2 ho2 => ?_, ?_⟩
    · exact M.evX_intro hd hPr ed hX 11 1 0 (one_in hw' ho1X)
        (fun a => M.rule_mk11 ⟨rfl, o1, β1, β2, w, y, hw', ho1, l12, hy, hG, hleast, hprl, ho2⟩)
        (M.rank_inN (M.mark_rank hq ho2) lt2 ne2)
    · have hgen : M.Gen P Sg j ν β2 w := ⟨y, hy, hSgy⟩
      exact M.evX_intro hd hPr ed hX 12 1 0 (one_in hw' ho1X)
        (fun a => M.rule_mk12 ⟨rfl, o1, β1, β2, w, y, hw', ho1, l12, hy, hG, hleast, hprl, rfl⟩)
        (M.inN_mono hd (M.gen_lt hd hSg hgen).2.2 lt2)

/-- Every name of rank below a generated stage is the value of a term. -/
theorem evX_all (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    (ed : M.EvData R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev m j i) {X : V} (hX : ∀ n, M.mem n X ↔ ∃ t, M.mem (M.op t n) Ev) :
    ∀ x, M.InNRaw P th io M.nat j.1 ρ x → M.mem x X := by
  obtain ⟨hνρ, hνne, hbρ⟩ := M.gen_lt hd hSg ed.hgen
  have hcl := M.evX_closed hd hPr hq hSg ed hX
  have hdρ := M.d_inN hd hνρ hνne
  have noin : ∀ (w : V) (k : M.Num), k + 1 ≤ 0 → ∃ e, M.ValRaw P th io M.nat Nt j.1 d ρ w k.1 e ∧ M.mem e X :=
    fun w k hk => (M.not_succ_le k (le_trans hk zero_le)).elim
  have hdX : M.mem d X := M.evX_intro hd hPr ed hX 2 0 0 (w := d) (noin d)
    (fun a => M.rule_mk2 ⟨rfl, rfl⟩) hdρ
  have hbX : M.mem b X := M.evX_intro hd hPr ed hX 1 0 0 (w := d) (noin d)
    (fun a => M.rule_mk1 ⟨rfl, rfl⟩) hbρ
  have hbase : ∀ x, M.InNRaw P th io M.nat j.1 ν x → M.mem x X := fun x hx =>
    M.closed_below hd hcl hdX hνρ (fun β' lt ne => by
      obtain ⟨o, ho⟩ := M.exists_mark hd hq (hd.hth.fld _ _ lt).1
      obtain ⟨a, ha⟩ := ed.g_tot β' lt ne
      have hoρ : M.InNRaw P th io M.nat j.1 ρ o := M.rank_inN (M.mark_rank hq ho) (hd.hth.trans _ _ _ lt hνρ)
        (M.wo_ne_of_lt_le hd.hth lt ne hνρ)
      have hoo := M.tie_refl_inN hd hPr hoρ
      refine ⟨o, o, (hX o).mpr (M.ev_intro hd ed 0 0 0 (w := d) (ed.g_dom β' a ha).2.2
        (fun k hk => (M.not_succ_le k (le_trans hk zero_le)).elim)
        (M.rule_mk0 ⟨rfl, β', ha, ho⟩) hoo hoo hoρ), M.mark_rank hq ho, ho⟩) hx
  exact ((M.gen_iff hd hSg).mp ed.hgen).2.2.2.2 X hbase hbX hdX hcl

/-- **The count of a generated stage.** If the stages below `ν` map one-to-one into the rung
`i`, and `ρ` is generated from `ν` and a name, then the stages below `ρ` map one-to-one into
the rung `i + 1`: a stage goes to the set of the terms that evaluate to its marker. -/
theorem gen_small (h : M.IsLadder R E z S m) (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    (ed : M.EvData R P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 Ev m j i) (hi1 : i + 1 ≤ m) :
    ∃ g', (∀ β, M.mem (M.op β ρ) th → β ≠ ρ → ∃ A, M.mem (M.op β A) g') ∧
      (∀ β A, M.mem (M.op β A) g' → M.mem (M.op (i + 1).1 A) R) ∧
      (∀ β A A', M.mem (M.op β A) g' → M.mem (M.op β A') g' → A = A') ∧
      (∀ β β' A, M.mem (M.op β A) g' → M.mem (M.op β' A) g' → β = β') := by
  obtain ⟨X, hX⟩ := M.exists_evX Ev
  have hall := M.evX_all hd hPr hq hSg ed hX
  obtain ⟨g', -, hg0⟩ := M.comp (σW [(0, 4), (20, 7), (22, 5), (178, 5), (393, 5), (394, 7)])
    (Fml.ex 401 (Fml.ex 402 (Fml.ex 403 (.and (fPr 0 401 402) (.and (fApp 393 398 402) (.and (fApp 22 401 271) (.and (.neg (.eq 401 271)) (.and (fApp4 20 25 401 160 403) (.all 404 (Fml.iff (.and (fApp 393 176 404) (fApp3 394 176 404 402)) (fApp 178 404 403))))))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 25 j.1) 160 q1) 176 i.1) 178 Ev) 271 ρ) 393 R) 394 E) 398 (i + 1).1)
  have hg1 : ∀ q, M.mem q g' ↔ ∃ β A o, q = M.op β A ∧ M.mem (M.op (i + 1).1 A) R ∧
      M.mem (M.op β ρ) th ∧ ¬ β = ρ ∧ M.mem (M.quad j.1 β q1 o) P ∧
      ∀ t, (M.mem (M.op i.1 t) R ∧ M.mem (M.trip i.1 t A) E) ↔ M.mem (M.op t o) Ev := by
    intro q
    rw [hg0 q]
    simp [Sat, M.sat_ex, M.sat_iff, M.sat_fPr', M.sat_fApp', M.sat_fApp3', M.sat_fApp4',
      Function.update_apply]
  have hg : ∀ β A, M.mem (M.op β A) g' ↔ ∃ o, M.mem (M.op (i + 1).1 A) R ∧
      M.mem (M.op β ρ) th ∧ ¬ β = ρ ∧ M.mem (M.quad j.1 β q1 o) P ∧
      ∀ t, (M.mem (M.op i.1 t) R ∧ M.mem (M.trip i.1 t A) E) ↔ M.mem (M.op t o) Ev := by
    intro β A
    rw [hg1]
    constructor
    · rintro ⟨β1, A1, o, hq, h⟩
      obtain ⟨e1, e2⟩ := M.op_inj hq
      rw [e1, e2]
      exact ⟨o, h⟩
    · rintro ⟨o, h⟩
      exact ⟨β, A, o, rfl, h⟩
  have hZ : ∀ o, ∃ Z, M.isSet Z ∧ ∀ t, M.mem t Z ↔ M.mem (M.op t o) Ev := by
    intro o
    obtain ⟨Z, hZs, hZ0⟩ := M.comp (σW [(178, 5)]) (fApp 178 0 403) 0 rfl
      (Function.update (Function.update (fun _ => dflt) 178 Ev) 403 o)
    refine ⟨Z, hZs, fun t => ?_⟩
    rw [hZ0 t]
    simp [M.sat_fApp', Function.update_apply]
  refine ⟨g', fun β lt ne => ?_, fun β A h1 => ?_, fun β A A' h1 h2 => ?_, fun β β' A h1 h2 => ?_⟩
  · obtain ⟨o, ho⟩ := M.exists_mark hd hq (hd.hth.fld _ _ lt).1
    obtain ⟨Z, hZs, hZm⟩ := hZ o
    obtain ⟨A, hA, hmem, -⟩ := h.full i hi1 Z hZs (fun t ht => M.ev_rung hd ed ((hZm t).mp ht))
    exact ⟨A, (hg β A).mpr ⟨o, hA, lt, ne, ho, fun t => ((hmem t).symm.trans (hZm t))⟩⟩
  · obtain ⟨o, hA, -⟩ := (hg β A).mp h1
    exact hA
  · obtain ⟨o, hA, lt, ne, ho, hm⟩ := (hg β A).mp h1
    obtain ⟨o', hA', -, -, ho', hm'⟩ := (hg β A').mp h2
    have eo : o = o' := hd.hP.fn _ _ _ _ _ ho ho'
    rw [← eo] at hm'
    obtain ⟨Z, hZs, hZm⟩ := hZ o
    obtain ⟨B, hB, hmemB, huniq⟩ := h.full i hi1 Z hZs (fun t ht => M.ev_rung hd ed ((hZm t).mp ht))
    have c1 : A = B := huniq A hA (fun t => (hZm t).trans (hm t).symm)
    have c2 : A' = B := huniq A' hA' (fun t => (hZm t).trans (hm' t).symm)
    rw [c1, c2]
  · obtain ⟨o, hA, lt, ne, ho, hm⟩ := (hg β A).mp h1
    obtain ⟨o', hA', lt', ne', ho', hm'⟩ := (hg β' A).mp h2
    have hoρ : M.InNRaw P th io M.nat j.1 ρ o := M.rank_inN (M.mark_rank hq ho) lt ne
    obtain ⟨t, ht⟩ := (hX o).mp (hall o hoρ)
    have ht' : M.mem (M.op t o') Ev := (hm' t).mp ((hm t).mpr ht)
    obtain ⟨t1, t2⟩ := M.ev_fun hd hPr hq hSg ed ht ht'
    exact M.tie_rank hd hPr (M.mark_rank hq ho) (M.mark_rank hq ho') t1 t2

/-- The count of a generated stage, with the data for terms constructed. -/
theorem gen_count (h : M.IsLadder R E z S m) (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    {i : M.Num} (hi1 : i + 1 ≤ m) {g b ρ ν : V}
    (g_tot : ∀ β, M.mem (M.op β ν) th → β ≠ ν → ∃ a, M.mem (M.op β a) g)
    (g_dom : ∀ β a, M.mem (M.op β a) g → M.mem (M.op β ν) th ∧ β ≠ ν ∧ M.mem (M.op i.1 a) R)
    (g_inj : ∀ β β' a, M.mem (M.op β a) g → M.mem (M.op β' a) g → β = β')
    (hgen : M.Gen P Sg j ν ρ b) :
    ∃ g', (∀ β, M.mem (M.op β ρ) th → β ≠ ρ → ∃ A, M.mem (M.op β A) g') ∧
      (∀ β A, M.mem (M.op β A) g' → M.mem (M.op (i + 1).1 A) R) ∧
      (∀ β A A', M.mem (M.op β A) g' → M.mem (M.op β A') g' → A = A') ∧
      (∀ β β' A, M.mem (M.op β A) g' → M.mem (M.op β' A) g' → β = β') := by
  have hi : i ≤ m := le_trans (M.le_add_one i) hi1
  obtain ⟨u, v, hu, hv, huv⟩ := M.rung_two h hi
  obtain ⟨io2, io_dom, io_tot, io_fun, io_inj, -⟩ := M.exists_numerals hd.hP hi hu hv huv
  obtain ⟨Nt2, -, nt0, nts⟩ := M.exists_seq hd.hP hi
  obtain ⟨Ev, hEv⟩ := M.exists_evSet P th io Nt d tp q1 F Pr Sg g b ρ ν io2 Nt2 j i
  exact M.gen_small h hd hPr hq hSg
    ⟨hi, io_dom, io_tot, io_fun, io_inj, nt0, nts, g_tot, g_dom, g_inj, hgen, hEv⟩ hi1

end ev3
/-! ## The least stage that is not small exists -/

theorem segOf_emb_seg {s r f a : V} (hr : M.IsWO r) (ha : M.mem (M.op a a) r)
    (h : M.SegOf s r f a) : M.Emb s (M.seg r a) := by
  obtain ⟨hf, hfull, hna, hsurj⟩ := h
  refine ⟨f, ⟨fun x y hxy => ?_, fun x y x' y' hxy hxy' => ?_, hf.2.2.1,
    fun x y y' hxy hle => ?_⟩, hfull⟩
  · exact ⟨(hf.1 x y hxy).1, (M.seg_fld hr).mpr (M.segOf_ran_lt hr ha ⟨hf, hfull, hna, hsurj⟩ hxy)⟩
  · rw [hf.2.1 x y x' y' hxy hxy', M.mem_seg]
    exact ⟨fun h1 => ⟨h1, M.segOf_ran_lt hr ha ⟨hf, hfull, hna, hsurj⟩ hxy'⟩, fun h1 => h1.1⟩
  · exact hf.2.2.2 x y y' hxy (M.mem_seg.mp hle).1

theorem emb_conv_of_onto {r s f : V} (hf : M.PIso r s f)
    (honto : ∀ y, M.mem (M.op y y) s → ∃ x, M.mem (M.op x y) f) : M.Emb s r :=
  ⟨M.conv f, M.piso_conv hf, fun y hy => by
    obtain ⟨x, hx⟩ := honto y hy
    exact ⟨x, M.mem_conv.mpr hx⟩⟩

/-- A well-ordering none of whose proper initial segments is as long as `H1` embeds into
`H1`. -/
theorem emb_of_not_seg {r H1 : V} (hr : M.IsWO r) (hH1 : M.IsWO H1)
    (hno : ∀ a, M.mem (M.op a a) r → ¬ M.Emb H1 (M.seg r a)) : M.Emb r H1 := by
  rcases M.emb_total hr hH1 with h1 | ⟨f, hf, hfull⟩
  · exact h1
  · rcases M.piso_onto_or_seg hr hf hfull with honto | ⟨a, ha, hseg⟩
    · exact M.emb_conv_of_onto hf honto
    · exact (hno a ha (M.segOf_emb_seg hr ha hseg)).elim

theorem seg_seg {r κ a x y : V} (hr : M.IsWO r) (ha : M.mem (M.op a κ) r) (hne : a ≠ κ) :
    M.mem (M.op x y) (M.seg (M.seg r κ) a) ↔ M.mem (M.op x y) (M.seg r a) := by
  simp only [M.mem_seg]
  constructor
  · rintro ⟨⟨h1, -, -⟩, ⟨h2, -, -⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨k1, k2⟩ := M.lt_of_le_lt hr h2 ha hne
    exact ⟨⟨h1, k1, k2⟩, ⟨h2, ha, hne⟩, h3⟩

section next1

variable {R E z S P th io Nt nle p F d tp qo Nu Pr Sg : V} {m j : M.Num}
variable {q1 : V}

/-- **The least stage that is not small exists.** Let the well-ordering of the stages be
longer than every well-ordering of a part of the rung `L`. If the stages below `ν` map
one-to-one into a rung `i` with `i + 3 ≤ L`, then there is a least stage `κ` that is not
`ν`-small, and the stages below `κ` map one-to-one into the rung `i + 3`. -/
theorem next_exists (h : M.IsLadder R E z S m) (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    {i L : M.Num} (hiL : i + 1 + 1 + 1 ≤ L) (hL : L ≤ m)
    (hlong : ∀ w, M.IsWO w →
      (∀ a b, M.mem (M.op a b) w → M.mem (M.op L.1 a) R ∧ M.mem (M.op L.1 b) R) →
      M.Emb w th ∧ ¬ M.Emb th w)
    {g ν : V}
    (g_tot : ∀ β, M.mem (M.op β ν) th → β ≠ ν → ∃ a, M.mem (M.op β a) g)
    (g_dom : ∀ β a, M.mem (M.op β a) g → M.mem (M.op β ν) th ∧ β ≠ ν ∧ M.mem (M.op i.1 a) R)
    (g_inj : ∀ β β' a, M.mem (M.op β a) g → M.mem (M.op β' a) g → β = β') :
    ∃ κ g', M.IsNext P th Sg j ν κ ∧
      (∀ β, M.mem (M.op β κ) th → β ≠ κ → ∃ a, M.mem (M.op β a) g') ∧
      (∀ β a, M.mem (M.op β a) g' → M.mem (M.op β κ) th ∧ β ≠ κ ∧
        M.mem (M.op (i + 1 + 1 + 1).1 a) R) ∧
      (∀ β β' a, M.mem (M.op β a) g' → M.mem (M.op β' a) g' → β = β') := by
  have hth := hd.hth
  have hi3 : i + 1 + 1 + 1 ≤ m := le_trans hiL hL
  have hi1 : i + 1 ≤ m := le_trans (le_trans (M.le_add_one _) (M.le_add_one _)) hi3
  obtain ⟨H1, hH1, fldH1, hlong1, -⟩ := M.hartogs h hd.hP (i := i + 1) hi3
  have small_emb : ∀ β, M.Small P th Sg j ν β →
      M.Emb (M.seg th β) H1 ∧ ¬ M.Emb H1 (M.seg th β) := by
    rintro β ⟨ρ2, b, hβρ2, hgen⟩
    obtain ⟨g', gt, gr, gf, gi⟩ := M.gen_count h hd hPr hq hSg hi1 g_tot g_dom g_inj hgen
    obtain ⟨w, hw, hwran, hemb, -⟩ := M.wo_transport (M.isWO_seg hth (a := β)) gf gi
      (fun e he => by
        obtain ⟨h1, h2⟩ := (M.seg_fld hth).mp he
        exact gt e (hth.trans _ _ _ h1 hβρ2) (M.wo_ne_of_lt_le hth h1 h2 hβρ2))
    obtain ⟨k1, k2⟩ := hlong1 w hw (fun a b hab => by
      obtain ⟨⟨e, he⟩, ⟨e', he'⟩⟩ := hwran a b hab
      exact ⟨gr e a he, gr e' b he'⟩)
    exact ⟨M.emb_trans hemb k1, fun hc => k2 (M.emb_trans hc hemb)⟩
  have exists_ns : ∃ ρ, M.mem (M.op ρ ρ) th ∧ ¬ M.Small P th Sg j ν ρ := by
    by_contra hcon
    have hall : ∀ ρ, M.mem (M.op ρ ρ) th → M.Small P th Sg j ν ρ := fun ρ hρ => by
      by_contra hns
      exact hcon ⟨ρ, hρ, hns⟩
    obtain ⟨f, hf, hfull⟩ := M.emb_of_not_seg hth hH1 (fun a ha => (small_emb a (hall a ha)).2)
    obtain ⟨e, e1, e2, e3, e4⟩ := M.rung_lift h (i + 1 + 1 + 1) L hiL hL
    refine M.hartogs_no_inj hth hlong (g := M.rcomp f e) (fun x a a' h1 h2 => ?_)
      (fun x x' a h1 h2 => ?_) (fun x hx => ?_) (fun x a h1 => ?_)
    · obtain ⟨y, k1, k2⟩ := M.mem_rcomp.mp h1
      obtain ⟨y', k1', k2'⟩ := M.mem_rcomp.mp h2
      have ey : y = y' := M.piso_fun hH1 hf k1 k1'
      rw [← ey] at k2'
      exact e3 y a a' k2 k2'
    · obtain ⟨y, k1, k2⟩ := M.mem_rcomp.mp h1
      obtain ⟨y', k1', k2'⟩ := M.mem_rcomp.mp h2
      have ey : y = y' := e4 y y' a k2 k2'
      rw [← ey] at k1'
      exact M.piso_inj hth hf k1 k1'
    · obtain ⟨y, hy⟩ := hfull x hx
      obtain ⟨z0, hz0⟩ := e1 y (fldH1 y (hf.1 x y hy).2)
      exact ⟨z0, M.mem_rcomp.mpr ⟨y, hy, hz0⟩⟩
    · obtain ⟨y, k1, k2⟩ := M.mem_rcomp.mp h1
      exact (e2 y a k2).2
  obtain ⟨B, -, hB0⟩ := M.comp (σW [(20, 7), (22, 5), (164, 5)]) (.neg (Fml.ex 401 (Fml.ex 402 (.and (fApp 22 0 401) (Fml.ex 403 (.and (fApp4 20 25 272 402 403) (fApp 164 401 403))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 22 th) 25 j.1) 164 Sg) 272 ν)
  have hB : ∀ ρ, M.mem ρ B ↔ ¬ M.Small P th Sg j ν ρ := by
    intro ρ
    rw [hB0 ρ]
    simp [Small, Gen, Sat, M.sat_ex, M.sat_fApp', M.sat_fApp4', Function.update_apply]
  obtain ⟨ρ0, hρ0, hns0⟩ := exists_ns
  obtain ⟨κ, hκB, hκ, hmin⟩ := hth.least B ⟨ρ0, (hB ρ0).mpr hns0, hρ0⟩
  have hnext : M.IsNext P th Sg j ν κ := ⟨hκ, (hB κ).mp hκB, fun ρ lt ne => by
    by_contra hns
    exact ne (hth.antisymm _ _ lt (hmin ρ ((hB ρ).mpr hns) (hth.fld _ _ lt).1))⟩
  have hsmall : ∀ a, M.mem (M.op a a) (M.seg th κ) → M.Small P th Sg j ν a := fun a ha => by
    obtain ⟨h1, h2⟩ := (M.seg_fld hth).mp ha
    exact hnext.2.2 a h1 h2
  obtain ⟨f, hf, hfull⟩ := M.emb_of_not_seg (M.isWO_seg hth (a := κ)) hH1 (fun a ha hc => by
    obtain ⟨h1, h2⟩ := (M.seg_fld hth).mp ha
    exact (small_emb a (hsmall a ha)).2
      ((M.emb_congr (fun x y => Iff.rfl) (fun x y => M.seg_seg hth h1 h2)).mp hc))
  refine ⟨κ, f, hnext, fun β lt ne => hfull β ((M.seg_fld hth).mpr ⟨lt, ne⟩), fun β a hβa => ?_,
    fun β β' a h1 h2 => M.piso_inj (M.isWO_seg hth) hf h1 h2⟩
  obtain ⟨k1, k2⟩ := hf.1 β a hβa
  obtain ⟨l1, l2⟩ := (M.seg_fld hth).mp k1
  exact ⟨l1, l2, fldH1 a k2⟩

end next1
/-! ## Separation at the least stage that is not small, as coded sentences -/

/-- The instance of Separation for the formula `φ`, with the comprehension variable `0`:
`∀a ∃b ∀v₀ (v₀ ε b ↔ (v₀ ε a ∧ φ))`. -/
noncomputable def cSep (a b φ : M.Num) : M.Num :=
  M.cAll a (M.cEx b (M.cAll 0 (M.cIff (M.cRel 0 0 b) (M.cAnd (M.cRel 0 0 a) φ))))

section sep1

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {ν Sg : V}
variable {q1 : V}

/-- The sequence of the values of `t1` at the variables `1`, `2`, …, below `n`. -/
theorem exists_tail (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {κ t1 : V}
    (hdκ : M.InNRaw P th io M.nat j.1 κ d) (n : M.Num) :
    ∃ u, M.mem (M.op j.1 u) R ∧ ∀ k : M.Num, k + 1 ≤ n → ∀ e, M.ValRaw P th io M.nat Nt j.1 d κ t1 (k + 1).1 e →
      M.ValRaw P th io M.nat Nt j.1 d κ u k.1 e := by
  obtain ⟨g, -, hg0⟩ := M.comp (σW [(0, 4), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7)])
    (Fml.ex 326 (Fml.ex 327 (Fml.ex 328 (.and (fPr 0 326 327) (.and (.mem 326 27) (.and (fApp3 28 326 11 328) (fVal 250 340 328 327))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 11 (1 : M.Num).1) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 250 κ) 340 t1)
  have hg1 : ∀ q, M.mem q g ↔ ∃ k e k', q = M.op k e ∧ M.mem k M.nat ∧
      M.mem (M.trip k (1 : M.Num).1 k') M.adG ∧ M.ValRaw P th io M.nat Nt j.1 d κ t1 k' e := by
    intro q
    rw [hg0 q]
    simp [Sat, M.sat_ex, M.sat_fPr', M.sat_fVal, M.sat_fApp3', Function.update_apply]
  have hgs : ∀ (k : M.Num) (e : V), M.mem (M.op k.1 e) g ↔ M.ValRaw P th io M.nat Nt j.1 d κ t1 (k + 1).1 e := by
    intro k e
    rw [hg1]
    constructor
    · rintro ⟨k1, e1, k', hq, -, hk', hv⟩
      obtain ⟨q1', q2'⟩ := M.op_inj hq
      rw [← q1'] at hk'
      rw [← q2', M.adG_num hk'] at hv
      exact hv
    · intro h
      exact ⟨k.1, e, (k + 1).1, rfl, k.2, (M.adG_iff k 1 (k + 1)).mpr rfl, h⟩
  have hvalN : ∀ (i : V) (e : V), M.ValRaw P th io M.nat Nt j.1 d κ t1 i e → M.InNRaw P th io M.nat j.1 κ e := by
    intro i e hv
    rcases M.val_cases hv with h | h
    · exact h
    · rw [h]
      exact hdκ
  obtain ⟨u, huR, hu⟩ := M.exists_seq_vals hd (σ := κ) (g := g) n
    (fun k hk => by
      obtain ⟨e, he⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) κ t1 (k + 1).1
      exact ⟨e, hvalN _ e he, (hgs k e).mpr he⟩)
    (fun k a hk hka => hvalN _ a ((hgs k a).mp hka))
  refine ⟨u, huR, fun k hk e he => ?_⟩
  obtain ⟨a, hga, hva⟩ := hu k hk
  rw [M.val_unique hd he ((hgs k a).mp hga)]
  exact hva

/-- Truth under a sequence that begins with `y₀` and continues with the tail of `t1` is truth
under a sequence that has a value denoting the same set as `y₀` at the variable `0` and the
values of `t1` elsewhere. -/
theorem cons_agree (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {κ t1 u y0 y s t3 : V}
    (c : M.Num) (hκ : M.mem (M.op κ κ) th) (hs : M.mem (M.quad j.1 y0 u s) P)
    (hy0 : M.InNRaw P th io M.nat j.1 κ y0)
    (htail : ∀ k : M.Num, k + 1 ≤ c → ∀ e, M.ValRaw P th io M.nat Nt j.1 d κ t1 (k + 1).1 e → M.ValRaw P th io M.nat Nt j.1 d κ u k.1 e)
    (h0 : M.ValRaw P th io M.nat Nt j.1 d κ t3 (0 : M.Num).1 y) (hsim : M.SimRaw P j.1 tp F y0 y)
    (hrest : ∀ k : M.Num, k + 1 ≤ c → ∀ e, M.ValRaw P th io M.nat Nt j.1 d κ t1 (k + 1).1 e → M.ValRaw P th io M.nat Nt j.1 d κ t3 (k + 1).1 e) :
    M.TrueAt P io F j.1 κ c s ↔ M.TrueAt P io F j.1 κ c t3 := by
  refine M.inv_hier hd c s t3 (fun i hi => ?_)
  rcases M.num_cases i with e0 | ⟨k, ek⟩
  · have ei : i = 0 := e0
    rw [ei]
    exact ⟨y0, y, M.val_cons_zero hd hs hy0, h0, hsim⟩
  · have ei : i = k + 1 := by rw [ek, M.nsucc_eq_add_one]
    rw [ei] at hi ⊢
    obtain ⟨e, he⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) κ t1 (k + 1).1
    exact ⟨e, e, (M.val_cons_succ hd hs k).mpr (htail k hi e he), hrest k hi e he,
      M.val_sim_refl hd hκ he⟩

/-- **Separation at the least stage that is not small**, as coded sentences: for every code
`φ`, the instance of Separation for `φ` is true at that stage under every sequence. The
variable `b` must be larger than the code of `v₀ ε a ∧ φ`, so that it does not occur in it. -/
theorem hier_sep (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    {κ : V} (hκ : M.IsNext P th Sg j ν κ) {σ' δ : V}
    (hκσ' : M.mem (M.op κ σ') th) (neκ : κ ≠ σ') (hσ'δ : M.mem (M.op σ' δ) th) (neσ' : σ' ≠ δ) (a b φ : M.Num) (ha0 : a ≠ 0)
    (hb : M.cAnd (M.cRel 0 0 a) φ + 1 ≤ b) (t : V) :
    M.TrueAt P io F j.1 κ (M.cSep a b φ) t := by
  have hth := hd.hth
  have hα := hκ.1
  obtain ⟨φ', hφ'⟩ : ∃ φ' : M.Num, φ' = M.cAnd (M.cRel 0 0 a) φ := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : M.Num, I = M.cAll 0 (M.cIff (M.cRel 0 0 b) φ') := ⟨_, rfl⟩
  have hunf : M.cSep a b φ = M.cAll a (M.cEx b I) := by
    rw [hI, hφ']
    rfl
  rw [← hφ'] at hb
  have haφ : a ≤ φ' := by
    rw [hφ']
    exact le_trans (M.le_cRel_right 0 0 a) (M.le_cAnd_left _ _)
  have hb0 : b ≠ 0 := fun e => by
    rw [e] at hb
    exact M.not_succ_le φ' (le_trans hb zero_le)
  have hφI : φ' ≤ I := by
    rw [hI]
    exact le_trans (M.le_cIff_right _ _) (M.le_cAll_body 0 _)
  rw [hunf, M.hier_all_ex hd]
  refine ⟨hα, fun A hA => ?_⟩
  obtain ⟨t1, hag1⟩ := M.exists_upd hd hA t a.1 (M.cAll a (M.cEx b I))
  refine ⟨t1, hag1, ?_⟩
  have hA1 : M.ValRaw P th io M.nat Nt j.1 d κ t1 a.1 A := M.agree_same hag1 (M.le_cAll_var a _)
  obtain ⟨βA, rA, ltA, neA⟩ := M.inN_rank hA
  have hdκ : M.InNRaw P th io M.nat j.1 κ d := M.d_inN hd ltA neA
  obtain ⟨u, huR, htail⟩ := M.exists_tail hd (t1 := t1) hdκ (φ' + 1)
  have consA : ∀ y0 s, M.mem (M.quad j.1 y0 u s) P → M.ValRaw P th io M.nat Nt j.1 d κ s a.1 A := by
    intro y0 s hs
    rcases M.num_cases a with e0 | ⟨k, ek⟩
    · exact (ha0 e0).elim
    · have eak : a = k + 1 := by rw [ek, M.nsucc_eq_add_one]
      rw [eak] at hA1 haφ ⊢
      exact (M.val_cons_succ hd hs k).mpr (htail k (le_trans haφ (M.le_add_one _)) A hA1)
  obtain ⟨B0, hB0, hB0m⟩ := M.next_sep hd hPr hq hNu hSg hκ hκσ' neκ hσ'δ neσ' ltA neA huR φ'
    (fun y hy ⟨s, hs, htr⟩ => by
      rw [hφ', M.hier_and hd] at htr
      obtain ⟨-, h1, -⟩ := htr
      have hy0 : M.ValRaw P th io M.nat Nt j.1 d κ s (0 : M.Num).1 y := M.val_cons_zero hd hs hy
      obtain ⟨y', hsy, hey⟩ := (M.rel_val hd 0 a hα hy0 (consA y s hs)).mp h1
      exact ⟨y', M.eps_inN_rank hd rA hey, hsy⟩)
  rw [M.hier_ex hd hα]
  obtain ⟨t2, hag2⟩ := M.exists_upd hd hB0 t1 b.1 (M.cAll b (M.cNeg I))
  refine ⟨B0, hB0, t2, hag2, ?_⟩
  have hB2 : M.ValRaw P th io M.nat Nt j.1 d κ t2 b.1 B0 := M.agree_same hag2 (M.le_cAll_var b _)
  rw [hI, M.hier_all_ex hd]
  refine ⟨hα, fun y hy => ?_⟩
  obtain ⟨t3, hag3⟩ := M.exists_upd hd hy t2 (0 : M.Num).1 (M.cAll 0 (M.cIff (M.cRel 0 0 b) φ'))
  refine ⟨t3, hag3, ?_⟩
  have hy3 : M.ValRaw P th io M.nat Nt j.1 d κ t3 (0 : M.Num).1 y := M.agree_same hag3 (M.le_cAll_var 0 _)
  have hB3 : M.ValRaw P th io M.nat Nt j.1 d κ t3 b.1 B0 := M.agree_other hag3
    (le_trans (le_trans (M.le_cRel_right 0 0 b) (M.le_cIff_left _ _)) (M.le_cAll_body 0 _)) hb0 hB2
  have hrest : ∀ k : M.Num, k + 1 ≤ φ' → ∀ e, M.ValRaw P th io M.nat Nt j.1 d κ t1 (k + 1).1 e → M.ValRaw P th io M.nat Nt j.1 d κ t3 (k + 1).1 e := by
    intro k hk e he
    have h2 : M.ValRaw P th io M.nat Nt j.1 d κ t2 (k + 1).1 e := M.agree_other hag2
      (le_trans (le_trans hk hφI) (le_trans (M.le_cNeg I) (M.le_cAll_body b _)))
      (fun e' => M.not_succ_le φ' (le_trans hb (by rw [← e']; exact hk))) he
    exact M.agree_other hag3 (le_trans hk (le_trans (M.le_cIff_right _ _) (M.le_cAll_body 0 _)))
      (fun e' => M.not_succ_le k (by rw [e']; exact zero_le)) h2
  rw [M.hier_iff hd hα, M.rel_val hd 0 b hα hy3 hB3, hB0m y]
  constructor
  · rintro ⟨y0, hsy, hy0, s, hs, htr⟩
    exact (M.cons_agree hd φ' hα hs hy0 (fun k hk => htail k (le_trans hk (M.le_add_one _))) hy3
      (M.sim_symm hd hsy) hrest).mp htr
  · intro htr
    obtain ⟨s, hs⟩ := hd.hP.tot j hd.hj y u (M.inN_rung hd hy) huR
    exact ⟨y, M.inN_refl hd hy, hy, s, hs,
      (M.cons_agree hd φ' hα hs hy (fun k hk => htail k (le_trans hk (M.le_add_one _))) hy3
        (M.inN_refl hd hy) hrest).mpr htr⟩

end sep1
/-! ## Collection at the least stage that is not small, as coded sentences -/

/-- The instance of Collection for the formula `φ`:
`∀a (∀y (y ε a → ∃z φ) → ∃b ∀y (y ε a → ∃z (z ε b ∧ φ)))`. -/
noncomputable def cColl (a b y z φ : M.Num) : M.Num :=
  M.cAll a (M.cImp (M.cAll y (M.cImp (M.cRel 0 y a) (M.cEx z φ)))
    (M.cEx b (M.cAll y (M.cImp (M.cRel 0 y a) (M.cEx z (M.cAnd (M.cRel 0 z b) φ))))))

section coll3

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num} {ν Sg : V}
variable {q1 : V}

theorem agree_val_ne {α t t' a e : V} {v i C : M.Num}
    (hag : M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v.1 a C.1) (hi : i ≤ C) (hne : i ≠ v) :
    M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e ↔ M.ValRaw P th io M.nat Nt j.1 d α t i.1 e := by
  have h := hag i.1 i.2 ((M.leRaw_iff M.adG_spec i C).mpr hi) e
  constructor
  · intro h1
    rcases h.mp h1 with ⟨e1, -⟩ | ⟨-, h2⟩
    · exact (hne (Subtype.ext e1)).elim
    · exact h2
  · intro h1
    exact M.agree_other hag hi hne h1

/-- Truth with the value at `v` changed depends only on the values at the other variables. -/
theorem tu_coin_eq (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t ts w : V} (c v : M.Num)
    (hα : M.mem (M.op α α) th) (hw : M.InNRaw P th io M.nat j.1 α w)
    (h : ∀ i : M.Num, i ≤ c → i ≠ v → ∀ e, M.ValRaw P th io M.nat Nt j.1 d α t i.1 e → M.ValRaw P th io M.nat Nt j.1 d α ts i.1 e) :
    M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 t w ↔ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F α c.1 v.1 ts w := by
  obtain ⟨t1, hag1⟩ := M.exists_upd hd hw t v.1 c
  obtain ⟨t2, hag2⟩ := M.exists_upd hd hw ts v.1 c
  rw [M.trueUpd_iff hd c v hag1, M.trueUpd_iff hd c v hag2]
  refine M.inv_hier hd c t1 t2 (fun i hi => ?_)
  by_cases e : i = v
  · rw [e] at hi ⊢
    exact ⟨w, w, M.agree_same hag1 hi, M.agree_same hag2 hi, M.inN_refl hd hw⟩
  · obtain ⟨e1, he1⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j) α t i.1
    exact ⟨e1, e1, M.agree_other hag1 hi e he1, M.agree_other hag2 hi e (h i hi e e1 he1),
      M.val_sim_refl hd hα he1⟩

/-- **Collection at the least stage that is not small**, as coded sentences: for every code
`φ`, the instance of Collection for `φ` is true at that stage under every sequence. The
variable `b` must be larger than the code `φ` and different from the other three. -/
theorem hier_coll (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    {κ : V} (hκ : M.IsNext P th Sg j ν κ) {σ' δ : V}
    (hκσ' : M.mem (M.op κ σ') th) (neκ : κ ≠ σ') (hσ'δ : M.mem (M.op σ' δ) th) (neσ' : σ' ≠ δ) (a b y z φ : M.Num) (hay : a ≠ y)
    (hab : a ≠ b) (hby : b ≠ y) (hbz : b ≠ z) (hφb : φ + 1 ≤ b) (t : V) :
    M.TrueAt P io F j.1 κ (M.cColl a b y z φ) t := by
  have hα := hκ.1
  obtain ⟨ψ, hψ⟩ : ∃ ψ : M.Num, ψ = M.cAnd (M.cRel 0 z b) φ := ⟨_, rfl⟩
  obtain ⟨D1, hD1⟩ : ∃ D1 : M.Num, D1 = M.cImp (M.cRel 0 y a) (M.cEx z φ) := ⟨_, rfl⟩
  obtain ⟨D2, hD2⟩ : ∃ D2 : M.Num, D2 = M.cImp (M.cRel 0 y a) (M.cEx z ψ) := ⟨_, rfl⟩
  have hunf : M.cColl a b y z φ = (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := by
    rw [hD1, hD2, hψ]
    rfl
  have b_body : M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)) ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := M.le_cAll_body a _
  have b_C1 : M.cAll y D1 ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (M.le_cImp_left _ _) b_body
  have b_C2 : M.cEx b (M.cAll y D2) ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (M.le_cImp_right _ _) b_body
  have b_bE : M.cAll b (M.cNeg (M.cAll y D2)) ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (M.le_cNeg _) b_C2
  have b_E2 : M.cAll y D2 ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (M.le_cEx_body b _) b_bE
  have b_D1 : D1 ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (M.le_cAll_body y D1) b_C1
  have b_D2 : D2 ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (M.le_cAll_body y D2) b_E2
  have b_exφ : M.cEx z φ ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (by rw [hD1]; exact M.le_cImp_right _ _) b_D1
  have b_exψ : M.cEx z ψ ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (by rw [hD2]; exact M.le_cImp_right _ _) b_D2
  have b_zφ : M.cAll z (M.cNeg φ) ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (M.le_cNeg _) b_exφ
  have b_zψ : M.cAll z (M.cNeg ψ) ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (M.le_cNeg _) b_exψ
  have b_φ : φ ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (M.le_cEx_body z φ) b_zφ
  have b_a : a ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := M.le_cAll_var a _
  have b_y : y ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (M.le_cAll_var y D1) b_C1
  have b_b : b ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (M.le_cAll_var b _) b_bE
  have b_z : z ≤ (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2)))) := le_trans (M.le_cAll_var z _) b_zφ
  rw [hunf, M.hier_all_ex hd]
  refine ⟨hα, fun A hA => ?_⟩
  obtain ⟨t1, hag1⟩ := M.exists_upd hd hA t a.1 (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2))))
  refine ⟨t1, hag1, ?_⟩
  have vA1 : M.ValRaw P th io M.nat Nt j.1 d κ t1 a.1 A := M.agree_same hag1 b_a
  rw [M.hier_imp hd hα]
  intro hC1
  have hC1' := ((M.hier_all hd y D1 t1).mp hC1).2
  have hyp : ∀ y0, M.InNRaw P th io M.nat j.1 κ y0 → M.EpsStarRaw P th io M.nat j.1 tp F y0 A → ∀ t1', M.AgreeRaw P th io M.nat Nt j.1 d M.adG κ t1 t1' y.1 y0 φ.1 →
      ∃ z0, M.InNRaw P th io M.nat j.1 κ z0 ∧ M.TrueUpdR P th io M.nat Nt j.1 d M.adG F κ φ.1 z.1 t1' z0 := by
    intro y0 hy0 hy0A t1' hag'
    obtain ⟨t'', hag''⟩ := M.exists_upd hd hy0 t1 y.1 (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2))))
    have h1 := hC1' y0 t'' hy0 (M.agree_mono hag'' b_C1)
    rw [hD1, M.hier_imp hd hα] at h1
    have vy : M.ValRaw P th io M.nat Nt j.1 d κ t'' y.1 y0 := M.agree_same hag'' b_y
    have vA : M.ValRaw P th io M.nat Nt j.1 d κ t'' a.1 A := M.agree_other hag'' b_a hay vA1
    have h2 := h1 ((M.rel_val hd y a hα vy vA).mpr hy0A)
    obtain ⟨z0, hz0, t3, hag3, htr3⟩ := (M.hier_ex hd hα z φ t'').mp h2
    refine ⟨z0, hz0, ?_⟩
    have tu'' : M.TrueUpdR P th io M.nat Nt j.1 d M.adG F κ φ.1 z.1 t'' z0 :=
      (M.trueUpd_iff hd φ z (M.agree_mono hag3 (M.le_cEx_body z φ))).mpr htr3
    refine (M.tu_coin_eq hd φ z hα hz0 (fun i hi hne e he => ?_)).mp tu''
    by_cases eiy : i = y
    · have hyφ : y ≤ φ := by rw [← eiy]; exact hi
      rw [eiy] at he ⊢
      rw [M.val_unique hd he vy]
      exact M.agree_same hag' hyφ
    · exact M.agree_other hag' hi eiy ((M.agree_val_ne hag'' (le_trans hi b_φ) eiy).mp he)
  obtain ⟨γ, hγκ, hγne, hcoll⟩ := M.next_coll hd hPr hq hNu hSg hκ hκσ' neκ hσ'δ neσ' φ y z hA hyp
  obtain ⟨B0, hB0, hB0m⟩ := M.level_mem hd hγκ hγne
  rw [M.hier_ex hd hα]
  obtain ⟨t2, hag2⟩ := M.exists_upd hd hB0 t1 b.1 (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2))))
  refine ⟨B0, hB0, t2, M.agree_mono hag2 b_bE, ?_⟩
  have vB2 : M.ValRaw P th io M.nat Nt j.1 d κ t2 b.1 B0 := M.agree_same hag2 b_b
  have vA2 : M.ValRaw P th io M.nat Nt j.1 d κ t2 a.1 A := M.agree_other hag2 b_a hab vA1
  rw [M.hier_all_ex hd]
  refine ⟨hα, fun y0 hy0 => ?_⟩
  obtain ⟨t3, hag3⟩ := M.exists_upd hd hy0 t2 y.1 (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2))))
  refine ⟨t3, M.agree_mono hag3 b_E2, ?_⟩
  have vy3 : M.ValRaw P th io M.nat Nt j.1 d κ t3 y.1 y0 := M.agree_same hag3 b_y
  have vA3 : M.ValRaw P th io M.nat Nt j.1 d κ t3 a.1 A := M.agree_other hag3 b_a hay vA2
  have vB3 : M.ValRaw P th io M.nat Nt j.1 d κ t3 b.1 B0 := M.agree_other hag3 b_b hby vB2
  rw [hD2, M.hier_imp hd hα, M.rel_val hd y a hα vy3 vA3]
  intro hy0A
  obtain ⟨t1', hag1'⟩ := M.exists_upd hd hy0 t1 y.1 φ
  obtain ⟨z0, hz0γ, tu1'⟩ := hcoll y0 hy0 hy0A t1' hag1'
  have hz0 : M.InNRaw P th io M.nat j.1 κ z0 := M.inN_mono hd hz0γ hγκ
  rw [M.hier_ex hd hα]
  obtain ⟨t4, hag4⟩ := M.exists_upd hd hz0 t3 z.1 (M.cAll a (M.cImp (M.cAll y D1) (M.cEx b (M.cAll y D2))))
  refine ⟨z0, hz0, t4, M.agree_mono hag4 b_zψ, ?_⟩
  have vz4 : M.ValRaw P th io M.nat Nt j.1 d κ t4 z.1 z0 := M.agree_same hag4 b_z
  have vB4 : M.ValRaw P th io M.nat Nt j.1 d κ t4 b.1 B0 := M.agree_other hag4 b_b hbz vB3
  rw [hψ, M.hier_and hd]
  have tu3 : M.TrueUpdR P th io M.nat Nt j.1 d M.adG F κ φ.1 z.1 t3 z0 := by
    refine (M.tu_coin_eq hd φ z hα hz0 (fun i hi hne e he => ?_)).mp tu1'
    by_cases eiy : i = y
    · have hyφ : y ≤ φ := by rw [← eiy]; exact hi
      rw [eiy] at he ⊢
      rw [M.val_unique hd he (M.agree_same hag1' hyφ)]
      exact vy3
    · have h1 : M.ValRaw P th io M.nat Nt j.1 d κ t1 i.1 e := (M.agree_val_ne hag1' hi eiy).mp he
      have hib : i ≠ b := fun e' => M.not_succ_le φ (le_trans hφb (by rw [← e']; exact hi))
      exact M.agree_other hag3 (le_trans hi b_φ) eiy (M.agree_other hag2 (le_trans hi b_φ) hib h1)
  exact ⟨hα, (M.rel_val hd z b hα vz4 vB4).mpr ⟨z0, M.inN_refl hd hz0, (hB0m z0).mpr hz0γ⟩,
    (M.trueUpd_iff hd φ z (M.agree_mono hag4 b_φ)).mp tu3⟩

end coll3
/-! ## The canonical order is a well-ordering, as coded sentences -/

/-- `∀x∀y (x <* y ∨ (x ≈ y ∨ y <* x))`. -/
noncomputable def cWLin (x y z : M.Num) : M.Num :=
  M.cAll x (M.cAll y (M.cOr (M.cRel 2 x y) (M.cOr (M.cEq z x y) (M.cRel 2 y x))))

/-- `∀x ¬ x <* x`. -/
noncomputable def cWIrr (x : M.Num) : M.Num := M.cAll x (M.cNeg (M.cRel 2 x x))

/-- `∀x∀y∀z (x <* y → (y <* z → x <* z))`. -/
noncomputable def cWTrans (x y z : M.Num) : M.Num :=
  M.cAll x (M.cAll y (M.cAll z (M.cImp (M.cRel 2 x y) (M.cImp (M.cRel 2 y z) (M.cRel 2 x z)))))

/-- `∀x∀y (x ≈ y → ∀w ((x <* w → y <* w) ∧ (w <* x → w <* y)))`. -/
noncomputable def cWCong (x y z w : M.Num) : M.Num :=
  M.cAll x (M.cAll y (M.cImp (M.cEq z x y) (M.cAll w (M.cAnd (M.cImp (M.cRel 2 x w) (M.cRel 2 y w))
    (M.cImp (M.cRel 2 w x) (M.cRel 2 w y))))))

/-- `∀a (∃x x ε a → ∃x (x ε a ∧ ∀y (y ε a → ¬ y <* x)))`: every set that has a member has a
least member. -/
noncomputable def cWLeast (a x y : M.Num) : M.Num :=
  M.cAll a (M.cImp (M.cEx x (M.cRel 0 x a))
    (M.cEx x (M.cAnd (M.cRel 0 x a)
      (M.cAll y (M.cImp (M.cRel 0 y a) (M.cNeg (M.cRel 2 y x)))))))

section wo1

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **The canonical order is total**, as a coded sentence true at every stage. -/
theorem hier_wlin (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    {α : V} (hα : M.mem (M.op α α) th) (x y z : M.Num) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) (t : V) :
    M.TrueAt P io F j.1 α (M.cWLin x y z) t := by
  have hunf : M.cWLin x y z = M.cAll x (M.cAll y (M.cOr (M.cRel 2 x y)
    (M.cOr (M.cEq z x y) (M.cRel 2 y x)))) := rfl
  rw [hunf]
  refine (M.hier_all hd x _ t).mpr ⟨hα, fun X t1 hX hag1 => ?_⟩
  refine (M.hier_all hd y _ t1).mpr ⟨hα, fun Y t2 hY hag2 => ?_⟩
  have vY : M.ValRaw P th io M.nat Nt j.1 d α t2 y.1 Y := M.agree_same hag2 (M.le_cAll_var y _)
  have vX : M.ValRaw P th io M.nat Nt j.1 d α t2 x.1 X := M.agree_other hag2
    (le_trans (le_trans (M.le_cRel_left 2 x y) (M.le_cOr_left _ _)) (M.le_cAll_body y _)) hxy
    (M.agree_same hag1 (M.le_cAll_var x _))
  rw [M.hier_or hd hα, M.hier_or hd hα, M.hier_lt hd hPr, M.hier_lt hd hPr,
    M.hier_eq_sim hd hα z x y hzx hzy vX vY hX hY]
  rcases M.lt_tri hd hPr (M.inN_refl hd hX) (M.inN_refl hd hY) with h | h | h
  · exact Or.inl ⟨hα, X, Y, vX, vY, hX, hY, h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hα, Y, X, vY, vX, hY, hX, h⟩)

/-- **The canonical order is irreflexive.** -/
theorem hier_wirr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    {α : V} (hα : M.mem (M.op α α) th) (x : M.Num) (t : V) : M.TrueAt P io F j.1 α (M.cWIrr x) t := by
  have hunf : M.cWIrr x = M.cAll x (M.cNeg (M.cRel 2 x x)) := rfl
  rw [hunf]
  refine (M.hier_all hd x _ t).mpr ⟨hα, fun X t1 hX hag1 => ?_⟩
  have vX : M.ValRaw P th io M.nat Nt j.1 d α t1 x.1 X := M.agree_same hag1 (M.le_cAll_var x _)
  rw [M.hier_neg hd, M.hier_lt hd hPr]
  refine ⟨hα, ?_⟩
  rintro ⟨-, a, b, va, vb, -, -, hlt⟩
  rw [M.val_unique hd va vX, M.val_unique hd vb vX] at hlt
  exact M.lt_irrefl hd (M.inN_refl hd hX) hlt

/-- **The canonical order is transitive.** -/
theorem hier_wtrans (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    {α : V} (hα : M.mem (M.op α α) th) (x y z : M.Num) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (t : V) :
    M.TrueAt P io F j.1 α (M.cWTrans x y z) t := by
  have hunf : M.cWTrans x y z = M.cAll x (M.cAll y (M.cAll z (M.cImp (M.cRel 2 x y)
    (M.cImp (M.cRel 2 y z) (M.cRel 2 x z))))) := rfl
  have bx3 : x ≤ M.cAll z (M.cImp (M.cRel 2 x y) (M.cImp (M.cRel 2 y z) (M.cRel 2 x z))) :=
    le_trans (le_trans (M.le_cRel_left 2 x y) (M.le_cImp_left _ _)) (M.le_cAll_body z _)
  have by3 : y ≤ M.cAll z (M.cImp (M.cRel 2 x y) (M.cImp (M.cRel 2 y z) (M.cRel 2 x z))) :=
    le_trans (le_trans (M.le_cRel_right 2 x y) (M.le_cImp_left _ _)) (M.le_cAll_body z _)
  rw [hunf]
  refine (M.hier_all hd x _ t).mpr ⟨hα, fun X t1 hX hag1 => ?_⟩
  refine (M.hier_all hd y _ t1).mpr ⟨hα, fun Y t2 hY hag2 => ?_⟩
  refine (M.hier_all hd z _ t2).mpr ⟨hα, fun Z t3 hZ hag3 => ?_⟩
  have vZ : M.ValRaw P th io M.nat Nt j.1 d α t3 z.1 Z := M.agree_same hag3 (M.le_cAll_var z _)
  have vY : M.ValRaw P th io M.nat Nt j.1 d α t3 y.1 Y := M.agree_other hag3 by3 hyz (M.agree_same hag2 (M.le_cAll_var y _))
  have vX : M.ValRaw P th io M.nat Nt j.1 d α t3 x.1 X := M.agree_other hag3 bx3 hxz
    (M.agree_other hag2 (le_trans bx3 (M.le_cAll_body y _)) hxy
      (M.agree_same hag1 (M.le_cAll_var x _)))
  rw [M.hier_imp hd hα, M.hier_imp hd hα, M.hier_lt hd hPr, M.hier_lt hd hPr, M.hier_lt hd hPr]
  rintro ⟨-, a, b, va, vb, -, -, h1⟩ ⟨-, b', c, vb', vc, -, -, h2⟩
  rw [M.val_unique hd va vX, M.val_unique hd vb vY] at h1
  rw [M.val_unique hd vb' vY, M.val_unique hd vc vZ] at h2
  exact ⟨hα, X, Z, vX, vZ, hX, hZ, M.lt_trans' hd hPr h1 h2⟩

/-- **The canonical order respects "have the same members".** -/
theorem hier_wcong (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    {α : V} (hα : M.mem (M.op α α) th) (x y z w : M.Num) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) (hxw : x ≠ w)
    (hyw : y ≠ w) (t : V) : M.TrueAt P io F j.1 α (M.cWCong x y z w) t := by
  have hunf : M.cWCong x y z w = M.cAll x (M.cAll y (M.cImp (M.cEq z x y) (M.cAll w (M.cAnd
    (M.cImp (M.cRel 2 x w) (M.cRel 2 y w)) (M.cImp (M.cRel 2 w x) (M.cRel 2 w y)))))) := rfl
  rw [hunf]
  refine (M.hier_all hd x _ t).mpr ⟨hα, fun X t1 hX hag1 => ?_⟩
  refine (M.hier_all hd y _ t1).mpr ⟨hα, fun Y t2 hY hag2 => ?_⟩
  have vY : M.ValRaw P th io M.nat Nt j.1 d α t2 y.1 Y := M.agree_same hag2 (M.le_cAll_var y _)
  have vX : M.ValRaw P th io M.nat Nt j.1 d α t2 x.1 X := M.agree_other hag2
    (le_trans (le_trans (M.le_cEq_left z x y) (M.le_cImp_left _ _)) (M.le_cAll_body y _)) hxy
    (M.agree_same hag1 (M.le_cAll_var x _))
  rw [M.hier_imp hd hα, M.hier_eq_sim hd hα z x y hzx hzy vX vY hX hY]
  intro hs
  refine (M.hier_all hd w _ t2).mpr ⟨hα, fun W t3 hW hag3 => ?_⟩
  have vW : M.ValRaw P th io M.nat Nt j.1 d α t3 w.1 W := M.agree_same hag3 (M.le_cAll_var w _)
  have vX3 : M.ValRaw P th io M.nat Nt j.1 d α t3 x.1 X := M.agree_other hag3
    (le_trans (le_trans (le_trans (M.le_cRel_left 2 x w) (M.le_cImp_left _ _)) (M.le_cAnd_left _ _))
      (M.le_cAll_body w _)) hxw vX
  have vY3 : M.ValRaw P th io M.nat Nt j.1 d α t3 y.1 Y := M.agree_other hag3
    (le_trans (le_trans (le_trans (M.le_cRel_left 2 y w) (M.le_cImp_right _ _)) (M.le_cAnd_left _ _))
      (M.le_cAll_body w _)) hyw vY
  rw [M.hier_and hd, M.hier_imp hd hα, M.hier_imp hd hα, M.hier_lt hd hPr, M.hier_lt hd hPr,
    M.hier_lt hd hPr, M.hier_lt hd hPr]
  refine ⟨hα, ?_, ?_⟩
  · rintro ⟨-, a, b, va, vb, -, -, h1⟩
    rw [M.val_unique hd va vX3, M.val_unique hd vb vW] at h1
    exact ⟨hα, Y, W, vY3, vW, hY, hW, M.lt_congr hd hs (M.inN_refl hd hW) h1⟩
  · rintro ⟨-, a, b, va, vb, -, -, h1⟩
    rw [M.val_unique hd va vW, M.val_unique hd vb vX3] at h1
    exact ⟨hα, W, Y, vW, vY3, hW, hY, M.lt_congr hd (M.inN_refl hd hW) hs h1⟩

/-- **Every set that has a member has a least member in the canonical order**, as a coded
sentence true at every stage. -/
theorem hier_wleast (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    {α : V} (hα : M.mem (M.op α α) th) (a x y : M.Num) (hax : a ≠ x) (hxy : x ≠ y) (hay : a ≠ y) (t : V) :
    M.TrueAt P io F j.1 α (M.cWLeast a x y) t := by
  have hunf : M.cWLeast a x y = M.cAll a (M.cImp (M.cEx x (M.cRel 0 x a))
    (M.cEx x (M.cAnd (M.cRel 0 x a)
      (M.cAll y (M.cImp (M.cRel 0 y a) (M.cNeg (M.cRel 2 y x))))))) := rfl
  have hx3 : x ≤ M.cAll y (M.cImp (M.cRel 0 y a) (M.cNeg (M.cRel 2 y x))) :=
    le_trans (M.le_cRel_right 2 y x)
      (le_trans (M.le_cNeg _) (le_trans (M.le_cImp_right _ _) (M.le_cAll_body y _)))
  have ha3 : a ≤ M.cAll y (M.cImp (M.cRel 0 y a) (M.cNeg (M.cRel 2 y x))) :=
    le_trans (M.le_cRel_right 0 y a) (le_trans (M.le_cImp_left _ _) (M.le_cAll_body y _))
  rw [hunf]
  refine (M.hier_all hd a _ t).mpr ⟨hα, fun A t1 hA hag1 => ?_⟩
  have ka1 := M.agree_same hag1 (M.le_cAll_var a _)
  rw [M.hier_imp hd hα]
  intro hex
  obtain ⟨X0, hX0, t', hag', htr'⟩ := (M.hier_ex hd hα x _ t1).mp hex
  have kx' := M.agree_same hag' (M.le_cEx_var x _)
  have ka' := M.agree_other hag' (le_trans (M.le_cRel_right 0 x a) (M.le_cEx_body x _)) hax ka1
  have hX0A := (M.rel_val hd x a hα kx' ka').mp htr'
  obtain ⟨S, -, hS0⟩ := M.comp (σW [(6, 5), (20, 7), (22, 5), (24, 5), (27, 3)]) epsStarFml 70
    rfl (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th)
      24 io) 25 j.1) 27 M.nat) 73 A)
  have hS : ∀ z, M.mem z S ↔ M.EpsStarRaw P th io M.nat j.1 tp F z A := by
    intro z
    rw [hS0 z]
    simp [M.sat_epsStarFml, Function.update_apply]
  obtain ⟨a1, ha1S, ha1, hmin⟩ := M.lt_least hd hPr S ⟨X0, (hS X0).mpr hX0A, M.inN_refl hd hX0⟩
  obtain ⟨b', hb'N, hsb, heb'⟩ := M.epsStar_rep hd hA ((hS a1).mp ha1S)
  rw [M.hier_ex hd hα]
  obtain ⟨t2, hag2⟩ := M.exists_upd hd hb'N t1 x.1 (M.cAll x (M.cNeg (M.cAnd (M.cRel 0 x a)
    (M.cAll y (M.cImp (M.cRel 0 y a) (M.cNeg (M.cRel 2 y x)))))))
  refine ⟨b', hb'N, t2, hag2, ?_⟩
  have kx2 := M.agree_same hag2 (M.le_cAll_var x _)
  have ka2 := M.agree_other hag2
    (le_trans (le_trans (M.le_cRel_right 0 x a) (M.le_cAnd_left _ _)) (M.le_cEx_body x _))
    hax ka1
  rw [M.hier_and hd]
  refine ⟨hα, (M.rel_val hd x a hα kx2 ka2).mpr ⟨b', M.inN_refl hd hb'N, heb'⟩, ?_⟩
  refine (M.hier_all hd y _ t2).mpr ⟨hα, fun Y t3 hY hag3 => ?_⟩
  have ky3 := M.agree_same hag3 (M.le_cAll_var y _)
  have kx3 := M.agree_other hag3 hx3 hxy kx2
  have ka3 := M.agree_other hag3 ha3 hay ka2
  rw [M.hier_imp hd hα, M.rel_val hd y a hα ky3 ka3, M.hier_neg hd, M.hier_lt hd hPr]
  intro hYA
  refine ⟨hα, ?_⟩
  rintro ⟨-, c1, c2, v1, v2, -, -, hlt⟩
  rw [M.val_unique hd v1 ky3, M.val_unique hd v2 kx3] at hlt
  exact hmin Y ((hS Y).mpr hYA) (M.lt_congr hd (M.epsStar_left hd hYA) (M.sim_symm hd hsb) hlt)

end wo1
/-! ## The sequence of stages -/

theorem muG_iff (a b c : M.Num) : M.mem (M.trip a.1 b.1 c.1) M.muG ↔ a * b = c := by
  constructor
  · intro h
    exact Subtype.ext (M.graph₂_val M.muG_spec h).symm
  · intro h
    exact (M.muG_spec _ _ _).mpr ⟨a, b, rfl, rfl, by rw [← h]; rfl⟩

theorem muG_num {a b : M.Num} {c : V} (h : M.mem (M.trip a.1 b.1 c) M.muG) : c = (a * b).1 :=
  M.graph₂_val M.muG_spec h

theorem mul_three_le {k m1 : M.Num} (h : k + 1 ≤ m1) : 3 * k + 1 + 1 + 1 ≤ 3 * m1 := by
  obtain ⟨c, hc⟩ := M.le_def.mp h
  exact M.le_def.mpr ⟨3 * c, by rw [← hc]; ring⟩

/-- The statement proved by induction on `k` (name `400`) for the sequence of stages. -/
def seqFml : Fml :=
  Fml.imp (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 400 84 396))) (Fml.ex 420 (Fml.ex 421 (Fml.ex
    422 (.and (Fml.ex 423 (Fml.ex 424 (.and (fApp4 20 25 272 161 423) (.and (fApp4 20 25 272 423
    424) (fApp 420 10 424))))) (.and (.all 430 (.all 431 (.all 432 (Fml.imp (fApp 420 430 431)
    (Fml.imp (fApp 420 430 432) (.eq 431 432)))))) (.and (.all 430 (.all 431 (Fml.imp (fApp 420
    430 431) (.and (.mem 430 27) (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 430 84 400))))))) (.and
    (.all 430 (.all 433 (.all 431 (.all 432 (.all 434 (.all 435 (.all 436 (.all 437 (Fml.imp
    (fApp3 28 430 11 433) (Fml.imp (fApp 420 430 431) (Fml.imp (fApp 420 433 432) (Fml.imp
    (fApp4 20 25 434 435 431) (Fml.imp (fApp4 20 25 436 437 432) (.and (.and (fApp 22 436 436)
    (.and (.neg (Fml.ex 446 (Fml.ex 447 (.and (fApp 22 436 446) (Fml.ex 448 (.and (fApp4 20 25
    434 447 448) (fApp 164 446 448))))))) (.all 445 (Fml.imp (fApp 22 445 436) (Fml.imp (.neg
    (.eq 445 436)) (Fml.ex 446 (Fml.ex 447 (.and (fApp 22 445 446) (Fml.ex 448 (.and (fApp4 20
    25 434 447 448) (fApp 164 446 448))))))))))) (Fml.ex 438 (Fml.ex 439 (Fml.ex 440 (.and
    (fApp4 20 25 435 435 438) (.and (fApp4 20 25 436 440 437) (.and (fApp4 20 25 439 438 440)
    (fApp 24 449 439))))))))))))))))))))) (.and (.all 430 (Fml.imp (.mem 430 27) (Fml.imp
    (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 430 84 400))) (Fml.ex 431 (Fml.ex 434 (Fml.ex 435
    (.and (fApp 420 430 431) (fApp4 20 25 434 435 431)))))))) (Fml.ex 441 (Fml.ex 442 (Fml.ex
    443 (.and (fApp 420 400 443) (.and (fApp4 20 25 441 442 443) (.and (fApp3 29 13 400 422)
    (.and (.all 444 (Fml.imp (fApp 22 444 441) (Fml.imp (.neg (.eq 444 441)) (Fml.ex 450 (fApp
    421 444 450))))) (.and (.all 444 (.all 450 (Fml.imp (fApp 421 444 450) (.and (fApp 22 444
    441) (.and (.neg (.eq 444 441)) (fApp 393 422 450)))))) (.and (.all 444 (.all 451 (.all 450
    (Fml.imp (fApp 421 444 450) (Fml.imp (fApp 421 451 450) (.eq 444 451)))))) (.all 430 (.all
    431 (.all 434 (.all 435 (Fml.imp (fApp 420 430 431) (Fml.imp (fApp4 20 25 434 435 431) (fApp
    22 434 441))))))))))))))))))))))))

/-- **The statement proved by induction for the sequence of stages.** If `k ≤ m₁`, there is a
set `W` that assigns to each `i ≤ k` the pair of a stage `νᵢ` and a name `Pⁱ`: `ν₀ = l` and
`P⁰` is the ordinal name of `l`; `νᵢ₊₁` is the least stage that is not `νᵢ`-small, and `Pⁱ⁺¹` is
the name of rank `νᵢ₊₁` given by the formula `v₀ ⊆ v₁` with the parameter `Pⁱ`; the stages
below `ν_k` map one-to-one into the rung `3k`; and every `νᵢ` is at most `ν_k`. -/
def SeqR (R P th io Sg qo nat ad mu z0 o1 three csub l : V) (j : M.Num) (m1 k : V) : Prop :=
  (∃ x, M.mem x nat ∧ M.mem (M.trip k x m1) ad) →
  ∃ W g y,
    (∃ o y0, M.mem (M.quad j.1 l qo o) P ∧ M.mem (M.quad j.1 l o y0) P ∧ M.mem (M.op z0 y0) W) ∧
    (∀ i y1 y2, M.mem (M.op i y1) W → M.mem (M.op i y2) W → y1 = y2) ∧
    (∀ i y1, M.mem (M.op i y1) W → M.mem i nat ∧ ∃ x, M.mem x nat ∧ M.mem (M.trip i x k) ad) ∧
    (∀ i i' y1 y2 ξ p ξ' p', M.mem (M.trip i o1 i') ad → M.mem (M.op i y1) W →
      M.mem (M.op i' y2) W → M.mem (M.quad j.1 ξ p y1) P → M.mem (M.quad j.1 ξ' p' y2) P →
      M.IsNext P th Sg j ξ ξ' ∧ ∃ u f q, M.mem (M.quad j.1 p p u) P ∧ M.mem (M.quad j.1 ξ' q p') P ∧
        M.mem (M.quad j.1 f u q) P ∧ M.mem (M.op csub f) io) ∧
    (∀ i, M.mem i nat → (∃ x, M.mem x nat ∧ M.mem (M.trip i x k) ad) →
      ∃ y1 ξ p, M.mem (M.op i y1) W ∧ M.mem (M.quad j.1 ξ p y1) P) ∧
    ∃ ν p yk, M.mem (M.op k yk) W ∧ M.mem (M.quad j.1 ν p yk) P ∧ M.mem (M.trip three k y) mu ∧
      (∀ β, M.mem (M.op β ν) th → ¬ β = ν → ∃ a, M.mem (M.op β a) g) ∧
      (∀ β a, M.mem (M.op β a) g → M.mem (M.op β ν) th ∧ ¬ β = ν ∧ M.mem (M.op y a) R) ∧
      (∀ β β' a, M.mem (M.op β a) g → M.mem (M.op β' a) g → β = β') ∧
      ∀ i y1 ξ p1, M.mem (M.op i y1) W → M.mem (M.quad j.1 ξ p1 y1) P → M.mem (M.op ξ ν) th

section seq1

variable {R E z S P th io Nt nle p F d tp qo Nu Pr Sg : V} {n j : M.Num}
variable {q1 : V}

/-- **The sequence of stages exists.** By induction on `k`, using `next_exists` at each step. -/
theorem stage_seq_raw (h : M.IsLadder R E z S n) (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr n j)
    (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    {L m1 : M.Num} (hL : L ≤ n) (hm : 3 * m1 ≤ L)
    (hlong : ∀ w, M.IsWO w →
      (∀ a b, M.mem (M.op a b) w → M.mem (M.op L.1 a) R ∧ M.mem (M.op L.1 b) R) →
      M.Emb w th ∧ ¬ M.Emb th w)
    (hunb : ∀ e, M.mem (M.op e e) th → ∃ e', M.mem (M.op e e') th ∧ e ≠ e')
    {l o g0 : V} (hl : M.mem (M.op l l) th) (ho : M.mem (M.quad j.1 l qo o) P)
    (g0_tot : ∀ β, M.mem (M.op β l) th → β ≠ l → ∃ a, M.mem (M.op β a) g0)
    (g0_dom : ∀ β a, M.mem (M.op β a) g0 → M.mem (M.op β l) th ∧ β ≠ l ∧
      M.mem (M.op (0 : M.Num).1 a) R)
    (g0_inj : ∀ β β' a, M.mem (M.op β a) g0 → M.mem (M.op β' a) g0 → β = β') (k : M.Num) :
    M.SeqR R P th io Sg qo M.nat M.adG M.muG (0 : M.Num).1 (1 : M.Num).1 (3 : M.Num).1 (M.cBAll 2 0 (M.cRel 0 2 1)).1 l j m1.1 k.1 := by
  have hsat : ∀ k : M.Num, Sat M.mem M.isSet seqFml (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 10 (0 : M.Num).1) 11 (1 : M.Num).1) 13 (3 : M.Num).1) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 28 M.adG) 29 M.muG) 161 qo) 164 Sg) 272 l) 393 R) 396 m1.1) 449 (M.cBAll 2 0 (M.cRel 0 2 1)).1) 400 k.1) ↔
      M.SeqR R P th io Sg qo M.nat M.adG M.muG (0 : M.Num).1 (1 : M.Num).1 (3 : M.Num).1 (M.cBAll 2 0 (M.cRel 0 2 1)).1 l j m1.1 k.1 := by
    intro k
    simp [seqFml, SeqR, IsNext, Small, Gen, Sat, M.sat_imp, M.sat_ex, M.sat_fApp', M.sat_fApp3',
      M.sat_fApp4', Function.update_apply]
  have key := M.num_ind_fml (σW [(20, 7), (22, 5), (24, 5), (27, 3), (28, 7), (29, 7), (164, 5), (393, 5), (420, 5), (421, 5)]) seqFml 400 rfl (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 10 (0 : M.Num).1) 11 (1 : M.Num).1) 13 (3 : M.Num).1) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 28 M.adG) 29 M.muG) 161 qo) 164 Sg) 272 l) 393 R) 396 m1.1) 449 (M.cBAll 2 0 (M.cRel 0 2 1)).1) ?_ ?_ k
  · exact (hsat k).mp key
  · rw [show M.zero = (0 : M.Num).1 from rfl, hsat 0]
    intro _
    obtain ⟨y0, hy0⟩ := hd.hP.tot j hd.hj l o (hd.th_rung l l hl).1 (hd.hP.dom _ _ _ _ ho).2.2.2
    obtain ⟨W, -, hW0⟩ := M.comp (σW [(0, 4)]) (fPr 0 451 452) 0 rfl
      (Function.update (Function.update (fun _ => dflt) 451 (0 : M.Num).1) 452 y0)
    have hW1 : ∀ q0, M.mem q0 W ↔ q0 = M.op (0 : M.Num).1 y0 := by
      intro q0
      rw [hW0 q0]
      simp [M.sat_fPr', Function.update_apply]
    have hW : ∀ i y1, M.mem (M.op i y1) W ↔ i = (0 : M.Num).1 ∧ y1 = y0 := by
      intro i y1
      rw [hW1]
      constructor
      · intro h1
        exact M.op_inj h1
      · rintro ⟨h1, h2⟩
        rw [h1, h2]
    have hmem0 : M.mem (M.op (0 : M.Num).1 y0) W := (hW _ _).mpr ⟨rfl, rfl⟩
    refine ⟨W, g0, (0 : M.Num).1, ⟨o, y0, ho, hy0, hmem0⟩, fun i y1 y2 h1 h2 => ?_,
      fun i y1 h1 => ?_, fun i i' y1 y2 ξ pp ξ' pp' hs h1 h2 _ _ => ?_, fun i hi hle => ?_,
      l, o, y0, hmem0, hy0, (M.muG_iff 3 0 0).mpr (by ring), g0_tot, g0_dom, g0_inj,
      fun i y1 ξ p1 h1 hq1 => ?_⟩
    · exact ((hW i y1).mp h1).2.trans ((hW i y2).mp h2).2.symm
    · rw [((hW i y1).mp h1).1]
      exact ⟨(0 : M.Num).2, (M.leRaw_iff M.adG_spec 0 0).mpr (le_refl _)⟩
    · exfalso
      have e1 := ((hW i y1).mp h1).1
      have e2 := ((hW i' y2).mp h2).1
      rw [e1] at hs
      have e3 := M.adG_num (a := 0) (b := 1) hs
      rw [e2] at e3
      exact M.not_succ_le 0 (le_of_eq (Subtype.ext e3).symm)
    · have e0 : (⟨i, hi⟩ : M.Num) = 0 :=
        le_antisymm ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ 0).mp hle) zero_le
      have ei : i = (0 : M.Num).1 := congrArg Subtype.val e0
      rw [ei]
      exact ⟨y0, l, o, hmem0, hy0⟩
    · rw [((hW i y1).mp h1).2] at hq1
      rw [(hd.hP.inj _ _ _ _ _ _ hq1 hy0).1]
      exact hl
  · intro k ih
    rw [show M.succ k.1 = (k + 1).1 from (M.val_add_one k).symm, hsat (k + 1)]
    intro hle
    have hk1 : k + 1 ≤ m1 := (M.leRaw_iff M.adG_spec (k + 1) m1).mp hle
    obtain ⟨W, g, y, hA, hB, hC, hD, hF, ν, p0, yk, hkW, hyk, hmu, gt, gd, gi, hG⟩ :=
      (hsat k).mp ih ((M.leRaw_iff M.adG_spec k m1).mpr (le_trans (M.le_add_one k) hk1))
    have ey : y = (3 * k : M.Num).1 := M.muG_num hmu
    rw [ey] at gd
    have hi3 : 3 * k + 1 + 1 + 1 ≤ L := le_trans (M.mul_three_le hk1) hm
    obtain ⟨κ, g', hnext, gt', gd', gi'⟩ := M.next_exists h hd hPr hq hSg hi3 hL hlong gt gd gi
    have hκ := hnext.1
    have hν : M.mem (M.op ν ν) th := hG k.1 yk ν p0 hkW hyk
    obtain ⟨e', he', hne'⟩ := hunb ν hν
    obtain ⟨ν', s1, s2, -, s4⟩ := M.exists_succ_stage hd he' hne'
    obtain ⟨hνκ, hνκne⟩ := M.next_gt hd hq hSg hnext ⟨s1, s2, s4⟩
    have hpR : M.mem (M.op j.1 p0) R := (hd.hP.dom _ _ _ _ hyk).2.2.1
    obtain ⟨u, hu⟩ := hd.hP.tot j hd.hj p0 p0 hpR hpR
    obtain ⟨f, hf⟩ := hd.io_tot (M.cBAll 2 0 (M.cRel 0 2 1))
    obtain ⟨q, hq'⟩ := hd.hP.tot j hd.hj f u (hd.io_dom _ _ hf).2 (hd.hP.dom _ _ _ _ hu).2.2.2
    obtain ⟨p', hp'⟩ := hd.hP.tot j hd.hj κ q (hd.th_rung κ κ hκ).1 (hd.hP.dom _ _ _ _ hq').2.2.2
    obtain ⟨y', hy'⟩ := hd.hP.tot j hd.hj κ p' (hd.th_rung κ κ hκ).1 (hd.hP.dom _ _ _ _ hp').2.2.2
    obtain ⟨W', -, hW0⟩ := M.comp (σW [(0, 4), (420, 5)]) (Fml.or (.mem 0 420) (fPr 0 451 452)) 0 rfl
      (Function.update (Function.update (Function.update (fun _ => dflt) 420 W) 451 (k + 1).1) 452 y')
    have hW1 : ∀ q0, M.mem q0 W' ↔ M.mem q0 W ∨ q0 = M.op (k + 1).1 y' := by
      intro q0
      rw [hW0 q0]
      simp [Sat, M.sat_or, M.sat_fPr', Function.update_apply]
    have hW' : ∀ i y1, M.mem (M.op i y1) W' ↔
        M.mem (M.op i y1) W ∨ (i = (k + 1).1 ∧ y1 = y') := by
      intro i y1
      rw [hW1]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (M.op_inj h1)
      · rintro (h1 | ⟨h1, h2⟩)
        · exact Or.inl h1
        · exact Or.inr (by rw [h1, h2])
    have old_ne : ∀ i y1, M.mem (M.op i y1) W → i ≠ (k + 1).1 := by
      intro i y1 h1 e
      obtain ⟨hi, hle1⟩ := hC i y1 h1
      rw [e] at hle1
      exact M.not_succ_le k ((M.leRaw_iff M.adG_spec (k + 1) k).mp hle1)
    have e3 : (3 * k + 1 + 1 + 1 : M.Num) = 3 * (k + 1) := by ring
    have hnew : M.mem (M.op (k + 1).1 y') W' := (hW' _ _).mpr (Or.inr ⟨rfl, rfl⟩)
    refine ⟨W', g', (3 * (k + 1) : M.Num).1, ?_, fun i y1 y2 h1 h2 => ?_, fun i y1 h1 => ?_,
      fun i i' y1 y2 ξ pp ξ' pp' hs h1 h2 q1' q2' => ?_, fun i hi hle1 => ?_,
      κ, p', y', hnew, hy', (M.muG_iff 3 (k + 1) _).mpr rfl, gt', fun β a hβa => ?_, gi',
      fun i y1 ξ p1 h1 hq1 => ?_⟩
    · obtain ⟨o0, y0, a1, a2, a3⟩ := hA
      exact ⟨o0, y0, a1, a2, (hW' _ _).mpr (Or.inl a3)⟩
    · rcases (hW' i y1).mp h1 with h1 | ⟨e1, e1'⟩
      · rcases (hW' i y2).mp h2 with h2 | ⟨e2, e2'⟩
        · exact hB i y1 y2 h1 h2
        · exact (old_ne i y1 h1 e2).elim
      · rcases (hW' i y2).mp h2 with h2 | ⟨e2, e2'⟩
        · exact (old_ne i y2 h2 e1).elim
        · rw [e1', e2']
    · rcases (hW' i y1).mp h1 with h1 | ⟨e1, -⟩
      · obtain ⟨hi, hle1⟩ := hC i y1 h1
        exact ⟨hi, (M.leRaw_iff M.adG_spec ⟨i, hi⟩ (k + 1)).mpr
          (le_trans ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ k).mp hle1) (M.le_add_one k))⟩
      · rw [e1]
        exact ⟨(k + 1).2, (M.leRaw_iff M.adG_spec (k + 1) (k + 1)).mpr (le_refl _)⟩
    · rcases (hW' i' y2).mp h2 with h2 | ⟨e2, e2'⟩
      · rcases (hW' i y1).mp h1 with h1 | ⟨e1, -⟩
        · exact hD i i' y1 y2 ξ pp ξ' pp' hs h1 h2 q1' q2'
        · exfalso
          rw [e1] at hs
          have ei' := M.adG_num (a := k + 1) (b := 1) hs
          obtain ⟨hi', hle'⟩ := hC i' y2 h2
          rw [ei'] at hle'
          exact M.not_succ_le k (le_trans (M.le_add_one (k + 1))
            ((M.leRaw_iff M.adG_spec (k + 1 + 1) k).mp hle'))
      · rw [e2'] at q2'
        obtain ⟨eξ', ep'⟩ := hd.hP.inj _ _ _ _ _ _ q2' hy'
        rcases (hW' i y1).mp h1 with h1 | ⟨e1, -⟩
        · obtain ⟨hi, -⟩ := hC i y1 h1
          rw [e2] at hs
          have hik : (⟨i, hi⟩ : M.Num) + 1 = k + 1 :=
            Subtype.ext (M.adG_num (a := ⟨i, hi⟩) (b := 1) hs).symm
          have eik : i = k.1 := congrArg Subtype.val (M.add_one_inj hik)
          rw [eik] at h1
          have ey1 : y1 = yk := hB _ _ _ h1 hkW
          rw [ey1] at q1'
          obtain ⟨eξ, ep⟩ := hd.hP.inj _ _ _ _ _ _ q1' hyk
          rw [eξ, eξ', ep, ep']
          exact ⟨hnext, u, f, q, hu, hp', hq', hf⟩
        · exfalso
          rw [e1, e2] at hs
          have e4 := M.adG_num (a := k + 1) (b := 1) hs
          exact M.not_succ_le (k + 1) (le_of_eq (Subtype.ext e4).symm)
    · have hle' := (M.leRaw_iff M.adG_spec ⟨i, hi⟩ (k + 1)).mp hle1
      rcases M.eq_or_succ_le hle' with e | e
      · have ei : i = (k + 1).1 := congrArg Subtype.val e
        rw [ei]
        exact ⟨y', κ, p', hnew, hy'⟩
      · obtain ⟨y1, ξ, pp, h1, h2⟩ := hF i hi
          ((M.leRaw_iff M.adG_spec ⟨i, hi⟩ k).mpr (M.le_of_succ_le_succ e))
        exact ⟨y1, ξ, pp, (hW' _ _).mpr (Or.inl h1), h2⟩
    · obtain ⟨g1, g2, g3⟩ := gd' β a hβa
      exact ⟨g1, g2, by rw [← e3]; exact g3⟩
    · rcases (hW' i y1).mp h1 with h1 | ⟨-, e1'⟩
      · exact hd.hth.trans _ _ _ (hG i y1 ξ p1 h1 hq1) hνκ
      · rw [e1'] at hq1
        rw [(hd.hP.inj _ _ _ _ _ _ hq1 hy').1]
        exact hκ

end seq1
/-! ## The sequence of stages, in usable form; the power set names -/

/-- **A sequence of stages and names.** `W` assigns to each `i ≤ m₁` the pair of a stage `νᵢ`
and a name `Pⁱ`, with `ν₀ = l`, `P⁰` the ordinal name of `l`, each `νᵢ₊₁` the least stage that
is not `νᵢ`-small, each `Pⁱ⁺¹` the name of rank `νᵢ₊₁` given by the formula `v₀ ⊆ v₁` and the
parameter `Pⁱ`, and `κ = ν_{m₁}` the largest of the stages. -/
structure StageSeq (P th io Sg qo W l : V) (j m1 : M.Num) (κ : V) : Prop where
  zero : ∃ o y0, M.mem (M.quad j.1 l qo o) P ∧ M.mem (M.quad j.1 l o y0) P ∧
    M.mem (M.op (0 : M.Num).1 y0) W
  fn : ∀ i y1 y2, M.mem (M.op i y1) W → M.mem (M.op i y2) W → y1 = y2
  idx : ∀ i y1, M.mem (M.op i y1) W → ∃ k : M.Num, k.1 = i ∧ k ≤ m1
  step : ∀ (i : M.Num) (y1 y2 ξ p ξ' p' : V), M.mem (M.op i.1 y1) W → M.mem (M.op (i + 1).1 y2) W →
    M.mem (M.quad j.1 ξ p y1) P → M.mem (M.quad j.1 ξ' p' y2) P →
    M.IsNext P th Sg j ξ ξ' ∧ ∃ u, M.mem (M.quad j.1 p p u) P ∧ M.NameOf P io j p' ξ' (M.cBAll 2 0 (M.cRel 0 2 1)) u
  tot : ∀ i : M.Num, i ≤ m1 → ∃ y1 ξ p, M.mem (M.op i.1 y1) W ∧ M.mem (M.quad j.1 ξ p y1) P
  top : ∃ p yk, M.mem (M.op m1.1 yk) W ∧ M.mem (M.quad j.1 κ p yk) P
  le_top : ∀ i y1 ξ p1, M.mem (M.op i y1) W → M.mem (M.quad j.1 ξ p1 y1) P → M.mem (M.op ξ κ) th

section seq2

variable {R E z S P th io Nt nle p F d tp qo Nu Pr Sg : V} {m j : M.Num}
variable {q1 : V}

theorem exists_stageSeq (h : M.IsLadder R E z S m) (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j)
    (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    {L m1 : M.Num} (hL : L ≤ m) (hm : 3 * m1 ≤ L)
    (hlong : ∀ w, M.IsWO w →
      (∀ a b, M.mem (M.op a b) w → M.mem (M.op L.1 a) R ∧ M.mem (M.op L.1 b) R) →
      M.Emb w th ∧ ¬ M.Emb th w)
    (hunb : ∀ e, M.mem (M.op e e) th → ∃ e', M.mem (M.op e e') th ∧ e ≠ e')
    {l o g0 : V} (hl : M.mem (M.op l l) th) (ho : M.mem (M.quad j.1 l qo o) P)
    (g0_tot : ∀ β, M.mem (M.op β l) th → β ≠ l → ∃ a, M.mem (M.op β a) g0)
    (g0_dom : ∀ β a, M.mem (M.op β a) g0 → M.mem (M.op β l) th ∧ β ≠ l ∧
      M.mem (M.op (0 : M.Num).1 a) R)
    (g0_inj : ∀ β β' a, M.mem (M.op β a) g0 → M.mem (M.op β' a) g0 → β = β') :
    ∃ W κ, M.StageSeq P th io Sg qo W l j m1 κ := by
  obtain ⟨W, g, y, hA, hB, hC, hD, hF, ν, p0, yk, hkW, hyk, hmu, gt, gd, gi, hG⟩ :=
    M.stage_seq_raw h hd hPr hq hSg hL hm hlong hunb hl ho g0_tot g0_dom g0_inj m1
      ((M.leRaw_iff M.adG_spec m1 m1).mpr (le_refl _))
  refine ⟨W, ν, hA, hB, fun i y1 h1 => ?_, fun i y1 y2 ξ pp ξ' pp' h1 h2 q1' q2' => ?_,
    fun i hi => hF i.1 i.2 ((M.leRaw_iff M.adG_spec i m1).mpr hi), ⟨p0, yk, hkW, hyk⟩, hG⟩
  · obtain ⟨hi, hle⟩ := hC i y1 h1
    exact ⟨⟨i, hi⟩, rfl, (M.leRaw_iff M.adG_spec ⟨i, hi⟩ m1).mp hle⟩
  · obtain ⟨hn, u, f, q, hu, hp', hq', hf⟩ := hD i.1 (i + 1).1 y1 y2 ξ pp ξ' pp'
      ((M.adG_iff i 1 (i + 1)).mpr rfl) h1 h2 q1' q2'
    exact ⟨hn, u, hu, f, q, hp', hq', hf⟩

/-- **The members of the name given by `v₀ ⊆ v₁`.** -/
theorem sub_name_mem (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ξ' p0 p' u : V}
    (hξ' : M.mem (M.op ξ' ξ') th) (hn : M.NameOf P io j p' ξ' (M.cBAll 2 0 (M.cRel 0 2 1)) u)
    (hu : M.mem (M.quad j.1 p0 p0 u) P) (hp : M.InNRaw P th io M.nat j.1 ξ' p0) (a : V) :
    M.EpsRaw P th io M.nat j.1 F a p' ↔ M.InNRaw P th io M.nat j.1 ξ' a ∧ ∀ e, M.InNRaw P th io M.nat j.1 ξ' e → M.EpsStarRaw P th io M.nat j.1 tp F e a → M.EpsStarRaw P th io M.nat j.1 tp F e p0 := by
  obtain ⟨f, q, h1, h2, h3⟩ := hn
  rw [M.eps_iff hd h1 h2 h3 a]
  have b1 : (1 : M.Num) ≤ (M.cBAll 2 0 (M.cRel 0 2 1)) :=
    le_trans (M.le_cRel_right 0 2 1) (le_trans (M.le_add_one _) (M.cBAll_bounds 2 0 _).2.2)
  have vals : ∀ s, M.mem (M.quad j.1 a u s) P → M.InNRaw P th io M.nat j.1 ξ' a →
      M.ValRaw P th io M.nat Nt j.1 d ξ' s (0 : M.Num).1 a ∧ M.ValRaw P th io M.nat Nt j.1 d ξ' s (1 : M.Num).1 p0 := by
    intro s hs ha
    refine ⟨M.val_cons_zero hd hs ha, ?_⟩
    have h4 := (M.val_cons_succ hd hs 0 (e := p0)).mpr (M.val_cons_zero hd hu hp)
    rwa [zero_add] at h4
  constructor
  · rintro ⟨ha, s, hs, htr⟩
    refine ⟨ha, ?_⟩
    obtain ⟨v0, v1⟩ := vals s hs ha
    rw [M.hier_ball_ex hd hξ' 2 0 (M.cRel 0 2 1) M.n20 v0] at htr
    intro e he hea
    obtain ⟨t', hag, htr'⟩ := htr e he hea
    have ve : M.ValRaw P th io M.nat Nt j.1 d ξ' t' (2 : M.Num).1 e := M.agree_same hag (M.cBAll_bounds 2 0 _).1
    have vp : M.ValRaw P th io M.nat Nt j.1 d ξ' t' (1 : M.Num).1 p0 := M.agree_other hag b1 M.n12 v1
    exact (M.rel_val hd 2 1 hξ' ve vp).mp htr'
  · rintro ⟨ha, hall⟩
    obtain ⟨s, hs⟩ := hd.hP.tot j hd.hj a u (M.inN_rung hd ha) (hd.hP.dom _ _ _ _ hu).2.2.2
    refine ⟨ha, s, hs, ?_⟩
    obtain ⟨v0, v1⟩ := vals s hs ha
    rw [M.hier_ball_ex hd hξ' 2 0 (M.cRel 0 2 1) M.n20 v0]
    intro e he hea
    obtain ⟨t', hag⟩ := M.exists_upd hd he s (2 : M.Num).1 (M.cBAll 2 0 (M.cRel 0 2 1))
    refine ⟨t', hag, ?_⟩
    have ve : M.ValRaw P th io M.nat Nt j.1 d ξ' t' (2 : M.Num).1 e := M.agree_same hag (M.cBAll_bounds 2 0 _).1
    have vp : M.ValRaw P th io M.nat Nt j.1 d ξ' t' (1 : M.Num).1 p0 := M.agree_other hag b1 M.n12 v1
    exact (M.rel_val hd 2 1 hξ' ve vp).mpr (hall e he hea)

/-- **The power set at the next stage is the power set in every later level.** Let `ν₁` be the
least stage that is not `ν`-small, `p` a name of rank `ν`, and `p'` the name of rank `ν₁` given
by `v₀ ⊆ v₁` and the parameter `p`. Then for every name `x` of rank below a later stage `κ`
that is not the last: `x` denotes a member of the set denoted by `p'` if and only if every
member of the set denoted by `x` is a member of the set denoted by `p`. -/
theorem pow_of_next (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    {ν ν1 κ δ p0 p' u : V} (hnext : M.IsNext P th Sg j ν ν1) (hκδ : M.mem (M.op κ δ) th)
    (neκ : κ ≠ δ) (hνν1 : M.mem (M.op ν ν1) th) (neν : ν ≠ ν1)
    (rp : M.RankIs P io M.nat j.1 ν p0) (hn : M.NameOf P io j p' ν1 (M.cBAll 2 0 (M.cRel 0 2 1)) u) (hu : M.mem (M.quad j.1 p0 p0 u) P)
    (x : V) (hx : M.InNRaw P th io M.nat j.1 κ x) :
    M.EpsStarRaw P th io M.nat j.1 tp F x p' ↔ ∀ y, M.EpsStarRaw P th io M.nat j.1 tp F y x → M.EpsStarRaw P th io M.nat j.1 tp F y p0 := by
  have hp1 : M.InNRaw P th io M.nat j.1 ν1 p0 := M.rank_inN rp hνν1 neν
  have hν1 := hnext.1
  have hmem := M.sub_name_mem hd hν1 hn hu hp1
  constructor
  · rintro ⟨a, hsa, hea⟩ y hyx
    obtain ⟨ha, hall⟩ := (hmem a).mp hea
    have hya : M.EpsStarRaw P th io M.nat j.1 tp F y a := M.epsStar_congr hd (M.epsStar_left hd hyx) hsa hyx
    obtain ⟨e, he, hsye, hee⟩ := M.epsStar_rep hd ha hya
    have h1 : M.EpsStarRaw P th io M.nat j.1 tp F e p0 := hall e he ⟨e, M.inN_refl hd he, hee⟩
    exact M.epsStar_congr hd (M.sim_symm hd hsye) (M.inN_refl hd hp1) h1
  · intro hall
    obtain ⟨σ, rx, ltσ, neσ⟩ := M.inN_rank hx
    obtain ⟨x', hx', hsx⟩ := M.next_absorb hd hPr hq hNu hSg hnext rx ltσ neσ hκδ neκ hνν1 neν
      (fun y hy => by
        have hyN := M.eps_inN_rank hd rx hy
        obtain ⟨y', hsy, hey'⟩ := hall y ⟨y, M.inN_refl hd hyN, hy⟩
        exact ⟨y', M.eps_inN_rank hd rp hey', hsy⟩)
    refine ⟨x', hsx, (hmem x').mpr ⟨hx', fun e he hex' => ?_⟩⟩
    exact hall e (M.epsStar_congr hd (M.inN_refl hd he) (M.sim_symm hd hsx) hex')

end seq2
/-! ## Facts about the sequence of stages; the numbers; the power set names -/

/-- The sequence `W` has the stage `ξ` and the name `p` at the index `i`. -/
def SAt (P W : V) (j i : M.Num) (ξ p : V) : Prop :=
  ∃ y1, M.mem (M.op i.1 y1) W ∧ M.mem (M.quad j.1 ξ p y1) P

/-- **The numbers of the hierarchy.** `Nm` assigns to each number `i` of the model the ordinal
name of the `i`-th stage; these are, up to "denote the same set", exactly the members of the
set denoted by `ol`, the ordinal name of the first limit stage `l`; the name for `0` denotes
the empty set and the name for `i + 1` denotes the successor of the set denoted by the name
for `i`. -/
structure NumNames (P th io F tp qo Nm ol : V) (j : M.Num) (l : V) : Prop where
  hol : M.mem (M.quad j.1 l qo ol) P
  tot : ∀ i : M.Num, ∃ o, M.mem (M.op i.1 o) Nm
  fn : ∀ i o o', M.mem (M.op i o) Nm → M.mem (M.op i o') Nm → o = o'
  rank : ∀ i o, M.mem (M.op i o) Nm → ∃ ξ, M.RankIs P io M.nat j.1 ξ o ∧ M.mem (M.op ξ l) th ∧ ξ ≠ l
  mem : ∀ i o, M.mem (M.op i o) Nm → M.EpsStarRaw P th io M.nat j.1 tp F o ol
  onto : ∀ x, M.EpsStarRaw P th io M.nat j.1 tp F x ol →
    ∃ (i : M.Num) (o : V), M.mem (M.op i.1 o) Nm ∧ M.SimRaw P j.1 tp F x o
  zero : ∀ o u, M.mem (M.op (0 : M.Num).1 o) Nm → ¬ M.EpsStarRaw P th io M.nat j.1 tp F u o
  succ : ∀ (i : M.Num) (o o' u : V), M.mem (M.op i.1 o) Nm → M.mem (M.op (i + 1).1 o') Nm →
    (M.EpsStarRaw P th io M.nat j.1 tp F u o' ↔
      (M.EpsStarRaw P th io M.nat j.1 tp F u o ∨ M.SimRaw P j.1 tp F u o))
  inj : ∀ (i i' : M.Num) (o o' : V), M.mem (M.op i.1 o) Nm → M.mem (M.op i'.1 o') Nm →
    M.SimRaw P j.1 tp F o o' → i = i'

/-- **The iterated power sets.** `Pw` assigns to each `i < m₁` a name of rank below `κ`; the
name for `0` is `ol`; and the name for `i + 1` denotes the power set of the set denoted by the
name for `i`, in the sense of the level at `κ`. -/
structure PowNames (P th io F tp Pw ol κ : V) (j m1 : M.Num) : Prop where
  zero : 1 ≤ m1 → M.mem (M.op (0 : M.Num).1 ol) Pw
  tot : ∀ i : M.Num, i + 1 ≤ m1 → ∃ p0, M.mem (M.op i.1 p0) Pw
  fn : ∀ i p0 p', M.mem (M.op i p0) Pw → M.mem (M.op i p') Pw → p0 = p'
  dom : ∀ i p0, M.mem (M.op i p0) Pw → ∃ k : M.Num, k.1 = i ∧ k + 1 ≤ m1
  inN : ∀ i p0, M.mem (M.op i p0) Pw → M.InNRaw P th io M.nat j.1 κ p0
  pow : ∀ (i : M.Num) (p0 p' : V), M.mem (M.op i.1 p0) Pw → M.mem (M.op (i + 1).1 p') Pw →
    ∀ x, M.InNRaw P th io M.nat j.1 κ x → (M.EpsStarRaw P th io M.nat j.1 tp F x p' ↔
      ∀ y, M.EpsStarRaw P th io M.nat j.1 tp F y x → M.EpsStarRaw P th io M.nat j.1 tp F y p0)

section seq3

variable {R E z S P th io Nt nle p F d tp qo Nu Pr Sg : V} {m j m1 : M.Num}
variable {q1 W l κ : V}

theorem sat_fun (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (ss : M.StageSeq P th io Sg qo W l j m1 κ)
    {i : M.Num} {ξ p0 ξ' p' : V} (h1 : M.SAt P W j i ξ p0) (h2 : M.SAt P W j i ξ' p') :
    ξ = ξ' ∧ p0 = p' := by
  obtain ⟨y1, a1, a2⟩ := h1
  obtain ⟨y2, b1, b2⟩ := h2
  rw [ss.fn _ _ _ b1 a1] at b2
  exact hd.hP.inj _ _ _ _ _ _ a2 b2

theorem sat_tot (ss : M.StageSeq P th io Sg qo W l j m1 κ) {i : M.Num} (hi : i ≤ m1) : ∃ ξ p0, M.SAt P W j i ξ p0 := by
  obtain ⟨y1, ξ, p0, h1, h2⟩ := ss.tot i hi
  exact ⟨ξ, p0, y1, h1, h2⟩

theorem sat_step (ss : M.StageSeq P th io Sg qo W l j m1 κ) {i : M.Num} {ξ p0 ξ' p' : V} (h1 : M.SAt P W j i ξ p0)
    (h2 : M.SAt P W j (i + 1) ξ' p') :
    M.IsNext P th Sg j ξ ξ' ∧ ∃ u, M.mem (M.quad j.1 p0 p0 u) P ∧ M.NameOf P io j p' ξ' (M.cBAll 2 0 (M.cRel 0 2 1)) u := by
  obtain ⟨y1, a1, a2⟩ := h1
  obtain ⟨y2, b1, b2⟩ := h2
  exact ss.step i y1 y2 ξ p0 ξ' p' a1 b1 a2 b2

theorem sat_le_top (ss : M.StageSeq P th io Sg qo W l j m1 κ) {i : M.Num} {ξ p0 : V} (h1 : M.SAt P W j i ξ p0) : M.mem (M.op ξ κ) th := by
  obtain ⟨y1, a1, a2⟩ := h1
  exact ss.le_top _ _ _ _ a1 a2

theorem sat_idx (ss : M.StageSeq P th io Sg qo W l j m1 κ) {i : M.Num} {ξ p0 : V} (h1 : M.SAt P W j i ξ p0) : i ≤ m1 := by
  obtain ⟨y1, a1, -⟩ := h1
  obtain ⟨k, hk, hle⟩ := ss.idx _ _ a1
  have e : k = i := Subtype.ext hk
  rw [← e]
  exact hle

theorem sat_lt (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) (ss : M.StageSeq P th io Sg qo W l j m1 κ)
    (hunb : ∀ e, M.mem (M.op e e) th → ∃ e', M.mem (M.op e e') th ∧ e ≠ e') {i : M.Num} {ξ p0 ξ' p' : V} (h1 : M.SAt P W j i ξ p0) (h2 : M.SAt P W j (i + 1) ξ' p') :
    M.mem (M.op ξ ξ') th ∧ ξ ≠ ξ' := by
  obtain ⟨hnext, -⟩ := M.sat_step ss h1 h2
  have hξ := (hd.hth.fld _ _ (M.sat_le_top ss h1)).1
  obtain ⟨e', he', hne'⟩ := hunb ξ hξ
  obtain ⟨ν', s1, s2, -, s4⟩ := M.exists_succ_stage hd he' hne'
  exact M.next_gt hd hq hSg hnext ⟨s1, s2, s4⟩

theorem sat_zero (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (ss : M.StageSeq P th io Sg qo W l j m1 κ) {o : V}
    (ho : M.mem (M.quad j.1 l qo o) P) : M.SAt P W j 0 l o := by
  obtain ⟨o0, y0, a1, a2, a3⟩ := ss.zero
  have e : o0 = o := hd.hP.fn _ _ _ _ _ a1 ho
  rw [e] at a2
  exact ⟨y0, a3, a2⟩

theorem sat_rank (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hqo : M.OrdQ P io j d qo) (ss : M.StageSeq P th io Sg qo W l j m1 κ)
    {i : M.Num} {ξ p0 : V} (h1 : M.SAt P W j i ξ p0) : M.RankIs P io M.nat j.1 ξ p0 := by
  rcases M.num_cases i with e0 | ⟨k, ek⟩
  · have ei : i = 0 := e0
    rw [ei] at h1
    obtain ⟨o0, y0, a1, a2, a3⟩ := ss.zero
    obtain ⟨e1, e2⟩ := M.sat_fun hd ss h1 ⟨y0, a3, a2⟩
    rw [e1, e2]
    exact M.ordName_rank hd hqo a1
  · have ei : i = k + 1 := by rw [ek, M.nsucc_eq_add_one]
    rw [ei] at h1
    have hk : k ≤ m1 := le_trans (M.le_add_one k) (M.sat_idx ss h1)
    obtain ⟨ξ0, p1, h0⟩ := M.sat_tot ss hk
    obtain ⟨-, u, -, hn⟩ := M.sat_step ss h0 h1
    exact M.nameOf_rank hn

theorem sat_inN (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) (hqo : M.OrdQ P io j d qo) (ss : M.StageSeq P th io Sg qo W l j m1 κ)
    (hunb : ∀ e, M.mem (M.op e e) th → ∃ e', M.mem (M.op e e') th ∧ e ≠ e') {i : M.Num} {ξ p0 : V} (h1 : M.SAt P W j i ξ p0) (hi : i + 1 ≤ m1) : M.InNRaw P th io M.nat j.1 κ p0 := by
  obtain ⟨ξ', p', h2⟩ := M.sat_tot ss hi
  obtain ⟨lt, ne⟩ := M.sat_lt hd hq hSg ss hunb h1 h2
  have le2 := M.sat_le_top ss h2
  exact M.rank_inN (M.sat_rank hd hqo ss h1) (hd.hth.trans _ _ _ lt le2)
    (M.wo_ne_of_lt_le hd.hth lt ne le2)

/-- The last stage of the sequence is a limit stage. -/
theorem top_lim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j) (hq : M.IsMark P th io Nt d j q1) (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j) (ss : M.StageSeq P th io Sg qo W l j m1 κ) (hm1 : 1 ≤ m1) : M.IsLim th κ := by
  obtain ⟨p1, yk, a1, a2⟩ := ss.top
  obtain ⟨c, hc⟩ := M.le_def.mp hm1
  have e : m1 = c + 1 := by rw [← hc]; ring
  have htop : M.SAt P W j (c + 1) κ p1 := by
    rw [← e]
    exact ⟨yk, a1, a2⟩
  obtain ⟨ξ0, p0', h0⟩ := M.sat_tot ss (i := c) (by rw [e]; exact M.le_add_one c)
  exact M.next_lim hd hPr hq hSg (M.sat_step ss h0 htop).1

/-- **The numbers of the hierarchy exist.** -/
theorem exists_numNames (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hqo : M.OrdQ P io j d qo) {l N : V} (hl : M.IsLim th l)
    (hβ : ∃ β, M.mem (M.op β l) th ∧ β ≠ l)
    (Ntot : ∀ n : M.Num, ∃ ξ, M.mem (M.op n.1 ξ) N)
    (Ndom : ∀ k ξ, M.mem (M.op k ξ) N → M.mem k M.nat ∧ M.mem (M.op ξ l) th ∧ ξ ≠ l)
    (Nfun : ∀ k ξ ξ', M.mem (M.op k ξ) N → M.mem (M.op k ξ') N → ξ = ξ')
    (Nonto : ∀ ξ, M.mem (M.op ξ l) th → ξ ≠ l → ∃ n : M.Num, M.mem (M.op n.1 ξ) N)
    (Nord : ∀ (n n' : M.Num) (ξ ξ' : V), M.mem (M.op n.1 ξ) N → M.mem (M.op n'.1 ξ') N →
      (n ≤ n' ↔ M.mem (M.op ξ ξ') th)) :
    ∃ Nm ol, M.NumNames P th io F tp qo Nm ol j l := by
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
  refine ⟨Nm, ol, hol, fun i => ?_, fun i o o' h1 h2 => ?_, fun i o h1 => ?_, fun i o h1 => ?_,
    fun x hx => ?_, fun o u h1 => ?_, fun i o o' u h1 h2 => ?_, fun i i' o o' h1 h2 hs => ?_⟩
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

/-- **The iterated power sets exist.** -/
theorem exists_powNames (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hPr : M.IsPrec P th io Nt d Pr j)
    (hq : M.IsMark P th io Nt d j q1) (hNu : ∀ k o, ¬ M.mem (M.op k o) Nu)
    (hSg : M.IsSig P th io Nt d tp q1 F Pr Sg j)
    (hqo : M.OrdQ P io j d qo) (ss : M.StageSeq P th io Sg qo W l j m1 κ) (hunb : ∀ e, M.mem (M.op e e) th → ∃ e', M.mem (M.op e e') th ∧ e ≠ e') {ol : V} (hol : M.mem (M.quad j.1 l qo ol) P) :
    ∃ Pw, M.PowNames P th io F tp Pw ol κ j m1 := by
  obtain ⟨Pw, -, hP0⟩ := M.comp (σW [(0, 4), (20, 7), (27, 3), (28, 7), (464, 5)]) (Fml.ex 401 (Fml.ex 402 (Fml.ex 403 (Fml.ex 404 (.and (fPr 0 401 402) (.and (fApp 464 401 403) (.and (fApp4 20 25 404 402 403) (Fml.ex 84 (.and (.mem 84 27) (.and (.neg (.eq 84 10)) (fApp3 28 401 84 396))))))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 10 (0 : M.Num).1) 20 P) 25 j.1) 27 M.nat) 28 M.adG) 396 m1.1) 464 W)
  have hP1 : ∀ q0, M.mem q0 Pw ↔ ∃ i p0 y1 ξ, q0 = M.op i p0 ∧ M.mem (M.op i y1) W ∧
      M.mem (M.quad j.1 ξ p0 y1) P ∧
      ∃ x, M.mem x M.nat ∧ ¬ x = (0 : M.Num).1 ∧ M.mem (M.trip i x m1.1) M.adG := by
    intro q0
    rw [hP0 q0]
    simp [Sat, M.sat_ex, M.sat_fPr', M.sat_fApp', M.sat_fApp3', M.sat_fApp4', Function.update_apply]
  have hPw : ∀ (i : M.Num) (p0 : V), M.mem (M.op i.1 p0) Pw ↔
      (∃ ξ, M.SAt P W j i ξ p0) ∧ i + 1 ≤ m1 := by
    intro i p0
    rw [hP1]
    constructor
    · rintro ⟨i1, p1, y1, ξ, hq0, h1, h2, h3⟩
      obtain ⟨e1, e2⟩ := M.op_inj hq0
      rw [← e1] at h1 h3
      rw [← e2] at h2
      exact ⟨⟨ξ, y1, h1, h2⟩, (M.ltRaw_num i m1).mp h3⟩
    · rintro ⟨⟨ξ, y1, h1, h2⟩, h3⟩
      exact ⟨i.1, p0, y1, ξ, rfl, h1, h2, (M.ltRaw_num i m1).mpr h3⟩
  have hdom : ∀ i p0, M.mem (M.op i p0) Pw → ∃ k : M.Num, k.1 = i := by
    intro i p0 h1
    obtain ⟨i1, p1, y1, ξ, hq0, h1', -⟩ := (hP1 _).mp h1
    obtain ⟨e1, -⟩ := M.op_inj hq0
    obtain ⟨k, hk, -⟩ := ss.idx _ _ h1'
    exact ⟨k, hk.trans e1.symm⟩
  refine ⟨Pw, fun hm1 => ?_, fun i hi => ?_, fun i p0 p' h1 h2 => ?_, fun i p0 h1 => ?_,
    fun i p0 h1 => ?_, fun i p0 p' h1 h2 x hx => ?_⟩
  · exact (hPw 0 ol).mpr ⟨⟨l, M.sat_zero hd ss hol⟩, by rw [zero_add]; exact hm1⟩
  · obtain ⟨ξ, p0, h1⟩ := M.sat_tot ss (le_trans (M.le_add_one i) hi)
    exact ⟨p0, (hPw i p0).mpr ⟨⟨ξ, h1⟩, hi⟩⟩
  · obtain ⟨k, hk⟩ := hdom i p0 h1
    rw [← hk] at h1 h2
    obtain ⟨⟨ξ, a1⟩, -⟩ := (hPw k p0).mp h1
    obtain ⟨⟨ξ', a2⟩, -⟩ := (hPw k p').mp h2
    exact (M.sat_fun hd ss a1 a2).2
  · obtain ⟨k, hk⟩ := hdom i p0 h1
    rw [← hk] at h1
    exact ⟨k, hk, ((hPw k p0).mp h1).2⟩
  · obtain ⟨k, hk⟩ := hdom i p0 h1
    rw [← hk] at h1
    obtain ⟨⟨ξ, a1⟩, hi⟩ := (hPw k p0).mp h1
    exact M.sat_inN hd hq hSg hqo ss hunb a1 hi
  · obtain ⟨⟨ξ, a1⟩, -⟩ := (hPw i p0).mp h1
    obtain ⟨⟨ξ', a2⟩, -⟩ := (hPw (i + 1) p').mp h2
    obtain ⟨hnext, u, hu, hn⟩ := M.sat_step ss a1 a2
    obtain ⟨lt, ne⟩ := M.sat_lt hd hq hSg ss hunb a1 a2
    obtain ⟨δ, hδ, hneδ⟩ := hunb κ (hd.hth.fld _ _ (M.sat_le_top ss a1)).2
    exact M.pow_of_next hd hPr hq hNu hSg hnext hδ hneδ lt ne (M.sat_rank hd hqo ss a1) hn hu x hx

end seq3
/-! ## The sequence of the iterated power sets as a member of the level -/

/-- The statement proved by induction on `k` (name `400`) for the internal sequence. -/
def innerFml : Fml :=
  Fml.imp (fLtN 400 396) (Fml.ex 470 (.and (Fml.ex 65 (.and (.eq 65 462) (fInN 470))) (.all 471
    (Fml.iff (fEpsS 471 470) (Fml.ex 472 (Fml.ex 473 (Fml.ex 474 (Fml.ex 475 (.and (.mem 472 27)
    (.and (fLeN 472 400) (.and (fApp 460 472 473) (.and (fApp 461 472 474) (.and (Fml.ex 476
    (Fml.ex 477 (.and (fSim 476 476) (.and (fSim 477 477) (.and (.all 478 (Fml.iff (fEpsS 478
    476) (Fml.or (fSim 478 473) (fSim 478 473)))) (.and (.all 478 (Fml.iff (fEpsS 478 477)
    (Fml.or (fSim 478 473) (fSim 478 474)))) (.all 478 (Fml.iff (fEpsS 478 475) (Fml.or (fSim
    478 476) (fSim 478 477)))))))))) (fSim 471 475))))))))))))))

/-- `f` denotes the set of the ordered pairs of the number `i` and the `i`-th iterated power
set, for `i ≤ k`. -/
def InnerSeqR (P th io nat ad F tp Nm Pw κ : V) (j : M.Num) (k f : V) : Prop :=
  M.InNRaw P th io nat j.1 κ f ∧ ∀ x, M.EpsStarRaw P th io nat j.1 tp F x f ↔
    ∃ i o p0 c, M.mem i nat ∧ (∃ y, M.mem y nat ∧ M.mem (M.trip i y k) ad) ∧ M.mem (M.op i o) Nm ∧
      M.mem (M.op i p0) Pw ∧ M.IsOPairN P th io F tp j o p0 c ∧ M.SimRaw P j.1 tp F x c

section inner1

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j m1 : M.Num}
variable {l κ Nm ol Pw : V}

theorem pairN_congr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a b c a' b' c' : V}
    (h : M.IsPairN P th io F tp j a b c) (h' : M.IsPairN P th io F tp j a' b' c')
    (sa : M.SimRaw P j.1 tp F a a') (sb : M.SimRaw P j.1 tp F b b') (hc : M.SimRaw P j.1 tp F c c) (hc' : M.SimRaw P j.1 tp F c' c') : M.SimRaw P j.1 tp F c c' := by
  obtain ⟨β, -, rc, -, hβ, -⟩ := M.sim_names hd hc
  obtain ⟨β', -, rc', -, hβ', -⟩ := M.sim_names hd hc'
  have h1 : ∀ x, M.EpsStarRaw P th io M.nat j.1 tp F x c ↔ (M.SimRaw P j.1 tp F x a ∨ M.SimRaw P j.1 tp F x b) := h
  have h1' : ∀ x, M.EpsStarRaw P th io M.nat j.1 tp F x c' ↔ (M.SimRaw P j.1 tp F x a' ∨ M.SimRaw P j.1 tp F x b') := h'
  rw [M.sim_iff_ext hd rc rc' hβ hβ']
  intro x
  rw [h1 x, h1' x]
  constructor
  · rintro (k1 | k1)
    · exact Or.inl (M.sim_trans hd k1 sa)
    · exact Or.inr (M.sim_trans hd k1 sb)
  · rintro (k1 | k1)
    · exact Or.inl (M.sim_trans hd k1 (M.sim_symm hd sa))
    · exact Or.inr (M.sim_trans hd k1 (M.sim_symm hd sb))

/-- Two names that denote the ordered pair of the same sets denote the same set. -/
theorem opairN_congr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a b c c' : V}
    (h : M.IsOPairN P th io F tp j a b c) (h' : M.IsOPairN P th io F tp j a b c') (ha : M.SimRaw P j.1 tp F a a) (hb : M.SimRaw P j.1 tp F b b)
    (hc : M.SimRaw P j.1 tp F c c) (hc' : M.SimRaw P j.1 tp F c' c') : M.SimRaw P j.1 tp F c c' := by
  obtain ⟨s, q, hss, hqq, hs, hq, hcm⟩ := h
  obtain ⟨s', q', hs's', hq'q', hs', hq', hcm'⟩ := h'
  exact M.pairN_congr hd hcm hcm' (M.pairN_congr hd hs hs' ha ha hss hs's')
    (M.pairN_congr hd hq hq' ha hb hqq hq'q') hc hc'

/-- **The sequence of the iterated power sets is a member of the level.** For every `k < m₁`
there is a name of rank below `κ` that denotes the set of the ordered pairs of the number `i`
and the `i`-th iterated power set, `i ≤ k`. -/
theorem exists_inner_seq (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (hlim : M.IsLim th κ)
    (nn : M.NumNames P th io F tp qo Nm ol j l) (pn : M.PowNames P th io F tp Pw ol κ j m1)
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
    obtain ⟨p00, hp00⟩ := pn.tot 0 h01
    have hoκ := numκ _ _ ho0
    have hpκ := pn.inN _ _ hp00
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
      rw [nn.fn _ _ _ r1 ho0, pn.fn _ _ _ r2 hp00] at r3
      exact Or.inl (M.sim_trans hd r4 (M.opairN_congr hd r3 hc0p (M.inN_refl hd hoκ)
        (M.inN_refl hd hpκ) (M.sim_trans hd (M.sim_symm hd r4) r4) (M.inN_refl hd hc0)))
  · intro k ih
    rw [show M.succ k.1 = (k + 1).1 from (M.val_add_one k).symm, hsat (k + 1)]
    intro hlt
    have hk2 : k + 1 + 1 ≤ m1 := (M.ltRaw_num (k + 1) m1).mp hlt
    obtain ⟨f, hf, hfm⟩ := (hsat k).mp ih
      ((M.ltRaw_num k m1).mpr (le_trans (M.le_add_one _) hk2))
    obtain ⟨o', ho'⟩ := nn.tot (k + 1)
    obtain ⟨p', hp'⟩ := pn.tot (k + 1) hk2
    have hoκ := numκ _ _ ho'
    have hpκ := pn.inN _ _ hp'
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
        rw [nn.fn _ _ _ r1 ho', pn.fn _ _ _ r2 hp'] at r3
        have hs : M.SimRaw P j.1 tp F x c' := M.sim_trans hd r4 (M.opairN_congr hd r3 hc'p (M.inN_refl hd hoκ)
          (M.inN_refl hd hpκ) (M.sim_trans hd (M.sim_symm hd r4) r4) (M.inN_refl hd hc'))
        exact ⟨s1, (hs1m x).mpr (Or.inl hs), (hs2m s1).mpr (Or.inr (M.inN_refl hd hs1))⟩
      · have hxf : M.EpsStarRaw P th io M.nat j.1 tp F x f := (hfm x).mpr ⟨i, o, p1, c, hi,
          (M.leRaw_iff M.adG_spec ⟨i, hi⟩ k).mpr (M.le_of_succ_le_succ e), r1, r2, r3, r4⟩
        exact ⟨f, hxf, (hs2m f).mpr (Or.inl (M.inN_refl hd hf))⟩

end inner1
/-! ## Lemma 3.2 -/

theorem vr_zero_zero : M.vr 0 0 = 0 := by
  have h : M.vr 0 0 = ((0 + 0) * (0 + 0) + 0 : M.Num) := rfl
  rw [h]
  simp

/-- **Lemma 3.2, in the form proved.** A hierarchy of names over a ladder of height `n`, and
a limit stage `κ` of it, such that the level at `κ`, as a structure `(U, EL)` in the sense of
§3.1, has these properties.

* Extensionality, foundation, pairing, union and infinity are true at `κ` under every
  sequence, and so are all instances of Separation and of Collection, for arbitrary codes `φ`
  in the language with the membership symbol and the symbol `2` for the canonical order; the
  canonical order is a linear order, respects "have the same members", and every set that has
  a member has a least member. The symbol `1` is never true.
* The structure is well-founded: every set of names of rank below `κ` that is closed under
  "denote the same set" and has a member has a member none of whose members is in the set.
* Its numbers are the numbers of the model: `Nm` is a one-to-one map of the numbers of the
  model onto the members of the set denoted by `ol`, up to "denote the same set", which takes
  `0` to the empty set and `i + 1` to the successor of the image of `i`.
* The iterated power sets of that set exist up to `m`: `Pw` assigns to each `i ≤ m` a name of
  rank below `κ`, the first is `ol`, and each next one denotes the set of the subsets, in the
  structure, of the previous one; and `sq` denotes the set of the ordered pairs of the `i`-th
  number and the `i`-th iterated power set, `i ≤ m`, so the finite sequence of the iterated
  power sets is a member of the structure.

`bridge` relates truth at `κ` under a sequence to truth in `(U, EL)` at an assignment with the
same values. -/
structure Lemma32 (R P th io Nt nle p F d tp qo Nu Pr κ U EL ol Nm Pw sq l : V) (n j m : M.Num) :
    Prop where
  hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr n j
  hPr : M.IsPrec P th io Nt d Pr j
  hκ : M.IsLim th κ
  hU : ∀ k a, M.mem (M.op k a) U ↔ M.mem k M.nat ∧ M.InNRaw P th io M.nat j.1 κ a
  hE : ∀ r a b, M.mem (M.trip r a b) EL ↔ M.mem r M.nat ∧ M.InNRaw P th io M.nat j.1 κ a ∧ M.InNRaw P th io M.nat j.1 κ b ∧
    M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG (1 : M.Num).1 (2 : M.Num).1 F κ r a b
  bridge : ∀ (c : M.Num) (s t : V), M.IsAsg U s →
    (∀ i : M.Num, i ≤ c → ∃ e, M.mem (M.op i.1 e) s ∧ M.ValRaw P th io M.nat Nt j.1 d κ t i.1 e) →
    (M.Holds U EL c s → M.TrueAt P io F j.1 κ c t) ∧ (M.Fails U EL c s → ¬ M.TrueAt P io F j.1 κ c t)
  noT : ∀ (v w : M.Num) (t : V), ¬ M.TrueAt P io F j.1 κ (M.cRel 1 v w) t
  ext : ∀ x y z w : M.Num, x ≠ y → z ≠ x → z ≠ y → w ≠ x → w ≠ y → ∀ t, M.TrueAt P io F j.1 κ (M.cExt x y z w) t
  found : ∀ a x y : M.Num, a ≠ x → x ≠ y → a ≠ y → ∀ t, M.TrueAt P io F j.1 κ (M.cFound a x y) t
  pairing : ∀ a b c x z : M.Num, a ≠ b → a ≠ c → b ≠ c → c ≠ x → a ≠ x → b ≠ x → z ≠ x → z ≠ a →
    z ≠ b → ∀ t, M.TrueAt P io F j.1 κ (M.cPairAx a b c x z) t
  union : ∀ b c x y : M.Num, b ≠ c → c ≠ x → b ≠ x → x ≠ y → b ≠ y →
    ∀ t, M.TrueAt P io F j.1 κ (M.cUnionAx b c x y) t
  infinity : ∀ w e u x y z : M.Num, w ≠ e → e ≠ u → w ≠ x → w ≠ y → x ≠ y → y ≠ u → x ≠ u →
    z ≠ u → z ≠ x → ∀ t, M.TrueAt P io F j.1 κ (M.cInf w e u x y z) t
  sep : ∀ a b φ : M.Num, a ≠ 0 → M.cAnd (M.cRel 0 0 a) φ + 1 ≤ b → ∀ t, M.TrueAt P io F j.1 κ (M.cSep a b φ) t
  coll : ∀ a b y z φ : M.Num, a ≠ y → a ≠ b → b ≠ y → b ≠ z → φ + 1 ≤ b →
    ∀ t, M.TrueAt P io F j.1 κ (M.cColl a b y z φ) t
  wlin : ∀ x y z : M.Num, x ≠ y → z ≠ x → z ≠ y → ∀ t, M.TrueAt P io F j.1 κ (M.cWLin x y z) t
  wirr : ∀ (x : M.Num) (t : V), M.TrueAt P io F j.1 κ (M.cWIrr x) t
  wtrans : ∀ x y z : M.Num, x ≠ y → x ≠ z → y ≠ z → ∀ t, M.TrueAt P io F j.1 κ (M.cWTrans x y z) t
  wcong : ∀ x y z w : M.Num, x ≠ y → z ≠ x → z ≠ y → x ≠ w → y ≠ w →
    ∀ t, M.TrueAt P io F j.1 κ (M.cWCong x y z w) t
  wleast : ∀ a x y : M.Num, a ≠ x → x ≠ y → a ≠ y → ∀ t, M.TrueAt P io F j.1 κ (M.cWLeast a x y) t
  wf : ∀ X a, M.mem a X → M.InNRaw P th io M.nat j.1 κ a → (∀ x x', M.mem x X → M.SimRaw P j.1 tp F x' x → M.mem x' X) →
    ∃ b, M.mem b X ∧ ∀ x, M.mem x X → ¬ M.EpsStarRaw P th io M.nat j.1 tp F x b
  olκ : M.InNRaw P th io M.nat j.1 κ ol
  nums : M.NumNames P th io F tp qo Nm ol j l
  pows : M.PowNames P th io F tp Pw ol κ j (m + 1)
  sqκ : M.InNRaw P th io M.nat j.1 κ sq
  sq_mem : ∀ x, M.EpsStarRaw P th io M.nat j.1 tp F x sq ↔ ∃ (i : M.Num) (o p0 c : V), i ≤ m ∧ M.mem (M.op i.1 o) Nm ∧
    M.mem (M.op i.1 p0) Pw ∧ M.IsOPairN P th io F tp j o p0 c ∧ M.SimRaw P j.1 tp F x c

/-- **Lemma 3.2.** Over every ladder of height at least `3(m + 1) + 2` in a model of
NFU + Infinity there are a hierarchy of names and a stage `κ` with the properties collected in
`Lemma32`. -/
theorem lemma_3_2 {R E z S : V} {n m : M.Num} (h : M.IsLadder R E z S n)
    (hn : 3 * (m + 1) + 1 + 1 ≤ n) :
    ∃ P th io Nt nle p F d tp qo Nu Pr κ U EL ol Nm Pw sq l,
      M.Lemma32 R P th io Nt nle p F d tp qo Nu Pr κ U EL ol Nm Pw sq l n (3 * (m + 1) + 1 + 1) m := by
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
  obtain ⟨Nm, ol, nn⟩ := M.exists_numNames hd hqo hl hβ Ntot Ndom Nfun Nonto Nord
  obtain ⟨W, κ, ss⟩ := M.exists_stageSeq h hd hPr hq hSg (L := 3 * (m + 1)) (m1 := m + 1) hL
    (le_refl _) hlong hunb hl.1 nn.hol g0_tot g0_dom g0_inj
  have hm1 : (1 : M.Num) ≤ m + 1 := M.le_def.mpr ⟨m, by ring⟩
  have hlim := M.top_lim hd hPr hq hSg ss hm1
  obtain ⟨Pw, pn⟩ := M.exists_powNames hd hPr hq hNu hSg hqo ss hunb nn.hol
  have hlκ : M.mem (M.op l κ) th ∧ l ≠ κ := by
    have h0 := M.sat_zero hd ss nn.hol
    obtain ⟨ξ1, p1, h1⟩ := M.sat_tot ss (i := 0 + 1) (by rw [zero_add]; exact hm1)
    obtain ⟨lt, ne⟩ := M.sat_lt hd hq hSg ss hunb h0 h1
    have le2 := M.sat_le_top ss h1
    exact ⟨hth.trans _ _ _ lt le2, M.wo_ne_of_lt_le hth lt ne le2⟩
  have holκ := M.rank_inN (M.ordName_rank hd hqo nn.hol) hlκ.1 hlκ.2
  have hdκ := M.d_inN hd hlκ.1 hlκ.2
  obtain ⟨sq, hsq, hsqm⟩ := M.exists_inner_seq hd hlim nn pn hlκ.1 m (le_refl _)
  obtain ⟨U, EL, hU, hE, hbr⟩ := M.hier_structure hd hlim.1 hdκ
  obtain ⟨pκ, yk, a1, a2⟩ := ss.top
  have htop : M.SAt P W (3 * (m + 1) + 1 + 1) (m + 1) κ pκ := ⟨yk, a1, a2⟩
  obtain ⟨ξm, pm, hm0⟩ := M.sat_tot ss (i := m) (M.le_add_one m)
  have hnext := (M.sat_step ss hm0 htop).1
  obtain ⟨σ', hσ', neσ'⟩ := hunb κ hlim.1
  obtain ⟨δ, hδ, neδ⟩ := hunb σ' (hth.fld _ _ hσ').2
  obtain ⟨β0, hβ0, hβ0ne⟩ := hβ
  refine ⟨P, th, io, Nt, nle, p, F, d, tp, qo, Nu, Pr, κ, U, EL, ol, Nm, Pw, sq, l, ?_⟩
  exact
    { hd := hd
      hPr := hPr
      hκ := hlim
      hU := hU
      hE := hE
      bridge := hbr
      noT := fun v w t => M.hier_T_false hd hNu v w t
      ext := fun x y z w h1 h2 h3 h4 h5 t => M.hier_ext hd hlim.1 x y z w h1 h2 h3 h4 h5 t
      found := fun a x y h1 h2 h3 t => M.hier_found hd hlim.1 a x y h1 h2 h3 t
      pairing := fun a b c x z h1 h2 h3 h4 h5 h6 h7 h8 h9 t =>
        M.hier_pairing hd hlim a b c x z h1 h2 h3 h4 h5 h6 h7 h8 h9 t
      union := fun b c x y h1 h2 h3 h4 h5 t => M.hier_union hd hlim b c x y h1 h2 h3 h4 h5 t
      infinity := fun w e u x y z h1 h2 h3 h4 h5 h6 h7 h8 h9 t =>
        M.hier_inf hd hl hβ0 hβ0ne hlκ.1 hlκ.2 w e u x y z h1 h2 h3 h4 h5 h6 h7 h8 h9 t
      sep := fun a b φ ha hb t =>
        M.hier_sep hd hPr hq hNu hSg hnext hσ' neσ' hδ neδ a b φ ha hb t
      coll := fun a b y z φ h1 h2 h3 h4 h5 t =>
        M.hier_coll hd hPr hq hNu hSg hnext hσ' neσ' hδ neδ a b y z φ h1 h2 h3 h4 h5 t
      wlin := fun x y z h1 h2 h3 t => M.hier_wlin hd hPr hlim.1 x y z h1 h2 h3 t
      wirr := fun x t => M.hier_wirr hd hPr hlim.1 x t
      wtrans := fun x y z h1 h2 h3 t => M.hier_wtrans hd hPr hlim.1 x y z h1 h2 h3 t
      wcong := fun x y z w h1 h2 h3 h4 h5 t => M.hier_wcong hd hPr hlim.1 x y z w h1 h2 h3 h4 h5 t
      wleast := fun a x y h1 h2 h3 t => M.hier_wleast hd hPr hlim.1 a x y h1 h2 h3 t
      wf := fun X a haX haκ hcl => by
        obtain ⟨β, ra, lt, -⟩ := M.inN_rank haκ
        exact M.eps_wf hd haX ra (hth.fld _ _ lt).1 hcl
      olκ := holκ
      nums := nn
      pows := pn
      sqκ := hsq
      sq_mem := fun x => by
        rw [hsqm x]
        constructor
        · rintro ⟨i, o, p0, c, hi, hle, r1, r2, r3, r4⟩
          exact ⟨⟨i, hi⟩, o, p0, c, (M.leRaw_iff M.adG_spec ⟨i, hi⟩ m).mp hle, r1, r2, r3, r4⟩
        · rintro ⟨i, o, p0, c, hle, r1, r2, r3, r4⟩
          exact ⟨i.1, o, p0, c, i.2, (M.leRaw_iff M.adG_spec i m).mpr hle, r1, r2, r3, r4⟩ }

section l32

variable {R P th io Nt nle p F d tp qo Nu Pr κ U EL ol Nm Pw sq l : V} {n j m : M.Num}

/-- **From truth at the stage to truth in the structure.** A code that is a formula of the
structure and is true at `κ` under every sequence is true in the structure at every assignment
all of whose values are names of rank below `κ`. -/
theorem l32_holds (L : M.Lemma32 R P th io Nt nle p F d tp qo Nu Pr κ U EL ol Nm Pw sq l n j m) {c : M.Num}
    (hform : M.Form U EL c) (htrue : ∀ t, M.TrueAt P io F j.1 κ c t) {s : V} (hs : M.IsAsg U s)
    (hsU : ∀ i a, M.mem (M.op i a) s → M.InNRaw P th io M.nat j.1 κ a) : M.Holds U EL c s := by
  rcases hform s hs with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨t, -, ht⟩ := M.exists_seq_vals L.hd (σ := κ) (g := s) (c + 1)
      (fun k hk => by
        obtain ⟨a, ha, -⟩ := hs.2.2.1 k.1 k.2
        exact ⟨a, hsU _ _ ha, ha⟩)
      (fun k a hk hka => hsU _ _ hka)
    exact (L.bridge c s t hs (fun i hi => ht i (add_le_add_left hi 1))).2 h1 (htrue t)

/-- **Separation holds in the structure**: for a formula `φ` of the structure, the instance of
Separation for `φ` with variables of the sort `0`. -/
theorem l32_sep_holds (L : M.Lemma32 R P th io Nt nle p F d tp qo Nu Pr κ U EL ol Nm Pw sq l n j m) {φ : M.Num}
    (hφ : M.Form U EL φ) (a b : M.Num) (ha : M.vr 0 a ≠ 0)
    (hb : M.cAnd (M.cRel 0 0 (M.vr 0 a)) φ + 1 ≤ M.vr 0 b) {s : V} (hs : M.IsAsg U s)
    (hsU : ∀ i a, M.mem (M.op i a) s → M.InNRaw P th io M.nat j.1 κ a) :
    M.Holds U EL (M.cSep (M.vr 0 a) (M.vr 0 b) φ) s := by
  refine M.l32_holds L ?_ (L.sep _ _ φ ha hb) hs hsU
  have h0 : M.Form U EL (M.cAll (M.vr 0 0) (M.cIff (M.cRel 0 0 (M.vr 0 b))
      (M.cAnd (M.cRel 0 0 (M.vr 0 a)) φ))) :=
    M.form_all (M.form_iff (M.form_rel 0 _ _) (M.form_and (M.form_rel 0 _ _) hφ)) 0 0
  rw [M.vr_zero_zero] at h0
  exact M.form_all (M.form_ex h0 0 b) 0 a

/-- **Collection holds in the structure**: for a formula `φ` of the structure, the instance of
Collection for `φ` with variables of the sort `0`. -/
theorem l32_coll_holds (L : M.Lemma32 R P th io Nt nle p F d tp qo Nu Pr κ U EL ol Nm Pw sq l n j m) {φ : M.Num}
    (hφ : M.Form U EL φ) (a b y z : M.Num) (hay : a ≠ y) (hab : a ≠ b) (hby : b ≠ y)
    (hbz : b ≠ z) (hb : φ + 1 ≤ M.vr 0 b) {s : V} (hs : M.IsAsg U s)
    (hsU : ∀ i a, M.mem (M.op i a) s → M.InNRaw P th io M.nat j.1 κ a) :
    M.Holds U EL (M.cColl (M.vr 0 a) (M.vr 0 b) (M.vr 0 y) (M.vr 0 z) φ) s := by
  refine M.l32_holds L ?_ (L.coll _ _ _ _ φ (M.vr_ne_snd hay) (M.vr_ne_snd hab) (M.vr_ne_snd hby)
    (M.vr_ne_snd hbz) hb) hs hsU
  exact M.form_all (M.form_imp
    (M.form_all (M.form_imp (M.form_rel 0 _ _) (M.form_ex hφ 0 z)) 0 y)
    (M.form_ex (M.form_all (M.form_imp (M.form_rel 0 _ _)
      (M.form_ex (M.form_and (M.form_rel 0 _ _) hφ) 0 z)) 0 y) 0 b)) 0 a

end l32
/-- **Lemma 3.2 at calm heights.** If the number `3(m + 1) + 2` is calm, then, by Lemma 3.1,
there is a ladder of that height, and so the structure of Lemma 3.2 exists. -/
theorem lemma_3_2_calm {m : M.Num} (hn : M.InS (3 * (m + 1) + 1 + 1 : M.Num).1) :
    ∃ R P th io Nt nle p F d tp qo Nu Pr κ U EL ol Nm Pw sq l,
      M.Lemma32 R P th io Nt nle p F d tp qo Nu Pr κ U EL ol Nm Pw sq l (3 * (m + 1) + 1 + 1)
        (3 * (m + 1) + 1 + 1) m := by
  obtain ⟨R, E, z, S, h, -⟩ := M.lemma_3_1 hn
  obtain ⟨P, th, io, Nt, nle, p, F, d, tp, qo, Nu, Pr, κ, U, EL, ol, Nm, Pw, sq, l, L⟩ :=
    M.lemma_3_2 h (le_refl _)
  exact ⟨R, P, th, io, Nt, nle, p, F, d, tp, qo, Nu, Pr, κ, U, EL, ol, Nm, Pw, sq, l, L⟩

end Model

end NFUCut
