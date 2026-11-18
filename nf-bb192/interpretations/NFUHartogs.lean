module

public import ConNF.NF.NFUSound

/-!
# The ladder: pairing, well-orderings, and the constructible hierarchy (§3.3 of the note)

This file continues `NFUSound`. It works in an arbitrary model `M` of NFU + Infinity, with a
ladder `R`, `E`, `z`, `S` of height `m` as in `NFULadder`.

Step 1 (pairing and sequences on the rungs).
* `exists_pairing`: a set `P` of quadruples `⟨i, a, b, c⟩` which for every rung `i ≤ m` is the
  graph of an injection from pairs of members of rung `i` into rung `i` (`IsPairing`).
* `rel_code`, `rel_decode`: the set relations on rung `i` are the relations coded by members of
  rung `i + 1`.
* `exists_seq`, `nth_fun`, `seq_code`: every member of a rung is read as a sequence, and every
  finite sequence of members of a rung (of any length that is a number of the model) is coded
  by a member of the rung. `exists_numerals`: an injection of the numbers into a rung.

Step 2 (well-orderings and the Hartogs well-ordering).
* `IsWO`, `PIso`, `Emb`, `SegOf`; `piso_agree`, `wo_compare` (comparability), `wo_min`.
* `hartogs`: for every rung `i` with two rungs above it there is a set well-ordering `H` of
  members of rung `i + 2` in which every set well-ordering of a subset of rung `i` embeds as a
  proper initial segment, and whose proper initial segments are isomorphic to well-orderings of
  subsets of rung `i`. `hartogs_no_inj`: `H` does not inject into rung `i`.
* `wo_sum`, `wo_lex`, `seg_of_strict`: sums and products of well-orderings on a rung.

Step 3 (the constructible hierarchy, definition and first facts).
* `nat_least`, `isWO_natLe`; `wo_rec`: recursion along a set well-ordering for a stratified
  condition.
* `exists_hierData`: the hierarchy along a set well-ordering `th` of members of a rung
  (`HierData`). Names are members of the rung of the form `(β, (φ̂, u))`. One recursion along the
  product of `th` and the numbers with a top point defines truth at every stage (`TrueAt`) and
  when two names denote the same set (`SimRaw`).
* The clauses `hier_rel`, `hier_neg`, `hier_and`, `hier_all`, `hier_all_ex`, `hier_sim`;
  `coin_hier` (coincidence); `eps_rank` (the levels are transitive); `eps_iff` (the members of a
  name); `sim_refl`, `sim_symm`, `sim_trans`, `inv_hier` (denoting the same set is a
  congruence); `sim_iff_ext` (extensionality); `hier_eq_sim` (equality is definable);
  `level_name`, `pair_name`.
* `hier_structure`, `exists_asg_of_seq`, `level_models`: every level above the least is a set
  structure in the sense of `NFUSat` whose satisfaction relation agrees with `TrueAt`.
* `def_name` (the names of rank `α` denote the definable subsets of the level), `up_name`
  (the levels increase), `union_name`, `level_mem`; `pair_lim`, `union_lim` (limit levels are
  closed under pairs and unions); `eps_wf` (foundation).
* `d0_abs`: bounded formulas are absolute between the levels; `sep_d0`, `bound_lim`,
  `sep_lim`: separation for bounded formulas at limit levels.
* The ordinals of the hierarchy: `ordName_mem`, `ordN_ordName`, `ordName_members`,
  `ord_is_ordName`, `ordName_lt`, `ordName_inj`. Up to "denote the same set", the names that
  denote ordinals are the ordinal names of the stages, ordered as the stages.

* Axioms as coded sentences: `hier_ext`, `hier_found` (true at every stage), `hier_pairing`,
  `hier_union` (true at limit stages), `hier_inf` (true above a limit stage that is not the
  least); `limit_level_axioms`, `level_infinity`: the same in the set structures of the
  levels, in the sense of `NFUSat`. `ordName_succ`, `ordName_lim`: the ordinal names of
  successor and limit stages.

* `exists_limit_stage`, `hartogs_limit`, `limit_above`: the Hartogs well-ordering has a limit
  stage that is not the least, and limit stages are cofinal in it. `exists_zf0_level`: in
  every ladder with a pairing and rungs `i`, `i + 1`, `i + 2` there is a limit level in which
  extensionality, foundation, pairing, union and infinity hold.

* `exists_omega_stage`, `omega_members`: the stages below the first limit stage are the
  numbers of the model, and the members of the ordinal name of that stage are the ordinal
  names of those stages.

* `opair_lim`, `opair_inj`: ordered pairs in the hierarchy.
* `good_above`: stages that are limits of limit stages are cofinal in the Hartogs
  well-ordering. `exists_good_level`: `exists_zf0_level` with such a stage.

Not here: the definable well-ordering of the hierarchy, satisfaction over a level expressed
in later levels, condensation, and steps 4–9 of §3.3.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

@[expose] public section

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

/-! ## Pairing on the rungs of a ladder (§3.3, step 1) -/

/-- Quadruples of objects of one type. -/
noncomputable def quad (i a b c : V) : V := M.op (M.op i a) (M.op b c)

theorem quad_inj {i a b c i' a' b' c' : V} (h : M.quad i a b c = M.quad i' a' b' c') :
    i = i' ∧ a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨h1, h2⟩ := M.op_inj h
  obtain ⟨h3, h4⟩ := M.op_inj h1
  obtain ⟨h5, h6⟩ := M.op_inj h2
  exact ⟨h3, h4, h5, h6⟩

/-- `q = ⟨i, a, b, c⟩`, with bound names `32`–`37`. -/
def fQuad (q i a b c : ℕ) : Fml :=
  Fml.ex 32 (Fml.ex 33 (.and (fOp q 32 33 34 35) (.and (fOp 32 i a 36 37) (fOp 33 b c 36 37))))

theorem sat_fQuad {q i a b c : ℕ} (ρ : ℕ → V) (hq : q < 30 ∨ q = 39) (hi : i < 30) (ha : a < 30)
    (hb : b < 30) (hc : c < 30) :
    Sat M.mem M.isSet (fQuad q i a b c) ρ ↔ ρ q = M.quad (ρ i) (ρ a) (ρ b) (ρ c) := by
  have q32 : q ≠ 32 := by omega
  have q33 : q ≠ 33 := by omega
  have i32 : i ≠ 32 := by omega
  have i33 : i ≠ 33 := by omega
  have a32 : a ≠ 32 := by omega
  have a33 : a ≠ 33 := by omega
  have b32 : b ≠ 32 := by omega
  have b33 : b ≠ 33 := by omega
  have c32 : c ≠ 32 := by omega
  have c33 : c ≠ 33 := by omega
  simp only [fQuad, M.sat_ex, Sat,
    M.sat_fOp (p := q) (a := 32) (b := 33) (u := 34) (c := 35) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    M.sat_fOp (p := 32) (a := i) (b := a) (u := 36) (c := 37) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    M.sat_fOp (p := 33) (a := b) (b := c) (u := 36) (c := 37) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    Function.update_self, Function.update_of_ne q32, Function.update_of_ne q33,
    Function.update_of_ne i32, Function.update_of_ne i33,
    Function.update_of_ne a32, Function.update_of_ne a33, Function.update_of_ne b32,
    Function.update_of_ne b33, Function.update_of_ne c32, Function.update_of_ne c33,
    Function.update_of_ne (show (32 : ℕ) ≠ 33 by decide)]
  unfold quad
  constructor
  · rintro ⟨p1, p2, h1, rfl, rfl⟩
    exact h1
  · intro h
    exact ⟨_, _, h, rfl, rfl⟩

/-- `⟨i, a, b, c⟩ ∈ G`, with bound names `32`–`37` and `39`. -/
def fApp4 (G i a b c : ℕ) : Fml := Fml.ex 39 (.and (.mem 39 G) (fQuad 39 i a b c))

theorem sat_fApp4 {G i a b c : ℕ} (ρ : ℕ → V) (hG : G < 30) (hi : i < 30) (ha : a < 30)
    (hb : b < 30) (hc : c < 30) :
    Sat M.mem M.isSet (fApp4 G i a b c) ρ ↔ M.mem (M.quad (ρ i) (ρ a) (ρ b) (ρ c)) (ρ G) := by
  have h1 : G ≠ 39 := by omega
  have h2 : i ≠ 39 := by omega
  have h3 : a ≠ 39 := by omega
  have h4 : b ≠ 39 := by omega
  have h5 : c ≠ 39 := by omega
  simp only [fApp4, M.sat_ex, Sat,
    fun ρ' : ℕ → V => M.sat_fQuad (q := 39) (i := i) (a := a) (b := b) (c := c) ρ' (Or.inr rfl)
      hi ha hb hc,
    Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

/-! ### Rungs -/

/-- Members of a rung above the base with the same extension are equal. -/
theorem rung_ext {R E z S : V} {m : M.Num} (h : M.IsLadder R E z S m) {i : M.Num}
    (hi : i + 1 ≤ m) {b b' : V} (hb : M.mem (M.op (i + 1).1 b) R)
    (hb' : M.mem (M.op (i + 1).1 b') R)
    (hext : ∀ a, M.mem (M.op i.1 a) R →
      (M.mem (M.trip i.1 a b) E ↔ M.mem (M.trip i.1 a b') E)) : b = b' := by
  obtain ⟨X, hXs, hX0⟩ := M.comp (σW [(1, 5), (2, 7)]) (.and (fApp 1 3 0) (fApp3 2 3 0 4)) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 1 R)
      2 E) 3 i.1) 4 b)
  have hX : ∀ a, M.mem a X ↔ M.mem (M.op i.1 a) R ∧ M.mem (M.trip i.1 a b) E := by
    intro a
    rw [hX0 a]
    simp [Sat, M.sat_fApp, M.sat_fApp3, Function.update_apply]
  obtain ⟨b0, -, -, huniq⟩ := h.full i hi X hXs (fun a ha => ((hX a).mp ha).1)
  have e1 : b = b0 := huniq b hb hX
  have e2 : b' = b0 := huniq b' hb' (fun a => (hX a).trans
    ⟨fun ⟨h1, h2⟩ => ⟨h1, (hext a h1).mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (hext a h1).mpr h2⟩⟩)
  rw [e1, e2]

/-- Every rung is a set. -/
theorem rung_set (R : V) (i : V) : ∃ D, M.isSet D ∧ ∀ a, M.mem a D ↔ M.mem (M.op i a) R := by
  obtain ⟨D, hDs, hD0⟩ := M.comp (σW [(1, 5)]) (fApp 1 2 0) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 R) 2 i)
  refine ⟨D, hDs, fun a => ?_⟩
  rw [hD0 a]
  simp [M.sat_fApp, Function.update_apply]

theorem rung_nonempty {R E z S : V} {m : M.Num} (h : M.IsLadder R E z S m) {j : M.Num}
    (hj : j ≤ m) : ∃ a, M.mem (M.op j.1 a) R := by
  rcases M.num_cases j with e | ⟨k, e⟩
  · refine ⟨z, ?_⟩
    rw [e]
    exact h.zero_mem
  · have hk : k + 1 ≤ m := by
      rw [← M.nsucc_eq_add_one, ← e]
      exact hj
    obtain ⟨b, hb, -⟩ := h.full k hk M.emp M.emp_isSet (fun a ha => absurd ha (M.not_mem_emp a))
    refine ⟨b, ?_⟩
    rw [e, M.nsucc_eq_add_one]
    exact hb

/-- Every rung has two different members. -/
theorem rung_two {R E z S : V} {m : M.Num} (h : M.IsLadder R E z S m) {j : M.Num}
    (hj : j ≤ m) : ∃ u v, M.mem (M.op j.1 u) R ∧ M.mem (M.op j.1 v) R ∧ u ≠ v := by
  rcases M.num_cases j with e | ⟨k, e⟩
  · obtain ⟨b, hb, hzb, -⟩ := h.succ_fun z h.zero_mem
    refine ⟨z, b, ?_, ?_, fun hzb' => ?_⟩
    · rw [e]
      exact h.zero_mem
    · rw [e]
      exact hb
    · rw [← hzb'] at hzb
      exact h.zero_ne z hzb
  · have hk : k + 1 ≤ m := by
      rw [← M.nsucc_eq_add_one, ← e]
      exact hj
    obtain ⟨a0, ha0⟩ := M.rung_nonempty h (le_trans (M.le_add_one k) hk)
    obtain ⟨b, hb, hbe, -⟩ := h.full k hk M.emp M.emp_isSet
      (fun a ha => absurd ha (M.not_mem_emp a))
    obtain ⟨D, hDs, hD⟩ := M.rung_set R k.1
    obtain ⟨c, hc, hce, -⟩ := h.full k hk D hDs (fun a ha => (hD a).mp ha)
    refine ⟨b, c, ?_, ?_, fun hbc => ?_⟩
    · rw [e, M.nsucc_eq_add_one]
      exact hb
    · rw [e, M.nsucc_eq_add_one]
      exact hc
    · have h2 := (hce a0).mp ((hD a0).mpr ha0)
      rw [← hbc] at h2
      exact M.not_mem_emp a0 ((hbe a0).mpr h2)

/-! ### Pairing families -/

/-- `P` is a family of pairing functions on the rungs up to `i`: a set of quadruples
`⟨j, a, b, c⟩`, `j ≤ i`, which for each `j ≤ i` is the graph of an injection from pairs of
members of rung `j` into rung `j`. -/
structure IsPairing (R P : V) (i : M.Num) : Prop where
  dom : ∀ j a b c, M.mem (M.quad j a b c) P → (∃ k : M.Num, k.1 = j ∧ k ≤ i) ∧
    M.mem (M.op j a) R ∧ M.mem (M.op j b) R ∧ M.mem (M.op j c) R
  tot : ∀ j : M.Num, j ≤ i → ∀ a b, M.mem (M.op j.1 a) R → M.mem (M.op j.1 b) R →
    ∃ c, M.mem (M.quad j.1 a b c) P
  inj : ∀ j a b c a' b', M.mem (M.quad j a b c) P → M.mem (M.quad j a' b' c) P →
    a = a' ∧ b = b'
  fn : ∀ j a b c c', M.mem (M.quad j a b c) P → M.mem (M.quad j a b c') P → c = c'

/-- The same with the numbers as objects. -/
def PairingRaw (ad R P i : V) : Prop :=
  (∀ j a b c, M.mem (M.quad j a b c) P → M.LeRaw ad j i ∧
    M.mem (M.op j a) R ∧ M.mem (M.op j b) R ∧ M.mem (M.op j c) R) ∧
  (∀ j a b, M.LeRaw ad j i → M.mem (M.op j a) R → M.mem (M.op j b) R →
    ∃ c, M.mem (M.quad j a b c) P) ∧
  (∀ j a b c a' b', M.mem (M.quad j a b c) P → M.mem (M.quad j a' b' c) P →
    a = a' ∧ b = b') ∧
  (∀ j a b c c', M.mem (M.quad j a b c) P → M.mem (M.quad j a b c') P → c = c')

theorem leRaw_num {ad : V} (had : M.IsGraphOf₂ ad M.addN) {j : V} {i : M.Num}
    (h : M.LeRaw ad j i.1) : ∃ k : M.Num, k.1 = j ∧ k ≤ i := by
  obtain ⟨c, hc, htr⟩ := h
  obtain ⟨k, n, hk, hn, hkn⟩ := (had _ _ _).mp htr
  exact ⟨k, hk, M.le_def.mpr ⟨n, Subtype.ext hkn⟩⟩

theorem pairingRaw_iff {ad : V} (had : M.IsGraphOf₂ ad M.addN) (R P : V) (i : M.Num) :
    M.PairingRaw ad R P i.1 ↔ M.IsPairing R P i := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun j a b c hq => ?_, fun j hj a b ha hb => ?_, h3, h4⟩
    · obtain ⟨hle, ha, hb, hc⟩ := h1 j a b c hq
      exact ⟨M.leRaw_num had hle, ha, hb, hc⟩
    · exact h2 j.1 a b ((M.leRaw_iff had j i).mpr hj) ha hb
  · intro h
    refine ⟨fun j a b c hq => ?_, fun j a b hle ha hb => ?_, h.inj, h.fn⟩
    · obtain ⟨⟨k, hk, hki⟩, ha, hb, hc⟩ := h.dom j a b c hq
      refine ⟨?_, ha, hb, hc⟩
      rw [← hk]
      exact (M.leRaw_iff had k i).mpr hki
    · obtain ⟨k, hk, hki⟩ := M.leRaw_num had hle
      rw [← hk] at ha hb ⊢
      exact h.tot k hki a b ha hb

/-- "`P` (name `3`) is a pairing family up to `i` (name `0`) for the rungs `R` (name `1`)";
the names `6`, `7` stand for `ℕ` and the graph of addition. -/
def pairingFml : Fml :=
  .and (.all 8 (.all 9 (.all 10 (.all 11 (Fml.imp (fApp4 3 8 9 10 11)
    (.and (fLe 8 0) (.and (fApp 1 8 9) (.and (fApp 1 8 10) (fApp 1 8 11)))))))))
  (.and (.all 8 (.all 9 (.all 10 (Fml.imp (fLe 8 0) (Fml.imp (fApp 1 8 9)
    (Fml.imp (fApp 1 8 10) (Fml.ex 11 (fApp4 3 8 9 10 11))))))))
  (.and (.all 8 (.all 9 (.all 10 (.all 11 (.all 12 (.all 13 (Fml.imp (fApp4 3 8 9 10 11)
    (Fml.imp (fApp4 3 8 12 13 11) (.and (.eq 9 12) (.eq 10 13))))))))))
  (.all 8 (.all 9 (.all 10 (.all 11 (.all 12 (Fml.imp (fApp4 3 8 9 10 11)
    (Fml.imp (fApp4 3 8 9 10 12) (.eq 11 12))))))))))

/-- "If `k ≤ m` then there is a pairing family up to `k`", `k` the name `0`, `m` the
name `16`. -/
def hasPairingFml : Fml := Fml.imp (fLe 0 16) (Fml.ex 3 pairingFml)

def σPr : ℕ → ℕ := σW [(1, 5), (3, 7), (6, 3), (7, 7)]

/-- The pairing of rung `0`, through the isomorphism with `ℕ`. -/
def basePairFml : Fml :=
  Fml.ex 9 (Fml.ex 10 (Fml.ex 11 (.and (fQuad 0 5 9 10 11) (Fml.ex 12 (Fml.ex 13 (Fml.ex 15
    (.and (fApp 4 12 9) (.and (fApp 4 13 10) (.and (fApp 4 15 11) (fPairN 15 12 13))))))))))

theorem pairing_zero {R E z S : V} {m : M.Num} (h : M.IsLadder R E z S m) :
    ∃ P, M.IsPairing R P 0 := by
  have had := M.adG_spec
  have hmu := M.muG_spec
  obtain ⟨f, hf1, hf2, hf3, -, -⟩ := M.ladder_base_iso h
  obtain ⟨P, -, hP0⟩ := M.comp (σW [(0, 6), (4, 5), (7, 7), (18, 7)]) basePairFml 0 rfl
    (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 4 f)
      5 M.zero) 7 M.adG) 18 M.muG)
  have hP : ∀ q, M.mem q P ↔ ∃ a b c, q = M.quad M.zero a b c ∧ ∃ k l n,
      M.mem (M.op k a) f ∧ M.mem (M.op l b) f ∧ M.mem (M.op n c) f ∧
      M.PairRaw M.adG M.muG k l n := by
    intro q
    rw [hP0 q]
    simp [basePairFml, Sat, M.sat_ex, M.sat_fQuad, M.sat_fApp, M.sat_fPairN,
      Function.update_apply]
  -- unpacking a member
  have unpack : ∀ {j a b c : V}, M.mem (M.quad j a b c) P → j = M.zero ∧ ∃ X Y : M.Num,
      M.mem (M.op X.1 a) f ∧ M.mem (M.op Y.1 b) f ∧ M.mem (M.op (M.pairN X Y).1 c) f := by
    intro j a b c hq
    obtain ⟨a', b', c', e, k, l, n, hk, hl, hn, hp⟩ := (hP _).mp hq
    obtain ⟨e1, e2, e3, e4⟩ := M.quad_inj e
    obtain ⟨X, Y, hX, hY, hc⟩ := (M.pairRaw_iff had hmu _ _ _).mp hp
    rw [← hX, ← e2] at hk
    rw [← hY, ← e3] at hl
    rw [hc, ← e4] at hn
    exact ⟨e1, X, Y, hk, hl, hn⟩
  have inR : ∀ {X : M.Num} {a : V}, M.mem (M.op X.1 a) f → M.mem (M.op M.zero a) R := by
    intro X a ha
    obtain ⟨a0, ha0, -, hu⟩ := hf1 X
    rw [hu a ha]
    exact ha0
  have funf : ∀ {X : M.Num} {a a' : V}, M.mem (M.op X.1 a) f → M.mem (M.op X.1 a') f →
      a = a' := by
    intro X a a' ha ha'
    obtain ⟨a0, -, -, hu⟩ := hf1 X
    rw [hu a ha, hu a' ha']
  refine ⟨P, fun j a b c hq => ?_, fun j hj a b ha hb => ?_, fun j a b c a' b' hq hq' => ?_,
    fun j a b c c' hq hq' => ?_⟩
  · obtain ⟨e, X, Y, hX, hY, hc⟩ := unpack hq
    rw [e]
    exact ⟨⟨0, rfl, le_refl 0⟩, inR hX, inR hY, inR hc⟩
  · have e : j = 0 := le_antisymm hj zero_le
    rw [e] at ha hb ⊢
    obtain ⟨X, hX⟩ := hf3 a ha
    obtain ⟨Y, hY⟩ := hf3 b hb
    obtain ⟨c, -, hc, -⟩ := hf1 (M.pairN X Y)
    exact ⟨c, (hP _).mpr ⟨a, b, c, rfl, X.1, Y.1, (M.pairN X Y).1, hX, hY, hc,
      (M.pairRaw_iff had hmu _ _ _).mpr ⟨X, Y, rfl, rfl, rfl⟩⟩⟩
  · obtain ⟨-, X, Y, hX, hY, hc⟩ := unpack hq
    obtain ⟨-, X', Y', hX', hY', hc'⟩ := unpack hq'
    obtain ⟨e1, e2⟩ := M.pairN_inj (hf2 _ _ c hc hc')
    rw [← e1] at hX'
    rw [← e2] at hY'
    exact ⟨funf hX hX', funf hY hY'⟩
  · obtain ⟨-, X, Y, hX, hY, hc⟩ := unpack hq
    obtain ⟨-, X', Y', hX', hY', hc'⟩ := unpack hq'
    have e1 : X = X' := hf2 _ _ a hX hX'
    have e2 : Y = Y' := hf2 _ _ b hY hY'
    rw [← e1, ← e2] at hc'
    exact funf hc hc'

/-- The members of the code of the pair `(x, y)` on the next rung: the pairs `(u, a)` with
`a` in `x` and the pairs `(v, b)` with `b` in `y`. -/
def PStep (R E P k u v x y p : V) : Prop :=
  (∃ a, M.mem (M.op k a) R ∧ M.mem (M.trip k a x) E ∧ M.mem (M.quad k u a p) P) ∨
  (∃ b, M.mem (M.op k b) R ∧ M.mem (M.trip k b y) E ∧ M.mem (M.quad k v b p) P)

/-- `PStep`, with `R`, `E`, `P`, `k`, `u`, `v`, `x`, `y`, `p` the names `1`, `2`, `3`, `4`,
`17`, `19`, `9`, `10`, `12`. -/
def pStepFml : Fml :=
  Fml.or (Fml.ex 13 (.and (fApp 1 4 13) (.and (fApp3 2 4 13 9) (fApp4 3 4 17 13 12))))
    (Fml.ex 13 (.and (fApp 1 4 13) (.and (fApp3 2 4 13 10) (fApp4 3 4 19 13 12))))

theorem sat_pStepFml (ρ : ℕ → V) : Sat M.mem M.isSet pStepFml ρ ↔
    M.PStep (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 17) (ρ 19) (ρ 9) (ρ 10) (ρ 12) := by
  simp [pStepFml, PStep, Sat, M.sat_or, M.sat_ex, M.sat_fApp, M.sat_fApp3, M.sat_fApp4,
    Function.update_apply]

/-- The new pairing family: the old one and the pairs of the next rung (name `5`). -/
def nextPairFml : Fml :=
  Fml.or (.mem 0 3) (Fml.ex 9 (Fml.ex 10 (Fml.ex 11 (.and (fQuad 0 5 9 10 11)
    (.and (fApp 1 5 9) (.and (fApp 1 5 10) (.and (fApp 1 5 11)
    (.all 12 (Fml.iff (.and (fApp 1 4 12) (fApp3 2 4 12 11)) pStepFml)))))))))

/-- **A pairing family extends to the next rung.** -/
theorem pairing_succ {R E z S : V} {m : M.Num} (h : M.IsLadder R E z S m) {k : M.Num}
    (hk : k + 1 ≤ m) {P : V} (hP : M.IsPairing R P k) : ∃ P', M.IsPairing R P' (k + 1) := by
  have hkm : k ≤ m := le_trans (M.le_add_one k) hk
  obtain ⟨u, v, hu, hv, huv⟩ := M.rung_two h hkm
  obtain ⟨P', -, hP0⟩ := M.comp (σW [(0, 6), (1, 5), (2, 7), (3, 7)]) nextPairFml 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (fun _ => dflt) 1 R) 2 E) 3 P) 4 k.1) 5 (k + 1).1)
      17 u) 19 v)
  have hP' : ∀ q, M.mem q P' ↔ M.mem q P ∨ ∃ x y c, q = M.quad (k + 1).1 x y c ∧
      M.mem (M.op (k + 1).1 x) R ∧ M.mem (M.op (k + 1).1 y) R ∧ M.mem (M.op (k + 1).1 c) R ∧
      ∀ p, (M.mem (M.op k.1 p) R ∧ M.mem (M.trip k.1 p c) E) ↔ M.PStep R E P k.1 u v x y p := by
    intro q
    rw [hP0 q]
    simp [nextPairFml, Sat, M.sat_or, M.sat_ex, M.sat_iff, M.sat_fQuad, M.sat_fApp, M.sat_fApp3,
      M.sat_pStepFml, Function.update_apply]
  -- a quadruple of the new family is old or new
  have split : ∀ {j a b c : V}, M.mem (M.quad j a b c) P' →
      (M.mem (M.quad j a b c) P ∧ ∃ kk : M.Num, kk.1 = j ∧ kk ≤ k) ∨
      (j = (k + 1).1 ∧ M.mem (M.op (k + 1).1 a) R ∧ M.mem (M.op (k + 1).1 b) R ∧
        M.mem (M.op (k + 1).1 c) R ∧
        ∀ p, (M.mem (M.op k.1 p) R ∧ M.mem (M.trip k.1 p c) E) ↔
          M.PStep R E P k.1 u v a b p) := by
    intro j a b c hq
    rcases (hP' _).mp hq with hq | ⟨x, y, c', e, hx, hy, hc, hall⟩
    · exact Or.inl ⟨hq, (hP.dom j a b c hq).1⟩
    · obtain ⟨e1, e2, e3, e4⟩ := M.quad_inj e
      rw [← e2] at hx hall
      rw [← e3] at hy hall
      rw [← e4] at hc hall
      exact Or.inr ⟨e1, hx, hy, hc, hall⟩
  have clash : ∀ {j : V}, (∃ kk : M.Num, kk.1 = j ∧ kk ≤ k) → j = (k + 1).1 → False := by
    rintro j ⟨kk, hkk, hle⟩ e
    have e' : kk = k + 1 := Subtype.ext (hkk.trans e)
    rw [e'] at hle
    exact M.not_succ_le k hle
  -- the two tags keep the two halves apart
  have key : ∀ {x y x' y' : V}, (∀ p, M.PStep R E P k.1 u v x y p →
      M.PStep R E P k.1 u v x' y' p) →
      (∀ a, M.mem (M.op k.1 a) R → M.mem (M.trip k.1 a x) E → M.mem (M.trip k.1 a x') E) ∧
      (∀ b, M.mem (M.op k.1 b) R → M.mem (M.trip k.1 b y) E → M.mem (M.trip k.1 b y') E) := by
    intro x y x' y' himp
    constructor
    · intro a ha hax
      obtain ⟨p, hp⟩ := hP.tot k (le_refl k) u a hu ha
      rcases himp p (Or.inl ⟨a, ha, hax, hp⟩) with ⟨a', -, hax', hp'⟩ | ⟨b', -, -, hp'⟩
      · obtain ⟨-, e⟩ := hP.inj _ _ _ _ _ _ hp hp'
        rw [e]
        exact hax'
      · exact absurd (hP.inj _ _ _ _ _ _ hp hp').1 huv
    · intro b hb hby
      obtain ⟨p, hp⟩ := hP.tot k (le_refl k) v b hv hb
      rcases himp p (Or.inr ⟨b, hb, hby, hp⟩) with ⟨a', -, -, hp'⟩ | ⟨b', -, hby', hp'⟩
      · exact absurd (hP.inj _ _ _ _ _ _ hp hp').1.symm huv
      · obtain ⟨-, e⟩ := hP.inj _ _ _ _ _ _ hp hp'
        rw [e]
        exact hby'
  refine ⟨P', fun j a b c hq => ?_, fun j hj a b ha hb => ?_, fun j a b c a' b' hq hq' => ?_,
    fun j a b c c' hq hq' => ?_⟩
  · rcases split hq with ⟨hq, kk, hkk, hle⟩ | ⟨e, ha, hb, hc, -⟩
    · exact ⟨⟨kk, hkk, le_trans hle (M.le_add_one k)⟩, (hP.dom j a b c hq).2⟩
    · rw [e]
      exact ⟨⟨k + 1, rfl, le_refl _⟩, ha, hb, hc⟩
  · rcases M.eq_or_succ_le hj with e | hlt
    · rw [e] at ha hb ⊢
      -- the set of members of the code
      obtain ⟨X, hXs, hX0⟩ := M.comp (σW [(1, 5), (2, 7), (3, 7)]) pStepFml 12 rfl
        (Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (fun _ => dflt) 1 R) 2 E) 3 P)
          4 k.1) 17 u) 19 v) 9 a) 10 b)
      have hX : ∀ p, M.mem p X ↔ M.PStep R E P k.1 u v a b p := by
        intro p
        rw [hX0 p, M.sat_pStepFml]
        simp [Function.update_apply]
      have hXR : ∀ p, M.mem p X → M.mem (M.op k.1 p) R := by
        intro p hp
        rcases (hX p).mp hp with ⟨a', -, -, hq⟩ | ⟨b', -, -, hq⟩
        · exact (hP.dom _ _ _ _ hq).2.2.2
        · exact (hP.dom _ _ _ _ hq).2.2.2
      obtain ⟨c, hc, hce, -⟩ := h.full k hk X hXs hXR
      exact ⟨c, (hP' _).mpr (Or.inr ⟨a, b, c, rfl, ha, hb, hc,
        fun p => (hce p).symm.trans (hX p)⟩)⟩
    · obtain ⟨c, hc⟩ := hP.tot j (M.le_of_succ_le_succ hlt) a b ha hb
      exact ⟨c, (hP' _).mpr (Or.inl hc)⟩
  · rcases split hq with ⟨hq, hk1⟩ | ⟨e, ha, hb, hc, hall⟩
    · rcases split hq' with ⟨hq', -⟩ | ⟨e', -⟩
      · exact hP.inj _ _ _ _ _ _ hq hq'
      · exact absurd e' (fun e' => clash hk1 e')
    · rcases split hq' with ⟨-, hk1⟩ | ⟨-, ha', hb', -, hall'⟩
      · exact absurd e (fun e => clash hk1 e)
      · have h1 := key (x := a) (y := b) (x' := a') (y' := b')
          (fun p hp => (hall' p).mp ((hall p).mpr hp))
        have h2 := key (x := a') (y := b') (x' := a) (y' := b)
          (fun p hp => (hall p).mp ((hall' p).mpr hp))
        exact ⟨M.rung_ext h hk ha ha' (fun t ht => ⟨h1.1 t ht, h2.1 t ht⟩),
          M.rung_ext h hk hb hb' (fun t ht => ⟨h1.2 t ht, h2.2 t ht⟩)⟩
  · rcases split hq with ⟨hq, hk1⟩ | ⟨e, -, -, hc, hall⟩
    · rcases split hq' with ⟨hq', -⟩ | ⟨e', -⟩
      · exact hP.fn _ _ _ _ _ hq hq'
      · exact absurd e' (fun e' => clash hk1 e')
    · rcases split hq' with ⟨-, hk1⟩ | ⟨-, -, -, hc', hall'⟩
      · exact absurd e (fun e => clash hk1 e)
      · exact M.rung_ext h hk hc hc' (fun t ht =>
          ⟨fun hE => ((hall' t).mpr ((hall t).mp ⟨ht, hE⟩)).2,
            fun hE => ((hall t).mpr ((hall' t).mp ⟨ht, hE⟩)).2⟩)

/-- **Pairing on the rungs** (§3.3, step 1). Every ladder has a pairing family for all its
rungs. The proof is an induction on `k ≤ m` for a stratified condition. -/
theorem exists_pairing {R E z S : V} {m : M.Num} (h : M.IsLadder R E z S m) :
    ∃ P, M.IsPairing R P m := by
  have had := M.adG_spec
  have hsat : ∀ k : V, Sat M.mem M.isSet hasPairingFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 1 R) 6 M.nat)
        7 M.adG) 16 m.1) 0 k) ↔
      (M.LeRaw M.adG k m.1 → ∃ P, M.PairingRaw M.adG R P k) := by
    intro k
    simp [hasPairingFml, pairingFml, fLe, PairingRaw, LeRaw, Sat, M.sat_imp, M.sat_ex,
      M.sat_fApp, M.sat_fApp3, M.sat_fApp4, Function.update_apply]
  have h0 : Sat M.mem M.isSet hasPairingFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 1 R) 6 M.nat)
        7 M.adG) 16 m.1) 0 M.zero) := by
    rw [hsat]
    intro _
    obtain ⟨P, hP⟩ := M.pairing_zero h
    exact ⟨P, (M.pairingRaw_iff had R P 0).mpr hP⟩
  have hs : ∀ k : M.Num, Sat M.mem M.isSet hasPairingFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 1 R) 6 M.nat)
        7 M.adG) 16 m.1) 0 k.1) →
      Sat M.mem M.isSet hasPairingFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 1 R) 6 M.nat)
        7 M.adG) 16 m.1) 0 (M.succ k.1)) := by
    intro k ih
    rw [hsat] at ih ⊢
    intro hle
    have hle' : k + 1 ≤ m := by
      rw [← M.nsucc_eq_add_one]
      exact (M.leRaw_iff had (M.nsucc k) m).mp hle
    have hk : k ≤ m := le_trans (M.le_add_one k) hle'
    obtain ⟨P, hP⟩ := ih ((M.leRaw_iff had k m).mpr hk)
    obtain ⟨P', hP'⟩ := M.pairing_succ h hle' ((M.pairingRaw_iff had R P k).mp hP)
    refine ⟨P', ?_⟩
    have h9 := (M.pairingRaw_iff had R P' (k + 1)).mpr hP'
    rw [M.val_add_one] at h9
    exact h9
  have key := M.num_ind_fml σPr hasPairingFml 0 rfl _ h0 hs m
  rw [hsat] at key
  obtain ⟨P, hP⟩ := key ((M.leRaw_iff had m m).mpr (le_refl m))
  exact ⟨P, (M.pairingRaw_iff had R P m).mp hP⟩

/-! ### Relations on a rung are coded on the next rung -/

/-- **Every set relation on a rung is coded by a member of the next rung** (§3.3, first
consequence of fullness): the code has as members the pairs of the relation. -/
theorem rel_code {R E z S : V} {m : M.Num} (h : M.IsLadder R E z S m) {P : V}
    (hP : M.IsPairing R P m) {i : M.Num} (hi : i + 1 ≤ m) {r : V}
    (hr : ∀ a b, M.mem (M.op a b) r → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) :
    ∃ c, M.mem (M.op (i + 1).1 c) R ∧ ∀ a b, M.mem (M.op a b) r ↔
      ∃ p, M.mem (M.quad i.1 a b p) P ∧ M.mem (M.trip i.1 p c) E := by
  have him : i ≤ m := le_trans (M.le_add_one i) hi
  obtain ⟨X, hXs, hX0⟩ := M.comp (σW [(3, 7), (4, 5)])
    (Fml.ex 9 (Fml.ex 10 (.and (fApp 4 9 10) (fApp4 3 5 9 10 0)))) 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 3 P) 4 r) 5 i.1)
  have hX : ∀ p, M.mem p X ↔ ∃ a b, M.mem (M.op a b) r ∧ M.mem (M.quad i.1 a b p) P := by
    intro p
    rw [hX0 p]
    simp [Sat, M.sat_ex, M.sat_fApp, M.sat_fApp4, Function.update_apply]
  obtain ⟨c, hc, hce, -⟩ := h.full i hi X hXs (fun p hp => by
    obtain ⟨a, b, -, hq⟩ := (hX p).mp hp
    exact (hP.dom _ _ _ _ hq).2.2.2)
  refine ⟨c, hc, fun a b => ⟨fun hab => ?_, ?_⟩⟩
  · obtain ⟨ha, hb⟩ := hr a b hab
    obtain ⟨p, hp⟩ := hP.tot i him a b ha hb
    exact ⟨p, hp, ((hce p).mp ((hX p).mpr ⟨a, b, hab, hp⟩)).2⟩
  · rintro ⟨p, hq, hE⟩
    obtain ⟨a', b', hab', hq'⟩ := (hX p).mp ((hce p).mpr ⟨(hP.dom _ _ _ _ hq).2.2.2, hE⟩)
    obtain ⟨e1, e2⟩ := hP.inj _ _ _ _ _ _ hq hq'
    rw [e1, e2]
    exact hab'

/-- Conversely the relation coded by a member of a rung is a set. -/
theorem rel_decode (R E P : V) (i c : V) : ∃ r, M.isSet r ∧
    (∀ t, M.mem t r → ∃ a b, t = M.op a b) ∧
    ∀ a b, M.mem (M.op a b) r ↔ ∃ p, M.mem (M.quad i a b p) P ∧ M.mem (M.trip i p c) E := by
  obtain ⟨r, hrs, hr0⟩ := M.comp (σW [(0, 4), (2, 7), (3, 7)])
    (Fml.ex 9 (Fml.ex 10 (Fml.ex 11 (.and (fPr 0 9 10) (.and (fApp4 3 5 9 10 11)
      (fApp3 2 5 11 4)))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 2 E)
      3 P) 4 c) 5 i)
  have hr : ∀ t, M.mem t r ↔ ∃ a b p, t = M.op a b ∧ M.mem (M.quad i a b p) P ∧
      M.mem (M.trip i p c) E := by
    intro t
    rw [hr0 t]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp3, M.sat_fApp4, Function.update_apply]
  refine ⟨r, hrs, fun t ht => ?_, fun a b => ⟨fun hab => ?_, ?_⟩⟩
  · obtain ⟨a, b, p, e, -⟩ := (hr t).mp ht
    exact ⟨a, b, e⟩
  · obtain ⟨a', b', p, e, hq, hE⟩ := (hr _).mp hab
    obtain ⟨e1, e2⟩ := M.op_inj e
    rw [e1, e2]
    exact ⟨p, hq, hE⟩
  · rintro ⟨p, hq, hE⟩
    exact (hr _).mpr ⟨a, b, p, rfl, hq, hE⟩

/-! ## Well-orderings that are sets (§3.3, step 2)

A well-ordering is a set `r` of pairs, reflexive on its field, such that every set that meets
the field has a least member. Everything here is for an arbitrary model of NFU; the two
orderings compared must have their points at one type. -/

/-- `r` is a (reflexive) well-ordering of its field `{a : ⟨a, a⟩ ∈ r}`. -/
structure IsWO (r : V) : Prop where
  fld : ∀ a b, M.mem (M.op a b) r → M.mem (M.op a a) r ∧ M.mem (M.op b b) r
  trans : ∀ a b c, M.mem (M.op a b) r → M.mem (M.op b c) r → M.mem (M.op a c) r
  antisymm : ∀ a b, M.mem (M.op a b) r → M.mem (M.op b a) r → a = b
  least : ∀ X, (∃ a, M.mem a X ∧ M.mem (M.op a a) r) →
    ∃ a, M.mem a X ∧ M.mem (M.op a a) r ∧
      ∀ b, M.mem b X → M.mem (M.op b b) r → M.mem (M.op a b) r

theorem wo_total {r : V} (hr : M.IsWO r) {a b : V} (ha : M.mem (M.op a a) r)
    (hb : M.mem (M.op b b) r) : M.mem (M.op a b) r ∨ M.mem (M.op b a) r := by
  obtain ⟨c, hc, -, hmin⟩ := hr.least (M.up a b) ⟨a, M.mem_up.mpr (Or.inl rfl), ha⟩
  rcases M.mem_up.mp hc with e | e
  · have h1 := hmin b (M.mem_up.mpr (Or.inr rfl)) hb
    rw [e] at h1
    exact Or.inl h1
  · have h1 := hmin a (M.mem_up.mpr (Or.inl rfl)) ha
    rw [e] at h1
    exact Or.inr h1

/-- `f` is an isomorphism between an initial segment of `r` and an initial segment of `s`. -/
def PIso (r s f : V) : Prop :=
  (∀ x y, M.mem (M.op x y) f → M.mem (M.op x x) r ∧ M.mem (M.op y y) s) ∧
  (∀ x y x' y', M.mem (M.op x y) f → M.mem (M.op x' y') f →
    (M.mem (M.op x x') r ↔ M.mem (M.op y y') s)) ∧
  (∀ x y x', M.mem (M.op x y) f → M.mem (M.op x' x) r → ∃ y', M.mem (M.op x' y') f) ∧
  (∀ x y y', M.mem (M.op x y) f → M.mem (M.op y' y) s → ∃ x', M.mem (M.op x' y') f)

/-- `PIso`, with `r`, `s`, `f` the names `1`, `2`, `3`. -/
def pisoFml : Fml :=
  .and (.all 8 (.all 9 (Fml.imp (fApp 3 8 9) (.and (fApp 1 8 8) (fApp 2 9 9)))))
  (.and (.all 8 (.all 9 (.all 10 (.all 11 (Fml.imp (fApp 3 8 9) (Fml.imp (fApp 3 10 11)
    (Fml.iff (fApp 1 8 10) (fApp 2 9 11))))))))
  (.and (.all 8 (.all 9 (.all 10 (Fml.imp (fApp 3 8 9) (Fml.imp (fApp 1 10 8)
    (Fml.ex 11 (fApp 3 10 11)))))))
  (.all 8 (.all 9 (.all 11 (Fml.imp (fApp 3 8 9) (Fml.imp (fApp 2 11 9)
    (Fml.ex 10 (fApp 3 10 11)))))))))

theorem sat_pisoFml (ρ : ℕ → V) :
    Sat M.mem M.isSet pisoFml ρ ↔ M.PIso (ρ 1) (ρ 2) (ρ 3) := by
  simp [pisoFml, PIso, Sat, M.sat_imp, M.sat_iff, M.sat_ex, M.sat_fApp, Function.update_apply]

theorem piso_fun {r s f : V} (hs : M.IsWO s) (hf : M.PIso r s f) {x y y' : V}
    (h1 : M.mem (M.op x y) f) (h2 : M.mem (M.op x y') f) : y = y' := by
  have hx := (hf.1 x y h1).1
  exact hs.antisymm y y' ((hf.2.1 x y x y' h1 h2).mp hx) ((hf.2.1 x y' x y h2 h1).mp hx)

theorem piso_inj {r s f : V} (hr : M.IsWO r) (hf : M.PIso r s f) {x x' y : V}
    (h1 : M.mem (M.op x y) f) (h2 : M.mem (M.op x' y) f) : x = x' := by
  have hy := (hf.1 x y h1).2
  exact hr.antisymm x x' ((hf.2.1 x y x' y h1 h2).mpr hy) ((hf.2.1 x' y x y h2 h1).mpr hy)

/-- Two partial isomorphisms between well-orderings agree where both are defined. -/
theorem piso_agree {r s f f' : V} (hr : M.IsWO r) (hs : M.IsWO s) (hf : M.PIso r s f)
    (hf' : M.PIso r s f') :
    ∀ x y y', M.mem (M.op x y) f → M.mem (M.op x y') f' → y = y' := by
  -- one-sided step
  have aux : ∀ {g g' : V}, M.PIso r s g → M.PIso r s g' → ∀ {x y y' : V},
      M.mem (M.op x y) g → M.mem (M.op x y') g' →
      (∀ x'' z z', M.mem (M.op x'' x) r → x'' ≠ x → M.mem (M.op x'' z) g →
        M.mem (M.op x'' z') g' → z = z') → M.mem (M.op y y') s → y = y' := by
    intro g g' hg hg' x y y' hxy hxy' ih hyy'
    by_contra hne
    obtain ⟨x'', hx''⟩ := hg'.2.2.2 x y' y hxy' hyy'
    have h1 : M.mem (M.op x'' x) r := (hg'.2.1 x'' y x y' hx'' hxy').mpr hyy'
    have h2 : x'' ≠ x := by
      intro e
      rw [e] at hx''
      exact hne (M.piso_fun hs hg' hx'' hxy')
    obtain ⟨z, hz⟩ := hg.2.2.1 x y x'' hxy h1
    have e : z = y := ih x'' z y h1 h2 hz hx''
    rw [e] at hz
    exact h2 (M.piso_inj hr hg hz hxy)
  obtain ⟨D, -, hD0⟩ := M.comp (σW [(3, 5), (4, 5)])
    (Fml.ex 9 (Fml.ex 11 (.and (fApp 3 0 9) (.and (fApp 4 0 11) (.neg (.eq 9 11)))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 3 f) 4 f')
  have hD : ∀ x, M.mem x D ↔ ∃ y y', M.mem (M.op x y) f ∧ M.mem (M.op x y') f' ∧ y ≠ y' := by
    intro x
    rw [hD0 x]
    simp [Sat, M.sat_ex, M.sat_fApp, Function.update_apply]
  intro x y y' hxy hxy'
  by_contra hne
  obtain ⟨x0, hx0, hx0r, hmin⟩ := hr.least D
    ⟨x, (hD x).mpr ⟨y, y', hxy, hxy', hne⟩, (hf.1 x y hxy).1⟩
  obtain ⟨y0, y0', h0, h0', hne0⟩ := (hD x0).mp hx0
  have ih : ∀ x'' z z', M.mem (M.op x'' x0) r → x'' ≠ x0 → M.mem (M.op x'' z) f →
      M.mem (M.op x'' z') f' → z = z' := by
    intro x'' z z' hle hne'' hz hz'
    by_contra hzz
    have h1 := hmin x'' ((hD x'').mpr ⟨z, z', hz, hz', hzz⟩) (hf.1 x'' z hz).1
    exact hne'' (hr.antisymm x'' x0 hle h1)
  rcases M.wo_total hs (hf.1 x0 y0 h0).2 (hf'.1 x0 y0' h0').2 with h | h
  · exact hne0 (aux hf hf' h0 h0' ih h)
  · exact hne0 (aux hf' hf h0' h0 (fun x'' z z' hle hne'' hz hz' =>
      (ih x'' z' z hle hne'' hz' hz).symm) h).symm

/-! ### Converse, composition, identity -/

theorem exists_conv (f : V) : ∃ g, M.isSet g ∧ ∀ x y, M.mem (M.op x y) g ↔ M.mem (M.op y x) f := by
  obtain ⟨g, hgs, hg0⟩ := M.comp (σW [(0, 4), (1, 5)])
    (Fml.ex 9 (Fml.ex 10 (.and (fPr 0 9 10) (fApp 1 10 9)))) 0 rfl
    (Function.update (fun _ => dflt) 1 f)
  have hg : ∀ t, M.mem t g ↔ ∃ x y, t = M.op x y ∧ M.mem (M.op y x) f := by
    intro t
    rw [hg0 t]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp, Function.update_apply]
  refine ⟨g, hgs, fun x y => ⟨fun h => ?_, fun h => (hg _).mpr ⟨x, y, rfl, h⟩⟩⟩
  obtain ⟨x', y', e, h'⟩ := (hg _).mp h
  obtain ⟨e1, e2⟩ := M.op_inj e
  rw [e1, e2]
  exact h'

/-- The converse of a set of pairs. -/
noncomputable def conv (f : V) : V := Classical.choose (M.exists_conv f)

theorem mem_conv {f x y : V} : M.mem (M.op x y) (M.conv f) ↔ M.mem (M.op y x) f :=
  (Classical.choose_spec (M.exists_conv f)).2 x y

theorem piso_conv {r s f : V} (hf : M.PIso r s f) : M.PIso s r (M.conv f) := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  refine ⟨fun x y h => ?_, fun x y x' y' h h' => ?_, fun x y x' h hle => ?_,
    fun x y y' h hle => ?_⟩
  · exact (h1 y x (M.mem_conv.mp h)).symm
  · exact (h2 y x y' x' (M.mem_conv.mp h) (M.mem_conv.mp h')).symm
  · obtain ⟨y', hy'⟩ := h4 y x x' (M.mem_conv.mp h) hle
    exact ⟨y', M.mem_conv.mpr hy'⟩
  · obtain ⟨x', hx'⟩ := h3 y x y' (M.mem_conv.mp h) hle
    exact ⟨x', M.mem_conv.mpr hx'⟩

theorem exists_rcomp (f g : V) : ∃ h, M.isSet h ∧
    ∀ x z, M.mem (M.op x z) h ↔ ∃ y, M.mem (M.op x y) f ∧ M.mem (M.op y z) g := by
  obtain ⟨h, hhs, hh0⟩ := M.comp (σW [(0, 4), (1, 5), (2, 5)])
    (Fml.ex 9 (Fml.ex 10 (Fml.ex 11 (.and (fPr 0 9 11) (.and (fApp 1 9 10) (fApp 2 10 11))))))
    0 rfl (Function.update (Function.update (fun _ => dflt) 1 f) 2 g)
  have hh : ∀ t, M.mem t h ↔ ∃ x y z, t = M.op x z ∧ M.mem (M.op x y) f ∧
      M.mem (M.op y z) g := by
    intro t
    rw [hh0 t]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp, Function.update_apply]
  refine ⟨h, hhs, fun x z => ⟨fun hxz => ?_, fun ⟨y, h1, h2⟩ => (hh _).mpr ⟨x, y, z, rfl, h1, h2⟩⟩⟩
  obtain ⟨x', y, z', e, h1, h2⟩ := (hh _).mp hxz
  obtain ⟨e1, e2⟩ := M.op_inj e
  rw [e1, e2]
  exact ⟨y, h1, h2⟩

/-- Composition of sets of pairs: first `f`, then `g`. -/
noncomputable def rcomp (f g : V) : V := Classical.choose (M.exists_rcomp f g)

theorem mem_rcomp {f g x z : V} :
    M.mem (M.op x z) (M.rcomp f g) ↔ ∃ y, M.mem (M.op x y) f ∧ M.mem (M.op y z) g :=
  (Classical.choose_spec (M.exists_rcomp f g)).2 x z

theorem piso_rcomp {r s t f g : V} (hf : M.PIso r s f) (hg : M.PIso s t g) :
    M.PIso r t (M.rcomp f g) := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  obtain ⟨g1, g2, g3, g4⟩ := hg
  refine ⟨fun x z h => ?_, fun x z x' z' h h' => ?_, fun x z x' h hle => ?_,
    fun x z z' h hle => ?_⟩
  · obtain ⟨y, hxy, hyz⟩ := M.mem_rcomp.mp h
    exact ⟨(f1 x y hxy).1, (g1 y z hyz).2⟩
  · obtain ⟨y, hxy, hyz⟩ := M.mem_rcomp.mp h
    obtain ⟨y', hxy', hyz'⟩ := M.mem_rcomp.mp h'
    exact (f2 x y x' y' hxy hxy').trans (g2 y z y' z' hyz hyz')
  · obtain ⟨y, hxy, hyz⟩ := M.mem_rcomp.mp h
    obtain ⟨y', hxy'⟩ := f3 x y x' hxy hle
    obtain ⟨z', hyz'⟩ := g3 y z y' hyz ((f2 x' y' x y hxy' hxy).mp hle)
    exact ⟨z', M.mem_rcomp.mpr ⟨y', hxy', hyz'⟩⟩
  · obtain ⟨y, hxy, hyz⟩ := M.mem_rcomp.mp h
    obtain ⟨y', hyz'⟩ := g4 y z z' hyz hle
    obtain ⟨x', hxy'⟩ := f4 x y y' hxy ((g2 y' z' y z hyz' hyz).mpr hle)
    exact ⟨x', M.mem_rcomp.mpr ⟨y', hxy', hyz'⟩⟩

theorem exists_idf (r : V) : ∃ g, M.isSet g ∧
    ∀ x y, M.mem (M.op x y) g ↔ x = y ∧ M.mem (M.op x x) r := by
  obtain ⟨g, hgs, hg0⟩ := M.comp (σW [(0, 4), (1, 5)])
    (Fml.ex 9 (.and (fPr 0 9 9) (fApp 1 9 9))) 0 rfl (Function.update (fun _ => dflt) 1 r)
  have hg : ∀ t, M.mem t g ↔ ∃ x, t = M.op x x ∧ M.mem (M.op x x) r := by
    intro t
    rw [hg0 t]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp, Function.update_apply]
  refine ⟨g, hgs, fun x y => ⟨fun h => ?_, fun ⟨e, h⟩ => (hg _).mpr ⟨x, by rw [e], h⟩⟩⟩
  obtain ⟨x', e, h'⟩ := (hg _).mp h
  obtain ⟨e1, e2⟩ := M.op_inj e
  rw [e1, e2]
  exact ⟨rfl, h'⟩

/-- The identity on the field of `r`. -/
noncomputable def idf (r : V) : V := Classical.choose (M.exists_idf r)

theorem mem_idf {r x y : V} : M.mem (M.op x y) (M.idf r) ↔ x = y ∧ M.mem (M.op x x) r :=
  (Classical.choose_spec (M.exists_idf r)).2 x y

theorem piso_idf {r : V} (hr : M.IsWO r) : M.PIso r r (M.idf r) := by
  refine ⟨fun x y h => ?_, fun x y x' y' h h' => ?_, fun x y x' h hle => ?_,
    fun x y y' h hle => ?_⟩
  · obtain ⟨e, hx⟩ := M.mem_idf.mp h
    rw [← e]
    exact ⟨hx, hx⟩
  · obtain ⟨e, -⟩ := M.mem_idf.mp h
    obtain ⟨e', -⟩ := M.mem_idf.mp h'
    rw [e, e']
  · exact ⟨x', M.mem_idf.mpr ⟨rfl, (hr.fld x' x hle).1⟩⟩
  · exact ⟨y', M.mem_idf.mpr ⟨rfl, (hr.fld y' y hle).1⟩⟩

/-! ### Comparability -/

/-- **Comparability of well-orderings.** For two set well-orderings with points of one type
there is a set isomorphism between initial segments of them which is defined on the whole
of the first or onto the whole of the second. -/
theorem wo_compare {r s : V} (hr : M.IsWO r) (hs : M.IsWO s) :
    ∃ F, M.PIso r s F ∧ ((∀ x, M.mem (M.op x x) r → ∃ y, M.mem (M.op x y) F) ∨
      (∀ y, M.mem (M.op y y) s → ∃ x, M.mem (M.op x y) F)) := by
  obtain ⟨F, -, hF0⟩ := M.comp (σW [(0, 4), (1, 5), (2, 5), (3, 5)])
    (Fml.ex 3 (.and pisoFml (.mem 0 3))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 r) 2 s)
  have hF : ∀ t, M.mem t F ↔ ∃ f, M.PIso r s f ∧ M.mem t f := by
    intro t
    rw [hF0 t]
    simp [Sat, M.sat_ex, M.sat_pisoFml, Function.update_apply]
  have hFp : M.PIso r s F := by
    refine ⟨fun x y h => ?_, fun x y x' y' h h' => ?_, fun x y x' h hle => ?_,
      fun x y y' h hle => ?_⟩
    · obtain ⟨f, hf, hm⟩ := (hF _).mp h
      exact hf.1 x y hm
    · obtain ⟨f, hf, hm⟩ := (hF _).mp h
      obtain ⟨f', hf', hm'⟩ := (hF _).mp h'
      rcases M.wo_total hr (hf.1 x y hm).1 (hf'.1 x' y' hm').1 with hle | hle
      · obtain ⟨y'', hy''⟩ := hf'.2.2.1 x' y' x hm' hle
        have e : y = y'' := M.piso_agree hr hs hf hf' x y y'' hm hy''
        rw [← e] at hy''
        exact hf'.2.1 x y x' y' hy'' hm'
      · obtain ⟨y'', hy''⟩ := hf.2.2.1 x y x' hm hle
        have e : y'' = y' := M.piso_agree hr hs hf hf' x' y'' y' hy'' hm'
        rw [e] at hy''
        exact hf.2.1 x y x' y' hm hy''
    · obtain ⟨f, hf, hm⟩ := (hF _).mp h
      obtain ⟨y', hy'⟩ := hf.2.2.1 x y x' hm hle
      exact ⟨y', (hF _).mpr ⟨f, hf, hy'⟩⟩
    · obtain ⟨f, hf, hm⟩ := (hF _).mp h
      obtain ⟨x', hx'⟩ := hf.2.2.2 x y y' hm hle
      exact ⟨x', (hF _).mpr ⟨f, hf, hx'⟩⟩
  refine ⟨F, hFp, ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  rw [not_forall] at hc1 hc2
  obtain ⟨x0, hx0⟩ := hc1
  obtain ⟨y0, hy0⟩ := hc2
  rw [Classical.not_imp] at hx0 hy0
  obtain ⟨A, -, hA0⟩ := M.comp (σW [(1, 5)]) (.neg (Fml.ex 9 (fApp 1 0 9))) 0 rfl
    (Function.update (fun _ => dflt) 1 F)
  have hA : ∀ x, M.mem x A ↔ ¬ ∃ y, M.mem (M.op x y) F := by
    intro x
    rw [hA0 x]
    simp [Sat, M.sat_ex, M.sat_fApp, Function.update_apply]
  obtain ⟨B, -, hB0⟩ := M.comp (σW [(1, 5)]) (.neg (Fml.ex 9 (fApp 1 9 0))) 0 rfl
    (Function.update (fun _ => dflt) 1 F)
  have hB : ∀ y, M.mem y B ↔ ¬ ∃ x, M.mem (M.op x y) F := by
    intro y
    rw [hB0 y]
    simp [Sat, M.sat_ex, M.sat_fApp, Function.update_apply]
  obtain ⟨a, haA, har, hamin⟩ := hr.least A ⟨x0, (hA x0).mpr hx0.2, hx0.1⟩
  obtain ⟨b, hbB, hbs, hbmin⟩ := hs.least B ⟨y0, (hB y0).mpr hy0.2, hy0.1⟩
  have haF : ¬ ∃ y, M.mem (M.op a y) F := (hA a).mp haA
  have hbF : ¬ ∃ x, M.mem (M.op x b) F := (hB b).mp hbB
  -- members of `F` lie strictly below `(a, b)`
  have below : ∀ x y, M.mem (M.op x y) F → (M.mem (M.op x a) r ∧ ¬ M.mem (M.op a x) r) ∧
      (M.mem (M.op y b) s ∧ ¬ M.mem (M.op b y) s) := by
    intro x y h
    have n1 : ¬ M.mem (M.op a x) r := fun hle => haF (hFp.2.2.1 x y a h hle)
    have n2 : ¬ M.mem (M.op b y) s := fun hle => hbF (hFp.2.2.2 x y b h hle)
    exact ⟨⟨(M.wo_total hr (hFp.1 x y h).1 har).resolve_right n1, n1⟩,
      ⟨(M.wo_total hs (hFp.1 x y h).2 hbs).resolve_right n2, n2⟩⟩
  have hF' : ∀ x y, M.mem (M.op x y) (M.adj F (M.op a b)) ↔
      M.mem (M.op x y) F ∨ (x = a ∧ y = b) := by
    intro x y
    rw [M.mem_adj]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (M.op_inj h)
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr (by rw [h1, h2])
  have hnew : M.PIso r s (M.adj F (M.op a b)) := by
    refine ⟨fun x y h => ?_, fun x y x' y' h h' => ?_, fun x y x' h hle => ?_,
      fun x y y' h hle => ?_⟩
    · rcases (hF' x y).mp h with h | ⟨e1, e2⟩
      · exact hFp.1 x y h
      · rw [e1, e2]
        exact ⟨har, hbs⟩
    · rcases (hF' x y).mp h with h | ⟨e1, e2⟩
      · rcases (hF' x' y').mp h' with h' | ⟨e1', e2'⟩
        · exact hFp.2.1 x y x' y' h h'
        · rw [e1', e2']
          exact ⟨fun _ => (below x y h).2.1, fun _ => (below x y h).1.1⟩
      · rcases (hF' x' y').mp h' with h' | ⟨e1', e2'⟩
        · rw [e1, e2]
          exact ⟨fun hh => absurd hh (below x' y' h').1.2,
            fun hh => absurd hh (below x' y' h').2.2⟩
        · rw [e1, e2, e1', e2']
          exact ⟨fun _ => hbs, fun _ => har⟩
    · rcases (hF' x y).mp h with h | ⟨e1, e2⟩
      · obtain ⟨y', hy'⟩ := hFp.2.2.1 x y x' h hle
        exact ⟨y', (hF' x' y').mpr (Or.inl hy')⟩
      · rw [e1] at hle
        by_cases hx' : ∃ y', M.mem (M.op x' y') F
        · obtain ⟨y', hy'⟩ := hx'
          exact ⟨y', (hF' x' y').mpr (Or.inl hy')⟩
        · have h1 := hamin x' ((hA x').mpr hx') (hr.fld x' a hle).1
          exact ⟨b, (hF' x' b).mpr (Or.inr ⟨hr.antisymm x' a hle h1, rfl⟩)⟩
    · rcases (hF' x y).mp h with h | ⟨e1, e2⟩
      · obtain ⟨x', hx'⟩ := hFp.2.2.2 x y y' h hle
        exact ⟨x', (hF' x' y').mpr (Or.inl hx')⟩
      · rw [e2] at hle
        by_cases hy' : ∃ x', M.mem (M.op x' y') F
        · obtain ⟨x', hx'⟩ := hy'
          exact ⟨x', (hF' x' y').mpr (Or.inl hx')⟩
        · have h1 := hbmin y' ((hB y').mpr hy') (hs.fld y' b hle).1
          exact ⟨a, (hF' a y').mpr (Or.inr ⟨rfl, hs.antisymm y' b hle h1⟩)⟩
  exact haF ⟨b, (hF _).mpr ⟨_, hnew, M.mem_adj.mpr (Or.inr rfl)⟩⟩

/-! ### Embeddings as initial segments -/

/-- The conjunction form of `IsWO`. -/
def WORaw (r : V) : Prop :=
  (∀ a b, M.mem (M.op a b) r → M.mem (M.op a a) r ∧ M.mem (M.op b b) r) ∧
  (∀ a b c, M.mem (M.op a b) r → M.mem (M.op b c) r → M.mem (M.op a c) r) ∧
  (∀ a b, M.mem (M.op a b) r → M.mem (M.op b a) r → a = b) ∧
  (∀ X, (∃ a, M.mem a X ∧ M.mem (M.op a a) r) →
    ∃ a, M.mem a X ∧ M.mem (M.op a a) r ∧
      ∀ b, M.mem b X → M.mem (M.op b b) r → M.mem (M.op a b) r)

theorem woRaw_iff {r : V} : M.WORaw r ↔ M.IsWO r :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun h => ⟨h.fld, h.trans, h.antisymm, h.least⟩⟩

/-- `WORaw`, with `r` the name `1`. -/
def woFml : Fml :=
  .and (.all 8 (.all 9 (Fml.imp (fApp 1 8 9) (.and (fApp 1 8 8) (fApp 1 9 9)))))
  (.and (.all 8 (.all 9 (.all 10 (Fml.imp (fApp 1 8 9) (Fml.imp (fApp 1 9 10) (fApp 1 8 10))))))
  (.and (.all 8 (.all 9 (Fml.imp (fApp 1 8 9) (Fml.imp (fApp 1 9 8) (.eq 8 9)))))
  (.all 12 (Fml.imp (Fml.ex 8 (.and (.mem 8 12) (fApp 1 8 8)))
    (Fml.ex 8 (.and (.mem 8 12) (.and (fApp 1 8 8)
      (.all 9 (Fml.imp (.mem 9 12) (Fml.imp (fApp 1 9 9) (fApp 1 8 9)))))))))))

theorem sat_woFml (ρ : ℕ → V) : Sat M.mem M.isSet woFml ρ ↔ M.IsWO (ρ 1) := by
  rw [← M.woRaw_iff]
  simp [woFml, WORaw, Sat, M.sat_imp, M.sat_ex, M.sat_fApp, Function.update_apply]

theorem isWO_congr {r r' : V} (h : ∀ a b, M.mem (M.op a b) r ↔ M.mem (M.op a b) r') :
    M.IsWO r ↔ M.IsWO r' := by
  rw [← M.woRaw_iff, ← M.woRaw_iff]
  simp only [WORaw, h]

theorem piso_congr {r r' s s' f : V} (h1 : ∀ a b, M.mem (M.op a b) r ↔ M.mem (M.op a b) r')
    (h2 : ∀ a b, M.mem (M.op a b) s ↔ M.mem (M.op a b) s') :
    M.PIso r s f ↔ M.PIso r' s' f := by
  simp only [PIso, h1, h2]

/-- `r` is isomorphic to an initial segment of `s`. -/
def Emb (r s : V) : Prop :=
  ∃ f, M.PIso r s f ∧ ∀ x, M.mem (M.op x x) r → ∃ y, M.mem (M.op x y) f

theorem emb_congr {r r' s s' : V} (h1 : ∀ a b, M.mem (M.op a b) r ↔ M.mem (M.op a b) r')
    (h2 : ∀ a b, M.mem (M.op a b) s ↔ M.mem (M.op a b) s') : M.Emb r s ↔ M.Emb r' s' := by
  simp only [Emb, M.piso_congr h1 h2, h1]

theorem emb_refl {r : V} (hr : M.IsWO r) : M.Emb r r :=
  ⟨M.idf r, M.piso_idf hr, fun x hx => ⟨x, M.mem_idf.mpr ⟨rfl, hx⟩⟩⟩

theorem emb_trans {r s t : V} (h1 : M.Emb r s) (h2 : M.Emb s t) : M.Emb r t := by
  obtain ⟨f, hf, hfd⟩ := h1
  obtain ⟨g, hg, hgd⟩ := h2
  refine ⟨M.rcomp f g, M.piso_rcomp hf hg, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hfd x hx
  obtain ⟨z, hz⟩ := hgd y (hf.1 x y hy).2
  exact ⟨z, M.mem_rcomp.mpr ⟨y, hy, hz⟩⟩

theorem emb_total {r s : V} (hr : M.IsWO r) (hs : M.IsWO s) : M.Emb r s ∨ M.Emb s r := by
  obtain ⟨F, hF, h | h⟩ := M.wo_compare hr hs
  · exact Or.inl ⟨F, hF, h⟩
  · refine Or.inr ⟨M.conv F, M.piso_conv hF, fun y hy => ?_⟩
    obtain ⟨x, hx⟩ := h y hy
    exact ⟨x, M.mem_conv.mpr hx⟩

/-- `f` is an isomorphism of `s` onto the predecessors of `a` in `r`. -/
def SegOf (s r f a : V) : Prop :=
  M.PIso s r f ∧ (∀ x, M.mem (M.op x x) s → ∃ y, M.mem (M.op x y) f) ∧
  (¬ ∃ x, M.mem (M.op x a) f) ∧
  ∀ a', M.mem (M.op a' a) r → a' ≠ a → ∃ x, M.mem (M.op x a') f

/-- `SegOf`, with `s`, `r`, `f`, `a` the names `1`, `2`, `3`, `19`. -/
def segOfFml : Fml :=
  .and pisoFml (.and (.all 8 (Fml.imp (fApp 1 8 8) (Fml.ex 9 (fApp 3 8 9))))
    (.and (.neg (Fml.ex 8 (fApp 3 8 19)))
    (.all 10 (Fml.imp (fApp 2 10 19) (Fml.imp (.neg (.eq 10 19)) (Fml.ex 8 (fApp 3 8 10)))))))

theorem sat_segOfFml (ρ : ℕ → V) :
    Sat M.mem M.isSet segOfFml ρ ↔ M.SegOf (ρ 1) (ρ 2) (ρ 3) (ρ 19) := by
  simp [segOfFml, SegOf, Sat, M.sat_imp, M.sat_ex, M.sat_pisoFml, M.sat_fApp,
    Function.update_apply]

theorem segOf_congr {s s' r r' f a : V} (h1 : ∀ a b, M.mem (M.op a b) s ↔ M.mem (M.op a b) s')
    (h2 : ∀ a b, M.mem (M.op a b) r ↔ M.mem (M.op a b) r') :
    M.SegOf s r f a ↔ M.SegOf s' r' f a := by
  simp only [SegOf, M.piso_congr h1 h2, h1, h2]

theorem exists_nonran (f : V) : ∃ B, ∀ y, M.mem y B ↔ ¬ ∃ x, M.mem (M.op x y) f := by
  obtain ⟨B, -, hB0⟩ := M.comp (σW [(1, 5)]) (.neg (Fml.ex 9 (fApp 1 9 0))) 0 rfl
    (Function.update (fun _ => dflt) 1 f)
  refine ⟨B, fun y => ?_⟩
  rw [hB0 y]
  simp [Sat, M.sat_ex, M.sat_fApp, Function.update_apply]

/-- An embedding as an initial segment is onto or is onto the predecessors of a point. -/
theorem piso_onto_or_seg {s r f : V} (hr : M.IsWO r) (hf : M.PIso s r f)
    (hfull : ∀ x, M.mem (M.op x x) s → ∃ y, M.mem (M.op x y) f) :
    (∀ y, M.mem (M.op y y) r → ∃ x, M.mem (M.op x y) f) ∨
      ∃ a, M.mem (M.op a a) r ∧ M.SegOf s r f a := by
  by_cases h : ∀ y, M.mem (M.op y y) r → ∃ x, M.mem (M.op x y) f
  · exact Or.inl h
  · rw [not_forall] at h
    obtain ⟨y0, hy0⟩ := h
    rw [Classical.not_imp] at hy0
    obtain ⟨B, hB⟩ := M.exists_nonran f
    obtain ⟨a, haB, har, hmin⟩ := hr.least B ⟨y0, (hB y0).mpr hy0.2, hy0.1⟩
    refine Or.inr ⟨a, har, hf, hfull, (hB a).mp haB, fun a' hle hne => ?_⟩
    by_contra hn
    exact hne (hr.antisymm a' a hle (hmin a' ((hB a').mpr hn) (hr.fld a' a hle).1))

/-- A well-ordering is not isomorphic to the predecessors of one of its points. -/
theorem not_segOf_self {r f a : V} (hr : M.IsWO r) (ha : M.mem (M.op a a) r) :
    ¬ M.SegOf r r f a := by
  rintro ⟨hf, hfull, hna, -⟩
  obtain ⟨y, hy⟩ := hfull a ha
  have e : y = a := M.piso_agree hr hr hf (M.piso_idf hr) a y a hy (M.mem_idf.mpr ⟨rfl, ha⟩)
  rw [e] at hy
  exact hna ⟨a, hy⟩

/-- **Least elements for the comparison of lengths.** Let `Q` be a condition on
well-orderings that holds of `r`, and suppose the points `a` of `r` such that some
well-ordering with `Q` is isomorphic to the predecessors of `a` form a set. Then some
well-ordering with `Q` embeds as an initial segment in every other. -/
theorem wo_min {r : V} (hr : M.IsWO r) (Q : V → Prop) (hQ : ∀ s, Q s → M.IsWO s) (hQr : Q r)
    (A : V) (hA : ∀ a, M.mem a A ↔ M.mem (M.op a a) r ∧ ∃ s f, Q s ∧ M.SegOf s r f a) :
    ∃ s, Q s ∧ ∀ t, Q t → M.Emb s t := by
  by_cases hne : ∃ a, M.mem a A
  · obtain ⟨a0, ha0⟩ := hne
    obtain ⟨a1, ha1, ha1r, hmin⟩ := hr.least A ⟨a0, ha0, ((hA a0).mp ha0).1⟩
    obtain ⟨-, s1, f1, hQ1, hf1, hfull1, hna1, hbelow1⟩ := (hA a1).mp ha1
    refine ⟨s1, hQ1, fun t hQt => ?_⟩
    rcases M.emb_total (hQ s1 hQ1) (hQ t hQt) with h | ⟨g, hg, hgfull⟩
    · exact h
    · by_cases honto : ∀ y, M.mem (M.op y y) s1 → ∃ x, M.mem (M.op x y) g
      · refine ⟨M.conv g, M.piso_conv hg, fun y hy => ?_⟩
        obtain ⟨x, hx⟩ := honto y hy
        exact ⟨x, M.mem_conv.mpr hx⟩
      · exfalso
        rw [not_forall] at honto
        obtain ⟨y0, hy0⟩ := honto
        rw [Classical.not_imp] at hy0
        obtain ⟨b0, hb0⟩ := hfull1 y0 hy0.1
        have hcomp := M.piso_rcomp hg hf1
        have hcfull : ∀ x, M.mem (M.op x x) t → ∃ z, M.mem (M.op x z) (M.rcomp g f1) := by
          intro x hx
          obtain ⟨y, hy⟩ := hgfull x hx
          obtain ⟨z, hz⟩ := hfull1 y (hg.1 x y hy).2
          exact ⟨z, M.mem_rcomp.mpr ⟨y, hy, hz⟩⟩
        have hb0n : ¬ ∃ x, M.mem (M.op x b0) (M.rcomp g f1) := by
          rintro ⟨x, hx⟩
          obtain ⟨y, hxy, hyb⟩ := M.mem_rcomp.mp hx
          have e : y = y0 := M.piso_inj (hQ s1 hQ1) hf1 hyb hb0
          rw [e] at hxy
          exact hy0.2 ⟨x, hxy⟩
        have hb0r : M.mem (M.op b0 b0) r := (hf1.1 y0 b0 hb0).2
        rcases M.piso_onto_or_seg hr hcomp hcfull with h | ⟨a2, ha2r, hseg⟩
        · exact hb0n (h b0 hb0r)
        · have ha2A : M.mem a2 A := (hA a2).mpr ⟨ha2r, t, _, hQt, hseg⟩
          have h12 : M.mem (M.op a1 a2) r := hmin a2 ha2A ha2r
          have h2b : M.mem (M.op a2 b0) r := by
            by_contra hn
            have hb : M.mem (M.op b0 a2) r := (M.wo_total hr ha2r hb0r).resolve_left hn
            have hne' : b0 ≠ a2 := by
              intro e
              rw [e] at hn
              exact hn ha2r
            exact hb0n (hseg.2.2.2 b0 hb hne')
          obtain ⟨x, hx⟩ := hf1.2.2.2 y0 b0 a1 hb0 (hr.trans a1 a2 b0 h12 h2b)
          exact hna1 ⟨x, hx⟩
  · refine ⟨r, hQr, fun t hQt => ?_⟩
    rcases M.emb_total hr (hQ t hQt) with h | ⟨g, hg, hgfull⟩
    · exact h
    · rcases M.piso_onto_or_seg hr hg hgfull with h | ⟨a, har, hseg⟩
      · refine ⟨M.conv g, M.piso_conv hg, fun y hy => ?_⟩
        obtain ⟨x, hx⟩ := h y hy
        exact ⟨x, M.mem_conv.mpr hx⟩
      · exact absurd ⟨a, (hA a).mpr ⟨har, t, g, hQt, hseg⟩⟩ hne

/-! ### The predecessors of a point -/

theorem exists_seg (w a : V) : ∃ g, M.isSet g ∧ (∀ t, M.mem t g → ∃ x y, t = M.op x y) ∧
    ∀ x y, M.mem (M.op x y) g ↔ M.mem (M.op x y) w ∧ M.mem (M.op y a) w ∧ y ≠ a := by
  obtain ⟨g, hgs, hg0⟩ := M.comp (σW [(0, 4), (1, 5)])
    (Fml.ex 9 (Fml.ex 10 (.and (fPr 0 9 10) (.and (fApp 1 9 10) (.and (fApp 1 10 2)
      (.neg (.eq 10 2))))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 w) 2 a)
  have hg : ∀ t, M.mem t g ↔ ∃ x y, t = M.op x y ∧ M.mem (M.op x y) w ∧ M.mem (M.op y a) w ∧
      y ≠ a := by
    intro t
    rw [hg0 t]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp, Function.update_apply]
  refine ⟨g, hgs, fun t ht => ?_, fun x y => ⟨fun h => ?_, fun h => (hg _).mpr ⟨x, y, rfl, h⟩⟩⟩
  · obtain ⟨x, y, e, -⟩ := (hg t).mp ht
    exact ⟨x, y, e⟩
  · obtain ⟨x', y', e, h'⟩ := (hg _).mp h
    obtain ⟨e1, e2⟩ := M.op_inj e
    rw [e1, e2]
    exact h'

/-- The restriction of `w` to the predecessors of `a`. -/
noncomputable def seg (w a : V) : V := Classical.choose (M.exists_seg w a)

theorem mem_seg {w a x y : V} : M.mem (M.op x y) (M.seg w a) ↔
    M.mem (M.op x y) w ∧ M.mem (M.op y a) w ∧ y ≠ a :=
  (Classical.choose_spec (M.exists_seg w a)).2.2 x y

theorem seg_fld {w a x : V} (hw : M.IsWO w) : M.mem (M.op x x) (M.seg w a) ↔
    M.mem (M.op x a) w ∧ x ≠ a := by
  rw [M.mem_seg]
  exact ⟨fun h => h.2, fun h => ⟨(hw.fld x a h.1).1, h⟩⟩

theorem lt_of_le_lt {w a x y : V} (hw : M.IsWO w) (h1 : M.mem (M.op x y) w)
    (h2 : M.mem (M.op y a) w) (h3 : y ≠ a) : M.mem (M.op x a) w ∧ x ≠ a := by
  refine ⟨hw.trans x y a h1 h2, fun e => ?_⟩
  rw [e] at h1
  exact h3 (hw.antisymm y a h2 h1)

theorem isWO_seg {w a : V} (hw : M.IsWO w) : M.IsWO (M.seg w a) := by
  refine ⟨fun x y h => ?_, fun x y z h1 h2 => ?_, fun x y h1 h2 => ?_, fun X hX => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := M.mem_seg.mp h
    exact ⟨(M.seg_fld hw).mpr (M.lt_of_le_lt hw h1 h2 h3), (M.seg_fld hw).mpr ⟨h2, h3⟩⟩
  · obtain ⟨h1, -⟩ := M.mem_seg.mp h1
    obtain ⟨h2, h3⟩ := M.mem_seg.mp h2
    exact M.mem_seg.mpr ⟨hw.trans x y z h1 h2, h3⟩
  · exact hw.antisymm x y (M.mem_seg.mp h1).1 (M.mem_seg.mp h2).1
  · obtain ⟨Y, -, hY0⟩ := M.comp (σW [(1, 5), (3, 3)])
      (.and (.mem 0 3) (.and (fApp 1 0 2) (.neg (.eq 0 2)))) 0 rfl
      (Function.update (Function.update (Function.update (fun _ => dflt) 1 w) 2 a) 3 X)
    have hY : ∀ x, M.mem x Y ↔ M.mem x X ∧ M.mem (M.op x a) w ∧ x ≠ a := by
      intro x
      rw [hY0 x]
      simp [Sat, M.sat_fApp, Function.update_apply]
    obtain ⟨x0, hx0, hx0s⟩ := hX
    have hx0' := (M.seg_fld hw).mp hx0s
    obtain ⟨b, hbY, hbw, hmin⟩ := hw.least Y ⟨x0, (hY x0).mpr ⟨hx0, hx0'⟩, (hw.fld x0 a hx0'.1).1⟩
    obtain ⟨hbX, hba⟩ := (hY b).mp hbY
    refine ⟨b, hbX, (M.seg_fld hw).mpr hba, fun c hcX hcs => ?_⟩
    have hc' := (M.seg_fld hw).mp hcs
    exact M.mem_seg.mpr ⟨hmin c ((hY c).mpr ⟨hcX, hc'⟩) (hw.fld c a hc'.1).1, hc'⟩

/-- The identity is an isomorphism of the restriction onto the predecessors. -/
theorem segOf_seg {w a : V} (hw : M.IsWO w) :
    M.SegOf (M.seg w a) w (M.idf (M.seg w a)) a := by
  refine ⟨⟨fun x y h => ?_, fun x y x' y' h h' => ?_, fun x y x' h hle => ?_,
    fun x y y' h hle => ?_⟩, fun x hx => ⟨x, M.mem_idf.mpr ⟨rfl, hx⟩⟩, ?_, fun a' hle hne => ?_⟩
  · obtain ⟨e, hx⟩ := M.mem_idf.mp h
    rw [← e]
    exact ⟨hx, (hw.fld x a ((M.seg_fld hw).mp hx).1).1⟩
  · obtain ⟨e, hx⟩ := M.mem_idf.mp h
    obtain ⟨e', hx'⟩ := M.mem_idf.mp h'
    rw [← e, ← e', M.mem_seg]
    exact ⟨fun h => h.1, fun h => ⟨h, (M.seg_fld hw).mp hx'⟩⟩
  · exact ⟨x', M.mem_idf.mpr ⟨rfl, ((M.isWO_seg hw).fld x' x hle).1⟩⟩
  · obtain ⟨e, hx⟩ := M.mem_idf.mp h
    rw [← e] at hle
    obtain ⟨hxa, hxne⟩ := (M.seg_fld hw).mp hx
    exact ⟨y', M.mem_idf.mpr ⟨rfl, (M.seg_fld hw).mpr (M.lt_of_le_lt hw hle hxa hxne)⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨e, hxs⟩ := M.mem_idf.mp hx
    rw [e] at hxs
    exact ((M.seg_fld hw).mp hxs).2 rfl
  · exact ⟨a', M.mem_idf.mpr ⟨rfl, (M.seg_fld hw).mpr ⟨hle, hne⟩⟩⟩

/-! ## The Hartogs well-ordering of a rung (§3.3, step 2)

Fix a ladder with a pairing family and a rung `i` with two rungs above it. The members of
rung `i + 1` code the set relations on rung `i`. The well-orderings among them, compared by
length, and divided by isomorphism, form a well-ordering `H` whose points are members of rung
`i + 2`. It is longer than every well-ordering of a subset of rung `i`, and each of its proper
initial segments is isomorphic to one of those. -/

theorem exists_decSet (E P i : V) : ∃ D, ∀ c a b, M.mem (M.trip c a b) D ↔
    ∃ p, M.mem (M.quad i a b p) P ∧ M.mem (M.trip i p c) E := by
  obtain ⟨D, -, hD0⟩ := M.comp (σW [(0, 6), (2, 7), (3, 7)])
    (Fml.ex 15 (Fml.ex 16 (Fml.ex 17 (Fml.ex 19 (.and (fTrip 0 15 16 17)
      (.and (fApp4 3 5 16 17 19) (fApp3 2 5 19 15))))))) 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 2 E) 3 P) 5 i)
  have hD : ∀ t, M.mem t D ↔ ∃ c a b p, t = M.trip c a b ∧ M.mem (M.quad i a b p) P ∧
      M.mem (M.trip i p c) E := by
    intro t
    rw [hD0 t]
    simp [Sat, M.sat_ex, M.sat_fTrip, M.sat_fApp3, M.sat_fApp4, Function.update_apply]
  refine ⟨D, fun c a b => ⟨fun h => ?_, fun ⟨p, h1, h2⟩ => (hD _).mpr ⟨c, a, b, p, rfl, h1, h2⟩⟩⟩
  obtain ⟨c', a', b', p, e, h1, h2⟩ := (hD _).mp h
  obtain ⟨e1, e2, e3⟩ := M.trip_inj e
  rw [e1, e2, e3]
  exact ⟨p, h1, h2⟩

theorem exists_dec (D c : V) : ∃ r, M.isSet r ∧ (∀ t, M.mem t r → ∃ a b, t = M.op a b) ∧
    ∀ a b, M.mem (M.op a b) r ↔ M.mem (M.trip c a b) D := by
  obtain ⟨r, hrs, hr0⟩ := M.comp (σW [(0, 4), (1, 7)])
    (Fml.ex 9 (Fml.ex 10 (.and (fPr 0 9 10) (fApp3 1 2 9 10)))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 D) 2 c)
  have hr : ∀ t, M.mem t r ↔ ∃ a b, t = M.op a b ∧ M.mem (M.trip c a b) D := by
    intro t
    rw [hr0 t]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp3, Function.update_apply]
  refine ⟨r, hrs, fun t ht => ?_, fun a b => ⟨fun h => ?_, fun h => (hr _).mpr ⟨a, b, rfl, h⟩⟩⟩
  · obtain ⟨a, b, e, -⟩ := (hr t).mp ht
    exact ⟨a, b, e⟩
  · obtain ⟨a', b', e, h'⟩ := (hr _).mp h
    obtain ⟨e1, e2⟩ := M.op_inj e
    rw [e1, e2]
    exact h'

/-- `r` is the relation coded by `c`: a set of pairs, with `⟨a, b⟩ ∈ r` iff `⟨c, a, b⟩ ∈ D`. -/
def DecOf (D r c : V) : Prop :=
  M.isSet r ∧ (∀ t, M.mem t r → ∃ a b, t = M.op a b) ∧
  ∀ a b, M.mem (M.op a b) r ↔ M.mem (M.trip c a b) D

/-- The relation coded by `c`. -/
noncomputable def dec (D c : V) : V := Classical.choose (M.exists_dec D c)

theorem decOf_dec (D c : V) : M.DecOf D (M.dec D c) c := Classical.choose_spec (M.exists_dec D c)

theorem mem_dec {D c a b : V} : M.mem (M.op a b) (M.dec D c) ↔ M.mem (M.trip c a b) D :=
  (M.decOf_dec D c).2.2 a b

theorem decOf_eq {D r c : V} (h : M.DecOf D r c) : r = M.dec D c := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨g1, g2, g3⟩ := M.decOf_dec D c
  refine M.ext h1 g1 fun t => ⟨fun ht => ?_, fun ht => ?_⟩
  · obtain ⟨a, b, e⟩ := h2 t ht
    rw [e] at ht ⊢
    exact (g3 a b).mpr ((h3 a b).mp ht)
  · obtain ⟨a, b, e⟩ := g2 t ht
    rw [e] at ht ⊢
    exact (h3 a b).mpr ((g3 a b).mp ht)

theorem exists_decOf_iff {D c : V} {Φ : V → Prop} :
    (∃ r, M.DecOf D r c ∧ Φ r) ↔ Φ (M.dec D c) :=
  ⟨fun ⟨r, hr, h⟩ => M.decOf_eq hr ▸ h, fun h => ⟨_, M.decOf_dec D c, h⟩⟩

/-- `DecOf`, with `D` the name `24`. -/
def decFml (rr cc : ℕ) : Fml :=
  .and (.set rr) (.and (.all 13 (Fml.imp (.mem 13 rr) (Fml.ex 8 (Fml.ex 9 (fPr 13 8 9)))))
    (.all 8 (.all 9 (Fml.iff (fApp rr 8 9) (fApp3 24 cc 8 9)))))

theorem sat_decFml_1_0 (ρ : ℕ → V) :
    Sat M.mem M.isSet (decFml 1 0) ρ ↔ M.DecOf (ρ 24) (ρ 1) (ρ 0) := by
  simp [decFml, DecOf, Sat, M.sat_imp, M.sat_iff, M.sat_ex, M.sat_fPr, M.sat_fApp, M.sat_fApp3,
    Function.update_apply]

theorem sat_decFml_1_15 (ρ : ℕ → V) :
    Sat M.mem M.isSet (decFml 1 15) ρ ↔ M.DecOf (ρ 24) (ρ 1) (ρ 15) := by
  simp [decFml, DecOf, Sat, M.sat_imp, M.sat_iff, M.sat_ex, M.sat_fPr, M.sat_fApp, M.sat_fApp3,
    Function.update_apply]

theorem sat_decFml_2_16 (ρ : ℕ → V) :
    Sat M.mem M.isSet (decFml 2 16) ρ ↔ M.DecOf (ρ 24) (ρ 2) (ρ 16) := by
  simp [decFml, DecOf, Sat, M.sat_imp, M.sat_iff, M.sat_ex, M.sat_fPr, M.sat_fApp, M.sat_fApp3,
    Function.update_apply]

theorem exists_woCodes (R D j : V) :
    ∃ W, ∀ c, M.mem c W ↔ M.mem (M.op j c) R ∧ M.IsWO (M.dec D c) := by
  obtain ⟨W, -, hW0⟩ := M.comp (σW [(1, 5), (12, 3), (13, 4), (20, 5), (24, 7)])
    (.and (fApp 20 25 0) (Fml.ex 1 (.and (decFml 1 0) woFml))) 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 20 R) 24 D) 25 j)
  refine ⟨W, fun c => ?_⟩
  rw [hW0 c, ← M.exists_decOf_iff (Φ := M.IsWO)]
  simp [Sat, M.sat_ex, M.sat_fApp, M.sat_decFml_1_0, M.sat_woFml, Function.update_apply]

/-- `Emb`, with the two orderings the names `1`, `2`. -/
def embFml : Fml :=
  Fml.ex 3 (.and pisoFml (.all 8 (Fml.imp (fApp 1 8 8) (Fml.ex 9 (fApp 3 8 9)))))

theorem sat_embFml (ρ : ℕ → V) : Sat M.mem M.isSet embFml ρ ↔ M.Emb (ρ 1) (ρ 2) := by
  simp [embFml, Emb, Sat, M.sat_imp, M.sat_ex, M.sat_pisoFml, M.sat_fApp, Function.update_apply]

theorem exists_embSet (W D : V) : ∃ Q, ∀ c c', M.mem (M.op c c') Q ↔
    M.mem c W ∧ M.mem c' W ∧ M.Emb (M.dec D c) (M.dec D c') := by
  obtain ⟨Q, -, hQ0⟩ := M.comp (σW [(0, 4), (1, 5), (2, 5), (3, 5), (13, 4), (23, 3), (24, 7)])
    (Fml.ex 15 (Fml.ex 16 (.and (fPr 0 15 16) (.and (.mem 15 23) (.and (.mem 16 23)
      (Fml.ex 1 (Fml.ex 2 (.and (decFml 1 15) (.and (decFml 2 16) embFml))))))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 23 W) 24 D)
  have hQ : ∀ t, M.mem t Q ↔ ∃ c c', t = M.op c c' ∧ M.mem c W ∧ M.mem c' W ∧
      ∃ r s, M.DecOf D r c ∧ M.DecOf D s c' ∧ M.Emb r s := by
    intro t
    rw [hQ0 t]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_decFml_1_15, M.sat_decFml_2_16, M.sat_embFml,
      Function.update_apply]
  refine ⟨Q, fun c c' => ⟨fun h => ?_, fun ⟨h1, h2, h3⟩ =>
    (hQ _).mpr ⟨c, c', rfl, h1, h2, _, _, M.decOf_dec D c, M.decOf_dec D c', h3⟩⟩⟩
  obtain ⟨d, d', e, h1, h2, r, s, hr, hs, hemb⟩ := (hQ _).mp h
  obtain ⟨e1, e2⟩ := M.op_inj e
  rw [M.decOf_eq hr, M.decOf_eq hs] at hemb
  rw [e1, e2]
  exact ⟨h1, h2, hemb⟩

/-- `e`, a member of rung `k`, is the isomorphism class of the code `c`: its members on rung
`j` are the codes equivalent to `c` in the preorder `Q`. -/
def IsClass (R E Q j k e c : V) : Prop :=
  M.mem (M.op k e) R ∧ ∀ c', (M.mem (M.op j c') R ∧ M.mem (M.trip j c' e) E) ↔
    (M.mem (M.op c c') Q ∧ M.mem (M.op c' c) Q)

/-- `IsClass`, with `R`, `E`, `Q`, `j`, `k` the names `20`, `21`, `22`, `25`, `26`. -/
def classFml (e c : ℕ) : Fml :=
  .and (fApp 20 26 e) (.all 7 (Fml.iff (.and (fApp 20 25 7) (fApp3 21 25 7 e))
    (.and (fApp 22 c 7) (fApp 22 7 c))))

theorem sat_classFml_17_15 (ρ : ℕ → V) : Sat M.mem M.isSet (classFml 17 15) ρ ↔
    M.IsClass (ρ 20) (ρ 21) (ρ 22) (ρ 25) (ρ 26) (ρ 17) (ρ 15) := by
  simp [classFml, IsClass, Sat, M.sat_iff, M.sat_fApp, M.sat_fApp3, Function.update_apply]

theorem sat_classFml_18_16 (ρ : ℕ → V) : Sat M.mem M.isSet (classFml 18 16) ρ ↔
    M.IsClass (ρ 20) (ρ 21) (ρ 22) (ρ 25) (ρ 26) (ρ 18) (ρ 16) := by
  simp [classFml, IsClass, Sat, M.sat_iff, M.sat_fApp, M.sat_fApp3, Function.update_apply]

theorem exists_hOrd (R E Q j k : V) : ∃ H, ∀ e e', M.mem (M.op e e') H ↔
    ∃ c c', M.mem (M.op c c') Q ∧ M.IsClass R E Q j k e c ∧ M.IsClass R E Q j k e' c' := by
  obtain ⟨H, -, hH0⟩ := M.comp (σW [(0, 4), (20, 5), (21, 7), (22, 5)])
    (Fml.ex 17 (Fml.ex 18 (Fml.ex 15 (Fml.ex 16 (.and (fPr 0 17 18) (.and (fApp 22 15 16)
      (.and (classFml 17 15) (classFml 18 16)))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (fun _ => dflt) 20 R) 21 E) 22 Q) 25 j) 26 k)
  have hH : ∀ t, M.mem t H ↔ ∃ e e' c c', t = M.op e e' ∧ M.mem (M.op c c') Q ∧
      M.IsClass R E Q j k e c ∧ M.IsClass R E Q j k e' c' := by
    intro t
    rw [hH0 t]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp, M.sat_classFml_17_15, M.sat_classFml_18_16,
      Function.update_apply]
  refine ⟨H, fun e e' => ⟨fun h => ?_, fun ⟨c, c', h1, h2, h3⟩ =>
    (hH _).mpr ⟨e, e', c, c', rfl, h1, h2, h3⟩⟩⟩
  obtain ⟨e1, e1', c, c', eq, h1, h2, h3⟩ := (hH _).mp h
  obtain ⟨q1, q2⟩ := M.op_inj eq
  rw [q1, q2]
  exact ⟨c, c', h1, h2, h3⟩

/-- The data of the Hartogs well-ordering of rung `i`: the decoding set `D`, the set `W` of
codes of well-orderings, the preorder `Q` of these by length, and the ordering `H` of the
classes. -/
structure Hart (R E P D W Q H : V) (i : M.Num) : Prop where
  hD : ∀ c a b, M.mem (M.trip c a b) D ↔
    ∃ p, M.mem (M.quad i.1 a b p) P ∧ M.mem (M.trip i.1 p c) E
  hW : ∀ c, M.mem c W ↔ M.mem (M.op (i + 1).1 c) R ∧ M.IsWO (M.dec D c)
  hQ : ∀ c c', M.mem (M.op c c') Q ↔ M.mem c W ∧ M.mem c' W ∧ M.Emb (M.dec D c) (M.dec D c')
  hH : ∀ e e', M.mem (M.op e e') H ↔ ∃ c c', M.mem (M.op c c') Q ∧
    M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e c ∧ M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e' c'

theorem exists_hart (R E P : V) (i : M.Num) : ∃ D W Q H, M.Hart R E P D W Q H i := by
  obtain ⟨D, hD⟩ := M.exists_decSet E P i.1
  obtain ⟨W, hW⟩ := M.exists_woCodes R D (i + 1).1
  obtain ⟨Q, hQ⟩ := M.exists_embSet W D
  obtain ⟨H, hH⟩ := M.exists_hOrd R E Q (i + 1).1 (i + 1 + 1).1
  exact ⟨D, W, Q, H, hD, hW, hQ, hH⟩

section hart

variable {R E P D W Q H : V} {i : M.Num}

theorem q_refl (hd : M.Hart R E P D W Q H i) {c : V} (hc : M.mem c W) : M.mem (M.op c c) Q :=
  (hd.hQ c c).mpr ⟨hc, hc, M.emb_refl ((hd.hW c).mp hc).2⟩

theorem q_trans (hd : M.Hart R E P D W Q H i) {c c' c'' : V} (h1 : M.mem (M.op c c') Q)
    (h2 : M.mem (M.op c' c'') Q) : M.mem (M.op c c'') Q := by
  obtain ⟨a1, -, a3⟩ := (hd.hQ c c').mp h1
  obtain ⟨-, b2, b3⟩ := (hd.hQ c' c'').mp h2
  exact (hd.hQ c c'').mpr ⟨a1, b2, M.emb_trans a3 b3⟩

theorem class_mem (hd : M.Hart R E P D W Q H i) {c e : V} (hc : M.mem c W)
    (he : M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e c) :
    M.mem (M.op (i + 1).1 c) R ∧ M.mem (M.trip (i + 1).1 c e) E :=
  (he.2 c).mpr ⟨M.q_refl hd hc, M.q_refl hd hc⟩

theorem class_equiv (hd : M.Hart R E P D W Q H i) {c c' e : V} (hc : M.mem c W)
    (he : M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e c)
    (he' : M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e c') :
    M.mem (M.op c' c) Q ∧ M.mem (M.op c c') Q :=
  (he'.2 c).mp (M.class_mem hd hc he)

theorem class_of_equiv (hd : M.Hart R E P D W Q H i) {c c' e : V}
    (he : M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e c) (h1 : M.mem (M.op c c') Q)
    (h2 : M.mem (M.op c' c) Q) : M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e c' :=
  ⟨he.1, fun c'' => (he.2 c'').trans
    ⟨fun ⟨a, b⟩ => ⟨M.q_trans hd h2 a, M.q_trans hd b h1⟩,
      fun ⟨a, b⟩ => ⟨M.q_trans hd h1 a, M.q_trans hd b h2⟩⟩⟩

theorem class_unique {z S : V} {m : M.Num} (h : M.IsLadder R E z S m) (hi : i + 1 + 1 ≤ m)
    {c e e' : V} (he : M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e c)
    (he' : M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e' c) : e = e' :=
  M.rung_ext h hi he.1 he'.1 (fun t ht =>
    ⟨fun hE => ((he'.2 t).mpr ((he.2 t).mp ⟨ht, hE⟩)).2,
      fun hE => ((he.2 t).mpr ((he'.2 t).mp ⟨ht, hE⟩)).2⟩)

theorem class_exists {z S : V} {m : M.Num} (h : M.IsLadder R E z S m) (hi : i + 1 + 1 ≤ m)
    (hd : M.Hart R E P D W Q H i) {c : V} (hc : M.mem c W) :
    ∃ e, M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e c := by
  obtain ⟨Y, hYs, hY0⟩ := M.comp (σW [(1, 5)]) (.and (fApp 1 2 0) (fApp 1 0 2)) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 Q) 2 c)
  have hY : ∀ c', M.mem c' Y ↔ M.mem (M.op c c') Q ∧ M.mem (M.op c' c) Q := by
    intro c'
    rw [hY0 c']
    simp [Sat, M.sat_fApp, Function.update_apply]
  obtain ⟨e, he, hee, -⟩ := h.full (i + 1) hi Y hYs (fun c' hc' =>
    ((hd.hW c').mp ((hd.hQ c c').mp ((hY c').mp hc').1).2.1).1)
  exact ⟨e, he, fun c' => (hee c').symm.trans (hY c')⟩

theorem fld_H (hd : M.Hart R E P D W Q H i) {e : V} : M.mem (M.op e e) H ↔
    ∃ c, M.mem c W ∧ M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e c := by
  rw [hd.hH]
  constructor
  · rintro ⟨c, c', hq, he, -⟩
    exact ⟨c, ((hd.hQ c c').mp hq).1, he⟩
  · rintro ⟨c, hc, he⟩
    exact ⟨c, c, M.q_refl hd hc, he, he⟩

/-- The set of points of `r` whose predecessors are isomorphic to a well-ordering coded in a
class belonging to `X`; `r`, `X` are the names `2`, `27`, and the point is the name `19`. -/
def minFml : Fml :=
  .and (fApp 2 19 19) (Fml.ex 15 (Fml.ex 17 (.and (.mem 17 27) (.and (classFml 17 15)
    (.and (.mem 15 23) (Fml.ex 1 (.and (decFml 1 15) (Fml.ex 3 segOfFml))))))))

def σH : ℕ → ℕ :=
  σW [(1, 5), (2, 5), (3, 5), (13, 4), (20, 5), (21, 7), (22, 5), (23, 3), (24, 7), (27, 3)]

/-- **The classes of well-orderings of subsets of a rung are well-ordered by length.** -/
theorem isWO_H {z S : V} {m : M.Num} (h : M.IsLadder R E z S m) (hi : i + 1 + 1 ≤ m)
    (hd : M.Hart R E P D W Q H i) : M.IsWO H := by
  refine ⟨fun e e' hee => ?_, fun e e' e'' h1 h2 => ?_, fun e e' h1 h2 => ?_, fun X hX => ?_⟩
  · obtain ⟨c, c', hq, he, he'⟩ := (hd.hH e e').mp hee
    obtain ⟨hc, hc', -⟩ := (hd.hQ c c').mp hq
    exact ⟨(M.fld_H hd).mpr ⟨c, hc, he⟩, (M.fld_H hd).mpr ⟨c', hc', he'⟩⟩
  · obtain ⟨c, c', hq, he, he'⟩ := (hd.hH e e').mp h1
    obtain ⟨d', d'', hq', hd', hd''⟩ := (hd.hH e' e'').mp h2
    obtain ⟨-, hc', -⟩ := (hd.hQ c c').mp hq
    have h3 := (M.class_equiv hd hc' he' hd').2
    exact (hd.hH e e'').mpr ⟨c, d'', M.q_trans hd hq (M.q_trans hd h3 hq'), he, hd''⟩
  · obtain ⟨c, c', hq, he, he'⟩ := (hd.hH e e').mp h1
    obtain ⟨d', d, hq', hd', hd0⟩ := (hd.hH e' e).mp h2
    obtain ⟨hc, hc', -⟩ := (hd.hQ c c').mp hq
    have h3 := M.class_equiv hd hc' he' hd'
    have h4 := M.class_equiv hd hc he hd0
    have h5 : M.mem (M.op c' c) Q := M.q_trans hd h3.2 (M.q_trans hd hq' h4.1)
    exact M.class_unique h hi (M.class_of_equiv hd he hq h5) he'
  · obtain ⟨e0, he0X, he0H⟩ := hX
    obtain ⟨c0, hc0, hcl0⟩ := (M.fld_H hd).mp he0H
    have hr : M.IsWO (M.dec D c0) := ((hd.hW c0).mp hc0).2
    obtain ⟨A, -, hA0⟩ := M.comp σH minFml 19 rfl
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (fun _ => dflt)
        2 (M.dec D c0)) 20 R) 21 E) 22 Q) 23 W) 24 D) 25 (i + 1).1) 26 (i + 1 + 1).1) 27 X)
    have hA : ∀ a, M.mem a A ↔ M.mem (M.op a a) (M.dec D c0) ∧ ∃ c e, M.mem e X ∧
        M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e c ∧ M.mem c W ∧
        ∃ s, M.DecOf D s c ∧ ∃ f, M.SegOf s (M.dec D c0) f a := by
      intro a
      rw [hA0 a]
      simp [minFml, Sat, M.sat_ex, M.sat_fApp, M.sat_classFml_17_15, M.sat_decFml_1_15,
        M.sat_segOfFml, Function.update_apply]
    obtain ⟨s1, ⟨c1, e1, he1X, hcl1, hc1W, hs1⟩, hmin⟩ := M.wo_min hr
      (fun s => ∃ c e, M.mem e X ∧ M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e c ∧ M.mem c W ∧
        s = M.dec D c)
      (fun s ⟨c, e, _, _, hcW, hs⟩ => by rw [hs]; exact ((hd.hW c).mp hcW).2)
      ⟨c0, e0, he0X, hcl0, hc0, rfl⟩ A (fun a => (hA a).trans (and_congr Iff.rfl
        ⟨fun ⟨c, e, heX, hcl, hcW, s, hs, f, hseg⟩ =>
          ⟨M.dec D c, f, ⟨c, e, heX, hcl, hcW, rfl⟩, M.decOf_eq hs ▸ hseg⟩,
        fun ⟨s, f, ⟨c, e, heX, hcl, hcW, hs⟩, hseg⟩ =>
          ⟨c, e, heX, hcl, hcW, M.dec D c, M.decOf_dec D c, f, hs ▸ hseg⟩⟩))
    refine ⟨e1, he1X, (M.fld_H hd).mpr ⟨c1, hc1W, hcl1⟩, fun e heX heH => ?_⟩
    obtain ⟨c, hcW, hcl⟩ := (M.fld_H hd).mp heH
    have hemb := hmin (M.dec D c) ⟨c, e, heX, hcl, hcW, rfl⟩
    rw [hs1] at hemb
    exact (hd.hH e1 e).mpr ⟨c1, c, (hd.hQ c1 c).mpr ⟨hc1W, hcW, hemb⟩, hcl1, hcl⟩

end hart

/-! ### `H` is longer than every well-ordering of a subset of the rung -/

theorem segOf_ran_lt {s w f a x y : V} (hw : M.IsWO w) (ha : M.mem (M.op a a) w)
    (h1 : M.SegOf s w f a) (hxy : M.mem (M.op x y) f) : M.mem (M.op y a) w ∧ y ≠ a := by
  have hne : y ≠ a := by
    intro e
    rw [e] at hxy
    exact h1.2.2.1 ⟨x, hxy⟩
  refine ⟨?_, hne⟩
  by_contra hn
  have hay : M.mem (M.op a y) w := (M.wo_total hw (h1.1.1 x y hxy).2 ha).resolve_left hn
  exact h1.2.2.1 (h1.1.2.2.2 x y a hxy hay)

/-- Lengths of initial segments compare as their end points do. -/
theorem segOf_le_iff {s s' w f f' a a' : V} (hs : M.IsWO s) (hw : M.IsWO w)
    (ha : M.mem (M.op a a) w) (ha' : M.mem (M.op a' a') w) (h1 : M.SegOf s w f a)
    (h2 : M.SegOf s' w f' a') : M.mem (M.op a a') w ↔ M.Emb s s' := by
  constructor
  · intro hle
    refine ⟨M.rcomp f (M.conv f'), M.piso_rcomp h1.1 (M.piso_conv h2.1), fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := h1.2.1 x hx
    obtain ⟨hya, hyne⟩ := M.segOf_ran_lt hw ha h1 hy
    have hya' : M.mem (M.op y a') w := hw.trans y a a' hya hle
    have hne' : y ≠ a' := by
      intro e
      rw [e] at hya
      exact hyne (e.trans (hw.antisymm a' a hya hle))
    obtain ⟨x', hx'⟩ := h2.2.2.2 y hya' hne'
    exact ⟨x', M.mem_rcomp.mpr ⟨y, hy, M.mem_conv.mpr hx'⟩⟩
  · rintro ⟨g, hg, hgfull⟩
    by_contra hn
    have hlt : M.mem (M.op a' a) w := (M.wo_total hw ha ha').resolve_left hn
    have hne : a' ≠ a := by
      intro e
      rw [e] at hn
      exact hn ha
    obtain ⟨x0, hx0⟩ := h1.2.2.2 a' hlt hne
    obtain ⟨u, hu⟩ := hgfull x0 (h1.1.1 x0 a' hx0).1
    obtain ⟨y, hy⟩ := h2.2.1 u (hg.1 x0 u hu).2
    have e : a' = y := M.piso_agree hs hw h1.1 (M.piso_rcomp hg h2.1) x0 a' y hx0
      (M.mem_rcomp.mpr ⟨u, hu, hy⟩)
    rw [← e] at hy
    exact h2.2.2.1 ⟨u, hy⟩

/-- The graph of the map sending a point of `w` (name `2`) to the class of the
well-orderings isomorphic to its predecessors. -/
def segMapFml : Fml :=
  Fml.ex 19 (Fml.ex 17 (.and (fPr 0 19 17) (.and (fApp 2 19 19) (Fml.ex 15 (.and (.mem 15 23)
    (.and (classFml 17 15) (Fml.ex 1 (.and (decFml 1 15) (Fml.ex 3 segOfFml)))))))))

theorem exists_segMap (R E Q W D j k w : V) : ∃ Φ, ∀ a e, M.mem (M.op a e) Φ ↔
    M.mem (M.op a a) w ∧ ∃ c, M.mem c W ∧ M.IsClass R E Q j k e c ∧
      ∃ f, M.SegOf (M.dec D c) w f a := by
  obtain ⟨Φ, -, hΦ0⟩ := M.comp (σW [(0, 4), (1, 5), (2, 5), (3, 5), (13, 4), (20, 5), (21, 7),
    (22, 5), (23, 3), (24, 7)]) segMapFml 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 2 w) 20 R) 21 E)
      22 Q) 23 W) 24 D) 25 j) 26 k)
  have hΦ : ∀ t, M.mem t Φ ↔ ∃ a e, t = M.op a e ∧ M.mem (M.op a a) w ∧ ∃ c, M.mem c W ∧
      M.IsClass R E Q j k e c ∧ ∃ s, M.DecOf D s c ∧ ∃ f, M.SegOf s w f a := by
    intro t
    rw [hΦ0 t]
    simp [segMapFml, Sat, M.sat_ex, M.sat_fPr, M.sat_fApp, M.sat_classFml_17_15,
      M.sat_decFml_1_15, M.sat_segOfFml, Function.update_apply]
  refine ⟨Φ, fun a e => ⟨fun h => ?_, fun ⟨h1, c, h2, h3, f, h4⟩ =>
    (hΦ _).mpr ⟨a, e, rfl, h1, c, h2, h3, _, M.decOf_dec D c, f, h4⟩⟩⟩
  obtain ⟨a', e', eq, h1, c, h2, h3, s, hs, f, h4⟩ := (hΦ _).mp h
  obtain ⟨q1, q2⟩ := M.op_inj eq
  rw [M.decOf_eq hs] at h4
  rw [q1, q2]
  exact ⟨h1, c, h2, h3, f, h4⟩

section hart2

variable {R E P D W Q H z S : V} {i m : M.Num}

theorem dec_in_rung (hP : M.IsPairing R P m) (hd : M.Hart R E P D W Q H i) {c a b : V}
    (h : M.mem (M.op a b) (M.dec D c)) : M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R := by
  obtain ⟨p, hq, -⟩ := (hd.hD c a b).mp (M.mem_dec.mp h)
  exact ⟨(hP.dom _ _ _ _ hq).2.1, (hP.dom _ _ _ _ hq).2.2.1⟩

/-- Every well-ordering of a subset of rung `i` has a code. -/
theorem code_of_wo (h : M.IsLadder R E z S m) (hP : M.IsPairing R P m) (hi : i + 1 + 1 ≤ m)
    (hd : M.Hart R E P D W Q H i) {w : V} (hw : M.IsWO w)
    (hwT : ∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) :
    ∃ c, M.mem c W ∧ ∀ a b, M.mem (M.op a b) (M.dec D c) ↔ M.mem (M.op a b) w := by
  have hi1 : i + 1 ≤ m := le_trans (M.le_add_one (i + 1)) hi
  obtain ⟨c, hc, hcode⟩ := M.rel_code h hP hi1 hwT
  have same : ∀ a b, M.mem (M.op a b) (M.dec D c) ↔ M.mem (M.op a b) w := fun a b =>
    M.mem_dec.trans ((hd.hD c a b).trans (hcode a b).symm)
  exact ⟨c, (hd.hW c).mpr ⟨hc, (M.isWO_congr same).mpr hw⟩, same⟩

/-- The properties of the map from a well-ordering `w` of a subset of rung `i` into `H`: it
is an isomorphism onto an initial segment, and onto the predecessors of the class of `w`. -/
theorem segMap_spec (h : M.IsLadder R E z S m) (hP : M.IsPairing R P m) (hi : i + 1 + 1 ≤ m)
    (hd : M.Hart R E P D W Q H i) {w : V} (hw : M.IsWO w)
    (hwT : ∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) {Φ : V}
    (hΦ : ∀ a e, M.mem (M.op a e) Φ ↔ M.mem (M.op a a) w ∧ ∃ c, M.mem c W ∧
      M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e c ∧ ∃ f, M.SegOf (M.dec D c) w f a) :
    M.PIso w H Φ ∧ (∀ a, M.mem (M.op a a) w → ∃ e, M.mem (M.op a e) Φ) ∧
    ∀ cw e, M.mem cw W → (∀ a b, M.mem (M.op a b) (M.dec D cw) ↔ M.mem (M.op a b) w) →
      M.IsClass R E Q (i + 1).1 (i + 1 + 1).1 e cw → M.SegOf w H Φ e := by
  have hH := M.isWO_H h hi hd
  have hWO : ∀ {c : V}, M.mem c W → M.IsWO (M.dec D c) := fun hc => ((hd.hW _).mp hc).2
  -- the map is defined everywhere
  have total : ∀ a, M.mem (M.op a a) w → ∃ e, M.mem (M.op a e) Φ := by
    intro a ha
    obtain ⟨c, hc, same⟩ := M.code_of_wo h hP hi hd (M.isWO_seg (a := a) hw) (fun x y hxy =>
      hwT x y (M.mem_seg.mp hxy).1)
    obtain ⟨e, he⟩ := M.class_exists h hi hd hc
    exact ⟨e, (hΦ a e).mpr ⟨ha, c, hc, he, _,
      (M.segOf_congr same (fun _ _ => Iff.rfl)).mpr (M.segOf_seg hw)⟩⟩
  have piso : M.PIso w H Φ := by
    refine ⟨fun a e hae => ?_, fun a e a' e' hae hae' => ?_, fun a e a' hae hle => ?_,
      fun a e e' hae hle => ?_⟩
    · obtain ⟨ha, c, hc, hcl, -⟩ := (hΦ a e).mp hae
      exact ⟨ha, (M.fld_H hd).mpr ⟨c, hc, hcl⟩⟩
    · obtain ⟨ha, c, hc, hcl, f, hseg⟩ := (hΦ a e).mp hae
      obtain ⟨ha', c', hc', hcl', f', hseg'⟩ := (hΦ a' e').mp hae'
      rw [M.segOf_le_iff (hWO hc) hw ha ha' hseg hseg']
      constructor
      · intro hemb
        exact (hd.hH e e').mpr ⟨c, c', (hd.hQ c c').mpr ⟨hc, hc', hemb⟩, hcl, hcl'⟩
      · intro hee
        obtain ⟨d, d', hq, hdcl, hdcl'⟩ := (hd.hH e e').mp hee
        have h1 := M.class_equiv hd hc hcl hdcl
        have h2 := M.class_equiv hd hc' hcl' hdcl'
        exact ((hd.hQ c c').mp (M.q_trans hd h1.2 (M.q_trans hd hq h2.1))).2.2
    · exact total a' (hw.fld a' a hle).1
    · obtain ⟨ha, c, hc, hcl, f, hseg⟩ := (hΦ a e).mp hae
      obtain ⟨d', d, hq, hdcl', hdcl⟩ := (hd.hH e' e).mp hle
      have h1 := M.class_equiv hd hc hcl hdcl
      obtain ⟨hd'W, -, g, hg, hgfull⟩ := (hd.hQ d' c).mp (M.q_trans hd hq h1.1)
      have hcomp := M.piso_rcomp hg hseg.1
      have hcfull : ∀ x, M.mem (M.op x x) (M.dec D d') →
          ∃ y, M.mem (M.op x y) (M.rcomp g f) := by
        intro x hx
        obtain ⟨u, hu⟩ := hgfull x hx
        obtain ⟨y, hy⟩ := hseg.2.1 u (hg.1 x u hu).2
        exact ⟨y, M.mem_rcomp.mpr ⟨u, hu, hy⟩⟩
      rcases M.piso_onto_or_seg hw hcomp hcfull with honto | ⟨a2, ha2, hseg2⟩
      · obtain ⟨x, hx⟩ := honto a ha
        obtain ⟨u, -, hu⟩ := M.mem_rcomp.mp hx
        exact absurd ⟨u, hu⟩ hseg.2.2.1
      · exact ⟨a2, (hΦ a2 e').mpr ⟨ha2, d', hd'W, hdcl', _, hseg2⟩⟩
  refine ⟨piso, total, fun cw e hcw same hecl => ⟨piso, total, ?_, fun e' hle hne => ?_⟩⟩
  · rintro ⟨a, hae⟩
    obtain ⟨ha, c, hc, hcl, f, hseg⟩ := (hΦ a e).mp hae
    have h1 := M.class_equiv hd hcw hecl hcl
    obtain ⟨g, hg, hgfull⟩ := (M.emb_congr same (fun _ _ => Iff.rfl)).mp
      ((hd.hQ cw c).mp h1.2).2.2
    obtain ⟨u, hu⟩ := hgfull a ha
    obtain ⟨y, hy⟩ := hseg.2.1 u (hg.1 a u hu).2
    have e1 : y = a := M.piso_agree hw hw (M.piso_rcomp hg hseg.1) (M.piso_idf hw) a y a
      (M.mem_rcomp.mpr ⟨u, hu, hy⟩) (M.mem_idf.mpr ⟨rfl, ha⟩)
    rw [e1] at hy
    exact hseg.2.2.1 ⟨u, hy⟩
  · obtain ⟨d', d, hq, hdcl', hdcl⟩ := (hd.hH e' e).mp hle
    have h1 := M.class_equiv hd hcw hecl hdcl
    obtain ⟨hd'W, -, hemb⟩ := (hd.hQ d' cw).mp (M.q_trans hd hq h1.1)
    obtain ⟨g, hg, hgfull⟩ := (M.emb_congr (fun _ _ => Iff.rfl) same).mp hemb
    rcases M.piso_onto_or_seg hw hg hgfull with honto | ⟨a2, ha2, hseg2⟩
    · exfalso
      have hemb' : M.Emb (M.dec D cw) (M.dec D d') :=
        (M.emb_congr same (fun _ _ => Iff.rfl)).mpr ⟨M.conv g, M.piso_conv hg, fun y hy => by
          obtain ⟨x, hx⟩ := honto y hy
          exact ⟨x, M.mem_conv.mpr hx⟩⟩
      have hee' : M.mem (M.op e e') H :=
        (hd.hH e e').mpr ⟨cw, d', (hd.hQ cw d').mpr ⟨hcw, hd'W, hemb'⟩, hecl, hdcl'⟩
      exact hne (hH.antisymm e' e hle hee')
    · exact ⟨a2, (hΦ a2 e').mpr ⟨ha2, d', hd'W, hdcl', _, hseg2⟩⟩

/-- **The Hartogs well-ordering** (§3.3, step 2). In a ladder with a pairing family, for
every rung `i` with two rungs above it there is a set well-ordering `H` of members of rung
`i + 2` such that every set well-ordering of a subset of rung `i` is isomorphic to a proper
initial segment of `H` and `H` is not isomorphic to an initial segment of it, and such that
the predecessors of every point of `H` are isomorphic to a well-ordering of a subset of
rung `i`. -/
theorem hartogs (h : M.IsLadder R E z S m) (hP : M.IsPairing R P m) (hi : i + 1 + 1 ≤ m) :
    ∃ H, M.IsWO H ∧ (∀ e, M.mem (M.op e e) H → M.mem (M.op (i + 1 + 1).1 e) R) ∧
      (∀ w, M.IsWO w →
        (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) →
        M.Emb w H ∧ ¬ M.Emb H w) ∧
      ∀ e, M.mem (M.op e e) H → ∃ w f, M.IsWO w ∧
        (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) ∧
        M.SegOf w H f e := by
  obtain ⟨D, W, Q, H, hd⟩ := M.exists_hart R E P i
  have hH := M.isWO_H h hi hd
  refine ⟨H, hH, fun e he => ?_, fun w hw hwT => ?_, fun e he => ?_⟩
  · obtain ⟨c, -, hcl⟩ := (M.fld_H hd).mp he
    exact hcl.1
  · obtain ⟨Φ, hΦ⟩ := M.exists_segMap R E Q W D (i + 1).1 (i + 1 + 1).1 w
    obtain ⟨hpiso, htotal, hsegc⟩ := M.segMap_spec h hP hi hd hw hwT hΦ
    obtain ⟨cw, hcw, same⟩ := M.code_of_wo h hP hi hd hw hwT
    obtain ⟨e, hecl⟩ := M.class_exists h hi hd hcw
    have hseg := hsegc cw e hcw same hecl
    refine ⟨⟨Φ, hpiso, htotal⟩, ?_⟩
    rintro ⟨g, hg, hgfull⟩
    have heH : M.mem (M.op e e) H := (M.fld_H hd).mpr ⟨cw, hcw, hecl⟩
    obtain ⟨u, hu⟩ := hgfull e heH
    obtain ⟨y, hy⟩ := htotal u (hg.1 e u hu).2
    have e1 : y = e := M.piso_agree hH hH (M.piso_rcomp hg hpiso) (M.piso_idf hH) e y e
      (M.mem_rcomp.mpr ⟨u, hu, hy⟩) (M.mem_idf.mpr ⟨rfl, heH⟩)
    rw [e1] at hy
    exact hseg.2.2.1 ⟨u, hy⟩
  · obtain ⟨c, hc, hcl⟩ := (M.fld_H hd).mp he
    have hw : M.IsWO (M.dec D c) := ((hd.hW c).mp hc).2
    have hwT : ∀ a b, M.mem (M.op a b) (M.dec D c) →
        M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R := fun a b hab => M.dec_in_rung hP hd hab
    obtain ⟨Φ, hΦ⟩ := M.exists_segMap R E Q W D (i + 1).1 (i + 1 + 1).1 (M.dec D c)
    obtain ⟨-, -, hsegc⟩ := M.segMap_spec h hP hi hd hw hwT hΦ
    exact ⟨M.dec D c, Φ, hw, hwT, hsegc c e hc (fun _ _ => Iff.rfl) hcl⟩

end hart2

/-! ### A well-ordering transported along an injection -/

/-- If a set `g` maps the field of a well-ordering `H` injectively, then the image carries a
well-ordering in which `H` embeds as an initial segment. -/
theorem wo_transport {H g : V} (hH : M.IsWO H)
    (hfun : ∀ e a a', M.mem (M.op e a) g → M.mem (M.op e a') g → a = a')
    (hinj : ∀ e e' a, M.mem (M.op e a) g → M.mem (M.op e' a) g → e = e')
    (htot : ∀ e, M.mem (M.op e e) H → ∃ a, M.mem (M.op e a) g) :
    ∃ w, M.IsWO w ∧ (∀ a b, M.mem (M.op a b) w →
      (∃ e, M.mem (M.op e a) g) ∧ ∃ e, M.mem (M.op e b) g) ∧ M.Emb H w ∧
      ∀ a a', M.mem (M.op a a') w ↔ ∃ e e', M.mem (M.op e a) g ∧ M.mem (M.op e' a') g ∧
        M.mem (M.op e e') H := by
  obtain ⟨w, -, hw0⟩ := M.comp (σW [(0, 4), (1, 5), (2, 5)])
    (Fml.ex 9 (Fml.ex 10 (Fml.ex 11 (Fml.ex 12 (.and (fPr 0 9 10) (.and (fApp 1 11 9)
      (.and (fApp 1 12 10) (fApp 2 11 12)))))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 g) 2 H)
  have hw1 : ∀ t, M.mem t w ↔ ∃ a a' e e', t = M.op a a' ∧ M.mem (M.op e a) g ∧
      M.mem (M.op e' a') g ∧ M.mem (M.op e e') H := by
    intro t
    rw [hw0 t]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp, Function.update_apply]
  have hw : ∀ a a', M.mem (M.op a a') w ↔ ∃ e e', M.mem (M.op e a) g ∧ M.mem (M.op e' a') g ∧
      M.mem (M.op e e') H := by
    intro a a'
    constructor
    · intro h
      obtain ⟨b, b', e, e', eq, h1, h2, h3⟩ := (hw1 _).mp h
      obtain ⟨q1, q2⟩ := M.op_inj eq
      rw [q1, q2]
      exact ⟨e, e', h1, h2, h3⟩
    · rintro ⟨e, e', h1, h2, h3⟩
      exact (hw1 _).mpr ⟨a, a', e, e', rfl, h1, h2, h3⟩
  obtain ⟨g', -, hg0⟩ := M.comp (σW [(0, 4), (1, 5), (2, 5)])
    (Fml.ex 9 (Fml.ex 10 (.and (fPr 0 9 10) (.and (fApp 1 9 10) (fApp 2 9 9))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 g) 2 H)
  have hg1 : ∀ t, M.mem t g' ↔ ∃ e a, t = M.op e a ∧ M.mem (M.op e a) g ∧
      M.mem (M.op e e) H := by
    intro t
    rw [hg0 t]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp, Function.update_apply]
  have hg' : ∀ e a, M.mem (M.op e a) g' ↔ M.mem (M.op e a) g ∧ M.mem (M.op e e) H := by
    intro e a
    constructor
    · intro h
      obtain ⟨e', a', eq, h1, h2⟩ := (hg1 _).mp h
      obtain ⟨q1, q2⟩ := M.op_inj eq
      rw [q1, q2]
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact (hg1 _).mpr ⟨e, a, rfl, h1, h2⟩
  have hwo : M.IsWO w := by
    refine ⟨fun a a' h => ?_, fun a a' a'' p1 p2 => ?_, fun a a' p1 p2 => ?_, fun X hX => ?_⟩
    · obtain ⟨e, e', h1, h2, h3⟩ := (hw a a').mp h
      exact ⟨(hw a a).mpr ⟨e, e, h1, h1, (hH.fld e e' h3).1⟩,
        (hw a' a').mpr ⟨e', e', h2, h2, (hH.fld e e' h3).2⟩⟩
    · obtain ⟨e, e', h1, h2, h3⟩ := (hw a a').mp p1
      obtain ⟨d', d'', k1, k2, k3⟩ := (hw a' a'').mp p2
      rw [← hinj e' d' a' h2 k1] at k3
      exact (hw a a'').mpr ⟨e, d'', h1, k2, hH.trans e e' d'' h3 k3⟩
    · obtain ⟨e, e', h1, h2, h3⟩ := (hw a a').mp p1
      obtain ⟨d', d, k1, k2, k3⟩ := (hw a' a).mp p2
      rw [← hinj e' d' a' h2 k1, ← hinj e d a h1 k2] at k3
      have e1 : e = e' := hH.antisymm e e' h3 k3
      rw [← e1] at h2
      exact hfun e a a' h1 h2
    · obtain ⟨a0, ha0X, ha0w⟩ := hX
      obtain ⟨e0, e0', he0, -, he0H⟩ := (hw a0 a0).mp ha0w
      obtain ⟨Y, -, hY0⟩ := M.comp (σW [(1, 5), (3, 3)])
        (Fml.ex 9 (.and (.mem 9 3) (fApp 1 0 9))) 0 rfl
        (Function.update (Function.update (fun _ => dflt) 1 g) 3 X)
      have hY : ∀ e, M.mem e Y ↔ ∃ a, M.mem a X ∧ M.mem (M.op e a) g := by
        intro e
        rw [hY0 e]
        simp [Sat, M.sat_ex, M.sat_fApp, Function.update_apply]
      obtain ⟨e1, he1Y, he1H, hmin⟩ := hH.least Y
        ⟨e0, (hY e0).mpr ⟨a0, ha0X, he0⟩, (hH.fld _ _ he0H).1⟩
      obtain ⟨a1, ha1X, he1a1⟩ := (hY e1).mp he1Y
      refine ⟨a1, ha1X, (hw a1 a1).mpr ⟨e1, e1, he1a1, he1a1, he1H⟩, fun b hbX hbw => ?_⟩
      obtain ⟨e, e', heb, -, heH⟩ := (hw b b).mp hbw
      exact (hw a1 b).mpr ⟨e1, e, he1a1, heb,
        hmin e ((hY e).mpr ⟨b, hbX, heb⟩) (hH.fld _ _ heH).1⟩
  refine ⟨w, hwo, fun a b hab => ?_, ⟨g', ⟨fun e a h => ?_, fun e a e' a' h h' => ?_,
    fun e a e'' h hle => ?_, fun e a a'' h hle => ?_⟩, fun e he => ?_⟩, hw⟩
  · obtain ⟨e, e', h1, h2, -⟩ := (hw a b).mp hab
    exact ⟨⟨e, h1⟩, ⟨e', h2⟩⟩
  · obtain ⟨h1, h2⟩ := (hg' e a).mp h
    exact ⟨h2, (hw a a).mpr ⟨e, e, h1, h1, h2⟩⟩
  · obtain ⟨h1, h2⟩ := (hg' e a).mp h
    obtain ⟨k1, k2⟩ := (hg' e' a').mp h'
    constructor
    · intro hee
      exact (hw a a').mpr ⟨e, e', h1, k1, hee⟩
    · intro haa
      obtain ⟨d, d', j1, j2, j3⟩ := (hw a a').mp haa
      rw [hinj e d a h1 j1, hinj e' d' a' k1 j2]
      exact j3
  · have he'' := (hH.fld e'' e hle).1
    obtain ⟨a'', ha''⟩ := htot e'' he''
    exact ⟨a'', (hg' e'' a'').mpr ⟨ha'', he''⟩⟩
  · obtain ⟨d'', d, j1, j2, j3⟩ := (hw a'' a).mp hle
    exact ⟨d'', (hg' d'' a'').mpr ⟨j1, (hH.fld d'' d j3).1⟩⟩
  · obtain ⟨a, ha⟩ := htot e he
    exact ⟨a, (hg' e a).mpr ⟨ha, he⟩⟩

/-- **The Hartogs well-ordering of a rung does not inject into the rung**: no set maps its
field injectively into rung `i`. -/
theorem hartogs_no_inj {R H : V} {i : M.Num} (hH : M.IsWO H)
    (hlong : ∀ w, M.IsWO w →
      (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) →
      M.Emb w H ∧ ¬ M.Emb H w) {g : V}
    (hfun : ∀ e a a', M.mem (M.op e a) g → M.mem (M.op e a') g → a = a')
    (hinj : ∀ e e' a, M.mem (M.op e a) g → M.mem (M.op e' a) g → e = e')
    (htot : ∀ e, M.mem (M.op e e) H → ∃ a, M.mem (M.op e a) g)
    (hran : ∀ e a, M.mem (M.op e a) g → M.mem (M.op i.1 a) R) : False := by
  obtain ⟨w, hw, hwran, hemb, -⟩ := M.wo_transport hH hfun hinj htot
  refine (hlong w hw (fun a b hab => ?_)).2 hemb
  obtain ⟨⟨e, he⟩, ⟨e', he'⟩⟩ := hwran a b hab
  exact ⟨hran e a he, hran e' b he'⟩

/-! ## Recursion along a set well-ordering (§3.3, step 3, first part)

A family of sets `F_α`, `α` a point of a set well-ordering `r`, is given by the set `F` of pairs
`⟨α, y⟩` with `y ∈ F_α`. The theorem `wo_rec` builds `F` from a stratified condition that says
when `y ∈ F_α` in terms of the part of `F` below `α`. -/

/-- `G'` is the part of `G` below `α`: the set of pairs `⟨β, z⟩ ∈ G` with `β` strictly below
`α` in `r`. -/
def IsRestr (r G' G α : V) : Prop :=
  M.isSet G' ∧ (∀ t, M.mem t G' → ∃ β z, t = M.op β z) ∧
  ∀ β z, M.mem (M.op β z) G' ↔ M.mem (M.op β z) G ∧ M.mem (M.op β α) r ∧ β ≠ α

/-- `IsRestr`, with `r`, `G'`, `G`, `α` the names `2`, `6`, `3`, `4`. -/
def restrFml : Fml :=
  .and (.set 6) (.and (.all 7 (Fml.imp (.mem 7 6) (Fml.ex 8 (Fml.ex 9 (fPr 7 8 9)))))
    (.all 8 (.all 9 (Fml.iff (fApp 6 8 9)
      (.and (fApp 3 8 9) (.and (fApp 2 8 4) (.neg (.eq 8 4))))))))

theorem sat_restrFml (ρ : ℕ → V) :
    Sat M.mem M.isSet restrFml ρ ↔ M.IsRestr (ρ 2) (ρ 6) (ρ 3) (ρ 4) := by
  simp [restrFml, IsRestr, Sat, M.sat_imp, M.sat_iff, M.sat_ex, M.sat_fPr, M.sat_fApp,
    Function.update_apply]

theorem exists_restr (r G α : V) : ∃ G', M.IsRestr r G' G α := by
  obtain ⟨G', hs, h0⟩ := M.comp (σW [(0, 4), (1, 5), (2, 5)])
    (Fml.ex 8 (Fml.ex 9 (.and (fPr 0 8 9) (.and (fApp 1 8 9) (.and (fApp 2 8 4)
      (.neg (.eq 8 4))))))) 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 1 G) 2 r) 4 α)
  have h : ∀ t, M.mem t G' ↔ ∃ β z, t = M.op β z ∧ M.mem (M.op β z) G ∧ M.mem (M.op β α) r ∧
      β ≠ α := by
    intro t
    rw [h0 t]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp, Function.update_apply]
  refine ⟨G', hs, fun t ht => ?_, fun β z => ⟨fun hm => ?_, fun hm => (h _).mpr ⟨β, z, rfl, hm⟩⟩⟩
  · obtain ⟨β, z, e, -⟩ := (h t).mp ht
    exact ⟨β, z, e⟩
  · obtain ⟨β', z', e, hm'⟩ := (h _).mp hm
    obtain ⟨e1, e2⟩ := M.op_inj e
    rw [e1, e2]
    exact hm'

/-- The part of `G` below `α`. -/
noncomputable def restr (r G α : V) : V := Classical.choose (M.exists_restr r G α)

theorem isRestr_restr (r G α : V) : M.IsRestr r (M.restr r G α) G α :=
  Classical.choose_spec (M.exists_restr r G α)

theorem mem_restr {r G α β z : V} : M.mem (M.op β z) (M.restr r G α) ↔
    M.mem (M.op β z) G ∧ M.mem (M.op β α) r ∧ β ≠ α := (M.isRestr_restr r G α).2.2 β z

theorem restr_eq {r G' G α : V} (h : M.IsRestr r G' G α) : G' = M.restr r G α := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨g1, g2, g3⟩ := M.isRestr_restr r G α
  refine M.ext h1 g1 fun t => ⟨fun ht => ?_, fun ht => ?_⟩
  · obtain ⟨a, b, e⟩ := h2 t ht
    rw [e] at ht ⊢
    exact (g3 a b).mpr ((h3 a b).mp ht)
  · obtain ⟨a, b, e⟩ := g2 t ht
    rw [e] at ht ⊢
    exact (h3 a b).mpr ((g3 a b).mp ht)

theorem exists_restr_iff {r G α : V} {Φ : V → Prop} :
    (∃ G', M.IsRestr r G' G α ∧ Φ G') ↔ Φ (M.restr r G α) :=
  ⟨fun ⟨G', hG', h⟩ => M.restr_eq hG' ▸ h, fun h => ⟨_, M.isRestr_restr r G α, h⟩⟩

theorem restr_congr {r G G' α : V} (h : ∀ β z, M.mem (M.op β α) r → β ≠ α →
    (M.mem (M.op β z) G ↔ M.mem (M.op β z) G')) : M.restr r G α = M.restr r G' α := by
  obtain ⟨h1, h2, h3⟩ := M.isRestr_restr r G α
  exact M.restr_eq ⟨h1, h2, fun β z => (h3 β z).trans
    ⟨fun ⟨a, b, c⟩ => ⟨(h β z b c).mp a, b, c⟩, fun ⟨a, b, c⟩ => ⟨(h β z b c).mpr a, b, c⟩⟩⟩

/-- `G` is the family up to and including `γ`. -/
def Approx (r : V) (Φ : V → V → V → Prop) (G γ : V) : Prop :=
  ∀ α y, M.mem (M.op α y) G ↔ M.mem (M.op α γ) r ∧ Φ α y (M.restr r G α)

/-- `Approx`, with `r`, `G`, `γ` the names `2`, `3`, `0`; the step `φ` speaks of `α`, `y` and
the part below `α` through the names `4`, `5`, `6`. -/
def approxFml (φ : Fml) : Fml :=
  .all 4 (.all 5 (Fml.iff (fApp 3 4 5) (.and (fApp 2 4 0) (Fml.ex 6 (.and restrFml φ)))))

/-- The stratification for recursion along a well-ordering: the names below `10` and the
bound names of the pair formulas are fixed, the other names are given by `l`. -/
def σR (l : List (ℕ × ℕ)) : ℕ → ℕ :=
  σW ([(0, 2), (1, 5), (2, 5), (3, 5), (4, 2), (5, 2), (6, 5), (7, 4), (8, 2), (9, 2), (36, 3),
    (37, 2), (38, 4)] ++ l)

theorem strat_approxFml {φ : Fml} {l : List (ℕ × ℕ)} (hφ : φ.strat (σR l) = true) :
    (approxFml φ).strat (σR l) = true := by
  simp [approxFml, restrFml, fApp, fPr, fOp, fSing, fUp, Fml.ex, Fml.iff, Fml.imp, Fml.or,
    Fml.strat, hφ, show σR l 0 = 2 from rfl, show σR l 2 = 5 from rfl, show σR l 3 = 5 from rfl,
    show σR l 4 = 2 from rfl, show σR l 5 = 2 from rfl, show σR l 6 = 5 from rfl,
    show σR l 7 = 4 from rfl, show σR l 8 = 2 from rfl, show σR l 9 = 2 from rfl,
    show σR l 36 = 3 from rfl, show σR l 37 = 2 from rfl, show σR l 38 = 4 from rfl]

theorem xor_of_not_iff {A B : Prop} (h : ¬ (A ↔ B)) : (A ∧ ¬ B) ∨ (B ∧ ¬ A) := by
  tauto

theorem upd_ge {ρ ρ' : ℕ → V} (k : ℕ) (hk : k < 10) (a : V) (h : ∀ n, 10 ≤ n → ρ' n = ρ n) :
    ∀ n, 10 ≤ n → Function.update ρ' k a n = ρ n := fun n hn => by
  rw [Function.update_of_ne (by omega)]
  exact h n hn

theorem sat_at {Φ : V → V → V → Prop} {φ : Fml} {ρ : ℕ → V}
    (hsat : ∀ ρ' : ℕ → V, (∀ n, 10 ≤ n → ρ' n = ρ n) →
      (Sat M.mem M.isSet φ ρ' ↔ Φ (ρ' 4) (ρ' 5) (ρ' 6)))
    {ρ' : ℕ → V} (hρ' : ∀ n, 10 ≤ n → ρ' n = ρ n) (α y G' : V) :
    Sat M.mem M.isSet φ (Function.update (Function.update (Function.update ρ' 4 α) 5 y) 6 G') ↔
      Φ α y G' := by
  rw [hsat (Function.update (Function.update (Function.update ρ' 4 α) 5 y) 6 G')
    (upd_ge 6 (by decide) _ (upd_ge 5 (by decide) _ (upd_ge 4 (by decide) _ hρ')))]
  simp [Function.update_apply]

theorem sat_approxFml {Φ : V → V → V → Prop} {φ : Fml} {ρ : ℕ → V}
    (hsat : ∀ ρ' : ℕ → V, (∀ n, 10 ≤ n → ρ' n = ρ n) →
      (Sat M.mem M.isSet φ ρ' ↔ Φ (ρ' 4) (ρ' 5) (ρ' 6)))
    {ρ' : ℕ → V} (hρ' : ∀ n, 10 ≤ n → ρ' n = ρ n) :
    Sat M.mem M.isSet (approxFml φ) ρ' ↔ M.Approx (ρ' 2) Φ (ρ' 3) (ρ' 0) := by
  have key := M.sat_at hsat hρ'
  have h1 : Sat M.mem M.isSet (approxFml φ) ρ' ↔ ∀ α y, M.mem (M.op α y) (ρ' 3) ↔
      M.mem (M.op α (ρ' 0)) (ρ' 2) ∧ ∃ G', M.IsRestr (ρ' 2) G' (ρ' 3) α ∧ Φ α y G' := by
    simp [approxFml, Sat, M.sat_iff, M.sat_ex, M.sat_fApp, M.sat_restrFml, key,
      Function.update_apply]
  rw [h1]
  exact forall_congr' fun α => forall_congr' fun y =>
    iff_congr Iff.rfl (and_congr Iff.rfl M.exists_restr_iff)

/-- **Recursion along a set well-ordering.** Let `r` be a set well-ordering and `Φ α y G` a
condition given by a stratified formula `φ` (with `α`, `y`, `G` the names `4`, `5`, `6`, the
parameters at names from `10` on). Then there is a set `F` of pairs with
`⟨α, y⟩ ∈ F` iff `α` is a point of `r` and `Φ α y (the part of F below α)`. -/
theorem wo_rec {r : V} (hr : M.IsWO r) (Φ : V → V → V → Prop) (φ : Fml) (l : List (ℕ × ℕ))
    (hφ : φ.strat (σR l) = true) (ρ : ℕ → V)
    (hsat : ∀ ρ' : ℕ → V, (∀ n, 10 ≤ n → ρ' n = ρ n) →
      (Sat M.mem M.isSet φ ρ' ↔ Φ (ρ' 4) (ρ' 5) (ρ' 6))) :
    ∃ F, ∀ α y, M.mem (M.op α y) F ↔ M.mem (M.op α α) r ∧ Φ α y (M.restr r F α) := by
  have v0 : σR l 0 = 2 := rfl
  have v2 : σR l 2 = 5 := rfl
  have v3 : σR l 3 = 5 := rfl
  have v4 : σR l 4 = 2 := rfl
  have v5 : σR l 5 = 2 := rfl
  have v6 : σR l 6 = 5 := rfl
  have v7 : σR l 7 = 4 := rfl
  have v8 : σR l 8 = 2 := rfl
  have v9 : σR l 9 = 2 := rfl
  have v36 : σR l 36 = 3 := rfl
  have v37 : σR l 37 = 2 := rfl
  have v38 : σR l 38 = 4 := rfl
  have hsa := strat_approxFml hφ
  have hrge : ∀ n, 10 ≤ n → Function.update ρ 2 r n = ρ n :=
    upd_ge 2 (by decide) r (fun n _ => rfl)
  -- two approximations agree
  have agree : ∀ {G G' γ γ' : V}, M.Approx r Φ G γ → M.Approx r Φ G' γ' → ∀ α y,
      M.mem (M.op α γ) r → M.mem (M.op α γ') r →
      (M.mem (M.op α y) G ↔ M.mem (M.op α y) G') := by
    intro G G' γ γ' hG hG'
    obtain ⟨Dg, -, hD0⟩ := M.comp (σR []) (.and (fApp 2 4 0) (.and (fApp 2 4 8)
      (Fml.ex 5 (Fml.or (.and (fApp 3 4 5) (.neg (fApp 1 4 5)))
        (.and (fApp 1 4 5) (.neg (fApp 3 4 5))))))) 4 rfl
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (fun _ => dflt) 1 G') 2 r) 3 G) 0 γ) 8 γ')
    have hD : ∀ α, M.mem α Dg ↔ M.mem (M.op α γ) r ∧ M.mem (M.op α γ') r ∧
        ∃ y, (M.mem (M.op α y) G ∧ ¬ M.mem (M.op α y) G') ∨
          (M.mem (M.op α y) G' ∧ ¬ M.mem (M.op α y) G) := by
      intro α
      rw [hD0 α]
      simp [Sat, M.sat_ex, M.sat_or, M.sat_fApp, Function.update_apply]
    intro α y h1 h2
    by_contra hne
    have hne' : (M.mem (M.op α y) G ∧ ¬ M.mem (M.op α y) G') ∨
        (M.mem (M.op α y) G' ∧ ¬ M.mem (M.op α y) G) := xor_of_not_iff hne
    obtain ⟨α0, hα0, hα0r, hmin⟩ := hr.least Dg
      ⟨α, (hD α).mpr ⟨h1, h2, y, hne'⟩, (hr.fld α γ h1).1⟩
    obtain ⟨k1, k2, y0, hy0⟩ := (hD α0).mp hα0
    have hbelow : ∀ β z, M.mem (M.op β α0) r → β ≠ α0 →
        (M.mem (M.op β z) G ↔ M.mem (M.op β z) G') := by
      intro β z hβ hβne
      by_contra hc
      have hc' : (M.mem (M.op β z) G ∧ ¬ M.mem (M.op β z) G') ∨
          (M.mem (M.op β z) G' ∧ ¬ M.mem (M.op β z) G) := xor_of_not_iff hc
      have h3 := hmin β ((hD β).mpr ⟨hr.trans β α0 γ hβ k1, hr.trans β α0 γ' hβ k2, z, hc'⟩)
        (hr.fld β α0 hβ).1
      exact hβne (hr.antisymm β α0 hβ h3)
    have hiff : M.mem (M.op α0 y0) G ↔ M.mem (M.op α0 y0) G' := by
      rw [hG α0 y0, hG' α0 y0, M.restr_congr hbelow]
      exact ⟨fun ⟨_, b⟩ => ⟨k2, b⟩, fun ⟨_, b⟩ => ⟨k1, b⟩⟩
    rcases hy0 with ⟨a, b⟩ | ⟨a, b⟩
    · exact b (hiff.mp a)
    · exact b (hiff.mpr a)
  -- the points without an approximation
  obtain ⟨B, -, hB0⟩ := M.comp (σR l) (.and (fApp 2 0 0) (.neg (Fml.ex 3 (approxFml φ)))) 0
    (by simp [Fml.strat, Fml.ex, Fml.iff, Fml.imp, Fml.or, fApp, fPr, fOp, fSing, fUp, hsa, v0, v2,
      v3, v4, v5, v6, v7, v8, v9, v36, v37, v38])
    (Function.update ρ 2 r)
  have hB : ∀ γ, M.mem γ B ↔ M.mem (M.op γ γ) r ∧ ¬ ∃ G, M.Approx r Φ G γ := by
    intro γ
    rw [hB0 γ]
    have e : ∀ G, Sat M.mem M.isSet (approxFml φ) (Function.update (Function.update
        (Function.update ρ 2 r) 0 γ) 3 G) ↔ M.Approx r Φ G γ := fun G => by
      rw [M.sat_approxFml hsat (upd_ge 3 (by decide) _ (upd_ge 0 (by decide) _ hrge))]
      simp [Function.update_apply]
    simp [Sat, M.sat_ex, M.sat_fApp, e, Function.update_apply]
  have exists_approx : ∀ γ, M.mem (M.op γ γ) r → ∃ G, M.Approx r Φ G γ := by
    intro γ hγ
    by_contra hno
    obtain ⟨γ0, hγ0B, hγ0r, hmin⟩ := hr.least B ⟨γ, (hB γ).mpr ⟨hγ, hno⟩, hγ⟩
    have hno0 := ((hB γ0).mp hγ0B).2
    have hbelow : ∀ β, M.mem (M.op β γ0) r → β ≠ γ0 → ∃ G, M.Approx r Φ G β := by
      intro β hβ hne
      by_contra hc
      exact hne (hr.antisymm β γ0 hβ
        (hmin β ((hB β).mpr ⟨(hr.fld β γ0 hβ).1, hc⟩) (hr.fld β γ0 hβ).1))
    -- the union of the approximations below `γ0`
    obtain ⟨U, -, hU0⟩ := M.comp (σR l) (Fml.ex 0 (Fml.ex 3 (.and (fApp 2 0 8)
      (.and (.neg (.eq 0 8)) (.and (approxFml φ) (.mem 7 3)))))) 7
      (by simp [Fml.strat, Fml.ex, Fml.iff, Fml.imp, Fml.or, fApp, fPr, fOp, fSing, fUp, hsa, v0,
        v2, v3, v4, v5, v6, v7, v8, v9, v36, v37, v38])
      (Function.update (Function.update ρ 2 r) 8 γ0)
    have hU : ∀ t, M.mem t U ↔ ∃ β G, M.mem (M.op β γ0) r ∧ β ≠ γ0 ∧ M.Approx r Φ G β ∧
        M.mem t G := by
      intro t
      rw [hU0 t]
      have e : ∀ β G, Sat M.mem M.isSet (approxFml φ) (Function.update (Function.update
          (Function.update (Function.update (Function.update ρ 2 r) 8 γ0) 7 t) 0 β) 3 G) ↔
          M.Approx r Φ G β := fun β G => by
        rw [M.sat_approxFml hsat (upd_ge 3 (by decide) _ (upd_ge 0 (by decide) _
          (upd_ge 7 (by decide) _ (upd_ge 8 (by decide) _ hrge))))]
        simp [Function.update_apply]
      simp [Sat, M.sat_ex, M.sat_fApp, e, Function.update_apply]
    have hUpair : ∀ α y, M.mem (M.op α y) U → M.mem (M.op α γ0) r ∧ α ≠ γ0 := by
      intro α y hm
      obtain ⟨β, G, hβ, hne, hG, hm'⟩ := (hU _).mp hm
      have hαβ := ((hG α y).mp hm').1
      refine ⟨hr.trans α β γ0 hαβ hβ, fun e => ?_⟩
      rw [e] at hαβ
      exact hne (hr.antisymm β γ0 hβ hαβ)
    have hUiff : ∀ {α G : V}, M.Approx r Φ G α → M.mem (M.op α γ0) r → α ≠ γ0 → ∀ β y,
        M.mem (M.op β α) r → (M.mem (M.op β y) U ↔ M.mem (M.op β y) G) := by
      intro α G hG hα hne β y hβ
      constructor
      · intro hm
        obtain ⟨β', G', -, -, hG', hm'⟩ := (hU _).mp hm
        exact (agree hG' hG β y ((hG' β y).mp hm').1 hβ).mp hm'
      · intro hm
        exact (hU _).mpr ⟨α, G, hα, hne, hG, hm⟩
    -- the approximation at `γ0`
    obtain ⟨G0, -, hG00⟩ := M.comp (σR l) (Fml.or (.mem 7 3) (Fml.ex 4 (.and (.eq 4 0)
      (Fml.ex 5 (.and (fPr 7 4 5) (Fml.ex 6 (.and restrFml φ))))))) 7
      (by simp [restrFml, Fml.strat, Fml.ex, Fml.iff, Fml.imp, Fml.or, fApp, fPr, fOp, fSing, fUp,
        hφ, v0, v2, v3, v4, v5, v6, v7, v8, v9, v36, v37, v38])
      (Function.update (Function.update (Function.update ρ 2 r) 3 U) 0 γ0)
    have hG0' : ∀ t, M.mem t G0 ↔ M.mem t U ∨ ∃ y, t = M.op γ0 y ∧
        ∃ G', M.IsRestr r G' U γ0 ∧ Φ γ0 y G' := by
      intro t
      rw [hG00 t]
      have e := M.sat_at hsat (ρ' := Function.update (Function.update (Function.update
        (Function.update ρ 2 r) 3 U) 0 γ0) 7 t)
        (upd_ge 7 (by decide) _ (upd_ge 0 (by decide) _ (upd_ge 3 (by decide) _ hrge)))
      simp [Sat, M.sat_or, M.sat_ex, M.sat_fPr, M.sat_restrFml, e, Function.update_apply]
    have hG0 : ∀ α y, M.mem (M.op α y) G0 ↔ M.mem (M.op α y) U ∨
        (α = γ0 ∧ Φ γ0 y (M.restr r U γ0)) := by
      intro α y
      rw [hG0']
      refine or_congr Iff.rfl ⟨?_, ?_⟩
      · rintro ⟨y', e, h⟩
        obtain ⟨e1, e2⟩ := M.op_inj e
        rw [e2]
        exact ⟨e1, M.exists_restr_iff.mp h⟩
      · rintro ⟨e, h⟩
        exact ⟨y, by rw [e], M.exists_restr_iff.mpr h⟩
    have R1 : ∀ α, M.mem (M.op α γ0) r → ∀ β z, M.mem (M.op β α) r → β ≠ α →
        (M.mem (M.op β z) G0 ↔ M.mem (M.op β z) U) := by
      intro α hα β z hβ hne
      rw [hG0]
      refine ⟨fun h => h.resolve_right fun ⟨e, _⟩ => ?_, Or.inl⟩
      rw [e] at hβ
      exact hne (e.trans (hr.antisymm γ0 α hβ hα))
    refine hno0 ⟨G0, fun α y => ?_⟩
    by_cases hαle : M.mem (M.op α γ0) r
    · by_cases hαeq : α = γ0
      · rw [hαeq, hG0, M.restr_congr (R1 γ0 hγ0r)]
        constructor
        · rintro (h | ⟨-, h⟩)
          · exact absurd rfl (hUpair γ0 y h).2
          · exact ⟨hγ0r, h⟩
        · rintro ⟨-, h⟩
          exact Or.inr ⟨rfl, h⟩
      · obtain ⟨Gα, hGα⟩ := hbelow α hαle hαeq
        have hαα : M.mem (M.op α α) r := (hr.fld α γ0 hαle).1
        have e1 : M.restr r G0 α = M.restr r Gα α := M.restr_congr (fun β z hβ hne =>
          (R1 α hαle β z hβ hne).trans (hUiff hGα hαle hαeq β z hβ))
        rw [hG0, e1]
        constructor
        · rintro (h | ⟨e, -⟩)
          · exact ⟨hαle, ((hGα α y).mp ((hUiff hGα hαle hαeq α y hαα).mp h)).2⟩
          · exact absurd e hαeq
        · rintro ⟨-, h⟩
          exact Or.inl ((hUiff hGα hαle hαeq α y hαα).mpr ((hGα α y).mpr ⟨hαα, h⟩))
    · rw [hG0]
      constructor
      · rintro (h | ⟨e, -⟩)
        · exact absurd (hUpair α y h).1 hαle
        · rw [e] at hαle
          exact absurd hγ0r hαle
      · rintro ⟨h, -⟩
        exact absurd h hαle
  -- the union of all approximations
  obtain ⟨F, -, hF0⟩ := M.comp (σR l) (Fml.ex 0 (Fml.ex 3 (.and (fApp 2 0 0)
    (.and (approxFml φ) (.mem 7 3))))) 7
    (by simp [Fml.strat, Fml.ex, Fml.iff, Fml.imp, Fml.or, fApp, fPr, fOp, fSing, fUp, hsa, v0, v2,
      v3, v4, v5, v6, v7, v8, v9, v36, v37, v38])
    (Function.update ρ 2 r)
  have hF : ∀ t, M.mem t F ↔ ∃ γ G, M.mem (M.op γ γ) r ∧ M.Approx r Φ G γ ∧ M.mem t G := by
    intro t
    rw [hF0 t]
    have e : ∀ γ G, Sat M.mem M.isSet (approxFml φ) (Function.update (Function.update
        (Function.update (Function.update ρ 2 r) 7 t) 0 γ) 3 G) ↔ M.Approx r Φ G γ := fun γ G => by
      rw [M.sat_approxFml hsat (upd_ge 3 (by decide) _ (upd_ge 0 (by decide) _
        (upd_ge 7 (by decide) _ hrge)))]
      simp [Function.update_apply]
    simp [Sat, M.sat_ex, M.sat_fApp, e, Function.update_apply]
  have key : ∀ {γ G : V}, M.mem (M.op γ γ) r → M.Approx r Φ G γ → ∀ α, M.mem (M.op α γ) r →
      M.restr r F α = M.restr r G α := by
    intro γ G hγ hG α hα
    refine M.restr_congr fun β z hβ hne => ⟨fun hm => ?_, fun hm => (hF _).mpr ⟨γ, G, hγ, hG, hm⟩⟩
    obtain ⟨γ', G', hγ', hG', hm'⟩ := (hF _).mp hm
    exact (agree hG' hG β z ((hG' β z).mp hm').1 (hr.trans β α γ hβ hα)).mp hm'
  refine ⟨F, fun α y => ⟨fun hm => ?_, fun ⟨hα, hΦ⟩ => ?_⟩⟩
  · obtain ⟨γ, G, hγ, hG, hm'⟩ := (hF _).mp hm
    obtain ⟨hαγ, hΦ⟩ := (hG α y).mp hm'
    rw [key hγ hG α hαγ]
    exact ⟨(hr.fld α γ hαγ).1, hΦ⟩
  · obtain ⟨G, hG⟩ := exists_approx α hα
    rw [key hα hG α hα] at hΦ
    exact (hF _).mpr ⟨α, G, hα, hG, (hG α y).mpr ⟨hα, hΦ⟩⟩

/-! ### Products and sums of well-orderings on a rung (§3.3, step 2, last sentence) -/

/-- The lexicographic order on pairs: `c = (a, b)`, `c' = (a', b')` on rung `i`, with
`a < a'` in `w`, or `a = a'` and `b ≤ b'` in `w'`. -/
def LexRaw (P i w w' c c' : V) : Prop :=
  ∃ a b a' b', M.mem (M.quad i a b c) P ∧ M.mem (M.quad i a' b' c') P ∧
    M.mem (M.op a a) w ∧ M.mem (M.op a' a') w ∧ M.mem (M.op b b) w' ∧ M.mem (M.op b' b') w' ∧
    ((M.mem (M.op a a') w ∧ a ≠ a') ∨ (a = a' ∧ M.mem (M.op b b') w'))

theorem exists_lex (P i w w' : V) :
    ∃ p, ∀ c c', M.mem (M.op c c') p ↔ M.LexRaw P i w w' c c' := by
  obtain ⟨p, -, hp0⟩ := M.comp (σW [(0, 4), (1, 5), (2, 5), (3, 7)])
    (Fml.ex 15 (Fml.ex 16 (.and (fPr 0 15 16) (Fml.ex 8 (Fml.ex 9 (Fml.ex 10 (Fml.ex 11
      (.and (fApp4 3 5 8 9 15) (.and (fApp4 3 5 10 11 16) (.and (fApp 1 8 8) (.and (fApp 1 10 10)
      (.and (fApp 2 9 9) (.and (fApp 2 11 11) (Fml.or (.and (fApp 1 8 10) (.neg (.eq 8 10)))
        (.and (.eq 8 10) (fApp 2 9 11)))))))))))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 1 w)
      2 w') 3 P) 5 i)
  have hp : ∀ t, M.mem t p ↔ ∃ c c', t = M.op c c' ∧ M.LexRaw P i w w' c c' := by
    intro t
    rw [hp0 t]
    simp [LexRaw, Sat, M.sat_ex, M.sat_or, M.sat_fPr, M.sat_fApp, M.sat_fApp4,
      Function.update_apply]
  refine ⟨p, fun c c' => ⟨fun h => ?_, fun h => (hp _).mpr ⟨c, c', rfl, h⟩⟩⟩
  obtain ⟨d, d', e, h'⟩ := (hp _).mp h
  obtain ⟨e1, e2⟩ := M.op_inj e
  rw [e1, e2]
  exact h'

/-- **The lexicographic product of two well-orderings of subsets of a rung** is a
well-ordering of a subset of the same rung. -/
theorem wo_lex {R P : V} {m i : M.Num} (hP : M.IsPairing R P m) {w w' p : V} (hw : M.IsWO w)
    (hw' : M.IsWO w') (hp : ∀ c c', M.mem (M.op c c') p ↔ M.LexRaw P i.1 w w' c c') :
    M.IsWO p ∧ ∀ c c', M.mem (M.op c c') p → M.mem (M.op i.1 c) R ∧ M.mem (M.op i.1 c') R := by
  refine ⟨⟨fun c c' h => ?_, fun c c' c'' h1 h2 => ?_, fun c c' h1 h2 => ?_, fun X hX => ?_⟩,
    fun c c' h => ?_⟩
  · obtain ⟨a, b, a', b', q, q', ha, ha', hb, hb', -⟩ := (hp c c').mp h
    exact ⟨(hp c c).mpr ⟨a, b, a, b, q, q, ha, ha, hb, hb, Or.inr ⟨rfl, hb⟩⟩,
      (hp c' c').mpr ⟨a', b', a', b', q', q', ha', ha', hb', hb', Or.inr ⟨rfl, hb'⟩⟩⟩
  · obtain ⟨a, b, a', b', q, q', ha, ha', hb, hb', k1⟩ := (hp c c').mp h1
    obtain ⟨x', y', a'', b'', r', q'', -, ha'', -, hb'', k2⟩ := (hp c' c'').mp h2
    obtain ⟨e1, e2⟩ := hP.inj _ _ _ _ _ _ r' q'
    rw [e1, e2] at k2
    refine (hp c c'').mpr ⟨a, b, a'', b'', q, q'', ha, ha'', hb, hb'', ?_⟩
    rcases k1 with ⟨l1, n1⟩ | ⟨e, l1⟩
    · rcases k2 with ⟨l2, n2⟩ | ⟨e', l2⟩
      · refine Or.inl ⟨hw.trans _ _ _ l1 l2, fun e => ?_⟩
        rw [← e] at l2
        exact n1 (hw.antisymm a a' l1 l2)
      · rw [← e']
        exact Or.inl ⟨l1, n1⟩
    · rcases k2 with ⟨l2, n2⟩ | ⟨e', l2⟩
      · rw [e]
        exact Or.inl ⟨l2, n2⟩
      · exact Or.inr ⟨e.trans e', hw'.trans _ _ _ l1 l2⟩
  · obtain ⟨a, b, a', b', q, q', ha, ha', hb, hb', k1⟩ := (hp c c').mp h1
    obtain ⟨x', y', x, y, r', r, -, -, -, -, k2⟩ := (hp c' c).mp h2
    obtain ⟨e1, e2⟩ := hP.inj _ _ _ _ _ _ r' q'
    obtain ⟨e3, e4⟩ := hP.inj _ _ _ _ _ _ r q
    rw [e1, e2, e3, e4] at k2
    rcases k1 with ⟨l1, n1⟩ | ⟨e, l1⟩
    · rcases k2 with ⟨l2, n2⟩ | ⟨e', l2⟩
      · exact absurd (hw.antisymm a a' l1 l2) n1
      · exact absurd e'.symm n1
    · rcases k2 with ⟨l2, n2⟩ | ⟨e', l2⟩
      · exact absurd e.symm n2
      · have eb : b = b' := hw'.antisymm b b' l1 l2
        rw [← e, ← eb] at q'
        exact hP.fn _ _ _ _ _ q q'
  · obtain ⟨c0, hc0X, hc0p⟩ := hX
    obtain ⟨a0, b0, -, -, q0, -, ha0, -, hb0, -, -⟩ := (hp c0 c0).mp hc0p
    -- the first coordinates of members of `X`
    obtain ⟨A1, -, hA0⟩ := M.comp (σW [(1, 5), (2, 5), (3, 7), (4, 3)])
      (Fml.ex 9 (Fml.ex 15 (.and (.mem 15 4) (.and (fApp4 3 5 0 9 15) (.and (fApp 1 0 0)
        (fApp 2 9 9)))))) 0 rfl
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (fun _ => dflt) 1 w) 2 w') 3 P) 4 X) 5 i.1)
    have hA : ∀ a, M.mem a A1 ↔ ∃ b c, M.mem c X ∧ M.mem (M.quad i.1 a b c) P ∧
        M.mem (M.op a a) w ∧ M.mem (M.op b b) w' := by
      intro a
      rw [hA0 a]
      simp [Sat, M.sat_ex, M.sat_fApp, M.sat_fApp4, Function.update_apply]
    obtain ⟨a1, ha1A, ha1w, hmin1⟩ := hw.least A1 ⟨a0, (hA a0).mpr ⟨b0, c0, hc0X, q0, ha0, hb0⟩, ha0⟩
    obtain ⟨b0', c0', hc0'X, q0', -, hb0'⟩ := (hA a1).mp ha1A
    -- the second coordinates over the least first coordinate
    obtain ⟨B1, -, hB0⟩ := M.comp (σW [(2, 5), (3, 7), (4, 3)])
      (Fml.ex 15 (.and (.mem 15 4) (.and (fApp4 3 5 8 0 15) (fApp 2 0 0)))) 0 rfl
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (fun _ => dflt) 2 w') 3 P) 4 X) 5 i.1) 8 a1)
    have hB : ∀ b, M.mem b B1 ↔ ∃ c, M.mem c X ∧ M.mem (M.quad i.1 a1 b c) P ∧
        M.mem (M.op b b) w' := by
      intro b
      rw [hB0 b]
      simp [Sat, M.sat_ex, M.sat_fApp, M.sat_fApp4, Function.update_apply]
    obtain ⟨b1, hb1B, hb1w, hmin2⟩ := hw'.least B1 ⟨b0', (hB b0').mpr ⟨c0', hc0'X, q0', hb0'⟩, hb0'⟩
    obtain ⟨c1, hc1X, q1, -⟩ := (hB b1).mp hb1B
    refine ⟨c1, hc1X, (hp c1 c1).mpr ⟨a1, b1, a1, b1, q1, q1, ha1w, ha1w, hb1w, hb1w,
      Or.inr ⟨rfl, hb1w⟩⟩, fun c hcX hcp => ?_⟩
    obtain ⟨a, b, -, -, q, -, ha, -, hb, -, -⟩ := (hp c c).mp hcp
    refine (hp c1 c).mpr ⟨a1, b1, a, b, q1, q, ha1w, ha, hb1w, hb, ?_⟩
    have hle : M.mem (M.op a1 a) w := hmin1 a ((hA a).mpr ⟨b, c, hcX, q, ha, hb⟩) ha
    by_cases e : a1 = a
    · refine Or.inr ⟨e, hmin2 b ((hB b).mpr ⟨c, hcX, ?_, hb⟩) hb⟩
      rw [e]
      exact q
    · exact Or.inl ⟨hle, e⟩
  · obtain ⟨a, b, a', b', q, q', -⟩ := (hp c c').mp h
    exact ⟨(hP.dom _ _ _ _ q).2.2.2, (hP.dom _ _ _ _ q').2.2.2⟩

/-- The order of the sum: the copy of `w` tagged `u` below the copy of `w'` tagged `v`. -/
def SumRaw (P i u v w w' c c' : V) : Prop :=
  (∃ a a', M.mem (M.quad i u a c) P ∧ M.mem (M.quad i u a' c') P ∧ M.mem (M.op a a') w) ∨
  (∃ b b', M.mem (M.quad i v b c) P ∧ M.mem (M.quad i v b' c') P ∧ M.mem (M.op b b') w') ∨
  (∃ a b, M.mem (M.quad i u a c) P ∧ M.mem (M.quad i v b c') P ∧ M.mem (M.op a a) w ∧
    M.mem (M.op b b) w')

theorem exists_sum (P i u v w w' : V) :
    ∃ s, ∀ c c', M.mem (M.op c c') s ↔ M.SumRaw P i u v w w' c c' := by
  obtain ⟨s, -, hs0⟩ := M.comp (σW [(0, 4), (1, 5), (2, 5), (3, 7)])
    (Fml.ex 15 (Fml.ex 16 (.and (fPr 0 15 16) (Fml.or
      (Fml.ex 8 (Fml.ex 10 (.and (fApp4 3 5 6 8 15) (.and (fApp4 3 5 6 10 16) (fApp 1 8 10)))))
      (Fml.or
      (Fml.ex 9 (Fml.ex 11 (.and (fApp4 3 5 7 9 15) (.and (fApp4 3 5 7 11 16) (fApp 2 9 11)))))
      (Fml.ex 8 (Fml.ex 9 (.and (fApp4 3 5 6 8 15) (.and (fApp4 3 5 7 9 16) (.and (fApp 1 8 8)
        (fApp 2 9 9))))))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (fun _ => dflt) 1 w) 2 w') 3 P) 5 i) 6 u) 7 v)
  have hs : ∀ t, M.mem t s ↔ ∃ c c', t = M.op c c' ∧ M.SumRaw P i u v w w' c c' := by
    intro t
    rw [hs0 t]
    simp [SumRaw, Sat, M.sat_ex, M.sat_or, M.sat_fPr, M.sat_fApp, M.sat_fApp4,
      Function.update_apply]
  refine ⟨s, fun c c' => ⟨fun h => ?_, fun h => (hs _).mpr ⟨c, c', rfl, h⟩⟩⟩
  obtain ⟨d, d', e, h'⟩ := (hs _).mp h
  obtain ⟨e1, e2⟩ := M.op_inj e
  rw [e1, e2]
  exact h'

/-- **The sum of two well-orderings of subsets of a rung** is a well-ordering of a subset of
the same rung. -/
theorem wo_sum {R P : V} {m i : M.Num} (hP : M.IsPairing R P m) {u v w w' s : V} (huv : u ≠ v)
    (hw : M.IsWO w) (hw' : M.IsWO w')
    (hs : ∀ c c', M.mem (M.op c c') s ↔ M.SumRaw P i.1 u v w w' c c') :
    M.IsWO s ∧ ∀ c c', M.mem (M.op c c') s → M.mem (M.op i.1 c) R ∧ M.mem (M.op i.1 c') R := by
  -- a point is in exactly one of the two copies
  have clash : ∀ {a b c : V}, M.mem (M.quad i.1 u a c) P → M.mem (M.quad i.1 v b c) P → False :=
    fun q q' => huv (hP.inj _ _ _ _ _ _ q q').1
  refine ⟨⟨fun c c' h => ?_, fun c c' c'' h1 h2 => ?_, fun c c' h1 h2 => ?_, fun X hX => ?_⟩,
    fun c c' h => ?_⟩
  · rcases (hs c c').mp h with ⟨a, a', q, q', l⟩ | ⟨b, b', q, q', l⟩ | ⟨a, b, q, q', ha, hb⟩
    · exact ⟨(hs c c).mpr (Or.inl ⟨a, a, q, q, (hw.fld a a' l).1⟩),
        (hs c' c').mpr (Or.inl ⟨a', a', q', q', (hw.fld a a' l).2⟩)⟩
    · exact ⟨(hs c c).mpr (Or.inr (Or.inl ⟨b, b, q, q, (hw'.fld b b' l).1⟩)),
        (hs c' c').mpr (Or.inr (Or.inl ⟨b', b', q', q', (hw'.fld b b' l).2⟩))⟩
    · exact ⟨(hs c c).mpr (Or.inl ⟨a, a, q, q, ha⟩),
        (hs c' c').mpr (Or.inr (Or.inl ⟨b, b, q', q', hb⟩))⟩
  · rcases (hs c c').mp h1 with ⟨a, a', q, q', l⟩ | ⟨b, b', q, q', l⟩ | ⟨a, b, q, q', ha, hb⟩
    · rcases (hs c' c'').mp h2 with ⟨x, x', r, r', l'⟩ | ⟨y, y', r, r', l'⟩ | ⟨x, y, r, r', hx, hy⟩
      · rw [(hP.inj _ _ _ _ _ _ r q').2] at l'
        exact (hs c c'').mpr (Or.inl ⟨a, x', q, r', hw.trans _ _ _ l l'⟩)
      · exact absurd (clash q' r) id
      · exact (hs c c'').mpr (Or.inr (Or.inr ⟨a, y, q, r', (hw.fld a a' l).1, hy⟩))
    · rcases (hs c' c'').mp h2 with ⟨x, x', r, r', l'⟩ | ⟨y, y', r, r', l'⟩ | ⟨x, y, r, r', hx, hy⟩
      · exact absurd (clash r q') id
      · rw [(hP.inj _ _ _ _ _ _ r q').2] at l'
        exact (hs c c'').mpr (Or.inr (Or.inl ⟨b, y', q, r', hw'.trans _ _ _ l l'⟩))
      · exact absurd (clash r q') id
    · rcases (hs c' c'').mp h2 with ⟨x, x', r, r', l'⟩ | ⟨y, y', r, r', l'⟩ | ⟨x, y, r, r', hx, hy⟩
      · exact absurd (clash r q') id
      · exact (hs c c'').mpr (Or.inr (Or.inr ⟨a, y', q, r', ha, (hw'.fld y y' l').2⟩))
      · exact absurd (clash r q') id
  · rcases (hs c c').mp h1 with ⟨a, a', q, q', l⟩ | ⟨b, b', q, q', l⟩ | ⟨a, b, q, q', ha, hb⟩
    · rcases (hs c' c).mp h2 with ⟨x, x', r, r', l'⟩ | ⟨y, y', r, r', l'⟩ | ⟨x, y, r, r', hx, hy⟩
      · rw [(hP.inj _ _ _ _ _ _ r q').2, (hP.inj _ _ _ _ _ _ r' q).2] at l'
        have e : a = a' := hw.antisymm a a' l l'
        rw [← e] at q'
        exact hP.fn _ _ _ _ _ q q'
      · exact absurd (clash q r') id
      · exact absurd (clash q r') id
    · rcases (hs c' c).mp h2 with ⟨x, x', r, r', l'⟩ | ⟨y, y', r, r', l'⟩ | ⟨x, y, r, r', hx, hy⟩
      · exact absurd (clash r' q) id
      · rw [(hP.inj _ _ _ _ _ _ r q').2, (hP.inj _ _ _ _ _ _ r' q).2] at l'
        have e : b = b' := hw'.antisymm b b' l l'
        rw [← e] at q'
        exact hP.fn _ _ _ _ _ q q'
      · exact absurd (clash r q') id
    · rcases (hs c' c).mp h2 with ⟨x, x', r, r', l'⟩ | ⟨y, y', r, r', l'⟩ | ⟨x, y, r, r', hx, hy⟩
      · exact absurd (clash r q') id
      · exact absurd (clash q r') id
      · exact absurd (clash r q') id
  · obtain ⟨c0, hc0X, hc0s⟩ := hX
    -- the members of `X` in the first copy
    obtain ⟨A1, -, hA0⟩ := M.comp (σW [(1, 5), (3, 7), (4, 3)])
      (Fml.ex 15 (.and (.mem 15 4) (.and (fApp4 3 5 6 0 15) (fApp 1 0 0)))) 0 rfl
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (fun _ => dflt) 1 w) 3 P) 4 X) 5 i.1) 6 u)
    have hA : ∀ a, M.mem a A1 ↔ ∃ c, M.mem c X ∧ M.mem (M.quad i.1 u a c) P ∧
        M.mem (M.op a a) w := by
      intro a
      rw [hA0 a]
      simp [Sat, M.sat_ex, M.sat_fApp, M.sat_fApp4, Function.update_apply]
    obtain ⟨B1, -, hB0⟩ := M.comp (σW [(2, 5), (3, 7), (4, 3)])
      (Fml.ex 15 (.and (.mem 15 4) (.and (fApp4 3 5 7 0 15) (fApp 2 0 0)))) 0 rfl
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (fun _ => dflt) 2 w') 3 P) 4 X) 5 i.1) 7 v)
    have hB : ∀ b, M.mem b B1 ↔ ∃ c, M.mem c X ∧ M.mem (M.quad i.1 v b c) P ∧
        M.mem (M.op b b) w' := by
      intro b
      rw [hB0 b]
      simp [Sat, M.sat_ex, M.sat_fApp, M.sat_fApp4, Function.update_apply]
    -- a point of the field is in one of the copies
    have cases : ∀ c, M.mem (M.op c c) s →
        (∃ a, M.mem (M.quad i.1 u a c) P ∧ M.mem (M.op a a) w) ∨
        (∃ b, M.mem (M.quad i.1 v b c) P ∧ M.mem (M.op b b) w') := by
      intro c hc
      rcases (hs c c).mp hc with ⟨a, a', q, -, l⟩ | ⟨b, b', q, -, l⟩ | ⟨a, b, q, q', -, -⟩
      · exact Or.inl ⟨a, q, (hw.fld a a' l).1⟩
      · exact Or.inr ⟨b, q, (hw'.fld b b' l).1⟩
      · exact absurd (clash q q') id
    by_cases hA1 : ∃ a, M.mem a A1
    · obtain ⟨a0, ha0⟩ := hA1
      obtain ⟨c00, -, -, ha0w⟩ := (hA a0).mp ha0
      obtain ⟨a1, ha1A, ha1w, hmin⟩ := hw.least A1 ⟨a0, ha0, ha0w⟩
      obtain ⟨c1, hc1X, q1, -⟩ := (hA a1).mp ha1A
      refine ⟨c1, hc1X, (hs c1 c1).mpr (Or.inl ⟨a1, a1, q1, q1, ha1w⟩), fun c hcX hcs => ?_⟩
      rcases cases c hcs with ⟨a, q, ha⟩ | ⟨b, q, hb⟩
      · exact (hs c1 c).mpr (Or.inl ⟨a1, a, q1, q, hmin a ((hA a).mpr ⟨c, hcX, q, ha⟩) ha⟩)
      · exact (hs c1 c).mpr (Or.inr (Or.inr ⟨a1, b, q1, q, ha1w, hb⟩))
    · rcases cases c0 hc0s with ⟨a, q, ha⟩ | ⟨b0, q0, hb0⟩
      · exact absurd ⟨a, (hA a).mpr ⟨c0, hc0X, q, ha⟩⟩ hA1
      · obtain ⟨b1, hb1B, hb1w, hmin⟩ := hw'.least B1 ⟨b0, (hB b0).mpr ⟨c0, hc0X, q0, hb0⟩, hb0⟩
        obtain ⟨c1, hc1X, q1, -⟩ := (hB b1).mp hb1B
        refine ⟨c1, hc1X, (hs c1 c1).mpr (Or.inr (Or.inl ⟨b1, b1, q1, q1, hb1w⟩)),
          fun c hcX hcs => ?_⟩
        rcases cases c hcs with ⟨a, q, ha⟩ | ⟨b, q, hb⟩
        · exact absurd ⟨a, (hA a).mpr ⟨c, hcX, q, ha⟩⟩ hA1
        · exact (hs c1 c).mpr (Or.inr (Or.inl ⟨b1, b, q1, q,
            hmin b ((hB b).mpr ⟨c, hcX, q, hb⟩) hb⟩))
  · rcases (hs c c').mp h with ⟨a, a', q, q', -⟩ | ⟨b, b', q, q', -⟩ | ⟨a, b, q, q', -, -⟩
    · exact ⟨(hP.dom _ _ _ _ q).2.2.2, (hP.dom _ _ _ _ q').2.2.2⟩
    · exact ⟨(hP.dom _ _ _ _ q).2.2.2, (hP.dom _ _ _ _ q').2.2.2⟩
    · exact ⟨(hP.dom _ _ _ _ q).2.2.2, (hP.dom _ _ _ _ q').2.2.2⟩

/-- A well-ordering that embeds in `H` but not conversely is isomorphic to the predecessors
of a point of `H`. -/
theorem seg_of_strict {w H : V} (hH : M.IsWO H) (h1 : M.Emb w H) (h2 : ¬ M.Emb H w) :
    ∃ e f, M.mem (M.op e e) H ∧ M.SegOf w H f e := by
  obtain ⟨f, hf, hfull⟩ := h1
  rcases M.piso_onto_or_seg hH hf hfull with honto | ⟨e, he, hseg⟩
  · exact absurd ⟨M.conv f, M.piso_conv hf, fun y hy => by
      obtain ⟨x, hx⟩ := honto y hy
      exact ⟨x, M.mem_conv.mpr hx⟩⟩ h2
  · exact ⟨e, f, he, hseg⟩

/-! ## The natural numbers as a set well-ordering -/

/-- **The least number principle**: a set that contains a number contains a least one. -/
theorem nat_least {X : V} (hX : ∃ n : M.Num, M.mem n.1 X) :
    ∃ a : M.Num, M.mem a.1 X ∧ ∀ b : M.Num, M.mem b.1 X → a ≤ b := by
  have had := M.adG_spec
  have hsat : ∀ n : M.Num, Sat M.mem M.isSet
      (Fml.imp (Fml.ex 8 (.and (.mem 8 6) (.and (fLe 8 0) (.mem 8 1))))
        (Fml.ex 9 (.and (.mem 9 6) (.and (.mem 9 1)
          (.all 10 (Fml.imp (.mem 10 6) (Fml.imp (.mem 10 1) (fLe 9 10))))))))
      (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 1 X)
        6 M.nat) 7 M.adG) 0 n.1) ↔
      ((∃ k : M.Num, k ≤ n ∧ M.mem k.1 X) →
        ∃ a : M.Num, M.mem a.1 X ∧ ∀ b : M.Num, M.mem b.1 X → a ≤ b) := by
    intro n
    have h1 : Sat M.mem M.isSet
        (Fml.imp (Fml.ex 8 (.and (.mem 8 6) (.and (fLe 8 0) (.mem 8 1))))
          (Fml.ex 9 (.and (.mem 9 6) (.and (.mem 9 1)
            (.all 10 (Fml.imp (.mem 10 6) (Fml.imp (.mem 10 1) (fLe 9 10))))))))
        (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 1 X)
          6 M.nat) 7 M.adG) 0 n.1) ↔
        ((∃ k, M.mem k M.nat ∧ M.LeRaw M.adG k n.1 ∧ M.mem k X) →
          ∃ a, M.mem a M.nat ∧ M.mem a X ∧ ∀ b, M.mem b M.nat → M.mem b X →
            M.LeRaw M.adG a b) := by
      simp [fLe, LeRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fApp3, Function.update_apply]
    rw [h1]
    constructor
    · rintro h ⟨k, hk, hkX⟩
      obtain ⟨a, ha, haX, hmin⟩ := h ⟨k.1, k.2, (M.leRaw_iff had k n).mpr hk, hkX⟩
      exact ⟨⟨a, ha⟩, haX, fun b hb => (M.leRaw_iff had ⟨a, ha⟩ b).mp (hmin b.1 b.2 hb)⟩
    · rintro h ⟨k, hk, hkn, hkX⟩
      obtain ⟨a, haX, hmin⟩ := h ⟨⟨k, hk⟩, (M.leRaw_iff had ⟨k, hk⟩ n).mp hkn, hkX⟩
      exact ⟨a.1, a.2, haX, fun b hb hbX => (M.leRaw_iff had a ⟨b, hb⟩).mpr (hmin ⟨b, hb⟩ hbX)⟩
  have key : ∀ n : M.Num, (∃ k : M.Num, k ≤ n ∧ M.mem k.1 X) →
      ∃ a : M.Num, M.mem a.1 X ∧ ∀ b : M.Num, M.mem b.1 X → a ≤ b := by
    intro n
    rw [← hsat n]
    refine M.num_ind_fml (σW [(1, 3), (6, 3), (7, 7)]) _ 0 rfl _ ?_ (fun k ih => ?_) n
    · rw [show M.zero = (0 : M.Num).1 from rfl, hsat 0]
      rintro ⟨k, hk, hkX⟩
      have e : k = 0 := le_antisymm hk zero_le
      rw [e] at hkX
      exact ⟨0, hkX, fun b _ => zero_le⟩
    · rw [hsat k] at ih
      rw [show M.succ k.1 = (k + 1).1 from (M.val_add_one k).symm, hsat (k + 1)]
      rintro ⟨j, hj, hjX⟩
      by_cases hlow : ∃ j' : M.Num, j' ≤ k ∧ M.mem j'.1 X
      · exact ih hlow
      · rcases M.eq_or_succ_le hj with e | hlt
        · refine ⟨k + 1, e ▸ hjX, fun b hbX => ?_⟩
          rcases M.lt_trichotomy' b (k + 1) with e' | h' | h'
          · rw [e']
          · exact absurd ⟨b, M.le_of_succ_le_succ h', hbX⟩ hlow
          · exact le_trans (M.le_add_one (k + 1)) h'
        · exact absurd ⟨j, M.le_of_succ_le_succ hlt, hjX⟩ hlow
  obtain ⟨n, hn⟩ := hX
  exact key n ⟨n, le_refl n, hn⟩

theorem exists_natLe : ∃ r, ∀ a b, M.mem (M.op a b) r ↔
    ∃ x y : M.Num, x.1 = a ∧ y.1 = b ∧ x ≤ y := by
  have had := M.adG_spec
  obtain ⟨r, -, hr0⟩ := M.comp (σW [(0, 4), (6, 3), (7, 7)])
    (Fml.ex 8 (Fml.ex 9 (.and (fPr 0 8 9) (.and (.mem 8 6) (.and (.mem 9 6) (fLe 8 9)))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 6 M.nat) 7 M.adG)
  have hr : ∀ t, M.mem t r ↔ ∃ a b, t = M.op a b ∧ M.mem a M.nat ∧ M.mem b M.nat ∧
      M.LeRaw M.adG a b := by
    intro t
    rw [hr0 t]
    simp [fLe, LeRaw, Sat, M.sat_ex, M.sat_fPr, M.sat_fApp3, Function.update_apply]
  refine ⟨r, fun a b => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨a', b', e, ha, hb, hle⟩ := (hr _).mp h
    obtain ⟨e1, e2⟩ := M.op_inj e
    exact ⟨⟨a', ha⟩, ⟨b', hb⟩, e1.symm, e2.symm, (M.leRaw_iff had ⟨a', ha⟩ ⟨b', hb⟩).mp hle⟩
  · rintro ⟨x, y, hx, hy, hle⟩
    exact (hr _).mpr ⟨x.1, y.1, by rw [hx, hy], x.2, y.2, (M.leRaw_iff had x y).mpr hle⟩

/-- The order of the natural numbers, as a set of pairs. -/
noncomputable def natLe : V := Classical.choose M.exists_natLe

theorem mem_natLe {a b : V} : M.mem (M.op a b) M.natLe ↔
    ∃ x y : M.Num, x.1 = a ∧ y.1 = b ∧ x ≤ y := Classical.choose_spec M.exists_natLe a b

theorem natLe_iff (x y : M.Num) : M.mem (M.op x.1 y.1) M.natLe ↔ x ≤ y := by
  rw [M.mem_natLe]
  constructor
  · rintro ⟨x', y', hx, hy, hle⟩
    rw [← Subtype.ext hx, ← Subtype.ext hy]
    exact hle
  · intro h
    exact ⟨x, y, rfl, rfl, h⟩

/-- **The natural numbers are a set well-ordering.** -/
theorem isWO_natLe : M.IsWO M.natLe := by
  refine ⟨fun a b h => ?_, fun a b c h1 h2 => ?_, fun a b h1 h2 => ?_, fun X hX => ?_⟩
  · obtain ⟨x, y, hx, hy, -⟩ := M.mem_natLe.mp h
    exact ⟨M.mem_natLe.mpr ⟨x, x, hx, hx, le_refl x⟩, M.mem_natLe.mpr ⟨y, y, hy, hy, le_refl y⟩⟩
  · obtain ⟨x, y, hx, hy, hle⟩ := M.mem_natLe.mp h1
    obtain ⟨y', z, hy', hz, hle'⟩ := M.mem_natLe.mp h2
    have e : y' = y := Subtype.ext (hy'.trans hy.symm)
    rw [e] at hle'
    exact M.mem_natLe.mpr ⟨x, z, hx, hz, le_trans hle hle'⟩
  · obtain ⟨x, y, hx, hy, hle⟩ := M.mem_natLe.mp h1
    obtain ⟨y', x', hy', hx', hle'⟩ := M.mem_natLe.mp h2
    have e1 : y' = y := Subtype.ext (hy'.trans hy.symm)
    have e2 : x' = x := Subtype.ext (hx'.trans hx.symm)
    rw [e1, e2] at hle'
    rw [← hx, ← hy, le_antisymm hle hle']
  · obtain ⟨a0, ha0X, ha0r⟩ := hX
    obtain ⟨x0, -, hx0, -, -⟩ := M.mem_natLe.mp ha0r
    obtain ⟨a, haX, hmin⟩ := M.nat_least (X := X) ⟨x0, by rw [hx0]; exact ha0X⟩
    refine ⟨a.1, haX, (M.natLe_iff a a).mpr (le_refl a), fun b hbX hbr => ?_⟩
    obtain ⟨y, -, hy, -, -⟩ := M.mem_natLe.mp hbr
    rw [← hy]
    exact (M.natLe_iff a y).mpr (hmin y (by rw [hy]; exact hbX))

/-! ## Finite sequences on a rung (§3.3, step 1, last part)

With the pairing of rung `j`, every member `t` of the rung is read as a sequence: its entry
`0` is `a` if `t` is the pair `(a, t')`, and its entry `n + 1` is the entry `n` of `t'`. The
relation "the entry `n` of `t` is `a`" is a set, by recursion on `n`. -/

/-- One step of the recursion for entries: `y` is the pair `(t, a)`, `t` is a pair `(a', t')`,
and either `n = 0` and `a = a'`, or `n = k + 1` and the pair `(t', a)` was obtained at `k`. -/
def NthStepRaw (P j z n y G : V) : Prop :=
  ∃ t a a' t', M.mem (M.quad j t a y) P ∧ M.mem (M.quad j a' t' t) P ∧
    ((n = z ∧ a = a') ∨ ∃ k y', n = M.succ k ∧ M.mem (M.quad j t' a y') P ∧ M.mem (M.op k y') G)

/-- `NthStepRaw`, with `P`, `j`, `0`, `n`, `y`, `G` the names `20`, `25`, `21`, `4`, `5`, `6`. -/
def nthFml : Fml :=
  Fml.ex 11 (Fml.ex 12 (Fml.ex 13 (Fml.ex 15 (.and (fApp4 20 25 11 12 5)
    (.and (fApp4 20 25 13 15 11) (Fml.or (.and (.eq 4 21) (.eq 12 13))
      (Fml.ex 16 (Fml.ex 17 (.and (fSuccEq 4 16) (.and (fApp4 20 25 15 12 17)
        (fApp 6 16 17)))))))))))

theorem sat_nthFml (ρ : ℕ → V) : Sat M.mem M.isSet nthFml ρ ↔
    M.NthStepRaw (ρ 20) (ρ 25) (ρ 21) (ρ 4) (ρ 5) (ρ 6) := by
  simp [nthFml, NthStepRaw, Sat, M.sat_ex, M.sat_or, M.sat_fApp4, M.sat_fApp, M.sat_fSuccEq,
    Function.update_apply]

/-- **Finite sequences on a rung.** For a rung `j` with pairing there is a set `Nt` of triples
`⟨t, n, a⟩`, "the entry `n` of `t` is `a`", such that the entry `0` of `t` is `a` exactly when
`t` is a pair `(a, t')`, and the entry `n + 1` of `t` is `b` exactly when `t` is a pair
`(a, t')` and the entry `n` of `t'` is `b`. -/
theorem exists_seq {R P : V} {m j : M.Num} (hP : M.IsPairing R P m) (hj : j ≤ m) :
    ∃ Nt, (∀ t n a, M.mem (M.trip t n a) Nt →
        M.mem n M.nat ∧ M.mem (M.op j.1 t) R ∧ M.mem (M.op j.1 a) R) ∧
      (∀ t a, M.mem (M.trip t M.zero a) Nt ↔ ∃ t', M.mem (M.quad j.1 a t' t) P) ∧
      ∀ (n : M.Num) (t b : V), M.mem (M.trip t (n + 1).1 b) Nt ↔
        ∃ a t', M.mem (M.quad j.1 a t' t) P ∧ M.mem (M.trip t' n.1 b) Nt := by
  obtain ⟨ρ, e20, e21, e25⟩ : ∃ ρ : ℕ → V, ρ 20 = P ∧ ρ 21 = M.zero ∧ ρ 25 = j.1 :=
    ⟨Function.update (Function.update (Function.update (fun _ => dflt) 20 P) 21 M.zero) 25 j.1,
      by simp [Function.update_apply]⟩
  obtain ⟨F, hF⟩ := M.wo_rec M.isWO_natLe (fun n y G => M.NthStepRaw P j.1 M.zero n y G) nthFml
    [(20, 7)] rfl ρ (fun ρ' h => by
      rw [M.sat_nthFml, h 20 (by decide), h 21 (by decide), h 25 (by decide), e20, e21, e25])
  obtain ⟨Nt, -, hN0⟩ := M.comp (σW [(0, 6), (1, 5), (3, 7)])
    (Fml.ex 11 (Fml.ex 12 (Fml.ex 13 (Fml.ex 15 (.and (fTrip 0 11 12 13)
      (.and (fApp4 3 5 11 13 15) (fApp 1 12 15))))))) 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 1 F) 3 P) 5 j.1)
  have hN1 : ∀ q, M.mem q Nt ↔ ∃ t n a y, q = M.trip t n a ∧ M.mem (M.quad j.1 t a y) P ∧
      M.mem (M.op n y) F := by
    intro q
    rw [hN0 q]
    simp [Sat, M.sat_ex, M.sat_fTrip, M.sat_fApp4, M.sat_fApp, Function.update_apply]
  have hN : ∀ t n a, M.mem (M.trip t n a) Nt ↔ ∃ y, M.mem (M.quad j.1 t a y) P ∧
      M.mem (M.op n y) F := by
    intro t n a
    constructor
    · intro h
      obtain ⟨t', n', a', y, e, h1, h2⟩ := (hN1 _).mp h
      obtain ⟨e1, e2, e3⟩ := M.trip_inj e
      rw [e1, e2, e3]
      exact ⟨y, h1, h2⟩
    · rintro ⟨y, h1, h2⟩
      exact (hN1 _).mpr ⟨t, n, a, y, rfl, h1, h2⟩
  have numOf : ∀ {n y : V}, M.mem (M.op n y) F → ∃ x : M.Num, x.1 = n := by
    intro n y h
    obtain ⟨x, -, hx, -, -⟩ := M.mem_natLe.mp ((hF n y).mp h).1
    exact ⟨x, hx⟩
  refine ⟨Nt, fun t n a h => ?_, fun t a => ⟨fun h => ?_, ?_⟩, fun n t b => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨y, hq, hy⟩ := (hN t n a).mp h
    obtain ⟨x, hx⟩ := numOf hy
    rw [← hx]
    exact ⟨x.2, (hP.dom _ _ _ _ hq).2.1, (hP.dom _ _ _ _ hq).2.2.1⟩
  · obtain ⟨y, hq, hy⟩ := (hN t M.zero a).mp h
    obtain ⟨-, t1, a1, a', t', q1, q2, hcase⟩ := (hF M.zero y).mp hy
    obtain ⟨e1, e2⟩ := hP.inj _ _ _ _ _ _ q1 hq
    rw [e1] at q2
    rcases hcase with ⟨-, e⟩ | ⟨k, y', e0, -, hk⟩
    · rw [← e, e2] at q2
      exact ⟨t', q2⟩
    · exfalso
      obtain ⟨x, -, hx, -, -⟩ := M.mem_natLe.mp (M.mem_restr.mp hk).2.1
      rw [← hx, ← M.val_add_one x] at e0
      exact M.peano.1 x (Subtype.ext e0.symm)
  · rintro ⟨t', hq⟩
    obtain ⟨-, ha, -, ht⟩ := hP.dom _ _ _ _ hq
    obtain ⟨y, hy⟩ := hP.tot j hj t a ht ha
    exact (hN t M.zero a).mpr ⟨y, hy, (hF M.zero y).mpr
      ⟨(M.natLe_iff 0 0).mpr (le_refl 0), t, a, a, t', hy, hq, Or.inl ⟨rfl, rfl⟩⟩⟩
  · obtain ⟨y, hq, hy⟩ := (hN t (n + 1).1 b).mp h
    obtain ⟨-, t1, b1, a', t', q1, q2, hcase⟩ := (hF (n + 1).1 y).mp hy
    obtain ⟨e1, e2⟩ := hP.inj _ _ _ _ _ _ q1 hq
    rw [e1] at q2
    rcases hcase with ⟨e, -⟩ | ⟨k, y', e0, q3, hk⟩
    · exact absurd (Subtype.ext e : n + 1 = 0) (M.peano.1 n)
    · obtain ⟨hkF, hkle, -⟩ := M.mem_restr.mp hk
      obtain ⟨x, -, hx, -, -⟩ := M.mem_natLe.mp hkle
      rw [← hx, ← M.val_add_one x] at e0
      have e3 : n = x := M.peano.2.1 n x (Subtype.ext e0)
      rw [e2] at q3
      rw [← hx, ← e3] at hkF
      exact ⟨a', t', q2, (hN t' n.1 b).mpr ⟨y', q3, hkF⟩⟩
  · rintro ⟨a, t', hq, hN'⟩
    obtain ⟨y', q3, hy'⟩ := (hN t' n.1 b).mp hN'
    obtain ⟨-, -, -, ht⟩ := hP.dom _ _ _ _ hq
    obtain ⟨-, -, hb, -⟩ := hP.dom _ _ _ _ q3
    obtain ⟨y, hy⟩ := hP.tot j hj t b ht hb
    exact (hN t (n + 1).1 b).mpr ⟨y, hy, (hF (n + 1).1 y).mpr
      ⟨(M.natLe_iff (n + 1) (n + 1)).mpr (le_refl _), t, b, a, t', hy, hq,
        Or.inr ⟨n.1, y', M.val_add_one n, q3, M.mem_restr.mpr
          ⟨hy', (M.natLe_iff n (n + 1)).mpr (M.le_add_one n), M.val_ne_of_lt (le_refl _)⟩⟩⟩⟩

/-- The entries of a sequence are unique. -/
theorem nth_fun {R P Nt : V} {m j : M.Num} (hP : M.IsPairing R P m)
    (h0 : ∀ t a, M.mem (M.trip t M.zero a) Nt ↔ ∃ t', M.mem (M.quad j.1 a t' t) P)
    (hs : ∀ (n : M.Num) (t b : V), M.mem (M.trip t (n + 1).1 b) Nt ↔
      ∃ a t', M.mem (M.quad j.1 a t' t) P ∧ M.mem (M.trip t' n.1 b) Nt) (n : M.Num) :
    ∀ t a a', M.mem (M.trip t n.1 a) Nt → M.mem (M.trip t n.1 a') Nt → a = a' := by
  have hsat : ∀ k : V, Sat M.mem M.isSet
      (.all 8 (.all 9 (.all 10 (Fml.imp (fApp3 1 8 0 9) (Fml.imp (fApp3 1 8 0 10) (.eq 9 10))))))
      (Function.update (Function.update (fun _ => dflt) 1 Nt) 0 k) ↔
      ∀ t a a', M.mem (M.trip t k a) Nt → M.mem (M.trip t k a') Nt → a = a' := by
    intro k
    simp [Sat, M.sat_imp, M.sat_fApp3, Function.update_apply]
  rw [← hsat n.1]
  refine M.num_ind_fml (σW [(1, 7)]) _ 0 rfl _ ?_ (fun k ih => ?_) n
  · rw [hsat]
    intro t a a' h1 h2
    obtain ⟨t1, q1⟩ := (h0 t a).mp h1
    obtain ⟨t2, q2⟩ := (h0 t a').mp h2
    exact (hP.inj _ _ _ _ _ _ q1 q2).1
  · rw [hsat] at ih
    rw [hsat, ← M.val_add_one k]
    intro t b b' h1 h2
    obtain ⟨a1, t1, q1, k1⟩ := (hs k t b).mp h1
    obtain ⟨a2, t2, q2, k2⟩ := (hs k t b').mp h2
    rw [← (hP.inj _ _ _ _ _ _ q1 q2).2] at k2
    exact ih t1 b b' k1 k2

theorem lt_raw_iff (k n : M.Num) :
    (∃ s, s = M.succ k.1 ∧ M.LeRaw M.adG s n.1) ↔ k + 1 ≤ n := by
  constructor
  · rintro ⟨s, hs, h⟩
    rw [hs, ← M.val_add_one] at h
    exact (M.leRaw_iff M.adG_spec (k + 1) n).mp h
  · intro h
    refine ⟨_, rfl, ?_⟩
    rw [← M.val_add_one]
    exact (M.leRaw_iff M.adG_spec (k + 1) n).mpr h

/-- "Every `g` that has a value in rung `j` (name `3`) at each `k < n` is coded up to `n` by a
member of the rung"; `n`, `R`, `Nt` are the names `0`, `1`, `2`. -/
def seqCodeFml : Fml :=
  .all 5 (Fml.imp (.all 8 (Fml.imp (.mem 8 6) (Fml.imp (Fml.ex 13 (.and (fSuccEq 13 8) (fLe 13 0)))
      (Fml.ex 9 (.and (fApp 1 3 9) (fApp 5 8 9))))))
    (Fml.ex 10 (.and (fApp 1 3 10) (.all 8 (Fml.imp (.mem 8 6) (Fml.imp
      (Fml.ex 13 (.and (fSuccEq 13 8) (fLe 13 0)))
      (Fml.ex 9 (.and (fApp 5 8 9) (fApp3 2 10 8 9)))))))))

/-- **Every finite sequence of members of a rung is coded by a member of the rung.** If the
set `g` has a value in rung `j` at every `k < n`, then some member `t` of the rung has, for
every `k < n`, a value of `g` at `k` as its entry `k`. Here `n` is a number of the model. -/
theorem seq_code {R P Nt : V} {m j : M.Num} (hP : M.IsPairing R P m) (hj : j ≤ m)
    (hne : ∃ a, M.mem (M.op j.1 a) R)
    (h0 : ∀ t a, M.mem (M.trip t M.zero a) Nt ↔ ∃ t', M.mem (M.quad j.1 a t' t) P)
    (hs : ∀ (n : M.Num) (t b : V), M.mem (M.trip t (n + 1).1 b) Nt ↔
      ∃ a t', M.mem (M.quad j.1 a t' t) P ∧ M.mem (M.trip t' n.1 b) Nt) (n : M.Num) (g : V)
    (hg : ∀ k : M.Num, k + 1 ≤ n → ∃ a, M.mem (M.op j.1 a) R ∧ M.mem (M.op k.1 a) g) :
    ∃ t, M.mem (M.op j.1 t) R ∧ ∀ k : M.Num, k + 1 ≤ n →
      ∃ a, M.mem (M.op k.1 a) g ∧ M.mem (M.trip t k.1 a) Nt := by
  have hsat : ∀ n : M.Num, Sat M.mem M.isSet seqCodeFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 1 R)
      2 Nt) 3 j.1) 6 M.nat) 7 M.adG) 0 n.1) ↔
      ∀ g, (∀ k : M.Num, k + 1 ≤ n → ∃ a, M.mem (M.op j.1 a) R ∧ M.mem (M.op k.1 a) g) →
        ∃ t, M.mem (M.op j.1 t) R ∧ ∀ k : M.Num, k + 1 ≤ n →
          ∃ a, M.mem (M.op k.1 a) g ∧ M.mem (M.trip t k.1 a) Nt := by
    intro n
    have h1 : Sat M.mem M.isSet seqCodeFml (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 1 R)
        2 Nt) 3 j.1) 6 M.nat) 7 M.adG) 0 n.1) ↔
        ∀ g, (∀ k, M.mem k M.nat → (∃ s, s = M.succ k ∧ M.LeRaw M.adG s n.1) →
            ∃ a, M.mem (M.op j.1 a) R ∧ M.mem (M.op k a) g) →
          ∃ t, M.mem (M.op j.1 t) R ∧ ∀ k, M.mem k M.nat →
            (∃ s, s = M.succ k ∧ M.LeRaw M.adG s n.1) →
            ∃ a, M.mem (M.op k a) g ∧ M.mem (M.trip t k a) Nt := by
      simp [seqCodeFml, fLe, LeRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fApp, M.sat_fApp3,
        M.sat_fSuccEq, Function.update_apply]
    rw [h1]
    refine forall_congr' fun g => ⟨fun h hyp => ?_, fun h hyp => ?_⟩
    · obtain ⟨t, ht, hcon⟩ := h (fun k hk hlt => hyp ⟨k, hk⟩ ((M.lt_raw_iff ⟨k, hk⟩ n).mp hlt))
      exact ⟨t, ht, fun k hk => hcon k.1 k.2 ((M.lt_raw_iff k n).mpr hk)⟩
    · obtain ⟨t, ht, hcon⟩ := h (fun k hk => hyp k.1 k.2 ((M.lt_raw_iff k n).mpr hk))
      exact ⟨t, ht, fun k hk hlt => hcon ⟨k, hk⟩ ((M.lt_raw_iff ⟨k, hk⟩ n).mp hlt)⟩
  have key := M.num_ind_fml (σW [(1, 5), (2, 7), (5, 5), (6, 3), (7, 7)]) seqCodeFml 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (fun _ => dflt) 1 R) 2 Nt) 3 j.1) 6 M.nat) 7 M.adG)
    (by
      rw [show M.zero = (0 : M.Num).1 from rfl, hsat 0]
      intro g _
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, ha, fun k hk => absurd hk (fun h => M.succ_not_le_zero h)⟩)
    (fun n ih => by
      rw [hsat n] at ih
      rw [show M.succ n.1 = (n + 1).1 from (M.val_add_one n).symm, hsat (n + 1)]
      intro g hyp
      -- the sequence shifted by one
      obtain ⟨g', -, hg0⟩ := M.comp (σW [(0, 4), (1, 5)])
        (Fml.ex 8 (Fml.ex 9 (Fml.ex 13 (.and (fPr 0 8 9) (.and (fSuccEq 13 8) (fApp 1 13 9))))))
        0 rfl (Function.update (fun _ => dflt) 1 g)
      have hg1 : ∀ p, M.mem p g' ↔ ∃ k a, p = M.op k a ∧ M.mem (M.op (M.succ k) a) g := by
        intro p
        rw [hg0 p]
        simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp, M.sat_fSuccEq, Function.update_apply]
      have hg' : ∀ k a, M.mem (M.op k a) g' ↔ M.mem (M.op (M.succ k) a) g := by
        intro k a
        constructor
        · intro h
          obtain ⟨k', a', e, h'⟩ := (hg1 _).mp h
          obtain ⟨e1, e2⟩ := M.op_inj e
          rw [e1, e2]
          exact h'
        · intro h
          exact (hg1 _).mpr ⟨k, a, rfl, h⟩
      obtain ⟨t', ht', hcon⟩ := ih g' (fun k hk => by
        obtain ⟨a, ha, hka⟩ := hyp (k + 1) (add_le_add hk (le_refl 1))
        rw [M.val_add_one] at hka
        exact ⟨a, ha, (hg' k.1 a).mpr hka⟩)
      obtain ⟨a0, ha0, h0a⟩ := hyp 0 (add_le_add (zero_le : (0 : M.Num) ≤ n) (le_refl 1))
      obtain ⟨t, ht⟩ := hP.tot j hj a0 t' ha0 ht'
      refine ⟨t, (hP.dom _ _ _ _ ht).2.2.2, fun k hk => ?_⟩
      rcases M.num_cases k with e | ⟨k', e⟩
      · rw [e]
        exact ⟨a0, h0a, (h0 t a0).mpr ⟨t', ht⟩⟩
      · rw [e, M.nsucc_eq_add_one] at hk ⊢
        obtain ⟨a, hka, hnt⟩ := hcon k' (M.le_of_succ_le_succ hk)
        refine ⟨a, ?_, (hs k' t a).mpr ⟨a0, t', ht, hnt⟩⟩
        rw [M.val_add_one]
        exact (hg' k'.1 a).mp hka) n
  exact (hsat n).mp key g hg

/-! ## Numerals on a rung, and macros with more names (§3.3, step 3, preparations) -/

theorem sat_fPr' {p a b : ℕ} (ρ : ℕ → V) (hp : p < 30 ∨ 59 < p) (ha : a < 30 ∨ 59 < a)
    (hb : b < 30 ∨ 59 < b) :
    Sat M.mem M.isSet (fPr p a b) ρ ↔ ρ p = M.op (ρ a) (ρ b) :=
  M.sat_fOp (by omega) (by omega) (by omega) (by omega) (by omega) (by decide) ρ

theorem sat_fApp' {g a b : ℕ} (ρ : ℕ → V) (hg : g < 30 ∨ 59 < g) (ha : a < 30 ∨ 59 < a)
    (hb : b < 30 ∨ 59 < b) :
    Sat M.mem M.isSet (fApp g a b) ρ ↔ M.mem (M.op (ρ a) (ρ b)) (ρ g) := by
  have h1 : g ≠ 38 := by omega
  have h2 : a ≠ 38 := by omega
  have h3 : b ≠ 38 := by omega
  simp only [fApp, M.sat_ex, Sat,
    M.sat_fOp (p := 38) (a := a) (b := b) (u := 36) (c := 37) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

theorem sat_fTrip' {a b c : ℕ} (ρ : ℕ → V) (ha : a < 30 ∨ 59 < a) (hb : b < 30 ∨ 59 < b)
    (hc : c < 30 ∨ 59 < c) :
    Sat M.mem M.isSet (fTrip 39 a b c) ρ ↔ ρ 39 = M.trip (ρ a) (ρ b) (ρ c) := by
  have a32 : a ≠ 32 := by omega
  have a33 : a ≠ 33 := by omega
  have b32 : b ≠ 32 := by omega
  have b33 : b ≠ 33 := by omega
  have c32 : c ≠ 32 := by omega
  have c33 : c ≠ 33 := by omega
  simp only [fTrip, M.sat_ex, Sat,
    M.sat_fOp (p := 39) (a := 32) (b := 33) (u := 34) (c := 35) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    M.sat_fOp (p := 32) (a := a) (b := b) (u := 36) (c := 37) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    M.sat_fOp (p := 33) (a := c) (b := c) (u := 36) (c := 37) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    Function.update_self, Function.update_of_ne (show (39 : ℕ) ≠ 32 by decide),
    Function.update_of_ne (show (39 : ℕ) ≠ 33 by decide),
    Function.update_of_ne a32, Function.update_of_ne a33, Function.update_of_ne b32,
    Function.update_of_ne b33, Function.update_of_ne c32, Function.update_of_ne c33,
    Function.update_of_ne (show (32 : ℕ) ≠ 33 by decide)]
  unfold trip
  constructor
  · rintro ⟨p1, p2, h1, rfl, rfl⟩
    exact h1
  · intro h
    exact ⟨_, _, h, rfl, rfl⟩

theorem sat_fApp3' {G a b c : ℕ} (ρ : ℕ → V) (hG : G < 30 ∨ 59 < G) (ha : a < 30 ∨ 59 < a)
    (hb : b < 30 ∨ 59 < b) (hc : c < 30 ∨ 59 < c) :
    Sat M.mem M.isSet (fApp3 G a b c) ρ ↔ M.mem (M.trip (ρ a) (ρ b) (ρ c)) (ρ G) := by
  have h1 : G ≠ 39 := by omega
  have h2 : a ≠ 39 := by omega
  have h3 : b ≠ 39 := by omega
  have h4 : c ≠ 39 := by omega
  simp only [fApp3, M.sat_ex, Sat,
    fun ρ' : ℕ → V => M.sat_fTrip' (a := a) (b := b) (c := c) ρ' ha hb hc,
    Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

theorem sat_fQuad' {i a b c : ℕ} (ρ : ℕ → V) (hi : i < 30 ∨ 59 < i) (ha : a < 30 ∨ 59 < a)
    (hb : b < 30 ∨ 59 < b) (hc : c < 30 ∨ 59 < c) :
    Sat M.mem M.isSet (fQuad 39 i a b c) ρ ↔ ρ 39 = M.quad (ρ i) (ρ a) (ρ b) (ρ c) := by
  have i32 : i ≠ 32 := by omega
  have i33 : i ≠ 33 := by omega
  have a32 : a ≠ 32 := by omega
  have a33 : a ≠ 33 := by omega
  have b32 : b ≠ 32 := by omega
  have b33 : b ≠ 33 := by omega
  have c32 : c ≠ 32 := by omega
  have c33 : c ≠ 33 := by omega
  simp only [fQuad, M.sat_ex, Sat,
    M.sat_fOp (p := 39) (a := 32) (b := 33) (u := 34) (c := 35) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    M.sat_fOp (p := 32) (a := i) (b := a) (u := 36) (c := 37) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    M.sat_fOp (p := 33) (a := b) (b := c) (u := 36) (c := 37) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    Function.update_self, Function.update_of_ne (show (39 : ℕ) ≠ 32 by decide),
    Function.update_of_ne (show (39 : ℕ) ≠ 33 by decide),
    Function.update_of_ne i32, Function.update_of_ne i33,
    Function.update_of_ne a32, Function.update_of_ne a33, Function.update_of_ne b32,
    Function.update_of_ne b33, Function.update_of_ne c32, Function.update_of_ne c33,
    Function.update_of_ne (show (32 : ℕ) ≠ 33 by decide)]
  unfold quad
  constructor
  · rintro ⟨p1, p2, h1, rfl, rfl⟩
    exact h1
  · intro h
    exact ⟨_, _, h, rfl, rfl⟩

theorem sat_fApp4' {G i a b c : ℕ} (ρ : ℕ → V) (hG : G < 30 ∨ 59 < G) (hi : i < 30 ∨ 59 < i)
    (ha : a < 30 ∨ 59 < a) (hb : b < 30 ∨ 59 < b) (hc : c < 30 ∨ 59 < c) :
    Sat M.mem M.isSet (fApp4 G i a b c) ρ ↔ M.mem (M.quad (ρ i) (ρ a) (ρ b) (ρ c)) (ρ G) := by
  have h1 : G ≠ 39 := by omega
  have h2 : i ≠ 39 := by omega
  have h3 : a ≠ 39 := by omega
  have h4 : b ≠ 39 := by omega
  have h5 : c ≠ 39 := by omega
  simp only [fApp4, M.sat_ex, Sat,
    fun ρ' : ℕ → V => M.sat_fQuad' (i := i) (a := a) (b := b) (c := c) ρ' hi ha hb hc,
    Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

/-- **Numerals on a rung.** With the pairing of rung `j` and two different members `u`, `v`,
there is a set `ι` of pairs that is an injection of the natural numbers into the rung:
`0 ↦ (u, u)` and `n + 1 ↦ (v, ι n)`. -/
theorem exists_numerals {R P : V} {m j : M.Num} (hP : M.IsPairing R P m) (hj : j ≤ m)
    {u v : V} (hu : M.mem (M.op j.1 u) R) (hv : M.mem (M.op j.1 v) R) (huv : u ≠ v) :
    ∃ io, (∀ k a, M.mem (M.op k a) io → M.mem k M.nat ∧ M.mem (M.op j.1 a) R) ∧
      (∀ n : M.Num, ∃ a, M.mem (M.op n.1 a) io) ∧
      (∀ k a a', M.mem (M.op k a) io → M.mem (M.op k a') io → a = a') ∧
      (∀ k k' a, M.mem (M.op k a) io → M.mem (M.op k' a) io → k = k') ∧
      ∀ k a, M.mem (M.op k a) io →
        M.mem (M.quad j.1 u u a) P ∨ ∃ x, M.mem (M.quad j.1 v x a) P := by
  obtain ⟨D, -, hD⟩ := M.rung_set R j.1
  obtain ⟨c0, hc0⟩ := hP.tot j hj u u hu hu
  obtain ⟨G, -, hG0⟩ := M.comp (σW [(0, 4), (3, 7)])
    (Fml.ex 8 (Fml.ex 9 (.and (fPr 0 8 9) (fApp4 3 5 6 8 9)))) 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 3 P) 5 j.1) 6 v)
  have hG1 : ∀ p, M.mem p G ↔ ∃ x y, p = M.op x y ∧ M.mem (M.quad j.1 v x y) P := by
    intro p
    rw [hG0 p]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp4, Function.update_apply]
  have hG : ∀ x y, M.mem (M.op x y) G ↔ M.mem (M.quad j.1 v x y) P := by
    intro x y
    constructor
    · intro h
      obtain ⟨x', y', e, h'⟩ := (hG1 _).mp h
      obtain ⟨e1, e2⟩ := M.op_inj e
      rw [e1, e2]
      exact h'
    · intro h
      exact (hG1 _).mpr ⟨x, y, rfl, h⟩
  have hfun : M.FunOn G D := by
    intro x hx
    obtain ⟨y, hy⟩ := hP.tot j hj v x hv ((hD x).mp hx)
    exact ⟨y, (hD y).mpr (hP.dom _ _ _ _ hy).2.2.2, (hG x y).mpr hy,
      fun y' hy' => hP.fn _ _ _ _ _ ((hG x y').mp hy') hy⟩
  obtain ⟨f, hf1, hf0, hfs⟩ := M.exists_rec_set ((hD c0).mpr (hP.dom _ _ _ _ hc0).2.2.2) hfun
  -- the value at a successor
  have hsucc : ∀ (n : M.Num) (a : V), M.mem (M.op (n + 1).1 a) f →
      ∃ x, M.mem (M.op n.1 x) f ∧ M.mem (M.quad j.1 v x a) P := by
    intro n a ha
    obtain ⟨x, hxD, hx, -⟩ := hf1 n
    obtain ⟨y, -, hxy, -⟩ := hfun x hxD
    have h1 := hfs n x y hx hxy
    rw [← M.val_add_one] at h1
    obtain ⟨a0, -, -, huniq⟩ := hf1 (n + 1)
    rw [huniq a ha, ← huniq y h1]
    exact ⟨x, hx, (hG x y).mp hxy⟩
  have hzero : ∀ a, M.mem (M.op M.zero a) f → a = c0 := by
    intro a ha
    obtain ⟨a0, -, -, huniq⟩ := hf1 0
    rw [huniq a ha, ← huniq c0 hf0]
  -- injectivity, by induction
  have hinj : ∀ n : M.Num, ∀ n' a, M.mem n' M.nat → M.mem (M.op n.1 a) f →
      M.mem (M.op n' a) f → n.1 = n' := by
    intro n
    rw [← M.sat_baseInjFml f n.1]
    refine M.num_ind_fml (σW [(1, 5), (2, 3)]) baseInjFml 0 rfl _ ?_ (fun k ih => ?_) n
    · rw [M.sat_baseInjFml]
      intro n' a hn' h1 h2
      rcases M.num_cases ⟨n', hn'⟩ with e | ⟨k, e⟩
      · exact (congrArg Subtype.val e).symm
      · exfalso
        have e' : n' = (k + 1).1 := by
          rw [← M.nsucc_eq_add_one]
          exact congrArg Subtype.val e
        rw [e'] at h2
        obtain ⟨x, -, hq⟩ := hsucc k a h2
        rw [hzero a h1] at hq
        exact huv (hP.inj _ _ _ _ _ _ hc0 hq).1
    · rw [M.sat_baseInjFml] at ih ⊢
      intro n' a hn' h1 h2
      rw [← M.val_add_one] at h1
      obtain ⟨x, hx, hq⟩ := hsucc k a h1
      rcases M.num_cases ⟨n', hn'⟩ with e | ⟨k', e⟩
      · exfalso
        have e' : n' = M.zero := congrArg Subtype.val e
        rw [e'] at h2
        rw [hzero a h2] at hq
        exact huv (hP.inj _ _ _ _ _ _ hc0 hq).1
      · have e' : n' = (k' + 1).1 := by
          rw [← M.nsucc_eq_add_one]
          exact congrArg Subtype.val e
        rw [e'] at h2 ⊢
        obtain ⟨x', hx', hq'⟩ := hsucc k' a h2
        rw [(hP.inj _ _ _ _ _ _ hq hq').2] at hx
        have e2 : k = k' := Subtype.ext (ih k'.1 x' k'.2 hx hx')
        rw [← M.val_add_one, e2]
  -- restrict to numbers
  obtain ⟨io, -, hio0⟩ := M.comp (σW [(0, 4), (1, 5), (2, 3)])
    (Fml.ex 8 (Fml.ex 9 (.and (fPr 0 8 9) (.and (.mem 8 2) (fApp 1 8 9))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 f) 2 M.nat)
  have hio1 : ∀ p, M.mem p io ↔ ∃ k a, p = M.op k a ∧ M.mem k M.nat ∧ M.mem (M.op k a) f := by
    intro p
    rw [hio0 p]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp, Function.update_apply]
  have hio : ∀ k a, M.mem (M.op k a) io ↔ M.mem k M.nat ∧ M.mem (M.op k a) f := by
    intro k a
    constructor
    · intro h
      obtain ⟨k', a', e, h1, h2⟩ := (hio1 _).mp h
      obtain ⟨e1, e2⟩ := M.op_inj e
      rw [e1, e2]
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact (hio1 _).mpr ⟨k, a, rfl, h1, h2⟩
  refine ⟨io, fun k a h => ?_, fun n => ?_, fun k a a' h h' => ?_, fun k k' a h h' => ?_,
    fun k a h => ?_⟩
  · obtain ⟨hk, hka⟩ := (hio k a).mp h
    obtain ⟨a0, ha0D, -, huniq⟩ := hf1 ⟨k, hk⟩
    rw [huniq a hka]
    exact ⟨hk, (hD a0).mp ha0D⟩
  · obtain ⟨a, -, ha, -⟩ := hf1 n
    exact ⟨a, (hio n.1 a).mpr ⟨n.2, ha⟩⟩
  · obtain ⟨hk, hka⟩ := (hio k a).mp h
    obtain ⟨-, hka'⟩ := (hio k a').mp h'
    obtain ⟨a0, -, -, huniq⟩ := hf1 ⟨k, hk⟩
    rw [huniq a hka, huniq a' hka']
  · obtain ⟨hk, hka⟩ := (hio k a).mp h
    obtain ⟨hk', hka'⟩ := (hio k' a).mp h'
    exact hinj ⟨k, hk⟩ k' a hk' hka hka'
  · obtain ⟨hk, hka⟩ := (hio k a).mp h
    rcases M.num_cases ⟨k, hk⟩ with e | ⟨k', e⟩
    · have e' : k = M.zero := congrArg Subtype.val e
      rw [e'] at hka
      rw [hzero a hka]
      exact Or.inl hc0
    · have e' : k = (k' + 1).1 := by
        rw [← M.nsucc_eq_add_one]
        exact congrArg Subtype.val e
      rw [e'] at hka
      obtain ⟨x, -, hq⟩ := hsucc k' a hka
      exact Or.inr ⟨x, hq⟩


/-! ### A well-ordering with a new top point -/

theorem exists_addTop (w tp : V) : ∃ w', ∀ a a', M.mem (M.op a a') w' ↔
    M.mem (M.op a a') w ∨ (a' = tp ∧ (M.mem (M.op a a) w ∨ a = tp)) := by
  obtain ⟨w', -, h0⟩ := M.comp (σW [(0, 4), (1, 5)])
    (Fml.ex 8 (Fml.ex 9 (.and (fPr 0 8 9) (Fml.or (fApp 1 8 9)
      (.and (.eq 9 2) (Fml.or (fApp 1 8 8) (.eq 8 2))))))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 w) 2 tp)
  have h1 : ∀ t, M.mem t w' ↔ ∃ a a', t = M.op a a' ∧
      (M.mem (M.op a a') w ∨ (a' = tp ∧ (M.mem (M.op a a) w ∨ a = tp))) := by
    intro t
    rw [h0 t]
    simp [Sat, M.sat_ex, M.sat_or, M.sat_fPr, M.sat_fApp, Function.update_apply]
  refine ⟨w', fun a a' => ⟨fun h => ?_, fun h => (h1 _).mpr ⟨a, a', rfl, h⟩⟩⟩
  obtain ⟨b, b', e, h'⟩ := (h1 _).mp h
  obtain ⟨e1, e2⟩ := M.op_inj e
  rw [e1, e2]
  exact h'

/-- A well-ordering with a new point put on top is a well-ordering. -/
theorem wo_addTop {w tp w' : V} (hw : M.IsWO w) (htp : ¬ M.mem (M.op tp tp) w)
    (hw' : ∀ a a', M.mem (M.op a a') w' ↔
      M.mem (M.op a a') w ∨ (a' = tp ∧ (M.mem (M.op a a) w ∨ a = tp))) : M.IsWO w' := by
  have noL : ∀ a, ¬ M.mem (M.op tp a) w := fun a h => htp (hw.fld tp a h).1
  have noR : ∀ a, ¬ M.mem (M.op a tp) w := fun a h => htp (hw.fld a tp h).2
  have top_top : M.mem (M.op tp tp) w' := (hw' tp tp).mpr (Or.inr ⟨rfl, Or.inr rfl⟩)
  refine ⟨fun a a' h => ?_, fun a b c h1 h2 => ?_, fun a b h1 h2 => ?_, fun X hX => ?_⟩
  · rcases (hw' a a').mp h with h | ⟨e, h | h⟩
    · exact ⟨(hw' a a).mpr (Or.inl (hw.fld a a' h).1), (hw' a' a').mpr (Or.inl (hw.fld a a' h).2)⟩
    · rw [e]
      exact ⟨(hw' a a).mpr (Or.inl h), top_top⟩
    · rw [e, h]
      exact ⟨top_top, top_top⟩
  · rcases (hw' a b).mp h1 with k1 | ⟨e1, k1⟩
    · rcases (hw' b c).mp h2 with k2 | ⟨e2, -⟩
      · exact (hw' a c).mpr (Or.inl (hw.trans a b c k1 k2))
      · exact (hw' a c).mpr (Or.inr ⟨e2, Or.inl (hw.fld a b k1).1⟩)
    · rcases (hw' b c).mp h2 with k2 | ⟨e2, -⟩
      · rw [e1] at k2
        exact absurd k2 (noL c)
      · exact (hw' a c).mpr (Or.inr ⟨e2, k1⟩)
  · rcases (hw' a b).mp h1 with k1 | ⟨e1, -⟩
    · rcases (hw' b a).mp h2 with k2 | ⟨e2, -⟩
      · exact hw.antisymm a b k1 k2
      · rw [e2] at k1
        exact absurd k1 (noL b)
    · rcases (hw' b a).mp h2 with k2 | ⟨e2, -⟩
      · rw [e1] at k2
        exact absurd k2 (noL a)
      · rw [e1, e2]
  · obtain ⟨a0, ha0X, ha0⟩ := hX
    by_cases hin : ∃ a, M.mem a X ∧ M.mem (M.op a a) w
    · obtain ⟨a1, ha1X, ha1, hmin⟩ := hw.least X hin
      refine ⟨a1, ha1X, (hw' a1 a1).mpr (Or.inl ha1), fun b hbX hb => ?_⟩
      rcases (hw' b b).mp hb with k | ⟨e, -⟩
      · exact (hw' a1 b).mpr (Or.inl (hmin b hbX k))
      · exact (hw' a1 b).mpr (Or.inr ⟨e, Or.inl ha1⟩)
    · have e0 : a0 = tp := by
        rcases (hw' a0 a0).mp ha0 with k | ⟨e, -⟩
        · exact absurd ⟨a0, ha0X, k⟩ hin
        · exact e
      refine ⟨a0, ha0X, ha0, fun b hbX hb => ?_⟩
      rcases (hw' b b).mp hb with k | ⟨e, -⟩
      · exact absurd ⟨b, hbX, k⟩ hin
      · rw [e0, e]
        exact top_top
/-! ## The constructible hierarchy along a well-ordering (§3.3, step 3)

Fix a rung `j` with its pairing `P`, entries of sequences `Nt` and numerals `io`, a set
well-ordering `th` of members of the rung, and a member `d` of the rung (a default value).

* A *name of rank `β`* is a member of the rung of the form `(β, (φ̂, u))`, with `β` a point of
  `th`, `φ̂` the numeral of a number `φ` (a formula), and `u` any member of the rung, read as the
  sequence of parameters.
* The *value* of the variable `i` under a member `t` of the rung, at stage `α`, is the entry
  `i` of `t` if that is a name of rank below `α`, and `d` otherwise.
* Truth is defined for all pairs (stage `α`, formula `c`) at once, by recursion along the
  lexicographic product of `th` and the natural numbers. The fact "`c` is true at stage `α`
  under `t`" is the pair `⟨(α, ĉ), t⟩`.

The clauses are those of Tarski for the structure of the names of rank below `α`. A name
`(β, (φ̂, u))` has as members the names `a` of rank below `β` such that `φ` is true at stage `β`
under the sequence `(a, u)`. Different names may denote the same set. The same recursion
records this, at a top point `(γ, tp)` added above the formulas of each stage: two names
denote the same set if every member of one denotes the same set as a member of the other.
The atomic formula `v ε w` means that some name denoting the same set as the value of `v` is a
member of the value of `w`. The language has no equality. -/

/-- `a` is a name of rank below `α`. -/
def InNRaw (P th io nat j α a : V) : Prop :=
  ∃ β f u q, M.mem (M.quad j β q a) P ∧ M.mem (M.quad j f u q) P ∧ M.mem (M.op β α) th ∧
    β ≠ α ∧ ∃ k, M.mem k nat ∧ M.mem (M.op k f) io

/-- `InNRaw`, with `α`, `a` the names `65`, `68`. Parameters throughout: `P` `20`, `th` `22`,
`Nt` `23`, `io` `24`, `j` `25`, `d` `26`, `ℕ` `27`, the graphs of `+`, `·` `28`, `29`, the
numbers `0`–`3` `10`–`13`. -/
def inNFml : Fml :=
  Fml.ex 60 (Fml.ex 61 (Fml.ex 62 (Fml.ex 63 (.and (fApp4 20 25 60 63 68)
    (.and (fApp4 20 25 61 62 63) (.and (fApp 22 60 65) (.and (.neg (.eq 60 65))
      (Fml.ex 64 (.and (.mem 64 27) (fApp 24 64 61))))))))))

theorem sat_inNFml (ρ : ℕ → V) : Sat M.mem M.isSet inNFml ρ ↔
    M.InNRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 25) (ρ 65) (ρ 68) := by
  simp [inNFml, InNRaw, Sat, M.sat_ex, M.sat_fApp4', M.sat_fApp', Function.update_apply]

/-- The value of the variable `i` under `t` at stage `α` is `a`. -/
def ValRaw (P th io nat Nt j d α t i a : V) : Prop :=
  (M.mem (M.trip t i a) Nt ∧ M.InNRaw P th io nat j α a) ∨
  ((¬ ∃ e, M.mem (M.trip t i e) Nt ∧ M.InNRaw P th io nat j α e) ∧ a = d)

/-- `ValRaw`, with `α`, `t`, `i`, `a` the names `65`, `66`, `67`, `68`. -/
def valFml : Fml :=
  Fml.or (.and (fApp3 23 66 67 68) inNFml)
    (.and (.neg (Fml.ex 68 (.and (fApp3 23 66 67 68) inNFml))) (.eq 68 26))

theorem sat_valFml (ρ : ℕ → V) : Sat M.mem M.isSet valFml ρ ↔
    M.ValRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 65) (ρ 66) (ρ 67) (ρ 68) := by
  simp [valFml, ValRaw, Sat, M.sat_or, M.sat_ex, M.sat_fApp3', M.sat_inNFml,
    Function.update_apply]

/-- `a ε b` as given by the earlier stages `G`: `b` is a name `(β, (f, u))`, `a` is a name of
rank below `β`, and the formula `f` is true at stage `β` under the sequence `(a, u)`. -/
def EpsRaw (P th io nat j G a b : V) : Prop :=
  ∃ β f u q s pt, M.mem (M.quad j β q b) P ∧ M.mem (M.quad j f u q) P ∧
    M.InNRaw P th io nat j β a ∧ M.mem (M.quad j a u s) P ∧ M.mem (M.quad j β f pt) P ∧
    M.mem (M.op pt s) G

/-- `EpsRaw`, with `G`, `a`, `b` the names `6`, `72`, `73`. -/
def epsFml : Fml :=
  Fml.ex 74 (Fml.ex 75 (Fml.ex 76 (Fml.ex 77 (Fml.ex 78 (Fml.ex 79 (.and (fApp4 20 25 74 77 73)
    (.and (fApp4 20 25 75 76 77)
    (.and (Fml.ex 65 (.and (.eq 65 74) (Fml.ex 68 (.and (.eq 68 72) inNFml))))
    (.and (fApp4 20 25 72 76 78) (.and (fApp4 20 25 74 75 79) (fApp 6 79 78)))))))))))

theorem sat_epsFml (ρ : ℕ → V) : Sat M.mem M.isSet epsFml ρ ↔
    M.EpsRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 25) (ρ 6) (ρ 72) (ρ 73) := by
  simp [epsFml, EpsRaw, Sat, M.sat_ex, M.sat_fApp4', M.sat_fApp', M.sat_inNFml,
    Function.update_apply]

/-- "`a` and `a'` denote the same set", as recorded in `G` at a top point `(γ, tp)`. -/
def SimRaw (P j tp G a a' : V) : Prop :=
  ∃ γ pg y, M.mem (M.quad j γ tp pg) P ∧ M.mem (M.quad j a a' y) P ∧ M.mem (M.op pg y) G

/-- `SimRaw`, with `tp`, `G`, `a`, `a'` the names `21`, `6`, `94`, `95`. -/
def simFml : Fml :=
  Fml.ex 96 (Fml.ex 97 (Fml.ex 98 (.and (fApp4 20 25 96 21 97) (.and (fApp4 20 25 94 95 98)
    (fApp 6 97 98)))))

theorem sat_simFml (ρ : ℕ → V) : Sat M.mem M.isSet simFml ρ ↔
    M.SimRaw (ρ 20) (ρ 25) (ρ 21) (ρ 6) (ρ 94) (ρ 95) := by
  simp [simFml, SimRaw, Sat, M.sat_ex, M.sat_fApp4', M.sat_fApp', Function.update_apply]

/-- Membership between the sets denoted: some name that denotes the same set as `a` is a
member of `b`. -/
def EpsStarRaw (P th io nat j tp G a b : V) : Prop :=
  ∃ a', M.SimRaw P j tp G a a' ∧ M.EpsRaw P th io nat j G a' b

/-- `EpsStarRaw`, with `a`, `b` the names `70`, `73`. -/
def epsStarFml : Fml :=
  Fml.ex 72 (.and (Fml.ex 94 (.and (.eq 94 70) (Fml.ex 95 (.and (.eq 95 72) simFml)))) epsFml)

theorem sat_epsStarFml (ρ : ℕ → V) : Sat M.mem M.isSet epsStarFml ρ ↔
    M.EpsStarRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 25) (ρ 21) (ρ 6) (ρ 70) (ρ 73) := by
  simp [epsStarFml, EpsStarRaw, Sat, M.sat_ex, M.sat_simFml, M.sat_epsFml,
    Function.update_apply]

/-- `a` is a name of rank `β`. -/
def RankIs (P io nat j β a : V) : Prop :=
  ∃ f u q, M.mem (M.quad j β q a) P ∧ M.mem (M.quad j f u q) P ∧
    ∃ k, M.mem k nat ∧ M.mem (M.op k f) io

/-- `RankIs`, with `β`, `a` the names `74`, `72`. -/
def rankFml : Fml :=
  Fml.ex 61 (Fml.ex 62 (Fml.ex 63 (.and (fApp4 20 25 74 63 72) (.and (fApp4 20 25 61 62 63)
    (Fml.ex 64 (.and (.mem 64 27) (fApp 24 64 61)))))))

theorem sat_rankFml (ρ : ℕ → V) : Sat M.mem M.isSet rankFml ρ ↔
    M.RankIs (ρ 20) (ρ 24) (ρ 27) (ρ 25) (ρ 74) (ρ 72) := by
  simp [rankFml, RankIs, Sat, M.sat_ex, M.sat_fApp4', M.sat_fApp', Function.update_apply]

/-- The clause at a top point `(α, tp)`: `y` is a pair `(a, a')` of names of ranks at most
`α`, one of them of rank `α`, such that every member of one has the same denotation as a
member of the other. -/
def SimStepRaw (P th io nat j tp G α y : V) : Prop :=
  ∃ a a' β β', M.mem (M.quad j a a' y) P ∧ M.RankIs P io nat j β a ∧ M.RankIs P io nat j β' a' ∧
    M.mem (M.op β α) th ∧ M.mem (M.op β' α) th ∧ (β = α ∨ β' = α) ∧
    (∀ x, M.EpsRaw P th io nat j G x a →
      ∃ x', M.EpsRaw P th io nat j G x' a' ∧ M.SimRaw P j tp G x x') ∧
    (∀ x', M.EpsRaw P th io nat j G x' a' →
      ∃ x, M.EpsRaw P th io nat j G x a ∧ M.SimRaw P j tp G x x')

/-- `SimStepRaw`, with `α`, `y` the names `65`, `5`. -/
def simStepFml : Fml :=
  Fml.ex 86 (Fml.ex 87 (Fml.ex 88 (Fml.ex 89 (.and (fApp4 20 25 86 87 5)
    (.and (Fml.ex 74 (.and (.eq 74 88) (Fml.ex 72 (.and (.eq 72 86) rankFml))))
    (.and (Fml.ex 74 (.and (.eq 74 89) (Fml.ex 72 (.and (.eq 72 87) rankFml))))
    (.and (fApp 22 88 65) (.and (fApp 22 89 65) (.and (Fml.or (.eq 88 65) (.eq 89 65))
    (.and (.all 90 (Fml.imp (Fml.ex 72 (.and (.eq 72 90) (Fml.ex 73 (.and (.eq 73 86) epsFml))))
        (Fml.ex 91 (.and (Fml.ex 72 (.and (.eq 72 91) (Fml.ex 73 (.and (.eq 73 87) epsFml))))
          (Fml.ex 94 (.and (.eq 94 90) (Fml.ex 95 (.and (.eq 95 91) simFml))))))))
      (.all 91 (Fml.imp (Fml.ex 72 (.and (.eq 72 91) (Fml.ex 73 (.and (.eq 73 87) epsFml))))
        (Fml.ex 90 (.and (Fml.ex 72 (.and (.eq 72 90) (Fml.ex 73 (.and (.eq 73 86) epsFml))))
          (Fml.ex 94 (.and (.eq 94 90) (Fml.ex 95 (.and (.eq 95 91) simFml))))))))))))))))))

theorem sat_simStepFml (ρ : ℕ → V) : Sat M.mem M.isSet simStepFml ρ ↔
    M.SimStepRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 25) (ρ 21) (ρ 6) (ρ 65) (ρ 5) := by
  simp [simStepFml, SimStepRaw, Sat, M.sat_imp, M.sat_or, M.sat_ex, M.sat_fApp4', M.sat_fApp',
    M.sat_rankFml, M.sat_epsFml, M.sat_simFml, Function.update_apply]

/-- `t'` has the values of `t` at the variables `i ≤ c`, except that its value at `v` is `a`. -/
def AgreeRaw (P th io nat Nt j d ad α t t' v a c : V) : Prop :=
  ∀ i, M.mem i nat → (∃ x, M.mem x nat ∧ M.mem (M.trip i x c) ad) → ∀ e,
    (M.ValRaw P th io nat Nt j d α t' i e ↔
      ((i = v ∧ e = a) ∨ (i ≠ v ∧ M.ValRaw P th io nat Nt j d α t i e)))

/-- `AgreeRaw`, with `α`, `t`, `t'`, `v`, `a`, `c` the names `65`, `5`, `80`, `81`, `82`,
`83`. -/
def agreeHFml : Fml :=
  .all 67 (Fml.imp (.mem 67 27) (Fml.imp (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 67 84 83)))
    (.all 68 (Fml.iff (Fml.ex 66 (.and (.eq 66 80) valFml))
      (Fml.or (.and (.eq 67 81) (.eq 68 82))
        (.and (.neg (.eq 67 81)) (Fml.ex 66 (.and (.eq 66 5) valFml))))))))

theorem sat_agreeHFml (ρ : ℕ → V) : Sat M.mem M.isSet agreeHFml ρ ↔
    M.AgreeRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 65) (ρ 5) (ρ 80)
      (ρ 81) (ρ 82) (ρ 83) := by
  simp [agreeHFml, AgreeRaw, Sat, M.sat_imp, M.sat_iff, M.sat_or, M.sat_ex, M.sat_fApp3',
    M.sat_valFml, Function.update_apply]

/-- `c` is the code of the pair of `x` and `y`; the graphs of `+`, `·` are the names `28`,
`29`. -/
def fPN (c x y : ℕ) : Fml :=
  Fml.ex 100 (Fml.ex 101 (.and (fApp3 28 x y 100) (.and (fApp3 29 100 100 101)
    (fApp3 28 101 x c))))

/-! ### The two built-in predicates

Besides `ε` the language of the hierarchy has two more relation symbols, whose meaning at a
stage `α` is given by the earlier stages.

* `T(a, b)` ("satisfaction below"): `a` denotes an ordered pair of the ordinal name of a stage
  `β` below `α` and the numeral of a number `c`; `b` denotes a set of ordered pairs which is a
  function on the numerals of the numbers `i ≤ c`; and `c` is true at stage `β` under a
  sequence whose value at each `i ≤ c` denotes the same set as the value of `b` at the numeral
  of `i`.
* `a <* b` (the canonical well-ordering): the least name, in a fixed order `Pr` of the names,
  that denotes the same set as `a` is strictly below the least one for `b`.

All quantifiers in these clauses are over the names of rank below `α`. -/

/-- `InNRaw` at the stage named `65`, for the name `x`. -/
def fInN (x : ℕ) : Fml := Fml.ex 68 (.and (.eq 68 x) inNFml)

theorem sat_fInN {x : ℕ} (ρ : ℕ → V) (hx : 199 < x) :
    Sat M.mem M.isSet (fInN x) ρ ↔
      M.InNRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 25) (ρ 65) (ρ x) := by
  have h1 : x ≠ 68 := by omega
  simp [fInN, Sat, M.sat_ex, M.sat_inNFml, Function.update_apply, h1]

/-- `SimRaw` for the names `x`, `y`. -/
def fSim (x y : ℕ) : Fml := Fml.ex 94 (.and (.eq 94 x) (Fml.ex 95 (.and (.eq 95 y) simFml)))

theorem sat_fSim {x y : ℕ} (ρ : ℕ → V) (hx : 199 < x) (hy : 199 < y) :
    Sat M.mem M.isSet (fSim x y) ρ ↔ M.SimRaw (ρ 20) (ρ 25) (ρ 21) (ρ 6) (ρ x) (ρ y) := by
  have h1 : x ≠ 94 := by omega
  have h2 : y ≠ 94 := by omega
  have h3 : y ≠ 95 := by omega
  simp [fSim, Sat, M.sat_ex, M.sat_simFml, Function.update_apply, h1, h2, h3]

/-- `EpsStarRaw` for the names `x`, `y`. -/
def fEpsS (x y : ℕ) : Fml :=
  Fml.ex 70 (.and (.eq 70 x) (Fml.ex 73 (.and (.eq 73 y) epsStarFml)))

theorem sat_fEpsS {x y : ℕ} (ρ : ℕ → V) (hx : 199 < x) (hy : 199 < y) :
    Sat M.mem M.isSet (fEpsS x y) ρ ↔
      M.EpsStarRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 25) (ρ 21) (ρ 6) (ρ x) (ρ y) := by
  have h1 : x ≠ 70 := by omega
  have h2 : y ≠ 70 := by omega
  have h3 : y ≠ 73 := by omega
  simp [fEpsS, Sat, M.sat_ex, M.sat_epsStarFml, Function.update_apply, h1, h2, h3]

/-- Among the names of rank below `α`, `p` denotes the pair of the sets denoted by `x`, `y`. -/
def IsPairAt (P th io nat j tp G α x y p : V) : Prop :=
  ∀ z, M.InNRaw P th io nat j α z →
    (M.EpsStarRaw P th io nat j tp G z p ↔ (M.SimRaw P j tp G z x ∨ M.SimRaw P j tp G z y))

def fIsPair (x y p : ℕ) : Fml :=
  .all 240 (Fml.imp (fInN 240) (Fml.iff (fEpsS 240 p) (Fml.or (fSim 240 x) (fSim 240 y))))

theorem sat_fIsPair {x y p : ℕ} (ρ : ℕ → V) (hx : 199 < x ∧ x ≠ 240) (hy : 199 < y ∧ y ≠ 240)
    (hp : 199 < p ∧ p ≠ 240) :
    Sat M.mem M.isSet (fIsPair x y p) ρ ↔
      M.IsPairAt (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 25) (ρ 21) (ρ 6) (ρ 65) (ρ x) (ρ y) (ρ p) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hp1, hp2⟩ := hp
  simp [fIsPair, IsPairAt, Sat, M.sat_imp, M.sat_iff, M.sat_or, M.sat_fInN, M.sat_fEpsS,
    M.sat_fSim, Function.update_apply, hx1, hx2, hy1, hy2, hp1, hp2]

/-- Among the names of rank below `α`, `p` denotes the ordered pair `{{x}, {x, y}}`. -/
def IsOPairAt (P th io nat j tp G α x y p : V) : Prop :=
  ∃ s q, M.InNRaw P th io nat j α s ∧ M.InNRaw P th io nat j α q ∧
    M.IsPairAt P th io nat j tp G α x x s ∧ M.IsPairAt P th io nat j tp G α x y q ∧
    M.IsPairAt P th io nat j tp G α s q p

def fIsOPair (x y p : ℕ) : Fml :=
  Fml.ex 241 (Fml.ex 242 (.and (fInN 241) (.and (fInN 242) (.and (fIsPair x x 241)
    (.and (fIsPair x y 242) (fIsPair 241 242 p))))))

theorem sat_fIsOPair {x y p : ℕ} (ρ : ℕ → V) (hx : 199 < x ∧ x < 240) (hy : 199 < y ∧ y < 240)
    (hp : 199 < p ∧ p < 240) :
    Sat M.mem M.isSet (fIsOPair x y p) ρ ↔
      M.IsOPairAt (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 25) (ρ 21) (ρ 6) (ρ 65) (ρ x) (ρ y) (ρ p) := by
  have hx1 : 199 < x ∧ x ≠ 240 := ⟨hx.1, by omega⟩
  have hy1 : 199 < y ∧ y ≠ 240 := ⟨hy.1, by omega⟩
  have hp1 : 199 < p ∧ p ≠ 240 := ⟨hp.1, by omega⟩
  have a1 : x ≠ 241 := by omega
  have a2 : x ≠ 242 := by omega
  have a3 : y ≠ 241 := by omega
  have a4 : y ≠ 242 := by omega
  have a5 : p ≠ 241 := by omega
  have a6 : p ≠ 242 := by omega
  simp [fIsOPair, IsOPairAt, Sat, M.sat_ex, M.sat_fInN, M.sat_fIsPair, Function.update_apply,
    hx1, hy1, hp1, a1, a2, a3, a4, a5, a6]

/-- `ValRaw` for the names `st`, `t`, `i`, `e`. -/
def fVal (st t i e : ℕ) : Fml :=
  Fml.ex 65 (.and (.eq 65 st) (Fml.ex 66 (.and (.eq 66 t) (Fml.ex 67 (.and (.eq 67 i)
    (Fml.ex 68 (.and (.eq 68 e) valFml)))))))

theorem sat_fVal {st t i e : ℕ} (ρ : ℕ → V) (hst : st < 30 ∨ 199 < st) (ht : 199 < t)
    (hi : 199 < i) (he : 199 < e) :
    Sat M.mem M.isSet (fVal st t i e) ρ ↔
      M.ValRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ st) (ρ t) (ρ i) (ρ e) := by
  have b1 : st ≠ 65 := by omega
  have b2 : t ≠ 65 := by omega
  have b3 : t ≠ 66 := by omega
  have b4 : i ≠ 65 := by omega
  have b5 : i ≠ 66 := by omega
  have b6 : i ≠ 67 := by omega
  have b7 : e ≠ 65 := by omega
  have b8 : e ≠ 66 := by omega
  have b9 : e ≠ 67 := by omega
  have b10 : e ≠ 68 := by omega
  simp [fVal, Sat, M.sat_ex, M.sat_valFml, Function.update_apply, b1, b2, b3, b4, b5, b6, b7,
    b8, b9, b10]

/-- `i ≤ c` for numbers named `i`, `c`. -/
def fLeN (i c : ℕ) : Fml := Fml.ex 84 (.and (.mem 84 27) (fApp3 28 i 84 c))

theorem sat_fLeN {i c : ℕ} (ρ : ℕ → V) (hi : 199 < i) (hc : 199 < c) :
    Sat M.mem M.isSet (fLeN i c) ρ ↔ ∃ x, M.mem x (ρ 27) ∧ M.mem (M.trip (ρ i) x (ρ c)) (ρ 28) := by
  have b1 : i ≠ 84 := by omega
  have b2 : c ≠ 84 := by omega
  have b3 : i < 30 ∨ 59 < i := by omega
  have b4 : c < 30 ∨ 59 < c := by omega
  simp [fLeN, Sat, M.sat_ex, M.sat_fApp3', Function.update_apply, b1, b2, b3, b4]

/-- The clause for `T` at stage `α`, for the names `a`, `b` of rank below `α`. -/
def TRaw (P th io nat Nt j d tp qo Nu ad G α a b : V) : Prop :=
  M.InNRaw P th io nat j α a ∧ M.InNRaw P th io nat j α b ∧
  ∃ β c ob oc t', M.mem (M.op β α) th ∧ β ≠ α ∧ M.mem (M.quad j β qo ob) P ∧ M.mem c nat ∧
    M.mem (M.op c oc) Nu ∧ M.InNRaw P th io nat j α ob ∧ M.InNRaw P th io nat j α oc ∧
    M.IsOPairAt P th io nat j tp G α ob oc a ∧
    (∀ i, M.mem i nat → (∃ x, M.mem x nat ∧ M.mem (M.trip i x c) ad) → ∀ oi y y' p p',
      M.mem (M.op i oi) Nu → M.InNRaw P th io nat j α oi → M.InNRaw P th io nat j α y →
      M.InNRaw P th io nat j α y' → M.InNRaw P th io nat j α p → M.InNRaw P th io nat j α p' →
      M.EpsStarRaw P th io nat j tp G p b → M.IsOPairAt P th io nat j tp G α oi y p →
      M.EpsStarRaw P th io nat j tp G p' b → M.IsOPairAt P th io nat j tp G α oi y' p' →
      M.SimRaw P j tp G y y') ∧
    (∀ i, M.mem i nat → (∃ x, M.mem x nat ∧ M.mem (M.trip i x c) ad) → ∃ oi y p e,
      M.mem (M.op i oi) Nu ∧ M.InNRaw P th io nat j α oi ∧ M.InNRaw P th io nat j α y ∧
      M.InNRaw P th io nat j α p ∧ M.EpsStarRaw P th io nat j tp G p b ∧
      M.IsOPairAt P th io nat j tp G α oi y p ∧ M.ValRaw P th io nat Nt j d β t' i e ∧
      M.SimRaw P j tp G y e) ∧
    ∃ ch pt, M.mem (M.op c ch) io ∧ M.mem (M.quad j β ch pt) P ∧ M.mem (M.op pt t') G

/-- `TRaw`, with `α`, `a`, `b` the names `65`, `200`, `201`; `qo`, `Nu` are `160`, `161`. -/
def tRawFml : Fml :=
  .and (fInN 200) (.and (fInN 201) (Fml.ex 202 (Fml.ex 203 (Fml.ex 204 (Fml.ex 205 (Fml.ex 206
    (.and (fApp 22 202 65) (.and (.neg (.eq 202 65)) (.and (fApp4 20 25 202 160 204) (.and (.mem
    203 27) (.and (fApp 161 203 205) (.and (fInN 204) (.and (fInN 205) (.and (fIsOPair 204 205
    200) (.and (.all 207 (Fml.imp (.mem 207 27) (Fml.imp (fLeN 207 203) (.all 208 (.all 209
    (.all 210 (.all 211 (.all 212 (Fml.imp (fApp 161 207 208) (Fml.imp (fInN 208) (Fml.imp (fInN
    209) (Fml.imp (fInN 210) (Fml.imp (fInN 211) (Fml.imp (fInN 212) (Fml.imp (fEpsS 211 201)
    (Fml.imp (fIsOPair 208 209 211) (Fml.imp (fEpsS 212 201) (Fml.imp (fIsOPair 208 210 212)
    (fSim 209 210))))))))))))))))))) (.and (.all 207 (Fml.imp (.mem 207 27) (Fml.imp (fLeN 207
    203) (Fml.ex 208 (Fml.ex 209 (Fml.ex 211 (Fml.ex 213 (.and (fApp 161 207 208) (.and (fInN
    208) (.and (fInN 209) (.and (fInN 211) (.and (fEpsS 211 201) (.and (fIsOPair 208 209 211)
    (.and (fVal 202 206 207 213) (fSim 209 213))))))))))))))) (Fml.ex 214 (Fml.ex 215 (.and
    (fApp 24 203 214) (.and (fApp4 20 25 202 214 215) (fApp 6 215 206)))))))))))))))))))))

theorem sat_tRawFml (ρ : ℕ → V) : Sat M.mem M.isSet tRawFml ρ ↔
    M.TRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 21) (ρ 160) (ρ 161) (ρ 28)
      (ρ 6) (ρ 65) (ρ 200) (ρ 201) := by
  simp [tRawFml, TRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fApp', M.sat_fApp4', M.sat_fInN,
    M.sat_fSim, M.sat_fEpsS, M.sat_fIsOPair, M.sat_fVal, M.sat_fLeN, Function.update_apply]

/-- The clause for `<*` at stage `α`, for the names `a`, `b` of rank below `α`. -/
def LtRaw (P th io nat j tp Pr G α a b : V) : Prop :=
  M.InNRaw P th io nat j α a ∧ M.InNRaw P th io nat j α b ∧
  ∃ a0 b0, M.InNRaw P th io nat j α a0 ∧ M.InNRaw P th io nat j α b0 ∧
    M.SimRaw P j tp G a a0 ∧ M.SimRaw P j tp G b b0 ∧
    (∀ a', M.InNRaw P th io nat j α a' → M.SimRaw P j tp G a' a0 → M.mem (M.op a0 a') Pr) ∧
    (∀ b', M.InNRaw P th io nat j α b' → M.SimRaw P j tp G b' b0 → M.mem (M.op b0 b') Pr) ∧
    M.mem (M.op a0 b0) Pr ∧ ¬ M.mem (M.op b0 a0) Pr

/-- `LtRaw`, with `α`, `a`, `b` the names `65`, `200`, `201`; `Pr` is `162`. -/
def ltRawFml : Fml :=
  .and (fInN 200) (.and (fInN 201) (Fml.ex 202 (Fml.ex 203 (.and (fInN 202) (.and (fInN 203)
    (.and (fSim 200 202) (.and (fSim 201 203) (.and (.all 204 (Fml.imp (fInN 204) (Fml.imp (fSim
    204 202) (fApp 162 202 204)))) (.and (.all 204 (Fml.imp (fInN 204) (Fml.imp (fSim 204 203)
    (fApp 162 203 204)))) (.and (fApp 162 202 203) (.neg (fApp 162 203 202))))))))))))

theorem sat_ltRawFml (ρ : ℕ → V) : Sat M.mem M.isSet ltRawFml ρ ↔
    M.LtRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 25) (ρ 21) (ρ 162) (ρ 6) (ρ 65) (ρ 200) (ρ 201) := by
  simp [ltRawFml, LtRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fApp', M.sat_fInN, M.sat_fSim,
    Function.update_apply]

/-- The meaning at stage `α` of the relation symbol `r` between the names `a`, `b`: `T` for
`r = 1`, `<*` for `r = 2`, and membership between the sets denoted otherwise. -/
def AtomAtRaw (P th io nat Nt j d tp qo Nu Pr ad z1 z2 G α r a b : V) : Prop :=
  (r ≠ z1 ∧ r ≠ z2 ∧ M.EpsStarRaw P th io nat j tp G a b) ∨
  (r = z1 ∧ M.TRaw P th io nat Nt j d tp qo Nu ad G α a b) ∨
  (r = z2 ∧ M.LtRaw P th io nat j tp Pr G α a b)

/-- `AtomAtRaw`, with `α`, `r`, `a`, `b` the names `65`, `86`, `70`, `73`. -/
def atomAtFml : Fml :=
  Fml.or (.and (.neg (.eq 86 11)) (.and (.neg (.eq 86 12)) epsStarFml))
    (Fml.or
      (.and (.eq 86 11) (Fml.ex 200 (.and (.eq 200 70) (Fml.ex 201 (.and (.eq 201 73) tRawFml)))))
      (.and (.eq 86 12) (Fml.ex 200 (.and (.eq 200 70) (Fml.ex 201 (.and (.eq 201 73) ltRawFml))))))

theorem sat_atomAtFml (ρ : ℕ → V) : Sat M.mem M.isSet atomAtFml ρ ↔
    M.AtomAtRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 21) (ρ 160) (ρ 161) (ρ 162)
      (ρ 28) (ρ 11) (ρ 12) (ρ 6) (ρ 65) (ρ 86) (ρ 70) (ρ 73) := by
  simp [atomAtFml, AtomAtRaw, Sat, M.sat_or, M.sat_ex, M.sat_epsStarFml, M.sat_tRawFml,
    M.sat_ltRawFml, Function.update_apply]

/-- The atomic clause: `c` is `(0, (r, (v, w)))` and the relation `r` holds at stage `α`
between the values of `v` and `w`. -/
def AtomRaw (P th io nat Nt j d tp qo Nu Pr ad mu z0 z1 z2 G α t c : V) : Prop :=
  ∃ r v w p1 p2, M.PairRaw ad mu z0 p1 c ∧ M.PairRaw ad mu r p2 p1 ∧ M.PairRaw ad mu v w p2 ∧
    ∃ a b, M.ValRaw P th io nat Nt j d α t v a ∧ M.ValRaw P th io nat Nt j d α t w b ∧
      M.AtomAtRaw P th io nat Nt j d tp qo Nu Pr ad z1 z2 G α r a b

def atomFml : Fml :=
  Fml.ex 86 (Fml.ex 87 (Fml.ex 88 (Fml.ex 89 (Fml.ex 90 (.and (fPN 83 10 89) (.and (fPN 89 86 90)
    (.and (fPN 90 87 88) (Fml.ex 66 (.and (.eq 66 5) (Fml.ex 70 (Fml.ex 73
      (.and (Fml.ex 67 (.and (.eq 67 87) (Fml.ex 68 (.and (.eq 68 70) valFml))))
      (.and (Fml.ex 67 (.and (.eq 67 88) (Fml.ex 68 (.and (.eq 68 73) valFml))))
        atomAtFml)))))))))))))

theorem sat_atomFml (ρ : ℕ → V) : Sat M.mem M.isSet atomFml ρ ↔
    M.AtomRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 21) (ρ 160) (ρ 161) (ρ 162)
      (ρ 28) (ρ 29) (ρ 10) (ρ 11) (ρ 12) (ρ 6) (ρ 65) (ρ 5) (ρ 83) := by
  simp [atomFml, AtomRaw, fPN, PairRaw, Sat, M.sat_ex, M.sat_fApp3', M.sat_valFml,
    M.sat_atomAtFml, Function.update_apply]

/-- The clause for negation: `c` is `(1, c')` and `c'` is not true. -/
def NegRaw (P io nat j ad mu z1 G α t c : V) : Prop :=
  ∃ c' ch' pt', M.PairRaw ad mu z1 c' c ∧ M.mem c' nat ∧ M.mem (M.op c' ch') io ∧
    M.mem (M.quad j α ch' pt') P ∧ ¬ M.mem (M.op pt' t) G

def negHFml : Fml :=
  Fml.ex 91 (Fml.ex 92 (Fml.ex 93 (.and (fPN 83 11 91) (.and (.mem 91 27) (.and (fApp 24 91 92)
    (.and (fApp4 20 25 65 92 93) (.neg (fApp 6 93 5))))))))

theorem sat_negHFml (ρ : ℕ → V) : Sat M.mem M.isSet negHFml ρ ↔
    M.NegRaw (ρ 20) (ρ 24) (ρ 27) (ρ 25) (ρ 28) (ρ 29) (ρ 11) (ρ 6) (ρ 65) (ρ 5) (ρ 83) := by
  simp [negHFml, NegRaw, fPN, PairRaw, Sat, M.sat_ex, M.sat_fApp3', M.sat_fApp4', M.sat_fApp',
    Function.update_apply]

/-- The clause for conjunction: `c` is `(2, (c', c''))` and both are true. -/
def AndRaw (P io nat j ad mu z2 G α t c : V) : Prop :=
  ∃ c' c'' p ch' ch'' pt' pt'', M.PairRaw ad mu z2 p c ∧ M.PairRaw ad mu c' c'' p ∧
    M.mem c' nat ∧ M.mem (M.op c' ch') io ∧ M.mem (M.quad j α ch' pt') P ∧
    M.mem c'' nat ∧ M.mem (M.op c'' ch'') io ∧ M.mem (M.quad j α ch'' pt'') P ∧
    M.mem (M.op pt' t) G ∧ M.mem (M.op pt'' t) G

def andHFml : Fml :=
  Fml.ex 91 (Fml.ex 94 (Fml.ex 89 (Fml.ex 92 (Fml.ex 95 (Fml.ex 93 (Fml.ex 96 (.and (fPN 83 12 89)
    (.and (fPN 89 91 94) (.and (.mem 91 27) (.and (fApp 24 91 92) (.and (fApp4 20 25 65 92 93)
    (.and (.mem 94 27) (.and (fApp 24 94 95) (.and (fApp4 20 25 65 95 96)
    (.and (fApp 6 93 5) (fApp 6 96 5))))))))))))))))

theorem sat_andHFml (ρ : ℕ → V) : Sat M.mem M.isSet andHFml ρ ↔
    M.AndRaw (ρ 20) (ρ 24) (ρ 27) (ρ 25) (ρ 28) (ρ 29) (ρ 12) (ρ 6) (ρ 65) (ρ 5) (ρ 83) := by
  simp [andHFml, AndRaw, fPN, PairRaw, Sat, M.sat_ex, M.sat_fApp3', M.sat_fApp4', M.sat_fApp',
    Function.update_apply]

/-- The clause for the quantifier: `c` is `(3, (v, c'))` and `c'` is true under every `t'`
that has the values of `t`, except that its value at `v` is an arbitrary name `a` of rank
below `α`. -/
def AllRaw (P th io nat Nt j d ad mu z3 G α t c : V) : Prop :=
  ∃ v c' p ch' pt', M.PairRaw ad mu z3 p c ∧ M.PairRaw ad mu v c' p ∧ M.mem c' nat ∧
    M.mem (M.op c' ch') io ∧ M.mem (M.quad j α ch' pt') P ∧
    ∀ a t', M.InNRaw P th io nat j α a → M.AgreeRaw P th io nat Nt j d ad α t t' v a c →
      M.mem (M.op pt' t') G

def allHFml : Fml :=
  Fml.ex 81 (Fml.ex 91 (Fml.ex 89 (Fml.ex 92 (Fml.ex 93 (.and (fPN 83 13 89) (.and (fPN 89 81 91)
    (.and (.mem 91 27) (.and (fApp 24 91 92) (.and (fApp4 20 25 65 92 93)
    (.all 82 (.all 80 (Fml.imp (Fml.ex 68 (.and (.eq 68 82) inNFml))
      (Fml.imp agreeHFml (fApp 6 93 80))))))))))))))

theorem sat_allHFml (ρ : ℕ → V) : Sat M.mem M.isSet allHFml ρ ↔
    M.AllRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 29) (ρ 13) (ρ 6)
      (ρ 65) (ρ 5) (ρ 83) := by
  simp [allHFml, AllRaw, fPN, PairRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fApp3', M.sat_fApp4',
    M.sat_fApp', M.sat_inNFml, M.sat_agreeHFml, Function.update_apply]

/-- One step of the recursion at the point `pt`. If `pt = (α, ĉ)` for a number `c`, it is one
step of the truth definition for the formula `c` at stage `α` and the sequence `t`. If
`pt = (α, tp)`, it is the clause for "denote the same set", and `t` is a pair of names. -/
def HierRaw (P th io nat Nt j d tp qo Nu Pr ad mu z0 z1 z2 z3 G pt t : V) : Prop :=
  ∃ α ch, M.mem (M.quad j α ch pt) P ∧
    ((∃ c, M.mem c nat ∧ M.mem (M.op c ch) io ∧
      (M.AtomRaw P th io nat Nt j d tp qo Nu Pr ad mu z0 z1 z2 G α t c ∨
        M.NegRaw P io nat j ad mu z1 G α t c ∨
        M.AndRaw P io nat j ad mu z2 G α t c ∨ M.AllRaw P th io nat Nt j d ad mu z3 G α t c)) ∨
     (ch = tp ∧ M.SimStepRaw P th io nat j tp G α t))

/-- `HierRaw`, with `pt`, `t`, `G` the names `4`, `5`, `6`. -/
def hierFml : Fml :=
  Fml.ex 65 (Fml.ex 85 (.and (fApp4 20 25 65 85 4) (Fml.or
    (Fml.ex 83 (.and (.mem 83 27) (.and (fApp 24 83 85)
      (Fml.or atomFml (Fml.or negHFml (Fml.or andHFml allHFml))))))
    (.and (.eq 85 21) simStepFml))))

theorem sat_hierFml (ρ : ℕ → V) : Sat M.mem M.isSet hierFml ρ ↔
    M.HierRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 21) (ρ 160) (ρ 161) (ρ 162)
      (ρ 28) (ρ 29) (ρ 10) (ρ 11) (ρ 12) (ρ 13) (ρ 6) (ρ 4) (ρ 5) := by
  simp [hierFml, HierRaw, Sat, M.sat_or, M.sat_ex, M.sat_fApp4', M.sat_fApp', M.sat_atomFml,
    M.sat_negHFml, M.sat_andHFml, M.sat_allHFml, M.sat_simStepFml, Function.update_apply]

/-- **The recursion for the constructible hierarchy has a solution.** For a set well-ordering
`p` (in the application, the lexicographic product of `th` and the numerals with a top
point) there is a set `F` of pairs `⟨pt, t⟩` such that `⟨pt, t⟩ ∈ F` exactly when `pt` is a
point of `p` and one step of the recursion holds at `pt` for `t`, given the part of `F`
below `pt`. -/
theorem exists_hier {p : V} (hp : M.IsWO p) (P th io Nt j d tp qo Nu Pr : V) :
    ∃ F, ∀ pt t, M.mem (M.op pt t) F ↔ M.mem (M.op pt pt) p ∧
      M.HierRaw P th io M.nat Nt j d tp qo Nu Pr M.adG M.muG (0 : M.Num).1 (1 : M.Num).1
        (2 : M.Num).1 (3 : M.Num).1 (M.restr p F pt) pt t := by
  obtain ⟨ρ, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e10, e11, e12, e13, e160, e161,
      e162⟩ :
      ∃ ρ : ℕ → V, ρ 20 = P ∧ ρ 21 = tp ∧ ρ 22 = th ∧ ρ 23 = Nt ∧ ρ 24 = io ∧ ρ 25 = j ∧
        ρ 26 = d ∧ ρ 27 = M.nat ∧ ρ 28 = M.adG ∧ ρ 29 = M.muG ∧ ρ 10 = (0 : M.Num).1 ∧
        ρ 11 = (1 : M.Num).1 ∧ ρ 12 = (2 : M.Num).1 ∧ ρ 13 = (3 : M.Num).1 ∧ ρ 160 = qo ∧
        ρ 161 = Nu ∧ ρ 162 = Pr :=
    ⟨Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (fun _ => dflt) 20 P)
      21 tp) 22 th) 23 Nt) 24 io) 25 j) 26 d) 27 M.nat) 28 M.adG) 29 M.muG) 10 (0 : M.Num).1)
      11 (1 : M.Num).1) 12 (2 : M.Num).1) 13 (3 : M.Num).1) 160 qo) 161 Nu) 162 Pr,
      by simp [Function.update_apply]⟩
  exact M.wo_rec hp (fun pt t G => M.HierRaw P th io M.nat Nt j d tp qo Nu Pr M.adG M.muG
      (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 (3 : M.Num).1 G pt t) hierFml
    [(20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7), (29, 7), (161, 5), (162, 5)] rfl ρ
    (fun ρ' h => by
      rw [M.sat_hierFml, h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide),
        h 24 (by decide), h 25 (by decide), h 26 (by decide), h 27 (by decide), h 28 (by decide),
        h 29 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide),
        h 160 (by decide), h 161 (by decide), h 162 (by decide),
        e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e10, e11, e12, e13, e160, e161, e162])

/-! ### The order of the names

A total preorder `Pr` of the names, defined without reference to truth: names are compared
first by rank, then by the number of the formula, then by their parameters at the indices up
to that number, lexicographically, the values of the parameters being compared by the order of
the earlier stages. Names that tie denote the same set (proved later). The order is the
solution of a recursion along `th`. -/

/-- `RankIs` for the names `b`, `x`. -/
def fRank (b x : ℕ) : Fml := Fml.ex 74 (.and (.eq 74 b) (Fml.ex 72 (.and (.eq 72 x) rankFml)))

theorem sat_fRank {b x : ℕ} (ρ : ℕ → V) (hb : 199 < b) (hx : 199 < x) :
    Sat M.mem M.isSet (fRank b x) ρ ↔ M.RankIs (ρ 20) (ρ 24) (ρ 27) (ρ 25) (ρ b) (ρ x) := by
  have h1 : b ≠ 74 := by omega
  have h2 : x ≠ 74 := by omega
  have h3 : x ≠ 72 := by omega
  simp [fRank, Sat, M.sat_ex, M.sat_rankFml, Function.update_apply, h1, h2, h3]

/-- `i < c` for numbers named `i`, `c`; the number `0` is the name `10`. -/
def fLtN (i c : ℕ) : Fml :=
  Fml.ex 84 (.and (.mem 84 27) (.and (.neg (.eq 84 10)) (fApp3 28 i 84 c)))

theorem sat_fLtN {i c : ℕ} (ρ : ℕ → V) (hi : 199 < i) (hc : 199 < c) :
    Sat M.mem M.isSet (fLtN i c) ρ ↔
      ∃ x, M.mem x (ρ 27) ∧ ¬ x = ρ 10 ∧ M.mem (M.trip (ρ i) x (ρ c)) (ρ 28) := by
  have b1 : i ≠ 84 := by omega
  have b2 : c ≠ 84 := by omega
  have b3 : i < 30 ∨ 59 < i := by omega
  have b4 : c < 30 ∨ 59 < c := by omega
  simp [fLtN, Sat, M.sat_ex, M.sat_fApp3', Function.update_apply, b1, b2, b3, b4]

/-- `x` is at most `y` in the order of the names given by the earlier stages `G`: `x` has
smaller rank, or the same rank and the pair is recorded in `G`; or `x = y`. -/
def LeERaw (P th io nat j G x y : V) : Prop :=
  x = y ∨ ∃ ρx ρy, M.RankIs P io nat j ρx x ∧ M.RankIs P io nat j ρy y ∧
    ((M.mem (M.op ρx ρy) th ∧ ¬ ρx = ρy) ∨
      (ρx = ρy ∧ ∃ yy, M.mem (M.quad j x y yy) P ∧ M.mem (M.op ρx yy) G))

def fLeE (x y : ℕ) : Fml :=
  Fml.or (.eq x y) (Fml.ex 220 (Fml.ex 221 (.and (fRank 220 x) (.and (fRank 221 y) (Fml.or (.and
    (fApp 22 220 221) (.neg (.eq 220 221))) (.and (.eq 220 221) (Fml.ex 222 (.and (fApp4 20 25 x
    y 222) (fApp 6 220 222)))))))))

theorem sat_fLeE {x y : ℕ} (ρ : ℕ → V) (hx : 222 < x) (hy : 222 < y) :
    Sat M.mem M.isSet (fLeE x y) ρ ↔
      M.LeERaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 25) (ρ 6) (ρ x) (ρ y) := by
  have b1 : x ≠ 220 := by omega
  have b2 : x ≠ 221 := by omega
  have b3 : x ≠ 222 := by omega
  have b4 : y ≠ 220 := by omega
  have b5 : y ≠ 221 := by omega
  have b6 : y ≠ 222 := by omega
  have b7 : 199 < x := by omega
  have b8 : 199 < y := by omega
  have b9 : x < 30 ∨ 59 < x := by omega
  have b10 : y < 30 ∨ 59 < y := by omega
  simp [fLeE, LeERaw, Sat, M.sat_or, M.sat_ex, M.sat_fRank, M.sat_fApp', M.sat_fApp4',
    Function.update_apply, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]

/-- `u'` is strictly below `u` lexicographically at the indices up to `k`, at stage `β`. -/
def LexLtRaw (P th io nat Nt j d ad z0 G β k u' u : V) : Prop :=
  ∃ i, M.mem i nat ∧ (∃ x, M.mem x nat ∧ M.mem (M.trip i x k) ad) ∧ ∃ e' e,
    M.ValRaw P th io nat Nt j d β u' i e' ∧ M.ValRaw P th io nat Nt j d β u i e ∧
    M.LeERaw P th io nat j G e' e ∧ ¬ M.LeERaw P th io nat j G e e' ∧
    ∀ i', M.mem i' nat → (∃ x, M.mem x nat ∧ ¬ x = z0 ∧ M.mem (M.trip i' x i) ad) →
      ∃ g' g, M.ValRaw P th io nat Nt j d β u' i' g' ∧ M.ValRaw P th io nat Nt j d β u i' g ∧
        M.LeERaw P th io nat j G g' g ∧ M.LeERaw P th io nat j G g g'

/-- `LexLtRaw`, with `β`, `k`, `u'`, `u` the names `4`, `223`, `224`, `225`. -/
def lexLtFml : Fml :=
  Fml.ex 226 (.and (.mem 226 27) (.and (fLeN 226 223) (Fml.ex 227 (Fml.ex 228 (.and (fVal 4 224
    226 227) (.and (fVal 4 225 226 228) (.and (fLeE 227 228) (.and (.neg (fLeE 228 227)) (.all
    229 (Fml.imp (.mem 229 27) (Fml.imp (fLtN 229 226) (Fml.ex 230 (Fml.ex 231 (.and (fVal 4 224
    229 230) (.and (fVal 4 225 229 231) (.and (fLeE 230 231) (fLeE 231 230)))))))))))))))))

theorem sat_lexLtFml (ρ : ℕ → V) : Sat M.mem M.isSet lexLtFml ρ ↔
    M.LexLtRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 10) (ρ 6) (ρ 4)
      (ρ 223) (ρ 224) (ρ 225) := by
  simp [lexLtFml, LexLtRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fVal, M.sat_fLeN, M.sat_fLtN,
    M.sat_fLeE, Function.update_apply]

/-- One step of the recursion for the order of the names: `y` is the pair of two names `n`,
`n'` of rank `β` with `n` at most `n'`. -/
def PrStepRaw (P th io nat Nt j d ad z0 G β y : V) : Prop :=
  ∃ n n' f u q f' u' q' k k', M.mem (M.quad j n n' y) P ∧ M.mem (M.quad j β q n) P ∧
    M.mem (M.quad j f u q) P ∧ M.mem k nat ∧ M.mem (M.op k f) io ∧ M.mem (M.quad j β q' n') P ∧
    M.mem (M.quad j f' u' q') P ∧ M.mem k' nat ∧ M.mem (M.op k' f') io ∧
    (((∃ x, M.mem x nat ∧ M.mem (M.trip k x k') ad) ∧ ¬ k = k') ∨
      (k = k' ∧ ¬ M.LexLtRaw P th io nat Nt j d ad z0 G β k u' u))

/-- `PrStepRaw`, with `β`, `y`, `G` the names `4`, `5`, `6`. -/
def prStepFml : Fml :=
  Fml.ex 232 (Fml.ex 233 (Fml.ex 234 (Fml.ex 225 (Fml.ex 235 (Fml.ex 236 (Fml.ex 224 (Fml.ex 237
    (Fml.ex 223 (Fml.ex 238 (.and (fApp4 20 25 232 233 5) (.and (fApp4 20 25 4 235 232) (.and
    (fApp4 20 25 234 225 235) (.and (.mem 223 27) (.and (fApp 24 223 234) (.and (fApp4 20 25 4
    237 233) (.and (fApp4 20 25 236 224 237) (.and (.mem 238 27) (.and (fApp 24 238 236) (Fml.or
    (.and (fLeN 223 238) (.neg (.eq 223 238))) (.and (.eq 223 238) (.neg
    lexLtFml)))))))))))))))))))))

theorem sat_prStepFml (ρ : ℕ → V) : Sat M.mem M.isSet prStepFml ρ ↔
    M.PrStepRaw (ρ 20) (ρ 22) (ρ 24) (ρ 27) (ρ 23) (ρ 25) (ρ 26) (ρ 28) (ρ 10) (ρ 6) (ρ 4)
      (ρ 5) := by
  simp [prStepFml, PrStepRaw, Sat, M.sat_or, M.sat_ex, M.sat_fApp', M.sat_fApp4', M.sat_fLeN,
    M.sat_lexLtFml, Function.update_apply]

/-- `Pr` is the order of the names: it compares names of different ranks by rank, and names of
the same rank by the solution `Pr0` of the recursion. -/
def IsPrec (P th io Nt d Pr : V) (j : M.Num) : Prop :=
  ∃ Pr0, (∀ β y, M.mem (M.op β y) Pr0 ↔ M.mem (M.op β β) th ∧
      M.PrStepRaw P th io M.nat Nt j.1 d M.adG (0 : M.Num).1 (M.restr th Pr0 β) β y) ∧
    ∀ n n', M.mem (M.op n n') Pr ↔ ∃ ρx ρy, M.RankIs P io M.nat j.1 ρx n ∧
      M.RankIs P io M.nat j.1 ρy n' ∧ ((M.mem (M.op ρx ρy) th ∧ ¬ ρx = ρy) ∨
        (ρx = ρy ∧ ∃ yy, M.mem (M.quad j.1 n n' yy) P ∧ M.mem (M.op ρx yy) Pr0))

theorem exists_precOrder {th : V} (hth : M.IsWO th) (P io Nt d : V) (j : M.Num) :
    ∃ Pr, M.IsPrec P th io Nt d Pr j := by
  obtain ⟨ρ, e20, e22, e23, e24, e25, e26, e27, e28, e10⟩ :
      ∃ ρ : ℕ → V, ρ 20 = P ∧ ρ 22 = th ∧ ρ 23 = Nt ∧ ρ 24 = io ∧ ρ 25 = j.1 ∧ ρ 26 = d ∧
        ρ 27 = M.nat ∧ ρ 28 = M.adG ∧ ρ 10 = (0 : M.Num).1 :=
    ⟨Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 20 P)
      22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 10 (0 : M.Num).1,
      by simp [Function.update_apply]⟩
  obtain ⟨Pr0, hPr0⟩ := M.wo_rec hth (fun β y G => M.PrStepRaw P th io M.nat Nt j.1 d M.adG
      (0 : M.Num).1 G β y) prStepFml [(20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7)] rfl ρ
    (fun ρ' h => by
      rw [M.sat_prStepFml, h 20 (by decide), h 22 (by decide), h 23 (by decide), h 24 (by decide),
        h 25 (by decide), h 26 (by decide), h 27 (by decide), h 28 (by decide), h 10 (by decide),
        e20, e22, e23, e24, e25, e26, e27, e28, e10])
  obtain ⟨Pr, -, hPr⟩ := M.comp (σW [(0, 4), (6, 5), (20, 7), (22, 5), (24, 5), (27, 3)])
    (Fml.ex 201 (Fml.ex 202 (Fml.ex 220 (Fml.ex 221 (.and (fPr 0 201 202) (.and (fRank 220 201) (.and (fRank 221 202) (Fml.or (.and (fApp 22 220 221) (.neg (.eq 220 221))) (.and (.eq 220 221) (Fml.ex 222 (.and (fApp4 20 25 201 202 222) (fApp 6 220 222)))))))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (fun _ => dflt) 6 Pr0) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat)
  have hPr1 : ∀ t, M.mem t Pr ↔ ∃ n n' ρx ρy, t = M.op n n' ∧ M.RankIs P io M.nat j.1 ρx n ∧
      M.RankIs P io M.nat j.1 ρy n' ∧ ((M.mem (M.op ρx ρy) th ∧ ¬ ρx = ρy) ∨
        (ρx = ρy ∧ ∃ yy, M.mem (M.quad j.1 n n' yy) P ∧ M.mem (M.op ρx yy) Pr0)) := by
    intro t
    rw [hPr t]
    simp [Sat, M.sat_or, M.sat_ex, M.sat_fPr', M.sat_fRank, M.sat_fApp', M.sat_fApp4',
      Function.update_apply]
  refine ⟨Pr, Pr0, hPr0, fun n n' => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨n1, n1', ρx, ρy, e, h'⟩ := (hPr1 _).mp h
    obtain ⟨e1, e2⟩ := M.op_inj e
    rw [e1, e2]
    exact ⟨ρx, ρy, h'⟩
  · obtain ⟨ρx, ρy, h'⟩ := h
    exact (hPr1 _).mpr ⟨n, n', ρx, ρy, rfl, h'⟩
/-! ### The clauses of the truth definition, in clean form -/

/-- The data of the constructible hierarchy on rung `j` along the well-ordering `th`: the
pairing `P`, the numerals `io`, the entries of sequences `Nt`, the order `nle` of the
numerals with the top point `tp`, the lexicographic product `p` of `th` and `nle`, the default
value `d` (a name of least rank), and the solution `F` of the recursion. -/
structure HierData (R P th io Nt nle p F d tp qo Nu Pr : V) (m j : M.Num) : Prop where
  hP : M.IsPairing R P m
  hj : j ≤ m
  hth : M.IsWO th
  th_rung : ∀ a b, M.mem (M.op a b) th → M.mem (M.op j.1 a) R ∧ M.mem (M.op j.1 b) R
  io_dom : ∀ k a, M.mem (M.op k a) io → M.mem k M.nat ∧ M.mem (M.op j.1 a) R
  io_tot : ∀ n : M.Num, ∃ a, M.mem (M.op n.1 a) io
  io_fun : ∀ k a a', M.mem (M.op k a) io → M.mem (M.op k a') io → a = a'
  io_inj : ∀ k k' a, M.mem (M.op k a) io → M.mem (M.op k' a) io → k = k'
  nt_dom : ∀ t n a, M.mem (M.trip t n a) Nt →
    M.mem n M.nat ∧ M.mem (M.op j.1 t) R ∧ M.mem (M.op j.1 a) R
  nt_zero : ∀ t a, M.mem (M.trip t M.zero a) Nt ↔ ∃ t', M.mem (M.quad j.1 a t' t) P
  nt_succ : ∀ (n : M.Num) (t b : V), M.mem (M.trip t (n + 1).1 b) Nt ↔
    ∃ a t', M.mem (M.quad j.1 a t' t) P ∧ M.mem (M.trip t' n.1 b) Nt
  nle_num : ∀ (c c' : M.Num) (a a' : V), M.mem (M.op c.1 a) io → M.mem (M.op c'.1 a') io →
    (M.mem (M.op a a') nle ↔ c ≤ c')
  nle_top : ∀ a, M.mem (M.op a tp) nle ↔ (a = tp ∨ ∃ k, M.mem (M.op k a) io)
  tp_not_num : ∀ k, ¬ M.mem (M.op k tp) io
  tp_rung : M.mem (M.op j.1 tp) R
  hp : ∀ c c', M.mem (M.op c c') p ↔ M.LexRaw P j.1 th nle c c'
  d_spec : ∃ α0 f0 u0 q0, M.mem (M.quad j.1 α0 q0 d) P ∧ M.mem (M.quad j.1 f0 u0 q0) P ∧
    (∃ k, M.mem (M.op k f0) io) ∧ ∀ α, M.mem (M.op α α) th → M.mem (M.op α0 α) th
  hF : ∀ pt t, M.mem (M.op pt t) F ↔ M.mem (M.op pt pt) p ∧
    M.HierRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG M.muG (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1
      (3 : M.Num).1 (M.restr p F pt) pt t

/-- The formula `c` is true at stage `α` under the sequence `t`. -/
def TrueAt (P io F j α : V) (c : M.Num) (t : V) : Prop :=
  ∃ ch pt, M.mem (M.op c.1 ch) io ∧ M.mem (M.quad j α ch pt) P ∧ M.mem (M.op pt t) F

theorem pairRaw_num (k : M.Num) (x : V) (c : M.Num) :
    M.PairRaw M.adG M.muG k.1 x c.1 ↔ ∃ Y : M.Num, Y.1 = x ∧ c = M.pairN k Y := by
  rw [M.pairRaw_iff M.adG_spec M.muG_spec]
  constructor
  · rintro ⟨X, Y, hX, hY, hc⟩
    have e : X = k := Subtype.ext hX
    rw [e] at hc
    exact ⟨Y, hY, Subtype.ext hc⟩
  · rintro ⟨Y, hY, hc⟩
    exact ⟨k, Y, rfl, hY, by rw [hc]⟩

section hier

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem hier_pt (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) (c : M.Num) :
    ∃ ch pt, M.mem (M.op c.1 ch) io ∧ M.mem (M.quad j.1 α ch pt) P ∧ M.mem (M.op pt pt) p := by
  obtain ⟨ch, hc⟩ := hd.io_tot c
  obtain ⟨pt, q⟩ := hd.hP.tot j hd.hj α ch (hd.th_rung α α hα).1 (hd.io_dom _ _ hc).2
  have hnn : M.mem (M.op ch ch) nle := (hd.nle_num c c ch ch hc hc).mpr (le_refl c)
  exact ⟨ch, pt, hc, q, (hd.hp pt pt).mpr ⟨α, ch, α, ch, q, q, hα, hα, hnn, hnn, Or.inr ⟨rfl, hnn⟩⟩⟩

theorem hier_pt_top (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) :
    ∃ pt, M.mem (M.quad j.1 α tp pt) P ∧ M.mem (M.op pt pt) p := by
  obtain ⟨pt, q⟩ := hd.hP.tot j hd.hj α tp (hd.th_rung α α hα).1 hd.tp_rung
  have hnn : M.mem (M.op tp tp) nle := (hd.nle_top tp).mpr (Or.inl rfl)
  exact ⟨pt, q, (hd.hp pt pt).mpr ⟨α, tp, α, tp, q, q, hα, hα, hnn, hnn, Or.inr ⟨rfl, hnn⟩⟩⟩

theorem hier_below' (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α α' ch ch' pt pt' : V}
    (q : M.mem (M.quad j.1 α ch pt) P) (q' : M.mem (M.quad j.1 α' ch' pt') P)
    (hα : M.mem (M.op α α) th) (hα' : M.mem (M.op α' α') th) (hch : M.mem (M.op ch ch) nle)
    (hch' : M.mem (M.op ch' ch') nle)
    (hlt : (M.mem (M.op α' α) th ∧ α' ≠ α) ∨ (α' = α ∧ M.mem (M.op ch' ch) nle ∧ ch' ≠ ch)) :
    M.mem (M.op pt' pt) p ∧ pt' ≠ pt := by
  constructor
  · refine (hd.hp pt' pt).mpr ⟨α', ch', α, ch, q', q, hα', hα, hch', hch, ?_⟩
    rcases hlt with h | ⟨e, h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, h⟩
  · intro e
    rw [e] at q'
    obtain ⟨e1, e2⟩ := hd.hP.inj _ _ _ _ _ _ q' q
    rcases hlt with ⟨-, hne⟩ | ⟨-, -, hne⟩
    · exact hne e1
    · exact hne e2

theorem hier_below (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α α' ch ch' pt pt' : V}
    {c c' : M.Num} (q : M.mem (M.quad j.1 α ch pt) P) (q' : M.mem (M.quad j.1 α' ch' pt') P)
    (hc : M.mem (M.op c.1 ch) io) (hc' : M.mem (M.op c'.1 ch') io) (hα : M.mem (M.op α α) th)
    (hα' : M.mem (M.op α' α') th)
    (hlt : (M.mem (M.op α' α) th ∧ α' ≠ α) ∨ (α' = α ∧ c' + 1 ≤ c)) :
    M.mem (M.op pt' pt) p ∧ pt' ≠ pt := by
  refine M.hier_below' hd q q' hα hα' ((hd.nle_num c c ch ch hc hc).mpr (le_refl c))
    ((hd.nle_num c' c' ch' ch' hc' hc').mpr (le_refl c')) ?_
  rcases hlt with h | ⟨e, hcc⟩
  · exact Or.inl h
  · refine Or.inr ⟨e, (hd.nle_num c' c ch' ch hc' hc).mpr (le_trans (M.le_add_one c') hcc),
      fun e2 => ?_⟩
    rw [e2] at hc'
    have e3 : c' = c := Subtype.ext (hd.io_inj _ _ _ hc' hc)
    rw [e3] at hcc
    exact M.not_succ_le c hcc

theorem hier_restr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α α' ch ch' pt pt' : V}
    {c c' : M.Num} (q : M.mem (M.quad j.1 α ch pt) P) (q' : M.mem (M.quad j.1 α' ch' pt') P)
    (hc : M.mem (M.op c.1 ch) io) (hc' : M.mem (M.op c'.1 ch') io) (hα : M.mem (M.op α α) th)
    (hα' : M.mem (M.op α' α') th)
    (hlt : (M.mem (M.op α' α) th ∧ α' ≠ α) ∨ (α' = α ∧ c' + 1 ≤ c)) (t : V) :
    M.mem (M.op pt' t) (M.restr p F pt) ↔ M.mem (M.op pt' t) F := by
  have hb := M.hier_below hd q q' hc hc' hα hα' hlt
  rw [M.mem_restr]
  exact ⟨fun h => h.1, fun h => ⟨h, hb.1, hb.2⟩⟩

theorem hier_unpack (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α ch pt : V} {c : M.Num}
    (q : M.mem (M.quad j.1 α ch pt) P) (hc : M.mem (M.op c.1 ch) io) (G t : V) :
    M.HierRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG M.muG (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1
      (3 : M.Num).1 G pt t ↔
    (M.AtomRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG M.muG (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1 G α t c.1 ∨
      M.NegRaw P io M.nat j.1 M.adG M.muG (1 : M.Num).1 G α t c.1 ∨
      M.AndRaw P io M.nat j.1 M.adG M.muG (2 : M.Num).1 G α t c.1 ∨
      M.AllRaw P th io M.nat Nt j.1 d M.adG M.muG (3 : M.Num).1 G α t c.1) := by
  constructor
  · rintro ⟨α1, ch1, q1, ⟨c1, -, hc1, h⟩ | ⟨e, -⟩⟩
    · obtain ⟨e1, e2⟩ := hd.hP.inj _ _ _ _ _ _ q1 q
      rw [e2] at hc1
      rw [e1, hd.io_inj _ _ _ hc1 hc] at h
      exact h
    · obtain ⟨-, e2⟩ := hd.hP.inj _ _ _ _ _ _ q1 q
      rw [← e2, e] at hc
      exact absurd hc (hd.tp_not_num _)
  · intro h
    exact ⟨α, ch, q, Or.inl ⟨c.1, c.2, hc, h⟩⟩

theorem hier_unpack_top (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α pt : V}
    (q : M.mem (M.quad j.1 α tp pt) P) (G t : V) :
    M.HierRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG M.muG (0 : M.Num).1 (1 : M.Num).1 (2 : M.Num).1
      (3 : M.Num).1 G pt t ↔ M.SimStepRaw P th io M.nat j.1 tp G α t := by
  constructor
  · rintro ⟨α1, ch1, q1, ⟨c1, -, hc1, -⟩ | ⟨-, h⟩⟩
    · obtain ⟨-, e2⟩ := hd.hP.inj _ _ _ _ _ _ q1 q
      rw [e2] at hc1
      exact absurd hc1 (hd.tp_not_num _)
    · rw [(hd.hP.inj _ _ _ _ _ _ q1 q).1] at h
      exact h
  · intro h
    exact ⟨α, tp, q, Or.inr ⟨rfl, h⟩⟩

theorem trueAt_iff (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α ch pt : V} {c : M.Num}
    (q : M.mem (M.quad j.1 α ch pt) P) (hc : M.mem (M.op c.1 ch) io) (t : V) :
    M.TrueAt P io F j.1 α c t ↔ M.mem (M.op pt t) F := by
  constructor
  · rintro ⟨ch2, pt2, hc2, q2, h⟩
    rw [hd.io_fun _ _ _ hc2 hc] at q2
    rw [hd.hP.fn _ _ _ _ _ q2 q] at h
    exact h
  · intro h
    exact ⟨ch, pt, hc, q, h⟩

theorem trueAt_fld (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V} {c : M.Num} {t : V}
    (h : M.TrueAt P io F j.1 α c t) : M.mem (M.op α α) th := by
  obtain ⟨ch, pt, hc, q, hF⟩ := h
  obtain ⟨a, b, a', b', q1, -, ha, -⟩ := (hd.hp pt pt).mp ((hd.hF pt t).mp hF).1
  rw [(hd.hP.inj _ _ _ _ _ _ q1 q).1] at ha
  exact ha

/-- **Negation.** -/
theorem hier_neg (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V} (c : M.Num) (t : V) :
    M.TrueAt P io F j.1 α (M.cNeg c) t ↔
      M.mem (M.op α α) th ∧ ¬ M.TrueAt P io F j.1 α c t := by
  constructor
  · intro h
    have hα := M.trueAt_fld hd h
    refine ⟨hα, ?_⟩
    obtain ⟨ch, pt, hc, q, hpt⟩ := M.hier_pt hd hα (M.cNeg c)
    obtain ⟨ch', pt', hc', q', -⟩ := M.hier_pt hd hα c
    have hF := (M.trueAt_iff hd q hc t).mp h
    have hier := (M.hier_unpack hd q hc _ t).mp ((hd.hF pt t).mp hF).2
    rw [M.trueAt_iff hd q' hc' t]
    rcases hier with hA | hN | hC | hQ
    · obtain ⟨r, v, w, p1, p2, hpr, -⟩ := hA
      obtain ⟨Y, -, e⟩ := (M.pairRaw_num 0 p1 (M.cNeg c)).mp hpr
      have e' : M.pairN 1 c = M.pairN 0 Y := e
      exact absurd (M.pairN_inj e').1 M.n10
    · obtain ⟨c1, ch1, pt1, hpr, -, hc1, q1, hnot⟩ := hN
      obtain ⟨Y, hY, e⟩ := (M.pairRaw_num 1 c1 (M.cNeg c)).mp hpr
      have e' : M.pairN 1 c = M.pairN 1 Y := e
      rw [← hY, ← (M.pairN_inj e').2] at hc1
      rw [hd.io_fun _ _ _ hc1 hc'] at q1
      rw [hd.hP.fn _ _ _ _ _ q1 q'] at hnot
      intro hF'
      exact hnot ((M.hier_restr hd q q' hc hc' hα hα
        (Or.inr ⟨rfl, M.lt_pairN_right c (le_refl 1)⟩) t).mpr hF')
    · obtain ⟨c1, c2, p0, ch1, ch2, pt1, pt2, hpr, -⟩ := hC
      obtain ⟨Y, -, e⟩ := (M.pairRaw_num 2 p0 (M.cNeg c)).mp hpr
      have e' : M.pairN 1 c = M.pairN 2 Y := e
      exact absurd (M.pairN_inj e').1 M.n12
    · obtain ⟨v, c1, p0, ch1, pt1, hpr, -⟩ := hQ
      obtain ⟨Y, -, e⟩ := (M.pairRaw_num 3 p0 (M.cNeg c)).mp hpr
      have e' : M.pairN 1 c = M.pairN 3 Y := e
      exact absurd (M.pairN_inj e').1 M.n13
  · rintro ⟨hα, hnot⟩
    obtain ⟨ch, pt, hc, q, hpt⟩ := M.hier_pt hd hα (M.cNeg c)
    obtain ⟨ch', pt', hc', q', -⟩ := M.hier_pt hd hα c
    refine (M.trueAt_iff hd q hc t).mpr ((hd.hF pt t).mpr ⟨hpt, (M.hier_unpack hd q hc _ t).mpr
      (Or.inr (Or.inl ⟨c.1, ch', pt', (M.pairRaw_num 1 c.1 (M.cNeg c)).mpr ⟨c, rfl, rfl⟩, c.2,
        hc', q', fun hr => hnot ((M.trueAt_iff hd q' hc' t).mpr ((M.hier_restr hd q q' hc hc'
          hα hα (Or.inr ⟨rfl, M.lt_pairN_right c (le_refl 1)⟩) t).mp hr))⟩))⟩)

theorem one_le_two' : (1 : M.Num) ≤ 2 := M.le_def.mpr ⟨1, by norm_num⟩

theorem one_le_three' : (1 : M.Num) ≤ 3 := M.le_def.mpr ⟨2, by norm_num⟩

/-- **Conjunction.** -/
theorem hier_and (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V} (c c' : M.Num) (t : V) :
    M.TrueAt P io F j.1 α (M.cAnd c c') t ↔
      M.mem (M.op α α) th ∧ M.TrueAt P io F j.1 α c t ∧ M.TrueAt P io F j.1 α c' t := by
  have lt1 : c + 1 ≤ M.cAnd c c' :=
    le_trans (add_le_add (M.le_pairN_left c c') (le_refl 1)) (M.lt_pairN_right _ M.one_le_two')
  have lt2 : c' + 1 ≤ M.cAnd c c' :=
    le_trans (add_le_add (M.le_pairN_right c c') (le_refl 1)) (M.lt_pairN_right _ M.one_le_two')
  constructor
  · intro h
    have hα := M.trueAt_fld hd h
    refine ⟨hα, ?_⟩
    obtain ⟨ch, pt, hc, q, hpt⟩ := M.hier_pt hd hα (M.cAnd c c')
    obtain ⟨ch1', pt1', hc1', q1', -⟩ := M.hier_pt hd hα c
    obtain ⟨ch2', pt2', hc2', q2', -⟩ := M.hier_pt hd hα c'
    have hF := (M.trueAt_iff hd q hc t).mp h
    have hier := (M.hier_unpack hd q hc _ t).mp ((hd.hF pt t).mp hF).2
    rw [M.trueAt_iff hd q1' hc1' t, M.trueAt_iff hd q2' hc2' t]
    rcases hier with hA | hN | hC | hQ
    · obtain ⟨r, v, w, p1, p2, hpr, -⟩ := hA
      obtain ⟨Y, -, e⟩ := (M.pairRaw_num 0 p1 (M.cAnd c c')).mp hpr
      have e' : M.pairN 2 (M.pairN c c') = M.pairN 0 Y := e
      exact absurd (M.pairN_inj e').1 M.n20
    · obtain ⟨c1, ch1, pt1, hpr, -⟩ := hN
      obtain ⟨Y, -, e⟩ := (M.pairRaw_num 1 c1 (M.cAnd c c')).mp hpr
      have e' : M.pairN 2 (M.pairN c c') = M.pairN 1 Y := e
      exact absurd (M.pairN_inj e').1 M.n21
    · obtain ⟨c1, c2, p0, ch1, ch2, pt1, pt2, hpr, hpr2, -, hc1, q1, -, hc2, q2, h1, h2⟩ := hC
      obtain ⟨Y, hY, e⟩ := (M.pairRaw_num 2 p0 (M.cAnd c c')).mp hpr
      have e' : M.pairN 2 (M.pairN c c') = M.pairN 2 Y := e
      rw [← hY, ← (M.pairN_inj e').2] at hpr2
      obtain ⟨X1, X2, hX1, hX2, e2⟩ := (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mp hpr2
      obtain ⟨e3, e4⟩ := M.pairN_inj (Subtype.ext e2 : M.pairN c c' = M.pairN X1 X2)
      rw [← hX1, ← e3] at hc1
      rw [← hX2, ← e4] at hc2
      rw [hd.io_fun _ _ _ hc1 hc1'] at q1
      rw [hd.io_fun _ _ _ hc2 hc2'] at q2
      rw [hd.hP.fn _ _ _ _ _ q1 q1'] at h1
      rw [hd.hP.fn _ _ _ _ _ q2 q2'] at h2
      exact ⟨(M.hier_restr hd q q1' hc hc1' hα hα (Or.inr ⟨rfl, lt1⟩) t).mp h1,
        (M.hier_restr hd q q2' hc hc2' hα hα (Or.inr ⟨rfl, lt2⟩) t).mp h2⟩
    · obtain ⟨v, c1, p0, ch1, pt1, hpr, -⟩ := hQ
      obtain ⟨Y, -, e⟩ := (M.pairRaw_num 3 p0 (M.cAnd c c')).mp hpr
      have e' : M.pairN 2 (M.pairN c c') = M.pairN 3 Y := e
      exact absurd (M.pairN_inj e').1 M.n23
  · rintro ⟨hα, h1, h2⟩
    obtain ⟨ch, pt, hc, q, hpt⟩ := M.hier_pt hd hα (M.cAnd c c')
    obtain ⟨ch1', pt1', hc1', q1', -⟩ := M.hier_pt hd hα c
    obtain ⟨ch2', pt2', hc2', q2', -⟩ := M.hier_pt hd hα c'
    refine (M.trueAt_iff hd q hc t).mpr ((hd.hF pt t).mpr ⟨hpt, (M.hier_unpack hd q hc _ t).mpr
      (Or.inr (Or.inr (Or.inl ⟨c.1, c'.1, (M.pairN c c').1, ch1', ch2', pt1', pt2',
        (M.pairRaw_num 2 _ (M.cAnd c c')).mpr ⟨M.pairN c c', rfl, rfl⟩,
        (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mpr ⟨c, c', rfl, rfl, rfl⟩,
        c.2, hc1', q1', c'.2, hc2', q2',
        (M.hier_restr hd q q1' hc hc1' hα hα (Or.inr ⟨rfl, lt1⟩) t).mpr
          ((M.trueAt_iff hd q1' hc1' t).mp h1),
        (M.hier_restr hd q q2' hc hc2' hα hα (Or.inr ⟨rfl, lt2⟩) t).mpr
          ((M.trueAt_iff hd q2' hc2' t).mp h2)⟩)))⟩)

end hier

section hier2

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **The quantifier.** `∀v c` is true at stage `α` under `t` if and only if `c` is true under
every `t'` that has the values of `t` at the variables up to the code, except that its value
at `v` is an arbitrary name of rank below `α`. -/
theorem hier_all (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V} (v c : M.Num) (t : V) :
    M.TrueAt P io F j.1 α (M.cAll v c) t ↔ M.mem (M.op α α) th ∧
      ∀ a t', M.InNRaw P th io M.nat j.1 α a →
        M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v.1 a (M.cAll v c).1 →
        M.TrueAt P io F j.1 α c t' := by
  have lt1 : c + 1 ≤ M.cAll v c :=
    le_trans (add_le_add (M.le_pairN_right v c) (le_refl 1)) (M.lt_pairN_right _ M.one_le_three')
  constructor
  · intro h
    have hα := M.trueAt_fld hd h
    refine ⟨hα, fun a t' ha hag => ?_⟩
    obtain ⟨ch, pt, hc, q, hpt⟩ := M.hier_pt hd hα (M.cAll v c)
    obtain ⟨ch', pt', hc', q', -⟩ := M.hier_pt hd hα c
    have hF := (M.trueAt_iff hd q hc t).mp h
    have hier := (M.hier_unpack hd q hc _ t).mp ((hd.hF pt t).mp hF).2
    rcases hier with hA | hN | hC | hQ
    · obtain ⟨r, v0, w, p1, p2, hpr, -⟩ := hA
      obtain ⟨Y, -, e⟩ := (M.pairRaw_num 0 p1 (M.cAll v c)).mp hpr
      have e' : M.pairN 3 (M.pairN v c) = M.pairN 0 Y := e
      exact absurd (M.pairN_inj e').1 M.n30
    · obtain ⟨c1, ch1, pt1, hpr, -⟩ := hN
      obtain ⟨Y, -, e⟩ := (M.pairRaw_num 1 c1 (M.cAll v c)).mp hpr
      have e' : M.pairN 3 (M.pairN v c) = M.pairN 1 Y := e
      exact absurd (M.pairN_inj e').1 M.n31
    · obtain ⟨c1, c2, p0, ch1, ch2, pt1, pt2, hpr, -⟩ := hC
      obtain ⟨Y, -, e⟩ := (M.pairRaw_num 2 p0 (M.cAll v c)).mp hpr
      have e' : M.pairN 3 (M.pairN v c) = M.pairN 2 Y := e
      exact absurd (M.pairN_inj e').1 M.n32
    · obtain ⟨v1, c1, p0, ch1, pt1, hpr, hpr2, -, hc1, q1, hall⟩ := hQ
      obtain ⟨Y, hY, e⟩ := (M.pairRaw_num 3 p0 (M.cAll v c)).mp hpr
      have e' : M.pairN 3 (M.pairN v c) = M.pairN 3 Y := e
      rw [← hY, ← (M.pairN_inj e').2] at hpr2
      obtain ⟨X1, X2, hX1, hX2, e2⟩ := (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mp hpr2
      obtain ⟨e3, e4⟩ := M.pairN_inj (Subtype.ext e2 : M.pairN v c = M.pairN X1 X2)
      rw [← hX2, ← e4] at hc1
      rw [← hX1, ← e3] at hall
      rw [hd.io_fun _ _ _ hc1 hc'] at q1
      rw [hd.hP.fn _ _ _ _ _ q1 q'] at hall
      exact (M.trueAt_iff hd q' hc' t').mpr ((M.hier_restr hd q q' hc hc' hα hα
        (Or.inr ⟨rfl, lt1⟩) t').mp (hall a t' ha hag))
  · rintro ⟨hα, hall⟩
    obtain ⟨ch, pt, hc, q, hpt⟩ := M.hier_pt hd hα (M.cAll v c)
    obtain ⟨ch', pt', hc', q', -⟩ := M.hier_pt hd hα c
    refine (M.trueAt_iff hd q hc t).mpr ((hd.hF pt t).mpr ⟨hpt, (M.hier_unpack hd q hc _ t).mpr
      (Or.inr (Or.inr (Or.inr ⟨v.1, c.1, (M.pairN v c).1, ch', pt',
        (M.pairRaw_num 3 _ (M.cAll v c)).mpr ⟨M.pairN v c, rfl, rfl⟩,
        (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mpr ⟨v, c, rfl, rfl, rfl⟩, c.2, hc', q',
        fun a t' ha hag => (M.hier_restr hd q q' hc hc' hα hα (Or.inr ⟨rfl, lt1⟩) t').mpr
          ((M.trueAt_iff hd q' hc' t').mp (hall a t' ha hag))⟩)))⟩)

/-- A name of rank below `α` is a name of rank below every later stage. -/
theorem inN_mono (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α α' a : V}
    (h : M.InNRaw P th io M.nat j.1 α a) (hle : M.mem (M.op α α') th) :
    M.InNRaw P th io M.nat j.1 α' a := by
  obtain ⟨β, f, u, q, h1, h2, h3, h4, h5⟩ := h
  refine ⟨β, f, u, q, h1, h2, hd.hth.trans β α α' h3 hle, fun e => ?_, h5⟩
  rw [e] at h3
  exact h4 (e.trans (hd.hth.antisymm α' α h3 hle))

theorem inN_rank {α a : V} (h : M.InNRaw P th io M.nat j.1 α a) :
    ∃ β, M.RankIs P io M.nat j.1 β a ∧ M.mem (M.op β α) th ∧ β ≠ α := by
  obtain ⟨β, f, u, q, h1, h2, h3, h4, h5⟩ := h
  exact ⟨β, ⟨f, u, q, h1, h2, h5⟩, h3, h4⟩

theorem rank_unique (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {β β' a : V}
    (h : M.RankIs P io M.nat j.1 β a) (h' : M.RankIs P io M.nat j.1 β' a) : β = β' := by
  obtain ⟨f, u, q, h1, -⟩ := h
  obtain ⟨f', u', q', h1', -⟩ := h'
  exact (hd.hP.inj _ _ _ _ _ _ h1 h1').1

theorem no_inN_least (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α0 a : V}
    (hleast : ∀ α, M.mem (M.op α α) th → M.mem (M.op α0 α) th)
    (h : M.InNRaw P th io M.nat j.1 α0 a) : False := by
  obtain ⟨β, -, -, -, -, -, m1, m2, -⟩ := h
  exact m2 (hd.hth.antisymm β α0 m1 (hleast β (hd.hth.fld β α0 m1).1))

/-- **The levels are transitive**: the members of a name of rank below `α` are names of rank
below `α`. -/
theorem eps_rank (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α a b : V}
    (hb : M.InNRaw P th io M.nat j.1 α b) (h : M.EpsRaw P th io M.nat j.1 F a b) :
    M.InNRaw P th io M.nat j.1 α a := by
  obtain ⟨β, f, u, q0, s, pt, h1, -, h3, -⟩ := h
  obtain ⟨β', f', u', q', k1, -, k3, -, -⟩ := hb
  rw [(hd.hP.inj _ _ _ _ _ _ k1 h1).1] at k3
  exact M.inN_mono hd h3 k3

/-- Membership in a name of rank below `α` is the same whether read from the part of `F`
below a point of stage `α` or from the whole of `F`. -/
theorem eps_restr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α ch pt : V}
    (q : M.mem (M.quad j.1 α ch pt) P) (hch : M.mem (M.op ch ch) nle)
    (hα : M.mem (M.op α α) th) {a b : V}
    (hb : M.InNRaw P th io M.nat j.1 α b ∨ b = d) :
    M.EpsRaw P th io M.nat j.1 (M.restr p F pt) a b ↔ M.EpsRaw P th io M.nat j.1 F a b := by
  constructor
  · rintro ⟨β, f, u, q0, s, pt2, h1, h2, h3, h4, h5, h6⟩
    exact ⟨β, f, u, q0, s, pt2, h1, h2, h3, h4, h5, (M.mem_restr.mp h6).1⟩
  · rintro ⟨β, f, u, q0, s, pt2, h1, h2, h3, h4, h5, h6⟩
    refine ⟨β, f, u, q0, s, pt2, h1, h2, h3, h4, h5, ?_⟩
    rcases hb with ⟨β', f', u', q', k1, k2, k3, k4, k, hk, hkf⟩ | hbd
    · obtain ⟨e1, e2⟩ := hd.hP.inj _ _ _ _ _ _ k1 h1
      rw [e2] at k2
      obtain ⟨e3, -⟩ := hd.hP.inj _ _ _ _ _ _ k2 h2
      rw [e1] at k3 k4
      rw [e3] at hkf
      have hff : M.mem (M.op f f) nle :=
        (hd.nle_num ⟨k, hk⟩ ⟨k, hk⟩ f f hkf hkf).mpr (le_refl _)
      have hbel := M.hier_below' hd q h5 hα (hd.hth.fld β α k3).1 hch hff (Or.inl ⟨k3, k4⟩)
      exact M.mem_restr.mpr ⟨h6, hbel.1, hbel.2⟩
    · exfalso
      obtain ⟨α0, f0, u0, q00, d1, -, -, dleast⟩ := hd.d_spec
      rw [hbd] at h1
      rw [← (hd.hP.inj _ _ _ _ _ _ d1 h1).1] at h3
      exact M.no_inN_least hd dleast h3

/-- The same at a top point, for a name of rank at most that of the point. -/
theorem eps_restr_top (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {γ pg : V}
    (q : M.mem (M.quad j.1 γ tp pg) P) (hγ : M.mem (M.op γ γ) th) {β a x : V}
    (ha : M.RankIs P io M.nat j.1 β a) (hle : M.mem (M.op β γ) th) :
    M.EpsRaw P th io M.nat j.1 (M.restr p F pg) x a ↔ M.EpsRaw P th io M.nat j.1 F x a := by
  constructor
  · rintro ⟨β1, f, u, q0, s, pt2, h1, h2, h3, h4, h5, h6⟩
    exact ⟨β1, f, u, q0, s, pt2, h1, h2, h3, h4, h5, (M.mem_restr.mp h6).1⟩
  · rintro ⟨β1, f, u, q0, s, pt2, h1, h2, h3, h4, h5, h6⟩
    refine ⟨β1, f, u, q0, s, pt2, h1, h2, h3, h4, h5, ?_⟩
    obtain ⟨f', u', q', k1, k2, k, hk, hkf⟩ := ha
    obtain ⟨e1, e2⟩ := hd.hP.inj _ _ _ _ _ _ k1 h1
    rw [e2] at k2
    obtain ⟨e3, -⟩ := hd.hP.inj _ _ _ _ _ _ k2 h2
    rw [e3] at hkf
    rw [e1] at hle
    have hff : M.mem (M.op f f) nle := (hd.nle_num ⟨k, hk⟩ ⟨k, hk⟩ f f hkf hkf).mpr (le_refl _)
    have htt : M.mem (M.op tp tp) nle := (hd.nle_top tp).mpr (Or.inl rfl)
    have hlt : (M.mem (M.op β1 γ) th ∧ β1 ≠ γ) ∨
        (β1 = γ ∧ M.mem (M.op f tp) nle ∧ f ≠ tp) := by
      by_cases e : β1 = γ
      · refine Or.inr ⟨e, (hd.nle_top f).mpr (Or.inr ⟨k, hkf⟩), fun e' => ?_⟩
        rw [e'] at hkf
        exact hd.tp_not_num k hkf
      · exact Or.inl ⟨hle, e⟩
    have hbel := M.hier_below' hd q h5 hγ (hd.hth.fld β1 γ hle).1 htt hff hlt
    exact M.mem_restr.mpr ⟨h6, hbel.1, hbel.2⟩

/-- "Denote the same set", for names of rank below `α`, is the same whether read from the
part of `F` below a point of stage `α` or from the whole of `F`. -/
theorem sim_restr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α ch pt : V}
    (q : M.mem (M.quad j.1 α ch pt) P) (hch : M.mem (M.op ch ch) nle)
    (hα : M.mem (M.op α α) th) {a a' : V} (ha : M.InNRaw P th io M.nat j.1 α a)
    (ha' : M.InNRaw P th io M.nat j.1 α a') :
    M.SimRaw P j.1 tp (M.restr p F pt) a a' ↔ M.SimRaw P j.1 tp F a a' := by
  constructor
  · rintro ⟨γ, pg, y, g1, g2, g3⟩
    exact ⟨γ, pg, y, g1, g2, (M.mem_restr.mp g3).1⟩
  · rintro ⟨γ, pg, y, g1, g2, g3⟩
    refine ⟨γ, pg, y, g1, g2, ?_⟩
    obtain ⟨-, hier⟩ := (hd.hF pg y).mp g3
    obtain ⟨a1, a1', β, β', s1, r1, r2, l1, l2, hmax, -, -⟩ :=
      (M.hier_unpack_top hd g1 _ y).mp hier
    obtain ⟨e1, e2⟩ := hd.hP.inj _ _ _ _ _ _ s1 g2
    rw [e1] at r1
    rw [e2] at r2
    obtain ⟨β0, rk0, lt0, ne0⟩ := M.inN_rank ha
    obtain ⟨β0', rk0', lt0', ne0'⟩ := M.inN_rank ha'
    rw [← M.rank_unique hd r1 rk0] at lt0 ne0
    rw [← M.rank_unique hd r2 rk0'] at lt0' ne0'
    have hγlt : M.mem (M.op γ α) th ∧ γ ≠ α := by
      rcases hmax with e | e
      · rw [← e]
        exact ⟨lt0, ne0⟩
      · rw [← e]
        exact ⟨lt0', ne0'⟩
    have hbel := M.hier_below' hd q g1 hα (hd.hth.fld γ α hγlt.1).1 hch
      ((hd.nle_top tp).mpr (Or.inl rfl)) (Or.inl hγlt)
    exact M.mem_restr.mpr ⟨g3, hbel.1, hbel.2⟩

/-- Membership between the sets denoted by two values at stage `α` is the same whether read
from the part of `F` below a point of stage `α` or from the whole of `F`. -/
theorem epsStar_restr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α ch pt : V}
    (q : M.mem (M.quad j.1 α ch pt) P) (hch : M.mem (M.op ch ch) nle)
    (hα : M.mem (M.op α α) th) {a b : V} (ha : M.InNRaw P th io M.nat j.1 α a ∨ a = d)
    (hb : M.InNRaw P th io M.nat j.1 α b ∨ b = d) :
    M.EpsStarRaw P th io M.nat j.1 tp (M.restr p F pt) a b ↔
      M.EpsStarRaw P th io M.nat j.1 tp F a b := by
  constructor
  · rintro ⟨a', ⟨γ, pg, y, g1, g2, g3⟩, he⟩
    exact ⟨a', ⟨γ, pg, y, g1, g2, (M.mem_restr.mp g3).1⟩, (M.eps_restr hd q hch hα hb).mp he⟩
  · rintro ⟨a', hs, he⟩
    obtain ⟨α0, f0, u0, q00, d1, d2, ⟨k0, hk0⟩, dleast⟩ := hd.d_spec
    have hbN : M.InNRaw P th io M.nat j.1 α b := by
      rcases hb with hb | hbd
      · exact hb
      · exfalso
        obtain ⟨β, f, u, q0, s, pt2, h1, -, h3, -⟩ := he
        rw [hbd] at h1
        rw [← (hd.hP.inj _ _ _ _ _ _ d1 h1).1] at h3
        exact M.no_inN_least hd dleast h3
    have ha'N : M.InNRaw P th io M.nat j.1 α a' := M.eps_rank hd hbN he
    have haN : M.InNRaw P th io M.nat j.1 α a := by
      rcases ha with ha | had
      · exact ha
      · rw [had]
        obtain ⟨βb, -, ltb, neb⟩ := M.inN_rank hbN
        refine ⟨α0, f0, u0, q00, d1, d2, dleast α hα, fun e => ?_, k0, (hd.io_dom _ _ hk0).1, hk0⟩
        rw [← e] at ltb neb
        exact neb (hd.hth.antisymm βb α0 ltb (dleast βb (hd.hth.fld βb α0 ltb).1))
    exact ⟨a', (M.sim_restr hd q hch hα haN ha'N).mpr hs,
      (M.eps_restr hd q hch hα (Or.inl hbN)).mpr he⟩

/-- The default name has rank below every stage that is not the least. -/
theorem d_inN (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α β : V}
    (hlt : M.mem (M.op β α) th) (hne : β ≠ α) : M.InNRaw P th io M.nat j.1 α d := by
  obtain ⟨α0, f0, u0, q0, h1, h2, ⟨k, hk⟩, hleast⟩ := hd.d_spec
  have h0β := hleast β (hd.hth.fld β α hlt).1
  refine ⟨α0, f0, u0, q0, h1, h2, hd.hth.trans α0 β α h0β hlt, fun e => ?_, k,
    (hd.io_dom _ _ hk).1, hk⟩
  rw [e] at h0β
  exact hne (hd.hth.antisymm β α hlt h0β)

theorem val_cases {α t i e : V} (hv : M.ValRaw P th io M.nat Nt j.1 d α t i e) :
    M.InNRaw P th io M.nat j.1 α e ∨ e = d := by
  rcases hv with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-- A value at an earlier stage is a name of rank below a later stage. -/
theorem val_inN_of_lt (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α β t i e : V}
    (hβα : M.mem (M.op β α) th) (hne : β ≠ α)
    (hv : M.ValRaw P th io M.nat Nt j.1 d β t i e) : M.InNRaw P th io M.nat j.1 α e := by
  rcases hv with ⟨-, h⟩ | ⟨-, h⟩
  · exact M.inN_mono hd h hβα
  · obtain ⟨α0, f0, u0, q00, d1, d2, ⟨k0, hk0⟩, dleast⟩ := hd.d_spec
    have h0β := dleast β (hd.hth.fld β α hβα).1
    rw [h]
    refine ⟨α0, f0, u0, q00, d1, d2, hd.hth.trans α0 β α h0β hβα, fun e1 => ?_, k0,
      (hd.io_dom _ _ hk0).1, hk0⟩
    rw [e1] at h0β
    exact hne (hd.hth.antisymm β α hβα h0β)

theorem isPairAt_restr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α ch pt : V}
    (q : M.mem (M.quad j.1 α ch pt) P) (hch : M.mem (M.op ch ch) nle)
    (hα : M.mem (M.op α α) th) {x y s : V} (hx : M.InNRaw P th io M.nat j.1 α x)
    (hy : M.InNRaw P th io M.nat j.1 α y) (hs : M.InNRaw P th io M.nat j.1 α s) :
    M.IsPairAt P th io M.nat j.1 tp (M.restr p F pt) α x y s ↔
      M.IsPairAt P th io M.nat j.1 tp F α x y s := by
  constructor
  · intro h z hz
    rw [← M.epsStar_restr hd q hch hα (Or.inl hz) (Or.inl hs), ← M.sim_restr hd q hch hα hz hx,
      ← M.sim_restr hd q hch hα hz hy]
    exact h z hz
  · intro h z hz
    rw [M.epsStar_restr hd q hch hα (Or.inl hz) (Or.inl hs), M.sim_restr hd q hch hα hz hx,
      M.sim_restr hd q hch hα hz hy]
    exact h z hz

theorem isOPairAt_restr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α ch pt : V}
    (q : M.mem (M.quad j.1 α ch pt) P) (hch : M.mem (M.op ch ch) nle)
    (hα : M.mem (M.op α α) th) {x y s : V} (hx : M.InNRaw P th io M.nat j.1 α x)
    (hy : M.InNRaw P th io M.nat j.1 α y) (hs : M.InNRaw P th io M.nat j.1 α s) :
    M.IsOPairAt P th io M.nat j.1 tp (M.restr p F pt) α x y s ↔
      M.IsOPairAt P th io M.nat j.1 tp F α x y s := by
  constructor
  · rintro ⟨s1, s2, h1, h2, h3, h4, h5⟩
    exact ⟨s1, s2, h1, h2, (M.isPairAt_restr hd q hch hα hx hx h1).mp h3,
      (M.isPairAt_restr hd q hch hα hx hy h2).mp h4, (M.isPairAt_restr hd q hch hα h1 h2 hs).mp h5⟩
  · rintro ⟨s1, s2, h1, h2, h3, h4, h5⟩
    exact ⟨s1, s2, h1, h2, (M.isPairAt_restr hd q hch hα hx hx h1).mpr h3,
      (M.isPairAt_restr hd q hch hα hx hy h2).mpr h4,
      (M.isPairAt_restr hd q hch hα h1 h2 hs).mpr h5⟩

/-- The clause for `T` reads the same from the part of `F` below a point of stage `α` and from
the whole of `F`. -/
theorem tRaw_restr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α ch pt : V}
    (q : M.mem (M.quad j.1 α ch pt) P) (hch : M.mem (M.op ch ch) nle)
    (hα : M.mem (M.op α α) th) (a b : V) :
    M.TRaw P th io M.nat Nt j.1 d tp qo Nu M.adG (M.restr p F pt) α a b ↔
      M.TRaw P th io M.nat Nt j.1 d tp qo Nu M.adG F α a b := by
  have truth : ∀ {β c t' : V}, M.mem (M.op β α) th → β ≠ α → M.mem c M.nat →
      ((∃ ch' pt', M.mem (M.op c ch') io ∧ M.mem (M.quad j.1 β ch' pt') P ∧
          M.mem (M.op pt' t') (M.restr p F pt)) ↔
        ∃ ch' pt', M.mem (M.op c ch') io ∧ M.mem (M.quad j.1 β ch' pt') P ∧
          M.mem (M.op pt' t') F) := by
    intro β c t' hβα hne hc
    constructor
    · rintro ⟨ch', pt', k1, k2, k3⟩
      exact ⟨ch', pt', k1, k2, (M.mem_restr.mp k3).1⟩
    · rintro ⟨ch', pt', k1, k2, k3⟩
      have hch' : M.mem (M.op ch' ch') nle :=
        (hd.nle_num ⟨c, hc⟩ ⟨c, hc⟩ ch' ch' k1 k1).mpr (le_refl _)
      have hbel := M.hier_below' hd q k2 hα (hd.hth.fld β α hβα).1 hch hch' (Or.inl ⟨hβα, hne⟩)
      exact ⟨ch', pt', k1, k2, M.mem_restr.mpr ⟨k3, hbel.1, hbel.2⟩⟩
  constructor
  · rintro ⟨ha, hb, β, c, ob, oc, t', g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩
    refine ⟨ha, hb, β, c, ob, oc, t', g1, g2, g3, g4, g5, g6, g7,
      (M.isOPairAt_restr hd q hch hα g6 g7 ha).mp g8, ?_, ?_, (truth g1 g2 g4).mp g11⟩
    · intro i hi hle oi y y' s s' k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
      exact (M.sim_restr hd q hch hα k3 k4).mp (g9 i hi hle oi y y' s s' k1 k2 k3 k4 k5 k6
        ((M.epsStar_restr hd q hch hα (Or.inl k5) (Or.inl hb)).mpr k7)
        ((M.isOPairAt_restr hd q hch hα k2 k3 k5).mpr k8)
        ((M.epsStar_restr hd q hch hα (Or.inl k6) (Or.inl hb)).mpr k9)
        ((M.isOPairAt_restr hd q hch hα k2 k4 k6).mpr k10))
    · intro i hi hle
      obtain ⟨oi, y, s, e, k1, k2, k3, k4, k5, k6, k7, k8⟩ := g10 i hi hle
      exact ⟨oi, y, s, e, k1, k2, k3, k4,
        (M.epsStar_restr hd q hch hα (Or.inl k4) (Or.inl hb)).mp k5,
        (M.isOPairAt_restr hd q hch hα k2 k3 k4).mp k6, k7,
        (M.sim_restr hd q hch hα k3 (M.val_inN_of_lt hd g1 g2 k7)).mp k8⟩
  · rintro ⟨ha, hb, β, c, ob, oc, t', g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩
    refine ⟨ha, hb, β, c, ob, oc, t', g1, g2, g3, g4, g5, g6, g7,
      (M.isOPairAt_restr hd q hch hα g6 g7 ha).mpr g8, ?_, ?_, (truth g1 g2 g4).mpr g11⟩
    · intro i hi hle oi y y' s s' k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
      exact (M.sim_restr hd q hch hα k3 k4).mpr (g9 i hi hle oi y y' s s' k1 k2 k3 k4 k5 k6
        ((M.epsStar_restr hd q hch hα (Or.inl k5) (Or.inl hb)).mp k7)
        ((M.isOPairAt_restr hd q hch hα k2 k3 k5).mp k8)
        ((M.epsStar_restr hd q hch hα (Or.inl k6) (Or.inl hb)).mp k9)
        ((M.isOPairAt_restr hd q hch hα k2 k4 k6).mp k10))
    · intro i hi hle
      obtain ⟨oi, y, s, e, k1, k2, k3, k4, k5, k6, k7, k8⟩ := g10 i hi hle
      exact ⟨oi, y, s, e, k1, k2, k3, k4,
        (M.epsStar_restr hd q hch hα (Or.inl k4) (Or.inl hb)).mpr k5,
        (M.isOPairAt_restr hd q hch hα k2 k3 k4).mpr k6, k7,
        (M.sim_restr hd q hch hα k3 (M.val_inN_of_lt hd g1 g2 k7)).mpr k8⟩

/-- The same for the clause for `<*`. -/
theorem ltRaw_restr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α ch pt : V}
    (q : M.mem (M.quad j.1 α ch pt) P) (hch : M.mem (M.op ch ch) nle)
    (hα : M.mem (M.op α α) th) (a b : V) :
    M.LtRaw P th io M.nat j.1 tp Pr (M.restr p F pt) α a b ↔
      M.LtRaw P th io M.nat j.1 tp Pr F α a b := by
  constructor
  · rintro ⟨ha, hb, a0, b0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    exact ⟨ha, hb, a0, b0, g1, g2, (M.sim_restr hd q hch hα ha g1).mp g3,
      (M.sim_restr hd q hch hα hb g2).mp g4,
      fun a' k1 k2 => g5 a' k1 ((M.sim_restr hd q hch hα k1 g1).mpr k2),
      fun b' k1 k2 => g6 b' k1 ((M.sim_restr hd q hch hα k1 g2).mpr k2), g7, g8⟩
  · rintro ⟨ha, hb, a0, b0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    exact ⟨ha, hb, a0, b0, g1, g2, (M.sim_restr hd q hch hα ha g1).mpr g3,
      (M.sim_restr hd q hch hα hb g2).mpr g4,
      fun a' k1 k2 => g5 a' k1 ((M.sim_restr hd q hch hα k1 g1).mp k2),
      fun b' k1 k2 => g6 b' k1 ((M.sim_restr hd q hch hα k1 g2).mp k2), g7, g8⟩

/-- The meaning of a relation symbol at stage `α`, for two values at that stage, reads the
same from the part of `F` below a point of stage `α` and from the whole of `F`. -/
theorem atomAt_restr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α ch pt : V}
    (q : M.mem (M.quad j.1 α ch pt) P) (hch : M.mem (M.op ch ch) nle)
    (hα : M.mem (M.op α α) th) {a b : V} (ha : M.InNRaw P th io M.nat j.1 α a ∨ a = d)
    (hb : M.InNRaw P th io M.nat j.1 α b ∨ b = d) (r : V) :
    M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG (1 : M.Num).1 (2 : M.Num).1
        (M.restr p F pt) α r a b ↔
      M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG (1 : M.Num).1 (2 : M.Num).1
        F α r a b := by
  unfold AtomAtRaw
  rw [M.epsStar_restr hd q hch hα ha hb, M.tRaw_restr hd q hch hα a b,
    M.ltRaw_restr hd q hch hα a b]

/-- **The atomic clause.** `r(v, w)` is true at stage `α` under `t` if and only if the
relation `r` holds at stage `α` between the values of `v` and `w`: `T` for `r = 1`, `<*` for
`r = 2`, and membership between the sets denoted otherwise. -/
theorem hier_rel (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V} (r v w : M.Num)
    (t : V) :
    M.TrueAt P io F j.1 α (M.cRel r v w) t ↔ M.mem (M.op α α) th ∧
      ∃ a b, M.ValRaw P th io M.nat Nt j.1 d α t v.1 a ∧ M.ValRaw P th io M.nat Nt j.1 d α t w.1 b ∧
        M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG (1 : M.Num).1 (2 : M.Num).1
          F α r.1 a b := by
  have vald : ∀ {i b : V}, M.ValRaw P th io M.nat Nt j.1 d α t i b →
      M.InNRaw P th io M.nat j.1 α b ∨ b = d := by
    rintro i b (⟨-, h⟩ | ⟨-, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  constructor
  · intro h
    have hα := M.trueAt_fld hd h
    refine ⟨hα, ?_⟩
    obtain ⟨ch, pt, hc, q, hpt⟩ := M.hier_pt hd hα (M.cRel r v w)
    have hnn : M.mem (M.op ch ch) nle := (hd.nle_num _ _ ch ch hc hc).mpr (le_refl _)
    have hF := (M.trueAt_iff hd q hc t).mp h
    have hier := (M.hier_unpack hd q hc _ t).mp ((hd.hF pt t).mp hF).2
    rcases hier with hA | hN | hC | hQ
    · obtain ⟨r1, v1, w1, p1, p2, hpr1, hpr2, hpr3, a, b, hva, hvb, heps⟩ := hA
      obtain ⟨Y, hY, e⟩ := (M.pairRaw_num 0 p1 (M.cRel r v w)).mp hpr1
      have e' : M.pairN 0 (M.pairN r (M.pairN v w)) = M.pairN 0 Y := e
      rw [← hY, ← (M.pairN_inj e').2] at hpr2
      obtain ⟨X1, X2, hX1, hX2, e2⟩ := (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mp hpr2
      obtain ⟨e3, e4⟩ := M.pairN_inj (Subtype.ext e2 : M.pairN r (M.pairN v w) = M.pairN X1 X2)
      rw [← hX2, ← e4] at hpr3
      obtain ⟨Z1, Z2, hZ1, hZ2, e5⟩ := (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mp hpr3
      obtain ⟨e6, e7⟩ := M.pairN_inj (Subtype.ext e5 : M.pairN v w = M.pairN Z1 Z2)
      rw [← hZ1, ← e6] at hva
      rw [← hZ2, ← e7] at hvb
      rw [← hX1, ← e3] at heps
      exact ⟨a, b, hva, hvb, (M.atomAt_restr hd q hnn hα (vald hva) (vald hvb) r.1).mp heps⟩
    · obtain ⟨c1, ch1, pt1, hpr, -⟩ := hN
      obtain ⟨Y, -, e⟩ := (M.pairRaw_num 1 c1 (M.cRel r v w)).mp hpr
      have e' : M.pairN 0 (M.pairN r (M.pairN v w)) = M.pairN 1 Y := e
      exact absurd (M.pairN_inj e').1 M.n01
    · obtain ⟨c1, c2, p0, ch1, ch2, pt1, pt2, hpr, -⟩ := hC
      obtain ⟨Y, -, e⟩ := (M.pairRaw_num 2 p0 (M.cRel r v w)).mp hpr
      have e' : M.pairN 0 (M.pairN r (M.pairN v w)) = M.pairN 2 Y := e
      exact absurd (M.pairN_inj e').1 M.n02
    · obtain ⟨v1, c1, p0, ch1, pt1, hpr, -⟩ := hQ
      obtain ⟨Y, -, e⟩ := (M.pairRaw_num 3 p0 (M.cRel r v w)).mp hpr
      have e' : M.pairN 0 (M.pairN r (M.pairN v w)) = M.pairN 3 Y := e
      exact absurd (M.pairN_inj e').1 M.n03
  · rintro ⟨hα, a, b, hva, hvb, heps⟩
    obtain ⟨ch, pt, hc, q, hpt⟩ := M.hier_pt hd hα (M.cRel r v w)
    have hnn : M.mem (M.op ch ch) nle := (hd.nle_num _ _ ch ch hc hc).mpr (le_refl _)
    refine (M.trueAt_iff hd q hc t).mpr ((hd.hF pt t).mpr ⟨hpt, (M.hier_unpack hd q hc _ t).mpr
      (Or.inl ⟨r.1, v.1, w.1, (M.pairN r (M.pairN v w)).1, (M.pairN v w).1,
        (M.pairRaw_num 0 _ (M.cRel r v w)).mpr ⟨M.pairN r (M.pairN v w), rfl, rfl⟩,
        (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mpr ⟨r, M.pairN v w, rfl, rfl, rfl⟩,
        (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mpr ⟨v, w, rfl, rfl, rfl⟩,
        a, b, hva, hvb, (M.atomAt_restr hd q hnn hα (vald hva) (vald hvb) r.1).mpr heps⟩)⟩)

/-- The atomic clause for a relation symbol other than `1`, `2`: membership between the sets
denoted by the values. -/
theorem hier_relE (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (r v w : M.Num) (hr1 : r ≠ 1) (hr2 : r ≠ 2) (t : V) :
    M.TrueAt P io F j.1 α (M.cRel r v w) t ↔ M.mem (M.op α α) th ∧
      ∃ a b, M.ValRaw P th io M.nat Nt j.1 d α t v.1 a ∧ M.ValRaw P th io M.nat Nt j.1 d α t w.1 b ∧
        M.EpsStarRaw P th io M.nat j.1 tp F a b := by
  have h1 : r.1 ≠ (1 : M.Num).1 := fun e => hr1 (Subtype.ext e)
  have h2 : r.1 ≠ (2 : M.Num).1 := fun e => hr2 (Subtype.ext e)
  rw [M.hier_rel hd]
  constructor
  · rintro ⟨hα, a, b, hva, hvb, ⟨-, -, h⟩ | ⟨e, -⟩ | ⟨e, -⟩⟩
    · exact ⟨hα, a, b, hva, hvb, h⟩
    · exact (h1 e).elim
    · exact (h2 e).elim
  · rintro ⟨hα, a, b, hva, hvb, h⟩
    exact ⟨hα, a, b, hva, hvb, Or.inl ⟨h1, h2, h⟩⟩

end hier2

/-- **The constructible hierarchy along a well-ordering exists** (§3.3, step 3, first part).
In a ladder with a pairing family, for every rung `j` and every nonempty set well-ordering
`th` of members of rung `j` there are numerals `io`, entries of sequences `Nt`, and a
solution `F` of the recursion, forming the data of the hierarchy (`HierData`). -/
theorem exists_hierData {R E z S P th : V} {m j : M.Num} (h : M.IsLadder R E z S m)
    (hP : M.IsPairing R P m) (hj : j ≤ m) (hth : M.IsWO th)
    (th_rung : ∀ a b, M.mem (M.op a b) th → M.mem (M.op j.1 a) R ∧ M.mem (M.op j.1 b) R)
    (hne : ∃ α, M.mem (M.op α α) th) (cq : M.Num) (Nst : V) :
    ∃ io Nt nle p F d tp qo Nu Pr, M.HierData R P th io Nt nle p F d tp qo Nu Pr m j ∧ M.IsWO p ∧
      (∀ t a, M.mem (M.trip t M.zero a) Nt ↔ ∃ t', M.mem (M.quad j.1 a t' t) P) ∧
      (∀ (n : M.Num) (t b : V), M.mem (M.trip t (n + 1).1 b) Nt ↔
        ∃ a t', M.mem (M.quad j.1 a t' t) P ∧ M.mem (M.trip t' n.1 b) Nt) ∧
      (∃ f, M.mem (M.op cq.1 f) io ∧ M.mem (M.quad j.1 f d qo) P) ∧
      (∀ k o, M.mem (M.op k o) Nu ↔ ∃ ξ, M.mem (M.op k ξ) Nst ∧ M.mem (M.quad j.1 ξ qo o) P) ∧
      M.IsPrec P th io Nt d Pr j := by
  obtain ⟨u, v, hu, hv, huv⟩ := M.rung_two h hj
  obtain ⟨io, io_dom, io_tot, io_fun, io_inj, io_shape⟩ := M.exists_numerals hP hj hu hv huv
  obtain ⟨Nt, hNd, hN0, hNs⟩ := M.exists_seq hP hj
  obtain ⟨nle0, hnle0WO, -, -, hnle0⟩ := M.wo_transport M.isWO_natLe io_fun io_inj
    (fun e he => by
      obtain ⟨x, -, hx, -, -⟩ := M.mem_natLe.mp he
      obtain ⟨a, ha⟩ := io_tot x
      rw [← hx]
      exact ⟨a, ha⟩)
  -- the top point
  obtain ⟨tp, htp⟩ := hP.tot j hj u v hu hv
  have tp_not_num : ∀ k, ¬ M.mem (M.op k tp) io := by
    intro k hk
    rcases io_shape k tp hk with h1 | ⟨x, h1⟩
    · exact huv (hP.inj _ _ _ _ _ _ h1 htp).2
    · exact huv (hP.inj _ _ _ _ _ _ h1 htp).1.symm
  have htpn : ¬ M.mem (M.op tp tp) nle0 := by
    intro h1
    obtain ⟨e, e', he, -, -⟩ := (hnle0 tp tp).mp h1
    exact tp_not_num e he
  obtain ⟨nle, hnle⟩ := M.exists_addTop nle0 tp
  have hnleWO := M.wo_addTop hnle0WO htpn hnle
  have nle_num : ∀ (c c' : M.Num) (a a' : V), M.mem (M.op c.1 a) io → M.mem (M.op c'.1 a') io →
      (M.mem (M.op a a') nle ↔ c ≤ c') := by
    intro c c' a a' hc hc'
    constructor
    · intro h1
      rcases (hnle a a').mp h1 with h0 | ⟨e, -⟩
      · obtain ⟨e, e', he, he', hle⟩ := (hnle0 a a').mp h0
        rw [io_inj _ _ _ he hc, io_inj _ _ _ he' hc'] at hle
        exact (M.natLe_iff c c').mp hle
      · rw [e] at hc'
        exact absurd hc' (tp_not_num _)
    · intro hle
      exact (hnle a a').mpr (Or.inl ((hnle0 a a').mpr
        ⟨c.1, c'.1, hc, hc', (M.natLe_iff c c').mpr hle⟩))
  have nle_top : ∀ a, M.mem (M.op a tp) nle ↔ (a = tp ∨ ∃ k, M.mem (M.op k a) io) := by
    intro a
    constructor
    · intro h1
      rcases (hnle a tp).mp h1 with h0 | ⟨-, h0 | h0⟩
      · obtain ⟨e, e', -, he', -⟩ := (hnle0 a tp).mp h0
        exact absurd he' (tp_not_num e')
      · obtain ⟨e, -, he, -, -⟩ := (hnle0 a a).mp h0
        exact Or.inr ⟨e, he⟩
      · exact Or.inl h0
    · rintro (e | ⟨k, hk⟩)
      · exact (hnle a tp).mpr (Or.inr ⟨rfl, Or.inr e⟩)
      · have hkn := (io_dom k a hk).1
        exact (hnle a tp).mpr (Or.inr ⟨rfl, Or.inl ((hnle0 a a).mpr
          ⟨k, k, hk, hk, (M.natLe_iff ⟨k, hkn⟩ ⟨k, hkn⟩).mpr (le_refl _)⟩)⟩)
  obtain ⟨p, hp⟩ := M.exists_lex P j.1 th nle
  have hpWO := (M.wo_lex hP hth hnleWO hp).1
  -- the default value: a name of least rank
  obtain ⟨D, -, hD⟩ := M.rung_set R j.1
  obtain ⟨α1, hα1⟩ := hne
  obtain ⟨α0, hα0D, hα0, hleast⟩ := hth.least D ⟨α1, (hD α1).mpr (th_rung α1 α1 hα1).1, hα1⟩
  obtain ⟨f0, hf0⟩ := io_tot 0
  obtain ⟨q00, hq00⟩ := hP.tot j hj f0 u (io_dom _ _ hf0).2 hu
  obtain ⟨d, hd⟩ := hP.tot j hj α0 q00 ((hD α0).mp hα0D) (hP.dom _ _ _ _ hq00).2.2.2
  -- the parameters of the two built-in predicates
  obtain ⟨fq, hfq⟩ := io_tot cq
  obtain ⟨qo, hqo⟩ := hP.tot j hj fq d (io_dom _ _ hfq).2 (hP.dom _ _ _ _ hd).2.2.2
  obtain ⟨Nu, -, hNu0⟩ := M.comp (σW [(0, 4), (1, 5), (3, 7)])
    (Fml.ex 8 (Fml.ex 9 (Fml.ex 60 (.and (fPr 0 8 9) (.and (fApp 1 8 60) (fApp4 3 5 60 6 9))))))
    0 rfl
    (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 1 Nst)
      3 P) 5 j.1) 6 qo)
  have hNu1 : ∀ t, M.mem t Nu ↔ ∃ k o ξ, t = M.op k o ∧ M.mem (M.op k ξ) Nst ∧
      M.mem (M.quad j.1 ξ qo o) P := by
    intro t
    rw [hNu0 t]
    simp [Sat, M.sat_ex, M.sat_fPr', M.sat_fApp', M.sat_fApp4', Function.update_apply]
  have hNu : ∀ k o, M.mem (M.op k o) Nu ↔ ∃ ξ, M.mem (M.op k ξ) Nst ∧
      M.mem (M.quad j.1 ξ qo o) P := by
    intro k o
    constructor
    · intro h1
      obtain ⟨k1, o1, ξ, e, h2⟩ := (hNu1 _).mp h1
      obtain ⟨e1, e2⟩ := M.op_inj e
      rw [e1, e2]
      exact ⟨ξ, h2⟩
    · rintro ⟨ξ, h2⟩
      exact (hNu1 _).mpr ⟨k, o, ξ, rfl, h2⟩
  obtain ⟨Pr, hPr⟩ := M.exists_precOrder hth P io Nt d j
  obtain ⟨F, hF⟩ := M.exists_hier hpWO P th io Nt j.1 d tp qo Nu Pr
  exact ⟨io, Nt, nle, p, F, d, tp, qo, Nu, Pr, ⟨hP, hj, hth, th_rung, io_dom, io_tot, io_fun,
    io_inj, hNd, hN0, hNs, nle_num, nle_top, tp_not_num, (hP.dom _ _ _ _ htp).2.2.2, hp,
    ⟨α0, f0, u, q00, hd, hq00, ⟨_, hf0⟩,
      fun α hα => hleast α ((hD α).mpr (th_rung α α hα).1) hα⟩, hF⟩,
    hpWO, hN0, hNs, ⟨fq, hfq, hqo⟩, hNu, hPr⟩

/-! ### First facts about the hierarchy: shapes, coincidence, membership -/

section hier3

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem eps_inN_rank (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {β a x G : V}
    (ra : M.RankIs P io M.nat j.1 β a) (h : M.EpsRaw P th io M.nat j.1 G x a) :
    M.InNRaw P th io M.nat j.1 β x := by
  obtain ⟨β1, f, u, q0, s, pt, h1, -, h3, -⟩ := h
  obtain ⟨f', u', q', k1, -⟩ := ra
  rw [(hd.hP.inj _ _ _ _ _ _ h1 k1).1] at h3
  exact h3

/-- **Denoting the same set.** For names `a`, `a'`: they denote the same set if and only if
every member of `a` denotes the same set as some member of `a'`, and conversely. -/
theorem hier_sim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a a' β β' : V}
    (ra : M.RankIs P io M.nat j.1 β a) (ra' : M.RankIs P io M.nat j.1 β' a')
    (hβ : M.mem (M.op β β) th) (hβ' : M.mem (M.op β' β') th) :
    M.SimRaw P j.1 tp F a a' ↔
      (∀ x, M.EpsRaw P th io M.nat j.1 F x a →
        ∃ x', M.EpsRaw P th io M.nat j.1 F x' a' ∧ M.SimRaw P j.1 tp F x x') ∧
      (∀ x', M.EpsRaw P th io M.nat j.1 F x' a' →
        ∃ x, M.EpsRaw P th io M.nat j.1 F x a ∧ M.SimRaw P j.1 tp F x x') := by
  have htt : M.mem (M.op tp tp) nle := (hd.nle_top tp).mpr (Or.inl rfl)
  -- reading from the part of `F` below a top point above both ranks
  have conv : ∀ {γ pg : V}, M.mem (M.quad j.1 γ tp pg) P → M.mem (M.op γ γ) th →
      M.mem (M.op β γ) th → M.mem (M.op β' γ) th →
      (∀ x, M.EpsRaw P th io M.nat j.1 (M.restr p F pg) x a ↔
        M.EpsRaw P th io M.nat j.1 F x a) ∧
      (∀ x', M.EpsRaw P th io M.nat j.1 (M.restr p F pg) x' a' ↔
        M.EpsRaw P th io M.nat j.1 F x' a') ∧
      ∀ x x', M.EpsRaw P th io M.nat j.1 F x a → M.EpsRaw P th io M.nat j.1 F x' a' →
        (M.SimRaw P j.1 tp (M.restr p F pg) x x' ↔ M.SimRaw P j.1 tp F x x') := by
    intro γ pg qg hγ hle hle'
    exact ⟨fun x => M.eps_restr_top hd qg hγ ra hle, fun x' => M.eps_restr_top hd qg hγ ra' hle',
      fun x x' hx hx' => M.sim_restr hd qg htt hγ
        (M.inN_mono hd (M.eps_inN_rank hd ra hx) hle)
        (M.inN_mono hd (M.eps_inN_rank hd ra' hx') hle')⟩
  constructor
  · rintro ⟨γ1, pg1, y1, g1, g2, g3⟩
    obtain ⟨-, hier⟩ := (hd.hF pg1 y1).mp g3
    obtain ⟨a1, a1', b1, b1', s1, r1, r2, l1, l2, -, fwd, bwd⟩ :=
      (M.hier_unpack_top hd g1 _ y1).mp hier
    obtain ⟨e1, e2⟩ := hd.hP.inj _ _ _ _ _ _ s1 g2
    rw [e1] at r1 fwd bwd
    rw [e2] at r2 fwd bwd
    rw [M.rank_unique hd r1 ra] at l1
    rw [M.rank_unique hd r2 ra'] at l2
    obtain ⟨E1, E2, S⟩ := conv g1 (hd.hth.fld β γ1 l1).2 l1 l2
    constructor
    · intro x hx
      obtain ⟨x', hx', hs⟩ := fwd x ((E1 x).mpr hx)
      exact ⟨x', (E2 x').mp hx', (S x x' hx ((E2 x').mp hx')).mp hs⟩
    · intro x' hx'
      obtain ⟨x, hx, hs⟩ := bwd x' ((E2 x').mpr hx')
      exact ⟨x, (E1 x).mp hx, (S x x' ((E1 x).mp hx) hx').mp hs⟩
  · rintro ⟨fwd, bwd⟩
    obtain ⟨γ, hγ, hle, hle', hmax⟩ : ∃ γ, M.mem (M.op γ γ) th ∧ M.mem (M.op β γ) th ∧
        M.mem (M.op β' γ) th ∧ (β = γ ∨ β' = γ) := by
      rcases M.wo_total hd.hth hβ hβ' with h | h
      · exact ⟨β', hβ', h, hβ', Or.inr rfl⟩
      · exact ⟨β, hβ, hβ, h, Or.inl rfl⟩
    obtain ⟨pg, qg, hpg⟩ := M.hier_pt_top hd hγ
    have hra := ra
    have hra' := ra'
    obtain ⟨f, u, q, k1, -⟩ := hra
    obtain ⟨f', u', q', k1', -⟩ := hra'
    obtain ⟨y, hy⟩ := hd.hP.tot j hd.hj a a' (hd.hP.dom _ _ _ _ k1).2.2.2
      (hd.hP.dom _ _ _ _ k1').2.2.2
    obtain ⟨E1, E2, S⟩ := conv qg hγ hle hle'
    refine ⟨γ, pg, y, qg, hy, (hd.hF pg y).mpr ⟨hpg, (M.hier_unpack_top hd qg _ y).mpr
      ⟨a, a', β, β', hy, ra, ra', hle, hle', hmax, fun x hx => ?_, fun x' hx' => ?_⟩⟩⟩
    · have hxF := (E1 x).mp hx
      obtain ⟨x', hx', hs⟩ := fwd x hxF
      exact ⟨x', (E2 x').mpr hx', (S x x' hxF hx').mpr hs⟩
    · have hxF' := (E2 x').mp hx'
      obtain ⟨x, hx, hs⟩ := bwd x' hxF'
      exact ⟨x, (E1 x).mpr hx, (S x x' hx hxF').mpr hs⟩

/-- A formula that is true somewhere has one of the four shapes. -/
theorem trueAt_shape (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V} {c : M.Num} {t : V}
    (h : M.TrueAt P io F j.1 α c t) :
    (∃ r v w, c = M.cRel r v w) ∨ (∃ c', c = M.cNeg c') ∨ (∃ c' c'', c = M.cAnd c' c'') ∨
      ∃ v c', c = M.cAll v c' := by
  have hα := M.trueAt_fld hd h
  obtain ⟨ch, pt, hc, q, hpt⟩ := M.hier_pt hd hα c
  have hF := (M.trueAt_iff hd q hc t).mp h
  rcases (M.hier_unpack hd q hc _ t).mp ((hd.hF pt t).mp hF).2 with hA | hN | hC | hQ
  · obtain ⟨r1, v1, w1, p1, p2, hpr1, hpr2, hpr3, -⟩ := hA
    obtain ⟨Y, hY, e⟩ := (M.pairRaw_num 0 p1 c).mp hpr1
    rw [← hY] at hpr2
    obtain ⟨X1, X2, -, hX2, e2⟩ := (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mp hpr2
    rw [← hX2] at hpr3
    obtain ⟨Z1, Z2, -, -, e5⟩ := (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mp hpr3
    refine Or.inl ⟨X1, Z1, Z2, ?_⟩
    rw [e, Subtype.ext e2, Subtype.ext e5]
    rfl
  · obtain ⟨c1, ch1, pt1, hpr, -⟩ := hN
    obtain ⟨Y, -, e⟩ := (M.pairRaw_num 1 c1 c).mp hpr
    exact Or.inr (Or.inl ⟨Y, e⟩)
  · obtain ⟨c1, c2, p0, ch1, ch2, pt1, pt2, hpr, hpr2, -⟩ := hC
    obtain ⟨Y, hY, e⟩ := (M.pairRaw_num 2 p0 c).mp hpr
    rw [← hY] at hpr2
    obtain ⟨X1, X2, -, -, e2⟩ := (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mp hpr2
    refine Or.inr (Or.inr (Or.inl ⟨X1, X2, ?_⟩))
    rw [e, Subtype.ext e2]
    rfl
  · obtain ⟨v1, c1, p0, ch1, pt1, hpr, hpr2, -⟩ := hQ
    obtain ⟨Y, hY, e⟩ := (M.pairRaw_num 3 p0 c).mp hpr
    rw [← hY] at hpr2
    obtain ⟨X1, X2, -, -, e2⟩ := (M.pairRaw_iff M.adG_spec M.muG_spec _ _ _).mp hpr2
    refine Or.inr (Or.inr (Or.inr ⟨X1, X2, ?_⟩))
    rw [e, Subtype.ext e2]
    rfl

/-- The step of the coincidence lemma. -/
theorem coin_hier_core (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V} (c : M.Num)
    (ih : ∀ c' : M.Num, c' + 1 ≤ c → ∀ t t', (∀ i : M.Num, i ≤ c' → ∀ e,
      (M.ValRaw P th io M.nat Nt j.1 d α t i.1 e ↔ M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e)) →
      M.TrueAt P io F j.1 α c' t → M.TrueAt P io F j.1 α c' t')
    (t t' : V) (hag : ∀ i : M.Num, i ≤ c → ∀ e,
      (M.ValRaw P th io M.nat Nt j.1 d α t i.1 e ↔ M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e))
    (h : M.TrueAt P io F j.1 α c t) : M.TrueAt P io F j.1 α c t' := by
  rcases M.trueAt_shape hd h with ⟨r, v, w, e⟩ | ⟨c', e⟩ | ⟨c', c'', e⟩ | ⟨v, c', e⟩
  · rw [e] at h hag ⊢
    obtain ⟨hα, a, b, hva, hvb, heps⟩ := (M.hier_rel hd r v w t).mp h
    have hvw : M.pairN v w ≤ M.cRel r v w :=
      le_trans (M.le_pairN_right r _) (M.le_pairN_right 0 _)
    exact (M.hier_rel hd r v w t').mpr ⟨hα, a, b,
      (hag v (le_trans (M.le_pairN_left v w) hvw) a).mp hva,
      (hag w (le_trans (M.le_pairN_right v w) hvw) b).mp hvb, heps⟩
  · rw [e] at h hag ⊢
    obtain ⟨hα, hnot⟩ := (M.hier_neg hd c' t).mp h
    have lt1 : c' + 1 ≤ M.cNeg c' := M.lt_pairN_right c' (le_refl 1)
    refine (M.hier_neg hd c' t').mpr ⟨hα, fun h' => hnot ?_⟩
    exact ih c' (by rw [e]; exact lt1) t' t (fun i hi e' =>
      (hag i (le_trans hi (le_trans (M.le_add_one c') lt1)) e').symm) h'
  · rw [e] at h hag ⊢
    obtain ⟨hα, h1, h2⟩ := (M.hier_and hd c' c'' t).mp h
    have lt1 : c' + 1 ≤ M.cAnd c' c'' :=
      le_trans (add_le_add (M.le_pairN_left c' c'') (le_refl 1))
        (M.lt_pairN_right _ M.one_le_two')
    have lt2 : c'' + 1 ≤ M.cAnd c' c'' :=
      le_trans (add_le_add (M.le_pairN_right c' c'') (le_refl 1))
        (M.lt_pairN_right _ M.one_le_two')
    exact (M.hier_and hd c' c'' t').mpr ⟨hα,
      ih c' (by rw [e]; exact lt1) t t' (fun i hi e' =>
        hag i (le_trans hi (le_trans (M.le_add_one c') lt1)) e') h1,
      ih c'' (by rw [e]; exact lt2) t t' (fun i hi e' =>
        hag i (le_trans hi (le_trans (M.le_add_one c'') lt2)) e') h2⟩
  · rw [e] at h hag ⊢
    obtain ⟨hα, hall⟩ := (M.hier_all hd v c' t).mp h
    refine (M.hier_all hd v c' t').mpr ⟨hα, fun a t'' ha hagr => hall a t'' ha ?_⟩
    intro i hi hle e'
    rw [hagr i hi hle e']
    have hiN : (⟨i, hi⟩ : M.Num) ≤ M.cAll v c' := by
      obtain ⟨x, hx, htr⟩ := hle
      exact M.le_def.mpr ⟨⟨x, hx⟩, Subtype.ext (M.graph₂_val M.adG_spec
        (m := ⟨i, hi⟩) (n := ⟨x, hx⟩) htr).symm⟩
    exact or_congr Iff.rfl (and_congr Iff.rfl (hag ⟨i, hi⟩ hiN e').symm)

end hier3

/-- "Coincidence up to `n`" (name `99`) at stage `α` (name `65`), with `F` the name `6`. -/
def coinHFml : Fml :=
  .all 83 (Fml.imp (.mem 83 27) (Fml.imp (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 83 84 99)))
    (.all 80 (.all 81 (Fml.imp
      (.all 67 (Fml.imp (.mem 67 27) (Fml.imp (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 67 84 83)))
        (.all 68 (Fml.iff (Fml.ex 66 (.and (.eq 66 80) valFml))
          (Fml.ex 66 (.and (.eq 66 81) valFml)))))))
      (Fml.imp (Fml.ex 85 (Fml.ex 86 (.and (fApp 24 83 85) (.and (fApp4 20 25 65 85 86)
          (fApp 6 86 80)))))
        (Fml.ex 85 (Fml.ex 86 (.and (fApp 24 83 85) (.and (fApp4 20 25 65 85 86)
          (fApp 6 86 81)))))))))))

section hier4

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **Coincidence.** The truth of a formula at a stage depends only on the values of the
variables up to its code. -/
theorem coin_hier (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V} (c : M.Num) (t t' : V)
    (hag : ∀ i : M.Num, i ≤ c → ∀ e,
      (M.ValRaw P th io M.nat Nt j.1 d α t i.1 e ↔ M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e)) :
    M.TrueAt P io F j.1 α c t ↔ M.TrueAt P io F j.1 α c t' := by
  have had := M.adG_spec
  have hsat : ∀ n : M.Num, Sat M.mem M.isSet coinHFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (fun _ => dflt)
      6 F) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 65 α) 99 n.1) ↔
      ∀ c : M.Num, c ≤ n → ∀ t t', (∀ i : M.Num, i ≤ c → ∀ e,
        (M.ValRaw P th io M.nat Nt j.1 d α t i.1 e ↔
          M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e)) →
        M.TrueAt P io F j.1 α c t → M.TrueAt P io F j.1 α c t' := by
    intro n
    have h1 : Sat M.mem M.isSet coinHFml (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (fun _ => dflt)
        6 F) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 65 α) 99 n.1) ↔
        ∀ c, M.mem c M.nat → M.LeRaw M.adG c n.1 → ∀ t t',
          (∀ i, M.mem i M.nat → M.LeRaw M.adG i c → ∀ e,
            (M.ValRaw P th io M.nat Nt j.1 d α t i e ↔
              M.ValRaw P th io M.nat Nt j.1 d α t' i e)) →
          (∃ ch pt, M.mem (M.op c ch) io ∧ M.mem (M.quad j.1 α ch pt) P ∧ M.mem (M.op pt t) F) →
          ∃ ch pt, M.mem (M.op c ch) io ∧ M.mem (M.quad j.1 α ch pt) P ∧
            M.mem (M.op pt t') F := by
      simp [coinHFml, LeRaw, Sat, M.sat_imp, M.sat_iff, M.sat_ex, M.sat_fApp3', M.sat_fApp4',
        M.sat_fApp', M.sat_valFml, Function.update_apply]
    rw [h1]
    constructor
    · intro raw c hc t t' hag htr
      exact raw c.1 c.2 ((M.leRaw_iff had c n).mpr hc) t t'
        (fun i hi hle e => hag ⟨i, hi⟩ ((M.leRaw_iff had ⟨i, hi⟩ c).mp hle) e) htr
    · intro clean c hc hle t t' hag htr
      exact clean ⟨c, hc⟩ ((M.leRaw_iff had ⟨c, hc⟩ n).mp hle) t t'
        (fun i hi e => hag i.1 i.2 ((M.leRaw_iff had i ⟨c, hc⟩).mpr hi) e) htr
  have key := M.num_ind_fml (σW [(6, 5), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7)])
    coinHFml 99 rfl (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt)
      6 F) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG) 65 α)
    (by
      rw [show M.zero = (0 : M.Num).1 from rfl, hsat 0]
      intro c0 hc0 t0 t0' hag0 htr0
      exact M.coin_hier_core hd c0 (fun c' hc' => absurd (le_trans hc' hc0)
        (fun h => M.succ_not_le_zero h)) t0 t0' hag0 htr0)
    (fun k ih => by
      rw [hsat k] at ih
      rw [show M.succ k.1 = (k + 1).1 from (M.val_add_one k).symm, hsat (k + 1)]
      intro c0 hc0 t0 t0' hag0 htr0
      exact M.coin_hier_core hd c0 (fun c' hc' =>
        ih c' (M.le_of_succ_le_succ (le_trans hc' hc0))) t0 t0' hag0 htr0) c
  rw [hsat c] at key
  exact ⟨key c (le_refl c) t t' hag, key c (le_refl c) t' t (fun i hi e => (hag i hi e).symm)⟩

/-- **Membership in a name.** The members of the name `(β, (φ̂, u))` are the names `a` of rank
below `β` such that `φ` is true at stage `β` under the sequence `(a, u)`: the name denotes a
subset of the earlier names defined over them by `φ` with the parameters `u`. -/
theorem eps_iff (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {β f u q b : V} {φ : M.Num}
    (hq : M.mem (M.quad j.1 β q b) P) (hfu : M.mem (M.quad j.1 f u q) P)
    (hφ : M.mem (M.op φ.1 f) io) (a : V) :
    M.EpsRaw P th io M.nat j.1 F a b ↔ M.InNRaw P th io M.nat j.1 β a ∧
      ∃ s, M.mem (M.quad j.1 a u s) P ∧ M.TrueAt P io F j.1 β φ s := by
  constructor
  · rintro ⟨β1, f1, u1, q1, s, pt, h1, h2, h3, h4, h5, h6⟩
    obtain ⟨e1, e2⟩ := hd.hP.inj _ _ _ _ _ _ h1 hq
    rw [e2] at h2
    obtain ⟨e3, e4⟩ := hd.hP.inj _ _ _ _ _ _ h2 hfu
    rw [e1] at h3 h5
    rw [e3] at h5
    rw [e4] at h4
    exact ⟨h3, s, h4, f, pt, hφ, h5, h6⟩
  · rintro ⟨h3, s, h4, ch, pt, hch, h5, h6⟩
    rw [hd.io_fun _ _ _ hch hφ] at h5
    exact ⟨β, f, u, q, s, pt, hq, hfu, h3, h4, h5, h6⟩

end hier4

/-! ### "Denote the same set" is an equivalence relation -/

section hier5

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- Two things that denote the same set are names, with ranks in `th`. -/
theorem sim_names (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a a' : V}
    (h : M.SimRaw P j.1 tp F a a') :
    ∃ β β', M.RankIs P io M.nat j.1 β a ∧ M.RankIs P io M.nat j.1 β' a' ∧ M.mem (M.op β β) th ∧
      M.mem (M.op β' β') th := by
  obtain ⟨γ, pg, y, g1, g2, g3⟩ := h
  obtain ⟨-, hier⟩ := (hd.hF pg y).mp g3
  obtain ⟨a1, a1', β, β', s1, r1, r2, l1, l2, -⟩ := (M.hier_unpack_top hd g1 _ y).mp hier
  obtain ⟨e1, e2⟩ := hd.hP.inj _ _ _ _ _ _ s1 g2
  rw [e1] at r1
  rw [e2] at r2
  exact ⟨β, β', r1, r2, (hd.hth.fld β γ l1).1, (hd.hth.fld β' γ l2).1⟩

/-- **Reflexivity.** Every name denotes the same set as itself. -/
theorem sim_refl (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {β a : V}
    (ra : M.RankIs P io M.nat j.1 β a) (hβ : M.mem (M.op β β) th) : M.SimRaw P j.1 tp F a a := by
  obtain ⟨B, -, hB0⟩ := M.comp (σW [(6, 5), (20, 7), (22, 5), (24, 5), (27, 3)])
    (.and (fApp 22 74 74) (Fml.ex 72 (.and rankFml (.neg (Fml.ex 94 (.and (.eq 94 72)
      (Fml.ex 95 (.and (.eq 95 72) simFml)))))))) 74 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th) 24 io) 25 j.1)
      27 M.nat)
  have hB : ∀ β, M.mem β B ↔ M.mem (M.op β β) th ∧ ∃ a, M.RankIs P io M.nat j.1 β a ∧
      ¬ M.SimRaw P j.1 tp F a a := by
    intro β
    rw [hB0 β]
    simp [Sat, M.sat_ex, M.sat_fApp', M.sat_rankFml, M.sat_simFml, Function.update_apply]
  by_contra hn
  obtain ⟨β0, hβ0B, hβ0, hmin⟩ := hd.hth.least B ⟨β, (hB β).mpr ⟨hβ, a, ra, hn⟩, hβ⟩
  obtain ⟨-, a0, ra0, hn0⟩ := (hB β0).mp hβ0B
  have key : ∀ x, M.EpsRaw P th io M.nat j.1 F x a0 → M.SimRaw P j.1 tp F x x := by
    intro x hx
    obtain ⟨βx, rx, ltx, nex⟩ := M.inN_rank (M.eps_inN_rank hd ra0 hx)
    by_contra hnx
    exact nex (hd.hth.antisymm βx β0 ltx (hmin βx ((hB βx).mpr
      ⟨(hd.hth.fld βx β0 ltx).1, x, rx, hnx⟩) (hd.hth.fld βx β0 ltx).1))
  exact hn0 ((M.hier_sim hd ra0 ra0 hβ0 hβ0).mpr
    ⟨fun x hx => ⟨x, hx, key x hx⟩, fun x hx => ⟨x, hx, key x hx⟩⟩)

/-- **Symmetry.** -/
theorem sim_symm (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a a' : V}
    (h : M.SimRaw P j.1 tp F a a') : M.SimRaw P j.1 tp F a' a := by
  obtain ⟨β, β', ra, ra', hβ, hβ'⟩ := M.sim_names hd h
  obtain ⟨B, -, hB0⟩ := M.comp (σW [(6, 5), (20, 7), (22, 5), (24, 5), (27, 3)])
    (.and (fApp 22 74 74) (Fml.ex 72 (.and rankFml (Fml.ex 87
      (.and (Fml.ex 94 (.and (.eq 94 72) (Fml.ex 95 (.and (.eq 95 87) simFml))))
        (.neg (Fml.ex 94 (.and (.eq 94 87) (Fml.ex 95 (.and (.eq 95 72) simFml)))))))))) 74 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th) 24 io) 25 j.1)
      27 M.nat)
  have hB : ∀ β, M.mem β B ↔ M.mem (M.op β β) th ∧ ∃ a, M.RankIs P io M.nat j.1 β a ∧
      ∃ a', M.SimRaw P j.1 tp F a a' ∧ ¬ M.SimRaw P j.1 tp F a' a := by
    intro β
    rw [hB0 β]
    simp [Sat, M.sat_ex, M.sat_fApp', M.sat_rankFml, M.sat_simFml, Function.update_apply]
  by_contra hn
  obtain ⟨β0, hβ0B, hβ0, hmin⟩ := hd.hth.least B ⟨β, (hB β).mpr ⟨hβ, a, ra, a', h, hn⟩, hβ⟩
  obtain ⟨-, a0, ra0, a0', h0, hn0⟩ := (hB β0).mp hβ0B
  obtain ⟨b0, b0', -, ra0', -, hb0'⟩ := M.sim_names hd h0
  have low : ∀ x x', M.EpsRaw P th io M.nat j.1 F x a0 → M.SimRaw P j.1 tp F x x' →
      M.SimRaw P j.1 tp F x' x := by
    intro x x' hx hs
    obtain ⟨βx, rx, ltx, nex⟩ := M.inN_rank (M.eps_inN_rank hd ra0 hx)
    by_contra hns
    exact nex (hd.hth.antisymm βx β0 ltx (hmin βx ((hB βx).mpr
      ⟨(hd.hth.fld βx β0 ltx).1, x, rx, x', hs, hns⟩) (hd.hth.fld βx β0 ltx).1))
  obtain ⟨fwd, bwd⟩ := (M.hier_sim hd ra0 ra0' hβ0 hb0').mp h0
  refine hn0 ((M.hier_sim hd ra0' ra0 hb0' hβ0).mpr ⟨fun x' hx' => ?_, fun x hx => ?_⟩)
  · obtain ⟨x, hx, hs⟩ := bwd x' hx'
    exact ⟨x, hx, low x x' hx hs⟩
  · obtain ⟨x', hx', hs⟩ := fwd x hx
    exact ⟨x', hx', low x x' hx hs⟩

/-- **Transitivity.** -/
theorem sim_trans (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a a' a'' : V}
    (h : M.SimRaw P j.1 tp F a a') (h' : M.SimRaw P j.1 tp F a' a'') :
    M.SimRaw P j.1 tp F a a'' := by
  obtain ⟨β, β', ra, ra', hβ, hβ'⟩ := M.sim_names hd h
  obtain ⟨B, -, hB0⟩ := M.comp (σW [(6, 5), (20, 7), (22, 5), (24, 5), (27, 3)])
    (.and (fApp 22 74 74) (Fml.ex 72 (.and rankFml (Fml.ex 87 (Fml.ex 90
      (.and (Fml.ex 94 (.and (.eq 94 72) (Fml.ex 95 (.and (.eq 95 87) simFml))))
      (.and (Fml.ex 94 (.and (.eq 94 87) (Fml.ex 95 (.and (.eq 95 90) simFml))))
        (.neg (Fml.ex 94 (.and (.eq 94 72) (Fml.ex 95 (.and (.eq 95 90) simFml))))))))))))
    74 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th) 24 io) 25 j.1)
      27 M.nat)
  have hB : ∀ β, M.mem β B ↔ M.mem (M.op β β) th ∧ ∃ a, M.RankIs P io M.nat j.1 β a ∧
      ∃ a' a'', M.SimRaw P j.1 tp F a a' ∧ M.SimRaw P j.1 tp F a' a'' ∧
        ¬ M.SimRaw P j.1 tp F a a'' := by
    intro β
    rw [hB0 β]
    simp [Sat, M.sat_ex, M.sat_fApp', M.sat_rankFml, M.sat_simFml, Function.update_apply]
  by_contra hn
  obtain ⟨β0, hβ0B, hβ0, hmin⟩ := hd.hth.least B
    ⟨β, (hB β).mpr ⟨hβ, a, ra, a', a'', h, h', hn⟩, hβ⟩
  obtain ⟨-, a0, ra0, a1, a2, h01, h12, hn02⟩ := (hB β0).mp hβ0B
  obtain ⟨-, b1, -, ra1, -, hb1⟩ := M.sim_names hd h01
  obtain ⟨-, b2, -, ra2, -, hb2⟩ := M.sim_names hd h12
  have low : ∀ x x' x'', M.EpsRaw P th io M.nat j.1 F x a0 → M.SimRaw P j.1 tp F x x' →
      M.SimRaw P j.1 tp F x' x'' → M.SimRaw P j.1 tp F x x'' := by
    intro x x' x'' hx hs hs'
    obtain ⟨βx, rx, ltx, nex⟩ := M.inN_rank (M.eps_inN_rank hd ra0 hx)
    by_contra hns
    exact nex (hd.hth.antisymm βx β0 ltx (hmin βx ((hB βx).mpr
      ⟨(hd.hth.fld βx β0 ltx).1, x, rx, x', x'', hs, hs', hns⟩) (hd.hth.fld βx β0 ltx).1))
  obtain ⟨fwd01, bwd01⟩ := (M.hier_sim hd ra0 ra1 hβ0 hb1).mp h01
  obtain ⟨fwd12, bwd12⟩ := (M.hier_sim hd ra1 ra2 hb1 hb2).mp h12
  refine hn02 ((M.hier_sim hd ra0 ra2 hβ0 hb2).mpr ⟨fun x hx => ?_, fun x'' hx'' => ?_⟩)
  · obtain ⟨x', hx', hs⟩ := fwd01 x hx
    obtain ⟨x'', hx'', hs'⟩ := fwd12 x' hx'
    exact ⟨x'', hx'', low x x' x'' hx hs hs'⟩
  · obtain ⟨x', hx', hs'⟩ := bwd12 x'' hx''
    obtain ⟨x, hx, hs⟩ := bwd01 x' hx'
    exact ⟨x, hx, low x x' x'' hx hs hs'⟩

end hier5

/-! ### Values, updated sequences, and invariance of truth -/

section hier6

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- The value of a variable is unique. -/
theorem val_unique (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t i e e' : V}
    (h : M.ValRaw P th io M.nat Nt j.1 d α t i e) (h' : M.ValRaw P th io M.nat Nt j.1 d α t i e') :
    e = e' := by
  have nfun : ∀ a a', M.mem (M.trip t i a) Nt → M.mem (M.trip t i a') Nt → a = a' := by
    intro a a' k1 k2
    have hi := (hd.nt_dom t i a k1).1
    exact M.nth_fun hd.hP hd.nt_zero hd.nt_succ ⟨i, hi⟩ t a a' k1 k2
  rcases h with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · rcases h' with ⟨k1', -⟩ | ⟨k1', -⟩
    · exact nfun e e' k1 k1'
    · exact absurd ⟨e, k1, k2⟩ k1'
  · rcases h' with ⟨k1', k2'⟩ | ⟨-, k2'⟩
    · exact absurd ⟨e', k1', k2'⟩ k1
    · rw [k2, k2']

/-- Every variable has a value. -/
theorem val_exists (α t i : V) : ∃ e, M.ValRaw P th io M.nat Nt j.1 d α t i e := by
  by_cases h : ∃ e, M.mem (M.trip t i e) Nt ∧ M.InNRaw P th io M.nat j.1 α e
  · obtain ⟨e, h1, h2⟩ := h
    exact ⟨e, Or.inl ⟨h1, h2⟩⟩
  · exact ⟨d, Or.inr ⟨h, rfl⟩⟩

/-- The value at an entry of a sequence. -/
theorem val_of_nth (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t i e : V}
    (h : M.mem (M.trip t i e) Nt) :
    (M.InNRaw P th io M.nat j.1 α e ∧ M.ValRaw P th io M.nat Nt j.1 d α t i e) ∨
    (¬ M.InNRaw P th io M.nat j.1 α e ∧ M.ValRaw P th io M.nat Nt j.1 d α t i d) := by
  by_cases hN : M.InNRaw P th io M.nat j.1 α e
  · exact Or.inl ⟨hN, Or.inl ⟨h, hN⟩⟩
  · refine Or.inr ⟨hN, Or.inr ⟨?_, rfl⟩⟩
    rintro ⟨e2, k1, k2⟩
    have hi := (hd.nt_dom t i e h).1
    rw [M.nth_fun hd.hP hd.nt_zero hd.nt_succ ⟨i, hi⟩ t e2 e k1 h] at k2
    exact hN k2

theorem d_rung (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) : M.mem (M.op j.1 d) R := by
  obtain ⟨α0, f0, u0, q00, d1, -⟩ := hd.d_spec
  exact (hd.hP.dom _ _ _ _ d1).2.2.2

theorem inN_rung (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α a : V}
    (h : M.InNRaw P th io M.nat j.1 α a) : M.mem (M.op j.1 a) R := by
  obtain ⟨β, f, u, q, h1, -⟩ := h
  exact (hd.hP.dom _ _ _ _ h1).2.2.2

/-- **The sequence with one variable changed exists**: for every `t`, every variable `v`,
every name `a` of rank below `α` and every bound `c` there is a `t'` whose values at the
variables up to `c` are those of `t`, except that its value at `v` is `a`. -/
theorem exists_updR (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α a : V}
    (ha : M.InNRaw P th io M.nat j.1 α a) (t v : V) (c : M.Num) :
    ∃ t', M.mem (M.op j.1 t') R ∧ M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v a c.1 := by
  obtain ⟨g, -, hg0⟩ := M.comp (σW [(0, 4), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3)])
    (Fml.ex 67 (Fml.ex 68 (.and (fPr 0 67 68) (.and (.mem 67 27)
      (Fml.or (.and (.eq 67 81) (.eq 68 82))
        (.and (.neg (.eq 67 81)) (Fml.ex 66 (.and (.eq 66 5) valFml)))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (fun _ => dflt) 5 t) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat)
      65 α) 81 v) 82 a)
  have hg1 : ∀ q, M.mem q g ↔ ∃ i e, q = M.op i e ∧ M.mem i M.nat ∧
      ((i = v ∧ e = a) ∨ (i ≠ v ∧ M.ValRaw P th io M.nat Nt j.1 d α t i e)) := by
    intro q
    rw [hg0 q]
    simp [Sat, M.sat_ex, M.sat_or, M.sat_fPr', M.sat_valFml, Function.update_apply]
  have hg : ∀ i e, M.mem (M.op i e) g ↔ M.mem i M.nat ∧
      ((i = v ∧ e = a) ∨ (i ≠ v ∧ M.ValRaw P th io M.nat Nt j.1 d α t i e)) := by
    intro i e
    constructor
    · intro h
      obtain ⟨i', e', eq, h'⟩ := (hg1 _).mp h
      obtain ⟨e1, e2⟩ := M.op_inj eq
      rw [e1, e2]
      exact h'
    · intro h
      exact (hg1 _).mpr ⟨i, e, rfl, h⟩
  have hvalR : ∀ {i e : V}, M.ValRaw P th io M.nat Nt j.1 d α t i e → M.mem (M.op j.1 e) R := by
    rintro i e (⟨-, h⟩ | ⟨-, h⟩)
    · exact M.inN_rung hd h
    · rw [h]
      exact M.d_rung hd
  obtain ⟨t', ht'R, hcode⟩ := M.seq_code hd.hP hd.hj ⟨d, M.d_rung hd⟩ hd.nt_zero hd.nt_succ
    (c + 1) g (fun k _ => by
      by_cases e : k.1 = v
      · exact ⟨a, M.inN_rung hd ha, (hg k.1 a).mpr ⟨k.2, Or.inl ⟨e, rfl⟩⟩⟩
      · obtain ⟨e0, he0⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d)
          (j := j) α t k.1
        exact ⟨e0, hvalR he0, (hg k.1 e0).mpr ⟨k.2, Or.inr ⟨e, he0⟩⟩⟩)
  refine ⟨t', ht'R, fun i hi hle e' => ?_⟩
  have hiN : (⟨i, hi⟩ : M.Num) + 1 ≤ c + 1 := by
    obtain ⟨x, hx, htr⟩ := hle
    exact add_le_add (M.le_def.mpr ⟨⟨x, hx⟩, Subtype.ext (M.graph₂_val M.adG_spec
      (m := ⟨i, hi⟩) (n := ⟨x, hx⟩) htr).symm⟩) (le_refl 1)
  obtain ⟨e, hge, hnt⟩ := hcode ⟨i, hi⟩ hiN
  obtain ⟨-, hcase⟩ := (hg i e).mp hge
  -- the value of `t'` at `i`
  have hval' : ∀ e0, M.ValRaw P th io M.nat Nt j.1 d α t' i e0 →
      (M.ValRaw P th io M.nat Nt j.1 d α t' i e' ↔ e' = e0) := fun e0 h0 =>
    ⟨fun h => M.val_unique hd h h0, fun h => by rw [h]; exact h0⟩
  rcases hcase with ⟨eiv, eea⟩ | ⟨niv, hvt⟩
  · -- `i = v`: the entry is `a`, a name of rank below `α`
    rw [eea] at hnt
    rw [hval' a (Or.inl ⟨hnt, ha⟩)]
    constructor
    · intro h
      exact Or.inl ⟨eiv, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd eiv h
  · -- `i ≠ v`: the entry is the value of `t`
    have hvt' : M.ValRaw P th io M.nat Nt j.1 d α t' i e := by
      rcases M.val_of_nth hd (α := α) hnt with ⟨-, h⟩ | ⟨hN, h⟩
      · exact h
      · rcases hvt with ⟨-, k2⟩ | ⟨-, k2⟩
        · exact absurd k2 hN
        · rw [k2]
          exact h
    rw [hval' e hvt']
    constructor
    · intro h
      exact Or.inr ⟨niv, by rw [h]; exact hvt⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h niv
      · exact M.val_unique hd h hvt

theorem exists_upd (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α a : V}
    (ha : M.InNRaw P th io M.nat j.1 α a) (t v : V) (c : M.Num) :
    ∃ t', M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v a c.1 := by
  obtain ⟨t', -, h⟩ := M.exists_updR hd ha t v c
  exact ⟨t', h⟩

/-- Membership between the sets denoted respects "denote the same set". -/
theorem epsStar_congr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a a1 b b1 : V}
    (ha : M.SimRaw P j.1 tp F a a1) (hb : M.SimRaw P j.1 tp F b b1)
    (h : M.EpsStarRaw P th io M.nat j.1 tp F a b) : M.EpsStarRaw P th io M.nat j.1 tp F a1 b1 := by
  obtain ⟨a', hs, he⟩ := h
  obtain ⟨βb, βb1, rb, rb1, hβb, hβb1⟩ := M.sim_names hd hb
  obtain ⟨x', hx', hs'⟩ := ((M.hier_sim hd rb rb1 hβb hβb1).mp hb).1 a' he
  exact ⟨x', M.sim_trans hd (M.sim_trans hd (M.sim_symm hd ha) hs) hs', hx'⟩

theorem inN_refl (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α y : V}
    (hy : M.InNRaw P th io M.nat j.1 α y) : M.SimRaw P j.1 tp F y y := by
  obtain ⟨βy, ry, hβy, -⟩ := M.inN_rank hy
  exact M.sim_refl hd ry (hd.hth.fld βy α hβy).1


theorem isPairAt_congr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α x y s s1 : V}
    (hs : M.SimRaw P j.1 tp F s s1) (h : M.IsPairAt P th io M.nat j.1 tp F α x y s) :
    M.IsPairAt P th io M.nat j.1 tp F α x y s1 := by
  intro z hz
  rw [← h z hz]
  exact ⟨fun k => M.epsStar_congr hd (M.inN_refl hd hz) (M.sim_symm hd hs) k,
    fun k => M.epsStar_congr hd (M.inN_refl hd hz) hs k⟩

theorem isOPairAt_congr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α x y s s1 : V}
    (hs : M.SimRaw P j.1 tp F s s1) (h : M.IsOPairAt P th io M.nat j.1 tp F α x y s) :
    M.IsOPairAt P th io M.nat j.1 tp F α x y s1 := by
  obtain ⟨u1, u2, h1, h2, h3, h4, h5⟩ := h
  exact ⟨u1, u2, h1, h2, h3, h4, M.isPairAt_congr hd hs h5⟩

/-- The meaning of a relation symbol at stage `α` depends only on the sets denoted. -/
theorem atomAt_congr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α a b a1 b1 r : V}
    (hs1 : M.SimRaw P j.1 tp F a a1) (hs2 : M.SimRaw P j.1 tp F b b1)
    (ha1 : M.InNRaw P th io M.nat j.1 α a1 ∨ a1 = d)
    (hb1 : M.InNRaw P th io M.nat j.1 α b1 ∨ b1 = d)
    (h : M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG (1 : M.Num).1 (2 : M.Num).1
      F α r a b) :
    M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG (1 : M.Num).1 (2 : M.Num).1
      F α r a1 b1 := by
  have inN_of : ∀ {x x1 : V}, M.InNRaw P th io M.nat j.1 α x →
      (M.InNRaw P th io M.nat j.1 α x1 ∨ x1 = d) → M.InNRaw P th io M.nat j.1 α x1 := by
    intro x x1 hx hx1
    rcases hx1 with k | k
    · exact k
    · obtain ⟨βx, -, ltx, nex⟩ := M.inN_rank hx
      rw [k]
      exact M.d_inN hd ltx nex
  rcases h with ⟨h1, h2, heps⟩ | ⟨h1, hT⟩ | ⟨h1, hL⟩
  · exact Or.inl ⟨h1, h2, M.epsStar_congr hd hs1 hs2 heps⟩
  · obtain ⟨ha, hb, β, c, ob, oc, t', g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := hT
    refine Or.inr (Or.inl ⟨h1, inN_of ha ha1, inN_of hb hb1, β, c, ob, oc, t', g1, g2, g3, g4,
      g5, g6, g7, M.isOPairAt_congr hd hs1 g8, ?_, ?_, g11⟩)
    · intro i hi hle oi y y' s s' k1 k2 k3 k4 k5 k6 k7 k8 k9 k10
      exact g9 i hi hle oi y y' s s' k1 k2 k3 k4 k5 k6
        (M.epsStar_congr hd (M.inN_refl hd k5) (M.sim_symm hd hs2) k7) k8
        (M.epsStar_congr hd (M.inN_refl hd k6) (M.sim_symm hd hs2) k9) k10
    · intro i hi hle
      obtain ⟨oi, y, s, e, k1, k2, k3, k4, k5, k6, k7, k8⟩ := g10 i hi hle
      exact ⟨oi, y, s, e, k1, k2, k3, k4, M.epsStar_congr hd (M.inN_refl hd k4) hs2 k5, k6, k7,
        k8⟩
  · obtain ⟨ha, hb, a0, b0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := hL
    exact Or.inr (Or.inr ⟨h1, inN_of ha ha1, inN_of hb hb1, a0, b0, g1, g2,
      M.sim_trans hd (M.sim_symm hd hs1) g3, M.sim_trans hd (M.sim_symm hd hs2) g4, g5, g6, g7,
      g8⟩)

end hier6

/-- "Invariance up to `n`" (name `99`) at stage `α` (name `65`), with `F` the name `6`. -/
def invHFml : Fml :=
  .all 83 (Fml.imp (.mem 83 27) (Fml.imp (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 83 84 99)))
    (.all 80 (.all 81 (Fml.imp
      (.all 67 (Fml.imp (.mem 67 27) (Fml.imp (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 67 84 83)))
        (Fml.ex 92 (Fml.ex 93
          (.and (Fml.ex 66 (.and (.eq 66 80) (Fml.ex 68 (.and (.eq 68 92) valFml))))
          (.and (Fml.ex 66 (.and (.eq 66 81) (Fml.ex 68 (.and (.eq 68 93) valFml))))
            (Fml.ex 94 (.and (.eq 94 92) (Fml.ex 95 (.and (.eq 95 93) simFml)))))))))))
      (Fml.imp (Fml.ex 85 (Fml.ex 86 (.and (fApp 24 83 85) (.and (fApp4 20 25 65 85 86)
          (fApp 6 86 80)))))
        (Fml.ex 85 (Fml.ex 86 (.and (fApp 24 83 85) (.and (fApp4 20 25 65 85 86)
          (fApp 6 86 81)))))))))))

section hier7

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- The step of the invariance lemma. -/
theorem inv_hier_core (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V} (c : M.Num)
    (ih : ∀ c' : M.Num, c' + 1 ≤ c → ∀ t t', (∀ i : M.Num, i ≤ c' → ∃ e e',
      M.ValRaw P th io M.nat Nt j.1 d α t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e' ∧
        M.SimRaw P j.1 tp F e e') →
      M.TrueAt P io F j.1 α c' t → M.TrueAt P io F j.1 α c' t')
    (t t' : V) (hag : ∀ i : M.Num, i ≤ c → ∃ e e',
      M.ValRaw P th io M.nat Nt j.1 d α t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e' ∧
        M.SimRaw P j.1 tp F e e')
    (h : M.TrueAt P io F j.1 α c t) : M.TrueAt P io F j.1 α c t' := by
  have swap : ∀ {c' : M.Num} {s s' : V}, (∀ i : M.Num, i ≤ c' → ∃ e e',
      M.ValRaw P th io M.nat Nt j.1 d α s i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d α s' i.1 e' ∧
        M.SimRaw P j.1 tp F e e') → ∀ i : M.Num, i ≤ c' → ∃ e e',
      M.ValRaw P th io M.nat Nt j.1 d α s' i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d α s i.1 e' ∧
        M.SimRaw P j.1 tp F e e' := by
    intro c' s s' hyp i hi
    obtain ⟨e, e', h1, h2, h3⟩ := hyp i hi
    exact ⟨e', e, h2, h1, M.sim_symm hd h3⟩
  rcases M.trueAt_shape hd h with ⟨r, v, w, e⟩ | ⟨c', e⟩ | ⟨c', c'', e⟩ | ⟨v, c', e⟩
  · rw [e] at h hag ⊢
    obtain ⟨hα, a, b, hva, hvb, heps⟩ := (M.hier_rel hd r v w t).mp h
    have hvw : M.pairN v w ≤ M.cRel r v w :=
      le_trans (M.le_pairN_right r _) (M.le_pairN_right 0 _)
    obtain ⟨e1, e1', k1, k1', s1⟩ := hag v (le_trans (M.le_pairN_left v w) hvw)
    obtain ⟨e2, e2', k2, k2', s2⟩ := hag w (le_trans (M.le_pairN_right v w) hvw)
    rw [M.val_unique hd hva k1, M.val_unique hd hvb k2] at heps
    exact (M.hier_rel hd r v w t').mpr ⟨hα, e1', e2', k1', k2',
      M.atomAt_congr hd s1 s2 (M.val_cases k1') (M.val_cases k2') heps⟩
  · rw [e] at h hag ⊢
    obtain ⟨hα, hnot⟩ := (M.hier_neg hd c' t).mp h
    have lt1 : c' + 1 ≤ M.cNeg c' := M.lt_pairN_right c' (le_refl 1)
    refine (M.hier_neg hd c' t').mpr ⟨hα, fun h' => hnot ?_⟩
    exact ih c' (by rw [e]; exact lt1) t' t (swap (fun i hi =>
      hag i (le_trans hi (le_trans (M.le_add_one c') lt1)))) h'
  · rw [e] at h hag ⊢
    obtain ⟨hα, h1, h2⟩ := (M.hier_and hd c' c'' t).mp h
    have lt1 : c' + 1 ≤ M.cAnd c' c'' :=
      le_trans (add_le_add (M.le_pairN_left c' c'') (le_refl 1))
        (M.lt_pairN_right _ M.one_le_two')
    have lt2 : c'' + 1 ≤ M.cAnd c' c'' :=
      le_trans (add_le_add (M.le_pairN_right c' c'') (le_refl 1))
        (M.lt_pairN_right _ M.one_le_two')
    exact (M.hier_and hd c' c'' t').mpr ⟨hα,
      ih c' (by rw [e]; exact lt1) t t' (fun i hi =>
        hag i (le_trans hi (le_trans (M.le_add_one c') lt1))) h1,
      ih c'' (by rw [e]; exact lt2) t t' (fun i hi =>
        hag i (le_trans hi (le_trans (M.le_add_one c'') lt2))) h2⟩
  · rw [e] at h hag ⊢
    obtain ⟨hα, hall⟩ := (M.hier_all hd v c' t).mp h
    have lt1 : c' + 1 ≤ M.cAll v c' :=
      le_trans (add_le_add (M.le_pairN_right v c') (le_refl 1))
        (M.lt_pairN_right _ M.one_le_three')
    refine (M.hier_all hd v c' t').mpr ⟨hα, fun a t1 ha hag1 => ?_⟩
    obtain ⟨t0, hag0⟩ := M.exists_upd hd ha t v.1 (M.cAll v c')
    have h0 := hall a t0 ha hag0
    refine ih c' (by rw [e]; exact lt1) t0 t1 (fun i hi => ?_) h0
    have hic : i ≤ M.cAll v c' := le_trans hi (le_trans (M.le_add_one c') lt1)
    have hle := (M.leRaw_iff M.adG_spec i (M.cAll v c')).mpr hic
    by_cases eiv : i.1 = v.1
    · obtain ⟨βa, ra, lta, -⟩ := M.inN_rank ha
      exact ⟨a, a, (hag0 i.1 i.2 hle a).mpr (Or.inl ⟨eiv, rfl⟩),
        (hag1 i.1 i.2 hle a).mpr (Or.inl ⟨eiv, rfl⟩),
        M.sim_refl hd ra (hd.hth.fld βa α lta).1⟩
    · obtain ⟨e0, e0', k0, k0', s0⟩ := hag i hic
      exact ⟨e0, e0', (hag0 i.1 i.2 hle e0).mpr (Or.inr ⟨eiv, k0⟩),
        (hag1 i.1 i.2 hle e0').mpr (Or.inr ⟨eiv, k0'⟩), s0⟩

/-- **Invariance.** If the values of the variables up to the code of `c` under `t` and under
`t'` denote the same sets, then `c` is true under `t` if and only if it is true under `t'`.
So "denote the same set" is a congruence for the truth definition of every stage. -/
theorem inv_hier (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V} (c : M.Num) (t t' : V)
    (hag : ∀ i : M.Num, i ≤ c → ∃ e e',
      M.ValRaw P th io M.nat Nt j.1 d α t i.1 e ∧ M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e' ∧
        M.SimRaw P j.1 tp F e e') :
    M.TrueAt P io F j.1 α c t ↔ M.TrueAt P io F j.1 α c t' := by
  have had := M.adG_spec
  have hsat : ∀ n : M.Num, Sat M.mem M.isSet invHFml (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG)
      65 α) 99 n.1) ↔
      ∀ c : M.Num, c ≤ n → ∀ t t', (∀ i : M.Num, i ≤ c → ∃ e e',
        M.ValRaw P th io M.nat Nt j.1 d α t i.1 e ∧
          M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e' ∧ M.SimRaw P j.1 tp F e e') →
        M.TrueAt P io F j.1 α c t → M.TrueAt P io F j.1 α c t' := by
    intro n
    have h1 : Sat M.mem M.isSet invHFml (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG)
        65 α) 99 n.1) ↔
        ∀ c, M.mem c M.nat → M.LeRaw M.adG c n.1 → ∀ t t',
          (∀ i, M.mem i M.nat → M.LeRaw M.adG i c → ∃ e e',
            M.ValRaw P th io M.nat Nt j.1 d α t i e ∧
              M.ValRaw P th io M.nat Nt j.1 d α t' i e' ∧ M.SimRaw P j.1 tp F e e') →
          (∃ ch pt, M.mem (M.op c ch) io ∧ M.mem (M.quad j.1 α ch pt) P ∧ M.mem (M.op pt t) F) →
          ∃ ch pt, M.mem (M.op c ch) io ∧ M.mem (M.quad j.1 α ch pt) P ∧
            M.mem (M.op pt t') F := by
      simp [invHFml, LeRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fApp3', M.sat_fApp4', M.sat_fApp',
        M.sat_valFml, M.sat_simFml, Function.update_apply]
    rw [h1]
    constructor
    · intro raw c hc t t' hag htr
      exact raw c.1 c.2 ((M.leRaw_iff had c n).mpr hc) t t'
        (fun i hi hle => hag ⟨i, hi⟩ ((M.leRaw_iff had ⟨i, hi⟩ c).mp hle)) htr
    · intro clean c hc hle t t' hag htr
      exact clean ⟨c, hc⟩ ((M.leRaw_iff had ⟨c, hc⟩ n).mp hle) t t'
        (fun i hi => hag i.1 i.2 ((M.leRaw_iff had i ⟨c, hc⟩).mpr hi)) htr
  have key := M.num_ind_fml (σW [(6, 5), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7)])
    invHFml 99 rfl (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th) 23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat) 28 M.adG)
      65 α)
    (by
      rw [show M.zero = (0 : M.Num).1 from rfl, hsat 0]
      intro c0 hc0 t0 t0' hag0 htr0
      exact M.inv_hier_core hd c0 (fun c' hc' => absurd (le_trans hc' hc0)
        (fun h => M.succ_not_le_zero h)) t0 t0' hag0 htr0)
    (fun k ih => by
      rw [hsat k] at ih
      rw [show M.succ k.1 = (k + 1).1 from (M.val_add_one k).symm, hsat (k + 1)]
      intro c0 hc0 t0 t0' hag0 htr0
      exact M.inv_hier_core hd c0 (fun c' hc' =>
        ih c' (M.le_of_succ_le_succ (le_trans hc' hc0))) t0 t0' hag0 htr0) c
  rw [hsat c] at key
  refine ⟨key c (le_refl c) t t' hag, key c (le_refl c) t' t (fun i hi => ?_)⟩
  obtain ⟨e, e', h1, h2, h3⟩ := hag i hi
  exact ⟨e', e, h2, h1, M.sim_symm hd h3⟩

end hier7

section hier8

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **The quantifier, in Tarski's form.** `∀v c` is true at stage `α` under `t` if and only
if for every name `a` of rank below `α`, `c` is true under some (equivalently, by
`hier_all`, every) sequence that has the values of `t` except that its value at `v` is `a`. -/
theorem hier_all_ex (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V} (v c : M.Num)
    (t : V) :
    M.TrueAt P io F j.1 α (M.cAll v c) t ↔ M.mem (M.op α α) th ∧
      ∀ a, M.InNRaw P th io M.nat j.1 α a →
        ∃ t', M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v.1 a (M.cAll v c).1 ∧
          M.TrueAt P io F j.1 α c t' := by
  constructor
  · intro h
    obtain ⟨hα, hall⟩ := (M.hier_all hd v c t).mp h
    refine ⟨hα, fun a ha => ?_⟩
    obtain ⟨t', hag⟩ := M.exists_upd hd ha t v.1 (M.cAll v c)
    exact ⟨t', hag, hall a t' ha hag⟩
  · rintro ⟨hα, hex⟩
    refine (M.hier_all hd v c t).mpr ⟨hα, fun a t1 ha hag1 => ?_⟩
    obtain ⟨t0, hag0, h0⟩ := hex a ha
    have lt1 : c + 1 ≤ M.cAll v c :=
      le_trans (add_le_add (M.le_pairN_right v c) (le_refl 1))
        (M.lt_pairN_right _ M.one_le_three')
    refine (M.coin_hier hd c t0 t1 (fun i hi e => ?_)).mp h0
    have hle := (M.leRaw_iff M.adG_spec i (M.cAll v c)).mpr
      (le_trans hi (le_trans (M.le_add_one c) lt1))
    exact (hag0 i.1 i.2 hle e).trans (hag1 i.1 i.2 hle e).symm

/-- **Extensionality.** Two names denote the same set if and only if the same things are
members of the sets they denote. -/
theorem sim_iff_ext (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a b β β' : V}
    (ra : M.RankIs P io M.nat j.1 β a) (rb : M.RankIs P io M.nat j.1 β' b)
    (hβ : M.mem (M.op β β) th) (hβ' : M.mem (M.op β' β') th) :
    M.SimRaw P j.1 tp F a b ↔ ∀ x, (M.EpsStarRaw P th io M.nat j.1 tp F x a ↔
      M.EpsStarRaw P th io M.nat j.1 tp F x b) := by
  have self : ∀ {x c : V}, M.EpsStarRaw P th io M.nat j.1 tp F x c → M.SimRaw P j.1 tp F x x := by
    rintro x c ⟨x', hs, -⟩
    obtain ⟨βx, -, rx, -, hβx, -⟩ := M.sim_names hd hs
    exact M.sim_refl hd rx hβx
  have memStar : ∀ {x c βc : V}, M.RankIs P io M.nat j.1 βc c →
      M.EpsRaw P th io M.nat j.1 F x c → M.EpsStarRaw P th io M.nat j.1 tp F x c := by
    intro x c βc rc hx
    obtain ⟨βx, rx, ltx, -⟩ := M.inN_rank (M.eps_inN_rank hd rc hx)
    exact ⟨x, M.sim_refl hd rx (hd.hth.fld βx βc ltx).1, hx⟩
  constructor
  · intro h x
    exact ⟨fun hx => M.epsStar_congr hd (self hx) h hx,
      fun hx => M.epsStar_congr hd (self hx) (M.sim_symm hd h) hx⟩
  · intro h
    refine (M.hier_sim hd ra rb hβ hβ').mpr ⟨fun x hx => ?_, fun x' hx' => ?_⟩
    · obtain ⟨x', hs, hx'⟩ := (h x).mp (memStar ra hx)
      exact ⟨x', hx', hs⟩
    · obtain ⟨x, hs, hx⟩ := (h x').mpr (memStar rb hx')
      exact ⟨x, hx, M.sim_symm hd hs⟩

end hier8

/-! ### Equality is definable in every level -/

/-- The code of `A ↔ B`. -/
noncomputable def cIff (A B : M.Num) : M.Num :=
  M.cAnd (M.cNeg (M.cAnd A (M.cNeg B))) (M.cNeg (M.cAnd B (M.cNeg A)))

/-- The code of "`v` and `w` have the same members": `∀z (z ε v ↔ z ε w)`. -/
noncomputable def cEq (z v w : M.Num) : M.Num :=
  M.cAll z (M.cIff (M.cRel 0 z v) (M.cRel 0 z w))

theorem iff_prop {h p q : Prop} (hh : h) :
    (h ∧ (h ∧ ¬(h ∧ p ∧ h ∧ ¬q)) ∧ (h ∧ ¬(h ∧ q ∧ h ∧ ¬p))) ↔ (p ↔ q) := by
  tauto

section hier9

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- The atomic clause for `ε`, given the values. -/
theorem rel_val (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t a b : V} (v w : M.Num)
    (hα : M.mem (M.op α α) th) (hva : M.ValRaw P th io M.nat Nt j.1 d α t v.1 a)
    (hvb : M.ValRaw P th io M.nat Nt j.1 d α t w.1 b) :
    M.TrueAt P io F j.1 α (M.cRel 0 v w) t ↔ M.EpsStarRaw P th io M.nat j.1 tp F a b := by
  rw [M.hier_relE hd 0 v w M.n01 M.n02]
  constructor
  · rintro ⟨-, a1, b1, k1, k2, h⟩
    rw [M.val_unique hd k1 hva, M.val_unique hd k2 hvb] at h
    exact h
  · intro h
    exact ⟨hα, a, b, hva, hvb, h⟩

theorem hier_iff (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) (A B : M.Num) (t : V) :
    M.TrueAt P io F j.1 α (M.cIff A B) t ↔
      (M.TrueAt P io F j.1 α A t ↔ M.TrueAt P io F j.1 α B t) := by
  simp only [cIff, M.hier_and hd, M.hier_neg hd]
  exact iff_prop hα

/-- **Equality is definable.** The formula `∀z (z ε v ↔ z ε w)` is true at stage `α` exactly
when the values of `v` and `w` have the same members among the sets denoted by names of rank
below `α`. -/
theorem hier_eq (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t a b : V}
    (hα : M.mem (M.op α α) th) (z v w : M.Num) (hzv : z ≠ v) (hzw : z ≠ w)
    (hva : M.ValRaw P th io M.nat Nt j.1 d α t v.1 a)
    (hvb : M.ValRaw P th io M.nat Nt j.1 d α t w.1 b) :
    M.TrueAt P io F j.1 α (M.cEq z v w) t ↔ ∀ x, M.InNRaw P th io M.nat j.1 α x →
      (M.EpsStarRaw P th io M.nat j.1 tp F x a ↔ M.EpsStarRaw P th io M.nat j.1 tp F x b) := by
  -- the variables are below the code
  have hC : M.cIff (M.cRel 0 z v) (M.cRel 0 z w) ≤ M.cEq z v w :=
    le_trans (M.le_pairN_right z _) (M.le_pairN_right 3 _)
  have hA : M.cRel 0 z v ≤ M.cIff (M.cRel 0 z v) (M.cRel 0 z w) :=
    le_trans (le_trans (M.le_pairN_left _ (M.cNeg (M.cRel 0 z w))) (M.le_pairN_right 2 _))
      (le_trans (M.le_pairN_right 1 _)
        (le_trans (M.le_pairN_left _ _) (M.le_pairN_right 2 _)))
  have hB : M.cRel 0 z w ≤ M.cIff (M.cRel 0 z v) (M.cRel 0 z w) :=
    le_trans (le_trans (M.le_pairN_left _ (M.cNeg (M.cRel 0 z v))) (M.le_pairN_right 2 _))
      (le_trans (M.le_pairN_right 1 _)
        (le_trans (M.le_pairN_right _ _) (M.le_pairN_right 2 _)))
  have hzv' : M.pairN z v ≤ M.cRel 0 z v :=
    le_trans (M.le_pairN_right 0 _) (M.le_pairN_right 0 _)
  have hzw' : M.pairN z w ≤ M.cRel 0 z w :=
    le_trans (M.le_pairN_right 0 _) (M.le_pairN_right 0 _)
  have lez : z ≤ M.cEq z v w :=
    le_trans (M.le_pairN_left z v) (le_trans hzv' (le_trans hA hC))
  have lev : v ≤ M.cEq z v w :=
    le_trans (M.le_pairN_right z v) (le_trans hzv' (le_trans hA hC))
  have lew : w ≤ M.cEq z v w :=
    le_trans (M.le_pairN_right z w) (le_trans hzw' (le_trans hB hC))
  -- the body under a sequence with `z` changed to `x`
  have body : ∀ x t', M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' z.1 x (M.cEq z v w).1 →
      (M.TrueAt P io F j.1 α (M.cIff (M.cRel 0 z v) (M.cRel 0 z w)) t' ↔
        (M.EpsStarRaw P th io M.nat j.1 tp F x a ↔ M.EpsStarRaw P th io M.nat j.1 tp F x b)) := by
    intro x t' hag
    have kz : M.ValRaw P th io M.nat Nt j.1 d α t' z.1 x :=
      (hag z.1 z.2 ((M.leRaw_iff M.adG_spec z _).mpr lez) x).mpr (Or.inl ⟨rfl, rfl⟩)
    have kv : M.ValRaw P th io M.nat Nt j.1 d α t' v.1 a :=
      (hag v.1 v.2 ((M.leRaw_iff M.adG_spec v _).mpr lev) a).mpr
        (Or.inr ⟨fun e => hzv (Subtype.ext e).symm, hva⟩)
    have kw : M.ValRaw P th io M.nat Nt j.1 d α t' w.1 b :=
      (hag w.1 w.2 ((M.leRaw_iff M.adG_spec w _).mpr lew) b).mpr
        (Or.inr ⟨fun e => hzw (Subtype.ext e).symm, hvb⟩)
    rw [M.hier_iff hd hα, M.rel_val hd z v hα kz kv, M.rel_val hd z w hα kz kw]
  unfold cEq at *
  rw [M.hier_all_ex hd]
  constructor
  · rintro ⟨-, hall⟩ x hx
    obtain ⟨t', hag, htr⟩ := hall x hx
    exact (body x t' hag).mp htr
  · intro h
    refine ⟨hα, fun x hx => ?_⟩
    obtain ⟨t', hag⟩ := M.exists_upd hd hx t z.1
      (M.cAll z (M.cIff (M.cRel 0 z v) (M.cRel 0 z w)))
    exact ⟨t', hag, (body x t' hag).mpr (h x hx)⟩

/-- **Equality is definable**, second form: for values that are names of rank below `α`, the
formula `∀z (z ε v ↔ z ε w)` is true at stage `α` exactly when they denote the same set. -/
theorem hier_eq_sim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t a b : V}
    (hα : M.mem (M.op α α) th) (z v w : M.Num) (hzv : z ≠ v) (hzw : z ≠ w)
    (hva : M.ValRaw P th io M.nat Nt j.1 d α t v.1 a)
    (hvb : M.ValRaw P th io M.nat Nt j.1 d α t w.1 b)
    (ha : M.InNRaw P th io M.nat j.1 α a) (hb : M.InNRaw P th io M.nat j.1 α b) :
    M.TrueAt P io F j.1 α (M.cEq z v w) t ↔ M.SimRaw P j.1 tp F a b := by
  obtain ⟨βa, ra, lta, -⟩ := M.inN_rank ha
  obtain ⟨βb, rb, ltb, -⟩ := M.inN_rank hb
  have hβa := (hd.hth.fld βa α lta).1
  have hβb := (hd.hth.fld βb α ltb).1
  rw [M.hier_eq hd hα z v w hzv hzw hva hvb, M.sim_iff_ext hd ra rb hβa hβb]
  -- members of names of rank below `α` are denoted by names of rank below `α`
  have down : ∀ {c c' : V}, M.InNRaw P th io M.nat j.1 α c →
      (∀ x, M.InNRaw P th io M.nat j.1 α x → M.EpsStarRaw P th io M.nat j.1 tp F x c →
        M.EpsStarRaw P th io M.nat j.1 tp F x c') →
      ∀ x, M.EpsStarRaw P th io M.nat j.1 tp F x c → M.EpsStarRaw P th io M.nat j.1 tp F x c' := by
    intro c c' hc hres x hx
    obtain ⟨x', hs, hx'⟩ := hx
    have hx'N := M.eps_rank hd hc hx'
    obtain ⟨βx, rx, ltx, -⟩ := M.inN_rank hx'N
    have hxx' : M.SimRaw P j.1 tp F x' x' := M.sim_refl hd rx (hd.hth.fld βx α ltx).1
    obtain ⟨y, hsy, hy⟩ := hres x' hx'N ⟨x', hxx', hx'⟩
    exact ⟨y, M.sim_trans hd hs hsy, hy⟩
  constructor
  · intro h x
    exact ⟨down ha (fun x hx => (h x hx).mp) x, down hb (fun x hx => (h x hx).mpr) x⟩
  · intro h x _
    exact h x

end hier9

/-! ### Two closure facts: the level as a set, and pairs -/

/-- The code of `X ∨ Y`. -/
noncomputable def cOr (X Y : M.Num) : M.Num := M.cNeg (M.cAnd (M.cNeg X) (M.cNeg Y))

theorem or_prop {h p q : Prop} (hh : h) : (h ∧ ¬(h ∧ (h ∧ ¬p) ∧ (h ∧ ¬q))) ↔ (p ∨ q) := by
  tauto

section hier10

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem hier_or (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) (X Y : M.Num) (t : V) :
    M.TrueAt P io F j.1 α (M.cOr X Y) t ↔
      (M.TrueAt P io F j.1 α X t ∨ M.TrueAt P io F j.1 α Y t) := by
  simp only [cOr, M.hier_and hd, M.hier_neg hd]
  exact or_prop hα

theorem nth_cons_succ (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {x u s : V}
    (hs : M.mem (M.quad j.1 x u s) P) (n : M.Num) (e : V) :
    M.mem (M.trip s (n + 1).1 e) Nt ↔ M.mem (M.trip u n.1 e) Nt := by
  rw [hd.nt_succ]
  constructor
  · rintro ⟨a, t', q', h⟩
    rw [(hd.hP.inj _ _ _ _ _ _ q' hs).2] at h
    exact h
  · intro h
    exact ⟨x, u, hs, h⟩

/-- **Every level is a set of the next level**: for every stage `α` there is a name of rank
`α` whose members are exactly the names of rank below `α`. -/
theorem level_name (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) :
    ∃ b, M.RankIs P io M.nat j.1 α b ∧
      ∀ a, M.EpsRaw P th io M.nat j.1 F a b ↔ M.InNRaw P th io M.nat j.1 α a := by
  obtain ⟨f, hf⟩ := hd.io_tot (M.cNeg (M.cAnd 0 (M.cNeg 0)))
  obtain ⟨q, hq⟩ := hd.hP.tot j hd.hj f d (hd.io_dom _ _ hf).2 (M.d_rung hd)
  obtain ⟨b, hb⟩ := hd.hP.tot j hd.hj α q (hd.th_rung α α hα).1 (hd.hP.dom _ _ _ _ hq).2.2.2
  refine ⟨b, ⟨f, d, q, hb, hq, _, (hd.io_dom _ _ hf).1, hf⟩, fun a => ?_⟩
  rw [M.eps_iff hd hb hq hf a]
  constructor
  · exact fun h => h.1
  · intro ha
    obtain ⟨s, hs⟩ := hd.hP.tot j hd.hj a d (M.inN_rung hd ha) (M.d_rung hd)
    refine ⟨ha, s, hs, (M.hier_neg hd _ s).mpr ⟨hα, fun h => ?_⟩⟩
    obtain ⟨-, h1, h2⟩ := (M.hier_and hd _ _ s).mp h
    exact ((M.hier_neg hd _ s).mp h2).2 h1

/-- **Pairs.** For names `a`, `b` of rank below `α` there is a name of rank `α` whose members
are the names of rank below `α` that denote the same set as `a` or as `b`. -/
theorem pair_name (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α a b : V}
    (hα : M.mem (M.op α α) th) (ha : M.InNRaw P th io M.nat j.1 α a)
    (hb : M.InNRaw P th io M.nat j.1 α b) :
    ∃ c, M.RankIs P io M.nat j.1 α c ∧ ∀ x, M.EpsRaw P th io M.nat j.1 F x c ↔
      M.InNRaw P th io M.nat j.1 α x ∧ (M.SimRaw P j.1 tp F x a ∨ M.SimRaw P j.1 tp F x b) := by
  obtain ⟨f, hf⟩ := hd.io_tot (M.cOr (M.cEq 3 0 1) (M.cEq 3 0 2))
  obtain ⟨u2, hu2⟩ := hd.hP.tot j hd.hj b d (M.inN_rung hd hb) (M.d_rung hd)
  obtain ⟨u, hu⟩ := hd.hP.tot j hd.hj a u2 (M.inN_rung hd ha) (hd.hP.dom _ _ _ _ hu2).2.2.2
  have huR := (hd.hP.dom _ _ _ _ hu).2.2.2
  obtain ⟨q, hq⟩ := hd.hP.tot j hd.hj f u (hd.io_dom _ _ hf).2 huR
  obtain ⟨c, hc⟩ := hd.hP.tot j hd.hj α q (hd.th_rung α α hα).1 (hd.hP.dom _ _ _ _ hq).2.2.2
  refine ⟨c, ⟨f, u, q, hc, hq, _, (hd.io_dom _ _ hf).1, hf⟩, fun x => ?_⟩
  rw [M.eps_iff hd hc hq hf x]
  -- truth of the formula under the sequence `(x, a, b, …)`
  have key : ∀ s, M.InNRaw P th io M.nat j.1 α x → M.mem (M.quad j.1 x u s) P →
      (M.TrueAt P io F j.1 α (M.cOr (M.cEq 3 0 1) (M.cEq 3 0 2)) s ↔
        (M.SimRaw P j.1 tp F x a ∨ M.SimRaw P j.1 tp F x b)) := by
    intro s hx hs
    have v0 : M.ValRaw P th io M.nat Nt j.1 d α s (0 : M.Num).1 x :=
      Or.inl ⟨(hd.nt_zero s x).mpr ⟨u, hs⟩, hx⟩
    have n1 : M.mem (M.trip s (1 : M.Num).1 a) Nt := by
      have h1 := (M.nth_cons_succ hd hs 0 a).mpr ((hd.nt_zero u a).mpr ⟨u2, hu⟩)
      rwa [zero_add] at h1
    have v1 : M.ValRaw P th io M.nat Nt j.1 d α s (1 : M.Num).1 a := Or.inl ⟨n1, ha⟩
    have n2 : M.mem (M.trip s (2 : M.Num).1 b) Nt := by
      have h1 : M.mem (M.trip u (1 : M.Num).1 b) Nt := by
        have h0 := (M.nth_cons_succ hd hu 0 b).mpr ((hd.nt_zero u2 b).mpr ⟨d, hu2⟩)
        rwa [zero_add] at h0
      have h2 := (M.nth_cons_succ hd hs 1 b).mpr h1
      rwa [one_add_one_eq_two] at h2
    have v2 : M.ValRaw P th io M.nat Nt j.1 d α s (2 : M.Num).1 b := Or.inl ⟨n2, hb⟩
    rw [M.hier_or hd hα, M.hier_eq_sim hd hα 3 0 1 M.n30 M.n31 v0 v1 hx ha,
      M.hier_eq_sim hd hα 3 0 2 M.n30 M.n32 v0 v2 hx hb]
  constructor
  · rintro ⟨hx, s, hs, htr⟩
    exact ⟨hx, (key s hx hs).mp htr⟩
  · rintro ⟨hx, hor⟩
    obtain ⟨s, hs⟩ := hd.hP.tot j hd.hj x u (M.inN_rung hd hx) huR
    exact ⟨hx, s, hs, (key s hx hs).mpr hor⟩

end hier10

/-! ## The levels as set structures in the sense of §3.1

For a stage `α` above the least one, the names of rank below `α` with membership between the
sets they denote form a set structure `(U, E)` as in `NFUSat` (every sort is the set of these
names, every relation is that membership). Its satisfaction relation agrees with the truth
definition of the hierarchy. -/

theorem sat_fTripq' {q a b c : ℕ} (ρ : ℕ → V) (hq : q < 30 ∨ q = 39) (ha : a < 30 ∨ 59 < a)
    (hb : b < 30 ∨ 59 < b) (hc : c < 30 ∨ 59 < c) :
    Sat M.mem M.isSet (fTrip q a b c) ρ ↔ ρ q = M.trip (ρ a) (ρ b) (ρ c) := by
  have q32 : q ≠ 32 := by omega
  have q33 : q ≠ 33 := by omega
  have a32 : a ≠ 32 := by omega
  have a33 : a ≠ 33 := by omega
  have b32 : b ≠ 32 := by omega
  have b33 : b ≠ 33 := by omega
  have c32 : c ≠ 32 := by omega
  have c33 : c ≠ 33 := by omega
  simp only [fTrip, M.sat_ex, Sat,
    M.sat_fOp (p := q) (a := 32) (b := 33) (u := 34) (c := 35) (by omega) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    M.sat_fOp (p := 32) (a := a) (b := b) (u := 36) (c := 37) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    M.sat_fOp (p := 33) (a := c) (b := c) (u := 36) (c := 37) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by decide),
    Function.update_self, Function.update_of_ne q32, Function.update_of_ne q33,
    Function.update_of_ne a32, Function.update_of_ne a33, Function.update_of_ne b32,
    Function.update_of_ne b33, Function.update_of_ne c32, Function.update_of_ne c33,
    Function.update_of_ne (show (32 : ℕ) ≠ 33 by decide)]
  unfold trip
  constructor
  · rintro ⟨p1, p2, h1, rfl, rfl⟩
    exact h1
  · intro h
    exact ⟨_, _, h, rfl, rfl⟩

/-- A code that is true or false somewhere in a set structure has one of the four shapes. -/
theorem shape_of_decided {U E : V} {c : M.Num} {s : V}
    (h : M.Holds U E c s ∨ M.Fails U E c s) :
    (∃ r v w, c = M.cRel r v w) ∨ (∃ x, c = M.cNeg x) ∨ (∃ φ ψ, c = M.cAnd φ ψ) ∨
      ∃ t n φ, c = M.cAll (M.vr t n) φ := by
  have key : ∀ sg : M.Num, M.mem (M.fact (M.pairN c sg).1 s) (M.satSet U E) →
      (∃ r v w, c = M.cRel r v w) ∨ (∃ x, c = M.cNeg x) ∨ (∃ φ ψ, c = M.cAnd φ ψ) ∨
        ∃ t n φ, c = M.cAll (M.vr t n) φ := by
    intro sg hm
    obtain ⟨b, k, x, s', e, -, hB⟩ := M.satSet_inv hm
    have ec : c = M.pairN k x := (M.pairN_inj (Subtype.ext (M.fact_inj e).1)).1
    rcases hB with ⟨hk, r, v, w, hx, -⟩ | ⟨hk, -⟩ | ⟨hk, φ, ψ, hx, -⟩ | ⟨hk, t, n, φ, hx, -⟩
    · exact Or.inl ⟨r, v, w, by rw [ec, hk, hx]; rfl⟩
    · exact Or.inr (Or.inl ⟨x, by rw [ec, hk]; rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨φ, ψ, by rw [ec, hk, hx]; rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨t, n, φ, by rw [ec, hk, hx]; rfl⟩))
  rcases h with h | h
  · exact key 1 h
  · exact key 0 h

section hier11

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- The sorts and the relations of the structure of names of rank below `α`. -/
theorem exists_level_structure (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) (α : V) :
    ∃ U E, (∀ k a, M.mem (M.op k a) U ↔ M.mem k M.nat ∧ M.InNRaw P th io M.nat j.1 α a) ∧
      ∀ r a b, M.mem (M.trip r a b) E ↔ M.mem r M.nat ∧ M.InNRaw P th io M.nat j.1 α a ∧
        M.InNRaw P th io M.nat j.1 α b ∧ M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG
          (1 : M.Num).1 (2 : M.Num).1 F α r a b := by
  obtain ⟨U, -, hU0⟩ := M.comp (σW [(0, 4), (20, 7), (22, 5), (24, 5), (27, 3)])
    (Fml.ex 67 (Fml.ex 68 (.and (fPr 0 67 68) (.and (.mem 67 27) inNFml)))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 65 α)
  have hU1 : ∀ q, M.mem q U ↔ ∃ k a, q = M.op k a ∧ M.mem k M.nat ∧
      M.InNRaw P th io M.nat j.1 α a := by
    intro q
    rw [hU0 q]
    simp [Sat, M.sat_ex, M.sat_fPr', M.sat_inNFml, Function.update_apply]
  obtain ⟨E, -, hE0⟩ := M.comp (σW [(0, 6), (6, 5), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3),
      (28, 7), (161, 5), (162, 5)])
    (Fml.ex 67 (Fml.ex 70 (Fml.ex 73 (.and (fTrip 0 67 70 73) (.and (.mem 67 27)
      (.and (Fml.ex 68 (.and (.eq 68 70) inNFml))
      (.and (Fml.ex 68 (.and (.eq 68 73) inNFml))
        (Fml.ex 86 (.and (.eq 86 67) atomAtFml))))))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp)
      22 th) 24 io) 25 j.1) 27 M.nat) 65 α) 23 Nt) 26 d) 28 M.adG) 11 (1 : M.Num).1)
      12 (2 : M.Num).1) 160 qo) 161 Nu) 162 Pr)
  have hE1 : ∀ q, M.mem q E ↔ ∃ r a b, q = M.trip r a b ∧ M.mem r M.nat ∧
      M.InNRaw P th io M.nat j.1 α a ∧ M.InNRaw P th io M.nat j.1 α b ∧
      M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG
          (1 : M.Num).1 (2 : M.Num).1 F α r a b := by
    intro q
    rw [hE0 q]
    simp [Sat, M.sat_ex, M.sat_fTripq', M.sat_inNFml, M.sat_atomAtFml, Function.update_apply]
  refine ⟨U, E, fun k a => ⟨fun h => ?_, fun h => (hU1 _).mpr ⟨k, a, rfl, h⟩⟩,
    fun r a b => ⟨fun h => ?_, fun h => (hE1 _).mpr ⟨r, a, b, rfl, h⟩⟩⟩
  · obtain ⟨k', a', e, h'⟩ := (hU1 _).mp h
    obtain ⟨e1, e2⟩ := M.op_inj e
    rw [e1, e2]
    exact h'
  · obtain ⟨r', a', b', e, h'⟩ := (hE1 _).mp h
    obtain ⟨e1, e2, e3⟩ := M.trip_inj e
    rw [e1, e2, e3]
    exact h'

/-- The step of the comparison of the two truth definitions. -/
theorem bridge_core (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α U E : V}
    (hα : M.mem (M.op α α) th) (hdN : M.InNRaw P th io M.nat j.1 α d)
    (hU : ∀ k a, M.mem (M.op k a) U ↔ M.mem k M.nat ∧ M.InNRaw P th io M.nat j.1 α a)
    (hE : ∀ r a b, M.mem (M.trip r a b) E ↔ M.mem r M.nat ∧ M.InNRaw P th io M.nat j.1 α a ∧
      M.InNRaw P th io M.nat j.1 α b ∧ M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG
          (1 : M.Num).1 (2 : M.Num).1 F α r a b)
    (c : M.Num)
    (ih : ∀ c' : M.Num, c' + 1 ≤ c → ∀ s t, M.IsAsg U s →
      (∀ i : M.Num, i ≤ c' → ∃ e, M.mem (M.op i.1 e) s ∧
        M.ValRaw P th io M.nat Nt j.1 d α t i.1 e) →
      (M.Holds U E c' s → M.TrueAt P io F j.1 α c' t) ∧
      (M.Fails U E c' s → ¬ M.TrueAt P io F j.1 α c' t))
    (s t : V) (hs : M.IsAsg U s)
    (hm : ∀ i : M.Num, i ≤ c → ∃ e, M.mem (M.op i.1 e) s ∧
      M.ValRaw P th io M.nat Nt j.1 d α t i.1 e) :
    (M.Holds U E c s → M.TrueAt P io F j.1 α c t) ∧
    (M.Fails U E c s → ¬ M.TrueAt P io F j.1 α c t) := by
  have sfun : ∀ {i : M.Num} {e e' : V}, M.mem (M.op i.1 e) s → M.mem (M.op i.1 e') s → e = e' := by
    intro i e e' h1 h2
    obtain ⟨a0, -, huniq⟩ := hs.2.2.1 i.1 i.2
    rw [huniq e h1, huniq e' h2]
  have matchv : ∀ {v : M.Num} {a : V}, v ≤ c → M.mem (M.op v.1 a) s →
      M.ValRaw P th io M.nat Nt j.1 d α t v.1 a := by
    intro v a hv ha
    obtain ⟨e, he, hval⟩ := hm v hv
    rw [sfun ha he]
    exact hval
  have matchv' : ∀ {v : M.Num} {a : V}, v ≤ c → M.ValRaw P th io M.nat Nt j.1 d α t v.1 a →
      M.mem (M.op v.1 a) s := by
    intro v a hv ha
    obtain ⟨e, he, hval⟩ := hm v hv
    rw [M.val_unique hd ha hval]
    exact he
  have valN : ∀ {i a : V}, M.ValRaw P th io M.nat Nt j.1 d α t i a →
      M.InNRaw P th io M.nat j.1 α a := by
    rintro i a (⟨-, h⟩ | ⟨-, h⟩)
    · exact h
    · rw [h]
      exact hdN
  -- the assignment and the sequence after changing one variable
  have matchUpd : ∀ (t0 n φ : M.Num), M.cAll (M.vr t0 n) φ ≤ c → ∀ a t',
      M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' (M.vr t0 n).1 a (M.cAll (M.vr t0 n) φ).1 →
      ∀ i : M.Num, i ≤ φ → ∃ e, M.mem (M.op i.1 e) (M.updS s (M.vr t0 n).1 a) ∧
        M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e := by
    intro t0 n φ hle a t' hag i hi
    have hiA : i ≤ M.cAll (M.vr t0 n) φ :=
      le_trans hi (le_trans (M.le_pairN_right _ φ) (M.le_pairN_right 3 _))
    have hraw := (M.leRaw_iff M.adG_spec i (M.cAll (M.vr t0 n) φ)).mpr hiA
    by_cases e : i.1 = (M.vr t0 n).1
    · refine ⟨a, ?_, (hag i.1 i.2 hraw a).mpr (Or.inl ⟨e, rfl⟩)⟩
      rw [e]
      exact M.mem_updS_same.mpr rfl
    · obtain ⟨e0, he0, hv0⟩ := hm i (le_trans hiA hle)
      exact ⟨e0, (M.mem_updS_of_ne e).mpr he0, (hag i.1 i.2 hraw e0).mpr (Or.inr ⟨e, hv0⟩)⟩
  constructor
  · intro hH
    rcases M.shape_of_decided (Or.inl hH) with ⟨r, v, w, e⟩ | ⟨x, e⟩ | ⟨φ, ψ, e⟩ | ⟨t0, n, φ, e⟩
    · subst e
      have hvw : M.pairN v w ≤ M.cRel r v w :=
        le_trans (M.le_pairN_right r _) (M.le_pairN_right 0 _)
      obtain ⟨-, a, b, ha, hb, hE'⟩ := (M.holds_rel r v w s).mp hH
      obtain ⟨-, -, -, heps⟩ := (hE r.1 a b).mp hE'
      exact (M.hier_rel hd r v w t).mpr ⟨hα, a, b,
        matchv (le_trans (M.le_pairN_left v w) hvw) ha,
        matchv (le_trans (M.le_pairN_right v w) hvw) hb, heps⟩
    · subst e
      have lt1 : x + 1 ≤ M.cNeg x := M.lt_pairN_right x (le_refl 1)
      obtain ⟨-, hF⟩ := (M.holds_neg x s).mp hH
      exact (M.hier_neg hd x t).mpr ⟨hα, (ih x lt1 s t hs (fun i hi =>
        hm i (le_trans hi (le_trans (M.le_add_one x) lt1)))).2 hF⟩
    · subst e
      have lt1 : φ + 1 ≤ M.cAnd φ ψ :=
        le_trans (add_le_add (M.le_pairN_left φ ψ) (le_refl 1))
          (M.lt_pairN_right _ M.one_le_two')
      have lt2 : ψ + 1 ≤ M.cAnd φ ψ :=
        le_trans (add_le_add (M.le_pairN_right φ ψ) (le_refl 1))
          (M.lt_pairN_right _ M.one_le_two')
      obtain ⟨-, h1, h2⟩ := (M.holds_and φ ψ s).mp hH
      exact (M.hier_and hd φ ψ t).mpr ⟨hα,
        (ih φ lt1 s t hs (fun i hi => hm i (le_trans hi (le_trans (M.le_add_one φ) lt1)))).1 h1,
        (ih ψ lt2 s t hs (fun i hi => hm i (le_trans hi (le_trans (M.le_add_one ψ) lt2)))).1 h2⟩
    · subst e
      have lt1 : φ + 1 ≤ M.cAll (M.vr t0 n) φ :=
        le_trans (add_le_add (M.le_pairN_right _ φ) (le_refl 1))
          (M.lt_pairN_right _ M.one_le_three')
      obtain ⟨-, hall⟩ := (M.holds_all t0 n φ s).mp hH
      refine (M.hier_all hd (M.vr t0 n) φ t).mpr ⟨hα, fun a t' ha hag => ?_⟩
      have haU : M.mem (M.op t0.1 a) U := (hU t0.1 a).mpr ⟨t0.2, ha⟩
      exact (ih φ lt1 _ t' (M.isAsg_updS hs t0 n haU)
        (matchUpd t0 n φ (le_refl _) a t' hag)).1 (hall a haU)
  · intro hF htr
    rcases M.shape_of_decided (Or.inr hF) with ⟨r, v, w, e⟩ | ⟨x, e⟩ | ⟨φ, ψ, e⟩ | ⟨t0, n, φ, e⟩
    · subst e
      have hvw : M.pairN v w ≤ M.cRel r v w :=
        le_trans (M.le_pairN_right r _) (M.le_pairN_right 0 _)
      obtain ⟨-, hnR⟩ := (M.fails_rel r v w s).mp hF
      obtain ⟨-, a, b, hva, hvb, heps⟩ := (M.hier_rel hd r v w t).mp htr
      exact hnR ⟨a, b, matchv' (le_trans (M.le_pairN_left v w) hvw) hva,
        matchv' (le_trans (M.le_pairN_right v w) hvw) hvb,
        (hE r.1 a b).mpr ⟨r.2, valN hva, valN hvb, heps⟩⟩
    · subst e
      have lt1 : x + 1 ≤ M.cNeg x := M.lt_pairN_right x (le_refl 1)
      obtain ⟨-, hH'⟩ := (M.fails_neg x s).mp hF
      exact ((M.hier_neg hd x t).mp htr).2 ((ih x lt1 s t hs (fun i hi =>
        hm i (le_trans hi (le_trans (M.le_add_one x) lt1)))).1 hH')
    · subst e
      have lt1 : φ + 1 ≤ M.cAnd φ ψ :=
        le_trans (add_le_add (M.le_pairN_left φ ψ) (le_refl 1))
          (M.lt_pairN_right _ M.one_le_two')
      have lt2 : ψ + 1 ≤ M.cAnd φ ψ :=
        le_trans (add_le_add (M.le_pairN_right φ ψ) (le_refl 1))
          (M.lt_pairN_right _ M.one_le_two')
      obtain ⟨-, hcases⟩ := (M.fails_and φ ψ s).mp hF
      obtain ⟨-, h1, h2⟩ := (M.hier_and hd φ ψ t).mp htr
      rcases hcases with ⟨hf, -⟩ | ⟨-, hf⟩
      · exact (ih φ lt1 s t hs (fun i hi =>
          hm i (le_trans hi (le_trans (M.le_add_one φ) lt1)))).2 hf h1
      · exact (ih ψ lt2 s t hs (fun i hi =>
          hm i (le_trans hi (le_trans (M.le_add_one ψ) lt2)))).2 hf h2
    · subst e
      have lt1 : φ + 1 ≤ M.cAll (M.vr t0 n) φ :=
        le_trans (add_le_add (M.le_pairN_right _ φ) (le_refl 1))
          (M.lt_pairN_right _ M.one_le_three')
      obtain ⟨-, -, a, haU, hFa⟩ := (M.fails_all t0 n φ s).mp hF
      obtain ⟨-, hex⟩ := (M.hier_all_ex hd (M.vr t0 n) φ t).mp htr
      obtain ⟨t', hag, htr'⟩ := hex a ((hU t0.1 a).mp haU).2
      exact (ih φ lt1 _ t' (M.isAsg_updS hs t0 n haU)
        (matchUpd t0 n φ (le_refl _) a t' hag)).2 hFa htr'

end hier11

/-- "The two truth definitions agree up to `n`" (name `99`) at stage `α` (name `65`): the
set of assignments, the satisfaction relation and `F` are the names `4`, `8`, `6`. -/
def bridgeFml : Fml :=
  .all 9 (Fml.imp (.mem 9 27) (Fml.imp (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 9 84 99)))
    (.all 5 (.all 80 (Fml.imp (.mem 5 4) (Fml.imp
      (.all 67 (Fml.imp (.mem 67 27) (Fml.imp (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 67 84 9)))
        (Fml.ex 68 (.and (fApp 5 67 68) (Fml.ex 66 (.and (.eq 66 80) valFml)))))))
      (.and (Fml.imp (fLit 8 9 11 5)
          (Fml.ex 85 (Fml.ex 86 (.and (fApp 24 9 85) (.and (fApp4 20 25 65 85 86)
            (fApp 6 86 80))))))
        (Fml.imp (fLit 8 9 10 5)
          (.neg (Fml.ex 85 (Fml.ex 86 (.and (fApp 24 9 85) (.and (fApp4 20 25 65 85 86)
            (fApp 6 86 80))))))))))))))

def σB : ℕ → ℕ :=
  σW [(4, 6), (5, 5), (6, 5), (7, 7), (8, 8), (18, 7), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3),
    (28, 7), (110, 7), (111, 3), (112, 4), (113, 5), (115, 3), (116, 4), (117, 6), (118, 5),
    (119, 4)]

section hier12

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **The levels are set structures in the sense of §3.1, and the two truth definitions
agree.** For a stage `α` above the least one, let `(U, E)` be the set structure whose sorts
are all the set of names of rank below `α` and whose relations are all membership between the
sets denoted. Then for every code `c`, every assignment `s` of the structure and every `t`
whose values at the variables up to `c` are those of `s`: if `c` is true at `s` in the sense
of §3.1 then it is true at stage `α` under `t`, and if it is false at `s` then it is not. -/
theorem hier_structure (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) (hdN : M.InNRaw P th io M.nat j.1 α d) :
    ∃ U E, (∀ k a, M.mem (M.op k a) U ↔ M.mem k M.nat ∧ M.InNRaw P th io M.nat j.1 α a) ∧
      (∀ r a b, M.mem (M.trip r a b) E ↔ M.mem r M.nat ∧ M.InNRaw P th io M.nat j.1 α a ∧
        M.InNRaw P th io M.nat j.1 α b ∧ M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG
          (1 : M.Num).1 (2 : M.Num).1 F α r a b) ∧
      ∀ (c : M.Num) (s t : V), M.IsAsg U s →
        (∀ i : M.Num, i ≤ c → ∃ e, M.mem (M.op i.1 e) s ∧
          M.ValRaw P th io M.nat Nt j.1 d α t i.1 e) →
        (M.Holds U E c s → M.TrueAt P io F j.1 α c t) ∧
        (M.Fails U E c s → ¬ M.TrueAt P io F j.1 α c t) := by
  have had := M.adG_spec
  have hmu := M.muG_spec
  obtain ⟨U, E, hU, hE⟩ := M.exists_level_structure hd α
  refine ⟨U, E, hU, hE, ?_⟩
  obtain ⟨ρ, e4, e6, e7, e8, e10, e11, e18, e20, e22, e23, e24, e25, e26, e27, e28, e65⟩ :
      ∃ ρ : ℕ → V, ρ 4 = M.asg U ∧ ρ 6 = F ∧ ρ 7 = M.adG ∧ ρ 8 = M.satSet U E ∧
        ρ 10 = (0 : M.Num).1 ∧ ρ 11 = (1 : M.Num).1 ∧ ρ 18 = M.muG ∧ ρ 20 = P ∧ ρ 22 = th ∧
        ρ 23 = Nt ∧ ρ 24 = io ∧ ρ 25 = j.1 ∧ ρ 26 = d ∧ ρ 27 = M.nat ∧ ρ 28 = M.adG ∧
        ρ 65 = α :=
    ⟨Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (fun _ => dflt) 4 (M.asg U)) 6 F) 7 M.adG) 8 (M.satSet U E))
      10 (0 : M.Num).1) 11 (1 : M.Num).1) 18 M.muG) 20 P) 22 th) 23 Nt) 24 io) 25 j.1) 26 d)
      27 M.nat) 28 M.adG) 65 α, by simp [Function.update_apply]⟩
  have hsat : ∀ n : M.Num, Sat M.mem M.isSet bridgeFml (Function.update ρ 99 n.1) ↔
      ∀ c : M.Num, c ≤ n → ∀ s t, M.IsAsg U s →
        (∀ i : M.Num, i ≤ c → ∃ e, M.mem (M.op i.1 e) s ∧
          M.ValRaw P th io M.nat Nt j.1 d α t i.1 e) →
        (M.Holds U E c s → M.TrueAt P io F j.1 α c t) ∧
        (M.Fails U E c s → ¬ M.TrueAt P io F j.1 α c t) := by
    intro n
    have h1 : Sat M.mem M.isSet bridgeFml (Function.update ρ 99 n.1) ↔
        ∀ c, M.mem c M.nat → M.LeRaw M.adG c n.1 → ∀ s t, M.mem s (M.asg U) →
          (∀ i, M.mem i M.nat → M.LeRaw M.adG i c → ∃ e, M.mem (M.op i e) s ∧
            M.ValRaw P th io M.nat Nt j.1 d α t i e) →
          (M.LitRaw M.adG M.muG (M.satSet U E) c (1 : M.Num).1 s →
            ∃ ch pt, M.mem (M.op c ch) io ∧ M.mem (M.quad j.1 α ch pt) P ∧
              M.mem (M.op pt t) F) ∧
          (M.LitRaw M.adG M.muG (M.satSet U E) c (0 : M.Num).1 s →
            ¬ ∃ ch pt, M.mem (M.op c ch) io ∧ M.mem (M.quad j.1 α ch pt) P ∧
              M.mem (M.op pt t) F) := by
      simp [bridgeFml, LeRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fApp3', M.sat_fApp4', M.sat_fApp',
        M.sat_fLit, M.sat_valFml, Function.update_apply, e4, e6, e7, e8, e10, e11, e18, e20, e22,
        e23, e24, e25, e26, e27, e28, e65]
    rw [h1]
    constructor
    · intro raw c hc s t hs hm
      have r := raw c.1 c.2 ((M.leRaw_iff had c n).mpr hc) s t (M.mem_asg.mpr hs)
        (fun i hi hle => hm ⟨i, hi⟩ ((M.leRaw_iff had ⟨i, hi⟩ c).mp hle))
      exact ⟨fun hH => r.1 ((M.litRaw_iff had hmu _ c 1 s).mpr hH),
        fun hF htr => r.2 ((M.litRaw_iff had hmu _ c 0 s).mpr hF) htr⟩
    · intro clean c hc hle s t hs hm
      have r := clean ⟨c, hc⟩ ((M.leRaw_iff had ⟨c, hc⟩ n).mp hle) s t (M.mem_asg.mp hs)
        (fun i hi => hm i.1 i.2 ((M.leRaw_iff had i ⟨c, hc⟩).mpr hi))
      exact ⟨fun hH => r.1 ((M.litRaw_iff had hmu _ ⟨c, hc⟩ 1 s).mp hH),
        fun hF htr => r.2 ((M.litRaw_iff had hmu _ ⟨c, hc⟩ 0 s).mp hF) htr⟩
  intro c
  have key := M.num_ind_fml σB bridgeFml 99 rfl ρ
    (by
      rw [show M.zero = (0 : M.Num).1 from rfl, hsat 0]
      intro c0 hc0 s0 t0 hs0 hm0
      exact M.bridge_core hd hα hdN hU hE c0 (fun c' hc' => absurd (le_trans hc' hc0)
        (fun h => M.succ_not_le_zero h)) s0 t0 hs0 hm0)
    (fun k ih => by
      rw [hsat k] at ih
      rw [show M.succ k.1 = (k + 1).1 from (M.val_add_one k).symm, hsat (k + 1)]
      intro c0 hc0 s0 t0 hs0 hm0
      exact M.bridge_core hd hα hdN hU hE c0 (fun c' hc' =>
        ih c' (M.le_of_succ_le_succ (le_trans hc' hc0))) s0 t0 hs0 hm0) c
  rw [hsat c] at key
  exact key c (le_refl c)

end hier12

section hier13

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- For a decided code the two truth definitions agree exactly. -/
theorem holds_iff_trueAt {U E α t s : V} {c : M.Num}
    (hb : (M.Holds U E c s → M.TrueAt P io F j.1 α c t) ∧
      (M.Fails U E c s → ¬ M.TrueAt P io F j.1 α c t))
    (hform : M.Holds U E c s ∨ M.Fails U E c s) :
    M.Holds U E c s ↔ M.TrueAt P io F j.1 α c t :=
  ⟨hb.1, fun htr => hform.resolve_right (fun hF => hb.2 hF htr)⟩

/-- **Every sequence gives an assignment of the level structure**, with the same values. In
particular the structure has assignments. -/
theorem exists_asg_of_seq (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α U : V}
    (hdN : M.InNRaw P th io M.nat j.1 α d)
    (hU : ∀ k a, M.mem (M.op k a) U ↔ M.mem k M.nat ∧ M.InNRaw P th io M.nat j.1 α a) (t : V) :
    ∃ s, M.IsAsg U s ∧ ∀ (i : M.Num) (e : V), M.mem (M.op i.1 e) s ↔
      M.ValRaw P th io M.nat Nt j.1 d α t i.1 e := by
  obtain ⟨s, hss, hs0⟩ := M.comp (σW [(0, 4), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3)])
    (Fml.ex 67 (Fml.ex 68 (.and (fPr 0 67 68) (.and (.mem 67 27)
      (Fml.ex 66 (.and (.eq 66 5) valFml)))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 5 t) 20 P) 22 th)
      23 Nt) 24 io) 25 j.1) 26 d) 27 M.nat |> fun ρ => Function.update ρ 65 α)
  have hs1 : ∀ q, M.mem q s ↔ ∃ i e, q = M.op i e ∧ M.mem i M.nat ∧
      M.ValRaw P th io M.nat Nt j.1 d α t i e := by
    intro q
    rw [hs0 q]
    simp [Sat, M.sat_ex, M.sat_fPr', M.sat_valFml, Function.update_apply]
  have hs : ∀ i e, M.mem (M.op i e) s ↔ M.mem i M.nat ∧
      M.ValRaw P th io M.nat Nt j.1 d α t i e := by
    intro i e
    constructor
    · intro h
      obtain ⟨i', e', eq, h'⟩ := (hs1 _).mp h
      obtain ⟨e1, e2⟩ := M.op_inj eq
      rw [e1, e2]
      exact h'
    · intro h
      exact (hs1 _).mpr ⟨i, e, rfl, h⟩
  refine ⟨s, ⟨hss, fun q hq => ?_, fun i hi => ?_, fun t0 n a h => ?_⟩, fun i e => ?_⟩
  · obtain ⟨i, e, eq, hi, -⟩ := (hs1 q).mp hq
    exact ⟨i, e, hi, eq⟩
  · obtain ⟨e, he⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j)
      α t i
    exact ⟨e, (hs i e).mpr ⟨hi, he⟩, fun b hb => M.val_unique hd ((hs i b).mp hb).2 he⟩
  · rcases ((hs _ a).mp h).2 with ⟨-, hN⟩ | ⟨-, hN⟩
    · exact (hU t0.1 a).mpr ⟨t0.2, hN⟩
    · rw [hN]
      exact (hU t0.1 d).mpr ⟨t0.2, hdN⟩
  · rw [hs i.1 e]
    exact and_iff_right i.2

end hier13

/-! ### Definable subsets are named; the levels increase; unions -/

/-- The code of `∃v c`. -/
noncomputable def cEx (v c : M.Num) : M.Num := M.cNeg (M.cAll v (M.cNeg c))

section hier14

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- The clause for the existential quantifier. -/
theorem hier_ex (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) (v c : M.Num) (t : V) :
    M.TrueAt P io F j.1 α (M.cEx v c) t ↔ ∃ a, M.InNRaw P th io M.nat j.1 α a ∧
      ∃ t', M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v.1 a (M.cAll v (M.cNeg c)).1 ∧
        M.TrueAt P io F j.1 α c t' := by
  unfold cEx
  rw [M.hier_neg hd, M.hier_all hd]
  constructor
  · rintro ⟨-, hn⟩
    by_contra hcon
    exact hn ⟨hα, fun a t' ha hag => (M.hier_neg hd c t').mpr
      ⟨hα, fun htr => hcon ⟨a, ha, t', hag, htr⟩⟩⟩
  · rintro ⟨a, ha, t', hag, htr⟩
    exact ⟨hα, fun hall => ((M.hier_neg hd c t').mp (hall.2 a t' ha hag)).2 htr⟩

/-- **The names of rank `α` denote the definable subsets of the level.** For every stage `α`,
every code `φ` and every `u` in the rung there is a name of rank `α` whose members are exactly
the names `a` of rank below `α` such that `φ` is true at stage `α` under the sequence
`(a, u)`. -/
theorem def_name (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α u : V}
    (hα : M.mem (M.op α α) th) (hu : M.mem (M.op j.1 u) R) (φ : M.Num) :
    ∃ b, M.RankIs P io M.nat j.1 α b ∧ ∀ a, M.EpsRaw P th io M.nat j.1 F a b ↔
      M.InNRaw P th io M.nat j.1 α a ∧
        ∃ s, M.mem (M.quad j.1 a u s) P ∧ M.TrueAt P io F j.1 α φ s := by
  obtain ⟨f, hf⟩ := hd.io_tot φ
  obtain ⟨q, hq⟩ := hd.hP.tot j hd.hj f u (hd.io_dom _ _ hf).2 hu
  obtain ⟨b, hb⟩ := hd.hP.tot j hd.hj α q (hd.th_rung α α hα).1 (hd.hP.dom _ _ _ _ hq).2.2.2
  exact ⟨b, ⟨f, u, q, hb, hq, _, (hd.io_dom _ _ hf).1, hf⟩, fun a => M.eps_iff hd hb hq hf a⟩

/-- **The levels increase.** A name of rank below `α` denotes the same set as some name of
rank `α`. -/
theorem up_name (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α b : V}
    (hα : M.mem (M.op α α) th) (hb : M.InNRaw P th io M.nat j.1 α b) :
    ∃ b', M.RankIs P io M.nat j.1 α b' ∧ M.SimRaw P j.1 tp F b' b := by
  obtain ⟨u, hu⟩ := hd.hP.tot j hd.hj b d (M.inN_rung hd hb) (M.d_rung hd)
  have huR := (hd.hP.dom _ _ _ _ hu).2.2.2
  obtain ⟨b', rb', hmem⟩ := M.def_name hd hα huR (M.cRel 0 0 1)
  obtain ⟨β, rb, hβα, -⟩ := M.inN_rank hb
  have hβ : M.mem (M.op β β) th := (hd.hth.fld β α hβα).1
  have key : ∀ x, M.EpsRaw P th io M.nat j.1 F x b' ↔
      M.InNRaw P th io M.nat j.1 α x ∧ M.EpsStarRaw P th io M.nat j.1 tp F x b := by
    intro x
    rw [hmem x]
    have vals : ∀ s, M.InNRaw P th io M.nat j.1 α x → M.mem (M.quad j.1 x u s) P →
        (M.TrueAt P io F j.1 α (M.cRel 0 0 1) s ↔ M.EpsStarRaw P th io M.nat j.1 tp F x b) := by
      intro s hx hs
      have v0 : M.ValRaw P th io M.nat Nt j.1 d α s (0 : M.Num).1 x :=
        Or.inl ⟨(hd.nt_zero s x).mpr ⟨u, hs⟩, hx⟩
      have n1 : M.mem (M.trip s (1 : M.Num).1 b) Nt := by
        have h1 := (M.nth_cons_succ hd hs 0 b).mpr ((hd.nt_zero u b).mpr ⟨d, hu⟩)
        rwa [zero_add] at h1
      exact M.rel_val hd 0 1 hα v0 (Or.inl ⟨n1, hb⟩)
    constructor
    · rintro ⟨hx, s, hs, htr⟩
      exact ⟨hx, (vals s hx hs).mp htr⟩
    · rintro ⟨hx, heps⟩
      obtain ⟨s, hs⟩ := hd.hP.tot j hd.hj x u (M.inN_rung hd hx) huR
      exact ⟨hx, s, hs, (vals s hx hs).mpr heps⟩
  refine ⟨b', rb', (M.hier_sim hd rb' rb hα hβ).mpr ⟨fun x hx => ?_, fun x' hx' => ?_⟩⟩
  · obtain ⟨-, x'', hs, he⟩ := (key x).mp hx
    exact ⟨x'', he, hs⟩
  · have hx'β := M.eps_inN_rank hd rb hx'
    have hx'α := M.inN_mono hd hx'β hβα
    obtain ⟨βx, rx, hβx, -⟩ := M.inN_rank hx'β
    have hrefl := M.sim_refl hd rx (hd.hth.fld βx β hβx).1
    exact ⟨x', (key x').mpr ⟨hx'α, x', hrefl, hx'⟩, hrefl⟩

/-- **Unions.** For a name `b` of rank below `α` there is a name of rank `α` whose members are
the names of rank below `α` that denote a member of a member of the set denoted by `b`. -/
theorem union_name (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α b : V}
    (hα : M.mem (M.op α α) th) (hb : M.InNRaw P th io M.nat j.1 α b) :
    ∃ c, M.RankIs P io M.nat j.1 α c ∧ ∀ x, M.EpsRaw P th io M.nat j.1 F x c ↔
      M.InNRaw P th io M.nat j.1 α x ∧ ∃ y, M.InNRaw P th io M.nat j.1 α y ∧
        M.EpsStarRaw P th io M.nat j.1 tp F x y ∧ M.EpsStarRaw P th io M.nat j.1 tp F y b := by
  obtain ⟨u, hu⟩ := hd.hP.tot j hd.hj b d (M.inN_rung hd hb) (M.d_rung hd)
  have huR := (hd.hP.dom _ _ _ _ hu).2.2.2
  obtain ⟨c, rc, hmem⟩ := M.def_name hd hα huR
    (M.cEx 2 (M.cAnd (M.cRel 0 0 2) (M.cRel 0 2 1)))
  refine ⟨c, rc, fun x => ?_⟩
  rw [hmem x]
  have key : ∀ s, M.InNRaw P th io M.nat j.1 α x → M.mem (M.quad j.1 x u s) P →
      (M.TrueAt P io F j.1 α (M.cEx 2 (M.cAnd (M.cRel 0 0 2) (M.cRel 0 2 1))) s ↔
        ∃ y, M.InNRaw P th io M.nat j.1 α y ∧ M.EpsStarRaw P th io M.nat j.1 tp F x y ∧
          M.EpsStarRaw P th io M.nat j.1 tp F y b) := by
    intro s hx hs
    have v0 : M.ValRaw P th io M.nat Nt j.1 d α s (0 : M.Num).1 x :=
      Or.inl ⟨(hd.nt_zero s x).mpr ⟨u, hs⟩, hx⟩
    have n1 : M.mem (M.trip s (1 : M.Num).1 b) Nt := by
      have h1 := (M.nth_cons_succ hd hs 0 b).mpr ((hd.nt_zero u b).mpr ⟨d, hu⟩)
      rwa [zero_add] at h1
    have v1 : M.ValRaw P th io M.nat Nt j.1 d α s (1 : M.Num).1 b := Or.inl ⟨n1, hb⟩
    have hbody : M.cAnd (M.cRel 0 0 2) (M.cRel 0 2 1) ≤
        M.cAll 2 (M.cNeg (M.cAnd (M.cRel 0 0 2) (M.cRel 0 2 1))) :=
      le_trans (M.le_pairN_right 1 _) (le_trans (M.le_pairN_right 2 _) (M.le_pairN_right 3 _))
    have h02 : M.pairN 0 2 ≤ M.cAnd (M.cRel 0 0 2) (M.cRel 0 2 1) :=
      le_trans (le_trans (M.le_pairN_right 0 _) (M.le_pairN_right 0 _))
        (le_trans (M.le_pairN_left _ _) (M.le_pairN_right 2 _))
    have h21 : M.pairN 2 1 ≤ M.cAnd (M.cRel 0 0 2) (M.cRel 0 2 1) :=
      le_trans (le_trans (M.le_pairN_right 0 _) (M.le_pairN_right 0 _))
        (le_trans (M.le_pairN_right _ _) (M.le_pairN_right 2 _))
    have le0 := le_trans (M.le_pairN_left 0 2) (le_trans h02 hbody)
    have le2 := le_trans (M.le_pairN_right 0 2) (le_trans h02 hbody)
    have le1 := le_trans (M.le_pairN_right 2 1) (le_trans h21 hbody)
    have body : ∀ y t', M.AgreeRaw P th io M.nat Nt j.1 d M.adG α s t' (2 : M.Num).1 y
        (M.cAll 2 (M.cNeg (M.cAnd (M.cRel 0 0 2) (M.cRel 0 2 1)))).1 →
        (M.TrueAt P io F j.1 α (M.cAnd (M.cRel 0 0 2) (M.cRel 0 2 1)) t' ↔
          (M.EpsStarRaw P th io M.nat j.1 tp F x y ∧ M.EpsStarRaw P th io M.nat j.1 tp F y b)) := by
      intro y t' hag
      have k2 : M.ValRaw P th io M.nat Nt j.1 d α t' (2 : M.Num).1 y :=
        (hag _ (2 : M.Num).2 ((M.leRaw_iff M.adG_spec 2 _).mpr le2) y).mpr (Or.inl ⟨rfl, rfl⟩)
      have k0 : M.ValRaw P th io M.nat Nt j.1 d α t' (0 : M.Num).1 x :=
        (hag _ (0 : M.Num).2 ((M.leRaw_iff M.adG_spec 0 _).mpr le0) x).mpr
          (Or.inr ⟨fun e => M.n20 (Subtype.ext e).symm, v0⟩)
      have k1 : M.ValRaw P th io M.nat Nt j.1 d α t' (1 : M.Num).1 b :=
        (hag _ (1 : M.Num).2 ((M.leRaw_iff M.adG_spec 1 _).mpr le1) b).mpr
          (Or.inr ⟨fun e => M.n21 (Subtype.ext e).symm, v1⟩)
      rw [M.hier_and hd, M.rel_val hd 0 2 hα k0 k2, M.rel_val hd 2 1 hα k2 k1]
      exact and_iff_right hα
    rw [M.hier_ex hd hα]
    constructor
    · rintro ⟨y, hy, t', hag, htr⟩
      exact ⟨y, hy, (body y t' hag).mp htr⟩
    · rintro ⟨y, hy, h⟩
      obtain ⟨t', hag⟩ := M.exists_upd hd hy s (2 : M.Num).1
        (M.cAll 2 (M.cNeg (M.cAnd (M.cRel 0 0 2) (M.cRel 0 2 1))))
      exact ⟨y, hy, t', hag, (body y t' hag).mpr h⟩
  constructor
  · rintro ⟨hx, s, hs, htr⟩
    exact ⟨hx, (key s hx hs).mp htr⟩
  · rintro ⟨hx, h⟩
    obtain ⟨s, hs⟩ := hd.hP.tot j hd.hj x u (M.inN_rung hd hx) huR
    exact ⟨hx, s, hs, (key s hx hs).mpr h⟩

end hier14

/-! ### The default name; limit stages -/

/-- `l` is a limit stage of `th`: above every stage below `l` there is another stage below
`l`. -/
def IsLim (th l : V) : Prop :=
  M.mem (M.op l l) th ∧ ∀ β, M.mem (M.op β l) th → β ≠ l →
    ∃ γ, M.mem (M.op β γ) th ∧ β ≠ γ ∧ M.mem (M.op γ l) th ∧ γ ≠ l

section hier15

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem rank_inN {α β a : V} (h : M.RankIs P io M.nat j.1 β a) (hlt : M.mem (M.op β α) th)
    (hne : β ≠ α) : M.InNRaw P th io M.nat j.1 α a := by
  obtain ⟨f, u, q, h1, h2, h3⟩ := h
  exact ⟨β, f, u, q, h1, h2, hlt, hne, h3⟩

/-- Two names of rank below a limit stage have rank below a common earlier stage. -/
theorem inN_lim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l a b : V}
    (hl : M.IsLim th l) (ha : M.InNRaw P th io M.nat j.1 l a)
    (hb : M.InNRaw P th io M.nat j.1 l b) :
    ∃ γ, M.mem (M.op γ l) th ∧ γ ≠ l ∧ M.InNRaw P th io M.nat j.1 γ a ∧
      M.InNRaw P th io M.nat j.1 γ b := by
  obtain ⟨βa, fa, ua, qa, a1, a2, a3, a4, a5⟩ := ha
  obtain ⟨βb, fb, ub, qb, b1, b2, b3, b4, b5⟩ := hb
  rcases M.wo_total hd.hth (hd.hth.fld βa l a3).1 (hd.hth.fld βb l b3).1 with h | h
  · obtain ⟨γ, g1, g2, g3, g4⟩ := hl.2 βb b3 b4
    refine ⟨γ, g3, g4, ⟨βa, fa, ua, qa, a1, a2, hd.hth.trans βa βb γ h g1, fun e => ?_, a5⟩,
      ⟨βb, fb, ub, qb, b1, b2, g1, g2, b5⟩⟩
    rw [e] at h
    exact g2 (hd.hth.antisymm βb γ g1 h)
  · obtain ⟨γ, g1, g2, g3, g4⟩ := hl.2 βa a3 a4
    refine ⟨γ, g3, g4, ⟨βa, fa, ua, qa, a1, a2, g1, g2, a5⟩,
      ⟨βb, fb, ub, qb, b1, b2, hd.hth.trans βb βa γ h g1, fun e => ?_, b5⟩⟩
    rw [e] at h
    exact g2 (hd.hth.antisymm βa γ g1 h)

/-- **Limit levels are closed under pairs.** -/
theorem pair_lim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l a b : V}
    (hl : M.IsLim th l) (ha : M.InNRaw P th io M.nat j.1 l a)
    (hb : M.InNRaw P th io M.nat j.1 l b) :
    ∃ c, M.InNRaw P th io M.nat j.1 l c ∧ ∀ x, M.EpsStarRaw P th io M.nat j.1 tp F x c ↔
      (M.SimRaw P j.1 tp F x a ∨ M.SimRaw P j.1 tp F x b) := by
  obtain ⟨γ, g1, g2, ha', hb'⟩ := M.inN_lim hd hl ha hb
  obtain ⟨c, rc, hmem⟩ := M.pair_name hd (hd.hth.fld γ l g1).1 ha' hb'
  refine ⟨c, M.rank_inN rc g1 g2, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨x', hs, he⟩
    rcases ((hmem x').mp he).2 with h | h
    · exact Or.inl (M.sim_trans hd hs h)
    · exact Or.inr (M.sim_trans hd hs h)
  · rintro (h | h)
    · exact ⟨a, h, (hmem a).mpr ⟨ha', Or.inl (M.inN_refl hd ha')⟩⟩
    · exact ⟨b, h, (hmem b).mpr ⟨hb', Or.inr (M.inN_refl hd hb')⟩⟩

/-- **Limit levels are closed under unions.** -/
theorem union_lim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l b : V}
    (hl : M.IsLim th l) (hb : M.InNRaw P th io M.nat j.1 l b) :
    ∃ c, M.InNRaw P th io M.nat j.1 l c ∧ ∀ x, M.EpsStarRaw P th io M.nat j.1 tp F x c ↔
      ∃ y, M.EpsStarRaw P th io M.nat j.1 tp F x y ∧ M.EpsStarRaw P th io M.nat j.1 tp F y b := by
  obtain ⟨γ, g1, g2, hb', -⟩ := M.inN_lim hd hl hb hb
  obtain ⟨c, rc, hmem⟩ := M.union_name hd (hd.hth.fld γ l g1).1 hb'
  refine ⟨c, M.rank_inN rc g1 g2, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨x', hs, he⟩
    obtain ⟨-, y, hy, h1, h2⟩ := (hmem x').mp he
    exact ⟨y, M.epsStar_congr hd (M.sim_symm hd hs) (M.inN_refl hd hy) h1, h2⟩
  · rintro ⟨y, hxy, y', hsy, hy'⟩
    have hy'N := M.eps_rank hd hb' hy'
    have hxx : M.SimRaw P j.1 tp F x x := by
      obtain ⟨x0, hs0, -⟩ := hxy
      obtain ⟨β, -, ra, -, hβ, -⟩ := M.sim_names hd hs0
      exact M.sim_refl hd ra hβ
    obtain ⟨x'', hs'', hx''⟩ := M.epsStar_congr hd hxx hsy hxy
    have hx''N := M.eps_rank hd hy'N hx''
    exact ⟨x'', hs'', (hmem x'').mpr ⟨hx''N, y', hy'N,
      ⟨x'', M.inN_refl hd hx''N, hx''⟩, ⟨y', M.inN_refl hd hy'N, hy'⟩⟩⟩

/-- **Earlier levels are members of later levels.** -/
theorem level_mem (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α β : V}
    (hlt : M.mem (M.op β α) th) (hne : β ≠ α) :
    ∃ c, M.InNRaw P th io M.nat j.1 α c ∧
      ∀ a, M.EpsRaw P th io M.nat j.1 F a c ↔ M.InNRaw P th io M.nat j.1 β a := by
  obtain ⟨c, rc, hmem⟩ := M.level_name hd (hd.hth.fld β α hlt).1
  exact ⟨c, M.rank_inN rc hlt hne, hmem⟩

end hier15

/-! ### Foundation; the levels as models -/

section hier16

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **Foundation.** A set that contains a name and is closed under "denote the same set" has
a member `b` such that no member of the set denotes a member of the set denoted by `b`. -/
theorem eps_wf (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {X a β : V}
    (ha : M.mem a X) (ra : M.RankIs P io M.nat j.1 β a) (hβ : M.mem (M.op β β) th)
    (hcl : ∀ x x', M.mem x X → M.SimRaw P j.1 tp F x' x → M.mem x' X) :
    ∃ b, M.mem b X ∧ ∀ x, M.mem x X → ¬ M.EpsStarRaw P th io M.nat j.1 tp F x b := by
  obtain ⟨B, -, hB0⟩ := M.comp (σW [(20, 7), (22, 5), (24, 5), (27, 3), (110, 3)])
    (.and (fApp 22 74 74) (Fml.ex 72 (.and rankFml (.mem 72 110)))) 74 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (fun _ => dflt) 20 P) 22 th) 24 io) 25 j.1) 27 M.nat) 110 X)
  have hB : ∀ β, M.mem β B ↔ M.mem (M.op β β) th ∧ ∃ a, M.RankIs P io M.nat j.1 β a ∧
      M.mem a X := by
    intro β
    rw [hB0 β]
    simp [Sat, M.sat_ex, M.sat_fApp', M.sat_rankFml, Function.update_apply]
  obtain ⟨β0, hβ0B, hβ0, hmin⟩ := hd.hth.least B ⟨β, (hB β).mpr ⟨hβ, a, ra, ha⟩, hβ⟩
  obtain ⟨-, b, rb, hbX⟩ := (hB β0).mp hβ0B
  refine ⟨b, hbX, fun x hx hxb => ?_⟩
  obtain ⟨x', hs, he⟩ := hxb
  obtain ⟨βx, rx, ltx, nex⟩ := M.inN_rank (M.eps_inN_rank hd rb he)
  have hx'X : M.mem x' X := hcl x x' hx (M.sim_symm hd hs)
  exact nex (hd.hth.antisymm βx β0 ltx (hmin βx ((hB βx).mpr
    ⟨(hd.hth.fld βx β0 ltx).1, x', rx, hx'X⟩) (hd.hth.fld βx β0 ltx).1))

/-- **The levels as models.** For a stage `α` above the least one there is a set structure
`(U, E)` in the sense of §3.1, with every sort the set of names of rank below `α` and every
relation membership between the sets denoted, such that every sequence `t` has an assignment
`s` with the same values, and for every code `c` that the structure decides, `c` is true at
`s` in the sense of §3.1 if and only if it is true at stage `α` under `t`. -/
theorem level_models (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) (hdN : M.InNRaw P th io M.nat j.1 α d) :
    ∃ U E, (∀ k a, M.mem (M.op k a) U ↔ M.mem k M.nat ∧ M.InNRaw P th io M.nat j.1 α a) ∧
      (∀ r a b, M.mem (M.trip r a b) E ↔ M.mem r M.nat ∧ M.InNRaw P th io M.nat j.1 α a ∧
        M.InNRaw P th io M.nat j.1 α b ∧ M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG
          (1 : M.Num).1 (2 : M.Num).1 F α r a b) ∧
      ∀ t, ∃ s, M.IsAsg U s ∧
        (∀ (i : M.Num) (e : V), M.mem (M.op i.1 e) s ↔
          M.ValRaw P th io M.nat Nt j.1 d α t i.1 e) ∧
        ∀ c : M.Num, M.Form U E c → (M.Holds U E c s ↔ M.TrueAt P io F j.1 α c t) := by
  obtain ⟨U, E, hU, hE, hbr⟩ := M.hier_structure hd hα hdN
  refine ⟨U, E, hU, hE, fun t => ?_⟩
  obtain ⟨s, hs, hval⟩ := M.exists_asg_of_seq hd hdN hU t
  refine ⟨s, hs, hval, fun c hc => M.holds_iff_trueAt (hbr c s t hs (fun i _ => ?_)) (hc s hs)⟩
  obtain ⟨e, he⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j)
    α t i.1
  exact ⟨e, (hval i e).mpr he, he⟩

end hier16

/-! ### Bounded formulas are absolute between the levels -/

/-- The code of `∀v (v ε w → c)`. -/
noncomputable def cBAll (v w c : M.Num) : M.Num :=
  M.cAll v (M.cNeg (M.cAnd (M.cRel 0 v w) (M.cNeg c)))

theorem cBAll_bounds (v w c : M.Num) :
    v ≤ M.cBAll v w c ∧ w ≤ M.cBAll v w c ∧ c + 1 ≤ M.cBAll v w c := by
  have hand : M.cAnd (M.cRel 0 v w) (M.cNeg c) ≤ M.cBAll v w c :=
    le_trans (M.le_pairN_right 1 _) (le_trans (M.le_pairN_right v _) (M.le_pairN_right 3 _))
  have hrel : M.cRel 0 v w ≤ M.cBAll v w c :=
    le_trans (le_trans (M.le_pairN_left _ (M.cNeg c)) (M.le_pairN_right 2 _)) hand
  have hneg : M.cNeg c ≤ M.cBAll v w c :=
    le_trans (le_trans (M.le_pairN_right (M.cRel 0 v w) _) (M.le_pairN_right 2 _)) hand
  have hvw : M.pairN v w ≤ M.cRel 0 v w :=
    le_trans (M.le_pairN_right 0 _) (M.le_pairN_right 0 _)
  exact ⟨le_trans (M.le_pairN_left v w) (le_trans hvw hrel),
    le_trans (M.le_pairN_right v w) (le_trans hvw hrel),
    le_trans (M.lt_pairN_right c (le_refl 1)) hneg⟩

/-- `D` is a set of codes of bounded formulas: every member is atomic (with a relation symbol
other than `1`, `2`, so that it means membership), or the negation or
the conjunction of members, or `∀v (v ε w → x)` with `x` a member and `v ≠ w`. -/
def IsD0 (D : V) : Prop :=
  ∀ c : M.Num, M.mem c.1 D →
    (∃ r v w : M.Num, r ≠ 1 ∧ r ≠ 2 ∧ c = M.cRel r v w) ∨
      (∃ x : M.Num, M.mem x.1 D ∧ c = M.cNeg x) ∨
    (∃ x y : M.Num, M.mem x.1 D ∧ M.mem y.1 D ∧ c = M.cAnd x y) ∨
    ∃ v w x : M.Num, v ≠ w ∧ M.mem x.1 D ∧ c = M.cBAll v w x

section hier17

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem val_inN {γ t i e : V} (hdγ : M.InNRaw P th io M.nat j.1 γ d)
    (h : M.ValRaw P th io M.nat Nt j.1 d γ t i e) : M.InNRaw P th io M.nat j.1 γ e := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact h
  · rw [h]
    exact hdγ

/-- A value at a later stage that is a name of rank below an earlier stage is the value at
the earlier stage. -/
theorem val_down (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {γ α t i e : V}
    (hγα : M.mem (M.op γ α) th) (h : M.ValRaw P th io M.nat Nt j.1 d α t i e)
    (he : M.InNRaw P th io M.nat j.1 γ e) : M.ValRaw P th io M.nat Nt j.1 d γ t i e := by
  rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, he⟩
  · exact Or.inr ⟨fun ⟨e', k1, k2⟩ => h1 ⟨e', k1, M.inN_mono hd k2 hγα⟩, h2⟩

theorem val_iff_of_down (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {γ α t i : V}
    (hγα : M.mem (M.op γ α) th)
    (h : ∀ e, M.ValRaw P th io M.nat Nt j.1 d α t i e → M.InNRaw P th io M.nat j.1 γ e) (e : V) :
    M.ValRaw P th io M.nat Nt j.1 d γ t i e ↔ M.ValRaw P th io M.nat Nt j.1 d α t i e := by
  constructor
  · intro hγe
    obtain ⟨e0, he0⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j)
      α t i
    rw [M.val_unique hd hγe (M.val_down hd hγα he0 (h e0 he0))]
    exact he0
  · intro hαe
    exact M.val_down hd hγα hαe (h e hαe)

/-- The clause for the bounded quantifier. -/
theorem hier_ball (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t b : V}
    (hα : M.mem (M.op α α) th) (v w c : M.Num) (hvw : v ≠ w)
    (hw : M.ValRaw P th io M.nat Nt j.1 d α t w.1 b) :
    M.TrueAt P io F j.1 α (M.cBAll v w c) t ↔ ∀ a t', M.InNRaw P th io M.nat j.1 α a →
      M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v.1 a (M.cBAll v w c).1 →
      M.EpsStarRaw P th io M.nat j.1 tp F a b → M.TrueAt P io F j.1 α c t' := by
  obtain ⟨lev, lew, -⟩ := M.cBAll_bounds v w c
  have hbody : ∀ a t', M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v.1 a (M.cBAll v w c).1 →
      (M.TrueAt P io F j.1 α (M.cNeg (M.cAnd (M.cRel 0 v w) (M.cNeg c))) t' ↔
        (M.EpsStarRaw P th io M.nat j.1 tp F a b → M.TrueAt P io F j.1 α c t')) := by
    intro a t' hag
    have kv : M.ValRaw P th io M.nat Nt j.1 d α t' v.1 a :=
      (hag v.1 v.2 ((M.leRaw_iff M.adG_spec v _).mpr lev) a).mpr (Or.inl ⟨rfl, rfl⟩)
    have kw : M.ValRaw P th io M.nat Nt j.1 d α t' w.1 b :=
      (hag w.1 w.2 ((M.leRaw_iff M.adG_spec w _).mpr lew) b).mpr
        (Or.inr ⟨fun e => hvw (Subtype.ext e).symm, hw⟩)
    rw [M.hier_neg hd, M.hier_and hd, M.rel_val hd v w hα kv kw, M.hier_neg hd]
    constructor
    · rintro ⟨-, hn⟩ he
      by_contra hc
      exact hn ⟨hα, he, hα, hc⟩
    · intro h
      exact ⟨hα, fun hh => hh.2.2.2 (h hh.2.1)⟩
  have hunf : M.cBAll v w c = M.cAll v (M.cNeg (M.cAnd (M.cRel 0 v w) (M.cNeg c))) := rfl
  rw [hunf, M.hier_all hd, ← hunf]
  constructor
  · rintro ⟨-, hall⟩ a t' ha hag he
    exact (hbody a t' hag).mp (hall a t' ha hag) he
  · intro h
    exact ⟨hα, fun a t' ha hag => (hbody a t' hag).mpr (h a t' ha hag)⟩

/-- The step of the absoluteness of bounded formulas. -/
theorem d0_core (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {γ α D : V}
    (hγα : M.mem (M.op γ α) th) (hdγ : M.InNRaw P th io M.nat j.1 γ d) (hD : M.IsD0 D)
    (c : M.Num) (hc : M.mem c.1 D)
    (ih : ∀ c' : M.Num, c' + 1 ≤ c → M.mem c'.1 D → ∀ t,
      (∀ i : M.Num, i ≤ c' → ∀ e, (M.ValRaw P th io M.nat Nt j.1 d γ t i.1 e ↔
        M.ValRaw P th io M.nat Nt j.1 d α t i.1 e)) →
      (M.TrueAt P io F j.1 γ c' t ↔ M.TrueAt P io F j.1 α c' t))
    (t : V) (hv : ∀ i : M.Num, i ≤ c → ∀ e, (M.ValRaw P th io M.nat Nt j.1 d γ t i.1 e ↔
      M.ValRaw P th io M.nat Nt j.1 d α t i.1 e)) :
    M.TrueAt P io F j.1 γ c t ↔ M.TrueAt P io F j.1 α c t := by
  have hγ : M.mem (M.op γ γ) th := (hd.hth.fld γ α hγα).1
  have hα : M.mem (M.op α α) th := (hd.hth.fld γ α hγα).2
  rcases hD c hc with ⟨r, v, w, hr1, hr2, e⟩ | ⟨x, hx, e⟩ | ⟨x, y, hx, hy, e⟩ |
    ⟨v, w, x, hvw, hx, e⟩
  · subst e
    have hvw : M.pairN v w ≤ M.cRel r v w :=
      le_trans (M.le_pairN_right r _) (M.le_pairN_right 0 _)
    have lev := le_trans (M.le_pairN_left v w) hvw
    have lew := le_trans (M.le_pairN_right v w) hvw
    rw [M.hier_relE hd r v w hr1 hr2, M.hier_relE hd r v w hr1 hr2]
    constructor
    · rintro ⟨-, a, b, ha, hb, he⟩
      exact ⟨hα, a, b, (hv v lev a).mp ha, (hv w lew b).mp hb, he⟩
    · rintro ⟨-, a, b, ha, hb, he⟩
      exact ⟨hγ, a, b, (hv v lev a).mpr ha, (hv w lew b).mpr hb, he⟩
  · subst e
    have lt1 : x + 1 ≤ M.cNeg x := M.lt_pairN_right x (le_refl 1)
    have hx' := ih x lt1 hx t (fun i hi => hv i (le_trans hi (le_trans (M.le_add_one x) lt1)))
    rw [M.hier_neg hd, M.hier_neg hd, hx']
    exact ⟨fun h => ⟨hα, h.2⟩, fun h => ⟨hγ, h.2⟩⟩
  · subst e
    have lt1 : x + 1 ≤ M.cAnd x y :=
      le_trans (add_le_add (M.le_pairN_left x y) (le_refl 1))
        (M.lt_pairN_right _ M.one_le_two')
    have lt2 : y + 1 ≤ M.cAnd x y :=
      le_trans (add_le_add (M.le_pairN_right x y) (le_refl 1))
        (M.lt_pairN_right _ M.one_le_two')
    have hx' := ih x lt1 hx t (fun i hi => hv i (le_trans hi (le_trans (M.le_add_one x) lt1)))
    have hy' := ih y lt2 hy t (fun i hi => hv i (le_trans hi (le_trans (M.le_add_one y) lt2)))
    rw [M.hier_and hd, M.hier_and hd, hx', hy']
    exact ⟨fun h => ⟨hα, h.2⟩, fun h => ⟨hγ, h.2⟩⟩
  · subst e
    obtain ⟨lev, lew, lt1⟩ := M.cBAll_bounds v w x
    have lex : x ≤ M.cBAll v w x := le_trans (M.le_add_one x) lt1
    obtain ⟨b, hbγ⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d) (j := j)
      γ t w.1
    have hbα := (hv w lew b).mp hbγ
    have hbN : M.InNRaw P th io M.nat j.1 γ b := M.val_inN hdγ hbγ
    have raw : ∀ i : M.Num, i ≤ M.cBAll v w x →
        ∃ z, M.mem z M.nat ∧ M.mem (M.trip i.1 z (M.cBAll v w x).1) M.adG :=
      fun i hi => (M.leRaw_iff M.adG_spec i _).mpr hi
    -- a sequence changed at stage `α` to a name of rank below `γ`, against one changed at `γ`
    have mid : ∀ a0 t2 t3, M.InNRaw P th io M.nat j.1 γ a0 →
        M.AgreeRaw P th io M.nat Nt j.1 d M.adG γ t t2 v.1 a0 (M.cBAll v w x).1 →
        M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t3 v.1 a0 (M.cBAll v w x).1 →
        (M.TrueAt P io F j.1 γ x t2 ↔ M.TrueAt P io F j.1 α x t3) := by
      intro a0 t2 t3 ha0 hag2 hag3
      have hv3 : ∀ i : M.Num, i ≤ M.cBAll v w x → ∀ e,
          (M.ValRaw P th io M.nat Nt j.1 d γ t3 i.1 e ↔
            M.ValRaw P th io M.nat Nt j.1 d α t3 i.1 e) := by
        intro i hi e
        refine M.val_iff_of_down hd hγα (fun e' he' => ?_) e
        rcases (hag3 i.1 i.2 (raw i hi) e').mp he' with ⟨-, h⟩ | ⟨-, h⟩
        · rw [h]
          exact ha0
        · exact M.val_inN hdγ ((hv i hi e').mpr h)
      have h3 := ih x lt1 hx t3 (fun i hi => hv3 i (le_trans hi lex))
      have h23 : M.TrueAt P io F j.1 γ x t2 ↔ M.TrueAt P io F j.1 γ x t3 := by
        refine M.coin_hier hd x t2 t3 (fun i hi e => ?_)
        have hiC := le_trans hi lex
        rw [hag2 i.1 i.2 (raw i hiC) e, hv3 i hiC e, hag3 i.1 i.2 (raw i hiC) e, hv i hiC e]
      exact h23.trans h3
    rw [M.hier_ball hd hγ v w x hvw hbγ, M.hier_ball hd hα v w x hvw hbα]
    constructor
    · intro h a t' ha hag he
      obtain ⟨a', hs, hea'⟩ := he
      have ha'γ : M.InNRaw P th io M.nat j.1 γ a' := M.eps_rank hd hbN hea'
      have ha'α := M.inN_mono hd ha'γ hγα
      obtain ⟨t2, hag2⟩ := M.exists_upd hd ha'γ t v.1 (M.cBAll v w x)
      obtain ⟨t3, hag3⟩ := M.exists_upd hd ha'α t v.1 (M.cBAll v w x)
      have htr2 := h a' t2 ha'γ hag2 ⟨a', M.inN_refl hd ha'γ, hea'⟩
      have htr3 := (mid a' t2 t3 ha'γ hag2 hag3).mp htr2
      refine (M.inv_hier hd x t3 t' (fun i hi => ?_)).mp htr3
      have hiC := le_trans hi lex
      by_cases hiv : i.1 = v.1
      · exact ⟨a', a, (hag3 i.1 i.2 (raw i hiC) a').mpr (Or.inl ⟨hiv, rfl⟩),
          (hag i.1 i.2 (raw i hiC) a).mpr (Or.inl ⟨hiv, rfl⟩), M.sim_symm hd hs⟩
      · obtain ⟨e, he⟩ := M.val_exists (P := P) (th := th) (io := io) (Nt := Nt) (d := d)
          (j := j) α t i.1
        have heN := M.val_inN hdγ ((hv i hiC e).mpr he)
        exact ⟨e, e, (hag3 i.1 i.2 (raw i hiC) e).mpr (Or.inr ⟨hiv, he⟩),
          (hag i.1 i.2 (raw i hiC) e).mpr (Or.inr ⟨hiv, he⟩), M.inN_refl hd heN⟩
    · intro h a t' ha hag he
      have haα := M.inN_mono hd ha hγα
      obtain ⟨t3, hag3⟩ := M.exists_upd hd haα t v.1 (M.cBAll v w x)
      exact (mid a t' t3 ha hag hag3).mpr (h a t3 haα hag3 he)

end hier17

/-- "Bounded formulas up to `n` (name `99`) in `D` (name `121`) have the same truth value at
the stages `γ` (name `120`) and `α` (name `65`)". -/
def d0Fml : Fml :=
  .all 9 (Fml.imp (.mem 9 27) (Fml.imp (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 9 84 99)))
    (Fml.imp (.mem 9 121) (.all 80 (Fml.imp
      (.all 67 (Fml.imp (.mem 67 27) (Fml.imp (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 67 84 9)))
        (.all 68 (Fml.iff
          (Fml.ex 65 (.and (.eq 65 120) (Fml.ex 66 (.and (.eq 66 80) valFml))))
          (Fml.ex 66 (.and (.eq 66 80) valFml)))))))
      (Fml.iff
        (Fml.ex 85 (Fml.ex 86 (.and (fApp 24 9 85) (.and (fApp4 20 25 120 85 86)
          (fApp 6 86 80)))))
        (Fml.ex 85 (Fml.ex 86 (.and (fApp 24 9 85) (.and (fApp4 20 25 65 85 86)
          (fApp 6 86 80)))))))))))

section hier18

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **Bounded formulas are absolute between the levels.** Let `γ` be a stage above the least
one and `α` a later stage. Let `D` be a set of codes of bounded formulas (`IsD0`), `c` a
member of `D`, and `t` a sequence whose values at the variables up to `c` are the same at the
two stages. Then `c` is true at stage `γ` under `t` if and only if it is true at stage `α`
under `t`. -/
theorem d0_abs (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {γ α D : V}
    (hγα : M.mem (M.op γ α) th) (hdγ : M.InNRaw P th io M.nat j.1 γ d) (hD : M.IsD0 D)
    (c : M.Num) (hc : M.mem c.1 D) (t : V)
    (hv : ∀ i : M.Num, i ≤ c → ∀ e, (M.ValRaw P th io M.nat Nt j.1 d γ t i.1 e ↔
      M.ValRaw P th io M.nat Nt j.1 d α t i.1 e)) :
    M.TrueAt P io F j.1 γ c t ↔ M.TrueAt P io F j.1 α c t := by
  have had := M.adG_spec
  obtain ⟨ρ, e6, e20, e22, e23, e24, e25, e26, e27, e28, e65, e120, e121⟩ :
      ∃ ρ : ℕ → V, ρ 6 = F ∧ ρ 20 = P ∧ ρ 22 = th ∧ ρ 23 = Nt ∧ ρ 24 = io ∧ ρ 25 = j.1 ∧
        ρ 26 = d ∧ ρ 27 = M.nat ∧ ρ 28 = M.adG ∧ ρ 65 = α ∧ ρ 120 = γ ∧ ρ 121 = D :=
    ⟨Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 22 th) 23 Nt) 24 io) 25 j.1)
      26 d) 27 M.nat) 28 M.adG) 65 α) 120 γ) 121 D, by simp [Function.update_apply]⟩
  have hsat : ∀ n : M.Num, Sat M.mem M.isSet d0Fml (Function.update ρ 99 n.1) ↔
      ∀ c : M.Num, c ≤ n → M.mem c.1 D → ∀ t,
        (∀ i : M.Num, i ≤ c → ∀ e, (M.ValRaw P th io M.nat Nt j.1 d γ t i.1 e ↔
          M.ValRaw P th io M.nat Nt j.1 d α t i.1 e)) →
        (M.TrueAt P io F j.1 γ c t ↔ M.TrueAt P io F j.1 α c t) := by
    intro n
    have h1 : Sat M.mem M.isSet d0Fml (Function.update ρ 99 n.1) ↔
        ∀ c, M.mem c M.nat → M.LeRaw M.adG c n.1 → M.mem c D → ∀ t,
          (∀ i, M.mem i M.nat → M.LeRaw M.adG i c → ∀ e,
            (M.ValRaw P th io M.nat Nt j.1 d γ t i e ↔
              M.ValRaw P th io M.nat Nt j.1 d α t i e)) →
          ((∃ ch pt, M.mem (M.op c ch) io ∧ M.mem (M.quad j.1 γ ch pt) P ∧
              M.mem (M.op pt t) F) ↔
            (∃ ch pt, M.mem (M.op c ch) io ∧ M.mem (M.quad j.1 α ch pt) P ∧
              M.mem (M.op pt t) F)) := by
      simp [d0Fml, LeRaw, Sat, M.sat_imp, M.sat_iff, M.sat_ex, M.sat_fApp3', M.sat_fApp4',
        M.sat_fApp', M.sat_valFml, Function.update_apply, e6, e20, e22, e23, e24, e25, e26,
        e27, e28, e65, e120, e121]
    rw [h1]
    constructor
    · intro raw c hc hcD t hm
      exact raw c.1 c.2 ((M.leRaw_iff had c n).mpr hc) hcD t
        (fun i hi hle e => hm ⟨i, hi⟩ ((M.leRaw_iff had ⟨i, hi⟩ c).mp hle) e)
    · intro clean c hc hle hcD t hm
      exact clean ⟨c, hc⟩ ((M.leRaw_iff had ⟨c, hc⟩ n).mp hle) hcD t
        (fun i hi e => hm i.1 i.2 ((M.leRaw_iff had i ⟨c, hc⟩).mpr hi) e)
  have key := M.num_ind_fml (σW [(6, 5), (20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7),
      (121, 3)]) d0Fml 99 rfl ρ
    (by
      rw [show M.zero = (0 : M.Num).1 from rfl, hsat 0]
      intro c0 hc0 hc0D t0 hv0
      exact M.d0_core hd hγα hdγ hD c0 hc0D (fun c' hc' => absurd (le_trans hc' hc0)
        (fun h => M.succ_not_le_zero h)) t0 hv0)
    (fun k ih => by
      rw [hsat k] at ih
      rw [show M.succ k.1 = (k + 1).1 from (M.val_add_one k).symm, hsat (k + 1)]
      intro c0 hc0 hc0D t0 hv0
      exact M.d0_core hd hγα hdγ hD c0 hc0D (fun c' hc' hc'D t' hv' =>
        ih c' (M.le_of_succ_le_succ (le_trans hc' hc0)) hc'D t' hv') t0 hv0) c
  rw [hsat c] at key
  exact key c (le_refl c) hc t hv

end hier18

/-! ### Separation for bounded formulas; sets of codes of bounded formulas -/

section hier19

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **Separation for bounded formulas.** Let `γ` be a stage above the least one, `α` a later
stage, `c` a bounded formula and `u` a sequence of parameters whose entries up to `c` that
are names of rank below `α` are names of rank below `γ`. Then the set of names `x` of rank
below `γ` such that `c` is true **at stage `α`** under `(x, u)` is denoted by a name of rank
`γ`, so by a name of rank below `α`. -/
theorem sep_d0 (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {γ α D u : V}
    (hγα : M.mem (M.op γ α) th) (hne : γ ≠ α) (hdγ : M.InNRaw P th io M.nat j.1 γ d)
    (hD : M.IsD0 D) (c : M.Num) (hc : M.mem c.1 D) (hu : M.mem (M.op j.1 u) R)
    (hpar : ∀ (k : M.Num) (e : V), k + 1 ≤ c → M.mem (M.trip u k.1 e) Nt →
      M.InNRaw P th io M.nat j.1 α e → M.InNRaw P th io M.nat j.1 γ e) :
    ∃ z, M.InNRaw P th io M.nat j.1 α z ∧ ∀ x, M.EpsRaw P th io M.nat j.1 F x z ↔
      M.InNRaw P th io M.nat j.1 γ x ∧
        ∃ s, M.mem (M.quad j.1 x u s) P ∧ M.TrueAt P io F j.1 α c s := by
  have hγ := (hd.hth.fld γ α hγα).1
  obtain ⟨z, rz, hmem⟩ := M.def_name hd hγ hu c
  have key : ∀ x s, M.InNRaw P th io M.nat j.1 γ x → M.mem (M.quad j.1 x u s) P →
      (M.TrueAt P io F j.1 γ c s ↔ M.TrueAt P io F j.1 α c s) := by
    intro x s hx hs
    refine M.d0_abs hd hγα hdγ hD c hc s (fun i hi e =>
      M.val_iff_of_down hd hγα (fun e' he' => ?_) e)
    rcases he' with ⟨h1, h2⟩ | ⟨-, h2⟩
    · rcases M.num_cases i with h0 | ⟨k, hk⟩
      · subst h0
        obtain ⟨t', ht'⟩ := (hd.nt_zero s e').mp h1
        rw [(hd.hP.inj _ _ _ _ _ _ ht' hs).1]
        exact hx
      · subst hk
        rw [M.nsucc_eq_add_one] at h1 hi
        exact hpar k e' hi ((M.nth_cons_succ hd hs k e').mp h1) h2
    · rw [h2]
      exact hdγ
  refine ⟨z, M.rank_inN rz hγα hne, fun x => ?_⟩
  rw [hmem x]
  constructor
  · rintro ⟨hx, s, hs, htr⟩
    exact ⟨hx, s, hs, (key x s hx hs).mp htr⟩
  · rintro ⟨hx, s, hs, htr⟩
    exact ⟨hx, s, hs, (key x s hx hs).mpr htr⟩

end hier19

/-- The empty set is a set of codes of bounded formulas. -/
theorem isD0_empty : ∃ D, M.IsD0 D := by
  obtain ⟨D, -, hD⟩ := M.comp (fun _ => 0) (.neg (.eq 0 0)) 0 rfl (fun _ => dflt)
  refine ⟨D, fun c hc => ?_⟩
  have := (hD c.1).mp hc
  simp [Sat] at this

/-- A set of codes of bounded formulas can be enlarged by a code formed from its members. -/
theorem isD0_insert {D : V} (hD : M.IsD0 D) (c : M.Num)
    (hc : (∃ r v w : M.Num, r ≠ 1 ∧ r ≠ 2 ∧ c = M.cRel r v w) ∨ (∃ x : M.Num, M.mem x.1 D ∧ c = M.cNeg x) ∨
      (∃ x y : M.Num, M.mem x.1 D ∧ M.mem y.1 D ∧ c = M.cAnd x y) ∨
      ∃ v w x : M.Num, v ≠ w ∧ M.mem x.1 D ∧ c = M.cBAll v w x) :
    ∃ D', M.IsD0 D' ∧ M.mem c.1 D' ∧ ∀ x, M.mem x D → M.mem x D' := by
  obtain ⟨D', -, hD'⟩ := M.comp (σW [(1, 3)]) (Fml.or (.mem 0 1) (.eq 0 2)) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 D) 2 c.1)
  have h : ∀ x, M.mem x D' ↔ M.mem x D ∨ x = c.1 := by
    intro x
    rw [hD' x]
    simp [Sat, M.sat_or, Function.update_apply]
  have up : ∀ x : M.Num, M.mem x.1 D → M.mem x.1 D' := fun x hx => (h _).mpr (Or.inl hx)
  have lift : ∀ y : M.Num,
      ((∃ r v w : M.Num, r ≠ 1 ∧ r ≠ 2 ∧ y = M.cRel r v w) ∨ (∃ x : M.Num, M.mem x.1 D ∧ y = M.cNeg x) ∨
        (∃ x z : M.Num, M.mem x.1 D ∧ M.mem z.1 D ∧ y = M.cAnd x z) ∨
        ∃ v w x : M.Num, v ≠ w ∧ M.mem x.1 D ∧ y = M.cBAll v w x) →
      ((∃ r v w : M.Num, r ≠ 1 ∧ r ≠ 2 ∧ y = M.cRel r v w) ∨ (∃ x : M.Num, M.mem x.1 D' ∧ y = M.cNeg x) ∨
        (∃ x z : M.Num, M.mem x.1 D' ∧ M.mem z.1 D' ∧ y = M.cAnd x z) ∨
        ∃ v w x : M.Num, v ≠ w ∧ M.mem x.1 D' ∧ y = M.cBAll v w x) := by
    rintro y (h1 | ⟨x, hx, e⟩ | ⟨x, z, hx, hz, e⟩ | ⟨v, w, x, hvw, hx, e⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨x, up x hx, e⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨x, z, up x hx, up z hz, e⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨v, w, x, hvw, up x hx, e⟩))
  refine ⟨D', fun y hy => ?_, (h _).mpr (Or.inr rfl), fun x hx => (h x).mpr (Or.inl hx)⟩
  rcases (h _).mp hy with hy | hy
  · exact lift y (hD y hy)
  · rw [show y = c from Subtype.ext hy]
    exact lift c hc

/-! ### The bounded quantifier in Tarski's form; transitive sets and ordinals -/

section hier20

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem agree_same {α t t' a : V} {v C : M.Num}
    (hag : M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v.1 a C.1) (hv : v ≤ C) :
    M.ValRaw P th io M.nat Nt j.1 d α t' v.1 a :=
  (hag v.1 v.2 ((M.leRaw_iff M.adG_spec v C).mpr hv) a).mpr (Or.inl ⟨rfl, rfl⟩)

theorem agree_other {α t t' a e : V} {v i C : M.Num}
    (hag : M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v.1 a C.1) (hi : i ≤ C) (hne : i ≠ v)
    (h : M.ValRaw P th io M.nat Nt j.1 d α t i.1 e) :
    M.ValRaw P th io M.nat Nt j.1 d α t' i.1 e :=
  (hag i.1 i.2 ((M.leRaw_iff M.adG_spec i C).mpr hi) e).mpr
    (Or.inr ⟨fun e' => hne (Subtype.ext e'), h⟩)

/-- The clause for the bounded quantifier, in Tarski's form. -/
theorem hier_ball_ex (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t b : V}
    (hα : M.mem (M.op α α) th) (v w c : M.Num) (hvw : v ≠ w)
    (hw : M.ValRaw P th io M.nat Nt j.1 d α t w.1 b) :
    M.TrueAt P io F j.1 α (M.cBAll v w c) t ↔ ∀ a, M.InNRaw P th io M.nat j.1 α a →
      M.EpsStarRaw P th io M.nat j.1 tp F a b →
      ∃ t', M.AgreeRaw P th io M.nat Nt j.1 d M.adG α t t' v.1 a (M.cBAll v w c).1 ∧
        M.TrueAt P io F j.1 α c t' := by
  obtain ⟨-, -, lt1⟩ := M.cBAll_bounds v w c
  rw [M.hier_ball hd hα v w c hvw hw]
  constructor
  · intro h a ha he
    obtain ⟨t', hag⟩ := M.exists_upd hd ha t v.1 (M.cBAll v w c)
    exact ⟨t', hag, h a t' ha hag he⟩
  · intro h a t'' ha hag'' he
    obtain ⟨t', hag, htr⟩ := h a ha he
    refine (M.coin_hier hd c t' t'' (fun i hi e => ?_)).mp htr
    have raw := (M.leRaw_iff M.adG_spec i (M.cBAll v w c)).mpr
      (le_trans hi (le_trans (M.le_add_one c) lt1))
    rw [hag i.1 i.2 raw e, hag'' i.1 i.2 raw e]

/-- The code of "`x` is transitive": `∀y ε x ∀z ε y (z ε x)`. -/
noncomputable def cTr (x y z : M.Num) : M.Num :=
  M.cBAll y x (M.cBAll z y (M.cRel 0 z x))

/-- The code of "`x` is a transitive set of transitive sets". -/
noncomputable def cOrd (x y z w : M.Num) : M.Num :=
  M.cAnd (M.cTr x y z) (M.cBAll y x (M.cTr y z w))

/-- `a` is transitive, for names of rank below `α`. -/
def TrS (P th io Nt F tp : V) (j : M.Num) (α a : V) : Prop :=
  ∀ b, M.InNRaw P th io M.nat j.1 α b → M.EpsStarRaw P th io M.nat j.1 tp F b a →
    ∀ c, M.InNRaw P th io M.nat j.1 α c → M.EpsStarRaw P th io M.nat j.1 tp F c b →
      M.EpsStarRaw P th io M.nat j.1 tp F c a

theorem hier_trans (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t a : V}
    (hα : M.mem (M.op α α) th) (x y z : M.Num) (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x)
    (hx : M.ValRaw P th io M.nat Nt j.1 d α t x.1 a) :
    M.TrueAt P io F j.1 α (M.cTr x y z) t ↔ M.TrS P th io Nt F tp j α a := by
  obtain ⟨ley1, lex1, -⟩ := M.cBAll_bounds y x (M.cBAll z y (M.cRel 0 z x))
  obtain ⟨lez2, ley2, lt2⟩ := M.cBAll_bounds z y (M.cRel 0 z x)
  have lex2 : x ≤ M.cBAll z y (M.cRel 0 z x) :=
    le_trans (le_trans (M.le_pairN_right z x)
      (le_trans (M.le_pairN_right 0 _) (M.le_pairN_right 0 _)))
      (le_trans (M.le_add_one _) lt2)
  unfold cTr TrS
  rw [M.hier_ball_ex hd hα y x _ hyx hx]
  constructor
  · intro h b hb heb c hc hec
    obtain ⟨t', hag, htr⟩ := h b hb heb
    have ky := M.agree_same hag ley1
    have kx := M.agree_other hag lex1 (Ne.symm hyx) hx
    obtain ⟨t'', hag', htr'⟩ := (M.hier_ball_ex hd hα z y _ hzy ky).mp htr c hc hec
    have kz' := M.agree_same hag' lez2
    have kx' := M.agree_other hag' lex2 (Ne.symm hzx) kx
    exact (M.rel_val hd z x hα kz' kx').mp htr'
  · intro h b hb heb
    obtain ⟨t', hag⟩ := M.exists_upd hd hb t y.1 (M.cBAll y x (M.cBAll z y (M.cRel 0 z x)))
    have ky := M.agree_same hag ley1
    have kx := M.agree_other hag lex1 (Ne.symm hyx) hx
    refine ⟨t', hag, (M.hier_ball_ex hd hα z y _ hzy ky).mpr (fun c hc hec => ?_)⟩
    obtain ⟨t'', hag'⟩ := M.exists_upd hd hc t' z.1 (M.cBAll z y (M.cRel 0 z x))
    have kz' := M.agree_same hag' lez2
    have kx' := M.agree_other hag' lex2 (Ne.symm hzx) kx
    exact ⟨t'', hag', (M.rel_val hd z x hα kz' kx').mpr (h b hb heb c hc hec)⟩

theorem hier_ord (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t a : V}
    (hα : M.mem (M.op α α) th) (x y z w : M.Num) (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x)
    (hwz : w ≠ z) (hwy : w ≠ y)
    (hx : M.ValRaw P th io M.nat Nt j.1 d α t x.1 a) :
    M.TrueAt P io F j.1 α (M.cOrd x y z w) t ↔ (M.TrS P th io Nt F tp j α a ∧
      ∀ b, M.InNRaw P th io M.nat j.1 α b → M.EpsStarRaw P th io M.nat j.1 tp F b a →
        M.TrS P th io Nt F tp j α b) := by
  obtain ⟨ley1, -, -⟩ := M.cBAll_bounds y x (M.cTr y z w)
  unfold cOrd
  rw [M.hier_and hd, M.hier_trans hd hα x y z hyx hzy hzx hx,
    M.hier_ball_ex hd hα y x _ hyx hx]
  constructor
  · rintro ⟨-, h1, h2⟩
    refine ⟨h1, fun b hb heb => ?_⟩
    obtain ⟨t', hag, htr⟩ := h2 b hb heb
    exact (M.hier_trans hd hα y z w hzy hwz hwy (M.agree_same hag ley1)).mp htr
  · rintro ⟨h1, h2⟩
    refine ⟨hα, h1, fun b hb heb => ?_⟩
    obtain ⟨t', hag⟩ := M.exists_upd hd hb t y.1 (M.cBAll y x (M.cTr y z w))
    exact ⟨t', hag, (M.hier_trans hd hα y z w hzy hwz hwy (M.agree_same hag ley1)).mpr
      (h2 b hb heb)⟩

end hier20

/-! ### Ordinals of the hierarchy -/

/-- `a` denotes a transitive set. -/
def TrN (P th io F tp : V) (j : M.Num) (a : V) : Prop :=
  ∀ b c, M.EpsStarRaw P th io M.nat j.1 tp F b a → M.EpsStarRaw P th io M.nat j.1 tp F c b →
    M.EpsStarRaw P th io M.nat j.1 tp F c a

/-- `a` denotes an ordinal: a transitive set of transitive sets. -/
def OrdN (P th io F tp : V) (j : M.Num) (a : V) : Prop :=
  M.TrN P th io F tp j a ∧
    ∀ b, M.EpsStarRaw P th io M.nat j.1 tp F b a → M.TrN P th io F tp j b

/-- `q` is the pair of the numeral of the code of "`v₀` is an ordinal" and the default name;
the name `(ξ, q)` is the **ordinal name of the stage `ξ`**. -/
def OrdQ (P io : V) (j : M.Num) (d q : V) : Prop :=
  ∃ f, M.mem (M.op (M.cOrd 0 1 2 3).1 f) io ∧ M.mem (M.quad j.1 f d q) P

section hier21

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem epsStar_left (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {x y : V}
    (h : M.EpsStarRaw P th io M.nat j.1 tp F x y) : M.SimRaw P j.1 tp F x x := by
  obtain ⟨x0, hs0, -⟩ := h
  obtain ⟨β, -, ra, -, hβ, -⟩ := M.sim_names hd hs0
  exact M.sim_refl hd ra hβ

theorem epsStar_rep (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α a b : V}
    (ha : M.InNRaw P th io M.nat j.1 α a) (h : M.EpsStarRaw P th io M.nat j.1 tp F b a) :
    ∃ b', M.InNRaw P th io M.nat j.1 α b' ∧ M.SimRaw P j.1 tp F b b' ∧
      M.EpsRaw P th io M.nat j.1 F b' a := by
  obtain ⟨b', hs, he⟩ := h
  exact ⟨b', M.eps_rank hd ha he, hs, he⟩

theorem trS_iff (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α a : V}
    (ha : M.InNRaw P th io M.nat j.1 α a) :
    M.TrS P th io Nt F tp j α a ↔ M.TrN P th io F tp j a := by
  constructor
  · intro h b c hb hc
    obtain ⟨b', hb'N, hsb, heb'⟩ := M.epsStar_rep hd ha hb
    have hcb' := M.epsStar_congr hd (M.epsStar_left hd hc) hsb hc
    obtain ⟨c', hc'N, hsc, hec'⟩ := M.epsStar_rep hd hb'N hcb'
    have h1 := h b' hb'N ⟨b', M.inN_refl hd hb'N, heb'⟩ c' hc'N ⟨c', M.inN_refl hd hc'N, hec'⟩
    exact M.epsStar_congr hd (M.sim_symm hd hsc) (M.inN_refl hd ha) h1
  · exact fun h b _ hb c _ hc => h b c hb hc

theorem trN_congr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a a' : V}
    (hs : M.SimRaw P j.1 tp F a a') (h : M.TrN P th io F tp j a) : M.TrN P th io F tp j a' := by
  intro b c hb hc
  have hb' := M.epsStar_congr hd (M.epsStar_left hd hb) (M.sim_symm hd hs) hb
  exact M.epsStar_congr hd (M.epsStar_left hd hc) hs (h b c hb' hc)

theorem ordN_congr (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a a' : V}
    (hs : M.SimRaw P j.1 tp F a a') (h : M.OrdN P th io F tp j a) : M.OrdN P th io F tp j a' :=
  ⟨M.trN_congr hd hs h.1, fun b hb =>
    h.2 b (M.epsStar_congr hd (M.epsStar_left hd hb) (M.sim_symm hd hs) hb)⟩

/-- A member of an ordinal is an ordinal. -/
theorem ordN_mem {a b : V} (h : M.OrdN P th io F tp j a)
    (hb : M.EpsStarRaw P th io M.nat j.1 tp F b a) : M.OrdN P th io F tp j b :=
  ⟨h.2 b hb, fun c hc => h.2 c (h.1 b c hb hc)⟩

/-- The formula "`x` is a transitive set of transitive sets" is true at a stage exactly of the
names that denote ordinals. -/
theorem hier_ordN (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α t a : V}
    (hα : M.mem (M.op α α) th) (x y z w : M.Num) (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x)
    (hwz : w ≠ z) (hwy : w ≠ y) (ha : M.InNRaw P th io M.nat j.1 α a)
    (hx : M.ValRaw P th io M.nat Nt j.1 d α t x.1 a) :
    M.TrueAt P io F j.1 α (M.cOrd x y z w) t ↔ M.OrdN P th io F tp j a := by
  rw [M.hier_ord hd hα x y z w hyx hzy hzx hwz hwy hx]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(M.trS_iff hd ha).mp h1, fun b hb => ?_⟩
    obtain ⟨b', hb'N, hsb, heb'⟩ := M.epsStar_rep hd ha hb
    exact M.trN_congr hd (M.sim_symm hd hsb)
      ((M.trS_iff hd hb'N).mp (h2 b' hb'N ⟨b', M.inN_refl hd hb'N, heb'⟩))
  · rintro ⟨h1, h2⟩
    exact ⟨(M.trS_iff hd ha).mpr h1, fun b hbN hb => (M.trS_iff hd hbN).mpr (h2 b hb)⟩

/-- **Membership is irreflexive.** -/
theorem epsStar_irrefl (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {β a : V}
    (ra : M.RankIs P io M.nat j.1 β a) (hβ : M.mem (M.op β β) th) :
    ¬ M.EpsStarRaw P th io M.nat j.1 tp F a a := by
  intro haa
  obtain ⟨X, -, hX0⟩ := M.comp (σW [(6, 5), (20, 7), (22, 5), (24, 5), (27, 3)]) simFml 94 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th)
      24 io) 25 j.1) 27 M.nat) 95 a)
  have hX : ∀ z, M.mem z X ↔ M.SimRaw P j.1 tp F z a := by
    intro z
    rw [hX0 z]
    simp [M.sat_simFml, Function.update_apply]
  have haX : M.mem a X := (hX a).mpr (M.sim_refl hd ra hβ)
  obtain ⟨b, hbX, hmin⟩ := M.eps_wf hd haX ra hβ
    (fun x x' hx hs => (hX x').mpr (M.sim_trans hd hs ((hX x).mp hx)))
  exact hmin a haX (M.epsStar_congr hd (M.sim_refl hd ra hβ)
    (M.sim_symm hd ((hX b).mp hbX)) haa)

theorem exists_ordQ (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) : ∃ q, M.OrdQ P io j d q := by
  obtain ⟨f, hf⟩ := hd.io_tot (M.cOrd 0 1 2 3)
  obtain ⟨q, hq⟩ := hd.hP.tot j hd.hj f d (hd.io_dom _ _ hf).2 (M.d_rung hd)
  exact ⟨q, f, hf, hq⟩

theorem exists_ordName (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q ξ : V}
    (hq : M.OrdQ P io j d q) (hξ : M.mem (M.op ξ ξ) th) : ∃ o, M.mem (M.quad j.1 ξ q o) P := by
  obtain ⟨f, -, hfq⟩ := hq
  exact hd.hP.tot j hd.hj ξ q (hd.th_rung ξ ξ hξ).1 (hd.hP.dom _ _ _ _ hfq).2.2.2

theorem ordName_rank (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q ξ o : V}
    (hq : M.OrdQ P io j d q) (ho : M.mem (M.quad j.1 ξ q o) P) :
    M.RankIs P io M.nat j.1 ξ o := by
  obtain ⟨f, hf, hfq⟩ := hq
  exact ⟨f, d, q, ho, hfq, _, (hd.io_dom _ _ hf).1, hf⟩

/-- **The members of the ordinal name of the stage `ξ`** are the names of rank below `ξ` that
denote ordinals. -/
theorem ordName_mem (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q ξ o : V}
    (hq : M.OrdQ P io j d q) (hξ : M.mem (M.op ξ ξ) th) (ho : M.mem (M.quad j.1 ξ q o) P)
    (x : V) : M.EpsRaw P th io M.nat j.1 F x o ↔
      M.InNRaw P th io M.nat j.1 ξ x ∧ M.OrdN P th io F tp j x := by
  obtain ⟨f, hf, hfq⟩ := hq
  rw [M.eps_iff hd ho hfq hf x]
  constructor
  · rintro ⟨hx, s, hs, htr⟩
    have v0 : M.ValRaw P th io M.nat Nt j.1 d ξ s (0 : M.Num).1 x :=
      Or.inl ⟨(hd.nt_zero s x).mpr ⟨d, hs⟩, hx⟩
    exact ⟨hx, (M.hier_ordN hd hξ 0 1 2 3 M.n10 M.n21 M.n20 M.n32 M.n31 hx v0).mp htr⟩
  · rintro ⟨hx, hord⟩
    obtain ⟨s, hs⟩ := hd.hP.tot j hd.hj x d (M.inN_rung hd hx) (M.d_rung hd)
    have v0 : M.ValRaw P th io M.nat Nt j.1 d ξ s (0 : M.Num).1 x :=
      Or.inl ⟨(hd.nt_zero s x).mpr ⟨d, hs⟩, hx⟩
    exact ⟨hx, s, hs, (M.hier_ordN hd hξ 0 1 2 3 M.n10 M.n21 M.n20 M.n32 M.n31 hx v0).mpr hord⟩

/-- **The ordinal name of a stage denotes an ordinal.** -/
theorem ordN_ordName (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q ξ o : V}
    (hq : M.OrdQ P io j d q) (hξ : M.mem (M.op ξ ξ) th) (ho : M.mem (M.quad j.1 ξ q o) P) :
    M.OrdN P th io F tp j o := by
  have hmem := M.ordName_mem hd hq hξ ho
  have mem_ord : ∀ b, M.EpsStarRaw P th io M.nat j.1 tp F b o → M.OrdN P th io F tp j b := by
    rintro b ⟨b', hs, he⟩
    exact M.ordN_congr hd (M.sim_symm hd hs) ((hmem b').mp he).2
  refine ⟨fun b c hb hc => ?_, fun b hb => (mem_ord b hb).1⟩
  obtain ⟨b', hsb, heb'⟩ := hb
  obtain ⟨hb'N, hb'ord⟩ := (hmem b').mp heb'
  have hcb' := M.epsStar_congr hd (M.epsStar_left hd hc) hsb hc
  obtain ⟨c', hc'N, hsc, hec'⟩ := M.epsStar_rep hd hb'N hcb'
  have hc'ord := M.ordN_mem hb'ord ⟨c', M.inN_refl hd hc'N, hec'⟩
  exact ⟨c', hsc, (hmem c').mpr ⟨hc'N, hc'ord⟩⟩

/-- The ordinal name of a stage does not denote the same set as a name of lower rank. -/
theorem ordName_not_low (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q ξ o y : V}
    (hq : M.OrdQ P io j d q) (hξ : M.mem (M.op ξ ξ) th) (ho : M.mem (M.quad j.1 ξ q o) P)
    (hy : M.InNRaw P th io M.nat j.1 ξ y) (hs : M.SimRaw P j.1 tp F o y) : False :=
  M.epsStar_irrefl hd (M.ordName_rank hd hq ho) hξ
    ⟨y, hs, (M.ordName_mem hd hq hξ ho y).mpr
      ⟨hy, M.ordN_congr hd hs (M.ordN_ordName hd hq hξ ho)⟩⟩

end hier21

section hier22

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- The step of the classification of the ordinals. -/
theorem ord_core (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q ρ x : V}
    (hq : M.OrdQ P io j d q) (hρ : M.mem (M.op ρ ρ) th) (rx : M.RankIs P io M.nat j.1 ρ x)
    (hord : M.OrdN P th io F tp j x)
    (ih : ∀ ζ o' e', M.mem (M.op ζ ρ) th → M.mem (M.quad j.1 ζ q o') P →
      M.EpsRaw P th io M.nat j.1 F e' o' →
      ∃ ζ' o'', M.mem (M.op ζ' ζ) th ∧ ζ' ≠ ζ ∧ M.mem (M.quad j.1 ζ' q o'') P ∧
        M.SimRaw P j.1 tp F e' o'') :
    ∃ ξ o, M.mem (M.op ξ ρ) th ∧ M.mem (M.quad j.1 ξ q o) P ∧ M.SimRaw P j.1 tp F x o := by
  have hxx : M.SimRaw P j.1 tp F x x := M.sim_refl hd rx hρ
  obtain ⟨B, -, hB0⟩ := M.comp (σW [(6, 5), (20, 7), (22, 5), (24, 5), (27, 3)])
    (.and (fApp 22 140 140) (.neg (Fml.ex 70 (.and (fApp4 20 25 140 122 70) epsStarFml))))
    140 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 6 F)
      20 P) 21 tp) 22 th) 24 io) 25 j.1) 27 M.nat) 122 q) 73 x)
  have hB : ∀ ζ, M.mem ζ B ↔ M.mem (M.op ζ ζ) th ∧
      ¬ ∃ o', M.mem (M.quad j.1 ζ q o') P ∧ M.EpsStarRaw P th io M.nat j.1 tp F o' x := by
    intro ζ
    rw [hB0 ζ]
    simp [Sat, M.sat_ex, M.sat_fApp', M.sat_fApp4', M.sat_epsStarFml, Function.update_apply]
  have hρB : M.mem ρ B := by
    refine (hB ρ).mpr ⟨hρ, ?_⟩
    rintro ⟨o', ho', y, hs, hy⟩
    exact M.ordName_not_low hd hq hρ ho' (M.eps_inN_rank hd rx hy) hs
  obtain ⟨ξ, hξB, hξ, hminB⟩ := hd.hth.least B ⟨ρ, hρB, hρ⟩
  have hξρ := hminB ρ hρB hρ
  have hξnot : ∀ o', M.mem (M.quad j.1 ξ q o') P →
      ¬ M.EpsStarRaw P th io M.nat j.1 tp F o' x :=
    fun o' ho' he => ((hB ξ).mp hξB).2 ⟨o', ho', he⟩
  obtain ⟨oξ, hoξ⟩ := M.exists_ordName hd hq hξ
  obtain ⟨oρ, hoρ⟩ := M.exists_ordName hd hq hρ
  have rξ := M.ordName_rank hd hq hoξ
  refine ⟨ξ, oξ, hξρ, hoξ, (M.sim_iff_ext hd rx rξ hρ hξ).mpr (fun z => ⟨?_, ?_⟩)⟩
  · rintro ⟨z', hsz, hez'⟩
    have hz'N := M.eps_inN_rank hd rx hez'
    have hz'ord := M.ordN_mem hord ⟨z', M.inN_refl hd hz'N, hez'⟩
    obtain ⟨ζ, o', hζρ, hζne, ho', hsim⟩ := ih ρ oρ z' hρ hoρ
      ((M.ordName_mem hd hq hρ hoρ z').mpr ⟨hz'N, hz'ord⟩)
    have hζ := (hd.hth.fld ζ ρ hζρ).1
    have ho'x : M.EpsStarRaw P th io M.nat j.1 tp F o' x :=
      M.epsStar_congr hd hsim hxx ⟨z', M.inN_refl hd hz'N, hez'⟩
    have hlt : M.mem (M.op ζ ξ) th ∧ ζ ≠ ξ := by
      have hne : ζ ≠ ξ := by
        intro e
        rw [e] at ho'
        exact hξnot o' ho' ho'x
      rcases M.wo_total hd.hth hζ hξ with h | h
      · exact ⟨h, hne⟩
      · exfalso
        have h1 : M.EpsRaw P th io M.nat j.1 F oξ o' :=
          (M.ordName_mem hd hq hζ ho' oξ).mpr
            ⟨M.rank_inN rξ h (Ne.symm hne), M.ordN_ordName hd hq hξ hoξ⟩
        exact hξnot oξ hoξ (hord.1 o' oξ ho'x ⟨oξ, M.sim_refl hd rξ hξ, h1⟩)
    exact ⟨o', M.sim_trans hd hsz hsim, (M.ordName_mem hd hq hξ hoξ o').mpr
      ⟨M.rank_inN (M.ordName_rank hd hq ho') hlt.1 hlt.2, M.ordN_ordName hd hq hζ ho'⟩⟩
  · rintro ⟨z', hsz, hez'⟩
    obtain ⟨ζ, o', hζξ, hζne, ho', hsim⟩ := ih ξ oξ z' hξρ hoξ hez'
    have hζ := (hd.hth.fld ζ ξ hζξ).1
    have hex : ∃ o'', M.mem (M.quad j.1 ζ q o'') P ∧
        M.EpsStarRaw P th io M.nat j.1 tp F o'' x := by
      by_contra hn
      exact hζne (hd.hth.antisymm ζ ξ hζξ (hminB ζ ((hB ζ).mpr ⟨hζ, hn⟩) hζ))
    obtain ⟨o'', ho'', he''⟩ := hex
    rw [hd.hP.fn _ _ _ _ _ ho'' ho'] at he''
    exact M.epsStar_congr hd (M.sim_symm hd (M.sim_trans hd hsz hsim)) hxx he''

/-- **The members of the ordinal name of a stage are the ordinal names of the earlier
stages**, up to "denote the same set". -/
theorem ordName_members (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q ξ o e : V}
    (hq : M.OrdQ P io j d q) (hξ : M.mem (M.op ξ ξ) th) (ho : M.mem (M.quad j.1 ξ q o) P)
    (he : M.EpsRaw P th io M.nat j.1 F e o) :
    ∃ ζ o', M.mem (M.op ζ ξ) th ∧ ζ ≠ ξ ∧ M.mem (M.quad j.1 ζ q o') P ∧
      M.SimRaw P j.1 tp F e o' := by
  obtain ⟨C, -, hC0⟩ := M.comp (σW [(6, 5), (20, 7), (22, 5), (24, 5), (27, 3)])
    (.and (fApp 22 140 140) (Fml.ex 141 (Fml.ex 142 (.and (fApp4 20 25 140 122 141)
      (.and (Fml.ex 72 (.and (.eq 72 142) (Fml.ex 73 (.and (.eq 73 141) epsFml))))
        (.neg (Fml.ex 143 (Fml.ex 144 (.and (fApp 22 143 140) (.and (.neg (.eq 143 140))
          (.and (fApp4 20 25 143 122 144)
            (Fml.ex 94 (.and (.eq 94 142) (Fml.ex 95 (.and (.eq 95 144) simFml)))))))))))))))
    140 rfl
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 6 F)
      20 P) 21 tp) 22 th) 24 io) 25 j.1) 27 M.nat) 122 q)
  have hC : ∀ ξ, M.mem ξ C ↔ M.mem (M.op ξ ξ) th ∧ ∃ o e, M.mem (M.quad j.1 ξ q o) P ∧
      M.EpsRaw P th io M.nat j.1 F e o ∧
      ¬ ∃ ζ o', M.mem (M.op ζ ξ) th ∧ ζ ≠ ξ ∧ M.mem (M.quad j.1 ζ q o') P ∧
        M.SimRaw P j.1 tp F e o' := by
    intro ξ
    rw [hC0 ξ]
    simp [Sat, M.sat_ex, M.sat_fApp', M.sat_fApp4', M.sat_epsFml, M.sat_simFml,
      Function.update_apply]
  by_contra hcon
  obtain ⟨ξ0, hξ0C, hξ0, hmin⟩ := hd.hth.least C ⟨ξ, (hC ξ).mpr ⟨hξ, o, e, ho, he, hcon⟩, hξ⟩
  obtain ⟨-, o0, e0, ho0, he0, hno⟩ := (hC ξ0).mp hξ0C
  obtain ⟨he0N, he0ord⟩ := (M.ordName_mem hd hq hξ0 ho0 e0).mp he0
  obtain ⟨ρ, re, hρξ0, hρne⟩ := M.inN_rank he0N
  have hρ := (hd.hth.fld ρ ξ0 hρξ0).1
  obtain ⟨ξ1, o1, hξ1ρ, ho1, hsim⟩ := M.ord_core hd hq hρ re he0ord
    (fun ζ o' e' hζρ ho' he' => by
      by_contra hn
      have hζ := (hd.hth.fld ζ ρ hζρ).1
      have h1 := hmin ζ ((hC ζ).mpr ⟨hζ, o', e', ho', he', hn⟩) hζ
      exact hρne (hd.hth.antisymm ρ ξ0 hρξ0 (hd.hth.trans ξ0 ζ ρ h1 hζρ)))
  refine hno ⟨ξ1, o1, hd.hth.trans ξ1 ρ ξ0 hξ1ρ hρξ0, fun e1 => ?_, ho1, hsim⟩
  rw [e1] at hξ1ρ
  exact hρne (hd.hth.antisymm ρ ξ0 hρξ0 hξ1ρ)

/-- **Every ordinal of the hierarchy is the ordinal name of a stage**: a name of rank `ρ`
that denotes an ordinal denotes the same set as the ordinal name of some stage `ξ ≤ ρ`. -/
theorem ord_is_ordName (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q ρ x : V}
    (hq : M.OrdQ P io j d q) (hρ : M.mem (M.op ρ ρ) th) (rx : M.RankIs P io M.nat j.1 ρ x)
    (hord : M.OrdN P th io F tp j x) :
    ∃ ξ o, M.mem (M.op ξ ρ) th ∧ M.mem (M.quad j.1 ξ q o) P ∧ M.SimRaw P j.1 tp F x o :=
  M.ord_core hd hq hρ rx hord (fun ζ _ _ hζρ ho' he' =>
    M.ordName_members hd hq (hd.hth.fld ζ ρ hζρ).1 ho' he')

/-- **The ordinal names are ordered as the stages.** -/
theorem ordName_lt (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q ζ ξ oζ oξ : V}
    (hq : M.OrdQ P io j d q) (hζ : M.mem (M.op ζ ζ) th) (hξ : M.mem (M.op ξ ξ) th)
    (hoζ : M.mem (M.quad j.1 ζ q oζ) P) (hoξ : M.mem (M.quad j.1 ξ q oξ) P) :
    M.EpsStarRaw P th io M.nat j.1 tp F oζ oξ ↔ (M.mem (M.op ζ ξ) th ∧ ζ ≠ ξ) := by
  have rζ := M.ordName_rank hd hq hoζ
  constructor
  · rintro ⟨y, hs, hy⟩
    have hyN := ((M.ordName_mem hd hq hξ hoξ y).mp hy).1
    rcases M.wo_total hd.hth hζ hξ with h | h
    · refine ⟨h, fun e => ?_⟩
      rw [← e] at hyN
      exact M.ordName_not_low hd hq hζ hoζ hyN hs
    · exact (M.ordName_not_low hd hq hζ hoζ (M.inN_mono hd hyN h) hs).elim
  · rintro ⟨h, hne⟩
    exact ⟨oζ, M.sim_refl hd rζ hζ, (M.ordName_mem hd hq hξ hoξ oζ).mpr
      ⟨M.rank_inN rζ h hne, M.ordN_ordName hd hq hζ hoζ⟩⟩

/-- Ordinal names of different stages denote different sets. -/
theorem ordName_inj (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q ζ ξ oζ oξ : V}
    (hq : M.OrdQ P io j d q) (hζ : M.mem (M.op ζ ζ) th) (hξ : M.mem (M.op ξ ξ) th)
    (hoζ : M.mem (M.quad j.1 ζ q oζ) P) (hoξ : M.mem (M.quad j.1 ξ q oξ) P)
    (hs : M.SimRaw P j.1 tp F oζ oξ) : ζ = ξ := by
  by_contra hne
  rcases M.wo_total hd.hth hζ hξ with h | h
  · exact M.ordName_not_low hd hq hξ hoξ
      (M.rank_inN (M.ordName_rank hd hq hoζ) h hne) (M.sim_symm hd hs)
  · exact M.ordName_not_low hd hq hζ hoζ
      (M.rank_inN (M.ordName_rank hd hq hoξ) h (Ne.symm hne)) hs

end hier22

/-! ### Separation for bounded formulas at limit levels -/

/-- "Some stage `γ` (name `150`) below `l` (name `151`) bounds the ranks of the entries up to
`n` (name `99`) of `u` (name `152`) that are names of rank below `l`". -/
def bndFml : Fml :=
  Fml.ex 150 (.and (fApp 22 150 151) (.and (.neg (.eq 150 151))
    (.all 67 (Fml.imp (.mem 67 27) (Fml.imp (Fml.ex 84 (.and (.mem 84 27) (fApp3 28 67 84 99)))
      (.all 68 (Fml.imp (fApp3 23 152 67 68)
        (Fml.imp (Fml.ex 65 (.and (.eq 65 151) inNFml))
          (Fml.ex 65 (.and (.eq 65 150) inNFml))))))))))

section hier23

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem bound_step (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l u γ : V}
    (hl : M.IsLim th l) (hγ : M.mem (M.op γ l) th) (hγne : γ ≠ l) (k : M.Num) :
    ∃ γ', M.mem (M.op γ γ') th ∧ M.mem (M.op γ' l) th ∧ γ' ≠ l ∧
      ∀ e, M.mem (M.trip u k.1 e) Nt → M.InNRaw P th io M.nat j.1 l e →
        M.InNRaw P th io M.nat j.1 γ' e := by
  have hγγ := (hd.hth.fld γ l hγ).1
  by_cases h : ∃ e, M.mem (M.trip u k.1 e) Nt ∧ M.InNRaw P th io M.nat j.1 l e
  · obtain ⟨e, he, βe, fe, ue, qe, a1, a2, a3, a4, a5⟩ := h
    rcases M.wo_total hd.hth hγγ (hd.hth.fld βe l a3).1 with h1 | h1
    · obtain ⟨γ', g1, g2, g3, g4⟩ := hl.2 βe a3 a4
      refine ⟨γ', hd.hth.trans γ βe γ' h1 g1, g3, g4, fun e' he' _ => ?_⟩
      rw [M.nth_fun hd.hP hd.nt_zero hd.nt_succ k u e' e he' he]
      exact ⟨βe, fe, ue, qe, a1, a2, g1, g2, a5⟩
    · obtain ⟨γ', g1, g2, g3, g4⟩ := hl.2 γ hγ hγne
      refine ⟨γ', g1, g3, g4, fun e' he' _ => ?_⟩
      rw [M.nth_fun hd.hP hd.nt_zero hd.nt_succ k u e' e he' he]
      refine ⟨βe, fe, ue, qe, a1, a2, hd.hth.trans βe γ γ' h1 g1, fun eq => ?_, a5⟩
      rw [eq] at h1
      exact g2 (hd.hth.antisymm γ γ' g1 h1)
  · exact ⟨γ, hγγ, hγ, hγne, fun e he heN => absurd ⟨e, he, heN⟩ h⟩

/-- **Finitely many names of rank below a limit stage have rank below a common earlier
stage.** Here "finitely many" is in the sense of the model: the entries up to `n` of a
sequence `u`, for a number `n` of the model. -/
theorem bound_lim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l u β : V}
    (hl : M.IsLim th l) (hβ : M.mem (M.op β l) th) (hβne : β ≠ l) (n : M.Num) :
    ∃ γ, M.mem (M.op γ l) th ∧ γ ≠ l ∧ ∀ k : M.Num, k ≤ n → ∀ e,
      M.mem (M.trip u k.1 e) Nt → M.InNRaw P th io M.nat j.1 l e →
        M.InNRaw P th io M.nat j.1 γ e := by
  have had := M.adG_spec
  obtain ⟨ρ, e20, e22, e23, e24, e25, e27, e28, e151, e152⟩ :
      ∃ ρ : ℕ → V, ρ 20 = P ∧ ρ 22 = th ∧ ρ 23 = Nt ∧ ρ 24 = io ∧ ρ 25 = j.1 ∧
        ρ 27 = M.nat ∧ ρ 28 = M.adG ∧ ρ 151 = l ∧ ρ 152 = u :=
    ⟨Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (fun _ => dflt)
      20 P) 22 th) 23 Nt) 24 io) 25 j.1) 27 M.nat) 28 M.adG) 151 l) 152 u,
      by simp [Function.update_apply]⟩
  have hsat : ∀ n : M.Num, Sat M.mem M.isSet bndFml (Function.update ρ 99 n.1) ↔
      ∃ γ, M.mem (M.op γ l) th ∧ γ ≠ l ∧ ∀ k : M.Num, k ≤ n → ∀ e,
        M.mem (M.trip u k.1 e) Nt → M.InNRaw P th io M.nat j.1 l e →
          M.InNRaw P th io M.nat j.1 γ e := by
    intro n
    have h1 : Sat M.mem M.isSet bndFml (Function.update ρ 99 n.1) ↔
        ∃ γ, M.mem (M.op γ l) th ∧ ¬ γ = l ∧ ∀ k, M.mem k M.nat → M.LeRaw M.adG k n.1 →
          ∀ e, M.mem (M.trip u k e) Nt → M.InNRaw P th io M.nat j.1 l e →
            M.InNRaw P th io M.nat j.1 γ e := by
      simp [bndFml, LeRaw, Sat, M.sat_imp, M.sat_ex, M.sat_fApp3', M.sat_fApp', M.sat_inNFml,
        Function.update_apply, e20, e22, e23, e24, e25, e27, e28, e151, e152]
    rw [h1]
    constructor
    · rintro ⟨γ, g1, g2, g3⟩
      exact ⟨γ, g1, g2, fun k hk e he heN =>
        g3 k.1 k.2 ((M.leRaw_iff had k n).mpr hk) e he heN⟩
    · rintro ⟨γ, g1, g2, g3⟩
      exact ⟨γ, g1, g2, fun k hk hle e he heN =>
        g3 ⟨k, hk⟩ ((M.leRaw_iff had ⟨k, hk⟩ n).mp hle) e he heN⟩
  have key := M.num_ind_fml (σW [(20, 7), (22, 5), (23, 7), (24, 5), (27, 3), (28, 7)])
      bndFml 99 rfl ρ
    (by
      rw [show M.zero = (0 : M.Num).1 from rfl, hsat 0]
      obtain ⟨γ', -, g2, g3, g4⟩ := M.bound_step hd (u := u) hl hβ hβne (0 : M.Num)
      refine ⟨γ', g2, g3, fun k hk e he heN => ?_⟩
      rcases M.eq_or_succ_le hk with e1 | e1
      · rw [e1] at he
        exact g4 e he heN
      · exact (M.succ_not_le_zero e1).elim)
    (fun k0 ih => by
      rw [hsat k0] at ih
      rw [show M.succ k0.1 = (k0 + 1).1 from (M.val_add_one k0).symm, hsat (k0 + 1)]
      obtain ⟨γ, g1, g2, g3⟩ := ih
      obtain ⟨γ', h1, h2, h3, h4⟩ := M.bound_step hd (u := u) hl g1 g2 (k0 + 1)
      refine ⟨γ', h2, h3, fun k hk e he heN => ?_⟩
      rcases M.eq_or_succ_le hk with e1 | e1
      · rw [e1] at he
        exact h4 e he heN
      · exact M.inN_mono hd (g3 k (M.le_of_succ_le_succ e1) e he heN) h1) n
  exact (hsat n).mp key

/-- **Limit levels satisfy separation for bounded formulas.** Let `l` be a limit stage, `β` a
stage below it, `c` a bounded formula and `u` a sequence of parameters. Then there are a stage
`γ` with `β ≤ γ < l` and a name `z` of rank below `l` whose members are the names `x` of rank
below `γ` such that `c` is true at stage `l` under `(x, u)`. -/
theorem sep_lim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l D u β : V}
    (hl : M.IsLim th l) (hβ : M.mem (M.op β l) th) (hβne : β ≠ l) (hD : M.IsD0 D)
    (c : M.Num) (hc : M.mem c.1 D) (hu : M.mem (M.op j.1 u) R) :
    ∃ γ z, M.mem (M.op β γ) th ∧ M.mem (M.op γ l) th ∧ γ ≠ l ∧
      M.InNRaw P th io M.nat j.1 l z ∧ ∀ x, M.EpsRaw P th io M.nat j.1 F x z ↔
        M.InNRaw P th io M.nat j.1 γ x ∧
          ∃ s, M.mem (M.quad j.1 x u s) P ∧ M.TrueAt P io F j.1 l c s := by
  obtain ⟨β', b1, b2, b3, b4⟩ := hl.2 β hβ hβne
  have hdβ' : M.InNRaw P th io M.nat j.1 β' d := M.d_inN hd b1 b2
  obtain ⟨γ1, g1, g2, g3⟩ := M.bound_lim hd (u := u) hl hβ hβne c
  rcases M.wo_total hd.hth (hd.hth.fld γ1 l g1).1 (hd.hth.fld β' l b3).1 with h | h
  · obtain ⟨z, hz, hmem⟩ := M.sep_d0 hd b3 b4 hdβ' hD c hc hu (fun k e hk he heN =>
      M.inN_mono hd (g3 k (le_trans (M.le_add_one k) hk) e he heN) h)
    exact ⟨β', z, b1, b3, b4, hz, hmem⟩
  · obtain ⟨z, hz, hmem⟩ := M.sep_d0 hd g1 g2 (M.inN_mono hd hdβ' h) hD c hc hu
      (fun k e hk he heN => g3 k (le_trans (M.le_add_one k) hk) e he heN)
    exact ⟨γ1, z, hd.hth.trans β β' γ1 b1 h, g1, g2, hz, hmem⟩

end hier23

/-! ### Axioms as coded sentences: extensionality -/

/-- The code of `A → B`. -/
noncomputable def cImp (A B : M.Num) : M.Num := M.cNeg (M.cAnd A (M.cNeg B))

theorem le_cNeg (c : M.Num) : c ≤ M.cNeg c := M.le_pairN_right 1 c

theorem le_cAnd_left (a b : M.Num) : a ≤ M.cAnd a b :=
  le_trans (M.le_pairN_left a b) (M.le_pairN_right 2 _)

theorem le_cAnd_right (a b : M.Num) : b ≤ M.cAnd a b :=
  le_trans (M.le_pairN_right a b) (M.le_pairN_right 2 _)

theorem le_cAll_var (v c : M.Num) : v ≤ M.cAll v c :=
  le_trans (M.le_pairN_left v c) (M.le_pairN_right 3 _)

theorem le_cAll_body (v c : M.Num) : c ≤ M.cAll v c :=
  le_trans (M.le_pairN_right v c) (M.le_pairN_right 3 _)

theorem le_cRel_left (r v w : M.Num) : v ≤ M.cRel r v w :=
  le_trans (M.le_pairN_left v w) (le_trans (M.le_pairN_right r _) (M.le_pairN_right 0 _))

theorem le_cRel_right (r v w : M.Num) : w ≤ M.cRel r v w :=
  le_trans (M.le_pairN_right v w) (le_trans (M.le_pairN_right r _) (M.le_pairN_right 0 _))

theorem le_cImp_left (A B : M.Num) : A ≤ M.cImp A B :=
  le_trans (M.le_cAnd_left A _) (M.le_cNeg _)

theorem le_cImp_right (A B : M.Num) : B ≤ M.cImp A B :=
  le_trans (M.le_cNeg B) (le_trans (M.le_cAnd_right A _) (M.le_cNeg _))

theorem le_cIff_left (A B : M.Num) : A ≤ M.cIff A B :=
  le_trans (le_trans (M.le_cAnd_left A (M.cNeg B)) (M.le_cNeg _)) (M.le_cAnd_left _ _)

theorem le_cIff_right (A B : M.Num) : B ≤ M.cIff A B :=
  le_trans (le_trans (M.le_cAnd_left B (M.cNeg A)) (M.le_cNeg _)) (M.le_cAnd_right _ _)

theorem le_cOr_left (A B : M.Num) : A ≤ M.cOr A B :=
  le_trans (le_trans (M.le_cNeg A) (M.le_cAnd_left _ _)) (M.le_cNeg _)

theorem le_cOr_right (A B : M.Num) : B ≤ M.cOr A B :=
  le_trans (le_trans (M.le_cNeg B) (M.le_cAnd_right _ _)) (M.le_cNeg _)

theorem le_cEq_left (z v w : M.Num) : v ≤ M.cEq z v w :=
  le_trans (M.le_cRel_right 0 z v) (le_trans (M.le_cIff_left _ _) (M.le_cAll_body z _))

theorem le_cEq_right (z v w : M.Num) : w ≤ M.cEq z v w :=
  le_trans (M.le_cRel_right 0 z w) (le_trans (M.le_cIff_right _ _) (M.le_cAll_body z _))

theorem le_cEx_var (v c : M.Num) : v ≤ M.cAll v (M.cNeg c) := M.le_cAll_var v _

theorem le_cEx_body (v c : M.Num) : c ≤ M.cAll v (M.cNeg c) :=
  le_trans (M.le_cNeg c) (M.le_cAll_body v _)

/-- Extensionality in the language without equality:
`∀x ∀y (∀z (z ε x ↔ z ε y) → ∀w (x ε w → y ε w))`. -/
noncomputable def cExt (x y z w : M.Num) : M.Num :=
  M.cAll x (M.cAll y (M.cImp (M.cEq z x y)
    (M.cAll w (M.cImp (M.cRel 0 x w) (M.cRel 0 y w)))))

section hier24

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

theorem hier_imp (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) (A B : M.Num) (t : V) :
    M.TrueAt P io F j.1 α (M.cImp A B) t ↔
      (M.TrueAt P io F j.1 α A t → M.TrueAt P io F j.1 α B t) := by
  have hunf : M.cImp A B = M.cNeg (M.cAnd A (M.cNeg B)) := rfl
  rw [hunf, M.hier_neg hd, M.hier_and hd, M.hier_neg hd]
  constructor
  · rintro ⟨-, hn⟩ hA
    by_contra hB
    exact hn ⟨hα, hA, hα, hB⟩
  · intro h
    exact ⟨hα, fun hh => hh.2.2.2 (h hh.2.1)⟩

/-- **Extensionality is true at every stage**, as a coded sentence. -/
theorem hier_ext (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) (x y z w : M.Num) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hwx : w ≠ x) (hwy : w ≠ y) (t : V) :
    M.TrueAt P io F j.1 α (M.cExt x y z w) t := by
  have hunf : M.cExt x y z w = M.cAll x (M.cAll y (M.cImp (M.cEq z x y)
    (M.cAll w (M.cImp (M.cRel 0 x w) (M.cRel 0 y w))))) := rfl
  rw [hunf, M.hier_all_ex hd]
  refine ⟨hα, fun a ha => ?_⟩
  obtain ⟨t1, hag1⟩ := M.exists_upd hd ha t x.1 (M.cAll x (M.cAll y (M.cImp (M.cEq z x y)
    (M.cAll w (M.cImp (M.cRel 0 x w) (M.cRel 0 y w))))))
  refine ⟨t1, hag1, ?_⟩
  have kx1 := M.agree_same hag1 (M.le_cAll_var x _)
  rw [M.hier_all_ex hd]
  refine ⟨hα, fun b hb => ?_⟩
  obtain ⟨t2, hag2⟩ := M.exists_upd hd hb t1 y.1 (M.cAll y (M.cImp (M.cEq z x y)
    (M.cAll w (M.cImp (M.cRel 0 x w) (M.cRel 0 y w)))))
  refine ⟨t2, hag2, ?_⟩
  have ky2 := M.agree_same hag2 (M.le_cAll_var y _)
  have kx2 := M.agree_other hag2
    (le_trans (M.le_cEq_left z x y) (le_trans (M.le_cImp_left _ _) (M.le_cAll_body y _)))
    hxy kx1
  rw [M.hier_imp hd hα]
  intro hEq
  have hsim : M.SimRaw P j.1 tp F a b :=
    (M.hier_eq_sim hd hα z x y hzx hzy kx2 ky2 ha hb).mp hEq
  rw [M.hier_all_ex hd]
  refine ⟨hα, fun c hc => ?_⟩
  obtain ⟨t3, hag3⟩ := M.exists_upd hd hc t2 w.1
    (M.cAll w (M.cImp (M.cRel 0 x w) (M.cRel 0 y w)))
  refine ⟨t3, hag3, ?_⟩
  have kw3 := M.agree_same hag3 (M.le_cAll_var w _)
  have kx3 := M.agree_other hag3
    (le_trans (M.le_cRel_left 0 x w) (le_trans (M.le_cImp_left _ _) (M.le_cAll_body w _)))
    (Ne.symm hwx) kx2
  have ky3 := M.agree_other hag3
    (le_trans (M.le_cRel_left 0 y w) (le_trans (M.le_cImp_right _ _) (M.le_cAll_body w _)))
    (Ne.symm hwy) ky2
  rw [M.hier_imp hd hα, M.rel_val hd x w hα kx3 kw3, M.rel_val hd y w hα ky3 kw3]
  exact fun h => M.epsStar_congr hd hsim (M.inN_refl hd hc) h

end hier24

/-! ### Axioms as coded sentences: pairing and union at limit stages -/

noncomputable def cPB (a b c x z : M.Num) : M.Num :=
  M.cIff (M.cRel 0 x c) (M.cOr (M.cEq z x a) (M.cEq z x b))

/-- Pairing: `∀a ∀b ∃c ∀x (x ε c ↔ (x ≈ a ∨ x ≈ b))`, with `≈` the formula of `cEq`. -/
noncomputable def cPairAx (a b c x z : M.Num) : M.Num :=
  M.cAll a (M.cAll b (M.cEx c (M.cAll x (M.cPB a b c x z))))

noncomputable def cUE (b x y : M.Num) : M.Num := M.cAnd (M.cRel 0 x y) (M.cRel 0 y b)

noncomputable def cUB (b c x y : M.Num) : M.Num :=
  M.cIff (M.cRel 0 x c) (M.cEx y (M.cUE b x y))

/-- Union: `∀b ∃c ∀x (x ε c ↔ ∃y (x ε y ∧ y ε b))`. -/
noncomputable def cUnionAx (b c x y : M.Num) : M.Num :=
  M.cAll b (M.cEx c (M.cAll x (M.cUB b c x y)))

section hier25

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **Pairing is true at every limit stage**, as a coded sentence. -/
theorem hier_pairing (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l : V}
    (hl : M.IsLim th l) (a b c x z : M.Num) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcx : c ≠ x) (hax : a ≠ x) (hbx : b ≠ x) (hzx : z ≠ x) (hza : z ≠ a) (hzb : z ≠ b)
    (t : V) : M.TrueAt P io F j.1 l (M.cPairAx a b c x z) t := by
  have hα := hl.1
  have hA4 : a ≤ M.cPB a b c x z :=
    le_trans (M.le_cEq_right z x a) (le_trans (M.le_cOr_left _ _) (M.le_cIff_right _ _))
  have hB4 : b ≤ M.cPB a b c x z :=
    le_trans (M.le_cEq_right z x b) (le_trans (M.le_cOr_right _ _) (M.le_cIff_right _ _))
  have hC4 : c ≤ M.cPB a b c x z := le_trans (M.le_cRel_right 0 x c) (M.le_cIff_left _ _)
  have h43 : M.cPB a b c x z ≤ M.cAll x (M.cPB a b c x z) := M.le_cAll_body x _
  have h32 : M.cAll x (M.cPB a b c x z) ≤ M.cAll c (M.cNeg (M.cAll x (M.cPB a b c x z))) :=
    M.le_cEx_body c _
  have h21 : M.cAll c (M.cNeg (M.cAll x (M.cPB a b c x z))) ≤
      M.cAll b (M.cEx c (M.cAll x (M.cPB a b c x z))) :=
    le_trans (M.le_cNeg _) (M.le_cAll_body b _)
  have hunf : M.cPairAx a b c x z =
      M.cAll a (M.cAll b (M.cEx c (M.cAll x (M.cPB a b c x z)))) := rfl
  rw [hunf, M.hier_all_ex hd]
  refine ⟨hα, fun A hA => ?_⟩
  obtain ⟨t1, hag1⟩ := M.exists_upd hd hA t a.1
    (M.cAll a (M.cAll b (M.cEx c (M.cAll x (M.cPB a b c x z)))))
  refine ⟨t1, hag1, ?_⟩
  have ka1 := M.agree_same hag1 (M.le_cAll_var a _)
  rw [M.hier_all_ex hd]
  refine ⟨hα, fun B hB => ?_⟩
  obtain ⟨t2, hag2⟩ := M.exists_upd hd hB t1 b.1
    (M.cAll b (M.cEx c (M.cAll x (M.cPB a b c x z))))
  refine ⟨t2, hag2, ?_⟩
  have kb2 := M.agree_same hag2 (M.le_cAll_var b _)
  have ka2 := M.agree_other hag2 (le_trans hA4 (le_trans h43 (le_trans h32 h21))) hab ka1
  obtain ⟨C, hC, hCmem⟩ := M.pair_lim hd hl hA hB
  rw [M.hier_ex hd hα]
  obtain ⟨t3, hag3⟩ := M.exists_upd hd hC t2 c.1
    (M.cAll c (M.cNeg (M.cAll x (M.cPB a b c x z))))
  refine ⟨C, hC, t3, hag3, ?_⟩
  have kc3 := M.agree_same hag3 (M.le_cAll_var c _)
  have ka3 := M.agree_other hag3 (le_trans hA4 (le_trans h43 h32)) hac ka2
  have kb3 := M.agree_other hag3 (le_trans hB4 (le_trans h43 h32)) hbc kb2
  rw [M.hier_all_ex hd]
  refine ⟨hα, fun X hX => ?_⟩
  obtain ⟨t4, hag4⟩ := M.exists_upd hd hX t3 x.1 (M.cAll x (M.cPB a b c x z))
  refine ⟨t4, hag4, ?_⟩
  have kx4 := M.agree_same hag4 (M.le_cAll_var x _)
  have kc4 := M.agree_other hag4 (le_trans hC4 h43) hcx kc3
  have ka4 := M.agree_other hag4 (le_trans hA4 h43) hax ka3
  have kb4 := M.agree_other hag4 (le_trans hB4 h43) hbx kb3
  have h4 : M.cPB a b c x z = M.cIff (M.cRel 0 x c) (M.cOr (M.cEq z x a) (M.cEq z x b)) := rfl
  rw [h4, M.hier_iff hd hα, M.rel_val hd x c hα kx4 kc4, M.hier_or hd hα,
    M.hier_eq_sim hd hα z x a hzx hza kx4 ka4 hX hA,
    M.hier_eq_sim hd hα z x b hzx hzb kx4 kb4 hX hB]
  exact hCmem X

/-- **Union is true at every limit stage**, as a coded sentence. -/
theorem hier_union (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l : V}
    (hl : M.IsLim th l) (b c x y : M.Num) (hbc : b ≠ c) (hcx : c ≠ x) (hbx : b ≠ x)
    (hxy : x ≠ y) (hby : b ≠ y) (t : V) :
    M.TrueAt P io F j.1 l (M.cUnionAx b c x y) t := by
  have hα := hl.1
  have hxE : x ≤ M.cAll y (M.cNeg (M.cUE b x y)) :=
    le_trans (le_trans (M.le_cRel_left 0 x y) (M.le_cAnd_left _ _)) (M.le_cEx_body y _)
  have hbE : b ≤ M.cAll y (M.cNeg (M.cUE b x y)) :=
    le_trans (le_trans (M.le_cRel_right 0 y b) (M.le_cAnd_right _ _)) (M.le_cEx_body y _)
  have hbU : b ≤ M.cUB b c x y := le_trans hbE (le_trans (M.le_cNeg _) (M.le_cIff_right _ _))
  have hcU : c ≤ M.cUB b c x y := le_trans (M.le_cRel_right 0 x c) (M.le_cIff_left _ _)
  have h32 : M.cUB b c x y ≤ M.cAll x (M.cUB b c x y) := M.le_cAll_body x _
  have h21 : M.cAll x (M.cUB b c x y) ≤ M.cAll c (M.cNeg (M.cAll x (M.cUB b c x y))) :=
    M.le_cEx_body c _
  have hunf : M.cUnionAx b c x y = M.cAll b (M.cEx c (M.cAll x (M.cUB b c x y))) := rfl
  rw [hunf, M.hier_all_ex hd]
  refine ⟨hα, fun B hB => ?_⟩
  obtain ⟨t1, hag1⟩ := M.exists_upd hd hB t b.1
    (M.cAll b (M.cEx c (M.cAll x (M.cUB b c x y))))
  refine ⟨t1, hag1, ?_⟩
  have kb1 := M.agree_same hag1 (M.le_cAll_var b _)
  obtain ⟨C, hC, hCmem⟩ := M.union_lim hd hl hB
  rw [M.hier_ex hd hα]
  obtain ⟨t2, hag2⟩ := M.exists_upd hd hC t1 c.1
    (M.cAll c (M.cNeg (M.cAll x (M.cUB b c x y))))
  refine ⟨C, hC, t2, hag2, ?_⟩
  have kc2 := M.agree_same hag2 (M.le_cAll_var c _)
  have kb2 := M.agree_other hag2 (le_trans hbU (le_trans h32 h21)) hbc kb1
  rw [M.hier_all_ex hd]
  refine ⟨hα, fun X hX => ?_⟩
  obtain ⟨t3, hag3⟩ := M.exists_upd hd hX t2 x.1 (M.cAll x (M.cUB b c x y))
  refine ⟨t3, hag3, ?_⟩
  have kx3 := M.agree_same hag3 (M.le_cAll_var x _)
  have kc3 := M.agree_other hag3 (le_trans hcU h32) hcx kc2
  have kb3 := M.agree_other hag3 (le_trans hbU h32) hbx kb2
  have h4 : M.cUB b c x y = M.cIff (M.cRel 0 x c) (M.cEx y (M.cUE b x y)) := rfl
  have h5 : M.cUE b x y = M.cAnd (M.cRel 0 x y) (M.cRel 0 y b) := rfl
  rw [h4, M.hier_iff hd hα, M.rel_val hd x c hα kx3 kc3, M.hier_ex hd hα, hCmem X]
  constructor
  · rintro ⟨Y, hXY, hYB⟩
    obtain ⟨Y', hY'N, hs, heY'⟩ := M.epsStar_rep hd hB hYB
    have hXY' := M.epsStar_congr hd (M.epsStar_left hd hXY) hs hXY
    obtain ⟨t4, hag4⟩ := M.exists_upd hd hY'N t3 y.1 (M.cAll y (M.cNeg (M.cUE b x y)))
    have ky4 := M.agree_same hag4 (M.le_cAll_var y _)
    have kx4 := M.agree_other hag4 hxE hxy kx3
    have kb4 := M.agree_other hag4 hbE hby kb3
    refine ⟨Y', hY'N, t4, hag4, ?_⟩
    rw [h5, M.hier_and hd, M.rel_val hd x y hα kx4 ky4, M.rel_val hd y b hα ky4 kb4]
    exact ⟨hα, hXY', Y', M.inN_refl hd hY'N, heY'⟩
  · rintro ⟨Y, hY, t4, hag4, htr⟩
    have ky4 := M.agree_same hag4 (M.le_cAll_var y _)
    have kx4 := M.agree_other hag4 hxE hxy kx3
    have kb4 := M.agree_other hag4 hbE hby kb3
    rw [h5, M.hier_and hd, M.rel_val hd x y hα kx4 ky4, M.rel_val hd y b hα ky4 kb4] at htr
    exact ⟨Y, htr.2.1, htr.2.2⟩

end hier25

/-! ### Axioms as coded sentences: foundation; the axioms in the level structures -/

/-- Foundation: `∀a (∃x (x ε a) → ∃x (x ε a ∧ ∀y (y ε x → ¬ y ε a)))`. -/
noncomputable def cFound (a x y : M.Num) : M.Num :=
  M.cAll a (M.cImp (M.cEx x (M.cRel 0 x a))
    (M.cEx x (M.cAnd (M.cRel 0 x a)
      (M.cAll y (M.cImp (M.cRel 0 y x) (M.cNeg (M.cRel 0 y a)))))))

theorem vr_ne_snd {t n n' : M.Num} (h : n ≠ n') : M.vr t n ≠ M.vr t n' :=
  fun e => h (M.pairN_inj e).2

theorem vr_ne_fst {t t' n n' : M.Num} (h : t ≠ t') : M.vr t n ≠ M.vr t' n' :=
  fun e => h (M.pairN_inj e).1

theorem form_imp {U E : V} {A B : M.Num} (hA : M.Form U E A) (hB : M.Form U E B) :
    M.Form U E (M.cImp A B) := M.form_neg (M.form_and hA (M.form_neg hB))

theorem form_iff {U E : V} {A B : M.Num} (hA : M.Form U E A) (hB : M.Form U E B) :
    M.Form U E (M.cIff A B) :=
  M.form_and (M.form_neg (M.form_and hA (M.form_neg hB)))
    (M.form_neg (M.form_and hB (M.form_neg hA)))

theorem form_or {U E : V} {A B : M.Num} (hA : M.Form U E A) (hB : M.Form U E B) :
    M.Form U E (M.cOr A B) := M.form_neg (M.form_and (M.form_neg hA) (M.form_neg hB))

theorem form_ex {U E : V} {A : M.Num} (hA : M.Form U E A) (t n : M.Num) :
    M.Form U E (M.cEx (M.vr t n) A) := M.form_neg (M.form_all (M.form_neg hA) t n)

theorem form_eq {U E : V} (t n v w : M.Num) : M.Form U E (M.cEq (M.vr t n) v w) :=
  M.form_all (M.form_iff (M.form_rel 0 _ v) (M.form_rel 0 _ w)) t n

section hier26

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **Foundation is true at every stage**, as a coded sentence. -/
theorem hier_found (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) (a x y : M.Num) (hax : a ≠ x) (hxy : x ≠ y) (hay : a ≠ y)
    (t : V) : M.TrueAt P io F j.1 α (M.cFound a x y) t := by
  have hunf : M.cFound a x y = M.cAll a (M.cImp (M.cEx x (M.cRel 0 x a))
    (M.cEx x (M.cAnd (M.cRel 0 x a)
      (M.cAll y (M.cImp (M.cRel 0 y x) (M.cNeg (M.cRel 0 y a))))))) := rfl
  have hx3 : x ≤ M.cAll y (M.cImp (M.cRel 0 y x) (M.cNeg (M.cRel 0 y a))) :=
    le_trans (M.le_cRel_right 0 y x) (le_trans (M.le_cImp_left _ _) (M.le_cAll_body y _))
  have ha3 : a ≤ M.cAll y (M.cImp (M.cRel 0 y x) (M.cNeg (M.cRel 0 y a))) :=
    le_trans (M.le_cRel_right 0 y a)
      (le_trans (M.le_cNeg _) (le_trans (M.le_cImp_right _ _) (M.le_cAll_body y _)))
  rw [hunf, M.hier_all_ex hd]
  refine ⟨hα, fun A hA => ?_⟩
  obtain ⟨t1, hag1⟩ := M.exists_upd hd hA t a.1 (M.cAll a (M.cImp (M.cEx x (M.cRel 0 x a))
    (M.cEx x (M.cAnd (M.cRel 0 x a)
      (M.cAll y (M.cImp (M.cRel 0 y x) (M.cNeg (M.cRel 0 y a))))))))
  refine ⟨t1, hag1, ?_⟩
  have ka1 := M.agree_same hag1 (M.le_cAll_var a _)
  rw [M.hier_imp hd hα]
  intro hex
  obtain ⟨X0, hX0, t', hag', htr'⟩ := (M.hier_ex hd hα x _ t1).mp hex
  have kx' := M.agree_same hag' (M.le_cEx_var x _)
  have ka' := M.agree_other hag' (le_trans (M.le_cRel_right 0 x a) (M.le_cEx_body x _)) hax ka1
  have hX0A := (M.rel_val hd x a hα kx' ka').mp htr'
  -- the set of the names that denote members of the set denoted by `A`
  obtain ⟨S, -, hS0⟩ := M.comp (σW [(6, 5), (20, 7), (22, 5), (24, 5), (27, 3)]) epsStarFml 70
    rfl (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => dflt) 6 F) 20 P) 21 tp) 22 th)
      24 io) 25 j.1) 27 M.nat) 73 A)
  have hS : ∀ z, M.mem z S ↔ M.EpsStarRaw P th io M.nat j.1 tp F z A := by
    intro z
    rw [hS0 z]
    simp [M.sat_epsStarFml, Function.update_apply]
  obtain ⟨β, r0, hβα, -⟩ := M.inN_rank hX0
  obtain ⟨b, hbS, hmin⟩ := M.eps_wf hd ((hS X0).mpr hX0A) r0 (hd.hth.fld β α hβα).1
    (fun z z' hz hs => (hS z').mpr
      (M.epsStar_congr hd (M.sim_symm hd hs) (M.inN_refl hd hA) ((hS z).mp hz)))
  obtain ⟨b', hb'N, hsb, heb'⟩ := M.epsStar_rep hd hA ((hS b).mp hbS)
  rw [M.hier_ex hd hα]
  obtain ⟨t2, hag2⟩ := M.exists_upd hd hb'N t1 x.1 (M.cAll x (M.cNeg (M.cAnd (M.cRel 0 x a)
    (M.cAll y (M.cImp (M.cRel 0 y x) (M.cNeg (M.cRel 0 y a)))))))
  refine ⟨b', hb'N, t2, hag2, ?_⟩
  have kx2 := M.agree_same hag2 (M.le_cAll_var x _)
  have ka2 := M.agree_other hag2
    (le_trans (le_trans (M.le_cRel_right 0 x a) (M.le_cAnd_left _ _)) (M.le_cEx_body x _))
    hax ka1
  rw [M.hier_and hd]
  refine ⟨hα, (M.rel_val hd x a hα kx2 ka2).mpr ⟨b', M.inN_refl hd hb'N, heb'⟩, ?_⟩
  rw [M.hier_all_ex hd]
  refine ⟨hα, fun Y hY => ?_⟩
  obtain ⟨t3, hag3⟩ := M.exists_upd hd hY t2 y.1
    (M.cAll y (M.cImp (M.cRel 0 y x) (M.cNeg (M.cRel 0 y a))))
  refine ⟨t3, hag3, ?_⟩
  have ky3 := M.agree_same hag3 (M.le_cAll_var y _)
  have kx3 := M.agree_other hag3 hx3 hxy kx2
  have ka3 := M.agree_other hag3 ha3 hay ka2
  rw [M.hier_imp hd hα, M.rel_val hd y x hα ky3 kx3, M.hier_neg hd,
    M.rel_val hd y a hα ky3 ka3]
  intro hYb'
  refine ⟨hα, fun hYA => ?_⟩
  exact hmin Y ((hS Y).mpr hYA)
    (M.epsStar_congr hd (M.epsStar_left hd hYA) (M.sim_symm hd hsb) hYb')

/-- **Extensionality, foundation, pairing and union hold in every limit level**, as coded
sentences in the set structure of the level, in the sense of §3.1. -/
theorem limit_level_axioms (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l β : V}
    (hl : M.IsLim th l) (hβ : M.mem (M.op β l) th) (hβne : β ≠ l) :
    ∃ U E, (∀ k a, M.mem (M.op k a) U ↔ M.mem k M.nat ∧ M.InNRaw P th io M.nat j.1 l a) ∧
      (∀ r a b, M.mem (M.trip r a b) E ↔ M.mem r M.nat ∧ M.InNRaw P th io M.nat j.1 l a ∧
        M.InNRaw P th io M.nat j.1 l b ∧ M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG
          (1 : M.Num).1 (2 : M.Num).1 F l r a b) ∧
      ∃ s, M.IsAsg U s ∧
        M.Holds U E (M.cExt (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3)) s ∧
        M.Holds U E (M.cFound (M.vr 0 0) (M.vr 0 1) (M.vr 0 2)) s ∧
        M.Holds U E (M.cPairAx (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3) (M.vr 1 0)) s ∧
        M.Holds U E (M.cUnionAx (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3)) s := by
  have hdN : M.InNRaw P th io M.nat j.1 l d := M.d_inN hd hβ hβne
  obtain ⟨U, E, hU, hE, hmod⟩ := M.level_models hd hl.1 hdN
  obtain ⟨s, hs, -, hiff⟩ := hmod d
  refine ⟨U, E, hU, hE, s, hs, ?_, ?_, ?_, ?_⟩
  · refine (hiff _ ?_).mpr (M.hier_ext hd hl.1 _ _ _ _ (M.vr_ne_snd M.n01)
      (M.vr_ne_snd M.n20) (M.vr_ne_snd M.n21) (M.vr_ne_snd M.n30) (M.vr_ne_snd M.n31) d)
    exact M.form_all (M.form_all (M.form_imp (M.form_eq 0 2 _ _)
      (M.form_all (M.form_imp (M.form_rel 0 _ _) (M.form_rel 0 _ _)) 0 3)) 0 1) 0 0
  · refine (hiff _ ?_).mpr (M.hier_found hd hl.1 _ _ _ (M.vr_ne_snd M.n01)
      (M.vr_ne_snd M.n12) (M.vr_ne_snd M.n02) d)
    exact M.form_all (M.form_imp (M.form_ex (M.form_rel 0 _ _) 0 1)
      (M.form_ex (M.form_and (M.form_rel 0 _ _)
        (M.form_all (M.form_imp (M.form_rel 0 _ _) (M.form_neg (M.form_rel 0 _ _))) 0 2)) 0 1))
      0 0
  · refine (hiff _ ?_).mpr (M.hier_pairing hd hl _ _ _ _ _ (M.vr_ne_snd M.n01)
      (M.vr_ne_snd M.n02) (M.vr_ne_snd M.n12) (M.vr_ne_snd M.n23) (M.vr_ne_snd M.n03)
      (M.vr_ne_snd M.n13) (M.vr_ne_fst M.n10) (M.vr_ne_fst M.n10) (M.vr_ne_fst M.n10) d)
    exact M.form_all (M.form_all (M.form_ex (M.form_all (M.form_iff (M.form_rel 0 _ _)
      (M.form_or (M.form_eq 1 0 _ _) (M.form_eq 1 0 _ _))) 0 3) 0 2) 0 1) 0 0
  · refine (hiff _ ?_).mpr (M.hier_union hd hl _ _ _ _ (M.vr_ne_snd M.n01)
      (M.vr_ne_snd M.n12) (M.vr_ne_snd M.n02) (M.vr_ne_snd M.n23) (M.vr_ne_snd M.n03) d)
    exact M.form_all (M.form_ex (M.form_all (M.form_iff (M.form_rel 0 _ _)
      (M.form_ex (M.form_and (M.form_rel 0 _ _) (M.form_rel 0 _ _)) 0 3)) 0 2) 0 1) 0 0

end hier26

/-! ### Successor stages and the ordinal names; the ordinal name of a limit stage -/

section hier27

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- The least stage. -/
theorem exists_least_stage (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {α : V}
    (hα : M.mem (M.op α α) th) :
    ∃ α0, M.mem (M.op α0 α0) th ∧ ∀ β, M.mem (M.op β β) th → M.mem (M.op α0 β) th := by
  obtain ⟨α0, -, -, -, -, -, -, hleast⟩ := hd.d_spec
  exact ⟨α0, (hd.hth.fld α0 α (hleast α hα)).1, hleast⟩

/-- The ordinal name of the least stage denotes the empty set. -/
theorem ordName_zero (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q α0 o : V}
    (hq : M.OrdQ P io j d q) (hα0 : M.mem (M.op α0 α0) th)
    (hleast : ∀ β, M.mem (M.op β β) th → M.mem (M.op α0 β) th)
    (ho : M.mem (M.quad j.1 α0 q o) P) (u : V) :
    ¬ M.EpsStarRaw P th io M.nat j.1 tp F u o := by
  rintro ⟨u', -, he⟩
  exact M.no_inN_least hd hleast ((M.ordName_mem hd hq hα0 ho u').mp he).1

/-- **Successor stages.** Above a stage that is not the last there is a least stage. -/
theorem exists_succ_stage (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {ζ ξ : V}
    (hζξ : M.mem (M.op ζ ξ) th) (hne : ζ ≠ ξ) :
    ∃ ζ', M.mem (M.op ζ ζ') th ∧ ζ ≠ ζ' ∧ M.mem (M.op ζ' ξ) th ∧
      ∀ γ, M.mem (M.op ζ γ) th → ζ ≠ γ → M.mem (M.op ζ' γ) th := by
  obtain ⟨B, -, hB0⟩ := M.comp (σW [(22, 5)]) (.and (fApp 22 141 140) (.neg (.eq 141 140)))
    140 rfl (Function.update (Function.update (fun _ => dflt) 22 th) 141 ζ)
  have hB : ∀ γ, M.mem γ B ↔ M.mem (M.op ζ γ) th ∧ ζ ≠ γ := by
    intro γ
    rw [hB0 γ]
    simp [Sat, M.sat_fApp', Function.update_apply]
  obtain ⟨ζ', hζ'B, -, hmin⟩ := hd.hth.least B
    ⟨ξ, (hB ξ).mpr ⟨hζξ, hne⟩, (hd.hth.fld ζ ξ hζξ).2⟩
  obtain ⟨h1, h2⟩ := (hB ζ').mp hζ'B
  exact ⟨ζ', h1, h2, hmin ξ ((hB ξ).mpr ⟨hζξ, hne⟩) (hd.hth.fld ζ ξ hζξ).2,
    fun γ g1 g2 => hmin γ ((hB γ).mpr ⟨g1, g2⟩) (hd.hth.fld ζ γ g1).2⟩

/-- **The ordinal name of a successor stage** denotes the set denoted by the ordinal name of
the stage together with that set itself. -/
theorem ordName_succ (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q ζ ζ' o o' : V}
    (hq : M.OrdQ P io j d q) (h1 : M.mem (M.op ζ ζ') th) (h2 : ζ ≠ ζ')
    (hsucc : ∀ γ, M.mem (M.op ζ γ) th → ζ ≠ γ → M.mem (M.op ζ' γ) th)
    (ho : M.mem (M.quad j.1 ζ q o) P) (ho' : M.mem (M.quad j.1 ζ' q o') P) (u : V) :
    M.EpsStarRaw P th io M.nat j.1 tp F u o' ↔
      (M.EpsStarRaw P th io M.nat j.1 tp F u o ∨ M.SimRaw P j.1 tp F u o) := by
  have hζ := (hd.hth.fld ζ ζ' h1).1
  have hζ' := (hd.hth.fld ζ ζ' h1).2
  have ro := M.ordName_rank hd hq ho
  constructor
  · rintro ⟨u', hs, he⟩
    obtain ⟨η, oη, hη1, hη2, hoη, hsim⟩ := M.ordName_members hd hq hζ' ho' he
    have hη := (hd.hth.fld η ζ' hη1).1
    have hus : M.SimRaw P j.1 tp F u oη := M.sim_trans hd hs hsim
    by_cases e : η = ζ
    · rw [e] at hoη
      rw [hd.hP.fn _ _ _ _ _ hoη ho] at hus
      exact Or.inr hus
    · rcases M.wo_total hd.hth hη hζ with h | h
      · refine Or.inl (M.epsStar_congr hd (M.sim_symm hd hus) (M.sim_refl hd ro hζ) ?_)
        exact (M.ordName_lt hd hq hη hζ hoη ho).mpr ⟨h, e⟩
      · exact (hη2 (hd.hth.antisymm η ζ' hη1 (hsucc η h (Ne.symm e)))).elim
  · rintro (⟨u', hs, he⟩ | hs)
    · obtain ⟨hu'N, hu'ord⟩ := (M.ordName_mem hd hq hζ ho u').mp he
      exact ⟨u', hs, (M.ordName_mem hd hq hζ' ho' u').mpr ⟨M.inN_mono hd hu'N h1, hu'ord⟩⟩
    · exact ⟨o, hs, (M.ordName_mem hd hq hζ' ho' o).mpr
        ⟨M.rank_inN ro h1 h2, M.ordN_ordName hd hq hζ ho⟩⟩

/-- **The ordinal name of a limit stage is closed under successors.** -/
theorem ordName_lim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q l ol x : V}
    (hq : M.OrdQ P io j d q) (hl : M.IsLim th l) (hol : M.mem (M.quad j.1 l q ol) P)
    (hx : M.EpsStarRaw P th io M.nat j.1 tp F x ol) :
    ∃ y, M.InNRaw P th io M.nat j.1 l y ∧ M.EpsStarRaw P th io M.nat j.1 tp F y ol ∧
      ∀ u, M.EpsStarRaw P th io M.nat j.1 tp F u y ↔
        (M.EpsStarRaw P th io M.nat j.1 tp F u x ∨ M.SimRaw P j.1 tp F u x) := by
  obtain ⟨x', hsx, hex'⟩ := hx
  obtain ⟨ζ, o, hζ1, hζ2, ho, hsim⟩ := M.ordName_members hd hq hl.1 hol hex'
  have hxo : M.SimRaw P j.1 tp F x o := M.sim_trans hd hsx hsim
  have hζ := (hd.hth.fld ζ l hζ1).1
  obtain ⟨γ, g1, g2, g3, g4⟩ := hl.2 ζ hζ1 hζ2
  obtain ⟨ζ', s1, s2, s3, s4⟩ := M.exists_succ_stage hd g1 g2
  have hζ' := (hd.hth.fld ζ ζ' s1).2
  have hζ'l : M.mem (M.op ζ' l) th := hd.hth.trans ζ' γ l s3 g3
  have hζ'ne : ζ' ≠ l := by
    intro e
    rw [e] at s3
    exact g4 (hd.hth.antisymm γ l g3 s3)
  obtain ⟨o', ho'⟩ := M.exists_ordName hd hq hζ'
  have ro' := M.ordName_rank hd hq ho'
  refine ⟨o', M.rank_inN ro' hζ'l hζ'ne,
    (M.ordName_lt hd hq hζ' hl.1 ho' hol).mpr ⟨hζ'l, hζ'ne⟩, fun u => ?_⟩
  rw [M.ordName_succ hd hq s1 s2 s4 ho ho' u]
  constructor
  · rintro (h | h)
    · exact Or.inl (M.epsStar_congr hd (M.epsStar_left hd h) (M.sim_symm hd hxo) h)
    · exact Or.inr (M.sim_trans hd h (M.sim_symm hd hxo))
  · rintro (h | h)
    · exact Or.inl (M.epsStar_congr hd (M.epsStar_left hd h) hxo h)
    · exact Or.inr (M.sim_trans hd h hxo)

end hier27

/-! ### Axioms as coded sentences: infinity -/

noncomputable def cI1 (w e u : M.Num) : M.Num :=
  M.cEx e (M.cAnd (M.cRel 0 e w) (M.cAll u (M.cNeg (M.cRel 0 u e))))

noncomputable def cI4 (u x y z : M.Num) : M.Num :=
  M.cIff (M.cRel 0 u y) (M.cOr (M.cRel 0 u x) (M.cEq z u x))

noncomputable def cI3 (w u x y z : M.Num) : M.Num :=
  M.cEx y (M.cAnd (M.cRel 0 y w) (M.cAll u (M.cI4 u x y z)))

noncomputable def cI2 (w u x y z : M.Num) : M.Num :=
  M.cAll x (M.cImp (M.cRel 0 x w) (M.cI3 w u x y z))

/-- Infinity: `∃w (∃e (e ε w ∧ ∀u ¬ u ε e) ∧ ∀x (x ε w → ∃y (y ε w ∧ ∀u (u ε y ↔ (u ε x ∨
u ≈ x)))))`. -/
noncomputable def cInf (w e u x y z : M.Num) : M.Num :=
  M.cEx w (M.cAnd (M.cI1 w e u) (M.cI2 w u x y z))

section hier28

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **Infinity is true at every stage above a limit stage that is not the least stage**, as
a coded sentence. The witness is the ordinal name of the limit stage. -/
theorem hier_inf (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l lam β : V}
    (hlam : M.IsLim th lam) (hβ : M.mem (M.op β lam) th) (hβne : β ≠ lam)
    (hlaml : M.mem (M.op lam l) th) (hne : lam ≠ l) (w e u x y z : M.Num)
    (hwe : w ≠ e) (heu : e ≠ u) (hwx : w ≠ x) (hwy : w ≠ y) (hxy : x ≠ y) (hyu : y ≠ u)
    (hxu : x ≠ u) (hzu : z ≠ u) (hzx : z ≠ x) (t : V) :
    M.TrueAt P io F j.1 l (M.cInf w e u x y z) t := by
  have hα : M.mem (M.op l l) th := (hd.hth.fld lam l hlaml).2
  obtain ⟨q, hq⟩ := M.exists_ordQ hd
  obtain ⟨ol, hol⟩ := M.exists_ordName hd hq hlam.1
  have holN : M.InNRaw P th io M.nat j.1 l ol :=
    M.rank_inN (M.ordName_rank hd hq hol) hlaml hne
  obtain ⟨α0, hα0, hleast⟩ := M.exists_least_stage hd hlam.1
  obtain ⟨o0, ho0⟩ := M.exists_ordName hd hq hα0
  have h0ne : α0 ≠ lam := by
    intro e0
    have h1 := hleast β (hd.hth.fld β lam hβ).1
    rw [e0] at h1
    exact hβne (hd.hth.antisymm β lam hβ h1)
  have ho0N : M.InNRaw P th io M.nat j.1 l o0 :=
    M.inN_mono hd (M.rank_inN (M.ordName_rank hd hq ho0) (hleast lam hlam.1) h0ne) hlaml
  have ho0ol := (M.ordName_lt hd hq hα0 hlam.1 ho0 hol).mpr ⟨hleast lam hlam.1, h0ne⟩
  have hunf : M.cInf w e u x y z = M.cEx w (M.cAnd (M.cI1 w e u) (M.cI2 w u x y z)) := rfl
  have h1unf : M.cI1 w e u =
      M.cEx e (M.cAnd (M.cRel 0 e w) (M.cAll u (M.cNeg (M.cRel 0 u e)))) := rfl
  have h2unf : M.cI2 w u x y z = M.cAll x (M.cImp (M.cRel 0 x w) (M.cI3 w u x y z)) := rfl
  have h3unf : M.cI3 w u x y z =
      M.cEx y (M.cAnd (M.cRel 0 y w) (M.cAll u (M.cI4 u x y z))) := rfl
  have h4unf : M.cI4 u x y z =
      M.cIff (M.cRel 0 u y) (M.cOr (M.cRel 0 u x) (M.cEq z u x)) := rfl
  have hx4 : x ≤ M.cI4 u x y z :=
    le_trans (M.le_cRel_right 0 u x) (le_trans (M.le_cOr_left _ _) (M.le_cIff_right _ _))
  have hy4 : y ≤ M.cI4 u x y z := le_trans (M.le_cRel_right 0 u y) (M.le_cIff_left _ _)
  rw [hunf, M.hier_ex hd hα]
  obtain ⟨t1, hag1⟩ := M.exists_upd hd holN t w.1
    (M.cAll w (M.cNeg (M.cAnd (M.cI1 w e u) (M.cI2 w u x y z))))
  refine ⟨ol, holN, t1, hag1, ?_⟩
  have kw1 := M.agree_same hag1 (M.le_cAll_var w _)
  rw [M.hier_and hd]
  refine ⟨hα, ?_, ?_⟩
  · rw [h1unf, M.hier_ex hd hα]
    obtain ⟨t2, hag2⟩ := M.exists_upd hd ho0N t1 e.1
      (M.cAll e (M.cNeg (M.cAnd (M.cRel 0 e w) (M.cAll u (M.cNeg (M.cRel 0 u e))))))
    refine ⟨o0, ho0N, t2, hag2, ?_⟩
    have ke2 := M.agree_same hag2 (M.le_cAll_var e _)
    have kw2 := M.agree_other hag2
      (le_trans (le_trans (M.le_cRel_right 0 e w) (M.le_cAnd_left _ _)) (M.le_cEx_body e _))
      hwe kw1
    rw [M.hier_and hd]
    refine ⟨hα, (M.rel_val hd e w hα ke2 kw2).mpr ho0ol, ?_⟩
    rw [M.hier_all_ex hd]
    refine ⟨hα, fun U hU => ?_⟩
    obtain ⟨t3, hag3⟩ := M.exists_upd hd hU t2 u.1 (M.cAll u (M.cNeg (M.cRel 0 u e)))
    refine ⟨t3, hag3, ?_⟩
    have ku3 := M.agree_same hag3 (M.le_cAll_var u _)
    have ke3 := M.agree_other hag3
      (le_trans (M.le_cRel_right 0 u e) (le_trans (M.le_cNeg _) (M.le_cAll_body u _))) heu ke2
    rw [M.hier_neg hd, M.rel_val hd u e hα ku3 ke3]
    exact ⟨hα, M.ordName_zero hd hq hα0 hleast ho0 U⟩
  · rw [h2unf, M.hier_all_ex hd]
    refine ⟨hα, fun X hX => ?_⟩
    obtain ⟨t4, hag4⟩ := M.exists_upd hd hX t1 x.1
      (M.cAll x (M.cImp (M.cRel 0 x w) (M.cI3 w u x y z)))
    refine ⟨t4, hag4, ?_⟩
    have kx4 := M.agree_same hag4 (M.le_cAll_var x _)
    have kw4 := M.agree_other hag4
      (le_trans (M.le_cRel_right 0 x w) (le_trans (M.le_cImp_left _ _) (M.le_cAll_body x _)))
      hwx kw1
    rw [M.hier_imp hd hα, M.rel_val hd x w hα kx4 kw4]
    intro hXol
    obtain ⟨Y, hYlam, hYol, hYmem⟩ := M.ordName_lim hd hq hlam hol hXol
    have hYN : M.InNRaw P th io M.nat j.1 l Y := M.inN_mono hd hYlam hlaml
    rw [h3unf, M.hier_ex hd hα]
    obtain ⟨t5, hag5⟩ := M.exists_upd hd hYN t4 y.1
      (M.cAll y (M.cNeg (M.cAnd (M.cRel 0 y w) (M.cAll u (M.cI4 u x y z)))))
    refine ⟨Y, hYN, t5, hag5, ?_⟩
    have ky5 := M.agree_same hag5 (M.le_cAll_var y _)
    have kw5 := M.agree_other hag5
      (le_trans (le_trans (M.le_cRel_right 0 y w) (M.le_cAnd_left _ _)) (M.le_cEx_body y _))
      hwy kw4
    have kx5 := M.agree_other hag5
      (le_trans (le_trans (le_trans hx4 (M.le_cAll_body u _)) (M.le_cAnd_right _ _))
        (M.le_cEx_body y _)) hxy kx4
    rw [M.hier_and hd]
    refine ⟨hα, (M.rel_val hd y w hα ky5 kw5).mpr hYol, ?_⟩
    rw [M.hier_all_ex hd]
    refine ⟨hα, fun U hU => ?_⟩
    obtain ⟨t6, hag6⟩ := M.exists_upd hd hU t5 u.1 (M.cAll u (M.cI4 u x y z))
    refine ⟨t6, hag6, ?_⟩
    have ku6 := M.agree_same hag6 (M.le_cAll_var u _)
    have ky6 := M.agree_other hag6 (le_trans hy4 (M.le_cAll_body u _)) hyu ky5
    have kx6 := M.agree_other hag6 (le_trans hx4 (M.le_cAll_body u _)) hxu kx5
    rw [h4unf, M.hier_iff hd hα, M.rel_val hd u y hα ku6 ky6, M.hier_or hd hα,
      M.rel_val hd u x hα ku6 kx6, M.hier_eq_sim hd hα z u x hzu hzx ku6 kx6 hU hX]
    exact hYmem U

/-- **Infinity holds in every level above a limit stage that is not the least stage**, as a
coded sentence in the set structure of the level, in the sense of §3.1. -/
theorem level_infinity (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l lam β : V}
    (hlam : M.IsLim th lam) (hβ : M.mem (M.op β lam) th) (hβne : β ≠ lam)
    (hlaml : M.mem (M.op lam l) th) (hne : lam ≠ l) :
    ∃ U E, (∀ k a, M.mem (M.op k a) U ↔ M.mem k M.nat ∧ M.InNRaw P th io M.nat j.1 l a) ∧
      (∀ r a b, M.mem (M.trip r a b) E ↔ M.mem r M.nat ∧ M.InNRaw P th io M.nat j.1 l a ∧
        M.InNRaw P th io M.nat j.1 l b ∧ M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG
          (1 : M.Num).1 (2 : M.Num).1 F l r a b) ∧
      ∃ s, M.IsAsg U s ∧ M.Holds U E
        (M.cInf (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3) (M.vr 1 0) (M.vr 1 1)) s := by
  have hα : M.mem (M.op l l) th := (hd.hth.fld lam l hlaml).2
  obtain ⟨U, E, hU, hE, hmod⟩ := M.level_models hd hα (M.d_inN hd hlaml hne)
  obtain ⟨s, hs, -, hiff⟩ := hmod d
  refine ⟨U, E, hU, hE, s, hs, (hiff _ ?_).mpr (M.hier_inf hd hlam hβ hβne hlaml hne _ _ _ _ _ _
    (M.vr_ne_snd M.n01) (M.vr_ne_snd M.n12) (M.vr_ne_snd M.n03) (M.vr_ne_fst M.n01)
    (M.vr_ne_fst M.n01) (M.vr_ne_fst M.n10) (M.vr_ne_snd M.n32) (M.vr_ne_fst M.n10)
    (M.vr_ne_fst M.n10) d)⟩
  exact M.form_ex (M.form_and
    (M.form_ex (M.form_and (M.form_rel 0 _ _) (M.form_all (M.form_neg (M.form_rel 0 _ _)) 0 2))
      0 1)
    (M.form_all (M.form_imp (M.form_rel 0 _ _)
      (M.form_ex (M.form_and (M.form_rel 0 _ _)
        (M.form_all (M.form_iff (M.form_rel 0 _ _)
          (M.form_or (M.form_rel 0 _ _) (M.form_eq 1 1 _ _))) 0 2)) 1 0)) 0 3)) 0 0

end hier28

/-! ### Limit stages exist -/

/-- **A well-ordering in which every well-ordering of a subset of a rung embeds properly has
a limit stage that is not the least.** The stage is the point whose predecessors are the
image of the natural numbers. -/
theorem exists_limit_stage {R E z S P H : V} {m i : M.Num} (h : M.IsLadder R E z S m)
    (hP : M.IsPairing R P m) (hi : i ≤ m) (hH : M.IsWO H)
    (hemb : ∀ w, M.IsWO w →
      (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) →
      M.Emb w H ∧ ¬ M.Emb H w) :
    ∃ l β, M.IsLim H l ∧ M.mem (M.op β l) H ∧ β ≠ l := by
  obtain ⟨u, v, hu, hv, huv⟩ := M.rung_two h hi
  obtain ⟨io, io_dom, io_tot, io_fun, io_inj, -⟩ := M.exists_numerals hP hi hu hv huv
  obtain ⟨w, hw, hwran, -, hwmem⟩ := M.wo_transport (g := io) M.isWO_natLe io_fun io_inj
    (fun e he => by
      obtain ⟨x, y, hx, -, -⟩ := M.mem_natLe.mp he
      obtain ⟨a, ha⟩ := io_tot x
      rw [hx] at ha
      exact ⟨a, ha⟩)
  have hwT : ∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R := by
    intro a b hab
    obtain ⟨⟨e, he⟩, ⟨e', he'⟩⟩ := hwran a b hab
    exact ⟨(io_dom _ _ he).2, (io_dom _ _ he').2⟩
  obtain ⟨⟨f, hf, hfull⟩, hnot⟩ := hemb w hw hwT
  rcases M.piso_onto_or_seg hH hf hfull with honto | ⟨l, hl, hseg⟩
  · exfalso
    refine hnot ⟨M.conv f, M.piso_conv hf, fun y hy => ?_⟩
    obtain ⟨x, hx⟩ := honto y hy
    exact ⟨x, M.mem_conv.mpr hx⟩
  · have num : ∀ n : M.Num, ∃ a y, M.mem (M.op n.1 a) io ∧ M.mem (M.op a y) f := by
      intro n
      obtain ⟨a, ha⟩ := io_tot n
      obtain ⟨y, hy⟩ := hfull a ((hwmem a a).mpr
        ⟨n.1, n.1, ha, ha, (M.natLe_iff n n).mpr (le_refl n)⟩)
      exact ⟨a, y, ha, hy⟩
    obtain ⟨a0, y0, ha0, hy0⟩ := num 0
    obtain ⟨h0l, h0ne⟩ := M.segOf_ran_lt hH hl hseg hy0
    refine ⟨l, y0, ⟨hl, fun β hβ hβne => ?_⟩, h0l, h0ne⟩
    obtain ⟨x, hx⟩ := hseg.2.2.2 β hβ hβne
    obtain ⟨e, e', he, -, hee'⟩ := (hwmem x x).mp (hf.1 x β hx).1
    obtain ⟨n, n', hn, -, -⟩ := M.mem_natLe.mp hee'
    rw [← hn] at he
    obtain ⟨a1, y1, ha1, hy1⟩ := num (n + 1)
    have hxa1 : M.mem (M.op x a1) w := (hwmem x a1).mpr
      ⟨n.1, (n + 1).1, he, ha1, (M.natLe_iff n (n + 1)).mpr (M.le_add_one n)⟩
    have hβy1 : M.mem (M.op β y1) H := (hf.2.1 x β a1 y1 hx hy1).mp hxa1
    obtain ⟨hy1l, hy1ne⟩ := M.segOf_ran_lt hH hl hseg hy1
    refine ⟨y1, hβy1, fun e1 => ?_, hy1l, hy1ne⟩
    rw [← e1] at hy1
    have hxa : x = a1 := M.piso_inj hw hf hx hy1
    rw [← hxa] at ha1
    have e2 : n = n + 1 := Subtype.ext (io_inj _ _ _ he ha1)
    exact M.not_succ_le n (le_of_eq e2.symm)

/-- The Hartogs well-ordering of a rung, with a limit stage that is not the least. -/
theorem hartogs_limit {R E z S P : V} {m i : M.Num} (h : M.IsLadder R E z S m)
    (hP : M.IsPairing R P m) (hi : i + 1 + 1 ≤ m) :
    ∃ H, M.IsWO H ∧ (∀ e, M.mem (M.op e e) H → M.mem (M.op (i + 1 + 1).1 e) R) ∧
      (∀ w, M.IsWO w →
        (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) →
        M.Emb w H ∧ ¬ M.Emb H w) ∧
      ∃ l β, M.IsLim H l ∧ M.mem (M.op β l) H ∧ β ≠ l := by
  obtain ⟨H, hH, h1, h2, -⟩ := M.hartogs h hP hi
  exact ⟨H, hH, h1, h2, M.exists_limit_stage h hP
    (le_trans (le_trans (M.le_add_one i) (M.le_add_one (i + 1))) hi) hH h2⟩

/-! ### A limit level in every ladder with a pairing -/

/-- **In every ladder with a pairing and rungs `i`, `i + 1`, `i + 2` there is a limit level
of the constructible hierarchy in which extensionality, foundation, pairing and union hold.**
The hierarchy runs along the Hartogs well-ordering `th` of rung `i`, its names are members of
rung `i + 2`, the stage `l` is a limit stage of `th`, and the four sentences hold in the set
structure of the level `l` in the sense of §3.1. -/
theorem exists_limit_level {R E z S P : V} {m i : M.Num} (h : M.IsLadder R E z S m)
    (hP : M.IsPairing R P m) (hi : i + 1 + 1 ≤ m) :
    ∃ th io Nt nle p F d tp qo Nu Pr l, M.HierData R P th io Nt nle p F d tp qo Nu Pr m (i + 1 + 1) ∧
      (∀ w, M.IsWO w →
        (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) →
        M.Emb w th ∧ ¬ M.Emb th w) ∧
      M.IsLim th l ∧
      ∃ U E, (∀ k a, M.mem (M.op k a) U ↔
          M.mem k M.nat ∧ M.InNRaw P th io M.nat (i + 1 + 1).1 l a) ∧
        (∀ r a b, M.mem (M.trip r a b) E ↔ M.mem r M.nat ∧
          M.InNRaw P th io M.nat (i + 1 + 1).1 l a ∧ M.InNRaw P th io M.nat (i + 1 + 1).1 l b ∧
          M.AtomAtRaw P th io M.nat Nt (i + 1 + 1).1 d tp qo Nu Pr M.adG
          (1 : M.Num).1 (2 : M.Num).1 F l r a b) ∧
        ∃ s, M.IsAsg U s ∧
          M.Holds U E (M.cExt (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3)) s ∧
          M.Holds U E (M.cFound (M.vr 0 0) (M.vr 0 1) (M.vr 0 2)) s ∧
          M.Holds U E (M.cPairAx (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3) (M.vr 1 0)) s ∧
          M.Holds U E (M.cUnionAx (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3)) s := by
  obtain ⟨H, hH, h1, h2, l, β, hl, hβ, hβne⟩ := M.hartogs_limit h hP hi
  obtain ⟨io, Nt, nle, p, F, d, tp, qo, Nu, Pr, hd, -⟩ := M.exists_hierData h hP hi hH
    (fun a b hab => ⟨h1 a (hH.fld a b hab).1, h1 b (hH.fld a b hab).2⟩) ⟨l, hl.1⟩ (M.cOrd 0 1 2 3) H
  exact ⟨H, io, Nt, nle, p, F, d, tp, qo, Nu, Pr, l, hd, h2, hl, M.limit_level_axioms hd hl hβ hβne⟩

/-! ### Limit stages are cofinal in the Hartogs well-ordering -/

/-- A well-ordering does not contain a copy of its sum with a nonempty well-ordering. -/
theorem not_emb_sum {R P : V} {m i : M.Num} (hP : M.IsPairing R P m) (hi : i ≤ m)
    {u v w w' s b0 : V} (huv : u ≠ v) (hu : M.mem (M.op i.1 u) R) (hv : M.mem (M.op i.1 v) R)
    (hw : M.IsWO w) (hw' : M.IsWO w')
    (hwT : ∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R)
    (hw'T : ∀ a b, M.mem (M.op a b) w' → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R)
    (hs : ∀ c c', M.mem (M.op c c') s ↔ M.SumRaw P i.1 u v w w' c c')
    (hb0 : M.mem (M.op b0 b0) w') : ¬ M.Emb s w := by
  rintro ⟨φ, hφ, hφtot⟩
  have hsWO := (M.wo_sum hP huv hw hw' hs).1
  have clash : ∀ {a b c : V}, M.mem (M.quad i.1 u a c) P → M.mem (M.quad i.1 v b c) P → False :=
    fun q q' => huv (hP.inj _ _ _ _ _ _ q q').1
  -- the map of `w` onto the first copy
  obtain ⟨τ, -, hτ0⟩ := M.comp (σW [(0, 4), (1, 5), (3, 7)])
    (Fml.ex 8 (Fml.ex 9 (.and (fPr 0 8 9) (.and (fApp4 3 5 6 8 9) (fApp 1 8 8))))) 0 rfl
    (Function.update (Function.update (Function.update (Function.update (fun _ => dflt) 1 w)
      3 P) 5 i.1) 6 u)
  have hτ1 : ∀ t, M.mem t τ ↔ ∃ a c, t = M.op a c ∧ M.mem (M.quad i.1 u a c) P ∧
      M.mem (M.op a a) w := by
    intro t
    rw [hτ0 t]
    simp [Sat, M.sat_ex, M.sat_fPr', M.sat_fApp4', M.sat_fApp', Function.update_apply]
  have hτ : ∀ a c, M.mem (M.op a c) τ ↔ M.mem (M.quad i.1 u a c) P ∧ M.mem (M.op a a) w := by
    intro a c
    constructor
    · intro h
      obtain ⟨a', c', e, h'⟩ := (hτ1 _).mp h
      obtain ⟨e1, e2⟩ := M.op_inj e
      rw [e1, e2]
      exact h'
    · intro h
      exact (hτ1 _).mpr ⟨a, c, rfl, h⟩
  have hτP : M.PIso w s τ := by
    refine ⟨fun a c h => ?_, fun a c a' c' h h' => ?_, fun a c a' h hle => ?_,
      fun a c c' h hle => ?_⟩
    · obtain ⟨q, ha⟩ := (hτ a c).mp h
      exact ⟨ha, (hs c c).mpr (Or.inl ⟨a, a, q, q, ha⟩)⟩
    · obtain ⟨q, ha⟩ := (hτ a c).mp h
      obtain ⟨q', ha'⟩ := (hτ a' c').mp h'
      constructor
      · intro hle
        exact (hs c c').mpr (Or.inl ⟨a, a', q, q', hle⟩)
      · intro hle
        rcases (hs c c').mp hle with ⟨a1, a1', r, r', l⟩ | ⟨b, b', r, r', l⟩ |
          ⟨a1, b, r, r', -, -⟩
        · rw [(hP.inj _ _ _ _ _ _ r q).2, (hP.inj _ _ _ _ _ _ r' q').2] at l
          exact l
        · exact (clash q r).elim
        · exact (clash q' r').elim
    · have ha' := (hw.fld a' a hle).1
      obtain ⟨c', hc'⟩ := hP.tot i hi u a' hu (hwT a' a hle).1
      exact ⟨c', (hτ a' c').mpr ⟨hc', ha'⟩⟩
    · obtain ⟨q, ha⟩ := (hτ a c).mp h
      rcases (hs c' c).mp hle with ⟨a1, a1', r, r', l⟩ | ⟨b, b', r, r', l⟩ |
        ⟨a1, b, r, r', ha1, -⟩
      · exact ⟨a1, (hτ a1 c').mpr ⟨r, (hw.fld a1 a1' l).1⟩⟩
      · exact (clash q r').elim
      · exact (clash q r').elim
  -- a point of the second copy is moved by the composite, which is impossible
  obtain ⟨x, hx⟩ := hP.tot i hi v b0 hv (hw'T b0 b0 hb0).1
  have hxs : M.mem (M.op x x) s := (hs x x).mpr (Or.inr (Or.inl ⟨b0, b0, hx, hx, hb0⟩))
  obtain ⟨y0, hy0⟩ := hφtot x hxs
  have hy0w := (hφ.1 x y0 hy0).2
  obtain ⟨c0, hc0⟩ := hP.tot i hi u y0 hu (hwT y0 y0 hy0w).1
  have h1 : M.mem (M.op x c0) (M.rcomp φ τ) := M.mem_rcomp.mpr ⟨y0, hy0, (hτ y0 c0).mpr ⟨hc0, hy0w⟩⟩
  have h2 : M.mem (M.op x x) (M.idf s) := M.mem_idf.mpr ⟨rfl, hxs⟩
  have e := M.piso_agree hsWO hsWO (M.piso_rcomp hφ hτP) (M.piso_idf hsWO) x c0 x h1 h2
  rw [e] at hc0
  exact clash hc0 hx

/-- **Limit stages are cofinal**: in a well-ordering `H` in which every well-ordering of a
subset of a rung embeds properly and whose proper initial segments are isomorphic to such
well-orderings, above every stage there is a limit stage. -/
theorem limit_above {R E z S P H : V} {m i : M.Num} (h : M.IsLadder R E z S m)
    (hP : M.IsPairing R P m) (hi : i ≤ m) (hH : M.IsWO H)
    (hemb : ∀ w, M.IsWO w →
      (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) →
      M.Emb w H ∧ ¬ M.Emb H w)
    (hseg : ∀ e, M.mem (M.op e e) H → ∃ w f, M.IsWO w ∧
      (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) ∧
      M.SegOf w H f e)
    {e : V} (he : M.mem (M.op e e) H) :
    ∃ l, M.IsLim H l ∧ M.mem (M.op e l) H ∧ e ≠ l := by
  obtain ⟨u, v, hu, hv, huv⟩ := M.rung_two h hi
  obtain ⟨io, io_dom, io_tot, io_fun, io_inj, -⟩ := M.exists_numerals hP hi hu hv huv
  obtain ⟨wN, hwN, hwNran, -, hwNmem⟩ := M.wo_transport (g := io) M.isWO_natLe io_fun io_inj
    (fun e he => by
      obtain ⟨x, y, hx, -, -⟩ := M.mem_natLe.mp he
      obtain ⟨a, ha⟩ := io_tot x
      rw [hx] at ha
      exact ⟨a, ha⟩)
  have hwNT : ∀ a b, M.mem (M.op a b) wN → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R := by
    intro a b hab
    obtain ⟨⟨e, he⟩, ⟨e', he'⟩⟩ := hwNran a b hab
    exact ⟨(io_dom _ _ he).2, (io_dom _ _ he').2⟩
  have numle : ∀ (n n' : M.Num) (a a' : V), M.mem (M.op n.1 a) io → M.mem (M.op n'.1 a') io →
      n ≤ n' → M.mem (M.op a a') wN :=
    fun n n' a a' ha ha' hle => (hwNmem a a').mpr ⟨n.1, n'.1, ha, ha', (M.natLe_iff n n').mpr hle⟩
  obtain ⟨n0, hn0⟩ := io_tot 0
  have hn0w : M.mem (M.op n0 n0) wN := numle 0 0 n0 n0 hn0 hn0 (le_refl 0)
  obtain ⟨w0, f0, hw0, hw0T, hseg0⟩ := hseg e he
  obtain ⟨s, hs⟩ := M.exists_sum P i.1 u v w0 wN
  obtain ⟨hsWO, hsT⟩ := M.wo_sum hP huv hw0 hwN hs
  have clash : ∀ {a b c : V}, M.mem (M.quad i.1 u a c) P → M.mem (M.quad i.1 v b c) P → False :=
    fun q q' => huv (hP.inj _ _ _ _ _ _ q q').1
  obtain ⟨h1, h2⟩ := hemb s hsWO hsT
  obtain ⟨l, g, hl, hsegl⟩ := M.seg_of_strict hH h1 h2
  -- every point of the sum has a point strictly above it
  have up : ∀ x, M.mem (M.op x x) s → ∃ x', M.mem (M.op x x') s ∧ x ≠ x' := by
    intro x hx
    rcases (hs x x).mp hx with ⟨a, a', q, q', la⟩ | ⟨b, b', q, q', lb⟩ | ⟨a, b, q, q', -, -⟩
    · obtain ⟨x', hx'⟩ := hP.tot i hi v n0 hv (hwNT n0 n0 hn0w).1
      refine ⟨x', (hs x x').mpr (Or.inr (Or.inr ⟨a, n0, q, hx', (hw0.fld a a' la).1, hn0w⟩)),
        fun e1 => ?_⟩
      rw [← e1] at hx'
      exact clash q hx'
    · obtain ⟨e1, e1', he1, -, hee⟩ := (hwNmem b b).mp (hwN.fld b b' lb).1
      obtain ⟨n, n', hn, -, -⟩ := M.mem_natLe.mp hee
      rw [← hn] at he1
      obtain ⟨b1, hb1⟩ := io_tot (n + 1)
      have hbb1 := numle n (n + 1) b b1 he1 hb1 (M.le_add_one n)
      obtain ⟨x', hx'⟩ := hP.tot i hi v b1 hv (hwNT b b1 hbb1).2
      refine ⟨x', (hs x x').mpr (Or.inr (Or.inl ⟨b, b1, q, hx', hbb1⟩)), fun e2 => ?_⟩
      rw [← e2] at hx'
      have e3 : b = b1 := (hP.inj _ _ _ _ _ _ q hx').2
      rw [← e3] at hb1
      have e4 : n = n + 1 := Subtype.ext (io_inj _ _ _ he1 hb1)
      exact M.not_succ_le n (le_of_eq e4.symm)
    · exact (clash q q').elim
  refine ⟨l, ⟨hl, fun β hβ hβne => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := hsegl.2.2.2 β hβ hβne
    obtain ⟨x', hxx', hne'⟩ := up x (hsegl.1.1 x β hx).1
    obtain ⟨γ, hγ⟩ := hsegl.2.1 x' (hsWO.fld x x' hxx').2
    obtain ⟨hγl, hγne⟩ := M.segOf_ran_lt hH hl hsegl hγ
    refine ⟨γ, (hsegl.1.2.1 x β x' γ hx hγ).mp hxx', fun e1 => ?_, hγl, hγne⟩
    rw [← e1] at hγ
    exact hne' (M.piso_inj hsWO hsegl.1 hx hγ)
  · have hnot : ¬ M.Emb s w0 :=
      M.not_emb_sum hP hi huv hu hv hw0 hwN hw0T hwNT hs hn0w
    have hiff := M.segOf_le_iff hsWO hH hl he hsegl hseg0
    rcases M.wo_total hH he hl with h3 | h3
    · refine ⟨h3, fun e1 => ?_⟩
      exact hnot (hiff.mp (by rw [e1]; exact hl))
    · exact (hnot (hiff.mp h3)).elim

/-! ### A limit level with extensionality, foundation, pairing, union and infinity -/

section hier29

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **Extensionality, foundation, pairing, union and infinity hold in every limit level above
a limit stage that is not the least**, as coded sentences in the set structure of the level,
in the sense of §3.1. -/
theorem limit_level_zf0 (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l lam β : V}
    (hl : M.IsLim th l) (hlam : M.IsLim th lam) (hβ : M.mem (M.op β lam) th) (hβne : β ≠ lam)
    (hlaml : M.mem (M.op lam l) th) (hne : lam ≠ l) :
    ∃ U E, (∀ k a, M.mem (M.op k a) U ↔ M.mem k M.nat ∧ M.InNRaw P th io M.nat j.1 l a) ∧
      (∀ r a b, M.mem (M.trip r a b) E ↔ M.mem r M.nat ∧ M.InNRaw P th io M.nat j.1 l a ∧
        M.InNRaw P th io M.nat j.1 l b ∧ M.AtomAtRaw P th io M.nat Nt j.1 d tp qo Nu Pr M.adG
          (1 : M.Num).1 (2 : M.Num).1 F l r a b) ∧
      ∃ s, M.IsAsg U s ∧
        M.Holds U E (M.cExt (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3)) s ∧
        M.Holds U E (M.cFound (M.vr 0 0) (M.vr 0 1) (M.vr 0 2)) s ∧
        M.Holds U E (M.cPairAx (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3) (M.vr 1 0)) s ∧
        M.Holds U E (M.cUnionAx (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3)) s ∧
        M.Holds U E
          (M.cInf (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3) (M.vr 1 0) (M.vr 1 1)) s := by
  obtain ⟨U, E, hU, hE, hmod⟩ := M.level_models hd hl.1 (M.d_inN hd hlaml hne)
  obtain ⟨s, hs, -, hiff⟩ := hmod d
  refine ⟨U, E, hU, hE, s, hs, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hiff _ ?_).mpr (M.hier_ext hd hl.1 _ _ _ _ (M.vr_ne_snd M.n01)
      (M.vr_ne_snd M.n20) (M.vr_ne_snd M.n21) (M.vr_ne_snd M.n30) (M.vr_ne_snd M.n31) d)
    exact M.form_all (M.form_all (M.form_imp (M.form_eq 0 2 _ _)
      (M.form_all (M.form_imp (M.form_rel 0 _ _) (M.form_rel 0 _ _)) 0 3)) 0 1) 0 0
  · refine (hiff _ ?_).mpr (M.hier_found hd hl.1 _ _ _ (M.vr_ne_snd M.n01)
      (M.vr_ne_snd M.n12) (M.vr_ne_snd M.n02) d)
    exact M.form_all (M.form_imp (M.form_ex (M.form_rel 0 _ _) 0 1)
      (M.form_ex (M.form_and (M.form_rel 0 _ _)
        (M.form_all (M.form_imp (M.form_rel 0 _ _) (M.form_neg (M.form_rel 0 _ _))) 0 2)) 0 1))
      0 0
  · refine (hiff _ ?_).mpr (M.hier_pairing hd hl _ _ _ _ _ (M.vr_ne_snd M.n01)
      (M.vr_ne_snd M.n02) (M.vr_ne_snd M.n12) (M.vr_ne_snd M.n23) (M.vr_ne_snd M.n03)
      (M.vr_ne_snd M.n13) (M.vr_ne_fst M.n10) (M.vr_ne_fst M.n10) (M.vr_ne_fst M.n10) d)
    exact M.form_all (M.form_all (M.form_ex (M.form_all (M.form_iff (M.form_rel 0 _ _)
      (M.form_or (M.form_eq 1 0 _ _) (M.form_eq 1 0 _ _))) 0 3) 0 2) 0 1) 0 0
  · refine (hiff _ ?_).mpr (M.hier_union hd hl _ _ _ _ (M.vr_ne_snd M.n01)
      (M.vr_ne_snd M.n12) (M.vr_ne_snd M.n02) (M.vr_ne_snd M.n23) (M.vr_ne_snd M.n03) d)
    exact M.form_all (M.form_ex (M.form_all (M.form_iff (M.form_rel 0 _ _)
      (M.form_ex (M.form_and (M.form_rel 0 _ _) (M.form_rel 0 _ _)) 0 3)) 0 2) 0 1) 0 0
  · refine (hiff _ ?_).mpr (M.hier_inf hd hlam hβ hβne hlaml hne _ _ _ _ _ _
      (M.vr_ne_snd M.n01) (M.vr_ne_snd M.n12) (M.vr_ne_snd M.n03) (M.vr_ne_fst M.n01)
      (M.vr_ne_fst M.n01) (M.vr_ne_fst M.n10) (M.vr_ne_snd M.n32) (M.vr_ne_fst M.n10)
      (M.vr_ne_fst M.n10) d)
    exact M.form_ex (M.form_and
      (M.form_ex (M.form_and (M.form_rel 0 _ _)
        (M.form_all (M.form_neg (M.form_rel 0 _ _)) 0 2)) 0 1)
      (M.form_all (M.form_imp (M.form_rel 0 _ _)
        (M.form_ex (M.form_and (M.form_rel 0 _ _)
          (M.form_all (M.form_iff (M.form_rel 0 _ _)
            (M.form_or (M.form_rel 0 _ _) (M.form_eq 1 1 _ _))) 0 2)) 1 0)) 0 3)) 0 0

end hier29

/-- **In every ladder with a pairing and rungs `i`, `i + 1`, `i + 2` there is a limit level of
the constructible hierarchy in which extensionality, foundation, pairing, union and infinity
hold.** The hierarchy runs along the Hartogs well-ordering `th` of rung `i`, its names are
members of rung `i + 2`, and the five sentences hold in the set structure of the level `l` in
the sense of §3.1. -/
theorem exists_zf0_level {R E z S P : V} {m i : M.Num} (h : M.IsLadder R E z S m)
    (hP : M.IsPairing R P m) (hi : i + 1 + 1 ≤ m) :
    ∃ th io Nt nle p F d tp qo Nu Pr l, M.HierData R P th io Nt nle p F d tp qo Nu Pr m (i + 1 + 1) ∧
      (∀ w, M.IsWO w →
        (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) →
        M.Emb w th ∧ ¬ M.Emb th w) ∧
      M.IsLim th l ∧
      ∃ U E, (∀ k a, M.mem (M.op k a) U ↔
          M.mem k M.nat ∧ M.InNRaw P th io M.nat (i + 1 + 1).1 l a) ∧
        (∀ r a b, M.mem (M.trip r a b) E ↔ M.mem r M.nat ∧
          M.InNRaw P th io M.nat (i + 1 + 1).1 l a ∧ M.InNRaw P th io M.nat (i + 1 + 1).1 l b ∧
          M.AtomAtRaw P th io M.nat Nt (i + 1 + 1).1 d tp qo Nu Pr M.adG
          (1 : M.Num).1 (2 : M.Num).1 F l r a b) ∧
        ∃ s, M.IsAsg U s ∧
          M.Holds U E (M.cExt (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3)) s ∧
          M.Holds U E (M.cFound (M.vr 0 0) (M.vr 0 1) (M.vr 0 2)) s ∧
          M.Holds U E (M.cPairAx (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3) (M.vr 1 0)) s ∧
          M.Holds U E (M.cUnionAx (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3)) s ∧
          M.Holds U E
            (M.cInf (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3) (M.vr 1 0) (M.vr 1 1)) s := by
  have hi0 : i ≤ m := le_trans (le_trans (M.le_add_one i) (M.le_add_one (i + 1))) hi
  obtain ⟨H, hH, h1, h2, h3⟩ := M.hartogs h hP hi
  obtain ⟨l1, β, hl1, hβ, hβne⟩ := M.exists_limit_stage h hP hi0 hH h2
  obtain ⟨l, hl, hl1l, hl1ne⟩ := M.limit_above h hP hi0 hH h2 h3 hl1.1
  obtain ⟨io, Nt, nle, p, F, d, tp, qo, Nu, Pr, hd, -⟩ := M.exists_hierData h hP hi hH
    (fun a b hab => ⟨h1 a (hH.fld a b hab).1, h1 b (hH.fld a b hab).2⟩) ⟨l, hl.1⟩ (M.cOrd 0 1 2 3) H
  exact ⟨H, io, Nt, nle, p, F, d, tp, qo, Nu, Pr, l, hd, h2, hl,
    M.limit_level_zf0 hd hl hl1 hβ hβne hl1l hl1ne⟩

/-! ### The finite stages and the numbers -/

/-- **The stages below the first limit stage are the numbers.** In a well-ordering `H` in
which every well-ordering of a subset of a rung embeds properly there are a limit stage `l`,
not the least, and a set function `N` that is an isomorphism of the natural numbers with
their order onto the stages below `l`. -/
theorem exists_omega_stage {R E z S P H : V} {m i : M.Num} (h : M.IsLadder R E z S m)
    (hP : M.IsPairing R P m) (hi : i ≤ m) (hH : M.IsWO H)
    (hemb : ∀ w, M.IsWO w →
      (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) →
      M.Emb w H ∧ ¬ M.Emb H w) :
    ∃ l N, M.IsLim H l ∧ (∃ β, M.mem (M.op β l) H ∧ β ≠ l) ∧
      (∀ n : M.Num, ∃ ξ, M.mem (M.op n.1 ξ) N) ∧
      (∀ k ξ, M.mem (M.op k ξ) N → M.mem k M.nat ∧ M.mem (M.op ξ l) H ∧ ξ ≠ l) ∧
      (∀ k ξ ξ', M.mem (M.op k ξ) N → M.mem (M.op k ξ') N → ξ = ξ') ∧
      (∀ ξ, M.mem (M.op ξ l) H → ξ ≠ l → ∃ n : M.Num, M.mem (M.op n.1 ξ) N) ∧
      ∀ (n n' : M.Num) (ξ ξ' : V), M.mem (M.op n.1 ξ) N → M.mem (M.op n'.1 ξ') N →
        (n ≤ n' ↔ M.mem (M.op ξ ξ') H) := by
  obtain ⟨u, v, hu, hv, huv⟩ := M.rung_two h hi
  obtain ⟨io, io_dom, io_tot, io_fun, io_inj, -⟩ := M.exists_numerals hP hi hu hv huv
  obtain ⟨w, hw, hwran, -, hwmem⟩ := M.wo_transport (g := io) M.isWO_natLe io_fun io_inj
    (fun e he => by
      obtain ⟨x, y, hx, -, -⟩ := M.mem_natLe.mp he
      obtain ⟨a, ha⟩ := io_tot x
      rw [hx] at ha
      exact ⟨a, ha⟩)
  have hwT : ∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R := by
    intro a b hab
    obtain ⟨⟨e, he⟩, ⟨e', he'⟩⟩ := hwran a b hab
    exact ⟨(io_dom _ _ he).2, (io_dom _ _ he').2⟩
  obtain ⟨h1, h2⟩ := hemb w hw hwT
  obtain ⟨l, f, hl, hseg⟩ := M.seg_of_strict hH h1 h2
  have hf := hseg.1
  have numle : ∀ (n n' : M.Num) (a a' : V), M.mem (M.op n.1 a) io → M.mem (M.op n'.1 a') io →
      n ≤ n' → M.mem (M.op a a') w :=
    fun n n' a a' ha ha' hle => (hwmem a a').mpr ⟨n.1, n'.1, ha, ha', (M.natLe_iff n n').mpr hle⟩
  have num : ∀ n : M.Num, ∃ a y, M.mem (M.op n.1 a) io ∧ M.mem (M.op a y) f := by
    intro n
    obtain ⟨a, ha⟩ := io_tot n
    obtain ⟨y, hy⟩ := hseg.2.1 a (numle n n a a ha ha (le_refl n))
    exact ⟨a, y, ha, hy⟩
  have hN : ∀ k ξ, M.mem (M.op k ξ) (M.rcomp io f) ↔
      ∃ a, M.mem (M.op k a) io ∧ M.mem (M.op a ξ) f := fun k ξ => M.mem_rcomp
  -- the limit property, as in `exists_limit_stage`
  have hlim : M.IsLim H l := by
    refine ⟨hl, fun β hβ hβne => ?_⟩
    obtain ⟨x, hx⟩ := hseg.2.2.2 β hβ hβne
    obtain ⟨e, e', he, -, hee'⟩ := (hwmem x x).mp (hf.1 x β hx).1
    obtain ⟨n, n', hn, -, -⟩ := M.mem_natLe.mp hee'
    rw [← hn] at he
    obtain ⟨a1, y1, ha1, hy1⟩ := num (n + 1)
    have hβy1 : M.mem (M.op β y1) H :=
      (hf.2.1 x β a1 y1 hx hy1).mp (numle n (n + 1) x a1 he ha1 (M.le_add_one n))
    obtain ⟨hy1l, hy1ne⟩ := M.segOf_ran_lt hH hl hseg hy1
    refine ⟨y1, hβy1, fun e1 => ?_, hy1l, hy1ne⟩
    rw [← e1] at hy1
    have hxa : x = a1 := M.piso_inj hw hf hx hy1
    rw [← hxa] at ha1
    have e2 : n = n + 1 := Subtype.ext (io_inj _ _ _ he ha1)
    exact M.not_succ_le n (le_of_eq e2.symm)
  obtain ⟨a0, y0, ha0, hy0⟩ := num 0
  obtain ⟨h0l, h0ne⟩ := M.segOf_ran_lt hH hl hseg hy0
  refine ⟨l, M.rcomp io f, hlim, ⟨y0, h0l, h0ne⟩, fun n => ?_, fun k ξ hk => ?_,
    fun k ξ ξ' hk hk' => ?_, fun ξ hξ hξne => ?_, fun n n' ξ ξ' hn hn' => ?_⟩
  · obtain ⟨a, y, ha, hy⟩ := num n
    exact ⟨y, (hN _ _).mpr ⟨a, ha, hy⟩⟩
  · obtain ⟨a, ha, hfa⟩ := (hN _ _).mp hk
    exact ⟨(io_dom _ _ ha).1, M.segOf_ran_lt hH hl hseg hfa⟩
  · obtain ⟨a, ha, hfa⟩ := (hN _ _).mp hk
    obtain ⟨a', ha', hfa'⟩ := (hN _ _).mp hk'
    rw [← io_fun _ _ _ ha ha'] at hfa'
    exact M.piso_fun hH hf hfa hfa'
  · obtain ⟨x, hx⟩ := hseg.2.2.2 ξ hξ hξne
    obtain ⟨e, e', he, -, -⟩ := (hwmem x x).mp (hf.1 x ξ hx).1
    exact ⟨⟨e, (io_dom _ _ he).1⟩, (hN _ _).mpr ⟨x, he, hx⟩⟩
  · obtain ⟨a, ha, hfa⟩ := (hN _ _).mp hn
    obtain ⟨a', ha', hfa'⟩ := (hN _ _).mp hn'
    constructor
    · intro hle
      exact (hf.2.1 a ξ a' ξ' hfa hfa').mp (numle n n' a a' ha ha' hle)
    · intro hle
      obtain ⟨e, e', he, he', hee'⟩ := (hwmem a a').mp ((hf.2.1 a ξ a' ξ' hfa hfa').mpr hle)
      rw [io_inj _ _ _ he ha, io_inj _ _ _ he' ha'] at hee'
      exact (M.natLe_iff n n').mp hee'

section hier30

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **The members of the ordinal name of the first limit stage are the ordinal names of the
stages numbered by the numbers of the model.** -/
theorem omega_members (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {q l ol N x : V}
    (hq : M.OrdQ P io j d q) (hl : M.mem (M.op l l) th) (hol : M.mem (M.quad j.1 l q ol) P)
    (hNonto : ∀ ξ, M.mem (M.op ξ l) th → ξ ≠ l → ∃ n : M.Num, M.mem (M.op n.1 ξ) N)
    (hx : M.EpsStarRaw P th io M.nat j.1 tp F x ol) :
    ∃ (n : M.Num) (ξ o : V), M.mem (M.op n.1 ξ) N ∧ M.mem (M.quad j.1 ξ q o) P ∧
      M.SimRaw P j.1 tp F x o := by
  obtain ⟨x', hs, he⟩ := hx
  obtain ⟨ξ, o, h1, h2, ho, hsim⟩ := M.ordName_members hd hq hl hol he
  obtain ⟨n, hn⟩ := hNonto ξ h1 h2
  exact ⟨n, ξ, o, hn, ho, M.sim_trans hd hs hsim⟩

end hier30

/-! ### Unordered and ordered pairs in the hierarchy -/

/-- `c` denotes the pair `{a, b}`. -/
def IsPairN (P th io F tp : V) (j : M.Num) (a b c : V) : Prop :=
  ∀ x, M.EpsStarRaw P th io M.nat j.1 tp F x c ↔ (M.SimRaw P j.1 tp F x a ∨ M.SimRaw P j.1 tp F x b)

/-- `c` denotes the ordered pair `{{a}, {a, b}}`. -/
def IsOPairN (P th io F tp : V) (j : M.Num) (a b c : V) : Prop :=
  ∃ s p, M.SimRaw P j.1 tp F s s ∧ M.SimRaw P j.1 tp F p p ∧ M.IsPairN P th io F tp j a a s ∧
    M.IsPairN P th io F tp j a b p ∧ M.IsPairN P th io F tp j s p c

section hier31

variable {R P th io Nt nle p F d tp qo Nu Pr : V} {m j : M.Num}

/-- **Limit levels are closed under ordered pairs.** -/
theorem opair_lim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {l a b : V}
    (hl : M.IsLim th l) (ha : M.InNRaw P th io M.nat j.1 l a)
    (hb : M.InNRaw P th io M.nat j.1 l b) :
    ∃ c, M.InNRaw P th io M.nat j.1 l c ∧ M.IsOPairN P th io F tp j a b c := by
  obtain ⟨s, hs, hsm⟩ := M.pair_lim hd hl ha ha
  obtain ⟨q, hq, hqm⟩ := M.pair_lim hd hl ha hb
  obtain ⟨c, hc, hcm⟩ := M.pair_lim hd hl hs hq
  exact ⟨c, hc, s, q, M.inN_refl hd hs, M.inN_refl hd hq, hsm, hqm, hcm⟩

/-- Membership in sets that are denoted by names denoting the same set. -/
theorem epsStar_sim (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {x c c' : V}
    (hs : M.SimRaw P j.1 tp F c c') (h : M.EpsStarRaw P th io M.nat j.1 tp F x c) :
    M.EpsStarRaw P th io M.nat j.1 tp F x c' :=
  M.epsStar_congr hd (M.epsStar_left hd h) hs h

/-- **Ordered pairs determine their components**, up to "denote the same set". -/
theorem opair_inj (hd : M.HierData R P th io Nt nle p F d tp qo Nu Pr m j) {a b a' b' c c' : V}
    (haa : M.SimRaw P j.1 tp F a a) (hbb : M.SimRaw P j.1 tp F b b)
    (ha'a' : M.SimRaw P j.1 tp F a' a') (hb'b' : M.SimRaw P j.1 tp F b' b')
    (h : M.IsOPairN P th io F tp j a b c) (h' : M.IsOPairN P th io F tp j a' b' c')
    (hcc : M.SimRaw P j.1 tp F c c') :
    M.SimRaw P j.1 tp F a a' ∧ M.SimRaw P j.1 tp F b b' := by
  obtain ⟨s, q, hss, hqq, hs, hq, hc⟩ := h
  obtain ⟨s', q', hs's', hq'q', hs', hq', hc'⟩ := h'
  have symm := fun {x y : V} (h : M.SimRaw P j.1 tp F x y) => M.sim_symm hd h
  have trans := fun {x y z : V} (h : M.SimRaw P j.1 tp F x y) (h' : M.SimRaw P j.1 tp F y z) =>
    M.sim_trans hd h h'
  -- the first components
  have haa' : M.SimRaw P j.1 tp F a a' := by
    rcases (hc' s).mp (M.epsStar_sim hd hcc ((hc s).mpr (Or.inl hss))) with h1 | h1
    · rcases (hs' a).mp (M.epsStar_sim hd h1 ((hs a).mpr (Or.inl haa))) with h2 | h2
      · exact h2
      · exact h2
    · rcases (hs a').mp (M.epsStar_sim hd (symm h1) ((hq' a').mpr (Or.inl ha'a'))) with h2 | h2
      · exact symm h2
      · exact symm h2
  refine ⟨haa', ?_⟩
  rcases (hc' q).mp (M.epsStar_sim hd hcc ((hc q).mpr (Or.inr hqq))) with h1 | h1
  · -- `{a, b}` is `{a'}`
    have hba' : M.SimRaw P j.1 tp F b a' := by
      rcases (hs' b).mp (M.epsStar_sim hd h1 ((hq b).mpr (Or.inr hbb))) with h2 | h2
      · exact h2
      · exact h2
    rcases (hc q').mp (M.epsStar_sim hd (symm hcc) ((hc' q').mpr (Or.inr hq'q'))) with h3 | h3
    · rcases (hs b').mp (M.epsStar_sim hd h3 ((hq' b').mpr (Or.inr hb'b'))) with h4 | h4
      · exact trans hba' (trans (symm haa') (symm h4))
      · exact trans hba' (trans (symm haa') (symm h4))
    · rcases (hs' b').mp (M.epsStar_sim hd (trans h3 h1) ((hq' b').mpr (Or.inr hb'b')))
        with h4 | h4
      · exact trans hba' (symm h4)
      · exact trans hba' (symm h4)
  · -- `{a, b}` is `{a', b'}`
    rcases (hq' b).mp (M.epsStar_sim hd h1 ((hq b).mpr (Or.inr hbb))) with h2 | h2
    · have hba : M.SimRaw P j.1 tp F b a := trans h2 (symm haa')
      rcases (hq b').mp (M.epsStar_sim hd (symm h1) ((hq' b').mpr (Or.inr hb'b'))) with h3 | h3
      · exact trans hba (symm h3)
      · exact symm h3
    · exact h2

end hier31

/-! ### Good stages are cofinal in the Hartogs well-ordering -/

/-- `l` is a good stage: a limit stage that is a limit of limit stages. -/
def IsGood (th l : V) : Prop :=
  M.IsLim th l ∧ ∀ β, M.mem (M.op β l) th → β ≠ l →
    ∃ γ, M.IsLim th γ ∧ M.mem (M.op β γ) th ∧ β ≠ γ ∧ M.mem (M.op γ l) th ∧ γ ≠ l

/-- The point of the second copy of a sum with coordinates the numbers `n`, `k`. -/
def LexPt (P io i v : V) (n k : M.Num) (x : V) : Prop :=
  ∃ a b c, M.mem (M.op n.1 a) io ∧ M.mem (M.op k.1 b) io ∧ M.mem (M.quad i a b c) P ∧
    M.mem (M.quad i v c x) P

/-- **Good stages are cofinal**: under the hypotheses of `limit_above`, above every stage
there is a limit stage that is a limit of limit stages. Its predecessors are a copy of the
predecessors of the given stage followed by a copy of the pairs of numbers in the
lexicographic order. -/
theorem good_above {R E z S P H : V} {m i : M.Num} (h : M.IsLadder R E z S m)
    (hP : M.IsPairing R P m) (hi : i ≤ m) (hH : M.IsWO H)
    (hemb : ∀ w, M.IsWO w →
      (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) →
      M.Emb w H ∧ ¬ M.Emb H w)
    (hseg : ∀ e, M.mem (M.op e e) H → ∃ w f, M.IsWO w ∧
      (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) ∧
      M.SegOf w H f e)
    {e : V} (he : M.mem (M.op e e) H) :
    ∃ l, M.IsGood H l ∧ M.mem (M.op e l) H ∧ e ≠ l := by
  obtain ⟨u, v, hu, hv, huv⟩ := M.rung_two h hi
  obtain ⟨io, io_dom, io_tot, io_fun, io_inj, -⟩ := M.exists_numerals hP hi hu hv huv
  obtain ⟨wN, hwN, hwNran, -, hwNmem⟩ := M.wo_transport (g := io) M.isWO_natLe io_fun io_inj
    (fun e he => by
      obtain ⟨x, y, hx, -, -⟩ := M.mem_natLe.mp he
      obtain ⟨a, ha⟩ := io_tot x
      rw [hx] at ha
      exact ⟨a, ha⟩)
  have numle : ∀ (n n' : M.Num) (a a' : V), M.mem (M.op n.1 a) io → M.mem (M.op n'.1 a') io →
      n ≤ n' → M.mem (M.op a a') wN :=
    fun n n' a a' ha ha' hle => (hwNmem a a').mpr ⟨n.1, n'.1, ha, ha', (M.natLe_iff n n').mpr hle⟩
  have numge : ∀ (n n' : M.Num) (a a' : V), M.mem (M.op n.1 a) io → M.mem (M.op n'.1 a') io →
      M.mem (M.op a a') wN → n ≤ n' := by
    intro n n' a a' ha ha' hle
    obtain ⟨e1, e1', he1, he1', hee⟩ := (hwNmem a a').mp hle
    rw [io_inj _ _ _ he1 ha, io_inj _ _ _ he1' ha'] at hee
    exact (M.natLe_iff n n').mp hee
  have numfld : ∀ a, M.mem (M.op a a) wN → ∃ n : M.Num, M.mem (M.op n.1 a) io := by
    intro a ha
    obtain ⟨e1, e1', he1, -, -⟩ := (hwNmem a a).mp ha
    exact ⟨⟨e1, (io_dom _ _ he1).1⟩, he1⟩
  obtain ⟨w0, f0, hw0, hw0T, hseg0⟩ := hseg e he
  obtain ⟨q, hq⟩ := M.exists_lex P i.1 wN wN
  obtain ⟨hqWO, hqT⟩ := M.wo_lex hP hwN hwN hq
  obtain ⟨s, hs⟩ := M.exists_sum P i.1 u v w0 q
  obtain ⟨hsWO, hsT⟩ := M.wo_sum hP huv hw0 hqWO hs
  have clash : ∀ {a b c : V}, M.mem (M.quad i.1 u a c) P → M.mem (M.quad i.1 v b c) P → False :=
    fun r r' => huv (hP.inj _ _ _ _ _ _ r r').1
  have ptq : ∀ {n k : M.Num} {a b c : V}, M.mem (M.op n.1 a) io → M.mem (M.op k.1 b) io →
      M.mem (M.quad i.1 a b c) P → M.mem (M.op c c) q := by
    intro n k a b c ha hb hc
    have haw := numle n n a a ha ha (le_refl n)
    have hbw := numle k k b b hb hb (le_refl k)
    exact (hq c c).mpr ⟨a, b, a, b, hc, hc, haw, haw, hbw, hbw, Or.inr ⟨rfl, hbw⟩⟩
  have pt_ex : ∀ n k : M.Num, ∃ x, M.LexPt P io i.1 v n k x := by
    intro n k
    obtain ⟨a, ha⟩ := io_tot n
    obtain ⟨b, hb⟩ := io_tot k
    obtain ⟨c, hc⟩ := hP.tot i hi a b (io_dom _ _ ha).2 (io_dom _ _ hb).2
    obtain ⟨x, hx⟩ := hP.tot i hi v c hv (hP.dom _ _ _ _ hc).2.2.2
    exact ⟨x, a, b, c, ha, hb, hc, hx⟩
  have pt_fun : ∀ {n k : M.Num} {x x' : V}, M.LexPt P io i.1 v n k x →
      M.LexPt P io i.1 v n k x' → x = x' := by
    rintro n k x x' ⟨a, b, c, ha, hb, hc, hx⟩ ⟨a', b', c', ha', hb', hc', hx'⟩
    rw [← io_fun _ _ _ ha ha', ← io_fun _ _ _ hb hb'] at hc'
    rw [← hP.fn _ _ _ _ _ hc hc'] at hx'
    exact hP.fn _ _ _ _ _ hx hx'
  have pt_inj : ∀ {n k n' k' : M.Num} {x : V}, M.LexPt P io i.1 v n k x →
      M.LexPt P io i.1 v n' k' x → n = n' ∧ k = k' := by
    rintro n k n' k' x ⟨a, b, c, ha, hb, hc, hx⟩ ⟨a', b', c', ha', hb', hc', hx'⟩
    have e1 : c = c' := (hP.inj _ _ _ _ _ _ hx hx').2
    rw [← e1] at hc'
    obtain ⟨e2, e3⟩ := hP.inj _ _ _ _ _ _ hc hc'
    rw [← e2] at ha'
    rw [← e3] at hb'
    exact ⟨Subtype.ext (io_inj _ _ _ ha ha'), Subtype.ext (io_inj _ _ _ hb hb')⟩
  have pt_le : ∀ {n k n' k' : M.Num} {x x' : V}, M.LexPt P io i.1 v n k x →
      M.LexPt P io i.1 v n' k' x' → ((n ≤ n' ∧ n ≠ n') ∨ (n = n' ∧ k ≤ k')) →
      M.mem (M.op x x') s := by
    rintro n k n' k' x x' ⟨a, b, c, ha, hb, hc, hx⟩ ⟨a', b', c', ha', hb', hc', hx'⟩ hord
    refine (hs x x').mpr (Or.inr (Or.inl ⟨c, c', hx, hx', (hq c c').mpr ⟨a, b, a', b', hc, hc',
      numle n n a a ha ha (le_refl n), numle n' n' a' a' ha' ha' (le_refl n'),
      numle k k b b hb hb (le_refl k), numle k' k' b' b' hb' hb' (le_refl k'), ?_⟩⟩))
    rcases hord with ⟨o1, o2⟩ | ⟨o1, o2⟩
    · refine Or.inl ⟨numle n n' a a' ha ha' o1, fun e1 => o2 ?_⟩
      rw [← e1] at ha'
      exact Subtype.ext (io_inj _ _ _ ha ha')
    · refine Or.inr ⟨?_, numle k k' b b' hb hb' o2⟩
      rw [← o1] at ha'
      exact io_fun _ _ _ ha ha'
  have pt_ge : ∀ {n k n' k' : M.Num} {x x' : V}, M.LexPt P io i.1 v n k x →
      M.LexPt P io i.1 v n' k' x' → M.mem (M.op x x') s →
      ((n ≤ n' ∧ n ≠ n') ∨ (n = n' ∧ k ≤ k')) := by
    rintro n k n' k' x x' ⟨a, b, c, ha, hb, hc, hx⟩ ⟨a', b', c', ha', hb', hc', hx'⟩ hle
    rcases (hs x x').mp hle with ⟨a1, a1', r, r', -⟩ | ⟨c1, c1', r, r', lq⟩ | ⟨a1, b1, r, r', -, -⟩
    · exact (clash r hx).elim
    · rw [(hP.inj _ _ _ _ _ _ r hx).2, (hP.inj _ _ _ _ _ _ r' hx').2] at lq
      obtain ⟨A, B, A', B', rc, rc', -, -, -, -, hord⟩ := (hq c c').mp lq
      obtain ⟨eA, eB⟩ := hP.inj _ _ _ _ _ _ rc hc
      obtain ⟨eA', eB'⟩ := hP.inj _ _ _ _ _ _ rc' hc'
      rw [eA, eA', eB, eB'] at hord
      rcases hord with ⟨o1, o2⟩ | ⟨o1, o2⟩
      · refine Or.inl ⟨numge n n' a a' ha ha' o1, fun e1 => o2 ?_⟩
        rw [← e1] at ha'
        exact io_fun _ _ _ ha ha'
      · refine Or.inr ⟨?_, numge k k' b b' hb hb' o2⟩
        rw [← o1] at ha'
        exact Subtype.ext (io_inj _ _ _ ha ha')
    · exact (clash r hx).elim
  have u_lt : ∀ {x a xs : V} {n k : M.Num}, M.mem (M.quad i.1 u a x) P → M.mem (M.op a a) w0 →
      M.LexPt P io i.1 v n k xs → M.mem (M.op x xs) s ∧ x ≠ xs := by
    rintro x a xs n k r ha ⟨a', b', c', ha', hb', hc', hx'⟩
    refine ⟨(hs x xs).mpr (Or.inr (Or.inr ⟨a, c', r, hx', ha, ptq ha' hb' hc'⟩)), fun e1 => ?_⟩
    rw [← e1] at hx'
    exact clash r hx'
  have cls : ∀ x, M.mem (M.op x x) s → (∃ a, M.mem (M.quad i.1 u a x) P ∧ M.mem (M.op a a) w0) ∨
      ∃ n k : M.Num, M.LexPt P io i.1 v n k x := by
    intro x hx
    rcases (hs x x).mp hx with ⟨a, a', r, r', la⟩ | ⟨c, c', r, r', lq⟩ | ⟨a, b, r, r', -, -⟩
    · exact Or.inl ⟨a, r, (hw0.fld a a' la).1⟩
    · obtain ⟨A, B, A', B', rc, -, hA, -, hB, -, -⟩ := (hq c c').mp lq
      obtain ⟨n, hn⟩ := numfld A hA
      obtain ⟨k, hk⟩ := numfld B hB
      exact Or.inr ⟨n, k, A, B, c, hn, hk, rc, r⟩
    · exact (clash r r').elim
  have ne_succ : ∀ n : M.Num, n ≠ n + 1 := fun n e1 => M.not_succ_le n (le_of_eq e1.symm)
  have zero_ne : ∀ n : M.Num, (0 : M.Num) ≠ n + 1 :=
    fun n e1 => M.succ_not_le_zero (le_of_eq e1.symm)
  obtain ⟨h1, h2⟩ := hemb s hsWO hsT
  obtain ⟨l, g, hl, hsegl⟩ := M.seg_of_strict hH h1 h2
  have hg := hsegl.1
  obtain ⟨x00, hx00⟩ := pt_ex 0 0
  have star : ∀ x, M.mem (M.op x x) s → ∃ (n : M.Num) (xs : V),
      M.LexPt P io i.1 v (n + 1) 0 xs ∧ M.mem (M.op x xs) s ∧ x ≠ xs := by
    intro x hx
    rcases cls x hx with ⟨a, r, ha⟩ | ⟨n, k, hpt⟩
    · obtain ⟨xs, hxs⟩ := pt_ex (0 + 1) 0
      obtain ⟨h3, h4⟩ := u_lt r ha hxs
      exact ⟨0, xs, hxs, h3, h4⟩
    · obtain ⟨xs, hxs⟩ := pt_ex (n + 1) 0
      refine ⟨n, xs, hxs, pt_le hpt hxs (Or.inl ⟨M.le_add_one n, ne_succ n⟩), fun e1 => ?_⟩
      rw [← e1] at hxs
      exact ne_succ n (pt_inj hpt hxs).1
  have gstep : ∀ {x x' β : V}, M.mem (M.op x β) g → M.mem (M.op x x') s → x ≠ x' →
      ∃ γ, M.mem (M.op x' γ) g ∧ M.mem (M.op β γ) H ∧ β ≠ γ ∧ M.mem (M.op γ l) H ∧ γ ≠ l := by
    intro x x' β hx hxx' hne'
    obtain ⟨γ, hγ⟩ := hsegl.2.1 x' (hsWO.fld x x' hxx').2
    obtain ⟨hγl, hγne⟩ := M.segOf_ran_lt hH hl hsegl hγ
    refine ⟨γ, hγ, (hg.2.1 x β x' γ hx hγ).mp hxx', fun e1 => ?_, hγl, hγne⟩
    rw [← e1] at hγ
    exact hne' (M.piso_inj hsWO hg hx hγ)
  have hlim : M.IsLim H l := by
    refine ⟨hl, fun β hβ hβne => ?_⟩
    obtain ⟨x, hx⟩ := hsegl.2.2.2 β hβ hβne
    obtain ⟨n, xs, -, h3, h4⟩ := star x (hg.1 x β hx).1
    obtain ⟨γ, -, g1, g2, g3, g4⟩ := gstep hx h3 h4
    exact ⟨γ, g1, g2, g3, g4⟩
  refine ⟨l, ⟨hlim, fun β hβ hβne => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := hsegl.2.2.2 β hβ hβne
    obtain ⟨n, xs, hxs, h3, h4⟩ := star x (hg.1 x β hx).1
    obtain ⟨γ, hγ, g1, g2, g3, g4⟩ := gstep hx h3 h4
    refine ⟨γ, ⟨(hH.fld γ l g3).1, fun β' hβ' hβ'ne => ?_⟩, g1, g2, g3, g4⟩
    have hβ'nel : β' ≠ l := by
      intro e1
      rw [e1] at hβ'
      exact g4 (hH.antisymm γ l g3 hβ')
    obtain ⟨x', hx'⟩ := hsegl.2.2.2 β' (hH.trans β' γ l hβ' g3) hβ'nel
    have hx'xs : M.mem (M.op x' xs) s := (hg.2.1 x' β' xs γ hx' hγ).mpr hβ'
    have hx'ne : x' ≠ xs := by
      intro e1
      rw [e1] at hx'
      exact hβ'ne (M.piso_fun hH hg hx' hγ)
    have mid : ∃ x'', M.mem (M.op x' x'') s ∧ x' ≠ x'' ∧ M.mem (M.op x'' xs) s ∧ x'' ≠ xs := by
      rcases cls x' (hsWO.fld x' xs hx'xs).1 with ⟨a, r, ha⟩ | ⟨n', k', hpt'⟩
      · obtain ⟨u1, u2⟩ := u_lt r ha hx00
        refine ⟨x00, u1, u2, pt_le hx00 hxs (Or.inl ⟨zero_le, zero_ne n⟩), fun e1 => ?_⟩
        rw [e1] at hx00
        exact zero_ne n (pt_inj hx00 hxs).1
      · rcases pt_ge hpt' hxs hx'xs with ⟨c1, c2⟩ | ⟨c1, c2⟩
        · obtain ⟨x'', hx''⟩ := pt_ex n' (k' + 1)
          refine ⟨x'', pt_le hpt' hx'' (Or.inr ⟨rfl, M.le_add_one k'⟩), fun e1 => ?_,
            pt_le hx'' hxs (Or.inl ⟨c1, c2⟩), fun e1 => ?_⟩
          · rw [← e1] at hx''
            exact ne_succ k' (pt_inj hpt' hx'').2
          · rw [e1] at hx''
            exact c2 (pt_inj hx'' hxs).1
        · exfalso
          rcases M.eq_or_succ_le c2 with e2 | e2
          · rw [c1, e2] at hpt'
            exact hx'ne (pt_fun hpt' hxs)
          · exact M.succ_not_le_zero e2
    obtain ⟨x'', m1, m2, m3, m4⟩ := mid
    obtain ⟨γ', hγ', k1, k2, -, -⟩ := gstep hx' m1 m2
    refine ⟨γ', k1, k2, (hg.2.1 x'' γ' xs γ hγ' hγ).mp m3, fun e1 => ?_⟩
    rw [e1] at hγ'
    exact m4 (M.piso_inj hsWO hg hγ' hγ)
  · obtain ⟨a0, b0, c0, ha0, hb0, hc0, -⟩ := hx00
    have hnot : ¬ M.Emb s w0 :=
      M.not_emb_sum hP hi huv hu hv hw0 hqWO hw0T hqT hs (ptq ha0 hb0 hc0)
    have hiff := M.segOf_le_iff hsWO hH hl he hsegl hseg0
    rcases M.wo_total hH he hl with h3 | h3
    · exact ⟨h3, fun e1 => hnot (hiff.mp (by rw [e1]; exact hl))⟩
    · exact (hnot (hiff.mp h3)).elim

/-- **In every ladder with a pairing and rungs `i`, `i + 1`, `i + 2` there is a good level of
the constructible hierarchy in which extensionality, foundation, pairing, union and infinity
hold.** As `exists_zf0_level`, with the stage `l` a limit of limit stages. -/
theorem exists_good_level {R E z S P : V} {m i : M.Num} (h : M.IsLadder R E z S m)
    (hP : M.IsPairing R P m) (hi : i + 1 + 1 ≤ m) :
    ∃ th io Nt nle p F d tp qo Nu Pr l, M.HierData R P th io Nt nle p F d tp qo Nu Pr m (i + 1 + 1) ∧
      (∀ w, M.IsWO w →
        (∀ a b, M.mem (M.op a b) w → M.mem (M.op i.1 a) R ∧ M.mem (M.op i.1 b) R) →
        M.Emb w th ∧ ¬ M.Emb th w) ∧
      M.IsGood th l ∧
      ∃ U E, (∀ k a, M.mem (M.op k a) U ↔
          M.mem k M.nat ∧ M.InNRaw P th io M.nat (i + 1 + 1).1 l a) ∧
        (∀ r a b, M.mem (M.trip r a b) E ↔ M.mem r M.nat ∧
          M.InNRaw P th io M.nat (i + 1 + 1).1 l a ∧ M.InNRaw P th io M.nat (i + 1 + 1).1 l b ∧
          M.AtomAtRaw P th io M.nat Nt (i + 1 + 1).1 d tp qo Nu Pr M.adG
          (1 : M.Num).1 (2 : M.Num).1 F l r a b) ∧
        ∃ s, M.IsAsg U s ∧
          M.Holds U E (M.cExt (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3)) s ∧
          M.Holds U E (M.cFound (M.vr 0 0) (M.vr 0 1) (M.vr 0 2)) s ∧
          M.Holds U E (M.cPairAx (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3) (M.vr 1 0)) s ∧
          M.Holds U E (M.cUnionAx (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3)) s ∧
          M.Holds U E
            (M.cInf (M.vr 0 0) (M.vr 0 1) (M.vr 0 2) (M.vr 0 3) (M.vr 1 0) (M.vr 1 1)) s := by
  have hi0 : i ≤ m := le_trans (le_trans (M.le_add_one i) (M.le_add_one (i + 1))) hi
  obtain ⟨H, hH, h1, h2, h3⟩ := M.hartogs h hP hi
  obtain ⟨l1, β, hl1, hβ, hβne⟩ := M.exists_limit_stage h hP hi0 hH h2
  obtain ⟨l, hl, hl1l, hl1ne⟩ := M.good_above h hP hi0 hH h2 h3 hl1.1
  obtain ⟨io, Nt, nle, p, F, d, tp, qo, Nu, Pr, hd, -⟩ := M.exists_hierData h hP hi hH
    (fun a b hab => ⟨h1 a (hH.fld a b hab).1, h1 b (hH.fld a b hab).2⟩) ⟨l, hl.1.1⟩ (M.cOrd 0 1 2 3) H
  exact ⟨H, io, Nt, nle, p, F, d, tp, qo, Nu, Pr, l, hd, h2, hl,
    M.limit_level_zf0 hd hl.1 hl1 hβ hβne hl1l hl1ne⟩

end Model

end NFUCut
