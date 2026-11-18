import FnTheory

set_option autoImplicit false

/-!
# Inside a model of FunctionNF: truth values, sets and stratified comprehension

Fix a model `M` of `𝗙𝗡𝗙`.

* **Evaluation.** A stratified λ-term has exactly one value (`den_unique`, `fn_abs`); `ev t env`
  is that value, and it satisfies the expected equations (`ev_app`, `ev_lam`, `ev_eqt`).
* **Truth values.** `bool p` is `⊤` if `p` holds and `⊥` otherwise. A *parametric term* is a
  λ-term given as a function of the positions of its variables, so that it can be placed under
  further binders without renaming. `Ok Γ L P R` says that `P` is stratified at level `L` when
  its variables have the levels `Γ`, and that its value is `bool (R v)`.
  * `pNot`, `pIff`: equality tests.
  * `pRaise`: `λw.p ≐ λw.⊤`, one level up.
  * `pLower`: `p d ≐ ⊤ d`, one level down, where `⊤ d ≠ ⊥ d`.
  * `pAnd`: the pair `λz.λu.λv. z (λw.a) b`, compared with the pair of `⊤` and `⊤`, three
    levels up, then lowered three times.
  * `pAll`: `λx.p ≐ λx.⊤`.
* **`BT Γ R`**: a relation `R` together with such a term for every level. The combinators
  `BT.mem`, `BT.eq`, `BT.app`, `BT.not`, `BT.and`, `BT.or`, `BT.imp`, `BT.iff`, `BT.all`, `BT.ex`,
  `BT.comp` build them, so no λ-term is written by hand after this file.
* **Sets.** A set is an object all of whose values are `⊤` or `⊥` (`IsSet`), and `x ∈ s` means
  that `s` is a set and `s · x = ⊤` (`Mem`). `BT.set`: every relation with a `BT` defines a
  set. `isNFU`: the structure `(M, Mem)` satisfies NFU.
-/

namespace FFL.FirstOrder.FNF

open JensenNFU (TFm)
open JensenNFU.TFm (scons scons_zero scons_succ)

variable {M : Type} [s : Tarski.Structure ℒλ M] [Tarski.Structure.Eq ℒλ M] [Nonempty M]
  [hM : M↓[ℒλ] ⊧* 𝗙𝗡𝗙]

local infixl:70 " ⬝ " => App

/-! ### Evaluation -/

theorem den_unique (t : LTm) :
    ∀ (env : ℕ → M) (v v' : M), Den t env v → Den t env v' → v = v' := by
  induction t with
  | var i => intro env v v' h h'; exact h.trans h'.symm
  | app s t ihs iht =>
    rintro env v v' ⟨a, b, ha, hb, rfl⟩ ⟨a', b', ha', hb', rfl⟩
    rw [ihs env a a' ha ha', iht env b b' hb hb']
  | lam t ih =>
    intro env v v' h h'
    refine fn_ext hM fun x => ?_
    obtain ⟨w, hw, e⟩ := h x
    obtain ⟨w', hw', e'⟩ := h' x
    rw [e, e', ih _ w w' hw hw']
  | eqt s t ihs iht =>
    rintro env v v' ⟨a, b, ha, hb, rfl⟩ ⟨a', b', ha', hb', rfl⟩
    rw [ihs env a a' ha ha', iht env b b' hb hb']
  | tt => intro env v v' h h'; exact h.trans h'.symm
  | ff => intro env v v' h h'; exact h.trans h'.symm

/-- The value of a λ-term (meaningful when the term is stratified). -/
noncomputable def ev (t : LTm) (env : ℕ → M) : M := Classical.epsilon (Den t env)

theorem den_ev {γ : ℕ → ℕ} {t : LTm} {ℓ : ℕ} (h : HasLev γ t ℓ) (env : ℕ → M) :
    Den t env (ev t env) := Classical.epsilon_spec (fn_abs hM h env)

theorem ev_eq {γ : ℕ → ℕ} {t : LTm} {ℓ : ℕ} (h : HasLev γ t ℓ) {env : ℕ → M} {v : M}
    (hv : Den t env v) : ev t env = v := den_unique t env _ _ (den_ev h env) hv

theorem ev_var (i : ℕ) (env : ℕ → M) : ev (.var i) env = env i :=
  ev_eq (γ := fun _ => 0) (ℓ := 0) (t := .var i) rfl rfl

theorem ev_tt (env : ℕ → M) : ev .tt env = TT :=
  ev_eq (γ := fun _ => 0) (ℓ := 0) (t := .tt) trivial rfl

theorem ev_ff (env : ℕ → M) : ev .ff env = FF :=
  ev_eq (γ := fun _ => 0) (ℓ := 0) (t := .ff) trivial rfl

theorem ev_app {γ : ℕ → ℕ} {s' t : LTm} {ℓ : ℕ} (h : HasLev γ (.app s' t) ℓ) (env : ℕ → M) :
    ev (.app s' t) env = ev s' env ⬝ ev t env :=
  ev_eq h ⟨_, _, den_ev h.1 env, den_ev h.2 env, rfl⟩

theorem ev_eqt {γ : ℕ → ℕ} {s' t : LTm} {ℓ : ℕ} (h : HasLev γ (.eqt s' t) ℓ) (env : ℕ → M) :
    ev (.eqt s' t) env = EqT (ev s' env) (ev t env) :=
  ev_eq h ⟨_, _, den_ev h.1 env, den_ev h.2 env, rfl⟩

theorem ev_lam {γ : ℕ → ℕ} {t : LTm} {ℓ : ℕ} (h : HasLev γ (.lam t) ℓ) (env : ℕ → M) (x : M) :
    ev (.lam t) env ⬝ x = ev t (scons x env) := by
  obtain ⟨w, hw, e⟩ := den_ev h env x
  obtain ⟨k, -, hk⟩ := h
  rw [e]
  exact (ev_eq hk hw).symm

/-! ### Truth values -/

open Classical in
/-- `⊤` if `p` holds, `⊥` otherwise. -/
noncomputable def bool (p : Prop) : M := if p then TT else FF

omit [Tarski.Structure.Eq ℒλ M] [Nonempty M] hM in
theorem bool_true {p : Prop} (h : p) : (bool p : M) = TT := if_pos h

omit [Tarski.Structure.Eq ℒλ M] [Nonempty M] hM in
theorem bool_false {p : Prop} (h : ¬p) : (bool p : M) = FF := if_neg h

theorem bool_eq_tt {p : Prop} : (bool p : M) = TT ↔ p :=
  ⟨fun h => by_contra fun hp => tt_ne_ff hM (h.symm.trans (bool_false hp)), bool_true⟩

omit [Tarski.Structure.Eq ℒλ M] [Nonempty M] hM in
theorem bool_congr {p q : Prop} (h : p ↔ q) : (bool p : M) = bool q := by
  rw [show p = q from propext h]

theorem bool_inj {p q : Prop} : (bool p : M) = bool q ↔ (p ↔ q) := by
  refine ⟨fun h => ⟨fun hp => ?_, fun hq => ?_⟩, bool_congr⟩
  · exact bool_eq_tt.mp (h ▸ bool_true hp)
  · exact bool_eq_tt.mp (h.symm ▸ bool_true hq)

theorem eqT_eq_bool (a b : M) : EqT a b = bool (a = b) := by
  by_cases h : a = b
  · rw [bool_true h, h]; exact eqT_self hM b
  · rw [bool_false h]; exact eqT_ne hM h

omit [Tarski.Structure.Eq ℒλ M] [Nonempty M] hM in
theorem bool_or (p : Prop) : (bool p : M) = TT ∨ (bool p : M) = FF := by
  by_cases h : p
  · exact Or.inl (bool_true h)
  · exact Or.inr (bool_false h)

/-- `⊤` and `⊥` take different values at `D`. -/
def Sep (D : M) : Prop := (TT : M) ⬝ D ≠ FF ⬝ D

theorem exists_sep : ∃ D : M, Sep D := by
  by_contra h
  exact tt_ne_ff hM (fn_ext hM fun x => by_contra fun hx => h ⟨x, hx⟩)

/-! ### Parametric terms -/

/-- A λ-term as a function of the positions `ρ` of its variables and the positions `d` of the
objects used for lowering (`d ℓ` is the one of level `ℓ`). -/
abbrev PT := (ℕ → ℕ) → (ℕ → ℕ) → LTm

/-- The levels `γ` agree with `Γ` on the variables and with the convention for `d`, up to a
shift by `c`. -/
def Adm (Γ : List ℕ) (γ ρ d : ℕ → ℕ) (c : ℕ) : Prop :=
  (∀ i (h : i < Γ.length), γ (ρ i) = Γ[i] + c) ∧ ∀ ℓ, γ (d ℓ) = ℓ + c

theorem Adm.up {Γ : List ℕ} {γ ρ d : ℕ → ℕ} {c : ℕ} (h : Adm Γ γ ρ d c) (k : ℕ) :
    Adm Γ (scons k γ) (fun i => ρ i + 1) (fun ℓ => d ℓ + 1) c := ⟨fun i hi => h.1 i hi, fun ℓ => h.2 ℓ⟩

/-- `P` is stratified at level `L` and its value is the truth value of `R`. -/
structure Ok (Γ : List ℕ) (L : ℕ) (P : PT) (R : (ℕ → M) → Prop) : Prop where
  lev : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c → HasLev γ (P ρ d) (L + c)
  sem : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ) (env v : ℕ → M), Adm Γ γ ρ d c →
    (∀ i, i < Γ.length → env (ρ i) = v i) → (∀ ℓ, Sep (env (d ℓ))) →
      ev (P ρ d) env = bool (R v)

variable {Γ : List ℕ} {L : ℕ} {P Q : PT} {R S : (ℕ → M) → Prop}

omit [Tarski.Structure.Eq ℒλ M] hM in
theorem Ok.congr (h : Ok Γ L P R) (e : ∀ v, R v ↔ S v) : Ok Γ L P S :=
  ⟨h.lev, fun γ ρ d c env v ha he hd => (h.sem γ ρ d c env v ha he hd).trans (bool_congr (e v))⟩

/-- Negation: `p ≐ ⊥`. -/
def pNot (P : PT) : PT := fun ρ d => .eqt (P ρ d) .ff

theorem Ok.not (h : Ok Γ L P R) : Ok Γ L (pNot P) (fun v => ¬R v) := by
  have hlev : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c → HasLev γ (pNot P ρ d) (L + c) :=
    fun γ ρ d c ha => ⟨h.lev γ ρ d c ha, trivial⟩
  refine ⟨hlev, fun γ ρ d c env v ha he hd => ?_⟩
  show ev (.eqt (P ρ d) .ff) env = _
  rw [ev_eqt (hlev γ ρ d c ha), h.sem γ ρ d c env v ha he hd, ev_ff, eqT_eq_bool]
  refine bool_congr ⟨fun e hR => tt_ne_ff hM ((bool_true hR).symm.trans e), fun hR => bool_false hR⟩

/-- Equivalence: `p ≐ q`. -/
def pIff (P Q : PT) : PT := fun ρ d => .eqt (P ρ d) (Q ρ d)

theorem Ok.iff (h : Ok Γ L P R) (h' : Ok Γ L Q S) : Ok Γ L (pIff P Q) (fun v => (R v ↔ S v)) := by
  have hlev : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c → HasLev γ (pIff P Q ρ d) (L + c) :=
    fun γ ρ d c ha => ⟨h.lev γ ρ d c ha, h'.lev γ ρ d c ha⟩
  refine ⟨hlev, fun γ ρ d c env v ha he hd => ?_⟩
  show ev (.eqt (P ρ d) (Q ρ d)) env = _
  rw [ev_eqt (hlev γ ρ d c ha), h.sem γ ρ d c env v ha he hd, h'.sem γ ρ d c env v ha he hd,
    eqT_eq_bool]
  exact bool_congr bool_inj

/-- One level up: `λw.p ≐ λw.⊤`. -/
def pRaise (P : PT) : PT :=
  fun ρ d => .eqt (.lam (P (fun i => ρ i + 1) (fun ℓ => d ℓ + 1))) (.lam .tt)

theorem Ok.raise (h : Ok Γ L P R) : Ok Γ (L + 1) (pRaise P) R := by
  have hlev : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c → HasLev γ (pRaise P ρ d) (L + 1 + c) :=
    fun γ ρ d c ha => ⟨⟨L + c, by omega, h.lev _ _ _ c (ha.up _)⟩, ⟨L + c, by omega, trivial⟩⟩
  refine ⟨hlev, fun γ ρ d c env v ha he hd => ?_⟩
  have hl := hlev γ ρ d c ha
  have hx : ∀ x : M, ev (.lam (P (fun i => ρ i + 1) (fun ℓ => d ℓ + 1))) env ⬝ x = bool (R v) :=
    fun x => by
      rw [ev_lam hl.1]
      exact h.sem _ _ _ c (scons x env) v (ha.up (L + c)) he hd
  have hy : ∀ x : M, ev (.lam .tt) env ⬝ x = TT := fun x => by rw [ev_lam hl.2, ev_tt]
  show ev (.eqt (.lam _) (.lam .tt)) env = _
  rw [ev_eqt hl, eqT_eq_bool]
  refine bool_congr ⟨fun e => ?_, fun hR => fn_ext hM fun x => ?_⟩
  · obtain ⟨x⟩ := ‹Nonempty M›
    have := hx x
    rw [e, hy x] at this
    exact bool_eq_tt.mp this.symm
  · rw [hx x, hy x, bool_true hR]

/-- One level down: `p d ≐ ⊤ d`. -/
def pLower (ℓ : ℕ) (P : PT) : PT :=
  fun ρ d => .eqt (.app (P ρ d) (.var (d ℓ))) (.app .tt (.var (d ℓ)))

theorem Ok.lower {ℓ : ℕ} (h : Ok Γ (ℓ + 1) P R) : Ok Γ ℓ (pLower ℓ P) R := by
  have hlev : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c → HasLev γ (pLower ℓ P ρ d) (ℓ + c) :=
    fun γ ρ d c ha => by
      have := h.lev γ ρ d c ha
      rw [show ℓ + 1 + c = ℓ + c + 1 by omega] at this
      exact ⟨⟨this, ha.2 ℓ⟩, ⟨trivial, ha.2 ℓ⟩⟩
  refine ⟨hlev, fun γ ρ d c env v ha he hd => ?_⟩
  have hl := hlev γ ρ d c ha
  show ev (.eqt (.app (P ρ d) (.var (d ℓ))) (.app .tt (.var (d ℓ)))) env = _
  rw [ev_eqt hl, ev_app hl.1, ev_app hl.2, ev_var, ev_tt, h.sem γ ρ d c env v ha he hd,
    eqT_eq_bool]
  refine bool_congr ⟨fun e => by_contra fun hR => ?_, fun hR => by rw [bool_true hR]⟩
  rw [bool_false hR] at e
  exact hd ℓ e.symm

/-- The pair `λz.λu.λv. z (λw.a) b` of two truth values. -/
def pPair (P Q : PT) : PT := fun ρ d =>
  .lam (.lam (.lam (.app (.app (.var 2) (.lam (P (fun i => ρ i + 4) (fun ℓ => d ℓ + 4))))
    (Q (fun i => ρ i + 3) (fun ℓ => d ℓ + 3)))))

/-- The pair of `⊤` and `⊤`. -/
def pairTT : LTm := .lam (.lam (.lam (.app (.app (.var 2) (.lam .tt)) .tt)))

/-- The identity `λk.k`. -/
def idT : LTm := .lam (.var 0)

/-- `λk.λm.m`. -/
def kiT : LTm := .lam (.lam (.var 0))

theorem ev_idT (env : ℕ → M) (x : M) : ev idT env ⬝ x = x := by
  have h : HasLev (fun _ => 0) idT 1 := ⟨0, rfl, rfl⟩
  rw [idT, ev_lam h, ev_var]; rfl

theorem ev_kiT (env : ℕ → M) (a b : M) : ev kiT env ⬝ a ⬝ b = b := by
  have h : HasLev (fun _ => 0) kiT 2 := ⟨1, rfl, 0, rfl, rfl⟩
  obtain ⟨k, -, hk⟩ := id h
  rw [kiT, ev_lam h, ev_lam hk, ev_var]; rfl

theorem Ok.pairEq (h : Ok Γ L P R) (h' : Ok Γ L Q S) :
    Ok Γ (L + 3) (fun ρ d => .eqt (pPair P Q ρ d) pairTT) (fun v => R v ∧ S v) := by
  -- the levels of the pieces
  have hadm3 : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c →
      Adm Γ (scons (L + c) (scons (L + c + 1) (scons (L + c + 2) γ)))
        (fun i => ρ i + 3) (fun ℓ => d ℓ + 3) c :=
    fun γ ρ d c ha => ⟨fun i hi => ha.1 i hi, fun ℓ => ha.2 ℓ⟩
  have hadm4 : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c →
      Adm Γ (scons (L + c) (scons (L + c) (scons (L + c + 1) (scons (L + c + 2) γ))))
        (fun i => ρ i + 4) (fun ℓ => d ℓ + 4) c :=
    fun γ ρ d c ha => ⟨fun i hi => ha.1 i hi, fun ℓ => ha.2 ℓ⟩
  have hbody : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c →
      HasLev (scons (L + c) (scons (L + c + 1) (scons (L + c + 2) γ)))
        (.app (.app (.var 2) (.lam (P (fun i => ρ i + 4) (fun ℓ => d ℓ + 4))))
          (Q (fun i => ρ i + 3) (fun ℓ => d ℓ + 3))) (L + c) :=
    fun γ ρ d c ha => ⟨⟨rfl, ⟨L + c, rfl, h.lev _ _ _ c (hadm4 γ ρ d c ha)⟩⟩,
      h'.lev _ _ _ c (hadm3 γ ρ d c ha)⟩
  have hpair : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c → HasLev γ (pPair P Q ρ d) (L + 3 + c) :=
    fun γ ρ d c ha => ⟨L + c + 2, by omega, L + c + 1, rfl, L + c, rfl, hbody γ ρ d c ha⟩
  have hbodyT : ∀ (γ : ℕ → ℕ) (c : ℕ),
      HasLev (scons (L + c) (scons (L + c + 1) (scons (L + c + 2) γ)))
        (.app (.app (.var 2) (.lam .tt)) .tt) (L + c) :=
    fun γ c => ⟨⟨rfl, ⟨L + c, rfl, trivial⟩⟩, trivial⟩
  have hTT : ∀ (γ : ℕ → ℕ) (c : ℕ), HasLev γ pairTT (L + 3 + c) :=
    fun γ c => ⟨L + c + 2, by omega, L + c + 1, rfl, L + c, rfl, hbodyT γ c⟩
  refine ⟨fun γ ρ d c ha => ⟨hpair γ ρ d c ha, hTT γ c⟩, fun γ ρ d c env v ha he hd => ?_⟩
  -- the values of the two pairs at `z`, `u`, `w`
  have e1 : ∀ z u w : M, ev (pPair P Q ρ d) env ⬝ z ⬝ u ⬝ w =
      z ⬝ ev (.lam (P (fun i => ρ i + 4) (fun ℓ => d ℓ + 4))) (scons w (scons u (scons z env))) ⬝
        bool (S v) := fun z u w => by
    have hp := hpair γ ρ d c ha
    obtain ⟨k2, -, hk2⟩ := id hp
    obtain ⟨k1, -, hk1⟩ := id hk2
    have hb := hbody γ ρ d c ha
    have e : ev (pPair P Q ρ d) env ⬝ z ⬝ u ⬝ w =
        ev (.app (.app (.var 2) (.lam (P (fun i => ρ i + 4) (fun ℓ => d ℓ + 4))))
          (Q (fun i => ρ i + 3) (fun ℓ => d ℓ + 3))) (scons w (scons u (scons z env))) := by
      show ev (.lam (.lam (.lam _))) env ⬝ z ⬝ u ⬝ w = _
      rw [ev_lam hp, ev_lam hk2, ev_lam hk1]
    rw [e, ev_app hb, ev_app hb.1, ev_var,
      h'.sem _ (fun i => ρ i + 3) (fun ℓ => d ℓ + 3) c (scons w (scons u (scons z env))) v
        (hadm3 γ ρ d c ha) (fun i hi => he i hi) (fun ℓ => hd ℓ)]
    rfl
  have e2 : ∀ (z u w x : M),
      ev (.lam (P (fun i => ρ i + 4) (fun ℓ => d ℓ + 4))) (scons w (scons u (scons z env))) ⬝ x =
        bool (R v) := fun z u w x => by
    have hb := hbody γ ρ d c ha
    rw [ev_lam hb.1.2]
    exact h.sem _ (fun i => ρ i + 4) (fun ℓ => d ℓ + 4) c
      (scons x (scons w (scons u (scons z env)))) v (hadm4 γ ρ d c ha) (fun i hi => he i hi)
      (fun ℓ => hd ℓ)
  have e3 : ∀ z u w : M, ev pairTT env ⬝ z ⬝ u ⬝ w =
      z ⬝ ev (.lam .tt) (scons w (scons u (scons z env))) ⬝ TT := fun z u w => by
    have hp := hTT γ c
    obtain ⟨k2, -, hk2⟩ := id hp
    obtain ⟨k1, -, hk1⟩ := id hk2
    have hb := hbodyT γ c
    have e : ev pairTT env ⬝ z ⬝ u ⬝ w =
        ev (.app (.app (.var 2) (.lam .tt)) .tt) (scons w (scons u (scons z env))) := by
      show ev (.lam (.lam (.lam _))) env ⬝ z ⬝ u ⬝ w = _
      rw [ev_lam hp, ev_lam hk2, ev_lam hk1]
    rw [e, ev_app hb, ev_app hb.1, ev_var, ev_tt]
    rfl
  have e4 : ∀ (z u w x : M), ev (.lam .tt) (scons w (scons u (scons z env))) ⬝ x = TT :=
    fun z u w x => by
      have hb := hbodyT γ c
      rw [ev_lam hb.1.2, ev_tt]
  show ev (.eqt (pPair P Q ρ d) pairTT) env = _
  rw [ev_eqt ⟨hpair γ ρ d c ha, hTT γ c⟩, eqT_eq_bool]
  refine bool_congr ⟨fun e => ?_, fun hRS => ?_⟩
  · obtain ⟨x⟩ := ‹Nonempty M›
    constructor
    · have := e1 (ev idT env) x x
      rw [e, e3, ev_idT, ev_idT, e2, e4] at this
      exact bool_eq_tt.mp this.symm
    · have := e1 (ev kiT env) x x
      rw [e, e3, ev_kiT, ev_kiT] at this
      exact bool_eq_tt.mp this.symm
  · refine fn_ext hM fun z => fn_ext hM fun u => fn_ext hM fun w => ?_
    rw [e1, e3, bool_true hRS.2]
    congr 2
    exact fn_ext hM fun x => by rw [e2, e4, bool_true hRS.1]

/-- Conjunction: compare the pair with the pair of `⊤` and `⊤`, and lower three times. -/
def pAnd (L : ℕ) (P Q : PT) : PT :=
  pLower L (pLower (L + 1) (pLower (L + 2) (fun ρ d => .eqt (pPair P Q ρ d) pairTT)))

theorem Ok.and (h : Ok Γ L P R) (h' : Ok Γ L Q S) : Ok Γ L (pAnd L P Q) (fun v => R v ∧ S v) :=
  ((h.pairEq h').lower.lower).lower

/-- The universal quantifier: `λx.p ≐ λx.⊤`. -/
def pAll (P : PT) : PT :=
  fun ρ d => .eqt (.lam (P (scons 0 (fun i => ρ i + 1)) (fun ℓ => d ℓ + 1))) (.lam .tt)

theorem Ok.all {t : ℕ} (h : Ok (t :: Γ) t P R) :
    Ok Γ (t + 1) (pAll P) (fun v => ∀ a, R (scons a v)) := by
  have hadm : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c →
      Adm (t :: Γ) (scons (t + c) γ) (scons 0 (fun i => ρ i + 1)) (fun ℓ => d ℓ + 1) c :=
    fun γ ρ d c ha => ⟨fun i hi => by
      cases i with
      | zero => rfl
      | succ i => exact ha.1 i (by simpa using hi), fun ℓ => ha.2 ℓ⟩
  have hlev : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c → HasLev γ (pAll P ρ d) (t + 1 + c) :=
    fun γ ρ d c ha => ⟨⟨t + c, by omega, h.lev _ _ _ c (hadm γ ρ d c ha)⟩, ⟨t + c, by omega, trivial⟩⟩
  refine ⟨hlev, fun γ ρ d c env v ha he hd => ?_⟩
  have hl := hlev γ ρ d c ha
  have hx : ∀ x : M, ev (.lam (P (scons 0 (fun i => ρ i + 1)) (fun ℓ => d ℓ + 1))) env ⬝ x =
      bool (R (scons x v)) := fun x => by
    rw [ev_lam hl.1]
    refine h.sem _ _ _ c (scons x env) (scons x v) (hadm γ ρ d c ha) (fun i hi => ?_) hd
    cases i with
    | zero => rfl
    | succ i => exact he i (by simpa using hi)
  have hy : ∀ x : M, ev (.lam .tt) env ⬝ x = TT := fun x => by rw [ev_lam hl.2, ev_tt]
  show ev (.eqt (.lam _) (.lam .tt)) env = _
  rw [ev_eqt hl, eqT_eq_bool]
  refine bool_congr ⟨fun e a => ?_, fun hR => fn_ext hM fun x => ?_⟩
  · have := hx a
    rw [e, hy a] at this
    exact bool_eq_tt.mp this.symm
  · rw [hx x, hy x, bool_true (hR x)]

/-- `k` levels up. -/
def pRaiseN : ℕ → PT → PT
  | 0, P => P
  | k + 1, P => pRaise (pRaiseN k P)

theorem Ok.raiseN (h : Ok Γ L P R) : ∀ k, Ok Γ (L + k) (pRaiseN k P) R
  | 0 => h
  | k + 1 => (Ok.raiseN h k).raise

/-- `k` levels down, to the level `L`. -/
def pLowerN (L : ℕ) : ℕ → PT → PT
  | 0, P => P
  | k + 1, P => pLower L (pLowerN (L + 1) k P)

theorem Ok.lowerN : ∀ (k L : ℕ) (P : PT), Ok Γ (L + k) P R → Ok Γ L (pLowerN L k P) R
  | 0, _, _, h => h
  | k + 1, L, P, h =>
    Ok.lower (Ok.lowerN k (L + 1) P (by rwa [show L + 1 + k = L + (k + 1) by omega]))

/-- From the level `a` to the level `L`. -/
def pMove (a L : ℕ) (P : PT) : PT :=
  if a ≤ L then pRaiseN (L - a) P else pLowerN L (a - L) P

theorem Ok.move {a : ℕ} (h : Ok Γ a P R) (L : ℕ) : Ok Γ L (pMove a L P) R := by
  unfold pMove
  split
  · have := h.raiseN (L - a)
    rwa [show a + (L - a) = L by omega] at this
  · exact Ok.lowerN (a - L) L P (by rwa [show L + (a - L) = a by omega])

/-! ### Relations with a truth-value term at every level -/

/-- A relation `R` on environments, with a stratified λ-term for its truth value at every
level. `Γ` lists the levels of the variables. -/
structure BT (Γ : List ℕ) (R : (ℕ → M) → Prop) where
  tm : ℕ → PT
  ok : ∀ L, Ok Γ L (tm L) R

namespace BT

/-- From a term at one level. -/
def ofOk (a : ℕ) (P : PT) (h : Ok Γ a P R) : BT Γ R := ⟨fun L => pMove a L P, fun L => h.move L⟩

/-- The same terms define every equivalent relation. -/
def congr (p : BT Γ R) (e : ∀ v, R v ↔ S v) : BT Γ S := ⟨p.tm, fun L => (p.ok L).congr e⟩

protected def not (p : BT Γ R) : BT Γ (fun v => ¬R v) :=
  ⟨fun L => pNot (p.tm L), fun L => (p.ok L).not⟩

protected def and (p : BT Γ R) (q : BT Γ S) : BT Γ (fun v => R v ∧ S v) :=
  ⟨fun L => pAnd L (p.tm L) (q.tm L), fun L => (p.ok L).and (q.ok L)⟩

protected def iff (p : BT Γ R) (q : BT Γ S) : BT Γ (fun v => (R v ↔ S v)) :=
  ⟨fun L => pIff (p.tm L) (q.tm L), fun L => (p.ok L).iff (q.ok L)⟩

protected def or (p : BT Γ R) (q : BT Γ S) : BT Γ (fun v => R v ∨ S v) :=
  ((p.not.and q.not).not).congr fun _ => by tauto

protected def imp (p : BT Γ R) (q : BT Γ S) : BT Γ (fun v => R v → S v) :=
  ((p.and q.not).not).congr fun _ => by tauto

/-- Universal quantification over a new first variable of level `t`. -/
protected def all (t : ℕ) {R : (ℕ → M) → Prop} (p : BT (t :: Γ) R) :
    BT Γ (fun v => ∀ a, R (scons a v)) := ofOk (t + 1) (pAll (p.tm t)) (p.ok t).all

/-- Existential quantification over a new first variable of level `t`. -/
protected def ex (t : ℕ) {R : (ℕ → M) → Prop} (p : BT (t :: Γ) R) :
    BT Γ (fun v => ∃ a, R (scons a v)) :=
  ((p.not.all t).not).congr fun _ => by push_neg; rfl

/-- `vᵢ = vⱼ`. -/
def eq (i j a : ℕ) (hi : Γ[i]? = some a) (hj : Γ[j]? = some a) : BT Γ (fun v : ℕ → M => v i = v j) :=
  ofOk a (fun ρ _ => .eqt (.var (ρ i)) (.var (ρ j))) (by
    obtain ⟨hi', ei⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj', ej⟩ := List.getElem?_eq_some_iff.mp hj
    have hlev : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c →
        HasLev γ (.eqt (.var (ρ i)) (.var (ρ j))) (a + c) :=
      fun γ ρ d c ha => ⟨by rw [← ei]; exact ha.1 i hi', by rw [← ej]; exact ha.1 j hj'⟩
    refine ⟨hlev, fun γ ρ d c env v ha he hd => ?_⟩
    rw [ev_eqt (hlev γ ρ d c ha), ev_var, ev_var, eqT_eq_bool, he i hi', he j hj'])

/-- `vᵢ · vⱼ = vₖ`. -/
def app (i j k a : ℕ) (hi : Γ[i]? = some (a + 1)) (hj : Γ[j]? = some a) (hk : Γ[k]? = some a) :
    BT Γ (fun v : ℕ → M => v i ⬝ v j = v k) :=
  ofOk a (fun ρ _ => .eqt (.app (.var (ρ i)) (.var (ρ j))) (.var (ρ k))) (by
    obtain ⟨hi', ei⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj', ej⟩ := List.getElem?_eq_some_iff.mp hj
    obtain ⟨hk', ek⟩ := List.getElem?_eq_some_iff.mp hk
    have hlev : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c →
        HasLev γ (.eqt (.app (.var (ρ i)) (.var (ρ j))) (.var (ρ k))) (a + c) :=
      fun γ ρ d c ha => ⟨⟨by show γ (ρ i) = _; rw [ha.1 i hi', ei]; omega, by rw [← ej]; exact ha.1 j hj'⟩,
        by rw [← ek]; exact ha.1 k hk'⟩
    refine ⟨hlev, fun γ ρ d c env v ha he hd => ?_⟩
    have hl := hlev γ ρ d c ha
    rw [ev_eqt hl, ev_app hl.1, ev_var, ev_var, ev_var, eqT_eq_bool, he i hi', he j hj', he k hk'])

/-- `vᵢ · vⱼ = ⊤`. -/
def appTT (i j a : ℕ) (hi : Γ[i]? = some (a + 1)) (hj : Γ[j]? = some a) :
    BT Γ (fun v : ℕ → M => v i ⬝ v j = TT) :=
  ofOk a (fun ρ _ => .eqt (.app (.var (ρ i)) (.var (ρ j))) .tt) (by
    obtain ⟨hi', ei⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj', ej⟩ := List.getElem?_eq_some_iff.mp hj
    have hlev : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c →
        HasLev γ (.eqt (.app (.var (ρ i)) (.var (ρ j))) .tt) (a + c) :=
      fun γ ρ d c ha => ⟨⟨by show γ (ρ i) = _; rw [ha.1 i hi', ei]; omega, by rw [← ej]; exact ha.1 j hj'⟩, trivial⟩
    refine ⟨hlev, fun γ ρ d c env v ha he hd => ?_⟩
    have hl := hlev γ ρ d c ha
    rw [ev_eqt hl, ev_app hl.1, ev_var, ev_var, ev_tt, eqT_eq_bool, he i hi', he j hj'])

/-- `vᵢ · vⱼ = ⊥`. -/
def appFF (i j a : ℕ) (hi : Γ[i]? = some (a + 1)) (hj : Γ[j]? = some a) :
    BT Γ (fun v : ℕ → M => v i ⬝ v j = FF) :=
  ofOk a (fun ρ _ => .eqt (.app (.var (ρ i)) (.var (ρ j))) .ff) (by
    obtain ⟨hi', ei⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj', ej⟩ := List.getElem?_eq_some_iff.mp hj
    have hlev : ∀ (γ ρ d : ℕ → ℕ) (c : ℕ), Adm Γ γ ρ d c →
        HasLev γ (.eqt (.app (.var (ρ i)) (.var (ρ j))) .ff) (a + c) :=
      fun γ ρ d c ha => ⟨⟨by show γ (ρ i) = _; rw [ha.1 i hi', ei]; omega, by rw [← ej]; exact ha.1 j hj'⟩, trivial⟩
    refine ⟨hlev, fun γ ρ d c env v ha he hd => ?_⟩
    have hl := hlev γ ρ d c ha
    rw [ev_eqt hl, ev_app hl.1, ev_var, ev_var, ev_ff, eqT_eq_bool, he i hi', he j hj'])

/-- Substitution of variables: `R (v ∘ f)`, when the levels match up to a shift by `c`. -/
def comp {Γ' : List ℕ} (p : BT Γ R) (f : ℕ → ℕ) (c : ℕ)
    (hf : ∀ i (h : i < Γ.length), Γ'[f i]? = some (Γ[i] + c)) :
    BT Γ' (fun v => R (fun i => v (f i))) :=
  ofOk (0 + c) (fun ρ d => p.tm 0 (fun i => ρ (f i)) (fun ℓ => d (ℓ + c))) (by
    have hadm : ∀ (γ ρ d : ℕ → ℕ) (c' : ℕ), Adm Γ' γ ρ d c' →
        Adm Γ γ (fun i => ρ (f i)) (fun ℓ => d (ℓ + c)) (c + c') :=
      fun γ ρ d c' ha => ⟨fun i hi => by
        obtain ⟨h', e⟩ := List.getElem?_eq_some_iff.mp (hf i hi)
        rw [ha.1 (f i) h', e]; omega, fun ℓ => by rw [ha.2 (ℓ + c)]; omega⟩
    refine ⟨fun γ ρ d c' ha => ?_, fun γ ρ d c' env v ha he hd => ?_⟩
    · have := (p.ok 0).lev γ _ _ (c + c') (hadm γ ρ d c' ha)
      rwa [show 0 + c + c' = 0 + (c + c') by omega]
    · exact (p.ok 0).sem γ _ _ (c + c') env (fun i => v (f i)) (hadm γ ρ d c' ha)
        (fun i hi => he (f i) (List.getElem?_eq_some_iff.mp (hf i hi)).1) (fun ℓ => hd (ℓ + c)))

end BT

/-! ### Sets -/

/-- A set: an object all of whose values are `⊤` or `⊥`. -/
def IsSet (x : M) : Prop := ∀ a, x ⬝ a = TT ∨ x ⬝ a = FF

/-- `x ∈ y`: `y` is a set and `y · x = ⊤`. -/
def Mem (x y : M) : Prop := IsSet y ∧ y ⬝ x = TT

namespace BT

/-- `vᵢ` is a set. -/
def isSet (i a : ℕ) (hi : Γ[i]? = some (a + 1)) : BT Γ (fun v : ℕ → M => IsSet (v i)) :=
  (BT.all a ((appTT (i + 1) 0 a (by rw [List.getElem?_cons_succ]; exact hi) rfl).or
    (appFF (i + 1) 0 a (by rw [List.getElem?_cons_succ]; exact hi) rfl))).congr fun _ => Iff.rfl

/-- `vᵢ ∈ vⱼ`. -/
def mem (i j a : ℕ) (hi : Γ[i]? = some a) (hj : Γ[j]? = some (a + 1)) :
    BT Γ (fun v : ℕ → M => Mem (v i) (v j)) :=
  ((isSet j a hj).and (appTT j i a hj hi)).congr fun _ => Iff.rfl

/-- **Comprehension.** A relation with a `BT` defines a set, for all values of the
parameters. -/
theorem set {t : ℕ} {R : (ℕ → M) → Prop} (p : BT (t :: Γ) R) (q : ℕ → M) :
    ∃ y : M, IsSet y ∧ ∀ x, Mem x y ↔ R (scons x q) := by
  obtain ⟨D, hD⟩ := exists_sep (M := M)
  have hadm : Adm (t :: Γ) (scons t (fun j => if h : j < Γ.length then Γ[j] else j - Γ.length))
      (fun i => i) (fun ℓ => Γ.length + ℓ + 1) 0 := by
    refine ⟨fun i hi => ?_, fun ℓ => ?_⟩
    · cases i with
      | zero => rfl
      | succ i =>
        have hi' : i < Γ.length := by simpa using hi
        show (if h : i < Γ.length then Γ[i] else i - Γ.length) = Γ[i] + 0
        rw [dif_pos hi']; rfl
    · show (if h : Γ.length + ℓ < Γ.length then Γ[Γ.length + ℓ] else Γ.length + ℓ - Γ.length) = ℓ + 0
      rw [dif_neg (by omega)]; omega
  have hl : HasLev (fun j => if h : j < Γ.length then Γ[j] else j - Γ.length)
      (.lam (p.tm t (fun i => i) (fun ℓ => Γ.length + ℓ + 1))) (t + 1) :=
    ⟨t, rfl, by simpa using (p.ok t).lev _ _ _ 0 hadm⟩
  have hy : ∀ x : M, ev (.lam (p.tm t (fun i => i) (fun ℓ => Γ.length + ℓ + 1)))
      (fun j => if j < Γ.length then q j else D) ⬝ x = bool (R (scons x q)) := fun x => by
    rw [ev_lam hl]
    refine (p.ok t).sem _ _ _ 0 _ (scons x q) hadm (fun i hi => ?_) (fun ℓ => ?_)
    · cases i with
      | zero => rfl
      | succ i =>
        have hi' : i < Γ.length := by simpa using hi
        show (if i < Γ.length then q i else D) = q i
        rw [if_pos hi']
    · show Sep (if Γ.length + ℓ < Γ.length then q (Γ.length + ℓ) else D)
      rw [if_neg (by omega)]; exact hD
  have hset : IsSet (ev (.lam (p.tm t (fun i => i) (fun ℓ => Γ.length + ℓ + 1)))
      (fun j => if j < Γ.length then q j else D)) := fun x => by rw [hy x]; exact bool_or _
  exact ⟨_, hset, fun x => ⟨fun h => bool_eq_tt.mp ((hy x).symm.trans h.2),
    fun h => ⟨hset, (hy x).trans (bool_true h)⟩⟩⟩

end BT

/-- Sets with the same members are equal. -/
theorem set_ext {x y : M} (hx : IsSet x) (hy : IsSet y) (h : ∀ z, Mem z x ↔ Mem z y) : x = y := by
  refine fn_ext hM fun a => ?_
  rcases hx a with h1 | h1
  · rw [h1, ((h a).mp ⟨hx, h1⟩).2]
  · rcases hy a with h2 | h2
    · exact absurd (((h a).mpr ⟨hy, h2⟩).2.symm.trans h1) (tt_ne_ff hM)
    · rw [h1, h2]

/-! ### NFU -/

/-- Satisfaction with a list as environment agrees with satisfaction with a function as
environment, for well typed formulas. -/
theorem sat_iff_satT {V : Type} (mem : V → V → Prop) (d : V) (φ : TFm) :
    ∀ (Γ : List ℕ) (env : List V), TFm.Strat Γ φ → env.length = Γ.length →
      (TFm.Sat mem φ env ↔ TFm.SatT (fun _ _ => True) mem φ (fun i => env.getD i d)) := by
  induction φ with
  | mem i j =>
    rintro Γ env ⟨t, hi, hj⟩ hlen
    have hi' : i < env.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
    have hj' : j < env.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hj).1
    simp only [TFm.Sat, TFm.satT_mem]
    rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj',
      List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj']
    exact JensenNFU.ex_some
  | eq i j =>
    rintro Γ env ⟨t, hi, hj⟩ hlen
    have hi' : i < env.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
    have hj' : j < env.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hj).1
    simp only [TFm.Sat, TFm.satT_eq]
    rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj',
      List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj']
    exact JensenNFU.ex_some
  | neg φ ih =>
    intro Γ env hs hlen
    simp only [TFm.Sat, TFm.satT_neg, ih Γ env hs hlen]
  | and φ ψ ih1 ih2 =>
    intro Γ env hs hlen
    simp only [TFm.Sat, TFm.satT_and, ih1 Γ env hs.1 hlen, ih2 Γ env hs.2 hlen]
  | all t φ ih =>
    intro Γ env hs hlen
    simp only [TFm.Sat, TFm.satT_all]
    refine forall_congr' fun a => ?_
    rw [ih (t :: Γ) (a :: env) hs (by simp [hlen])]
    have : (fun i => (a :: env).getD i d) = scons a (fun i => env.getD i d) := by
      funext i
      cases i <;> simp
    rw [this]
    simp

/-- The truth value of a well typed formula of set theory, with `Mem` as membership. -/
def ofTFm : (φ : TFm) → (Γ : List ℕ) → TFm.Strat Γ φ →
    BT Γ (fun v : ℕ → M => TFm.SatT (fun _ _ => True) Mem φ v)
  | .mem i j, Γ, hs => BT.mem i j (Γ.getD i 0)
      (by obtain ⟨t, h1, -⟩ := hs; simp [List.getD_eq_getElem?_getD, h1])
      (by obtain ⟨t, h1, h2⟩ := hs; simp [List.getD_eq_getElem?_getD, h1, h2])
  | .eq i j, Γ, hs => BT.eq i j (Γ.getD i 0)
      (by obtain ⟨t, h1, -⟩ := hs; simp [List.getD_eq_getElem?_getD, h1])
      (by obtain ⟨t, h1, h2⟩ := hs; simp [List.getD_eq_getElem?_getD, h1, h2])
  | .neg φ, Γ, hs => ((ofTFm φ Γ hs).not).congr fun _ => Iff.rfl
  | .and φ ψ, Γ, hs => ((ofTFm φ Γ hs.1).and (ofTFm ψ Γ hs.2)).congr fun _ => Iff.rfl
  | .all t φ, Γ, hs => ((ofTFm φ (t :: Γ) hs).all t).congr fun _ =>
      ⟨fun h a _ => h a, fun h a => h a trivial⟩

/-- **The structure `(M, Mem)` satisfies NFU**: extensionality for objects with members, and
stratified comprehension. -/
theorem isNFU : JensenNFU.IsNFU M (Mem (M := M)) where
  ext x y hne h := by
    obtain ⟨z, hz⟩ := hne
    exact set_ext hz.1 ((h z).mp hz).1 h
  comprehension t Γ φ hs params hp := by
    obtain ⟨d⟩ := ‹Nonempty M›
    obtain ⟨y, -, hy⟩ := (ofTFm (M := M) φ (t :: Γ) hs).set (fun i => params.getD i d)
    refine ⟨y, fun x => (hy x).trans ?_⟩
    rw [sat_iff_satT Mem d φ (t :: Γ) (x :: params) hs (by simp [hp])]
    have : (fun i => (x :: params).getD i d) = scons x (fun i => params.getD i d) := by
      funext i
      cases i <;> simp
    rw [this]

end FFL.FirstOrder.FNF
