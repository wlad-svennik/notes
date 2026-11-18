import MHOrder
import MacModel

set_option autoImplicit false

/-!
# Definable subsets of a constructible set are constructible

Inside a model `V` of `𝗠𝗛`.

A valuation of `n` variables in a set `t` is coded by a finite function on the numeral `n`
(`fnOf`). For every formula `φ` the set of the codes of the valuations in `t` that satisfy `φ`
in the structure `(t, ∈)` is obtained from `t` and numerals by finitely many of the eight
operations, each applied over a level (`sat_good`). So every subset of `t` that is definable
in `(t, ∈)` with parameters appears at a later level (`sep_good`).

The statements are relative to a property `X` of sets that is closed under the operations and
under the successor of levels (`Closed`), so that they can be used both for the class of all
constructible sets and inside a set closed under the operations.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

open Semiformula

section levels

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- The `k`-th successor. -/
noncomputable def scn : ℕ → V → V
  | 0, γ => γ
  | k + 1, γ => sc (scn k γ)

theorem scn_sub {γ : V} : ∀ k, ∀ z, z ∈ γ → z ∈ scn k γ
  | 0, _, h => h
  | k + 1, z, h => mem_sc.mpr (Or.inr (scn_sub k z h))

theorem ord_scn {γ : V} (hγ : Ord γ) : ∀ k, Ord (scn k γ)
  | 0 => hγ
  | k + 1 => ord_sc (ord_scn hγ k)

theorem lev_scn_sub {γ : V} (hγ : Ord γ) : ∀ k, ∀ x, x ∈ Lev γ → x ∈ Lev (scn k γ)
  | 0, _, h => h
  | k + 1, x, h =>
    lev_mono (ord_sc (ord_scn hγ k)) (self_mem_sc _) x (lev_scn_sub hγ k x h)

/-- An ordinal that includes `ω`. -/
def Big (γ : V) : Prop := Ord γ ∧ ∀ n, n ∈ (om : V) → n ∈ γ

theorem big_sc {γ : V} (h : Big γ) : Big (sc γ) :=
  ⟨ord_sc h.1, fun n hn => mem_sc.mpr (Or.inr (h.2 n hn))⟩

theorem big_scn {γ : V} (h : Big γ) : ∀ k, Big (scn k γ)
  | 0 => h
  | k + 1 => big_sc (big_scn h k)

theorem lev_empty : Lev (∅ : V) = ∅ := mem_ext fun x => by
  constructor
  · intro hx
    obtain ⟨β, hβ, -⟩ := (mem_lev ord_empty).mp hx
    exact absurd hβ (by simp)
  · intro hx
    exact absurd hx (by simp)

theorem empty_mem_lev {γ : V} (hγ : Ord γ) (hne : ∃ z, z ∈ γ) : (∅ : V) ∈ Lev γ := by
  have h0 : (∅ : V) ∈ γ := by
    rcases ord_tri ord_empty hγ with h | h | h
    · exact h
    · obtain ⟨z, hz⟩ := hne
      rw [← h] at hz
      exact absurd hz (by simp)
    · exact absurd h (by simp)
  have := lev_mem hγ h0
  rwa [lev_empty] at this

theorem ord_nm : ∀ k : ℕ, Ord (nm k : V)
  | 0 => ord_empty
  | k + 1 => ord_sc (ord_nm k)

theorem mem_nm : ∀ {n : ℕ} {x : V}, x ∈ (nm n : V) ↔ ∃ j, j < n ∧ x = nm j
  | 0, x => by simp [nm]
  | n + 1, x => by
    have : x ∈ (nm (n + 1) : V) ↔ x = nm n ∨ x ∈ (nm n : V) := mem_sc
    rw [this, mem_nm (n := n)]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨n, Nat.lt_succ_self n, rfl⟩
      · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
      · exact Or.inr ⟨j, h, rfl⟩
      · exact Or.inl rfl

theorem isNum_nm_iff {i j : ℕ} : IsNum i (nm j : V) ↔ j = i :=
  ⟨fun h => nm_inj ((isNum_iff i _).mp h), fun h => by subst h; exact isNum_nm _⟩

theorem phi_iff (lt z y₁ y₂ y₃ : V) (i : ℕ) : Phi lt z (nm i) y₁ y₂ y₃ ↔
    (i = 0 ∧ (z ∈ y₁ ∨ z = y₂)) ∨ (i = 1 ∧ (z ∈ y₁ ∧ ¬z ∈ y₂)) ∨ (i = 2 ∧ FunR z y₁ y₂) ∨
    (i = 3 ∧ (z ∈ y₁ ∧ MemAt z y₂ y₃)) ∨ (i = 4 ∧ (z ∈ y₁ ∧ EqAt z y₂ y₃)) ∨
    (i = 5 ∧ (z ∈ y₁ ∧ ∃ e, e ∈ y₂ ∧ AgreeOff z e y₃)) ∨
    (i = 6 ∧ ∃ e, e ∈ y₁ ∧ (Pr e y₃ z ∧ AgreeOff y₂ e y₃)) ∨ (i = 7 ∧ z ∈ lt) := by
  simp only [Phi, PhiE, isNum_nm_iff, or_assoc]

theorem phi0 {lt z y₁ y₂ y₃ : V} : Phi lt z (nm 0) y₁ y₂ y₃ ↔ (z ∈ y₁ ∨ z = y₂) :=
  (phi_iff ..).trans (by simp)

theorem phi1 {lt z y₁ y₂ y₃ : V} : Phi lt z (nm 1) y₁ y₂ y₃ ↔ (z ∈ y₁ ∧ ¬z ∈ y₂) :=
  (phi_iff ..).trans (by simp)

theorem phi2 {lt z y₁ y₂ y₃ : V} : Phi lt z (nm 2) y₁ y₂ y₃ ↔ FunR z y₁ y₂ :=
  (phi_iff ..).trans (by simp)

theorem phi3 {lt z y₁ y₂ y₃ : V} : Phi lt z (nm 3) y₁ y₂ y₃ ↔ (z ∈ y₁ ∧ MemAt z y₂ y₃) :=
  (phi_iff ..).trans (by simp)

theorem phi4 {lt z y₁ y₂ y₃ : V} : Phi lt z (nm 4) y₁ y₂ y₃ ↔ (z ∈ y₁ ∧ EqAt z y₂ y₃) :=
  (phi_iff ..).trans (by simp)

theorem phi5 {lt z y₁ y₂ y₃ : V} :
    Phi lt z (nm 5) y₁ y₂ y₃ ↔ (z ∈ y₁ ∧ ∃ e, e ∈ y₂ ∧ AgreeOff z e y₃) :=
  (phi_iff ..).trans (by simp)

theorem phi6 {lt z y₁ y₂ y₃ : V} :
    Phi lt z (nm 6) y₁ y₂ y₃ ↔ ∃ e, e ∈ y₁ ∧ (Pr e y₃ z ∧ AgreeOff y₂ e y₃) :=
  (phi_iff ..).trans (by simp)

theorem phi7 {lt z y₁ y₂ y₃ : V} : Phi lt z (nm 7) y₁ y₂ y₃ ↔ z ∈ lt :=
  (phi_iff ..).trans (by simp)

theorem isD_of {A lt s y₁ y₂ y₃ x : V} (h : ∀ z, z ∈ x ↔ z ∈ A ∧ Phi lt z s y₁ y₂ y₃) :
    IsD A lt s y₁ y₂ y₃ x :=
  ⟨fun z hz => (h z).mp hz, fun z hz hp => (h z).mpr ⟨hz, hp⟩⟩

theorem adj_char {γ y₁ y₂ y₃ : V} (hγ : Ord γ) (h1 : y₁ ∈ Lev γ) (h2 : y₂ ∈ Lev γ) (z : V) :
    z ∈ (insert y₂ y₁ : V) ↔ z ∈ Lev γ ∧ Phi (LtS γ) z (nm 0) y₁ y₂ y₃ := by
  rw [phi0]
  constructor
  · intro hz
    rcases (by simpa using hz : z = y₂ ∨ z ∈ y₁) with e | hz
    · exact ⟨e ▸ h2, Or.inr e⟩
    · exact ⟨lev_tr hγ y₁ h1 z hz, Or.inl hz⟩
  · rintro ⟨-, hz | e⟩
    · simp [hz]
    · simp [e]

theorem adj_mem_lev {γ y₁ y₂ : V} (hγ : Ord γ) (hne : ∃ z, z ∈ γ) (h₁ : y₁ ∈ Lev γ)
    (h₂ : y₂ ∈ Lev γ) : (insert y₂ y₁ : V) ∈ Lev (sc γ) :=
  def_mem_lev (ord_sc hγ) (self_mem_sc γ) (empty_mem_lev hγ hne) h₁ h₂ h₂
    (isD_of (s := nm 0) (adj_char hγ h₁ h₂))

theorem insert_empty (a : V) : (insert a (∅ : V) : V) = {a} := mem_ext fun z => by simp

theorem nm_mem_lev_nm : ∀ k : ℕ, (nm k : V) ∈ Lev (nm (k + 1) : V)
  | 0 => empty_mem_lev (ord_nm 1) ⟨∅, self_mem_sc _⟩
  | k + 1 =>
    adj_mem_lev (ord_nm (k + 1)) ⟨nm k, self_mem_sc _⟩ (nm_mem_lev_nm k) (nm_mem_lev_nm k)

theorem nm_mem_lev {γ : V} (hγ : Big γ) (k : ℕ) : (nm k : V) ∈ Lev γ :=
  lev_mono hγ.1 (hγ.2 _ (nm_mem_om (k + 1))) _ (nm_mem_lev_nm k)

theorem big_ne {γ : V} (hγ : Big γ) : ∃ z, z ∈ γ := ⟨∅, hγ.2 _ empty_mem_om⟩

theorem kp_mem_lev {γ a b : V} (hγ : Big γ) (ha : a ∈ Lev γ) (hb : b ∈ Lev γ) :
    kp a b ∈ Lev (scn 4 γ) := by
  have h0 := empty_mem_lev hγ.1 (big_ne hγ)
  have g1 := big_scn hγ 1
  have g2 := big_scn hγ 2
  have g3 := big_scn hγ 3
  have s1 : ({a} : V) ∈ Lev (scn 1 γ) := insert_empty a ▸ adj_mem_lev hγ.1 (big_ne hγ) h0 ha
  have s2 : ({b} : V) ∈ Lev (scn 1 γ) := insert_empty b ▸ adj_mem_lev hγ.1 (big_ne hγ) h0 hb
  have s3 : ({a, b} : V) ∈ Lev (scn 2 γ) :=
    adj_mem_lev g1.1 (big_ne g1) s2 (lev_scn_sub hγ.1 1 a ha)
  have s4 : ({{a, b}} : V) ∈ Lev (scn 3 γ) :=
    insert_empty ({a, b} : V) ▸ adj_mem_lev g2.1 (big_ne g2)
      (empty_mem_lev g2.1 (big_ne g2)) s3
  exact adj_mem_lev g3.1 (big_ne g3) s4 (lev_scn_sub g1.1 2 _ s1)

end levels

/-! ### Finite functions on numerals -/

section fn

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- The coordinate of the variable `i` among `n` variables: the most recent variable `0` has
the last coordinate. -/
def co (n : ℕ) (i : Fin n) : ℕ := n - 1 - (i : ℕ)

theorem co_zero (n : ℕ) : co (n + 1) 0 = n := by simp [co]

theorem co_succ {n : ℕ} (i : Fin n) : co (n + 1) i.succ = co n i := by
  simp [co]; omega

theorem co_lt {n : ℕ} (i : Fin n) : co n i < n := by
  have := i.2; simp only [co]; omega

theorem co_inj {n : ℕ} {i j : Fin n} (h : co n i = co n j) : i = j := by
  have := i.2; have := j.2
  apply Fin.ext
  simp only [co] at h
  omega

/-- The function on the numeral `n` whose value at the coordinate of `i` is `e i`. -/
noncomputable def fnOf : (n : ℕ) → (Fin n → V) → V
  | 0, _ => ∅
  | n + 1, e => insert (kp (nm n) (e 0)) (fnOf n (fun i ↦ e i.succ))

theorem mem_fnOf : ∀ {n : ℕ} {e : Fin n → V} {p : V},
    p ∈ fnOf n e ↔ ∃ i : Fin n, p = kp (nm (co n i)) (e i)
  | 0, e, p => by simp [fnOf]
  | n + 1, e, p => by
    have h1 : p ∈ fnOf (n + 1) e ↔ p = kp (nm n) (e 0) ∨ p ∈ fnOf n (fun i ↦ e i.succ) := by
      simp [fnOf]
    rw [h1, mem_fnOf (n := n)]
    constructor
    · rintro (h | ⟨i, h⟩)
      · exact ⟨0, by rw [co_zero]; exact h⟩
      · exact ⟨i.succ, by rw [co_succ]; exact h⟩
    · rintro ⟨i, h⟩
      cases i using Fin.cases with
      | zero => left; rw [co_zero] at h; exact h
      | succ i => right; rw [co_succ] at h; exact ⟨i, h⟩

theorem pr_fnOf {n : ℕ} {e : Fin n → V} {i : Fin n} {x : V} :
    Pr (fnOf n e) (nm (co n i)) x ↔ x = e i := by
  rw [pr_iff, mem_fnOf]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨h1, h2⟩ := kp_inj hj
    have := co_inj (nm_inj h1)
    subst this
    exact h2
  · intro h
    exact ⟨i, by rw [h]⟩

theorem fnOf_inj {n : ℕ} {e e' : Fin n → V} (h : fnOf n e = fnOf n e') : e = e' := by
  funext i
  have h1 : Pr (fnOf n e) (nm (co n i)) (e i) := pr_fnOf.mpr rfl
  rw [h] at h1
  exact pr_fnOf.mp h1

theorem memAt_iff {z i j : V} : MemAt z i j ↔ ∃ a b, Pr z i a ∧ Pr z j b ∧ a ∈ b := by
  constructor
  · rintro ⟨p, hp, u, -, a, -, q, hq, w, -, b, -, h1, h2, h3⟩
    exact ⟨a, b, ⟨p, hp, h1⟩, ⟨q, hq, h2⟩, h3⟩
  · rintro ⟨a, b, ⟨p, hp, h1⟩, ⟨q, hq, h2⟩, h3⟩
    obtain ⟨u, hu, hau⟩ := pr_snd_mem h1
    obtain ⟨w, hw, hbw⟩ := pr_snd_mem h2
    exact ⟨p, hp, u, hu, a, hau, q, hq, w, hw, b, hbw, h1, h2, h3⟩

theorem eqAt_iff {z i j : V} : EqAt z i j ↔ ∃ a, Pr z i a ∧ Pr z j a := by
  constructor
  · rintro ⟨p, hp, u, -, a, -, h1, h2⟩
    exact ⟨a, ⟨p, hp, h1⟩, h2⟩
  · rintro ⟨a, ⟨p, hp, h1⟩, h2⟩
    obtain ⟨u, hu, hau⟩ := pr_snd_mem h1
    exact ⟨p, hp, u, hu, a, hau, h1, h2⟩

theorem memAt_fnOf {n : ℕ} {e : Fin n → V} {i j : Fin n} :
    MemAt (fnOf n e) (nm (co n i)) (nm (co n j)) ↔ e i ∈ e j := by
  rw [memAt_iff]
  constructor
  · rintro ⟨a, b, h1, h2, h3⟩
    rw [pr_fnOf.mp h1, pr_fnOf.mp h2] at h3
    exact h3
  · intro h
    exact ⟨e i, e j, pr_fnOf.mpr rfl, pr_fnOf.mpr rfl, h⟩

theorem eqAt_fnOf {n : ℕ} {e : Fin n → V} {i j : Fin n} :
    EqAt (fnOf n e) (nm (co n i)) (nm (co n j)) ↔ e i = e j := by
  rw [eqAt_iff]
  constructor
  · rintro ⟨a, h1, h2⟩
    rw [← pr_fnOf.mp h1, ← pr_fnOf.mp h2]
  · intro h
    exact ⟨e i, pr_fnOf.mpr rfl, pr_fnOf.mpr h⟩

theorem agreeOff_fnOf {n : ℕ} {e : Fin n → V} {e₂ : Fin (n + 1) → V} :
    AgreeOff (fnOf n e) (fnOf (n + 1) e₂) (nm n) ↔ ∀ i, e i = e₂ i.succ := by
  constructor
  · intro h i
    rcases h _ (mem_fnOf.mpr ⟨i, rfl⟩) with ⟨u, -, a, -, hop⟩ | hp
    · have h1 := (kp_inj (isOp_iff.mp hop)).1
      have h2 := nm_inj h1
      have := co_lt i
      omega
    · have h1 : Pr (fnOf (n + 1) e₂) (nm (co (n + 1) i.succ)) (e i) := by
        rw [co_succ]; exact pr_iff.mpr hp
      exact pr_fnOf.mp h1
  · intro h p hp
    obtain ⟨i, rfl⟩ := mem_fnOf.mp hp
    right
    exact mem_fnOf.mpr ⟨i.succ, by rw [co_succ, h i]⟩

theorem funR_fnOf {n : ℕ} {t : V} (e : Fin n → V) (he : ∀ i, e i ∈ t) :
    FunR (fnOf n e) (nm n) t := by
  refine ⟨fun p hp => ?_, fun i hi => ?_, fun p hp q hq i _ a _ b _ h1 h2 => ?_⟩
  · obtain ⟨i, rfl⟩ := mem_fnOf.mp hp
    exact ⟨_, nm_mem_of_lt (co_lt i), e i, he i, isOp_kp _ _⟩
  · obtain ⟨j, hj, rfl⟩ := mem_nm.mp hi
    have hlt : n - 1 - j < n := by omega
    have hco : co n ⟨n - 1 - j, hlt⟩ = j := by simp only [co]; omega
    refine ⟨kp (nm j) (e ⟨n - 1 - j, hlt⟩), mem_fnOf.mpr ⟨⟨n - 1 - j, hlt⟩, ?_⟩, e _, he _,
      isOp_kp _ _⟩
    rw [hco]
  · obtain ⟨i₁, rfl⟩ := mem_fnOf.mp hp
    obtain ⟨i₂, rfl⟩ := mem_fnOf.mp hq
    obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp h1)
    obtain ⟨e3, e4⟩ := kp_inj (isOp_iff.mp h2)
    have := co_inj (nm_inj (e1.trans e3.symm))
    subst this
    exact e2.symm.trans e4

theorem funR_exists : ∀ (n : ℕ) {t z : V}, FunR z (nm n) t →
    ∃ e : Fin n → V, (∀ i, e i ∈ t) ∧ z = fnOf n e
  | 0, t, z, h => ⟨Fin.elim0, fun i => i.elim0, mem_ext fun p =>
      ⟨fun hp => by
        obtain ⟨i, hi, -⟩ := h.1 p hp
        exact absurd hi (by simp [nm]), fun hp => absurd hp (by simp [fnOf])⟩⟩
  | n + 1, t, z, h => by
    obtain ⟨p₀, hp₀, a₀, ha₀, hop₀⟩ := h.2.1 (nm n) (self_mem_sc _)
    let z' : V := sepB (k := 1) (BDef.eq 0 1).not z ![p₀]
    have hz' : ∀ p, p ∈ z' ↔ p ∈ z ∧ ¬p = p₀ := fun p => mem_sepB _ _ _ p
    have hF : FunR z' (nm n) t := by
      refine ⟨fun p hp => ?_, fun i hi => ?_, fun p hp q hq i hi a ha b hb h1 h2 => ?_⟩
      · obtain ⟨hpz, hne⟩ := (hz' p).mp hp
        obtain ⟨i, hi, a, ha, hop⟩ := h.1 p hpz
        have hi' : i ∈ sc (nm n : V) := hi
        rcases mem_sc.mp hi' with e | hi''
        · rw [e] at hop
          have := h.2.2 p hpz p₀ hp₀ _ (self_mem_sc _) a ha a₀ ha₀ hop hop₀
          rw [this] at hop
          exact absurd ((isOp_iff.mp hop).trans (isOp_iff.mp hop₀).symm) hne
        · exact ⟨i, hi'', a, ha, hop⟩
      · obtain ⟨p, hp, a, ha, hop⟩ := h.2.1 i (mem_sc.mpr (Or.inr hi))
        refine ⟨p, (hz' p).mpr ⟨hp, fun e => ?_⟩, a, ha, hop⟩
        rw [e] at hop
        have := (op_inj hop hop₀).1
        rw [this] at hi
        exact mem_irrefl _ hi
      · exact h.2.2 p ((hz' p).mp hp).1 q ((hz' q).mp hq).1 i (mem_sc.mpr (Or.inr hi)) a ha b hb
          h1 h2
    obtain ⟨e', he', hze'⟩ := funR_exists n hF
    refine ⟨a₀ :> e', fun i => ?_, ?_⟩
    · cases i using Fin.cases with
      | zero => exact ha₀
      | succ i => exact he' i
    · refine mem_ext fun p => ?_
      have h1 : p ∈ fnOf (n + 1) (a₀ :> e') ↔ p = kp (nm n) a₀ ∨ p ∈ fnOf n e' := by
        simp [fnOf]
      rw [h1, ← hze', hz']
      have e₀ : p₀ = kp (nm n) a₀ := isOp_iff.mp hop₀
      constructor
      · intro hp
        by_cases e : p = p₀
        · exact Or.inl (e.trans e₀)
        · exact Or.inr ⟨hp, e⟩
      · rintro (e | ⟨hp, -⟩)
        · rw [e, ← e₀]; exact hp₀
        · exact hp

theorem funR_iff {n : ℕ} {t z : V} :
    FunR z (nm n) t ↔ ∃ e : Fin n → V, (∀ i, e i ∈ t) ∧ z = fnOf n e :=
  ⟨funR_exists n, fun ⟨e, he, h⟩ => h ▸ funR_fnOf e he⟩

end fn

/-! ### Closed properties -/

section good

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- A property of sets that contains the numerals and is closed under the successor of levels
and under the operations. -/
structure Closed (X : V → Prop) : Prop where
  num : ∀ k : ℕ, X (nm k)
  succ : ∀ γ, Ord γ → X (Lev γ) → X (Lev (sc γ))
  op : ∀ γ s y₁ y₂ y₃ x, Ord γ → X (Lev γ) → s ∈ Lev γ → y₁ ∈ Lev γ → y₂ ∈ Lev γ → y₃ ∈ Lev γ →
    X s → X y₁ → X y₂ → X y₃ → IsD (Lev γ) (LtS γ) s y₁ y₂ y₃ x → X x

/-- `x` has the property, and is a member of a level that has it and includes `ω`. -/
def Good (X : V → Prop) (x : V) : Prop := X x ∧ ∃ γ, Big γ ∧ X (Lev γ) ∧ x ∈ Lev γ

variable {X : V → Prop}

theorem good_common {a : V} (ha : Good X a) : ∀ l : List V, (∀ b ∈ l, Good X b) →
    ∃ γ, Big γ ∧ X (Lev γ) ∧ a ∈ Lev γ ∧ ∀ b ∈ l, b ∈ Lev γ
  | [], _ => let ⟨_, γ, h1, h2, h3⟩ := ha; ⟨γ, h1, h2, h3, by simp⟩
  | b :: l, h => by
    obtain ⟨γ, hγ, hXγ, haγ, hl⟩ := good_common ha l (fun c hc => h c (List.mem_cons_of_mem _ hc))
    obtain ⟨-, γ', hγ', hXγ', hbγ'⟩ := h b (by simp)
    rcases ord_tri hγ.1 hγ'.1 with e | e | e
    · refine ⟨γ', hγ', hXγ', lev_mono hγ'.1 e a haγ, fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with e' | hc
      · rw [e']; exact hbγ'
      · exact lev_mono hγ'.1 e c (hl c hc)
    · refine ⟨γ, hγ, hXγ, haγ, fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with e' | hc
      · rw [e', e]; exact hbγ'
      · exact hl c hc
    · refine ⟨γ, hγ, hXγ, haγ, fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with e' | hc
      · rw [e']; exact lev_mono hγ.1 e b hbγ'
      · exact hl c hc

theorem good_nm (hX : Closed X) {a : V} (ha : Good X a) (k : ℕ) : Good X (nm k) :=
  ⟨hX.num k, let ⟨_, γ, hγ, hXγ, _⟩ := ha; ⟨γ, hγ, hXγ, nm_mem_lev hγ k⟩⟩

/-- **A set obtained by one operation from sets with the property has the property.** -/
theorem good_def (hX : Closed X) (i : ℕ) {y₁ y₂ y₃ x : V}
    (h₁ : Good X y₁) (h₂ : Good X y₂) (h₃ : Good X y₃)
    (hx : ∀ γ, Ord γ → y₁ ∈ Lev γ → y₂ ∈ Lev γ → y₃ ∈ Lev γ →
      ∀ z, z ∈ x ↔ z ∈ Lev γ ∧ Phi (LtS γ) z (nm i) y₁ y₂ y₃) : Good X x := by
  obtain ⟨γ, hγ, hXγ, h1, hl⟩ := good_common h₁ [y₂, y₃] (by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with e | e
    · rw [e]; exact h₂
    · rw [e]; exact h₃)
  have h2 : y₂ ∈ Lev γ := hl y₂ (by simp)
  have h3 : y₃ ∈ Lev γ := hl y₃ (by simp)
  have hD : IsD (Lev γ) (LtS γ) (nm i) y₁ y₂ y₃ x := isD_of (hx γ hγ.1 h1 h2 h3)
  exact ⟨hX.op γ _ _ _ _ x hγ.1 hXγ (nm_mem_lev hγ i) h1 h2 h3 (hX.num i) h₁.1 h₂.1 h₃.1 hD,
    sc γ, big_sc hγ, hX.succ γ hγ.1 hXγ,
    def_mem_lev (ord_sc hγ.1) (self_mem_sc γ) (nm_mem_lev hγ i) h1 h2 h3 hD⟩

theorem good_adj (hX : Closed X) {y₁ y₂ : V} (h₁ : Good X y₁) (h₂ : Good X y₂) :
    Good X (insert y₂ y₁ : V) :=
  good_def hX 0 h₁ h₂ h₂ fun _ hγ h1 h2 _ z => adj_char hγ h1 h2 z

theorem good_diff (hX : Closed X) {y₁ y₂ x : V} (h₁ : Good X y₁) (h₂ : Good X y₂)
    (hx : ∀ z, z ∈ x ↔ z ∈ y₁ ∧ ¬z ∈ y₂) : Good X x :=
  good_def hX 1 h₁ h₂ h₂ fun γ hγ h1 _ _ z => by
    rw [phi1, hx]
    exact ⟨fun h => ⟨lev_tr hγ y₁ h1 z h.1, h⟩, fun h => h.2⟩

theorem good_memAt (hX : Closed X) {F x : V} (hF : Good X F) (a b : ℕ)
    (hx : ∀ z, z ∈ x ↔ z ∈ F ∧ MemAt z (nm a) (nm b)) : Good X x :=
  good_def hX 3 hF (good_nm hX hF a) (good_nm hX hF b) fun γ hγ h1 _ _ z => by
    rw [phi3, hx]
    exact ⟨fun h => ⟨lev_tr hγ F h1 z h.1, h⟩, fun h => h.2⟩

theorem good_eqAt (hX : Closed X) {F x : V} (hF : Good X F) (a b : ℕ)
    (hx : ∀ z, z ∈ x ↔ z ∈ F ∧ EqAt z (nm a) (nm b)) : Good X x :=
  good_def hX 4 hF (good_nm hX hF a) (good_nm hX hF b) fun γ hγ h1 _ _ z => by
    rw [phi4, hx]
    exact ⟨fun h => ⟨lev_tr hγ F h1 z h.1, h⟩, fun h => h.2⟩

theorem good_ex (hX : Closed X) {F E x : V} (hF : Good X F) (hE : Good X E) (n : ℕ)
    (hx : ∀ z, z ∈ x ↔ z ∈ F ∧ ∃ e, e ∈ E ∧ AgreeOff z e (nm n)) : Good X x :=
  good_def hX 5 hF hE (good_nm hX hF n) fun γ hγ h1 _ _ z => by
    rw [phi5, hx]
    exact ⟨fun h => ⟨lev_tr hγ F h1 z h.1, h⟩, fun h => h.2⟩

theorem good_slice (hX : Closed X) {E e₀ x : V} (hE : Good X E) (h₀ : Good X e₀) (n : ℕ)
    (hx : ∀ z, z ∈ x ↔ ∃ e, e ∈ E ∧ (Pr e (nm n) z ∧ AgreeOff e₀ e (nm n))) : Good X x :=
  good_def hX 6 hE h₀ (good_nm hX hE n) fun γ hγ h1 _ _ z => by
    rw [phi6, hx]
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    obtain ⟨e, he, ⟨p, hp, hop⟩, -⟩ := h
    obtain ⟨u, hu, hzu⟩ := pr_snd_mem hop
    have t1 := lev_tr hγ E h1 e he
    have t2 := lev_tr hγ e t1 p hp
    have t3 := lev_tr hγ p t2 u hu
    exact lev_tr hγ u t3 z hzu

theorem good_sing (hX : Closed X) {a : V} (ha : Good X a) : Good X ({a} : V) :=
  insert_empty a ▸ good_adj hX (good_nm hX ha 0) ha

theorem good_kp (hX : Closed X) {a b : V} (ha : Good X a) (hb : Good X b) : Good X (kp a b) := by
  have s3 : Good X ({a, b} : V) := good_adj hX (good_sing hX hb) ha
  exact good_adj hX (good_sing hX s3) (good_sing hX ha)

theorem good_fnOf (hX : Closed X) {a : V} (ha : Good X a) : ∀ (n : ℕ) (e : Fin n → V),
    (∀ i, Good X (e i)) → Good X (fnOf n e)
  | 0, _, _ => good_nm hX ha 0
  | n + 1, e, he => good_adj hX (good_fnOf hX ha n _ fun i => he i.succ)
      (good_kp hX (good_nm hX ha n) (he 0))

theorem x_scn (hX : Closed X) {γ : V} (hγ : Ord γ) (h : X (Lev γ)) : ∀ k, X (Lev (scn k γ))
  | 0 => h
  | k + 1 => hX.succ _ (ord_scn hγ k) (x_scn hX hγ h k)

/-- All the functions from the numeral `n` to `t` are members of one level. -/
theorem fnOf_mem_lev {γ t : V} (hγ : Big γ) (ht : t ∈ Lev γ) : ∀ (n : ℕ) (e : Fin n → V),
    (∀ i, e i ∈ t) → fnOf n e ∈ Lev (scn n (scn 4 γ))
  | 0, _, _ => empty_mem_lev (big_scn hγ 4).1 (big_ne (big_scn hγ 4))
  | n + 1, e, he => by
    have g := big_scn (big_scn hγ 4) n
    have h1 := fnOf_mem_lev hγ ht n (fun i ↦ e i.succ) (fun i => he i.succ)
    have h2 : kp (nm n) (e 0) ∈ Lev (scn 4 γ) :=
      kp_mem_lev hγ (nm_mem_lev hγ n) (lev_tr hγ.1 t ht _ (he 0))
    exact adj_mem_lev g.1 (big_ne g) h1 (lev_scn_sub (big_scn hγ 4).1 n _ h2)

/-- **The set of all the functions from the numeral `n` to `t`.** -/
theorem good_fun (hX : Closed X) {t : V} (ht : Good X t) (n : ℕ) :
    ∃ F, Good X F ∧ ∀ z, z ∈ F ↔ FunR z (nm n) t := by
  obtain ⟨hXt, γ, hγ, hXγ, htγ⟩ := ht
  let γ' : V := scn n (scn 4 γ)
  have hγ' : Big γ' := big_scn (big_scn hγ 4) n
  have hXγ' : X (Lev γ') := x_scn hX (big_scn hγ 4).1 (x_scn hX hγ.1 hXγ 4) n
  have htγ' : t ∈ Lev γ' := lev_scn_sub (big_scn hγ 4).1 n _ (lev_scn_sub hγ.1 4 _ htγ)
  let F : V := sepB (k := 2) (funRB.comp ![0, 1, 2]) (Lev γ') ![nm n, t]
  have hF : ∀ z, z ∈ F ↔ z ∈ Lev γ' ∧ FunR z (nm n) t := fun z => mem_sepB _ _ _ z
  have hD : IsD (Lev γ') (LtS γ') (nm 2) (nm n) t t F := isD_of fun z => by rw [phi2, hF]
  refine ⟨F, ⟨hX.op γ' _ _ _ _ F hγ'.1 hXγ' (nm_mem_lev hγ' 2) (nm_mem_lev hγ' n) htγ' htγ'
      (hX.num 2) (hX.num n) hXt hXt hD, sc γ', big_sc hγ', hX.succ γ' hγ'.1 hXγ',
      def_mem_lev (ord_sc hγ'.1) (self_mem_sc γ') (nm_mem_lev hγ' 2) (nm_mem_lev hγ' n) htγ' htγ'
        hD⟩, fun z => ⟨fun h => ((hF z).mp h).2, fun h => (hF z).mpr ⟨?_, h⟩⟩⟩
  obtain ⟨e, he, rfl⟩ := funR_iff.mp h
  exact fnOf_mem_lev hγ htγ n e he

end good

/-! ### The valuations that satisfy a formula -/

section sat

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

variable {X : V → Prop}

/-- The code of a valuation in `t`. -/
noncomputable def fnS {t : V} {n : ℕ} (e : Fin n → extSet t) : V := fnOf n (fun i ↦ (e i : V))

theorem fnS_inj {t : V} {n : ℕ} {e e' : Fin n → extSet t} (h : fnS e = fnS e') : e = e' := by
  have := fnOf_inj h
  funext i
  exact Subtype.ext (congrFun this i)

theorem pr_fnOf_zero {n : ℕ} {e : Fin (n + 1) → V} {x : V} :
    Pr (fnOf (n + 1) e) (nm n) x ↔ x = e 0 := by
  have := pr_fnOf (e := e) (i := 0) (x := x)
  rwa [co_zero] at this

/-- `E` is the set of the codes of the valuations in `t` with the property `P`. -/
def Rep (t : V) (n : ℕ) (P : (Fin n → extSet t) → Prop) (E : V) : Prop :=
  ∀ z, z ∈ E ↔ ∃ e : Fin n → extSet t, z = fnS e ∧ P e

theorem rep_congr {t : V} {n : ℕ} {P Q : (Fin n → extSet t) → Prop} {E : V}
    (h : ∀ e, P e ↔ Q e) (hR : Rep t n P E) : Rep t n Q E :=
  fun z => (hR z).trans (exists_congr fun e => and_congr Iff.rfl (h e))

theorem rep_top (hX : Closed X) {t : V} (ht : Good X t) (n : ℕ) :
    ∃ E, Good X E ∧ Rep t n (fun _ ↦ True) E := by
  obtain ⟨F, hF, hFm⟩ := good_fun hX ht n
  refine ⟨F, hF, fun z => (hFm z).trans (funR_iff.trans ?_)⟩
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨fun i ↦ ⟨e i, he i⟩, rfl, trivial⟩
  · rintro ⟨e, rfl, -⟩
    exact ⟨fun i ↦ (e i : V), fun i => (e i).2, rfl⟩

/-- The difference of two sets. -/
noncomputable def diffS (a b : V) : V := sepB (k := 1) (BDef.mem 0 1).not a ![b]

theorem mem_diffS {a b z : V} : z ∈ diffS a b ↔ z ∈ a ∧ ¬z ∈ b := mem_sepB _ _ _ z

theorem rep_not (hX : Closed X) {t : V} (ht : Good X t) {n : ℕ}
    {P : (Fin n → extSet t) → Prop} {E : V} (hE : Good X E) (hR : Rep t n P E) :
    ∃ E', Good X E' ∧ Rep t n (fun e ↦ ¬P e) E' := by
  obtain ⟨F, hF, hFR⟩ := rep_top hX ht n
  refine ⟨diffS F E, good_diff hX hF hE (fun z => mem_diffS), fun z => ?_⟩
  rw [mem_diffS, hFR z, hR z]
  constructor
  · rintro ⟨⟨e, rfl, -⟩, hn⟩
    exact ⟨e, rfl, fun hP => hn ⟨e, rfl, hP⟩⟩
  · rintro ⟨e, rfl, hn⟩
    refine ⟨⟨e, rfl, trivial⟩, ?_⟩
    rintro ⟨e', he', hP⟩
    rw [fnS_inj he'] at hn
    exact hn hP

theorem rep_and (hX : Closed X) {t : V} {n : ℕ} {P Q : (Fin n → extSet t) → Prop} {E₁ E₂ : V}
    (h₁ : Good X E₁) (h₂ : Good X E₂) (hR₁ : Rep t n P E₁) (hR₂ : Rep t n Q E₂) :
    ∃ E, Good X E ∧ Rep t n (fun e ↦ P e ∧ Q e) E := by
  have hD : Good X (diffS E₁ E₂) := good_diff hX h₁ h₂ (fun z => mem_diffS)
  refine ⟨diffS E₁ (diffS E₁ E₂), good_diff hX h₁ hD (fun z => mem_diffS), fun z => ?_⟩
  rw [mem_diffS, mem_diffS]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : z ∈ E₂ := by
      by_contra h
      exact h2 ⟨h1, h⟩
    obtain ⟨e, rfl, hP⟩ := (hR₁ z).mp h1
    obtain ⟨e', he', hQ⟩ := (hR₂ _).mp h3
    rw [← fnS_inj he'] at hQ
    exact ⟨e, rfl, hP, hQ⟩
  · rintro ⟨e, rfl, hP, hQ⟩
    exact ⟨(hR₁ _).mpr ⟨e, rfl, hP⟩, fun h => h.2 ((hR₂ _).mpr ⟨e, rfl, hQ⟩)⟩

theorem rep_or (hX : Closed X) {t : V} (ht : Good X t) {n : ℕ}
    {P Q : (Fin n → extSet t) → Prop} {E₁ E₂ : V}
    (h₁ : Good X E₁) (h₂ : Good X E₂) (hR₁ : Rep t n P E₁) (hR₂ : Rep t n Q E₂) :
    ∃ E, Good X E ∧ Rep t n (fun e ↦ P e ∨ Q e) E := by
  obtain ⟨A, hA, hRA⟩ := rep_not hX ht h₁ hR₁
  obtain ⟨B, hB, hRB⟩ := rep_not hX ht h₂ hR₂
  obtain ⟨C, hC, hRC⟩ := rep_and hX hA hB hRA hRB
  obtain ⟨D, hD, hRD⟩ := rep_not hX ht hC hRC
  exact ⟨D, hD, rep_congr (fun e => by rw [not_and_or, not_not, not_not]) hRD⟩

theorem rep_mem (hX : Closed X) {t : V} (ht : Good X t) {n : ℕ} (i j : Fin n) :
    ∃ E, Good X E ∧ Rep t n (fun e ↦ (e i : V) ∈ (e j : V)) E := by
  obtain ⟨F, hF, hFR⟩ := rep_top hX ht n
  let E : V := sepB (k := 2) (memAtB.comp ![0, 1, 2]) F ![nm (co n i), nm (co n j)]
  have hE : ∀ z, z ∈ E ↔ z ∈ F ∧ MemAt z (nm (co n i)) (nm (co n j)) :=
    fun z => mem_sepB _ _ _ z
  refine ⟨E, good_memAt hX hF _ _ hE, fun z => ?_⟩
  rw [hE, hFR z]
  constructor
  · rintro ⟨⟨e, rfl, -⟩, h⟩
    exact ⟨e, rfl, memAt_fnOf.mp h⟩
  · rintro ⟨e, rfl, h⟩
    exact ⟨⟨e, rfl, trivial⟩, memAt_fnOf.mpr h⟩

theorem rep_eq (hX : Closed X) {t : V} (ht : Good X t) {n : ℕ} (i j : Fin n) :
    ∃ E, Good X E ∧ Rep t n (fun e ↦ (e i : V) = (e j : V)) E := by
  obtain ⟨F, hF, hFR⟩ := rep_top hX ht n
  let E : V := sepB (k := 2) (eqAtB.comp ![0, 1, 2]) F ![nm (co n i), nm (co n j)]
  have hE : ∀ z, z ∈ E ↔ z ∈ F ∧ EqAt z (nm (co n i)) (nm (co n j)) :=
    fun z => mem_sepB _ _ _ z
  refine ⟨E, good_eqAt hX hF _ _ hE, fun z => ?_⟩
  rw [hE, hFR z]
  constructor
  · rintro ⟨⟨e, rfl, -⟩, h⟩
    exact ⟨e, rfl, eqAt_fnOf.mp h⟩
  · rintro ⟨e, rfl, h⟩
    exact ⟨⟨e, rfl, trivial⟩, eqAt_fnOf.mpr h⟩

theorem rep_ex (hX : Closed X) {t : V} (ht : Good X t) {n : ℕ}
    {P : (Fin (n + 1) → extSet t) → Prop} {E : V} (hE : Good X E) (hR : Rep t (n + 1) P E) :
    ∃ E', Good X E' ∧ Rep t n (fun e ↦ ∃ x, P (x :> e)) E' := by
  obtain ⟨F, hF, hFR⟩ := rep_top hX ht n
  let E' : V := sepB (k := 2) (BDef.bex 1 (agreeOffB.comp ![1, 0, 3])) F ![E, nm n]
  have hE' : ∀ z, z ∈ E' ↔ z ∈ F ∧ ∃ e, e ∈ E ∧ AgreeOff z e (nm n) :=
    fun z => mem_sepB _ _ _ z
  refine ⟨E', good_ex hX hF hE n hE', fun z => ?_⟩
  rw [hE', hFR z]
  constructor
  · rintro ⟨⟨e, rfl, -⟩, e', he', hag⟩
    obtain ⟨e₂, rfl, hP⟩ := (hR e').mp he'
    have h := agreeOff_fnOf.mp hag
    have e₂eq : (e₂ 0 :> e) = e₂ := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact Subtype.ext (h i)
    exact ⟨e, rfl, e₂ 0, by rw [e₂eq]; exact hP⟩
  · rintro ⟨e, rfl, x, hP⟩
    exact ⟨⟨e, rfl, trivial⟩, fnS (x :> e), (hR _).mpr ⟨_, rfl, hP⟩,
      agreeOff_fnOf.mpr fun i => rfl⟩

theorem rep_all (hX : Closed X) {t : V} (ht : Good X t) {n : ℕ}
    {P : (Fin (n + 1) → extSet t) → Prop} {E : V} (hE : Good X E) (hR : Rep t (n + 1) P E) :
    ∃ E', Good X E' ∧ Rep t n (fun e ↦ ∀ x, P (x :> e)) E' := by
  obtain ⟨A, hA, hRA⟩ := rep_not hX ht hE hR
  obtain ⟨B, hB, hRB⟩ := rep_ex hX ht hA hRA
  obtain ⟨C, hC, hRC⟩ := rep_not hX ht hB hRB
  exact ⟨C, hC, rep_congr (fun e => not_exists_not) hRC⟩

lemma term_cases {n : ℕ} (u : Semiterm ℒₛₑₜ Empty n) : ∃ i : Fin n, u = #i := by
  match u with
  | #i => exact ⟨i, rfl⟩
  | &x => exact x.elim
  | .func f _ => exact Empty.elim f

/-- **For every formula, the set of the codes of the valuations in `t` that satisfy it in the
structure `(t, ∈)` has the property.** -/
theorem sat_good (hX : Closed X) {t : V} (ht : Good X t) :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n),
      ∃ E, Good X E ∧ Rep t n (fun e ↦ Eval (M := extSet t) e Empty.elim φ) E := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum =>
    obtain ⟨E, hE, hR⟩ := rep_top hX ht _
    exact ⟨E, hE, rep_congr (fun e => by simp) hR⟩
  | hfalsum =>
    obtain ⟨E, hE, hR⟩ := rep_top hX ht _
    obtain ⟨E', hE', hR'⟩ := rep_not hX ht hE hR
    exact ⟨E', hE', rep_congr (fun e => by simp) hR'⟩
  | hrel r v =>
    cases r with
    | eq =>
      obtain ⟨i, hi⟩ := term_cases (v 0)
      obtain ⟨j, hj⟩ := term_cases (v 1)
      obtain ⟨E, hE, hR⟩ := rep_eq hX ht i j
      refine ⟨E, hE, rep_congr (fun e => ?_) hR⟩
      show (e i : V) = (e j : V) ↔ ((v 0).val (M := extSet t) e Empty.elim =
        (v 1).val (M := extSet t) e Empty.elim)
      rw [hi, hj]
      simp [Subtype.ext_iff]
    | mem =>
      obtain ⟨i, hi⟩ := term_cases (v 0)
      obtain ⟨j, hj⟩ := term_cases (v 1)
      obtain ⟨E, hE, hR⟩ := rep_mem hX ht i j
      refine ⟨E, hE, rep_congr (fun e => ?_) hR⟩
      show (e i : V) ∈ (e j : V) ↔ ((v 0).val (M := extSet t) e Empty.elim ∈
        (v 1).val (M := extSet t) e Empty.elim)
      rw [hi, hj]
      simp only [Semiterm.val_bvar]
      exact Iff.rfl
  | hnrel r v =>
    cases r with
    | eq =>
      obtain ⟨i, hi⟩ := term_cases (v 0)
      obtain ⟨j, hj⟩ := term_cases (v 1)
      obtain ⟨E, hE, hR⟩ := rep_eq hX ht i j
      obtain ⟨E', hE', hR'⟩ := rep_not hX ht hE hR
      refine ⟨E', hE', rep_congr (fun e => ?_) hR'⟩
      show ¬(e i : V) = (e j : V) ↔ ¬((v 0).val (M := extSet t) e Empty.elim =
        (v 1).val (M := extSet t) e Empty.elim)
      rw [hi, hj]
      simp [Subtype.ext_iff]
    | mem =>
      obtain ⟨i, hi⟩ := term_cases (v 0)
      obtain ⟨j, hj⟩ := term_cases (v 1)
      obtain ⟨E, hE, hR⟩ := rep_mem hX ht i j
      obtain ⟨E', hE', hR'⟩ := rep_not hX ht hE hR
      refine ⟨E', hE', rep_congr (fun e => ?_) hR'⟩
      show ¬(e i : V) ∈ (e j : V) ↔ ¬((v 0).val (M := extSet t) e Empty.elim ∈
        (v 1).val (M := extSet t) e Empty.elim)
      rw [hi, hj]
      simp only [Semiterm.val_bvar]
      exact Iff.rfl
  | hand φ ψ ih1 ih2 =>
    obtain ⟨E₁, h₁, hR₁⟩ := ih1
    obtain ⟨E₂, h₂, hR₂⟩ := ih2
    obtain ⟨E, hE, hR⟩ := rep_and hX h₁ h₂ hR₁ hR₂
    exact ⟨E, hE, rep_congr (fun e => by simp) hR⟩
  | hor φ ψ ih1 ih2 =>
    obtain ⟨E₁, h₁, hR₁⟩ := ih1
    obtain ⟨E₂, h₂, hR₂⟩ := ih2
    obtain ⟨E, hE, hR⟩ := rep_or hX ht h₁ h₂ hR₁ hR₂
    exact ⟨E, hE, rep_congr (fun e => by simp) hR⟩
  | hall φ ih =>
    obtain ⟨E₁, h₁, hR₁⟩ := ih
    obtain ⟨E, hE, hR⟩ := rep_all hX ht h₁ hR₁
    exact ⟨E, hE, rep_congr (fun e => by simp) hR⟩
  | hexs φ ih =>
    obtain ⟨E₁, h₁, hR₁⟩ := ih
    obtain ⟨E, hE, hR⟩ := rep_ex hX ht h₁ hR₁
    exact ⟨E, hE, rep_congr (fun e => by simp) hR⟩

/-- The valuations whose first value varies and whose other values are given. -/
theorem rep_slice (hX : Closed X) {t : V} {m : ℕ} {P : (Fin (m + 1) → extSet t) → Prop} {E : V}
    (hE : Good X E) (hR : Rep t (m + 1) P E) (p : Fin m → extSet t)
    (hp : ∀ i, Good X (p i : V)) :
    ∃ y, Good X y ∧ ∀ z, z ∈ y ↔ ∃ hz : z ∈ extSet t, P ((⟨z, hz⟩ : extSet t) :> p) := by
  have h₀ : Good X (fnS p) := good_fnOf hX hE m _ hp
  let y : V := sepB (k := 3) (BDef.bex 1 ((prB.comp ![0, 4, 1]).and (agreeOffB.comp ![3, 0, 4])))
    t ![E, fnS p, nm m]
  have hy : ∀ z, z ∈ y ↔ z ∈ t ∧ ∃ e, e ∈ E ∧ (Pr e (nm m) z ∧ AgreeOff (fnS p) e (nm m)) :=
    fun z => mem_sepB _ _ _ z
  have hzt : ∀ z e, e ∈ E → Pr e (nm m) z → z ∈ t := by
    intro z e he hpr
    obtain ⟨e₂, rfl, -⟩ := (hR e).mp he
    rw [pr_fnOf_zero.mp hpr]
    exact (e₂ 0).2
  have hy' : ∀ z, z ∈ y ↔ ∃ e, e ∈ E ∧ (Pr e (nm m) z ∧ AgreeOff (fnS p) e (nm m)) :=
    fun z => (hy z).trans ⟨fun h => h.2, fun h => ⟨let ⟨e, he, hpr, _⟩ := h; hzt z e he hpr, h⟩⟩
  refine ⟨y, good_slice hX hE h₀ m hy', fun z => (hy' z).trans ?_⟩
  constructor
  · rintro ⟨e, he, hpr, hag⟩
    obtain ⟨e₂, rfl, hP⟩ := (hR e).mp he
    have hz0 : z = (e₂ 0 : V) := pr_fnOf_zero.mp hpr
    have h := agreeOff_fnOf.mp hag
    have hz : z ∈ extSet t := hz0 ▸ (e₂ 0).2
    have e₂eq : ((⟨z, hz⟩ : extSet t) :> p) = e₂ := by
      funext i
      cases i using Fin.cases with
      | zero => exact Subtype.ext hz0
      | succ i => exact Subtype.ext (h i)
    exact ⟨hz, by rw [e₂eq]; exact hP⟩
  · rintro ⟨hz, hP⟩
    exact ⟨fnS ((⟨z, hz⟩ : extSet t) :> p), (hR _).mpr ⟨_, rfl, hP⟩, pr_fnOf_zero.mpr rfl,
      agreeOff_fnOf.mpr fun i => rfl⟩

/-- **Every subset of `t` that is definable in the structure `(t, ∈)` with parameters has the
property.** -/
theorem sep_good (hX : Closed X) {t : V} (ht : Good X t) (ψ : SetTheorySemiproposition 1)
    (ε : ℕ → extSet t) (hε : ∀ k, Good X (ε k : V)) :
    ∃ y, Good X y ∧ ∀ z, z ∈ y ↔ ∃ hz : z ∈ extSet t, Eval (M := extSet t) ![⟨z, hz⟩] ε ψ := by
  classical
  let m := ψ.fvSup
  let ω : Rew ℒₛₑₜ ℕ 1 Empty (m + 1) :=
    Rew.bind (fun _ ↦ (#0 : Semiterm ℒₛₑₜ Empty (m + 1)))
      (fun k ↦ if h : k < m then (#(Fin.succ ⟨k, h⟩) : Semiterm ℒₛₑₜ Empty (m + 1)) else #0)
  obtain ⟨E, hE, hR⟩ := sat_good hX ht (ω ▹ ψ)
  obtain ⟨y, hy, hym⟩ := rep_slice hX hE hR (fun i : Fin m ↦ ε i) (fun i => hε i)
  refine ⟨y, hy, fun z => (hym z).trans (exists_congr fun hz => ?_)⟩
  have e1 : (Semiterm.val (M := extSet t) ((⟨z, hz⟩ : extSet t) :> fun i : Fin m ↦ ε i)
      Empty.elim ∘ ω ∘ Semiterm.bvar) = ![(⟨z, hz⟩ : extSet t)] := by
    funext i
    simp [ω]
  rw [eval_rew, e1]
  refine eval_iff_of_funEqOn ψ ?_
  intro k hk
  have hk' : k < m := lt_fvSup_of_fvar? hk
  simp [ω, hk']

/-- **Separation in a transitive set with the property**, for a condition with a bounded
definition. -/
theorem sep_good_bdef (hX : Closed X) {k : ℕ} {R : MRel (k + 1)} (d : BDef R) {t : V}
    (ht : Good X t) (htr : ∀ y, y ∈ t → ∀ z, z ∈ y → z ∈ t) (p : Fin k → V)
    (hp : ∀ i, p i ∈ t ∧ Good X (p i)) :
    ∃ y, Good X y ∧ ∀ z, z ∈ y ↔ z ∈ t ∧ R V (z :> p) := by
  obtain ⟨E, hE, hR⟩ := sat_good hX ht d.φ
  obtain ⟨y, hy, hym⟩ := rep_slice hX hE hR (fun i ↦ ⟨p i, (hp i).1⟩) (fun i => (hp i).2)
  refine ⟨y, hy, fun z => (hym z).trans ?_⟩
  have htr' : ∀ y ∈ extSet t, ∀ z ∈ y, z ∈ extSet t := htr
  have key : ∀ hz : z ∈ extSet t,
      (Eval (M := extSet t) ((⟨z, hz⟩ : extSet t) :> fun i ↦ (⟨p i, (hp i).1⟩ : extSet t))
        Empty.elim d.φ ↔ R V (z :> p)) := by
    intro hz
    have h1 := eval_submodel_iff (U := extSet t) htr' d.bdd
      ((⟨z, hz⟩ : extSet t) :> fun i ↦ (⟨p i, (hp i).1⟩ : extSet t)) Empty.elim
    have e1 : (fun i ↦ ((((⟨z, hz⟩ : extSet t) :> fun i ↦ (⟨p i, (hp i).1⟩ : extSet t)) i :
        extSet t) : V)) = (z :> p) := by
      funext i
      cases i using Fin.cases <;> simp
    have e2 : (fun x : Empty ↦ ((Empty.elim x : extSet t) : V)) = Empty.elim :=
      funext fun x => x.elim
    rw [e1, e2] at h1
    exact h1.trans (d.eval V (z :> p))
  exact ⟨fun ⟨hz, h⟩ => ⟨hz, (key hz).mp h⟩, fun ⟨hz, h⟩ => ⟨hz, (key hz).mpr h⟩⟩

/-- The trivial property is closed. -/
theorem closed_true : Closed (fun _ : V ↦ True) :=
  ⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial⟩

end sat

end MH

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.MH.sep_good
