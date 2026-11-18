import MDefs
import TSTTheories

set_option autoImplicit false

/-!
# `𝗠` interprets `𝗧𝗦𝗧𝗜`

Type `n` is interpreted as `Pⁿ(ω)`, membership as membership and equality as equality; the
domain is everything.

* **ω.** A set `J` is *inductive* (`IndR`) if it has a member without members and, with each
  member `x`, a member `x ∪ {x}`. `NatR x` says that `x` belongs to every inductive set. In a
  model of `𝗠` these `x` form a set, `lvl 0`. The definition has no parameters.
* **Levels.** `lvl (n + 1)` is the power set of `lvl n`. The formula for "`x` has type `n`" is
  `(tyF' n).φ`: there is `p` with `IsLvl n p` and `x ∈ p`.
* **Comprehension.** A typed formula becomes a bounded formula, with the levels as parameters
  (`toBdd`), and bounded separation applies (`ty_comp`).
* **Infinity.** The subsets of ω that are included in a member of ω form a family that contains
  the empty set, is closed under adjoining one element and does not contain ω (`ty_inf`). The
  closure uses three facts about ω, each proved by induction: its members are transitive
  (`nat_trans`); `n ⊆ b → n = b ∨ n ∈ b` (`nat_D`); `b ∈ n ∨ n ⊆ b` (`nat_C`).
* **Result**: `mInterpretsTSTI : 𝗠 ⊳ 𝗧𝗦𝗧𝗜`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula
open JensenNFU (TFm)

/-! ### Relations and their definitions -/

section rel

variable {V : Type} [SetStructure V]

/-- `y = x ∪ {x}`, written with bounded quantifiers. -/
def SuccR (y x : V) : Prop := (∀ z ∈ y, z = x ∨ z ∈ x) ∧ x ∈ y ∧ ∀ z ∈ x, z ∈ y

/-- `J` is inductive. -/
def IndR (J : V) : Prop :=
  (∃ e : V, e ∈ J ∧ ∀ z : V, z ∈ e → False) ∧ ∀ x : V, x ∈ J → ∃ y : V, y ∈ J ∧ SuccR y x

/-- `x` belongs to every inductive set. -/
def NatR (x : V) : Prop := ∀ J : V, IndR J → x ∈ J

/-- `p` is the level `n`: `Pⁿ` of the collection of all `x` with `NatR x`. -/
def IsLvl : ℕ → V → Prop
  | 0, p => ∀ z, z ∈ p ↔ NatR z
  | n + 1, p => ∃ q, IsLvl n q ∧ ∀ z, z ∈ p ↔ ∀ w ∈ z, w ∈ q

/-- `x` has type `n`. -/
def TyR (n : ℕ) (x : V) : Prop := ∃ p : V, IsLvl n p ∧ x ∈ p

theorem succR_iff {y x : V} : SuccR y x ↔ ∀ z, z ∈ y ↔ z = x ∨ z ∈ x := by
  constructor
  · rintro ⟨h1, h2, h3⟩ z
    exact ⟨h1 z, fun h => h.elim (fun e => e ▸ h2) (h3 z)⟩
  · intro h
    exact ⟨fun z hz => (h z).mp hz, (h x).mpr (Or.inl rfl), fun z hz => (h z).mpr (Or.inr hz)⟩

end rel

/-- `SuccR` is bounded. -/
def succB : BDef (k := 2) (fun V _ v ↦ SuccR (v 0) (v 1)) :=
  ((((BDef.eq (k := 3) 0 2).or (BDef.mem 0 2)).ball 0).and
    ((BDef.mem 1 0).and ((BDef.mem (k := 3) 0 1).ball 1))).congr fun _ _ _ => Iff.rfl

/-- `IndR` is bounded. -/
def indB : BDef (k := 1) (fun V _ v ↦ IndR (v 0)) :=
  ((((BDef.fls (k := 3)).ball 0).bex 0).and (((succB.comp (m := 3) ![0, 1]).bex 1).ball 0)).congr
    fun _ _ _ => Iff.rfl

/-- A formula for `NatR`. -/
def natF : FDef (k := 1) (fun V _ v ↦ NatR (v 0)) :=
  (((indB.toFDef.comp (m := 2) ![0]).imp (BDef.mem 1 0).toFDef).all).congr fun _ _ _ => Iff.rfl

/-- A formula for `IsLvl n`. -/
def isLvlF : (n : ℕ) → FDef (k := 1) (fun V _ v ↦ IsLvl n (v 0))
  | 0 => (((BDef.mem (k := 2) 0 1).toFDef.iff (natF.comp ![0])).all).congr fun _ _ _ => Iff.rfl
  | n + 1 => ((((isLvlF n).comp (m := 2) ![0]).and
      (((BDef.mem (k := 3) 0 2).toFDef.iff ((BDef.mem (k := 4) 0 2).ball 0).toFDef).all)).ex).congr
        fun _ _ _ => Iff.rfl

/-- A formula for "has type `n`". -/
def tyF' (n : ℕ) : FDef (k := 1) (fun V _ v ↦ TyR n (v 0)) :=
  ((((isLvlF n).comp (m := 2) ![0]).and (BDef.mem 1 0).toFDef).ex).congr fun _ _ _ => Iff.rfl

/-! ### Typed formulas as bounded formulas -/

/-- A typed formula as a bounded formula of `ℒₛₑₜ`: a quantifier of type `t` is bounded by the
parameter `&(2 * t)`, which stands for the level `t`. -/
def toBdd : TFm → {n : ℕ} → (ℕ → Semiterm ℒₛₑₜ ℕ n) → Semiformula ℒₛₑₜ ℕ n
  | .mem i j, _, ρ => Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![ρ i, ρ j]
  | .eq i j, _, ρ => Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![ρ i, ρ j]
  | .neg φ, _, ρ => ∼(toBdd φ ρ)
  | .and φ ψ, _, ρ => toBdd φ ρ ⋏ toBdd ψ ρ
  | .all t φ, _, ρ => ∀¹[memOp.operator ![#0, &(2 * t)]]
      (toBdd φ (TFm.scons #0 (fun i => Rew.bShift (ρ i))))

theorem toBdd_bdd (φ : TFm) : ∀ {n : ℕ} (ρ : ℕ → Semiterm ℒₛₑₜ ℕ n),
    (Bounding.mem ℒₛₑₜ).Closure (toBdd φ ρ) := by
  induction φ with
  | mem i j => intro n ρ; simp [toBdd]
  | eq i j => intro n ρ; simp [toBdd]
  | neg φ ih => intro n ρ; simpa [toBdd] using ih ρ
  | and φ ψ ih1 ih2 => intro n ρ; simpa [toBdd] using ⟨ih1 ρ, ih2 ρ⟩
  | all t φ ih =>
    intro n ρ
    exact Bounding.Closure.ball (Set.mem_singleton_iff.mpr rfl) (by simp [Semiterm.Positive])
      (ih _)

theorem eval_toBdd {W : Type} [SetStructure W] (φ : TFm) :
    ∀ {n : ℕ} (ρ : ℕ → Semiterm ℒₛₑₜ ℕ n) (e : Fin n → W) (ε : ℕ → W),
      Eval (M := W) e ε (toBdd φ ρ) ↔
        TFm.SatT (fun t a => a ∈ ε (2 * t)) (fun a b => a ∈ b) φ (fun i => (ρ i).val e ε) := by
  induction φ with
  | mem i j => intro n ρ e ε; exact Iff.rfl
  | eq i j => intro n ρ e ε; exact Iff.rfl
  | neg φ ih => intro n ρ e ε; simp [toBdd, ih]
  | and φ ψ ih1 ih2 => intro n ρ e ε; simp [toBdd, ih1, ih2]
  | all t φ ih =>
    intro n ρ e ε
    simp only [toBdd, eval_ball, eval_memOp, ih, TFm.satT_all, Semiterm.val_fvar]
    refine forall_congr' fun a => imp_congr (by simp) ?_
    have : (fun i => Semiterm.val (a :> e) ε
        (TFm.scons (#0 : Semiterm ℒₛₑₜ ℕ (n + 1)) (fun i => Rew.bShift (ρ i)) i)) =
        TFm.scons a (fun i => (ρ i).val e ε) := by
      funext i
      cases i with
      | zero => simp
      | succ i => simp [Semiterm.val_bShift]
    rw [this]

/-! ### Inside a model of `𝗠` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

theorem exists_succ (x : V) : ∃ y : V, SuccR y x := by
  obtain ⟨s, hs⟩ := m_pair x x
  obtain ⟨t, ht⟩ := m_pair x s
  obtain ⟨u, hu⟩ := m_union t
  refine ⟨u, succR_iff.mpr fun z => ?_⟩
  rw [hu]
  constructor
  · rintro ⟨w, hw, hz⟩
    rcases (ht w).mp hw with rfl | rfl
    · exact Or.inr hz
    · exact Or.inl (by simpa using (hs z).mp hz)
  · rintro (rfl | hz)
    · exact ⟨s, (ht s).mpr (Or.inr rfl), (hs z).mpr (Or.inl rfl)⟩
    · exact ⟨x, (ht x).mpr (Or.inl rfl), hz⟩

theorem succ_unique {y y' x : V} (h : SuccR y x) (h' : SuccR y' x) : y = y' :=
  m_ext fun z => ((succR_iff.mp h) z).trans ((succR_iff.mp h') z).symm

theorem empty_unique {e e' : V} (h : ∀ z, z ∉ e) (h' : ∀ z, z ∉ e') : e = e' :=
  m_ext fun z => ⟨fun hz => absurd hz (h z), fun hz => absurd hz (h' z)⟩

theorem not_mem_self (x : V) : x ∉ x := by
  intro hx
  obtain ⟨s, hs⟩ := m_pair x x
  obtain ⟨y, hy, h⟩ := m_found s ⟨x, (hs x).mpr (Or.inl rfl)⟩
  have : y = x := by simpa using (hs y).mp hy
  subst this
  exact h y hy hx

theorem exists_ind : ∃ I : V, IndR I := by
  obtain ⟨I, hI0, hIs⟩ := m_inf (V := V)
  obtain ⟨e, he⟩ := m_empty (V := V)
  refine ⟨I, ⟨e, hI0 e he, fun z hz => he z hz⟩, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := exists_succ x
  exact ⟨y, hIs x hx y (succR_iff.mp hy), hy⟩

/-- The objects that belong to every inductive set form a set. -/
theorem exists_omega : ∃ W : V, ∀ z, z ∈ W ↔ NatR z := by
  obtain ⟨I, hI⟩ := exists_ind (V := V)
  obtain ⟨P, hP⟩ := m_power I
  obtain ⟨W, hW0⟩ := (((indB.comp (m := 3) ![0]).imp (BDef.mem 1 0)).ball 1).sep I ![P]
  have hW : ∀ z, z ∈ W ↔ z ∈ I ∧ ∀ J ∈ P, IndR J → z ∈ J := hW0
  refine ⟨W, fun z => ⟨fun hz K hK => ?_, fun hz => (hW z).mpr ⟨hz I hI, fun J _ hJ => hz J hJ⟩⟩⟩
  obtain ⟨hzI, h⟩ := (hW z).mp hz
  obtain ⟨K', hK'0⟩ := (BDef.mem (k := 2) 0 1).sep I ![K]
  have hK' : ∀ w, w ∈ K' ↔ w ∈ I ∧ w ∈ K := hK'0
  have hind : IndR K' := by
    obtain ⟨⟨e₁, he₁I, he₁⟩, hIs⟩ := hI
    obtain ⟨⟨e₂, he₂K, he₂⟩, hKs⟩ := hK
    refine ⟨⟨e₁, (hK' e₁).mpr ⟨he₁I, ?_⟩, he₁⟩, fun x hx => ?_⟩
    · rw [empty_unique (fun z hz => he₁ z hz) (fun z hz => he₂ z hz)]
      exact he₂K
    · obtain ⟨hxI, hxK⟩ := (hK' x).mp hx
      obtain ⟨y₁, hy₁I, hy₁⟩ := hIs x hxI
      obtain ⟨y₂, hy₂K, hy₂⟩ := hKs x hxK
      exact ⟨y₁, (hK' y₁).mpr ⟨hy₁I, succ_unique hy₁ hy₂ ▸ hy₂K⟩, hy₁⟩
  exact ((hK' z).mp (h K' ((hP K').mpr fun w hw => ((hK' w).mp hw).1) hind)).2

/-- The levels: `lvl 0` is ω and `lvl (n + 1)` is the power set of `lvl n`. -/
noncomputable def lvl : ℕ → V
  | 0 => Classical.choose (exists_omega (V := V))
  | n + 1 => Classical.choose (m_power (lvl n))

theorem lvl_zero {z : V} : z ∈ (lvl 0 : V) ↔ NatR z :=
  Classical.choose_spec (exists_omega (V := V)) z

theorem lvl_succ {n : ℕ} {z : V} : z ∈ (lvl (n + 1) : V) ↔ ∀ w ∈ z, w ∈ (lvl n : V) :=
  Classical.choose_spec (m_power (lvl (V := V) n)) z

theorem isLvl_iff : ∀ (n : ℕ) (p : V), IsLvl n p ↔ p = lvl n
  | 0, p => ⟨fun h => m_ext fun z => (h z).trans lvl_zero.symm,
      fun h z => h ▸ lvl_zero⟩
  | n + 1, p => by
    constructor
    · rintro ⟨q, hq, h⟩
      rw [(isLvl_iff n q).mp hq] at h
      exact m_ext fun z => (h z).trans lvl_succ.symm
    · intro h
      exact ⟨lvl n, (isLvl_iff n _).mpr rfl, fun z => h ▸ lvl_succ⟩

theorem tyR_iff {n : ℕ} {x : V} : TyR n x ↔ x ∈ (lvl n : V) :=
  ⟨fun ⟨p, hp, hx⟩ => (isLvl_iff n p).mp hp ▸ hx, fun h => ⟨lvl n, (isLvl_iff n _).mpr rfl, h⟩⟩

/-- ω is inductive. -/
theorem indR_omega : IndR (lvl 0 : V) := by
  obtain ⟨e, he⟩ := m_empty (V := V)
  refine ⟨⟨e, lvl_zero.mpr fun J hJ => ?_, fun z hz => he z hz⟩, fun x hx => ?_⟩
  · obtain ⟨⟨e', he'J, he'⟩, -⟩ := hJ
    rw [empty_unique he (fun z hz => he' z hz)]
    exact he'J
  · obtain ⟨y, hy⟩ := exists_succ x
    refine ⟨y, lvl_zero.mpr fun J hJ => ?_, hy⟩
    obtain ⟨y', hy'J, hy'⟩ := hJ.2 x (lvl_zero.mp hx J hJ)
    rw [succ_unique hy hy']
    exact hy'J

/-- **Induction on ω**, for properties with a bounded definition. -/
theorem nat_induction {k : ℕ} {R : MRel (k + 1)} (d : BDef R) (p : Fin k → V)
    (h0 : ∀ e ∈ (lvl 0 : V), (∀ z, z ∉ e) → R V (e :> p))
    (hs : ∀ x ∈ (lvl 0 : V), R V (x :> p) → ∀ y ∈ (lvl 0 : V), SuccR y x → R V (y :> p)) :
    ∀ x ∈ (lvl 0 : V), R V (x :> p) := by
  obtain ⟨A, hA⟩ := d.sep (lvl 0) p
  have hind : IndR A := by
    obtain ⟨⟨e, heW, he⟩, hWs⟩ := indR_omega (V := V)
    refine ⟨⟨e, (hA e).mpr ⟨heW, h0 e heW fun z hz => he z hz⟩, he⟩, fun x hx => ?_⟩
    obtain ⟨hxW, hxR⟩ := (hA x).mp hx
    obtain ⟨y, hyW, hy⟩ := hWs x hxW
    exact ⟨y, (hA y).mpr ⟨hyW, hs x hxW hxR y hyW hy⟩, hy⟩
  intro x hx
  exact ((hA x).mp (lvl_zero.mp hx A hind)).2

/-- The members of ω are transitive. -/
theorem nat_trans : ∀ n ∈ (lvl 0 : V), ∀ y ∈ n, ∀ z ∈ y, z ∈ n := by
  have h0 : ∀ e ∈ (lvl 0 : V), (∀ z, z ∉ e) → ∀ y ∈ e, ∀ z ∈ y, z ∈ e :=
    fun e _ he y hy => absurd hy (he y)
  have hs : ∀ x ∈ (lvl 0 : V), (∀ y ∈ x, ∀ z ∈ y, z ∈ x) → ∀ s ∈ (lvl 0 : V), SuccR s x →
      ∀ y ∈ s, ∀ z ∈ y, z ∈ s := by
    intro x _ hx s _ hs y hy z hz
    rcases hs.1 y hy with rfl | hyx
    · exact hs.2.2 z hz
    · exact hs.2.2 z (hx y hyx z hz)
  exact nat_induction (((BDef.mem (k := 3) 0 2).ball 0).ball 0) ![] h0 hs

/-- For `n`, `b` in ω: if `n ⊆ b` then `n = b` or `n ∈ b`. -/
theorem nat_D : ∀ b ∈ (lvl 0 : V), ∀ n ∈ (lvl 0 : V), (∀ z ∈ n, z ∈ b) → n = b ∨ n ∈ b := by
  have h0 : ∀ e ∈ (lvl 0 : V), (∀ z, z ∉ e) →
      ∀ n ∈ (lvl 0 : V), (∀ z ∈ n, z ∈ e) → n = e ∨ n ∈ e :=
    fun e _ he n _ hn => Or.inl (empty_unique (fun z hz => he z (hn z hz)) he)
  have hs : ∀ b ∈ (lvl 0 : V), (∀ n ∈ (lvl 0 : V), (∀ z ∈ n, z ∈ b) → n = b ∨ n ∈ b) →
      ∀ s ∈ (lvl 0 : V), SuccR s b →
        ∀ n ∈ (lvl 0 : V), (∀ z ∈ n, z ∈ s) → n = s ∨ n ∈ s := by
    intro b _ hb s _ hs n hn hns
    by_cases hbn : b ∈ n
    · refine Or.inl (m_ext fun z => ⟨hns z, fun hz => ?_⟩)
      rcases hs.1 z hz with rfl | hzb
      · exact hbn
      · exact nat_trans n hn b hbn z hzb
    · have hnb : ∀ z ∈ n, z ∈ b := fun z hz => by
        rcases hs.1 z (hns z hz) with rfl | hzb
        · exact absurd hz hbn
        · exact hzb
      rcases hb n hn hnb with rfl | h
      · exact Or.inr hs.2.1
      · exact Or.inr (hs.2.2 n h)
  exact nat_induction
    ((((BDef.mem (k := 4) 0 2).ball 0).imp ((BDef.eq 0 1).or (BDef.mem 0 1))).ball 1)
    ![(lvl 0 : V)] h0 hs

/-- For `n`, `b` in ω: `b ∈ n` or `n ⊆ b`. -/
theorem nat_C : ∀ n ∈ (lvl 0 : V), ∀ b ∈ (lvl 0 : V), b ∈ n ∨ ∀ z ∈ n, z ∈ b := by
  have h0 : ∀ e ∈ (lvl 0 : V), (∀ z, z ∉ e) → ∀ b ∈ (lvl 0 : V), b ∈ e ∨ ∀ z ∈ e, z ∈ b :=
    fun e _ he b _ => Or.inr fun z hz => absurd hz (he z)
  have hs : ∀ n ∈ (lvl 0 : V), (∀ b ∈ (lvl 0 : V), b ∈ n ∨ ∀ z ∈ n, z ∈ b) →
      ∀ s ∈ (lvl 0 : V), SuccR s n → ∀ b ∈ (lvl 0 : V), b ∈ s ∨ ∀ z ∈ s, z ∈ b := by
    intro n hn ih s _ hs b hb
    rcases ih b hb with h | h
    · exact Or.inl (hs.2.2 b h)
    · rcases nat_D b hb n hn h with rfl | hnb
      · exact Or.inl hs.2.1
      · refine Or.inr fun z hz => ?_
        rcases hs.1 z hz with rfl | hzn
        · exact hnb
        · exact h z hzn
  exact nat_induction (((BDef.mem (k := 3) 0 1).or ((BDef.mem (k := 4) 0 1).ball 1)).ball 1)
    ![(lvl 0 : V)] h0 hs

/-- Extensionality for the levels. -/
theorem ty_ext {n : ℕ} {x y : V} (hx : x ∈ (lvl (n + 1) : V)) (hy : y ∈ (lvl (n + 1) : V))
    (h : ∀ z ∈ (lvl n : V), (z ∈ x ↔ z ∈ y)) : x = y :=
  m_ext fun z => ⟨fun hz => (h z (lvl_succ.mp hx z hz)).mp hz,
    fun hz => (h z (lvl_succ.mp hy z hz)).mpr hz⟩

/-- Comprehension for the levels: a typed formula defines an object of the next level. -/
theorem ty_comp (t : ℕ) (φ : TFm) (v : ℕ → V) :
    ∃ y ∈ (lvl (t + 1) : V), ∀ x ∈ (lvl t : V),
      (x ∈ y ↔ TFm.SatT (fun k (a : V) => a ∈ (lvl k : V)) (fun a b => a ∈ b) φ
        (TFm.scons x v)) := by
  let ε : ℕ → V := fun k => if k % 2 = 0 then lvl (k / 2) else v (k / 2)
  obtain ⟨y, hy⟩ := sep_raw
    (toBdd φ (TFm.scons (#0 : Semiterm ℒₛₑₜ ℕ 1) (fun i => &(2 * i + 1)))) (toBdd_bdd φ _) ε (lvl t)
  refine ⟨y, lvl_succ.mpr fun w hw => ((hy w).mp hw).1, fun x hx => ?_⟩
  rw [hy x, eval_toBdd]
  have hε : (fun k (a : V) => a ∈ ε (2 * k)) = fun k (a : V) => a ∈ (lvl k : V) := by
    funext k a
    simp [ε]
  have henv : (fun i => Semiterm.val ![x] ε
      (TFm.scons (#0 : Semiterm ℒₛₑₜ ℕ 1) (fun i => &(2 * i + 1)) i)) = TFm.scons x v := by
    funext i
    cases i with
    | zero => simp
    | succ i =>
      have h1 : (2 * i + 1) % 2 = 1 := by omega
      have h2 : (2 * i + 1) / 2 = i := by omega
      simp [ε, h1, h2]
  rw [hε, henv]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

/-- ω is not finite. -/
theorem ty_inf (v : ℕ → V) :
    TFm.SatT (fun k (a : V) => a ∈ (lvl k : V)) (fun a b => a ∈ b) (TFm.infFm 0) v := by
  obtain ⟨F, hF0⟩ := (((BDef.mem (k := 4) 0 1).ball 1).bex 1).sep (lvl 1) ![(lvl 0 : V)]
  have hF : ∀ A, A ∈ F ↔ A ∈ (lvl 1 : V) ∧ ∃ n ∈ (lvl 0 : V), ∀ a ∈ A, a ∈ n := hF0
  refine TFm.satT_infFm.mpr ⟨F, lvl_succ.mpr fun w hw => ((hF w).mp hw).1, ?_, ?_, ?_⟩
  · intro e he hemp
    obtain ⟨⟨e₀, he₀, -⟩, -⟩ := indR_omega (V := V)
    exact (hF e).mpr ⟨he, e₀, he₀, fun a ha => absurd ha (hemp a (lvl_succ.mp he a ha))⟩
  · intro s _ hsF b hb s' hs' hadj
    obtain ⟨-, n, hn, hsn⟩ := (hF s).mp hsF
    refine (hF s').mpr ⟨hs', ?_⟩
    rcases nat_C n hn b hb with hbn | hnb
    · refine ⟨n, hn, fun a ha => ?_⟩
      rcases (hadj a (lvl_succ.mp hs' a ha)).mp ha with h | rfl
      · exact hsn a h
      · exact hbn
    · obtain ⟨m, hm, hmb⟩ := (indR_omega (V := V)).2 b hb
      refine ⟨m, hm, fun a ha => ?_⟩
      rcases (hadj a (lvl_succ.mp hs' a ha)).mp ha with h | rfl
      · exact hmb.2.2 a (hnb a (hsn a h))
      · exact hmb.2.1
  · intro u _ hall huF
    obtain ⟨-, n, hn, hun⟩ := (hF u).mp huF
    exact not_mem_self n (hun n (hall n hn))

end model

/-! ### The interpretation -/

open DirectTranslation

/-- The interpretation of the relation symbols. -/
def tstRel : {k : ℕ} → (ℒₜₛₜ).Rel k → Semiformula.Operator ℒₛₑₜ k
  | _, Language.TST.Rel.eq => Semiformula.Operator.Eq.eq
  | _, Language.TST.Rel.mem => ⟨(BDef.mem (k := 2) 0 1).φ⟩
  | _, Language.TST.Rel.ty n => ⟨(tyF' n).φ⟩

/-- **The translation of the language of type theory into `𝗠`**: the domain is everything,
membership is membership, equality is equality, and "has type `n`" is "belongs to `Pⁿ(ω)`". -/
def tstTranslation : DirectTranslation 𝗠 ℒₜₛₜ where
  domain := ⟨(FDef.tru (k := 1)).φ⟩
  rel := tstRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    suffices ∃ x : M, (⟨(FDef.tru (k := 1)).φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] by
      simpa [models_iff] using this
    exact ⟨Classical.arbitrary M, (FDef.tru.eval M _).mpr trivial⟩
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : tstRel (Language.Eq.eq : (ℒₜₛₜ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section tstModel

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-- An object of the model, as an object of the interpreted structure. -/
def toModel (a : V) : tstTranslation.Model V := ⟨a, (FDef.tru.eval V _).mpr trivial⟩

theorem coe_inj {a b : tstTranslation.Model V} (h : (a : V) = (b : V)) : a = b := by
  cases a; cases b; cases h; rfl

theorem tm_ty (n : ℕ) (a : tstTranslation.Model V) : TST.Ty n a ↔ (a : V) ∈ (lvl n : V) := by
  unfold TST.Ty
  rw [Model.rel_iff]
  have h2 : (fun i ↦ ((![a] i : tstTranslation.Model V) : V)) = ![(a : V)] := by
    funext i; fin_cases i; rfl
  rw [h2]
  exact ((tyF' n).eval V ![(a : V)]).trans tyR_iff

theorem tm_mem (a b : tstTranslation.Model V) : TST.Mem a b ↔ (a : V) ∈ (b : V) := by
  unfold TST.Mem
  rw [Model.rel_iff]
  have h2 : (fun i ↦ ((![a, b] i : tstTranslation.Model V) : V)) = ![(a : V), (b : V)] := by
    funext i; fin_cases i <;> rfl
  rw [h2]
  exact (BDef.mem (k := 2) 0 1).eval V ![(a : V), (b : V)]

/-- A typed formula holds in the interpreted structure iff it holds for the levels. -/
theorem tm_holds (φ : TFm) : ∀ v : ℕ → tstTranslation.Model V,
    TST.Holds φ v ↔ TFm.SatT (fun k (a : V) => a ∈ (lvl k : V)) (fun a b => a ∈ b) φ
      (fun i => (v i : V)) := by
  induction φ with
  | mem i j => intro v; exact tm_mem _ _
  | eq i j => intro v; exact ⟨fun h => congrArg _ h, fun h => coe_inj h⟩
  | neg φ ih => intro v; simp only [TFm.satT_neg, ih v]
  | and φ ψ ih1 ih2 => intro v; simp only [TFm.satT_and, ih1 v, ih2 v]
  | all t φ ih =>
    intro v
    simp only [TFm.satT_all]
    have e : ∀ a : tstTranslation.Model V, (fun i => ((TFm.scons a v i : tstTranslation.Model V) : V)) =
        TFm.scons (a : V) (fun i => (v i : V)) := by
      intro a
      funext i
      cases i <;> rfl
    constructor
    · intro h a ha
      have := (ih _).mp (h (toModel a) ((tm_ty t _).mpr ha))
      rwa [e] at this
    · intro h a ha
      refine (ih _).mpr ?_
      rw [e]
      exact h (a : V) ((tm_ty t a).mp ha)

/-- **In a model of `𝗠`, the interpreted structure is a model of `𝗧𝗦𝗧𝗜`.** -/
theorem tstModel_models : (tstTranslation.Model V)↓[ℒₜₛₜ] ⊧* 𝗧𝗦𝗧𝗜 :=
  TST.models_of
    (fun n x y hx hy h => coe_inj (ty_ext ((tm_ty _ x).mp hx) ((tm_ty _ y).mp hy) fun z hz => by
      have := h (toModel z) ((tm_ty n _).mpr hz)
      rwa [tm_mem, tm_mem] at this))
    (fun t Γ φ _ v _ => by
      obtain ⟨y, hy, h⟩ := ty_comp (V := V) t φ (fun i => (v i : V))
      refine ⟨toModel y, (tm_ty _ _).mpr hy, fun x hx => ?_⟩
      rw [tm_mem, tm_holds]
      have e : (fun i => ((TFm.scons x v i : tstTranslation.Model V) : V)) =
          TFm.scons (x : V) (fun i => (v i : V)) := by
        funext i
        cases i <;> rfl
      rw [e]
      exact h (x : V) ((tm_ty t x).mp hx))
    (fun v => (tm_holds _ v).mpr (ty_inf _))

end tstModel

/-- **`𝗠` interprets `𝗧𝗦𝗧𝗜`**, the simple theory of types with infinity. -/
instance mInterpretsTSTI : 𝗠 ⊳ 𝗧𝗦𝗧𝗜 where
  trln := tstTranslation
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp tstModel_models φ hφ)

/-- **The syntactic transformation.** The translation of a theorem of `𝗧𝗦𝗧𝗜` is a theorem of
`𝗠`. -/
theorem m_provable_translate_of_tsti {σ : Sentence ℒₜₛₜ} (h : 𝗧𝗦𝗧𝗜 ⊢ σ) :
    𝗠 ⊢ mInterpretsTSTI σ :=
  DirectInterpretation.sound mInterpretsTSTI h

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.mInterpretsTSTI
